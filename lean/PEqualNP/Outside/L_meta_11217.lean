import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11217

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
        ∃ w ∈ ops a b, build ops goal k (insert w available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ w ∈ ops a b, w ∉ s ∧
        ∃ needed, insert a (insert b needed) = s ∧ live ops goal k (insert w needed)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, w, hw, next⟩
    · obtain ⟨s, hs, hl⟩ := ih skip
      exact ⟨s, hs, .inl hl⟩
    · obtain ⟨s, hs, hl⟩ := ih next
      by_cases hwa : w ∈ available
      · have hsub : s ⊆ available := by
          intro x hx
          rcases Finset.mem_insert.mp (hs hx) with rfl | hx'
          · exact hwa
          · exact hx'
        exact ⟨s, hsub, .inl hl⟩
      · by_cases hws : w ∈ s
        · refine ⟨insert a (insert b (s.erase w)), ?_, .inr ⟨a, ?_, b, ?_, hab, w, hw, ?_, s.erase w, rfl, ?_⟩⟩
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ha
            · rcases Finset.mem_insert.mp hx with rfl | hx
              · exact hb
              · have hx' := Finset.mem_erase.mp hx
                exact (Finset.mem_insert.mp (hs hx'.2)).resolve_left hx'.1
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · intro hmem
            rcases Finset.mem_insert.mp hmem with hwa_eq | hmem
            · exact hwa (hwa_eq ▸ ha)
            · rcases Finset.mem_insert.mp hmem with hwb_eq | hmem
              · exact hwa (hwb_eq ▸ hb)
              · exact (Finset.mem_erase.mp hmem).1 rfl
          · simpa [Finset.insert_erase hws] using hl
        · have hsub : s ⊆ available := fun x hx =>
            (Finset.mem_insert.mp (hs hx)).resolve_left (fun hxw => hws (hxw ▸ hx))
          exact ⟨s, hsub, .inl hl⟩

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => simp [live] at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, _, b, _, _, w, _, hnew, needed, hs, tail⟩
    · exact (ih skip).trans (Nat.le_succ _)
    · have hc := ih tail
      have hw : w ∉ needed := by
        intro hw
        apply hnew
        rw [← hs]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
      rw [Finset.card_insert_of_notMem hw] at hc
      have hsub : s.card ≤ needed.card + 2 := by
        rw [← hs]
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hstep : ∀ a b z, z ∈ ops a b → D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => exact ⟨goal, by simp [live] at h; simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, _, w, hw, _, needed, hs, tail⟩
    · exact ih skip
    · obtain ⟨u, hu, hdu⟩ := ih tail
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rcases hstep a b u hw hdu with hda | hdb
        · exact ⟨a, ha, hda⟩
        · exact ⟨b, hb, hdb⟩
      · exact ⟨u, hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hdu⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ w ∈ ops a b, w ∉ s ∧
        ∃ needed, insert a (insert b needed) = s ∧ live ops goal k (insert w needed) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 512
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)

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

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256 + i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256 + i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
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
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

private theorem not_zero_512 : ~~~(0 : W) = BitVec.allOnes 512 := by decide +kernel

theorem basicOps_zero_left (b z : W) (hz : z ∈ basicOps 0 b) : z = 0 ∨ z = b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · left; exact BitVec.zero_and
  · right; exact BitVec.zero_or
  · left; exact BitVec.zero_and
  · right; rw [not_zero_512]; exact BitVec.and_allOnes

theorem basicOps_zero_right (a z : W) (hz : z ∈ basicOps a 0) : z = 0 ∨ z = a := by
  rw [ops_swap] at hz
  exact basicOps_zero_left a z hz

theorem live_ne_zero {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {s : Finset W}
    (h : live basicOps g k s) : (0 : W) ∉ s := by
  have hne : g ≠ 0 := by rcases hg with rfl | rfl <;> decide +kernel
  induction k generalizing s with
  | zero =>
    intro h0
    change s = {g} at h
    rw [h, Finset.mem_singleton] at h0
    exact hne h0.symm
  | succ k ih =>
    rcases h with skip | ⟨a, _, b, _, _, w, hw, _, r, hs, tail⟩
    · exact ih skip
    · intro h0
      by_cases ha0 : a = 0
      · subst ha0
        rcases basicOps_zero_left b w hw with rfl | rfl <;> contradiction
      by_cases hb0 : b = 0
      · subst hb0
        rcases basicOps_zero_right a w hw with rfl | rfl <;> contradiction
      apply ih tail
      rw [← hs] at h0
      rcases Finset.mem_insert.mp h0 with h0a | h0b
      · exact False.elim (ha0 h0a.symm)
      · rcases Finset.mem_insert.mp h0b with h0b' | h0r
        · exact False.elim (hb0 h0b'.symm)
        · exact Finset.mem_insert_of_mem h0r

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

inductive BTree (α : Type) where
  | nil : BTree α
  | node : α → BTree α → BTree α → BTree α

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey, Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 10 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closedEmpty (k : Nat) : Closed k .nil := by
  intro _ _ _ _ _ hm
  contradiction

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def descend (k : Nat) (ws : List W) (f : List W → Bool) : Bool :=
  (pairs ws).any fun (a, b, r) =>
    let c := cuts r
    let ca := sep a ||| c
    let cb := sep b ||| c
    let cab := sep a ||| cb
    let n := r.length
    (ops a b).any fun z =>
      if z == 0 || decide (z ∈ ws) then false else
      let dz := sep z
      (decide (n ≤ k) && (dz ||| c == -1) && f (z :: r)) ||
      (decide (n + 1 ≤ k) && (dz ||| ca == -1) && f (z :: a :: r)) ||
      (decide (n + 1 ≤ k) && (dz ||| cb == -1) && f (z :: b :: r)) ||
      (decide (n + 2 ≤ k) && (dz ||| cab == -1) && f (z :: a :: b :: r))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem descend_hit {k ws a b r z kept f}
    (hm : (a, b, r) ∈ pairs ws) (hz : z ∈ ops a b)
    (hz0 : z ≠ 0) (hzw : z ∉ ws)
    (hk : kept ∈ keepChoices a b r) (hl : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (hf : f (z :: kept) = true) : descend k ws f = true := by
  apply List.any_eq_true.mpr ⟨(a, b, r), hm, ?_⟩
  apply List.any_eq_true.mpr ⟨z, hz, ?_⟩
  have hskip : (z == 0 || decide (z ∈ ws)) = false :=
    Bool.or_eq_false_iff.mpr ⟨beq_false_of_ne hz0, decide_eq_false hzw⟩
  simp only [hskip, Bool.false_eq_true, ↓reduceIte]
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with eq | eq | eq | eq <;> subst kept
  · change sep z ||| cuts r = -1 at hc
    simp [hl, hc, hf]
  · change sep z ||| (sep a ||| cuts r) = -1 at hc
    change r.length + 1 ≤ k at hl
    simp [hl, hc, hf]
  · change sep z ||| (sep b ||| cuts r) = -1 at hc
    change r.length + 1 ≤ k at hl
    simp [hl, hc, hf]
  · change sep z ||| (sep a ||| (sep b ||| cuts r)) = -1 at hc
    change r.length + 2 ≤ k at hl
    simp [hl, hc, hf]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem descend_sound {k : Nat} {g : W} (hg : g = goal ∨ g = ~~~goal)
    {ws : List W} (hn : ws.Nodup) (h : live basicOps g (k + 1) ws.toFinset)
    (f : List W → Bool) (hf : ∀ ys : List W, ys.Nodup → live basicOps g k ys.toFinset → f ys = true) :
    doneTest ws || descend k ws f = true := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq, doneTest]
  · rw [Bool.or_eq_true]
    right
    obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have hzw : z ∉ ws := fun hu => hout (List.mem_toFinset.mpr hu)
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a, b, r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : descend k ws f = true := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hz0 : z ≠ 0 := by
        intro hz0'
        apply live_ne_zero hg hraw
        rw [hz0']
        exact List.mem_toFinset.mpr (List.mem_cons_self)
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      exact descend_hit hmem (List.mem_toFinset.mp hop) hz0 hzw hkeep (by omega) (cuts_full hg hraw) (hf _ hnd hraw)
    rcases hm with direct | swap
    · exact go hp direct hs.symm hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [← hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def certRow (k : Nat) (tr : BTree (List W)) (ws : List W) : Bool :=
  !(doneTest ws || descend k ws (fun zs => !containsKey (ordered zs) tr))

theorem checkedLayer (k : Nat) (hk : k < 10) (tr next : BTree (List W))
    (hs : Closed k next) (hc : everyKey (certRow k next) tr = true) :
    Closed (k + 1) tr := by
  intro g hg ws hn _ hm h
  have ok := every_at tr hc hm
  have impossible := descend_sound hg hn h (fun zs => !containsKey (ordered zs) next) (by
    intro ys hy hr
    cases eq : containsKey (ordered ys) next with
    | false => rfl
    | true =>
      have hp := ordered_perm ys
      have hl := live_card hr
      rw [List.toFinset_card_of_nodup hy] at hl
      have hsize : (ordered ys).length ≤ 10 := by rw [hp.length_eq]; omega
      exact False.elim (hs g hg _ (hp.nodup_iff.mpr hy) hsize eq (by rwa [perm_set hp])))
  simp only [certRow, Bool.not_eq_true'] at ok
  cases hd : doneTest ws <;> cases hh : descend k ws (fun zs => !containsKey (ordered zs) next) <;> simp_all

theorem splitCheck {f : List W → Bool} {ws} {l r : BTree (List W)}
    (m : f ws = true) (a : everyKey f l = true) (b : everyKey f r = true) :
    everyKey f (.node ws l r) = true := by simp [everyKey, m, a, b]

def startOK (n : Nat) (tr : BTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n + 1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 10) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
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
  · simpa [startOK, size, cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · rw [not_zero_512, BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · rw [not_zero_512, BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩
  · have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; exact BitVec.getElem_zero k.isLt
    rcases hop with rfl | rfl | rfl <;>
      simp only [step, List.map_nil, List.map_append, action, GateOp.eval,
        List.foldr_nil, List.head?_nil, List.headD_nil, Option.map_none, Option.getD_none,
        List.all_nil, List.any_nil, List.map_cons, bit, BitVec.getElem_not,
        bit0, Bool.not_false]
  · have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; exact BitVec.getElem_zero k.isLt
    rcases hop with rfl | rfl | rfl <;>
      simp only [step, List.map_cons, List.map_nil, read_bit, List.map_append, action, GateOp.eval,
        List.foldr_cons, List.foldr_nil, List.head?_cons, List.headD_cons, Option.map_some,
        Option.getD_some, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
        Bool.and_true, Bool.or_false, bit, BitVec.getElem_and, BitVec.getElem_or,
        BitVec.getElem_not, bit0, Bool.not_false]
  · have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; exact BitVec.getElem_zero k.isLt
    rcases hop with rfl | rfl | rfl <;>
      simp only [step, List.map_cons, List.map_nil, read_bit, List.map_append, action, GateOp.eval,
        List.foldr_cons, List.foldr_nil, List.head?_cons, List.headD_cons, Option.map_some,
        Option.getD_some, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
        Bool.and_true, Bool.or_false, bit, BitVec.getElem_and, BitVec.getElem_or,
        BitVec.getElem_not, bit0, Bool.not_false]
  · simp at cap

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
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
      action, List.head?_nil, List.map_nil, List.foldr_nil, Option.map_none, Option.getD_none]
    · exact .inl (.inr (.inl rfl))
    · exact .inl (.inl rfl)
    · exact .inr (.inl rfl)
  · rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
      action, List.head?_cons, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      Option.map_some, Option.getD_some,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => by rw [not_zero_512]; exact BitVec.and_allOnes]
    · exact .inl (available_read hw _)
    · exact .inl (available_read hw _)
    · exact holds_not (available_read hw _)
  · rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
      action, List.head?_cons, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      Option.map_some, Option.getD_some,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => by rw [not_zero_512]; exact BitVec.and_allOnes]
    · exact and_reach (available_read hw _) (available_read hw _)
    · exact or_reach (available_read hw _) (available_read hw _)
    · exact holds_not (available_read hw _)
  · simp at cap

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
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide +kernel : goal ≠ 0) zero)
    · exact False.elim ((by decide +kernel : goal ≠ ~~~0) ones)
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
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def za:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zb:W:=0xc07ffff0fc07e007fc3ffc07ffffe3ffffffff8000019e3987e0724e73e7fe000000000000000000000000000000000000000000000000000000000000000000
def zc:W:=0xff800000fffffff800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zd:W:=0xfffffffffffffffffffffff800000000000000000003fffffffffffffc000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def ze:W:=0x3fffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zf:W:=0xfffffffffffffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zg:W:=0x7ff8000000000000000007ffe003fffff000000001182187e060000387e0000000000000000000000000000000000000000000000000000000000000000000
def zh:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fff80000086180000124e72661e000000000000000000000000000000000000000000000000000000000000000000
def zi:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zj:W:=0xf87f87ffff87fc07fffffffffe1fffffe00ffffffffcc71e049e1e4ffe7f9fff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zk:W:=0xfff807f0fffffffffc3ffc07fffffffe000ffffffffea6d9f80193fe73fe1fffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zl:W:=0xffffffff0000000000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zm:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffe0019e3987e073cff3e7ffe0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zn:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fff800003fffffffe124e72661e00040040880000020000030200000000001000c0000003ef7a292a000000000000
def zo:W:=0xfffffffffc07e007fc3ffc07ffffffffffffff800003c6fe0001fe4e73fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zp:W:=0xffffffffffffffffffffffffe01fe3fe000fff800003ff180001fffffe661e00263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zq:W:=0xc07ffff0fff80007ffc00007ffffe3ffffffffffe001983987e0738f83e7ffe0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zr:W:=0xfff807f0fffffffffc3ffc07fffffc000000007ffffea6c1f80193fe73f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zs:W:=0xf87f87ffff87fc07fffffffe1e1e1fc1e00f007ffffcc706049e1e4ffc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zt:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zu:W:=0xffff87fffffffffffffffffe1e1e1fc1e00f007ffffee706049f9ffffc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zv:W:=0xfffffffffffffffffffffffffffffc000000007fffffffc1f801fffffff801fff6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zw:W:=0x3847870fc3861c0783fc03fe1e1e1c000000007ffffffffffffe0c09cc1801ff040040880000020000030200000000001000c0000003ef7a292a000000000000
def zx:W:=0xffc7870fffffffff83fc03ffffffffc1e00f007ffffe61c7fc9f8ff9cffd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zy:W:=0xffffffffc3861c0000000007ffffffffffffffffffffc0fe0001fc0003ffffffbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zz:W:=0xfffffffffffffffffffffffe1e1e1c000000007fffffff000001fffffc1801ff263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zA:W:=0xf87807f0ff87fc07fc3ffc07fe1ffffe000ffffffffc86196718124e727e1fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zB:W:=0xc07807f03c01e007fc3ffc01e001e3fe000fff80000086196718124e72661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zC:W:=0x7ff8003c780007ffc00001e1e003fffff000000001182187e0638f8387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zD:W:=0x61e1e1c000000007ffffffffffffe0000001801ff040040880000020000030200000000001000c0000003ef7a292a000000000000
def zE:W:=0x387ff800fffe1c07ffc00007fffe1ffffff0007ffffd182187e0638f839fe1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zF:W:=0x38000000c3861c00000000061e1e1c000000007ffffffffffffe0000001801ff040040880000020000030200000000001000c0000003ef7a292a000000000000
def zG:W:=0xc7c7870f3c79e3ff83fc03f9e1e1e3c1e00f0000000261c7fc9f8ff9cfe59800d8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zH:W:=0xc7ffffff3c79e3fffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zI:W:=0xc7ffffff0000000000000001e1e1e3ffffffff800003c0fe0001fc0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zJ:W:=0xff800000fffffff8000000061e1e1c000000007fffffffffffff83f0001801ff040040880000020000030200000000001000c0000003ef7a292a000000000000
def zK:W:=0xc07ffff0fc07e007fc3ffc07ffffe3fffffffffc1f019e39e7f8724e73e7ff9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zL:W:=0xffffffffffffffffffffffffffe003fffff000000003ff2187e1ffffff87e000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zM:W:=0x7ff8000000000000000007ffe003fffff000000003fffffffe60000387e000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zN:W:=0xc07ffff0fc07e007fc3ffc07ffffe3fffffffffc1f0186396718724e73e7ff9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zO:W:=0xffffffffffffffffffffffffffffe3ffffffff800003ff380001ffffffe7fe00263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zP:W:=0xf87fffffc3861c0783fc03fffffffffffffffffffffdc13e049e7c09cfffffff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zQ:W:=0xfffffff0fffffff800000007ffffffffffffffffffffa0f9f801f3f003ffffffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zR:W:=0xff800000fffffff800000007fffffc000000007fffff38e1ffe183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zS:W:=0xc07ffff00000000000000007ffffe3ffffffff800003fffffffe700003e7fe00040040880000020000030200000000001000c0000003ef7a292a000000000000
def zT:W:=0x387fff0fc3861c0783fc03fffffe1fffffff007ffffd592787fe6c09cf9ff9ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zU:W:=0xc07ffff00000000000000007ffffe3ffffffff80000180380000700003e7fe000000000000000000000000000000000000000000000000000000000000000000
def zV:W:=0xffffffff0000000000000007ffffffffffffff800003fffffffffc0003fffe00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zW:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffd592787fe0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zX:W:=0xfffff800fffffff800000007fffffffffff0007fffff38e1ffe1e3f003ffe1ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zY:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffffffffffe0c09cc1d99ff0c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def zZ:W:=0xffc7870fffffffff83fc03fffffffc000000007ffffe61c7fc9f8ff9cff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def z0:W:=0xfffffffffffffffffffffffe1e1e1c000000007fffffff06049ffffffc1801ff263664cc224113844222c380000000000c0020000003fb000000f49294000000
def z1:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0379e698e6124e72661f9844484198cc26a212b51a3a166086a15a904687369617eb6b4e32024c62461598
def z2:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff01182187e073cff3e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def z3:W:=0xc07ffff00000000000000007ffffe3ffffffff800001983987e0700003e7fe000000000000000000000000000000000000000000000000000000000000000000
def z4:W:=0xfffffffffc07e007fc3ffc07ffffffffffffff800003fffe0001fe4e73fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def z5:W:=0xffff87fffffffffffffffffffffffc000000007ffffee7c1f8019ffffff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def z6:W:=0xfffffffffffffffffffffffe1e1e1fc1e00f007fffffff06049ffffffc1d99ff2e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def z7:W:=0xffffffff0007fff8003fffffffffffffffffff800003fffe0001fc707ffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def z8:W:=0xff800000fffffff800000007fffffc000000007fffffffffffff83f003f801ffd48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def z9:W:=0xffc7870fffffffff83fc03fe1e1e1fc1e00f007ffffe61c7fc9f8ff9cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zaa:W:=0xffffffffffffffffffffffffe01fe3fe000fff800003fffe0001fffffe661e00263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zab:W:=0xffffffff0000000000000007ffffffffffffff800003d8ff87e1fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zac:W:=0xffffffffffffffffffffffffffffffffffffff800003fffe0001fffffffffe00bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zad:W:=0xfffffffffffffffffffffffe1e1e1c000000007fffffffc1f801fffffc1801ff263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zae:W:=0xc07ffff0fc07e007fc3ffc07ffffe3ffffffff80000186380000724e73e7fe000000000000000000000000000000000000000000000000000000000000000000
def zaf:W:=0xfff807f0fffffffffc3ffc07e01fe3fe000ffffffffea619ff1993fe72661fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zag:W:=0xc03800f03c01e0007c03fc07e01fe3fe000fff80000086196300124632661e00400800108c24a012240930046084a11200424632121004116308024422420488
def zah:W:=0x3878003c7800007c000007ffe003fffff0000000011821836063860387e000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zai:W:=0x3807800f03801c0003c003f81e001c01e000007ffffc4106049e0c018c1981ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zaj:W:=0x7f80003f8000003c000001fe00001fff0007fe001182187e061818181e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zak:W:=0xffffffff000000000000000000000000000000000003fffffffffc0000000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zal:W:=0xc07807f000000007fc3ffc07e01fe3fe000fff80000086180000100e72661e000000000000000000000000000000000000000000000000000000000000000000
def zam:W:=0xc07807f0ffffe007fc3ffc07ffffe3ffffffffffff008639e7f813ce73e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def zan:W:=0x7f80003f8000003c000001fe003fffff00003e001182087e061818187e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zao:W:=0xc7b878f00000000000000001e1e1e3ffffffff80000380fe0001f00003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zap:W:=0xffffffffc3861c0783fc03ffffffffffffffffffffffc1fe0001fc09cfffffffbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zaq:W:=0xc03800f03c01e0007c03fc01e001e3fe000fff80000086196718124632661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zar:W:=0xf87f87ffff87fc07fffffffffe1ffffe000ffffffffcc71967181e4ffe7e1fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zas:W:=0x3878003c7800007c000001e1e003fffff000000001182187e063860387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zat:W:=0x387fff0ffffe1c07fffc03fffffe1ffffff0007ffffd592187e06f8fcf9fe1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zau:W:=0xffffffff0000000000000007ffffffffffffff800003fffff801fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zav:W:=0x7fffff00000007fffffffffffffc000000007ffffddfc1f8007c0ffff801fff6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zaw:W:=0x7807f000000007fc3ffc07e01fe3fe000ffffc1f0086196718100e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zax:W:=0xfffffffffffffff800000007ffffffffffffff800003e0fe0001fff003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zay:W:=0xfff807f0fffffffffc3ffc07e01fe3fe000ffffc1f02a619671993fe72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zaz:W:=0x47870f0000000783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zaA:W:=0x7fffff0000000000000007ffffffffffffff800001c0fe00007c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zaB:W:=0xffc7870fffffffff83fc03fe1e1e1fc1e00f007ffffe6106049f8ff9cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zaC:W:=0x7ff80000000007ffc00007ffe003fffff0007fe001182187e0600f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zaD:W:=0xfffff800ffffffffffc00007ffe003fffff0007fe003382187e1e3ff8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zaE:W:=0x1dffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zaF:W:=0xff800000fffffff80000000000000000000000000003ffffffff83f000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zaG:W:=0x23ffffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zaH:W:=0x7fffff000000000000000000000000000000000003fffffffe7c0000000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zaI:W:=0xf87807f0ff87fc07fffffffffe1ffffe000ffffffffc8719679e124ffe7e1fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zaJ:W:=0x387ff800fffe1c07fffc03fffffe1ffffff0007ffffd192187fe638fcf9fe1ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zaK:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffffffc8619ff18124e72661fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zaL:W:=0x7ff800fff80007ffc00007ffe003fffff0007ffffd1821ffe0638f8387e1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zaM:W:=0xc07807f000000007fc3ffc07e01fe3fe000ffffc1f0086196718100e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zaN:W:=0xc07807f0fffffffffc3ffc07e01fe3fe000ffffc1f00a619671813fe72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zaO:W:=0x3847870fffffffff83fc03fe1e1e1fc1e00f007ffffc6106049e0ff9cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zaP:W:=0x7ff80000000007ffc00007ffe003fffff000000001182007e0600f8387e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zaQ:W:=0xc07807f000000007fc3ffc07e01fe3fe000fff80000086180718100e72661e000048011044022002951918122002214a80464314860404102718000c60061510
def zaR:W:=0xc07807f0fffffffffc3ffc07e01fe3fe000ffffffffca619ff1813fe72661fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zaS:W:=0x7ff800ffffffffffc00007ffe003fffff0007ffffd3821ffe063ff8387e1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zaT:W:=0x1ffffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zaU:W:=0xfffffffffffffff80000000000000000000000000003fffffffffff000000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zaV:W:=0x7f80003f80007ffc000001fe00001fff00003e001182087e0618f8181e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zaW:W:=0xc07ffff0ffffe007ffc00007ffffe3ffffffffffff019839e7e073cf83e7fff8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zaX:W:=0xc00007f00007e007fc3ffc00001fe000000fff801f0086186718104e70601e18404801104c062012951938126006214a80464734861404106718004c60461518
def zaY:W:=0xfffffffffffffffffffffff800000000000000000003fffff801fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zaZ:W:=0x7ffffffffffff800000000000003fffffffffffffde03ff8007ff00007ffff6da556aa9934c9302000a144cdcdda311988ac631873c06fd000bf600350aaaa
def za0:W:=0xfff807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0286196719924e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def za1:W:=0x47870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def za2:W:=0xffc7870fc3861c0783fc03fe1e1e1fc1e00f007ffffe4106049f8c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def za3:W:=0x1fffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def za4:W:=0xff800000000000000000000000000000000000000003ffffffff800000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def za5:W:=0x3f87f80f03f81ff803c003f80000000000000000000379000001edb18c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def za6:W:=0x7ff8000000000000000007ffffe3ffffffff80000100380000600003e7fe000000000000000000000000000000000000000000000000000000000000000000
def za7:W:=0xffffffff0000000000000007ffffffffffffff80000000180001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def za8:W:=0x3fe7fffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def za9:W:=0xffffffff0000000000000007e01fe3fe000fff800003fffffffffc0002661e00242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zba:W:=0x7ff80000000007ffc000001fe003fffff00003e001182087e0600f8187e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zbb:W:=0xfffff800ffffffffffc00007ffffe3fffff0007fff033821e7e1e3ff83e7e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zbc:W:=0x3878003c7800007c000001ffe0003ffff00003e001182183e063860383e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zbd:W:=0x3f87f80f03f81ff803c003ffe01fe3fe000ffffc1f0379196719edb18e661f98667e65dcee67b396f73bfb966086a15a8c4667369617ff116718f6def6461598
def zbe:W:=0xffffffffffffffffffffffffe01fe3fe000ffffc1f03ff196719fffffe661f98667e65dcee67b396f73bfb966086a15a8c4667369617ff116718f6def6461598
def zbf:W:=0x3f87f80f0000000000000007ffffffffffffff80000340fe0001ec0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zbg:W:=0x387fff0ffffe1c07fffc03ffffe003fffff0007ffffd592187fe6f8fcf87e1ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zbh:W:=0x7e01fe3fe000ffffc1f0000196718000002661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zbi:W:=0x3807800f03801c0003c003fe1e1e1fc1e00f007ffffc4106049e0c018c1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zbj:W:=0x7f80003f8000003c00007ffe003fffff0007fe001182187e061818387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zbk:W:=0xc07ffff0ffffe007fffffc07ffe003fffff0007fe0019e2187e073cff387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zbl:W:=0x387fff0ffffe1c07fffc03fffffe03ffffff007fff01592187f86f8fcf87f9f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zbm:W:=0x3f80000003f81ff800000007fffffc000000007ffffe20c1f80181b003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zbn:W:=0xc07ffff0ffffe007fffffc07ffffe3fffff0007fff019e21e7e073cff3e7e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zbo:W:=0x379fffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zbp:W:=0xc07807f0fc07e007fc3ffc0000000000000000000003fffffffe124e70000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zbq:W:=0x3f87f80f00000000000000001fe01c01fff00000000340e60001ec000199e000bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zbr:W:=0x3f87f80f000000000000000000000000000000000003ffffffffec0000000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zbs:W:=0x7ff80000000007ffc000001fe003fffff000000001182007e0600f8187e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zbt:W:=0xc07ff800ffffffffffc00007ffffe3fffff0007ffffd3821ffe063ff83e7e1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zbu:W:=0x3ff8003c7800007c000001ffe0003ffff0000000011821836063860383e000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zbv:W:=0x3f80000f000000000000000000001c00000000000002e7de781f8c0000180000bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zbw:W:=0xff80000003f81ff800000007fffffc000000007ffffe20c1f80181b003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zbx:W:=0xff800000fffffffffc3ffc07fffffc000000007ffffe26c1f80183fe73f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zby:W:=0x3847870fff87fc07fffffffe1e1e1fc1e00f007ffffc4706049e0e4ffc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zbz:W:=0x7ff80003f8000003c00007ffe003fffff0007fe001182187e061818387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zbA:W:=0x7ff800ffffe007fffffc07ffe003fffff0007fe0011e2187e063cff387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zbB:W:=0x3f9fffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zbC:W:=0xfc07e007fc3ffc0000000000000000000003fffffffe024e70000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zbD:W:=0xfffffffffffffffffffffff800000000000000000003fffe98e7fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zbE:W:=0x3f87f80f03f81ff803c003f81fe01c01fff00000000379e60001edb18d99e000bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zbF:W:=0x39fffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zbG:W:=0xc07807f00000000000000007e01fe3fe000fff80000080180000100002661e000000000000000000000000000000000000000000000000000000000000000000
def zbH:W:=0x3f87f80ffc07e007fc3ffc001fe01c01fff0007c1f0346e76719ee4e7199e198fd6d57bacc26a152b519b957799fb37b9b4eff3696d7c4ff6719be4c62febf98
def zbI:W:=0xc07ff800ffffe007ffc00007ffffe3fffff0007fff011821e7e063cf83e7e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zbJ:W:=0xfff807f0fffffffffc3ffc07fffffffe000ffffffffea6d9ff1993fe73fe1fffd0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zbK:W:=0xff800000fffffff8000000001fe01c000000007ffffe20c1f80183f0019801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zbL:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffd592607fe0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zbM:W:=0x7ff800fff80007ffc00007ffffe3ffffffffffe001183987e0638f83e7ffe0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zbN:W:=0x3ffe7fffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zbO:W:=0x7e01fe3fe000fff800003fffffffe000002661e00040040880000020000030200000000001000c0000003ef7a292a000000000000
def zbP:W:=0x3f87f80ffffffffffffffff8000000000000000000037f000001effffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zbQ:W:=0xc07807f0fc07e007fc3ffc00001fe000000fff801f0086186018124e70601e184000011008062010840928104006204200024524021404106118004060401418
def zbR:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff019e39e7f873cff3e7fff8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zbS:W:=0x3f800000fffffff800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zbT:W:=0x7ff8003c7800007c000007ffe003fffff0000000011821836063860387e000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zbU:W:=0xc07807f0ff87fc07ffffffffe01fe3fe000ffffffffc8719679e124ffe661fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zbV:W:=0xc07ffff0fff80007ffc00007ffe003fffff0007fe001982187e0738f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zbW:W:=0x3f800000fffffff8000000001fe01c000000007ffffe20c1f80183f0019801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zbX:W:=0xfffffffffffffffffffffff800000000000000000003ffc1f801fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zbY:W:=0xfff807f0fffffff800000007fffffffe000ffffffffea0d9f80193f003fe1fffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zbZ:W:=0x3807800fc3861c0783fc03f81e001c01e000007ffffc4106049e0c09cc1981ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zb0:W:=0xc07ffff0ffffe007fffffc07ffe003fffff0007fe001182187e073cff387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zb1:W:=0xffffffffc380000783c00007ffffffffffffff800003c0fe0001fc0983fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zb2:W:=0xf87f87ffc3861c0783fc03fffe1fffffe00ffffffffcc11e049e1c09ce7f9fff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zb3:W:=0x7f800fff80007ffc000001fe00001fff0007fe001182187e0638f8181e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zb4:W:=0x7ffffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zb5:W:=0xffffffffc3861c0783fc03f800000000000000000003fffffffffc09cc000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zb6:W:=0xffffffff0000000000000007ffffffffffffff800000003e0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zb7:W:=0xc07807f0000000000000000000000000000000000003fffffffe100000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zb8:W:=0xc07807f0fc07e007fc3ffc000000000000000000000086000000124e700000000000000000000000000000000000000000000000000000000000000000000000
def zb9:W:=0x37fe7fffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zca:W:=0xc07807f03c01e0007c03fc07e01fe3fe000fff80000086196300124632661e00400800108c24a012240930046084a11200424632121004116308024422420488
def zcb:W:=0xc07807f00000000000000007e01fe3fe000fff800003fffffffe100002661e00040040880000020000030200000000001000c0000003ef7a292a000000000000
def zcc:W:=0xff8007ff0007fff8003ffff800000000000000000003ffffffff9c707c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zcd:W:=0xffffffff03f81ff800000007ffffffffffffff800003e0fe0001fdb003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zce:W:=0x7ffffffffffffff80000000fe0000000003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zcf:W:=0x47870fc006000783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcg:W:=0x3800070fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zch:W:=0x3fc7870fc3fe1fff83fc03fe1e1e1fc1e00f007ffffe6106049f8db9cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zci:W:=0x7ff800fc000007ffc00007ffe003fffff0007c0001182107e0620f8387e180005a8800e6a88087399050a622a0819cc464021ad408100106c0428f820741c0
def zcj:W:=0xff8007fffffffffffffffff8000000000000000000003f0000019ffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zck:W:=0x7807f000000007fc3ffc00000003fe000fff80000086180718100e70061e000048011044022002951918122002214a80464314860404102718000c60061510
def zcl:W:=0xfffff800ffffffffffc00007fffffffffff0007fffff38e1ffe1e3ff83ffe1ffd0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zcm:W:=0xffffffffffffffffffffffffffe003fffff000000003ff200001ffffff87e000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zcn:W:=0x3ffff800fff81fffffc00007ffe003fffff0007fe003382187e1e3bf8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zco:W:=0x387f87ffc3861c07fffffffe1e1e1fc1e00f007ffffcc706049e1c0ffc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcp:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086186018124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zcq:W:=0xfffffffffffffffffffffff800000000000000000003ff2187e1fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zcr:W:=0x7807f0c0060007fc3ffc07e01fe3fe000ffffc1f0086196718100e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zcs:W:=0x7f800fff8000003c00007ffe003fffff0007fe001182187e063818387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zct:W:=0x7ffff0fff80007fffffc07ffe003fffff0007fe0019e2187e0738ff387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zcu:W:=0xffffffff0007fff8003fffffffffffffffffff800003e7fe0001fc707ffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zcv:W:=0xfffffffffffffffffffffff80000000000000000000000000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zcw:W:=0x7807f00000000000000000000003fe000fff800003fffffffe100000061e00040040880000020000030200000000001000c0000003ef7a292a000000000000
def zcx:W:=0x7f80f0000000000000007ffffffffffffff80000140fe00006c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zcy:W:=0xfffffffffffffffffc3ffc07ffffffffffffff800003e6fe0001fffe73fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zcz:W:=0x7800f0000000003c003fe1e1e1fc1e00f007ffffc4106049e0c018c1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcA:W:=0x7f8000000000003c00007ffe003fffff0007fe001182187e060018387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zcB:W:=0xfffffff0fffffffffffffc07ffe003fffff0007fe003be2187e1f3fff387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zcC:W:=0x2e7de781e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zcD:W:=0xfff807f0fffffffffc3ffc0000000000000000000003ffffffff93fe70000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zcE:W:=0x159fffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zcF:W:=0xffffffff0000000000000001e1ffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zcG:W:=0xfffffffffc07e00000000007ffffffffffffff800003c0fe0001fe4003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zcH:W:=0x3847870f03801c0783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcI:W:=0x387fff0fc3861c0783fc03fffffe1fffffff007ffffd4126049e6c09cf9ff9ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcJ:W:=0xc00007f0fc07e007fc3ffc00001fe000000ffffc1f0086196718124e70601f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zcK:W:=0x7ff80003f80007ffc00007ffe003fffff0007fe001182187e0618f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zcL:W:=0x7ff80003f80007ffc00007ffe003fffff00003e001182087e0618f8387e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zcM:W:=0xff800000fffffff800000007fffffc000000007ffffe20c0f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zcN:W:=0x3ffffffffffffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zcO:W:=0x3847870fc3861c0783fc03f81e001fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcP:W:=0x3f87f80f007803f8000000001fe01c01fff00000000378e60001edb00199e000bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zcQ:W:=0xf847870fff87fc0783fc03fe1e1e1fc1e00f007ffffc4106049e0e49cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcR:W:=0xfffffffffffffffffffffff800000000000000000002e7000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zcS:W:=0x3847800fc3801c0783c003fe1e1e1fc1e00f007ffffc4106049e0c098c1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zcT:W:=0xc07807f03c01e0007c03fc07e01fe3fe000fff80000086180000124632661e000000000000000000000000000000000000000000000000000000000000000000
def zcU:W:=0x7fffff0000000000000001e1e1e3ffffffff800001c0fe00007c0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zcV:W:=0x3f800000fffffff8000000061ffe1c000000007ffffe20c1f80183f0019801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zcW:W:=0xfff80007ffc00000000000000000007fe000180187e0038f800001e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zcX:W:=0xfffffffffffffff800000007ffffffffffffffffffffe0fe0001fff003ffffffbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zcY:W:=0xfff807f0fffffffffc3ffc07fe1ffffe000ffffffffea619671993fe727e1fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zcZ:W:=0xc07ffff0ffffe007fffffc07fffe03ffffff007fff019e2187f873cff387f9f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zc0:W:=0xc7b878f00000000000000007ffffffffffffff80000380fe0001f00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zc1:W:=0xffc7870fffffffff83fc03fffffffc000000007ffffe61c1f8018ff9cff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zc2:W:=0xc7b878f03c79e3f87c03fc0000000000000000000003be000001f3f630000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zc3:W:=0xffffffff0000000000000007ffffffffffffff800003f9fff8e7fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zc4:W:=0x7ff8000000000000000007ffe003fffff0000000010020000060000387e0000000000000000000000000000000000000000000000000000000000000000000
def zc5:W:=0xfffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zc6:W:=0xffffffff0000000000000007ffffffffffffff800003f9fe98e7fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zc7:W:=0xc03800f03c01e0007c03fc07e01fe3fe000ffffc1f0086196718124632661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zc8:W:=0xffffffffc3861c0783fc03ffffffffffffffff800003c1fe0001fc09cffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zc9:W:=0xc78000003c79e3f800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zda:W:=0xf87f87ffff87fc07ffffffffe01fe3fe000ffffc1f00c71967181e4ffe661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdb:W:=0x3878003c7800007c000007ffe003fffff0007fe001182187e063860387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zdc:W:=0xc07807f03c01e0007c03fc01e001e3fe000fff80000086196300124632661e00400800108c24a012240930046084a11200424632121004116308024422420488
def zdd:W:=0x387fff0ffffe1c07fffc03ffffe003fffff0007fe001592187e06f8fcf87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zde:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f019e39e7f8124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdf:W:=0x7807f000000007fc3ffc07e01fe3fe000fff80000086180718100e72661e000048011044022002951918122002214a80464314860404102718000c60061510
def zdg:W:=0x3befffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zdh:W:=0xc00007f0fc07e007fc3ffc00001fe000000ffffc1f0086186018124e70601f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdi:W:=0x3847870fc3861c0783fc03f800000000000000000003fffffffe0c09cc000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zdj:W:=0xc07ffff0fc07e007fc3ffc07ffffe3ffffffffffff018639e7f8724e73e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def zdk:W:=0x3ffff80ffffffffffffffff8000000000000000000037f000001effffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zdl:W:=0xffffffff0000000000000007ffffffffffffff800003d8fe80e1fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zdm:W:=0xffffffff0000000000000007ffffffffffffff800003c1fe049ffc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zdn:W:=0xfffffffffffffffffffffff800000000000000000003be000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zdo:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fff80000086196300124e72661e00400800108c24a012240930046084a11200424632121004116308024422420488
def zdp:W:=0x387fff00fffe1c07fffc0007fffe1fffffff007ffffd182187f8638fc39ff9ff005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zdq:W:=0x7ff800fff80007ffc00007ffe003fffff0007ffffd182187fe638f8387e1ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zdr:W:=0xc07807f03c01e0007c03fc07e01fe3fe000ffffc1f0086196718124632661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zds:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00118218760638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zdt:W:=0xc07807f0ff87fc07ffffffffe01fe3fe000ffffc1f0087196718124ffe661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdu:W:=0x7ff800fffe1c07fffc03ffffe003fffff0007fe001192187e0638fcf87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zdv:W:=0x3fefffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zdw:W:=0xfffffffffffffffffffffff8000000000000000000013f000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zdx:W:=0x7ff800fffe1c07fffc03ffffe003fffff0007ffffd192187fe638fcf87e1ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zdy:W:=0x7807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdz:W:=0xffffffff3c7ffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zdA:W:=0xf84787ffc3861c0783fc03fe1e1fffc1e00ffffffffcc11e049e1c09cc7d9fff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zdB:W:=0x3f87f80f03f81ff803c003f81fe01c01fff00003e0ff79e60087edb18d99e067bf37f6ef22c117c54266c3e11b1916a13f29b80821cbfbee0085fc939cb9aa44
def zdC:W:=0x7807f000000007fc3ffc01e001e3fe000fff80000086196718100e72661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdD:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086180418124e72661f980040010040020000911008120002004880040104840400000410000840041110
def zdE:W:=0x3ff807f003f81ffffc3ffc001fe01ffe000fff83e0fea6d89f1991be719e1e6790c801105512686295191813b452694a82c653558ea40490b719012c61ae1532
def zdF:W:=0x3efffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zdG:W:=0x7f8003ff800007fc000001fe00001fff00003e001182183e063878181e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zdH:W:=0xc07ffff0ff87e007fffffc07ffffe3ffffffffffff0186396798724ff3e7fff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zdI:W:=0xfffffffffffffffffffffff8000000000000000000003e000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zdJ:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc590787fe0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zdK:W:=0xf87f87ffff87fc07fffffffffe1fffffe00ffffffffcc71f679e1e4ffe7f9fff48498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def zdL:W:=0xfffffffffffffffffffffff800000000000000000003fffe049ffffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zdM:W:=0xc7b878f0c3861c0783fc03f9e1e1e03e1ff0ffffffff81f8049ff009cfe267ffb564d5ab4082054191548933131314e9ba2db10ca58fc0ea0495b40948ad3354
def zdN:W:=0xc7800000fffffff800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zdO:W:=0xc03800f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdP:W:=0xf87f87fffc07e007fc3ffc07e01fe3fe000ffffc1f00c61967181e4e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdQ:W:=0x3847870f000000000000000000000000000000000003fffffffe0c0000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zdR:W:=0x387fffff0000000000000007ffffffffffffff800001c0fe00007c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zdS:W:=0xffffffff3c79e3f800000007ffffffffffffff800003e0fe0001fff003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zdT:W:=0xc7f807f0fc7fe3fffc3ffc07e01fe3fe000ffffc1f02a619671993fe72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zdU:W:=0xc7fff800fff9e3ffffc00007ffe003fffff0007fe003382187e1e3ff8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zdV:W:=0x3807800fc3861c0783fc03fe1e1e1c01e000007ffffc4106049e0c09cc1981ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zdW:W:=0x47870fc380000783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zdX:W:=0xc07807f0c0060007fc3ffc07e01fe3fe000ffffc1f0086180718100e72661f980048011044022002951918122002214a80464314860404102718000c60061510
def zdY:W:=0xffb878f00000000000000007ffffffffffffff80000380fe0001f00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zdZ:W:=0xffffffff0000000783fc03ffffffffffffffff800003c1fe0001fc09cffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zd0:W:=0x7ff800ffffffffffffffffffe003fffff0007fe001182187e063ffff87e1e0025aa844f7e990a77bb050a6a6a0819cc4e4025ad428100186c0439f970741e0
def zd1:W:=0x387800fff800007c000007ffe003fffff0007fe001182187e063860387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zd2:W:=0xc07807f0fc07e0007c03fc07e01fe3fe000ffffc1f0086196300124632661f98400800108c24a012240930046084a11200424632121004116308024422420488
def zd3:W:=0xffffff0ffffffffffffc03ffffe003fffff0007fe003792187e1efffcf87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zd4:W:=0xffc7870fffffffff83fc03f800000000000000000003ffffffff8ff9cc000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zd5:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f02a6d9ff18124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zd6:W:=0xfffffffffffffffffffffff80000003e1ff0ff800003ff380001fffffc026600273674ee224113844222c380010110211c08a0000003fb6a0000f49294002200
def zd7:W:=0xff800000fffffff800000001ffe1fc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zd8:W:=0xffffffff0000000000000007ffffffffffffff800002c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zd9:W:=0xffffffff0000000000000007ffffffffffffff80000000000001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zea:W:=0x3878f000000000000000000000003e1ff0ff800003fffffffe700000026600252454aa0000030000038300010110211808e0000003ef7a292ab40000002200
def zeb:W:=0xc07807f0fc07e007fc3ffc07fe1fe3ffe00fffffff0086196798124e72679ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zec:W:=0x7ff800000000007c000007ffe003fffff0000000011820036060060387e000001a080026080086088050802020010444400210400010000240408680024000
def zed:W:=0xc07807f000000007fc3ffc00001fe3fe000fff80000086180718100e70661e000048011044022002951918122002214a80464314860404102718000c60061510
def zee:W:=0x3ff80003f800007fc000001fe0003ffff00003e001182083e061878183e060001a8800378800a7088050a0a620018444e002584028100082c0418781034060
def zef:W:=0xc03807f00007e0007c3ffc00001fe03e000fff801f0086186318104670621e18400801100c062012840938106006214200424734021404106318004460421418
def zeg:W:=0xfffffffffffffffffffffff8000000000000000000019e000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zeh:W:=0xffffffff0000000000000007ffffffffffffff80000180380001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zei:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f02e7dfff9e124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zej:W:=0xfffffffffc07e007fc3ffc0000000000000000000003fffffffffe4e70000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zek:W:=0x38000000c3861c00000000061e1e1c000000007ffffc000000000000001801ff0000000000000000000000000000000000000000000000000000000000000000
def zel:W:=0x7fff00fffe0007fffc0007fffe03ffffff007fff01182187e0638fc387f9f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zem:W:=0xffffffff0000000000000001e1e1e3ffffffff800003c0fe0001fc0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zen:W:=0xfffffffffffffffffffffff800000000000000000003ff2787fffffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zeo:W:=0xc07807f0fc07e007fc3ffc01e001e3fe000fff80000086196718124e72661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zep:W:=0xc07807f0fc07e007fc3ffc07fe1ffffe000ffffffffc86196718124e727e1fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zeq:W:=0x7ff80000000007ffc00007ffe003fffff000000001182187e0600f8387e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zer:W:=0xffffffffff87fc07ffffffffffffffffffffff800003c7fe0001fe4ffffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zes:W:=0x387ff800fffe1c07ffc00007ffe003fffff0007fe001182187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zet:W:=0x7ff8003c780007ffc00007ffe003fffff000000001182187e0638f8387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zeu:W:=0x7ff800fffe1c07ffc00007ffe003fffff0007ffffd182187e0638f8387e1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zev:W:=0x3ff8003c7800007fc00001e1e0003ffff000000001182183e063878383e000001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zew:W:=0xc07807f03c01e007fc3ffc07e01fe3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zex:W:=0xc3861c0000000000000000000000007ffffffffffffe0000000001ff040040880000020000030200000000001000c0000003ef7a292a000000000000
def zey:W:=0xfffffffffffffffffffffff8000000000000000000001f000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zez:W:=0xfffffffffffffffffffffffe1e1e1c00000000000003ff000001fffffc180000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zeA:W:=0x3800000000000000000000061e1e1c00000000000003fffffffe000000180000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zeB:W:=0x7ff800ffffffffffc00007ffe003fffff0007ffffd182187e063ff8387e1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zeC:W:=0xfffffc07fffffff8000000000000007ffffc1f01e7fe03cffc0001ff405a8911ffaea4b7bddd78b6e6a6a5dee4e7477ef73c1411e7dc43cfeb4755fc
def zeD:W:=0xfffffffffffffffffffffff800000000000000000003fff80001fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zeE:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00338e1ffe0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zeF:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffe61c7fc9e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zeG:W:=0x47870f0000000783fc03f8000003c1e00f000000004106049e0c09cc0598000841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zeH:W:=0xff8007ff0007fff8003ffff8001ffc00000fff800002e7de781f9c707c781e00bf2576ee0041134042238341191912211b08f80000c3effe292bbc1014b8aa00
def zeI:W:=0x3f80000003f81ff8000000001fe01c000000007ffffe20c1f80181b0019801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zeJ:W:=0xc03807f03c07e0007c3ffc00001fe000000fff801f0086186018124670601e184000011008062010840928104006204200024524021404106118004060401418
def zeK:W:=0xfffffffffffffffffffffff800000000000000000003ff06001ffffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zeL:W:=0xffffffff3c79e3fffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zeM:W:=0x3800070fc3861c0783fc03f8001e1c00000f007ffffc4106049e0c09cc1819ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zeN:W:=0xc7fffffffffffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zeO:W:=0xc03800f03c01e0007c03fc01e001e03e0000ff80000086196300124632620600400800108c24a012240930046084a11200424632121004116308024422420488
def zeP:W:=0xfffffffffffffffffffffff8000000000000000000023f000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zeQ:W:=0x7ff800fffe0007ffc00007fffe03fffff0007fff01182187e0638f8387e1f8005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zeR:W:=0xf87807f0fc07e007fc3ffc07fe1ffffe000ffffc1f0086196718124e727e1f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zeS:W:=0x3f800000c3fe1ff800000007fffffc000000007ffffe20c1f80181b003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zeT:W:=0x61e1e1fc1e00f007ffffc0006049e0000001d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zeU:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086186418124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zeV:W:=0x7ff800fff80007ffc000001fe00001fff0007fe001182187e0638f8181e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zeW:W:=0x13ffffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zeX:W:=0xffc7870ffffffffffffffff8000000000000000000027f0000018ffffc000000021220442241128442224280000000000400000000003b000000409294000000
def zeY:W:=0xffffffff0000000000000007ffffffffffffffffffffc0fe0001fc0003ffffffbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zeZ:W:=0xffb800f0fffffff87c03fc07fffffc000000007ffffea6c1f80193f633f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def ze0:W:=0x47f800c3f8000783c00007ffe003fffff0007fe001182187e061898387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ze1:W:=0xc07ff8f0fff9e007ffc3fc07ffe003fffff0007fe0019e2187e073cfb387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ze2:W:=0xc03800f03c01e0007c03fc0000000000000000000003fffffffe124630000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def ze3:W:=0x7f800fff80007ffc00007ffe00001fff0007fe001182187e0638f8381e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ze4:W:=0xf87ff800fffffc07ffc00007fffffffffff0007ffffd1821e7e063cf83ffe1ff405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def ze5:W:=0x7800000000000000000007e00003fe000000000003fffffffe000002060000040040880000020000030200000000001000c0000003ef7a292a000000000000
def ze6:W:=0xc03800f00000000000000001e001e03e0000ff800003fffffffe100002620600040040880000020000030200000000001000c0000003ef7a292a000000000000
def ze7:W:=0xfffffffffffffffffffffff800000000000000000003ffe69cfffffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def ze8:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001592787fe638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ze9:W:=0xffffffff0000000000000007ffffffffffffff800001c03e0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zfa:W:=0xc7f87ff00000000000000007ffffffffffffff80000380fe0001f00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zfb:W:=0xffffffff0000000000000007ffffffffffffff800003dffe0001fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zfc:W:=0x7ff800fff80007ffc000001fe003fffff0007fe001182187e0638f8187e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfd:W:=0xff87800ffffffff803c003fffffffc000000007ffffe61c1f8018ff18ff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfe:W:=0x787800fc780007fc000007ffe003fffff0007fe001182187e0638e0387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zff:W:=0x387ff80ffff81c07ffc003ffffe003fffff0007fe001592187e06f8f8f87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfg:W:=0x7ff800fff81c07ffc003ffffe003fffff0007fe0fd192187e6638f8f87e1e7005a8801f7a884a739d450a6a6a0859ce4e5025af528100186c4438f8b0741e4
def zfh:W:=0xfffffffffffffffffffffff81e001c0000000003e0ffff000001fffffc180067263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zfi:W:=0x7fffff00000007fffffff800000000000000000001df0000007c0ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zfj:W:=0xc7800000fc7fe3f800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfk:W:=0x7ff800fc780007ffc00007e1e003fffff0007c0001182187e0638f8387e180005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfl:W:=0x3800000003801c00000000001e001c0000000003e0fffffffffe000000180067040040880000020000030200000000001000c0000003ef7a292a000000000000
def zfm:W:=0x7800000007803f800000007fffffc000000007ffffe20c1f80181b003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfn:W:=0xffffffffffffffffffffffffe00003fe000000000003ff000001fffffe060000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zfo:W:=0x7fff0ffff80007fffc03ffffe003fffff0007fe001592187e06f8fcf87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfp:W:=0x78000078000000000007ffe003fffff0007fe001182187e061800387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfq:W:=0x338fffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zfr:W:=0xf87f87ffff87fc07fffffff800000000000000000003fffffffe1e4ffc000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zfs:W:=0xc07807f0fc07e007fc3ffc00001fe000000fff80000086180000124e70601e000000000000000000000000000000000000000000000000000000000000000000
def zft:W:=0xc07807f0fc07e007fc3ffc00001fe000000fff801f0086196718124e70601e184000011008062010840928104006204200024524021404106118004060401418
def zfu:W:=0xff8000003c79e3f800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfv:W:=0xfffffffffffffffffffffff800000000000000000002ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zfw:W:=0xc07807f0ffffe007fc3ffc07ffffe3fe000fffffff019e39e7f813ce73e61ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zfx:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00379e7fffe638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfy:W:=0xff87f80f0000000000000007ffffffffffffff80000340fe0001ec0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zfz:W:=0x3847870fc3861c0783fc03fe1e1e1fffffff007ffffc412607fe0c09cc1ff9ff08498b01448a040399d418722a2a07cce1650b1ce54c000406d4080d4817d954
def zfA:W:=0xf87f87ffff87fc07fffffff800000000000000000000c70000001e4ffc0000000000000000000000000000000000000000000000000000000000000000000000
def zfB:W:=0xf83f80ff3f81fc007fc3fff9fe01fc3fe000ff83e0fcc71f63861e47be7b8667480982118ca4a413244d30646a8ca79221634e3a33580415638c0a452a538ccc
def zfC:W:=0xffc00700ffffffff803c0007fffffc000000007ffffe20c1f80183f843f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfD:W:=0x3ff8003ff800007fc00007ffe003fffff0007fe001182187e063878387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfE:W:=0x400700c0060007803c000000000000000000000003fffffffe000840000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zfF:W:=0x7fff00fff80007ffc00007fffe03ffffff007fe001182187e0638f8387f9e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zfG:W:=0x3ff800fff800007fc00007ffe0003ffff0007fe001182183e063878383e1e0001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zfH:W:=0x3847870ffffe1c0783fc03fe1e1e1fc1e00f007ffffc4106049e0f89cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zfI:W:=0xff8000003ff9fff800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfJ:W:=0xffffffff3ff9fffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zfK:W:=0x3878000000000000000007ffffffffffffff80000100fe0000600003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zfL:W:=0xffffffff0000000000000001ffe1ffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zfM:W:=0xff800000fffffff800000007fffffffe000ffffffffe20d9f80183f003fe1fffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfN:W:=0x47800000000000000000061e0003c1e00000000003fffffffe000000058000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zfO:W:=0xffc7870ffffffff800000007fffffc000000007ffffe60c1f8018ff003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zfP:W:=0xffffffffc006000000000007fffffffffffffffc1f03c0fe0001fc0003ffff98bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zfQ:W:=0x7fff00fffe0007fffc0007fffe03ffffff007fff01182187f8638fc387f9f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zfR:W:=0x118fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zfS:W:=0x7ff8000000000000000007ffffffffffffff80000100fe0000600003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zfT:W:=0xfffffffffffffff8000000000000000000003f00000003fffc000000021220442241128442224280000000000400000000003b000000409294000000
def zfU:W:=0x7807f000000007fc3ffc00001fe3fe000fff801f0086186718100e70661e18404801104c062012951938126006214a80464734861404106718004c60461518
def zfV:W:=0xfff807f0fffffffffc3ffc07ffffe3fe000fffffff02a619e71993fe73e61ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zfW:W:=0xf87f87ffff87fc07fffffffffe1fe3ffe00fffffff00c71967981e4ffe679ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zfX:W:=0xffffffff0000000000000007ffffffffffffff800003ffff87e1fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zfY:W:=0x3fffffff0000000000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zfZ:W:=0x7f800fff8000003c00007ffe00001fff0007fe001182187e063818381e1e000128800b3a880a5288040a486a0809444a0004a5028100180c04383830140e0
def zf0:W:=0xfff807f0fffffff800000007fffffc000000007ffffea0c1f80193f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zf1:W:=0xff8007ff0007fff8003fffffffe003fffff0007fe002e72187e19c707f87e1e0266cecccd5e993237bb29326a6a0819cc8e4225ad42beb0186c0b71d170741e0
def zf2:W:=0xff8007ff000000000000000000000000000000000003ffffffff9c0000000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zf3:W:=0x7ff800fff80007ffc00001e1e003fffff0007fe001182187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zf4:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff011821e7e073cff3e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def zf5:W:=0xc07f87f0ff87fc07fffffffffe1fe3ffe00ffffffffc8719679e124ffe679fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zf6:W:=0xfffffffffffffffffffffff800000000000000000003ffff87e1fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zf7:W:=0xff8007fffff80007ffc00000001ffc00000fffffe002d8df87e19f8f80781fe0bd7fdeaaf7a881e73990d1e7bfb993bddfecba5ad4ebd0ef86c1ff8f83bfebe0
def zf8:W:=0xffffffff0000000000000007ffffffffffffff800003c0fe049ffc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zf9:W:=0xc07807f03c07e007fc3ffc01e01fe3fe000fff801f0086196718124e72661e1840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zga:W:=0xc07807f0ffffe007fc3ffc07ffffe3fe000fffffff008619e71813ce73e61ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zgb:W:=0xff8007fffffffffffffffff800000000000000000002ff0000019ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zgc:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fff801f0086186018124e72661e184000011008062010840928104006204200024524021404106118004060401418
def zgd:W:=0xff800000fffffff800000007fffffffffff0007ffffe20e1f80183f003ffe1ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zge:W:=0x3800070fc3861c0783fc03f8001e1c00000f007ffffc4106001e0c09cc1819ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zgf:W:=0xc07807f0fc07e007fc3ffc00001fe000000ffffc1f0086196718124e70601f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zgg:W:=0xc07807f0fc07e007fc3ffc07ffffe3fffffffffc1f0086396718124e73e7ff9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zgh:W:=0x3ffdffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zgi:W:=0x7ffe003fffff000000003fffffffe00000387e000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zgj:W:=0xc07ffff0fc07e007fc3ffc07e01fe3fe000ffffc1f0186196718724e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zgk:W:=0xff800000fffffff800000000001ffc000000007ffffe20c1f80183f0007801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zgl:W:=0x7807f000000007fc3ffc07e01fe3fe000ffffc1f0086180718100e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zgm:W:=0xfffffffffffffffffffffff8000003fe000fff800003ff180001fffffc061e00263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zgn:W:=0xfffff800fffffff800000007fffffffffff0007fffff20e1f801e3f003ffe1ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zgo:W:=0x7f80003f8000003c000001fe00001fff00003e001182187e061818181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zgp:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc000000000c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zgq:W:=0x7ff800fff80007ffc00007fffe1ffffff0007ffffd182187e0638f839fe1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zgr:W:=0xfffff800fff80007ffc00007ffe003fffff0007fe003182187e1e38f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zgs:W:=0xffffffff00000007fc3ffc07ffffffffffffff800003c6fe0001fc0e73fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zgt:W:=0xffffffff03801c0000000007ffffffffffffff83e0ffc0fe0001fc0003fffe67bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zgu:W:=0xc7b878f03c79e3f87c03fc061e1e1fc1e00f007fffffbe06049ff3f6301d99ff2e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def zgv:W:=0xc07807f0fc000007fc3ffc07e01fe3fe000ffffc000086190718120e72661f8000480110c422a002b51918162082a15a80464316960404112718020c62061590
def zgw:W:=0xfc07e007fc3ffc00000000000000007c1f0006016718024e7000019840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zgx:W:=0x387800000000007c000007ffe003fffff0007fe001182187e060060387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zgy:W:=0x2ffdffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zgz:W:=0xff800000fffffff800000007fffffc000000007ffffe61c7fc9f83f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zgA:W:=0xffffffff0000000000000007ffffffffffffff80000000f80001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zgB:W:=0xffffffffffffffff83fc03ffffffffffffffff800003e1fe0001fff9cffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zgC:W:=0xc00000000000000000000007e01fe000000000000003fffffffe000002600000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zgD:W:=0x7ff800fff81fffffc00007ffe003fffff0007fe0fd38219fe063bf8387e1e700da8800f7b8c8a7399050a6a6e0c99cc4e4025bdc28100196c043af830741e2
def zgE:W:=0xffffffff0000000000000007ffffffffffffff800003c0ff8001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zgF:W:=0x37ffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zgG:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe0013821ffe0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zgH:W:=0xfffffffffffffffffffffff80000000000000000000000fffffffffffc00000022362444224111844221c180000000001c00e0000000147a292af49294000000
def zgI:W:=0xff87ffff0000000000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zgJ:W:=0x387fff0ffff80007ffc00007ffe003fffff0007fe001582187e06f8f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zgK:W:=0x3847870fc3861c0783fc03fffffe1fffffff007ffffc4126049e0c09cf9ff9ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zgL:W:=0xc007fff003ffe00003fffc001fffe001ffffff83ff019e38e0f871c1f1e1fe78401289103b8e20b58c8968b0c62620c644a2456c423c1410e1d841c3e1415478
def zgM:W:=0xfffffffffffffffffffffff800000000000000000003fffe0001fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zgN:W:=0xfffffffffff80007ffc00007ffffffffffffffffe003d8ff87e1ff8f83ffffe0bd7fdeaaf7a881e73990d1e7bfb993bddfecba5ad4ebd0ef86c1ff8f83bfebe0
def zgO:W:=0xc7b878f0000000000000000000000000000000000003fffffffff00000000000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zgP:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00000000000638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zgQ:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe002e7de781e638f8387e1e0045ac888f7a882a7399352a6a6a0819cd4e4c25ad42bff7bafea438f830741e0
def zgR:W:=0xffc7870fc387ffff83fc03fe1e1e1fc1e00f007ffffe6106049f8c79cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zgS:W:=0xc07807f0000000007c03fc07e01fe3fe000fff80000086180300100632661e000008001004002002040910002000210200424210020004102308000420020400
def zgT:W:=0x7fffff00000007fffffff8000003c1e00f00000001df3e07fe7c0ffc0598002e77e7cd62c31785d377cbf20a0a06c8bd25e90ca54fff7e2dbefc9bdc159954
def zgU:W:=0xff8007fffffffff8003ffff800000000000000000003ffffffff9ff07c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zgV:W:=0xff8000000007fff80000000000000000000000000003ffffffff807000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zgW:W:=0x379e7f8e600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zgX:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0000000000124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zgY:W:=0xffffffff03801c0003c003ffffffffffffffff800003c1fe0001fc018ffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zgZ:W:=0x7ff80000000007ffc00000000003fffff000000001182007e0600f8007e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zg0:W:=0xfffffffffc07e007fc3ffc07fffffffffffffffc1f03c6ff6719fe4e73ffff98fd6d57bacc26a152b519b957799fb37b9b4eff3696d7c4ff6719be4c62febf98
def zg1:W:=0xfffffffffffffffffffffff9e001e03e0000ff800003ff180001fffffe620600263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zg2:W:=0xfffffffffffffff8003fffffffffffffffffff800003e7fe0001fff07ffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zg3:W:=0xffffffff0000000000000007ffffffffffffff800003c1fe001ffc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zg4:W:=0x7ff800fff80007ffc00001e1e003fffff000000001182187e0638f8387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zg5:W:=0x7fff8003ffff800000000000000000003fffffffe00707c000000060060cc0041120042230200000000001000c0000003ef7a292a001014000000
def zg6:W:=0x3807800fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zg7:W:=0xc03800f0fc07e0007c03fc07e01fe3fe000ffffc1f0086196718124632661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zg8:W:=0xfffffffffffffffffffffff80000000000000000000086000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zg9:W:=0x3bef9fb60000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zha:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc410000000c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhb:W:=0xfffffffffffffffffffffff8000003fffff000000003ff200001fffffc07e000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zhc:W:=0xfffffffffffffffffffffff800000000000000000003ffe7f8e7fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zhd:W:=0xfffff800ffffffffffc00007fffe1ffffff0007fffff382187e1e3ff839fe1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zhe:W:=0xc00007f0fc07e007fc3ffc07e01fe000000ffffc1f0086196718124e72601f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zhf:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f01df3fe7fe124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zhg:W:=0xc07f87fffc07e007ffffffffe01fe3fe000ffffc1f00c71967181e4ffe661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zhh:W:=0xffffffff0000000000000007ffffffffffffff80000340fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zhi:W:=0x3800070fc3861c0783fc03fe1e1e1c00000f007ffffc4106049e0c09cc1819ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhj:W:=0xfffffffffffffffffffffff8000000000000000000037f000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zhk:W:=0xf87f87ffff87fc07fffffffe1e1e1fc1e00f007ffffc4106049e1e4ffc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhl:W:=0x7ff8000000000000000000000003fffff000000003fffffffe60000007e000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zhm:W:=0x338fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zhn:W:=0xf87f87f0ff87fc07fffffc07fe1fffffe00ffffffffc86196798124ff27f9fff40488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zho:W:=0xffffffff0000000000000007ffffffffffffff800002c0de0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zhp:W:=0xfffffffffffffffffffffff800000000000000000003ffe1ffe1fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zhq:W:=0xffffffff0000000000000007ffffffffffffff800000c01e0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zhr:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00118e1ffe0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zhs:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086180018124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zht:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007fffff79e7fffe0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhu:W:=0xfffff8000007ffffffc00000001ffffffff000001fff38e07fe1e07f807fe01fd0da88006e9c48d7199070a37274498cc6641639cc98108056c140ef80ef414a
def zhv:W:=0x7ff800fffe0007fffc0007ffe003fffff0007fff01182187f8638fc387e1f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zhw:W:=0x3847870f0000000783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhx:W:=0xc00007f0fc07e007fc3ffc00001fe000000fff801f0086186018124e70601e184000011008062010840928104006204200024524021404106118004060401418
def zhy:W:=0x3ff01fffe00000000000004004088000002000003020000000000000040000003ef10292a000000000000
def zhz:W:=0x19efffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zhA:W:=0x387ff800ffffffffffc00007fffe1ffffff0007ffffd3821ffe063ff839fe1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zhB:W:=0xc07807f0fc07e007fc3ffc00001fe3fe000fff801f0086186718124e70661e18404801104c062012951938126006214a80464734861404106718004c60461518
def zhC:W:=0xfffffffffff8000000000007ffffffffffffff800003c0fe0001ff8003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zhD:W:=0x7ff80000780007ffc0000001e003fffff000000001182087e0618f8187e000005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zhE:W:=0xc07807f0ffffe007fc3ffc07e01fe3fe000ffffc1f008619671813ce72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zhF:W:=0x3847870f00061c0783fc03fe1e1e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhG:W:=0xc07807f0fc7fe007fc3ffc07e1ffe3fe000ffffc1f008619e71813ce73e61f9840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zhH:W:=0xfff800000000000000000000000000000003fffffffe038000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zhI:W:=0x7f80000000000000000001fe00001fff000000003fffffffe60000181e000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zhJ:W:=0xc07807f00007e007fc3ffc07e01fe3fe000fff801f0086186718104e72661e18404801104c062012951938126006214a80464734861404106718004c60461518
def zhK:W:=0xc07807f0ffffe007fc3ffc07e01fe3fe000fffffff008619e71813ce72661ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zhL:W:=0x13f21fffe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zhM:W:=0x3847870fc3861c0783fc03f8001e1fc1e00f007ffffc4106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhN:W:=0x3847870fc3861c0783fc03fffffe1fc1e00f007ffffc4106049e0c09cf9d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhO:W:=0xc00007f00007e000003ffc00001fe000000fff801f0086186018104070601e184000011008062010840928104006204200024524021404106118004060401418
def zhP:W:=0xc7800000fff9e3f800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zhQ:W:=0x3ffff80f0000000000000007ffffffffffffff80000340fe0001ec0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zhR:W:=0xc07f87f0ff87e007fffffc07ffffe3ffffffffffff008639e7f8124ff3e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def zhS:W:=0xffffffff0000000000000007ffffffffffffff800003e0fff801fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zhT:W:=0x3f800000fff81ff800000007fffffc000000007ffffe20c1f80183b003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zhU:W:=0xf84787ffc387fc0783fffffe1e1e1fc1e00f007ffffcc706049e1c49fc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zhV:W:=0xc00007f00007e000003ffc0000000000000000000003fffffffe104070000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zhW:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00118200360638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zhX:W:=0xfffffffffffffffffffffff8001fe000000fff800003ff180001fffffc601e00263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zhY:W:=0x7ff80000000007ffc00001e1e003fffff000000001182007e0600f8387e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zhZ:W:=0x3847800fc3861c0783fc03fe1e001fc1e000007ffffc4106049e0c09cc1d81ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zh0:W:=0x78078000000000000000007ffffffffffffff80000300fe0001e00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zh1:W:=0xc00007f00000000000000000001fe000000fff800003fffffffe100000601e00040040880000020000030200000000001000c0000003ef7a292a000000000000
def zh2:W:=0x7f8000000000000000007ffffffffffffff80000100fe0000600003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zh3:W:=0xfffffffffc07fffffc3fffffffffffffffffff800003e7fe0001fe7e7ffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zh4:W:=0xff800000fffffff800000007e01ffc000000007ffffe20c1f80183f0027801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zh5:W:=0xff800000fffffff800000007fffffc000000007ffffddf3e07ff83f003f801ffd48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def zh6:W:=0x3840070fc3861c0783fc03fe001e1fc0000f007ffffc4106049e0c09cc1c19ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zh7:W:=0xc07807f03c01e007fc3ffc07e01fe3fe000fff80000086196718124e72661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zh8:W:=0xffffffff00000000003fffffffffffffffffff800003c7fe0001fc007ffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zh9:W:=0xffffffff00001ff8000003ffffffffffffffff800003e1fe0001fc300ffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zia:W:=0x19efffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zib:W:=0x7ff800fff80007ffc000001fe003fffff00003e001182087e0638f8187e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zic:W:=0xff800000fffffff800000007fffffc000000007ffffe20c7fc9f83f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zid:W:=0x3f80000f00001ff8000003f800000000000000000003ffffffff8c300c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zie:W:=0xfffffffffffffff8000000000000007fff003f01e7f803fffc0001f8425aa954ffefb2b7ffbb7ab6e6a6a1dec4e6477ed63c3f11e7d843dff74755f8
def zif:W:=0x3f80000ffffffffffffffff8000000000000000000027f0000018ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zig:W:=0x3800000fc3861c0783fc03f800001c000000007ffffc4106049e0c09cc1801ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zih:W:=0x1df3f87fe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zii:W:=0xff800000fffffff800000007fffffc000000007ffffc0000000183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zij:W:=0x7ff800c3800007ffc00007ffe003fffff0007fe001182007e0600f8387e1e0005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zik:W:=0xffffffff0000000000000007ffffe3ffffffff800003c0380001fc0003e7fe0024244488000001000000810000000000080020000003c0000000b40000000000
def zil:W:=0x27fc7fffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zim:W:=0x3f800000fffffff80000000000001c000000007ffffe20c1f80183f0001801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zin:W:=0xf87807f0fffffffffc3ffc07fe1ffffe000ffffffffca619ff1813fe727e1fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zio:W:=0x3f800000c3fe1ff8000000061ffe1c000000007ffffe20c1f80181b0019801ff908000001110486000000001945048000280104108a000809001012001a80022
def zip:W:=0x387fff0ffffe1c07fffc03fffffe1fffffff007ffffd592787fe6f8fcf9ff9ff085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def ziq:W:=0xffffffff00001ff800000007ffffffffffffff8000ffe0fe1801fc3003fffe07bda556aa001049400000814119595a211b08b80108c3c0ee1001bc2000b8aa02
def zir:W:=0xc0787ff0fc07e007fc3ffc07e1ffe3fe1ffffffc1f0186396718724e73e67f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zis:W:=0xfffffffffffffc00000000000000007ffffc3e01fff803fff00001ff40da8910ffbee8b7bd9978b6e6e6e9dec4e6477fde3c1411f7d843efe34755fa
def zit:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc000086190700124e72661f8000480000c4208002311010062080811880440212940000010600020c02060180
def ziu:W:=0xfffffff00000000000000007ffffffffffffff80000380f80001f00003fffe009000000000000040000000011010000002001000008000800001000000a80000
def ziv:W:=0xff8007fffffffffffffffff800000000000000000003ff0000019ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def ziw:W:=0xff800000ffffffff83fc03fffffffc000000007ffffe21c1f80183f9cff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zix:W:=0xc07807f0fc7fe3fffc3ffc07e01fe3fe000ffffc1f00a619ff1813fe72661f9840c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def ziy:W:=0x3ff8003ff800007fc00001ffe0003ffff00003e0011821836063878383e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def ziz:W:=0xffffffff0000000000000007ffffffffffffff800003c1fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def ziA:W:=0xfffffffffc000007fc000007ffffffffffffff800003c0fe0001fe0e03fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def ziB:W:=0xffffffff0000000000000007ffffffffffffff80000280d80001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def ziC:W:=0xfff80000fffffffffc000007fffffc000000007ffffe20c1f80183fe03f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def ziD:W:=0x387f870fff861c07fffc03fe1e1e1fc1e00f007ffffc4106049e0e0fcc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def ziE:W:=0xff800000fffffff8000000001ffffc000000007ffffe20c1f80183f001f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def ziF:W:=0x3f87f80f03f81ff803c003f81fe01c01fff00003e0ff79e69801edb18d99e067bfb776ee33515be44222c3c19d595a211f88b84108e3fbee9001fdb295b8aa22
def ziG:W:=0xc07807f0ff87fc07fc3ffc07e01fe3fe000ffffffffc86196718124e72661fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def ziH:W:=0xfff80000fffffff800000007fffffffe0000007ffffe20c1f80183f003fe01ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def ziI:W:=0x7ff8003c780007ffc00007ffe003fffff0007fe001182187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ziJ:W:=0x387f870fc3861c0783fc03fffe1e1fffe00f007ffffc4106049e0c09ce1f99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def ziK:W:=0xc07807f00007e007fc3ffc00001fe3fe000fff801f0086186718104e70661e18404801104c062012951938126006214a80464734861404106718004c60461518
def ziL:W:=0x7ff80003f80007ffc000001fe003fffff00003e001182087e0618f8187e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def ziM:W:=0xc07807f0fc07e007fc3ffc07e01fe000000ffffc1f0086196018124e72601f98400001108826a010a40928144086a05200024526121404116118024062401498
def ziN:W:=0xc07807f0fc07e007fc3ffc07ffffe3ffffffffffff008639e7f8124e73e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def ziO:W:=0xc03807f0fc07e007fc3ffc01e01fe03e000ffffc1f0086196718124e72621f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def ziP:W:=0xffffffff00061c00003c03ffffffffffffffff800003c1fe0001fc004ffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def ziQ:W:=0xc07fffff0000000000000007ffffffffffffff800001c0fe00007c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def ziR:W:=0xff80070ffffffff8003c03fffffffc000000007ffffe61c1f8018ff04ff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def ziS:W:=0xc07800f0fc01e007fc03fc07e01fe3fe000ffffc1f0086196718124e32661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def ziT:W:=0x3800070f00061c00003c03f800000000000000000003fffffffe0c004c000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def ziU:W:=0xc07807f0fc01e007fc03fc07e01fe3fe000ffffc000086196700124e32661f8040480010cc24a012351930066084a11a80464632961004116708024c22460588
def ziV:W:=0x7fffffc000000007ffffc00c1f800000003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def ziW:W:=0xc07f87f0ff87e007fffffc07fe1fe3ffe00fffffff019e39e7f8124ff2679ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def ziX:W:=0xfffffffffffffffffffffffe001e00000000007c1f03ff000001fffffc000198263664cc224113844222c380000000000c0020000003fb000000f49294000000
def ziY:W:=0x4007000000000000000006001e03c0000f00000003fffffffe000000041800040040880000020000030200000000001000c0000003ef7a292a000000000000
def ziZ:W:=0xc07807f0fc07fc07fc3fffffe01fe3fe000ffffc1ffc8719671e124e7e661f9f40480111cc26a412b55d38166086a55aa0474736b7140411671c024c6a46159c
def zi0:W:=0xfffffffffc07e007fc3ffc07ffffffffffffff800003c0fe0001fe4e73fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zi1:W:=0xc7ffffff0000000000000007ffe1e3ffffffff800003c0fe0001fc0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zi2:W:=0x3bef9ffe0000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zi3:W:=0xffffffff00061c0000000007ffffffffffffff801fffc0fe0001fc0003fffe1fbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zi4:W:=0x3800000000061c0000000000001e1c00000000001ffffffffffe00000018001f040040880000020000030200000000001000c0000003ef7a292a000000000000
def zi5:W:=0x3fc7ff0ffffffffffffffff8000000000000000000037f000001effffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zi6:W:=0xc7fffff00000000000000007ffffe3ffffffff80000380f80001f00003e7fe00b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zi7:W:=0x3878003c7800007c000001e1e0003e1ff00000000118218360638603826000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zi8:W:=0xc07fffff0000000000000007ffffe3ffffffff800001c03e00007c0003e7fe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zi9:W:=0xffffffffc387ffff83ffffffffffffffffffff800003e7fe0001fc79fffffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zja:W:=0xc07f87f0ff87e007fffffc07fe1fe3ffe00fffffff0086196798124ff2679ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zjb:W:=0xc78000f00001e3f80003fc0000000000000000000003ffffffff907030000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zjc:W:=0xff800000fffffff8000000061e1ffc000000007ffffe20c0780183f0007801ffd080000008144850000020015054480002001421089000805001006000e8000a
def zjd:W:=0x3dffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zje:W:=0xff800000fffffff800000007fffffc3e1ff0007ffffe20e1fb6183f003fa61ffd08808009d3cc87228803005f4f4c91442c0167358b00081d241036403ea40aa
def zjf:W:=0xc07807f0fc07e007fc3ffc07e1ffe3fe1ffffffc1f008639e778124e73e67f9840480910dd2ea032bd993816e4a6a15ec0c64776d6340411e758034c634655b8
def zjg:W:=0xffffffff0000000000000007ffffffffffffff800003c0180001fc0003fffe00bd2556aa0000014000008141191912210b08380000c3c0840001bc0000b8aa00
def zjh:W:=0xffc787fffffffffffffffff800000000000000000002ff0000019ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zji:W:=0xc07807f0c007e007fc3ffc06001fe3fe000ffffc1f0086186718104e70661f98404801104c062012951938126006214a80464734861404106718004c60461518
def zjj:W:=0xfffffffffffffffffffffff9e1e0003e1ff000000003ff200001ffffff826000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zjk:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fff80000086196718124e72661e000000000000000000000100000000000000004000000004102108000000000000
def zjl:W:=0xf87fffff0000000000000007ffffffffffffff800001c03e00007c0003fffe000801020000000000000000400808020001000800004000040000080000108800
def zjm:W:=0xffffffff0000000000000007ffffffffffffff800003f8fe9861fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zjn:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00118218360638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zjo:W:=0x3878000000000000000001e1e0003e1ff000000003fffffffe600003826000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zjp:W:=0x47f800fff80007ffc000061fe003c1fff0007fe001182187e0638f8185e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zjq:W:=0xc78000003c79e3f80000000000000000000000000003ffffffff83f000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zjr:W:=0xffffffff0001e3f80003fc07ffffffffffffff800003e6fe0001fc7033fffe00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zjs:W:=0xfffffffffffffffffffffff800000000000000000000c7000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zjt:W:=0xff800000fffffff800000007fffffc000000007fffff79e7ffff83f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zju:W:=0x38387f0f3c7e1c007c3c03f9e1fe1c3e1fff00001ffd5927837e6f864f9a781f081b0b01b72a84a6a8c458d4acaa875465c10b567164100582544b86cb12d8b4
def zjv:W:=0x3800f0000000007c03fc07e01fe3fe000ffffc1f0086196718100632661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjw:W:=0xff8000003c7ffff800000007fffffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zjx:W:=0xc03807f03c07e0007c3ffc01e01fe03e000fff801f0086186018124672621e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zjy:W:=0xc03807f03c07e0007c3ffc07e01fe3fe000ffffc1f0086196718124672661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjz:W:=0x7ff800fc000007fc000007ffe003fffff0007c0001182187e0620e0387e18000480000c4208002311010062080811880440212940000010600020c02060180
def zjA:W:=0xc07807f03c07e0007c3ffc07e01fe3fe000fff801f0086196318124672661e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zjB:W:=0xfffffffffffffffffffffffe1e0003c1e00000000003ff000001fffffc058000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zjC:W:=0xc07807f0fc07e007fc3ffc06001fe3c0000ffffc1f0086186418124e70641f984040011048062010951928124006204a80064524861404106518004860441518
def zjD:W:=0xffffffffffffffffffffffffe01fe000000000000003ff000001fffffe600000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zjE:W:=0xfffffffffffffffffffffff800000000000000000003ff218361fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zjF:W:=0xc07f87f0fc07e007fc3ffc07fe1fe3ffe00ffffc1f0086196718124e72679f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjG:W:=0xc07807f0fc07e007fc3ffc00001fe3fe000ffffc1f0086196718124e70661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjH:W:=0xc03807f0fc07e0007c3ffc07e01fe03e000ffffc1f0086196318124672621f98400801108c26a012a40938146086a15200424736121404116318024462421498
def zjI:W:=0xfffffffffffffffffffffff800000000000000000003ff2080e1fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zjJ:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182007e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zjK:W:=0xc07807f0ff87e007fc3ffc07fe1fe3fe000fffffff0086196718124e72661ff840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjL:W:=0xffffffff0000000000000007ffffffffffffff800003fffe98e7fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zjM:W:=0xc07807f0fc07e007fc3ffc07e01fe3fffffffffc1f00863967f8124e7267ff9840488910ccaea013bd99383662a6a1dec066473ed61c041167d8024d624755d8
def zjN:W:=0xc03807f03c07e0007c3ffc01e01fe03e000fff801f0086196318124672621e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zjO:W:=0xffffffff0000000000000007ffffffffffffff800003c0de0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zjP:W:=0x7f80003f8000003c000001fe00001fff00003e001182080e061818181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zjQ:W:=0x7ffff0fff80007ffc00007ffe003ffffffffffe001983987e0738f8387ffe0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zjR:W:=0x3807870f03861c0003fc03fe1e1e1fc1e00f007ffffc4106049e0c01cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zjS:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00c71f679e124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjT:W:=0x41fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zjU:W:=0xc07807f0fc07e007fc3ffc07ffffe3ffffffffffff019e39e7f8124e73e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def zjV:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffcc11e049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zjW:W:=0xf87f87ffff87fc07ffffffffe01fe3fe000ffffc1f00861967181e4ffe661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zjX:W:=0xc07f87f0ffffe007fffffc07ffffe3ffe00fffffff008619e79813cff3e79ff840488110dda6a033b5193836e686a1da80e6477e963c0411e798034d634715f8
def zjY:W:=0x379e79fe600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zjZ:W:=0x7fffff0000000000000007ffffffffffffff800001c03e00007c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zj0:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086d9ff18124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zj1:W:=0xfff807f0fffffffffc3ffc07e01fe3fe000ffffc1f02a6d9ff1993fe72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zj2:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182187f8638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zj3:W:=0x7ff800fff800007c000007ffe003fffff0007fe0011821836063860387e1e0001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zj4:W:=0xc7b878f00000000000000007ffffffffffffff80000380f80001f00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zj5:W:=0xffffffffc3861c0783fc03ffffffffffffffff800003fffe0001fc09cffffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zj6:W:=0xff800000fffffff800000007fffffc000000007ffffe61c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zj7:W:=0xc07ff800fff80007ffc00007ffffe3fffff0007fe001182187e0638f83e7e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zj8:W:=0xf87f87ffff87fc07ffffffffe01fe3fe000ffffc1f00c71f679e1e4ffe661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zj9:W:=0x3878003c7800007c000007ffe003fffff0007fe0011821836063860387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zka:W:=0x7ff800ffffe007ffc00007ffe003fffff0007fff011821e7e063cf8387e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zkb:W:=0xc3800000000000061e0000000000007fe003fffffffe0000000001e0040040880000020000030200000000001000c0000003ef7a292a000000000000
def zkc:W:=0xff87f800fffffff800000007fffffc01fff0007fffff20e1f801e3f003f9e1ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zkd:W:=0x7ff80003f8000003c00007ffe003fffff00003e001182187e061818387e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zke:W:=0xffffffff0000000000000007ffffffffffffff800003fffe0001fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zkf:W:=0xff800000fffffff800000007fffffc000000007ffffe20c1ff0183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zkg:W:=0xffffffffffffffffffffffffffe003fffff000000003ff000001ffffff87e000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkh:W:=0xffffffffc3861c0783fc03ffffffffffffffff800003c1fe049ffc09cffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zki:W:=0xfffff800fffffff800000007fffffc000000007fffff20c1f801e3f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zkj:W:=0x23fc1fffe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zkk:W:=0x7f07fffe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zkl:W:=0x7ff800fffe1c07fffc03ffffe003fffff0007ffffd592787fe638fcf87e1ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zkm:W:=0xc7ffffff0000000000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zkn:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086180718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zko:W:=0xfffff800ffffffffffc00007ffe003fffff0007fe001182187e1e3ff8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zkp:W:=0xfffffffffffffffffffffff800000000000000000003ff06049ffffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkq:W:=0xfffffffffffffffffffffff800000000000000000003c0000001fffffc000000263664cc224111844220c180000000000c0020000003d0000000f49294000000
def zkr:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086180000124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zks:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f008619fffe124e72661f9840480110cc26a012b51938166086a15a80464736961404116f3a024c62461598
def zkt:W:=0x3f01fffe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zku:W:=0x7ff8000000000000000007ffe003fffff0007fe001182187e060000387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zkv:W:=0xfff807fffffffffffffffff800000000000000000002ff0000019ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkw:W:=0xfffffffffffffffffffffff800000000000000000003ff060001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkx:W:=0xf87ffffffffffc07ffffffffffe003fffff0007fe001df2187e07fcfff87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zky:W:=0xc07807f0fc07e007fc3ffc07e00003fe0000007c000086010700124e7206018000480000c4208002311010062080811880440212940000010600020c02060180
def zkz:W:=0xff8007fffffffffffffffff800000000000000000002e70000019ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkA:W:=0xf847870fc3861c0783fc03fffe1fffc1e00f007ffffc4106049e0c09ce7d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zkB:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106001e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zkC:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106009e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zkD:W:=0x3ff8003ff800007fc00001ffe0003ffff00003e001182183e063878383e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zkE:W:=0xff87f80ffffffffffffffff8000000000000000000037f000001effffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkF:W:=0xff800000fffffff800000000001ffc000000007ffffe20c0780183f0007801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zkG:W:=0xff800000fffffff800000007fffffc000000007fffff38e1f8e183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zkH:W:=0x3f87f80f03f81ff803c003f81fe01c01fff00003e00379e680e1edb18d99e060bf37feee33c913e54aa2c3e19f3912a55fa8b84840ebfbee80c1fd9395b9ea60
def zkI:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4106041e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zkJ:W:=0xc07f87f0ff87e007fffffc07e01fe3fe000ffffc1f0086196718124ff2661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zkK:W:=0x3847870f03801c0003c003fe1e1e1fc1e00f007ffffc4106049e0c018c1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zkL:W:=0x3c0fffffe000000000000040040880000000000010000000000001000c0000003c47a292a000000000000
def zkM:W:=0xffffffff0000000000000007ffffffffffffff80000000fe0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zkN:W:=0x3ffffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zkO:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe003fffffffe638f8387e1e0045ac888f7a882a7399352a6a6a0819cd4e4c25ad42bff7bafea438f830741e0
def zkP:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00100200000638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zkQ:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff01983987e073cff3e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def zkR:W:=0x1df3e07fe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zkS:W:=0xff800000fffffff800000007fffffc000000007ffffe2000000183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zkT:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196798124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zkU:W:=0x387fff0f0000000000000007ffffffffffffff80000140fe00006c0003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zkV:W:=0x3f87f80ffffffffffffffff800000000000000000003ff000001effffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zkW:W:=0xffffffff0000000000000007ffffffffffffff800003d8fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zkX:W:=0xfffffffffffffffffffffff80000000000000000000220000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zkY:W:=0xffffffff0000000000000007ffffffffffffff80000200fe0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zkZ:W:=0xc07ffff0fff80007ffc00007ffffe3ffffffffffe001182187e0738f83e7ffe0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zk0:W:=0xc7b878f03c79e3f87c03fc01e1e1e000000000000003bef9fb61f3f633e00000f6b664ccbb75dbf46223e385d4d4c8101e80f46318b3fffbf92bf7f297e800aa
def zk1:W:=0xffffffff0000000000000007ffffffffffffff800003fffe049ffc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zk2:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086180300124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zk3:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffd4126049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zk4:W:=0xffffffff0000000000000007ffffffffffffff800003c1fe0087fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zk5:W:=0x379e7fffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zk6:W:=0xff8007ff0000000000000000001ffc00000fff800002c0de00019c0000781e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zk7:W:=0x3847870fc3861c0783fc03fe1e1e1c000000007ffffc4106049e0c09cc1801ff0000000000000000000000000000000000000000000000000000000000000000
def zk8:W:=0xfffffffffffffff800000007ffffffffffffff800003fffe0001fff003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zk9:W:=0xff8007ff0007fff800000000001ffc00000fff801ffee7de781f9c7000781e1ffda556aa08144b500003a341595d5a211b08fc2108d3effe792bbc6000f8aa0a
def zla:W:=0xc7ffffff3c79e3fffffffff800000000000000000003be000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlb:W:=0xc07ffff0fffe0007fffc0007ffffe3ffffffffffff01983987f8738fc3e7fff8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zlc:W:=0xf87807f0ff87fc07fc3ffc07fe1ffffe000ffffffffea6d9ff18124e727e1fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zld:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001983987e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zle:W:=0xc7ffffff0000000000000001e1e1e3ffffffff80000380f80001fc0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlf:W:=0x3d8fffffe000000000000040040880000000000010000000000001000c0000003c47a292a000000000000
def zlg:W:=0xfffffffffffffffffffffff8000000000000007fffffff000001fffffc0001ff263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlh:W:=0xfffffffffffffffffffffff800000000000000000001df000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zli:W:=0x7f80003f8000003c000001fe00001fff00003e001182183e061818181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zlj:W:=0xf87807f0ff87fc07fc3ffc07fe1ffffe000ffffffffcc71f679e124e727e1fff40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zlk:W:=0x7ff8003c780007ffc00001e1e003fffff00000000118218360638f8387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zll:W:=0x387ff800fffe1c07ffc00007fffe1ffffff0007ffffd592787fe638f839fe1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zlm:W:=0xc07807f000000007fc3ffc07e01fe3fe000fff80000086196718100e72661e000048011044022002951918122002214a80464314860404102718000c60061510
def zln:W:=0x38000000c3861c00000000061e1e1c000000007ffffc4106049e0000001801ff0000000000000000000000000000000000000000000000000000000000000000
def zlo:W:=0xff800000fffffff800000007fffffc000000007ffffe21c1fc9f83f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zlp:W:=0xc7ffffff0000000000000001e1e1e3ffffffff800001c03e0001fc0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlq:W:=0xfffffffffffffffffffffff80000000000000000000027000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zlr:W:=0x7ff80000000007ffc00007ffe003fffff0007fe001182007e0600f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zls:W:=0xfffffffffffffffffffffff800000000000000000003ffe698e7fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zlt:W:=0x3807800f03801c0003c003f800000000000000000003fffffffe0c018c000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zlu:W:=0xffffffff0007fff800000007ffffffffffffff800003e0fe0001fc7003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlv:W:=0xfffffffffffffffffffffff800000000000000000003ff000419fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlw:W:=0xffffffff0000000000000007ffffffffffffff800003c03e0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlx:W:=0xffffffff0000000000000007ffffffffffffff80000000de0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zly:W:=0x7ff8003ff80007ffc00001ffe003fffff00003e001182187e0638f8387e060005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zlz:W:=0xffffffff0000000000000007ffffffffffffff800003c0fff801fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlA:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffe61c69c9e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zlB:W:=0xffffffff0000000000000007ffffffffffffff800001c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlC:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f02a6196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zlD:W:=0xffffffffc3861c0000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlE:W:=0xfffffffffffffffffffffff800000000000000000003df000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlF:W:=0xfffffffffffffffffffffff800000000000000000003ff01f801fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlG:W:=0xff87fffffffffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlH:W:=0xffffffff0000000000000007ffffffffffffff800003f9fe9cfffc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zlI:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00a619ff18124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zlJ:W:=0x2e7dff81e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zlK:W:=0xffb80000fffffff87c000007fffffc3e0000007ffffe20c1fb0183f603fa01ffd08800009d34c87220003005f4d4c91002c0167318b00081d201036403ea00aa
def zlL:W:=0xffffffff0000000000000007ffffffffffffff800003e0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlM:W:=0xfffffffffffffffffffffff800000000000000000001ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zlN:W:=0xc07807f00000000000000007e01fe3fe000fff800003c0fe0000100002661e0004004088000000000000000000000000100080000003c06a0000000000000000
def zlO:W:=0xffb87800fffffff800000007fffffc3e1ff0007fffff20e1f801e3f003fa61ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zlP:W:=0xffffffff0000000000000007ffffffffffffff800003f9ff9fe7fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zlQ:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0286d96718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zlR:W:=0x3f87f80f0000000000000007ffffffffffffff800003c0fe0001ec0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlS:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffe41c6049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zlT:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086186718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zlU:W:=0xffffffff0000000000000007ffffffffffffff800003c0000001fc0003fffe00bd2556aa0000014000008141191912210b08380000c3c0840001bc0000b8aa00
def zlV:W:=0x379e7fffe0000000000000000000000000000000000000000000000000000000000000000000000000000
def zlW:W:=0x7ff80003f80007ffc000001fe003fffff00003e001182007e0618f8187e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zlX:W:=0xfffffffffffffffffffffff800000000000000000003c6000001fffffc000000263664cc224111844220c180000000000c0020000003d0000000f49294000000
def zlY:W:=0xffffffff0000000000000007ffffffffffffff80000280d80001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zlZ:W:=0xfffffffffffffffffffffffe001e03c0000f00000003ff000001fffffc041800263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zl0:W:=0xffffffff0000000000000007ffe003fffff000000003fffffffffc000387e000242444880000030000038300000000001800e0000003ef7a292ab40000000000
def zl1:W:=0xffffffff0000000000000007ffffffffffffff80000080180001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zl2:W:=0xfffffffffffffff800000007ffffffffffffff800003e0fff801fff003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zl3:W:=0xffffffff0000000000000007ffffffffffffff800003c0ff6001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zl4:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f008639e7f8124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zl5:W:=0xffb87ffffffffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zl6:W:=0x7ff800fff80007ffc000001fe00001fff00003e001182187e0638f8181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zl7:W:=0x7ff800fff80007ffc00007ffffe3ffffffffffff01182187e0638f83e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def zl8:W:=0xffffe007fffffc00000000000000007fff001e01e7f803cff00001f8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zl9:W:=0x7ff800fff80007ffc00007fffe03ffffff007fff01182187f8638f8387f9f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zma:W:=0x7ff800fff80007ffc00007ffe003fffff000000001182187e0638f8387e0000012000022000084000040800000000004000000000010000000408280000000
def zmb:W:=0xc07807f0fc07e007ffffffffe01fe3fe000ffffc1f008719679e124ffe661f9840488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zmc:W:=0xffffffff0000000000000007ffffffffffffff80000380f80001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zmd:W:=0xffffffffffffffffffffffffe01fe3fe000fff800003ff000001fffffe661e00263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zme:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0186396718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zmf:W:=0x7fffff0000000000000007ffffffffffffff800003c0fe00007c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zmg:W:=0x387800fff80007ffc00007ffe003fffff0007fe001182187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zmh:W:=0x3ff800fff80007ffc00001ffe0003ffff0007fe001182187e0638f8383e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zmi:W:=0x3f87f80f03f81ff803c003f800001c0000000000000379c60001edb18c180000bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zmj:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f019e3967f8124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zmk:W:=0xfff807f0fffffff800000007fffffffe000ffffffffe20c1f80193f003fe1fffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zml:W:=0xf87f87ffc3861c0783fc03fffe1fffffe00ffffffffc4106049e1c09ce7f9fff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zmm:W:=0x3807800fc3861c0003c003fe1e1e1c01e000007ffffc4106049e0c018c1981ff0801820100800401004400600a08068021210808214800040084080108118844
def zmn:W:=0xc07ff800ffffe007ffc00007ffffe3fffff0007fff01182187e063cf83e7e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zmo:W:=0xc78000003c79e3f800000001e1e1e00000000000000220c1f80183f003e00000d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zmp:W:=0x1182187e00000000000000000000000000000000000000000000000000000000000000000000000000000
def zmq:W:=0x379e69cfe00000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zmr:W:=0x7ff800ffffffffffc00007ffe003fffff0007fe001382187e063ff8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zms:W:=0x7ff800c3f80007ffc000061fe003fffff0007fe001182087e0618f8187e1e0005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zmt:W:=0xff800000fffffff800000007fffffc000000007fffff38e1fb6183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zmu:W:=0xf87f87ffc3861c0783fc03fe1e1e1fc1e00f007ffffcc106049e1c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zmv:W:=0xc07807f0fc07e007fc3ffc01e01fe03e000fff801f0086196318124e72621e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zmw:W:=0x379e698e600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zmx:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086000000124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zmy:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182087e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zmz:W:=0x2fffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zmA:W:=0xc07ffff0fc07e007fc3ffc07e01fe3fffffffffc1f0186396718724e7267ff9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zmB:W:=0xf87807f0fffffc07fc3ffc07fffffffe000ffffffffc8619e71813ce73fe1fff40480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zmC:W:=0xffffffff0000000000000007ffffffffffffff80000080fe0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zmD:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffe6106049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zmE:W:=0xffffffff0007fff8003fffffffffffffffffff800003c0fe0001fc707ffffe00bf2576ee0041114042208141191912211b08b80000c3c0ee0001bc1014b8aa00
def zmF:W:=0x7ff8000000000000000007ffe003fffff0000000011821836060000387e0000000000000000000000000000000000000000000000000000000000000000000
def zmG:W:=0xc07ffff0ffffe007fc3ffc07ffffe3ffffffffffff018639e71873ce73e7fff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zmH:W:=0xfffffffffffffffffffffff800000000000000000000bf000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zmI:W:=0xfffffffffffffffffffffff800000000000000000003ffe60001fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zmJ:W:=0xfffffffffffffffffffffff800000000000000000003ff2600e7fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zmK:W:=0x7ff800fff8000000000007ffe003fffff0007fe001182187e063800387e1e000000000912080202000000484808010008000421020000180000300030000a0
def zmL:W:=0x7ff800fff80007ffc00007ffffe3fffff0007fff011821e7e0638f83e7e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zmM:W:=0xffffffff0000000000000007ffffffffffffff800003d9fe00e7fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zmN:W:=0xf87f87ffff87fc07ffffffffe01fe3fe000ffffffffcc719679e1e4ffe661fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zmO:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182107e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zmP:W:=0xc07807f0fc07e007fc3ffc07ffffe3fe000fffffff008619e718124e73e61ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zmQ:W:=0xffb87fff0000000000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zmR:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00338e19fe0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zmS:W:=0x3f87f80f0000000000000007ffffffffffffff80000000fe0001ec0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zmT:W:=0xfffff8000000000000000007ffffffffffffff80000300fe0001e00003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zmU:W:=0xfffffffffffffff800000007ffffffffffffff800003c0fe0001fff003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zmV:W:=0xff8007ff0000000000000000001ffc00000fff800002c7de001f9c0000781e00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zmW:W:=0xff8007f0fffffff800000007fffffc00000ffffffffea0d9f80193f003f81fffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zmX:W:=0xc07ff800ffffe007ffc00007ffffe3fffff0007fff0338e1ffe063cf83e7e1f8405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zmY:W:=0xffffffff0000000000000007ffffffffffffff80000100200001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zmZ:W:=0xc03807f03c01e0007c3ffc01e001e03e000fff80000086196318124672621e00400801108c26a012a40938146086a15200424736121404116318024462421498
def zm0:W:=0x7ff800c380000783c00007ffe003fffff0007fe001182187e060098387e1e00040800040800001111000220200008880240008840800000480000900050140
def zm1:W:=0x7ff8003c7800007c000001e1e003fffff0000000011821836063860387e000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zm2:W:=0xc07807f0fc07e007fc3ffc0000000000000000000003ff000000124e7000000004004088000002000002020000000000000000000003eb000000000000000000
def zm3:W:=0xffffffffc380000000000007ffffffffffffffffe003c0fe0001fc0003ffffe0bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zm4:W:=0xf87807f0ff87fc07fc3ffc07e01fe3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zm5:W:=0x7f800fff80007ffc00007ffe003fffff0007fe001182187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zm6:W:=0x3bffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zm7:W:=0x38000000c3861c000000000000000000000000000003fffffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zm8:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f008619e718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zm9:W:=0xfffffffffffffffffffffff800000000000000000003ff180001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zna:W:=0xff800000fffffff800000007fffffc000000007ffffea6c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def znb:W:=0xff800000fffffff800000007fffffc000000007ffffea0d9f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def znc:W:=0xffc7870fffffffff83fc03fe1e1e1fc1e00f007ffffc4106049f8ff9cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def znd:W:=0xfffffffffffffffffffffff800000000000000000003ff016001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zne:W:=0x387ff800fff81c07ffc00007ffe01ffffff0007fe0fd182187e0638f839fe1e7005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def znf:W:=0xffffffff0007e000003ffc07ffffffffffffff800003c6fe0001fc4073fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zng:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fffffff008619e7f8124e72661ff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def znh:W:=0x47870f0000000783fc03f800000000000000000003fffffffe0c09cc000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zni:W:=0x7ff800fffffffffffc03ffffe003fffff0007ffffd3921fffe63ffcf87e1ff40da8901ffbeccb7b9d478b6e6e6cddce4e5077ffd3c1001d6d443efcb4751fe
def znj:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196018124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def znk:W:=0x3f80000003f81ff80000000000000000000000000003ffffffff81b000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def znl:W:=0xc07807f03c01e0007c03fc07e01fe3fe000fff80000086196718124632661e00400800108c24a012240930046084a11200424632121004116308024422420488
def znm:W:=0xfffffffffffffffffffffff80000000000000000000006000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def znn:W:=0xc07ff800fff9e007ffc00007ffe1e3fffff0007fe0011821e7e063cf83e7e1e0405a8800ffac80b7399070a6e6a4819cc4e4067ad4381001c6c043cf834741e8
def zno:W:=0x7ff8003c7800007c000007ffe003fffff000000001182187e063860387e000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def znp:W:=0xc07807f0fc07fffffc3ffc07e01fe3fe000ffffc1ffca6197f18127e72661f9f40c80110cc36e812b519381660c6e95a804647379e1404117718026c6246159a
def znq:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001592787e6638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def znr:W:=0xffffffff0000000000000007ffffffffffffff800003c0fe0481fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zns:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007fffffbef9fb600c09cc1d99ff0c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def znt:W:=0x7ff800ffffffffffc00007ffe003fffff0007fffff38e1ffe063ff8387e1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def znu:W:=0x3807870fc3861c0003fc03fe1e1e1c01e00f007ffffc4106009e0c01cc1999ff0801830100820401804408700a0a06c02121090c214c00040094080148119854
def znv:W:=0xffffffff0000000000000007ffffffffffffff80000040fe0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def znw:W:=0xff800000fffffff800000007fffffc000000007ffffe20c1fc8183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def znx:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00861f679e124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zny:W:=0xc7ffffff3c79e3fffffffff800000000000000000001df000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def znz:W:=0xff80000003fffff800000007fffffc000000007ffffe20c1f80181f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def znA:W:=0xc7ffffff0000000000000007e1ffe3ffffffff800003c0fe0001fc0003e7fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def znB:W:=0xfffffffffffffffffffffff8000000000000000000007f000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def znC:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001192187fe638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def znD:W:=0xc07807f0fc07e007fc3ffc07ffffe3fe000ffffc1f0086196718124e73e61f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def znE:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc412787fe0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def znF:W:=0xff800000c3fffff8000000061ffffc000000007ffffe20c0f80181f001f801ffd08000001914487000002001d45448000280146108b00080d001016001e8002a
def znG:W:=0xc07807f0fc07e007fc3ffc07ffffe3ffffffffffff0086196718124e73e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def znH:W:=0xc7b878f00000000000000007ffffffffffffff80000000fe0001f00003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def znI:W:=0xff800000fffffff800000007fffffc000000007fffff20e1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def znJ:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe0019e2187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def znK:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196000124e72661f984000000088248010200020044084801000000422101000014000024002400088
def znL:W:=0x7ff80000000007ffc00001e1e003fffff000000001182187e0600f8387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def znM:W:=0xc07f87f0ff87e007fffffc07fe1fe3ffe00fffffff0086196718124ff2679ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def znN:W:=0x7ff800fffe1c07fffc03ffffe003fffff0007ffffd182187e0638fcf87e1ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def znO:W:=0x3f87f80f0000000003c003f81fe01c01fff00000000359e60001ec018d99e000bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def znP:W:=0xfffffffffffffffffffffff80000000000000000000041000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def znQ:W:=0x3878f00000000000000007ffffffffffffff80000180fe0000700003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def znR:W:=0xfffffffffffffffffffffff800000000000000000003ff060087fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def znS:W:=0x7807f0fc000007fc3ffc07e01fe3fe000ffffc1f0086196718120e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def znT:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff01182187f873cff3e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def znU:W:=0xc07807f00007e007fc3ffc00001fe000000fff801f0086186018104e70601e184000011008062010840928104006204200024524021404106118004060401418
def znV:W:=0xff800000fffffff800000001e1fffc000000007ffffe20c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def znW:W:=0xfffffffffffffffffffffff800000000000000000003ffc00001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def znX:W:=0xffffffff0000000000000007ffffffffffffff800003f9fe0001fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def znY:W:=0xc07807f0fffffffffc3ffc07ffffe3fe000ffffffffca619ff1813fe73e61fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def znZ:W:=0xff800000fffffff8000000061e1e1c000000007ffffe20c1f80183f0001801ff0000000000000000000000000000000000000000000000000000000000000000
def zn0:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc6107fc9e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zn1:W:=0xc7fffffffc7fe3fffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zn2:W:=0xc07ffff00000000000000007ffffffffffffff80000180fe0000700003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zn3:W:=0xc07807f03c01e007fc3ffc01e001e3fe000fff80000086180718124e72661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zn4:W:=0xfffffffffffffffffffffff800000000000000000003ffe79fe7fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zn5:W:=0xffffffffc3861c0783fc03ffffffffffffffff800003c0fe0001fc09cffffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zn6:W:=0x387ff800fffe1c07ffc00007fffe1ffffff0007fffff38e1ffe0638f839fe1ff005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zn7:W:=0xc00007f03c07e0007c3ffc00001fe000000fff801f0086196318124670601e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zn8:W:=0x3f87f80f03f81ff803c003f81fe01c01fff00000000379e698e7edb18d99e000bf3776ee224113c44222c3c1191912211f08b80000c3fbee0823fc9294b8aa00
def zn9:W:=0xffffffff0000000000000007ffffffffffffff8000003f01fffffc0003fffe00b92516220000034000038341191912210b08780000c02f94292bbc0000b8aa00
def zoa:W:=0x47f800c3f8000783c000061fe003c1fff0007fe001182187e061898185e1e000528800738800a5199040a28620008cc4a40048c428100084c0418b81054160
def zob:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196300124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zoc:W:=0xffff87fffffffffffffffff800000000000000000002e70000019ffffc0000000000000000000000000000000000000000000000000000000000000000000000
def zod:W:=0xfffffffffffffffffffffff800000000000000000003ffc7fc9ffffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zoe:W:=0x3fc7ff0f0000000000000007ffffffffffffff80000340fe0001ec0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zof:W:=0xff800000fffffff800000007fffffc000000007ffffe20c0780183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zog:W:=0x38000000c3861c00000000061e1e1c000000007ffffe20c1f8000000001801ff0000000000000000000000000000000000000000000000000000000000000000
def zoh:W:=0x7ff800fff9e3ffffc00007ffe003fffff0007fe0013821ffe063ff8387e1e040da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zoi:W:=0x387ff800fff80007ffc00007fffe1ffffff0007fe001182187e0638f839fe1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zoj:W:=0xc03807f03c01e0007c03fc01e01fe03e000fff80000086196300124632621e00400800108c24a012240930046084a11200424632121004116308024422420488
def zok:W:=0xffc78000fffffff800000007ffffffc1e000007ffffe20c1f80183f003fd81ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zol:W:=0x7fff00fffe0007fffc0007ffe003fffff0007fe001182187e0638fc387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zom:W:=0xfffffffffffffffffffffff800000000000000000003ff018001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zon:W:=0xc07f87f0fc07e007fffffc07e01fe3ffe00ffffc1f0086196798124ff2679f9840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zoo:W:=0xc07ffff0fc07e007fc3ffc07ffffe3fffffffffc1f0086196718724e73e7ff9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zop:W:=0xc07ffff00000000000000007ffffe3ffffffff800003c0fe0000700003e7fe0004004088000000000000000000000000100080000003c06a0000000000000000
def zoq:W:=0xc07fff00ffffe007fffc0007ffffe3ffffff007fff011821e7f863cfc3e7f9f8405a8900ffae80b7b99078b6e6a681dcc4e4077ed43c1001c6d043cfc34751f8
def zor:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00318e187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zos:W:=0xffffffff0000000000000007ffffffffffffff80000380fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zot:W:=0xff8007ff0000000000000000001ffc00000fff800002e6de78019c0000781e00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zou:W:=0xc07807f00007e007fc3ffc07e01fe3fe000ffffc1f0086196718104e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zov:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f019e196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zow:W:=0xffffffffc3861c0000000007ffffffffffffffffffffc1fe049ffc0003ffffffbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zox:W:=0xfffffffffffffffffffffff800000000000000000003fe000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zoy:W:=0xff8007ff0007e000003ffc00001ffc00000fff801f02e7de781f9c4070781e18fd2557ba08062350840bab51591f32631b0afd2402d7effe693bbc4060f8be18
def zoz:W:=0xc07807f0fc07e007fc3ffc01e001e3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zoA:W:=0xfffffffffffffffffffffff800000000000000000003ff00049ffffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zoB:W:=0xffffffff0000000000000007ffffffffffffff800003d8ff8361fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zoC:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086186000124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zoD:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0000010700124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zoE:W:=0xc07807f0ffffffffffffffffe01fe3fe000ffffffffca719ff9e13fffe661fff40c88111ddb6ec33b55d3836e6c6eddaa0e7477fbf3c0411f79c036d6b4715fe
def zoF:W:=0xffffffffffffffffffffffffffe003fffff000000003fffe0001ffffff87e000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zoG:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f008719679e124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zoH:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182787fe638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zoI:W:=0x478000c380000783c0000000000000000000000003fffffffe000980000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zoJ:W:=0xfffffffffffffffffffffff800000000000000000003ffc09801fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zoK:W:=0xffffffff0000000000000007ffffffffffffff800003e1fffc9ffc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zoL:W:=0xfffffffffffffffffffffff800000000000000000003bf000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zoM:W:=0xfffff800ffffffffffc00007ffe003fffff0007fe00338e1ffe1e3ff8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zoN:W:=0xc03800f03c01e0007c03fc01e01fe03e000fff801f0086196318124632621e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zoO:W:=0xfffffffffffffffffffffff800000000000000000002a6000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zoP:W:=0x3f87f80ffffffffffffffff8000000000000000000003f000001effffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zoQ:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001582787e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zoR:W:=0xffff87ffffffffffffffffffe01fe3fe000ffffc1f02e71967199ffffe661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zoS:W:=0xffbff8ff0000000000000007ffffffffffffff800003c0fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zoT:W:=0xffb800f0fffffff800000007fffffc3e0000fffffffea0d9f80193f003fa07ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zoU:W:=0x7ff800ffffe007fffffc07ffe003fffff0007fff01182187e063cff387e1f8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def zoV:W:=0xc07807f0fffffffffc3ffc07e01fe3fe000ffffffffc8619671813fe72661fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zoW:W:=0xc07807f0ffffe007fc3ffc07ffffe3fe000fffffff008619671813ce73e61ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zoX:W:=0xc07f87f0ff87e007fffffc07fe1fe3ffe00fffffff00c71f679e124ff2679ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zoY:W:=0xfffffffffffffffffffffff800000000000000000003ff0098e7fffffc000000263664cc224113844222c380000000000c0020000003fb000822f49294000000
def zoZ:W:=0xff800000fffffff800000007fffffc000000007ffffe61c7f88783f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zo0:W:=0xffffffff0000000000000007ffffffffffffff800003fefe0001fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zo1:W:=0x7ff8003c780007ffc00001e1e003fffff000000001182007e0638f8387e000005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zo2:W:=0xc07807f000000007fc3ffc01e001e3fe000fff80000086180718100e72661e000048011044022002951918122002214a80464314860404102718000c60061510
def zo3:W:=0x7ff8000000000000000007ffffffffffffff80000000fe0000600003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zo4:W:=0xffffffff0000000000000007ffffffffffffff800003c0fe0419fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zo5:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffcc706049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zo6:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182183e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zo7:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe0011821e7e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zo8:W:=0xc006000000000006001e00000000007c1f03fffffffe000000000198040040880000020000030200000000001000c0000003ef7a292a000000000000
def zo9:W:=0xffc787ffc387ffff83fffff800000000000000000003ffffffff9c79fc000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zpa:W:=0xff800000fffffff800000007fffffc000000007ffffe61c7f81f83f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpb:W:=0xffffffff0000000000000007ffffffffffffff800000c01e0001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zpc:W:=0xc07807f0ff87fc07ffffffffe01fe3fe000ffffffffc86196718124ffe661fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zpd:W:=0xc07ff8f0fff9e007ffc3fc07ffe1e3fffff0ffffe001182187e073cfb3e7e7e0405a8810ffaca0b73d9870a6e6a4a19ec4e6067ad6381001c6c043cfa34745e8
def zpe:W:=0x159fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zpf:W:=0x7ff800000000000000000000000000000000000003fffffffe600000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zpg:W:=0x387fff0fc3861c0783fc03fe1e1e1fc1e00f007ffffd4106049e6c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zph:W:=0xff800000fffffff800000007fffffc000000007ffffe60c7f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpi:W:=0xffffffff0000000000000007ffffffffffffff800003e0fe9801fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zpj:W:=0x387fff0ffffe1c07fffc03ffffe003fffff0007fe001592787fe6f8fcf87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zpk:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f03bef9fff8124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zpl:W:=0x3ff8003ff800007fc00001ffe0003ffff00003e001182187e063878383e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zpm:W:=0xfffffffffffffffffffffff800000000000000000003ffc61807fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zpn:W:=0xfffffffffffffffffffffff800000000000000000000c7000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zpo:W:=0xff8007f0fffffff8003ffc07fffffc000000007ffffea6c1f80193f073f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpp:W:=0xffb800f0fffffff87c03fc07fffffc3e0000fffffffe20c1f80193f633fa07ffd08800109d34e87224083005f4d4e91202c216731ab00081d201036423ea04aa
def zpq:W:=0x7ffffffffe00ffffffffc00dfff9e000003ff9fffd8c98311ddb6ec73b55d3877fedeefdaa3e75f7fbffc0495f79d0b6d6bff9dfe
def zpr:W:=0xfff807f0fffffffffc3ffc07fffffc000000007ffffe20c1f80193fe73f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zps:W:=0xff800000fffffff8000000061e1e1c000000007ffffe2000000183f0001801ff0000000000000000000000000000000000000000000000000000000000000000
def zpt:W:=0x7ff800fc000007ffc00007ffe003fffff0007fe001182187e0620f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zpu:W:=0xfffff800fffffff800000007fffffffffff0007ffffe20c1f801e3f003ffe1ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpv:W:=0xff800000fffffff800000007fffffc000000007ffffe20e1ffe183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpw:W:=0x387fff0fc3861c0783fc03fffffe1fffffff007ffffc4106049e6c09cf9ff9ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zpx:W:=0xc07807f00007e007fc3ffc00001fe3fe000fff801f0086196718104e70661e18404801104c062012951938126006214a80464734861404106718004c60461518
def zpy:W:=0xffc78000ffffffff83c00007fffffc000000007ffffe20c1f80183f983f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpz:W:=0xff8007ff0000000000000000001ffc00000fff800002e7de781f9c0000781e00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zpA:W:=0xc03807f03c07e0007c3ffc01e01fe03e000fff801f0086196718124672621e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zpB:W:=0xffc7870fffffffff83fc03fffffffc000000007ffffe20c1f8018ff9cff801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zpC:W:=0xfffffffffffffffffffffff8000000000000000000003f000001fffffc00000022362444224113844222c380000000000c00200000003b000000f49294000000
def zpD:W:=0xff8007ff0007fff8003ffff800000000000000000003ff0000019c707c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zpE:W:=0xff8007ff0000000000000000001ffc00000fff800003ffffffff9c0000781e00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zpF:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4107649e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zpG:W:=0x387f87ffc3861c0783fc03fe1e1e1fffe00ffffffffcc11e049e1c09cc1f9fff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zpH:W:=0xc07807f00001e007fc3ffc000001e3fe000fff80000086186718104e70661e00404801104c062012951938126006214a80464734861404106718004c60461518
def zpI:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff000000000073cff3e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def zpJ:W:=0x7ff800fff80007fffc03ffffe003fffff0007fe001192187fe638fcf87e1e0005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zpK:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff019e2187e073cff3e7fff8405a8910ffaea0b7bd9878b6e6a6a1dec4e6077ed63c1001c6d043cfe34755f8
def zpL:W:=0xc07807f03c01e007fc3ffc01e001e3fe000fff80000086196300124e72661e0040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zpM:W:=0xffffffff0000000000000007ffffffffffffff80000100fe0001fc0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zpN:W:=0xff800000fffffff8000000000000000000000000000220c1f80183f0000000000000000000000000000000000000000000000000000000000000000000000000
def zpO:W:=0x27fc7fffe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zpP:W:=0xffffffff0000000000000007ffffffffffffff800003e7fe0001fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0001bc0000b8aa00
def zpQ:W:=0xffffffff0000000000000007ffffffffffffff800003e7fe781ffc0003fffe00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zpR:W:=0xc07807f0fc01e007fc3ffc07e001e3fe000ffffc000086196718124e72661f8040480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zpS:W:=0xfffffffffffffffffffffff800000000000000000003ffc07801fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zpT:W:=0x3847870fc3861c0783fc03f8000000000000000000004106049e0c09cc0000000000000000000000000000000000000000000000000000000000000000000000
def zpU:W:=0xfffffffffffffffffffffff800000000000000000003ff2007e1fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zpV:W:=0xbffffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zpW:W:=0xfffffffffffffffffffffffe1e0000000000007fe003ff000001fffffc0001e0263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zpX:W:=0xfffffffffffffffffffffff8000000000000000000019e000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zpY:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086190718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zpZ:W:=0xffffffff0000000000000007ffffffffffffff800003d8fe07e1fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zp0:W:=0xffffffff0000000000000007ffffffffffffff80000180380001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zp1:W:=0x3847870fc3861c0783fc03fe1e1e1c000000007ffffc410000000c09cc1801ff0000000000000000000000000000000000000000000000000000000000000000
def zp2:W:=0xffffffff0000000000000007ffffffffffffff800003e1fe1807fc0003fffe00bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zp3:W:=0xc07807f0ff87e007fffffc07e01fe3fe000fffffff0086196798124ff2661ff840488110cca6a013b51938366286a1da8066473e961c04116798024d624715d8
def zp4:W:=0xc07ffff00000000000000007ffffe3ffffffff80000080180000700003e7fe000000000000000000000000000000000000000000000000000000000000000000
def zp5:W:=0x387fff0fc3861c0783fc03fe1e1e1fffffff007ffffd4126049e6c09cc1ff9ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zp6:W:=0x7f80000000000000000001fe00001fff000000001182187e060000181e0000000000000000000000000000000000000000000000000000000000000000000
def zp7:W:=0x7fff00fffe1c07fffc03fffffe03ffffff007ffffd192187fe638fcf87f9ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zp8:W:=0x7f80003f8000003c00001ffe0003ffff00003e001182183e061818383e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zp9:W:=0xffffffff0000000000000007ffffffffffffff800003c6fe0001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zqa:W:=0xfffffffffffffffffffffff800000000000000000003ff0187e1fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zqb:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196700124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqc:W:=0xffffffffffffffffffffffffffe00000000000000003ff000001ffffff800000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zqd:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00c71f671e124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqe:W:=0xffffe007fffffc00000000000000007fff000601671803cff00001f8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zqf:W:=0xfff80007ffc00000000000000000007fff001801e7f8038f800001f8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zqg:W:=0xfffffffffffffffffffffff800000000000000000002a6000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zqh:W:=0xffffffffffffffffffffffffffffff8000003ffe000003fffffffe009b133266224112c4422242c1191912211708980000c03bee0001489294b8aa00
def zqi:W:=0x7ff8000000000000000007ffffffffffffff800003c0fe0000600003fffe009d0152aa0000004000000041191912211308980000c3c0ee0001080000b8aa00
def zqj:W:=0xffffffff0007fff8003ffff800000000000000000003fffffffffc707c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zqk:W:=0xc07807f00007e007fc3ffc00001fe3fe000fff801f0086180718104e70661e18404801104c062012951938126006214a80464734861404106718004c60461518
def zql:W:=0x3fdffffe000000000000000000000000020000030200000000001000c00000002f7a292a000000000000
def zqm:W:=0xffffe007fffffc00000000000000007fff003f01fffe03cff00001f8405a8910ffaea2b7bd9b7ab6e6a6a1dec4e6477ed63c3f11effa43cfe34755f8
def zqn:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00c7196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqo:W:=0x7ff80003f80007ffc000001fe003fffff00003e001182187e0618f8187e060005a8800778800a7199050a2a620018cc4e40258c428100086c0418f81074160
def zqp:W:=0xc07ff800ffffe007ffc00007ffe003fffff0007fe001182187e063cf8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zqq:W:=0xffffffff0000000000000007ffffffffffffff800003d9ff87fffc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zqr:W:=0xffffffff0000000000000007ffffffffffffff800003e0fe7801fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zqs:W:=0xc03807f03c07e0007c3ffc01e01fe03e000fff801f0086196300124672621e18400801108c26a012a40938146086a15200424736121404116318024462421498
def zqt:W:=0x7ff8000000000000000007ffe003fffff000000001182007e060000387e0000000000000000000000000000000000000000000000000000000000000000000
def zqu:W:=0xc00007f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqv:W:=0x7ffe00000000000000003fffffffe000003800000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zqw:W:=0x3807870fc3861c0783fc03f81e1e1c01e00f007ffffc4106049e0c09cc1999ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zqx:W:=0xc0000000fc07e0000000000000000000000000000003fffffffe024000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zqy:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00c61f6718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqz:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe003382187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zqA:W:=0xfffff800ffffffffffc00007ffe003fffff0007fffff3821ffe1e3ff8387e1ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zqB:W:=0x7fff00fff80007fffc0007ffe003ffffff007fe001182187f8638fc387f9e0005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zqC:W:=0xc07807f00007e007fc3ffc00001fe3fe000fff801f0086186018104e70661e18404801104c062012951938126006214a80464734861404106718004c60461518
def zqD:W:=0xfff807f0fc07fffffc3ffc07e01fe3fe000ffffc1f02a6196719927e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqE:W:=0x7ff800c3800007ffc00007ffe003fffff0007fe001182187e0600f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zqF:W:=0xff8007ff0007fff8003ffff800000000000000000002e7de781f9c707c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zqG:W:=0xff800000fffffff800000007fffffc000000007fffff38c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zqH:W:=0xc7fffffffff9e3fffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zqI:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086196318124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqJ:W:=0x7ff8003ff800007fc00007ffe003fffff00003e001182183e063878387e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zqK:W:=0x3847870fc3861c0783fc03f8001e1c00000f007ffffc4106049e0c09cc1819ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zqL:W:=0xfffffff80000000000000000000000000003fffffffe03f000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zqM:W:=0xf87807fffc07fc07fc3fffffe01fe3fe000ffffc1f00c71967181e4e7e661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqN:W:=0xfffffffffffffffffffffff800000000000000000003e7000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zqO:W:=0xfffffffffffffffffffffff800000000000000000003ff010701fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zqP:W:=0xff800000fffffff800000007fffffc000000007ffffe38c1ffe183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zqQ:W:=0x3847ff0fc3861c0783fc03fe1ffe1fc1ffff007ffffd4126049e6c09cd9df9ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zqR:W:=0xfff807fffc07fffffc3ffff800000000000000000003ffffffff9e7e7c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zqS:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f009e19e7f8124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqT:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f02a6d97f18124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zqU:W:=0xc3861c0783fc03f800000000000000000003fffffffe0009cc000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zqV:W:=0xc7b878f00000000000000007ffffffffffffff800003c0fe0001f00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zqW:W:=0xffffffff0000000000000007ffffffffffffff800003c0f80001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zqX:W:=0xc07ff8f0fff80007ffc00007ffe1e3fffff0ffffe001983987e0738f83e7e7e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zqY:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffd5906049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zqZ:W:=0xfffffffffffffffffffffff800000000000000000003ff200001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zq0:W:=0xff8007ff00061c00003c03f8001ffc00000fff801ffee7de781f9c004c781e1fbd2557ab0002074080478b51191b16613b09f90421c7effe293fbc0048b8ba14
def zq1:W:=0xffffffff0000000000000007ffffffffffffff800003c0ff87e1fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zq2:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0080180000124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zq3:W:=0x7fff00fffe0007fffc0007fffe03ffffff007fff01592787fe638fc387f9f8005a8900f7aa80a7b99058b6a6a281dcc4e4035ed42c100186d0438fc30751f0
def zq4:W:=0x387f870fc3861c07fffc03fe1e1e1fffe00f007ffffc4106079e0c0fcc1f99ff0849830144820403915418722a0a07c8a1650b1ca54c00040694080d48179954
def zq5:W:=0xff800000fffffff8000000061e1ffc000000007ffffe20c1f80183f0007801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zq6:W:=0xff800000fffffff800000007fffffc000000007ffffe20c1fc1983f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zq7:W:=0xffffffffc0060007803c0007ffffffffffffff800003c0fe0001fc0843fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zq8:W:=0x7ffff0fff80007fffffc07ffe003ffffffffffe001182187e0738ff387ffe0005a8910f7aaa0a7bd9858b6a6a2a1dec4e6035ed62c100186d0438fe30755f0
def zq9:W:=0xc7fff8f00000000000000007ffffffffffffff80000380fe0001f00003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zra:W:=0xc03800f03c01e0007c03fc07e01fe3fe000ffffc1f0086196300124632661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zrb:W:=0x3807800fc3861c0003c003fe1e1e1fc1e00f007ffffc4106049e0c018c1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrc:W:=0x7ff800fff80007ffc00001ffe0003ffff00003e001182183e0638f8383e060001a8800b7a880a7288050a4a6a0819444e0025a5028100182c04387830340e0
def zrd:W:=0x7f80003f8000003c000001fe00001fff00003e001182087e061818181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zre:W:=0xffc00700fffffff800000007ffffffc0000f007ffffe20c1f80183f003fc19ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zrf:W:=0xc04007f0fc07e007fc3ffc06001fe3c0000ffffc1f0086196718124e70641f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zrg:W:=0x387f87ffc3861c07fffffffe1e1e1fffe00ffffffffc4106049e1c0ffc1f9fff0849831144822403955c18722a0a27caa1670b1ca74c00040694080d68179d54
def zrh:W:=0xfffffffffffffffffffffff81fe00001fff000000003ff200001fffffd81e000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zri:W:=0xffffffff3c01e0007c03fc07ffffffffffffff800003c6fe0001fe4633fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zrj:W:=0x3847870fc3861c0783fc03f81e001c01e000007ffffc4106049e0c09cc1981ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrk:W:=0xfffffffffffffffffffffff800000000000000000003ff000481fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zrl:W:=0x3847870fc3861c0783fc03fe1e1e1c00000f007ffffc4106001e0c09cc1819ff080103010002040080440850080a064021010904214400040014080048109814
def zrm:W:=0xfffffffffffffffffffffff800000000000000000003ff3e0001fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zrn:W:=0x3f800000fffffff800000007ffe01c000000007ffffe20c1f80183f0039801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zro:W:=0xfff807f0fffffffffc3ffc0000000000000000000002a600000193fe700000000000000000000000000000000000000000000000000000000000000000000000
def zrp:W:=0x7ff8003c7800007c000007ffe003fffff0007fe001182187e063860387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zrq:W:=0xff800000fffffff800000007fffffc000000007ffffe20c1780183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zrr:W:=0x3847870fc3861c0783fc03fffe1fffffe00ffffffffc411e049e0c09ce7f9fff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrs:W:=0x7807f000000007fc3ffc0000000000000000000003fffffffe100e70000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zrt:W:=0x2e7de7c9e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zru:W:=0x7ff800fff80007ffc00007ffe003fffff000000001182007e0638f8387e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zrv:W:=0x7fffff0000000000000007ffffffffffffff80000000fe00007c0003fffe00b92516220000014000008141191912211b08b80000c000ee0001bc0000b8aa00
def zrw:W:=0x61e1e1c000000007ffffc000000000000001801ff0000000000000000000000000000000000000000000000000000000000000000
def zrx:W:=0xfff807f0fffffffffc3ffc07e01fe3fe000ffffc1f008619671993fe72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zry:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4107849e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrz:W:=0xfffffffffffffffffffffff800000000000000000003ffe09861fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zrA:W:=0xc07807f0ff87fc07ffffffffe01fe3fe000ffffffffcc71f679e124ffe661fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zrB:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffe61c67c9e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrC:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc4107079e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrD:W:=0xc07807f0ffffe007fc3ffc07ffffe3fe000fffffff02a6d9ff1813ce73e61ff840480110dd26a032b5193816e486a15a80c6477696340411e718034c634615b8
def zrE:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000fff80000086180718124e72661e000048011044022002951918122002214a80464314860404102718000c60061510
def zrF:W:=0x780000fc000007fc00000000000000000000000003fffffffe020e00000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zrG:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffffffc8619679e124e72661fff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zrH:W:=0x18fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zrI:W:=0x7ff800fff80007ffc00007ffe003fffff00000000118218360638f8387e000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zrJ:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffd592684fe0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zrK:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f019e39e778124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zrL:W:=0x7ff00000000003ffff800000000000000000003fffffffe1c007c000000262464cc0041130042238300000000001800e0000003ef7a292ab41014000000
def zrM:W:=0xffffffff0000000000000007ffffffffffffff800003c0ff0701fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zrN:W:=0x387fff0ffffe1c07fffc03ffffe003fffff0007fe001182187e06f8fcf87e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zrO:W:=0xffffffff0000000000000007ffffffffffffff800003f8ffffe1fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zrP:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001592187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zrQ:W:=0xfffffffffffffffffffffff800000000000000000003ffde0001fffffc000000263664cc224113844222c380000000001c00a0000003fb6a0000f49294000000
def zrR:W:=0x7ff800fc780007fc000007ffe003fffff0007c000118218760638e0387e180005a0800f72880a639905086a4a0811cc4c40252d42010018640438e830641a0
def zrS:W:=0xfffffffffffffffffffffff8001e1c00000000001fffff000001fffffc18001f263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zrT:W:=0x220fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zrU:W:=0xffffffff00001c00000003ffffffffffffffff8000ffc1fe0007fc000ffffe07bd2556ab0000054000448141191916213b09b80021c3c0ee0005bc0008b8aa04
def zrV:W:=0xc07807f0fffffffffc3ffc07e01fe3fe000ffffffffea6d9ff1813fe72661fff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zrW:W:=0xffffffffc3861c0000000007ffffffffffffffffffffe0fff801fc0003ffffffbd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zrX:W:=0xffbff8fffffffffffffffff800000000000000000003ff000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zrY:W:=0xffffff0ffffffffffffc03ffffffffffffff007ffffc00000001efffcffff9ffd8db8b01ffbeccf7b9d478f7fefecfdce7e51f7ffdfc1085d6d54befcbffd9fe
def zrZ:W:=0xf87807f0fc07fc07fc3ffc07e01ffffe000ffffc1ffc86196718124e727e1f9f40480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zr0:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc41c7fc9e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zr1:W:=0xffffffff0000000000000007ffffffffffffff800003c0fe98e7fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0823bc0000b8aa00
def zr2:W:=0xff8000000000000000000007fffffc000000007ffffe00c1f801800003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zr3:W:=0xff800000fffffffffffffffffffffc000000007ffffe3fc1f80183fffff801ffd2922044bb75daf462226285d4d4c8100680146318b03b81d00143f297e800aa
def zr4:W:=0xc07807f00000000000000007e01fe3fe000ffffc1f0080196718100002661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zr5:W:=0xc07807f0ffffffffffffffffe01fe3fe000ffffc1f00bf19671813fffe661f98425a2154ee67b296f73b7a966086a15a8446473696143f11671842def6461598
def zr6:W:=0x3847870f00000000000000061e1e1fc1e00f007ffffc4006049e0c00001d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zr7:W:=0x7ff800ffffffffffffffffffe003fffff0007fe0013f2187e063ffff87e1e0025aa844f7e992a77bb252a6a6a0819cc4e4025ad4283b0186c0439f970741e0
def zr8:W:=0xfffffffffffffff800000000000000000003fffffffe03fffc000000061260cc2241128442234280000000001400c0000003ff7a292a409294000000
def zr9:W:=0xff800000fffffff800000000000000000000007ffffe2001f80183f0000001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zsa:W:=0xc07807f0fc07e007fc3ffc00000000000000007c1f0086016718124e7000019840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zsb:W:=0xc07807f0fc07e007fc3ffc07fffffffffffffffc1f0086ff6718124e73ffff98d9491332cc26a052b5193857799fb37b934edf3696d404ff67190a4c62febf98
def zsc:W:=0xc7b878f03c79e3f87c03fc01e1e1e03e1ff0ff800003bef80001f3f633e26600b73674ee224113c44222c381111110211e08b0000083fbea0001f49294a82200
def zsd:W:=0x3847870fc3861c0783fc03fffffffffffffffffffffc41fe049e0c09cfffffff9941932340820441915408731b1b16e9b32d990ca5cc00ee0495080948bdbb54
def zse:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f00000000410600000c09cc1d98000801020000000000000000400808020001000800004000040000080000108800
def zsf:W:=0x7ff800fff80007ffc00007ffe003fffff00000000118200000638f8387e0000012000022000084000040800000000004000000000010000000408280000000
def zsg:W:=0xffffffff000000000000000000000000000000000003c0000001fc000000000024244488000001000000810000000000080020000003c0000000b40000000000
def zsh:W:=0xfffffff800000007fffffc000000007ffffc20c1f80003f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zsi:W:=0xfffffffffffffff800000007fffffc000000007fffffe0c1f801fff003f801fff4a444889934c9702000a105d4d4c8100a80346318b3c081d001b76003e800aa
def zsj:W:=0xfc07e007fc3ffc07e01fe3fe000ffffc1f0006196718024e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zsk:W:=0xfffffffffc07e007fc3ffc07e01fe3fe000ffffc1f03c6196719fe4e72661f98646c4598cc26a112b519b9166086a15a884667369617c4116718b64c62461598
def zsl:W:=0xc3861c0783fc03fe1e1e1fc1e00f007ffffc0106049e0009cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zsm:W:=0xffffffffc3861c0783fc03fe1e1e1fc1e00f007fffffc106049ffc09cc1d99ff2c65c78940820501915489720a0a06c8a925290ca54fc0040494bc0948159954
def zsn:W:=0xffffffff00000007ffffffffffffffffffffff800003dffe0001fc0ffffffe00bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zso:W:=0xc07ffffffc07e007ffffffffe01fe3fe000ffffc1f01df1967187e4ffe661f98667e65dcee67b396f73bfb966086a15a8c4667369617ff116718f6def6461598
def zsp:W:=0x38000000c3861c00000000061e1e1fc1e00f007ffffc0006049e0000001d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zsq:W:=0x387fffffc3861c07fffffffe1e1e1fc1e00f007ffffddf06049e7c0ffc1d99ff2e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def zsr:W:=0xfff8000000000007ffe003fffff0007fe000002187e003800387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zss:W:=0xffffffff0000000000000000000003ffffffff800003c03e0001fc000007fe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zst:W:=0xffffffff0000000000000007ffffffffffffffffffffc0fff801fc0003fffffffda556aa9934c9702000a145ddddda311b88bc6318f3c0efd001bf6003f8aaaa
def zsu:W:=0xc07807f0fc07e007fc3ffc00000003fe000fff80000086180718124e70061e000048011044022002951918122002214a80464314860404102718000c60061510
def zsv:W:=0xc07807f0fc07e007fc3ffc07fffffffe000ffffffffc86d9ff18124e73fe1fffd0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zsw:W:=0x3847870fc3861c0783fc03f8000003c1e00f000000004106049e0c09cc0598000841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zsx:W:=0x7ff800fff80007ffc00000000003fffff000000001182007e0638f8007e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zsy:W:=0x7ff800fff80007ffc00007fffffffffff0007ffffd18e1ffe0638f83ffe1ffd0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zsz:W:=0x7fffffc000000007ffffffffffffe000003f801ffd48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def zsA:W:=0xfffffffffffffff8000000000000007ffffc3f01f80003fffc0001ff42922044bb75dab462226284c4c4c8100480046318303b01d00043f2974000aa
def zsB:W:=0x3f87f80f03f81ff803c003f81fe01c0000000003e0ff79c09801edb18d980067b6b664cc33515be44222c381945048000e80304108a3fb809001f5b295a80022
def zsC:W:=0xc7b878f03c79e3f87c03fc01e1e1e000000000000003bec1f801f3f633e00000f6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zsD:W:=0xff8007ff0007fff8003ffff8001ffc00000000001ffee7c078019c707c78001ff6a464cc08555b504222a301505448000a0034210893eb805001b47014e8000a
def zsE:W:=0x7ff800fff80007ffc00007ffe000000000007fe00118018000638f838001e000120000b32080a42000408484808010048000421020100180004382830000a0
def zsF:W:=0xfffffffffffffffffffffffffffffc000000007ffffc00000001fffffff801fff2b62444bb75d9f46220e185d4d4c8100e80346318b01081d001f7f297e800aa
def zsG:W:=0x3ffc1f80000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zsH:W:=0xff800000fffffff800000000000000000000000000022000000183f0000000000000000000000000000000000000000000000000000000000000000000000000
def zsI:W:=0x7fffff0000000000000000000003ffffffff800001c03e00007c000007fe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zsJ:W:=0x3ffffffff800000003e000000000007fe0009011222000000000000004009091221110888000040006e000008000010aa00
def zsK:W:=0x7fffff000000000000000000000000000000000001c00000007c000000000024244488000001000000810000000000080020000003c0000000b40000000000
def zsL:W:=0xfff80007ffc00007ffe000000000007fe000180187e0038f838001e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zsM:W:=0x7ffffffff80007ffc00007ffe003ffffffffffe001d83f87e07f8f8387ffe02d7fdeaaf7a881a73990d1e6afa993bdddecaa5ad46bd06f86c0ff8f8317ebe0
def zsN:W:=0x7fffff0000000000000000000003ffffffff800003fffffffe7c000007fe002d2556aa0000030000038340090912211908e8000043ef7e292abc000010aa00
def zsO:W:=0xfffffff800000000000000000000007ffffc2001f80003f0000001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zsP:W:=0xffffffff00000007fffffff800000000000000000003df000001fc0ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zsQ:W:=0x7ffffc0001f8000000000001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zsR:W:=0xfffffffffffffffffffffff8000000000000007fffffff01f801fffffc0001ff66b664ccbb75dbb46222e384c4c4c8100c8024631833fb01d000f7f2974000aa
def zsS:W:=0xff8000000000000000000007fffffc0000000000000200c00001800003f800009000000000000040000000011010000002001000008000800001000000a80000
def zsT:W:=0xc0000000fc07e007fc3ffc07e01fe0000000007c1f0006016718024e7260019840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zsU:W:=0x3847870f0000000783fc03fe1e1e1fc1e00f000000004106049e0c09cc1d98000841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zsV:W:=0x3847870fffffffff83fc03fe1e1e1fc1e00f007ffffc6107fc9e0ff9cc1d99ff48c18301d9b6cc31b1542876cececed8a1a50d6fbd7c0005d4940b694b5599fe
def zsW:W:=0x7fffffff8000000000000000000001f000000000ffc000000021220442241128442224280000000000400000000003b000000409294000000
def zsX:W:=0x7fffffffffffffffffffc00fff800000003ffffffd98112229934c87020002045ddddda3113889c6318f000efd0010b6003f8aaaa
def zsY:W:=0xfffffffffffffffffffffffffffffffffffffffffffffffff801ffffffffffffffb776eebb75dbf46222e3c5ddddda311f88bc6318f3fbefd001fff297f8aaaa
def zsZ:W:=0xfffffffffffffff80000000000000000000000000003e0000001fff00000000024244488000001000000810000000000080020000003c0000000b40000000000
def zs0:W:=0xfffffffffffffff800000007ffffffffffffffffffffe0fff801fff003fffffffda556aa9934c9702000a145ddddda311b88bc6318f3c0efd001bf6003f8aaaa
def zs1:W:=0x3f87f80f03f81ff8000000001fe01c01fff00003e0ff60e69801edb00199e067bda556aa11104960000081419d595a211b88b84108e3c0ee9001bd2001b8aa22
def zs2:W:=0x3ff3e07fe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zs3:W:=0xfffffffffffffff800000007fffffffffffffffffffc00000001fff003fffffff9a516229934c9702000a145ddddda310b883c6318f00085d001bf6003f8aaaa
def zs4:W:=0x3e0fff80000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zs5:W:=0x7fffffc0000000000000000c00000000003f800009000000000000040000000011010000002001000008000800001000000a80000
def zs6:W:=0xff800000000000000000000000000000000000000002000000018000000000000000000000000000000000000000000000000000000000000000000000000000
def zs7:W:=0x7807f0fc07e007fc3ffc00000003fe000ffffc1f0086196718124e70061f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zs8:W:=0xfff807f0fc07e007fc3ffc07fffffffe000ffffc1f0286d96719924e73fe1f98d0480110cc26a052b51938177096a15a82465736969404916719024c62ee1598
def zs9:W:=0xffc7870fc3861c0783fc03ffffffffc1e00f007ffffe41c6049f8c09cffd99ff9841830140820441915408731a1a06c8a325190ca5cc00840495080948bd9954
def zta:W:=0x7ff800fff80007ffc00000000003fffff0007fe001182187e0638f8007e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ztb:W:=0x1ff3ffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def ztc:W:=0xc07807f00000000000000007ffffffffffffff80000080fe0000100003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def ztd:W:=0xffffffff03f81ff803c003ffffffffffffffff800003f9fe0001fdb18ffffe00bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zte:W:=0x3fc7ff0fc3fe1fff83fc03fe1e1e1fc1e00f007fffff7906049fedb9cc1d99ff2e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def ztf:W:=0x86fffffe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def ztg:W:=0x3f87f80f03f81ff803c003f800000000000000000003ffffffffedb18c000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zth:W:=0xff800000fffffff800000007fffffffe000ffffffffe20d9ff1983f003fe1fffd0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zti:W:=0x3847870fc3861c0783fc03f81e001c01e0000003e0fc410600860c09cc1980670801820100800401004400600a08068021210808214800040084080108118844
def ztj:W:=0x7ff800fff80007ffc000001fe00001fff00003e001182080e0638f8181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def ztk:W:=0x7ff800fff80007ffc00007ffffe3ffffffffffff011839e7f8638f83e7fff8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def ztl:W:=0x7e01fe3fe000ffffc1f03fffffffe000002661f9844484198cc26a212b51b3a166086a15a9046c7369617ef7b6f3a024c62461598
def ztm:W:=0xfffffffffffffff8000000000000007c1f003f01671803fffc000198425a2154ee67b296f73b7a966086a15a8446473696143f11671842def6461598
def ztn:W:=0xffffffff0000000000000007e01fe3fe000fff800003c0180001fc0002661e0024244488000001000000810000000000080020000003c0000000b40000000000
def zto:W:=0x7fffff00000007fffffff8000003fe000fff800001df1807187c0ffc061e00267e65dc66433386d73bdb922002214a8c4663148607ff102718f49ef4061510
def ztp:W:=0xff800000fffffff800000007e01fe0000000007c1f022001600183f0026001984000000088248010200020044084801000000422101000014000024002400088
def ztq:W:=0xc7b878f03c79e3f87c03fc01e001e03e0000ff800003be196301f3f632620600663e64dcae65b396662bf3846084a1120c4266321213ff116308f6d6b6420488
def ztr:W:=0x3847870fc3861c0783fc03fe001e03c0000f007c1f00410004180c09cc0419980040010040020000911008120002004880040104840400000410000840041110
def zts:W:=0xff8007ff0007fff8003ffff8001fe000000fff801f02e71860199c707c601e18662465dc08473310c62bab1040062042080265240217ef106118b45074401418
def ztt:W:=0xffffffffffffffffffffffffe01fe3fe000ffffc1f0000000001fffffe661f98627e2554ee67b196f738f9966086a15a8c462736961410014610f6def6461598
def ztu:W:=0xc07ffffffc07e007fc3ffc07e01fe3fffffffffc1f01c63f67187e4e7267ff986d6d57bacc26a112b519b956698fb37b994eef369657c47f6718be4c6256bf98
def ztv:W:=0x38000000c3861c0783fc03fe1e1e1c000000007ffffc0100049e0009cc1801ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def ztw:W:=0x3f87f80f00000000000000000000000000000000000340000001ec000000000024244488000001000000810000000000080020000003c0000000b40000000000
def ztx:W:=0xc0000000fffffff800000007e01fe0000000007ffffc2001f80003f0026001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zty:W:=0xff87f80ffffffff800000007fffffc01fff0007fffff60e7f801eff003f9e1fffda556aa9934c9702000a145ddddda311b88bc6318f3c0efd001bf6003f8aaaa
def ztz:W:=0x3fc7ff0fc3861c0783fc03fe1ffe1fc1ffff007fffff41e6049fec09cd9df9ffbd65d7ab40820541915489731b1b16e9bb2db90ca5cfc0ee0495bc0948bdbb54
def ztA:W:=0x780000fff80007ffc00007e00003fe0000007fe000180187e0038f820601e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def ztB:W:=0x3800070f00061c00003c03f8001e1c00000f00001ffc4106001e0c004c18181f080103010002040080440850080a064021010904214400040014080048109814
def ztC:W:=0xffffffff03f81ff803c003f800000000000000000003f9000001fdb18c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def ztD:W:=0xff80000003f81ff800000007fffffc0000000003e0fe20c0980181b003f80067908000001110486000000001945048000280104108a000809001012001a80022
def ztE:W:=0x3807800f03801c0003c003f81e001c01e0000003e0fc410600860c018c1980670801820100800401004400600a08068021210808214800040084080108118844
def ztF:W:=0x3847870f03801c0003c003fe1e1e1fc1e00f0003e0fc410600860c018c1d98670801820100800401004400600a08068021210808214800040084080108118844
def ztG:W:=0x3847870fff87fc07fffffffe1e1e1fc1e00f007ffffc4707679e0e4ffc1d99ff48498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def ztH:W:=0x3f81ff803c003f8000000000000000000003900000001b18c000000021220442241128442224280000000000400000000003b000000409294000000
def ztI:W:=0xfffffffffc07e007fc3ffc0000000000000000000003c6000001fe4e7000000024244488000001000000810000000000080020000003c0000000b40000000000
def ztJ:W:=0x7fffff00000007fc3ffc00000003ffffffff800001c63e07187c0e7007fe002d6d57ba4402210295199952290b336b994eeb148647c47e2718bc0c6016bf10
def ztK:W:=0xc7b878f03c01e0007c03fc01e1e1e03e1ff0ff80000386f96301f24633e26600f52c54ba8c24a1522409b1057195b1331a4af6321293c4fb6309b64422ea2688
def ztL:W:=0x3c0fe000000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def ztM:W:=0x7ff800fc000007fc000007ffe003fffff0007c000100210700620e0387e18000480000c4208002311010062080811880440212940000010600020c02060180
def ztN:W:=0x3c6ff6718000000000000040040880000000000010000000000001000c0000003c47a2108000000000000
def ztO:W:=0xffbff8ff0000000000000001ffe1fc3ffff0ff800003c0fe0001fc0003fbe600bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def ztP:W:=0x7e01fe3fe000fff80000000180000000002661e000000000000000000000000000000000000000000000000000000000000000000
def ztQ:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f01df3f67fe124e72661f9844484198cc26a212b51b3a166086a15a9046c7369617ef7b6f3a024c62461598
def ztR:W:=0x220c1f8000000000000000000000000000000000000000000000000000000000000000000000000000000
def ztS:W:=0xc7f87ff00000000000000007e1ffe3fe1fffff80000380f80001f00003e67e00b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def ztT:W:=0xc006000000000006001e00000000007c1f00000000000000000001980000000000000000000000000000000000000000000000000000000000000000
def ztU:W:=0xfffffffffffffffffffffff81fe01c0000000003e0ffffc09801fffffd980067b6b664cc33515be44222c381945048000e80304108a3fb809001f5b295a80022
def ztV:W:=0x3f80000003f81ff800000000000000000000000000022000000181b0000000000000000000000000000000000000000000000000000000000000000000000000
def ztW:W:=0xc07fffff0000000000000007e01fe3ffffffff800001c03e00007c000267fe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def ztX:W:=0x3f81ff8000000000000000000000003e0fc2000980001b0000000670080000011104820000000008440480000800041082000009000012001000022
def ztY:W:=0xffffffff03f81ff800000007ffffffffffffff83e0ffe0fe9801fdb003fffe67bda556aa11104960000081419d595a211b88b84108e3c0ee9001bd2001b8aa22
def ztZ:W:=0xc7b878f03c79e3f800000001e1e1e03e1ff0ff800003a0f9f801f3f003e26600f5a454aa9934c9702000a105d5d5d8311a88b46318b3c0ebd001b76003e822aa
def zt0:W:=0x3f80000000000000000000001fe01c0000000000000200c000018000019800009000000000000040000000011010000002001000008000800001000000a80000
def zt1:W:=0x3800070f00061c00003c03f8001e1c00000f00001ffc000000000c004c18181f080103010002040080440850080a064021010904214400040014080048109814
def zt2:W:=0xffffffff0007fff8003ffff800000000000000000003e7000001fc707c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zt3:W:=0xc00000000000000000000007e01fe000000000000000000000000000026000000000000000000000000000000000000000000000000000000000000000000000
def zt4:W:=0x3fc7870fc3fe1fff83fc03fe1ffe1fc1e00f007ffffe61c69c9f8db9cd9d99ff98c1830151924c61915408739e5a4ec8a3a5194dadec00849495092949bd9976
def zt5:W:=0x861967180000000000000000000000000000000100000000000000004000000004102108000000000000
def zt6:W:=0x7ff800fc000007ffc00007e00003fffff0007c0001182107e0620f8207e180005a8800e6a88087399050a622a0819cc464021ad408100106c0428f820741c0
def zt7:W:=0x7fc3ffc000000000000000000000006000718000e700000000048011044022002951918122002214a80464314860404102718000c60061510
def zt8:W:=0x3807800fc3861c0003c003fe1e1e1c01e000007ffffc410600860c018c1981ff0801820100800401004400600a08068021210808214800040084080108118844
def zt9:W:=0x780700fc060007fc3c0007e01e03fe000f007c1f0000010718020e4206199800480100c4228002b11018162082815880440316940400010610020c42061190
def zua:W:=0xff800000fffffffffc3ffc07fffffc000000007ffffe26c1ff1983fe73f801ffd0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zub:W:=0x3fe000fff80000000180718000000061e000048011044022002951918122002214a80464314860404102718000c60061510
def zuc:W:=0xfffffffffffffffffffffffffffffffe000fffffffffffd9ff19fffffffe1ffff6fe65dcff77fbf6f73bfb97f4d6e95a8ec677779eb7ff91f719f7fef7ee15ba
def zud:W:=0xfffffffffffffffffc3ffc07ffffffffffffffffffffe6ffff19fffe73fffffffded57badd36e972b519b957fddffb7b9bceff779ef7c4fff719bf6c63febfba
def zue:W:=0xfff807f00000000000000007fffffffe000fff80000280d80001900003fe1e009000000000000040000000011010000002001000008000800001000000a80000
def zuf:W:=0xff800000fffffffffffffff8000000000000000000023f00000183fffc000000021220442241128442224280000000000400000000003b000000409294000000
def zug:W:=0x3f80000003f81ff8000000001fe01c0000000003e0fe20c0980181b001980067908000001110486000000001945048000280104108a000809001012001a80022
def zuh:W:=0xc0000000fc07e00000000007e01fe0000000007c1f00000160000240026001984000000088248010200020044084801000000422101000014000024002400088
def zui:W:=0x7e01fe0000000007c1f00000160000000026001984000000088248010200020044084801000000422101000014000024002400088
def zuj:W:=0xfff8000000000007ffe000000000007fe000000000000380038001e000000000912080202000000484808010008000421020000180000300030000a0
def zuk:W:=0xffffffffffffffffffffffffe01fe0000000007c1f03ff016001fffffe600198663664ccaa6593946222e384408480100c0024221013fb014000f6d296400088
def zul:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc0100049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zum:W:=0xc0000000fc07e0000000000000000000000000000000000000000240000000000000000000000000000000000000000000000000000000000000000000000000
def zun:W:=0xf847870fff87fc0783fc03fffe1fffc1e00f007ffffc4107649e0e49ce7d99ff48418301c8a68411b15428764a8e86d8a1250d2eb55c000544940a494a5599dc
def zuo:W:=0x7f8000ff800007ffc00007fe0003ffe000007fe00000010780020f820781e000488000c4a0800331101026228081988064021a940800010680020d020701c0
def zup:W:=0x3fffe9ffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zuq:W:=0x61c00003c03f800000000000000001ffc0100001e00004c00001f0000010100020400804408100002044020010104210400000014000048001014
def zur:W:=0x3847870f0000000000000007ffffffffffffff80000040fe00000c0003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zus:W:=0xffb878f0fffffff87c03fc07fffffc000000007fffffbec1f801f3f633f801fff6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zut:W:=0x478000c380000783c00007ffe003fffff0007fe000002187e000098387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zuu:W:=0xc7fff8f0fff9e3ffffc3fc07ffe003fffff0007fe003be2187e1f3ffb387e1e0267eecccf7e993a77bb2d3a6a6a0819ccce4225ad42bfb0186c0f79f970741e0
def zuv:W:=0xc7b878f03c79e3f87c03fc0000000000000000000003fffffffff3f630000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zuw:W:=0xfc07e00000000000000000000000007c1f00000160000240000001984000000088248010200020044084801000000422101000014000024002400088
def zux:W:=0xff800000fffffff800000007ffffffc1e00f007ffffe20c7fc9f83f003fd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zuy:W:=0x400700c0060007803c000000000000000000000000000000000008400000000000000000000000000000000000000000000000000000000000000000000000
def zuz:W:=0xc07807f0fc07e007fc3ffc01e001e03e0000ff80000086196300124e72620600400800108c24a012240930046084a11200424632121004116308024422420488
def zuA:W:=0xc07807f0fc07e007fc3ffc07fe1fffffe00ffffffffc861f679e124e727f9fff48498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def zuB:W:=0x3847870fc3861c0783fc03f800000000000000000000410000000c09cc0000000000000000000000000000000000000000000000000000000000000000000000
def zuC:W:=0x7ff800fff80007ffc00007fffe1fffffff007ffffd182787fe638f839ff9ff085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def zuD:W:=0x780000fc07e007fc3ffc07e00003fe0000007c1f0006016718024e7206019840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zuE:W:=0x3fff9fb60000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zuF:W:=0x61e1e1fc1e00f007ffffffffffffe0000001d99ff0c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def zuG:W:=0xff8007ff0007e000003ffc00001ffc00000fff801f02c6de60199c4070781e18fd2557ba080621508409a951591f32631b0afd2402d7c4fe6119bc4060f8be18
def zuH:W:=0xffffffff00000000000000061e1e1fc1e00f00000003c0060001fc00001d98002c254688000001000000814008080200090028000043c0040000bc0000108800
def zuI:W:=0x338e1ffe00000000000000000000000000000000000000000000000000000000000000000000000000000
def zuJ:W:=0x61e1e1fc1e00f007ffffc000000000000001d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zuK:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe0013f21fffe638f8387e1e0005a8800f7a882a7399352a6a6a0819cc4e4425ad4283f11afea438f830741e0
def zuL:W:=0xfffffffffffffffffffffffe1e1e1fc1e00f007ffffc00000001fffffc1d99ff2a77a74562c31585d374c9f20a0a06c8ad25290ca54c10040494fc9bdc159954
def zuM:W:=0x7800000007803f80000000001e0000000000000000220c0980181b001800000908000001110486000000001945048000280104108a000809001012001a80022
def zuN:W:=0x47870fc3861c0783fc03f8000003c1e00f007ffffc4106049e0c09cc0599ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zuO:W:=0xff8007f00007fff8003ffc00001ffc00000fff801ffea6d87819907070781e1fd0800110081668508409281150566842020255250a9404907119006060e8141a
def zuP:W:=0xffb87fff3c7ffff87c3ffff800000000000000000003ff000001fff67c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zuQ:W:=0xc7b878f00000000000000001e1e1e03e1ff0ff80000380f80001f00003e26600b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zuR:W:=0x7ffffffff80007ffffffffffe003fffff0007fe001df2187e07f8fff87e1e0267eecccf7e993a77bb2d3a6a6a0819ccce4225ad42bfb0186c0f79f970741e0
def zuS:W:=0x38000000fffffff8000000061e1e1c000000007ffffc2001f80003f0001801ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zuT:W:=0x3f800000c3fe1ff8000000061ffe1c000000007ffffe20c0980181b0019801ff908000001110486000000001945048000280104108a000809001012001a80022
def zuU:W:=0xffb878f0fffffff800000007fffffc3e1ff0ffffffffa0f9f801f3f003fa67fff5a454aa9934c9702000a105d5d5d8311a88b46318b3c0ebd001b76003e822aa
def zuV:W:=0x478000fff80007ffc000061e0003c1e000007fe000180187e0038f800581e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zuW:W:=0xc7fff8f0fff80007ffc00007ffe1e3fffff0ffffe00398f987e1f38f83e7e7e0b57edcaaf7a881e73990d1a7b7b191bddeecb25ad4abd0eb86c1f78f83af63e0
def zuX:W:=0x1fffe000000000000000000000000000000010000000000000000400000000410292a000000000000
def zuY:W:=0xc7b878f00000000000000001e1e1e03e1ff0ff800003fffffffff00003e26600b52454aa0000034000038301111110211a08f0000083effa292bb40000a82200
def zuZ:W:=0x7ffffc0000049e0000000001ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zu0:W:=0xfffffffffffffffffffffff8000000000000007fffffff00049ffffffc0001ff2676e5cd62c31785d376cbb2020204c8ac25210ca50ffb000494f49bdc051154
def zu1:W:=0xc3861c0783fc03f800000000000000000000010000000009cc0000000000000000000000000000000000000000000000000000000000000000000000
def zu2:W:=0x478700c386000783fc00061e1e03c1e00f007fff00000004980009c00599f8004081004082000191100832020200c88024010c840c00000490000940051150
def zu3:W:=0xfffffffffffffffffffffffe1e1e1fc1e00f00000003ff060001fffffc1d98002e3766cc224113844222c3c0080802000d0028000043fb040000fc9294108800
def zu4:W:=0xffffffffc3861c0783fc03ffffffffffffffffffffffc1fe049ffc09cfffffffbd65d7ab40820541915489731b1b16e9bb2db90ca5cfc0ee0495bc0948bdbb54
def zu5:W:=0xff8000003c79e3f800000007fffffc0000000000000220c1f80183f003f80000d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zu6:W:=0xc78000f00001e3f80003fc0000000000000000000002a6000001907030000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zu7:W:=0x3847870f00000000000000061e1e1fc1e00f00000000400600000c00001d98000801020000000000000000400808020001000800004000040000080000108800
def zu8:W:=0xc3861c0783fc03f8000000000000007ffffc0100049e0009cc0001ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zu9:W:=0x3fefffb60000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zva:W:=0x3c79e3f87c03fc00000000000000000000003e00000003f630000000021220442241128442224280000000000400000000003b000000409294000000
def zvb:W:=0xff8007ff0007fff800000000001ffc00000fff801ffee0de78019c7000781e1ffda556aa081449500000a141595d5a211b08bc2108d3c0ee5001bc6000f8aa0a
def zvc:W:=0x7fffffffffffffffffffc00fe049e000003ffffff9941932340820441915408731b1b16e9b32d990ca5cc00ee0495080948bdbb54
def zvd:W:=0x3ffff80f0000000000000007ffe01ffffff00000000340e60001ec00039fe000bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zve:W:=0xfffffffffffffffffffffffffffffffffffffffffffffffe049fffffffffffffbf77f7ef62c317c5d376cbf31b1b16e9bf2db90ca5cffbee0495fc9bdcbdbb54
def zvf:W:=0xffffffffc3861c0783fc03f800000000000000000003c1000001fc09cc00000024244488000001000000810000000000080020000003c0000000b40000000000
def zvg:W:=0xc07807f0c0060007803c0007e01fe3fe000ffffc1f0080180418100842661f980040010040020000911008120002004880040104840400000410000840041110
def zvh:W:=0x7ff800c380000783c00007ffe003fffff0007fe0010020048060098387e1e00040800040800001111000220200008880240008840800000480000900050140
def zvi:W:=0xff8000003ff9fff800000001ffe1fc0000000003e0fe20c1f80183f003f80067d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zvj:W:=0xf87f87ffff87fc07fffffffffe1fffffe00ffffffffffffffffe1e4ffe7f9fff4c49c399cca6a613b55f3a766a8ea7dab167cf3eb75fef7f6fbe0a4d6a579ddc
def zvk:W:=0x61e1e1fc1e00f00000000000600000000001d98000801020000000000000000400808020001000800004000040000080000108800
def zvl:W:=0xc03800f0fc07e007fc3ffc01e001e03e0000fffc1f0086196718124e7262079840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zvm:W:=0xff800000fffffff80000000000000000000000000003ff00000183f00000000004004088000002000002020000000000000000000003eb000000000000000000
def zvn:W:=0xc07ffffffc07e007fffffff800000000000000000001df0000007e4ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zvo:W:=0xc7fff8f00000000000000007ffe1e3fffff0ff80000380f80001f00003e7e600b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zvp:W:=0xc7f807f0fc7fe3fffc3ffc07e1ffe3fe000ffffc1f02a6d9ff1993fe73e61f98d0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zvq:W:=0x3847870f00000000000000061e1e1fc1e00f00000003fffffffe0c00001d98000c0142880000020000030240080802001100c8000043ef7e292a080000108800
def zvr:W:=0x38000000c3861c0000000007fffffc000000007ffffc00c1f800000003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zvs:W:=0x387fffff00000000000000061e1e1fffffffff800001c03e00007c00001ffe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zvt:W:=0x7807f0c0060007fc3ffc06001e03fe000ffffc1f0086180718100e70061f980048011044022002951918122002214a80464314860404102718000c60061510
def zvu:W:=0xc7b878f000000000000000000000000000000000000380000001f0000000000024244488000001000000810000000000080020000003c0000000b40000000000
def zvv:W:=0xc7fff800fff9e3ffffc00007ffe1e3fffff0007fe00338e1ffe1e3ff83e7e1e0d0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zvw:W:=0xc78000003c79e3f800000001e1e1e000000000000003ffffffff83f003e00000d48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def zvx:W:=0xfffffffffffffffffffffff8000003c1e00f00000003ff06049ffffffc0598002e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def zvy:W:=0x3ff06049e00000000000004004088000002000002020000000000000000000003eb000000000000000000
def zvz:W:=0x783fc03f8000000000000000000000100049e0009cc000000004081014082040191540832020204c8a025010ca50c00000494000948051154
def zvA:W:=0xffffffff0000000783fc03ffffffffffffffff800003c1fe049ffc09cffffe00bd65d7ab40820541915489731b1b16e9bb2db90ca5cfc0ee0495bc0948bdbb54
def zvB:W:=0xc3861c0783fc03f8000000000000007ffffffffffffe0009cc0001ff0440c1894082060191570a32020204c8b025c10ca50fef7a2dbe000948051154
def zvC:W:=0x47870f0000000000000000000003c1e00f00000000400600000c00000598000801020000000000000000400808020001000800004000040000080000108800
def zvD:W:=0x200c000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zvE:W:=0xc03800f0fc07e0007c03fc07e01fe03e0000fffc1f0086196300124632620798400800108c24a012240930046084a11200424632121004116308024422420488
def zvF:W:=0x861860180000000000000000000000000000000100000000000000004000000004102108000000000000
def zvG:W:=0xc07f87fffc07e007ffffffffe01fe3ffe00ffffc1f00c71f679e1e4ffe679f9848498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def zvH:W:=0x387800fff800007c000007ffe0003e1ff0007fe001182183606386038261e0001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zvI:W:=0x47870f0000000783fc03f8000003c1e00f00000003fffffffe0c09cc0598000c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def zvJ:W:=0x3847870f03801c0783fc03f81e001fc1e00f0003e0fc4106049e0c09cc1d98670841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zvK:W:=0x3878f0000000007c03fc00000000000000000000019e000000700630000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zvL:W:=0x7ffffffc1e00f007ffffc00c7fc9e000003fd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zvM:W:=0x400700c3861c0783fc03fe001e03c0000f007ffffc0100049e0009cc0419ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zvN:W:=0xffc7870fffffffff83fc03f800000000000000000002610000018ff9cc0000000000000000000000000000000000000000000000000000000000000000000000
def zvO:W:=0x3878f000000000000000000000003e1ff0ff80000180380000700000026600252454aa0000010000008100010110211808a0000003c06a0000b40000002200
def zvP:W:=0xffffffff83fc03f8000000000000007ffffc2101fc9e03f9cc0001ff40c08101d9b6cc31b1542836c6c6ccd8a0a5056fbd3c0001d49403694b4511fe
def zvQ:W:=0xffffffffffffffff83fc03ffffffffffffffffffffffe1fffc9ffff9cffffffffde5d7abd9b6cd71b154a977dfdfdef9bbadbd6fbdffc0efd495bf694bfdbbfe
def zvR:W:=0xff87f80ffffffff803c003fffffffc000000007fffff79c1f801eff18ff801fff6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zvS:W:=0xc0400700fc07e007803c0007e01fe3c0000f007c1f000001641802484264199840400100c8268010b11028164086805880040526941400014410024842441198
def zvT:W:=0xfffffffffffffffffffffff81fe00001fff00003e003ff2080e1fffffd81e0602636eccc33c913a54aa2c3a0862000844ca02048402bfb0080c0f59395014060
def zvU:W:=0xc0000000fc07e00000000007e01fe0000000007c1f0220c1f8000240026001984000000088248010200020044084801000000422101000014000024002400088
def zvV:W:=0xff80070f0007fff8003c03f8001ffc00000f00001ffe61c6781f8c704c78181fd881030108164c5080442851585e4e4023011d2529d400845015086048f8981e
def zvW:W:=0xffffffff00000000000000000000000000000000000000000001fc00000000002024040000000100000081000000000008002000000000000000b40000000000
def zvX:W:=0xffc7870fffffffff83fc03ffffffffc1e00f007ffffc000000018ff9cffd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zvY:W:=0x261c7fc9e0000000000000000000000000000000000000000000000000000000000000000000000000000
def zvZ:W:=0x3847870ffffffffffffffffe1e1e1fc1e00f007ffffc7f06049e0ffffc1d99ff0a53a34562c31685d3764af20a0a06c8a525090ca54c3b040494489bdc159954
def zv0:W:=0xfff807f0fffffffffc3ffc07fffffffe000ffffffffc0000000193fe73fe1fffd0c80110dd36e872b5183817f4d6e95a82c617779eb40081d611036c63ee15ba
def zv1:W:=0x3807800f03801c0003c003f81e001c01e0000003e0fc4106049e0c018c1980670801820100800401004400600a08068021210808214800040084080108118844
def zv2:W:=0x38000000c3861c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zv3:W:=0x7fffff00000007fffffff800000000000000000003fffffffe7c0ffc000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zv4:W:=0x261c6180600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zv5:W:=0xc3861c0000000000000000000000007ffffc000000000000000001ff0000000000000000000000000000000000000000000000000000000000000000
def zv6:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0000016000124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zv7:W:=0xf9fb60000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zv8:W:=0xfffffff800000000000000000000007ffffffffffffe03f0000001ff448040889934ca3020032204c4c4c8101080c4631833ef7bf92a0360034000aa
def zv9:W:=0x3c79e3f800000000000000000000000000002001f80003f000000000408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zwa:W:=0x3fc7ff0f00000000000000061ffe1fc1ffff0000000340e60001ec00019df800bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zwb:W:=0xffb800f0fffffff87c03fc07fffffc3e0000fffffffea6d9fb0193f633fa07ffd08800109d34e87224093005f4d4e91202c256731ab00491f309036423ea04aa
def zwc:W:=0xc03800f03c01e0007c03fc01e001e03e0000ff800003fffffffe124632620600440840988c24a212240b32046084a1121042c6321213ef7b6b2a024422420488
def zwd:W:=0xffc7870f0000000000000007ffffffc1e00f0000000240c600018c0003fd9800980102000000004000000041181802000300180000c000840001080000b88800
def zwe:W:=0x1e001c01e0000003e0fc000600860000001980670801820100800401004400600a08068021210808214800040084080108118844
def zwf:W:=0xc7f87ff0fc7fe3fffc3ffc07e01fe3fe000ffffc1f03be196719f3fe72661f98667e65dcee67b396f73bfb966086a15a8c4667369617ff116718f6def6461598
def zwg:W:=0xfffffffffffffffffffffff81e001c01e0000003e0ffff060087fffffc1980672e37e6cd22c117854266c3e00a0806802d212808214bfb040084fc939c118844
def zwh:W:=0x3807800f03801c0003c003f800000000000000000000410000000c018c0000000000000000000000000000000000000000000000000000000000000000000000
def zwi:W:=0x3801c0003c003f80000000000000003e0fc0100008600018c0000670000800100800401004400200200048020210008210800000084000108010044
def zwj:W:=0x7800f0000000003c003f800000001e00000000000410600860c018c0180000801820100800401004400600a08068021210808214800040084080108118844
def zwk:W:=0xff87800ffffffff803c003fffffffc01e000007ffffe61c7f8878ff18ff981ffd881820199b4cc7120442065dedcce9023a11c6b39f80085d0850b610bf988ee
def zwl:W:=0x400700c0060007803c0006001e03c0000f007c1f00000004180008400419980040010040020000911008120002004880040104840400000410000840041110
def zwm:W:=0x787800fc780007fc000007e1e003fe1ff0007c000118218760638e03866180005a0800f72880a639905086a4a0811cc4c40252d42010018640438e830641a0
def zwn:W:=0x3807800f03801c0003c003f81e001c01e0000003e0fffffffffe0c018c1980670c01c28900800601004702600a0806803121c808214bef7e29ae080108118844
def zwo:W:=0x7807800007803f8000000000000000000000000000338000001e1b000000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zwp:W:=0xfc07e007fc3ffc00000000000000007c1f03fffffffe024e7000019844484198cc26a212b51b3a166086a15a9046c7369617ef7b6f3a024c62461598
def zwq:W:=0x7807800000000000000000001e000001ff00000000300e00001e00001806000b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zwr:W:=0xff87fc07fffffff8000000000000007ffffc0701679e024ffc0001ff40488111cca6a413b55d38366286a5daa067473eb71c0411679c024d6a4715dc
def zws:W:=0xffffffffff87fc07ffffffffffffffffffffffffffffc7ff679ffe4ffffffffffd6dd7bbcca6a553b55db9777b9fb7fbbb6fff3eb7dfc4ff679dbe4d6affbfdc
def zwt:W:=0xf87f87ff0000000000000007fe1fffffe00fff800000c01e00001c00027f9e000801020000000000000000400808020001000800004000040000080000108800
def zwu:W:=0x2a6d9ff180000000000000000000000000000000100000000000000004000000004102108000000000000
def zwv:W:=0x3f80000000000001fe0000000000003e000000080000180018000600000000011000020000000008400000000800040002000008000010001000020
def zww:W:=0xf8000000ff87fc0000000007fe1ffc000000007ffffc000160000240027801ff4000000088248010200020044084801000000422101000014000024002400088
def zwx:W:=0x3847870fc3861c0783fc03fffe1fffffe00ffffffffc411f679e0c09ce7f9fff48498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def zwy:W:=0x47870fc006000783fc03fe001e03c1e00f007c1f004106049e0c09cc0599980841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zwz:W:=0x400700fc07e007fc3ffc06001e03c0000f007c1f0006016718024e7004199840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zwA:W:=0x387ff80ffff81c07ffc003ffffe01ffffff0007fe0fd592787e66f8f8f9fe1e7085b8a01f7a884a739d450e6aea8879ce5e50a5af568100586c44b8f8b17c9e4
def zwB:W:=0x7ffffffffffffff80000000000000000003fffe00990112220000004000000041191912210308180000c000840001080000b8aa00
def zwC:W:=0xfffffffffc3ffc00000000000000007ffffc2601ff1803fe700001ff40c80110dd36e832b5193816e4c6e95a80c647779e340411f718036c634615ba
def zwD:W:=0x3c01e0007c03fc000000000000000000000006016300024630000000400800108c24a012240930046084a11200424632121004116308024422420488
def zwE:W:=0xfffffffffff80007ffc00007ffe003fffff0007fe003d82187e1ff8f8387e1e0247ecc88f7a881a73990d1a6a6a0819ccce4225ad42bd00186c0f78f830741e0
def zwF:W:=0x780000fc000007fc000007e00003fe0000007c0003fffffffe020e0206018004484088c420820231131206208081189044c2129403ef7b2f2a020c02060180
def zwG:W:=0xf80007ff0007fc00003ffff8001ffc00000fff801ffcc71e601e1c407c781e1f4801031108062410844d2850480e264221034d2423540414611c084068509c1c
def zwH:W:=0x3f87f80f03f81ff803c003f80000000000000000000000000001edb18c00000022362444224111844220c180000000000c002000000010000000f49294000000
def zwI:W:=0xbf19fffe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zwJ:W:=0x3800000000000000000000061e1e1c00000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000000000
def zwK:W:=0xc71f679e0000000000000000000000000000000100000000000000004000000004102108000000000000
def zwL:W:=0xfffffffffff80007ffc00007ffffffffffffffffe003c0fe0001ff8f83ffffe0bd7fdeaaf7a881e73990d1e7bfb993bddfecba5ad4ebd0ef86c1ff8f83bfebe0
def zwM:W:=0x6001e03c0000f007c1f00000004180000000419980040010040020000911008120002004880040104840400000410000840041110
def zwN:W:=0xffffffffc0060007803c0007fffffffffffffffc1f03c0fe0419fc0843ffff98bd6557aa4002014091108953191b12699b0cb90484c7c0ee0411bc0840bcbb10
def zwO:W:=0x7fffffffe000ffffffffc00d9ff18000003fe1fffd0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zwP:W:=0x40070000000007803c0000000003c0000f00000000000004180008400418000040010040020000911008120002004880040104840400000410000840041110
def zwQ:W:=0xffc00700ffffffff803c0007ffffffc0000f007ffffe20c1fc1983f843fc19ffd0c00100d936c870b1102817d4d6c858828415679cb40081d411036843ec11ba
def zwR:W:=0x7ffffffffffffffffffff800000000000000000001ff0000007ffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zwS:W:=0x3fffffff03f81ffffffffff800000000000000000003ff000001fdbffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zwT:W:=0x3fffffbe6000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zwU:W:=0xff8007ff0007fff8003ffff800000000000000000002e70000019c707c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zwV:W:=0xfff8000000000007fffffc000000007ffffc00c1f800038003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zwW:W:=0xff8007fffffffff8003ffffffffffc000000007ffffee7c1f8019ff07ff801fff6a464cc9975db706222a305d4d4c8100a80346318b3eb81d001b77017e800aa
def zwX:W:=0x780000fc000007fc000007e01fe3fe000ffffc1f0000196718020e02661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zwY:W:=0xfff807fffc07fffffc3fffffe01fe3fe000ffffc1f02e71967199e7e7e661f98666c65dccc67b312f73bbb166086a15a884667369617ef116718b65c76461598
def zwZ:W:=0xc0780000fc07e007fc000007e01fe3fe0000007c1f0000016700024e0266019840480000cc248012311030066084811880440632941000014600024c02460188
def zw0:W:=0x478000c380000783c000061e1e1fc1e00f007ffffc0006049e0009801d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zw1:W:=0x7ffe003fffff0007fe000002187e000000387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zw2:W:=0xff800000fffffff800000007fffffc000000007ffffea6d9ff1983f003f801ffd08000009934c87020012005d4d4c8100280546318b00491f109036003e800aa
def zw3:W:=0xffffffffffffffffffffffffffe003fffff0007fe003ff2187e1ffffff87e1e0267eecccf7e993a77bb2d3a6a6a0819ccce4225ad42bfb0186c0f79f970741e0
def zw4:W:=0xffffffff0000000000000000001ffc00000fff800003c0de0001fc0000781e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zw5:W:=0xc3800000000000061e0000000000007fe000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000
def zw6:W:=0xff800000fffffff800000007fffffffffff0007ffffe20e1ffe183f003ffe1ffd0c88800ddbcc87339903027f6f4c99cc2e4167bdcb80081d6c1036d03ef41ea
def zw7:W:=0x7807f000000007fc3ffc000000000000000000000086000000100e700000000000000000000000000000000000000000000000000000000000000000000000
def zw8:W:=0x3847870fc3861c0783fc03f8001e1c00000f00001ffc4106001e0c09cc18181f080103010002040080440850080a064021010904214400040014080048109814
def zw9:W:=0x3f80000003f81ff8000000001fe01c0000000003e0fe20c1f80181b001980067908000001110486000000001945048000280104108a000809001012001a80022
def zxa:W:=0x3847870fc3861c0783fc03fffffe1fffffff007ffffc412787fe0c09cf9ff9ff08498b01d5aa8423b9d41876aeaa87dce1e50b5ef56c000586d40b0d4b17d9f4
def zxb:W:=0x7ff800fff80007ffc000000000000000000000000118000000638f800000000012000022000084000040800000000004000000000010000000408280000000
def zxc:W:=0x1fe01c01fff00000000000e6000000000199e000990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zxd:W:=0x3ffde781e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zxe:W:=0x7ffe003fffff0007fe003fffffffe00000387e1e00448c888d5a8822339931226a6a0819cd0e4c25ad42bef7bafea030d030741e0
def zxf:W:=0xfffffffffffffffffffffff8001e1c00000f00001fffff06001ffffffc18181f2e3767cd22431784c266cbd0080a06402d0129042147fb040014fc92dc109814
def zxg:W:=0xffffffff0000000000000007ffe003fffff000000003c0200001fc000387e00024244488000001000000810000000000080020000003c0000000b40000000000
def zxh:W:=0xc7b878f03c79e3f87c03fc01e1e0003e1ff000000003be218361f3f633826000263e6cccb76993a66aa2d384a4a081144cc022525023fb018240f796970240a0
def zxi:W:=0x7ff800fff80007ffc000061e0003c1e000007fe00118000480638f800581e00052800062800085111040a20200008884240008840810000480408b80050140
def zxj:W:=0x7ffffffffffffff800003fffffffe000003fffe009d0152aa0000024000030241191912211308d80000c3effe292b080000b8aa00
def zxk:W:=0x7e00003fe0000007c00000001070000000206018000480000c4208002311010062080811880440212940000010600020c02060180
def zxl:W:=0xffffffffffffffffffffffffffe003fffff0007fe00000000001ffffff87e1e0227eac44f7e991a77bb0d1a6a6a0819ccce4225ad428100186c0f79f970741e0
def zxm:W:=0x3ff2187e000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zxn:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe000002187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zxo:W:=0xffffffff0000000000000007fffffc00000000000003c0c00001fc0003f80000b42444880000014000008101101000000a0030000083c0800001b40000a80000
def zxp:W:=0xff8007ff0000000000000007ffffffffffffff800002c0fe00019c0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zxq:W:=0x7fffff00000007fffffff8000003fffff000000001df2007e07c0ffc07e000267eeccc66c913875bb2d3a22220018ccc642218c40bfb0006c0f49f94074140
def zxr:W:=0x3f80000f000000000000000000001c0000000000000240c600018c0000180000bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zxs:W:=0xfffffffffff80007ffc00007ffffffffffffff800003d8fe0001ff8f83fffe00bd3756aa220001c40000c1c1191912211f08b80000c3d0ee0001fc8280b8aa00
def zxt:W:=0xff8000000007fff800000007fffffc000000007ffffe20c1f801807003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zxu:W:=0xfffff800ffffffffffc00007fffffc000000007fffff38c1f801e3ff83f801ffd0920000bb34c8f420006085d4d4c8100680146318b01081d00143e283e800aa
def zxv:W:=0xc00007f00007e000003ffc07e01fe3fe000ffffc1f0086196718104072661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zxw:W:=0x3800070f00061c00003c03fe1e1e1fc1e00f007ffffc4106049e0c004c1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zxx:W:=0x387fff0ffffe1c07fffc03fe1e1e1fc1e00f007ffffd5906049e6f8fcc1d99ff0853830162820485915448f20a0a06c8a525090ca54c10040494488bc8159954
def zxy:W:=0x3fc7ff0fc3fe1fff83fc03f80000000000000000000379000001edb9cc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zxz:W:=0x2e7fffffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zxA:W:=0xffc787ffc387ffff83fffffe1e1e1fc1e00f007ffffee706049f9c79fc1d99ff2e65e7cd40c31701d3768b720a0a06c8a925290ca54feb040494bc195c159954
def zxB:W:=0x7ff800fffffffffffffff8000000000000000000013f00000063fffc000000021220442241128442224280000000000400000000003b000000409294000000
def zxC:W:=0x1ffc00000fff80000000de0000000000781e00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zxD:W:=0xfffffff800000007ffe000000000007ffffc2001f80003f0038001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zxE:W:=0xc3861c0783fc03f8000000000000007ffffc000000000009cc0001ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zxF:W:=0xff8007fffffffff800000007fffffc00000ffffffffee0dff8019ff003f81ffffda556aa9934c9702000a145ddddda311b88bc6318f3c0efd001bf6003f8aaaa
def zxG:W:=0xffc787ffc3861c0783fc03fe1e1fffc1e00ffffffffec1de049f9c09cc7d9fffbd65d7ab40820541915489731b1b16e9bb2db90ca5cfc0ee0495bc0948bdbb54
def zxH:W:=0xfffffffffffffffffffffffffffffc000000007fffffff000001fffffff801fff6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zxI:W:=0x7fe000000187e00000000001e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zxJ:W:=0xfffffffffffffffffffffff8000000000000007fe003ff0187e1fffffc0001e0267eecccf7e993a77bb2d3a6a6a0819ccce4225ad42bfb0186c0f79f970741e0
def zxK:W:=0x3847870ffffffffffffffff8000000000000000000007f0000000ffffc000000021220442241128442224280000000000400000000003b000000409294000000
def zxL:W:=0xff800000fffffff800000000000000000000000000000000000183f0000000000000000000000000000000000000000000000000000000000000000000000000
def zxM:W:=0xffc7870ffffffff800000007ffffffc1e00f007ffffe60c7f8018ff003fd99ffd88102009934c87020002045dcdcca1003801c6318f00085d0010b6003f888aa
def zxN:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0006016718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zxO:W:=0xff800000ffffffffffc00007fffffc000000007ffffe38c1ffe183ff83f801ffd0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zxP:W:=0x3847870ffffe1c07fffc03fe1e1e1fc1e00f007ffffc590787fe0f8fcc1d99ff085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def zxQ:W:=0x7fffff00000007fffffff8000003c1e00f00000001df06049e7c0ffc0598002e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def zxR:W:=0x38478000c3861c0783c000061e1e1fc1e000007ffffc000004800009801d81ff0040800040800001111000220200008880240008840800000480000900050140
def zxS:W:=0x7fffff00000007fffffff8000003ffffffff800001df3e00007c0ffc07fe002f3776ee224113844222c3c0090912211d08a8000043fb6e0000fc929410aa00
def zxT:W:=0xc7f87ff0fc7fe3fffc3ffc0000000000000000000003be000001f3fe70000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zxU:W:=0x3e7fe781e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zxV:W:=0xfff80007ffc00000000000000000007fe003fffffffe038f800001e0045ac888f7a882a7399352a6a6a0819cd4e4c25ad42bff7bafea438f830741e0
def zxW:W:=0x7fff8003ffff8000000000000000000002700000000707c000000020020440041120042220200000000000000000000002b000000001014000000
def zxX:W:=0xfffffffffff80007ffc0000000000000000000000003d8000001ff8f8000000024364488220001840000c180000000000c0020000003d0000000f48280000000
def zxY:W:=0xc07807f0fc000007fc000007e01fe3fe000ffffc000080190700120e02661f8000480000c4208002311010062080811880440212940000010600020c02060180
def zxZ:W:=0x7ff800fff80007ffc00000000000000000007fe001180187e0638f800001e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zx0:W:=0xc7b878f03c7800007c000001e1e1e03e1ff0ff80000398f98361f38603e26600b53e5caab72881e62880d185b5b191355ec8b25250a3d0eb8241f78683aa62a0
def zx1:W:=0xffffffffc3861c0783fc03fffffffffffffffffffffffffffffffc09cfffffffbd65d7ab4082074191578b731b1b16e9bb2df90ca5cfeffe2dbfbc0948bdbb54
def zx2:W:=0x47f800c3f8000783c000061fe003c1fff0007fe001182084e061898185e1e000528800738800a5199040a28620008cc4a40048c428100084c0418b81054160
def zx3:W:=0xfffffffffc07e007fc3ffc07fffffffffffffffc1f0000000001fe4e73ffff98f96d1732cc26a152b518b957799fb37b8b4e3f3696d400854611be4c62febf98
def zx4:W:=0xffc787ffc387ffff83fffff800000000000000000002e70000019c79fc000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zx5:W:=0x7ffe003fffff0000000000020000000000387e0000000000000000000000000000000000000000000000000000000000000000000
def zx6:W:=0x3ff19671800000000000004004088000002000003020000000000000040000003ef102108000000000000
def zx7:W:=0xffffffff00000000000000001fe01c01fff000000003c0e60001fc000199e000bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zx8:W:=0x7fffff00000007fffffff800000000000000000003ff0000007c0ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zx9:W:=0x4007000000000000000006001e03c0000f00000000000000000000000418000000000000000000000000000000000000000000000000000000000000000000
def zya:W:=0x7ff800000000000000000000000000000000000001000000006000000000000000000000000000000000000000000000000000000000000000000000000000
def zyb:W:=0x780000fff80007fc000007ffe003fe0000007fe00000018700038e038601e000480000d520802231101006a480811880c40252942000018600030c030601a0
def zyc:W:=0xc0000000fc07e00000000007e01fe3fe000ffffc1f0000196718024002661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zyd:W:=0x3ffff80ffff81fffffc003ffffe003fffff0007fe003792187e1efbf8f87e1e0267eecccf7e993a77bb2d3a6a6a0819ccce4225ad42bfb0186c0f79f970741e0
def zye:W:=0xfff8000000000007ffe000000000007fe000000180000380038001e000000000912080202000000484808010008000421020000180000300030000a0
def zyf:W:=0xff8000000007fff800000000001ffc00000000001ffe20c0780180700078001fd080000008144850000020015054480002001421089000805001006000e8000a
def zyg:W:=0xffff87ffffffffffffffffffffffffffe00ffffffffee7dfff9f9fffffff9fffd8c98311ddb6ec73b55d3877fedeefdaa3e75f7fbffc0495f79d0b6d6bff9dfe
def zyh:W:=0xfffffffffffffffffffffff8001ffc00000fff800003ffde0001fffffc781e00bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zyi:W:=0xc7b800f03c79e3f87c03fc01e1e1e03e0000ff800002a6d9fb0193f633e20600d08800109d34e87224093005f4d4e91202c256731ab00491f309036423ea04aa
def zyj:W:=0xffffffffffffffffffffffffffe003fffff0007fe003ffffffffffffff87e1e0267eecccf7e993a77bb3d3a6a6a0819cdce4e25ad42bff7bafeaf79f970741e0
def zyk:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00118000000638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zyl:W:=0xfffffffffffffffffffffffe1e1e1fc1e00f007ffffc4106049ffffffc1d99ff2a77a74562c31585d374c9f20a0a06c8ad25290ca54c10040494fc9bdc159954
def zym:W:=0x3bef9ff78000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zyn:W:=0x387fff0ffff80007ffc00007fffe1fffffff007fe001582787e06f8f839ff9e0085b8a00f7a880a7399050e6aea8839cc5e40a5ad468100586c04b8f8317c9e0
def zyo:W:=0xfffffffffffffffffffffff8001ffc00000000001fffffc07801fffffc78001ff6b664cc2a555bd44222e381505448000e0034210893fb805001f4f294e8000a
def zyp:W:=0xffbff8ff3ff9fff87fc3fff800000000000000000003ff000001fff7bc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zyq:W:=0x7fffff0000000000000007ffe003ffffffff800001c03e00007c000387fe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zyr:W:=0xfffffffffffffffffffffff81fe01c01fff000000003ffe60001fffffd99e000bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zys:W:=0x7fff80000000000000000000000001ffc2000780000700000001f408000000814481000002000404448000000042108100000500000600040000a
def zyt:W:=0xfff807f0fc07fffffc3ffc07e01ffffe000ffffc1ffea6d97f19927e727e1f9fd0c80110cc36e852b519381770d6e95a824657379e9404917719026c62ee159a
def zyu:W:=0x400700c0060007803c0006001e03c0000f007c1f03fffffffe000840041998044041884002020091130a12000200489004c1048407ef7a2d3a000840041110
def zyv:W:=0xffc7870fc387ffff83fc03fe1e1fffc1e00f007ffffe61c67c9f8c79cc7d99ffd8c1830148964c51915428735a5e4ec8a3251d2daddc00845495086948fd995e
def zyw:W:=0xff87f80f0000000000000007fffffc01fff00000000340e60001ec0003f9e000bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zyx:W:=0x3800000003801c00000000001e001c0000000003e0fc000000000000001800670000000000000000000000000000000000000000000000000000000000000000
def zyy:W:=0x3c78000000000001e1e000000000000000000001800003800380000000000000912080202000000484808010008000421020000180000300030000a0
def zyz:W:=0xff8007fffffffff8003ffff800000000000000000002e70000019ff07c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zyA:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007fffffc1fe049e0c09cc1d99ff0c41c38940820401915408720a0a06c8b125890ca54fc06e0494080948159954
def zyB:W:=0xfffffffffffffffffffffff8000003fffff000000003ff2007e1fffffc07e000267eeccc66c913875bb2d3a22220018ccc642218c40bfb0006c0f49f94074140
def zyC:W:=0xff8007ff0000000000000007fffffc00000fff800002c0de00019c0003f81e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zyD:W:=0xfffffffffffffffffffffffffffffffffffffffc1f03ffff6719ffffffffff98ff7f77feee67b3d6f73bfbd7799fb37b9f4eff3696d7ffff6719fedef6febf98
def zyE:W:=0x7ffc0000000000000000000000000180007e0000f80000000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zyF:W:=0xffffffff00000007ffc00007ffffffffffffff800003d8fe07e1fc0f83fffe00bd7fdeaa668801c71990d1e33b3913addf6cba18c4cbd0ee06c1fc8f80bfeb40
def zyG:W:=0x7ff8000000000000000000000003fffff0000000010020000060000007e0000000000000000000000000000000000000000000000000000000000000000000
def zyH:W:=0x387fff0fc3861c07fffc03fe1e1e1fffffff007ffffd592607fe6c0fcc1ff9ff085b8b01668a048799d458f22a2a07cce5650b1ce54c100406d4488fc817d954
def zyI:W:=0xff8000000000000000000007fffffc00000000000003ffffffff800003f80000940040880000024000030201101000001200d0000083effa292b000000a80000
def zyJ:W:=0x7ff80000000007ffc00000000003fffff000000003fffffffe600f8007e000045ac88866880287199352a22220018cd464c218c40bff7a2fea408f80074140
def zyK:W:=0x7ff00000000003ffff800000000000000000000c70000001c007c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zyL:W:=0xfffff800ffffffffffc000000000000000000000000338000001e3ff800000000012000022000084000040800000000004000000000010000000408280000000
def zyM:W:=0xffffffffffc00000000000000000007ffffc3801ffe003ff800001ff40da8800ffbcc8b7399070a6e6e4c99cc4e4067bdc381001d6c043ef834741ea
def zyN:W:=0xffffffffffffffffffc00007fffffffffffffffffffff8ffffe1ffff83fffffffdffdeaaffbcc9f73990f1e7fffddbbddfecbe7bdcfbd0efd6c1ffef83ffebea
def zyO:W:=0x7fffffffffffffffc1f0000ff6718000003ffff98d9491332cc26a052b5193857799fb37b934edf3696d404ff67190a4c62febf98
def zyP:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f03ff196718124e72661f9844484198cc26a212b51b3a166086a15a804647369617ef116718024c62461598
def zyQ:W:=0xfffff8000000000000000007fffffffffff00000000300e00001e00003ffe0009000000000000040000000011010000002001000008000800001000000a80000
def zyR:W:=0xc7b878003c79e3f87c000001e1e1e03e1ff00000000338e1fb61e3f603e26000d09a0800bf3cc8f628807085f4f4c91446c0167358b01081d24143e683ea40aa
def zyS:W:=0x19e380360000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zyT:W:=0x7fffff0000000000000000000003ffffffff800003c0fe00007c000007fe002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zyU:W:=0xffffffff0007fffffffffff800000000000000000003ff000001fc7ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zyV:W:=0x7ffe000000000007fe000000180000000038001e000000000912080202000000484808010008000421020000180000300030000a0
def zyW:W:=0xffffffffffffffffffffffffffe000000000007fe003ff018001ffffff8001e0263664ccb36193a46222c384848080100c8020421023fb018000f792970000a0
def zyX:W:=0xffffffff0000000000000000001fffffffffff800003c0fe0001fc00007ffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zyY:W:=0x7ffffffffffffffffe00000ff87e0000003ffffe099499a22d5a8806339901067bfb993bdd3ec9a5ad4e800ef86c10b0d03bfebe0
def zyZ:W:=0xfff8000000000000000000000000007fe000000180000380000001e000000000912080202000000484808010008000421020000180000300030000a0
def zy0:W:=0x3847870f00061c0783fc03f8001e1fc1e00f00001ffc4106049e0c09cc1d981f0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zy1:W:=0x3847870ffffe1c0783fc03fffffe1fc1e00f007ffffc4107849e0f89cf9d99ff08418301d1a28421b15408768e8a86d8a1a5094eb56c000584940b094b1599f4
def zy2:W:=0x3fffe7ffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zy3:W:=0x478000c3861c0783fc03fe1e0003c1e000007ffffc0100049e0009cc0581ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zy4:W:=0x3ffff80ffff81fffffc003f80000000000000000000379000001efbf8c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zy5:W:=0xc07807f0fc07e00000000007e01fe3fe000ffffc1f0080196000124002661f984000000088248010200020044084801000000422101000014000024002400088
def zy6:W:=0x7e000003ffc0000000000000000001f00060060180040700000184000011008062010840928104006204200024524021404106118004060401418
def zy7:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffddf3e07fe0c09cc1d99ff0c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def zy8:W:=0xc00007f00000000000000000001fe000000fff80000080180000100000601e000000000000000000000000000000000000000000000000000000000000000000
def zy9:W:=0xff8007f0fffffff8003ffc07fffffc00000ffffffffea6d9f81993f073f81fffd08001109936e870a4092815d4d6e852028255671ab40491f119036063e814ba
def zza:W:=0x3ff00000000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zzb:W:=0xff8000003c7ffff800000001e1fffc00000000001ffe20c1f80183f003f8001fd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zzc:W:=0xff800000fffffff800000007fffffffffffffffffffe20fff80183f003ffffffd98112229934c87020002045ddddda3113889c6318f000efd0010b6003f8aaaa
def zzd:W:=0x1fe00001fff00003e000002080e000000181e0600000880011880021088000208620008440a000484028000080c0010101014060
def zze:W:=0xc03800f03c01e0007c03fc01e001e03e0000ff80000086196718124632620600400800108c24a012240930046084a11200424632121004116308024422420488
def zzf:W:=0xfff807ff0000000000000007e01ffffe000fff800002c0de00019c00027e1e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zzg:W:=0x3f8000003c000000000000000000003e000180080e001818000006000128800338800a5088040a08620008444a000484028100080c0418381014060
def zzh:W:=0x3c1e00f000000000006049e0000000598000841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zzi:W:=0xffffffff0007fff800000007ffffffffffffff801fffe0fe7801fc7003fffe1ffda556aa081449500000a141595d5a211b08bc2108d3c0ee5001bc6000f8aa0a
def zzj:W:=0x7f8000000000003c0000000000001fff000000001182000e060018001e0000012880022880085088040a002200084442000084008100000c0408380014040
def zzk:W:=0x3840070fc0061c07803c03fe001e1fc0000f007c1ffc4106041e0c084c1c199f084103014002040091540852080a0648a1050904a54400040414080848149914
def zzl:W:=0x3847ff0fc3fe1c0783fc03fe1ffe1fc1ffff007ffffd592684fe6d89cd9df9ff08538b01738a04a599d448f28e2a06cce5a5094ce56c100484d4498bc915d974
def zzm:W:=0x2e7df7f1e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zzn:W:=0xffffffffffffffffffffffffffffffffffffffffe003ffff87e1ffffffffffe0bf7ffeeef7e993e77bb2d3e7bfb993bddfecba5ad4ebfbef86c1ff9f97bfebe0
def zzo:W:=0x61e1e1fc1e00f007ffffc00fffffe0000001d99ff0841830140820401915508720a0a06c8b125c90ca54c047e2dbe080948159954
def zzp:W:=0x7f80003f8000003c000001fe00001fff00003e003fffffffe61818181e0600412c888338802a5088342a08620008454a0c048402bff7aa9ea418381014060
def zzq:W:=0xff8007ff0000000000000000001ffc00000fff800000000000019c0000781e00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zzr:W:=0xc00000f00001e0000003fc000001e0000000ff800000861860001040306006004000001008042010040920004004200200024420021004106108004020400408
def zzs:W:=0x3f80000f00001ff8000003f800000000000000000002610000018c300c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zzt:W:=0x7ffffe3ffffffffffff000039e7f8000003e7fff840488910ddaea033bd993836e6a6a1dec0e6477ed63c0411e7d8034d634755f8
def zzu:W:=0xffffffffffffe007fffffc07ffffffffffffffffff03deffe7f9ffcff3fffff8fd7fdfbaffaea1f7bd99f9f7ffbfb3ffdfeeff7ed6ffd4ffe7d9ffcfe3fffff8
def zzv:W:=0xfffff800ffffffffffc00007fffffffffff0007ffffd182187e1e3ff83ffe1ffd0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zzw:W:=0xff800000fff8000000000007fffffc000000007fe00200c18001838003f801e0900000009120806020000005949080100280104210a000818001030003a800a0
def zzx:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffcc71f679e0c09cc1d99ff0841830140820401915508720a0a06c8a125490ca54c0414259c080948159954
def zzy:W:=0x3f80000000001ff80000000000001c000000000000fe20c018018030001800079080000000104840000000011050480002001001088000801001002000a80002
def zzz:W:=0x3c1fe049e00000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zzA:W:=0xfffffffffffffff8000000000000007fe0003f0187e003fffc0001e0025aa844f7e992a77bb252a6a6a0819cc4e4025ad4283b0186c0439f970741e0
def zzB:W:=0x3f87f80f00000000000000001fe01c01fff00000000000000001ec000199e000b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zzC:W:=0xfc07e007fc3ffc00000000000000007c1f0000000000024e7000019840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zzD:W:=0xfffffffffffffffffffffff8000003fe000fff800003ff180719fffffc061e00267e65dc66433386d73bdb922002214a8c4663148607ff102718f49ef4061510
def zzE:W:=0xffb878f00000000000000007fffffc3e1ff0ff80000380f80001f00003fa6600b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zzF:W:=0xfffffffffffffffffffffff8000003ffffffff800003ff3e0001fffffc07fe002f3776ee224113844222c3c0090912211d08a8000043fb6e0000fc929410aa00
def zzG:W:=0x7ff80000000007ffc000000000000000000000000118000000600f800000000012000022000084000040800000000004000000000010000000408280000000
def zzH:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f02e7df7f1e124e72661f9844484198cc26a212b51b3a166086a15a9046c7369617ef7b6f3a024c62461598
def zzI:W:=0x780000fc000007fc000007e00003fe0000007c000000010700020e0206018000480000c4208002311010062080811880440212940000010600020c02060180
def zzJ:W:=0xffffffffc380000783c00007ffffffffffffffffe003c0fe0481fc0983ffffe0bd65d6aa40800141111081631b1912a99b2cb80884cbc0ee0481bc0900bdab40
def zzK:W:=0xc0000000fc07e00000000007e01fe0000000007c1f00861967180240026001984000000088248010200120044084801000004422101004116108024002400088
def zzL:W:=0xffffffff03801c0003c003ffffffffffffffff83e0ffc1fe0087fc018ffffe67bd25d6ab00800541004481611b1916a13b29b80821cbc0ee0085bc0108b9aa44
def zzM:W:=0xffffffffffffffffffffffffffffe3ffffffffffff03ff39e7f9ffffffe7fff8667eeddcffefb3b7ffbbfbb6e6a6a1decce6677ed63fff11e7d8f7dff74755f8
def zzN:W:=0xc00007f00007e000003ffc00001fe000000fff801f03fffffffe104070601e184400419808062210840b2a10400620421002c5240217ef7a693a004060401418
def zzO:W:=0xff87ffff03fffff803fffff800000000000000000003ff000001fdf1fc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zzP:W:=0xc78000003c79e3f800000000000000000000000000022000000183f0000000000000000000000000000000000000000000000000000000000000000000000000
def zzQ:W:=0x780000fc000007fc0000000000000000000000000000000000020e000000000000000000000000000000000000000000000000000000000000000000000000
def zzR:W:=0xfffffffffc000007fc000007fffffffffffffffc0003c0ff0701fe0e03ffff80bd6d56aac420814231109147399993399b4cba1294c3c0ef0601be0c02beab80
def zzS:W:=0xc1f8000000000000000000000000000000000000000000000000000000000000000000000000000000
def zzT:W:=0x78000000000007fc000000000003fe00000000000000000700000e000600000048000044000002111010022000010880440210840000000600000c00060100
def zzU:W:=0x7800000000000000000007e00003fe000000000000000000000000020600000000000000000000000000000000000000000000000000000000000000000000
def zzV:W:=0x4106049e0000000000000000000000000000000000000000000000000000000000000000000000000000
def zzW:W:=0xff80000003fffff8000000001ffffc0000000003fffe20c0f80181f001f8007fd08000001914487000002001d45448000280146108b00080d001016001e8002a
def zzX:W:=0x7807f00000000000000000000003fe000fff80000080180000100000061e000000000000000000000000000000000000000000000000000000000000000000
def zzY:W:=0x3807870f03861c0003fc03f81e1e1c01e00f0003fffc4106009e0c01cc19987f0801830100820401804408700a0a06c02121090c214c00040094080148119854
def zzZ:W:=0x387f870fff861c07fffc03fffe1e1fffe00f007ffffc4107079e0e0fce1f99ff08498301c4a28403b15418762a8a87d8a1650b1eb54c000506940a0d4a1799d4
def zz0:W:=0x7ffff000000007fffffc00000003ffffffff8000019e3807f8700ff007fe00005a8910668a20879d9958b2222221cec466431cc60c141027d8408fe0075550
def zz1:W:=0xff8007ff0007fff8003ffff8001e1c00000f00001ffee706001f9c707c18181f2e2567cd00431700c2668b50080a0640290129042147eb040014bc105c109814
def zz2:W:=0x3f000000000000000000000000000000020000020200000000000000000000002b000000000000000000
def zz3:W:=0x7ff800fff80007ffc0000000000000000000000003ff000000638f8000000004124088220002840002428000000000040000000003fb000000408280000000
def zz4:W:=0x1e1c00000f00001ffc0006001e00000018181f080103010002040080440850080a064021010904214400040014080048109814
def zz5:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f03fffffffe124e72661f9844484198cc26a212b51b3a166086a15a9046c7369617ef7b6f3a024c62461598
def zz6:W:=0x7fff0f00000007fffc03f8000003ffffff00000001592607fe6c0fcc07f800085b8b01668a048799d458f22a2a07cce5650b1ce54c100406d4488fc817d954
def zz7:W:=0x3800070f00061c00003c03f800000000000000000000410000000c004c0000000000000000000000000000000000000000000000000000000000000000000000
def zz8:W:=0x3807800f00000000000000001e001c01e00000000000400600000c00001980000801020000000000000000400808020001000800004000040000080000108800
def zz9:W:=0xffffffff00000007fc3ffc07ffffffffffffff800003c6fe0719fc0e73fffe00bd6d57ba4402214295199953391b336b9b4efb1486c7c4fe2719bc0c60bebf10
def zAa:W:=0x70f00000000003c03f800000000000f000000004106001e0c004c001800080103010002040080440850080a064021010904214400040014080048109814
def zAb:W:=0x3800000000061c0000000000001e1c00000000001ffc0000000000000018001f0000000000000000000000000000000000000000000000000000000000000000
def zAc:W:=0xc07800f0fc01e007fc03fc07e001e3fe0000fffc000086196700124e3266078040480010cc24a012351930066084a11a80464632961004116708024c22460588
def zAd:W:=0xc71e001e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zAe:W:=0xff87f800fffffff803c00007fffffc01fff0007fffff38e1f8e1e3f183f9e1ffd0928800bbbcc8f5288060a5d6f4c89446a0146b58b81081d0c143e383e940ea
def zAf:W:=0xc78000003c79e3f800000001e1e1e0000000000000000000000183f003e00000d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zAg:W:=0xff800000fffffff800000007fffffc000000007ffffc2001f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zAh:W:=0xc03878f03c79e0007c03fc01e1e1e03e1ff0ff8000019e39e36073c633e26600401a0810bf2ca0b62c897084e4a4a11644c2467252301411e34843c6a34244a8
def zAi:W:=0xf87807fffc07fc07fc3fffffe01ffffe000ffffc1ffcc71f671e1e4e7e7e1f9f48490311cc26a412b55d3856688ea75aa1474f36b7540415671c0a4c6a569d9c
def zAj:W:=0xffffffff3c79e3f800000007ffffffffffffff800003e0fff801fff003fffe00fda556aa9934c9702000a145ddddda311b88bc6318f3c0efd001bf6003f8aaaa
def zAk:W:=0xffffffff000000000000000000000000000000000003ff000001fc000000000024244488000003000002830000000000080020000003eb000000b40000000000
def zAl:W:=0x70000060000003c0000001e0000000f00001f00000000180000400018180000010000020000800008100002004000000104000400000010000040001010
def zAm:W:=0xfffffffffffffffffffffff9e1e0003e1ff000000003ff218361ffffff826000263e6cccb76993a66aa2d384a4a081144cc022525023fb018240f796970240a0
def zAn:W:=0x3878003c7800007c00000000000000000000000001180000006386000000000012000022000084000040800000000004000000000010000000408280000000
def zAo:W:=0xffc787ff00000000000000061e1fffc1e00fff800002c0de00019c00007d9e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zAp:W:=0x3f87f80f00000000000000001fe01c01fff00000000379e698e7ec000199e000bd2556aa0000034000028341191912211b08b80000c3ebee0823bc0000b8aa00
def zAq:W:=0xc07ffff0ffffe007fffffc00000000000000000000019e00000073cff00000000012000022000084000040800000000004000000000010000000408280000000
def zAr:W:=0x387800000000007c0000000000003e1ff00000000118200360600600026000001a080026080086088050802020010444400210400010000240408680024000
def zAs:W:=0xff8000000000000000000007fffffc0000000000000000000001800003f800009000000000000040000000011010000002001000008000800001000000a80000
def zAt:W:=0xfc00000000000007e00000000000007c0000000100000200020001800000000080208000200000040080801000000002100000010000020002000080
def zAu:W:=0xfffffffffffffffffffffff800000000000000000003ffde781ffffffc000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zAv:W:=0xfffffff800000000000000000000007ffffc3f01fffe03f0000001ff408000009934ca3020032204c4c4c8100080446318302f11f92a0360034000aa
def zAw:W:=0x7800007800000000000001e000001ff0000000011820806061800180600000120800330800a4088040808420000444800040402010008040418281004020
def zAx:W:=0x7807f000000007fc3ffc00000003fe000fff800003fffffffe100e70061e000448419844022202951b1a122002214a9046c3148607ef7a2f3a000c60061510
def zAy:W:=0xffffffff3c79e3f87c03fc07ffffffffffffff800003fefe0001fff633fffe00bf3776ee224113c44222c3c1191912211f08b80000c3fbee0001fc9294b8aa00
def zAz:W:=0x478000c380000783c000061e0003c1e000007fe000000004800009800581e00040800040800001111000220200008880240008840800000480000900050140
def zAA:W:=0x7f000000000003ffc0000000000000fff80000086180018100070001e000000011000022000840908100002204200024104020404102118000060001410
def zAB:W:=0x1ffc00000000001ffc00c0780000000078001fd080000008144850000020015054480002001421089000805001006000e8000a
def zAC:W:=0xc78000f000000000000000000001e0000000ff80000280d80001900000600600b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zAD:W:=0x7fffe1fffffff007ffffc002787fe0000039ff9ff08498b01d5aa8423b9d41876aeaa87dce1e50b5ef56c000586d40b0d4b17d9f4
def zAE:W:=0x387fff0f0000000000000007fffe1fffffff00000001402600006c00039ff8000801020000000000000000400808020001000800004000040000080000108800
def zAF:W:=0xfffffffffffffffffffffff80000000000000000000379000001fffffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zAG:W:=0xfff800000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000000000000
def zAH:W:=0x7ff80000000007ffc00000000003fffff00000000000000000600f8007e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zAI:W:=0x7f80000000000000000001fe00001fff0000000010020000060000181e0000000000000000000000000000000000000000000000000000000000000000000
def zAJ:W:=0xff800000fffffff800000007fffffc000000007ffffee7dff81f83f003f801ffd48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def zAK:W:=0x60167180000000000000000000000000000000100000000000000004000000004102108000000000000
def zAL:W:=0x387fff0ffffe1c07fffc03fffffe1fffffff007ffffc000000006f8fcf9ff9ff085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def zAM:W:=0x1592787fe0000000000000000000000000000000000000000000000000000000000000000000000000000
def zAN:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007fffffff06049e0c09cc1d99ff0c41c3894082060191560a720a0a06c8a125090ca54feb040494080948159954
def zAO:W:=0xfffffffffffffffffffffffe1e0003c1e000007fe003ff000481fffffc0581e02676e4cc62c113855332c3a2020000888c242008840bfb000480f49b94050140
def zAP:W:=0xfffffff800000000000000000000000000002000000003f0000000000000000000000000000000000000000000000000000000000000000000000000
def zAQ:W:=0x478000c380000783c0000000000000000000000000000000000009800000000000000000000000000000000000000000000000000000000000000000000000
def zAR:W:=0xc0000000fc07e00000000007e01fe0000000007c1f00000000000240026001984000000088248010200020044084801000000422101000014000024002400088
def zAS:W:=0xff87f80ffffffff803c003f80000000000000000000379000001eff18c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zAT:W:=0x3878003c7800007c000001e1e0003e1ff000000003fffffffe638603826000041a4888b72882a628835284a4a0811454c0c2525023ff7bab6a4386830240a0
def zAU:W:=0xffb87fff0000000000000001e1fffc3e1fffff800003c0fe0001fc0003fa7e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zAV:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00379e79fe6638f8387e1e0045ac888f7a882a7399252a6a6a0819cd4e4825ad42bfb6b8ee2438f830741e0
def zAW:W:=0xffc78000ffffffff83c00007ffffffc1e000007ffffe20c1fc8183f983fd81ffd0c08000d9b4c87131102027d6d4c89882a4146b9cb80081d481036903ed01ea
def zAX:W:=0x3800070f0000000000000000001e1c00000f00000000400600000c00001818000801020000000000000000400808020001000800004000040000080000108800
def zAY:W:=0xc0000000fc07e00000000007fffffc000000007ffffc00c1f800024003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zAZ:W:=0x780000380000003c000001e000001e0000003e000000000800001800180600000800000800001000000200200008000200008000800000080000100010040
def zA0:W:=0x400000c000000780000006000003c00000007c0000000004000008000401800040000040000000111000020000000880040000840000000400000800040100
def zA1:W:=0xc0000000ffffe00000000007ffffe0000000007fff000001e00003c003e001f8400000009924803020002004c48480100080046210300001c0000340034000a8
def zA2:W:=0xfffffffffffffffffffffff9e1e1e03e1ff0ff800003fff80001ffffffe26600b73674ee224113c44222c381111110211e08b0000083fbea0001f49294a82200
def zA3:W:=0xfffffffffffffffffffffffffffffc00000000000003ffc00001fffffff80000b63664cc224113c44222c381101000000e0030000083fb800001f49294a80000
def zA4:W:=0x7ff000000000000000000000000000fff800000c01e00001c0000001e002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zA5:W:=0xffffffffffffffffffffffffffffffffffffff800003c0fe0001fffffffffe00bf3776ee224111c44220c1c1191912211f08b80000c3d0ee0001fc9294b8aa00
def zA6:W:=0x3fffffff00000000000000001fe01fffffffff800003c0fe0001fc00019ffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zA7:W:=0xc0000000fc07e00000000007e01fe0000000007c1f03fffffffe024002600198440040888824821020032204408480101000c4221013ef7b692a024002400088
def zA8:W:=0x7fffff00000007ffc00000000003ffffffff800001d83e07e07c0f8007fe002d7fdeaa668801871990d1e22b2913addd6caa18c44bd06e06c0fc8f8017eb40
def zA9:W:=0x478000c380000783c000061e0003c1e000007fe001182187e00009800581e00040800040800001111000220200008880240008840800000480000900050140
def zBa:W:=0xfffffffffffffffffffffffffe1fffffe00fffffffffff1f679ffffffe7f9fff6e7fe7ddeee7b797f77ffbf66a8ea7daad676f3eb75fff15679cfedffe579ddc
def zBb:W:=0x3800000f00001c00000003f800001c000000000000fc410600060c000c1800070801020100000400004400400808060021010800214000040004080008108804
def zBc:W:=0x7fffffc000000007ffffe20c1f800000003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zBd:W:=0x380f8000000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zBe:W:=0x7e01fe3fe000ffffc1f0086196718000002661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zBf:W:=0xff800000fffffff800000007fffffc0000000000000220c0000183f003f800009000000000000040000000011010000002001000008000800001000000a80000
def zBg:W:=0xff8007ff000000000000000000000000000000000002c00000019c000000000024244488000001000000810000000000080020000003c0000000b40000000000
def zBh:W:=0xfffffffffffffff8000000000000000000003f01fffe03fffc000000021220442241128442234280000000000400400000003f10292a409294000000
def zBi:W:=0xffffffffffffffffffffffffe01fe3fe000ffffc1f0086196719fffffe661f98627e2554ee67b196f739f9966086a15a8c466736961414116718f6def6461598
def zBj:W:=0x3847800fc3801c0783c003fe1e001fc1e000007fe0fc410604860c098c1d81e70841820140800401115400620a080688a1250808a54800040484080908158944
def zBk:W:=0x338e0986000000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zBl:W:=0xff800000fffffff8000000001fe01c0000000003e0fe20c0980183f001980067908000001110486000000001945048000280104108a000809001012001a80022
def zBm:W:=0xc07807f00000000000000007e01fe3fe000fff80000000000000100002661e000000000000000000000000000000000000000000000000000000000000000000
def zBn:W:=0xfff80007ffc000000000000000000000000018000000038f800000000012000022000084000040800000000004000000000010000000408280000000
def zBo:W:=0xfffffff0fffffffffffffc07ffffffffffffffffffffbef9fff9f3fff3ffffffd0da8910ffbee8f7bd9978b7f6f6e9dec6e6577fdebc1491f7d943efe3ef55fa
def zBp:W:=0xff8000000000000000000000001ffc0000000000000200c000018000007800009000000000000040000000011010000002001000008000800001000000a80000
def zBq:W:=0xff800000fffffff800000007fffffc000000007ffffe20ffffff83f003f801ffd08000009934c87020012005d4d4c8101280d46318b004fbf92b036003e800aa
def zBr:W:=0x7807f0fc000007fc3ffc07e00003fe000ffffc000086190718120e72061f8000480110c422a002b51918162082a15a80464316960404112718020c62061590
def zBs:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc41fffffe0c09cc1d99ff0841830140820401915508720a0a06c8b125c90ca54c047e2dbe080948159954
def zBt:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00118fffffe638f8387e1e0005a8800f7a880a7399150a6a6a0819cd4e4c25ad428147bafea438f830741e0
def zBu:W:=0xfff80007ffc00000000000000000007fe00000000000038f800001e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zBv:W:=0x3847870f000000000000000000000000000000000000400000000c00000000000000000000000000000000000000000000000000000000000000000000000000
def zBw:W:=0x7fffff00000007fffffff800000000000000000001df3e07fe7c0ffc000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zBx:W:=0xff8007ff0007fff8003ffff8001ffc00000fff800002e7de00019c707c781e00bf2576ee0041134042228341191912211b08b80000c3ebee0001bc1014b8aa00
def zBy:W:=0x7ff800fff8000000000007ffe003fffff0007fe0010021800063800387e1e000000000912080202000000484808010008000421020000180000300030000a0
def zBz:W:=0x3847870fc3861c0783fc03f8000000000000007ffffc4100049e0c09cc0001ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zBA:W:=0x7e01fe3fe000ffffc1f0000000000000002661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zBB:W:=0x3f800000fff81ff800000007ffe01c000000007fe0fe20c1980183b0039801e7908000009130c8602000000594d0c8100280104318a000819001032003a800a2
def zBC:W:=0x7ff800fff80007ffc0000000000000000000000001182187e0638f800000000012000022000084000040800000000004000000000010000000408280000000
def zBD:W:=0x3878000000000000000001e1e0003e1ff000000001002000006000038260000000000000000000000000000000000000000000000000000000000000000000
def zBE:W:=0x3bff9fffe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zBF:W:=0x387fff0ffffe1c07fffc03f800000000000000000001590000006f8fcc0000000012000022000084000040800000000004000000000010000000408280000000
def zBG:W:=0xc07807f0fc07e007fc3ffc07e01fe0000000007c1f0086016000124e726001984000000088248010200020044084801000000422101000014000024002400088
def zBH:W:=0xff8000000000000000000007ffffffffffffff80000200fe0001800003fffe00990112220000004000000041191912211308980000c000ee0001080000b8aa00
def zBI:W:=0xc00007f00007e000003ffc0000000000000000000000860000001040700000000000000000000000000000000000000000000000000000000000000000000000
def zBJ:W:=0x3800070fc3861c00003c03fe1e1e1c00000f007ffffc4106001e0c004c1819ff080103010002040080440850080a064021010904214400040014080048109814
def zBK:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc0006049e0c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zBL:W:=0xfc07e007fc3ffc000000000000000000000006000000024e700000000000000000000000000000000000000000000000000000000000000000000000
def zBM:W:=0x3847870f00000000000000061e1e1fc1e00f00000000000000000c00001d98000801020000000000000000400808020001000800004000040000080000108800
def zBN:W:=0x801800000000000000000000000000000000000000000000000000000000000000000000000000000000
def zBO:W:=0xfc07e007fc3ffc00000000000000007c1f0086196718024e7000019840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zBP:W:=0xfffffffffc07e007fc3ffc07fffffffffffffffc1f0086196719fe4e73ffff98f96d1732cc26a152b519b957799fb37b8b4e7f3696d404956719be4c62febf98
def zBQ:W:=0x3f87f80f03f81ff803c003f80000000000000000000379e698e7edb18c000000263664cc224113844222c380000000001c00a0000003fb6a0822f49294000000
def zBR:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00000000480638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zBS:W:=0xc3861c0783fc03f8000000000000007ffffc4106049e0009cc0001ff004081014082040191540832020204c8a025010ca50c00000494000948051154
def zBT:W:=0xfffffffffff80007ffc00007ffffffffffffffffe001182187e1ff8f83ffffe0b97f9e22f7a881e73990d1e7bfb993bdcfec3a5ad4e8108586c1ff8f83bfebe0
def zBU:W:=0x1e1e0003e1ff00000000000218360000003826000000808009528802228801004a4a0811440c002525020000182400304030240a0
def zBV:W:=0x1fe000000fff801f0000186018000000601e184000011008062010840928104006204200024524021404106118004060401418
def zBW:W:=0x61e0003c1e000007fe000000004800000000581e00040800040800001111000220200008880240008840800000480000900050140
def zBX:W:=0x3847870fc0060007803c00061e1e1fc1e00f007c1f00400604180c08401d9998084103004002000091100852080a024881040904844400040410080840149910
def zBY:W:=0xff800000fffffff800000007fffffc000000007ffffe00c0000183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zBZ:W:=0xfffffffffffffffffffffff9e1e1e000000000000003ffc1f801ffffffe00000f6b664ccbb75dbf46222e385d4d4c8100e80346318b3fb81d001f7f297e800aa
def zB0:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f00bf19fffe124e72661f9840480110cc26a212b51b3a166086a15a8046473696142f116f3a024c62461598
def zB1:W:=0xfffffffffffffffffffffffffffffc000000007ffffe20c1f801fffffff801fff2b62444bb75d9f46220e185d4d4c8100e80346318b01081d001f7f297e800aa
def zB2:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc400600000c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zB3:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc7f07fffe0c09cc1d99ff084183014082060191570a720a0a06c8a125490ca54c2f142dbe080948159954
def zB4:W:=0x220c078000000000000000000000000000000000000000000000000000000000000000000000000000000
def zB5:W:=0x7ffffffffffffff80000000fffffe000003fffe00990112220000004000010041191912211308d80000c004fe292b080000b8aa00
def zB6:W:=0x3be00000000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zB7:W:=0x47870fc380000783fc03fe1e0003c1e00f007fe0004106049e0c09cc0599e00841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zB8:W:=0xffffffffffffffffffffffffffffffffffffff800003fffffffffffffffffe00bf3776ee224113c44223c3c1191912211f08f80000c3fffe292bfc9294b8aa00
def zB9:W:=0xffc7870fffffffff83fc03ffffffffc1e00f007ffffc4106049f8ff9cffd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zCa:W:=0x780000fc000007fc000007e00003fe0000007c000000000000020e0206018000480000c4208002311010062080811880440212940000010600020c02060180
def zCb:W:=0x7fffff0000000000000000000003ffffffff800001df3e07fe7c000007fe002d2556aa0000030000038340090912211908e8000043ef7e292abc000010aa00
def zCc:W:=0x3f87f80f03f81ff803c003f81e001c01e0000003e0ff79060087edb18c1980672e37e6cd22c117854266c3e00a0806802d212808214bfb040084fc939c118844
def zCd:W:=0xffffffffffffffffffffffffffffffc1e00f007fffffffc7fc9ffffffffd99fffef7e7cdfbf7dff5f376ebf7dedeced8afa53d6fbdfffb85d495fffbdffd99fe
def zCe:W:=0xff8000000000000000000007fffffc0000000000000220c1f801800003f800009000000000000040000000011010000002001000008000800001000000a80000
def zCf:W:=0x19e39e7f80000000000000000000000000000000100000000000000004000000004102108000000000000
def zCg:W:=0xfffffffffc07e00000000007fffffffffffffffc1f03c0ff6001fe4003ffff98fd2556aa882481502000a145599d92311b08bc2210d3c0ef4001be4002f8aa88
def zCh:W:=0x387fffffc3861c07fffffff800000000000000000001df0000007c0ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zCi:W:=0xffb87800fffffff87c000007fffffc3e1ff0007fffff38e1fb61e3f603fa61ffd09a0800bf3cc8f628807085f4f4c91446c0167358b01081d24143e683ea40aa
def zCj:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0000196718124e72661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zCk:W:=0xff800000fffffff800000007fffffc000000007fffffffc1f80183f003f801ffd48040889934ca7020022205d4d4c8100280146318b3eb81d001036003e800aa
def zCl:W:=0x3f87f80f03f8000003c000001fe01c01fff00003e00358e680e1ed818199e060bd37deaa338801e50880c1e19f3912a55fa8b84840ebd0ee80c1fd8381b9ea60
def zCm:W:=0xc7b878f00000000000000001e1e1e03e1ff0ff800003bef9fb61f00003e26600b52454aa0000034000038301111110211a08f0000083effa292bb40000a82200
def zCn:W:=0xc7b878f03c79e3f87c03fc000000000000000000000000000001f3f63000000022362444224111844220c180000000000c002000000010000000f49294000000
def zCo:W:=0x7ff80003f8000003c00007ffe003fffff00003e001182080e061818387e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zCp:W:=0x7ff8000000000000000007ffe003fffff0007fe001002187e060000387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zCq:W:=0x7ffffffffffffff800003c0fe0000000003fffe009d0152aa0000004000000041191912211308980000c3c0ee0001080000b8aa00
def zCr:W:=0x3847870f00000000000000061e1e1fc1e00f000000004106049e0c00001d98000801020000000000000000400808020001000800004000040000080000108800
def zCs:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe003ff2187e0638f8387e1e0045ac888f7a882a7399252a6a6a0819cc4e4025ad42bfb0186c0438f830741e0
def zCt:W:=0xffffffffffffffffffffffffe00003fe0000007c0003ff010701fffffe060180267e64cce66193867332d386208081188c4422129403fb010600f69e96060180
def zCu:W:=0xffffffffffffffffffffffffffe003fffff0007fe001182187e1ffffff87e1e0227eac44f7e991a77bb0d1a6a6a0819ccce4225ad428100186c0f79f970741e0
def zCv:W:=0xde781e000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zCw:W:=0x7ff800c3800007ffc000061e0003fffff0007fe001182007e0600f8007e1e0005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zCx:W:=0x1df3f67fe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zCy:W:=0x4800000000000000000000000000000000000000000000000000000000000000000000000000000
def zCz:W:=0xf87f87ffff87fc07fffffffffe1fffffe00ffffffffc000000001e4ffe7f9fff48498311cca6a413b55c38766a8ea7daa1670f3eb75c000546940a4d6a579ddc
def zCA:W:=0x3ffff80ffff80007ffc00007ffe01ffffff0007fe00358e787e1ef8f839fe1e0bd7fdeaaf7a881e73990d1e7bfb993bddfecba5ad4ebd0ef86c1ff8f83bfebe0
def zCB:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe000180187e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zCC:W:=0x47800000000000000000061e0003c1e00000000000000000000000000580000000000000000000000000000000000000000000000000000000000000000000
def zCD:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe003d8ff87e0638f8387e1e0045ac888f7a880a7399050a6a6a0819cd4e4825ad42bd06b86c0438f830741e0
def zCE:W:=0xc78000000001e3f8000000000001e00000000000000220c07801807000600000d080000008144850000020015054480002001421089000805001006000e8000a
def zCF:W:=0xffffffff00061c00003c03ffffffffffffffff801fffc1fe001ffc004ffffe1fbd2557ab0002054080448951191b16613b09b90421c7c0ee0015bc0048b8ba14
def zCG:W:=0x7ff800ffffe007fffffc07ffe003fffff0007fff011e21e7f863cff387e1f8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zCH:W:=0xc78000000000000000000001e1e1e00000000000000200c00001800003e000009000000000000040000000011010000002001000008000800001000000a80000
def zCI:W:=0xffffffff0000000000000007ffffffffffffffffe003c0ff87e1fc0003ffffe0bd6ddeaad5a8816339909167bfb993bddbecba5ad4ebc0ef86c1bf0d03bfebe0
def zCJ:W:=0xfffffffffffffff800000007fffffffffffffffffffe20c1f801fff003fffffff9a516229934c9702000a145ddddda310b883c6318f00085d001bf6003f8aaaa
def zCK:W:=0x7fffffc000000007ffffc00000000000003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zCL:W:=0x3807f80f03f81c0003c003f81fe01c01fff00003e0fd592680e66d818d99e06708138a01338804a508c440e08e28068465a108486168100480c449838911c864
def zCM:W:=0x2200000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zCN:W:=0xc00007f00007e000003ffc00001fe000000fff801f0000000000104070601e184000011008062010840828104006204200020524021400004010004060401418
def zCO:W:=0xff8000000007fff800000007fffffc00000000001ffe20c07801807003f8001fd080000008144850000020015054480002001421089000805001006000e8000a
def zCP:W:=0x3f87f80003f81ff803c000001fe01c01fff00003e0ff38e098e1e1b18199e06790928800339848e5088040a19670488446a0104948a8108090c141a381a94062
def zCQ:W:=0xfffffff800000000000000000000007ffffc0000000003f0000001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zCR:W:=0xfffffffffffffffffffffff8000000000000007c1f03ff016719fffffc000198667e65dcee67b396f73bfb966086a15a8c4667369617ff116718f6def6461598
def zCS:W:=0xfffffffffffffff800000007ffffffffffffffffffffc0fe0001fff003fffffffda556aa9934c9702000a145ddddda311b88bc6318f3c0efd001bf6003f8aaaa
def zCT:W:=0xffffffff3c7800007c000007ffffffffffffff800003d8ff8361ff8603fffe00bd3f5eaab72881e62880d1c5bdb993355fc8ba5250e3d0ef8241ff8683baeaa0
def zCU:W:=0x3f87800f03f81ff803c003f81fe01c01e0000003e0fe61c698878db18d9980679881820111904c61004400619e584e8023a1184929e800849085092109b98866
def zCV:W:=0xfffffffffffffff800000000000000000003ff00000003fffc000000061260cc224112844222428000000000040000000003fb000000409294000000
def zCW:W:=0xfff807f0fffffffffc3ffc07fffffffe000ffffffffc8619671993fe73fe1fffd0c80110dd36e872b5193817f4d6e95a82c657779eb40491f719036c63ee15ba
def zCX:W:=0xff800000fffffff800000001e1e1e00000000000000220c1f80183f003e00000d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zCY:W:=0xc07807f0fc07e007fc3ffc06001e03c0000f007c1f0086000418124e700419980040010040020000911008120002004880040104840400000410000840041110
def zCZ:W:=0xffffffffc3861c0783fc03fffffffffffffffffffffc00000001fc09cfffffffb965972340820541915489731b1b16e9ab2d390ca5cc00840495bc0948bdbb54
def zC0:W:=0x7ff80000000007ffc00000000003fffff000000001182187e0600f8007e000005a880066880087199050a22220018cc4640218c408100006c0408f80074140
def zC1:W:=0x6049e0000000000000000000000000000000000000000000000000000000000000000000000000000
def zC2:W:=0x3e07fe000000000000000000000000000000010000000000001000c0000000047a292a000000000000
def zC3:W:=0xfffffffffffffffffffffff800000000000000000003ff3e07fffffffc000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zC4:W:=0x2c0de000000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zC5:W:=0xffffffff0000000000000007ffffffffffffff80000200c00001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zC6:W:=0xffffffff0000000000000007ffffffffffffff800003dffe07fffc0003fffe00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zC7:W:=0xc07807f0fffffffffffffff800000000000000000000bf00000013fffc000000021220442241128442224280000000000400000000003b000000409294000000
def zC8:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00000018000638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zC9:W:=0x7fffffc000000007ffffc00fffffe000003f801ffd08000009934c87020012005d4d4c8101280d46318b004fbf92b036003e800aa
def zDa:W:=0xffffffff000000000000000000000000000000000003c0fe0001fc0000000000242444880000010000008100000000001800a0000003c06a0000b40000000000
def zDb:W:=0x7fffff0000000000000000000003ffffffff800000000000007c000007fe002925162200000100000081400909122109082800004000040000bc000010aa00
def zDc:W:=0x780000fc000007fc000007e00003fe0000007c0001182187e0020e0206018000480000c4208002311010062080811880440212940000010600020c02060180
def zDd:W:=0x861807180000000000000000000000000000000100000000000000004000000004102108000000000000
def zDe:W:=0xfffffffffffffff800000007fffffffffffffffffffffffffffffff003fffffffda556aa9934cb702003a345ddddda311b88fc6318f3effff92bbf6003f8aaaa
def zDf:W:=0xff8000000000000000000007fffffc00000000000003c0fe0001800003f8000094004088000000400000000110100000120090000083c0ea0001000000a80000
def zDg:W:=0xffffff0ffffffffffffc03ffffffffffffff007fffff79e7ffffefffcffff9ffd8db8b01ffbeccf7b9d478f7fefecfdce7e51f7ffdfc1085d6d54befcbffd9fe
def zDh:W:=0xffffffff0000000000000001e1e1e03e1ff0ff800003c0f80001fc0003e26600b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zDi:W:=0xc78000003c79e3f800000001e1e1e000000000000003bef9fb6183f003e00000d48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def zDj:W:=0x7ff800fff80007ffc00001e1e0003e1ff00000000118218360638f83826000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zDk:W:=0x3800070f00061c00003c03f8001e1c00000f00001ffee7de781e0c004c18181f0c0143890002060080470a50080a06403101c9042147ef7e293e080048109814
def zDl:W:=0x3800070f00061c00003c03f8001e1c00000f00001ffc4106049e0c004c18181f080103010002040080440850080a064021010904214400040014080048109814
def zDm:W:=0xffffffff0000000000000007ffffffffffffff80000040060001fc0003fffe00b92516220000014000008141191912210b08380000c000840001bc0000b8aa00
def zDn:W:=0xfff8000000000007ffe000000000007fe001182187e00380038001e000000000912080202000000484808010008000421020000180000300030000a0
def zDo:W:=0xff8000000007fff80000000000000000000000000002200000018070000000000000000000000000000000000000000000000000000000000000000000000000
def zDp:W:=0xc7800000fff9e3f800000007ffe1e0000000007fe00220c1f80183f003e001e0d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zDq:W:=0xfffffffffff8000000000007ffffffffffffffffe003c0ff8001ff8003ffffe0bd2556aa91208160200081459d9992311b88b84210e3c0ef8001bf0003b8aaa0
def zDr:W:=0x3807800f03801c0003c003f81e001c01e0000003e0ff79e698e60c018c1980670c01c28900800601004602600a08068031218808214beb6e08a6080108118844
def zDs:W:=0xff8007ff0000000000000000001ffc00000fff800003c0fe00019c0000781e00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zDt:W:=0xf87ffffffffffc07fffffffffffffffffffffffffffddf3fe7fe7fcfffffffff485b8b11ffaea4b7bddd78f6eeaea7dee5e74f7ef77c1415e7dc4bcfeb57ddfc
def zDu:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc410600860c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zDv:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe003bef9ffe0638f8387e1e0045ac888f7a882a7399352a6a6a0819cd4e4c25ad42bff7bafea438f830741e0
def zDw:W:=0xfffffffffff80007ffc00007ffffffffffffffffe00000000001ff8f83ffffe0b97f9e22f7a881e73990d1e7bfb993bdcfec3a5ad4e8108586c1ff8f83bfebe0
def zDx:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007fffff79e69cfe0c09cc1d99ff0c41c3894082060191560a720a0a06c8b125890ca54feb6e0cb6080948159954
def zDy:W:=0x410600860000000000000000000000000000000000000000000000000000000000000000000000000000
def zDz:W:=0x7807f000000007fc3ffc00000003fe000fff800001df3e07fe100e70061e000448419844022202951b1a122002214a9046c3148607ef7a2f3a000c60061510
def zDA:W:=0xc00007f00007e000003ffc00001fe000000fff801f02e7de781e104070601e184400419808062210840b2a10400620421002c5240217ef7a693a004060401418
def zDB:W:=0xc7f87ff0fc07e007fc3ffc07e1ffe3fe1ffffffc1f0386f96719f24e73e67f98f56c55bacc26a152b519b9177197b17b9a4ef7369697c4fb6719b64c62ee3798
def zDC:W:=0xff800000fffffff800000000001ffc00000000001ffe20c0780183f00078001fd080000008144850000020015054480002001421089000805001006000e8000a
def zDD:W:=0x3c7800007c0000000000000000000000000018018360038600000000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zDE:W:=0x3f80000003f81ff8000000001fe01c0000000003e0fc0000000181b001980067908000001110486000000001945048000280104108a000809001012001a80022
def zDF:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0086fffffe124e72661f9840480110cc26a012b51938166086a15a9046c7369614047b6f3a024c62461598
def zDG:W:=0xfffe1c07fffc03f8000000000000007ffffc190187fe038fcc0001ff005a8901f7aa84a7b9d458b6a6a285dce4e5035ef52c100186d4438fcb0751f4
def zDH:W:=0xfffffffffffffff8000000000000007ffffc3f00049e03fffc0001ff0252a14562c31685d3764ab2020204c8a425010ca50c3b000494409bdc051154
def zDI:W:=0xc03800f00000000000000001e001e03e0000ff800000801800001000026206000000000000000000000000000000000000000000000000000000000000000000
def zDJ:W:=0x47870f0000000783fc03f800000000000000000000410000000c09cc0000000000000000000000000000000000000000000000000000000000000000000000
def zDK:W:=0x1e001e03e0000ff80000000196300000002620600400800108c24a012240930046084a11200424632121004116308024422420488
def zDL:W:=0xfffff800fff80007ffc00007fffffffffff0007fe00318e187e1e38f83ffe1e0905a8800f7a880e7399050a7b6b0819cc6e4125ad4a8108186c1438f83af41e0
def zDM:W:=0x2e700000000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zDN:W:=0x7807f000000007fc3ffc00000003fe000fff80000086196718100e70061e000048011044022002951918122002214a80464314860404102718000c60061510
def zDO:W:=0x861963000000000000000000000000000000000100000000000000004000000004102108000000000000
def zDP:W:=0x400700c0060007803c0006001e03c0000f007c1f004106049e0008400419980040010040020000911008120002004880040104840400000410000840041110
def zDQ:W:=0x3f87f80f03f81ff803c003f800000000000000000003ff000001edb18c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zDR:W:=0x3dffe07fe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zDS:W:=0xc07ff8f0fff9e007ffc3fc07ffe1e3fffff0ffffe0019e39e7e073cfb3e7e7e0405a8810ffaca0b73d9970a6e6a4a19ec4e6467ad6381411e7c843cfa34745e8
def zDT:W:=0xffffffffffffffffffffffffe01fe3fe000ffffc1f03ff000001fffffe661f98667e65dcee67b396f73afb966086a15a8c4627369617fb014610f6def6461598
def zDU:W:=0xfffffffffffffffffffffffe1e1e1fc1e00f007ffffffffffffffffffc1d99ff2e77e7cd62c31785d377cbf20a0a06c8bd25e90ca54fff7e2dbefc9bdc159954
def zDV:W:=0xfffffffffc07e007fc3ffc07fffffffffffffffc1f03c0fe0001fe4e73ffff98fd6d57bacc26a152b518b957799fb37b9b4ebf3696d7c0ef4611be4c62febf98
def zDW:W:=0x7807f000000007fc3ffc00000003fe000fff80000000000000100e70061e000048011044022002951818122002214a80460314860400000610000c60061510
def zDX:W:=0xfff807fffc07e007fc3ffc07e01ffffe000ffffc1f02c6df67199e4e727e1f98fd6d57bacc26a152b519b957799fb37b9b4eff3696d7c4ff6719be4c62febf98
def zDY:W:=0xff800000fc07e00000000007fffffc000000007c1f0200c16001824003f80198d000000088248050200020055094801002001422109000814001024002e80088
def zDZ:W:=0xfff807f0fffffffffc3ffc07fffffffe000ffffffffe20c1f80193fe73fe1fffd0c80110dd36e872b5183817f4d6e95a82c617779eb40081d611036c63ee15ba
def zD0:W:=0xff800000fffffff800000007fffffc000000007fffff79e7f8e783f003f801ffd48040889934ca7020022205d4d4c8101280946318b3ebebd823036003e800aa
def zD1:W:=0x7e01fe3fe000ffffc1f0000fffffe000002661f9840480110cc26a012b51938166086a15a9046c7369614047b6f3a024c62461598
def zD2:W:=0xfffffffffffffffffffffff800000000000000000003ff196719fffffc000000263664cc224113844223c380000000000c0060000003ff102108f49294000000
def zD3:W:=0xff800000fffffff800000007fffffc000000007ffffe20c0980183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zD4:W:=0x478000c380000783c000061e0003c1e000007fe003fffffffe0009800581e00440c0884080020111130222020000889024c008840bef7a2daa000900050140
def zD5:W:=0x4780000000000783c00000000003c1e00000000000000004800009800580000040800040800001111000220200008880240008840800000480000900050140
def zD6:W:=0x1182080e00000000000000000000000000000000000000000000000000000000000000000000000000000
def zD7:W:=0xfffffffffffffffffffffffffffffffffff0007fffffffe1ffe1ffffffffe1fff6feecccfffddbf77bb2f3a7f6f4c99ccee4367bdcbbfb81d6c1f7ff97ef41ea
def zD8:W:=0xe698e600000000000000000000000000000000000000000000100080000000006a0822000000000000
def zD9:W:=0xffc7870fffffffff83fc03ffffffffc1e00f007ffffe20c1f8018ff9cffd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zEa:W:=0x37900000000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zEb:W:=0x3f80000003f81ff8000000001fe01c0000000003e0ffffffffff81b0019800679480408811104a6000030201945048001280d04108a3effab92b012001a80022
def zEc:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe00000010700638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zEd:W:=0x478000c380000783c000061e0003c1e000007fe0004106049e0009800581e00040800040800001111000220200008880240008840800000480000900050140
def zEe:W:=0xfc07e007fc3ffc00000000000000007c1f003f01fffe024e7000019840480110cc26a212b51b3a166086a15a8046473696142f116f3a024c62461598
def zEf:W:=0x1df00000000000000000004004088000002000002020000000000000000000003eb000000000000000000
def zEg:W:=0x47870f0000000783fc03f8000003c1e00f00000001df3e07fe0c09cc0598000c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def zEh:W:=0x390098e6000000000000000000000000020000020200000000000000000000002b000822000000000000
def zEi:W:=0x1f0007fe000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zEj:W:=0x1592600e600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zEk:W:=0xf87f87fffc07e007fc3ffc07fe1fffffe00ffffc1f00c61f67181e4e727f9f9848490310cc26a012b5193856688ea35a81464f369654041567180a4c62569d98
def zEl:W:=0x7ffff0fff80007fffffc07ffe003ffffffffffe0019e3987f8738ff387ffe0005a8910f7aaa0a7bd9958b6a6a2a1dec4e6435ed62c1411a7d8438fe30755f0
def zEm:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001182080e0638f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zEn:W:=0xffffffff0000000000000007ffffffffffffff800003c6ff6719fc0003fffe00bd2556aa0000014000018141191912211b08f80000c3c4fe2109bc0000b8aa00
def zEo:W:=0x400700c0060007803c0006001e03c0000f007c1f00861967180008400419980040010040020000911108120002004880044104840404102518000840041110
def zEp:W:=0x7f87ff00000007fffffff8000003ffe00fff800000c71e079e1c0ffc079e000849831144822403955d18722a0a27caa1674b1ca74c0414279c080d68179d54
def zEq:W:=0x3847870fc380000783c000061e1e1fc1e00f007fe000400604800c09801d99e00841820040800001111000620a08028881240808844800040480080900158940
def zEr:W:=0xfffffffffc07e007fc3ffc07fffffffffffffffc1f03fffffffffe4e73ffff98fd6d57bacc26a352b51bbb57799fb37b9b4eff3696d7efff6f3bbe4c62febf98
def zEs:W:=0xffffffffffffffffffffffffe01fe3fe000ffffc1f03fffffffffffffe661f98667e65dcee67b396f73bfb966086a15a9c46e7369617ff7b6f3af6def6461598
def zEt:W:=0xff8007ff00061c00003c03f8001ffc00000fff801ffec1de001f9c004c781e1fbd2557ab0002054080448951191b16613b09b90421c7c0ee0015bc0048b8ba14
def zEu:W:=0xfff807f0fffffffffc3ffc07fffffffe000fffffffffffffffff93fe73fe1fffd4c84198dd36ea72b51b3a17f4d6e95a92c6d7779eb7effbff3b036c63ee15ba
def zEv:W:=0x1967180000000000000000000000000000000100000000000000004000000004102108000000000000
def zEw:W:=0x410000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zEx:W:=0xc00000000007e00000000000001fe000000000001f00000060000040006000184000000008040010000020004004000000000420001000004000004000400008
def zEy:W:=0x7ff80000000007ffc00000000003fffff000000001df3e07fe600f8007e000045ac88866880287199352a22220018cd464c218c40bff7a2fea408f80074140
def zEz:W:=0xc3861c0783fc03f8000000000000007ffffc3f01fffe0009cc0001ff004081014082060191570a32020204c8a025410ca50c2f102dbe000948051154
def zEA:W:=0x3f87f80f03801c0003c003f81fe01c01fff00003e0ff41e60087ec018d99e067bd25d6ab00800541004481611b1916a13b29b80821cbc0ee0085bc0108b9aa44
def zEB:W:=0x7ff800fff80007ffc00007e00003fe0000007c000118010700638f82060180005a0000e6208086311050862080811884440212940010010600428e82060180
def zEC:W:=0x7ffe00000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000000000
def zED:W:=0xfffffffffffffffffffffff80000000000000000000118000001fffffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zEE:W:=0x1180000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zEF:W:=0x387fffffc3861c0783fc03fe1e1e1ffffffffffffffdc13e049e7c09cc1fffff2d65d7ab40820501915489720b0b16e9b92da90ca54fc06e0494bc094815bb54
def zEG:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f03bef9ff78124e72661f9844484198cc26a212b51b3a166086a15a9046c7369617ef7b6f3a024c62461598
def zEH:W:=0xfff80007ffc00007ffe003fffff0007fe000182187e0038f8387e1e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zEI:W:=0xc03800f03c01e0007c03fc01e001e03e0000ff800003bef9fb60124632620600440840988c24a212240b32046084a1121042c6321213ef7b6b2a024422420488
def zEJ:W:=0x7ff800fff80007ffc0000000000000000000000003fffffffe638f80000000041240882200028400034280000000001400c0000003ff7a292a408280000000
def zEK:W:=0x3fffef8fe000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zEL:W:=0xff8000000007fff800000000001ffc00000000001ffe20c1f80180700078001fd080000008144850000020015054480002001421089000805001006000e8000a
def zEM:W:=0xff800000fffffff800000007ffe000000000007fe0022001800183f0038001e000000000912080202000000484808010008000421020000180000300030000a0
def zEN:W:=0x387fff0ffffe1c07fffc03fffffe1fffffff007ffffc4106049e6f8fcf9ff9ff085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def zEO:W:=0xfffffff800000000000000000000007ffffe20c1f80003f0000001ff408000009934c83020002004c4c4c8100080046318300001d0000360034000aa
def zEP:W:=0xfffffffffffffffffffffffe001e03c0000f007c1f03ff000419fffffc041998267665cc62431384d332cb92000200488c0421048407fb000410f49ad4041110
def zEQ:W:=0x400700c0060007803c00061e1e1fc1e00f007ffffc0006049e0008401d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zER:W:=0xffffffff0000000000000007ffffffffffffff80000340e60001fc0003fffe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zES:W:=0xc07807f0000000000000000000000000000000000000800000001000000000000000000000000000000000000000000000000000000000000000000000000000
def zET:W:=0xffffffff3c79e3f87c03fc0000000000000000000003fe000001fff630000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zEU:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe001df3f87fe638f8387e1e0045ac888f7a882a7399352a6a6a0819cd4e4c25ad42bff7bafea438f830741e0
def zEV:W:=0x2001f8000000000000000000000000000000000000000000000000000000000000000000000000000000
def zEW:W:=0xc07ffff0fc07e007fffffc07e01fe3fffffffffc1f019e3967f8724ff267ff98405a8910eeaea097bd9978b662a6a1dec466473ed61c141167d842cfe24755d8
def zEX:W:=0x7ff800fff80007ffc00007ffe003fffff0007fe0019e39e7f8638f8387e1e0005a8800f7a880a7399150a6a6a0819cc4e4425ad4281411a7c8438f830741e0
def zEY:W:=0xfffff800ffffffffffc00007fffffffffff0007fffffffffffffe3ff83ffe1ffd4dac888ffbccaf7399372a7f6f4c99cd6e4d67bdcbbfffbffeb43ef83ef41ea
def zEZ:W:=0xffffffff3c01e0007c03fc07ffffffffffffff800003c6ff6301fe4633fffe00fd2d56ba8c24a1522409b145799db3331b4afe3212d3c4ff6309be4422faae88
def zE0:W:=0x7f80f000000000000000000000001fff000000001402600006c000001e0002d2556aa0000010000008140090912211908a8000043c06e0000bc000010aa00
def zE1:W:=0xffffffff0000000000000007ffffffffffffffffffffc0fe049ffc0003ffffffbd65d7ab40820541915489731b1b16e9bb2db90ca5cfc0ee0495bc0948bdbb54
def zE2:W:=0x160000000000000000000000000000000000000000000000000000000000000000000000000000000
def zE3:W:=0xc7800000fc7fe3f800000007e1ffe0000000007c1f0220c1f80183f003e00198d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zE4:W:=0x7f80003f8000003c0000000000000000000000001180000006181800000000012000022000084000040800000000004000000000010000000408280000000
def zE5:W:=0xff800000fffffff800000007fffffc000000007fffffe0fff80183f003f801ffd48040889934c87020002005d4d4c8101280946318b3c0ebd001036003e800aa
def zE6:W:=0x220c098000000000000000000000000000000000000000000000000000000000000000000000000000000
def zE7:W:=0x1182183600000000000000000000000000000000000000000000000000000000000000000000000000000
def zE8:W:=0x400600000000000000000000000000000000000000000000000000000000000000000000000000000000
def zE9:W:=0x3847870fc3861c0783fc03ffffffffc1e00f007ffffc41c7fc9e0c09cffd99ffd8c18301d9b6cc71b1542877dedeced8a3a51d6fbdfc0085d4950b694bfd99fe
def zFa:W:=0xff800000fffffff800000007fffffc000000007ffffc00c1f80183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zFb:W:=0xc7b878f03c79e3f87c03fc0000000000000000000003ff000001f3f630000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zFc:W:=0x7c1f000001671800000000019840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zFd:W:=0x3847870f00061c00003c03fe1e1e1fc1e00f00001ffc4106001e0c004c1d981f080103010002040080440850080a064021010904214400040014080048109814
def zFe:W:=0xfffffffffffffffffffffffe1e1e1fc1e00f007fffffff000001fffffc1d99ff2e77e7cd62c31785d376cbf20a0a06c8ad25290ca54ffb040494fc9bdc159954
def zFf:W:=0xc00007f0fc07e000003ffc07e01fe000000ffffc1f0086196018124072601f98400001108826a010a40928144086a05200024526121404116118024062401498
def zFg:W:=0xffffffffc3861c0783fc03ffffffffffffffffffffffc0fe0001fc09cfffffffbd65d7ab40820541915489731b1b16e9bb2db90ca5cfc0ee0495bc0948bdbb54
def zFh:W:=0x47870f0000000783fc03f8000003c1e00f00000000000000000c09cc0598000841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zFi:W:=0xfffffffffffffffffffffffffffffc000000007ffffffffffffffffffff801fff6b664ccbb75dbf46223e385d4d4c8101e80f46318b3fffbf92bf7f297e800aa
def zFj:W:=0x7fffff0000000783fc03f8000003ffffffff800001c13e049e7c09cc07fe002d65d7ab40820501915489720b0b16e9b92da90ca54fc06e0494bc094815bb54
def zFk:W:=0x3d8ff87e000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zFl:W:=0xc07807f00000000000000007e01fe3fe000fff80000086196718100002661e000000000000000000000100000000000000004000000004102108000000000000
def zFm:W:=0x3e01fb60000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zFn:W:=0xf87f87ffff87fc07fffffffffe1fffffe00ffffffffc861967181e4ffe7f9fff48498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def zFo:W:=0x387fff0ffffe1c07fffc03fffffe1fffffff007ffffd182187e06f8fcf9ff9ff085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def zFp:W:=0x860000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zFq:W:=0xc7b878f03c79e3f87c03fc0000000000000000000003bef9fb61f3f630000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zFr:W:=0xffffffff0000000000000007fffffffffffffffc1f03c0ff6719fc0003ffff98fd6d57bacc26a152b519b957799fb37b9b4eff3696d7c4ff6719be4c62febf98
def zFs:W:=0xffffffff03f8000003c00007ffffffffffffff83e003d8fe80e1fd8183fffe60bd37deaa338801e50880c1e19f3912a55fa8b84840ebd0ee80c1fd8381b9ea60
def zFt:W:=0xffffffffffffffffffffffffffe003fffff0007fe003ff000001ffffff87e1e0267eecccf7e993a77bb2d3a6a6a0819ccce4225ad42bfb0186c0f79f970741e0
def zFu:W:=0xff87ffff00000000000000001ffffc01ffffff800003c0fe0001fc0001f9fe00bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zFv:W:=0xff800000c3861c0000000007fffffc000000007ffffe00c00001800003f801ff9000000000000040000000011010000002001000008000800001000000a80000
def zFw:W:=0xff800000fffffff800000007fffffc000000007ffffc0001800183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zFx:W:=0xffffffffc3861c0783fc03fffffffffffffffffffffc4106049ffc09cfffffffb965972340820541915489731b1b16e9ab2d390ca5cc00840495bc0948bdbb54
def zFy:W:=0xfffffffffffffffffffffff800000000000000000003fff9fb61fffffc000000263664cc224113844223c380000000001c00e0000003ff7a292af49294000000
def zFz:W:=0xffffffff0000000000000007ffffffffffffff800003fefffb61fc0003fffe00bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zFA:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f0000000418124e72661f9840480110cc26a012b51838166086a15a80460736961400014610024c62461598
def zFB:W:=0xff800000fffffff800000007fffffc000000007fffffbef9fb6183f003f801ffd48040889934ca7020032205d4d4c8101280d46318b3effbf92b036003e800aa
def zFC:W:=0x387f87ffc3861c07fffffffe1e1e1fffe00ffffffffcc71e079e1c0ffc1f9fff0849831144822403955d18722a0a27caa1674b1ca74c0414279c080d68179d54
def zFD:W:=0xc7b878f00000000000000001e1e1e03e1ff0ff800003c0fe0001f00003e26600b52454aa0000014000008101111110211a08b0000083c0ea0001b40000a82200
def zFE:W:=0x7fffffffffff0007ffffc00e1ffe0000003ffe1ffd0c88800ddbcc87339903027f6f4c99cc2e4167bdcb80081d6c1036d03ef41ea
def zFF:W:=0x3847870fc3861c0783fc03f800000000000000000003ff0000000c09cc00000004004088000002000002020000000000000000000003eb000000000000000000
def zFG:W:=0x3807800f03801c0003c003f81e001c01e0000003e0fc000000000c018c1980670801820100800401004400600a08068021210808214800040084080108118844
def zFH:W:=0xfffffffffffffff8000000000000000000000000000003fffc0000000212204422411084422040800000000004000000000010000000409294000000
def zFI:W:=0x7fffff00000007fffffff800000000000000000000000000007c0ffc00000022362444224111844220c180000000000c002000000010000000f49294000000
def zFJ:W:=0xc7b878f00000000000000001e1e1e03e1ff0ff80000000000001f00003e26600b12414220000014000008101111110210a083000008000800001b40000a82200
def zFK:W:=0xff8000000007fff800000000001ffc00000000001ffc0000000180700078001fd080000008144850000020015054480002001421089000805001006000e8000a
def zFL:W:=0xfffffffffffffffffffffffffffe1fffffff007fffffff2787ffffffff9ff9ff2e7fefcdf7eb97a7fbf6dbf6aeaa87dcede52b5ef56ffb0586d4ff9fdf17d9f4
def zFM:W:=0xffc7870fffffffff83fc03ffffffffc1e00f007fffffffffffff8ff9cffd99ffdcc1c389d9b6ce71b1572a77dedeced8b3a5dd6fbdffeffffdbf0b694bfd99fe
def zFN:W:=0x3800070f00061c00003c03f8001e1c00000f00001ffffffffffe0c004c18181f0c0143890002060080470a50080a06403101c9042147ef7e293e080048109814
def zFO:W:=0x7ff8000000000000000007ffe003fffff000000003c0fe000060000387e00004004088000000000000000000000000100080000003c06a0000000000000000
def zFP:W:=0xff80070ffffffff8003c03fffffffc00000f007ffffe61c7f81f8ff04ff819ffd88103019936cc70a0442855dcdece5023811d6739f40085d0150b604bf898be
def zFQ:W:=0x1002000000000000000000000000000000000000000000000000000000000000000000000000000000000
def zFR:W:=0x3f9fe98e600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zFS:W:=0xc03800f03c01e0007c03fc01e001e03e0000ff80000000000000124632620600400800108c24a012240830046084a11200420632121000014200024422420488
def zFT:W:=0x400700c0060007803c0007e01fe3fe000ffffc1f0000196718000842661f9840480110cc26a012b51938166086a15a80464736961404116718024c62461598
def zFU:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc000004180c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zFV:W:=0x780000fc000007fc000007e00003fe0000007c000086196718020e0206018000480000c4208002311110062080811880444212940004112708020c02060180
def zFW:W:=0xc7800000fffffff800000001e1e1e0000000007ffffe20c1f80183f003e001ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zFX:W:=0xfc000007fc000000000000000000007c000000010700020e0000018000480000c4208002311010062080811880440212940000010600020c02060180
def zFY:W:=0xfff8000000000007ffe000000000007fe003fffffffe0380038001e0040040889120822020030204848080101080c0421023ef7ba92a0300030000a0
def zFZ:W:=0xc04007f0c007e007803ffc06001fe3c0000ffffc1f0086186418104870641f984040011048062010951928124006204a80064524861404106518004860441518
def zF0:W:=0xffffffffffffffffffffffffffffffffffffff80000000000001fffffffffe00bb373666224111c44220c1c1191912210f08380000c010840001fc9294b8aa00
def zF1:W:=0xffb878f0fffffff87c03fc0000000000000000000003be000001f3f630000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zF2:W:=0x7f80f0000000003c003f800000000000000000001590000006c018c000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zF3:W:=0xf84787ffc387fc0783fffffe1e1fffc1e00ffffffffcc71e649e1c49fc7d9fff4841831148862411955d28724a0e26caa1274d2ca75c0414659c084968559d5c
def zF4:W:=0x3ffe698e600000000000004004088000002000002020000000000100080000003eb6a0822000000000000
def zF5:W:=0xfffffffffffe1c07fffc03ffffffffffffffffffffffd9ff87ffff8fcfffffffbd7fdfabf7aa85e7b9d4d9f7bfbb97fdffedbb5ef5efd0ef86d5ff8fcbbffbf4
def zF6:W:=0x3878003c7800007c000001e1e0003e1ff000000001182187e0638603826000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zF7:W:=0xfff80007ffc00000000000000000007fe0003f01fffe038f800001e0005a8800f7a882a7399352a6a6a0819cc4e4425ad4283f11afea438f830741e0
def zF8:W:=0xff800000c387fff8000000061e1ffc000000007ffffe20c078018070007801ffd080000008144850000020015054480002001421089000805001006000e8000a
def zF9:W:=0x1fe01c0000000003e0fc00c09800000001980067908000001110486000000001945048000280104108a000809001012001a80022
def zGa:W:=0x7ff8000000000000000007ffe003fffff0000000000000000060000387e0000000000000000000000000000000000000000000000000000000000000000000
def zGb:W:=0x4180000000000000000000000000000000000000000000000000000000000000000000000000000
def zGc:W:=0x4106001e0000000000000000000000000000000000000000000000000000000000000000000000000000
def zGd:W:=0xc07807f0fc07e007fc3ffc000000000000000000000000000000124e700000000000000000000000000000000000000000000000000000000000000000000000
def zGe:W:=0x3fffe000000000000000004004088000002000002020000000000100080000003eb6a0000000000000000
def zGf:W:=0x107000000000000000000000000000000000000000000000000000000000000000000000000000000
def zGg:W:=0x3ffff800fff81fffffc00007ffe01ffffff0007fe0ff38e19fe1e3bf839fe1e790da8800f7b8c8e7399050a7b6f0c99cc6e4125bdca8108196c143af83af41e2
def zGh:W:=0xfffffffffffffffffffffff8001fe000000fff801f03ff186019fffffc601e18663665dc2a473394c62beb90400620420c0265240217ff106118f4d2f4401418
def zGi:W:=0x780000fc000007fc000007ffe003fffff0007fe000002187e0020e0387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zGj:W:=0xc07ffff0ffffe007fffffc07e01fe3fe000ffffc1f019e19671873cff2661f98405a0110ee26a096b51978966086a15a8446473696141411671842cee2461598
def zGk:W:=0x7ffe003fffff0007fe001182187e000000387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zGl:W:=0x7fff0ffff80007fffc03ffffe003ffffff007fe001592787fe6f8fcf87f9e0085b8b01f7aa84a7b9d458f6aeaa87dce5e50b5ef56c100586d44b8fcb17d9f4
def zGm:W:=0xffffffff0000000000000007ffffffffffffff800003c0fffffffc0003fffe00bd2556aa0000014000018141191912211b08f80000c3c4fe292bbc0000b8aa00
def zGn:W:=0xfffffffffffffffffffffff9e001e03e0000ff800003ff196301fffffe620600663e64dcae65b396662bf3846084a1120c4266321213ff116308f6d6b6420488
def zGo:W:=0xfffff800ffffffffffc00007fffffffffff0007ffffc00000001e3ff83ffe1ffd0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zGp:W:=0x100049e0000000000000000000000000000000000000000000000000000000000000000000000000000
def zGq:W:=0xc0060007803c0000000000000000007c1f00000004180008400001980040010040020000911008120002004880040104840400000410000840041110
def zGr:W:=0x387fff0ffffe1c07fffc03fffffe1fffffff007ffffffffffffe6f8fcf9ff9ff0c5bcb89f7aa86a7b9d75af6aeaa87dcf5e5cb5ef56fff7faffe4b8fcb17d9f4
def zGs:W:=0xfffffffffffffffffffffff800000000000000000003ff01fffffffffc000000263664cc224113844223c380000000000c0060000003ff10292af49294000000
def zGt:W:=0x2700781e000000000000000000000000020000030200000000000000400000002f10292a000000000000
def zGu:W:=0x3fffff000000000002007e000000007e0000048880044880003199010222220018cc0640218c408000006c0000d00074140
def zGv:W:=0x3f87f80f03f81ff803c003f81fe00001fff00003e003792080e1edb18d81e0602636eccc33c913a54aa2c3a0862000844ca02048402bfb0080c0f59395014060
def zGw:W:=0xf87f87ffff87fc07fffffffffe1fffffe00ffffffffc4106049e1e4ffe7f9fff48498311cca6a413b55c38766a8ea7daa1670f3eb75c000546940a4d6a579ddc
def zGx:W:=0x3f87f80f00000000000000001fe01c01fff000000003c0fe0001ec000199e000bd2556aa0000014000008141191912211b08b80000c3c0ee0001bc0000b8aa00
def zGy:W:=0x3800003c0000007c000001e000003e000000000000000103000206020200000008000084208002200010042080811000400212100000010200020402020080
def zGz:W:=0x7fe1fffffe00ffffffffc001f679e0000027f9fff48498311cca6a413b55d38766a8ea7daa1674f3eb75c0415679c0a4d6a579ddc
def zGA:W:=0x7f80003f8000003c000001fe00001fff00003e0000000000061818181e06000128800338800a5088040a08620008444a000484028100080c0418381014060
def zGB:W:=0x478000fff8000783c00007ffe003c1e000007fe000000184800389838581e000408000d1a08021311000268680809880a4004a9428000184800309030501e0
def zGC:W:=0xc07807f0fc07e007fc3ffc07e01fe3fe000ffffc1f03c6ff6718124e72661f9844484198cc26a012b51938166086a15a9046c7369617c47b6718024c62461598
def zGD:W:=0x3878003c7800007c000001e1e0003e1ff00000000000000000638603826000001a0800b72880a628805084a4a0811444c002525020100182404386830240a0
def zGE:W:=0xc07807f00007e000003ffc07e01fe3fe000fff801f0086186018104072661e184000011008062010840928104006204200024524021404106118004060401418
def zGF:W:=0x400700c0060007803c0006001e03c0000f007c1f00000000000008400419980040010040020000911008120002004880040104840400000410000840041110
def zGG:W:=0x7ffe003fffff0007fe0000000000000000387e1e000488800d5a8802339901026a6a0819cc0e4025ad428000186c0030d030741e0
def zGH:W:=0x478000c380000783c000061e0003c1e000007fe000000000000009800581e00040800040800001111000220200008880240008840800000480000900050140
def zGI:W:=0xff8007ff0007fff8003ffff800000000000000000000000000019c707c0000002224244400411100422081000000000008002000000000000000b41014000000
def zGJ:W:=0x1e1e1e00000000000000000c1f800000003e00000d08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zGK:W:=0x2a6d87800000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zGL:W:=0x1e1e1e03e1ff0ff80000000f80000000003e266009100102200000040000000011111102112089000008000ea0001000000a82200
def zGM:W:=0xff8000000007fff800000000001ffc00000000001fffffffffff80700078001fd480408808144a5000032201505448001200d4210893effa792b006000e8000a
def zGN:W:=0x3847870fc3861c00000000061e1e1fc1e00f007ffffc400600000c00001d99ff0801020000000000000000400808020001000800004000040000080000108800
def zGO:W:=0xc07807f0ffffe007fffffc07e01fe3fe000fffffff009e19e7f813cff2661ff8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zGP:W:=0x1c03e000000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zGQ:W:=0xc00000003c01e00000000001e001e000000000000000000160000240026000004000000088248010200020044084801000000422101000014000024002400088
def zGR:W:=0xff800000fffffff800000007fffffc000000007ffffc0001600183f003f801ffd08000009934c87020002005d4d4c8100280146318b00081d001036003e800aa
def zGS:W:=0xffffffffffffffffffffffffffffffffffffff800003ff000001fffffffffe00bf3776ee224113c44222c3c1191912210f08380000c3fb840001fc9294b8aa00
def zGT:W:=0x3878003c7800007c000001e1e0003e1ff000000003bef9fb60638603826000041a4888b72882a628835284a4a0811454c0c2525023ff7bab6a4386830240a0
def zGU:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffee7de7c9e0c09cc1d99ff0c41c3894082060191570a720a0a06c8b125c90ca54fef7e2dbe080948159954
def zGV:W:=0xfffffffffff80007ffc00007ffffffffffffffffe003ffffffffff8f83ffffe0bd7fdeaaf7a883e73993d3e7bfb993bddfecfa5ad4ebffffafebff8f83bfebe0
def zGW:W:=0xfe000000000000000000000000000000000000000000000000100080000000006a0000000000000000
def zGX:W:=0x7ffe003fffff0007fe00000fffffe00000387e1e000488800d5a8802339911026a6a0819cd0e4c25ad428047bafea030d030741e0
def zGY:W:=0xff800000ffffffff83fc03fffffffc000000007ffffe21c1fc9f83f9cff801ffd0c08101d9b6cc71b1542837d6d6ccd8a2a5156fbdbc0081d49503694bed11fe
def zGZ:W:=0x7ffffffff80007fffffff800000000000000000001df0000007f8ffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zG0:W:=0xfff8000000000007ffe000000000007fe00220c1f8000380038001e000000000912080202000000484808010008000421020000180000300030000a0
def zG1:W:=0x340e6000000000000000004004088000000000000000000000000100080000003c06a0000000000000000
def zG2:W:=0x38000000fffe1c0000000007fffe1c000000007ffffc000180000380039801ff00000000912080202000000484808010008000421020000180000300030000a0
def zG3:W:=0x7f80003f8000003c000001fe00001fff00003e00379e698e661818181e0600412c888338802a5088242a08620008454a08048402bfb6a88e2418381014060
def zG4:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff03fffffffe73cff3e7fff8445ac998ffaea2b7bd9b7ab6e6a6a1ded4e6c77ed63fff7beffa43cfe34755f8
def zG5:W:=0x3847870fc3861c0783fc03fe1e1e1fc1e00f007ffffc000004800c09cc1d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zG6:W:=0xc07807f0fc07e007fc3ffc000000000000000000000086196718124e700000000000000000000000000100000000000000004000000004102108000000000000
def zG7:W:=0x3f87f80f00000000000000001fe01c01fff000000003ffffffffec000199e000bd2556aa0000034000038341191912211b08f80000c3effe292bbc0000b8aa00
def zG8:W:=0x3847870fc3861c0783fc03f800000000000000000000000000000c09cc0000000000000000000000000000000000000000000000000000000000000000000000
def zG9:W:=0x7ff800fff80007ffc000000000000000000000000000000000638f800000000012000022000084000040800000000004000000000010000000408280000000
def zHa:W:=0x3847870fc3861c0783fc03fe1e0003c1e000007fe000410004800c09cc0581e00040800040800001111000220200008880240008840800000480000900050140
def zHb:W:=0x7f800fff8000003c00007ffe00001fff0007fe001182180e063818381e1e000128800b3a880a5288040a486a0809444a0004a5028100180c04383830140e0
def zHc:W:=0xc03800f03c01e0007c03fc0000000000000000000000860000001246300000000000000000000000000000000000000000000000000000000000000000000000
def zHd:W:=0x387800fff80007ffc00001e1e0003e1ff0007fe001182187e0638f838261e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zHe:W:=0x61e1e1fc1e00f007ffffc4106049e0000001d99ff0841830140820401915408720a0a06c8a125090ca54c00040494080948159954
def zHf:W:=0x38400700c3861c07803c00061e1e1fc0000f007ffffc000004180008401c19ff0040010040020000911008120002004880040104840400000410000840041110
def zHg:W:=0xff8000000007fff800000000001ffc00000000001ffee7de781f80700078001fd480408808144a5000032201505448001200d4210893effa792b006000e8000a
def zHh:W:=0xffffffff0007e000003ffc07ffffffffffffff801f03c6fe6019fc4073fffe18fd2557ba080621508409a951591f32631b0afd2402d7c4fe6119bc4060f8be18
def zHi:W:=0xc0787ff0fc7fe007fc3ffc07e1ffe3fe1ffffffc1f019e39e77873ce73e67f98405a0910ff2ea0b6bd997896e4a6a15ec4c64776d6341411e75843cee34655b8
def zHj:W:=0x3fffffb7e000000000000040040880000020000030200000000001000c0000003ef7a292a000000000000
def zHk:W:=0x3f80000003f81ff8000000001fe01c0000000003e0ff79e698e781b0019800679480408811104a6000020201945048001280904108a3ebea9823012001a80022
def zHl:W:=0x7ff800fff80007ffc00007ffffffffffffffffe00118ff87e0638f83ffffe0995b9a22f7a880e7399050e7bfb993bdd7ec9a5ad4e810ef86c14b8f83bfebe0
def zHm:W:=0xfffff800ffffffffffc00007fffffffffff0007ffffe20c1f801e3ff83ffe1ffd0da8800ffbcc8f7399070a7f6f4c99cc6e4167bdcb81081d6c143ef83ef41ea
def zHn:W:=0x180187e00000000000000000000000000000000000000000000000000000000000000000000000000000
def zHo:W:=0x2187e00000000000000000000000000000000000000000000000000000000000000000000000000000
def zHp:W:=0xc07ffff0ffffe007fffffc07ffffe3ffffffffffff008619671873cff3e7fff8405a8910ffaea0b7bd9978b6e6a6a1dec4e6477ed63c1411e7d843cfe34755f8
def zHq:W:=0xc7fff8f0fff9e3ffffc3fc0000000000000000000003be000001f3ffb0000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zHr:W:=0x180000000000000000000000000000000000000000000000000000000000000000000000000000000
def zHs:W:=0xfff80000fffffffffc000007fffffffe0000007ffffe20c1ff0183fe03fe01ffd0c80000dd34c87231103007f4d4c91882c416739cb00081d601036c03ee01aa
def zHt:W:=0x3c000000000000000000004004088000000000000000000000000000000000003c0000000000000000000
def zHu:W:=0x3847870f00000000000000061e1e1fc1e00f00000003c0fe00000c00001d98000c014288000000000000004008080200110088000043c06e0000080000108800
def zHv:W:=0xfff807fffc07fffffc3ffff800000000000000000002e70000019e7e7c000000262464cc004113004222830000000000080020000003eb000000b41014000000
def zHw:W:=0xc380000783c00000000000000000007fe000000004800009800001e00040800040800001111000220200008880240008840800000480000900050140
def zHx:W:=0x1182007e00000000000000000000000000000000000000000000000000000000000000000000000000000
def zHy:W:=0x3800f0000000007c03fc000000003e0000ff800000861803001006300206000008001004002002040910002000210200424210020004102308000420020400
def zHz:W:=0xc7b878f0fffffffffffffff800000000000000000003bf000001f3fffc000000263664cc224113844222c380000000000c0020000003fb000000f49294000000
def zHA:W:=0xfff80007ffc00000000000000000007fe001182187e0038f800001e0005a8800f7a880a7399050a6a6a0819cc4e4025ad428100186c0438f830741e0
def zHB:W:=0xc00007f00007e000003ffc00001fe000000fff801f0086196718104070601e184000011008062010840928104006204200024524021404106118004060401418
def zHC:W:=0xff800000fffffff800000007fffffc000000007ffffe3fc1ffff83f003f801ffd08000009934ca7020032205d4d4c8100280546318b02f91f92b036003e800aa
def zHD:W:=0xff800000fc07fff800000007e01ffc000000007c1ffe20c1780182700278019fd08000008834c8502000200550d4c81002001423189000815001026002e8008a
def ins:List W:=[za,zt,zi,zc,zl,zf,ze]

def tree3:BTree (List W):=(.node [za,zb,zc,zd] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree3:everyKey (certRow 2 .nil) tree3=true:=by decide +kernel

def tree4:BTree (List W):=(.node [zg,za,zh,zc,zd] (.node [ze,za,zb,zc,zf] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree4:everyKey (certRow 3 tree3) tree4=true:=by decide +kernel

def tree5:BTree (List W):=(.node [ze,zE,zt,zx,zy,zf] (.node [ze,zi,zU,zs,zc,zf] (.node [ze,zi,zt,zI,zx,zz] (.node [ze,zi,za,zU,zr,zf] (.node [ze,zC,zt,zx,zl,zz] (.node [ze,zg,za,zt,zc,zp] (.node [ze,zg,za,zh,zc,zf] .nil .nil) .nil) (.node [ze,zi,za,zt,zQ,zO] .nil .nil)) (.node [ze,zi,za,zk,zl,zp] (.node [ze,zi,za,zN,zc,zO] (.node [ze,zi,za,zae,zc,zf] .nil .nil) .nil) (.node [ze,zi,zB,zx,zl,zz] .nil .nil))) (.node [ze,zi,zt,zx,zl,zad] (.node [ze,zi,zt,zx,zl,zz] (.node [ze,zi,zt,zP,zQ,zf] (.node [ze,zi,zt,zP,zc,zO] .nil .nil) .nil) (.node [ze,zi,zt,zx,zl,z0] .nil .nil)) (.node [ze,zi,zt,zu,zl,zv] (.node [ze,zi,zt,zx,zy,zz] .nil .nil) (.node [ze,zi,zt,z5,zl,z6] .nil .nil)))) (.node [ze,za,zK,zc,zl,zL] (.node [ze,za,zt,zU,zR,zf] (.node [ze,zi,zj,zc,zl,zp] (.node [ze,zi,zA,zx,zy,zf] (.node [ze,zi,zA,zx,zl,zz] .nil .nil) .nil) (.node [ze,zi,zj,zk,zl,zf] .nil .nil)) (.node [ze,za,zN,zc,zab,zf] (.node [ze,za,zt,zX,zl,zL] (.node [ze,za,zt,z3,zc,zf] .nil .nil) .nil) (.node [ze,za,zN,zR,zl,zf] .nil .nil))) (.node [ze,za,zm,zk,zl,zf] (.node [ze,za,zq,zr,zl,zf] (.node [ze,za,zK,zX,zl,zf] (.node [ze,za,zK,zc,zab,zf] .nil .nil) .nil) (.node [ze,za,zm,zc,zo,zf] .nil .nil)) (.node [ze,zW,zN,zc,zl,zf] (.node [ze,zW,zt,zU,zc,zf] .nil .nil) (.node [ze,zE,zt,zx,zl,zz] .nil .nil))))) (.node [zi,zF,zt,zx,zy,zf] (.node [zM,za,zt,zX,zl,zf] (.node [ze,zm,zj,zc,zl,zf] (.node [ze,zT,zK,zc,zl,zf] (.node [ze,zT,zt,zX,zl,zf] (.node [ze,zT,zt,zc,zl,zL] .nil .nil) .nil) (.node [ze,zq,zs,zc,zl,zf] .nil .nil)) (.node [zM,zi,za,zh,zc,zf] (.node [zg,za,zt,zc,zd,zac] (.node [zD,zi,zt,zx,zl,zf] .nil .nil) .nil) (.node [zM,zi,za,zt,zc,zp] .nil .nil))) (.node [zi,zF,zt,zI,zx,zf] (.node [zi,zF,zB,zx,zl,zf] (.node [zC,zF,zt,zx,zl,zf] (.node [zM,zT,zt,zc,zl,zf] .nil .nil) .nil) (.node [zi,zF,zt,zG,zl,zf] .nil .nil)) (.node [zi,zF,zt,zx,zl,zf] (.node [zi,zF,zt,zH,zx,zl] .nil .nil) (.node [zi,zF,zt,zx,zl,zz] .nil .nil)))) (.node [zi,zY,zt,zZ,zl,zf] (.node [zi,za,zt,zS,zc,zO] (.node [zi,za,zh,zc,zV,zd] (.node [zi,zw,zt,zx,zl,zf] (.node [zi,zF,zA,zx,zl,zf] .nil .nil) .nil) (.node [zi,za,zn,zk,zl,zf] .nil .nil)) (.node [zi,za,zt,zc,z7,zd] (.node [zi,za,zt,zc,zV,zaa] (.node [zi,za,zt,zS,zQ,zf] .nil .nil) .nil) (.node [zi,za,zt,zc,z4,zd] .nil .nil))) (.node [zF,zE,zt,zx,zl,zf] (.node [zi,zt,zJ,zx,zl,zf] (.node [zi,zt,zS,zP,zc,zf] (.node [zi,zn,zj,zc,zl,zf] .nil .nil) .nil) (.node [zi,zt,z8,z9,zl,zf] .nil .nil)) (.node [za,zt,zS,zq,zc,zf] (.node [za,zn,zm,zc,zl,zf] .nil .nil) (.node [za,z1,z2,zc,zl,zf] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree5:everyKey (certRow 4 tree4) tree5=true:=by decide +kernel

def tree6_lllll:BTree (List W):=(.node [zjT,zi,za,zt,zc,zl,zcv] (.node [zrH,zi,za,zt,zc,zl,zf] (.node [zc5,zi,za,zt,zc,zl,zkq] (.node [zc5,zi,za,zt,zc,zl,znP] (.node [zc5,zi,za,zt,zc,zl,zcv] (.node [zc5,zg,za,zt,zc,zl,zf] .nil .nil) (.node [zc5,zi,za,zt,zc,zl,zgH] .nil .nil)) (.node [zc5,zi,za,zt,zc,zl,zkX] (.node [zc5,zi,za,zt,zc,zl,zg8] .nil .nil) (.node [zc5,zi,za,zt,zc,zl,zcR] .nil .nil))) (.node [zc5,zi,za,zt,zR,zl,zf] (.node [zc5,zi,za,zt,zc,zc6,zf] (.node [zc5,zi,za,zt,zc,zab,zf] .nil .nil) (.node [zc5,zi,za,zt,zc,zke,zf] .nil .nil)) (.node [zc5,zi,zW,zt,zc,zl,zf] (.node [zc5,zi,za,zde,zc,zl,zf] .nil .nil) .nil))) (.node [zkt,zi,za,zt,zc,zmY,zf] (.node [zkt,zi,za,zt,zc,zd9,zf] (.node [zbF,zi,za,zt,zc,zl,zf] (.node [zaT,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zdF,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zkt,zi,za,zt,zc,zl1,zf] (.node [zkt,zi,za,zt,zc,zn9,zf] .nil .nil) .nil)) (.node [zql,zi,za,zt,zc,zl,zf] (.node [zkt,zi,za,zt,zc,zl,zls] (.node [zkt,zi,za,zt,zc,zlU,zf] .nil .nil) (.node [zkt,zi,za,zt,zc,zl,zgM] .nil .nil)) (.node [zkN,zi,za,zt,zc,zl,zf] (.node [za8,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [zcE,zi,za,zt,zc,zl,zf] (.node [zfR,zi,za,zt,zc,zl,zcR] (.node [zmp,ze,za,zt,zU,zc,zf] (.node [zb4,zi,za,zt,zc,zl,zf] (.node [zkk,zi,za,zt,zc,zd9,zf] .nil .nil) (.node [zpV,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zfR,zfS,zi,za,zt,zc,zf] (.node [zmp,ze,za,zN,zc,zl,zf] .nil .nil) (.node [zfR,zi,za,zt,zc,zl,zcv] .nil .nil))) (.node [zhL,zi,za,zt,zc,zd9,zf] (.node [zfR,zi,za,zt,zc,zl,zd] (.node [zfR,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zfR,zi,za,zt,zc,zcu,zf] .nil .nil)) (.node [zpe,zi,za,zt,zc,zl,zf] (.node [zeW,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zkR,zi,zeF,zt,zc,zl,zf] (.node [zkR,zi,za,zt,zh5,zl,zf] (.node [zhz,zi,za,zt,zc,zl,zf] (.node [zia,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zkR,zi,za,zt,zii,zl,zf] .nil .nil)) (.node [zkR,zi,za,zt,zc,zl,zbX] (.node [zkR,zi,za,zt,zkS,zl,zf] .nil .nil) .nil)) (.node [zaE,zaC,za,zt,zc,zl,zf] (.node [zaE,zaz,zi,zt,zc,zl,zf] (.node [zih,zi,za,zt,zii,zl,zf] .nil .nil) (.node [zaE,zaw,zi,za,zc,zl,zf] .nil .nil)) (.node [zaE,zi,za,zt,zc,zl,zf] (.node [zaE,zi,zaA,za,zt,zc,zf] .nil .nil) .nil)))))
def tree6_llllr:BTree (List W):=(.node [zgy,zi,za,zt,zc,zl,zcm] (.node [zcC,zgP,za,zt,zc,zl,zf] (.node [zpO,zi,za,zt,zc,zl,zf] (.node [za3,zi,za,zt,zc,zl,zf] (.node [zaE,zi,zt,zc,zaB,zl,zf] (.node [zaE,zi,za,zc,zay,zl,zf] .nil .nil) (.node [zaE,za,zt,zc,zaD,zl,zf] .nil .nil)) (.node [zkj,zi,za,zt,zc,zd9,zf] (.node [zrT,zi,za,zt,zc,zl,zcv] .nil .nil) (.node [zaG,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zcC,ze,za,zN,zc,zl,zf] (.node [zil,zi,za,zt,zc,zl,zf] (.node [zil,zi,za,zt,zU,zc,zf] .nil .nil) (.node [zcC,ze,za,zt,zU,zc,zf] .nil .nil)) (.node [zcC,zM,za,zt,zc,zl,zf] (.node [zcC,zg,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zrt,zgP,za,zt,zc,zl,zf] (.node [zcC,za,zt,zpI,zc,zl,zf] (.node [zcC,zi,za,zt,zc,zab,zf] (.node [zcC,zkP,za,zt,zc,zl,zf] .nil .nil) (.node [zcC,zgQ,za,zt,zc,zl,zf] .nil .nil)) (.node [zcC,za,zt,zc,zpE,zl,zf] (.node [zcC,za,zt,zc,zk6,zV,zf] .nil .nil) .nil)) (.node [zgy,zi,za,zt,zgk,zl,zf] (.node [zgy,zi,zeM,zt,zc,zl,zf] (.node [zlJ,zgP,za,zt,zc,zl,zf] .nil .nil) (.node [zgy,zi,za,zcJ,zc,zl,zf] .nil .nil)) (.node [zgy,zi,za,zt,zc,zl,zf] (.node [zgy,zi,za,zt,zc,zgb,zl] .nil .nil) .nil)))) (.node [zmw,zi,za,zmx,zc,zl,zf] (.node [zmw,zgo,za,zgX,zc,zl,zf] (.node [zmz,zi,za,zt,zc,zl,zf] (.node [zgy,zi,za,zN,zc,zl,zf] (.node [zgy,zi,za,zt,zgn,zl,zf] .nil .nil) (.node [zgy,zi,zcI,zt,zc,zl,zf] .nil .nil)) (.node [zfq,zi,za,zt,zc,zl,zf] (.node [zhm,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zmw,zi,za,zgX,zc,zl,zls] (.node [zmw,zi,za,zgX,zc,zl,zg8] (.node [zmw,zi,za,zgX,zc,zl1,zf] .nil .nil) (.node [zmw,zi,za,zgX,zc,zl,zf] .nil .nil)) (.node [zmw,zi,za,zq2,zc,zl,zf] (.node [zmw,zi,za,zgX,zc,zc6,zf] .nil .nil) .nil))) (.node [zk5,zi,za,zh,zc,zl,zf] (.node [zjY,zi,za,zgX,zc,zl,zf] (.node [zmw,za,zgX,z2,zc,zl,zf] (.node [zmw,zi,za,z1,zc,zl,zf] .nil .nil) (.node [zmq,zi,za,zgX,zc,zl,zf] .nil .nil)) (.node [zlV,zi,za,zt,zc,zl,zf] (.node [zgW,zi,za,zgX,zc,zl,zf] .nil .nil) .nil)) (.node [zbo,zi,za,zbm,zt,zl,zf] (.node [zbo,zbj,za,zt,zc,zl,zf] (.node [zk5,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zbo,zi,zbi,zt,zc,zl,zf] .nil .nil)) (.node [zbo,zi,za,zt,zc,zl,zcv] (.node [zbo,zi,za,zbf,zt,zc,zf] .nil .nil) .nil)))))
def tree6_llll:BTree (List W):=.node [zaE,zi,za,zt,zc,zax,zf] tree6_lllll tree6_llllr
def tree6_lllrl:BTree (List W):=(.node [zdg,zi,za,zt,zc0,zc,zf] (.node [zb9,zi,za,zt,zc,zV,zf] (.node [zb9,zi,zbZ,zt,zc,zl,zf] (.node [zbo,zi,za,zt,zr,zl,zf] (.node [zbo,zi,za,zt,zc,zl,zd] (.node [zbo,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zbo,zi,za,zt,zc,zo,zf] .nil .nil)) (.node [zbo,za,zt,zbk,zc,zl,zf] (.node [zbo,zi,zt,zs,zc,zl,zf] .nil .nil) (.node [zb9,zb3,za,zt,zc,zl,zf] .nil .nil))) (.node [zb9,zi,za,zt,zc,zl1,zf] (.node [zb9,zi,za,zbP,zt,zc,zl] (.node [zb9,zi,za,zbW,zt,zl,zf] .nil .nil) (.node [zb9,zi,za,zt,zc,zd9,zf] .nil .nil)) (.node [zb9,zi,za,zt,zc,zl,zp] (.node [zb9,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zg9,zi,za,zt,zc,zl,zkp] (.node [zgF,zi,za,zt,zc,zl,zf] (.node [zb9,zi,zt,zb2,zc,zl,zf] (.node [zb9,zi,za,zt,zbY,zl,zf] .nil .nil) (.node [zb9,za,zt,zq,zc,zl,zf] .nil .nil)) (.node [zg9,zi,zha,zt,zc,zl,zf] (.node [zg9,zi,zgp,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zdg,zdb,za,zt,zc,zl,zf] (.node [zg9,zi,zns,zt,zc,zl,zf] (.node [zg9,zi,za,zt,zgz,zl,zf] .nil .nil) (.node [zi2,zi,zgp,zt,zc,zl,zf] .nil .nil)) (.node [zdg,zi,za,zt,zc9,zl,zf] (.node [zdg,zi,za,zc7,zc,zl,zf] .nil .nil) .nil)))) (.node [zbN,zi,za,zt,zc,zl,zf] (.node [zkL,zi,za,zt,zc,zl,zcv] (.node [zdg,zi,za,zda,zc,zl,zf] (.node [zdg,zi,za,zt,zc,zc8,zf] (.node [zdg,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zdg,zi,za,zt,zc1,zl,zf] .nil .nil)) (.node [zm6,zi,za,zt,zc,zl,zf] (.node [zdg,za,zdd,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zdv,zi,za,zt,zc,zl,zf] (.node [zjd,zi,za,zt,zc,zl,zf] (.node [zlf,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zbB,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zgh,zi,za,zt,zc,zl,zf] (.node [zhy,zi,za,zt,zc,zd9,zf] .nil .nil) .nil))) (.node [ze,ziV,zi,zt,zaB,zl,zf] (.node [ze,zbh,zi,za,zr,zl,zf] (.node [ze,zeT,zi,zt,zc1,zl,zf] (.node [ze,zrw,zi,zt,zx,zl,zf] .nil .nil) (.node [ze,zeT,zi,zda,zc,zl,zf] .nil .nil)) (.node [ze,ziV,zi,za,zay,zl,zf] (.node [ze,zbh,zi,zs,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zce,zi,za,zN,zc,zf] (.node [ze,zce,zg,za,zt,zc,zf] (.node [ze,zpq,zi,za,zt,zc,zl] .nil .nil) (.node [ze,zce,zi,za,zt,zgn,zf] .nil .nil)) (.node [ze,zgw,zcW,za,zbR,zc,zf] (.node [ze,zce,zi,zcI,zt,zc,zf] .nil .nil) .nil)))))
def tree6_lllrr:BTree (List W):=(.node [ze,zli,za,zt,zc,zl,zf] (.node [ze,zie,zi,za,zt,zc,zf] (.node [ze,zcW,za,zN,zc,zl,zf] (.node [ze,zcW,zi,za,zh,zc,zf] (.node [ze,zgw,zi,za,zN,zc,zf] (.node [ze,zgw,zi,za,zU,zc,zf] .nil .nil) (.node [ze,zgw,za,zq,zc,zl,zf] .nil .nil)) (.node [ze,zcW,za,zt,zU,zc,zf] (.node [ze,zcW,zi,za,zt,zc,zp] .nil .nil) (.node [ze,zcW,za,zt,zq,zc,zf] .nil .nil))) (.node [ze,zqm,zi,za,zt,zc,zf] (.node [ze,zqe,zi,za,zt,zc,zf] (.node [ze,zqf,zi,za,zt,zc,zf] .nil .nil) (.node [ze,zl8,zi,za,zt,zc,zf] .nil .nil)) (.node [ze,zis,zi,za,zt,zc,zf] (.node [ze,zeC,zi,za,zt,zc,zf] .nil .nil) .nil))) (.node [ze,zcA,za,zt,zc,zl,zf] (.node [ze,zcz,zi,zt,zc,zl,zf] (.node [ze,zqh,zi,za,zt,zc,zf] (.node [ze,zqh,zi,za,zt,zc,zl] .nil .nil) (.node [ze,zfp,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zh2,zi,za,zt,zc,zf] (.node [ze,zp6,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zjP,za,zt,zR,zl,zf] (.node [ze,zjP,za,zt,zc,zl,zcq] (.node [ze,zjP,za,zcp,zc,zl,zf] .nil .nil) (.node [ze,zjP,za,zt,zc,zab,zf] .nil .nil)) (.node [ze,zrd,za,zt,zc,zl,zf] (.node [ze,zjP,zW,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zbj,za,zt,zr,zl,zf] (.node [ze,zp8,za,zt,zc,zl,zf] (.node [ze,zaj,za,zh,zc,zl,zf] (.node [ze,zgo,za,zt,zc,zl,zf] (.node [ze,zgo,za,zcp,zc,zl,zf] .nil .nil) (.node [ze,zgo,za,zbR,zc,zl,zf] .nil .nil)) (.node [ze,zan,za,zt,zc,zl,zf] (.node [ze,zaj,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zbj,za,zbQ,zc,zl,zf] (.node [ze,zbj,za,zbm,zt,zl,zf] (.node [ze,zbj,zbi,zt,zc,zl,zf] .nil .nil) (.node [ze,zbj,za,zbf,zt,zc,zf] .nil .nil)) (.node [ze,zbj,za,zt,zc,zo,zf] (.node [ze,zbj,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zb3,zbZ,zt,zc,zl,zf] (.node [ze,zdG,za,zt,zc,zl,zf] (.node [ze,zbj,zt,zs,zc,zl,zf] (.node [ze,zbj,za,zbR,zc,zl,zf] .nil .nil) (.node [ze,zaV,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zcs,za,zt,zc,zl,zf] (.node [ze,zfZ,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zb3,za,zt,zc,zl,zp] (.node [ze,zb3,za,zbP,zt,zc,zl] (.node [ze,zb3,za,zbW,zt,zl,zf] .nil .nil) (.node [ze,zb3,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zb3,zt,zb2,zc,zl,zf] (.node [ze,zb3,za,zt,zbY,zl,zf] .nil .nil) .nil)))))
def tree6_lllr:BTree (List W):=.node [ze,zgw,zg,za,zt,zc,zf] tree6_lllrl tree6_lllrr
def tree6_lll:BTree (List W):=.node [zbo,zi,za,zt,zc,zl,zg8] tree6_llll tree6_lllr
def tree6_llrll:BTree (List W):=(.node [ze,ziy,za,zt,zc,zl,zf] (.node [ze,zj9,za,zt,zc,zl,zf] (.node [ze,zi7,za,zt,zgn,zl,zf] (.node [ze,zfK,zi,za,zt,zc,zf] (.node [ze,zcx,zi,za,zt,zc,zf] (.node [ze,zm5,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zjv,zi,za,zc,zl,zf] .nil .nil)) (.node [ze,zi7,za,zt,zU,zc,zf] (.node [ze,zgx,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi7,za,zt,zc,zl,zcm] .nil .nil))) (.node [ze,zas,za,zt,zc,zl,zf] (.node [ze,zi7,za,zja,zc,zl,zf] (.node [ze,zi7,za,ziN,zc,zl,zf] .nil .nil) (.node [ze,zi7,za,zN,zc,zl,zf] .nil .nil)) (.node [ze,zah,za,zt,zc,zl,zf] (.node [ze,zbc,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zdb,za,zda,zc,zl,zf] (.node [ze,zdb,za,zt,zc,zl,zf] (.node [ze,zdb,za,zt,zc9,zl,zf] (.node [ze,zdb,za,zc7,zc,zl,zf] .nil .nil) (.node [ze,zdb,za,zt,zc0,zc,zf] .nil .nil)) (.node [ze,zdb,za,zt,zc1,zl,zf] (.node [ze,zdb,za,zt,zc,zc8,zf] .nil .nil) .nil)) (.node [ze,zee,za,zt,zc,zl,zf] (.node [ze,zmg,za,zt,zc,zl,zf] (.node [ze,zd1,za,zt,zc,zl,zf] .nil .nil) (.node [ze,znQ,zi,za,zt,zc,zf] .nil .nil)) (.node [ze,zev,za,zt,zc,zl,zf] (.node [ze,zbu,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zcf,zi,zt,zc,zl,zf] (.node [ze,zaz,zaw,zi,zc,zl,zf] (.node [ze,zfG,za,zt,zc,zl,zf] (.node [ze,zpl,za,zt,zc,zl,zf] (.node [ze,zkD,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zfD,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zeG,zi,zt,zc,zl,zz] (.node [ze,zmh,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zaz,zi,zt,zc,zax,zf] (.node [ze,zaz,zi,zaA,zt,zc,zf] (.node [ze,zaz,zaC,zt,zc,zl,zf] .nil .nil) (.node [ze,zaz,zi,zt,zc,zl,zf] .nil .nil)) (.node [ze,zaz,zt,zc,zaD,zl,zf] (.node [ze,zaz,zi,zc,zay,zl,zf] .nil .nil) .nil))) (.node [ze,zck,zi,za,zc,zl,zp] (.node [ze,ze0,za,zt,zc,zl,zf] (.node [ze,za1,zi,zt,zc,zl,zf] (.node [ze,zdW,zi,zt,zc,zl,zf] .nil .nil) (.node [ze,zoa,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zck,zi,za,zU,zc,zf] (.node [ze,zjp,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zck,za,z2,zc,zl,zf] (.node [ze,zck,za,zbI,zc,zl,zf] (.node [ze,zck,zi,zb2,zc,zl,zf] .nil .nil) (.node [ze,zck,za,zq,zc,zl,zf] .nil .nil)) (.node [ze,zdC,zi,za,zc,zl,zf] (.node [ze,zfU,zi,za,zc,zl,zf] .nil .nil) .nil)))))
def tree6_llrlr:BTree (List W):=(.node [ze,zg,za,zt,zX,zl,zf] (.node [ze,zc4,za,zt,zR,zl,zf] (.node [ze,zcr,zi,za,zc,zl,zf] (.node [ze,zaw,zi,za,zc,zl,zf] (.node [ze,zaw,zaC,za,zc,zl,zf] (.node [ze,zgl,zi,za,zc,zl,zf] .nil .nil) (.node [ze,zaw,zi,zaA,za,zc,zf] .nil .nil)) (.node [ze,zaw,zi,zc,zaB,zl,zf] (.node [ze,zaw,zi,za,zc,zax,zf] .nil .nil) (.node [ze,zaw,za,zc,zaD,zl,zf] .nil .nil))) (.node [ze,zc4,zi,za,zh,zc,zf] (.node [ze,zdy,zi,za,zc,zl,zf] (.node [ze,znS,zi,za,zc,zl,zf] .nil .nil) (.node [ze,zfe,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zc4,za,zt,zc,zab,zf] (.node [ze,zc4,zi,za,zt,zc,zp] .nil .nil) .nil))) (.node [ze,zg,za,zt,zkF,zl,zf] (.node [ze,zg,zge,zt,zc,zl,zf] (.node [ze,zqt,za,zt,zc,zl,zf] (.node [ze,zc4,zW,zt,zc,zl,zf] .nil .nil) (.node [ze,zmF,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zg,za,zbG,zt,zc,zf] (.node [ze,zg,za,zdh,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zg,za,zt,zc,zl,zL] (.node [ze,zg,za,zt,zc,zkz,zl] (.node [ze,zg,za,zt,zc,zk6,zf] .nil .nil) (.node [ze,zg,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zg,za,zt,zc,zf,zac] (.node [ze,zg,za,zt,zc,zab,zf] .nil .nil) .nil)))) (.node [ze,zgZ,za,zga,zc,zl,zf] (.node [ze,zfS,zi,za,zt,zc,zf] (.node [ze,za6,zi,za,zt,zc,zf] (.node [ze,zg,zT,zt,zc,zl,zf] (.node [ze,zg,za,zK,zc,zl,zf] .nil .nil) (.node [ze,zku,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zfS,zi,za,zt,zc,zgb] (.node [ze,zo3,zi,za,zt,zc,zf] .nil .nil) .nil)) (.node [ze,zgZ,za,zt,zU,zc,zf] (.node [ze,zqi,zi,za,zt,zc,zf] (.node [ze,zfS,zi,za,zt,zc,zac] .nil .nil) (.node [ze,zec,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zgZ,za,ziN,zc,zl,zf] (.node [ze,zgZ,za,zt,zc,zl,zcm] .nil .nil) .nil))) (.node [ze,zaP,za,zaQ,zc,zl,zf] (.node [ze,zba,za,zt,zc,zl,zf] (.node [ze,zgZ,zcI,zt,zc,zl,zf] (.node [ze,zgZ,za,zN,zc,zl,zf] .nil .nil) (.node [ze,zbs,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,znL,za,zt,zc,zl,zf] (.node [ze,zhY,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zaP,za,zaR,zc,zl,zf] (.node [ze,zaP,za,zt,zc,zl,zf] (.node [ze,zaP,za,zt,zgk,zl,zf] .nil .nil) (.node [ze,zaP,za,zt,zcl,zl,zf] .nil .nil)) (.node [ze,zlr,za,zt,zc,zl,zf] (.node [ze,zeq,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree6_llrl:BTree (List W):=.node [ze,zdf,zi,za,zc,zl,zf] tree6_llrll tree6_llrlr
def tree6_llrrl:BTree (List W):=(.node [ze,zC,za,zt,zc,zy,zf] (.node [ze,zbT,za,zca,zc,zl,zf] (.node [ze,zlW,za,zt,zc,zl,zf] (.node [ze,zaC,zt,zc,zaB,zl,zf] (.node [ze,zaC,za,zt,zc,zax,zf] (.node [ze,zaC,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zaC,za,zc,zay,zl,zf] .nil .nil)) (.node [ze,zkd,za,zt,zc,zl,zf] (.node [ze,zhD,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zbz,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zcK,za,zt,zc,zl,zf] (.node [ze,zqo,za,zt,zc,zl,zf] (.node [ze,ziL,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zcL,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zbT,zeM,zt,zc,zl,zf] (.node [ze,zm1,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zlk,za,zt,zc,zl,zf] (.node [ze,zno,za,zt,zc,zl,zf] (.node [ze,zbT,za,zbU,zc,zl,zf] (.node [ze,zbT,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zbT,zip,zt,zc,zl,zf] .nil .nil)) (.node [ze,zo1,za,zt,zc,zl,zf] (.node [ze,zrp,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zC,za,zt,zH,zc,zl] (.node [ze,zC,za,zB,zc,zl,zf] (.node [ze,zC,zek,zt,zx,zl,zf] .nil .nil) (.node [ze,zC,za,zt,zI,zc,zf] .nil .nil)) (.node [ze,zC,za,zt,zc,zl,zz] (.node [ze,zC,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zfk,za,zt,zc,zl,zf] (.node [ze,zij,za,zt,zc,zl,zf] (.node [ze,zqJ,za,zt,zc,zl,zf] (.node [ze,zet,za,zt,zc,zl,zf] (.node [ze,zC,za,zA,zc,zl,zf] .nil .nil) (.node [ze,ziI,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zm0,za,zt,zc,zl,zf] (.node [ze,zly,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zci,za,zt,zc,zl,zf] (.node [ze,zms,za,zt,zc,zl,zf] (.node [ze,zqE,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zjz,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zrR,za,zt,zc,zl,zf] (.node [ze,zpt,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zg4,za,zt,zc,zl,zf] (.node [ze,zeV,za,zt,zc,zl,zf] (.node [ze,zj3,za,zt,zc,zl,zf] (.node [ze,zmK,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zl6,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zfc,za,zt,zc,zl,zf] (.node [ze,zib,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zrI,za,zt,zc,zl,zf] (.node [ze,zrc,za,zt,zc,zl,zf] (.node [ze,zf3,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zru,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zgP,za,zt,zR,zl,zf] (.node [ze,zma,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree6_llrrr:BTree (List W):=(.node [ze,zi,zfi,zt,zc,zaB,zl] (.node [ze,zjn,za,zt,zc,zl,zf] (.node [ze,zjJ,za,zd5,zc,zl,zf] (.node [ze,zjJ,za,zt,zc,zl,zlh] (.node [ze,zjJ,za,zkn,zc,zl,zf] (.node [ze,zhW,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zjJ,za,zt,zc,ze9,zf] .nil .nil)) (.node [ze,zjJ,za,zt,zc,zl,zbX] (.node [ze,zjJ,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zjJ,za,zt,zc,zhS,zf] .nil .nil))) (.node [ze,zjn,za,zob,zc,zl,zf] (.node [ze,zmy,za,zt,zc,zl,zf] (.node [ze,zjJ,zeF,zt,zc,zl,zf] .nil .nil) (.node [ze,zmO,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zjn,za,zt,zc,zl,zdn] (.node [ze,zjn,za,zt,zc,zmc,zf] .nil .nil) .nil))) (.node [ze,zi,zcU,za,zt,zc,zf] (.node [ze,zjn,za,zjS,zc,zl,zf] (.node [ze,zjn,za,zt,zc,zdm,zf] (.node [ze,zjn,za,zt,zc,zl,zkp] .nil .nil) (.node [ze,zjn,za,zt,zgz,zl,zf] .nil .nil)) (.node [ze,zds,za,zt,zc,zl,zf] (.node [ze,zo6,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zaA,za,zc,zay,zf] (.node [ze,zi,zjZ,za,zt,zc,zf] (.node [ze,zi,zrv,za,zt,zc,zf] .nil .nil) (.node [ze,zi,zaA,za,zt,zc,zf] .nil .nil)) (.node [ze,zi,zmf,za,zt,zc,zf] (.node [ze,zi,zaA,zt,zc,zaB,zf] .nil .nil) .nil)))) (.node [ze,zi,zek,zt,zx,zy,zf] (.node [ze,zi,zh0,za,zt,zc,zf] (.node [ze,zi,zaZ,za,zt,zc,zf] (.node [ze,zi,zav,za,zt,zc,zl] (.node [ze,zi,zgT,za,zt,zl,zf] .nil .nil) (.node [ze,zi,zav,za,zt,zl,zf] .nil .nil)) (.node [ze,zi,zfm,za,zt,zl,zf] (.node [ze,zi,zaZ,za,zt,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zek,zt,zH,zx,zl] (.node [ze,zi,zek,zt,zG,zl,zf] (.node [ze,zi,zek,zB,zx,zl,zf] .nil .nil) (.node [ze,zi,zek,zt,zI,zx,zf] .nil .nil)) (.node [ze,zi,zek,zt,zx,zl,zz] (.node [ze,zi,zek,zt,zx,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zge,zt,zc,zl,zf] (.node [ze,zi,zF,zt,zx,zl,zf] (.node [ze,zi,zln,zt,zx,zl,zf] (.node [ze,zi,zek,zA,zx,zl,zf] .nil .nil) (.node [ze,zi,zog,zt,zx,zl,zf] .nil .nil)) (.node [ze,zi,zig,zt,zc,zl,zf] (.node [ze,zi,zig,zt,zU,zc,zf] .nil .nil) .nil)) (.node [ze,zi,zeM,zt,zc,zl,zf] (.node [ze,zi,zeM,zt,zgk,zl,zf] (.node [ze,zi,zeM,zcJ,zc,zl,zf] .nil .nil) (.node [ze,zi,zeM,zt,zc,zgb,zl] .nil .nil)) (.node [ze,zi,zeM,zt,zgn,zl,zf] (.node [ze,zi,zeM,zt,zc,zl,zcm] .nil .nil) .nil)))))
def tree6_llrr:BTree (List W):=.node [ze,zgP,zW,zt,zc,zl,zf] tree6_llrrl tree6_llrrr
def tree6_llr:BTree (List W):=.node [ze,zaC,zaA,za,zt,zc,zf] tree6_llrl tree6_llrr
def tree6_ll:BTree (List W):=.node [ze,ze3,za,zt,zc,zl,zf] tree6_lll tree6_llr
def tree6_lrlll:BTree (List W):=(.node [ze,zi,zhF,zt,zc,zl,zf] (.node [ze,zi,zbZ,zt,zc,zl,zf] (.node [ze,zi,zbi,zt,zc,zo,zf] (.node [ze,zi,zai,zt,zc,zl,zf] (.node [ze,zi,zcg,zt,zc,zl,zf] (.node [ze,zi,zhi,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zai,zh,zc,zl,zf] .nil .nil)) (.node [ze,zi,zbi,zbf,zt,zc,zf] (.node [ze,zi,zbi,zbm,zt,zl,zf] .nil .nil) (.node [ze,zi,zbi,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,zbZ,zbW,zt,zl,zf] (.node [ze,zi,zmm,zt,zc,zl,zf] (.node [ze,zi,zbi,zt,zr,zl,zf] .nil .nil) (.node [ze,zi,zrb,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zbZ,zca,zc,zl,zf] (.node [ze,zi,zbZ,zbP,zt,zc,zl] .nil .nil) .nil))) (.node [ze,zi,znu,zt,zc,zl,zf] (.node [ze,zi,zdV,zt,zc,zl,zf] (.node [ze,zi,zbZ,zt,zbY,zl,zf] (.node [ze,zi,zbZ,zt,zc,zl,zp] .nil .nil) (.node [ze,zi,zbZ,zdK,zc,zl,zf] .nil .nil)) (.node [ze,zi,zjR,zt,zc,zl,zf] (.node [ze,zi,zg6,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zcS,zt,zc,zl,zf] (.node [ze,zi,zju,zt,zc,zl,zf] (.node [ze,zi,zqw,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zh6,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zhw,zt,zc,zl,zf] (.node [ze,zi,zhZ,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zkB,zt,zc,zl,zcR] (.node [ze,zi,zp1,zt,zx,zl,zf] (.node [ze,zi,zhM,zt,zc,zl,zf] (.node [ze,zi,zcH,zt,zc,zl,zf] (.node [ze,zi,zkK,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zqK,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zcO,zt,zc,zl,zf] (.node [ze,zi,zrj,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zkB,zcp,zc,zl,zf] (.node [ze,zi,zrl,zt,zc,zl,zf] (.node [ze,zi,zk7,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zgp,zt,zgz,zl,zf] .nil .nil)) (.node [ze,zi,zkB,zt,zc,zho,zf] (.node [ze,zi,zkB,zt,zof,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zkI,zt,zc,zl,zf] (.node [ze,zi,zkB,zt,zR,zl,zf] (.node [ze,zi,zkB,zt,zc,zl,zcq] (.node [ze,zi,zkB,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zkB,zt,zc,zab,zf] .nil .nil)) (.node [ze,zi,zkC,zt,zc,zl,zf] (.node [ze,zi,zkB,zde,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zeI,zt,zl,zf] (.node [ze,zi,za,zdR,zt,zc,zf] (.node [ze,zi,za,zkU,zt,zc,zf] .nil .nil) (.node [ze,zi,za,zeI,zh,zl,zf] .nil .nil)) (.node [ze,zi,za,zbm,zt,zl,zf] (.node [ze,zi,za,zbm,zbf,zt,zf] .nil .nil) .nil)))))
def tree6_lrllr:BTree (List W):=(.node [ze,zi,za,za5,zU,zc,zf] (.node [ze,zi,za,zif,zt,zc,zl] (.node [ze,zi,za,zbW,zt,zl,zf] (.node [ze,zi,za,zim,zt,zU,zf] (.node [ze,zi,za,zeS,zt,zl,zf] (.node [ze,zi,za,zio,zt,zl,zf] .nil .nil) (.node [ze,zi,za,zhT,zt,zl,zf] .nil .nil)) (.node [ze,zi,za,zbW,zbP,zt,zl] (.node [ze,zi,za,zim,zt,zl,zf] .nil .nil) (.node [ze,zi,za,zbW,zaQ,zl,zf] .nil .nil))) (.node [ze,zi,za,zrn,zt,zl,zf] (.node [ze,zi,za,zbW,zbJ,zl,zf] (.node [ze,zi,za,zbW,zt,zl,zp] .nil .nil) (.node [ze,zi,za,zcV,zt,zl,zf] .nil .nil)) (.node [ze,zi,za,zif,zt,zU,zc] (.node [ze,zi,za,zbS,zt,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zbf,zt,zc,zf] (.node [ze,zi,za,zbq,zc,zo,zf] (.node [ze,zi,za,zbq,zh,zc,zf] (.node [ze,zi,za,zbq,za5,zc,zac] .nil .nil) (.node [ze,zi,za,zbq,zt,zc,zp] .nil .nil)) (.node [ze,zi,za,zmS,zt,zc,zf] (.node [ze,zi,za,zbq,zr,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zcP,zc,zl,zf] (.node [ze,zi,za,zlR,zt,zc,zf] (.node [ze,zi,za,zbf,zt,zr,zf] .nil .nil) (.node [ze,zi,za,znO,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,za5,zt,zc,zo] (.node [ze,zi,za,za5,zh,zc,zl] .nil .nil) .nil)))) (.node [ze,zi,za,zbP,zt,zbY,zl] (.node [ze,zi,za,ziF,zc,zl,zf] (.node [ze,zi,za,zn8,zc,zl,zf] (.node [ze,zi,za,zmi,zc,zl,zf] (.node [ze,zi,za,za5,zc,zl,zp] .nil .nil) (.node [ze,zi,za,zbE,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zdB,zc,zl,zf] (.node [ze,zi,za,zkH,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zbH,zc,zl,zf] (.node [ze,zi,za,zbd,zc,zl,zf] (.node [ze,zi,za,zbd,zt,zc,zl] .nil .nil) (.node [ze,zi,za,zbH,zt,zc,zf] .nil .nil)) (.node [ze,zi,za,zbP,zt,zc,zl] (.node [ze,zi,za,zoP,zt,zc,zl] .nil .nil) .nil))) (.node [ze,zi,za,zdk,zt,zc,zl] (.node [ze,zi,za,zdE,zt,zl,zf] (.node [ze,zi,za,zoe,zt,zc,zf] (.node [ze,zi,za,zkV,zt,zc,zl] .nil .nil) (.node [ze,zi,za,zi5,zt,zc,zl] .nil .nil)) (.node [ze,zi,za,zhQ,zt,zc,zf] (.node [ze,zi,za,zdE,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zhO,zr,zl,zf] (.node [ze,zi,za,zcN,zt,zc,zl] (.node [ze,zi,za,zfY,zt,zc,zf] .nil .nil) (.node [ze,zi,za,zhO,zc,zo,zf] .nil .nil)) (.node [ze,zi,za,zn7,zc,zl,zf] (.node [ze,zi,za,zaX,zc,zl,zf] .nil .nil) .nil)))))
def tree6_lrll:BTree (List W):=.node [ze,zi,za,zbm,zt,zo,zf] tree6_lrlll tree6_lrllr
def tree6_lrlrl:BTree (List W):=(.node [ze,zi,za,zqs,zc,zl,zf] (.node [ze,zi,za,zag,zc,zl,zf] (.node [ze,zi,za,zqu,zc,zl,zf] (.node [ze,zi,za,zcJ,zc,zl,zf] (.node [ze,zi,za,zcJ,zgk,zl,zf] (.node [ze,zi,za,zdh,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zcJ,zc,zgb,zl] .nil .nil)) (.node [ze,zi,za,zcJ,zgn,zl,zf] (.node [ze,zi,za,zcJ,zc,zl,zcm] .nil .nil) (.node [ze,zi,za,zhe,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zeO,zbY,zl,zf] (.node [ze,zi,za,zeO,zU,zc,zf] (.node [ze,zi,za,zgL,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zeO,zc,zl,zp] .nil .nil)) (.node [ze,zi,za,zoN,zc,zl,zf] (.node [ze,zi,za,zaq,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zg7,zc,zl,zf] (.node [ze,zi,za,zc7,zc,zl,zf] (.node [ze,zi,za,zc7,zc9,zl,zf] (.node [ze,zi,za,zra,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zc7,zc0,zc,zf] .nil .nil)) (.node [ze,zi,za,zc7,zc1,zl,zf] (.node [ze,zi,za,zc7,zc,zc8,zf] .nil .nil) .nil)) (.node [ze,zi,za,zmZ,zc,zl,zf] (.node [ze,zi,za,zef,zc,zl,zf] (.node [ze,zi,za,zdO,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zoj,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zjx,zc,zl,zf] (.node [ze,zi,za,zeJ,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zaQ,zbJ,zl,zf] (.node [ze,zi,za,ziS,zc,zl,zf] (.node [ze,zi,za,zjH,zc,zl,zf] (.node [ze,zi,za,zpA,zc,zl,zf] (.node [ze,zi,za,zjN,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zjy,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zrf,zc,zl,zf] (.node [ze,zi,za,ziO,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zo2,zc,zl,zf] (.node [ze,zi,za,zgS,zc,zl,zf] (.node [ze,zi,za,zbG,zr,zl,zf] .nil .nil) (.node [ze,zi,za,zed,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zaQ,zc,zl,zf] (.node [ze,zi,za,zal,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,ziK,zc,zl,zf] (.node [ze,zi,za,znU,zc,zl,zf] (.node [ze,zi,za,zaM,zc,zl,zf] (.node [ze,zi,za,zlm,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zpH,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zqC,zc,zl,zf] (.node [ze,zi,za,zqk,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zdc,zc,zl,zf] (.node [ze,zi,za,zhJ,zc,zl,zf] (.node [ze,zi,za,zpx,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zou,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zca,zc,zl,zf] (.node [ze,zi,za,zcT,zc,zl,zf] .nil .nil) .nil)))))
def tree6_lrlrr:BTree (List W):=(.node [ze,zi,za,zjC,zc,zl,zf] (.node [ze,zi,za,zgv,zc,zl,zf] (.node [ze,zi,za,zB,zc,zy,zf] (.node [ze,zi,za,zB,zI,zc,zf] (.node [ze,zi,za,zn3,zc,zl,zf] (.node [ze,zi,za,zdr,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zpL,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zB,zc,zl,zf] (.node [ze,zi,za,zB,zH,zc,zl] .nil .nil) (.node [ze,zi,za,zB,zc,zl,zz] .nil .nil))) (.node [ze,zi,za,zf9,zc,zl,zf] (.node [ze,zi,za,zew,zc,zl,zf] (.node [ze,zi,za,zh7,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zjA,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zji,zc,zl,zf] (.node [ze,zi,za,zdX,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zft,zc,zl,zf] (.node [ze,zi,za,zb8,zU,zc,zf] (.node [ze,zi,za,zpR,zc,zl,zf] (.node [ze,zi,za,ziU,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zd2,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zbQ,zc,zl,zf] (.node [ze,zi,za,zfs,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zeo,zc,zl,zf] (.node [ze,zi,za,zhB,zc,zl,zf] (.node [ze,zi,za,zgf,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zjG,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zmv,zc,zl,zf] (.node [ze,zi,za,zoz,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zit,zc,zl,zf] (.node [ze,zi,za,zh,zc,zV,zf] (.node [ze,zi,za,zh,zc,zl,zf] (.node [ze,zi,za,zh,zc,zd9,zf] (.node [ze,zi,za,ziM,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zh,zc,zl,zcv] .nil .nil)) (.node [ze,zi,za,zh,zc,zl,zp] (.node [ze,zi,za,zh,zc,zl,zd] .nil .nil) .nil)) (.node [ze,zi,za,zdo,zc,zl,zf] (.node [ze,zi,za,zh,zk,zl,zf] (.node [ze,zi,za,zh,zc,zo,zf] .nil .nil) (.node [ze,zi,za,zrE,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zgc,zc,zl,zf] (.node [ze,zi,za,zjk,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zkn,zc,zl,zf] (.node [ze,zi,za,zdD,zc,zl,zf] (.node [ze,zi,za,zhs,zc,zl,zf] (.node [ze,zi,za,zkr,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zk2,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zkn,zc,zl,zlh] (.node [ze,zi,za,zkn,zc,ze9,zf] .nil .nil) .nil)) (.node [ze,zi,za,zcp,zof,zl,zf] (.node [ze,zi,za,zkn,zc,zhS,zf] (.node [ze,zi,za,zkn,zc,zl,zbX] .nil .nil) (.node [ze,zi,za,zoC,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zcp,zc,zl,zcR] (.node [ze,zi,za,zcp,zc,zho,zf] .nil .nil) .nil)))))
def tree6_lrlr:BTree (List W):=.node [ze,zi,za,znl,zc,zl,zf] tree6_lrlrl tree6_lrlrr
def tree6_lrl:BTree (List W):=.node [ze,zi,za,zhx,zc,zl,zf] tree6_lrll tree6_lrlr
def tree6_lrrll:BTree (List W):=(.node [ze,zi,za,zt,zfj,zl,zf] (.node [ze,zi,za,zqI,zc,zl,zf] (.node [ze,zi,za,znj,zc,zl,zf] (.node [ze,zi,za,zeU,zc,zl,zf] (.node [ze,zi,za,zcp,zc,zab,zf] (.node [ze,zi,za,zcp,zc,zl,zcq] .nil .nil) (.node [ze,zi,za,zcp,zR,zl,zf] .nil .nil)) (.node [ze,zi,za,zpY,zc,zl,zf] (.node [ze,zi,za,zlT,zc,zl,zf] .nil .nil) (.node [ze,zi,za,znK,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zob,zc,zl,zkp] (.node [ze,zi,za,zob,zc,zl,zdn] (.node [ze,zi,za,zob,zc,zmc,zf] .nil .nil) (.node [ze,zi,za,zob,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zob,zgz,zl,zf] (.node [ze,zi,za,zob,zc,zdm,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zn2,zc,zf] (.node [ze,zi,za,zt,zU,zc,zO] (.node [ze,zi,za,zt,zp4,zc,zf] (.node [ze,zi,za,zqb,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zU,zc,zf] .nil .nil)) (.node [ze,zi,za,zt,zop,zc,zf] (.node [ze,zi,za,zt,zU,zQ,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc9,zc0,zf] (.node [ze,zi,za,zt,ziQ,zc,zf] (.node [ze,zi,za,zt,zi8,zc,zf] .nil .nil) (.node [ze,zi,za,zt,zmo,zl,zz] .nil .nil)) (.node [ze,zi,za,zt,zc9,zc8,zf] (.node [ze,zi,za,zt,zc9,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zq9,zc,zf] (.node [ze,zi,za,zt,zc0,zc1,zf] (.node [ze,zi,za,zt,znH,zc,zf] (.node [ze,zi,za,zt,zdN,zl,zf] (.node [ze,zi,za,zt,zhP,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zao,zc,zf] .nil .nil)) (.node [ze,zi,za,zt,zc0,zc,zf] (.node [ze,zi,za,zt,zj4,zc,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zdM,zc,zf] (.node [ze,zi,za,zt,zc2,zc1,zl] (.node [ze,zi,za,zt,zqV,zc,zf] .nil .nil) (.node [ze,zi,za,zt,zgu,zc,zl] .nil .nil)) (.node [ze,zi,za,zt,zfa,zc,zf] (.node [ze,zi,za,zt,zG,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,znA,zc,zf] (.node [ze,zi,za,zt,zI,zH,zc] (.node [ze,zi,za,zt,zlp,zc,zf] (.node [ze,zi,za,zt,zi6,zc,zf] .nil .nil) (.node [ze,zi,za,zt,zle,zc,zf] .nil .nil)) (.node [ze,zi,za,zt,zI,zc,zz] (.node [ze,zi,za,zt,zI,zc,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zla,zc,zl] (.node [ze,zi,za,zt,zkm,zc,zf] (.node [ze,zi,za,zt,zi1,zc,zf] .nil .nil) (.node [ze,zi,za,zt,zny,zc,zl] .nil .nil)) (.node [ze,zi,za,zt,zH,zc,zy] (.node [ze,zi,za,zt,zH,zc,zl] .nil .nil) .nil)))))
def tree6_lrrlr:BTree (List W):=(.node [ze,zi,za,zt,zrq,zl,zf] (.node [ze,zi,za,zt,ziE,zl,zf] (.node [ze,zi,za,zt,zfI,zl,zf] (.node [ze,zi,za,zt,zbw,zl,zf] (.node [ze,zi,za,zt,zeN,zc,zl] (.node [ze,zi,za,zt,zqH,zc,zl] .nil .nil) (.node [ze,zi,za,zt,zjl,zc,zf] .nil .nil)) (.node [ze,zi,za,zt,zfu,zl,zf] (.node [ze,zi,za,zt,znz,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zjw,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zgk,zl,zf] (.node [ze,zi,za,zt,zkF,zl,zf] (.node [ze,zi,za,zt,znF,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zgk,zgb,zl] .nil .nil)) (.node [ze,zi,za,zt,zbK,zl,zf] (.node [ze,zi,za,zt,zgk,zl,zcm] .nil .nil) .nil))) (.node [ze,zi,za,zt,zh5,zl,zf] (.node [ze,zi,za,zt,zjc,zl,zf] (.node [ze,zi,za,zt,zd7,zl,zf] (.node [ze,zi,za,zt,znV,zl,zf] .nil .nil) (.node [ze,zi,za,zt,znZ,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zh4,zl,zf] (.node [ze,zi,za,zt,zq5,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zof,zl,zcq] (.node [ze,zi,za,zt,zof,zl,zcR] (.node [ze,zi,za,zt,zof,zho,zf] .nil .nil) (.node [ze,zi,za,zt,zof,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zcM,zl,zf] (.node [ze,zi,za,zt,zof,zab,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zl5,zl] (.node [ze,zi,za,zt,zc,ziv,zl] (.node [ze,zi,za,zt,zc,zkz,zl] (.node [ze,zi,za,zt,zc,zf7,zf] (.node [ze,zi,za,zt,zc,zf1,zl] .nil .nil) (.node [ze,zi,za,zt,zc,zcj,zl] .nil .nil)) (.node [ze,zi,za,zt,zc,zgb,zac] (.node [ze,zi,za,zt,zc,zgb,zl] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zlG,zl] (.node [ze,zi,za,zt,zc,zkE,zl] (.node [ze,zi,za,zt,zc,zfy,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zgI,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zmQ,zf] (.node [ze,zi,za,zt,zc,zdY,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zmT,zf] (.node [ze,zi,za,zt,zc,zjh,zl] (.node [ze,zi,za,zt,zc,zrX,zl] (.node [ze,zi,za,zt,zc,zoS,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zeX,zl] .nil .nil)) (.node [ze,zi,za,zt,zc,zoc,zl] (.node [ze,zi,za,zt,zc,zkv,zl] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zfL,zf] (.node [ze,zi,za,zt,zc,zem,zf] (.node [ze,zi,za,zt,zc,ziu,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zcF,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zd9,zgM] (.node [ze,zi,za,zt,zc,zik,zf] .nil .nil) .nil)))))
def tree6_lrrl:BTree (List W):=.node [ze,zi,za,zt,zn1,zc,zl] tree6_lrrll tree6_lrrlr
def tree6_lrrrl:BTree (List W):=(.node [ze,zi,za,zt,zc,zmc,zdn] (.node [ze,zi,za,zt,zc,zp0,zf] (.node [ze,zi,za,zt,zc,zl1,zg8] (.node [ze,zi,za,zt,zc,zgA,zf] (.node [ze,zi,za,zt,zc,zb6,zf] (.node [ze,zi,za,zt,zc,za7,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zlx,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zn9,zf] (.node [ze,zi,za,zt,zc,zkM,zf] .nil .nil) (.node [ze,zi,za,zt,zc,znv,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zpb,zf] (.node [ze,zi,za,zt,zc,zl1,zls] (.node [ze,zi,za,zt,zc,zl1,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zmC,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zpM,zf] (.node [ze,zi,za,zt,zc,zhq,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,ziB,zf] (.node [ze,zi,za,zt,zc,ze9,zbX] (.node [ze,zi,za,zt,zc,ze9,zlh] (.node [ze,zi,za,zt,zc,zeh,zf] .nil .nil) (.node [ze,zi,za,zt,zc,ze9,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zkY,zf] (.node [ze,zi,za,zt,zc,zlB,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zho,zcq] (.node [ze,zi,za,zt,zc,zho,zcR] (.node [ze,zi,za,zt,zc,zlY,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zho,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zhh,zf] (.node [ze,zi,za,zt,zc,zd8,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zl,zlq] (.node [ze,zi,za,zt,zc,zqW,zf] (.node [ze,zi,za,zt,zc,zjg,zf] (.node [ze,zi,za,zt,zc,zmc,zkp] (.node [ze,zi,za,zt,zc,zmc,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zos,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zjO,zf] (.node [ze,zi,za,zt,zc,zlw,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zgH] (.node [ze,zi,za,zt,zc,zl,zdz] (.node [ze,zi,za,zt,zc,zl,zeL] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zfJ] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zey] (.node [ze,zi,za,zt,zc,zl,znm] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zjs] (.node [ze,zi,za,zt,zc,zl,zg8] (.node [ze,zi,za,zt,zc,zl,zpC] (.node [ze,zi,za,zt,zc,zl,zdI] .nil .nil) (.node [ze,zi,za,zt,zc,zl,znB] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zpn] (.node [ze,zi,za,zt,zc,zl,zmH] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zlh] (.node [ze,zi,za,zt,zc,zl,zpX] (.node [ze,zi,za,zt,zc,zl,zdw] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zeg] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zeP] (.node [ze,zi,za,zt,zc,zl,zlM] .nil .nil) .nil)))))
def tree6_lrrrr:BTree (List W):=(.node [ze,zi,za,zt,zc,zl,zjE] (.node [ze,zi,za,zt,zc,zl,zoY] (.node [ze,zi,za,zt,zc,zl,zlE] (.node [ze,zi,za,zt,zc,zl,zhj] (.node [ze,zi,za,zt,zc,zl,zcR] (.node [ze,zi,za,zt,zc,zl,zqg] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zfv] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zoL] (.node [ze,zi,za,zt,zc,zl,zdn] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zlX] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zlv] (.node [ze,zi,za,zt,zc,zl,zox] (.node [ze,zi,za,zt,zc,zl,zqN] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zoA] (.node [ze,zi,za,zt,zc,zl,zrk] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zeK] (.node [ze,zi,za,zt,zc,zl,zqa] (.node [ze,zi,za,zt,zc,zl,znd] (.node [ze,zi,za,zt,zc,zl,zqO] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zom] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zkw] (.node [ze,zi,za,zt,zc,zl,zlF] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zqZ] (.node [ze,zi,za,zt,zc,zl,zkp] (.node [ze,zi,za,zt,zc,zl,znR] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zm9] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zjI] (.node [ze,zi,za,zt,zc,zl,zpU] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zl,zmI] (.node [ze,zi,za,zt,zc,zl,zoJ] (.node [ze,zi,za,zt,zc,zl,zrm] (.node [ze,zi,za,zt,zc,zl,zmJ] (.node [ze,zi,za,zt,zc,zl,zcq] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zen] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zpS] (.node [ze,zi,za,zt,zc,zl,znW] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zrQ] (.node [ze,zi,za,zt,zc,zl,zpm] (.node [ze,zi,za,zt,zc,zl,zbX] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zod] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zhp] (.node [ze,zi,za,zt,zc,zl,zrz] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zdL] (.node [ze,zi,za,zt,zc,zl,zhc] (.node [ze,zi,za,zt,zc,zl,ze7] (.node [ze,zi,za,zt,zc,zl,zls] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zn4] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zgM] (.node [ze,zi,za,zt,zc,zl,zeD] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zlg] (.node [ze,zi,za,zt,zc,zl,zf6] (.node [ze,zi,za,zt,zc,zl,zbD] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zaY] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zgm] (.node [ze,zi,za,zt,zc,zl,zd6] .nil .nil) .nil)))))
def tree6_lrrr:BTree (List W):=.node [ze,zi,za,zt,zc,zl,zoO] tree6_lrrrl tree6_lrrrr
def tree6_lrr:BTree (List W):=.node [ze,zi,za,zt,zc,zd9,zp] tree6_lrrl tree6_lrrr
def tree6_lr:BTree (List W):=.node [ze,zi,za,zcp,zc,zl,zf] tree6_lrl tree6_lrr
def tree6_l:BTree (List W):=.node [ze,zi,zeM,zN,zc,zl,zf] tree6_ll tree6_lr
def tree6_rllll:BTree (List W):=(.node [ze,zi,za,zt,zc,zr1,zf] (.node [ze,zi,za,zt,zc,zl,zfn] (.node [ze,zi,za,zt,zc,zl,zlZ] (.node [ze,zi,za,zt,zc,zl,zrh] (.node [ze,zi,za,zt,zc,zl,zhX] (.node [ze,zi,za,zt,zc,zl,zrS] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zfh] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zjj] (.node [ze,zi,za,zt,zc,zl,zg1] .nil .nil) (.node [ze,zi,za,zt,zc,zl,ziX] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zz] (.node [ze,zi,za,zt,zc,zl,zjB] (.node [ze,zi,za,zt,zc,zl,zpW] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zez] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zad] (.node [ze,zi,za,zt,zc,zl,z0] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zcm] (.node [ze,zi,za,zt,zc,zl,zaa] (.node [ze,zi,za,zt,zc,zl,zmd] (.node [ze,zi,za,zt,zc,zl,zjD] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zp] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zkg] (.node [ze,zi,za,zt,zc,zl,zqc] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zo4,zf] (.node [ze,zi,za,zt,zc,zl,zoF] (.node [ze,zi,za,zt,zc,zl,zL] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zO] .nil .nil)) (.node [ze,zi,za,zt,zc,zf8,zf] (.node [ze,zi,za,zt,zc,znr,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zpZ,zf] (.node [ze,zi,za,zt,zc,zg3,zf] (.node [ze,zi,za,zt,zc,zq1,zf] (.node [ze,zi,za,zt,zc,zl3,zf] (.node [ze,zi,za,zt,zc,zrM,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zgE,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,ziz,zf] (.node [ze,zi,za,zt,zc,zlz,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zdm,zkp] (.node [ze,zi,za,zt,zc,zdm,zdn] (.node [ze,zi,za,zt,zc,zk4,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zdm,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zkW,zf] (.node [ze,zi,za,zt,zc,zp9,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zqq,zf] (.node [ze,zi,za,zt,zc,zab,zf] (.node [ze,zi,za,zt,zc,zoB,zf] (.node [ze,zi,za,zt,zc,zdl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zab,zcR] .nil .nil)) (.node [ze,zi,za,zt,zc,zmM,zf] (.node [ze,zi,za,zt,zc,zab,zcq] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zpi,zf] (.node [ze,zi,za,zt,zc,zlL,zf] (.node [ze,zi,za,zt,zc,zfb,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zqr,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zhS,zf] (.node [ze,zi,za,zt,zc,zhS,zlh] .nil .nil) .nil)))))
def tree6_rlllr:BTree (List W):=(.node [ze,zi,za,zt,zc,zh9,zf] (.node [ze,zi,za,zt,zc,zke,zf] (.node [ze,zi,za,zt,zc,zc6,zf] (.node [ze,zi,za,zt,zc,zjm,zf] (.node [ze,zi,za,zt,zc,zoK,zf] (.node [ze,zi,za,zt,zc,zp2,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zpP,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,znX,zf] (.node [ze,zi,za,zt,zc,zrO,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zc6,zg8] .nil .nil))) (.node [ze,zi,za,zt,zc,zc3,zf] (.node [ze,zi,za,zt,zc,zlH,zf] (.node [ze,zi,za,zt,zc,zc6,zls] .nil .nil) (.node [ze,zi,za,zt,zc,zlP,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zke,zcv] (.node [ze,zi,za,zt,zc,zo0,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zV,zp] (.node [ze,zi,za,zt,zc,zfX,zf] (.node [ze,zi,za,zt,zc,zk1,zf] (.node [ze,zi,za,zt,zc,zke,zd] .nil .nil) (.node [ze,zi,za,zt,zc,zjL,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zV,zgM] (.node [ze,zi,za,zt,zc,zau,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zgs,zf] (.node [ze,zi,za,zt,zc,zh8,zf] (.node [ze,zi,za,zt,zc,zeY,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zdZ,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,ziq,zf] (.node [ze,zi,za,zt,zc,zrU,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zri,zf] (.node [ze,zi,za,zt,zc,zcu,zcv] (.node [ze,zi,za,zt,zc,znf,zf] (.node [ze,zi,za,zt,zc,zi3,zf] (.node [ze,zi,za,zt,zc,zjr,zf] .nil .nil) (.node [ze,zi,za,zt,zc,ziP,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zmE,zf] (.node [ze,zi,za,zt,zc,zlu,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zgt,zf] (.node [ze,zi,za,zt,zc,zcu,zd] (.node [ze,zi,za,zt,zc,zcu,zf] .nil .nil) (.node [ze,zi,za,zt,zc,z7,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zcd,zf] (.node [ze,zi,za,zt,zc,zgY,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zy,zf] (.node [ze,zi,za,zt,zc,zm3,zf] (.node [ze,zi,za,zt,zc,zfP,zf] (.node [ze,zi,za,zt,zc,zdS,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zq7,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zlD,zf] (.node [ze,zi,za,zt,zc,zb1,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zn5,zf] (.node [ze,zi,za,zt,zc,zow,zf] (.node [ze,zi,za,zt,zc,zy,zz] .nil .nil) (.node [ze,zi,za,zt,zc,zrW,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zkh,zf] (.node [ze,zi,za,zt,zc,zc8,zf] .nil .nil) .nil)))))
def tree6_rlll:BTree (List W):=.node [ze,zi,za,zt,zc,zhS,zbX] tree6_rllll tree6_rlllr
def tree6_rllrl:BTree (List W):=(.node [ze,zi,za,zt,zqP,zl,zf] (.node [ze,zi,za,zt,zc,zmU,zf] (.node [ze,zi,za,zt,zc,zo,zd] (.node [ze,zi,za,zt,zc,zcG,zf] (.node [ze,zi,za,zt,zc,zi9,zf] (.node [ze,zi,za,zt,zc,zap,zf] .nil .nil) (.node [ze,zi,za,zt,zc,ziA,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zo,zcv] (.node [ze,zi,za,zt,zc,zi0,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zo,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zh3,zf] (.node [ze,zi,za,zt,zc,z4,zf] (.node [ze,zi,za,zt,zc,zo,zbe] .nil .nil) (.node [ze,zi,za,zt,zc,zg0,zp] .nil .nil)) (.node [ze,zi,za,zt,zc,zhC,zf] (.node [ze,zi,za,zt,zc,zer,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zcy,zf] (.node [ze,zi,za,zt,zc,zcX,zf] (.node [ze,zi,za,zt,zc,zl2,zf] (.node [ze,zi,za,zt,zc,zax,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zk8,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zgB,zf] (.node [ze,zi,za,zt,zc,zg2,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zic,zl,zf] (.node [ze,zi,za,zt,znw,zl,zf] (.node [ze,zi,za,zt,zq6,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zkf,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zlo,zl,zf] (.node [ze,zi,za,zt,zpv,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zkG,zl,zf] (.node [ze,zi,za,zt,zgz,zl,zf] (.node [ze,zi,za,zt,zoZ,zl,zf] (.node [ze,zi,za,zt,zj6,zl,zf] (.node [ze,zi,za,zt,zph,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zpa,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zgz,zl,zdn] (.node [ze,zi,za,zt,zgz,zmc,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zna,zl,zf] (.node [ze,zi,za,zt,zgz,zdm,zf] (.node [ze,zi,za,zt,zgz,zl,zkp] .nil .nil) (.node [ze,zi,za,zt,znb,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zqG,zl,zf] (.node [ze,zi,za,zt,znI,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zjt,zl,zf] (.node [ze,zi,za,zt,zR,zl,zf] (.node [ze,zi,za,zt,zR,zho,zf] (.node [ze,zi,za,zt,zmt,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zR,zl,zcR] .nil .nil)) (.node [ze,zi,za,zt,zR,zab,zf] (.node [ze,zi,za,zt,zR,zl,zcq] .nil .nil) .nil)) (.node [ze,zi,za,zt,ziw,zl,zf] (.node [ze,zi,za,zt,zfM,zl,zf] (.node [ze,zi,za,zt,zje,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zgd,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,ziR,zl,zf] (.node [ze,zi,za,zt,zbx,zl,zf] .nil .nil) .nil)))))
def tree6_rllrr:BTree (List W):=(.node [ze,zi,za,zt,zro,zl,zv] (.node [ze,zi,za,zt,zpB,zl,zf] (.node [ze,zi,za,zt,zpp,zl,zf] (.node [ze,zi,za,zt,zkc,zl,zf] (.node [ze,zi,za,zt,zgb,zgn,zl] (.node [ze,zi,za,zt,zpo,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zfd,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zoT,zl,zf] (.node [ze,zi,za,zt,zlK,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zeZ,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zok,zl,zf] (.node [ze,zi,za,zt,zre,zl,zf] (.node [ze,zi,za,zt,zlO,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zfC,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zfO,zl,zf] (.node [ze,zi,za,zt,zpy,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,ziC,zl,zf] (.node [ze,zi,za,zt,zZ,zl,zf] (.node [ze,zi,za,zt,zc1,zl,z6] (.node [ze,zi,za,zt,zc1,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc1,zc8,zf] .nil .nil)) (.node [ze,zi,za,zt,ziH,zl,zf] (.node [ze,zi,za,zt,zx,zl,zz] .nil .nil) .nil)) (.node [ze,zi,za,zt,zbY,zl,zf] (.node [ze,zi,za,zt,zmk,zl,zf] (.node [ze,zi,za,zt,zf0,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zbY,zd9,zf] .nil .nil)) (.node [ze,zi,za,zt,zbY,zV,zf] (.node [ze,zi,za,zt,zbY,zl,zp] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zX,zl,zf] (.node [ze,zi,za,zt,z5,zl,zf] (.node [ze,zi,za,zt,zr,zl,zd] (.node [ze,zi,za,zt,zr,zl,zcv] (.node [ze,zi,za,zt,zpr,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zr,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zk,zl,zf] (.node [ze,zi,za,zt,zr,zo,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zgn,zl,zf] (.node [ze,zi,za,zt,zki,zl,zf] (.node [ze,zi,za,zt,zhu,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zpu,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zgn,zf,zac] (.node [ze,zi,za,zt,zgn,zl,zcm] .nil .nil) .nil))) (.node [ze,zi,za,zj0,zc,zl,zf] (.node [ze,zi,za,zks,zc,zl,zf] (.node [ze,zi,za,zkT,zc,zl,zf] (.node [ze,zi,za,zt,zQ,zl,zf] .nil .nil) (.node [ze,zi,za,zm8,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zl4,zc,zl,zf] (.node [ze,zi,za,znx,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zqy,zc,zl,zf] (.node [ze,zi,za,zqS,zc,zl,zf] (.node [ze,zi,za,zoG,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zlI,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zqd,zc,zl,zf] (.node [ze,zi,za,zqn,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rllr:BTree (List W):=.node [ze,zi,za,zt,zmW,zl,zf] tree6_rllrl tree6_rllrr
def tree6_rll:BTree (List W):=.node [ze,zi,za,zt,zc,zj5,zf] tree6_rlll tree6_rllr
def tree6_rlrll:BTree (List W):=(.node [ze,zi,za,zng,zc,zl,zf] (.node [ze,zi,za,zde,zc,zab,zf] (.node [ze,zi,za,zmj,zc,zl,zf] (.node [ze,zi,za,zjS,zc,zdm,zf] (.node [ze,zi,za,zjS,zc,zl,zf] (.node [ze,zi,za,zjS,zc,zl,zdn] .nil .nil) (.node [ze,zi,za,zjS,zc,zl,zkp] .nil .nil)) (.node [ze,zi,za,zme,zc,zl,zf] (.node [ze,zi,za,zjS,zgz,zl,zf] .nil .nil) (.node [ze,zi,za,zov,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zde,zc,zl,zcR] (.node [ze,zi,za,zde,zof,zl,zf] (.node [ze,zi,za,zrK,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zde,zc,zho,zf] .nil .nil)) (.node [ze,zi,za,zde,zc,zl,zcq] (.node [ze,zi,za,zde,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zd5,zc,zl,zlh] (.node [ze,zi,za,zlC,zc,zl,zf] (.node [ze,zi,za,zhf,zc,zl,zf] (.node [ze,zi,za,zde,zR,zl,zf] .nil .nil) (.node [ze,zi,za,zlQ,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zd5,zc,ze9,zf] (.node [ze,zi,za,zqT,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zei,zc,zl,zf] (.node [ze,zi,za,zd5,zc,zl,zbX] (.node [ze,zi,za,zd5,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zd5,zc,zhS,zf] .nil .nil)) (.node [ze,zi,za,zpk,zc,zl,zf] (.node [ze,zi,za,z1,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,ziZ,zc,zl,zf] (.node [ze,zi,za,znD,zc,zl,zf] (.node [ze,zi,za,zjf,zc,zl,zf] (.node [ze,zi,za,zaK,zc,zl,zf] (.node [ze,zi,za,zrG,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zjM,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zep,zc,zl,zf] (.node [ze,zi,za,zeb,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,ziN,zc,zl,zf] (.node [ze,zi,za,zgg,zc,zl,zf] (.node [ze,zi,za,zmP,zc,zl,zf] .nil .nil) (.node [ze,zi,za,znG,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zmb,zc,zl,zf] (.node [ze,zi,za,zjU,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zdt,zc,zl,zf] (.node [ze,zi,za,zjK,zc,zl,zf] (.node [ze,zi,za,zhG,zc,zl,zf] (.node [ze,zi,za,znp,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zix,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,ziG,zc,zl,zf] (.node [ze,zi,za,zp3,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zhE,zc,zl,zf] (.node [ze,zi,za,zbU,zc,zl,zf] (.node [ze,zi,za,zpc,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zrA,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zoW,zc,zl,zf] (.node [ze,zi,za,zhK,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rlrlr:BTree (List W):=(.node [ze,zi,za,zN,zc,zgb,zl] (.node [ze,zi,za,zja,zc,zl,zf] (.node [ze,zi,za,znY,zc,zl,zf] (.node [ze,zi,za,zaN,zc,zl,zf] (.node [ze,zi,za,zrD,zc,zl,zf] (.node [ze,zi,za,zfw,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zam,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zaR,zc,zl,zf] (.node [ze,zi,za,zoV,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zrV,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zon,zc,zl,zf] (.node [ze,zi,za,zir,zc,zl,zf] (.node [ze,zi,za,zoE,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zjF,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,znM,zc,zl,zf] (.node [ze,zi,za,zkJ,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zU,zN,zc,zf] (.node [ze,zi,za,zf5,zc,zl,zf] (.node [ze,zi,za,ziW,zc,zl,zf] (.node [ze,zi,za,zoX,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zhR,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zhg,zc,zl,zf] (.node [ze,zi,za,zjX,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zmA,zc,zl,zf] (.node [ze,zi,za,zU,zc,zbJ,zf] (.node [ze,zi,za,zU,zdK,zc,zf] .nil .nil) (.node [ze,zi,za,zgj,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zN,zgk,zl,zf] (.node [ze,zi,za,zoo,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zI,zA,zc,zf] (.node [ze,zi,za,zdH,zc,zl,zf] (.node [ze,zi,za,zN,zgn,zl,zf] (.node [ze,zi,za,zN,zc,zl,zcm] (.node [ze,zi,za,zN,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zN,zc,zf,zac] .nil .nil)) (.node [ze,zi,za,zdj,zc,zl,zf] (.node [ze,zi,za,zK,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zc9,zda,zl,zf] (.node [ze,zi,za,zbR,zc,zo,zf] (.node [ze,zi,za,zmG,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbR,zr,zl,zf] .nil .nil)) (.node [ze,zi,za,zdT,zc,zl,zf] (.node [ze,zi,za,zc0,zda,zc,zf] .nil .nil) .nil))) (.node [ze,zi,za,zA,zc,zl,zz] (.node [ze,zi,za,zrZ,zc,zl,zf] (.node [ze,zi,za,zfB,zc,zl,zf] (.node [ze,zi,za,zH,zA,zc,zl] .nil .nil) (.node [ze,zi,za,zeR,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zA,zc,zl,zf] (.node [ze,zi,za,zm4,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zaI,zc,zl,zf] (.node [ze,zi,za,zlj,zc,zl,zf] (.node [ze,zi,za,zA,zc,zy,zf] .nil .nil) (.node [ze,zi,za,zlc,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zin,zc,zl,zf] (.node [ze,zi,za,zmB,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rlrl:BTree (List W):=.node [ze,zi,za,zga,zc,zl,zf] tree6_rlrll tree6_rlrlr
def tree6_rlrrl:BTree (List W):=(.node [ze,zi,znE,zt,zc,zl,zf] (.node [ze,zi,za,zc,zrx,zl,zf] (.node [ze,zi,za,zmN,zc,zl,zf] (.node [ze,zi,za,zda,zc,zl,zf] (.node [ze,zi,za,zdP,zc,zl,zf] (.node [ze,zi,za,zhn,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zjW,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zda,zc1,zl,zf] (.node [ze,zi,za,zda,zc,zc8,zf] .nil .nil) (.node [ze,zi,za,zj8,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zdK,zbY,zl,zf] (.node [ze,zi,za,zar,zc,zl,zf] (.node [ze,zi,za,zfW,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zdK,zc,zl,zp] .nil .nil)) (.node [ze,zi,za,zc,zqD,zl,zf] (.node [ze,zi,za,zc,za0,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zc,zbJ,zl,zp] (.node [ze,zi,za,zc,zaf,zl,zf] (.node [ze,zi,za,zc,zay,zax,zf] (.node [ze,zi,za,zc,zay,zl,zf] .nil .nil) (.node [ze,zi,za,zc,zj1,zl,zf] .nil .nil)) (.node [ze,zi,za,zc,zfV,zl,zf] (.node [ze,zi,za,zc,zcY,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zrC,zt,zc,zl,zf] (.node [ze,zi,za,zay,zl,zf,zv] (.node [ze,zi,za,zc,zoR,zl,zf] .nil .nil) (.node [ze,zi,za,zr,zl,zf,zbe] .nil .nil)) (.node [ze,zi,zry,zt,zc,zl,zf] (.node [ze,zi,zpF,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zW,zt,zc,zl,zf] (.node [ze,zi,zqY,zt,zc,zl,zf] (.node [ze,zi,zjV,zt,zc,zl,zf] (.node [ze,zi,zdJ,zt,zc,zl,zf] (.node [ze,zi,zr0,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zn0,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zk3,zt,zc,zl,zf] (.node [ze,zi,zo5,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zW,zt,zof,zl,zf] (.node [ze,zi,zrJ,zt,zc,zl,zf] (.node [ze,zi,zbL,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zW,zcp,zc,zl,zf] .nil .nil)) (.node [ze,zi,zW,zt,zc,zl,zcR] (.node [ze,zi,zW,zt,zc,zho,zf] .nil .nil) .nil))) (.node [ze,zi,zrB,zt,zc,zl,zf] (.node [ze,zi,zW,zde,zc,zl,zf] (.node [ze,zi,zW,zt,zc,zab,zf] (.node [ze,zi,zW,zt,zc,zl,zcq] .nil .nil) (.node [ze,zi,zW,zt,zR,zl,zf] .nil .nil)) (.node [ze,zi,zmD,zt,zc,zl,zf] (.node [ze,zi,zlS,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zeF,zt,zc,ze9,zf] (.node [ze,zi,zeF,zkn,zc,zl,zf] (.node [ze,zi,zlA,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zeF,zt,zii,zl,zf] .nil .nil)) (.node [ze,zi,zeF,zt,zc,zl,zf] (.node [ze,zi,zeF,zt,zc,zl,zlh] .nil .nil) .nil)))))
def tree6_rlrrr:BTree (List W):=(.node [ze,zi,zcI,zt,zc,zf,zac] (.node [ze,zi,ziJ,zt,zc,zl,zf] (.node [ze,zi,zrr,zt,zc,zl,zf] (.node [ze,zi,zht,zt,zc,zl,zf] (.node [ze,zi,zeF,zt,z8,zl,zf] (.node [ze,zi,zeF,zt,zc,zhS,zf] .nil .nil) (.node [ze,zi,zeF,zd5,zc,zl,zf] .nil .nil)) (.node [ze,zi,zY,zt,zgz,zl,zf] (.node [ze,zi,zns,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zfz,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,zfH,zt,zc,zl,zf] (.node [ze,zi,zgK,zt,zc,zl,zf] (.node [ze,zi,zhN,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zby,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zqQ,zt,zc,zl,zf] (.node [ze,zi,zaO,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zp5,zt,zc,zl,zf] (.node [ze,zi,zco,zt,zc,zl,zf] (.node [ze,zi,ziD,zt,zc,zl,zf] (.node [ze,zi,zq4,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zpG,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zpg,zt,zc,zl,zf] (.node [ze,zi,zrg,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zcI,zt,zc,zgb,zl] (.node [ze,zi,zcI,zcJ,zc,zl,zf] (.node [ze,zi,zpw,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zcI,zt,zgk,zl,zf] .nil .nil)) (.node [ze,zi,zcI,zt,zc,zl,zcm] (.node [ze,zi,zcI,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zt,zU,zP,zc,zf] (.node [ze,zi,zbf,zt,zs,zc,zf] (.node [ze,zi,zbm,zt,zs,zl,zf] (.node [ze,zi,zcI,zN,zc,zl,zf] (.node [ze,zi,zcI,zt,zgn,zl,zf] .nil .nil) (.node [ze,zi,zT,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zbq,zs,zc,zl,zf] (.node [ze,zi,zbW,zt,zb2,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zbG,zs,zc,zl,zf] (.node [ze,zi,zch,zt,zc,zl,zf] (.node [ze,zi,zbP,zt,zb2,zc,zl] .nil .nil) (.node [ze,zi,zhO,zs,zc,zl,zf] .nil .nil)) (.node [ze,zi,zh,zj,zc,zl,zf] (.node [ze,zi,zca,zdK,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zt,zkA,zc,zl,zf] (.node [ze,zi,zt,zG,zc,zl,zf] (.node [ze,zi,zt,zgu,zc,zl,zf] (.node [ze,zi,zt,zk0,zc,zl,zf] .nil .nil) (.node [ze,zi,zt,zdM,zc,zl,zf] .nil .nil)) (.node [ze,zi,zt,zfB,zc,zl,zf] (.node [ze,zi,zt,zG,zx,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zt,zmu,zc,zl,zf] (.node [ze,zi,zt,zdA,zc,zl,zf] (.node [ze,zi,zt,zcQ,zc,zl,zf] .nil .nil) (.node [ze,zi,zt,zhU,zc,zl,zf] .nil .nil)) (.node [ze,zi,zt,zb2,zc,zd9,zf] (.node [ze,zi,zt,zml,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rlrr:BTree (List W):=.node [ze,zi,zeF,zt,zc,zl,zbX] tree6_rlrrl tree6_rlrrr
def tree6_rlr:BTree (List W):=.node [ze,zi,za,zqM,zc,zl,zf] tree6_rlrl tree6_rlrr
def tree6_rl:BTree (List W):=.node [ze,zi,za,zjS,zc,zmc,zf] tree6_rll tree6_rlr
def tree6_rrlll:BTree (List W):=(.node [ze,zi,zb2,zc,zbJ,zl,zf] (.node [ze,zi,zt,zc,zgR,zl,zf] (.node [ze,zi,zt,zs,zc,zl,zd] (.node [ze,zi,zt,zfA,zc,zl,z6] (.node [ze,zi,zt,zb2,zc,zV,zf] (.node [ze,zi,zt,zb2,zc,zl,zp] .nil .nil) (.node [ze,zi,zt,zb2,zbY,zl,zf] .nil .nil)) (.node [ze,zi,zt,zs,zc,zl,zcv] (.node [ze,zi,zt,zhk,zc,zl,zf] .nil .nil) (.node [ze,zi,zt,zs,zc,zl,zf] .nil .nil))) (.node [ze,zi,zt,zP,zc,zl,zf] (.node [ze,zi,zt,zs,zr,zl,zf] (.node [ze,zi,zt,zs,zc,zo,zf] .nil .nil) (.node [ze,zi,zt,zj,zc,zl,zf] .nil .nil)) (.node [ze,zi,zt,zc,za2,zl,zf] (.node [ze,zi,zt,zps,zx,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zt,zc,zu,zl,zf] (.node [ze,zi,zt,zc,zaB,zax,zf] (.node [ze,zi,zt,zc,zaB,zl,zf] (.node [ze,zi,zt,zc,znc,zl,zf] .nil .nil) (.node [ze,zi,zt,zc,zaB,zl,zv] .nil .nil)) (.node [ze,zi,zt,zc,zx,zl,zz] (.node [ze,zi,zt,zc,z9,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zt,zx,zl,zz] (.node [ze,zi,zt,zc1,zl,zf,z6] (.node [ze,zi,zt,zaB,zl,zf,zv] .nil .nil) (.node [ze,zi,zt,zx,zl,zf,zz] .nil .nil)) (.node [ze,zi,zbR,zs,zc,zl,zf] (.node [ze,zi,zt,zx,zl,z6,zv] .nil .nil) .nil)))) (.node [ze,ze8,za,zob,zc,zl,zf] (.node [ze,zhr,za,zt,zc,zl,zf] (.node [ze,zj2,za,zt,zc,zl,zf] (.node [ze,zi,zda,zc,zl,zf,z6] (.node [ze,zi,zs,zc,zl,zf,zbe] .nil .nil) (.node [ze,zi,zc,zaB,zay,zl,zf] .nil .nil)) (.node [ze,zoH,za,zt,zc,zl,zf] (.node [ze,zo7,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zrP,za,zt,zc,zl,zf] (.node [ze,zgG,za,zt,zc,zl,zf] (.node [ze,znC,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zoQ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,ze8,zgp,zt,zc,zl,zf] (.node [ze,znq,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,ze8,za,zjS,zc,zl,zf] (.node [ze,ze8,za,zt,zc,zl,zkp] (.node [ze,ze8,za,zt,zc,zl,zdn] (.node [ze,ze8,za,zt,zc,zmc,zf] .nil .nil) (.node [ze,ze8,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,ze8,za,zt,zgz,zl,zf] (.node [ze,ze8,za,zt,zc,zdm,zf] .nil .nil) .nil)) (.node [ze,zgQ,za,zt,zc,zl,zf] (.node [ze,zld,za,zt,zc,zl,zf] (.node [ze,ze8,zY,zt,zc,zl,zf] .nil .nil) (.node [ze,znJ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zqz,za,zt,zc,zl,zf] (.node [ze,zor,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rrllr:BTree (List W):=(.node [ze,znN,za,zt,zc,zl,zf] (.node [ze,zaL,za,zt,zc,zl,zf] (.node [ze,zeE,za,zt,z8,zl,zf] (.node [ze,zeE,za,zt,zc,zl,zlh] (.node [ze,zeE,za,zt,zii,zl,zf] (.node [ze,zeE,za,zkn,zc,zl,zf] .nil .nil) (.node [ze,zeE,za,zt,zc,ze9,zf] .nil .nil)) (.node [ze,zeE,za,zt,zc,zl,zbX] (.node [ze,zeE,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zeE,za,zt,zc,zhS,zf] .nil .nil))) (.node [ze,zkO,za,zt,zR,zl,zf] (.node [ze,zeE,zeF,zt,zc,zl,zf] (.node [ze,zeE,za,zd5,zc,zl,zf] .nil .nil) (.node [ze,zfx,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zdq,za,zt,zc,zl,zf] (.node [ze,zkO,zW,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zfg,za,zt,zc,zl,zf] (.node [ze,zbM,za,zt,zc,zl,zf] (.node [ze,zgq,za,zt,zc,zl,zf] (.node [ze,zl9,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zmL,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zpJ,za,zt,zc,zl,zf] (.node [ze,zl7,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zhv,za,zt,zc,zl,zf] (.node [ze,zoh,za,zt,zc,zl,zf] (.node [ze,zgD,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zeQ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zdu,za,zt,zc,zl,zf] (.node [ze,zeu,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zni,za,zt,zc,zl,zf] (.node [ze,zoU,za,zt,zc,zl,zf] (.node [ze,zkl,za,zt,zc,zl,zf] (.node [ze,zdx,za,zt,zc,zl,zf] (.node [ze,zdx,za,zca,zc,zl,zf] .nil .nil) (.node [ze,zdx,za,zbU,zc,zl,zf] .nil .nil)) (.node [ze,zbA,za,zt,zc,zl,zf] (.node [ze,zka,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zaS,za,zt,zc,zl,zf] (.node [ze,zeB,za,zt,zc,zl,zf] (.node [ze,zmr,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zaS,za,zaQ,zc,zl,zf] .nil .nil)) (.node [ze,znt,za,zt,zc,zl,zf] (.node [ze,zaS,za,zaR,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zfQ,za,zt,zc,zl,zf] (.node [ze,zol,za,zt,zc,zl,zf] (.node [ze,zfF,za,zt,zc,zl,zf] (.node [ze,zd0,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zqB,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zfQ,za,zeO,zc,zl,zf] (.node [ze,zel,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zfo,za,zt,zc,zl,zf] (.node [ze,zq3,za,zt,zc,zl,zf] (.node [ze,zfQ,za,zdK,zc,zl,zf] .nil .nil) (.node [ze,zp7,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zct,za,zt,zc,zl,zf] (.node [ze,zjQ,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rrll:BTree (List W):=.node [ze,zmR,za,zt,zc,zl,zf] tree6_rrlll tree6_rrllr
def tree6_rrlrl:BTree (List W):=(.node [ze,za,zdd,zt,zc,zc8,zf] (.node [ze,za,zE,zt,zc,zy,zf] (.node [ze,za,zne,zt,zc,zl,zf] (.node [ze,zbi,zt,zbk,zc,zl,zf] (.node [ze,zek,zE,zt,zx,zl,zf] (.node [ze,zaA,za,zt,zc,zaD,zf] .nil .nil) (.node [ze,zeM,zip,zt,zc,zl,zf] .nil .nil)) (.node [ze,zju,za,zt,zc,zl,zf] (.node [ze,zbZ,zt,zq,zc,zl,zf] .nil .nil) (.node [ze,za,zoi,zt,zc,zl,zf] .nil .nil))) (.node [ze,za,zE,zt,zH,zc,zl] (.node [ze,za,zE,zB,zc,zl,zf] (.node [ze,za,zes,zt,zc,zl,zf] .nil .nil) (.node [ze,za,zE,zt,zI,zc,zf] .nil .nil)) (.node [ze,za,zE,zt,zc,zl,zz] (.node [ze,za,zE,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,za,zdp,zt,zc,zl,zf] (.node [ze,za,zaJ,zt,zc,zl,zf] (.node [ze,za,zll,zt,zc,zl,zf] (.node [ze,za,zE,zA,zc,zl,zf] .nil .nil) (.node [ze,za,zn6,zt,zc,zl,zf] .nil .nil)) (.node [ze,za,zff,zt,zc,zl,zf] (.node [ze,za,zhA,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,za,zdd,zt,zc9,zl,zf] (.node [ze,za,zrN,zt,zc,zl,zf] (.node [ze,za,zgJ,zt,zc,zl,zf] .nil .nil) (.node [ze,za,zdd,zc7,zc,zl,zf] .nil .nil)) (.node [ze,za,zdd,zt,zc,zl,zf] (.node [ze,za,zdd,zt,zc0,zc,zf] .nil .nil) .nil)))) (.node [ze,za,zbW,zt,zq,zl,zf] (.node [ze,za,zip,zt,zU,zc,zf] (.node [ze,za,zbg,zt,zc,zl,zf] (.node [ze,za,zdd,zda,zc,zl,zf] (.node [ze,za,zdd,zt,zc1,zl,zf] .nil .nil) (.node [ze,za,zpj,zt,zc,zl,zf] .nil .nil)) (.node [ze,za,zat,zt,zc,zl,zf] (.node [ze,za,zbl,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,za,zip,zja,zc,zl,zf] (.node [ze,za,zip,zt,zgn,zl,zf] (.node [ze,za,zip,zt,zc,zl,zcm] .nil .nil) (.node [ze,za,zip,ziN,zc,zl,zf] .nil .nil)) (.node [ze,za,zbm,zt,zbk,zl,zf] (.node [ze,za,zip,zN,zc,zl,zf] .nil .nil) .nil))) (.node [ze,za,zeO,zq,zc,zl,zf] (.node [ze,za,zbP,zt,zq,zc,zl] (.node [ze,za,zbf,zt,zbk,zc,zf] (.node [ze,za,zbv,zt,zc,zl,zf] .nil .nil) (.node [ze,za,za5,zq,zc,zl,zf] .nil .nil)) (.node [ze,za,zgL,zt,zc,zl,zf] (.node [ze,za,zcn,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,za,zky,zbR,zc,zl,zf] (.node [ze,za,zb8,zq,zc,zl,zf] (.node [ze,za,zeO,z2,zc,zl,zf] .nil .nil) (.node [ze,za,zbQ,zbR,zc,zl,zf] .nil .nil)) (.node [ze,za,zoD,zbR,zc,zl,zf] (.node [ze,za,zh,zm,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rrlrr:BTree (List W):=(.node [ze,za,zt,zbk,zr,zl,zf] (.node [ze,za,zt,zbV,zc,zl,zf] (.node [ze,za,zt,zqX,zc,zl,zf] (.node [ze,za,zt,zmn,zc,zl,zf] (.node [ze,za,zt,znn,zc,zl,zf] (.node [ze,za,zt,zj7,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zqp,zc,zl,zf] .nil .nil)) (.node [ze,za,zt,zmX,zc,zl,zf] (.node [ze,za,zt,zbI,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zbt,zc,zl,zf] .nil .nil))) (.node [ze,za,zt,zU,zq,zc,zf] (.node [ze,za,zt,zpd,zc,zl,zf] (.node [ze,za,zt,ze1,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zoq,zc,zl,zf] .nil .nil)) (.node [ze,za,zt,zU,zc,zgN,zf] (.node [ze,za,zt,zU,zc,zcl,zf] .nil .nil) .nil))) (.node [ze,za,zt,zlb,zc,zl,zf] (.node [ze,za,zt,zq,zc,zl,zp] (.node [ze,za,zt,zq,zc,zd9,zf] (.node [ze,za,zt,zkZ,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zq,zc,zl,zf] .nil .nil)) (.node [ze,za,zt,zq,zbY,zl,zf] (.node [ze,za,zt,zq,zc,zV,zf] .nil .nil) .nil)) (.node [ze,za,zt,zbk,zc,zl,zf] (.node [ze,za,zt,zb0,zc,zl,zf] (.node [ze,za,zt,zaW,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zbk,zc,zl,zcv] .nil .nil)) (.node [ze,za,zt,zbk,zc,zo,zf] (.node [ze,za,zt,zbk,zc,zl,zd] .nil .nil) .nil)))) (.node [ze,za,zt,zkx,zc,zl,zf] (.node [ze,za,zt,zkQ,zc,zl,zf] (.node [ze,za,zt,z2,zc,zl,zf] (.node [ze,za,zt,zbn,zc,zl,zf] (.node [ze,za,zt,zcZ,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zm,zc,zl,zf] .nil .nil)) (.node [ze,za,zt,zf4,zc,zl,zf] (.node [ze,za,zt,znT,zc,zl,zf] .nil .nil) .nil)) (.node [ze,za,zt,zbR,zR,zl,zf] (.node [ze,za,zt,zbR,zc,zl,zcq] (.node [ze,za,zt,zpK,zc,zl,zf] .nil .nil) (.node [ze,za,zt,zbR,zc,zab,zf] .nil .nil)) (.node [ze,za,zt,ze4,zc,zl,zf] (.node [ze,za,zt,zdU,zc,zl,zf] .nil .nil) .nil))) (.node [ze,za,zt,zc,zq0,zl,zf] (.node [ze,za,zt,zc,zmV,zl,zf] (.node [ze,za,zt,zc,zk6,zab,zf] (.node [ze,za,zt,zgk,zcl,zl,zf] .nil .nil) (.node [ze,za,zt,zc,zk6,zpQ,zf] .nil .nil)) (.node [ze,za,zt,zc,zpz,zl,zf] (.node [ze,za,zt,zc,zot,zl,zf] .nil .nil) .nil)) (.node [ze,za,zt,zc,zf1,zl,zf] (.node [ze,za,zt,zc,zk9,zl,zf] (.node [ze,za,zt,zc,zoy,zl,zf] .nil .nil) (.node [ze,za,zt,zc,zeH,zl,zf] .nil .nil)) (.node [ze,za,zt,zc,zhu,zl,zf] (.node [ze,za,zt,zc,zf7,zl,zf] .nil .nil) .nil)))))
def tree6_rrlr:BTree (List W):=.node [ze,za,zcp,zbR,zc,zl,zf] tree6_rrlrl tree6_rrlrr
def tree6_rrl:BTree (List W):=.node [ze,zq8,za,zt,zc,zl,zf] tree6_rrll tree6_rrlr
def tree6_rrrll:BTree (List W):=(.node [zD,zi,za,zt,zc,zl,zf] (.node [ze,za,zN,zc,zcl,zl,zf] (.node [ze,za,zt,zc,zcl,zl,zcm] (.node [ze,za,zt,zc,zoM,zl,zf] (.node [ze,za,zt,zc,zaD,zl,zf] (.node [ze,za,zt,zc,zko,zl,zf] .nil .nil) (.node [ze,za,zt,zc,zaD,zax,zf] .nil .nil)) (.node [ze,za,zt,zc,zhd,zl,zf] (.node [ze,za,zt,zc,zqA,zl,zf] .nil .nil) (.node [ze,za,zt,zc,zbb,zl,zf] .nil .nil))) (.node [ze,za,ziN,zc,zcl,zl,zf] (.node [ze,za,zt,zc,zcB,zl,zf] (.node [ze,za,zt,zc,zd3,zl,zf] .nil .nil) (.node [ze,za,zt,zR,zk6,zl,zf] .nil .nil)) (.node [ze,za,zbI,zc,zbJ,zl,zf] (.node [ze,za,zga,zc,zcl,zl,zf] .nil .nil) .nil))) (.node [ze,za,zc,zay,zaD,zl,zf] (.node [ze,za,zq,zc,zl,zg0,zf] (.node [ze,za,zq,zdK,zc,zl,zf] (.node [ze,za,zN,zc,zl,zgN,zf] .nil .nil) (.node [ze,za,zq,zc,zbJ,zl,zf] .nil .nil)) (.node [ze,za,z2,zc,zbJ,zl,zf] (.node [ze,za,z2,zdK,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zt,zq,zb2,zc,zl,zf] (.node [ze,zW,zt,zc,zk6,zl,zf] (.node [ze,zW,zt,zbR,zc,zl,zf] .nil .nil) (.node [ze,zcI,zt,zc,zcl,zl,zf] .nil .nil)) (.node [ze,zt,zc,zaB,zaD,zl,zf] (.node [ze,zt,zbk,zs,zc,zl,zf] .nil .nil) .nil)))) (.node [zqL,zi,za,zt,zc,zl,zf] (.node [zo8,zi,za,zt,zc,zl,zf] (.node [zce,zM,zi,za,zt,zc,zf] (.node [zqv,zi,za,zt,zc,zl,zf] (.node [zbO,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zgi,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zg5,zi,za,zt,zc,zl,zf] (.node [zce,zi,za,zt,zc,zak,zf] .nil .nil) .nil)) (.node [zbC,zi,za,zt,zc,zl,zf] (.node [zex,zi,za,zt,zc,zl,zf] (.node [zkb,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zqU,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zhH,zi,za,zt,zc,zl,zf] (.node [zgw,zM,zi,za,zt,zc,zf] .nil .nil) .nil))) (.node [zjo,zi,za,zt,zc,zl,zf] (.node [zhI,zi,za,zt,zc,zl,zf] (.node [zfT,zi,za,zt,zc,zak,zl] (.node [zfT,zi,za,zt,zc,zcc,zl] .nil .nil) (.node [zrL,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zb3,za,zcb,zt,zc,zl,zf] (.node [zbj,za,zbp,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ziY,zi,za,zt,zc,zl,zf] (.node [zdb,zdi,za,zt,zc,zl,zf] (.node [zi7,zM,za,zt,zc,zl,zf] .nil .nil) (.node [zea,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zfN,zi,za,zt,zc,zl,zf] (.node [zfE,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rrrlr:BTree (List W):=(.node [zM,za,zip,zt,zc,zl,zf] (.node [zM,zgZ,za,zt,zc,zl,zf] (.node [zck,zi,za,zcb,zc,zl,zf] (.node [ze5,zi,za,zt,zc,zl,zf] (.node [zeG,zi,zF,zt,zc,zl,zf] (.node [znh,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zaz,zi,zt,zaF,zc,zl,zf] .nil .nil)) (.node [zcw,zi,za,zt,zc,zl,zf] (.node [zrF,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zrs,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zg,zM,za,zt,zc,zl,zf] (.node [zpf,zi,za,zt,zc,zl,zf] (.node [zaw,zi,za,zaF,zc,zl,zf] .nil .nil) (.node [zhl,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zg,za,zt,zc,zl,zf,zd] (.node [zg,zkO,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zM,zi,za,zt,zc,zl,zf] (.node [zM,zi,za,zt,zgk,zl,zf] (.node [zM,zi,za,zcJ,zc,zl,zf] (.node [zM,zi,zeM,zt,zc,zl,zf] .nil .nil) (.node [zM,zi,za,zbG,zt,zc,zf] .nil .nil)) (.node [zM,zi,za,zt,zc,zgb,zl] (.node [zM,zi,za,zt,zc,zk6,zf] .nil .nil) .nil)) (.node [zM,zi,za,zt,zgn,zl,zf] (.node [zM,zi,za,zt,zc,zgN,zf] (.node [zM,zi,za,zt,zc,zl,zcm] .nil .nil) (.node [zM,zi,za,zt,zc,zf,zac] .nil .nil)) (.node [zM,zi,zcI,zt,zc,zl,zf] (.node [zM,zi,za,zN,zc,zl,zf] .nil .nil) .nil)))) (.node [zi,zfl,za,zt,zc,zl,zf] (.node [zi,zgQ,za,zt,zc,zl,zf] (.node [zC,zF,za,zt,zc,zl,zf] (.node [zfS,zi,za,zt,zc,zcc,zf] (.node [zM,za,zt,zc,zcl,zl,zf] .nil .nil) (.node [zaC,za,zt,zaF,zc,zl,zf] .nil .nil)) (.node [zgP,za,zt,zc,zqF,zl,zf] (.node [zgP,zgQ,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zi,zfi,za,zt,zaF,zc,zl] (.node [zi,zaH,za,zt,zc,zl,zf] (.node [zi,zkO,za,zt,zc,zab,zf] .nil .nil) (.node [zi,zaA,za,zt,zaF,zc,zf] .nil .nil)) (.node [zi,zi4,za,zt,zc,zl,zf] (.node [zi,zeA,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zi,zF,za,zt,zc,zl,zf] (.node [zi,zF,za,zt,zmo,zl,zf] (.node [zi,zek,zF,zt,zx,zl,zf] (.node [zi,zm7,za,zt,zc,zl,zf] .nil .nil) (.node [zi,zF,za,zB,zc,zl,zf] .nil .nil)) (.node [zi,zF,za,zt,zH,zc,zl] (.node [zi,zF,za,zt,zI,zc,zf] .nil .nil) .nil)) (.node [zi,zF,za,zA,zc,zl,zf] (.node [zi,zF,za,zt,zc,zy,zf] (.node [zi,zF,za,zt,zc,zl,zz] .nil .nil) (.node [zi,zF,za,zt,zx,zl,zf] .nil .nil)) (.node [zi,zF,zt,zx,zl,zf] (.node [zi,zF,zt,zc,zx,zl,zf] .nil .nil) .nil)))))
def tree6_rrrl:BTree (List W):=.node [zoI,zi,za,zt,zc,zl,zf] tree6_rrrll tree6_rrrlr
def tree6_rrrrl:BTree (List W):=(.node [zi,za,zh1,zt,zc,zl,zf] (.node [zi,zw,za,zt,zc,zl,zf] (.node [zi,zdi,za,zt,zc0,zc,zf] (.node [zi,zdQ,za,zt,zc,zl,zf] (.node [zi,zbi,zbp,zt,zc,zl,zf] (.node [zi,zlt,za,zt,zc,zl,zf] .nil .nil) (.node [zi,zbZ,zcb,zt,zc,zl,zf] .nil .nil)) (.node [zi,zdi,za,zc7,zc,zl,zf] (.node [zi,zpT,zY,zt,zc,zl,zf] .nil .nil) (.node [zi,zdi,za,zt,zc9,zl,zf] .nil .nil))) (.node [zi,zdi,za,zt,zc,zc8,zf] (.node [zi,zdi,za,zt,zc,zl,zf] (.node [zi,zdi,za,zt,zc2,zc,zl] .nil .nil) (.node [zi,zdi,za,zt,zc,zl,z6] .nil .nil)) (.node [zi,zdi,za,zda,zc,zl,zf] (.node [zi,zdi,za,zt,zc1,zl,zf] .nil .nil) .nil))) (.node [zi,za,zbW,zcb,zt,zl,zf] (.node [zi,za,zY,zt,zgz,zl,zf] (.node [zi,za,zns,zt,zc,zl,zf] (.node [zi,zgp,zns,zt,zc,zl,zf] .nil .nil) (.node [zi,za,zY,zt,zc,zl,zkp] .nil .nil)) (.node [zi,za,zbm,zbp,zt,zl,zf] (.node [zi,za,znk,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zi,za,zbP,zcb,zt,zc,zl] (.node [zi,za,zbr,zt,zc,zl,zf] (.node [zi,za,zid,zt,zc,zl,zf] .nil .nil) (.node [zi,za,zbf,zbp,zt,zc,zf] .nil .nil)) (.node [zi,za,zqx,zt,zc,zl,zf] (.node [zi,za,zgC,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [zi,za,zbp,zt,zc,zl,zf] (.node [zi,za,zlN,zt,zc,zV,zf] (.node [zi,za,ze2,zt,zc,zl,zf] (.node [zi,za,zhO,zbp,zc,zl,zf] (.node [zi,za,zhV,zt,zc,zl,zf] .nil .nil) (.node [zi,za,ze6,zt,zc,zl,zf] .nil .nil)) (.node [zi,za,zb7,zt,zc,zl,zf] (.node [zi,za,zeO,zcb,zc,zl,zf] .nil .nil) .nil)) (.node [zi,za,zcb,zdK,zc,zl,zf] (.node [zi,za,zcb,zt,zc,zl,zp] (.node [zi,za,zcb,zt,zc,zl,zf] .nil .nil) (.node [zi,za,zcb,zt,zbY,zl,zf] .nil .nil)) (.node [zi,za,zm2,zt,zc,zl,zd] (.node [zi,za,zcb,zc,zbJ,zl,zf] .nil .nil) .nil))) (.node [zi,za,zt,z1,zc,zl,zf] (.node [zi,za,zh,zn,zc,zl,zf] (.node [zi,za,zbp,zt,zr,zl,zf] (.node [zi,za,zbp,zt,zc,zo,zf] .nil .nil) (.node [zi,za,zbp,zbR,zc,zl,zf] .nil .nil)) (.node [zi,za,zgX,z1,zc,zl,zf] (.node [zi,za,zn,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zi,za,zt,zjb,zc,zl,zf] (.node [zi,za,zt,zS,zc,zl,zf] (.node [zi,za,zt,zU,zS,zc,zf] .nil .nil) (.node [zi,za,zt,zjq,zc,zl,zf] .nil .nil)) (.node [zi,za,zt,zfr,zc,zl,zf] (.node [zi,za,zt,zgO,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rrrrr:BTree (List W):=(.node [zi,za,zt,zc,zl,zV,zls] (.node [zi,za,zt,zc,zgU,zl,zf] (.node [zi,za,zt,zh5,zc,zl,zf] (.node [zi,za,zt,zaF,zc,zl,zv] (.node [zi,za,zt,zpN,z8,zl,zf] (.node [zi,za,zt,zgV,zc,zl,zf] .nil .nil) (.node [zi,za,zt,zaF,zc,zl,zf] .nil .nil)) (.node [zi,za,zt,zJ,zc,zl,zf] (.node [zi,za,zt,zaF,zc,zax,zf] .nil .nil) (.node [zi,za,zt,zii,zh5,zl,zf] .nil .nil))) (.node [zi,za,zt,zc,zcc,zl,zf] (.node [zi,za,zt,zc,zf2,zl,zf] (.node [zi,za,zt,zc,z8,zl,zbX] .nil .nil) (.node [zi,za,zt,zc,zpD,zl,zd] .nil .nil)) (.node [zi,za,zt,zc,zcc,zcu,zf] (.node [zi,za,zt,zc,zcc,zl,zac] .nil .nil) .nil))) (.node [zi,za,zt,zc,zak,zl,zac] (.node [zi,za,zt,zc,zqR,zl,zf] (.node [zi,za,zt,zc,zo9,zl,zf] (.node [zi,za,zt,zc,zd4,zl,zf] .nil .nil) (.node [zi,za,zt,zc,zcD,zl,zf] .nil .nil)) (.node [zi,za,zt,zc,zak,zl,zf] (.node [zi,za,zt,zc,zrY,zl,zf] .nil .nil) .nil)) (.node [zi,za,zt,zc,zd9,zn9,zf] (.node [zi,za,zt,zc,za9,zl,zf] (.node [zi,za,zt,zc,zak,zf,zac] .nil .nil) (.node [zi,za,zt,zc,zl0,zl,zf] .nil .nil)) (.node [zi,za,zt,zc,zl1,zV,zf] (.node [zi,za,zt,zc,zn9,zl,zf] .nil .nil) .nil)))) (.node [zi,za,zt,zR,zl,zf,zd] (.node [zi,za,zt,zc,zl,zgH,zf] (.node [zi,za,zt,zc,zl,zej,zf] (.node [zi,za,zt,zc,zl,zqj,zf] (.node [zi,za,zt,zc,zl,zV,zgM] .nil .nil) (.node [zi,za,zt,zc,zl,zb5,zf] .nil .nil)) (.node [zi,za,zt,zc,zl,zcv,zgH] (.node [zi,za,zt,zc,zl,zaU,zf] .nil .nil) .nil)) (.node [zi,za,zt,zc,zc6,zf,zd] (.node [zi,za,zt,zc,zl,zcR,zd] (.node [zi,za,zt,zc,zl,zg8,zd] .nil .nil) (.node [zi,za,zt,zc,zab,zf,zd] .nil .nil)) (.node [zi,za,zt,zc,zV,zd,zac] (.node [zi,za,zt,zc,zke,zf,zd] .nil .nil) .nil))) (.node [zi,zbp,zt,zs,zc,zl,zf] (.node [zi,zeF,zt,zc,z8,zl,zf] (.node [zi,za,zaF,zc,zay,zl,zf] (.node [zi,za,zde,zc,zl,zf,zd] .nil .nil) (.node [zi,zW,zt,zc,zl,zf,zd] .nil .nil)) (.node [zi,zcb,zt,zb2,zc,zl,zf] (.node [zi,zY,zt,z8,zx,zl,zf] .nil .nil) .nil)) (.node [za,zcb,zt,zq,zc,zl,zf] (.node [zF,za,zE,zt,zc,zl,zf] (.node [zi,zt,zaF,zc,zaB,zl,zf] .nil .nil) (.node [zdi,za,zdd,zt,zc,zl,zf] .nil .nil)) (.node [za,zt,zaF,zc,zaD,zl,zf] (.node [za,zbp,zt,zbk,zc,zl,zf] .nil .nil) .nil)))))
def tree6_rrrr:BTree (List W):=.node [zi,za,zt,za4,zc,zl,zf] tree6_rrrrl tree6_rrrrr
def tree6_rrr:BTree (List W):=.node [zi,ziT,za,zt,zc,zl,zf] tree6_rrrl tree6_rrrr
def tree6_rr:BTree (List W):=.node [ze,za,zt,zc,zgr,zl,zf] tree6_rrl tree6_rrr
def tree6_r:BTree (List W):=.node [ze,zi,zt,zb2,zc,zl,zf] tree6_rl tree6_rr
def tree6:BTree (List W):=.node [ze,zi,za,zt,zc,zl,zhb] tree6_l tree6_r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lllll:everyKey (certRow 5 tree5) tree6_lllll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llllr:everyKey (certRow 5 tree5) tree6_llllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llll:everyKey (certRow 5 tree5) tree6_llll=true:=splitCheck (by decide +kernel) ok_tree6_lllll ok_tree6_llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lllrl:everyKey (certRow 5 tree5) tree6_lllrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lllrr:everyKey (certRow 5 tree5) tree6_lllrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lllr:everyKey (certRow 5 tree5) tree6_lllr=true:=splitCheck (by decide +kernel) ok_tree6_lllrl ok_tree6_lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lll:everyKey (certRow 5 tree5) tree6_lll=true:=splitCheck (by decide +kernel) ok_tree6_llll ok_tree6_lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llrll:everyKey (certRow 5 tree5) tree6_llrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llrlr:everyKey (certRow 5 tree5) tree6_llrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llrl:everyKey (certRow 5 tree5) tree6_llrl=true:=splitCheck (by decide +kernel) ok_tree6_llrll ok_tree6_llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llrrl:everyKey (certRow 5 tree5) tree6_llrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llrrr:everyKey (certRow 5 tree5) tree6_llrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llrr:everyKey (certRow 5 tree5) tree6_llrr=true:=splitCheck (by decide +kernel) ok_tree6_llrrl ok_tree6_llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_llr:everyKey (certRow 5 tree5) tree6_llr=true:=splitCheck (by decide +kernel) ok_tree6_llrl ok_tree6_llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_ll:everyKey (certRow 5 tree5) tree6_ll=true:=splitCheck (by decide +kernel) ok_tree6_lll ok_tree6_llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrlll:everyKey (certRow 5 tree5) tree6_lrlll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrllr:everyKey (certRow 5 tree5) tree6_lrllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrll:everyKey (certRow 5 tree5) tree6_lrll=true:=splitCheck (by decide +kernel) ok_tree6_lrlll ok_tree6_lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrlrl:everyKey (certRow 5 tree5) tree6_lrlrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrlrr:everyKey (certRow 5 tree5) tree6_lrlrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrlr:everyKey (certRow 5 tree5) tree6_lrlr=true:=splitCheck (by decide +kernel) ok_tree6_lrlrl ok_tree6_lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrl:everyKey (certRow 5 tree5) tree6_lrl=true:=splitCheck (by decide +kernel) ok_tree6_lrll ok_tree6_lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrrll:everyKey (certRow 5 tree5) tree6_lrrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrrlr:everyKey (certRow 5 tree5) tree6_lrrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrrl:everyKey (certRow 5 tree5) tree6_lrrl=true:=splitCheck (by decide +kernel) ok_tree6_lrrll ok_tree6_lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrrrl:everyKey (certRow 5 tree5) tree6_lrrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrrrr:everyKey (certRow 5 tree5) tree6_lrrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrrr:everyKey (certRow 5 tree5) tree6_lrrr=true:=splitCheck (by decide +kernel) ok_tree6_lrrrl ok_tree6_lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lrr:everyKey (certRow 5 tree5) tree6_lrr=true:=splitCheck (by decide +kernel) ok_tree6_lrrl ok_tree6_lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_lr:everyKey (certRow 5 tree5) tree6_lr=true:=splitCheck (by decide +kernel) ok_tree6_lrl ok_tree6_lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_l:everyKey (certRow 5 tree5) tree6_l=true:=splitCheck (by decide +kernel) ok_tree6_ll ok_tree6_lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rllll:everyKey (certRow 5 tree5) tree6_rllll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlllr:everyKey (certRow 5 tree5) tree6_rlllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlll:everyKey (certRow 5 tree5) tree6_rlll=true:=splitCheck (by decide +kernel) ok_tree6_rllll ok_tree6_rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rllrl:everyKey (certRow 5 tree5) tree6_rllrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rllrr:everyKey (certRow 5 tree5) tree6_rllrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rllr:everyKey (certRow 5 tree5) tree6_rllr=true:=splitCheck (by decide +kernel) ok_tree6_rllrl ok_tree6_rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rll:everyKey (certRow 5 tree5) tree6_rll=true:=splitCheck (by decide +kernel) ok_tree6_rlll ok_tree6_rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlrll:everyKey (certRow 5 tree5) tree6_rlrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlrlr:everyKey (certRow 5 tree5) tree6_rlrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlrl:everyKey (certRow 5 tree5) tree6_rlrl=true:=splitCheck (by decide +kernel) ok_tree6_rlrll ok_tree6_rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlrrl:everyKey (certRow 5 tree5) tree6_rlrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlrrr:everyKey (certRow 5 tree5) tree6_rlrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlrr:everyKey (certRow 5 tree5) tree6_rlrr=true:=splitCheck (by decide +kernel) ok_tree6_rlrrl ok_tree6_rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rlr:everyKey (certRow 5 tree5) tree6_rlr=true:=splitCheck (by decide +kernel) ok_tree6_rlrl ok_tree6_rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rl:everyKey (certRow 5 tree5) tree6_rl=true:=splitCheck (by decide +kernel) ok_tree6_rll ok_tree6_rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrlll:everyKey (certRow 5 tree5) tree6_rrlll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrllr:everyKey (certRow 5 tree5) tree6_rrllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrll:everyKey (certRow 5 tree5) tree6_rrll=true:=splitCheck (by decide +kernel) ok_tree6_rrlll ok_tree6_rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrlrl:everyKey (certRow 5 tree5) tree6_rrlrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrlrr:everyKey (certRow 5 tree5) tree6_rrlrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrlr:everyKey (certRow 5 tree5) tree6_rrlr=true:=splitCheck (by decide +kernel) ok_tree6_rrlrl ok_tree6_rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrl:everyKey (certRow 5 tree5) tree6_rrl=true:=splitCheck (by decide +kernel) ok_tree6_rrll ok_tree6_rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrrll:everyKey (certRow 5 tree5) tree6_rrrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrrlr:everyKey (certRow 5 tree5) tree6_rrrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrrl:everyKey (certRow 5 tree5) tree6_rrrl=true:=splitCheck (by decide +kernel) ok_tree6_rrrll ok_tree6_rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrrrl:everyKey (certRow 5 tree5) tree6_rrrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrrrr:everyKey (certRow 5 tree5) tree6_rrrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrrr:everyKey (certRow 5 tree5) tree6_rrrr=true:=splitCheck (by decide +kernel) ok_tree6_rrrrl ok_tree6_rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rrr:everyKey (certRow 5 tree5) tree6_rrr=true:=splitCheck (by decide +kernel) ok_tree6_rrrl ok_tree6_rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_rr:everyKey (certRow 5 tree5) tree6_rr=true:=splitCheck (by decide +kernel) ok_tree6_rrl ok_tree6_rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6_r:everyKey (certRow 5 tree5) tree6_r=true:=splitCheck (by decide +kernel) ok_tree6_rl ok_tree6_rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree6:everyKey (certRow 5 tree5) tree6=true:=splitCheck (by decide +kernel) ok_tree6_l ok_tree6_r

def tree7_lllll:BTree (List W):=(.node [zc5,zi,za,zt,zc,zl,zcv] (.node [zGW,ze,zi,za,zt,zc,zl,zf] (.node [zEv,ze,zi,za,zt,zc,zl,zf] (.node [zE2,ze,zi,za,zt,zc,zl,zf] (.node [zCy,ze,zi,za,zt,zc,zl,zf] (.node [zGb,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zGf,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zuX,ze,zi,za,zt,zc,zl,zf] (.node [zHr,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zC1,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zCv,ze,zi,za,zt,zc,zl,zf] (.node [zC2,ze,zi,za,zt,zc,zl,zf] (.node [zHo,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zzS,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zv7,ze,zi,za,zt,zc,zl,zf] (.node [zD8,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zc5,ze,zi,za,zt,zc,zl,zf] (.node [zc5,zmw,zi,za,zt,zc,zl,zf] (.node [zc5,zmp,zi,za,zt,zc,zl,zf] (.node [zc5,zkt,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zc5,zkR,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zc5,zza,zi,za,zt,zc,zl,zf] (.node [zc5,zg9,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zc5,ze,zi,za,zt,zc,zl,zcv] .nil .nil))) (.node [zc5,zi,za,zt,zz5,zc,zl,zf] (.node [zc5,zgP,zi,za,zt,zc,zl,zf] (.node [zc5,ze,zi,za,zt,zc,zl,zd] .nil .nil) (.node [zc5,zi,za,zY,zt,zc,zl,zf] .nil .nil)) (.node [zc5,zi,za,zt,zc,zl,zV,zf] (.node [zc5,zi,za,zt,zc,z8,zl,zf] .nil .nil) .nil)))) (.node [zkt,ze,zi,za,zt,zc,zl,zf] (.node [zEh,ze,zi,za,zt,zc,zl,zf] (.node [zHn,ze,zi,za,zt,zc,zl,zf] (.node [zGp,ze,zi,za,zt,zc,zl,zf] (.node [zc5,zi,za,zt,zc,zl,zcv,zf] .nil .nil) (.node [zAK,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zEV,ze,zi,za,zt,zc,zl,zf] (.node [zEi,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zGt,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zkt,zmw,zi,za,zt,zc,zl,zf] (.node [zz2,ze,zi,za,zt,zc,zl,zf] (.node [zFm,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zkt,zcC,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zkt,ze,zi,za,zt,zc,zd9,zf] (.node [zkt,ztL,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zkN,ze,zi,za,zt,zc,zl,zf] (.node [zkt,zi,za,zt,zc,zd9,zl,zf] (.node [zkt,zi,zkO,za,zt,zc,zl,zf] (.node [zkt,ze,zi,za,zt,zc,zV,zf] .nil .nil) (.node [zkt,zi,za,zt,zz5,zc,zl,zf] .nil .nil)) (.node [zkt,zi,za,zt,zc,zl,zf,zd] (.node [zkt,zi,za,zt,zc,zd9,zf] .nil .nil) .nil)) (.node [zEw,ze,zi,za,zt,zc,zl,zf] (.node [zkN,zi,za,zt,zc,zl,zf] (.node [zkN,zi,za,zt,zc,zsg,zl,zf] .nil .nil) (.node [zE8,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zDy,ze,zi,za,zt,zc,zl,zf] (.node [zGc,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_llllr:BTree (List W):=(.node [zFQ,ze,zi,za,zt,zc,zl,zf] (.node [zkk,ze,zi,za,zt,zc,zl,zf] (.node [zzV,ze,zi,za,zt,zc,zdm,zf] (.node [zzV,ze,zi,za,zt,zc,zmc,zf] (.node [zzV,ze,zi,zgp,zt,zc,zl,zf] (.node [zzV,ze,zjn,za,zt,zc,zl,zf] .nil .nil) (.node [zzV,ze,zi,za,zob,zc,zl,zf] .nil .nil)) (.node [zzV,ze,zi,za,zt,zc,zl,zf] (.node [zzV,ze,zi,za,zt,zc,zl,zdn] .nil .nil) (.node [zzV,ze,zi,za,zt,zc,zl,zkp] .nil .nil))) (.node [zzV,ze,ze8,za,zt,zc,zl,zf] (.node [zzV,ze,zi,za,zjS,zc,zl,zf] (.node [zzV,ze,zi,za,zt,zgz,zl,zf] .nil .nil) (.node [zzV,ze,zi,zY,zt,zc,zl,zf] .nil .nil)) (.node [zjT,ze,zi,za,zt,zc,zl,zf] (.node [zzV,zi,za,zY,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zt5,ze,zi,za,zt,zc,zl,zf] (.node [zvF,ze,zi,za,zt,zc,zl,zf] (.node [zFp,ze,zi,za,zt,zc,zl,zf] (.node [zBN,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zDd,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zt5,zmw,zi,za,zt,zc,zl,zf] (.node [zDO,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zt5,ze,zi,za,zgX,zc,zl,zf] .nil .nil))) (.node [zwI,ze,zi,za,zt,zc,zl,zf] (.node [zt5,zi,za,zt,zz5,zc,zl,zf] (.node [zt5,ze,zi,za,zz5,zc,zl,zf] .nil .nil) (.node [ztf,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zwK,ze,zi,za,zt,zc,zl,zf] (.node [zAd,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [zmp,ze,zi,za,zt,zc,zl,zcq] (.node [zmp,ze,zgP,za,zt,zc,zl,zf] (.node [zE7,ze,zi,za,zt,zc,zl,zf] (.node [zHx,ze,zi,za,zt,zc,zl,zf] (.node [zEE,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zD6,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zmp,ze,zjP,za,zt,zc,zl,zf] (.node [zmp,zcC,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zmp,ze,zc4,za,zt,zc,zl,zf] .nil .nil))) (.node [zmp,ze,zi,za,zt,zc,zho,zf] (.node [zmp,ze,zi,za,zcp,zc,zl,zf] (.node [zmp,ze,zi,zkB,zt,zc,zl,zf] .nil .nil) (.node [zmp,ze,zi,za,zt,zof,zl,zf] .nil .nil)) (.node [zmp,ze,zi,za,zt,zc,zl,zf] (.node [zmp,ze,zi,za,zt,zc,zl,zcR] .nil .nil) .nil))) (.node [zmp,ze,za,zt,zc,zk6,zl,zf] (.node [zmp,ze,zi,zW,zt,zc,zl,zf] (.node [zmp,ze,zi,za,zt,zR,zl,zf] (.node [zmp,ze,zi,za,zt,zc,zab,zf] .nil .nil) (.node [zmp,ze,zi,za,zde,zc,zl,zf] .nil .nil)) (.node [zmp,ze,za,zt,zbR,zc,zl,zf] (.node [zmp,ze,zkO,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zfR,zi,za,zt,zc,zwU,zl,zf] (.node [zmp,zi,za,zt,zc,zl,zf,zd] (.node [zmp,zi,zkO,za,zt,zc,zl,zf] .nil .nil) (.node [zfR,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zhL,ze,zi,za,zt,zc,zl,zf] (.node [zfR,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_llll:BTree (List W):=.node [zzV,zg9,zi,za,zt,zc,zl,zf] tree7_lllll tree7_llllr
def tree7_lllrl:BTree (List W):=(.node [ztR,ze,zi,za,zt,zc,zl,zf] (.node [zCx,ze,zi,za,zt,zc,zl,zf] (.node [zkR,ze,zi,za,zt,zii,zl,zf] (.node [zGP,ze,zi,za,zt,zc,zl,zf] (.node [zyS,ze,zi,za,zt,zc,zl,zf] (.node [zAM,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zCf,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zkR,ztR,zi,za,zt,zc,zl,zf] (.node [zEf,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zkR,zg9,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zkR,zi,za,zt,zii,zc,zl,zf] (.node [zkR,ze,zi,za,zt,z8,zl,zf] (.node [zkR,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zkR,zi,za,zY,zt,zc,zl,zf] .nil .nil)) (.node [zkR,zi,za,zt,zc,zl,zf,zd] (.node [zkR,zi,za,zt,zii,zl,zf] .nil .nil) .nil))) (.node [zB4,ze,zi,za,zt,zc,zl,zf] (.node [zaE,zi,za,zt,zc,zl,zf] (.node [zaE,ze,zi,za,zt,zc,zl,zf] (.node [zih,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zaE,zi,za,zt,zsH,zc,zl,zf] .nil .nil)) (.node [zvD,ze,zi,za,zt,zc,zl,zf] (.node [ztb,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zCM,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ztR,ze,zi,za,zt,zii,zl,zf] (.node [ztR,ze,zjJ,za,zt,zc,zl,zf] (.node [zE6,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ztR,ze,zi,za,zkn,zc,zl,zf] .nil .nil)) (.node [ztR,ze,zi,za,zt,zc,zl,zlh] (.node [ztR,ze,zi,za,zt,zc,ze9,zf] .nil .nil) .nil)))) (.node [zDM,ze,zi,za,zt,zc,zl,zf] (.node [zrT,ze,zi,za,zt,zc,zl,zf] (.node [ztR,ze,zi,za,zd5,zc,zl,zf] (.node [ztR,ze,zi,za,zt,zc,zhS,zf] (.node [ztR,ze,zi,za,zt,zc,zl,zbX] .nil .nil) (.node [ztR,ze,zi,za,zt,z8,zl,zf] .nil .nil)) (.node [ztR,ze,zeE,za,zt,zc,zl,zf] (.node [ztR,ze,zi,zeF,zt,zc,zl,zf] .nil .nil) (.node [ztR,zi,za,zt,zc,z8,zl,zf] .nil .nil))) (.node [zGK,ze,zi,za,zt,zc,zl,zf] (.node [zv4,ze,zi,za,zt,zc,zl,zf] (.node [zkj,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zvY,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zC4,ze,zi,za,zt,zc,zl,zf] (.node [zwu,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zcC,ze,za,zt,zc,zk6,zl,zf] (.node [zcC,ze,zi,za,zt,zc,zl,zf] (.node [zcC,ze,zc4,za,zt,zc,zl,zf] (.node [zcC,ze,zjP,za,zt,zc,zl,zf] .nil .nil) (.node [zcC,ze,zgP,za,zt,zc,zl,zf] .nil .nil)) (.node [zcC,ze,za,zt,zbR,zc,zl,zf] (.node [zcC,ze,zkO,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zrt,ze,zi,za,zt,zc,zl,zf] (.node [zcC,zgP,za,zt,zc,zl,zf] (.node [zcC,zgP,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zcC,zi,za,zt,zc,zl,zV,zf] .nil .nil)) (.node [zlJ,ze,zi,za,zt,zc,zl,zf] (.node [zzm,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lllrr:BTree (List W):=(.node [zg9,ze,zi,zgp,zt,zc,zl,zf] (.node [zmw,zi,za,zgX,zt,zc,zl,zf] (.node [zmw,ze,zi,za,zgX,zc,zl,zf] (.node [zBk,ze,zi,za,zt,zc,zl,zf] (.node [zgy,zc4,zi,za,zt,zc,zl,zf] (.node [zgy,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zgy,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zG1,ze,zi,za,zt,zc,zl,zf] (.node [zuI,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zEa,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zmw,ze,zi,za,zt,zc,zl,zls] (.node [zmw,ze,zi,za,zt,zc,zl,zg8] (.node [zmw,ze,zi,za,zt,zc,zl1,zf] .nil .nil) (.node [zmw,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zmw,ze,zi,za,zz5,zc,zl,zf] (.node [zmw,ze,zi,za,zt,zc,zc6,zf] .nil .nil) .nil))) (.node [zbo,zi,za,zb8,zt,zc,zl,zf] (.node [zmq,ze,zi,za,zt,zc,zl,zf] (.node [zmw,zi,za,zt,zc,zl,zV,zf] (.node [zmw,zi,za,zgX,zc,zl,zf] .nil .nil) (.node [zmw,zi,za,zt,zc,zl,zf,zd] .nil .nil)) (.node [zgW,ze,zi,za,zt,zc,zl,zf] (.node [zjY,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zbo,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zb9,zi,za,zt,zc,zl,zf] (.node [zb9,ze,zi,za,zt,zc,zl,zf] (.node [zbo,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zb9,zi,za,zbG,zt,zc,zl,zf] .nil .nil)) (.node [zB6,ze,zi,za,zt,zc,zl,zf] (.node [zBd,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ztL,ze,zi,za,zt,zc,zl,zpC] (.node [zi2,ze,zi,za,zt,zc,zl,zf] (.node [zg9,zi,zgp,zt,zc,zl,zf] (.node [zg9,ze,zi,zY,zt,zc,zl,zf] (.node [zg9,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zg9,zi,zgp,za,zt,zc,zl,zf] .nil .nil)) (.node [zg9,zi,za,zt,zc,zl,zf,zd] (.node [zg9,zi,za,zt,zc,z8,zl,zf] .nil .nil) (.node [zym,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zBE,ze,zi,za,zt,zc,zl,zf] (.node [zdg,zi,zuB,za,zt,zc,zl,zf] (.node [zdg,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zdg,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ztL,ze,zi,za,zt,zc,zd9,zf] (.node [zHt,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ztN,ze,zi,za,zt,zc,zl,zf] (.node [ztL,zi,za,zt,zc,zl,zV,zf] (.node [ztL,ze,zi,za,zt,zc,zl,zgM] (.node [ztL,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ztL,ze,zi,za,zt,zc,zV,zf] .nil .nil)) (.node [zzz,ze,zi,za,zt,zc,zl,zf] (.node [zkL,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zxU,ze,zi,za,zt,zc,zl,zf] (.node [zDR,ze,zi,za,zt,zc,zl,zf] (.node [zFk,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zs4,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zu9,ze,zi,za,zt,zc,zl,zf] (.node [zFR,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lllr:BTree (List W):=.node [zxz,ze,zi,za,zt,zc,zl,zf] tree7_lllrl tree7_lllrr
def tree7_lll:BTree (List W):=.node [zEj,ze,zi,za,zt,zc,zl,zf] tree7_llll tree7_lllr
def tree7_llrll:BTree (List W):=(.node [ze,zBV,zi,za,zt,zc,zl,zf] (.node [zGe,ze,zi,za,zt,zc,zl,zf] (.node [zx6,ze,zi,za,zt,zc,zl,zf] (.node [zza,ze,zi,za,zt,zc,zke,zf] (.node [zza,ze,zi,za,zt,zc,zl,zf] (.node [zza,ze,zi,za,zt,zc,zl,zcv] .nil .nil) (.node [zza,ze,zi,za,zt,zc,zl,zd] .nil .nil)) (.node [zhy,ze,zi,za,zt,zc,zl,zf] (.node [zza,zi,za,zt,zc,zl,zf,zd] .nil .nil) (.node [zvy,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [zxd,ze,zi,za,zt,zc,zl,zf] (.node [zs2,ze,zi,za,zt,zc,zl,zf] (.node [zxm,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zsG,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [zuE,ze,zi,za,zt,zc,zl,zf] (.node [zF4,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zuZ,zi,za,zt,zc,zl,zf] (.node [zHj,ze,zi,za,zt,zc,zl,zf] (.node [zup,ze,zi,za,zt,zc,zl,zf] (.node [zy2,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [zEK,ze,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zFc,zi,za,zt,zc,zl,zf] (.node [zwT,ze,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zxI,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zGu,zi,za,zt,zc,zl,zf] (.node [ze,zzh,zi,za,zt,zc,zl,zf] (.node [ze,zsQ,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zub,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zz4,zi,za,zt,zc,zl,zf] (.node [ze,zsJ,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zuJ,zi,za,zt,zc,zl,zf] (.node [ze,zBU,zi,za,zt,zc,zl,zf] (.node [ze,zzd,zi,za,zt,zc,zl,zf] (.node [ze,zxC,zi,za,zt,zc,zl,zf] (.node [ze,zAB,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zwe,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zxc,zi,za,zt,zc,zl,zf] (.node [ze,zF9,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zDK,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zBW,zi,za,zt,zc,zl,zf] (.node [ze,zGL,zi,za,zt,zc,zl,zf] (.node [ze,zGJ,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zwM,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zvk,zi,za,zt,zc,zl,zf] (.node [ze,zrw,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zeT,zi,zt,zc2,zc,zl,zf] (.node [ze,zeT,zi,za,zt,zc2,zc,zl] (.node [ze,zeT,zi,ztE,zt,zc,zl,zf] (.node [ze,zeT,zeG,zi,zt,zc,zl,zf] .nil .nil) (.node [ze,zeT,zi,zuB,zt,zc,zl,zf] .nil .nil)) (.node [ze,zeT,zi,za,zt,zc,zl,z6] (.node [ze,zeT,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zHe,zi,za,zt,zc,zl,zf] (.node [ze,zeT,zi,zt,zc,zx,zl,zf] (.node [ze,zeT,zi,zt,zdK,zc,zl,zf] .nil .nil) (.node [ze,zzo,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zxk,zi,za,zt,zc,zl,zf] (.node [ze,zuF,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_llrlr:BTree (List W):=(.node [ze,zw1,zi,za,ziN,zc,zl,zf] (.node [ze,zBe,zi,za,zt,zc,zl,zf] (.node [ze,zbh,zi,za,zt,zc,zl,zcv] (.node [ze,zbh,zi,za,za5,zt,zc,zl] (.node [ze,zBA,zi,za,zt,zc,zl,zf] (.node [ze,ztP,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zbh,zck,zi,za,zc,zl,zf] .nil .nil)) (.node [ze,zbh,zi,za,zeO,zc,zl,zf] (.node [ze,zbh,zi,za,za5,zc,zl,zf] .nil .nil) (.node [ze,zbh,zi,za,zb8,zc,zl,zf] .nil .nil))) (.node [ze,zbh,zi,za,zdK,zc,zl,zf] (.node [ze,zbh,zi,za,zt,zc,zl,zd] (.node [ze,zbh,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zbh,zi,za,zt,zc,zl,zbe] .nil .nil)) (.node [ze,zD1,zi,za,zt,zc,zl,zf] (.node [ze,zbh,zi,za,zc,zbJ,zl,zf] .nil .nil) .nil))) (.node [ze,zw1,zi7,za,zt,zc,zl,zf] (.node [ze,zyV,zi,za,zt,zc,zl,zf] (.node [ze,zGz,zi,za,zt,zc,zl,zf] (.node [ze,ztl,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zEC,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zGG,zi,za,zt,zc,zl,zf] (.node [ze,zx5,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zw1,zjP,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zw1,zi,za,zt,zc,zwU,zl] (.node [ze,zw1,zxb,za,zt,zc,zl,zf] (.node [ze,zw1,zgZ,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zw1,zi,za,zbQ,zc,zl,zf] .nil .nil)) (.node [ze,zw1,zi,za,zt,zc,zl,zw3] (.node [ze,zw1,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,ziV,zi,za,zt,zmo,zl,zf] (.node [ze,zAD,zi,za,zt,zc,zl,zf] (.node [ze,zw1,za,zt,zc,zcl,zl,zf] (.node [ze,zw1,za,zt,zbR,zc,zl,zf] (.node [ze,zw1,za,zip,zt,zc,zl,zf] .nil .nil) (.node [ze,zw1,za,zt,zc,zwU,zl,zf] .nil .nil)) (.node [ze,zGk,zi,za,zt,zc,zl,zf] (.node [ze,zGX,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zxe,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,ziV,zi,zfi,za,zt,zc,zl] (.node [ze,zs5,zi,za,zt,zc,zl,zf] (.node [ze,zzt,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zCK,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,ziV,zi,za,zug,zt,zl,zf] (.node [ze,ziV,zi,zfi,za,zt,zl,zf] .nil .nil) .nil))) (.node [ze,zBc,zi,za,zt,zc,zl,zf] (.node [ze,ziV,zi,za,zt,zx,zl,zf] (.node [ze,ziV,zi,za,zt,zc,zl,zf] (.node [ze,ziV,zi,za,zt,zsH,zl,zf] .nil .nil) (.node [ze,ziV,zi,za,zt,zc,zl,zv] .nil .nil)) (.node [ze,zC9,zi,za,zt,zc,zl,zf] (.node [ze,ziV,zi,za,zt,zbJ,zl,zf] .nil .nil) .nil)) (.node [ze,zFE,zi,za,zt,zc,zl,zf] (.node [ze,zvL,zi,za,zt,zc,zl,zf] (.node [ze,zsz,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zwO,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zce,zcW,zi,za,zt,zc,zf] (.node [ze,zwB,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_llrl:BTree (List W):=.node [ze,zui,zi,za,zt,zc,zl,zf] tree7_llrll tree7_llrlr
def tree7_llrrl:BTree (List W):=(.node [ze,zwv,zi,za,zt,zc,zl,zf] (.node [ze,zCq,zi,za,zt,zc,zl,zf] (.node [ze,zce,zi,za,zt,zc,zl,zf] (.node [ze,zce,zi,za,zbq,zt,zc,zf] (.node [ze,zce,zc4,zi,za,zt,zc,zf] (.node [ze,zce,zfT,zi,za,zt,zc,zf] .nil .nil) (.node [ze,zce,zi,zsI,za,zt,zc,zf] .nil .nil)) (.node [ze,zce,zi,za,zt,zc,zsg,zf] (.node [ze,zce,zi,za,zt,zuQ,zc,zf] .nil .nil) (.node [ze,zce,zi,za,zt,zc,zd9,zf] .nil .nil))) (.node [ze,zce,zi,za,zt,zc,zg0,zf] (.node [ze,zce,zi,za,zt,zc,zV,zf] (.node [ze,zce,zi,za,zt,zc,zl,zac] .nil .nil) (.node [ze,zce,zi,za,zt,zc,zu4,zf] .nil .nil)) (.node [ze,zB5,zi,za,zt,zc,zl,zf] (.node [ze,zce,zi,za,zt,zc,zs0,zf] .nil .nil) .nil))) (.node [ze,zyE,zi,za,zt,zc,zl,zf] (.node [ze,zvc,zi,za,zt,zc,zl,zf] (.node [ze,zyO,zi,za,zt,zc,zl,zf] (.node [ze,zxj,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zyY,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zvz,zi,za,zt,zc,zl,zf] (.node [ze,zsX,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zt7,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zys,zi,za,zt,zc,zl,zf] (.node [ze,zuq,zi,za,zt,zc,zl,zf] (.node [ze,zsW,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zy6,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zwi,zi,za,zt,zc,zl,zf] (.node [ze,zxW,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zxE,zi,za,zt,zc,zl,zf] (.node [ze,zva,zi,za,zt,zc,zl,zf] (.node [ze,zwD,zi,za,zt,zc,zl,zf] (.node [ze,ztX,zi,za,zt,zc,zl,zf] (.node [ze,zzg,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,ztH,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zDD,zi,za,zt,zc,zl,zf] (.node [ze,zyy,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zv9,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zHw,zi,za,zt,zc,zl,zf] (.node [ze,zGq,zi,za,zt,zc,zl,zf] (.node [ze,ztT,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zw5,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zu1,zi,za,zt,zc,zl,zf] (.node [ze,zv5,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zu8,zi,za,zt,zc,zl,zf] (.node [ze,zu8,zi,zu7,zt,zc,zl,zf] (.node [ze,zu8,zi,ztB,zt,zc,zl,zf] (.node [ze,zu8,zbT,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zu8,zi,ztE,zt,zc,zl,zf] .nil .nil)) (.node [ze,zu8,zi,za,zt,zuQ,zc,zf] (.node [ze,zu8,zi,za,zca,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zu8,zi,zt,zuQ,zc,zl,zf] (.node [ze,zu8,zi,za,zbU,zc,zl,zf] (.node [ze,zu8,zi,za,zt,zc,zu4,zf] .nil .nil) (.node [ze,zu8,zi,zip,zt,zc,zl,zf] .nil .nil)) (.node [ze,zu8,zdx,za,zt,zc,zl,zf] (.node [ze,zu8,zi,zt,zdK,zc,zl,zf] .nil .nil) .nil)))))
def tree7_llrrr:BTree (List W):=(.node [ze,zye,zi,za,ziK,zc,zl,zf] (.node [ze,zgw,zi,za,zt,zc,zd9,zf] (.node [ze,zzC,zi,za,zt,zc,zl,zf] (.node [ze,zAt,zi,za,zt,zc,zl,zf] (.node [ze,zvB,zi,za,zt,zc,zl,zf] (.node [ze,zBS,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zsl,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zuw,zi,za,zt,zc,zl,zf] (.node [ze,zFX,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zBL,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zgw,zi,za,zbq,zc,zl,zf] (.node [ze,zgw,zc4,zi,za,zt,zc,zf] (.node [ze,zgw,zcW,zi,za,zt,zc,zf] .nil .nil) (.node [ze,zgw,zi,za,zbq,zt,zc,zf] .nil .nil)) (.node [ze,zgw,zi,za,zbG,zc,zl,zf] (.node [ze,zgw,zi,za,zhO,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zwp,zi,za,zt,zc,zl,zf] (.node [ze,zgw,zi,za,zbR,zc,zl,zf] (.node [ze,zgw,zi,za,zt,zc,zV,zf] (.node [ze,zgw,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zgw,zi,za,zt,zc,zg0,zf] .nil .nil)) (.node [ze,zBO,zi,za,zt,zc,zl,zf] (.node [ze,zEe,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zyZ,zi,za,zt,zc,zl,zf] (.node [ze,zwr,zi,za,zt,zc,zl,zf] (.node [ze,zsj,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zAG,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zye,zgZ,za,zt,zc,zl,zf] (.node [ze,zuj,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zcW,zi,za,zbG,zt,zc,zf] (.node [ze,zFY,zi,za,zt,zc,zl,zf] (.node [ze,zye,zi,za,zga,zc,zl,zf] (.node [ze,zye,zi,za,zt,zc,zl,zf] (.node [ze,zye,zi,za,zt,zyf,zl,zf] .nil .nil) (.node [ze,zye,zi,za,zt,zcl,zl,zf] .nil .nil)) (.node [ze,zDn,zi,za,zt,zc,zl,zf] (.node [ze,zye,za,zt,zc,zcl,zl,zf] .nil .nil) (.node [ze,zG0,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zBu,zi,za,zt,zc,zl,zf] (.node [ze,zwV,zi,za,zt,zc,zl,zf] (.node [ze,zsr,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zBn,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zcW,zc4,za,zt,zc,zl,zf] (.node [ze,zcW,zjP,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zF7,zi,za,zt,zc,zl,zf] (.node [ze,zcW,zi,za,zt,zc,zf,zac] (.node [ze,zcW,zi,za,zt,zc,zl,zf] (.node [ze,zcW,zi,za,zt,zc,zk6,zf] .nil .nil) (.node [ze,zcW,zi,za,zt,zc,zgN,zf] .nil .nil)) (.node [ze,zcW,za,zt,zc,zk6,zl,zf] (.node [ze,zcW,za,zt,zbR,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zEH,zi,za,zt,zc,zl,zf] (.node [ze,zxV,zi,za,zt,zc,zl,zf] (.node [ze,zHA,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zsL,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zl8,zi,za,zt,zbR,zc,zf] (.node [ze,zDG,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_llrr:BTree (List W):=.node [ze,zEz,zi,za,zt,zc,zl,zf] tree7_llrrl tree7_llrrr
def tree7_llr:BTree (List W):=.node [ze,zce,zfT,zi,za,zt,zc,zl] tree7_llrl tree7_llrr
def tree7_ll:BTree (List W):=.node [zza,ze,zi,za,zt,zc,zkM,zf] tree7_lll tree7_llr
def tree7_lrlll:BTree (List W):=(.node [ze,zfT,zi,za,zt,zc,zl,zf] (.node [ze,zsO,zi,za,zaR,zc,zl,zf] (.node [ze,zsO,zi,za,zaQ,zc,zl,zf] (.node [ze,zsO,zaP,za,zt,zc,zl,zf] (.node [ze,zAP,zi,za,zt,zc,zl,zf] (.node [ze,zl8,zi,za,zt,zc,zf] .nil .nil) (.node [ze,zCQ,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zsO,zi,zsI,za,zt,zl,zf] (.node [ze,zsO,zi,zsI,za,zt,zc,zf] .nil .nil) (.node [ze,zsO,zi,za,zug,zt,zl,zf] .nil .nil))) (.node [ze,zsO,zi,za,zt,zc,zs0,zf] (.node [ze,zsO,zi,za,zt,zyf,zl,zf] (.node [ze,zsO,zi,za,zt,zsS,zl,zf] .nil .nil) (.node [ze,zsO,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zsO,zi,za,zt,zcl,zl,zf] (.node [ze,zsO,zi,za,zt,zbJ,zl,zf] .nil .nil) .nil))) (.node [ze,zwC,zi,za,zt,zc,zl,zf] (.node [ze,zv8,zi,za,zt,zc,zl,zf] (.node [ze,zAv,zi,za,zt,zc,zl,zf] (.node [ze,zsO,zaS,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zEO,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zsh,zi,za,zt,zc,zl,zf] (.node [ze,zxD,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zvP,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zfT,zi,za,zt,zc,zwU,zl] (.node [ze,zFH,zi,za,zt,zc,zl,zf] (.node [ze,zyM,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zfT,zi,za,za5,zt,zc,zl] .nil .nil)) (.node [ze,zfT,zi,za,zt,zc,zl,zcv] (.node [ze,zfT,zi,za,zt,zc,zsg,zl] .nil .nil) .nil)))) (.node [ze,zA4,zi,za,zt,zc,zl,zf] (.node [ze,ztm,zi,za,zt,zc,zl,zf] (.node [ze,zfT,zi,za,zt,zc,zf,zac] (.node [ze,zfT,zi,za,zt,zc,zl,zbe] (.node [ze,zfT,zi,za,zt,zc,zl,zd] .nil .nil) (.node [ze,zfT,zi,za,zt,zc,zl,zw3] .nil .nil)) (.node [ze,zCV,zi,za,zt,zc,zl,zf] (.node [ze,zBh,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zr8,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zAl,zi,za,zt,zc,zl,zf] (.node [ze,zDH,zi,za,zt,zc,zl,zf] (.node [ze,zzA,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zsA,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zAA,zi,za,zt,zc,zl,zf] (.node [ze,zAa,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zE4,zi,za,zt,zc,zl,zf] (.node [ze,zwj,zi,za,zt,zc,zl,zf] (.node [ze,zAw,zi,za,zt,zc,zl,zf] (.node [ze,zyK,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zAZ,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zzj,zi,za,zt,zc,zl,zf] (.node [ze,zAI,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zjP,zgZ,za,zt,zc,zl,zf] (.node [ze,zjP,zi7,za,zt,zc,zl,zf] (.node [ze,zGA,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zjP,zzI,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zjP,zi,za,zt,zc,zl,zf] (.node [ze,zjP,zi,za,zhO,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lrllr:BTree (List W):=(.node [ze,zi7,zi,ztB,zt,zc,zl,zf] (.node [ze,zb3,zi,za,zt,zc,zl,zf] (.node [ze,zgo,za,zt,zc,zl,zf] (.node [ze,zjP,za,zt,zc,zl,zgN,zf] (.node [ze,zjP,za,zhO,zt,zc,zl,zf] (.node [ze,zjP,za,zip,zt,zc,zl,zf] .nil .nil) (.node [ze,zjP,za,zt,zc,zcl,zl,zf] .nil .nil)) (.node [ze,zgo,zi,za,zt,zc,zl,zf] (.node [ze,zjP,za,zt,zc,zl,zf,zw3] .nil .nil) (.node [ze,zgo,za,zgX,zt,zc,zl,zf] .nil .nil))) (.node [ze,zbj,za,zb8,zt,zc,zl,zf] (.node [ze,zzp,zi,za,zt,zc,zl,zf] (.node [ze,zG3,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zbj,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zHb,zi,za,zt,zc,zl,zf] (.node [ze,zbj,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zAr,zi,za,zt,zc,zl,zf] (.node [ze,zF2,zi,za,zt,zc,zl,zf] (.node [ze,zb3,za,zt,zc,zl,zf] (.node [ze,zb3,za,zbG,zt,zc,zl,zf] .nil .nil) (.node [ze,zE0,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zHy,zi,za,zt,zc,zl,zf] (.node [ze,zGy,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zBD,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi7,zc4,za,zt,zc,zl,zf] (.node [ze,zGD,zi,za,zt,zc,zl,zf] (.node [ze,zAn,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi7,zAz,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi7,zgP,za,zt,zc,zl,zf] (.node [ze,zi7,zgZ,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zvH,zi,za,zt,zc,zl,zf] (.node [ze,zi7,za,zt,zc,zl,zf,zw3] (.node [ze,zi7,ztB,za,zt,zc,zl,zf] (.node [ze,zi7,zi,zip,zt,zc,zl,zf] (.node [ze,zi7,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi7,zkO,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi7,za,zt,zc,zk6,zl,zf] (.node [ze,zi7,za,zt,zbR,zc,zl,zf] .nil .nil) (.node [ze,zi7,za,zt,zc,zcl,zl,zf] .nil .nil))) (.node [ze,zdb,zi,za,zt,zc,zl,zf] (.node [ze,zGT,zi,za,zt,zc,zl,zf] (.node [ze,zF6,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zAT,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zdb,za,zt,zc,zl,zf] (.node [ze,zdb,zuB,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zA0,zi,za,zt,zc,zl,zf] (.node [ze,zkD,zwl,za,zt,zc,zl,zf] (.node [ze,zvO,zi,za,zt,zc,zl,zf] (.node [ze,zHd,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zvK,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zkD,za,zt,zc,zl,zf] (.node [ze,zkD,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zGF,zi,za,zt,zc,zl,zf] (.node [ze,zwP,zi,za,zt,zc,zl,zf] (.node [ze,zx9,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zuy,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zwl,zi,za,zeO,zc,zl,zf] (.node [ze,zwl,zi,ztE,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lrll:BTree (List W):=.node [ze,zjP,zi,za,zbR,zc,zl,zf] tree7_lrlll tree7_lrllr
def tree7_lrlrl:BTree (List W):=(.node [ze,zvC,zi,za,zt,zc,zl,zf] (.node [ze,zAz,zi,ztB,zt,zc,zl,zf] (.node [ze,zFT,zi,za,zt,zc,zl,zf] (.node [ze,zDP,zi,za,zt,zc,zl,zf] (.node [ze,zwl,zi,zt,zdK,zc,zl,zf] (.node [ze,zwl,zi,za,zdK,zc,zl,zf] .nil .nil) (.node [ze,zwl,zfQ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zyu,zi,za,zt,zc,zl,zf] (.node [ze,zEo,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zEQ,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zD5,zi,za,zt,zc,zl,zf] (.node [ze,zwz,zi,za,zt,zc,zl,zf] (.node [ze,zvM,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zCC,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zGH,zi,za,zt,zc,zl,zf] (.node [ze,zAQ,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zD4,zi,za,zt,zc,zl,zf] (.node [ze,zAz,zi,zip,zt,zc,zl,zf] (.node [ze,zAz,zi,za,zt,zc,zl,zf] (.node [ze,zAz,zi,za,zjN,zc,zl,zf] .nil .nil) (.node [ze,zAz,zi,za,zja,zc,zl,zf] .nil .nil)) (.node [ze,zEd,zi,za,zt,zc,zl,zf] (.node [ze,zAz,za,zip,zt,zc,zl,zf] .nil .nil) (.node [ze,zA9,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zGB,zi,za,zt,zc,zl,zf] (.node [ze,zut,zi,za,zt,zc,zl,zf] (.node [ze,zw0,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zy3,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zu2,zi,za,zt,zc,zl,zf] (.node [ze,zuV,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zaz,zi,zt,zc,zl,zf] (.node [ze,zeG,zi,zY,zt,zc,zl,zf] (.node [ze,zeG,zi,zgp,zt,zc,zl,zf] (.node [ze,zFh,zi,za,zt,zc,zl,zf] (.node [ze,zDJ,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zeG,zi,zek,zt,zc,zl,zf] .nil .nil)) (.node [ze,zeG,zi,za,zt,zc,zl,zf] (.node [ze,zeG,zi,za,zt,zmo,zl,zf] .nil .nil) (.node [ze,zeG,zi,za,zt,zx,zl,zf] .nil .nil))) (.node [ze,zvI,zi,za,zt,zc,zl,zf] (.node [ze,zeG,zi,zt,zc,zl,zf,z6] (.node [ze,zeG,zi,zt,zmo,zc,zl,zf] .nil .nil) (.node [ze,zEg,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zaz,zi,zt,zsH,zc,zl,zf] (.node [ze,zaz,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zzQ,zi,za,zt,zc,zl,zf] (.node [ze,zx2,zi,za,zt,zc,zl,zf] (.node [ze,zB7,zi,za,zt,zc,zl,zf] (.node [ze,zwy,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zuN,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zzT,zi,za,zt,zc,zl,zf] (.node [ze,zzU,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zzI,zi,za,zbR,zc,zl,zf] (.node [ze,zzI,zi,za,zhO,zc,zl,zf] (.node [ze,zCa,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zzI,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zFV,zi,za,zt,zc,zl,zf] (.node [ze,zzI,za,zt,zbR,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lrlrr:BTree (List W):=(.node [ze,zaw,zi,za,zsH,zc,zl,zf] (.node [ze,zck,zi,za,zhO,zc,zl,zf] (.node [ze,zzX,zi,za,zt,zc,zl,zf] (.node [ze,zuD,zi,za,zt,zc,zl,zf] (.node [ze,zwX,zi,za,zt,zc,zl,zf] (.node [ze,zwF,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zGi,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,ztA,zi,za,zt,zc,zl,zf] (.node [ze,zyb,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zt9,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zck,zi,za,zug,zc,zl,zf] (.node [ze,zDW,zi,za,zt,zc,zl,zf] (.node [ze,zw7,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zck,zi,za,zug,zt,zl,zf] .nil .nil)) (.node [ze,zck,zi,za,zuh,zc,zl,zf] (.node [ze,zck,zi,za,zbq,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zck,zi,za,zbR,zc,zl,zf] (.node [ze,zck,zi,za,zt,zc,zl,zf] (.node [ze,zck,zi,za,zbG,zc,zl,zf] (.node [ze,zck,zi,za,zeO,zc,zl,zf] .nil .nil) (.node [ze,zck,zi,za,zgX,zc,zl,zf] .nil .nil)) (.node [ze,zck,zi,za,zz5,zc,zl,zf] (.node [ze,zck,zi,za,zt,zbJ,zl,zf] .nil .nil) .nil)) (.node [ze,zDz,zi,za,zt,zc,zl,zf] (.node [ze,zck,zi,za,zc,zl,zf,zbe] (.node [ze,zck,zi,za,zdK,zc,zl,zf] .nil .nil) (.node [ze,zDN,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zaw,zi,za,zt,zc,zl,zf] (.node [ze,zAx,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zc4,zi,za,zt,zgk,zl,zf] (.node [ze,zya,zi,za,zt,zc,zl,zf] (.node [ze,zs7,zi,za,zt,zc,zl,zf] (.node [ze,zvt,zi,za,zt,zc,zl,zf] (.node [ze,zaw,zi,za,zc,zl,zf] .nil .nil) (.node [ze,zBr,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zuo,zi,za,zt,zc,zl,zf] (.node [ze,zwm,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zEp,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zc4,zi,zeM,zt,zc,zl,zf] (.node [ze,zGa,zi,za,zt,zc,zl,zf] (.node [ze,zyG,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zc4,zgZ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zc4,zi,za,zbG,zt,zc,zf] (.node [ze,zc4,zi,za,zcJ,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zc4,zi,za,zt,zgn,zl,zf] (.node [ze,zc4,zi,za,zt,zc,zl,zcm] (.node [ze,zc4,zi,za,zt,zc,zgb,zl] (.node [ze,zc4,zi,za,zt,zc,zk6,zf] .nil .nil) (.node [ze,zc4,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zc4,zi,za,zt,zc,zf,zac] (.node [ze,zc4,zi,za,zt,zc,zgN,zf] .nil .nil) .nil)) (.node [ze,zc4,za,zt,zc,zcl,zl,zf] (.node [ze,zc4,zi,zcI,zt,zc,zl,zf] (.node [ze,zc4,zi,za,zN,zc,zl,zf] .nil .nil) (.node [ze,zc4,za,zip,zt,zc,zl,zf] .nil .nil)) (.node [ze,zg,zi,za,zt,zc,zl,zf] (.node [ze,zc4,za,zt,zc,zl,zgN,zf] .nil .nil) .nil)))))
def tree7_lrlr:BTree (List W):=.node [ze,zDc,zi,za,zt,zc,zl,zf] tree7_lrlrl tree7_lrlrr
def tree7_lrl:BTree (List W):=.node [ze,zwl,zi,za,zt,zc,zl,zf] tree7_lrll tree7_lrlr
def tree7_lrrll:BTree (List W):=(.node [ze,ziL,za,zuh,zt,zc,zl,zf] (.node [ze,zgZ,za,zip,zt,zc,zl,zf] (.node [ze,zzG,zi,za,zt,zc,zl,zf] (.node [ze,zCp,zi,za,zt,zc,zl,zf] (.node [ze,zFO,zi,za,zt,zc,zl,zf] (.node [ze,zg,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zM,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zfS,zi,za,zt,zc,zl,zf] (.node [ze,zfS,zi,za,zt,zc,zwU,zf] .nil .nil) (.node [ze,zfS,zi,za,zt,zc,zf] .nil .nil))) (.node [ze,zgZ,zi,za,zt,zc,zl,zf] (.node [ze,zgZ,zgP,za,zt,zc,zl,zf] (.node [ze,zAH,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zgZ,zi,za,zt,zyf,zl,zf] .nil .nil)) (.node [ze,zgZ,zkO,za,zt,zc,zl,zf] (.node [ze,zgZ,zi,za,zt,zcl,zl,zf] .nil .nil) .nil))) (.node [ze,zaP,zi,za,zt,zc,zl,zf] (.node [ze,zgZ,za,zt,zc,zl,zf,zw3] (.node [ze,zgZ,za,zt,zyf,zc,zl,zf] (.node [ze,zgZ,za,zt,zbR,zc,zl,zf] .nil .nil) (.node [ze,zgZ,za,zt,zc,zk6,zl,zf] .nil .nil)) (.node [ze,zEy,zi,za,zt,zc,zl,zf] (.node [ze,zC0,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zyJ,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zaC,za,zt,zc,zl,zf] (.node [ze,zaC,zi,za,zt,zc,zl,zf] (.node [ze,zaP,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zaC,za,zt,zsH,zc,zl,zf] .nil .nil)) (.node [ze,ziL,zi,za,zt,zc,zl,zf] (.node [ze,zCo,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zxb,zi,za,zt,zc,zl,zw3] (.node [ze,zCw,zi,za,zt,zc,zl,zf] (.node [ze,zC,zi,za,zt,zc,zl,zf] (.node [ze,zbT,zi,za,zt,zc,zl,zf] (.node [ze,ziL,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zbT,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zC,za,zt,zc,zl,zf] (.node [ze,zC,zek,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zvh,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zG9,zi,za,zt,zc,zl,zf] (.node [ze,zt6,zi,za,zt,zc,zl,zf] (.node [ze,ztM,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zBy,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zxb,zi,za,zt,zc,zl,zf] (.node [ze,zxb,zi,za,zt,zc,zwU,zl] .nil .nil) .nil))) (.node [ze,zta,zi,za,zt,zc,zl,zf] (.node [ze,zEJ,zi,za,zt,zc,zl,zf] (.node [ze,zBC,zi,za,zt,zc,zl,zf] (.node [ze,zxb,za,zt,zc,zl,zf,zw3] .nil .nil) (.node [ze,zz3,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zsx,zi,za,zt,zc,zl,zf] (.node [ze,zxZ,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zEB,zi,za,zt,zc,zl,zf] (.node [ze,zDj,zi,za,zt,zc,zl,zf] (.node [ze,ztj,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zxi,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zsf,zi,za,zt,zc,zl,zf] (.node [ze,zsE,zi,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lrrlr:BTree (List W):=(.node [ze,zi,zdx,za,zt,zc,zl,zf] (.node [ze,zi,zBt,za,zt,zc,zl,zf] (.node [ze,zkP,zi,za,zt,zc,zl,zf] (.node [ze,zEc,zi,za,zt,zc,zl,zf] (.node [ze,zgP,za,zt,zc,zcl,zl,zf] (.node [ze,zgP,za,zip,zt,zc,zl,zf] .nil .nil) (.node [ze,zBR,zi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zxn,zi,za,zt,zc,zl,zf] (.node [ze,zC8,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zCB,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zEm,zi,za,zt,zc,zl,zf] (.node [ze,zjJ,zi,za,zt,zc,zl,zf] (.node [ze,zyk,zi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zjJ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zjn,za,zt,zc,zl,zf] (.node [ze,zjn,zi,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zCD,za,zt,zc,zl,zf] (.node [ze,zi,zEU,za,zt,zc,zl,zf] (.node [ze,zi,ze8,za,zt,zc,zl,zf] (.node [ze,zi,zuK,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zEX,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zAV,za,zt,zc,zl,zf] (.node [ze,zi,zeE,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zDv,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,ztk,za,zt,zc,zl,zf] (.node [ze,zi,zkO,za,zt,zc,zl,zf] (.node [ze,zi,zCs,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zuC,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zHl,za,zt,zc,zl,zf] (.node [ze,zi,zsy,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zsI,za,zt,zc,zl,zf] (.node [ze,zi,zz0,za,zt,zc,zl,zf] (.node [ze,zi,zr7,za,zt,zc,zl,zf] (.node [ze,zi,zaS,za,zt,zc,zl,zf] (.node [ze,zi,zCG,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zxB,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zz6,za,zt,zc,zl,zf] (.node [ze,zi,zfQ,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zGl,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,zsI,za,zt,zuQ,zc,zf] (.node [ze,zi,zsK,za,zt,zc,zl,zf] (.node [ze,zi,zEl,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zDb,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zsI,za,zt,zc,zd9,zf] (.node [ze,zi,zsI,za,zt,zsS,zc,zf] .nil .nil) .nil))) (.node [ze,zi,zsN,za,zt,zc,zl,zf] (.node [ze,zi,zsI,za,zt,zl,zs0,zf] (.node [ze,zi,zsI,za,zt,zc,zu4,zf] (.node [ze,zi,zsI,za,zt,zc,zV,zf] .nil .nil) (.node [ze,zi,zsI,za,zt,zc,zf,zac] .nil .nil)) (.node [ze,zi,zyT,za,zt,zc,zl,zf] (.node [ze,zi,zCb,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zaA,za,zt,zc,zf] (.node [ze,zi,zaA,za,zt,zsH,zc,zf] (.node [ze,zi,zyq,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zaA,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,ztJ,za,zt,zc,zl,zf] (.node [ze,zi,zFj,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lrrl:BTree (List W):=.node [ze,zgP,zi,za,zt,zc,zl,zf] tree7_lrrll tree7_lrrlr
def tree7_lrrrl:BTree (List W):=(.node [ze,zi,zek,za,zt,zH,zc,zl] (.node [ze,zi,zxS,za,zt,zc,zl,zf] (.node [ze,zi,zfi,za,zt,zl,zf,zv] (.node [ze,zi,zfi,za,zt,zc,zl,zcv] (.node [ze,zi,zfi,za,zt,zc2,zc,zl] (.node [ze,zi,zFI,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zfi,za,zt,zsH,zc,zl] .nil .nil)) (.node [ze,zi,zfi,za,zt,zc,zl,zd] (.node [ze,zi,zfi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zfi,za,zt,zc,zl,z6] .nil .nil))) (.node [ze,zi,zxQ,za,zt,zc,zl,zf] (.node [ze,zi,zx8,za,zt,zc,zl,zf] (.node [ze,zi,zBw,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zv3,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zxq,za,zt,zc,zl,zf] (.node [ze,zi,zto,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zwJ,za,zt,zc,zl,zf] (.node [ze,zi,zwR,za,zt,zc,zl,zf] (.node [ze,zi,zGZ,za,zt,zc,zl,zf] (.node [ze,zi,zsM,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zuR,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zwq,za,zt,zc,zl,zf] (.node [ze,zi,zuM,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zwo,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,zek,za,zB,zc,zl,zf] (.node [ze,zi,zyx,za,zt,zc,zl,zf] (.node [ze,zi,zAb,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zv2,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zek,za,zt,zI,zc,zf] (.node [ze,zi,zek,za,zt,zmo,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zuS,za,zt,zc,zl,zf] (.node [ze,zi,zln,za,zt,zc,zl,zf] (.node [ze,zi,zek,za,zt,zx,zl,zf] (.node [ze,zi,zek,za,zt,zc,zl,zz] (.node [ze,zi,zek,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zek,za,zt,zc,zy,zf] .nil .nil)) (.node [ze,zi,zek,zt,zc,zx,zl,zf] (.node [ze,zi,zek,za,zA,zc,zl,zf] .nil .nil) (.node [ze,zi,zek,zt,zx,zl,zf] .nil .nil))) (.node [ze,zi,zvr,za,zt,zc,zl,zf] (.node [ze,zi,zF,za,zt,zc,zl,zf] (.node [ze,zi,zog,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zsp,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zG2,za,zt,zc,zl,zf] (.node [ze,zi,ztv,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,ztB,zY,zt,zc,zl,zf] (.node [ze,zi,zt1,za,zt,zc,zl,zf] (.node [ze,zi,zAX,za,zt,zc,zl,zf] (.node [ze,zi,zBb,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zz7,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,ztB,za,zt,zc,zl,zf] (.node [ze,zi,ztB,zgp,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zFN,za,zt,zc,zl,zf] (.node [ze,zi,zDl,za,zt,zc,zl,zf] (.node [ze,zi,ztB,zt,zc,zl,zu4,zf] .nil .nil) (.node [ze,zi,zDk,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zBJ,za,zt,zc,zl,zf] (.node [ze,zi,zxw,za,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_lrrrr:BTree (List W):=(.node [ze,zi,zu7,za,zt,zuQ,zc,zf] (.node [ze,zi,zbi,zb8,zt,zc,zl,zf] (.node [ze,zi,ztE,zeO,zt,zc,zl,zf] (.node [ze,zi,zFG,za,zt,zc,zl,zf] (.node [ze,zi,zz8,za,zt,zc,zl,zf] (.node [ze,zi,zeM,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zwh,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,ztE,za,zt,zc,zl,zf] (.node [ze,zi,ztE,za,zeO,zc,zl,zf] .nil .nil) (.node [ze,zi,ztE,za,zdK,zc,zl,zf] .nil .nil))) (.node [ze,zi,zDr,za,zt,zc,zl,zf] (.node [ze,zi,ztE,zt,zc,zl,zf,z6] (.node [ze,zi,ztE,zt,zc,zl,zu4,zf] .nil .nil) (.node [ze,zi,zv1,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zbi,za,zt,zc,zl,zf] (.node [ze,zi,zwn,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zCL,za,zt,zc,zl,zf] (.node [ze,zi,zbZ,zbG,zt,zc,zl,zf] (.node [ze,zi,zt8,za,zt,zc,zl,zf] (.node [ze,zi,zbi,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zbZ,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zzY,za,zt,zc,zl,zf] (.node [ze,zi,zbZ,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,zBj,za,zt,zc,zl,zf] (.node [ze,zi,zzk,za,zt,zc,zl,zf] (.node [ze,zi,zHf,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zxR,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zBM,za,zt,zc,zl,zf] (.node [ze,zi,zBv,za,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zEq,za,zt,zc,zl,zf] (.node [ze,zi,zur,za,zt,zc,zl,zf] (.node [ze,zi,zCr,za,zt,zc,zl,zf] (.node [ze,zi,zu7,za,zt,zc,zu4,zf] (.node [ze,zi,zu7,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zu7,zt,zc,zl,zu4,zf] .nil .nil)) (.node [ze,zi,zvq,za,zt,zc,zl,zf] (.node [ze,zi,zHu,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zr6,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,ztF,za,zt,zc,zl,zf] (.node [ze,zi,zFd,za,zt,zc,zl,zf] (.node [ze,zi,zsU,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zy0,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zBX,za,zt,zc,zl,zf] (.node [ze,zi,zvJ,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,zuB,za,zt,zc,zl,zf] (.node [ze,zi,zuB,za,zt,zc9,zl,zf] (.node [ze,zi,zG8,za,zt,zc,zl,zf] (.node [ze,zi,zGN,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zuB,za,zc7,zc,zl,zf] .nil .nil)) (.node [ze,zi,zuB,za,zt,zc2,zc,zl] (.node [ze,zi,zuB,za,zt,zc0,zc,zf] .nil .nil) .nil)) (.node [ze,zi,zuB,za,zda,zc,zl,zf] (.node [ze,zi,zuB,za,zt,zc,zc8,zf] (.node [ze,zi,zuB,za,zt,zc,zl,z6] .nil .nil) (.node [ze,zi,zuB,za,zt,zc1,zl,zf] .nil .nil)) (.node [ze,zi,zpT,za,zt,zc,zl,zf] (.node [ze,zi,zuB,zt,zc,zl,zf,z6] .nil .nil) .nil)))))
def tree7_lrrr:BTree (List W):=.node [ze,zi,zeM,za,zt,zc,zl,zf] tree7_lrrrl tree7_lrrrr
def tree7_lrr:BTree (List W):=.node [ze,zi,zA8,za,zt,zc,zl,zf] tree7_lrrl tree7_lrrr
def tree7_lr:BTree (List W):=.node [ze,zg,za,zt,zc,zl,zV,zf] tree7_lrl tree7_lrr
def tree7_l:BTree (List W):=.node [ze,zl8,zi,za,zt,zc,zl,zf] tree7_ll tree7_lr
def tree7_rllll:BTree (List W):=(.node [ze,zi,za,zyA,zt,zc,zl,zf] (.node [ze,zi,zBK,za,zt,zc,zl,zf] (.node [ze,zi,zp1,za,zt,zc,zl,zf] (.node [ze,zi,zw8,za,zt,zc,zl,zf] (.node [ze,zi,zBz,za,zt,zc,zl,zf] (.node [ze,zi,zdi,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zsw,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,ztr,za,zt,zc,zl,zf] (.node [ze,zi,zti,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zHa,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,zgp,zt,zc,zx,zl,zf] (.node [ze,zi,zgp,za,zt,zc,zl,zf] (.node [ze,zi,zse,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zgp,zip,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zG5,za,zt,zc,zl,zf] (.node [ze,zi,zFU,za,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zB3,zt,zc,zl,zf] (.node [ze,zi,zkB,za,zt,zc,zl,zf] (.node [ze,zi,zB2,za,zt,zc,zl,zf] (.node [ze,zi,zul,za,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zha,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zDu,za,zt,zc,zl,zf] (.node [ze,zi,zkB,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zBs,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zeF,zt,zc,zl,zf] (.node [ze,zi,za,zW,zt,zc,zl,zf] (.node [ze,zi,za,zzx,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zy7,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zDx,zt,zc,zl,zf] (.node [ze,zi,za,zGU,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zFC,zt,zc,zl,zf] (.node [ze,zi,za,zy1,zt,zc,zl,zf] (.node [ze,zi,za,zxa,zt,zc,zl,zf] (.node [ze,zi,za,zY,zt,zc,zl,zf] (.node [ze,zi,za,zAN,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zwx,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zsd,zt,zc,zl,zf] (.node [ze,zi,za,zE9,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,ztG,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zvZ,zt,zc,zl,zf] (.node [ze,zi,za,zsV,zt,zc,zl,zf] (.node [ze,zi,za,zxP,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zxK,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zzZ,zt,zc,zl,zf] (.node [ze,zi,za,zzl,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zBF,zt,zc,zl,zf] (.node [ze,zi,za,zcI,zt,zc,zl,zf] (.node [ze,zi,za,zwA,zt,zc,zl,zf] (.node [ze,zi,za,zE,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zAE,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zyn,zt,zc,zl,zf] (.node [ze,zi,za,zyH,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zEN,zt,zc,zl,zf] (.node [ze,zi,za,zdd,zt,zc,zl,zf] (.node [ze,zi,za,zxx,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zAL,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zip,zt,zc,zl,zf] (.node [ze,zi,za,zFo,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rlllr:BTree (List W):=(.node [ze,zi,za,zzB,zt,zc,zl,zf] (.node [ze,zi,za,zHk,zt,zc,zl,zf] (.node [ze,zi,za,zDE,zt,zc,zl,zf] (.node [ze,zi,za,zsq,zt,zc,zl,zf] (.node [ze,zi,za,zEF,zt,zc,zl,zf] (.node [ze,zi,za,zvs,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zCh,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zzy,zt,zc,zl,zf] (.node [ze,zi,za,zt0,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,ztV,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zug,zt,zl,zf,zv] (.node [ze,zi,za,zug,zt,zc,zl,zf] (.node [ze,zi,za,zug,zuh,zt,zl,zf] .nil .nil) (.node [ze,zi,za,zug,zt,zl,zs0,zf] .nil .nil)) (.node [ze,zi,za,zw9,zt,zc,zl,zf] (.node [ze,zi,za,zug,zc,zbJ,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zbW,zt,zc,zl,zf] (.node [ze,zi,za,zbm,zt,zl,zf] (.node [ze,zi,za,zbm,zb8,zt,zl,zf] (.node [ze,zi,za,zEb,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbm,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zBB,zt,zc,zl,zf] (.node [ze,zi,za,zuT,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbW,zbG,zt,zl,zf] .nil .nil))) (.node [ze,zi,za,zCU,zt,zc,zl,zf] (.node [ze,zi,za,zxr,zt,zc,zl,zf] (.node [ze,zi,za,zbW,zt,zl,zf] .nil .nil) (.node [ze,zi,za,zzs,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,ztw,zt,zc,zl,zf] (.node [ze,zi,za,zCP,zt,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zbf,zt,zc,zf] (.node [ze,zi,za,zbq,zc,zbJ,zl,zf] (.node [ze,zi,za,zbq,zb8,zc,zl,zf] (.node [ze,zi,za,zbq,zeO,zc,zl,zf] (.node [ze,zi,za,zbq,za5,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbq,zbG,zt,zc,zf] .nil .nil)) (.node [ze,zi,za,zbq,zt,zc,zf,zac] (.node [ze,zi,za,zbq,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbq,zdK,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zG7,zt,zc,zl,zf] (.node [ze,zi,za,zAp,zt,zc,zl,zf] (.node [ze,zi,za,zbq,zc,zl,zg0,zf] .nil .nil) (.node [ze,zi,za,zGx,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zbf,zt,zc,zl,zf] (.node [ze,zi,za,zbf,zb8,zt,zc,zf] .nil .nil) .nil))) (.node [ze,zi,za,za5,zb8,zt,zc,zl] (.node [ze,zi,za,zwH,zt,zc,zl,zf] (.node [ze,zi,za,zCl,zt,zc,zl,zf] (.node [ze,zi,za,zEA,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zs1,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,za5,zbG,zc,zl,zf] (.node [ze,zi,za,za5,zhO,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,za5,zc,zl,zf,zbe] (.node [ze,zi,za,za5,zt,zc,zl,zac] (.node [ze,zi,za,za5,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,za5,zbR,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zDQ,zt,zc,zl,zf] (.node [ze,zi,za,zBQ,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rlll:BTree (List W):=.node [ze,zi,za,zGr,zt,zc,zl,zf] tree7_rllll tree7_rlllr
def tree7_rllrl:BTree (List W):=(.node [ze,zi,za,zzK,zt,zc,zl,zf] (.node [ze,zi,za,zGg,zt,zc,zl,zf] (.node [ze,zi,za,zbP,zt,zc,zl] (.node [ze,zi,za,zbE,zt,zc,zl,zf] (.node [ze,zi,za,zGv,zt,zc,zl,zf] (.node [ze,zi,za,zCc,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zsB,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zbE,zc,zl,zf,zac] (.node [ze,zi,za,zbE,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbP,zbG,zt,zc,zl] .nil .nil))) (.node [ze,zi,za,ztz,zt,zc,zl,zf] (.node [ze,zi,za,zt4,zt,zc,zl,zf] (.node [ze,zi,za,zbP,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zwa,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zte,zt,zc,zl,zf] (.node [ze,zi,za,zxy,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zEx,zt,zc,zl,zf] (.node [ze,zi,za,zyd,zt,zc,zl,zf] (.node [ze,zi,za,zCA,zt,zc,zl,zf] (.node [ze,zi,za,zvd,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zy4,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zwS,zt,zc,zl,zf] (.node [ze,zi,za,zA6,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt3,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zuh,zt,zc,zl,zf] (.node [ze,zi,za,zum,zt,zc,zl,zf] (.node [ze,zi,za,zGQ,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zAR,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zuh,zc,zbJ,zl,zf] (.node [ze,zi,za,zuh,zt,zbJ,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zhO,zt,zc,zl,zf] (.node [ze,zi,za,zzr,zt,zc,zl,zf] (.node [ze,zi,za,zAY,zt,zc,zl,zf] (.node [ze,zi,za,zA7,zt,zc,zl,zf] (.node [ze,zi,za,zvU,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zyc,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zA1,zt,zc,zl,zf] (.node [ze,zi,za,zsT,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,ztx,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zhO,zeO,zc,zl,zf] (.node [ze,zi,za,zBI,zt,zc,zl,zf] (.node [ze,zi,za,zy8,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zCN,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zhO,zgX,zc,zl,zf] (.node [ze,zi,za,zhO,zb8,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zzN,zt,zc,zl,zf] (.node [ze,zi,za,zhO,zc,zl,zg0,zf] (.node [ze,zi,za,zhO,zdK,zc,zl,zf] (.node [ze,zi,za,zhO,zz5,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zhO,zc,zbJ,zl,zf] .nil .nil)) (.node [ze,zi,za,zDA,zt,zc,zl,zf] (.node [ze,zi,za,zHB,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zcJ,zc,zl,zf] (.node [ze,zi,za,zFf,zt,zc,zl,zf] (.node [ze,zi,za,zxv,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zcJ,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zHc,zt,zc,zl,zf] (.node [ze,zi,za,zDI,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rllrr:BTree (List W):=(.node [ze,zi,za,zbG,zt,zc,zg0,zf] (.node [ze,zi,za,zjN,zt,zc,zl,zf] (.node [ze,zi,za,zze,zt,zc,zl,zf] (.node [ze,zi,za,zeO,zz5,zc,zl,zf] (.node [ze,zi,za,zeO,zgX,zc,zl,zf] (.node [ze,zi,za,zeO,zbG,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zeO,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zeO,zc,zbJ,zl,zf] (.node [ze,zi,za,zeO,zbR,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zeO,zc,zl,zf,zbe] .nil .nil))) (.node [ze,zi,za,zc7,zc,zl,zf] (.node [ze,zi,za,zwc,zt,zc,zl,zf] (.node [ze,zi,za,zEI,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zc7,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zvl,zt,zc,zl,zf] (.node [ze,zi,za,zvE,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zES,zt,zc,zl,zf] (.node [ze,zi,za,zFZ,zt,zc,zl,zf] (.node [ze,zi,za,zAh,zt,zc,zl,zf] (.node [ze,zi,za,zjN,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zvS,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zAc,zt,zc,zl,zf] (.node [ze,zi,za,zwZ,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zbG,zt,zc,zl,zf] (.node [ze,zi,za,zbG,zb8,zc,zl,zf] (.node [ze,zi,za,zBm,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbG,zt,zc,zd9,zf] .nil .nil)) (.node [ze,zi,za,zbG,zt,zc,zV,zf] (.node [ze,zi,za,zbG,zt,zc,zl,zp] .nil .nil) .nil)))) (.node [ze,zi,za,zca,zt,zc,zl,zf] (.node [ze,zi,za,zr4,zt,zc,zl,zf] (.node [ze,zi,za,zbG,zc,zl,zg0,zf] (.node [ze,zi,za,zbG,zdK,zc,zl,zf] (.node [ze,zi,za,zbG,zt,zbY,zl,zf] .nil .nil) (.node [ze,zi,za,zbG,zc,zbJ,zl,zf] .nil .nil)) (.node [ze,zi,za,zlN,zt,zc,zl,zf] (.node [ze,zi,za,zFl,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zcb,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zGE,zt,zc,zl,zf] (.node [ze,zi,za,zaQ,zt,zc,zl,zf] (.node [ze,zi,za,ztc,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zaQ,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,ziK,zc,zl,zf] (.node [ze,zi,za,ziK,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zGd,zt,zc,zl,zf] (.node [ze,zi,za,zvg,zt,zc,zl,zf] (.node [ze,zi,za,zB,zt,zc,zl,zf] (.node [ze,zi,za,zca,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zB,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zy5,zt,zc,zl,zf] (.node [ze,zi,za,zxY,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zb8,zt,zc,zl,zbe] (.node [ze,zi,za,zb8,zt,zc,zl,zf] (.node [ze,zi,za,zb8,zt,zc,zl,zcv] .nil .nil) (.node [ze,zi,za,zb8,zt,zc,zl,zd] .nil .nil)) (.node [ze,zi,za,zb8,zt,zr,zl,zf] (.node [ze,zi,za,zb8,zt,zc,zo,zf] .nil .nil) .nil)))))
def tree7_rllr:BTree (List W):=.node [ze,zi,za,zFS,zt,zc,zl,zf] tree7_rllrl tree7_rllrr
def tree7_rll:BTree (List W):=.node [ze,zi,za,ztg,zt,zc,zl,zf] tree7_rlll tree7_rllr
def tree7_rlrll:BTree (List W):=(.node [ze,zi,za,zcp,zc,zl,zf] (.node [ze,zi,za,zh,zc,zl,zf,zac] (.node [ze,zi,za,zbQ,zc,zl,zf] (.node [ze,zi,za,zbp,zt,zc,zl,zf] (.node [ze,zi,za,zG6,zt,zc,zl,zf] (.node [ze,zi,za,zb8,zc,zl,zf,zbe] .nil .nil) (.node [ze,zi,za,zm2,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zsu,zt,zc,zl,zf] (.node [ze,zi,za,zsa,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbQ,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zBG,zt,zc,zl,zf] (.node [ze,zi,za,zCY,zt,zc,zl,zf] (.node [ze,zi,za,zuz,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zky,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zh,zc,zl,zf] (.node [ze,zi,za,zh,zt,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zCj,zt,zc,zl,zf] (.node [ze,zi,za,zgX,zc,zbJ,zl,zf] (.node [ze,zi,za,zgX,zbR,zc,zl,zf] (.node [ze,zi,za,zgX,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zgX,zdK,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zoD,zt,zc,zl,zf] (.node [ze,zi,za,zFA,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zv6,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zkn,zt,zc,zl,zf] (.node [ze,zi,za,zq2,zt,zc,zl,zf] (.node [ze,zi,za,zxN,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zmx,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zcp,zt,zc,zl,zf] (.node [ze,zi,za,zkn,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,ziN,zc,zl,zf] (.node [ze,zi,za,zt,zd5,zc,zl,zf] (.node [ze,zi,za,zt,zB0,zc,zl,zf] (.node [ze,zi,za,zob,zc,zl,zf] (.node [ze,zi,za,zob,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zDF,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zde,zc,zl,zf] (.node [ze,zi,za,zt,zjS,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,ztQ,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zyP,zc,zl,zf] (.node [ze,zi,za,zt,zEG,zc,zl,zf] (.node [ze,zi,za,zt,zzH,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zGC,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zuA,zc,zl,zf] (.node [ze,zi,za,zt,zz5,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zC7,zc,zl,zf] (.node [ze,zi,za,zt,zga,zc,zl,zf] (.node [ze,zi,za,zt,zsb,zc,zl,zf] (.node [ze,zi,za,zt,zsv,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zbU,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zaR,zc,zl,zf] (.node [ze,zi,za,zt,zGO,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zvG,zc,zl,zf] (.node [ze,zi,za,zt,zHi,zc,zl,zf] (.node [ze,zi,za,zt,zr5,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zja,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zDS,zc,zl,zf] (.node [ze,zi,za,zt,zbI,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rlrlr:BTree (List W):=(.node [ze,zi,za,zt,zE3,zc,zl,zf] (.node [ze,zi,za,zt,ztu,zc,zl,zf] (.node [ze,zi,za,zt,zbk,zc,zl,zf] (.node [ze,zi,za,zt,zEW,zc,zl,zf] (.node [ze,zi,za,zt,zU,zc,zf] (.node [ze,zi,za,zt,zU,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zN,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zAq,zc,zl,zf] (.node [ze,zi,za,zt,zq,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zGj,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zbR,zc,zl,zf] (.node [ze,zi,za,zt,zHp,zc,zl,zf] (.node [ze,zi,za,zt,zpI,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,z2,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,ztW,zc,zl,zf] (.node [ze,zi,za,zt,zG4,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zmo,zc,zl,zf] (.node [ze,zi,za,zt,zCE,zc,zl,zf] (.node [ze,zi,za,zt,zso,zc,zl,zf] (.node [ze,zi,za,zt,zvn,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zCH,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zAf,zc,zl,zf] (.node [ze,zi,za,zt,zzP,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zmo,zii,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zvw,zc,zl,zf] (.node [ze,zi,za,zt,zmo,zl,zf,zv] (.node [ze,zi,za,zt,zmo,z8,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zDi,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc9,zl,zf] (.node [ze,zi,za,zt,zc9,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zFD,zc,zl,zf] (.node [ze,zi,za,zt,zFJ,zc,zl,zf] (.node [ze,zi,za,zt,zu6,zc,zl,zf] (.node [ze,zi,za,zt,zFW,zc,zl,zf] (.node [ze,zi,za,zt,zDp,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zAC,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zyR,zc,zl,zf] (.node [ze,zi,za,zt,zyi,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zvu,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zuQ,zc,zs0,zf] (.node [ze,zi,za,zt,zuQ,zc,zl,zf] (.node [ze,zi,za,zt,zuQ,zc,zd9,zf] .nil .nil) (.node [ze,zi,za,zt,zuQ,zc,zV,zf] .nil .nil)) (.node [ze,zi,za,zt,zCm,zc,zl,zf] (.node [ze,zi,za,zt,zuQ,zc,zf,zac] .nil .nil) .nil))) (.node [ze,zi,za,zt,zCn,zc,zl,zf] (.node [ze,zi,za,zt,ztK,zc,zl,zf] (.node [ze,zi,za,zt,zc0,zc,zl,zf] (.node [ze,zi,za,zt,zuY,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc0,zc,zf] .nil .nil)) (.node [ze,zi,za,zt,ztZ,zc,zl,zf] (.node [ze,zi,za,zt,zx0,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc2,zc,zl,zv] (.node [ze,zi,za,zt,zc2,zc,zl,zf] (.node [ze,zi,za,zt,zc2,zc,zl,zcv] .nil .nil) (.node [ze,zi,za,zt,zc2,zc,zl,zd] .nil .nil)) (.node [ze,zi,za,zt,zFb,zc,zl,zf] (.node [ze,zi,za,zt,zFq,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rlrl:BTree (List W):=.node [ze,zi,za,zt,zU,zbR,zc,zf] tree7_rlrll tree7_rlrlr
def tree7_rlrrl:BTree (List W):=(.node [ze,zi,za,zt,zs,zc,zl,zf] (.node [ze,zi,za,zt,zuu,zc,zl,zf] (.node [ze,zi,za,zt,zDB,zc,zl,zf] (.node [ze,zi,za,zt,zsc,zc,zl,zf] (.node [ze,zi,za,zt,zxh,zc,zl,zf] (.node [ze,zi,za,zt,ztq,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zsC,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zvp,zc,zl,zf] (.node [ze,zi,za,zt,zHz,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,ztS,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zvo,zc,zl,zf] (.node [ze,zi,za,zt,zwf,zc,zl,zf] (.node [ze,zi,za,zt,zxT,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zvv,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zHq,zc,zl,zf] (.node [ze,zi,za,zt,zuW,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zF3,zc,zl,zf] (.node [ze,zi,za,zt,zH,zc,zl,zf] (.node [ze,zi,za,zt,zI,zc,zf] (.node [ze,zi,za,zt,zI,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zH,zc,zl] .nil .nil)) (.node [ze,zi,za,zt,zwG,zc,zl,zf] (.node [ze,zi,za,zt,zww,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zun,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zb2,zc,zl,zf] (.node [ze,zi,za,zt,zAi,zc,zl,zf] (.node [ze,zi,za,zt,zA,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zwt,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zfA,zc,zl,zf] (.node [ze,zi,za,zt,zEk,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zDf,zc,zl,zf] (.node [ze,zi,za,zt,zs6,zc,zl,zf] (.node [ze,zi,za,zt,zFn,zc,zl,zf] (.node [ze,zi,za,zt,zCz,zc,zl,zf] (.node [ze,zi,za,zt,zda,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zGw,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zvj,zc,zl,zf] (.node [ze,zi,za,zt,zdK,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zDt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zsS,zc,zs0,zf] (.node [ze,zi,za,zt,zAs,zc,zl,zf] (.node [ze,zi,za,zt,zBp,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zsS,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zCe,zc,zl,zf] (.node [ze,zi,za,zt,zsS,zl,zs0,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zyf,zc,zl,zf] (.node [ze,zi,za,zt,zDo,zc,zl,zf] (.node [ze,zi,za,zt,zr2,zc,zl,zf] (.node [ze,zi,za,zt,zyI,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zBH,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zyf,zii,zl,zf] (.node [ze,zi,za,zt,zFK,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zHg,zc,zl,zf] (.node [ze,zi,za,zt,zyf,zl,zs0,zf] (.node [ze,zi,za,zt,zyf,z8,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zEL,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zCO,zc,zl,zf] (.node [ze,zi,za,zt,zGM,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rlrrr:BTree (List W):=(.node [ze,zi,za,zt,zii,zc,zl,zf] (.node [ze,zi,za,zt,zsH,zl,zf,zv] (.node [ze,zi,za,zt,zDY,zc,zl,zf] (.node [ze,zi,za,zt,zzb,zc,zl,zf] (.node [ze,zi,za,zt,zzW,zc,zl,zf] (.node [ze,zi,za,zt,ztD,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zu5,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zFv,zc,zl,zf] (.node [ze,zi,za,zt,zvi,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zF8,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zsH,zc,zl,zf] (.node [ze,zi,za,zt,zzw,zc,zl,zf] (.node [ze,zi,za,zt,zHD,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zxL,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zsH,zc,zax,zf] (.node [ze,zi,za,zt,zsH,zc,zl,zv] .nil .nil) .nil))) (.node [ze,zi,za,zt,zgk,zl,zf] (.node [ze,zi,za,zt,zr9,zc,zl,zf] (.node [ze,zi,za,zt,zvm,zc,zl,zf] (.node [ze,zi,za,zt,zpN,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zaF,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zgk,zc,zl,zf] (.node [ze,zi,za,zt,zDC,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,ztp,zc,zl,zf] (.node [ze,zi,za,zt,zCX,zc,zl,zf] (.node [ze,zi,za,zt,zBl,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zps,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zBf,zc,zl,zf] (.node [ze,zi,za,zt,zEM,zc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zw2,zl,zf] (.node [ze,zi,za,zt,zkS,zc,zl,zf] (.node [ze,zi,za,zt,zFw,zc,zl,zf] (.node [ze,zi,za,zt,zii,zcl,zl,zf] (.node [ze,zi,za,zt,zii,zx,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zGR,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zAg,zc,zl,zf] (.node [ze,zi,za,zt,zFa,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zBY,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zBq,zl,zf] (.node [ze,zi,za,zt,zof,zl,zf] (.node [ze,zi,za,zt,zof,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zD3,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zgz,zl,zf] (.node [ze,zi,za,zt,zc,zHC,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,z8,zl,zf] (.node [ze,zi,za,zt,zc,zFB,zl,zf] (.node [ze,zi,za,zt,zc,zR,zl,zf] (.node [ze,zi,za,zt,zc,zAJ,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zD0,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zCk,zl,zf] (.node [ze,zi,za,zt,zc,zE5,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zzc,zl,zf] (.node [ze,zi,za,zt,zc,zth,zl,zf] (.node [ze,zi,za,zt,zc,zux,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zw6,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zua,zl,zf] (.node [ze,zi,za,zt,zc,zGY,zl,zf] .nil .nil) .nil)))))
def tree7_rlrr:BTree (List W):=.node [ze,zi,za,zt,zxt,zc,zl,zf] tree7_rlrrl tree7_rlrrr
def tree7_rlr:BTree (List W):=.node [ze,zi,za,zt,zuv,zc,zl,zf] tree7_rlrl tree7_rlrr
def tree7_rl:BTree (List W):=.node [ze,zi,za,zb8,zbR,zc,zl,zf] tree7_rll tree7_rlr
def tree7_rrlll:BTree (List W):=(.node [ze,zi,za,zt,zc,zts,zl,zf] (.node [ze,zi,za,zt,zc,zyC,zl,zf] (.node [ze,zi,za,zt,zc,zzq,zl,zf] (.node [ze,zi,za,zt,zc,zFP,zl,zf] (.node [ze,zi,za,zt,zc,zr3,zl,zf] (.node [ze,zi,za,zt,zc,zuf,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zvV,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zy9,zl,zf] (.node [ze,zi,za,zt,zc,zuO,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zBg,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zpz,zl,zf] (.node [ze,zi,za,zt,zc,zk6,zl,zf] (.node [ze,zi,za,zt,zc,zk6,zd9,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zk6,zV,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zpE,zl,zf] (.node [ze,zi,za,zt,zc,zDs,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zwU,zl,zd] (.node [ze,zi,za,zt,zc,zvb,zl,zf] (.node [ze,zi,za,zt,zc,zEt,zl,zf] (.node [ze,zi,za,zt,zc,zxp,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zuG,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zwU,zl,zcv] (.node [ze,zi,za,zt,zc,zGI,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zwU,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zpD,zl,zf] (.node [ze,zi,za,zt,zc,zwU,zcu,zf] (.node [ze,zi,za,zt,zc,zwU,zl,zac] .nil .nil) (.node [ze,zi,za,zt,zc,zqF,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zz1,zl,zf] (.node [ze,zi,za,zt,zc,zcc,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zzO,zl,zf] (.node [ze,zi,za,zt,zc,zwk,zl,zf] (.node [ze,zi,za,zt,zc,zyz,zl,zf] (.node [ze,zi,za,zt,zc,zBx,zl,zf] (.node [ze,zi,za,zt,zc,zsD,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zxF,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zgb,zl] (.node [ze,zi,za,zt,zc,zwW,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zgb,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zAS,zl,zf] (.node [ze,zi,za,zt,zc,zyw,zl,zf] (.node [ze,zi,za,zt,zc,zAe,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zty,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zFu,zl,zf] (.node [ze,zi,za,zt,zc,zvR,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zAU,zl,zf] (.node [ze,zi,za,zt,zc,zuU,zl,zf] (.node [ze,zi,za,zt,zc,zCi,zl,zf] (.node [ze,zi,za,zt,zc,zwb,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zzE,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zus,zl,zf] (.node [ze,zi,za,zt,zc,zF1,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zwQ,zl,zf] (.node [ze,zi,za,zt,zc,ztO,zl,zf] (.node [ze,zi,za,zt,zc,zuP,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zyp,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zwd,zl,zf] (.node [ze,zi,za,zt,zc,zAW,zl,zf] .nil .nil) .nil)))))
def tree7_rrllr:BTree (List W):=(.node [ze,zi,za,zt,zc,zHv,zl,zf] (.node [ze,zi,za,zt,zc,zHs,zl,zf] (.node [ze,zi,za,zt,zc,zD9,zl,zf] (.node [ze,zi,za,zt,zc,zaB,zl,zf] (.node [ze,zi,za,zt,zc,zxM,zl,zf] (.node [ze,zi,za,zt,zc,zyv,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zvN,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zvX,zl,zf] (.node [ze,zi,za,zt,zc,zc1,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zB9,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zxG,zl,zf] (.node [ze,zi,za,zt,zc,zFM,zl,zf] (.node [ze,zi,za,zt,zc,zx,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zAo,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zxA,zl,zf] (.node [ze,zi,za,zt,zc,zx4,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zv0,zl,zf] (.node [ze,zi,za,zt,zc,zbY,zl,zf] (.node [ze,zi,za,zt,zc,zs8,zl,zf] (.node [ze,zi,za,zt,zc,zue,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zyt,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zay,zl,zf] (.node [ze,zi,za,zt,zc,zro,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zr,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zEu,zl,zf] (.node [ze,zi,za,zt,zc,zDZ,zl,zf] (.node [ze,zi,za,zt,zc,zCW,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zbJ,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zDX,zl,zf] (.node [ze,zi,za,zt,zc,zzf,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zBo,zl,zf] (.node [ze,zi,za,zt,zc,zxu,zl,zf] (.node [ze,zi,za,zt,zc,zDL,zl,zf] (.node [ze,zi,za,zt,zc,zyg,zl,zf] (.node [ze,zi,za,zt,zc,zwY,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zyQ,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zyL,zl,zf] (.node [ze,zi,za,zt,zc,zgn,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zaD,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zcl,zl,zf] (.node [ze,zi,za,zt,zc,zzv,zl,zf] (.node [ze,zi,za,zt,zc,zGo,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zHm,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zDg,zl,zf] (.node [ze,zi,za,zt,zc,zEY,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zak,zl,zf] (.node [ze,zi,za,zt,zc,zsg,zf,zac] (.node [ze,zi,za,zt,zc,zsg,zl,zf] (.node [ze,zi,za,zt,zc,zvW,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zsg,zl,zac] .nil .nil)) (.node [ze,zi,za,zt,zc,zAk,zl,zf] (.node [ze,zi,za,zt,zc,zDa,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zx7,zl,zf] (.node [ze,zi,za,zt,zc,zw4,zl,zf] (.node [ze,zi,za,zt,zc,zss,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zyX,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zuH,zl,zf] (.node [ze,zi,za,zt,zc,zDh,zl,zf] .nil .nil) .nil)))))
def tree7_rrll:BTree (List W):=.node [ze,zi,za,zt,zc,zs9,zl,zf] tree7_rrlll tree7_rrllr
def tree7_rrlrl:BTree (List W):=(.node [ze,zi,za,zt,zc,zl,zc6,zf] (.node [ze,zi,za,zt,zc,ze9,zf] (.node [ze,zi,za,zt,zc,zkM,zl,zf] (.node [ze,zi,za,zt,zc,zd9,zu4,zf] (.node [ze,zi,za,zt,zc,zxo,zl,zf] (.node [ze,zi,za,zt,zc,zxg,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zd9,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zd9,zs0,zf] (.node [ze,zi,za,zt,zc,zd9,zgN,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zd9,zf,zac] .nil .nil))) (.node [ze,zi,za,zt,zc,zl1,zf] (.node [ze,zi,za,zt,zc,zDm,zl,zf] (.node [ze,zi,za,zt,zc,zkM,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl1,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,ze9,zl,zf] (.node [ze,zi,za,zt,zc,zmY,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zGm,zf] (.node [ze,zi,za,zt,zc,zER,zl,zf] (.node [ze,zi,za,zt,zc,zho,zl,zf] (.node [ze,zi,za,zt,zc,zC5,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zho,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zmc,zf] (.node [ze,zi,za,zt,zc,zmc,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zlU,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zC6,zf] (.node [ze,zi,za,zt,zc,zl,zEn,zf] (.node [ze,zi,za,zt,zc,zl,zdm,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zab,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zpQ,zf] (.node [ze,zi,za,zt,zc,zl,zhS,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zl,zzi,zf] (.node [ze,zi,za,zt,zc,zl,zvA,zf] (.node [ze,zi,za,zt,zc,zl,zFr,zf] (.node [ze,zi,za,zt,zc,zl,zke,zf] (.node [ze,zi,za,zt,zc,zl,zFz,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zV,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zE1,zf] (.node [ze,zi,za,zt,zc,zl,zCI,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zst,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zsn,zf] (.node [ze,zi,za,zt,zc,zl,zyF,zf] (.node [ze,zi,za,zt,zc,zl,zz9,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zsP,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zHh,zf] (.node [ze,zi,za,zt,zc,zl,zCF,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,ztC,zf] (.node [ze,zi,za,zt,zc,zl,zzL,zf] (.node [ze,zi,za,zt,zc,zl,zcu,zf] (.node [ze,zi,za,zt,zc,zl,zt2,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zyU,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,ztY,zf] (.node [ze,zi,za,zt,zc,zl,zFs,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zAj,zf] (.node [ze,zi,za,zt,zc,zl,zEZ,zf] (.node [ze,zi,za,zt,zc,zl,ztd,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zCT,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zAy,zf] (.node [ze,zi,za,zt,zc,zl,zET,zf] .nil .nil) .nil)))))
def tree7_rrlrr:BTree (List W):=(.node [ze,zi,za,zt,zc,zl,zgN,zf] (.node [ze,zi,za,zt,zc,zl,zo,zf] (.node [ze,zi,za,zt,zc,zl,zFg,zf] (.node [ze,zi,za,zt,zc,zl,zsm,zf] (.node [ze,zi,za,zt,zc,zl,zy,zf] (.node [ze,zi,za,zt,zc,zl,zzJ,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zvf,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zCZ,zf] (.node [ze,zi,za,zt,zc,zl,zc8,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zFx,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zCg,zf] (.node [ze,zi,za,zt,zc,zl,zx1,zf] (.node [ze,zi,za,zt,zc,zl,zu4,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zzR,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zsk,zf] (.node [ze,zi,za,zt,zc,zl,ztI,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zDq,zf] (.node [ze,zi,za,zt,zc,zl,zg0,zf] (.node [ze,zi,za,zt,zc,zl,zBP,zf] (.node [ze,zi,za,zt,zc,zl,zx3,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zDV,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zws,zf] (.node [ze,zi,za,zt,zc,zl,zEr,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zDw,zf] (.node [ze,zi,za,zt,zc,zl,zwE,zf] (.node [ze,zi,za,zt,zc,zl,zxX,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zxs,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zwL,zf] (.node [ze,zi,za,zt,zc,zl,zBT,zf] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zl,zcv,zf] (.node [ze,zi,za,zt,zc,zl,zCJ,zf] (.node [ze,zi,za,zt,zc,zl,zsZ,zf] (.node [ze,zi,za,zt,zc,zl,zF5,zf] (.node [ze,zi,za,zt,zc,zl,zGV,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zzu,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zax,zf] (.node [ze,zi,za,zt,zc,zl,zsi,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zs3,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zvQ,zf] (.node [ze,zi,za,zt,zc,zl,zs0,zf] (.node [ze,zi,za,zt,zc,zl,zCS,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zDe,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zyN,zf] (.node [ze,zi,za,zt,zc,zl,zud,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,znP,zf] (.node [ze,zi,za,zt,zc,zl,zcv,zac] (.node [ze,zi,za,zt,zc,zl,zcv,zw3] (.node [ze,zi,za,zt,zc,zl,zcv,z6] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zcv,zv] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zpC,zf] (.node [ze,zi,za,zt,zc,zl,zpC] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zlh] (.node [ze,zi,za,zt,zc,zl,zg8,zf] (.node [ze,zi,za,zt,zc,zl,zg8] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zED,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zkX,zf] (.node [ze,zi,za,zt,zc,zl,zlh,zf] .nil .nil) .nil)))))
def tree7_rrlr:BTree (List W):=.node [ze,zi,za,zt,zc,zl,zwN,zf] tree7_rrlrl tree7_rrlrr
def tree7_rrl:BTree (List W):=.node [ze,zi,za,zt,zc,ztn,zl,zf] tree7_rrll tree7_rrlr
def tree7_rrrll:BTree (List W):=(.node [ze,zi,za,zt,zc,zl,zf,zvT] (.node [ze,zi,za,zt,zc,zl,zf,zgM] (.node [ze,zi,za,zt,zc,zl,zf,zD2] (.node [ze,zi,za,zt,zc,zl,zdn,zf] (.node [ze,zi,za,zt,zc,zl,zAF,zf] (.node [ze,zi,za,zt,zc,zl,zcR,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zdn] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zGs] (.node [ze,zi,za,zt,zc,zl,zkq,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zkp] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zf,zAu] (.node [ze,zi,za,zt,zc,zl,zf,zC3] (.node [ze,zi,za,zt,zc,zl,zf,zcq] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zbX] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zFy] (.node [ze,zi,za,zt,zc,zl,zf,zls] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zf,zyB] (.node [ze,zi,za,zt,zc,zl,zf,zu0] (.node [ze,zi,za,zt,zc,zl,zf,zCR] (.node [ze,zi,za,zt,zc,zl,zf,zd] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zxJ] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zvx] (.node [ze,zi,za,zt,zc,zl,zf,zsR] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zzD] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zf,zyo] (.node [ze,zi,za,zt,zc,zl,zf,zxf] (.node [ze,zi,za,zt,zc,zl,zf,zzF] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zGh] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zwg] (.node [ze,zi,za,zt,zc,zl,zf,zyh] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zl,zf,zDU] (.node [ze,zi,za,zt,zc,zl,zf,zAO] (.node [ze,zi,za,zt,zc,zl,zf,zAm] (.node [ze,zi,za,zt,zc,zl,zf,zyr] (.node [ze,zi,za,zt,zc,zl,zf,ztU] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zGn] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zA2] (.node [ze,zi,za,zt,zc,zl,zf,zBZ] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zEP] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zf,zyl] (.node [ze,zi,za,zt,zc,zl,zf,zu3] (.node [ze,zi,za,zt,zc,zl,zf,zz] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zuL] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,z6] (.node [ze,zi,za,zt,zc,zl,zf,zFe] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zf,zbe] (.node [ze,zi,za,zt,zc,zl,zf,ztt] (.node [ze,zi,za,zt,zc,zl,zf,zuk] (.node [ze,zi,za,zt,zc,zl,zf,zCt] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zp] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zDT] (.node [ze,zi,za,zt,zc,zl,zf,zBi] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zcm] (.node [ze,zi,za,zt,zc,zl,zf,zBa] (.node [ze,zi,za,zt,zc,zl,zf,zEs] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zyW] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zCu] (.node [ze,zi,za,zt,zc,zl,zf,zxl] .nil .nil) .nil)))))
def tree7_rrrlr:BTree (List W):=(.node [ze,zi,za,zt,zc,zl,zd,zv] (.node [ze,zi,za,zt,zc,zl,zf,zA5] (.node [ze,zi,za,zt,zc,zl,zf,zxH] (.node [ze,zi,za,zt,zc,zl,zf,zzM] (.node [ze,zi,za,zt,zc,zl,zf,zyj] (.node [ze,zi,za,zt,zc,zl,zf,zw3] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zFL] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zsF] (.node [ze,zi,za,zt,zc,zl,zf,zA3] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zB1] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zf,zuc] (.node [ze,zi,za,zt,zc,zl,zf,zFi] (.node [ze,zi,za,zt,zc,zl,zf,zv] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zCd] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zF0] (.node [ze,zi,za,zt,zc,zl,zf,zD7] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zl,zkp] (.node [ze,zi,za,zt,zc,zl,zf,zyD] (.node [ze,zi,za,zt,zc,zl,zf,zac] (.node [ze,zi,za,zt,zc,zl,zf,zGS] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zB8] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zve] (.node [ze,zi,za,zt,zc,zl,zf,zzn] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zf,zsY] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zgM] (.node [ze,zi,za,zt,zc,zl,zbX] (.node [ze,zi,za,zt,zc,zl,zcq] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zls] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zd,zw3] (.node [ze,zi,za,zt,zc,zl,zd,z6] .nil .nil) .nil)))) (.node [ze,zi,za,zt,zc,zV,zs0,zf] (.node [ze,zi,za,zt,zc,zdm,zf] (.node [ze,zi,za,zt,zc,zl,zp] (.node [ze,zi,za,zt,zc,zl,zz] (.node [ze,zi,za,zt,zc,zl,zd,zac] .nil .nil) (.node [ze,zi,za,zt,zc,zl,z6,zv] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zcm] (.node [ze,zi,za,zt,zc,zl,zbe,zac] .nil .nil) (.node [ze,zi,za,zt,zc,zl,zw3,zac] .nil .nil))) (.node [ze,zi,za,zt,zc,zke,zf] (.node [ze,zi,za,zt,zc,zhS,zf] (.node [ze,zi,za,zt,zc,zab,zf] .nil .nil) (.node [ze,zi,za,zt,zc,zc6,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zV,zgN,zf] (.node [ze,zi,za,zt,zc,zV,zu4,zf] .nil .nil) .nil))) (.node [ze,zi,za,zt,zc,zo,zf] (.node [ze,zi,za,zt,zc,zc8,zf] (.node [ze,zi,za,zt,zc,zcu,zf] (.node [ze,zi,za,zt,zc,zV,zf,zac] .nil .nil) (.node [ze,zi,za,zt,zc,zy,zf] .nil .nil)) (.node [ze,zi,za,zt,zc,zu4,zf,zac] (.node [ze,zi,za,zt,zc,zu4,zs0,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zgz,zl,zf] (.node [ze,zi,za,zt,zc,zax,zf] (.node [ze,zi,za,zt,zc,zg0,zf,zac] .nil .nil) (.node [ze,zi,za,zt,zc,zs0,zf,zac] .nil .nil)) (.node [ze,zi,za,zt,z8,zx,zl,zf] (.node [ze,zi,za,zt,zR,zl,zf] .nil .nil) .nil)))))
def tree7_rrrl:BTree (List W):=.node [ze,zi,za,zt,zc,zl,zf,zFt] tree7_rrrll tree7_rrrlr
def tree7_rrrrl:BTree (List W):=(.node [ze,zi,za,zc,zbJ,zl,zf,zbe] (.node [ze,zi,za,ziN,zc,zl,zf] (.node [ze,zi,za,zt,zcl,zl,zs0,zf] (.node [ze,zi,za,zt,zr,zl,zf] (.node [ze,zi,za,zt,zx,zl,zf,zv] (.node [ze,zi,za,zt,zc1,zl,zf] .nil .nil) (.node [ze,zi,za,zt,zbY,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zbJ,zl,zf,zv] (.node [ze,zi,za,zt,zbJ,zl,zs0,zf] .nil .nil) (.node [ze,zi,za,zt,zgn,zl,zf] .nil .nil))) (.node [ze,zi,za,zz5,zbR,zc,zl,zf] (.node [ze,zi,za,zde,zc,zl,zf] (.node [ze,zi,za,zjS,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zd5,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zz5,zc,zbJ,zl,zf] (.node [ze,zi,za,zz5,zdK,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zi,za,zbR,zc,zl,zg0,zf] (.node [ze,zi,za,zja,zc,zl,zf] (.node [ze,zi,za,zga,zc,zl,zf] (.node [ze,zi,za,zbU,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zaR,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zbR,zdK,zc,zl,zf] (.node [ze,zi,za,zN,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zbR,zc,zbJ,zl,zf] .nil .nil))) (.node [ze,zi,za,zdK,zc,zl,zf,zbe] (.node [ze,zi,za,zda,zc,zl,zf] (.node [ze,zi,za,zA,zc,zl,zf] .nil .nil) (.node [ze,zi,za,zdK,zc,zbJ,zl,zf] .nil .nil)) (.node [ze,zi,za,zc,zay,zl,zf] (.node [ze,zi,za,zsH,zc,zay,zl,zf] .nil .nil) .nil)))) (.node [ze,zi,zt,zdK,zc,zl,zu4,zf] (.node [ze,zi,zbG,zt,zb2,zc,zl,zf] (.node [ze,zi,zY,zt,zc,zx,zl,zf] (.node [ze,zi,zeF,zt,zc,zl,zf] (.node [ze,zi,zW,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zY,zip,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zip,zt,zc,zl,zu4,zf] (.node [ze,zi,zcI,zt,zc,zl,zf] .nil .nil) (.node [ze,zi,zeO,zt,zdK,zc,zl,zf] .nil .nil))) (.node [ze,zi,zt,zc2,zc,zl,zf,z6] (.node [ze,zi,zt,zmo,zc,zx,zl,zf] (.node [ze,zi,zb8,zt,zs,zc,zl,zf] .nil .nil) (.node [ze,zi,zt,zuQ,zc,zl,zu4,zf] .nil .nil)) (.node [ze,zi,zt,zs,zc,zl,zf] (.node [ze,zi,zt,zb2,zc,zl,zf] .nil .nil) .nil))) (.node [ze,zkO,za,zip,zt,zc,zl,zf] (.node [ze,zi,zt,zc,zx,zl,zf,z6] (.node [ze,zi,zt,zsH,zc,zaB,zl,zf] (.node [ze,zi,zt,zdK,zc,zl,zf,z6] .nil .nil) (.node [ze,zi,zt,zc,zaB,zl,zf] .nil .nil)) (.node [ze,zeE,za,zt,zc,zl,zf] (.node [ze,ze8,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zfQ,za,zt,zc,zl,zf] (.node [ze,zdx,za,zt,zc,zl,zf] (.node [ze,zkO,za,zt,zc,zcl,zl,zf] .nil .nil) (.node [ze,zaS,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,ztB,za,zip,zt,zc,zl,zf] (.node [ze,zek,za,zE,zt,zc,zl,zf] .nil .nil) .nil)))))
def tree7_rrrrr:BTree (List W):=(.node [zM,zi,za,zt,zc,zl,zf] (.node [ze,za,zt,z2,zc,zl,zf] (.node [ze,za,zhO,zt,zbR,zc,zl,zf] (.node [ze,za,zip,zt,zc,zk6,zl,zf] (.node [ze,za,zdd,zt,zc,zl,zf] (.node [ze,za,zE,zt,zc,zl,zf] .nil .nil) (.node [ze,za,zip,zt,zbR,zc,zl,zf] .nil .nil)) (.node [ze,za,zip,zt,zc,zl,zf,zw3] (.node [ze,za,zip,zt,zc,zcl,zl,zf] .nil .nil) (.node [ze,za,zuh,zt,zbI,zc,zl,zf] .nil .nil))) (.node [ze,za,zt,zbI,zc,zl,zf] (.node [ze,za,zb8,zt,zbk,zc,zl,zf] (.node [ze,za,zbG,zt,zq,zc,zl,zf] .nil .nil) (.node [ze,za,zgX,zt,z2,zc,zl,zf] .nil .nil)) (.node [ze,za,zt,zbk,zc,zl,zf] (.node [ze,za,zt,zq,zc,zl,zf] .nil .nil) .nil))) (.node [ze,za,zt,zc,zk6,zl,zgN,zf] (.node [ze,za,zt,zyf,zc,zcl,zl,zf] (.node [ze,za,zt,zbR,zc,zl,zgN,zf] (.node [ze,za,zt,zbR,zc,zcl,zl,zf] .nil .nil) (.node [ze,za,zt,zbR,zc,zl,zf,zw3] .nil .nil)) (.node [ze,za,zt,zc,zk6,zcl,zl,zf] (.node [ze,za,zt,zsH,zc,zaD,zl,zf] .nil .nil) .nil)) (.node [ze,za,zt,zc,zaD,zl,zf] (.node [ze,za,zt,zc,zpz,zl,zf] (.node [ze,za,zt,zc,zpz,zl,zV,zf] .nil .nil) (.node [ze,za,zt,zc,zwU,zl,zf,zw3] .nil .nil)) (.node [zc4,zM,zi,za,zt,zc,zl,zf] (.node [ze,za,zt,zc,zcl,zl,zf,zw3] .nil .nil) .nil)))) (.node [zi,za,zgX,zt,zz5,zc,zl,zf] (.node [zi,zgp,za,zY,zt,zc,zl,zf] (.node [zi,zek,zF,za,zt,zc,zl,zf] (.node [zgP,zi,za,zt,zc,zl,zf,zd] (.node [zgP,zi,zkO,za,zt,zc,zl,zf] .nil .nil) (.node [zi,zkO,za,zt,zc,zl,zV,zf] .nil .nil)) (.node [zi,zuB,zdi,za,zt,zc,zl,zf] (.node [zi,zF,za,zt,zc,zl,zf] .nil .nil) (.node [zi,zdi,za,zt,zc,zl,zf] .nil .nil))) (.node [zi,za,zcb,zt,zc,zl,zf] (.node [zi,za,zY,zt,zc,zl,zf,zd] (.node [zi,za,zY,zt,zc,z8,zl,zf] .nil .nil) (.node [zi,za,zbG,zcb,zt,zc,zl,zf] .nil .nil)) (.node [zi,za,zbp,zt,zc,zl,zf] (.node [zi,za,zb8,zbp,zt,zc,zl,zf] .nil .nil) .nil))) (.node [zi,za,zt,zc,zwU,zcc,zl,zf] (.node [zi,za,zt,zaF,zc,zl,zf] (.node [zi,za,zt,zz5,zc,zl,zf,zd] (.node [zi,za,zt,zz5,zc,zl,zV,zf] .nil .nil) (.node [zi,za,zt,zsH,zaF,zc,zl,zf] .nil .nil)) (.node [zi,za,zt,zc,z8,zl,zf,zd] (.node [zi,za,zt,zii,zc,z8,zl,zf] .nil .nil) .nil)) (.node [zi,za,zt,zc,zd9,zl,zV,zf] (.node [zi,za,zt,zc,zsg,zak,zl,zf] (.node [zi,za,zt,zc,zcc,zl,zf] .nil .nil) (.node [zi,za,zt,zc,zak,zl,zf] .nil .nil)) (.node [zi,za,zt,zc,zl,zcv,zf,zd] (.node [zi,za,zt,zc,zl,zV,zf,zd] .nil .nil) .nil)))))
def tree7_rrrr:BTree (List W):=.node [ze,zuB,za,zdd,zt,zc,zl,zf] tree7_rrrrl tree7_rrrrr
def tree7_rrr:BTree (List W):=.node [ze,zi,za,zt,z8,zcl,zl,zf] tree7_rrrl tree7_rrrr
def tree7_rr:BTree (List W):=.node [ze,zi,za,zt,zc,zl,zcR] tree7_rrl tree7_rrr
def tree7_r:BTree (List W):=.node [ze,zi,za,zt,zc,zxO,zl,zf] tree7_rl tree7_rr
def tree7:BTree (List W):=.node [ze,zi,zFF,za,zt,zc,zl,zf] tree7_l tree7_r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lllll:everyKey (certRow 6 tree6) tree7_lllll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llllr:everyKey (certRow 6 tree6) tree7_llllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llll:everyKey (certRow 6 tree6) tree7_llll=true:=splitCheck (by decide +kernel) ok_tree7_lllll ok_tree7_llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lllrl:everyKey (certRow 6 tree6) tree7_lllrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lllrr:everyKey (certRow 6 tree6) tree7_lllrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lllr:everyKey (certRow 6 tree6) tree7_lllr=true:=splitCheck (by decide +kernel) ok_tree7_lllrl ok_tree7_lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lll:everyKey (certRow 6 tree6) tree7_lll=true:=splitCheck (by decide +kernel) ok_tree7_llll ok_tree7_lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llrll:everyKey (certRow 6 tree6) tree7_llrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llrlr:everyKey (certRow 6 tree6) tree7_llrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llrl:everyKey (certRow 6 tree6) tree7_llrl=true:=splitCheck (by decide +kernel) ok_tree7_llrll ok_tree7_llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llrrl:everyKey (certRow 6 tree6) tree7_llrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llrrr:everyKey (certRow 6 tree6) tree7_llrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llrr:everyKey (certRow 6 tree6) tree7_llrr=true:=splitCheck (by decide +kernel) ok_tree7_llrrl ok_tree7_llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_llr:everyKey (certRow 6 tree6) tree7_llr=true:=splitCheck (by decide +kernel) ok_tree7_llrl ok_tree7_llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_ll:everyKey (certRow 6 tree6) tree7_ll=true:=splitCheck (by decide +kernel) ok_tree7_lll ok_tree7_llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrlll:everyKey (certRow 6 tree6) tree7_lrlll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrllr:everyKey (certRow 6 tree6) tree7_lrllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrll:everyKey (certRow 6 tree6) tree7_lrll=true:=splitCheck (by decide +kernel) ok_tree7_lrlll ok_tree7_lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrlrl:everyKey (certRow 6 tree6) tree7_lrlrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrlrr:everyKey (certRow 6 tree6) tree7_lrlrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrlr:everyKey (certRow 6 tree6) tree7_lrlr=true:=splitCheck (by decide +kernel) ok_tree7_lrlrl ok_tree7_lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrl:everyKey (certRow 6 tree6) tree7_lrl=true:=splitCheck (by decide +kernel) ok_tree7_lrll ok_tree7_lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrrll:everyKey (certRow 6 tree6) tree7_lrrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrrlr:everyKey (certRow 6 tree6) tree7_lrrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrrl:everyKey (certRow 6 tree6) tree7_lrrl=true:=splitCheck (by decide +kernel) ok_tree7_lrrll ok_tree7_lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrrrl:everyKey (certRow 6 tree6) tree7_lrrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrrrr:everyKey (certRow 6 tree6) tree7_lrrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrrr:everyKey (certRow 6 tree6) tree7_lrrr=true:=splitCheck (by decide +kernel) ok_tree7_lrrrl ok_tree7_lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lrr:everyKey (certRow 6 tree6) tree7_lrr=true:=splitCheck (by decide +kernel) ok_tree7_lrrl ok_tree7_lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_lr:everyKey (certRow 6 tree6) tree7_lr=true:=splitCheck (by decide +kernel) ok_tree7_lrl ok_tree7_lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_l:everyKey (certRow 6 tree6) tree7_l=true:=splitCheck (by decide +kernel) ok_tree7_ll ok_tree7_lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rllll:everyKey (certRow 6 tree6) tree7_rllll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlllr:everyKey (certRow 6 tree6) tree7_rlllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlll:everyKey (certRow 6 tree6) tree7_rlll=true:=splitCheck (by decide +kernel) ok_tree7_rllll ok_tree7_rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rllrl:everyKey (certRow 6 tree6) tree7_rllrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rllrr:everyKey (certRow 6 tree6) tree7_rllrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rllr:everyKey (certRow 6 tree6) tree7_rllr=true:=splitCheck (by decide +kernel) ok_tree7_rllrl ok_tree7_rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rll:everyKey (certRow 6 tree6) tree7_rll=true:=splitCheck (by decide +kernel) ok_tree7_rlll ok_tree7_rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlrll:everyKey (certRow 6 tree6) tree7_rlrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlrlr:everyKey (certRow 6 tree6) tree7_rlrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlrl:everyKey (certRow 6 tree6) tree7_rlrl=true:=splitCheck (by decide +kernel) ok_tree7_rlrll ok_tree7_rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlrrl:everyKey (certRow 6 tree6) tree7_rlrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlrrr:everyKey (certRow 6 tree6) tree7_rlrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlrr:everyKey (certRow 6 tree6) tree7_rlrr=true:=splitCheck (by decide +kernel) ok_tree7_rlrrl ok_tree7_rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rlr:everyKey (certRow 6 tree6) tree7_rlr=true:=splitCheck (by decide +kernel) ok_tree7_rlrl ok_tree7_rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rl:everyKey (certRow 6 tree6) tree7_rl=true:=splitCheck (by decide +kernel) ok_tree7_rll ok_tree7_rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrlll:everyKey (certRow 6 tree6) tree7_rrlll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrllr:everyKey (certRow 6 tree6) tree7_rrllr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrll:everyKey (certRow 6 tree6) tree7_rrll=true:=splitCheck (by decide +kernel) ok_tree7_rrlll ok_tree7_rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrlrl:everyKey (certRow 6 tree6) tree7_rrlrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrlrr:everyKey (certRow 6 tree6) tree7_rrlrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrlr:everyKey (certRow 6 tree6) tree7_rrlr=true:=splitCheck (by decide +kernel) ok_tree7_rrlrl ok_tree7_rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrl:everyKey (certRow 6 tree6) tree7_rrl=true:=splitCheck (by decide +kernel) ok_tree7_rrll ok_tree7_rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrrll:everyKey (certRow 6 tree6) tree7_rrrll=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrrlr:everyKey (certRow 6 tree6) tree7_rrrlr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrrl:everyKey (certRow 6 tree6) tree7_rrrl=true:=splitCheck (by decide +kernel) ok_tree7_rrrll ok_tree7_rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrrrl:everyKey (certRow 6 tree6) tree7_rrrrl=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrrrr:everyKey (certRow 6 tree6) tree7_rrrrr=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrrr:everyKey (certRow 6 tree6) tree7_rrrr=true:=splitCheck (by decide +kernel) ok_tree7_rrrrl ok_tree7_rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rrr:everyKey (certRow 6 tree6) tree7_rrr=true:=splitCheck (by decide +kernel) ok_tree7_rrrl ok_tree7_rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_rr:everyKey (certRow 6 tree6) tree7_rr=true:=splitCheck (by decide +kernel) ok_tree7_rrl ok_tree7_rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7_r:everyKey (certRow 6 tree6) tree7_r=true:=splitCheck (by decide +kernel) ok_tree7_rl ok_tree7_rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree7:everyKey (certRow 6 tree6) tree7=true:=splitCheck (by decide +kernel) ok_tree7_l ok_tree7_r

def tree8_l:BTree (List W):=(.node [ze,zsO,zi,za,zt,zc,zl,zf] (.node [ztL,ze,zi,za,zt,zc,zl,zf] (.node [zkR,ze,zi,za,zt,zc,zl,zf] (.node [zzV,ze,zi,za,zt,zc,zl,zf] (.node [zkt,ze,zi,za,zt,zc,zl,zf] (.node [zc5,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [zmp,ze,zi,za,zt,zc,zl,zf] (.node [zt5,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [zmw,ze,zi,za,zt,zc,zl,zf] (.node [zcC,ze,zi,za,zt,zc,zl,zf] (.node [ztR,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [zg9,ze,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zce,zi,za,zt,zc,zl,zf] (.node [ze,zbh,zi,za,zt,zc,zl,zf] (.node [ze,zeT,zi,za,zt,zc,zl,zf] (.node [zza,ze,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,ziV,zi,za,zt,zc,zl,zf] (.node [ze,zw1,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zye,zi,za,zt,zc,zl,zf] (.node [ze,zgw,zi,za,zt,zc,zl,zf] (.node [ze,zu8,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zcW,zi,za,zt,zc,zl,zf] .nil .nil)))) (.node [ze,zxb,zi,za,zt,zc,zl,zf] (.node [ze,zeG,zi,za,zt,zc,zl,zf] (.node [ze,zi7,zi,za,zt,zc,zl,zf] (.node [ze,zjP,zi,za,zt,zc,zl,zf] (.node [ze,zfT,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zAz,zi,za,zt,zc,zl,zf] (.node [ze,zwl,zi,za,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zc4,zi,za,zt,zc,zl,zf] (.node [ze,zck,zi,za,zt,zc,zl,zf] (.node [ze,zzI,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zgZ,zi,za,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,zek,za,zt,zc,zl,zf] (.node [ze,zi,zsI,za,zt,zc,zl,zf] (.node [ze,zi,zkO,za,zt,zc,zl,zf] (.node [ze,zgP,zi,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zi,zfi,za,zt,zc,zl,zf] .nil .nil)) (.node [ze,zi,zu7,za,zt,zc,zl,zf] (.node [ze,zi,ztE,za,zt,zc,zl,zf] (.node [ze,zi,ztB,za,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zi,zuB,za,zt,zc,zl,zf] .nil .nil)))))
def tree8_r:BTree (List W):=(.node [ze,zi,za,zt,zii,zc,zl,zf] (.node [ze,zi,za,zgX,zt,zc,zl,zf] (.node [ze,zi,za,zuh,zt,zc,zl,zf] (.node [ze,zi,za,zug,zt,zc,zl,zf] (.node [ze,zi,za,zip,zt,zc,zl,zf] (.node [ze,zi,za,zY,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zi,za,za5,zt,zc,zl,zf] (.node [ze,zi,za,zbq,zt,zc,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zbG,zt,zc,zl,zf] (.node [ze,zi,za,zeO,zt,zc,zl,zf] (.node [ze,zi,za,zhO,zt,zc,zl,zf] .nil .nil) .nil) (.node [ze,zi,za,zb8,zt,zc,zl,zf] .nil .nil))) (.node [ze,zi,za,zt,zc2,zc,zl,zf] (.node [ze,zi,za,zt,zmo,zc,zl,zf] (.node [ze,zi,za,zt,zbR,zc,zl,zf] (.node [ze,zi,za,zt,zz5,zc,zl,zf] .nil .nil) .nil) (.node [ze,zi,za,zt,zuQ,zc,zl,zf] .nil .nil)) (.node [ze,zi,za,zt,zyf,zc,zl,zf] (.node [ze,zi,za,zt,zsS,zc,zl,zf] (.node [ze,zi,za,zt,zdK,zc,zl,zf] .nil .nil) .nil) (.node [ze,zi,za,zt,zsH,zc,zl,zf] .nil .nil)))) (.node [ze,zi,za,zt,zc,zl,zg0,zf] (.node [ze,zi,za,zt,zc,zcl,zl,zf] (.node [ze,zi,za,zt,zc,zwU,zl,zf] (.node [ze,zi,za,zt,zc,zk6,zl,zf] (.node [ze,zi,za,zt,zc,z8,zl,zf] .nil .nil) .nil) (.node [ze,zi,za,zt,zc,zbJ,zl,zf] (.node [ze,zi,za,zt,zc,zx,zl,zf] .nil .nil) .nil)) (.node [ze,zi,za,zt,zc,zl,zV,zf] (.node [ze,zi,za,zt,zc,zd9,zl,zf] (.node [ze,zi,za,zt,zc,zsg,zl,zf] .nil .nil) .nil) (.node [ze,zi,za,zt,zc,zl,zu4,zf] .nil .nil))) (.node [ze,zi,za,zt,zc,zl,zf,z6] (.node [ze,zi,za,zt,zc,zl,zcv,zf] (.node [ze,zi,za,zt,zc,zl,zs0,zf] (.node [ze,zi,za,zt,zc,zl,zgN,zf] .nil .nil) .nil) (.node [ze,zi,za,zt,zc,zl,zf,zd] .nil .nil)) (.node [ze,zi,za,zt,zc,zl,zf,zv] (.node [ze,zi,za,zt,zc,zl,zf,zw3] (.node [ze,zi,za,zt,zc,zl,zf,zbe] .nil .nil) .nil) (.node [ze,zi,za,zt,zc,zl,zf,zac] .nil .nil)))))
def tree8:BTree (List W):=.node [ze,zi,zgp,za,zt,zc,zl,zf] tree8_l tree8_r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree8_l:everyKey (certRow 7 tree7) tree8_l=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree8_r:everyKey (certRow 7 tree7) tree8_r=true:=by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree8:everyKey (certRow 7 tree7) tree8=true:=splitCheck (by decide +kernel) ok_tree8_l ok_tree8_r

def tree9:BTree (List W):=(.node [ze,zi,za,zt,zc,zl,zf] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok_tree9:everyKey (certRow 8 tree8) tree9=true:=by decide +kernel


private theorem distinctIns : ins.Nodup := by unfold ins; decide +kernel

private def targetFn (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) ||
  (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem probe : ∀ j : Fin 512,
    targetFn (fun i : Fin 7 => bit j (ins.getD i.val 0)) = bit j goal := by decide +kernel

private def allBool (p : Bool → Bool) : Bool := p false && p true

private theorem allBool_spec (p : Bool → Bool) (h : allBool p = true) (b : Bool) : p b = true := by
  cases b
  · exact (Bool.and_eq_true _ _ |>.mp h).1
  · exact (Bool.and_eq_true _ _ |>.mp h).2

private def check7 (p : (Fin 7 → Bool) → Bool) : Bool :=
  allBool fun x0 => allBool fun x1 => allBool fun x2 => allBool fun x3 =>
    allBool fun x4 => allBool fun x5 => allBool fun x6 =>
      p (fun i => match i.val with
        | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | 5 => x5 | _ => x6)

private theorem check7_spec (p : (Fin 7 → Bool) → Bool) (h : check7 p = true) (x : Fin 7 → Bool) :
    p x = true := by
  have h1 := allBool_spec _ (allBool_spec _ (allBool_spec _ (allBool_spec _
    (allBool_spec _ (allBool_spec _ (allBool_spec _ h (x 0)) (x 1)) (x 2)) (x 3)) (x 4)) (x 5)) (x 6)
  have heq : (fun i : Fin 7 => match i.val with
      | 0 => x 0 | 1 => x 1 | 2 => x 2 | 3 => x 3 | 4 => x 4 | 5 => x 5 | _ => x 6) = x :=
    funext fun ⟨k, hk⟩ => match k, hk with
      | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  exact heq ▸ h1

private theorem targetFn_check : check7 (fun x => targetFn x ==
    decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) = true := by
  decide +kernel

private theorem targetFn_eq (x : Fin 7 → Bool) :
    targetFn x = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).length / 2,
      (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧
      (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  beq_iff_eq.mp (check7_spec _ targetFn_check x)

private def d11 : List Gate :=
  [ ⟨.or,  [2, 1]⟩
  , ⟨.or,  [3, 0]⟩
  , ⟨.and, [0, 3]⟩
  , ⟨.and, [7, 4]⟩
  , ⟨.or,  [8, 1]⟩
  , ⟨.and, [11, 5]⟩
  , ⟨.or,  [10, 12]⟩
  , ⟨.or,  [8, 2]⟩
  , ⟨.and, [14, 6]⟩
  , ⟨.or,  [9, 15]⟩
  , ⟨.or,  [13, 16]⟩
  ]

private theorem d11_ok : ∀ g ∈ d11, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [d11, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem d11_check : check7 (fun x => Circuit.eval ⟨d11, 17⟩ (List.ofFn x) == targetFn x) = true := by
  decide +kernel

private theorem d11_eval (x : Fin 7 → Bool) :
    Circuit.eval ⟨d11, 17⟩ (List.ofFn x) = targetFn x :=
  beq_iff_eq.mp (check7_spec _ d11_check x)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private theorem ok_start : ins.sublists.all (startOK 9 tree9) = true := by decide +kernel

private theorem closed9 : Closed 9 tree9 :=
  checkedLayer 8 (by decide) tree9 tree8
    (checkedLayer 7 (by decide) tree8 tree7
      (checkedLayer 6 (by decide) tree7 tree6
        (checkedLayer 5 (by decide) tree6 tree5
          (checkedLayer 4 (by decide) tree5 tree4
            (checkedLayer 3 (by decide) tree4 tree3
              (checkedLayer 2 (by decide) tree3 .nil (closedEmpty 2) ok_tree3)
              ok_tree4)
            ok_tree5)
          ok_tree6)
        ok_tree7)
      ok_tree8)
    ok_tree9

private theorem lower_cost (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetFn x) :
    9 < binaryCost gs := by
  by_contra! bound
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 7) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [ins]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact probe k
  obtain ⟨t, ht, run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) :
      build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_build 9 tree9 ins distinctIns (by decide) closed9 ok_start t ht (lift bound run)

private theorem binaryCost_lt_of_not {gs : List Gate} (hnot : ∃ g ∈ gs, g.op = GateOp.not) :
    binaryCost gs < gs.length := by
  rcases hnot with ⟨g, hg, hgop⟩
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    simp only [binaryCost, List.filter_cons, List.length_cons]
    rcases List.mem_cons.mp hg with rfl | hxs
    · simp only [isBinary, hgop, Bool.false_eq_true, ↓reduceIte]
      exact Nat.lt_succ_of_le (List.length_filter_le isBinary xs)
    · have ih' := ih hxs
      by_cases hxb : isBinary x = true
      · simp only [hxb, ↓reduceIte, List.length_cons]; exact Nat.succ_lt_succ ih'
      · simp only [hxb, Bool.false_eq_true, ↓reduceIte]; exact Nat.lt_succ_of_lt ih'

theorem main_proof (gates : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).length / 2,
        (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧
        (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).length / 2,
          (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧
          (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · by_cases hlen : 11 ≤ gates.length
    · refine ⟨d11, 17, d11_ok, ?_, fun x => ?_⟩
      · simpa [d11] using hlen
      · rw [d11_eval x, targetFn_eq x]
    · exfalso
      have hcost := lower_cost gates o hg (fun x => by rw [he x, ← targetFn_eq x])
      have hlt := binaryCost_lt_of_not hnot
      omega
  · refine ⟨gates, o, ?_, le_rfl, he⟩
    intro g hgm
    rcases hg g hgm with ⟨hor, hlen⟩
    refine ⟨?_, hlen⟩
    rcases hor with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact False.elim (hnot ⟨g, hgm, h3⟩)

end PEqualNP.Outside.L_meta_11217

theorem PEqualNP.Outside.L_meta_11217 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  fun gates o hg _ he => PEqualNP.Outside.L_meta_11217.main_proof gates o hg he
