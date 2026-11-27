import PEqualNP.Defs

-- The signed live-wire and projection arguments are adapted from L_meta_9564 and L_meta_10916 (Apache-2.0).
-- Every possible first gate becomes free when one of its inputs is set to zero.
-- Two restrictions also eliminate later gates and leave two triangles sharing a vertex.
namespace PEqualNP.Outside.L_meta_10910.Signed

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 440
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 220 := ((x >>> 220) ^^^ x).setWidth 220
def cuts (ws : List W) : BitVec 220 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 220) ++ (0 : BitVec 220)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def differs (i : Fin 220) (w : W) : Prop :=
  w.getLsbD (220+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 220) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 220+i.val < 440 := by omega
  have hi' : i.val < 440 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 220) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 220)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
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
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 440 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 440)
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

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 440) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 440) :
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

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 440) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#440)[k.val] = false; simp
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

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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


def src (p : Array Nat) (j : Nat) := (p[j]?.getD 0) % 440
def proj (p : Array Nat) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 440 => w.getLsbD (src p j.val)))).cast (List.length_ofFn)
theorem src_lt (p : Array Nat) (j : Nat) : src p j < 440 := Nat.mod_lt _ (by decide)
set_option maxRecDepth 16000 in
theorem project_bit (p : Array Nat) (j : Nat) (w : W) (hj : j < 440) :
    (proj p w).getLsbD j = w.getLsbD (src p j) := by
  rw [proj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]; simp only [List.getElem?_ofFn, dif_pos hj, Option.getD_some]
theorem p_and (p : Array Nat) (a b : W) : proj p (a &&& b) = proj p a &&& proj p b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit p j _ hj, BitVec.getLsbD_and]
theorem p_or (p : Array Nat) (a b : W) : proj p (a ||| b) = proj p a ||| proj p b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit p j _ hj, BitVec.getLsbD_or]
theorem p_not (p : Array Nat) (a : W) : proj p (~~~a) = ~~~proj p a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit p j _ hj, BitVec.getLsbD_not, src_lt p j, hj, decide_true, Bool.true_and]

def simple (w : W) := w = 0 ∨ w = ~~~0
def clean (p : Array Nat) (i : Fin 220) (A : Finset W) := ∀ u ∈ A, differs i u → simple (proj p u)
theorem reach_proj (p : Array Nat) {a b z : W} {D : Finset W} (ha : holds D (proj p a))
    (hb : holds D (proj p b)) (hz : z ∈ basicOps a b) : reachable D (proj p z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> simp only [p_and,p_or,p_not]
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)
set_option maxRecDepth 16000 in
theorem free_proj (p : Array Nat) {a b z : W} {D : Finset W} (ha : holds D (proj p a))
    (hb : holds D (proj p b)) (hz : z ∈ basicOps a b)
    (hc : simple (proj p a) ∨ simple (proj p b)) : holds D (proj p z) := by
  have h0 : holds D 0 := .inl rfl
  have h1 : holds D (~~~0) := holds_not h0
  have hna := holds_not ha
  have hnb := holds_not hb
  have t_zero_and (x : W) : (0 : W) &&& x = 0 := BitVec.zero_and
  have t_and_zero (x : W) : x &&& (0 : W) = 0 := BitVec.and_zero
  have t_zero_or (x : W) : (0 : W) ||| x = x := BitVec.zero_or
  have t_or_zero (x : W) : x ||| (0 : W) = x := BitVec.or_zero
  have t_allOnes_and (x : W) : (~~~0 : W) &&& x = x := BitVec.allOnes_and
  have t_and_allOnes (x : W) : x &&& (~~~0 : W) = x := BitVec.and_allOnes
  have t_allOnes_or (x : W) : (~~~0 : W) ||| x = ~~~0 := BitVec.allOnes_or
  have t_or_allOnes (x : W) : x ||| (~~~0 : W) = ~~~0 := BitVec.or_allOnes
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> simp only [p_and,p_or,p_not] <;>
    rcases hc with (hc|hc)|(hc|hc) <;> rw [hc] <;>
    simp only [BitVec.not_not, t_zero_and, t_and_zero, t_zero_or, t_or_zero, t_allOnes_and, t_and_allOnes, t_allOnes_or, t_or_allOnes] <;> assumption

set_option maxRecDepth 16000 in
theorem shrink (p : Array Nat) (i : Fin 220) (fixed : proj p goal = goal)
    {t : W} (ht : t = goal ∨ t = ~~~goal) (hd : differs i t) (k : Nat)
    {A D : Finset W} (mapA : ∀ u ∈ A, holds D (proj p u)) (h : build basicOps t k A) :
    ∃ q m, (q = goal ∨ q = ~~~goal) ∧ build basicOps q m D ∧ m ≤ k ∧ (clean p i A → m < k) := by
  induction k generalizing A D with
  | zero =>
    have hv := mapA t h
    have ps : proj p t = goal ∨ proj p t = ~~~goal := by
      rcases ht with rfl|rfl
      · exact .inl fixed
      · exact .inr ((p_not ..).trans (congrArg (fun w : W => ~~~w) fixed))
    have nons : ¬ simple (proj p t) := by
      rcases ps with eq|eq <;> rw [eq] <;> unfold simple <;> decide
    rcases hv with c|c|⟨q,hq,rep⟩
    · exact (nons (.inl c)).elim
    · exact (nons (.inr c)).elim
    have hqg : q = goal ∨ q = ~~~goal := by
      rcases rep with r|r <;> rcases ps with e|e <;> rw [r] at e
      · exact .inl e
      · exact .inr e
      · exact .inr (by simpa using congrArg (fun w : W => ~~~w) e)
      · exact .inl (by simpa using congrArg (fun w : W => ~~~w) e)
    exact ⟨q,0,hqg,hq,le_rfl,fun hcl => (nons (hcl t h hd)).elim⟩
  | succ k ih =>
    rcases h with hs|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · obtain ⟨q,m,hq,hr,hl,_⟩ := ih mapA hs
      exact ⟨q,m,hq,hr,by omega,fun _ => by omega⟩
    by_cases old : holds D (proj p z)
    · have extA : ∀ u ∈ insert z A, holds D (proj p u) := by
        intro u hu; rcases Finset.mem_insert.mp hu with rfl|hu
        · exact old
        · exact mapA u hu
      obtain ⟨q,m,hq,hr,hl,_⟩ := ih extA tail
      exact ⟨q,m,hq,hr,by omega,fun _ => by omega⟩
    · rcases reach_proj p (mapA a ha) (mapA b hb) hz with h0|⟨x,hx,y,hy,ne,w,op,rep⟩
      · contradiction
      have extA : ∀ u ∈ insert z A, holds (insert w D) (proj p u) := by
        intro u hu; rcases Finset.mem_insert.mp hu with rfl|hu
        · exact rep
        · exact holds_insert (mapA u hu)
      obtain ⟨q,m,hq,hr,hl,hcl⟩ := ih extA tail
      refine ⟨q,m+1,hq,.inr ⟨x,hx,y,hy,ne,w,op,hr⟩,by omega,?_⟩
      intro orig
      have next : clean p i (insert z A) := by
        intro u hu diff
        rcases Finset.mem_insert.mp hu with rfl|hu
        · rcases ops_differs i a b u hz diff with da|db
          · exact (old (free_proj p (mapA a ha) (mapA b hb) hz (.inl (orig a ha da)))).elim
          · exact (old (free_proj p (mapA a ha) (mapA b hb) hz (.inr (orig b hb db)))).elim
        · exact orig u hu diff
      have := hcl next
      omega
def rows : List W := [0x2a14c000fffffffffffffffffffffffffff5555557aaab56eaaad5ebb94c03f, 0x73400002000000000000000000000000001999999acccd9b733366bddc003c2, 0x7c000084000000000000000000000000001e1e1e1cf0f1e3bc3c78cee803c84, 0xffffffffffffffffffffffffffe0000000000000000000040000917ffffffffffffffffffffffffffffe01fe0ff01fc3fc07f0f083c917, 0x288d50000000000000000000000000001fffe000fffe003fff800ff288d50, 0x12288000000000000000000000000001fffffff0000003ffffff004d2288, 0x423220000000000000000000000000001fffffffffffffc00000000723220]
def five : List W := [0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff, 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff, 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00, 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000, 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000]
def six0 : List W := [0x114000000000000000000000000000000000000000000000000055aaba, 0x58000000000000000000000000000000000000000000000000066cf2c, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001, 0x20000000000000000000000000000000000000000000000000078f3ce, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800241fffffffffffffffffffffffffffffffffffffffffffffffffff03f1, 0x38000000000000000000000000000000000000000000000000007ffc00]
def toSix0 : Array Nat := #[16, 6, 10, 26, 32, 7, 19, 44, 46, 48, 12, 60, 21, 70, 72, 74, 22, 13, 87, 97, 99, 101, 103, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 236, 332, 244, 246, 248, 241, 227, 237, 242, 233, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236]
def toFive0 : Array Nat := #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229]
def six3 : List W := [0xfffffffffffffffffffffffffffffffffffffffffffffffff800001, 0x114000000000000000000000000000000000000000000000000055aaba, 0x58000000000000000000000000000000000000000000000000066cf2c, 0x20000000000000000000000000000000000000000000000000078f3ce, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800241fffffffffffffffffffffffffffffffffffffffffffffffffff03f1, 0x38000000000000000000000000000000000000000000000000007ffc00]
def toSix3 : Array Nat := #[18, 6, 10, 26, 32, 7, 19, 44, 46, 48, 12, 60, 21, 70, 72, 74, 22, 13, 87, 97, 99, 101, 103, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 236, 332, 244, 246, 248, 241, 227, 237, 242, 233, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236]
def toFive3 : Array Nat := #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229, 242, 225, 222, 439, 223, 224, 226, 227, 228, 229]
def six1 : List W := [0xfffffffffffffffffffffffffffffffffffffffffffffffff800089fffffffffffffffffffffffffffffffffffffffffffffffffd555b7, 0x2c00000000000000000000000000000000000000000000000006666dc, 0x13000000000000000000000000000000000000000000000000007878e6, 0x1c000000000000000000000000000000000000000000000000007f80f8, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001, 0x20000000000000000000000000000000000000000000000000007fff00]
def toSix1 : Array Nat := #[18, 219, 2, 10, 25, 15, 11, 29, 20, 12, 59, 17, 62, 65, 66, 21, 69, 72, 73, 76, 77, 80, 81, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 240, 332, 246, 247, 439, 222, 241, 235, 231, 237, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240]
def toFive1 : Array Nat := #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228]
def six5 : List W := [0x9400000000000000000000000000000000000000000000000005555b6, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001, 0x5800000000000000000000000000000000000000000000000006666dc, 0x16000000000000000000000000000000000000000000000000007878e6, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800181fffffffffffffffffffffffffffffffffffffffffffffffffff80f9, 0x20000000000000000000000000000000000000000000000000007fff00]
def toSix5 : Array Nat := #[6, 219, 2, 10, 25, 15, 11, 29, 20, 12, 59, 17, 62, 65, 66, 21, 69, 72, 73, 76, 77, 80, 81, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 241, 332, 240, 246, 247, 439, 222, 235, 231, 237, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241]
def toFive5 : Array Nat := #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228]
def six2 : List W := [0xfffffffffffffffffffffffffffffffffffffffffffffffff800089fffffffffffffffffffffffffffffffffffffffffffffffffd555b7, 0x2c00000000000000000000000000000000000000000000000006666dc, 0x13000000000000000000000000000000000000000000000000007878e6, 0x1c000000000000000000000000000000000000000000000000007f80f8, 0x20000000000000000000000000000000000000000000000000007fff00, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001]
def toSix2 : Array Nat := #[20, 219, 1, 6, 24, 15, 8, 28, 18, 32, 33, 16, 36, 37, 38, 19, 43, 44, 45, 50, 51, 52, 53, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 240, 332, 244, 245, 439, 221, 241, 235, 231, 236, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240, 240]
def toFive2 : Array Nat := #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228, 242, 229, 439, 224, 222, 223, 225, 226, 227, 228]
def six6 : List W := [0x9400000000000000000000000000000000000000000000000005555b6, 0x5800000000000000000000000000000000000000000000000006666dc, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001, 0x16000000000000000000000000000000000000000000000000007878e6, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800181fffffffffffffffffffffffffffffffffffffffffffffffffff80f9, 0x20000000000000000000000000000000000000000000000000007fff00]
def toSix6 : Array Nat := #[10, 219, 1, 6, 24, 15, 8, 28, 18, 32, 33, 16, 36, 37, 38, 19, 43, 44, 45, 50, 51, 52, 53, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 241, 332, 240, 244, 245, 439, 221, 235, 231, 236, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 332, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241]
def toFive6 : Array Nat := #[8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228, 242, 229, 222, 225, 223, 224, 226, 439, 227, 228]
def six : Nat → List W
  | 0 => six0
  | 1 => six1
  | 2 => six2
  | 3 => six3
  | 5 => six5
  | 6 => six6
  | _ => six0
def toSix : Nat → Array Nat
  | 0 => toSix0
  | 1 => toSix1
  | 2 => toSix2
  | 3 => toSix3
  | 5 => toSix5
  | 6 => toSix6
  | _ => toSix0
def toFive : Nat → Array Nat
  | 0 => toFive0
  | 1 => toFive1
  | 2 => toFive2
  | 3 => toFive3
  | 5 => toFive5
  | 6 => toFive6
  | _ => toFive0

abbrev Bins := List (Nat × W)

def selectedBits (bs : Bins) (j : Nat) : List Nat :=
  bs.filterMap fun pair => if pair.2.getLsbD j then some pair.1 else none

def sparseImage (bs : Bins) (w : W) : W :=
  bs.foldr (fun pair v => if w.getLsbD pair.1 then pair.2 ||| v else v) 0

theorem sparse_bit (bs : Bins) (w : W) (j : Nat) :
    (sparseImage bs w).getLsbD j = (selectedBits bs j).any (fun r => w.getLsbD r) := by
  induction bs with
  | nil => simp [sparseImage,selectedBits]
  | cons p bs ih =>
    rcases p with ⟨r,mask⟩
    cases hr : w.getLsbD r <;> cases hm : mask.getLsbD j <;>
      simpa [sparseImage,selectedBits,hr,hm,BitVec.getLsbD_or] using ih

def faithfulBins (bs : Bins) (p : Array Nat) : Prop :=
  ∀ j : Fin 440, selectedBits bs j.val = [src p j.val]

theorem sparse_eq {bs : Bins} {p : Array Nat} (hf : faithfulBins bs p) (w : W) :
    sparseImage bs w = proj p w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [sparse_bit,project_bit p j w hj,hf ⟨j,hj⟩]
  simp

def toSixBins0 : Bins := [(16, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001), (6, 0x2), (10, 0x4), (26, 0x8), (32, 0x10), (7, 0x20), (19, 0x40), (44, 0x80), (46, 0x100), (48, 0x200), (12, 0x400), (60, 0x800), (21, 0x1000), (70, 0x2000), (72, 0x4000), (74, 0x8000), (22, 0x10000), (13, 0x20000), (87, 0x40000), (97, 0x80000), (99, 0x100000), (101, 0x200000), (103, 0x400000), (236, 0xfffffffffffffffffffffffffffffffffffffffffffffffff8000010000000000000000000000000000000000000000000000000000000), (332, 0x7ffc020000000000000000000000000000000000000000000000000000000), (244, 0x40000000000000000000000000000000000000000000000000000000), (246, 0x80000000000000000000000000000000000000000000000000000000), (248, 0x100000000000000000000000000000000000000000000000000000000), (241, 0x200000000000000000000000000000000000000000000000000000000), (227, 0x400000000000000000000000000000000000000000000000000000000), (237, 0x800000000000000000000000000000000000000000000000000000000), (242, 0x1000000000000000000000000000000000000000000000000000000000), (233, 0x2000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toSixFaithful0 : faithfulBins toSixBins0 toSix0 := by unfold faithfulBins; decide +kernel
def toSixBins1 : Bins := [(18, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001), (219, 0x2), (2, 0x4), (10, 0x8), (25, 0x10), (15, 0x20), (11, 0x40), (29, 0x80), (20, 0x100), (12, 0x200), (59, 0x400), (17, 0x800), (62, 0x1000), (65, 0x2000), (66, 0x4000), (21, 0x8000), (69, 0x10000), (72, 0x20000), (73, 0x40000), (76, 0x80000), (77, 0x100000), (80, 0x200000), (81, 0x400000), (240, 0xfffffffffffffffffffffffffffffffffffffffffffffffff8000010000000000000000000000000000000000000000000000000000000), (332, 0x7ffc020000000000000000000000000000000000000000000000000000000), (246, 0x40000000000000000000000000000000000000000000000000000000), (247, 0x80000000000000000000000000000000000000000000000000000000), (439, 0x100000000000000000000000000000000000000000000000000000000), (222, 0x200000000000000000000000000000000000000000000000000000000), (241, 0x400000000000000000000000000000000000000000000000000000000), (235, 0x800000000000000000000000000000000000000000000000000000000), (231, 0x1000000000000000000000000000000000000000000000000000000000), (237, 0x2000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toSixFaithful1 : faithfulBins toSixBins1 toSix1 := by unfold faithfulBins; decide +kernel
def toSixBins2 : Bins := [(20, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001), (219, 0x2), (1, 0x4), (6, 0x8), (24, 0x10), (15, 0x20), (8, 0x40), (28, 0x80), (18, 0x100), (32, 0x200), (33, 0x400), (16, 0x800), (36, 0x1000), (37, 0x2000), (38, 0x4000), (19, 0x8000), (43, 0x10000), (44, 0x20000), (45, 0x40000), (50, 0x80000), (51, 0x100000), (52, 0x200000), (53, 0x400000), (240, 0xfffffffffffffffffffffffffffffffffffffffffffffffff8000010000000000000000000000000000000000000000000000000000000), (332, 0x7ffc020000000000000000000000000000000000000000000000000000000), (244, 0x40000000000000000000000000000000000000000000000000000000), (245, 0x80000000000000000000000000000000000000000000000000000000), (439, 0x100000000000000000000000000000000000000000000000000000000), (221, 0x200000000000000000000000000000000000000000000000000000000), (241, 0x400000000000000000000000000000000000000000000000000000000), (235, 0x800000000000000000000000000000000000000000000000000000000), (231, 0x1000000000000000000000000000000000000000000000000000000000), (236, 0x2000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toSixFaithful2 : faithfulBins toSixBins2 toSix2 := by unfold faithfulBins; decide +kernel
def toSixBins3 : Bins := [(18, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001), (6, 0x2), (10, 0x4), (26, 0x8), (32, 0x10), (7, 0x20), (19, 0x40), (44, 0x80), (46, 0x100), (48, 0x200), (12, 0x400), (60, 0x800), (21, 0x1000), (70, 0x2000), (72, 0x4000), (74, 0x8000), (22, 0x10000), (13, 0x20000), (87, 0x40000), (97, 0x80000), (99, 0x100000), (101, 0x200000), (103, 0x400000), (236, 0xfffffffffffffffffffffffffffffffffffffffffffffffff8000010000000000000000000000000000000000000000000000000000000), (332, 0x7ffc020000000000000000000000000000000000000000000000000000000), (244, 0x40000000000000000000000000000000000000000000000000000000), (246, 0x80000000000000000000000000000000000000000000000000000000), (248, 0x100000000000000000000000000000000000000000000000000000000), (241, 0x200000000000000000000000000000000000000000000000000000000), (227, 0x400000000000000000000000000000000000000000000000000000000), (237, 0x800000000000000000000000000000000000000000000000000000000), (242, 0x1000000000000000000000000000000000000000000000000000000000), (233, 0x2000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toSixFaithful3 : faithfulBins toSixBins3 toSix3 := by unfold faithfulBins; decide +kernel
def toSixBins5 : Bins := [(6, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001), (219, 0x2), (2, 0x4), (10, 0x8), (25, 0x10), (15, 0x20), (11, 0x40), (29, 0x80), (20, 0x100), (12, 0x200), (59, 0x400), (17, 0x800), (62, 0x1000), (65, 0x2000), (66, 0x4000), (21, 0x8000), (69, 0x10000), (72, 0x20000), (73, 0x40000), (76, 0x80000), (77, 0x100000), (80, 0x200000), (81, 0x400000), (241, 0xfffffffffffffffffffffffffffffffffffffffffffffffff8000010000000000000000000000000000000000000000000000000000000), (332, 0x7ffc020000000000000000000000000000000000000000000000000000000), (240, 0x40000000000000000000000000000000000000000000000000000000), (246, 0x80000000000000000000000000000000000000000000000000000000), (247, 0x100000000000000000000000000000000000000000000000000000000), (439, 0x200000000000000000000000000000000000000000000000000000000), (222, 0x400000000000000000000000000000000000000000000000000000000), (235, 0x800000000000000000000000000000000000000000000000000000000), (231, 0x1000000000000000000000000000000000000000000000000000000000), (237, 0x2000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toSixFaithful5 : faithfulBins toSixBins5 toSix5 := by unfold faithfulBins; decide +kernel
def toSixBins6 : Bins := [(10, 0xfffffffffffffffffffffffffffffffffffffffffffffffff800001), (219, 0x2), (1, 0x4), (6, 0x8), (24, 0x10), (15, 0x20), (8, 0x40), (28, 0x80), (18, 0x100), (32, 0x200), (33, 0x400), (16, 0x800), (36, 0x1000), (37, 0x2000), (38, 0x4000), (19, 0x8000), (43, 0x10000), (44, 0x20000), (45, 0x40000), (50, 0x80000), (51, 0x100000), (52, 0x200000), (53, 0x400000), (241, 0xfffffffffffffffffffffffffffffffffffffffffffffffff8000010000000000000000000000000000000000000000000000000000000), (332, 0x7ffc020000000000000000000000000000000000000000000000000000000), (240, 0x40000000000000000000000000000000000000000000000000000000), (244, 0x80000000000000000000000000000000000000000000000000000000), (245, 0x100000000000000000000000000000000000000000000000000000000), (439, 0x200000000000000000000000000000000000000000000000000000000), (221, 0x400000000000000000000000000000000000000000000000000000000), (235, 0x800000000000000000000000000000000000000000000000000000000), (231, 0x1000000000000000000000000000000000000000000000000000000000), (236, 0x2000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toSixFaithful6 : faithfulBins toSixBins6 toSix6 := by unfold faithfulBins; decide +kernel
def toSixBins : Nat → Bins
  | 0 => toSixBins0
  | 1 => toSixBins1
  | 2 => toSixBins2
  | 3 => toSixBins3
  | 5 => toSixBins5
  | 6 => toSixBins6
  | _ => toSixBins0
theorem toSixImage (i : Nat) (w : W) : sparseImage (toSixBins i) w = proj (toSix i) w := by
  apply sparse_eq
  unfold toSixBins toSix
  split
  · exact toSixFaithful0
  · exact toSixFaithful1
  · exact toSixFaithful2
  · exact toSixFaithful3
  · exact toSixFaithful5
  · exact toSixFaithful6
  · exact toSixFaithful0
def toFiveBins0 : Bins := [(1, 0x3ff), (6, 0xffc00), (4, 0x3ff00000), (7, 0xffc0000000), (2, 0x3ff0000000000), (3, 0xffc000000000000), (8, 0x3ff000000000000000), (5, 0xffc00000000000000000), (9, 0x3ff00000000000000000000), (12, 0xffc0000000000000000000000), (13, 0x3ff0000000000000000000000000), (19, 0xffc000000000000000000000000000), (16, 0x3ff000000000000000000000000000000), (20, 0xffc00000000000000000000000000000000), (10, 0x3ff00000000000000000000000000000000000), (14, 0xffc0000000000000000000000000000000000000), (11, 0x3ff0000000000000000000000000000000000000000), (15, 0xffc000000000000000000000000000000000000000000), (17, 0x3ff000000000000000000000000000000000000000000000), (21, 0xffc00000000000000000000000000000000000000000000000), (18, 0x3ff00000000000000000000000000000000000000000000000000), (22, 0xffc0000000000000000000000000000000000000000000000000000), (242, 0x401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000), (225, 0x802008020080200802008020080200802008020080200802008020000000000000000000000000000000000000000000000000000000), (222, 0x1004010040100401004010040100401004010040100401004010040000000000000000000000000000000000000000000000000000000), (439, 0x2008020080200802008020080200802008020080200802008020080000000000000000000000000000000000000000000000000000000), (223, 0x4010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000), (224, 0x8020080200802008020080200802008020080200802008020080200000000000000000000000000000000000000000000000000000000), (226, 0x10040100401004010040100401004010040100401004010040100400000000000000000000000000000000000000000000000000000000), (227, 0x20080200802008020080200802008020080200802008020080200800000000000000000000000000000000000000000000000000000000), (228, 0x40100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000), (229, 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toFiveFaithful0 : faithfulBins toFiveBins0 toFive0 := by unfold faithfulBins; decide +kernel
def toFiveBins1 : Bins := [(8, 0x3ff), (11, 0xffc00), (1, 0x3ff00000), (12, 0xffc0000000), (9, 0x3ff0000000000), (10, 0xffc000000000000), (13, 0x3ff000000000000000), (2, 0xffc00000000000000000), (14, 0x3ff00000000000000000000), (15, 0xffc0000000000000000000000), (16, 0x3ff0000000000000000000000000), (19, 0xffc000000000000000000000000000), (5, 0x3ff000000000000000000000000000000), (20, 0xffc00000000000000000000000000000000), (3, 0x3ff00000000000000000000000000000000000), (17, 0xffc0000000000000000000000000000000000000), (4, 0x3ff0000000000000000000000000000000000000000), (18, 0xffc000000000000000000000000000000000000000000), (6, 0x3ff000000000000000000000000000000000000000000000), (21, 0xffc00000000000000000000000000000000000000000000000), (7, 0x3ff00000000000000000000000000000000000000000000000000), (22, 0xffc0000000000000000000000000000000000000000000000000000), (242, 0x401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000), (229, 0x802008020080200802008020080200802008020080200802008020000000000000000000000000000000000000000000000000000000), (439, 0x1004010040100401004010040100401004010040100401004010040000000000000000000000000000000000000000000000000000000), (224, 0x2008020080200802008020080200802008020080200802008020080000000000000000000000000000000000000000000000000000000), (222, 0x4010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000), (223, 0x8020080200802008020080200802008020080200802008020080200000000000000000000000000000000000000000000000000000000), (225, 0x10040100401004010040100401004010040100401004010040100400000000000000000000000000000000000000000000000000000000), (226, 0x20080200802008020080200802008020080200802008020080200800000000000000000000000000000000000000000000000000000000), (227, 0x40100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000), (228, 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toFiveFaithful1 : faithfulBins toFiveBins1 toFive1 := by unfold faithfulBins; decide +kernel
def toFiveBins2 : Bins := [(8, 0x3ff), (11, 0xffc00), (1, 0x3ff00000), (12, 0xffc0000000), (9, 0x3ff0000000000), (10, 0xffc000000000000), (13, 0x3ff000000000000000), (2, 0xffc00000000000000000), (14, 0x3ff00000000000000000000), (15, 0xffc0000000000000000000000), (16, 0x3ff0000000000000000000000000), (19, 0xffc000000000000000000000000000), (5, 0x3ff000000000000000000000000000000), (20, 0xffc00000000000000000000000000000000), (3, 0x3ff00000000000000000000000000000000000), (17, 0xffc0000000000000000000000000000000000000), (4, 0x3ff0000000000000000000000000000000000000000), (18, 0xffc000000000000000000000000000000000000000000), (6, 0x3ff000000000000000000000000000000000000000000000), (21, 0xffc00000000000000000000000000000000000000000000000), (7, 0x3ff00000000000000000000000000000000000000000000000000), (22, 0xffc0000000000000000000000000000000000000000000000000000), (242, 0x401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000), (229, 0x802008020080200802008020080200802008020080200802008020000000000000000000000000000000000000000000000000000000), (439, 0x1004010040100401004010040100401004010040100401004010040000000000000000000000000000000000000000000000000000000), (224, 0x2008020080200802008020080200802008020080200802008020080000000000000000000000000000000000000000000000000000000), (222, 0x4010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000), (223, 0x8020080200802008020080200802008020080200802008020080200000000000000000000000000000000000000000000000000000000), (225, 0x10040100401004010040100401004010040100401004010040100400000000000000000000000000000000000000000000000000000000), (226, 0x20080200802008020080200802008020080200802008020080200800000000000000000000000000000000000000000000000000000000), (227, 0x40100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000), (228, 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toFiveFaithful2 : faithfulBins toFiveBins2 toFive2 := by unfold faithfulBins; decide +kernel
def toFiveBins3 : Bins := [(1, 0x3ff), (6, 0xffc00), (4, 0x3ff00000), (7, 0xffc0000000), (2, 0x3ff0000000000), (3, 0xffc000000000000), (8, 0x3ff000000000000000), (5, 0xffc00000000000000000), (9, 0x3ff00000000000000000000), (12, 0xffc0000000000000000000000), (13, 0x3ff0000000000000000000000000), (19, 0xffc000000000000000000000000000), (16, 0x3ff000000000000000000000000000000), (20, 0xffc00000000000000000000000000000000), (10, 0x3ff00000000000000000000000000000000000), (14, 0xffc0000000000000000000000000000000000000), (11, 0x3ff0000000000000000000000000000000000000000), (15, 0xffc000000000000000000000000000000000000000000), (17, 0x3ff000000000000000000000000000000000000000000000), (21, 0xffc00000000000000000000000000000000000000000000000), (18, 0x3ff00000000000000000000000000000000000000000000000000), (22, 0xffc0000000000000000000000000000000000000000000000000000), (242, 0x401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000), (225, 0x802008020080200802008020080200802008020080200802008020000000000000000000000000000000000000000000000000000000), (222, 0x1004010040100401004010040100401004010040100401004010040000000000000000000000000000000000000000000000000000000), (439, 0x2008020080200802008020080200802008020080200802008020080000000000000000000000000000000000000000000000000000000), (223, 0x4010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000), (224, 0x8020080200802008020080200802008020080200802008020080200000000000000000000000000000000000000000000000000000000), (226, 0x10040100401004010040100401004010040100401004010040100400000000000000000000000000000000000000000000000000000000), (227, 0x20080200802008020080200802008020080200802008020080200800000000000000000000000000000000000000000000000000000000), (228, 0x40100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000), (229, 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toFiveFaithful3 : faithfulBins toFiveBins3 toFive3 := by unfold faithfulBins; decide +kernel
def toFiveBins5 : Bins := [(8, 0x3ff), (11, 0xffc00), (1, 0x3ff00000), (12, 0xffc0000000), (9, 0x3ff0000000000), (10, 0xffc000000000000), (13, 0x3ff000000000000000), (2, 0xffc00000000000000000), (14, 0x3ff00000000000000000000), (15, 0xffc0000000000000000000000), (16, 0x3ff0000000000000000000000000), (19, 0xffc000000000000000000000000000), (5, 0x3ff000000000000000000000000000000), (20, 0xffc00000000000000000000000000000000), (3, 0x3ff00000000000000000000000000000000000), (17, 0xffc0000000000000000000000000000000000000), (4, 0x3ff0000000000000000000000000000000000000000), (18, 0xffc000000000000000000000000000000000000000000), (6, 0x3ff000000000000000000000000000000000000000000000), (21, 0xffc00000000000000000000000000000000000000000000000), (7, 0x3ff00000000000000000000000000000000000000000000000000), (22, 0xffc0000000000000000000000000000000000000000000000000000), (242, 0x401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000), (229, 0x802008020080200802008020080200802008020080200802008020000000000000000000000000000000000000000000000000000000), (222, 0x1004010040100401004010040100401004010040100401004010040000000000000000000000000000000000000000000000000000000), (225, 0x2008020080200802008020080200802008020080200802008020080000000000000000000000000000000000000000000000000000000), (223, 0x4010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000), (224, 0x8020080200802008020080200802008020080200802008020080200000000000000000000000000000000000000000000000000000000), (226, 0x10040100401004010040100401004010040100401004010040100400000000000000000000000000000000000000000000000000000000), (439, 0x20080200802008020080200802008020080200802008020080200800000000000000000000000000000000000000000000000000000000), (227, 0x40100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000), (228, 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toFiveFaithful5 : faithfulBins toFiveBins5 toFive5 := by unfold faithfulBins; decide +kernel
def toFiveBins6 : Bins := [(8, 0x3ff), (11, 0xffc00), (1, 0x3ff00000), (12, 0xffc0000000), (9, 0x3ff0000000000), (10, 0xffc000000000000), (13, 0x3ff000000000000000), (2, 0xffc00000000000000000), (14, 0x3ff00000000000000000000), (15, 0xffc0000000000000000000000), (16, 0x3ff0000000000000000000000000), (19, 0xffc000000000000000000000000000), (5, 0x3ff000000000000000000000000000000), (20, 0xffc00000000000000000000000000000000), (3, 0x3ff00000000000000000000000000000000000), (17, 0xffc0000000000000000000000000000000000000), (4, 0x3ff0000000000000000000000000000000000000000), (18, 0xffc000000000000000000000000000000000000000000), (6, 0x3ff000000000000000000000000000000000000000000000), (21, 0xffc00000000000000000000000000000000000000000000000), (7, 0x3ff00000000000000000000000000000000000000000000000000), (22, 0xffc0000000000000000000000000000000000000000000000000000), (242, 0x401004010040100401004010040100401004010040100401004010000000000000000000000000000000000000000000000000000000), (229, 0x802008020080200802008020080200802008020080200802008020000000000000000000000000000000000000000000000000000000), (222, 0x1004010040100401004010040100401004010040100401004010040000000000000000000000000000000000000000000000000000000), (225, 0x2008020080200802008020080200802008020080200802008020080000000000000000000000000000000000000000000000000000000), (223, 0x4010040100401004010040100401004010040100401004010040100000000000000000000000000000000000000000000000000000000), (224, 0x8020080200802008020080200802008020080200802008020080200000000000000000000000000000000000000000000000000000000), (226, 0x10040100401004010040100401004010040100401004010040100400000000000000000000000000000000000000000000000000000000), (439, 0x20080200802008020080200802008020080200802008020080200800000000000000000000000000000000000000000000000000000000), (227, 0x40100401004010040100401004010040100401004010040100401000000000000000000000000000000000000000000000000000000000), (228, 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem toFiveFaithful6 : faithfulBins toFiveBins6 toFive6 := by unfold faithfulBins; decide +kernel
def toFiveBins : Nat → Bins
  | 0 => toFiveBins0
  | 1 => toFiveBins1
  | 2 => toFiveBins2
  | 3 => toFiveBins3
  | 5 => toFiveBins5
  | 6 => toFiveBins6
  | _ => toFiveBins0
theorem toFiveImage (i : Nat) (w : W) : sparseImage (toFiveBins i) w = proj (toFive i) w := by
  apply sparse_eq
  unfold toFiveBins toFive
  split
  · exact toFiveFaithful0
  · exact toFiveFaithful1
  · exact toFiveFaithful2
  · exact toFiveFaithful3
  · exact toFiveFaithful5
  · exact toFiveFaithful6
  · exact toFiveFaithful0

abbrev Case := W × Nat × Fin 220
def cases : List Case := [
  (0x220000000000000000000000000000000011111112888912622244a99800002, 0, 0),
  (0x7b54c002fffffffffffffffffffffffffffddddddfeeefdffbbbf7fffd4c3ff, 0, 1),
  (0x814c000ffffffffffffffffffffffffffe444444522224488889142214c03d, 0, 0),
  (0x5140000200000000000000000000000000088888884444891111221444003c0, 0, 0),
  (0x280000000000000000000000000000000014141414a0a142a82850caa800004, 0, 0),
  (0x7e14c084ffffffffffffffffffffffffffff5f5f5ffafbf7febefdeff94fcbf, 0, 2),
  (0x214c000ffffffffffffffffffffffffffe14141430a0a1442828521114c03b, 0, 0),
  (0x54000084000000000000000000000000000a0a0a085050a1141428044003c80, 0, 0),
  (0xfffffffffffffffffffffffffff5401540aa01542a80550b080c017, 0, 0),
  (0xffffffffffffffffffffffffffe000000000000000000006a14c917fffffffffffffffffffffffffffff55ff7ffabfeffeaffefb97c93f, 0, 0),
  (0x2a14c000000000000000000000000000000015401700aa02c02a80e0b140028, 0, 0),
  (0xffffffffffffffffffffffffffe0000000000000000000040000917000000000000000000000000000aa00aa05500a815402a040030900, 0, 3),
  (0x80000000000000000000000000000015554000aaaa002aaa800bb008010, 0, 0),
  (0x2a3ccd50fffffffffffffffffffffffffffffff557ffff56ffffd5effbccd7f, 0, 4),
  (0x2a144000ffffffffffffffffffffffffffe0001557000156c00055e0094402f, 0, 0),
  (0x280d50000000000000000000000000000aaaa000555400155500044280d40, 0, 0),
  (0x155555570000002aaad5e00040008, 0, 0),
  (0x2a15e288ffffffffffffffffffffffffffffffffffaaab56fffffffbbdde2bf, 0, 3),
  (0x2a14c000ffffffffffffffffffffffffffe0000000aaab56c000000bb90c037, 0, 0),
  (0x12288000000000000000000000000000aaaaaa800000015552a100492280, 0, 0),
  (0x15555557aaab56c00000000100020, 0, 0),
  (0x2a56f220ffffffffffffffffffffffffffffffffffffffffeaaad5ebbf6f23f, 0, 5),
  (0x2a14c000ffffffffffffffffffffffffffe00000000000002aaad5ebb84c01f, 0, 0),
  (0x423220000000000000000000000000000aaaaaa85554a9000000000623200, 0, 0),
  (0x700000000000000000000000000000000018181818c0c1833030608cc800080, 1, 6),
  (0x7f400086000000000000000000000000001f9f9f9efcfdfbff3f7efffc03fc6, 1, 7),
  (0x340000200000000000000000000000000018181820c0c18430306311400342, 1, 6),
  (0xc00008400000000000000000000000000060606043030608c0c18422003c04, 1, 6),
  (0x400000020000000000000000000000000019801980cc01983300660d0800102, 1, 6),
  (0xffffffffffffffffffffffffffe0000000000000000000073400917fffffffffffffffffffffffffffff99ffaffcdff7ff37fbfdc3cbd7, 1, 8),
  (0x33400000000000000000000000000000000019801a00cc03403300b0d4002c0, 1, 6),
  (0xffffffffffffffffffffffffffe0000000000000000000000000915ffffffffffffffffffffffffffe66006603300640cc01902003c815, 1, 6),
  (0x19998000cccc003333000dd000140, 1, 6),
  (0x73688d52000000000000000000000000001ffff99affff9b7fffe6bffe88fd2, 1, 6),
  (0x73400002000000000000000000000000000000199a00019b400066b00c00282, 1, 6),
  (0x288d5000000000000000000000000000066660003332000ccc80022288c10, 1, 7),
  (0x1999999a000000333366b00400280, 1, 6),
  (0x7341228a000000000000000000000000001fffffffcccd9b7ffffffddcd23ca, 1, 7),
  (0x734000020000000000000000000000000000000000cccd9b4000000dd800142, 1, 6),
  (0x1228800000000000000000000000000066666650000000ccc994000d2008, 1, 6),
  (0x400000000000000000000000000000001999999acccd9b400000000400200, 1, 6),
  (0x73423222000000000000000000000000001ffffffffffffff33366bddf233e2, 1, 9),
  (0x730000020000000000000000000000000000000000000000333366bdd8001c2, 1, 6),
  (0x232200000000000000000000000000006666665333264800000000323020, 1, 6),
  (0x40000004000000000000000000000000001e001e00f001e03c00780e0800804, 2, 10),
  (0xffffffffffffffffffffffffffe000000000000000000007c000997fffffffffffffffffffffffffffffe1ffcfff1ffbffc7fcfe83fd97, 2, 11),
  (0x3c00008000000000000000000000000000001e001c00f003803c00c0e003480, 2, 10),
  (0xffffffffffffffffffffffffffe0000000000000000000000000913ffffffffffffffffffffffffffe1e001e00f001c03c00701003c113, 2, 10),
  (0x1e1e0000f0f0003c3c000ee000c00, 2, 10),
  (0x7c288dd4000000000000000000000000001ffffe1cffffe3bffff8cffa8bdd4, 2, 10),
  (0x7c0000840000000000000000000000000000001e1c0001e3800078c00803084, 2, 10),
  (0x288d500000000000000000000000000001e1e0000f0e0003c380011288150, 2, 12),
  (0x80000000000000000000000000001e1e1e1c0000003c3c78c00002080, 2, 10),
  (0x7c01228c000000000000000000000000001ffffffff0f1e3bffffffeecd3e8c, 2, 13),
  (0x7c0000040000000000000000000000000000000000f0f1e38000000ee801c04, 2, 10),
  (0x122080000000000000000000000000001e1e1e300000003c3873004d0208, 2, 10),
  (0x1e1e1e1cf0f1e3800000000003000, 2, 10),
  (0x7c4232a4000000000000000000000000001ffffffffffffffc3c78ceef23ea4, 2, 12),
  (0x7c00008400000000000000000000000000000000000000003c3c78cee800c84, 2, 10),
  (0x4232200000000000000000000000000001e1e1e30f0e1c400000000720220, 2, 10),
  (0x910000000000000000000000000001fe00000ff00003fc0000f0008910, 3, 14),
  (0xffffffffffffffffffffffffffe0000000000000000000040288d57ffffffffffffffffffffffffffffffffe0fffffc3fffff0ffabcd57, 3, 15),
  (0xffffffffffffffffffffffffffe0000000000000000000040000007ffffffffffffffffffffffffffe0001fe00001fc00007f000834007, 3, 14),
  (0x28844000000000000000000000000000001fe00000fe00003f8000f280440, 3, 14),
  (0x1fe01fe00000003fc07f000010000, 3, 14),
  (0xffffffffffffffffffffffffffe0000000000000000000040012b9fffffffffffffffffffffffffffffffffffff01fc3fffffff0cfeb9f, 3, 16),
  (0xffffffffffffffffffffffffffe0000000000000000000040000917ffffffffffffffffffffffffffe0000000ff01fc0000000f082c917, 3, 14),
  (0x1228800000000000000000000000000001fe01f000000003f80f004c2288, 3, 14),
  (0x1fe01fe0ff01fc000000000020000, 3, 14),
  (0xffffffffffffffffffffffffffe0000000000000000000040423b37ffffffffffffffffffffffffffffffffffffffffffc07f0f0f3fb37, 3, 17),
  (0xffffffffffffffffffffffffffe0000000000000000000040000917ffffffffffffffffffffffffffe00000000000003fc07f0f081c917, 3, 14),
  (0x42322000000000000000000000000000001fe01f00fe03c00000000703220, 3, 14),
  (0x1fffe0000000003fff80000080000, 5, 18),
  (0x29afd8000000000000000000000000001ffffffffffe003ffffffff6dafd8, 5, 19),
  (0x288d500000000000000000000000000000000000fffe000000000ff208d50, 5, 18),
  (0x122880000000000000000000000000000001fff00000000007ff00452288, 5, 18),
  (0x1fffe000fffe00000000000200000, 6, 20),
  (0x6abf70000000000000000000000000001fffffffffffffffff800ff7abf70, 6, 21),
  (0x288d5000000000000000000000000000000000000000003fff800ff088d50, 6, 20),
  (0x4232200000000000000000000000000000001fff0001ffc00000000523220, 6, 20),
  (0x2200000000000000000000000000001fffffff000000000000000402200, 5, 18),
  (0x4332a8000000000000000000000000001ffffffffffffffffffff007f32a8, 5, 22),
  (0x1008800000000000000000000000000000000000000003ffffff000d0088, 5, 18),
  (0x4210200000000000000000000000000000000000ffffffc00000000321020, 5, 18)]

def heldB (ds : List W) (v : W) : Bool :=
  v == 0 || v == ~~~0 || ds.any (fun d => v == d || v == ~~~d)

theorem held_sound {ds : List W} {v : W} (h : heldB ds v = true) : holds ds.toFinset v := by
  simp only [heldB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with (h|h)|⟨d,hd,h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨d, List.mem_toFinset.mpr hd, h⟩)

def mapsB (p : Array Nat) (xs ys : List W) :=
  xs.all fun w => heldB ys (proj p w)

theorem maps_sound {p xs ys} (h : mapsB p xs ys = true) :
    ∀ u ∈ xs.toFinset, holds ys.toFinset (proj p u) := by
  intro u hu
  exact held_sound ((List.all_eq_true.mp h) u (List.mem_toFinset.mp hu))

def cleanB (p : Array Nat) (i : Fin 220) (xs : List W) :=
  xs.all fun w => (w.getLsbD (220+i.val) == w.getLsbD i.val) ||
      (proj p w == 0 || proj p w == ~~~0)

theorem clean_sound {p i xs} (h : cleanB p i xs = true) : clean p i xs.toFinset := by
  intro u hu diff
  have q := (List.all_eq_true.mp h) u (List.mem_toFinset.mp hu)
  simp only [Bool.or_eq_true,beq_iff_eq] at q
  exact q.resolve_left diff

def firstResults : List W := rows.flatMap fun a =>
  rows.flatMap fun b => if a = b then [] else ops a b

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem covers : firstResults.all (fun z => cases.any (fun c => c.1 == z)) = true := by decide +kernel

theorem firstCase {a b z : W} (ha : a ∈ rows.toFinset) (hb : b ∈ rows.toFinset)
    (ne : a ≠ b) (hz : z ∈ basicOps a b) : ∃ c ∈ cases, c.1 = z := by
  have hr : z ∈ firstResults := by
    refine List.mem_flatMap.mpr ⟨a,List.mem_toFinset.mp ha,List.mem_flatMap.mpr ⟨b,List.mem_toFinset.mp hb,?_⟩⟩
    simpa only [if_neg ne] using List.mem_toFinset.mp hz
  simpa only [List.any_eq_true, beq_iff_eq] using List.all_eq_true.mp covers z hr

def sparseMaps (bins : Bins) (xs ys : List W) :=
  xs.all fun w => heldB ys (sparseImage bins w)

def sparseClean (bins : Bins) (i : Fin 220) (xs : List W) :=
  xs.all fun w => (w.getLsbD (220+i.val) == w.getLsbD i.val) ||
      (sparseImage bins w == 0 || sparseImage bins w == ~~~0)

def firstOK (c : Case) :=
  sparseMaps (toSixBins c.2.1) (c.1::rows) (six c.2.1) &&
  sparseClean (toSixBins c.2.1) c.2.2 (c.1::rows)

def laterOK (i : Nat) :=
  (sparseImage (toSixBins i) goal == goal) && (sparseImage (toFiveBins i) goal == goal) &&
  sparseMaps (toFiveBins i) (six i) five && sparseClean (toFiveBins i) 0 (six i)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst0 : firstOK (0x220000000000000000000000000000000011111112888912622244a99800002, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst1 : firstOK (0x7b54c002fffffffffffffffffffffffffffddddddfeeefdffbbbf7fffd4c3ff, 0, 1) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst2 : firstOK (0x814c000ffffffffffffffffffffffffffe444444522224488889142214c03d, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst3 : firstOK (0x5140000200000000000000000000000000088888884444891111221444003c0, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst4 : firstOK (0x280000000000000000000000000000000014141414a0a142a82850caa800004, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst5 : firstOK (0x7e14c084ffffffffffffffffffffffffffff5f5f5ffafbf7febefdeff94fcbf, 0, 2) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst6 : firstOK (0x214c000ffffffffffffffffffffffffffe14141430a0a1442828521114c03b, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst7 : firstOK (0x54000084000000000000000000000000000a0a0a085050a1141428044003c80, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst8 : firstOK (0xfffffffffffffffffffffffffff5401540aa01542a80550b080c017, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst9 : firstOK (0xffffffffffffffffffffffffffe000000000000000000006a14c917fffffffffffffffffffffffffffff55ff7ffabfeffeaffefb97c93f, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst10 : firstOK (0x2a14c000000000000000000000000000000015401700aa02c02a80e0b140028, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst11 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040000917000000000000000000000000000aa00aa05500a815402a040030900, 0, 3) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst12 : firstOK (0x80000000000000000000000000000015554000aaaa002aaa800bb008010, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst13 : firstOK (0x2a3ccd50fffffffffffffffffffffffffffffff557ffff56ffffd5effbccd7f, 0, 4) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst14 : firstOK (0x2a144000ffffffffffffffffffffffffffe0001557000156c00055e0094402f, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst15 : firstOK (0x280d50000000000000000000000000000aaaa000555400155500044280d40, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst16 : firstOK (0x155555570000002aaad5e00040008, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst17 : firstOK (0x2a15e288ffffffffffffffffffffffffffffffffffaaab56fffffffbbdde2bf, 0, 3) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst18 : firstOK (0x2a14c000ffffffffffffffffffffffffffe0000000aaab56c000000bb90c037, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst19 : firstOK (0x12288000000000000000000000000000aaaaaa800000015552a100492280, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst20 : firstOK (0x15555557aaab56c00000000100020, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst21 : firstOK (0x2a56f220ffffffffffffffffffffffffffffffffffffffffeaaad5ebbf6f23f, 0, 5) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst22 : firstOK (0x2a14c000ffffffffffffffffffffffffffe00000000000002aaad5ebb84c01f, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst23 : firstOK (0x423220000000000000000000000000000aaaaaa85554a9000000000623200, 0, 0) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst24 : firstOK (0x700000000000000000000000000000000018181818c0c1833030608cc800080, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst25 : firstOK (0x7f400086000000000000000000000000001f9f9f9efcfdfbff3f7efffc03fc6, 1, 7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst26 : firstOK (0x340000200000000000000000000000000018181820c0c18430306311400342, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst27 : firstOK (0xc00008400000000000000000000000000060606043030608c0c18422003c04, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst28 : firstOK (0x400000020000000000000000000000000019801980cc01983300660d0800102, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst29 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000073400917fffffffffffffffffffffffffffff99ffaffcdff7ff37fbfdc3cbd7, 1, 8) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst30 : firstOK (0x33400000000000000000000000000000000019801a00cc03403300b0d4002c0, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst31 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000000000915ffffffffffffffffffffffffffe66006603300640cc01902003c815, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst32 : firstOK (0x19998000cccc003333000dd000140, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst33 : firstOK (0x73688d52000000000000000000000000001ffff99affff9b7fffe6bffe88fd2, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst34 : firstOK (0x73400002000000000000000000000000000000199a00019b400066b00c00282, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst35 : firstOK (0x288d5000000000000000000000000000066660003332000ccc80022288c10, 1, 7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst36 : firstOK (0x1999999a000000333366b00400280, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst37 : firstOK (0x7341228a000000000000000000000000001fffffffcccd9b7ffffffddcd23ca, 1, 7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst38 : firstOK (0x734000020000000000000000000000000000000000cccd9b4000000dd800142, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst39 : firstOK (0x1228800000000000000000000000000066666650000000ccc994000d2008, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst40 : firstOK (0x400000000000000000000000000000001999999acccd9b400000000400200, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst41 : firstOK (0x73423222000000000000000000000000001ffffffffffffff33366bddf233e2, 1, 9) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst42 : firstOK (0x730000020000000000000000000000000000000000000000333366bdd8001c2, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst43 : firstOK (0x232200000000000000000000000000006666665333264800000000323020, 1, 6) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst44 : firstOK (0x40000004000000000000000000000000001e001e00f001e03c00780e0800804, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst45 : firstOK (0xffffffffffffffffffffffffffe000000000000000000007c000997fffffffffffffffffffffffffffffe1ffcfff1ffbffc7fcfe83fd97, 2, 11) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst46 : firstOK (0x3c00008000000000000000000000000000001e001c00f003803c00c0e003480, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst47 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000000000913ffffffffffffffffffffffffffe1e001e00f001c03c00701003c113, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst48 : firstOK (0x1e1e0000f0f0003c3c000ee000c00, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst49 : firstOK (0x7c288dd4000000000000000000000000001ffffe1cffffe3bffff8cffa8bdd4, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst50 : firstOK (0x7c0000840000000000000000000000000000001e1c0001e3800078c00803084, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst51 : firstOK (0x288d500000000000000000000000000001e1e0000f0e0003c380011288150, 2, 12) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst52 : firstOK (0x80000000000000000000000000001e1e1e1c0000003c3c78c00002080, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst53 : firstOK (0x7c01228c000000000000000000000000001ffffffff0f1e3bffffffeecd3e8c, 2, 13) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst54 : firstOK (0x7c0000040000000000000000000000000000000000f0f1e38000000ee801c04, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst55 : firstOK (0x122080000000000000000000000000001e1e1e300000003c3873004d0208, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst56 : firstOK (0x1e1e1e1cf0f1e3800000000003000, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst57 : firstOK (0x7c4232a4000000000000000000000000001ffffffffffffffc3c78ceef23ea4, 2, 12) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst58 : firstOK (0x7c00008400000000000000000000000000000000000000003c3c78cee800c84, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst59 : firstOK (0x4232200000000000000000000000000001e1e1e30f0e1c400000000720220, 2, 10) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst60 : firstOK (0x910000000000000000000000000001fe00000ff00003fc0000f0008910, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst61 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040288d57ffffffffffffffffffffffffffffffffe0fffffc3fffff0ffabcd57, 3, 15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst62 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040000007ffffffffffffffffffffffffffe0001fe00001fc00007f000834007, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst63 : firstOK (0x28844000000000000000000000000000001fe00000fe00003f8000f280440, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst64 : firstOK (0x1fe01fe00000003fc07f000010000, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst65 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040012b9fffffffffffffffffffffffffffffffffffff01fc3fffffff0cfeb9f, 3, 16) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst66 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040000917ffffffffffffffffffffffffffe0000000ff01fc0000000f082c917, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst67 : firstOK (0x1228800000000000000000000000000001fe01f000000003f80f004c2288, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst68 : firstOK (0x1fe01fe0ff01fc000000000020000, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst69 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040423b37ffffffffffffffffffffffffffffffffffffffffffc07f0f0f3fb37, 3, 17) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst70 : firstOK (0xffffffffffffffffffffffffffe0000000000000000000040000917ffffffffffffffffffffffffffe00000000000003fc07f0f081c917, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst71 : firstOK (0x42322000000000000000000000000000001fe01f00fe03c00000000703220, 3, 14) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst72 : firstOK (0x1fffe0000000003fff80000080000, 5, 18) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst73 : firstOK (0x29afd8000000000000000000000000001ffffffffffe003ffffffff6dafd8, 5, 19) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst74 : firstOK (0x288d500000000000000000000000000000000000fffe000000000ff208d50, 5, 18) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst75 : firstOK (0x122880000000000000000000000000000001fff00000000007ff00452288, 5, 18) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst76 : firstOK (0x1fffe000fffe00000000000200000, 6, 20) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst77 : firstOK (0x6abf70000000000000000000000000001fffffffffffffffff800ff7abf70, 6, 21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst78 : firstOK (0x288d5000000000000000000000000000000000000000003fff800ff088d50, 6, 20) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst79 : firstOK (0x4232200000000000000000000000000000001fff0001ffc00000000523220, 6, 20) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst80 : firstOK (0x2200000000000000000000000000001fffffff000000000000000402200, 5, 18) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst81 : firstOK (0x4332a8000000000000000000000000001ffffffffffffffffffff007f32a8, 5, 22) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst82 : firstOK (0x1008800000000000000000000000000000000000000003ffffff000d0088, 5, 18) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst83 : firstOK (0x4210200000000000000000000000000000000000ffffffc00000000321020, 5, 18) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allFirst : cases.all firstOK = true := by
  simp only [cases, List.all_cons, List.all_nil, Bool.true_and, allFirst0, allFirst1, allFirst2, allFirst3, allFirst4, allFirst5, allFirst6, allFirst7, allFirst8, allFirst9, allFirst10, allFirst11, allFirst12, allFirst13, allFirst14, allFirst15, allFirst16, allFirst17, allFirst18, allFirst19, allFirst20, allFirst21, allFirst22, allFirst23, allFirst24, allFirst25, allFirst26, allFirst27, allFirst28, allFirst29, allFirst30, allFirst31, allFirst32, allFirst33, allFirst34, allFirst35, allFirst36, allFirst37, allFirst38, allFirst39, allFirst40, allFirst41, allFirst42, allFirst43, allFirst44, allFirst45, allFirst46, allFirst47, allFirst48, allFirst49, allFirst50, allFirst51, allFirst52, allFirst53, allFirst54, allFirst55, allFirst56, allFirst57, allFirst58, allFirst59, allFirst60, allFirst61, allFirst62, allFirst63, allFirst64, allFirst65, allFirst66, allFirst67, allFirst68, allFirst69, allFirst70, allFirst71, allFirst72, allFirst73, allFirst74, allFirst75, allFirst76, allFirst77, allFirst78, allFirst79, allFirst80, allFirst81, allFirst82, allFirst83]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater0 : laterOK 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater1 : laterOK 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater2 : laterOK 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater3 : laterOK 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater4 : laterOK 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater5 : laterOK 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLater : [0,1,2,3,5,6].all laterOK = true := by
  simp only [List.all_cons, List.all_nil, Bool.true_and, allLater0, allLater1, allLater2, allLater3, allLater4, allLater5]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem indices : cases.all (fun c => ([0,1,2,3,5,6] : List Nat).contains c.2.1) = true := by decide +kernel

theorem alwaysDiff {t : W} (h : t = goal ∨ t = ~~~goal) (i : Fin 220) : differs i t := by
  have all : ∀ j : Fin 220, differs j goal ∧ differs j (~~~goal) := by unfold differs; decide +kernel
  rcases h with rfl|rfl
  · exact (all i).1
  · exact (all i).2


def withNext (next : Nat → List W → Bool) (extra : Nat) (ws : List W) : Bool :=
  (ws == [goal] || ws == [~~~goal]) || (pairs ws).any (fun (a,b,r) => dispatch extra next a b r)

def screened (bad : List (Nat × List W)) (f : Nat → List W → Bool) (e : Nat) (ws : List W) : Bool :=
  if (e,ws) ∈ bad then false else f e ws

theorem screened_eq (bad : List (Nat × List W)) (f : Nat → List W → Bool)
    (empty : ∀ s ∈ bad, f s.1 s.2 = false) : screened bad f = f := by
  funext e ws
  by_cases h : (e,ws) ∈ bad
  · simpa only [screened,if_pos h] using (empty (e,ws) h).symm
  · simp only [screened,if_neg h]
def wire0 : W := 0x80200802008020080200802008020080200802008020080200802ffc00ffc00ffc00ffc00ffc00ffffffffff003fffffffffc00fffff
def wire1 : W := 0x4912449124491244912449124491244912449124491244912449124fffff00000fffff00000fffff003ff003ffffc00ffc00fffff003ff
def wire2 : W := 0x9224892248922489224892248922489224892248922489224892248ffffffffff0000000000fffffffc00003fffffff00000fffffffc00
def wire3 : W := 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070ffffffffffffffffffff0000000000003ffffffffffff0000000000
def wire4 : W := 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380ffffffffffffffffffffffffffffffffc0000000000000000000000
def wire5 : W := 0xffc0000000ffc0000000ffc00003ff003ff00000ffc00ffc00003ff
def wire6 : W := 0x4992649926499264992649926499264992649926499264992649926fffffffc00fffffffc00fffffffffffffffffffffffffffffffffff
def wire7 : W := 0x8020080200802008020080200802008020080200802008020080200000ffc0000000ffc0000000ffc00ffc00003ff003ff00000ffc00
def wire8 : W := 0x4912449124491244912449124491244912449124491244912449124003ff00000003ff00000003ff0000000000ffc0000000003ff00000
def wire9 : W := 0xffc00ffc000000000000ffc00ffc00003ff003ff00000ffc00ffc00
def wire10 : W := 0x92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4a92a4affffffffffffc00ffc00fffffffffffffffffffffffffffffffffff
def wire11 : W := 0x802008020080200802008020080200802008020080200802008020000000000ffc00ffc0000000003ffffc0000000fffff00000003ff
def wire12 : W := 0x9224892248922489224892248922489224892248922489224892248003ff003ff0000000000003ff0000000000ffc0000000003ff00000
def wire13 : W := 0xffc00ffc00ffc00ffc000000000000003ff003fffffff0000000000
def wire14 : W := 0x1c8721c8721c8721c8721c8721c8721c8721c8721c8721c8721c872ffffffffffffffffffffffc00ffffffffffffffffffffffc00fffff
def wire15 : W := 0x8020080200802008020080200802008020080200802008020080200000000000000000000ffc00fffffffc000000000000ffc00fffff
def wire16 : W := 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070003ff003ff003ff003ff000000000000000ffc00000000000000000
def wire17 : W := 0xffc00ffc00ffc00ffc00ffc00fffffffc0000000000000000000000
def wire18 : W := 0xe0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82e0b82fffffffffffffffffffffffffffffffffff003fffffffffc00fffff
def wire19 : W := 0x80200802008020080200802008020080200802008020080200802000000000000000000000000000000003ff003fffffffffc00fffff
def wire20 : W := 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e0380003ff003ff003ff003ff003ff000000000000000000000000000000
def wire21 : W := 0xfffff000000000000000fffff00000003ffffc0000000fffff00000
def wire22 : W := 0xdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cdb36cfffffffffffffff00000ffffffffff003fffffffffc00ffffffffff
def wire23 : W := 0x49124491244912449124491244912449124491244912449124491240000000000fffff0000000000003ff0000000000ffc0000000003ff
def wire24 : W := 0x922489224892248922489224892248922489224892248922489224800000fffff000000000000000ffc0000000003ff0000000000ffc00
def wire25 : W := 0x802008020080200802008020080200802008020080200802008020fffff00000fffff000000000000000003ffffc00ffc000000000000
def wire26 : W := 0x5d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d174fffffffffffffffffffffffff003ff003fffffffffffffffff003ff
def wire27 : W := 0x411044110441104411044110441104411044110441104411044110400000000000000000000fffff003ff000000000000000fffff003ff
def wire28 : W := 0x140501405014050140501405014050140501405014050140501405000000fffff00000fffff000000000000000003ff003ff0000000000
def wire29 : W := 0x4010040100401004010040100401004010040100401004010040100fffff00000fffff00000fffff003ff0000000000000000000000000
def wire30 : W := 0xe93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4fffffffffffffffffffffffffffffffffffffc00ffc00fffff003ff
def wire31 : W := 0x902409024090240902409024090240902409024090240902409024000000000000000000000000000000003ffffc00ffc00fffff003ff
def wire32 : W := 0xa0280a0280a0280a0280a0280a0280a0280a0280a0280a0280a028000000fffff00000fffff00000ffc00ffc0000000000000000000000
def wire33 : W := 0x1004010040100401004010040100401004010040100401004010040ffffffffff00000000000000000000003fffffff000000000000000
def wire34 : W := 0x9e2789e2789e2789e2789e2789e2789e2789e2789e2789e2789e278fffffffffffffffffffffffffffc00003fffffffffffffffffffc00
def wire35 : W := 0x822088220882208822088220882208822088220882208822088220800000000000000000000fffffffc00000000000000000fffffffc00
def wire36 : W := 0xc0300c0300c0300c0300c0300c0300c0300c0300c0300c0300c0300000000000ffffffffff00000000000000000000fffff0000000000
def wire37 : W := 0x8020080200802008020080200802008020080200802008020080200ffffffffff0000000000fffffffc000000000000000000000000000
def wire38 : W := 0xf23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8f23c8ffffffffffffffffffffffffffffffffffffffff00000fffffffc00
def wire39 : W := 0x1204812048120481204812048120481204812048120481204812048000000000000000000000000000000003fffffff00000fffffffc00
def wire40 : W := 0x60180601806018060180601806018060180601806018060180601800000000000ffffffffff00000003ffffc0000000000000000000000
def wire41 : W := 0xffffffffffffffffffff00000000000000000000000000000000000
def wire42 : W := 0xfc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fffffffffffffffffffffffffffffffffffffffffffff0000000000
def wire43 : W := 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c070000000000000000000000000000000003ffffffffffff0000000000
def wire44 : W := 0xe0380e0380e0380e0380e0380e0380e0380e0380e0380e0380e038000000000000000000000ffffffffffffc0000000000000000000000
def state0 : Nat × List W := (1, [wire5, wire0, wire1, wire2, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects0 : optimized 6 state0.1 state0.2 = false := by decide +kernel
def state1 : Nat × List W := (1, [wire6, wire0, wire1, wire2, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects1 : optimized 6 state1.1 state1.2 = false := by decide +kernel
def state2 : Nat × List W := (1, [wire7, wire0, wire1, wire2, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects2 : optimized 6 state2.1 state2.2 = false := by decide +kernel
def state3 : Nat × List W := (1, [wire8, wire0, wire1, wire2, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects3 : optimized 6 state3.1 state3.2 = false := by decide +kernel
def state4 : Nat × List W := (1, [wire9, wire0, wire2, wire1, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects4 : optimized 6 state4.1 state4.2 = false := by decide +kernel
def state5 : Nat × List W := (1, [wire10, wire0, wire2, wire1, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects5 : optimized 6 state5.1 state5.2 = false := by decide +kernel
def state6 : Nat × List W := (1, [wire11, wire0, wire2, wire1, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects6 : optimized 6 state6.1 state6.2 = false := by decide +kernel
def state7 : Nat × List W := (1, [wire12, wire0, wire2, wire1, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects7 : optimized 6 state7.1 state7.2 = false := by decide +kernel
def state8 : Nat × List W := (1, [wire13, wire0, wire3, wire1, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects8 : optimized 6 state8.1 state8.2 = false := by decide +kernel
def state9 : Nat × List W := (1, [wire14, wire0, wire3, wire1, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects9 : optimized 6 state9.1 state9.2 = false := by decide +kernel
def state10 : Nat × List W := (1, [wire15, wire0, wire3, wire1, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects10 : optimized 6 state10.1 state10.2 = false := by decide +kernel
def state11 : Nat × List W := (1, [wire16, wire0, wire3, wire1, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects11 : optimized 6 state11.1 state11.2 = false := by decide +kernel
def state12 : Nat × List W := (1, [wire17, wire0, wire4, wire1, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects12 : optimized 6 state12.1 state12.2 = false := by decide +kernel
def state13 : Nat × List W := (1, [wire18, wire0, wire4, wire1, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects13 : optimized 6 state13.1 state13.2 = false := by decide +kernel
def state14 : Nat × List W := (1, [wire19, wire0, wire4, wire1, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects14 : optimized 6 state14.1 state14.2 = false := by decide +kernel
def state15 : Nat × List W := (1, [wire20, wire0, wire4, wire1, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects15 : optimized 6 state15.1 state15.2 = false := by decide +kernel
def state16 : Nat × List W := (1, [wire21, wire1, wire2, wire0, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects16 : optimized 6 state16.1 state16.2 = false := by decide +kernel
def state17 : Nat × List W := (1, [wire22, wire1, wire2, wire0, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects17 : optimized 6 state17.1 state17.2 = false := by decide +kernel
def state18 : Nat × List W := (1, [wire23, wire1, wire2, wire0, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects18 : optimized 6 state18.1 state18.2 = false := by decide +kernel
def state19 : Nat × List W := (1, [wire24, wire1, wire2, wire0, wire3, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects19 : optimized 6 state19.1 state19.2 = false := by decide +kernel
def state20 : Nat × List W := (1, [wire25, wire1, wire3, wire0, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects20 : optimized 6 state20.1 state20.2 = false := by decide +kernel
def state21 : Nat × List W := (1, [wire26, wire1, wire3, wire0, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects21 : optimized 6 state21.1 state21.2 = false := by decide +kernel
def state22 : Nat × List W := (1, [wire27, wire1, wire3, wire0, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects22 : optimized 6 state22.1 state22.2 = false := by decide +kernel
def state23 : Nat × List W := (1, [wire28, wire1, wire3, wire0, wire2, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects23 : optimized 6 state23.1 state23.2 = false := by decide +kernel
def state24 : Nat × List W := (1, [wire29, wire1, wire4, wire0, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects24 : optimized 6 state24.1 state24.2 = false := by decide +kernel
def state25 : Nat × List W := (1, [wire30, wire1, wire4, wire0, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects25 : optimized 6 state25.1 state25.2 = false := by decide +kernel
def state26 : Nat × List W := (1, [wire31, wire1, wire4, wire0, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects26 : optimized 6 state26.1 state26.2 = false := by decide +kernel
def state27 : Nat × List W := (1, [wire32, wire1, wire4, wire0, wire2, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects27 : optimized 6 state27.1 state27.2 = false := by decide +kernel
def state28 : Nat × List W := (1, [wire33, wire2, wire3, wire0, wire1, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects28 : optimized 6 state28.1 state28.2 = false := by decide +kernel
def state29 : Nat × List W := (1, [wire34, wire2, wire3, wire0, wire1, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects29 : optimized 6 state29.1 state29.2 = false := by decide +kernel
def state30 : Nat × List W := (1, [wire35, wire2, wire3, wire0, wire1, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects30 : optimized 6 state30.1 state30.2 = false := by decide +kernel
def state31 : Nat × List W := (1, [wire36, wire2, wire3, wire0, wire1, wire4])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects31 : optimized 6 state31.1 state31.2 = false := by decide +kernel
def state32 : Nat × List W := (1, [wire37, wire2, wire4, wire0, wire1, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects32 : optimized 6 state32.1 state32.2 = false := by decide +kernel
def state33 : Nat × List W := (1, [wire38, wire2, wire4, wire0, wire1, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects33 : optimized 6 state33.1 state33.2 = false := by decide +kernel
def state34 : Nat × List W := (1, [wire39, wire2, wire4, wire0, wire1, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects34 : optimized 6 state34.1 state34.2 = false := by decide +kernel
def state35 : Nat × List W := (1, [wire40, wire2, wire4, wire0, wire1, wire3])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects35 : optimized 6 state35.1 state35.2 = false := by decide +kernel
def state36 : Nat × List W := (1, [wire41, wire3, wire4, wire0, wire1, wire2])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects36 : optimized 6 state36.1 state36.2 = false := by decide +kernel
def state37 : Nat × List W := (1, [wire42, wire3, wire4, wire0, wire1, wire2])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects37 : optimized 6 state37.1 state37.2 = false := by decide +kernel
def state38 : Nat × List W := (1, [wire43, wire3, wire4, wire0, wire1, wire2])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects38 : optimized 6 state38.1 state38.2 = false := by decide +kernel
def state39 : Nat × List W := (1, [wire44, wire3, wire4, wire0, wire1, wire2])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rejects39 : optimized 6 state39.1 state39.2 = false := by decide +kernel
def roots : List (Nat × List W) := [state0, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, state12, state13, state14, state15, state16, state17, state18, state19, state20, state21, state22, state23, state24, state25, state26, state27, state28, state29, state30, state31, state32, state33, state34, state35, state36, state37, state38, state39]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded : ∀ s ∈ roots, optimized 6 s.1 s.2 = false := by
  intro s hs
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rejects0
  · exact rejects1
  · exact rejects2
  · exact rejects3
  · exact rejects4
  · exact rejects5
  · exact rejects6
  · exact rejects7
  · exact rejects8
  · exact rejects9
  · exact rejects10
  · exact rejects11
  · exact rejects12
  · exact rejects13
  · exact rejects14
  · exact rejects15
  · exact rejects16
  · exact rejects17
  · exact rejects18
  · exact rejects19
  · exact rejects20
  · exact rejects21
  · exact rejects22
  · exact rejects23
  · exact rejects24
  · exact rejects25
  · exact rejects26
  · exact rejects27
  · exact rejects28
  · exact rejects29
  · exact rejects30
  · exact rejects31
  · exact rejects32
  · exact rejects33
  · exact rejects34
  · exact rejects35
  · exact rejects36
  · exact rejects37
  · exact rejects38
  · exact rejects39
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem noFive : optimized 7 3 five = false := by
  change withNext (optimized 6) 3 five = false
  rw [← screened_eq roots (optimized 6) excluded]
  have evaluate (f : Nat → List W → Bool) : withNext (screened roots f) 3 five = false := by rfl
  exact evaluate _
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem smallReject : search 7 five = false := by
  unfold search
  have only (f : Nat → List W → Bool) (h : f 3 five = false) :
      five.sublists.any (fun ws => decide (ws.length ≤ 7+1) && (cuts ws == -1) && f (7+1-ws.length) ws) = false := by
    have mask : (fun e ws => if e = 3 ∧ ws = five then false else f e ws) = f := by
      funext e ws
      split
      · rename_i h'
        rw [h'.1,h'.2,h]
      · rfl
    rw [← mask]
    rfl
  exact only (optimized 7) noFive


theorem ruledOut (c : Case) (hc : c ∈ cases) {t : W}
    (ht : t = goal ∨ t = ~~~goal) (k : Nat) (low : k ≤ 9)
    (hr : build basicOps t k (c.1 :: rows).toFinset) : False := by
  have yes := List.all_eq_true.mp allFirst c hc
  have ix : c.2.1 ∈ ([0,1,2,3,5,6] : List Nat) := by
    simpa only [List.contains_iff_mem] using List.all_eq_true.mp indices c hc
  have later := List.all_eq_true.mp allLater c.2.1 ix
  simp only [firstOK, sparseMaps, sparseClean, toSixImage, Bool.and_eq_true] at yes
  simp only [laterOK, sparseMaps, sparseClean, toSixImage, toFiveImage, Bool.and_eq_true, beq_iff_eq] at later
  obtain ⟨v,n,hv,run,_,h⟩ :=
    shrink (toSix c.2.1) c.2.2 later.1.1.1 ht (alwaysDiff ht _) k (maps_sound yes.1) hr
  have hn := h (clean_sound yes.2)
  obtain ⟨w,m,hw,run',_,h'⟩ :=
    shrink (toFive c.2.1) 0 later.1.1.2 hv (alwaysDiff hv _) n (maps_sound later.1.2) run
  have hm := h' (clean_sound later.2)
  have lift {a b : Nat} (hle : a ≤ b) (hbuild : build basicOps w a five.toFinset) :
      build basicOps w b five.toFinset := by
    induction hle with
    | refl => exact hbuild
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (smallReject.symm.trans (search_complete hw 7 five (by decide) (lift (by omega) run')))

theorem noSmall {t : W} (ht : t = goal ∨ t = ~~~goal) (k : Nat) (low : k ≤ 10)
    (run : build basicOps t k rows.toFinset) : False := by
  induction k with
  | zero =>
    rcases ht with rfl|rfl <;> change _ ∈ rows.toFinset at run <;> revert run <;> decide +kernel
  | succ k ih =>
    rcases run with h|⟨a,ha,b,hb,ne,z,hz,hr⟩
    · exact ih (by omega) h
    · obtain ⟨c,hc,rfl⟩ := firstCase ha hb ne hz
      apply ruledOut c hc ht k (by omega)
      simpa only [List.toFinset_cons] using hr

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sample : ∀ k : Fin 440, F (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows, holds rows.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 440) :
      (gs.foldl step (rows.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 7) : Bool := bit k (rows.getD i.val 0)
    have same : List.ofFn x = rows.map (bit k) := by
      apply List.ext_getElem
      · simp [rows]
      · intro i hi hj
        have hlt : i < rows.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (rows.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows rows.toFinset init evaluate
  exact noSmall ht _ low run

end PEqualNP.Outside.L_meta_10910.Signed


namespace PEqualNP.Outside.L_meta_10910

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6)) := by
  decide

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 15]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [12, 17]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide

end PEqualNP.Outside.L_meta_10910

theorem PEqualNP.Outside.L_meta_10910 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_10910.Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_10910.Signed.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_10910.Signed.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_10910.Signed.bound gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_10910.bridge x))
    have hl : PEqualNP.Outside.L_meta_10910.wg.length = 12 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10910.wg, 18, PEqualNP.Outside.L_meta_10910.wfits, by omega, PEqualNP.Outside.L_meta_10910.weval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
