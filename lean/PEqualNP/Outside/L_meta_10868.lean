import PEqualNP.Defs

-- A circuit containing a NOT has strictly more gates than binary gates.
-- The signed lower bound rules out ten binary gates, and the explicit AND/OR circuit uses twelve.
-- The signed live-wire search and its correctness proof follow the checked L-meta-9146
-- and L-meta-8633 by k-sandhu, following L-meta-8463 and L-meta-1449 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_10868.Signed

-- Each sampled positive assignment is paired with each negative assignment.
-- Separating all pairs is necessary at every live set of wires.

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
abbrev W := BitVec 4830
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 2415 := ((x >>> 2415) ^^^ x).setWidth 2415
def cuts (ws : List W) : BitVec 2415 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 2415) ++ (0 : BitVec 2415)
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

def differs (i : Fin 2415) (w : W) : Prop :=
  w.getLsbD (2415+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 2415) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 2415+i.val < 4830 := by omega
  have hi' : i.val < 4830 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 2415) :
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
  change (cuts ws)[j] = (BitVec.allOnes 2415)[j]
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
  · change reachable av (BitVec.allOnes 4830 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 4830)
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

private def bit (k : Fin 4830) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 4830) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 4830) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#4830)[k.val] = false; simp
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

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 5 && x 6)

theorem bound_from_search (inputs : List W) (width : inputs.length = 7)
    (reject : ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t 10 inputs.toFinset → False)
    (sample : ∀ k : Fin 4830, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 4830) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 7) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact reject t ht (lift low run)

def rows : List W :=
  [0x505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a80505500a0aa0141540282a8050557fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffffffff800000fffffe000003fffff800000fffffffffffc000007fffff000001fffffc000007fffff000001fffffc000007fffff000001fffffc000007ffffffffffe000003fffff800000fffffe000003fffff800000fffffe000003fffff800000fffffffffffffffff800000fffffffffffc000007ffffffffffe000003fffff800000fffffffffffffffffffffff,
   0x40566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b3040566080acc101598202b30405667ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000000000007ffffffffffe000003fffffffffff000000000003fffffffffff000001fffffffffff800000000001fffffffffff800000000001fffffffffff800000000001fffffffffff800000fffffffffffc00000000000fffffffffffc00000000000fffffffffffc00000000000fffffe000003fffffffffff000001fffffffffff800000ffffffffffffffffffffffffffffe000003fffff800000,
   0x1667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c01667802ccf00599e00b33c0166787ffffffffffffffffffffff800000000000000000000007ffffffffffffffffffffff800000000000000000000007ffffffffffffffffffffff800000000000000000000007ffffffffffffffffffffff800000000000000000000007ffffffffffffffffffffff800000000000000000000007ffffffffffffffffffffff800000000000000000000007ffffffffffffffffffffff800000000000000003ffffffffffffffffffffffc00000000000000001ffffffffffffffffffffffe00000000000000000000001ffffffffffffffffffffffe00000000000000000fffffffffffffffffffffff00000000000000000000000fffffffffffffffffffffff000000000003ffffffffffffffffe00000000000000000fffffffffffc00000000000fffffffffffc00000000000,
   0x218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c0218780430f00861e010c3c02187807fffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000003ffffffffffffffffffffffffffffffffff00000000000000000000000fffffffffffffffffffffff,
   0x9f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f80013f00027e0004fc0009f8007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000,
   0xe00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00001c0000380000700000e00007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000,
   0x300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c0000180000300000600000c00001800003000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

-- A restriction selects a previously sampled coordinate at each bit position.
def projection (mask : W) (j : Fin 2415) (x : W) : W :=
  (x &&& mask) ||| (~~~mask &&& ((if x.getLsbD j.val then ~~~goal else 0) |||
    (if x.getLsbD (2415+j.val) then goal else 0)))

private theorem projection_bit (m : W) (j : Fin 2415) (x : W) (i : ℕ) (hi : i < 4830) :
    (projection m j x)[i] =
      (if m[i] then x[i] else if goal[i] then x.getLsbD (2415+j.val) else x.getLsbD j.val) := by
  unfold projection
  cases x.getLsbD j.val <;> cases x.getLsbD (2415+j.val) <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.getElem_or,BitVec.getElem_and,
      BitVec.getElem_not] <;>
    cases m[i] <;> cases goal[i] <;> simp

abbrev Restriction := {p : W → W //
  (∀ x y, p (x &&& y) = p x &&& p y) ∧ (∀ x y, p (x ||| y) = p x ||| p y) ∧
  (∀ x, p (~~~x) = ~~~p x) ∧ p goal = goal}

abbrev Restriction.P (R : Restriction) := R.val
private theorem Restriction.band (R : Restriction) : ∀ x y, R.P (x &&& y) = R.P x &&& R.P y := R.property.1
private theorem Restriction.bor (R : Restriction) : ∀ x y, R.P (x ||| y) = R.P x ||| R.P y := R.property.2.1
private theorem Restriction.neg (R : Restriction) : ∀ x, R.P (~~~x) = ~~~R.P x := R.property.2.2.1
private theorem Restriction.target (R : Restriction) : R.P goal = goal := R.property.2.2.2

def restrict (m : W) (j : Fin 2415) (pg : projection m j goal = goal) : Restriction := by
  refine ⟨projection m j, ?_, ?_, ?_, pg⟩
  · intro x y
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [projection_bit, BitVec.getElem_and, BitVec.getLsbD_and]
    split <;> first | rfl | split <;> rfl
  · intro x y
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [projection_bit, BitVec.getElem_or, BitVec.getLsbD_or]
    split <;> first | rfl | split <;> rfl
  · intro x
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hj : j.val < 4830 := by omega
    have hk : 2415+j.val < 4830 := by omega
    simp only [projection_bit, BitVec.getElem_not, BitVec.getLsbD_not, hj, hk, decide_true, Bool.true_and]
    split <;> first | rfl | split <;> rfl

abbrev constWord (x : W) : Prop := x = 0 ∨ x = ~~~0
def dead (R : Restriction) (s : Finset W) : ℕ := (s.filter fun x => constWord (R.P x)).card

private theorem dead_ins_le (R : Restriction) (s : Finset W) (w : W) :
    dead R (insert w s) ≤ dead R s + 1 := by
  by_cases h : constWord (R.P w)
  · simpa only [dead, Finset.filter_insert, if_pos h] using
      Finset.card_insert_le w (s.filter fun x => constWord (R.P x))
  · simp [dead, Finset.filter_insert, h]

private theorem dead_ins_mono (R : Restriction) (s : Finset W) (w : W) :
    dead R s ≤ dead R (insert w s) := Finset.card_le_card <|
      Finset.filter_subset_filter _ (Finset.subset_insert ..)

private theorem dead_ins_keep {R : Restriction} {s : Finset W} {w : W}
    (h : ¬constWord (R.P w)) : dead R (insert w s) = dead R s := by
  simp [dead, Finset.filter_insert,h]

private theorem dead_ins_new {R : Restriction} {s : Finset W} {w : W}
    (h : constWord (R.P w)) (hm : w ∉ s) : dead R (insert w s) = dead R s + 1 := by
  simp [dead, Finset.filter_insert,h,hm]

private theorem const_closed {R : Restriction} {a b z : W} (hz : z ∈ basicOps a b)
    (ha : constWord (R.P a)) (hb : constWord (R.P b)) : constWord (R.P z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> rcases ha with ha|ha <;> rcases hb with hb|hb <;>
    simp only [R.band,R.bor,R.neg,ha,hb] <;> decide +kernel

private theorem projected_reach {R : Restriction} {av : Finset W} {a b z : W}
    (hz : z ∈ basicOps a b) (ha : holds av (R.P a)) (hb : holds av (R.P b)) :
    reachable av (R.P z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp only [R.band,R.bor,R.neg]
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)

set_option maxRecDepth 100000 in
private theorem projected_free {R : Restriction} {av : Finset W} {a b z : W}
    (hz : z ∈ basicOps a b) (ha : holds av (R.P a)) (hb : holds av (R.P b))
    (hc : constWord (R.P a) ∨ constWord (R.P b)) : holds av (R.P z) := by
  have zero : holds av (0 : W) := .inl rfl
  have ones : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have za : ∀ x : W, (0 : W) &&& x = 0 := fun _ => BitVec.zero_and
  have az : ∀ x : W, x &&& (0 : W) = 0 := fun _ => BitVec.and_zero
  have zo : ∀ x : W, (0 : W) ||| x = x := fun _ => BitVec.zero_or
  have oz : ∀ x : W, x ||| (0 : W) = x := fun _ => BitVec.or_zero
  have no : ~~~(BitVec.allOnes 4830) = (0 : W) := rfl
  have hznot := holds_not ha
  have hbn := holds_not hb
  have one : ~~~(0 : W) = BitVec.allOnes 4830 := rfl
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> rcases hc with (hc|hc)|(hc|hc) <;>
    simp only [R.band,R.bor,R.neg,hc,one,no,za,az,zo,oz,BitVec.allOnes_and,BitVec.and_allOnes,
      BitVec.or_allOnes,BitVec.allOnes_or] <;> assumption

private theorem projected_live (R : Restriction) {g : W} (hg : g = goal ∨ g = ~~~goal)
    {k : ℕ} {s av : Finset W} (hl : live basicOps g k s)
    (hs : ∀ w ∈ s, holds av (R.P w)) :
    ∃ c t, (t = goal ∨ t = ~~~goal) ∧ c + dead R s ≤ k ∧ build basicOps t c av := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at hl
    subst s
    have pg : R.P g = g := by rcases hg with rfl|rfl <;> simp only [R.target,R.neg]
    have nc : ¬constWord (R.P g) := by rw [pg]; rcases hg with rfl|rfl <;> decide +kernel
    have d : dead R {g} = 0 := by
      change dead R (insert g ∅) = 0
      rw [dead_ins_keep nc]
      simp [dead]
    have h := hs g (by simp)
    rcases h with h|h|⟨t,ht,h|h⟩
    · exact False.elim (nc (.inl h))
    · exact False.elim (nc (.inr h))
    · exact ⟨0,t,by rwa [← h,pg],by omega,ht⟩
    · have et := congrArg (fun u : W => ~~~u) h
      simp only [BitVec.not_not,pg] at et
      exact ⟨0,t,by rw [← et]; rcases hg with rfl|rfl <;> simp only [BitVec.not_not,or_true,true_or],by omega,ht⟩
  | succ k ih =>
    rcases hl with skip | ⟨a,ha,b,hb,hab,z,hz,hout,r,eq,tail⟩
    · obtain ⟨c,t,ht,le,run⟩ := ih skip hs
      exact ⟨c,t,ht,by omega,run⟩
    subst s
    have hpa := hs a ha
    have hpb := hs b hb
    have holdr (w : W) (hw : w ∈ r) := hs w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    have non : z ∉ r := fun h => hout (by simp [h])
    have lift (A : Finset W) (other : ∀ w ∈ r, holds A (R.P w)) (hz' : holds A (R.P z)) :
        ∀ w ∈ insert z r, holds A (R.P w) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|hm
      · exact hz'
      · exact other _ hm
    by_cases hc : constWord (R.P a) ∨ constWord (R.P b)
    · have ds : dead R (insert a (insert b r)) ≤ dead R (insert z r)+1 := by
        have h1 := dead_ins_le R (insert b r) a
        have h2 := dead_ins_le R r b
        have h3 := dead_ins_mono R r z
        by_cases hA : constWord (R.P a) <;> by_cases hB : constWord (R.P b)
        · have he := dead_ins_new (const_closed hz hA hB) non
          omega
        · rw [dead_ins_keep hB] at h1; omega
        · rw [dead_ins_keep hA]; omega
        · exact False.elim (hc.elim hA hB)
      obtain ⟨c,t,ht,le,run⟩ := ih tail (lift av holdr (projected_free hz hpa hpb hc))
      exact ⟨c,t,ht,by omega,run⟩
    · have hA : ¬constWord (R.P a) := fun h => hc (.inl h)
      have hB : ¬constWord (R.P b) := fun h => hc (.inr h)
      have ds : dead R (insert a (insert b r)) ≤ dead R (insert z r) := by
        rw [dead_ins_keep hA, dead_ins_keep hB]
        exact dead_ins_mono R r z
      rcases projected_reach hz hpa hpb with existing|⟨u,hu,v,hv,ne,w,hw,rep⟩
      · obtain ⟨c,t,ht,le,run⟩ := ih tail (lift av holdr existing)
        exact ⟨c,t,ht,by omega,run⟩
      · obtain ⟨c,t,ht,le,run⟩ := ih tail
          (lift (insert w av) (fun x hx => holds_insert (holdr x hx)) rep)
        exact ⟨c+1,t,ht,by omega,Or.inr ⟨u,hu,v,hv,ne,w,hw,run⟩⟩

abbrev Certificate := Restriction × ℕ × List W
abbrev Query := Certificate × ℕ

private def covers (n : ℕ) (q : Certificate) (ws : List W) : Bool :=
  decide (n ≤ q.2.1 + ws.countP (fun w => decide (constWord (q.1.P w)))) && ws.all fun w =>
    let v := q.1.P w
    (v == 0) || (v == ~~~0) || q.2.2.contains v || q.2.2.contains (~~~v)

private def impossible (q : Certificate) : Prop :=
  ∀ g, (g = goal ∨ g = ~~~goal) → ¬build basicOps g q.2.1 q.2.2.toFinset

private theorem excludes {g : W} (hg : g = goal ∨ g = ~~~goal) {ws : List W} {n : ℕ}
    {q : Certificate} (hc : covers n q ws = true) (nd : ws.Nodup) (no : impossible q)
    (hl : live basicOps g n ws.toFinset) : False := by
  simp only [covers, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨cap,mem⟩ := hc
  have holdsAll : ∀ w ∈ ws.toFinset, holds q.2.2.toFinset (q.1.P w) := by
    intro w hw
    have h := mem w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    rcases h with ((h|h)|h)|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨_,List.mem_toFinset.mpr h,.inl rfl⟩)
    · exact .inr (.inr ⟨_,List.mem_toFinset.mpr h,.inr BitVec.not_not.symm⟩)
  obtain ⟨c,t,ht,hle,run⟩ := projected_live q.1 hg hl holdsAll
  have dl : dead q.1 ws.toFinset = ws.countP (fun w => decide (constWord (q.1.P w))) := nd.card_eq_countP
  have hcap : c ≤ q.2.1 := by omega
  have lift {a b : ℕ} (hab : a ≤ b) (hr : build basicOps t a q.2.2.toFinset) :
      build basicOps t b q.2.2.toFinset := by
    induction hab with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no t ht (lift hcap run)

private def seeds (n : ℕ) (xs : List W) : List (List W) :=
  xs.sublists.filter fun ws => decide (ws.length ≤ n+1) && (cuts ws == -1)

private def choicesWithCuts (a b z : W) (r : List W) : List (List W × BitVec 2415) :=
  let base := sep z ||| cuts r
  [(r,base), (a::r,base ||| sep a), (b::r,base ||| sep b), (a::b::r,base ||| sep a ||| sep b)]

private theorem choice_with_cut {a b z : W} {r t : List W} (h : t ∈ keepChoices a b r) :
    (t,cuts (z::t)) ∈ choicesWithCuts a b z r := by
  simp [keepChoices] at h
  rcases h with rfl|rfl|rfl|rfl <;> simp only [choicesWithCuts,List.mem_cons,List.not_mem_nil,or_false]
  · exact .inl rfl
  · exact .inr (.inl (by simp only [cuts,List.foldr_cons]; congr 1; ac_rfl))
  · exact .inr (.inr (.inl (by simp only [cuts,List.foldr_cons]; congr 1; ac_rfl)))
  · exact .inr (.inr (.inr (by simp only [cuts,List.foldr_cons]; congr 1; ac_rfl)))

private def children (k : ℕ) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if ws.contains z then [] else
        ((choicesWithCuts a b z r).filter fun (kept,c) =>
          decide (kept.length ≤ k) && (c == -1)).map (fun s => z :: s.1)

-- One sixteen-bit entry accompanies each surviving successor.
private def everyCode {α : Type} (p : ℕ → α → Bool) : ℕ → List α → Bool
  | _, [] => true
  | code, x :: xs => p (code % 65536) x && everyCode p (code / 65536) xs

private theorem everyCode_mem {α : Type} {p : ℕ → α → Bool} {xs : List α} {code : ℕ}
    (h : everyCode p code xs = true) {x : α} (hx : x ∈ xs) : ∃ j, p j x = true := by
  induction xs generalizing code with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [everyCode,Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,h.1⟩
    · exact ih h.2 hm

private theorem firstChild {g : W} (hg : g = goal ∨ g = ~~~goal) {ws : List W} {k : ℕ}
    (hn : ws.Nodup) (h : live basicOps g (k+1) ws.toFinset) :
    ws = [g] ∨ ∃ t ∈ children k ws, t.Nodup ∧ live basicOps g k t.toFinset := by
  rcases first_live h with done|⟨a,ha,b,hb,ne,z,hz,hout,rest,hs,tail⟩
  · exact .inl (singleton_list hn done)
  · right
    obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) ne
    have go {a b : W} (m : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b rest)) (hop : z ∈ basicOps a b) :
        ∃ t ∈ children k ws, t.Nodup ∧ live basicOps g k t.toFinset := by
      obtain ⟨kept,hk,hnd,hfin⟩ := recover_kept perm hn hset
      have fresh : z ∉ ws := fun hm => hout (List.mem_toFinset.mpr hm)
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
      have nd' := List.nodup_cons.mpr ⟨hznew,hnd⟩
      have hl' : live basicOps g k (z::kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl'
      rw [List.toFinset_card_of_nodup nd',List.length_cons] at hc
      refine ⟨z::kept,?_,nd',hl'⟩
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),m,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simp only [List.contains_iff_mem,fresh,ite_false,List.mem_map]
      exact ⟨(kept,cuts (z::kept)),List.mem_filter.mpr ⟨choice_with_cut hk,by simp [cuts_full hg hl',show kept.length ≤ k by omega]⟩,rfl⟩
    rcases hm with hm|hm
    · exact go hm hp hs hz
    · exact go hm (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

private def checkLive (db : ℕ → Query) (count : ℕ) (trees : ℕ → ℕ) (cap : ℕ) :
    ℕ → ℕ → List W → Bool
  | 0, _, ws => ws != [goal] && ws != [~~~goal]
  | k+1, code, ws =>
    if code = 0 then !(optimized (k+1) (k+2-ws.length) ws)
    else if code ≤ count then
      let q := db (code-1)
      decide (q.1.2.1 < cap) && covers (k+1) q.1 ws
    else
      (ws != [goal] && ws != [~~~goal]) &&
        everyCode (checkLive db count trees cap k) (trees (code-count-1)) (children k ws)

private theorem checkLive_sound {db : ℕ → Query} {count : ℕ} {trees : ℕ → ℕ} {cap : ℕ}
    (lower : ∀ i < count, (db i).1.2.1 < cap → impossible (db i).1)
    {g : W} (hg : g = goal ∨ g = ~~~goal) {k code : ℕ} {ws : List W} (hn : ws.Nodup)
    (h : checkLive db count trees cap k code ws = true) (hl : live basicOps g k ws.toFinset) : False := by
  induction k generalizing code ws with
  | zero =>
    have eq := singleton_list hn hl
    rcases hg with rfl|rfl <;> simp [checkLive,eq] at h
  | succ k ih =>
    simp only [checkLive] at h
    split at h
    · have sz := live_card hl
      rw [List.toFinset_card_of_nodup hn] at sz
      have e := optimized_complete hg (k+1) ws (k+2-ws.length) hn (by omega) hl
      simp [e] at h
    · split at h
      · simp only [Bool.and_eq_true,decide_eq_true_eq] at h
        exact excludes hg h.2 hn (lower _ (by omega) h.1) hl
      · simp only [Bool.and_eq_true] at h
        obtain ⟨ng,steps⟩ := h
        rcases firstChild hg hn hl with eq|⟨t,mt,nt,lt⟩
        · rcases hg with rfl|rfl <;> simp [eq] at ng
        · obtain ⟨j,hj⟩ := everyCode_mem steps mt
          exact ih nt hj lt

private def checkQuery (db : ℕ → Query) (count : ℕ) (trees : ℕ → ℕ) (q : Query) : Bool :=
  decide q.1.2.2.Nodup && everyCode (checkLive db count trees q.1.2.1 q.1.2.1) q.2
    (seeds q.1.2.1 q.1.2.2)

private theorem query_sound {db : ℕ → Query} {count : ℕ} {trees : ℕ → ℕ} {q : Query}
    (lower : ∀ i < count, (db i).1.2.1 < q.1.2.1 → impossible (db i).1)
    (checked : checkQuery db count trees q = true) : impossible q.1 := by
  classical
  intro g hg run
  simp only [checkQuery,Bool.and_eq_true] at checked
  obtain ⟨nd,ok⟩ := checked
  have nd' := of_decide_eq_true nd
  obtain ⟨s,hs,hl⟩ := compress run
  let ws := q.1.2.2.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hl' : live basicOps g q.1.2.1 ws.toFinset := eq.symm ▸ hl
  have nw : ws.Nodup := nd'.filter (· ∈ s)
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup nw] at sz
  have mem : ws ∈ seeds q.1.2.1 q.1.2.2 := List.mem_filter.mpr
    ⟨List.mem_sublists.mpr (List.filter_sublist ..),by simp [sz,cuts_full hg hl']⟩
  obtain ⟨j,hj⟩ := everyCode_mem ok mem
  exact checkLive_sound lower hg nw hj hl'

private theorem bank_sound {db : ℕ → Query} {count : ℕ} {trees : ℕ → ℕ}
    (ok : ∀ i < count, checkQuery db count trees (db i) = true) :
    ∀ i < count, impossible (db i).1 := by
  intro i hi
  generalize he : (db i).1.2.1 = n
  induction n using Nat.strong_induction_on generalizing i with
  | ind n ih =>
    exact query_sound (fun j hj lt => ih _ (he ▸ lt) j hj rfl) (ok i hi)

private def x0 : W := rows[0]!
private def x1 : W := rows[1]!
private def x2 : W := rows[2]!
private def x3 : W := rows[3]!
private def x4 : W := rows[4]!
private def x5 : W := rows[5]!
private def x6 : W := rows[6]!
private def R0 : Restriction := restrict 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 0 (by decide +kernel)
private def R4 : Restriction := restrict 0x3e9987fd330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661e00000000000000000000001f4cc3fe9987fd330f00000000000000000000000fa661ff4cc3fe9987fd330f00000000000000000000000fa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661e00000000000000000fa661ff4cc3fe9987800000000001f4cc3fe9987800000000001f4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3fe9987800000000000000000000007d330ffa661ff4cc3c00000000000000000000003e9987fd330ffa661e00000000000000000000001f4cc3fe9987fd330ffa661e00000000000000000000001f4cc3fe9987fd330f00000000000000000000000fa661ff4cc3fe9987fd330f00000000000000000000000fa661ff4cc3c00000000000000001f4cc3fe9987fd330f000000000003e9987fd330f000000000003e9987fd330f 0 (by decide +kernel)
private def R5 : Restriction := restrict 0x7d1305000001f44c1400000000000000000000000000007d1305000001f44c1400000000000000000000000000007d1305000001f44c1400000000000000000000000000007d1305000001f44c1400000000000000000000000000007d1305000001f44c1400000000000000000000000000007d1305000001f44c1400000000000000000000000000007d130500000000000000000000000000000000003e898280000000000000000000000000000000001f44c14000007d130500000000000000000000000000001f44c140000000000000000000000000000000000fa260a000003e89828000000000000000000000000000000000000000000000000000000001f44c1400000000000000000000003e89828000000000000000000000000000000000000000000000000000fa260a000003e898280000000000000000000000000000fa260a000003e898280000000000000000000000000000fa260a000003e898280000000000000000000000000000fa260a000003e898280000000000000000000000000000fa260a000003e898280000000000000000000000000000fa260a000003e898280000000000000000000000000000fa260a00000000000000000000000000000000007d130500000000000000000000000000000000003e8982800000fa260a00000000000000000000000000003e898280000000000000000000000000000000001f44c14000007d13050000000000000000000000000000000000000000000000000000000003e8982800000000000000000000007d130500000000000000000000000 92 (by decide +kernel)
private def R6 : Restriction := restrict 0xea6207d4c40c0000000000000000000000000000000000ea6207d4c40c0000000000000000000000000000000000ea6207d4c40c0000000000000000000000000000000000ea6207d4c40c0000000000000000000000000000000000ea6207d4c40c0000000000000000000000000000000000ea6207d4c40c0000000000000000000000000000000000ea6206000000000000000000000000000000000075310300000000000000000000000000000000003a9881f5310300000000000000000000000000000000003a988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000ea620600000000000000000000000000003a988180000000000000000000000000000000000000003a988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000000001d4c40fa988180000000000000000000000000000000001d4c40c0000000000000000000000000000000000ea62060000000000000000000000000000000000753103ea6206000000000000000000000000000000000075310300000000000000000000000000000000003a9881f5310300000000000000000000000000001d4c40c00000000000000000000000000007531030000000000000000000000000000000000000000753103 0 (by decide +kernel)
private def R7 : Restriction := restrict 0x1d444040000000000000000000000000000000000000001d444040000000000000000000000000000000000000001d444040000000000000000000000000000000000000001d444040000000000000000000000000000000000000001d444040000000000000000000000000000000000000001d44404000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000751101000000000000000000000000000000000000000000000000000000000000000000000000000000003a8880800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003a888080000000000000000000000000000000000000003a888080000000000000000000000000000000000000003a888080000000000000000000000000000000000000003a888080000000000000000000000000000000000000003a888080000000000000000000000000000000000000003a88808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ea2202000000000000000000000000000000000000000000000000000000000000000000000000000000007511010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R12 : Restriction := restrict 0x1e1807bc300f78601ef0c03c000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601ef0c03c000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601ef0c03c000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03de18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601e0000000000000000000000000000000000000000000000f0c03de1807800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c300f78601ef0c03de18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601ef0c03de18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601ef0c03de18078000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601e000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c0000000000000000000000000000000000000000000001e1807bc300f00000000000000000000000 92 (by decide +kernel)
private def R13 : Restriction := restrict 0x3c1005000000f04014000000000000000000000000000000000000000000000000000000000000000000000000003c1005000000f04014000000000000000000000000000000000000000000000000000000000000000000000000003c1005000000f04014000000000000000000000000000000000000000000000000000000000000000000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000f04014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e08028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000078200a000001e080280000000000000000000000000000000000000000000000000000000000000000000000000078200a000001e080280000000000000000000000000000000000000000000000000000000000000000000000000078200a000001e08028000000000000000000000000000000000000000000000000000000000000000000003c1005000000000000000000000000000000000000000000000000000000000000000000000000000000001e08028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c100500000000000000000000000 92 (by decide +kernel)
private def R14 : Restriction := restrict 0x686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000343003000000000000000000000000000000000000000000000000000000000000000000000000000000001a180180000000000000000000000000000000000000000000000000000000000000000000000000068600600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da1801800000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da1801800000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da180180000000000000000000000000000000000000000000000000000000000000000000000000068600600000000000000000000000000000000000000000000000000000000000000000000000000000000343003000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R20 : Restriction := restrict 0x360187ec030fd8061fb00c3c0000000000000000000000360187ec030fd8061fb00c3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000360187ec030fd8061e00000000000000000000001b00c3f60187ec030f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3f60187800000000000000000000006c030fd8061e000000000000000000000000000000000000000000000000000000000000000000001b00c3f6018780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3f60187800000000000000000000006c030fd8061fb00c3f6018780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3c0000000000000000000000360187ec030fd8061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3f60187ec030f00000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000360187ec030f 0 (by decide +kernel)
private def R21 : Restriction := restrict 0x6c0305000001b00c1400000000000000000000000000006c0305000001b00c140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030500000000000000000000000000000000003601828000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8060a0000036018280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8060a0000036018280000000000000000000000000000d8060a000003601828000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8060a00000000000000000000000000000000006c03050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00c14000006c03050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R22 : Restriction := restrict 0xc8020790040c0000000000000000000000000000000000c8020790040c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c802060000000000000000000000000000000000640103000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000190040f2008180000000000000000000000000000c8020600000000000000000000000000000000000000000000000000000000000000000000000000320081800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000190040f200818000000000000000000000000000000000190040f20081800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000190040c0000000000000000000000000000000000c80206000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000320081e401030000000000000000000000000000190040c00000000000000000000000000000000000000000000000000000000000000000000000000640103 0 (by decide +kernel)
private def R28 : Restriction := restrict 0x160007ac000f58001eb0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0003d60007ac000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001eb0003d6000780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160007ac000f58001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001eb0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R29 : Restriction := restrict 0x2c0005000000b00014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000016000280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058000a00000160002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c00050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 1012 (by decide +kernel)
private def R30 : Restriction := restrict 0x48000690000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000480006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000d20001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R36 : Restriction := restrict 0x309987e1330fc2661f84cc3c0000000000000000000000309987e1330fc2661f84cc3c0000000000000000000000309987e1330fc2661e0000000000000000000000184cc3f09987e1330f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2661f84cc3f0998780000000000184cc3f0998780000000000184cc3f0998780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000061330fc2661f84cc3f099878000000000000000000000061330fc2661f84cc3f099878000000000000000000000061330fc2661f84cc3c0000000000000000000000309987e1330fc2661e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184cc3f09987e1330f00000000000309987e1330f00000000000309987e1330f 0 (by decide +kernel)
private def R38 : Restriction := restrict 0xc2620784c40c0000000000000000000000000000000000c2620784c40c0000000000000000000000000000000000c262060000000000000000000000000000000000613103000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000309881800000000000000000000000000000000000000030988180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184c40f098818000000000000000000000000000000000184c40f098818000000000000000000000000000000000184c40c0000000000000000000000000000000000c262060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006131030000000000000000000000000000000000000000613103 0 (by decide +kernel)
private def R44 : Restriction := restrict 0x101807a0300f40601e80c03c00000000000000000000000000000000000000000000000000000000000000080c03d01807a0300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300f40601e80c03d01807800000000000000000000000000000000000000000000000000000000000000101807a0300f40601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R45 : Restriction := restrict 0x201005000000804014000000000000000000000000000000000000000000000000000000000000000000001008028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040200a000001008028000000000000000000000000000000000000000000000000000000000000000000002010050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100500000000000000000000000 92 (by decide +kernel)
private def R52 : Restriction := restrict 0x300187e0030fc0061e00000000000000000000001800c3f00187e0030f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001800c3f001878000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060030fc0061f800c3c0000000000000000000000300187e0030fc0061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300187e0030f 0 (by decide +kernel)
private def R84 : Restriction := restrict 0xc030f18061e300c3c60187800000000000000000000000c030f18061e000000000000000000000000000000000000000000000000000000000000000000000300c3c60187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018061e300c3c601878c030f0000000000000000000000018061e300c3c000000000000000000000000000000000000000000000000000000000000000000000601878c030f 0 (by decide +kernel)
private def R86 : Restriction := restrict 0x10040c2008180000000000000000000000000000080206000000000000000000000000000000000000000000000000000000000000000000000000000200818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200818401030000000000000000000000000000010040c00000000000000000000000000000000000000000000000000000000000000000000000000040103 0 (by decide +kernel)
private def R205 : Restriction := restrict 0x4010608020c000000000000000000000000000000000004010608020c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004010608020c0000000000000000000000000000020083040106000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c100418000000000000000000000000000000000008020c00000000000000000000000000000000000000000000000000000000000000000000000000020083000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c100418000000000000000000000000000000000008020c10041800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c100418000000000000000000000000000004010608020c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100418200830000000000000000000000000000000000010041800000000000000000000000000000000000000000000000000000000000000000000000000040106000000 25 (by decide +kernel)
private def R208 : Restriction := restrict 0x22600044c000000000000000000000000000000000000022600044c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022600044c000000000000000000000000000000000000022600044c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000898001130000000000000000000000000000000000000089800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008980000000000000000000000000000000000000000000000000000000000000000000000000000000000044c000898000000000000000000000000000000000000044c00089800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c000898000000000000000000000000000000000000044c000898000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000113000226000000000000000000000000000000000000011300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001130000000000000000000000000000000000000000000000000 196 (by decide +kernel)
private def R343 : Restriction := restrict 0x410300000001040c000000000000000000000000000000000000000000000000000000000000000000000000000041030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001040c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008206000000020818000000000000000000000000000000000000000000000000000000000000000000000000000082060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002081800000000000000000000000000000000000000000000000000000 215 (by decide +kernel)
private def R619 : Restriction := restrict 0x8020c100418000000000000000000000000000000000008020c000000000000000000000000000000000000000000000000000000000000000000000000000200830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100418200830000000000000000000000000000000000010041800000000000000000000000000000000000000000000000000000000000000000000000000040106000000 25 (by decide +kernel)
private def R622 : Restriction := restrict 0x898001130000000000000000000000000000000000000089800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000113000226000000000000000000000000000000000000011300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001130000000000000000000000000000000000000000000000000 196 (by decide +kernel)
private def R1014 : Restriction := restrict 0x40601e80c03c0000000000000000000000000000000000000000000000000000000000000000000000000020300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000040601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R1020 : Restriction := restrict 0xc2600184c0000000000000000000000000000000000000c2600184c0000000000000000000000000000000000000c260000000000000000000000000000000000000613000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000309800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184c003098000000000000000000000000000000000000184c003098000000000000000000000000000000000000184c0000000000000000000000000000000000000c260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006130000000000000000000000000000000000000000000000000 196 (by decide +kernel)
private def R1033 : Restriction := restrict 0x262160000000988580000000000004c42c0000000000000000004c42c09885800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004c42c0000001310b000000000000098858000000000000000000988581310b 0 (by decide +kernel)
private def R1035 : Restriction := restrict 0x10180580000040601680c02c00000000000000000000000000000000000000000000000000000000000000080c02c0000020300b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c02c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300b00000080c02d018058000000000000000000000000000000000000000000000000000000000000001018058000004060160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010180580000000000000000000000000000 115 (by decide +kernel)
private def R1037 : Restriction := restrict 0x10100520200a4040148080280000000000000000000000000000000000000000000000000000000000000008080290100520200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200a4040148080290100500000000000000000000000000000000000000000000000000000000000000010100520200a4040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100500000000000000000000000000000 116 (by decide +kernel)
private def R1038 : Restriction := restrict 0x30010660020cc00418000000000000000000000018008330010660020c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001800830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060020cc00419800830000000000000000000000030010660020cc004180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300106000000 25 (by decide +kernel)
private def R1039 : Restriction := restrict 0x441c00883801107000000000000008838011070000000000000088380110700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088380110700220e0000000000000110700220e0000000000000110700220e 1 (by decide +kernel)
private def R1045 : Restriction := restrict 0x461e00000001187800000000000008c3c00000000000000000008c3c011878000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008c3c0000000230f000000000000011878000000000000000000118780230f 0 (by decide +kernel)
private def R1047 : Restriction := restrict 0x2601404c0280980500000000000004c0280980500000000000004c02809805000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004c0280980501300a0000000000000980501300a0000000000000980501300a 1 (by decide +kernel)
private def R1058 : Restriction := restrict 0x40601e80c03c00000000000000000000000000000000000000000000000000000000000000080c03d01807a0300f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d01807800000000000000000000000000000000000000000000000000000000000000101807a0300f40601e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 989 (by decide +kernel)
private def R1064 : Restriction := restrict 0x80c03d01807a0300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f40601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R1065 : Restriction := restrict 0x10100780000040401e00000000000000000000000000000000000000000000000000000000000000000000080803d01007a0200f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080803c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200f00000080803c00000000000000000000000000000000000000000000000000000000000000000000101007a0200f40401e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100780000000000000000000000000000 115 (by decide +kernel)
private def R1109 : Restriction := restrict 0x301187800000c0461e000000000000000000000000000000000060230f00000000000000000000000000001808c3f01187e0230f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001808c3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060230f000001808c3c0000000000000000000000000000000000c0461e0000000000000000000000000000301187e0230fc0461e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030118780000000000000000000000000000 115 (by decide +kernel)
private def R1116 : Restriction := restrict 0x20018540030a80061400000000000000000000001000c280000040030a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000c2a001850000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040030a800615000c280000000000000000000000200185000000800614000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020018540030a 1 (by decide +kernel)
private def R1118 : Restriction := restrict 0x18461e000000611878000000000000000000000000000018461e00000061187800000000000000000000000c230f18461e308c3c61187800000000000000000000000c230f18461e0000000000000000018461e00000061187800000000000308c3c00000000000000000308c3c6118780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000308c3c000000c230f00000000000000000000000000000308c3c000000c230f0000000000000000000000018461e308c3c611878c230f0000000000000000000000018461e308c3c00000000000000000308c3c000000c230f00000000000061187800000000000000000611878c230f 0 (by decide +kernel)
private def R1131 : Restriction := restrict 0x2108180000000000000000000000000000000000000000210818000000000000000000000000000000000010840c2108180000000000000000000000000000084206000000000000000000000000000002108180000000000000000000000000000000000000000210818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042103000000000000000000000000000000000000000004210300000000000000000000000000000000000210818421030000000000000000000000000000010840c00000000000000000000000000000421030000000000000000000000000000000000000000042103 0 (by decide +kernel)
private def R1132 : Restriction := restrict 0x1004180000000000000000000000000000000000000000100418000000000000000000000000000000000008020c100418000000000000000000000000000000000008020c000000000000000000000001004180000000000000000000000020083000000000000000000200830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020083000000000000000000000000000000000000000002008300000000000000000000000000000000000100418200830000000000000000000000000000000000010041800000000000000000000000200830000000000000000000000004010600000000000000000040106000000 25 (by decide +kernel)
private def R1147 : Restriction := restrict 0x10061e000000000000000000000000000000000000000010061e000000000000000000000000000000000008030f10061e000000000000000000000000000000000008030f0000000000000000000000010061e00000000000000000000000200c3c00000000000000000200c3c4018780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200c3c0000000000000000000000000000000000000000200c3c000000000000000000000000000000000010061e200c3c000000000000000000000000000000000010061e00000000000000000000000200c3c00000000000000000000000401878000000000000000004018788030f 0 (by decide +kernel)
private def R1153 : Restriction := restrict 0x21187800000000000000000000000000000000000000002118780000000000000000000000000000000000108c3c211878000000000000000000000000000008461e000000000000000000000000000002118780000000000000000000000000000000000108c3c21187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004230f000000000000000000000000000000000000000004230f000000000000000000000000000000000002118784230f00000000000000000000000000000108c3c000000000000000000000000000004230f000000000000000000000000000000000002118784230f 0 (by decide +kernel)
private def R1160 : Restriction := restrict 0x1006180000004018600000000000000000000000000000100618000000000000000000000000000000000008030c100618200c30401860000000000000000000000008030c0000000000000000000000010061800000040186000000000000200c3000000000000000000200c304018600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200c300000008030c00000000000000000000000000000200c300000000000000000000000000000000000100618200c304018608030c0000000000000000000000010061800000000000000000000000200c300000008030c000000000000401860000000000000000004018608030c 2 (by decide +kernel)
private def R1167 : Restriction := restrict 0x8460600000021181800000000000000000000000000000000000000002118180000000000000000000000042303084606108c0c2118180000000000000000000000000000084606000000000000000000846060000002118180000000000000000000000000000000000108c0c2118180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000108c0c00000042303000000000000000000000000000000000000000004230300000000000000000000000084606108c0c2118184230300000000000000000000000000000108c0c00000000000000000108c0c000000423030000000000000000000000000000000000021181842303 0 (by decide +kernel)
private def R1170 : Restriction := restrict 0x210808000000000000000000000000000000000000000021080800000000000000000000000000000000001084042108080000000000000000000000000000084202000000000000000000000000000002108080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042101000000000000000000000000000000000000000004210100000000000000000000000000000000000210808421010000000000000000000000000000010840400000000000000000000000000000421010000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R1177 : Restriction := restrict 0x18061a000000000000000000000000000000000000000018061a00000000000000000000000000000000000c030d18061a00000060186800000000000000000000000c030d0000000000000000000000018061a00000000000000000000000300c3400000000000000000300c340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300c340000000000000000000000000000000000000000300c34000000000000000000000000000000000018061a300c34000000c030d0000000000000000000000018061a00000000000000000000000300c34000000000000000000000006018680000000000000000060186800000 23 (by decide +kernel)
private def R1184 : Restriction := restrict 0x6118380000000000000000000000000000000000000000611838000000000000000000000000000018460e308c1c611838000000000000000000000000000018460e0000000000000000000000000000061183800000000000000000000000000000000000000006118380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c230700000000000000000000000000000000000000000c230700000000000000000000000000000308c1c611838c230700000000000000000000000000000308c1c00000000000000000000000000000c230700000000000000000000000000000000000000000c2307 0 (by decide +kernel)
private def R1203 : Restriction := restrict 0x1004180000000000000000000000000000000000000000000000000000000000000001004180000000000000000000000020083000000000000000000200830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200830000000000000000000000000000000000000000000000000000000000000000200830000000000000000000000004010600000000000000000040106000000 25 (by decide +kernel)
private def R1204 : Restriction := restrict 0x180418000000601060000000000000000000000000000018041800000060106000000000000000000000000c020c18041830083060106000000000000000000000000c020c1804180000000000000000018041800000000000000000000000300830000000000000000003008300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300830000000c020c00000000000000000000000000000300830000000c020c00000000000000000000000180418300830601060c020c0000000000000000000000018041830083000000000000000000300830000000000000000000000006010600000000000000000060106000000 25 (by decide +kernel)
private def R1206 : Restriction := restrict 0x210800000000000000000000000000000000000000000021080000000000000000000000000000000000001084002108000000000000000000000000000000084200000000000000000000000000000002108000000000000000000000000000000000000000000210800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042100000000000000000000000000000000000000000004210000000000000000000000000000000000000210800421000000000000000000000000000000010840000000000000000000000000000000421000000000000000000000000000000000000000000042100 8 (by decide +kernel)
private def R1214 : Restriction := restrict 0x184206000000610818000000000000000000000000000018420600000061081800000000000000000000000c210318420630840c61081800000000000000000000000c2103184206000000000000000000000000000006108180000000000000000000000000000000000000000610818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030840c000000c21030000000000000000000000000000030840c000000c21030000000000000000000000018420630840c610818c21030000000000000000000000018420630840c00000000000000000000000000000c210300000000000000000000000000000000000000000c2103 0 (by decide +kernel)
private def R1215 : Restriction := restrict 0x38600070c000e18000000000000000000000000000000000000000000000000000000000000000000000001c3000386000000000000000000000000000000000000000000000000070c000e18000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000070c000e18001c300000000000000000000000000000000000000000000000000000000000000000000000038600070c0000000000000000000000000000000000000000000000000e18001c300000000000000000000000000 104 (by decide +kernel)
private def R1216 : Restriction := restrict 0x100107a0020f0000000000000000000000000000080083d00107a0020f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080083c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020020f40041e0000000000000000000000000000100107a0020f40041e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100107800000 23 (by decide +kernel)
private def R1220 : Restriction := restrict 0xe26001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e260000000000000000000000000000000000000713000000000000000000000000000000000000038980071300000000000000000000000000000000000003898000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000389800000000000000000000000000000000000000000000000000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0000000000000000000000000000000000000e260000000000000000000000000000000000000713000e26000000000000000000000000000000000000071300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007130000000000000000000000000000000000000000000000000 196 (by decide +kernel)
private def R1230 : Restriction := restrict 0x606000c0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000606000c0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000606000c0c000000000000000000000000000000000000000000000000000000000000000000000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000018180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c00181800000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c00181800000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c001818000000000000000000000000000000000000000000000000000000000000000000000000000006060000000000000000000000000000000000000000000000000000000000000000000000000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R1231 : Restriction := restrict 0x1c440000000000000000000000000000000000000000001c440000000000000000000000000000000000000000001c440000000000000000000000000000000000000000001c440000000000000000000000000000000000000000001c440000000000000000000000000000000000000000001c440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000388800000000000000000000000000000000000000000038880000000000000000000000000000000000000000003888000000000000000000000000000000000000000000388800000000000000000000000000000000000000000038880000000000000000000000000000000000000000003888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e22000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 817 (by decide +kernel)
private def R1251 : Restriction := restrict 0x82400104800000000000000000000000000000000000008240000000000000000000000000000000000000000000824000000000000000000000000000000000000041200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010480020900000000000000000000000000000000000001048000000000000000000000000000000000000000000104800000000000000000000000000000000000008240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004120000000000000000000000000000000000000000000000000 197 (by decide +kernel)
private def R1269 : Restriction := restrict 0xe26001c4c00000000000000000000000000000000000000000000000000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000000001c4c0000000000000000000000000000000000000e26001c4c000000000000000000000000000000000000000000000000000000000000000000000000000007130000000000000000000000000000000000000000000000000000000000000000000000000000000000038980000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c4c00389800000000000000000000000000000000000000000000000000000000000000000000000000000000001c4c00389800000000000000000000000000000000000000000038980000000000000000000000000000000000001c4c00389800000000000000000000000000000000000000000000000000000000000000000000000000000e260000000000000000000000000000000000000000000000000000000000000000000000000000000000071300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R1270 : Restriction := restrict 0x604000c0800000000000000000000000000000000000000000000000000000000000000000000000000000000000604000c0800000000000000000000000000000000000000000000000000000000000000000000000000000000000604000000000000000000000000000000000000000000000000000000000000000000000000000000000003020000000000000000000000000000000000000000000000000000000000000000000000000000000000018100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0800181000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0800181000000000000000000000000000000000000000000000000000000000000000000000000000000000000c08000000000000000000000000000000000000000000000000000000000000000000000000000000000006040000000000000000000000000000000000000000000000000000000000000000000000000000000000030200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 657 (by decide +kernel)
private def R1277 : Restriction := restrict 0x1c4c0000000000000000000000000000000000000000001c4c0000000000000000000000000000000000000000001c4c0000000000000000000000000000000000000000001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e26001c4c0000000000000000000000000000000000000e2600000000000000000000000000000000000007130000000000000000000000000000000000000000000713000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003898000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038980000000000000000000000000000000000000000003898000000000000000000000000000000000000000000389800000000000000000000000000000000000000000038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0038980000000000000000000000000000000000001c4c0000000000000000000000000000000000000e260000000000000000000000000000000000000000000e26000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007130000000000000000000000000000000000000000000000000 196 (by decide +kernel)
private def R1291 : Restriction := restrict 0x1440000000000000000000000000000000000000000000144000000000000000000000000000000000000000000014400000000000000000000000000000000000000000001440000000000000000000000000000000000000000000144000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000288000000000000000000000000000000000000000000028800000000000000000000000000000000000000000002880000000000000000000000000000000000000000000288000000000000000000000000000000000000000000028800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 821 (by decide +kernel)
private def R1311 : Restriction := restrict 0x406000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040600080c00000000000000000000000000000000000000000000000000000000000000000000000000000203000000000000000000000000000000000000000000000000000000000000000000000000000000000001018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c001018000000000000000000000000000000000000000000000000000000000000000000000000000004060000000000000000000000000000000000000000000000000000000000000000000000000000000000020300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R1323 : Restriction := restrict 0x602000c0400000000000000000000000000000000000000000000000000000000000000000000000000000000000602000c0400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c04000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0400180800000000000000000000000000000000000000000000000000000000000000000000000000000000000c0400180800000000000000000000000000000000000000000000000000000000000000000000000000000000000000001808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R1363 : Restriction := restrict 0x3c0000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000f00000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e00000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R1364 : Restriction := restrict 0x100802a0100540200a80401400000000000000000000000000000000000000000000000000000000000000080401500802a010050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100540200a80401500802800000000000000000000000000000000000000000000000000000000000000100802a0100540200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100500000000000000000000000 92 (by decide +kernel)
private def R1371 : Restriction := restrict 0x20601440c0288180500000000000000000000000000000000000000000000000000000000000000000000010300a206014000000000000000000000000000000000000000000000040c028818050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040c0288180510300a00000000000000000000000000000000000000000000000000000000000000000000020601440c02800000000000000000000000000000000000000000000008180510300a00000000000000000000000 93 (by decide +kernel)
private def R1406 : Restriction := restrict 0x2c000f000000b0003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001e00000160007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001eb0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R1407 : Restriction := restrict 0x10180520300a40601480c02800000000000000000000000000000000000000000000000000000000000000080c0290180520300a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c0290180500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300a40601480c0290180500000000000000000000000000000000000000000000000000000000000000010180520300a4060140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010180520300a00000000000000000000000 93 (by decide +kernel)
private def R1410 : Restriction := restrict 0x10401c2080384100700000000000000000000000000000000000000000000000000000000000000000000008200e10401c000000000000000000000000000000000000000000000020803841007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002080384100708200e00000000000000000000000000000000000000000000000000000000000000000000010401c20803800000000000000000000000000000000000000000000004100708200e00000000000000000000000 93 (by decide +kernel)
private def R1434 : Restriction := restrict 0x14000628000c500018a0003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000314000628000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c500018a00031400060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014000628000c5000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R1442 : Restriction := restrict 0x380018700030e00060000000000000000000000000000000000000000000000000000000000000000000001c000c3800180000000000000000000000000000000000000000000000700030e000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700030e00061c000c0000000000000000000000000000000000000000000000000000000000000000000003800187000300000000000000000000000000000000000000000000000e00061c000c00000000000000000000000 94 (by decide +kernel)
private def R1459 : Restriction := restrict 0x1600062c000c580018b0003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b00031600062c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000c58001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000c580018b0003160006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001600062c000c58001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000580018b0003000000000000000000000000000000000000000000000000000000000000000000000000000000000 324 (by decide +kernel)
private def R1497 : Restriction := restrict 0x10100720200e40401c8080380000000000000000000000000000000000000000000000000000000000000008080390100720200e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008080390100700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200e40401c8080390100700000000000000000000000000000000000000000000000000000000000000010100720200e40401c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100720200e00000000000000000000000 93 (by decide +kernel)
private def R1503 : Restriction := restrict 0xd0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180180000000000000000000000000000000000000000000000000000000000000000000000000068600600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a1801800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a1801800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000343003000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R1550 : Restriction := restrict 0x686000d0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000686000d0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000686000d0c00000000000000000000000000000000000000000000000000000000000000000000000000000343000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180000000000000000000000000000000000000000000000000000000000000000000000000000068600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c001a1800000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c001a1800000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c001a180000000000000000000000000000000000000000000000000000000000000000000000000000068600000000000000000000000000000000000000000000000000000000000000000000000000000000000343000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000 334 (by decide +kernel)
private def R1568 : Restriction := restrict 0x10000520000a400014800028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000290000520000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000a400014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000a400014800029000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000520000a4000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040001480002800000000000000000000000000000000000000000000000000000000000000000000000000000000 323 (by decide +kernel)
private def R1582 : Restriction := restrict 0x4c0300000001300c0000000000000000000000000000004c0300000001300c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004c0300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009806000000026018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000980600000002601800000000000000000000000000000098060000000260180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000098060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001300c00000004c03000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 468 (by decide +kernel)
private def R1595 : Restriction := restrict 0x1e1807bc300f78601ef0c03c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03de18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601e0000000000000000000000000000000000000000000000f0c03de180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c300f78601ef0c03de1807800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601e000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c0000000000000000000000000000000000000000000001e1807bc300f00000000000000000000000 92 (by decide +kernel)
private def R1608 : Restriction := restrict 0x3c1005000000f0401400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000f04014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000078200a000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c1005000000000000000000000000000000000000000000000000000000000000000000000000000000001e08028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c100500000000000000000000000 92 (by decide +kernel)
private def R1622 : Restriction := restrict 0x3c0000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R1631 : Restriction := restrict 0x8080290100520200a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000808028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100520200a4040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100500000000000000000000000000000 116 (by decide +kernel)
private def R1652 : Restriction := restrict 0x3c300f000000f0c03c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f000000000000000000000000000000000000000000000000000000000000000000000000000f0c03c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000078601e000001e1807800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601e000000000000000000000000000000000000000000000000000000000000000000000000001e18078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f00000000000000000000000 92 (by decide +kernel)
private def R1672 : Restriction := restrict 0x606000c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000303000000000000000000000000000000000000000000000000000000000000000000000000000000000001818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c00181800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006060000000000000000000000000000000000000000000000000000000000000000000000000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R1699 : Restriction := restrict 0x7c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c000000000000000000000000000000000000003e000000000000000000000000000000000000001f00000000007c000000000000000000000000000000001f000000000000000000000000000000000000000f80000000003e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f8000000000000000000000000000000000000007c000000000000000000000000000000000000003e0000000000f8000000000000000000000000000000003e000000000000000000000000000000000000001f00000000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 478 (by decide +kernel)
private def R1735 : Restriction := restrict 0x30100560200ac04015808028000000000000000000000030100560200ac04015808028000000000000000000000030100560200ac040140000000000000000000000180802b0100560200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c04014000003010050000000000018080280000000000000000180802b0100500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060200ac0401580802b010050000000000000000000000060200ac0401580802b010050000000000000000000000060200ac04015808028000000000000000000000030100560200ac0401400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018080280000060200a000000000003010050000000000000000030100560200a 1 (by decide +kernel)
private def R1787 : Restriction := restrict 0xc0601f80c03c0000000000000000000000000000000000c0601f80c03c0000000000000000000000000000000000c0601e000000000000000000000000000000000060300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180c03f018078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180c03f018078000000000000000000000000000000000180c03f018078000000000000000000000000000000000180c03c0000000000000000000000000000000000c0601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000301807e0300f00000000000000000000000 92 (by decide +kernel)
private def R1826 : Restriction := restrict 0x30100560200ac04015808028000000000000000000000030100560200ac04015808028000000000000000000000030100560200ac040140000000000000000000000180802b0100560200a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001808028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060200ac0401580802b010050000000000000000000000060200ac0401580802b010050000000000000000000000060200ac04015808028000000000000000000000030100560200ac040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030100500000000000000000000000000000 116 (by decide +kernel)
private def R1836 : Restriction := restrict 0x5d0300000001740c0000000000000000000000000000005d0300000001740c0000000000000000000000000000005d0300000001740c0000000000000000000000000000005d0300000001740c0000000000000000000000000000005d0300000001740c00000000000000000000000000000000000000000000000000000000000000000000000000005d0300000000000000000000000000000000000000000000000000000000000000000000000000001740c00000005d030000000000000000000000000000001740c000000000000000000000000000000000000ba0600000002e81800000000000000000000000000000000000000000000000000000000001740c0000000000000000000000000000000000000000000000000000000000000000000000000000000000ba0600000002e818000000000000000000000000000000ba0600000002e818000000000000000000000000000000ba0600000002e818000000000000000000000000000000ba0600000002e818000000000000000000000000000000ba0600000002e8180000000000000000000000000000000000000000000000000000000000000000000000000000ba0600000000000000000000000000000000000000000000000000000000000000000000000000002e8180000000ba060000000000000000000000000000002e818000000000000000000000000000000000001740c00000005d03000000000000000000000000000000000000000000000000000000000002e81800000000000000000000000000000000000000000000000000000 215 (by decide +kernel)
private def R1846 : Restriction := restrict 0x154040000000000000000000000000000000000000000015404000000000000000000000000000000000000000001540400000000000000000000000000000000000000000154040000000000000000000000000000000000000000015404000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000550100000000000000000000000000000000000000000000000000000000000000000000000000000000002a8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002a808000000000000000000000000000000000000000002a808000000000000000000000000000000000000000002a808000000000000000000000000000000000000000002a808000000000000000000000000000000000000000002a808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa0200000000000000000000000000000000000000000000000000000000000000000000000000000000005501000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 468 (by decide +kernel)
private def R1873 : Restriction := restrict 0x1740c000000000000000000000000000000000000000001740c0000000000000000000000000000005d0300000001740c0000000000000000000000000000005d0300000001740c000000000000000000000000000000000000000001740c00000000000000000000000000000000000000000000000000000000000000000000000000005d0300000000000000000000000000000000000000000000000000000000000000000000000000000000000000005d0300000000000000000000000000000000000000000000000000000000000000000000000ba0600000002e8180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002e818000000000000000000000000000000000000000002e818000000000000000000000000000000ba0600000002e818000000000000000000000000000000ba0600000002e818000000000000000000000000000000000000000002e8180000000000000000000000000000000000000000000000000000000000000000000000000000ba060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ba0600000000000000000000000000000000000000000000000000000000000000000000001740c00000005d03000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 468 (by decide +kernel)
private def R1886 : Restriction := restrict 0x4802000000012008000000000000000000000000000000480200000001200800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000480200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900400000002401000000000000000000000000000000090040000000240100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001200800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 515 (by decide +kernel)
private def R1934 : Restriction := restrict 0x5c000000000170000000000000000000000000000000005c000000000170000000000000000000000000000000005c000000000170000000000000000000000000000000005c000000000170000000000000000000000000000000005c0000000001700000000000000000000000000000000000000000000000000000000000000000000000000000005c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b80000000002e000000000000000000000000000000000b80000000002e000000000000000000000000000000000b80000000002e000000000000000000000000000000000b80000000002e000000000000000000000000000000000b80000000002e0000000000000000000000000000000000000000000000000000000000000000000000000000000b800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R1939 : Restriction := restrict 0x309981e13303c2660784cc0c0000000000000000000000000000000000c2660784cc0c0000000000000000000000309981e13303c2660600000000000000000000000000000000006133030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2660784cc0f099818000000000000000000000000000000000184cc0f09981800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000613303c2660784cc0f099818000000000000000000000000000000000184cc0f0998180000000000000000000000613303c2660784cc0c0000000000000000000000000000000000c26606000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184cc0f09981e133030000000000000000000000000000000000309981e13303 0 (by decide +kernel)
private def R1948 : Restriction := restrict 0x300181e00303c00606000000000000000000000000000000000060030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001800c0f0018180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600303c00607800c0c0000000000000000000000000000000000c006060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300181e00303 0 (by decide +kernel)
private def R1949 : Restriction := restrict 0x611301000001844c040000000000000000000000000000000000000001844c04000000000000000000000000000061130100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001844c04000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2260200000308980800000000000000000000000000000000000000030898080000000000000000000000000000c2260200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003089808000000000000000000000000000000000000000000000000000 207 (by decide +kernel)
private def R1959 : Restriction := restrict 0x42600684c00c000000000000000000000000000000000042600684c00c00000000000000000000000000000000000000000000000000000000000000000000000000213003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000109801800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084c00d098018000000000000000000000000000000000084c00d098018000000000000000000000000000000000000000000000000000000000000000000000000004260060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002130030000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R1966 : Restriction := restrict 0x100101a0020300000000000000000000000000000000000000002002030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080080c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020020340040600000000000000000000000000000000000000004004060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100101800000 23 (by decide +kernel)
private def R1967 : Restriction := restrict 0x181800303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c001818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030300060600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000181800303 0 (by decide +kernel)
private def R2011 : Restriction := restrict 0x309981e13303c2660600000000000000000000000000000000006133030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003099818000000000000000000000000000000000184cc0f0998180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000613303c2660784cc0c0000000000000000000000000000000000c266060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006133030000000000000000000000000000000000309981e13303 0 (by decide +kernel)
private def R2012 : Restriction := restrict 0x300101e00203c0040600000000000000000000000000000000006002030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180080c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600203c0040780080c0000000000000000000000000000000000c004060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300101800000 23 (by decide +kernel)
private def R2020 : Restriction := restrict 0x42620684c40c000000000000000000000000000000000000000000000000000000000000000000000000002131030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001098818000000000000000000000000000000000000000109881800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084c40d098818000000000000000000000000000000000000000000000000000000000000000000000000004262060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002131030000000000000000000000000000000000000000213103 0 (by decide +kernel)
private def R2046 : Restriction := restrict 0x2e9987dd330fba661f74cc3c000000000000000000000000000000000000000000000000000000000000000000002e9987dd330fba661f74cc3c000000000000000000000000000000000000000000000000000000000000000000002e9987dd330fba661f74cc3c000000000000000000000000000000000000000000000000000000000000000000002e9987dd330fba661e000000000000000000000000000000000000000000000000000000000000000ba661f74cc3ee9987dd330f00000000000000000000000ba661f74cc3ee9987800000000000000000000005d330fba661f74cc3ee9987800000000000000000000005d330fba661e00000000000000000ba661f74cc3ee998780000000000174cc3ee998780000000000174cc3ee9987800000000000000000000005d330fba661f74cc3ee99878000000000000000000000000000000000000000000000000000000000000000000005d330fba661f74cc3ee99878000000000000000000000000000000000000000000000000000000000000000000005d330fba661f74cc3ee99878000000000000000000000000000000000000000000000000000000000000000000005d330fba661f74cc3c00000000000000000000000000000000000000000000000000000000000000174cc3ee9987dd330fba661e0000000000000000000000174cc3ee9987dd330f00000000000000000000000ba661f74cc3ee9987dd330f00000000000000000000000ba661f74cc3c0000000000000000174cc3ee9987dd330f000000000002e9987dd330f000000000002e9987dd330f 0 (by decide +kernel)
private def R2077 : Restriction := restrict 0x824205048408000000000000000000000000000000000082420400000000000000000000000000000000000000008242040000000000000000000000000000000000412102000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000209081000000000000000000000000000000000000000020908100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000104840a0908100000000000000000000000000000000001048408000000000000000000000000000000000000000104840800000000000000000000000000000000008242040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004121020000000000000000000000000000000000000000412102 1 (by decide +kernel)
private def R2092 : Restriction := restrict 0x61130f000001844c3c000000000000000000000000000061130f000001844c3c0000000000000000000000308987e1130fc2261e00000000000000000000001844c3f08987e1130f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001844c3c0000000000000000000000308987800000000001844c3f08987800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2261e0000030898780000000000000000000000000000c2261e000003089878000000000000000000000061130fc2261f844c3c0000000000000000000000308987e1130fc2261e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003089878000000000000000000000061130f00000000000308987e1130f 0 (by decide +kernel)
private def R2102 : Restriction := restrict 0x20100f00000080403c00000000000000000000000000000000000000000000000000000000000000080403d00807a0100f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010080780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040201e00000100807800000000000000000000000000000000000000000000000000000000000000100807a0100f40201e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100f00000000000000000000000 92 (by decide +kernel)
private def R2103 : Restriction := restrict 0x184440c000000000000000000000000000000000000000184440c0000000000000000000000000000000000c22206000000000000000000000000000000000061110300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003088818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030888180000000000000000000000000000000000000003088818000000000000000000000000000000000184440c0000000000000000000000000000000000c222060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000611103 0 (by decide +kernel)
private def R2105 : Restriction := restrict 0x410300000001040c000000000000000000000000000000000000000000000000000000000000000000000020818041030082060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001040c000000000000000000000000000000000000000001040c020818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082060000000208180000000000000000000000000000000000000000000000000000000000000000000000410300820601040c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002081800000000000000000000000000000000000000000208180410300 8 (by decide +kernel)
private def R2117 : Restriction := restrict 0x440280000000000000000000000008805000000000000044028088050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088050000000000000000000000001100a0000000000000880501100a 1 (by decide +kernel)
private def R2126 : Restriction := restrict 0x1844c3c0000000000000000000000000000000000000001844c3c0000000000000000000000000000000000c2261e000000000000000000000000000000000061130f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001844c3f0898780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000308987800000000000000000000000000000000000000030898780000000000000000000000000000000001844c3c0000000000000000000000000000000000c2261e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000308987e1130f 0 (by decide +kernel)
private def R2143 : Restriction := restrict 0x80403c0000000000000000000000000000000000000000000000000000000000000000000000000020100f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010080780000000000000000000000000000000000000000000000000000000000000000000000000040201e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100f00000000000000000000000 92 (by decide +kernel)
private def R2188 : Restriction := restrict 0x24818649030c920619240c30000000000000000000000024818649030c000000000000000000000000000000000024818649030c920619240c30000000000000000000000024818649030c000000000000000000000000000000000024818649030c920619240c30000000000000000000000024818649030c000000000000000000000000000000000024818649030c92061800000000000000000000001240c324818600000000000000000000000000000920619240c324818649030c00000000000000000000000920619240c30000000000000000000000000000049030c920619240c32481860000000000000000000000049030c00000000000000000000000920619240c3248186000000000001240c3248186000000000001240c32481860000000000000000000000049030c920619240c32481860000000000000000000000049030c920618000000000000000000000000000000000049030c920619240c32481860000000000000000000000049030c920618000000000000000000000000000000000049030c920619240c32481860000000000000000000000049030c920618000000000000000000000000000000000049030c920619240c30000000000000000000000024818649030c00000000000000000000000000001240c324818649030c92061800000000000000000000001240c324818600000000000000000000000000000920619240c324818649030c0000000000000000000000092061800000000000000000000001240c324818649030c0000000000024818649030c0000000000024818649030c 2 (by decide +kernel)
private def R2189 : Restriction := restrict 0x8030c100618200c30401860000000000000000000000008030c000000000000000000000000000000000000000000000000000000000000000000000000000200c30401860000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100618200c304018608030c000000000000000000000001006180000000000000000000000000000000000000000000000000000000000000000000000000004018608030c 2 (by decide +kernel)
private def R2223 : Restriction := restrict 0x78601ef0c03c0000000000000000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c0000000000000000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c000000000000000000000000000000000000000000000000000000000000000000000000003c300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03de18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601e0000000000000000000000000000000000000000000000f0c03de180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807800000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807800000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de180780000000000000000000000000000000000000000000000000000000000000000000000000078601e000000000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c0000000000000000000000000000000000000000000001e1807bc300f00000000000000000000000 92 (by decide +kernel)
private def R2235 : Restriction := restrict 0xf0401400000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0401400000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0401400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f04014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e08028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c100500000000000000000000000 92 (by decide +kernel)
private def R2249 : Restriction := restrict 0x4040148080280000000000000000000000000000000000000000000000000000000000000000000000000020200a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000808029010050000000000000000000000000000000000000000000000000000000000000000000000000004040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100500000000000000000000000000000 116 (by decide +kernel)
private def R2286 : Restriction := restrict 0xf0c03c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03c0000000000000000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c000000000000000000000000000000000000000000000000000000000000000000000000003c300f000000000000000000000000000000000000000000000000000000000000000000000000000f0c03c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807800000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807800000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de180780000000000000000000000000000000000000000000000000000000000000000000000000078601e000000000000000000000000000000000000000000000000000000000000000000000000001e18078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f00000000000000000000000 92 (by decide +kernel)
private def R2301 : Restriction := restrict 0x500018a00030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0003140006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R2303 : Restriction := restrict 0xf0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R2314 : Restriction := restrict 0x680204000001a008100000000000000000000000000000680204000001a0081000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020400000000000000000000000000000000003401020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d004080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d004080000034010200000000000000000000000000000d00408000003401020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0040800000000000000000000000000000000006802040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00810000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 508 (by decide +kernel)
private def R2319 : Restriction := restrict 0x3c1001000000f04004000000000000000000000000000000000000000000000000000000000000000000000000003c1001000000f0400400000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0400400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f040040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000782002000001e0800800000000000000000000000000000000000000000000000000000000000000000000000000782002000001e0800800000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e080080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 667 (by decide +kernel)
private def R2322 : Restriction := restrict 0x34010668020cd00419a00830000000000000000000000034010668020cd00419a0083000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034010668020cd0041800000000000000000000001a008334010668020c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020cd00418000000000000000000000000000000000068020c000000000000000000000000000000000000000000000000000000000000000000000000001a0083000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020cd00419a00833401060000000000000000000000068020cd00419a0083340106000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020cd00419a00830000000000000000000000034010668020cd004180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00419a008300000000000000000000000000000000000d0041800000000000000000000000000000000000000000000000000000000000000000000000000340106000000 25 (by decide +kernel)
private def R2330 : Restriction := restrict 0x200104400208800410000000000000000000000010008200000040020800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000820000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040020880041100082000000000000000000000002001040000008004100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200104000000 26 (by decide +kernel)
private def R2341 : Restriction := restrict 0x140004280008500010a0002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0002000000280008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000280008500010a0002140004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001400040000005000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 348 (by decide +kernel)
private def R2343 : Restriction := restrict 0x140002280004500008a000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000140002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002800040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000280004500008a0001140002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002800040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R2379 : Restriction := restrict 0x100006000000400018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000310000620000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000c000000800030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000620000c4000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R2395 : Restriction := restrict 0x34010668020cd00419a0083000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020c00000000000000000000000000001a008334010668020c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020cd00419a00833401060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00418000000000000000000000000000034010668020cd0041800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0041800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R2399 : Restriction := restrict 0x68020c000001a00830000000000000000000000000000068020c000001a0083000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034010668020cd0041800000000000000000000001a008334010668020c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d004180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d004180000034010600000000000000000000000000000d0041800000340106000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068020cd00419a00830000000000000000000000034010668020cd004180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a00830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000340106000000 25 (by decide +kernel)
private def R2418 : Restriction := restrict 0x289980513300a2660144cc000000000000000000000000289980513300a2660144cc000000000000000000000000289980513300a2660144cc0000000000000000000000000000000000000000000000000000000000000000000000289980513300a2660144cc000000000000000000000000289980513300a2660144cc000000000000000000000000289980513300a26600000000000000000000000000000000000000000000000000000000000000000a2660144cc028998051330000000000000000000000000a2660144cc028998000000000000000000000000513300a2660144cc02899800000000000000000000000000000000000000000000000000000a2660144cc028998000000000000144cc028998000000000000144cc028998000000000000000000000000513300a2660144cc028998000000000000000000000000513300a2660144cc028998000000000000000000000000513300a2660144cc0289980000000000000000000000000000000000000000000000000000000000000000000000513300a2660144cc028998000000000000000000000000513300a2660144cc028998000000000000000000000000513300a2660144cc0000000000000000000000000000000000000000000000000000000000000000144cc0289980513300a266000000000000000000000000144cc028998051330000000000000000000000000a2660144cc0289980513300000000000000000000000000000000000000000000000000000144cc02899805133000000000000028998051330000000000000289980513300 8 (by decide +kernel)
private def R2454 : Restriction := restrict 0x613307c2660f84cc1c0000000000000000000000000000613307c2660f84cc1c0000000000000000000000000000613307c2660e0000000000000000000000000000309983e13307000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184cc1f099838000000000000000030998380000000000000000309983800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2660f84cc1f0998380000000000000000000000000000c2660f84cc1f0998380000000000000000000000000000c2660f84cc1c0000000000000000000000000000613307c2660e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000309983e133070000000000000000061330700000000000000000613307 0 (by decide +kernel)
private def R2465 : Restriction := restrict 0x600307c0060e0000000000000000000000000000300183e00307000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030018380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0060f800c1c0000000000000000000000000000600307c0060e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600307 0 (by decide +kernel)
private def R2466 : Restriction := restrict 0x20300740600e80c01c00000000000000000000000000000000000000000000000000000000000000000000101803a030070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010180380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040600e80c01d0180380000000000000000000000000000000000000000000000000000000000000000000020300740600e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300700000000000000000000000 92 (by decide +kernel)
private def R2467 : Restriction := restrict 0x410300820601040c000000000000000000000000000000000000000000000000000000000000000000000000000041030082060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001040c02081800000000000000000000000000000000000000000208180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000820601040c0208180000000000000000000000000000000000000000000000000000000000000000000000000000820601040c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002081804103000000000000000000000000000000000000000000410300 8 (by decide +kernel)
private def R2470 : Restriction := restrict 0x88180110300000000000000000001103000000000000000000011030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011030022060000000000000000000220600000000000000000002206 1 (by decide +kernel)
private def R2524 : Restriction := restrict 0x613307c2660e0000000000000000000000000000309983e13307000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000309983800000000000000000000000000000000000000030998380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2660f84cc1c0000000000000000000000000000613307c2660e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006133070000000000000000000000000000000000000000613307 0 (by decide +kernel)
private def R2538 : Restriction := restrict 0x101803a03007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001018038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300740600e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300700000000000000000000000 92 (by decide +kernel)
private def R2552 : Restriction := restrict 0x160107ac020f0000000000000000000000000000000000160107ac020f58041eb0083c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160107ac020f00000000000000000000000000000b0083d60107ac020f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c020f58041e00000000000000000000000000000000002c020f58041e000000000000000000000000000000000000000000000000000000000000000000000b0083c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c020f58041e00000000000000000000000000000000002c020f58041eb0083d6010780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c020f58041e0000000000000000000000000000160107ac020f58041e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058041eb0083c000000000000000000000000000000000058041eb0083c00000000000000000000000000000000000000000000000000000000000000000000160107800000 23 (by decide +kernel)
private def R2561 : Restriction := restrict 0xc020f18041e00000000000000000000000000000000000c020f18041e00000000000000000000000000000000000000000000000000000000000000000000030083c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018041e30083c000000000000000000000000000000000018041e30083c00000000000000000000000000000000000000000000000000000000000000000000060107800000 23 (by decide +kernel)
private def R2562 : Restriction := restrict 0x2c020500000000000000000000000000000000000000002c0205000000b008140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c02050000000000000000000000000000000000160102800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058040a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058040a000000000000000000000000000000000000000058040a00000160102800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058040a00000000000000000000000000000000002c02050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b00814000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 506 (by decide +kernel)
private def R2569 : Restriction := restrict 0x40203080406000000000000000000000000000000000000000008040600000000000000000000000000000000000000000000000000000000000000000000010080c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040610080c000000000000000000000000000000000000000010080c00000000000000000000000000000000000000000000000000000000000000000000020101800000 23 (by decide +kernel)
private def R2584 : Restriction := restrict 0x90000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000120001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 989 (by decide +kernel)
private def R2589 : Restriction := restrict 0x2c020f00000000000000000000000000000000000000002c020f000000b0083c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160107ac020f00000000000000000000000000000b0083d60107ac020f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058041e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0083c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058041e000000000000000000000000000000000000000058041e0000016010780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c020f58041e0000000000000000000000000000160107ac020f58041e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0083c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160107800000 23 (by decide +kernel)
private def R2607 : Restriction := restrict 0x360187ec030fd8061e00000000000000000000001b00c3f60187ec030f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3f60187800000000000000000000006c030fd8061e000000000000000000000000000000000000000000000000000000000000000000001b00c3f60187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3c0000000000000000000000360187ec030fd8061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3f60187ec030f00000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000360187ec030f 0 (by decide +kernel)
private def R2619 : Restriction := restrict 0xb0003d60007ac000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160007ac000f58001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001eb0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R2623 : Restriction := restrict 0x4010608020c0000000000000000000000000000020083040106000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c100418000000000000000000000000000000000008020c000000000000000000000000000000000000000000000000000000000000000000000000000200830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c100418000000000000000000000000000004010608020c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100418200830000000000000000000000000000000000010041800000000000000000000000000000000000000000000000000000000000000000000000000040106000000 25 (by decide +kernel)
private def R2656 : Restriction := restrict 0x6c030f00000000000000000000000000001b00c3f60187ec030f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061e0000000000000000000000000000360187ec030fd8061e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R2659 : Restriction := restrict 0x6c000000000000000000000000000000000000003600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8000000000360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8000000000000000000000000000000000000006c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00000000006c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 478 (by decide +kernel)
private def R2685 : Restriction := restrict 0xea6203d4c4040000000000000000000000000000000000ea6203d4c4040000000000000000000000000000000000000001d4c4040000000000000000000000000000000000000001d4c4040000000000000000000000000000000000ea6203d4c4040000000000000000000000000000000000ea6203d4c4040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003a9880f5310100000000000000000000000000000000003a988080000000000000000000000000000000000000003a98808000000000000000000000000000000000000000000000000000000000000003a9880800000000000000000000000000000000000000000000000000000000000000000000000000000001d4c407a988080000000000000000000000000000000001d4c407a988080000000000000000000000000000000000000003a988080000000000000000000000000000000000000003a988080000000000000000000000000000000001d4c407a988080000000000000000000000000000000001d4c407a98808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000753101ea6202000000000000000000000000000000000075310100000000000000000000000000000000000000007531010000000000000000000000000000000000000000000000000000000000000007531010000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R2693 : Restriction := restrict 0xa988095310100000000000000000000000000000000000a988080000000000000000000000000000000000000000a98808000000000000000000000000000000000000000000000000000000000000000a9880800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001531012a6202000000000000000000000000000000000015310100000000000000000000000000000000000000001531010000000000000000000000000000000000000000000000000000000000000001531010000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R2695 : Restriction := restrict 0x686002d0c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00400000000000000000000000000000000000000000000000000000000000000000000000000000000686002d0c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c005a1800800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a1800800000000000000000000000000000000000000000000000000000000000000000000000000000000d0c005a18008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034300100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 644 (by decide +kernel)
private def R2716 : Restriction := restrict 0x210808000000000000000000000000000000000000000021080800000000000000000000000000000000000000002108080000000000000000000000000000000000000000000000000000000000000002108080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042101000000000000000000000000000000000000000004210100000000000000000000000000000000000000000421010000000000000000000000000000000000000000000000000000000000000000421010000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R2737 : Restriction := restrict 0xa108094210100000000000000000000000000000000000a108080000000000000000000000000000000000000000a10808000000000000000000000000000000000000000000000000000000000000000a108080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000142101284202000000000000000000000000000000000014210100000000000000000000000000000000000000001421010000000000000000000000000000000000000000000000000000000000000001421010000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R2742 : Restriction := restrict 0xea6203d4c40400000000000000000000000000000000000000000000000000000000000000000000000000000000000001d4c4040000000000000000000000000000000000000001d4c4040000000000000000000000000000000000ea6203d4c40400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003a988080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d4c407a9880800000000000000000000000000000000000000000000000000000000000000000000000000000000000003a988080000000000000000000000000000000000000003a988080000000000000000000000000000000001d4c407a98808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000075310100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 644 (by decide +kernel)
private def R2750 : Restriction := restrict 0x19444040000000000000000000000000000000000000001944404000000000000000000000000000000000000000194440400000000000000000000000000000000000000019444040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032888080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003288808000000000000000000000000000000000000000328880800000000000000000000000000000000000000032888080000000000000000000000000000000000000003288808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006511010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R2756 : Restriction := restrict 0x1940404000000000000000000000000000000000000000000000000000000000000000000000000000000000000019404040000000000000000000000000000000000000001940404000000000000000000000000000000000000000194040400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006501010000000000000000000000000000000000000000000000000000000000000000000000000000000032808080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000328080800000000000000000000000000000000000000000000000000000000000000000000000000000000000003280808000000000000000000000000000000000000000328080800000000000000000000000000000000000000032808080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ca0202000000000000000000000000000000000000000000000000000000000000000000000000000000006501010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R2766 : Restriction := restrict 0x406002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040600280c00400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001018008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c005018008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 644 (by decide +kernel)
private def R2782 : Restriction := restrict 0x10441c208838411070000000000000000000000000000010441c208838411070000000000000000000000008220e10441c208838000000000000000000000000000008220e10441c0000000000000000010441c208838411070000000000002088384110700000000000020883841107000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002088384110708220e000000000000000000000000000002088384110708220e0000000000000000000000010441c208838411070000000000000000000000000000010441c208838000000000000000002088384110708220e0000000000004110708220e0000000000004110708220e 1 (by decide +kernel)
private def R2823 : Restriction := restrict 0x10000780000040001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080003d00007a0000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000f40001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000f00000080003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100007a0000f40001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040001e80003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R2841 : Restriction := restrict 0x80003d00007a0000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000f40001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100007a0000f40001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040001e80003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R2844 : Restriction := restrict 0x160002ac000558000ab000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000558000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000558000ab0001560002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c00050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058000ab0001400000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R2855 : Restriction := restrict 0x300007800000c0001e0000000000000000000000000000300007800000c0001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300007e0000fc0001e0000000000000000000000180003f00007e0000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000fc0001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000f00000180003c000000000000000000000000000060000f00000180003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000fc0001f80003c0000000000000000000000300007e0000fc0001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0001f80003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R2857 : Restriction := restrict 0x6c0301000001b00c0400000000000000000000000000006c0301000001b00c040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d806020000036018080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d806020000036018080000000000000000000000000000d80602000003601808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8060200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b00c04000006c03010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R2901 : Restriction := restrict 0x360187ec030fd8061fb00c3c0000000000000000000000360187ec030fd8061fb00c3c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3f60187800000000000000000000006c030fd8061e000000000000000000000000000000000000000000000000000000000000000000001b00c3f6018780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3f60187800000000000000000000006c030fd8061fb00c3f60187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3f60187ec030f00000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000360187ec030f 0 (by decide +kernel)
private def R2939 : Restriction := restrict 0x360187ec030fd8061e00000000000000000000001b00c3f60187ec030f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061e000000000000000000000000000000000000000000000000000000000000000000001b00c3f60187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3c0000000000000000000000360187ec030fd8061e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000360187ec030f 0 (by decide +kernel)
private def R2958 : Restriction := restrict 0x8030f10061e000000000000000000000000000000000008030f000000000000000000000000000000000000000000000000000000000000000000000000000200c3c40187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010061e200c3c000000000000000000000000000000000010061e0000000000000000000000000000000000000000000000000000000000000000000000000004018788030f 0 (by decide +kernel)
private def R2963 : Restriction := restrict 0xc030d18061a00000060186800000000000000000000000c030d000000000000000000000000000000000000000000000000000000000000000000000000000300c3400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018061a300c34000000c030d0000000000000000000000018061a00000000000000000000000000000000000000000000000000000000000000000000000000060186800000 23 (by decide +kernel)
private def R2970 : Restriction := restrict 0xc030d18061a300c3460186800000000000000000000000c030d18061a000000000000000000000000000000000000000000000000000000000000000000000300c3400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018061a300c34601868c030d0000000000000000000000018061a300c3400000000000000000000000000000000000000000000000000000000000000000000060186800000 23 (by decide +kernel)
private def R2977 : Restriction := restrict 0xd440040000000000000000000000000000000000000000d4400400000000000000000000000000000000000000000000000000000000000000000000000000000000000000d440040000000000000000000000000000000000000000d440040000000000000000000000000000000000000000d4400400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000035100100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a880080000000000000000000000000000000000000001a8800800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a880080000000000000000000000000000000000000001a880080000000000000000000000000000000000000001a880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006a2002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 805 (by decide +kernel)
private def R2985 : Restriction := restrict 0x8020e10041c200838000000000000000000000000000008020e10041c00000000000000000000000000000000000000000000000000000000000000000000020083840107000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010041c200838401070000000000000000000000000000010041c2008380000000000000000000000000000000000000000000000000000000000000000000004010708020e 1 (by decide +kernel)
private def R2999 : Restriction := restrict 0x2088380000000000000000000000000000000000000000208838000000000000000000000000000000000010441c00000000000000000000000000000000000000000000000000000000000000010441c20883841107000000000000208838411070000000000002088384110700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000411070000000000000000000000000000000000000000041107000000000000000000000000000000000002088380000000000000000000000000000000000000000000000000000000000000002088384110708220e0000000000004110708220e0000000000004110708220e 1 (by decide +kernel)
private def R3011 : Restriction := restrict 0x802021004042008080000000000000000000000000000080202100404000000000000000000000000000000000000000000000000000000000000000000000200808401010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100404200808401010000000000000000000000000000010040420080800000000000000000000000000000000000000000000000000000000000000000000040101080202 1 (by decide +kernel)
private def R3033 : Restriction := restrict 0x3c0000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R3071 : Restriction := restrict 0x40600680c00c00000000000000000000000000000000000000000000000000000000000000080c00d01801a030030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c00d01801800000000000000000000000000000000000000000000000000000000000000101801a030034060060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 989 (by decide +kernel)
private def R3072 : Restriction := restrict 0x78601ef0c03c000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601ef0c03c0000000000000000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f000000000000000000000000000000000000000000000000000000000000000000000000000000001e18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601ef0c03de1807800000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de18078000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601e000000000000000000000000000000000000000000000000000000000000000000000000000000003c300f00000000000000000000000000000000000000000000000000000000000000000000078601ef0c03c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3073 : Restriction := restrict 0x8040140000000000000000000000000000000000000000000000000000000000000000000010080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008028000000000000000000000000000000000000000000000000000000000000000000002010050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 1012 (by decide +kernel)
private def R3082 : Restriction := restrict 0x40001e80003c00000000000000000000000000000000000000000000000000000000000000080003d00007a0000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080003d00007800000000000000000000000000000000000000000000000000000000000000100007a0000f40001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 989 (by decide +kernel)
private def R3087 : Restriction := restrict 0x606000c0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000606000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0018180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000181800000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c001818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R3091 : Restriction := restrict 0x1010050000004040140000000000000000000000000000000000000000000000000000000000000000000008080290100520200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200a0000008080280000000000000000000000000000000000000000000000000000000000000000000010100520200a4040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100500000000000000000000000000000 116 (by decide +kernel)
private def R3099 : Restriction := restrict 0x20100500000080401400000000000000000000000000000000000000000000000000000000000000080401500802a010050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040200a00000100802800000000000000000000000000000000000000000000000000000000000000100802a0100540200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100500000000000000000000000 92 (by decide +kernel)
private def R3117 : Restriction := restrict 0x606000c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000606000c0c000000000000000000000000000000000000000000000000000000000000000000000000000003030000000000000000000000000000000000000000000000000000000000000000000000000000000000018180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0018180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c001818000000000000000000000000000000000000000000000000000000000000000000000000000006060000000000000000000000000000000000000000000000000000000000000000000000000000000000030300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 656 (by decide +kernel)
private def R3142 : Restriction := restrict 0x101807a0300f40601e80c03c0000000000000000000000000000000000000000000000000000000000000000000000000020300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300f40601e80c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000040601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R3145 : Restriction := restrict 0x48600690c00c0000000000000000000000000000000000000000000000000000000000000000000000000000000048600690c00c0000000000000000000000000000000000000000000000000000000000000000000000000024300300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000486006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090c00d2180180000000000000000000000000000000000000000000000000000000000000000000000000000000090c00d218018000000000000000000000000000000000000000000000000000000000000000000000000004860060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3172 : Restriction := restrict 0x48000690000c0000000000000000000000000000000000000000000000000000000000000000000000000000000048000690000c0000000000000000000000000000000000000000000000000000000000000000000000000000000048000690000c00000000000000000000000000000000000000000000000000000000000000000000000000240003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004800060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000d2000180000000000000000000000000000000000000000000000000000000000000000000000000000000090000d2000180000000000000000000000000000000000000000000000000000000000000000000000000000000090000d200018000000000000000000000000000000000000000000000000000000000000000000000000004800060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3190 : Restriction := restrict 0x120001a4000348000690000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000d20001a4000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000480006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000024000348000690000d2000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000120001a400034800060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3216 : Restriction := restrict 0x686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180180000000000000000000000000000000000000000000000000000000000000000000000000068600600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da1801800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a1801800000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da180180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000343003000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3225 : Restriction := restrict 0xd0400c00000000000000000000000000000000000000000000000000000000000000000000000000000000682006d0400c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0400c000000000000000000000000000000000000000000000000000000000000000000000000003410030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068200600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a0801800000000000000000000000000000000000000000000000000000000000000000000000000000000d0400da0801800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a080180000000000000000000000000000000000000000000000000000000000000000000000000068200600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0400c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3236 : Restriction := restrict 0x3c300f000000f0c03c000000000000000000000000000000000000000000000000000000000000000000000000003c300f000000f0c03c000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601ef0c03c000000000000000000000000000000000000000000000000000000000000000f0c03de1807bc300f000000000000000000000000000000000000000000000000000000000000000000000000000f0c03c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0c03de18078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000078601e000001e180780000000000000000000000000000000000000000000000000000000000000000000000000078601e000001e18078000000000000000000000000000000000000000000000000000000000000000000003c300f78601ef0c03de18078000000000000000000000000000000000000000000000000000000000000001e1807bc300f78601e000000000000000000000000000000000000000000000000000000000000000000000000001e18078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e1807bc300f00000000000000000000000 92 (by decide +kernel)
private def R3247 : Restriction := restrict 0x14000628000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000314000628000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c500018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014000628000c5000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R3249 : Restriction := restrict 0x3c0000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000780000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R3257 : Restriction := restrict 0x201005000000804014000000000000000000000000000000000000000000000000000000000000000000000000002010050000008040140000000000000000000000000000000000000000000000000000000000000000000000000020100500000080401400000000000000000000000000000000000000000000000000000000000000000000100802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040200a0000010080280000000000000000000000000000000000000000000000000000000000000000000000000040200a0000010080280000000000000000000000000000000000000000000000000000000000000000000000000040200a000001008028000000000000000000000000000000000000000000000000000000000000000000002010050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100500000000000000000000000 92 (by decide +kernel)
private def R3354 : Restriction := restrict 0x2c1005000000b04014000000000000000000000000000000000000000000000000000000000000000000000000002c1005000000b040140000000000000000000000000000000000000000000000000000000000000000000016080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058200a0000016080280000000000000000000000000000000000000000000000000000000000000000000000000058200a000001608028000000000000000000000000000000000000000000000000000000000000000000002c1005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c100500000000000000000000000 92 (by decide +kernel)
private def R3355 : Restriction := restrict 0x160007ac000f58001eb0003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001eb0003d60007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001eb0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3364 : Restriction := restrict 0x686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000686006d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180180000000000000000000000000000000000000000000000000000000000000000000000000068600600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da1801800000000000000000000000000000000000000000000000000000000000000000000000000000000d0c00da1801800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a180180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000343003000000000000000000000000000000000000000000000000000000000000000000000000000d0c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3373 : Restriction := restrict 0xd0401400000000000000000000000000000000000000000000000000000000000000000000000000000000000000d0401400000000000000000000000000000000000000000000000000000000000000000000000000341005000000d04014000000000000000000000000000000000000000000000000000000000000000000001a0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a0802800000000000000000000000000000000000000000000000000000000000000000000000000000000000001a080280000000000000000000000000000000000000000000000000000000000000000000000000068200a000001a08028000000000000000000000000000000000000000000000000000000000000000000003410050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034100500000000000000000000000 92 (by decide +kernel)
private def R3415 : Restriction := restrict 0x184c42c0000000000000000000000309885800000c2621784c42c00000000000000000000000000000000000000000000000000000000000000184c42c0000061310b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184c42c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003098858000000000000000000000061310b00000184c42f09885800000000000000000000000000000000000000000000000000000000000000309885800000c262160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030988580000000000000000000000000000 115 (by decide +kernel)
private def R3430 : Restriction := restrict 0x10180780000040601e80c03c00000000000000000000000000000000000000000000000000000000000000080c03c0000020300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300f00000080c03d0180780000000000000000000000000000000000000000000000000000000000000010180780000040601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R3449 : Restriction := restrict 0x2a6216000000a988595310b000000000000000000000002a6216000000a98858000000000000000000000015310b00000054c42ca98858000000000000000000000015310b2a6216000000000000000002a6216000000a988580000000000054c42c0000000000000000054c42ca98858000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000054c42c0000015310b2a62160000000000000000000000054c42c0000015310b000000000000000000000002a6216000000a988595310b000000000000000000000002a621654c42c0000000000000000054c42c0000015310b000000000000a9885800000000000000000a988595310b 0 (by decide +kernel)
private def R3458 : Restriction := restrict 0x4010b00000010042c200858000000000000000000000004010b08021600000000000000000000000000000000000000000000000000000000000000000000010042c2008580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000802160000002008584010b0000000000000000000000008021610042c0000000000000000000000000000000000000000000000000000000000000000000002008584010b 0 (by decide +kernel)
private def R3460 : Restriction := restrict 0x226000000000898001130000000000000000000000000022600000000089800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002260000000008980000000000000044c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c000000001130002260000000000000000000000000044c000000001130000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c000000001130000000000000008980000000000000000000000000000000 127 (by decide +kernel)
private def R3467 : Restriction := restrict 0x1130000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002260000000008980000000000000044c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c000000001130000000000000008980000000000000000000000000000000 127 (by decide +kernel)
private def R3474 : Restriction := restrict 0x226206000000898819131030000000000000000000000022620600000089881800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002262060000008988180000000000044c40c00000000000000000000000898818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c40c000001131032262060000000000000000000000044c40c000001131030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c40c000001131030000000000008988180000000000000000000000113103 0 (by decide +kernel)
private def R3479 : Restriction := restrict 0x2a6000000000a9800153000000000000000000000000002a6000000000a98000000000000000000000000015300000000054c000a9800000000000000000000000001530002a6000000000000000000002a6000000000a980000000000000054c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000054c000000001530002a60000000000000000000000000054c00000000153000000000000000000000000002a6000000000a9800153000000000000000000000000002a600054c0000000000000000000054c00000000153000000000000000a980000000000000000000000000000000 127 (by decide +kernel)
private def R3487 : Restriction := restrict 0x2262000000008988011310000000000000000000000000226200000000898800000000000000000000000011310000000044c4008988000000000000000000000000000000000000000000000000000002262000000008988000000000000044c4000000000000000000044c400898800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c400000001131002262000000000000000000000000044c400000001131000000000000000000000000022620000000089880113100000000000000000000000000000000000000000000000000000044c400000001131000000000000008988000000000000000000089880113100 8 (by decide +kernel)
private def R3491 : Restriction := restrict 0x401080000001004202008400000000000000000000000040108080210000000000000000000000000000000000000000000000000000000000000000000000100420200840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080210000000200840401080000000000000000000000008021010042000000000000000000000000000000000000000000000000000000000000000000000020084040108 3 (by decide +kernel)
private def R3498 : Restriction := restrict 0xa02160000002808585010b00000000000000000000000000000000000000000000000000000000000000005010b00000014042c280858000000000000000000000005010b0a0216000000000000000000a0216000000280858000000000000000000000000000000000014042c280858000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014042c0000005010b0a02160000000000000000000000000000000000000000000000000000000000000000a02160000002808585010b000000000000000000000000a021614042c0000000000000000014042c0000005010b000000000000000000000000000000000002808585010b 0 (by decide +kernel)
private def R3500 : Restriction := restrict 0x5310b00000014c42c298858000000000000000000000005310b0a621600000000000000000000000000000298858000000000000000000000000000000000014c42c2988580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a62160000002988585310b000000000000000000000000a621614c42c000000000000000000000000000005310b000000000000000000000000000000000002988585310b 0 (by decide +kernel)
private def R3508 : Restriction := restrict 0x280216000000a008594010b00000000000000000000000280216000000a00858000000000000000000000014010b00000050042ca00858000000000000000000000014010b28021600000000000000000000000000000000000000000000000000000000000000000000050042ca00858000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050042c0000014010b2802160000000000000000000000050042c0000014010b00000000000000000000000280216000000a008594010b0000000000000000000000028021650042c000000000000000000000000000000000000000000000000000000000000000000000a008594010b 0 (by decide +kernel)
private def R3515 : Restriction := restrict 0x15110b00000000000000000000000000000000000000000000000000000000000000015110b00000054442ca88858000000000000000000000015110b2a221600000000000000000000000000000000000000000000000000000000000000000000054442ca888580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002a22160000000000000000000000000000000000000000000000000000000000000002a2216000000a888595110b000000000000000000000002a221654442c000000000000000000000000000000000000000000000000000000000000000000000a888595110b 0 (by decide +kernel)
private def R3521 : Restriction := restrict 0x2a6202000000a9880953101000000000000000000000002a6202000000a988080000000000000000000000000000000000000000a988080000000000000000000000000000000000000000000000000002a6202000000a988080000000000054c40400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000054c404000001531012a62020000000000000000000000054c404000001531010000000000000000000000000000000000000000153101000000000000000000000000000000000000000000000000000054c40400000153101000000000000a988080000000000000000000000000000 115 (by decide +kernel)
private def R3526 : Restriction := restrict 0x401090000001004242008480000000000000000000000040109080212000000000000000000000000000000000000000000000000000000000000000000000100424000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080212000000200848401090000000000000000000000008021210042400000000000000000000000000000000000000000000000000000000000000000000020084800000 23 (by decide +kernel)
private def R3568 : Restriction := restrict 0x20100540200a80401400000000000000000000000000000000000000000000000000000000000000000000100802a010050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040200a8040150080280000000000000000000000000000000000000000000000000000000000000000000020100540200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100500000000000000000000000 92 (by decide +kernel)
private def R3569 : Restriction := restrict 0x1010050000004040148080280000000000000000000000000000000000000000000000000000000000000008080280000020200a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008080280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200a000000808029010050000000000000000000000000000000000000000000000000000000000000001010050000004040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010100500000000000000000000000000000 116 (by decide +kernel)
private def R3593 : Restriction := restrict 0x14000628000c000000a0003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a00031400060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000c500018000001400060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014000628000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000 347 (by decide +kernel)
private def R3620 : Restriction := restrict 0x160007ac000f000000b0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0003d60007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000f58001e0000016000780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160007ac000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001eb0003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3627 : Restriction := restrict 0x2c000758000eb0001c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160003ac00070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058000eb0001d60003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000758000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0001c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3638 : Restriction := restrict 0x48001e90003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090003d20007a4000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090003d2000780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000120007a4000f48001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090003c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R3640 : Restriction := restrict 0x101807a0300f00000000000000000000000000000000000000000000000000000000000000000000000000080c03d01807a0300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300f40601e00000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f40601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R3648 : Restriction := restrict 0x1e00003c0000780000f00000000000000000000000000000000000000000000000000000000000000000000000001e00003c0000780000f00000000000000000000000000000000000000000000000000000000000000000000000001e00003c0000780000f00000000000000000000000000000000000000000000000000000000000000000000f00001e00003c0000000000000000000000000000000000000000000000000000000000000000000000000780000f00001e00000000000000000000000000000000000000000000000000000000000000000000000003c0000780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0000780000f00001e00000000000000000000000000000000000000000000000000000000000000000000000003c0000780000f00001e00000000000000000000000000000000000000000000000000000000000000000000000003c0000780000f00001e00000000000000000000000000000000000000000000000000000000000000000001e00003c0000780000000000000000000000000000000000000000000000000000000000000000000000000f00001e00003c0000000000000000000000000000000000000000000000000000000000000000000000000780000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 340 (by decide +kernel)
private def R3668 : Restriction := restrict 0x7c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c0000000001f0000000000000000000000000000000007c000000000000000000000000000000000000003e0000000000000000000000000000000000000000000000000000000000000000000000000000000000001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f80000000003e000000000000000000000000000000000f8000000000000000000000000000000000000007c0000000000000000000000000000000000000000000000000000000000000000000000000000000000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 685 (by decide +kernel)
private def R3676 : Restriction := restrict 0x10100520200a4040148080280000000000000000000000000000000000000000000000000000000000000000000010100520200a4040148080280000000000000000000000000000000000000000000000000000000000000000000010100520200a4040148080280000000000000000000000000000000000000000000000000000000000000008080290100520200a0000000000000000000000000000000000000000000000000000000000000000000004040140000010100500000000000000000000000000000000000000000000000000000000000000000000020200a4040140000000000000000000000000000000000000000000000808028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200a4040148080290100500000000000000000000000000000000000000000000000000000000000000000000020200a4040148080290100500000000000000000000000000000000000000000000000000000000000000000000020200a4040148080290100500000000000000000000000000000000000000000000000000000000000000010100520200a4040140000000000000000000000000000000000000000000000000000000000000000000008080280000020200a00000000000000000000000000000000000000000000000000000000000000000000040401480802800000000000000000000000000000000000000000000010100500000000000000000000000000000 116 (by decide +kernel)
private def R3721 : Restriction := restrict 0x20918541230a824615048c280000000000000000000000209185000000824614000000000000000000000000000020918541230a82461400000000000000000000001048c280000041230a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000824615048c2a09185000000000001048c2800000000000000001048c2a0918500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000041230a824615048c2a091850000000000000000000000041230a000001048c28000000000000000000000000000041230a824615048c2800000000000000000000002091850000008246140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001048c2a0918541230a000000000002091850000000000000000020918541230a 1 (by decide +kernel)
private def R3749 : Restriction := restrict 0x824615048c280000000000000000000000000000000000824614000000000000000000000000000020918541230a82461400000000000000000000001048c280000041230a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020918500000000000000000000000000000000001048c2a09185000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001048c2a0918500000000000000000000000000000000001048c28000000000000000000000000000041230a824615048c28000000000000000000000020918500000082461400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000041230a000000000000000000000000000000000020918541230a 1 (by decide +kernel)
private def R3761 : Restriction := restrict 0x20100540200a8040150080280000000000000000000000201005000000804014000000000000000000000000000020100540200a804014000000000000000000000010080280000040200a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040200a80401500802a010050000000000000000000000040200a000001008028000000000000000000000000000040200a80401500802800000000000000000000002010050000008040140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100500000000000000000000000000000 116 (by decide +kernel)
private def R3854 : Restriction := restrict 0x10180780000040601e00000000000000000000000000000000000000000000000000000000000000000000080c03d01807a0300f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080c03d0180780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020300f00000080c03c00000000000000000000000000000000000000000000000000000000000000000000101807a0300f40601e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101807a0300f00000000000000000000000 92 (by decide +kernel)
private def R3945 : Restriction := restrict 0x109987a1330f42661e84cc3c00000000000000000000000000000000000000000000000000000000000000084cc3d09987a1330f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042661e84cc3d0998780000000000084cc3d0998780000000000084cc3d09987800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021330f42661e84cc3d09987800000000000000000000000000000000000000000000000000000000000000109987a1330f42661e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084cc3d09987a1330f00000000000109987a1330f00000000000109987a1330f 0 (by decide +kernel)
private def R3953 : Restriction := restrict 0x800c3d00187a0030f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800c3d00187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100187a0030f40061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100187a0030f 0 (by decide +kernel)
private def R3976 : Restriction := restrict 0x8008310010620020c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008008300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010010620020c4004180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100106000000 25 (by decide +kernel)
private def R3984 : Restriction := restrict 0x210300000000840c00000000000000000000000000000000000000000000000000000000000000000000001081800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000840c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000420600000001081800000000000000000000000000000000000000000000000000000000000000000000002103000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001081800000000000000000000000000000000000000000000000000000 215 (by decide +kernel)
private def R3997 : Restriction := restrict 0x42600084c000000000000000000000000000000000000000000000000000000000000000000000000000002130000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001098000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084c001098000000000000000000000000000000000000000000000000000000000000000000000000000004260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002130000000000000000000000000000000000000000000000000 196 (by decide +kernel)
private def R4010 : Restriction := restrict 0x42661e84cc3c00000000000000000000000000000000000000000000000000000000000000084cc3d09987a1330f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001099878000000000000000000000000000000000084cc3d09987800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084cc3d09987800000000000000000000000000000000000000000000000000000000000000109987a1330f42661e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021330f0000000000000000000000000000000000109987a1330f 0 (by decide +kernel)
private def R4012 : Restriction := restrict 0x308187e1030fc2061f840c3c00000000000000000000000000000000000000000000000000000000000000000000308187e1030fc2061e00000000000000000000001840c3f08187e1030f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2061f840c3f0818780000000000000000000000000000000001840c3f0818780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000061030fc2061f840c3f0818780000000000000000000000000000000000000000000000000000000000000000000061030fc2061f840c3c0000000000000000000000308187e1030fc2061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001840c3f08187e1030f0000000000000000000000000000000000308187e1030f 0 (by decide +kernel)
private def R4019 : Restriction := restrict 0xc2020784040c00000000000000000000000000000000000000000000000000000000000000000000000000000000c202060000000000000000000000000000000000610103000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000308081800000000000000000000000000000000000000030808180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184040f0808180000000000000000000000000000000000000000000000000000000000000000000000000000000184040c0000000000000000000000000000000000c202060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006101030000000000000000000000000000000000000000610103 0 (by decide +kernel)
private def R4020 : Restriction := restrict 0x610305000001840c140000000000000000000000000000000000000000000000000000000000000000000000000061030500000000000000000000000000000000003081828000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001840c14000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2060a00000308182800000000000000000000000000000000000000000000000000000000000000000000000000c2060a00000000000000000000000000000000006103050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003081828000000000000000000000000000000000000000000000000000 207 (by decide +kernel)
private def R4039 : Restriction := restrict 0xc2061f840c3c00000000000000000000000000000000000000000000000000000000000000000000000000000000c2061e000000000000000000000000000000000061030f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030818780000000000000000000000000000000001840c3f08187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001840c3f08187800000000000000000000000000000000000000000000000000000000000000000000000000000001840c3c0000000000000000000000000000000000c2061e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000061030f0000000000000000000000000000000000308187e1030f 0 (by decide +kernel)
private def R4046 : Restriction := restrict 0xc2000784000c00000000000000000000000000000000000000000000000000000000000000000000000000000000c200060000000000000000000000000000000000610003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000308001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000184000f0800180000000000000000000000000000000000000000000000000000000000000000000000000000000184000c0000000000000000000000000000000000c200060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006100030000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R4047 : Restriction := restrict 0x42000684000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000210003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000108001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084000d0800180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004200060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002100030000000000000000000000000000000000000000000000 184 (by decide +kernel)
private def R4049 : Restriction := restrict 0x2020604040c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008081800000000000000000000000000000000000000000808180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004040c0808180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000101030000000000000000000000000000000000000000010103 0 (by decide +kernel)
private def R4092 : Restriction := restrict 0x22601444c0288980511300a0000000000000000000000022601444c028898050000000000000000000000011300a00000044c028000000000000000000000000000011300a2260140000000000000000022601444c0288980500000000000044c0288980500000000000044c028898050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c0288980511300a2260140000000000000000000000044c0288980511300a00000000000000000000000226014000000898050000000000000000000000000000022601444c0280000000000000000044c0288980511300a0000000000008980511300a0000000000008980511300a 1 (by decide +kernel)
private def R4108 : Restriction := restrict 0x8980111300200000000000000000000000000000000000898010000000000000000000000000000000000044c0080000000000000000000000000000000000226004000000000000000000000000000008980100000000000000000000000000000000000000000898010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000113002226004000000000000000000000000000000000011300200000000000000000000000000000000000898010000000000000000000000000000000000044c00800000000000000000000000000001130020000000000000000000000000000000000000000113002 1 (by decide +kernel)
private def R4117 : Restriction := restrict 0x880011100020000000000000000000000000000000000088001000000000000000000000000000000000004400080000000000000000000000000000000000220004000000000000000000000000000008800100000000000000000000000000000000000000000880010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110002220004000000000000000000000000000000000011000200000000000000000000000000000000000880010000000000000000000000000000000000044000800000000000000000000000000001100020000000000000000000000000000000000000000110002 1 (by decide +kernel)
private def R4122 : Restriction := restrict 0x44c0280000011300a0000000000000000000000000000044c028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022601444c0288980500000000000044c0288980500000000000044c02889805000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008980500000022601400000000000000000000000000000898050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000044c0288980511300a0000000000008980511300a0000000000008980511300a 1 (by decide +kernel)
private def R4164 : Restriction := restrict 0x360186ec030d000001b00c340000000000000000000000360186ec030d000001b00c34000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000360186ec030d00000000000000000000000000001b00c376018680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030dd8061a00000360186800000000000000000000006c030d000000000000000000000000000000000000000000000000000000000000000000000000001b00c340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030dd8061a00000360186800000000000000000000006c030dd8061a0000036018680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030dd8061a0000000000000000000000000000360186ec030d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061bb00c34000006c030d00000000000000000000000d8061a00000000000000000000000000000000000000000000000000000000000000000000000000360186800000 23 (by decide +kernel)
private def R4170 : Restriction := restrict 0x160006ac000d000000b0003400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0003560006800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c000d58001a0000016000680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160006ac000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000058001a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000 345 (by decide +kernel)
private def R4175 : Restriction := restrict 0x401090000000000002008480000000000000000000000040109000000000000000000000000000000000000000000000000000000000000000000000000000100424000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080212000000000000401090000000000000000000000008021200000000000000000000000000000000000000000000000000000000000000000000000000020084800000 23 (by decide +kernel)
private def R4195 : Restriction := restrict 0xc010918021200000060084800000000000000000000000c0109000000000000000000000000000000000000000000000000000000000000000000000000000300424000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180212300424000000c01090000000000000000000000018021200000000000000000000000000000000000000000000000000000000000000000000000000060084800000 23 (by decide +kernel)
private def R4207 : Restriction := restrict 0x10000680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800035000068000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100006a0000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040001a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000 345 (by decide +kernel)
private def R4221 : Restriction := restrict 0x640301000001900c040000000000000000000000000000000000000001900c0400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000064030100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c806020000032018080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c806020000032018080000000000000000000000000000000000000003201808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c8060200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001900c04000006403010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R4229 : Restriction := restrict 0x1900c140000000000000000000000000000000000000001900c140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006403050000000000000000000000000000000000320182800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000320182800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032018280000000000000000000000000000000000000003201828000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c8060a00000000000000000000000000000000006403050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006403050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 460 (by decide +kernel)
private def R4234 : Restriction := restrict 0x360186ec030d000001b00c340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030d00000000000000000000000000001b00c3760186800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030dd8061a000003601868000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061a0000000000000000000000000000360186ec030d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000 345 (by decide +kernel)
private def R4239 : Restriction := restrict 0x6c030f000001b00c3c00000000000000000000000000006c030f000001b00c3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030f000000000000000000000000000000000036018780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061fb00c3f60187800000000000000000000006c030fd8061e000000000000000000000000000000000000000000000000000000000000000000001b00c3f601878000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061e0000036018780000000000000000000000000000d8061e000003601878000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061e00000000000000000000000000000000006c030f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3f60187ec030f00000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000360187ec030f 0 (by decide +kernel)
private def R4252 : Restriction := restrict 0x8020c000000000000000000000000000000000000000008020c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c0000000000000000000000000000000000040106000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008020c100418000000000000000000000000000000000008020c0000000000000000000000000000000000000000000000000000000000000000000000000002008300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001004180000000000000000000000000000000000000000100418000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100418000000000000000000000000000000000008020c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100418200830000000000000000000000000000000000010041800000000000000000000000000000000000000000000000000000000000000000000000000040106000000 25 (by decide +kernel)
private def R4265 : Restriction := restrict 0x60000a00000000000000000000000000000000003000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180002b0000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00014000000000000000000000000000000000060000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000560000a 1 (by decide +kernel)
private def R4274 : Restriction := restrict 0x6c030f000001b00c3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030f0000000000000000000000000000000000360187800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c030fd8061e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061e000003601878000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061e00000000000000000000000000000000006c030f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d8061fb00c3c00000000000000000000000000000000000000000000000000000000000000000000000000000000 322 (by decide +kernel)
private def R4306 : Restriction := restrict 0x190040c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c80206000000000000000000000000000000000000000000000000000000000000000000000000003200818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000320081800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000190040c00000000000000000000000000000000000000000000000000000000000000000000000000640103 0 (by decide +kernel)
private def value0 : W := R0.P x0
private def value1 : W := R0.P x1
private def value2 : W := R0.P x2
private def value3 : W := R0.P x3
private def value4 : W := R0.P x4
private def value5 : W := R0.P x5
private def value6 : W := R0.P x6
private def value7 : W := R4.P x0
private def value8 : W := R4.P x1
private def value9 : W := R4.P x3
private def value10 : W := R4.P x4
private def value11 : W := R4.P x5
private def value12 : W := R4.P x6
private def value13 : W := R5.P x1
private def value14 : W := R5.P x3
private def value15 : W := R5.P x4
private def value16 : W := R5.P x5
private def value17 : W := R5.P x6
private def value18 : W := R6.P x0
private def value19 : W := R6.P x3
private def value20 : W := R6.P x4
private def value21 : W := R6.P x5
private def value22 : W := R6.P x6
private def value23 : W := R7.P x3
private def value24 : W := R7.P x4
private def value25 : W := R7.P x5
private def value26 : W := R7.P x6
private def value27 : W := R12.P ((~~~x5) &&& x6)
private def value28 : W := R12.P ((~~~x4) &&& x6)
private def value29 : W := R12.P ((~~~x1) &&& x6)
private def value30 : W := R12.P ((~~~x0) &&& x6)
private def value31 : W := R12.P x0
private def value32 : W := R12.P x1
private def value33 : W := R12.P x4
private def value34 : W := R12.P x5
private def value35 : W := R12.P x6
private def value36 : W := R13.P ((~~~x5) &&& x6)
private def value37 : W := R13.P ((~~~x5) &&& (x1 ||| x6))
private def value38 : W := R13.P ((~~~x5) &&& (x4 ||| x6))
private def value39 : W := R13.P x1
private def value40 : W := R13.P (x1 ||| ((~~~x5) &&& x6))
private def value41 : W := R13.P x4
private def value42 : W := R13.P (x4 ||| ((~~~x5) &&& x6))
private def value43 : W := R13.P x5
private def value44 : W := R13.P (x1 ||| x5)
private def value45 : W := R13.P (x4 ||| x5)
private def value46 : W := R13.P x6
private def value47 : W := R14.P ((~~~x4) &&& x6)
private def value48 : W := R14.P ((~~~x4) &&& (x0 ||| x6))
private def value49 : W := R14.P ((~~~x4) &&& (x5 ||| x6))
private def value50 : W := R14.P x0
private def value51 : W := R14.P (x0 ||| ((~~~x4) &&& x6))
private def value52 : W := R14.P x4
private def value53 : W := R14.P (x0 ||| x4)
private def value54 : W := R14.P x5
private def value55 : W := R14.P (x5 ||| ((~~~x4) &&& x6))
private def value56 : W := R14.P (x4 ||| x5)
private def value57 : W := R14.P x6
private def value58 : W := R20.P (x0 &&& (~~~x5))
private def value59 : W := R20.P ((~~~x5) &&& (x0 ||| x1))
private def value60 : W := R20.P x0
private def value61 : W := R20.P x1
private def value62 : W := R20.P x3
private def value63 : W := R20.P x5
private def value64 : W := R20.P (x0 ||| x5)
private def value65 : W := R20.P x6
private def value66 : W := R21.P (x1 &&& (~~~x5))
private def value67 : W := R21.P ((~~~x3) &&& x5)
private def value68 : W := R21.P x1
private def value69 : W := R21.P x3
private def value70 : W := R21.P x5
private def value71 : W := R21.P (x6 &&& ((~~~x1) ||| x5))
private def value72 : W := R21.P x6
private def value73 : W := R22.P x0
private def value74 : W := R22.P x5
private def value75 : W := R22.P (x0 ||| x6)
private def value76 : W := R22.P (x3 ||| x6)
private def value77 : W := R22.P (x5 ||| x6)
private def value78 : W := R28.P (x0 &&& (~~~x6))
private def value79 : W := R28.P ((~~~x5) &&& (x0 ||| x1))
private def value80 : W := R28.P ((~~~x1) &&& x6)
private def value81 : W := R28.P ((~~~x1) &&& (x0 ||| x6))
private def value82 : W := R28.P ((~~~x1) &&& (x5 ||| x6))
private def value83 : W := R28.P x0
private def value84 : W := R28.P (x0 ||| (x1 &&& (~~~x5)))
private def value85 : W := R28.P (x0 ||| ((~~~x1) &&& x6))
private def value86 : W := R28.P x1
private def value87 : W := R28.P (x0 ||| x1)
private def value88 : W := R28.P x5
private def value89 : W := R28.P (x5 ||| ((~~~x1) &&& x6))
private def value90 : W := R28.P (x0 ||| x5)
private def value91 : W := R28.P (x1 ||| x5)
private def value92 : W := R28.P x6
private def value93 : W := R29.P x5
private def value94 : W := R29.P (x6 &&& ((~~~x1) ||| x5))
private def value95 : W := R29.P (x5 ||| x6)
private def value96 : W := R30.P (x0 &&& (~~~x6))
private def value97 : W := R30.P (x5 &&& (~~~x6))
private def value98 : W := R30.P (x0 &&& (~~~x5))
private def value99 : W := R30.P ((~~~x5) &&& x6)
private def value100 : W := R30.P ((~~~x5) &&& (x0 ||| x6))
private def value101 : W := R30.P ((~~~x0) &&& x6)
private def value102 : W := R30.P ((~~~x0) &&& (x5 ||| x6))
private def value103 : W := R30.P (x6 &&& ((~~~x0) ||| (~~~x5)))
private def value104 : W := R30.P (x0 &&& x5)
private def value105 : W := R30.P (x5 &&& (x0 ||| (~~~x6)))
private def value106 : W := R30.P x0
private def value107 : W := R30.P x5
private def value108 : W := R30.P (x5 ||| (x0 &&& (~~~x6)))
private def value109 : W := R30.P (x5 ||| ((~~~x0) &&& x6))
private def value110 : W := R30.P x6
private def value111 : W := R36.P (x3 &&& (~~~x6))
private def value112 : W := R36.P (x0 &&& (~~~x3))
private def value113 : W := R36.P ((~~~x0) &&& x1)
private def value114 : W := R36.P ((~~~x0) &&& x4)
private def value115 : W := R36.P x0
private def value116 : W := R36.P x1
private def value117 : W := R36.P x3
private def value118 : W := R36.P x4
private def value119 : W := R36.P (x1 ||| x4)
private def value120 : W := R36.P x6
private def value121 : W := R38.P (x3 &&& (~~~x6))
private def value122 : W := R38.P (x0 &&& (~~~x3))
private def value123 : W := R38.P ((~~~x0) &&& x4)
private def value124 : W := R38.P x0
private def value125 : W := R38.P x3
private def value126 : W := R38.P x4
private def value127 : W := R38.P x6
private def value128 : W := R44.P ((~~~x0) &&& x6)
private def value129 : W := R44.P ((~~~x0) &&& (x1 ||| x6))
private def value130 : W := R44.P ((~~~x0) &&& (x4 ||| x6))
private def value131 : W := R44.P x0
private def value132 : W := R44.P x1
private def value133 : W := R44.P (x1 ||| ((~~~x0) &&& x6))
private def value134 : W := R44.P (x0 ||| x1)
private def value135 : W := R44.P x4
private def value136 : W := R44.P (x4 ||| ((~~~x0) &&& x6))
private def value137 : W := R44.P (x0 ||| x4)
private def value138 : W := R44.P x6
private def value139 : W := R44.P (x6 ||| ((~~~x0) &&& x1))
private def value140 : W := R44.P (x6 ||| ((~~~x0) &&& x4))
private def value141 : W := R45.P (x1 &&& (~~~x6))
private def value142 : W := R45.P (x4 &&& (~~~x6))
private def value143 : W := R45.P (x1 &&& (~~~x4))
private def value144 : W := R45.P ((~~~x4) &&& x6)
private def value145 : W := R45.P ((~~~x4) &&& (x1 ||| x6))
private def value146 : W := R45.P ((~~~x1) &&& x4)
private def value147 : W := R45.P ((~~~x1) &&& x6)
private def value148 : W := R45.P ((~~~x1) &&& (x4 ||| x6))
private def value149 : W := R45.P (x6 &&& ((~~~x1) ||| (~~~x4)))
private def value150 : W := R45.P (x1 &&& (x4 ||| (~~~x6)))
private def value151 : W := R45.P (x4 &&& (x1 ||| (~~~x6)))
private def value152 : W := R45.P x1
private def value153 : W := R45.P (x1 ||| ((~~~x4) &&& x6))
private def value154 : W := R45.P x4
private def value155 : W := R45.P (x4 ||| ((~~~x1) &&& x6))
private def value156 : W := R45.P x6
private def value157 : W := R45.P (x1 ||| (x4 ||| x6))
private def value158 : W := R52.P (x3 &&& (~~~x6))
private def value159 : W := R52.P (x0 &&& (~~~x3))
private def value160 : W := R52.P ((~~~x0) &&& x1)
private def value161 : W := R52.P x0
private def value162 : W := R52.P x1
private def value163 : W := R52.P x3
private def value164 : W := R52.P x6
private def value165 : W := R84.P ((~~~x5) &&& (x0 ||| x1))
private def value166 : W := R84.P ((x0 &&& (~~~x5)) ||| ((~~~x0) &&& (x1 ||| x5)))
private def value167 : W := R84.P x0
private def value168 : W := R84.P x3
private def value169 : W := R86.P (x0 &&& (~~~x5))
private def value170 : W := R86.P (x3 &&& (~~~x5))
private def value171 : W := R86.P (x0 &&& (~~~x3))
private def value172 : W := R86.P ((~~~x3) &&& x5)
private def value173 : W := R86.P ((~~~x3) &&& (x0 ||| x5))
private def value174 : W := R86.P ((x5 &&& (~~~x3)) ||| ((~~~x5) &&& x0))
private def value175 : W := R86.P ((~~~x0) &&& x3)
private def value176 : W := R86.P ((~~~x0) &&& x5)
private def value177 : W := R86.P x0
private def value178 : W := R86.P (x3 &&& ((~~~x0) ||| x5))
private def value179 : W := R86.P x3
private def value180 : W := R86.P (x3 ||| (x0 &&& (~~~x5)))
private def value181 : W := R86.P x5
private def value182 : W := R205.P x0
private def value183 : W := R205.P x5
private def value184 : W := R205.P (x0 ||| x6)
private def value185 : W := R205.P (x3 ||| x6)
private def value186 : W := R205.P (x5 ||| x6)
private def value187 : W := R208.P x0
private def value188 : W := R208.P x5
private def value189 : W := R208.P (x0 ||| x6)
private def value190 : W := R208.P (x3 ||| x6)
private def value191 : W := R208.P (x5 ||| x6)
private def value192 : W := R343.P (x1 &&& (~~~x6))
private def value193 : W := R343.P (x4 &&& (~~~x6))
private def value194 : W := R343.P (x1 &&& (~~~x4))
private def value195 : W := R343.P ((~~~x4) &&& x6)
private def value196 : W := R343.P ((~~~x4) &&& (x1 ||| x6))
private def value197 : W := R343.P ((~~~x1) &&& x4)
private def value198 : W := R343.P ((~~~x1) &&& x6)
private def value199 : W := R343.P ((~~~x1) &&& (x4 ||| x6))
private def value200 : W := R343.P x1
private def value201 : W := R343.P x4
private def value202 : W := R343.P x6
private def value203 : W := R619.P (x0 &&& (~~~x5))
private def value204 : W := R619.P (x3 &&& (~~~x5))
private def value205 : W := R619.P (x0 &&& (~~~x3))
private def value206 : W := R619.P ((~~~x3) &&& x5)
private def value207 : W := R619.P ((~~~x3) &&& (x0 ||| x5))
private def value208 : W := R619.P ((~~~x0) &&& x3)
private def value209 : W := R619.P ((~~~x0) &&& x5)
private def value210 : W := R619.P x0
private def value211 : W := R619.P x3
private def value212 : W := R619.P x5
private def value213 : W := R622.P (x0 &&& (~~~x5))
private def value214 : W := R622.P (x3 &&& (~~~x5))
private def value215 : W := R622.P (x0 &&& (~~~x3))
private def value216 : W := R622.P ((~~~x3) &&& x5)
private def value217 : W := R622.P ((~~~x3) &&& (x0 ||| x5))
private def value218 : W := R622.P ((~~~x0) &&& x3)
private def value219 : W := R622.P ((~~~x0) &&& x5)
private def value220 : W := R622.P x0
private def value221 : W := R622.P x3
private def value222 : W := R622.P x5
private def value223 : W := R1014.P x1
private def value224 : W := R1014.P x0
private def value225 : W := R1014.P x4
private def value226 : W := R1014.P x6
private def value227 : W := R1020.P (x3 &&& (~~~x6))
private def value228 : W := R1020.P (~~~x4)
private def value229 : W := R1020.P (x0 &&& (~~~x3))
private def value230 : W := R1020.P x0
private def value231 : W := R1020.P (x0 ||| (~~~x4))
private def value232 : W := R1020.P x3
private def value233 : W := R1020.P x6
private def value234 : W := R1033.P (x0 &&& (~~~x1))
private def value235 : W := R1033.P x1
private def value236 : W := R1033.P x3
private def value237 : W := R1033.P x4
private def value238 : W := R1035.P ((~~~x0) &&& x6)
private def value239 : W := R1035.P x1
private def value240 : W := R1035.P x0
private def value241 : W := R1035.P x4
private def value242 : W := R1035.P x6
private def value243 : W := R1037.P ((~~~x0) &&& (~~~x4))
private def value244 : W := R1037.P ((~~~x4) &&& x6)
private def value245 : W := R1037.P ((~~~x0) &&& (~~~x1))
private def value246 : W := R1037.P ((~~~x1) &&& x6)
private def value247 : W := R1037.P (~~~x0)
private def value248 : W := R1037.P x1
private def value249 : W := R1037.P ((~~~x0) ||| x1)
private def value250 : W := R1037.P x4
private def value251 : W := R1037.P ((~~~x0) ||| x4)
private def value252 : W := R1037.P x6
private def value253 : W := R1038.P (x3 &&& (~~~x6))
private def value254 : W := R1038.P (x0 &&& (~~~x3))
private def value255 : W := R1038.P (~~~x1)
private def value256 : W := R1038.P x0
private def value257 : W := R1038.P (x0 ||| (~~~x1))
private def value258 : W := R1038.P x3
private def value259 : W := R1038.P x6
private def value260 : W := R1039.P x1
private def value261 : W := R1039.P x3
private def value262 : W := R1039.P x4
private def value263 : W := R1039.P ((~~~x0) ||| x4)
private def value264 : W := R1045.P (x0 &&& (~~~x4))
private def value265 : W := R1045.P x1
private def value266 : W := R1045.P x3
private def value267 : W := R1045.P x4
private def value268 : W := R1047.P x1
private def value269 : W := R1047.P ((~~~x0) ||| x1)
private def value270 : W := R1047.P x3
private def value271 : W := R1047.P x4
private def value272 : W := R1058.P x1
private def value273 : W := R1058.P ((~~~x4) &&& x6)
private def value274 : W := R1058.P x0
private def value275 : W := R1058.P x4
private def value276 : W := R1058.P ((~~~x1) &&& x6)
private def value277 : W := R1064.P x4
private def value278 : W := R1064.P x0
private def value279 : W := R1064.P x1
private def value280 : W := R1064.P x6
private def value281 : W := R1065.P ((~~~x0) &&& x6)
private def value282 : W := R1065.P x1
private def value283 : W := R1065.P x4
private def value284 : W := R1065.P x0
private def value285 : W := R1065.P x6
private def value286 : W := R1109.P x1
private def value287 : W := R1109.P x4
private def value288 : W := R1109.P x0
private def value289 : W := R1109.P x6
private def value290 : W := R1116.P (~~~x0)
private def value291 : W := R1116.P x1
private def value292 : W := R1116.P x3
private def value293 : W := R1116.P x6
private def value294 : W := R1118.P x1
private def value295 : W := R1118.P x3
private def value296 : W := R1118.P x0
private def value297 : W := R1118.P x5
private def value298 : W := R1118.P (x4 ||| x5)
private def value299 : W := R1131.P x3
private def value300 : W := R1131.P (x0 &&& (x4 ||| x5))
private def value301 : W := R1131.P x0
private def value302 : W := R1131.P x5
private def value303 : W := R1132.P x3
private def value304 : W := R1132.P x0
private def value305 : W := R1132.P (x3 ||| x5)
private def value306 : W := R1132.P (x4 ||| x5)
private def value307 : W := R1147.P x3
private def value308 : W := R1147.P x0
private def value309 : W := R1147.P x5
private def value310 : W := R1147.P (x4 ||| x5)
private def value311 : W := R1153.P x3
private def value312 : W := R1153.P x0
private def value313 : W := R1153.P x5
private def value314 : W := R1153.P (x4 ||| x5)
private def value315 : W := R1160.P x3
private def value316 : W := R1160.P x0
private def value317 : W := R1160.P x5
private def value318 : W := R1160.P (x4 ||| x5)
private def value319 : W := R1167.P x3
private def value320 : W := R1167.P x0
private def value321 : W := R1167.P x5
private def value322 : W := R1167.P (x4 ||| x5)
private def value323 : W := R1170.P x3
private def value324 : W := R1170.P x0
private def value325 : W := R1170.P x5
private def value326 : W := R1177.P x3
private def value327 : W := R1177.P x0
private def value328 : W := R1177.P x5
private def value329 : W := R1177.P (x4 ||| x5)
private def value330 : W := R1184.P x3
private def value331 : W := R1184.P x0
private def value332 : W := R1184.P x5
private def value333 : W := R1184.P (x4 ||| x5)
private def value334 : W := R1203.P x0
private def value335 : W := R1203.P x3
private def value336 : W := R1203.P (x4 ||| x5)
private def value337 : W := R1204.P x3
private def value338 : W := R1204.P x0
private def value339 : W := R1204.P x5
private def value340 : W := R1204.P (x4 ||| x5)
private def value341 : W := R1206.P (~~~x3)
private def value342 : W := R1206.P x0
private def value343 : W := R1206.P x5
private def value344 : W := R1214.P x3
private def value345 : W := R1214.P x0
private def value346 : W := R1214.P x5
private def value347 : W := R1214.P (x4 ||| x5)
private def value348 : W := R1215.P (~~~x4)
private def value349 : W := R1215.P ((~~~x1) &&& x5)
private def value350 : W := R1215.P x0
private def value351 : W := R1215.P (x0 ||| (~~~x4))
private def value352 : W := R1215.P x1
private def value353 : W := R1215.P x5
private def value354 : W := R1216.P x0
private def value355 : W := R1216.P x3
private def value356 : W := R1216.P x1
private def value357 : W := R1216.P x6
private def value358 : W := R1220.P (~~~x4)
private def value359 : W := R1220.P x0
private def value360 : W := R1220.P x3
private def value361 : W := R1220.P x5
private def value362 : W := R1220.P (x0 ||| x5)
private def value363 : W := R1220.P x6
private def value364 : W := R1230.P ((~~~x4) &&& (~~~x5))
private def value365 : W := R1230.P ((~~~x5) &&& x6)
private def value366 : W := R1230.P ((~~~x0) &&& (~~~x4))
private def value367 : W := R1230.P (~~~x4)
private def value368 : W := R1230.P ((~~~x0) &&& x6)
private def value369 : W := R1230.P x0
private def value370 : W := R1230.P (x0 ||| (~~~x4))
private def value371 : W := R1230.P x5
private def value372 : W := R1230.P ((~~~x4) ||| x5)
private def value373 : W := R1230.P (x0 ||| x5)
private def value374 : W := R1230.P x6
private def value375 : W := R1231.P (~~~x4)
private def value376 : W := R1231.P x3
private def value377 : W := R1231.P x5
private def value378 : W := R1231.P x6
private def value379 : W := R1251.P (~~~x4)
private def value380 : W := R1251.P (~~~x0)
private def value381 : W := R1251.P x3
private def value382 : W := R1251.P x6
private def value383 : W := R1269.P (~~~x4)
private def value384 : W := R1269.P x0
private def value385 : W := R1269.P x5
private def value386 : W := R1269.P x6
private def value387 : W := R1270.P (~~~x0)
private def value388 : W := R1270.P x5
private def value389 : W := R1270.P x6
private def value390 : W := R1277.P (~~~x4)
private def value391 : W := R1277.P x3
private def value392 : W := R1277.P (x0 ||| x5)
private def value393 : W := R1277.P x6
private def value394 : W := R1291.P (~~~x4)
private def value395 : W := R1291.P (~~~x3)
private def value396 : W := R1291.P x5
private def value397 : W := R1291.P x6
private def value398 : W := R1311.P ((~~~x4) ||| x5)
private def value399 : W := R1311.P x0
private def value400 : W := R1311.P x6
private def value401 : W := R1323.P (x0 ||| (~~~x4))
private def value402 : W := R1323.P x5
private def value403 : W := R1323.P x6
private def value404 : W := R1363.P ((~~~x4) &&& (~~~x5))
private def value405 : W := R1363.P ((~~~x1) &&& (~~~x5))
private def value406 : W := R1363.P (~~~x5)
private def value407 : W := R1363.P ((~~~x4) &&& x6)
private def value408 : W := R1363.P ((~~~x1) &&& x6)
private def value409 : W := R1363.P x1
private def value410 : W := R1363.P (x1 ||| (~~~x5))
private def value411 : W := R1363.P x4
private def value412 : W := R1363.P (x4 ||| (~~~x5))
private def value413 : W := R1363.P x6
private def value414 : W := R1364.P ((~~~x0) &&& x6)
private def value415 : W := R1364.P x1
private def value416 : W := R1364.P (x1 ||| ((~~~x0) &&& x6))
private def value417 : W := R1364.P (x0 ||| x1)
private def value418 : W := R1364.P x4
private def value419 : W := R1364.P (x4 ||| ((~~~x0) &&& x6))
private def value420 : W := R1364.P (x0 ||| x4)
private def value421 : W := R1364.P x6
private def value422 : W := R1371.P (x4 &&& (~~~x5))
private def value423 : W := R1371.P (~~~x0)
private def value424 : W := R1371.P x1
private def value425 : W := R1371.P ((~~~x0) ||| x1)
private def value426 : W := R1371.P x4
private def value427 : W := R1371.P x5
private def value428 : W := R1371.P ((~~~x0) ||| x5)
private def value429 : W := R1406.P x0
private def value430 : W := R1406.P x1
private def value431 : W := R1406.P x5
private def value432 : W := R1406.P x6
private def value433 : W := R1407.P (~~~x0)
private def value434 : W := R1407.P x1
private def value435 : W := R1407.P x4
private def value436 : W := R1407.P x6
private def value437 : W := R1410.P (x1 &&& (~~~x5))
private def value438 : W := R1410.P (~~~x0)
private def value439 : W := R1410.P x1
private def value440 : W := R1410.P x4
private def value441 : W := R1410.P ((~~~x0) ||| x4)
private def value442 : W := R1410.P x5
private def value443 : W := R1434.P ((~~~x1) &&& (~~~x5))
private def value444 : W := R1434.P ((~~~x5) &&& x6)
private def value445 : W := R1434.P ((~~~x0) &&& (~~~x1))
private def value446 : W := R1434.P (~~~x1)
private def value447 : W := R1434.P ((~~~x0) &&& x6)
private def value448 : W := R1434.P x0
private def value449 : W := R1434.P (x0 ||| (~~~x1))
private def value450 : W := R1434.P x5
private def value451 : W := R1434.P ((~~~x1) ||| x5)
private def value452 : W := R1434.P (x0 ||| x5)
private def value453 : W := R1434.P x6
private def value454 : W := R1442.P ((~~~x4) &&& x5)
private def value455 : W := R1442.P (~~~x1)
private def value456 : W := R1442.P x0
private def value457 : W := R1442.P (x0 ||| (~~~x1))
private def value458 : W := R1442.P x4
private def value459 : W := R1442.P x5
private def value460 : W := R1459.P (~~~x1)
private def value461 : W := R1459.P x0
private def value462 : W := R1459.P x5
private def value463 : W := R1459.P x6
private def value464 : W := R1497.P (~~~x0)
private def value465 : W := R1497.P x1
private def value466 : W := R1497.P x4
private def value467 : W := R1497.P x6
private def value468 : W := R1503.P x0
private def value469 : W := R1503.P x4
private def value470 : W := R1503.P x5
private def value471 : W := R1503.P x6
private def value472 : W := R1550.P (~~~x4)
private def value473 : W := R1550.P x0
private def value474 : W := R1550.P x5
private def value475 : W := R1550.P x6
private def value476 : W := R1568.P ((~~~x0) &&& (~~~x5))
private def value477 : W := R1568.P (x5 ||| ((~~~x0) &&& (~~~x1)))
private def value478 : W := R1568.P x6
private def value479 : W := R1582.P (x1 &&& (~~~x5))
private def value480 : W := R1582.P (~~~x3)
private def value481 : W := R1582.P x1
private def value482 : W := R1582.P x5
private def value483 : W := R1582.P x6
private def value484 : W := R1595.P x4
private def value485 : W := R1595.P x0
private def value486 : W := R1595.P x1
private def value487 : W := R1595.P x5
private def value488 : W := R1595.P (x0 ||| x5)
private def value489 : W := R1595.P x6
private def value490 : W := R1608.P x4
private def value491 : W := R1608.P x1
private def value492 : W := R1608.P x5
private def value493 : W := R1608.P x6
private def value494 : W := R1622.P x4
private def value495 : W := R1622.P (~~~x5)
private def value496 : W := R1622.P x1
private def value497 : W := R1622.P x6
private def value498 : W := R1631.P x4
private def value499 : W := R1631.P (~~~x0)
private def value500 : W := R1631.P x1
private def value501 : W := R1631.P x6
private def value502 : W := R1652.P x4
private def value503 : W := R1652.P x1
private def value504 : W := R1652.P (x0 ||| x5)
private def value505 : W := R1652.P x6
private def value506 : W := R1672.P x0
private def value507 : W := R1672.P x5
private def value508 : W := R1672.P (~~~x4)
private def value509 : W := R1699.P (x3 &&& (~~~x6))
private def value510 : W := R1699.P (~~~x5)
private def value511 : W := R1699.P x1
private def value512 : W := R1699.P x4
private def value513 : W := R1699.P x6
private def value514 : W := R1699.P (x3 ||| x6)
private def value515 : W := R1735.P (x3 &&& (~~~x6))
private def value516 : W := R1735.P (~~~x0)
private def value517 : W := R1735.P x1
private def value518 : W := R1735.P x3
private def value519 : W := R1735.P x4
private def value520 : W := R1735.P x6
private def value521 : W := R1735.P (x3 ||| x6)
private def value522 : W := R1787.P x1
private def value523 : W := R1787.P x0
private def value524 : W := R1787.P x4
private def value525 : W := R1787.P x6
private def value526 : W := R1826.P (~~~x0)
private def value527 : W := R1826.P x1
private def value528 : W := R1826.P x4
private def value529 : W := R1826.P x6
private def value530 : W := R1836.P (~~~x3)
private def value531 : W := R1836.P x1
private def value532 : W := R1836.P x4
private def value533 : W := R1836.P x5
private def value534 : W := R1836.P x6
private def value535 : W := R1846.P (~~~x3)
private def value536 : W := R1846.P x4
private def value537 : W := R1846.P x5
private def value538 : W := R1846.P x6
private def value539 : W := R1873.P (~~~x3)
private def value540 : W := R1873.P (x1 ||| x4)
private def value541 : W := R1873.P x5
private def value542 : W := R1873.P x6
private def value543 : W := R1886.P (~~~x3)
private def value544 : W := R1886.P (~~~x1)
private def value545 : W := R1886.P x5
private def value546 : W := R1886.P x6
private def value547 : W := R1934.P (~~~x5)
private def value548 : W := R1934.P x1
private def value549 : W := R1934.P x4
private def value550 : W := R1934.P x6
private def value551 : W := R1939.P x0
private def value552 : W := R1939.P x1
private def value553 : W := R1939.P x3
private def value554 : W := R1939.P x4
private def value555 : W := R1939.P x6
private def value556 : W := R1948.P (x3 &&& (~~~x6))
private def value557 : W := R1948.P ((~~~x0) &&& x1)
private def value558 : W := R1948.P x0
private def value559 : W := R1948.P x1
private def value560 : W := R1948.P (x1 ||| (x3 &&& (~~~x6)))
private def value561 : W := R1948.P x3
private def value562 : W := R1948.P x6
private def value563 : W := R1948.P (x1 ||| x6)
private def value564 : W := R1949.P (x3 &&& (~~~x6))
private def value565 : W := R1949.P x1
private def value566 : W := R1949.P x4
private def value567 : W := R1949.P x6
private def value568 : W := R1959.P x0
private def value569 : W := R1959.P x3
private def value570 : W := R1959.P x4
private def value571 : W := R1959.P x6
private def value572 : W := R1966.P x0
private def value573 : W := R1966.P x1
private def value574 : W := R1966.P x6
private def value575 : W := R1967.P (x3 &&& (~~~x6))
private def value576 : W := R1967.P x0
private def value577 : W := R1967.P x1
private def value578 : W := R2011.P x0
private def value579 : W := R2011.P x1
private def value580 : W := R2011.P x3
private def value581 : W := R2011.P x6
private def value582 : W := R2012.P x0
private def value583 : W := R2012.P x1
private def value584 : W := R2012.P x6
private def value585 : W := R2020.P x3
private def value586 : W := R2020.P x0
private def value587 : W := R2020.P x4
private def value588 : W := R2020.P x6
private def value589 : W := R2046.P x0
private def value590 : W := R2046.P x1
private def value591 : W := R2046.P x4
private def value592 : W := R2046.P x5
private def value593 : W := R2046.P x6
private def value594 : W := R2046.P x3
private def value595 : W := R2077.P (~~~x0)
private def value596 : W := R2077.P x3
private def value597 : W := R2077.P x4
private def value598 : W := R2077.P x6
private def value599 : W := R2092.P x0
private def value600 : W := R2092.P x1
private def value601 : W := R2092.P x3
private def value602 : W := R2092.P x4
private def value603 : W := R2092.P x6
private def value604 : W := R2102.P x1
private def value605 : W := R2102.P x4
private def value606 : W := R2102.P ((~~~x0) &&& x6)
private def value607 : W := R2102.P x6
private def value608 : W := R2103.P x0
private def value609 : W := R2103.P x3
private def value610 : W := R2103.P x4
private def value611 : W := R2103.P x6
private def value612 : W := R2105.P x1
private def value613 : W := R2105.P x4
private def value614 : W := R2105.P (x0 ||| x4)
private def value615 : W := R2105.P x6
private def value616 : W := R2117.P x1
private def value617 : W := R2117.P x3
private def value618 : W := R2117.P (~~~x0)
private def value619 : W := R2126.P x0
private def value620 : W := R2126.P x3
private def value621 : W := R2126.P x4
private def value622 : W := R2126.P x6
private def value623 : W := R2143.P x1
private def value624 : W := R2143.P x0
private def value625 : W := R2143.P x4
private def value626 : W := R2143.P x6
private def value627 : W := R2188.P (~~~x1)
private def value628 : W := R2188.P x0
private def value629 : W := R2188.P x3
private def value630 : W := R2188.P x4
private def value631 : W := R2188.P x5
private def value632 : W := R2188.P x6
private def value633 : W := R2189.P x0
private def value634 : W := R2189.P x3
private def value635 : W := R2189.P x5
private def value636 : W := R2189.P (x5 ||| ((~~~x0) &&& (~~~x1)))
private def value637 : W := R2223.P x1
private def value638 : W := R2223.P x0
private def value639 : W := R2223.P x4
private def value640 : W := R2223.P x5
private def value641 : W := R2223.P (x0 ||| x5)
private def value642 : W := R2223.P x6
private def value643 : W := R2235.P x1
private def value644 : W := R2235.P x4
private def value645 : W := R2235.P x5
private def value646 : W := R2235.P x6
private def value647 : W := R2249.P x1
private def value648 : W := R2249.P (~~~x0)
private def value649 : W := R2249.P x4
private def value650 : W := R2249.P x6
private def value651 : W := R2286.P x1
private def value652 : W := R2286.P x4
private def value653 : W := R2286.P (x0 ||| x5)
private def value654 : W := R2286.P x6
private def value655 : W := R2301.P x0
private def value656 : W := R2301.P x5
private def value657 : W := R2301.P (~~~x1)
private def value658 : W := R2303.P x1
private def value659 : W := R2303.P (~~~x5)
private def value660 : W := R2303.P x4
private def value661 : W := R2303.P x6
private def value662 : W := R2314.P (~~~x1)
private def value663 : W := R2314.P x3
private def value664 : W := R2314.P x5
private def value665 : W := R2314.P x6
private def value666 : W := R2319.P x1
private def value667 : W := R2319.P x4
private def value668 : W := R2319.P x5
private def value669 : W := R2319.P x6
private def value670 : W := R2322.P (~~~x1)
private def value671 : W := R2322.P x0
private def value672 : W := R2322.P x3
private def value673 : W := R2322.P x5
private def value674 : W := R2322.P (x0 ||| x5)
private def value675 : W := R2322.P x6
private def value676 : W := R2330.P (~~~x1)
private def value677 : W := R2330.P (~~~x0)
private def value678 : W := R2330.P x3
private def value679 : W := R2330.P x6
private def value680 : W := R2341.P (~~~x0)
private def value681 : W := R2341.P x5
private def value682 : W := R2341.P x6
private def value683 : W := R2343.P (x0 ||| (~~~x1))
private def value684 : W := R2343.P x5
private def value685 : W := R2343.P x6
private def value686 : W := R2379.P ((~~~x1) ||| x5)
private def value687 : W := R2379.P x0
private def value688 : W := R2379.P x6
private def value689 : W := R2395.P (~~~x1)
private def value690 : W := R2395.P x0
private def value691 : W := R2395.P x5
private def value692 : W := R2395.P x6
private def value693 : W := R2399.P (~~~x1)
private def value694 : W := R2399.P x3
private def value695 : W := R2399.P (x0 ||| x5)
private def value696 : W := R2399.P x6
private def value697 : W := R2418.P (~~~x3)
private def value698 : W := R2418.P x0
private def value699 : W := R2418.P x1
private def value700 : W := R2418.P x4
private def value701 : W := R2418.P x5
private def value702 : W := R2418.P x6
private def value703 : W := R2454.P x0
private def value704 : W := R2454.P x1
private def value705 : W := R2454.P x3
private def value706 : W := R2454.P x4
private def value707 : W := R2454.P x6
private def value708 : W := R2465.P x0
private def value709 : W := R2465.P x1
private def value710 : W := R2465.P x3
private def value711 : W := R2465.P x6
private def value712 : W := R2466.P x1
private def value713 : W := R2466.P ((~~~x0) &&& x6)
private def value714 : W := R2466.P x4
private def value715 : W := R2466.P x6
private def value716 : W := R2467.P x1
private def value717 : W := R2467.P (x0 ||| x1)
private def value718 : W := R2467.P x4
private def value719 : W := R2467.P x6
private def value720 : W := R2470.P (~~~x0)
private def value721 : W := R2470.P x3
private def value722 : W := R2470.P x4
private def value723 : W := R2524.P x0
private def value724 : W := R2524.P x1
private def value725 : W := R2524.P x3
private def value726 : W := R2524.P x6
private def value727 : W := R2538.P x4
private def value728 : W := R2538.P x0
private def value729 : W := R2538.P x1
private def value730 : W := R2538.P x6
private def value731 : W := R2552.P x0
private def value732 : W := R2552.P x3
private def value733 : W := R2552.P x1
private def value734 : W := R2552.P x5
private def value735 : W := R2552.P x6
private def value736 : W := R2561.P ((~~~x5) &&& (x0 ||| x1))
private def value737 : W := R2561.P x0
private def value738 : W := R2561.P x3
private def value739 : W := R2561.P x5
private def value740 : W := R2562.P x3
private def value741 : W := R2562.P x1
private def value742 : W := R2562.P x5
private def value743 : W := R2562.P x6
private def value744 : W := R2569.P x0
private def value745 : W := R2569.P x1
private def value746 : W := R2569.P x5
private def value747 : W := R2584.P ((~~~x5) &&& x6)
private def value748 : W := R2584.P ((~~~x0) &&& x6)
private def value749 : W := R2589.P x3
private def value750 : W := R2589.P x1
private def value751 : W := R2589.P (x0 ||| x5)
private def value752 : W := R2589.P x6
private def value753 : W := R2607.P x5
private def value754 : W := R2607.P x0
private def value755 : W := R2607.P x1
private def value756 : W := R2607.P x3
private def value757 : W := R2607.P x6
private def value758 : W := R2619.P x5
private def value759 : W := R2619.P x0
private def value760 : W := R2619.P x1
private def value761 : W := R2619.P ((~~~x5) &&& (x0 ||| x1))
private def value762 : W := R2619.P x6
private def value763 : W := R2623.P x5
private def value764 : W := R2623.P x0
private def value765 : W := R2623.P x3
private def value766 : W := R2623.P (x5 ||| x6)
private def value767 : W := R2656.P x5
private def value768 : W := R2656.P x0
private def value769 : W := R2656.P x1
private def value770 : W := R2656.P x6
private def value771 : W := R2659.P x1
private def value772 : W := R2659.P x3
private def value773 : W := R2659.P (~~~x5)
private def value774 : W := R2685.P x0
private def value775 : W := R2685.P x3
private def value776 : W := R2685.P x4
private def value777 : W := R2685.P x5
private def value778 : W := R2685.P x6
private def value779 : W := R2693.P (x4 &&& (~~~x5))
private def value780 : W := R2693.P x0
private def value781 : W := R2693.P x3
private def value782 : W := R2693.P x5
private def value783 : W := R2695.P (x4 &&& (~~~x5))
private def value784 : W := R2695.P x0
private def value785 : W := R2695.P x4
private def value786 : W := R2695.P x5
private def value787 : W := R2695.P (x0 ||| x5)
private def value788 : W := R2695.P x6
private def value789 : W := R2716.P x3
private def value790 : W := R2716.P x0
private def value791 : W := R2716.P x5
private def value792 : W := R2737.P x0
private def value793 : W := R2737.P x3
private def value794 : W := R2737.P x5
private def value795 : W := R2742.P x0
private def value796 : W := R2742.P x4
private def value797 : W := R2742.P x5
private def value798 : W := R2742.P x6
private def value799 : W := R2750.P x4
private def value800 : W := R2750.P x3
private def value801 : W := R2750.P x5
private def value802 : W := R2750.P x6
private def value803 : W := R2756.P x4
private def value804 : W := R2756.P x3
private def value805 : W := R2756.P x5
private def value806 : W := R2756.P x6
private def value807 : W := R2766.P (x4 &&& (~~~x5))
private def value808 : W := R2766.P x0
private def value809 : W := R2766.P x6
private def value810 : W := R2782.P (x1 &&& (~~~x5))
private def value811 : W := R2782.P (~~~x0)
private def value812 : W := R2782.P x3
private def value813 : W := R2782.P x4
private def value814 : W := R2782.P x5
private def value815 : W := R2823.P ((~~~x5) &&& (x0 ||| x1))
private def value816 : W := R2823.P x0
private def value817 : W := R2823.P x6
private def value818 : W := R2841.P (x0 &&& (~~~x6))
private def value819 : W := R2841.P ((~~~x5) &&& (x0 ||| x1))
private def value820 : W := R2841.P x6
private def value821 : W := R2844.P (x0 ||| (x1 &&& (~~~x5)))
private def value822 : W := R2844.P x5
private def value823 : W := R2844.P x6
private def value824 : W := R2855.P ((~~~x5) &&& (x0 ||| x1))
private def value825 : W := R2855.P x0
private def value826 : W := R2855.P x6
private def value827 : W := R2857.P (x1 &&& (~~~x5))
private def value828 : W := R2857.P x3
private def value829 : W := R2857.P x5
private def value830 : W := R2857.P x6
private def value831 : W := R2901.P (x5 &&& (~~~x6))
private def value832 : W := R2901.P x0
private def value833 : W := R2901.P x3
private def value834 : W := R2901.P x5
private def value835 : W := R2901.P (x0 ||| x6)
private def value836 : W := R2901.P (x3 ||| x6)
private def value837 : W := R2939.P x0
private def value838 : W := R2939.P ((~~~x5) &&& (x0 ||| x1))
private def value839 : W := R2939.P x6
private def value840 : W := R2939.P (x3 ||| x6)
private def value841 : W := R2958.P ((~~~x5) &&& (x0 ||| x1))
private def value842 : W := R2958.P x0
private def value843 : W := R2958.P x3
private def value844 : W := R2958.P x5
private def value845 : W := R2963.P (x1 &&& (~~~x5))
private def value846 : W := R2963.P x0
private def value847 : W := R2963.P x3
private def value848 : W := R2963.P x5
private def value849 : W := R2970.P (x1 &&& (~~~x5))
private def value850 : W := R2970.P x0
private def value851 : W := R2970.P x3
private def value852 : W := R2970.P x5
private def value853 : W := R2977.P x3
private def value854 : W := R2977.P x4
private def value855 : W := R2977.P x5
private def value856 : W := R2977.P x6
private def value857 : W := R2985.P (x1 &&& (~~~x5))
private def value858 : W := R2985.P (~~~x0)
private def value859 : W := R2985.P ((~~~x0) ||| (x1 &&& (~~~x5)))
private def value860 : W := R2985.P x3
private def value861 : W := R2985.P x5
private def value862 : W := R2999.P (x1 &&& (~~~x5))
private def value863 : W := R2999.P x3
private def value864 : W := R2999.P x4
private def value865 : W := R2999.P (~~~x0)
private def value866 : W := R3011.P (~~~x0)
private def value867 : W := R3011.P x3
private def value868 : W := R3011.P x5
private def value869 : W := R3033.P (~~~x5)
private def value870 : W := R3033.P x1
private def value871 : W := R3033.P x4
private def value872 : W := R3033.P x6
private def value873 : W := R3071.P ((~~~x4) &&& x6)
private def value874 : W := R3071.P x0
private def value875 : W := R3071.P x4
private def value876 : W := R3071.P ((~~~x1) &&& x6)
private def value877 : W := R3072.P ((~~~x1) &&& ((~~~x4) &&& x6))
private def value878 : W := R3072.P ((~~~x4) &&& x6)
private def value879 : W := R3072.P x0
private def value880 : W := R3072.P (x0 ||| x1)
private def value881 : W := R3072.P ((~~~x1) &&& x6)
private def value882 : W := R3072.P (x0 ||| x4)
private def value883 : W := R3072.P x5
private def value884 : W := R3072.P (x1 ||| x5)
private def value885 : W := R3072.P (x4 ||| x5)
private def value886 : W := R3072.P x6
private def value887 : W := R3073.P ((~~~x4) &&& x6)
private def value888 : W := R3073.P ((~~~x1) &&& x6)
private def value889 : W := R3082.P x1
private def value890 : W := R3082.P ((~~~x4) &&& x6)
private def value891 : W := R3082.P x0
private def value892 : W := R3082.P ((~~~x1) &&& x6)
private def value893 : W := R3087.P (~~~x4)
private def value894 : W := R3087.P x0
private def value895 : W := R3087.P x5
private def value896 : W := R3087.P x6
private def value897 : W := R3091.P (~~~x0)
private def value898 : W := R3091.P x1
private def value899 : W := R3091.P x4
private def value900 : W := R3091.P x6
private def value901 : W := R3099.P x1
private def value902 : W := R3099.P (x0 ||| x1)
private def value903 : W := R3099.P x4
private def value904 : W := R3099.P ((~~~x0) &&& x6)
private def value905 : W := R3099.P (x0 ||| x4)
private def value906 : W := R3099.P x6
private def value907 : W := R3117.P (~~~x4)
private def value908 : W := R3117.P x0
private def value909 : W := R3117.P x5
private def value910 : W := R3117.P x6
private def value911 : W := R3142.P x0
private def value912 : W := R3142.P x1
private def value913 : W := R3142.P x4
private def value914 : W := R3142.P x6
private def value915 : W := R3145.P x0
private def value916 : W := R3145.P x5
private def value917 : W := R3145.P ((~~~x4) &&& x6)
private def value918 : W := R3145.P x6
private def value919 : W := R3172.P ((~~~x4) &&& x6)
private def value920 : W := R3172.P x0
private def value921 : W := R3172.P x5
private def value922 : W := R3172.P x6
private def value923 : W := R3190.P ((~~~x1) &&& x6)
private def value924 : W := R3190.P x0
private def value925 : W := R3190.P x5
private def value926 : W := R3190.P x6
private def value927 : W := R3216.P x0
private def value928 : W := R3216.P x4
private def value929 : W := R3216.P x5
private def value930 : W := R3216.P x6
private def value931 : W := R3225.P x0
private def value932 : W := R3225.P ((~~~x4) &&& x6)
private def value933 : W := R3225.P x5
private def value934 : W := R3225.P x6
private def value935 : W := R3236.P ((~~~x0) &&& ((~~~x5) &&& x6))
private def value936 : W := R3236.P ((~~~x5) &&& x6)
private def value937 : W := R3236.P x1
private def value938 : W := R3236.P (x0 ||| x1)
private def value939 : W := R3236.P x4
private def value940 : W := R3236.P (x0 ||| x4)
private def value941 : W := R3236.P ((~~~x0) &&& x6)
private def value942 : W := R3236.P (x1 ||| x5)
private def value943 : W := R3236.P (x4 ||| x5)
private def value944 : W := R3236.P x6
private def value945 : W := R3247.P (~~~x1)
private def value946 : W := R3247.P x0
private def value947 : W := R3247.P x5
private def value948 : W := R3247.P x6
private def value949 : W := R3249.P (~~~x5)
private def value950 : W := R3249.P x1
private def value951 : W := R3249.P x4
private def value952 : W := R3249.P x6
private def value953 : W := R3257.P ((~~~x5) &&& x6)
private def value954 : W := R3257.P x1
private def value955 : W := R3257.P x4
private def value956 : W := R3257.P x6
private def value957 : W := R3354.P x4
private def value958 : W := R3354.P ((~~~x5) &&& x6)
private def value959 : W := R3354.P x1
private def value960 : W := R3354.P x6
private def value961 : W := R3355.P x0
private def value962 : W := R3355.P x1
private def value963 : W := R3355.P x5
private def value964 : W := R3355.P x6
private def value965 : W := R3364.P x0
private def value966 : W := R3364.P x4
private def value967 : W := R3364.P x5
private def value968 : W := R3364.P x6
private def value969 : W := R3373.P x1
private def value970 : W := R3373.P ((~~~x5) &&& x6)
private def value971 : W := R3373.P x4
private def value972 : W := R3373.P x6
private def value973 : W := R3415.P x1
private def value974 : W := R3415.P x0
private def value975 : W := R3415.P x4
private def value976 : W := R3415.P x6
private def value977 : W := R3430.P x1
private def value978 : W := R3430.P x0
private def value979 : W := R3430.P x4
private def value980 : W := R3430.P x6
private def value981 : W := R3449.P x0
private def value982 : W := R3449.P x3
private def value983 : W := R3449.P x4
private def value984 : W := R3449.P x5
private def value985 : W := R3449.P (x1 ||| x5)
private def value986 : W := R3458.P (x0 &&& (x1 ||| x5))
private def value987 : W := R3458.P x0
private def value988 : W := R3458.P x3
private def value989 : W := R3458.P x5
private def value990 : W := R3460.P x0
private def value991 : W := R3460.P x3
private def value992 : W := R3460.P (x1 ||| x5)
private def value993 : W := R3460.P (x3 ||| x5)
private def value994 : W := R3467.P x0
private def value995 : W := R3467.P x3
private def value996 : W := R3467.P (x1 ||| x5)
private def value997 : W := R3474.P x0
private def value998 : W := R3474.P x3
private def value999 : W := R3474.P x5
private def value1000 : W := R3474.P (x1 ||| x5)
private def value1001 : W := R3479.P x0
private def value1002 : W := R3479.P x3
private def value1003 : W := R3479.P x5
private def value1004 : W := R3479.P (x1 ||| x5)
private def value1005 : W := R3487.P (~~~x3)
private def value1006 : W := R3487.P x0
private def value1007 : W := R3487.P x5
private def value1008 : W := R3487.P (x1 ||| x5)
private def value1009 : W := R3491.P (~~~x0)
private def value1010 : W := R3491.P x3
private def value1011 : W := R3491.P x5
private def value1012 : W := R3498.P x0
private def value1013 : W := R3498.P x3
private def value1014 : W := R3498.P x5
private def value1015 : W := R3498.P (x1 ||| x5)
private def value1016 : W := R3500.P x0
private def value1017 : W := R3500.P x3
private def value1018 : W := R3500.P x5
private def value1019 : W := R3500.P (x1 ||| x5)
private def value1020 : W := R3508.P x0
private def value1021 : W := R3508.P x3
private def value1022 : W := R3508.P x5
private def value1023 : W := R3508.P (x1 ||| x5)
private def value1024 : W := R3515.P x0
private def value1025 : W := R3515.P x3
private def value1026 : W := R3515.P x5
private def value1027 : W := R3515.P (x1 ||| x5)
private def value1028 : W := R3521.P x0
private def value1029 : W := R3521.P x3
private def value1030 : W := R3521.P x5
private def value1031 : W := R3521.P (x1 ||| x5)
private def value1032 : W := R3526.P x0
private def value1033 : W := R3526.P x3
private def value1034 : W := R3526.P x5
private def value1035 : W := R3568.P x1
private def value1036 : W := R3568.P ((~~~x0) &&& x6)
private def value1037 : W := R3568.P (x0 ||| x1)
private def value1038 : W := R3568.P x4
private def value1039 : W := R3568.P (x0 ||| x4)
private def value1040 : W := R3568.P x6
private def value1041 : W := R3569.P (~~~x0)
private def value1042 : W := R3569.P x1
private def value1043 : W := R3569.P x4
private def value1044 : W := R3569.P x6
private def value1045 : W := R3593.P (~~~x1)
private def value1046 : W := R3593.P x0
private def value1047 : W := R3593.P x5
private def value1048 : W := R3593.P x6
private def value1049 : W := R3620.P x0
private def value1050 : W := R3620.P x1
private def value1051 : W := R3620.P x5
private def value1052 : W := R3620.P x6
private def value1053 : W := R3627.P x0
private def value1054 : W := R3627.P ((~~~x1) &&& x6)
private def value1055 : W := R3627.P x5
private def value1056 : W := R3627.P x6
private def value1057 : W := R3638.P x0
private def value1058 : W := R3638.P x5
private def value1059 : W := R3638.P ((~~~x1) &&& x6)
private def value1060 : W := R3638.P x6
private def value1061 : W := R3640.P x0
private def value1062 : W := R3640.P x4
private def value1063 : W := R3640.P x1
private def value1064 : W := R3640.P x6
private def value1065 : W := R3648.P ((~~~x0) &&& (~~~x5))
private def value1066 : W := R3648.P (~~~x5)
private def value1067 : W := R3648.P ((~~~x0) &&& x6)
private def value1068 : W := R3648.P x0
private def value1069 : W := R3648.P (x0 ||| (~~~x5))
private def value1070 : W := R3648.P x1
private def value1071 : W := R3648.P x4
private def value1072 : W := R3648.P x6
private def value1073 : W := R3668.P (~~~x5)
private def value1074 : W := R3668.P x1
private def value1075 : W := R3668.P x4
private def value1076 : W := R3668.P x6
private def value1077 : W := R3676.P (~~~x0)
private def value1078 : W := R3676.P x1
private def value1079 : W := R3676.P x4
private def value1080 : W := R3676.P x5
private def value1081 : W := R3676.P x6
private def value1082 : W := R3676.P (x5 ||| x6)
private def value1083 : W := R3721.P (~~~x0)
private def value1084 : W := R3721.P x1
private def value1085 : W := R3721.P x3
private def value1086 : W := R3721.P x4
private def value1087 : W := R3721.P x6
private def value1088 : W := R3749.P (~~~x0)
private def value1089 : W := R3749.P x3
private def value1090 : W := R3749.P (x1 ||| x4)
private def value1091 : W := R3749.P x6
private def value1092 : W := R3761.P (~~~x0)
private def value1093 : W := R3761.P x1
private def value1094 : W := R3761.P x4
private def value1095 : W := R3761.P x6
private def value1096 : W := R3854.P x1
private def value1097 : W := R3854.P x4
private def value1098 : W := R3854.P x0
private def value1099 : W := R3854.P x6
private def value1100 : W := R3945.P x3
private def value1101 : W := R3945.P x0
private def value1102 : W := R3945.P x1
private def value1103 : W := R3945.P x4
private def value1104 : W := R3945.P x6
private def value1105 : W := R3953.P x3
private def value1106 : W := R3953.P x0
private def value1107 : W := R3953.P x1
private def value1108 : W := R3953.P x6
private def value1109 : W := R3976.P x3
private def value1110 : W := R3976.P (~~~x1)
private def value1111 : W := R3976.P x0
private def value1112 : W := R3976.P x6
private def value1113 : W := R3984.P x1
private def value1114 : W := R3984.P x4
private def value1115 : W := R3984.P (~~~x3)
private def value1116 : W := R3997.P x3
private def value1117 : W := R3997.P (~~~x4)
private def value1118 : W := R3997.P x0
private def value1119 : W := R3997.P x6
private def value1120 : W := R4010.P x3
private def value1121 : W := R4010.P x0
private def value1122 : W := R4010.P (x1 ||| x4)
private def value1123 : W := R4010.P x6
private def value1124 : W := R4012.P x0
private def value1125 : W := R4012.P x1
private def value1126 : W := R4012.P x4
private def value1127 : W := R4012.P x3
private def value1128 : W := R4012.P x6
private def value1129 : W := R4019.P x0
private def value1130 : W := R4019.P x4
private def value1131 : W := R4019.P x3
private def value1132 : W := R4019.P x6
private def value1133 : W := R4020.P (x3 &&& (~~~x6))
private def value1134 : W := R4020.P x1
private def value1135 : W := R4020.P x4
private def value1136 : W := R4020.P x6
private def value1137 : W := R4039.P x0
private def value1138 : W := R4039.P x4
private def value1139 : W := R4039.P x3
private def value1140 : W := R4039.P x6
private def value1141 : W := R4046.P x0
private def value1142 : W := R4046.P x4
private def value1143 : W := R4046.P x6
private def value1144 : W := R4047.P x0
private def value1145 : W := R4047.P x3
private def value1146 : W := R4047.P x6
private def value1147 : W := R4049.P (x3 &&& (~~~x6))
private def value1148 : W := R4049.P x0
private def value1149 : W := R4049.P x4
private def value1150 : W := R4092.P (x4 &&& (~~~x5))
private def value1151 : W := R4092.P (~~~x0)
private def value1152 : W := R4092.P x1
private def value1153 : W := R4092.P x3
private def value1154 : W := R4092.P x5
private def value1155 : W := R4108.P (x4 &&& (~~~x5))
private def value1156 : W := R4108.P (~~~x0)
private def value1157 : W := R4108.P ((~~~x0) ||| (x4 &&& (~~~x5)))
private def value1158 : W := R4108.P x3
private def value1159 : W := R4108.P x5
private def value1160 : W := R4117.P (~~~x0)
private def value1161 : W := R4117.P x3
private def value1162 : W := R4117.P x5
private def value1163 : W := R4122.P (x4 &&& (~~~x5))
private def value1164 : W := R4122.P x1
private def value1165 : W := R4122.P x3
private def value1166 : W := R4122.P (~~~x0)
private def value1167 : W := R4164.P x0
private def value1168 : W := R4164.P x1
private def value1169 : W := R4164.P x3
private def value1170 : W := R4164.P x5
private def value1171 : W := R4164.P x6
private def value1172 : W := R4170.P (x1 &&& (~~~x5))
private def value1173 : W := R4170.P x0
private def value1174 : W := R4170.P x1
private def value1175 : W := R4170.P x5
private def value1176 : W := R4170.P (x0 ||| x5)
private def value1177 : W := R4170.P x6
private def value1178 : W := R4175.P x0
private def value1179 : W := R4175.P x3
private def value1180 : W := R4175.P x5
private def value1181 : W := R4195.P x0
private def value1182 : W := R4195.P x3
private def value1183 : W := R4195.P x5
private def value1184 : W := R4207.P (x1 &&& (~~~x5))
private def value1185 : W := R4207.P x0
private def value1186 : W := R4207.P x6
private def value1187 : W := R4221.P x1
private def value1188 : W := R4221.P x3
private def value1189 : W := R4221.P x5
private def value1190 : W := R4221.P x6
private def value1191 : W := R4229.P x1
private def value1192 : W := R4229.P x3
private def value1193 : W := R4229.P x5
private def value1194 : W := R4229.P x6
private def value1195 : W := R4234.P x0
private def value1196 : W := R4234.P x1
private def value1197 : W := R4234.P x5
private def value1198 : W := R4234.P x6
private def value1199 : W := R4239.P x0
private def value1200 : W := R4239.P x1
private def value1201 : W := R4239.P x3
private def value1202 : W := R4239.P x5
private def value1203 : W := R4239.P x6
private def value1204 : W := R4252.P x0
private def value1205 : W := R4252.P x3
private def value1206 : W := R4252.P x5
private def value1207 : W := R4252.P (x0 ||| x6)
private def value1208 : W := R4265.P x1
private def value1209 : W := R4265.P x3
private def value1210 : W := R4265.P (~~~x0)
private def value1211 : W := R4274.P x0
private def value1212 : W := R4274.P x1
private def value1213 : W := R4274.P x5
private def value1214 : W := R4274.P x6
private def value1215 : W := R4306.P x0
private def value1216 : W := R4306.P x3
private def value1217 : W := R4306.P x5
private def value1218 : W := R4306.P x6
private def bank0 : Array Query := #[
  ((R29,2,[value93,value94,value95]),0),
  ((R30,2,[value100,value106,value110]),0),
  ((R30,2,[value102,value107,value110]),0),
  ((R30,2,[value106,value107,value110]),0),
  ((R45,2,[value145,value152,value156]),0),
  ((R45,2,[value148,value154,value156]),0),
  ((R45,2,[value152,value154,value156]),0),
  ((R86,2,[value173,value177,value181]),0),
  ((R86,2,[value177,value179,value181]),0),
  ((R343,2,[value196,value200,value202]),0),
  ((R343,2,[value199,value201,value202]),0),
  ((R343,2,[value200,value201,value202]),0),
  ((R619,2,[value207,value210,value212]),0),
  ((R619,2,[value210,value211,value212]),0),
  ((R622,2,[value217,value220,value222]),0),
  ((R622,2,[value220,value221,value222]),0),
  ((R1170,2,[value323,value324,value325]),0),
  ((R1203,2,[value334,value335,value336]),0),
  ((R1206,2,[value341,value342,value343]),0),
  ((R1270,2,[value387,value388,value389]),0),
  ((R1311,2,[value398,value399,value400]),0),
  ((R1323,2,[value401,value402,value403]),0),
  ((R1568,2,[value476,value477,value478]),0),
  ((R1967,2,[value575,value576,value577]),0),
  ((R2012,2,[value582,value583,value584]),0),
  ((R2117,2,[value616,value617,value618]),0),
  ((R2341,2,[value680,value681,value682]),0),
  ((R2343,2,[value683,value684,value685]),0),
  ((R2379,2,[value686,value687,value688]),0),
  ((R2470,2,[value720,value721,value722]),0),
  ((R2584,2,[value747,value748]),0),
  ((R2619,2,[value759,value761,value762]),0)]
private def bank1 : Array Query := #[
  ((R2659,2,[value771,value772,value773]),0),
  ((R2737,2,[value792,value793,value794]),0),
  ((R2766,2,[value807,value808,value809]),0),
  ((R2823,2,[value815,value816,value817]),0),
  ((R2841,2,[value818,value819,value820]),0),
  ((R2844,2,[value821,value822,value823]),0),
  ((R2855,2,[value824,value825,value826]),0),
  ((R3011,2,[value866,value867,value868]),0),
  ((R3073,2,[value887,value888]),0),
  ((R3467,2,[value994,value995,value996]),0),
  ((R3491,2,[value1009,value1010,value1011]),0),
  ((R3526,2,[value1032,value1033,value1034]),0),
  ((R4046,2,[value1141,value1142,value1143]),0),
  ((R4049,2,[value1147,value1148,value1149]),0),
  ((R4117,2,[value1160,value1161,value1162]),0),
  ((R4195,2,[value1181,value1182,value1183]),0),
  ((R4207,2,[value1184,value1185,value1186]),0),
  ((R4265,2,[value1208,value1209,value1210]),0),
  ((R7,3,[value23,value24,value25,value26]),0),
  ((R13,3,[value36,value39,value41,value46]),0),
  ((R13,3,[value39,value40,value41,value46]),0),
  ((R13,3,[value39,value41,value42,value46]),0),
  ((R13,3,[value39,value41,value44,value46]),0),
  ((R13,3,[value39,value41,value45,value46]),0),
  ((R14,3,[value47,value50,value54,value57]),0),
  ((R14,3,[value50,value51,value54,value57]),0),
  ((R14,3,[value50,value53,value54,value57]),0),
  ((R14,3,[value50,value54,value55,value57]),0),
  ((R14,3,[value50,value54,value56,value57]),0),
  ((R21,3,[value66,value67,value70,value72]),0),
  ((R21,3,[value66,value69,value70,value72]),0),
  ((R21,3,[value68,value69,value70,value72]),0)]
private def bank2 : Array Query := #[
  ((R21,3,[value69,value70,value71,value72]),0),
  ((R22,3,[value73,value74,value75,value76]),0),
  ((R22,3,[value73,value74,value76,value77]),0),
  ((R28,3,[value78,value79,value90,value92]),0),
  ((R28,3,[value79,value83,value90,value92]),0),
  ((R28,3,[value79,value84,value90,value92]),0),
  ((R28,3,[value80,value83,value88,value92]),0),
  ((R28,3,[value83,value85,value88,value92]),0),
  ((R28,3,[value83,value87,value88,value92]),0),
  ((R28,3,[value83,value88,value89,value92]),0),
  ((R28,3,[value83,value88,value91,value92]),0),
  ((R28,3,[value84,value88,value90,value92]),0),
  ((R30,3,[value99,value101,value104]),0),
  ((R30,3,[value100,value106,value110]),0),
  ((R30,3,[value102,value107,value110]),0),
  ((R30,3,[value106,value107,value110]),0),
  ((R30,3,[value96,value98,value108,value110]),0),
  ((R30,3,[value96,value106,value107,value110]),0),
  ((R30,3,[value97,value99,value106,value110]),0),
  ((R30,3,[value97,value106,value107,value110]),0),
  ((R30,3,[value98,value99,value101,value106]),0),
  ((R30,3,[value98,value99,value106,value110]),0),
  ((R30,3,[value98,value106,value107,value110]),0),
  ((R30,3,[value99,value101,value104,value106]),0),
  ((R30,3,[value99,value101,value105,value106]),0),
  ((R30,3,[value99,value101,value106,value107]),0),
  ((R30,3,[value99,value101,value106,value109]),0),
  ((R30,3,[value99,value103,value106,value107]),0),
  ((R30,3,[value99,value105,value106,value110]),0),
  ((R30,3,[value99,value106,value107,value110]),0),
  ((R30,3,[value99,value106,value109,value110]),0),
  ((R30,3,[value101,value103,value106,value107]),0)]
private def bank3 : Array Query := #[
  ((R30,3,[value101,value106,value107,value110]),0),
  ((R30,3,[value103,value106,value107,value110]),0),
  ((R30,3,[value105,value106,value107,value110]),0),
  ((R30,3,[value106,value107,value109,value110]),0),
  ((R38,3,[value121,value123,value124,value127]),0),
  ((R38,3,[value121,value124,value126,value127]),0),
  ((R38,3,[value122,value124,value126,value127]),0),
  ((R38,3,[value124,value125,value126,value127]),0),
  ((R44,3,[value128,value132,value135,value138]),0),
  ((R44,3,[value132,value133,value135,value138]),0),
  ((R44,3,[value132,value134,value135,value138]),0),
  ((R44,3,[value132,value135,value136,value138]),0),
  ((R44,3,[value132,value135,value137,value138]),0),
  ((R45,3,[value145,value152,value156]),0),
  ((R45,3,[value148,value154,value156]),0),
  ((R45,3,[value149,value152,value154]),0),
  ((R45,3,[value152,value154,value156]),0),
  ((R45,3,[value141,value147,value152,value154]),0),
  ((R45,3,[value141,value147,value154,value156]),0),
  ((R45,3,[value141,value152,value154,value156]),0),
  ((R45,3,[value142,value144,value152,value154]),0),
  ((R45,3,[value142,value144,value152,value156]),0),
  ((R45,3,[value142,value152,value154,value156]),0),
  ((R45,3,[value143,value144,value147,value152]),0),
  ((R45,3,[value143,value144,value152,value156]),0),
  ((R45,3,[value143,value152,value154,value156]),0),
  ((R45,3,[value144,value146,value147,value154]),0),
  ((R45,3,[value144,value147,value152,value154]),0),
  ((R45,3,[value144,value147,value152,value155]),0),
  ((R45,3,[value144,value147,value153,value154]),0),
  ((R45,3,[value144,value149,value152,value154]),0),
  ((R45,3,[value144,value151,value152,value156]),0)]
private def bank4 : Array Query := #[
  ((R45,3,[value144,value152,value154,value156]),0),
  ((R45,3,[value144,value152,value155,value156]),0),
  ((R45,3,[value145,value152,value154,value156]),0),
  ((R45,3,[value146,value147,value154,value156]),0),
  ((R45,3,[value146,value152,value154,value156]),0),
  ((R45,3,[value147,value149,value152,value154]),0),
  ((R45,3,[value147,value150,value154,value156]),0),
  ((R45,3,[value147,value152,value154,value156]),0),
  ((R45,3,[value147,value153,value154,value156]),0),
  ((R45,3,[value148,value152,value154,value156]),0),
  ((R45,3,[value149,value152,value154,value156]),0),
  ((R45,3,[value150,value152,value154,value156]),0),
  ((R45,3,[value151,value152,value154,value156]),0),
  ((R45,3,[value152,value153,value154,value156]),0),
  ((R45,3,[value152,value154,value155,value156]),0),
  ((R45,3,[value152,value154,value156,value157]),0),
  ((R52,3,[value158,value160,value161,value164]),0),
  ((R52,3,[value158,value161,value162,value164]),0),
  ((R52,3,[value159,value161,value162,value164]),0),
  ((R52,3,[value160,value161,value163,value164]),0),
  ((R52,3,[value161,value162,value163,value164]),0),
  ((R84,3,[value165,value166,value167,value168]),0),
  ((R86,3,[value177,value179,value181]),0),
  ((R86,3,[value169,value170,value177,value179]),0),
  ((R86,3,[value169,value171,value179,value181]),0),
  ((R86,3,[value169,value173,value177,value181]),0),
  ((R86,3,[value169,value176,value177,value179]),0),
  ((R86,3,[value169,value176,value179,value181]),0),
  ((R86,3,[value169,value177,value179,value181]),0),
  ((R86,3,[value170,value177,value179,value181]),0),
  ((R86,3,[value171,value177,value179,value181]),0),
  ((R86,3,[value172,value177,value179,value181]),0)]
private def bank5 : Array Query := #[
  ((R86,3,[value174,value177,value179,value181]),0),
  ((R86,3,[value175,value177,value179,value181]),0),
  ((R86,3,[value176,value177,value179,value181]),0),
  ((R86,3,[value177,value178,value179,value181]),0),
  ((R86,3,[value177,value179,value180,value181]),0),
  ((R205,3,[value182,value183,value184,value185]),0),
  ((R205,3,[value182,value183,value185,value186]),0),
  ((R208,3,[value187,value188,value189,value190]),0),
  ((R208,3,[value187,value188,value190,value191]),0),
  ((R343,3,[value200,value201,value202]),0),
  ((R343,3,[value192,value200,value201,value202]),0),
  ((R343,3,[value193,value200,value201,value202]),0),
  ((R343,3,[value194,value200,value201,value202]),0),
  ((R343,3,[value195,value200,value201,value202]),0),
  ((R343,3,[value197,value200,value201,value202]),0),
  ((R343,3,[value198,value200,value201,value202]),0),
  ((R619,3,[value210,value211,value212]),0),
  ((R619,3,[value203,value210,value211,value212]),0),
  ((R619,3,[value204,value210,value211,value212]),0),
  ((R619,3,[value205,value210,value211,value212]),0),
  ((R619,3,[value206,value210,value211,value212]),0),
  ((R619,3,[value208,value210,value211,value212]),0),
  ((R619,3,[value209,value210,value211,value212]),0),
  ((R622,3,[value220,value221,value222]),0),
  ((R622,3,[value213,value220,value221,value222]),0),
  ((R622,3,[value214,value220,value221,value222]),0),
  ((R622,3,[value215,value220,value221,value222]),0),
  ((R622,3,[value216,value220,value221,value222]),0),
  ((R622,3,[value218,value220,value221,value222]),0),
  ((R622,3,[value219,value220,value221,value222]),0),
  ((R1014,3,[value223,value224,value225,value226]),0),
  ((R1020,3,[value227,value228,value230,value233]),0)]
private def bank6 : Array Query := #[
  ((R1020,3,[value227,value230,value231,value233]),0),
  ((R1020,3,[value228,value229,value230,value233]),0),
  ((R1020,3,[value228,value230,value232,value233]),0),
  ((R1020,3,[value230,value231,value232,value233]),0),
  ((R1033,3,[value234,value235,value236,value237]),0),
  ((R1035,3,[value238,value239,value241,value242]),0),
  ((R1035,3,[value239,value240,value241,value242]),0),
  ((R1037,3,[value243,value248,value250,value252]),0),
  ((R1037,3,[value245,value248,value250,value252]),0),
  ((R1037,3,[value247,value248,value250,value252]),0),
  ((R1037,3,[value248,value249,value250,value252]),0),
  ((R1037,3,[value248,value250,value251,value252]),0),
  ((R1038,3,[value253,value255,value256,value259]),0),
  ((R1038,3,[value253,value256,value257,value259]),0),
  ((R1038,3,[value254,value255,value256,value259]),0),
  ((R1038,3,[value255,value256,value258,value259]),0),
  ((R1038,3,[value256,value257,value258,value259]),0),
  ((R1039,3,[value260,value261,value262,value263]),0),
  ((R1045,3,[value264,value265,value266,value267]),0),
  ((R1047,3,[value268,value269,value270,value271]),0),
  ((R1058,3,[value273,value274,value276]),0),
  ((R1058,3,[value272,value273,value274,value276]),0),
  ((R1058,3,[value273,value274,value275,value276]),0),
  ((R1064,3,[value277,value278,value279,value280]),0),
  ((R1065,3,[value281,value282,value283,value285]),0),
  ((R1065,3,[value282,value283,value284,value285]),0),
  ((R1109,3,[value286,value287,value288,value289]),0),
  ((R1116,3,[value290,value291,value292,value293]),0),
  ((R1131,3,[value299,value300,value301,value302]),0),
  ((R1132,3,[value303,value304,value305,value306]),0),
  ((R1147,3,[value307,value308,value309,value310]),0),
  ((R1153,3,[value311,value312,value313,value314]),0)]
private def bank7 : Array Query := #[
  ((R1160,3,[value315,value316,value317,value318]),0),
  ((R1167,3,[value319,value320,value321,value322]),0),
  ((R1177,3,[value326,value327,value328,value329]),0),
  ((R1184,3,[value330,value331,value332,value333]),0),
  ((R1204,3,[value337,value338,value339,value340]),0),
  ((R1214,3,[value344,value345,value346,value347]),0),
  ((R1215,3,[value348,value349,value350,value352]),0),
  ((R1215,3,[value350,value351,value352,value353]),0),
  ((R1216,3,[value354,value355,value356,value357]),0),
  ((R1230,3,[value364,value369,value371,value374]),0),
  ((R1230,3,[value366,value369,value371,value374]),0),
  ((R1230,3,[value367,value369,value371,value374]),0),
  ((R1230,3,[value369,value370,value371,value374]),0),
  ((R1230,3,[value369,value371,value372,value374]),0),
  ((R1230,3,[value369,value372,value373,value374]),0),
  ((R1231,3,[value375,value376,value377,value378]),0),
  ((R1251,3,[value379,value380,value381,value382]),0),
  ((R1269,3,[value383,value384,value385,value386]),0),
  ((R1277,3,[value390,value391,value392,value393]),0),
  ((R1291,3,[value394,value395,value396,value397]),0),
  ((R1363,3,[value404,value409,value411,value413]),0),
  ((R1363,3,[value405,value409,value411,value413]),0),
  ((R1363,3,[value406,value409,value411,value413]),0),
  ((R1363,3,[value409,value410,value411,value413]),0),
  ((R1363,3,[value409,value411,value412,value413]),0),
  ((R1364,3,[value414,value415,value418,value421]),0),
  ((R1364,3,[value415,value416,value418,value421]),0),
  ((R1364,3,[value415,value417,value418,value421]),0),
  ((R1364,3,[value415,value418,value419,value421]),0),
  ((R1364,3,[value415,value418,value420,value421]),0),
  ((R1371,3,[value422,value423,value424,value427]),0),
  ((R1371,3,[value422,value423,value424,value428]),0)]
private def bank8 : Array Query := #[
  ((R1371,3,[value424,value425,value426,value427]),0),
  ((R1406,3,[value429,value430,value431,value432]),0),
  ((R1407,3,[value433,value434,value435,value436]),0),
  ((R1410,3,[value437,value438,value440,value442]),0),
  ((R1410,3,[value439,value440,value441,value442]),0),
  ((R1434,3,[value443,value448,value450,value453]),0),
  ((R1434,3,[value445,value448,value450,value453]),0),
  ((R1434,3,[value446,value448,value450,value453]),0),
  ((R1434,3,[value448,value449,value450,value453]),0),
  ((R1434,3,[value448,value450,value451,value453]),0),
  ((R1434,3,[value448,value451,value452,value453]),0),
  ((R1442,3,[value454,value455,value456,value458]),0),
  ((R1442,3,[value456,value457,value458,value459]),0),
  ((R1459,3,[value460,value461,value462,value463]),0),
  ((R1497,3,[value464,value465,value466,value467]),0),
  ((R1503,3,[value468,value469,value470,value471]),0),
  ((R1550,3,[value472,value473,value474,value475]),0),
  ((R1582,3,[value479,value480,value482,value483]),0),
  ((R1582,3,[value480,value481,value482,value483]),0),
  ((R1608,3,[value490,value491,value492,value493]),0),
  ((R1622,3,[value494,value495,value496,value497]),0),
  ((R1631,3,[value498,value499,value500,value501]),0),
  ((R1652,3,[value502,value503,value504,value505]),0),
  ((R1672,3,[value506,value507,value508]),0),
  ((R1699,3,[value510,value511,value512,value514]),0),
  ((R1735,3,[value516,value517,value519,value521]),0),
  ((R1787,3,[value522,value523,value524,value525]),0),
  ((R1826,3,[value526,value527,value528,value529]),0),
  ((R1846,3,[value535,value536,value537,value538]),0),
  ((R1873,3,[value539,value540,value541,value542]),0),
  ((R1886,3,[value543,value544,value545,value546]),0),
  ((R1948,3,[value556,value557,value558,value562]),0)]
private def bank9 : Array Query := #[
  ((R1948,3,[value556,value558,value559,value563]),0),
  ((R1948,3,[value558,value559,value560,value562]),0),
  ((R1948,3,[value558,value559,value561,value562]),0),
  ((R1949,3,[value564,value565,value566,value567]),0),
  ((R1959,3,[value568,value569,value570,value571]),0),
  ((R1966,3,[value572,value573,value574]),0),
  ((R2011,3,[value578,value579,value580,value581]),0),
  ((R2020,3,[value585,value586,value587,value588]),0),
  ((R2077,3,[value595,value596,value597,value598]),0),
  ((R2102,3,[value604,value605,value606,value607]),0),
  ((R2103,3,[value608,value609,value610,value611]),0),
  ((R2126,3,[value619,value620,value621,value622]),0),
  ((R2143,3,[value623,value624,value625,value626]),0),
  ((R2189,3,[value633,value634,value635,value636]),0),
  ((R2235,3,[value643,value644,value645,value646]),0),
  ((R2249,3,[value647,value648,value649,value650]),0),
  ((R2286,3,[value651,value652,value653,value654]),0),
  ((R2301,3,[value655,value656,value657]),0),
  ((R2303,3,[value658,value659,value660,value661]),0),
  ((R2314,3,[value662,value663,value664,value665]),0),
  ((R2319,3,[value666,value667,value668,value669]),0),
  ((R2330,3,[value676,value677,value678,value679]),0),
  ((R2395,3,[value689,value690,value691,value692]),0),
  ((R2399,3,[value693,value694,value695,value696]),0),
  ((R2465,3,[value708,value709,value710,value711]),0),
  ((R2466,3,[value712,value713,value714,value715]),0),
  ((R2524,3,[value723,value724,value725,value726]),0),
  ((R2538,3,[value727,value728,value729,value730]),0),
  ((R2561,3,[value736,value737,value738,value739]),0),
  ((R2562,3,[value740,value741,value742,value743]),0),
  ((R2569,3,[value744,value745,value746]),0),
  ((R2589,3,[value749,value750,value751,value752]),0)]
private def bank10 : Array Query := #[
  ((R2619,3,[value758,value759,value760,value762]),0),
  ((R2656,3,[value767,value768,value769,value770]),0),
  ((R2693,3,[value779,value780,value781,value782]),0),
  ((R2695,3,[value783,value784,value787,value788]),0),
  ((R2695,3,[value784,value785,value786,value788]),0),
  ((R2716,3,[value789,value790,value791]),0),
  ((R2742,3,[value795,value796,value797,value798]),0),
  ((R2750,3,[value799,value800,value801,value802]),0),
  ((R2756,3,[value803,value804,value805,value806]),0),
  ((R2857,3,[value827,value828,value829,value830]),0),
  ((R2901,3,[value831,value832,value833,value834]),0),
  ((R2901,3,[value832,value833,value834,value835]),0),
  ((R2901,3,[value832,value833,value834,value836]),0),
  ((R2939,3,[value837,value838,value839,value840]),0),
  ((R2958,3,[value841,value842,value843,value844]),0),
  ((R2963,3,[value845,value846,value847,value848]),0),
  ((R2970,3,[value849,value850,value851,value852]),0),
  ((R2977,3,[value853,value854,value855,value856]),0),
  ((R2985,3,[value857,value858,value860,value861]),0),
  ((R2985,3,[value858,value859,value860,value861]),0),
  ((R2999,3,[value862,value863,value864,value865]),0),
  ((R3033,3,[value869,value870,value871,value872]),0),
  ((R3071,3,[value873,value874,value875,value876]),0),
  ((R3082,3,[value889,value890,value891,value892]),0),
  ((R3087,3,[value893,value894,value895,value896]),0),
  ((R3091,3,[value897,value898,value899,value900]),0),
  ((R3099,3,[value901,value902,value903,value906]),0),
  ((R3099,3,[value901,value903,value904,value906]),0),
  ((R3099,3,[value901,value903,value905,value906]),0),
  ((R3117,3,[value907,value908,value909,value910]),0),
  ((R3142,3,[value911,value912,value913,value914]),0),
  ((R3145,3,[value915,value916,value917,value918]),0)]
private def bank11 : Array Query := #[
  ((R3172,3,[value919,value920,value921,value922]),0),
  ((R3190,3,[value923,value924,value925,value926]),0),
  ((R3216,3,[value927,value928,value929,value930]),0),
  ((R3225,3,[value931,value932,value933,value934]),0),
  ((R3247,3,[value945,value946,value947,value948]),0),
  ((R3249,3,[value949,value950,value951,value952]),0),
  ((R3257,3,[value953,value954,value955,value956]),0),
  ((R3354,3,[value957,value958,value959,value960]),0),
  ((R3355,3,[value961,value962,value963,value964]),0),
  ((R3364,3,[value965,value966,value967,value968]),0),
  ((R3373,3,[value969,value970,value971,value972]),0),
  ((R3415,3,[value973,value974,value975,value976]),0),
  ((R3430,3,[value977,value978,value979,value980]),0),
  ((R3458,3,[value986,value987,value988,value989]),0),
  ((R3460,3,[value990,value991,value992,value993]),0),
  ((R3474,3,[value997,value998,value999,value1000]),0),
  ((R3479,3,[value1001,value1002,value1003,value1004]),0),
  ((R3487,3,[value1005,value1006,value1007,value1008]),0),
  ((R3498,3,[value1012,value1013,value1014,value1015]),0),
  ((R3500,3,[value1016,value1017,value1018,value1019]),0),
  ((R3508,3,[value1020,value1021,value1022,value1023]),0),
  ((R3515,3,[value1024,value1025,value1026,value1027]),0),
  ((R3521,3,[value1028,value1029,value1030,value1031]),0),
  ((R3568,3,[value1035,value1036,value1038,value1040]),0),
  ((R3568,3,[value1035,value1037,value1038,value1040]),0),
  ((R3568,3,[value1035,value1038,value1039,value1040]),0),
  ((R3569,3,[value1041,value1042,value1043,value1044]),0),
  ((R3593,3,[value1045,value1046,value1047,value1048]),0),
  ((R3620,3,[value1049,value1050,value1051,value1052]),0),
  ((R3627,3,[value1053,value1054,value1055,value1056]),0),
  ((R3638,3,[value1057,value1058,value1059,value1060]),0),
  ((R3640,3,[value1061,value1062,value1063,value1064]),0)]
private def bank12 : Array Query := #[
  ((R3749,3,[value1088,value1089,value1090,value1091]),0),
  ((R3854,3,[value1096,value1097,value1098,value1099]),0),
  ((R3953,3,[value1105,value1106,value1107,value1108]),0),
  ((R3976,3,[value1109,value1110,value1111,value1112]),0),
  ((R3984,3,[value1113,value1114,value1115]),0),
  ((R3997,3,[value1116,value1117,value1118,value1119]),0),
  ((R4010,3,[value1120,value1121,value1122,value1123]),0),
  ((R4019,3,[value1129,value1130,value1131,value1132]),0),
  ((R4020,3,[value1133,value1134,value1135,value1136]),0),
  ((R4039,3,[value1137,value1138,value1139,value1140]),0),
  ((R4047,3,[value1144,value1145,value1146]),0),
  ((R4108,3,[value1155,value1156,value1158,value1159]),0),
  ((R4108,3,[value1156,value1157,value1158,value1159]),0),
  ((R4122,3,[value1163,value1164,value1165,value1166]),0),
  ((R4170,3,[value1172,value1173,value1176,value1177]),0),
  ((R4170,3,[value1173,value1174,value1175,value1177]),0),
  ((R4175,3,[value1178,value1179,value1180]),0),
  ((R4221,3,[value1187,value1188,value1189,value1190]),0),
  ((R4229,3,[value1191,value1192,value1193,value1194]),0),
  ((R4234,3,[value1195,value1196,value1197,value1198]),0),
  ((R4274,3,[value1211,value1212,value1213,value1214]),0),
  ((R4306,3,[value1215,value1216,value1217,value1218]),0),
  ((R13,4,[value36,value39,value41,value46]),0x203),
  ((R13,4,[value37,value39,value41,value43,value46]),0x20300710203),
  ((R13,4,[value38,value39,value41,value43,value46]),0x20300710203),
  ((R14,4,[value47,value50,value54,value57]),0x203),
  ((R14,4,[value48,value50,value52,value54,value57]),0x20300500203),
  ((R14,4,[value49,value50,value52,value54,value57]),0x20300500203),
  ((R28,4,[value80,value83,value88,value92]),0x203),
  ((R28,4,[value81,value83,value86,value88,value92]),0x20300500203),
  ((R28,4,[value82,value83,value86,value88,value92]),0x20300500203),
  ((R44,4,[value128,value132,value135,value138]),0x203)]
private def bank13 : Array Query := #[
  ((R44,4,[value129,value131,value132,value135,value138]),0x20300710203),
  ((R44,4,[value130,value131,value132,value135,value138]),0x20300710203),
  ((R44,4,[value131,value132,value135,value138,value139]),0x2030071),
  ((R44,4,[value131,value132,value135,value138,value140]),0x2030071),
  ((R1037,4,[value247,value248,value250,value252]),0x203),
  ((R1037,4,[value244,value247,value248,value250,value252]),0x2030203),
  ((R1037,4,[value246,value247,value248,value250,value252]),0x2030203),
  ((R1230,4,[value367,value369,value371,value374]),0x203),
  ((R1230,4,[value365,value367,value369,value371,value374]),0x2030203),
  ((R1230,4,[value367,value368,value369,value371,value374]),0x2030203),
  ((R1363,4,[value406,value409,value411,value413]),0x203),
  ((R1363,4,[value406,value407,value409,value411,value413]),0x2030203),
  ((R1363,4,[value406,value408,value409,value411,value413]),0x2030203),
  ((R1364,4,[value414,value415,value418,value421]),0x203),
  ((R1434,4,[value446,value448,value450,value453]),0x203),
  ((R1434,4,[value444,value446,value448,value450,value453]),0x2030203),
  ((R1434,4,[value446,value447,value448,value450,value453]),0x2030203),
  ((R1735,4,[value516,value517,value518,value519,value520]),0xca),
  ((R1826,4,[value526,value527,value528,value529]),0x203),
  ((R1934,4,[value547,value548,value549,value550]),0x203),
  ((R2105,4,[value612,value613,value614,value615]),0x203),
  ((R2467,4,[value716,value717,value718,value719]),0x203),
  ((R2623,4,[value763,value764,value765,value766]),0x203),
  ((R3072,4,[value877,value878,value879,value883,value886]),0x2030203),
  ((R3072,4,[value877,value879,value881,value883,value886]),0x2030203),
  ((R3072,4,[value878,value879,value880,value883,value886]),0x203),
  ((R3072,4,[value878,value879,value881,value883,value886]),0x2030029),
  ((R3072,4,[value878,value879,value883,value884,value886]),0x203),
  ((R3072,4,[value879,value881,value882,value883,value886]),0x203),
  ((R3072,4,[value879,value881,value883,value885,value886]),0x203),
  ((R3172,4,[value919,value920,value921,value922]),0x203),
  ((R3190,4,[value923,value924,value925,value926]),0x203)]
private def bank14 : Array Query := #[
  ((R3236,4,[value935,value936,value937,value939,value944]),0x2030203),
  ((R3236,4,[value935,value937,value939,value941,value944]),0x2030203),
  ((R3236,4,[value936,value937,value938,value939,value944]),0x203),
  ((R3236,4,[value936,value937,value939,value940,value944]),0x203),
  ((R3236,4,[value936,value937,value939,value941,value944]),0x203001f),
  ((R3236,4,[value937,value939,value941,value942,value944]),0x203),
  ((R3236,4,[value937,value939,value941,value943,value944]),0x203),
  ((R3257,4,[value953,value954,value955,value956]),0x203),
  ((R3648,4,[value1066,value1068,value1070,value1071,value1072]),0xf7),
  ((R3668,4,[value1073,value1074,value1075,value1076]),0x203),
  ((R3761,4,[value1092,value1093,value1094,value1095]),0x203),
  ((R4252,4,[value1204,value1205,value1206,value1207]),0x203),
  ((R20,5,[value60,value61,value62,value63,value64,value65]),0x2040097),
  ((R36,5,[value115,value116,value117,value118,value119,value120]),0x2050071),
  ((R1118,5,[value294,value295,value296,value297,value298]),0x206),
  ((R1220,5,[value358,value359,value360,value361,value362,value363]),0x20700b8),
  ((R1595,5,[value484,value485,value486,value487,value488,value489]),0x2080050),
  ((R1699,5,[value509,value510,value511,value512,value513]),0x1ca),
  ((R1735,5,[value515,value516,value517,value519,value520]),0x1b3),
  ((R1735,5,[value516,value517,value518,value519,value520]),0x1a5),
  ((R2223,5,[value637,value638,value639,value640,value641,value642]),0x2090050),
  ((R2322,5,[value670,value671,value672,value673,value674,value675]),0x20a00b1),
  ((R2782,5,[value810,value811,value812,value813,value814]),0x20b),
  ((R3449,5,[value981,value982,value983,value984,value985]),0x20c),
  ((R3648,5,[value1065,value1068,value1070,value1071,value1072]),0x1ab),
  ((R3648,5,[value1066,value1067,value1068,value1070,value1071]),0x1ab),
  ((R3648,5,[value1068,value1069,value1070,value1071,value1072]),0x1ab),
  ((R3676,5,[value1077,value1078,value1079,value1080,value1081,value1082]),0x1a501a501a5),
  ((R4092,5,[value1150,value1151,value1152,value1153,value1154]),0x20d),
  ((R5,6,[value13,value14,value15,value16,value17]),0x20f),
  ((R6,6,[value18,value19,value20,value21,value22]),0x211),
  ((R12,6,[value31,value32,value33,value34,value35]),0x212)]
private def bank15 : Array Query := #[
  ((R20,6,[value60,value61,value62,value63,value65]),0x214),
  ((R20,6,[value58,value60,value61,value62,value63,value65]),0x2150214),
  ((R20,6,[value59,value60,value61,value62,value63,value65]),0x22a02140228),
  ((R36,6,[value111,value115,value116,value118,value120]),0x22c),
  ((R36,6,[value112,value115,value116,value118,value120]),0x22e),
  ((R36,6,[value115,value116,value117,value118,value120]),0x22f),
  ((R36,6,[value113,value115,value116,value117,value118,value120]),0x231022f),
  ((R36,6,[value114,value115,value116,value117,value118,value120]),0x233022f),
  ((R1220,6,[value358,value359,value360,value361,value363]),0x237),
  ((R1595,6,[value484,value485,value486,value487,value489]),0x238),
  ((R1836,6,[value530,value531,value532,value533,value534]),0x23a),
  ((R1939,6,[value551,value552,value553,value554,value555]),0x23e),
  ((R2092,6,[value599,value600,value601,value602,value603]),0x240),
  ((R2223,6,[value637,value638,value639,value640,value642]),0x241),
  ((R2322,6,[value670,value671,value672,value673,value675]),0x245),
  ((R2454,6,[value703,value704,value705,value706,value707]),0x247),
  ((R2552,6,[value731,value732,value733,value734,value735]),0x249),
  ((R2607,6,[value753,value754,value755,value756,value757]),0x24b),
  ((R2685,6,[value774,value775,value776,value777,value778]),0x24f),
  ((R3721,6,[value1083,value1084,value1085,value1086,value1087]),0x251),
  ((R3945,6,[value1100,value1101,value1102,value1103,value1104]),0x253),
  ((R4012,6,[value1124,value1125,value1126,value1127,value1128]),0x256),
  ((R4164,6,[value1167,value1168,value1169,value1170,value1171]),0x259),
  ((R4239,6,[value1199,value1200,value1201,value1202,value1203]),0x25b),
  ((R12,7,[value31,value32,value33,value34,value35]),0x264),
  ((R12,7,[value27,value31,value32,value33,value34,value35]),0x27d0264),
  ((R12,7,[value28,value31,value32,value33,value34,value35]),0x2960264),
  ((R12,7,[value29,value31,value32,value33,value34,value35]),0x2ad0264),
  ((R12,7,[value30,value31,value32,value33,value34,value35]),0x2c40264),
  ((R2046,7,[value589,value590,value591,value592,value593,value594]),0x2c5),
  ((R2188,7,[value627,value628,value629,value630,value631,value632]),0x2c6),
  ((R2418,7,[value697,value698,value699,value700,value701,value702]),0x2c7)]
private def bank16 : Array Query := #[
  ((R4,9,[value7,value8,value9,value10,value11,value12]),0x2e2),
  ((R0,10,[value0,value1,value2,value3,value4,value5,value6]),0x201)]
private def bankBlocks : Array (Array Query) := #[bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16]
private def bank (i : ℕ) : Query :=
  ((bankBlocks[i / 32]?).getD #[])[i % 32]?.getD ((R29,0,[]),0)
private def trees0 : Array ℕ := #[
  0,
  0x800040009000e0095,
  0x95,
  0x90009001100dd009d001200a0001300a000de00df000900e000090097000e00e600e5000e00b100e300e400e200e1,
  0xf00f200f30010001400ef00c4,
  0x117,
  0x131,
  0xd01370138000e001b010b00d1,
  0xb50104015500b2015300d2000e000e000e000e002800b5001e0154,
  0x9000901700009017400090097001001750171001000b800a0002b00a0016f01730172002c016e009d002a01770176,
  0xff00ff018e0100018c00d400100010002f00ff00100010001a018d,
  0x40,
  0x71000700f700070081007700f001140007004000710007000c00070071000c00aa0007000700710007000700070071000c0007000c0007008800740134012f00070135007100070085007a020e00400007000c000c0007,
  0x680009001000080004,
  0x9006800970009000900970009000900090097001000090097001000b8000900090004009700970097000900a00004011d00040009001000100009000900520097000900a3009d02100068000900970010001000b800090004009f01290004,
  0x5e000700f700070081000400ec000400070004007100070088000401080004000700040071000700040004000400040061000700ca0007000700070007000700040007007100070004000700710007,
  0x95000800040009000e,
  0x900950097000900090004009700970097000900a0000401130004000900970009000900090097000e00090097000e00b10009000e0009000e0009000900520097000900a3009d021300950004009f00dc000400090097000e000e00b10009,
  0x9d009d009d009d009d00b2009d009d009c009b00400095009900dc009d00b20009009d009d00090213004002030004005700a500040009009d0097000e000e00b200b10009009500950203,
  0xb700b700b700b70026004c0004000400090009009d000e00090009,
  0x46000900260024000e,
  0xe009d0009,
  0x2030203000e000e0009,
  0x450057,
  0x4502030044001700450045003f0046003e0045009d000e00240024,
  0x4c0024003f009a00570009000e,
  0x27009b0096002400450024,
  0x240203,
  0xe000e009d0203009d009d0203009d020302030009009d00090203009d009d003f,
  0x203014c001700b7003f0041009d,
  0xe000e009d009d0009000900250051000900b7009d003f,
  0xa1]
private def trees1 : Array ℕ := #[
  0x9b0203000e000e000900b7009d0203009d009d0203009d020302030009009d000900970098014e00a400b3009d0057,
  0x203014d00570098002000a400b3,
  0x270045000e000e000900b7009d009d00090009005700a5009d0057,
  0x20302030001000e00640009,
  0x14b000e000e,
  0x9d02270226009d009d0057022502240223009d0222005701120057009d003f02210220021f009d021e021d003f021c021b003f0057003f021a0057009d009702190218009d009700b100b100b102030057014a02030057003f009d009702170216003f,
  0x95000e0009,
  0x9d009d009d009d009d009d014f000e009d00b1000e00b1009d013d009d012e009d009d009d009b0229009d015000b1009d0009009d009d0009000e000e02030004005700a500040009009d000e0151000e00b100b10009009d00970095000900b7009d,
  0x92,
  0x81009200c000920088007400cd011b0092007a022b009200710007011c000700920007007100070066000700710007007100aa0071020300920007007100070066000700710007000700710007000700070071,
  0x93,
  0x81009300c200930088007400cf00670093007a022d0093007100070071000700930007007100070067000700710007007100070071007101b30007009300070071000700670007007100070007007100710203,
  0x81009500c300d8000c00070071000c00aa0007000c0007000c00070088007400d000bf0095007a020500950007000c000c00070071000700ca0007009500070071000700070007007100070007007100c7000700710007,
  0x940007,
  0x6600aa007400d100940094000c000c0067016c00c5000700c700070088007401a3016d0095007a02300095000700c70071000c000c00c700aa0007000700070203007100c70203,
  0x950007,
  0x9500c4009200aa000c000c007a009500d3000700950007009300db0081009501a40095000700070203000700950071000c000c009500aa0007007a009502320095007100950203,
  0xc100b800100010001600c40010001000b9001400100010,
  0xc000b800100010001500ef0010001000be001400100010,
  0xef00c400f3000f00f200100014,
  0x1000c300b80010001000ec00b800b800b8001000bc00ba00f400c3001000f000b8001000be00b9023600c300bd00bb00f100ec001000b800b8020300c3001000b800b80235001000ec00b8001000b800b8001000f0001000b800b802340010,
  0x5e00d8011500d8005000040108000400d8000400500004006100520116010200d80057020800d80004011400500004005001180050020300d80004005000040004005000040004000400500114000400500004,
  0x11e,
  0xaa000c00aa000c00ae00ac00f40113000c011300aa000c00b000ab011f011d000c011d00aa000c00af00ad0239011300aa000c00aa00aa01b4000c000c00aa00aa02030113000c00aa000c011d000c00aa000c,
  0x68,
  0x1210068000a01270019000c,
  0x650124012001240018012100190122000c000c000c000c,
  0xae012300c30123000c00aa023d000c00aa0128000c0125000c012300b00068023c006801230068023b0123012601260126020300aa000c00aa000c012300aa000c00aa00aa000c000c000c00aa000c000c00aa006800aa000c00aa00aa000c,
  0x1a00950007000c0006012c,
  0x810095023f0095000c00070071000c00aa0007000c00070071000c00aa00070088007400d0012d0095007a020500950007000c000c00070071000700710007007101b500710203000700070071000700070071012b00710007007100710007,
  0x5e00bf013300bf0050000400ec000400bf000400500004006100520130011000bf0057020900bf0004012f00500004005001320050020300bf000400500004000400500004000400040050012f000400500004,
  0xce00b1000e000e001c00d1000e000e00b2001b000e000e]
private def trees2 : Array ℕ := #[
  0xcd00b1000e000e001d010b000e000e00b7001b000e000e,
  0x10b00d10138000d0137000e001b,
  0xe00d000b1000e000e010800b100b100b1000e00b500b3011f00d0000e013400b1000e00b700b2024400d000b600b401360108000e00b100b1020300d0000e00b100b10243000e010800b1000e00b100b1000e0134000e00b100b10242000e,
  0x1e00680005013b0007000c,
  0x81013900c3013c000c00070071000c00aa0007000c0007000c000700880074024600680139007a023b013900070071000c000c00aa00070071000700710007013900710007007100710007000700070071000700070071007101b600710203,
  0x1400004000e000d0004,
  0xe00e900b1000e000e00b1000e000e000e00b1000e00040050000e00b10004000e000400b100b100b1000e00b50004005000040004013f013f0203000e005200b1000e00b700b2024800e900040050000e000e00b10004000400b400500004,
  0x210095000801420009000e,
  0x901410097009700970009000900970009000900090097000e0009000e0009000900970097000900a2009f00dc014100090097000e000e00b100090097009701b70203009e00a00205014100090097000e000e00b10009009d00a3024a0095,
  0x33,
  0x144003300220010000f0147,
  0x1430143014301430023014400100010002200be00100010,
  0x1000b800b80010001000b800100010001000b8001000b8024e001000b801480010014500b800b800b8001000bc00ba011d014501490010001001450010003300b800b800b8001000be00b9024d0033014601460146020300bd00bb024c0145,
  0x181,
  0xae00dc00f100dc000c00aa01cb000c00aa00aa000c00aa000c00dc00b001290136012900dc0129025000dc00aa000c000c0129000c00aa000c00aa000c00aa000c00dc000c00aa00aa0203000c00aa000c0129,
  0x187,
  0x8101830186018300880128018400bf01830128025201830071000700ca000701830007007100070128000700710007007101850071020301830007007100070128000700710007000700710007000700070071,
  0x920095002d000c000b018a,
  0x92018900910189002e0092002d0092000c000c000c000c,
  0xc00aa0255000c00aa018300ae009502540095018b018b018b020300b0018800d0018800e9000c000c0188009501880205009500aa000c00aa000c000c000c00aa000c000c00aa009500aa000c00aa00aa000c018800aa000c00aa00aa000c,
  0x18f0040000d01940030000e,
  0x1500150015001500031018f000e000e003000b7000e000e,
  0xe00b100b1000e000e019000b100b100b1000e00b500b301130190000e00b1000e000e000e00b1000e00b10258000e00b10193000e0192000e0190000e004000b100b100b1000e00b700b20257004000b600b4020e01900191019101910203,
  0x320040000801950009000e,
  0x900970097000900090102009700970097000900a0009e01130196000900970009000900090097000e00090097000e00b10009000e0009000e00090097009701cc020300a3009d025a004000a2009f020e010200090097000e000e00b10009,
  0x740107010400710085004900fc00c9006b006b01050050000400070004000700880074010f011000070057007100070004007a00500004020300070007020300040004,
  0x7700eb00ff0071007a003b00fe00c8006d006d010100500004000700040007008100770103010200070057007100070004008500500004020300070007020300040004,
  0x5a00f70069006900fa000700ca000700070071006400070004008100610004000400880061000400070007020300ca00ca0203,
  0x5400f6010c005000570037007401060085004b010d0071000700040007000400880074010e00bf0004007a00500004000700c700710007020300040004020300070007,
  0x7c00ec008400470073000401080004000700880088000700040050008f00040007008800880007000400040203010801080203,
  0x5400f500e7005000570038007700ea007a003d00e80071000700040007000400810077011100d80004008500500004000700da00710007020300040004020300070007,
  0x7c0108007900390076000400ec0004000700810081000700040050008e0004000700810081000700040004020300ec00ec0203]
private def trees3 : Array ℕ := #[
  0x5a00ca005600340053000700f7000700040081005e000400040088005e00040007007100ca000700070007020300f700f70203,
  0x263007101ab00710262005001a8005000710050026100710260005001af005000710050025f00710050005000500050025e007101a50071007100710071007100500071025d007100500071025c0071,
  0x6a00050004,
  0x6c00060004,
  0x16700f700fa00ca006900340069003401a0000700070203006400f702030004008102660004000400880265000400ca00ca0203,
  0xca01c100f700fa00ca0007005f00070203,
  0x4900350007,
  0x5300f8005600350165005e005e0165005e005e005e0269000700040108005e0007005e010e0007000400830165006e00900004005e0050000701a1010f0007020300880165,
  0xf80165005e006e005e02030004,
  0x8800f600880088007301060084005e00bf00bf02030088016602030004005e008f00040007008800880007005e01650203,
  0xf60073016500bf016600040203,
  0x3b00360007,
  0x5300f900560036015e005e005e015e005e005e005e026e0007000400ec005e0007005e011100070004008a015e006f00900004005e0050000701a20103000702030081015e,
  0xf9015e005e006f005e02030004,
  0x8100f500810081007600ea0079005e00d800d802030081015602030004005e008e00040007008100810007005e015e0203,
  0xf50076015e00d8015600040203,
  0x3500490007,
  0x74027300c901c300fc00c90056016b00880074010f016a,
  0x36003b0007,
  0x77027500c801c400fe00c8005601680081007701030169,
  0xf700f70069005500690058004d00fa000700ca000700070059005b000700070007005c0060007100ca00ca,
  0xf701c500fa00ca00ca005d005f0007000700620071,
  0xf600740165007400bf00880074010e0004,
  0x730165005301660004000700710088,
  0xf50077015e007700d80081007701110004,
  0x76015e005301560004000700710081,
  0x7101c8007101ab01ab00710071027c005e01a9005e0071005e027b005e027a005e01b0005e0071005e0279005e005e005e005e005e02780277007101a501a50071007100710197007100710197005e00710276005e005e00710274005e0071007100710203020301ab01ab01ab02030203005e0050027202710270026f005e0050005e0050026d026c026b026a005e0050007100710268026701a501a500710071,
  0x6b003a0004,
  0x7600ed0079003a015a0081008100810081015a0081027e0004000700ca008100070081015a004e008100070081007100040081010300070004019e008e000402030081015a,
  0xed015a0081004e008102030007,
  0x7600eb00790061008100c800810081010201020203000700810081000700610159020300040061008e00040081015a0203,
  0xeb0081015a0102015900070203]
private def trees4 : Array ℕ := #[
  0x4800020007,
  0x4a00030007,
  0x16100ec016201080047003900470039019d0004000402030007005e02840007008f00ec02030007006102830007008e01080203,
  0x10801b800ec016201080004008200040203,
  0x37003c0004,
  0x7600ee0079003c015600810081015600810287008100810004000700f7008100040081011100070004019f008e0004000700810156004f0081000700810071020300810156,
  0xee01560081004f008102030007,
  0x7600ea0079005e008100f50081008100d800d80203005e015e02030004005e008e00040007008100810007008101560203,
  0xea0081015600d8015e00070203,
  0x3a006b0004,
  0x10701ba008c008e015b028c007901640061008c008e0163,
  0xeb015d015a007501020081005201030007,
  0x15c015a007601590007000400710081,
  0x3c00370004,
  0x540290010601bc008c008e00790160005e008c008e015f,
  0xec00ec007b007800d700d600d501570004007e000400040158007d000400040004007f0086007001080108,
  0xec01bb0087008901080080008200040004008b0050,
  0x54015600ea007500d80081005401110007,
  0x5301560076015e0007000400710081,
  0x295008101ac0081005001bf005001a801a800500050008100500294008102930292005001af01af0050008100500291008100500050019a00500050019a028f008101a60081008100810081008100500081028e008100500081028d00810050005000500203020300810071028b028a028902880081007101a801a801a802030203005000500286028501af01af0050005000810071028202810280027f00810071,
  0x6d00480004,
  0x73010900840048017b008800880088008802970088017b0004000700ca008800070088017b004e00880007008800710004019b008f000400040088010f000702030088017b,
  0x109017b0088004e008802030007,
  0x73010700840061008800c900880088011001100203000700880088000700040061008f00040061017c02030088017b0203,
  0x1070088017b0110017c00070203,
  0x1620108016100ec0039004700390047019d0004000402030007005e02840007008e010802030007006102830007008f00ec0203,
  0xec01b90108016100ec0004008900040203,
  0x38004a0004,
  0x73010a0084004a016600880088029e00880166008800880004000700f700880004019c008f000400040088010e0007000700880166004f0088000700880071020300880166,
  0x10a01660088004f008802030007,
  0x7301060084005e008800f60088008800bf00bf02030004005e008f0004005e016502030007008800880007008801660203,
  0x1060088016600bf016500070203]
private def trees5 : Array ℕ := #[
  0x1070179017b0072011000880052010f0007,
  0x48006d0004,
  0xeb01bd008d008f017a02a40084017e0061008d008f017d,
  0x178017b0073017c0007000400710088,
  0x5401660106007200bf00880054010e0007,
  0x4a00380004,
  0x5402a800ea01be008d008f0084017f005e008d008f0180,
  0x10801080078007b00d600d700d501580004007d000400040157007e0004000400040086007f007000ec00ec,
  0x10801bb0080008200ec0087008900040004008b0050,
  0x530166007301650007000400710088,
  0x2ac008801ad008802ab02aa005001a801a800500088005002a90088005001c0005001af01af005000500088005002a700880050019d005000500050019d02a6008801a7008800880088008800880050008802a500880050008802a30088005000500050020302030088007102a202a102a0029f0088007100500050029d029c01a801a80050005001af01af01af0203020300880071029b029a0299029800880071,
  0x4b006a0007,
  0xfb00cb006a006a017c0061006102ae006100610061017c0007000401080061000701980064000700040083017c006e009000040061005000070061010f000702030088017c,
  0xcb017c0061006e006102030004,
  0x8800c9008800880073010700840061011001100203000700880088000700040061008f00040088017b02030061017c0203,
  0xc90073017c0110017b00040203,
  0x3d006c0007,
  0xfd00cc006c006c01590061006102b300610061006101590007000400ec006100070199006400070004008a0159006f00900004006100500007006101030007020300810159,
  0xcc01590061006f006102030004,
  0x8100c800810081007600eb00790061010201020203000700810081000700040061008e00040081015a0203006101590203,
  0xc8007601590102015a00040203,
  0xfa00ca016700f7003400690034006901a00007000702030004008102660004000400880265000400ca00ca0203006400f70203,
  0xf701c200ca016700f7000700ca00070203,
  0x74017c00c90074011000880074010f0004,
  0x77015900c8007701020081007701030004,
  0x6a004b0007,
  0xf601c600630064007402bc00c6013a008800740064016d,
  0x73017c0178017b0004000700710088,
  0x6c003d0007,
  0xf501c700630064007702bf00d9012a0081007700640182,
  0x760159015c015a0004000700710081,
  0xca00ca0055006900580069004d00590007005b0007000700fa00ca0007000700070060005c007100f700f7]
private def trees6 : Array ℕ := #[
  0xca01c5005d005f00f700fa00ca0007000700620071,
  0x2c302c2007101ab01ab007102c1006101aa00610071006102c0006102be006101b100610071006102bd00610061006100610061007101ae007101a501a500710071007101a000710071007101a00061007102bb00610061007102ba0061007100710071020302030071007102b902b801ab01ab007100710061005002b702b602b502b4006100500061005002b202b102b002af0061005001a501a501a502030203,
  0x9700aa00970203000c000c000c000c00090097000c009700aa0009001000090010000900090009000900090010000900100009000e0009000e00090009000900090009000e0009000e00090009000900090009000c000c000c000c00090097000c009700aa0009000c000c000c000c00090010001000090009000e000e0009,
  0xe000c00b1000e000e000e000e000e000c000e00b1000e000e00b100b1000c00b1000e000c000c000c000c000e00b100b1000c00b1000e000e000c00b1000e000c000c000c000c000e000c00b1000e000c000c000c000c000e000e000e000e000c000e00b100b100aa000e000e000e000e000e00b100aa00b10203000c000e00b100b100aa000e,
  0x10000c00b800100010001000100010001000b800aa001000b8000c0010001000100010000c001000b8001000100010001000100010000c00b80010000c000c000c000c00b800aa0010001000b8000c0010000c00b800100010000c00b800b800b80010000c000c000c000c00b800b800aa02030010000c00b800b800b80010000c000c000c000c,
  0x2030203,
  0xe00b100b1000e000e000e000e000e00b1000e00b1000e000e00b100b100b100b1000e00b500b3011d0071000e015200b1000e000e000e00b1000e00b1000e000e003301d7000e00b10033000e00b1000e000e000e00b1000e003300aa000e00b10033000e003300b100b100b1000e00b700b200710033000e003300b100b100b1000e00b600b40071003300330097000e00b1003300970071000e0097000e00b1000e00b1000e0097000e00b1003301e3000e00b100330071000e0097000e00b1000e00b1000e0097000e00b1003300aa000e00b100330071020302c8000e00b100b1020302c8003300970097,
  0x1000b800b80010001000b800b800b800b8001000bc00ba01130071001000100010001000b1001000b10010013e001000b100100010001000b8001000b800100010004001dd001000b800400010004000aa001000b80040001000b800100010001000b80010004000b800b800b8001000be00b90071004000bd00bb007100400010004000b100b100b1001000400097001000b800400097007100100097001000b8001000b800100097001000b8004001e2001000b800400071001000b8004000aa001000b80040007100100097001000b1001000b100100097020302c8001000b800b8020302c8004000970097,
  0x203,
  0x2c8020302cb,
  0x1ce0008000401cd000e0009000e0009,
  0x81007701d001d1000c00070071000c00aa0007000c0007000c00070088007401d601d50085007a02cd01cd0007000c000c0007007100070071007101d9000700710007007100070007000700710007007100070071000700710007007100070071007101d4000700710007007100070007000700710007007100070071000700710007000700710007007100070071007101e60071009700070071007101d40007009700710097000700b8007100b8000700970007007100070071007101e50007007100070071007101e000710097000700b1007100b10007009702cc02c800070071007102cc02c8000700710071,
  0xc004200a8000c000c004200a6000c00af00ad00420042000c000c00aa000c00aa000c0042000c00b800a800b8000c0042000c00b100a600b1000c000c011a00aa011a00aa000c00ac00ae011a004200ab00b0011a00420203009700970097000c000c000c000c000c00a8000c0042000c00a6000c0042000c000c00aa000c000c00aa000c011a0071000c00aa00aa,
  0x9d00aa00100010000e000e000c009d00aa000c00090010001000090009000e000e0009020300090009000c009700aa000c00ac00ae00a8004200ab00b000a60042000c009700090097000c0009000c000c0203020300a200aa000c00a2000c00aa020300970071,
  0xb8009700b800970071007100ca0071009700b800b8009700b1009700b10097009700970097009700b1009700b100970071009701d401dc01d400970097009700970097007101d3009700aa00aa00aa02d002cf009700970097009700970071007101d4007101d40071009700b800b800b800b800970071007100710071009700b100b100b100b1009700970097007100710097009700710071007100ca01a501b201d4007100710097009700b800b800b800b8009700970071007100ca00aa00aa00aa007100710097009700b100b100b100b10097009702cb02c800710071007102cb02c8009700970097,
  0x2cb,
  0x1cd01ce000800040009000e000e0009,
  0x900540097000900090004009700970097000900a0000400500004000900520097000900a3009d02d301ce0004009f00500004000900090097000900970009001000090010000900100009001000090010000900100009000900090097000900970009000e0009000e0009000e0009000e0009000e0009000e0009000900970009009700090097009701e100090097000900970009009700090097000e00b100090097000e00b100090097000e00b100090097000e00b100090097000e00b100090097000e00b10009009702d202c800090097009702d202c8000900970097,
  0xe000e000e000e000e00b100b100b100b1000e000e012500b1000e000e00b100b1000e000e00b100b1000e00b600b401290071000e006800b100b100b1000e000e006800b100b100b1000e00b300b50071006800b200b700710068000e000e00b1000e00b1000e000e00b1000e000e000e00b1000e006800aa000e00b10068000e006801d8000e00b10068000e00b100680097006800710097000e0097000e00b1000e00b1000e0097000e0097000e00b1000e00b1000e0097000e00b1006800aa000e00b100680071000e00b1006801e7000e00b100680071020302c8006800970097020302c8000e00b100b1,
  0x20302030203020302030203,
  0xc004200a8000c000c004200a6000c00af00ad00420042000c000c000c000c000c00a8000c0042000c00a6000c0042000c000c00aa000c00aa000c0042000c00b800a800b8000c0042000c00b100a600b1000c000c00aa000c000c000c00aa000c011a00aa011a00aa000c00ac00ae011a004200ab00b0011a0042011a0071000c000c00aa00aa0203009700970097,
  0x9d00aa00100010000e000e00a200aa000c009700aa000c00ac00ae00a8004200ab00b000a60042007100970203000c009700090097000c0009000c009d00aa000c00090010001000090009000e000e000900a2000c000c00aa02030009000902030203000c000c,
  0x10000900100009000e0009000e00090009000900090009000c000c000c000c00090010001000090009000e000e0009000c000c000c000c00090010001000090009000e000e0009000c000c000c000c000c00090097009700aa0009000900090009000900090009000900090097007100970203009700aa00970203,
  0xaf00ad004300430043000c00a9000c0043000c00a7000c000c00a9000c0043000c00a7000c0043000c000c000c000c0043000c00b800a900b8000c0043000c00b100a700b1000c000c000c00aa000c00aa000c000c00aa000c000c000c00aa00ac00ae00a9004300ab00b000a70043000c011900aa011900aa000c01190071000c000c00aa00aa0203009700970097,
  0x100010000e000e00a300aa009e00aa00ac00ae00a9004300ab00b000a70043000c009700aa000c007100970203000c009700090097000c000900090010001000090009000e000e0009000c00a300aa000c009e000c000c00aa02030009000902030203000c000c,
  0x900090009000900090010001000090009000e000e000900090010001000090009000e000e0009000c000c000c000c00090010001000090009000e000e0009000c000c000c000c000c000c000c000c00090009000900090009000900090009000c00090097009700aa00090097007100970203009700aa00970203,
  0xb8009700b8009700b1009700b10097009700970097009700aa00aa00aa00aa009700b800b80097009700b100b1009700aa009702dc02db02da00970097009700970097009700970097009700aa009702d902d802d7009700aa00aa00aa00aa009700b800b80097009700b100b1009700aa00aa00aa00aa02d601e001e401e0,
  0x1000b800b800b800b80010001000100010001000e9001000b10010001000b800b8001000bd00bb00dc0071001000b100b100100010009500b800b800b8001000ba00bc007100950010009500b100b100b1001000b900be007100950010001000b8001000b800100010009500aa001000b80095001000b800100010001000b80010009501cf001000b80095001000b80095009700950071009700100097001000b8001000b800100097001000b8009500aa001000b80095007100100097001000b1001000b100100097001000b8009501e8001000b800950071020302c8009500970097020302c8001000b800b8,
  0xaf00ad004300430043000c00a9000c0043000c00a7000c0043000c00b800a900b8000c0043000c00b100a700b1000c000c000c00aa000c00aa000c00ac00ae00a9004300ab00b000a70043000c011900aa011900aa000c0203009700970097000c00a9000c0043000c00a7000c0043000c000c000c000c000c000c00aa000c000c00aa000c01190071000c00aa00aa,
  0x100010000e000e00a300aa00090010001000090009000e000e0009000c00a300aa000c02030009000900ac00ae00a9004300ab00b000a70043000c009700aa000c000c009700090097000c0009000c000c02030203009e00aa000c009e000c00aa020300970071,
  0x9700b800b80097009700970097009700b1009700b10097009700b800b800970071007100f70071009700b100b100970097009700970097007101d2009700aa00aa00aa02e002df009700970097009700970071009701da01dc01d40097009700b800b800b800b800970071007100710071009700b100b100b100b100970071007101db007101d9007100970097007100710097009700710097009700b800b800b800b8009700970071007100f700aa00aa00aa007100710097009700b100b100b100b1009700970071007100f701ab01c901d40071007102cb02c800710071007102cb02c8009700970097,
  0x1fa01e602e101f201fb01e101e901ea01e601e102de01e601fe01e001f901f902dd01f501e601e001eb01e601f601e0020001e101fc01df01ef01ee01e601df02d501e601e101df02d401e101f101ec01ff01e001fd01de02d101f801e601de02ce01e601e101f302ca01ed01e001de01f401e001df01f702c901f0]
private def treesBlocks : Array (Array ℕ) := #[trees0, trees1, trees2, trees3, trees4, trees5, trees6]
private def trees (i : ℕ) : ℕ :=
  ((treesBlocks[i / 32]?).getD #[])[i % 32]?.getD 0
private def checkBlock (b : ℕ) : Bool :=
  (List.range 32).all fun j =>
    let i := b+17*j
    decide (514 ≤ i) || checkQuery bank 514 trees (bank i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked0 : checkBlock 0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked1 : checkBlock 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked2 : checkBlock 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked3 : checkBlock 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked4 : checkBlock 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked5 : checkBlock 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked6 : checkBlock 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked7 : checkBlock 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked8 : checkBlock 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked9 : checkBlock 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked10 : checkBlock 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked11 : checkBlock 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked12 : checkBlock 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked13 : checkBlock 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked14 : checkBlock 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked15 : checkBlock 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked16 : checkBlock 16 = true := by decide +kernel
private theorem bankChecked  : ∀ i < 514, checkQuery bank 514 trees (bank i) = true := by
  intro i hi
  have good (b : ℕ) (hb : b < 17) : checkBlock b = true := by
    interval_cases b
    · exact checked0
    · exact checked1
    · exact checked2
    · exact checked3
    · exact checked4
    · exact checked5
    · exact checked6
    · exact checked7
    · exact checked8
    · exact checked9
    · exact checked10
    · exact checked11
    · exact checked12
    · exact checked13
    · exact checked14
    · exact checked15
    · exact checked16
  have H := good (i % 17) (by omega)
  unfold checkBlock at H
  have t := List.all_eq_true.mp H (i / 17) (List.mem_range.mpr (by omega))
  have eq : (i % 17) + 17 * (i / 17) = i := by omega
  simpa only [eq,show ¬514 ≤ i by omega, decide_false,Bool.false_or] using t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem rejectBuild {g : W} (hg : g = goal ∨ g = ~~~goal)
    (run : build basicOps g 10 rows.toFinset) : False := by
  have h := bank_sound bankChecked 513 (by decide)
  have xs : (bank 513).1.2.2.toFinset = rows.toFinset := by decide +kernel
  have cap : (bank 513).1.2.1 = 10 := by decide +kernel
  apply h g hg
  rw [xs,cap]
  exact run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 10 < binaryCost gs :=
  bound_from_search rows rfl (fun _ hg run => rejectBuild hg run) (by decide +kernel) gs o hg he

end PEqualNP.Outside.L_meta_10868.Signed


namespace PEqualNP.Outside.L_meta_10868

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = Signed.F x := by
  decide +kernel

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3,6]⟩, ⟨.or, [0,5]⟩, ⟨.and, [7,8]⟩, ⟨.or, [1,4]⟩, ⟨.or, [2,10]⟩, ⟨.and, [6,11]⟩, ⟨.or, [0,2]⟩, ⟨.and, [5,13]⟩, ⟨.and, [4,1]⟩, ⟨.or, [9,12]⟩, ⟨.or, [14,15]⟩, ⟨.or, [16,17]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10868

theorem PEqualNP.Outside.L_meta_10868 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_10868.Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_10868.Signed.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_10868.Signed.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_10868.Signed.bound gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_10868.bridge x))
    have hl : PEqualNP.Outside.L_meta_10868.wg.length = 12 := rfl
    exact ⟨PEqualNP.Outside.L_meta_10868.wg, 18, PEqualNP.Outside.L_meta_10868.wfits, by omega, PEqualNP.Outside.L_meta_10868.weval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
