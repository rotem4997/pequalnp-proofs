import PEqualNP.Defs

-- Signed live-wire checker adapted from L_meta_10916 and L_meta_9564 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_11205.Signed

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
abbrev W := BitVec 90
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 45 := ((x >>> 45) ^^^ x).setWidth 45
def cuts (ws : List W) : BitVec 45 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 45) ++ (0 : BitVec 45)
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

def differs (i : Fin 45) (w : W) : Prop :=
  w.getLsbD (45+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 45) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 45+i.val < 90 := by omega
  have hi' : i.val < 90 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 45) :
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
  change (cuts ws)[j] = (BitVec.allOnes 45)[j]
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
  · change reachable av (BitVec.allOnes 90 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 90)
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

private def bit (k : Fin 90) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 90) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 90) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#90)[k.val] = false; simp
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


def src (i j : Nat) := if j = i then 0 else if j = 45+i then 45 else j
def proj (i : Nat) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 90 => w.getLsbD (src i j.val)))).cast (List.length_ofFn)
theorem src_lt (i j : Nat) (hj : j < 90) : src i j < 90 := by
  unfold src; split <;> first | split <;> omega | omega
set_option maxRecDepth 16000 in
theorem project_bit (i j : Nat) (w : W) (hj : j < 90) :
    (proj i w).getLsbD j = w.getLsbD (src i j) := by
  rw [proj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]; simp only [List.getElem?_ofFn, dif_pos hj, Option.getD_some]
theorem p_and (i : Nat) (a b : W) : proj i (a &&& b) = proj i a &&& proj i b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit i j _ hj, BitVec.getLsbD_and]
theorem p_or (i : Nat) (a b : W) : proj i (a ||| b) = proj i a ||| proj i b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit i j _ hj, BitVec.getLsbD_or]
theorem p_not (i : Nat) (a : W) : proj i (~~~a) = ~~~proj i a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit i j _ hj, BitVec.getLsbD_not, src_lt i j hj, hj, decide_true, Bool.true_and]

def simple (w : W) := w = 0 ∨ w = ~~~0
def clean (i : Fin 45) (A : Finset W) := ∀ u ∈ A, differs i u → simple (proj i u)
theorem reach_proj (i : Fin 45) {a b z : W} {D : Finset W} (ha : holds D (proj i a))
    (hb : holds D (proj i b)) (hz : z ∈ basicOps a b) : reachable D (proj i z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> simp only [p_and,p_or,p_not]
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)
theorem free_proj (i : Fin 45) {a b z : W} {D : Finset W} (ha : holds D (proj i a))
    (hb : holds D (proj i b)) (hz : z ∈ basicOps a b)
    (hc : simple (proj i a) ∨ simple (proj i b)) : holds D (proj i z) := by
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

theorem shrink (i : Fin 45) (fixed : proj i goal = goal)
    {t : W} (ht : t = goal ∨ t = ~~~goal) (hd : differs i t) (k : Nat)
    {A D : Finset W} (mapA : ∀ u ∈ A, holds D (proj i u)) (h : build basicOps t k A) :
    ∃ q m, (q = goal ∨ q = ~~~goal) ∧ build basicOps q m D ∧ m ≤ k ∧ (clean i A → m < k) := by
  induction k generalizing A D with
  | zero =>
    have hv := mapA t h
    have ps : proj i t = goal ∨ proj i t = ~~~goal := by
      rcases ht with rfl|rfl
      · exact .inl fixed
      · exact .inr ((p_not ..).trans (congrArg (fun w : W => ~~~w) fixed))
    have nons : ¬ simple (proj i t) := by
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
    by_cases old : holds D (proj i z)
    · have extA : ∀ u ∈ insert z A, holds D (proj i u) := by
        intro u hu; rcases Finset.mem_insert.mp hu with rfl|hu
        · exact old
        · exact mapA u hu
      obtain ⟨q,m,hq,hr,hl,_⟩ := ih extA tail
      exact ⟨q,m,hq,hr,by omega,fun _ => by omega⟩
    · rcases reach_proj i (mapA a ha) (mapA b hb) hz with h0|⟨x,hx,y,hy,ne,w,op,rep⟩
      · contradiction
      have extA : ∀ u ∈ insert z A, holds (insert w D) (proj i u) := by
        intro u hu; rcases Finset.mem_insert.mp hu with rfl|hu
        · exact rep
        · exact holds_insert (mapA u hu)
      obtain ⟨q,m,hq,hr,hl,hcl⟩ := ih extA tail
      refine ⟨q,m+1,hq,.inr ⟨x,hx,y,hy,ne,w,op,hr⟩,by omega,?_⟩
      intro orig
      have next : clean i (insert z A) := by
        intro u hu diff
        rcases Finset.mem_insert.mp hu with rfl|hu
        · rcases ops_differs i a b u hz diff with da|db
          · exact (old (free_proj i (mapA a ha) (mapA b hb) hz (.inl (orig a ha da)))).elim
          · exact (old (free_proj i (mapA a ha) (mapA b hb) hz (.inr (orig b hb db)))).elim
        · exact orig u hu diff
      have := hcl next
      omega
def rows : List W := [0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x100000000000, 0x105003c0029487801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]

def reduced : List W := [0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]

theorem cleanLeaf : clean 44 rows.toFinset := by
  intro u hu
  have hm := List.mem_toFinset.mp hu
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs simple <;> decide +kernel

theorem mapLeaf : ∀ u ∈ rows.toFinset, holds reduced.toFinset (proj 44 u) := by
  intro u hu
  have hm := List.mem_toFinset.mp hu
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr ⟨0x2408c4366463204e63b3273, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0xa50182d28007384c3f9c, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x8cf811a87c0467c18fc3e0, by decide, .inl (by decide +kernel)⟩)
  · exact .inl (by decide +kernel)
  · exact .inr (.inr ⟨0x105003c0029587801f003ff, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x150002e55000f8001fffc00, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0xaa528000000ffffe000000, by decide, .inl (by decide +kernel)⟩)

abbrev State := ℕ × List W

def children (extra : ℕ) (ws : List W) : List State :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun w =>
      let v := sep w ||| cuts r
      (if v == -1 then [(extra, w :: r)] else []) ++
      (if extra != 0 && (v ||| sep a == -1) then [(extra-1, w :: a :: r)] else []) ++
      (if extra != 0 && (v ||| sep b == -1) then [(extra-1, w :: b :: r)] else []) ++
      (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra-2, w :: a :: b :: r)] else [])

theorem child_of_search {k extra : ℕ} {ws : List W}
    (unfinished : (ws == [goal] || ws == [~~~goal]) = false)
    (found : optimized (k+1) extra ws = true) :
    ∃ s ∈ children extra ws, optimized k s.1 s.2 = true := by
  simp only [optimized, unfinished, Bool.false_or, List.any_eq_true] at found
  rcases found with ⟨⟨a,b,r⟩,hp,h⟩
  simp only [dispatch, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h
  obtain ⟨w,hw,h⟩ := h
  have insertChild (s : State) (hh : s ∈
      (if (sep w ||| cuts r) == -1 then [(extra, w :: r)] else []) ++
      (if extra != 0 && ((sep w ||| cuts r) ||| sep a == -1) then [(extra-1, w :: a :: r)] else []) ++
      (if extra != 0 && ((sep w ||| cuts r) ||| sep b == -1) then [(extra-1, w :: b :: r)] else []) ++
      (if extra ≥ 2 && ((sep w ||| cuts r) ||| sep a ||| sep b == -1) then [(extra-2, w :: a :: b :: r)] else [])) :
      s ∈ children extra ws :=
    List.mem_flatMap.mpr ⟨(a,b,r),hp,List.mem_flatMap.mpr ⟨w,hw,hh⟩⟩
  rcases h with ((⟨hv,run⟩ | ⟨he,(⟨hv,run⟩ | ⟨hv,run⟩)⟩) | ⟨⟨he,hv⟩,run⟩)
  · exact ⟨_,insertChild (_,_) (by simp only [hv, Bool.true_and, if_true, List.mem_append, List.mem_singleton] <;> tauto),run⟩
  · exact ⟨_,insertChild (_,_) (by simp only [he,hv, Bool.true_and, if_true, List.mem_append, List.mem_singleton] <;> tauto),run⟩
  · exact ⟨_,insertChild (_,_) (by simp only [he,hv, Bool.true_and, if_true, List.mem_append, List.mem_singleton] <;> tauto),run⟩
  · exact ⟨_,insertChild (_,_) (by simp only [he,hv, Bool.true_and, if_true, List.mem_append, List.mem_singleton] <;> tauto),run⟩

def AllBefore (P : ℕ → Prop) : ℕ → Prop
  | 0 => True
  | n+1 => AllBefore P n ∧ P n

theorem allBefore_mem {P : ℕ → Prop} {n : ℕ} (ok : AllBefore P n) {i : ℕ} (hi : i < n) : P i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases e : i = n
    · exact e ▸ ok.2
    · exact ih ok.1 (by omega)

def rejects (k : Nat) (s : State) : Prop := optimized k s.1 s.2 = false

theorem rejectChildren (k : Nat) (s : State) (n : Nat)
    (hn : (children s.1 s.2).length = n)
    (unfinished : (s.2 == [goal] || s.2 == [~~~goal]) = false)
    (ok : AllBefore (fun j => rejects k ((children s.1 s.2).getD j (0,[]))) n) :
    rejects (k+1) s := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨c, hc, run⟩ := child_of_search unfinished h
  obtain ⟨i, hi, eq⟩ := List.getElem_of_mem hc
  have he := allBefore_mem ok (hn ▸ hi)
  change optimized k _ _ = false at he
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, eq] at he
  exact Bool.noConfusion (he.symm.trans run)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject1 : rejects 7 (1, [0x84010242000420083210, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject3 : rejects 6 (1, [0xa50182d28007384c3f9c, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject4 : rejects 6 (0, [0xa50182d28007384c3f9c, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject5 : rejects 6 (1, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject6 : rejects 6 (0, [0x240ad43e6d6b207fe7f3fff, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject7 : rejects 6 (1, [0x240084264043200c6330063, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject8 : rejects 6 (1, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject9 : rejects 6 (0, [0x240084264043200c6330063, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject10 : rejects 6 (0, [0x0, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject11 : rejects 6 (0, [0xa801a0540007c00f03e0, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject12 : rejects 6 (0, [0x2ccfd53eefeb667ffffffff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject13 : rejects 6 (0, [0x24005424682b2003e703c1f, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject14 : rejects 6 (0, [0x8c5010082804600180c000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject15 : rejects 6 (0, [0x1000007003ff, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject16 : rejects 6 (0, [0x345ad7fe6fffa7fffff3fff, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject17 : rejects 6 (0, [0x240ad43e6d6a207fe0f3c00, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject18 : rejects 6 (0, [0x105003c0029487801800000, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject19 : rejects 6 (0, [0x40000244000200007f3c00, 0x240ad43e6d6b207fe7f3fff, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject20 : rejects 6 (0, [0x350ad6ff7d6bf87ffffffff, 0x240ad43e6d6b207fe7f3fff, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject21 : rejects 6 (0, [0x200ad41a2d6b007fe0003ff, 0x240ad43e6d6b207fe7f3fff, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject22 : rejects 6 (0, [0x110002c11000d800180c000, 0x240ad43e6d6b207fe7f3fff, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject23 : rejects 6 (0, [0x207fe000000, 0x240ad43e6d6b207fe7f3fff, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject24 : rejects 6 (0, [0x2eaffc3e6d6bffffe7f3fff, 0x240ad43e6d6b207fe7f3fff, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject25 : rejects 6 (0, [0x240ad43e6d6b000007f3fff, 0x240ad43e6d6b207fe7f3fff, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject26 : rejects 6 (0, [0xaa528000000df800000000, 0x240ad43e6d6b207fe7f3fff, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject27 : rejects 6 (0, [0xa00180500007000c0380, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject28 : rejects 6 (2, [0x8cfd11aafe8467f9cffffc, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject29 : rejects 6 (1, [0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject30 : rejects 6 (1, [0x8cfd11aafe8467f9cffffc, 0x8cf811a87c0467c18fc3e0, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject31 : rejects 6 (0, [0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject32 : rejects 6 (1, [0x5000282800038403c1c, 0x8cf811a87c0467c18fc3e0, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject33 : rejects 6 (0, [0x5000282800038403c1c, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject34 : rejects 6 (1, [0x8c5810282c0460c183c060, 0xa50182d28007384c3f9c, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject35 : rejects 6 (0, [0x8c5810282c0460c183c060, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x240ad43e6d6b207fe7f3fff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject36 : rejects 6 (0, [0x40039c, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject37 : rejects 6 (1, [0x105a53d82fbd87f39fc3fff, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject38 : rejects 6 (0, [0x105a53d82fbd87f39fc3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject39 : rejects 6 (1, [0xa50182d28007380c3c00, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject40 : rejects 6 (0, [0xa50182d28007380c3c00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject41 : rejects 6 (0, [0x105003c0029587801b00063, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject42 : rejects 6 (1, [0x4c3c00, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject43 : rejects 6 (0, [0x4c3c00, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject44 : rejects 6 (0, [0x150a52fd7d28f8739ffff9c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject45 : rejects 6 (0, [0xa50182d280073800039c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject46 : rejects 6 (1, [0x150002e55000f8001b3c000, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject47 : rejects 6 (0, [0x150002e55000f8001b3c000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject48 : rejects 6 (0, [0x738000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject49 : rejects 6 (1, [0xaaf78182d28ffffe4c3f9c, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject50 : rejects 6 (0, [0xaaf78182d28ffffe4c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject51 : rejects 6 (1, [0xa50182d28000004c3f9c, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject52 : rejects 6 (0, [0xa50182d28000004c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject53 : rejects 6 (0, [0xaa528000000ff8c6000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject54 : rejects 6 (0, [0x4001000280060018003e0, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject55 : rejects 6 (0, [0x18df83da87d5c7fc1ffc3ff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject56 : rejects 6 (0, [0x88f801a8540407c00fc000, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject57 : rejects 6 (0, [0x101002c000158180070001f, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject58 : rejects 6 (1, [0x400018fc000, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject59 : rejects 6 (0, [0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject60 : rejects 6 (0, [0x1dcf83ffd7c0fe7c1ffffe0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject61 : rejects 6 (0, [0x8cf811a87c0067c00003e0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject62 : rejects 6 (1, [0x150002e55000b8000703c00, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject63 : rejects 6 (0, [0x150002e55000b8000703c00, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject64 : rejects 6 (0, [0x88500000000467c0000000, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject65 : rejects 6 (1, [0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject66 : rejects 6 (0, [0xaefa91a87c0fffff8fc3e0, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject67 : rejects 6 (1, [0x4a811a87c0000018fc3e0, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject68 : rejects 6 (0, [0x4a811a87c0000018fc3e0, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject69 : rejects 6 (0, [0x22028000000b983e000000, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject70 : rejects 6 (0, [0x100002c0000080001f00000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject71 : rejects 6 (0, [0x155003e55295ff801ffffff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject72 : rejects 6 (0, [0x5001000295078000003ff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject73 : rejects 6 (0, [0x50000255000780000ffc00, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject74 : rejects 6 (0, [0x87800000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject75 : rejects 6 (0, [0x1af52bc00295ffffff003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject76 : rejects 6 (0, [0x105003c0029500001f003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject77 : rejects 6 (0, [0xaa528000000787fe000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject78 : rejects 6 (0, [0xf8000000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject79 : rejects 6 (0, [0x1fa52ae55000ffffffffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject80 : rejects 6 (0, [0x150002e5500000001fffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject81 : rejects 6 (0, [0xaa52800000007ffe000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject2 : rejects 7 (2, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by
  apply rejectChildren 6 _ 79 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, reject3⟩, reject4⟩, reject5⟩, reject6⟩, reject7⟩, reject8⟩, reject9⟩, reject10⟩, reject11⟩, reject12⟩, reject13⟩, reject14⟩, reject15⟩, reject16⟩, reject17⟩, reject18⟩, reject19⟩, reject20⟩, reject21⟩, reject22⟩, reject23⟩, reject24⟩, reject25⟩, reject26⟩, reject27⟩, reject28⟩, reject29⟩, reject30⟩, reject31⟩, reject32⟩, reject33⟩, reject34⟩, reject35⟩, reject36⟩, reject37⟩, reject38⟩, reject39⟩, reject40⟩, reject41⟩, reject42⟩, reject43⟩, reject44⟩, reject45⟩, reject46⟩, reject47⟩, reject48⟩, reject49⟩, reject50⟩, reject51⟩, reject52⟩, reject53⟩, reject54⟩, reject55⟩, reject56⟩, reject57⟩, reject58⟩, reject59⟩, reject60⟩, reject61⟩, reject62⟩, reject63⟩, reject64⟩, reject65⟩, reject66⟩, reject67⟩, reject68⟩, reject69⟩, reject70⟩, reject71⟩, reject72⟩, reject73⟩, reject74⟩, reject75⟩, reject76⟩, reject77⟩, reject78⟩, reject79⟩, reject80⟩, reject81⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject82 : rejects 7 (1, [0x240ad43e6d6b207fe7f3fff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject83 : rejects 7 (2, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject84 : rejects 7 (1, [0x240084264043200c6330063, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject85 : rejects 7 (1, [0x21008090800318440d8c, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject86 : rejects 7 (1, [0x880120440004c00b0260, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject87 : rejects 7 (1, [0x2ccfc53ee7e3667e7bff3f3, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject88 : rejects 7 (1, [0x24004424602320026303013, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject89 : rejects 7 (1, [0x8c7010883804630184c180, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject90 : rejects 7 (1, [0x100000300273, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject91 : rejects 7 (1, [0x3458c7f666f7a7ce7fb33ff, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject92 : rejects 7 (1, [0x2408c4366462204e60b3000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject93 : rejects 7 (1, [0x105003c0029487801c0018c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject94 : rejects 7 (1, [0x40000244000200003b3000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject95 : rejects 7 (1, [0x3508c6f77463f84e7fffe73, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject96 : rejects 7 (1, [0x2008c4122463004e6000273, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject97 : rejects 7 (1, [0x110002c11000d8001c4cc00, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject98 : rejects 7 (1, [0x204e6000000, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject99 : rejects 7 (1, [0x2eadec366463ffffe3b3273, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject100 : rejects 7 (1, [0x2408c4366463000003b3273, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject101 : rejects 7 (1, [0xaa528000000dfb18000000, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject102 : rejects 7 (1, [0xa00180500007000c0380, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject104 : rejects 6 (1, [0xa50182d28007384c3f9c, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject105 : rejects 6 (0, [0xa50182d28007384c3f9c, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject106 : rejects 6 (1, [0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject107 : rejects 6 (0, [0x8cfd11aafe8467f9cffffc, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject108 : rejects 6 (1, [0x8c5810282c0460c183c060, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject109 : rejects 6 (1, [0x8c5810282c0460c183c060, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject110 : rejects 6 (0, [0x8c5810282c0460c183c060, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject111 : rejects 6 (0, [0x0, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject112 : rejects 6 (0, [0x8c0122460004e00b3270, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject113 : rejects 6 (0, [0x2ccfd53eefeb667ffffffff, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject114 : rejects 6 (0, [0x8c711088b8846319c4cd8c, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject115 : rejects 6 (0, [0x24000424400320006300003, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject116 : rejects 6 (0, [0x400100028006001c003fc, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject117 : rejects 6 (0, [0x18dfd3daaffdc7ff9ffffff, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject118 : rejects 6 (0, [0x88fd01aad68407f80ffc00, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject119 : rejects 6 (0, [0x101002c0001581800300003, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject120 : rejects 6 (1, [0x40001cffc00, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject121 : rejects 6 (0, [0x40001cffc00, 0x8cfd11aafe8467f9cffffc, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject122 : rejects 6 (0, [0x1dcfd3ffffe8fe7f9fffffc, 0x8cfd11aafe8467f9cffffc, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject123 : rejects 6 (0, [0x8cfd11aafe8067f80003fc, 0x8cfd11aafe8467f9cffffc, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject124 : rejects 6 (1, [0x150002e55000b8000300000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject125 : rejects 6 (0, [0x150002e55000b8000300000, 0x8cfd11aafe8467f9cffffc, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject126 : rejects 6 (0, [0x88500000000467f8000000, 0x8cfd11aafe8467f9cffffc, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject127 : rejects 6 (1, [0xaeff91aafe8fffffcffffc, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject128 : rejects 6 (0, [0xaeff91aafe8fffffcffffc, 0x8cfd11aafe8467f9cffffc, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject129 : rejects 6 (1, [0x4ad11aafe800001cffffc, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject130 : rejects 6 (0, [0x4ad11aafe800001cffffc, 0x8cfd11aafe8467f9cffffc, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject131 : rejects 6 (0, [0x22028000000b9806000000, 0x8cfd11aafe8467f9cffffc, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject132 : rejects 6 (0, [0x84010242000420083210, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject133 : rejects 6 (2, [0x240ad43e6d6b207fe7f3fff, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject134 : rejects 6 (1, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject135 : rejects 6 (1, [0x240ad43e6d6b207fe7f3fff, 0x2408c4366463204e63b3273, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject136 : rejects 6 (0, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject137 : rejects 6 (1, [0x21008090800318440d8c, 0x2408c4366463204e63b3273, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject138 : rejects 6 (0, [0x21008090800318440d8c, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject139 : rejects 6 (1, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject140 : rejects 6 (0, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x8cfd11aafe8467f9cffffc, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject141 : rejects 6 (0, [0x40039c, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject142 : rejects 6 (0, [0x105a53d82fbd87f39fc3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject143 : rejects 6 (0, [0xa50182d28007380c3c00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject144 : rejects 6 (0, [0x105003c0029587801b00063, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject145 : rejects 6 (0, [0x4c3c00, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject146 : rejects 6 (1, [0x150a52fd7d28f8739ffff9c, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject147 : rejects 6 (0, [0x150a52fd7d28f8739ffff9c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject148 : rejects 6 (1, [0xa50182d280073800039c, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject149 : rejects 6 (0, [0xa50182d280073800039c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject150 : rejects 6 (0, [0x150002e55000f8001b3c000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject151 : rejects 6 (0, [0x738000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject152 : rejects 6 (0, [0xaaf78182d28ffffe4c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject153 : rejects 6 (0, [0xa50182d28000004c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject154 : rejects 6 (0, [0xaa528000000ff8c6000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject155 : rejects 6 (0, [0x100000300273, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject156 : rejects 6 (0, [0x3458c7f666f7a7ce7fb33ff, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject157 : rejects 6 (0, [0x2408c4366462204e60b3000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject158 : rejects 6 (0, [0x105003c0029487801c0018c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject159 : rejects 6 (0, [0x40000244000200003b3000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject160 : rejects 6 (0, [0x3508c6f77463f84e7fffe73, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject161 : rejects 6 (0, [0x2008c4122463004e6000273, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject162 : rejects 6 (0, [0x110002c11000d8001c4cc00, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject163 : rejects 6 (0, [0x204e6000000, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject164 : rejects 6 (0, [0x2eadec366463ffffe3b3273, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject165 : rejects 6 (0, [0x2408c4366463000003b3273, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject166 : rejects 6 (0, [0xaa528000000dfb18000000, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject167 : rejects 6 (0, [0x100002c0000080001f00000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject168 : rejects 6 (0, [0x155003e55295ff801ffffff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject169 : rejects 6 (0, [0x5001000295078000003ff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject170 : rejects 6 (0, [0x50000255000780000ffc00, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject171 : rejects 6 (0, [0x87800000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject172 : rejects 6 (0, [0x1af52bc00295ffffff003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject173 : rejects 6 (0, [0x105003c0029500001f003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject174 : rejects 6 (0, [0xaa528000000787fe000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject175 : rejects 6 (0, [0xf8000000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject176 : rejects 6 (0, [0x1fa52ae55000ffffffffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject177 : rejects 6 (0, [0x150002e5500000001fffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject178 : rejects 6 (0, [0xaa52800000007ffe000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject103 : rejects 7 (2, [0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by
  apply rejectChildren 6 _ 75 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, reject104⟩, reject105⟩, reject106⟩, reject107⟩, reject108⟩, reject109⟩, reject110⟩, reject111⟩, reject112⟩, reject113⟩, reject114⟩, reject115⟩, reject116⟩, reject117⟩, reject118⟩, reject119⟩, reject120⟩, reject121⟩, reject122⟩, reject123⟩, reject124⟩, reject125⟩, reject126⟩, reject127⟩, reject128⟩, reject129⟩, reject130⟩, reject131⟩, reject132⟩, reject133⟩, reject134⟩, reject135⟩, reject136⟩, reject137⟩, reject138⟩, reject139⟩, reject140⟩, reject141⟩, reject142⟩, reject143⟩, reject144⟩, reject145⟩, reject146⟩, reject147⟩, reject148⟩, reject149⟩, reject150⟩, reject151⟩, reject152⟩, reject153⟩, reject154⟩, reject155⟩, reject156⟩, reject157⟩, reject158⟩, reject159⟩, reject160⟩, reject161⟩, reject162⟩, reject163⟩, reject164⟩, reject165⟩, reject166⟩, reject167⟩, reject168⟩, reject169⟩, reject170⟩, reject171⟩, reject172⟩, reject173⟩, reject174⟩, reject175⟩, reject176⟩, reject177⟩, reject178⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject179 : rejects 7 (1, [0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject180 : rejects 7 (1, [0x5000282800038403c1c, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject181 : rejects 7 (2, [0x8c5810282c0460c183c060, 0xa50182d28007384c3f9c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject182 : rejects 7 (1, [0x8c5810282c0460c183c060, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject183 : rejects 7 (1, [0x40039c, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject184 : rejects 7 (1, [0x105a53d82fbd87f39fc3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject185 : rejects 7 (1, [0xa50182d28007380c3c00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject186 : rejects 7 (1, [0x105003c0029587801b00063, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject187 : rejects 7 (1, [0x4c3c00, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject188 : rejects 7 (1, [0x150a52fd7d28f8739ffff9c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject189 : rejects 7 (1, [0xa50182d280073800039c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject190 : rejects 7 (1, [0x150002e55000f8001b3c000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject191 : rejects 7 (1, [0x738000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject192 : rejects 7 (1, [0xaaf78182d28ffffe4c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject193 : rejects 7 (1, [0xa50182d28000004c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject194 : rejects 7 (1, [0xaa528000000ff8c6000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject195 : rejects 7 (1, [0x4001000280060018003e0, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject196 : rejects 7 (1, [0x18df83da87d5c7fc1ffc3ff, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject197 : rejects 7 (1, [0x88f801a8540407c00fc000, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject198 : rejects 7 (1, [0x101002c000158180070001f, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject200 : rejects 6 (1, [0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject201 : rejects 6 (0, [0x400018fc000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject202 : rejects 6 (1, [0x150002e55000f8001fffc00, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject203 : rejects 6 (0, [0x150002e55000f8001fffc00, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject204 : rejects 6 (0, [0x0, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject205 : rejects 6 (1, [0x150002e55000b8000703c00, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject206 : rejects 6 (1, [0x150002e55000b8000703c00, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject207 : rejects 6 (0, [0x150002e55000b8000703c00, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject208 : rejects 6 (0, [0xb0000, 0x400018fc000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject209 : rejects 6 (1, [0x2408c4366463604e7bff273, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject210 : rejects 6 (0, [0x2408c4366463604e7bff273, 0x400018fc000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject211 : rejects 6 (0, [0x4000184c000, 0x400018fc000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject212 : rejects 6 (1, [0x2408c4366463204e6303273, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject213 : rejects 6 (0, [0x2408c4366463204e6303273, 0x400018fc000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject214 : rejects 6 (0, [0xc0000, 0x400018fc000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject215 : rejects 6 (2, [0xa50182d2840739cfff9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject216 : rejects 6 (1, [0xa50182d2840739cfff9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject217 : rejects 6 (1, [0xa50182d2840739cfff9c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject218 : rejects 6 (0, [0xa50182d2840739cfff9c, 0x400018fc000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject219 : rejects 6 (1, [0x4000183c000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject220 : rejects 6 (0, [0x4000183c000, 0x400018fc000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject221 : rejects 6 (1, [0xa50182d2800738403f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject222 : rejects 6 (0, [0xa50182d2800738403f9c, 0x400018fc000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject223 : rejects 6 (0, [0x1800000, 0x400018fc000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject224 : rejects 6 (1, [0x105003c00295c7801ffc3ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject225 : rejects 6 (0, [0x105003c00295c7801ffc3ff, 0x400018fc000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject226 : rejects 6 (0, [0x400000fc000, 0x400018fc000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject227 : rejects 6 (1, [0x105003c00295878007003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject228 : rejects 6 (0, [0x105003c00295878007003ff, 0x400018fc000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject229 : rejects 6 (0, [0x40000000000, 0x400018fc000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject230 : rejects 6 (2, [0xaa528000000fffff8fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject231 : rejects 6 (1, [0xaa528000000fffff8fc000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject232 : rejects 6 (1, [0xaa528000000fffff8fc000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject233 : rejects 6 (0, [0xaa528000000fffff8fc000, 0x400018fc000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject234 : rejects 6 (1, [0x18fc000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject235 : rejects 6 (0, [0x18fc000, 0x400018fc000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject236 : rejects 6 (1, [0xaa528000000bfffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject237 : rejects 6 (0, [0xaa528000000bfffe000000, 0x400018fc000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject238 : rejects 6 (0, [0x40000244000200003b3000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x400018fc000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject239 : rejects 6 (0, [0x3508c6f77463f84e7fffe73, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x400018fc000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject240 : rejects 6 (0, [0x110002c11000d8001c4cc00, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x400018fc000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject241 : rejects 6 (0, [0x2008c4122463004e6000273, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x400018fc000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject242 : rejects 6 (0, [0x4c3c00, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x400018fc000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject243 : rejects 6 (0, [0x150a52fd7d28f8739ffff9c, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x400018fc000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject244 : rejects 6 (0, [0x150002e55000f8001b3c000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x400018fc000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject245 : rejects 6 (0, [0xa50182d280073800039c, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x400018fc000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject246 : rejects 6 (0, [0x100002c0000080001f00000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject247 : rejects 6 (1, [0x155003e55295ff801ffffff, 0x105003c0029587801f003ff, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject248 : rejects 6 (0, [0x155003e55295ff801ffffff, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject249 : rejects 6 (1, [0x50000255000780000ffc00, 0x105003c0029587801f003ff, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject250 : rejects 6 (0, [0x50000255000780000ffc00, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject251 : rejects 6 (0, [0x5001000295078000003ff, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject252 : rejects 6 (0, [0xf8000000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject253 : rejects 6 (0, [0x1fa52ae55000ffffffffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject254 : rejects 6 (0, [0x150002e5500000001fffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject255 : rejects 6 (0, [0xaa52800000007ffe000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject256 : rejects 6 (0, [0x84010242000420083210, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject257 : rejects 6 (1, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject258 : rejects 6 (0, [0x240ad43e6d6b207fe7f3fff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject259 : rejects 6 (1, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject260 : rejects 6 (0, [0x240084264043200c6330063, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject261 : rejects 6 (0, [0x21008090800318440d8c, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject262 : rejects 6 (0, [0x100000300273, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject263 : rejects 6 (0, [0x3458c7f666f7a7ce7fb33ff, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject264 : rejects 6 (0, [0x2408c4366462204e60b3000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject265 : rejects 6 (0, [0x105003c0029487801c0018c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject266 : rejects 6 (0, [0x204e6000000, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject267 : rejects 6 (0, [0x2eadec366463ffffe3b3273, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject268 : rejects 6 (0, [0x2408c4366463000003b3273, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject269 : rejects 6 (0, [0xaa528000000dfb18000000, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject270 : rejects 6 (0, [0x40039c, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject271 : rejects 6 (0, [0x105a53d82fbd87f39fc3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject272 : rejects 6 (0, [0xa50182d28007380c3c00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject273 : rejects 6 (0, [0x105003c0029587801b00063, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject274 : rejects 6 (0, [0x738000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject275 : rejects 6 (0, [0xaaf78182d28ffffe4c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject276 : rejects 6 (0, [0xa50182d28000004c3f9c, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject277 : rejects 6 (0, [0xaa528000000ff8c6000000, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject278 : rejects 6 (0, [0x87800000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject279 : rejects 6 (0, [0x1af52bc00295ffffff003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject280 : rejects 6 (0, [0x105003c0029500001f003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject281 : rejects 6 (0, [0xaa528000000787fe000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject199 : rejects 7 (2, [0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by
  apply rejectChildren 6 _ 82 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, reject200⟩, reject201⟩, reject202⟩, reject203⟩, reject204⟩, reject205⟩, reject206⟩, reject207⟩, reject208⟩, reject209⟩, reject210⟩, reject211⟩, reject212⟩, reject213⟩, reject214⟩, reject215⟩, reject216⟩, reject217⟩, reject218⟩, reject219⟩, reject220⟩, reject221⟩, reject222⟩, reject223⟩, reject224⟩, reject225⟩, reject226⟩, reject227⟩, reject228⟩, reject229⟩, reject230⟩, reject231⟩, reject232⟩, reject233⟩, reject234⟩, reject235⟩, reject236⟩, reject237⟩, reject238⟩, reject239⟩, reject240⟩, reject241⟩, reject242⟩, reject243⟩, reject244⟩, reject245⟩, reject246⟩, reject247⟩, reject248⟩, reject249⟩, reject250⟩, reject251⟩, reject252⟩, reject253⟩, reject254⟩, reject255⟩, reject256⟩, reject257⟩, reject258⟩, reject259⟩, reject260⟩, reject261⟩, reject262⟩, reject263⟩, reject264⟩, reject265⟩, reject266⟩, reject267⟩, reject268⟩, reject269⟩, reject270⟩, reject271⟩, reject272⟩, reject273⟩, reject274⟩, reject275⟩, reject276⟩, reject277⟩, reject278⟩, reject279⟩, reject280⟩, reject281⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject283 : rejects 6 (0, [0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject284 : rejects 6 (1, [0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject285 : rejects 6 (0, [0x8cf811a87c0467c18fc3e0, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject286 : rejects 6 (0, [0x8cf811a87c0467c18fc3e0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject287 : rejects 6 (0, [0x0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject288 : rejects 6 (0, [0x8cf811a87c0067c00003e0, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject289 : rejects 6 (0, [0x8cf811a87c0067c00003e0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject290 : rejects 6 (0, [0x400018fc000, 0x150002e55000f8001fffc00, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject291 : rejects 6 (1, [0x150002e55000f8001fffc00, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject292 : rejects 6 (0, [0x150002e55000f8001fffc00, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject293 : rejects 6 (0, [0x150002e55000f8001fffc00, 0x150002e55000f8001fffc00, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject294 : rejects 6 (0, [0x0, 0x150002e55000f8001fffc00, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject295 : rejects 6 (0, [0x150002e55000b8000703c00, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject296 : rejects 6 (0, [0x150002e55000b8000703c00, 0x150002e55000f8001fffc00, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject297 : rejects 6 (0, [0xb0000, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject298 : rejects 6 (1, [0x2408c4366463604e7bff273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject299 : rejects 6 (0, [0x2408c4366463604e7bff273, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject300 : rejects 6 (0, [0x2408c4366463604e7bff273, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject301 : rejects 6 (0, [0x4000184c000, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject302 : rejects 6 (1, [0x2408c4366463204e6303273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject303 : rejects 6 (0, [0x2408c4366463204e6303273, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject304 : rejects 6 (0, [0x2408c4366463204e6303273, 0x2408c4366463204e63b3273, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject305 : rejects 6 (0, [0xc0000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject306 : rejects 6 (1, [0xa50182d2840739cfff9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject307 : rejects 6 (0, [0xa50182d2840739cfff9c, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject308 : rejects 6 (0, [0xa50182d2840739cfff9c, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject309 : rejects 6 (0, [0x4000183c000, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject310 : rejects 6 (1, [0xa50182d2800738403f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject311 : rejects 6 (0, [0xa50182d2800738403f9c, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject312 : rejects 6 (0, [0xa50182d2800738403f9c, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject313 : rejects 6 (0, [0x1800000, 0x105003c0029587801f003ff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject314 : rejects 6 (1, [0x105003c00295c7801ffc3ff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject315 : rejects 6 (0, [0x105003c00295c7801ffc3ff, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject316 : rejects 6 (0, [0x105003c00295c7801ffc3ff, 0x105003c0029587801f003ff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject317 : rejects 6 (0, [0x400000fc000, 0x105003c0029587801f003ff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject318 : rejects 6 (1, [0x105003c00295878007003ff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject319 : rejects 6 (0, [0x105003c00295878007003ff, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject320 : rejects 6 (0, [0x105003c00295878007003ff, 0x105003c0029587801f003ff, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject321 : rejects 6 (0, [0x40000000000, 0xaa528000000ffffe000000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject322 : rejects 6 (1, [0xaa528000000fffff8fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject323 : rejects 6 (0, [0xaa528000000fffff8fc000, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject324 : rejects 6 (0, [0xaa528000000fffff8fc000, 0xaa528000000ffffe000000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject325 : rejects 6 (0, [0x18fc000, 0xaa528000000ffffe000000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject326 : rejects 6 (1, [0xaa528000000bfffe000000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject327 : rejects 6 (0, [0xaa528000000bfffe000000, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject328 : rejects 6 (0, [0xaa528000000bfffe000000, 0xaa528000000ffffe000000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject329 : rejects 6 (0, [0x400018fc000, 0x150002e55000f8001fffc00, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject330 : rejects 6 (1, [0x1dcf83ffd7c0fe7c1ffffe0, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject331 : rejects 6 (0, [0x1dcf83ffd7c0fe7c1ffffe0, 0x8cf811a87c0467c18fc3e0, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject332 : rejects 6 (0, [0x1dcf83ffd7c0fe7c1ffffe0, 0x150002e55000f8001fffc00, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject333 : rejects 6 (0, [0x8cf811a87c0067c00003e0, 0x150002e55000f8001fffc00, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject334 : rejects 6 (0, [0x150002e55000b8000703c00, 0x8cf811a87c0467c18fc3e0, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject335 : rejects 6 (0, [0x150002e55000b8000703c00, 0x150002e55000f8001fffc00, 0x400018fc000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject336 : rejects 6 (0, [0x880120440004c00b0260, 0x2408c4366463204e63b3273, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject337 : rejects 6 (0, [0x2ccfc53ee7e3667e7bff3f3, 0x2408c4366463204e63b3273, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject338 : rejects 6 (0, [0x8c7010883804630184c180, 0x2408c4366463204e63b3273, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject339 : rejects 6 (0, [0x24004424602320026303013, 0x2408c4366463204e63b3273, 0x400018fc000, 0x150002e55000f8001fffc00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject340 : rejects 6 (0, [0xa00180500007000c0380, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject341 : rejects 6 (0, [0x8cfd11aafe8467f9cffffc, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject342 : rejects 6 (0, [0x8c5810282c0460c183c060, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject343 : rejects 6 (0, [0x5000282800038403c1c, 0xa50182d28007384c3f9c, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject344 : rejects 6 (0, [0x4001000280060018003e0, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject345 : rejects 6 (0, [0x18df83da87d5c7fc1ffc3ff, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject346 : rejects 6 (0, [0x88f801a8540407c00fc000, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject347 : rejects 6 (0, [0x101002c000158180070001f, 0x105003c0029587801f003ff, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject348 : rejects 6 (0, [0x88500000000467c0000000, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject349 : rejects 6 (0, [0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject350 : rejects 6 (0, [0x4a811a87c0000018fc3e0, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject351 : rejects 6 (0, [0x22028000000b983e000000, 0xaa528000000ffffe000000, 0x400018fc000, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject352 : rejects 6 (0, [0x155003e55295ff801ffffff, 0x105003c0029587801f003ff, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject353 : rejects 6 (0, [0x50000255000780000ffc00, 0x105003c0029587801f003ff, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject354 : rejects 6 (0, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject355 : rejects 6 (0, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject282 : rejects 7 (1, [0x400018fc000, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by
  apply rejectChildren 6 _ 77 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, reject200⟩, reject201⟩, reject283⟩, reject284⟩, reject285⟩, reject286⟩, reject204⟩, reject287⟩, reject288⟩, reject289⟩, reject290⟩, reject291⟩, reject292⟩, reject293⟩, reject294⟩, reject295⟩, reject296⟩, reject297⟩, reject298⟩, reject299⟩, reject300⟩, reject301⟩, reject302⟩, reject303⟩, reject304⟩, reject305⟩, reject306⟩, reject307⟩, reject308⟩, reject309⟩, reject310⟩, reject311⟩, reject312⟩, reject313⟩, reject314⟩, reject315⟩, reject316⟩, reject317⟩, reject318⟩, reject319⟩, reject320⟩, reject321⟩, reject322⟩, reject323⟩, reject324⟩, reject325⟩, reject326⟩, reject327⟩, reject328⟩, reject329⟩, reject330⟩, reject331⟩, reject332⟩, reject333⟩, reject205⟩, reject334⟩, reject335⟩, reject336⟩, reject337⟩, reject338⟩, reject339⟩, reject340⟩, reject341⟩, reject342⟩, reject343⟩, reject344⟩, reject345⟩, reject346⟩, reject347⟩, reject348⟩, reject349⟩, reject350⟩, reject351⟩, reject352⟩, reject353⟩, reject354⟩, reject355⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject356 : rejects 7 (1, [0x1dcf83ffd7c0fe7c1ffffe0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject357 : rejects 7 (1, [0x8cf811a87c0067c00003e0, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject358 : rejects 7 (2, [0x150002e55000b8000703c00, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject359 : rejects 7 (1, [0x150002e55000b8000703c00, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject360 : rejects 7 (1, [0x88500000000467c0000000, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject362 : rejects 6 (1, [0xaa528000000ffffe000000, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject363 : rejects 6 (0, [0xaa528000000ffffe000000, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject364 : rejects 6 (1, [0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject365 : rejects 6 (0, [0xaefa91a87c0fffff8fc3e0, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject366 : rejects 6 (1, [0x4a811a87c0000018fc3e0, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject367 : rejects 6 (1, [0x4a811a87c0000018fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject368 : rejects 6 (0, [0x4a811a87c0000018fc3e0, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject369 : rejects 6 (0, [0x0, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject370 : rejects 6 (0, [0x880120440204e60b0260, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject371 : rejects 6 (0, [0x2eefed3ee7e3fffffbff3f3, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject372 : rejects 6 (0, [0xae729088380dfb1984c180, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject373 : rejects 6 (0, [0x24004424602300000303013, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject374 : rejects 6 (0, [0xa00180500007380c0380, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject375 : rejects 6 (1, [0xaeff91aafe8fffffcffffc, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject376 : rejects 6 (0, [0xaeff91aafe8fffffcffffc, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject377 : rejects 6 (1, [0xae5a90282c0ff8c783c060, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject378 : rejects 6 (0, [0xae5a90282c0ff8c783c060, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject379 : rejects 6 (0, [0x5000282800000403c1c, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject380 : rejects 6 (0, [0x4001000280878018003e0, 0xaefa91a87c0fffff8fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject381 : rejects 6 (0, [0x1affabda87d5fffffffc3ff, 0xaefa91a87c0fffff8fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject382 : rejects 6 (0, [0xaafa81a8540787fe0fc000, 0xaefa91a87c0fffff8fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject383 : rejects 6 (0, [0x101002c000150000070001f, 0xaefa91a87c0fffff8fc3e0, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject384 : rejects 6 (1, [0xf80018fc000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject385 : rejects 6 (0, [0xf80018fc000, 0xaefa91a87c0fffff8fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject386 : rejects 6 (0, [0x1fefabffd7c0fffffffffe0, 0xaefa91a87c0fffff8fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject387 : rejects 6 (0, [0xaefa91a87c007ffe0003e0, 0xaefa91a87c0fffff8fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject388 : rejects 6 (1, [0x150002e5500000000703c00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject389 : rejects 6 (0, [0x150002e5500000000703c00, 0xaefa91a87c0fffff8fc3e0, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject390 : rejects 6 (0, [0x204e6000000, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject391 : rejects 6 (0, [0x2eadec366463ffffe3b3273, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject392 : rejects 6 (0, [0xaa528000000dfb18000000, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject393 : rejects 6 (0, [0x2408c4366463000003b3273, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xaefa91a87c0fffff8fc3e0, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject394 : rejects 6 (0, [0x738000000, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject395 : rejects 6 (0, [0xaaf78182d28ffffe4c3f9c, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject396 : rejects 6 (0, [0xaa528000000ff8c6000000, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject397 : rejects 6 (0, [0xa50182d28000004c3f9c, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject398 : rejects 6 (0, [0x87800000000, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject399 : rejects 6 (0, [0x1af52bc00295ffffff003ff, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject400 : rejects 6 (0, [0xaa528000000787fe000000, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject401 : rejects 6 (0, [0x105003c0029500001f003ff, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject402 : rejects 6 (0, [0xf8000000000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject403 : rejects 6 (1, [0x1fa52ae55000ffffffffc00, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject404 : rejects 6 (0, [0x1fa52ae55000ffffffffc00, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject405 : rejects 6 (1, [0xaa52800000007ffe000000, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject406 : rejects 6 (0, [0xaa52800000007ffe000000, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject407 : rejects 6 (0, [0x150002e5500000001fffc00, 0xaa528000000ffffe000000, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject408 : rejects 6 (0, [0x84010242000420083210, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject409 : rejects 6 (1, [0x240ad43e6d6b207fe7f3fff, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject410 : rejects 6 (0, [0x240ad43e6d6b207fe7f3fff, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject411 : rejects 6 (1, [0x240084264043200c6330063, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject412 : rejects 6 (0, [0x240084264043200c6330063, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject413 : rejects 6 (0, [0x21008090800318440d8c, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject414 : rejects 6 (0, [0x100000300273, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject415 : rejects 6 (0, [0x3458c7f666f7a7ce7fb33ff, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject416 : rejects 6 (0, [0x2408c4366462204e60b3000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject417 : rejects 6 (0, [0x105003c0029487801c0018c, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject418 : rejects 6 (0, [0x40000244000200003b3000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject419 : rejects 6 (0, [0x3508c6f77463f84e7fffe73, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject420 : rejects 6 (0, [0x2008c4122463004e6000273, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject421 : rejects 6 (0, [0x110002c11000d8001c4cc00, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject422 : rejects 6 (0, [0x40039c, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject423 : rejects 6 (0, [0x105a53d82fbd87f39fc3fff, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject424 : rejects 6 (0, [0xa50182d28007380c3c00, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject425 : rejects 6 (0, [0x105003c0029587801b00063, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject426 : rejects 6 (0, [0x4c3c00, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject427 : rejects 6 (0, [0x150a52fd7d28f8739ffff9c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject428 : rejects 6 (0, [0xa50182d280073800039c, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject429 : rejects 6 (0, [0x150002e55000f8001b3c000, 0xa50182d28007384c3f9c, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject430 : rejects 6 (0, [0x100002c0000080001f00000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject431 : rejects 6 (0, [0x155003e55295ff801ffffff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject432 : rejects 6 (0, [0x5001000295078000003ff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject433 : rejects 6 (0, [0x50000255000780000ffc00, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject361 : rejects 7 (2, [0xaefa91a87c0fffff8fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by
  apply rejectChildren 6 _ 72 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, reject362⟩, reject363⟩, reject364⟩, reject365⟩, reject366⟩, reject367⟩, reject368⟩, reject369⟩, reject370⟩, reject371⟩, reject372⟩, reject373⟩, reject374⟩, reject375⟩, reject376⟩, reject377⟩, reject378⟩, reject379⟩, reject380⟩, reject381⟩, reject382⟩, reject383⟩, reject384⟩, reject385⟩, reject386⟩, reject387⟩, reject388⟩, reject389⟩, reject390⟩, reject391⟩, reject392⟩, reject393⟩, reject394⟩, reject395⟩, reject396⟩, reject397⟩, reject398⟩, reject399⟩, reject400⟩, reject401⟩, reject402⟩, reject403⟩, reject404⟩, reject405⟩, reject406⟩, reject407⟩, reject408⟩, reject409⟩, reject410⟩, reject411⟩, reject412⟩, reject413⟩, reject414⟩, reject415⟩, reject416⟩, reject417⟩, reject418⟩, reject419⟩, reject420⟩, reject421⟩, reject422⟩, reject423⟩, reject424⟩, reject425⟩, reject426⟩, reject427⟩, reject428⟩, reject429⟩, reject430⟩, reject431⟩, reject432⟩, reject433⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject434 : rejects 7 (1, [0xaefa91a87c0fffff8fc3e0, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject435 : rejects 7 (2, [0x4a811a87c0000018fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject436 : rejects 7 (1, [0x4a811a87c0000018fc3e0, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject437 : rejects 7 (1, [0x22028000000b983e000000, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject438 : rejects 7 (1, [0x100002c0000080001f00000, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject439 : rejects 7 (1, [0x155003e55295ff801ffffff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject440 : rejects 7 (1, [0x5001000295078000003ff, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject441 : rejects 7 (1, [0x50000255000780000ffc00, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0xaa528000000ffffe000000]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject442 : rejects 7 (1, [0x87800000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject443 : rejects 7 (1, [0x1af52bc00295ffffff003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject444 : rejects 7 (1, [0x105003c0029500001f003ff, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject445 : rejects 7 (1, [0xaa528000000787fe000000, 0x105003c0029587801f003ff, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x150002e55000f8001fffc00]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject446 : rejects 7 (1, [0xf8000000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject447 : rejects 7 (1, [0x1fa52ae55000ffffffffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject448 : rejects 7 (1, [0x150002e5500000001fffc00, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject449 : rejects 7 (1, [0xaa52800000007ffe000000, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000, 0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff]) := by unfold rejects; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject0 : rejects 8 (3, [0x2408c4366463204e63b3273, 0xa50182d28007384c3f9c, 0x8cf811a87c0467c18fc3e0, 0x105003c0029587801f003ff, 0x150002e55000f8001fffc00, 0xaa528000000ffffe000000]) := by
  apply rejectChildren 7 _ 68 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨trivial, reject1⟩, reject2⟩, reject82⟩, reject83⟩, reject84⟩, reject85⟩, reject86⟩, reject87⟩, reject88⟩, reject89⟩, reject90⟩, reject91⟩, reject92⟩, reject93⟩, reject94⟩, reject95⟩, reject96⟩, reject97⟩, reject98⟩, reject99⟩, reject100⟩, reject101⟩, reject102⟩, reject103⟩, reject179⟩, reject180⟩, reject181⟩, reject182⟩, reject183⟩, reject184⟩, reject185⟩, reject186⟩, reject187⟩, reject188⟩, reject189⟩, reject190⟩, reject191⟩, reject192⟩, reject193⟩, reject194⟩, reject195⟩, reject196⟩, reject197⟩, reject198⟩, reject199⟩, reject282⟩, reject356⟩, reject357⟩, reject358⟩, reject359⟩, reject360⟩, reject361⟩, reject434⟩, reject435⟩, reject436⟩, reject437⟩, reject438⟩, reject439⟩, reject440⟩, reject441⟩, reject442⟩, reject443⟩, reject444⟩, reject445⟩, reject446⟩, reject447⟩, reject448⟩, reject449⟩

theorem smallReject : search 8 reduced = false := by
  have covers : ∀ ws ∈ reduced.sublists, cuts ws = -1 → ws = reduced := by decide +kernel
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨ws, hm, good⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at good
  obtain ⟨⟨_, hc⟩, run⟩ := good
  obtain rfl := covers ws hm hc
  exact Bool.noConfusion (reject0.symm.trans run)

theorem noSmall {t : W} (ht : t = goal ∨ t = ~~~goal) (k : Nat) (low : k ≤ 9)
    (run : build basicOps t k rows.toFinset) : False := by
  have d : differs 44 t := by rcases ht with rfl|rfl <;> unfold differs <;> decide
  obtain ⟨t1,k1,ht1,run1,_,less⟩ := shrink 44 (by decide +kernel) ht d k mapLeaf run
  have hk := less cleanLeaf
  have lift {n m : Nat} (h : n ≤ m) (hr : build basicOps t1 n reduced.toFinset) : build basicOps t1 m reduced.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (smallReject.symm.trans (search_complete ht1 8 reduced (by decide) (lift (by omega) run1)))

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 4 && x 6) || (x 5 && x 6)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sample : ∀ k : Fin 90, F (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows, holds rows.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 90) :
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

end PEqualNP.Outside.L_meta_11205.Signed


namespace PEqualNP.Outside.L_meta_11205

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = ((x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 4 && x 6) || (x 5 && x 6)) := by
  decide

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 16]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide

end PEqualNP.Outside.L_meta_11205

theorem PEqualNP.Outside.L_meta_11205 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_11205.Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_11205.Signed.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_11205.Signed.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_11205.Signed.bound gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_11205.bridge x))
    have hl : PEqualNP.Outside.L_meta_11205.wg.length = 11 := rfl
    exact ⟨PEqualNP.Outside.L_meta_11205.wg, 17, PEqualNP.Outside.L_meta_11205.wfits, by omega, PEqualNP.Outside.L_meta_11205.weval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
