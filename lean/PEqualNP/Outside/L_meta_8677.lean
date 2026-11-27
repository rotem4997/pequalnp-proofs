import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8677

-- The signed live-wire search and its soundness proof follow L-meta-8463 and L-meta-1449,
-- Apache-2.0. The sampled assignments, the goal and the witness are for the table 0xeeeaeaa8.

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

-- The upper and lower halves represent opposite target labels on the 93 pairs of
-- assignments that differ in at most two coordinates.
abbrev W := BitVec 186
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 93 := ((x >>> 93) ^^^ x).setWidth 93
def cuts (ws : List W) : BitVec 93 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 93) ++ (0 : BitVec 93)
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

def differs (i : Fin 93) (w : W) : Prop :=
  w.getLsbD (93+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 93) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 93+i.val < 186 := by omega
  have hi' : i.val < 186 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 93) :
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
  change (cuts ws)[j] = (BitVec.allOnes 93)[j]
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

def attempt (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W) : Bool :=
  let v := sep w ||| cuts r
  let go := fun e l => !decide (w ∈ a :: b :: r) && next e (w :: l)
  ((v == -1) && go extra r) ||
  ((extra != 0) && (((v ||| sep a == -1) && go (extra - 1) (a :: r)) ||
                     ((v ||| sep b == -1) && go (extra - 1) (b :: r)))) ||
  ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && go (extra - 2) (a :: b :: r))

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  (ops a b).any (attempt extra next a b r)

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (new : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp only [attempt, decide_eq_false new, Bool.not_false, Bool.true_and]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

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
        have fresh : z ∉ a :: b :: r := fun hu =>
          hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hu))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop fresh hk (by omega) (by omega) (cuts_full hg hl)
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
  · change reachable av (BitVec.allOnes 186 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 186)
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

private def bit (k : Fin 186) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 186) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 186) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#186)[k.val] = false; simp
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
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
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

def inputs : List W := [0x203f80ff01ffff80fffffffe00000040008840004421082, 0x3fc3ff07fe0f03ff0781e07e160ca81950510ca8288a23c, 0x3ffc0007fff003fff801ff81ab62042e6d021736810cf08, 0x3ffffff8000003fffffe0001cdb7368408041bc733c0410, 0x3ffffffffffffc0000000001f1dbc7378e6782040200820]

def targetFun (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xeeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 8000 in
theorem sample_rows : ∀ j : Fin 186,
    targetFun (fun i => (inputs.getD i.val 0)[j.val]) = goal[j.val] := by
  decide +kernel

theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 186) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (inputs.getD i.val 0)
    have width : inputs.length = 5 := rfl
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k goal
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

-- The same search on natural numbers, where the kernel computes with literals.
def low : ℕ := 0x1fffffffffffffffffffffff
def full : ℕ := 0x3ffffffffffffffffffffffffffffffffffffffffffffff
def high : ℕ := 0x3ffffffffffffffffffffffe00000000000000000000000

def andB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x
def orB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x
def force (k : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) k

def sepN (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 93) x) 0x200000000000000000000000
def cutsN (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ v => Nat.lor (sepN w) v) ws
def memN (w : ℕ) (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun u _ t => orB (Nat.beq w u) t) ws

def anySingles {α : Type} (ws : List α) : (α → List α → Bool) → Bool :=
  List.rec (motive := fun _ => (α → List α → Bool) → Bool) (fun _ => false)
    (fun a rest ih p => orB (p a rest) (ih (fun b bs => p b (a :: bs)))) ws

def anyPairs {α : Type} (ws : List α) : (α → α → List α → Bool) → Bool :=
  List.rec (motive := fun _ => (α → α → List α → Bool) → Bool) (fun _ => false)
    (fun a rest ih p => orB (anySingles rest (p a)) (ih (fun b c bs => p b c (a :: bs)))) ws

def goN (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) (w e : ℕ) (l : List ℕ) : Bool :=
  andB (Bool.rec (motive := fun _ => Bool) true false (memN w (a :: b :: r)))
    (force w (fun u => next e (u :: l)))

def attemptN (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) (w : ℕ) : Bool :=
  orB (andB (Nat.beq (Nat.lor (sepN w) (cutsN r)) low) (goN next a b r w extra r))
    (Nat.rec (motive := fun _ => Bool) false (fun e _ =>
      orB (andB (Nat.beq (Nat.lor (Nat.lor (sepN w) (cutsN r)) (sepN a)) low)
            (goN next a b r w e (a :: r)))
        (orB (andB (Nat.beq (Nat.lor (Nat.lor (sepN w) (cutsN r)) (sepN b)) low)
              (goN next a b r w e (b :: r)))
          (Nat.rec (motive := fun _ => Bool) false (fun d _ =>
            andB (Nat.beq (Nat.lor (Nat.lor (Nat.lor (sepN w) (cutsN r)) (sepN a)) (sepN b)) low)
              (goN next a b r w d (a :: b :: r))) e))) extra)

def dispatchN (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  orB (attemptN extra next a b r (Nat.land a b))
    (orB (attemptN extra next a b r (Nat.lor a b))
      (orB (attemptN extra next a b r (Nat.land a (Nat.sub full b)))
        (attemptN extra next a b r (Nat.land b (Nat.sub full a)))))

def isGoalN : List ℕ → Bool
  | [w] => Nat.beq w high || Nat.beq w low
  | _ => false

def optimizedN (k : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → List ℕ → Bool) (fun _ ws => isGoalN ws)
    (fun _ next extra ws => orB (isGoalN ws) (anyPairs ws (dispatchN extra next))) k

def searchN (k : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws =>
    Nat.ble ws.length (k+1) && Nat.beq (cutsN ws) low && optimizedN k (Nat.sub (k+1) ws.length) ws

theorem andB_eq (x y : Bool) : andB x y = (x && y) := by cases x <;> rfl
theorem orB_eq (x y : Bool) : orB x y = (x || y) := by cases x <;> rfl
theorem notB_eq (x : Bool) : Bool.rec (motive := fun _ => Bool) true false x = !x := by
  cases x <;> rfl
theorem force_eq (k : ℕ) (f : ℕ → Bool) : force k f = f k := by cases k <;> rfl

theorem toNat_beq {m : ℕ} (x y : BitVec m) : Nat.beq x.toNat y.toNat = (x == y) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.toNat_inj]

theorem low_eq : low = (-1 : BitVec 93).toNat := by decide +kernel
theorem full_eq : full = 2 ^ 186 - 1 := by decide +kernel
theorem goal_toNat : goal.toNat = high := by decide +kernel
theorem not_goal_toNat : (~~~goal).toNat = low := by decide +kernel

theorem sepN_eq (a : W) : sepN a.toNat = (sep a).toNat := by
  simp only [sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

theorem cutsN_eq (ws : List W) : cutsN (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    change Nat.lor (sepN a.toNat) (cutsN (r.map BitVec.toNat)) = (sep a ||| cuts r).toNat
    rw [ih, sepN_eq, BitVec.toNat_or]
    rfl

theorem memN_eq (w : W) (ws : List W) : memN w.toNat (ws.map BitVec.toNat) = decide (w ∈ ws) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    change orB (Nat.beq w.toNat a.toNat) (memN w.toNat (r.map BitVec.toNat)) = _
    rw [orB_eq, ih, toNat_beq, Bool.eq_iff_iff]
    simp

theorem isGoalN_eq (ws : List W) :
    isGoalN (ws.map BitVec.toNat) = (ws == [goal] || ws == [~~~goal]) := by
  rcases ws with _ | ⟨a, _ | ⟨b, r⟩⟩
  · rfl
  · change (Nat.beq a.toNat high || Nat.beq a.toNat low) = _
    rw [← goal_toNat, ← not_goal_toNat, toNat_beq, toNat_beq]
    simp
  · simp [isGoalN]

theorem anySingles_eq {α β : Type} (f : α → β) (ws : List α) : ∀ p : β → List β → Bool,
    anySingles (ws.map f) p = (singles ws).any (fun t => p (f t.1) (t.2.map f)) := by
  induction ws with
  | nil => intro _; rfl
  | cons a r ih =>
    intro p
    change orB (p (f a) (r.map f)) (anySingles (r.map f) (fun b bs => p b (f a :: bs))) = _
    rw [orB_eq, ih]
    simp only [singles, List.any_cons, List.any_map]
    rfl

theorem anyPairs_eq {α β : Type} (f : α → β) (ws : List α) : ∀ p : β → β → List β → Bool,
    anyPairs (ws.map f) p = (pairs ws).any (fun t => p (f t.1) (f t.2.1) (t.2.2.map f)) := by
  induction ws with
  | nil => intro _; rfl
  | cons a r ih =>
    intro p
    change orB (anySingles (r.map f) (p (f a)))
      (anyPairs (r.map f) (fun b c bs => p b c (f a :: bs))) = _
    rw [orB_eq, ih, anySingles_eq]
    simp only [pairs, List.any_append, List.any_map]
    rfl

theorem attemptN_eq (extra : ℕ) (nextN : ℕ → List ℕ → Bool) (next : ℕ → List W → Bool)
    (h : ∀ e ws, nextN e (ws.map BitVec.toNat) = next e ws) (a b : W) (r : List W) (w : W) :
    attemptN extra nextN a.toNat b.toNat (r.map BitVec.toNat) w.toNat =
      attempt extra next a b r w := by
  have join (x y : BitVec 93) : Nat.lor x.toNat y.toNat = (x ||| y).toNat :=
    (BitVec.toNat_or x y).symm
  have whole (x : BitVec 93) : Nat.beq x.toNat low = (x == -1) := by rw [low_eq, toNat_beq]
  have cons (z : W) (zs : List W) :
      z.toNat :: zs.map BitVec.toNat = (z :: zs).map BitVec.toNat := rfl
  have go (e : ℕ) (l : List W) : goN nextN a.toNat b.toNat (r.map BitVec.toNat) w.toNat e
      (l.map BitVec.toNat) = (!decide (w ∈ a :: b :: r) && next e (w :: l)) := by
    simp only [goN, andB_eq, notB_eq, force_eq, cons, memN_eq, h]
  rcases extra with _ | _ | e <;>
    simp only [attemptN, andB_eq, orB_eq, sepN_eq, cutsN_eq, join, whole, cons, go] <;>
    simp [attempt, Bool.or_assoc]

theorem dispatchN_eq (extra : ℕ) (nextN : ℕ → List ℕ → Bool) (next : ℕ → List W → Bool)
    (h : ∀ e ws, nextN e (ws.map BitVec.toNat) = next e ws) (a b : W) (r : List W) :
    dispatchN extra nextN a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra next a b r := by
  have meet (x y : W) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have join (x y : W) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  have flip (x : W) : Nat.sub full x.toNat = (~~~x).toNat := by
    rw [BitVec.toNat_not, full_eq]
    rfl
  simp only [dispatchN, dispatch, ops, flip, meet, join, attemptN_eq extra nextN next h, orB_eq,
    List.any_cons, List.any_nil, Bool.or_false]

theorem optimizedN_eq (k : ℕ) : ∀ extra ws,
    optimizedN k extra (ws.map BitVec.toNat) = optimized k extra ws := by
  induction k with
  | zero => intro _ ws; exact isGoalN_eq ws
  | succ k ih =>
    intro extra ws
    change orB (isGoalN (ws.map BitVec.toNat))
      (anyPairs (ws.map BitVec.toNat) (dispatchN extra (optimizedN k))) = _
    rw [orB_eq, isGoalN_eq, anyPairs_eq]
    simp only [dispatchN_eq extra (optimizedN k) (optimized k) ih]
    rfl

theorem searchN_eq (k : ℕ) (inputs : List W) :
    searchN k (inputs.map BitVec.toNat) = search k inputs := by
  unfold searchN search
  rw [List.sublists_map, List.any_map]
  congr 1
  funext ws
  have len : Nat.ble ws.length (k+1) = decide (ws.length ≤ k+1) := by
    rw [Bool.eq_iff_iff]; simp
  simp only [Function.comp_apply, List.length_map, cutsN_eq, optimizedN_eq, low_eq, toNat_beq, len]
  rfl

def inputsN : List ℕ := [0x203f80ff01ffff80fffffffe00000040008840004421082, 0x3fc3ff07fe0f03ff0781e07e160ca81950510ca8288a23c, 0x3ffc0007fff003fff801ff81ab62042e6d021736810cf08, 0x3ffffff8000003fffffe0001cdb7368408041bc733c0410, 0x3ffffffffffffc0000000001f1dbc7378e6782040200820]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem search_numbers : searchN 7 inputsN = false := by decide +kernel

theorem inputs_toNat : inputs.map BitVec.toNat = inputsN := by decide +kernel

theorem search_seven : search 7 inputs = false := by
  rw [← searchN_eq, inputs_toNat]
  exact search_numbers

theorem no_seven_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 7 inputs.toFinset) : False :=
  Bool.noConfusion (search_seven.symm.trans
    (search_complete ht 7 inputs (by decide +kernel) run))

-- The majority of x2, x3, x4 shares its first gate with their disjunction.
def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [9, 12]⟩], 13⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

theorem witness_eval : ∀ x : Fin 5 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  decide +kernel

end PEqualNP.Outside.L_meta_8677

theorem PEqualNP.Outside.L_meta_8677 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_8677.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_8677.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_8677.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_8677.bound_from_impossible
      7 PEqualNP.Outside.L_meta_8677.no_seven_binary C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_8677.witness, PEqualNP.Outside.L_meta_8677.witness_mono,
      ?_, PEqualNP.Outside.L_meta_8677.witness_eval⟩
    change 9 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
