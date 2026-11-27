import PEqualNP.Defs

-- For this edge function, twelve monotone gates suffice. A circuit with a negation and
-- at most eleven gates would contain at most ten binary gates, even with free complements.
-- At least one input to its first binary gate must be used again. Setting that input to
-- zero eliminates two gates. Further vertex deletions give either a four-vertex clique
-- with at most six gates or a five-vertex graph with one universal vertex and a matching
-- with at most seven. The two finite searches below exclude these possibilities.

-- Signed live-wire completeness adapted from open-goat/pequalnp-proofs L_meta_9146, Apache-2.0.
namespace PEqualNP.Outside.L_meta_10636.Signed

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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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
abbrev W := BitVec 476
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 238 := ((x >>> 238) ^^^ x).setWidth 238
def cuts (ws : List W) : BitVec 238 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 238) ++ (0 : BitVec 238)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

def differs (i : Fin 238) (w : W) : Prop :=
  w.getLsbD (238+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ops_differs (i : Fin 238) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 238+i.val < 476 := by omega
  have hi' : i.val < 476 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cuts_spec (ws : List W) (i : Fin 238) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 238)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 476 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 476)
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 476) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 476) :
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 476) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#476)[k.val] = false; simp
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
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

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636
open PEqualNP.CircuitLowerBounds
def gates : List Gate := [⟨.or,[5,6]⟩, ⟨.or,[3,7]⟩, ⟨.or,[4,7]⟩, ⟨.and,[1,8]⟩, ⟨.and,[2,9]⟩, ⟨.or,[3,4]⟩, ⟨.or,[0,7]⟩, ⟨.and,[12,13]⟩, ⟨.and,[5,6]⟩, ⟨.or,[10,11]⟩, ⟨.or,[14,15]⟩, ⟨.or,[16,17]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem fits : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates, List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = Signed.F x := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem exactGates : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates,18⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_10636

namespace PEqualNP.Outside.L_meta_10636.Signed

abbrev targetSign (g : W) := g = goal ∨ g = ~~~goal
def finish (av : Finset W) (k : Nat) := ∃ t, targetSign t ∧ build basicOps t k av

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish_more {av k} (h : finish av k) : finish av (k+1) := by
  obtain ⟨t, ht, run⟩ := h
  exact ⟨t, ht, Or.inl run⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish_step {av k a b z} (ha : a ∈ av) (hb : b ∈ av) (hab : a ≠ b)
    (hz : z ∈ basicOps a b) (h : finish (insert z av) k) : finish av (k+1) := by
  obtain ⟨t, ht, run⟩ := h
  exact ⟨t, ht, Or.inr ⟨a,ha,b,hb,hab,z,hz,run⟩⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_nonzero {g} (h : targetSign g) : g ≠ (0 : W) ∧ g ≠ ~~~(0 : W) := by
  rcases h with rfl | rfl <;> decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish_of_holds {av g} (h : targetSign g) (known : holds av g) : finish av 0 := by
  rcases known with zero | ones | ⟨t, ht, eq | eq⟩
  · exact ((target_nonzero h).1 zero).elim
  · exact ((target_nonzero h).2 ones).elim
  · exact ⟨t, eq ▸ h, ht⟩
  · have ht' : t = ~~~g := by rw [eq, BitVec.not_not]
    exact ⟨t, by rcases h with rfl | rfl <;> first | exact .inr ht' | exact .inl (ht'.trans BitVec.not_not), ht⟩

def Pullback := {f : W → W //
    (∀ x y, f (x &&& y) = f x &&& f y) ∧ (∀ x y, f (x ||| y) = f x ||| f y) ∧
    (∀ x, f (~~~x) = ~~~f x) ∧ f goal = goal}

namespace Pullback
def fn (p : Pullback) : W → W := p.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapAnd (p : Pullback) (x y : W) : p.fn (x &&& y) = p.fn x &&& p.fn y := p.property.1 x y
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapOr (p : Pullback) (x y : W) : p.fn (x ||| y) = p.fn x ||| p.fn y := p.property.2.1 x y
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapNot (p : Pullback) (x : W) : p.fn (~~~x) = ~~~p.fn x := p.property.2.2.1 x
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapGoal (p : Pullback) : p.fn goal = goal := p.property.2.2.2
end Pullback

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapped_goal (p : Pullback) {g} (hg : targetSign g) : targetSign (p.fn g) := by
  rcases hg with rfl | rfl
  · exact .inl p.mapGoal
  · exact .inr (by rw [p.mapNot,p.mapGoal])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapped_reach (p : Pullback) {av a b z} (hz : z ∈ basicOps a b)
    (ha : holds av (p.fn a)) (hb : holds av (p.fn b)) : reachable av (p.fn z) := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp only [p.mapAnd,p.mapOr,p.mapNot]
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mapped_zero (p : Pullback) {av a b z} (hz : z ∈ basicOps a b)
    (ha : holds av (p.fn a)) (hb : holds av (p.fn b)) (zero : p.fn a = 0 ∨ p.fn b = 0) :
    holds av (p.fn z) := by
  have h0 : holds av (0 : W) := .inl rfl
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have zAnd (w : W) : (0 : W) &&& w = 0 := BitVec.zero_and
  have andZ (w : W) : w &&& (0 : W) = 0 := BitVec.and_zero
  have zOr (w : W) : (0 : W) ||| w = w := BitVec.zero_or
  have orZ (w : W) : w ||| (0 : W) = w := BitVec.or_zero
  have andN (w : W) : w &&& ~~~(0 : W) = w := BitVec.and_allOnes
  rcases zero with za | zb <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [p.mapAnd,p.mapOr,p.mapNot, * ,
      zAnd,andZ,zOr,orZ,andN] <;> assumption

abbrev inStock (p : Pullback) (av s : Finset W) := ∀ x ∈ s, holds av (p.fn x)
abbrev marked (p : Pullback) (s : Finset W) := ∃ v ∈ s, p.fn v = 0

-- A zero-valued live wire must be consumed before the nonconstant output.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem project_live (p : Pullback) {g} (hg : targetSign g) (n : Nat) (s av : Finset W)
    (run : live basicOps g n s) (known : inStock p av s) :
    finish av n ∧ (marked p s → n ≠ 0 ∧ finish av (n-1)) := by
  induction n generalizing s av with
  | zero =>
    change s = {g} at run
    subst s
    refine ⟨finish_of_holds (mapped_goal p hg) (known g (by simp)), ?_⟩
    rintro ⟨m, hm, hzero⟩
    rw [Finset.mem_singleton.mp hm] at hzero
    exact ((target_nonzero (mapped_goal p hg)).1 hzero).elim
  | succ n ih =>
    rcases run with skip | ⟨a,ha,b,hb,hab,z,hz,hnew,r,hs,tail⟩
    · obtain ⟨ok,save⟩ := ih s av skip known
      exact ⟨finish_more ok,fun _ => ⟨Nat.succ_ne_zero _,by simpa using ok⟩⟩
    · have sub : r ⊆ s := by
        rw [hs]
        exact fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      have stock {A : Finset W} (old : inStock p A s) (h : holds A (p.fn z)) : inStock p A (insert z r) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact h
        · exact old u (sub hr)
      have reach := mapped_reach p hz (known a ha) (known b hb)
      have normal : finish av (n+1) := by
        rcases reach with held | ⟨u,hu,v,hv,ne,w,op,rep⟩
        · exact finish_more (ih _ av tail (stock known held)).1
        · exact finish_step hu hv ne op (ih _ (insert w av) tail
              (stock (fun t ht => holds_insert (known t ht)) rep)).1
      refine ⟨normal,?_⟩
      rintro ⟨m,hm,hm0⟩
      refine ⟨Nat.succ_ne_zero _, ?_⟩
      change finish av n
      by_cases consume : m = a ∨ m = b
      · have zero : p.fn a = 0 ∨ p.fn b = 0 := by rcases consume with rfl|rfl <;> simp [hm0]
        exact (ih _ av tail (stock known (mapped_zero p hz (known a ha) (known b hb) zero))).1
      · have mr : m ∈ r := by
          rw [hs] at hm
          simpa [Finset.mem_insert, not_or.mp consume |>.1, not_or.mp consume |>.2] using hm
        have m' : marked p (insert z r) := ⟨m,Finset.mem_insert_of_mem mr,hm0⟩
        rcases reach with held | ⟨u,hu,v,hv,ne,w,op,rep⟩
        · exact (ih _ av tail (stock known held)).1
        · obtain ⟨hn,less⟩ := (ih _ (insert w av) tail
              (stock (fun t ht => holds_insert (known t ht)) rep)).2 m'
          have succ := finish_step hu hv ne op less
          convert succ using 1 <;> omega
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
def rootRows : List W := [0x15540aaa055502aa815540ad40aaf07245103fffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaab56bb3c1c903db,0x19808cc046602330119808c808cc0e004f08800000000000000000000000cccccccccccccccf33333339b2d83836fc24,0x1e002f0017800bc005e002f002f006501002000000000000000000000000f0f0f0f0f0f0f0f3c3c3c3de3ce006808010,0xfffffffffffffffffffffffe001300098004c00260013001300000130477fffffffffffffffffffffffff00ff00ff00ff03fc03fc1fc0f8e0c7c1fd,0x1c000e000700038001c001c0009010040800000000000000000000000ffff0000ffff0003fffc001fff0307080202,0x6000300018000c0006000600150000000000000000000000000000000ffffffff00000003ffffffe0000408100c00,0x18000c00060003000180018000a0000000000000000000000000000000fffffffffffffffc00000000000410203000]
def rows0 : List W := [0x3f00fe0000001f800fc7000780000fc0fc008a1142508a120003c00f1f92a44c05571452fe0b7f1d5032ac10552ff015555556b5557c211f027c7,0xe03fff00000000000fcff8000000fc0fff00002c0580602c000000078fe2a558001b3b28a596ff3fe0c8441565eafd512e666664d999a842213e3f8,0xffc00000000003e00ff00001f800fff0000001302604813024003c07f001005c94a2ad451faa3fcb0eaaa35a9fc1d422478787871e1e3c84f21fc41,0x3fff0000001ffff0000000001c0380701c038003ff80001c9ad214cce8a2fffd51563354dfc2a821ab48ff807f81fe03108ffe4088,0xfc000000000e0000000000000000400802004007c00000020e323a70f0f3f94d66e6b4398860c30c60c8f7fff8001fffc21f4448912,0x3f0000000000f000000000000000008010040080f80000000070c3c38700ffce71b8b8dbc611830c30830f07ffffffe00003f08891224]
def rows1 : List W := [0xff07f8001f87c00079f81f800000003c0fe02a82a82a0a82bc3c000078c7542015bbfe1f0417e075875837824b3aff81aaaaaaaaaab7f0f01113e3,0xfff800000000001ffe000000001f803ff000300b00b02c0b0000003c7f18a802628d966b6afff882882840ac95cfd2a6ccccccccccda111122f1fc,0xf000000000000079f80000001fc1fffc00000002c02c0b02c00003c3f8000fce48b56aa959e7e612b12b29953ff154508f0f0f0ff0fe32222f0fe21,0x7e000000001ffe00000000000300300c03000003fc0002d0d092c674d263fabba4c24c56f852621a9d3ff00ff0ff0fc4444ff2046,0x7f80000001ffe00000000000000c00c030000003fc00000323251d07871dff3cccc1079f9821838460e1cffff000fff0088ff444488,0x1ff8000001ffe0000000000000000300300000c03fc000000003c39e1f807ff8dd71179fc1060c61c0883060fffffff00000ff88888910]
def rows3 : List W := [0xfc003e1e0038e3bf03e00003f81f83f00ff00aaa2aa2aa8aaf0f000e38e52ddbf87828e38e26b0dc2ab57552bac97fc02aaaaaaaaaaafc3c0478e39,0x3e3f03c00000fe03ffe003fff0000cc0b30b302cc0000f0fc0f962ad292af8fc0f295125655ab5514fbfc484b33333cf333c84447c3f03e,0x3ffc0000000003fffffc0000000f003c03c00f0000000fff01b336529153fff0306208306fdffdfa9289497c3c3cf3c3cf088888bffc0,0x3fc000000000fffc0000000000000000c00c003000000ff0000234479cddff6db64584b2bff0e18610e4d2527fc03f03fc0fd1113fc9249,0x1fc000000003ff00000000000000000003003000c0000ff0000003c878e77f9db6db820f7cc1830618630723a3bfffc003fff0223fd112492,0x3fe00000003ffc000000000000000000000c000003000ff0000000000f80ffe6e6db6dfbf843060c18618c383c3c3ffffffc00003fe22224924]
def rows5 : List W := [0x1f00001c777f00000000003f81f80fe03fe02a05540aa82abc00000e39cdfc194571dc4cac51138a4b575564ee92ff82aaaaaaaaaaedf0112278e73,0x1f01f87800003e000003ffe000fffc0003046608cc2330003c00fc1f2956fcafe1e511424a48c15ebdd093b7f1289cccccccf3cb6112f04bf07c,0x7dff8000000001f803ffffff00000000017802f00bc0000078ffe032ab2bf7fe06058820938a6bd779fea252514f0f0f0f3cf3822425e3ff80,0x3e07e0000000fc001fffc00000000000000098013000c0003c07f00003cdfcdfb6ce866130ce4fff0e1832438949a1ff00ff03f03f44f41fc9215,0x3ff800000000ffffe0000000000000000000e001c00300003ff800000072fff35b750b82cb7f91383061c38c4e8e46ffff0003ffc088ffe8124a2,0x1fc00000007fff0000000000000000000000030006000c003fc0000000007fc73cedbbf3ff0c7061c0c1861c3070f078fffffffc0000ff889124948]
def minorRows (v : Fin 7) : List W := match v.val with
  | 0 => rows0
  | 1 => rows1
  | 2 => rows1
  | 3 => rows3
  | 4 => rows3
  | 5 => rows5
  | _ => rows5
def selector0 : Nat := 0x78bc5e2ee773b9dcee773ba130984c2613098a45229148a452291479bcde6f379bcde6f57abd5eaf57abd5eaf57abd63f1f8fc7e3f1f88442211088441ecf67b3d9ecef77bbddeef77c22110878bc5e2f178bc5dcee84c26130984c2629148a3cde6f38fc7e3f1f8844220f67b3d9ecf67b3bddeef77c22110884422110878bc5e2f178bc5dcee773b9dcee84c26130984c2629148a452291479bcde6f379bcdeaf57abd5eaf57abd5eaf677c21e2ee84c51e6f58fc41ecef843c5dd098a3cdeb1f883d9df087742628f37ac7e20f677c21e2ee84c51e6f58fc41ecef843b9e6f58fc7e3f1f8fc42211088441ecf67b3d9deef77bbe1108843c5e2f178bb9dcee84c2613098a45228f379bcc702f16180a80c210d8141931170883e188bc44602c030843a0500844602c10874360c988b856251107c38188bc580f401e0e8723216900783a1c88c3c441b0d44e19a08d46626120668032118f86c2f13880333c0f0ec662f12080333a1908c722d0f0d0622e15894441f180b0421d064040c210640468311288831178b0b0541d0d8320234170943e1883ca80c1b02832022e0f870311603cc456220e05e2c11180b054210e86c0a0ca39188a442190882401f8f87a3c1d8e872111b8d86a34198c86230178b4582b15018502713094482311084401f0f074381b028662f0780844602c1501822210e86c0a34128622f311105e2c30108325c1f0c41e581d008ac381603ca8360c8301402
def restrict0 : List W := [0x0,0x3f00fe0000001f800fc7000780000fc0fc008a1142508a120003c00f1f92a44c05571452fe0b7f1d5032ac10552ff015555556b5557c211f027c7,0xe03fff00000000000fcff8000000fc0fff00002c0580602c000000078fe2a558001b3b28a596ff3fe0c8441565eafd512e666664d999a842213e3f8,0xffc00000000003e00ff00001f800fff0000001302604813024003c07f001005c94a2ad451faa3fcb0eaaa35a9fc1d422478787871e1e3c84f21fc41,0x3fff0000001ffff0000000001c0380701c038003ff80001c9ad214cce8a2fffd51563354dfc2a821ab48ff807f81fe03108ffe4088,0xfc000000000e0000000000000000400802004007c00000020e323a70f0f3f94d66e6b4398860c30c60c8f7fff8001fffc21f4448912,0x3f0000000000f000000000000000008010040080f80000000070c3c38700ffce71b8b8dbc611830c30830f07ffffffe00003f08891224]
def selector1 : Nat := 0x773b9dcee8241209048241209048a45229148a3d1e8f47a3d1e8f47a3d5eaf57abd5eaf57abd5eaf57abd5eb0d86c361b0d86c7e3f1f8fc32190c864322110883d9ecf67b42210f178bc5e2f178c12090482452290d86c361b0d86c7e3f1f8fc7e3f0c86432190c8644221108844220f67b3d9ecf67b3da11088442210f178bc5e2f178bb9dcee773b9dcee773ba09048241229148a45229147a3d1e8f47a3d1e8f57abd5eaf57abd609147a3d61b1f86441ed0878bba09147a3d61b1f86441ed0878bba09147a3d619107b421e2ee82451e8f586c7ded0878bba09147a3d61b0d86c363f1f8fc7e190c86432211088441ecf67b3da110884421e2f178bc5dcee7741209048245229147a3d084360c804e2612e1647c3b188b844602c0e8002230160a8421d0d8327134184b8592a928863b1b8c45c2b02204f27534994ba803c1d0c8793a92c8e3f3c1d08c88361a49c80231f0d85d270fc6465238fc646423088c0582a004007134184b8592a888843a1b00400712510c7c3b1b980b0421d064020034184862e15960a83a1b06400682e164943e1d8c45c042a0d802002a8f86e3115810c255218ec6e2e15980a8421d0d8320146a31128842a1102803e9f0f2783a9d0e222369b0d26832990c2602e970b25827938964a2391886421f8f8763a190c45c2b0c804080038984b25511180b0543890c763711108743634128622e3010832012e0f862042c0e800551b8ac08541b0640200
def restrict1 : List W := [0xff07f8001f87c00079f81f800000003c0fe02a82a82a0a82bc3c000078c7542015bbfe1f0417e075875837824b3aff81aaaaaaaaaab7f0f01113e3,0x0,0xfff800000000001ffe000000001f803ff000300b00b02c0b0000003c7f18a802628d966b6afff882882840ac95cfd2a6ccccccccccda111122f1fc,0xf000000000000079f80000001fc1fffc00000002c02c0b02c00003c3f8000fce48b56aa959e7e612b12b29953ff154508f0f0f0ff0fe32222f0fe21,0x7e000000001ffe00000000000300300c03000003fc0002d0d092c674d263fabba4c24c56f852621a9d3ff00ff0ff0fc4444ff2046,0x7f80000001ffe00000000000000c00c030000003fc00000323251d07871dff3cccc1079f9821838460e1cffff000fff0088ff444488,0x1ff8000001ffe0000000000000000300300000c03fc000000003c39e1f807ff8dd71179fc1060c61c0883060fffffff00000ff88888910]
def selector2 : Nat := 0x8442211087c3e1f0f87c3e1f0f879bcde6f379bd1e8f47a3d1e8f47a3d5eaf57abd5eaf57abd5eaf57abd5eb0d86c361b0d86c7e3f1f8fc32190c864322110883d9ecf67b3b9dcef77bbddeef77be1f0f87c3cde70d86c361b0d86c7e3f1f8fc7e3f0c86432190c8644221108844220f67b3d9ecf67b3d9dcee773b9dcef77bbddeef77c22110884422110884421f0f87c3e1e6f379bcde6f37a3d1e8f47a3d1e8f57abd5eaf57abd5f0f37a3d61b1f86441ecee77c21f0f37a3d61b1f86441ecee77c21f0f37a3d619107b3b9df087c3cde8f586c7decee77c21f0f37a3d61b0d86c363f1f8fc7e190c86432211088441ecf67b3d9dcee773b9deef77bbe1108843e1f0f87c3cde6f37a3d0740a01000e259311848843178b844583010802222c180183a21028047134164c4612992876431a8bc5c24149e502733496cc678401c8b4813992c7a45401c87888351a498781e208d46326114605b1e914605a1e088b06006000027134164c461298887442050000271250ec88431a960c03a21008000134164762e121801842050080268311849444218bc5c29060280001299106a2f120a4b2531d90c6a2e12160183a21028040045a2912883d9e8f27841a090280399c8e222359a8d2682d968b25831988c26026930964a1e8f0763a229108642180bc5c2401000520138964c25311160c00c388ec8635110e8840a341285e2e2c0e80400311105e293010802531a890520c050080001
def restrict2 : List W := [0xff07f8001f87c00079f81f800000003c0fe02a82a82a0a82bc3c000078c7542015bbfe1f0417e075875837824b3aff81aaaaaaaaaab7f0f01113e3,0xfff800000000001ffe000000001f803ff000300b00b02c0b0000003c7f18a802628d966b6afff882882840ac95cfd2a6ccccccccccda111122f1fc,0x0,0x7e000000001ffe00000000000300300c03000003fc0002d0d092c674d263fabba4c24c56f852621a9d3ff00ff0ff0fc4444ff2046,0xf000000000000079f80000001fc1fffc00000002c02c0b02c00003c3f8000fce48b56aa959e7e612b12b29953ff154508f0f0f0ff0fe32222f0fe21,0x7f80000001ffe00000000000000c00c030000003fc00000323251d07871dff3cccc1079f9821838460e1cffff000fff0088ff444488,0x1ff8000001ffe0000000000000000300300000c03fc000000003c39e1f807ff8dd71179fc1060c61c0883060fffffff00000ff88888910]
def selector3 : Nat := 0x7a3d1e8f47a3d1eaf57abd5eaf57abd5eaf57abd61b0d86c361b1f8fc7e3f0c86432191088441deef77bbddf08844222f178bc2613098241209148a451f0f87c3ce1b0d86c361b0d8fc7e3f1f8fc7e190c86432191088442211077bbddeef77bbddf08844221108844222f178bc5e2f178bc26130984c2613048241209048245229148a451f0f87c3e1f0f879bcde6f379bcde6f37a3d1e8f47a3d1e8f47abd5eaf57abd5eaf58bc2609147c3cde8f586c7e191077c222f0982451f0f37a3d6191077c222f0982451f0f37a3d61b1f86441df088bc2609147c3cde8f586c361b0d8fc7e3f1f86432190c88442211077bbddeef8442211088bc5e2f0984c2609048245229147c3e1f0f379bd084391b0285a1938984ac552990c70371a8b05629409d4e66531a00e87232204e64722a00e44641198c64822a00c8463b99c927633120ea65239d0c8463998c8a7211180ae5406004e26230958aa53111086c0a009c488431b8d4c00c210285a1900988c244218b056292b1547037160ac52572a0e46c2d0c95ca8391b06402562a8e06e2b2b830720a16804c456299107035160a4e2612a94c86371a8ac44602a0308436050650e8642a11068240a00ee763a9d0e67238888ce6632990c6622b958aa54298309248239188a442190872381b8d86a0a168b0561914804e2612a94c44602a030e2431b8d444421b028c444160a4c0420c804ae3916958702c2a8dc56541b064a635148301401
def restrict3 : List W := [0xfc003e1e0038e3bf03e00003f81f83f00ff00aaa2aa2aa8aaf0f000e38e52ddbf87828e38e26b0dc2ab57552bac97fc02aaaaaaaaaaafc3c0478e39,0x3e3f03c00000fe03ffe003fff0000cc0b30b302cc0000f0fc0f962ad292af8fc0f295125655ab5514fbfc484b33333cf333c84447c3f03e,0x3ffc0000000003fffffc0000000f003c03c00f0000000fff01b336529153fff0306208306fdffdfa9289497c3c3cf3c3cf088888bffc0,0x0,0x3fc000000000fffc0000000000000000c00c003000000ff0000234479cddff6db64584b2bff0e18610e4d2527fc03f03fc0fd1113fc9249,0x1fc000000003ff00000000000000000003003000c0000ff0000003c878e77f9db6db820f7cc1830618630723a3bfffc003fff0223fd112492,0x3fe00000003ffc000000000000000000000c000003000ff0000000000f80ffe6e6db6dfbf843060c18618c383c3c3ffffffc00003fe22224924]
def selector4 : Nat := 0x7a3d1e8f47a3d1eaf57abd5eaf57abd5eaf57abd61b0d86c361b1f8fc7e3f0c86432191088441e2f178bc5e2ee773ba2f178bc2613097c3e1f0f379bce0904824521b0d86c361b0d8fc7e3f1f8fc7e190c86432191088442211078bc5e2f178bc5e2ee773b9dcee773ba2f178bc5e2f178bc26130984c2612f87c3e1f0f87c3cde6f379bce09048241209048a45229148a45229147a3d1e8f47a3d1e8f47abd5eaf57abd5eaf58bc25f0f382451e8f586c7e191078bba2f097c3ce09147a3d6191078bba2f097c3ce09147a3d61b1f86441e2ee8bc25f0f382451e8f586c361b0d8fc7e3f1f86432190c88442211078bc5e2f1773b9dcee8bc5e2f0984c25f0f87c3cde6f38241209148a3d07439050d84e0238964ac532a8ec70351b83c48043c9ccea5b2e9e0e4742d1e4ea3d1f9e0e83c3e178ba401f9e0b43c3b97c82762f100e65b1e9c8b43c3a9747e7411160ae0c2a000e25c2c958a655110e81436001c47c3b1a8dcb0541d0d84e0200170b23e1d83c48042b14c7035078900857060e414270115c1839050080056298e06a242b950723613800b8562a8f8703707810e2592995476351b890445806150740a1b008fe7e3d9e8fa7c3c9e0ee76399c8ea7438888be5e2d968ba5c2b958a60c2a95082401e8f07e3e1d8e872381a8286e361383c480202000e25929954445806150e23b1a8dc443a050d8b83e07810b03a01000ae3913958700f298d4480c05008aa37021506c00
def restrict4 : List W := [0xfc003e1e0038e3bf03e00003f81f83f00ff00aaa2aa2aa8aaf0f000e38e52ddbf87828e38e26b0dc2ab57552bac97fc02aaaaaaaaaaafc3c0478e39,0x3ffc0000000003fffffc0000000f003c03c00f0000000fff01b336529153fff0306208306fdffdfa9289497c3c3cf3c3cf088888bffc0,0x3e3f03c00000fe03ffe003fff0000cc0b30b302cc0000f0fc0f962ad292af8fc0f295125655ab5514fbfc484b33333cf333c84447c3f03e,0x3fc000000000fffc0000000000000000c00c003000000ff0000234479cddff6db64584b2bff0e18610e4d2527fc03f03fc0fd1113fc9249,0x0,0x1fc000000003ff00000000000000000003003000c0000ff0000003c878e77f9db6db820f7cc1830618630723a3bfffc003fff0223fd112492,0x3fe00000003ffc000000000000000000000c000003000ff0000000000f80ffe6e6db6dfbf843060c18618c383c3c3ffffffc00003fe22224924]
def selector5 : Nat := 0x7abd5eb0d86c361b0d8fc7decf67b3d9ecef77bbddeef843c5e2f178bc5dd178bc5e130984c1209048a3e1f0f879c361b0d86c361b0d8fc7e3f1f8fc7e3f1f7b3d9ecf67b3d9deef77bbddf088442211088442210f178bc5e2f178bb9dcee773b9dcee773ba2f178bc5e2f178bc26130984c2613048241209048245229148a45229147c3e1f0f87c3e1f0f379bcde6f379bcde8f47a3d1e8f47a3d1e8f57abd5eaf57abd5f0f37a3d61b1f7b3be10f17745e13048a3e1e6f47ac363ef677c21e2ee8bc2609147c3cde8f586c7ddf0878bba2f0982451f0f37a3d61b0d86c363f1f8fc7decf67b3d9deef77bbe1108843c5e2f178bb9dcee8bc5e2f0984c2609048245228f87c3e1e6f37a3d01e04121a4ca632e96cc85a361a86632181a8cc63198c0c86c2f17466322d19cbe343317866652e8c8c8632d8c0b4602c15ca80c00800d06230970b2562a94cc0580c8040400300303201011a0c461188bc5c2b14960a8191380800682e164622f1703c08242b14c582b078104857060b432270115ca82d0c804005c2b154622c15810ae0c168044e0200188ac53178b0520f30964aa53170ac520412180b054060640202379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa54298306833190c4602f168b05619148044e0f02090040030964aa5330160a80c340c45e2e310bc582930064025c1883c085801000ae2d13958580f2a8ac08540c94c5224060080200
def restrict5 : List W := [0x1f00001c777f00000000003f81f80fe03fe02a05540aa82abc00000e39cdfc194571dc4cac51138a4b575564ee92ff82aaaaaaaaaaedf0112278e73,0x1f01f87800003e000003ffe000fffc0003046608cc2330003c00fc1f2956fcafe1e511424a48c15ebdd093b7f1289cccccccf3cb6112f04bf07c,0x7dff8000000001f803ffffff00000000017802f00bc0000078ffe032ab2bf7fe06058820938a6bd779fea252514f0f0f0f3cf3822425e3ff80,0x3e07e0000000fc001fffc00000000000000098013000c0003c07f00003cdfcdfb6ce866130ce4fff0e1832438949a1ff00ff03f03f44f41fc9215,0x3ff800000000ffffe0000000000000000000e001c00300003ff800000072fff35b750b82cb7f91383061c38c4e8e46ffff0003ffc088ffe8124a2,0x0,0x1fc00000007fff0000000000000000000000030006000c003fc0000000007fc73cedbbf3ff0c7061c0c1861c3070f078fffffffc0000ff889124948]
def selector6 : Nat := 0x7abd5eb0c86432190c88441ecf67b3d9ecef77bbddeef843c5e2f178bc5dd178bc5e130984c1209048a3e1f0f879c32190c86432190c8844221108844221107b3d9ecf67b3d9deef77bbddf088442211088442210f178bc5e2f178bb9dcee773b9dcee773ba2f178bc5e2f178bc26130984c2613048241209048245229148a45229147c3e1f0f87c3e1f0f379bcde6f379bcde8f47a3d1e8f47a3d1e8f57abd5eaf57abd5f0f37a3d619107b3be10f17745e13048a3e1e6f47ac3220f677c21e2ee8bc2609147c3cde8f586441df0878bba2f0982451f0f37a3d6190c86432211088441ecf67b3d9deef77bbe1108843c5e2f178bb9dcee8bc5e2f0984c2609048245228f87c3e1e6f37a3d01e041212c8e451f8f48c3c271306632181309045198c08c4e200fc66321e12482342410066471f8c88c451e8c078421d0e46c0a008009444218f876381b8d4843a0c8040400210283201011288843188bc5c2b148e86c1913808004a1f0ec622f1703c08241c0d4582b078104839050b43227010e46c2d0c804003e1c0dc622c15810720a168044e02001107035178b0520f218ec6e35170ac5204121087436050640202289409e4e26930964a249208e46229108642209007e3e1e8f0763a1c8e06e361a8286833190c4602f168b05619148044e0f020900400218ec6e35210e86c0a250c45e2e220bc582921064023e1883c083a01000722d138e0580f1b8ac08360c8d45224050080200
def restrict6 : List W := [0x1f00001c777f00000000003f81f80fe03fe02a05540aa82abc00000e39cdfc194571dc4cac51138a4b575564ee92ff82aaaaaaaaaaedf0112278e73,0x1f01f87800003e000003ffe000fffc0003046608cc2330003c00fc1f2956fcafe1e511424a48c15ebdd093b7f1289cccccccf3cb6112f04bf07c,0x7dff8000000001f803ffffff00000000017802f00bc0000078ffe032ab2bf7fe06058820938a6bd779fea252514f0f0f0f3cf3822425e3ff80,0x3e07e0000000fc001fffc00000000000000098013000c0003c07f00003cdfcdfb6ce866130ce4fff0e1832438949a1ff00ff03f03f44f41fc9215,0x3ff800000000ffffe0000000000000000000e001c00300003ff800000072fff35b750b82cb7f91383061c38c4e8e46ffff0003ffc088ffe8124a2,0x1fc00000007fff0000000000000000000000030006000c003fc0000000007fc73cedbbf3ff0c7061c0c1861c3070f078fffffffc0000ff889124948,0x0]
def selection (v : Fin 7) : Nat := match v.val with
  | 0 => selector0
  | 1 => selector1
  | 2 => selector2
  | 3 => selector3
  | 4 => selector4
  | 5 => selector5
  | _ => selector6
def restricted (v : Fin 7) : List W := match v.val with
  | 0 => restrict0
  | 1 => restrict1
  | 2 => restrict2
  | 3 => restrict3
  | 4 => restrict4
  | 5 => restrict5
  | _ => restrict6
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed

def sourceBit (v : Fin 7) (k : Nat) : Nat := (((selection v) >>> (9*k)) % 512) % 476

def pullBits (v : Fin 7) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 476 => w.getLsbD (sourceBit v i.val))).cast List.length_ofFn

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pull_bit (v : Fin 7) (w : W) {k : Nat} (hk : k < 476) :
    (pullBits v w).getLsbD k = w.getLsbD (sourceBit v k) := by
  have len : k < (List.ofFn fun i : Fin 476 => w.getLsbD (sourceBit v i.val)).length := by
    rw [List.length_ofFn]
    exact hk
  rw [pullBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len]
  exact List.getElem_ofFn ..

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pull_and (v : Fin 7) (a b : W) : pullBits v (a &&& b) = pullBits v a &&& pullBits v b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, pull_bit _ _ hi]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pull_or (v : Fin 7) (a b : W) : pullBits v (a ||| b) = pullBits v a ||| pullBits v b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, pull_bit _ _ hi]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pull_not (v : Fin 7) (a : W) : pullBits v (~~~a) = ~~~(pullBits v a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bound : sourceBit v i < 476 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_not, pull_bit _ _ hi, hi, bound, decide_true, Bool.true_and]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pull_goal : ∀ v : Fin 7, pullBits v goal = goal := by
  have check : ∀ v : Fin 7, ∀ i : Fin 476, goal.getLsbD (sourceBit v i.val) = goal.getLsbD i.val := by decide +kernel
  intro v
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (pull_bit v goal hi).trans (check v ⟨i,hi⟩)
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed

def deleteVertex (v : Fin 7) : Pullback :=
  ⟨pullBits v,pull_and v,pull_or v,pull_not v,pull_goal v⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cuts_superset {g} (hg : targetSign g) {k : Nat} {s : Finset W} (ws : List W)
    (sub : s ⊆ ws.toFinset) (run : live basicOps g k s) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨w,hw,sep⟩ := live_separates (differs ⟨j,hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) run
  have hb := (cuts_spec ws ⟨j,hj⟩).mpr ⟨w,List.mem_toFinset.mp (sub hw),sep⟩
  change (cuts ws)[j] = (BitVec.allOnes 238)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hb

def otherRows (a b : W) := rootRows.filter fun x => x != a && x != b

def mergeTest : Bool := rootRows.all fun a => rootRows.all fun b =>
  (a == b) || (ops a b).all fun z => cuts (z::otherRows a b) != -1

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem passedMerge : mergeTest = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem noMerge {a b z : W} (ha : a ∈ rootRows) (hb : b ∈ rootRows) (hne : a ≠ b) (hz : z ∈ ops a b) :
    cuts (z::otherRows a b) ≠ -1 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp passedMerge a ha) b hb
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  exact bne_iff_ne.mp (List.all_eq_true.mp (h.resolve_left hne) z hz)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rootNotOutput (x : W) (hx : x ∈ rootRows) : x ≠ goal ∧ x ≠ ~~~goal := by
  have h : rootRows.all (fun z => (z != goal) && (z != ~~~goal)) = true := by decide +kernel
  simpa only [Bool.and_eq_true,bne_iff_ne] using List.all_eq_true.mp h x hx

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restrictedZero : ∀ v : Fin 7, (restricted v).getD v.val 0 = 0 := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restrictedKnown : ∀ v j : Fin 7,
   (restricted v).getD j.val 0 = 0 ∨ (restricted v).getD j.val 0 ∈ minorRows v := by decide +kernel
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord0_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits0 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 0 k.val)) = (((restricted 0).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord0_0
  · exact coord0_1
  · exact coord0_2
  · exact coord0_3
  · exact coord0_4
  · exact coord0_5
  · exact coord0_6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord1_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits1 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 1 k.val)) = (((restricted 1).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord1_0
  · exact coord1_1
  · exact coord1_2
  · exact coord1_3
  · exact coord1_4
  · exact coord1_5
  · exact coord1_6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord2_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits2 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 2 k.val)) = (((restricted 2).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord2_0
  · exact coord2_1
  · exact coord2_2
  · exact coord2_3
  · exact coord2_4
  · exact coord2_5
  · exact coord2_6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord3_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits3 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 3 k.val)) = (((restricted 3).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord3_0
  · exact coord3_1
  · exact coord3_2
  · exact coord3_3
  · exact coord3_4
  · exact coord3_5
  · exact coord3_6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord4_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits4 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 4 k.val)) = (((restricted 4).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord4_0
  · exact coord4_1
  · exact coord4_2
  · exact coord4_3
  · exact coord4_4
  · exact coord4_5
  · exact coord4_6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord5_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits5 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 5 k.val)) = (((restricted 5).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord5_0
  · exact coord5_1
  · exact coord5_2
  · exact coord5_3
  · exact coord5_4
  · exact coord5_5
  · exact coord5_6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_0 : ∀ k : Fin 476, ((rootRows.getD 0 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 0 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_1 : ∀ k : Fin 476, ((rootRows.getD 1 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 1 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_2 : ∀ k : Fin 476, ((rootRows.getD 2 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 2 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_3 : ∀ k : Fin 476, ((rootRows.getD 3 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 3 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_4 : ∀ k : Fin 476, ((rootRows.getD 4 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 4 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_5 : ∀ k : Fin 476, ((rootRows.getD 5 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 5 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem coord6_6 : ∀ k : Fin 476, ((rootRows.getD 6 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD 6 0).getLsbD k.val) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem vertexBits6 : ∀ j : Fin 7, ∀ k : Fin 476, ((rootRows.getD j.val 0).getLsbD (sourceBit 6 k.val)) = (((restricted 6).getD j.val 0).getLsbD k.val) := by
  intro j
  fin_cases j
  · exact coord6_0
  · exact coord6_1
  · exact coord6_2
  · exact coord6_3
  · exact coord6_4
  · exact coord6_5
  · exact coord6_6
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mappedRaw (v j : Fin 7) : (deleteVertex v).fn (rootRows.getD j.val 0) = (restricted v).getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (pullBits v _).getLsbD i = _
  rw [pull_bit _ _ hi]
  fin_cases v <;> first
    | exact vertexBits0 j ⟨i,hi⟩
    | exact vertexBits1 j ⟨i,hi⟩
    | exact vertexBits2 j ⟨i,hi⟩
    | exact vertexBits3 j ⟨i,hi⟩
    | exact vertexBits4 j ⟨i,hi⟩
    | exact vertexBits5 j ⟨i,hi⟩
    | exact vertexBits6 j ⟨i,hi⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rootIndex {x : W} (hx : x ∈ rootRows.toFinset) : ∃ v : Fin 7, rootRows.getD v.val 0 = x := by
  obtain ⟨v,hv,he⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
  refine ⟨⟨v,hv⟩,?_⟩
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hv,Option.getD_some] using he

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rootStock (v : Fin 7) : inStock (deleteVertex v) (minorRows v).toFinset rootRows.toFinset := by
  intro x hx
  obtain ⟨j,rfl⟩ := rootIndex hx
  rw [mappedRaw]
  rcases restrictedKnown v j with h | h
  · exact .inl h
  · exact .inr (.inr ⟨_,List.mem_toFinset.mpr h,.inl rfl⟩)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restrictRoot {g} (hg : targetSign g) (run : build basicOps g 10 rootRows.toFinset) :
    ∃ v : Fin 7, finish (minorRows v).toFinset 8 := by
  obtain ⟨s,hs,hr⟩ := compress run
  rcases first_live hr with single | ⟨a,ha,b,hb,hab,z,hz,hnew,r,eq,tail⟩
  · have mem : g ∈ rootRows := List.mem_toFinset.mp (hs (by simp [single]))
    rcases hg with rfl | rfl
    · exact ((rootNotOutput _ mem).1 rfl).elim
    · exact ((rootNotOutput _ mem).2 rfl).elim
  have sub : r ⊆ s := fun _ h => eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  have keep : a ∈ r ∨ b ∈ r := by
    by_contra! neither
    have incl : insert z r ⊆ (z :: otherRows a b).toFinset := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hm
      · simp
      · have ha' : w ≠ a := fun h => neither.1 (h ▸ hm)
        have hb' : w ≠ b := fun h => neither.2 (h ▸ hm)
        have mem := List.mem_toFinset.mp (hs (sub hm))
        simp [otherRows,mem,ha',hb']
    exact noMerge (List.mem_toFinset.mp (hs ha)) (List.mem_toFinset.mp (hs hb)) hab
      (List.mem_toFinset.mp hz) (cuts_superset hg _ incl tail)
  obtain ⟨m,hm,hside⟩ : ∃ m ∈ r, m = a ∨ m = b := by
    rcases keep with h | h
    · exact ⟨a,h,.inl rfl⟩
    · exact ⟨b,h,.inr rfl⟩
  obtain ⟨v,hv⟩ := rootIndex (hs (sub hm))
  have zero : (deleteVertex v).fn m = 0 := by rw [← hv,mappedRaw,restrictedZero]
  have atGate : (deleteVertex v).fn a = 0 ∨ (deleteVertex v).fn b = 0 := by
    rcases hside with rfl | rfl <;> simp [zero]
  have old := rootStock v
  have new := mapped_zero (deleteVertex v) hz (old a (hs ha)) (old b (hs hb)) atGate
  have avail : inStock (deleteVertex v) (minorRows v).toFinset (insert z r) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | h
    · exact new
    · exact old w (hs (sub h))
  exact ⟨v, ((project_live (deleteVertex v) hg 9 _ _ tail avail).2 ⟨m,Finset.mem_insert_of_mem hm,zero⟩).2⟩
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
abbrev dead (n : Nat) (ws : List W) :=
  ∀ g : W, (g = goal ∨ g = ~~~goal) → ¬live basicOps g n ws.toFinset

def insertWire (x : W) : List W → List W
  | [] => [x]
  | a::r => if x.toNat ≤ a.toNat then x::a::r else a::insertWire x r
def ordered (ws : List W) := ws.foldr insertWire []
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem insertWire_set (x : W) (ws : List W) : (insertWire x ws).toFinset = insert x ws.toFinset := by
  induction ws with
  | nil => simp [insertWire]
  | cons a r ih =>
    by_cases h : x.toNat ≤ a.toNat
    · simp [insertWire,h]
    · simp [insertWire,h,ih,Finset.insert_comm]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ordered_set (ws : List W) : (ordered ws).toFinset = ws.toFinset := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    change (insertWire a (ordered r)).toFinset = _
    rw [insertWire_set, ih, List.toFinset_cons]

def candidates (n : Nat) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z ∈ ws then [] else
      ((keepChoices a b r).filter (fun kept => decide (kept.length ≤ n) && (cuts (z::kept) == -1))).map
        (fun kept => ordered (z::kept))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem dead_split (n : Nat) (ws : List W) (nd : ws.Nodup) (h₀ : ws ≠ [goal] ∧ ws ≠ [~~~goal])
    (all : ∀ c ∈ candidates n ws, dead n c) : dead (n+1) ws := by
  intro g hg h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have he := singleton_list nd done
    rcases hg with rfl | rfl
    · exact h₀.1 he
    · exact h₀.2 he
  obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : W} (pair : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a::b::r))
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
    obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm nd hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
    have hl : live basicOps g n (z :: kept).toFinset := by simpa [hfin] using tail
    have sz := live_card hl
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at sz
    have sz' : kept.length ≤ n := by omega
    have hcut := cuts_full hg hl
    have out : z ∉ ws := fun mem => hout (List.mem_toFinset.mpr mem)
    have mem : ordered (z::kept) ∈ candidates n ws := by
      refine List.mem_flatMap.mpr ⟨(a,b,r),pair,?_⟩
      refine List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩
      simpa only [out,ite_false,List.mem_map,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using
        (show ∃ w, (w ∈ keepChoices a b r ∧ w.length ≤ n ∧ cuts (z::w) = -1) ∧ ordered (z::w) = ordered (z::kept) from
          ⟨kept,⟨hk,sz',hcut⟩,rfl⟩)
    apply all _ mem g hg
    simpa only [ordered_set] using hl
  rcases hm with pair | pair
  · exact go pair hp hs hz
  · exact go pair (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem dead_leaf (n : Nat) (ws : List W) (nd : ws.Nodup)
    (h : optimized n (n+1-ws.length) ws = false) : dead n ws := by
  intro g hg run
  have sz := live_card run
  rw [List.toFinset_card_of_nodup nd] at sz
  exact Bool.noConfusion (h.symm.trans (optimized_complete hg n ws _ nd (by omega) run))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_dead_cons {n : Nat} {x : List W} {xs : List (List W)}
    (h : dead n x) (hs : ∀ y ∈ xs, dead n y) : ∀ y ∈ x::xs, dead n y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hmem
  · exact h
  · exact hs _ hmem
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_dead_nil (n : Nat) : ∀ y ∈ ([] : List (List W)), dead n y := by simp

def goodChild (n : Nat) (known : List (List W)) (c : List W) : Bool :=
  known.contains c || (decide c.Nodup && !(optimized n (n+1-c.length) c))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem dead_split_checked (n : Nat) (ws : List W) (listed : List (List W)) (nd : ws.Nodup)
   (noOut : ws ≠ [goal] ∧ ws ≠ [~~~goal]) (known : ∀ c ∈ listed, dead n c)
   (pass : (candidates n ws).all (goodChild n listed) = true) : dead (n+1) ws := by
  apply dead_split n ws nd noOut
  intro c hc
  have good := List.all_eq_true.mp pass c hc
  simp only [goodChild,Bool.or_eq_true,List.contains_iff_mem,Bool.and_eq_true,decide_eq_true_eq,
    Bool.not_eq_true'] at good
  rcases good with mem | ⟨hn,hr⟩
  · exact known c mem
  · exact dead_leaf n c hn hr

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem scan_block {α : Type} (xs : List α) (p : α → Bool) (i k : Nat)
    (a : ((xs.drop i).take k).all p = true) (b : (xs.drop (i+k)).all p = true) :
    (xs.drop i).all p = true := by
  rw [← List.take_append_drop k (xs.drop i),List.all_append,a,Bool.true_and,List.drop_drop]
  simpa [Nat.add_comm] using b

end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
def fiveA : List W := [0x28282828282828282828282828282828282828282828282bfffffffffffff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ffffff,0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b000000000000ffff0000ffff0000ffff0000ffff00ffff0000ffff00ff00,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3fffffffffffffffffff00000000ffffffff000000ffffffff000000ffff,0x101010101010101010101010101010101010101010101010000000000000ffffffffffffffff00000000000000ffffffffffffff0000,0x202020202020202020202020202020202020202020202020000000000000ffffffffffffffffffffffffffffff000000000000000000]
def rows9 : List W := [0x8a2288a2288a2288a2288a2288a2288a2288a2288a2288a2288a22bffffffc00ffc00ffc00ffc00ffc00ffc00ffc00fffff003ffffc00fffff,0x2c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b00000fffff00000fffff00000fffff00000fffff003ffffc00fffffffc00,0x1304c1304c1304c1304c1304c1304c1304c1304c1304c1304c1304c3ffffffffffffff0000000000ffffffffff00000003fffffff00000fffff,0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c07000000ffffffffffffffffffff000000000000000003ffffffffffff00000,0x200802008020080200802008020080200802008020080200802008000000fffffffffffffffffffffffffffffffffffffc00000000000000000]
def rows8 : List W := [0x2108421084210bffffffffffffffffffffffffffffffffffffffffffffffc1f07c1ff83ff,0x42108421084213fffffffffffffffffffffffffffffffffffffffffffffffe007fe0ffc1f,0x842108421084200000000000000000000000000000000000000000000007ffff8000fffe0,0x1084210842108400000000000000000000000000000000000000000000007ffffffff00000]
def mapCode0 : Nat := 0x8a45229148a45229148a45229148a45229148a45229148a45229148a45229148a45229148a45229148a45229148a45229148a4521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c521f0a833fdf6f878c5006030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06032a954aa552a954aa552994ca6532994ca65328944a25128944a2512793c9e4f2793c9e4f269349a4d269349a4d2592c964b2592c964b249249249249249249100804020100804020229148a45229148a450d86c361b0d86c361b2090482412090482410984c26130984c261308040201008040201006030180c06030180c028140a05028140a051b8dc6e371b8dc6e370d068341a0d068341a198cc6633198cc66330904824120904824120783c1e0f0783c1e0f0582c160b0582c160b020100804020100804070381c0e070381c0e0180c06030180c0603
def smallerRaw0 : List W := [0x0,0x28282828282828282828282828282828282828282828282bfffffffffffff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ffffff,0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b000000000000ffff0000ffff0000ffff0000ffff00ffff0000ffff00ff00,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3fffffffffffffffffff00000000ffffffff000000ffffffff000000ffff,0x101010101010101010101010101010101010101010101010000000000000ffffffffffffffff00000000000000ffffffffffffff0000,0x202020202020202020202020202020202020202020202020000000000000ffffffffffffffffffffffffffffff000000000000000000]
def mapCode1 : Nat := 0x8b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2d168b45a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845a1d06813f9f4f77845804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804020100804022b158ac562b158ac562a150a8542a150a85429148a45229148a45228140a05028140a050271389c4e271389c4e26130984c26130984c25128944a25128944a0d86c361b0d86c361b231188c46231188c460b85c2e170b85c2e172110884422110884420984c26130984c26130783c1e0f0783c1e0f0582c160b0582c160b0201008040201008041d0e8743a1d0e8743a0b0582c160b0582c161b0d86c361b0d86c36090482412090482412070381c0e070381c0e05028140a05028140a0180c06030180c0603068341a0d068341a0d010080402010080402
def smallerRaw1 : List W := [0x0,0x28282828282828282828282828282828282828282828282bfffffffffffff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ffffff,0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b000000000000ffff0000ffff0000ffff0000ffff00ffff0000ffff00ff00,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3fffffffffffffffffff00000000ffffffff000000ffffffff000000ffff,0x101010101010101010101010101010101010101010101010000000000000ffffffffffffffff00000000000000ffffffffffffff0000,0x202020202020202020202020202020202020202020202020000000000000ffffffffffffffffffffffffffffff000000000000000000]
def mapCode3 : Nat := 0x8c46231188c46231188c46231188c46231188c46231188c46231188c46231188c46231188c46231188c46231188c46231188c462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a462210882401f4ef7a4600c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c06030180c062c160b0582c160b0582a150a8542a150a8542b158ac562b158ac5629148a45229148a45228140a05028140a05026130984c26130984c271389c4e271389c4e0e8743a1d0e8743a1d2412090482412090480c86432190c8643219231188c46231188c460a8542a150a8542a15070381c0e070381c0e0100804020100804020402010080402010081e0f0783c1e0f0783c0c06030180c06030181d0e8743a1d0e8743a0a05028140a0502814068341a0d068341a0d0080402010080402010381c0e070381c0e0706030180c06030180c030180c06030180c06
def smallerRaw3 : List W := [0x0,0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b000000000000ffff0000ffff0000ffff0000ffff00ffff0000ffff00ff00,0x28282828282828282828282828282828282828282828282bfffffffffffff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ffffff,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3fffffffffffffffffff00000000ffffffff000000ffffffff000000ffff,0x101010101010101010101010101010101010101010101010000000000000ffffffffffffffff00000000000000ffffffffffffff0000,0x202020202020202020202020202020202020202020202020000000000000ffffffffffffffffffffffffffffff000000000000000000]
def mapCode5 : Nat := 0x8d46a351a8d46a351a8d46a351a8d46a351a8d46a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846a250e8541e07007d3d5e11a8943a150781c01f4f57846804020100804020100804020100804020100804022d168b45a2d168b45a2d168b0582c160b0582c160b0582b158ac562b158ac562b15846231188c46231188c462329148a45229148a45229148a05028140a05028140a0500f87c3e1f0f87c3e1f0f87c361b0d86c361b0d86c361b25128944a25128944a2512830180c06030180c0603018231188c46231188c462311828140a05028140a0502814070381c0e070381c0e0703810080402010080402010080180c06030180c06030180c783c1e0f0783c1e0f0783c0b85c2e170b85c2e170b85c3c1e0f0783c1e0f0783c1e068341a0d068341a0d068340e070381c0e070381c0e0706030180c06030180c060300402010080402010080402
def smallerRaw5 : List W := [0x0,0x8a2288a2288a2288a2288a2288a2288a2288a2288a2288a2288a22bffffffc00ffc00ffc00ffc00ffc00ffc00ffc00fffff003ffffc00fffff,0x2c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b00000fffff00000fffff00000fffff00000fffff003ffffc00fffffffc00,0x1304c1304c1304c1304c1304c1304c1304c1304c1304c1304c1304c3ffffffffffffff0000000000ffffffffff00000003fffffff00000fffff,0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c07000000ffffffffffffffffffff000000000000000003ffffffffffff00000,0x200802008020080200802008020080200802008020080200802008000000fffffffffffffffffffffffffffffffffffffc00000000000000000]
def mapCode7 : Nat := 0x773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcee773b9dcf57a3c9deee7abd1e4ef773d5e8f277bb9eaf4793bddcf57a3c9deee7abd1e4ef773d5e8f277bb9eaf4793bddcf57a3c9deee7abd1e4ef773d5e8f277bb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002a150a8542a140a0502814088442211088402010080401a0d068341a0c06030180c048241209048180c06030180a05028140a02010080402000000000000
def smallerRaw7 : List W := [0x2108421084210bffffffffffffffffffffffffffffffffffffffffffffffc1f07c1ff83ff,0x0,0x42108421084213fffffffffffffffffffffffffffffffffffffffffffffffe007fe0ffc1f,0x842108421084200000000000000000000000000000000000000000000007ffff8000fffe0,0x1084210842108400000000000000000000000000000000000000000000007ffffffff00000]
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
def sourceCode (v : Nat) (k : Nat) : Nat := ((v >>> (9*k)) % 512) % 476

def projectCode (v : Nat) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 476 => w.getLsbD (sourceCode v i.val))).cast List.length_ofFn

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem code_bit (v : Nat) (w : W) {k : Nat} (hk : k < 476) :
    (projectCode v w).getLsbD k = w.getLsbD (sourceCode v k) := by
  have len : k < (List.ofFn fun i : Fin 476 => w.getLsbD (sourceCode v i.val)).length := by
    rw [List.length_ofFn]
    exact hk
  rw [projectCode, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len]
  exact List.getElem_ofFn ..

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem code_and (v : Nat) (a b : W) : projectCode v (a &&& b) = projectCode v a &&& projectCode v b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, code_bit _ _ hi]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem code_or (v : Nat) (a b : W) : projectCode v (a ||| b) = projectCode v a ||| projectCode v b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, code_bit _ _ hi]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem code_not (v : Nat) (a : W) : projectCode v (~~~a) = ~~~(projectCode v a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bound : sourceCode v i < 476 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_not, code_bit _ _ hi, hi, bound, decide_true, Bool.true_and]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem selectedGoal (code : Nat) (h : ∀ i : Fin 476,
    goal.getLsbD (sourceCode code i.val) = goal.getLsbD i.val) : projectCode code goal = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (code_bit code goal hi).trans (h ⟨i,hi⟩)

def useCode (n : Nat) (hc : projectCode n goal = goal) : Pullback :=
  ⟨projectCode n,code_and n,code_or n,code_not n,hc⟩
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelGoal0 : projectCode mapCode0 goal = goal := selectedGoal _ (by decide +kernel)
def levelMap0 := useCode mapCode0 levelGoal0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit0_0 : ∀ k : Fin 476, (rows0.getD 0 0).getLsbD (sourceCode mapCode0 k.val) = (smallerRaw0.getD 0 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit0_1 : ∀ k : Fin 476, (rows0.getD 1 0).getLsbD (sourceCode mapCode0 k.val) = (smallerRaw0.getD 1 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit0_2 : ∀ k : Fin 476, (rows0.getD 2 0).getLsbD (sourceCode mapCode0 k.val) = (smallerRaw0.getD 2 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit0_3 : ∀ k : Fin 476, (rows0.getD 3 0).getLsbD (sourceCode mapCode0 k.val) = (smallerRaw0.getD 3 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit0_4 : ∀ k : Fin 476, (rows0.getD 4 0).getLsbD (sourceCode mapCode0 k.val) = (smallerRaw0.getD 4 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit0_5 : ∀ k : Fin 476, (rows0.getD 5 0).getLsbD (sourceCode mapCode0 k.val) = (smallerRaw0.getD 5 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelImage0 (j : Fin 6) : (levelMap0).fn (rows0.getD j.val 0) = smallerRaw0.getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (projectCode mapCode0 _).getLsbD k = _
  rw [code_bit _ _ hk]
  fin_cases j
  · exact levelBit0_0 ⟨k,hk⟩
  · exact levelBit0_1 ⟨k,hk⟩
  · exact levelBit0_2 ⟨k,hk⟩
  · exact levelBit0_3 ⟨k,hk⟩
  · exact levelBit0_4 ⟨k,hk⟩
  · exact levelBit0_5 ⟨k,hk⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelGoal1 : projectCode mapCode1 goal = goal := selectedGoal _ (by decide +kernel)
def levelMap1 := useCode mapCode1 levelGoal1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit1_0 : ∀ k : Fin 476, (rows1.getD 0 0).getLsbD (sourceCode mapCode1 k.val) = (smallerRaw1.getD 0 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit1_1 : ∀ k : Fin 476, (rows1.getD 1 0).getLsbD (sourceCode mapCode1 k.val) = (smallerRaw1.getD 1 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit1_2 : ∀ k : Fin 476, (rows1.getD 2 0).getLsbD (sourceCode mapCode1 k.val) = (smallerRaw1.getD 2 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit1_3 : ∀ k : Fin 476, (rows1.getD 3 0).getLsbD (sourceCode mapCode1 k.val) = (smallerRaw1.getD 3 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit1_4 : ∀ k : Fin 476, (rows1.getD 4 0).getLsbD (sourceCode mapCode1 k.val) = (smallerRaw1.getD 4 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit1_5 : ∀ k : Fin 476, (rows1.getD 5 0).getLsbD (sourceCode mapCode1 k.val) = (smallerRaw1.getD 5 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelImage1 (j : Fin 6) : (levelMap1).fn (rows1.getD j.val 0) = smallerRaw1.getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (projectCode mapCode1 _).getLsbD k = _
  rw [code_bit _ _ hk]
  fin_cases j
  · exact levelBit1_0 ⟨k,hk⟩
  · exact levelBit1_1 ⟨k,hk⟩
  · exact levelBit1_2 ⟨k,hk⟩
  · exact levelBit1_3 ⟨k,hk⟩
  · exact levelBit1_4 ⟨k,hk⟩
  · exact levelBit1_5 ⟨k,hk⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelGoal3 : projectCode mapCode3 goal = goal := selectedGoal _ (by decide +kernel)
def levelMap3 := useCode mapCode3 levelGoal3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit3_0 : ∀ k : Fin 476, (rows3.getD 0 0).getLsbD (sourceCode mapCode3 k.val) = (smallerRaw3.getD 0 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit3_1 : ∀ k : Fin 476, (rows3.getD 1 0).getLsbD (sourceCode mapCode3 k.val) = (smallerRaw3.getD 1 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit3_2 : ∀ k : Fin 476, (rows3.getD 2 0).getLsbD (sourceCode mapCode3 k.val) = (smallerRaw3.getD 2 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit3_3 : ∀ k : Fin 476, (rows3.getD 3 0).getLsbD (sourceCode mapCode3 k.val) = (smallerRaw3.getD 3 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit3_4 : ∀ k : Fin 476, (rows3.getD 4 0).getLsbD (sourceCode mapCode3 k.val) = (smallerRaw3.getD 4 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit3_5 : ∀ k : Fin 476, (rows3.getD 5 0).getLsbD (sourceCode mapCode3 k.val) = (smallerRaw3.getD 5 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelImage3 (j : Fin 6) : (levelMap3).fn (rows3.getD j.val 0) = smallerRaw3.getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (projectCode mapCode3 _).getLsbD k = _
  rw [code_bit _ _ hk]
  fin_cases j
  · exact levelBit3_0 ⟨k,hk⟩
  · exact levelBit3_1 ⟨k,hk⟩
  · exact levelBit3_2 ⟨k,hk⟩
  · exact levelBit3_3 ⟨k,hk⟩
  · exact levelBit3_4 ⟨k,hk⟩
  · exact levelBit3_5 ⟨k,hk⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelGoal5 : projectCode mapCode5 goal = goal := selectedGoal _ (by decide +kernel)
def levelMap5 := useCode mapCode5 levelGoal5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit5_0 : ∀ k : Fin 476, (rows5.getD 0 0).getLsbD (sourceCode mapCode5 k.val) = (smallerRaw5.getD 0 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit5_1 : ∀ k : Fin 476, (rows5.getD 1 0).getLsbD (sourceCode mapCode5 k.val) = (smallerRaw5.getD 1 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit5_2 : ∀ k : Fin 476, (rows5.getD 2 0).getLsbD (sourceCode mapCode5 k.val) = (smallerRaw5.getD 2 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit5_3 : ∀ k : Fin 476, (rows5.getD 3 0).getLsbD (sourceCode mapCode5 k.val) = (smallerRaw5.getD 3 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit5_4 : ∀ k : Fin 476, (rows5.getD 4 0).getLsbD (sourceCode mapCode5 k.val) = (smallerRaw5.getD 4 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit5_5 : ∀ k : Fin 476, (rows5.getD 5 0).getLsbD (sourceCode mapCode5 k.val) = (smallerRaw5.getD 5 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelImage5 (j : Fin 6) : (levelMap5).fn (rows5.getD j.val 0) = smallerRaw5.getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (projectCode mapCode5 _).getLsbD k = _
  rw [code_bit _ _ hk]
  fin_cases j
  · exact levelBit5_0 ⟨k,hk⟩
  · exact levelBit5_1 ⟨k,hk⟩
  · exact levelBit5_2 ⟨k,hk⟩
  · exact levelBit5_3 ⟨k,hk⟩
  · exact levelBit5_4 ⟨k,hk⟩
  · exact levelBit5_5 ⟨k,hk⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelGoal7 : projectCode mapCode7 goal = goal := selectedGoal _ (by decide +kernel)
def levelMap7 := useCode mapCode7 levelGoal7
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit7_0 : ∀ k : Fin 476, (fiveA.getD 0 0).getLsbD (sourceCode mapCode7 k.val) = (smallerRaw7.getD 0 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit7_1 : ∀ k : Fin 476, (fiveA.getD 1 0).getLsbD (sourceCode mapCode7 k.val) = (smallerRaw7.getD 1 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit7_2 : ∀ k : Fin 476, (fiveA.getD 2 0).getLsbD (sourceCode mapCode7 k.val) = (smallerRaw7.getD 2 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit7_3 : ∀ k : Fin 476, (fiveA.getD 3 0).getLsbD (sourceCode mapCode7 k.val) = (smallerRaw7.getD 3 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelBit7_4 : ∀ k : Fin 476, (fiveA.getD 4 0).getLsbD (sourceCode mapCode7 k.val) = (smallerRaw7.getD 4 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem levelImage7 (j : Fin 5) : (levelMap7).fn (fiveA.getD j.val 0) = smallerRaw7.getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (projectCode mapCode7 _).getLsbD k = _
  rw [code_bit _ _ hk]
  fin_cases j
  · exact levelBit7_0 ⟨k,hk⟩
  · exact levelBit7_1 ⟨k,hk⟩
  · exact levelBit7_2 ⟨k,hk⟩
  · exact levelBit7_3 ⟨k,hk⟩
  · exact levelBit7_4 ⟨k,hk⟩
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem removeRaw (n : Nat) (p : Pullback) (ws dst : List W) (key : W)
    (loses : cuts (ws.filter (fun w => w != key)) ≠ -1) (zero : p.fn key = 0)
    (stock : inStock p dst.toFinset ws.toFinset) (h : finish ws.toFinset (n+1)) :
    finish dst.toFinset n := by
  obtain ⟨g,hg,builds⟩ := h
  obtain ⟨s,sub,run⟩ := compress builds
  have uses : key ∈ s := by
    by_contra absent
    apply loses (cuts_superset hg _ (fun w hw => ?_) run)
    have neq : w ≠ key := fun e => absent (e ▸ hw)
    simp [List.mem_toFinset.mp (sub hw),neq]
  exact ((project_live p hg (n+1) s _ run (fun w hw => stock w (sub hw))).2 ⟨key,uses,zero⟩).2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem stockOfRows (p : Pullback) (ws dst raw : List W) (m : Nat) (width : ws.length = m)
    (image : ∀ j : Fin m, p.fn (ws.getD j.val 0) = raw.getD j.val 0)
    (h : ∀ j : Fin m, raw.getD j.val 0 = 0 ∨ raw.getD j.val 0 ∈ dst) :
    inStock p dst.toFinset ws.toFinset := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
  let i : Fin m := ⟨j,width ▸ hj⟩
  have row : ws.getD i.val 0 = ws[j] := by
    simp only [i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
  rw [← row,image]
  rcases h i with z | known
  · exact .inl z
  · exact .inr (.inr ⟨_,List.mem_toFinset.mpr known,.inl rfl⟩)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem smaller0 (n : Nat) (h : finish rows0.toFinset (n+1)) : finish fiveA.toFinset n :=
  removeRaw n levelMap0 rows0 fiveA (rows0.getD 0 0) (by decide +kernel)
    ((levelImage0 (0 : Fin 6)).trans (by decide +kernel))
    (stockOfRows _ rows0 fiveA smallerRaw0 6 rfl levelImage0 (by decide +kernel)) h
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem smaller1 (n : Nat) (h : finish rows1.toFinset (n+1)) : finish fiveA.toFinset n :=
  removeRaw n levelMap1 rows1 fiveA (rows1.getD 0 0) (by decide +kernel)
    ((levelImage1 (0 : Fin 6)).trans (by decide +kernel))
    (stockOfRows _ rows1 fiveA smallerRaw1 6 rfl levelImage1 (by decide +kernel)) h
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem smaller3 (n : Nat) (h : finish rows3.toFinset (n+1)) : finish fiveA.toFinset n :=
  removeRaw n levelMap3 rows3 fiveA (rows3.getD 0 0) (by decide +kernel)
    ((levelImage3 (0 : Fin 6)).trans (by decide +kernel))
    (stockOfRows _ rows3 fiveA smallerRaw3 6 rfl levelImage3 (by decide +kernel)) h
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem smaller5 (n : Nat) (h : finish rows5.toFinset (n+1)) : finish rows9.toFinset n :=
  removeRaw n levelMap5 rows5 rows9 (rows5.getD 0 0) (by decide +kernel)
    ((levelImage5 (0 : Fin 6)).trans (by decide +kernel))
    (stockOfRows _ rows5 rows9 smallerRaw5 6 rfl levelImage5 (by decide +kernel)) h
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem smaller7 (n : Nat) (h : finish fiveA.toFinset (n+1)) : finish rows8.toFinset n :=
  removeRaw n levelMap7 fiveA rows8 (fiveA.getD 1 0) (by decide +kernel)
    ((levelImage7 (1 : Fin 5)).trans (by decide +kernel))
    (stockOfRows _ fiveA rows8 smallerRaw7 5 rfl levelImage7 (by decide +kernel)) h
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
def v8_0 : W := 0x2108421084210bffffffffffffffffffffffffffffffffffffffffffffffc1f07c1ff83ff
def v8_1 : W := 0x42108421084213fffffffffffffffffffffffffffffffffffffffffffffffe007fe0ffc1f
def v8_2 : W := 0x842108421084200000000000000000000000000000000000000000000007ffff8000fffe0
def v8_3 : W := 0x1084210842108400000000000000000000000000000000000000000000007ffffffff00000
def hn8_0 : List (List W) := []
def cn8_0 : List (List W) := candidates 5 rows8
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_0 : ((cn8_0.drop 0).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_1 : ((cn8_0.drop 1).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_2 : ((cn8_0.drop 2).take 2).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_3 : ((cn8_0.drop 4).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_4 : ((cn8_0.drop 5).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_5 : ((cn8_0.drop 6).take 2).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_6 : ((cn8_0.drop 8).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_7 : ((cn8_0.drop 9).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_8 : ((cn8_0.drop 10).take 2).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_9 : ((cn8_0.drop 12).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_10 : ((cn8_0.drop 13).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_11 : ((cn8_0.drop 14).take 2).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_12 : ((cn8_0.drop 16).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_13 : ((cn8_0.drop 17).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_14 : ((cn8_0.drop 18).take 2).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_15 : ((cn8_0.drop 20).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_16 : ((cn8_0.drop 21).take 1).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn8_0_17 : ((cn8_0.drop 22).take 2).all (goodChild 5 hn8_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n8_0 : dead 6 rows8 := by
  apply dead_split_checked 5 rows8 hn8_0 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 5
  · exact (scan_block cn8_0 (goodChild 5 hn8_0) 0 1 bn8_0_0 (scan_block cn8_0 (goodChild 5 hn8_0) 1 1 bn8_0_1 (scan_block cn8_0 (goodChild 5 hn8_0) 2 2 bn8_0_2 (scan_block cn8_0 (goodChild 5 hn8_0) 4 1 bn8_0_3 (scan_block cn8_0 (goodChild 5 hn8_0) 5 1 bn8_0_4 (scan_block cn8_0 (goodChild 5 hn8_0) 6 2 bn8_0_5 (scan_block cn8_0 (goodChild 5 hn8_0) 8 1 bn8_0_6 (scan_block cn8_0 (goodChild 5 hn8_0) 9 1 bn8_0_7 (scan_block cn8_0 (goodChild 5 hn8_0) 10 2 bn8_0_8 (scan_block cn8_0 (goodChild 5 hn8_0) 12 1 bn8_0_9 (scan_block cn8_0 (goodChild 5 hn8_0) 13 1 bn8_0_10 (scan_block cn8_0 (goodChild 5 hn8_0) 14 2 bn8_0_11 (scan_block cn8_0 (goodChild 5 hn8_0) 16 1 bn8_0_12 (scan_block cn8_0 (goodChild 5 hn8_0) 17 1 bn8_0_13 (scan_block cn8_0 (goodChild 5 hn8_0) 18 2 bn8_0_14 (scan_block cn8_0 (goodChild 5 hn8_0) 20 1 bn8_0_15 (scan_block cn8_0 (goodChild 5 hn8_0) 21 1 bn8_0_16 (scan_block cn8_0 (goodChild 5 hn8_0) 22 2 bn8_0_17 (by decide +kernel)))))))))))))))))))
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed
def v9_0 : W := 0xfffff00000fffff00000000000000000000003ffffc00fffff00000
def v9_1 : W := 0x3ffffffc00ffc000000000000ffc00ffc0000000003ff003ff00000fffff
def v9_2 : W := 0x2c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b02c0b00000fffff00000fffff00000fffff00000fffff003ffffc00fffffffc00
def v9_3 : W := 0x8a2288a2288a2288a2288a2288a2288a2288a2288a2288a2288a22bffffffc00ffc00ffc00ffc00ffc00ffc00ffc00fffff003ffffc00fffff
def v9_4 : W := 0x1304c1304c1304c1304c1304c1304c1304c1304c1304c1304c1304c3ffffffffffffff0000000000ffffffffff00000003fffffff00000fffff
def v9_5 : W := 0x1c0701c0701c0701c0701c0701c0701c0701c0701c0701c0701c07000000ffffffffffffffffffff000000000000000003ffffffffffff00000
def v9_6 : W := 0x200802008020080200802008020080200802008020080200802008000000fffffffffffffffffffffffffffffffffffffc00000000000000000
def sn9_1 : List W := [v9_1,v9_2,v9_3,v9_4,v9_5,v9_6]
def hn9_1 : List (List W) := []
def cn9_1 : List (List W) := candidates 5 sn9_1
def sn9_2 : List W := [v9_0,v9_2,v9_3,v9_4,v9_5,v9_6]
def hn9_2 : List (List W) := []
def cn9_2 : List (List W) := candidates 5 sn9_2
def hn9_0 : List (List W) := [sn9_1,sn9_2]
def cn9_0 : List (List W) := candidates 6 rows9
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_1_0 : ((cn9_1.drop 0).take 31).all (goodChild 5 hn9_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_1_1 : ((cn9_1.drop 31).take 16).all (goodChild 5 hn9_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n9_1 : dead 6 sn9_1 := by
  apply dead_split_checked 5 sn9_1 hn9_1 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 5
  · exact (scan_block cn9_1 (goodChild 5 hn9_1) 0 31 bn9_1_0 (scan_block cn9_1 (goodChild 5 hn9_1) 31 16 bn9_1_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_2_0 : ((cn9_2.drop 0).take 31).all (goodChild 5 hn9_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_2_1 : ((cn9_2.drop 31).take 16).all (goodChild 5 hn9_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n9_2 : dead 6 sn9_2 := by
  apply dead_split_checked 5 sn9_2 hn9_2 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 5
  · exact (scan_block cn9_2 (goodChild 5 hn9_2) 0 31 bn9_2_0 (scan_block cn9_2 (goodChild 5 hn9_2) 31 16 bn9_2_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_0 : ((cn9_0.drop 0).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_1 : ((cn9_0.drop 2).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_2 : ((cn9_0.drop 3).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_3 : ((cn9_0.drop 5).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_4 : ((cn9_0.drop 6).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_5 : ((cn9_0.drop 8).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_6 : ((cn9_0.drop 10).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_7 : ((cn9_0.drop 11).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_8 : ((cn9_0.drop 12).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_9 : ((cn9_0.drop 13).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_10 : ((cn9_0.drop 14).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_11 : ((cn9_0.drop 16).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_12 : ((cn9_0.drop 18).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_13 : ((cn9_0.drop 19).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_14 : ((cn9_0.drop 21).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_15 : ((cn9_0.drop 22).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_16 : ((cn9_0.drop 24).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_17 : ((cn9_0.drop 25).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_18 : ((cn9_0.drop 26).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_19 : ((cn9_0.drop 28).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_20 : ((cn9_0.drop 30).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_21 : ((cn9_0.drop 31).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_22 : ((cn9_0.drop 32).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_23 : ((cn9_0.drop 33).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_24 : ((cn9_0.drop 34).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_25 : ((cn9_0.drop 36).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_26 : ((cn9_0.drop 37).take 1).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn9_0_27 : ((cn9_0.drop 38).take 2).all (goodChild 6 hn9_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n9_0 : dead 7 rows9 := by
  apply dead_split_checked 6 rows9 hn9_0 (by decide +kernel) (by decide +kernel)
  · exact all_dead_cons n9_1 (all_dead_cons n9_2 (all_dead_nil 6))
  · exact (scan_block cn9_0 (goodChild 6 hn9_0) 0 2 bn9_0_0 (scan_block cn9_0 (goodChild 6 hn9_0) 2 1 bn9_0_1 (scan_block cn9_0 (goodChild 6 hn9_0) 3 2 bn9_0_2 (scan_block cn9_0 (goodChild 6 hn9_0) 5 1 bn9_0_3 (scan_block cn9_0 (goodChild 6 hn9_0) 6 2 bn9_0_4 (scan_block cn9_0 (goodChild 6 hn9_0) 8 2 bn9_0_5 (scan_block cn9_0 (goodChild 6 hn9_0) 10 1 bn9_0_6 (scan_block cn9_0 (goodChild 6 hn9_0) 11 1 bn9_0_7 (scan_block cn9_0 (goodChild 6 hn9_0) 12 1 bn9_0_8 (scan_block cn9_0 (goodChild 6 hn9_0) 13 1 bn9_0_9 (scan_block cn9_0 (goodChild 6 hn9_0) 14 2 bn9_0_10 (scan_block cn9_0 (goodChild 6 hn9_0) 16 2 bn9_0_11 (scan_block cn9_0 (goodChild 6 hn9_0) 18 1 bn9_0_12 (scan_block cn9_0 (goodChild 6 hn9_0) 19 2 bn9_0_13 (scan_block cn9_0 (goodChild 6 hn9_0) 21 1 bn9_0_14 (scan_block cn9_0 (goodChild 6 hn9_0) 22 2 bn9_0_15 (scan_block cn9_0 (goodChild 6 hn9_0) 24 1 bn9_0_16 (scan_block cn9_0 (goodChild 6 hn9_0) 25 1 bn9_0_17 (scan_block cn9_0 (goodChild 6 hn9_0) 26 2 bn9_0_18 (scan_block cn9_0 (goodChild 6 hn9_0) 28 2 bn9_0_19 (scan_block cn9_0 (goodChild 6 hn9_0) 30 1 bn9_0_20 (scan_block cn9_0 (goodChild 6 hn9_0) 31 1 bn9_0_21 (scan_block cn9_0 (goodChild 6 hn9_0) 32 1 bn9_0_22 (scan_block cn9_0 (goodChild 6 hn9_0) 33 1 bn9_0_23 (scan_block cn9_0 (goodChild 6 hn9_0) 34 2 bn9_0_24 (scan_block cn9_0 (goodChild 6 hn9_0) 36 1 bn9_0_25 (scan_block cn9_0 (goodChild 6 hn9_0) 37 1 bn9_0_26 (scan_block cn9_0 (goodChild 6 hn9_0) 38 2 bn9_0_27 (by decide +kernel)))))))))))))))))))))))))))))
end PEqualNP.Outside.L_meta_10636.Signed

namespace PEqualNP.Outside.L_meta_10636.Signed

def essential (ws : List W) := ws.sublists.all fun sub => (cuts sub != -1) || (sub == ws)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish_impossible (n : Nat) (ws : List W) (hess : essential ws = true)
    (reject : dead n ws) : ¬ finish ws.toFinset n := by
  classical
  rintro ⟨g,hg,run⟩
  obtain ⟨s,sub,hl⟩ := compress run
  let take := ws.filter (· ∈ s)
  have eq : take.toFinset = s := by
    ext w
    simp only [take,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun h => List.mem_toFinset.mp (sub h)
  have live' : live basicOps g n take.toFinset := eq.symm ▸ hl
  have mask := cuts_full hg live'
  have same := List.all_eq_true.mp hess take (List.mem_sublists.mpr (List.filter_sublist ..))
  simp only [mask,bne_self_eq_false,Bool.false_or,beq_iff_eq] at same
  exact reject g hg (same ▸ live')

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem impossible4 : ¬ finish rows8.toFinset 6 := finish_impossible 6 _ (by decide +kernel) n8_0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem impossible5 : ¬ finish rows9.toFinset 7 := finish_impossible 7 _ (by decide +kernel) n9_0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem impossibleRoot {g} (hg : targetSign g) : ¬ build basicOps g 10 rootRows.toFinset := by
  intro run
  obtain ⟨v,h⟩ := restrictRoot hg run
  fin_cases v
  · exact impossible4 (smaller7 6 (smaller0 7 h))
  · exact impossible4 (smaller7 6 (smaller1 7 h))
  · exact impossible4 (smaller7 6 (smaller1 7 h))
  · exact impossible4 (smaller7 6 (smaller3 7 h))
  · exact impossible4 (smaller7 6 (smaller3 7 h))
  · exact impossible5 (smaller5 7 h)
  · exact impossible5 (smaller5 7 h)

open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem trueRows : ∀ k : Fin 476, F (fun i => (rootRows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem boundActual (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rootRows, holds rootRows.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu,.inl rfl⟩)
  obtain ⟨g,hs,run⟩ := compile gs o hg rootRows rootRows.toFinset init (by
    intro k
    let read (w : W) := w[k.val]
    let x (i : Fin 7) : Bool := read (rootRows.getD i.val 0)
    have width : rootRows.length = 7 := rfl
    have same : List.ofFn x = rootRows.map read := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < rootRows.length := by simpa using hj
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt,Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (rootRows.map read) = (~~~goal)[k.val]
    rw [←same,he]
    exact trueRows k)
  have lift {a b : Nat} (le : a ≤ b) (r : build basicOps g a rootRows.toFinset) : build basicOps g b rootRows.toFinset := by
    induction le with
    | refl => exact r
    | step _ ih => exact Or.inl ih
  exact impossibleRoot hs (lift low run)
end PEqualNP.Outside.L_meta_10636.Signed
open PEqualNP.Outside.L_meta_10636
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_10636 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 4, 5, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ computes
  by_cases hasNot : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : Signed.binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr ⟨g,mem,by simp [Signed.isBinary,op]⟩
    have lb := Signed.boundActual gs o (fun t ht => legal t ht) (fun x => (computes x).trans (bridge x))
    exact ⟨gates,18,fits,by have n : gates.length = 12 := rfl; omega,exactGates⟩
  · refine ⟨gs,o,fun g hg => ⟨?_,(legal g hg).2⟩,le_rfl,computes⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g,hg,h⟩).elim
