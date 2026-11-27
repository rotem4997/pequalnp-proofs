import PEqualNP.Defs

-- A circuit using NOT needs twelve binary gates. Restriction projects its
-- signed live-wire program onto five-input cofactors, then onto four-input
-- thresholds whose binary gate count is checked by the finite search below.

-- Signed live-wire completeness adapted from open-goat/pequalnp-proofs L_meta_9146, Apache-2.0.
-- The signed live-wire engine and row restrictions follow Kerim Alagün's
-- merged L-meta-10636 (#15157, e648cf35), Apache-2.0.
-- The four-input certificate follows the signed search of k-sandhu's
-- L-meta-8463, as adapted for L-meta-12200.

namespace PEqualNP.Outside.L_meta_12104.Signed

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
abbrev W := BitVec 128
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cuts_spec (ws : List W) (i : Fin 64) :
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
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
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
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
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

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
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

end PEqualNP.Outside.L_meta_12104.Signed
namespace PEqualNP.Outside.L_meta_12104.Signed

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

def flat (w : W) : Prop := w = 0 ∨ w = ~~~(0 : W)

abbrev markedFlat (p : Pullback) (s : Finset W) :=
  ∃ v ∈ s, flat (p.fn v)

theorem mapped_flat (p : Pullback) {av a b z} (hz : z ∈ basicOps a b)
    (ha : holds av (p.fn a)) (hb : holds av (p.fn b))
    (known : flat (p.fn a) ∨ flat (p.fn b)) : holds av (p.fn z) := by
  have hzero : holds av (0 : W) := .inl rfl
  have hones : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have zAnd (w : W) : (0 : W) &&& w = 0 := BitVec.zero_and
  have andZ (w : W) : w &&& (0 : W) = 0 := BitVec.and_zero
  have zOr (w : W) : (0 : W) ||| w = w := BitVec.zero_or
  have orZ (w : W) : w ||| (0 : W) = w := BitVec.or_zero
  have oAnd (w : W) : (~~~(0 : W)) &&& w = w := BitVec.allOnes_and
  have andO (w : W) : w &&& ~~~(0 : W) = w := BitVec.and_allOnes
  have oOr (w : W) : (~~~(0 : W)) ||| w = ~~~(0 : W) := BitVec.allOnes_or
  have orO (w : W) : w ||| ~~~(0 : W) = ~~~(0 : W) := BitVec.or_allOnes
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases known with (h | h) | (h | h) <;> rcases hz with rfl | rfl | rfl | rfl
  all_goals
    simp only [p.mapAnd, p.mapOr, p.mapNot, h, BitVec.not_not,
      zAnd, andZ, zOr, orZ, oAnd, andO, oOr, orO] <;>
    first | exact ha | exact hb | exact hzero | exact hones |
      exact holds_not ha | exact holds_not hb


theorem project_live_flat (p : Pullback) {g} (hg : targetSign g) (n : ℕ) (s av : Finset W)
    (run : live basicOps g n s) (known : inStock p av s) :
    finish av n ∧ (markedFlat p s → n ≠ 0 ∧ finish av (n - 1)) := by
  induction n generalizing s av with
  | zero =>
    change s = {g} at run
    subst s
    refine ⟨finish_of_holds (mapped_goal p hg) (known g (by simp)), ?_⟩
    rintro ⟨m, hm, hmFlat⟩
    rw [Finset.mem_singleton.mp hm] at hmFlat
    obtain ⟨z, one⟩ := target_nonzero (mapped_goal p hg)
    exact (hmFlat.elim z one).elim
  | succ n ih =>
    rcases run with skip | ⟨a,ha,b,hb,hab,z,hz,hnew,r,hs,tail⟩
    · exact ⟨finish_more (ih s av skip known).1,
        fun _ => ⟨Nat.succ_ne_zero _, by simpa using (ih s av skip known).1⟩⟩
    · have sub : r ⊆ s := by
        rw [hs]
        exact fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      have stock {A : Finset W} (old : inStock p A s) (h : holds A (p.fn z)) :
          inStock p A (insert z r) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact h
        · exact old u (sub hr)
      have reach := mapped_reach p hz (known a ha) (known b hb)
      refine ⟨(project_live p hg (n + 1) s av
        (Or.inr ⟨a,ha,b,hb,hab,z,hz,hnew,r,hs,tail⟩) known).1, ?_⟩
      rintro ⟨m,hm,hmFlat⟩
      refine ⟨Nat.succ_ne_zero _, ?_⟩
      change finish av n
      by_cases consume : m = a ∨ m = b
      · have const : flat (p.fn a) ∨ flat (p.fn b) := by
          rcases consume with rfl | rfl
          · exact .inl hmFlat
          · exact .inr hmFlat
        exact (ih _ av tail (stock known (mapped_flat p hz (known a ha) (known b hb) const))).1
      · have mr : m ∈ r := by
          rw [hs] at hm
          simpa [Finset.mem_insert, not_or.mp consume |>.1, not_or.mp consume |>.2] using hm
        have marked : markedFlat p (insert z r) := ⟨m, Finset.mem_insert_of_mem mr, hmFlat⟩
        rcases reach with held | ⟨u,hu,v,hv,ne,w,op,rep⟩
        · exact (ih _ av tail (stock known held)).1
        · obtain ⟨hn,less⟩ := (ih _ (insert w av) tail
              (stock (fun t ht => holds_insert (known t ht)) rep)).2 marked
          have rest := finish_step hu hv ne op less
          simpa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)] using rest

end PEqualNP.Outside.L_meta_12104.Signed


namespace PEqualNP.Outside.L_meta_12104.Cofactors

def map6 : Fin 6 → Fin 6 → Option (Fin 5)
  | 0 => ![none, some 2, some 3, some 0, some 1, some 4]
  | 1 => ![some 2, none, some 3, some 0, some 1, some 4]
  | 2 => ![some 2, some 3, none, some 0, some 1, some 4]
  | 3 => ![some 0, some 1, some 2, none, some 3, some 4]
  | 4 => ![some 0, some 1, some 2, some 3, none, some 4]
  | 5 => ![some 2, some 3, some 4, some 0, some 1, none]

def map5 : Fin 5 → Fin 5 → Option (Fin 4)
  | 0 => ![none, some 0, some 1, some 2, some 3]
  | 1 => ![some 0, none, some 1, some 2, some 3]
  | 2 => ![some 0, some 1, none, some 2, some 3]
  | 3 => ![some 0, some 1, some 2, none, some 3]
  | 4 => ![some 0, some 1, some 2, some 3, none]

def f6 (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676608 * 2 ^ 32 + 3900735488)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem map6None : ∀ p i : Fin 6, map6 p i = none ↔ i = p := by decide +kernel

theorem map5None : ∀ p i : Fin 5, map5 p i = none ↔ i = p := by decide +kernel

end PEqualNP.Outside.L_meta_12104.Cofactors

namespace PEqualNP.Outside.L_meta_12104.Signed
def sourceCode (v : Nat) (k : Nat) : Nat := ((v >>> (7*k)) % 128)

def projectCode (v : Nat) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 128 => w.getLsbD (sourceCode v i.val))).cast List.length_ofFn

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem code_bit (v : Nat) (w : W) {k : Nat} (hk : k < 128) :
    (projectCode v w).getLsbD k = w.getLsbD (sourceCode v k) := by
  have len : k < (List.ofFn fun i : Fin 128 => w.getLsbD (sourceCode v i.val)).length := by
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
  have bound : sourceCode v i < 128 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_not, code_bit _ _ hi, hi, bound, decide_true, Bool.true_and]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem selectedGoal (code : Nat) (h : ∀ i : Fin 128,
    goal.getLsbD (sourceCode code i.val) = goal.getLsbD i.val) : projectCode code goal = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (code_bit code goal hi).trans (h ⟨i,hi⟩)

def useCode (n : Nat) (hc : projectCode n goal = goal) : Pullback :=
  ⟨projectCode n,code_and n,code_or n,code_not n,hc⟩
end PEqualNP.Outside.L_meta_12104.Signed

namespace PEqualNP.Outside.L_meta_12104.Signed

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

abbrev SignedFork {m : ℕ} (raw : Fin m → W) : Prop :=
  ∀ p q : Fin m, p ≠ q → ∀ b : Bool, ∃ l r : Fin 128,
    goal.getLsbD l.val ≠ goal.getLsbD r.val ∧ (raw q).getLsbD l.val = b ∧
      ∀ j : Fin m, j ≠ p → (raw j).getLsbD l.val = (raw j).getLsbD r.val

theorem basicOps_swap {a b z : W} (hz : z ∈ basicOps a b) : z ∈ basicOps b a := by
  simpa [basicOps, ops, BitVec.and_comm a b, BitVec.or_comm a b,
    or_assoc, or_left_comm, or_comm] using hz

private def bitDiff (l r : Fin 128) (w : W) : Prop :=
  w.getLsbD l.val ≠ w.getLsbD r.val

private lemma bitDiff_op (l r : Fin 128) (a b z : W) (hz : z ∈ basicOps a b) :
    bitDiff l r z → bitDiff l r a ∨ bitDiff l r b := by
  intro h
  by_contra! same
  simp only [bitDiff] at h same
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp_all [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, l.isLt, r.isLt]

private lemma bitDiff_goal {g : W} (hg : targetSign g) (l r : Fin 128)
    (h : bitDiff l r goal) : bitDiff l r g := by
  rcases hg with rfl | rfl
  · exact h
  · simpa [bitDiff, BitVec.getLsbD_not, l.isLt, r.isLt] using h

private lemma absorbing_right_rows {a b z : W} (hz : z ∈ basicOps a b) :
    ∃ value : Bool, ∀ l r : Fin 128,
      b.getLsbD l.val = value → b.getLsbD r.val = value →
        z.getLsbD l.val = z.getLsbD r.val := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨false, ?_⟩
    intro l r hl hr
    simp only [BitVec.getLsbD_and, hl, hr, Bool.and_false]
  · refine ⟨true, ?_⟩
    intro l r hl hr
    simp only [BitVec.getLsbD_or, hl, hr, Bool.or_true]
  · refine ⟨true, ?_⟩
    intro l r hl hr
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hl, hr, Bool.not_true, Bool.and_false]
  · refine ⟨false, ?_⟩
    intro l r hl hr
    simp only [BitVec.getLsbD_and, hl, hr, Bool.false_and]

private lemma retaining_left {m : ℕ} (raw : Fin m → W) (fork : SignedFork raw)
    {g z : W} (hg : targetSign g) (i j : Fin m) (ij : i ≠ j)
    (hz : z ∈ basicOps (raw i) (raw j)) {k : ℕ} {rest : Finset W}
    (inRaw : rest ⊆ (List.ofFn raw).toFinset)
    (tail : live basicOps g k (insert z rest)) :
    raw i ∈ rest ∧ z ≠ g := by
  obtain ⟨b, quiet⟩ := absorbing_right_rows hz
  obtain ⟨l,r,goalDiff,jLeft,otherRaw⟩ := fork i j ij b
  have hdiff := bitDiff_goal hg l r goalDiff
  have noZ : ¬ bitDiff l r z := by
    intro disagree
    exact disagree (quiet l r jLeft ((otherRaw j ij.symm).symm.trans jLeft))
  constructor
  · obtain ⟨w,hw,diff⟩ := live_separates (bitDiff l r) hdiff (bitDiff_op l r) tail
    rcases Finset.mem_insert.mp hw with rfl | inRest
    · exact False.elim (noZ diff)
    · obtain ⟨p,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (inRaw inRest))
      have pEq : p = i := by
        by_contra! ne
        exact diff (otherRaw p ne)
      simpa only [pEq] using inRest
  · rintro rfl
    exact noZ hdiff

theorem first_raw_pair {m : ℕ} (raw : Fin m → W) (fork : SignedFork raw)
    (notTarget : ∀ i, ¬ targetSign (raw i)) {k : ℕ} {g : W} (hg : targetSign g)
    (program : build basicOps g (k+1) (List.ofFn raw).toFinset) :
    ∃ i j : Fin m, ∃ z : W, ∃ rest : Finset W,
      i ≠ j ∧ raw i ≠ raw j ∧ z ∈ basicOps (raw i) (raw j) ∧ z ≠ g ∧
      z ≠ raw i ∧ z ≠ raw j ∧ rest ⊆ (List.ofFn raw).toFinset ∧
      raw i ∈ rest ∧ raw j ∈ rest ∧ live basicOps g k (insert z rest) := by
  obtain ⟨s, sub, trace⟩ := compress program
  rcases first_live trace with single | ⟨a,ha,b,hb,hab,z,op,fresh,rest,eq,tail⟩
  · have present : g ∈ s := by rw [single]; simp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (sub present))
    exact False.elim (notTarget i (hi ▸ hg))
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (sub ha))
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (sub hb))
    have ij : i ≠ j := fun h => hab (congrArg raw h)
    have restRaw : rest ⊆ (List.ofFn raw).toFinset := by
      intro w hw
      apply sub
      rw [eq]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
    have iKeep := retaining_left raw fork hg i j ij op restRaw tail
    have jKeep := retaining_left raw fork hg j i ij.symm (basicOps_swap op) restRaw tail
    exact ⟨i,j,z,rest,ij,hab,op,iKeep.2,fun h => fresh (h.symm ▸ ha),
      fun h => fresh (h.symm ▸ hb),restRaw,iKeep.1,jKeep.1,tail⟩

theorem absorbing_left {a b z : W} (hz : z ∈ basicOps a b) :
    ∃ value : Bool,
      ∀ p : Pullback, p.fn a = (if value then ~~~(0 : W) else 0) → flat (p.fn z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨false, ?_⟩
    intro p h
    simp [flat, p.mapAnd, h, BitVec.zero_and]
  · refine ⟨true, ?_⟩
    intro p h
    have zeroNot : ~~~(0 : W) = BitVec.allOnes 128 := BitVec.not_zero
    rw [p.mapOr, show p.fn a = ~~~(0 : W) from h, zeroNot, BitVec.allOnes_or]
    exact Or.inr zeroNot.symm
  · refine ⟨false, ?_⟩
    intro p h
    simp [flat, p.mapAnd, p.mapNot, h, BitVec.zero_and]
  · refine ⟨true, ?_⟩
    intro p h
    simp [flat, p.mapAnd, p.mapNot, h, BitVec.and_zero]

-- Keep track of the partner at the first read of wire.
def firstReader (wire partner goal : W) : ℕ → Finset W → Prop
  | 0, _ => False
  | k + 1, s => firstReader wire partner goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ basicOps a b, z ∉ s ∧
      ∃ rest : Finset W, s = insert a (insert b rest) ∧
        ((((wire = a ∧ partner = b) ∨ (wire = b ∧ partner = a)) ∧
            live basicOps goal k (insert z rest)) ∨
          (wire ≠ a ∧ wire ≠ b ∧ firstReader wire partner goal k (insert z rest)))

theorem locate_first_reader {goal wire : W} (neq : wire ≠ goal)
    {k : ℕ} {s : Finset W} (run : live basicOps goal k s) (present : wire ∈ s) :
    ∃ partner : W, partner ≠ wire ∧ firstReader wire partner goal k s := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at run
    exact False.elim (neq (Finset.mem_singleton.mp (run ▸ present)))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, fresh, rest, eq, tail⟩
    · obtain ⟨partner, ne, proof⟩ := ih skip present
      exact ⟨partner, ne, Or.inl proof⟩
    · by_cases wa : wire = a
      · exact ⟨b, fun e => hab.symm (e.trans wa), Or.inr
          ⟨a, ha, b, hb, hab, z, hz, fresh, rest, eq, Or.inl ⟨Or.inl ⟨wa,rfl⟩,tail⟩⟩⟩
      · by_cases wb : wire = b
        · exact ⟨a, fun e => hab (e.trans wb), Or.inr
            ⟨a, ha, b, hb, hab, z, hz, fresh, rest, eq, Or.inl ⟨Or.inr ⟨wb,rfl⟩,tail⟩⟩⟩
        · have mem : wire ∈ rest := by simpa [eq, wa, wb] using present
          obtain ⟨partner, ne, proof⟩ := ih tail (Finset.mem_insert_of_mem mem)
          exact ⟨partner, ne, Or.inr
            ⟨a, ha, b, hb, hab, z, hz, fresh, rest, eq, Or.inr ⟨wa,wb,proof⟩⟩⟩

theorem first_reader_live {wire partner goal : W} {n : ℕ} {s : Finset W}
    (trace : firstReader wire partner goal n s) : live basicOps goal n s := by
  induction n generalizing s with
  | zero => exact False.elim trace
  | succ n ih =>
    rcases trace with skip | ⟨a,ha,b,hb,hab,w,hw,fresh,rest,eq,read⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨a,ha,b,hb,hab,w,hw,fresh,rest,eq,?_⟩
      rcases read with ⟨_, proof⟩ | ⟨_,_,proof⟩
      · exact proof
      · exact ih proof

-- Collapsing two live wires saves two gates if the tracked first read uses them separately.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem project_two_readers (p : Pullback) {goal wire partner pivot : W}
    (Flat : W → Prop)
    (flat_reach : ∀ {av a b z}, z ∈ basicOps a b → holds av (p.fn a) →
      holds av (p.fn b) → Flat (p.fn a) ∨ Flat (p.fn b) → holds av (p.fn z))
    (oneSave : ∀ n s av, live basicOps goal n s → inStock p av s →
      (∃ v ∈ s, Flat (p.fn v)) → n ≠ 0 ∧ finish av (n-1))
    (wireFlat : Flat (p.fn wire)) (pivotFlat : Flat (p.fn pivot))
    (pivotWire : pivot ≠ wire) (pivotPartner : pivot ≠ partner)
    {n : ℕ} {s av : Finset W} (trace : firstReader wire partner goal n s)
    (wireMem : wire ∈ s) (pivotMem : pivot ∈ s) (known : inStock p av s) :
    2 ≤ n ∧ finish av (n - 2) := by
  induction n generalizing s av with
  | zero => exact False.elim trace
  | succ n ih =>
    rcases trace with skip | ⟨a,ha,b,hb,hab,z,hz,fresh,rest,eq,read⟩
    · obtain ⟨hn, bound⟩ := ih skip wireMem pivotMem known
      refine ⟨by omega, ?_⟩
      have more := finish_more bound
      convert more using 1 <;> omega
    · have sub : rest ⊆ s := by
        rw [eq]
        exact fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
      have stock {A : Finset W} (old : inStock p A s) (emit : holds A (p.fn z)) :
          inStock p A (insert z rest) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | h
        · exact emit
        · exact old u (sub h)
      have keep {v : W} (hv : v ∈ s) (va : v ≠ a) (vb : v ≠ b) :
          v ∈ insert z rest := by
        have : v ∈ rest := by simpa [eq, va, vb] using hv
        exact Finset.mem_insert_of_mem this
      rcases read with ⟨direct, tail⟩ | ⟨wa,wb,trace⟩
      · have flatInputs : Flat (p.fn a) ∨ Flat (p.fn b) := by
          rcases direct with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact Or.inl wireFlat
          · exact Or.inr wireFlat
        have separate : pivot ≠ a ∧ pivot ≠ b := by
          rcases direct with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact ⟨pivotWire,pivotPartner⟩
          · exact ⟨pivotPartner,pivotWire⟩
        obtain ⟨hn, bound⟩ := oneSave n _ av tail
          (stock known (flat_reach hz (known a ha) (known b hb) flatInputs))
          ⟨pivot, keep pivotMem separate.1 separate.2, pivotFlat⟩
        refine ⟨by omega, ?_⟩
        convert bound using 1 <;> omega
      · have tailWire := keep wireMem wa wb
        have tail := first_reader_live trace
        by_cases used : pivot = a ∨ pivot = b
        · have flatInputs : Flat (p.fn a) ∨ Flat (p.fn b) := by
            rcases used with rfl | rfl
            · exact Or.inl pivotFlat
            · exact Or.inr pivotFlat
          obtain ⟨hn, bound⟩ := oneSave n _ av tail
            (stock known (flat_reach hz (known a ha) (known b hb) flatInputs))
              ⟨wire,tailWire,wireFlat⟩
          refine ⟨by omega, ?_⟩
          convert bound using 1 <;> omega
        · have tailPivot := keep pivotMem (not_or.mp used).1 (not_or.mp used).2
          rcases mapped_reach p hz (known a ha) (known b hb) with held | ⟨u,hu,v,hv,ne,w,op,rep⟩
          · obtain ⟨hn, bound⟩ := ih trace tailWire tailPivot (stock known held)
            refine ⟨by omega, ?_⟩
            have more := finish_more bound
            convert more using 1 <;> omega
          · obtain ⟨hn, bound⟩ := ih trace tailWire tailPivot
              (stock (fun t ht => holds_insert (known t ht)) rep)
            refine ⟨by omega, ?_⟩
            have more := finish_step hu hv ne op bound
            convert more using 1 <;> omega

open PEqualNP.Outside.L_meta_12104.Cofactors

def raw6 : Fin 6 → W := ![0xa955508aa8952aaad5bbbeadddf56eef, 0x3266611331264ccce6dddf36eef9b777, 0xc3878223c23870f0f8eeefc7777e3bbb, 0x3f8043c03c07f00ff0ff7f87fbfc3fd, 0xfc0007c003ff80007ff0fbff87dffc3e, 0x7fffc0000007fff03fff81fffc0]

-- The five-input stocks encode majority, three-of-five excluding
-- one triple, and four-of-five, in that order.
def raw5 : Fin 3 → Fin 5 → W
  | 0 => ![0x112a112a112a112aab77ab77ab77ab77, 0x224c224c224c224ccdbbcdbbcdbbcdbb, 0x4470447044704470f1ddf1ddf1ddf1dd, 0x8780878087808780fe1efe1efe1efe1e, 0xf800f800f800f800ffe0ffe0ffe0ffe0]
  | 1 => ![0x895044a82254112a7b6ef6ddedbbdb77, 0x126089304498224cbdb77b6ef6ddedbb, 0x238511c288e14470de3bbc7778eef1dd, 0x3c061e030f018780efc3df87bf0f7e1e, 0xc007e003f001f8000ffc1ff83ff07fe0]
  | 2 => ![0xaaa254aaa8952aaafbefbefbefbefbef, 0xccc4993331264ccc7df7df7df7df7df7, 0xf08e1c3c23870f0befbefbefbefbefb, 0xf00f01fc03c07f00df7df7df7df7df7d, 0xffe0003ff8000efbefbefbefbefbe]

def raw4 (b : Bool) : Fin 4 → W :=
  if b then ![0x802c0300802c03c799e88fc799e88f, 0x6c5201006c520100ecf53968ecf53968, 0x9028802090288020be2aced6be2aced6, 0x30012cc030012cc5346f7f95346f7f9]
  else ![0x3866177038661770ff7fd3fcff7fd3fc, 0x130ac697130ac69793adfeff93adfeff, 0x41d5312941d531296fd77fdf6fd77fdf, 0xacb90806acb90806fcffed33fcffed33]

def stock6 : List W := List.ofFn raw6

def stock5 (t : Fin 3) : List W := List.ofFn (raw5 t)

def stock4 (b : Bool) : List W := List.ofFn (raw4 b)

abbrev allowed6 (p : Fin 6) (b : Bool) : Prop := (p = 3 ∨ p = 4) → b = true

def child6 (p : Fin 6) (b : Bool) : Fin 3 :=
  if p = 3 ∨ p = 4 then 0 else if b then 1 else 2

abbrev allowed5 (t : Fin 3) (p : Fin 5) (b : Bool) : Prop :=
  (t = 1 → b = (p == 0 || p == 1)) ∧ (t = 2 → b = true)

def child5 (t : Fin 3) (b : Bool) : Bool := if t = 2 then false else b

-- Each seven-bit entry selects the source row for a cofactor row.
def packed6 (p : Fin 6) (b : Bool) : Nat :=
  (![0xb34e644b146542ad3e440c1a72ded192e6acd8ad559d1acd39912c51950ab4f9103069cb7b464b9ab362b556746b34e644b146542ad3e440104478426304111e1098c104478426304111e1098c104478426304111e1098c104478426304111e1098c104478426304111e1098c1044784, 0xc76e3d49b1694b875e8498386fddcf8edc7a9362d2970ebd093070dfbb9f1db8f526c5a52e1d7a1260e1bf773e3b71ea4d8b4a5c3af424c102001822834492161c80a0c38281000c1141a2490b0e405061c140800608a0d1248587202830e0a040030450689242c39014187050200182, 0xb34e644af424c1ad3e440bfa72decf8edeacd8ad549b16cd39912bd09306b4f9102fe9cb7b3e3b7ab362b5526c5b34e644af424c1ad3e4400e44703242c3911c0c90b0e44703242c3911c0c90b0e44703242c3911c0c90b0e44703242c3911c0c90b0e44703242c3911c0c90b0e44703, 0xc9723d59d1a94b87628ca858705dd192e47ab3a352970ec51950b0e0bba325c8f56746a52e1d8a32a161c177464b91eace8d4a5c3b14654202002022834493182080a0c3c28100101141a2498c10405061e140800808a0d124c608202830f0a040040450689263041014187850200202, 0xb146542af424c1ad3e440bba325ccf8edeacd8ad52970ec51950abd09306b4f9102ee8c9733e3b7ab362b54a5c3b146542af424c1ad3e4400c3c702202830f1c0880a0c3c702202830f1c0880a0c3c702202830f1c0880a0c3c702202830f1c0880a0c3c702202830f1c0880a0c3c702, 0xcb7a3d59d1aa4d8b669cc898705fd396f47ab3a3549b16cd399130e0bfa72de8f56746a9362d9a732261c17f4e5bd1eace8d526c5b34e64402002032834493182090b0e4428100101941a2498c10485872214080080ca0d124c608242c3910a0400406506892630412161c8850200203, 0, 0xd597263c566c57ad3a6cc972a4c8d597263c566c57ad3a6cc972a4c8d597263c566c57ad3a6cc972a4c8d597263c566c57ad3a6cc972a4c8284c911203c709101c305080c100284c911203c709101c305080c100284c911203c709101c305080c100284c911203c709101c305080c100, 0, 0xd5a7467cd66c57ad56a53a54684fd5a7467cd66c57ad56a53a54684fd5a7467cd66c57ad56a53a54684fd5a7467cd66c57ad56a53a54684f284c911203c70d182c505080c101284c911203c70d182c505080c101284c911203c70d182c505080c101284c911203c70d182c505080c101, 0xb146542af424c1ad3e4408f56746a9362d9a732252970ec51950abd09306b4f91023d59d1aa4d8b669cc894a5c3b146542af424c1ad3e44000101820a04004060828100101820a04004060828100101820a04004060828100101820a04004060828100101820a0400406082810010182, 0xcb7aee8c9733e3b7ab362b58705fd396f5dd192e67c76f566c56b0e0bfa72debba325ccf8edeacd8ad61c17f4e5bd77464b99f1dbd59b15a141878e2834493182090b0e4480a0c3c7141a2498c104858722405061e38a0d124c608242c391202830f1c506892630412161c890141878e] : Fin 12 → Nat) (Fin.ofNat 12 (2 * p.val + if b then 1 else 0))

def packed5Level : Fin 3 → Fin 10 → Nat
  | 0 => ![0x971e6c69b2e24a9f266cf9d2634f89123c9971a349890a4c68f3a74a971e6c69b2e24a9f266cf9d2634f89123c9971a349890a4c68f3a74a0e285071428183182838a0e3850e0e38603183018a060c38e060c60c0e285071428183182838a0e3850e0e38603183018a060c38e060c60c, 0x91162c88b1664c871644591062c191061cc870e645993244199321c391162c88b1664c871644591062c191061cc870e645993244199321c30820109041058500181000218480162c4060824486163430910040850820109041058500181000218480162c406082448616343091004085, 0x971e645992e24a9f2264f9d222cf89123c897162c889064458f3a74a971e645992e24a9f2264f9d222cf89123c897162c889064458f3a74a0c24486122410218243090c3448d0c346021830109040830d040860c0c24486122410218243090c3448d0c346021830109040830d040860c, 0x931a3498d1a6cd871a4c6930a342930a1cd870e6c69b364c29b361c3931a3498d1a6cd871a4c6930a342930a1cd870e6c69b364c29b361c3082018a0610585001c180021c500162c4070828507163838a1004085082018a0610585001c180021c500162c4070828507163838a1004085, 0x971e643992e1499f2264f9b221cf850a3c8970e1c885064438f366c9971e643992e1499f2264f9b221cf850a3c8970e1c885064438f366c90a24485122408114242890a2c48b0a2c5011428089020428b020450a0a24485122408114242890a2c48b0a2c5011428089020428b020450a, 0x951a34a8d1a74e8b1a546951234495122ce8b167469d3a5449d3a2c5951a34a8d1a74e8b1a546951234495122ce8b167469d3a5449d3a2c5082018c0610686001c180041c6001a3440708306071a3838c1008106082018c0610686001c180041c6001a3440708306071a3838c1008106, 0x9712643992e1469d1664e9b161ce850a245970e1c585062c389366c69712643992e1469d1664e9b161ce850a245970e1c585062c389366c60a183050c180000e182860a203080a203800e1c006000028800003870a183050c180000e182860a203080a203800e1c00600002880000387, 0x95264ca93267cf9126549951e4c7951e44f91227c99f3e5479f3e44895264ca93267cf9126549951e4c7951e44f91227c99f3e5479f3e448082c18c0610689022818104286011a3458a083060a1a3850c1608109082c18c0610689022818104286011a3458a083060a1a3850c1608109, 0x8f12443911e146951644a93161ca850a2458f0e1c585062c389264c68f12443911e146951644a93161ca850a2458f0e1c585062c389264c602081010408000060808202101040210180060c0020000084000018302081010408000060808202101040210180060c00200000840000183, 0x9d366ce9b367cf993674d9d2e6cb9d2e64f99327cd9f3e74b9f3e64c9d366ce9b367cf993674d9d2e6cb9d2e64f99327cd9f3e74b9f3e64c102c38c0e206890a283850c286051a3458a103060a1a3850c1618309102c38c0e206890a283850c286051a3458a103060a1a3850c1618309]
  | 1 => ![0, 0x91162c88b1664c871644591062c191061cc870e645993244199321c391162c88b1664c871644591062c191061cc870e645993244199321c30820109041058500181000218480162c4060824486163030910040850820109041058500181000218480162c406082448616303091004085, 0, 0x931a3498d1a6cd871a4c6930a342930a1cd870e6c69b364c29b361c3931a3498d1a6cd871a4c6930a342930a1cd870e6c69b364c29b361c3082018a0610585001c180021c500162c4070828507163438a1004085082018a0610585001c180021c500162c4070828507163438a1004085, 0x971e643992e1499f2264f9b221cf850a3c8970e1c885064438f366c9971e643992e1499f2264f9b221cf850a3c8970e1c885064438f366c90a24485122408114242890a2c48b0a2c5011428089020428b020450a0a24485122408114242890a2c48b0a2c5011428089020428b020450a, 0, 0x9712643992e1469d1664e9b161ce850a245970e1c585062c389366c69712643992e1469d1664e9b161ce850a245970e1c585062c389366c60a183050c180000e182860a203080a203800e1c006000028800003870a183050c180000e182860a203080a203800e1c00600002880000387, 0, 0x8f12443911e146951644a93161ca850a2458f0e1c585062c389264c68f12443911e146951644a93161ca850a2458f0e1c585062c389264c602081010408000060808202101040210180060c0020000084000018302081010408000060808202101040210180060c00200000840000183, 0]
  | 2 => ![0, 0xa126947a5422cdaf2e957a92e3d78b164cba11e3cb8b0e5c79352a4da126947a5422cdaf2e957a92e3d78b164cba11e3cb8b0e5c79352a4d02081010408000060808202141050214180060c0020000085000018302081010408000060808202141050214180060c00200000850000183, 0, 0xa32a947a54634eb12e958ab2e3d88d1a54ba31e3cb8d0e5c79556acea32a947a54634eb12e958ab2e3d88d1a54ba31e3cb8d0e5c79556ace0208101040800008080820214105021420008100020000085000020402081010408000080808202141050214200081000200000850000204, 0, 0xa732a47a94e34eb336a59ab363d98d1a64da71e3cd8d166c79956acea732a47a94e34eb336a59ab363d98d1a64da71e3cd8d166c79956ace020c181060c000080c08302141850214200081000300000850000204020c181060c000080c08302141850214200081000300000850000204, 0, 0xad32bcbaf5a54eb336bd9b1365d9952a64dad2e5cd95266cb9962c4ead32bcbaf5a54eb336bd9b1365d9952a64dad2e5cd95266cb9962c4e040c182060c000080c10304141850414200081000300001050000204040c182060c000080c10304141850414200081000300001050000204, 0, 0xad4ebd2af5a8d5b352bd9b152959a3469d4ad4a954a342a52a762c55ad4ebd2af5a8d5b352bd9b152959a3469d4ad4a954a342a52a762c55040c182060c081080c10304141850414201081008302041050204204040c182060c081080c10304141850414201081008302041050204204]

def packed5 (t : Fin 3) (p : Fin 5) (b : Bool) : Nat :=
  packed5Level t (Fin.ofNat 10 (2 * p.val + if b then 1 else 0))

def constantWord (b : Bool) : W := if b then ~~~0 else 0

def forkCode6 : Nat := 0xa42a586961a90a9a1e586961a687961a708ba2a3810000000960a3818e065828e066838e06704ba1a380a40a38000000008e029028e02a038e02a84c61e580a406580960290100000009602b839602c04c61a680a8066809a02a019a02b8200000009a02c84c81a700aa067009c02a819c02c029c02c830000000

def forkCode5 : Fin 3 → Nat
  | 0 => 0x90261858a1a18586162868616307982618100000008a0a18186062828606303981a180900a180000000086024028602483981628090062808a0240100000008a025039a1630092063008c024818c025020000000
  | 1 => 0x90261858a1a18586162868616307982618100000008a0a18186062828606303981a180900a180000000086024028602483981628090062808a0240100000008a025039a1630092063008c024818c025020000000
  | 2 => 0x960a3818e065828e066838e06704a40a38000000008e029028e02a038e02a84a406580960290100000009602b839602c04a8066809a02a019a02b8200000009a02c84aa067009c02a819c02c029c02c830000000

def forkPair (width code p q : Nat) (b : Bool) : Fin 128 × Fin 128 :=
  let tok := code >>> (14 * (2 * (width * p + q) + if b then 1 else 0))
  (Fin.ofNat 128 tok, Fin.ofNat 128 (tok >>> 7))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem raw6Bits : ∀ k : Fin 128,
    f6 (fun j => (raw6 j).getLsbD k.val) = (~~~goal).getLsbD k.val := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem raw6NotTarget : ∀ i : Fin 6, ¬ targetSign (raw6 i) := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem raw5NotTarget : ∀ t : Fin 3, ∀ i : Fin 5, ¬ targetSign (raw5 t i) := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem fork6Check : ∀ p q : Fin 6, p ≠ q → ∀ b : Bool,
    let pair := forkPair 6 forkCode6 p.val q.val b
    goal.getLsbD pair.1.val ≠ goal.getLsbD pair.2.val ∧
    (raw6 q).getLsbD pair.1.val = b ∧
    ∀ j : Fin 6, j ≠ p → (raw6 j).getLsbD pair.1.val = (raw6 j).getLsbD pair.2.val := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem fork5Check : ∀ t : Fin 3, ∀ p q : Fin 5, p ≠ q → ∀ b : Bool,
    let pair := forkPair 5 (forkCode5 t) p.val q.val b
    goal.getLsbD pair.1.val ≠ goal.getLsbD pair.2.val ∧
    (raw5 t q).getLsbD pair.1.val = b ∧
    ∀ j : Fin 5, j ≠ p → (raw5 t j).getLsbD pair.1.val = (raw5 t j).getLsbD pair.2.val := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem preserves6 : ∀ p : Fin 6, ∀ b : Bool, allowed6 p b →
    ∀ k : Fin 128, goal.getLsbD (sourceCode (packed6 p b) k.val) = goal.getLsbD k.val := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem preserves5 : ∀ t : Fin 3, ∀ p : Fin 5, ∀ b : Bool, allowed5 t p b →
    ∀ k : Fin 128, goal.getLsbD (sourceCode (packed5 t p b) k.val) = goal.getLsbD k.val := by
  decide +kernel

def cut6 (p : Fin 6) (b : Bool) (ok : allowed6 p b) : Pullback :=
  useCode (packed6 p b) (selectedGoal _ (preserves6 p b ok))

def cut5 (t : Fin 3) (p : Fin 5) (b : Bool) (ok : allowed5 t p b) : Pullback :=
  useCode (packed5 t p b) (selectedGoal _ (preserves5 t p b ok))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem projects6 : ∀ p : Fin 6, ∀ b : Bool, allowed6 p b →
    ∀ j : Fin 6, ∀ k : Fin 128,
      (raw6 j).getLsbD (sourceCode (packed6 p b) k.val) =
        ((map6 p j).elim (constantWord b) (raw5 (child6 p b))).getLsbD k.val := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem projects5 : ∀ t : Fin 3, ∀ p : Fin 5, ∀ b : Bool, allowed5 t p b →
    ∀ j : Fin 5, ∀ k : Fin 128,
      (raw5 t j).getLsbD (sourceCode (packed5 t p b) k.val) =
        ((map5 p j).elim (constantWord b) (raw4 (child5 t b))).getLsbD k.val := by
  decide +kernel

theorem cut6Raw (p : Fin 6) (b : Bool) (ok : allowed6 p b) (j : Fin 6) :
    (cut6 p b ok).fn (raw6 j) = (map6 p j).elim (constantWord b) (raw5 (child6 p b)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  exact (code_bit (packed6 p b) (raw6 j) hk).trans (projects6 p b ok j ⟨k,hk⟩)

theorem cut5Raw (t : Fin 3) (p : Fin 5) (b : Bool) (ok : allowed5 t p b) (j : Fin 5) :
    (cut5 t p b ok).fn (raw5 t j) = (map5 p j).elim (constantWord b) (raw4 (child5 t b)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  exact (code_bit (packed5 t p b) (raw5 t j) hk).trans (projects5 t p b ok j ⟨k,hk⟩)


theorem cut6Stock (p : Fin 6) (b : Bool) (ok : allowed6 p b) :
    inStock (cut6 p b ok) (stock5 (child6 p b)).toFinset (stock6.toFinset) := by
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hw)
  rw [cut6Raw]
  cases h : map6 p j with
  | none =>
    cases b
    · exact .inl rfl
    · exact .inr (.inl rfl)
  | some i =>
    exact .inr (.inr ⟨_, List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩), .inl rfl⟩)

theorem cut5Stock (t : Fin 3) (p : Fin 5) (b : Bool) (ok : allowed5 t p b) :
    inStock (cut5 t p b ok) (stock4 (child5 t b)).toFinset (stock5 t).toFinset := by
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hw)
  rw [cut5Raw]
  cases h : map5 p j with
  | none =>
    cases b
    · exact .inl rfl
    · exact .inr (.inl rfl)
  | some i =>
    exact .inr (.inr ⟨_, List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩), .inl rfl⟩)

theorem cut6Pivot (p : Fin 6) (b : Bool) (ok : allowed6 p b) :
    (cut6 p b ok).fn (raw6 p) = constantWord b := by
  rw [cut6Raw, (map6None p p).2 rfl]
  rfl

theorem cut5Pivot (t : Fin 3) (p : Fin 5) (b : Bool) (ok : allowed5 t p b) :
    (cut5 t p b ok).fn (raw5 t p) = constantWord b := by
  rw [cut5Raw, (map5None p p).2 rfl]
  rfl

theorem constantFlat (b : Bool) : flat (constantWord b) := by
  cases b
  · exact .inl rfl
  · exact .inr rfl



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

namespace T3
private def raw0 : W := raw4 false 0
private def raw1 : W := raw4 false 1
private def raw2 : W := raw4 false 2
private def raw3 : W := raw4 false 3
private def rows : List W := [raw0, raw1, raw2, raw3]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem first_0_1 : dispatch 3 (optimized 5) raw0 raw1 [raw2, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_2 : dispatch 3 (optimized 5) raw0 raw2 [raw1, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_3 : dispatch 3 (optimized 5) raw0 raw3 [raw1, raw2] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_1_2 : dispatch 3 (optimized 5) raw1 raw2 [raw0, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_1_3 : dispatch 3 (optimized 5) raw1 raw3 [raw0, raw2] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_2_3 : dispatch 3 (optimized 5) raw2 raw3 [raw0, raw1] = false := by
  decide +kernel

private theorem whole : optimized 6 3 rows = false := by
  change ((rows == [goal] || rows == [~~~goal]) ||
    (pairs rows).any fun (a,b,r) => dispatch 3 (optimized 5) a b r) = false
  have longer : (rows == [goal] || rows == [~~~goal]) = false := by decide +kernel
  rw [longer]
  simp only [Bool.false_or, rows, pairs, singles, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.any_cons, List.any_nil]
  simp only [first_0_1, first_0_2, first_0_3, first_1_2, first_1_3, first_2_3, Bool.false_or]

private theorem proper : ∀ ws ∈ rows.sublists, ws ≠ rows → cuts ws ≠ -1 := by
  decide +kernel

theorem reject : search 6 rows = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hw
  by_cases full : ws = rows
  · subst ws
    have room : 6 + 1 - rows.length = 3 := rfl
    simp [room, whole]
  · have bad : (cuts ws == -1) = false :=
      Bool.eq_false_iff.mpr (fun h => proper ws hw full (beq_iff_eq.mp h))
    rw [bad]
    simp


end T3

namespace T2
private def raw0 : W := raw4 true 0
private def raw1 : W := raw4 true 1
private def raw2 : W := raw4 true 2
private def raw3 : W := raw4 true 3
private def rows : List W := [raw0, raw1, raw2, raw3]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem first_0_1 : dispatch 3 (optimized 5) raw0 raw1 [raw2, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_2 : dispatch 3 (optimized 5) raw0 raw2 [raw1, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_0_3 : dispatch 3 (optimized 5) raw0 raw3 [raw1, raw2] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_1_2 : dispatch 3 (optimized 5) raw1 raw2 [raw0, raw3] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_1_3 : dispatch 3 (optimized 5) raw1 raw3 [raw0, raw2] = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem first_2_3 : dispatch 3 (optimized 5) raw2 raw3 [raw0, raw1] = false := by
  decide +kernel

private theorem whole : optimized 6 3 rows = false := by
  change ((rows == [goal] || rows == [~~~goal]) ||
    (pairs rows).any fun (a,b,r) => dispatch 3 (optimized 5) a b r) = false
  have longer : (rows == [goal] || rows == [~~~goal]) = false := by decide +kernel
  rw [longer]
  simp only [Bool.false_or, rows, pairs, singles, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.any_cons, List.any_nil]
  simp only [first_0_1, first_0_2, first_0_3, first_1_2, first_1_3, first_2_3, Bool.false_or]

private theorem proper : ∀ ws ∈ rows.sublists, ws ≠ rows → cuts ws ≠ -1 := by
  decide +kernel

theorem reject : search 6 rows = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hw
  by_cases full : ws = rows
  · subst ws
    have room : 6 + 1 - rows.length = 3 := rfl
    simp [room, whole]
  · have bad : (cuts ws == -1) = false :=
      Bool.eq_false_iff.mpr (fun h => proper ws hw full (beq_iff_eq.mp h))
    rw [bad]
    simp


end T2

theorem impossible4 (b : Bool) : ¬ finish (stock4 b).toFinset 6 := by
  rintro ⟨t, sign, run⟩
  have good : (stock4 b).Nodup := by cases b <;> decide +kernel
  have check := search_complete sign 6 (stock4 b) good run
  cases b
  · change search 6 T3.rows = true at check
    simp [T3.reject] at check
  · change search 6 T2.rows = true at check
    simp [T2.reject] at check

theorem fork6 : SignedFork raw6 := by
  intro p q neq b
  refine ⟨_, _, fork6Check p q neq b⟩

theorem fork5 (t : Fin 3) : SignedFork (raw5 t) := by
  intro p q neq b
  refine ⟨_, _, fork5Check t p q neq b⟩

private theorem firstStock {m : ℕ} (raw : Fin m → W) {p : Pullback} {av rest : Finset W}
    {i j : Fin m} {z : W} (first : z ∈ basicOps (raw i) (raw j))
    (full : inStock p av (List.ofFn raw).toFinset)
    (sub : rest ⊆ (List.ofFn raw).toFinset)
    (flatPivot : flat (p.fn (raw i))) : inStock p av (insert z rest) := by
  have hi := full (raw i) (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have hj := full (raw j) (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨j,rfl⟩))
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | inRest
  · exact mapped_flat p first hi hj (.inl flatPivot)
  · exact full w (sub inRest)

private theorem oneCut {m : ℕ} (raw : Fin m → W) {p : Pullback} {av rest : Finset W}
    {i j : Fin m} {z g : W} {k : ℕ} (hg : targetSign g)
    (first : z ∈ basicOps (raw i) (raw j)) (full : inStock p av (List.ofFn raw).toFinset)
    (sub : rest ⊆ (List.ofFn raw).toFinset) (kept : raw i ∈ rest)
    (flatPivot : flat (p.fn (raw i)))
    (tail : live basicOps g k (insert z rest)) : finish av (k-1) := by
  exact ((project_live_flat p hg k _ av tail (firstStock raw first full sub flatPivot)).2
    ⟨_, Finset.mem_insert_of_mem kept, flatPivot⟩).2

private theorem twoCut {m : ℕ} (raw : Fin m → W) {p : Pullback} {av rest : Finset W}
    {i j : Fin m} {z g other : W} {k : ℕ} (hg : targetSign g)
    (first : z ∈ basicOps (raw i) (raw j)) (full : inStock p av (List.ofFn raw).toFinset)
    (sub : rest ⊆ (List.ofFn raw).toFinset) (kept : raw i ∈ rest)
    (flatPivot : flat (p.fn (raw i))) (flatWire : flat (p.fn z))
    (pivotWire : raw i ≠ z) (pivotPartner : raw i ≠ other)
    (reader : firstReader z other g k (insert z rest)) : finish av (k-2) :=
  (project_two_readers p flat (mapped_flat p)
    (fun n s av run known => (project_live_flat p hg n s av run known).2)
    flatWire flatPivot pivotWire pivotPartner reader
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem kept)
    (firstStock raw first full sub flatPivot)).2

private theorem orient {m : ℕ} (raw : Fin m → W) {i j : Fin m} {z other : W}
    {rest : Finset W} (different : raw i ≠ raw j) (first : z ∈ basicOps (raw i) (raw j))
    (ni : z ≠ raw i) (nj : z ≠ raw j) (keepI : raw i ∈ rest) (keepJ : raw j ∈ rest) :
    ∃ p q : Fin m, (p = i ∨ p = j) ∧ z ∈ basicOps (raw p) (raw q) ∧
      z ≠ raw p ∧ raw p ∈ rest ∧ raw p ≠ other := by
  by_cases hi : raw i = other
  · exact ⟨j,i,Or.inr rfl,basicOps_swap first,nj,keepJ,
      fun e => different (hi.trans e.symm)⟩
  · exact ⟨i,j,Or.inl rfl,first,ni,keepI,hi⟩

theorem impossible5Small (tag : Fin 3) : ¬ finish (stock5 tag).toFinset 8 := by
  rintro ⟨g, hg, program⟩
  obtain ⟨i,j,z,r,ij,distinct,first,ng,ni,nj,sub,keepI,keepJ,tail⟩ :=
    first_raw_pair (raw5 tag) (fork5 tag) (raw5NotTarget tag) hg program
  let b := if tag = 1 then i == 0 || i == 1 else true
  have ok : allowed5 tag i b := by
    constructor <;> intro ht <;> simp [b, ht]
  have flatPivot : flat ((cut5 tag i b ok).fn (raw5 tag i)) := by
    rw [cut5Pivot]
    exact constantFlat b
  exact impossible4 (child5 tag b)
    (oneCut (raw5 tag) hg first (cut5Stock tag i b ok) sub keepI flatPivot tail)

theorem impossible5Majority : ¬ finish (stock5 0).toFinset 9 := by
  rintro ⟨g, hg, program⟩
  obtain ⟨i,j,z,r,ij,distinct,first,ng,ni,nj,sub,keepI,keepJ,tail⟩ :=
    first_raw_pair (raw5 0) (fork5 0) (raw5NotTarget 0) hg program
  obtain ⟨other, different, read⟩ := locate_first_reader ng tail (Finset.mem_insert_self _ _)
  obtain ⟨p,q,choice,first',np,kept,away⟩ :=
    orient (raw5 0) (other := other) distinct first ni nj keepI keepJ
  obtain ⟨b, absorb⟩ := absorbing_left first'
  have ok : allowed5 0 p b := by simp [allowed5]
  have pivot := cut5Pivot 0 p b ok
  have flatPivot : flat ((cut5 0 p b ok).fn (raw5 0 p)) := by
    rw [pivot]
    exact constantFlat b
  have flatWire := absorb (cut5 0 p b ok) pivot
  exact impossible4 (child5 0 b)
    (twoCut (raw5 0) hg first' (cut5Stock 0 p b ok) sub kept
      flatPivot flatWire np.symm away read)

theorem impossible6 : ¬ finish stock6.toFinset 11 := by
  rintro ⟨g, hg, program⟩
  obtain ⟨i,j,z,r,ij,distinct,first,ng,ni,nj,sub,keepI,keepJ,tail⟩ :=
    first_raw_pair raw6 fork6 raw6NotTarget hg program
  have specialCase {p q : Fin 6} (special : p = 3 ∨ p = 4)
      (op : z ∈ basicOps (raw6 p) (raw6 q)) (keep : raw6 p ∈ r) : False := by
    have ok : allowed6 p true := fun _ => rfl
    have flatPivot : flat ((cut6 p true ok).fn (raw6 p)) := by
      rw [cut6Pivot]
      exact constantFlat true
    have bound := oneCut raw6 hg op (cut6Stock p true ok) sub keep flatPivot tail
    exact impossible5Majority (by simpa [child6,special] using bound)
  by_cases si : i = 3 ∨ i = 4
  · exact specialCase si first keepI
  by_cases sj : j = 3 ∨ j = 4
  · exact specialCase sj (basicOps_swap first) keepJ
  obtain ⟨other, different, read⟩ := locate_first_reader ng tail (Finset.mem_insert_self _ _)
  obtain ⟨p,q,choice,first',np,kept,away⟩ := orient raw6 (other := other) distinct first ni nj keepI keepJ
  have neither : ¬(p = 3 ∨ p = 4) := by
    rcases choice with rfl | rfl
    · exact si
    · exact sj
  obtain ⟨b, absorb⟩ := absorbing_left first'
  have ok : allowed6 p b := fun h => (neither h).elim
  have pivot := cut6Pivot p b ok
  have flatPivot : flat ((cut6 p b ok).fn (raw6 p)) := by
    rw [pivot]
    exact constantFlat b
  have flatWire := absorb (cut6 p b ok) pivot
  exact impossible5Small (child6 p b)
    (twoCut raw6 hg first' (cut6Stock p b ok) sub kept
      flatPivot flatWire np.symm away read)

theorem finishLE {av : Finset W} {a b : ℕ} (le : a ≤ b) (h : finish av a) :
    finish av b := by
  induction le with
  | refl => exact h
  | step _ ih => exact finish_more ih

theorem stock6Finish (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f6 x) :
    finish stock6.toFinset (binaryCost C.gates) := by
  have init : ∀ u ∈ stock6, holds stock6.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have sample (k : Fin 128) :
      (C.gates.foldl step (stock6.map (bit k))).getD C.output false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (raw6 i)
    have same : stock6.map (bit k) = List.ofFn x := by
      simp [stock6, x]
    rw [same]
    exact (computes x).trans (raw6Bits k)
  exact compile C.gates C.output legal stock6 stock6.toFinset init sample

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [2, 5]⟩,
    ⟨.and, [7, 9]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩,
    ⟨.and, [10, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 14]⟩,
    ⟨.and, [15, 16]⟩, ⟨.and, [13, 17]⟩], 18⟩

theorem witnessMonotone : Monotone2 witness := by
  intro g member
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnessEval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = f6 x := by
  decide +kernel

theorem replaceFromLower (lower : ¬finish stock6.toFinset 11)
    (s : ℕ) (original : HasCircuitSize 6 f6 s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f6 x := by
  obtain ⟨C, legal, size, computes⟩ := original
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    refine ⟨witness, witnessMonotone, ?_, witnessEval⟩
    change 13 ≤ s
    by_contra! hs
    exact lower (finishLE (by omega) (stock6Finish C legal computes))
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := legal g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_12104.Signed

theorem PEqualNP.Outside.L_meta_12104 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_12104.Signed.replaceFromLower
    PEqualNP.Outside.L_meta_12104.Signed.impossible6
