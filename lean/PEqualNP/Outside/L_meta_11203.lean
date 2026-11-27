import PEqualNP.Defs

-- The eleven-gate monotone circuit below is checked on every input assignment.
-- With one negation, a shorter circuit could use at most nine binary gates, even if
-- all wire complements were free. Setting input 3 to zero removes an essential input
-- and saves at least one binary gate. The remaining six-input function needs at least
-- nine binary gates. The finite signed live-wire search verifies this last bound.

-- Signed live-wire completeness adapted from open-goat/pequalnp-proofs L_meta_9146, Apache-2.0.
namespace PEqualNP.Outside.L_meta_11203.Signed

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

def F (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 5 && x 6)
end PEqualNP.Outside.L_meta_11203.Signed
namespace PEqualNP.Outside.L_meta_11203
open PEqualNP.CircuitLowerBounds
def gates : List Gate := [⟨.or,[5,6]⟩, ⟨.or,[1,2]⟩, ⟨.and,[8,7]⟩, ⟨.or,[3,4]⟩, ⟨.or,[10,6]⟩, ⟨.and,[0,11]⟩, ⟨.and,[1,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[9,12]⟩, ⟨.or,[13,14]⟩, ⟨.or,[15,16]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem fits : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates, List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = Signed.F x := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem exactGates : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates,17⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_11203

namespace PEqualNP.Outside.L_meta_11203.Signed
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
end PEqualNP.Outside.L_meta_11203.Signed

namespace PEqualNP.Outside.L_meta_11203.Signed
def rootRows : List W := [0xfffe000fff8020200aa0200aa0200aa0001540000001f0000001e3cf1e2fded844fffe2356aaaaad5ab56dab56ad5b6f8888888fc0a2891f8f3c7,0xfffffff000004000acc000acc000acc001598000000000001e3dfc0fe053efe7ffc2244d9b3333366cd9b6cd9b366db511111110494578f7f03f8,0xff000000000000000acf000acf000acf00159e0000000001e79fc1fff003fc424089044a91e3c3c3c78f1e38f1e3c7f1c622222220979e7f07ffc00,0xa4cf00b4cf00b4cf00ab9e01e1e1e1e01f81ffe00000084848912489201fc03fc07f01fc0fe03f87e07f878787907e07ff881041,0xc8f000d8f000d8f000cde001fe01fe001ffe0000000011908f223911c07fffc0007ffe000fffc007ff87f807f8207ff90211208a,0xf00001f00001f00000e00000001ffffe000000000001e20f043c21e119fffffff8000000ffffff800044447ffffa08224224510,0xf00000e00000e00000f00001fffe0000000000000000203f007c03e01e1ffffffffffffff00000000007fffc4442410448448a24]
def rows11 : List W := [0x1ff80000003ff801ff00ffe01ff01422a88aa22a8003c01c738d93289618f72272544bdd6457744fba897fc455555b56aaad111f02f1ce3,0x3ffffe0000ffffe0001803300cc0330000001f83f2a5512aab1144949895eebdd91093df7f8949e6666d9b3cf62221257e0fc,0x3ff003fffffffff00000000000bc02f00bc0000079ffc0346824d3422892ff126f7def7bbfc8a129292787871e3cf3844425e7ff00,0x1ffe007fe00003ffffc00000000000000000014c013008c03c3c07e00003f71c71b9c331cedfff44e89a252513a4a4c0ff807e03f03ff0f41f92425,0x7ffffffc0000000000000000000000007001c00300003ff8000000780781fe7bdff8e2388710e43a3a1c4747237fff8003ffc088ffe824948,0x1fffff800000000000000000000000000000018002000c003fc0000000007fe7ffc07c1e0f03c0f81f07c3c3e078783c7ffffffc0000ff889049292]
def restrictRaw : List W := [0x1ff80000003ff801ff00ffe01ff01422a88aa22a8003c01c738d93289618f72272544bdd6457744fba897fc455555b56aaad111f02f1ce3,0x3ffffe0000ffffe0001803300cc0330000001f83f2a5512aab1144949895eebdd91093df7f8949e6666d9b3cf62221257e0fc,0x3ff003fffffffff00000000000bc02f00bc0000079ffc0346824d3422892ff126f7def7bbfc8a129292787871e3cf3844425e7ff00,0x0,0x1ffe007fe00003ffffc00000000000000000014c013008c03c3c07e00003f71c71b9c331cedfff44e89a252513a4a4c0ff807e03f03ff0f41f92425,0x7ffffffc0000000000000000000000007001c00300003ff8000000780781fe7bdff8e2388710e43a3a1c4747237fff8003ffc088ffe824948,0x1fffff800000000000000000000000000000018002000c003fc0000000007fe7ffc07c1e0f03c0f81f07c3c3e078783c7ffffffc0000ff889049292]
def selector : Nat := 0xa0d0683399cce673399cce673399cce6733198cc6633198cc6633198ca6532994ca6532994ca65320904824120904824120904763b1d8ec763b1d8ec76271389c4e271389c4e271388c46231188c46231188c46030180c06030180c06030180bf9fcfe7f3f9fcfe7f3f9fcfa7d3e9f4fa7d3e9f4fa7c3e1f0f87c3e1f0f87a3d1e8f47a3d1e8f47a3d1e8f178bc5e2f178bc5e2ee773b9dcee773b9dceea0d068341a0d0682f478bba833998ca6411d89c4602fe7d3e1e8f177506632990476271180bf9f4f87a3c5dd419ccc6411d89c4602fe7d3e1e8f17750673399cce6633198cc6532994ca64120904823b1d8ec4e271389c46230180c05fcfe7f3e9f4fa7c3e1e8f47a3c5e2f1773b8200d03aa950a718a391a8b058140403008f934981b0a0984b0903c12aa540c4e67238028080300a9d369918808e47005010023e4d2606c271e0d41c08552391a0b399c81414018047c282612c4e3c1a8401a074ea3c240f049d0220e080340e9c47058160539854141401a6d1a1605808e4150500534280903c4e1107035328b0b01404700a810280300a609812048f02208080d8960f048d41c080681c620b02808140401ab558ab552a550a71f275389b4d265303618a3d1c8d4593096160903c160902808e8733909ce03c0a8441c0a0401028100681c06011f0a0984b1882c0a021f09c78351b0d41c08188280828138401a03008582a1409044200f07034160a048200e050200c0401
end PEqualNP.Outside.L_meta_11203.Signed

namespace PEqualNP.Outside.L_meta_11203.Signed
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
end PEqualNP.Outside.L_meta_11203.Signed

namespace PEqualNP.Outside.L_meta_11203.Signed
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
theorem graphMapGoal : projectCode selector goal = goal := selectedGoal _ (by decide +kernel)
def graphMap := useCode selector graphMapGoal
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit0 : ∀ k : Fin 476, (rootRows.getD 0 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 0 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit1 : ∀ k : Fin 476, (rootRows.getD 1 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 1 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit2 : ∀ k : Fin 476, (rootRows.getD 2 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 2 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit3 : ∀ k : Fin 476, (rootRows.getD 3 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 3 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit4 : ∀ k : Fin 476, (rootRows.getD 4 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 4 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit5 : ∀ k : Fin 476, (rootRows.getD 5 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 5 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem projectedBit6 : ∀ k : Fin 476, (rootRows.getD 6 0).getLsbD (sourceCode selector k.val) = (restrictRaw.getD 6 0).getLsbD k.val := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem graphImage (j : Fin 7) : graphMap.fn (rootRows.getD j.val 0) = restrictRaw.getD j.val 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (projectCode selector _).getLsbD k = _
  rw [code_bit _ _ hk]
  fin_cases j
  · exact projectedBit0 ⟨k,hk⟩
  · exact projectedBit1 ⟨k,hk⟩
  · exact projectedBit2 ⟨k,hk⟩
  · exact projectedBit3 ⟨k,hk⟩
  · exact projectedBit4 ⟨k,hk⟩
  · exact projectedBit5 ⟨k,hk⟩
  · exact projectedBit6 ⟨k,hk⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem deleteLeaf (h : finish rootRows.toFinset 9) : finish rows11.toFinset 8 :=
  removeRaw 8 graphMap rootRows rows11 (rootRows.getD 3 0) (by decide +kernel)
    ((graphImage (3 : Fin 7)).trans (by decide +kernel))
    (stockOfRows _ rootRows rows11 restrictRaw 7 rfl graphImage (by decide +kernel)) h
end PEqualNP.Outside.L_meta_11203.Signed

namespace PEqualNP.Outside.L_meta_11203.Signed
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

end PEqualNP.Outside.L_meta_11203.Signed

namespace PEqualNP.Outside.L_meta_11203.Signed
def v11_0 : W := 0x132096007402020040d804074043a008780455555b54000011080041082
def v11_1 : W := 0x200100aa11449080108610c010121c470101666600033cc000212024048
def v11_2 : W := 0x25412a801004040080e81d010083c078080866666d98000022000048090
def v11_3 : W := 0x40020134228928e0208710e43a380802020278780003cf0000424824900
def v11_4 : W := 0x46824d0020080f0100f01e0783c080101010787871e0000044001049200
def v11_5 : W := 0x780781c0781e0802008010040202004040207fff8000000088888000000
def v11_6 : W := 0x193081018c32042544b4460122405128024c055005a02a02d10140290421
def v11_7 : W := 0x2a51020a9010084989544a898000113248040e6006c03303620200512024
def v11_8 : W := 0xffffe00018003000c0030000000003f0a151228b11449008910821080003556d094986060c1830c6222121000fc
def v11_9 : W := 0x7fe0000001fe000080110044011000000038072245128a30044848894229988009045768009a222248914522220250e01c
def v11_10 : W := 0x3ff801ff00ffe01ff01402a80aa02a8000001c738d8328160084200214435864134445a28838c400005b54002d110002d14a3
def v11_11 : W := 0x3ffffe0000ffffe0001803300cc0330000001f83f000410a021044100000aa15411092cc5b0909006601980cc00201206c0d8
def v11_12 : W := 0x3ffffe0000ffffe0001803300cc0330000001f83f28010002b014090981506a0d810101f078141800000033cf60021253606c
def v11_13 : W := 0x3ffffe0000ffffe0001803300cc0330000001f83f285502a01000004188568ad190081c338884880006d9800362200055a0b4
def v11_14 : W := 0x3ffffe0000ffffe0001803300cc0330000001f83f2a5512aab1144949895eebdd91093df7f8949e6666d9b3cf62221257e0fc
def v11_15 : W := 0x3ff00000001ffff000000000008c023008c000007807c014282451422892b6122114226ab6c0000129218181060c30844425a01f00
def v11_16 : W := 0x3ff003fffffffff00000000000bc02f00bc0000079ffc0346824d3422892ff126f7def7bbfc8a129292787871e3cf3844425e7ff00
def v11_17 : W := 0x3ff003fffffffffffffe000180bf02fc0bf0000079ffff3e7d36fbf33cdbff9b7ffffffbbffdf7f9bdbfe7e7dfbfffe66637f7fffc
def v11_18 : W := 0x1ff8000000000001ff0000001ff00420888222088003c000700d12289410e62262444a114006644c20807684111112448209111e0281c03
def v11_19 : W := 0x1ff80000003ff801ff00ffe01ff01422a88aa22a8003c01c738d93289618f72272544bdd6457744fba897fc455555b56aaad111f02f1ce3
def v11_20 : W := 0x1ff80000003fffffff00fffffff01c23b88ee23b8003c01ff3ffb779bebbf766f6dcdffffddf74dfffffffcdf7777fdfbeff333f27ffcff
def v11_21 : W := 0x7fe00003ffffc00000000000000000004c013000c0003c07e00003801800398321c0dc3f04e0982424138484c080000003f03f00740f92425
def v11_22 : W := 0x7ffffffc0000000000000000000000007001c00300003ff8000000780781fe7bdff8e2388710e43a3a1c4747237fff8003ffc088ffe824948
def v11_23 : W := 0x1ffe007fe00003ffffc00000000000000000014c013008c03c3c07e00003f71c71b9c331cedfff44e89a252513a4a4c0ff807e03f03ff0f41f92425
def v11_24 : W := 0x1fffff800000000000000000000000000000018002000c003fc0000000007fe7ffc07c1e0f03c0f81f07c3c3e078783c7ffffffc0000ff889049292
def v11_25 : W := 0x1fffff8000000000003ffffe0000ffffe0001983320ccc333fc0001f83f2fff7ffeb7d5e9f9bd5febfdfd3d3ff7ff97dffffffff3cf6ffa9b57f2fe
def v11_26 : W := 0x1fffffffe00003ffffc0000000000000000001cc03300cc03ffc07e00003fffffff9ff3fcfdffffcff9fe7e7f3fcfcfcfffffffff03ffffc9fdb6b7
def v11_27 : W := 0x1ffffffffffffc000000000000000000000001f003c00f003ffff80000007fe7fffe7fdfffe3f8ff1fe7fbfbfc7f7f3f7fffffffffc0fffff86dbda
def sn11_1 : List W := [v11_14,v11_16,v11_20,v11_22,v11_23,v11_24]
def hn11_1 : List (List W) := []
def cn11_1 : List (List W) := candidates 6 sn11_1
def sn11_2 : List W := [v11_14,v11_16,v11_19,v11_20,v11_22,v11_23,v11_24]
def hn11_2 : List (List W) := []
def cn11_2 : List (List W) := candidates 6 sn11_2
def sn11_3 : List W := [v11_14,v11_16,v11_18,v11_22,v11_23,v11_24]
def hn11_3 : List (List W) := []
def cn11_3 : List (List W) := candidates 6 sn11_3
def sn11_4 : List W := [v11_14,v11_16,v11_18,v11_19,v11_22,v11_23,v11_24]
def hn11_4 : List (List W) := []
def cn11_4 : List (List W) := candidates 6 sn11_4
def sn11_5 : List W := [v11_9,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_5 : List (List W) := []
def cn11_5 : List (List W) := candidates 6 sn11_5
def sn11_6 : List W := [v11_6,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_6 : List (List W) := []
def cn11_6 : List (List W) := candidates 6 sn11_6
def sn11_7 : List W := [v11_10,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_7 : List (List W) := []
def cn11_7 : List (List W) := candidates 6 sn11_7
def sn11_8 : List W := [v11_0,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_8 : List (List W) := []
def cn11_8 : List (List W) := candidates 6 sn11_8
def sn11_9 : List W := [v11_14,v11_17,v11_19,v11_22,v11_23,v11_24]
def hn11_9 : List (List W) := []
def cn11_9 : List (List W) := candidates 6 sn11_9
def sn11_10 : List W := [v11_14,v11_16,v11_17,v11_19,v11_22,v11_23,v11_24]
def hn11_10 : List (List W) := []
def cn11_10 : List (List W) := candidates 6 sn11_10
def sn11_11 : List W := [v11_8,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_11 : List (List W) := []
def cn11_11 : List (List W) := candidates 6 sn11_11
def sn11_12 : List W := [v11_14,v11_15,v11_19,v11_22,v11_23,v11_24]
def hn11_12 : List (List W) := []
def cn11_12 : List (List W) := candidates 6 sn11_12
def sn11_13 : List W := [v11_7,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_13 : List (List W) := []
def cn11_13 : List (List W) := candidates 6 sn11_13
def sn11_14 : List W := [v11_11,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_14 : List (List W) := []
def cn11_14 : List (List W) := candidates 6 sn11_14
def sn11_15 : List W := [v11_1,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_15 : List (List W) := []
def cn11_15 : List (List W) := candidates 6 sn11_15
def sn11_16 : List W := [v11_13,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_16 : List (List W) := []
def cn11_16 : List (List W) := candidates 6 sn11_16
def sn11_17 : List W := [v11_2,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_17 : List (List W) := []
def cn11_17 : List (List W) := candidates 6 sn11_17
def sn11_18 : List W := [v11_14,v11_16,v11_19,v11_22,v11_23,v11_24,v11_25]
def hn11_18 : List (List W) := []
def cn11_18 : List (List W) := candidates 6 sn11_18
def sn11_19 : List W := [v11_12,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_19 : List (List W) := []
def cn11_19 : List (List W) := candidates 6 sn11_19
def sn11_20 : List W := [v11_3,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_20 : List (List W) := []
def cn11_20 : List (List W) := candidates 6 sn11_20
def sn11_21 : List W := [v11_4,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_21 : List (List W) := []
def cn11_21 : List (List W) := candidates 6 sn11_21
def sn11_22 : List W := [v11_14,v11_16,v11_19,v11_22,v11_24,v11_26]
def hn11_22 : List (List W) := []
def cn11_22 : List (List W) := candidates 6 sn11_22
def sn11_23 : List W := [v11_14,v11_16,v11_19,v11_22,v11_23,v11_24,v11_26]
def hn11_23 : List (List W) := []
def cn11_23 : List (List W) := candidates 6 sn11_23
def sn11_24 : List W := [v11_14,v11_16,v11_19,v11_21,v11_22,v11_24]
def hn11_24 : List (List W) := []
def cn11_24 : List (List W) := candidates 6 sn11_24
def sn11_25 : List W := [v11_14,v11_16,v11_19,v11_21,v11_22,v11_23,v11_24]
def hn11_25 : List (List W) := []
def cn11_25 : List (List W) := candidates 6 sn11_25
def sn11_26 : List W := [v11_5,v11_14,v11_16,v11_19,v11_22,v11_23,v11_24]
def hn11_26 : List (List W) := []
def cn11_26 : List (List W) := candidates 6 sn11_26
def sn11_27 : List W := [v11_14,v11_16,v11_19,v11_22,v11_23,v11_24,v11_27]
def hn11_27 : List (List W) := []
def cn11_27 : List (List W) := candidates 6 sn11_27
def hn11_0 : List (List W) := [sn11_1,sn11_2,sn11_3,sn11_4,sn11_5,sn11_6,sn11_7,sn11_8,sn11_9,sn11_10,sn11_11,sn11_12,sn11_13,sn11_14,sn11_15,sn11_16,sn11_17,sn11_18,sn11_19,sn11_20,sn11_21,sn11_22,sn11_23,sn11_24,sn11_25,sn11_26,sn11_27]
def cn11_0 : List (List W) := candidates 7 rows11
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_0 : ((cn11_1.drop 0).take 1).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_1 : ((cn11_1.drop 1).take 1).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_2 : ((cn11_1.drop 2).take 2).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_3 : ((cn11_1.drop 4).take 9).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_4 : ((cn11_1.drop 13).take 6).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_5 : ((cn11_1.drop 19).take 9).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_6 : ((cn11_1.drop 28).take 15).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_7 : ((cn11_1.drop 43).take 8).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_8 : ((cn11_1.drop 51).take 1).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_9 : ((cn11_1.drop 52).take 8).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_10 : ((cn11_1.drop 60).take 10).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_11 : ((cn11_1.drop 70).take 1).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_1_12 : ((cn11_1.drop 71).take 4).all (goodChild 6 hn11_1) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_1 : dead 7 sn11_1 := by
  apply dead_split_checked 6 sn11_1 hn11_1 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_1 (goodChild 6 hn11_1) 0 1 bn11_1_0 (scan_block cn11_1 (goodChild 6 hn11_1) 1 1 bn11_1_1 (scan_block cn11_1 (goodChild 6 hn11_1) 2 2 bn11_1_2 (scan_block cn11_1 (goodChild 6 hn11_1) 4 9 bn11_1_3 (scan_block cn11_1 (goodChild 6 hn11_1) 13 6 bn11_1_4 (scan_block cn11_1 (goodChild 6 hn11_1) 19 9 bn11_1_5 (scan_block cn11_1 (goodChild 6 hn11_1) 28 15 bn11_1_6 (scan_block cn11_1 (goodChild 6 hn11_1) 43 8 bn11_1_7 (scan_block cn11_1 (goodChild 6 hn11_1) 51 1 bn11_1_8 (scan_block cn11_1 (goodChild 6 hn11_1) 52 8 bn11_1_9 (scan_block cn11_1 (goodChild 6 hn11_1) 60 10 bn11_1_10 (scan_block cn11_1 (goodChild 6 hn11_1) 70 1 bn11_1_11 (scan_block cn11_1 (goodChild 6 hn11_1) 71 4 bn11_1_12 (by decide +kernel))))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_2_0 : ((cn11_2.drop 0).take 2).all (goodChild 6 hn11_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_2_1 : ((cn11_2.drop 2).take 27).all (goodChild 6 hn11_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_2_2 : ((cn11_2.drop 29).take 13).all (goodChild 6 hn11_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_2_3 : ((cn11_2.drop 42).take 6).all (goodChild 6 hn11_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_2_4 : ((cn11_2.drop 48).take 1).all (goodChild 6 hn11_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_2_5 : ((cn11_2.drop 49).take 13).all (goodChild 6 hn11_2) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_2 : dead 7 sn11_2 := by
  apply dead_split_checked 6 sn11_2 hn11_2 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_2 (goodChild 6 hn11_2) 0 2 bn11_2_0 (scan_block cn11_2 (goodChild 6 hn11_2) 2 27 bn11_2_1 (scan_block cn11_2 (goodChild 6 hn11_2) 29 13 bn11_2_2 (scan_block cn11_2 (goodChild 6 hn11_2) 42 6 bn11_2_3 (scan_block cn11_2 (goodChild 6 hn11_2) 48 1 bn11_2_4 (scan_block cn11_2 (goodChild 6 hn11_2) 49 13 bn11_2_5 (by decide +kernel)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_3_0 : ((cn11_3.drop 0).take 21).all (goodChild 6 hn11_3) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_3_1 : ((cn11_3.drop 21).take 43).all (goodChild 6 hn11_3) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_3 : dead 7 sn11_3 := by
  apply dead_split_checked 6 sn11_3 hn11_3 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_3 (goodChild 6 hn11_3) 0 21 bn11_3_0 (scan_block cn11_3 (goodChild 6 hn11_3) 21 43 bn11_3_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_4_0 : ((cn11_4.drop 0).take 42).all (goodChild 6 hn11_4) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_4_1 : ((cn11_4.drop 42).take 7).all (goodChild 6 hn11_4) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_4 : dead 7 sn11_4 := by
  apply dead_split_checked 6 sn11_4 hn11_4 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_4 (goodChild 6 hn11_4) 0 42 bn11_4_0 (scan_block cn11_4 (goodChild 6 hn11_4) 42 7 bn11_4_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_5_0 : ((cn11_5.drop 0).take 27).all (goodChild 6 hn11_5) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_5_1 : ((cn11_5.drop 27).take 17).all (goodChild 6 hn11_5) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_5 : dead 7 sn11_5 := by
  apply dead_split_checked 6 sn11_5 hn11_5 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_5 (goodChild 6 hn11_5) 0 27 bn11_5_0 (scan_block cn11_5 (goodChild 6 hn11_5) 27 17 bn11_5_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_6_0 : ((cn11_6.drop 0).take 25).all (goodChild 6 hn11_6) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_6_1 : ((cn11_6.drop 25).take 21).all (goodChild 6 hn11_6) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_6_2 : ((cn11_6.drop 46).take 12).all (goodChild 6 hn11_6) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_6 : dead 7 sn11_6 := by
  apply dead_split_checked 6 sn11_6 hn11_6 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_6 (goodChild 6 hn11_6) 0 25 bn11_6_0 (scan_block cn11_6 (goodChild 6 hn11_6) 25 21 bn11_6_1 (scan_block cn11_6 (goodChild 6 hn11_6) 46 12 bn11_6_2 (by decide +kernel))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_7_0 : ((cn11_7.drop 0).take 31).all (goodChild 6 hn11_7) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_7_1 : ((cn11_7.drop 31).take 15).all (goodChild 6 hn11_7) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_7 : dead 7 sn11_7 := by
  apply dead_split_checked 6 sn11_7 hn11_7 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_7 (goodChild 6 hn11_7) 0 31 bn11_7_0 (scan_block cn11_7 (goodChild 6 hn11_7) 31 15 bn11_7_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_8_0 : ((cn11_8.drop 0).take 28).all (goodChild 6 hn11_8) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_8_1 : ((cn11_8.drop 28).take 22).all (goodChild 6 hn11_8) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_8 : dead 7 sn11_8 := by
  apply dead_split_checked 6 sn11_8 hn11_8 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_8 (goodChild 6 hn11_8) 0 28 bn11_8_0 (scan_block cn11_8 (goodChild 6 hn11_8) 28 22 bn11_8_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_0 : ((cn11_9.drop 0).take 5).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_1 : ((cn11_9.drop 5).take 1).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_2 : ((cn11_9.drop 6).take 1).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_3 : ((cn11_9.drop 7).take 2).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_4 : ((cn11_9.drop 9).take 10).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_5 : ((cn11_9.drop 19).take 7).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_6 : ((cn11_9.drop 26).take 11).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_7 : ((cn11_9.drop 37).take 16).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_8 : ((cn11_9.drop 53).take 15).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_9 : ((cn11_9.drop 68).take 4).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_9_10 : ((cn11_9.drop 72).take 1).all (goodChild 6 hn11_9) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_9 : dead 7 sn11_9 := by
  apply dead_split_checked 6 sn11_9 hn11_9 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_9 (goodChild 6 hn11_9) 0 5 bn11_9_0 (scan_block cn11_9 (goodChild 6 hn11_9) 5 1 bn11_9_1 (scan_block cn11_9 (goodChild 6 hn11_9) 6 1 bn11_9_2 (scan_block cn11_9 (goodChild 6 hn11_9) 7 2 bn11_9_3 (scan_block cn11_9 (goodChild 6 hn11_9) 9 10 bn11_9_4 (scan_block cn11_9 (goodChild 6 hn11_9) 19 7 bn11_9_5 (scan_block cn11_9 (goodChild 6 hn11_9) 26 11 bn11_9_6 (scan_block cn11_9 (goodChild 6 hn11_9) 37 16 bn11_9_7 (scan_block cn11_9 (goodChild 6 hn11_9) 53 15 bn11_9_8 (scan_block cn11_9 (goodChild 6 hn11_9) 68 4 bn11_9_9 (scan_block cn11_9 (goodChild 6 hn11_9) 72 1 bn11_9_10 (by decide +kernel))))))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_10_0 : ((cn11_10.drop 0).take 14).all (goodChild 6 hn11_10) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_10_1 : ((cn11_10.drop 14).take 24).all (goodChild 6 hn11_10) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_10_2 : ((cn11_10.drop 38).take 20).all (goodChild 6 hn11_10) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_10 : dead 7 sn11_10 := by
  apply dead_split_checked 6 sn11_10 hn11_10 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_10 (goodChild 6 hn11_10) 0 14 bn11_10_0 (scan_block cn11_10 (goodChild 6 hn11_10) 14 24 bn11_10_1 (scan_block cn11_10 (goodChild 6 hn11_10) 38 20 bn11_10_2 (by decide +kernel))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_11_0 : ((cn11_11.drop 0).take 31).all (goodChild 6 hn11_11) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_11_1 : ((cn11_11.drop 31).take 13).all (goodChild 6 hn11_11) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_11 : dead 7 sn11_11 := by
  apply dead_split_checked 6 sn11_11 hn11_11 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_11 (goodChild 6 hn11_11) 0 31 bn11_11_0 (scan_block cn11_11 (goodChild 6 hn11_11) 31 13 bn11_11_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_12_0 : ((cn11_12.drop 0).take 21).all (goodChild 6 hn11_12) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_12_1 : ((cn11_12.drop 21).take 43).all (goodChild 6 hn11_12) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_12 : dead 7 sn11_12 := by
  apply dead_split_checked 6 sn11_12 hn11_12 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_12 (goodChild 6 hn11_12) 0 21 bn11_12_0 (scan_block cn11_12 (goodChild 6 hn11_12) 21 43 bn11_12_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_13_0 : ((cn11_13.drop 0).take 20).all (goodChild 6 hn11_13) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_13_1 : ((cn11_13.drop 20).take 17).all (goodChild 6 hn11_13) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_13_2 : ((cn11_13.drop 37).take 11).all (goodChild 6 hn11_13) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_13_3 : ((cn11_13.drop 48).take 5).all (goodChild 6 hn11_13) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_13 : dead 7 sn11_13 := by
  apply dead_split_checked 6 sn11_13 hn11_13 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_13 (goodChild 6 hn11_13) 0 20 bn11_13_0 (scan_block cn11_13 (goodChild 6 hn11_13) 20 17 bn11_13_1 (scan_block cn11_13 (goodChild 6 hn11_13) 37 11 bn11_13_2 (scan_block cn11_13 (goodChild 6 hn11_13) 48 5 bn11_13_3 (by decide +kernel)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_14_0 : ((cn11_14.drop 0).take 30).all (goodChild 6 hn11_14) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_14_1 : ((cn11_14.drop 30).take 15).all (goodChild 6 hn11_14) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_14 : dead 7 sn11_14 := by
  apply dead_split_checked 6 sn11_14 hn11_14 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_14 (goodChild 6 hn11_14) 0 30 bn11_14_0 (scan_block cn11_14 (goodChild 6 hn11_14) 30 15 bn11_14_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_15_0 : ((cn11_15.drop 0).take 23).all (goodChild 6 hn11_15) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_15_1 : ((cn11_15.drop 23).take 16).all (goodChild 6 hn11_15) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_15_2 : ((cn11_15.drop 39).take 10).all (goodChild 6 hn11_15) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_15_3 : ((cn11_15.drop 49).take 2).all (goodChild 6 hn11_15) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_15 : dead 7 sn11_15 := by
  apply dead_split_checked 6 sn11_15 hn11_15 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_15 (goodChild 6 hn11_15) 0 23 bn11_15_0 (scan_block cn11_15 (goodChild 6 hn11_15) 23 16 bn11_15_1 (scan_block cn11_15 (goodChild 6 hn11_15) 39 10 bn11_15_2 (scan_block cn11_15 (goodChild 6 hn11_15) 49 2 bn11_15_3 (by decide +kernel)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_16_0 : ((cn11_16.drop 0).take 28).all (goodChild 6 hn11_16) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_16_1 : ((cn11_16.drop 28).take 17).all (goodChild 6 hn11_16) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_16 : dead 7 sn11_16 := by
  apply dead_split_checked 6 sn11_16 hn11_16 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_16 (goodChild 6 hn11_16) 0 28 bn11_16_0 (scan_block cn11_16 (goodChild 6 hn11_16) 28 17 bn11_16_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_17_0 : ((cn11_17.drop 0).take 32).all (goodChild 6 hn11_17) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_17_1 : ((cn11_17.drop 32).take 16).all (goodChild 6 hn11_17) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_17 : dead 7 sn11_17 := by
  apply dead_split_checked 6 sn11_17 hn11_17 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_17 (goodChild 6 hn11_17) 0 32 bn11_17_0 (scan_block cn11_17 (goodChild 6 hn11_17) 32 16 bn11_17_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_18_0 : ((cn11_18.drop 0).take 24).all (goodChild 6 hn11_18) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_18_1 : ((cn11_18.drop 24).take 21).all (goodChild 6 hn11_18) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_18 : dead 7 sn11_18 := by
  apply dead_split_checked 6 sn11_18 hn11_18 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_18 (goodChild 6 hn11_18) 0 24 bn11_18_0 (scan_block cn11_18 (goodChild 6 hn11_18) 24 21 bn11_18_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_19_0 : ((cn11_19.drop 0).take 25).all (goodChild 6 hn11_19) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_19_1 : ((cn11_19.drop 25).take 22).all (goodChild 6 hn11_19) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_19_2 : ((cn11_19.drop 47).take 1).all (goodChild 6 hn11_19) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_19 : dead 7 sn11_19 := by
  apply dead_split_checked 6 sn11_19 hn11_19 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_19 (goodChild 6 hn11_19) 0 25 bn11_19_0 (scan_block cn11_19 (goodChild 6 hn11_19) 25 22 bn11_19_1 (scan_block cn11_19 (goodChild 6 hn11_19) 47 1 bn11_19_2 (by decide +kernel))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_20_0 : ((cn11_20.drop 0).take 31).all (goodChild 6 hn11_20) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_20_1 : ((cn11_20.drop 31).take 21).all (goodChild 6 hn11_20) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_20 : dead 7 sn11_20 := by
  apply dead_split_checked 6 sn11_20 hn11_20 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_20 (goodChild 6 hn11_20) 0 31 bn11_20_0 (scan_block cn11_20 (goodChild 6 hn11_20) 31 21 bn11_20_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_21_0 : ((cn11_21.drop 0).take 28).all (goodChild 6 hn11_21) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_21_1 : ((cn11_21.drop 28).take 22).all (goodChild 6 hn11_21) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_21 : dead 7 sn11_21 := by
  apply dead_split_checked 6 sn11_21 hn11_21 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_21 (goodChild 6 hn11_21) 0 28 bn11_21_0 (scan_block cn11_21 (goodChild 6 hn11_21) 28 22 bn11_21_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_22_0 : ((cn11_22.drop 0).take 7).all (goodChild 6 hn11_22) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_22_1 : ((cn11_22.drop 7).take 1).all (goodChild 6 hn11_22) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_22_2 : ((cn11_22.drop 8).take 11).all (goodChild 6 hn11_22) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_22_3 : ((cn11_22.drop 19).take 27).all (goodChild 6 hn11_22) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_22_4 : ((cn11_22.drop 46).take 11).all (goodChild 6 hn11_22) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_22_5 : ((cn11_22.drop 57).take 13).all (goodChild 6 hn11_22) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_22 : dead 7 sn11_22 := by
  apply dead_split_checked 6 sn11_22 hn11_22 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_22 (goodChild 6 hn11_22) 0 7 bn11_22_0 (scan_block cn11_22 (goodChild 6 hn11_22) 7 1 bn11_22_1 (scan_block cn11_22 (goodChild 6 hn11_22) 8 11 bn11_22_2 (scan_block cn11_22 (goodChild 6 hn11_22) 19 27 bn11_22_3 (scan_block cn11_22 (goodChild 6 hn11_22) 46 11 bn11_22_4 (scan_block cn11_22 (goodChild 6 hn11_22) 57 13 bn11_22_5 (by decide +kernel)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_23_0 : ((cn11_23.drop 0).take 22).all (goodChild 6 hn11_23) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_23_1 : ((cn11_23.drop 22).take 28).all (goodChild 6 hn11_23) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_23_2 : ((cn11_23.drop 50).take 7).all (goodChild 6 hn11_23) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_23 : dead 7 sn11_23 := by
  apply dead_split_checked 6 sn11_23 hn11_23 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_23 (goodChild 6 hn11_23) 0 22 bn11_23_0 (scan_block cn11_23 (goodChild 6 hn11_23) 22 28 bn11_23_1 (scan_block cn11_23 (goodChild 6 hn11_23) 50 7 bn11_23_2 (by decide +kernel))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_24_0 : ((cn11_24.drop 0).take 21).all (goodChild 6 hn11_24) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_24_1 : ((cn11_24.drop 21).take 43).all (goodChild 6 hn11_24) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_24 : dead 7 sn11_24 := by
  apply dead_split_checked 6 sn11_24 hn11_24 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_24 (goodChild 6 hn11_24) 0 21 bn11_24_0 (scan_block cn11_24 (goodChild 6 hn11_24) 21 43 bn11_24_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_25_0 : ((cn11_25.drop 0).take 39).all (goodChild 6 hn11_25) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_25_1 : ((cn11_25.drop 39).take 10).all (goodChild 6 hn11_25) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_25 : dead 7 sn11_25 := by
  apply dead_split_checked 6 sn11_25 hn11_25 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_25 (goodChild 6 hn11_25) 0 39 bn11_25_0 (scan_block cn11_25 (goodChild 6 hn11_25) 39 10 bn11_25_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_26_0 : ((cn11_26.drop 0).take 29).all (goodChild 6 hn11_26) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_26_1 : ((cn11_26.drop 29).take 19).all (goodChild 6 hn11_26) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_26 : dead 7 sn11_26 := by
  apply dead_split_checked 6 sn11_26 hn11_26 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_26 (goodChild 6 hn11_26) 0 29 bn11_26_0 (scan_block cn11_26 (goodChild 6 hn11_26) 29 19 bn11_26_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_27_0 : ((cn11_27.drop 0).take 37).all (goodChild 6 hn11_27) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_27_1 : ((cn11_27.drop 37).take 9).all (goodChild 6 hn11_27) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_27 : dead 7 sn11_27 := by
  apply dead_split_checked 6 sn11_27 hn11_27 (by decide +kernel) (by decide +kernel)
  · exact all_dead_nil 6
  · exact (scan_block cn11_27 (goodChild 6 hn11_27) 0 37 bn11_27_0 (scan_block cn11_27 (goodChild 6 hn11_27) 37 9 bn11_27_1 (by decide +kernel)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_0 : ((cn11_0.drop 0).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_1 : ((cn11_0.drop 1).take 6).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_2 : ((cn11_0.drop 7).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_3 : ((cn11_0.drop 8).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_4 : ((cn11_0.drop 9).take 2).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_5 : ((cn11_0.drop 11).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_6 : ((cn11_0.drop 12).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_7 : ((cn11_0.drop 13).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_8 : ((cn11_0.drop 14).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_9 : ((cn11_0.drop 15).take 2).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_10 : ((cn11_0.drop 17).take 2).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_11 : ((cn11_0.drop 19).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_12 : ((cn11_0.drop 20).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_13 : ((cn11_0.drop 21).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_14 : ((cn11_0.drop 22).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_15 : ((cn11_0.drop 23).take 4).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_16 : ((cn11_0.drop 27).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_17 : ((cn11_0.drop 28).take 3).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_18 : ((cn11_0.drop 31).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_19 : ((cn11_0.drop 32).take 3).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_20 : ((cn11_0.drop 35).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_21 : ((cn11_0.drop 36).take 3).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_22 : ((cn11_0.drop 39).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_23 : ((cn11_0.drop 40).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_24 : ((cn11_0.drop 41).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_25 : ((cn11_0.drop 42).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_26 : ((cn11_0.drop 43).take 2).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_27 : ((cn11_0.drop 45).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_28 : ((cn11_0.drop 46).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_29 : ((cn11_0.drop 47).take 2).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_30 : ((cn11_0.drop 49).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_31 : ((cn11_0.drop 50).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_32 : ((cn11_0.drop 51).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_33 : ((cn11_0.drop 52).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_34 : ((cn11_0.drop 53).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_35 : ((cn11_0.drop 54).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_36 : ((cn11_0.drop 55).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_37 : ((cn11_0.drop 56).take 5).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_38 : ((cn11_0.drop 61).take 3).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_39 : ((cn11_0.drop 64).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bn11_0_40 : ((cn11_0.drop 65).take 1).all (goodChild 7 hn11_0) = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem n11_0 : dead 8 rows11 := by
  apply dead_split_checked 7 rows11 hn11_0 (by decide +kernel) (by decide +kernel)
  · exact all_dead_cons n11_1 (all_dead_cons n11_2 (all_dead_cons n11_3 (all_dead_cons n11_4 (all_dead_cons n11_5 (all_dead_cons n11_6 (all_dead_cons n11_7 (all_dead_cons n11_8 (all_dead_cons n11_9 (all_dead_cons n11_10 (all_dead_cons n11_11 (all_dead_cons n11_12 (all_dead_cons n11_13 (all_dead_cons n11_14 (all_dead_cons n11_15 (all_dead_cons n11_16 (all_dead_cons n11_17 (all_dead_cons n11_18 (all_dead_cons n11_19 (all_dead_cons n11_20 (all_dead_cons n11_21 (all_dead_cons n11_22 (all_dead_cons n11_23 (all_dead_cons n11_24 (all_dead_cons n11_25 (all_dead_cons n11_26 (all_dead_cons n11_27 (all_dead_nil 7)))))))))))))))))))))))))))
  · exact (scan_block cn11_0 (goodChild 7 hn11_0) 0 1 bn11_0_0 (scan_block cn11_0 (goodChild 7 hn11_0) 1 6 bn11_0_1 (scan_block cn11_0 (goodChild 7 hn11_0) 7 1 bn11_0_2 (scan_block cn11_0 (goodChild 7 hn11_0) 8 1 bn11_0_3 (scan_block cn11_0 (goodChild 7 hn11_0) 9 2 bn11_0_4 (scan_block cn11_0 (goodChild 7 hn11_0) 11 1 bn11_0_5 (scan_block cn11_0 (goodChild 7 hn11_0) 12 1 bn11_0_6 (scan_block cn11_0 (goodChild 7 hn11_0) 13 1 bn11_0_7 (scan_block cn11_0 (goodChild 7 hn11_0) 14 1 bn11_0_8 (scan_block cn11_0 (goodChild 7 hn11_0) 15 2 bn11_0_9 (scan_block cn11_0 (goodChild 7 hn11_0) 17 2 bn11_0_10 (scan_block cn11_0 (goodChild 7 hn11_0) 19 1 bn11_0_11 (scan_block cn11_0 (goodChild 7 hn11_0) 20 1 bn11_0_12 (scan_block cn11_0 (goodChild 7 hn11_0) 21 1 bn11_0_13 (scan_block cn11_0 (goodChild 7 hn11_0) 22 1 bn11_0_14 (scan_block cn11_0 (goodChild 7 hn11_0) 23 4 bn11_0_15 (scan_block cn11_0 (goodChild 7 hn11_0) 27 1 bn11_0_16 (scan_block cn11_0 (goodChild 7 hn11_0) 28 3 bn11_0_17 (scan_block cn11_0 (goodChild 7 hn11_0) 31 1 bn11_0_18 (scan_block cn11_0 (goodChild 7 hn11_0) 32 3 bn11_0_19 (scan_block cn11_0 (goodChild 7 hn11_0) 35 1 bn11_0_20 (scan_block cn11_0 (goodChild 7 hn11_0) 36 3 bn11_0_21 (scan_block cn11_0 (goodChild 7 hn11_0) 39 1 bn11_0_22 (scan_block cn11_0 (goodChild 7 hn11_0) 40 1 bn11_0_23 (scan_block cn11_0 (goodChild 7 hn11_0) 41 1 bn11_0_24 (scan_block cn11_0 (goodChild 7 hn11_0) 42 1 bn11_0_25 (scan_block cn11_0 (goodChild 7 hn11_0) 43 2 bn11_0_26 (scan_block cn11_0 (goodChild 7 hn11_0) 45 1 bn11_0_27 (scan_block cn11_0 (goodChild 7 hn11_0) 46 1 bn11_0_28 (scan_block cn11_0 (goodChild 7 hn11_0) 47 2 bn11_0_29 (scan_block cn11_0 (goodChild 7 hn11_0) 49 1 bn11_0_30 (scan_block cn11_0 (goodChild 7 hn11_0) 50 1 bn11_0_31 (scan_block cn11_0 (goodChild 7 hn11_0) 51 1 bn11_0_32 (scan_block cn11_0 (goodChild 7 hn11_0) 52 1 bn11_0_33 (scan_block cn11_0 (goodChild 7 hn11_0) 53 1 bn11_0_34 (scan_block cn11_0 (goodChild 7 hn11_0) 54 1 bn11_0_35 (scan_block cn11_0 (goodChild 7 hn11_0) 55 1 bn11_0_36 (scan_block cn11_0 (goodChild 7 hn11_0) 56 5 bn11_0_37 (scan_block cn11_0 (goodChild 7 hn11_0) 61 3 bn11_0_38 (scan_block cn11_0 (goodChild 7 hn11_0) 64 1 bn11_0_39 (scan_block cn11_0 (goodChild 7 hn11_0) 65 1 bn11_0_40 (by decide +kernel))))))))))))))))))))))))))))))))))))))))))
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
theorem impossibleRoot {g} (hg : targetSign g) (b : build basicOps g 9 rootRows.toFinset) : False :=
  finish_impossible 8 rows11 (by decide +kernel) n11_0 (deleteLeaf ⟨g,hg,b⟩)
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem trueRows : ∀ k : Fin 476, F (fun i => (rootRows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem boundActual (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 9 < binaryCost gs := by
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
end PEqualNP.Outside.L_meta_11203.Signed

open PEqualNP.Outside.L_meta_11203
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_11203 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ computes
  by_cases hasNot : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : Signed.binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr ⟨g,mem,by simp [Signed.isBinary,op]⟩
    have lb := Signed.boundActual gs o (fun t ht => legal t ht) (fun x => (computes x).trans (bridge x))
    exact ⟨gates,17,fits,by have n : gates.length = 11 := rfl; omega,exactGates⟩
  · refine ⟨gs,o,fun g hg => ⟨?_,(legal g hg).2⟩,le_rfl,computes⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g,hg,h⟩).elim
