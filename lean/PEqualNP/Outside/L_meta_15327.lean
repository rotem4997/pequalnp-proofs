import Mathlib
import PEqualNP.Defs

-- A monotone witness is checked on every input. Even if wire negations are free,
-- the certified live-wire search requires at least one fewer binary gate than the witness.
-- The compiler and search are adapted from the proof of L-meta-8724.
namespace PEqualNP.Outside.L_meta_15327

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
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

-- The upper and lower halves represent opposite target labels on 64 pairs of assignments.
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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

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

theorem cuts_spec (ws : List W) (i : Fin 64) :
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
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
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

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 128 rows at once, NOT gates cost nothing.
private def bit (k : Fin 128) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

set_option maxRecDepth 5000 in
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
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def table (x : Fin 6 → Bool) : Bool := Nat.testBit (3937061000 * 2 ^ 32 + 3903373312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

-- The least significant 60-bit chunk is stored first.
def fromChunks (parts : List ℕ) : ℕ := parts.foldr (fun part n => (n <<< 60) + part) 0

def wordFromChunks (parts : List ℕ) : W := BitVec.ofNat 128 (fromChunks parts)

def fullInputs : List W := [
  wordFromChunks [0xc5fffc439770000, 0xafffc439777fff1, 0xef],
  wordFromChunks [0x3a3837fcc002aed, 0x53837fcfffaaed1, 0xfc],
  wordFromChunks [0xd7155be03a9cc56, 0x7155bfffa9cc56a, 0xb1],
  wordFromChunks [0xa5a6601efcdf098, 0x5a663fefcdf0983, 0x3a],
  wordFromChunks [0x3ac0029720e7f1f, 0xac7fe9720e7f1fc, 0xc3],
  wordFromChunks [0xfc0783183f07fe0, 0xcff83183f07fe00, 0xf]]

theorem tableOnRows : ∀ j : Fin 128, Nat.testBit (3937061000 * 2 ^ 32 + 3903373312) (∑ i : Fin 6, if (fullInputs.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

-- Partition the finite search into independently checked subtrees.
abbrev State := ℕ × List W

def nextLayer (next : ℕ → List W → Bool) (e : ℕ) (ws : List W) : Bool :=
  (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => dispatch e next a b r)

theorem dispatch_increases {f g : ℕ → List W → Bool}
    (imp : ∀ e ws, f e ws = true → g e ws = true)
    (e : ℕ) (a b : W) (r : List W) (h : dispatch e f a b r = true) :
    dispatch e g a b r = true := by
  obtain ⟨z, hz, h⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨z, hz, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with h | ⟨hx, h⟩
  · left
    rcases h with h | ⟨hx, h⟩
    · left
      exact ⟨h.1, imp _ _ h.2⟩
    · right
      refine ⟨hx, ?_⟩
      rcases h with h | h
      · exact Or.inl ⟨h.1, imp _ _ h.2⟩
      · exact Or.inr ⟨h.1, imp _ _ h.2⟩
  · exact Or.inr ⟨hx, imp _ _ h⟩

theorem layer_increases {f g : ℕ → List W → Bool}
    (imp : ∀ e ws, f e ws = true → g e ws = true)
    {e : ℕ} {ws : List W} (h : nextLayer f e ws = true) : nextLayer g e ws = true := by
  unfold nextLayer at *
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with hit | moves
  · exact Or.inl hit
  · right
    obtain ⟨⟨a,b,r⟩, hm, ok⟩ := List.any_eq_true.mp moves
    exact List.any_eq_true.mpr ⟨(a,b,r), hm, dispatch_increases imp e a b r ok⟩

def outsideList (states : List State) (e : ℕ) (ws : List W) : Bool :=
  !states.contains (e,ws)

theorem rejectLayer {k : ℕ} {s : State} {states : List State}
    (covered : nextLayer (outsideList states) s.1 s.2 = false)
    (sub : ∀ p ∈ states, optimized k p.1 p.2 = false) :
    optimized (k+1) s.1 s.2 = false := by
  cases h : optimized (k+1) s.1 s.2 with
  | false => rfl
  | true =>
    change nextLayer (optimized k) s.1 s.2 = true at h
    have lift (e : ℕ) (ws : List W) (hit : optimized k e ws = true) : outsideList states e ws = true := by
      have hn : (e,ws) ∉ states := by
        intro hm
        exact Bool.noConfusion ((sub (e,ws) hm).symm.trans hit)
      simpa [outsideList] using hn
    exact Bool.noConfusion (covered.symm.trans (layer_increases lift h))

theorem rejectFull (k : ℕ) (xs : List W)
    (cover : xs.sublists.all (fun ws => !(cuts ws == -1) || ws == xs) = true)
    (bad : optimized k (k+1-xs.length) xs = false) : search k xs = false := by
  cases h : search k xs with
  | false => rfl
  | true =>
    obtain ⟨ws, hm, ok⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at ok
    have eqs := List.all_eq_true.mp cover ws hm
    have he : ws = xs := by simpa [ok.1.2] using eqs
    subst ws
    exact Bool.noConfusion (bad.symm.trans ok.2)

-- Pull exactly the operands and carry the wires of the chosen branch in their original order.
def branch (s : State) (i j op keep : ℕ) : State :=
  let a := s.2.getD i 0
  let b := s.2.getD j 0
  let r := (s.2.take i) ++ ((s.2.drop (i+1)).take (j-i-1)) ++ (s.2.drop (j+1))
  let z := (ops a b).getD op 0
  match keep with
  | 0 => (s.1, z :: r)
  | 1 => (s.1-1, z :: a :: r)
  | 2 => (s.1-1, z :: b :: r)
  | _ => (s.1-2, z :: a :: b :: r)

def state0 : State := (2, fullInputs)

def state1 : State := branch state0 0 1 0 3

def state2 : State := branch state0 0 1 1 3

def state3 : State := branch state0 0 1 2 3

def state4 : State := branch state0 0 1 3 3

def state5 : State := branch state0 0 2 0 3

def state6 : State := branch state0 0 2 1 3

def state7 : State := branch state0 0 2 2 3

def state8 : State := branch state0 0 2 3 3

def state9 : State := branch state0 0 3 0 3

def state10 : State := branch state0 0 3 1 3

def state11 : State := branch state0 0 3 2 3

def state12 : State := branch state0 0 3 3 3

def state13 : State := branch state0 0 4 0 1

def state14 : State := branch state0 0 4 0 3

def state15 : State := branch state0 0 4 1 3

def state16 : State := branch state0 0 4 2 1

def state17 : State := branch state0 0 4 2 3

def state18 : State := branch state0 0 4 3 3

def state19 : State := branch state0 0 5 0 1

def state20 : State := branch state0 0 5 0 3

def state21 : State := branch state0 0 5 1 3

def state22 : State := branch state0 0 5 2 1

def state23 : State := branch state0 0 5 2 3

def state24 : State := branch state0 0 5 3 3

def state25 : State := branch state0 1 2 0 3

def state26 : State := branch state0 1 2 1 3

def state27 : State := branch state0 1 2 2 3

def state28 : State := branch state0 1 2 3 3

def state29 : State := branch state0 1 3 0 1

def state30 : State := branch state0 1 3 0 3

def state31 : State := branch state0 1 3 1 3

def state32 : State := branch state0 1 3 2 1

def state33 : State := branch state0 1 3 2 3

def state34 : State := branch state0 1 3 3 3

def state35 : State := branch state0 1 4 0 3

def state36 : State := branch state0 1 4 1 3

def state37 : State := branch state0 1 4 2 3

def state38 : State := branch state0 1 4 3 3

def state39 : State := branch state0 1 5 0 3

def state40 : State := branch state0 1 5 1 3

def state41 : State := branch state0 1 5 2 3

def state42 : State := branch state0 1 5 3 3

def state43 : State := branch state0 2 3 0 1

def state44 : State := branch state0 2 3 0 3

def state45 : State := branch state0 2 3 1 3

def state46 : State := branch state0 2 3 2 1

def state47 : State := branch state0 2 3 2 3

def state48 : State := branch state0 2 3 3 3

def state49 : State := branch state0 2 4 0 3

def state50 : State := branch state0 2 4 1 3

def state51 : State := branch state0 2 4 2 3

def state52 : State := branch state0 2 4 3 3

def state53 : State := branch state0 2 5 0 3

def state54 : State := branch state0 2 5 1 3

def state55 : State := branch state0 2 5 2 3

def state56 : State := branch state0 2 5 3 3

def state57 : State := branch state0 3 4 0 3

def state58 : State := branch state0 3 4 1 3

def state59 : State := branch state0 3 4 2 3

def state60 : State := branch state0 3 4 3 3

def state61 : State := branch state0 3 5 0 3

def state62 : State := branch state0 3 5 1 3

def state63 : State := branch state0 3 5 2 3

def state64 : State := branch state0 3 5 3 3

def state65 : State := branch state0 4 5 0 3

def state66 : State := branch state0 4 5 1 3

def state67 : State := branch state0 4 5 2 3

def state68 : State := branch state0 4 5 3 3

theorem eliminate1 : optimized 6 state1.1 state1.2 = false := by decide +kernel

theorem eliminate2 : optimized 6 state2.1 state2.2 = false := by decide +kernel

theorem eliminate3 : optimized 6 state3.1 state3.2 = false := by decide +kernel

theorem eliminate4 : optimized 6 state4.1 state4.2 = false := by decide +kernel

theorem eliminate5 : optimized 6 state5.1 state5.2 = false := by decide +kernel

theorem eliminate6 : optimized 6 state6.1 state6.2 = false := by decide +kernel

theorem eliminate7 : optimized 6 state7.1 state7.2 = false := by decide +kernel

theorem eliminate8 : optimized 6 state8.1 state8.2 = false := by decide +kernel

theorem eliminate9 : optimized 6 state9.1 state9.2 = false := by decide +kernel

theorem eliminate10 : optimized 6 state10.1 state10.2 = false := by decide +kernel

theorem eliminate11 : optimized 6 state11.1 state11.2 = false := by decide +kernel

theorem eliminate12 : optimized 6 state12.1 state12.2 = false := by decide +kernel

theorem eliminate13 : optimized 6 state13.1 state13.2 = false := by decide +kernel

theorem eliminate14 : optimized 6 state14.1 state14.2 = false := by decide +kernel

theorem eliminate15 : optimized 6 state15.1 state15.2 = false := by decide +kernel

theorem eliminate16 : optimized 6 state16.1 state16.2 = false := by decide +kernel

theorem eliminate17 : optimized 6 state17.1 state17.2 = false := by decide +kernel

theorem eliminate18 : optimized 6 state18.1 state18.2 = false := by decide +kernel

theorem eliminate19 : optimized 6 state19.1 state19.2 = false := by decide +kernel

theorem eliminate20 : optimized 6 state20.1 state20.2 = false := by decide +kernel

theorem eliminate21 : optimized 6 state21.1 state21.2 = false := by decide +kernel

theorem eliminate22 : optimized 6 state22.1 state22.2 = false := by decide +kernel

theorem eliminate23 : optimized 6 state23.1 state23.2 = false := by decide +kernel

theorem eliminate24 : optimized 6 state24.1 state24.2 = false := by decide +kernel

theorem eliminate25 : optimized 6 state25.1 state25.2 = false := by decide +kernel

theorem eliminate26 : optimized 6 state26.1 state26.2 = false := by decide +kernel

theorem eliminate27 : optimized 6 state27.1 state27.2 = false := by decide +kernel

theorem eliminate28 : optimized 6 state28.1 state28.2 = false := by decide +kernel

theorem eliminate29 : optimized 6 state29.1 state29.2 = false := by decide +kernel

theorem eliminate30 : optimized 6 state30.1 state30.2 = false := by decide +kernel

theorem eliminate31 : optimized 6 state31.1 state31.2 = false := by decide +kernel

theorem eliminate32 : optimized 6 state32.1 state32.2 = false := by decide +kernel

theorem eliminate33 : optimized 6 state33.1 state33.2 = false := by decide +kernel

theorem eliminate34 : optimized 6 state34.1 state34.2 = false := by decide +kernel

theorem eliminate35 : optimized 6 state35.1 state35.2 = false := by decide +kernel

theorem eliminate36 : optimized 6 state36.1 state36.2 = false := by decide +kernel

theorem eliminate37 : optimized 6 state37.1 state37.2 = false := by decide +kernel

theorem eliminate38 : optimized 6 state38.1 state38.2 = false := by decide +kernel

theorem eliminate39 : optimized 6 state39.1 state39.2 = false := by decide +kernel

theorem eliminate40 : optimized 6 state40.1 state40.2 = false := by decide +kernel

theorem eliminate41 : optimized 6 state41.1 state41.2 = false := by decide +kernel

theorem eliminate42 : optimized 6 state42.1 state42.2 = false := by decide +kernel

theorem eliminate43 : optimized 6 state43.1 state43.2 = false := by decide +kernel

theorem eliminate44 : optimized 6 state44.1 state44.2 = false := by decide +kernel

theorem eliminate45 : optimized 6 state45.1 state45.2 = false := by decide +kernel

theorem eliminate46 : optimized 6 state46.1 state46.2 = false := by decide +kernel

theorem eliminate47 : optimized 6 state47.1 state47.2 = false := by decide +kernel

theorem eliminate48 : optimized 6 state48.1 state48.2 = false := by decide +kernel

theorem eliminate49 : optimized 6 state49.1 state49.2 = false := by decide +kernel

theorem eliminate50 : optimized 6 state50.1 state50.2 = false := by decide +kernel

theorem eliminate51 : optimized 6 state51.1 state51.2 = false := by decide +kernel

theorem eliminate52 : optimized 6 state52.1 state52.2 = false := by decide +kernel

theorem eliminate53 : optimized 6 state53.1 state53.2 = false := by decide +kernel

theorem eliminate54 : optimized 6 state54.1 state54.2 = false := by decide +kernel

theorem eliminate55 : optimized 6 state55.1 state55.2 = false := by decide +kernel

theorem eliminate56 : optimized 6 state56.1 state56.2 = false := by decide +kernel

theorem eliminate57 : optimized 6 state57.1 state57.2 = false := by decide +kernel

theorem eliminate58 : optimized 6 state58.1 state58.2 = false := by decide +kernel

theorem eliminate59 : optimized 6 state59.1 state59.2 = false := by decide +kernel

theorem eliminate60 : optimized 6 state60.1 state60.2 = false := by decide +kernel

theorem eliminate61 : optimized 6 state61.1 state61.2 = false := by decide +kernel

theorem eliminate62 : optimized 6 state62.1 state62.2 = false := by decide +kernel

theorem eliminate63 : optimized 6 state63.1 state63.2 = false := by decide +kernel

theorem eliminate64 : optimized 6 state64.1 state64.2 = false := by decide +kernel

theorem eliminate65 : optimized 6 state65.1 state65.2 = false := by decide +kernel

theorem eliminate66 : optimized 6 state66.1 state66.2 = false := by decide +kernel

theorem eliminate67 : optimized 6 state67.1 state67.2 = false := by decide +kernel

theorem eliminate68 : optimized 6 state68.1 state68.2 = false := by decide +kernel

theorem eliminate0 : optimized 7 state0.1 state0.2 = false := by
  apply rejectLayer (states := [state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, state12, state13, state14, state15, state16, state17, state18, state19, state20, state21, state22, state23, state24, state25, state26, state27, state28, state29, state30, state31, state32, state33, state34, state35, state36, state37, state38, state39, state40, state41, state42, state43, state44, state45, state46, state47, state48, state49, state50, state51, state52, state53, state54, state55, state56, state57, state58, state59, state60, state61, state62, state63, state64, state65, state66, state67, state68])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate1
    · exact eliminate2
    · exact eliminate3
    · exact eliminate4
    · exact eliminate5
    · exact eliminate6
    · exact eliminate7
    · exact eliminate8
    · exact eliminate9
    · exact eliminate10
    · exact eliminate11
    · exact eliminate12
    · exact eliminate13
    · exact eliminate14
    · exact eliminate15
    · exact eliminate16
    · exact eliminate17
    · exact eliminate18
    · exact eliminate19
    · exact eliminate20
    · exact eliminate21
    · exact eliminate22
    · exact eliminate23
    · exact eliminate24
    · exact eliminate25
    · exact eliminate26
    · exact eliminate27
    · exact eliminate28
    · exact eliminate29
    · exact eliminate30
    · exact eliminate31
    · exact eliminate32
    · exact eliminate33
    · exact eliminate34
    · exact eliminate35
    · exact eliminate36
    · exact eliminate37
    · exact eliminate38
    · exact eliminate39
    · exact eliminate40
    · exact eliminate41
    · exact eliminate42
    · exact eliminate43
    · exact eliminate44
    · exact eliminate45
    · exact eliminate46
    · exact eliminate47
    · exact eliminate48
    · exact eliminate49
    · exact eliminate50
    · exact eliminate51
    · exact eliminate52
    · exact eliminate53
    · exact eliminate54
    · exact eliminate55
    · exact eliminate56
    · exact eliminate57
    · exact eliminate58
    · exact eliminate59
    · exact eliminate60
    · exact eliminate61
    · exact eliminate62
    · exact eliminate63
    · exact eliminate64
    · exact eliminate65
    · exact eliminate66
    · exact eliminate67
    · exact eliminate68

theorem rejectSmall : search 7 fullInputs = false := by
  apply rejectFull
  · decide +kernel
  · exact eliminate0

theorem binaryLowerBound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = table x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ fullInputs, holds fullInputs.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (fullInputs.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 6 => bit k (fullInputs.getD i.val 0)) =
        fullInputs.map (bit k) := by
      apply List.ext_getElem (by simp [fullInputs])
      intro i hi hj
      have hlt : i < fullInputs.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (fullInputs.map (bit k)) = bit k goal
    rw [← same, he]
    exact tableOnRows k
  obtain ⟨t,ht,run⟩ := compile gs o hg fullInputs fullInputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a fullInputs.toFinset) :
      build basicOps t b fullInputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (rejectSmall.symm.trans (search_complete ht 7 fullInputs (by decide +kernel) (lift low run)))


def witness : Circuit := ⟨[
  ⟨.or, [1,4]⟩,
  ⟨.and, [2,3]⟩,
  ⟨.and, [1,7]⟩,
  ⟨.or, [1,2]⟩,
  ⟨.and, [4,9]⟩,
  ⟨.or, [5,10]⟩,
  ⟨.and, [0,11]⟩,
  ⟨.or, [8,12]⟩,
  ⟨.and, [6,13]⟩], 14⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = table x := by decide +kernel

theorem monotone_replacement (s : ℕ) (C : Circuit) (hC : FanInTwo C) (hs : C.size ≤ s)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = table x := by
  by_cases present : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, hn⟩ := present
    have cut : binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hm, by simp [isBinary, hn]⟩
    have lower := binaryLowerBound C.gates C.output hC he
    exact ⟨witness, witness_mono, by change 9 ≤ s; omega, witness_eval⟩
  · exact ⟨C, fun g hg => ⟨(hC g hg).1.imp_right (·.resolve_right fun h => present ⟨g, hg, h⟩),
      (hC g hg).2⟩, hs, he⟩

end PEqualNP.Outside.L_meta_15327

theorem PEqualNP.Outside.L_meta_15327 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937061000 * 2 ^ 32 + 3903373312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937061000 * 2 ^ 32 + 3903373312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hC, hs, he⟩
  exact PEqualNP.Outside.L_meta_15327.monotone_replacement s C hC hs he
