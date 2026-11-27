import Mathlib
import PEqualNP.Defs

-- An eleven-gate monotone circuit factors the edge function using the common
-- neighbors of vertices 0 and 4. Even with complement wires free, nine binary
-- gates cannot match its values on the stated pairs of Boolean assignments.
-- The live-wire compiler and search follow the proof of L-meta-8724.
namespace PEqualNP.Outside.L_meta_14940

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

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
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
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
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
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
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

-- Running a circuit on the 512 rows at once, NOT gates cost nothing.
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
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
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

def graphEdges : List ℕ := [0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7]

def table (x : Fin 8 → Bool) : Bool := decide (∃ i < graphEdges.length / 2,
    (List.ofFn x).getD (graphEdges.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (graphEdges.getD (2*i+1) 0) false = true)

def fromChunks (parts : List ℕ) : ℕ := parts.foldr (fun part n => (n <<< 60) + part) 0

def wordFromChunks (parts : List ℕ) : W := BitVec.ofNat 512 (fromChunks parts)

def fullInputs : List W := [
  wordFromChunks [0x40032443202c500, 0x1042c0200080c2, 0x158171322742129, 0x862944308040441, 0xa4c3612cf818026, 0x2c0a0288bda402b, 0x717623c296d8104, 0x453580716f3f5c9, 0x232a6a9],
  wordFromChunks [0x75235a8821a9030, 0x50129621c46098, 0x488c7c040259321, 0xc20d150930246d, 0x5aa8abab030d427, 0x39e39c4609d7523, 0x7c244a593210709, 0x9150578252f620b, 0xd1259854],
  wordFromChunks [0x99ddd4d3bcce0b, 0xa881ae83d344c51, 0xd182b90b4616310, 0xaaaa83066b00d24, 0xdd4d3bcde0be19a, 0xae93d344c51099d, 0xd9022636310a881, 0x39364a10d24d5c2, 0xe1d2f9ae],
  wordFromChunks [0x2816ebc40ec2a80, 0xcf717ca4494e052, 0xd0ee2e2ab7825f7, 0x3e43b537e9194d5, 0xebc40ec2ac00562, 0x7ca4494e052b816, 0x2238b7825f7cf71, 0xb57deb5b4d4c3f6, 0x4d723e41],
  wordFromChunks [0x252052900540212, 0x301143005860a10, 0x80e04c90800050, 0x88000443113004, 0x529505482124458, 0xc3005871a3265f0, 0x86e9180a1d879d3, 0x464f917504182e, 0x66da09c2],
  wordFromChunks [0x81c80249212880, 0x2c2808da210400, 0x24082000000c84, 0x30402a080800980, 0x862c92528840280, 0xc1efb2744c00a1e, 0x7340b301c8422c6, 0x3a883484ddc4e70, 0x43a95249],
  wordFromChunks [0xa880104ca108c9, 0xca0890148011525, 0x804082005080882, 0x31460a8948a8002, 0x4106ce948fb2980, 0x9c1484195252b89, 0x848b58d08b2de08, 0x4a0958e2aae80c2, 0x35a5bdde],
  wordFromChunks [0x924000004001044, 0x800500481008, 0x201000000028000, 0x410000800000200, 0x3950703154c0801, 0x22546d834089e44, 0x1994842c6030039, 0xafdf0329a01a115, 0xb8c14921]]

theorem tableOnRows : ∀ j : Fin 512, table (fun i => (fullInputs.getD i.val 0)[j.val]) = goal[j.val] := by decide +kernel

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

def state2 : State := branch state0 0 1 1 1

def state3 : State := branch state0 0 1 1 3

def state4 : State := branch state0 0 1 2 3

def state5 : State := branch state0 0 1 3 1

def state6 : State := branch state0 0 1 3 3

def state7 : State := branch state0 0 2 0 3

def state8 : State := branch state0 0 2 1 1

def state9 : State := branch state0 0 2 1 3

def state10 : State := branch state0 0 2 2 3

def state11 : State := branch state0 0 2 3 1

def state12 : State := branch state0 0 2 3 3

def state13 : State := branch state0 0 3 0 3

def state14 : State := branch state0 0 3 1 1

def state15 : State := branch state0 0 3 1 3

def state16 : State := branch state0 0 3 2 3

def state17 : State := branch state0 0 3 3 1

def state18 : State := branch state0 0 3 3 3

def state19 : State := branch state0 0 4 0 3

def state20 : State := branch state0 0 4 1 3

def state21 : State := branch state0 0 4 2 3

def state22 : State := branch state0 0 4 3 3

def state23 : State := branch state0 0 5 0 3

def state24 : State := branch state0 0 5 1 3

def state25 : State := branch state0 0 5 2 3

def state26 : State := branch state0 0 5 3 3

def state27 : State := branch state0 0 6 0 3

def state28 : State := branch state0 0 6 1 3

def state29 : State := branch state0 0 6 2 3

def state30 : State := branch state0 0 6 3 3

def state31 : State := branch state0 0 7 0 3

def state32 : State := branch state0 0 7 1 3

def state33 : State := branch state0 0 7 2 3

def state34 : State := branch state0 0 7 3 3

def state35 : State := branch state0 1 2 0 3

def state36 : State := branch state0 1 2 1 3

def state37 : State := branch state0 1 2 2 3

def state38 : State := branch state0 1 2 3 3

def state39 : State := branch state0 1 3 0 3

def state40 : State := branch state0 1 3 1 3

def state41 : State := branch state0 1 3 2 3

def state42 : State := branch state0 1 3 3 3

def state43 : State := branch state0 1 4 0 3

def state44 : State := branch state0 1 4 1 2

def state45 : State := branch state0 1 4 1 3

def state46 : State := branch state0 1 4 2 2

def state47 : State := branch state0 1 4 2 3

def state48 : State := branch state0 1 4 3 3

def state49 : State := branch state0 1 5 0 3

def state50 : State := branch state0 1 5 1 3

def state51 : State := branch state0 1 5 2 3

def state52 : State := branch state0 1 5 3 3

def state53 : State := branch state0 1 6 0 3

def state54 : State := branch state0 1 6 1 3

def state55 : State := branch state0 1 6 2 3

def state56 : State := branch state0 1 6 3 3

def state57 : State := branch state0 1 7 0 3

def state58 : State := branch state0 1 7 1 3

def state59 : State := branch state0 1 7 2 3

def state60 : State := branch state0 1 7 3 3

def state61 : State := branch state0 2 3 0 3

def state62 : State := branch state0 2 3 1 0

def state63 : State := branch state62 0 1 0 3

def state64 : State := branch state62 0 1 1 2

def state65 : State := branch state62 0 1 1 3

def state66 : State := branch state62 0 1 2 2

def state67 : State := branch state62 0 1 2 3

def state68 : State := branch state62 0 1 3 3

def state69 : State := branch state62 0 2 0 3

def state70 : State := branch state62 0 2 1 3

def state71 : State := branch state62 0 2 2 3

def state72 : State := branch state62 0 2 3 3

def state73 : State := branch state62 0 3 0 3

def state74 : State := branch state62 0 3 1 2

def state75 : State := branch state62 0 3 1 3

def state76 : State := branch state62 0 3 2 2

def state77 : State := branch state62 0 3 2 3

def state78 : State := branch state62 0 3 3 3

def state79 : State := branch state62 0 4 0 3

def state80 : State := branch state62 0 4 1 2

def state81 : State := branch state62 0 4 1 3

def state82 : State := branch state62 0 4 2 2

def state83 : State := branch state62 0 4 2 3

def state84 : State := branch state62 0 4 3 3

def state85 : State := branch state62 0 5 0 3

def state86 : State := branch state62 0 5 1 3

def state87 : State := branch state62 0 5 2 3

def state88 : State := branch state62 0 5 3 3

def state89 : State := branch state62 0 6 0 2

def state90 : State := branch state62 0 6 0 3

def state91 : State := branch state62 0 6 1 3

def state92 : State := branch state62 0 6 2 3

def state93 : State := branch state62 0 6 3 2

def state94 : State := branch state62 0 6 3 3

def state95 : State := branch state62 1 2 0 3

def state96 : State := branch state62 1 2 1 1

def state97 : State := branch state62 1 2 1 3

def state98 : State := branch state62 1 2 2 3

def state99 : State := branch state62 1 2 3 1

def state100 : State := branch state62 1 2 3 3

def state101 : State := branch state62 1 3 0 3

def state102 : State := branch state62 1 3 1 3

def state103 : State := branch state62 1 3 2 3

def state104 : State := branch state62 1 3 3 3

def state105 : State := branch state62 1 4 0 3

def state106 : State := branch state62 1 4 1 3

def state107 : State := branch state62 1 4 2 3

def state108 : State := branch state62 1 4 3 3

def state109 : State := branch state62 1 5 0 3

def state110 : State := branch state62 1 5 1 3

def state111 : State := branch state62 1 5 2 3

def state112 : State := branch state62 1 5 3 3

def state113 : State := branch state62 1 6 0 3

def state114 : State := branch state62 1 6 1 3

def state115 : State := branch state62 1 6 2 3

def state116 : State := branch state62 1 6 3 3

def state117 : State := branch state62 2 3 0 3

def state118 : State := branch state62 2 3 1 2

def state119 : State := branch state62 2 3 1 3

def state120 : State := branch state62 2 3 2 2

def state121 : State := branch state62 2 3 2 3

def state122 : State := branch state62 2 3 3 3

def state123 : State := branch state62 2 4 0 3

def state124 : State := branch state62 2 4 1 3

def state125 : State := branch state62 2 4 2 3

def state126 : State := branch state62 2 4 3 3

def state127 : State := branch state62 2 5 0 3

def state128 : State := branch state62 2 5 1 3

def state129 : State := branch state62 2 5 2 3

def state130 : State := branch state62 2 5 3 3

def state131 : State := branch state62 2 6 0 3

def state132 : State := branch state62 2 6 1 3

def state133 : State := branch state62 2 6 2 3

def state134 : State := branch state62 2 6 3 3

def state135 : State := branch state62 3 4 0 3

def state136 : State := branch state62 3 4 1 3

def state137 : State := branch state62 3 4 2 3

def state138 : State := branch state62 3 4 3 3

def state139 : State := branch state62 3 5 0 3

def state140 : State := branch state62 3 5 1 3

def state141 : State := branch state62 3 5 2 3

def state142 : State := branch state62 3 5 3 3

def state143 : State := branch state62 3 6 0 3

def state144 : State := branch state62 3 6 1 3

def state145 : State := branch state62 3 6 2 3

def state146 : State := branch state62 3 6 3 3

def state147 : State := branch state62 4 5 0 3

def state148 : State := branch state62 4 5 1 1

def state149 : State := branch state62 4 5 1 3

def state150 : State := branch state62 4 5 2 3

def state151 : State := branch state62 4 5 3 1

def state152 : State := branch state62 4 5 3 3

def state153 : State := branch state62 4 6 0 3

def state154 : State := branch state62 4 6 1 3

def state155 : State := branch state62 4 6 2 3

def state156 : State := branch state62 4 6 3 3

def state157 : State := branch state62 5 6 0 3

def state158 : State := branch state62 5 6 1 3

def state159 : State := branch state62 5 6 2 3

def state160 : State := branch state62 5 6 3 3

def state161 : State := branch state0 2 3 1 1

def state162 : State := branch state161 0 1 0 1

def state163 : State := branch state161 0 1 1 0

def state164 : State := branch state161 0 1 1 1

def state165 : State := branch state161 0 1 1 2

def state166 : State := branch state161 0 1 2 1

def state167 : State := branch state161 0 1 2 2

def state168 : State := branch state161 0 1 3 1

def state169 : State := branch state161 0 2 1 2

def state170 : State := branch state161 0 2 2 2

def state171 : State := branch state161 0 4 1 2

def state172 : State := branch state161 0 4 2 2

def state173 : State := branch state161 0 5 1 2

def state174 : State := branch state161 0 5 2 2

def state175 : State := branch state161 0 7 0 2

def state176 : State := branch state161 0 7 3 2

def state177 : State := branch state161 1 2 0 2

def state178 : State := branch state161 1 2 1 2

def state179 : State := branch state161 1 2 2 2

def state180 : State := branch state161 1 2 3 2

def state181 : State := branch state161 1 3 0 2

def state182 : State := branch state161 1 3 1 2

def state183 : State := branch state161 1 3 2 2

def state184 : State := branch state161 1 3 3 2

def state185 : State := branch state161 1 4 0 2

def state186 : State := branch state161 1 4 1 2

def state187 : State := branch state161 1 4 2 2

def state188 : State := branch state161 1 4 3 2

def state189 : State := branch state161 1 5 0 2

def state190 : State := branch state161 1 5 1 2

def state191 : State := branch state161 1 5 2 2

def state192 : State := branch state161 1 5 3 2

def state193 : State := branch state161 1 6 0 2

def state194 : State := branch state161 1 6 1 2

def state195 : State := branch state161 1 6 2 2

def state196 : State := branch state161 1 6 3 2

def state197 : State := branch state161 1 7 0 2

def state198 : State := branch state161 1 7 1 2

def state199 : State := branch state161 1 7 2 2

def state200 : State := branch state161 1 7 3 2

def state201 : State := branch state161 2 3 1 1

def state202 : State := branch state161 2 3 3 1

def state203 : State := branch state161 3 4 1 2

def state204 : State := branch state161 3 4 2 2

def state205 : State := branch state161 5 6 1 1

def state206 : State := branch state161 5 6 3 1

def state207 : State := branch state0 2 3 1 2

def state208 : State := branch state207 0 1 0 1

def state209 : State := branch state207 0 1 1 2

def state210 : State := branch state207 0 1 2 1

def state211 : State := branch state207 0 1 2 2

def state212 : State := branch state207 0 2 1 2

def state213 : State := branch state207 0 2 2 2

def state214 : State := branch state207 0 4 1 2

def state215 : State := branch state207 0 4 2 2

def state216 : State := branch state207 0 5 1 2

def state217 : State := branch state207 0 5 2 2

def state218 : State := branch state207 0 7 0 2

def state219 : State := branch state207 0 7 3 2

def state220 : State := branch state207 1 2 0 2

def state221 : State := branch state207 1 2 1 2

def state222 : State := branch state207 1 2 2 2

def state223 : State := branch state207 1 2 3 2

def state224 : State := branch state207 1 3 0 2

def state225 : State := branch state207 1 3 1 2

def state226 : State := branch state207 1 3 2 2

def state227 : State := branch state207 1 3 3 2

def state228 : State := branch state207 1 4 0 2

def state229 : State := branch state207 1 4 1 2

def state230 : State := branch state207 1 4 2 2

def state231 : State := branch state207 1 4 3 2

def state232 : State := branch state207 1 5 0 2

def state233 : State := branch state207 1 5 1 2

def state234 : State := branch state207 1 5 2 2

def state235 : State := branch state207 1 5 3 2

def state236 : State := branch state207 1 6 0 2

def state237 : State := branch state207 1 6 1 2

def state238 : State := branch state207 1 6 2 2

def state239 : State := branch state207 1 6 3 2

def state240 : State := branch state207 1 7 0 2

def state241 : State := branch state207 1 7 1 2

def state242 : State := branch state207 1 7 2 2

def state243 : State := branch state207 1 7 3 2

def state244 : State := branch state207 2 3 1 1

def state245 : State := branch state207 2 3 3 1

def state246 : State := branch state207 3 4 1 2

def state247 : State := branch state207 3 4 2 2

def state248 : State := branch state207 5 6 1 1

def state249 : State := branch state207 5 6 3 1

def state250 : State := branch state0 2 3 1 3

def state251 : State := branch state0 2 3 2 2

def state252 : State := branch state0 2 3 2 3

def state253 : State := branch state0 2 3 3 1

def state254 : State := branch state0 2 3 3 3

def state255 : State := branch state0 2 4 0 3

def state256 : State := branch state0 2 4 1 2

def state257 : State := branch state0 2 4 1 3

def state258 : State := branch state0 2 4 2 2

def state259 : State := branch state0 2 4 2 3

def state260 : State := branch state0 2 4 3 3

def state261 : State := branch state0 2 5 0 3

def state262 : State := branch state0 2 5 1 2

def state263 : State := branch state262 0 1 0 1

def state264 : State := branch state262 0 1 1 2

def state265 : State := branch state262 0 1 2 1

def state266 : State := branch state262 0 1 2 2

def state267 : State := branch state262 0 2 1 2

def state268 : State := branch state262 0 2 2 2

def state269 : State := branch state262 0 4 1 1

def state270 : State := branch state262 0 4 1 2

def state271 : State := branch state262 0 4 2 2

def state272 : State := branch state262 0 4 3 1

def state273 : State := branch state262 0 5 1 2

def state274 : State := branch state262 0 5 2 2

def state275 : State := branch state262 0 7 0 2

def state276 : State := branch state262 0 7 3 2

def state277 : State := branch state262 1 4 1 1

def state278 : State := branch state262 1 4 3 1

def state279 : State := branch state262 1 6 1 0

def state280 : State := branch state262 1 6 1 1

def state281 : State := branch state262 1 6 1 2

def state282 : State := branch state262 1 6 2 2

def state283 : State := branch state262 1 6 3 1

def state284 : State := branch state262 1 7 1 2

def state285 : State := branch state262 1 7 2 2

def state286 : State := branch state262 2 3 1 1

def state287 : State := branch state262 2 3 3 1

def state288 : State := branch state262 2 4 1 1

def state289 : State := branch state262 2 4 3 1

def state290 : State := branch state262 3 5 1 2

def state291 : State := branch state262 3 5 2 2

def state292 : State := branch state262 4 5 1 2

def state293 : State := branch state262 4 5 2 2

def state294 : State := branch state262 4 7 0 2

def state295 : State := branch state262 4 7 3 2

def state296 : State := branch state0 2 5 1 3

def state297 : State := branch state0 2 5 2 2

def state298 : State := branch state0 2 5 2 3

def state299 : State := branch state0 2 5 3 3

def state300 : State := branch state0 2 6 0 3

def state301 : State := branch state0 2 6 1 3

def state302 : State := branch state0 2 6 2 3

def state303 : State := branch state0 2 6 3 3

def state304 : State := branch state0 2 7 0 2

def state305 : State := branch state304 0 1 0 2

def state306 : State := branch state304 0 1 1 1

def state307 : State := branch state304 0 1 3 1

def state308 : State := branch state304 0 1 3 2

def state309 : State := branch state304 0 2 1 0

def state310 : State := branch state304 0 2 1 1

def state311 : State := branch state304 0 2 1 2

def state312 : State := branch state304 0 2 2 2

def state313 : State := branch state304 0 2 3 1

def state314 : State := branch state304 0 3 1 1

def state315 : State := branch state304 0 3 3 1

def state316 : State := branch state304 0 4 1 0

def state317 : State := branch state304 0 4 1 1

def state318 : State := branch state304 0 4 1 2

def state319 : State := branch state304 0 4 2 2

def state320 : State := branch state304 0 4 3 1

def state321 : State := branch state304 0 5 1 0

def state322 : State := branch state304 0 5 1 1

def state323 : State := branch state304 0 5 1 2

def state324 : State := branch state304 0 5 2 2

def state325 : State := branch state304 0 5 3 1

def state326 : State := branch state304 0 6 1 0

def state327 : State := branch state304 0 6 1 1

def state328 : State := branch state304 0 6 1 2

def state329 : State := branch state304 0 6 2 2

def state330 : State := branch state304 0 6 3 1

def state331 : State := branch state304 0 7 1 1

def state332 : State := branch state304 0 7 3 1

def state333 : State := branch state304 1 4 0 1

def state334 : State := branch state304 1 4 2 1

def state335 : State := branch state304 2 3 1 1

def state336 : State := branch state304 2 3 3 1

def state337 : State := branch state304 2 4 1 1

def state338 : State := branch state304 2 4 3 1

def state339 : State := branch state304 3 5 1 2

def state340 : State := branch state304 3 5 2 2

def state341 : State := branch state304 4 5 1 2

def state342 : State := branch state304 4 5 2 2

def state343 : State := branch state304 4 6 1 2

def state344 : State := branch state304 4 6 2 2

def state345 : State := branch state304 6 7 1 1

def state346 : State := branch state304 6 7 3 1

def state347 : State := branch state0 2 7 0 3

def state348 : State := branch state0 2 7 1 3

def state349 : State := branch state0 2 7 2 3

def state350 : State := branch state0 2 7 3 2

def state351 : State := branch state0 2 7 3 3

def state352 : State := branch state0 3 4 0 3

def state353 : State := branch state0 3 4 1 2

def state354 : State := branch state0 3 4 1 3

def state355 : State := branch state0 3 4 2 2

def state356 : State := branch state0 3 4 2 3

def state357 : State := branch state0 3 4 3 3

def state358 : State := branch state0 3 5 0 3

def state359 : State := branch state0 3 5 1 2

def state360 : State := branch state359 0 1 0 1

def state361 : State := branch state359 0 1 1 2

def state362 : State := branch state359 0 1 2 1

def state363 : State := branch state359 0 1 2 2

def state364 : State := branch state359 0 2 1 2

def state365 : State := branch state359 0 2 2 2

def state366 : State := branch state359 0 4 1 1

def state367 : State := branch state359 0 4 1 2

def state368 : State := branch state359 0 4 2 2

def state369 : State := branch state359 0 4 3 1

def state370 : State := branch state359 0 5 1 2

def state371 : State := branch state359 0 5 2 2

def state372 : State := branch state359 0 7 0 2

def state373 : State := branch state359 0 7 3 2

def state374 : State := branch state359 1 4 1 1

def state375 : State := branch state359 1 4 3 1

def state376 : State := branch state359 1 6 1 0

def state377 : State := branch state359 1 6 1 1

def state378 : State := branch state359 1 6 1 2

def state379 : State := branch state359 1 6 2 2

def state380 : State := branch state359 1 6 3 1

def state381 : State := branch state359 1 7 1 2

def state382 : State := branch state359 1 7 2 2

def state383 : State := branch state359 2 3 1 1

def state384 : State := branch state359 2 3 3 1

def state385 : State := branch state359 2 4 1 1

def state386 : State := branch state359 2 4 3 1

def state387 : State := branch state359 3 5 1 2

def state388 : State := branch state359 3 5 2 2

def state389 : State := branch state359 4 5 1 2

def state390 : State := branch state359 4 5 2 2

def state391 : State := branch state359 4 7 0 2

def state392 : State := branch state359 4 7 3 2

def state393 : State := branch state0 3 5 1 3

def state394 : State := branch state0 3 5 2 2

def state395 : State := branch state0 3 5 2 3

def state396 : State := branch state0 3 5 3 3

def state397 : State := branch state0 3 6 0 3

def state398 : State := branch state0 3 6 1 3

def state399 : State := branch state0 3 6 2 3

def state400 : State := branch state0 3 6 3 3

def state401 : State := branch state0 3 7 0 2

def state402 : State := branch state401 0 1 0 2

def state403 : State := branch state401 0 1 1 1

def state404 : State := branch state401 0 1 3 1

def state405 : State := branch state401 0 1 3 2

def state406 : State := branch state401 0 2 1 0

def state407 : State := branch state401 0 2 1 1

def state408 : State := branch state401 0 2 1 2

def state409 : State := branch state401 0 2 2 2

def state410 : State := branch state401 0 2 3 1

def state411 : State := branch state401 0 3 1 1

def state412 : State := branch state401 0 3 3 1

def state413 : State := branch state401 0 4 1 0

def state414 : State := branch state401 0 4 1 1

def state415 : State := branch state401 0 4 1 2

def state416 : State := branch state401 0 4 2 2

def state417 : State := branch state401 0 4 3 1

def state418 : State := branch state401 0 5 1 0

def state419 : State := branch state401 0 5 1 1

def state420 : State := branch state401 0 5 1 2

def state421 : State := branch state401 0 5 2 2

def state422 : State := branch state401 0 5 3 1

def state423 : State := branch state401 0 6 1 0

def state424 : State := branch state401 0 6 1 1

def state425 : State := branch state401 0 6 1 2

def state426 : State := branch state401 0 6 2 2

def state427 : State := branch state401 0 6 3 1

def state428 : State := branch state401 0 7 1 1

def state429 : State := branch state401 0 7 3 1

def state430 : State := branch state401 1 4 0 1

def state431 : State := branch state401 1 4 2 1

def state432 : State := branch state401 2 3 1 1

def state433 : State := branch state401 2 3 3 1

def state434 : State := branch state401 2 4 1 1

def state435 : State := branch state401 2 4 3 1

def state436 : State := branch state401 3 5 1 2

def state437 : State := branch state401 3 5 2 2

def state438 : State := branch state401 4 5 1 2

def state439 : State := branch state401 4 5 2 2

def state440 : State := branch state401 4 6 1 2

def state441 : State := branch state401 4 6 2 2

def state442 : State := branch state401 6 7 1 1

def state443 : State := branch state401 6 7 3 1

def state444 : State := branch state0 3 7 0 3

def state445 : State := branch state0 3 7 1 3

def state446 : State := branch state0 3 7 2 3

def state447 : State := branch state0 3 7 3 2

def state448 : State := branch state0 3 7 3 3

def state449 : State := branch state0 4 5 0 3

def state450 : State := branch state0 4 5 1 3

def state451 : State := branch state0 4 5 2 3

def state452 : State := branch state0 4 5 3 3

def state453 : State := branch state0 4 6 0 3

def state454 : State := branch state0 4 6 1 3

def state455 : State := branch state0 4 6 2 3

def state456 : State := branch state0 4 6 3 3

def state457 : State := branch state0 4 7 0 3

def state458 : State := branch state0 4 7 1 3

def state459 : State := branch state0 4 7 2 3

def state460 : State := branch state0 4 7 3 3

def state461 : State := branch state0 5 6 0 3

def state462 : State := branch state0 5 6 1 1

def state463 : State := branch state462 0 1 0 1

def state464 : State := branch state462 0 1 1 2

def state465 : State := branch state462 0 1 2 1

def state466 : State := branch state462 0 1 2 2

def state467 : State := branch state462 0 3 0 1

def state468 : State := branch state462 0 3 2 1

def state469 : State := branch state462 1 2 1 2

def state470 : State := branch state462 1 2 2 2

def state471 : State := branch state462 1 3 1 2

def state472 : State := branch state462 1 3 2 2

def state473 : State := branch state462 1 4 1 0

def state474 : State := branch state462 1 4 1 1

def state475 : State := branch state462 1 4 1 2

def state476 : State := branch state462 1 4 2 2

def state477 : State := branch state462 1 4 3 1

def state478 : State := branch state462 1 5 1 0

def state479 : State := branch state462 1 5 1 1

def state480 : State := branch state462 1 5 1 2

def state481 : State := branch state462 1 5 2 2

def state482 : State := branch state462 1 5 3 1

def state483 : State := branch state462 1 6 1 2

def state484 : State := branch state462 1 6 2 2

def state485 : State := branch state462 1 7 0 2

def state486 : State := branch state462 1 7 3 2

def state487 : State := branch state462 2 3 1 1

def state488 : State := branch state462 2 3 3 1

def state489 : State := branch state462 2 4 1 1

def state490 : State := branch state462 2 4 3 1

def state491 : State := branch state462 2 5 1 1

def state492 : State := branch state462 2 5 3 1

def state493 : State := branch state462 3 6 1 2

def state494 : State := branch state462 3 6 2 2

def state495 : State := branch state462 4 5 1 0

def state496 : State := branch state462 4 5 1 1

def state497 : State := branch state462 4 5 1 2

def state498 : State := branch state462 4 5 2 2

def state499 : State := branch state462 4 5 3 1

def state500 : State := branch state462 4 6 1 2

def state501 : State := branch state462 4 6 2 2

def state502 : State := branch state462 4 7 0 2

def state503 : State := branch state462 4 7 3 2

def state504 : State := branch state462 5 6 1 2

def state505 : State := branch state462 5 6 2 2

def state506 : State := branch state462 5 7 0 2

def state507 : State := branch state462 5 7 3 2

def state508 : State := branch state0 5 6 1 3

def state509 : State := branch state0 5 6 2 3

def state510 : State := branch state0 5 6 3 1

def state511 : State := branch state0 5 6 3 3

def state512 : State := branch state0 5 7 0 3

def state513 : State := branch state0 5 7 1 3

def state514 : State := branch state0 5 7 2 3

def state515 : State := branch state0 5 7 3 3

def state516 : State := branch state0 6 7 0 3

def state517 : State := branch state0 6 7 1 3

def state518 : State := branch state0 6 7 2 3

def state519 : State := branch state0 6 7 3 3

theorem eliminate1 : optimized 8 state1.1 state1.2 = false := by decide +kernel

theorem eliminate2 : optimized 8 state2.1 state2.2 = false := by decide +kernel

theorem eliminate3 : optimized 8 state3.1 state3.2 = false := by decide +kernel

theorem eliminate4 : optimized 8 state4.1 state4.2 = false := by decide +kernel

theorem eliminate5 : optimized 8 state5.1 state5.2 = false := by decide +kernel

theorem eliminate6 : optimized 8 state6.1 state6.2 = false := by decide +kernel

theorem eliminate7 : optimized 8 state7.1 state7.2 = false := by decide +kernel

theorem eliminate8 : optimized 8 state8.1 state8.2 = false := by decide +kernel

theorem eliminate9 : optimized 8 state9.1 state9.2 = false := by decide +kernel

theorem eliminate10 : optimized 8 state10.1 state10.2 = false := by decide +kernel

theorem eliminate11 : optimized 8 state11.1 state11.2 = false := by decide +kernel

theorem eliminate12 : optimized 8 state12.1 state12.2 = false := by decide +kernel

theorem eliminate13 : optimized 8 state13.1 state13.2 = false := by decide +kernel

theorem eliminate14 : optimized 8 state14.1 state14.2 = false := by decide +kernel

theorem eliminate15 : optimized 8 state15.1 state15.2 = false := by decide +kernel

theorem eliminate16 : optimized 8 state16.1 state16.2 = false := by decide +kernel

theorem eliminate17 : optimized 8 state17.1 state17.2 = false := by decide +kernel

theorem eliminate18 : optimized 8 state18.1 state18.2 = false := by decide +kernel

theorem eliminate19 : optimized 8 state19.1 state19.2 = false := by decide +kernel

theorem eliminate20 : optimized 8 state20.1 state20.2 = false := by decide +kernel

theorem eliminate21 : optimized 8 state21.1 state21.2 = false := by decide +kernel

theorem eliminate22 : optimized 8 state22.1 state22.2 = false := by decide +kernel

theorem eliminate23 : optimized 8 state23.1 state23.2 = false := by decide +kernel

theorem eliminate24 : optimized 8 state24.1 state24.2 = false := by decide +kernel

theorem eliminate25 : optimized 8 state25.1 state25.2 = false := by decide +kernel

theorem eliminate26 : optimized 8 state26.1 state26.2 = false := by decide +kernel

theorem eliminate27 : optimized 8 state27.1 state27.2 = false := by decide +kernel

theorem eliminate28 : optimized 8 state28.1 state28.2 = false := by decide +kernel

theorem eliminate29 : optimized 8 state29.1 state29.2 = false := by decide +kernel

theorem eliminate30 : optimized 8 state30.1 state30.2 = false := by decide +kernel

theorem eliminate31 : optimized 8 state31.1 state31.2 = false := by decide +kernel

theorem eliminate32 : optimized 8 state32.1 state32.2 = false := by decide +kernel

theorem eliminate33 : optimized 8 state33.1 state33.2 = false := by decide +kernel

theorem eliminate34 : optimized 8 state34.1 state34.2 = false := by decide +kernel

theorem eliminate35 : optimized 8 state35.1 state35.2 = false := by decide +kernel

theorem eliminate36 : optimized 8 state36.1 state36.2 = false := by decide +kernel

theorem eliminate37 : optimized 8 state37.1 state37.2 = false := by decide +kernel

theorem eliminate38 : optimized 8 state38.1 state38.2 = false := by decide +kernel

theorem eliminate39 : optimized 8 state39.1 state39.2 = false := by decide +kernel

theorem eliminate40 : optimized 8 state40.1 state40.2 = false := by decide +kernel

theorem eliminate41 : optimized 8 state41.1 state41.2 = false := by decide +kernel

theorem eliminate42 : optimized 8 state42.1 state42.2 = false := by decide +kernel

theorem eliminate43 : optimized 8 state43.1 state43.2 = false := by decide +kernel

theorem eliminate44 : optimized 8 state44.1 state44.2 = false := by decide +kernel

theorem eliminate45 : optimized 8 state45.1 state45.2 = false := by decide +kernel

theorem eliminate46 : optimized 8 state46.1 state46.2 = false := by decide +kernel

theorem eliminate47 : optimized 8 state47.1 state47.2 = false := by decide +kernel

theorem eliminate48 : optimized 8 state48.1 state48.2 = false := by decide +kernel

theorem eliminate49 : optimized 8 state49.1 state49.2 = false := by decide +kernel

theorem eliminate50 : optimized 8 state50.1 state50.2 = false := by decide +kernel

theorem eliminate51 : optimized 8 state51.1 state51.2 = false := by decide +kernel

theorem eliminate52 : optimized 8 state52.1 state52.2 = false := by decide +kernel

theorem eliminate53 : optimized 8 state53.1 state53.2 = false := by decide +kernel

theorem eliminate54 : optimized 8 state54.1 state54.2 = false := by decide +kernel

theorem eliminate55 : optimized 8 state55.1 state55.2 = false := by decide +kernel

theorem eliminate56 : optimized 8 state56.1 state56.2 = false := by decide +kernel

theorem eliminate57 : optimized 8 state57.1 state57.2 = false := by decide +kernel

theorem eliminate58 : optimized 8 state58.1 state58.2 = false := by decide +kernel

theorem eliminate59 : optimized 8 state59.1 state59.2 = false := by decide +kernel

theorem eliminate60 : optimized 8 state60.1 state60.2 = false := by decide +kernel

theorem eliminate61 : optimized 8 state61.1 state61.2 = false := by decide +kernel

theorem eliminate63 : optimized 7 state63.1 state63.2 = false := by decide +kernel

theorem eliminate64 : optimized 7 state64.1 state64.2 = false := by decide +kernel

theorem eliminate65 : optimized 7 state65.1 state65.2 = false := by decide +kernel

theorem eliminate66 : optimized 7 state66.1 state66.2 = false := by decide +kernel

theorem eliminate67 : optimized 7 state67.1 state67.2 = false := by decide +kernel

theorem eliminate68 : optimized 7 state68.1 state68.2 = false := by decide +kernel

theorem eliminate69 : optimized 7 state69.1 state69.2 = false := by decide +kernel

theorem eliminate70 : optimized 7 state70.1 state70.2 = false := by decide +kernel

theorem eliminate71 : optimized 7 state71.1 state71.2 = false := by decide +kernel

theorem eliminate72 : optimized 7 state72.1 state72.2 = false := by decide +kernel

theorem eliminate73 : optimized 7 state73.1 state73.2 = false := by decide +kernel

theorem eliminate74 : optimized 7 state74.1 state74.2 = false := by decide +kernel

theorem eliminate75 : optimized 7 state75.1 state75.2 = false := by decide +kernel

theorem eliminate76 : optimized 7 state76.1 state76.2 = false := by decide +kernel

theorem eliminate77 : optimized 7 state77.1 state77.2 = false := by decide +kernel

theorem eliminate78 : optimized 7 state78.1 state78.2 = false := by decide +kernel

theorem eliminate79 : optimized 7 state79.1 state79.2 = false := by decide +kernel

theorem eliminate80 : optimized 7 state80.1 state80.2 = false := by decide +kernel

theorem eliminate81 : optimized 7 state81.1 state81.2 = false := by decide +kernel

theorem eliminate82 : optimized 7 state82.1 state82.2 = false := by decide +kernel

theorem eliminate83 : optimized 7 state83.1 state83.2 = false := by decide +kernel

theorem eliminate84 : optimized 7 state84.1 state84.2 = false := by decide +kernel

theorem eliminate85 : optimized 7 state85.1 state85.2 = false := by decide +kernel

theorem eliminate86 : optimized 7 state86.1 state86.2 = false := by decide +kernel

theorem eliminate87 : optimized 7 state87.1 state87.2 = false := by decide +kernel

theorem eliminate88 : optimized 7 state88.1 state88.2 = false := by decide +kernel

theorem eliminate89 : optimized 7 state89.1 state89.2 = false := by decide +kernel

theorem eliminate90 : optimized 7 state90.1 state90.2 = false := by decide +kernel

theorem eliminate91 : optimized 7 state91.1 state91.2 = false := by decide +kernel

theorem eliminate92 : optimized 7 state92.1 state92.2 = false := by decide +kernel

theorem eliminate93 : optimized 7 state93.1 state93.2 = false := by decide +kernel

theorem eliminate94 : optimized 7 state94.1 state94.2 = false := by decide +kernel

theorem eliminate95 : optimized 7 state95.1 state95.2 = false := by decide +kernel

theorem eliminate96 : optimized 7 state96.1 state96.2 = false := by decide +kernel

theorem eliminate97 : optimized 7 state97.1 state97.2 = false := by decide +kernel

theorem eliminate98 : optimized 7 state98.1 state98.2 = false := by decide +kernel

theorem eliminate99 : optimized 7 state99.1 state99.2 = false := by decide +kernel

theorem eliminate100 : optimized 7 state100.1 state100.2 = false := by decide +kernel

theorem eliminate101 : optimized 7 state101.1 state101.2 = false := by decide +kernel

theorem eliminate102 : optimized 7 state102.1 state102.2 = false := by decide +kernel

theorem eliminate103 : optimized 7 state103.1 state103.2 = false := by decide +kernel

theorem eliminate104 : optimized 7 state104.1 state104.2 = false := by decide +kernel

theorem eliminate105 : optimized 7 state105.1 state105.2 = false := by decide +kernel

theorem eliminate106 : optimized 7 state106.1 state106.2 = false := by decide +kernel

theorem eliminate107 : optimized 7 state107.1 state107.2 = false := by decide +kernel

theorem eliminate108 : optimized 7 state108.1 state108.2 = false := by decide +kernel

theorem eliminate109 : optimized 7 state109.1 state109.2 = false := by decide +kernel

theorem eliminate110 : optimized 7 state110.1 state110.2 = false := by decide +kernel

theorem eliminate111 : optimized 7 state111.1 state111.2 = false := by decide +kernel

theorem eliminate112 : optimized 7 state112.1 state112.2 = false := by decide +kernel

theorem eliminate113 : optimized 7 state113.1 state113.2 = false := by decide +kernel

theorem eliminate114 : optimized 7 state114.1 state114.2 = false := by decide +kernel

theorem eliminate115 : optimized 7 state115.1 state115.2 = false := by decide +kernel

theorem eliminate116 : optimized 7 state116.1 state116.2 = false := by decide +kernel

theorem eliminate117 : optimized 7 state117.1 state117.2 = false := by decide +kernel

theorem eliminate118 : optimized 7 state118.1 state118.2 = false := by decide +kernel

theorem eliminate119 : optimized 7 state119.1 state119.2 = false := by decide +kernel

theorem eliminate120 : optimized 7 state120.1 state120.2 = false := by decide +kernel

theorem eliminate121 : optimized 7 state121.1 state121.2 = false := by decide +kernel

theorem eliminate122 : optimized 7 state122.1 state122.2 = false := by decide +kernel

theorem eliminate123 : optimized 7 state123.1 state123.2 = false := by decide +kernel

theorem eliminate124 : optimized 7 state124.1 state124.2 = false := by decide +kernel

theorem eliminate125 : optimized 7 state125.1 state125.2 = false := by decide +kernel

theorem eliminate126 : optimized 7 state126.1 state126.2 = false := by decide +kernel

theorem eliminate127 : optimized 7 state127.1 state127.2 = false := by decide +kernel

theorem eliminate128 : optimized 7 state128.1 state128.2 = false := by decide +kernel

theorem eliminate129 : optimized 7 state129.1 state129.2 = false := by decide +kernel

theorem eliminate130 : optimized 7 state130.1 state130.2 = false := by decide +kernel

theorem eliminate131 : optimized 7 state131.1 state131.2 = false := by decide +kernel

theorem eliminate132 : optimized 7 state132.1 state132.2 = false := by decide +kernel

theorem eliminate133 : optimized 7 state133.1 state133.2 = false := by decide +kernel

theorem eliminate134 : optimized 7 state134.1 state134.2 = false := by decide +kernel

theorem eliminate135 : optimized 7 state135.1 state135.2 = false := by decide +kernel

theorem eliminate136 : optimized 7 state136.1 state136.2 = false := by decide +kernel

theorem eliminate137 : optimized 7 state137.1 state137.2 = false := by decide +kernel

theorem eliminate138 : optimized 7 state138.1 state138.2 = false := by decide +kernel

theorem eliminate139 : optimized 7 state139.1 state139.2 = false := by decide +kernel

theorem eliminate140 : optimized 7 state140.1 state140.2 = false := by decide +kernel

theorem eliminate141 : optimized 7 state141.1 state141.2 = false := by decide +kernel

theorem eliminate142 : optimized 7 state142.1 state142.2 = false := by decide +kernel

theorem eliminate143 : optimized 7 state143.1 state143.2 = false := by decide +kernel

theorem eliminate144 : optimized 7 state144.1 state144.2 = false := by decide +kernel

theorem eliminate145 : optimized 7 state145.1 state145.2 = false := by decide +kernel

theorem eliminate146 : optimized 7 state146.1 state146.2 = false := by decide +kernel

theorem eliminate147 : optimized 7 state147.1 state147.2 = false := by decide +kernel

theorem eliminate148 : optimized 7 state148.1 state148.2 = false := by decide +kernel

theorem eliminate149 : optimized 7 state149.1 state149.2 = false := by decide +kernel

theorem eliminate150 : optimized 7 state150.1 state150.2 = false := by decide +kernel

theorem eliminate151 : optimized 7 state151.1 state151.2 = false := by decide +kernel

theorem eliminate152 : optimized 7 state152.1 state152.2 = false := by decide +kernel

theorem eliminate153 : optimized 7 state153.1 state153.2 = false := by decide +kernel

theorem eliminate154 : optimized 7 state154.1 state154.2 = false := by decide +kernel

theorem eliminate155 : optimized 7 state155.1 state155.2 = false := by decide +kernel

theorem eliminate156 : optimized 7 state156.1 state156.2 = false := by decide +kernel

theorem eliminate157 : optimized 7 state157.1 state157.2 = false := by decide +kernel

theorem eliminate158 : optimized 7 state158.1 state158.2 = false := by decide +kernel

theorem eliminate159 : optimized 7 state159.1 state159.2 = false := by decide +kernel

theorem eliminate160 : optimized 7 state160.1 state160.2 = false := by decide +kernel

theorem eliminate62 : optimized 8 state62.1 state62.2 = false := by
  apply rejectLayer (states := [state63, state64, state65, state66, state67, state68, state69, state70, state71, state72, state73, state74, state75, state76, state77, state78, state79, state80, state81, state82, state83, state84, state85, state86, state87, state88, state89, state90, state91, state92, state93, state94, state95, state96, state97, state98, state99, state100, state101, state102, state103, state104, state105, state106, state107, state108, state109, state110, state111, state112, state113, state114, state115, state116, state117, state118, state119, state120, state121, state122, state123, state124, state125, state126, state127, state128, state129, state130, state131, state132, state133, state134, state135, state136, state137, state138, state139, state140, state141, state142, state143, state144, state145, state146, state147, state148, state149, state150, state151, state152, state153, state154, state155, state156, state157, state158, state159, state160])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate63
    · exact eliminate64
    · exact eliminate65
    · exact eliminate66
    · exact eliminate67
    · exact eliminate68
    · exact eliminate69
    · exact eliminate70
    · exact eliminate71
    · exact eliminate72
    · exact eliminate73
    · exact eliminate74
    · exact eliminate75
    · exact eliminate76
    · exact eliminate77
    · exact eliminate78
    · exact eliminate79
    · exact eliminate80
    · exact eliminate81
    · exact eliminate82
    · exact eliminate83
    · exact eliminate84
    · exact eliminate85
    · exact eliminate86
    · exact eliminate87
    · exact eliminate88
    · exact eliminate89
    · exact eliminate90
    · exact eliminate91
    · exact eliminate92
    · exact eliminate93
    · exact eliminate94
    · exact eliminate95
    · exact eliminate96
    · exact eliminate97
    · exact eliminate98
    · exact eliminate99
    · exact eliminate100
    · exact eliminate101
    · exact eliminate102
    · exact eliminate103
    · exact eliminate104
    · exact eliminate105
    · exact eliminate106
    · exact eliminate107
    · exact eliminate108
    · exact eliminate109
    · exact eliminate110
    · exact eliminate111
    · exact eliminate112
    · exact eliminate113
    · exact eliminate114
    · exact eliminate115
    · exact eliminate116
    · exact eliminate117
    · exact eliminate118
    · exact eliminate119
    · exact eliminate120
    · exact eliminate121
    · exact eliminate122
    · exact eliminate123
    · exact eliminate124
    · exact eliminate125
    · exact eliminate126
    · exact eliminate127
    · exact eliminate128
    · exact eliminate129
    · exact eliminate130
    · exact eliminate131
    · exact eliminate132
    · exact eliminate133
    · exact eliminate134
    · exact eliminate135
    · exact eliminate136
    · exact eliminate137
    · exact eliminate138
    · exact eliminate139
    · exact eliminate140
    · exact eliminate141
    · exact eliminate142
    · exact eliminate143
    · exact eliminate144
    · exact eliminate145
    · exact eliminate146
    · exact eliminate147
    · exact eliminate148
    · exact eliminate149
    · exact eliminate150
    · exact eliminate151
    · exact eliminate152
    · exact eliminate153
    · exact eliminate154
    · exact eliminate155
    · exact eliminate156
    · exact eliminate157
    · exact eliminate158
    · exact eliminate159
    · exact eliminate160

theorem eliminate162 : optimized 7 state162.1 state162.2 = false := by decide +kernel

theorem eliminate163 : optimized 7 state163.1 state163.2 = false := by decide +kernel

theorem eliminate164 : optimized 7 state164.1 state164.2 = false := by decide +kernel

theorem eliminate165 : optimized 7 state165.1 state165.2 = false := by decide +kernel

theorem eliminate166 : optimized 7 state166.1 state166.2 = false := by decide +kernel

theorem eliminate167 : optimized 7 state167.1 state167.2 = false := by decide +kernel

theorem eliminate168 : optimized 7 state168.1 state168.2 = false := by decide +kernel

theorem eliminate169 : optimized 7 state169.1 state169.2 = false := by decide +kernel

theorem eliminate170 : optimized 7 state170.1 state170.2 = false := by decide +kernel

theorem eliminate171 : optimized 7 state171.1 state171.2 = false := by decide +kernel

theorem eliminate172 : optimized 7 state172.1 state172.2 = false := by decide +kernel

theorem eliminate173 : optimized 7 state173.1 state173.2 = false := by decide +kernel

theorem eliminate174 : optimized 7 state174.1 state174.2 = false := by decide +kernel

theorem eliminate175 : optimized 7 state175.1 state175.2 = false := by decide +kernel

theorem eliminate176 : optimized 7 state176.1 state176.2 = false := by decide +kernel

theorem eliminate177 : optimized 7 state177.1 state177.2 = false := by decide +kernel

theorem eliminate178 : optimized 7 state178.1 state178.2 = false := by decide +kernel

theorem eliminate179 : optimized 7 state179.1 state179.2 = false := by decide +kernel

theorem eliminate180 : optimized 7 state180.1 state180.2 = false := by decide +kernel

theorem eliminate181 : optimized 7 state181.1 state181.2 = false := by decide +kernel

theorem eliminate182 : optimized 7 state182.1 state182.2 = false := by decide +kernel

theorem eliminate183 : optimized 7 state183.1 state183.2 = false := by decide +kernel

theorem eliminate184 : optimized 7 state184.1 state184.2 = false := by decide +kernel

theorem eliminate185 : optimized 7 state185.1 state185.2 = false := by decide +kernel

theorem eliminate186 : optimized 7 state186.1 state186.2 = false := by decide +kernel

theorem eliminate187 : optimized 7 state187.1 state187.2 = false := by decide +kernel

theorem eliminate188 : optimized 7 state188.1 state188.2 = false := by decide +kernel

theorem eliminate189 : optimized 7 state189.1 state189.2 = false := by decide +kernel

theorem eliminate190 : optimized 7 state190.1 state190.2 = false := by decide +kernel

theorem eliminate191 : optimized 7 state191.1 state191.2 = false := by decide +kernel

theorem eliminate192 : optimized 7 state192.1 state192.2 = false := by decide +kernel

theorem eliminate193 : optimized 7 state193.1 state193.2 = false := by decide +kernel

theorem eliminate194 : optimized 7 state194.1 state194.2 = false := by decide +kernel

theorem eliminate195 : optimized 7 state195.1 state195.2 = false := by decide +kernel

theorem eliminate196 : optimized 7 state196.1 state196.2 = false := by decide +kernel

theorem eliminate197 : optimized 7 state197.1 state197.2 = false := by decide +kernel

theorem eliminate198 : optimized 7 state198.1 state198.2 = false := by decide +kernel

theorem eliminate199 : optimized 7 state199.1 state199.2 = false := by decide +kernel

theorem eliminate200 : optimized 7 state200.1 state200.2 = false := by decide +kernel

theorem eliminate201 : optimized 7 state201.1 state201.2 = false := by decide +kernel

theorem eliminate202 : optimized 7 state202.1 state202.2 = false := by decide +kernel

theorem eliminate203 : optimized 7 state203.1 state203.2 = false := by decide +kernel

theorem eliminate204 : optimized 7 state204.1 state204.2 = false := by decide +kernel

theorem eliminate205 : optimized 7 state205.1 state205.2 = false := by decide +kernel

theorem eliminate206 : optimized 7 state206.1 state206.2 = false := by decide +kernel

theorem eliminate161 : optimized 8 state161.1 state161.2 = false := by
  apply rejectLayer (states := [state162, state163, state164, state165, state166, state167, state168, state169, state170, state171, state172, state173, state174, state175, state176, state177, state178, state179, state180, state181, state182, state183, state184, state185, state186, state187, state188, state189, state190, state191, state192, state193, state194, state195, state196, state197, state198, state199, state200, state201, state202, state203, state204, state205, state206])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate162
    · exact eliminate163
    · exact eliminate164
    · exact eliminate165
    · exact eliminate166
    · exact eliminate167
    · exact eliminate168
    · exact eliminate169
    · exact eliminate170
    · exact eliminate171
    · exact eliminate172
    · exact eliminate173
    · exact eliminate174
    · exact eliminate175
    · exact eliminate176
    · exact eliminate177
    · exact eliminate178
    · exact eliminate179
    · exact eliminate180
    · exact eliminate181
    · exact eliminate182
    · exact eliminate183
    · exact eliminate184
    · exact eliminate185
    · exact eliminate186
    · exact eliminate187
    · exact eliminate188
    · exact eliminate189
    · exact eliminate190
    · exact eliminate191
    · exact eliminate192
    · exact eliminate193
    · exact eliminate194
    · exact eliminate195
    · exact eliminate196
    · exact eliminate197
    · exact eliminate198
    · exact eliminate199
    · exact eliminate200
    · exact eliminate201
    · exact eliminate202
    · exact eliminate203
    · exact eliminate204
    · exact eliminate205
    · exact eliminate206

theorem eliminate208 : optimized 7 state208.1 state208.2 = false := by decide +kernel

theorem eliminate209 : optimized 7 state209.1 state209.2 = false := by decide +kernel

theorem eliminate210 : optimized 7 state210.1 state210.2 = false := by decide +kernel

theorem eliminate211 : optimized 7 state211.1 state211.2 = false := by decide +kernel

theorem eliminate212 : optimized 7 state212.1 state212.2 = false := by decide +kernel

theorem eliminate213 : optimized 7 state213.1 state213.2 = false := by decide +kernel

theorem eliminate214 : optimized 7 state214.1 state214.2 = false := by decide +kernel

theorem eliminate215 : optimized 7 state215.1 state215.2 = false := by decide +kernel

theorem eliminate216 : optimized 7 state216.1 state216.2 = false := by decide +kernel

theorem eliminate217 : optimized 7 state217.1 state217.2 = false := by decide +kernel

theorem eliminate218 : optimized 7 state218.1 state218.2 = false := by decide +kernel

theorem eliminate219 : optimized 7 state219.1 state219.2 = false := by decide +kernel

theorem eliminate220 : optimized 7 state220.1 state220.2 = false := by decide +kernel

theorem eliminate221 : optimized 7 state221.1 state221.2 = false := by decide +kernel

theorem eliminate222 : optimized 7 state222.1 state222.2 = false := by decide +kernel

theorem eliminate223 : optimized 7 state223.1 state223.2 = false := by decide +kernel

theorem eliminate224 : optimized 7 state224.1 state224.2 = false := by decide +kernel

theorem eliminate225 : optimized 7 state225.1 state225.2 = false := by decide +kernel

theorem eliminate226 : optimized 7 state226.1 state226.2 = false := by decide +kernel

theorem eliminate227 : optimized 7 state227.1 state227.2 = false := by decide +kernel

theorem eliminate228 : optimized 7 state228.1 state228.2 = false := by decide +kernel

theorem eliminate229 : optimized 7 state229.1 state229.2 = false := by decide +kernel

theorem eliminate230 : optimized 7 state230.1 state230.2 = false := by decide +kernel

theorem eliminate231 : optimized 7 state231.1 state231.2 = false := by decide +kernel

theorem eliminate232 : optimized 7 state232.1 state232.2 = false := by decide +kernel

theorem eliminate233 : optimized 7 state233.1 state233.2 = false := by decide +kernel

theorem eliminate234 : optimized 7 state234.1 state234.2 = false := by decide +kernel

theorem eliminate235 : optimized 7 state235.1 state235.2 = false := by decide +kernel

theorem eliminate236 : optimized 7 state236.1 state236.2 = false := by decide +kernel

theorem eliminate237 : optimized 7 state237.1 state237.2 = false := by decide +kernel

theorem eliminate238 : optimized 7 state238.1 state238.2 = false := by decide +kernel

theorem eliminate239 : optimized 7 state239.1 state239.2 = false := by decide +kernel

theorem eliminate240 : optimized 7 state240.1 state240.2 = false := by decide +kernel

theorem eliminate241 : optimized 7 state241.1 state241.2 = false := by decide +kernel

theorem eliminate242 : optimized 7 state242.1 state242.2 = false := by decide +kernel

theorem eliminate243 : optimized 7 state243.1 state243.2 = false := by decide +kernel

theorem eliminate244 : optimized 7 state244.1 state244.2 = false := by decide +kernel

theorem eliminate245 : optimized 7 state245.1 state245.2 = false := by decide +kernel

theorem eliminate246 : optimized 7 state246.1 state246.2 = false := by decide +kernel

theorem eliminate247 : optimized 7 state247.1 state247.2 = false := by decide +kernel

theorem eliminate248 : optimized 7 state248.1 state248.2 = false := by decide +kernel

theorem eliminate249 : optimized 7 state249.1 state249.2 = false := by decide +kernel

theorem eliminate207 : optimized 8 state207.1 state207.2 = false := by
  apply rejectLayer (states := [state208, state163, state164, state209, state210, state211, state168, state212, state213, state214, state215, state216, state217, state218, state219, state220, state221, state222, state223, state224, state225, state226, state227, state228, state229, state230, state231, state232, state233, state234, state235, state236, state237, state238, state239, state240, state241, state242, state243, state244, state245, state246, state247, state248, state249])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate208
    · exact eliminate163
    · exact eliminate164
    · exact eliminate209
    · exact eliminate210
    · exact eliminate211
    · exact eliminate168
    · exact eliminate212
    · exact eliminate213
    · exact eliminate214
    · exact eliminate215
    · exact eliminate216
    · exact eliminate217
    · exact eliminate218
    · exact eliminate219
    · exact eliminate220
    · exact eliminate221
    · exact eliminate222
    · exact eliminate223
    · exact eliminate224
    · exact eliminate225
    · exact eliminate226
    · exact eliminate227
    · exact eliminate228
    · exact eliminate229
    · exact eliminate230
    · exact eliminate231
    · exact eliminate232
    · exact eliminate233
    · exact eliminate234
    · exact eliminate235
    · exact eliminate236
    · exact eliminate237
    · exact eliminate238
    · exact eliminate239
    · exact eliminate240
    · exact eliminate241
    · exact eliminate242
    · exact eliminate243
    · exact eliminate244
    · exact eliminate245
    · exact eliminate246
    · exact eliminate247
    · exact eliminate248
    · exact eliminate249

theorem eliminate250 : optimized 8 state250.1 state250.2 = false := by decide +kernel

theorem eliminate251 : optimized 8 state251.1 state251.2 = false := by decide +kernel

theorem eliminate252 : optimized 8 state252.1 state252.2 = false := by decide +kernel

theorem eliminate253 : optimized 8 state253.1 state253.2 = false := by decide +kernel

theorem eliminate254 : optimized 8 state254.1 state254.2 = false := by decide +kernel

theorem eliminate255 : optimized 8 state255.1 state255.2 = false := by decide +kernel

theorem eliminate256 : optimized 8 state256.1 state256.2 = false := by decide +kernel

theorem eliminate257 : optimized 8 state257.1 state257.2 = false := by decide +kernel

theorem eliminate258 : optimized 8 state258.1 state258.2 = false := by decide +kernel

theorem eliminate259 : optimized 8 state259.1 state259.2 = false := by decide +kernel

theorem eliminate260 : optimized 8 state260.1 state260.2 = false := by decide +kernel

theorem eliminate261 : optimized 8 state261.1 state261.2 = false := by decide +kernel

theorem eliminate263 : optimized 7 state263.1 state263.2 = false := by decide +kernel

theorem eliminate264 : optimized 7 state264.1 state264.2 = false := by decide +kernel

theorem eliminate265 : optimized 7 state265.1 state265.2 = false := by decide +kernel

theorem eliminate266 : optimized 7 state266.1 state266.2 = false := by decide +kernel

theorem eliminate267 : optimized 7 state267.1 state267.2 = false := by decide +kernel

theorem eliminate268 : optimized 7 state268.1 state268.2 = false := by decide +kernel

theorem eliminate269 : optimized 7 state269.1 state269.2 = false := by decide +kernel

theorem eliminate270 : optimized 7 state270.1 state270.2 = false := by decide +kernel

theorem eliminate271 : optimized 7 state271.1 state271.2 = false := by decide +kernel

theorem eliminate272 : optimized 7 state272.1 state272.2 = false := by decide +kernel

theorem eliminate273 : optimized 7 state273.1 state273.2 = false := by decide +kernel

theorem eliminate274 : optimized 7 state274.1 state274.2 = false := by decide +kernel

theorem eliminate275 : optimized 7 state275.1 state275.2 = false := by decide +kernel

theorem eliminate276 : optimized 7 state276.1 state276.2 = false := by decide +kernel

theorem eliminate277 : optimized 7 state277.1 state277.2 = false := by decide +kernel

theorem eliminate278 : optimized 7 state278.1 state278.2 = false := by decide +kernel

theorem eliminate279 : optimized 7 state279.1 state279.2 = false := by decide +kernel

theorem eliminate280 : optimized 7 state280.1 state280.2 = false := by decide +kernel

theorem eliminate281 : optimized 7 state281.1 state281.2 = false := by decide +kernel

theorem eliminate282 : optimized 7 state282.1 state282.2 = false := by decide +kernel

theorem eliminate283 : optimized 7 state283.1 state283.2 = false := by decide +kernel

theorem eliminate284 : optimized 7 state284.1 state284.2 = false := by decide +kernel

theorem eliminate285 : optimized 7 state285.1 state285.2 = false := by decide +kernel

theorem eliminate286 : optimized 7 state286.1 state286.2 = false := by decide +kernel

theorem eliminate287 : optimized 7 state287.1 state287.2 = false := by decide +kernel

theorem eliminate288 : optimized 7 state288.1 state288.2 = false := by decide +kernel

theorem eliminate289 : optimized 7 state289.1 state289.2 = false := by decide +kernel

theorem eliminate290 : optimized 7 state290.1 state290.2 = false := by decide +kernel

theorem eliminate291 : optimized 7 state291.1 state291.2 = false := by decide +kernel

theorem eliminate292 : optimized 7 state292.1 state292.2 = false := by decide +kernel

theorem eliminate293 : optimized 7 state293.1 state293.2 = false := by decide +kernel

theorem eliminate294 : optimized 7 state294.1 state294.2 = false := by decide +kernel

theorem eliminate295 : optimized 7 state295.1 state295.2 = false := by decide +kernel

theorem eliminate262 : optimized 8 state262.1 state262.2 = false := by
  apply rejectLayer (states := [state263, state264, state265, state266, state267, state268, state80, state269, state270, state271, state272, state273, state274, state275, state276, state277, state278, state279, state280, state281, state282, state283, state284, state285, state286, state287, state288, state289, state290, state291, state292, state293, state294, state295])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate263
    · exact eliminate264
    · exact eliminate265
    · exact eliminate266
    · exact eliminate267
    · exact eliminate268
    · exact eliminate80
    · exact eliminate269
    · exact eliminate270
    · exact eliminate271
    · exact eliminate272
    · exact eliminate273
    · exact eliminate274
    · exact eliminate275
    · exact eliminate276
    · exact eliminate277
    · exact eliminate278
    · exact eliminate279
    · exact eliminate280
    · exact eliminate281
    · exact eliminate282
    · exact eliminate283
    · exact eliminate284
    · exact eliminate285
    · exact eliminate286
    · exact eliminate287
    · exact eliminate288
    · exact eliminate289
    · exact eliminate290
    · exact eliminate291
    · exact eliminate292
    · exact eliminate293
    · exact eliminate294
    · exact eliminate295

theorem eliminate296 : optimized 8 state296.1 state296.2 = false := by decide +kernel

theorem eliminate297 : optimized 8 state297.1 state297.2 = false := by decide +kernel

theorem eliminate298 : optimized 8 state298.1 state298.2 = false := by decide +kernel

theorem eliminate299 : optimized 8 state299.1 state299.2 = false := by decide +kernel

theorem eliminate300 : optimized 8 state300.1 state300.2 = false := by decide +kernel

theorem eliminate301 : optimized 8 state301.1 state301.2 = false := by decide +kernel

theorem eliminate302 : optimized 8 state302.1 state302.2 = false := by decide +kernel

theorem eliminate303 : optimized 8 state303.1 state303.2 = false := by decide +kernel

theorem eliminate305 : optimized 7 state305.1 state305.2 = false := by decide +kernel

theorem eliminate306 : optimized 7 state306.1 state306.2 = false := by decide +kernel

theorem eliminate307 : optimized 7 state307.1 state307.2 = false := by decide +kernel

theorem eliminate308 : optimized 7 state308.1 state308.2 = false := by decide +kernel

theorem eliminate309 : optimized 7 state309.1 state309.2 = false := by decide +kernel

theorem eliminate310 : optimized 7 state310.1 state310.2 = false := by decide +kernel

theorem eliminate311 : optimized 7 state311.1 state311.2 = false := by decide +kernel

theorem eliminate312 : optimized 7 state312.1 state312.2 = false := by decide +kernel

theorem eliminate313 : optimized 7 state313.1 state313.2 = false := by decide +kernel

theorem eliminate314 : optimized 7 state314.1 state314.2 = false := by decide +kernel

theorem eliminate315 : optimized 7 state315.1 state315.2 = false := by decide +kernel

theorem eliminate316 : optimized 7 state316.1 state316.2 = false := by decide +kernel

theorem eliminate317 : optimized 7 state317.1 state317.2 = false := by decide +kernel

theorem eliminate318 : optimized 7 state318.1 state318.2 = false := by decide +kernel

theorem eliminate319 : optimized 7 state319.1 state319.2 = false := by decide +kernel

theorem eliminate320 : optimized 7 state320.1 state320.2 = false := by decide +kernel

theorem eliminate321 : optimized 7 state321.1 state321.2 = false := by decide +kernel

theorem eliminate322 : optimized 7 state322.1 state322.2 = false := by decide +kernel

theorem eliminate323 : optimized 7 state323.1 state323.2 = false := by decide +kernel

theorem eliminate324 : optimized 7 state324.1 state324.2 = false := by decide +kernel

theorem eliminate325 : optimized 7 state325.1 state325.2 = false := by decide +kernel

theorem eliminate326 : optimized 7 state326.1 state326.2 = false := by decide +kernel

theorem eliminate327 : optimized 7 state327.1 state327.2 = false := by decide +kernel

theorem eliminate328 : optimized 7 state328.1 state328.2 = false := by decide +kernel

theorem eliminate329 : optimized 7 state329.1 state329.2 = false := by decide +kernel

theorem eliminate330 : optimized 7 state330.1 state330.2 = false := by decide +kernel

theorem eliminate331 : optimized 7 state331.1 state331.2 = false := by decide +kernel

theorem eliminate332 : optimized 7 state332.1 state332.2 = false := by decide +kernel

theorem eliminate333 : optimized 7 state333.1 state333.2 = false := by decide +kernel

theorem eliminate334 : optimized 7 state334.1 state334.2 = false := by decide +kernel

theorem eliminate335 : optimized 7 state335.1 state335.2 = false := by decide +kernel

theorem eliminate336 : optimized 7 state336.1 state336.2 = false := by decide +kernel

theorem eliminate337 : optimized 7 state337.1 state337.2 = false := by decide +kernel

theorem eliminate338 : optimized 7 state338.1 state338.2 = false := by decide +kernel

theorem eliminate339 : optimized 7 state339.1 state339.2 = false := by decide +kernel

theorem eliminate340 : optimized 7 state340.1 state340.2 = false := by decide +kernel

theorem eliminate341 : optimized 7 state341.1 state341.2 = false := by decide +kernel

theorem eliminate342 : optimized 7 state342.1 state342.2 = false := by decide +kernel

theorem eliminate343 : optimized 7 state343.1 state343.2 = false := by decide +kernel

theorem eliminate344 : optimized 7 state344.1 state344.2 = false := by decide +kernel

theorem eliminate345 : optimized 7 state345.1 state345.2 = false := by decide +kernel

theorem eliminate346 : optimized 7 state346.1 state346.2 = false := by decide +kernel

theorem eliminate304 : optimized 8 state304.1 state304.2 = false := by
  apply rejectLayer (states := [state305, state306, state307, state308, state309, state310, state311, state312, state313, state314, state315, state316, state317, state318, state319, state320, state321, state322, state323, state324, state325, state326, state327, state328, state329, state330, state331, state332, state333, state334, state335, state336, state337, state338, state339, state340, state341, state342, state343, state344, state345, state346])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate305
    · exact eliminate306
    · exact eliminate307
    · exact eliminate308
    · exact eliminate309
    · exact eliminate310
    · exact eliminate311
    · exact eliminate312
    · exact eliminate313
    · exact eliminate314
    · exact eliminate315
    · exact eliminate316
    · exact eliminate317
    · exact eliminate318
    · exact eliminate319
    · exact eliminate320
    · exact eliminate321
    · exact eliminate322
    · exact eliminate323
    · exact eliminate324
    · exact eliminate325
    · exact eliminate326
    · exact eliminate327
    · exact eliminate328
    · exact eliminate329
    · exact eliminate330
    · exact eliminate331
    · exact eliminate332
    · exact eliminate333
    · exact eliminate334
    · exact eliminate335
    · exact eliminate336
    · exact eliminate337
    · exact eliminate338
    · exact eliminate339
    · exact eliminate340
    · exact eliminate341
    · exact eliminate342
    · exact eliminate343
    · exact eliminate344
    · exact eliminate345
    · exact eliminate346

theorem eliminate347 : optimized 8 state347.1 state347.2 = false := by decide +kernel

theorem eliminate348 : optimized 8 state348.1 state348.2 = false := by decide +kernel

theorem eliminate349 : optimized 8 state349.1 state349.2 = false := by decide +kernel

theorem eliminate350 : optimized 8 state350.1 state350.2 = false := by decide +kernel

theorem eliminate351 : optimized 8 state351.1 state351.2 = false := by decide +kernel

theorem eliminate352 : optimized 8 state352.1 state352.2 = false := by decide +kernel

theorem eliminate353 : optimized 8 state353.1 state353.2 = false := by decide +kernel

theorem eliminate354 : optimized 8 state354.1 state354.2 = false := by decide +kernel

theorem eliminate355 : optimized 8 state355.1 state355.2 = false := by decide +kernel

theorem eliminate356 : optimized 8 state356.1 state356.2 = false := by decide +kernel

theorem eliminate357 : optimized 8 state357.1 state357.2 = false := by decide +kernel

theorem eliminate358 : optimized 8 state358.1 state358.2 = false := by decide +kernel

theorem eliminate360 : optimized 7 state360.1 state360.2 = false := by decide +kernel

theorem eliminate361 : optimized 7 state361.1 state361.2 = false := by decide +kernel

theorem eliminate362 : optimized 7 state362.1 state362.2 = false := by decide +kernel

theorem eliminate363 : optimized 7 state363.1 state363.2 = false := by decide +kernel

theorem eliminate364 : optimized 7 state364.1 state364.2 = false := by decide +kernel

theorem eliminate365 : optimized 7 state365.1 state365.2 = false := by decide +kernel

theorem eliminate366 : optimized 7 state366.1 state366.2 = false := by decide +kernel

theorem eliminate367 : optimized 7 state367.1 state367.2 = false := by decide +kernel

theorem eliminate368 : optimized 7 state368.1 state368.2 = false := by decide +kernel

theorem eliminate369 : optimized 7 state369.1 state369.2 = false := by decide +kernel

theorem eliminate370 : optimized 7 state370.1 state370.2 = false := by decide +kernel

theorem eliminate371 : optimized 7 state371.1 state371.2 = false := by decide +kernel

theorem eliminate372 : optimized 7 state372.1 state372.2 = false := by decide +kernel

theorem eliminate373 : optimized 7 state373.1 state373.2 = false := by decide +kernel

theorem eliminate374 : optimized 7 state374.1 state374.2 = false := by decide +kernel

theorem eliminate375 : optimized 7 state375.1 state375.2 = false := by decide +kernel

theorem eliminate376 : optimized 7 state376.1 state376.2 = false := by decide +kernel

theorem eliminate377 : optimized 7 state377.1 state377.2 = false := by decide +kernel

theorem eliminate378 : optimized 7 state378.1 state378.2 = false := by decide +kernel

theorem eliminate379 : optimized 7 state379.1 state379.2 = false := by decide +kernel

theorem eliminate380 : optimized 7 state380.1 state380.2 = false := by decide +kernel

theorem eliminate381 : optimized 7 state381.1 state381.2 = false := by decide +kernel

theorem eliminate382 : optimized 7 state382.1 state382.2 = false := by decide +kernel

theorem eliminate383 : optimized 7 state383.1 state383.2 = false := by decide +kernel

theorem eliminate384 : optimized 7 state384.1 state384.2 = false := by decide +kernel

theorem eliminate385 : optimized 7 state385.1 state385.2 = false := by decide +kernel

theorem eliminate386 : optimized 7 state386.1 state386.2 = false := by decide +kernel

theorem eliminate387 : optimized 7 state387.1 state387.2 = false := by decide +kernel

theorem eliminate388 : optimized 7 state388.1 state388.2 = false := by decide +kernel

theorem eliminate389 : optimized 7 state389.1 state389.2 = false := by decide +kernel

theorem eliminate390 : optimized 7 state390.1 state390.2 = false := by decide +kernel

theorem eliminate391 : optimized 7 state391.1 state391.2 = false := by decide +kernel

theorem eliminate392 : optimized 7 state392.1 state392.2 = false := by decide +kernel

theorem eliminate359 : optimized 8 state359.1 state359.2 = false := by
  apply rejectLayer (states := [state360, state361, state362, state363, state364, state365, state80, state366, state367, state368, state369, state370, state371, state372, state373, state374, state375, state376, state377, state378, state379, state380, state381, state382, state383, state384, state385, state386, state387, state388, state389, state390, state391, state392])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate360
    · exact eliminate361
    · exact eliminate362
    · exact eliminate363
    · exact eliminate364
    · exact eliminate365
    · exact eliminate80
    · exact eliminate366
    · exact eliminate367
    · exact eliminate368
    · exact eliminate369
    · exact eliminate370
    · exact eliminate371
    · exact eliminate372
    · exact eliminate373
    · exact eliminate374
    · exact eliminate375
    · exact eliminate376
    · exact eliminate377
    · exact eliminate378
    · exact eliminate379
    · exact eliminate380
    · exact eliminate381
    · exact eliminate382
    · exact eliminate383
    · exact eliminate384
    · exact eliminate385
    · exact eliminate386
    · exact eliminate387
    · exact eliminate388
    · exact eliminate389
    · exact eliminate390
    · exact eliminate391
    · exact eliminate392

theorem eliminate393 : optimized 8 state393.1 state393.2 = false := by decide +kernel

theorem eliminate394 : optimized 8 state394.1 state394.2 = false := by decide +kernel

theorem eliminate395 : optimized 8 state395.1 state395.2 = false := by decide +kernel

theorem eliminate396 : optimized 8 state396.1 state396.2 = false := by decide +kernel

theorem eliminate397 : optimized 8 state397.1 state397.2 = false := by decide +kernel

theorem eliminate398 : optimized 8 state398.1 state398.2 = false := by decide +kernel

theorem eliminate399 : optimized 8 state399.1 state399.2 = false := by decide +kernel

theorem eliminate400 : optimized 8 state400.1 state400.2 = false := by decide +kernel

theorem eliminate402 : optimized 7 state402.1 state402.2 = false := by decide +kernel

theorem eliminate403 : optimized 7 state403.1 state403.2 = false := by decide +kernel

theorem eliminate404 : optimized 7 state404.1 state404.2 = false := by decide +kernel

theorem eliminate405 : optimized 7 state405.1 state405.2 = false := by decide +kernel

theorem eliminate406 : optimized 7 state406.1 state406.2 = false := by decide +kernel

theorem eliminate407 : optimized 7 state407.1 state407.2 = false := by decide +kernel

theorem eliminate408 : optimized 7 state408.1 state408.2 = false := by decide +kernel

theorem eliminate409 : optimized 7 state409.1 state409.2 = false := by decide +kernel

theorem eliminate410 : optimized 7 state410.1 state410.2 = false := by decide +kernel

theorem eliminate411 : optimized 7 state411.1 state411.2 = false := by decide +kernel

theorem eliminate412 : optimized 7 state412.1 state412.2 = false := by decide +kernel

theorem eliminate413 : optimized 7 state413.1 state413.2 = false := by decide +kernel

theorem eliminate414 : optimized 7 state414.1 state414.2 = false := by decide +kernel

theorem eliminate415 : optimized 7 state415.1 state415.2 = false := by decide +kernel

theorem eliminate416 : optimized 7 state416.1 state416.2 = false := by decide +kernel

theorem eliminate417 : optimized 7 state417.1 state417.2 = false := by decide +kernel

theorem eliminate418 : optimized 7 state418.1 state418.2 = false := by decide +kernel

theorem eliminate419 : optimized 7 state419.1 state419.2 = false := by decide +kernel

theorem eliminate420 : optimized 7 state420.1 state420.2 = false := by decide +kernel

theorem eliminate421 : optimized 7 state421.1 state421.2 = false := by decide +kernel

theorem eliminate422 : optimized 7 state422.1 state422.2 = false := by decide +kernel

theorem eliminate423 : optimized 7 state423.1 state423.2 = false := by decide +kernel

theorem eliminate424 : optimized 7 state424.1 state424.2 = false := by decide +kernel

theorem eliminate425 : optimized 7 state425.1 state425.2 = false := by decide +kernel

theorem eliminate426 : optimized 7 state426.1 state426.2 = false := by decide +kernel

theorem eliminate427 : optimized 7 state427.1 state427.2 = false := by decide +kernel

theorem eliminate428 : optimized 7 state428.1 state428.2 = false := by decide +kernel

theorem eliminate429 : optimized 7 state429.1 state429.2 = false := by decide +kernel

theorem eliminate430 : optimized 7 state430.1 state430.2 = false := by decide +kernel

theorem eliminate431 : optimized 7 state431.1 state431.2 = false := by decide +kernel

theorem eliminate432 : optimized 7 state432.1 state432.2 = false := by decide +kernel

theorem eliminate433 : optimized 7 state433.1 state433.2 = false := by decide +kernel

theorem eliminate434 : optimized 7 state434.1 state434.2 = false := by decide +kernel

theorem eliminate435 : optimized 7 state435.1 state435.2 = false := by decide +kernel

theorem eliminate436 : optimized 7 state436.1 state436.2 = false := by decide +kernel

theorem eliminate437 : optimized 7 state437.1 state437.2 = false := by decide +kernel

theorem eliminate438 : optimized 7 state438.1 state438.2 = false := by decide +kernel

theorem eliminate439 : optimized 7 state439.1 state439.2 = false := by decide +kernel

theorem eliminate440 : optimized 7 state440.1 state440.2 = false := by decide +kernel

theorem eliminate441 : optimized 7 state441.1 state441.2 = false := by decide +kernel

theorem eliminate442 : optimized 7 state442.1 state442.2 = false := by decide +kernel

theorem eliminate443 : optimized 7 state443.1 state443.2 = false := by decide +kernel

theorem eliminate401 : optimized 8 state401.1 state401.2 = false := by
  apply rejectLayer (states := [state402, state403, state404, state405, state406, state407, state408, state409, state410, state411, state412, state413, state414, state415, state416, state417, state418, state419, state420, state421, state422, state423, state424, state425, state426, state427, state428, state429, state430, state431, state432, state433, state434, state435, state436, state437, state438, state439, state440, state441, state442, state443])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate402
    · exact eliminate403
    · exact eliminate404
    · exact eliminate405
    · exact eliminate406
    · exact eliminate407
    · exact eliminate408
    · exact eliminate409
    · exact eliminate410
    · exact eliminate411
    · exact eliminate412
    · exact eliminate413
    · exact eliminate414
    · exact eliminate415
    · exact eliminate416
    · exact eliminate417
    · exact eliminate418
    · exact eliminate419
    · exact eliminate420
    · exact eliminate421
    · exact eliminate422
    · exact eliminate423
    · exact eliminate424
    · exact eliminate425
    · exact eliminate426
    · exact eliminate427
    · exact eliminate428
    · exact eliminate429
    · exact eliminate430
    · exact eliminate431
    · exact eliminate432
    · exact eliminate433
    · exact eliminate434
    · exact eliminate435
    · exact eliminate436
    · exact eliminate437
    · exact eliminate438
    · exact eliminate439
    · exact eliminate440
    · exact eliminate441
    · exact eliminate442
    · exact eliminate443

theorem eliminate444 : optimized 8 state444.1 state444.2 = false := by decide +kernel

theorem eliminate445 : optimized 8 state445.1 state445.2 = false := by decide +kernel

theorem eliminate446 : optimized 8 state446.1 state446.2 = false := by decide +kernel

theorem eliminate447 : optimized 8 state447.1 state447.2 = false := by decide +kernel

theorem eliminate448 : optimized 8 state448.1 state448.2 = false := by decide +kernel

theorem eliminate449 : optimized 8 state449.1 state449.2 = false := by decide +kernel

theorem eliminate450 : optimized 8 state450.1 state450.2 = false := by decide +kernel

theorem eliminate451 : optimized 8 state451.1 state451.2 = false := by decide +kernel

theorem eliminate452 : optimized 8 state452.1 state452.2 = false := by decide +kernel

theorem eliminate453 : optimized 8 state453.1 state453.2 = false := by decide +kernel

theorem eliminate454 : optimized 8 state454.1 state454.2 = false := by decide +kernel

theorem eliminate455 : optimized 8 state455.1 state455.2 = false := by decide +kernel

theorem eliminate456 : optimized 8 state456.1 state456.2 = false := by decide +kernel

theorem eliminate457 : optimized 8 state457.1 state457.2 = false := by decide +kernel

theorem eliminate458 : optimized 8 state458.1 state458.2 = false := by decide +kernel

theorem eliminate459 : optimized 8 state459.1 state459.2 = false := by decide +kernel

theorem eliminate460 : optimized 8 state460.1 state460.2 = false := by decide +kernel

theorem eliminate461 : optimized 8 state461.1 state461.2 = false := by decide +kernel

theorem eliminate463 : optimized 7 state463.1 state463.2 = false := by decide +kernel

theorem eliminate464 : optimized 7 state464.1 state464.2 = false := by decide +kernel

theorem eliminate465 : optimized 7 state465.1 state465.2 = false := by decide +kernel

theorem eliminate466 : optimized 7 state466.1 state466.2 = false := by decide +kernel

theorem eliminate467 : optimized 7 state467.1 state467.2 = false := by decide +kernel

theorem eliminate468 : optimized 7 state468.1 state468.2 = false := by decide +kernel

theorem eliminate469 : optimized 7 state469.1 state469.2 = false := by decide +kernel

theorem eliminate470 : optimized 7 state470.1 state470.2 = false := by decide +kernel

theorem eliminate471 : optimized 7 state471.1 state471.2 = false := by decide +kernel

theorem eliminate472 : optimized 7 state472.1 state472.2 = false := by decide +kernel

theorem eliminate473 : optimized 7 state473.1 state473.2 = false := by decide +kernel

theorem eliminate474 : optimized 7 state474.1 state474.2 = false := by decide +kernel

theorem eliminate475 : optimized 7 state475.1 state475.2 = false := by decide +kernel

theorem eliminate476 : optimized 7 state476.1 state476.2 = false := by decide +kernel

theorem eliminate477 : optimized 7 state477.1 state477.2 = false := by decide +kernel

theorem eliminate478 : optimized 7 state478.1 state478.2 = false := by decide +kernel

theorem eliminate479 : optimized 7 state479.1 state479.2 = false := by decide +kernel

theorem eliminate480 : optimized 7 state480.1 state480.2 = false := by decide +kernel

theorem eliminate481 : optimized 7 state481.1 state481.2 = false := by decide +kernel

theorem eliminate482 : optimized 7 state482.1 state482.2 = false := by decide +kernel

theorem eliminate483 : optimized 7 state483.1 state483.2 = false := by decide +kernel

theorem eliminate484 : optimized 7 state484.1 state484.2 = false := by decide +kernel

theorem eliminate485 : optimized 7 state485.1 state485.2 = false := by decide +kernel

theorem eliminate486 : optimized 7 state486.1 state486.2 = false := by decide +kernel

theorem eliminate487 : optimized 7 state487.1 state487.2 = false := by decide +kernel

theorem eliminate488 : optimized 7 state488.1 state488.2 = false := by decide +kernel

theorem eliminate489 : optimized 7 state489.1 state489.2 = false := by decide +kernel

theorem eliminate490 : optimized 7 state490.1 state490.2 = false := by decide +kernel

theorem eliminate491 : optimized 7 state491.1 state491.2 = false := by decide +kernel

theorem eliminate492 : optimized 7 state492.1 state492.2 = false := by decide +kernel

theorem eliminate493 : optimized 7 state493.1 state493.2 = false := by decide +kernel

theorem eliminate494 : optimized 7 state494.1 state494.2 = false := by decide +kernel

theorem eliminate495 : optimized 7 state495.1 state495.2 = false := by decide +kernel

theorem eliminate496 : optimized 7 state496.1 state496.2 = false := by decide +kernel

theorem eliminate497 : optimized 7 state497.1 state497.2 = false := by decide +kernel

theorem eliminate498 : optimized 7 state498.1 state498.2 = false := by decide +kernel

theorem eliminate499 : optimized 7 state499.1 state499.2 = false := by decide +kernel

theorem eliminate500 : optimized 7 state500.1 state500.2 = false := by decide +kernel

theorem eliminate501 : optimized 7 state501.1 state501.2 = false := by decide +kernel

theorem eliminate502 : optimized 7 state502.1 state502.2 = false := by decide +kernel

theorem eliminate503 : optimized 7 state503.1 state503.2 = false := by decide +kernel

theorem eliminate504 : optimized 7 state504.1 state504.2 = false := by decide +kernel

theorem eliminate505 : optimized 7 state505.1 state505.2 = false := by decide +kernel

theorem eliminate506 : optimized 7 state506.1 state506.2 = false := by decide +kernel

theorem eliminate507 : optimized 7 state507.1 state507.2 = false := by decide +kernel

theorem eliminate462 : optimized 8 state462.1 state462.2 = false := by
  apply rejectLayer (states := [state463, state464, state465, state466, state467, state468, state469, state470, state471, state472, state473, state474, state475, state476, state477, state478, state479, state480, state481, state482, state483, state484, state485, state486, state487, state488, state489, state490, state491, state492, state493, state494, state495, state496, state497, state498, state499, state500, state501, state502, state503, state504, state505, state506, state507])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact eliminate463
    · exact eliminate464
    · exact eliminate465
    · exact eliminate466
    · exact eliminate467
    · exact eliminate468
    · exact eliminate469
    · exact eliminate470
    · exact eliminate471
    · exact eliminate472
    · exact eliminate473
    · exact eliminate474
    · exact eliminate475
    · exact eliminate476
    · exact eliminate477
    · exact eliminate478
    · exact eliminate479
    · exact eliminate480
    · exact eliminate481
    · exact eliminate482
    · exact eliminate483
    · exact eliminate484
    · exact eliminate485
    · exact eliminate486
    · exact eliminate487
    · exact eliminate488
    · exact eliminate489
    · exact eliminate490
    · exact eliminate491
    · exact eliminate492
    · exact eliminate493
    · exact eliminate494
    · exact eliminate495
    · exact eliminate496
    · exact eliminate497
    · exact eliminate498
    · exact eliminate499
    · exact eliminate500
    · exact eliminate501
    · exact eliminate502
    · exact eliminate503
    · exact eliminate504
    · exact eliminate505
    · exact eliminate506
    · exact eliminate507

theorem eliminate508 : optimized 8 state508.1 state508.2 = false := by decide +kernel

theorem eliminate509 : optimized 8 state509.1 state509.2 = false := by decide +kernel

theorem eliminate510 : optimized 8 state510.1 state510.2 = false := by decide +kernel

theorem eliminate511 : optimized 8 state511.1 state511.2 = false := by decide +kernel

theorem eliminate512 : optimized 8 state512.1 state512.2 = false := by decide +kernel

theorem eliminate513 : optimized 8 state513.1 state513.2 = false := by decide +kernel

theorem eliminate514 : optimized 8 state514.1 state514.2 = false := by decide +kernel

theorem eliminate515 : optimized 8 state515.1 state515.2 = false := by decide +kernel

theorem eliminate516 : optimized 8 state516.1 state516.2 = false := by decide +kernel

theorem eliminate517 : optimized 8 state517.1 state517.2 = false := by decide +kernel

theorem eliminate518 : optimized 8 state518.1 state518.2 = false := by decide +kernel

theorem eliminate519 : optimized 8 state519.1 state519.2 = false := by decide +kernel

theorem eliminate0 : optimized 9 state0.1 state0.2 = false := by
  apply rejectLayer (states := [state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, state12, state13, state14, state15, state16, state17, state18, state19, state20, state21, state22, state23, state24, state25, state26, state27, state28, state29, state30, state31, state32, state33, state34, state35, state36, state37, state38, state39, state40, state41, state42, state43, state44, state45, state46, state47, state48, state49, state50, state51, state52, state53, state54, state55, state56, state57, state58, state59, state60, state61, state62, state161, state207, state250, state251, state252, state253, state254, state255, state256, state257, state258, state259, state260, state261, state262, state296, state297, state298, state299, state300, state301, state302, state303, state304, state347, state348, state349, state350, state351, state352, state353, state354, state355, state356, state357, state358, state359, state393, state394, state395, state396, state397, state398, state399, state400, state401, state444, state445, state446, state447, state448, state449, state450, state451, state452, state453, state454, state455, state456, state457, state458, state459, state460, state461, state462, state508, state509, state510, state511, state512, state513, state514, state515, state516, state517, state518, state519])
  · decide +kernel
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact eliminate161
    · exact eliminate207
    · exact eliminate250
    · exact eliminate251
    · exact eliminate252
    · exact eliminate253
    · exact eliminate254
    · exact eliminate255
    · exact eliminate256
    · exact eliminate257
    · exact eliminate258
    · exact eliminate259
    · exact eliminate260
    · exact eliminate261
    · exact eliminate262
    · exact eliminate296
    · exact eliminate297
    · exact eliminate298
    · exact eliminate299
    · exact eliminate300
    · exact eliminate301
    · exact eliminate302
    · exact eliminate303
    · exact eliminate304
    · exact eliminate347
    · exact eliminate348
    · exact eliminate349
    · exact eliminate350
    · exact eliminate351
    · exact eliminate352
    · exact eliminate353
    · exact eliminate354
    · exact eliminate355
    · exact eliminate356
    · exact eliminate357
    · exact eliminate358
    · exact eliminate359
    · exact eliminate393
    · exact eliminate394
    · exact eliminate395
    · exact eliminate396
    · exact eliminate397
    · exact eliminate398
    · exact eliminate399
    · exact eliminate400
    · exact eliminate401
    · exact eliminate444
    · exact eliminate445
    · exact eliminate446
    · exact eliminate447
    · exact eliminate448
    · exact eliminate449
    · exact eliminate450
    · exact eliminate451
    · exact eliminate452
    · exact eliminate453
    · exact eliminate454
    · exact eliminate455
    · exact eliminate456
    · exact eliminate457
    · exact eliminate458
    · exact eliminate459
    · exact eliminate460
    · exact eliminate461
    · exact eliminate462
    · exact eliminate508
    · exact eliminate509
    · exact eliminate510
    · exact eliminate511
    · exact eliminate512
    · exact eliminate513
    · exact eliminate514
    · exact eliminate515
    · exact eliminate516
    · exact eliminate517
    · exact eliminate518
    · exact eliminate519

theorem rejectSmall : search 9 fullInputs = false := by
  apply rejectFull
  · decide +kernel
  · exact eliminate0

theorem binaryLowerBound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = table x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ fullInputs, holds fullInputs.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (fullInputs.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 8 => bit k (fullInputs.getD i.val 0)) =
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
  exact Bool.noConfusion (rejectSmall.symm.trans (search_complete ht 9 fullInputs (by decide +kernel) (lift low run)))


def witness : Circuit := ⟨[
  ⟨.or, [0,4]⟩,
  ⟨.and, [0,4]⟩,
  ⟨.or, [5,6]⟩,
  ⟨.or, [8,1]⟩,
  ⟨.and, [11,10]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.or, [13,5]⟩,
  ⟨.or, [14,8]⟩,
  ⟨.and, [15,7]⟩,
  ⟨.or, [9,12]⟩,
  ⟨.or, [17,16]⟩], 18⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]
theorem witness_eval : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = table x := by decide +kernel

theorem monotone_replacement (s : ℕ) (C : Circuit) (hC : FanInTwo C) (hs : C.size ≤ s)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = table x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = table x := by
  by_cases present : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, hn⟩ := present
    have cut : binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hm, by simp [isBinary, hn]⟩
    have lower := binaryLowerBound C.gates C.output hC he
    exact ⟨witness, witness_mono, by change 11 ≤ s; omega, witness_eval⟩
  · exact ⟨C, fun g hg => ⟨(hC g hg).1.imp_right (·.resolve_right fun h => present ⟨g, hg, h⟩),
      (hC g hg).2⟩, hs, he⟩

end PEqualNP.Outside.L_meta_14940

theorem PEqualNP.Outside.L_meta_14940 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ eval
  obtain ⟨D, hD, hSize, hEval⟩ := PEqualNP.Outside.L_meta_14940.monotone_replacement gates.length ⟨gates, o⟩ legal (by rfl) eval
  exact ⟨D.gates, D.output, hD, hSize, hEval⟩
