import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11139

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

abbrev W := BitVec 256
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
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
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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

def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 256))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)



def table6 (x : Fin 6 → Bool) : Bool :=
  Nat.testBit 0xfffffffefffeeea0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def ins_g2 : List W := [0x3900000000000000000000ffffffffff380280a0280a0280a0280a0280a0280a, 0x3f0000000000003fffffff00000000003b0b02c0b02c0b02c0b02c0b02c0b02c, 0xcf00000003ffffc000000000000003ffc72c0b02c0b02c0b02c0b02c0b02c0b0, 0xc6003ffffc0000000003ff00000ffc00c4300c0300c0300c0300c0300c0300c0, 0x50ffc00ffc00ffc00ffc00003ff0000000401004010040100401004010040100, 0xa0fffff003ff003ff00000ffc000000000802008020080200802008020080200]
def ins_k5mp3 : List W := [0xffffff0000000000ffffff0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 0xffff000000000000ffff0000002c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2c, 0xffff00000000ff00ffff00000000ff30303030303030303030303030303030, 0xff00ff00ff00ff00ff00ff00ff00ff0040404040404040404040404040404040, 0xffff00ff00ff0000ffff00ff00ff000080808080808080808080808080808080]
def ins_k5me : List W := [0xc0000000000fffff80000000001fffff850a142850a142850a142850a142850a, 0x1fffff00000000003ffffe00000060c183060c183060c183060c183060c, 0xc07ffe0007f0003f80fffc000fe0007f08102040810204081020408102040810, 0x3f80fe03f8001fc07f01fc07f0003f8010204081020408102040810204081020, 0x3fff01fc000fe0007ffe03f8001fc00020408102040810204081020408102040]
def ins_k5mp4 : List W := [0xc000000003ffffff8000000007ffffff8140a05028140a05028140a05028140a, 0xffffc00000000001ffff80000000582c160b0582c160b0582c160b0582c, 0xc01ff000000000ff803fe000000001ff160b0582c160b0582c160b0582c160b0, 0x3fe00007fc01ff007fc0000ff803fe00180c06030180c06030180c06030180c0, 0x3ffffff803fe00007ffffff007fc000020100804020100804020100804020100]
def ins_k4 : List W := [0xff0001fffc0007fff0001fffc0007fff42108421084210842108421084210842, 0x1f07fe007c1ff801f07fe007c1ff801f84210842108421084210842108421084, 0xe0f83e0f83e0f83e0f83e0f83e0f83e008421084210842108421084210842108, 0xffc1f003ff07c00ffc1f003ff07c0010842108421084210842108421084210]
def ix_del0 : List ℕ := [40, 42, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 62, 64, 65, 66, 67, 68, 69, 70, 72, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 87, 88, 89, 90, 92, 94, 95, 96, 97, 98, 99, 100, 102, 104, 105, 106, 107, 108, 109, 110, 112, 114, 115, 116, 117, 118, 119, 40, 42, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 62, 64, 65, 66, 67, 68, 69, 70, 72, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 87, 88, 89, 90, 92, 94, 95, 96, 97, 98, 99, 100, 102, 104, 105, 106, 107, 108, 109, 110, 112, 114, 115, 116, 117, 118, 119]
def ix_del1 : List ℕ := [0, 4, 6, 7, 1, 8, 9, 70, 74, 76, 77, 71, 78, 79, 80, 84, 86, 87, 81, 88, 89, 10, 14, 16, 17, 11, 18, 19, 90, 94, 96, 97, 91, 98, 99, 100, 104, 106, 107, 101, 108, 109, 20, 24, 26, 27, 21, 28, 29, 30, 34, 36, 37, 31, 38, 39, 110, 114, 116, 117, 111, 118, 119, 0, 4, 6, 7, 1, 8, 9, 70, 74, 76, 77, 71, 78, 79, 80, 84, 86, 87, 81, 88, 89, 10, 14, 16, 17, 11, 18, 19, 90, 94, 96, 97, 91, 98, 99, 100, 104, 106, 107, 101, 108, 109, 20, 24, 26, 27, 21, 28, 29, 30, 34, 36, 37, 31, 38, 39, 110, 114, 116, 117, 111, 118, 119, 0, 4]
def ix_del2 : List ℕ := [10, 11, 12, 13, 16, 18, 19, 20, 21, 22, 23, 26, 28, 29, 30, 31, 32, 33, 36, 38, 39, 40, 41, 42, 43, 46, 48, 49, 50, 51, 52, 53, 56, 58, 59, 60, 61, 62, 63, 66, 68, 69, 90, 91, 92, 93, 96, 98, 99, 100, 101, 102, 103, 106, 108, 109, 110, 111, 112, 113, 116, 118, 119, 10, 11, 12, 13, 16, 18, 19, 20, 21, 22, 23, 26, 28, 29, 30, 31, 32, 33, 36, 38, 39, 40, 41, 42, 43, 46, 48, 49, 50, 51, 52, 53, 56, 58, 59, 60, 61, 62, 63, 66, 68, 69, 90, 91, 92, 93, 96, 98, 99, 100, 101, 102, 103, 106, 108, 109, 110, 111, 112, 113, 116, 118, 119, 10, 11]
def ix_del3 : List ℕ := [0, 4, 2, 5, 1, 3, 8, 9, 70, 74, 72, 75, 71, 73, 78, 79, 80, 84, 82, 85, 81, 83, 88, 89, 50, 54, 52, 55, 51, 53, 58, 59, 60, 64, 62, 65, 61, 63, 68, 69, 20, 24, 22, 25, 21, 23, 28, 29, 30, 34, 32, 35, 31, 33, 38, 39, 110, 114, 112, 115, 111, 113, 118, 119, 0, 4, 2, 5, 1, 3, 8, 9, 70, 74, 72, 75, 71, 73, 78, 79, 80, 84, 82, 85, 81, 83, 88, 89, 50, 54, 52, 55, 51, 53, 58, 59, 60, 64, 62, 65, 61, 63, 68, 69, 20, 24, 22, 25, 21, 23, 28, 29, 30, 34, 32, 35, 31, 33, 38, 39, 110, 114, 112, 115, 111, 113, 118, 119]
def ix_del4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 60, 61, 62, 63, 64, 65, 66, 67, 69, 80, 81, 82, 83, 84, 85, 86, 87, 89, 100, 101, 102, 103, 104, 105, 106, 107, 109, 0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 60, 61, 62, 63, 64, 65, 66, 67, 69, 80, 81, 82, 83, 84, 85, 86, 87, 89, 100, 101, 102, 103, 104, 105, 106, 107, 109, 0, 1]
def ix_del5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 70, 71, 72, 73, 74, 75, 76, 77, 78, 90, 91, 92, 93, 94, 95, 96, 97, 98, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 70, 71, 72, 73, 74, 75, 76, 77, 78, 90, 91, 92, 93, 94, 95, 96, 97, 98, 0, 1]
def ix_me_del0 : List ℕ := [21, 23, 25, 26, 27, 28, 30, 32, 33, 34, 35, 37, 39, 40, 41, 42, 44, 46, 47, 48, 49, 51, 53, 54, 55, 56, 58, 60, 61, 62, 21, 23, 25, 26, 27, 28, 30, 32, 33, 34, 35, 37, 39, 40, 41, 42, 44, 46, 47, 48, 49, 51, 53, 54, 55, 56, 58, 60, 61, 62, 21, 23, 25, 26, 27, 28, 30, 32, 33, 34, 35, 37, 39, 40, 41, 42, 44, 46, 47, 48, 49, 51, 53, 54, 55, 56, 58, 60, 61, 62, 21, 23, 25, 26, 27, 28, 30, 32, 33, 34, 35, 37, 39, 40, 41, 42, 44, 46, 47, 48, 49, 51, 53, 54, 55, 56, 58, 60, 61, 62, 21, 23, 25, 26, 27, 28, 30, 32]
def ix_me_del1 : List ℕ := [0, 1, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 18, 19, 20, 42, 43, 46, 47, 48, 49, 50, 53, 54, 55, 56, 57, 60, 61, 62, 0, 1, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 18, 19, 20, 42, 43, 46, 47, 48, 49, 50, 53, 54, 55, 56, 57, 60, 61, 62, 0, 1, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 18, 19, 20, 42, 43, 46, 47, 48, 49, 50, 53, 54, 55, 56, 57, 60, 61, 62, 0, 1, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 18, 19, 20, 42, 43, 46, 47, 48, 49, 50, 53, 54, 55, 56, 57, 60, 61, 62, 0, 1, 4, 5, 6, 7, 8, 11]
def ix_mp3_del1 : List ℕ := [0, 1, 4, 6, 7, 8, 9, 12, 14, 15, 16, 17, 20, 22, 23, 40, 41, 44, 46, 47, 48, 49, 52, 54, 55, 56, 57, 60, 62, 63, 0, 1, 4, 6, 7, 8, 9, 12, 14, 15, 16, 17, 20, 22, 23, 40, 41, 44, 46, 47, 48, 49, 52, 54, 55, 56, 57, 60, 62, 63, 0, 1, 4, 6, 7, 8, 9, 12, 14, 15, 16, 17, 20, 22, 23, 40, 41, 44, 46, 47, 48, 49, 52, 54, 55, 56, 57, 60, 62, 63, 0, 1, 4, 6, 7, 8, 9, 12, 14, 15, 16, 17, 20, 22, 23, 40, 41, 44, 46, 47, 48, 49, 52, 54, 55, 56, 57, 60, 62, 63, 0, 1, 4, 6, 7, 8, 9, 12]
def ix_me_sym0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 0, 1]
def ix_me_sym1 : List ℕ := [0, 1, 2, 3, 4, 6, 5, 14, 15, 16, 17, 18, 20, 19, 7, 8, 9, 10, 11, 13, 12, 21, 22, 23, 24, 25, 27, 26, 35, 36, 37, 38, 39, 41, 40, 28, 29, 30, 31, 32, 34, 33, 49, 50, 51, 52, 53, 55, 54, 42, 43, 44, 45, 46, 48, 47, 56, 57, 58, 59, 60, 62, 61, 0, 1, 2, 3, 4, 6, 5, 14, 15, 16, 17, 18, 20, 19, 7, 8, 9, 10, 11, 13, 12, 21, 22, 23, 24, 25, 27, 26, 35, 36, 37, 38, 39, 41, 40, 28, 29, 30, 31, 32, 34, 33, 49, 50, 51, 52, 53, 55, 54, 42, 43, 44, 45, 46, 48, 47, 56, 57, 58, 59, 60, 62, 61, 0, 1]
def ix_me_sym2 : List ℕ := [14, 15, 16, 17, 20, 18, 19, 0, 1, 2, 3, 6, 4, 5, 7, 8, 9, 10, 13, 11, 12, 35, 36, 37, 38, 41, 39, 40, 21, 22, 23, 24, 27, 25, 26, 28, 29, 30, 31, 34, 32, 33, 49, 50, 51, 52, 55, 53, 54, 56, 57, 58, 59, 62, 60, 61, 42, 43, 44, 45, 48, 46, 47, 14, 15, 16, 17, 20, 18, 19, 0, 1, 2, 3, 6, 4, 5, 7, 8, 9, 10, 13, 11, 12, 35, 36, 37, 38, 41, 39, 40, 21, 22, 23, 24, 27, 25, 26, 28, 29, 30, 31, 34, 32, 33, 49, 50, 51, 52, 55, 53, 54, 56, 57, 58, 59, 62, 60, 61, 42, 43, 44, 45, 48, 46, 47, 14, 15]
def ix_me_sym3 : List ℕ := [14, 15, 16, 17, 20, 19, 18, 7, 8, 9, 10, 13, 12, 11, 0, 1, 2, 3, 6, 5, 4, 35, 36, 37, 38, 41, 40, 39, 28, 29, 30, 31, 34, 33, 32, 21, 22, 23, 24, 27, 26, 25, 56, 57, 58, 59, 62, 61, 60, 49, 50, 51, 52, 55, 54, 53, 42, 43, 44, 45, 48, 47, 46, 14, 15, 16, 17, 20, 19, 18, 7, 8, 9, 10, 13, 12, 11, 0, 1, 2, 3, 6, 5, 4, 35, 36, 37, 38, 41, 40, 39, 28, 29, 30, 31, 34, 33, 32, 21, 22, 23, 24, 27, 26, 25, 56, 57, 58, 59, 62, 61, 60, 49, 50, 51, 52, 55, 54, 53, 42, 43, 44, 45, 48, 47, 46, 14, 15]
def ix_me_sym4 : List ℕ := [7, 8, 9, 10, 12, 11, 13, 0, 1, 2, 3, 5, 4, 6, 14, 15, 16, 17, 19, 18, 20, 28, 29, 30, 31, 33, 32, 34, 21, 22, 23, 24, 26, 25, 27, 35, 36, 37, 38, 40, 39, 41, 42, 43, 44, 45, 47, 46, 48, 56, 57, 58, 59, 61, 60, 62, 49, 50, 51, 52, 54, 53, 55, 7, 8, 9, 10, 12, 11, 13, 0, 1, 2, 3, 5, 4, 6, 14, 15, 16, 17, 19, 18, 20, 28, 29, 30, 31, 33, 32, 34, 21, 22, 23, 24, 26, 25, 27, 35, 36, 37, 38, 40, 39, 41, 42, 43, 44, 45, 47, 46, 48, 56, 57, 58, 59, 61, 60, 62, 49, 50, 51, 52, 54, 53, 55, 7, 8]
def ix_me_sym5 : List ℕ := [7, 8, 9, 10, 12, 13, 11, 14, 15, 16, 17, 19, 20, 18, 0, 1, 2, 3, 5, 6, 4, 28, 29, 30, 31, 33, 34, 32, 35, 36, 37, 38, 40, 41, 39, 21, 22, 23, 24, 26, 27, 25, 56, 57, 58, 59, 61, 62, 60, 42, 43, 44, 45, 47, 48, 46, 49, 50, 51, 52, 54, 55, 53, 7, 8, 9, 10, 12, 13, 11, 14, 15, 16, 17, 19, 20, 18, 0, 1, 2, 3, 5, 6, 4, 28, 29, 30, 31, 33, 34, 32, 35, 36, 37, 38, 40, 41, 39, 21, 22, 23, 24, 26, 27, 25, 56, 57, 58, 59, 61, 62, 60, 42, 43, 44, 45, 47, 48, 46, 49, 50, 51, 52, 54, 55, 53, 7, 8]
def ix_mp3_sym0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
def ix_mp3_sym1 : List ℕ := [0, 4, 2, 5, 1, 3, 6, 7, 40, 44, 42, 45, 41, 43, 46, 47, 48, 52, 50, 53, 49, 51, 54, 55, 24, 28, 26, 29, 25, 27, 30, 31, 32, 36, 34, 37, 33, 35, 38, 39, 8, 12, 10, 13, 9, 11, 14, 15, 16, 20, 18, 21, 17, 19, 22, 23, 56, 60, 58, 61, 57, 59, 62, 63, 0, 4, 2, 5, 1, 3, 6, 7, 40, 44, 42, 45, 41, 43, 46, 47, 48, 52, 50, 53, 49, 51, 54, 55, 24, 28, 26, 29, 25, 27, 30, 31, 32, 36, 34, 37, 33, 35, 38, 39, 8, 12, 10, 13, 9, 11, 14, 15, 16, 20, 18, 21, 17, 19, 22, 23, 56, 60, 58, 61, 57, 59, 62, 63]
def ix_mp3_sym2 : List ℕ := [0, 1, 2, 3, 4, 5, 7, 6, 16, 17, 18, 19, 20, 21, 23, 22, 8, 9, 10, 11, 12, 13, 15, 14, 32, 33, 34, 35, 36, 37, 39, 38, 24, 25, 26, 27, 28, 29, 31, 30, 48, 49, 50, 51, 52, 53, 55, 54, 40, 41, 42, 43, 44, 45, 47, 46, 56, 57, 58, 59, 60, 61, 63, 62, 0, 1, 2, 3, 4, 5, 7, 6, 16, 17, 18, 19, 20, 21, 23, 22, 8, 9, 10, 11, 12, 13, 15, 14, 32, 33, 34, 35, 36, 37, 39, 38, 24, 25, 26, 27, 28, 29, 31, 30, 48, 49, 50, 51, 52, 53, 55, 54, 40, 41, 42, 43, 44, 45, 47, 46, 56, 57, 58, 59, 60, 61, 63, 62]
def ix_mp3_sym3 : List ℕ := [0, 4, 2, 5, 1, 3, 7, 6, 48, 52, 50, 53, 49, 51, 55, 54, 40, 44, 42, 45, 41, 43, 47, 46, 32, 36, 34, 37, 33, 35, 39, 38, 24, 28, 26, 29, 25, 27, 31, 30, 16, 20, 18, 21, 17, 19, 23, 22, 8, 12, 10, 13, 9, 11, 15, 14, 56, 60, 58, 61, 57, 59, 63, 62, 0, 4, 2, 5, 1, 3, 7, 6, 48, 52, 50, 53, 49, 51, 55, 54, 40, 44, 42, 45, 41, 43, 47, 46, 32, 36, 34, 37, 33, 35, 39, 38, 24, 28, 26, 29, 25, 27, 31, 30, 16, 20, 18, 21, 17, 19, 23, 22, 8, 12, 10, 13, 9, 11, 15, 14, 56, 60, 58, 61, 57, 59, 63, 62]

theorem spec_g2 : ∀ j : Fin 256,
    Nat.testBit 0xfffffffefffeeea0 (∑ i : Fin 6, if (ins_g2.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by
  decide +kernel

theorem mem_ops_ones {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hone : x = ~~~0 ∨ y = ~~~0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : W) := .inl rfl
  have h1 : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have hand1 (v : W) : v &&& (~~~(0 : W)) = v :=
    (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 256))).trans BitVec.and_allOnes
  have h1and (v : W) : (~~~(0 : W)) &&& v = v := (BitVec.and_comm _ _).trans (hand1 v)
  have hor1 (v : W) : v ||| (~~~(0 : W)) = ~~~(0 : W) := by
    change v ||| ~~~0#256 = ~~~0#256
    rw [BitVec.not_zero, BitVec.or_allOnes]
  have h1or (v : W) : (~~~(0 : W)) ||| v = ~~~(0 : W) := (BitVec.or_comm _ _).trans (hor1 v)
  have hand0 (v : W) : v &&& (0 : W) = 0 := BitVec.and_zero
  have hnot1 : ~~~(~~~(0 : W)) = 0 := BitVec.not_not
  rcases hone with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl
  · rwa [h1and]
  · rw [h1or]; exact h1
  · rw [h1and]; exact holds_not hy
  · rw [hnot1, hand0]; exact h0
  · rwa [hand1]
  · rw [hor1]; exact h1
  · rw [hnot1, hand0]; exact h0
  · rw [h1and]; exact holds_not hx

theorem mem_ops_same {av : Finset W} {a x y z : W} (ha : a ∈ av)
    (hx : x = a ∨ x = ~~~a) (hy : y = a ∨ y = ~~~a) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have h0 : holds av (0 : W) := .inl rfl
  have h1 : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have hpa : holds av a := .inr (.inr ⟨a, ha, .inl rfl⟩)
  have hna : holds av (~~~a) := .inr (.inr ⟨a, ha, .inr rfl⟩)
  have haor : a ||| ~~~a = ~~~(0 : W) := by
    change a ||| ~~~a = ~~~0#256; rw [BitVec.or_not_self, BitVec.not_zero]
  have hnao : ~~~a ||| a = ~~~(0 : W) := by
    change ~~~a ||| a = ~~~0#256; rw [BitVec.not_or_self, BitVec.not_zero]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.and_self, BitVec.or_self, BitVec.and_not_self, BitVec.not_and_self, BitVec.not_not, haor, hnao] <;>
    assumption

def mapRow (ix : List ℕ) (j : Fin 256) : Fin 256 :=
  ⟨((if j.val < 128 then 0 else 128) + ix.getD (j.val % 128) 0) % 256,
    Nat.mod_lt _ (by decide)⟩

def proj (ix : List ℕ) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 256 => w[(mapRow ix k).val]))).cast List.length_ofFn

theorem proj_bit (ix : List ℕ) (w : W) (j : ℕ) (hj : j < 256) :
    (proj ix w)[j] = w[(mapRow ix ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [proj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem proj_not (ix : List ℕ) (u : W) : proj ix (~~~u) = ~~~proj ix u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [proj_bit, BitVec.getElem_not]

theorem proj_and (ix : List ℕ) (u v : W) : proj ix (u &&& v) = proj ix u &&& proj ix v :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [proj_bit, BitVec.getElem_and]

theorem proj_or (ix : List ℕ) (u v : W) : proj ix (u ||| v) = proj ix u ||| proj ix v :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [proj_bit, BitVec.getElem_or]

theorem proj_ops (ix : List ℕ) (a b z : W) (hz : z ∈ basicOps a b) :
    proj ix z ∈ basicOps (proj ix a) (proj ix b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [proj_and, proj_or, proj_not]

theorem proj_ops_getD (ix : List ℕ) (a b : W) (o : Fin 4) :
    proj ix ((ops a b).getD o.val 0) = (ops (proj ix a) (proj ix b)).getD o.val 0 := by
  fin_cases o <;> simp [ops, proj_and, proj_or, proj_not]

theorem goal_bit_spec : ∀ m : Fin 256, goal[m.val] = decide (128 ≤ m.val) := by decide +kernel

theorem proj_goal_of_lt (ix : List ℕ) (hlt : ∀ j : Fin 128, ix.getD j.val 0 < 128) :
    proj ix goal = goal := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [proj_bit ix goal j hj]
  have hltj : ix.getD (j % 128) 0 < 128 := hlt ⟨j % 128, Nat.mod_lt _ (by decide)⟩
  have h1 := goal_bit_spec ⟨j, hj⟩
  have h2 := goal_bit_spec (mapRow ix ⟨j, hj⟩)
  dsimp only at h1 h2
  rw [h1, h2]
  dsimp only [mapRow]
  by_cases h128 : j < 128
  · simp only [h128, ite_true]
    exact decide_eq_decide.mpr (by omega)
  · simp only [h128, ite_false]
    exact decide_eq_decide.mpr (by omega)

theorem sb_reject {k : ℕ} {ws : List W} (hnd : ws.Nodup) (hno : search k ws = false)
    {t : W} (ht : t = goal ∨ t = ~~~goal) (hsb : SignedBuild k ws.toFinset t) : False := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have opposite : ~~~t = goal ∨ ~~~t = ~~~goal := by rcases ht with rfl | rfl <;> simp
  have no {u : W} (hu : u = goal ∨ u = ~~~goal) (run : build basicOps u k ws.toFinset) : False :=
    Bool.noConfusion (hno.symm.trans (search_complete hu k ws hnd run))
  rcases hsb with c | c | run | run
  · rcases ht with rfl | rfl
    · exact ne.1 c
    · exact ne.2.2.1 c
  · rcases ht with rfl | rfl
    · exact ne.2.1 c
    · exact ne.2.2.2 c
  · exact no ht run
  · exact no opposite run

theorem sb_reject_proj (ix : List ℕ) (hgoal : proj ix goal = goal) {k : ℕ} {ws : List W}
    (hnd : ws.Nodup) (hno : search k ws = false) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (hsb : SignedBuild k ws.toFinset (proj ix t)) : False := by
  have ht' : proj ix t = goal ∨ proj ix t = ~~~goal := by
    rcases ht with rfl | rfl
    · exact .inl hgoal
    · exact .inr (by rw [proj_not, hgoal])
  exact sb_reject hnd hno ht' hsb

theorem proj_goal_ix (ix : List ℕ) (h : ∀ j : Fin 128, ix.getD j.val 0 < 128) : proj ix goal = goal :=
  proj_goal_of_lt ix h

def g2in (i : Fin 6) : W := ins_g2.getD i.val 0
def meIn (i : Fin 5) : W := ins_k5me.getD i.val 0
def mp3In (i : Fin 5) : W := ins_k5mp3.getD i.val 0
def mp4In (i : Fin 5) : W := ins_k5mp4.getD i.val 0
def op45 (o : Fin 4) : W := (ops (g2in 4) (g2in 5)).getD o.val 0
def meOp34 (o : Fin 4) : W := (ops (meIn 3) (meIn 4)).getD o.val 0
def mp3Op02 (o : Fin 4) : W := (ops (mp3In 0) (mp3In 2)).getD o.val 0
def mp3Op03 (o : Fin 4) : W := (ops (mp3In 0) (mp3In 3)).getD o.val 0
def mp3Op34 (o : Fin 4) : W := (ops (mp3In 3) (mp3In 4)).getD o.val 0

def changes (w : W) (r : Fin 128) : Bool := w.getLsbD (128 + r.val) != w.getLsbD r.val

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) : ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

theorem unchanged (w : W) (r : Fin 128) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem goal_changes : ∀ k : Fin 128, differs k goal ∧ differs k (~~~goal) := by
  unfold differs; decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4_no6 : search 6 ins_k4 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp4_no6 : search 6 ins_k5mp4 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_op34_no6_0 : search 6 (ins_k5me ++ [meOp34 0]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_op34_no6_1 : search 6 (ins_k5me ++ [meOp34 1]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_op34_no6_2 : search 6 (ins_k5me ++ [meOp34 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op02_no6_0 : search 6 (ins_k5mp3 ++ [mp3Op02 0]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op02_no6_1 : search 6 (ins_k5mp3 ++ [mp3Op02 1]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op02_no6_2 : search 6 (ins_k5mp3 ++ [mp3Op02 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op03_no6_0 : search 6 (ins_k5mp3 ++ [mp3Op03 0]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op03_no6_1 : search 6 (ins_k5mp3 ++ [mp3Op03 1]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op03_no6_2 : search 6 (ins_k5mp3 ++ [mp3Op03 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op03_no6_3 : search 6 (ins_k5mp3 ++ [mp3Op03 3]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op34_no6_0 : search 6 (ins_k5mp3 ++ [mp3Op34 0]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op34_no6_1 : search 6 (ins_k5mp3 ++ [mp3Op34 1]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_op34_no6_2 : search 6 (ins_k5mp3 ++ [mp3Op34 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_2ops_no5_01 : search 5 (ins_k5me ++ [meOp34 0, meOp34 1]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_2ops_no5_01 : search 5 (ins_k5mp3 ++ [mp3Op34 0, mp3Op34 1]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_2ops_no5_02 : search 5 (ins_k5me ++ [meOp34 0, meOp34 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_2ops_no5_02 : search 5 (ins_k5mp3 ++ [mp3Op34 0, mp3Op34 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_2ops_no5_12 : search 5 (ins_k5me ++ [meOp34 1, meOp34 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_2ops_no5_12 : search 5 (ins_k5mp3 ++ [mp3Op34 1, mp3Op34 2]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5me_2ops_no5_23 : search 5 (ins_k5me ++ [meOp34 2, meOp34 3]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k5mp3_2ops_no5_23 : search 5 (ins_k5mp3 ++ [mp3Op34 2, mp3Op34 3]) = false := by decide +kernel


theorem k4_nd : ins_k4.Nodup := by decide +kernel
theorem k5mp4_nd : ins_k5mp4.Nodup := by decide +kernel
theorem k5me_op34_nd : ∀ o : Fin 4, (ins_k5me ++ [meOp34 o]).Nodup := by decide +kernel
theorem k5mp3_op02_nd : ∀ o : Fin 4, (ins_k5mp3 ++ [mp3Op02 o]).Nodup := by decide +kernel
theorem k5mp3_op03_nd : ∀ o : Fin 4, (ins_k5mp3 ++ [mp3Op03 o]).Nodup := by decide +kernel
theorem k5mp3_op34_nd : ∀ o : Fin 4, (ins_k5mp3 ++ [mp3Op34 o]).Nodup := by decide +kernel
theorem k5me_2ops_nd : ∀ o1 o2 : Fin 4, o1 ≠ o2 → (ins_k5me ++ [meOp34 o1, meOp34 o2]).Nodup := by decide +kernel
theorem k5mp3_2ops_nd : ∀ o1 o2 : Fin 4, o1 ≠ o2 → (ins_k5mp3 ++ [mp3Op34 o1, mp3Op34 o2]).Nodup := by decide +kernel

theorem ix_lt_128 :
    (∀ j : Fin 128, ix_del0.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_del1.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_del2.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_del3.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_del4.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_del5.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_del0.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_del1.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_mp3_del1.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_sym0.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_sym1.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_sym2.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_sym3.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_sym4.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_me_sym5.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_mp3_sym0.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_mp3_sym1.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_mp3_sym2.getD j.val 0 < 128) ∧
    (∀ j : Fin 128, ix_mp3_sym3.getD j.val 0 < 128) := by decide +kernel

theorem me_index : ∀ w ∈ ins_k5me, ∃ i : Fin 5, meIn i = w := by
  intro w hw
  simp only [ins_k5me, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩

theorem mp3_index : ∀ w ∈ ins_k5mp3, ∃ i : Fin 5, mp3In i = w := by
  intro w hw
  simp only [ins_k5mp3, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩

theorem g2_index : ∀ w ∈ ins_g2, ∃ i : Fin 6, g2in i = w := by
  intro w hw
  simp only [ins_g2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩

theorem me_not_goal : ∀ i : Fin 5, meIn i ≠ goal ∧ meIn i ≠ ~~~goal := by decide +kernel
theorem mp3_not_goal : ∀ i : Fin 5, mp3In i ≠ goal ∧ mp3In i ≠ ~~~goal := by decide +kernel
theorem g2_not_goal : ∀ i : Fin 6, g2in i ≠ goal ∧ g2in i ≠ ~~~goal := by decide +kernel
theorem op45_not_goal : ∀ o : Fin 4, op45 o ≠ goal ∧ op45 o ≠ ~~~goal := by decide +kernel

set_option maxRecDepth 8000 in
theorem me_del0_maps : proj ix_me_del0 (meIn 0) = 0 ∧ ∀ i : Fin 5, i ≠ 0 → proj ix_me_del0 (meIn i) ∈ ins_k4 := by decide +kernel
set_option maxRecDepth 8000 in
theorem me_del1_maps : proj ix_me_del1 (meIn 1) = 0 ∧ ∀ i : Fin 5, i ≠ 1 → proj ix_me_del1 (meIn i) ∈ ins_k4 := by decide +kernel
set_option maxRecDepth 8000 in
theorem mp3_del1_maps : proj ix_mp3_del1 (mp3In 1) = 0 ∧ ∀ i : Fin 5, i ≠ 1 → proj ix_mp3_del1 (mp3In i) ∈ ins_k4 := by decide +kernel

def meSymIx : Fin 6 → List ℕ
  | ⟨0, _⟩ => ix_me_sym0
  | ⟨1, _⟩ => ix_me_sym1
  | ⟨2, _⟩ => ix_me_sym2
  | ⟨3, _⟩ => ix_me_sym3
  | ⟨4, _⟩ => ix_me_sym4
  | ⟨5, _⟩ => ix_me_sym5

def mp3SymIx : Fin 4 → List ℕ
  | ⟨0, _⟩ => ix_mp3_sym0
  | ⟨1, _⟩ => ix_mp3_sym1
  | ⟨2, _⟩ => ix_mp3_sym2
  | ⟨3, _⟩ => ix_mp3_sym3

set_option maxRecDepth 16000 in
theorem me_sym_pres : ∀ s : Fin 6, ∀ i : Fin 5, proj (meSymIx s) (meIn i) ∈ ins_k5me := by decide +kernel
set_option maxRecDepth 16000 in
theorem mp3_sym_pres : ∀ s : Fin 4, ∀ i : Fin 5, proj (mp3SymIx s) (mp3In i) ∈ ins_k5mp3 := by decide +kernel

theorem me_sym_goal (s : Fin 6) : proj (meSymIx s) goal = goal := by
  fin_cases s
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mp3_sym_goal (s : Fin 4) : proj (mp3SymIx s) goal = goal := by
  fin_cases s
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option maxRecDepth 16000 in
theorem me_op_orbit : ∀ u v : Fin 5, 2 ≤ u.val → 2 ≤ v.val → u ≠ v → ∀ o : Fin 4,
    ∃ (s : Fin 6) (o' : Fin 3), proj (meSymIx s) ((ops (meIn u) (meIn v)).getD o.val 0) = meOp34 ⟨o'.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem mp3_op_orbit : ∀ u v : Fin 5, u.val ≠ 1 → v.val ≠ 1 → u ≠ v → ∀ o : Fin 4,
    (∃ (s : Fin 4) (o' : Fin 3), proj (mp3SymIx s) ((ops (mp3In u) (mp3In v)).getD o.val 0) = mp3Op02 ⟨o'.val, by omega⟩) ∨
    (∃ (s : Fin 4) (o' : Fin 4), proj (mp3SymIx s) ((ops (mp3In u) (mp3In v)).getD o.val 0) = mp3Op03 o') ∨
    (∃ (s : Fin 4) (o' : Fin 3), proj (mp3SymIx s) ((ops (mp3In u) (mp3In v)).getD o.val 0) = mp3Op34 ⟨o'.val, by omega⟩) := by
  decide +kernel

theorem me_op34_no6_all (o : Fin 3) : search 6 (ins_k5me ++ [meOp34 ⟨o.val, by omega⟩]) = false := by
  fin_cases o
  · exact k5me_op34_no6_0
  · exact k5me_op34_no6_1
  · exact k5me_op34_no6_2

theorem mp3_op02_no6_all (o : Fin 3) : search 6 (ins_k5mp3 ++ [mp3Op02 ⟨o.val, by omega⟩]) = false := by
  fin_cases o
  · exact k5mp3_op02_no6_0
  · exact k5mp3_op02_no6_1
  · exact k5mp3_op02_no6_2

theorem mp3_op03_no6_all (o : Fin 4) : search 6 (ins_k5mp3 ++ [mp3Op03 o]) = false := by
  fin_cases o
  · exact k5mp3_op03_no6_0
  · exact k5mp3_op03_no6_1
  · exact k5mp3_op03_no6_2
  · exact k5mp3_op03_no6_3

theorem mp3_op34_no6_all (o : Fin 3) : search 6 (ins_k5mp3 ++ [mp3Op34 ⟨o.val, by omega⟩]) = false := by
  fin_cases o
  · exact k5mp3_op34_no6_0
  · exact k5mp3_op34_no6_1
  · exact k5mp3_op34_no6_2

theorem k5me_op_no6 {k : ℕ} (hk : k ≤ 6) (u v : Fin 5) (hu : 2 ≤ u.val) (hv : 2 ≤ v.val) (hne : u ≠ v)
    (o : Fin 4) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t k (insert ((ops (meIn u) (meIn v)).getD o.val 0) ins_k5me.toFinset)) : False := by
  obtain ⟨s, o', heq⟩ := me_op_orbit u v hu hv hne o
  obtain ⟨st, hst, hl⟩ := compress run
  apply sb_reject_proj (meSymIx s) (me_sym_goal s) (k5me_op34_nd ⟨o'.val, by omega⟩) (me_op34_no6_all o') ht
  apply sb_le hk
  apply live_transport (proj_ops (meSymIx s)) hl
  intro w hw
  rcases Finset.mem_insert.mp (hst hw) with rfl | hmem
  · exact .inr (.inr ⟨_, by rw [heq]; simp, .inl rfl⟩)
  · obtain ⟨i, rfl⟩ := me_index _ (List.mem_toFinset.mp hmem)
    exact .inr (.inr ⟨_, by simp [me_sym_pres s i], .inl rfl⟩)

theorem k5mp3_op_no6 {k : ℕ} (hk : k ≤ 6) (u v : Fin 5) (hu : u.val ≠ 1) (hv : v.val ≠ 1) (hne : u ≠ v)
    (o : Fin 4) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t k (insert ((ops (mp3In u) (mp3In v)).getD o.val 0) ins_k5mp3.toFinset)) : False := by
  obtain ⟨st, hst, hl⟩ := compress run
  rcases mp3_op_orbit u v hu hv hne o with ⟨s, o', heq⟩ | ⟨s, o', heq⟩ | ⟨s, o', heq⟩
  · apply sb_reject_proj (mp3SymIx s) (mp3_sym_goal s) (k5mp3_op02_nd ⟨o'.val, by omega⟩) (mp3_op02_no6_all o') ht
    apply sb_le hk
    apply live_transport (proj_ops (mp3SymIx s)) hl
    intro w hw
    rcases Finset.mem_insert.mp (hst hw) with rfl | hmem
    · exact .inr (.inr ⟨_, by rw [heq]; simp, .inl rfl⟩)
    · obtain ⟨i, rfl⟩ := mp3_index _ (List.mem_toFinset.mp hmem)
      exact .inr (.inr ⟨_, by simp [mp3_sym_pres s i], .inl rfl⟩)
  · apply sb_reject_proj (mp3SymIx s) (mp3_sym_goal s) (k5mp3_op03_nd o') (mp3_op03_no6_all o') ht
    apply sb_le hk
    apply live_transport (proj_ops (mp3SymIx s)) hl
    intro w hw
    rcases Finset.mem_insert.mp (hst hw) with rfl | hmem
    · exact .inr (.inr ⟨_, by rw [heq]; simp, .inl rfl⟩)
    · obtain ⟨i, rfl⟩ := mp3_index _ (List.mem_toFinset.mp hmem)
      exact .inr (.inr ⟨_, by simp [mp3_sym_pres s i], .inl rfl⟩)
  · apply sb_reject_proj (mp3SymIx s) (mp3_sym_goal s) (k5mp3_op34_nd ⟨o'.val, by omega⟩) (mp3_op34_no6_all o') ht
    apply sb_le hk
    apply live_transport (proj_ops (mp3SymIx s)) hl
    intro w hw
    rcases Finset.mem_insert.mp (hst hw) with rfl | hmem
    · exact .inr (.inr ⟨_, by rw [heq]; simp, .inl rfl⟩)
    · obtain ⟨i, rfl⟩ := mp3_index _ (List.mem_toFinset.mp hmem)
      exact .inr (.inr ⟨_, by simp [mp3_sym_pres s i], .inl rfl⟩)

theorem k5me_no7 (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t 7 ins_k5me.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 6) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := me_index t (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl | rfl
    · exact (me_not_goal i).1 hi
    · exact (me_not_goal i).2 hi
  · obtain ⟨u, rfl⟩ := me_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨v, rfl⟩ := me_index _ (List.mem_toFinset.mp (hs hb))
    have huv : u ≠ v := fun e => hab (congrArg meIn e)
    have sub : rest ⊆ ins_k5me.toFinset := fun x hx =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    by_cases h0 : u = 0 ∨ v = 0
    · apply sb_reject_proj ix_me_del0 (proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.1) k4_nd k4_no6 ht
      apply live_transport (proj_ops ix_me_del0) tail
      have hav : ∀ i : Fin 5, holds ins_k4.toFinset (proj ix_me_del0 (meIn i)) := fun i => by
        by_cases hi : i = 0
        · subst hi; exact .inl me_del0_maps.1
        · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (me_del0_maps.2 i hi), .inl rfl⟩)
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact mem_ops_zero (hav u) (hav v) (h0.imp (fun h => by rw [h]; exact me_del0_maps.1) (fun h => by rw [h]; exact me_del0_maps.1))
          (proj_ops ix_me_del0 _ _ _ hz)
      · obtain ⟨i, rfl⟩ := me_index _ (List.mem_toFinset.mp (sub hw))
        exact hav i
    · by_cases h1 : u = 1 ∨ v = 1
      · apply sb_reject_proj ix_me_del1 (proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.1) k4_nd k4_no6 ht
        apply live_transport (proj_ops ix_me_del1) tail
        have hav : ∀ i : Fin 5, holds ins_k4.toFinset (proj ix_me_del1 (meIn i)) := fun i => by
          by_cases hi : i = 1
          · subst hi; exact .inl me_del1_maps.1
          · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (me_del1_maps.2 i hi), .inl rfl⟩)
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact mem_ops_zero (hav u) (hav v) (h1.imp (fun h => by rw [h]; exact me_del1_maps.1) (fun h => by rw [h]; exact me_del1_maps.1))
            (proj_ops ix_me_del1 _ _ _ hz)
        · obtain ⟨i, rfl⟩ := me_index _ (List.mem_toFinset.mp (sub hw))
          exact hav i
      · have hu2 : 2 ≤ u.val := by
          have : u ≠ 0 := fun e => h0 (.inl e)
          have : u ≠ 1 := fun e => h1 (.inl e)
          omega
        have hv2 : 2 ≤ v.val := by
          have : v ≠ 0 := fun e => h0 (.inr e)
          have : v ≠ 1 := fun e => h1 (.inr e)
          omega
        obtain ⟨o, rfl⟩ := index_of_op _ _ _ hz
        have hsb : SignedBuild 6 (insert ((ops (meIn u) (meIn v)).getD o.val 0) ins_k5me.toFinset) t :=
          live_transport (f := id) (fun _ _ _ h => h) tail (fun w hw => by
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact .inr (.inr ⟨_, Finset.mem_insert_self .., .inl rfl⟩)
            · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (sub hw), .inl rfl⟩))
        have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
        rcases hsb with c | c | r | r
        · rcases ht with rfl | rfl <;> [exact ne.1 c; exact ne.2.2.1 c]
        · rcases ht with rfl | rfl <;> [exact ne.2.1 c; exact ne.2.2.2 c]
        · exact k5me_op_no6 (le_refl 6) u v hu2 hv2 huv o ht r
        · exact k5me_op_no6 (le_refl 6) u v hu2 hv2 huv o (by rcases ht with rfl | rfl <;> simp) r

theorem k5mp3_no7 (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t 7 ins_k5mp3.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 6) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := mp3_index t (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl | rfl
    · exact (mp3_not_goal i).1 hi
    · exact (mp3_not_goal i).2 hi
  · obtain ⟨u, rfl⟩ := mp3_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨v, rfl⟩ := mp3_index _ (List.mem_toFinset.mp (hs hb))
    have huv : u ≠ v := fun e => hab (congrArg mp3In e)
    have sub : rest ⊆ ins_k5mp3.toFinset := fun x hx =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    by_cases h1 : u = 1 ∨ v = 1
    · apply sb_reject_proj ix_mp3_del1 (proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.2.2.2.1) k4_nd k4_no6 ht
      apply live_transport (proj_ops ix_mp3_del1) tail
      have hav : ∀ i : Fin 5, holds ins_k4.toFinset (proj ix_mp3_del1 (mp3In i)) := fun i => by
        by_cases hi : i = 1
        · subst hi; exact .inl mp3_del1_maps.1
        · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (mp3_del1_maps.2 i hi), .inl rfl⟩)
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact mem_ops_zero (hav u) (hav v) (h1.imp (fun h => by rw [h]; exact mp3_del1_maps.1) (fun h => by rw [h]; exact mp3_del1_maps.1))
          (proj_ops ix_mp3_del1 _ _ _ hz)
      · obtain ⟨i, rfl⟩ := mp3_index _ (List.mem_toFinset.mp (sub hw))
        exact hav i
    · have hu1 : u.val ≠ 1 := fun e => h1 (.inl (Fin.ext e))
      have hv1 : v.val ≠ 1 := fun e => h1 (.inr (Fin.ext e))
      obtain ⟨o, rfl⟩ := index_of_op _ _ _ hz
      have hsb : SignedBuild 6 (insert ((ops (mp3In u) (mp3In v)).getD o.val 0) ins_k5mp3.toFinset) t :=
        live_transport (f := id) (fun _ _ _ h => h) tail (fun w hw => by
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact .inr (.inr ⟨_, Finset.mem_insert_self .., .inl rfl⟩)
          · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (sub hw), .inl rfl⟩))
      have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
      rcases hsb with c | c | r | r
      · rcases ht with rfl | rfl <;> [exact ne.1 c; exact ne.2.2.1 c]
      · rcases ht with rfl | rfl <;> [exact ne.2.1 c; exact ne.2.2.2 c]
      · exact k5mp3_op_no6 (le_refl 6) u v hu1 hv1 huv o ht r
      · exact k5mp3_op_no6 (le_refl 6) u v hu1 hv1 huv o (by rcases ht with rfl | rfl <;> simp) r

theorem k5me_no7_sb {k : ℕ} (hk : k ≤ 7) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (hsb : SignedBuild k ins_k5me.toFinset t) : False := by
  have hsb7 := sb_le hk hsb
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  rcases hsb7 with c | c | r | r
  · rcases ht with rfl | rfl <;> [exact ne.1 c; exact ne.2.2.1 c]
  · rcases ht with rfl | rfl <;> [exact ne.2.1 c; exact ne.2.2.2 c]
  · exact k5me_no7 t ht r
  · exact k5me_no7 (~~~t) (by rcases ht with rfl | rfl <;> simp) r

theorem k5mp3_no7_sb {k : ℕ} (hk : k ≤ 7) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (hsb : SignedBuild k ins_k5mp3.toFinset t) : False := by
  have hsb7 := sb_le hk hsb
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  rcases hsb7 with c | c | r | r
  · rcases ht with rfl | rfl <;> [exact ne.1 c; exact ne.2.2.1 c]
  · rcases ht with rfl | rfl <;> [exact ne.2.1 c; exact ne.2.2.2 c]
  · exact k5mp3_no7 t ht r
  · exact k5mp3_no7 (~~~t) (by rcases ht with rfl | rfl <;> simp) r

set_option maxRecDepth 8000 in
theorem me_2ops_orbit : ∀ o1 o2 : Fin 4, o1 ≠ o2 →
    ∃ s : Fin 2, ∃ a b : Fin 4, ((a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3)) ∧
      proj (meSymIx ⟨s.val, by omega⟩) (meOp34 o1) ∈ [meOp34 a, meOp34 b] ∧
      proj (meSymIx ⟨s.val, by omega⟩) (meOp34 o2) ∈ [meOp34 a, meOp34 b] := by decide +kernel

set_option maxRecDepth 8000 in
theorem mp3_2ops_orbit : ∀ o1 o2 : Fin 4, o1 ≠ o2 →
    ∃ s : Fin 4, ∃ a b : Fin 4, ((a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3)) ∧
      proj (mp3SymIx s) (mp3Op34 o1) ∈ [mp3Op34 a, mp3Op34 b] ∧
      proj (mp3SymIx s) (mp3Op34 o2) ∈ [mp3Op34 a, mp3Op34 b] := by decide +kernel

theorem k5me_2ops_no5_sb {k : ℕ} (hk : k ≤ 5) (o1 o2 : Fin 4) (hne : o1 ≠ o2) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (hsb : SignedBuild k (insert (meOp34 o2) (insert (meOp34 o1) ins_k5me.toFinset)) t) : False := by
  obtain ⟨s, a, b, hab, h1, h2⟩ := me_2ops_orbit o1 o2 hne
  have hno : search 5 (ins_k5me ++ [meOp34 a, meOp34 b]) = false := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact k5me_2ops_no5_01
    · exact k5me_2ops_no5_02
    · exact k5me_2ops_no5_12
    · exact k5me_2ops_no5_23
  have hab_ne : a ≠ b := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have go {u : W} (hu : u = goal ∨ u = ~~~goal)
      (run : build basicOps u 5 (insert (meOp34 o2) (insert (meOp34 o1) ins_k5me.toFinset))) : False := by
    obtain ⟨st, hst, hl⟩ := compress run
    apply sb_reject_proj (meSymIx ⟨s.val, by omega⟩) (me_sym_goal ⟨s.val, by omega⟩) (k5me_2ops_nd a b hab_ne) hno hu
    apply live_transport (proj_ops (meSymIx ⟨s.val, by omega⟩)) hl
    intro w hw
    rcases Finset.mem_insert.mp (hst hw) with rfl | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 <;> exact .inr (.inr ⟨_, by simp [h2], .inl rfl⟩)
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases h1 with h1 | h1 <;> exact .inr (.inr ⟨_, by simp [h1], .inl rfl⟩)
      · obtain ⟨i, rfl⟩ := me_index _ (List.mem_toFinset.mp hw)
        exact .inr (.inr ⟨_, by simp [me_sym_pres ⟨s.val, by omega⟩ i], .inl rfl⟩)
  rcases sb_le hk hsb with c | c | r | r
  · rcases ht with rfl | rfl <;> [exact ne.1 c; exact ne.2.2.1 c]
  · rcases ht with rfl | rfl <;> [exact ne.2.1 c; exact ne.2.2.2 c]
  · exact go ht r
  · exact go (by rcases ht with rfl | rfl <;> simp) r

theorem k5mp3_2ops_no5_sb {k : ℕ} (hk : k ≤ 5) (o1 o2 : Fin 4) (hne : o1 ≠ o2) {t : W} (ht : t = goal ∨ t = ~~~goal)
    (hsb : SignedBuild k (insert (mp3Op34 o2) (insert (mp3Op34 o1) ins_k5mp3.toFinset)) t) : False := by
  obtain ⟨s, a, b, hab, h1, h2⟩ := mp3_2ops_orbit o1 o2 hne
  have hno : search 5 (ins_k5mp3 ++ [mp3Op34 a, mp3Op34 b]) = false := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact k5mp3_2ops_no5_01
    · exact k5mp3_2ops_no5_02
    · exact k5mp3_2ops_no5_12
    · exact k5mp3_2ops_no5_23
  have hab_ne : a ≠ b := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have go {u : W} (hu : u = goal ∨ u = ~~~goal)
      (run : build basicOps u 5 (insert (mp3Op34 o2) (insert (mp3Op34 o1) ins_k5mp3.toFinset))) : False := by
    obtain ⟨st, hst, hl⟩ := compress run
    apply sb_reject_proj (mp3SymIx s) (mp3_sym_goal s) (k5mp3_2ops_nd a b hab_ne) hno hu
    apply live_transport (proj_ops (mp3SymIx s)) hl
    intro w hw
    rcases Finset.mem_insert.mp (hst hw) with rfl | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with h2 | h2 <;> exact .inr (.inr ⟨_, by rw [h2]; simp, .inl rfl⟩)
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases h1 with h1 | h1 <;> exact .inr (.inr ⟨_, by rw [h1]; simp, .inl rfl⟩)
      · obtain ⟨i, rfl⟩ := mp3_index _ (List.mem_toFinset.mp hw)
        exact .inr (.inr ⟨_, by simp [mp3_sym_pres s i], .inl rfl⟩)
  rcases sb_le hk hsb with c | c | r | r
  · rcases ht with rfl | rfl <;> [exact ne.1 c; exact ne.2.2.1 c]
  · rcases ht with rfl | rfl <;> [exact ne.2.1 c; exact ne.2.2.2 c]
  · exact go ht r
  · exact go (by rcases ht with rfl | rfl <;> simp) r

def delIx : Fin 6 → List ℕ
  | ⟨0, _⟩ => ix_del0
  | ⟨1, _⟩ => ix_del1
  | ⟨2, _⟩ => ix_del2
  | ⟨3, _⟩ => ix_del3
  | ⟨4, _⟩ => ix_del4
  | ⟨5, _⟩ => ix_del5

theorem del_goal (p : Fin 6) : proj (delIx p) goal = goal := by
  fin_cases p
  · exact proj_goal_of_lt _ ix_lt_128.1
  · exact proj_goal_of_lt _ ix_lt_128.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.1
  · exact proj_goal_of_lt _ ix_lt_128.2.2.2.2.2.1

set_option maxRecDepth 16000 in
theorem g2_del_zero : ∀ p : Fin 6, proj (delIx p) (g2in p) = 0 := by decide +kernel

set_option maxRecDepth 16000 in
theorem g2_del03_maps : ∀ p : Fin 6, (p = 0 ∨ p = 3) →
    (∀ i : Fin 6, i ≠ p → proj (delIx p) (g2in i) ∈ ins_k5mp3) ∧
    (∀ o : Fin 4, proj (delIx p) (op45 o) = mp3Op34 o) := by decide +kernel

set_option maxRecDepth 16000 in
theorem g2_del12_maps : ∀ p : Fin 6, (p = 1 ∨ p = 2) →
    (∀ i : Fin 6, i ≠ p → proj (delIx p) (g2in i) ∈ ins_k5me) ∧
    (∀ o : Fin 4, proj (delIx p) (op45 o) = meOp34 o) := by decide +kernel

set_option maxRecDepth 16000 in
theorem g2_del45_maps : ∀ p : Fin 6, (p = 4 ∨ p = 5) →
    (∀ i : Fin 6, i ≠ p → proj (delIx p) (g2in i) ∈ ins_k5mp4) ∧
    proj (delIx p) (op45 0) = 0 ∧
    proj (delIx p) (op45 1) = mp4In 4 ∧
    (proj (delIx p) (op45 2) = 0 ∨ proj (delIx p) (op45 2) = mp4In 4) ∧
    (proj (delIx p) (op45 3) = 0 ∨ proj (delIx p) (op45 3) = mp4In 4) := by
  intro p hp
  rcases hp with rfl | rfl <;> decide +kernel

set_option maxRecDepth 16000 in
theorem op45_del45_zero :
    proj ix_del4 (op45 0) = 0 ∧ proj ix_del4 (op45 2) = 0 ∧ proj ix_del5 (op45 3) = 0 := by decide +kernel

theorem g2_del45_holds (p : Fin 6) (hp : p = 4 ∨ p = 5) :
    (∀ i : Fin 6, holds ins_k5mp4.toFinset (proj (delIx p) (g2in i))) ∧
    (∀ o : Fin 4, holds ins_k5mp4.toFinset (proj (delIx p) (op45 o))) := by
  have hm := g2_del45_maps p hp
  have h4in : mp4In 4 ∈ ins_k5mp4.toFinset := by decide +kernel
  constructor
  · intro i
    by_cases hi : i = p
    · subst hi; exact .inl (g2_del_zero i)
    · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (hm.1 i hi), .inl rfl⟩)
  · intro o
    fin_cases o
    · exact .inl hm.2.1
    · exact .inr (.inr ⟨mp4In 4, h4in, .inl hm.2.2.1⟩)
    · rcases hm.2.2.2.1 with h | h
      · exact .inl h
      · exact .inr (.inr ⟨mp4In 4, h4in, .inl h⟩)
    · rcases hm.2.2.2.2 with h | h
      · exact .inl h
      · exact .inr (.inr ⟨mp4In 4, h4in, .inl h⟩)

theorem g2_del4_only45_holds (o1 o2 : Fin 4) (c d u : W)
    (hc : c = g2in 4 ∨ c = g2in 5 ∨ c = op45 o1 ∨ c = op45 o2)
    (hd : d = g2in 4 ∨ d = g2in 5 ∨ d = op45 o1 ∨ d = op45 o2)
    (hu : u ∈ basicOps c d) : holds ins_k5mp4.toFinset (proj ix_del4 u) := by
  have h4in : mp4In 4 ∈ ins_k5mp4.toFinset := by decide +kernel
  have hspec : ∀ x, (x = g2in 4 ∨ x = g2in 5 ∨ x = op45 o1 ∨ x = op45 o2) →
      proj ix_del4 x = 0 ∨ proj ix_del4 x = mp4In 4 := by
    have h40 : proj ix_del4 (g2in 4) = 0 := g2_del_zero 4
    have h54 : proj ix_del4 (g2in 5) = mp4In 4 := by decide +kernel
    have hm := (g2_del45_maps 4 (.inl rfl)).2
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact .inl h40
    · exact .inr h54
    · fin_cases o1
      · exact .inl hm.1
      · exact .inr hm.2.1
      · exact hm.2.2.1
      · exact hm.2.2.2
    · fin_cases o2
      · exact .inl hm.1
      · exact .inr hm.2.1
      · exact hm.2.2.1
      · exact hm.2.2.2
  have hholds : ∀ x, (proj ix_del4 x = 0 ∨ proj ix_del4 x = mp4In 4) → holds ins_k5mp4.toFinset (proj ix_del4 x) :=
    fun x h => h.elim (fun h0 => .inl h0) (fun h4 => .inr (.inr ⟨mp4In 4, h4in, .inl h4⟩))
  have hc' := hspec c hc
  have hd' := hspec d hd
  have hop := proj_ops ix_del4 c d u hu
  rcases hc' with hc0 | hc4
  · exact mem_ops_zero (hholds c (.inl hc0)) (hholds d hd') (.inl hc0) hop
  · rcases hd' with hd0 | hd4
    · exact mem_ops_zero (hholds c (.inr hc4)) (hholds d (.inl hd0)) (.inr hd0) hop
    · exact mem_ops_same h4in (.inl hc4) (.inl hd4) hop

set_option maxRecDepth 16000 in
theorem op45_closure : ∀ o1 : Fin 4, ∀ a b : Fin 3, a ≠ b → ∀ o : Fin 4,
    let pool : Fin 3 → W := fun k => match k with | ⟨0, _⟩ => g2in 4 | ⟨1, _⟩ => g2in 5 | ⟨2, _⟩ => op45 o1
    let w := (ops (pool a) (pool b)).getD o.val 0
    (w = 0 ∨ w = ~~~0 ∨ ∃ k : Fin 3, w = pool k ∨ w = ~~~pool k) ∨
    (∃ o2 : Fin 4, o2 ≠ o1 ∧ (w = op45 o2 ∨ w = ~~~op45 o2)) := by decide +kernel

def w7 (o1 : Fin 4) (i : Fin 7) : W :=
  if h : i.val < 6 then g2in ⟨i.val, h⟩ else op45 o1

def w8 (o1 o2 : Fin 4) (i : Fin 8) : W :=
  if h : i.val < 6 then g2in ⟨i.val, h⟩ else if i.val = 6 then op45 o1 else op45 o2

theorem w7_eq_g2in (o1 : Fin 4) (c : Fin 7) (p : Fin 6) (h : p.val = c.val) : w7 o1 c = g2in p := by
  have hc : c.val < 6 := by omega
  simp only [w7, hc, dite_true]
  exact congrArg g2in (Fin.ext h.symm)

theorem w8_eq_g2in (o1 o2 : Fin 4) (c : Fin 8) (p : Fin 6) (h : p.val = c.val) : w8 o1 o2 c = g2in p := by
  have hc : c.val < 6 := by omega
  simp only [w8, hc, dite_true]
  exact congrArg g2in (Fin.ext h.symm)

theorem g2in_mem (q : Fin 6) : g2in q ∈ ins_g2.toFinset := by
  rw [List.mem_toFinset]
  have hlen : ins_g2.length = 6 := rfl
  have hq : q.val < ins_g2.length := by omega
  simpa only [g2in, List.getD_eq_getElem _ _ hq] using List.getElem_mem hq

theorem w7_mem_A (o1 : Fin 4) (c : Fin 7) : w7 o1 c ∈ insert (op45 o1) ins_g2.toFinset := by
  unfold w7
  split_ifs with h
  · exact Finset.mem_insert_of_mem (g2in_mem ⟨c.val, h⟩)
  · exact Finset.mem_insert_self ..

theorem w8_mem_A (o1 o2 : Fin 4) (c : Fin 8) : w8 o1 o2 c ∈ insert (op45 o2) (insert (op45 o1) ins_g2.toFinset) := by
  unfold w8
  split_ifs with h1 h2
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (g2in_mem ⟨c.val, h1⟩))
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  · exact Finset.mem_insert_self ..

set_option maxRecDepth 16000 in
theorem sep_pair1 : ∀ i j : Fin 6, i < j → ¬(i = 4 ∧ j = 5) → ∀ o : Fin 4,
    ∃ p : Fin 6, (p = i ∨ p = j) ∧ p.val < 4 ∧
      ∃ r : Fin 128, changes ((ops (g2in i) (g2in j)).getD o.val 0) r = false ∧
        ∀ q : Fin 6, q ≠ p → changes (g2in q) r = false := by decide +kernel

set_option maxRecDepth 16000 in
theorem sep_pair2 : ∀ o1 : Fin 4, ∀ a b : Fin 7, a < b → a.val < 4 → ∀ o : Fin 4,
    (o1 = 0 ∧ b = 6 ∧ (o = 1 ∨ o = 2) ∧
      ∃ r : Fin 128, changes ((ops (w7 o1 a) (w7 o1 b)).getD o.val 0) r = false ∧
        changes (op45 o1) r = false ∧
        ∀ q : Fin 6, q ≠ 4 → changes (g2in q) r = false) ∨
    (∃ p : Fin 6, (p.val = a.val ∨ p.val = b.val) ∧ p.val < 4 ∧
      ∃ r : Fin 128, changes ((ops (w7 o1 a) (w7 o1 b)).getD o.val 0) r = false ∧
        changes (op45 o1) r = false ∧
        ∀ q : Fin 6, q ≠ p → changes (g2in q) r = false) := by decide +kernel

set_option maxRecDepth 16000 in
theorem sep_pair3 : ∀ o1 o2 : Fin 4, o1 ≠ o2 → ∀ c d : Fin 8, c < d → c.val < 4 →
    (d = 6 → o1 = 1) → (d = 7 → o2 = 1) → ∀ o : Fin 4,
    ∃ p : Fin 6, (p.val = c.val ∨ p.val = d.val) ∧ p.val < 4 ∧
      ∃ r : Fin 128, changes ((ops (w8 o1 o2 c) (w8 o1 o2 d)).getD o.val 0) r = false ∧
        changes (op45 o1) r = false ∧ changes (op45 o2) r = false ∧
        ∀ q : Fin 6, q ≠ p → changes (g2in q) r = false := by decide +kernel

theorem raw_present_gen {t z : W} (ht : t = goal ∨ t = ~~~goal) {k : ℕ} {rest : Finset W}
    (p : W) (r : Fin 128) (hrz : changes z r = false)
    (hother : ∀ w ∈ rest, w ≠ p → changes w r = false)
    (h : live basicOps t k (insert z rest)) : p ∈ rest := by
  have hd : differs r t := by rcases ht with rfl | rfl; exact (goal_changes r).1; exact (goal_changes r).2
  obtain ⟨w, hw, hdw⟩ := live_separates (differs r) hd (ops_differs r) h
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact False.elim (unchanged _ _ hrz hdw)
  · by_contra hn
    have hne : w ≠ p := fun e => hn (e ▸ hw)
    exact unchanged _ _ (hother w hw hne) hdw

theorem del_p_lt4_elim (p : Fin 6) (hp : p.val < 4) :
    (p = 0 ∨ p = 3) ∨ (p = 1 ∨ p = 2) := by
  fin_cases p <;> simp_all

theorem build_of_mem {k : ℕ} {av : Finset W} {t : W} (h : t ∈ av) : build basicOps t k av := by
  induction k with
  | zero => exact h
  | succ m ih => exact Or.inl ih

theorem sb_to_build {k : ℕ} {av : Finset W} {t : W} (ht : t = goal ∨ t = ~~~goal)
    (hsb : SignedBuild k av t) : ∃ t', (t' = goal ∨ t' = ~~~goal) ∧ build basicOps t' k av := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  rcases hsb with c | c | r | r
  · rcases ht with rfl | rfl <;> [exact False.elim (ne.1 c); exact False.elim (ne.2.2.1 c)]
  · rcases ht with rfl | rfl <;> [exact False.elim (ne.2.1 c); exact False.elim (ne.2.2.2 c)]
  · exact ⟨t, ht, r⟩
  · exact ⟨~~~t, by rcases ht with rfl | rfl <;> simp, r⟩

theorem w8_mem (o1 o2 : Fin 4) (x : W) (hx : x ∈ insert (op45 o2) (insert (op45 o1) ins_g2.toFinset)) :
    ∃ i : Fin 8, w8 o1 o2 i = x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨7, by simp [w8]⟩
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨6, by simp [w8]⟩
    · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp hx)
      exact ⟨⟨q.val, by omega⟩, w8_eq_g2in o1 o2 ⟨q.val, by omega⟩ q rfl⟩

theorem w7_mem (o1 : Fin 4) (x : W) (hx : x ∈ insert (op45 o1) ins_g2.toFinset) :
    ∃ i : Fin 7, w7 o1 i = x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨6, by simp [w7]⟩
  · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp hx)
    exact ⟨⟨q.val, by omega⟩, w7_eq_g2in o1 ⟨q.val, by omega⟩ q rfl⟩

set_option maxRecDepth 8000 in
theorem no_seven_after_two45 (o1 o2 : Fin 4) (hne : o1 ≠ o2) :
    ∀ k ≤ 7, ∀ t : W, (t = goal ∨ t = ~~~goal) →
      ¬ build basicOps t k (insert (op45 o2) (insert (op45 o1) ins_g2.toFinset)) := by
  intro k
  induction k with
  | zero =>
    intro _ t ht h0
    rcases Finset.mem_insert.mp h0 with h | h
    · rcases ht with rfl | rfl <;> [exact (op45_not_goal o2).1 h.symm; exact (op45_not_goal o2).2 h.symm]
    · rcases Finset.mem_insert.mp h with h | h
      · rcases ht with rfl | rfl <;> [exact (op45_not_goal o1).1 h.symm; exact (op45_not_goal o1).2 h.symm]
      · obtain ⟨i, hi⟩ := g2_index _ (List.mem_toFinset.mp h)
        rcases ht with rfl | rfl <;> [exact (g2_not_goal i).1 hi; exact (g2_not_goal i).2 hi]
  | succ k ih =>
    intro hk t ht run
    let A := insert (op45 o2) (insert (op45 o1) ins_g2.toFinset)
    obtain ⟨s, hs, hl⟩ := compress run
    rcases first_live (k := k) hl with endcase | ⟨a, ha, b, hb, hab, u, hu, _, rest, he, tail⟩
    · have htA : t ∈ A := hs (by simp [endcase])
      exact ih (by omega) t ht (build_of_mem htA)
    · have sub : rest ⊆ A := fun x hx => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      obtain ⟨ia, rfl⟩ := w8_mem o1 o2 a (hs ha)
      obtain ⟨ib, rfl⟩ := w8_mem o1 o2 b (hs hb)
      have hiab : ia ≠ ib := fun e => hab (congrArg (w8 o1 o2) e)
      have step_ord : ∀ (c d : Fin 8), c < d → u ∈ basicOps (w8 o1 o2 c) (w8 o1 o2 d) → False := by
        intro c d hcd hucd
        by_cases hc4 : 4 ≤ c.val
        · have hd4 : 4 ≤ d.val := by omega
          have hmem45 : ∀ x : Fin 8, 4 ≤ x.val →
              w8 o1 o2 x = g2in 4 ∨ w8 o1 o2 x = g2in 5 ∨ w8 o1 o2 x = op45 o1 ∨ w8 o1 o2 x = op45 o2 := by
            intro x hx
            unfold w8
            split_ifs with h1 h2
            · by_cases h4 : x.val = 4
              · left; exact congrArg g2in (Fin.ext h4)
              · right; left
                have h5 : x.val = 5 := by omega
                exact congrArg g2in (Fin.ext h5)
            · right; right; left; rfl
            · right; right; right; rfl
          apply sb_reject_proj ix_del4 (del_goal 4) k5mp4_nd k5mp4_no6 ht
          apply sb_le (by omega : k ≤ 6)
          apply live_transport (proj_ops ix_del4) tail
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact g2_del4_only45_holds o1 o2 _ _ _ (hmem45 c hc4) (hmem45 d hd4) hucd
          · have h45 := g2_del45_holds 4 (.inl rfl)
            rcases Finset.mem_insert.mp (sub hw) with rfl | h1
            · exact h45.2 o2
            · rcases Finset.mem_insert.mp h1 with rfl | h2
              · exact h45.2 o1
              · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                exact h45.1 q
        · have hclt : c.val < 4 := by omega
          have kill_del45 (p45 : Fin 6) (hp45 : p45 = 4 ∨ p45 = 5) (hdz : proj (delIx p45) (w8 o1 o2 d) = 0) : False := by
            have h45 := g2_del45_holds p45 hp45
            have hcw : holds ins_k5mp4.toFinset (proj (delIx p45) (w8 o1 o2 c)) := by
              have hc6 : c.val < 6 := by omega
              simp only [w8, hc6, dite_true]; exact h45.1 ⟨c.val, hc6⟩
            apply sb_reject_proj (delIx p45) (del_goal p45) k5mp4_nd k5mp4_no6 ht
            apply sb_le (by omega : k ≤ 6)
            apply live_transport (proj_ops (delIx p45)) tail
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact mem_ops_zero hcw (.inl hdz) (.inr hdz) (proj_ops (delIx p45) _ _ _ hucd)
            · rcases Finset.mem_insert.mp (sub hw) with rfl | h1
              · exact h45.2 o2
              · rcases Finset.mem_insert.mp h1 with rfl | h2
                · exact h45.2 o1
                · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                  exact h45.1 q
          by_cases hd6 : d = 6 ∧ o1 ≠ 1
          · rcases hd6 with ⟨rfl, ho1⟩
            fin_cases o1
            · exact kill_del45 4 (.inl rfl) (by simpa [w8, delIx] using op45_del45_zero.1)
            · exact (ho1 rfl).elim
            · exact kill_del45 4 (.inl rfl) (by simpa [w8, delIx] using op45_del45_zero.2.1)
            · exact kill_del45 5 (.inr rfl) (by simpa [w8, delIx] using op45_del45_zero.2.2)
          · by_cases hd7 : d = 7 ∧ o2 ≠ 1
            · rcases hd7 with ⟨rfl, ho2⟩
              fin_cases o2
              · exact kill_del45 4 (.inl rfl) (by simpa [w8, delIx] using op45_del45_zero.1)
              · exact (ho2 rfl).elim
              · exact kill_del45 4 (.inl rfl) (by simpa [w8, delIx] using op45_del45_zero.2.1)
              · exact kill_del45 5 (.inr rfl) (by simpa [w8, delIx] using op45_del45_zero.2.2)
            · have hdo1 : d = 6 → o1 = 1 := fun h => by by_contra hne1; exact hd6 ⟨h, hne1⟩
              have hdo2 : d = 7 → o2 = 1 := fun h => by by_contra hne1; exact hd7 ⟨h, hne1⟩
              obtain ⟨ou, rfl⟩ := index_of_op _ _ _ hucd
              obtain ⟨p, hpd, hplt, r, hru, hro1, hro2, hrq⟩ := sep_pair3 o1 o2 hne c d hcd hclt hdo1 hdo2 ou
              have hpin : g2in p ∈ rest := raw_present_gen ht (g2in p) r hru (fun w hw hne_p => by
                rcases Finset.mem_insert.mp (sub hw) with rfl | h1
                · exact hro2
                · rcases Finset.mem_insert.mp h1 with rfl | h2
                  · exact hro1
                  · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                    exact hrq q (fun eq => hne_p (congrArg g2in eq))) tail
              have hpg : g2in p ≠ t := by rcases ht with rfl | rfl; exact (g2_not_goal p).1; exact (g2_not_goal p).2
              have hzero : proj (delIx p) (g2in p) = 0 := g2_del_zero p
              have hcd_p : proj (delIx p) (w8 o1 o2 c) = 0 ∨ proj (delIx p) (w8 o1 o2 d) = 0 := by
                rcases hpd with hpv | hpv
                · left; rw [w8_eq_g2in o1 o2 c p hpv]; exact hzero
                · right; rw [w8_eq_g2in o1 o2 d p hpv]; exact hzero
              rcases del_p_lt4_elim p hplt with hp03 | hp12
              · have hm := g2_del03_maps p hp03
                have hav : ∀ w ∈ A, holds (insert (mp3Op34 o2) (insert (mp3Op34 o1) ins_k5mp3.toFinset)) (proj (delIx p) w) := by
                  intro w hw
                  rcases Finset.mem_insert.mp hw with rfl | h1
                  · exact .inr (.inr ⟨mp3Op34 o2, Finset.mem_insert_self .., .inl (hm.2 o2)⟩)
                  · rcases Finset.mem_insert.mp h1 with rfl | h2
                    · exact .inr (.inr ⟨mp3Op34 o1, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), .inl (hm.2 o1)⟩)
                    · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                      by_cases hqp : q = p
                      · subst hqp; exact .inl hzero
                      · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hm.1 q hqp))), .inl rfl⟩)
                have hsb := live_transport_save (proj_ops (delIx p)) tail (Finset.mem_insert_of_mem hpin) hpg hzero (fun w hw => by
                  rcases Finset.mem_insert.mp hw with rfl | hw
                  · have hcw : w8 o1 o2 c ∈ A := w8_mem_A o1 o2 c
                    have hdw : w8 o1 o2 d ∈ A := w8_mem_A o1 o2 d
                    exact mem_ops_zero (hav _ hcw) (hav _ hdw) hcd_p (proj_ops (delIx p) _ _ _ hucd)
                  · exact hav w (sub hw))
                have ht' : proj (delIx p) t = goal ∨ proj (delIx p) t = ~~~goal := by
                  rcases ht with rfl | rfl; exact .inl (del_goal p); exact .inr (by rw [proj_not, del_goal p])
                exact k5mp3_2ops_no5_sb (by omega) o1 o2 hne ht' hsb
              · have hm := g2_del12_maps p hp12
                have hav : ∀ w ∈ A, holds (insert (meOp34 o2) (insert (meOp34 o1) ins_k5me.toFinset)) (proj (delIx p) w) := by
                  intro w hw
                  rcases Finset.mem_insert.mp hw with rfl | h1
                  · exact .inr (.inr ⟨meOp34 o2, Finset.mem_insert_self .., .inl (hm.2 o2)⟩)
                  · rcases Finset.mem_insert.mp h1 with rfl | h2
                    · exact .inr (.inr ⟨meOp34 o1, Finset.mem_insert_of_mem (Finset.mem_insert_self ..), .inl (hm.2 o1)⟩)
                    · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                      by_cases hqp : q = p
                      · subst hqp; exact .inl hzero
                      · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hm.1 q hqp))), .inl rfl⟩)
                have hsb := live_transport_save (proj_ops (delIx p)) tail (Finset.mem_insert_of_mem hpin) hpg hzero (fun w hw => by
                  rcases Finset.mem_insert.mp hw with rfl | hw
                  · have hcw : w8 o1 o2 c ∈ A := w8_mem_A o1 o2 c
                    have hdw : w8 o1 o2 d ∈ A := w8_mem_A o1 o2 d
                    exact mem_ops_zero (hav _ hcw) (hav _ hdw) hcd_p (proj_ops (delIx p) _ _ _ hucd)
                  · exact hav w (sub hw))
                have ht' : proj (delIx p) t = goal ∨ proj (delIx p) t = ~~~goal := by
                  rcases ht with rfl | rfl; exact .inl (del_goal p); exact .inr (by rw [proj_not, del_goal p])
                exact k5me_2ops_no5_sb (by omega) o1 o2 hne ht' hsb
      rcases lt_or_gt_of_ne hiab with hlt | hgt
      · exact step_ord ia ib hlt hu
      · exact step_ord ib ia hgt (ops_swap _ _ ▸ hu)

set_option maxRecDepth 8000 in
theorem no_eight_after_45 (o1 : Fin 4) :
    ∀ k ≤ 8, ∀ t : W, (t = goal ∨ t = ~~~goal) →
      ¬ build basicOps t k (insert (op45 o1) ins_g2.toFinset) := by
  intro k
  induction k with
  | zero =>
    intro _ t ht h0
    rcases Finset.mem_insert.mp h0 with h | h
    · rcases ht with rfl | rfl <;> [exact (op45_not_goal o1).1 h.symm; exact (op45_not_goal o1).2 h.symm]
    · obtain ⟨i, hi⟩ := g2_index _ (List.mem_toFinset.mp h)
      rcases ht with rfl | rfl <;> [exact (g2_not_goal i).1 hi; exact (g2_not_goal i).2 hi]
  | succ k ih =>
    intro hk t ht run
    let A := insert (op45 o1) ins_g2.toFinset
    obtain ⟨s, hs, hl⟩ := compress run
    rcases first_live (k := k) hl with endcase | ⟨a, ha, b, hb, hab, w, hw, _, rest, he, tail⟩
    · have htA : t ∈ A := hs (by simp [endcase])
      exact ih (by omega) t ht (build_of_mem htA)
    · have sub : rest ⊆ A := fun x hx => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      obtain ⟨ia, rfl⟩ := w7_mem o1 a (hs ha)
      obtain ⟨ib, rfl⟩ := w7_mem o1 b (hs hb)
      have hiab : ia ≠ ib := fun e => hab (congrArg (w7 o1) e)
      have step_ord : ∀ (c d : Fin 7), c < d → w ∈ basicOps (w7 o1 c) (w7 o1 d) → False := by
        intro c d hcd hwcd
        by_cases hc4 : 4 ≤ c.val
        · have hd4 : 4 ≤ d.val := by omega
          obtain ⟨ow, rfl⟩ := index_of_op _ _ _ hwcd
          let pc : Fin 3 := ⟨c.val - 4, by omega⟩
          let pd : Fin 3 := ⟨d.val - 4, by omega⟩
          have hpne : pc ≠ pd := fun e => by have := congrArg Fin.val e; dsimp only [pc, pd] at this; omega
          have hcl := op45_closure o1 pc pd hpne ow
          have heq_pool : ∀ (x : Fin 7) (hx : 4 ≤ x.val),
              w7 o1 x = (match (⟨x.val - 4, by omega⟩ : Fin 3) with | ⟨0, _⟩ => g2in 4 | ⟨1, _⟩ => g2in 5 | ⟨2, _⟩ => op45 o1) := by
            intro x hx
            rcases x with ⟨xv, hxv⟩
            interval_cases xv <;> simp [w7]
          have heqc := heq_pool c hc4
          have heqd := heq_pool d hd4
          dsimp only at hcl
          rw [← heqc, ← heqd] at hcl
          rcases hcl with htriv | ⟨o2, ho2ne, ho2eq⟩
          · have hholdA : holds A ((ops (w7 o1 c) (w7 o1 d)).getD ow.val 0) := by
              rcases htriv with h0 | h1 | ⟨m, hm⟩
              · exact .inl h0
              · exact .inr (.inl h1)
              · fin_cases m
                · exact .inr (.inr ⟨g2in 4, Finset.mem_insert_of_mem (g2in_mem 4), hm⟩)
                · exact .inr (.inr ⟨g2in 5, Finset.mem_insert_of_mem (g2in_mem 5), hm⟩)
                · exact .inr (.inr ⟨op45 o1, Finset.mem_insert_self .., hm⟩)
            have hsb : SignedBuild k A t :=
              live_transport (f := id) (fun _ _ _ h => h) tail (fun u hu => by
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact hholdA
              · exact .inr (.inr ⟨u, sub hu, .inl rfl⟩))
            obtain ⟨t', ht', hb'⟩ := sb_to_build ht hsb
            exact ih (by omega) t' ht' hb'
          · have hhold2 : holds (insert (op45 o2) A) ((ops (w7 o1 c) (w7 o1 d)).getD ow.val 0) :=
              .inr (.inr ⟨op45 o2, Finset.mem_insert_self .., ho2eq⟩)
            have hsb := live_transport (f := id) (fun _ _ _ h => h) tail (fun u hu => by
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact hhold2
              · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem (sub hu), .inl rfl⟩))
            obtain ⟨t', ht', hb'⟩ := sb_to_build ht hsb
            exact no_seven_after_two45 o1 o2 ho2ne.symm k (by omega) t' ht' hb'
        · have hclt : c.val < 4 := by omega
          obtain ⟨ow, rfl⟩ := index_of_op _ _ _ hwcd
          rcases sep_pair2 o1 c d hcd hclt ow with ⟨ho10, hd6, _, r, hrw, hro1, hrq⟩ | ⟨p, hpd, hplt, r, hrw, hro1, hrq⟩
          · subst ho10; subst hd6
            have h4in : g2in 4 ∈ rest := raw_present_gen ht (g2in 4) r hrw (fun u hu hne4 => by
              rcases Finset.mem_insert.mp (sub hu) with rfl | h2
              · exact hro1
              · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                exact hrq q (fun eq => hne4 (congrArg g2in eq))) tail
            have h4g : g2in 4 ≠ t := by rcases ht with rfl | rfl; exact (g2_not_goal 4).1; exact (g2_not_goal 4).2
            have h40 : proj ix_del4 (g2in 4) = 0 := g2_del_zero 4
            have h45 := g2_del45_holds 4 (.inl rfl)
            have hcw : holds ins_k5mp4.toFinset (proj ix_del4 (w7 0 c)) := by
              have hc6 : c.val < 6 := by omega
              simp only [w7, hc6, dite_true]; exact h45.1 ⟨c.val, hc6⟩
            have hdz : proj ix_del4 (w7 0 6) = 0 := by simpa [w7] using op45_del45_zero.1
            apply sb_reject_proj ix_del4 (del_goal 4) k5mp4_nd k5mp4_no6 ht
            apply sb_le (by omega : k - 1 ≤ 6)
            apply live_transport_save (proj_ops ix_del4) tail (Finset.mem_insert_of_mem h4in) h4g h40
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact mem_ops_zero hcw (.inl hdz) (.inr hdz) (proj_ops ix_del4 _ _ _ hwcd)
            · rcases Finset.mem_insert.mp (sub hu) with rfl | h2
              · exact h45.2 0
              · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                exact h45.1 q
          · have hpin : g2in p ∈ rest := raw_present_gen ht (g2in p) r hrw (fun u hu hnep => by
              rcases Finset.mem_insert.mp (sub hu) with rfl | h2
              · exact hro1
              · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                exact hrq q (fun eq => hnep (congrArg g2in eq))) tail
            have hpg : g2in p ≠ t := by rcases ht with rfl | rfl; exact (g2_not_goal p).1; exact (g2_not_goal p).2
            have hzero : proj (delIx p) (g2in p) = 0 := g2_del_zero p
            have hcd_p : proj (delIx p) (w7 o1 c) = 0 ∨ proj (delIx p) (w7 o1 d) = 0 := by
              rcases hpd with hpv | hpv
              · left; rw [w7_eq_g2in o1 c p hpv]; exact hzero
              · right; rw [w7_eq_g2in o1 d p hpv]; exact hzero
            have ht' : proj (delIx p) t = goal ∨ proj (delIx p) t = ~~~goal := by
              rcases ht with rfl | rfl; exact .inl (del_goal p); exact .inr (by rw [proj_not, del_goal p])
            rcases del_p_lt4_elim p hplt with hp03 | hp12
            · have hm := g2_del03_maps p hp03
              have hav : ∀ u ∈ A, holds (insert (mp3Op34 o1) ins_k5mp3.toFinset) (proj (delIx p) u) := by
                intro u hu
                rcases Finset.mem_insert.mp hu with rfl | h2
                · exact .inr (.inr ⟨mp3Op34 o1, Finset.mem_insert_self .., .inl (hm.2 o1)⟩)
                · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                  by_cases hqp : q = p
                  · subst hqp; exact .inl hzero
                  · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hm.1 q hqp)), .inl rfl⟩)
              have hsb := live_transport_save (proj_ops (delIx p)) tail (Finset.mem_insert_of_mem hpin) hpg hzero (fun u hu => by
                rcases Finset.mem_insert.mp hu with rfl | hu
                · have hcw : w7 o1 c ∈ A := w7_mem_A o1 c
                  have hdw : w7 o1 d ∈ A := w7_mem_A o1 d
                  exact mem_ops_zero (hav _ hcw) (hav _ hdw) hcd_p (proj_ops (delIx p) _ _ _ hwcd)
                · exact hav u (sub hu))
              obtain ⟨t', ht'', hb'⟩ := sb_to_build ht' hsb
              exact k5mp3_op_no6 (by omega) 3 4 (by decide) (by decide) (by decide) o1 ht'' hb'
            · have hm := g2_del12_maps p hp12
              have hav : ∀ u ∈ A, holds (insert (meOp34 o1) ins_k5me.toFinset) (proj (delIx p) u) := by
                intro u hu
                rcases Finset.mem_insert.mp hu with rfl | h2
                · exact .inr (.inr ⟨meOp34 o1, Finset.mem_insert_self .., .inl (hm.2 o1)⟩)
                · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp h2)
                  by_cases hqp : q = p
                  · subst hqp; exact .inl hzero
                  · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hm.1 q hqp)), .inl rfl⟩)
              have hsb := live_transport_save (proj_ops (delIx p)) tail (Finset.mem_insert_of_mem hpin) hpg hzero (fun u hu => by
                rcases Finset.mem_insert.mp hu with rfl | hu
                · have hcw : w7 o1 c ∈ A := w7_mem_A o1 c
                  have hdw : w7 o1 d ∈ A := w7_mem_A o1 d
                  exact mem_ops_zero (hav _ hcw) (hav _ hdw) hcd_p (proj_ops (delIx p) _ _ _ hwcd)
                · exact hav u (sub hu))
              obtain ⟨t', ht'', hb'⟩ := sb_to_build ht' hsb
              exact k5me_op_no6 (by omega) 3 4 (by decide) (by decide) (by decide) o1 ht'' hb'
      rcases lt_or_gt_of_ne hiab with hlt | hgt
      · exact step_ord ia ib hlt hw
      · exact step_ord ib ia hgt (ops_swap _ _ ▸ hw)

theorem no_nine_g2 (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t 9 ins_g2.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 8) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := g2_index t (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl | rfl
    · exact (g2_not_goal i).1 hi
    · exact (g2_not_goal i).2 hi
  · obtain ⟨ia, rfl⟩ := g2_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨ib, rfl⟩ := g2_index _ (List.mem_toFinset.mp (hs hb))
    have hiab : ia ≠ ib := fun e => hab (congrArg g2in e)
    have sub : rest ⊆ ins_g2.toFinset := fun x hx =>
      hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have step_ord : ∀ (i j : Fin 6), i < j → z ∈ basicOps (g2in i) (g2in j) → False := by
      intro i j hij hzij
      by_cases h45 : i = 4 ∧ j = 5
      · rcases h45 with ⟨rfl, rfl⟩
        obtain ⟨o1, rfl⟩ := index_of_op _ _ _ hzij
        have hsb : SignedBuild 8 (insert (op45 o1) ins_g2.toFinset) t :=
          live_transport (f := id) (fun _ _ _ h => h) tail (fun u hu => by
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact .inr (.inr ⟨op45 o1, Finset.mem_insert_self .., .inl rfl⟩)
          · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem (sub hu), .inl rfl⟩))
        obtain ⟨t', ht', hb'⟩ := sb_to_build ht hsb
        exact no_eight_after_45 o1 8 (le_refl 8) t' ht' hb'
      · obtain ⟨o, rfl⟩ := index_of_op _ _ _ hzij
        obtain ⟨p, hpij, hplt, r, hrz, hrq⟩ := sep_pair1 i j hij h45 o
        have hpin : g2in p ∈ rest := raw_present_gen ht (g2in p) r hrz (fun w hw hnep => by
          obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp (sub hw))
          exact hrq q (fun eq => hnep (congrArg g2in eq))) tail
        have hpg : g2in p ≠ t := by rcases ht with rfl | rfl; exact (g2_not_goal p).1; exact (g2_not_goal p).2
        have hzero : proj (delIx p) (g2in p) = 0 := g2_del_zero p
        have hij_p : proj (delIx p) (g2in i) = 0 ∨ proj (delIx p) (g2in j) = 0 :=
          hpij.imp (fun h => by rw [← h]; exact hzero) (fun h => by rw [← h]; exact hzero)
        have ht' : proj (delIx p) t = goal ∨ proj (delIx p) t = ~~~goal := by
          rcases ht with rfl | rfl; exact .inl (del_goal p); exact .inr (by rw [proj_not, del_goal p])
        rcases del_p_lt4_elim p hplt with hp03 | hp12
        · have hm := g2_del03_maps p hp03
          have hav : ∀ q : Fin 6, holds ins_k5mp3.toFinset (proj (delIx p) (g2in q)) := fun q => by
            by_cases hqp : q = p
            · subst hqp; exact .inl hzero
            · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (hm.1 q hqp), .inl rfl⟩)
          have hsb := live_transport_save (proj_ops (delIx p)) tail (Finset.mem_insert_of_mem hpin) hpg hzero (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact mem_ops_zero (hav i) (hav j) hij_p (proj_ops (delIx p) _ _ _ hzij)
            · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp (sub hu))
              exact hav q)
          exact k5mp3_no7_sb (le_refl 7) ht' hsb
        · have hm := g2_del12_maps p hp12
          have hav : ∀ q : Fin 6, holds ins_k5me.toFinset (proj (delIx p) (g2in q)) := fun q => by
            by_cases hqp : q = p
            · subst hqp; exact .inl hzero
            · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (hm.1 q hqp), .inl rfl⟩)
          have hsb := live_transport_save (proj_ops (delIx p)) tail (Finset.mem_insert_of_mem hpin) hpg hzero (fun u hu => by
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact mem_ops_zero (hav i) (hav j) hij_p (proj_ops (delIx p) _ _ _ hzij)
            · obtain ⟨q, rfl⟩ := g2_index _ (List.mem_toFinset.mp (sub hu))
              exact hav q)
          exact k5me_no7_sb (le_refl 7) ht' hsb
    rcases lt_or_gt_of_ne hiab with hlt | hgt
    · exact step_ord ia ib hlt hz
    · exact step_ord ib ia hgt (ops_swap _ _ ▸ hz)

theorem ten_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = table6 x) :
    9 < binaryCost gs := by
  by_contra hlow
  have low : binaryCost gs ≤ 9 := by omega
  have init : ∀ u ∈ ins_g2, holds ins_g2.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (ins_g2.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 6 => bit k (ins_g2.getD i.val 0)) = ins_g2.map (bit k) := by
      apply List.ext_getElem (by simp [ins_g2])
      intro i hi hj
      have hlt : i < ins_g2.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins_g2.map (bit k)) = bit k goal
    rw [← same, he]
    exact spec_g2 k
  obtain ⟨t, ht, run⟩ := compile gs o hg ins_g2 ins_g2.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins_g2.toFinset) :
      build basicOps t b ins_g2.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_nine_g2 t ht (lift low run)

def rcStep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) : List Gate × List (Bool ⊕ ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (out, env ++ [Sum.inl true])
    | i :: _ =>
      match env.getD i (Sum.inl false) with
      | Sum.inl b => (out, env ++ [Sum.inl (!b)])
      | Sum.inr w' => (out ++ [{ op := GateOp.not, inputs := [w'] }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.and =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) then
      (out, env ++ [Sum.inl false])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl true])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.and, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.or =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) then
      (out, env ++ [Sum.inl true])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl false])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.or, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | _ => (out, env ++ [Sum.inl false])

def rcCircuit (nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (gs : List Gate) (o : ℕ) : List Gate × ℕ :=
  let res := gs.foldl (rcStep nOut) ([], env0)
  match res.2.getD o (Sum.inl false) with
  | Sum.inr w' => (res.1, w')
  | Sum.inl false => (res.1, nOut + res.1.length)
  | Sum.inl true => (res.1 ++ [{ op := GateOp.not, inputs := [] }], nOut + res.1.length)

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t; omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]; omega

lemma rcStep_env_len (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (rcStep nOut st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]
    cases g.inputs with
    | nil => simp
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) <;> simp
  · simp [rcStep, h]
  · simp [rcStep, h]

lemma rcStep_legal (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, legal g') (hg : legal g) :
    ∀ g' ∈ (rcStep nOut st g).1, legal g' := by
  rcases st with ⟨out, env⟩
  dsimp only at h1 ⊢
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    cases g.inputs with
    | nil => exact h1
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => exact h1
      | inr w' =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · exact ⟨by simp, by simp⟩

lemma rcFold_legal (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ))
    (h1 : ∀ g' ∈ st.1, legal g') (hM : ∀ g ∈ gs, legal g) :
    ∀ g' ∈ (gs.foldl (rcStep nOut) st).1, legal g' := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rcStep nOut st g) (rcStep_legal nOut st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma binaryCost_append_one (gs : List Gate) (g : Gate) :
    binaryCost (gs ++ [g]) = binaryCost gs + (if isBinary g then 1 else 0) := by
  unfold binaryCost
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isBinary g <;> simp

lemma rcStep_binCost_le (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    binaryCost (rcStep nOut st g).1 ≤ binaryCost st.1 + (if isBinary g then 1 else 0) := by
  rcases st with ⟨out, env⟩
  dsimp only
  cases h : g.op
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases g.inputs with
    | nil => dsimp only; exact le_refl _
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => dsimp only; exact le_refl _
      | inr w' => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp [rcStep, h, isBinary]
  · simp [rcStep, h, isBinary]

lemma rcFold_binCost_le (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ)) :
    binaryCost (gs.foldl (rcStep nOut) st).1 ≤ binaryCost st.1 + binaryCost gs := by
  induction gs generalizing st with
  | nil => simp [binaryCost]
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    omega

lemma rcFold_eval_inv (nOut : ℕ) (gs : List Gate) (ys : List Bool) (hyl : ys.length = nOut)
    (hM : ∀ g ∈ gs, legal g) (ws : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i (Sum.inl false) with
      | Sum.inl b => ws.getD i false = b
      | Sum.inr w' => w' < nOut + st.1.length ∧ ws.getD i false = (st.1.foldl step ys).getD w' false) :
    let ws' := gs.foldl step ws
    let st' := gs.foldl (rcStep nOut) st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i (Sum.inl false) with
      | Sum.inl b => ws'.getD i false = b
      | Sum.inr w' => w' < nOut + st'.1.length ∧ ws'.getD i false = (st'.1.foldl step ys).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (step ws g).length = env.length + 1 := by simp [step, hlen_ws]
    have hget_old : ∀ i < env.length, (step ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (step ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (step ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (step ws g).length = (rcStep nOut (out, env) g).2.length ∧
        ∀ i, match (rcStep nOut (out, env) g).2.getD i (Sum.inl false) with
          | Sum.inl b => (step ws g).getD i false = b
          | Sum.inr w' => w' < nOut + (rcStep nOut (out, env) g).1.length ∧
              (step ws g).getD i false = ((rcStep nOut (out, env) g).1.foldl step ys).getD w' false := by
      constructor
      · rw [rcStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl step ys) = step (out.foldl step ys) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + out.length ∧ (step ws g).getD i false = (out.foldl step ys).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]; exact hinv i
        have hkeep_old_app : ∀ (x : Bool ⊕ ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + (out ++ [gnew]).length ∧
                (step ws g).getD i false = ((out ++ [gnew]).foldl step ys).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i (Sum.inl false) with
          | inl b => rw [hm] at hk; exact hk
          | inr w' =>
            rw [hm] at hk; dsimp only at hk
            have hw' : w' < nOut + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
            have hlen_w : (step (out.foldl step ys) gnew).length = nOut + out.length + 1 := by simp [step, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl step ys).length),
                List.getD_eq_getElem _ _ (by omega : w' < (step (out.foldl step ys) gnew).length)]
            simp [step, List.getElem_append_left (by omega : w' < (out.foldl step ys).length)]
        have hkeep_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none),
            w' < nOut + out.length := by
          intro w' hw'
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
          have hij := hinv j
          cases hm : env.getD j (Sum.inl false) with
          | inl b => rw [hm] at hj; cases hj
          | inr w0 =>
            rw [hm] at hj hij; dsimp only at hij
            cases hj; exact hij.1
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl false) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl false), hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjf⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjf hj'; dsimp only at hj'
                  cases b with
                  | false => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                  | true => simp at hjf
                | inr w' => rw [hm] at hjf; simp at hjf
              · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
          · have hand_eq : (g.inputs.map fun j => ws.getD j false).all id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).all id := by
              have hnof : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl false := by
                intro j hj heqf
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqf]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl false) →
                  (l.map fun j => ws.getD j false).all id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).all id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnf
                  have ha := hnf a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnf j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | false => exact absurd hm ha
                    | true =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia, Bool.true_and, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnof
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hand_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl true) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop]; simpa [GateOp.eval] using hand_eq
                · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl true), hget_last, hop]
                simp only [GateOp.eval, List.any_eq_true, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjt⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjt hj'; dsimp only at hj'
                  cases b with
                  | true => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hj'⟩
                  | false => simp at hjt
                | inr w' => rw [hm] at hjt; simp at hjt
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          · have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).any id := by
              have hnot : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl true := by
                intro j hj heqt
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqt]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl true) →
                  (l.map fun j => ws.getD j false).any id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).any id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnt
                  have ha := hnt a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | true => exact absurd hm ha
                    | false =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnot
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl false) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl false), hget_last, hop]; simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          cases hgi : g.inputs with
          | nil =>
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop, hgi]; rfl
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          | cons j rest_i =>
            dsimp only
            cases hm : env.getD j (Sum.inl false) with
            | inl b =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl (!b)) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl (!b)), hget_last, hop, hgi]; simpa [GateOp.eval] using hj'
                · rw [hkeep_hi (Sum.inl (!b)) i (by omega)]; exact hget_hi i (by omega)
            | inr w' =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (Sum.inr (nOut + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hgi, hfold_app]
                  have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                  simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hj'.2
                · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step ws g) (rcStep nOut (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma rcFold_inr_agree (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = st.2.length) (hylen : wy.length = st.2.length)
    (heq_cost : binaryCost (gs.foldl (rcStep nOut) st).1 = binaryCost st.1 + binaryCost gs)
    (hagree : ∀ i w', st.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false) :
    ∀ i w', (gs.foldl (rcStep nOut) st).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false := by
  induction gs generalizing wx wy st with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons] at heq_cost ⊢
    have hg := hM g List.mem_cons_self
    have h1 := rcFold_binCost_le nOut rest (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hstep_cost : binaryCost (rcStep nOut st g).1 = binaryCost st.1 + (if isBinary g then 1 else 0) := by omega
    have hrest_cost : binaryCost (rest.foldl (rcStep nOut) (rcStep nOut st g)).1 =
        binaryCost (rcStep nOut st g).1 + binaryCost rest := by omega
    rcases st with ⟨out, env⟩
    dsimp only at hxlen hylen hagree hstep_cost
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step wx g) (step wy g)
      (rcStep nOut (out, env) g) (by rw [rcStep_env_len]; simp [step, hxlen])
      (by rw [rcStep_env_len]; simp [step, hylen]) hrest_cost ?_
    have hget_old_x : ∀ i < env.length, (step wx g).getD i false = wx.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < env.length, (step wy g).getD i false = wy.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : (step wx g).getD env.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : (step wy g).getD env.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hall_inr_of_len2 :
        (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 →
        ∀ j ∈ g.inputs, ∃ w0, env.getD j (Sum.inl false) = Sum.inr w0 := by
      intro hl2 j hj
      cases hm : env.getD j (Sum.inl false) with
      | inr w0 => exact ⟨w0, rfl⟩
      | inl b =>
        exfalso
        have hlt := list_filterMap_len_lt (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
          g.inputs j hj (by rw [hm])
        have hcap := hg.2
        omega
    have hstep_env_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
        (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x i hi => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
      simp [List.getElem_append_left hi]
    have hstep_env_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
        (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
      List.getD_eq_default _ _ (by simp; omega)
    have hstep_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    intro i w' hiw'
    by_cases hi : i < env.length
    · have h1 : (rcStep nOut (out, env) g).2.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
        cases h : g.op
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; cases g.inputs with
          | nil => exact hstep_env_old _ i hi
          | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
      rw [h1] at hiw'
      rw [hget_old_x i hi, hget_old_y i hi]
      exact hagree i w' hiw'
    · by_cases heq : i = env.length
      · subst heq
        rw [hget_last_x, hget_last_y]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop] at hiw'
          cases hgi : g.inputs with
          | nil =>
            rw [hgi] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
          | cons j rest_i =>
            rw [hgi] at hiw'; dsimp only at hiw'
            cases hm : env.getD j (Sum.inl false) with
            | inl b => rw [hm] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
            | inr w0 =>
              rw [hop]
              simp only [GateOp.eval, List.map_cons, List.headD_cons, hagree j w0 hm]
      · exfalso
        have hlen_st : (rcStep nOut (out, env) g).2.length = env.length + 1 := rcStep_env_len nOut (out, env) g
        rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'

lemma rcCircuit_props (nIn nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (hlen0 : env0.length = nIn)
    (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g) :
    let res := rcCircuit nOut env0 gs o
    (∀ g ∈ res.1, legal g) ∧
    binaryCost res.1 ≤ binaryCost gs ∧
    (∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      Circuit.eval ⟨res.1, res.2⟩ ys = Circuit.eval ⟨gs, o⟩ xs) := by
  dsimp only [rcCircuit]
  have hfold_leg := rcFold_legal nOut gs ([], env0) (by intro g h; cases h) hM
  have hfold_bc : binaryCost (gs.foldl (rcStep nOut) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le nOut gs ([], env0); simpa [binaryCost] using this
  have hcore_eval : ∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      ∀ i, match (gs.foldl (rcStep nOut) ([], env0)).2.getD i (Sum.inl false) with
        | Sum.inl b => (gs.foldl step xs).getD i false = b
        | Sum.inr w' => w' < nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length ∧
            (gs.foldl step xs).getD i false = ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD w' false := by
    intro xs ys hxl hyl hinit
    have hinit' : ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut + (([] : List Gate), env0).1.length ∧ xs.getD i false = ((([] : List Gate), env0).1.foldl step ys).getD w' false := by
      intro i
      by_cases hi : i < nIn
      · simpa using hinit i hi
      · dsimp only
        rw [List.getD_eq_default _ _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
    exact (rcFold_eval_inv nOut gs ys hyl hM xs ([], env0) (by simp [hlen0, hxl]) hinit').2
  cases hm : (gs.foldl (rcStep nOut) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    refine ⟨hfold_leg, hfold_bc, ?_⟩
    intro xs ys hxl hyl hinit
    have h := hcore_eval xs ys hxl hyl hinit o
    rw [hm] at h; exact h.2.symm
  | inl b =>
    cases b with
    | false =>
      refine ⟨hfold_leg, hfold_bc, ?_⟩
      intro xs ys hxl hyl hinit
      have h := hcore_eval xs ys hxl hyl hinit o
      rw [hm] at h
      change ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
        (gs.foldl step xs).getD o false
      rw [h, List.getD_eq_default _ _ (by rw [wfold_len, hyl])]
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with h | rfl
        · exact hfold_leg g h
        · exact ⟨by simp, by decide⟩
      · rw [binaryCost_append_one]; simp [isBinary]; exact hfold_bc
      · intro xs ys hxl hyl hinit
        have h := hcore_eval xs ys hxl hyl hinit o
        rw [hm] at h
        change (((gs.foldl (rcStep nOut) ([], env0)).1 ++ [({ op := GateOp.not, inputs := [] } : Gate)]).foldl step ys).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
          (gs.foldl step xs).getD o false
        rw [h, List.foldl_append]
        change (step ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys) ({ op := GateOp.not, inputs := [] } : Gate)).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false = true
        have hlen : ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).length =
            nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length := by rw [wfold_len, hyl]
        rw [← hlen, List.getD_eq_getElem _ _ (by simp [step])]
        simp [step, GateOp.eval]

lemma rcCircuit_binCost_lt (k : ℕ) (hk : k < 7) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = 7) (hx2l : x2.length = 7)
    (hagree_xy : ∀ i < 7, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = 7) (hz2l : z2.length = 7)
    (hz1k : z1.getD k false = false) (hz2k : z2.getD k false = false)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 7 => if i.val = k then Sum.inl false else Sum.inr i.val
    binaryCost (rcCircuit 7 env0 gs o).1 + 1 ≤ binaryCost gs := by
  intro env0
  have hle_fold : binaryCost (gs.foldl (rcStep 7) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le 7 gs ([], env0); simpa [binaryCost] using this
  have hbc_rc : binaryCost (rcCircuit 7 env0 gs o).1 = binaryCost (gs.foldl (rcStep 7) ([], env0)).1 := by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep 7) ([], env0)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  rw [hbc_rc]
  by_contra hlt
  have hzero : binaryCost ([] : List Gate) = 0 := rfl
  have heq_cost : binaryCost (gs.foldl (rcStep 7) ([], env0)).1 = binaryCost ([] : List Gate) + binaryCost gs := by
    rw [hzero, Nat.zero_add]; omega
  cases hm : (gs.foldl (rcStep 7) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    have hinit : ∀ i w0, (([] : List Gate), env0).2.getD i (Sum.inl false) = Sum.inr w0 → x1.getD i false = x2.getD i false := by
      intro i w0 hiw
      by_cases hi : i < 7
      · dsimp only at hiw
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])] at hiw
        change (List.ofFn fun j : Fin 7 => if j.val = k then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) = Sum.inr w0 at hiw
        rw [List.getElem_ofFn] at hiw
        by_cases hik : i = k
        · simp [hik] at hiw
        · exact hagree_xy i hi hik
      · dsimp only at hiw
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)] at hiw; cases hiw
    have hsame := rcFold_inr_agree 7 gs hM x1 x2 ([], env0) (by simp [env0, hx1l]) (by simp [env0, hx2l])
      heq_cost hinit o w' hm
    exact hdiff_xy hsame
  | inl b =>
    have hinit_z : ∀ (z : List Bool), z.length = 7 → z.getD k false = false →
        ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < 7 + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
      intro z hzl hzk i
      by_cases hi : i < 7
      · dsimp only
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
        change match (List.ofFn fun j : Fin 7 => if j.val = k then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < 7 + 0 ∧ z.getD i false = z.getD w' false
        rw [List.getElem_ofFn]
        by_cases hik : i = k
        · subst hik; simp only [ite_true]; exact hzk
        · simp [hik, hi]
      · dsimp only
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)]
        exact List.getD_eq_default z false (by omega)
    have hz1 := (rcFold_eval_inv 7 gs z1 hz1l hM z1 ([], env0) (by simp [env0, hz1l]) (hinit_z z1 hz1l hz1k)).2 o
    have hz2 := (rcFold_eval_inv 7 gs z2 hz2l hM z2 ([], env0) (by simp [env0, hz2l]) (hinit_z z2 hz2l hz2k)).2 o
    rw [hm] at hz1 hz2
    dsimp only at hz1 hz2
    exact hdiff_zz (hz1.trans hz2.symm)



def graphF (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def witGates : List Gate :=
  [ { op := GateOp.or,  inputs := [6, 4] }
  , { op := GateOp.or,  inputs := [5, 6] }
  , { op := GateOp.or,  inputs := [0, 8] }
  , { op := GateOp.or,  inputs := [0, 1] }
  , { op := GateOp.or,  inputs := [3, 4] }
  , { op := GateOp.and, inputs := [10, 5] }
  , { op := GateOp.or,  inputs := [2, 10] }
  , { op := GateOp.or,  inputs := [7, 12] }
  , { op := GateOp.and, inputs := [9, 11] }
  , { op := GateOp.or,  inputs := [13, 5] }
  , { op := GateOp.and, inputs := [14, 16] }
  , { op := GateOp.or,  inputs := [15, 17] } ]

lemma witGates_mono : ∀ g ∈ witGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma witGates_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witGates, 18⟩ (List.ofFn x) = graphF x := by
  decide +kernel

def lift6 (y : Fin 6 → Bool) : Fin 7 → Bool
  | ⟨0, _⟩ => y 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => y 2
  | ⟨4, _⟩ => y 3
  | ⟨5, _⟩ => y 4
  | ⟨6, _⟩ => y 5

lemma graphF_lift6 : ∀ y : Fin 6 → Bool, graphF (lift6 y) = table6 y := by
  decide +kernel

lemma main_proof (gates : List Gate) (o : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graphF x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = graphF x := by
  by_cases hasNot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨gNot, hgNot, hopNot⟩ := hasNot
    have hbc_lt : binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨gNot, hgNot, by simp [isBinary, hopNot]⟩
    have hleg' : ∀ g ∈ gates, legal g := fun g hg => ⟨by simpa using (hleg g hg).1, (hleg g hg).2⟩
    let env2 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 7 => if i.val = 2 then Sum.inl false else Sum.inr i.val
    let C1 := rcCircuit 7 env2 gates o
    have h1_props := rcCircuit_props 7 7 env2 (by simp [env2]) gates o hleg'
    have h1_eval : ∀ x : Fin 7 → Bool, x 2 = false → Circuit.eval ⟨C1.1, C1.2⟩ (List.ofFn x) = graphF x := by
      intro x hx2
      rw [h1_props.2.2 (List.ofFn x) (List.ofFn x) (by simp) (by simp) ?_, heval x]
      intro i hi
      rw [List.getD_eq_getElem env2 _ (by simp [env2, hi])]
      change match (List.ofFn fun j : Fin 7 => if j.val = 2 then Sum.inl false else Sum.inr j.val)[i]'(by simp [hi]) with
        | Sum.inl b => (List.ofFn x).getD i false = b
        | Sum.inr w' => w' < 7 ∧ (List.ofFn x).getD i false = (List.ofFn x).getD w' false
      rw [List.getElem_ofFn]
      by_cases hi2 : i = 2
      · subst hi2; simp only [ite_true]; rw [List.getD_eq_getElem _ _ (by simp)]; simpa using hx2
      · simp [hi2, hi]
    have h1_lt : binaryCost C1.1 + 1 ≤ binaryCost gates := by
      let fx1 : Fin 7 → Bool := fun i => decide (i.val = 2 ∨ i.val = 4)
      let fx2 : Fin 7 → Bool := fun i => decide (i.val = 4)
      let fz1 : Fin 7 → Bool := fun _ => false
      let fz2 : Fin 7 → Bool := fun i => decide (i.val = 0 ∨ i.val = 3)
      exact rcCircuit_binCost_lt 2 (by decide) gates o hleg'
        (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp) (by decide)
        (by rw [heval fx1, heval fx2]; decide)
        (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by decide) (by decide)
        (by rw [heval fz1, heval fz2]; decide)
    let env6 : List (Bool ⊕ ℕ) := [Sum.inr 0, Sum.inr 1, Sum.inl false, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]
    let C2 := rcCircuit 6 env6 C1.1 C1.2
    have h2_props := rcCircuit_props 7 6 env6 (by decide) C1.1 C1.2 h1_props.1
    have h2_eval : ∀ y : Fin 6 → Bool, Circuit.eval ⟨C2.1, C2.2⟩ (List.ofFn y) = table6 y := by
      intro y
      rw [h2_props.2.2 (List.ofFn (lift6 y)) (List.ofFn y) (by simp) (by simp) ?_,
          h1_eval (lift6 y) rfl, graphF_lift6 y]
      intro i hi
      interval_cases i
      · exact ⟨by decide, by simp [lift6]⟩
      · exact ⟨by decide, by simp [lift6]⟩
      · simp [env6, lift6]
      · exact ⟨by decide, by simp [lift6]⟩
      · exact ⟨by decide, by simp [lift6]⟩
      · exact ⟨by decide, by simp [lift6]⟩
      · exact ⟨by decide, by simp [lift6]⟩
    have h10 : 9 < binaryCost C2.1 := ten_binary C2.1 C2.2 h2_props.1 h2_eval
    have h2_le : binaryCost C2.1 ≤ binaryCost C1.1 := h2_props.2.1
    have h12 : witGates.length ≤ gates.length := by
      change 12 ≤ gates.length; omega
    exact ⟨witGates, 18, witGates_mono, h12, witGates_eval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (hleg g hg).2⟩, le_refl _, heval⟩
    rcases (hleg g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_11139

theorem PEqualNP.Outside.L_meta_11139 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hleg _ heval
  exact PEqualNP.Outside.L_meta_11139.main_proof gates o hleg heval
