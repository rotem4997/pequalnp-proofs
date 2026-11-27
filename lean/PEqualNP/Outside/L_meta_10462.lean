import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10462

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

abbrev W := BitVec 512
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

open PEqualNP.CircuitLowerBounds

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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
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

def ins_fffefee8 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082, 0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104, 0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208, 0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410, 0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]

theorem nd_fffefee8 : ins_fffefee8.Nodup := by decide +kernel

theorem spec_fffefee8 : ∀ j : Fin 512, Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (ins_fffefee8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,e | e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · subst z; exact Or.inr (Or.inr (Or.inl ha))
  · subst z; exact Or.inr (Or.inr (Or.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z := by
  rcases h with h|h|h|h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inl h)))
  · exact .inr (.inr (.inr (.inl h)))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t := by
  rcases h with h|h|h|h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (.inr ⟨a,ha,b,hb,hne,z,hz,h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨a,ha,b,hb,hne,z,hz,h⟩)))

theorem sb_holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x := by
  rcases h with h|h|⟨a,ha,e⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a,sub ha,e⟩)

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
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | (rw [absorb]; assumption) | simp_all

theorem ops_map_of {f : W → W} (hAnd : ∀ a b, f (a &&& b) = (f a &&& f b))
    (hOr : ∀ a b, f (a ||| b) = (f a ||| f b)) (hNot : ∀ a, f (~~~a) = ~~~(f a)) :
    ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) := by
  intro a b z hz
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
  rcases hz with rfl|rfl|rfl|rfl <;> simp [hAnd,hOr,hNot]

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
        · exact sb_holds_mono sub (hav u (by simp [he,hr]))

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
          · exact sb_holds_mono sub (inOld u hr)

def k4inputs : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842, 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084, 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108, 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

private theorem k5DispatchMono {e : ℕ} {a b : W} {r : List W}
    {f g : ℕ → List W → Bool} (h : ∀ e l, f e l = true → g e l = true)
    (ok : dispatch e f a b r = true) : dispatch e g a b r = true := by
  simp only [dispatch, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at ok ⊢
  obtain ⟨w, hw, hw'⟩ := ok
  refine ⟨w, hw, ?_⟩
  rcases hw' with ((⟨u,v⟩ | ⟨u,(⟨v,t⟩ | ⟨v,t⟩)⟩) | ⟨⟨u,v⟩,t⟩)
  · exact .inl (.inl ⟨u, h _ _ v⟩)
  · exact .inl (.inr ⟨u, .inl ⟨v, h _ _ t⟩⟩)
  · exact .inl (.inr ⟨u, .inr ⟨v, h _ _ t⟩⟩)
  · exact .inr ⟨⟨u,v⟩, h _ _ t⟩

private def k5Etat (i j : ℕ) : ℕ × List W :=
  let (a,b,r) := (pairs k4inputs).getD i (0,0,[])
  (1, (ops a b).getD j 0 :: a :: b :: r)

private def k5Etats : List (ℕ × List W) :=
  (List.range 6).flatMap fun i => (List.range 4).map fun j => k5Etat i j

private def k5Cert (e : ℕ) (l : List W) := !(k5Etats.contains (e,l))

private theorem k5Top : ((pairs k4inputs).any (fun (a,b,r) => dispatch 3 k5Cert a b r)) = false := by
  decide +kernel

private theorem k5Root :
    k4inputs.sublists.filter (fun l => decide (l.length ≤ 7) && (cuts l == -1)) = [k4inputs] := by
  decide +kernel

private theorem k5Si (h : ∀ p ∈ k5Etats, optimized 5 p.1 p.2 = false) :
    search 6 k4inputs = false := by
  have mono (e l) (ok : optimized 5 e l = true) : k5Cert e l = true := by
    simp only [k5Cert, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun hm => Bool.noConfusion ((h (e,l) hm).symm.trans ok)
  have hfalse : optimized 6 3 k4inputs = false := by
    have initial : (k4inputs == [goal] || k4inputs == [~~~goal]) = false := by decide +kernel
    rw [optimized, initial, Bool.false_or]
    apply List.any_eq_false.mpr
    rintro ⟨a,b,r⟩ hp hd
    exact (List.any_eq_false.mp k5Top _ hp) (k5DispatchMono mono hd)
  apply List.any_eq_false.mpr
  intro ws hw hs
  obtain ⟨hc, ho⟩ := Bool.and_eq_true_iff.mp hs
  have hmem : ws ∈ k4inputs.sublists.filter (fun l => decide (l.length ≤ 7) && (cuts l == -1)) :=
    List.mem_filter.mpr ⟨hw,hc⟩
  rw [k5Root] at hmem
  have eq : ws = k4inputs := List.mem_singleton.mp hmem
  subst ws
  exact Bool.noConfusion (hfalse.symm.trans ho)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille00 : optimized 5 (k5Etat 0 0).1 (k5Etat 0 0).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille01 : optimized 5 (k5Etat 0 1).1 (k5Etat 0 1).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille02 : optimized 5 (k5Etat 0 2).1 (k5Etat 0 2).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille03 : optimized 5 (k5Etat 0 3).1 (k5Etat 0 3).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille10 : optimized 5 (k5Etat 1 0).1 (k5Etat 1 0).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille11 : optimized 5 (k5Etat 1 1).1 (k5Etat 1 1).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille12 : optimized 5 (k5Etat 1 2).1 (k5Etat 1 2).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille13 : optimized 5 (k5Etat 1 3).1 (k5Etat 1 3).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille20 : optimized 5 (k5Etat 2 0).1 (k5Etat 2 0).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille21 : optimized 5 (k5Etat 2 1).1 (k5Etat 2 1).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille22 : optimized 5 (k5Etat 2 2).1 (k5Etat 2 2).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille23 : optimized 5 (k5Etat 2 3).1 (k5Etat 2 3).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille30 : optimized 5 (k5Etat 3 0).1 (k5Etat 3 0).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille31 : optimized 5 (k5Etat 3 1).1 (k5Etat 3 1).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille32 : optimized 5 (k5Etat 3 2).1 (k5Etat 3 2).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille33 : optimized 5 (k5Etat 3 3).1 (k5Etat 3 3).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille40 : optimized 5 (k5Etat 4 0).1 (k5Etat 4 0).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille41 : optimized 5 (k5Etat 4 1).1 (k5Etat 4 1).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille42 : optimized 5 (k5Etat 4 2).1 (k5Etat 4 2).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille43 : optimized 5 (k5Etat 4 3).1 (k5Etat 4 3).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille50 : optimized 5 (k5Etat 5 0).1 (k5Etat 5 0).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille51 : optimized 5 (k5Etat 5 1).1 (k5Etat 5 1).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille52 : optimized 5 (k5Etat 5 2).1 (k5Etat 5 2).2 = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem k5Feuille53 : optimized 5 (k5Etat 5 3).1 (k5Etat 5 3).2 = false := by decide +kernel

theorem k4exact : search 6 k4inputs = false := by
  apply k5Si
  intro p hp
  change p ∈ [k5Etat 0 0, k5Etat 0 1, k5Etat 0 2, k5Etat 0 3, k5Etat 1 0, k5Etat 1 1, k5Etat 1 2, k5Etat 1 3, k5Etat 2 0, k5Etat 2 1, k5Etat 2 2, k5Etat 2 3, k5Etat 3 0, k5Etat 3 1, k5Etat 3 2, k5Etat 3 3, k5Etat 4 0, k5Etat 4 1, k5Etat 4 2, k5Etat 4 3, k5Etat 5 0, k5Etat 5 1, k5Etat 5 2, k5Etat 5 3] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact k5Feuille00
  · exact k5Feuille01
  · exact k5Feuille02
  · exact k5Feuille03
  · exact k5Feuille10
  · exact k5Feuille11
  · exact k5Feuille12
  · exact k5Feuille13
  · exact k5Feuille20
  · exact k5Feuille21
  · exact k5Feuille22
  · exact k5Feuille23
  · exact k5Feuille30
  · exact k5Feuille31
  · exact k5Feuille32
  · exact k5Feuille33
  · exact k5Feuille40
  · exact k5Feuille41
  · exact k5Feuille42
  · exact k5Feuille43
  · exact k5Feuille50
  · exact k5Feuille51
  · exact k5Feuille52
  · exact k5Feuille53


def vinput (i : Fin 5) : W := ins_fffefee8.getD i.val 0

def pairIx : Fin 5 → List ℕ := ![[12, 14, 15, 16, 17, 30, 32, 33, 34, 35, 42, 44, 45, 46, 47, 54, 56, 57, 58, 59, 72, 74, 75, 76, 77, 84, 86, 87, 88, 89, 96, 98, 99, 100, 101, 108, 110, 111, 112, 113, 120, 122, 123, 124, 125, 132, 134, 135, 136, 137, 144, 146, 147, 148, 149],
[6, 7, 9, 10, 11, 24, 25, 27, 28, 29, 42, 43, 45, 46, 47, 48, 49, 51, 52, 53, 66, 67, 69, 70, 71, 84, 85, 87, 88, 89, 90, 91, 93, 94, 95, 108, 109, 111, 112, 113, 114, 115, 117, 118, 119, 132, 133, 135, 136, 137, 138, 139, 141, 142, 143],
[0, 1, 2, 4, 5, 24, 25, 26, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 66, 67, 68, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 130, 131],
[0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 66, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 101, 102, 103, 104, 105, 107],
[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64]]

def sourceRow (i : Fin 5) (j : Fin 512) : Fin 512 :=
  ⟨((if j.val < 256 then 0 else 256) + (pairIx i).getD ((j.val % 256) % 55) 0) % 512,
    Nat.mod_lt _ (by decide)⟩

def restriction (i : Fin 5) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(sourceRow i k).val]))).cast List.length_ofFn

theorem restriction_bit (i : Fin 5) (w : W) (j : Fin 512) :
    (restriction i w)[j.val] = w[(sourceRow i j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [restriction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dif_pos, Option.getD_some]

theorem restriction_land (i : Fin 5) (u v : W) :
    restriction i (u &&& v) = (restriction i u &&& restriction i v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (restriction i (u &&& v))[k.val] = (restriction i u &&& restriction i v)[k.val]
  simp only [restriction_bit, BitVec.getElem_and]

theorem restriction_lor (i : Fin 5) (u v : W) :
    restriction i (u ||| v) = (restriction i u ||| restriction i v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (restriction i (u ||| v))[k.val] = (restriction i u ||| restriction i v)[k.val]
  simp only [restriction_bit, BitVec.getElem_or]

theorem restriction_neg (i : Fin 5) (u : W) : restriction i (~~~u) = ~~~restriction i u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (restriction i (~~~u))[k.val] = (~~~restriction i u)[k.val]
  simp only [restriction_bit, BitVec.getElem_not]

def remaining (i : Fin 5) : List W :=
  ((List.finRange 5).filter (· != i)).map fun j => restriction i (vinput j)

set_option maxRecDepth 8000 in
theorem projected_input : ∀ i : Fin 5, restriction i (vinput i) = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem projected_goal : ∀ i : Fin 5, restriction i goal = goal := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_nd : ∀ i : Fin 5, (remaining i).Nodup := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_same : ∀ i : Fin 5, remaining i = k4inputs := by decide +kernel

theorem remaining_reject (i : Fin 5) : search 6 (remaining i) = false := by
  rw [remaining_same]
  exact k4exact

set_option maxRecDepth 8000 in
theorem input_index : ∀ w ∈ ins_fffefee8, ∃ i : Fin 5, vinput i = w := by
  intro w hw
  simp only [ins_fffefee8, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩

theorem restricted_available : ∀ i j : Fin 5, holds (remaining i).toFinset (restriction i (vinput j)) := by
  intro i j
  by_cases h : i = j
  · subst j
    exact Or.inl (projected_input i)
  · right; right
    exact ⟨_, List.mem_toFinset.mpr (List.mem_map.mpr ⟨j, by simp [Ne.symm h],rfl⟩), Or.inl rfl⟩

def changes (w : W) (r : Fin 256) : Bool :=
  w.getLsbD (256+r.val) != w.getLsbD r.val

set_option maxRecDepth 8000 in
theorem separating_pair : ∀ i j : Fin 5, i ≠ j → ∀ op : Fin 4, ∃ r : Fin 256,
    changes ((ops (vinput i) (vinput j)).getD op.val 0) r = false ∧
    ∀ q : Fin 5, q ≠ i → changes (vinput q) r = false := by decide +kernel

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

theorem unchanged (w : W) (r : Fin 256) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem input_not_goal : ∀ i : Fin 5, vinput i ≠ goal ∧ vinput i ≠ ~~~goal := by decide +kernel

theorem goal_changes : ∀ k : Fin 256, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel

theorem restricted_new (i j : Fin 5) (z : W) (hz : z ∈ basicOps (vinput i) (vinput j)) :
    holds (remaining i).toFinset (restriction i z) := by
  exact mem_ops_zero (restricted_available i i) (restricted_available i j)
    (Or.inl (projected_input i))
    (ops_map_of (restriction_land i) (restriction_lor i) (restriction_neg i) _ _ _ hz)

theorem raw_present {t : W} (ht : t = goal ∨ t = ~~~goal) (i j : Fin 5) (hij : i ≠ j)
    {z : W} (hz : z ∈ basicOps (vinput i) (vinput j)) (rest : Finset W)
    (hsub : rest ⊆ ins_fffefee8.toFinset)
    (h : live basicOps t 7 (insert z rest)) : vinput i ∈ rest := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  obtain ⟨r, hrz, hrq⟩ := separating_pair i j hij o
  rw [ho] at hrz
  have hd : differs r t := by
    rcases ht with rfl|rfl
    · exact (goal_changes r).1
    · exact (goal_changes r).2
  obtain ⟨w, hw, hdw⟩ := live_separates (differs r) hd (ops_differs r) h
  rcases Finset.mem_insert.mp hw with rfl|hw
  · exact False.elim (unchanged _ _ hrz hdw)
  · obtain ⟨q,rfl⟩ := input_index _ (List.mem_toFinset.mp (hsub hw))
    by_contra hn
    have qi : q ≠ i := by intro eq; exact hn (eq ▸ hw)
    exact unchanged _ _ (hrq q qi) hdw

set_option maxRecDepth 4000 in
theorem projected_impossible (i : Fin 5) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (h : SignedBuild 6 (remaining i).toFinset (restriction i t)) : False := by
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have signs : restriction i t = goal ∨ restriction i t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact Or.inl (projected_goal i)
    · exact Or.inr (by rw [restriction_neg,projected_goal])
  have opposite : ~~~restriction i t = goal ∨ ~~~restriction i t = ~~~goal := by
    rcases signs with h|h <;> simp [h]
  have no {u : W} (hu : u = goal ∨ u = ~~~goal) (run : build basicOps u 6 (remaining i).toFinset) : False := by
    have hit := search_complete hu 6 (remaining i) (remaining_nd i) run
    exact Bool.noConfusion ((remaining_reject i).symm.trans hit)
  rcases h with c | c | run | run
  · rcases signs with h|h
    · exact ne.1 (h.symm.trans c)
    · exact ne.2.2.1 (h.symm.trans c)
  · rcases signs with h|h
    · exact ne.2.1 (h.symm.trans c)
    · exact ne.2.2.2 (h.symm.trans c)
  · exact no signs run
  · exact no opposite run

theorem no_eight_binary (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 ins_fffefee8.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a,ha,b,hb,hab,z,hz,_,rest,he,tail⟩
  · have tx : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := input_index _ (List.mem_toFinset.mp (hs tx))
    rcases ht with rfl|rfl
    · exact (input_not_goal i).1 hi
    · exact (input_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := input_index _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg vinput eq)
    have sub : rest ⊆ ins_fffefee8.toFinset := by
      intro u hu
      exact hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    have keep := raw_present ht i j hij hz rest sub tail
    have pg : vinput i ≠ t := by rcases ht with rfl|rfl; exact (input_not_goal i).1; exact (input_not_goal i).2
    apply projected_impossible i t ht
    apply live_transport_save (ops_map_of (restriction_land i) (restriction_lor i) (restriction_neg i))
      tail (Finset.mem_insert_of_mem keep) pg (projected_input i)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact restricted_new i j w hz
    · obtain ⟨k,rfl⟩ := input_index _ (List.mem_toFinset.mp (sub hw))
      exact restricted_available i k

open PEqualNP.CircuitLowerBounds

def bouts : List ℕ := [0,2,0,3,1,3,0,4,1,4,2,4,3,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6]
def but (x : Fin 7 → Bool) := decide (∃ i < bouts.length / 2,
  (List.ofFn x).getD (bouts.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (bouts.getD (2*i+1) 0) false = true)
def mono (gs : List Gate) : Prop := ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
def calcule (gs : List Gate) (o : ℕ) := ∀ x : Fin 7 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = but x
def temoin : List Gate :=
  [⟨.or,[0,1]⟩, ⟨.and,[7,3]⟩, ⟨.and,[0,2]⟩, ⟨.or,[8,9]⟩,
   ⟨.or,[2,3]⟩, ⟨.or,[7,11]⟩, ⟨.or,[4,5]⟩, ⟨.and,[4,5]⟩,
   ⟨.and,[13,6]⟩, ⟨.or,[14,15]⟩, ⟨.or,[13,6]⟩, ⟨.and,[12,17]⟩,
   ⟨.or,[10,16]⟩, ⟨.or,[18,19]⟩]

theorem temoinMono : mono temoin := by simp [mono, temoin]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem exactitude : calcule temoin 20 := by unfold calcule; decide +kernel

theorem remplacement (s : ℕ) (hs : 14 ≤ s) : ∃ gs o, mono gs ∧ gs.length ≤ s ∧ calcule gs o :=
  ⟨temoin,20,temoinMono,hs,exactitude⟩

theorem insuffisant {gs : List Gate} {o : ℕ}
    (admis : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (cal : calcule gs o) (h : ¬∃ ds p, mono ds ∧ ds.length ≤ gs.length ∧ calcule ds p) :
    gs.length ≤ 13 ∧ ∃ g ∈ gs, g.op = .not := by
  constructor
  · by_contra! e; exact h (remplacement _ (by omega))
  · by_contra! e
    apply h
    refine ⟨gs,o,?_,le_rfl,cal⟩
    intro g hg
    obtain ⟨h₁|h₂|h₃,cap⟩ := admis g hg
    · exact ⟨Or.inl h₁,cap⟩
    · exact ⟨Or.inr h₂,cap⟩
    · exact (e g hg h₃).elim

open PEqualNP.CircuitLowerBounds

def circuit13 : List Gate :=
  [⟨.or,[4,5]⟩, ⟨.or,[7,6]⟩, ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩,
   ⟨.or,[3,8]⟩, ⟨.or,[0,8]⟩, ⟨.and,[9,11]⟩, ⟨.and,[10,12]⟩,
   ⟨.and,[4,5]⟩, ⟨.and,[7,6]⟩, ⟨.or,[13,14]⟩, ⟨.or,[15,16]⟩, ⟨.or,[17,18]⟩]

theorem admis13 : mono circuit13 := by simp [mono,circuit13]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem correct13 : calcule circuit13 19 := by unfold calcule; decide +kernel

theorem remplace13 {gs : List Gate} {o : ℕ}
    (admis : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (bon : calcule gs o) (h : ¬∃ ds p, mono ds ∧ ds.length ≤ gs.length ∧ calcule ds p) :
    gs.length ≤ 12 ∧ ∃ g ∈ gs, g.op = .not := by
  refine ⟨?_, (insuffisant admis bon h).2⟩
  by_contra! hn
  exact h ⟨circuit13,19,admis13,hn,correct13⟩

abbrev H := BitVec 8
def tab (f : Fin 512 → Bool) : W := (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
def low (i : Fin 4) : W := tab fun k => k.val.testBit i.val
def high (h : H) : W := tab fun k => h.getLsbD ((k.val / 16) % 8)
def start : List H := [170,204,240]
def pool (s : List H) : Finset W := ((List.ofFn low) ++ s.map high).toFinset
def calcul (u : ℕ) : Bool :=
  let a := u.testBit 0; let b := u.testBit 1; let c := u.testBit 2; let d := u.testBit 3
  let e := u.testBit 4; let f := u.testBit 5; let g := u.testBit 6
  ((a || b) && (d || e || f || g)) || ((c || d) && (a || e || f || g)) || (e && f) || ((e || f) && g)
def cible : W := tab fun k => calcul k.val
def actif (h : H) : Bool := [0,1,2,4].any (fun i => h.getLsbD i != h.getLsbD 0)
def table5 (h : H) : W := tab fun k =>
  h.getLsbD ((if (vinput 2)[k.val] then 1 else 0) + (if (vinput 3)[k.val] then 2 else 0) + (if (vinput 4)[k.val] then 4 else 0))
def Gens (d : ℕ) (s : List H) : Prop := ∃ av : Finset W, ins_fffefee8.toFinset ⊆ av ∧
  (∀ h ∈ s, holds av (table5 h)) ∧
  ∀ k t, SignedBuild k av t → SignedBuild (d+k) ins_fffefee8.toFinset t
def Mort (d : ℕ) (s : List H) : Prop := ∀ (k : ℕ) (t : W), d+k ≤ 11 →
  (t = cible ∨ t = ~~~cible) → live basicOps t k (pool s) → False

theorem tab_bit (f : Fin 512 → Bool) (k : Fin 512) : (tab f)[k.val] = f k := by
  rw [← BitVec.getLsbD_eq_getElem k.isLt]
  simp only [tab,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,k.isLt,dite_eq_left,Option.getD_some]

def lowMap (p : Fin 3) (i : Fin 4) : Option (Fin 5) :=
  ![![none,some 0,none,some 1],![some 0,none,none,some 1],![some 0,none,some 1,none]] p i

def xk (k : Fin 512) (i : Fin 5) : Bool := (vinput i)[k.val]
def trois (x : Fin 5 → Bool) : ℕ := (if x 2 then 1 else 0)+(if x 3 then 2 else 0)+(if x 4 then 4 else 0)
def paire (x : Fin 5 → Bool) : ℕ := (if x 3 then 1 else 0)+(if x 4 then 2 else 0)
def dilate (p : Fin 3) (j : ℕ) : ℕ := (j % 2^p.val) + (j / 2^p.val)*(2^(p.val+1))
def sous (p : Fin 3) (h : H) : BitVec 4 :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 4 => h.getLsbD (dilate p i.val)))).cast List.length_ofFn
def table2 (u : BitVec 4) : W := tab fun k => u.getLsbD (paire (xk k))

def ligneL (p : Fin 3) (x : Fin 5 → Bool) : Fin 512 :=
  ⟨((∑ i : Fin 4, if ((lowMap p i).map x).getD false then 2^i.val else 0) + 16*trois x)%512, Nat.mod_lt _ (by decide)⟩
def ligneH (p : Fin 3) (x : Fin 5 → Bool) : Fin 512 :=
  ⟨((if x 0 then 1 else 0)+(if x 1 then 6 else 0)+(if x 2 then 8 else 0)+16*dilate p (paire x))%512,Nat.mod_lt _ (by decide)⟩
def lire (ligne : Fin 512 → Fin 512) (w : W) : W := tab fun k => w[(ligne k).val]
def projL (p : Fin 3) : W → W := lire fun k => ligneL p (xk k)
def projH (p : Fin 3) : W → W := lire fun k => ligneH p (xk k)

theorem homLire (l : Fin 512 → Fin 512) : ∀ a b z, z ∈ basicOps a b → lire l z ∈ basicOps (lire l a) (lire l b) := by
  apply ops_map_of
  · intro a b; apply BitVec.eq_of_getElem_eq; intro i hi
    let k : Fin 512 := ⟨i,hi⟩
    change (lire l (a &&& b))[k.val] = (lire l a &&& lire l b)[k.val]
    simp only [lire,tab_bit,BitVec.getElem_and]
  · intro a b; apply BitVec.eq_of_getElem_eq; intro i hi
    let k : Fin 512 := ⟨i,hi⟩
    change (lire l (a ||| b))[k.val] = (lire l a ||| lire l b)[k.val]
    simp only [lire,tab_bit,BitVec.getElem_or]
  · intro a; apply BitVec.eq_of_getElem_eq; intro i hi
    let k : Fin 512 := ⟨i,hi⟩
    change (lire l (~~~a))[k.val] = (~~~lire l a)[k.val]
    simp only [lire,tab_bit,BitVec.getElem_not]

theorem homL (p : Fin 3) : ∀ a b z, z ∈ basicOps a b → projL p z ∈ basicOps (projL p a) (projL p b) := homLire (fun k => ligneL p (xk k))
theorem homH (p : Fin 3) : ∀ a b z, z ∈ basicOps a b → projH p z ∈ basicOps (projH p a) (projH p b) := homLire (fun k => ligneH p (xk k))

theorem cibleLire (l : (Fin 5 → Bool) → Fin 512)
    (test : ∀ x, calcul (l x).val = Nat.testBit 0xfffefee8 (∑ i : Fin 5, if x i then 2^i.val else 0)) :
    lire (fun k => l (xk k)) cible = goal ∧ lire (fun k => l (xk k)) (~~~cible) = ~~~goal := by
  constructor
  · apply BitVec.eq_of_getElem_eq; intro i hi
    let k : Fin 512 := ⟨i,hi⟩
    change (lire _ cible)[k.val] = goal[k.val]
    simp only [lire,cible,tab_bit]; exact (test (xk k)).trans (spec_fffefee8 k)
  · apply BitVec.eq_of_getElem_eq; intro i hi
    let k : Fin 512 := ⟨i,hi⟩
    change (lire _ (~~~cible))[k.val] = (~~~goal)[k.val]
    simp only [lire,cible,tab_bit,BitVec.getElem_not]; exact congrArg Bool.not ((test (xk k)).trans (spec_fffefee8 k))

theorem cibleL (p : Fin 3) : projL p cible = goal ∧ projL p (~~~cible) = ~~~goal := by
  apply cibleLire; fin_cases p <;> decide +kernel

theorem cibleH (p : Fin 3) : projH p cible = goal ∧ projH p (~~~cible) = ~~~goal := by
  apply cibleLire; fin_cases p <;> decide +kernel

theorem lowL (p : Fin 3) (i : Fin 4) : projL p (low i) = ((lowMap p i).map vinput).getD 0 := by
  have e : ∀ p i (x : Fin 5 → Bool), (ligneL p x).val.testBit (i : Fin 4).val = ((lowMap p i).map x).getD false := by decide +kernel
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (projL p (low i))[k.val] = _
  simp only [projL,lire,low,tab_bit,e]
  cases hh : lowMap p i with
  | none => simp
  | some v => rfl

theorem highL (p : Fin 3) (h : H) : projL p (high h) = table5 h := by
  have e : ∀ p x, ((ligneL p x).val / 16) % 8 = trois x := by decide +kernel
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (projL p (high h))[k.val] = (table5 h)[k.val]
  simp only [projL,lire,high,table5,tab_bit,e]; rfl

theorem lowH (p : Fin 3) (i : Fin 4) : projH p (low i) = vinput (![0,1,1,2] i) := by
  have e : ∀ p (i : Fin 4) x, (ligneH p x).val.testBit i.val = x (![0,1,1,2] i) := by decide +kernel
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (projH p (low i))[k.val] = _
  simp only [projH,lire,low,tab_bit,e]; rfl

theorem highH (p : Fin 3) (h : H) : projH p (high h) = table2 (sous p h) := by
  have e : ∀ p x, ((ligneH p x).val / 16) % 8 = dilate p (paire x) := by decide +kernel
  have borne : ∀ x, paire x < 4 := by decide +kernel
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (projH p (high h))[k.val] = (table2 (sous p h))[k.val]
  simp only [projH,lire,high,table2,tab_bit,e,sous,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,borne,dite_eq_left,Option.getD_some]

theorem gensInit : Gens 0 start := by
  refine ⟨_, Finset.Subset.rfl, ?_, fun k t h => by simpa only [Nat.zero_add] using h⟩
  intro h hm
  have ex : ∃ i : Fin 5, table5 h = vinput i := by
    have eqn : ∀ (x : Fin 5 → Bool), (170 : H).getLsbD (trois x) = x 2 ∧ (204 : H).getLsbD (trois x) = x 3 ∧ (240 : H).getLsbD (trois x) = x 4 := by decide +kernel
    simp only [start,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl
    · refine ⟨2,?_⟩; apply BitVec.eq_of_getElem_eq; intro j hj
      exact (tab_bit _ ⟨j,hj⟩).trans (eqn (xk ⟨j,hj⟩)).1
    · refine ⟨3,?_⟩; apply BitVec.eq_of_getElem_eq; intro j hj
      exact (tab_bit _ ⟨j,hj⟩).trans (eqn (xk ⟨j,hj⟩)).2.1
    · refine ⟨4,?_⟩; apply BitVec.eq_of_getElem_eq; intro j hj
      exact (tab_bit _ ⟨j,hj⟩).trans (eqn (xk ⟨j,hj⟩)).2.2
  obtain ⟨i,e⟩ := ex
  have hh : ∀ j : Fin 5, vinput j ∈ ins_fffefee8.toFinset := by decide +kernel
  exact .inr (.inr ⟨_,hh i,.inl e⟩)

theorem tableAnd (a b : H) : table5 (a &&& b) = table5 a &&& table5 b := by
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (table5 (a &&& b))[k.val] = (table5 a &&& table5 b)[k.val]
  simp only [table5,tab_bit,BitVec.getElem_and,BitVec.getLsbD_and]

theorem tableOr (a b : H) : table5 (a ||| b) = table5 a ||| table5 b := by
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (table5 (a ||| b))[k.val] = (table5 a ||| table5 b)[k.val]
  simp only [table5,tab_bit,BitVec.getElem_or,BitVec.getLsbD_or]

theorem tableNot (a : H) : table5 (~~~a) = ~~~table5 a := by
  have bl : ∀ x, trois x < 8 := by decide +kernel
  apply BitVec.eq_of_getElem_eq; intro j hj
  let k : Fin 512 := ⟨j,hj⟩
  change (tab (fun i => (~~~a).getLsbD (trois (xk i))))[k.val] = (~~~table5 a)[k.val]
  simp only [tab_bit,BitVec.getElem_not,BitVec.getLsbD_not,bl,decide_true,Bool.true_and]
  rw [show (table5 a)[k.val] = a.getLsbD (trois (xk k)) from tab_bit _ _]

theorem gensNext {d : ℕ} {s s' : List H} {a b z : H} (hg : Gens d s) (ha : a ∈ s) (hb : b ∈ s)
    (hz : z ∈ [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]) (ht : ∀ w ∈ s', w = z ∨ w ∈ s) : Gens (d+1) s' := by
  obtain ⟨av,sub,good,trans⟩ := hg
  have zr : reachable av (table5 z) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · rw [tableAnd]; exact and_reach (good _ ha) (good _ hb)
    · rw [tableOr]; exact or_reach (good _ ha) (good _ hb)
    · rw [tableAnd,tableNot]; exact and_reach (good _ ha) (holds_not (good _ hb))
    · rw [tableAnd,tableNot]; exact and_reach (good _ hb) (holds_not (good _ ha))
  rcases zr with pre|⟨x,hx,y,hy,ne,u,hu,new⟩
  · refine ⟨av,sub,fun w hw => (ht w hw).elim (fun e => e ▸ pre) (good w),?_⟩
    intro k t h; apply sb_le (by omega : d+k ≤ d+1+k); exact trans k t h
  · refine ⟨insert u av,fun v hv => Finset.mem_insert_of_mem (sub hv),?_,?_⟩
    · intro w hw; rcases ht w hw with rfl|old
      · exact new
      · exact holds_insert (good w old)
    · intro k t h; have v := trans (k+1) t (sb_step hx hy ne hu h)
      simpa only [Nat.add_right_comm d 1 k,Nat.add_assoc] using v

private abbrev mConst (x : W) := x = 0 ∨ x = ~~~0
private abbrev mPoids (f : W → W) (s : Finset W) := (s.filter fun w => mConst (f w)).card

private theorem mGauche {x y z : W} {av : Finset W} (cx : mConst x)
    (hy : holds av y) (hop : z ∈ basicOps x y) : holds av z := by
  rcases cx with rfl | rfl
  · exact mem_ops_zero (.inl rfl) hy (.inl rfl) hop
  · simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hop
    simp only [BitVec.not_not] at hop
    have et (v : W) : ~~~(0 : W) &&& v = v :=
      (congrArg (fun w : W => w &&& v) BitVec.not_zero).trans BitVec.allOnes_and
    have ou (v : W) : ~~~(0 : W) ||| v = ~~~(0 : W) :=
      (congrArg (fun w : W => w ||| v) BitVec.not_zero).trans (BitVec.allOnes_or.trans BitVec.not_zero.symm)
    rcases hop with rfl | rfl | rfl | rfl
    · rw [et]; exact hy
    · exact .inr (.inl (ou y))
    · rw [et]; exact holds_not hy
    · exact .inl BitVec.and_zero

private theorem mGratuit {x y z : W} {av : Finset W} (hx : holds av x) (hy : holds av y)
    (hc : mConst x ∨ mConst y) (hop : z ∈ basicOps x y) : holds av z := by
  rcases hc with h | h
  · exact mGauche h hy hop
  · exact mGauche h hx (ops_swap x y ▸ hop)

private theorem mFerme {x y z : W} (hx : mConst x) (hy : mConst y)
    (hop : z ∈ basicOps x y) : mConst z := by
  have hy' : holds ∅ y := hy.elim Or.inl (fun e => .inr (.inl e))
  simpa only [holds, Finset.notMem_empty, false_and, exists_false, or_false] using mGauche hx hy' hop

private theorem mIns (f : W → W) (u : W) (s : Finset W) :
    mPoids f (insert u s) ≤ mPoids f s + (if mConst (f u) then 1 else 0) := by
  by_cases h : mConst (f u)
  · simpa only [mPoids, Finset.filter_insert, h, ite_true] using
      Finset.card_insert_le u (s.filter fun w => mConst (f w))
  · simp [mPoids, Finset.filter_insert, h]

private theorem mNeuf (f : W → W) (u : W) (s : Finset W) (hn : u ∉ s) :
    mPoids f (insert u s) = mPoids f s + (if mConst (f u) then 1 else 0) := by
  have hn' : u ∉ s.filter (fun w => mConst (f w)) := fun h => hn (Finset.mem_filter.mp h).1
  by_cases h : mConst (f u) <;> simp [mPoids, Finset.filter_insert, h, hn']

private theorem mTransport {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} (hg : f g ≠ 0 ∧ f g ≠ ~~~0) {k : ℕ} {s : Finset W} (run : live basicOps g k s) :
    mPoids f s ≤ k ∧ ∀ av, (∀ w ∈ s, holds av (f w)) → SignedBuild (k - mPoids f s) av (f g) := by
  induction k generalizing s with
  | zero =>
    change s = {g} at run
    subst s
    have hc : ¬ mConst (f g) := not_or.mpr hg
    constructor
    · simp only [mPoids, Finset.filter_singleton, hc, ite_false, Finset.card_empty, le_refl]
    · intro av hav
      simpa only [Nat.zero_sub] using sb_zero (hav g (by simp))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, _, z, hz, hout, r, he, tail⟩
    · obtain ⟨bound, go⟩ := ih skip
      exact ⟨by omega, fun av hav => sb_le (by omega) (go av hav)⟩
    · obtain ⟨bound, go⟩ := ih tail
      have mapped := hm a b z hz
      have hzr : z ∉ r := fun h => hout (by simp [he, h])
      have hnew := mNeuf f z r hzr
      have ha' := mIns f a (insert b r)
      have hb' := mIns f b r
      have hold : mPoids f s ≤ mPoids f r + (if mConst (f a) then 1 else 0) +
          (if mConst (f b) then 1 else 0) := by rw [he]; omega
      have diff : mPoids f s ≤ mPoids f (insert z r) + 1 := by
        by_cases ca : mConst (f a) <;> by_cases cb : mConst (f b)
        · have cz := mFerme ca cb mapped
          simp only [ca, cb, cz, ite_true] at hold hnew
          omega
        all_goals simp only [ca, cb, ite_true, ite_false] at hold; omega
      refine ⟨by omega, ?_⟩
      intro av hav
      have hr (u : W) (hu : u ∈ r) : holds av (f u) := hav u (by simp [he, hu])
      have suite (av' : Finset W) (hsub : av ⊆ av') (ok : holds av' (f z)) :
          SignedBuild (k - mPoids f (insert z r)) av' (f g) := by
        apply go av'
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ok
        · exact sb_holds_mono hsub (hr u hu)
      by_cases hc : mConst (f a) ∨ mConst (f b)
      · exact sb_le (by omega) (suite av (fun _ h => h) (mGratuit (hav a ha) (hav b hb) hc mapped))
      · obtain ⟨ca, cb⟩ := not_or.mp hc
        simp only [ca, cb, ite_false, Nat.add_zero] at hold
        exact sb_le (by omega) (sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped) suite)

theorem multi {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hg : f g ≠ 0 ∧ f g ≠ ~~~0) (hav : ∀ w ∈ s, holds av (f w)) :
    SignedBuild (k - (s.filter (fun w => f w = 0 ∨ f w = ~~~0)).card) av (f g) :=
  (mTransport hm hg run).2 av hav

theorem assez {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s : Finset W} (run : live basicOps g k s) (hg : f g ≠ 0 ∧ f g ≠ ~~~0) :
    (s.filter (fun w => f w = 0 ∨ f w = ~~~0)).card ≤ k := (mTransport hm hg run).1

theorem noSigned8 {k : ℕ} {t : W} (hk : k ≤ 8) (ht : t = goal ∨ t = ~~~goal) :
    ¬ SignedBuild k ins_fffefee8.toFinset t := by
  intro h
  rcases sb_le hk h with c | c | run | run
  · rcases ht with rfl | rfl <;> revert c <;> decide +kernel
  · rcases ht with rfl | rfl <;> revert c <;> decide +kernel
  · exact no_eight_binary t ht run
  · apply no_eight_binary (~~~t) _ run
    rcases ht with rfl | rfl <;> simp

def basG : Fin 3 → Fin 4 := ![0,1,1]
def basD : Fin 3 → Fin 4 := ![2,2,3]

def basBit (x : Fin 128) (i : Fin 4) := x.val.testBit i.val
def basHaut (x : Fin 128) := (x.val / 16) % 8
def basFlip (q : Fin 4) (x : Fin 128) : Fin 128 :=
  ⟨(x.val ^^^ (2 ^ q.val)) % 128, Nat.mod_lt _ (by decide)⟩
def basLigne (x : Fin 128) : Fin 512 := ⟨x.val, by omega⟩
def basOp (m : Fin 4) (a b : Bool) : Bool := ![a && b, a || b, a && !b, b && !a] m
def basBloque : Fin 4 → Bool := ![false,true,true,false]

theorem basStableH : ∀ q x, basHaut (basFlip q x) = basHaut x := by decide +kernel
theorem basStableL : ∀ q j x, j ≠ q → basBit (basFlip q x) j = basBit x j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem basDeux : ∀ (i j m : Fin 4), i ≠ j → ∃ p,
    (i = basG p ∨ i = basD p ∨ j = basG p ∨ j = basD p) ∧
    ∀ q, (q = basG p ∨ q = basD p) → (q = i ∨ q = j) → ∃ x,
      calcul x.val ≠ calcul (basFlip q x).val ∧
      basOp m (basBit x i) (basBit x j) = basOp m (basBit (basFlip q x) i) (basBit (basFlip q x) j) := by
  decide +kernel

theorem basUn : ∀ i : Fin 4, ∃ p, i = basG p ∨ i = basD p := by decide

set_option maxRecDepth 8192 in
theorem basTranche : ∀ (q : Fin 4) (u : Fin 8),
    u.val ∈ [0,1,2,4] → ∃ x, basHaut x = u.val ∧ calcul x.val ≠ calcul (basFlip q x).val := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem basActif : ∀ (h : H), actif h = true → ∀ v : Bool,
    ∃ u : Fin 8, u.val ∈ [0,1,2,4] ∧ h.getLsbD u.val = v := by decide +kernel

theorem basBloc : ∀ m a b, basOp m a (basBloque m) = basOp m b (basBloque m) := by decide

def basVal (x : Fin 128) (w : W) : Bool := w[(basLigne x).val]
theorem basValL (x : Fin 128) (i) : basVal x (low i) = basBit x i := tab_bit _ _
theorem basValH (x : Fin 128) (h) : basVal x (high h) = h.getLsbD (basHaut x) := tab_bit _ _
theorem basValC (x : Fin 128) : basVal x cible = calcul x.val := tab_bit _ _
theorem basValN (x : Fin 128) (w : W) : basVal x (~~~w) = !basVal x w := by simp [basVal]

theorem basMode {a b z : W} (hz : z ∈ basicOps a b) : ∃ m, ∀ x,
    basVal x z = basOp m (basVal x a) (basVal x b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact ⟨0, fun x => by simp [basVal,basOp]⟩
  · exact ⟨1, fun x => by simp [basVal,basOp]⟩
  · exact ⟨2, fun x => by simp [basVal,basOp]⟩
  · exact ⟨3, fun x => by simp [basVal,basOp]⟩

theorem basPool {s : List H} {w : W} : w ∈ pool s ↔ (∃ i, w = low i) ∨ (∃ h ∈ s, w = high h) := by
  simp only [pool, List.mem_toFinset, List.mem_append, List.mem_ofFn', Set.mem_range, List.mem_map]
  grind

theorem basHerite (x y : Fin 128) (a b z : W) (hz : z ∈ basicOps a b)
    (hn : basVal x z ≠ basVal y z) : basVal x a ≠ basVal y a ∨ basVal x b ≠ basVal y b := by
  obtain ⟨m, hm⟩ := basMode hz
  contrapose! hn
  rw [hm,hm,hn.1,hn.2]

theorem basVivant {s : List H} {r : Finset W} {t z : W} {k : ℕ} (sub : r ⊆ pool s)
    (ht : t = cible ∨ t = ~~~cible) (run : live basicOps t k (insert z r)) (q : Fin 4)
    (tem : ∃ x, calcul x.val ≠ calcul (basFlip q x).val ∧ basVal x z = basVal (basFlip q x) z) : low q ∈ r := by
  obtain ⟨x,hc,hz⟩ := tem
  have dt : basVal x t ≠ basVal (basFlip q x) t := by
    rcases ht with rfl|rfl
    · simpa only [basValC] using hc
    · simp only [basValN,basValC]; revert hc; cases calcul x.val <;> cases calcul (basFlip q x).val <;> decide
  obtain ⟨w,hw,dw⟩ := live_separates (fun w => basVal x w ≠ basVal (basFlip q x) w) dt (basHerite x (basFlip q x)) run
  rcases Finset.mem_insert.mp hw with rfl|hr
  · exact (dw hz).elim
  rcases basPool.mp (sub hr) with ⟨j,rfl⟩|⟨h,_,rfl⟩
  · by_cases he : j = q
    · simpa [he] using hr
    · exact (dw (by simp only [basValL,basStableL q j x he])).elim
  · exact (dw (by simp only [basValH,basStableH])).elim

theorem basInj : Function.Injective low := by
  intro i j h
  by_contra hn
  have tem : ∀ i j : Fin 4, i ≠ j → ∃ x, basBit x i ≠ basBit x j := by decide +kernel
  obtain ⟨x,hd⟩ := tem i j hn
  exact hd (by simpa only [basValL] using congrArg (basVal x) h)

theorem basSepH (q : Fin 4) (h : H) : low q ≠ high h := by
  intro he
  have hn : ∀ q : Fin 4, basBit 0 q ≠ basBit (basFlip q 0) q := by decide
  apply hn q
  rw [← basValL, ← basValL, he, basValH, basValH, basStableH]

theorem basHZero : high 0 = 0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  let j : Fin 512 := ⟨i,hi⟩
  change (tab _)[j.val] = (0 : W)[j.val]
  simp [tab_bit]

theorem basOpZero {a z : W} (hz : z ∈ basicOps a 0) : z = 0 ∨ z = a := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have hab : a &&& (~~~(0 : W)) = a := (congrArg (fun u : W => a &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  rcases hz with rfl|rfl|rfl|rfl
  · simp
  · simp
  · exact .inr hab
  · simp

theorem basReste {s : List H} {a b : W} {r : Finset W} (he : pool s = insert a (insert b r))
    (q : Fin 4) (ha : low q ≠ a) (hb : low q ≠ b) : low q ∈ r := by
  have hm : low q ∈ pool s := basPool.mpr (.inl ⟨q,rfl⟩)
  simpa only [he, Finset.mem_insert, ha, hb, false_or] using hm

def basChoix (a b : W) (r : Finset W) : Prop := ∃ p,
  (a = low (basG p) ∨ a = low (basD p) ∨ b = low (basG p) ∨ b = low (basD p)) ∧
  low (basG p) ∈ r ∧ low (basD p) ∈ r

theorem basGauche {s : List H} {k : ℕ} {t b z : W} {r : Finset W} (i : Fin 4)
    (hs : ∀ h ∈ s, actif h = true ∨ h = 0) (ht : t = cible ∨ t = ~~~cible) (hb : b ∈ pool s)
    (ne : low i ≠ b) (hz : z ∈ basicOps (low i) b) (hznew : z ∉ pool s)
    (he : pool s = insert (low i) (insert b r)) (run : live basicOps t k (insert z r)) : basChoix (low i) b r := by
  have sub : r ⊆ pool s := by rw [he]; exact fun _ hu => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
  obtain ⟨m,hm⟩ := basMode hz
  rcases basPool.mp hb with ⟨j,rfl⟩|⟨h,hh,rfl⟩
  · obtain ⟨p,hp,tem⟩ := basDeux i j m (fun e => ne (congrArg low e))
    have tous (q : Fin 4) (hq : q = basG p ∨ q = basD p) : low q ∈ r := by
      by_cases op : q = i ∨ q = j
      · obtain ⟨x,hc,hx⟩ := tem q hq op
        exact basVivant sub ht run q ⟨x,hc,by simpa only [hm,basValL] using hx⟩
      · exact basReste he q (fun e => op (.inl (basInj e))) (fun e => op (.inr (basInj e)))
    refine ⟨p,?_,tous _ (.inl rfl),tous _ (.inr rfl)⟩
    rcases hp with e|e|e|e <;> simp [e]
  · rcases hs h hh with act|rfl
    · obtain ⟨p,hp⟩ := basUn i
      obtain ⟨u,hu,e⟩ := basActif h act (basBloque m)
      obtain ⟨x,hx,hc⟩ := basTranche i u hu
      have iv : low i ∈ r := basVivant sub ht run i ⟨x,hc,by
        simp only [hm,basValL,basValH,basStableH,hx,e]; exact basBloc _ _ _⟩
      have tous (q : Fin 4) : low q ∈ r := by
        by_cases eq : q = i
        · exact eq ▸ iv
        · exact basReste he q (fun e => eq (basInj e)) (basSepH q h)
      refine ⟨p,?_,tous _,tous _⟩
      rcases hp with e|e <;> simp [e]
    · rw [basHZero] at hb hz
      rcases basOpZero hz with rfl|rfl
      · exact (hznew hb).elim
      · exact (hznew (basPool.mpr (.inl ⟨i,rfl⟩))).elim

theorem basPlan {s : List H} {k : ℕ} {t a b z : W} {r : Finset W}
    (hs : ∀ h ∈ s, actif h = true ∨ h = 0) (ht : t = cible ∨ t = ~~~cible) (ha : a ∈ pool s) (hb : b ∈ pool s)
    (ne : a ≠ b) (hz : z ∈ basicOps a b) (hznew : z ∉ pool s) (lo : (∃ i, a = low i) ∨ (∃ i, b = low i))
    (he : pool s = insert a (insert b r)) (run : live basicOps t k (insert z r)) : basChoix a b r := by
  rcases lo with ⟨i,rfl⟩|⟨i,rfl⟩
  · exact basGauche i hs ht hb ne hz hznew he run
  · have hz' : z ∈ basicOps (low i) a := by
      simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
      rw [BitVec.and_comm (low i) a,BitVec.or_comm (low i) a]
      exact hz.imp_right (Or.imp_right Or.symm)
    obtain ⟨p,hp,hg,hd⟩ := basGauche i hs ht ha (Ne.symm ne) hz' hznew (he.trans (Finset.insert_comm ..)) run
    refine ⟨p,?_,hg,hd⟩
    rcases hp with e|e|e|e
    · exact .inr (.inr (.inl e))
    · exact .inr (.inr (.inr e))
    · exact .inl e
    · exact .inr (.inl e)

theorem bas {s : List H} {d k : ℕ} {t a b z : W} {r : Finset W}
    (hs : ∀ v ∈ s, actif v = true ∨ v = 0) (gen : Gens d s) (budget : d+(k+1) ≤ 11)
    (ht : t = cible ∨ t = ~~~cible) (ha : a ∈ pool s) (hb : b ∈ pool s) (ne : a ≠ b)
    (hz : z ∈ basicOps a b) (hznew : z ∉ pool s) (lo : (∃ i, a = low i) ∨ (∃ i, b = low i))
    (he : pool s = insert a (insert b r)) (run : live basicOps t k (insert z r)) : False := by
  obtain ⟨p,hp,hg,hd⟩ := basPlan hs ht ha hb ne hz hznew lo he run
  obtain ⟨av,init,hhaut,prefixe⟩ := gen
  have test : ∀ p, lowMap p (basG p) = none ∧ lowMap p (basD p) = none ∧ basG p ≠ basD p := by decide
  have zéroG : projL p (low (basG p)) = 0 := by rw [lowL,(test p).1]; rfl
  have zéroD : projL p (low (basD p)) = 0 := by rw [lowL,(test p).2.1]; rfl
  have hgrat : projL p a = 0 ∨ projL p b = 0 := by
    rcases hp with e|e|e|e
    · exact .inl (e ▸ zéroG)
    · exact .inl (e ▸ zéroD)
    · exact .inr (e ▸ zéroG)
    · exact .inr (e ▸ zéroD)
  have hpool (w : W) (hw : w ∈ pool s) : holds av (projL p w) := by
    rcases basPool.mp hw with ⟨i,rfl⟩|⟨h,hh,rfl⟩
    · rw [lowL]; cases eq : lowMap p i with
      | none => exact .inl rfl
      | some j =>
        have allin : ∀ j, vinput j ∈ ins_fffefee8.toFinset := by decide +kernel
        exact .inr (.inr ⟨_,init (allin j),.inl rfl⟩)
    · rw [highL]; exact hhaut h hh
  have hafter (w : W) (hw : w ∈ insert z r) : holds av (projL p w) := by
    rcases Finset.mem_insert.mp hw with rfl|hr
    · exact mem_ops_zero (hpool a ha) (hpool b hb) hgrat (homL p a b _ hz)
    · apply hpool; rw [he]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)
  have but : projL p t = goal ∨ projL p t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact .inl (cibleL p).1
    · exact .inr (cibleL p).2
  have nc : projL p t ≠ 0 ∧ projL p t ≠ ~~~0 := by
    rcases but with e|e <;> rw [e] <;> decide +kernel
  let cs := (insert z r).filter (fun w => projL p w = 0 ∨ projL p w = ~~~0)
  have compte : 2 ≤ cs.card := by
    have sub : {low (basG p), low (basD p)} ⊆ cs := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|hsing
      · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hg,.inl zéroG⟩
      · rw [Finset.mem_singleton.mp hsing]
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hd,.inl zéroD⟩
    simpa only [Finset.card_pair (fun e => (test p).2.2 (basInj e))] using Finset.card_le_card sub
  have borne : cs.card ≤ k := assez (homL p) run nc
  have preuve : SignedBuild (k - cs.card) av (projL p t) := multi (homL p) run nc hafter
  exact noSigned8 (by omega : d + (k - cs.card) ≤ 8) but (prefixe _ _ preuve)

open PEqualNP.CircuitLowerBounds

def fil (i : Fin 7) : W := tab fun k => k.val.testBit i.val
def entree : List W := List.ofFn fil
def bitlu (k : Fin 512) (w : W) := w[k.val]
def pas (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem lu (w : List W) (i : ℕ) (k : Fin 512) : (w.map (bitlu k)).getD i false = bitlu k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt h),bitlu]

theorem compileCible (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g) (w : List W) (av : Finset W)
    (hw : ∀ u ∈ w, holds av u) (he : ∀ k, (gs.foldl pas (w.map (bitlu k))).getD o false = bitlu k cible) :
    SignedBuild (binaryCost gs) av cible := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD o 0 = cible := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil,lu,bitlu] using he ⟨i,hi⟩
    exact sb_zero (hv ▸ available_read hw o)
  | cons g gs ih =>
    let z := action w g
    have stepOK (k : Fin 512) : pas (w.map (bitlu k)) g = (w ++ [z]).map (bitlu k) :=
      action_spec w g (hg g (by simp)) k
    have cont (A : Finset W) (hs : av ⊆ A) (hz : holds A z) : SignedBuild (binaryCost gs) A cible := by
      apply ih (fun g' hm => hg g' (List.mem_cons_of_mem _ hm)) (w ++ [z]) A
      · intro u hu; rcases List.mem_append.mp hu with h|h
        · exact sb_holds_mono hs (hw u h)
        · exact List.mem_singleton.mp h ▸ hz
      · intro k; simpa only [List.foldl_cons,stepOK] using he k
    have act := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at act
      simpa [binaryCost,neg] using cont av (fun _ h => h) act
    · simp only [neg,ite_true] at act
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]; exact sb_advance act cont

theorem septInit : entree.toFinset = pool start := by
  have e0 : low 0 = fil 0 := rfl
  have e1 : low 1 = fil 1 := rfl
  have e2 : low 2 = fil 2 := rfl
  have e3 : low 3 = fil 3 := rfl
  have h4 : high 170 = fil 4 := by decide +kernel
  have h5 : high 204 = fil 5 := by decide +kernel
  have h6 : high 240 = fil 6 := by decide +kernel
  change ([fil 0,fil 1,fil 2,fil 3,fil 4,fil 5,fil 6] : List W).toFinset = [low 0,low 1,low 2,low 3,high 170,high 204,high 240].toFinset
  rw [e0,e1,e2,e3,h4,h5,h6]

theorem entree_bits (k : Fin 512) : entree.map (bitlu k) = List.ofFn (fun i : Fin 7 => k.val.testBit i.val) := by
  simp only [entree,List.map_ofFn,Function.comp_def,fil,bitlu,tab_bit]

set_option maxRecDepth 10000 in
theorem liaison (k : Fin 512) : PEqualNP.Outside.L_meta_10462.but (fun i : Fin 7 => k.val.testBit i.val) = bitlu k cible := by
  have e : ∀ (x : Fin 7 → Bool), PEqualNP.Outside.L_meta_10462.but x = (((x 0 || x 1) && (x 3 || x 4 || x 5 || x 6)) || ((x 2 || x 3) && (x 0 || x 4 || x 5 || x 6)) || (x 4 && x 5) || ((x 4 || x 5) && x 6)) := by decide +kernel
  rw [e]; exact (tab_bit (fun j => calcul j.val) k).symm

def rA (i : Fin 7) : Fin 512 := ![4,8,1,1,1,1,1] i
def rB (i : Fin 7) : Fin 512 := ![5,10,5,9,17,33,65] i
def ecart (i : Fin 7) (w : W) : Prop := w[(rA i).val] ≠ w[(rB i).val]

theorem transmet (i : Fin 7) : ∀ a b, ∀ z ∈ basicOps a b, ecart i z → ecart i a ∨ ecart i b := by
  intro a b z hz; contrapose!; simp only [ecart,not_not]; rintro ⟨ha,hb⟩
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,ha,hb]

theorem necessaires {t : W} {s : Finset W} {k : ℕ} (ht : t = cible ∨ t = ~~~cible)
    (hs : s ⊆ entree.toFinset) (run : live basicOps t k s) : s = pool start := by
  rw [← septInit]; apply Finset.Subset.antisymm hs
  intro v hv; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hv)
  have sens : ∀ i, ecart i cible ∧ ecart i (~~~cible) := by
    intro i; simp only [ecart,cible,BitVec.getElem_not,tab_bit]; fin_cases i <;> decide +kernel
  obtain ⟨w,hw,dw⟩ := live_separates _ (ht.elim (fun e => e ▸ (sens i).1) (fun e => e ▸ (sens i).2)) (transmet i) run
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (hs hw))
  have uniq : ∀ i j : Fin 7, ecart i (fil j) → i = j := by
    simp only [ecart,fil,tab_bit]; decide +kernel
  exact (uniq i j dw).symm ▸ hw

theorem taille {gs : List Gate} {o : ℕ} (mort : Mort 0 start) (admis : ∀ g ∈ gs, legal g) (bon : PEqualNP.Outside.L_meta_10462.calcule gs o) : 12 ≤ binaryCost gs := by
  by_contra! petit
  have h := compileCible gs o admis entree entree.toFinset (fun w hw => .inr (.inr ⟨w,List.mem_toFinset.mpr hw,.inl rfl⟩))
    (fun k => by change (Circuit.mk gs o).eval (entree.map (bitlu k)) = bitlu k cible; rw [entree_bits]; exact (bon _).trans (liaison k))
  have nc : cible ≠ 0 ∧ cible ≠ ~~~0 := by decide +kernel
  have ex : ∃ t, (t = cible ∨ t = ~~~cible) ∧ build basicOps t (binaryCost gs) entree.toFinset := by
    rcases h with h|h|h|h
    · exact (nc.1 h).elim
    · exact (nc.2 h).elim
    · exact ⟨_,.inl rfl,h⟩
    · exact ⟨_,.inr rfl,h⟩
  obtain ⟨t,ht,hb⟩ := ex
  obtain ⟨s,hs,hl⟩ := compress hb
  exact mort _ _ (by omega) ht (necessaires ht hs hl ▸ hl)

theorem suffit (mort : Mort 0 start) {gs : List Gate} {o : ℕ} (admis : ∀ g ∈ gs, legal g) (bon : PEqualNP.Outside.L_meta_10462.calcule gs o) :
    ∃ ds p, PEqualNP.Outside.L_meta_10462.mono ds ∧ ds.length ≤ gs.length ∧ PEqualNP.Outside.L_meta_10462.calcule ds p := by
  by_contra h
  obtain ⟨upper,g,mem,op⟩ := PEqualNP.Outside.L_meta_10462.remplace13 admis bon h
  have lb := taille mort admis bon
  have strict : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,mem,by simp [isBinary,op]⟩
  omega

def couplesH : List (ℕ × ℕ) := [(0,1),(0,2),(0,4),(0,3),(0,5),(0,6),(0,7),(1,3),(1,5),(1,6),(1,7),(2,3),(2,5),(2,6),(2,7),(4,3),(4,5),(4,6),(4,7)]

def confondH (s : List H) : Bool :=
  couplesH.any fun (u,v) => s.all fun h => h.getLsbD u == h.getLsbD v

def extraitH (p : Fin 3) (h : H) : BitVec 4 :=
  let n := h.toNat
  BitVec.ofNat 4 (if p = 0 then
    (n &&& 1) ||| ((n >>> 1) &&& 2) ||| ((n >>> 2) &&& 4) ||| ((n >>> 3) &&& 8)
  else if p = 1 then (n &&& 3) ||| ((n >>> 2) &&& 12)
  else n &&& 15)

def codeH (u : BitVec 4) : BitVec 5 :=
  match (if u.getLsbD 0 then ~~~u else u).toNat with
  | 2 => 1 | 4 => 2 | 8 => 4 | 14 => 8 | 6 => 16 | _ => 0

def masqueH (p : Fin 3) (s : List H) : BitVec 5 :=
  (s.map fun h => codeH (extraitH p h)).foldr (· ||| ·) 0

def cstH (p : Fin 3) (h : H) : Bool :=
  let u := extraitH p h
  u == 0 || u == 15

def coutH (m : BitVec 5) : ℕ :=
  [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,3,3,3,3,3,4,4,4,3,4,4,4,3,4,4,5].getD m.toNat 0

def borneH (p : Fin 3) (d : ℕ) (s : List H) : Bool :=
  decide (12 + coutH (masqueH p s) ≤ d + 9 + s.countP (cstH p))

def coupe (d : ℕ) (s : List H) : Bool :=
  confondH s || borneH 0 d s || borneH 1 d s || borneH 2 d s

abbrev U4H := BitVec 4
abbrev PGH := Fin 6

def parentsH : PGH → U4H × U4H × U4H :=
  ![(10,12,2),(10,12,4),(10,12,8),(10,12,14),(2,4,6),(14,8,6)]

def planH (m : BitVec 5) : List PGH :=
  [[],[0],[1],[0,1],[2],[0,2],[1,2],[0,1,2],[3],[0,3],[1,3],[0,1,3],[2,3],[0,2,3],[1,2,3],[0,1,2,3],[0,1,4],[0,1,4],[0,1,4],[0,1,4],[2,3,5],[0,1,2,4],[0,1,2,4],[0,1,2,4],[2,3,5],[0,1,3,4],[0,1,3,4],[0,1,3,4],[2,3,5],[0,2,3,5],[1,2,3,5],[0,1,2,3,4]].getD m.toNat []

def normalH (u : U4H) := if u.getLsbD 0 then ~~~u else u

def valideH (m : BitVec 5) : List PGH → List U4H → Bool
  | [], a => (List.finRange 16).all fun i =>
      let u := BitVec.ofFin (w := 4) i
      codeH u &&& m != codeH u || a.contains (normalH u)
  | g :: gs, a =>
      a.contains (parentsH g).1 && a.contains (parentsH g).2.1 &&
        valideH m gs ((parentsH g).2.2 :: a)

set_option maxRecDepth 6000 in
theorem tousPlansH : ∀ m, (planH m).length = coutH m ∧ valideH m (planH m) [0,10,12] = true := by
  decide +kernel

theorem paire_ltH : ∀ x, paire x < 4 := by decide +kernel

theorem andTableH (u v : U4H) : table2 (u &&& v) = table2 u &&& table2 v := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  let k : Fin 512 := ⟨i,hi⟩
  change (table2 _)[k.val] = (_ &&& _)[k.val]
  simp only [table2,tab_bit,BitVec.getElem_and,BitVec.getLsbD_and]

theorem orTableH (u v : U4H) : table2 (u ||| v) = table2 u ||| table2 v := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  let k : Fin 512 := ⟨i,hi⟩
  change (table2 _)[k.val] = (_ ||| _)[k.val]
  simp only [table2,tab_bit,BitVec.getElem_or,BitVec.getLsbD_or]

theorem notTableH (u : U4H) : table2 (~~~u) = ~~~table2 u := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  let k : Fin 512 := ⟨i,hi⟩
  change (table2 _)[k.val] = (~~~_)[k.val]
  simp only [table2,tab_bit,BitVec.getElem_not,BitVec.getLsbD_not,paire_ltH,decide_true,Bool.true_and]

theorem portesBonnesH (g : PGH) : table2 (parentsH g).2.2 ∈
    basicOps (table2 (parentsH g).1) (table2 (parentsH g).2.1) := by
  have tous : ∀ (i : PGH), (parentsH i).2.2 ∈
      [(parentsH i).1 &&& (parentsH i).2.1, (parentsH i).1 ||| (parentsH i).2.1,
       (parentsH i).1 &&& ~~~(parentsH i).2.1, (parentsH i).2.1 &&& ~~~(parentsH i).1] := by decide +kernel
  have hp := tous g
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  rcases hp with h|h|h|h <;> simp [h,andTableH,orTableH,notTableH]

theorem rejoueH {m : BitVec 5} {gs : List PGH} {a : List U4H} {av : Finset W} {k : ℕ} {t : W}
    (ok : valideH m gs a = true) (ha : ∀ u ∈ a, holds av (table2 u))
    (suite : ∀ av' : Finset W, av ⊆ av' →
      (∀ u, codeH u &&& m = codeH u → holds av' (table2 u)) → SignedBuild k av' t) :
    SignedBuild (gs.length + k) av t := by
  induction gs generalizing a av with
  | nil =>
    simp only [List.length_nil,Nat.zero_add]
    apply suite av (fun _ h => h)
    intro u hu
    have hv := List.all_eq_true.mp ok u.toFin (List.mem_finRange _)
    change (codeH u &&& m != codeH u || a.contains (normalH u)) = true at hv
    have hmem : normalH u ∈ a := by simpa [hu] using hv
    have hh := ha _ hmem
    unfold normalH at hh
    split at hh
    · have hn := holds_not hh
      rwa [notTableH,BitVec.not_not] at hn
    · exact hh
  | cons g gs ih =>
    simp only [valideH,Bool.and_eq_true,List.contains_iff_mem] at ok
    change SignedBuild (gs.length + 1 + k) av t
    rw [show gs.length + 1 + k = (gs.length + k) + 1 by omega]
    apply sb_advance (mem_ops_reach (ha _ ok.1.1) (ha _ ok.1.2) (portesBonnesH g))
    intro av' sub hw
    apply ih ok.2
    · intro u hu
      rcases List.mem_cons.mp hu with rfl|hu
      · exact hw
      · exact sb_holds_mono sub (ha _ hu)
    · intro av'' sub' hu
      exact suite av'' (sub.trans sub') hu

theorem tablesDepartH : table2 0 = 0 ∧ table2 10 = vinput 3 ∧ table2 12 = vinput 4 := by
  have ex : ∀ x, (10 : U4H).getLsbD (paire x) = x 3 ∧ (12 : U4H).getLsbD (paire x) = x 4 := by decide +kernel
  refine ⟨?_,?_,?_⟩ <;> apply BitVec.eq_of_getElem_eq <;> intro i hi
  · let k : Fin 512 := ⟨i,hi⟩
    change (table2 0)[k.val] = (0 : W)[k.val]
    exact (tab_bit _ k).trans ((BitVec.getLsbD_zero (w := 4)).trans (BitVec.getElem_zero k.isLt).symm)
  · let k : Fin 512 := ⟨i,hi⟩
    exact (tab_bit _ k).trans (ex (xk k)).1
  · let k : Fin 512 := ⟨i,hi⟩
    exact (tab_bit _ k).trans (ex (xk k)).2

theorem departH : ∀ i : Fin 5, vinput i ∈ ins_fffefee8.toFinset := by decide +kernel

theorem prefixeH (m : BitVec 5) {k : ℕ} {t : W}
    (suite : ∀ av : Finset W, ins_fffefee8.toFinset ⊆ av →
      (∀ u, codeH u &&& m = codeH u → holds av (table2 u)) → SignedBuild k av t) :
    SignedBuild (coutH m + k) ins_fffefee8.toFinset t := by
  rw [← (tousPlansH m).1]
  apply rejoueH (tousPlansH m).2 _ suite
  intro u hu
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl|rfl|rfl
  · exact .inl tablesDepartH.1
  · exact .inr (.inr ⟨_,departH 3,.inl tablesDepartH.2.1⟩)
  · exact .inr (.inr ⟨_,departH 4,.inl tablesDepartH.2.2⟩)

theorem extraireH : ∀ p h, sous p h = extraitH p h := by decide +kernel

theorem dansMasqueH (p : Fin 3) {h : H} {s : List H} (hs : h ∈ s) :
    codeH (extraitH p h) &&& masqueH p s = codeH (extraitH p h) := by
  induction s with
  | nil => simp at hs
  | cons w s ih =>
    change _ &&& (codeH (extraitH p w) ||| masqueH p s) = _
    rcases List.mem_cons.mp hs with rfl|hh
    · apply BitVec.eq_of_getElem_eq
      intro i hi
      simp [BitVec.getElem_and,BitVec.getElem_or]
      exact Or.inl
    · have sub := ih hh
      apply BitVec.eq_of_getElem_eq
      intro i hi
      have e := congrArg (fun b : BitVec 5 => b[i]) sub
      simp only [BitVec.getElem_and,BitVec.getElem_or] at e ⊢
      cases hh' : (codeH (extraitH p h))[i] <;> simp_all

theorem highInjH : Function.Injective high := by
  intro a b eq
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let k : Fin 512 := ⟨16*i,by omega⟩
  have e := congrArg (fun w : W => w[k.val]) eq
  change (high a)[k.val] = (high b)[k.val] at e
  simp only [high,tab_bit] at e
  have ek : (k.val / 16) % 8 = i := by dsimp [k]; omega
  simpa only [ek,BitVec.getLsbD_eq_getElem hi] using e

theorem poolIciH {s : List H} {w : W} (hw : w ∈ pool s) :
    (∃ i, low i = w) ∨ ∃ h ∈ s, high h = w := by
  simpa only [pool,List.mem_toFinset,List.mem_append,List.mem_ofFn,List.mem_map,Set.mem_range] using hw

theorem constBasH {p : Fin 3} {h : H} (hh : cstH p h = true) :
    projH p (high h) = 0 ∨ projH p (high h) = ~~~0 := by
  rw [highH,extraireH]
  simp only [cstH,Bool.or_eq_true,beq_iff_eq] at hh
  rcases hh with hz|hz
  · rw [hz]; exact .inl tablesDepartH.1
  · rw [hz]
    right
    change table2 (~~~(0 : U4H)) = _
    rw [notTableH,tablesDepartH.1]

theorem compteH (p : Fin 3) {s : List H} (hn : s.Nodup) :
    s.countP (cstH p) ≤ ((pool s).filter (fun w => projH p w = 0 ∨ projH p w = ~~~0)).card := by
  let a := (s.filter (cstH p)).toFinset
  have ha : (a.image high).card = s.countP (cstH p) := by
    rw [Finset.card_image_of_injective _ highInjH,List.countP_eq_length_filter]
    exact List.toFinset_card_of_nodup (hn.filter _)
  rw [← ha]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨hs,hc⟩ := List.mem_filter.mp (List.mem_toFinset.mp hh)
  apply Finset.mem_filter.mpr
  exact ⟨List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_map.mpr ⟨h,hs,rfl⟩)),constBasH hc⟩

theorem borneBonneH (p : Fin 3) {d : ℕ} {s : List H} (hn : s.Nodup)
    (hb : borneH p d s = true) : Mort d s := by
  intro k t budget ht run
  have but : projH p t = goal ∨ projH p t = ~~~goal := by
    rcases ht with rfl|rfl
    · exact .inl (cibleH p).1
    · exact .inr (cibleH p).2
  have nc : projH p t ≠ 0 ∧ projH p t ≠ ~~~0 := by
    rcases but with h|h <;> rw [h] <;> decide +kernel
  have zle := assez (homH p) run nc
  have cnt := compteH p hn
  have cond : 12 + coutH (masqueH p s) ≤ d + 9 + s.countP (cstH p) := of_decide_eq_true hb
  apply noSigned8 (k := coutH (masqueH p s) + (k - ((pool s).filter (fun w => projH p w = 0 ∨ projH p w = ~~~0)).card)) (by omega) but
  apply prefixeH
  intro av sub hab
  apply multi (homH p) run nc
  intro w hw
  rcases poolIciH hw with ⟨i,rfl⟩|⟨h,hh,rfl⟩
  · rw [lowH]; exact .inr (.inr ⟨_,sub (departH _),.inl rfl⟩)
  · rw [highH,extraireH]; exact hab _ (dansMasqueH p hh)

def ligneCoupleH (u v : ℕ) : Fin 512 :=
  ⟨(16 * v + (if u = 0 then 1 else 0)) % 512, Nat.mod_lt _ (by decide)⟩

theorem couplesBonsH : ∀ c ∈ couplesH,
    let i := ligneCoupleH c.1 c.1
    let j := ligneCoupleH c.1 c.2
    calcul i.val ≠ calcul j.val ∧
    (∀ b : Fin 4, i.val.testBit b.val = j.val.testBit b.val) ∧
    (i.val / 16) % 8 = c.1 ∧ (j.val / 16) % 8 = c.2 := by
  decide +kernel

theorem confusionBonneH {d : ℕ} {s : List H} (hc : confondH s = true) : Mort d s := by
  intro k t _ ht run
  obtain ⟨⟨u,v⟩,hm,h⟩ := List.any_eq_true.mp hc
  let i := ligneCoupleH u u
  let j := ligneCoupleH u v
  obtain ⟨hd,hl,hu,hv⟩ := couplesBonsH (u,v) hm
  let D := fun w : W => w[i.val] ≠ w[j.val]
  have cd : cible[i.val] ≠ cible[j.val] := by simpa only [cible,tab_bit] using hd
  have dt : D t := by
    change t[i.val] ≠ t[j.val]
    rcases ht with rfl|rfl
    · exact cd
    · intro e
      apply cd
      apply Bool.not_inj
      simpa only [BitVec.getElem_not] using e
  have hered : ∀ a b, ∀ z ∈ basicOps a b, D z → D a ∨ D b := by
    intro a b z hz
    contrapose!
    simp only [D,not_not]
    rintro ⟨ha,hb⟩
    simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,ha,hb]
  obtain ⟨w,hw,dw⟩ := live_separates D dt hered run
  apply dw
  rcases poolIciH hw with ⟨b,rfl⟩|⟨a,ha,rfl⟩
  · simpa only [low,tab_bit] using hl b
  · have ab : a.getLsbD u = a.getLsbD v := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
    simpa only [high,tab_bit,i,j,hu,hv] using ab

theorem coupe_bonne {d : ℕ} {s : List H} (hn : s.Nodup) (hc : coupe d s = true) : Mort d s := by
  simp only [coupe,Bool.or_eq_true] at hc
  rcases hc with ((hc|hc)|hc)|hc
  · exact confusionBonneH hc
  · exact borneBonneH _ hn hc
  · exact borneBonneH _ hn hc
  · exact borneBonneH _ hn hc

private theorem pc_tab (f : Fin 512 → Bool) (k : Fin 512) :
    (tab f)[k.val] = f k := by
  rw [← BitVec.getLsbD_eq_getElem k.isLt]
  simp only [tab, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, k.isLt, dite_eq_left, Option.getD_some]

private theorem pc_inj : Function.Injective high := by
  intro a b e
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let k : Fin 512 := ⟨16*i, by omega⟩
  have h := congrArg (fun w : W => w[k.val]) e
  simp only [high, pc_tab] at h
  have hk : k.val / 16 % 8 = i := by dsimp [k]; omega
  simpa only [hk, BitVec.getLsbD_eq_getElem hi] using h

private theorem pc_disj (i : Fin 4) (a : H) : low i ≠ high a := by
  intro e
  let k : Fin 512 := ⟨2^i.val, by fin_cases i <;> decide⟩
  have h := congrArg (fun w : W => w[k.val]) e
  let o : Fin 512 := 0
  have h0 := congrArg (fun w : W => w[o.val]) e
  simp only [low, high, pc_tab] at h h0
  have e₁ : k.val.testBit i.val = true := by change (2^i.val : ℕ).testBit i.val = true; fin_cases i <;> decide
  have e₂ : k.val / 16 % 8 = 0 := by change 2^i.val / 16 % 8 = 0; fin_cases i <;> decide
  have e₃ : o.val.testBit i.val = false := by fin_cases i <;> decide
  rw [e₁,e₂] at h
  rw [e₃] at h0
  have e₄ : o.val / 16 % 8 = 0 := by decide
  rw [e₄] at h0
  exact Bool.noConfusion (h.trans h0.symm)

private theorem pc_mem {w : W} {s : List H} :
    w ∈ pool s ↔ (∃ i, w = low i) ∨ ∃ a ∈ s, w = high a := by
  simp only [pool,List.mem_toFinset,List.mem_append,List.mem_ofFn,List.mem_map]
  grind

private theorem pc_nontriv (s : List H) (t : W) : pool s ≠ {t} := by
  intro e
  have h (i : Fin 4) : low i = t := by
    have h := (pc_mem (s := s) (w := low i)).mpr (Or.inl ⟨i,rfl⟩)
    simpa only [e, Finset.mem_singleton] using h
  have e' := (h 0).trans (h 1).symm
  let k : Fin 512 := 1
  have hh := congrArg (fun w : W => w[k.val]) e'
  simp only [low, pc_tab] at hh
  exact (by decide : ¬ (1 : ℕ).testBit 0 = (1 : ℕ).testBit 1) hh

def pcOps (a b : H) : List H := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]

private theorem pc_ops (a b : H) : ops (high a) (high b) = (pcOps a b).map high := by
  have ht (u v : H) : high (u &&& v) = high u &&& high v := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    let k : Fin 512 := ⟨j,hj⟩
    change (high _)[k.val] = (high u &&& high v)[k.val]
    simp only [BitVec.getElem_and,high,pc_tab,BitVec.getLsbD_and]
  have ho (u v : H) : high (u ||| v) = high u ||| high v := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    let k : Fin 512 := ⟨j,hj⟩
    change (high _)[k.val] = (high u ||| high v)[k.val]
    simp only [BitVec.getElem_or,high,pc_tab,BitVec.getLsbD_or]
  have hc (u : H) : high (~~~u) = ~~~high u := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    let k : Fin 512 := ⟨j,hj⟩
    change (high _)[k.val] = (~~~high u)[k.val]
    simp only [BitVec.getElem_not,high,pc_tab,BitVec.getLsbD_not,
      Nat.mod_lt _ (by decide : 0 < 8), decide_true, Bool.true_and]
  simp [ops,pcOps,ht,ho,hc]

def pcGardes (a b : H) (ka kb : Bool) (s : List H) : List H :=
  s.filter fun v => (v != a || ka) && (v != b || kb)

def pcFils (a b z : H) (ka kb : Bool) (s : List H) : List H :=
  (pcGardes a b ka kb s).orderedInsert (· ≤ ·) z

def pcEnfants (s : List H) : List (List H) := do
  let a ← s
  let b ← s
  guard (a < b)
  let z ← pcOps a b
  guard (z ∉ s)
  let ka ← [false,true]
  let kb ← [false,true]
  pure (pcFils a b z ka kb s)

private theorem pc_fils_mem {a b z : H} {s : List H} (ka kb : Bool)
    (ha : a ∈ s) (hb : b ∈ s) (hlt : a < b) (hz : z ∈ pcOps a b) (hn : z ∉ s) :
    pcFils a b z ka kb s ∈ pcEnfants s := by
  simp only [pcEnfants, List.bind_eq_flatMap, List.mem_flatMap]
  refine ⟨a,ha,b,hb,?_⟩
  cases ka <;> cases kb <;> simp [guard, hlt] <;> exact ⟨z,hz,by simp [hn]⟩

private theorem pc_transition {a b : H} {w : W} {s : List H} {r : Finset W}
    (hd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s) (hlt : a < b)
    (hw : w ∈ basicOps (high a) (high b)) (hout : w ∉ pool s)
    (he : pool s = insert (high a) (insert (high b) r)) :
    ∃ z ∈ pcOps a b, ∃ u ∈ pcEnfants s, u.Nodup ∧ pool u = insert w r ∧
      ∀ v ∈ u, v = z ∨ v ∈ s := by
  have hw' := List.mem_toFinset.mp hw
  rw [pc_ops] at hw'
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw'
  have hout' : z ∉ s := fun h => hout (pc_mem.mpr (.inr ⟨z,h,rfl⟩))
  let ka := decide (high a ∈ r)
  let kb := decide (high b ∈ r)
  let u := pcFils a b z ka kb s
  refine ⟨z,hz,u,pc_fils_mem ka kb ha hb hlt hz hout', ?_, ?_, ?_⟩
  · apply (List.perm_orderedInsert _ _ _).nodup_iff.mpr
    exact List.nodup_cons.mpr ⟨fun h => hout' (List.mem_filter.mp h).1, hd.filter _⟩
  · have lowr (i : Fin 4) : low i ∈ r := by
      have h := (pc_mem (s := s) (w := low i)).mpr (Or.inl ⟨i,rfl⟩)
      simpa only [he,Finset.mem_insert,pc_disj,false_or] using h
    have vpool (v : H) : high v ∈ pool s ↔ v ∈ s := by
      rw [pc_mem]
      constructor
      · rintro (⟨i,hi⟩ | ⟨x,hx,heq⟩)
        · exact False.elim (pc_disj i _ hi.symm)
        · exact pc_inj heq ▸ hx
      · intro h; exact .inr ⟨v,h,rfl⟩
    have hr (v : H) : v ∈ pcGardes a b ka kb s ↔ high v ∈ r := by
      have h := (he ▸ vpool v).symm
      simp only [Finset.mem_insert,pc_inj.eq_iff] at h
      simp only [pcGardes, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
        bne_iff_ne,ka,kb,decide_eq_true_eq]
      by_cases ea : v = a <;> by_cases eb : v = b <;> simp_all
    ext x
    simp only [pc_mem, u, pcFils, List.mem_orderedInsert, hr, Finset.mem_insert]
    constructor
    · rintro (⟨i,rfl⟩ | ⟨v,hh,rfl⟩)
      · exact .inr (lowr i)
      · rcases hh with rfl | hh
        · exact .inl rfl
        · exact .inr hh
    · rintro (rfl | hx)
      · exact .inr ⟨z,.inl rfl,rfl⟩
      · have mem : x ∈ pool s := he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
        rcases pc_mem.mp mem with hh | ⟨v,_,rfl⟩
        · exact .inl hh
        · exact .inr ⟨v,.inr hx,rfl⟩
  · intro v hv
    rcases (List.mem_orderedInsert (· ≤ ·)).mp hv with hh | hh
    · exact .inl hh
    · exact .inr (List.mem_filter.mp hh).1

def pcOuverts : ℕ → List (List H)
  | 0 => [[170,204,240]]
  | 1 => [[170,204,238,240],[170,204,240,250],[170,204,240,252]]
  | 2 => [[204,238,240,250],[170,238,240,252],[170,204,240,254],[170,204,238,240,254],[14,170,204,240],[14,170,204,238,240],[170,204,250,252],[170,204,240,250,254],[50,170,204,240],[50,170,204,240,250],[170,204,240,252,254],[84,170,204,240],[84,170,204,240,252]]
  | 3 => [[238,250,252],[50,238,240,250],[14,204,238,250],[84,238,240,252],[14,170,238,252],[84,204,240,254],[50,170,240,254],[14,170,204,254],[84,204,238,240,254],[50,170,238,240,254],[14,170,204,238,254],[84,204,250,252],[50,170,250,252],[84,204,240,250,254],[50,170,240,250,254],[14,170,204,250,254],[84,204,240,252,254],[50,170,240,252,254],[14,170,204,252,254]]
  | 4 => [[14,50,238,250],[14,84,238,252],[50,84,240,254],[14,84,204,254],[14,50,170,254],[50,84,238,240],[50,84,238,240,254],[14,84,204,238,254],[14,50,170,238,254],[50,84,250,252],[50,84,240,250,254],[14,84,204,250],[14,84,204,250,254],[14,50,170,250,254],[50,84,240,252,254],[14,84,204,252,254],[14,50,170,252],[14,50,170,252,254]]
  | 5 => [[14,50,84,254],[14,50,84,238],[14,50,84,238,254],[14,50,84,250],[14,50,84,250,254],[14,50,84,252],[14,50,84,252,254]]
  | _ => []

def pcLigne (d : ℕ) (s : List H) : Bool :=
  (s.all fun h => actif h || h == 0) &&
    (pcEnfants s).all fun u => coupe (d+1) u || (pcOuverts (d+1)).contains u


private theorem pc_ok_0_0 : pcLigne 0 [170,204,240] = true := by decide +kernel

private theorem pc_niveau_0 : (pcOuverts 0).all (pcLigne 0) = true := by
  simp only [pcOuverts, List.all_cons, List.all_nil, Bool.true_and,
    pc_ok_0_0]

private theorem pc_ok_1_0 : pcLigne 1 [170,204,238,240] = true := by decide +kernel
private theorem pc_ok_1_1 : pcLigne 1 [170,204,240,250] = true := by decide +kernel
private theorem pc_ok_1_2 : pcLigne 1 [170,204,240,252] = true := by decide +kernel

private theorem pc_niveau_1 : (pcOuverts 1).all (pcLigne 1) = true := by
  simp only [pcOuverts, List.all_cons, List.all_nil, Bool.true_and,
    pc_ok_1_0, pc_ok_1_1, pc_ok_1_2]

private theorem pc_ok_2_0 : pcLigne 2 [204,238,240,250] = true := by decide +kernel
private theorem pc_ok_2_1 : pcLigne 2 [170,238,240,252] = true := by decide +kernel
private theorem pc_ok_2_2 : pcLigne 2 [170,204,240,254] = true := by decide +kernel
private theorem pc_ok_2_3 : pcLigne 2 [170,204,238,240,254] = true := by decide +kernel
private theorem pc_ok_2_4 : pcLigne 2 [14,170,204,240] = true := by decide +kernel
private theorem pc_ok_2_5 : pcLigne 2 [14,170,204,238,240] = true := by decide +kernel
private theorem pc_ok_2_6 : pcLigne 2 [170,204,250,252] = true := by decide +kernel
private theorem pc_ok_2_7 : pcLigne 2 [170,204,240,250,254] = true := by decide +kernel
private theorem pc_ok_2_8 : pcLigne 2 [50,170,204,240] = true := by decide +kernel
private theorem pc_ok_2_9 : pcLigne 2 [50,170,204,240,250] = true := by decide +kernel
private theorem pc_ok_2_10 : pcLigne 2 [170,204,240,252,254] = true := by decide +kernel
private theorem pc_ok_2_11 : pcLigne 2 [84,170,204,240] = true := by decide +kernel
private theorem pc_ok_2_12 : pcLigne 2 [84,170,204,240,252] = true := by decide +kernel

private theorem pc_niveau_2 : (pcOuverts 2).all (pcLigne 2) = true := by
  simp only [pcOuverts, List.all_cons, List.all_nil, Bool.true_and,
    pc_ok_2_0, pc_ok_2_1, pc_ok_2_2, pc_ok_2_3, pc_ok_2_4, pc_ok_2_5, pc_ok_2_6, pc_ok_2_7, pc_ok_2_8, pc_ok_2_9, pc_ok_2_10, pc_ok_2_11, pc_ok_2_12]

private theorem pc_ok_3_0 : pcLigne 3 [238,250,252] = true := by decide +kernel
private theorem pc_ok_3_1 : pcLigne 3 [50,238,240,250] = true := by decide +kernel
private theorem pc_ok_3_2 : pcLigne 3 [14,204,238,250] = true := by decide +kernel
private theorem pc_ok_3_3 : pcLigne 3 [84,238,240,252] = true := by decide +kernel
private theorem pc_ok_3_4 : pcLigne 3 [14,170,238,252] = true := by decide +kernel
private theorem pc_ok_3_5 : pcLigne 3 [84,204,240,254] = true := by decide +kernel
private theorem pc_ok_3_6 : pcLigne 3 [50,170,240,254] = true := by decide +kernel
private theorem pc_ok_3_7 : pcLigne 3 [14,170,204,254] = true := by decide +kernel
private theorem pc_ok_3_8 : pcLigne 3 [84,204,238,240,254] = true := by decide +kernel
private theorem pc_ok_3_9 : pcLigne 3 [50,170,238,240,254] = true := by decide +kernel
private theorem pc_ok_3_10 : pcLigne 3 [14,170,204,238,254] = true := by decide +kernel
private theorem pc_ok_3_11 : pcLigne 3 [84,204,250,252] = true := by decide +kernel
private theorem pc_ok_3_12 : pcLigne 3 [50,170,250,252] = true := by decide +kernel
private theorem pc_ok_3_13 : pcLigne 3 [84,204,240,250,254] = true := by decide +kernel
private theorem pc_ok_3_14 : pcLigne 3 [50,170,240,250,254] = true := by decide +kernel
private theorem pc_ok_3_15 : pcLigne 3 [14,170,204,250,254] = true := by decide +kernel
private theorem pc_ok_3_16 : pcLigne 3 [84,204,240,252,254] = true := by decide +kernel
private theorem pc_ok_3_17 : pcLigne 3 [50,170,240,252,254] = true := by decide +kernel
private theorem pc_ok_3_18 : pcLigne 3 [14,170,204,252,254] = true := by decide +kernel

private theorem pc_niveau_3 : (pcOuverts 3).all (pcLigne 3) = true := by
  simp only [pcOuverts, List.all_cons, List.all_nil, Bool.true_and,
    pc_ok_3_0, pc_ok_3_1, pc_ok_3_2, pc_ok_3_3, pc_ok_3_4, pc_ok_3_5, pc_ok_3_6, pc_ok_3_7, pc_ok_3_8, pc_ok_3_9, pc_ok_3_10, pc_ok_3_11, pc_ok_3_12, pc_ok_3_13, pc_ok_3_14, pc_ok_3_15, pc_ok_3_16, pc_ok_3_17, pc_ok_3_18]

private theorem pc_ok_4_0 : pcLigne 4 [14,50,238,250] = true := by decide +kernel
private theorem pc_ok_4_1 : pcLigne 4 [14,84,238,252] = true := by decide +kernel
private theorem pc_ok_4_2 : pcLigne 4 [50,84,240,254] = true := by decide +kernel
private theorem pc_ok_4_3 : pcLigne 4 [14,84,204,254] = true := by decide +kernel
private theorem pc_ok_4_4 : pcLigne 4 [14,50,170,254] = true := by decide +kernel
private theorem pc_ok_4_5 : pcLigne 4 [50,84,238,240] = true := by decide +kernel
private theorem pc_ok_4_6 : pcLigne 4 [50,84,238,240,254] = true := by decide +kernel
private theorem pc_ok_4_7 : pcLigne 4 [14,84,204,238,254] = true := by decide +kernel
private theorem pc_ok_4_8 : pcLigne 4 [14,50,170,238,254] = true := by decide +kernel
private theorem pc_ok_4_9 : pcLigne 4 [50,84,250,252] = true := by decide +kernel
private theorem pc_ok_4_10 : pcLigne 4 [50,84,240,250,254] = true := by decide +kernel
private theorem pc_ok_4_11 : pcLigne 4 [14,84,204,250] = true := by decide +kernel
private theorem pc_ok_4_12 : pcLigne 4 [14,84,204,250,254] = true := by decide +kernel
private theorem pc_ok_4_13 : pcLigne 4 [14,50,170,250,254] = true := by decide +kernel
private theorem pc_ok_4_14 : pcLigne 4 [50,84,240,252,254] = true := by decide +kernel
private theorem pc_ok_4_15 : pcLigne 4 [14,84,204,252,254] = true := by decide +kernel
private theorem pc_ok_4_16 : pcLigne 4 [14,50,170,252] = true := by decide +kernel
private theorem pc_ok_4_17 : pcLigne 4 [14,50,170,252,254] = true := by decide +kernel

private theorem pc_niveau_4 : (pcOuverts 4).all (pcLigne 4) = true := by
  simp only [pcOuverts, List.all_cons, List.all_nil, Bool.true_and,
    pc_ok_4_0, pc_ok_4_1, pc_ok_4_2, pc_ok_4_3, pc_ok_4_4, pc_ok_4_5, pc_ok_4_6, pc_ok_4_7, pc_ok_4_8, pc_ok_4_9, pc_ok_4_10, pc_ok_4_11, pc_ok_4_12, pc_ok_4_13, pc_ok_4_14, pc_ok_4_15, pc_ok_4_16, pc_ok_4_17]

private theorem pc_ok_5_0 : pcLigne 5 [14,50,84,254] = true := by decide +kernel
private theorem pc_ok_5_1 : pcLigne 5 [14,50,84,238] = true := by decide +kernel
private theorem pc_ok_5_2 : pcLigne 5 [14,50,84,238,254] = true := by decide +kernel
private theorem pc_ok_5_3 : pcLigne 5 [14,50,84,250] = true := by decide +kernel
private theorem pc_ok_5_4 : pcLigne 5 [14,50,84,250,254] = true := by decide +kernel
private theorem pc_ok_5_5 : pcLigne 5 [14,50,84,252] = true := by decide +kernel
private theorem pc_ok_5_6 : pcLigne 5 [14,50,84,252,254] = true := by decide +kernel

private theorem pc_niveau_5 : (pcOuverts 5).all (pcLigne 5) = true := by
  simp only [pcOuverts, List.all_cons, List.all_nil, Bool.true_and,
    pc_ok_5_0, pc_ok_5_1, pc_ok_5_2, pc_ok_5_3, pc_ok_5_4, pc_ok_5_5, pc_ok_5_6]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem pc_cert (d : ℕ) (s : List H) (hs : s ∈ pcOuverts d) : pcLigne d s = true := by
  have hd : d < 6 := by
    by_contra! h
    obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le' h
    simp [pcOuverts] at hs
  let i : Fin 6 := ⟨d,hd⟩
  have h : ∀ j : Fin 6, (pcOuverts j.val).all (pcLigne j.val) = true := by
    intro j; fin_cases j
    · exact pc_niveau_0
    · exact pc_niveau_1
    · exact pc_niveau_2
    · exact pc_niveau_3
    · exact pc_niveau_4
    · exact pc_niveau_5
  exact List.all_eq_true.mp (h i) s hs

theorem initial (base : Gens 0 start)
    (rejet : ∀ (d : ℕ) (s : List H), s.Nodup → coupe d s = true → Mort d s)
    (bas : ∀ {s : List H} {d k : ℕ} {t a b z : W} {r : Finset W},
      (∀ v ∈ s, actif v = true ∨ v = 0) → Gens d s → d+(k+1) ≤ 11 →
      (t = cible ∨ t = ~~~cible) → a ∈ pool s → b ∈ pool s → a ≠ b →
      z ∈ basicOps a b → z ∉ pool s → ((∃ i, a = low i) ∨ (∃ i, b = low i)) →
      pool s = insert a (insert b r) → live basicOps t k (insert z r) → False) :
    Mort 0 start := by
  have go : ∀ k d s, s ∈ pcOuverts d → s.Nodup → Gens d s →
      ∀ t, d+k ≤ 11 → (t = cible ∨ t = ~~~cible) → live basicOps t k (pool s) → False := by
    intro k
    induction k with
    | zero =>
      intro d s _ _ _ t _ _ run
      exact pc_nontriv s t run
    | succ k ih =>
      intro d s hs hn hg t bud ht run
      rcases first_live run with h | ⟨a,ha,b,hb,ne,w,hw,hwout,r,he,tail⟩
      · exact pc_nontriv s t h
      have cert := pc_cert d s hs
      simp only [pcLigne,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,
        List.contains_iff_mem] at cert
      by_cases lo : (∃ i, a = low i) ∨ (∃ i, b = low i)
      · exact bas cert.1 hg bud ht ha hb ne hw hwout lo he tail
      obtain ⟨x,hx,rfl⟩ := (pc_mem.mp ha).resolve_left fun h => lo (.inl h)
      obtain ⟨y,hy,rfl⟩ := (pc_mem.mp hb).resolve_left fun h => lo (.inr h)
      have branch {x y : H} (hx : x ∈ s) (hy : y ∈ s) (hlt : x < y)
          (hw : w ∈ basicOps (high x) (high y))
          (he : pool s = insert (high x) (insert (high y) r)) : False := by
        obtain ⟨z,hz,u,hu,un,eu,sub⟩ := pc_transition hn hx hy hlt hw hwout he
        have run' : live basicOps t k (pool u) := eu ▸ tail
        rcases cert.2 u hu with cut | ouvert
        · exact rejet (d+1) u un cut k t (by omega) ht run'
        · exact ih (d+1) u ouvert un (gensNext hg hx hy hz sub) t (by omega) ht run'
      have n : x.toNat ≠ y.toNat := fun h => ne (congrArg high (BitVec.toNat_inj.mp h))
      rcases lt_or_gt_of_ne n with h | h
      · exact branch hx hy (BitVec.lt_def.mpr h) hw he
      · exact branch hy hx (BitVec.lt_def.mpr h) (by rw [ops_swap]; exact hw) (he.trans (Finset.insert_comm ..))
  intro k t bud ht run
  exact go k 0 start (by decide) (by decide) base t bud ht run

theorem initialComplet : Mort 0 start := initial gensInit (fun _ _ => coupe_bonne) bas

theorem etatInitial : Mort 0 start := initialComplet

end PEqualNP.Outside.L_meta_10462

theorem PEqualNP.Outside.L_meta_10462 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hg _ he
  exact PEqualNP.Outside.L_meta_10462.suffit PEqualNP.Outside.L_meta_10462.etatInitial hg he
