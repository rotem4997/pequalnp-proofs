import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12296

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

abbrev W := BitVec 120
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 60 := ((x >>> 60) ^^^ x).setWidth 60
def cuts (ws : List W) : BitVec 60 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 60) ++ (0 : BitVec 60)
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

def differs (i : Fin 60) (w : W) : Prop :=
  w.getLsbD (60+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 60) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 60+i.val < 120 := by omega
  have hi' : i.val < 120 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 60) :
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
  change (cuts ws)[j] = (BitVec.allOnes 60)[j]
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
  · change reachable av (BitVec.allOnes 120 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 120)
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

def bit120 (k : Fin 120) (z : W) : Bool := z[k.val]

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

def k4inputs : List W := [0x1fffc0007fff108421084210842, 0x7fe007c1ff801f210842108421084, 0xf83e0f83e0f83e0421084210842108, 0xffc1f003ff07c00842108421084210]

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

def selectRows (rows : Fin 120 → Fin 120) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 120 => w[(rows k).val]))).cast List.length_ofFn

theorem selectRows_bit (rows : Fin 120 → Fin 120) (w : W) (j : Fin 120) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land (rows : Fin 120 → Fin 120) (u v : W) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 120 := ⟨j,hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor (rows : Fin 120 → Fin 120) (u v : W) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 120 := ⟨j,hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

theorem selectRows_neg (rows : Fin 120 → Fin 120) (u : W) : selectRows rows (~~~u) = ~~~selectRows rows u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 120 := ⟨j,hj⟩
  change (selectRows rows (~~~u))[k.val] = (~~~selectRows rows u)[k.val]
  simp only [selectRows_bit, BitVec.getElem_not]

theorem index_of_op (a b z : W) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩

def k4Word (i : Fin 4) : W := k4inputs.getD i.val 0

def k4Rows (i j : Fin 4) (k : Fin 120) : Fin 120 :=
  let index := (#[0x0, 0x3bcdeb38bdab49ca307b9ac5a928398a418820, 0x316bd69ddf3599c6507b98d5a882184093a0c5, 0x2519c1fcdf759bdb15a20e9314622040d6396a, 0x3bcd6f2e6ad8a4a0c72e2f5b5272845e418440, 0x0, 0x1cb6b15dd7379499072e2b7b50811881384a2f, 0x10649cbcd77796adcc54a138bc6120817ae2d4, 0x316ade8e62daa208230777ae6671849e939905, 0x1cb63558adaf4204430775be65263a0b38464f, 0x0, 0x4120c16ae2f462dcd5461393ce64a0bbd7799, 0x25184de839925188240737aee6f6ae28d62dca, 0x1063a4b28466f184440735bee5ab63957adb14, 0x411901184a6f399092dab7c518b6b95bd73b9, 0x0] : Array Nat)[4 * i.val + j.val]!
  Fin.ofNat 120 (((k.val / 60) * 60) + ((index >>> (5 * (k.val % 30))) &&& 31))

def k4Rename (i j : Fin 4) : W → W := selectRows (k4Rows i j)

set_option maxRecDepth 9000 in
set_option maxHeartbeats 0 in
theorem k4Rename_words : ∀ i j : Fin 4, i ≠ j →
    k4Rename i j (k4Word i) = k4Word 0 ∧
    k4Rename i j (k4Word j) = k4Word 1 ∧
    ∀ q : Fin 4, k4Rename i j (k4Word q) ∈ k4inputs := by decide +kernel

theorem k4Goal_bit : ∀ r : Fin 120, goal[r.val]'r.isLt = decide (60 ≤ r.val) := by
  decide +kernel

theorem k4Rename_goal (i j : Fin 4) : k4Rename i j goal = goal := by
  apply BitVec.eq_of_getElem_eq
  intro n hn
  let k : Fin 120 := ⟨n, hn⟩
  change (selectRows (k4Rows i j) goal)[k.val] = goal[k.val]
  rw [selectRows_bit]
  change goal[(k4Rows i j k).val] = goal[k.val]
  simp only [k4Goal_bit]
  have half : 60 ≤ (k4Rows i j k).val ↔ 60 ≤ k.val := by
    simp only [k4Rows, Fin.val_ofNat]
    let index := (#[0x0, 0x3bcdeb38bdab49ca307b9ac5a928398a418820, 0x316bd69ddf3599c6507b98d5a882184093a0c5, 0x2519c1fcdf759bdb15a20e9314622040d6396a, 0x3bcd6f2e6ad8a4a0c72e2f5b5272845e418440, 0x0, 0x1cb6b15dd7379499072e2b7b50811881384a2f, 0x10649cbcd77796adcc54a138bc6120817ae2d4, 0x316ade8e62daa208230777ae6671849e939905, 0x1cb63558adaf4204430775be65263a0b38464f, 0x0, 0x4120c16ae2f462dcd5461393ce64a0bbd7799, 0x25184de839925188240737aee6f6ae28d62dca, 0x1063a4b28466f184440735bee5ab63957adb14, 0x411901184a6f399092dab7c518b6b95bd73b9, 0x0] : Array Nat)[4 * i.val + j.val]!
    change 60 ≤ (k.val / 60 * 60 + ((index >>> (5 * (k.val % 30))) &&& 31)) % 120 ↔ _
    have hmask : (index >>> (5 * (k.val % 30))) &&& 31 < 32 := by
      rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    have hk := k.isLt
    omega
  simp only [half]

theorem k4Word_cover {w : W} (hw : w ∈ k4inputs.toFinset) : ∃ i : Fin 4, k4Word i = w := by
  rw [List.mem_toFinset] at hw
  simp only [k4inputs, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem k4Search : ∀ v : Fin 4,
    search 5 (((ops (k4Word 0) (k4Word 1)).getD v.val 0) :: k4inputs) = false := by
  decide +kernel

theorem signed_reject {k : ℕ} {ws : List W} (hn : ws.Nodup) (hf : search k ws = false)
    {t : W} (ht : t = goal ∨ t = ~~~goal) (h : SignedBuild k ws.toFinset t) : False := by
  have nt : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide
  rcases ht with rfl | rfl
  all_goals
    rcases h with h | h | h | h
    · first | exact nt.1 h | exact nt.2.2.1 h
    · first | exact nt.2.1 h | exact nt.2.2.2 h
    · exact Bool.noConfusion (hf.symm.trans (search_complete (by simp) k ws hn h))
    · exact Bool.noConfusion (hf.symm.trans (search_complete (by simp) k ws hn h))

theorem no_six_k4 (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 6 k4inputs.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 5) hl with endcase | ⟨a,ha,b,hb,hab,z,hz,_,rest,he,tail⟩
  · have mt := hs (show t ∈ s by simp [endcase])
    obtain ⟨i, hi⟩ := k4Word_cover mt
    have impossible : ∀ i : Fin 4, k4Word i ≠ goal ∧ k4Word i ≠ ~~~goal := by decide
    rcases ht with rfl | rfl
    · exact (impossible i).1 hi
    · exact (impossible i).2 hi
  · obtain ⟨i, rfl⟩ := k4Word_cover (hs ha)
    obtain ⟨j, rfl⟩ := k4Word_cover (hs hb)
    have hij : i ≠ j := fun e => hab (congrArg k4Word e)
    have ha := k4Rename_words i j hij
    let f := k4Rename i j
    have mapOp : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b) :=
      ops_map_of (selectRows_land _) (selectRows_lor _) (selectRows_neg _)
    have hZ := mapOp _ _ _ hz
    change f z ∈ basicOps (k4Rename i j (k4Word i)) (k4Rename i j (k4Word j)) at hZ
    rw [ha.1, ha.2.1] at hZ
    obtain ⟨v, hv⟩ := index_of_op _ _ _ hZ
    have ht' : f t = goal ∨ f t = ~~~goal := by
      rcases ht with rfl | rfl
      · exact .inl (k4Rename_goal i j)
      · right
        change selectRows (k4Rows i j) (~~~goal) = ~~~goal
        rw [selectRows_neg]
        exact congrArg (fun w : W => ~~~w) (k4Rename_goal i j)
    have nd : ∀ v : Fin 4, (((ops (k4Word 0) (k4Word 1)).getD v.val 0) :: k4inputs).Nodup := by decide
    apply signed_reject (nd v) (k4Search v) ht'
    apply live_transport mapOp tail
    intro w hw
    rcases Finset.mem_insert.mp hw with hwz | hr
    · subst w
      refine .inr (.inr ⟨f z, ?_, .inl rfl⟩)
      exact List.mem_toFinset.mpr (List.mem_cons.mpr (Or.inl hv.symm))
    · have hraw := hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      obtain ⟨q, rfl⟩ := k4Word_cover hraw
      exact .inr (.inr ⟨_, List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ha.2.2 q)), .inl rfl⟩)

abbrev SGate := Bool × ℕ × Bool × ℕ × Bool
abbrev Sym := Bool ⊕ (ℕ × Bool)

def evalOp (op a b : Bool) : Bool :=
  if op then a || b else a && b

def stepS (w : List Bool) (g : SGate) : List Bool :=
  w ++ [evalOp g.1 (xor (w.getD g.2.1 false) g.2.2.1) (xor (w.getD g.2.2.2.1 false) g.2.2.2.2)]

def wiresS (gs : List SGate) (w : List Bool) : List Bool :=
  gs.foldl stepS w

def valS (n : ℕ) (gs : List SGate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wiresS gs (List.ofFn x)).getD w false

def evalS (n : ℕ) (gs : List SGate) (o : ℕ) (os : Bool) (x : Fin n → Bool) : Bool :=
  xor (valS n gs x o) os

def CleanS (n : ℕ) (gs : List SGate) : Prop :=
  ∀ p g, gs[p]? = some g → g.2.1 < n + p ∧ g.2.2.2.1 < n + p

def HasBinSize (n : ℕ) (f : (Fin n → Bool) → Bool) (b : ℕ) : Prop :=
  ∃ (gs : List SGate) (o : ℕ) (os : Bool), CleanS n gs ∧ gs.length ≤ b ∧
    ∀ x : Fin n → Bool, evalS n gs o os x = f x

theorem wiresS_append (gs1 gs2 : List SGate) (w : List Bool) :
    wiresS (gs1 ++ gs2) w = wiresS gs2 (wiresS gs1 w) := by
  simp [wiresS, List.foldl_append]

theorem wiresS_shape (gs : List SGate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresS gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresS], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (stepS w g)
    refine ⟨evalOp g.1 (xor (w.getD g.2.1 false) g.2.2.1)
      (xor (w.getD g.2.2.2.1 false) g.2.2.2.2) :: t, ?_, by simp [hl]⟩
    change wiresS gs (stepS w g) = _
    rw [ht]
    simp [stepS]

theorem wiresS_length (gs : List SGate) (w : List Bool) :
    (wiresS gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresS_shape gs w
  rw [ht, List.length_append, hl]

theorem wiresS_prefix_getD (gs1 gs2 : List SGate) (w : List Bool) (k : ℕ)
    (hk : k < w.length + gs1.length) :
    (wiresS (gs1 ++ gs2) w).getD k false = (wiresS gs1 w).getD k false := by
  rw [wiresS_append]
  obtain ⟨t, ht, _⟩ := wiresS_shape gs2 (wiresS gs1 w)
  rw [ht]
  exact List.getD_append _ _ _ _ (by rw [wiresS_length]; exact hk)

theorem valS_input (n : ℕ) (gs : List SGate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    valS n gs x i = x ⟨i, hi⟩ := by
  unfold valS
  obtain ⟨t, ht, _⟩ := wiresS_shape gs (List.ofFn x)
  rw [ht, List.getD_append _ _ _ _ (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

theorem valS_beyond (n : ℕ) (gs : List SGate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : valS n gs x w = false := by
  unfold valS
  exact List.getD_eq_default _ _ (by rw [wiresS_length]; simp; omega)

theorem valS_gate (n : ℕ) (gs : List SGate) (hcl : CleanS n gs) (x : Fin n → Bool)
    (p : ℕ) (g : SGate) (hp : gs[p]? = some g) :
    valS n gs x (n + p) = evalOp g.1 (xor (valS n gs x g.2.1) g.2.2.1)
      (xor (valS n gs x g.2.2.2.1) g.2.2.2.2) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hp
  have htake : gs.take p ++ g :: gs.drop (p + 1) = gs := by
    have h1 := List.take_append_drop p gs
    have h2 : gs.drop p = g :: gs.drop (p + 1) := by
      rw [← hget]
      exact List.drop_eq_getElem_cons hlt
    rw [h2] at h1
    exact h1
  have hlen_take : (gs.take p).length = p := by simp [Nat.le_of_lt hlt]
  have hbound := hcl p g hp
  have h1 : valS n gs x g.2.1 = (wiresS (gs.take p) (List.ofFn x)).getD g.2.1 false := by
    unfold valS
    conv_lhs => rw [← htake]
    exact wiresS_prefix_getD (gs.take p) (g :: gs.drop (p + 1)) (List.ofFn x) g.2.1
      (by simp [hlen_take]; exact hbound.1)
  have h2 : valS n gs x g.2.2.2.1 = (wiresS (gs.take p) (List.ofFn x)).getD g.2.2.2.1 false := by
    unfold valS
    conv_lhs => rw [← htake]
    exact wiresS_prefix_getD (gs.take p) (g :: gs.drop (p + 1)) (List.ofFn x) g.2.2.2.1
      (by simp [hlen_take]; exact hbound.2)
  conv_lhs => unfold valS; rw [← htake]
  rw [show gs.take p ++ g :: gs.drop (p + 1) = (gs.take p ++ [g]) ++ gs.drop (p + 1) by simp]
  rw [wiresS_prefix_getD (gs.take p ++ [g]) (gs.drop (p + 1)) (List.ofFn x) (n + p)
    (by simp [hlen_take])]
  rw [wiresS_append]
  change (wiresS [g] (wiresS (gs.take p) (List.ofFn x))).getD (n + p) false = _
  have hlenw : (wiresS (gs.take p) (List.ofFn x)).length = n + p := by
    rw [wiresS_length]; simp [hlen_take]
  have hw1 : wiresS [g] (wiresS (gs.take p) (List.ofFn x)) =
      stepS (wiresS (gs.take p) (List.ofFn x)) g := rfl
  rw [hw1, stepS, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenw,
    Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  rw [← h1, ← h2]

theorem valS_append_lt (n : ℕ) (gs1 gs2 : List SGate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs1.length) : valS n (gs1 ++ gs2) x w = valS n gs1 x w := by
  unfold valS
  exact wiresS_prefix_getD gs1 gs2 (List.ofFn x) w (by simp; exact hw)

theorem cleanS_append_left (n : ℕ) (gs1 gs2 : List SGate) (h : CleanS n (gs1 ++ gs2)) :
    CleanS n gs1 := by
  intro p g hp
  have hlt : p < gs1.length := (List.getElem?_eq_some_iff.1 hp).1
  apply h p g
  rw [List.getElem?_append_left hlt]
  exact hp

theorem cleanS_take (n : ℕ) (gs : List SGate) (hcl : CleanS n gs) (p : ℕ) :
    CleanS n (gs.take p) := by
  intro q g hq
  have hlt : q < (gs.take p).length := (List.getElem?_eq_some_iff.1 hq).1
  have hqp : q < p := by simp at hlt; exact hlt.1
  apply hcl q g
  rw [← List.getElem?_take_of_lt hqp]
  exact hq

def symFlip : Sym → Sym
  | .inl c => .inl (!c)
  | .inr (w, s) => .inr (w, !s)

def symEval (n : ℕ) (gs : List SGate) (x : Fin n → Bool) : Sym → Bool
  | .inl c => c
  | .inr (w, s) => xor (valS n gs x w) s

theorem symEval_flip (n : ℕ) (gs : List SGate) (x : Fin n → Bool) (e : Sym) :
    symEval n gs x (symFlip e) = !(symEval n gs x e) := by
  rcases e with c | ⟨w, s⟩
  · cases c <;> rfl
  · simp only [symFlip, symEval]
    cases valS n gs x w <;> cases s <;> rfl

def SymValid (m : ℕ) (out : List SGate) (e : Sym) : Prop :=
  match e with
  | .inl _ => True
  | .inr (w, _) => w < m + out.length

theorem symValid_flip (m : ℕ) (out : List SGate) (e : Sym) (h : SymValid m out e) :
    SymValid m out (symFlip e) := by
  rcases e with c | ⟨w, s⟩ <;> simpa [symFlip, SymValid] using h

theorem symValid_mono (m : ℕ) (out1 out2 : List SGate) (hle : out1.length ≤ out2.length)
    (e : Sym) (h : SymValid m out1 e) : SymValid m out2 e := by
  rcases e with c | ⟨w, s⟩
  · trivial
  · exact Nat.lt_of_lt_of_le h (by omega)

theorem symEval_append (m : ℕ) (out tail : List SGate) (x : Fin m → Bool)
    (e : Sym) (hv : SymValid m out e) :
    symEval m (out ++ tail) x e = symEval m out x e := by
  rcases e with c | ⟨w, s⟩
  · rfl
  · simp [symEval, valS_append_lt m out tail x w hv]

def symBin (m : ℕ) (op : Bool) (e1 e2 : Sym) (out : List SGate) : List SGate × Sym :=
  match e1 with
  | .inl c => if op = c then (out, .inl c) else (out, e2)
  | .inr (i1, s1) =>
    match e2 with
    | .inl c => if op = c then (out, .inl c) else (out, .inr (i1, s1))
    | .inr (i2, s2) => (out ++ [(op, i1, s1, i2, s2)], .inr (m + out.length, false))

theorem symBin_clean (m : ℕ) (op : Bool) (e1 e2 : Sym) (out : List SGate)
    (hcl : CleanS m out) (h1 : SymValid m out e1) (h2 : SymValid m out e2) :
    CleanS m (symBin m op e1 e2 out).1 := by
  rcases e1 with c1 | ⟨i1, s1⟩
  · simp only [symBin]; split_ifs <;> exact hcl
  · rcases e2 with c2 | ⟨i2, s2⟩
    · simp only [symBin]; split_ifs <;> exact hcl
    · simp only [symBin]
      intro p g hp
      by_cases hlt : p < out.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hcl p g hp
      · have hpe : p = out.length := by
          have hp2 := (List.getElem?_eq_some_iff.1 hp).1
          simp at hp2
          omega
        subst hpe
        rw [List.getElem?_append_right (le_refl _)] at hp
        simp at hp
        subst hp
        exact ⟨h1, h2⟩

theorem symBin_valid (m : ℕ) (op : Bool) (e1 e2 : Sym) (out : List SGate)
    (h1 : SymValid m out e1) (h2 : SymValid m out e2) :
    SymValid m (symBin m op e1 e2 out).1 (symBin m op e1 e2 out).2 := by
  rcases e1 with c1 | ⟨i1, s1⟩
  · simp only [symBin]; split_ifs
    · trivial
    · exact h2
  · rcases e2 with c2 | ⟨i2, s2⟩
    · simp only [symBin]; split_ifs
      · trivial
      · exact h1
    · simp [symBin, SymValid]

theorem symBin_len (m : ℕ) (op : Bool) (e1 e2 : Sym) (out : List SGate) :
    out.length ≤ (symBin m op e1 e2 out).1.length ∧
    (symBin m op e1 e2 out).1.length ≤ out.length + 1 := by
  rcases e1 with c1 | ⟨i1, s1⟩
  · simp only [symBin]; split_ifs <;> simp
  · rcases e2 with c2 | ⟨i2, s2⟩
    · simp only [symBin]; split_ifs <;> simp
    · simp [symBin]

theorem symBin_const_len (m : ℕ) (op : Bool) (e1 e2 : Sym) (out : List SGate)
    (hc : (∃ c, e1 = .inl c) ∨ (∃ c, e2 = .inl c)) :
    (symBin m op e1 e2 out).1.length = out.length := by
  rcases hc with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · simp only [symBin]; split_ifs <;> rfl
  · rcases e1 with c1 | ⟨i1, s1⟩
    · simp only [symBin]; split_ifs <;> rfl
    · simp only [symBin]; split_ifs <;> rfl

theorem symBin_eval (m : ℕ) (op : Bool) (e1 e2 : Sym) (out : List SGate)
    (hcl : CleanS m out) (h1 : SymValid m out e1) (h2 : SymValid m out e2) (x : Fin m → Bool) :
    symEval m (symBin m op e1 e2 out).1 x (symBin m op e1 e2 out).2 =
      evalOp op (symEval m out x e1) (symEval m out x e2) := by
  rcases e1 with c1 | ⟨i1, s1⟩
  · simp only [symBin]
    split_ifs with h
    · subst h; cases op <;> simp [symEval, evalOp]
    · cases op <;> cases c1 <;> simp_all [symEval, evalOp]
  · rcases e2 with c2 | ⟨i2, s2⟩
    · simp only [symBin]
      split_ifs with h
      · subst h; cases op <;> simp [symEval, evalOp]
      · cases op <;> cases c2 <;> simp_all [symEval, evalOp]
    · simp only [symBin]
      have hcl' := symBin_clean m op (.inr (i1, s1)) (.inr (i2, s2)) out hcl h1 h2
      have hget : (out ++ [(op, i1, s1, i2, s2)])[out.length]? = some (op, i1, s1, i2, s2) := by
        simp
      have hv := valS_gate m (out ++ [(op, i1, s1, i2, s2)]) hcl' x out.length _ hget
      have ha1 := valS_append_lt m out [(op, i1, s1, i2, s2)] x i1 h1
      have ha2 := valS_append_lt m out [(op, i1, s1, i2, s2)] x i2 h2
      simp only [symEval] at hv ⊢
      rw [Bool.xor_false, hv, ha1, ha2]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

def stepToSigned (n : ℕ) (st : List Sym × List SGate) (g : Gate) : List Sym × List SGate :=
  match g.op with
  | .not =>
    match g.inputs with
    | [] => (st.1 ++ [.inl true], st.2)
    | a :: _ => (st.1 ++ [symFlip (st.1.getD a (.inl false))], st.2)
  | .and =>
    match g.inputs with
    | [] => (st.1 ++ [.inl true], st.2)
    | [a] => (st.1 ++ [st.1.getD a (.inl false)], st.2)
    | a :: b :: _ =>
      let res := symBin n false (st.1.getD a (.inl false)) (st.1.getD b (.inl false)) st.2
      (st.1 ++ [res.2], res.1)
  | .or =>
    match g.inputs with
    | [] => (st.1 ++ [.inl false], st.2)
    | [a] => (st.1 ++ [st.1.getD a (.inl false)], st.2)
    | a :: b :: _ =>
      let res := symBin n true (st.1.getD a (.inl false)) (st.1.getD b (.inl false)) st.2
      (st.1 ++ [res.2], res.1)
  | _ => (st.1 ++ [.inl false], st.2)

theorem compileToSigned_aux (n : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ∀ (st0 : List Sym × List SGate),
      CleanS n st0.2 →
      (∀ e ∈ st0.1, SymValid n st0.2 e) →
      let st1 := gs.foldl (stepToSigned n) st0
      CleanS n st1.2 ∧
      (∀ e ∈ st1.1, SymValid n st1.2 e) ∧
      st1.2.length ≤ st0.2.length + binaryCost gs ∧
      (∀ (x : Fin n → Bool) (ws : List Bool),
        ws.length = st0.1.length →
        (∀ w, symEval n st0.2 x (st0.1.getD w (.inl false)) = ws.getD w false) →
        let ws1 := gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) ws
        ws1.length = st1.1.length ∧
        ∀ w, symEval n st1.2 x (st1.1.getD w (.inl false)) = ws1.getD w false) := by
  induction gs with
  | nil =>
    intro st0 hcl0 hval0
    refine ⟨hcl0, hval0, by simp [binaryCost], fun x ws hlen hev => ⟨hlen, hev⟩⟩
  | cons g gs ih =>
    intro st0 hcl0 hval0
    obtain ⟨hop, hlen2⟩ := hfan g (by simp)
    obtain ⟨op, args⟩ := g
    dsimp only at hop hlen2
    have hrest : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or ∨ g'.op = .not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (by simp [hg'])
    have hget : ∀ i, SymValid n st0.2 (st0.1.getD i (.inl false)) := by
      intro i
      by_cases hi : i < st0.1.length
      · exact hval0 _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
        trivial
    have hstep_clean : CleanS n (stepToSigned n st0 ⟨op, args⟩).2 := by
      rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned]
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · exact hcl0
        · exact hcl0
        · exact symBin_clean n false _ _ _ hcl0 (hget a) (hget b)
        · simp at hlen2
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · exact hcl0
        · exact hcl0
        · exact symBin_clean n true _ _ _ hcl0 (hget a) (hget b)
        · simp at hlen2
      · rcases args with _ | ⟨a, _⟩
        · exact hcl0
        · exact hcl0
    have hstep_len_ge : st0.2.length ≤ (stepToSigned n st0 ⟨op, args⟩).2.length := by
      rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned]
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · exact le_rfl
        · exact le_rfl
        · exact (symBin_len n false _ _ _).1
        · simp at hlen2
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · exact le_rfl
        · exact le_rfl
        · exact (symBin_len n true _ _ _).1
        · simp at hlen2
      · rcases args with _ | ⟨a, _⟩ <;> exact le_rfl
    have hstep_len_le : (stepToSigned n st0 ⟨op, args⟩).2.length ≤
        st0.2.length + (if isBinary ⟨op, args⟩ then 1 else 0) := by
      rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned, isBinary]
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp
        · simp
        · simpa using (symBin_len n false _ _ _).2
        · simp at hlen2
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp
        · simp
        · simpa using (symBin_len n true _ _ _).2
        · simp at hlen2
      · rcases args with _ | ⟨a, _⟩ <;> simp
    have hstep_val : ∀ e ∈ (stepToSigned n st0 ⟨op, args⟩).1,
        SymValid n (stepToSigned n st0 ⟨op, args⟩).2 e := by
      intro e he
      rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned] at he
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h | rfl
          · exact hval0 e h
          · trivial
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h | rfl
          · exact hval0 e h
          · exact hget a
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h | rfl
          · exact symValid_mono n _ _ hstep_len_ge e (hval0 e h)
          · exact symBin_valid n false _ _ _ (hget a) (hget b)
        · simp at hlen2
      · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h | rfl
          · exact hval0 e h
          · trivial
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h | rfl
          · exact hval0 e h
          · exact hget a
        · simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h | rfl
          · exact symValid_mono n _ _ hstep_len_ge e (hval0 e h)
          · exact symBin_valid n true _ _ _ (hget a) (hget b)
        · simp at hlen2
      · rcases args with _ | ⟨a, _⟩ <;> simp only [List.mem_append, List.mem_singleton] at he
        · rcases he with h | rfl
          · exact hval0 e h
          · trivial
        · rcases he with h | rfl
          · exact hval0 e h
          · exact symValid_flip n st0.2 _ (hget a)
    obtain ⟨ih_cl, ih_val, ih_len, ih_ev⟩ := ih hrest (stepToSigned n st0 ⟨op, args⟩) hstep_clean hstep_val
    refine ⟨ih_cl, ih_val, ?_, ?_⟩
    · have hbc : binaryCost (⟨op, args⟩ :: gs) = (if isBinary ⟨op, args⟩ then 1 else 0) + binaryCost gs := by
        unfold binaryCost
        cases hb : isBinary ⟨op, args⟩ <;> simp [List.filter_cons, hb] <;> omega
      change (gs.foldl (stepToSigned n) (stepToSigned n st0 ⟨op, args⟩)).2.length ≤ _
      omega
    · intro x ws hlen hev
      let ws' := ws ++ [op.eval (args.map fun i => ws.getD i false)]
      have hlen' : ws'.length = (stepToSigned n st0 ⟨op, args⟩).1.length := by
        have hs1 : (stepToSigned n st0 ⟨op, args⟩).1.length = st0.1.length + 1 := by
          rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned]
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hlen2 ⊢
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hlen2 ⊢
          · rcases args with _ | ⟨a, _⟩ <;> simp
        simp [ws', hlen, hs1]
      have hev' : ∀ w, symEval n (stepToSigned n st0 ⟨op, args⟩).2 x
          ((stepToSigned n st0 ⟨op, args⟩).1.getD w (.inl false)) = ws'.getD w false := by
        intro w
        have heq_prefix : ∀ k < st0.1.length,
            symEval n (stepToSigned n st0 ⟨op, args⟩).2 x (st0.1.getD k (.inl false)) =
              symEval n st0.2 x (st0.1.getD k (.inl false)) := by
          intro k hk
          rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned]
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · rfl
            · rfl
            · dsimp only [stepToSigned]
              rcases h_e1 : st0.1.getD a (.inl false) with c1 | ⟨i1, s1⟩
              · simp only [symBin]; split_ifs <;> rfl
              · rcases h_e2 : st0.1.getD b (.inl false) with c2 | ⟨i2, s2⟩
                · simp only [symBin]; split_ifs <;> rfl
                · simp only [symBin]
                  exact symEval_append n st0.2 [(false, i1, s1, i2, s2)] x (st0.1.getD k (.inl false)) (hget k)
            · simp at hlen2
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · rfl
            · rfl
            · dsimp only [stepToSigned]
              rcases h_e1 : st0.1.getD a (.inl false) with c1 | ⟨i1, s1⟩
              · simp only [symBin]; split_ifs <;> rfl
              · rcases h_e2 : st0.1.getD b (.inl false) with c2 | ⟨i2, s2⟩
                · simp only [symBin]; split_ifs <;> rfl
                · simp only [symBin]
                  exact symEval_append n st0.2 [(true, i1, s1, i2, s2)] x (st0.1.getD k (.inl false)) (hget k)
            · simp at hlen2
          · rcases args with _ | ⟨a, _⟩ <;> rfl
        have hlast : ∀ e, (stepToSigned n st0 ⟨op, args⟩).1 = st0.1 ++ [e] →
            symEval n (stepToSigned n st0 ⟨op, args⟩).2 x e = op.eval (args.map fun i => ws.getD i false) := by
          intro e he
          rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned] at he
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · simp at he; subst he; simp [GateOp.eval, symEval]
            · simp at he; subst he
              have := hev a
              simp [GateOp.eval, symEval] at this ⊢
              exact this
            · simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at he
              subst he
              dsimp only [stepToSigned]
              rw [symBin_eval n false _ _ _ hcl0 (hget a) (hget b) x, hev a, hev b]
              simp [GateOp.eval, evalOp]
            · simp at hlen2
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · simp at he; subst he; simp [GateOp.eval, symEval]
            · simp at he; subst he
              have := hev a
              simp [GateOp.eval, symEval] at this ⊢
              exact this
            · simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at he
              subst he
              dsimp only [stepToSigned]
              rw [symBin_eval n true _ _ _ hcl0 (hget a) (hget b) x, hev a, hev b]
              simp [GateOp.eval, evalOp]
            · simp at hlen2
          · rcases args with _ | ⟨a, _⟩
            · simp at he; subst he; simp [GateOp.eval, symEval]
            · simp at he; subst he
              dsimp only [stepToSigned]
              rw [symEval_flip, ← List.getD_eq_getElem?_getD, hev a]
              simp [GateOp.eval]
        have hexists : ∃ e, (stepToSigned n st0 ⟨op, args⟩).1 = st0.1 ++ [e] := by
          rcases hop with rfl | rfl | rfl <;> simp only [stepToSigned]
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
            · simp at hlen2
          · rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
            · simp at hlen2
          · rcases args with _ | ⟨a, _⟩ <;> exact ⟨_, rfl⟩
        obtain ⟨e, he⟩ := hexists
        by_cases hw_lt : w < st0.1.length
        · rw [he, List.getD_append _ _ _ _ hw_lt, heq_prefix w hw_lt, hev w]
          exact (List.getD_append _ _ _ _ (by omega)).symm
        · by_cases hw_eq : w = st0.1.length
          · subst hw_eq
            rw [he, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
            have h1 : (ws'.getD st0.1.length false) = op.eval (args.map fun i => ws.getD i false) := by
              simp [ws', hlen]
            rw [h1]
            simpa using hlast e he
          · have hgt : st0.1.length + 1 ≤ w := by omega
            have h1 : (stepToSigned n st0 ⟨op, args⟩).1.getD w (.inl false) = .inl false :=
              List.getD_eq_default _ _ (by rw [he]; simp; omega)
            have h2 : ws'.getD w false = false :=
              List.getD_eq_default _ _ (by simp [ws', hlen]; omega)
            rw [h1, h2]
            rfl
      exact ih_ev x ws' hlen' hev'

theorem compileToSigned (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hnc : ∃ x y : Fin n → Bool, f x ≠ f y)
    (C : Circuit) (hfan : FanInTwo C) (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    HasBinSize n f (binaryCost C.gates) := by
  have hfan' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    exact ⟨by simpa [Set.mem_insert_iff] using h1, h2⟩
  let env0 : List Sym := List.ofFn fun i : Fin n => .inr (i.val, false)
  have hval0 : ∀ e ∈ env0, SymValid n [] e := by
    intro e he
    simp only [env0, List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    exact i.isLt
  obtain ⟨hcl, hval, hlen, hev⟩ := compileToSigned_aux n C.gates hfan' (env0, []) (by intro p g hp; simp at hp) hval0
  let st1 := C.gates.foldl (stepToSigned n) (env0, [])
  have hev0 : ∀ x : Fin n → Bool,
      (∀ w, symEval n [] x (env0.getD w (.inl false)) = (List.ofFn x).getD w false) := by
    intro x w
    by_cases hw : w < n
    · simp [env0, List.getD_eq_getElem?_getD, hw, symEval, valS_input]
    · rw [List.getD_eq_default _ _ (by simp [env0]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      rfl
  have hfinal : ∀ x : Fin n → Bool, symEval n st1.2 x (st1.1.getD C.output (.inl false)) = f x := by
    intro x
    have := (hev x (List.ofFn x) (by simp [env0]) (hev0 x)).2 C.output
    rw [this]
    exact heval x
  rcases h_out : st1.1.getD C.output (.inl false) with c | ⟨o, os⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    have hx := hfinal x
    have hy := hfinal y
    rw [h_out] at hx hy
    exact hx.symm.trans hy
  · refine ⟨st1.2, o, os, hcl, by simpa using hlen, ?_⟩
    intro x
    have hx := hfinal x
    rw [h_out] at hx
    exact hx

def actionS (w : List W) (g : SGate) : W :=
  let u1 := if g.2.2.1 then ~~~(w.getD g.2.1 0) else w.getD g.2.1 0
  let u2 := if g.2.2.2.2 then ~~~(w.getD g.2.2.2.1 0) else w.getD g.2.2.2.1 0
  if g.1 then u1 ||| u2 else u1 &&& u2

theorem read_bit120 (w : List W) (i : ℕ) (k : Fin 120) :
    (w.map (bit120 k)).getD i false = bit120 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit120]

theorem actionS_spec (w : List W) (g : SGate) (k : Fin 120) :
    stepS (w.map (bit120 k)) g = (w ++ [actionS w g]).map (bit120 k) := by
  simp only [stepS, actionS, evalOp, List.map_append, List.map_singleton, read_bit120]
  congr 1
  congr 1
  have h1 : xor (bit120 k (w.getD g.2.1 0)) g.2.2.1 =
      bit120 k (if g.2.2.1 then ~~~(w.getD g.2.1 0) else w.getD g.2.1 0) := by
    cases g.2.2.1 <;> simp [bit120, k.isLt]
  have h2 : xor (bit120 k (w.getD g.2.2.2.1 0)) g.2.2.2.2 =
      bit120 k (if g.2.2.2.2 then ~~~(w.getD g.2.2.2.1 0) else w.getD g.2.2.2.1 0) := by
    cases g.2.2.2.2 <;> simp [bit120, k.isLt]
  rw [h1, h2]
  cases g.1 <;> simp [bit120]

theorem gateS_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u) (g : SGate) :
    reachable av (actionS w g) := by
  have hr1 : holds av (if g.2.2.1 then ~~~(w.getD g.2.1 0) else w.getD g.2.1 0) := by
    cases g.2.2.1
    · exact available_read hw g.2.1
    · exact holds_not (available_read hw g.2.1)
  have hr2 : holds av (if g.2.2.2.2 then ~~~(w.getD g.2.2.2.1 0) else w.getD g.2.2.2.1 0) := by
    cases g.2.2.2.2
    · exact available_read hw g.2.2.2.1
    · exact holds_not (available_read hw g.2.2.2.1)
  unfold actionS
  cases g.1
  · exact and_reach hr1 hr2
  · exact or_reach hr1 hr2

theorem compileSigned (gs : List SGate) (out : ℕ) (os : Bool)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k : Fin 120, xor ((wiresS gs (w.map (bit120 k))).getD out false) os = bit120 k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = (if os then goal else ~~~goal) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      have hki := he ⟨i, hi⟩
      simp only [wiresS, List.foldl_nil, read_bit120, bit120] at hki
      cases os <;> simp_all [BitVec.getElem_not]
    have h : holds av (if os then goal else ~~~goal) := hv ▸ available_read hw out
    cases os
    · simp only [Bool.false_eq_true, ite_false] at h
      rcases h with zero | ones | ⟨t, ht, eq | eq⟩
      · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
      · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
      · exact ⟨t, .inr eq.symm, ht⟩
      · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
    · simp only [ite_true] at h
      rcases h with zero | ones | ⟨t, ht, eq | eq⟩
      · exact False.elim ((by decide : goal ≠ 0) zero)
      · exact False.elim ((by decide : goal ≠ ~~~0) ones)
      · exact ⟨t, .inl eq.symm, ht⟩
      · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := actionS w g
    have stepOK := actionS_spec w g
    have nextEval : ∀ k : Fin 120,
        xor ((wiresS gs ((w ++ [z]).map (bit120 k))).getD out false) os = bit120 k (~~~goal) := by
      intro k
      simpa only [wiresS, List.foldl_cons, stepOK] using he k
    have tail := ih (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    rcases gateS_reach w av hw g with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
    · obtain ⟨t, ht, run⟩ := cont av hw existing
      exact ⟨t, ht, Or.inl run⟩
    · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
      exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def target4 (T : ℕ) (x : Fin 4 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 4, if x i then 2 ^ (i : ℕ) else 0)

def k4CompInputs : List W := k4inputs.map (fun w => ~~~w)

set_option maxRecDepth 8000 in
theorem sample_th2 : ∀ j : Fin 120,
    target4 0xfee8 (fun i => (k4inputs.getD i.val 0)[j.val]) = goal[j.val] := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sample_th3 : ∀ j : Fin 120,
    target4 0xe880 (fun i => (k4CompInputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

theorem lift_build {a b : ℕ} {t : W} (h : a ≤ b) (hr : build basicOps t a k4inputs.toFinset) :
    build basicOps t b k4inputs.toFinset := by
  induction h with
  | refl => exact hr
  | step _ ih => exact Or.inl ih

theorem bound_th2_4 (b : ℕ) (h : HasBinSize 4 (target4 0xfee8) b) : 7 ≤ b := by
  obtain ⟨gs, o, os, _, hlen, hev⟩ := h
  by_contra! hlt
  have init : ∀ u ∈ k4inputs, holds k4inputs.toFinset u :=
    fun u hu => .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have eval120 : ∀ k : Fin 120,
      xor ((wiresS gs (k4inputs.map (bit120 k))).getD o false) (!os) = bit120 k (~~~goal) := by
    intro k
    let x : Fin 4 → Bool := fun i => bit120 k (k4inputs.getD i.val 0)
    have hof : List.ofFn x = k4inputs.map (bit120 k) := by
      apply List.ext_getElem
      · rfl
      · intro i hi hj
        have hlt2 : i < k4inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt2, Option.getD_some]
    have hx := hev x
    simp only [evalS, valS, hof] at hx
    have hs' : target4 0xfee8 x = bit120 k goal := sample_th2 k
    have hxor : xor ((wiresS gs (k4inputs.map (bit120 k))).getD o false) (!os) =
        !(target4 0xfee8 x) := by
      rw [← hx]
      cases (wiresS gs (k4inputs.map (bit120 k))).getD o false <;> cases os <;> rfl
    rw [hxor, hs']
    simp [bit120, k.isLt]
  obtain ⟨t, ht, run⟩ := compileSigned gs o (!os) k4inputs k4inputs.toFinset init eval120
  exact no_six_k4 t ht (lift_build (by omega : gs.length ≤ 6) run)

theorem bound_th3_4 (b : ℕ) (h : HasBinSize 4 (target4 0xe880) b) : 7 ≤ b := by
  obtain ⟨gs, o, os, _, hlen, hev⟩ := h
  by_contra! hlt
  have init : ∀ u ∈ k4CompInputs, holds k4inputs.toFinset u := by
    intro u hu
    simp only [k4CompInputs, List.mem_map] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    exact .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inr rfl⟩)
  have eval120 : ∀ k : Fin 120,
      xor ((wiresS gs (k4CompInputs.map (bit120 k))).getD o false) os = bit120 k (~~~goal) := by
    intro k
    let x : Fin 4 → Bool := fun i => bit120 k (k4CompInputs.getD i.val 0)
    have hof : List.ofFn x = k4CompInputs.map (bit120 k) := by
      apply List.ext_getElem
      · rfl
      · intro i hi hj
        have hlt2 : i < k4CompInputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt2, Option.getD_some]
    have hx := hev x
    simp only [evalS, valS, hof] at hx
    have hs := sample_th3 k
    rw [hx]
    exact hs
  obtain ⟨t, ht, run⟩ := compileSigned gs o os k4CompInputs k4inputs.toFinset init eval120
  exact no_six_k4 t ht (lift_build (by omega : gs.length ≤ 6) run)

def elimStep (m : ℕ) (st : List Sym × List SGate) (g : SGate) : List Sym × List SGate :=
  let e1 := if g.2.2.1 then symFlip (st.1.getD g.2.1 (.inl false)) else st.1.getD g.2.1 (.inl false)
  let e2 := if g.2.2.2.2 then symFlip (st.1.getD g.2.2.2.1 (.inl false)) else st.1.getD g.2.2.2.1 (.inl false)
  let res := symBin m g.1 e1 e2 st.2
  (st.1 ++ [res.2], res.1)

def elimRun (m : ℕ) (st : List Sym × List SGate) (gs : List SGate) : List Sym × List SGate :=
  gs.foldl (elimStep m) st

theorem elimRun_nil (m : ℕ) (st : List Sym × List SGate) :
    elimRun m st [] = st := rfl

theorem elimRun_cons (m : ℕ) (st : List Sym × List SGate) (g : SGate) (gs : List SGate) :
    elimRun m st (g :: gs) = elimRun m (elimStep m st g) gs := rfl

theorem elimRun_append (m : ℕ) (st : List Sym × List SGate) (gs1 gs2 : List SGate) :
    elimRun m st (gs1 ++ gs2) = elimRun m (elimRun m st gs1) gs2 := by
  simp [elimRun, List.foldl_append]

theorem elimRun_spec (n m : ℕ) (gs : List SGate) (hcl : CleanS n gs) :
    ∀ (k : ℕ) (hk : k ≤ gs.length) (st0 : List Sym × List SGate),
      st0.1.length = n + k →
      CleanS m st0.2 →
      (∀ e ∈ st0.1, SymValid m st0.2 e) →
      let st1 := elimRun m st0 (gs.drop k)
      st1.1.length = n + gs.length ∧
      CleanS m st1.2 ∧
      (∀ e ∈ st1.1, SymValid m st1.2 e) ∧
      st1.2.length ≤ st0.2.length + (gs.drop k).length ∧
      (∀ (x : Fin m → Bool) (y : Fin n → Bool),
        (∀ w < st0.1.length, symEval m st0.2 x (st0.1.getD w (.inl false)) = valS n gs y w) →
        ∀ w < st1.1.length, symEval m st1.2 x (st1.1.getD w (.inl false)) = valS n gs y w) := by
  intro k hk
  have key : ∀ d : ℕ, ∀ k ≤ gs.length, gs.length - k = d →
      ∀ (st0 : List Sym × List SGate),
      st0.1.length = n + k →
      CleanS m st0.2 →
      (∀ e ∈ st0.1, SymValid m st0.2 e) →
      let st1 := elimRun m st0 (gs.drop k)
      st1.1.length = n + gs.length ∧
      CleanS m st1.2 ∧
      (∀ e ∈ st1.1, SymValid m st1.2 e) ∧
      st1.2.length ≤ st0.2.length + (gs.drop k).length ∧
      (∀ (x : Fin m → Bool) (y : Fin n → Bool),
        (∀ w < st0.1.length, symEval m st0.2 x (st0.1.getD w (.inl false)) = valS n gs y w) →
        ∀ w < st1.1.length, symEval m st1.2 x (st1.1.getD w (.inl false)) = valS n gs y w) := by
    intro d
    induction d with
    | zero =>
      intro k hk hdiff st0 hlen hcl0 hval0
      have heq : k = gs.length := by omega
      subst heq
      simp only [List.drop_length, elimRun_nil, List.length_nil, add_zero]
      refine ⟨hlen, hcl0, hval0, le_rfl, fun x y h w hw => h w hw⟩
    | succ d ih =>
      intro k hk hdiff st0 hlen hcl0 hval0
      have hklt : k < gs.length := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[k]? = some g := ⟨gs[k], List.getElem?_eq_getElem hklt⟩
      have hdrop : gs.drop k = g :: gs.drop (k + 1) := by
        rw [← (List.getElem?_eq_some_iff.1 hg).2]
        exact List.drop_eq_getElem_cons hklt
      have hg_bounds := hcl k g hg
      have hget : ∀ i, i < n + k → SymValid m st0.2 (st0.1.getD i (.inl false)) := by
        intro i hi
        exact hval0 _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < st0.1.length)])
      let e1 := if g.2.2.1 then symFlip (st0.1.getD g.2.1 (.inl false)) else st0.1.getD g.2.1 (.inl false)
      let e2 := if g.2.2.2.2 then symFlip (st0.1.getD g.2.2.2.1 (.inl false)) else st0.1.getD g.2.2.2.1 (.inl false)
      have hv1 : SymValid m st0.2 e1 := by
        dsimp [e1]; cases g.2.2.1
        · exact hget g.2.1 hg_bounds.1
        · exact symValid_flip m st0.2 _ (hget g.2.1 hg_bounds.1)
      have hv2 : SymValid m st0.2 e2 := by
        dsimp [e2]; cases g.2.2.2.2
        · exact hget g.2.2.2.1 hg_bounds.2
        · exact symValid_flip m st0.2 _ (hget g.2.2.2.1 hg_bounds.2)
      let st' := elimStep m st0 g
      have hlen' : st'.1.length = n + (k + 1) := by simp [st', elimStep, hlen]; omega
      have hcl' : CleanS m st'.2 := symBin_clean m g.1 e1 e2 st0.2 hcl0 hv1 hv2
      have hlen_ge : st0.2.length ≤ st'.2.length := (symBin_len m g.1 e1 e2 st0.2).1
      have hlen_le : st'.2.length ≤ st0.2.length + 1 := (symBin_len m g.1 e1 e2 st0.2).2
      have hval' : ∀ e ∈ st'.1, SymValid m st'.2 e := by
        intro e he
        simp only [st', elimStep, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact symValid_mono m _ _ hlen_ge e (hval0 e he)
        · exact symBin_valid m g.1 e1 e2 st0.2 hv1 hv2
      obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih (k + 1) (by omega) (by omega) st' hlen' hcl' hval'
      rw [hdrop, elimRun_cons]
      refine ⟨ih1, ih2, ih3, ?_, ?_⟩
      · change (elimRun m st' (gs.drop (k + 1))).2.length ≤ st0.2.length + (g :: gs.drop (k + 1)).length
        rw [List.length_cons]
        omega
      · intro x y hev w hw
        apply ih5 x y _ w hw
        intro w' hw'
        rw [hlen'] at hw'
        by_cases hwlt : w' < n + k
        · have he' : st'.1.getD w' (.inl false) = st0.1.getD w' (.inl false) :=
            List.getD_append _ _ _ _ (by omega)
          rw [he']
          have hmem : st0.1.getD w' (.inl false) ∈ st0.1 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : w' < st0.1.length)]
            exact List.getElem_mem _
          have hval_old := hval0 _ hmem
          have hpres : symEval m st'.2 x (st0.1.getD w' (.inl false)) = symEval m st0.2 x (st0.1.getD w' (.inl false)) := by
            rcases h_s1 : st0.1.getD w' (.inl false) with c | ⟨u, s⟩
            · rfl
            · rw [h_s1] at hval_old
              dsimp only [st', elimStep]
              rcases h_e1 : e1 with c1 | ⟨i1, s1⟩
              · dsimp only [e1] at h_e1; rw [h_e1]; simp only [symBin]; split_ifs <;> rfl
              · rcases h_e2 : e2 with c2 | ⟨i2, s2⟩
                · dsimp only [e1, e2] at h_e1 h_e2; rw [h_e1, h_e2]; simp only [symBin]; split_ifs <;> rfl
                · dsimp only [e1, e2] at h_e1 h_e2; rw [h_e1, h_e2]; simp only [symBin]
                  exact symEval_append m st0.2 [(g.1, i1, s1, i2, s2)] x (.inr (u, s)) hval_old
          rw [hpres]
          exact hev w' (by omega)
        · have hweq : w' = n + k := by omega
          subst hweq
          have he' : st'.1.getD (n + k) (.inl false) = (symBin m g.1 e1 e2 st0.2).2 := by
            dsimp only [st', elimStep]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
            rfl
          rw [he']
          change symEval m (symBin m g.1 e1 e2 st0.2).1 x (symBin m g.1 e1 e2 st0.2).2 = valS n gs y (n + k)
          rw [symBin_eval m g.1 e1 e2 st0.2 hcl0 hv1 hv2 x]
          rw [valS_gate n gs hcl y k g hg]
          have h1 : symEval m st0.2 x e1 = xor (valS n gs y g.2.1) g.2.2.1 := by
            dsimp [e1]; cases g.2.2.1
            · simpa using hev g.2.1 (by omega)
            · simp only [ite_true, symEval_flip, hev g.2.1 (by omega)]
              cases valS n gs y g.2.1 <;> rfl
          have h2 : symEval m st0.2 x e2 = xor (valS n gs y g.2.2.2.1) g.2.2.2.2 := by
            dsimp [e2]; cases g.2.2.2.2
            · simpa using hev g.2.2.2.1 (by omega)
            · simp only [ite_true, symEval_flip, hev g.2.2.2.1 (by omega)]
              cases valS n gs y g.2.2.2.1 <;> rfl
          rw [h1, h2]
  exact key (gs.length - k) k hk rfl

def ReadsS (gs : List SGate) (p w : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ (g.2.1 = w ∨ g.2.2.2.1 = w)

theorem elimRun_dead (n : ℕ) (gs : List SGate) (hcl : CleanS n gs) (p : ℕ) (hp : p < gs.length)
    (hno : ∀ q, ¬ ReadsS gs q (n + p)) :
    ∀ (k : ℕ) (hk1 : p + 1 ≤ k) (hk2 : k ≤ gs.length) (st0 : List Sym × List SGate),
      st0.1.length = n + k →
      CleanS n st0.2 →
      (∀ e ∈ st0.1, SymValid n st0.2 e) →
      let st1 := elimRun n st0 (gs.drop k)
      st1.1.length = n + gs.length ∧
      CleanS n st1.2 ∧
      (∀ e ∈ st1.1, SymValid n st1.2 e) ∧
      st1.2.length ≤ st0.2.length + (gs.drop k).length ∧
      (∀ (x : Fin n → Bool),
        (∀ w < st0.1.length, w ≠ n + p → symEval n st0.2 x (st0.1.getD w (.inl false)) = valS n gs x w) →
        ∀ w < st1.1.length, w ≠ n + p → symEval n st1.2 x (st1.1.getD w (.inl false)) = valS n gs x w) := by
  have key : ∀ d : ℕ, ∀ k, p + 1 ≤ k → k ≤ gs.length → gs.length - k = d →
      ∀ (st0 : List Sym × List SGate),
      st0.1.length = n + k →
      CleanS n st0.2 →
      (∀ e ∈ st0.1, SymValid n st0.2 e) →
      let st1 := elimRun n st0 (gs.drop k)
      st1.1.length = n + gs.length ∧
      CleanS n st1.2 ∧
      (∀ e ∈ st1.1, SymValid n st1.2 e) ∧
      st1.2.length ≤ st0.2.length + (gs.drop k).length ∧
      (∀ (x : Fin n → Bool),
        (∀ w < st0.1.length, w ≠ n + p → symEval n st0.2 x (st0.1.getD w (.inl false)) = valS n gs x w) →
        ∀ w < st1.1.length, w ≠ n + p → symEval n st1.2 x (st1.1.getD w (.inl false)) = valS n gs x w) := by
    intro d
    induction d with
    | zero =>
      intro k hk1 hk2 hdiff st0 hlen hcl0 hval0
      have heq : k = gs.length := by omega
      subst heq
      simp only [List.drop_length, elimRun_nil, List.length_nil, add_zero]
      refine ⟨hlen, hcl0, hval0, le_rfl, fun x h w hw hne => h w hw hne⟩
    | succ d ih =>
      intro k hk1 hk2 hdiff st0 hlen hcl0 hval0
      have hklt : k < gs.length := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[k]? = some g := ⟨gs[k], List.getElem?_eq_getElem hklt⟩
      have hdrop : gs.drop k = g :: gs.drop (k + 1) := by
        rw [← (List.getElem?_eq_some_iff.1 hg).2]
        exact List.drop_eq_getElem_cons hklt
      have hg_bounds := hcl k g hg
      have hg_ne1 : g.2.1 ≠ n + p := fun e => hno k ⟨g, hg, Or.inl e⟩
      have hg_ne2 : g.2.2.2.1 ≠ n + p := fun e => hno k ⟨g, hg, Or.inr e⟩
      have hget : ∀ i, i < n + k → SymValid n st0.2 (st0.1.getD i (.inl false)) := by
        intro i hi
        exact hval0 _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < st0.1.length)])
      let e1 := if g.2.2.1 then symFlip (st0.1.getD g.2.1 (.inl false)) else st0.1.getD g.2.1 (.inl false)
      let e2 := if g.2.2.2.2 then symFlip (st0.1.getD g.2.2.2.1 (.inl false)) else st0.1.getD g.2.2.2.1 (.inl false)
      have hv1 : SymValid n st0.2 e1 := by
        dsimp [e1]; cases g.2.2.1
        · exact hget g.2.1 hg_bounds.1
        · exact symValid_flip n st0.2 _ (hget g.2.1 hg_bounds.1)
      have hv2 : SymValid n st0.2 e2 := by
        dsimp [e2]; cases g.2.2.2.2
        · exact hget g.2.2.2.1 hg_bounds.2
        · exact symValid_flip n st0.2 _ (hget g.2.2.2.1 hg_bounds.2)
      let st' := elimStep n st0 g
      have hlen' : st'.1.length = n + (k + 1) := by simp [st', elimStep, hlen]; omega
      have hcl' : CleanS n st'.2 := symBin_clean n g.1 e1 e2 st0.2 hcl0 hv1 hv2
      have hlen_ge : st0.2.length ≤ st'.2.length := (symBin_len n g.1 e1 e2 st0.2).1
      have hlen_le : st'.2.length ≤ st0.2.length + 1 := (symBin_len n g.1 e1 e2 st0.2).2
      have hval' : ∀ e ∈ st'.1, SymValid n st'.2 e := by
        intro e he
        simp only [st', elimStep, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact symValid_mono n _ _ hlen_ge e (hval0 e he)
        · exact symBin_valid n g.1 e1 e2 st0.2 hv1 hv2
      obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih (k + 1) (by omega) (by omega) (by omega) st' hlen' hcl' hval'
      rw [hdrop, elimRun_cons]
      refine ⟨ih1, ih2, ih3, ?_, ?_⟩
      · change (elimRun n st' (gs.drop (k + 1))).2.length ≤ st0.2.length + (g :: gs.drop (k + 1)).length
        rw [List.length_cons]
        omega
      · intro x hev w hw hne
        apply ih5 x _ w hw hne
        intro w' hw' hne'
        rw [hlen'] at hw'
        by_cases hwlt : w' < n + k
        · have he' : st'.1.getD w' (.inl false) = st0.1.getD w' (.inl false) :=
            List.getD_append _ _ _ _ (by omega)
          rw [he']
          have hmem : st0.1.getD w' (.inl false) ∈ st0.1 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : w' < st0.1.length)]
            exact List.getElem_mem _
          have hval_old := hval0 _ hmem
          have hpres : symEval n st'.2 x (st0.1.getD w' (.inl false)) = symEval n st0.2 x (st0.1.getD w' (.inl false)) := by
            rcases h_s1 : st0.1.getD w' (.inl false) with c | ⟨u, s⟩
            · rfl
            · rw [h_s1] at hval_old
              dsimp only [st', elimStep]
              rcases h_e1 : e1 with c1 | ⟨i1, s1⟩
              · dsimp only [e1] at h_e1; rw [h_e1]; simp only [symBin]; split_ifs <;> rfl
              · rcases h_e2 : e2 with c2 | ⟨i2, s2⟩
                · dsimp only [e1, e2] at h_e1 h_e2; rw [h_e1, h_e2]; simp only [symBin]; split_ifs <;> rfl
                · dsimp only [e1, e2] at h_e1 h_e2; rw [h_e1, h_e2]; simp only [symBin]
                  exact symEval_append n st0.2 [(g.1, i1, s1, i2, s2)] x (.inr (u, s)) hval_old
          rw [hpres]
          exact hev w' (by omega) hne'
        · have hweq : w' = n + k := by omega
          subst hweq
          have he' : st'.1.getD (n + k) (.inl false) = (symBin n g.1 e1 e2 st0.2).2 := by
            dsimp only [st', elimStep]
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
            rfl
          rw [he']
          change symEval n (symBin n g.1 e1 e2 st0.2).1 x (symBin n g.1 e1 e2 st0.2).2 = valS n gs x (n + k)
          rw [symBin_eval n g.1 e1 e2 st0.2 hcl0 hv1 hv2 x]
          rw [valS_gate n gs hcl x k g hg]
          have h1 : symEval n st0.2 x e1 = xor (valS n gs x g.2.1) g.2.2.1 := by
            dsimp [e1]; cases g.2.2.1
            · simpa using hev g.2.1 (by omega) hg_ne1
            · simp only [ite_true, symEval_flip, hev g.2.1 (by omega) hg_ne1]
              cases valS n gs x g.2.1 <;> rfl
          have h2 : symEval n st0.2 x e2 = xor (valS n gs x g.2.2.2.1) g.2.2.2.2 := by
            dsimp [e2]; cases g.2.2.2.2
            · simpa using hev g.2.2.2.1 (by omega) hg_ne2
            · simp only [ite_true, symEval_flip, hev g.2.2.2.1 (by omega) hg_ne2]
              cases valS n gs x g.2.2.2.1 <;> rfl
          rw [h1, h2]
  intro k hk1 hk2 st0
  exact key (gs.length - k) k hk1 hk2 rfl st0

def symIsConst : Sym → Bool
  | .inl _ => true
  | .inr _ => false

theorem symIsConst_flip (e : Sym) : symIsConst (symFlip e) = symIsConst e := by
  rcases e with c | ⟨w, s⟩ <;> rfl

def RCS (n : ℕ) (env0 : List Sym) (gs : List SGate) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧
    (symIsConst ((elimRun n (env0, []) (gs.take p)).1.getD g.2.1 (.inl false)) = true ∨
     symIsConst ((elimRun n (env0, []) (gs.take p)).1.getD g.2.2.2.1 (.inl false)) = true)

theorem elimRun_count (m : ℕ) (gs : List SGate) :
    ∀ (st0 : List Sym × List SGate) (S : Finset ℕ),
      (∀ p ∈ S, ∃ g, gs[p]? = some g ∧
        (symIsConst ((elimRun m st0 (gs.take p)).1.getD g.2.1 (.inl false)) = true ∨
         symIsConst ((elimRun m st0 (gs.take p)).1.getD g.2.2.2.1 (.inl false)) = true)) →
      (elimRun m st0 gs).2.length + S.card ≤ st0.2.length + gs.length := by
  induction gs with
  | nil =>
    intro st0 S hS
    have hE : S = ∅ := by
      ext p; simp only [Finset.notMem_empty, iff_false]
      intro hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elimRun]
  | cons g gs ih =>
    intro st0 S hS
    let S' : Finset ℕ := (S.erase 0).image (fun p => p - 1)
    have hcard : S.card = (if 0 ∈ S then 1 else 0) + S'.card := by
      by_cases h0 : 0 ∈ S
      · rw [if_pos h0, ← Finset.card_erase_add_one h0]
        have hinj : ∀ a ∈ S.erase 0, ∀ b ∈ S.erase 0, a - 1 = b - 1 → a = b := by
          intro a ha b hb he
          have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
          have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
          omega
        rw [Finset.card_image_of_injOn hinj]
        omega
      · have herase : S.erase 0 = S := Finset.erase_eq_self.mpr h0
        dsimp only [S']
        rw [if_neg h0, herase]
        have hinj : ∀ a ∈ S, ∀ b ∈ S, a - 1 = b - 1 → a = b := by
          intro a ha b hb he
          have ha0 : a ≠ 0 := fun e => h0 (e ▸ ha)
          have hb0 : b ≠ 0 := fun e => h0 (e ▸ hb)
          omega
        rw [Finset.card_image_of_injOn hinj]
        omega
    have hS' : ∀ p ∈ S', ∃ g', gs[p]? = some g' ∧
        (symIsConst ((elimRun m (elimStep m st0 g) (gs.take p)).1.getD g'.2.1 (.inl false)) = true ∨
         symIsConst ((elimRun m (elimStep m st0 g) (gs.take p)).1.getD g'.2.2.2.1 (.inl false)) = true) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hq0 : q ≠ 0 := (Finset.mem_erase.mp hq).1
      have hqS : q ∈ S := (Finset.mem_erase.mp hq).2
      obtain ⟨g', hg', hconst⟩ := hS q hqS
      have hq1 : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      obtain ⟨r, rfl⟩ := hq1
      simp only [Nat.add_sub_cancel] at hg' hconst ⊢
      exact ⟨g', hg', by simpa [List.take_succ_cons, elimRun_cons] using hconst⟩
    have ih_bound := ih (elimStep m st0 g) S' hS'
    rw [elimRun_cons]
    by_cases h0 : 0 ∈ S
    · obtain ⟨g0, hg0, hconst0⟩ := hS 0 h0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg0
      subst g0
      simp only [List.take_zero, elimRun_nil] at hconst0
      have hstep_len : (elimStep m st0 g).2.length = st0.2.length := by
        apply symBin_const_len
        rcases hconst0 with hc | hc
        · left
          rcases h1 : st0.1.getD g.2.1 (.inl false) with c | ⟨i, s⟩
          · exact ⟨if g.2.2.1 then !c else c, by cases g.2.2.1 <;> simp [symFlip]⟩
          · rw [h1] at hc; simp [symIsConst] at hc
        · right
          rcases h2 : st0.1.getD g.2.2.2.1 (.inl false) with c | ⟨i, s⟩
          · exact ⟨if g.2.2.2.2 then !c else c, by cases g.2.2.2.2 <;> simp [symFlip]⟩
          · rw [h2] at hc; simp [symIsConst] at hc
      rw [hcard, if_pos h0]
      simp only [List.length_cons]
      omega
    · have hstep_len : (elimStep m st0 g).2.length ≤ st0.2.length + 1 := by
        exact (symBin_len m g.1 _ _ st0.2).2
      rw [hcard, if_neg h0]
      simp only [List.length_cons]
      omega

theorem drop_const_alias (n : ℕ) (gs : List SGate) (o : ℕ) (os : Bool) (hcl : CleanS n gs)
    (p : ℕ) (hp : p < gs.length) (override : Sym)
    (hov_val : SymValid n (gs.take p) override)
    (hov_eq : ∀ x : Fin n → Bool, symEval n (gs.take p) x override = valS n gs x (n + p)) :
    ∃ (gs' : List SGate) (o' : ℕ) (os' : Bool),
      CleanS n gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ x : Fin n → Bool, evalS n gs' o' os' x = evalS n gs o os x := by
  let env0 : List Sym := (List.range (n + p)).map (fun w => .inr (w, false)) ++ [override]
  have hlen0 : env0.length = n + (p + 1) := by simp [env0]; omega
  have hcl0 : CleanS n (gs.take p) := cleanS_take n gs hcl p
  have hval0 : ∀ e ∈ env0, SymValid n (gs.take p) e := by
    intro e he
    simp only [env0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
    rcases he with ⟨w, hw, rfl⟩ | rfl
    · simp only [SymValid, List.length_take, Nat.lt_min]
      exact by omega
    · exact hov_val
  obtain ⟨hlen1, hcl1, hval1, hsz1, hev1⟩ :=
    elimRun_spec n n gs hcl (p + 1) hp (env0, gs.take p) hlen0 hcl0 hval0
  let st1 := elimRun n (env0, gs.take p) (gs.drop (p + 1))
  have hsz : st1.2.length + 1 ≤ gs.length := by
    have htake_len : (gs.take p).length = p := by simp [Nat.le_of_lt hp]
    have hdrop_len : (gs.drop (p + 1)).length = gs.length - (p + 1) := by simp
    change st1.2.length + 1 ≤ gs.length
    have := hsz1
    dsimp only [st1] at *
    omega
  have hev0 : ∀ x : Fin n → Bool, ∀ w < env0.length,
      symEval n (gs.take p) x (env0.getD w (.inl false)) = valS n gs x w := by
    intro x w hw
    rw [hlen0] at hw
    by_cases hwlt : w < n + p
    · have hget : env0.getD w (.inl false) = .inr (w, false) := by
        have h1 : ((List.range (n + p)).map (fun w => (Sum.inr (w, false) : Sym))).length = n + p := by simp
        rw [List.getD_append _ _ _ _ (by rw [h1]; exact hwlt)]
        simp [List.getD_eq_getElem?_getD, hwlt]
      rw [hget]
      simp only [symEval, Bool.xor_false]
      exact (valS_append_lt n (gs.take p) (gs.drop p) x w (by simp [Nat.le_of_lt hp, hwlt])).symm.trans
        (by rw [List.take_append_drop])
    · have hweq : w = n + p := by omega
      subst hweq
      have hget : env0.getD (n + p) (.inl false) = override := by
        simp [env0]
      rw [hget]
      exact hov_eq x
  by_cases ho : o < n + gs.length
  · rcases h_out : st1.1.getD o (.inl false) with c | ⟨o', fl⟩
    · refine ⟨[], n, xor c os, by intro q g hq; simp at hq, by simp; omega, ?_⟩
      intro x
      have hx := hev1 x x (hev0 x) o (by rw [hlen1]; exact ho)
      rw [h_out] at hx
      simp only [symEval] at hx
      change xor (valS n [] x n) (xor c os) = evalS n gs o os x
      rw [valS_beyond n [] x n (by simp)]
      simp only [evalS]
      rw [← hx]
      cases c <;> cases os <;> rfl
    · refine ⟨st1.2, o', xor fl os, hcl1, hsz, ?_⟩
      intro x
      have hx := hev1 x x (hev0 x) o (by rw [hlen1]; exact ho)
      rw [h_out] at hx
      simp only [symEval] at hx
      change xor (valS n st1.2 x o') (xor fl os) = evalS n gs o os x
      simp only [evalS] at hx ⊢
      rw [← hx]
      cases valS n st1.2 x o' <;> cases fl <;> cases os <;> rfl
  · refine ⟨[], n, os, by intro q g hq; simp at hq, by simp; omega, ?_⟩
    intro x
    change xor (valS n [] x n) os = evalS n gs o os x
    rw [valS_beyond n [] x n (by simp), evalS, valS_beyond n gs x o (by omega)]

theorem drop_dead_S (n : ℕ) (gs : List SGate) (o : ℕ) (os : Bool) (hcl : CleanS n gs)
    (p : ℕ) (hp : p < gs.length) (ho : o ≠ n + p) (hno : ∀ q, ¬ ReadsS gs q (n + p)) :
    ∃ (gs' : List SGate) (o' : ℕ) (os' : Bool),
      CleanS n gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ x : Fin n → Bool, evalS n gs' o' os' x = evalS n gs o os x := by
  let env0 : List Sym := (List.range (n + p)).map (fun w => .inr (w, false)) ++ [.inl false]
  have hlen0 : env0.length = n + (p + 1) := by simp [env0]; omega
  have hcl0 : CleanS n (gs.take p) := cleanS_take n gs hcl p
  have hval0 : ∀ e ∈ env0, SymValid n (gs.take p) e := by
    intro e he
    simp only [env0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
    rcases he with ⟨w, hw, rfl⟩ | rfl
    · simp only [SymValid, List.length_take, Nat.lt_min]
      exact by omega
    · trivial
  obtain ⟨hlen1, hcl1, hval1, hsz1, hev1⟩ :=
    elimRun_dead n gs hcl p hp hno (p + 1) (le_refl _) hp (env0, gs.take p) hlen0 hcl0 hval0
  let st1 := elimRun n (env0, gs.take p) (gs.drop (p + 1))
  have hsz : st1.2.length + 1 ≤ gs.length := by
    have htake_len : (gs.take p).length = p := by simp [Nat.le_of_lt hp]
    have hdrop_len : (gs.drop (p + 1)).length = gs.length - (p + 1) := by simp
    have := hsz1
    dsimp only [st1] at *
    omega
  have hev0 : ∀ x : Fin n → Bool, ∀ w < env0.length, w ≠ n + p →
      symEval n (gs.take p) x (env0.getD w (.inl false)) = valS n gs x w := by
    intro x w hw hne
    rw [hlen0] at hw
    have hwlt : w < n + p := by omega
    have hget : env0.getD w (.inl false) = .inr (w, false) := by
      have h1 : ((List.range (n + p)).map (fun w => (Sum.inr (w, false) : Sym))).length = n + p := by simp
      rw [List.getD_append _ _ _ _ (by rw [h1]; exact hwlt)]
      simp [List.getD_eq_getElem?_getD, hwlt]
    rw [hget]
    simp only [symEval, Bool.xor_false]
    exact (valS_append_lt n (gs.take p) (gs.drop p) x w (by simp [Nat.le_of_lt hp, hwlt])).symm.trans
      (by rw [List.take_append_drop])
  by_cases ho_lt : o < n + gs.length
  · rcases h_out : st1.1.getD o (.inl false) with c | ⟨o', fl⟩
    · refine ⟨[], n, xor c os, by intro q g hq; simp at hq, by simp; omega, ?_⟩
      intro x
      have hx := hev1 x (hev0 x) o (by rw [hlen1]; exact ho_lt) ho
      rw [h_out] at hx
      simp only [symEval] at hx
      change xor (valS n [] x n) (xor c os) = evalS n gs o os x
      rw [valS_beyond n [] x n (by simp)]
      simp only [evalS]
      rw [← hx]
      cases c <;> cases os <;> rfl
    · refine ⟨st1.2, o', xor fl os, hcl1, hsz, ?_⟩
      intro x
      have hx := hev1 x (hev0 x) o (by rw [hlen1]; exact ho_lt) ho
      rw [h_out] at hx
      simp only [symEval] at hx
      change xor (valS n st1.2 x o') (xor fl os) = evalS n gs o os x
      simp only [evalS] at hx ⊢
      rw [← hx]
      cases valS n st1.2 x o' <;> cases fl <;> cases os <;> rfl
  · refine ⟨[], n, os, by intro q g hq; simp at hq, by simp; omega, ?_⟩
    intro x
    change xor (valS n [] x n) os = evalS n gs o os x
    rw [valS_beyond n [] x n (by simp), evalS, valS_beyond n gs x o (by omega)]

def wireSum (gs : List SGate) : ℕ :=
  (gs.map fun g => g.2.1 + g.2.2.2.1).sum

def LeastS (n : ℕ) (f : (Fin n → Bool) → Bool) (gs : List SGate) (o : ℕ) (os : Bool) : Prop :=
  CleanS n gs ∧ (∀ x : Fin n → Bool, evalS n gs o os x = f x) ∧
  ∀ (gs' : List SGate) (o' : ℕ) (os' : Bool), CleanS n gs' →
    (∀ x : Fin n → Bool, evalS n gs' o' os' x = f x) →
    gs.length ≤ gs'.length ∧ (gs'.length = gs.length → wireSum gs ≤ wireSum gs')

theorem exists_leastS (n : ℕ) (f : (Fin n → Bool) → Bool) (b : ℕ) (h : HasBinSize n f b) :
    ∃ (gs : List SGate) (o : ℕ) (os : Bool), LeastS n f gs o os ∧ gs.length ≤ b := by
  classical
  let P : ℕ → Prop := fun k => ∃ (gs : List SGate) (o : ℕ) (os : Bool),
    CleanS n gs ∧ gs.length = k ∧ ∀ x : Fin n → Bool, evalS n gs o os x = f x
  obtain ⟨gs0, o0, os0, hcl0, hlen0, hev0⟩ := h
  have hexP : ∃ k, P k := ⟨gs0.length, gs0, o0, os0, hcl0, rfl, hev0⟩
  let L0 := Nat.find hexP
  have hL0_le : L0 ≤ gs0.length := Nat.find_min' hexP ⟨gs0, o0, os0, hcl0, rfl, hev0⟩
  obtain ⟨gs1, o1, os1, hcl1, hlen1, hev1⟩ := Nat.find_spec hexP
  let Q : ℕ → Prop := fun w => ∃ (gs : List SGate) (o : ℕ) (os : Bool),
    CleanS n gs ∧ gs.length = L0 ∧ wireSum gs = w ∧ ∀ x : Fin n → Bool, evalS n gs o os x = f x
  have hexQ : ∃ w, Q w := ⟨wireSum gs1, gs1, o1, os1, hcl1, hlen1, rfl, hev1⟩
  obtain ⟨gs, o, os, hcl, hlen, hsum, hev⟩ := Nat.find_spec hexQ
  refine ⟨gs, o, os, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' os' hcl' hev'
  have hlen_le : L0 ≤ gs'.length := Nat.find_min' hexP ⟨gs', o', os', hcl', rfl, hev'⟩
  refine ⟨by omega, ?_⟩
  intro hlen_eq
  have hsum_le : Nat.find hexQ ≤ wireSum gs' :=
    Nat.find_min' hexQ ⟨gs', o', os', hcl', by omega, rfl, hev'⟩
  omega

section S1
variable {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List SGate} {o : ℕ} {os : Bool}

theorem LeastS.no_const (L : LeastS n f gs o os) (p : ℕ) (hp : p < gs.length) (c : Bool) :
    ¬ ∀ x : Fin n → Bool, valS n gs x (n + p) = c := by
  intro hc
  obtain ⟨gs', o', os', hcl', hsz', hev'⟩ :=
    drop_const_alias n gs o os L.1 p hp (.inl c) trivial (fun x => (hc x).symm)
  have := (L.2.2 gs' o' os' hcl' (fun x => (hev' x).trans (L.2.1 x))).1
  omega

theorem LeastS.no_alias (L : LeastS n f gs o os) (p : ℕ) (hp : p < gs.length) (j : ℕ)
    (hj : j < n + p) (fl : Bool) :
    ¬ ∀ x : Fin n → Bool, valS n gs x (n + p) = xor (valS n gs x j) fl := by
  intro ha
  have hj_take : j < n + (gs.take p).length := by simp [Nat.le_of_lt hp, hj]
  obtain ⟨gs', o', os', hcl', hsz', hev'⟩ :=
    drop_const_alias n gs o os L.1 p hp (.inr (j, fl)) hj_take
      (fun x => by
        simp only [symEval]
        rw [← valS_append_lt n (gs.take p) (gs.drop p) x j hj_take, List.take_append_drop, ← ha x])
  have := (L.2.2 gs' o' os' hcl' (fun x => (hev' x).trans (L.2.1 x))).1
  omega

theorem LeastS.live (L : LeastS n f gs o os) (p : ℕ) (hp : p < gs.length) (ho : o ≠ n + p) :
    ∃ q, p < q ∧ ReadsS gs q (n + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ ReadsS gs q (n + p) := by
    intro q ⟨g, hg, hr⟩
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, g, hg, hr⟩
    · have hb := L.1 q g hg
      rcases hr with hr | hr <;> omega
  obtain ⟨gs', o', os', hcl', hsz', hev'⟩ := drop_dead_S n gs o os L.1 p hp ho hno'
  have := (L.2.2 gs' o' os' hcl' (fun x => (hev' x).trans (L.2.1 x))).1
  omega

theorem LeastS.no_same_inputs (L : LeastS n f gs o os) (p : ℕ) (g : SGate) (hg : gs[p]? = some g) :
    g.2.1 ≠ g.2.2.2.1 := by
  intro heq
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hb := L.1 p g hg
  have hv : ∀ x : Fin n → Bool, valS n gs x (n + p) =
      evalOp g.1 (xor (valS n gs x g.2.1) g.2.2.1) (xor (valS n gs x g.2.1) g.2.2.2.2) := by
    intro x
    rw [valS_gate n gs L.1 x p g hg, heq]
  cases h1 : g.1 <;> cases h2 : g.2.2.1 <;> cases h3 : g.2.2.2.2
  · exact L.no_alias p hp g.2.1 hb.1 false (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_const p hp false (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_const p hp false (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_alias p hp g.2.1 hb.1 true (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_alias p hp g.2.1 hb.1 false (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_const p hp true (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_const p hp true (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)
  · exact L.no_alias p hp g.2.1 hb.1 true (fun x => by rw [hv x, h1, h2, h3]; cases valS n gs x g.2.1 <;> rfl)

theorem tri_cases (op_p spa spw op_q sqa sqp : Bool) :
    (∃ c : Bool, ∀ A W, evalOp op_q (xor A sqa) (xor (evalOp op_p (xor A spa) (xor W spw)) sqp) = c) ∨
    (∃ fl : Bool, ∀ A W, evalOp op_q (xor A sqa) (xor (evalOp op_p (xor A spa) (xor W spw)) sqp) = xor A fl) ∨
    (∃ fl : Bool, ∀ A W, evalOp op_q (xor A sqa) (xor (evalOp op_p (xor A spa) (xor W spw)) sqp) =
      xor (evalOp op_p (xor A spa) (xor W spw)) fl) ∨
    (∃ op2 s1 s2 : Bool, ∀ A W, evalOp op_q (xor A sqa) (xor (evalOp op_p (xor A spa) (xor W spw)) sqp) =
      evalOp op2 (xor A s1) (xor W s2)) := by
  decide +revert

theorem wireSum_set_lt (gs : List SGate) (q : ℕ) (hq : q < gs.length) (g_old g_new : SGate)
    (hget : gs[q]? = some g_old) (hlt : g_new.2.1 + g_new.2.2.2.1 < g_old.2.1 + g_old.2.2.2.1) :
    wireSum (gs.set q g_new) < wireSum gs := by
  induction gs generalizing q with
  | nil => simp at hq
  | cons g gs ih =>
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set_cons_zero, wireSum, List.map_cons, List.sum_cons]
      omega
    | succ q =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.length_cons] at hq
      have ih' := ih q (by omega) hget
      simp only [List.set_cons_succ, wireSum, List.map_cons, List.sum_cons] at ih' ⊢
      omega

theorem LeastS.no_tri (L : LeastS n f gs o os) (p q a : ℕ)
    (hpa : ReadsS gs p a) (hqa : ReadsS gs q a) (hqp : ReadsS gs q (n + p)) : False := by
  obtain ⟨gp, hgp, hrpa⟩ := hpa
  obtain ⟨gq, hgq, hrqa⟩ := hqa
  obtain ⟨gq', hgq', hrqp⟩ := hqp
  have eqg : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst gq'
  have hbp := L.1 p gp hgp
  have hbq := L.1 q gq hgq
  have hp_len : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hq_len : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  have hpq : p < q := by
    have hns := L.no_same_inputs q gq hgq
    rcases hrqp with h1 | h2
    · omega
    · omega
  have ha_lt_p : a < n + p := by rcases hrpa with h | h <;> omega
  have ha_ne_p : a ≠ n + p := by omega
  obtain ⟨w, hw_lt, spa, spw, hvp⟩ :
      ∃ (w : ℕ) (hw : w < n + p) (spa spw : Bool),
        ∀ x : Fin n → Bool, valS n gs x (n + p) =
          evalOp gp.1 (xor (valS n gs x a) spa) (xor (valS n gs x w) spw) := by
    rcases hrpa with h1 | h2
    · refine ⟨gp.2.2.2.1, hbp.2, gp.2.2.1, gp.2.2.2.2, fun x => ?_⟩
      rw [valS_gate n gs L.1 x p gp hgp, h1]
    · refine ⟨gp.2.1, hbp.1, gp.2.2.2.2, gp.2.2.1, fun x => ?_⟩
      rw [valS_gate n gs L.1 x p gp hgp, h2]
      cases gp.1 <;> simp [evalOp, Bool.and_comm, Bool.or_comm]
  obtain ⟨sqa, sqp, hvq, hq_sum⟩ :
      ∃ (sqa sqp : Bool),
        (∀ x : Fin n → Bool, valS n gs x (n + q) =
          evalOp gq.1 (xor (valS n gs x a) sqa) (xor (valS n gs x (n + p)) sqp)) ∧
        gq.2.1 + gq.2.2.2.1 = a + (n + p) := by
    have hns := L.no_same_inputs q gq hgq
    rcases hrqa with ha1 | ha2 <;> rcases hrqp with hp1 | hp2
    · exact False.elim (ha_ne_p (ha1.symm.trans hp1))
    · refine ⟨gq.2.2.1, gq.2.2.2.2, fun x => ?_, by omega⟩
      rw [valS_gate n gs L.1 x q gq hgq, ha1, hp2]
    · refine ⟨gq.2.2.2.2, gq.2.2.1, fun x => ?_, by omega⟩
      rw [valS_gate n gs L.1 x q gq hgq, ha2, hp1]
      cases gq.1 <;> simp [evalOp, Bool.and_comm, Bool.or_comm]
    · exact False.elim (ha_ne_p (ha2.symm.trans hp2))
  rcases tri_cases gp.1 spa spw gq.1 sqa sqp with
    ⟨c, hc⟩ | ⟨fl, hfl⟩ | ⟨fl, hfl⟩ | ⟨op2, s1, s2, hop2⟩
  · exact L.no_const q hq_len c (fun x => by rw [hvq x, hvp x]; exact hc _ _)
  · exact L.no_alias q hq_len a (by omega) fl (fun x => by rw [hvq x, hvp x]; exact hfl _ _)
  · exact L.no_alias q hq_len (n + p) (by omega) fl (fun x => by rw [hvq x, hvp x]; exact hfl _ _)
  · let g_new : SGate := (op2, a, s1, w, s2)
    let gs' := gs.set q g_new
    have hcl' : CleanS n gs' := by
      intro r gr hgr
      by_cases hrq : r = q
      · subst hrq
        simp only [gs', List.getElem?_set_self hq_len, Option.some.injEq] at hgr
        subst hgr
        dsimp only [g_new]
        exact ⟨by omega, by omega⟩
      · rw [List.getElem?_set_ne (Ne.symm hrq)] at hgr
        exact L.1 r gr hgr
    have hev_wires : ∀ x : Fin n → Bool, ∀ u : ℕ, valS n gs' x u = valS n gs x u := by
      intro x u
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        by_cases hun : u < n
        · rw [valS_input n gs' x u hun, valS_input n gs x u hun]
        · obtain ⟨r, rfl⟩ : ∃ r, u = n + r := ⟨u - n, by omega⟩
          cases hr : gs[r]? with
          | none =>
            have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
            rw [valS_beyond n gs' x _ (by simp [gs']; omega), valS_beyond n gs x _ (by omega)]
          | some g_orig =>
            by_cases hrq : r = q
            · subst hrq
              have hr' : gs'[r]? = some g_new := List.getElem?_set_self hq_len
              rw [valS_gate n gs' hcl' x r g_new hr', hvq x, hvp x]
              have ha_eq := ih a (by omega)
              have hw_eq := ih w (by omega)
              change evalOp op2 (xor (valS n gs' x a) s1) (xor (valS n gs' x w) s2) = _
              rw [ha_eq, hw_eq]
              exact (hop2 _ _).symm
            · have hr' : gs'[r]? = some g_orig := by rw [List.getElem?_set_ne (Ne.symm hrq)]; exact hr
              have hb := L.1 r g_orig hr
              rw [valS_gate n gs' hcl' x r g_orig hr', valS_gate n gs L.1 x r g_orig hr]
              rw [ih g_orig.2.1 hb.1, ih g_orig.2.2.2.1 hb.2]
    have hev' : ∀ x : Fin n → Bool, evalS n gs' o os x = f x := by
      intro x
      unfold evalS
      rw [hev_wires x o]
      exact L.2.1 x
    have hsum_lt := wireSum_set_lt gs q hq_len gq g_new hgq (by dsimp [g_new]; omega)
    have hmin := (L.2.2 gs' o os hcl' hev').2 (by simp [gs'])
    dsimp only [gs'] at hmin
    omega

end S1

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

def DropS {m : ℕ} (f : (Fin (m + 1) → Bool) → Bool) (y : Fin (m + 1)) (b : Bool)
    (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasBinSize m (fun x => f (Fin.insertNth y b x)) s'

def PaysS {m : ℕ} (f : (Fin (m + 1) → Bool) → Bool) (y : Fin (m + 1)) (s : ℕ) : Prop :=
  (DropS f y false 3 s ∧ DropS f y true 3 s) ∨
  (DropS f y false 4 s ∧ DropS f y true 2 s) ∨
  (DropS f y false 2 s ∧ DropS f y true 4 s)

theorem DropS_mono {m : ℕ} {f : (Fin (m + 1) → Bool) → Bool} {y : Fin (m + 1)} {b : Bool}
    {k s k' s' : ℕ} (h : DropS f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : DropS f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

def restrEnv {n : ℕ} (i : Fin (n + 1)) (b : Bool) : List Sym :=
  List.ofFn (Fin.insertNth i (.inl b) (fun k : Fin n => .inr ((k : ℕ), false)))

theorem restrEnv_length {n : ℕ} (i : Fin (n + 1)) (b : Bool) :
    (restrEnv i b).length = n + 1 := by
  simp [restrEnv]

theorem restrEnv_valid {n : ℕ} (i : Fin (n + 1)) (b : Bool) :
    ∀ e ∈ restrEnv i b, SymValid n [] e := by
  intro e he
  simp only [restrEnv, List.mem_ofFn] at he
  obtain ⟨j, rfl⟩ := he
  cases j using i.succAboveCases with
  | x => simp [SymValid]
  | p k => simp [SymValid, k.isLt]

theorem restrEnv_eval {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin n → Bool) (gs : List SGate)
    (w : ℕ) (hw : w < n + 1) :
    symEval n [] x ((restrEnv i b).getD w (.inl false)) = valS (n + 1) gs (Fin.insertNth i b x) w := by
  rw [valS_input (n + 1) gs (Fin.insertNth i b x) w hw]
  simp only [restrEnv, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true,
    Option.getD_some]
  generalize (⟨w, hw⟩ : Fin (n + 1)) = j
  cases j using i.succAboveCases with
  | x => simp [symEval]
  | p k => simp [symEval, valS_input, k.isLt]

def IsCS {n : ℕ} (gs : List SGate) (i : Fin (n + 1)) (b : Bool) (w : ℕ) : Prop :=
  symIsConst ((elimRun n (restrEnv i b, []) (gs.take (w - n))).1.getD w (.inl false)) = true

theorem elimRun_env_prefix (n : ℕ) (l : List SGate) (st : List Sym × List SGate) :
    ∃ tail, (elimRun n st l).1 = st.1 ++ tail := by
  induction l generalizing st with
  | nil => exact ⟨[], by simp [elimRun]⟩
  | cons g' gs' ih =>
    obtain ⟨t, ht⟩ := ih (elimStep n st g')
    refine ⟨(symBin n g'.1
      (if g'.2.2.1 then symFlip (st.1.getD g'.2.1 (.inl false)) else st.1.getD g'.2.1 (.inl false))
      (if g'.2.2.2.2 then symFlip (st.1.getD g'.2.2.2.1 (.inl false)) else st.1.getD g'.2.2.2.1 (.inl false))
      st.2).2 :: t, ?_⟩
    rw [elimRun_cons, ht]
    simp [elimStep]

theorem elimRun_env_length (n : ℕ) (l : List SGate) (st : List Sym × List SGate) :
    (elimRun n st l).1.length = st.1.length + l.length := by
  induction l generalizing st with
  | nil => simp [elimRun]
  | cons g' gs' ih => rw [elimRun_cons, ih]; simp [elimStep]; omega

theorem saveS {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List SGate} {o : ℕ} {os : Bool}
    (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RCS n (restrEnv i b) gs p) :
    DropS f i b S.card gs.length := by
  obtain ⟨hlen1, hcl1, _, hsz1, hev1⟩ :=
    elimRun_spec (n + 1) n gs L.1 0 (Nat.zero_le _) (restrEnv i b, []) (restrEnv_length i b)
      (by intro p g hp; simp at hp) (restrEnv_valid i b)
  simp only [List.drop_zero, List.length_nil, zero_add] at hlen1 hcl1 hsz1 hev1
  let st1 := elimRun n (restrEnv i b, []) gs
  have hcount : st1.2.length + S.card ≤ gs.length := by
    simpa [st1] using elimRun_count n gs (restrEnv i b, []) S hS
  by_cases ho : o < (n + 1) + gs.length
  · rcases h_out : st1.1.getD o (.inl false) with c | ⟨o', fl⟩
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hev1 x (Fin.insertNth i b x) (fun w hw => restrEnv_eval i b x gs w (by simpa [restrEnv_length] using hw)) o (by rw [hlen1]; exact ho)
      have hy := hev1 y (Fin.insertNth i b y) (fun w hw => restrEnv_eval i b y gs w (by simpa [restrEnv_length] using hw)) o (by rw [hlen1]; exact ho)
      rw [h_out] at hx hy
      simp only [symEval] at hx hy
      apply hxy
      rw [← L.2.1, ← L.2.1]
      simp only [evalS]
      rw [← hx, ← hy]
    · refine ⟨st1.2.length, hcount, st1.2, o', xor fl os, hcl1, le_rfl, ?_⟩
      intro x
      have hx := hev1 x (Fin.insertNth i b x) (fun w hw => restrEnv_eval i b x gs w (by simpa [restrEnv_length] using hw)) o (by rw [hlen1]; exact ho)
      rw [h_out] at hx
      simp only [symEval] at hx
      change xor (valS n st1.2 x o') (xor fl os) = f (Fin.insertNth i b x)
      rw [← L.2.1 (Fin.insertNth i b x)]
      simp only [evalS] at hx ⊢
      rw [← hx]
      cases valS n st1.2 x o' <;> cases fl <;> cases os <;> rfl
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← L.2.1, ← L.2.1]
    simp only [evalS, valS_beyond (n + 1) gs _ o (by omega)]

theorem rcs_input {n : ℕ} {gs : List SGate} {p : ℕ} {i : Fin (n + 1)} (b : Bool)
    (h : ReadsS gs p i.val) : RCS n (restrEnv i b) gs p := by
  obtain ⟨g, hg, hin⟩ := h
  have hc : symIsConst ((elimRun n (restrEnv i b, []) (gs.take p)).1.getD i.val (.inl false)) = true := by
    obtain ⟨tail, htail⟩ := elimRun_env_prefix n (gs.take p) (restrEnv i b, [])
    rw [htail, List.getD_append _ _ _ _ (by rw [restrEnv_length]; exact i.isLt)]
    rw [restrEnv, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt, symIsConst]
  rcases hin with h1 | h2
  · exact ⟨g, hg, Or.inl (h1 ▸ hc)⟩
  · exact ⟨g, hg, Or.inr (h2 ▸ hc)⟩

theorem rcs_of_reads {n : ℕ} {gs : List SGate} {q p : ℕ} {i : Fin (n + 1)} {b : Bool}
    (hpq : p < q) (h : ReadsS gs q (n + 1 + p)) (hc : IsCS gs i b (n + 1 + p)) :
    RCS n (restrEnv i b) gs q := by
  obtain ⟨g, hg, hin⟩ := h
  have htake : gs.take q = gs.take (n + 1 + p - n) ++ (gs.take q).drop (p + 1) := by
    rw [show n + 1 + p - n = p + 1 by omega]
    have h1 := List.take_append_drop (p + 1) (gs.take q)
    rw [List.take_take, Nat.min_eq_left (by omega)] at h1
    exact h1.symm
  have hpre : ∃ tail, (elimRun n (restrEnv i b, []) (gs.take q)).1 =
      (elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n))).1 ++ tail := by
    rw [htake, elimRun_append]
    exact elimRun_env_prefix n _ _
  have hlen : (elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n))).1.length =
      n + 1 + (gs.take (p + 1)).length := by
    rw [show n + 1 + p - n = p + 1 by omega, elimRun_env_length, restrEnv_length]
  have hp_lt_gs : p < gs.length := by
    have hq_lt : q < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    omega
  have hlen_gt : n + 1 + p < (elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n))).1.length := by
    rw [hlen, List.length_take]
    omega
  obtain ⟨tail, htail⟩ := hpre
  have hconst_q : symIsConst ((elimRun n (restrEnv i b, []) (gs.take q)).1.getD (n + 1 + p) (.inl false)) = true := by
    rw [htail, List.getD_append _ _ _ _ hlen_gt]
    exact hc
  rcases hin with h1 | h2
  · exact ⟨g, hg, Or.inl (h1 ▸ hconst_q)⟩
  · exact ⟨g, hg, Or.inr (h2 ▸ hconst_q)⟩

theorem isCS_reader {n : ℕ} {gs : List SGate} (hcl : CleanS (n + 1) gs) (i : Fin (n + 1))
    (p : ℕ) (gp : SGate) (hgp : gs[p]? = some gp) (hip : gp.2.1 = i.val ∨ gp.2.2.2.1 = i.val)
    (b : Bool) (hb : b = xor gp.1 (if gp.2.1 = i.val then gp.2.2.1 else gp.2.2.2.2)) :
    IsCS gs i b (n + 1 + p) := by
  have hp_lt : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have htake : gs.take (p + 1) = gs.take p ++ [gp] := by
    have := List.take_succ_eq_append_getElem hp_lt
    have heqg : gs[p] = gp := (List.getElem?_eq_some_iff.1 hgp).2
    simpa [heqg] using this
  have hlen_p : (elimRun n (restrEnv i b, []) (gs.take p)).1.length = n + 1 + p := by
    rw [elimRun_env_length, restrEnv_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hp_lt)]
  obtain ⟨tail, htail⟩ := elimRun_env_prefix n (gs.take p) (restrEnv i b, [])
  have hi_val : (elimRun n (restrEnv i b, []) (gs.take p)).1.getD i.val (.inl false) = .inl b := by
    rw [htail, List.getD_append _ _ _ _ (by rw [restrEnv_length]; exact i.isLt)]
    rw [restrEnv, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt]
  unfold IsCS
  rw [show n + 1 + p - n = p + 1 by omega, htake, elimRun_append, elimRun_cons, elimRun_nil]
  dsimp only [elimStep]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen_p]), hlen_p, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  rcases hip with h1 | h2
  · have hfl : (if gp.2.1 = i.val then gp.2.2.1 else gp.2.2.2.2) = gp.2.2.1 := if_pos h1
    rw [hfl] at hb
    have h_e1 : (if gp.2.2.1 then symFlip ((elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.1 (.inl false))
        else (elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.1 (.inl false)) = .inl gp.1 := by
      rw [h1, hi_val, hb]
      cases h_op : gp.1 <;> cases h_s : gp.2.2.1 <;> simp [symFlip]
    rw [h_e1]
    cases gp.1 <;> simp [symBin, symIsConst]
  · by_cases h1 : gp.2.1 = i.val
    · have hfl : (if gp.2.1 = i.val then gp.2.2.1 else gp.2.2.2.2) = gp.2.2.1 := if_pos h1
      rw [hfl] at hb
      have h_e1 : (if gp.2.2.1 then symFlip ((elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.1 (.inl false))
          else (elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.1 (.inl false)) = .inl gp.1 := by
        rw [h1, hi_val, hb]
        cases h_op : gp.1 <;> cases h_s : gp.2.2.1 <;> simp [symFlip]
      rw [h_e1]
      cases gp.1 <;> simp [symBin, symIsConst]
    · have hfl : (if gp.2.1 = i.val then gp.2.2.1 else gp.2.2.2.2) = gp.2.2.2.2 := if_neg h1
      rw [hfl] at hb
      have h_e2 : (if gp.2.2.2.2 then symFlip ((elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.2.2.1 (.inl false))
          else (elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.2.2.1 (.inl false)) = .inl gp.1 := by
        rw [h2, hi_val, hb]
        cases h_op : gp.1 <;> cases h_s : gp.2.2.2.2 <;> simp [symFlip]
      rw [h_e2]
      generalize (if gp.2.2.1 then symFlip ((elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.1 (.inl false))
          else (elimRun n (restrEnv i b, []) (gs.take p)).1.getD gp.2.1 (.inl false)) = e1
      rcases e1 with c1 | ⟨i1, s1⟩
      · cases gp.1 <;> cases c1 <;> simp [symBin, symIsConst]
      · cases gp.1 <;> simp [symBin, symIsConst]

theorem isCS_both_const {n : ℕ} {gs : List SGate} (hcl : CleanS (n + 1) gs)
    (i : Fin (n + 1)) (b : Bool) (J : ℕ) (gJ : SGate) (hJ : gs[J]? = some gJ)
    (h1 : IsCS gs i b gJ.2.1) (h2 : IsCS gs i b gJ.2.2.2.1)
    (hg1 : n + 1 ≤ gJ.2.1) (hg2 : n + 1 ≤ gJ.2.2.2.1) :
    IsCS gs i b (n + 1 + J) := by
  have hJ_lt : J < gs.length := (List.getElem?_eq_some_iff.1 hJ).1
  have hJ_bounds := hcl J gJ hJ
  have htake : gs.take (J + 1) = gs.take J ++ [gJ] := by
    have := List.take_succ_eq_append_getElem hJ_lt
    have heqg : gs[J] = gJ := (List.getElem?_eq_some_iff.1 hJ).2
    simpa [heqg] using this
  have hlen_J : (elimRun n (restrEnv i b, []) (gs.take J)).1.length = n + 1 + J := by
    rw [elimRun_env_length, restrEnv_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hJ_lt)]
  have prefix_get : ∀ w, n + 1 ≤ w → w < n + 1 + J → IsCS gs i b w →
      symIsConst ((elimRun n (restrEnv i b, []) (gs.take J)).1.getD w (.inl false)) = true := by
    intro w hw1 hw2 hcw
    have hw_sub : w - n ≤ J := by omega
    have htw : gs.take J = gs.take (w - n) ++ (gs.drop (w - n)).take (J - (w - n)) := by
      rw [← List.drop_take]
      have h1 := List.take_append_drop (w - n) (gs.take J)
      rw [List.take_take, Nat.min_eq_left hw_sub] at h1
      exact h1.symm
    rw [htw, elimRun_append]
    obtain ⟨tail, htail⟩ := elimRun_env_prefix n _ (elimRun n (restrEnv i b, []) (gs.take (w - n)))
    rw [htail]
    have hlen_w : (elimRun n (restrEnv i b, []) (gs.take (w - n))).1.length = n + 1 + (w - n) := by
      rw [elimRun_env_length, restrEnv_length, List.length_take, Nat.min_eq_left (by omega)]
    rw [List.getD_append _ _ _ _ (by rw [hlen_w]; omega)]
    exact hcw
  have hc1 := prefix_get gJ.2.1 hg1 hJ_bounds.1 h1
  have hc2 := prefix_get gJ.2.2.2.1 hg2 hJ_bounds.2 h2
  unfold IsCS
  rw [show n + 1 + J - n = J + 1 by omega, htake, elimRun_append, elimRun_cons, elimRun_nil]
  dsimp only [elimStep]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen_J]), hlen_J, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  generalize ha1 : (elimRun n (restrEnv i b, []) (gs.take J)).1.getD gJ.2.1 (.inl false) = e1
  generalize ha2 : (elimRun n (restrEnv i b, []) (gs.take J)).1.getD gJ.2.2.2.1 (.inl false) = e2
  rw [ha1] at hc1
  rw [ha2] at hc2
  rcases e1 with c1 | ⟨i1, s1⟩
  · rcases e2 with c2 | ⟨i2, s2⟩
    · cases gJ.1 <;> cases gJ.2.2.1 <;> cases gJ.2.2.2.2 <;> cases c1 <;> cases c2 <;> rfl
    · simp [symIsConst] at hc2
  · simp [symIsConst] at hc1

def relabelWire (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩).val else m + (w - n)

def relabelSGate (n m : ℕ) (π : Fin n → Fin m) (g : SGate) : SGate :=
  (g.1, relabelWire n m π g.2.1, g.2.2.1, relabelWire n m π g.2.2.2.1, g.2.2.2.2)

theorem relabelS {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (b : ℕ)
    (hc : HasBinSize n h b) : HasBinSize m (fun x => h (x ∘ π)) b := by
  obtain ⟨gs, o, os, hcl, hlen, hev⟩ := hc
  let gs' := gs.map (relabelSGate n m π)
  have hcl' : CleanS m gs' := by
    intro p g' hp
    simp only [gs', List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨g, hg, rfl⟩ := hp
    have hb := hcl p g hg
    refine ⟨?_, ?_⟩
    · dsimp [relabelSGate, relabelWire]
      split_ifs with h1
      · exact Nat.lt_of_lt_of_le (π ⟨g.2.1, h1⟩).isLt (Nat.le_add_right _ _)
      · omega
    · dsimp [relabelSGate, relabelWire]
      split_ifs with h2
      · exact Nat.lt_of_lt_of_le (π ⟨g.2.2.2.1, h2⟩).isLt (Nat.le_add_right _ _)
      · omega
  have hval : ∀ (x : Fin m → Bool) (w : ℕ),
      valS m gs' x (relabelWire n m π w) = valS n gs (x ∘ π) w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hwn : w < n
      · simp only [relabelWire, hwn, dite_true]
        rw [valS_input m gs' x _ (π ⟨w, hwn⟩).isLt, valS_input n gs (x ∘ π) w hwn]
        rfl
      · simp only [relabelWire, hwn, dite_false]
        obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
        simp only [Nat.add_sub_cancel_left]
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [valS_beyond m gs' x _ (by simp [gs']; omega), valS_beyond n gs (x ∘ π) _ (by omega)]
        | some g =>
          have hr' : gs'[r]? = some (relabelSGate n m π g) := by simp [gs', hr]
          have hb := hcl r g hr
          rw [valS_gate m gs' hcl' x r _ hr', valS_gate n gs hcl (x ∘ π) r g hr]
          dsimp [relabelSGate]
          rw [ih g.2.1 hb.1, ih g.2.2.2.1 hb.2]
  refine ⟨gs', relabelWire n m π o, os, hcl', by simpa [gs'] using hlen, ?_⟩
  intro x
  unfold evalS
  rw [hval x o]
  exact hev (x ∘ π)

section S2
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List SGate} {o : ℕ} {os : Bool}

theorem LeastS.read_dep (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (p : ℕ)
    (hp : ReadsS gs p i.val) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x; by_contra h; exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by rw [← hx]; exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc_f : ∃ x y : Fin n → Bool, f (Fin.insertNth i false x) ≠ f (Fin.insertNth i false y) := by
    obtain ⟨g0, hg0, hmem⟩ := hp
    have hp_lt : p < gs.length := (List.getElem?_eq_some_iff.1 hg0).1
    by_contra hc
    push Not at hc
    have hconst : ∀ y : Fin (n + 1) → Bool, f y = f (Fin.insertNth i false (fun _ => false)) := by
      intro y
      rw [← hfix y, ← Fin.insertNth_removeNth i false y]
      exact hc (Fin.removeNth i y) (fun _ => false)
    have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
      have ho_lt : o < (n + 1) + gs.length ∨ (n + 1) + gs.length ≤ o := lt_or_ge o ((n + 1) + gs.length)
      rcases ho_lt with ho | ho
      · by_cases hon : o < n + 1
        · let x : Fin (n + 1) → Bool := fun _ => false
          let y : Fin (n + 1) → Bool := fun j => if j = ⟨o, hon⟩ then true else false
          refine ⟨x, y, ?_⟩
          rw [← L.2.1 x, ← L.2.1 y]
          simp only [evalS, valS_input (n + 1) gs _ o hon]
          simp [x, y]
        · obtain ⟨q, rfl⟩ : ∃ q, o = n + 1 + q := ⟨o - (n + 1), by omega⟩
          have hq : q < gs.length := by omega
          by_contra hc2
          push Not at hc2
          apply L.no_const q hq (valS (n + 1) gs (fun _ => false) (n + 1 + q))
          intro x
          have := hc2 x (fun _ => false)
          rw [← L.2.1 x, ← L.2.1 (fun _ => false)] at this
          simp only [evalS] at this
          cases os <;> simp_all
      · exfalso
        have hlen_gt : 0 < gs.length := by omega
        obtain ⟨gs', o', os', hcl', hsz', hev'⟩ :=
          show ∃ gs' o' os', CleanS (n + 1) gs' ∧ gs'.length + 1 ≤ gs.length ∧
              ∀ x, evalS (n + 1) gs' o' os' x = f x from
            ⟨[], n + 1, os, by intro q g hq; simp at hq, by simp; omega, fun x => by
              rw [← L.2.1 x]
              simp [evalS, valS_beyond (n + 1) [] x (n + 1) (by simp),
                valS_beyond (n + 1) gs x o ho]⟩
        have := (L.2.2 gs' o' os' hcl' hev').1
        omega
    obtain ⟨x, y, hxy⟩ := hfnc
    exact hxy ((hconst x).trans (hconst y).symm)
  obtain ⟨s', hs', hbin⟩ := saveS L i false hnc_f {p} (by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact rcs_input false hp)
  rw [Finset.card_singleton] at hs'
  obtain ⟨gs', o', os', hcl', hsz', hev'⟩ := relabelS i.succAbove _ s' hbin
  have hev_f : ∀ y : Fin (n + 1) → Bool, evalS (n + 1) gs' o' os' y = f y := by
    intro y
    rw [hev' y]
    change f (Fin.insertNth i false (Fin.removeNth i y)) = f y
    rw [Fin.insertNth_removeNth, hfix y]
  have hmin := (L.2.2 gs' o' os' hcl' hev_f).1
  omega

theorem LeastS.nextS (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p : ℕ) (hp : p < gs.length) (hc : IsCS gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ ReadsS gs q (n + 1 + p) ∧ RCS n (restrEnv i b) gs q := by
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨hlen1, _, _, _, hev1⟩ :=
      elimRun_spec (n + 1) n gs L.1 0 (Nat.zero_le _) (restrEnv i b, []) (restrEnv_length i b)
        (by intro q g hq; simp at hq) (restrEnv_valid i b)
    simp only [List.drop_zero] at hlen1 hev1
    have htake : gs.take (n + 1 + p - n) ++ gs.drop (p + 1) = gs := by
      rw [show n + 1 + p - n = p + 1 by omega, List.take_append_drop]
    have hpre : ∃ tail, (elimRun n (restrEnv i b, []) gs).1 =
        (elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n))).1 ++ tail := by
      have hrw : elimRun n (restrEnv i b, []) gs =
          elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n) ++ gs.drop (p + 1)) := by
        rw [htake]
      rw [hrw, elimRun_append]
      exact elimRun_env_prefix n _ _
    have hlen_p : (elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n))).1.length =
        n + 1 + (p + 1) := by
      rw [elimRun_env_length, restrEnv_length, show n + 1 + p - n = p + 1 by omega, List.length_take,
        Nat.min_eq_left (by omega)]
    obtain ⟨tail, htail⟩ := hpre
    have hget_o : (elimRun n (restrEnv i b, []) gs).1.getD (n + 1 + p) (.inl false) =
        (elimRun n (restrEnv i b, []) (gs.take (n + 1 + p - n))).1.getD (n + 1 + p) (.inl false) := by
      rw [htail, List.getD_append _ _ _ _ (by rw [hlen_p]; omega)]
    unfold IsCS at hc
    rw [← hget_o] at hc
    rcases hc_val : (elimRun n (restrEnv i b, []) gs).1.getD (n + 1 + p) (.inl false) with c | ⟨w, s⟩
    · obtain ⟨x, y, hxy⟩ := hnc
      have hx := hev1 x (Fin.insertNth i b x) (fun u hu => restrEnv_eval i b x gs u (by simpa [restrEnv_length] using hu)) (n + 1 + p) (by rw [hlen1]; omega)
      have hy := hev1 y (Fin.insertNth i b y) (fun u hu => restrEnv_eval i b y gs u (by simpa [restrEnv_length] using hu)) (n + 1 + p) (by rw [hlen1]; omega)
      rw [hc_val] at hx hy
      apply hxy
      rw [← L.2.1, ← L.2.1]
      simp only [evalS, e]
      rw [← hx, ← hy]
      rfl
    · rw [hc_val] at hc
      cases hc
  obtain ⟨q, hpq, hr⟩ := L.live p hp ho
  exact ⟨q, hpq, hr, rcs_of_reads hpq hr hc⟩

theorem LeastS.save2 (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RCS n (restrEnv i b) gs p1) (h2 : RCS n (restrEnv i b) gs p2) :
    DropS f i b 2 gs.length := by
  have := saveS L i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem LeastS.save3 (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RCS n (restrEnv i b) gs p1) (h2 : RCS n (restrEnv i b) gs p2)
    (h3 : RCS n (restrEnv i b) gs p3) : DropS f i b 3 gs.length := by
  have := saveS L i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem LeastS.save4 (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RCS n (restrEnv i b) gs p1) (h2 : RCS n (restrEnv i b) gs p2)
    (h3 : RCS n (restrEnv i b) gs p3) (h4 : RCS n (restrEnv i b) gs p4) :
    DropS f i b 4 gs.length := by
  have := saveS L i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this

theorem LeastS.third (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p q : ℕ) (hpq : p ≠ q) (hp : ReadsS gs p i.val) (hq : ReadsS gs q i.val)
    (hc : IsCS gs i b (n + 1 + p)) : DropS f i b 3 gs.length := by
  have hp_len : p < gs.length := let ⟨_, hgp, _⟩ := hp; (List.getElem?_eq_some_iff.1 hgp).1
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.nextS i b hnc p hp_len hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri p J i.val hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rcs_input b hp) (rcs_input b hq) hJrc

theorem LeastS.fourth (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p q : ℕ) (hpq : p ≠ q) (hp : ReadsS gs p i.val) (hq : ReadsS gs q i.val)
    (hcp : IsCS gs i b (n + 1 + p)) (hcq : IsCS gs i b (n + 1 + q)) :
    DropS f i b 4 gs.length := by
  have hp_len : p < gs.length := let ⟨_, hgp, _⟩ := hp; (List.getElem?_eq_some_iff.1 hgp).1
  have hq_len : q < gs.length := let ⟨_, hgq, _⟩ := hq; (List.getElem?_eq_some_iff.1 hgq).1
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.nextS i b hnc p hp_len hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.nextS i b hnc q hq_len hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri p J1 i.val hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri q J2 i.val hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : ReadsS gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have eqg : gJ' = gJ := by rw [hgJ] at hgJ'; exact (Option.some.inj hgJ').symm
    rw [eqg] at hinq
    have hpq_wire : n + 1 + p ≠ n + 1 + q := by omega
    have hg_inputs : (gJ.2.1 = n + 1 + p ∧ gJ.2.2.2.1 = n + 1 + q) ∨
        (gJ.2.1 = n + 1 + q ∧ gJ.2.2.2.1 = n + 1 + p) := by
      rcases hinp with a1 | a2 <;> rcases hinq with b1 | b2
      · exact False.elim (hpq_wire (a1.symm.trans b1))
      · exact Or.inl ⟨a1, b2⟩
      · exact Or.inr ⟨b1, a2⟩
      · exact False.elim (hpq_wire (a2.symm.trans b2))
    have hcJ : IsCS gs i b (n + 1 + J1) := by
      rcases hg_inputs with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact isCS_both_const L.1 i b J1 gJ hgJ (e1 ▸ hcp) (e2 ▸ hcq) (by omega) (by omega)
      · exact isCS_both_const L.1 i b J1 gJ hgJ (e1 ▸ hcq) (e2 ▸ hcp) (by omega) (by omega)
    have hJ_len : J1 < gs.length := (List.getElem?_eq_some_iff.1 hgJ).1
    obtain ⟨K, hKJ, _, hKrc⟩ := L.nextS i b hnc J1 hJ_len hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rcs_input b hp) (rcs_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rcs_input b hp) (rcs_input b hq) h1rc h2rc

theorem LeastS.two_readers (L : LeastS (n + 1) f gs o os) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin n → Bool, f (Fin.insertNth i b x) ≠ f (Fin.insertNth i b y))
    (p q : ℕ) (hpq : p ≠ q) (hp : ReadsS gs p i.val) (hq : ReadsS gs q i.val) :
    PaysS f i gs.length := by
  let ⟨gp, hgp, hip⟩ := hp
  let ⟨gq, hgq, hiq⟩ := hq
  let bp := xor gp.1 (if gp.2.1 = i.val then gp.2.2.1 else gp.2.2.2.2)
  let bq := xor gq.1 (if gq.2.1 = i.val then gq.2.2.1 else gq.2.2.2.2)
  have cp : IsCS gs i bp (n + 1 + p) := isCS_reader L.1 i p gp hgp hip bp rfl
  have cq : IsCS gs i bq (n + 1 + q) := isCS_reader L.1 i q gq hgq hiq bq rfl
  by_cases hbpq : bp = bq
  · cases hc : bp
    · rw [hc] at cp
      rw [← hbpq, hc] at cq
      exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq cp cq,
        L.save2 i true (hnc true) p q hpq (rcs_input true hp) (rcs_input true hq)⟩)
    · rw [hc] at cp
      rw [← hbpq, hc] at cq
      exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rcs_input false hp)
        (rcs_input false hq), L.fourth i true (hnc true) p q hpq hp hq cp cq⟩)
  · have key : ∀ b, DropS f i b 3 gs.length := by
      intro b
      by_cases hb : b = bp
      · subst hb; exact L.third i bp (hnc bp) p q hpq hp hq cp
      · have hb' : b = bq := by
          revert hb hbpq
          cases b <;> cases bp <;> cases bq <;> simp
        subst hb'; exact L.third i bq (hnc bq) q p (Ne.symm hpq) hq hp cq
    exact Or.inl ⟨key false, key true⟩

theorem agree_beyond_S (gs : List SGate) (hcl : CleanS (n + 1) gs)
    (v1 v2 : Fin (n + 1))
    (hno1 : ∀ r, 0 < r → ¬ ReadsS gs r v1.val)
    (hno2 : ∀ r, 0 < r → ¬ ReadsS gs r v2.val)
    (u u' : Fin (n + 1) → Bool)
    (hagr : ∀ i : Fin (n + 1), i ≠ v1 → i ≠ v2 → u i = u' i)
    (hg0 : valS (n + 1) gs u (n + 1 + 0) = valS (n + 1) gs u' (n + 1 + 0)) :
    ∀ w : ℕ, w ≠ v1.val → w ≠ v2.val → valS (n + 1) gs u w = valS (n + 1) gs u' w := by
  intro w hv1 hv2
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hwn : w < n + 1
    · rw [valS_input (n + 1) gs u w hwn, valS_input (n + 1) gs u' w hwn]
      exact hagr ⟨w, hwn⟩ (fun e => hv1 (congrArg Fin.val e)) (fun e => hv2 (congrArg Fin.val e))
    · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
      cases r with
      | zero => exact hg0
      | succ r =>
        cases hr : gs[r + 1]? with
        | none =>
          have hl : gs.length ≤ r + 1 := List.getElem?_eq_none_iff.1 hr
          rw [valS_beyond (n + 1) gs u _ (by omega), valS_beyond (n + 1) gs u' _ (by omega)]
        | some g =>
          have hb := hcl (r + 1) g hr
          have hn11 : g.2.1 ≠ v1.val := fun e => hno1 (r + 1) (by omega) ⟨g, hr, Or.inl e⟩
          have hn12 : g.2.1 ≠ v2.val := fun e => hno2 (r + 1) (by omega) ⟨g, hr, Or.inl e⟩
          have hn21 : g.2.2.2.1 ≠ v1.val := fun e => hno1 (r + 1) (by omega) ⟨g, hr, Or.inr e⟩
          have hn22 : g.2.2.2.1 ≠ v2.val := fun e => hno2 (r + 1) (by omega) ⟨g, hr, Or.inr e⟩
          rw [valS_gate (n + 1) gs hcl u (r + 1) g hr, valS_gate (n + 1) gs hcl u' (r + 1) g hr]
          rw [ih g.2.1 hb.1 hn11 hn12, ih g.2.2.2.1 hb.2 hn21 hn22]

theorem LeastS.funnel (L : LeastS (n + 1) f gs o os) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), ReadsS gs p i.val → ReadsS gs q i.val → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  have hne : gs ≠ [] := by
    rintro rfl
    by_cases hon : o < n + 1
    · let v : Fin (n + 1) := ⟨o, hon⟩
      have hv_eq : ∀ x, f x = xor (x v) os := by
        intro x
        rw [← L.2.1 x, evalS, valS_input (n + 1) [] x o hon]
      have hdv : Dep f v := ⟨fun _ => false, by rw [hv_eq, hv_eq]; cases os <;> simp⟩
      obtain ⟨x, y, hxy⟩ := hnc v hdv false
      apply hxy
      rw [hv_eq, hv_eq]
      simp
    · obtain ⟨p, x, hx⟩ := hdep
      apply hx
      rw [← L.2.1, ← L.2.1]
      simp [evalS, valS_beyond (n + 1) [] _ o (by simp; omega)]
  obtain ⟨g0, hg0⟩ : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil => exact False.elim (hne rfl)
    | cons g0 _ => exact ⟨g0, rfl⟩
  have hb0 := L.1 0 g0 hg0
  let vj : Fin (n + 1) := ⟨g0.2.1, hb0.1⟩
  let vk : Fin (n + 1) := ⟨g0.2.2.2.1, hb0.2⟩
  have hvjk : vj ≠ vk := fun e => L.no_same_inputs 0 g0 hg0 (congrArg Fin.val e)
  have hRj : ReadsS gs 0 vj.val := ⟨g0, hg0, Or.inl rfl⟩
  have hRk : ReadsS gs 0 vk.val := ⟨g0, hg0, Or.inr rfl⟩
  have hdvj := L.read_dep vj 0 hRj
  have hdvk := L.read_dep vk 0 hRk
  have hno_j : ∀ r, 0 < r → ¬ ReadsS gs r vj.val := by
    intro r hr hrr
    have := h1 vj 0 r hRj hrr
    omega
  have hno_k : ∀ r, 0 < r → ¬ ReadsS gs r vk.val := by
    intro r hr hrr
    have := h1 vk 0 r hRk hrr
    omega
  have ho_j : o ≠ vj.val := by
    intro e
    have hv_eq : ∀ x, f x = xor (x vj) os := by
      intro x
      rw [← L.2.1 x, evalS, e, valS_input (n + 1) gs x vj.val vj.isLt]
    obtain ⟨x, y, hxy⟩ := hnc vj hdvj false
    apply hxy
    rw [hv_eq, hv_eq]
    simp
  have ho_k : o ≠ vk.val := by
    intro e
    have hv_eq : ∀ x, f x = xor (x vk) os := by
      intro x
      rw [← L.2.1 x, evalS, e, valS_input (n + 1) gs x vk.val vk.isLt]
    obtain ⟨x, y, hxy⟩ := hnc vk hdvk false
    apply hxy
    rw [hv_eq, hv_eq]
    simp
  have hval0 : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      valS (n + 1) gs (set2 x vj a vk b) (n + 1 + 0) =
        evalOp g0.1 (xor a g0.2.2.1) (xor b g0.2.2.2.2) := by
    intro x a b
    rw [valS_gate (n + 1) gs L.1 _ 0 g0 hg0,
      valS_input (n + 1) gs _ g0.2.1 hb0.1,
      valS_input (n + 1) gs _ g0.2.2.2.1 hb0.2]
    change evalOp g0.1 (xor (set2 x vj a vk b vj) g0.2.2.1) (xor (set2 x vj a vk b vk) g0.2.2.2.2) = _
    simp [set2, Function.update_of_ne hvjk]
  have KC : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool),
      valS (n + 1) gs (set2 x vj a vk b) (n + 1 + 0) =
        valS (n + 1) gs (set2 x vj a' vk b') (n + 1 + 0) →
      f (set2 x vj a vk b) = f (set2 x vj a' vk b') := by
    intro x a b a' b' hg_eq
    rw [← L.2.1, ← L.2.1]
    simp only [evalS]
    congr 1
    apply agree_beyond_S gs L.1 vj vk hno_j hno_k _ _ _ hg_eq o ho_j ho_k
    intro i hi1 hi2
    simp [set2, Function.update_of_ne hi1, Function.update_of_ne hi2]
  refine ⟨vj, vk, hvjk, hdvj, hdvk, if g0.1 then g0.2.2.1 else !g0.2.2.1,
    if g0.1 then g0.2.2.2.2 else !g0.2.2.2.2, fun x => ?_⟩
  constructor <;> apply KC <;> rw [hval0, hval0] <;>
    cases g0.1 <;> cases g0.2.2.1 <;> cases g0.2.2.2.2 <;> rfl

end S2

theorem fanout_step_bin (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : ℕ)
    (hdep : ∃ p, Dep f p) (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasBinSize (n + 1) f b) :
    ∃ y : Fin (n + 1), PaysS f y b := by
  obtain ⟨gs, o, os, L, hlen⟩ := exists_leastS (n + 1) f b h
  have mono : ∀ y, PaysS f y gs.length → PaysS f y b := by
    intro y hp
    rcases hp with ⟨a, c⟩ | ⟨a, c⟩ | ⟨a, c⟩
    · exact Or.inl ⟨DropS_mono a le_rfl hlen, DropS_mono c le_rfl hlen⟩
    · exact Or.inr (Or.inl ⟨DropS_mono a le_rfl hlen, DropS_mono c le_rfl hlen⟩)
    · exact Or.inr (Or.inr ⟨DropS_mono a le_rfl hlen, DropS_mono c le_rfl hlen⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ ReadsS gs p i.val ∧ ReadsS gs q i.val
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep i p hp
    have hnc_i : ∀ c : Bool, ∃ x y : Fin n → Bool, f (Fin.insertNth i c x) ≠ f (Fin.insertNth i c y) := by
      intro c
      obtain ⟨x, y, hxy⟩ := hnc i hd c
      refine ⟨Fin.removeNth i x, Fin.removeNth i y, ?_⟩
      simpa [Fin.insertNth_removeNth] using hxy
    exact ⟨i, mono i (L.two_readers i hnc_i p q hpq hp hq)⟩
  · exfalso
    obtain ⟨p, q, hpq, hdp, hdq, hpf⟩ := L.funnel hdep hnc (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    exact hnf p q hpq hdp hdq hpf

theorem restrictS_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (i : Fin (n + 1)) (c : Bool)
    (b : ℕ) (hdep : Dep f i)
    (hnc : ∃ x y : Fin n → Bool, f (Fin.insertNth i c x) ≠ f (Fin.insertNth i c y))
    (h : HasBinSize (n + 1) f b) :
    ∃ b', b' + 1 ≤ b ∧ HasBinSize n (fun x => f (Fin.insertNth i c x)) b' := by
  obtain ⟨gs, o, os, L, hlen⟩ := exists_leastS (n + 1) f b h
  have hex : ∃ p, ReadsS gs p i.val := by
    by_contra hno
    push Not at hno
    by_cases hoi : o = i.val
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      rw [← L.2.1, ← L.2.1]
      simp only [evalS, hoi, valS_input (n + 1) gs _ i.val i.isLt]
      simp
    · have hind : ∀ (x : Fin (n + 1) → Bool) (w : ℕ), w ≠ i.val →
          valS (n + 1) gs (Function.update x i (!x i)) w = valS (n + 1) gs x w := by
        intro x w hw
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          by_cases hwn : w < n + 1
          · rw [valS_input (n + 1) gs _ w hwn, valS_input (n + 1) gs _ w hwn]
            have hne : (⟨w, hwn⟩ : Fin (n + 1)) ≠ i := fun e => hw (congrArg Fin.val e)
            exact Function.update_of_ne hne (!x i) x
          · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
            cases hr : gs[r]? with
            | none =>
              have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
              rw [valS_beyond (n + 1) gs _ _ (by omega), valS_beyond (n + 1) gs _ _ (by omega)]
            | some g =>
              have hb := L.1 r g hr
              have hn1 : g.2.1 ≠ i.val := fun e => hno r ⟨g, hr, Or.inl e⟩
              have hn2 : g.2.2.2.1 ≠ i.val := fun e => hno r ⟨g, hr, Or.inr e⟩
              rw [valS_gate (n + 1) gs L.1 _ r g hr, valS_gate (n + 1) gs L.1 _ r g hr]
              rw [ih g.2.1 hb.1 hn1, ih g.2.2.2.1 hb.2 hn2]
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← L.2.1, ← L.2.1]
      simp only [evalS]
      rw [hind x o hoi]
  obtain ⟨p, hp⟩ := hex
  obtain ⟨s', hs', hbin⟩ := saveS L i c hnc {p} (by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    exact rcs_input c hp)
  rw [Finset.card_singleton] at hs'
  exact ⟨s', by omega, hbin⟩

def maj5 (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfee8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem maj5_dep : ∃ p : Fin 5, Dep maj5 p :=
  ⟨0, fun i => decide (i = 1 ∨ i = 2), by decide +kernel⟩

theorem maj5_nc : RestrNC maj5 := by
  intro p _ b
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have hall : ∀ (p : Fin 5) (b : Bool),
      maj5 (Function.update (fun _ => false) p b) ≠
      maj5 (Function.update (fun _ => true) p b) := by
    decide +kernel
  exact hall p b

set_option maxRecDepth 16000 in
theorem maj5_nf : NoFunnel maj5 := by
  have hnot : ∀ (p q : Fin 5) (a b : Bool), p ≠ q →
      ¬ (∀ x : Fin 5 → Bool,
          maj5 (set2 x p (!a) q b) = maj5 (set2 x p a q (!b)) ∧
          maj5 (set2 x p a q (!b)) = maj5 (set2 x p (!a) q (!b))) := by
    decide +kernel
  intro p q hpq _ _ ⟨a, b, h⟩
  exact hnot p q a b hpq h

set_option maxRecDepth 8000 in
theorem maj5_cofactor : ∀ (p : Fin 5) (c : Bool) (x : Fin 4 → Bool),
    maj5 (Fin.insertNth p c x) = target4 (if c then 0xfee8 else 0xe880) x := by
  decide +kernel

theorem bound_maj5 (b : ℕ) (h : HasBinSize 5 maj5 b) : 10 ≤ b := by
  obtain ⟨y, hp⟩ := fanout_step_bin 4 maj5 b maj5_dep maj5_nc maj5_nf h
  have drop_lb : ∀ (c : Bool) (k : ℕ), DropS maj5 y c k b → k + 7 ≤ b := by
    intro c k ⟨s', hs', hbin⟩
    have heq : (fun x : Fin 4 → Bool => maj5 (Fin.insertNth y c x)) =
        target4 (if c then 0xfee8 else 0xe880) := funext (maj5_cofactor y c)
    rw [heq] at hbin
    cases c
    · have := bound_th3_4 s' hbin; omega
    · have := bound_th2_4 s' hbin; omega
  rcases hp with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, h1⟩
  · exact drop_lb false 3 h0
  · have := drop_lb false 4 h0; omega
  · have := drop_lb true 4 h1; omega

def target6 (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676736 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem target6_dep5 : Dep target6 5 :=
  ⟨fun i => decide (i = 0 ∨ i = 1 ∨ i = 3), by decide +kernel⟩

set_option maxRecDepth 8000 in
theorem target6_x5_true : ∀ x : Fin 5 → Bool, target6 (Fin.insertNth 5 true x) = maj5 x := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem maj5_nc_pair : ∃ x y : Fin 5 → Bool, maj5 x ≠ maj5 y := by
  decide +kernel

theorem bound_target6_bin (b : ℕ) (h : HasBinSize 6 target6 b) : 11 ≤ b := by
  have hnc : ∃ x y : Fin 5 → Bool, target6 (Fin.insertNth 5 true x) ≠ target6 (Fin.insertNth 5 true y) := by
    simpa only [target6_x5_true] using maj5_nc_pair
  obtain ⟨b', hb', hbin⟩ := restrictS_one 5 target6 5 true b target6_dep5 hnc h
  have heq : (fun x : Fin 5 → Bool => target6 (Fin.insertNth 5 true x)) = maj5 :=
    funext target6_x5_true
  rw [heq] at hbin
  have := bound_maj5 b' hbin
  omega

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [6, 8]⟩,
    ⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [2, 12]⟩,
    ⟨.and, [9, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [15, 16]⟩], 17⟩

theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target6 x := by
  decide +kernel

theorem main_proof : ∀ s : ℕ, HasCircuitSize 6 target6 s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target6 x := by
  intro s hs
  obtain ⟨C, hfan, hsize, heval⟩ := hs
  by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hmem, hop⟩ := hnot
    have hlt : binaryCost C.gates < C.size := by
      unfold binaryCost Circuit.size
      exact List.length_filter_lt_length_iff_exists.mpr ⟨g, hmem, by simp [isBinary, hop]⟩
    have hnc : ∃ x y : Fin 6 → Bool, target6 x ≠ target6 y := by
      obtain ⟨x, y, hxy⟩ := maj5_nc_pair
      refine ⟨Fin.insertNth 5 true x, Fin.insertNth 5 true y, ?_⟩
      simpa only [target6_x5_true] using hxy
    have hbin := compileToSigned 6 target6 hnc C hfan heval
    have hlb := bound_target6_bin (binaryCost C.gates) hbin
    have hwlen : witness.size = 12 := rfl
    exact ⟨witness, witness_mono, by omega, witness_eval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact ⟨Or.inl h, hlen⟩
    · exact ⟨Or.inr h, hlen⟩
    · exact False.elim (hnot ⟨g, hg, h⟩)

end PEqualNP.Outside.L_meta_12296

theorem PEqualNP.Outside.L_meta_12296 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :=
  PEqualNP.Outside.L_meta_12296.main_proof

