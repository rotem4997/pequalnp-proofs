import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14798

open CircuitLowerBounds


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
theorem allOnes_eq : (~~~(0 : W)) = BitVec.allOnes 512 := by decide +kernel

theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · rw [allOnes_eq]
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · rw [allOnes_eq]
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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 512 0)[k.val] = false; simp
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
    show ∀ x : W, x &&& ~~~0 = x from fun x => by rw [allOnes_eq, BitVec.and_allOnes]]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (word : W) (hnil : word ≠ 0) (hone : word ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (word)) :
    ∃ t, (t = word ∨ t = ~~~word) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = word := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (hnil zero)
    · exact False.elim (hone ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (word) := by
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
theorem bound_from_impossible {m : ℕ} (n : ℕ) (word : W) (hnil : word ≠ 0) (hone : word ≠ ~~~0) (inputs : List W) (f : (Fin m → Bool) → Bool)
    (width : inputs.length = m)
    (sample_rows : ∀ j : Fin 512, f (fun i => (inputs.getD i.val 0)[j.val]) = (word)[j.val])
    (impossible : ∀ t, t = word ∨ t = ~~~word → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin m → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (word) := by
    let x (i : Fin m) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (word)
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile word hnil hone gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

def m0 : W := 0xc20800800400208005220902001484290880011a204040a240369014180610a4c3318db72d9c76f66fe2ab0e4994c7794cb450164afcc3b66727901d182617af
def m1 : W := 0x03a00a900206409c348041e2822005408100c1d2644906844900035501142a60ef2778f850e97839748a647a866b21cba99ac3fbea8b4cc4db4a2bd5091cea60
def m2 : W := 0x0d40226313090921008002c051005892a43320e0da042e1821c004a800b1aa18bbdceb274e0fa22988e303e373157bd6e7f21454df06329b89ec04a842f1baf8
def m3 : W := 0x884984011c002c6141211209040d40206499020c0130d80880b3d0802e88449c120fe9cef27b6d31f4145a5fae2fc830f9bd2e0ff130fc4a80725192af89649c
def m4 : W := 0x00b2c00c8016020ea805600c08eb024441084c0005a3004114094a01e34045427fc8f6953666b48fbc1db2ec5c63966e434ac45015a2f17d45ad9e21e3c64d42
def m5 : W := 0x2412004460380000085880002982300400662c210882201036402c0a8041800365f392f6e1b9cdea0bdc9c01b8f668a1b06fefe309ff20b97a526e4eb4518017

def minorInputs : List W := [m0, m1, m2, m3, m4, m5]

def minorIndex (j : Fin 512) : ℕ :=
  (m0[j.val]).toNat * 1 + (m1[j.val]).toNat * 2 + (m2[j.val]).toNat * 4 + (m3[j.val]).toNat * 8 + (m4[j.val]).toNat * 16 + (m5[j.val]).toNat * 32

set_option maxRecDepth 10000 in
theorem minor_labels : ∀ j : Fin 512,
    (0xfffeffeefefaeca0 : BitVec 64).getLsbD (minorIndex j) = (~~~goal)[j.val] := by
  decide +kernel

theorem minor_all_needed : minorInputs.sublists.all (fun l => l == minorInputs || cuts l != -1) = true := by
  decide +kernel

def edgeList : List ℕ := [0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7]

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2 * i + 1) 0) false = true)

private def witness : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [9, 10]⟩,
   ⟨.or, [0, 5]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.and, [0, 5]⟩,
   ⟨.or, [1, 7]⟩, ⟨.and, [4, 16]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [18, 15]⟩,
   ⟨.or, [19, 17]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem upper (n : ℕ) (hn : 13 ≤ n) :
    ∃ (gs : List Gate) (o : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ n ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = target x := by
  refine ⟨witness, 20, ?_, hn, ?_⟩
  · simp [witness]
  · have allRows : ∀ a b c d e f g h : Bool,
        let x : Fin 8 → Bool := ![a, b, c, d, e, f, g, h]
        (Circuit.mk witness 20).eval (List.ofFn x) = target x := by decide +kernel
    intro x
    have hx : ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] = x := by
      funext i
      fin_cases i <;> rfl
    exact hx ▸ allRows (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

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
    first | (rwa [absorb]) | simp_all

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

def reindex (f : Fin 512 → Fin 512) (x : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 512 → Fin 512) (a : W) (j : Nat) (hj : j < 512) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 512 → Fin 512) (a b : W) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 512 → Fin 512) (a b : W) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 512 → Fin 512) (a : W) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

def distinguishes (i j : ℕ) (x : W) : Prop := x.getLsbD i ≠ x.getLsbD j

theorem op_distinguishes (i j : Fin 512) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (h : distinguishes i j z) : distinguishes i j a ∨ distinguishes i j b := by
  by_contra! h'
  obtain ⟨ha,hb⟩ := h'
  simp only [distinguishes, not_not] at ha hb
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  apply h
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, ha, hb, i.isLt, j.isLt, decide_true, Bool.true_and]

theorem pin_bound (input output : List W) (old new : W) (r : Fin 512 → Fin 512)
    (p : W) (i j : Fin 512) (k : ℕ)
    (hd : old.getLsbD i.val ≠ old.getLsbD j.val)
    (hu : ∀ w ∈ input, w ≠ p → w.getLsbD i.val = w.getLsbD j.val)
    (hn : p ≠ old ∧ p ≠ ~~~old) (hz : reindex r p = 0)
    (hv : ∀ w ∈ input, holds output.toFinset (reindex r w))
    (hr : reindex r old = new) (nc : new ≠ 0 ∧ new ≠ ~~~0)
    (t : W) (ht : t = old ∨ t = ~~~old) (hb : build basicOps t (k+1) input.toFinset) :
    ∃ u, (u = new ∨ u = ~~~new) ∧ build basicOps u k output.toFinset := by
  obtain ⟨s,hs,hl⟩ := compress hb
  have dt : distinguishes i.val j.val t := by
    rcases ht with rfl | rfl
    · exact hd
    · simpa [distinguishes, BitVec.getLsbD_not, i.isLt, j.isLt] using hd
  obtain ⟨v,hv',hdv⟩ := live_separates _ dt (op_distinguishes i j) hl
  have vp : v = p := by
    by_contra ne
    exact hdv (hu v (List.mem_toFinset.mp (hs hv')) ne)
  have transported := live_transport_save (ops_map_of (reindex_and r) (reindex_or r) (reindex_not r)) hl
    (vp ▸ hv') (ht.elim (fun e => e ▸ hn.1) (fun e => e ▸ hn.2)) hz
    (fun w hw => hv w (List.mem_toFinset.mp (hs hw)))
  have sign : reindex r t = new ∨ reindex r t = ~~~new := by
    rcases ht with rfl | rfl
    · exact Or.inl hr
    · exact Or.inr (by rw [reindex_not, hr])
  have comp : (~~~reindex r t) = new ∨ (~~~reindex r t) = ~~~new := by
    rcases sign with h|h <;> simp [h]
  rcases transported with bad | bad | ht' | ht'
  · rcases sign with h | h
    · exact (nc.1 (h.symm.trans bad)).elim
    · exact (nc.2 (by simpa using congrArg (fun x : W => ~~~x) (h.symm.trans bad))).elim
  · rcases sign with h | h
    · exact (nc.2 (h.symm.trans bad)).elim
    · exact (nc.1 (by simpa using congrArg (fun x : W => ~~~x) (h.symm.trans bad))).elim
  · exact ⟨_,sign,ht'⟩
  · exact ⟨_,comp,ht'⟩


def q0 : W := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def q1 : W := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def q2 : W := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def q3 : W := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def q4 : W := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def q5 : W := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def q6 : W := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def q7 : W := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000

def orig : W := 0xfffffffffffffffffffffffffefaeca0fffefffefefefefefffeffeefefaeca0fffffffffffffffffffffffffefaeca0fffefffefefefefefffeffeefefaeca0
def mid : W := 0xfffefffefefefefefffeffeefefaeca0fffefffefefefefefffeffeefefaeca0fffefffefefefefefffeffeefefaeca0fffefffefefefefefffeffeefefaeca0
def origInputs : List W := [q0,q1,q7,q2,q3,q4,q6,q5]
def midInputs : List W := [q0,q1,q2,q3,q4,q5,q6]

def rSeven (j : Fin 512) : Fin 512 := Fin.ofNat 512 (j.val % 128)
def rSix (j : Fin 512) : Fin 512 := Fin.ofNat 512 (minorIndex j)
theorem reindex_eq_of_rows (r : Fin 512 → Fin 512) (x y : W)
    (h : ∀ j : Fin 512, x.getLsbD (r j).val = y.getLsbD j.val) : reindex r x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]; exact h ⟨j,hj⟩

theorem kept_eq {ls : List W} {z v : W} (hm : v ∈ ls) (he : z = v) : holds ls.toFinset z :=
  .inr (.inr ⟨v, List.mem_toFinset.mpr hm, .inl he⟩)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pin_first (t : W) (ht : t = orig ∨ t = ~~~orig) (hb : build basicOps t 11 origInputs.toFinset) :
    ∃ u, (u = mid ∨ u = ~~~mid) ∧ build basicOps u 10 midInputs.toFinset := by
  have hv : ∀ w ∈ origInputs, holds midInputs.toFinset (reindex rSeven w) := by
    intro w hw
    simp only [origInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := q0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := q1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := q2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := q3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := q4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := q6) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := q5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  obtain ⟨u,hu,hrun⟩ := pin_bound origInputs midInputs orig mid rSeven q7 192 64 10
    (by decide +kernel) (by
      intro w hw
      simp only [origInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel)) hv
    (reindex_eq_of_rows _ _ _ (by decide +kernel)) (by decide +kernel) t ht hb
  exact ⟨u, hu, hrun⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pin_second (t : W) (ht : t = mid ∨ t = ~~~mid) (hb : build basicOps t 10 midInputs.toFinset) :
    ∃ u, (u = goal ∨ u = ~~~goal) ∧ build basicOps u 9 minorInputs.toFinset := by
  have hv : ∀ w ∈ midInputs, holds minorInputs.toFinset (reindex rSix w) := by
    intro w hw
    simp only [midInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := m0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := m1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := m2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := m3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := m4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := m5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
  obtain ⟨u,hu,hrun⟩ := pin_bound midInputs minorInputs mid (~~~goal) rSix q6 68 4 9
    (by decide +kernel) (by
      intro w hw
      simp only [midInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel)) hv
    (reindex_eq_of_rows _ _ _ (by decide +kernel)) (by decide +kernel) t ht hb
  exact ⟨u, by simpa [or_comm] using hu, hrun⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem truth_labels : ∀ j : Fin 512, target (fun i => (origInputs.getD i.val 0)[j.val]) = orig[j.val] := by
  decide +kernel

theorem solve (small : ∀ t : W, t = goal ∨ t = ~~~goal → build basicOps t 9 minorInputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = target x) :
    ∃ (gs' : List Gate) (o' : ℕ),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs' o').eval (List.ofFn x) = target x := by
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g,hm,hnot⟩ := hn
    have lb := bound_from_impossible 11 orig (by decide +kernel) (by decide +kernel) origInputs target rfl truth_labels
      (fun t ht hb => by
        obtain ⟨v,hv,hb'⟩ := pin_first t ht hb
        obtain ⟨u,hu,hb''⟩ := pin_second v hv hb'
        exact small u hu hb'') gs o hg he
    have hlt : binaryCost gs < gs.length := by
      have le := List.length_filter_le isBinary gs
      apply lt_of_le_of_ne le
      intro eq
      have bit := List.length_filter_eq_length_iff.mp eq g hm
      simp [isBinary, hnot] at bit
    exact upper _ (by omega)
  · refine ⟨gs, o, ?_, le_rfl, he⟩
    intro g hm
    obtain ⟨hop, cap⟩ := hg g hm
    refine ⟨?_,cap⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g,hm,h⟩).elim


abbrev CreditRow := W × List W × ℕ

def CreditRow.mask (p : CreditRow) : W := p.1
def CreditRow.refs (p : CreditRow) : List W := p.2.1
def CreditRow.cost (p : CreditRow) : ℕ := p.2.2

def CreditSound (p : CreditRow) : Prop :=
  ∃ (f : W → W) (av : Finset W),
    (∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b)) ∧
    (∀ w, (w &&& p.mask = 0 ∨ w &&& p.mask = p.mask) → (f w = 0 ∨ f w = ~~~0)) ∧
    (∀ w, (w &&& p.mask) ∈ p.refs → holds av (f w)) ∧
    (∀ t, (t = goal ∨ t = ~~~goal) → ∀ k, SignedBuild k av (f t) → p.cost ≤ k)


abbrev cwire (w : W) : Prop := w = 0 ∨ w = ~~~0

theorem const_holds {av : Finset W} {w : W} (h : cwire w) : holds av w := h.elim .inl (fun h => .inr (.inl h))

set_option maxRecDepth 4000 in
theorem paid_const_fold {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hc : cwire x ∨ cwire y) (hz : z ∈ basicOps x y) : holds av z := by
  have h0 : holds av (0 : W) := .inl rfl
  have h1 : holds av (~~~(0 : W)) := .inr (.inl rfl)
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by rw [allOnes_eq, BitVec.and_allOnes]
  have absorb' (v : W) : (~~~(0 : W)) &&& v = v := by rw [allOnes_eq, BitVec.allOnes_and]
  have allr (v : W) : v ||| (~~~(0 : W)) = ~~~0 := by rw [allOnes_eq, BitVec.or_allOnes]
  have alll (v : W) : (~~~(0 : W)) ||| v = ~~~0 := by rw [allOnes_eq, BitVec.allOnes_or]
  have zr (v : W) : v &&& (0 : W) = 0 := BitVec.and_zero
  have zl (v : W) : (0 : W) &&& v = 0 := BitVec.zero_and
  have ur (v : W) : v ||| (0 : W) = v := BitVec.or_zero
  have ul (v : W) : (0 : W) ||| v = v := BitVec.zero_or
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hc with (rfl|rfl)|(rfl|rfl) <;> rcases hz with rfl|rfl|rfl|rfl <;>
    simp only [zl, zr, ur, ul, absorb, absorb', allr, alll, BitVec.not_not] <;>
    first | assumption | exact holds_not hx | exact holds_not hy

theorem const_const_fold {x y z : W} (hx : cwire x) (hy : cwire y) (hz : z ∈ basicOps x y) : cwire z := by
  have h := paid_const_fold (av := ∅) (const_holds hx) (const_holds hy) (.inl hx) hz
  simpa [holds,cwire] using h

def marked (f : W → W) (s : Finset W) := (s.filter (fun w => cwire (f w))).card

theorem marked_false (f : W → W) (s : Finset W) (w : W) (h : ¬ cwire (f w)) : marked f (insert w s) = marked f s := by
  simp [marked, Finset.filter_insert, h]

theorem marked_bound (f : W → W) (s : Finset W) (w : W) : marked f s ≤ marked f (insert w s) ∧ marked f (insert w s) ≤ marked f s + 1 := by
  by_cases h : cwire (f w)
  · simp only [marked, Finset.filter_insert, h, ite_true]
    exact ⟨Finset.card_le_card (Finset.subset_insert ..), Finset.card_insert_le ..⟩
  · rw [marked_false _ _ _ h]; omega

theorem live_credit {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} (nc : ¬ cwire (f g)) {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : ∃ j, SignedBuild j av (f g) ∧ j + marked f s ≤ k := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    subst s
    refine ⟨0,sb_zero (hav g (by simp)), ?_⟩
    change 0 + marked f (insert g ∅) ≤ 0
    rw [marked_false _ _ _ nc]
    simp [marked]
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
    · obtain ⟨j,hr,le⟩ := ih skip hav
      exact ⟨j,hr,by omega⟩
    · have hop := hm a b z hz
      have old (u : W) (hu : u ∈ r) := hav u (by simp [he,hu])
      have bound_z := marked_bound f r z
      have bound_a := marked_bound f (insert b r) a
      have bound_b := marked_bound f r b
      have next (av' : Finset W) (sub : av ⊆ av') (hnew : holds av' (f z)) :=
        ih tail (av := av') (by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl|hm
          · exact hnew
          · exact sb_holds_mono sub (old _ hm))
      by_cases ha' : cwire (f a) <;> by_cases hb' : cwire (f b)
      · have zz := const_const_fold ha' hb' hop
        have zr : z ∉ r := fun h => hout (by simp [he,h])
        have count : marked f (insert z r) = marked f r + 1 := by
          simp [marked,Finset.filter_insert,zz,Finset.card_insert_of_notMem, zr]
        obtain ⟨j,hr,le⟩ := next av (fun _ h => h) (const_holds zz)
        exact ⟨j,hr,by rw [he]; omega⟩
      · obtain ⟨j,hr,le⟩ := next av (fun _ h => h) (paid_const_fold (hav a ha) (hav b hb) (.inl ha') hop)
        have eq := marked_false f r b hb'
        exact ⟨j,hr,by rw [he]; omega⟩
      · obtain ⟨j,hr,le⟩ := next av (fun _ h => h) (paid_const_fold (hav a ha) (hav b hb) (.inr hb') hop)
        have eq := marked_false f (insert b r) a ha'
        exact ⟨j,hr,by rw [he]; omega⟩
      · have ea := marked_false f (insert b r) a ha'
        have eb := marked_false f r b hb'
        rcases mem_ops_reach (hav a ha) (hav b hb) hop with known|⟨u,hu,v,hv,hne,q,hq,ok⟩
        · obtain ⟨j,hr,le⟩ := next av (fun _ h => h) known
          exact ⟨j,hr,by rw [he]; omega⟩
        · obtain ⟨j,hr,le⟩ := next (insert q av) (Finset.subset_insert ..) ok
          exact ⟨j+1,sb_step hu hv hne hq hr,by rw [he]; omega⟩

def creditConst (p : CreditRow) (w : W) : Bool := w &&& p.mask == 0 || w &&& p.mask == p.mask

def creditKnown (p : CreditRow) (w : W) : Bool := creditConst p w || p.refs.contains (w &&& p.mask)

def pruneRow (p : CreditRow) (k : ℕ) (ws : List W) : Bool :=
  p.cost != 0 && decide (k < p.cost + (ws.filter (creditConst p)).length) && ws.all (creditKnown p)

theorem pruneRow_sound (p : CreditRow) (hp : CreditSound p) {t : W} (ht : t = goal ∨ t = ~~~goal)
    {k : ℕ} {ws : List W} (nd : ws.Nodup) (hl : live basicOps t k ws.toFinset) : pruneRow p k ws = false := by
  by_contra bad
  have yes : pruneRow p k ws = true := by cases h : pruneRow p k ws <;> simp_all
  obtain ⟨f,av,hm,con,ref,lower⟩ := hp
  simp only [pruneRow,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq,List.all_eq_true] at yes
  have constant (w : W) (h : creditConst p w = true) := con w (by simpa [creditConst] using h)
  have known (w : W) (hw : w ∈ ws.toFinset) : holds av (f w) := by
    have h := yes.2 w (List.mem_toFinset.mp hw)
    simp only [creditKnown, Bool.or_eq_true] at h
    rcases h with hc|hr
    · exact const_holds (constant _ hc)
    · exact ref _ (List.contains_iff_mem.mp hr)
  have nc : ¬ cwire (f t) := by
    intro bad
    have e := lower t ht 0 (sb_zero (const_holds bad))
    omega
  obtain ⟨j,hj,bud⟩ := live_credit hm nc hl known
  have le := lower t ht j hj
  have sub : (ws.filter (creditConst p)).toFinset ⊆ ws.toFinset.filter (fun w => cwire (f w)) := by
    intro w hw
    have h := List.mem_filter.mp (List.mem_toFinset.mp hw)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr h.1, constant w h.2⟩
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup (nd.filter _)] at card
  unfold marked at bud
  omega


def creditOptimized (bank : List CreditRow) : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => !(bank.any (fun p => pruneRow p (k+1) ws)) &&
    ((ws == [goal] || ws == [~~~goal]) ||
      (pairs ws).any (fun (a, b, r) => dispatch extra (creditOptimized bank k) a b r))

theorem creditOptimized_complete (bank : List CreditRow) (ok : ∀ p ∈ bank, CreditSound p) {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    creditOptimized bank n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [creditOptimized, singleton_list hn h]
  | succ k ih =>
    have noPrune : bank.any (fun p => pruneRow p (k + 1) ws) = false :=
      List.any_eq_false.mpr (fun p hp yes => Bool.false_ne_true ((pruneRow_sound p (ok p hp) hg hn h).symm.trans yes))
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rw [creditOptimized, noPrune]
      rcases hg with rfl | rfl <;> simp [singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (creditOptimized bank k) a b r = true := by
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
        apply dispatch_complete (k := k) (extra := extra) (creditOptimized bank k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [creditOptimized, noPrune, Bool.not_false, Bool.true_and, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def credit_search (bank : List CreditRow) (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && creditOptimized bank n (n+1-ws.length) ws

theorem credit_search_complete (bank : List CreditRow) (ok : ∀ p ∈ bank, CreditSound p) {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : credit_search bank n inputs = true := by
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
    by simp [sz, cuts_full hg hl', creditOptimized_complete bank ok hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩



private def bankEntry (mask : W) (cost : ℕ) : CreditRow :=
  (mask, minorInputs.flatMap (fun x => [x &&& mask, (~~~x) &&& mask]), cost)

private def bankRows (p n pc nc : ℕ) (j : Fin 512) : Fin 512 :=
  Fin.ofNat 512 (if j.val < 256 then p >>> (9 * (j.val % pc))
    else n >>> (9 * ((j.val % 256 / pc) % nc)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bankRow_sound (mask : W) (d : ℕ) (r : Fin 512 → Fin 512) (vs : List W)
    (hm : reindex r mask = ~~~0)
    (hg : reindex r goal = goal)
    (hi : ∀ v ∈ minorInputs, holds vs.toFinset (reindex r v))
    (hd : vs.Nodup) (hs : search d vs = false) : CreditSound (bankEntry mask (d+1)) := by
  have masked (w : W) : reindex r (w &&& mask) = reindex r w := by
    rw [reindex_and, hm]
    exact (congrArg (fun v : W => reindex r w &&& v) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  have rz : reindex r 0 = 0 := by
    apply reindex_eq_of_rows
    simp
  refine ⟨reindex r, vs.toFinset, ops_map_of (reindex_and r) (reindex_or r) (reindex_not r), ?_, ?_, ?_⟩
  · intro w h
    change w &&& mask = 0 ∨ w &&& mask = mask at h
    rcases h with e | e
    · exact Or.inl ((masked w).symm.trans ((congrArg (reindex r) e).trans rz))
    · exact Or.inr ((masked w).symm.trans ((congrArg (reindex r) e).trans hm))
  · intro w hw
    change w &&& mask ∈ minorInputs.flatMap (fun v => [v &&& mask, (~~~v) &&& mask]) at hw
    obtain ⟨v,hv,he⟩ := List.mem_flatMap.mp hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with e | e
    · rw [← masked w, e, masked v]; exact hi v hv
    · rw [← masked w, e, masked (~~~v), reindex_not]; exact holds_not (hi v hv)
  · intro t ht k h
    change d + 1 ≤ k
    by_contra! hk
    have hh := sb_le (show k ≤ d by omega) h
    have ht' : reindex r t = goal ∨ reindex r t = ~~~goal := by
      rcases ht with rfl | rfl
      · exact Or.inl hg
      · exact Or.inr (by rw [reindex_not, hg])
    have hneg : ~~~(reindex r t) = goal ∨ ~~~(reindex r t) = ~~~goal := by
      rcases ht' with e | e <;> simp [e]
    rcases hh with he | he | hb | hb
    · rcases ht' with h' | h' <;> rw [h'] at he <;> revert he <;> decide +kernel
    · rcases ht' with h' | h' <;> rw [h'] at he <;> revert he <;> decide +kernel
    · exact Bool.noConfusion (hs.symm.trans (search_complete ht' d vs hd hb))
    · exact Bool.noConfusion (hs.symm.trans (search_complete hneg d vs hd hb))

private def bm0 : W := 0x5004712a81c1930282062c1450508a9b1a00100092040163000c002050221100000004010c040204002101804100160406001000040003000485802040221100
private def br0 := bankRows 0x19078100c 0x844561948 4 4
private def bv0_0 : W := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
private def bv0_2 : W := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
private def bv0_4 : W := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
private def bl0 : List W := [bv0_0, bv0_2, bv0_4]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp0 : CreditSound (bankEntry bm0 4) := by
  apply bankRow_sound bm0 3 br0 bl0
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv0_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv0_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv0_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm1 : W := 0x30051d1068e0d45052589431a600210012449205001891048a002142040800010002004880000900000044108008000010012ba920010c001010614204080000
private def br1 := bankRows 0x300684c13 0x8044e4d48 4 4
private def bv1_1 : W := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
private def bv1_3 : W := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
private def bv1_5 : W := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
private def bl1 : List W := [bv1_1, bv1_3, bv1_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp1 : CreditSound (bankEntry bm1 4) := by
  apply bankRow_sound bm1 3 br1 bl1
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv1_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv1_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv1_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm2 : W := 0xfc5ff56ffdf9bf63cb7fbe1d7ddffabf7eff3e2d9bb6f97bb6fffcaafeebd59f10d88707af1687c68b759b857994de3456653c041574b33b24b5d42af6e3159f
private def br2 := bankRows 0xe2219543a440b004ea040106846001a85c14320f020060c 0x4061f0085422070289c561948 21 11
private def bv2_0 : W := 0xf0000000000000000000000000000000000001fffff00000000003ffffe000007ab5dbd5aedead76f56bb7ab5dbd5aedead76f56bb7ab5dbd5aedead76f56bb7
private def bv2_2 : W := 0x3ffffe0000000000000003ffffe00000000007ffffc0000000000bcd96de6cb6f365b79b2dbcd96de6cb6f365b79b2dbcd96de6cb6f365b79b2db
private def bv2_3 : W := 0xfffff800003fffffffffffffff80000000000000002f1e7178f38bc79c5e3ce2f1e7178f38bc79c5e3ce2f1e7178f38bc79c5e3ce2
private def bv2_4 : W := 0x7ffffc0000000000ffffffffffc0000000000000000000000000000000cfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fc
private def bv2_5 : W := 0x7fffffffffffffff0000000000000000000000000000000000000000000fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00
private def bl2 : List W := [bv2_0, bv2_2, bv2_3, bv2_4, bv2_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp2 : CreditSound (bankEntry bm2 7) := by
  apply bankRow_sound bm2 6 br2 bl2
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv2_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv2_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv2_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv2_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv2_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm3 : W := 0xf2bfdd9cecf6f6deff7ffd3faeffa76d5bccdf1f25fbd1e7de3ffb57ff4e55e7442314d8b1f05dd6771cfc1c8cea8429180debab20f9cd647613fb57bd0e4507
private def br3 := bankRows 0xe7399543a3e148046260010684426001381c0a090203613 0x406010a83422051382c9a1948 21 11
private def bv3_0 : W := 0xf00000000000000000000000000000003ffffe00000fffff800003ffffe00000eab56f55ab7aad5bd56adeab56f55ab7aad5bd56adeab56f55ab7aad5bd56ade
private def bv3_1 : W := 0xfffff8000000000000000ffffffffffc0000000000bcd9b5e6cdaf366d79b36bcd9b5e6cdaf366d79b36bcd9b5e6cdaf366d79b36b
private def bv3_3 : W := 0x1fffff00000000003ffffffffff0000000000000000000003f1e39f8f1cfc78e7e3c73f1e39f8f1cfc78e7e3c73f1e39f8f1cfc78e7e3c73
private def bv3_4 : W := 0x7ffffc00001fffffffffffffffc0000000000000000000000000000000cfe03e7f01f3f80f9fc07cfe03e7f01f3f80f9fc07cfe03e7f01f3f80f9fc07c
private def bv3_5 : W := 0x7fffffffffe000000000000000000000000000000000000000000000000fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80
private def bl3 : List W := [bv3_0, bv3_1, bv3_3, bv3_4, bv3_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp3 : CreditSound (bankEntry bm3 7) := by
  apply bankRow_sound bm3 6 br3 bl3
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv3_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv3_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv3_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv3_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv3_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm4 : W := 0x77b67bfee3ffd39ebedeedf6fbf2bfdf9b66fdf3fecf27f77f4c2f7fd177bb63edf016310d8492ce0beba5a051d037cf0642d1f00ecf03b57f8dae6d50769b63
private def br4 := bankRows 0xf8289102c3e148048e0f118884c001c018641e090200a0c 0x4061f0083422131582c9a1948 21 11
private def bv4_0 : W := 0xf000000000000000000000000000000000000000000fffff800003ffffe00000fab6d7d5b6beadb5f56dafab6d7d5b6beadb5f56dafab6d7d5b6beadb5f56daf
private def bv4_1 : W := 0xfffff800003ffffe00000ffffffffffc0000000000acdb6566db2b36d959b6cacdb6566db2b36d959b6cacdb6566db2b36d959b6ca
private def bv4_2 : W := 0x3ffffe0000000000000003ffffffffff0000000000000000000003f1c79f8e3cfc71e7e38f3f1c79f8e3cfc71e7e38f3f1c79f8e3cfc71e7e38f3
private def bv4_4 : W := 0x7ffffc0000000000ffffffffffc0000000000000000000000000000000cfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fcfe07e7f03f3f81f9fc0fc
private def bv4_5 : W := 0x7fffffffffffffff0000000000000000000000000000000000000000000fff807ffc03ffe01fff00fff807ffc03ffe01fff00fff807ffc03ffe01fff00
private def bl4 : List W := [bv4_0, bv4_1, bv4_2, bv4_4, bv4_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp4 : CreditSound (bankEntry bm4 7) := by
  apply bankRow_sound bm4 6 br4 bl4
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv4_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv4_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv4_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv4_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv4_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm5 : W := 0xff4d3ff37fe9fdf157fa9ff3f714fdbbbef7b3fffa5cffbeebf6b5fe1cbfbabd8037096ac9994b7043e24d13a39c6991bcb53bafea5d0e82ba5261de1c39b2bd
private def br5 := bankRows 0xc51b1d408313000834470788c4426001781a030d84c0a0c 0x43e01038144e131582c9a1948 21 11
private def bv5_0 : W := 0xf000000000000000000000fffff8000000000000000fffff800003ffffe00000baab6dd55b6eaadb7556dbaab6dd55b6eaadb7556dbaab6dd55b6eaadb7556db
private def bv5_1 : W := 0x3ffffe00000ffffffffffc0000000000eccdb7666dbb336dd99b6eccdb7666dbb336dd99b6eccdb7666dbb336dd99b6e
private def bv5_2 : W := 0x7ffffc00001fffff00000000003ffffffffff0000000000000000000003f0e39f871cfc38e7e1c73f0e39f871cfc38e7e1c73f0e39f871cfc38e7e1c73
private def bv5_3 : W := 0x1fffffffffffffffc0000000000000000000000000000000cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07c
private def bv5_5 : W := 0x7fffffffffe000000000000000000000000000000000000000000000000fffc07ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80
private def bl5 : List W := [bv5_0, bv5_1, bv5_2, bv5_3, bv5_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp5 : CreditSound (bankEntry bm5 7) := by
  apply bankRow_sound bm5 6 br5 bl5
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv5_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv5_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv5_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv5_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv5_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm6 : W := 0x3df7ff7ffbffdf7ffaddf6fdffeb7bd6f77ffee5dfbfbf5dbfc96febe7f9ef5b3cce7248d2638909901d54f1b66b3886b34bafe9b5033c4998d86fe2e7d9e850
private def br6 := bankRows 0x10ce61d28858523602180340f131e02e0e030781a13 0x80c3e010a83422071384c564d48 19 12
private def bv6_1 : W := 0xff800000000000000000000000ffffe00000000000000ffffe00003ffff80000edab5db56bb6ad76d5aedab5db56bb6ad76d5aedab5db56bb6ad76d5aedab5db
private def bv6_2 : W := 0x1ffffc0000000000000000003ffff80000fffffffffc000000000b74d96e9b2dd365ba6cb74d96e9b2dd365ba6cb74d96e9b2dd365ba6cb74d96e
private def bv6_3 : W := 0x7ffff0000000003fffffffff000000000000000000039f1e73e3ce7c79cf8f39f1e73e3ce7c79cf8f39f1e73e3ce7c79cf8f39f1e73
private def bv6_4 : W := 0xffffe0000000007fffffffffffffc00000000000000000000000000003e7e07cfc0f9f81f3f03e7e07cfc0f9f81f3f03e7e07cfc0f9f81f3f03e7e07c
private def bv6_5 : W := 0xffffffffffffff8000000000000000000000000000000000000000000c07ff80fff01ffe03ffc07ff80fff01ffe03ffc07ff80fff01ffe03ffc07ff80
private def bl6 : List W := [bv6_1, bv6_2, bv6_3, bv6_4, bv6_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp6 : CreditSound (bankEntry bm6 6) := by
  apply bankRow_sound bm6 5 br6 bl6
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv6_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv6_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv6_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv6_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv6_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm7 : W := 0xdbedffbb9fc7fffff7a77fffd67dcffbff99d3def77ddfefc9bfd3f57fbe7ffc9a0c6d091e463215f42363fe4709975e4f90101cf600df4685ad91b14bae7fe8
private def br7 := bankRows 0x669e06a17270381438030c83c12041781a030d84c0a0c 0x8541a11038144e131582c9a1948 20 12
private def bv7_0 : W := 0xfffff000000000000000fffff00000fffff00000b5dbab5dbab5dbab5dbab5dbab5dbab5dbab5dbab5dbab5dbab5dbab5dbab5db
private def bv7_1 : W := 0xfffff00000000000000000000fffff00000ffffffffff0000000000d96ecd96ecd96ecd96ecd96ecd96ecd96ecd96ecd96ecd96ecd96ecd96ecd96e
private def bv7_2 : W := 0xfffff0000000000ffffffffff000000000000000000001e73f1e73f1e73f1e73f1e73f1e73f1e73f1e73f1e73f1e73f1e73f1e73f1e73
private def bv7_3 : W := 0xfffff0000000000fffffffffffffff000000000000000000000000000000e07cfe07cfe07cfe07cfe07cfe07cfe07cfe07cfe07cfe07cfe07cfe07cfe07c
private def bv7_4 : W := 0xfffffffffffffff000000000000000000000000000000000000000000000ff80fff80fff80fff80fff80fff80fff80fff80fff80fff80fff80fff80fff80
private def bl7 : List W := [bv7_0, bv7_1, bv7_2, bv7_3, bv7_4]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp7 : CreditSound (bankEntry bm7 6) := by
  apply bankRow_sound bm7 5 br7 bl7
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv7_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv7_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv7_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv7_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv7_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inl (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm8 : W := 0xc20800800400208005220902001484290880011a204040a240369014180610a4c3318db72d9c76f66fe2ab0e4994c7794cb450164afcc3b66727901d182617af
private def br8 := bankRows 0x7139caaf8220f802c53a8c404471188800cd1a938143819048105e0186c0a0c 0x40a0b0c 28 3
private def bv8_1 : W := 0xfffffff00000000000000fffffff00000000000000fffffff00000006555555655555565555556555555655555565555556555555655555565555556
private def bv8_2 : W := 0xb999999b999999b999999b999999b999999b999999b999999b999999b999999b
private def bv8_3 : W := 0xfffffff00000000000000fffffff00000000000000fffffff00000000000000ce1e1e1ce1e1e1ce1e1e1ce1e1e1ce1e1e1ce1e1e1ce1e1e1ce1e1e1ce1e1e1c
private def bv8_4 : W := 0xfe01fe0fe01fe0fe01fe0fe01fe0fe01fe0fe01fe0fe01fe0fe01fe0fe01fe0
private def bv8_5 : W := 0xfffe000fffe000fffe000fffe000fffe000fffe000fffe000fffe000fffe000
private def bl8 : List W := [bv8_1, bv8_2, bv8_3, bv8_4, bv8_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp8 : CreditSound (bankEntry bm8 4) := by
  apply bankRow_sound bm8 3 br8 bl8
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inl (reindex_eq_of_rows _ _ _ (by decide +kernel)))
    · exact kept_eq (v := bv8_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv8_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv8_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv8_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv8_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm9 : W := 0x3a00a900206409c348041e2822005408100c1d2644906844900035501142a60ef2778f850e97839748a647a866b21cba99ac3fbea8b4cc4db4a2bd5091cea60
private def br9 := bankRows 0x1ce737c1447c29628d862602383c4426669e09c0e1c018245e0686c2605 0x834260b26 26 4
private def bv9_0 : W := 0xfffffc0000000000000000000ffffffc0000000000000000000ffffffc000000aaaad6aaaab5aaaaad6aaaab5aaaaad6aaaab5aaaaad6aaaab5aaaaad6aaaab5
private def bv9_2 : W := 0x3ffffff00000000000000000003ffffff0000000000000333364ccccd93333364ccccd93333364ccccd93333364ccccd93333364ccccd9
private def bv9_3 : W := 0x3c3c7b0f0f1ec3c3c7b0f0f1ec3c3c7b0f0f1ec3c3c7b0f0f1ec3c3c7b0f0f1e
private def bv9_4 : W := 0xffffffc0000000000000000000ffffffc0000000000000000000c03f83f00fe0fc03f83f00fe0fc03f83f00fe0fc03f83f00fe0fc03f83f00fe0
private def bv9_5 : W := 0xffc003fff000fffc003fff000fffc003fff000fffc003fff000fffc003fff000
private def bl9 : List W := [bv9_0, bv9_2, bv9_3, bv9_4, bv9_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp9 : CreditSound (bankEntry bm9 6) := by
  apply bankRow_sound bm9 5 br9 bl9
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv9_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inr (.inl (reindex_eq_of_rows _ _ _ (by decide +kernel)))
    · exact kept_eq (v := bv9_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv9_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv9_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv9_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm10 : W := 0xd40226313090921008002c051005892a43320e0da042e1821c004a800b1aa18bbdceb274e0fa22988e303e373157bd6e7f21454df06329b89ec04a842f1baf8
private def br10 := bankRows 0x1c4437c1448816628d8ea042383c46cd3c0d42e38030c83c5e0680c0a0c 0x87c0e1315 26 4
private def bv10_0 : W := 0xaad55eaab557aaad55eaab557aaad55eaab557aaad55eaab557aaad55eaab557
private def bv10_1 : W := 0xfffffc0000000000000000000ffffffc0000000000000000000ffffffc000000336668ccd99a3336668ccd99a3336668ccd99a3336668ccd99a3336668ccd99a
private def bv10_3 : W := 0x3ffffff00000000000000000003ffffff00000000000003c78730f1e1cc3c78730f1e1cc3c78730f1e1cc3c78730f1e1cc3c78730f1e1c
private def bv10_4 : W := 0xc07f83f01fe0fc07f83f01fe0fc07f83f01fe0fc07f83f01fe0fc07f83f01fe0
private def bv10_5 : W := 0xffffffc0000000000000000000ffffffc0000000000000000000ff8003ffe000fff8003ffe000fff8003ffe000fff8003ffe000fff8003ffe000
private def bl10 : List W := [bv10_0, bv10_1, bv10_3, bv10_4, bv10_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp10 : CreditSound (bankEntry bm10 6) := by
  apply bankRow_sound bm10 5 br10 bl10
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv10_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv10_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inr (.inl (reindex_eq_of_rows _ _ _ (by decide +kernel)))
    · exact kept_eq (v := bv10_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv10_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv10_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm11 : W := 0x884984011c002c6141211209040d40206499020c0130d80880b3d0802e88449c120fe9cef27b6d31f4145a5fae2fc830f9bd2e0ff130fc4a80725192af89649c
private def br11 := bankRows 0x1c443739ccaa1d628d8ea0418980041a669e06a1727038145e0680c3613 0x8540e0513 26 4
private def bv11_0 : W := 0xfffffc0000000000000000000ffffffc0000000000000000000ffffffc000000aaaadaaaaab6aaaaadaaaaab6aaaaadaaaaab6aaaaadaaaaab6aaaaadaaaaab6
private def bv11_1 : W := 0x33336cccccdb333336cccccdb333336cccccdb333336cccccdb333336cccccdb
private def bv11_2 : W := 0x3ffffff00000000000000000003ffffff00000000000003c3c730f0f1cc3c3c730f0f1cc3c3c730f0f1cc3c3c730f0f1cc3c3c730f0f1c
private def bv11_4 : W := 0xffffffc0000000000000000000ffffffc0000000000000000000c03f83f00fe0fc03f83f00fe0fc03f83f00fe0fc03f83f00fe0fc03f83f00fe0
private def bv11_5 : W := 0xffc003fff000fffc003fff000fffc003fff000fffc003fff000fffc003fff000
private def bl11 : List W := [bv11_0, bv11_1, bv11_2, bv11_4, bv11_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp11 : CreditSound (bankEntry bm11 6) := by
  apply bankRow_sound bm11 5 br11 bl11
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv11_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv11_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv11_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inr (.inl (reindex_eq_of_rows _ _ _ (by decide +kernel)))
    · exact kept_eq (v := bv11_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv11_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm12 : W := 0xb2c00c8016020ea805600c08eb024441084c0005a3004114094a01e34045427fc8f6953666b48fbc1db2ec5c63966e434ac45015a2f17d45ad9e21e3c64d42
private def br12 := bankRows 0x1c443739ccaa1d7c14488161f0a402cd3c0d42e4e070287006190782408 0x80c2a0d08 26 4
private def bv12_0 : W := 0xaad5aeaab56baaad5aeaab56baaad5aeaab56baaad5aeaab56baaad5aeaab56b
private def bv12_1 : W := 0xfffffc0000000000000000000ffffffc0000000000000000000ffffffc0000003366c8ccd9b233366c8ccd9b233366c8ccd9b233366c8ccd9b233366c8ccd9b2
private def bv12_2 : W := 0x3c78f30f1e3cc3c78f30f1e3cc3c78f30f1e3cc3c78f30f1e3cc3c78f30f1e3c
private def bv12_3 : W := 0x3ffffff00000000000000000003ffffff0000000000000c07f03f01fc0fc07f03f01fc0fc07f03f01fc0fc07f03f01fc0fc07f03f01fc0
private def bv12_5 : W := 0xffffffc0000000000000000000ffffffc0000000000000000000ff8003ffe000fff8003ffe000fff8003ffe000fff8003ffe000fff8003ffe000
private def bl12 : List W := [bv12_0, bv12_1, bv12_2, bv12_3, bv12_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp12 : CreditSound (bankEntry bm12 6) := by
  apply bankRow_sound bm12 5 br12 bl12
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv12_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv12_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv12_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv12_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inr (.inl (reindex_eq_of_rows _ _ _ (by decide +kernel)))
    · exact kept_eq (v := bv12_5) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
  · decide +kernel
  · decide +kernel

private def bm13 : W := 0x2412004460380000085880002982300400662c210882201036402c0a8041800365f392f6e1b9cdea0bdc9c01b8f668a1b06fefe309ff20b97a526e4eb4518017
private def br13 := bankRows 0x38886e7399543af8289102c3e148058a363a8106260010688e0f118884c00 0x4061f00 27 3
private def bv13_0 : W := 0x556d556aadaaad55b555aab6aab556d556aadaaad55b555aab6aab556d556aad
private def bv13_1 : W := 0x99b199b336333666c666ccd8ccd99b199b336333666c666ccd8ccd99b199b336
private def bv13_2 : W := 0xffffffe00000000000007ffffff00000000000003ffffff8000000e1c61e3c38c3c7871878f0e30f1e1c61e3c38c3c7871878f0e30f1e1c61e3c38
private def bv13_3 : W := 0xfe07e03fc0fc07f81f80ff03f01fe07e03fc0fc07f81f80ff03f01fe07e03fc0
private def bv13_4 : W := 0x7ffffff00000000000003ffffff80000000000001ffffffc00000000000000007ffc000fff8001fff0003ffe0007ffc000fff8001fff0003ffe0007ffc000
private def bl13 : List W := [bv13_0, bv13_1, bv13_2, bv13_3, bv13_4]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem bp13 : CreditSound (bankEntry bm13 4) := by
  apply bankRow_sound bm13 3 br13 bl13
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · exact reindex_eq_of_rows _ _ _ (by decide +kernel)
  · intro w hw
    simp only [minorInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact kept_eq (v := bv13_0) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv13_1) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv13_2) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv13_3) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact kept_eq (v := bv13_4) (by decide +kernel) (reindex_eq_of_rows _ _ _ (by decide +kernel))
    · exact .inr (.inl (reindex_eq_of_rows _ _ _ (by decide +kernel)))
  · decide +kernel
  · decide +kernel

def bank : List CreditRow := [bankEntry bm0 4, bankEntry bm1 4, bankEntry bm2 7, bankEntry bm3 7, bankEntry bm4 7, bankEntry bm5 7, bankEntry bm6 6, bankEntry bm7 6, bankEntry bm8 4, bankEntry bm9 6, bankEntry bm10 6, bankEntry bm11 6, bankEntry bm12 6, bankEntry bm13 4]

theorem bank_sound : ∀ p ∈ bank, CreditSound p := by
  simp only [bank, List.forall_mem_cons]
  exact ⟨bp0, bp1, bp2, bp3, bp4, bp5, bp6, bp7, bp8, bp9, bp10, bp11, bp12, bp13, by simp⟩


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject01 : dispatch 4 (creditOptimized bank 8) m0 m1 [m2, m3, m4, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject02 : dispatch 4 (creditOptimized bank 8) m0 m2 [m1, m3, m4, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject03 : dispatch 4 (creditOptimized bank 8) m0 m3 [m1, m2, m4, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject04 : dispatch 4 (creditOptimized bank 8) m0 m4 [m1, m2, m3, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject05 : dispatch 4 (creditOptimized bank 8) m0 m5 [m1, m2, m3, m4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject12 : dispatch 4 (creditOptimized bank 8) m1 m2 [m0, m3, m4, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject13 : dispatch 4 (creditOptimized bank 8) m1 m3 [m0, m2, m4, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject14 : dispatch 4 (creditOptimized bank 8) m1 m4 [m0, m2, m3, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject15 : dispatch 4 (creditOptimized bank 8) m1 m5 [m0, m2, m3, m4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject23 : dispatch 4 (creditOptimized bank 8) m2 m3 [m0, m1, m4, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject24 : dispatch 4 (creditOptimized bank 8) m2 m4 [m0, m1, m3, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject25 : dispatch 4 (creditOptimized bank 8) m2 m5 [m0, m1, m3, m4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject34 : dispatch 4 (creditOptimized bank 8) m3 m4 [m0, m1, m2, m5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject35 : dispatch 4 (creditOptimized bank 8) m3 m5 [m0, m1, m2, m4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem minor_reject45 : dispatch 4 (creditOptimized bank 8) m4 m5 [m0, m1, m2, m3] = false := by decide +kernel

theorem minor_split : pairs minorInputs = [(m0, m1, [m2, m3, m4, m5]), (m0, m2, [m1, m3, m4, m5]), (m0, m3, [m1, m2, m4, m5]), (m0, m4, [m1, m2, m3, m5]), (m0, m5, [m1, m2, m3, m4]), (m1, m2, [m0, m3, m4, m5]), (m1, m3, [m0, m2, m4, m5]), (m1, m4, [m0, m2, m3, m5]), (m1, m5, [m0, m2, m3, m4]), (m2, m3, [m0, m1, m4, m5]), (m2, m4, [m0, m1, m3, m5]), (m2, m5, [m0, m1, m3, m4]), (m3, m4, [m0, m1, m2, m5]), (m3, m5, [m0, m1, m2, m4]), (m4, m5, [m0, m1, m2, m3])] := rfl

set_option maxRecDepth 16000 in
theorem minor_no_run : creditOptimized bank 9 4 minorInputs = false := by
  rw [creditOptimized]
  apply Bool.and_eq_false_iff.mpr
  right
  rw [minor_split]
  simp only [List.any_cons, List.any_nil, minor_reject01, minor_reject02, minor_reject03, minor_reject04, minor_reject05, minor_reject12, minor_reject13, minor_reject14, minor_reject15, minor_reject23, minor_reject24, minor_reject25, minor_reject34, minor_reject35, minor_reject45, Bool.or_false]
  decide +kernel

theorem minor_impossible (t : W) (ht : t = goal ∨ t = ~~~goal) (hb : build basicOps t 9 minorInputs.toFinset) : False := by
  have accept := credit_search_complete bank bank_sound ht 9 minorInputs (by decide +kernel) hb
  obtain ⟨l, hl, good⟩ := List.any_eq_true.mp accept
  simp only [Bool.and_eq_true, beq_iff_eq] at good
  have need := List.all_eq_true.mp minor_all_needed l hl
  have eq : l = minorInputs := by simpa [good.1.2] using need
  subst l
  exact Bool.false_ne_true (minor_no_run.symm.trans good.2)


end PEqualNP.Outside.L_meta_14798

theorem PEqualNP.Outside.L_meta_14798 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hg _ he
  exact PEqualNP.Outside.L_meta_14798.solve PEqualNP.Outside.L_meta_14798.minor_impossible gs o hg he
