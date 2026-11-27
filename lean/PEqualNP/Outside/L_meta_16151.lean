import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16151

namespace Signed

-- Signed live-wire search adapted from L-meta-9146 and L-meta-8633.
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

abbrev W := BitVec 196

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 66 := ((x >>> 66) ^^^ x).setWidth 66
def cuts (ws : List W) : BitVec 66 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (1519143913070204415 : BitVec 64) ++
  ((-1 : BitVec 66) ++ (0 : BitVec 66))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def differs (i : Fin 66) (w : W) : Prop :=
  w.getLsbD (66+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 66) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 66+i.val < 196 := by omega
  have hi' : i.val < 196 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 66) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 66)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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
    !((a :: b :: r).contains w) && (((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hnew : z ∉ a :: b :: r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simp [hnew], ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
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
        have absent : z ∉ a :: b :: r := fun hz =>
          hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))
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
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk absent (by omega) (by omega) (cuts_full hg hl)
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 196 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 196)
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

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 196) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 196) :
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

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 196) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0 : W)[k.val] = false; simp
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

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def F (x : Fin 6 → Bool) : Bool := (16927600160639347200 : ℕ).testBit (∑ i : Fin 6, if x i then 2 ^ i.val else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : ∀ g, (g = goal ∨ g = ~~~goal) → build basicOps g 7 inputs.toFinset → False)
    (sample : ∀ k : Fin 196, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 196) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact reject t ht (lift low run)

def rows : List W :=
  [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def maskN : Nat := 73786976294838206463

def sepN (w : Nat) : Nat := (w >>> 66) % 73786976294838206464 ^^^ w % 73786976294838206464

def cutsN (ws : List Nat) : Nat := ws.foldr (fun w acc => sepN w ||| acc) 0

def opsN (a b : Nat) : List Nat :=
  [a &&& b, a ||| b, a &&& (100433627766186892221372630771322662657637687111424552206335 - b), b &&& (100433627766186892221372630771322662657637687111424552206335 - a)]

def dispatchN (extra : Nat) (next : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  let base := cutsN r
  (opsN a b).any fun w =>
    let v := sepN w ||| base
    !((a :: b :: r).contains w) && (((v == maskN) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepN a == maskN) && next (extra - 1) (w :: a :: r)) ||
                      ((v ||| sepN b == maskN) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepN a ||| sepN b == maskN) && next (extra - 2) (w :: a :: b :: r)))

def reachedN (ws : List Nat) : Bool :=
  ws == [goal.toNat] || ws == [(~~~goal).toNat]

def optimizeN : Nat → Nat → List Nat → Bool
  | 0, _, ws => reachedN ws
  | k + 1, extra, ws => reachedN ws ||
    (pairs ws).any (fun (a, b, r) => dispatchN extra (optimizeN k) a b r)

def searchN (n : Nat) (inputs : List Nat) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsN ws == maskN) && optimizeN n (n + 1 - ws.length) ws

lemma singleMap (f : W → Nat) (xs : List W) :
    singles (xs.map f) = (singles xs).map (fun (a, r) => (f a, r.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [singles, ih, List.map_map, Function.comp_def]

lemma pairMap (f : W → Nat) (xs : List W) :
    pairs (xs.map f) = (pairs xs).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairs, singleMap, ih, List.map_map, Function.comp_def]

lemma maskMap : maskN = (-1 : BitVec 66).toNat := by decide

lemma sepMap (w : W) : sepN w.toNat = (sep w).toNat := by
  simp [sepN, sep, BitVec.toNat_setWidth]

lemma cutsMap (ws : List W) : cutsN (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change sepN w.toNat ||| cutsN (ws.map BitVec.toNat) = (sep w ||| cuts ws).toNat
    rw [sepMap, ih, BitVec.toNat_or]

lemma opsMap (a b : W) : (ops a b).map BitVec.toNat = opsN a.toNat b.toNat := by
  simp [ops, opsN]

lemma equalBits {n : Nat} (a b : BitVec n) : (a.toNat == b.toNat) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.toNat_inj]

lemma containsMap (ws : List W) (w : W) :
    (ws.map BitVec.toNat).contains w.toNat = ws.contains w := by
  apply Bool.eq_iff_iff.mpr
  simp [List.contains_iff_mem, List.mem_map, BitVec.toNat_inj]

lemma reachedMap (ws : List W) : reachedN (ws.map BitVec.toNat) = (ws == [goal] || ws == [~~~goal]) := by
  have same (w : W) : (ws.map BitVec.toNat == [w.toNat]) = (ws == [w]) := by
    change (ws.map BitVec.toNat == ([w] : List W).map BitVec.toNat) = _
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact List.map_inj_right (fun _ _ h => BitVec.toNat_inj.mp h)
  simp only [reachedN, same]

lemma dispatchMap (extra : Nat) (nextN : Nat → List Nat → Bool) (next : Nat → List W → Bool)
    (agree : ∀ e ws, nextN e (ws.map BitVec.toNat) = next e ws) (a b : W) (r : List W) :
    dispatchN extra nextN a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra next a b r := by
  simp only [dispatchN, dispatch, ← opsMap, List.any_map]
  apply List.any_congr rfl
  intro w
  simpa only [Function.comp_apply, sepMap, cutsMap, ← BitVec.toNat_or, maskMap, equalBits,
    ← List.map_cons, containsMap, agree]

lemma optimizeMap (depth extra : Nat) (ws : List W) :
    optimizeN depth extra (ws.map BitVec.toNat) = optimized depth extra ws := by
  induction depth generalizing extra ws with
  | zero => exact reachedMap ws
  | succ n ih =>
    simp only [optimizeN, optimized, reachedMap, pairMap, List.any_map]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a, b, r⟩
    exact dispatchMap extra (optimizeN n) (optimized n) ih a b r

lemma searchMap (n : Nat) (ws : List W) :
    searchN n (ws.map BitVec.toNat) = search n ws := by
  simp only [searchN, search, List.sublists_map, List.any_map]
  apply List.any_congr rfl
  intro a
  simp only [Function.comp_apply, List.length_map, cutsMap, maskMap, equalBits, optimizeMap]

def lastN (a b : Nat) (r : List Nat) : Bool :=
  if r.isEmpty then (opsN a b).any fun w =>
    !([a, b].contains w) && reachedN [w]
  else false

lemma reachedCuts (w : Nat) (h : reachedN [w] = true) : (sepN w == maskN) = true := by
  have hits : w = goal.toNat ∨ w = (~~~goal).toNat := by simpa [reachedN] using h
  obtain rfl | rfl := hits <;> decide

lemma lastEq (e a b : Nat) (r : List Nat) :
    lastN a b r = dispatchN e (fun _ => reachedN) a b r := by
  cases r with
  | nil =>
    simp only [lastN, List.isEmpty_nil, if_true, dispatchN, cutsN, List.foldr_nil, Nat.or_zero]
    apply List.any_congr rfl
    intro w
    have two (x : Nat) : reachedN [w, x] = false := by simp [reachedN]
    have three : reachedN [w, a, b] = false := by simp [reachedN]
    simp only [two, three, Bool.and_false, Bool.or_false]
    cases h : reachedN [w] with
    | false => simp [h]
    | true => simp [h, reachedCuts w h]
  | cons x xs => simp [lastN, dispatchN, reachedN]

def directN : Nat → Nat → List Nat → Bool
  | 0, _, ws => reachedN ws
  | 1, _, ws => reachedN ws || (pairs ws).any (fun (a, b, r) => lastN a b r)
  | k + 2, extra, ws => reachedN ws ||
    (pairs ws).any (fun (a, b, r) => dispatchN extra (directN (k + 1)) a b r)

lemma directEq (n : Nat) : directN n = optimizeN n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext e ws
    cases n with
    | zero =>
      simp only [directN, optimizeN]
      congr 1
      apply List.any_congr rfl
      rintro ⟨a, b, r⟩
      exact lastEq e a b r
    | succ n => simp only [directN, optimizeN, ih]

def relabel (f : Fin 196 → Fin 196) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => w.getLsbD (f i).val))).cast List.length_ofFn

lemma relabelBit (f : Fin 196 → Fin 196) (w : W) (i : Fin 196) :
    (relabel f w).getLsbD i.val = w.getLsbD (f i).val := by
  simp only [relabel, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dif_pos, Option.getD_some]

lemma relabelInj (f : Fin 196 → Fin 196) (hf : Function.Surjective f) :
    Function.Injective (relabel f) := by
  intro a b e
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨j, hj⟩ := hf ⟨i, hi⟩
  have h := congrArg (fun w : W => w.getLsbD j.val) e
  simpa only [relabelBit, hj, BitVec.getLsbD_eq_getElem hi] using h

lemma relabelAnd (f : Fin 196 → Fin 196) (x y : W) :
    relabel f (x &&& y) = relabel f x &&& relabel f y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_and, relabelBit f _ ⟨i, hi⟩]

lemma relabelOr (f : Fin 196 → Fin 196) (x y : W) :
    relabel f (x ||| y) = relabel f x ||| relabel f y := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_or, relabelBit f _ ⟨i, hi⟩]

lemma relabelNot (f : Fin 196 → Fin 196) (x : W) :
    relabel f (~~~x) = ~~~relabel f x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [← BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_not, relabelBit f _ ⟨i, hi⟩,
    hi, (f ⟨i, hi⟩).isLt, decide_true, Bool.true_and]

lemma relabelOp (f : Fin 196 → Fin 196) {a b z : W} (h : z ∈ basicOps a b) :
    relabel f z ∈ basicOps (relabel f a) (relabel f b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp only [relabelAnd, relabelOr, relabelNot] <;> tauto

set_option maxRecDepth 10000 in
lemma relabelLive (f : Fin 196 → Fin 196) (hf : Function.Surjective f) {g : W}
    {n : Nat} {ws : Finset W} (h : live basicOps g n ws) :
    live basicOps (relabel f g) n (ws.image (relabel f)) := by
  induction n generalizing ws with
  | zero =>
    change ws = {g} at h
    subst ws
    simp [live]
  | succ n ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, fresh, rest, rfl, tail⟩
    · exact .inl (ih skip)
    · let T := relabel f
      refine .inr ⟨T a, Finset.mem_image_of_mem _ ha, T b, Finset.mem_image_of_mem _ hb,
        fun e => hab (relabelInj f hf e), T z, relabelOp f hz, ?_, rest.image T, ?_, ?_⟩
      · intro hz
        obtain ⟨y, hy, e⟩ := Finset.mem_image.mp hz
        exact fresh (relabelInj f hf e ▸ hy)
      · simp [T, Finset.image_insert]
      · simpa only [Finset.image_insert] using ih tail

set_option maxRecDepth 10000 in
lemma necessaryStep {g a b z : W} {r : List W} {needed : Finset W}
    (k : Nat) (hg : g = goal ∨ g = ~~~goal) (perm : rows.Perm (a :: b :: r))
    (hset : rows.toFinset = insert a (insert b needed)) (hz : z ∈ basicOps a b)
    (fresh : z ∉ rows.toFinset) (hrun : live basicOps g k (insert z needed)) :
    dispatch (k + 2 - rows.length) (optimized k) a b r = true := by
  have nd : rows.Nodup := by decide
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm nd hset
  have hznew : z ∉ kept := by
    intro hu
    apply fresh
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
  have hnd := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using hrun
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have len := perm.length_eq
  simp only [List.length_cons] at len
  have room : rows.length ≤ k + 2 := by
    have aux : (a :: b :: r).length ≤ kept.length + 2 := by
      simp [keepChoices] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp
    simp only [List.length_cons] at aux
    omega
  have missing : z ∉ a :: b :: r := fun hm => fresh (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
  apply dispatch_complete (k := k) (optimized k) hz hk missing (by omega) (by omega) (cuts_full hg hl)
  exact optimized_complete hg k (z :: kept) (k - kept.length) hnd (by simp; omega) hl

set_option maxRecDepth 10000 in
lemma moveStep {g a b z x y : W} {r : List W} {needed : Finset W}
    (k : Nat) (f : Fin 196 → Fin 196) (hf : Function.Surjective f)
    (hrows : rows.toFinset.image (relabel f) = rows.toFinset)
    (hg : g = goal ∨ g = ~~~goal) (fixed : relabel f goal = goal)
    (hset : rows.toFinset = insert a (insert b needed)) (hz : z ∈ basicOps a b)
    (fresh : z ∉ rows.toFinset) (hrun : live basicOps g k (insert z needed))
    (perm : rows.Perm (x :: y :: r))
    (order : (relabel f a = x ∧ relabel f b = y) ∨ (relabel f a = y ∧ relabel f b = x)) :
    dispatch (k + 2 - rows.length) (optimized k) x y r = true := by
  let T := relabel f
  have image : rows.toFinset = insert (T a) (insert (T b) (needed.image T)) := by
    calc
      rows.toFinset = rows.toFinset.image T := hrows.symm
      _ = _ := by rw [hset, Finset.image_insert, Finset.image_insert]
  have rg : T g = goal ∨ T g = ~~~goal := by
    rcases hg with rfl | rfl
    · exact .inl fixed
    · exact .inr (by simp only [T, relabelNot, fixed])
  have absent : T z ∉ rows.toFinset := by
    rw [← hrows]
    intro hm
    obtain ⟨v, hv, e⟩ := Finset.mem_image.mp hm
    exact fresh (relabelInj f hf e ▸ hv)
  have tail := relabelLive f hf hrun
  rw [Finset.image_insert] at tail
  have op := relabelOp f hz
  dsimp only [T] at image
  rcases order with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [hx, hy] at image op
    exact necessaryStep k rg perm image op absent tail
  · rw [hy, hx, Finset.insert_comm] at image
    rw [hy, hx, ops_swap] at op
    exact necessaryStep k rg perm image op absent tail

def perm1 (i : Fin 196) : Fin 196 := Fin.ofNat 196 (([0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 13, 14, 15, 10, 11, 12, 16, 17, 19, 18, 21, 20, 23, 22, 25, 24, 26, 28, 27, 29, 30, 31, 33, 32, 34, 37, 38, 35, 36, 44, 45, 46, 47, 48, 39, 40, 41, 42, 43, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 58, 60, 62, 61, 63, 65, 64, 66, 67, 69, 68, 70, 72, 71, 73, 74, 75, 79, 80, 81, 76, 77, 78, 82, 83, 85, 84, 87, 86, 89, 88, 91, 90, 92, 94, 93, 95, 96, 97, 99, 98, 100, 103, 104, 101, 102, 110, 111, 112, 113, 114, 105, 106, 107, 108, 109, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 124, 126, 128, 127, 129, 131, 130, 132, 133, 136, 137, 134, 135, 138, 139, 140, 141, 144, 145, 142, 143, 146, 147, 148, 149, 152, 153, 150, 151, 154, 155, 156, 157, 160, 161, 158, 159, 162, 163, 164, 165, 168, 169, 166, 167, 170, 171, 172, 173, 176, 177, 174, 175, 178, 179, 180, 181, 184, 185, 182, 183, 186, 187, 188, 189, 192, 193, 190, 191, 194, 195] : List Nat).getD i.val 0)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma onto1 : Function.Surjective perm1 := by
  let rev (i : Fin 196) : Fin 196 := Fin.ofNat 196 (([0, 1, 3, 2, 4, 6, 5, 7, 8, 9, 13, 14, 15, 10, 11, 12, 16, 17, 19, 18, 21, 20, 23, 22, 25, 24, 26, 28, 27, 29, 30, 31, 33, 32, 34, 37, 38, 35, 36, 44, 45, 46, 47, 48, 39, 40, 41, 42, 43, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 58, 60, 62, 61, 63, 65, 64, 66, 67, 69, 68, 70, 72, 71, 73, 74, 75, 79, 80, 81, 76, 77, 78, 82, 83, 85, 84, 87, 86, 89, 88, 91, 90, 92, 94, 93, 95, 96, 97, 99, 98, 100, 103, 104, 101, 102, 110, 111, 112, 113, 114, 105, 106, 107, 108, 109, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 124, 126, 128, 127, 129, 131, 130, 132, 133, 136, 137, 134, 135, 138, 139, 140, 141, 144, 145, 142, 143, 146, 147, 148, 149, 152, 153, 150, 151, 154, 155, 156, 157, 160, 161, 158, 159, 162, 163, 164, 165, 168, 169, 166, 167, 170, 171, 172, 173, 176, 177, 174, 175, 178, 179, 180, 181, 184, 185, 182, 183, 186, 187, 188, 189, 192, 193, 190, 191, 194, 195] : List Nat).getD i.val 0)
  have h : ∀ i, perm1 (rev i) = i := by decide +kernel
  exact fun i => ⟨rev i, h i⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma fixed1 : relabel perm1 goal = goal := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rows1 : rows.toFinset.image (relabel perm1) = rows.toFinset := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck0 : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 80346902212949513774380889341042273384136713836437180455936 [94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck2 : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 100042835440248421822964740738255728582036747612376839225343 [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck3 : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 100432095294029695723237014575624475064859198628788546043904 [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck4 : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 100433627742802866029454694220141837846815249600006693322752 [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck5 : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 94525767309352369147593894796790183817692878148717022011392 [66955751844124594810692406889727347695696810027520350027775, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck6 : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100042835440248421822964740738255728582036747612376839225343 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck7 : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100432095294029695723237014575624475064859198628788546043904 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck8 : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck12 : dispatch 2 (optimized 6) 100042835440248421822964740738255728582036747612376839225343 100432095294029695723237014575624475064859198628788546043904 [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100433627742802866029454694220141837846815249600006693322752] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck13 : dispatch 2 (optimized 6) 100042835440248421822964740738255728582036747612376839225343 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma orbitCheck14 : dispatch 2 (optimized 6) 100432095294029695723237014575624475064859198628788546043904 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343] = false := by
  rw [← dispatchMap 2 (optimizeN 6) (optimized 6) (optimizeMap 6)]
  rw [← directEq]
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma excludesPair {g a b z : W} {r : List W} {needed : Finset W}
    (pol : g = goal ∨ g = ~~~goal) (which : (a, b, r) ∈ pairs rows)
    (hset : rows.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
    (fresh : z ∉ rows.toFinset) (tail : live basicOps g 6 (insert z needed)) : False := by
  have actual : pairs rows =
    [(66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, [94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]),
     (66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, [80346902212949513774380889341042273384136713836437180455936, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]),
     (66955751844124594810692406889727347695696810027520350027775, 100042835440248421822964740738255728582036747612376839225343, [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]),
     (66955751844124594810692406889727347695696810027520350027775, 100432095294029695723237014575624475064859198628788546043904, [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752]),
     (66955751844124594810692406889727347695696810027520350027775, 100433627742802866029454694220141837846815249600006693322752, [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904]),
     (80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, [66955751844124594810692406889727347695696810027520350027775, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]),
     (80346902212949513774380889341042273384136713836437180455936, 100042835440248421822964740738255728582036747612376839225343, [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]),
     (80346902212949513774380889341042273384136713836437180455936, 100432095294029695723237014575624475064859198628788546043904, [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752]),
     (80346902212949513774380889341042273384136713836437180455936, 100433627742802866029454694220141837846815249600006693322752, [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904]),
     (94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752]),
     (94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752]),
     (94525767309352369147593894796790183817692878148717022011392, 100433627742802866029454694220141837846815249600006693322752, [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904]),
     (100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100433627742802866029454694220141837846815249600006693322752]),
     (100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752, [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904]),
     (100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752, [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343])] := by decide
  rw [actual] at which
  simp only [List.mem_cons, List.not_mem_nil, or_false] at which
  rcases which with which | which | which | which | which | which | which | which | which | which | which | which | which | which | which
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 80346902212949513774380889341042273384136713836437180455936 [94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck0.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 80346902212949513774380889341042273384136713836437180455936 [94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = true :=
      moveStep 6 perm1 onto1 rows1 pol fixed1
        hset hop fresh tail (by decide) (Or.inl ⟨by decide +kernel, by decide +kernel⟩)
    exact Bool.noConfusion (orbitCheck0.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 100042835440248421822964740738255728582036747612376839225343 [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck2.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 100432095294029695723237014575624475064859198628788546043904 [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck3.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 66955751844124594810692406889727347695696810027520350027775 100433627742802866029454694220141837846815249600006693322752 [80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck4.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 94525767309352369147593894796790183817692878148717022011392 [66955751844124594810692406889727347695696810027520350027775, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck5.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100042835440248421822964740738255728582036747612376839225343 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck6.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100432095294029695723237014575624475064859198628788546043904 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck7.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck8.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100042835440248421822964740738255728582036747612376839225343 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904, 100433627742802866029454694220141837846815249600006693322752] = true :=
      moveStep 6 perm1 onto1 rows1 pol fixed1
        hset hop fresh tail (by decide) (Or.inl ⟨by decide +kernel, by decide +kernel⟩)
    exact Bool.noConfusion (orbitCheck6.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100432095294029695723237014575624475064859198628788546043904 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100433627742802866029454694220141837846815249600006693322752] = true :=
      moveStep 6 perm1 onto1 rows1 pol fixed1
        hset hop fresh tail (by decide) (Or.inl ⟨by decide +kernel, by decide +kernel⟩)
    exact Bool.noConfusion (orbitCheck7.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 80346902212949513774380889341042273384136713836437180455936 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343, 100432095294029695723237014575624475064859198628788546043904] = true :=
      moveStep 6 perm1 onto1 rows1 pol fixed1
        hset hop fresh tail (by decide) (Or.inl ⟨by decide +kernel, by decide +kernel⟩)
    exact Bool.noConfusion (orbitCheck8.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 100042835440248421822964740738255728582036747612376839225343 100432095294029695723237014575624475064859198628788546043904 [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100433627742802866029454694220141837846815249600006693322752] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck12.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 100042835440248421822964740738255728582036747612376839225343 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100432095294029695723237014575624475064859198628788546043904] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck13.symm.trans possible)
  · simp only [Prod.mk.injEq] at which
    obtain ⟨rfl, rfl, rfl⟩ := which
    have possible : dispatch 2 (optimized 6) 100432095294029695723237014575624475064859198628788546043904 100433627742802866029454694220141837846815249600006693322752 [66955751844124594810692406889727347695696810027520350027775, 80346902212949513774380889341042273384136713836437180455936, 94525767309352369147593894796790183817692878148717022011392, 100042835440248421822964740738255728582036747612376839225343] = true :=
      necessaryStep 6 pol (by decide) hset hop fresh tail
    exact Bool.noConfusion (orbitCheck14.symm.trans possible)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject (g : W) (pol : g = goal ∨ g = ~~~goal) (h : build basicOps g 7 rows.toFinset) : False := by
  classical
  obtain ⟨s, hs, hrun⟩ := compress h
  let ws := rows.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have run : live basicOps g 7 ws.toFinset := eq.symm ▸ hrun
  have full : rows.sublists.filter (fun w => cuts w == -1) = [rows] := by decide +kernel
  have only : ws ∈ rows.sublists.filter (fun w => cuts w == -1) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr (List.filter_sublist ..), by simp [cuts_full pol run]⟩
  rw [full, List.mem_singleton] at only
  rw [only] at run
  rcases first_live run with done | ⟨a, ha, b, hb, hab, z, hz, fresh, needed, hset, tail⟩
  · have single := singleton_list (by decide : rows.Nodup) done
    have lengths := congrArg List.length single
    simp [rows] at lengths
  · obtain ⟨r, pos, _⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    rcases pos with ab | ba
    · exact excludesPair pol ab hset hz fresh tail
    · exact excludesPair pol ba (by rw [hset, Finset.insert_comm]) (ops_swap a b ▸ hz) fresh tail

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    7 < binaryCost gs :=
  bound_from_search rows rfl (by decide) reject (by decide +kernel) gs o hg he

end Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩,
   ⟨GateOp.and, [6, 1]⟩,
   ⟨GateOp.and, [7, 2]⟩,
   ⟨GateOp.or, [1, 2]⟩,
   ⟨GateOp.or, [9, 4]⟩,
   ⟨GateOp.and, [10, 5]⟩,
   ⟨GateOp.or, [11, 3]⟩,
   ⟨GateOp.and, [12, 0]⟩,
   ⟨GateOp.or, [8, 13]⟩], 14⟩

lemma computes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = Signed.F x := by decide

end PEqualNP.Outside.L_meta_16151

open PEqualNP.Outside.L_meta_16151 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_16151 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, legal, small, correct⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hg, op⟩ := hasNot
    have binary : Signed.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr
        ⟨g, hg, by simp [Signed.isBinary, op]⟩
    have low := Signed.bound C.gates C.output
      (fun g h => ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (legal g h).1,
        (legal g h).2⟩) correct
    change C.gates.length ≤ s at small
    refine ⟨witness, by simp [Monotone2, witness], ?_, computes⟩
    change 9 ≤ s
    omega
  · refine ⟨C, ?_, small, correct⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    obtain (hop | hop | hop) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (legal g hg).1
    · exact Or.inl hop
    · exact Or.inr hop
    · exact (hasNot ⟨g, hg, hop⟩).elim
