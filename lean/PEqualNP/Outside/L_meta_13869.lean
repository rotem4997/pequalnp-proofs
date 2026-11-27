import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13869


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

abbrev W := BitVec 64
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
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

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 32) :
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
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
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
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
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

def table (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3937069736 * 2 ^ 32 + 3937061000)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def mono : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [4, 8]⟩,
    ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩

theorem mono_ok : Monotone2 mono := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxHeartbeats 4000000 in
theorem value_ok : ∀ x : Fin 6 → Bool, mono.eval (List.ofFn x) = table x := by
  decide +kernel

def rows : List W :=
  [0x80001025ff8ff1ff, 0x1735469287f54e93, 0x71598b18f8798f1c, 0x226e0dc0007e0fe0, 0x447fe000007ff000]

def initial : List W := rows ++ [~~~0]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem reject : search 5 rows = false := by decide +kernel


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def kept (g : Gate) : Bool := isBinary g && !g.inputs.contains 5

theorem reads_fixed (w : List W) (zero : w.getD 5 0 = ~~~0)
    (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) (h : g.inputs.contains 5 = true) :
    holds av (action w g) := by
  have ones : ~~~(0 : W) = BitVec.allOnes 64 := rfl
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  change args.contains 5 = true at h
  rcases args with _ | ⟨i,_ | ⟨j,_ | ⟨k,tl⟩⟩⟩ <;> simp at cap h
  · subst i
    rcases hop with rfl|rfl|rfl
    · change holds av (w.getD 5 0 &&& ~~~(0 : W))
      rw [zero,ones,BitVec.and_allOnes]
      exact Or.inr (Or.inl rfl)
    · change holds av (w.getD 5 0 ||| 0#64)
      rw [zero,BitVec.or_zero]
      exact Or.inr (Or.inl rfl)
    · change holds av (~~~(w.getD 5 0))
      rw [zero,BitVec.not_not]
      exact Or.inl rfl
  · rcases hop with rfl|rfl|rfl
    · change holds av (w.getD i 0 &&& (w.getD j 0 &&& ~~~(0 : W)))
      rw [ones,BitVec.and_allOnes]
      rcases h with rfl|rfl
      · rw [zero,ones,BitVec.allOnes_and]; exact available_read hw j
      · rw [zero,ones,BitVec.and_allOnes]; exact available_read hw i
    · change holds av (w.getD i 0 ||| (w.getD j 0 ||| 0#64))
      rw [BitVec.or_zero]
      rcases h with rfl|rfl
      · rw [zero,ones,BitVec.allOnes_or]; exact Or.inr (Or.inl rfl)
      · rw [zero,ones,BitVec.or_allOnes]; exact Or.inr (Or.inl rfl)
    · simpa [action] using holds_not (available_read hw i)

set_option maxRecDepth 4000 in
theorem compileDiscount (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (len : 5 < w.length) (zero : w.getD 5 0 = ~~~0)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (gs.countP kept) av := by
  induction gs generalizing w av with
  | nil =>
    have h := compile [] out hg w av hw he
    simpa [binaryCost] using h
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
        · exact (List.mem_singleton.mp hu) ▸ new) (by simp; omega)
        (by rw [List.getD_append _ _ _ _ len,zero]) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [List.countP_cons,kept,neg] using cont av hw stepClass
    by_cases saved : g.inputs.contains 5 = true
    · have h := reads_fixed w zero av hw g (hg g (by simp)) saved
      have present : 5 ∈ g.inputs := by simpa using saved
      simpa [List.countP_cons,kept,neg,present] using cont av hw h
    · simp only [neg,ite_true] at stepClass
      have absent : 5 ∉ g.inputs := by simpa using saved
      have len : (g::gs).countP kept = gs.countP kept+1 := by simp [List.countP_cons,kept,neg,absent]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def nextBool (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

def away (R : Bool → Bool → Prop) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i : ℕ, i ≠ 5 → R (a.getD i false) (b.getD i false)

theorem appendAway {R : Bool → Bool → Prop} (rflR : ∀ x, R x x)
    {a b : List Bool} (old : away R a b) {x y : Bool} (new : R x y) :
    away R (a++[x]) (b++[y]) := by
  refine ⟨by simp [old.1],?_⟩
  intro i off
  by_cases earlier : i < a.length
  · have later : i < b.length := old.1 ▸ earlier
    rw [List.getD_append _ _ _ _ earlier,List.getD_append _ _ _ _ later]
    exact old.2 i off
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have h := old.1; omega),old.1]
    cases i-b.length <;> simp [new,rflR]

def goesDown (a b : Bool) : Prop := b = true → a = true

theorem plainDown {a b : List Bool} (related : away goesDown a b)
    (g : Gate) (plain : g.op = .and ∨ g.op = .or) (off : ¬ 5 ∈ g.inputs) :
    goesDown (nextBool a g) (nextBool b g) := by
  have each (i : ℕ) (h : i ∈ g.inputs) := related.2 i (fun hi => off (hi ▸ h))
  rcases plain with h|h
  · simp only [goesDown,nextBool,h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro all i hi
    exact each i hi (all i hi)
  · simp only [goesDown,nextBool,h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,on⟩
    exact ⟨i,hi,each i hi on⟩

theorem foldDown (gs : List Gate) {a b : List Bool} (related : away goesDown a b)
    (plain : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (off : ∀ g ∈ gs, ¬ 5 ∈ g.inputs) :
    away goesDown (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact related
  | cons g gs ih =>
    exact ih (appendAway (fun _ h => h) related
      (plainDown related g (plain _ (by simp)) (off _ (by simp))))
      (fun h hh => plain h (by simp [hh])) (fun h hh => off h (by simp [hh]))

theorem negativeReadOnly (gs : List Gate) (hg : ∀ g ∈ gs, legal g)
    (one : (gs.filter isBinary).length + 1 ≥ gs.length)
    (off : ∀ g ∈ gs, g.op = .and ∨ g.op = .or → ¬ 5 ∈ g.inputs)
    {a b : List Bool} (equal : away Eq a b)
    (len : 5 < a.length) (a5 : a.getD 5 false = false) (b5 : b.getD 5 false = true) :
    away goesDown (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨equal.1,fun i hi => by rw [equal.2 i hi]; exact id⟩
  | cons g gs ih =>
    have bLen : 5 < b.length := equal.1 ▸ len
    obtain ⟨op,cap⟩ := hg g (by simp)
    have rest (j : Gate) (hj : j ∈ gs) : legal j := hg j (by simp [hj])
    have restOff (j : Gate) (hj : j ∈ gs) := off j (List.mem_cons_of_mem _ hj)
    by_cases neg : g.op = .not
    · have lengthEq : (gs.filter isBinary).length = gs.length := by
        simp only [List.filter_cons,isBinary,neg,Bool.false_eq_true,ite_false,List.length_cons] at one
        exact Nat.le_antisymm (List.length_filter_le ..) (by omega)
      have plain (j : Gate) (hj : j ∈ gs) : j.op = .and ∨ j.op = .or := by
        rcases (rest j hj).1 with h | h | h
        · exact .inl h
        · exact .inr h
        · have lt := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
            ⟨j,hj,by simp [isBinary,h]⟩
          omega
      have related : away goesDown a b := ⟨equal.1,fun i hi => by rw [equal.2 i hi]; exact id⟩
      have new : goesDown (nextBool a g) (nextBool b g) := by
        unfold nextBool goesDown
        rw [neg]
        cases h : g.inputs with
        | nil => simp [GateOp.eval]
        | cons i tail =>
          simp only [GateOp.eval,h,List.map_cons,List.headD_cons]
          by_cases pick : i = 5
          · subst i
            change goesDown (!(a.getD 5 false)) (!(b.getD 5 false))
            rw [a5,b5]
            simp [goesDown]
          · rw [equal.2 i pick]
            exact id
      exact foldDown gs (appendAway (fun _ h => h) related new) plain
        (fun j hj => restOff j hj (plain j hj))
    · have plain : g.op = .and ∨ g.op = .or := by tauto
      have eqNext : nextBool a g = nextBool b g := by
        unfold nextBool
        congr 1
        exact List.map_congr_left fun i hi => equal.2 i (fun he => off g (by simp) plain (he ▸ hi))
      have capRest : (gs.filter isBinary).length + 1 ≥ gs.length := by
        have keep : isBinary g = true := by rcases plain with h|h <;> simp [isBinary,h]
        simp only [List.filter_cons,keep,ite_true,List.length_cons] at one
        omega
      exact ih rest capRest restOff (a := a++[nextBool a g]) (b := b++[nextBool b g])
        (appendAway (fun _ => rfl) equal eqNext)
        (by simp; omega)
        (by rw [List.getD_append _ _ _ _ len,a5])
        (by rw [List.getD_append _ _ _ _ bLen,b5])


theorem seed_holds (w : W) (hw : w ∈ initial) : holds rows.toFinset w := by
  have eq : initial.toFinset = insert (~~~(0 : W)) rows.toFinset := by decide
  have h := (List.mem_toFinset.mpr hw : w ∈ initial.toFinset)
  rw [eq,Finset.mem_insert] at h
  rcases h with rfl|old
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨w,old,Or.inl rfl⟩)

theorem fixedLower (C : Circuit) (fits : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x) :
    6 ≤ C.gates.countP kept := by
  by_contra! tiny
  have evaluate (k : Fin 64) :
      (C.gates.foldl step (initial.map (bit k))).getD C.output false = bit k (~~~goal) := by
    let x (i : Fin 6) := bit k (initial.getD i.val 0)
    have width : initial.length = 6 := rfl
    have same : List.ofFn x = initial.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < initial.length := by simpa using hj
        simp only [List.getElem_ofFn,List.getElem_map,x,List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt,Option.getD_some]
    change C.eval (initial.map (bit k)) = bit k (~~~goal)
    rw [← same,computes]
    have all : ∀ k : Fin 64, table (fun i : Fin 6 => bit k (initial.getD i.val 0)) =
        bit k (~~~goal) := by decide +kernel
    exact all k
  obtain ⟨t,ht,run⟩ := compileDiscount C.gates C.output (fun g hm => fits g hm)
    initial rows.toFinset seed_holds (by decide) (by decide) evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a rows.toFinset) :
      build basicOps t b rows.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 5 rows (by decide)
    (lift (by omega) run)))

theorem sixthStable (gs : List Gate) (w : List Bool) (len : 5 < w.length) :
    (gs.foldl step w).getD 5 false = w.getD 5 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (w ++ [nextBool w g])).getD 5 false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ len]

theorem dependsPositively (C : Circuit) (fits : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x)
    (cap : C.size ≤ binaryCost C.gates + 1) :
    ∃ g ∈ C.gates, isBinary g = true ∧ g.inputs.contains 5 = true := by
  by_contra! none
  have ignores (g : Gate) (mem : g ∈ C.gates) (plain : g.op = .and ∨ g.op = .or) :
      ¬ 5 ∈ g.inputs := by
    have bin : isBinary g = true := by rcases plain with h|h <;> simp [isBinary,h]
    have no := none g mem bin
    simpa using no
  let a : List Bool := [true,false,true,false,false,false]
  let b : List Bool := [true,false,true,false,false,true]
  have same : away Eq a b := by
    refine ⟨rfl,?_⟩
    intro i hi
    by_cases bound : i < 6
    · let j : Fin 6 := ⟨i,bound⟩
      have all : ∀ j : Fin 6, j.val ≠ 5 → a.getD j.val false = b.getD j.val false := by
        dsimp [a,b]
        decide
      exact all j hi
    · rw [List.getD_eq_default _ _ (by simpa [a] using Nat.le_of_not_gt bound),
        List.getD_eq_default _ _ (by simpa [b] using Nat.le_of_not_gt bound)]
  have down := negativeReadOnly C.gates (fun g hm => fits g hm) cap ignores
    (a := a) (b := b) same (by decide) (by decide) (by decide)
  have output : C.output ≠ 5 := by
    intro eq
    let x : Fin 6 → Bool := ![true,true,false,false,false,false]
    have h := computes x
    have row : List.ofFn x = [true,true,false,false,false,false] := by decide
    have on : table x = true := by decide
    rw [on,row] at h
    change (C.gates.foldl step [true,true,false,false,false,false]).getD C.output false = true at h
    rw [eq,sixthStable _ _ (by decide)] at h
    contradiction
  have no : C.eval a = false := by
    let x : Fin 6 → Bool := ![true,false,true,false,false,false]
    have row : List.ofFn x = a := by decide
    rw [← row,computes]
    decide
  have yes : C.eval b = true := by
    let x : Fin 6 → Bool := ![true,false,true,false,false,true]
    have row : List.ofFn x = b := by decide
    rw [← row,computes]
    decide
  have monotone := down.2 C.output output
  change goesDown (C.eval a) (C.eval b) at monotone
  rw [no,yes] at monotone
  exact Bool.false_ne_true (monotone rfl)

theorem noSmallNot (C : Circuit) (fits : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x)
    (small : C.size ≤ 7) :
    ∀ g ∈ C.gates, g.op ≠ .not := by
  intro g mem use
  have short : binaryCost C.gates < C.size :=
    (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
      ⟨g,mem,by simp [isBinary,use]⟩
  have countEq : C.gates.countP kept =
      ((C.gates.filter isBinary).filter (fun g => !g.inputs.contains 5)).length := by
    rw [List.countP_eq_length_filter,List.filter_filter]
    rw [show kept = (fun g => !g.inputs.contains 5 && isBinary g) from
      funext fun g => Bool.and_comm _ _]
  have cost := fixedLower C fits computes
  rw [countEq] at cost
  have leq := List.length_filter_le (fun g : Gate => !g.inputs.contains 5) (C.gates.filter isBinary)
  change _ ≤ binaryCost C.gates at leq
  obtain ⟨h,hm,bin,reads⟩ := dependsPositively C fits computes (by omega)
  have atInput : 5 ∈ h.inputs := by simpa using reads
  have strict := (List.length_filter_lt_length_iff_exists (p := fun g : Gate => !g.inputs.contains 5)).mpr
    ⟨h,List.mem_filter.mpr ⟨hm,bin⟩,by simp [atInput]⟩
  change _ < binaryCost C.gates at strict
  omega

theorem replaceCircuit : ∀ s : ℕ, HasCircuitSize 6 table s →
    ∃ C, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x := by
  intro s h
  by_cases large : 8 ≤ s
  · exact ⟨mono,mono_ok,by change 8 ≤ s; exact large,value_ok⟩
  obtain ⟨C,fits,small,comp⟩ := h
  have hm := noSmallNot C fits comp (by omega)
  refine ⟨C,?_,small,comp⟩
  intro g hG
  obtain ⟨op,arity⟩ := fits g hG
  change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
  exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hm g hG eq).elim)),arity⟩


end PEqualNP.Outside.L_meta_13869

theorem PEqualNP.Outside.L_meta_13869 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069736 * 2 ^ 32 + 3937061000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069736 * 2 ^ 32 + 3937061000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :=
  PEqualNP.Outside.L_meta_13869.replaceCircuit
