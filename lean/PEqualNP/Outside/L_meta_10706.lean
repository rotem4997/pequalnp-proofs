import PEqualNP.Defs

-- The live-wire search, signed circuit compiler and four-input lower bound adapt
-- L-meta-8724 and L-meta-1449. Their compression and search follow L-meta-703 and L-meta-1429.
-- The signed one- and two-gate restriction lemmas below apply those techniques to this graph.

namespace PEqualNP.Outside.L_meta_10706_aux

namespace GThreshold

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
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
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

def k4inputs : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842, 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084, 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108, 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4exact : search 6 k4inputs = false := by decide +kernel

end GThreshold

namespace JElim
open GThreshold

theorem sb_flip {k : ℕ} {av : Finset W} {w : W} (h : SignedBuild k av (~~~w)) : SignedBuild k av w := by
  rcases h with h|h|h|h
  · right; left
    simpa using congrArg (fun x : W => ~~~x) h
  · left
    simpa using congrArg (fun x : W => ~~~x) h
  · right; right; right; exact h
  · right; right; left; simpa using h

theorem elimOne {av av' : Finset W} {p g : W} {k : ℕ}
    (D : W → Prop) (Dops : ∀ a b z, z ∈ basicOps a b → D z → D a ∨ D b)
    (Dg : D g ∧ D (~~~g)) (Donly : ∀ w ∈ av, D w → w = p)
    (gp : p ≠ g ∧ p ≠ ~~~g) (gn : g ≠ 0 ∧ g ≠ ~~~0)
    (f : W → W) (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    (hn : ∀ w, f (~~~w) = ~~~f w) (fp : f p = 0)
    (hav : ∀ w ∈ av, holds av' (f w)) (run : SignedBuild (k+1) av g) :
    SignedBuild k av' (f g) := by
  have go {t : W} (dt : D t) (pt : p ≠ t) (tr : build basicOps t (k+1) av) :
      SignedBuild k av' (f t) := by
    obtain ⟨s,hs,hl⟩ := compress tr
    obtain ⟨w,hw,hd⟩ := live_separates D dt Dops hl
    obtain rfl := Donly w (hs hw) hd
    exact live_transport_save hm hl hw pt fp (fun u hu => hav u (hs hu))
  rcases run with h|h|h|h
  · exact (gn.1 h).elim
  · exact (gn.2 h).elim
  · exact go Dg.1 gp.1 h
  · exact sb_flip ((hn g) ▸ go Dg.2 gp.2 h)


set_option maxRecDepth 5000 in
theorem top_and (x : W) : ~~~(0 : W) &&& x = x := BitVec.allOnes_and
set_option maxRecDepth 5000 in
theorem and_top (x : W) : x &&& ~~~(0 : W) = x := BitVec.and_allOnes
set_option maxRecDepth 5000 in
theorem top_or (x : W) : ~~~(0 : W) ||| x = ~~~0 := BitVec.allOnes_or
set_option maxRecDepth 5000 in
theorem or_top (x : W) : x ||| ~~~(0 : W) = ~~~0 := BitVec.or_allOnes
theorem zero_and (x : W) : (0 : W) &&& x = 0 := BitVec.zero_and
theorem and_zero (x : W) : x &&& (0 : W) = 0 := BitVec.and_zero

set_option maxRecDepth 5000 in
theorem ops_const {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hc : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOps x y) : holds av z := by
  rcases hc with (h|h)|(h|h)
  · exact mem_ops_zero hx hy (.inl h) hz
  · subst x
    simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simp only [top_and,top_or,BitVec.not_not,and_zero] <;> first | exact hy | exact holds_not hy | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  · exact mem_ops_zero hx hy (.inr h) hz
  · subst y
    simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simp only [and_top,or_top,BitVec.not_not,and_zero,top_and] <;> first | exact hx | exact holds_not hx | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
theorem live_save_const {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0 ∨ f p = ~~~0)
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
        · have zz : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := ops_const (hav a ha) (hav b hb) zz mapped
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

theorem choose_ext {av : Finset W} {z : W} (h : reachable av z) :
    ∃ av', av ⊆ av' ∧ holds av' z ∧
        ∀ k t, SignedBuild k av' t → SignedBuild (k+1) av t := by
  rcases h with h|⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact ⟨av,fun _ h => h,h,fun _ _ h => sb_wait h⟩
  · exact ⟨insert w av,fun u hu => Finset.mem_insert_of_mem hu,ok,fun _ _ h => sb_step ha hb hn hw h⟩

set_option maxRecDepth 5000 in
theorem zero_choice {a b p z : W} (hz : z ∈ basicOps a b) (touch : p = a ∨ p = b)
    (f : Bool → W → W) (h0 : f false p = 0) (h1 : f true p = ~~~0)
    (hn : ∀ v x, f v (~~~x) = ~~~f v x)
    (hand : ∀ v x y, f v (x &&& y) = (f v x &&& f v y))
    (hor : ∀ v x y, f v (x ||| y) = (f v x ||| f v y)) :
    ∃ v, f v z = 0 ∨ f v z = ~~~0 := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases touch with rfl|rfl <;> rcases hz with rfl|rfl|rfl|rfl
  · exact ⟨false, .inl (by rw [hand,h0,zero_and])⟩
  · exact ⟨true, .inr (by rw [hor,h1,top_or])⟩
  · exact ⟨false, .inl (by rw [hand,h0,zero_and])⟩
  · exact ⟨true, .inl (by rw [hand,hn,h1,BitVec.not_not,and_zero])⟩
  · exact ⟨false, .inl (by rw [hand,h0,and_zero])⟩
  · exact ⟨true, .inr (by rw [hor,h1,or_top])⟩
  · exact ⟨true, .inl (by rw [hand,hn,h1,BitVec.not_not,and_zero])⟩
  · exact ⟨false, .inl (by rw [hand,h0,zero_and])⟩

theorem two_pos {s : Finset W} {p g : W} {k : ℕ} (hl : live basicOps g k s)
    (hp : p ∈ s) (pg : p ≠ g) (f : Bool → W → W)
    (choice : ∀ a b z, z ∈ basicOps a b → p = a ∨ p = b → ∃ v, f v z = 0 ∨ f v z = ~~~0)
    (proper : ∀ v, f v g ≠ 0 ∧ f v g ≠ ~~~0) : 2 ≤ k := by
  cases k with
  | zero =>
    change s = {g} at hl
    exact (pg (by simpa [hl] using hp)).elim
  | succ k =>
    cases k with
    | succ k => omega
    | zero =>
      rcases hl with skip|⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · change s = {g} at skip
        exact (pg (by simpa [skip] using hp)).elim
      · change insert z r = {g} at tail
        have zg : z = g := by
          have h : z ∈ insert z r := Finset.mem_insert_self ..
          simpa [tail] using h
        subst z
        rw [he] at hp
        rcases Finset.mem_insert.mp hp with pa|rest
        · obtain ⟨v,bad⟩ := choice a b g hz (Or.inl pa)
          exact (bad.elim (proper v).1 (proper v).2).elim
        · rcases Finset.mem_insert.mp rest with pb|pr
          · obtain ⟨v,bad⟩ := choice a b g hz (Or.inr pb)
            exact (bad.elim (proper v).1 (proper v).2).elim
          · have hh : p ∈ insert g r := Finset.mem_insert_of_mem pr
            exact (pg (by simpa [tail] using hh)).elim

theorem transportTwo {s : Finset W} {av : Bool → Finset W} {p g : W} {k : ℕ}
    (hl : live basicOps g k s) (hp : p ∈ s) (pg : p ≠ g)
    (f : Bool → W → W)
    (hm : ∀ v a b z, z ∈ basicOps a b → f v z ∈ basicOps (f v a) (f v b))
    (fp0 : f false p = 0) (fp1 : f true p = ~~~0)
    (choice : ∀ a b z, z ∈ basicOps a b → p = a ∨ p = b → ∃ v, f v z = 0 ∨ f v z = ~~~0)
    (proper : ∀ v, f v g ≠ 0 ∧ f v g ≠ ~~~0)
    (hav : ∀ v w, w ∈ s → holds (av v) (f v w)) :
    ∃ v, SignedBuild (k-2) (av v) (f v g) := by
  induction k generalizing s av with
  | zero =>
    have := two_pos hl hp pg f choice proper
    omega
  | succ k ih =>
    rcases hl with skip|⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
    · obtain ⟨v,hv⟩ := ih skip hp hav
      exact ⟨v,sb_le (by omega) hv⟩
    · have old : ∀ v u, u ∈ r → holds (av v) (f v u) := fun v u hu => hav v u (by simp [he,hu])
      by_cases touch : p = a ∨ p = b
      · obtain ⟨v,collapsed⟩ := choice a b z hz touch
        have zp : z ≠ g := by
          rintro rfl
          exact collapsed.elim (proper v).1 (proper v).2
        have pv : f v p = 0 ∨ f v p = ~~~0 := by cases v <;> first | exact .inl fp0 | exact .inr fp1
        have zab : (f v a = 0 ∨ f v a = ~~~0) ∨ (f v b = 0 ∨ f v b = ~~~0) :=
          touch.elim (fun h => .inl (h ▸ pv)) (fun h => .inr (h ▸ pv))
        refine ⟨v,live_save_const (hm v) tail (Finset.mem_insert_self ..) zp collapsed ?_⟩
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl|hw
        · exact ops_const (hav v a ha) (hav v b hb) zab (hm v a b _ hz)
        · exact old v _ hw
      · have pr : p ∈ r := by
          rw [he] at hp
          simpa [Finset.mem_insert, (not_or.mp touch).1, (not_or.mp touch).2] using hp
        have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
        have bound := two_pos tail pt pg f choice proper
        have ext (v : Bool) : ∃ av', av v ⊆ av' ∧ holds av' (f v z) ∧
              ∀ n t, SignedBuild n av' t → SignedBuild (n+1) (av v) t :=
          choose_ext (mem_ops_reach (hav v a ha) (hav v b hb) (hm v a b z hz))
        choose newav sub held advance using ext
        obtain ⟨v, hv⟩ := ih (av := newav) tail pt (by
          intro v w hw
          rcases Finset.mem_insert.mp hw with rfl|hw
          · exact held v
          · exact holds_mono (sub v) (old v _ hw))
        exact ⟨v,sb_le (by omega) (advance v _ _ hv)⟩

theorem elimTwo {av av' : Finset W} {p g : W} {k : ℕ}
    (D : W → Prop) (Dops : ∀ a b z, z ∈ basicOps a b → D z → D a ∨ D b)
    (Dg : D g ∧ D (~~~g)) (Donly : ∀ w ∈ av, D w → w = p)
    (gp : p ≠ g ∧ p ≠ ~~~g) (gn : g ≠ 0 ∧ g ≠ ~~~0)
    (f : Bool → W → W)
    (hm : ∀ b a c z, z ∈ basicOps a c → f b z ∈ basicOps (f b a) (f b c))
    (hn : ∀ b w, f b (~~~w) = ~~~f b w)
    (hand : ∀ b u v, f b (u &&& v) = (f b u &&& f b v))
    (hor : ∀ b u v, f b (u ||| v) = (f b u ||| f b v))
    (fp0 : f false p = 0) (fp1 : f true p = ~~~0)
    (hav : ∀ b w, w ∈ av → holds av' (f b w)) (proper : ∀ b, f b g ≠ 0 ∧ f b g ≠ ~~~0)
    (run : SignedBuild (k+2) av g) : ∃ b, SignedBuild k av' (f b g) := by
  have go {t : W} (dt : D t) (pt : p ≠ t) (pr : ∀ b, f b t ≠ 0 ∧ f b t ≠ ~~~0)
      (tr : build basicOps t (k+2) av) : ∃ b, SignedBuild k av' (f b t) := by
    obtain ⟨s,hs,hl⟩ := compress tr
    obtain ⟨w,hw,hd⟩ := live_separates D dt Dops hl
    obtain rfl := Donly w (hs hw) hd
    exact transportTwo (av := fun _ => av') hl hw pt f hm fp0 fp1
      (fun _ _ _ hz t => zero_choice hz t f fp0 fp1 hn hand hor)
      pr (fun v u hu => hav v u (hs hu))
  rcases run with h|h|h|h
  · exact (gn.1 h).elim
  · exact (gn.2 h).elim
  · exact go Dg.1 gp.1 proper h
  · obtain ⟨b,hb⟩ := go Dg.2 gp.2 (by
      intro b
      rw [hn]
      constructor
      · intro e
        apply (proper b).2
        simpa using congrArg (fun x : W => ~~~x) e
      · intro e
        apply (proper b).1
        simpa using congrArg (fun x : W => ~~~x) e) h
    exact ⟨b,sb_flip ((hn b g) ▸ hb)⟩

end JElim

namespace JData
open GThreshold PEqualNP.CircuitLowerBounds

def x0_0 : W := 0xb55555aedaaaaaaaaaaab5556aaad55556bb6aaaaaaaaaaad555aaab55555aeda102a840aa102a840aa102a840aa102a840aa102a840aa102a840aa102a840aa
def x0_1 : W := 0xd999e6cb6cccccccccccd999b33366679b2db333333333336666cccd999e6cb6c0233008cc0233008cc0233008cc0233008cc0233008cc0233008cc0233008cc
def x0_2 : W := 0x1e1e78f38f0f0f0f0f0f1e1e3c3c7879e3ce3c3c3c3c3c3c7878f0f1e1e78f38000bc002f000bc002f000bc002f000bc002f000bc002f000bc002f000bc002f0
def x0_3 : W := 0x1fe07f03fff00ff00ff01fe03fc07f81fc0fffc03fc03fc07f80ff01fe07f03f004c00130004c00130004c00130004c00130004c00130004c00130004c001300
def x0_4 : W := 0xe0007ffc0ffff0000fffe0003fff8001fff03fffc0003fff8000fffe0007ffc00a70029c00a70029c00a70029c00a70029c00a70029c00a70029c00a70029c00
def x0_5 : W := 0xffff80000ffffffff00000003ffffffe00003fffffffc0000000fffffff80000038000e00038000e00038000e00038000e00038000e00038000e00038000e000
def x0_6 : W := 0xfffffffffffffffc000000000003fffffffffffffff0000000000000c00030000c00030000c00030000c00030000c00030000c00030000c00030000
def A0 : List W := [x0_0, x0_1, x0_2, x0_3, x0_4, x0_5, x0_6]
def x1_1 : W := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def x1_2 : W := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def x1_3 : W := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def x1_4 : W := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def x1_5 : W := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def x1_6 : W := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def A1 : List W := [x1_1, x1_2, x1_3, x1_4, x1_5, x1_6]
def x2_1 : W := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def x2_2 : W := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def x2_3 : W := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def x2_5 : W := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def x2_6 : W := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def A2 : List W := [x2_1, x2_2, x2_3, x2_5, x2_6]
def y1 : W := 0xfffffefefefeeca0fffffefefefeeca0fffffefefefeeca0fffffefefefeeca0fffffefefefeeca0fffffefefefeeca0fffffefefefeeca0fffffefefefeeca0
def y20 : W := 0xfffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0fffefea0
def y21 : W := 0xfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeecfffefeec

abbrev MapRows := List (Fin 512 × W)

def fill (p : Fin 512) (w : W) : W := if w[p.val] then ~~~0 else 0

def mux (m a b : W) : W := (m &&& a) ||| ((~~~m) &&& b)

def pull : MapRows → W → W
  | [], w => fill 0 w
  | (p,m)::rest, w => mux m (fill p w) (pull rest w)

theorem fill_not (p : Fin 512) (a : W) : fill p (~~~a) = ~~~(fill p a) := by
  cases h : a[p.val] <;> simp [fill, BitVec.getElem_not, h]
theorem fill_and (p : Fin 512) (a b : W) : fill p (a &&& b) = (fill p a &&& fill p b) := by
  cases h : a[p.val] <;> cases h' : b[p.val] <;> simp [fill, BitVec.getElem_and, h,h']
theorem fill_or (p : Fin 512) (a b : W) : fill p (a ||| b) = (fill p a ||| fill p b) := by
  cases h : a[p.val] <;> cases h' : b[p.val] <;> simp [fill, BitVec.getElem_or, h,h']

theorem mux_not (m a b : W) : mux m (~~~a) (~~~b) = ~~~(mux m a b) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  cases h : m[j] <;> simp [mux, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or,h]
theorem mux_and (m a b c d : W) : mux m (a &&& b) (c &&& d) = (mux m a c &&& mux m b d) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  cases h : m[j] <;> simp [mux, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or,h]
theorem mux_or (m a b c d : W) : mux m (a ||| b) (c ||| d) = (mux m a c ||| mux m b d) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  cases h : m[j] <;> simp [mux, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or,h]

theorem pnot (ix : MapRows) (u : W) : pull ix (~~~u) = ~~~(pull ix u) := by
  induction ix with
  | nil => exact fill_not _ _
  | cons v rest ih => simp only [pull, fill_not, ih, mux_not]

theorem pand (ix : MapRows) (a b : W) : pull ix (a &&& b) = (pull ix a &&& pull ix b) := by
  induction ix with
  | nil => exact fill_and _ _ _
  | cons v rest ih => simp only [pull, fill_and, ih, mux_and]

theorem por (ix : MapRows) (a b : W) : pull ix (a ||| b) = (pull ix a ||| pull ix b) := by
  induction ix with
  | nil => exact fill_or _ _ _
  | cons v rest ih => simp only [pull, fill_or, ih, mux_or]

theorem pops (ix : MapRows) (a b z : W) (hz : z ∈ basicOps a b) :
    pull ix z ∈ basicOps (pull ix a) (pull ix b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [pand, por, pnot]

abbrev dif (a b : Fin 512) (w : W) : Prop := w[a.val] ≠ w[b.val]

theorem difops (a b : Fin 512) (u v z : W) (hz : z ∈ basicOps u v)
    (h : dif a b z) : dif a b u ∨ dif a b v := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! hh
  obtain ⟨hu,hv⟩ := hh
  unfold dif at *
  rcases hz with rfl | rfl | rfl | rfl <;> apply h <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, hu,hv]

def src0 : MapRows := [(0, 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001),
(2, 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002),
(4, 0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004),
(6, 0x80000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008),
(8, 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010),
(9, 0x400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040),
(10, 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100),
(11, 0x2000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200),
(12, 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000),
(13, 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000),
(15, 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000),
(16, 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000),
(17, 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000),
(257, 0x200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020),
(260, 0x800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080),
(264, 0x4000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400),
(266, 0x8000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800),
(269, 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000),
(271, 0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000),
(273, 0x80000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000),
(275, 0x200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000),
(277, 0x400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000),
(279, 0x800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000),
(281, 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000),
(283, 0x2000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000),
(285, 0x4000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000),
(287, 0x8000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000),
(290, 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000),
(292, 0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000),
(294, 0x80000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000),
(296, 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000),
(298, 0x200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000),
(300, 0x400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000),
(302, 0x800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000),
(305, 0x2000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000),
(307, 0x4000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000),
(309, 0x8000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000),
(311, 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000),
(313, 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000),
(315, 0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000),
(317, 0x80000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000),
(320, 0x200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000),
(322, 0x400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000),
(324, 0x800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000),
(326, 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000),
(328, 0x2000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000),
(330, 0x4000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000),
(332, 0x8000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000),
(334, 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000),
(336, 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000),
(338, 0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000),
(340, 0x80000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000),
(342, 0x100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000),
(344, 0x200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000),
(346, 0x400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000),
(348, 0x800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000),
(350, 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000),
(352, 0x2000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000),
(354, 0x4000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000),
(356, 0x8000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000),
(358, 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000),
(360, 0x20000000000000002000000000000000200000000000000020000000000000002000000000000000200000000000000020000000000000002000000000000000),
(362, 0x40000000000000004000000000000000400000000000000040000000000000004000000000000000400000000000000040000000000000004000000000000000),
(364, 0x80000000000000008000000000000000800000000000000080000000000000008000000000000000800000000000000080000000000000008000000000000000)]
set_option maxRecDepth 8000 in
theorem map0_0_0 : pull src0 x0_0 = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map0_0_1 : pull src0 x0_1 = x1_1 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map0_0_2 : pull src0 x0_2 = x1_2 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map0_0_3 : pull src0 x0_3 = x1_3 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map0_0_4 : pull src0 x0_4 = x1_4 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map0_0_5 : pull src0 x0_5 = x1_5 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map0_0_6 : pull src0 x0_6 = x1_6 := by decide +kernel
theorem hav00 (w : W) (hw : w ∈ A0.toFinset) : holds A1.toFinset (pull src0 w) := by
  simp only [A0, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl map0_0_0
  · exact Or.inr (Or.inr ⟨x1_1, by simp [A1], Or.inl map0_0_1⟩)
  · exact Or.inr (Or.inr ⟨x1_2, by simp [A1], Or.inl map0_0_2⟩)
  · exact Or.inr (Or.inr ⟨x1_3, by simp [A1], Or.inl map0_0_3⟩)
  · exact Or.inr (Or.inr ⟨x1_4, by simp [A1], Or.inl map0_0_4⟩)
  · exact Or.inr (Or.inr ⟨x1_5, by simp [A1], Or.inl map0_0_5⟩)
  · exact Or.inr (Or.inr ⟨x1_6, by simp [A1], Or.inl map0_0_6⟩)
set_option maxRecDepth 8000 in
theorem goal00 : pull src0 goal = y1 := by decide +kernel
abbrev D0 : W → Prop := dif 8 256
set_option maxRecDepth 8000 in
theorem gd0 : D0 goal ∧ D0 (~~~goal) := by decide +kernel
set_option maxRecDepth 8000 in
theorem gp0 : x0_0 ≠ goal ∧ x0_0 ≠ ~~~goal := by decide +kernel
set_option maxRecDepth 8000 in
theorem gn0 : goal ≠ 0 ∧ goal ≠ ~~~0 := by decide +kernel
theorem only0 (w : W) (hw : w ∈ A0.toFinset) (hd : D0 w) : w = x0_0 := by
  simp only [A0, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact False.elim ((by decide +kernel : ¬ D0 x0_1) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 x0_2) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 x0_3) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 x0_4) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 x0_5) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 x0_6) hd)
def src10 : MapRows := [(0, 0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001),
(1, 0x2000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002),
(2, 0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004),
(3, 0x8000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008),
(4, 0x10000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010),
(5, 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020),
(6, 0x40000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040),
(7, 0x80000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080),
(16, 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100),
(17, 0x200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200),
(18, 0x400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400),
(19, 0x800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800),
(20, 0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000),
(21, 0x2000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000),
(22, 0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000),
(23, 0x8000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000),
(32, 0x10000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000),
(33, 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000),
(34, 0x40000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000),
(35, 0x80000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000),
(36, 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000),
(37, 0x200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000),
(38, 0x400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000),
(39, 0x800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000),
(48, 0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000),
(49, 0x2000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000),
(50, 0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000),
(51, 0x8000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000),
(52, 0x10000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000),
(53, 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000),
(54, 0x40000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000),
(55, 0x80000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000)]
set_option maxRecDepth 8000 in
theorem map1_0_1 : pull src10 x1_1 = x2_1 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_0_2 : pull src10 x1_2 = x2_2 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_0_3 : pull src10 x1_3 = x2_3 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_0_4 : pull src10 x1_4 = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_0_5 : pull src10 x1_5 = x2_5 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_0_6 : pull src10 x1_6 = x2_6 := by decide +kernel
theorem hav10 (w : W) (hw : w ∈ A1.toFinset) : holds A2.toFinset (pull src10 w) := by
  simp only [A1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨x2_1, by simp [A2], Or.inl map1_0_1⟩)
  · exact Or.inr (Or.inr ⟨x2_2, by simp [A2], Or.inl map1_0_2⟩)
  · exact Or.inr (Or.inr ⟨x2_3, by simp [A2], Or.inl map1_0_3⟩)
  · exact Or.inl map1_0_4
  · exact Or.inr (Or.inr ⟨x2_5, by simp [A2], Or.inl map1_0_5⟩)
  · exact Or.inr (Or.inr ⟨x2_6, by simp [A2], Or.inl map1_0_6⟩)
set_option maxRecDepth 8000 in
theorem goal10 : pull src10 y1 = y20 := by decide +kernel
def src11 : MapRows := [(8, 0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001),
(9, 0x2000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002),
(10, 0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004),
(11, 0x8000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008),
(12, 0x10000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010),
(13, 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020),
(14, 0x40000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040),
(15, 0x80000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080),
(24, 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100),
(25, 0x200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200),
(26, 0x400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400),
(27, 0x800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800),
(28, 0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000),
(29, 0x2000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000),
(30, 0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000),
(31, 0x8000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000),
(40, 0x10000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000),
(41, 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000),
(42, 0x40000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000),
(43, 0x80000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000),
(44, 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000),
(45, 0x200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000),
(46, 0x400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000),
(47, 0x800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000),
(56, 0x1000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000),
(57, 0x2000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000),
(58, 0x4000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000),
(59, 0x8000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000),
(60, 0x10000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000),
(61, 0x20000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000200000002000000020000000),
(62, 0x40000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000400000004000000040000000),
(63, 0x80000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000800000008000000080000000)]
set_option maxRecDepth 8000 in
theorem map1_1_1 : pull src11 x1_1 = x2_1 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_1_2 : pull src11 x1_2 = x2_2 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_1_3 : pull src11 x1_3 = x2_3 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_1_4 : pull src11 x1_4 = (~~~0) := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_1_5 : pull src11 x1_5 = x2_5 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map1_1_6 : pull src11 x1_6 = x2_6 := by decide +kernel
theorem hav11 (w : W) (hw : w ∈ A1.toFinset) : holds A2.toFinset (pull src11 w) := by
  simp only [A1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨x2_1, by simp [A2], Or.inl map1_1_1⟩)
  · exact Or.inr (Or.inr ⟨x2_2, by simp [A2], Or.inl map1_1_2⟩)
  · exact Or.inr (Or.inr ⟨x2_3, by simp [A2], Or.inl map1_1_3⟩)
  · exact Or.inr (Or.inl map1_1_4)
  · exact Or.inr (Or.inr ⟨x2_5, by simp [A2], Or.inl map1_1_5⟩)
  · exact Or.inr (Or.inr ⟨x2_6, by simp [A2], Or.inl map1_1_6⟩)
set_option maxRecDepth 8000 in
theorem goal11 : pull src11 y1 = y21 := by decide +kernel
abbrev D1 : W → Prop := dif 2 10
set_option maxRecDepth 8000 in
theorem gd1 : D1 y1 ∧ D1 (~~~y1) := by decide +kernel
set_option maxRecDepth 8000 in
theorem gp1 : x1_4 ≠ y1 ∧ x1_4 ≠ ~~~y1 := by decide +kernel
set_option maxRecDepth 8000 in
theorem gn1 : y1 ≠ 0 ∧ y1 ≠ ~~~0 := by decide +kernel
theorem only1 (w : W) (hw : w ∈ A1.toFinset) (hd : D1 w) : w = x1_4 := by
  simp only [A1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide +kernel : ¬ D1 x1_1) hd)
  · exact False.elim ((by decide +kernel : ¬ D1 x1_2) hd)
  · exact False.elim ((by decide +kernel : ¬ D1 x1_3) hd)
  · rfl
  · exact False.elim ((by decide +kernel : ¬ D1 x1_5) hd)
  · exact False.elim ((by decide +kernel : ¬ D1 x1_6) hd)
def src2 : MapRows := [(0, 0x8421084210842108421084210842108421084210842108421084210842108421),
(1, 0x842108421084210842108421084210842108421084210842108421084210842),
(4, 0x1084210842108421084210842108421084210842108421084210842108421084),
(5, 0x1f0000000000003e0000000000007c000000000000f8000000000001f0000000000000000000000000000000000000000000000000000000000000000),
(8, 0x2108421084210842108421084210842108421084210842108421084210842108),
(9, 0x3e0000000000007c000000000000f8000000000001f0000000000003e00000000000000000000000000000000000000000000000000000000000000000),
(12, 0x7c000000000000f8000000000001f0000000000003e0000000000007c000000000000000000000000000000000000000000000000000000000000000000),
(13, 0xf8000000000001f0000000000003e0000000000007c000000000000f80000000000000000000000000000000000000000000000000000000000000000000),
(16, 0x4210842108421084210842108421084210842108421084210842108421084210),
(17, 0x1f0000000000003e0000000000007c000000000000f8000000000001f000000000000000000000000000000000000000000000000000000000000000000000),
(20, 0x3e0000000000007c000000000000f8000000000001f0000000000003e0000000000000000000000000000000000000000000000000000000000000000000000),
(21, 0x7c000000000000f8000000000001f0000000000003e0000000000007c00000000000000000000000000000000000000000000000000000000000000000000000),
(24, 0x8000000000001f0000000000003e0000000000007c000000000000f8000000000000000000000000000000000000000000000000000000000000000000000000),
(25, 0x3e0000000000007c000000000000f8000000000001f00000000000000000000000000000000000000000000000000000000000000000000000000),
(28, 0x7c000000000000f8000000000001f0000000000003e000000000000000000000000000000000000000000000000000000000000000000000000000),
(29, 0xf8000000000001f0000000000003e0000000000007c0000000000000000000000000000000000000000000000000000000000000000000000000000)]
set_option maxRecDepth 8000 in
theorem map2_0_1 : pull src2 x2_1 = (k4inputs.getD 0 0) := by decide +kernel
set_option maxRecDepth 8000 in
theorem map2_0_2 : pull src2 x2_2 = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem map2_0_3 : pull src2 x2_3 = (k4inputs.getD 1 0) := by decide +kernel
set_option maxRecDepth 8000 in
theorem map2_0_5 : pull src2 x2_5 = (k4inputs.getD 2 0) := by decide +kernel
set_option maxRecDepth 8000 in
theorem map2_0_6 : pull src2 x2_6 = (k4inputs.getD 3 0) := by decide +kernel
theorem hav20 (w : W) (hw : w ∈ A2.toFinset) : holds k4inputs.toFinset (pull src2 w) := by
  simp only [A2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨(k4inputs.getD 0 0), by decide +kernel, Or.inl map2_0_1⟩)
  · exact Or.inl map2_0_2
  · exact Or.inr (Or.inr ⟨(k4inputs.getD 1 0), by decide +kernel, Or.inl map2_0_3⟩)
  · exact Or.inr (Or.inr ⟨(k4inputs.getD 2 0), by decide +kernel, Or.inl map2_0_5⟩)
  · exact Or.inr (Or.inr ⟨(k4inputs.getD 3 0), by decide +kernel, Or.inl map2_0_6⟩)
set_option maxRecDepth 8000 in
theorem goal200 : pull src2 y20 = goal := by decide +kernel
set_option maxRecDepth 8000 in
theorem goal201 : pull src2 y21 = goal := by decide +kernel
abbrev D20 : W → Prop := dif 8 10
set_option maxRecDepth 8000 in
theorem gd20 : D20 y20 ∧ D20 (~~~y20) := by decide +kernel
set_option maxRecDepth 8000 in
theorem gp20 : x2_2 ≠ y20 ∧ x2_2 ≠ ~~~y20 := by decide +kernel
set_option maxRecDepth 8000 in
theorem gn20 : y20 ≠ 0 ∧ y20 ≠ ~~~0 := by decide +kernel
theorem only20 (w : W) (hw : w ∈ A2.toFinset) (hd : D20 w) : w = x2_2 := by
  simp only [A2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide +kernel : ¬ D20 x2_1) hd)
  · rfl
  · exact False.elim ((by decide +kernel : ¬ D20 x2_3) hd)
  · exact False.elim ((by decide +kernel : ¬ D20 x2_5) hd)
  · exact False.elim ((by decide +kernel : ¬ D20 x2_6) hd)
abbrev D21 : W → Prop := dif 0 2
set_option maxRecDepth 8000 in
theorem gd21 : D21 y21 ∧ D21 (~~~y21) := by decide +kernel
set_option maxRecDepth 8000 in
theorem gp21 : x2_2 ≠ y21 ∧ x2_2 ≠ ~~~y21 := by decide +kernel
set_option maxRecDepth 8000 in
theorem gn21 : y21 ≠ 0 ∧ y21 ≠ ~~~0 := by decide +kernel
theorem only21 (w : W) (hw : w ∈ A2.toFinset) (hd : D21 w) : w = x2_2 := by
  simp only [A2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide +kernel : ¬ D21 x2_1) hd)
  · rfl
  · exact False.elim ((by decide +kernel : ¬ D21 x2_3) hd)
  · exact False.elim ((by decide +kernel : ¬ D21 x2_5) hd)
  · exact False.elim ((by decide +kernel : ¬ D21 x2_6) hd)
end JData

namespace SevenUpper
open PEqualNP.CircuitLowerBounds

def witness : List Gate :=
  [⟨.or, [5, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [11, 4]⟩, ⟨.and, [12, 8]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [17, 16]⟩]

theorem fits : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem size : witness.length = 12 := rfl

set_option maxRecDepth 100000 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witness, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel
end SevenUpper

namespace JProof
open GThreshold JData PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
theorem terminal : ¬ SignedBuild 6 k4inputs.toFinset goal := by
  rintro (za|oa|ha|hb)
  · exact (by decide +kernel : goal ≠ (0 : W)) za
  · exact (by decide +kernel : goal ≠ ~~~(0 : W)) oa
  · have hit := search_complete (Or.inl rfl) 6 k4inputs (by decide +kernel) ha
    exact Bool.noConfusion (k4exact.symm.trans hit)
  · have hit := search_complete (Or.inr rfl) 6 k4inputs (by decide +kernel) hb
    exact Bool.noConfusion (k4exact.symm.trans hit)

theorem stopped : ¬ SignedBuild 10 A0.toFinset goal := by
  intro h
  have h1 := JElim.elimOne (k := 9) D0 (difops _ _) gd0 only0 gp0 gn0 (pull src0)
      (pops _) (pnot _) map0_0_0 hav00 h
  rw [goal00] at h1
  let ix : Bool → MapRows := fun b => if b then src11 else src10
  have hav (b : Bool) (w : W) (hw : w ∈ A1.toFinset) : holds A2.toFinset (pull (ix b) w) := by
    cases b
    · exact hav10 w hw
    · exact hav11 w hw
  have prop (b : Bool) : pull (ix b) y1 ≠ 0 ∧ pull (ix b) y1 ≠ ~~~0 := by
    cases b
    · change pull src10 y1 ≠ 0 ∧ pull src10 y1 ≠ ~~~0
      rw [goal10]
      exact gn20
    · change pull src11 y1 ≠ 0 ∧ pull src11 y1 ≠ ~~~0
      rw [goal11]
      exact gn21
  obtain ⟨b,h2⟩ := JElim.elimTwo (k := 7) D1 (difops _ _) gd1 only1 gp1 gn1
      (fun b => pull (ix b)) (fun b => pops _) (fun b => pnot _) (fun b => pand _)
      (fun b => por _) map1_0_4 map1_1_4 hav prop h1
  cases b
  · change SignedBuild 7 A2.toFinset (pull src10 y1) at h2
    rw [goal10] at h2
    have hh := JElim.elimOne (k := 6) D20 (difops _ _) gd20 only20 gp20 gn20 (pull src2)
        (pops _) (pnot _) map2_0_2 hav20 h2
    rw [goal200] at hh
    exact terminal hh
  · change SignedBuild 7 A2.toFinset (pull src11 y1) at h2
    rw [goal11] at h2
    have hh := JElim.elimOne (k := 6) D21 (difops _ _) gd21 only21 gp21 gn21 (pull src2)
        (pops _) (pnot _) map2_0_2 hav20 h2
    rw [goal201] at hh
    exact terminal hh

def fn (x : Fin 7 → Bool) := (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) ||
    (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) ||
    (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def input (k : Fin 512) (i : Fin 7) : Bool := (A0.getD i.val 0)[k.val]

set_option maxRecDepth 8000 in
theorem goalAt : ∀ k : Fin 512, fn (input k) = goal[k.val] := by decide +kernel

theorem tableAt (k : Fin 512) : List.ofFn (input k) = A0.map (fun w => w[k.val]) := by
  apply List.ext_getElem (by simp [A0])
  intro i hi hj
  have hlt : i < A0.length := by simpa using hj
  simp only [List.getElem_ofFn, input, List.getElem_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt, Option.getD_some]

theorem lower (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = fn x) :
    11 ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ A0, holds A0.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  obtain ⟨t,ht,run⟩ := compile gs o hg A0 A0.toFinset init (by
    intro k
    change Circuit.eval ⟨gs,o⟩ (A0.map fun w => w[k.val]) = goal[k.val]
    rw [← tableAt, he, goalAt])
  apply stopped
  apply sb_le (k := binaryCost gs) (by omega)
  rcases ht with rfl|rfl
  · exact Or.inr (Or.inr (Or.inl run))
  · exact Or.inr (Or.inr (Or.inr run))

theorem cost_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : binaryCost gs < gs.length := by
  obtain ⟨g,hg,hn⟩ := h
  exact List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [isBinary, hn]⟩

end JProof

namespace JProof
open GThreshold PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
theorem posted_eval : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = fn x := by decide +kernel

end JProof

end PEqualNP.Outside.L_meta_10706_aux

open PEqualNP.Outside.L_meta_10706_aux

open PEqualNP.Outside.L_meta_10706_aux.GThreshold PEqualNP.Outside.L_meta_10706_aux.JProof PEqualNP.CircuitLowerBounds in

theorem PEqualNP.Outside.L_meta_10706 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legalGs _ compute
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · have evaluates : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = fn x :=
      fun x => (compute x).trans (posted_eval x)
    have hb := lower gs o legalGs evaluates
    have hc := cost_lt hn
    refine ⟨SevenUpper.witness, 18, SevenUpper.fits, ?_, SevenUpper.correct⟩
    rw [SevenUpper.size]
    omega
  · refine ⟨gs, o, ?_, Nat.le_refl _, compute⟩
    intro g hg
    have h := legalGs g hg
    exact ⟨h.1.imp_right (fun v => v.resolve_right (fun eq => hn ⟨g,hg,eq⟩)),h.2⟩
