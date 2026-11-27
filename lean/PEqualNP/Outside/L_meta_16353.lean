import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16353_aux

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

end JElim

namespace SevenUpper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def f (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241896 * 2 ^ 32 + 4008225440)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit := ⟨[⟨.and, [3, 4]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [7, 0]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [3, 2]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩

theorem fits : Monotone2 witness := by
  simp [Monotone2,witness]

theorem gate_count : witness.size = 9 := rfl

set_option maxRecDepth 12000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = f x := by
  decide +kernel

theorem upper {s : ℕ} (hs : 9 ≤ s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x :=
  ⟨witness,fits,gate_count ▸ hs,correct⟩

end SevenUpper

namespace Data
open GThreshold
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

def fromWords (words : List ℕ) : W :=
  BitVec.ofNat 512 (words.foldl (fun acc word => acc * 1152921504606846976 + word) 0)

def W0x0 : W := (fromWords [4149467703, 570953291855294195, 283708251021769583, 759661169186020247, 573901046231597312, 45634817834352649, 750148974371147850, 180340248373379673, 589972171812811800])
def W0x1 : W := (fromWords [434922984, 997467257388292509, 1139782191937257177, 539627908239157247, 790764549119619264, 418981282520173098, 396556499742704572, 190278562339173419, 323417640031244862])
def W0x2 : W := (fromWords [1811883613, 454799681153202151, 967167166912869494, 373766958634432623, 67422724636762639, 1638333621290450, 289925041689325057, 74956112310339622, 542244289758907331])
def W0x3 : W := (fromWords [3724860351, 591024014415563852, 693183475116262869, 708750618761647670, 954613326547110922, 383043547606398166, 1762560696215585, 314487907302670752, 379252550614074017])
def W0x4 : W := (fromWords [501990349, 851918126733951279, 32187917538795147, 501507283700780247, 674725972714887531, 588943371537533616, 15521203314000980, 677887287986989376, 614874785644708932])
def W0x5 : W := (fromWords [41235625, 149599941552370750, 1081975984808049789, 694547598720269612, 287296249284608628, 242748640862561925, 595582375147640050, 681690214990378320, 270991668841980385])
def inputs0 : List W := [W0x0, W0x1, W0x2, W0x3, W0x4, W0x5]
def W1x0 : W := (fromWords [4259314678, 864550385866231807, 1080300960345880319, 1152780215718035403, 1071781737689451042, 72484206736097418, 73187905229430800, 433795897796859168, 612525623188984730])
def W1x1 : W := (fromWords [2145570809, 900410961561108156, 528765825293712698, 485174666912592565, 249666640805789725, 75119850223116504, 648201939330319372, 133573773558843395, 118028659286903862])
def W1x3 : W := (fromWords [3221224671, 1120199512413960063, 1147283067226016757, 680001757576683518, 989056611627914384, 15235177813383969, 54942373775410181, 578809499205389010, 391475689536906309])
def W1x4 : W := (fromWords [1123506027, 1078532189851041512, 810109736878316922, 508038706203981631, 534323342137384488, 768155146644096608, 513796172316946872, 128125114331214540, 725562407210167112])
def W1x5 : W := (fromWords [332798525, 245988457959891621, 172349997809806774, 423117720952504996, 1098080494990060644, 201582084887085361, 18133099458385238, 657244594465103246, 12472023064538792])
def inputs1 : List W := [W1x0, W1x1, W1x3, W1x4, W1x5]
def R0 : MapRows := [(2, (fromWords [8, 38654705728, 9007201402224648, 54043195528478720, 299067162787840])),
  (3, (fromWords [72198331526283400, 1125908496777216, 4406770663424, 36029072198860818])),
  (5, (fromWords [35253091565568, 18049582881571844, 2251937252640770, 9077636718658560])),
  (10, (fromWords [512, 281474977759232, 72061992084971520, 36283883978752, 576495945265512704])),
  (13, (fromWords [2185232384, 335806464, 18875648, 21474836608])),
  (15, (fromWords [2080, 262144, 4311744528, 1407443871469568, 34493956616])),
  (16, (fromWords [128, 4503600717895680, 1, 70368744177680, 306244774677970945])),
  (17, (fromWords [17408, 32, 841813590016, 35441868928, 5497558147072])),
  (18, (fromWords [2, 4398046560258, 131072, 432347763251871776, 549755817984])),
  (19, (fromWords [32772, 8590000144, 68719525888, 4503604459208704, 536870944])),
  (21, (fromWords [2252899593748480, 70506191519744, 72620546205941760, 2336462211072])),
  (24, (fromWords [4096, 9007199255265792, 299067162755072, 17609365914176, 140738562097216])),
  (29, (fromWords [1126174793138433, 1099511627776, 576460752303570944, 3386495813566464])),
  (30, (fromWords [16, 562949955518464, 36591782405865472, 8796097216512, 72620546206466052])),
  (40, (fromWords [180152781187842048, 10995122573568, 33554444, 2097152])),
  (41, (fromWords [1, 70368811294720, 583356889232834560, 141287244693505, 1048576])),
  (42, (fromWords [256, 288250304799965188, 135334400, 9007199254740992, 8388608])),
  (43, (fromWords [576460752974513152, 432345564227567776, 8192, 148618787703357440])),
  (47, (fromWords [8256, 18014965445296128, 570425410, 274877972480, 4194304])),
  (258, (fromWords [1073742080, 5629808771860480, 4503603939119112, 144115188344299521, 18577350627164160, 0, 0, 0, 0])),
  (259, (fromWords [70574919385088, 8933532508160, 40536799122030592, 1163558182322176, 0, 0, 0, 0])),
  (260, (fromWords [738230400, 549756862480, 288371199539429376, 9007233615527936, 158329675448320, 0, 0, 0, 0])),
  (261, (fromWords [33554441, 140738293669888, 1181952, 1107558436, 81064931402711040, 0, 0, 0, 0])),
  (271, (fromWords [544, 27021608501641344, 1125899909202946, 288267759563833344, 144123984169402368, 0, 0, 0, 0])),
  (272, (fromWords [2148016128, 16642, 36345456367763969, 576460906922248256, 36030446554906624, 0, 0, 0, 0])),
  (278, (fromWords [4, 72066390131474433, 70680263524484, 18032059423391744, 576742228362264576, 0, 0, 0, 0])),
  (280, (fromWords [65538, 36046389209202752, 578730144336740416, 70368746276106, 12884901888, 0, 0, 0, 0])),
  (281, (fromWords [1314816, 144397763705044992, 9009398345105408, 73183502602338304, 290482175998951424, 0, 0, 0, 0])),
  (282, (fromWords [285214736, 2251799948066820, 18015498025304064, 845799319666816, 4503599694479360, 0, 0, 0, 0])),
  (284, (fromWords [2098176, 288230380446945280, 72620544259784704, 141287781253136, 74835514621952, 0, 0, 0, 0])),
  (292, (fromWords [12713984, 39582460609056, 144119587732979760, 2251799813685760, 17179869184, 0, 0, 0, 0])),
  (304, (fromWords [16448, 577025918462067720, 558354202624, 8798244737024, 34359738368, 0, 0, 0, 0]))]
set_option maxRecDepth 12000 in
theorem R0map0 : pull R0 W0x0 = W1x0 := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0map1 : pull R0 W0x1 = W1x1 := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0map2 : pull R0 W0x2 = 0 := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0map3 : pull R0 W0x3 = W1x3 := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0map4 : pull R0 W0x4 = W1x4 := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0map5 : pull R0 W0x5 = W1x5 := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0goal : pull R0 goal = goal := by decide +kernel
abbrev D0 : W → Prop := dif 18 267
set_option maxRecDepth 12000 in
theorem R0diff : D0 goal ∧ D0 (~~~goal) := by decide +kernel
set_option maxRecDepth 12000 in
theorem R0distinct : W0x2 ≠ goal ∧ W0x2 ≠ ~~~goal := by decide +kernel
set_option maxRecDepth 12000 in
theorem proper : goal ≠ 0 ∧ goal ≠ ~~~(0 : W) := by decide +kernel
theorem R0only (w : W) (hw : w ∈ inputs0.toFinset) (hd : D0 w) : w = W0x2 := by
  simp only [inputs0, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide +kernel : ¬ D0 W0x0) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 W0x1) hd)
  · rfl
  · exact False.elim ((by decide +kernel : ¬ D0 W0x3) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 W0x4) hd)
  · exact False.elim ((by decide +kernel : ¬ D0 W0x5) hd)
theorem R0avail (w : W) (hw : w ∈ inputs0.toFinset) : holds inputs1.toFinset (pull R0 w) := by
  simp only [inputs0, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨W1x0, by decide +kernel, Or.inl R0map0⟩)
  · exact Or.inr (Or.inr ⟨W1x1, by decide +kernel, Or.inl R0map1⟩)
  · exact Or.inl R0map2
  · exact Or.inr (Or.inr ⟨W1x3, by decide +kernel, Or.inl R0map3⟩)
  · exact Or.inr (Or.inr ⟨W1x4, by decide +kernel, Or.inl R0map4⟩)
  · exact Or.inr (Or.inr ⟨W1x5, by decide +kernel, Or.inl R0map5⟩)
end Data

namespace JProof
open GThreshold Data PEqualNP.CircuitLowerBounds
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem exactSearch : search 6 inputs1 = false := by decide +kernel

set_option maxRecDepth 8000 in
theorem terminal : ¬ SignedBuild 6 inputs1.toFinset goal := by
  rintro (za|oa|ha|hb)
  · exact (by decide +kernel : goal ≠ (0 : W)) za
  · exact (by decide +kernel : goal ≠ ~~~(0 : W)) oa
  · have hit := search_complete (Or.inl rfl) 6 inputs1 (by decide +kernel) ha
    exact Bool.noConfusion (exactSearch.symm.trans hit)
  · have hit := search_complete (Or.inr rfl) 6 inputs1 (by decide +kernel) hb
    exact Bool.noConfusion (exactSearch.symm.trans hit)

theorem stopped : ¬ SignedBuild 7 inputs0.toFinset goal := by

  intro h0
  have h1 := JElim.elimOne (k := 6) D0 (difops _ _) R0diff R0only R0distinct proper
    (pull R0) (pops _) (pnot _) R0map2 R0avail h0
  rw [R0goal] at h1
  exact terminal h1

def fn (x : Fin 6 → Bool) := SevenUpper.f x

def input (k : Fin 512) (i : Fin 6) : Bool := (inputs0.getD i.val 0)[k.val]

set_option maxRecDepth 8000 in
theorem goalAt : ∀ k : Fin 512, fn (input k) = goal[k.val] := by decide +kernel

theorem tableAt (k : Fin 512) : List.ofFn (input k) = inputs0.map (fun w => w[k.val]) := by
  apply List.ext_getElem (by simp [inputs0])
  intro i hi hj
  have hlt : i < inputs0.length := by simpa using hj
  simp only [List.getElem_ofFn, input, List.getElem_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt, Option.getD_some]

theorem lower (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = fn x) :
    8 ≤ binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs0, holds inputs0.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs0 inputs0.toFinset init (by
    intro k
    change Circuit.eval ⟨gs,o⟩ (inputs0.map fun w => w[k.val]) = goal[k.val]
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
end PEqualNP.Outside.L_meta_16353_aux

open PEqualNP.Outside.L_meta_16353_aux PEqualNP.Outside.L_meta_16353_aux.GThreshold PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_16353 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4008225440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4008225440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s model
  obtain ⟨C, fs, sz, he⟩ := model
  have lg (g : Gate) (hg : g ∈ C.gates) : legal g := by
    simpa only [legal,Set.mem_insert_iff,Set.mem_singleton_iff] using fs g hg
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · refine ⟨SevenUpper.witness, SevenUpper.fits, ?_, SevenUpper.correct⟩
    rw [SevenUpper.gate_count]
    have bound := JProof.lower C.gates C.output lg he
    have smaller := JProof.cost_lt hn
    change C.gates.length ≤ s at sz
    omega
  · refine ⟨C, ?_, sz, he⟩
    intro g hg
    have ok := lg g hg
    rcases ok.1 with h|h|h
    · simpa [h] using ok.2
    · simpa [h] using ok.2
    · exact False.elim (hn ⟨g,hg,h⟩)
