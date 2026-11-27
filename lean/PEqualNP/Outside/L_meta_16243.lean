import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16243

namespace Signed

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 274
-- Free complementation leaves four binary choices up to output polarity.
def norm (x : W) : W := if x.getLsbD 105 then ~~~x else x

theorem norm_or (w : W) : w = norm w ∨ w = ~~~(norm w) := by
  unfold norm
  split <;> simp

def rawOps (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def ops (x y : W) : List W := (rawOps x y).map norm
def sep (x : W) : BitVec 105 := ((x >>> 105) ^^^ x).setWidth 105
def cuts (ws : List W) : BitVec 105 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (~~~(0xfffffffc00000000 : BitVec 64)) ++ (-1 : BitVec 105) ++ (0 : BitVec 105)
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

def differs (i : Fin 105) (w : W) : Prop :=
  w.getLsbD (105+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 105) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  have hnorm : differs i (norm q) ↔ differs i q := by
    unfold norm differs
    split <;> simp [show 105+i.val < 274 by omega, show i.val < 274 by omega]
  have hd := hnorm.mp hd
  simp only [rawOps, List.mem_cons, List.not_mem_nil, or_false] at hq
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 105+i.val < 274 := by omega
  have hi' : i.val < 274 := by omega
  rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 105) :
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
  change (cuts ws)[j] = (BitVec.allOnes 105)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, rawOps, List.mem_toFinset, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false]
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
  ((ops a b).filter (fun w => !(a::b::r).contains w)).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hfresh : z ∉ a::b::r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_filter.mpr ⟨List.mem_toFinset.mp hz, ?_⟩, ?_⟩
  · simpa using hfresh
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
        have hnew : z ∉ a::b::r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hnew hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

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
  · change reachable av (BitVec.allOnes 274 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 274)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ rawOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z := by
    have used : norm w ∈ basicOps a b := List.mem_toFinset.mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
    refine .inr ⟨a,ha,b,hb,h,norm w,used,.inr (.inr ⟨norm w,Finset.mem_insert_self ..,?_⟩)⟩
    rcases hz with rfl | rfl
    · exact norm_or _
    · rcases norm_or w with eq | eq
      · exact .inr (congrArg (fun i => ~~~i) eq)
      · exact .inl (by simpa only [BitVec.not_not] using congrArg (fun i => ~~~i) eq)
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [rawOps] : a &&& b ∈ rawOps a b) _ (.inl rfl)
  · exact add _ (by simp [rawOps] : a &&& ~~~b ∈ rawOps a b) _ (.inl rfl)
  · exact add _ (by simp [rawOps] : b &&& ~~~a ∈ rawOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [rawOps] : a ||| b ∈ rawOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 274) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 274) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 274) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#274)[k.val] = false; simp
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1 && x 2) || (x 0 && x 3) || (x 0 && x 2 && x 4) || (x 1 && x 2 && x 4) || (x 0 && x 2 && x 5) || (x 1 && x 2 && x 5) || (x 1 && x 3 && x 4 && x 5)

def insertWire (w : W) : List W → List W
  | [] => [w]
  | x::xs => if (w.toNat >>> 210) ≤ (x.toNat >>> 210) then w::x::xs else x::insertWire w xs

def sortBank : List W → List W
  | [] => []
  | w::ws => insertWire w (sortBank ws)

theorem insertWire_perm (w : W) (ws : List W) : (insertWire w ws).Perm (w::ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    unfold insertWire
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap ..)

theorem sortBank_perm (ws : List W) : (sortBank ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons w ws ih => exact (insertWire_perm w (sortBank ws)).trans (ih.cons w)

theorem sortBank_finset (ws : List W) : (sortBank ws).toFinset = ws.toFinset := by
  ext w
  simpa only [List.mem_toFinset] using (sortBank_perm ws).mem_iff (a := w)

theorem sortBank_nodup {ws : List W} (h : ws.Nodup) : (sortBank ws).Nodup :=
  (sortBank_perm ws).nodup_iff.mpr h

abbrev Mark := W × BitVec 105

def mark (w : W) : Mark := (w,sep w)

def markedCuts (ws : List Mark) : BitVec 105 := ws.foldr (fun w v => w.2 ||| v) 0

lemma markedCuts_eq (ws : List W) : markedCuts (ws.map mark) = cuts ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [markedCuts,cuts,mark] using congrArg (sep w ||| ·) ih

lemma unmark (ws : List W) : (ws.map mark).map Prod.fst = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [mark,ih]

lemma singles_map_eq {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a,r) => (f a,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [singles,ih,List.map_map,Function.comp_def]

lemma pairs_map_eq {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,r) => (f a,f b,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [pairs,ih,singles_map_eq,List.map_map,Function.comp_def]

def cachedSearch : ℕ → List Mark → Bool
  | 0, ws => (ws.map Prod.fst == [goal] || ws.map Prod.fst == [~~~goal])
  | t+1, ws => (ws.map Prod.fst == [goal] || ws.map Prod.fst == [~~~goal]) ||
      (pairs ws).any (fun (a,b,r) =>
        let base := markedCuts r
        let old := a.1 :: b.1 :: r.map Prod.fst
        ((ops a.1 b.1).filter (fun z => !old.contains z)).any fun z =>
          (sep z ||| base == -1) && cachedSearch t (mark z :: r))

lemma cachedSearch_eq (t : ℕ) (ws : List W) : cachedSearch t (ws.map mark) = optimized t 0 ws := by
  induction t generalizing ws with
  | zero => simp only [cachedSearch,optimized,unmark]
  | succ k ih =>
    simp only [cachedSearch,optimized,unmark,pairs_map_eq,List.any_map,Function.comp_def]
    congr 1
    apply List.any_congr rfl
    intro s
    obtain ⟨a,b,r⟩ := s
    simp only [mark,markedCuts_eq,dispatch]
    apply List.any_congr rfl
    intro z
    have same : cachedSearch k ((z,sep z)::r.map mark) = optimized k 0 (z::r) := ih (z::r)
    rw [same]
    simp

def allowedNext (table : ℕ → List W → Bool) (t : ℕ) (ws : List W) : Bool :=
  if t = 0 then ws == [goal] || ws == [~~~goal] else !table t (sortBank ws)

def closedState (table : ℕ → List W → Bool) : ℕ → List W → Bool
  | 0, _ => false
  | k+1, ws =>
    !(ws == [goal] || ws == [~~~goal] ||
      (pairs ws).any (fun (a,b,r) =>
        dispatch (k+2-ws.length) (fun _ => allowedNext table k) a b r))

theorem closed_sound (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    {g : W} (hg : g = goal ∨ g = ~~~goal) :
    ∀ t ws, ws.Nodup → live basicOps g t ws.toFinset → table t ws = false := by
  intro t
  induction t with
  | zero =>
    intro ws _ _
    cases ht : table 0 ws
    · rfl
    · have bad := closure 0 ws ht
      simp [closedState] at bad
  | succ k ih =>
    intro ws nd running
    cases current : table (k+1) ws
    · rfl
    · have blocked := closure _ _ current
      rcases first_live running with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
      · rcases hg with rfl | rfl <;> simp [closedState,singleton_list nd done] at blocked
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have attempt {a b : W} (perm : ws.Perm (a::b::r))
            (hs : ws.toFinset = insert a (insert b needed)) (hz : z ∈ basicOps a b) :
            dispatch (k+2-ws.length) (fun _ => allowedNext table k) a b r = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm nd hs
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hs]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (hfin ▸ List.mem_toFinset.mpr hu))
          have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
          have hl : live basicOps g k (z::kept).toFinset := by simpa [hfin] using tail
          have q := live_card hl
          rw [List.toFinset_card_of_nodup hnd,List.length_cons] at q
          have q' := live_card running
          rw [List.toFinset_card_of_nodup nd] at q'
          have len := perm.length_eq
          simp only [List.length_cons] at len
          have hnew : z ∉ a::b::r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
          apply dispatch_complete (k := k) (extra := k+2-ws.length)
            (fun _ => allowedNext table k) hz hnew hk (by omega) (by omega) (cuts_full hg hl)
          by_cases done : k = 0
          · subst k
            rcases hg with rfl | rfl <;> simp [allowedNext,singleton_list hnd hl]
          · have cold := ih _ (sortBank_nodup hnd) ((sortBank_finset _).symm ▸ hl)
            simp [allowedNext,done,cold]
        have branch : (pairs ws).any (fun (a,b,r) =>
            dispatch (k+2-ws.length) (fun _ => allowedNext table k) a b r) = true := by
          apply List.any_eq_true.mpr
          rcases hm with direct | swap
          · exact ⟨(a,b,r),direct,attempt hp hs hz⟩
          · exact ⟨(b,a,r),swap,attempt (hp.trans (.swap _ _ _))
              (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
        simp [closedState,branch] at blocked

def rootClosed (table : ℕ → List W → Bool) (cap : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.all fun ws => !(decide (ws.length ≤ cap+1) &&
    (cuts ws == -1) && allowedNext table cap ws)

theorem rootClosed_sound (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    {g : W} (hg : g = goal ∨ g = ~~~goal) (cap : ℕ) (inputs : List W)
    (nd : inputs.Nodup) (root : rootClosed table cap inputs = true) :
    ¬ build basicOps g cap inputs.toFinset := by
  intro run
  classical
  obtain ⟨s,hs,hl⟩ := compress run
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hn := nd.filter (· ∈ s)
  have hl' : live basicOps g cap ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hn] at sz
  have fits : allowedNext table cap ws = true := by
    by_cases done : cap = 0
    · subst cap
      change ws.toFinset = {g} at hl'
      have only : ws = [g] := singleton_list (ws := ws) hn hl'
      rw [only]
      rcases hg with rfl | rfl <;> simp [allowedNext]
    · have cold := closed_sound table closure hg cap (sortBank ws) (sortBank_nodup hn)
        ((sortBank_finset ws).symm ▸ hl')
      simp [allowedNext,done,cold]
  unfold rootClosed at root
  have bad := List.all_eq_true.mp root ws (List.mem_sublists.mpr (List.filter_sublist ..))
  change ws.length ≤ cap + 1 at sz
  simp [sz,cuts_full hg hl',fits] at bad

def rows : List W := [0x2db7b7bf1414140a91050387a48830c00f8648b3098c889ffffa47f9e85fa33e59c6f,
0x36dadad5189899530226fbf804f95cf60cf89d48f193777dfdd7f8b67fae5ccfb679d,
0x38fcfcf9a121219c2c58e05fdb370301f17120b6d24ffff3ffbdbb2f87f93cf45bf9b,
0x3f1f1f1ec1c1c1e020e0fc60100183260061970c6450401e006afcd1fb07f3cbe6366,
0x3fe01fe0fe01fe0038ff0a801bc21d58008b67402f18ffa00689e90a1d3255b3ac1f8,
0x3fffe000fffe00003f1013001e041e98008cb24d0f1f80c00b0e120c1ec44e59a7a78]

inductive PackedBlocks where
  | leaf (index value : ℕ)
  | fork (index pivot : ℕ) (left right : PackedBlocks)

def PackedBlocks.byIndex : PackedBlocks → ℕ → ℕ
  | .leaf _ value, _ => value
  | .fork middle _ left right, i =>
    if i < middle then left.byIndex i else right.byIndex i

def PackedBlocks.byKey : PackedBlocks → ℕ → ℕ × ℕ
  | .leaf index value, _ => (index,value)
  | .fork _ pivot left right, k =>
    if k < pivot then left.byKey k else right.byKey k

structure PackedSeq where
  size : ℕ
  width : ℕ
  mask : ℕ
  blocks : PackedBlocks

def PackedSeq.inBlock (xs : PackedSeq) (b i : ℕ) : ℕ :=
  (b >>> (i * xs.width)) &&& xs.mask

def PackedSeq.at (xs : PackedSeq) (i : ℕ) : Option ℕ :=
  if i < xs.size then some (xs.inBlock (xs.blocks.byIndex (i / 32)) (i % 32)) else none

theorem PackedSeq.at_bound {xs : PackedSeq} {i key : ℕ} (h : xs.at i = some key) : i < xs.size := by
  by_contra bad
  simp [PackedSeq.at,bad] at h

def searchBlock (xs : PackedSeq) (value key : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | n+1, lo, hi =>
    if lo < hi then
      let i := (lo+hi)/2
      let x := xs.inBlock value i
      if x = key then i
      else if x < key then searchBlock xs value key n (i+1) hi
      else searchBlock xs value key n lo i
    else lo

def findKey (xs : PackedSeq) (key : ℕ) : Option ℕ :=
  let (j,value) := xs.blocks.byKey key
  let bound := min 32 (xs.size - 32*j)
  let i := 32*j + searchBlock xs value key 6 0 bound
  if xs.at i = some key then some i else none

theorem findKey_sound (xs : PackedSeq) (key i : ℕ) (h : findKey xs key = some i) : xs.at i = some key := by
  unfold findKey at h
  rcases selection : xs.blocks.byKey key with ⟨j,value⟩
  rw [selection] at h
  let k := 32 * j + searchBlock xs value key 6 0 (min 32 (xs.size - 32 * j))
  change (if xs.at k = some key then some k else none) = some i at h
  by_cases found : xs.at k = some key
  · rw [if_pos found] at h
    exact (Option.some.inj h) ▸ found
  · rw [if_neg found] at h
    cases h

def encodeBank (dict : PackedSeq) : List W → Option ℕ
  | [] => some 0
  | w::ws => do
    let i ← findKey dict (w.toNat >>> 210)
    let tail ← encodeBank dict ws
    return 4096 * tail + i + 1

set_option maxRecDepth 16000 in
def expanded : PackedSeq := ⟨1260, 274, 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, .fork 20 0x36dadbd51898df5302a7fbf804f95cf60cfadd48f193777dfdd7f8b67fae5dcfb679d (
.fork 10 0xd37a73f1414140a91050387a48830c00f8648b3098c889ffb7a47f9e85fa33e59c67 (
.fork 5 0xc0c0c10000001000000018003000000010000090033761fd95002604a80c0410499 (
.fork 2 0x1fff0001359e804de0dfe1bb2141ff7348b2d0c07f3ff4f1edf3e13bb1a658587 (
.fork 1 0x17a00000140000050080008000400002400000000800048041000012012208000 (
.leaf 0 0x5c78000000000000000000000000000000000000007801811347800e84090001800014b9000000080000000780000000010000b200000813f4b00121801920245840300004a540000400800100200022001003000200002000077d34102c1802800184101400008400001ea0000ea08000142010000010500200077200001a802012010800018000002100000486500123816104cc0407c1c400034101dc800006a00804804200006000000840000089510022e8780071402600700500f00077200001a802012010800018000002000000707800383b1800006049801841401810100000002a0000400420000400000052a0000040880010007a0002000030240b200000802002005418011a1204800200001480000598000324000004080400000d000000002000000004000040048020000000050a000140a000c00400000081000001000000400002002004418001a10040002000010a0000482300120001f04080407c40402c80100200800800406004480812000800003060000c06000a00c2000008026000005002000000c004044d0600281020000400000c180000500a0014020082208100380920000200003001011341800a04080001000003000000de0000a7088000c000400002450020000000000040000002010200000000008100002610c0098228003210198300034008200003001010241800800080001000000e10000201c0008001fc1320001f11000b290003f21f49101220038002418481000003800000f800003c020007080100000900000000fc801204040800c000802020000000c1000018130006009800f840400c10080090803721f49100220028000410481000002840000502a0014021e822081003c0922c802002007d24004800060009061004000001f0000000a80000007a00820000f0008b20080001ff07004f1e009a0045040700000078000007800003918000060098018000010100007801801347800680010001800000190000019c0000e05fc0310001f17000b2d0400013f03000218009200450403000000540000054c000381e000e5009831c0200342000077c14002c180200010410140000000e36200002c1000001a04020800002204060000000000000000000000000000000000388058800a36000006c08042000048800180000000000000000000000000000000000c14140a020c004001000830000010204044000000000000000000000000000000000284848210b16000016c180c07c00480100900000000000000000000000000000000001e1e00001300030004001c98008c0041090000000000000000000000000000000000078007800401c0a000300716002290100240000000000000000000000000000000000181818030206038004c85cd00c88084001800000000000000000000000000000000005050500a44140e009220c3003a1920042600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (
.leaf 1 0x7ffc0002756e009fa3fe83e581983dc936cbc201fcffd3c7b7cf84eec6996161c0001ffe0001ffe000efece001c381660063450060407f3e04e1edd3e133b1a24818600007ff40007ff7c03bfa3ff07ed059ff5cd36cbc301fcffd3c7a6cf84ecc6996161c0001ff90001ff9c00efe8dfc1f30141f17345b2f0407f33f4b1e923813b31a65858300007fe40007867003a3a17f04cc0407c5c416cbc101fccfd2c7a48e04ecc6996160c0001ff50001ff5300efe8f801fb41660c734d00f0807f3df4d1e9b2613a11a61858500007f800007f80003bc220007080500000d14008001fc801207a40804c84688206000001fdf0001d9f300e6ecf800f9c1660c710d00f0c0773ff4f1ecf3e12bb1865058700007efc000757aa0397b39e822685983d8d36c98301207fd3c3b7c7846ec6996141c0001f1f0001c1fc00e0ec7fc0318127f17105b2f040401ff070ecf1e10bb1865050700007c78000707800383b1800006049801841401810100780183b347840ec609004180001f000001c00000e008000000010000010500200040000000e800010211820010000007bf40006e77c01bba3ff07ed059ff5c436cbc301fcffd3c7a6cf84ecc2996161c0001efd0001a1dc0068e87fc1330127f17105b2f0407f3ff4f1e9b3e13b30a65858700007bf40002656c009ba3fe03e5019835c036cbc201fcffd3c7a6cf84ecc2996161c0001ef90001b99c006ee8dfc1f30141f17105b2f0407f33f4b1e923813b30a658583000073e40007ae7003aba17f05cc0407c5c416cbc101fccfd2c6a48e04e4c2916160c0001cf90001e1fc00e8ec7fc1338127f17105b2f0407f33f4b1a923813930a458583000073e40006a77401aba1ff05cd049fc5c416cbc101fccfd2c6a48e04e4c2916160c0001cf90001219c0048e05fc1330101f17100b2d0407f33f4b1a923813930a45858300007380000480000120000004080400000400000001fc801206a40804c04280206000001c18000101800040e0400001010000610000404040120020a801810130804010200006bd40002e57c00bba3ff07ed019ff5c036cbc201fcf7d347a6c984e84298616140001af500009d5b8027e8ffa0f960660f724db2f0807f3df4d1e9b2613a10a61858500006b7c0002656e009ba3fe83e581983dc036cbc201dcffd3c7b3cf84aec2194161c0001add000099df0026e8ffc0f94067fd700db2f0c0773ff4f1e8b3e12b30865058700006b540002654c009ba3e003e5019831c03403c201dcf7d347a2c984a84218416140001ac0000098000026088000c0004000000500200077200481e802012210820018000006850000205000083a1800004009801801401800100700103a241840842080041000018d1000001100000e0580031000000700000d0007731f491a822012810841058100005efc0000502a0014021e822081003c0922c80200207fd3c117c7806e84996101c00017a00000140000050080008000400002400000000800048041000012012208000)) (
.fork 3 0x18c011000001100000e0580031000000700000d0030051f91410240288084412601 (
.leaf 2 0x5edefc0050502a0414061e922083003c1922cc0210207ff7c91fc7817e8cb96701c017a01f0014000a81000107a40820800f0408b30084001ff97206f1e04da20c51c07005e80000050000004000400100002000010000400100000240808000110082006000017001e000000000000000000000000000000000000001e006204d1e005a2084000600528064000000200000001e00000000040002c80010004fe4c00886012480114700c01280150010000200000100040800800c0008000080001df95200b0600c000c104050021000007a80000180040000010080000024030000c0100001040100a002100088000084000012001940400e05840350201f0700004d043004000041004028008400220000210000022005440803c1e000c5009801c24023400c0100001040100a00210008800008000001c001e00000f460000182260060900c4040000000001000020000400220000148028001000220400001e800080000c1002cc001000080080190601068801060080052000016600000500000000040200000400050004000000000200004002000180000140028050002800000100000020800000000100100000800801106000688010000800420080120008c04000007c0040201f10000b600440002002002018041200041802000c0018030001800000508000020098000240200000003001081341801208200001000300060014000281000100240820800e0408010080000c004204d06004820800004000c0000037800000c00440010000200001240240000000000080000001008200000000200040098004302001120040840a60c0098080080000c00420090600400080000400038004008000701000007f00d00007c44002ca401c0107e45008900320201047004000e000003e0000070001000404008000040001000700400904020400c0080001800000300040060004c0800046010e1020030402002420c0107e45000900220201041004000a0010014000a81000107a40820800f0408b300840001f91002200048000411c0100007ffc0007fff003bfb3ff07ce059fc5cd16cbc101fcffd3c7b7cf84eec6996161c0001fff0001ff9e80efe8dfe1fb2141ff734db2f0c07f3ff4f1edf3e13bb1a65858700007ffc0007fd6e03bfa3fe87ed85983dcd36cbc201fcffd3c7b7cf84eec6996161c0001fff0001fe0a80ef0887a1ca21400f034db220807f3ff4f1edf3e13bb1a65858700007ffc0007e7fc03bbb3ff07ef059ff5c436cbc301fcffd3c7b7cf84eec6996161c0001fff0001f5fe80edecffe1bba167ff734db2f0c07f3ff4f1edf3e13bb1a65858700007ffc000787f003a3b1ff04ce049fc5c416cbc101fcffd3c7b7cf84eec6996161c0001fff0001ddfb80e7ecffa0f9e1660f734db2f0c07f3ff4f1edf3e13bb1a65858700007ffc0006f77e01bfa3ff87ed859ffdcd36cbc301fcffd3c7b7cf84eec6996161c0001fff0001359e804de0dfe1bb2141ff7348b2d0c07f3ff4f1edf3e13bb1a658587) (
.fork 4 0x1fe01f009c015b8300f17fa43960a60f7498bbd087005ff97616f5e2cdaa4c53e07 (
.leaf 3 0x7f807807f807801c03d58010160a9801924035011c017825985b578b16a9210e81801fe01d01fe01df0700f17fc43d42a7fd7498bfd0c7005ff97612b5e2cd2a4c53e07007f806407f806701c03c57f10d40a07c5d242ff411c014fe4d848960b34a9314f80c01fe01901e0019c0400f05fc0350201f17090bed0470053f936122582cd2a4c53e03007f805407f8054c1c03c5e010f50a9831d26037421c0177e5584ad18b3029304f81401fe00001fe000007001100040402800004900d000700400906120402c40a4803a00007f007c076007cc0803d5e010e70a9831c26033430c017fe5d853d78a36a9314981c01fa01f01d401ea8100f567a409a2a60f6498bf40c4001ff97216f1e24da24c53e07007c7c78070707800383f18000060c980186543181010078018bf3478c1ecf2908c1801f001f01c001fc0000f47fc0318227f17090bed040001ff07214f1e20da24c52607007c0078070007800003d18000060898018240310100007801885347881689210881801f000001c0000000001000000002000000900c00000000000210000204024802200007b807406e0077c1803c5ff10f50a9ff5c262fb431c017fe5d84ad78b34a1314f81c01ee01d01a001dc0400f07fc0350227f17090bed047005ff97612b5e2cd284c53e07007b80740260056c0803c5fe10e5029835c262eb421c017fe5d84ad78b34a1314f81c01ee01901b8019c0600f15fc4350281f17090bed0470053f936122582cd284c53e030073f3e4048486701123817f04dc0c07c5c402db411dfdcff6d6ec9e0fe4e3916fe0c01ce01901ea019c0600f05fc0350201f17090bed0470053f934122582c9284453e0300738064078007f01003d1ff00d6089fc5c242fb411c014fe4d048960b24a1114f80c01ce01901a801dd0600f07fc0354227f17090bed0470053f934122582c9284453e0300738064048006701003817f00d40807c5c002db411c014fe4d048960b24a1114f80c01ce00001200000040000000004020000000004000700400904120402c0084003a0000700060040006000003810000040800018000110100004800804006080481010880801ae01500b8015f0600f17fc43d40a7fd7098bad087005df95612b462cc084c13e05006b80540270056e0c03c5fe90e582983dd262ef421c0177e5584ad18b3021304f81401adad5009899530226f9f804f940e60c709d08f083777dfdd7f8b663ae18ce12785006b007c0260056e0803c5fe90e582983dc262eb420c017fe5d853d78a36a1314981c01ac01d009801df0200f17fc43940a7fd7098bad0c3005ff97610b5e28d284c52607006b00540260054c0803c5e010e5029831c26023420c0177e55842d18a3021304981401ac000009800000200110004000080000090080003004009061004028408480220000680050020005000003c180000400980182402100000070010842418810012008810018c011000001100000e0580031000000700000d0030051f91410240288084412601) (
.leaf 4 0x30300006060000008000c001000724002200100040c01002410001012003000000600c000c0180018000006028000c01c50008800400100372004810002042004000009802de82fc5050502a44140e1e9220c3003e1922cc2632227fffc81fe7817688f16703c0a0b7bf1414140a91050387a48830c00f8648b3098c889ffff047f9e05ba13659c0f028282847878502a4c140e1e9220f3603e3923cc26322207fe400ca0016000d0670240a0a0a11e141e0a91070387a4c83cd80f8e48f3098c8881ff9003280058003419c09028282847070702e4c1c0e1e9321f3403e3923cc26322207fe400ca0016000d0670240a0a0a11414140a91050387a48830c00f8648b3098c8881ff9003280058003419c0902828284000000200000001e00000000040002c800322207fe400ca0016000d0670240a0a00014140000110003000400108000840001090c80800b0002080040001001808028002805000500040140a000200410002090000242222001a000420004000c02002008080811010100200040380048810c00c80080001800001fd90002000080004104090101010080808050306000612cd80007c0408002480cdd800014001812803000002400404040080808110202001800704c1000180040900337600005000604a00c000009001010000a8a80000384000002810306000208100080c010000100010120030000004004000402a002a00081a00000b420c18000820400200372000010002042004000009000808080808080303060001f2c180007c40082c80832220008000c20014000c02600002020200404040891010007a0002000030640b3080c8880020003080050003009800008080009898000074400000281000200010800428320200080008200100004006000020002026002600181900000b020008000260000a088880020001080010003008000007fff8007fff8001fbc660017180f00001f5434801dfd80361fec180fd86fa82ee0001fe01f01fe01fc0700f57fc43582a7f17490bfd047005ff97616f5e2cdaa4c53e07007f807c07f8067a1c03c57f90f48a07fdd262ff431c017fe5d85bd78b36a9314f81c01fe01f01fe015b8700f17fa43d62a60f7498bfd087005ff97616f5e2cdaa4c53e07007f807c07f8002a1c00441e90308a003c1262fc021c017fe5d85bd78b36a9314f81c01fe01f01f801ff0600f57fc43dc2a7fd7098bed0c7005ff97616f5e2cdaa4c53e07007f807c07d007fa1403d5ff90f68a9ffdd262ff431c017fe5d85bd78b36a9314f81c01fe01f01e001fc0400f47fc0358227f17090bed047005ff97616f5e2cdaa4c53e07007f807c077007ee0c03d5fe90e78a983dd262ff431c017fe5d85bd78b36a9314f81c01fe01f01bc01df8700f17fe43d62a7ff7498bfd0c7005ff97616f5e2cdaa4c53e07007f807c04d0067a1403857f90f48a07fdd022df431c017fe5d85bd78b36a9314f81c01fe01f009c015b8300f17fa43960a60f7498bbd087005ff97616f5e2cdaa4c53e07)))) (
.fork 7 0x70000005e0000001000020000001c18008802400d1000000000000018004001a4060 (
.fork 6 0xfce0f92120219c0c18e05fcb370201f17020b6d24fbff3ffb5132f86f92c745be9b (
.leaf 5 0x383fc78f8ff07807fc3bd80381676f803b49505ad3f03782d93bb77970ef649064780e0fcf92021219c0c58e05fcb370101f17120b2d24ffff3ffb5ab2f85f93cb459d9b03838384f8f8f82a7c7c0e1ebf38f3603e39a3cc2e3eff87fe540cb813e030d0672640e0e0e13e3e341e9f1d039fefbe3cd9ff9e68f39b8fbfe1ff95032e04f80c3419c9903838384f8f880707c600c7f3cd87267c67083ce6c3eff87fe540cb813e030d0672640e0e0e13e3e1c1b9f17039faefc7cd80f9e68f39b8fbfe1ff95032e04f80c3419c9903838384f8d0f87a747c0e7fbff8f367fe79a3ce6e3eff87fe540cb813e030d0672640e0e0e13e203e1c1c1f029fcbf61c59f19a60f29b0fbfe1ff95032e04f80c3419c9903838384f870f86e6c7c0e7ebfe9f3603e79a3ce6e3eff87fe540cb813e030d0672640e0e0e13c3c3c1f9f1f039feffe7cd1ff9e68f39b8fbfe1ff95032e04f80c3419c9903838384e0e0e07c38780e7f3ff97347f660a3ca4e3eff87fe540cb813e030d0672640e0e0e13434341e9d1d039fefbe30c1ff9668b39b8fbfe1ff95032e04f80c3419c9903838384808080703060007f2cd80007c44082ca483eff87fe540cb813e030d0672640e0e0e11c1c1c1b9307039fa4f87cd00f9e48f3998fbfe1ff95032e04f80c3419c9903838380f8f8f8007c7c0e003f187360023981042c3eff803e140c3813c030c0262600e0e0c13e3e18131f1603980efc5cd80c9c28419b8fb7e1ff95022e04e80c1411c9903838284f8f8502a7c540e1eba30f3603e39a3cc2e3e2307fe500cb0136030d0670640e0e0a11c1c140a93050387a4883cd00f8e48f3098f88c1ff94032c04d80c3419c1903838000f8f800007c400c0038107260023081042c3e03002c10083013003040060600e0e000202000000c1000000a04000000002000020f80c00b04020c04c00c100181803830384f860f84c687c0e603fe973603269a1026e2eff87fe5404b812e030d0612640e0a0e13e143e0a991f0387afca3cd80f8e68f30b8cbfa1ff91032a0478043419c99038283847050702a441c0e1e9320f3403e3923cc2632fe87fe440ca811e010d0672640e0a0a13e14140a99150387ae883cd80f8e68f30b8c8881ff9003280458043419c1903807f80f807f80063fc2a002f087560022d9500ac23fe801a07a42814c856c8206600e000e03e003e00181f02800bc21c58008a60400b08bfa00681010a04300430080980380038080008000206000002c080000000080000822fe801a04042810c010c0202600e000003e000000181002000a001c18008820400b088080020000080400041000018036b03546260654c081bcfe013e573d833e26123460cddf7f75c42d99ab0313049a740c0dad5181899530226ebf804f95cf60cf80d40f183777dfdd5e8b665aa1c861059d030303046060604c08180e6013e1734032602102460cdd87f654009812a03010412640c0c0c10000001000000018003000000010000090033761fd95002604a80c0410499) (
.leaf 6 0x1b0b0b146262614c08986ee013e173d832627522c64cddb7f75d02d9f2b9303ed127461fe00019fe00000700130004041e90008c904d01170040090612041ac44a49a7a00186b08546262654c089befe013e573d833e27523c64c0177e55942d1ea39213ed98146021ad5189899530226fbf804f95cf60cf89d48f190773df4d3e8b2792e508fb4585180808107272710e4c9c6e809321f3d83a3b7524a640003001090241e019002e9001060202041898984302261ba004c85cf60c889d482190000c004240907806400ba400418080810020201000080608000000098000254208040003001090241e019002e900106020000189800000200130004001c9000889048011000000002000018044009a400018007f806007f80003bc2a0007087540022d15008441fc801207a40864c9468eb060060002001800980000260a8000c01c5000880540211000000000400018024003a4000168e8e9c5050502a44140e1e9220c3003e1922cc26322237ff491fe1a17a0cf8671b4517a31f1414140a91050387a48830c00f8648b30984001ff97246f1e84fa30e51c67140c5efc5050502a44140e1e9220c3003e1922cc2600207fd3c917c7a07e8cb96119c50303061414140291050380248830c00e8648010980000c004244d06806830a00064140c0c18000000000000000000000000000000000000003001091341a01a0c28001905030000141400001100030004001080008400010900000000020000080402080006014000c005000500040140a0002004100020900002400000000010000200804080018040202041010100200040380048810c00c8008000180000c004240906806000a00004087f80012ff800001c00440010103a6000324934105c0100241848104b1129269e8002001fe04a01fe0000ef088001c20d58000b474024107f200481e902113251a3ac180080000012b2800000800400000003060002249201040000000000000400100069000020000004a00ca0000a2080000400c1800080740241000000000000010004001a40000800000103030180028070800002009800025c20904000000000000040010006900002000000088888410222182000404c3600089548201000000000000010004001a40000404040901010080020010000002000000000800100000000000110000020c0000180101010204040400910100002000200002064001080000000000044000008300000600404000119180000440000000000002000100804300000000000000000000800001801000100460046001081000000000008000242000c00000000000000000001000006003ff8000fff800007c404c0038107a600232c1342c3e03002c1848301b1039600e8600ff00fe3fc03fe0181ff6e00bc39e7e00eaf04c4b48bfbe06e315dbe635a6784a29e03f3f3e4848486703163817f2cdc0c07c5c482db493fffcffed6ecbe1fe4f3d16fe6c0fce0f92120219c0c18e05fcb370201f17020b6d24fbff3ffb5132f86f92c745be9b)) (
.fork 8 0x71f1f1e41c1c1e000e0fc60000183260061970c6450401e0062fcd1fb07f3cbe6366 (
.leaf 7 0x1c7c0c79070307800283f1800006089801825c319140007801895347e81f8d2f9899871ce3195f20df9c14a7eadfc0f51e59f1fa47f6fd570053f93452259acb6947f7e631c5c0c7903030180028070800002009800025c209040007801891347e01f8c2f90198707030e41c0c0e000a01c20000082260000970c2450000e006244d1f807e30be40661c0c7c79030707800383f1800006049801865c2191410078018bb347e41fce2f905987031cf95edf219c1348f35fc5331d99f1fd92fbdd507f33f4b3a923993d72adfc5e31c0c5c7903030180028070800002009800025c209040007801891347e01f8c2f90198703070e40c1c0e000e01c2000008126000197082450000e006244d1f807e30be40661c0c0c79030307800283f1800006009801825c219140007801891347e01f8c2f9019870303065edede0293a71b8024c83cd80e8edf492d90000c004244d07806c30ba40641c0c0c197b7b01804e807c80100272f802325d24b440003001091341e01b0c2e9019070303065ede9c4393271ba024c87cfe0e8edf492d90000c004244d07806c30ba40641c0c0c197b78500a4c144e009220f3603a3b69243640003001091341e01b0c2e9019070303065ec0de6010a71ea000c09c7e008ad7482d10000c004244d07806c30ba40641c0c0c197a73790e4e9c6e809321f3f83a3b7d24b640003001091341e01b0c2e9019070303065e14de0291a70b8024c83cd80e8e4f412d90000c004244d07806c30ba40641c0c0c197373718e4e9c7e809323f3d83a3b7d24b640003001091341e01b0c2e90190703030658d8d86302a61fa004c8dcf60c889f482590000c004244d07806c30ba40641c0c0c195353518a46947e809222c3983a1b7c24b640003001091341e01b0c2e90190703030640c0c06000a01c2000008026000097082410000c004244d07806c30ba40641c0c0c187272710e4c9c6e809321f3d83a3b7524a640003001091341e01b0c2e9019070303045edede4313a71ba004c85cfe0c8edf492d90000c004240907806430ba40641c0c0c017b7b78004e9c6e0013007360023b5d24b44000000009000060190c2e9018070302045ede984313261ba004c85cfe0c8c9f492d90000c004240907806420ba40641c0c00017b7800004c004c00100072600232492434400000000800006011082690180703000040c00000000010000000000000009208041000000002000018044209a40601c080c117a63790c4a9c6e80132173f8322b7d20b640003001090241e019042e901907001fe05e01fe0010ef0a8001c21d58008b47402d107f200481e902193251a3ac1e01c007f810007f80003bc220007080500000d1c009041fc801207a40864c9468eb078070003005e00de0010a70a8000c01c58008a47402d1000000000400018024103a40601c000c0100030000028020000000000000001c0090400000000100006009040e9018070000005e0000001000020000001c18008802400d1000000000000018004001a4060) (
.fork 9 0x925052ae74166a038d904001b028308000362040e488882022805498011a33048062 (
.leaf 8 0x249094a39c859a30f364001f6c180c27c40d8ad83932220808a00c26014484c1261889242528e121608c2cd80007db060301f10122b6064c8882022803098051213049862249090a39c848230f160001f6c180c27c4048ad83932220808a00c26014480c1261889201fe0e601fe0038ff08801bc20148000367002e08ffa00689e90a013211b2081e02480148398059800e36400006c080420000d88003822220008200420004004c020180920052004000400100100000000000000024000080888800208010800100130080602480000398000000e040000068000020000088003822020008200020000000400018091f051ec1c141e020c0f460100183260061920c4440001e006a14d1e205a3484226624147c7b050707808383b18040060c9801841c119101007801a3b347840ece0900598905050ac14140a020c00400100083000001020404400002002804418001a3004006224141428000000000000000000000000000000000000000800a0110600068c01001889050000c1400000200000001000020000000204040000000008000000000200000602400140300050000830000004000040000040800100000000020000000000400001808e4e4e9a121209c2c58001fdb360301f11120b6924fbfe3ffbd032f84f92c3459c9b20f390e684848670b163817f6cdc0c07c5c482db493e234fecf04cb60b64a1d16f80c8243cf9a121219c2c58e05fdb370301f17120b6d24cffb3f6b9ab2b817930b459d83209090a38d8c8230b160001f6c180c27c4048ad81932220808a00c26014480c1260088242428e321628c2cd80007db060309f10122b6064c8882022803098051203049802209090a3858582b0b360101f6c1a0c07c4048ad81932220808a00c26014480c1260088242428a121208c2c580007db060301f10120b6024c8882022803098051203049802209090a0000000200000001e00000000040002c80032220808a00c26014480c1260088242000a12000002c1000001a04020000002004020c80800208020800400010018002080108280048000a16000006c080400000480000822220008200420004000c020000804040881010080204000001000030000010004004000020028000180012000400021fff8001fff800007c404c0038107a600232c9343c7e03002c1848307b1139669e9e07e3e3e760e0e07c0cb81c3fcb368027f110b7bab61fbfedffd747fe7cfecf3fbdcfd1f8f8001fbf800007c404c00381072600232c9243c7e03002c18083073113866961e07e01fe07e01fe0018ff0a800bc21d58008b67402f18ffa00681e90a1d3255b3ac1f81f800f81f803f80062fc2a002f08716002299d00bc62fe801a05042870c914ceb03e071fe0005ffe00001700130004041e98008c924d0d170040090612041ac44a49a7a601c7f800107f800001c00440010100a0000124834105c0100241848106b1129269e98071f1f1e41c1c1e000e0fc60000183260061970c6450401e0062fcd1fb07f3cbe6366) (
.leaf 9 0x349cdefc5050502a44140e1e9220c3003e1922cc2632227fdbe91fe7a17e8cf96719cd27272e1414140a91050387a48830c00f8648b3098c888e026a47d9e857a33a4986627978003fdf80000fc400c0078107a60023089143c3e03002c30083013003840061e09e005e0fe017e0038df02801bc21d58008b62400f08bfa00689010a04300530080f82717172f656562cc8b181e6053e37f4032642912570cdd8ff6f4119e12a6bc11413ec9a5a5ab1414140a91050387a48830c00f8648b3098c8883ffb807698059a33459c6b24ff80039ff80000fc40440078100a200012c834383e03002c3848300b1029600e98093ac535e69967533ad9f1781f3b41ae0c73fa08de8b88ddfb5e11bc629c097c1a66524dedefc1050502a4414061e922083003c1922cc2232227fffe91fe7817e8cf96719c937a53f0414040a91010107a40820800f0648b3088c889ffb7a07f9e05da33c59c672494eb579d9a654cf4dba3e06bf509b831d0bc17fa33def7db67aae985a84a584779492537bf0404140a91050087a08820400f0648b3088c889ff6f847f9e05ba33659c67249494ab9d9d9822f764001eec188c200c1d8adc3832220808a01d2601468cc126188925252ae76760ac3dd80407db068309f10522b70e4c8882022807498051a33049862249494ab9d9c9232f564001fec188c27cc1d8adc3932220808a01d2601468cc126188925252ae7660408bd110007ba042208030662b70e0c8882022807498051a33049862249494ab9d859ab0f364101f6c1a0c27c40d8ad83932220808a01d2601468cc126188925252ae725668cbdd90007fb062309f30762b70e4c8882022807498051a33049862249494ab98159822e764001eec0884200c1d8acc3832220808a01d2601468cc126188925252ae56564acbdd90407fb06a301f30762b70e4c8882022807498051a33049862249494ab858582b0b360101f6c1a0c07c4048ad81932220808a01d2601468cc126188925252ac54544a8b1c10407b000a300030742b70c4c8882022807498051a33049862249494aa94949232f564001fec188c07cc1d82dc2932220808a01d2601468cc126188925252a0404040891010007a0002000030640b3080c8882022807498051a33049862249494a39d9d9a30f764001f6c180c27c41d8adc3932220808a00c2601448cc1261889252520e76766003dd900001b060308000762050e0c88800208030800500330098602494942b9d9d0280f740100068120c20001488143932020808a0192601068c41061889252428e767208c3d580007db060309f10522b70e4c8882022803098051223049862249490a385848230b160001f6c180c07c4048ad81932220808a00c26014488c1261889252000e76600003d1000001a040208000422050e0c8080020802080040021001860249480001010000044000000000000000010000420320200082008200100084006180925052ae74166a038d904001b028308000362040e488882022805498011a33048062))))) (
.fork 15 0x2db4b7b9140014081005028780801040018240b2090c8893ffb84329885b213659c6b (
.fork 12 0x125adad5089899530226f9f804f94cf60c789d48f093777dfdd7f8b677ae5ccfb6795 (
.fork 11 0x124008e0ea01fe0028ff08801bc20d58000b674026107f200481a902153054a1ac190 (
.leaf 10 0x49002103a807a800a3e820006d08346000249d009841dc800006a00854815206906412400840080088000022080000400c1000080540201077200001a80215205481a419049000003a8000000a040000068003060002089001840000000000000500110069004121fe000c1fe000027001100140402800004920d041700400906120412c44a49a7a00487c207b070707808383f18040060c9801865c3191410078018af347cc17cb2798c192081f1ec1c1c1e020e0fc60100183260061970c6450401e0060fcd1f303f1c3e630648202003070707808383f18040060c9801865c31914100000002e0004c01430698c012080800008081400020f8600001002600609508601040000000b800130050c1a63004820000307000000800040004000080000024830104000000000400048010106988012001fe0c001fe0020ef088011c201400003470024107f200481e902113251a3ac1804800200300070000838020004000040000041c00904100000002a00044014206904010fce8f9a121219c2c58e05fdb370301f17120b6d24ffff3ffb5bb2f87f93cf45bf9b43a3f3e684848670b163817f6cdc0c07c5c482db493fffcffed6ecbe1fe4f3d16fe6d0e8e8e1a121219c2c58e05fdb370301f17120b6d24fffe1ff95bb2e07f81cf41bf9943a3a384808084703063817f2cdc0007c5c082cb483fff87fe56ecb81fe073d06fe6505ce859a121219c2c58e05fdb370301f17120b6d2477773f935ba2787e93cc453f93412173e684848670b163817f6cdc0c07c5c482db490dfdcfd2d6e49e1ee4f39169e4d0484840a12121942c58e0585b370301f0712004d24377600005b80607a01cc00239041212100000004400003816000c4000001c00003400ddd800016e0181e80730008e410484000a12000002c1000001a04020000002004020300400004100406800c40022104100210280048000a16000006c080400000480000801dc800006a00814805200006410080800810101802040e0401001030000610004404040000000b800030010c0023003cff8003fff80000fc404c0078107a600232c9343c7e03002c3848306b1129669e980f272000fffe00003f1013001e041e98008cb24d0f1c8080020a020818444219a58603c807f83f807f800e3fc2a006f087560022d9d00bc63fe801a27a42864c946ceb0780f200720fe01fe0038ff0a801bc21d58008b67402f1888800208410818124133ac0603c7c1c7b070707808383f18040060c9801865c319140007801a95347e81f8d2f98998f071f1ec1c1c1e020e0fc60100183260061970c6450401e006aecd1f907f38be41663c1c1c3b070703808380708040020c9800065c309140003801a91347e01f8c2f90198f07070e40c0c06000a01c2000008026000097082410000e006a44d1f807e30be4066389898b2e6e6e33cb9f86e9f7f397fdff626f7f88f72223809a90e67e15d80efb6018d37a73f1414140a91050387a48830c00f8648b3098c889ffb7a47f9e85fa33e59c67) (
.leaf 11 0x496b21542262254c088be5e011e532d831e27523c24dddf7e55ee2d9deb17336d9e55258c851088889510222f87800714c3600789548f0137771f915b82617a85cc5b6791495ea17fa857a82aa7e8241efd28b6603c34bfcc9a51dcffe5cebbcfd5b7da37d765d24d6000ebee00002f1010001a040e18000cb24d061700400004120416c04e41a7a1049238003aff80000bc40440078103a600032c934185c0100241048105b0131069e841248c841089889530222f97804794cb60c789d48f0937761f915b82617a85cc5b679149216b542222654c089be3e003e531d831e27523c24dddf7d357e2d9dea9731ed9e5524858d1088889510222f87800714c3600789548f0137771f495b82617a85cc5b679149215effafa8502ab854421eea30b9603c2bebf81a4c217fd3d157d7da6fb59ff985d24848c1088899530226f8f800f94c760c789d48f0937761f495b82617a85cc5b6791492121542222254c088be1e001e530d831e27523c24dddf7c156e2d9dea17316d9e552484840ebebea002efa18001b460f180009b74c261377600005b80617a05cc1a639049212103afaf87d0bbe3f1e16cde3cffc1e6dd33d94ddd800016e0185e81730698e412484840ebeb21942e58f0585b370f19f079b24cd65377600005b80617a05cc1a639049212103afaa2544b8cbe1e069d538f801e2dd33d84ddd800016e0185e81730698e412484840ebe1ebf42cfafc785b778f3ff079b74cf65377600005b80617a05cc1a639049212103ac87ae50b3eba1616ddc3c67c1e49d13d94ddd800016e0185e81730698e412484840ea89eb512afaf8781b734d3e0079b748f61377600005b80617a05cc1a639049212103a7a7a7d4bbebf1e16ddf3cdfc1e6dd33d94ddd800016e0185e81730698e412484840e1e1e1f42cf8fc785b378327f071b70cf65377600005b80617a05cc1a639049212103272727c48b8bf1e041c73cd801e65d33d14ddd800016e0185e81730698e412484840a9a9a9d52e7af8785b774f37f079b54cf25377600005b80617a05cc1a63904921210022222544088be1e001c530d801e25523c04ddd800016e0185e81730698e412484800ebebc1e02ef0fc601a058f3e0069b74c665340400004b80417805cc1a631049210003afa80000b8404000681038600022c930184c0100001040105a013106988412484000088800000200100000000c1000089048001300400004100416804c41a621049202103af07af80a3ebf1806d0e3cf801a6dd319941dc800006e0085c81530698e412401fe0ea01fe0028ff08801bc20d58000b674026107f200481e902153255a3ac19049007f802007f80003bc220007083540002d15008041fc801207a40854c9568eb06412401ce0ea01ea0028fa08001b420d180009274026107f200481a902153054a1ac19049003583a807b800a3ec20006d083460002d9d009841fc800006a40854c15686b064124008e0ea01fe0028ff08801bc20d58000b674026107f200481a902153054a1ac190)) (
.fork 13 0x17ebe000fffe00003f1013001e041e98008cb24d0f1f80c00b06120c1ec44e59a7a78 (
.leaf 12 0x5f802f83f807f800e3fc2a006f087560022d9d00bc63fe801a07a42874c956ceb07e175fe000fffe00003f1013001e041e98008cb24d0f170040090612041ec44e49a7a705d2d0003fff80000fc404c0078107a600232c9343c4c0100001840107a113926989c17401fe0fe01fe0038ff0a801bc21d58008b67402f107f200481e9021d3255a3ac1f05d002d03f807f800e3fc2a006f087560022d9d00bc41dc800007a0087489560e907c171f0b1ec1c1c1e020e0fc60100183260061970c6450401e0062fcd1fb07f3cbe63665c2c7c7b070707808383f18040060c9801865c3191410078018bf347ec1fcf2f98d9970b0b06c1c1c1e020e0fc60100183260061970c6450400c0042fcd07b06d3cba63645b2b2b146262654c089befe013e573d833e27523c64dddb7f75fe2d9feb9733ed9e7565aca55189899530226fbf804f95cf60cf89d48f193777df957f8b67fae5ccfb679559296b546262654c089befe013e573d833e27523c64dddf7d35fe2d9feb9733ed9e5564a4a44189899530226fbf804f95cf60cf89d48f193776c0047f8967fa65ccba6394552d2d1ad4d4d65af5778f61fefccf07fbdda0176f0dddb0011ff359be9a7f2808fd12ffe000fffe00003f1013001e041e98008cb24d0f1f80c00b06120c16c44e59a7a184ba38003fff80000fc404c0078107a600232c9343c7e03002c1048305b0131469e8612e8e000ebea00002e1010001a040e180008b24c061f80c00b04120c16c04c51a7a184ba38000faf800007c404c00381072600232c1242c7e03002c1048305b0131469e8612e01fe0fe01fe0038ff0a801bc21d58008b67402f18ffa00681e90a153255b3ac1984b802383f807f800e3fc2a006f087560022d9d00bc63fe801a06a42854c152c6b06612e008e0ea01ea0028fa08001b420d18000927402618ffa00681a90a153054b1ac1984b802380f802f80060fc2a002f08716002299500ac63fe801a06a42854c152c6b06612dac8d5189899530226fbf804f95cf60cf89d48f193777dfdd7b8b677ac5ccdb679d4b236b546262654c089befe013e573d833e27523c64dddf7f757e2d9dea9731ed9e752c8c8c1189899530226fbf804f95cf60cf89d48f1937761fd95b82617a85cc5b67994b23230422222544088be1e001c530d801e25523c04ddd87f656e0985ea17316d9e652a8a8a1d5d5d5eab1e5ffe7b489b3e60fe7dfbf6ddcc881ff90bb28135850f5bff0949a18003bfb80000fc404000681038600032c934387e0300081048305b0131469e8412600860ee01ee0038fb08001b420d18000b67402e18ffa00201a90a153054b1ac190497f8003aff80000bc40440078103a600032c934185c0100241848105b1139269e84125fe00009fe00000700110004040e90000c904d001700400906120416c44e49a7a1049738003afa80000b8404000681038600022c930185c0100241048105b0131069e84125adad5089899530226f9f804f94cf60c789d48f093777dfdd7f8b677ae5ccfb6795) (
.fork 14 0x28b4b4b9000000080000000780000000010000b2000c8893ffb803298059203459c0b (
.leaf 13 0xa2d2800000000000000000000000000000000000003202002c20082001000040060228a014a00000000000000000000000000000000000088880068801080010003008008a0505060000000000000000000000000000000000000004800a00006000480010000a69292951898984302261ba004c85cf60c889d482190001dfdd240b0780e400fb440d964e4e5c5050500a44140e009220c3003a19200426000077f74913c1a03a0c38411b64d2d2d5181818130206039804f85cd00c9808409183377dfdd740b66cae0c0e1049d92cacad45050502a44140e1e9220c3003e1922cc26322277ff490ee1a17800f86703649ad295109811530204f3f804b950e60cf09808d183005dfdd650b46a8e084e1260d925eca7c4050402a04100e1e9220c3003e1022cc0610007ff7c91bc7a13e88394703e4929ad5101099530026ebf804f950e60cf00d00f180773dfdd3e8b2692e108e1058d924a5efc4040502a00140e1e9220c3003e0922c80600207ff7c917c7a07e84b96103e49292951010100200040380048810c00c8008000180001dfdd240b0680e000e1040d924a00004040000000000c001000420002000000040000002408000020100020000224801280100010000004028000801040008000000100000004804000080200020000890484850000000000000000000000000000000000000007001090241a01800280001209090910000000000000000000000000000000000000011fd90002000080004104097dbd8003fff80000fc404c0078107a600232c9343c7e0300083848307b1139669e9c1f600f60fe01fe0038ff0a801bc21d58008b67402f18ffa00209e90a1d3255b3ac1f07c3c3c3b070707808383f18040060c9801865c319141003801abf347ec1fcf2f98d99bede000fffe00003f1013001e041e98008cb24d0f1f80c00b0c120c16c04e51a7a786f803783f807f800e3fc2a006f087560022d9d00bc63fe801a26a42854c156c6b07e1b7fe000effe00003f1011001e040e98000cb24d0e1f80c00b0e120c16c44e59a7a706db5b5a8323235664c8fe1fe81c5b0d80dfb57efe07fff8808b6fd3e5fc7ffc7befc9b6d6000efee00003f1010001a040e18000cb24d0e1f80c0020c120c16c04e51a7a706d807f83b807f800e3fc22006f083560002d9d00b863fe801a27a42854c956ceb07c1b600d60ee01ee0038fb08001b420d18000b67402e18ffa00209a90a153055b1ac1f06c34342b070707808383f18040060c9801865c319141000800a2f1064c07cf0798d89a6c6000ebea00002e1010001a040e180008b24c061f80c0020c120c16c04c51a7a1069803183a807a800a3e820006d08346000249d009863fe800826a42854c152c6b06418ecece9a121219c2c58e05fdb370301f17120b6d24fffe3ffbdbb2f87f93cf45bf9b61b1b1a284848670b163817f6cdc0c07c5c482db493fff8808b6ec3e1fc4f3c12ee497ebe000fffe00003f1013001e041e98008cb24d0f1f80c00b06120c1ec44e59a7a78) (
.leaf 14 0xb6ca5ed45040500840140e00122043003209200026222277ff6906e1a07804f8611b6da537aa1404140891050287a0803040038640b3090c888206a847498853a3324986ab68c5e985050500a44140e009220c3003a192004262222301b291761a05a0ce8201b2da0b7a11414140a91050387a48830c00f8648b3098c8881ff984328085a013619c69b6807f805007f80043bc2a0007084500020d1400a423fe801a27a42824c846c8207a2da017bf1400140a90050287a08830400f8248b20988889ff6f845f9e81ba1365846fb6805e83d805d800e3740a006e084520020d88003c2222001a210420204804c8201a2da017a01400140010050280008010400082400009088880068841080812013208068b680000050000000400008000000400002000000242202000820002020000040001a2d97979f1010100200040380048810c00c8008000180001ffdfa44f1e80fa30e5046fb4dedcfc1050102a4404041e902082003c1922cc2232227fede91fe7a17e8cf96719ed3737bf0404140a91050087a08820400f0648b3088c889ff6fa47f9e85fa33e59c67b4dcdcf8101010224404001e800080000c1902cc2032227809a91f67a15e8ce92619ad1f171e01c001e00000f460000182260060900c4040001e006a54d1ea07a34a42266b45edc7c0050002a0400041e902082003c1022cc0210007fe5e91bc7a13e8c394719ed171f1e0001c1e000e0ec6000018126006105006040401e006aecd1e907b38a40166b45c5efc0000502a0014021e822081003c0922c80200207fd3e917c7a07e8cb96119ed17171ec14140a020c0040010008300000102040440001e006a44d1e807a30a40066b45c5c785050500a44140e009220c3003a1920042600007801a91347a01e8c290019ad17171e000000000000000000000000000000000000001e006a44d1e807a30a40066b45c00000000000000000000000000000000000000000000002800002010082000182d0017000000000000000000000000000000000000000000000840000802010200060b2dadaf44040402800100e1e12204300360022c80632227fffe90ee7a17c80f96703e9b5b5bb0404040891010007a0002000030640b3080c8893ffb807698059a33459c6ba3d3d3e4808080703060007f2cd80007c44082ca483effcffef40cbe13e4b0d16726e8bcf4b90120019c0400e05fc0350201f17000b6d04f88d3ffbc132d82d928745be0ba2ded2fc0050002a0400041e902082003c1022cc0232227fffe81fe7817688f16703e8b4bcf90001219c0048e05fc1330101f17100b2d04cffb3ffb9ab2b817930b459d8ba2d2defc0000502a0014021e822081003c0922c80232227fffe11fe7816e84d96703e8b4b4b9a121208c2c580007db060301f10120b6024c8893ffb803298059203459c0ba2d2d2e45050502a44140e1e9220c3003e1922cc2632224ffee00ca6016480d16702e8b4b4b9000000080000000780000000010000b2000c8893ffb803298059203459c0b)))) (
.fork 17 0x30d8d8d1000001100000e0580031000000700000d0037771fd95b82607a81cc412799 (
.fork 16 0x2dbad7b5149815531205f3f804b950e60cf2d808d98b88ddffde51bc6a9e097e1a66d (
.leaf 15 0xb6defffc5057f82a47bc2e1e9728c7003e1d36cca633feffffefbfefa5fecef9677bedb7bfff1415359e914de3dfe5bb31c1fff748b3d9ccffbffffbeffbe97fb3be59defb6defffc5052756e449faffe93e5c3983fd936cfe633feffffefbfefa5fecef9677bedb7bfbf1415d5ea91e5efe7a489b1e60fe74db369ccc89ffffaeff9e95fb3be59d6fb6deeb545052654c449bafe013e5439833d03407e633def7ff6faae9a5b84a78477b6db7b7bff776140abd150387be8c32c80f866ab70f8c889ffffa47f9e85fa33e59c6fb6dedeffd855d82ae7740e1efe28c7203e1daacc3e32227fffe91fe7a17e8cf9671bedb7b7bfd55554aab1c50787b488b3c00f874ab70dcc889ffffa47f9e85fa33e59c6fb6dedefed4d4d23af5740e1ffe38cf07fe1da2dc2f32227fffe91fe7a17e8cf9671bedb7b7bf1e1e140a93050387a4883cd80f8e48f3098c889ffffa47f9e85fa33e59c6fb6dedefc7850782a441c0e1e9320f3603e3923cc2632227fffe91fe7a17e8cf9671bedb7b7bf1c1c1c0b93070387a4c87cd00f8e48f3098c889ffffa47f9e85fa33e59c6fb6dedefc5050502a44140e1e9220c3003e1922cc2632227fffe91fe7a17e8cf9671bedb7b7bf141400081100030784001080018400b3090c889ffffa47f9e85fa33e59c6fb6dedefc5000502040140a1e02004100060902c82432227fffe91fe7a17e8cf9671bedb7b7bf1010100a00040387848810c00d8008b2018c889ffffa47f9e85fa33e59c6fb6dedefc101010224404001e800080000c1902cc2032227fffe91fe7a17e8cf9671bedb7b7bf0014000a81000107a40820800f0408b3008c889ffffa47f9e85fa33e59c6fb6dedefc0000502a0014021e822081003c0922c80232227fffe91fe7a17e8cf9671bedb7b7bf000000080000000780000000010000b2000c889ffffa47f9e85fa33e59c6fb6dede805050500044140e001200430002190004243222003e290c2021580ce8261a2db7b71e14140000110003000400108000840001090c809e0b6a46d9e847a31a4186eb6ded2e45050002044000c1e10004200061002cc2432224ffee80ca6217488f1671aedb7b2951414100211040380048810c00c840801098c809dffda42b8684e021e11c6db6de94a85050102244040c1e9000c2000e1902cc243222082ca81d2621568ce1261aadb7a3061414140291050380248830c00e864801098c808c0b4a46d86846831a0186cb6de82845050502a44140e1e9220c3003e1922cc26322207fe680ca0217008f0671a6db7a01f1414000a91000307a40830800f8408b3098c809ffb7a06f9e84da21c51c6fb6de8003ddd80000f4400c0078104a20021088143c3202002c28082021100860061a2db7a00014140000110003000400108000840001090c80800b0a02080844021801868b6dc5ef85000500040140a000200410002090000242222781ba91767a05e8ce9201badb4b7b9140014081005028780801040018240b2090c8893ffb84329885b213659c6b) (
.leaf 16 0xc363000000000000000000000000000000000000000c0100241040101a003100088630c018c000000000000000000000000000000000000077200481a8020520148000198c060604000000400000381000004000001800001000100400002e0000c00430008c02fbfe0005ffe00001700130004041e98008c924d0d1f80c00b0e120c1ac44a59a7a68bededefd7b78502a4c144e1e9220f3603e3b6bec3672227fffe91fe7e17f8cfff71befb7b7bf5e14de0a91a70b87a4c83cd80f8e4ff32d9c889ffffa47f9f85fe33ffdc6fbededefd535351aa46947e9e9222c3983e1b7eecb672227fffe91fe7e17f8cfff71befb7b7bf1c9c9c4b93271ba7a4c87cf60f8eddfb299c889ffffa47f9f85fe33ffdc6fbede80017b7800004c004c001000726002324924347202002c28082061110866961a2fa01fe05e01fe0010ef0a8001c21d58008b47402d18ffa00689e90a193251b3ac1e8be805e8178037800429c2a000300716002291d00b46222001a210420604904ceb01a2f1f171e41c0c1e000a0fc60000182260060970c6450001e006a54d1fa07e34be6266bc5c7c79030707800383f1800006049801865c219141007801abb347e41fce2f9059af17171ec1c1c0e020e01c20100083260001970c2450001e006a44d1f807e30be4066bc5c5c7903030180028070800002009800025c209040007801a91347e01f8c2f9019af17171e40c000000000100000000000000092080410001e006a44d1f807e30be4066bc5c5c7900030000028020000000000000001c009040007801a91347e01f8c2f9019af17171e008080400020182000000026000095082010001e006a44d1f807e30be4066b7dfdffcd0d0d07a74740e7fbef8c307fe59a2ce6e3efffffffd1fffb3febcf9673fedf7f7ff1c1c1c1b9307039fa4f87cd00f9e48f3998fbfffffff47ffecffaf3e59cffb7dfdefcf8f8502a7c540e1eba30f3603e39a3cc2e3e237ffff91ff7b37ebcf9671fedf7f7bf1c1c140a93050387a4883cd00f8e48f3098f88dffffe47fdecdfaf3e59c7fb7df8000f8f800007c400c0038107260023081042c3e03002c38083033103860061e2df7b7ff3e143e0a991f0387afca3cd80f8e68f30b8cbfbffffb47fbec7fa73e59cffb7dedffc7050702a441c0e1e9320f3403e3923cc2632feffffed1fefb1fe9cf9673fede017e03e003e00181f02800bc21c58008a60400b08bfa00689410a0c320532080f8b6ffdefc57f8502a5c144e1e9230cb003e1b62fc263e237ffff95ff7ab7eadf96f9bedbff7bf1534159e9505e3dfe4bd32c1fff648b7d9cf88dffffe57fdeadfab7e5be6fb6ffdefc5270556e4c17cffe92e5c3983fdb62ef663e237ffff95ff7ab7eadf96f9bedbfe00015fe000017001300040412800084900d090f80c00b0e120c0ac40a5803a68b6fedefc575057aa4417df9e9226cb983f9b62fd2732227fffe95fe7a97e8df96f9bedbad7b5149815531205f3f804b950e60cf2d808d98b88ddffde51bc6a9e097e1a66d)) (
.fork 18 0x365a5ad5088899530226f8f800f94c760c789d48f093777df4d7f8b67fae5ccfb6795 (
.leaf 17 0xd969695022222544088be1e001c530d801e25523c04dddf0011fe259fe99732e98e5361fe00001fe000007001100040402800004900d00170040090612041ac44a49a7a00d87c6878070207800083f180000608980182543181410078018bf347ec1fcb2f98c1b61ada15009881530220f978043940a60c709d08f093405df956f8b47b8e58cfb6705d8687c78020707800383f180000604980186542181410078018bf347ec1fc72f98c1b61a1ad5008099530026f8f800f940660c709d08f090773df4d3f8b27b2e50cfb6785d8686853070707808383f18040060c9801865c3191410070010be241ec19432e98c1361a1a14189899430226fbe004c95cf60ce89d486190401c0042f8907b0650cba6304d8686850020205000083e180000400980182542180410070010be241ec19432e98c1361a00000080000000001000000000000000900800100000000210001a044049a6200d8007f800007f80003bc220007080500000d14008041fc801207a40864c9468eb06036001a0000008000002008000000000000000500201040000000e80019025083a4100d36b6b544040444800138f6012e4430033c02003460dddf7f75fe2d9beb8733849e772dad8d5089889530222f97804794cb60c789d48f093777dfdd7b8b677ac5ccdb679dcb636b542222654c089be3e003e531d831e27523c24dddf7f757e2d9dea9731ed9e772d8d8d1189899530226fbf804f95cf60cf89d48f1937771fd95b82617a85cc5b6799cb63634422222544088be1e001c530d801e25523c04dddc7f656e0985ea17316d9e672d8d8d1088801100200f05800310c1000789048d0137771fd95b82617a85cc5b6799cb63634420022440008ba16001c4304001e01503c04dddc7f656e0985ea17316d9e672d8d8d1008081500020f8780031002600709508f0137771fd95b82617a85cc5b6799c3f3e3e4848086703063817f2cdc0807c5c082db493fffcffed6ecbe1fe4f3d16fe6f0f8fcf92021219c0c58e05fcb370101f17120b2d24ffff3ffb5bb2f87f93cf45bf9bc3e3e3c684848670b163817f6cdc0c07c5c482db493fffc7fe56ecb81fe073d06fe670f8f8f12020211c0c18e05fcb370001f17020b2d20ffff1ff95bb2e07f81cf41bf99c3e3e3c4000004600003817e00c4000005c002cb403fffc7fe56ecb81fe073d06fe670dcf8d90120019c0400e05fc0350201f17000b6d0477773fdb5ba2787e93cc453f9bc36b63540260054c0803c5e010e5029831c26023420dddf7f75ee2d99eb0733049e770d8dcf90001219c0048e05fc1330101f17100b2d0437f73fdb5b92787b93ce45a79bc3636b540002654c009ba3e003e5019831c03403c20dddf7f757e2d99ea8731849e770d8d8d1a12121942c58e0585b370301f0712004d2437771fd95b82607a81cc412799c36363446060644c081b8f6013e5734033e02103460dddc7f656e0981ea0731049e670d8d8d1000001100000e0580031000000700000d0037771fd95b82607a81cc412799) (
.fork 19 0x36dac855189889530222fb7804795cb60cf89d48f193777df957b8b67fac5ccdb679d (
.leaf 18 0xdb6b210062622544088bede011c572d803e25523c44ddd80241ee0187e91732698e636dac2041898984302261ba004c85cf60c889d482193004c094650947e864c4ba621cdb6b03046260604c08184e6013e1734032626122464cdd87f65c40987ab13136d9a676dac015189801530200f37804395cb60cf89848d193005df95610b47e8c4c4db661ddb6b0003efe80000b8404c0078107a600222c9301c4c0100241840107a113126988636dac000189800000200130004001c900088904801130040090610041e844c49a6218db686b5062026500009beb80030471d803a255218441dcf0130fe249fc99532e98e736d8dad5180099530026eaf800f95c760cf80d40f193777dfdd5f8b67faa5cc7b679ddb636b4462226544089bebe003c571d803e25523c44dddc7f657e0987ea9731ed9e676d8dad1181899130226ebd804f95cd00cf80d40f1937771fd95f8261faa5cc7b6799db636b4460026440009bab6003c4714003e01503c44dddc7f657e0987ea9731ed9e676d8dad1000081100020e8580031000000700500f0137771fd95f8261faa5cc7b6799db636344600004400003896000c4704003e00103444dddc7f656e0987ea17316d9e676d7badf1814980a81260b87a4c83cd00f8c0df32194773ffdf3eef3fd6ff68ff5d9fdb4a6b546042600800982e0013207340322035008641dcf7f74fa2c9f4b9523ed16776c8dac1189899530226fbf804f95cf60cf89d48f1937761fd95f8261faa5cc7b6799db216b546222654c089bebe003e571d833e27523c64dddf7d357e2d9fea9731ed9e776c85ac0188899510226faf800f15c7600f89548f11377600485f8061fa25cc3a6398db086b106262610c08986e80132173d8322275208641dcb0130fa249f499522e906736c0dac11818981302260b9804f85cd00c980d40b1937761fd95e8261daa5c87b4599db007f83e807f800a3fc2a006f087560022d9d009c41fc801207a40874c9568eb06636c01fe01801fe0000ef0a8001c21d50008b454021107f200481e9021d3255a3ac198db007f8060027000009c2a0003007140022915008441fc801207a40874c9568eb06636c01ee01801b800006e0a8001c21d500089054021107f200481e9021d3254a3ac198db006b806002f80000bc2a0007087140022915008441fc801207a40874c9528eb06636c01ad5180099530026eaf800f95c760cf80d40f190773df4d1e8b27d2a5487b459ddb006b03e807e800a3f82a006f08756002249d009c41dc801207a0087489520e906636c01ac01800980000260a8000c01c5000880540211077200481e8021d225483a4198db000000600000000000080000007040022001000440000000000000700110069006369a9a95109091420024fbe0048910e60ce09d086190401dfdd2f8b07b0e50cfb670dd96b69542262254c088be5e011e532d831e27523c24dddf7e55fe2d9feb9733ed9e5765a5ad5088899530226f8f800f94c760c789d48f093777df4d7f8b67fae5ccfb6795) (
.leaf 19 0xdb6b6b7c626267cc089bffe013e773d833e27523c74dddfff7dff3dffebff33fd9e7f6dadad5fbfa99532e36fbf81efd5efe0cf8bf4cf793777dfdd7f8b67fae5ccfb679ddb6b6b57ea67ed4cabfbefe07fed77f833e6fd23de4dddf7f75fe2d9feb9733ed9e776dadad5d9d9d9f322e6fff814f9dff60cf99f4cf5d3777dfdd7f8b67fae5ccfb679ddb6b6b56e6e6e75cb9fbefe17ffd7fdff3e6f533cf4dddf7f75fe2d9feb9733ed9e776dadad51e9e99531326fbf804f95cfe0cfc9d49f993777dfdd7f8b67fae5ccfb679ddb6b6b547a627d4c489fefe013e573f833eb7523e64dddf7f75fe2d9feb9733ed9e776dadad51c9c9d539327fbf824f97cf60efedd49f993777dfdd7f8b67fae5ccfb679ddb6b6b546262654c089befe013e573d833e27523c64dddf7f75fe2d9feb9733ed9e776dadad51898980202261b8004c81cd00c889d482193777dfdd7f8b67fae5ccfb679ddb6b6b54626205400883ede010c472d803e25523c44dddf7f75fe2d9feb9733ed9e776dadad5189811120204f3d804b91cd00cf89848d193777dfdd7f8b67fae5ccfb679ddb6b6b5462026540009bebe003c471d803e25523c44dddf7f75fe2d9feb9733ed9e776dadad5181099120026ebd804f91cd00cf80d40f193777dfdd7f8b67fae5ccfb679ddb6b6b54424245480093efe012e4439833c27423c64dddf7f75fe2d9feb9733ed9e776dadad5088889510222f87800714c3600789548f013777dfdd7f8b67fae5ccfb679ddb6b6b540262054c0883e5e010e5029831c27423c24dddf7f75fe2d9feb9733ed9e776dadad5008099530026f8f800f940660c709d08f093777dfdd7f8b67fae5ccfb679ddb6b6b54020205400083e1e000c4009801c25423c04dddf7f75fe2d9feb9733ed9e776dadad1189899100226fbd804f11cd000f89548f1137771fd97f8261fae5ccfb6799db6b6b046262604c08986e6013e1734032627522c64ddd87f65fe0987eb9733ed9e676dadac01898980002261b8004c01cd000889548211377600d87f8061fa65ccba6398db6b6850626205000883ed80100472d803a25521844d0170251be251fe19732e98c736dad8d5189801530200f37804395cb60cf89848d193777dfdd7b8b67fac5ccdb679ddb6b634462622544088bede011c572d803e25523c44dddc7f65ee0987eb17336d9e676dad8d1189819130206f3d804f95cd00cf89848d1937771fd97b8261fac5ccdb6799db6b6344626004400803cd6010c4724003e24123444dddc7f65ee0987eb17336d9e676dad8d1008001100000f0580031000000709008d0137771fd97b8261fac5ccdb6799db6b5efc6260502a08144e1e9220f3403e2b63e8064c217ff7d957d7fa7fb5bff987f6dad295189810020204138004881cd00c8898480193005dfdd650b47e8e4c4fb661ddb6b23046262654c089befe013e573d833e27523c64ddd87f65ee0987eb17336d9e676dac855189889530222fb7804795cb60cf89d48f193777df957b8b67fac5ccdb679d)))))) (
.fork 30 0x3fdfdf1ec1c1c1e020e0fc60100183260061970c6453405e096efcd5ff87ffcbe637e (
.fork 25 0x3df7bfffb415340ab95d0387bf8a31c00f8768b30b8cffbffffbeffbed7fb7be59dff (
.fork 22 0x38bcbcb9810101882040e04790010300016100b6404cc893ffb8bb29835930f45bf0b (
.fork 21 0x36fae0003ebe00001f1013000e041c98008cb0490b1f80c00b06120c1ec44c59a7a18 (
.leaf 20 0xdbeb8000e2e0000038404c00381072400222c1200c7e03002c1848307b1131669e8636fae0001c9c00001300130004001c90008c9049091f80c00b06120c1ec44c59a7a18dbeb6bd4fa62fd4c68ffefe03fed73f833ebf523ee6ffff7ff5fe6f9fef973fef9e776fadaf51c989d531227fbf804f95cf60cfadd48f99bfffdffd7f9be7fbe5cffbe79ddb807f80f807f80063fc2a002f087560022d9500ac63fe801a07a42874c956ceb06636e01ae0fe01fe0038ff0a801bc21d58008b67402f18ffa00681e90a1d3254b3ac198db806b80f802f80060fc2a002f08716002299500ac63fe801a07a42874c952ceb06636e01ae03800b800083e0a800bc21c50008825402318ffa00681e90a1d3254b3ac198db806b8070027000409c2a000300714002291500a463fe801a07a42874c952ceb06636dffadf189c995b8326fbffa4f97cf60ffc9dfbf197777ffdf7fef7ffeffecff7f9fdb7feb5467fa654c1c9befe013f57bd833f27537c65dddf7f75fead9ffb97b3edfe776dffad5189c99530326fbf804f95cf60cfc9d49f197777dfdd7fab67fee5ecfb7f9ddb7f8003eff80000bc404c0078107a600232c9341c5c0100241848107b1139269e8636dfe00019fe00000700130004041e90008c904d01170040090612041ec44e49a7a18db7f8000627000000c004c001000724002324124045c0100241848107b1139269e8636dfdadf19d899f30226fff804f9def60cf89d4cf1d3777ffdf7fcf7ffaffecff679fdb7f6b7c6262654c089befe013e573d833e27523c64dddfff7dff3dffebffb3fd9e7f6defadd19b899df0626fbffc4fd5ef7fdf89dfef1d7777ffdf7fab7ffef7ccff7f9fdb7b800066e0000018004c0010107a4002224130045c0100241848107b1131269e8636dbdad718d899730226fff804f9dcf60cf89d48f193777dfdd7fcf67faedecfb679ddb6f6b5c6272654e0c9befe093e5f3d83bf27527c64dddf7f75ff3d9febb7b3ed9e776dbdad518de99530326fbf804f95cf60cfc9d49f193777dfdd7f8b67fae5ecfb679ddb6b800062f800001c004c001010724002324124045c0100241848107b1131269e8636dadfff18989d5b8227fbffa4f97cf60ffaddfaf1937f7ffdf7fdf7ffbffdeffe79fdb6b7fd46267fd4c0bbfefe017ed77d833ef7523c64dfdf7f75fe6d9fef977bef9e776dadff518989d530227fbf804f95cf60cfadd48f1937f7dfdd7f9b67fbe5defbe79ddb6b7f7c626767cc0b9bffe013e777d833e67523c74dddfff7dff3dffebff73fd9e7f6dadfdf189899530226fbf804f95cf60cf89d48f193777ffdf7fcf7ffaffdcff679fdb6b7bf46266e77c09bbefff17ed77dff7e677ebc74dfdfff7dfe6dffefdf3bff9e7f6dadbd71898d97302a6fff804f9dcf60cf89d48f193777dfdd7fcf67faeddcfb679ddb6b6f5c6262754e089fefe093e5f3d83beb7523c64dddf7f75ff3d9febb773ed9e776dadbd51898df5302a7fbf804f95cf60cfadd48f193777dfdd7f8b67fae5dcfb679d) (
.leaf 21 0xe171716284848650b16381616cdc0c07c1c48013490dddc800b6e01e1e84f30108e4b83c3c38a121218c2c58e047db070301f16120b6424cc8920228bb09835130f04bb02e07c707a070407808103d18040060c98018640310101007801aaf3478c16cb2108c1b81cfc198121019c2440e05fd0350301f17100b6d0474053f93cba2583c938c453f03e0707c7a040707808383b18040060c98018414118101007801a3f3478c0ec70908c1b81c1cf98101219c2048e05fd1330301f17100b6d0407f33f4b9b923833930e45a783e0707062040406008103810040040c00018400110101004800a2e0060c04c30108c0b81c00008100000020000000100002000000000400000000000810000200004002200e000700200040000810000004000040000040000000100000022a00004004200004037fbe0007efe00001f1013000e041c98008cb2490f1f80c00b06120c1ec44e59a7a78df806f81f803f80062fc2a002f08716002299d00bc63fe801a07a42874c956ceb07e37dfe0005ffe00001700130004041e98008c924d0d170040090612041ec44e49a7a78df6f6f5d636365cc0a9bffe013e773d833e27d23d64dddf7f75ff3d9febb7f3ed9ff77dbdbd71c9c9d539327fbf824f97cf60efedd49f993777dfdd7fcf67faedfcfb67fddf6f6f5c6262654c089befe013e573d833e27523c64dddf7f75ff3d9febb7f3ed9ff77dbdad55ede99531326fbf804f95cfe0cfc9f49fd93777dfdd7f8b67fae5ecfb67fddf6f6b547272654c4c9befe013e573d833f27527e64dddf7f75fe2d9feb97b3ed9ff77dbc0005ede00001300130004001c98008c92490d130040090610041e844e49a6278df6b6f557a637d4c4a9fefe013e573f833eb7d23f64dddf7f75fe2d9feb9773ed9ff77dadbd51c989d531227fbf804f95cf60cfadd48f993777dfdd7f8b67fae5dcfb67fddf007f817807f80043bc2a0007087560022d1d00b441fc801207a40874c9568eb07e37c01bc05e00de0010a70a8000c01c58008a47402d1077200481e8021d225583a41f8dc7c6c79070307800283f1800006089801825c3191410078018bf347ec1fcf2f98d9b71b1f1e40c1c1e000e0fc6000018126006197086450401e0062fcd1fb07f3cbe6366dc6c6c59030305800283f1800006009801825c2190410070010bf341ec1b4f2e98d936ffe0003ffe00001f1013000e041e98008cb04d0b1f80c00b06120c1ec44e59a7a18dbebebd4e2e2e57c38fbefff3ffd73dff7e2f7ebce7ffff7ff5feef9fff973feffe776fafaf51c9c9d5b9327fbffa4f97cf60ffeddfbf99ffffdffd7fbbe7ffe5cffbff9ddbebeb54fafa654c7cdbefe03bf573f833f2f527ee7fdff7ff5feaf9ffb9737edfe776fafad51c9c99531326fbf804f95cf60cfc9d49f99ff7fdffd7fabe7fee5cdfb7f9ddbeb8003fff80000fc404c0078107a600232c9343c7e03002c1848307b1131669e8636fae0003ebe00001f1013000e041c98008cb0490b1f80c00b06120c1ec44c59a7a18)) (
.fork 23 0x38fcfcf92020211c0c18e05fcb370001f17020b2d20ffff3ffbdbb2f87f93cf45bf9b (
.leaf 22 0xe3f3f3e4048006701003817f00d40807c5c002db413fffcffef6ecbe1fe4f3d16fe6f8fcfcf90001219c0048e05fc1330101f17100b2d04ffff3ffbdbb2f87f93cf45bf9be3f3f3e4000004600003817e00c4000005c002cb403fffcffef6ecbe1fe4f3d16fe6f8fcfcf1a12121102c58e0581b37030000712004d20ffff1ff9dbb2e07f81cf41bf99e3f3f38684848070b160007f6cd80c07c44482da483fff87fe76ecb81fe073d06fe678fcfce0a12120002c5800001b06030000012004020fffe00f8dbb0e07f01cf00bb98e3f3f06284840600b143810068140c0001848011093f03482cb2e8361f04f3410ec6b8fcf8f1a120211c2c18e05fdb370201f17020b6d20ffff1ff9dbb2e07f81cf41bf99e3f3e34684800440b043816068d4080001c08013483fdfc7fe76e8b81fa073504fe678fcf4b9a12000082c1000079a040200010020b6020f88d3ffbc132d86d92c745be1be3f3a38684848670b163817f6cdc0c07c5c482db493fff87fe76ecb81fe073d06fe678fce840a12121942c58e0585b370301f0712004d24ff7e00b0dba0e07e01cd003b98e3f390a284848230b160001f6c180c07c40482d8093e23082cb04c361b44b1c12e86b8fce0e1a120201c2c18001fdb360201f11020b6920fbfe1ff9d132e06f80c741be99e3f3806684800670b043817f68d40807c5c082db493e034fecf048b61b24b1514f86f8fce000bf3e00003f1003001e041e98008c20450b0f80c00b0c120c06c00c5003a18e3f3800284800000b04000006810080000008010083e03002c3048301b0031400e8638fc1cf8a10121802858e0401b030300006120044248ffb206a9b90b873134f04a39ae3e3f3c680848470b163817f6cdc0407c5c482cb483fffc7fe76ecb81fe073d06fe678f8dcf1a00121102858e0581b33010000712000d20bfff1ff9db92e07b81cf41a799e3d2f3e680048020a160001e6c080400040482c80833fecffee6acae15e4d2d16766f8e8fce1a121219c2c58e05fdb370301f17120b6d24fffe1ff9dbb2e07f81cf41bf99e3a1738284848650b16381616cdc0c07c1c48013492fff801a36e4381ec073c028e638e43ce8a121208c2c580007db060301f10120b6024cffa206a9ab0b857134b04999ae383f38680848070b160007f6cd80407c44482ca483fff87fe76acb817e072d0676678e01fe0a001fe0028ff08801bc20140000365002208ffa00689e90a053215b208198e38073e680048670a163817f6ccc0407c5c482cb4923fecfdae6a4ae14e4d2d16166f8e01ce0be013e00385f02801bc21d58008b60400b08ffa00689a90a053014b008198e380738280048000a16000006c080400000480000823fe801a26a42814c052c0206638e00000a0000000281000001a0000000000200002088080020800080400041000018e3737366040406408103816040c40c0001c40013410dddcff6f6e09e1ea4f31149e6f8bcbcb9810101882040e04790010300016100b6404cc893ffb8bb29835930f45bf0b) (
.fork 24 0x39fcfdf9e721679c3cd9e05fdb370309f17362b6de4ffff3ffbdbb2f87f93df45bffb (
.leaf 23 0xe7f3f7e784858670b363817f6cdc0c07c5c48adb593fffcffef6ecbe1fe4f7d16ffef9e01de0e601660038d900001b020108000362000e08ffa00689a90a053015b0081f8e474746b050506808303910040060c00018408111101004800a2f1060c06cf0108d8b8fffcffa1e121fc2c58f47fdb378327f171b0bed24fffffffffbfffe7fdbefc5bf9fe3fff3fe84d4867ab563857ffcfc8e07fdd4a2df4b3ffffffffeffff9ff6fbf16fe7f8fffcffa121219c2c58e05fdb370301f17120b6d24fffffffffbfffe7fdbefc5bf9fe3fff3e687fc8670bd63c57f7cdc0e07c5d6c2ff493fffcffefeecbe1ff4fbf16fe6f8fffce0a1ff20002f5811001f0603800005b00d020fffe00f8fbb0e07f41ef80bb98e3ff800287f80000bc40440078100a000012c034083e03002c3848301b1039600e8638fefcfda1b921df2e58f17fdf3f43a7fd71b8bed2cfffffffffbbbfe7fd3cfc5bf9fe3f7f3ee858486f0b163917f6cde0c07c5c482db493fffcffef6fdbe1fe6fbd16fe6f8fcffffa121e1fc2cf8ec7fdb378327f17125b6f24ffffffffdffffe7fbbdf65bf9fe3f3fffe8484d67ab177837feefc8d07fdcda2db4b3ffffffff7ffff9feef7d96fe7f8fcffffa121219c2c58e05fdb370301f17120b6d24ffffffffdffffe7fbbdf65bf9fe3f3ffe68487fe70b3ffa37f6fdc0d07c5cd96dbc93fffcffef7ecbe1fecf7d96fe6f8fcffe0a121fe002cff08801bc6034000036504220fffe00f8dfb0e07f21df20bb98e3f3fbf68486e77cb1fba3ff6ffd0d9ff5c4b6dbcb3ffffffff7eeff9fecf3d96fe7f8fcfdfba12161bc2cd8e45fdb378301f17120b6d24ffff3ffbdbf6f87f9bdf45bf9be3f3f3fe848487f0b16391ff6cde0c9fc5c482db493ffffffff6ffff9fe6f3d16fe7f8fcfcf9e363219c2c58e05fdb370309f17122b6d64ffff3ffbdbb2f87f93cf45bf9be3f3f3e78c858e70b363817f6cdc0c27c5c48adb593fffcffef6ecbe1fe4f3d16fe6f8fcfcf9e16161bc2cd8e45fdb378301f17122b6d64ffff3ffbdbb2f87f93cf45bf9be3f3f3e6fcfc8670fd638d7f7cdc7e67c7f483df6d3fffcffef6ecbe1fe4f3d16fe6f8fcfcf9bf213f9c3c5fe2dfdbf71f59f1fb60f6db4ffff3ffbdbb2f87f93cf45bf9be3f3f3e6e4e4e67cb97b8f7f7ffd7f47f7e4a3db4f3fffcffef6ecbe1fe4f3d16fe6f8fcfcf9b535359ebd5de3dfffbf33c1fff768b7dbcffff3ffbdbb2f87f93cf45bf9be3f3f3e684848670b163817f6cdc0c07c5c482db493fffcffef6ecbe1fe4f3d16fe6f8fcfcf9a12120082c5800079b060300010120b6020ffff3ffbdbb2f87f93cf45bf9be3f3f3e684800460b043817e68d4080005c082db483fffcffef6ecbe1fe4f3d16fe6f8fcfcf9a00121182858e05f9b330100017120b2d20ffff3ffbdbb2f87f93cf45bf9be3f3f3e6040406608103817e40c40c0005c402db413fffcffef6ecbe1fe4f3d16fe6f8fcfcf92020211c0c18e05fcb370001f17020b2d20ffff3ffbdbb2f87f93cf45bf9b) (
.leaf 24 0xf7defffc5050502a44140e1e9220c3003e1922cc2633feffffefbfefb5fedef9677ffde01fe0b4013400385d02801b821140008360000b08ffa00689e90a0d3215b2081f8f6fefefe5454562ac5178f1ed224cf003f9d22dd2733227fffebffe7ad7ecff96fdbfd1f1f1e810101802040e04010010300006100044040401e006afcd1eb07b3ca42366f3fbfbf6c4c4c678b1738f7f7efc4f07f7c4a2db4f3fffffffffeeffbffcf3f96fe7fcfefefda121219c2c58e05fdb370301f17120b6d24ffffffffffbbfefff3cfe5bf9feff78003bfb80000fc404000681038600032c934387e03002c3048305b0139469e9e3be01de0ee01ee0038fb08001b420d18000b67402e18ffa00689a90a153055b1ac1f8ebff8003aff80000bc40440078103a600032c934187e03002c3848305b1139669e863afcfcf9ebeb219c2e58f05fdb370f19f179b2fed65ffff3ffbdbb2f97f97cf5fff9bebf3f3e7ac87ae70b3eba17f6ddc3c67c5e49fdbd97fffcffef6ecbe5fe5f3d7ffe6fafcfcf9e1e1e1fc2cf8fc7fdb378327f171b7bef65ffff3ffbdbb2f97f97cf5fff9bebf3f3e6a6a6a774b9ebe1ff6ddd3cdfc5e6d7fbc97fffcffef6ecbe5fe5f3d7ffe6fafce000fffe00003f1013001e041e98008cb24d0f1f80c00b0c120c16c04c51a7a18ebf38003afa80000b8404000681038600022c930187e03002c3048305b0131469e863afce000eb2000002c1000001a040e1800082244061f80c00b0c120c16c04c51a7a18ebf3800387800000b0404000681008000002c830187e03002c3048305b0131469e863afce000a9a800002e1010001a040e100008b04c021f80c00b0c120c16c04c51a7a18eb807f83a807f800a3fc22006f083560002d9d009863fe801a27a42854c956ceb0663ae01ce0fe01fe0038ff0a801bc21d58008b67402f18ffa00689a90a153054b1ac198eb807383a807a800a3e820006d08346000249d009863fe801a26a42854c152c6b0663ae01ce0ea012000285800001b020d18000922400618ffa00689a90a153054b1ac198eb80738380078000a3e020006c08040000049c009863fe801a26a42854c152c6b0663ae01ce0a801a800287a08001b420d10000925402218ffa00689a90a153054b1ac198e8707063070707808383f18040060c9801865c319141004800a2e0064c05c30798c0b9fdfdfbe16161bc2cd8e45fdb378301f17122b6d64ffff3ffbdbf6f87f9bff45bffbe7f7f7ee94949672f567817fecdc8c07cddd82df693fffcffef6fdbe1fe6ffd16ffef9fdfdfba121219c2c58e05fdb370301f17120b6d24ffff3ffbdbf6f87f9bff45bffbe7f7f3e79d9c8670f563817f6cdc0c27c5d48adf793fffcffef6ecbe1fe4fbd16ffef9fdfcf9e161219c2c58e05fdb370301f17122b6d64ffff3ffbdbb2f87f93ef45bffbe7f780039d980000f44000006810082000108814383e03002c3048301b0039400e9e39fcfdf9e721679c3cd9e05fdb370309f17362b6de4ffff3ffbdbb2f87f93df45bffb)))) (
.fork 27 0x3f1f070ec1c1c0e020e01c20100083260001970c2450000e006a54d1fa07e34be6266 (
.fork 26 0x3efefad5b9b899532e36fbf81efd5ef60cf8bd4cf39ff7fdffdffabe7fee5cdfb7f9d (
.leaf 25 0xfbfbeb546262654c089befe013e573d833e27523c67fdff7ff7feaf9ffb9737edfe77efee000fbfa00002e1013001e041e980088b24c071f80c00b0e120c1ec44c59a7a18fbfb8002fef80000fc404c0078107a600232c1342c7e03002c3848307b1131669e863efee000b9b800002e1013001e041e900088b04c031f80c00b0e120c1ec44c59a7a18fbfb800286800000b0404000681008000002c030087e03002c3848307b1131669e863efee000189800000200130004001c9000889048011f80c00b0e120c1ec44c59a7a18fbf3fbe6e486e670b1fbab7f6fdc7d47c7e497dbcd7fffcffef7ecbe7fedf3dfffe6fefce000b92000002c1002001a041e1000882044031f80c00b0c120c1ec04c51a7a18fbeb7bd6e266e54ca9fbefe07fed77d833e6f523ce6ffff7ff7fe6f9fef973fef9e77efadef5189899530226fbf804f95cf60cf89d48f19bfffdffdff9be7fbe5cffbe79dfb807f82e007f800a3fc2a006f087540022d95008c63fe801a27a42874c956ceb0663ee01ee0fa01fa0028fe0a801bc21d58008927402718ffa00689e90a1d3254b3ac198fb807b82f806f800e1fc2a006f087560022d9500ac63fe801a27a42874c952ceb0663ee01ee0b801b800287e0a801bc21d50008925402318ffa00689e90a1d3254b3ac198fb807b8280068000a1e020006c080400000494008863fe801a27a42874c952ceb0663ee01ee01800980000260a8000c01c50008805402118ffa00689e90a1d3254b3ac198fb807382e0048000a16008006c087440022481000c63fe801a26a42874c152c6b0663edededd999999d32266fbf814f95ff60cf99d4cf1d3777ffdfff8b7ffaf7ccff679ffb7b7b746262654c089befe013e573d833e27523c64dddfff7ffe2dffebdf33fd9e7fe1e1e1c818181c02060f860100103260061950c6050401e006af891fb0770cbe6306f7ffffff858586f0b363917f6cde0c07c5c48adb593fffffffffffffbffefff96ffffdffffffb535359ebd5de3dfffbf33c1fff768b7dbcfffffffffffffefffbffe5bffff7fffffe84848670b163817f6cdc0c07c5c482db493fffffffffffffbffefff96ffffdffffff1414151a9105e3dfa4b930c00ff648b3d98fffffffffffffefffbffe5bffff7fff3e6d4d48670f5638d7f7cdc4e07c7d482df6d3fffcffefeecbe3ff4fbf16ffefdfffcf9a121219c2c58e05fdb370301f17120b6d24ffff3ffbfbb2f8ffd3efc5bffbf7ffdefed4d0502af4540e1efa30cb003e19a2dc2e3e237ffff95ff7bb7ebdf96f9ffdfff7bf1414140a91050387a48830c00f8648b3098f88dffffe57fdeedfaf7e5be7ff7ff8002d4d00000f4400c0078104a00021080142c3e03002c3848303b1039600e9e3dfcfff9b521359c3c5de2dfdbb71341f1f360b6db4ffff3ffbdfb2f8ffb3df65bffbf7f3ffe684848670b163817f6cdc0c07c5c482db493fffcffef7ecbe3fecf7d96ffefdf7bfffb415340ab95d0387bf8a31c00f8768b30b8cffbffffbeffbed7fb7be59dff) (
.leaf 26 0xfc7c142b070502808300500040020c00000648301140000800a8510668178d279898bf1f031ec1c0c1e020a0fc60100182260060970c6450001e006a54d1fa07e34be6266fc7c0c1b07030180828070804002089800025c309040003001295341e81b0d2e98993f1f001ec1c001e02000f460100182260060920c4450001e006a14d1fa05e249e6266fc7c00037f780000cc004c0050007a600232493434400000002840006811092698983f1f0000c1c0000020001000100002000000920c04100000000a10001a044249a6260fc707c63040706008383a10040040c0001841c119141004800a3e0066c0dc70f98d8bf1a1f14c081c14020e0f86010010126006197086410401c004af8907b0651cba6364fc5c7c7b050702808380300040020c0000041c109141007801abb347e41fce2f9059bf171f1ec0c1c06020e01c2010008126000197082410401e006aecd1f907f38be4166fc5c7c7b000707808383b1804006049801841c019141007801abb347e41fce2f9059bf171f1ec001c00020e0080010000100000107002410401e006aecd1f907f38be4166fc5c7c78000200000080200000000000000014008041007801abb347e41fce2f9059bf17171ec00000002000000010000000000002000410001e006a44d1f807e30be4066fc207c03070707808383f18040060c9801865c31914100000023e0006c09470e98d83f071f0ec1c1c0e020e01c20100083260001970c2450400e006aecd1f907f38be4166fc147c2b050702808380300040020c0000041c109141000800a3b106640fce0f9058bf031f1ec0c1c1e020e0fc6010018126006197086450401e006aecd1f907f38be4166fc0c7c1b03070180838070804002049800065c2090410030012bb341e41b4e2e90593f001fe0de01fe0030ef0a8011c21d58008b47402d107f200489e902193251a3ac1e0fc007f830007f80083bc220047080500000d1c009041fc801227a40864c9468eb0783f001fe0c001e00020e80800110201000001070024107f200489e902193251a3ac1e0fc007c7b000707808383b1804006049801841c019141007801a3b347e40fc60f9059bf001f00de01de0030e70a8010c01d58008b47402d1040000008e80019025183a4160fc007c0300070000838020004000040000041c00904100000023a0006409460e90583f000000c0000000200000001000000000000200041000000008000018004001a4060fbff8002e7f80000bc404c0078107a400232c1340c7e03002c3848307b1139669e863efefefdb9b9b9df2e7efbffdfff5ff7fdf9bdfef3dffffffffffbbfffff7cfffff9ffbfbfbf686868770b1e3e1ff6cdc0c9fc5c6d6fbc97fffffffffeefffffdf3ffffe7fefefefd1898995b0226fbff84f95cf60df89dfaf19ffffffffffbbfffff7cfffff9ffbfbf3e6e6e48670b963cd7f7cdc7e47c7e6c3fb4d7fffcffefeecbe7ff5f3f7ffe6fefefad5b9b899532e36fbf81efd5ef60cf8bd4cf39ff7fdffdffabe7fee5cdfb7f9d)) (
.fork 28 0x3f1f1fdfc1c1c1f020e0fc78103183260071970cf450773ff4fbfcf3fb2ff3cff67e7 (
.leaf 27 0xfc7c7eff070757aa8397f39ec2268d983d8f7ef99341207fd3ebf7c7ec7fcfbff9d9ff1f1f5ec1c1ebe020eafc60114383260061970c6450773e006bfcd3fb27f3cbe63e6fc7c7d7b070787d083a3f1e144ce0c9fc1c65c33d141dcf801aff34fec9fcf2f98f9bf1f1f5ec1c1c9f120e2fc781071c3260071970cf450773e006bfcd3fb27f3cbe63e6fc7c7c7b8f8f0780b3c3f18068160cb80186dc319941007801abf347ec1fcf2f98d9bf1f1f1ee3c1e3e028f8fc601b03832e0061b70c6650401e006afcd1fb07f3cbe6366fc7c7c7b87878790b3e3f1816c1e0c9fc186dc319941007801abf347ec1fcf2f98d9bf1f1f1edfdfc1e033e0ff6014019fbe00ed974d6d50401e006afcd1fb07f3cbe6366fc7c7c7b7f077f80c39ffb8043067df803af5d31b541007801abf347ec1fcf2f98d9bf1f1f1ed9d9d9e322e6ffe014c9dff60ce99f4c65d0401e006afcd1fb07f3cbe6366fc7c7c7b5757578ac797ff80d226cf983b9f7c35b741007801abf347ec1fcf2f98d9bf1f1f1ec1c1c1e020e0fc60100183260061970c6450401e006afcd1fb07f3cbe6366fc7c7c7b070700008380600040000c0000065c309041007801abf347ec1fcf2f98d9bf1f1f1ec1c101802040f040100103000061920c4450401e006afcd1fb07f3cbe6366fc7c7c7b070205008083e1804004089801825c319041007801abf347ec1fcf2f98d9bf1f1f1ec101c18020e0e84010010300006107046450401e006afcd1fb07f3cbe6366fc7c7c7b020705008383e1804004049801865c219041007801abf347ec1fcf2f98d9bf1f1f1e818181c02060f860100103260061950c6050401e006afcd1fb07f3cbe6366fc7c7c79030305800283f1800006009801825c219041007801abf347ec1fcf2f98d9bf1f1f1e01c081e00020fc60000182260060950c6050401e006afcd1fb07f3cbe6366fc7c7c78020707800383f18000060498018654218141007801abf347ec1fcf2f98d9bf1f1f1e008081400020f86000010026006095086010401e006afcd1fb07f3cbe6366fc7c7c03070700008380600040000c0000065c3090410000002be0006c194f2e98d83f1f1c18c1c101802040f040100103000061920c44504012002ab8019b0572c9e6362fc7c6853070205008083e1804004089801825c3190410070012be241ec194b2e98d93f1f171ec1c140a020c01400100083000001920c0450001e006a54d1fa07e34be6266fc7c5c7b07030180828070804002089800025c309040007801a95347e81f8d2f9899bf1f171ec1c001e02000f460100182260060920c4450001e006a54d1fa07e34be6266fc7c5c7b070000008000400040000800000248301040007801a95347e81f8d2f9899bf1f171e008000000000100000000000000090080010001e006a54d1fa07e34be6266fc7c2003070707808383f18040060c9801865c3191410000002ae0006c114b2698d83f1f070ec1c1c0e020e01c20100083260001970c2450000e006a54d1fa07e34be6266) (
.fork 29 0x3f5f5f1ee1e1c1e02cf0fc601a0583260061b70c6653405e006efcd5ff87ffcbe6376 (
.leaf 28 0xfd7d0003afa80000b8404000681038600022c930184c0100003840107a113926989c3f5f1f5eebc1ebe028fafc601b438f3e0069b74c6650773e006bfcd3ff27f7cbe63f6fd7c7d7b87078780a3e3f1806c0e0c980186dc319941dcf801aff34ffc9fdf2f98fdbf401fe0ea01fe0028ff08801bc20d58000b674026107f200489e9021d3255a3ac1f0fd007d03a807a800a3e820006d08346000249d009841dc800027a0087489560e907c3f3fe000e7fe00003f1011001e0402880004b20d0e1f80c00b0e120c1ac44a59a7a60fcfcfcfb878787b0b3e3f19f6c1e0c9fc586def99973227809abff67ed5fcfefbed9bf3f3f3ec5c5c5e8b1e1fc67b001a3260367d7bf6c5cc89e026affd9fb57f3fbefb66fcfcfc7b9f9f0780f7c3f18068160cb80196dc35b973027809abfb67ed1fcf6f9ed9bf3f3f1ee1e1c1e02cf0fc601a0583260061b70c665cc09e026afed9fb47f3dbe7b66fcfc80039f980000f4404000681008200012c8343872020008284820691109669e983f3f1f3ee7c1e7e038f9fc601b03832e0063f70c6e58c89e026afdd9fb17f3fbee366fcfc7cfb87078780a3e3f1806c0e0c980186dc319963227809abf767ec5fcfefb8d9bf201fe0e601fe0038ff08801bc20148000367002e18ffa00689e90a193251b3ac1e0fc807c8398079800e3e420006c080420000d9c00b86322000823a420644946ceb0583f1fff1fc1e1c1fc24e0fc7fd0358327f17197bef457405ff97efef5fbcffbcff7f67fc7ffc7b07ff07809f83f58050160e9801965c35915d017825bbfb57ef1fef2f9ed9bf1fff1ec1e1c1e024e0fc60100583260061970c6457405e096efed5fbc7fbcbe7b66fc7f80037ff80000dc004c0050107a6002324934345c0100243848106b1129269e983f1fe000c1fe000027001100140402800004920d04170040090e12041ac44a49a7a60fc7f800307800000900040004010080000024830105c0100243848106b1129269e983f1fdf1fc1d9c1f322e0fd781439c3a60c719f0cf4d3405ff97efcf5fb8ffbcff6767fc7f7c7f070707c08383f1e040c60c9801c65c33d14d017fe5fbf3d7ee3fef3fd9d9ff1fbf1fc1d5c1eaa1e0fd67b409a3a60f659fbf64d4401ff97afef1fb4ff3cff7f67fc7d7c7b07af07809b83f18040160c9801865c31914d017801bbf357ee1fef2f98d9bf1f5f1ec1e1c1f424e0fc7850358327f071970cf453405e006efcd5fb87fbcbe6366fc7d7c7b072707c48b83f1e040c70c9801c65c33d14d017801bbf357ee1fef2f98d9bf1f1fffc1c1e1fc20e8fc7fd1338327f17197bef4507f3ff4fbfdf3fb3ff3effe7e7fc7c7ffb0707ff8083bff380470e0d98018f5c319141fcf813aff74fecdfcfafb8f9bf1f1ffec1c1e1e020e8fc60110383260061970c64507f3e04ebfdd3fb37f3ebee3e6fc7c7f7f070767cc839bf3e043e70d9831c67c33d341dcffd3eff3cfecbfcf3fd9f9ff1f1fdfc1c1c1f020e0fc78103183260071970cf450773ff4fbfcf3fb2ff3cff67e7) (
.leaf 29 0xff7f6b576762654c889befe053e57bd833e27d33d64dddf7f77fe2d9feb97b3ed9ff7fdfdad5189899530226fbf804f95cf60cf89d48f193777dfddff8b67fae5ecfb67fdff7f00036760000088004c0050007a4002224930144c0100243840107a113926989e3fdf1fded9c1d9e020e6fee010c19f7600e9974c6550773e04ebfcd3ff27f7cbe63feff7c7f7b070707808383f18040060c9801865c319141dcf813aff34ffc9fdf2f98ffbfdadfd5d899d95322e6fbf814f95df60cf99f48f593777dfddff8b67fae5dcfb67fdff6b7f546262654c089befe013e573d833e27523c64dddf7f77fe2d9feb9773ed9ff7fc01fe0d801fe0020ef0a8011c21d50008b474025107f200489e9021d3255a3ac1f8ff007f036007600083982a004300754002241d009441dc801227a0087489560e907e3fbfe000d5fe000037001300140412800084920d0d1f80c00b0e120c1ac44a59a7a68fefefeff575757aac797ff9ed226cf983f9f7efdb773227fffebffe7ed7fcfffffdbffbfbfbfc1c1c1e820e0fc6790018326016197be645cc89ffffafff9fb5ff3fffff6ffefefefc5252552a4497ef9e9224c3983f9b76eda673227fffebffe7ed7fcfffffdbffbfbf1ed5d5c1e031e0ff60140193a600e5970d6d5cc09e0b6afed9fb47f3dbe7b6efefefc7b070707808383f18040060c9801865c31917302782dabfb67ed1fcf6f9edbbfbfb7bfd5d4140ab1051387b48832c00f86dabf0d9c889ffffa57f9fa5fe37fffe6ffefe800357500000c4004c0050004a0002124834347202002c284820691109669e9a3fbf1fbed5c1d5e030e5fee01081936600e3d70c6d58c89e06eafdd9fb17f3fbee36efefc7efb070707808383f18040060c9801865c31916322781babf767ec5fcfefb8dbbfb7bfbfd415d40ab1e50b87b48831c00f874fb32d9cc89ffffaeff9f95ff3bffdd6ffe807f835007f800c3bc2a0047084500020d1c00b463fe801a27a42864c946ceb07a3fa01fa0d401d40030e50a8010801140008347002d18c8800688e908191251b3ac168fe7e7e7f474747888393ff8052264f9833867c319741007ff7ebf3c7ec3fcf3fd9dbff9f9f9fc1c1c1e020e0fc60100183260061970c6450401ffdfafcf1fb0ff3cff676ffdfd8003bfb80000fc404000681038600032c934387e0300083848307b1139669e9c3f601f60ee01ee0038fb08001b420d18000b67402e18ffa00209e90a1d3255b3ac1f0fd7f8003aff80000bc40440078103a600032c934185c0100243848107b1139269e9c3f5f5f5ee1e1e1f42cf8fc785b378327f071b70cf653777e006ffcd7ffa7ffcbe63f6fd7d7d7b272727c48b8bf1e041c73cd801e65d33d14dddf801bff35ffe9fff2f98fdbf5f5f5ec1c1c1f020e0fc78103183260071970cf453777e006ffcd7ffa7ffcbe63f6fd7d7c7bafaf0780bbc3f18068163cf801a6dd31994d017801bbf357fe1fff2f98ddbf5f5f1ee1e1c1e02cf0fc601a0583260061b70c6653405e006efcd5ff87ffcbe6376))))) (
.fork 35 0x3fff1ffeffc1ffe038fffee01bc39f7e00ebf74c6f58ffbe06ebfddbff37f7fbee3fe (
.fork 32 0x3fe0dfe0fe19fe003aff0b801fc21dd8008b67402f1bffe00f8de90e1db25db3ac1f8 (
.fork 31 0x3fe01fe0dc01dc0030e70a8010c01d50008b47402d18ffa00689e90a1d3255b3ac1f8 (
.leaf 30 0xff807f82f006f000e1fc2a006f087540022d9500ac63fe801a27a42874c956ceb07e3fe01fe05e00de0010a70a8000c01c58008a47402d18ffa00689e90a1d3255b3ac1f8ff807f80f802f80060fc2a002f08716002299500ac63fe801a27a42874c956ceb07e3fe01fe01c01fe0010ef0a8001c21d50008b45402918ffa00689e90a1d3255b3ac1f8ff807f8070027000409c2a000300714002291500a463fe801a27a42874c956ceb07e3fe01f00fe01c00038f00a001a001d18008927402f18c0800208e8081d025593a4178ff807b83f806e000e1f82a006f08756002249d00bc63fe801a27a42874c952ceb07e3fe01de0fe01660038d902001b021d18008b62400f18ffa00689a90a1d3055b1ac1f8ff8073e7f8048670e163897f6ccc7467c7e48bcb7d63fecfdae6a4ae74e5d2d7f17effe01ce0fe01ea0038fa0a001b421d18008927402f18ffa00689a90a1d3054b1ac1f8ff807383f804f800e17c0a006f087560022d89003c63fe801a26a42874c152c6b07e3fe01ce0fe012000385802001b021d18008922400f18ffa00689a90a1d3054b1ac1f8ff80738380048000a16000006c080400000488001863fe801a26a42874c152c6b07e3fe01ae0fe00be00383f0a801bc21c58008a67402f18ffa00689e90a1d3254b3ac1f8ff806b03f8026000e0d82a006b00716002209d00bc63de801a27a0287489524e907e3fe017a0fe001400381502801a801c58008a62400f188880068841081c124533ac078ff803583f807b800e3ec28006d087460022d9d00bc63fe800826a42874c156c6b07e3fe008e0fe01fe0038ff0a801bc21d58008b67402f18ffa00689a90a1d3054b1ac1f8ff802103f807a800e3e828006d08746002249d00bc63de800826a02874815246907e3fe00520fe01660038d902001b021d18008b62400f188880020801081c104531ac078ff800c03f8037800e2dc2a006b00716002299d00bc620200082100207009144e901e3fe000e0fe003e00381f02801bc21c58008a62400f18bfa00689010a1c304431ac0f8ff800003f8000000e040080068007060022089003c6202000820002070011046901e3fdfe000d9fe00002700130014041e90008c924d05170040090e12041ec44e49a7a78ff7f7f7f878787d0b3e3f1e16cde0c9fc1c6dc33d94dddfff7fff3dffebfff3fd9ffffdfdfdfd9d9d9f322e6fff814f9dff60cf99f4cf5d3777ffdfffcf7ffafffcff67ffff7f7f7f070707c08383f1e040c60c9801c65c33d14dddfff7fff3dffebfff3fd9ffffdfdfdf1c9c9d539327fbf824f97cf60efedd49f993777ffdfffcf7ffafffcff67ffff7f7f7c6262654c089befe013e573d833e27523c64dddfff7fff3dffebfff3fd9ffffdfdfdf008081500020f8780031002600709508f013777ffdfffcf7ffafffcff67ffff7f7c7b676707808b83fd8050067ed803a65d31954d017825bbf357fe1fff2f98dfbfdfdf1ec1c1c1e020e0fc60100183260061970c6453405e096efcd5ff87ffcbe637e) (
.leaf 31 0xff82ff87f857f82ae7fc2e1eff28f7603e3dbfccbe73fe87fe67aca875e956def77e7fe0bfe0fe15fe0039ff0b801fc21dd8008f67412f1cffa00f89eb0a1d7255b3ad9f8ff827f87f847f808e3fc2e007f287760322dbd00be63fe87fe67a4a874e956def17e7fe05fe0fe2bfe003eff0a801bc61d58008b67402f1bffe0068de90e1db25db3ac1f8ff80ff83f89ff800f7fc2a006f187560023d9d04bc73fe801a27ac2875c956ceb67e3fe01ffffe01fe0ab8ff0a87bbca3d580f8b6ff22f98ffbff6f9edfbfd3bf5b7fc5ffff807ffbf807ff80e3ffbb806f0e75f803ad9d01bd63fef81ba7b76ff4cfd6cfb07fbfe01ffefe01fe0038ff0a801bc21d58008b67402f18ffbe06e9eddbfd33f5b3ec1feff807fe7f807fe70e3ffab7f6fcc7567c7ed9fcbfd63fecfdae7a4ae74edd6dff17effe01ff5fe01ff5338ffeaf81bfb5d7e0cfb6f40ff98ffbdf6d9e9ba7d3a55b7bc5fdff807fd7f807f808e3fc2a006f287560322dbd00be63fef7db67a6e9f4e956def17f7fe01feafe01fea038ff0e801bc29d58008b67402f58ffa206a9ed4b9d33f5b3ec1faff807f9bf807f980e3fc3a806f0a75f8022d9d00bc63feb01b27b769f4cb56ceb07f3fe01fe6fe01fe02b8ff0a803bca3d580e8b6f402f98ffac06c9edda7d32d5b3ac1fcff807f93f807f90ce3fc2a806f2975f8322dbd00be63feb01b27a669f4c956ceb07f3fe01fe0ff63fe003cff0a801bc61f58008b67442f18ffa00689e90a1d3255b3ac1f8ff807f83fd07fa80e3fc3a006f0a7d60022d9d10bd63fe801a27a42874c956ceb07e3fe01fe0ff21fe843cff0a805bc61f59f08b67442f58ffa00689e90a1d3255b3ac1f8ff807f83f87ff800effc2e007f087760023d9d04bc63fe801a27a42874c956ceb07e3fe01fe0fe19fe033aff0b801fca5dd80c8b6f402f98ffa00689e90a1d3255b3ac1f8ff807f83f857f80ae7fc2e00ff28f7603a3dbd04be63fe801a27a42874c956ceb07e3fe01fe0fe01fe0038ff0a801bc21d58008b67402f18ffa00689e90a1d3255b3ac1f8ff807f83f8078000e3e028006c08746002249d00bc63fe801a27a42874c956ceb07e3fe01fe0fe013400385d02801b821d58008b62400f18ffa00689e90a1d3255b3ac1f8ff807f83f8027000e0dc2a006b00716002299d00bc63fe801a27a42874c956ceb07e3fe01fe0f801f80028fe0a801bc21d50008927402718ffa00689e90a1d3255b3ac1f8ff807f83d007d000e3f42a006e084500020d9c00bc63fe801a27a42874c956ceb07e3fe01fe0ea01ea0028fa08001b420d18000927402618ffa00689e90a1d3255b3ac1f8ff807f8398079800e3e420006c080420000d9c00b863fe801a27a42874c956ceb07e3fe01fe0e001fe0028ff08801bc20140000367002618ffa00689e90a1d3255b3ac1f8ff807f8380078000a3e020006c08040000049c009863fe801a27a42874c956ceb07e3fe01fe0dc01dc0030e70a8010c01d50008b47402d18ffa00689e90a1d3255b3ac1f8)) (
.fork 33 0x3fe85fe0ff21fe003cff0a801bc61f58008b67442f1bffe0068df90e1fb25df3ae3f8 (
.leaf 32 0xffa17f83fa27fd44ebffebe06fcd75f803efdd23fc6fff801a37e4387ec977ceb8fe3fe84000ffea00003e1012001a041e180088b24c0f1b80c0020c100c1e804c51a6278ffa07f83ff07ff80e3fffb806f0e7df803afdd31bd63fe801a27e4287cc957ceb8fe3fe5ffe0ff7ffe003fff0b801fc61fd8008f67452f1fffe00f8deb0e1df25fb3ad9f8ff94ffabfd9ffa80f7fc3a006f1a7d60023d9d14bd73fe881aa7bd2e75cfdecfb67ebfe53feafe05fe08b9ff0a87bbc23d58038f67f32f1cffa206a9ef4b9d73f7b3ed9faff94ff83fd9ff800f7fc2a006f187d60023d9d14bc73fe801a27ac2875c95eceb67e3fe53fe0fe05fe0039ff0a801bc21d58008f67412f1cffa00689eb0a1d7257b3ad9f8ff948003fd980000f440080068107860023089143c7202000820082071011846961e3fe51feaff41fea038ff0e801bc29f58008b67442f58ffa206a9ed4b9d33f7b3ec1faff947fabf807f800e3fc2a006f087560022d9d00bc63fe881aa7b52e74cfdecfb07ebfe51fe0ff41fe0038ff0a801bc21f58008b67442f18ffa00689e90a1d3257b3ac1f8ff90ffa3fc87fa30f3fc2a1f6f187d67c62d9fd8bd73fe881aa7ac2e75cdd6cfb67ebfe43fe0ff21fe003cff0a801bc61f58008b67442f1cffa00689eb0a1d7255b3ad9f8ff907fa3fc07fa00e3fc2a006f087d60022d9d10bd63fe881aa7a42e74cdd6cfb07ebfe31fe6fec1fe6038ff1ea01bc29d7e008bf7482f18ffac06cbedda7d36d7bbac1fcff8c7f9bf857f80ae7fc2e00ff28f7603a3dbd04be63feb01b2fb769f4db5eeeb07f3fe31fe6fe01fe0038ff0a801bc21d58008b67402f18ffac06cbedda7d36d7bbac1fcff8c7f83fb7ff800effc6e007f087760023fdd24bc63fe801a2fa42874d95eeeb07e3fe31fe0fe15fe0039ff0b801fc21dd8008f67412f18ffa0068be90a1d3657bbac1f8ff8c0003fb780000ec404c00780072600232c9243c6202000828002070111866901e3fe21fe4fe99fe433aff1ba01fca5dfe0c8bff482f98ffac06cbe99a7d3655bbac1fcff887f93f847f808e3fc2e007f287760322dbd00be63feb01b2fa669f4d956eeb07f3fe11fe2fe41fe2038ff0e801bc29d58008b67402f18ffa00689ed4a1d32d7b3ac1f8ff847f8bf817f802e7fc2a00ef08f5600a3d9d04bc63fe801a27b52874cb5eceb07e3fe11fe0fe47fe0039ff0a801bc21d58008f67412f18ffa00689e90a1d3257b3ac1f8ff83ff87f887f870f3fc2a7f6fd87567c66d9fcafc7fff87fe77acb877e976def77e7fe0ffe0fe3ffe003fff0b801fc61dd8008f67412f1fffe00f8deb0e1df25db3ad9f8ff83ff83f887f800f3fc2a006f187560022d9d00bc7fff803e37ac3877c976ceb67e3fe0e000fe3e00003f1003001e041c98008c22410f1f80c00b0c020c1cc04c11a5878ff837f87f867f84cebfc2e607fe97760326dbd02fe6fff87fe77a4b876e976def17e7fe0dfe0fe19fe003aff0b801fc21dd8008b67402f1bffe00f8de90e1db25db3ac1f8) (
.fork 34 0x3ffa1ff4fe81ff4038fffae01bc31d7e00ebf7486f18ffbc06cbf99a7f3655fbae3fc (
.leaf 33 0xffe37fc7f807fc40e3ffab606fcc756003ed9d03fc6fffc7fe77e4b87ee977def9fe7ff8dfe0fe01fe0038ff0a801bc21d58008b67402f1bffe00f8df90e1fb25df3ae3f8ffdfff83f8fff800fffc2e007f187760023d9d04bc7fff803e3fac3877d97eeeb67e3ff7bffffe15fe0ab9ff0b87bfca3dd80f8f6ff32f9cffbffffbeffbfd7ff7bffddffffdefffc7052702a449c2e1e9320f3403e3937cca673feffffefbfeff5ffdefff77ffff7bffefe15fe0039ff0b801fc21dd8008f67412f1cffbe0febefdbfd77f7bbed9feffdeffd7f857f808e7fc2e007f287760323dbd04be73fef7ff6faee9f5f95efef77f7ff7bfe6fe15fe02b9ff0b803fca3dd80e8f6f412f9cffac0fcbefda7d76d7bbad9fcffdeff83fddff800f7fc2e007f187f60023d9d14bc73fe803e2fac2875d95eeeb67e3ff7bfe0fe15fe0039ff0b801fc21dd8008f67412f1cffa00f8beb0a1d7657bbad9f8ffdedefff850502ae4540e1efa20f3603e39abcc3e72227fffe91fe7f17f9cfff71ffff7b7bf1c14140a91050387a4883cd00f8e48f3099c889ffffa47f9fc5fe73ffdc7fffde8003f8500000e4400c0078007260023089043c7202002c28082071111866961e3ff79ffffe11fe0238ff0b801fca1dd80c8b6f402f98ffbffffbedfbfd3ff7bffc5ffffdc7ffbfd07fa80e3fc3a006f0a7d60022d9d10bd63fef81bafb76ff4dfdeefb07fbff71ffefe15fe02b9ff0b803fca3dd80e8f6f412f98ffbe06ebeddbfd37f7bbec1feffdc7ffbf807f800e3fc2a006f087560022d9d00bc63fef81bafb76ff4dfdeefb07fbff71ffee001e00028f808001b020100000127002618ffbe06ebeddbfd37f7bbec1feffdc7f83f807f800e3fc2a006f087560022d9d00bc63fe801a2fa42874d95eeeb07e3ff4bff9fe01fe0838ff0a879bc21d58018b67f22f1cffb3ffb9eb2b9d7b75b7fddfbffd2ff83f807f800e3fc2a006f087560022d9d00bc73fe803e27ac2875c956ceb67e3ff41ff8fe01fe0038ff0a801bc21d58008b67402f18ffb206a9e90b9d3375b3ec1faffce7fdff857f80ae7fc2e00ff28f7603a3dbd04be63fef7ff6fb7e9f4fb5efef17f7ff29ff5fe11fe0238ff0b801fca1dd80c8b6f402f98ffbdffdbe9ba7d3e55bfbc5fdffca7f83f847f800e3fc2e007f087760022d9d00bc63fe803e2fa42874d956eeb07e3ff21ff4fe01fe0038ff0a801bc21d58008b67402f18ffbc06cbe99a7d3655bbac1fcffc27fc7f807f800e3fc2a006f087560022d9d00bc63fec7fe67a4a874e956def17e7fed6000ffee00003f1012001a041e18008cb24d0f1f80c0020c120c1ec04e51a7a78ffa38003fff80000fc404c0078107a600232c9343c7e03002c3048307b0131469e9e3fe85fe0ffebfe003eff1a801bc61f58008bf74c2f1bffe0068df90e1fb25df3ae3f8ffa17f83fc87fe50f3ffab616fdc7d67c3ed9d13fd6fff801a37e4387ec977ceb8fe3fe85fe0ff21fe003cff0a801bc61f58008b67442f1bffe0068df90e1fb25df3ae3f8) (
.leaf 34 0xfffc7ffb87078780a3e3f1806c0e0c980186dc319963fef81baff76ffcdfdfefb8ffbfff1fe0ffc1fe0038ff1a801bc21f58008bf74c2f18ffa0068bf90a1f3657fbae3f8fffc7c7bff070780e3c3f98068067cf803a6dd31bd63027809abf367fc1fdf6f98dfbfff1f1ee1c1c1e028f0fc601a0183260061b70c6658c09e026afcd9ff07f7dbe637efffc0003ff000000e0404800680078600222c9303c6202000828402078111966989e3ffefffdffb9ffdf3efffbffdfff5ffffdfbfffeffdffffffffffbbfffff7dffffffffffb8003fee00000f8404c0078107a600222c9303c7e03002c3848307b1131669e9e3ffdffe0ff67fe003dff0a801bc61f58008f67452f1fffe00f8dfb0e1ff25ff3afbf8fff78003fd980000f440080068107860023089143c7e03002c3048307b0139469e9e3ffcfff9ff21ff9c3cffeadfdbf71f59f1fb67f6ff5ffff3ffbdfb2f9ffb7df7ffffbfff3ffe784878670b3e3a17f6cdc0c07c5c49edbd97fffcffef7ecbe7fedf7dffffefffcffe0ff3ffe003fff0b801fc61fd8008f67452f1fffe00f8dfb0e1ff25df3afbf8fff3ff83fc87f800f3fc2a006f187d60022d9d10bc7fff803e37ec387fc977cebefe3ffcfcf9ff21219c3c58e25fdb371f19f1f922f6df5ffff3ffbdbb2f9ff97cf5ffffbfff3f3e784848670b163817f6cdc0c07c5c48adb597fffcffef6ecbe7fe5f3d7fffefffcfce0ff2120003c5802001b061f18008922440f1fffe00f8dbb0e1ff05cf1afbf8fff38067fc800670f043897f68d47867c7e08bdb7d7e034fecf048b67b25b157df9efffce000ffea00003e1012001a041e180088b24c0f1f80c00b0c120c1ec04c51a7a78fff38003fcf80000fc400c0078107a60023089143c7e03002c3048307b0131469e9e3ffce000ff2000003c1002001a041e18008822440f1f80c00b0c120c1ec04c51a7a78fff3800384800000b04000006810080000008810187e03002c3048307b0131469e9e3ffc1ff8ff01ff8038ffeac01bc31f5800eb67446f58ffb206a9f90b9f3375f3ee3fafff07f83fc07f800e3fc2a006f087d60022d9d10bc63fe801a27e4287cc957ceb8fe3ffbdff71c9c9d539327fbf824f97cf60efedd49f99bfffdffdffdfe7fbedfffbe7fdffeb8003faf80000fc404c00781072600232c9243c7e03002c3848307b1131669e9e3ffadff5fe99ff533afffbf81ffb5dfe0cfbff48ff9bfffdffdff9be7fbe5dffbe7fdffeb7fd47262754c489fefe013e573d833eb7523e66ffff7ff7fe6f9fef977fef9ff7ffadfe0fe99fe003aff1b801fc21dd8008bf7482f1bffe00f8ff90e1fb65dfbae3f8ffeb6b57fa62654ce8dbefe07be573f833e2fd23fe6fdff7ff7fe2f9feb9737ed9ff7ffadad51c9899531226fbf804f95cf60cf89d48f99bf7fdffdff8be7fae5cdfb67fdffeb0003fa600000e8404c00780072600222c9203c6e03002c3840307a113166989e3ffa1ff4fe81ff4038fffae01bc31d7e00ebf7486f18ffbc06cbf99a7f3655fbae3fc)))) (
.fork 37 0x3fffe520fffe04003f1113001e041e98008ef24d0f1f88c00b0e130c1ed44f79afa78 (
.fork 36 0x3fffe015fffe00023f1013001e0c1e980c8cba4d0f9f80ddfb5e12bc7ecc4e5db7e7d (
.leaf 35 0xffff802bfff80280fc405c0078127a600232c9343d7e03082cb859367b17b9679e9ebfffe006fffe00603f1017201e049ebe008cb24d0f1f80cc0b4e16dc7ec4ce59a7a7cffff801bfff8000afc404c00f830fa603a32e9343e7e03302d385b71fb1339669e9f3fffe004fffe00433f1013201e0c5ebe0c8cba4d0f9f80cc0b4e129c7ec44e59a7a7cffff8003fffd8800ff604c007c187e600236c9343c7e03002c3848307b1139669e9e3fffe000ffff40a03fd017001e049f98008db24d0f5f80c00b0e120c1ec44e59a7a78ffff8003fffc8210fd604c017c187e67c236c9343d7e03002c3848307b1139669e9e3fffe000fffe1e003f1713801ec41ed8008ef24d0f1f80c00b0e120c1ec44e59a7a78ffff8003fff8600cfc584e007b317b603232e9343e7e03002c3848307b1139669e9e3fffe000fffe1402bf1513803e8c3ed80e8efa4d0f9f80c00b0e120c1ec44e59a7a78ffff8003fff80000fc404c0078107a600232c9343c7e03002c3848307b1139669e9e3fffe000ffe000003c1012001a041e180088b24c0f1f80c00b0e120c1ec44e59a7a78ffff8003fcd00000f4400c0078107a60023089143c7e03002c3848307b1139669e9e3fffe000fe9c00003b1013001e001c98008cb2490f1f80c00b0e120c1ec44e59a7a78ffff8003e7e00000b8404c0078107a400222c9301c7e03002c3848307b1139669e9e3fffe000f5f400003d1013001e0412800084b20d0f1f80c00b0e120c1ec44e59a7a78ffff8003afa80000b8404000681038600022c930187e03002c3848307b1139669e9e3fffe000e7e600003d1010001a0402080004b20d0e1f80c00b0e120c1ec44e59a7a78ffff800387f80000bc40440078100a000012c834187e03002c3848307b1139669e9e3fffe000e1e000002c1010001a0402000000b20c061f80c00b0e120c1ec44e59a7a78ffff800377700000cc004c0050007a4002324934347e03002c3848307b1139669e9e3fffe000bdbc00003f1013001e041e90008cb04d0b1f80c00b0e120c1ec44e59a7a78ffff80017b7800004c004c001000726002324924347e03002c3848307b1139669e9e3fffe0003ebe00001f1013000e041c98008cb0490b1f80c00b0e120c1ec44e59a7a78ffff800077f800005c004c0010107a4002324134247e03002c3848307b1139669e9e3fffe0001c9c00001300130004001c90008c9049091f80c00b0e120c1ec44e59a7a78ffff7fffff67ffccebffffe07fef7ff833effd33ff6ffffffffff7fffefffffff9ffffffdfffe1c1e1f028f8fc781b3383260071b70cf65bfffffffffdffffbffffffe7ffffff7ffc7262754c489fefe013e573d833eb7523e66ffffffffff7fffefffffff9ffffffbfffffd5ffeab9ffffe7bfcbbffe0fefffff6fdcffbffffbfffbff7ff7ffffffffffd7ffb878787d0b3e3f1e16cde0c9fc1c6dc33d96ffff81bbff77ffedfffefb8ffbfff1ffeffc1ffe038fffee01bc39f7e00ebf74c6f58ffbe06ebfddbff37f7fbee3fe) (
.leaf 36 0xffff942bfffd0280ff405c0078127e600236c9343d7e03082cb859367b17bd679e9ebfffe50afffe00003f1013001e041e98008cb24d0f1f80c20b2e164d9ec5ef59e7a7affff9403fffd0000ff404c0078107e600236c9343c7e03002c3848307b113d669e9e3fffe428ffff208c3f581307df061f99f18db2ff0f5f88c20b2e130d9ed56e79efa7affff9083fffc8000fd604c007c187e600236c9343c7e23002c384c307b5139e6be9e3fffe408ffff00803f5013001e041f98008db24d0f5f80c20b2e120d9ec56e59e7a7affff8c1bfffb0180fec07c8078127af80232dd34bc7e03302d395b71fb1b3d6e9e9f3fffe306fffe1402bf1513803e8c3ed80e8efa4d0f9f80cc0b4e56dc7ec6cf5ba7a7cffff8c1bfff80000fc404c0078107a600232c9343c7e03302d395b71fb1b3d6e9e9f3fffe300fffede003fb71b801ec41ed8008ef74d2f1f80c00b0e520c1ec64f5ba7a78ffff8c03fff85000fc544e007a107b60023bc9343c7e03002c3948307b193d6e9e9e3fffe204fffe98433f361ba01ecc5efe0c8cbf4d2f9f80cc0b4e529c7ec64e5ba7a7cffff8813fff84008fc504e007a307b603232e9343e7e03302d394a71fb19396e9e9f3fffe102fffe40203f9017001e049e98008cb24d0f1f80c00b0e164c1ec4cf59a7a78ffff840bfff81002fc444c00f810fa600a3bc9343c7e03002c3859307b133d669e9e3fffe100fffe46003f9113001e041e98008ef24d0f1f80c00b0e120c1ec44f59a7a78ffff8387fff88070fc604c7f7cd87a67c672cbfe7c7eff87fe7c4cb87bf139f6ffbe7fffe0e0fffe3e003f1f13801fc61ed8008ef24d0f1fbfe00f8f130e1ef44e79afaf8ffff8383fff88000fc604c007c187a600232c9343c7eff803e3c4c387bd139e6bebe3fffe0c1fffe18133f1613981efc5ed80c9cba4d9f9fb7e1ff9f122e1eec4e5db7ef9ffff8303fff86000fc584e007b107b600232c9343c7edf803e3c48387b9139669ebe3fffe0a1fffe140abf151387be8c3ed80f8efaff0f9f88c1ff9e132c1edc4e7dbfe79ffff8283fff85000fc544e007a107b60023bc9343c7e23003e384c307b5139e6be9e3fffe081fffe10023f1413801e8c1ed80c8cba4d0f9f80c1ff9e122c1ecc4e5db7e79ffff8103fff8a800fc684c007d187a600232c9343c7edf802c3c48387b9139669ebe3fffe020fffe26003f1913001f061e98008ef24d0f1f88c00b0e130c1ed44e79afa78ffff807ffff8002afc404c1ef830fa603e32ebfc3e7e037fedf85bf7fb37b977df9fffffe01efffe01e03f10f7601e059ebe00ecb24d4f5f80de0b6e16ddfec5ee59e7a7effff807bfff80000fc404c0078107a600232c9343c7e03782db85b77fb17b9679e9fbfffe019fffe019c3f10f35fde351e99f1fcb2ffdf5f80d3fb3e122d9ecd6e5df7e7bffff8057fff8054cfc43cde078f57af833f2e9377e7e0377ed784af1fb313976df9f7fffe015fffe00023f1013001e0c1e980c8cba4d0f9f80ddfb5e12bc7ecc4e5db7e7d)) (
.fork 38 0x3ffff8c0fffe00003f1013001e041e98008cb24d0f1ff7e00f8fba0e1fe45ed9a7bf8 (
.leaf 37 0xffffdf83fff8f800fc7c4e007f187b60023bc9343c7eff803e3d4c387bd93deebebe3ffff7bffffe140abf151387be8c3ed80f8efaff0f9f88dffffe57fdfedfef7fffe7fffffdefc7270502a4c144e1e9220f3403e3b63ec267e237ffff95ff7fb7fbdffff9ffffff7befffe14003f1513801e841ed8008ef24d0f1f88de0fee57ddfed7ef7befa7effffded7fff85008fc544e007a307b60323be9343e7e2377ff794ef1fb793dfeff9f7ffff7a6fffe1402bf1513803e8c3ed80e8efa4d0f9f88cc0fce57dc7ed6cf7bafa7cffffde83fffdd800ff744e007e187f60023fc9343c7e23003e394c307b593deebe9e3ffff7a0fffe14003f1513801e841ed8008ef24d0f1f88c00f8e530c1ed64f7bafa78ffffde7ffff84008fc504e007a307b603232e9343e7e037ffff95bf7fb3fbd7fdf9ffffff71effff40a03fd017001e049f98008db24d0f5f80de0b6e56ddfec7ef5be7a7effffdc7bfff8500afc544e00fa30fb603a3be9343e7e03782db95b77fb1fbd6f9e9fbffff71efffe00003f1013001e041e98008cb24d0f1f80de0b6e56ddfec7ef5be7a7effffdc7b87800000b0404000681008000002c830187e03782db95b77fb1fbd6f9e9fbffff700fffe00003f1013001e041e98008cb24d0f1f80c00b0e520c1ec64f5ba7a78ffffd2e7fff80020fc404c1e78107a600632cbfc3c7e234ffef84cb67b75b9f7ff9efffff4a0fffe00003f1013001e041e98008cb24d0f1f88c00f8e130c1ed44e79afa78ffffd063fff80000fc404c0078107a600232c9343c7e03482cb848367b15b9679e9ebffff397fffe1402bf1513803e8c3ed80e8efa4d0f9f80ddffde56fc7ececf5fb7e7dffffca57fff84008fc504e007a307b603232e9343e7e0377ff794af1fb39397edf9f7ffff280fffe10003f1413801e841ed8008cb24d0f1f80c00f8e520c1ec64e5ba7a78ffffc853fff80000fc404c0078107a600232c9343c7e03702d394a71fb19396e9e9f3ffff091fffe00003f1013001e041e98008cb24d0f1f80d1ff9e122c1ecc4e5db7e79ffffa103ffffa800ffe86c007d187e600236dd34bc7fdf802c3ee8387f917b669efe3fffe840ffff21943f58f3585f371f99f0fdb24ddf5ff7e00b0fba0e1fe45ed9a7bf8ffffa103fffc8000fd604c007c187e600236c9343c7fdf802c3ee8387f917b669efe3fffe840fffe89513f32fb781e755ebe00fcb74dff1ff7e00b0fba0e1fe45ed9a7bf8ffffa003ffff0780ffc3fd8078167ef803b6dd35bd7f03002c3ae8307f117b669ede3fffe5e0ffff7e003fdf13801fc61fd8008ff24d0f1fbfe00f8f130e1ef44f79afaf8ffff94abfffd9a80ff645c007c1a7e60023fc9343d7e23082cb85d367b57bde7be9ebfffe52afffe0408bf111307be043e98038ef2ff0f1f88c20b2e174d9ed5ef79efa7affff9483fffd9800ff644c007c187e60023fc9343c7e23002c384c307b513de6be9e3fffe520fffe04003f1113001e041e98008ef24d0f1f88c00b0e130c1ed44f79afa78) (
.fork 39 0x3fffffffbdbdbddfbf7ffbffffff7ff7fffffdfffbdffffffffffffffffffffffffff (
.leaf 38 0xfffffffc7272756e4c9feffe93e5f3d83ffb77efe67ffffffffffffffffffffffffffffffffeffffffe03fffffe01fc79ffe00eff74d6f5ffffe0fefffdffff7fffbefbfefffffffb87878780b3e3f1806c1e0c980186dc31997ffff83fbfff7fffdfffefbeffbffffff9ffffff9c3ffffbdfdff71fd9f1fff7ffff5ffff3ffbffb2f9fff7fffffffbffffffd7fffffd4cffffefe07ffd7ff833fffd37fe7ffff7ff7feef9fff97ffeffff7ffffff51c9c9d531327fbf804f95cf60cfedd49f99ffffdffdffbbe7ffe5fffbfffdffffff83fffff800fffc6e007f187f60023fdd34bc7fff803e3fec387fd97feebefe3fffffe0ffff34003f5d13801f861fd8008ff24d0f1fffe00f8ffb0e1ff65ffbafbf8ffffff83fcd7f800f7fc2e007f187f60023d9d14bc7fff803e3fec387fd97feebefe3fffffdfffffd9f33ff6fff81efddffe0cfdbf4dffdff7fffffffeffffefffdff7fffffffff7f878707c0b3c3f1e068d60c9801c6dc33d97fdffffffffbffffbfff7fdfffffffffdf1c9c99531326fbf804f95cf60cfc9d49f99ff7fffffffeffffefffdff7ffffffffeffffff57aaffd7ff9efa36fff83fbffffdbf7f237ffffbfff7ff7fffffffdfffffff5ee1e1e1f42cf8fc785b378327f071b70cf65ff7fe0b6ffedfffe7ffdbe7bfefffffc7bffff0780ffc3fd8078167ef803b6dd35bd7f03782dbbfb77ff1fff6f9edfbfffff1ee1e1c1e02cf0fc601a0583260061b70c665fc0de0b6efeddffc7ffdbe7b7efffffc03ffff0000ffc06c0078107e600236dd34bc7f03002c3be8307f197f6e9ede3ffffefdffffb9df3f7efbffdfff5ffffdfdbfffffdffffffffffbbfffff7effffffffffff783fffd9800ff644c007c187e60023fc9343c7fff803e3eec387fd17fe6befe3ffffcf9ffff219c3f58f35fdf371f99f1fdb2ffdf5ffff3ffbfbb2f9ffd7efdffffbfffff3e787848670b163c17f6cdc0c07c5c6cafb597fffcffefeecbe7ff5fbf7fffefffffce0ffff3e003f5f13801fc61fd8008ff24d0f1fffe00f8fbb0e1ff45ef9afbf8fffff383fffc8000fd604c007c187e600236c9343c7fff803e3eec387fd17be6befe3ffffc18ffff01803f50f3401e051f9800edb24d4f5fc0d20b2eba0d9fc57ed9e7b7afffff003fffc0000fd404c0078107e600236c9343c7f03002c3ae8307f117b669ede3ffffbd71c9c9d539327fbf824f97cf60efedd49f99ff7fdffdffefe7feedfdfb7ffdffffeb57fffa654cfcdbefe07bf57bf833f2fd37fe7fdff7ff7feaf9ffb97b7edfff7ffffad51c9c99531326fbf804f95cf60cfc9d49f99ff7fdffdffabe7fee5edfb7ffdffffeb03fffa6000fcd86e007b107b600232dd34bc7fdf803e3fe8387f997b6e9efe3ffffa14fffe81403f30fb601e051ebe00ecb74d6f1fc0dc0b4efa9c7fc65edba7b7cffffe347fff80440fc43cd6078d47a6003f2c9377c7fdfc7fe7ee8b87fb17b76dffe7ffff8c0fffe00003f1013001e041e98008cb24d0f1ff7e00f8fba0e1fe45ed9a7bf8) (
.leaf 39 0xfffffffffffff82afffc6e1eff38ff603e3ffffcbe7fffffffffffffffffffffffffffffffffffffe1fc3ff8ff7fdf379fbff1fdb7ffff5fffffffffffffffffffffffffffffffffffffcd67afd77cf7ffefcff67ffffebff7f7ffffffffffffffffffffffffffffffffffffe9d5bbf37fbffbefd7efe0ffeffffff9ffffffffffffffffffffffffffffffffffff87fff0f3fffbff6fde7dffc7efdffbfd7fffffffffffffffffffffffffffffffffff35ff9ebdffebdfffff3fd9ffff6ff7ffdfffffffffffffffffffffffffffffffffffa77fd6eefffeffeffedf7f83fffffeffe7ffffffffffffffffffffffffffffffffff9f9f9ff2efeffffdfffdff7fdf9bffef7dffffffffffffffffffffffffffffffffffd7d7d7faf7f7fffffefecf9fffdffeffff7fffffffffffffffffffffffffffffffffe1e1e1fc2cf8fc7fdb378327f171b7bef65ffffffffffffffffffffffffffffffffff777777eecf9ffffed3e7ffd83fff7ffff77fffffffffffffffffffffffffffffffffbdbdbddfbf7ffbffffff7ff7fffffdfffbdffffffffffffffffffffffffff))))))⟩

def decodeBank (dict : PackedSeq) : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, packed =>
    if packed = 0 then []
    else BitVec.ofNat 274 ((expanded.at ((packed % 4096) - 1)).getD 0) :: decodeBank dict n (packed / 4096)

def tableFrom (dict : PackedSeq) (banks : ℕ → PackedSeq) (t : ℕ) (ws : List W) : Bool :=
  match encodeBank dict ws with
  | none => false
  | some key =>
    match findKey (banks t) key with
    | none => false
    | some _ => ws == decodeBank dict 11 key

theorem tableFrom_sound (dict : PackedSeq) (banks : ℕ → PackedSeq) (t : ℕ) (ws : List W)
    (h : tableFrom dict banks t ws = true) :
    ∃ i key : ℕ, (banks t).at i = some key ∧ ws = decodeBank dict 11 key := by
  unfold tableFrom at h
  split at h
  · simp at h
  · next key e =>
    split at h
    · simp at h
    · next i hk => exact ⟨i,key,findKey_sound _ _ _ hk,beq_iff_eq.mp h⟩

def blockCheck (dict : PackedSeq) (banks : ℕ → PackedSeq) (t start count : ℕ) : Bool :=
  (List.range count).all fun i =>
    closedState (tableFrom dict banks) t (decodeBank dict 11 (((banks t).at (start+i)).getD 0))

theorem blockCheck_sound (dict : PackedSeq) (banks : ℕ → PackedSeq) {t start count i key : ℕ}
    (h : blockCheck dict banks t start count = true) (ilo : start ≤ i) (ihi : i < start+count)
    (hk : (banks t).at i = some key) : closedState (tableFrom dict banks) t (decodeBank dict 11 key) = true := by
  have idx : i-start ∈ List.range count := List.mem_range.mpr (by omega)
  have result := List.all_eq_true.mp h _ idx
  have back : start+(i-start) = i := by omega
  simpa [back,hk] using result


set_option maxRecDepth 16000 in
def dict : PackedSeq := ⟨1260, 64, 0xffffffffffffffff, .fork 20 0xdb6b6f5462637d4c (
.fork 10 0x34de9cfc5050502a (
.fork 5 0x303030400000040 (
.fork 2 0x7ffc0004d67a (
.fork 1 0x5e8000005000 (
.leaf 0 0x5c7800000000000052e40000002000004a5400004008000021000007a800000021000004865000002100000225440000200000070780000014a80000102200001480000598000000142800050280000010a00004823000000c180003018000000c180000500a00000c0000037800000008100002610c0000038400008070000003800000f800000003040000604c000002840000502a0000007c0000002a00000078000007800000006400000670000000540000054c000000038d88000000000003880588000000000305050280000000028484821000000000787800000000000078007800000000006060600c000000005050500a0000000000000000) (
.leaf 1 0x7ffc0002756e00007ff80007ff8000007ff40007ff7c00007fe40007fe7000007fe40007867000007fd40007fd4c00007f800007f80000007f7c000767cc00007efc000757aa00007c7c000707f000007c780007078000007c000007000000007bf40006e77c00007bf40006877000007bf40002656c00007be40006e670000073e40007ae70000073e4000787f0000073e40006a774000073e4000486700000738000048000000070600004060000006bd40002e57c00006bd40002756e00006b7c0002656e00006b740002677c00006b540002654c00006b00000260000000685000020500000063440000044000005efc0000502a00005e8000005000)) (
.fork 3 0x63004400000440 (
.leaf 2 0x5edefc0050502a005e807c0050002a005e800000500000005c0078000000000052806400000020004a0054004000080021000007a800000021000004800650002100000220054400200000070007800014802800100022001480000598000000140028050002800010802004800230000c001803000180000c00180050000a000c000003780000000800100260010c00038004008000700003800000f80000000300040060004c000280040050002a00007ffc0007fff000007ffc0007fe7a00007ffc0007fd6e00007ffc0007f82a00007ffc0007e7fc00007ffc0007d7fa00007ffc000787f000007ffc000777ee00007ffc0006f77e00007ffc0004d67a) (
.fork 4 0x7f807c0270056e (
.leaf 3 0x7f807807f80780007f807407f8077c007f806407f80670007f806407800670007f805407f8054c007f800007f80000007f007c076007cc007e807c075007aa007c7c7807070780007c007c070007f0007c007807000780007c000007000000007b807406e0077c007b807406800770007b80740260056c007b806406e006700073f3e4048486700073806407a8067000738064078007f00073806406a00774007380640480067000738000048000000070006004000600006b805402e0057c006b80540270056e006b6b540262654c006b007c0260056e006b00740260077c006b00540260054c006b00000260000000680050020005000063004400000440) (
.leaf 4 0x303000060600000030003006000600002de82fc5050502a0282defc5050502a028282847878502a028282847850782a028282847070702e028282845050502a02828284000000200282800050500000028002805000500002020204404040080101010080808050010101002020204401010000a8a8000001000100a800a8000080808080808030008080801010102200808000989800000080008098009800007fff8007fff800007f807c07f807f0007f807c07f8067a007f807c07f8056e007f807c07f8002a007f807c07e007fc007f807c07d007fa007f807c078007f0007f807c077007ee007f807c06f0077e007f807c04d0067a007f807c0270056e)))) (
.fork 7 0x1c00000178000000 (
.fork 6 0x3f383e484808670 (
.leaf 5 0x383fc78f8ff07800383f3e48084867003838384f8f8f82a03838384f8f8d07a03838384f8f8807003838384f8f8706e03838384f8d0f87a03838384f880f87003838384f870f86e03838384f0f0f07e03838384e0e0e07c03838384d0d0d07a0383838480808070038383847070706e03838380f8f8f80003838304f8f8604c03838284f8f8502a038382847070502a03838000f8f80000038380008080000003830384f860f84c03828384f850f82a038283847050702a03828284f850502a03807f80f807f80003800380f800f800038003808000800003800000f8000000036b03546260654c03036b546062654c030303046060604c0303030400000040) (
.leaf 6 0x1b0b0b146262614c187f800067f80000186b08546262654c18086b546262654c180808107272710e180808106262610c1808081002020100180800006260000018007f806007f8001800080060026000168e8e9c5050502a145e8c7c5050502a140c5efc5050502a140c0c185050500a140c0c1800000000140c00005050000014000c00500050001008081040404008087f80012ff8000008007f812807f800080000012b280000080000012803280008000001030301800800000022222104040404090101008004040408101010020404000119180000040004011801180003ff8000fff8000003fc03f8ff00ff8003f3f3e48484867003f383e484808670)) (
.fork 8 0x1c7c7c7907070780 (
.leaf 7 0x1c7c0c79070307801c738c657c837e701c5c0c79030301801c1c0c39070303801c0c7c79030707801c0c73e57b7c86701c0c5c79030301801c0c1c39030703801c0c0c79030307801c0c0c197b7b780a1c0c0c197b7b01801c0c0c197b7a710e1c0c0c197b78500a1c0c0c197b0379801c0c0c197a73790e1c0c0c197853780a1c0c0c197373718e1c0c0c196363618c1c0c0c195353518a1c0c0c19030301801c0c0c187272710e1c0c0c117b7b790c1c0c0c017b7b78001c0c08117b7a610c1c0c00017b7800001c0c0001030000001c080c117a63790c1c007f817807f8001c007f810007f8001c000c01780378001c000c01000300001c00000178000000) (
.fork 9 0x249414ab9d059a80 (
.leaf 8 0x249094a39c859a30249094a384858230249090a39c84823024807f839807f800248014839805980024801480100010002480000398000000247c147b0705078024147c7b050707802414142b05050280241414280000000024140003050000002400140300050000239393a68484827020f390e6848486702090f3e684848670209090a38d8c8230209090a38c858a30209090a3858582b0209090a284848230209090a0000000202090800284800000208010828004800020101022040402001fff8001fff800001f8f8f9d838381f01f8f8001fbf800001f807f81f807f8001f800f81f803f8001c7f80017ff800001c7f800107f800001c7c7c7907070780) (
.leaf 9 0x349cdefc5050502a349c9cb85050502a27978003fdf8000027801783f805f8002717172f656562cc269696ac5050502a24ff80039ff8000024eb14d79a659d4c24dedefc1050502a24de94fc1050102a2494eb579d9a654c2494defc1010502a249494ab9d9d9822249494ab9d9d82b0249494ab9d9c9232249494ab9d981022249494ab9d859ab0249494ab9c959a32249494ab98159822249494ab959592b2249494ab858582b0249494ab151512a2249494aa94949232249494a810101022249494a39d9d9a30249494839d9d98002494942b9d9d0280249490a39d9c8230249490a385848230249480039d9800002494800010100000249414ab9d059a80))))) (
.fork 15 0xb6d2dee450005020 (
.fork 12 0x496b6b542262654c (
.fork 11 0x49002383a807f800 (
.leaf 10 0x49002103a807a800490021002002200049000003a8000000487f800307f80000487c207b0707078048207c7b0707078048202003070707804820200002020500482000030700000048007f830007f800480020030007000043f3a3e68484867043a3f3e68484867043a3a3868484867043a3a384808084704173a16684848670412173e684848670412121028484865041212100000004404121000284800000410021028004800040202002040406003cff8003fff800003c9c8003fff800003c807f83f807f8003c801c83f807f8003c7c1c7b070707803c1c7c7b070707803c1c1c3b070703803c1c1c3903030180389898b2e6e6e33c34de9cfc5050502a) (
.leaf 11 0x496b21542262254c4963214422222544495ea17fa857a82a49358003afb8000049238003aff80000492321042262254c49216b542222654c492163442222254449215effafa8502a492123042222654c492121542222254c49212103afafa80049212103afaf87d049212103afac865049212103afaa254449212103af87afd049212103ac87ae5049212103aa27ad4449212103a7a7a7d449212103878787d049212103272727c449212102a6a6a754492121002222254449212003afaf078049210003afa80000492100002220000049202103af07af8049007f83a807f80049007f802007f80049007383a807a80049003583a807b80049002383a807f800)) (
.fork 13 0x5faf8003fff80000 (
.leaf 12 0x5f802f83f807f8005d7f8003fff800005d2d0003fff800005d007f83f807f8005d002d03f807f8005c7c2c7b070707805c2c7c7b070707805c2c2c1b070707805b2b2b146262654c596b29546262654c59296b546262654c592929106262654c552d2d1ad4d4d65a4bff8003fff800004ba38003fff800004ba38003afa800004ba38000faf800004b807f83f807f8004b802383f807f8004b802383a807a8004b802380f802f8004b6b23546262654c4b236b546262654c4b2323046262654c4b232304222225444aa2a287575757aa49a18003bfb8000049802183b807b800497f8003aff80000497f800027f8000049738003afa80000496b6b542262654c) (
.fork 14 0xa2d2d2e400000020 (
.leaf 13 0xa2d2800000000000a280528000000000a0505060000000009a4a4a546262610c964e4e5c5050500a934b4b546060604c92cacad45050502a926b4a544260454c925eca7c4050402a924a6b544042654c924a5efc4040502a924a4a5440404008924a00004040000092004a0040004000904848500000000082424244000000007dbd8003fff800007d803d83f807f8007c3c3c3b070707806fb78003fff800006f803783f807f8006dff8003bff800006db5b5a8323235666db58003bfb800006d807f83b807f8006d803583b807b8006c34342b0707078069b18003afa8000069803183a807a80063b3b3a68484867061b1b1a2848486705faf8003fff80000) (
.leaf 14 0xb6ca5ed450405008b694dea850105022b68c5e985050500ab682de845050502ab6807f805007f800b6805efc5000502ab6805e83d805d800b6805e8050005000b680000050000000b65e5e7c40404008b4dedcfc1050102ab4dcdefc1010502ab4dcdcf810101022b47c5c7807000780b45edc7c0050002ab45c7c7800070780b45c5efc0000502ab45c5c7b05050280b45c5c785050500ab45c5c7800000000b45c000000000000b4005c0000000000b2dadaf440404028a6d6d6ec10101022a3d3d3e480808070a2f3d2e404800670a2ded2fc0050002aa2d2f3e400048670a2d2defc0000502aa2d2d2e684848230a2d2d2e45050502aa2d2d2e400000020)))) (
.fork 17 0xc363634400000440 (
.fork 16 0xb6eb5ed45260554c (
.leaf 15 0xb6defffc5057f82ab6defffc5054d67ab6defffc5052756eb6defefc505757aab6deeb545052654cb6dedeffddd8502ab6dedeffd855d82ab6dedeff555552aab6dedefed4d4d23ab6dedefc7878502ab6dedefc7850782ab6dedefc7070702eb6dedefc5050502ab6dedefc50500020b6dedefc50005020b6dedefc40404028b6dedefc10101022b6dedefc0050002ab6dedefc0000502ab6dedefc00000020b6dede8050505000b6dedc7850500000b6ded2e450500020b6deca5450504008b6de94a850501022b6de8c185050500ab6de82845050502ab6de807c5050002ab6de8003ddd80000b6de800050500000b6dc5ef850005000b6d2dee450005020) (
.leaf 16 0xc363000000000000c300630000000000c060604000000400beff80017ff80000bededefd7b78502abededefd7853782abededefd535351aabededefc7272712ebede80017b780000be807f817807f800be805e8178037800bc7c5c7907030780bc5c7c7903070780bc5c5c7b07070380bc5c5c7903030180bc5c5c7903000000bc5c5c7900030000bc5c5c7802020100b7dfdffcd0d0d07ab7dfdffc7070706eb7dfdefcf8f8502ab7dfdefc7070502ab7df8000f8f80000b7dedffcf850f82ab7dedffc7050702ab7805f80f800f800b6ffdefc57f8502ab6ffdefc54d0567ab6ffdefc5270556eb6ff800057f80000b6fedefc575057aab6eb5ed45260554c)) (
.fork 18 0xd9696b542222654c (
.leaf 17 0xd969695022222544d87f800007f80000d87c687807020780d86b68540262054cd8687c7802070780d8686b540202654cd868685307070780d86868506262650cd868685002020500d868000002000000d8007f800007f800d800680000020000d36b6b5440404448cb6b63542262254ccb636b542222654ccb6363446262654ccb63634422222544cb63634422200440cb63634420022440cb63634402020540c3f3e3e484808670c3e3f3e480848670c3e3e3c684848670c3e3e3c480808470c3e3e3c400000460c373e36404800670c36b63540260054cc36373e400048670c3636b540002654cc363634684848650c36363446060644cc363634400000440) (
.fork 19 0xdb6b21546262254c (
.leaf 18 0xdb6b210062622544db6b08106262610cdb6b03046260604cdb6b00546260054cdb6b0003efe80000db6b000062600000db686b5062026500db636b546002654cdb636b4462226544db636b446062644cdb636b4460026440db636b4400020440db63634460000440db5eeb7c6052602adb4a6b5460426008db236b046262654cdb216b546222654cdb216b0062226544db086b106262610cdb036b046062604cdb007f83e807f800db007f806007f800db007f8060027000db007b806006e000db006b806002f800db006b546002654cdb006b03e807e800db006b0060026000db00000060000000da6a6a5442424508d96b69542262254cd9696b542222654c) (
.leaf 19 0xdb6b6b7c626267ccdb6b6b57efea654cdb6b6b57ea67ed4cdb6b6b57676767ccdb6b6b56e6e6e75cdb6b6b547a7a654cdb6b6b547a627d4cdb6b6b547272754edb6b6b546262654cdb6b6b5462626008db6b6b5462620540db6b6b5462604448db6b6b5462026540db6b6b5460426448db6b6b5442424548db6b6b5422222544db6b6b540262054cdb6b6b540202654cdb6b6b5402020540db6b6b4462626440db6b6b046262604cdb6b6b0062626000db6b685062620500db6b63546260054cdb6b634462622544db6b63446260644cdb6b634462600440db6b634402000440db6b5efc6260502adb6b4a5462604008db6b23046262654cdb6b21546262254c)))))) (
.fork 30 0xff7f7c7b07070780 (
.fork 25 0xf7defffed054d02a (
.fork 22 0xe2f2f2e604040620 (
.fork 21 0xdbeb8000faf80000 (
.leaf 20 0xdbeb8000e2e00000dbeb800072700000dbeb6bd4fa62fd4cdbeb6bd47262754cdb807f80f807f800db806b83f807f800db806b80f802f800db806b80e002e000db806b8070027000db7feb7c6272656edb7feb5467fa654cdb7feb546272654cdb7f8003eff80000db7f800067f80000db7f800062700000db7f6b7c676267ccdb7f6b7c6262654cdb7beb7466e2677cdb7b800066e00000db6f6b5c636265ccdb6f6b5c6272654edb6f6b54637a654cdb6b800062f80000db6b7ffc6262756edb6b7fd46267fd4cdb6b7fd46262754cdb6b7f7c626767ccdb6b7f7c6262654cdb6b7bf46266e77cdb6b6f5c626365ccdb6b6f5c6262754edb6b6f5462637d4c) (
.leaf 21 0xe171716284848650e0f0f0e284848630e07c707a07040780e073f06604840670e0707c7a04070780e07073e604048670e070706204040600e070000204000000e000700200040000dfef8001fbf80000df806f81f803f800df7f80017ff80000df6f6f5d636365ccdf6f6f5c7272754edf6f6f5c6262654cdf6f6b557b7a654cdf6f6b547272654cdf6f00017b780000df6b6f557a637d4cdf6b6f547262754cdf007f817807f800df006f0178037800dc7c6c7907030780dc6c7c7903070780dc6c6c5903030580dbff8000fff80000dbebebd4e2e2e57cdbebebd47272756edbebeb54fafa654cdbebeb547272654cdbeb8003fff80000dbeb8000faf80000)) (
.fork 23 0xe3f3f3e480808470 (
.leaf 22 0xe3f3f3e404800670e3f3f3e400048670e3f3f3e400000460e3f3f3c684848440e3f3f38684848070e3f3f38284848000e3f3f06284840600e3f3e3c684808470e3f3e34684800440e3f3d2e684800020e3f3a38684848670e3f3a10284848650e3f390a284848230e3f3838684808070e3f3806684800670e3f38002fcf80000e3f3800284800000e3f073e284048600e3e3f3c680848470e3e373c680048440e3d2f3e680048020e3a3f38684848670e3a1738284848650e390f3a284848230e383f38680848070e3807f828007f800e38073e680048670e3807382f804f800e380738280048000e380000280000000e373736604040640e2f2f2e604040620) (
.fork 24 0xe7f3f7e79c859e70 (
.leaf 23 0xe7f3f7e784858670e780778398059800e474746b05050680e3fff3fe878487f0e3fff3fe84d4867ae3fff3fe84848670e3fff3e687fc8670e3fff38287fc8000e3ff800287f80000e3fbf3f686e4877ce3f7f3ee858486f0e3f3fffe848787f0e3f3fffe8484d67ae3f3fffe84848670e3f3ffe68487fe70e3f3ff828487f800e3f3fbf68486e77ce3f3f7ee848586f0e3f3f3fe848487f0e3f3f3e78d8c8670e3f3f3e78c858e70e3f3f3e7858586f0e3f3f3e6fcfc8670e3f3f3e6fc84fe70e3f3f3e6e4e4e67ce3f3f3e6d4d4d67ae3f3f3e684848670e3f3f3e684848020e3f3f3e684800460e3f3f3e680048460e3f3f3e604040660e3f3f3e480808470) (
.leaf 24 0xf7defffc5050502af7807f82d004d000f6fefefe5454562af47c7c7a04040600f3fbfbf6c4c4c678f3fbfbf684848670eff78003bfb80000ef807783b807b800ebff8003aff80000ebf3f3e7afac8670ebf3f3e7ac87ae70ebf3f3e7878787f0ebf3f3e6a6a6a774ebf38003fff80000ebf38003afa80000ebf38003ac800000ebf3800387800000ebf38002a6a00000eb807f83a807f800eb807383f807f800eb807383a807a800eb807383a8048000eb80738380078000eb807382a006a000e870706307070780e7f7f7ef858586f0e7f7f7ee94949672e7f7f7ee84848670e7f7f3e79d9c8670e7f7f3e785848670e7f780039d980000e7f3f7e79c859e70)))) (
.fork 27 0xfc7c1c3b07070380 (
.fork 26 0xfbfbeb56e6e2654c (
.leaf 25 0xfbfbeb546262654cfbfb8003efe80000fbfb8002fef80000fbfb8002e6e00000fbfb800286800000fbfb800062600000fbf3fbe6e486e670fbf38002e4800000fbeb7bd6e266e54cfbeb7bd46262654cfb807f82e007f800fb807b83e807e800fb807b82f806f800fb807b82e006e000fb807b8280068000fb807b8060026000fb807382e0048000fb7b7b766666674cfb7b7b746262654cf878787206060700f7ffffff858586f0f7fffffed4d4d67af7fffffe84848670f7fffffc5050546af7fff3e6d4d48670f7fff3e684848670f7ffdefed4d0502af7ffdefc5050502af7ff8002d4d00000f7f3ffe6d484d670f7f3ffe684848670f7defffed054d02a) (
.leaf 26 0xfc7c142b07050280fc7c0c7b07030780fc7c0c1b07030180fc7c007b07000780fc7c00037f780000fc7c000307000000fc707c6304070600fc687c5302070500fc5c7c7b05070280fc5c7c7b03070180fc5c7c7b00070780fc5c7c7b00070000fc5c7c7800020000fc5c5c7b00000000fc207c0307070780fc1c7c3b07070380fc147c2b05070280fc0c7c7b03070780fc0c7c1b03070180fc007f837807f800fc007f830007f800fc007f8300078000fc007c7b00070780fc007c0378077800fc007c0300070000fc00000300000000fbff8002e7f80000fbfbfbf6e6e6e77cfbfbfbf686868770fbfbfbf46262656cfbfbf3e6e6e48670fbfbeb56e6e2654c)) (
.fork 28 0xfc7c7f7f070707c0 (
.leaf 27 0xfc7c7eff070757aafc7c7d7b0707af80fc7c7d7b070787d0fc7c7d7b070727c4fc7c7c7b8f8f0780fc7c7c7b8f078f80fc7c7c7b87878790fc7c7c7b7f7f0780fc7c7c7b7f077f80fc7c7c7b6767678cfc7c7c7b5757578afc7c7c7b07070780fc7c7c7b07070000fc7c7c7b07040600fc7c7c7b07020500fc7c7c7b04070600fc7c7c7b02070500fc7c7c7a06060700fc7c7c7903030580fc7c7c7807020780fc7c7c7802070780fc7c7c7802020500fc7c7c0307070000fc7c706307040600fc7c685307020500fc7c5c7b07050280fc7c5c7b07030180fc7c5c7b07000780fc7c5c7b07000000fc7c5c7802000000fc7c200307070780fc7c1c3b07070380) (
.fork 29 0xfd7d7c7b87870780 (
.leaf 28 0xfd7d0003afa80000fd7c7d7baf07af80fd7c7d7b87078780fd007f83a807f800fd007d03a807a800fcff80039ff80000fcfcfcfb878787b0fcfcfcfb171717a2fcfcfc7b9f9f0780fcfcfc7b87870780fcfc80039f980000fcfc7cfb9f079f80fcfc7cfb87078780fc807f839807f800fc807c8398079800fc7ffc7f078707f0fc7ffc7b07ff0780fc7ffc7b07870780fc7f80037ff80000fc7f800307f80000fc7f800307800000fc7f7c7f076707ccfc7f7c7f070707c0fc7efc7f075707aafc7d7c7b07af0780fc7d7c7b078707d0fc7d7c7b072707c4fc7c7fff070787f0fc7c7ffb0707ff80fc7c7ffb07078780fc7c7f7f070767ccfc7c7f7f070707c0) (
.leaf 29 0xff7f6b576762654cff7f6b546262654cff7f000367600000ff7c7f7b67076780ff7c7f7b07070780ff6b7f576267654cff6b7f546262654cff007f836007f800ff007f0360076000feff800357f80000fefefeff575757aafefefeff070707a0fefefefc5252552afefefc7b57570780fefefc7b07070780fefedeff5750502afefe800357500000fefc7efb57075780fefc7efb07070780fedefeff5057502afe807f835007f800fe807e8350075000fe7e7e7f47474788fe7e7e7f07070780fdfd8003bfb80000fd807d83b807b800fd7f8003aff80000fd7d7d7b878787d0fd7d7d7b272727c4fd7d7d7b070707c0fd7d7c7bafaf0780fd7d7c7b87870780))))) (
.fork 35 0xfffc7ffbff07ff80 (
.fork 32 0xff837f83f867f800 (
.fork 31 0xff807f8370077000 (
.leaf 30 0xff807f82f006f000ff807f8178037800ff807f80f802f800ff807f807007f800ff807f8070027000ff807c03f8070000ff807b83f806e000ff807783f8059800ff8073e7f8048670ff807383f807a800ff807383f804f800ff807383f8048000ff80738380048000ff806b83f802f800ff806b03f8026000ff805e83f8005000ff803583f807b800ff802383f807f800ff802103f807a800ff801483f8059800ff800c03f8037800ff800383f800f800ff800003f8000000ff7f800367f80000ff7f7f7f878787d0ff7f7f7f676767ccff7f7f7f070707c0ff7f7f7c7272754eff7f7f7c6262654cff7f7f7c02020540ff7f7c7b67670780ff7f7c7b07070780) (
.leaf 31 0xff82ff87f857f82aff82ff83f857f800ff827f87f847f808ff817f83f8aff800ff80ff83f89ff800ff807ffff807f82aff807ffbf807ff80ff807ffbf807f800ff807fe7f807fe70ff807fd7f807fd4cff807fd7f807f808ff807fabf807fa80ff807f9bf807f980ff807f9bf807f80aff807f93f807f90cff807f83fd8ff800ff807f83fd07fa80ff807f83fc87fa10ff807f83f87ff800ff807f83f867f80cff807f83f857f80aff807f83f807f800ff807f83f8078000ff807f83f804d000ff807f83f8027000ff807f83e007e000ff807f83d007d000ff807f83a807a800ff807f8398079800ff807f838007f800ff807f8380078000ff807f8370077000)) (
.fork 33 0xffa17f83fc87f800 (
.leaf 32 0xffa17f83fa27fd44ffa10003ffa80000ffa07f83ff07ff80ff97ff83fdfff800ff94ffabfd9ffa80ff94ffabf817f822ff94ff83fd9ff800ff94ff83f817f800ff948003fd980000ff947fabfd07fa80ff947fabf807f800ff947f83fd07f800ff90ffa3fc87fa30ff90ff83fc87f800ff907fa3fc07fa00ff8c7f9bfb07f980ff8c7f9bf857f80aff8c7f9bf807f800ff8c7f83fb7ff800ff8c7f83f857f800ff8c0003fb780000ff887f93fa67f90cff887f93f847f808ff847f8bf907f880ff847f8bf817f802ff847f83f91ff800ff83ff87f887f870ff83ff83f8fff800ff83ff83f887f800ff838003f8f80000ff837f87f867f84cff837f83f867f800) (
.fork 34 0xffe87fd3fa07fd00 (
.leaf 33 0xffe37fc7f807fc40ffe37f83f807f800ffdfff83f8fff800ffdefffff857f82affdefffc7052702affdefffbf857f800ffdeffd7f857f808ffdeff9bf857f80affdeff83fddff800ffdeff83f857f800ffdedefff850502affdedefc7050502affde8003f8500000ffde7ffff847f808ffdc7ffbfd07fa80ffdc7ffbf857f80affdc7ffbf807f800ffdc7ffb80078000ffdc7f83f807f800ffd2ffe7f807f820ffd2ff83f807f800ffd07fe3f807f800ffce7fdff857f80affca7fd7f847f808ffca7f83f847f800ffc87fd3f807f800ffc27fc7f807f800ffb58003ffb80000ffa38003fff80000ffa17f83ffaff800ffa17f83fc87fe50ffa17f83fc87f800) (
.leaf 34 0xfffc7ffb87078780fffc7f83ff07f800fffc7c7bff070780fffc7c7b87070780fffc0003ff000000fffbfff7fee7ff7cfffb8003fee00000fff7ff83fd9ff800fff78003fd980000fff3ffe7fc87fe70fff3ffe784878670fff3ff83fcfff800fff3ff83fc87f800fff3f3e7fc848670fff3f3e784848670fff3f383fc848000fff38067fc800670fff38003ffa80000fff38003fcf80000fff38003fc800000fff3800384800000fff07fe3fc07fe00fff07f83fc07f800ffef7fdc7272754effeb8003faf80000ffeb7fd7fa67fd4cffeb7fd47262754cffeb7f83fa67f800ffeb6b57fa62654cffeb6b547262654cffeb0003fa600000ffe87fd3fa07fd00)))) (
.fork 37 0xffff9483fff81000 (
.fork 36 0xffff8057fff80008 (
.leaf 35 0xffff802bfff80280ffff801bfff80180ffff801bfff8000affff8013fff8010cffff8003fffd8800ffff8003fffd0280ffff8003fffc8210ffff8003fff87800ffff8003fff8600cffff8003fff8500affff8003fff80000ffff8003ff800000ffff8003fcd00000ffff8003fa700000ffff8003e7e00000ffff8003d7d00000ffff8003afa80000ffff80039f980000ffff800387f80000ffff800387800000ffff800377700000ffff8002f6f00000ffff80017b780000ffff8000faf80000ffff800077f80000ffff800072700000ffff7fffff67ffccffff7fff870787c0ffff7ffc7262754cfffeffffff57ffaafffd7ffb878787d0fffc7ffbff07ff80) (
.leaf 36 0xffff942bfffd0280ffff942bfff80000ffff9403fffd0000ffff90a3fffc8230ffff9083fffc8000ffff9023fffc0200ffff8c1bfffb0180ffff8c1bfff8500affff8c1bfff80000ffff8c03fffb7800ffff8c03fff85000ffff8813fffa610cffff8813fff84008ffff840bfff90080ffff840bfff81002ffff8403fff91800ffff8387fff88070ffff8383fff8f800ffff8383fff88000ffff8307fff8604cffff8303fff86000ffff8287fff8502affff8283fff85000ffff8207fff84008ffff8103fff8a800ffff8083fff89800ffff807ffff8002affff807bfff80780ffff807bfff80000ffff8067fff80670ffff8057fff8054cffff8057fff80008)) (
.fork 38 0xffffe303fff80000 (
.leaf 37 0xffffdf83fff8f800ffffdefffff8502affffdefc7270502affffdefbfff85000ffffded7fff85008ffffde9bfff8500affffde83fffdd800ffffde83fff85000ffffde7ffff84008ffffdc7bfffd0280ffffdc7bfff8500affffdc7bfff80000ffffdc7b87800000ffffdc03fff80000ffffd2e7fff80020ffffd283fff80000ffffd063fff80000ffffce5ffff8500affffca57fff84008ffffca03fff84000ffffc853fff80000ffffc247fff80000ffffa103ffffa800ffffa103fffc8650ffffa103fffc8000ffffa103fffa2544ffffa003ffff0780ffff9783fffdf800ffff94abfffd9a80ffff94abfff81022ffff9483fffd9800ffff9483fff81000) (
.fork 39 0xfffffffef6f6f77e (
.leaf 38 0xfffffffc7272756efffffffbffffff80fffffffb87878780ffffffe7fffffe70ffffffd7fffffd4cffffffd47272754cffffff83fffff800ffffff83fffcd000ffffff83fcd7f800ffffff7fffff67ccffffff7f878707c0ffffff7c7272654cfffffeffffff57aafffffd7b878787d0fffffc7bffff0780fffffc7b87870780fffffc03ffff0000fffffbf7fffee77cfffff783fffd9800fffff3e7fffc8670fffff3e787848670fffff383fffcf800fffff383fffc8000fffff063fffc0600fffff003fffc0000ffffef5c7272754effffeb57fffa654cffffeb547272654cffffeb03fffa6000ffffe853fffa0500ffffe347fff80440ffffe303fff80000) (
.leaf 39 0xfffffffffffff82affffffffffff87f0fffffffffffcd67afffffffffffa756effffffffff87fff0fffffffffcd7fe7afffffffffa77fd6effffffffe7e7e7fcffffffffd7d7d7faffffffff878787f0ffffffff777777eefffffffef6f6f77e))))))⟩

set_option maxRecDepth 16000 in
def bank4 : PackedSeq := ⟨16, 59, 0x7ffffffffffffff, .leaf 0 0x9b48a46ea4f03e93690d4dd4b989e26d1ba97312a0fa4da3532e62781f49988a86ea4f03e9329158dd49e07d2651ba97312b0fa4ca3552e62781f49687d65cc4f03e923cd54b989e07d23b21797313c0fa4763eb3c32e61f48a86ea5cc4cc3e9150d90b989e07d2289ba97313c0fa4053642e62781f4⟩

set_option maxRecDepth 16000 in
def bank5 : PackedSeq := ⟨977, 71, 0x7fffffffffffffffff, .fork 15 0x4763eb3752781f40f2 (
.fork 7 0x4763552e62781f403a (
.fork 3 0x3eb3752e628a2781f4 (
.fork 1 0x3eb3752e61f4192189 (
.leaf 0 0x7d66ea5cc3e8308300facdd4b987d04b0111f59ba9730fa09001ebeb3752de2781f40407d66ea5424f04523e8facdd49e07d064854df59ba93c0fa0760203eb36b2e62781f40407d66c85cc5a04f03e8facd90b989e07d02b9f59b217313c0fa03dbeb3642e62781f402d7d65cc4f03e8206200facb989e07d02cc101f11ba97313c0fa0223dc3752e62781f40407aa6ea5cc5a04f03e8f54dd4b989e07d01edea9ba97313c0fa016bca3752e62db2781f47946ea5cc4f03e8118f28dd4b989e07d002dba99e99997313c0fa37533d2e62781f40746ea6665cc4f03e8068dd4c48c30b989e07d1ba97315094d13c0fa3752e62781f41a91a76ea5cc4f03e832431cdd4b989e07d0214111ba97313c0fa0408203752e62781f4074034) (
.fork 2 0x3eb3752e62781f40c0 (
.leaf 1 0x7d66ea5cc4f03e8118facdd4b989e07d0129f59ba97313c0fa024beb3752e62781f40487d66ea5cc4f03e808cfacdd4b989e07d0115f59ba97313c0fa0223eb3752e62781f40437d66ea5cc4f03e8084facdd4b989e07d0101f59ba97313c0fa01f3eb3752e62781f403d7d66ea5cc4f03e8078facdd4b989e07d00ddf59ba97313c0fa01a3eb3752e62781f40337d66ea5cc4f03e8064facdd4b989e07d00c5f59ba97313c0fa0183eb3752e62781f402f7d66ea5cc4f03e805cfacdd4b989e07d00a9f59ba97313c0fa014beb3752e62781f40287d66ea5cc4f03e804efacdd4b989e07b4111f59ba97313c0b68223eb3752e626e1f40447d66ea5cc4cc3e80f6facdd4b989987d00b5f59ba97312b0fa01ebeb3752e61f4192189) (
.leaf 2 0x7d66ea5cc4f04c83e8facdd4b989e08fc7d1f59ba97313c10e8fa3eb3752e62781fc1f47d66ea5cc4f03e8360facdd4b989e07d06b5f59ba97313c0fa0d5beb3752e62781f41a97d66ea5cc4f03e834afacdd4b989e07d0685f59ba97313c0fa0cfbeb3752e62781f41937d66ea5cc4f03e8324facdd4b989e07d0645f59ba97313c0fa0c83eb3752e62781f41867d66ea5cc4f03e8308facdd4b989e07d060df59ba97313c0fa0c13eb3752e62781f417d7d66ea5cc4f03e82f8facdd4b989e07d05e1f59ba97313c0fa0aebeb3752e62781f414a7d66ea5cc4f03e826cfacdd4b989e07d0421f59ba97313c0fa081beb3752e62781f41027d66ea5cc4f03e81f6facdd4b989e07d037df59ba97313c0fa0673eb3752e62781f40c0))) (
.fork 5 0x4303752e62781f4192 (
.fork 4 0x3eb37533c2e62781f4 (
.leaf 3 0x7d66ea6765cc4f03e8facdd4ce4b989e07d1f59ba99513c0fa0c93eb37531a2e62781f47d66ea6305cc4f03e8facdd4c4cb989e07d1f59ba9891731598fa3eb3753122e62781f47d66ea6245cc4603e8facdd4c44b989e07d1f59ba98817313c0fa3eb37530f2e62781f47d66ea60e5424f03e8facdd4bc4b989e07d1f59ba9731681330fa3eb3752e62b72781f47d66ea5cc56a4f03e8facdd4b98a9c9e07d1f59ba97315113c0fa3eb3752e62a12781f47d66ea5cc5424423e8facdd4b98a847d0435f59ba97315013c0fa3eb3752e629f2781f47d66ea5cc52c4b63e8facdd4b98a509e07d1f59ba97314993c0fa3eb3752e62932211f47d66ea5cc5263e821afacdd4b98a489e07d1f59ba97314713c0fa3eb3752e628a2781f4) (
.leaf 4 0x8526ea5cc4f03e8353094facdd4b989e07d2121f59ba97313c0fa41a3752e627825b1f48346ea5cc4f03e82d1068dd4b989e07d009a0b9ba97315093c0fa4103753122e62781f480a6ea6b65cc4f03e9014dd4b989e096c7d2029ba97313c0fa0b44053752e62781f403680a6ea5cc4f03e804cfacf60dd4b989e07d1f59e49ba97313c0fa3eb3c43752e61f41927d676e6ea5cc4f03e8facea0dd4b989e07d1f59d31ba97313c0fa3eb39b3752e62781f47d671c6ea5cc4f03e8face34dd4b989e07d1f59c697313c0fa0e6beb38d2e62781f40997d67186ea5cc4f03e8facdd4d18b989e07d1f59ba99f97313c0fa3eb37533e2e62781f47d66ea67a5cc4f03e8facdd4cf4b988847d1f59ba99e9730fa086beb37533c2e62781f4)) (
.fork 6 0x4673eb3752de2781f4 (
.leaf 5 0x8ce7d66ea4f03e81d919cfacdacb989e07d2339f597313c0fa059c673dc3752e62781f48ce6ea5cc4f03e8103180facb989e07d040e2d1f59ba97313c0fa4583eb3752e62781f48a889a6ea5cc4f03e9150f28dd4b989e07d22a1ba9ad97313c0fa4543752e627825b1f48a86ea5cc4f03e82d1150dd4b989e07d03a22a1ba97313c0fa01d4543752e62781f40368a86ea5cc4f03e804d13cfacdd4b989e07d2271f59ba97313c0fa44d3eb3752e62781f489a7d66ea5cc4ac3e9134facdd4b987d0482269ba97316213c0fa44d3752e62781f406c89a6ea5cc4f03e8075130facdd4b989e07d2241f59ba97313c0fa4463eb3752e61f418486e6ea5cc4f04b63e90dcdd4b989e07d05a21b9ba97313c0fa0134303752e62781f4192) (
.leaf 6 0x8ec6985cc4f03e839b1d8d30b989e07d02663b17313c0fa07e072c762e62781f40b30818ea7d66ea5cc4f03e91d0facdd4b989e07d2399f59ba97313c0fa4723eb3752e62781f48e27d66ea5cc4f03e91c0facdd4b989e07d2379f59ba97313c0fa46e3eb3752e62781f48da7d66ea5cc4f03e91b4facdd4b989e07b6369f59ba97313c0b6c6d3eb3752e626e1f48da7d66ea5cc3e82591b4facb989e07d0736369f597313c0fa04cc6d3eb2e62781f40368da7c46ea5cc4f03e91b4dd4b989e07d0216361f59ba97313c0fa46b3eb3752e62781f48d47d66ea5cc4f03e91a4facdd4b989e07d2341f59ba97313c0fa4673eb3752e62781f48ce7d66ea5cc4423e919cfacdd4b987d0436339f59ba9730fa0134673eb3752de2781f4)))) (
.fork 11 0x4763d53752e61f4125 (
.fork 9 0x4763752e62781f418d (
.fork 8 0x4763752e62781f4077 (
.leaf 7 0x8ec6ea5cc4f03e80e91d8dd4b989e07d01ce3b1ba97313c0fa0394763752e62781f40718ec6ea5cc4f03e80df1d8dd4b989e07d01ba3b1ba97313c0fa036c763752e62781f40698ec6ea5cc4f03e80d11d8dd4b989e07d019a3b1ba97313c0fa032c763752e62781ed0858ec6ea5cc4f02da10b1d8dd4b989b87d02163b1ba9731330fa03f4763752e62561f406c8ec6ea5cc4ac3e80751d8dd4b9892c8847d23b1ba9731258fa086c763752e61f418e1898ec6ea5cc3e82f42cb1d8dd4b987d04b02163b1ba9730fa09283f4763752de2781f40818ec6ea5344f04523e91d8dd49e07d063854e3b1ba93c0fa076040c7636b2e62781f40818ec6aa5cc5884f03e91d8d54b989e07d029e3b1aa97313c0fa0364763552e62781f403a) (
.leaf 8 0x8ec6ea5cc4f03e83191d8dd4b989e07d06163b1ba97313c0fa0bf4763752e62781f41658ec6ea5cc4f03e82c91d8dd4b989e07d058e3b1ba97313c0fa0b14763752e62781f41618ec6ea5cc4f03e82af1d8dd4b989e07d05223b1ba97313c0fa09cc763752e62781f41058ec6ea5cc4f03e81ff1d8dd4b989e07d03963b1ba97313c0fa0724763752e62781f40d88ec6ea5cc4f03e819b1d8dd4b989e07d030e3b1ba97313c0fa0464763752e62781f408b8ec6ea5cc4f03e81151d8dd4b989e07d02263b1ba97313c0fa043c763752e62781f40868ec6ea5cc4f03e810b1d8dd4b989e07d02123b1ba97313c0fa041c763752e62781f40818ec6ea5cc4f03e80ff1d8dd4b989e07d01fa3b1ba97313c0fa03ec763752e62781f4077)) (
.fork 10 0x4763753092e62781f4 (
.leaf 9 0x8ec6ea60e5344f03e91d8dd4be4b989e07d23b1ba97316212b0fa4763752e62b62781f48ec6ea5cc5584f03e91d8dd4b98a709e07d23b1ba97314d93c0fa4763752e629a2781f48ec6ea5cc5344423e91d8dd4b98a687d04363b1ba97314c93c0fa4763752e62982781f48ec6ea5cc51048a3e91d8dd4b989e094c7d23b1ba97313c1260fa4763752e627824b1f48ec6ea5cc4f04943e91d8dd4b989e09247d23b1ba97313c1240fa4763752e62782361f48ec6ea5cc4f042e3e91d8dd4b989e08047d23b1ba97313c0fa0d7c763752e62781f41ac8ec6ea5cc4f03e83511d8dd4b989e07d069e3b1ba97313c0fa0d24763752e62781f41a08ec6ea5cc4f03e833b1d8dd4b989e07d063e3b1ba97313c0fa0c74763752e62781f418d) (
.leaf 10 0x8ec7a86ea5cc4f03e91d8f4cdd4b989e07d23b1e81ba97313c0fa4763cf3752e62781f48ec7886ea5cc3e831d1d8ee4dd4b989e07d23b1d61ba97313c0fa4763a73752e62781f48ec73a6ea5cc4f03e91d8e4cdd4b989e07d23b1ba9a697313c0fa47637534c2e62781f48ec6ea6965cc4f03e91d8dd4cd8b989e07d23b1ba99a97313c0fa4763753342e62781f48ec6ea6665cc4f03e91d8dd4cccb988847d23b1ba9999730fa086c763753322e62781f48ec6ea6625cc4f03e91d8dd4cc0b989e07d23b1ba99513c0fa0c74763753192e62781f48ec6ea61c5cc4f03e91d8dd4c34b989e07d23b1ba9861731598fa47637530c2e62781f48ec6ea6185cc4603e91d8dd4c2cb989e07d23b1ba98517313c0fa4763753092e62781f4))) (
.fork 13 0x4763eb2e62781f40fc (
.fork 12 0x4763e73752e62781f4 (
.leaf 11 0x8ec7cc6ea5cc4f03e91d8f94dd4b989e07d23b1f21ba97313c0fa4763e33752e62781f48ec7c46ea5cc4f03e91d8f88dd4b989e07b63b1f11ba97313c0b6c763e23752e626e1f48ec7c46ea5cc3e82591d8f88b989e07d07363b1f117313c0fa04cc763e22e62781f40768ec7c26ea5cc4f03e91d8f80dd4b989e07d23b1ef9ba97313c0fa4763de3752e62781f48ec7ba6ea5cc4f03e91d8f70dd4b989e07d23b1ee1ba9731108fa4763dc3752e61f410d8ec7b86ea5cc3e80c91d8f70dd4b789e07d23b1ee1ba93c0fa0764763dc36b2e62781f48ec7b85cc4f03e81671d8f68dd4b989e07d23b1ec9ba97313c0fa4763d73752e62781f48ec7ac6ea5cc4f03e91d8f54dd4b989e07d23b1ea9ba9731330fa4763d53752e61f4125) (
.leaf 12 0x8ec7d65cc4f03e81f51d8facb989e07d03e63b1f597313c0fa07c4763eb2e62781f40c38ec7d65cc4f03e81811d8facb989e07d02fa3b1f597313c0fa05ec763eb2e62781f40bb8ec7d65cc4f03e81751d8facb989e07d02e23b1f597313c0fa05bc763eb2e62781f40b38ec7d65cc4f03e81611d8facb989e07d02be3b1f597313c0fa055c763eb2e62781f40aa8ec7d65cc4f03e81531d8facb989e07d02723b1f597313c0fa04dc763eb2e62781f409a8ec7d65cc4f039a2db1d8facb989b87d07363b1f59731370fa08bc763eb2e626e1f40998ec7d65bc4f03e81671d8fac9e08a47d05123b1f593c1090fa0a9c763eb2781f40ec0b38ec7d46ea5cc4f03e91d8fa4dd4b989e07d23b1f41ba97313c0fa4763e73752e62781f4)) (
.fork 14 0x4763eb35f2e62781f4 (
.leaf 13 0x8ec7d66b05cc4f03e91d8facd5cb989e07d23b1f59ab17313c0fa4763eb3552e62781f48ec7d66a85cc4f03e91d8facd4cb989e07d23b1f59a897313c0fa4763eb34f2e62781f48ec7d65cc5544f03e91d8facb98aa49e07d23b1f597313c10a8fa4763eb2e62782141f48ec7d65cc4f04263e91d8facb989e08487d23b1f597313c1088fa4763eb2e62782101f48ec7d65cc4f041e3e91d8facb989e07d06ba3b1f597313c0fa0cdc763eb2e62781f419a8ec7d65cc4f03e830f1d8facb989e07d051a3b1f597313c0fa0a2c763eb2e62781f41448ec7d65cc4f03e82871d8facb989e07d04f23b1f597313c0fa083c763eb2e62781f41018ec7d65cc4f03e82011d8facb989e07d03fa3b1f597313c0fa07ec763eb2e62781f40fc) (
.leaf 14 0x8ec7d66ea4f03e81e11d8facdd49e07d03b23b1f59ba93c0fa075c763eb3752781f40dc8ec7d66ea4f03e81851d8facdd49e07b453e3b1f59ba93c0f686dc763eb3752211f412c8ec7d66ea4423e81d91d8facdd47d062454e3b1f59ba17313c0fa4763eb3732e62781f48ec7d66e45cc4f03e91d8facdc4b989e07d23b1f59b817313c0fa4763eb36f2e62781f48ec7d66dc5cc4f03e91d8facdb4b989e07d23b1f59b617313c0fa4763eb36b2e62781f48ec7d66d65cc4423e91d8facdacb987d04363b1f59b59730fa0514763eb36b2de2781f48ec7d66d64f03e81d91d8facd9cb989e07d23b1f59b317313c0fa4763eb3652e62781f48ec7d66c85cc4f03e91d8facd8cb989e07d23b1f59b097313c0fa4763eb35f2e62781f4))))) (
.fork 23 0x4764163752e62781f4 (
.fork 19 0x4763eb3752e62781f0 (
.fork 17 0x4763eb3752e61f4181 (
.fork 16 0x4763eb3752e32781f4 (
.leaf 15 0x8ec7d66ea5c44f03e91d8facdd4b849e07d23b1f59ba97013c0fa4763eb3752df2781f48ec7d66ea5bc4f03e91d8facdd4b749e07d23b1f59ba96e13c0fa4763eb3752d92781f48ec7d66ea5ac4f03e91d8facdd4b389e07d23b1f59ba96593c0fa4763eb3752b32211f48ec7d66ea5663e81d91d8facdd49e08b07d23b1f59ba93c1158fa4763eb37527822a1f48ec7d66ea4f04523e91d8facdd49e08a07d23b1f59ba93c1108f6c763eb3752781f41a38ec7d66ea4f03e83291d8facdd49e07d05563b1f59ba93c0fa0aa4763eb3752781f41538ec7d66ea4f03e82a51d8facdd49e07d050a3b1f59ba93c0fa083c763eb3752781f40ff8ec7d66ea4f03e81f71d8facdd49e07d03de3b1f59ba93c0fa07ac763eb3752781f40f2) (
.leaf 16 0x8ec7d66ea5cc3e83011d8facdd4b987d05fe3b1f59ba9730fa0bdc763eb3752e61f417a8ec7d66ea5cc3e82f31d8facdd4b987d05de3b1f59ba9730fa0bb4763eb3752e61f41428ec7d66ea5cc3e82791d8facdd4b987d04e63b1f59ba9730fa09b4763eb3752e61f41348ec7d66ea5cc3e82671d8facdd4b987d04ca3b1f59ba9730fa0984763eb3752e61f412f8ec7d66ea5cc3e825b1d8facdd4b987d04b23b1f59ba9730fa0944763eb3752e61f41258ec7d66ea5cc3e82491d8facdd4b987d04823b1f59ba9730fa08fc763eb3752e61f411e8ec7d66ea5cc3e82211d8facdd4b987d043e3b1f59ba9730fa0874763eb3752e61ed12c8ec7d66ea5cc2da2591d8facdd4b949e07d23b1f59ba97213c0fa4763eb3752e32781f4)) (
.fork 18 0x4763eb3752e62691f4 (
.leaf 17 0x8ec7d66ea5cc4d03e91d8facdd4b9899c7d23b1f59ba9731330fa4763eb3752e62651f48ec7d66ea5cc4c43e91d8facdd4b989847d23b1f59ba97312c8fa4763eb3752e62581f48ec7d66ea5cc4ae3e91d8facdd4b989587d23b1f59ba97312a8fa4763eb3752e62541f48ec7d66ea5cc4a23e91d8facdd4b989407d23b1f59ba9731210fa4763eb3752e62411f48ec7d66ea5cc4663e91d8facdd4b988c87d23b1f59ba9731188fa4763eb3752e62301f48ec7d66ea5cc45e3e91d8facdd4b988b87d23b1f59ba9731168fa4763eb3752e61f41aa8ec7d66ea5cc3e83311d8facdd4b987d065e3b1f59ba9730fa0cb4763eb3752e61f418b8ec7d66ea5cc3e83151d8facdd4b987d06263b1f59ba9730fa0c44763eb3752e61f4181) (
.leaf 18 0x8ec7d66ea5cc4f03df1d8facdd4b989e07ba3b1f59ba97313c0f6c763eb3752e62781d68ec7d66ea5cc4f03ab1d8facdd4b989e06aa3b1f59ba97313c0ca4763eb3752e62781878ec7d66ea5cc4f02fd1d8facdd4b989e05e23b1f59ba97313c0ba4763eb3752e62781718ec7d66ea5cc4f02dd1d8facdd4b989e05b63b1f59ba97313c0a0c763eb3752e62781408ec7d66ea5cc4f02711d8facdd4b989dc7d23b1f59ba97313b0fa4763eb3752e62751f48ec7d66ea5cc4e83e91d8facdd4b989cc7d23b1f59ba9731390fa4763eb3752e62711f48ec7d66ea5cc4e03e91d8facdd4b989bc7d23b1f59ba9731370fa4763eb3752e626e1ed8ec7d66ea5cc4dc2db1d8facdd4b989b47d23b1f59ba9731360fa4763eb3752e62691f4))) (
.fork 21 0x4763eb3832e62781f4 (
.fork 20 0x4763eb3752ed2781f4 (
.leaf 19 0x8ec7d66ea5d84f03e91d8facdd4bac9e07d23b1f59ba9731598fa4763eb3752e62b21f48ec7d66ea5cc5603e91d8facdd4b98ab47d23b1f59ba9731518fa4763eb3752e629d1f48ec7d66ea5cc52a3e91d8facdd4b98a407d23b1f59ba9731468fa4763eb3752e628c1f48ec7d66ea5cc5163e91d8facdd4b98a1c7d23b1f59ba9731428fa4763eb3752e62831f48ec7d66ea5cc5043e91d8facdd4b98a047d23b1f59ba9731400fa4763eb3752e627b1f48ec7d66ea5cc4f43e91d8facdd4b989e47d23b1f59ba97313c105c763eb3752e62782088ec7d66ea5cc4f03ef1d8facdd4b989e07da3b1f59ba97313c0fac763eb3752e62781f48ec7d66ea5cc4f03e71d8facdd4b989e07ca3b1f59ba97313c0f8c763eb3752e62781f0) (
.leaf 20 0x8ec7d67025cc4f03e91d8facdfcb989e07d23b1f59bf17313c0fa4763eb37d2e62781f48ec7d66f85cc4f03e91d8facdecb989e07d23b1f59bd17313c0fa4763eb3753402e61f48ec7d66ea66e5cc3e91d8facdd4cb8b987d23b1f59ba99613c0fa4763eb37532a2781f48ec7d66ea6544f03db1d8facdd4ca89e053e3b1f59ba9950fa0c4c763eb3753272781f48ec7d66ea64a5cc4f11d8facdd4c889e07d23b1f59ba99017313c4763eb37531b2781f48ec7d66ea60e4f03e91d8facdd4c1c8847d23b1f59ba9838fa0964763eb3753052781f48ec7d66ea6064f03e91d8facdd4c009e07d23b1f59ba97d93c0fa4763eb3752f62781f48ec7d66ea5e64f03e91d8facdd4bbc9e07d23b1f59ba97713c0fa4763eb3752ed2781f4)) (
.fork 22 0x4763eb3c82e62781f4 (
.leaf 21 0x8ec7d678c5cc4f03e91d8facf18b989b87d23b1f59e31730fa0b54763eb3c62e61f41178ec7d678a6ea5cc3e91d8facf10dd4ca87d23b1f59e21ba9730fa4763eb3c43751f41538ec7d67886d65cc3e91d8facf10b987d03b63b1f59e21730fa0514763eb3c12e62781f48ec7d677e6ea5cc3e91d8facef0b989e07d23b1f59dd1ba9730fa4763eb3b22e62781f48ec7d675c5cc4f03e91d8facea4b989e07d23b1f59d297313c0fa4763eb3a52e62781cd8ec7d674a5cc4f02db1d8face8cb989e07d23b1f59d097313c0fa4763eb39e2e62781f48ec7d672e5cc4f03e91d8face50b989e07d23b1f59c797313c0fa4763eb38a2e62781f48ec7d67105cc4f03e91d8face1cb989e07d23b1f59c317313c0fa4763eb3832e62781f4) (
.leaf 22 0x8ec82a6ea5cc4f03e91d904cdd4b989e07d23b2091ba97313c0fa4764103752e62b31f48ec8206ea5cc4f03e91d9040dd4b988c07d23b2079ba97313c0fa47640d3752e62781f48ec8146ea5cc4f03e91d9024dd4b989e07d23b2041ba97313c0fa4764073752e62781f48ec80a6ea5cc4f03e91d9010dd4b989e07d23b2009ba97313c0fa4763ff3752e62781f48ec7fc6ea5cc4f03e91d8ff4dd4b989e07d23b1fe1ba97313c0fa4763f93752e62781f48ec7ec6ea5cc4f03e91d8fd4dd4b989e07d23b1fa1ba97313c0fa4763f33752e62781f48ec7e46ea5cc4f03e91d8fc4dd4b989e07d23b1f81ba97313c0fa4763ef3752e62781f48ec7dc6ea5cc4f03e91d8fb4dd4b989e07d23b1f61ba97313c0fa4763eb3c82e62781f4)))) (
.fork 27 0x4af3eb3752e62781f4 (
.fork 25 0x4764643eb3752e61f4 (
.fork 24 0x4764373752e62781f4 (
.leaf 23 0x8ec86e6ea5cc3e82f51d90d4facdd4b989e23b2199ba97313c0fa4764323752e62781f48ec8626ea5cc4f03e91d90c0f10dd4b987d23b2181ba99513c0fa4764303752e62781f48ec8606ea5cc3e83131d90c0dd49e07d054e3b2181aa97313c0fa4764302e62781f40ed8ec8605cc4f03e814f1d90b8dd4b989e07d23b2161ba97313c0fa47642b3752e62781f48ec8546ea5cc4f03e91d90a4dd4b989e07d23b2149ba9730fa0b54764283752e62781f48ec84e6ea5cc4f03e91d9098dd4b989e07d23b2109ba97313c0fa47641d3752e62781f48ec8386ea5cc4f03e91d9068dd4b989e07d23b20c9ba97313c0fa4764173753072781f48ec82e6ea5cc4f03e91d905cdd49e08a47d23b20b97313c0fa076c764163752e62781f4) (
.leaf 24 0x8ec8c47d65cc4f03e91d91810f4b989e07d23b2301f597313c0fa4764603e22e62781f48ec8c05cc4f048a3e91d9180b989e07d05823b23017313c0fa03b4764602e62781f40648ec8ba7d65cc4f03e91d9164dd4b989e07d23b22b1ba96213c0fa4764553752e62781f48ec8a86ea5cc4f03e91d9150b989e07d03f23b2291f59ba93c0fa4764503752e62781f48ec8946ea5cc4f03e91d9124facdd4b987d23b22321e9ba9730fa4764463eb3752e61f48ec88c7b86ea5cc3e91d9118dd4b989147d23b2231ba9730fa0b04764463752e61f40648ec8867d66ea5cc3e91d90fcdd4b989e07d23b21f1ba97313c0fa47643b3752e62781f48ec8746ea5cc4f03e91d90e4dd4b989e07d23b21c1ba97313c0fa4764373752e62781f4)) (
.fork 26 0x4983eb3752e62781f4 (
.leaf 25 0x92c7d66ea5cc4f03e9250facdd4b989e07d2499f59ba97313c0fa4923eb3752e62781f49227d66ea5cc4f03e923d0f4dd4b989e07d2479f59ba97313c0fa48f3753482e62781f491e6ea5cc4f048a3e923cdd4b989e07d0582479ba97313c0fa03b48f3752e62781f406491c7d66ea5cc4f03e9230facdd4b989e07d2451f59ba97313c0fa4893eb3752e62781f49107d66ea5cc4f03e921cfacdd4b989e07d2421f59ba97313c0fa4813eb3752e62781f49007d66ea5cc4f03e91fcfacdd4b989e07d23f1f59ba97313c0fa47d3eb3752e62781f48f87d66ea5cc4f03e91ecfacdd4b989e07d23d1f59ba97313c0fa4793eb3752e62781f48f07d66ea5cc4f03e91dcfacdd4b989e07d23b2329f597313c0fa4764643eb3752e61f4) (
.leaf 26 0x95c8526ea5cc4f03e92b8facdd4b989e07d2571f59ba9730fa0b54ae3752e62781f41a795a7d66ea5cc4f03e92b0facdd4b989e07d2559f59ba97313c0fa4a83eb3752e62781f494a7d66ea5cc4f03e9290facdd4b989e07d25121e9ba97313c0fa4a23eb3752e62781f49446ea5cc4f048a3e9288dd4b989e07d0582511ba97313c0fa0324a13eb3752e62781f494082e6ea5cc4f03e9280facdd4c1c9e07d2501f59ba97313c0fa4a03eb3752782291f49407d65cc4f03e81db280dd4b98a689e07d24f9f59ba97313c0fa49e3eb3752e62781f49387d66ea5cc4f03e926cfacdd4b989e07d24ca081ba97313c0fa4993eb3752e62b31f49327d66ea5cc4f03e9264facdd4b988c07d24c9ba98617313c0fa4983eb3752e62781f4))) (
.fork 29 0x4d13eb2e62781f4168 (
.fork 28 0x4c03eb3752e62781f4 (
.leaf 27 0x97e8a86ea5cc4f03e92fd0dcdd4b989e07d25fa0d1ba97313c0fa4bf4053752e62781f497a7d66ea5cc4f03e92f0facdd4b989e07d25d9f59ba97313c0fa4ba3eb3752e62781f497288c7d66ea5cc3e92e50f4dd4b989e07d25c9f59ba97313c0fa4b93eb3752e61f41809726ea5cc4f048a3e92e4dd4b989e07d05825c9ba97313c0fa0324b83eb3752e62781f496e7d66ea5cc4f03e92d8facdd4b989e07d25aa181ba97313c0fa4b53eb3c43752e61f496a7d66ea6544f03e92d4facdd4b989e07d25a9f59ba9730fa0c4cb53eb3752781f415396a7d66c85cc4f03e92d4facb989e07d03b65a9f597313c0fa0574b53752e62781f418e9667d66ea5cc4f03e92c4facdd4b989e07d2581f59ba97313c0fa4af3eb3752e62781f4) (
.leaf 28 0x9a27d65cc4f03e806d344facb989e07d009a671f59ba97313c0fa4cd4543752e62781f49987d66ea5a04f03e932cfacdd4b989e07d2652301f597313c0fa4ca4573752e62781f499487a6ea5cc4f03e9328facdd4b989e07d2651f597313c0fa0804ca3d53752e62781f49947946ea5cc4f03e9328dd4d20b989e07d2651ba97313c1228fa4ca3752e62781f41609946ea5cc4f03e81c7328dd4b989e07d01ee651ba97313c0fa03b4ca3752e62781f40649907d66ea5cc4f03e931d1d8facdd4b987d262a5f9f59ba9730fa4c54764373752e61f498a8ec7d66ea5cc3e93151d8dd4b987d059662a339f59ba9730fa4c53eb3752e625b1f498a7d66ea5cc3e82d1314facdd4b987d009a609f59ba97313c0fa4c03eb3752e62781f4)) (
.fork 30 0x4da4763552e62781f4 (
.leaf 29 0x9b48a66ea5cc4f03e9369134dd4b989e07d26d21b1ba97313c0fa4da4343752e62781f49b48306ea5cc4f03e936900cdd4b989e07d26d1f59ba9731330fa4da3eb3642e62781f49b47aa6ea5cc4f03e9368f44dd4b989e07d26d1e69ba97313c0fa4da3cb3752e62781f49b47946ea5cc4f03e9368dd4d1cb989e07d26d1ba97313c1220fa4da3752e62781f415e9b46ea5cc4f03e81c3368dd4b989e07d02326d1ba97313c0fa03c4da3752e62781f40679b27d66ea5cc4f03e93611d8dd4b989e07d26b23b1f597313c0fa4d54763eb3752e61f49a68ec7d65cc4f03e93452fcfacb989e07d268a3b22a17313c0fa4d14763eb2e62781f49a28ec5cc4f03e81cb3451b4facb989e07d2689f597313c12d8fa4d13eb2e62781f4168) (
.leaf 30 0x4e34b53eb2e62781f49c69407d65cc4f03e938d1d90c0b989e07d271a3b20b97313c0fa4e34763eb3c42e61f49c68ec7d64f04523e938d1d8fac9e08487d271a3b1f593c0fa0a9ce34763eb2781f41449c095c7d66ea5cc3e93811d90a4dd4b987d27023b1f59e31730fa4e04763eb3752e61d79bc8ec7d65cc4f03e936d1d8facdd4b987d26d23b1ba97312b0fa4da4763552e62781f4)))))⟩

set_option maxRecDepth 16000 in
def bank6 : PackedSeq := ⟨1158, 83, 0x7ffffffffffffffffffff, .fork 18 0x4763eb3752e62781f41cc (
.fork 9 0x4763eb3752e62781f400b (
.fork 4 0x3eb37535b2e62d02781f4 (
.fork 2 0x4764053752e62781f4 (
.fork 1 0x4763eb2e62781f40ab (
.leaf 0 0x8ec7c46ea5cc4f03e80011d8f70dd4b989e07d00023b1ea9ba97313c0fa00047637534c2e62781f40008ec6ea6665cc4f03e80011d8dd4c30b989e07d00023b1ba97314d13c0fa0004763752e627824b1f40008ec6ea5cc4f03e834e0011d8dd4b989e07d06380023b1ba97313c0fa0b28004763752e62781f40e50008ec6ea5cc4f03e810a0011d8dd4b989e07d02040023b1ba97313c0fa03f0004763752e62781f40740008da7d66ea5cc4f03e800119cfacdd4b989e07d0002269f59ba97313c0fa0003eb38d3752e62781f40007d66ea67a5cc4f03e8000facdd4c48b989e07d0001f59ba97315093c0fa0003eb3752e62932781f40007d66ea5cc4f03e8352000facdd4b989e07d0648001f59ba97313c0fa0c20003eb3752e62781f41030007d66ea5cc4f03e8088000facdd4b989e07d0100001f59ba97313c0fa01e8003eb3752e62781f4034) (
.leaf 1 0x8ec7d678c5cc4f03e80011d8facf10dd4b987d00023b1f59d297313c0fa0004763eb37532a2781f40008ec7d66ea60e4f03e80011d8facdd4b98acc7d00023b1f59ba97313c0f68004763eb3752e627816d0008ec7d66ea5cc4dc3e80011d8facdd4b989987d00023b1f59ba97312b0fa0004763eb3752e62301f40008ec7d66ea5cc3e83120011d8facdd4b987d06000023b1f59ba9730fa0bd0004763eb3752e61f412c0008ec7d66ea5cc3e824a0011d8facdd4b987d04800023b1f59ba96f13c0fa0004763eb3752782291f40008ec7d66ea4f03e82a60011d8facdd49e07d03b00023b1f59b597313c0fa0004763eb3642e62781f40008ec7d66aa5cc4f03e80011d8facb989e08487d00023b1f597313c0fa0a20004763eb2e62781f41000008ec7d65cc4f03e81f80011d8facb989e07d02cc0023b1f597313c0fa0580004763eb2e62781f40ab)) (
.fork 3 0x3eb3752e62781f4123026 (
.leaf 2 0x7d66ea5cc4f03e81d00f6facdd4b989e07d03a00b5f59ba97313c0fa05701b3eb3752e62781f40ae0267d66ea5cc4f03e80f6074facdd4b989e07d01ec0d9f59ba97313c0fa03d8133eb3752e62781f403a02d7d66ea5cc4f03e806c05afacdd4b989e07d00b4099f59ba97313c0fa0130110004da3ca3752e62781f40009a28ec7d65cc4f03e8001328facdd4b989e07d000262a3b1f59ba9730fa0004b93eb3752e62781f400096a7d66ea5cc4f03e80012b8facdd4b989e07d0002511f59ba97313c0fa0004a03eb3752e62781f40009327d66ea5cc4f03e800123cfacdd4b989e07d00023b2301f597313c0fa0004764543752e62781f40008ec88c7d66ea5cc3e80011d90dcdd4b989e07d00023b2181ba97313c0fa0004764293752e62781f40008ec8346ea5cc4f03e80011d905cdd4b989e07d00023b2081ba97313c0fa0004764053752e62781f4) (
.leaf 3 0x7d66ea6b65cc4f03e815cfacdd4d6cb989e07d01edf59ba9ad97313c0fa016beb37534533d2e62781f47d66ea68a5cc4f03e8068facdd4c48b989e07d034df59ba97316813c12d8fa3eb3752e62d02781f41687d66ea5cc5a04f03e81d0facdd4b98b409e07d00e9f59ba97316813c0fa01b3eb3752e62d02781f40267d66ea5cc5884f03e8206facdd4b98a849e07d045df59ba97314993c0fa08e3eb3752e627825b1f41e37d66ea5cc4f04b63e8246facdd4b989e096c7d02b9f59ba97313c12d8fa03dbeb3752e627825b1f402d7d66ea5cc4f04b63e8044facdd4b989e07d078c5a1f59ba97313c0fa0f18133eb3752e62781f41d91847d66ea5cc4f03e839a324facdd4b989e07d06d46a5f59ba97313c0fa0b4091beb3752e62781f41680ae7d66ea5cc4f03e82d00f6facdd4b989e07d05a00b5f59ba97313c0fa0b40113eb3752e62781f4123026))) (
.fork 6 0x4763eb2e62781f41170a2 (
.fork 5 0x4763752e62782451f40a7 (
.leaf 4 0x8ec6ea5cc4f048a3e80d91d8dd4b989e09147d017e3b1ba97313c1228fa01d4763752e62781f41e31658ec6ea5cc4f03e83b22c11d8dd4b989e07d07641923b1ba97313c0fa0e68c74763752e62781f41b51a78ec6ea5cc4f03e82c02391d8dd4b989e07d058029e3b1ba97313c0fa0b00364763752e62781f416005f8ec6ea5cc4f03e82c00751d8dd4b989e07d04701923b1ba97313c0fa0718364763752e62781f40e303a8ec6ea5cc4f03e814e0ed1d8dd4b989e07d029c1923b1ba97313c0fa03d8364763752e62781f407b03a8ec6ea5cc4f03e80ec0d91d8dd4b989e07d01d80ea3b1ba97313c0fa0360324763752e62781f406405f8ec6ea5cc4f03e80c807515d134facdd4b989e07d22b9f59ba97313c0fa01ebeb3ca3752e62d02781f47d67946ea5cc4f03e80f6facf28dd4b989e07d00b5f59c69ba97313c0fa053beb37535b2e62d02781f4) (
.leaf 5 0x8ec7d65cc4f03e81da1691d8facb989e07d03b42663b1f597313c0fa07683b4763eb2e62781f40ed0368ec7d65cc4f03e815c1331d8facb989e07d02b80da3b1f597313c0fa05384cc763eb2e62781f40a70768ec7d65cc4f03e81441331d8f28dd4b98b109e07d23b1e51ba97313c0fa0364763ca3752e62781f403a8ec6ea6985cc4f03e815d1d8dd4d20b98b109e07d23b1ba9a417313c0fa053c763753482e62781f406c8ec6ea6905cc4f03e80751d8dd4d14cccb989e07d23b1ba9a297313c0fa03a47637530c2e62781f40d38ec6ea5cc5a04f03e81cb1d8dd4b98b109e09147d23b1ba97316213c0fa0b04763752e62c42781f40e38ec6ea5cc5884f03e80f71d8dd4b98b109e07d01da3b1ba97316213c0fa0324763752e629a2781f41178ec6ea5cc4f04963e82471d8dd4b989e09147d07663b1ba97313c1228fa08e4763752e62782451f40a7)) (
.fork 7 0x4763eb3752781f41cd153 (
.leaf 6 0x8ec7d66ea4f03e838229f1d8facdd49e07d070436e3b1f59ba93c0fa0a7869c763eb3752781f414f0b48ec7d66ea4f03e821a1b71d8facdd49e07d03b42d23b1f59ba93c0fa074016c763eb3752781f40e306c8ec7d66ea4f03e81b61a71d8facdd49e07d036c2d23b1f59ad97313c0fa0e6c763eb35b2e62781f40998ec7d66b65cc4f03e806d1d8facd20b989e07d07363b1f59a417313c0fa04cc763eb3482e62781f40768ec7d65cc5a04f03e81f91d8facb98b109e07d04023b1f597315d13c0fa076c763eb2e62782381f41cd8ec7d65cc4f04703e822f1d8facb989e08e07d02663b1f597313c1108fa0a24763eb2e62782121f414f8ec7d65cc4f03e839a2b51d8facb989e07d07343b63b1f597313c0fa0e68574763eb2e62781f41cd0a78ec7d65cc4f03e839a1451d8facb989e07d05682663b1f597313c0fa08b876c763eb2e62781f41170a2) (
.fork 8 0x4763eb3752e62381f410d (
.leaf 7 0x8ec7d66ea5cc4703e81451d8facdd4b988c07d034e3b1f59ba9731108fa0b54763eb3752e62211f41238ec7d66ea5cc4423e82391d8facdd4b988847d045e3b1f59ba9731108fa06dc763eb3752e61f41e317a8ec7d66ea5cc3e83b23011d8facdd4b987d07346263b1f59ba9730fa0da8b54763eb3752e61f416a1298ec7d66ea5cc3e82d421b1d8facdd4b987d05a828a3b1f59ba9730fa0b50324763eb3752e61f416a0268ec7d66ea5cc3e824621b1d8facdd4b987d048c09a3b1f59ba9730fa08e086c763eb3752e61f411c0648ec7d66ea5cc3e822e21b1d8facdd4b987d045c28a3b1f59ba9730fa08686dc763eb3752d02781f402d8ec7d66ea5884f03e80d91d8facdd4ae89e07d02d23b1f59ba93c1148fa08bc763eb3752782211f41c18ec7d66ea4f04423e821b1d8facdd49e08847d034e3b1f59ba93c1108fa05a4763eb3752781f41cd153) (
.leaf 8 0x8ec7d66ea5cc4f03e80151d8facdd4b989e07d00263b1f59ba97313c0fa0044763eb3752e62781f40078ec7d66ea5cc4f03e800d1d8facdd4b989e07d00163b1f59ba97313c0fa0024763eb3752e62781f40038ec7d66ea5cc4f03e80051d8facdd4b989e07d00063b1f59ba97313c0f18114763eb3752e62781d905f8ec7d66ea5cc4f039a3831d8facdd4b989e073453e3b1f59ba97313c0e684cc763eb3752e62781c115a8ec7d66ea5cc4f03821a71d8facdd4b989e06d44a63b1f59ba97313c0b5094c763eb3752e62781680228ec7d66ea5cc4f02c00bf1d8facdd4b989e056853e3b1f59ba97313c0ad04cc763eb3752e627814f0d38ec7d66ea5cc4b64423e91d8facdd4b9896c7d04363b1f59ba97312d8fa0134763eb3752e62452211f48ec7d66ea5cc48a3e821b1d8facdd4b989147d01923b1f59ba97311c1108fa4763eb3752e62381f410d))))) (
.fork 13 0x4763eb3752e62781f40c1 (
.fork 11 0x4763eb3752e62781f405f (
.fork 10 0x4763eb3752e62781f4035 (
.leaf 9 0x8ec7d66ea5cc4f03e80691d8facdd4b989e07d00b63b1f59ba97313c0fa0164763eb3752e62781f402b8ec7d66ea5cc4f03e804d1d8facdd4b989e07d00963b1f59ba97313c0fa0124763eb3752e62781f40238ec7d66ea5cc4f03e80451d8facdd4b989e07d00863b1f59ba97313c0fa0104763eb3752e62781f401f8ec7d66ea5cc4f03e803d1d8facdd4b989e07d00763b1f59ba97313c0fa00e4763eb3752e62781f401b8ec7d66ea5cc4f03e80351d8facdd4b989e07d00663b1f59ba97313c0fa00c4763eb3752e62781f40178ec7d66ea5cc4f03e802d1d8facdd4b989e07d00563b1f59ba97313c0fa00a4763eb3752e62781f40138ec7d66ea5cc4f03e80251d8facdd4b989e07d00463b1f59ba97313c0fa0084763eb3752e62781f400f8ec7d66ea5cc4f03e801d1d8facdd4b989e07d00363b1f59ba97313c0fa0064763eb3752e62781f400b) (
.leaf 10 0x8ec7d66ea5cc4f03e80bd1d8facdd4b989e07d01763b1f59ba97313c0fa02e4763eb3752e62781f405b8ec7d66ea5cc4f03e80b51d8facdd4b989e07d01663b1f59ba97313c0fa02c4763eb3752e62781f40578ec7d66ea5cc4f03e80ad1d8facdd4b989e07d01563b1f59ba97313c0fa02a4763eb3752e62781f40538ec7d66ea5cc4f03e80a51d8facdd4b989e07d01463b1f59ba97313c0fa0284763eb3752e62781f404f8ec7d66ea5cc4f03e809d1d8facdd4b989e07d01363b1f59ba97313c0fa0264763eb3752e62781f404b8ec7d66ea5cc4f03e808f1d8facdd4b989e07d01123b1f59ba97313c0fa020c763eb3752e62781f40408ec7d66ea5cc4f03e807f1d8facdd4b989e07d00f63b1f59ba97313c0fa01dc763eb3752e62781f403a8ec7d66ea5cc4f03e80731d8facdd4b989e07d00e23b1f59ba97313c0fa01b4763eb3752e62781f4035)) (
.fork 12 0x4763eb3752e62781f4094 (
.leaf 11 0x8ec7d66ea5cc4f03e81271d8facdd4b989e07d024a3b1f59ba97313c0fa048c763eb3752e62781f40908ec7d66ea5cc4f03e811f1d8facdd4b989e07d023a3b1f59ba97313c0fa046c763eb3752e62781f40888ec7d66ea5cc4f03e810b1d8facdd4b989e07d020a3b1f59ba97313c0fa040c763eb3752e62781f40808ec7d66ea5cc4f03e80fd1d8facdd4b989e07d01f23b1f59ba97313c0fa03dc763eb3752e62781f407a8ec7d66ea5cc4f03e80f31d8facdd4b989e07d01e23b1f59ba97313c0fa03b4763eb3752e62781f40758ec7d66ea5cc4f03e80e91d8facdd4b989e07d01c23b1f59ba97313c0fa0364763eb3752e62781f406b8ec7d66ea5cc4f03e80d51d8facdd4b989e07d019e3b1f59ba97313c0fa0324763eb3752e62781f40638ec7d66ea5cc4f03e80c51d8facdd4b989e07d01863b1f59ba97313c0fa0304763eb3752e62781f405f) (
.leaf 12 0x8ec7d66ea5cc4f03e817f1d8facdd4b989e07d02f23b1f59ba97313c0fa05cc763eb3752e62781f40b68ec7d66ea5cc4f03e816b1d8facdd4b989e07d02d23b1f59ba97313c0fa059c763eb3752e62781f40b28ec7d66ea5cc4f03e81631d8facdd4b989e07d02c23b1f59ba97313c0fa0574763eb3752e62781f40ad8ec7d66ea5cc4f03e81591d8facdd4b989e07d02ae3b1f59ba97313c0fa0544763eb3752e62781f40a78ec7d66ea5cc4f03e814d1d8facdd4b989e07d02963b1f59ba97313c0fa0524763eb3752e62781f40a38ec7d66ea5cc4f03e81451d8facdd4b989e07d02863b1f59ba97313c0fa0504763eb3752e62781f409f8ec7d66ea5cc4f03e813d1d8facdd4b989e07d02763b1f59ba97313c0fa04cc763eb3752e62781f40988ec7d66ea5cc4f03e812f1d8facdd4b989e07d025a3b1f59ba97313c0fa04ac763eb3752e62781f4094))) (
.fork 15 0x4763eb3752e62781f411d (
.fork 14 0x4763eb3752e62781f40e9 (
.leaf 13 0x8ec7d66ea5cc4f03e81d11d8facdd4b989e07d039e3b1f59ba97313c0fa0734763eb3752e62781f40e58ec7d66ea5cc4f03e81c71d8facdd4b989e07d038a3b1f59ba97313c0fa070c763eb3752e62781f40e08ec7d66ea5cc4f03e81bd1d8facdd4b989e07d03763b1f59ba97313c0fa06dc763eb3752e62781f40da8ec7d66ea5cc4f03e81b31d8facdd4b989e07d035e3b1f59ba97313c0fa06b4763eb3752e62781f40d58ec7d66ea5cc4f03e81a91d8facdd4b989e07d034e3b1f59ba97313c0fa0694763eb3752e62781f40d18ec7d66ea5cc4f03e81a11d8facdd4b989e07d033e3b1f59ba97313c0fa0664763eb3752e62781f40cb8ec7d66ea5cc4f03e81951d8facdd4b989e07d03263b1f59ba97313c0fa0644763eb3752e62781f40c78ec7d66ea5cc4f03e818d1d8facdd4b989e07d03163b1f59ba97313c0fa0624763eb3752e62781f40c1) (
.leaf 14 0x8ec7d66ea5cc4f03e82391d8facdd4b989e07d046e3b1f59ba97313c0fa08d4763eb3752e62781f41198ec7d66ea5cc4f03e82311d8facdd4b989e07d045e3b1f59ba97313c0fa08b4763eb3752e62781f41158ec7d66ea5cc4f03e82291d8facdd4b989e07d044e3b1f59ba97313c0fa0894763eb3752e62781f41118ec7d66ea5cc4f03e821b1d8facdd4b989e07d04323b1f59ba97313c0fa085c763eb3752e62781f410a8ec7d66ea5cc4f03e82131d8facdd4b989e07d041a3b1f59ba97313c0fa0824763eb3752e62781f41038ec7d66ea5cc4f03e82011d8facdd4b989e07d03f23b1f59ba97313c0fa07b4763eb3752e62781f40f48ec7d66ea5cc4f03e81e71d8facdd4b989e07d03c63b1f59ba97313c0fa077c763eb3752e62781f40ee8ec7d66ea5cc4f03e81db1d8facdd4b989e07d03b23b1f59ba97313c0fa0754763eb3752e62781f40e9)) (
.fork 16 0x4763eb3752e62781f4156 (
.leaf 15 0x8ec7d66ea5cc4f03e82a71d8facdd4b989e07d05463b1f59ba97313c0fa0a84763eb3752e62781f414f8ec7d66ea5cc4f03e829d1d8facdd4b989e07d05363b1f59ba97313c0fa0a64763eb3752e62781f414b8ec7d66ea5cc4f03e82931d8facdd4b989e07d051e3b1f59ba97313c0fa0a24763eb3752e62781f413f8ec7d66ea5cc4f03e827d1d8facdd4b989e07d04f63b1f59ba97313c0fa09dc763eb3752e62781f413a8ec7d66ea5cc4f03e826f1d8facdd4b989e07d04d63b1f59ba97313c0fa098c763eb3752e62781f412e8ec7d66ea5cc4f03e82591d8facdd4b989e07d04ae3b1f59ba97313c0fa0954763eb3752e62781f41298ec7d66ea5cc4f03e824f1d8facdd4b989e07d049a3b1f59ba97313c0fa092c763eb3752e62781f41238ec7d66ea5cc4f03e82451d8facdd4b989e07d04863b1f59ba97313c0fa0904763eb3752e62781f411d) (
.fork 17 0x4763eb3752e62781f419e (
.leaf 16 0x8ec7d66ea5cc4f03e83391d8facdd4b989e07d06663b1f59ba97313c0fa0cac763eb3752e62781f41928ec7d66ea5cc4f03e831d1d8facdd4b989e07d06263b1f59ba97313c0fa0c24763eb3752e62781f41808ec7d66ea5cc4f03e82f51d8facdd4b989e07d05d63b1f59ba97313c0fa0b9c763eb3752e62781f41728ec7d66ea5cc4f03e82e11d8facdd4b989e07d05be3b1f59ba97313c0fa0b6c763eb3752e62781f416c8ec7d66ea5cc4f03e82d71d8facdd4b989e07d05aa3b1f59ba97313c0fa0b4c763eb3752e62781f41688ec7d66ea5cc4f03e82cf1d8facdd4b989e07d059a3b1f59ba97313c0fa0b2c763eb3752e62781f41608ec7d66ea5cc4f03e82bf1d8facdd4b989e07d057a3b1f59ba97313c0fa0ae4763eb3752e62781f415b8ec7d66ea5cc4f03e82b51d8facdd4b989e07d05663b1f59ba97313c0fa0ac4763eb3752e62781f4156) (
.leaf 17 0x8ec7d66ea5cc4f03e83971d8facdd4b989e07d072a3b1f59ba97313c0fa0e4c763eb3752e62781f41c88ec7d66ea5cc4f03e838f1d8facdd4b989e07d071a3b1f59ba97313c0fa0e2c763eb3752e62781f41c48ec7d66ea5cc4f03e83871d8facdd4b989e07d070a3b1f59ba97313c0fa0e0c763eb3752e62781f41c08ec7d66ea5cc4f03e837f1d8facdd4b989e07d06fa3b1f59ba97313c0fa0dec763eb3752e62781f41bc8ec7d66ea5cc4f03e83771d8facdd4b989e07d06ea3b1f59ba97313c0fa0dcc763eb3752e62781f41b88ec7d66ea5cc4f03e836f1d8facdd4b989e07d06da3b1f59ba97313c0fa0dac763eb3752e62781f41b48ec7d66ea5cc4f03e83671d8facdd4b989e07d06ca3b1f59ba97313c0fa0d8c763eb3752e62781f41a98ec7d66ea5cc4f03e834f1d8facdd4b989e07d069a3b1f59ba97313c0fa0d14763eb3752e62781f419e)))))) (
.fork 27 0x4763eb3bb3752e62781f4 (
.fork 22 0x4763eb3752e62b31f40d3 (
.fork 20 0x4763eb3752e62782241f4 (
.fork 19 0x4763eb3752e62781f81f4 (
.leaf 18 0x8ec7d66ea5cc4f03e83db1d8facdd4b989e07d07b23b1f59ba97313c0fa0f5c763eb3752e62781f41ea8ec7d66ea5cc4f03e83d31d8facdd4b989e07d07a23b1f59ba97313c0fa0f3c763eb3752e62781f41e68ec7d66ea5cc4f03e83cb1d8facdd4b989e07d07923b1f59ba97313c0fa0f1c763eb3752e62781f41e28ec7d66ea5cc4f03e83c31d8facdd4b989e07d07823b1f59ba97313c0fa0efc763eb3752e62781f41de8ec7d66ea5cc4f03e83bb1d8facdd4b989e07d07723b1f59ba97313c0fa0edc763eb3752e62781f41da8ec7d66ea5cc4f03e83b31d8facdd4b989e07d07623b1f59ba97313c0fa0ebc763eb3752e62781f41d48ec7d66ea5cc4f03e83a71d8facdd4b989e07d074a3b1f59ba97313c0fa0e8c763eb3752e62781f41d08ec7d66ea5cc4f03e839f1d8facdd4b989e07d073a3b1f59ba97313c0fa0e6c763eb3752e62781f41cc) (
.leaf 19 0x8ec7d66ea5cc4f04463e91d8facdd4b989e08887d23b1f59ba97313c1108fa4763eb3752e62782201f48ec7d66ea5cc4f043e3e91d8facdd4b989e08787d23b1f59ba97313c10e0fa4763eb3752e627821b1f48ec7d66ea5cc4f04343e91d8facdd4b989e08647d23b1f59ba97313c10c0fa4763eb3752e62782161f48ec7d66ea5cc4f04243e91d8facdd4b989e08387d23b1f59ba97313c1068fa4763eb3752e627820c1f48ec7d66ea5cc4f04143e91d8facdd4b989e08247d23b1f59ba97313c1038fa4763eb3752e62782061f48ec7d66ea5cc4f040a3e91d8facdd4b989e08107d23b1f59ba97313c1018fa4763eb3752e62782021f48ec7d66ea5cc4f04003e91d8facdd4b989e07fc7d23b1f59ba97313c0ff0fa4763eb3752e62781fd1f48ec7d66ea5cc4f03f63e91d8facdd4b989e07e87d23b1f59ba97313c0fc8fa4763eb3752e62781f81f4)) (
.fork 21 0x4763eb3752e627825e1f4 (
.leaf 20 0x8ec7d66ea5cc4f04ba3e91d8facdd4b989e09707d23b1f59ba97313c12d8fa4763eb3752e627825a1f48ec7d66ea5cc4f04ac3e91d8facdd4b989e09487d23b1f59ba97313c1278fa4763eb3752e627824e1f48ec7d66ea5cc4f049a3e91d8facdd4b989e092c7d23b1f59ba97313c1238fa4763eb3752e62782461f48ec7d66ea5cc4f048a3e91d8facdd4b989e09107d23b1f59ba97313c1218fa4763eb3752e62782401f48ec7d66ea5cc4f047c3e91d8facdd4b989e08f47d23b1f59ba97313c11e0fa4763eb3752e627823b1f48ec7d66ea5cc4f04743e91d8facdd4b989e08e47d23b1f59ba97313c11c0fa4763eb3752e62782371f48ec7d66ea5cc4f046a3e91d8facdd4b989e08d07d23b1f59ba97313c1180fa4763eb3752e62782291f48ec7d66ea5cc4f044e3e91d8facdd4b989e08987d23b1f59ba97313c1128fa4763eb3752e62782241f4) (
.leaf 21 0x8ec7d66ea5cc5624f03e91d8facdd4b98abc9e07d23b1f59ba97315713c0fa4763eb3752e62ab2781f48ec7d66ea5cc5504f03e91d8facdd4b98a989e07d23b1f59ba97315293c0fa4763eb3752e62a42781f48ec7d66ea5cc5424f03e91d8facdd4b98a789e07d23b1f59ba97314d13c0fa4763eb3752e62972781f48ec7d66ea5cc52c4f03e91d8facdd4b98a4c9e07d23b1f59ba97314893c0fa4763eb3752e628f2781f48ec7d66ea5cc5124f03e91d8facdd4b98a209e07d23b1f59ba97314313c0fa4763eb3752e62842781f48ec7d66ea5cc4fe4f03e91d8facdd4b989f89e07d23b1f59ba97313e93c0fa4763eb3752e627c2781f48ec7d66ea5cc4f04dc3e91d8facdd4b989e09ac7d23b1f59ba97313c1350fa4763eb3752e62782661f48ec7d66ea5cc4f04c63e91d8facdd4b989e09807d23b1f59ba97313c12f8fa4763eb3752e627825e1f4))) (
.fork 24 0x4763eb37531c2e62781f4 (
.fork 23 0x4763eb3752e62d82781f4 (
.leaf 22 0x8ec7d66ea5cc5ae4f03e91d8facdd4b98b549e07d23b1f59ba97316a13c0fa4763eb3752e62d32781f48ec7d66ea5cc5a44f03e91d8facdd4b98b449e07d23b1f59ba97316813c0fa4763eb3752e62cf2781f48ec7d66ea5cc59a4f03e91d8facdd4b98b309e07d23b1f59ba97316513c0fa4763eb3752e62c92781f48ec7d66ea5cc5904f03e91d8facdd4b98b1c9e07d23b1f59ba97316313c0fa4763eb3752e62c52781f48ec7d66ea5cc5884f03e91d8facdd4b98b0c9e07d23b1f59ba97316113c0fa4763eb3752e62c12781f48ec7d66ea5cc5804f03e91d8facdd4b98afc9e07d23b1f59ba97315f13c0fa4763eb3752e62bd2781f48ec7d66ea5cc5784f03e91d8facdd4b98aec9e07d23b1f59ba97315d13c0fa4763eb3752e62b92781f48ec7d66ea5cc5704f03e91d8facdd4b98ad09e07d23b1f59ba97315993c0fa4763eb3752e62b31f40d3) (
.leaf 23 0x8ec7d66ea62e5cc4f03e91d8facdd4c58b989e07d23b1f59ba98a97313c0fa4763eb3753142e62781f48ec7d66ea6245cc4f03e91d8facdd4c30b989e07d23b1f59ba98417313c0fa4763eb3753072e62781f48ec7d66ea60e4f03e822f1d8facdd4c18b989e07d23b1f59ba98217313c0fa4763eb3753022e62781f48ec7d66ea6025cc4f03e91d8facdd4bfcb989e07d23b1f59ba97f17313c0fa4763eb3752fd2e62781f48ec7d66ea5f85cc4f03e91d8facdd4be8b989e07d23b1f59ba97c17313c0fa4763eb3752f72e62781f48ec7d66ea5ea5cc4f03e91d8facdd4bd0b989e07d23b1f59ba97917313c0fa4763eb3752f02e62781f48ec7d66ea5d45cc4f03e91d8facdd4ba4b989e07d23b1f59ba97417313c0fa4763eb3752e72e62781f48ec7d66ea5cc5bc4f03e91d8facdd4b98b6c9e07d23b1f59ba97316d13c0fa4763eb3752e62d82781f4)) (
.fork 25 0x4763eb3753452e62781f4 (
.leaf 24 0x8ec7d66ea68a5cc4423e91d8facdd4d14b987d04363b1f59ba9a293c1108fa4763eb3753452781f40db8ec7d66ea6885cc4f03e91d8facdd4d0cb989e07d23b1f59ba9a117313c0fa4763eb3753412e62781f48ec7d66ea67a5cc4f03e91d8facdd4ce8b989e07d23b1f59ba99c17313c0fa4763eb3753332e62781f48ec7d66ea65e5cc4f03e91d8facdd4cb4b989e07d23b1f59ba99597313c0fa4763eb37532b2e62781c18ec7d66ea6565cc4f029f1d8facdd4cac9e07d07063b1f59ba99593c0fa069c763eb37532b2781f40b48ec7d66ea6545cc4f03e91d8facdd4ca89e07d07363b1f59ba99497313c0fa4763eb3753282e62781f48ec7d66ea64c5cc4f03e91d8facdd4c90b989e07d23b1f59ba99197313c0fa4763eb3753212e62781f48ec7d66ea63e5cc4f03e91d8facdd4c78b989e07d23b1f59ba98e97313c0fa4763eb37531c2e62781f4) (
.fork 26 0x4763eb38b3752e62781f4 (
.leaf 25 0x8ec7d67126ea5cc4f03e91d8face14dd4b989e07d23b1f59c21ba97313c0fa4763eb3823752e62781f48ec7d67006ea5cc4f03e91d8facde4dd4b989e07d23b1f59bc1ba97313c0fa4763eb3773752e62781f48ec7d66ec6ea5cc4f03e91d8facdd4dacb989e07d23b1f59ba9b517313c0fa4763eb3753692e62781f48ec7d66ea6d05cc4f03e91d8facdd4d90b989e07d23b1f59ba9b117313c0fa4763eb3753602e62781f48ec7d66ea6bc5cc4f03e91d8facdd4d74b989e07d23b1f59ba9ae17313c0fa4763eb37535b2e62781f48ec7d66ea6b45cc4f03e91d8facdd4d64b989e07d23b1f59ba9aa97313c0fa4763eb3753522e62781f48ec7d66ea6a05cc4f03e91d8facdd4d38b989e07d23b1f59ba9a617313c0fa4763eb37534a2e62781f48ec7d66ea6925cc4f03e91d8facdd4d20b989e07d23b1f59ba9a397313c0fa4763eb3753452e62781f4) (
.leaf 26 0x8ec7d67706ea5cc4f03e91d8faced8dd4b989e07d23b1f59db1ba97313c0e6c763eb3b63752e627815a8ec7d676c5cc4f03e839b1d8faced8b989e07d02663b1f59da9ba97313c0fa4763eb3b43752e62781f48ec7d67666ea5cc4f03e91d8facec4dd4b989e07d23b1f59d81ba97313c0fa4763eb3af3752e62781f48ec7d675a6ea5cc4f03e91d8faceacdd4b989e07d23b1f59d51ba97313c0fa4763eb3a53752e62781f48ec7d674a5cc4f03e829f1d8face90dd4b989e07d23b1f59d11ba97313c0fa4763eb3a03752e62781f48ec7d673e6ea5cc4f03e91d8face70dd4b989e07d23b1f59cd1ba97313c0fa4763eb3993752e62781f48ec7d67306ea5cc4f03e91d8face58dd4b989e07d23b1f59ca9ba97313c0fa4763eb3923752e62781f48ec7d67226ea5cc4f03e91d8face40dd4b989e07d23b1f59c69ba97313c0fa4763eb38b3752e62781f4))))) (
.fork 32 0x4bf3eb3752e62781f407b (
.fork 29 0x47643c3eb3752e62781f4 (
.fork 28 0x4764023eb3752e62781f4 (
.leaf 27 0x8ec8007d66ea5cc4f03e91d8fecfacdd4b989e07d23b1fd1f59ba97313c0fa4763f83eb3752e62781f48ec7ee7d66ea5cc4f03e91d8facf88dd4b989e07d23b1f59ee1ba97313c0fa4763eb3db3752e62781f48ec7d67aa6ea5cc4f03e91d8facf48dd4b989e07d23b1f59e89ba97313c0fa4763eb3ce3752e62781f48ec7d679a6ea5cc4f03e91d8facf30dd4b989e07d23b1f59e59ba97313c0fa4763eb3ca3752e62781f48ec7d678e6ea5cc4f03e91d8facf1cdd4b988e07d23b1f59e39ba9730fa0b54763eb3c73752e61f41178ec7d678e5cc4f04703e91d8facf1cb989e07d03b63b1f59e397313c0fa0514763eb3c63752e62781f48ec7d678c5cc4f04423e91d8facf10dd4b989e07d23b1f59e21ba9730fa0e6c763eb3c23752e62781f48ec7d67806ea5cc4f03e91d8facef8dd4b989e07d23b1f59de9ba97313c0fa4763eb3bb3752e62781f4) (
.leaf 28 0x8ec86e7d66ea5cc4f03e91d90dcdd4b989e07d078e3b21b1f59ba97313c0fa4764343eb3752e62781f48ec8607d66ea5cc4f03e91d90c0dd4b989e07d07363b2169f59ba97313c0fa4764293eb3752e62781f48ec8526ea5cc4f03e836b1d908cfacdd4b989e07d23b2111f59ba97313c0fa4764203eb3752e62781f48ec83e7d66ea5cc4f03e91d9078facdd4b989e07d23b20d9f59ba97313c0fa47641a3eb3752e62781f48ec8346ea5cc4f03e82471d9060facdd4b989e07d23b20b9f59ba97313c0fa4764173752e62781f41178ec8287d66ea5cc4f03e91d9044facdd4b989e07d23b2081f59ba97313c0fa4764103752e62781f40d38ec81c7d66ea5cc4f03e91d9030facdd4b989e07d23b2059f59ba97313c0fa4764063eb3752e62781f48ec80a7d66ea5cc4f03e91d9014dd4b989e07d02ba3b2019f59ba97313c0fa4764023eb3752e62781f4)) (
.fork 30 0x4764543eb3752e62781f4 (
.leaf 29 0x8ec8a86ea5cc5a04f03e91d914cfacdd4b989e07d23b2269f59ba97313c0fa47644b3eb3752e62781f48ec88e87a6ea5cc4f03e91d911cfacdd4b989e07d23b2239f59ba9731228fa4764473eb3752e61f416a8ec88e7d66ea5cc3e82391d911cdd4b989e09147d23b2239ba97313c0fa0b04764473752e62781f40648ec88c7d66ea5cc4f03e91d9118facdd4b987d07663b2229f59ba97313c0fa4764443eb3752e62781f48ec8847d66ea5cc4f03e91d9104facdd4b989e07d23b2201f59ba97313c0fa47643d3eb3752e62781f48ec87a7d66ea5cc4f03b31d90f4facdd4b989e05823b21e9f59aa97313c0fa47643d3eb2e62781f40ab8ec87a6ea5cc5884f03e91d90f4dd4b989e07d07663b21e9ba97313c0fa08e47643d3752e62781f40a78ec87a6ea5cc4f03e80d91d90f4dd4b989e07d017e3b21e9ba97313c0fa01d47643c3eb3752e62781f4) (
.fork 31 0x4854763eb3752e62781f4 (
.leaf 30 0x9068ec7d66ea5cc4f03e92091d8facdd4b989e07d23b2369f59ba97313c0fa4764673eb3752e62781f48ec8cc7d66ea5cc4f03e91d918cfacdd4b989e07d23b230a1e9ba97313c0fa4764613eb3752e62781f48ec8c27d66905cc4f03e91d9184facb989e07d03b63b2309f597313c0fa053c764613753482e62781f48ec8c26ea5cc4f048a3e91d9184dd4b989e07d05823b2309ba97313c0fa03b4764613752e62781f40648ec8c07d66ea5cc4f03e91d9180facb98b109e07d23b22f9f59ba97313c0fa47645e3eb3752e62781f48ec8b87d66ea5cc4f03e91d916cfacdd4b989e07d23b22b9f59ba97313c0fa4764573eb3752e62561f48ec8ae7d66ea5cc3e82411d915cfacdd4b109e07d23b22b9f59ba93c0fa071c764573752e62c42781f48ec8ae6ea5cc4f03e80d91d915cdd4b989e07d00ea3b22b1f59ba97313c0fa4764543eb3752e62781f4) (
.leaf 31 0x97e7d66ea5cc4f03e805b2fcfacdd4b989e07d008a5f23b1f59ba97313c0fa4b94763eb3752e62781f49727d66ea5cc4f03e83b32d51d8facdd4b989e07d25a9f59ba97313c0fa0e6cb24763eb3752e62781f495c8ec7d66ea5cc4f03e92b8facdd4b989e07d06d65523b1f59ba97313c0fa4a94763eb3752e62781f494e8ec7d66ea5cc4f03e92991d8facdd4b989e07d251a3b1f59ba97313c0fa4a24763eb3752e62781f49447d66ea5cc4f03e82392811d8facdd4b989e07d2501f59ba97313c0fa08bc9d4763eb3752e62781f49348ec7d66ea5cc4f03e92651d8facdd4b989e07d24c9f59ba97313c0fa069c974763eb3752e62781f492a8ec7d66ea5cc4f03e92411d8facdd4b989e07d247a3b1f59ba97313c0fa48f3eb3752e62781f40a791a8ec7d66ea5cc4f03e922d1d8facdd4b989e07d24323b1f59ba97313c0fa4854763eb3752e62781f4)))) (
.fork 34 0x4da4763752e62781f40e3 (
.fork 33 0x4cd4763eb3752781f40e8 (
.leaf 32 0x99a8ec7aa6ea5cc4f03e93351d8dd4b989e07d01fa669f59ba97316813c0fa4cd3eb3752e62781f407b99a7d66ea5cc4f03e805b3311d8facdd4b989e07d26523b1f59ba97313c0fa4ca3eb3752e62c42781f49928ec7d66ea5cc4f03e93192fcfacdd4b989e07d26323b1f59ba97313c0fa4c64763eb3752e625b1f498c8ec7d66ea5cc3e82d53191d8facdd4b987d048e631f59ba97313c12d8fa4c63eb3752e62781f416898c7d66ea5cc4f03e804d3151d8facdd4b989e07d262a3b1f59ba9730fa0f1cc44763eb3752e62781f49868ec7d66ea5cc4f03e93091d8facdd4b989e07d25fa3b1f59ba97313c0fa4bf4763eb3752e62781e397e8ec7d66ea5cc4f02d12fd1d8facd90b989e07d25fa3b1f597313c0fa0584bf3eb3752e62d02781f497e7d66ea5cc4f03e83c72fcfacdd4b989e07d048e5f9f59ba97313c0fa0574bf3eb3752e62781f407b) (
.leaf 33 0x9b48ec6ea5cc4f03e80f73691d8dd4b989e07d01da6d23b1ba97313c0fa0324da3eb3ca3752e62781f49b47d66ea6b65cc4f03e9368facdd4b989e096c7d26d1f59ba97313c0fa0b44da3eb3752e62781f40e89b47d66ea5cc4f03e8075368facdd4b989e07d00da6d1f59ba97313c0fa0134d74763eb3752e62781f49a88ec7d66ea5cc4f03e93492fcfacdd4b989e07d26923b1f59ba97313c0fa4d24763eb35b2e62781f49a48ec7d65cc4f03e81db3491d8facb989e07d02ba691f59ba9ad97313c0fa4d23eb3752e627825b1f49a47d66ea5cc4f03e82d1348facdd4b989e07d00da691f59ba97313c0fa0134d14763eb3752e62781f49a28ec7d65cc5a04f03e93411d8facdd4b989e07d267a3b1f59ba97313c0fa4cd4763eb3752e62781f499a8ec7d66ea5cc4cc3e93351d8facdd4b987d049666a3b1f59ba96813c0fa4cd4763eb3752781f40e8)) (
.fork 35 0x4e04764473eb3752e61f4 (
.leaf 34 0x9c08ec7d678e6ea5cc3e93811d8facdd4b989e07d27023b1f59ba97313c0dace04763eb3752e627816a9c08ec7d66ea5cc4423e93811d8facdd4b987d06d67023b1f59ba9730fa094ce04763eb3752e61f410d9c08ec7d66ea5cc3e81453811d8facdd4b987d01927023b1f59ba9730fa0134e04763eb3752de2781f49c08ec7d66ea4f03e81d93811d8facdacb989e07d27023b1f597313c0fa059ce04763dc3752e62781f49c08ec6ea5cc4f03e810338119cfacdd4b989e07d2701f59ba97313c0fa0204df4763eb3752e62781f49ba8ec7d66ea5cc4f03e93711d8facdd4b989e07d26d2669f59ba97313c0fa4da4bf3eb3752e62781f49b48ec8ae6ea5cc4f03e93691d90f4dd4b989e07d26d23b1f59ba97313c0fa4da4763ca3752e62781f49b48ec6ea6905cc4f03e93691d8dd4b989e09147d26d23b1ba97313c0fa0b04da4763752e62781f40e3) (
.fork 36 0x4e74763eb3752e62781f4 (
.leaf 35 0x9cc8ec7d66ea5cc4f03e93951d8facdd4b989e07d27223b1f59ba97313c0fa4e34d24763eb2e62781f49c68ec8c27d65cc4f03e938d1d8facf1cb989e07d271a3b1f59ba99593c0fa4e34763eb3752e62781f49c68ec7d66ea5cc4f03db38d1d8facdd4b989e05b671a3b1f59ba9731370fa4e34763eb3752e61f412c9c68ec7d66ea5744f03e938d1d8facdd49e08847d271a3b1f59ba93c0fa0a7ce34763eb3752781f40ed9c68ec7d66ea4f03e81b738d1d8facb98ae89e07d271a3b1f597313c0fa0e6ce34763eb2e62781f41179c68ec7d65cc4f03e816938d1d8facb989e07d026671a3b1f597313c0fa03b4e34763eb2e62781f40369c68ec7c46ea5cc4f03e938d1d8dd4b989e07d021671a369f59ba97313c0fa4e33eb3752e62781f40449c48ec7d66ea5cc4f03e93851d8facdd4b989e07d27026323b1f59ba9730fa4e04764473eb3752e61f4) (
.leaf 36 0x27623b1f59ba97313c0fa4eb4763eb3752e62781f49d48ec7d66ea5cc4f03e93a51d8facdd4b989e07d27423b1f59ba97313c0fa4e74763eb3752e62781f4))))))⟩

set_option maxRecDepth 16000 in
def bank7 : PackedSeq := ⟨60, 83, 0x7ffffffffffffffffffff, .fork 1 0x4763eb3752e62781f41cd (
.leaf 0 0x8ec7d66ea5cc4f03e83831d8facdd4b989e07d06d63b1f59ba97313c0fa0b54763eb3752e62781f41688ec7d66ea5cc4f03e82c11d8facdd4b989e07d056a3b1f59ba97313c0fa0a7c763eb3752e62781f41298ec7d66ea5cc4f03e82471d8facdd4b989e07d04723b1f59ba97313c0fa08bc763eb3752e62781f410d8ec7d66ea5cc4f03e81db1d8facdd4b989e07d03a23b1f59ba97313c0fa071c763eb3752e62781f40db8ec7d66ea5cc4f03e81a71d8facdd4b989e07d02d23b1f59ba97313c0fa0574763eb3752e62781f40a78ec7d66ea5cc4f03e81451d8facdd4b989e07d02663b1f59ba97313c0fa03dc763eb3752e62781f40768ec7d66ea5cc4f03e80d91d8facdd4b989e07d01923b1f59ba97313c0fa02fc763eb3752e62781f403a8ec7d66ea5cc4f03e806d1d8facdd4b989e07d00b63b1f59ba97313c0fa0134763eb3752e62781f4022) (
.leaf 1 0x9c68ec7d66ea5cc4f03e93811d8facdd4b989e07d26d23b1f59ba97313c0fa4d24763eb3752e62781f499a8ec7d66ea5cc4f03e93191d8facdd4b989e07d25fa3b1f59ba97313c0fa4764613eb3752e62781f48ec8ae7d66ea5cc4f03e91d911cfacdd4b989e07d23b21e9f59ba97313c0fa4763eb3ca3752e62781f48ec7d678e6ea5cc4f03e91d8faced8dd4b989e07d23b1f59ba9ad97313c0fa4763eb3753482e62781f48ec7d66ea68a5cc4f03e91d8facdd4cacb989e07d23b1f59ba97316813c0fa4763eb3752e62c42781f48ec7d66ea5cc5744f03e91d8facdd4b989e096c7d23b1f59ba97313c1228fa4763eb3752e62782381f48ec7d66ea5cc4f04423e91d8facdd4b989e07d078e3b1f59ba97313c0fa0ecc763eb3752e62781f41cd)⟩

set_option maxRecDepth 16000 in
def bank8 : PackedSeq := ⟨1, 71, 0x7fffffffffffffffff, .leaf 0 0x4763eb3752e62781f4⟩

def buckets (t : ℕ) : PackedSeq :=
  if t = 4 then bank4 else
  if t = 5 then bank5 else
  if t = 6 then bank6 else
  if t = 7 then bank7 else
  if t = 8 then bank8 else
  ⟨0, 0, 0, .leaf 0 0⟩

theorem bound_from_closure (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (table : ℕ → List W → Bool)
    (closure : ∀ t ws, table t ws = true → closedState table t ws = true)
    (root : rootClosed table 8 inputs = true)
    (sample : ∀ k : Fin 274, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 274) :
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
  exact rootClosed_sound table closure ht 8 inputs nd root (lift low run)

def table := tableFrom dict buckets

theorem tableClosure
    (h4 : blockCheck dict buckets 4 0 16 = true)
    (h5 : blockCheck dict buckets 5 0 977 = true)
    (h6 : blockCheck dict buckets 6 0 1158 = true)
    (h7 : blockCheck dict buckets 7 0 60 = true)
    (h8 : blockCheck dict buckets 8 0 1 = true)
    : ∀ t ws, table t ws = true → closedState table t ws = true := by
  intro t ws belongs
  obtain ⟨i,key,hk,rfl⟩ := tableFrom_sound _ _ _ _ belongs
  have ih := PackedSeq.at_bound hk
  have ready : blockCheck dict buckets t 0 (buckets t).size = true := by
    have ready4 : t = 4 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h4
    have ready5 : t = 5 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h5
    have ready6 : t = 6 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h6
    have ready7 : t = 7 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h7
    have ready8 : t = 8 → blockCheck dict buckets t 0 (buckets t).size = true := fun he => he.symm ▸ h8
    by_cases eq4 : t=4
    · exact ready4 eq4
    by_cases eq5 : t=5
    · exact ready5 eq5
    by_cases eq6 : t=6
    · exact ready6 eq6
    by_cases eq7 : t=7
    · exact ready7 eq7
    by_cases eq8 : t=8
    · exact ready8 eq8
    have empty : buckets t = ⟨0, 0, 0, .leaf 0 0⟩ := by simp [buckets,eq4,eq5,eq6,eq7,eq8]
    simp [empty,blockCheck]
  exact blockCheck_sound _ _ ready (Nat.zero_le _) (by simpa using ih) hk

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem sampleOK : ∀ k : Fin 274, F (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem joinChecks (t s a b : ℕ)
    (left : blockCheck dict buckets t s a = true)
    (right : blockCheck dict buckets t (s+a) b = true) :
    blockCheck dict buckets t s (a+b) = true := by
  unfold blockCheck at *
  apply List.all_eq_true.mpr
  intro i hi
  have bound := List.mem_range.mp hi
  by_cases cut : i < a
  · exact List.all_eq_true.mp left i (List.mem_range.mpr cut)
  · have upper : i-a < b := by omega
    have back : s+a+(i-a) = s+i := by omega
    simpa only [back] using List.all_eq_true.mp right (i-a) (List.mem_range.mpr upper)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held4Part0 : blockCheck dict buckets 4 0 16 = true := by
  decide +kernel

theorem held4 : blockCheck dict buckets 4 0 16 = true :=
  held4Part0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part0 : blockCheck dict buckets 5 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part32 : blockCheck dict buckets 5 32 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part64 : blockCheck dict buckets 5 64 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part96 : blockCheck dict buckets 5 96 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part128 : blockCheck dict buckets 5 128 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part160 : blockCheck dict buckets 5 160 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part192 : blockCheck dict buckets 5 192 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part224 : blockCheck dict buckets 5 224 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part256 : blockCheck dict buckets 5 256 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part288 : blockCheck dict buckets 5 288 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part320 : blockCheck dict buckets 5 320 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part352 : blockCheck dict buckets 5 352 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part384 : blockCheck dict buckets 5 384 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part416 : blockCheck dict buckets 5 416 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part448 : blockCheck dict buckets 5 448 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part480 : blockCheck dict buckets 5 480 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part512 : blockCheck dict buckets 5 512 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part544 : blockCheck dict buckets 5 544 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part576 : blockCheck dict buckets 5 576 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part608 : blockCheck dict buckets 5 608 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part640 : blockCheck dict buckets 5 640 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part672 : blockCheck dict buckets 5 672 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part704 : blockCheck dict buckets 5 704 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part736 : blockCheck dict buckets 5 736 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part768 : blockCheck dict buckets 5 768 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part800 : blockCheck dict buckets 5 800 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part832 : blockCheck dict buckets 5 832 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part864 : blockCheck dict buckets 5 864 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part896 : blockCheck dict buckets 5 896 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part928 : blockCheck dict buckets 5 928 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held5Part960 : blockCheck dict buckets 5 960 17 = true := by
  decide +kernel

theorem held5 : blockCheck dict buckets 5 0 977 = true :=
  (joinChecks 5 0 480 497 (joinChecks 5 0 224 256 (joinChecks 5 0 96 128 (joinChecks 5 0 32 64 held5Part0 (joinChecks 5 32 32 32 held5Part32 held5Part64)) (joinChecks 5 96 64 64 (joinChecks 5 96 32 32 held5Part96 held5Part128) (joinChecks 5 160 32 32 held5Part160 held5Part192))) (joinChecks 5 224 128 128 (joinChecks 5 224 64 64 (joinChecks 5 224 32 32 held5Part224 held5Part256) (joinChecks 5 288 32 32 held5Part288 held5Part320)) (joinChecks 5 352 64 64 (joinChecks 5 352 32 32 held5Part352 held5Part384) (joinChecks 5 416 32 32 held5Part416 held5Part448)))) (joinChecks 5 480 256 241 (joinChecks 5 480 128 128 (joinChecks 5 480 64 64 (joinChecks 5 480 32 32 held5Part480 held5Part512) (joinChecks 5 544 32 32 held5Part544 held5Part576)) (joinChecks 5 608 64 64 (joinChecks 5 608 32 32 held5Part608 held5Part640) (joinChecks 5 672 32 32 held5Part672 held5Part704))) (joinChecks 5 736 128 113 (joinChecks 5 736 64 64 (joinChecks 5 736 32 32 held5Part736 held5Part768) (joinChecks 5 800 32 32 held5Part800 held5Part832)) (joinChecks 5 864 64 49 (joinChecks 5 864 32 32 held5Part864 held5Part896) (joinChecks 5 928 32 17 held5Part928 held5Part960)))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part0 : blockCheck dict buckets 6 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part32 : blockCheck dict buckets 6 32 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part64 : blockCheck dict buckets 6 64 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part96 : blockCheck dict buckets 6 96 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part128 : blockCheck dict buckets 6 128 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part160 : blockCheck dict buckets 6 160 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part192 : blockCheck dict buckets 6 192 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part224 : blockCheck dict buckets 6 224 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part256 : blockCheck dict buckets 6 256 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part288 : blockCheck dict buckets 6 288 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part320 : blockCheck dict buckets 6 320 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part352 : blockCheck dict buckets 6 352 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part384 : blockCheck dict buckets 6 384 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part416 : blockCheck dict buckets 6 416 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part448 : blockCheck dict buckets 6 448 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part480 : blockCheck dict buckets 6 480 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part512 : blockCheck dict buckets 6 512 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part544 : blockCheck dict buckets 6 544 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part576 : blockCheck dict buckets 6 576 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part608 : blockCheck dict buckets 6 608 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part640 : blockCheck dict buckets 6 640 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part672 : blockCheck dict buckets 6 672 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part704 : blockCheck dict buckets 6 704 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part736 : blockCheck dict buckets 6 736 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part768 : blockCheck dict buckets 6 768 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part800 : blockCheck dict buckets 6 800 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part832 : blockCheck dict buckets 6 832 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part864 : blockCheck dict buckets 6 864 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part896 : blockCheck dict buckets 6 896 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part928 : blockCheck dict buckets 6 928 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part960 : blockCheck dict buckets 6 960 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part992 : blockCheck dict buckets 6 992 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1024 : blockCheck dict buckets 6 1024 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1056 : blockCheck dict buckets 6 1056 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1088 : blockCheck dict buckets 6 1088 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1120 : blockCheck dict buckets 6 1120 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held6Part1152 : blockCheck dict buckets 6 1152 6 = true := by
  decide +kernel

theorem held6 : blockCheck dict buckets 6 0 1158 = true :=
  (joinChecks 6 0 576 582 (joinChecks 6 0 288 288 (joinChecks 6 0 128 160 (joinChecks 6 0 64 64 (joinChecks 6 0 32 32 held6Part0 held6Part32) (joinChecks 6 64 32 32 held6Part64 held6Part96)) (joinChecks 6 128 64 96 (joinChecks 6 128 32 32 held6Part128 held6Part160) (joinChecks 6 192 32 64 held6Part192 (joinChecks 6 224 32 32 held6Part224 held6Part256)))) (joinChecks 6 288 128 160 (joinChecks 6 288 64 64 (joinChecks 6 288 32 32 held6Part288 held6Part320) (joinChecks 6 352 32 32 held6Part352 held6Part384)) (joinChecks 6 416 64 96 (joinChecks 6 416 32 32 held6Part416 held6Part448) (joinChecks 6 480 32 64 held6Part480 (joinChecks 6 512 32 32 held6Part512 held6Part544))))) (joinChecks 6 576 288 294 (joinChecks 6 576 128 160 (joinChecks 6 576 64 64 (joinChecks 6 576 32 32 held6Part576 held6Part608) (joinChecks 6 640 32 32 held6Part640 held6Part672)) (joinChecks 6 704 64 96 (joinChecks 6 704 32 32 held6Part704 held6Part736) (joinChecks 6 768 32 64 held6Part768 (joinChecks 6 800 32 32 held6Part800 held6Part832)))) (joinChecks 6 864 160 134 (joinChecks 6 864 64 96 (joinChecks 6 864 32 32 held6Part864 held6Part896) (joinChecks 6 928 32 64 held6Part928 (joinChecks 6 960 32 32 held6Part960 held6Part992))) (joinChecks 6 1024 64 70 (joinChecks 6 1024 32 32 held6Part1024 held6Part1056) (joinChecks 6 1088 32 38 held6Part1088 (joinChecks 6 1120 32 6 held6Part1120 held6Part1152))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held7Part0 : blockCheck dict buckets 7 0 32 = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held7Part32 : blockCheck dict buckets 7 32 28 = true := by
  decide +kernel

theorem held7 : blockCheck dict buckets 7 0 60 = true :=
  (joinChecks 7 0 32 28 held7Part0 held7Part32)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem held8Part0 : blockCheck dict buckets 8 0 1 = true := by
  decide +kernel

theorem held8 : blockCheck dict buckets 8 0 1 = true :=
  held8Part0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem checkedRoot : rootClosed table 8 rows = true := by
  decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 8 < binaryCost gs :=
  bound_from_closure rows rfl (by decide) table
    (tableClosure held4 held5 held6 held7 held8) checkedRoot sampleOK gs o hg he

end Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upper : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [6, 14]⟩], 15⟩
def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem upper_mono : Monotone2 upper := by
  intro g mem
  simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_correct : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) = target x := by decide +kernel
theorem agree : ∀ x : Fin 6 → Bool, target x = Signed.F x := by decide +kernel

end PEqualNP.Outside.L_meta_16243

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_16243 in
theorem PEqualNP.Outside.L_meta_16243 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940592256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨D,fit,sz,comp⟩ := h
  by_cases hasNot : ∃ g ∈ D.gates, g.op = GateOp.not
  · obtain ⟨g,mem,op⟩ := hasNot
    have short : Signed.binaryCost D.gates < D.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,mem,by simp [Signed.isBinary,op]⟩
    have legal : ∀ a ∈ D.gates, Signed.legal a := by
      intro a am
      have ready := fit a am
      simpa [Signed.legal] using ready
    have lower := Signed.bound D.gates D.output legal (fun x => (comp x).trans (agree x))
    have usize : upper.size = 10 := rfl
    change D.gates.length ≤ s at sz
    exact ⟨upper,upper_mono,by omega,upper_correct⟩
  · refine ⟨D, ?_,sz,comp⟩
    intro g mem
    have fitG := fit g mem
    refine ⟨?_,fitG.2⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *
    rcases fitG.1 with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hasNot ⟨g,mem,hn⟩).elim
