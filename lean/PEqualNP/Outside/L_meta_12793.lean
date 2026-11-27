import Mathlib
import PEqualNP.Defs

-- Signed circuit normalization and live-wire search adapted from L-meta-9564 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_12793.Signed

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

abbrev W := BitVec 64
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def goal : W := ~~~0xfeeaeaaafeeaeaaa
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

def mask (row : Fin 64) (w : W) : W := if w[row.val] then w else ~~~w

def same (row : Fin 64) (ws : List W) : W :=
  ws.foldr (fun w a => mask row w &&& a) (~~~0)

theorem same_spec (r s : Fin 64) (ws : List W) :
    (same r ws)[s.val] = true ↔ ∀ w ∈ ws, w[r.val] = w[s.val] := by
  induction ws with
  | nil =>
    change (BitVec.allOnes 64)[s.val] = true ↔ _
    simpa only [List.not_mem_nil, false_implies, implies_true, iff_true] using
      (BitVec.getElem_allOnes s.val s.isLt)
  | cons w tail ih =>
    rw [show same r (w :: tail) = mask r w &&& same r tail from rfl,
      BitVec.getElem_and, Bool.and_eq_true, ih, List.forall_mem_cons]
    simp only [mask]
    split <;> simp_all

theorem ops_differs (r s : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : z[r.val] ≠ z[s.val]) : a[r.val] ≠ a[s.val] ∨ b[r.val] ≠ b[s.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! h
  apply hd
  rcases hz with rfl | rfl | rfl | rfl <;> simp [h.1, h.2]

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
  (ops a b).any fun w =>
    (!(w == a || w == b || r.contains w)) && (next extra (w :: r) ||
    ((extra != 0) && (next (extra - 1) (w :: a :: r) || next (extra - 1) (w :: b :: r))) ||
    ((extra ≥ 2) && next (extra - 2) (w :: a :: b :: r)))

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (out : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (ht : next (k - kept.length) (z :: kept) = true) : dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have hz' : (z == a || z == b || r.contains z) = false := by simpa [and_assoc] using out
  rw [hz']
  simp only [Bool.not_false, Bool.true_and]
  simp [keepChoices] at hk
  rcases hk with e | e | e | e <;> subst kept <;> (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]
  · left; left
    rwa [show extra = k - r.length by omega]
  · left; right; refine ⟨by omega, .inl ?_⟩
    rwa [show extra - 1 = k - (r.length + 1) by omega]
  · left; right; refine ⟨by omega, .inr ?_⟩
    rwa [show extra - 1 = k - (r.length + 1) by omega]
  · right; refine ⟨by omega, ?_⟩
    rwa [show extra - 2 = k - (r.length + 1 + 1) by omega]

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

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

-- Two wire banks describe the sections x₅ = false and x₅ = true.
-- Until a binary gate can be skipped, all differing wires are constant on the false section.
def Stable (left right : W) : Prop := left = right ∨ left = 0 ∨ left = ~~~0

def StableBanks (left right : List W) : Prop :=
  left.length = right.length ∧ ∀ i : ℕ, Stable (left.getD i 0) (right.getD i 0)

theorem StableBanks.append {left right : List W} {u v : W}
    (h : StableBanks left right) (wire : Stable u v) :
    StableBanks (left ++ [u]) (right ++ [v]) := by
  constructor
  · simpa using h.1
  · intro i
    by_cases lower : i < left.length
    · rw [List.getD_append _ _ _ _ lower, List.getD_append _ _ _ _ (h.1 ▸ lower)]
      exact h.2 i
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt lower),
        List.getD_append_right _ _ _ _ (h.1 ▸ Nat.le_of_not_gt lower), ← h.1]
      cases i - left.length with
      | zero => exact wire
      | succ k => simp [List.getD_eq_getElem?_getD, Stable]

theorem stable_not {left right : W} (h : Stable left right) : Stable (~~~left) (~~~right) := by
  rcases h with rfl | rfl | eq
  · exact .inl rfl
  · exact .inr (.inr rfl)
  · exact .inr (.inl (by rw [eq, BitVec.not_not]))

theorem not_preserves {left right : List W} {g : Gate} (h : StableBanks left right)
    (hop : isBinary g = false) : Stable (action left g) (action right g) := by
  obtain ⟨op, ins⟩ := g
  have eq : op = GateOp.not := by cases op <;> simp_all [isBinary]
  subst op
  cases ins with
  | nil => exact .inl rfl
  | cons i tail => exact stable_not (h.2 i)

theorem changing_binary_is_free {left right : List W} {available : Finset W} {g : Gate}
    (h : StableBanks left right) (hw : ∀ w ∈ left, holds available w) (legalGate : legal g)
    (hop : isBinary g = true) (different : action left g ≠ action right g) :
    holds available (action left g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨opLegal, arity⟩ := legalGate
  change (op = .and ∨ op = .or ∨ op = .not) at opLegal
  change ins.length ≤ 2 at arity
  rcases opLegal with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · exact .inr (.inl rfl)
    · change holds available (left.getD i 0 &&& BitVec.allOnes 64)
      rw [BitVec.and_allOnes]
      exact available_read hw i
    · have val (w : List W) : action w ⟨.and, [i,j]⟩ = w.getD i 0 &&& w.getD j 0 := by
        change (_ &&& (_ &&& BitVec.allOnes 64)) = _
        rw [BitVec.and_allOnes]
      simp only [val] at different ⊢
      rcases h.2 i with e | e | e
      · rcases h.2 j with f | f | f
        · exact (different (by rw [e, f])).elim
        · rw [f]
          exact (BitVec.and_zero (x := left.getD i 0)).symm ▸ (.inl rfl : holds available 0)
        · rw [f]
          exact (BitVec.and_allOnes (x := left.getD i 0)).symm ▸ available_read hw i
      · rw [e]
        exact (BitVec.zero_and (x := left.getD j 0)).symm ▸ (.inl rfl : holds available 0)
      · rw [e]
        exact (BitVec.allOnes_and (x := left.getD j 0)).symm ▸ available_read hw j
    · simp at arity
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · exact .inl rfl
    · simpa [action] using available_read hw i
    · have val (w : List W) : action w ⟨.or, [i,j]⟩ = w.getD i 0 ||| w.getD j 0 := by
        change (w.getD i 0 ||| (w.getD j 0 ||| 0#64)) = _
        rw [BitVec.or_zero]
      simp only [val] at different ⊢
      rcases h.2 i with e | e | e
      · rcases h.2 j with f | f | f
        · exact (different (by rw [e, f])).elim
        · rw [f]
          exact (BitVec.or_zero (x := left.getD i 0)).symm ▸ available_read hw i
        · rw [f]
          exact (BitVec.or_allOnes (x := left.getD i 0)).symm ▸ (.inr (.inl rfl) : holds available (~~~0))
      · rw [e]
        exact (BitVec.zero_or (x := left.getD j 0)).symm ▸ available_read hw j
      · rw [e]
        exact (BitVec.allOnes_or (x := left.getD j 0)).symm ▸ (.inr (.inl rfl) : holds available (~~~0))
    · simp at arity
  · simp [isBinary] at hop

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem compile_saves (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (left right : List W) (available : Finset W) (stable : StableBanks left right)
    (hw : ∀ w ∈ left, holds available w)
    (evalLeft : ∀ k, (gs.foldl step (left.map (bit k))).getD out false = bit k (~~~goal))
    (different : ((gs.foldl (fun w g => w ++ [action w g]) left).getD out 0) ≠
      ((gs.foldl (fun w g => w ++ [action w g]) right).getD out 0)) :
    ∃ t k, (t = goal ∨ t = ~~~goal) ∧ k < binaryCost gs ∧ build basicOps t k available := by
  induction gs generalizing left right available with
  | nil =>
    have val : left.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      simpa only [List.foldl_nil, read_bit, bit] using evalLeft ⟨j, hj⟩
    rcases stable.2 out with same | c | c
    · exact (different same).elim
    · exact ((by decide : ~~~goal ≠ 0) (val.symm.trans c)).elim
    · exact ((by decide : ~~~goal ≠ ~~~0) (val.symm.trans c)).elim
  | cons g gs ih =>
    let u := action left g
    let v := action right g
    have hg' := hg g (by simp)
    have tailLegal : ∀ g ∈ gs, legal g := fun g mem => hg g (by simp [mem])
    have tailEval : ∀ k, (gs.foldl step ((left ++ [u]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k
      simpa only [List.foldl_cons, action_spec left g hg' k] using evalLeft k
    have tailDifferent : ((gs.foldl (fun w g => w ++ [action w g]) (left ++ [u])).getD out 0) ≠
        ((gs.foldl (fun w g => w ++ [action w g]) (right ++ [v])).getD out 0) := different
    have held (bank : Finset W) (old : ∀ w ∈ left, holds bank w) (new : holds bank u) :
        ∀ w ∈ left ++ [u], holds bank w := by
      intro w mem
      rcases List.mem_append.mp mem with hm | hm
      · exact old w hm
      · exact (List.mem_singleton.mp hm).symm ▸ new
    have stepClass := gate_reach left available hw g hg'
    cases hop : isBinary g with
    | false =>
      simp only [hop, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, hop] using
        ih tailLegal (left ++ [u]) (right ++ [v]) available
          (stable.append (not_preserves stable hop)) (held available hw stepClass) tailEval tailDifferent
    | true =>
      have size : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, hop]
      simp only [hop, ite_true] at stepClass
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := compile gs out tailLegal (left ++ [u]) available
          (held available hw existing) tailEval
        exact ⟨t, binaryCost gs, ht, by omega, run⟩
      · by_cases diff : u ≠ v
        · have existing := changing_binary_is_free stable hw hg' hop diff
          obtain ⟨t, ht, run⟩ := compile gs out tailLegal (left ++ [u]) available
            (held available hw existing) tailEval
          exact ⟨t, binaryCost gs, ht, by omega, run⟩
        · let bank := insert new available
          obtain ⟨t, k, ht, hk, run⟩ :=
            ih tailLegal (left ++ [u]) (right ++ [v]) bank (stable.append (.inl (not_ne_iff.mp diff)))
              (held bank (fun w hm => holds_insert (hw w hm)) rep) tailEval tailDifferent
          exact ⟨t, k + 1, ht, by omega, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

private theorem word_execution (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (k : Fin 64) :
    (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((gs.foldl (fun w g => w ++ [action w g]) w).getD out 0) := by
  induction gs generalizing w with
  | nil => exact read_bit w out k
  | cons g gs ih =>
    simp only [List.foldl_cons, action_spec w g (hg g (by simp)) k]
    exact ih (fun g m => hg g (by simp [m])) _

def inputs : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00, 0xffff0000ffff0000]

def bank (b : Bool) : List W := [if b then (~~~0) else 0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000]

def sectionInput (b : Bool) (i : Fin 64) (j : Fin 6) : Bool := bit i ((bank b).getD j.val 0)

theorem bank_initial : StableBanks (bank false) (bank true) := by
  constructor
  · rfl
  · intro i
    by_cases h : i < 6
    · interval_cases i <;> unfold Stable <;> decide
    · have h₁ : (bank false).length ≤ i := by exact Nat.le_of_not_gt h
      have h₂ : (bank true).length ≤ i := by exact Nat.le_of_not_gt h
      exact .inl ((List.getD_eq_default _ _ h₁).trans (List.getD_eq_default _ _ h₂).symm)

set_option maxRecDepth 10000 in
theorem bank_holds : ∀ w ∈ bank false, holds inputs.toFinset w := by
  intro w mem
  simp only [bank, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)

theorem mapped_input : ∀ b i, (bank b).map (bit i) = List.ofFn (sectionInput b i) := by
  decide +kernel

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4294901486 * 2 ^ 32 + 4277071598) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 10000 in
theorem target_false : ∀ i, target (sectionInput false i) = bit i (~~~goal) := by
  decide +kernel

theorem target_switch : target (sectionInput false 0) ≠ target (sectionInput true 0) := by
  decide +kernel

theorem extend_build {t : W} {k l : ℕ} {ws : Finset W} (h : k ≤ l)
    (run : build basicOps t k ws) : build basicOps t l ws := by
  induction h with
  | refl => exact run
  | step h ih => exact Or.inl ih

def feasibleFor (target : W) (negative : List (Fin 64)) (ws : List W) : Bool :=
  negative.all fun row => (same row ws &&& target) == 0

theorem feasibleFor_from_subset {target : W} {negative : List (Fin 64)}
    (valid : ∀ r ∈ negative, target[r.val] = false) {k : ℕ} {ws : List W} {s : Finset W}
    (run : live basicOps target k s) (sub : s ⊆ ws.toFinset) : feasibleFor target negative ws = true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getElem_eq
  intro s hs
  let j : Fin 64 := ⟨s, hs⟩
  change ((same r ws &&& target)[j.val]) = (0#64)[j.val]
  have rhs : (0#64)[j.val] = false := by simp
  rw [BitVec.getElem_and, rhs]
  cases pos : (target)[j.val] with
  | false => simp
  | true =>
    have diff : target[r.val] ≠ target[j.val] := by rw [valid r hr, pos]; decide
    obtain ⟨w, mem, unlike⟩ := live_separates (fun w => w[r.val] ≠ w[j.val]) diff
      (ops_differs r j) run
    have n : (same r ws)[j.val] ≠ true := fun h =>
      unlike ((same_spec r j ws).mp h w (List.mem_toFinset.mp (sub mem)))
    cases h : (same r ws)[j.val] <;> simp_all

theorem feasibleFor_of_live {target : W} {negative : List (Fin 64)}
    (valid : ∀ r ∈ negative, target[r.val] = false) {k : ℕ} {ws : List W}
    (run : live basicOps target k ws.toFinset) : feasibleFor target negative ws = true :=
  feasibleFor_from_subset valid run (fun _ h => h)

def optimizedFor (target : W) (negative : List (Fin 64)) : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [target])
  | k + 1, extra, ws => (ws == [target]) ||
    (feasibleFor target negative ws && (pairs ws).any (fun (a, b, r) => dispatch extra (optimizedFor target negative k) a b r))

set_option maxRecDepth 100000 in
theorem optimizedFor_complete {target : W} {negative : List (Fin 64)}
    (valid : ∀ r ∈ negative, target[r.val] = false) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps target n ws.toFinset) :
    optimizedFor target negative n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimizedFor, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimizedFor, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimizedFor target negative k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps target k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimizedFor target negative k) hop (fun hz => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))) hk (by omega) (by omega)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimizedFor, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      right
      refine ⟨feasibleFor_of_live valid h, ?_⟩
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem bound_from_local_search {t : W} {negative : List (Fin 64)} {inputs : List W} {n : ℕ}
    (valid : ∀ r ∈ negative, t[r.val] = false) (distinct : inputs.Nodup)
    (needAll : ∀ ws ∈ inputs.sublists, feasibleFor t negative ws = true → ws = inputs)
    (none : optimizedFor t negative n (n + 1 - inputs.length) inputs = false)
    (run : build basicOps t n inputs.toFinset) : False := by
  obtain ⟨s, sub, liveRun⟩ := compress run
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  have onWs : live basicOps t n ws.toFinset := eq.symm ▸ liveRun
  have mem : ws ∈ inputs.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have sameBank : ws = inputs := needAll ws mem (feasibleFor_of_live valid onWs)
  rw [sameBank] at onWs
  have small := live_card onWs
  rw [List.toFinset_card_of_nodup distinct] at small
  have yes := optimizedFor_complete valid n inputs (n + 1 - inputs.length) distinct (by omega) onWs
  exact Bool.noConfusion (none.symm.trans yes)

theorem build_preserves_zero {t n ws} (h : build basicOps t n ws) {r : Fin 64}
    (keep : ∀ w ∈ ws, w[r.val] = false) : t[r.val] = false := by
  induction n generalizing ws with
  | zero => exact keep _ h
  | succ n ih =>
    rcases h with shorter | ⟨a,ha,b,hb,_,z,hz,tail⟩
    · exact ih shorter keep
    · have za := keep a ha
      have zb := keep b hb
      simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      apply ih tail
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hz with rfl | rfl | rfl | rfl <;> simp [za, zb]
      · exact keep w hw

def rows : List (Fin 64) := [0, 2, 4, 6, 8, 10, 12, 16, 18, 20, 24]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem search_root : optimizedFor (~~~goal) rows 6 2 inputs = false := by
  decide +kernel

set_option maxRecDepth 32768 in
private theorem need_all : ∀ ws ∈ inputs.sublists,
    feasibleFor (~~~goal) rows ws = true → ws = inputs := by decide +kernel

private theorem no_small_section {t : W} (eitherSign : t = goal ∨ t = ~~~goal)
    (candidate : build basicOps t 6 inputs.toFinset) : False := by
  have allZero : inputs.all (fun w : W => !w[0]) = true := by decide +kernel
  have low := build_preserves_zero (r := (0 : Fin 64)) candidate (by
    intro w mem
    have check := List.all_eq_true.mp allZero w (List.mem_toFinset.mp mem)
    cases e : w[0] <;> simp_all)
  have eq : t = ~~~goal := eitherSign.resolve_left (by intro h; rw [h] at low; contradiction)
  subst t
  exact bound_from_local_search (negative := rows) (by decide) (by decide) need_all search_root candidate

set_option maxHeartbeats 0 in
theorem original_binary_lower (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, legal g) (eval : ∀ x, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    8 ≤ binaryCost gs := by
  have computed (b : Bool) (i : Fin 64) :
      (gs.foldl step ((bank b).map (bit i))).getD out false = target (sectionInput b i) := by
    rw [mapped_input]
    exact eval _
  have changed : (gs.foldl (fun w g => w ++ [action w g]) (bank false)).getD out 0 ≠
      (gs.foldl (fun w g => w ++ [action w g]) (bank true)).getD out 0 := by
    intro h
    apply target_switch
    rw [← computed false 0, ← computed true 0,
      word_execution gs out hg (bank false) 0, word_execution gs out hg (bank true) 0, h]
  obtain ⟨t, k, ht, budget, run⟩ := compile_saves gs out hg (bank false) (bank true)
    inputs.toFinset bank_initial bank_holds (fun i => (computed false i).trans (target_false i)) changed
  by_contra! h
  have hk : k ≤ 6 := by omega
  exact no_small_section ht (extend_build hk run)



end PEqualNP.Outside.L_meta_12793.Signed

namespace PEqualNP.Outside.L_meta_12793

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The threshold term requires a true input from each pair and one entirely true pair.
def upper : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [10, 11]⟩,
    ⟨.or, [0, 1]⟩, ⟨.or, [13, 12]⟩], 14⟩

private theorem upper_size : upper.size = 9 := rfl

private theorem upper_legal : Monotone2 upper := by
  intro g member
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem upper_eval : ∀ x : Fin 6 → Bool,
    upper.eval (List.ofFn x) = Signed.target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12793

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12793 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_12793 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4277071598) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4277071598) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, legal, cap, eval⟩ := h
  have hg : ∀ g ∈ C.gates, Signed.legal g := by
    simpa only [FanInTwo, Signed.legal, Set.mem_insert_iff, Set.mem_singleton_iff] using legal
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, member, op⟩ := hn
    have smaller : Signed.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr
        ⟨g, member, by cases g; simp_all [Signed.isBinary]⟩
    have lower := Signed.original_binary_lower C.gates C.output hg eval
    change C.gates.length ≤ s at cap
    exact ⟨upper, upper_legal, by rw [upper_size]; omega, upper_eval⟩
  · refine ⟨C, ?_, cap, eval⟩
    intro g member
    obtain ⟨op, arity⟩ := hg g member
    refine ⟨?_, arity⟩
    rcases op with op | op | op
    · simp [op]
    · simp [op]
    · exact (hn ⟨g, member, op⟩).elim
