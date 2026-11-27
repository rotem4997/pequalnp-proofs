import Mathlib
import PEqualNP.Defs

-- Signed circuit normalization and live-wire search adapted from L-meta-9564 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_10588.Signed

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
def goal : W := ~~~0xfffffffefefaeca0
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

def negatives : List (Fin 64) := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 32]

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

theorem negatives_spec (r : Fin 64) (h : r ∈ negatives) : (~~~goal)[r.val] = false := by
  have v : ∀ r : Fin 64, r ∈ negatives → (~~~goal)[r.val] = false := by decide +kernel
  exact v r h

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
  0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def bank (b : Bool) : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00, 0xffff0000ffff0000, if b then (~~~0) else 0, 0xffffffff00000000]

def sectionInput (b : Bool) (i : Fin 64) (j : Fin 7) : Bool := bit i ((bank b).getD j.val 0)

theorem bank_initial : StableBanks (bank false) (bank true) := by
  constructor
  · rfl
  · intro i
    by_cases h : i < 7
    · interval_cases i <;> unfold Stable <;> decide
    · have h₁ : (bank false).length ≤ i := by exact Nat.le_of_not_gt h
      have h₂ : (bank true).length ≤ i := by exact Nat.le_of_not_gt h
      exact .inl ((List.getD_eq_default _ _ h₁).trans (List.getD_eq_default _ _ h₂).symm)

set_option maxRecDepth 10000 in
theorem bank_holds : ∀ w ∈ bank false, holds inputs.toFinset w := by
  intro w mem
  simp only [bank, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)
  · exact .inl rfl
  · exact .inr (.inr ⟨_, by decide, .inl rfl⟩)

theorem mapped_input : ∀ b i, (bank b).map (bit i) = List.ofFn (sectionInput b i) := by
  decide +kernel

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 10000 in
theorem target_false : ∀ i, target (sectionInput false i) = bit i (~~~goal) := by
  decide +kernel

theorem target_switch : target (sectionInput false 1) ≠ target (sectionInput true 1) := by
  decide +kernel

theorem extend_build {t : W} {k l : ℕ} {ws : Finset W} (h : k ≤ l)
    (run : build basicOps t k ws) : build basicOps t l ws := by
  induction h with
  | refl => exact run
  | step h ih => exact Or.inl ih

/-- The charged parts of a run with respect to a restriction of its truth table. -/
structure Fuse where
  left : W
  right : W
  result : W

def restrictWord (m w : W) : W := m &&& w

def cheap (m : W) (p : Fuse) : Bool :=
  (restrictWord m p.result == 0) || (restrictWord m p.result == restrictWord m p.left) ||
    (restrictWord m p.result == restrictWord m p.right)

inductive Trace (t : W) : ℕ → Finset W → List Fuse → Prop where
  | done : Trace t 0 {t} []
  | skip {n ws tr} : Trace t n ws tr → Trace t (n + 1) ws tr
  | fuse {n ws tail a b z tr} : a ∈ ws → b ∈ ws → a ≠ b → z ∈ basicOps a b → z ∉ ws →
      ws = insert a (insert b tail) → Trace t n (insert z tail) tr →
      Trace t (n + 1) ws (⟨a,b,z⟩ :: tr)

theorem Trace.live {t n ws tr} (h : Trace t n ws tr) : live basicOps t n ws := by
  induction h with
  | done => rfl
  | skip _ ih => exact Or.inl ih
  | fuse ha hb ab hz fresh set _ ih => exact Or.inr ⟨_,ha,_,hb,ab,_,hz,fresh,_,set,ih⟩

theorem Trace.len {t n ws tr} (h : Trace t n ws tr) : tr.length ≤ n := by
  induction h with
  | done => decide
  | skip _ ih => omega
  | fuse _ _ _ _ _ _ _ ih => simpa using ih

theorem trace_of_live {t n ws} (h : live basicOps t n ws) : ∃ tr, Trace t n ws tr := by
  induction n generalizing ws with
  | zero =>
    change ws = {t} at h
    subst ws
    exact ⟨[], .done⟩
  | succ n ih =>
    rcases h with prev | ⟨a,ha,b,hb,ab,z,hz,fresh,s,eq,tail⟩
    · obtain ⟨tr, h⟩ := ih prev
      exact ⟨tr, .skip h⟩
    · obtain ⟨tr, h⟩ := ih tail
      exact ⟨_, .fuse ha hb ab hz fresh eq h⟩

theorem first_trace {t n ws tr} (h : Trace t (n + 1) ws tr) :
    (ws = {t} ∧ tr = []) ∨
    ∃ a ∈ ws, ∃ b ∈ ws, a ≠ b ∧ ∃ z ∈ basicOps a b, z ∉ ws ∧ ∃ s tail,
      ws = insert a (insert b s) ∧ tr = (⟨a,b,z⟩ : Fuse) :: tail ∧ Trace t n (insert z s) tail := by
  induction n generalizing ws tr with
  | zero =>
    cases h with
    | skip h => cases h; exact .inl ⟨rfl,rfl⟩
    | fuse ha hb ab hz fresh eq tail => exact .inr ⟨_,ha,_,hb,ab,_,hz,fresh,_,_,eq,rfl,tail⟩
  | succ n ih =>
    cases h with
    | skip h =>
      rcases ih h with base | ⟨a,ha,b,hb,ab,z,hz,fresh,s,l,eq,tr,tail⟩
      · exact .inl base
      · exact .inr ⟨a,ha,b,hb,ab,z,hz,fresh,s,l,eq,tr,.skip tail⟩
    | fuse ha hb ab hz fresh eq tail => exact .inr ⟨_,ha,_,hb,ab,_,hz,fresh,_,_,eq,rfl,tail⟩

def projected (m : W) (ws : Finset W) : Finset W := (ws.image (restrictWord m)).erase 0

theorem projected_insert (m z : W) (ws : Finset W) :
    projected m (insert z ws) =
      if restrictWord m z = 0 then projected m ws else insert (restrictWord m z) (projected m ws) := by
  by_cases h : restrictWord m z = 0
  · ext q; simp [projected, Finset.image_insert, h]
  · ext q; simp [projected, Finset.image_insert]; grind

theorem projected_mem (m : W) {w : W} {ws : Finset W} (h : w ∈ ws) (nz : restrictWord m w ≠ 0) :
    restrictWord m w ∈ projected m ws :=
  Finset.mem_erase.mpr ⟨nz, Finset.mem_image_of_mem _ h⟩

theorem projected_op (m : W) {a b z : W} (h : z ∈ basicOps a b) :
    restrictWord m z ∈ basicOps (restrictWord m a) (restrictWord m b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  have calcAnd : restrictWord m (a &&& b) = restrictWord m a &&& restrictWord m b := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [restrictWord, BitVec.getElem_and]
    cases m[i] <;> simp
  have calcOr : restrictWord m (a ||| b) = restrictWord m a ||| restrictWord m b := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [restrictWord, BitVec.getElem_and, BitVec.getElem_or]
    cases m[i] <;> simp
  have calcMinus (a b : W) : restrictWord m (a &&& ~~~b) = restrictWord m a &&& ~~~(restrictWord m b) := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [restrictWord, BitVec.getElem_and, BitVec.getElem_not]
    cases m[i] <;> simp
  rcases h with rfl | rfl | rfl | rfl
  · exact .inl calcAnd
  · exact .inr (.inl calcOr)
  · exact .inr (.inr (.inl (calcMinus a b)))
  · exact .inr (.inr (.inr (calcMinus b a)))

theorem productive_inputs {a b z : W} (h : z ∈ basicOps a b)
    (nz : z ≠ 0) (ea : z ≠ a) (eb : z ≠ b) : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  have cases_op := List.mem_toFinset.mp h
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at cases_op
  have a0 : a ≠ 0 := by
    rintro rfl
    rcases cases_op with rfl | rfl | rfl | rfl
    · exact nz BitVec.zero_and
    · exact eb BitVec.zero_or
    · exact nz BitVec.zero_and
    · exact eb BitVec.and_allOnes
  have b0 : b ≠ 0 := by
    rintro rfl
    rcases cases_op with rfl | rfl | rfl | rfl
    · exact nz BitVec.and_zero
    · exact ea BitVec.or_zero
    · exact ea BitVec.and_allOnes
    · exact nz BitVec.zero_and
  have dif : a ≠ b := by
    rintro rfl
    rcases cases_op with rfl | rfl | rfl | rfl
    · exact ea BitVec.and_self
    · exact ea BitVec.or_self
    · exact nz (BitVec.and_not_self a)
    · exact nz (BitVec.and_not_self a)
  exact ⟨a0,b0,dif⟩

theorem Trace.section_build {t n ws tr} (h : Trace t n ws tr) (m : W)
    (nz : restrictWord m t ≠ 0) :
    build basicOps (restrictWord m t) (tr.countP fun p => !cheap m p) (projected m ws) := by
  induction h with
  | done =>
    change restrictWord m t ∈ (Finset.image (restrictWord m) {t}).erase 0
    simpa only [Finset.image_singleton, Finset.mem_erase, Finset.mem_singleton, and_true] using nz
  | skip _ ih => exact ih
  | @fuse n ws tail a b z tr ha hb ne hop fresh eq run ih =>
    have sub : projected m tail ⊆ projected m ws := by
      intro p mem
      simp only [projected, Finset.mem_erase, Finset.mem_image] at mem ⊢
      obtain ⟨nonzero,w,hm,eqw⟩ := mem
      exact ⟨nonzero,w,by rw [eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),eqw⟩
    have grow : ∀ {s dst : Finset W} {k : ℕ}, s ⊆ dst →
        build basicOps (restrictWord m t) k s → build basicOps (restrictWord m t) k dst := by
      intro s t' k sub run
      induction k generalizing s t' with
      | zero => exact sub run
      | succ k ih =>
        rcases run with prev | ⟨a,ha,b,hb,ne,z,op,tail⟩
        · exact .inl (ih sub prev)
        · exact .inr ⟨a,sub ha,b,sub hb,ne,z,op,ih (Finset.insert_subset_insert _ sub) tail⟩
    by_cases c : cheap m ⟨a,b,z⟩ = true
    · rw [List.countP_cons_of_neg (by simp [c])]
      apply grow _ ih
      rw [projected_insert]
      split
      · exact sub
      · rename_i notZero
        apply Finset.insert_subset
        · simp only [cheap, Bool.or_eq_true, beq_iff_eq] at c
          rcases c with (h | h) | h
          · exact (notZero h).elim
          · rw [h]; exact projected_mem m ha (h ▸ notZero)
          · rw [h]; exact projected_mem m hb (h ▸ notZero)
        · exact sub
    · have cf : cheap m ⟨a,b,z⟩ = false := by cases e : cheap m ⟨a,b,z⟩ <;> simp_all
      rw [List.countP_cons_of_pos (by simp [cf])]
      simp only [cheap, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at cf
      have hpos := projected_op m hop
      obtain ⟨pa,pb,neproj⟩ := productive_inputs hpos cf.1.1 cf.1.2 cf.2
      rw [projected_insert, if_neg cf.1.1] at ih
      apply Or.inr
      refine ⟨restrictWord m a, projected_mem m ha pa, restrictWord m b, projected_mem m hb pb,
        neproj, restrictWord m z, hpos, grow (Finset.insert_subset_insert _ sub) ih⟩
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

theorem Trace.must_lose {t n ws tr} (h : Trace t n ws tr) (m : W) (nz : restrictWord m t ≠ 0)
    (operand : ∃ w ∈ ws, restrictWord m w = 0) : 0 < tr.countP (cheap m) := by
  induction h with
  | done =>
    obtain ⟨w, hw, hw0⟩ := operand
    obtain rfl : w = t := Finset.mem_singleton.mp hw
    exact (nz hw0).elim
  | skip _ ih => exact ih operand
  | @fuse n ws tail a b z tr ha hb ne hop fresh eq run ih =>
    cases flag : cheap m ⟨a,b,z⟩
    · have hf := flag
      simp only [cheap, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hf
      have hp := projected_op m hop
      obtain ⟨a0,b0,ab⟩ := productive_inputs hp hf.1.1 hf.1.2 hf.2
      obtain ⟨w, hw, hw0⟩ := operand
      rw [eq] at hw
      have hn : w ∈ tail := by
        rcases Finset.mem_insert.mp hw with he | hm
        · exact (a0 (he ▸ hw0)).elim
        · rcases Finset.mem_insert.mp hm with he | hm
          · exact (b0 (he ▸ hw0)).elim
          · exact hm
      have loss := ih ⟨w,Finset.mem_insert_of_mem hn,hw0⟩
      simpa [List.countP_cons, flag] using loss
    · simp [flag]

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

def raw (i : Fin 5) : W := inputs.getD i.val 0

def disposable : List W := List.ofFn raw

private theorem source_check : ∀ a ∈ inputs, ∀ b ∈ inputs, a ≠ b →
    a ∈ disposable ∨ b ∈ disposable := by
  have ok : inputs.all (fun a => inputs.all (fun b =>
    a == b || disposable.contains a || disposable.contains b)) = true := by decide +kernel
  intro a ha b hb ne
  have row := List.all_eq_true.mp (List.all_eq_true.mp ok a ha) b hb
  simpa [ne] using row

private theorem removing_raw_fails {a b z : W} (ha : a ∈ inputs) (hb : b ∈ inputs)
    (ne : a ≠ b) (op : z ∈ basicOps a b) :
    feasibleFor (~~~goal) negatives (z :: inputs.filter (· != a)) = false := by
  have ok : inputs.all (fun a => inputs.all (fun b => a == b ||
    (ops a b).all (fun z => !feasibleFor (~~~goal) negatives (z :: inputs.filter (· != a))))) = true := by
    decide +kernel
  have row := List.all_eq_true.mp (List.all_eq_true.mp ok a ha) b hb
  simp only [beq_eq_false_iff_ne.mpr ne, Bool.false_or] at row
  have no := List.all_eq_true.mp row z (List.mem_toFinset.mp op)
  cases h : feasibleFor (~~~goal) negatives (z :: inputs.filter (· != a)) <;> simp_all

private theorem root_separation {S : Finset W} {k : ℕ} (h : live basicOps (~~~goal) k S)
    {ws : List W} (sub : S ⊆ ws.toFinset) : feasibleFor (~~~goal) negatives ws = true :=
  feasibleFor_from_subset negatives_spec h sub

private theorem retained_first_wire {a b z : W} {s : Finset W} (ha : a ∈ inputs) (hb : b ∈ inputs)
    (ne : a ≠ b) (op : z ∈ basicOps a b) (rawSet : inputs.toFinset = insert a (insert b s))
    (tail : live basicOps (~~~goal) 8 (insert z s)) : a ∈ s := by
  by_contra absent
  have sub : insert z s ⊆ (z :: inputs.filter (· != a)).toFinset := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · simp
    · have hin : r ∈ inputs.toFinset := by
        rw [rawSet]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)
      have ne' : r ≠ a := by rintro rfl; exact absent hr
      simp [ne', List.mem_toFinset.mp hin]
  have h := root_separation tail sub
  exact Bool.noConfusion ((removing_raw_fails ha hb ne op).symm.trans h)

theorem main_search_absent
    (lower : ∀ i : Fin 5, ¬ build basicOps (restrictWord (~~~raw i) (~~~goal)) 7
      (projected (~~~raw i) inputs.toFinset)) {t : W}
    (polarity : t = goal ∨ t = ~~~goal) (candidate : build basicOps t 9 inputs.toFinset) : False := by
  have bits : inputs.all (fun w : W => !w[0]) = true := by decide +kernel
  have normalized := build_preserves_zero (r := (0 : Fin 64)) candidate (by
    intro w mem
    have h := List.all_eq_true.mp bits w (List.mem_toFinset.mp mem)
    cases e : w[0] <;> simp_all)
  have eq : t = ~~~goal := polarity.resolve_left (by intro h; rw [h] at normalized; contradiction)
  subst t
  obtain ⟨s, sub, liveRun⟩ := compress candidate
  let ws := inputs.filter (· ∈ s)
  have bankEq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  have wEq : ws = inputs := by
    have finite : ∀ v ∈ inputs.sublists, feasibleFor (~~~goal) negatives v = true → v = inputs := by
      decide +kernel
    exact finite ws (List.mem_sublists.mpr (List.filter_sublist ..)) (root_separation liveRun bankEq.symm.subset)
  have full : s = inputs.toFinset := bankEq.symm.trans (congrArg List.toFinset wEq)
  rw [full] at liveRun
  obtain ⟨steps, trace⟩ := trace_of_live liveRun
  rcases first_trace (n := 8) trace with impossible | ⟨a,ha,b,hb,ne,z,op,fresh,left,tail,set,history,run⟩
  · exact (by decide : inputs.toFinset ≠ {~~~goal}) impossible.1
  have ha' := List.mem_toFinset.mp ha
  have hb' := List.mem_toFinset.mp hb
  have choose : ∃ i : Fin 5, a = raw i ∨ b = raw i := by
    rcases source_check a ha' b hb' ne with h | h
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      exact ⟨i, Or.inl hi.symm⟩
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      exact ⟨i, Or.inr hi.symm⟩
  obtain ⟨i, which⟩ := choose
  have keepA := retained_first_wire ha' hb' ne op set run.live
  have keepB : b ∈ left := by
    have swapped : inputs.toFinset = insert b (insert a left) := set.trans (Finset.insert_comm ..)
    exact retained_first_wire hb' ha' ne.symm (ops_swap a b ▸ op) swapped run.live
  let m := ~~~raw i
  have projected_not_zero : ∀ i : Fin 5, restrictWord (~~~raw i) (~~~goal) ≠ 0 := by decide +kernel
  have nz := projected_not_zero i
  have raw_zero : restrictWord m (raw i) = 0 := by
    unfold m restrictWord
    exact BitVec.not_and_self (raw i)
  have zeroOperand : ∃ w ∈ insert z left, restrictWord m w = 0 := by
    rcases which with h | h
    · exact ⟨a,Finset.mem_insert_of_mem keepA,h ▸ raw_zero⟩
    · exact ⟨b,Finset.mem_insert_of_mem keepB,h ▸ raw_zero⟩
  have loss := run.must_lose m nz zeroOperand
  have cheapFirst : cheap m ⟨a,b,z⟩ = true := by
    cases h : cheap m ⟨a,b,z⟩
    · simp only [cheap, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      obtain ⟨ha0,hb0,_⟩ := productive_inputs (projected_op m op) h.1.1 h.1.2 h.2
      rcases which with he | he
      · exact (ha0 (he ▸ raw_zero)).elim
      · exact (hb0 (he ▸ raw_zero)).elim
    · rfl
  have short := trace.len
  have total := List.length_eq_countP_add_countP (cheap m) (l := steps)
  have comp : (fun p : Fuse => decide (¬ cheap m p = true)) = (fun p => !cheap m p) := by
    funext p
    cases cheap m p <;> rfl
  rw [comp] at total
  have count : 2 ≤ steps.countP (cheap m) := by rw [history, List.countP_cons_of_pos cheapFirst]; omega
  have budget : steps.countP (fun p => !cheap m p) ≤ 7 := by omega
  exact lower i (extend_build budget (trace.section_build m nz))
-- Reindexing assignments along a graph automorphism preserves every live gate.
def reindex (f : Fin 64 → Fin 64) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun r => w[(f r).val])).cast List.length_ofFn

theorem reindex_bit (f : Fin 64 → Fin 64) (w : W) (r : Fin 64) :
    (reindex f w)[r.val] = w[(f r).val] := by
  change (reindex f w).getLsbD r.val = _
  simp only [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]

theorem reindex_inj (f : Fin 64 → Fin 64) (onto : Function.Surjective f) :
    Function.Injective (reindex f) := by
  intro x y h
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨r, hr⟩ := onto ⟨i, hi⟩
  have eq := congrArg (fun z : W => z[r.val]) h
  simpa only [reindex_bit, hr] using eq

theorem reindex_and (f : Fin 64 → Fin 64) (a b : W) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let r : Fin 64 := ⟨i, hi⟩
  change (reindex f (a &&& b))[r.val] = (reindex f a &&& reindex f b)[r.val]
  simp only [BitVec.getElem_and, reindex_bit]

theorem reindex_or (f : Fin 64 → Fin 64) (a b : W) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let r : Fin 64 := ⟨i, hi⟩
  change (reindex f (a ||| b))[r.val] = (reindex f a ||| reindex f b)[r.val]
  simp only [BitVec.getElem_or, reindex_bit]

theorem reindex_not (f : Fin 64 → Fin 64) (a : W) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let r : Fin 64 := ⟨i, hi⟩
  change (reindex f (~~~a))[r.val] = (~~~reindex f a)[r.val]
  simp only [BitVec.getElem_not, reindex_bit]

theorem reindex_op (f : Fin 64 → Fin 64) {a b z : W} (h : z ∈ basicOps a b) :
    reindex f z ∈ basicOps (reindex f a) (reindex f b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp [reindex_and, reindex_or, reindex_not]

def bowtieGoal : W := 0x5555555454504400
def bowtieRows : List (Fin 64) := [0, 2, 4, 6, 8, 12, 16, 18, 24, 32]
def bowtieInputs : List W := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_0_1 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x4444444444444444 0x5050505050505050 [0x5500550055005500, 0x5555000055550000, 0x5555555500000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_0_2 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x4444444444444444 0x5500550055005500 [0x5050505050505050, 0x5555000055550000, 0x5555555500000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_0_3 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x4444444444444444 0x5555000055550000 [0x5050505050505050, 0x5500550055005500, 0x5555555500000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_0_4 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x4444444444444444 0x5555555500000000 [0x5050505050505050, 0x5500550055005500, 0x5555000055550000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_1_2 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x5050505050505050 0x5500550055005500 [0x4444444444444444, 0x5555000055550000, 0x5555555500000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_1_3 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x5050505050505050 0x5555000055550000 [0x4444444444444444, 0x5500550055005500, 0x5555555500000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_1_4 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x5050505050505050 0x5555555500000000 [0x4444444444444444, 0x5500550055005500, 0x5555000055550000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_2_3 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x5500550055005500 0x5555000055550000 [0x4444444444444444, 0x5050505050505050, 0x5555555500000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_2_4 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x5500550055005500 0x5555555500000000 [0x4444444444444444, 0x5050505050505050, 0x5555000055550000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem bowtie_3_4 : dispatch 3 (optimizedFor bowtieGoal bowtieRows 6)
    0x5555000055550000 0x5555555500000000 [0x4444444444444444, 0x5050505050505050, 0x5500550055005500] = false := by decide +kernel

private theorem bowtie_catalog : pairs bowtieInputs = [(0x4444444444444444, 0x5050505050505050, [0x5500550055005500, 0x5555000055550000, 0x5555555500000000]),
  (0x4444444444444444, 0x5500550055005500, [0x5050505050505050, 0x5555000055550000, 0x5555555500000000]),
  (0x4444444444444444, 0x5555000055550000, [0x5050505050505050, 0x5500550055005500, 0x5555555500000000]),
  (0x4444444444444444, 0x5555555500000000, [0x5050505050505050, 0x5500550055005500, 0x5555000055550000]),
  (0x5050505050505050, 0x5500550055005500, [0x4444444444444444, 0x5555000055550000, 0x5555555500000000]),
  (0x5050505050505050, 0x5555000055550000, [0x4444444444444444, 0x5500550055005500, 0x5555555500000000]),
  (0x5050505050505050, 0x5555555500000000, [0x4444444444444444, 0x5500550055005500, 0x5555000055550000]),
  (0x5500550055005500, 0x5555000055550000, [0x4444444444444444, 0x5050505050505050, 0x5555555500000000]),
  (0x5500550055005500, 0x5555555500000000, [0x4444444444444444, 0x5050505050505050, 0x5555000055550000]),
  (0x5555000055550000, 0x5555555500000000, [0x4444444444444444, 0x5050505050505050, 0x5500550055005500])] := by decide +kernel

private theorem bowtie_all_pairs :
    (pairs bowtieInputs).any (fun (a,b,r) => dispatch 3 (optimizedFor bowtieGoal bowtieRows 6) a b r) = false := by
  apply List.any_eq_false.mpr
  intro choice member
  rw [bowtie_catalog] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro h; exact Bool.noConfusion (bowtie_0_1.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_0_2.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_0_3.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_0_4.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_1_2.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_1_3.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_1_4.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_2_3.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_2_4.symm.trans h)
  · intro h; exact Bool.noConfusion (bowtie_3_4.symm.trans h)

private theorem bowtie_root :
    optimizedFor bowtieGoal bowtieRows 7 3 bowtieInputs = false := by
  change ((bowtieInputs == [bowtieGoal]) ||
    (feasibleFor bowtieGoal bowtieRows bowtieInputs &&
      (pairs bowtieInputs).any (fun (a,b,r) => dispatch 3 (optimizedFor bowtieGoal bowtieRows 6) a b r))) = false
  rw [bowtie_all_pairs]
  decide

set_option maxRecDepth 32768 in
private theorem bowtie_needs_all : ∀ ws ∈ bowtieInputs.sublists,
    feasibleFor bowtieGoal bowtieRows ws = true → ws = bowtieInputs := by decide +kernel

theorem bowtie_bound : ¬ build basicOps bowtieGoal 7 bowtieInputs.toFinset := by
  apply bound_from_local_search (negative := bowtieRows) (by decide) (by decide) bowtie_needs_all
  exact bowtie_root
def cliqueGoal : W := 0x33003200320020
def cliqueRows : List (Fin 64) := [0, 1, 4, 16, 32]
def cliqueInputs : List W := [0x22002200220022, 0x30003000300030, 0x33000000330000, 0x33003300000000]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique_0_1 : dispatch 3 (optimizedFor cliqueGoal cliqueRows 5)
    0x22002200220022 0x30003000300030 [0x33000000330000, 0x33003300000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique_0_2 : dispatch 3 (optimizedFor cliqueGoal cliqueRows 5)
    0x22002200220022 0x33000000330000 [0x30003000300030, 0x33003300000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique_0_3 : dispatch 3 (optimizedFor cliqueGoal cliqueRows 5)
    0x22002200220022 0x33003300000000 [0x30003000300030, 0x33000000330000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique_1_2 : dispatch 3 (optimizedFor cliqueGoal cliqueRows 5)
    0x30003000300030 0x33000000330000 [0x22002200220022, 0x33003300000000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique_1_3 : dispatch 3 (optimizedFor cliqueGoal cliqueRows 5)
    0x30003000300030 0x33003300000000 [0x22002200220022, 0x33000000330000] = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem clique_2_3 : dispatch 3 (optimizedFor cliqueGoal cliqueRows 5)
    0x33000000330000 0x33003300000000 [0x22002200220022, 0x30003000300030] = false := by decide +kernel

private theorem clique_catalog : pairs cliqueInputs = [(0x22002200220022, 0x30003000300030, [0x33000000330000, 0x33003300000000]),
  (0x22002200220022, 0x33000000330000, [0x30003000300030, 0x33003300000000]),
  (0x22002200220022, 0x33003300000000, [0x30003000300030, 0x33000000330000]),
  (0x30003000300030, 0x33000000330000, [0x22002200220022, 0x33003300000000]),
  (0x30003000300030, 0x33003300000000, [0x22002200220022, 0x33000000330000]),
  (0x33000000330000, 0x33003300000000, [0x22002200220022, 0x30003000300030])] := by decide +kernel

private theorem clique_all_pairs :
    (pairs cliqueInputs).any (fun (a,b,r) => dispatch 3 (optimizedFor cliqueGoal cliqueRows 5) a b r) = false := by
  apply List.any_eq_false.mpr
  intro choice member
  rw [clique_catalog] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · intro h; exact Bool.noConfusion (clique_0_1.symm.trans h)
  · intro h; exact Bool.noConfusion (clique_0_2.symm.trans h)
  · intro h; exact Bool.noConfusion (clique_0_3.symm.trans h)
  · intro h; exact Bool.noConfusion (clique_1_2.symm.trans h)
  · intro h; exact Bool.noConfusion (clique_1_3.symm.trans h)
  · intro h; exact Bool.noConfusion (clique_2_3.symm.trans h)

private theorem clique_root :
    optimizedFor cliqueGoal cliqueRows 6 3 cliqueInputs = false := by
  change ((cliqueInputs == [cliqueGoal]) ||
    (feasibleFor cliqueGoal cliqueRows cliqueInputs &&
      (pairs cliqueInputs).any (fun (a,b,r) => dispatch 3 (optimizedFor cliqueGoal cliqueRows 5) a b r))) = false
  rw [clique_all_pairs]
  decide

set_option maxRecDepth 32768 in
private theorem clique_needs_all : ∀ ws ∈ cliqueInputs.sublists,
    feasibleFor cliqueGoal cliqueRows ws = true → ws = cliqueInputs := by decide +kernel

theorem clique_bound : ¬ build basicOps cliqueGoal 6 cliqueInputs.toFinset := by
  apply bound_from_local_search (negative := cliqueRows) (by decide) (by decide) clique_needs_all
  exact clique_root
theorem reindex_build (f : Fin 64 → Fin 64) (onto : Function.Surjective f)
    {t : W} {n : ℕ} {ws : Finset W} (h : build basicOps t n ws) :
    build basicOps (reindex f t) n (ws.image (reindex f)) := by
  have inj := reindex_inj f onto
  induction n generalizing ws with
  | zero => exact Finset.mem_image_of_mem _ h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, ne, z, hop, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨reindex f a, Finset.mem_image_of_mem _ ha,
        reindex f b, Finset.mem_image_of_mem _ hb, fun e => ne (inj e),
        reindex f z, reindex_op f hop, ?_⟩
      simpa only [Finset.image_insert] using ih tail

def rowWith (p : Fin 6 → Fin 6) (r : Fin 64) : Fin 64 :=
  Fin.ofNat 64 (∑ i : Fin 6, if r.val.testBit (p i).val then 2 ^ i.val else 0)

def moveTo0 (i : Fin 5) : Fin 64 → Fin 64 :=
  rowWith (fun j => if j.val = i.val then 0
    else if j.val = 0 then ⟨i.val, by omega⟩ else j)

theorem move_symmetric : ∀ i r, moveTo0 i (moveTo0 i r) = r := by decide +kernel

theorem to_bowtie (i : Fin 5) (lim : i.val = 0 ∨ i.val = 2 ∨ i.val = 4)
    (run : build basicOps (restrictWord (~~~raw i) (~~~goal)) 7 (projected (~~~raw i) inputs.toFinset)) :
    build basicOps bowtieGoal 7 bowtieInputs.toFinset := by
  have surj : Function.Surjective (moveTo0 i) := fun r => ⟨moveTo0 i r, move_symmetric i r⟩
  have mapped := reindex_build (moveTo0 i) surj run
  have h1 : ∀ i : Fin 5, i.val = 0 ∨ i.val = 2 ∨ i.val = 4 →
      reindex (moveTo0 i) (restrictWord (~~~raw i) (~~~goal)) = bowtieGoal := by decide +kernel
  have h2 : ∀ i : Fin 5, i.val = 0 ∨ i.val = 2 ∨ i.val = 4 →
      (projected (~~~raw i) inputs.toFinset).image (reindex (moveTo0 i)) = bowtieInputs.toFinset := by
    decide +kernel
  exact h1 i lim ▸ h2 i lim ▸ mapped

def cliqueMask : W := ~~~(raw 1 ||| raw 3)

def otherLeaf (i : Fin 5) : Fin 5 := if i = 1 then 3 else 1

theorem larger_clique (i : Fin 5) (lim : i.val = 1 ∨ i.val = 3)
    (cliqueLower : ¬ build basicOps cliqueGoal 6 cliqueInputs.toFinset)
    (candidate : build basicOps (restrictWord (~~~raw i) (~~~goal)) 7
      (projected (~~~raw i) inputs.toFinset)) : False := by
  let t := restrictWord (~~~raw i) (~~~goal)
  let q := otherLeaf i
  let u := restrictWord (~~~raw i) (raw q)
  let x : Fin 64 := 32
  let y : Fin 64 := Fin.ofNat 64 (32 + 2^q.val)
  obtain ⟨S, sub, original⟩ := compress candidate
  have pointed : ∀ i : Fin 5, i.val = 1 ∨ i.val = 3 →
    let g := restrictWord (~~~raw i) (~~~goal)
    let q := otherLeaf i
    g[32] ≠ g[(Fin.ofNat 64 (32 + 2^q.val)).val] := by decide +kernel
  have essential : t[x.val] ≠ t[y.val] := pointed i lim
  obtain ⟨w, mem, differs⟩ := live_separates (fun w : W => w[x.val] ≠ w[y.val]) essential
    (ops_differs x y) original
  have one (w : W) (member : w ∈ projected (~~~raw i) inputs.toFinset)
      (differs : w[x.val] ≠ w[y.val]) : w = u := by
    simp only [projected, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at member
    obtain ⟨_, pre, hp, he⟩ := member
    have verify : ∀ i : Fin 5, i.val = 1 ∨ i.val = 3 → inputs.all (fun pre : W =>
      let q := otherLeaf i
      let w := restrictWord (~~~raw i) pre
      (w[32] == w[(Fin.ofNat 64 (32 + 2^q.val)).val]) ||
        (w == restrictWord (~~~raw i) (raw q))) = true := by decide +kernel
    have b := List.all_eq_true.mp (verify i lim) pre hp
    have different : (restrictWord (~~~raw i) pre)[x.val] ≠ (restrictWord (~~~raw i) pre)[y.val] :=
      he ▸ differs
    change ((restrictWord (~~~raw i) pre)[x.val] == (restrictWord (~~~raw i) pre)[y.val] ||
      restrictWord (~~~raw i) pre == u) = true at b
    simp only [beq_eq_false_iff_ne.mpr different, Bool.false_or, beq_iff_eq] at b
    exact he.symm.trans b
  have member : u ∈ S := one w (sub mem) differs ▸ mem
  have hp : ∀ i : Fin 5, i.val = 1 ∨ i.val = 3 →
      restrictWord cliqueMask (restrictWord (~~~raw i) (raw (otherLeaf i))) = 0 := by decide +kernel
  have goal' : ∀ i : Fin 5, i.val = 1 ∨ i.val = 3 →
      restrictWord cliqueMask (restrictWord (~~~raw i) (~~~goal)) = cliqueGoal := by decide +kernel
  have root' : ∀ i : Fin 5, i.val = 1 ∨ i.val = 3 →
      projected cliqueMask (projected (~~~raw i) inputs.toFinset) = cliqueInputs.toFinset := by
    decide +kernel
  have targetEq : restrictWord cliqueMask t = cliqueGoal := goal' i lim
  have targetNotZero : restrictWord cliqueMask t ≠ 0 := targetEq ▸ (by decide : cliqueGoal ≠ 0)
  obtain ⟨steps, trace⟩ := trace_of_live original
  have lost := trace.must_lose cliqueMask targetNotZero ⟨u,member,hp i lim⟩
  have length := trace.len
  have total := List.length_eq_countP_add_countP (cheap cliqueMask) (l := steps)
  have comp : (fun p : Fuse => decide (¬ cheap cliqueMask p = true)) = (fun p => !cheap cliqueMask p) := by
    funext p
    cases cheap cliqueMask p <;> rfl
  rw [comp] at total
  have size : steps.countP (fun p => !cheap cliqueMask p) ≤ 6 := by omega
  have was := extend_build size (trace.section_build cliqueMask targetNotZero)
  have rootSub : projected cliqueMask S ⊆ cliqueInputs.toFinset := by
    rw [← root' i lim]
    intro v mem
    obtain ⟨ne,w,hw,eq⟩ := by simpa only [projected, Finset.mem_erase, Finset.mem_image] using mem
    exact eq ▸ projected_mem cliqueMask (sub hw) (eq.symm ▸ ne)
  have grow {g : W} {S T : Finset W} {k : ℕ} (h : build basicOps g k S) (b : S ⊆ T) :
      build basicOps g k T := by
    induction k generalizing S T with
    | zero => exact b h
    | succ k ih =>
      rcases h with prior | ⟨a,ha,b',hb,ne,z,hop,tail⟩
      · exact Or.inl (ih prior b)
      · exact Or.inr ⟨a,b ha,b',b hb,ne,z,hop,ih tail (Finset.insert_subset_insert _ b)⟩
  exact cliqueLower (targetEq ▸ grow was rootSub)

theorem all_restricted_bounds
    (noBowtie : ¬ build basicOps bowtieGoal 7 bowtieInputs.toFinset)
    (noClique : ¬ build basicOps cliqueGoal 6 cliqueInputs.toFinset)
    (i : Fin 5) (run : build basicOps (restrictWord (~~~raw i) (~~~goal)) 7
      (projected (~~~raw i) inputs.toFinset)) : False := by
  have casesI : ∀ i : Fin 5, (i.val = 0 ∨ i.val = 2 ∨ i.val = 4) ∨ (i.val = 1 ∨ i.val = 3) := by decide
  rcases casesI i with small | more
  · exact noBowtie (to_bowtie i small run)
  · exact larger_clique i more noClique run
-- The section x₅ = false drops a binary gate even when x₅ is first read through a NOT.
set_option maxHeartbeats 0 in
theorem original_binary_lower (reject : ∀ {t : W}, (t = goal ∨ t = ~~~goal) →
      build basicOps t 9 inputs.toFinset → False) (gs : List Gate) (out : ℕ)
    (hg : ∀ g ∈ gs, legal g) (eval : ∀ x, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    11 ≤ binaryCost gs := by
  have computed (b : Bool) (i : Fin 64) :
      (gs.foldl step ((bank b).map (bit i))).getD out false = target (sectionInput b i) := by
    rw [mapped_input]
    exact eval _
  have changed : (gs.foldl (fun w g => w ++ [action w g]) (bank false)).getD out 0 ≠
      (gs.foldl (fun w g => w ++ [action w g]) (bank true)).getD out 0 := by
    intro h
    apply target_switch
    rw [← computed false 1, ← computed true 1,
      word_execution gs out hg (bank false) 1, word_execution gs out hg (bank true) 1, h]
  obtain ⟨t, k, ht, budget, run⟩ := compile_saves gs out hg (bank false) (bank true)
    inputs.toFinset bank_initial bank_holds (fun i => (computed false i).trans (target_false i)) changed
  by_contra! h
  have hk : k ≤ 9 := by omega
  exact reject ht (extend_build hk run)


end PEqualNP.Outside.L_meta_10588.Signed

namespace PEqualNP.Outside.L_meta_10588

open PEqualNP.CircuitLowerBounds

/-- Factor the two pairs of adjacent twins and share the first pair's OR. -/
def upper : List Gate :=
  [⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩,
   ⟨.or, [7, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [7, 6]⟩,
   ⟨.and, [4, 12]⟩, ⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩,
   ⟨.or, [11, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩]

theorem upper_size : upper.length = 12 := rfl

theorem upper_legal : ∀ g ∈ upper,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g mem
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨upper, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10588

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_10588 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_10588 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal _ computes
  by_cases h : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, member, op⟩ := h
    have smaller : Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr
        ⟨g, member, by cases g; simp_all [Signed.isBinary]⟩
    have size := Signed.original_binary_lower (Signed.main_search_absent (Signed.all_restricted_bounds Signed.bowtie_bound Signed.clique_bound)) gates out legal computes
    exact ⟨upper, 18, upper_legal, by rw [upper_size]; omega, upper_eval⟩
  · refine ⟨gates, out, ?_, le_rfl, computes⟩
    intro g mem
    obtain ⟨op, arity⟩ := legal g mem
    refine ⟨?_, arity⟩
    rcases op with op | op | op
    · exact Or.inl op
    · exact Or.inr op
    · exact (h ⟨g, mem, op⟩).elim
