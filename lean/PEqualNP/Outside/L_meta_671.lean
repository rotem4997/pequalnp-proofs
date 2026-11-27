import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_671_aux

-- Live-wire compilation and completeness adapted from Lewis Watson, L-meta-515.
namespace Live

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
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
    (h : live ops goal k s) : s.card ≤ k+1 := by
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

-- Any pair of rows which the output separates must stay separated at each cut.
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

end Live

namespace Live
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Live

namespace Check

abbrev W := BitVec 128
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 64)).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 64) ++ (0 : BitVec 64)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

def advance (k : ℕ) (next : List W → Bool) (a b : W) (rest : List W) : Bool :=
  let ds := ops a b
  let base := cuts rest
  let attempt := fun (kept : List W) (covered : BitVec 64) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0x3b0a9ced8d53332a1f000e6fc7f3313a, 0x496e55ab5666a98c003e718fc663f9cc, 0x9cb97e1e278bc5f11c387e0e0783c1f0, 0xf23f884ff913fe22e03f800ff803fe00, 0xffe4410ffffc8884ffc0000ffffc0000, 0xfffffff904422108fffffff000000000]

def inputs := rawInputs.map canon

end Check
namespace Check
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end Check

namespace Check
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (64+i.val)

theorem neg_differs (i : Fin 64) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 128 := by omega
  have hi : 64+i.val < 128 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 64) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (64+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (64+i.val) := by simpa [differs] using h.2
  have lo : i.val < 128 := by omega
  have hi : 64+i.val < 128 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 64) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬64 + i.val < 64 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check

namespace Check

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem advance_has {k : ℕ} {next : List W → Bool} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hn : kept.length+1 ≤ k+1) (hc : cuts (z::kept) = -1) (ht : next (z::kept) = true) :
    advance k next a b r = true := by
  have hh : (ops a b).any (fun w => (cuts kept ||| sep w == -1) && next (w :: kept)) := by
    apply List.any_eq_true.mpr
    refine ⟨z, by simpa [basicOps] using hz, ?_⟩
    change sep z ||| cuts kept = -1 at hc
    simp [BitVec.or_comm (cuts kept), hc, ht]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [advance, hn, ite_true, cuts, List.foldr_cons] at * <;> simp_all

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem search_complete (n : ℕ) (ws : List W) (hn : ws.Nodup)
    (h : Live.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [search, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          advance k (search k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        apply advance_has hop hk _ (cuts_full hl) (ih _ hnd hl)
        have hc := Live.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check

namespace Check
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 128 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

def negGate (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def binaries : List Gate → Nat
  | [] => 0
  | g :: gs => if negGate g then binaries gs else binaries gs + 1

private theorem not_step (w : List W) (g : Gate) (ng : negGate g = true)
    (av : Finset W) (hw : represents av w) :
    ∃ z, (canon z = 0 ∨ canon z ∈ av) ∧
      ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  cases op <;> try {contradiction}
  cases args with
  | nil =>
    exact ⟨-1, Or.inl (by decide), by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    refine ⟨~~~(w.getD i 0), ?_, ?_⟩
    · rw [canon_neg]
      rcases read_wire w i with h|h
      · rw [h]; left; decide
      · exact hw _ h
    · intro k
      simp only [step, List.map_cons, read_bit]
      simp [GateOp.eval, bit]

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 64) ++ (0 : BitVec 64))) :
    Live.build basicOps goal (binaries gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 64) ++ (0 : BitVec 64)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    by_cases ng : negGate g = true
    · obtain ⟨z,hz,hstep⟩ := not_step w g ng av hw
      rw [binaries, if_pos ng]
      apply ih (fun g' h => hg g' (by simp [h])) (w ++ [z]) av
      · intro u hu
        rcases List.mem_append.mp hu with old|fresh
        · exact hw _ old
        · exact List.mem_singleton.mp fresh ▸ hz
      · intro k; simpa only [List.foldl_cons,hstep] using he k
    rw [binaries, if_neg ng]
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 6 → Bool) : Bool :=
  (!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5)

def assignment (k : Fin 128) (i : Fin 6) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 64) := [4, 6, 0, 1, 2, 3]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (64+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 128) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 128) : graph (assignment k) =
    bit k ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : ((~~~(x 0)) &&& (~~~(x 1)) &&& x 2) ||| (x 0 &&& (~~~(x 1)) &&& x 3) ||| ((~~~(x 0)) &&& x 1 &&& x 4) ||| (x 0 &&& x 1 &&& x 5) =
      ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    Live.build basicOps goal (binaries C.gates) inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live.build basicOps goal k inputs.toFinset) :
    Live.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live.live basicOps goal m inputs.toFinset) :
    Live.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Check
namespace Check

def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩

end Check

namespace Check

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


end Check

namespace Live
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩

def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r)+1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega

theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha|hb|⟨u,w,hA,hB,hw,hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert,hZ,hA,hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert,hA], w, by simp [kept_insert,hB],
                hw, v, hop, build_mono covers next⟩

end Live

namespace Check

abbrev Half := BitVec 64
def fill (m : Half) (r : Fin 64) (x : Half) : Half :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)

def crop (m : Half) (r : Fin 64) (x : W) : W :=
  (fill m r ((x >>> 64).setWidth 64)) ++ (fill m r (x.setWidth 64))

theorem fill_bit (m x : Half) (r : Fin 64) {i : ℕ} (hi : i < 64) :
    (fill m r x)[i] = if m[i] then x[i] else x[r.val] := by
  unfold fill
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr, hm]

def pos (m : Half) (r : Fin 64) (i : Nat) :=
  if i < 64 then (if m.getLsbD i then i else r.val)
  else (if m.getLsbD (i-64) then i else 64+r.val)

theorem pos_lt (m : Half) (r : Fin 64) {i : Nat} (hi : i < 128) : pos m r i < 128 := by
  unfold pos; split <;> split <;> omega

theorem fill_lsb (m x : Half) (r : Fin 64) {i : Nat} (hi : i < 64) :
    (fill m r x).getLsbD i = if m.getLsbD i then x.getLsbD i else x.getLsbD r.val := by
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem r.isLt] using fill_bit m x r hi

theorem crop_bit (m : Half) (r : Fin 64) (x : W) (i : ℕ) (hi : i < 128) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_append]
  by_cases h : i < 64
  · rw [if_pos h, if_pos h, fill_lsb _ _ _ h]
    cases e : m.getLsbD i <;> simp only [BitVec.getLsbD_setWidth, h, r.isLt, decide_true,
      Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · have hr : i-64 < 64 := by omega
    rw [if_neg h, if_neg h, fill_lsb _ _ _ hr]
    cases e : m.getLsbD (i-64) <;> simp only [BitVec.getLsbD_setWidth, hr, r.isLt,
      decide_true, Bool.true_and, Bool.false_eq_true, if_false, if_true, BitVec.getLsbD_ushiftRight,
      show 64+(i-64)=i by omega]

theorem crop_and (m : Half) (r : Fin 64) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

theorem crop_neg (m : Half) (r : Fin 64) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

def cropOpt (m : Half) (r : Fin 64) (x : W) := wrap (crop m r x)

theorem crop_canon (m : Half) (r : Fin 64) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 2500 in
theorem crop_goal (m : Half) (r : Fin 64) : cropOpt m r goal = some goal := by
  have g : goal = (BitVec.allOnes 64 ++ (0 : Half)) := by decide
  have eq : crop m r goal = goal := by
    change (fill m r (BitVec.allOnes 64) ++ fill m r 0) = (BitVec.allOnes 64 ++ (0 : Half))
    congr 1
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp only [BitVec.getElem_allOnes, ite_self]
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp

  rw [cropOpt, eq]
  decide

set_option maxRecDepth 2500 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 128 := by
    rcases sign t with h'|h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr h'
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl|rfl
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by simpa only [wrap, if_neg hn, Option.some.injEq] using h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same|bad
    · exact .inl (by simp only [wrap, if_neg hx, ← hval, same])
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x,canon y,by simp only [wrap,if_neg hx],by simp only [wrap,if_neg hy],eq,
        hval ▸ signed_both (sign x) (sign y)⟩)

theorem mask_projects (m : Half) (r : Fin 64) : Live.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

end Check

namespace Check

def maybeBuild (n : Nat) (av : List W) : Bool :=
  av.sublists.any (fun ws => ws.length ≤ n+1 && cuts ws == -1 &&
    optimized n (n+1-ws.length) ws)

theorem maybeBuild_complete {n : ℕ} {av : List W} (hn : av.Nodup)
    (h : Live.build basicOps goal n av.toFinset) : maybeBuild n av = true := by
  obtain ⟨s,hs,hr⟩ := Live.compress h
  let xs := av.filter (fun a => decide (a ∈ s))
  have hsub : xs.Sublist av := List.filter_sublist
  have hnd : xs.Nodup := hn.sublist hsub
  have heq : xs.toFinset = s := by
    ext a
    simp only [List.mem_toFinset, xs, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hs ha),ha⟩⟩
  rw [←heq] at hr
  have bound := Live.live_card hr
  rw [List.toFinset_card_of_nodup hnd] at bound
  apply List.any_eq_true.mpr
  refine ⟨xs,List.mem_sublists.mpr hsub,?_⟩
  have ok := optimized_complete n xs (n+1-xs.length) hnd (by omega) hr
  simp [bound, cuts_full hr, ok]

def projectedBudget (m : Half) (r : Fin 64) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

def available (m : Half) (r : Fin 64) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

theorem available_spec (m : Half) (r : Fin 64) (ws : List W) :
    (available m r ws).toFinset = Live.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, Live.kept, List.mem_filterMap]

theorem projected_bound (m : Half) (r : Fin 64) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + Live.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega

theorem projection_survives (m : Half) (r : Fin 64) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (h : Live.live basicOps goal k ws.toFinset) :
    maybeBuild (projectedBudget m r k ws) (available m r ws) = true := by
  have hbuild := Live.project_live (crop_goal m r) (mask_projects m r) h _ (projected_bound m r k hn)
  rw [← available_spec] at hbuild
  exact maybeBuild_complete (List.nodup_dedup _) hbuild

end Check

namespace Check

abbrev Claim := Nat × List W
abbrev Hint := Half × Fin 64 × Nat

def goodClaim (c : Claim) : Bool := decide c.2.Nodup && !(maybeBuild c.1 c.2)

def usable (c : Claim) (m : Half) (r : Fin 64) (n : Nat) (ws : List W) : Bool :=
  projectedBudget m r n ws ≤ c.1 &&
  ws.all (fun w => match cropOpt m r w with | none => true | some y => c.2.contains y)

theorem unusable (c : Claim) (m : Half) (r : Fin 64) {n : Nat} {ws : List W}
    (hn : ws.Nodup) (live : Live.live basicOps goal n ws.toFinset) (hc : goodClaim c) :
    usable c m r n ws = false := by
  apply Bool.eq_false_iff.mpr
  intro u
  simp only [goodClaim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  simp only [usable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at u
  have budget := projected_bound m r n hn
  have bound : n ≤ c.1 + Live.zeros (cropOpt m r) ws.toFinset := by omega
  have build := Live.project_live (crop_goal m r) (mask_projects m r) live _ bound
  have sub : Live.kept (cropOpt m r) ws.toFinset ⊆ c.2.toFinset := by
    intro y hy
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hy
    have hy' : cropOpt m r w = some y := by simpa using hv
    have hu := u.2 w (List.mem_toFinset.mp hw)
    simpa [hy'] using hu
  have ok := maybeBuild_complete hc.1 (Live.build_mono sub build)
  exact Bool.noConfusion (hc.2.symm.trans ok)

def key (n : Nat) (ws : List W) : Nat := ws.foldl (fun h w => (65599*h+w.toNat)%1000000007) n

def matched (table : List Claim) (hint : Nat → Option Hint) (n : Nat) (ws : List W) : Bool :=
  match hint (key n ws) with
  | none => false
  | some (m,r,j) => (table[j]?).any (fun c => usable c m r n ws)

theorem matched_false {table : List Claim} (ht : table.all goodClaim = true)
    (hint : Nat → Option Hint) {n : Nat} {ws : List W} (hn : ws.Nodup)
    (h : Live.live basicOps goal n ws.toFinset) : matched table hint n ws = false := by
  unfold matched
  cases hh : hint (key n ws) with
  | none => rfl
  | some data =>
    obtain ⟨m,r,j⟩ := data
    change (table[j]?).any (fun c => usable c m r n ws) = false
    cases he : table[j]? with
    | none => rfl
    | some c =>
      exact unusable c m r hn h (List.all_eq_true.mp ht c (List.mem_of_getElem? he))

def front (table : List Claim) (hint : Nat → Option Hint) : Nat → Nat → Nat → List W → Bool
  | 0, n, extra, ws => !(matched table hint n ws) && optimized n extra ws
  | depth+1, n, extra, ws =>
    !(matched table hint n ws) && (ws == [goal] ||
      (pairs ws).any (fun (a,b,r) => dispatch extra (front table hint depth (n-1)) a b r))

theorem front_complete {table : List Claim} (ht : table.all goodClaim = true) (hint : Nat → Option Hint)
    (depth n : Nat) (ws : List W) (extra : Nat) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live.live basicOps goal n ws.toFinset) :
    front table hint depth n extra ws = true := by
  induction depth generalizing n ws extra with
  | zero => simp [front, matched_false ht hint hn h, optimized_complete n ws extra hn room h]
  | succ depth ih =>
    simp only [front, matched_false ht hint hn h, Bool.not_false, Bool.true_and]
    cases n with
    | zero => simp [singleton_list hn h]
    | succ k =>
      simp only [Nat.add_one_sub_one]
      rcases Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
      · simp [singleton_list hn done]
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go {a b : W} (perm : ws.Perm (a::b::r))
            (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
            dispatch extra (front table hint depth k) a b r = true := by
          obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
          have hl : Live.live basicOps goal k (z::kept).toFinset := by
            simpa [hfin] using tail
          have hc := Live.live_card hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          apply dispatch_complete (k := k) (extra := extra) (front table hint depth k) hop hk (by omega) (by omega) (cuts_full hl)
          apply ih _ _ _ hnd _ hl
          simp; omega
        simp only [Bool.or_eq_true, List.any_eq_true]
        right
        rcases hm with direct | swap
        · exact ⟨(a,b,r), direct, go hp hs hz⟩
        · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def claim0 : Claim := (2, [0x5000000000000000c0000000, 0xffffffffafffffff00000000c0000000])
def claim1 : Claim := (2, [0x1400000000000000300000000000, 0xffffebffffffffff0000300000000000])
def claim2 : Claim := (2, [0x40240000000000000034000000000000, 0xbffbffffffffffff0030000000000000, 0xc024000000000000c000000000000000])
def claim3 : Claim := (2, [0x400000201000000000000030100, 0xc000002010000000c0000000000, 0xfffffbfffffffeff0000000000030000])
def claim4 : Claim := (1, [0x5000000000000000c0000000, 0xffffffffafffffff00000000c0000000])
def claim5 : Claim := (2, [0x10000, 0xfffffffffffeffff0000000000000000])
def claim6 : Claim := (2, [0x80004000080000000000600008, 0x180004000080000018000000000, 0xffffff7ffffffff70000000000600000])
def claim7 : Claim := (2, [0x32000000000000001600000000000000, 0xb200000000000000a000000000000000, 0xddffffffffffffff1400000000000000])
def claim8 : Claim := (2, [0x100000000000000000000, 0xffffffffffffffff0000000000010000])
def claim9 : Claim := (5, [0x3fcafffd8fff33ff0000000fc0033000, 0x402e000b5002a800003e000fc003f800, 0xc03f000b7002ec00003e000fc003f800, 0xe024000ff8008800e000000ff8000000, 0xe03f800900022000e03f800000000000])
def claim10 : Claim := (5, [0x90014a0044001080d00062006e00118, 0x94055a00664018c00007180066001cc, 0xdc0410006ec00840dc0000006ec0000, 0xdc077b0044001080dc077b000000000, 0xf6bfea5ffb9bfef300007000000000c0])
def claim11 : Claim := (5, [0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x84b1621fffffffff0038700000000000, 0xc4e4410000000000e0c0000000000000, 0xf23f884000000000e03f800000000000])
def claim12 : Claim := (5, [0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x84b1621fffffffff0038700000000000, 0xf23f884000000000e03f800000000000, 0xffe4410000000000ffc0000000000000])
def claim13 : Claim := (5, [0x90014a0044001080d00062006e00118, 0x9404100066400840000000006600000, 0x94055a00664018c00007180066001cc, 0xdc077b0044001080dc077b000000000, 0xf6bfea5ffb9bfef300007000000000c0])
def claim14 : Claim := (5, [0x90014a0044001080d00062006e00118, 0x94055a00664018c00007180066001cc, 0xdc0410006ec00840dc0000006ec0000, 0xdc077b0044001080dc077b000000000, 0xf6bfaa5ff99bfe730d00062000800010])
def claim15 : Claim := (1, [0x1400000000000000300000000000, 0xffffebffffffffff0000300000000000])
def claim16 : Claim := (5, [0x828540a060281800038700e0603c1c0, 0x1c20400e078080801c00000e07800000, 0x1c387e08040201001c387e0000000000, 0xe7f7e3f3fafcfedf003870000000c0c0, 0xf7ffebfffbfffeff0038700e0003c0c0])
def claim17 : Claim := (5, [0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0xbf80000fafd800001f00000fc7f00000, 0xf200000ff9100000e000000ff8000000, 0xffc0000904400000ffc0000000000000])
def claim18 : Claim := (5, [0x3b000009044000001f00000000000000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0xbf80000fafd800001f00000fc7f00000, 0xf200000ff9100000e000000ff8000000])
def claim19 : Claim := (5, [0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0xbfbbfeffffffffff1f387e6000000000, 0xfb7fdde000000000e03ff18000000000, 0xffe4410000000000ffc0000000000000])
def claim20 : Claim := (5, [0x90014a0044001080d00062006e00118, 0x94055a0044001080000718000000000, 0x94055a00664018c00007180066001cc, 0xdc0410006ec00840dc0000006ec0000, 0xffbffeffffdbfffb0d00762006e001d8])
def claim21 : Claim := (5, [0x828540a060281800038700e0603c1c0, 0x18285c0e070381a00038700e0603c1c0, 0x1c20400e078080801c00000e07800000, 0x1c387e08040201001c387e0000000000, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim22 : Claim := (5, [0x3200000d891000000000000fc0000000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xffc0000904400000ffc0000000000000])
def claim23 : Claim := (5, [0x3200000d891000000000000fc0000000, 0x3b000009044000001f00000000000000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000])
def claim24 : Claim := (5, [0x3200000d891000000000000fc0000000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x94800004218800001c00000001800000, 0xffc0000904400000ffc0000000000000])
def claim25 : Claim := (5, [0x90014a0044001080d00062006e00118, 0x94055a0044001080000718000000000, 0x94055a00664018c00007180066001cc, 0xdc0410006ec00840dc0000006ec0000, 0xfebffe5fff9bfff30c007600068001d0])
def claim26 : Claim := (5, [0x40440100502408046046818018040a04, 0x414601a15064280c00060181c060380c, 0x63440101d874080463400001d8740000, 0x634681e100402008634681e000000000, 0xbeb9fe5eaf9bd7f36040800018040200])
def claim27 : Claim := (5, [0x90014a0000000001f000e6000000000, 0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x9cb97e1fffffffff1c387e0000000000, 0xc4e4410000000000e0c0000000000000])
def claim28 : Claim := (5, [0x90014a0000000001f000e6000000000, 0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x9cb97e1fffffffff1c387e0000000000, 0xffe4410000000000ffc0000000000000])
def claim29 : Claim := (5, [0x820400a060080800000000e06000000, 0x828540a060281800038700e0603c1c0, 0x1c387e08040201001c387e0000000000, 0xe7f7e3f3fafcfedf003870000000c0c0, 0xf7ffebfffbfffeff0038700e0003c0c0])
def claim30 : Claim := (5, [0x90a14a000000000003e718000000000, 0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x9cb97e1fffffffff1c387e0000000000, 0xf23f884000000000e03f800000000000])
def claim31 : Claim := (5, [0x25224888400000006c221d8c4, 0x272ac888400000000380c0000, 0x48911122200000006c3b11032, 0x6f911de2200000006f801de00, 0xffffffff27cbe5f9000000060381c0f0])
def claim32 : Claim := (5, [0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x94912a1fffffffff1c000e0000000000, 0xc4e4410000000000e0c0000000000000, 0xf23f884000000000e03f800000000000])
def claim33 : Claim := (5, [0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x9cb97e1fffffffff1c387e0000000000, 0xc4e4410000000000e0c0000000000000, 0xfb7fdde000000000e03ff18000000000])
def claim34 : Claim := (5, [0x25224888400000006c2211000, 0x25224888400000006c221d8c4, 0x48911122200000006c3b11032, 0x6f911de2200000006f801de00, 0xffffffff27cbe5f9000000060381c0f0])
def claim35 : Claim := (5, [0x4891000000000000fc7f00000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xf200000ff9100000e000000ff8000000])
def claim36 : Claim := (5, [0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0xddffffff77efffff1c00000fc7e00000, 0xf200000ff9100000e000000ff8000000, 0xffc0000904400000ffc0000000000000])
def claim37 : Claim := (5, [0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xb2000004a9100000e000000038000000, 0xffc0000904400000ffc0000000000000])
def claim38 : Claim := (5, [0x3ffff25227ffff0000000fc6600000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xf200000ff9100000e000000ff8000000])
def claim39 : Claim := (5, [0x3b00000d8d5000001f00000fc7f00000, 0x407ffff25227ffff0000000fc6600000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xf200000ff9100000e000000ff8000000])
def claim40 : Claim := (5, [0x3b000009044000001f00000000000000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0xddffffff77efffff1c00000fc7e00000, 0xf200000ff9100000e000000ff8000000])
def claim41 : Claim := (5, [0x3b000009044000001f00000000000000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xb2000004a9100000e000000038000000])
def claim42 : Claim := (5, [0x820400a060080800000000e06000000, 0x828540a060281800038700e0603c1c0, 0x1038080e0103c0200038000e0003c000, 0x18081c08040201001c000e0000000000, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim43 : Claim := (5, [0xa14a000022108001a308000004040, 0xa14a000022108001a308000037148, 0xa9ce00003332a00000e600003313a, 0x1b884000037622001b800000037600, 0xfffd7f1fffffcdf500183e0000034170])
def claim44 : Claim := (5, [0x4891000000000000fc7f00000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x94800004218800001c00000001800000, 0xf200000ff9100000e000000ff8000000])
def claim45 : Claim := (5, [0x4891000000000000fc7f00000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x9c80000e278800001c00000e07800000, 0xfb7fffffff77ffffe000000ffe600000])
def claim46 : Claim := (5, [0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0xbf80000dadd800001f00000fc7f00000, 0xf200000ff9100000e000000ff8000000, 0xffc0000904400000ffc0000000000000])
def claim47 : Claim := (5, [0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x94800004218800001c00000001800000, 0xb2000004a9100000e000000038000000, 0xffc0000904400000ffc0000000000000])
def claim48 : Claim := (5, [0x40440100502408046046818018040a04, 0x414401015064080400000001c0600000, 0x414601a15064280c00060181c060380c, 0x634681e100402008634681e000000000, 0xfebffe5fff9bfff360068001d8003a00])
def claim49 : Claim := (5, [0x3ffff25227ffff0000000fc6600000, 0x3b00000d8d5000001f00000fc7f00000, 0x497ffffb5667ffff0000000fc6600000, 0x94800004218800001c00000001800000, 0xf200000ff9100000e000000ff8000000])
def claim50 : Claim := (5, [0xa14a000022108001a308000037148, 0xa9ce00003332a00000e600003313a, 0x1b884000037622001b800000037600, 0x1bbef000022108001bbef000000000, 0xfff5631ffffcccd5001a308000004040])
def claim51 : Claim := (5, [0x828540a060281800038700e0603c1c0, 0x18385c0e0703c1a00038700e0603c1c0, 0x1c20400e078080801c00000e07800000, 0x1c387e08040201001c387e0000000000, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim52 : Claim := (5, [0x8285408040201000038700000000000, 0x828540a060281800038700e0603c1c0, 0x1038080e0103c0200038000e0003c000, 0x1c20400e078080801c00000e07800000, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim53 : Claim := (5, [0x90a14a0000000001f000e6000000000, 0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x9cb97e1fffffffff1c387e0000000000, 0xffe4410000000000ffc0000000000000])
def claim54 : Claim := (5, [0x25224888400000006c221d8c4, 0x48911122200000006c2211000, 0x48911122200000006c3b11032, 0x6fbbc888400000006fbbc0000, 0xffffffff27cbe5f9000000060381c0f0])
def claim55 : Claim := (5, [0x820400a060080800000000e06000000, 0x828540a060281800038700e0603c1c0, 0x18385c0e0703c1a00038700e0603c1c0, 0x1c387e08040201001c387e0000000000, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim56 : Claim := (5, [0x3b0a9ce0000000001f000e6000000000, 0x496e55a000000000003e718000000000, 0x9cb97e1fffffffff1c387e0000000000, 0xfb7fdde000000000e03ff18000000000, 0xffe4410000000000ffc0000000000000])
def claim57 : Claim := (5, [0x828540a060281800038700e0603c1c0, 0x1038080e0103c0200038000e0003c000, 0x1c387e08040201001c387e0000000000, 0xe7d7a3f1f8fc7e5f003870000000c0c0, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim58 : Claim := (5, [0x820400a060080800000000e06000000, 0x8285408040201000038700000000000, 0x828540a060281800038700e0603c1c0, 0x1038080e0103c0200038000e0003c000, 0xe7f7e3f3fafcfedf003870000000c0c0])
def claim59 : Claim := (5, [0x40440100502408046040800018040200, 0x40440100502408046046818018040a04, 0x414601a15064280c00060181c060380c, 0x634681e100402008634681e000000000, 0xfebffe5fff9bfff360068001d8003a00])
def claim60 : Claim := (5, [0x3fc0fff48ffd13ff0000000fc0033000, 0x3fcafffd8fff33ff0000000fc0033000, 0x402e000b5002a800003e000fc003f800, 0x8039000e2003c4000038000e0003c000, 0xe024000ff8008800e000000ff8000000])
def claim61 : Claim := (5, [0x90014a0044001080d00062000800010, 0x90014a0044001080d00062006e00118, 0x94055a00664018c00007180066001cc, 0xdc0410006ec00840dc0000006ec0000, 0xfebffe5fff9bfff30c007600068001d0])

def claims : List Claim := [claim0, claim1, claim2, claim3, claim4, claim5, claim6, claim7, claim8, claim9, claim10, claim11, claim12, claim13, claim14, claim15, claim16, claim17, claim18, claim19, claim20, claim21, claim22, claim23, claim24, claim25, claim26, claim27, claim28, claim29, claim30, claim31, claim32, claim33, claim34, claim35, claim36, claim37, claim38, claim39, claim40, claim41, claim42, claim43, claim44, claim45, claim46, claim47, claim48, claim49, claim50, claim51, claim52, claim53, claim54, claim55, claim56, claim57, claim58, claim59, claim60, claim61]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok0 : goodClaim claim0 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok1 : goodClaim claim1 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok2 : goodClaim claim2 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok3 : goodClaim claim3 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok4 : goodClaim claim4 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok5 : goodClaim claim5 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok6 : goodClaim claim6 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok7 : goodClaim claim7 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok8 : goodClaim claim8 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok9 : goodClaim claim9 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok10 : goodClaim claim10 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok11 : goodClaim claim11 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok12 : goodClaim claim12 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok13 : goodClaim claim13 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok14 : goodClaim claim14 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok15 : goodClaim claim15 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok16 : goodClaim claim16 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok17 : goodClaim claim17 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok18 : goodClaim claim18 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok19 : goodClaim claim19 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok20 : goodClaim claim20 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok21 : goodClaim claim21 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok22 : goodClaim claim22 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok23 : goodClaim claim23 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok24 : goodClaim claim24 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok25 : goodClaim claim25 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok26 : goodClaim claim26 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok27 : goodClaim claim27 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok28 : goodClaim claim28 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok29 : goodClaim claim29 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok30 : goodClaim claim30 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok31 : goodClaim claim31 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok32 : goodClaim claim32 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok33 : goodClaim claim33 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok34 : goodClaim claim34 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok35 : goodClaim claim35 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok36 : goodClaim claim36 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok37 : goodClaim claim37 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok38 : goodClaim claim38 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok39 : goodClaim claim39 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok40 : goodClaim claim40 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok41 : goodClaim claim41 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok42 : goodClaim claim42 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok43 : goodClaim claim43 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok44 : goodClaim claim44 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok45 : goodClaim claim45 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok46 : goodClaim claim46 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok47 : goodClaim claim47 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok48 : goodClaim claim48 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok49 : goodClaim claim49 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok50 : goodClaim claim50 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok51 : goodClaim claim51 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok52 : goodClaim claim52 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok53 : goodClaim claim53 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok54 : goodClaim claim54 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok55 : goodClaim claim55 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok56 : goodClaim claim56 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok57 : goodClaim claim57 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok58 : goodClaim claim58 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok59 : goodClaim claim59 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok60 : goodClaim claim60 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok61 : goodClaim claim61 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem allClaims : claims.all goodClaim = true := by
  simp only [claims, List.all_cons, List.all_nil, Bool.true_and, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11,
    ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23,
    ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35,
    ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47,
    ok48, ok49, ok50, ok51, ok52, ok53, ok54, ok55, ok56, ok57, ok58, ok59,
    ok60, ok61]

def hint0 : Option Hint := some (0xd8000000, 27, 0)
def hint1 : Option Hint := some (0x360000000000, 41, 1)
def hint2 : Option Hint := some (0xc035000000000000, 48, 2)
def hint3 : Option Hint := some (0x1800060000c, 2, 6)
def hint4 : Option Hint := some (0xc0000030120, 5, 3)
def hint5 : Option Hint := some (0xd8000000, 27, 4)
def hint6 : Option Hint := some (0x14000, 14, 5)
def hint7 : Option Hint := some (0xb680000000000000, 55, 7)
def hint8 : Option Hint := some (0x14000, 14, 8)
def hint9 : Option Hint := some (0xfffffff000000000, 36, 12)
def hint10 : Option Hint := some (0xe03f800ff803fe00, 9, 9)
def hint11 : Option Hint := some (0xdc077b006ec01dd, 0, 10)
def hint12 : Option Hint := some (0xfffffff000000000, 36, 11)
def hint13 : Option Hint := some (0xdc077b006ec01dd, 0, 13)
def hint14 : Option Hint := some (0xdc077b006ec01dd, 0, 14)
def hint15 : Option Hint := some (0x360000000000, 41, 15)
def hint16 : Option Hint := some (0x1c387e0e0783c1f0, 4, 16)
def hint17 : Option Hint := some (0xffc0000ffffc0000, 18, 17)
def hint18 : Option Hint := some (0xffc0000ffffc0000, 18, 18)
def hint19 : Option Hint := some (0xfffffff000000000, 36, 19)
def hint20 : Option Hint := some (0xdc077b006ec01dd, 0, 20)
def hint21 : Option Hint := some (0xffc0000ffffc0000, 18, 22)
def hint22 : Option Hint := some (0x1c387e0e0783c1f0, 4, 21)
def hint23 : Option Hint := some (0xffc0000ffffc0000, 18, 23)
def hint24 : Option Hint := some (0xffc0000ffffc0000, 18, 24)
def hint25 : Option Hint := some (0xdc077b006ec01dd, 0, 25)
def hint26 : Option Hint := some (0x634681e1d8743a0e, 1, 26)
def hint27 : Option Hint := some (0xfffffff000000000, 36, 27)
def hint28 : Option Hint := some (0xfffffff000000000, 36, 28)
def hint29 : Option Hint := some (0x1c387e0e0783c1f0, 4, 29)
def hint30 : Option Hint := some (0xfffffff000000000, 36, 30)
def hint31 : Option Hint := some (0x6fbbddef7, 0, 31)
def hint32 : Option Hint := some (0xfffffff000000000, 36, 32)
def hint33 : Option Hint := some (0xfffffff000000000, 36, 33)
def hint34 : Option Hint := some (0x6fbbddef7, 0, 34)
def hint35 : Option Hint := some (0xffc0000ffffc0000, 18, 35)
def hint36 : Option Hint := some (0xffc0000ffffc0000, 18, 36)
def hint37 : Option Hint := some (0xffc0000ffffc0000, 18, 37)
def hint38 : Option Hint := some (0xffc0000ffffc0000, 18, 38)
def hint39 : Option Hint := some (0xffc0000ffffc0000, 18, 39)
def hint40 : Option Hint := some (0xffc0000ffffc0000, 18, 40)
def hint41 : Option Hint := some (0xffc0000ffffc0000, 18, 41)
def hint42 : Option Hint := some (0x1c387e0e0783c1f0, 4, 42)
def hint43 : Option Hint := some (0x1bbef00003777b, 0, 43)
def hint44 : Option Hint := some (0xffc0000ffffc0000, 18, 44)
def hint45 : Option Hint := some (0xffc0000ffffc0000, 18, 45)
def hint46 : Option Hint := some (0xffc0000ffffc0000, 18, 46)
def hint47 : Option Hint := some (0xffc0000ffffc0000, 18, 47)
def hint48 : Option Hint := some (0x634681e1d8743a0e, 1, 48)
def hint49 : Option Hint := some (0xffc0000ffffc0000, 18, 49)
def hint50 : Option Hint := some (0x1bbef00003777b, 0, 50)
def hint51 : Option Hint := some (0x1c387e0e0783c1f0, 4, 51)
def hint52 : Option Hint := some (0x1c387e0e0783c1f0, 4, 52)
def hint53 : Option Hint := some (0xfffffff000000000, 36, 53)
def hint54 : Option Hint := some (0x6fbbddef7, 0, 54)
def hint55 : Option Hint := some (0x1c387e0e0783c1f0, 4, 55)
def hint56 : Option Hint := some (0xfffffff000000000, 36, 56)
def hint57 : Option Hint := some (0x1c387e0e0783c1f0, 4, 57)
def hint58 : Option Hint := some (0x1c387e0e0783c1f0, 4, 58)
def hint59 : Option Hint := some (0x634681e1d8743a0e, 1, 59)
def hint60 : Option Hint := some (0xe03f800ff803fe00, 9, 60)
def hint61 : Option Hint := some (0xdc077b006ec01dd, 0, 61)

-- The lookup table selects a suggested restriction. The usable predicate checks its validity.
def saltAtChunkBlock0 (i : Nat) : Nat :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x3100000010a0020202001120 else 0x2001010000000000000000000) else (if i < 3 then 0x11000000000010000000000110001020 else 0x14000000000000000000301100011000)) else (if i < 6 then (if i < 5 then 0x3000000000000000010001000000000 else 0x21100000100000010000001100001200) else (if i < 7 then 0x100010201000000000100010000 else 0x10000000000001000001000))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x611020000200003005000100001 else 0x10000010100001010000020001000001) else (if i < 11 then 0x1300100000100010000002100110010 else 0x100000000001002003000000000011)) else (if i < 14 then (if i < 13 then 0x10000001110002000031100000200 else 0x10110000800000000100002002001040) else (if i < 15 then 0x10000400010000000000222101000010 else 0x21210211000000150400500))))
def saltAtChunkBlock1 (i : Nat) : Nat :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x2001000002212000014001024000 else 0x1020000001000000000000210020210) else (if i < 19 then 0x2000021200000086100000004010 else 0x100010011010000010010100020012)) else (if i < 22 then (if i < 21 then 0x1224100010000110000001010000112 else 0x1303030011000002030000100001200) else (if i < 23 then 0x10001202100000122401010010000000 else 0x1020101200300000022010300100000))) else (if i < 28 then (if i < 26 then (if i < 25 then 0xa000100000000000010100000041 else 0x100001020200011003000000041000) else (if i < 27 then 0x10000000220020200100300a0000302 else 0x1000030000000211000001030002100)) else (if i < 30 then (if i < 29 then 0x1300000300000000201310000016000 else 0x100001000001000021414000205300) else (if i < 31 then 0x1012020010100100300220000000022 else 0x10210031003331110304010511110))))
def saltAtChunk (i : Nat) : Nat :=
  match i / 16 with
  | 0 => saltAtChunkBlock0 i
  | 1 => saltAtChunkBlock1 i
  | _ => 0

def saltAt (i : Nat) : Nat :=
  ((saltAtChunk (i / 32)) >>> ((i % 32) * 4)) % 16

def slotAtChunkBlock0 (i : Nat) : Nat :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x7400008821080000000000000400100050c4000000003 else 0x8000004021b000003008005100000105044000080) else (if i < 3 then 0x31010000000010000001440c100000000e0080c104200f else 0x831000801799c00000000000040000c00c320200011d0c4)) else (if i < 6 then (if i < 5 then 0x1000000000c50000000c0004002140080004404003002000 else 0x200003a0000030030000001030050dd140040003005003) else (if i < 7 then 0x1400000007c01020c8003000c44148140 else 0x400880000000000481020061050807a10c3003144740))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x4021000000000c5080000103206012008536044110141100 else 0xa50270008010080800004c41080040031840c00080c5000) else (if i < 11 then 0x3980045000000105000143580003080000102180000000 else 0x4802400000000811d0001000c30800441240c0000004004)) else (if i < 14 then (if i < 13 then 0x2020000000000001000001030000c0001100027202084000 else 0x2059c0200000000040043000000000100000140100000000) else (if i < 15 then 0x70000c0105140000044003003000016000040000012 else 0x1010800c00030430050030001000c00050c3004000000000))))
def slotAtChunkBlock1 (i : Nat) : Nat :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x21080002000002010400000000000020050000c8281003 else 0x442000080027000003026000002000100005000000005003) else (if i < 19 then 0x2204208044000000000002004101000000000100000100 else 0x1400801400b91000080c00009020c5105008942001002000)) else (if i < 22 then (if i < 21 then 0x400000880400c40000002404040c3000000000200008 else 0x102000103004080010000082140001000003002000b04) else (if i < 23 then 0x1020410420911810c00000000041040c00800000ca103 else 0xa49c01401000c0000004080200003f40003000000105003))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x1440400020080030009c0000000000005080000004027083 else 0x140000141005000006105000001000000000300002003200) else (if i < 27 then 0x451010c0000000000000000c841450c0000280732140 else 0xc0011000101008011184000102405150000000404102010)) else (if i < 30 then (if i < 29 then 0x801610300014002600000400390000028004000e0c5 else 0x902004080100002980203105102001044000100008981) else (if i < 31 then 0x261000000000000f4000000003101040143080024100000 else 0x44482050000000400040c40c30040000000c0000010003))))
def slotAtChunkBlock2 (i : Nat) : Nat :=
  (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x1012040800000101030800000c00c000866d140001000003 else 0x80c50420050050430004400c0000100200001) else (if i < 35 then 0xc15840c00040c10000840e6102000080000103108025000 else 0x41440840ea0c0000140000000000040100008000080008)) else (if i < 38 then (if i < 37 then 0x8020010470001a0000851021040000040001010460c3080 else 0x8001a000143004000003003000000000000000006140143) else (if i < 39 then 0x10514214408414100300000a025012105100004010200000 else 0x80000000080000000000200040000000008000003))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x400020510508000c0000050000049c4088000003002000 else 0x2002011050820040000000001440b10001430c0000003000) else (if i < 43 then 0x40c20002000000120040000000000000000c2110140 else 0xc20000000000000c00000c4083000000000003000)) else (if i < 46 then (if i < 45 then 0x440c000008010066f0830010c0000d40000000003000100 else 0x108040985680000140005044004004a01148000080) else (if i < 47 then 0x144101a8000500000000000298020010520502b000004100 else 0x1400c000010320000044000410400000813c000342011080))))
def slotAtChunkBlock3 (i : Nat) : Nat :=
  (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x50000d21050c000000400000000097b045003003024100 else 0xc00001001030250c4082003000000100003000000) else (if i < 51 then 0x9000050000250000081457440c0004140200000140400 else 0x40000800c40656a69650c4204002005024980121000100)) else (if i < 54 then (if i < 53 then 0x30000c00000051010001830c0b80026100000000000004 else 0x7b100000000004080100002086000085940003000034004) else (if i < 55 then 0x100100088000009140000a40000002e04080000004088000 else 0x4010010000058200000000308358511a2030000f80000d0))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x2000c00000000040001410c3184908400000000116743104 else 0x10300800504d0c40c00c51020031500000800c0000000024) else (if i < 59 then 0x200a650000c0200000105002004144003004000143000000 else 0xc00050c00000041010c3004000002004000000002100)) else (if i < 62 then (if i < 61 then 0x830c0082108000000140148402000000080084024080000 else 0x1030c0143944026000004000000000065580024080d40024) else (if i < 63 then 0xcc40000000410040c00000000000000c0102100100002 else 0x800000400000040000040000000000c40000c04c0000005))))
def slotAtChunkBlock4 (i : Nat) : Nat :=
  (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x44145103005000c400268c30000010040c4c6b082000 else 0x100003000080000003000140000102002540000004080080) else (if i < 67 then 0x800030001800000009c310b0420000809c0943143004000 else 0x30c40c0008145100000000000144004000140100005)) else (if i < 70 then (if i < 69 then 0xdd1400020030c00080420960c20c21430c00009c00c4000 else 0x50050c00041801010010040c8105203000100140004100) else (if i < 71 then 0x1800c00000000c21040080000010000040a70c0140000 else 0x401441040c19c60390420040806800050c5083100040000))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x8000000083402003004100080004001004000000 else 0x200100040104082000000000002200005040000000000002) else (if i < 75 then 0x40080000d040c01060c210000002408001dc02008144 else 0x4020000000000000200940004683202000003203b79)) else (if i < 78 then (if i < 77 then 0xc402082840441401439c30020009c0000000100000000000 else 0xc02201000000000030000000c02000002000000000c2083) else (if i < 79 then 0x1841481000000c0000140008003191004000002004100000 else 0x26000000140485000000000000000000008044090154084))))
def slotAtChunkBlock5 (i : Nat) : Nat :=
  (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x20030c00001041400007800000f9000000108 else 0x800881440c00440080040c3000003040108b810c1003100) else (if i < 83 then 0x9c00840033000100c4144000000000000000004100000003 else 0xc01800100000004841480030c46800c40080c0002000)) else (if i < 86 then (if i < 85 then 0x50086800001010124850810040030000800841030d0022 else 0x980d462800c0000100000104000140000140042145200002) else (if i < 87 then 0x1000c1001003100045000003000000000000000985000180 else 0x3104000082004000004940203000080003040100005))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x1000c21000001000c29c41c3080108082044000000006000 else 0x2824400000011400040002020000030040052040446800e4) else (if i < 91 then 0x852011420040000000000040059800000030004005c30c4 else 0x304000000185204000002044100680001200000003000)) else (if i < 94 then (if i < 93 then 0x1050000000001000040000c0010000003000000084100003 else 0x1441020655801400009400400480000406000020dd0c4000) else (if i < 95 then 0x40001002000000000241436844010c8081484081000002 else 0x8170001000000202200001100680003103200108003600))))
def slotAtChunkBlock6 (i : Nat) : Nat :=
  (if i < 98 then (if i < 97 then 0x3104002dc00000801000000000c0042003148983044 else 0x8000d030002000030000000000010c0004000004001142) else (if i < 99 then 0x8454303e1480c00050000000050000800c4000000 else 0x16104680040200804200))
def slotAtChunk (i : Nat) : Nat :=
  match i / 16 with
  | 0 => slotAtChunkBlock0 i
  | 1 => slotAtChunkBlock1 i
  | 2 => slotAtChunkBlock2 i
  | 3 => slotAtChunkBlock3 i
  | 4 => slotAtChunkBlock4 i
  | 5 => slotAtChunkBlock5 i
  | 6 => slotAtChunkBlock6 i
  | _ => 0

def slotAt (i : Nat) : Nat :=
  ((slotAtChunk (i / 32)) >>> ((i % 32) * 6)) % 64

def hintAtBlock0 (i : Nat) : Option Hint :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then none else hint0) else (if i < 3 then hint1 else hint2)) else (if i < 6 then (if i < 5 then hint3 else hint4) else (if i < 7 then hint5 else hint6))) else (if i < 12 then (if i < 10 then (if i < 9 then hint7 else hint8) else (if i < 11 then hint9 else hint10)) else (if i < 14 then (if i < 13 then hint11 else hint12) else (if i < 15 then hint13 else hint14))))
def hintAtBlock1 (i : Nat) : Option Hint :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then hint15 else hint16) else (if i < 19 then hint17 else hint18)) else (if i < 22 then (if i < 21 then hint19 else hint20) else (if i < 23 then hint21 else hint22))) else (if i < 28 then (if i < 26 then (if i < 25 then hint23 else hint24) else (if i < 27 then hint25 else hint26)) else (if i < 30 then (if i < 29 then hint27 else hint28) else (if i < 31 then hint29 else hint30))))
def hintAtBlock2 (i : Nat) : Option Hint :=
  (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then hint31 else hint32) else (if i < 35 then hint33 else hint34)) else (if i < 38 then (if i < 37 then hint35 else hint36) else (if i < 39 then hint37 else hint38))) else (if i < 44 then (if i < 42 then (if i < 41 then hint39 else hint40) else (if i < 43 then hint41 else hint42)) else (if i < 46 then (if i < 45 then hint43 else hint44) else (if i < 47 then hint45 else hint46))))
def hintAtBlock3 (i : Nat) : Option Hint :=
  (if i < 55 then (if i < 51 then (if i < 49 then hint47 else (if i < 50 then hint48 else hint49)) else (if i < 53 then (if i < 52 then hint50 else hint51) else (if i < 54 then hint52 else hint53))) else (if i < 59 then (if i < 57 then (if i < 56 then hint54 else hint55) else (if i < 58 then hint56 else hint57)) else (if i < 61 then (if i < 60 then hint58 else hint59) else (if i < 62 then hint60 else hint61))))
def hintAt (i : Nat) : Option Hint :=
  match i / 16 with
  | 0 => hintAtBlock0 i
  | 1 => hintAtBlock1 i
  | 2 => hintAtBlock2 i
  | 3 => hintAtBlock3 i
  | _ => none

def advice (k : Nat) : Option Hint :=
  hintAt (slotAt ((k / 1024 + saltAt (k % 1024)) % 3181))

def firstPair (i : Nat) : Bool :=
  ((pairs inputs)[i]?).any (fun (a,b,r) => dispatch 3 (front claims advice 1 7) a b r)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair0 : firstPair 0 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair1 : firstPair 1 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair2 : firstPair 2 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair3 : firstPair 3 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair4 : firstPair 4 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair5 : firstPair 5 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair6 : firstPair 6 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair7 : firstPair 7 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair8 : firstPair 8 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair9 : firstPair 9 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair10 : firstPair 10 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair11 : firstPair 11 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair12 : firstPair 12 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair13 : firstPair 13 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair14 : firstPair 14 = false := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem checked : front claims advice 2 8 3 inputs = false := by
  have hlen : (pairs inputs).length = 15 := by decide
  have each : ∀ i : Fin 15, firstPair i.val = false := by
    intro i
    fin_cases i
    · exact pair0
    · exact pair1
    · exact pair2
    · exact pair3
    · exact pair4
    · exact pair5
    · exact pair6
    · exact pair7
    · exact pair8
    · exact pair9
    · exact pair10
    · exact pair11
    · exact pair12
    · exact pair13
    · exact pair14
  apply Bool.eq_false_iff.mpr
  intro yes
  change (!(matched claims advice 8 inputs) && ((inputs == [goal]) ||
    (pairs inputs).any (fun (a,b,r) => dispatch 3 (front claims advice 1 7) a b r))) = true at yes
  simp only [Bool.and_eq_true, Bool.or_eq_true] at yes
  rcases yes.2 with stop | step
  · exact (by decide : (inputs == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := each (Fin.cast hlen i)
    simp only [Fin.val_cast, firstPair, List.getElem?_eq_getElem i.isLt, Option.any_some] at no
    rw [← hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)


theorem binary_lower (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hg : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) : 9 ≤ binaries C.gates := by
  by_contra! hs
  have hh := front_complete allClaims advice 2 8 inputs 3 (by decide) (by decide)
    (extend_live (by omega : binaries C.gates ≤ 8) (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (checked.symm.trans hh)

end Check
namespace Check

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ordered (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i : Fin u.length, u.getD i.val false = true → v.getD i.val false = true

lemma getOrdered {u v : List Bool} (h : ordered u v) (i : Nat) :
    u.getD i false = true → v.getD i false = true := by
  by_cases hi : i < u.length
  · exact h.2 ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by omega : u.length ≤ i)]
    simp

lemma appendOrdered {u v : List Bool} {a b : Bool} (h : ordered u v) (hab : a = true → b = true) :
    ordered (u ++ [a]) (v ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i.val < u.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact getOrdered h _
  · have len := i.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at len
    have e : i.val = u.length := by omega
    rw [e]
    simpa [h.1] using hab

lemma stepOrdered {u v : List Bool} (h : ordered u v) (g : Gate) (ok : legal g) (hn : negGate g = false) :
    ordered (step u g) (step v g) := by
  apply appendOrdered h
  obtain ⟨op, args⟩ := g
  have ops := ok.1
  change op = .and ∨ op = .or ∨ op = .not at ops
  rcases ops with rfl | rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.forall_mem_map, id_eq]
    intro hall i hi
    exact getOrdered h i (hall i hi)
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨v₀,hm,hv⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    exact ⟨_, List.mem_map_of_mem hi, getOrdered h i hv⟩
  · contradiction

lemma negOrdered {u v w z : List Bool} (hu : ordered u v) (hv : ordered v w)
    (hw : ordered w z) (g : Gate) (hn : negGate g = true) :
    ordered (step u g) (step v g) ∨ ordered (step w g) (step z g) := by
  obtain ⟨op, args⟩ := g
  cases op <;> try contradiction
  cases args with
  | nil => left; exact appendOrdered hu (fun h => h)
  | cons i tail =>
    by_cases hit : v.getD i false = true
    · right
      have h₁ := getOrdered hv i hit
      have h₂ := getOrdered hw i h₁
      apply appendOrdered hw
      simp only [GateOp.eval, List.map_cons, List.headD_cons, h₁, h₂]
      exact fun h => h
    · left
      have h₁ : u.getD i false = false := Bool.eq_false_iff.mpr (fun hh => hit (getOrdered hu i hh))
      have h₂ := Bool.eq_false_iff.mpr hit
      apply appendOrdered hu
      simp only [GateOp.eval, List.map_cons, List.headD_cons, h₁, h₂]
      exact fun h => h

lemma binaries_le : ∀ gs : List Gate, binaries gs ≤ gs.length
  | [] => by decide
  | g :: gs => by
      have h := binaries_le gs
      cases hn : negGate g <;> simp [binaries, hn] <;> omega

lemma oneFall (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (u v : List Bool)
    (h : ordered u v) (fall : ¬ ordered (gs.foldl step u) (gs.foldl step v)) :
    binaries gs + 1 ≤ gs.length := by
  induction gs generalizing u v with
  | nil => exact False.elim (fall h)
  | cons g gs ih =>
    have ht : ∀ g' ∈ gs, legal g' := fun g' hm => hg g' (List.mem_cons_of_mem _ hm)
    cases hn : negGate g with
    | false =>
      have hh := ih ht _ _ (stepOrdered h g (hg g List.mem_cons_self) hn) fall
      simp [binaries, hn]; omega
    | true => simpa [binaries, hn] using binaries_le gs

lemma twoFalls (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (u v w z : List Bool)
    (h₁ : ordered u v) (h₂ : ordered v w) (h₃ : ordered w z)
    (f₁ : ¬ ordered (gs.foldl step u) (gs.foldl step v))
    (f₂ : ¬ ordered (gs.foldl step w) (gs.foldl step z)) :
    binaries gs + 2 ≤ gs.length := by
  induction gs generalizing u v w z with
  | nil => exact False.elim (f₁ h₁)
  | cons g gs ih =>
    have ht : ∀ g' ∈ gs, legal g' := fun g' hm => hg g' (List.mem_cons_of_mem _ hm)
    have hg' := hg g List.mem_cons_self
    cases hn : negGate g with
    | false =>
      have hh := ih ht _ _ _ _ (stepOrdered h₁ g hg' hn) (stepOrdered h₂ g hg' hn)
        (stepOrdered h₃ g hg' hn) f₁ f₂
      simp [binaries, hn]; omega
    | true =>
      rcases negOrdered h₁ h₂ h₃ g hn with h|h
      · have hh := oneFall gs ht _ _ h f₁
        simp [binaries, hn]; omega
      · have hh := oneFall gs ht _ _ h f₂
        simp [binaries, hn]; omega

def row (v : Nat) (i : Fin 6) : Bool := v.testBit i.val

lemma mux_falls (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    binaries C.gates + 2 ≤ C.gates.length := by
  let w (v : Nat) := List.ofFn (row v)
  have fall (v z : Nat) (hv : graph (row v) = true) (hz : graph (row z) = false) :
      ¬ ordered (C.gates.foldl step (w v)) (C.gates.foldl step (w z)) := by
    intro h
    have h' := getOrdered h C.output
    change (C.eval (List.ofFn (row v)) = true → C.eval (List.ofFn (row z)) = true) at h'
    rw [he, he, hv, hz] at h'
    exact Bool.noConfusion (h' rfl)
  apply twoFalls C.gates hg (w 4) (w 5) (w 13) (w 15)
  · unfold ordered; decide
  · unfold ordered; decide
  · unfold ordered; decide
  · exact fall 4 5 (by decide) (by decide)
  · exact fall 13 15 (by decide) (by decide)

end Check
namespace Check

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def eleven : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩,
    ⟨.and, [6, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [8, 9]⟩,
    ⟨.and, [6, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [11, 12]⟩,
    ⟨.and, [7, 10]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem upper : HasCircuitSize 6 graph 11 := by
  refine ⟨eleven, ?_, by decide, ?_⟩
  · intro g hg
    simp only [eleven, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl), by decide⟩
  · intro x
    rw [show List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] from rfl]
    unfold graph
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide

end Check

end PEqualNP.Outside.L_meta_671_aux

theorem PEqualNP.Outside.L_meta_671 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5)) 11 ∧ ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (!(x 0) && !(x 1) && x 2) || (x 0 && !(x 1) && x 3) || (!(x 0) && x 1 && x 4) || (x 0 && x 1 && x 5)) 10 := by
  refine ⟨PEqualNP.Outside.L_meta_671_aux.Check.upper, ?_⟩
  rintro ⟨C,hg,hsize,he⟩
  have h₁ := PEqualNP.Outside.L_meta_671_aux.Check.binary_lower C hg he
  have h₂ := PEqualNP.Outside.L_meta_671_aux.Check.mux_falls C hg he
  change C.gates.length ≤ 10 at hsize
  omega
