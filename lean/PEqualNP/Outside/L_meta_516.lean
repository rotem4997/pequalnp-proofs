import Mathlib
import PEqualNP.Defs

-- Adapted from Lewis Watson’s checked circuit analyses for L-meta-515 and L-meta-528.

namespace Live516

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

end Live516

namespace Live516
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

end Live516

namespace Check516

abbrev W := BitVec 320
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 160)).setWidth 160
def cuts (ws : List W) : BitVec 160 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 160) ++ (0 : BitVec 160)))
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
  let attempt := fun (kept : List W) (covered : BitVec 160) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0x8400812124e19391e000c983e0ff8124780ff4cf8400812124608190e000408000458124380454c5,
   0x24120007326c1e7921364d532c12079f32c8fc002412000000240229201245512c12008b12c85c,
   0x18381c0639cc70e781c638719c301c39e1c30f0f18381c060984702701c2385194301c09c143090a,
   0xe0c0e0383e0f80f80607c07e1fc0e03e01fc0ff0e0c0e038360b80d80605c02a0ac0e03600ac06a0,
   0xff003fc00fff0007f8007fe000ffc001fff00000ff000a400f7e000368007fe000364001fba000,
   0xff00003ffff0000007ffff800000fffffe000000ff000035bff000000497ed800000c9bf74000000,
   0xffffffc00000000007ffffffffff000000000000296d36400000000007ffbf7fffba000000000000,
   0xfffffffffffffffff80000000000000000000000d692c9bfffffdbfdd00000000000000000000000]

def inputs := rawInputs.map canon

end Check516
namespace Check516
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
end Check516

namespace Check516
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 160) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (160+i.val)

theorem neg_differs (i : Fin 160) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 320 := by omega
  have hi : 160+i.val < 320 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 160) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 160) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (160+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (160+i.val) := by simpa [differs] using h.2
  have lo : i.val < 320 := by omega
  have hi : 160+i.val < 320 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 160) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬160 + i.val < 160 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 160) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live516.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live516.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 160)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check516

namespace Check516

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
    (h : Live516.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
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
        have hl : Live516.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        apply advance_has hop hk _ (cuts_full hl) (ih _ hnd hl)
        have hc := Live516.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check516

namespace Check516
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 320) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 320) :
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
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 320 := by
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

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 160) ++ (0 : BitVec 160))) :
    Live516.build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 160) ++ (0 : BitVec 160)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
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


def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)

def assignment (k : Fin 320) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live516.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 160) := [1, 5, 0, 4, 12, 25, 48, 91]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (160+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live516.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 320) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 320) : graph (assignment k) =
    bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 1) ||| (x 0 &&& x 4) ||| (x 4 &&& x 5) ||| (x 5 &&& x 1) ||| (x 0 &&& x 6) ||| (x 6 &&& x 7) ||| (x 7 &&& x 1) =
      ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 320) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    Live516.build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live516.build basicOps goal k inputs.toFinset) :
    Live516.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live516.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live516.live basicOps goal m inputs.toFinset) :
    Live516.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem lower_of_check (check : search 11 inputs = false) (s : ℕ)
    (h : HasCircuitSize 8 graph s) : 12 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 11 := by change C.gates.length ≤ s at hsize; omega
  have searched := search_complete 11 inputs (by decide) (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check516
namespace Check516

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

end Check516

namespace Check516

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live516.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
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
        have hl : Live516.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live516.live_card hl
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

theorem lower_of_optimized (check : optimized 11 4 inputs = false) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : 12 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 11 := by change C.gates.length ≤ s at hsize; omega
  have searched := optimized_complete 11 inputs 4 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check516

namespace Live516
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

end Live516

namespace Check516

abbrev Half := BitVec 160
def fill (m : Half) (r : Fin 160) (x : Half) : Half :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)

def crop (m : Half) (r : Fin 160) (x : W) : W :=
  (fill m r ((x >>> 160).setWidth 160)) ++ (fill m r (x.setWidth 160))

theorem fill_bit (m x : Half) (r : Fin 160) {i : ℕ} (hi : i < 160) :
    (fill m r x)[i] = if m[i] then x[i] else x[r.val] := by
  unfold fill
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr, hm]

def pos (m : Half) (r : Fin 160) (i : Nat) :=
  if i < 160 then (if m.getLsbD i then i else r.val)
  else (if m.getLsbD (i-160) then i else 160+r.val)

theorem pos_lt (m : Half) (r : Fin 160) {i : Nat} (hi : i < 320) : pos m r i < 320 := by
  unfold pos; split <;> split <;> omega

theorem fill_lsb (m x : Half) (r : Fin 160) {i : Nat} (hi : i < 160) :
    (fill m r x).getLsbD i = if m.getLsbD i then x.getLsbD i else x.getLsbD r.val := by
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem r.isLt] using fill_bit m x r hi

theorem crop_bit (m : Half) (r : Fin 160) (x : W) (i : ℕ) (hi : i < 320) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_append]
  by_cases h : i < 160
  · rw [if_pos h, if_pos h, fill_lsb _ _ _ h]
    cases e : m.getLsbD i <;> simp only [BitVec.getLsbD_setWidth, h, r.isLt, decide_true,
      Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · have hr : i-160 < 160 := by omega
    rw [if_neg h, if_neg h, fill_lsb _ _ _ hr]
    cases e : m.getLsbD (i-160) <;> simp only [BitVec.getLsbD_setWidth, hr, r.isLt,
      decide_true, Bool.true_and, Bool.false_eq_true, if_false, if_true, BitVec.getLsbD_ushiftRight,
      show 160+(i-160)=i by omega]

theorem crop_and (m : Half) (r : Fin 160) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

theorem crop_neg (m : Half) (r : Fin 160) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

def cropOpt (m : Half) (r : Fin 160) (x : W) := wrap (crop m r x)

theorem crop_canon (m : Half) (r : Fin 160) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 2500 in
theorem crop_goal (m : Half) (r : Fin 160) : cropOpt m r goal = some goal := by
  have g : goal = (BitVec.allOnes 160 ++ (0 : Half)) := by decide
  have eq : crop m r goal = goal := by
    change (fill m r (BitVec.allOnes 160) ++ fill m r 0) = (BitVec.allOnes 160 ++ (0 : Half))
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
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 320 := by
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

theorem mask_projects (m : Half) (r : Fin 160) : Live516.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

end Check516

namespace Check516

def maybeBuild (n : Nat) (av : List W) : Bool :=
  av.sublists.any (fun ws => ws.length ≤ n+1 && cuts ws == -1 &&
    optimized n (n+1-ws.length) ws)

theorem maybeBuild_complete {n : ℕ} {av : List W} (hn : av.Nodup)
    (h : Live516.build basicOps goal n av.toFinset) : maybeBuild n av = true := by
  obtain ⟨s,hs,hr⟩ := Live516.compress h
  let xs := av.filter (fun a => decide (a ∈ s))
  have hsub : xs.Sublist av := List.filter_sublist
  have hnd : xs.Nodup := hn.sublist hsub
  have heq : xs.toFinset = s := by
    ext a
    simp only [List.mem_toFinset, xs, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hs ha),ha⟩⟩
  rw [←heq] at hr
  have bound := Live516.live_card hr
  rw [List.toFinset_card_of_nodup hnd] at bound
  apply List.any_eq_true.mpr
  refine ⟨xs,List.mem_sublists.mpr hsub,?_⟩
  have ok := optimized_complete n xs (n+1-xs.length) hnd (by omega) hr
  simp [bound, cuts_full hr, ok]

def projectedBudget (m : Half) (r : Fin 160) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

def available (m : Half) (r : Fin 160) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

theorem available_spec (m : Half) (r : Fin 160) (ws : List W) :
    (available m r ws).toFinset = Live516.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, Live516.kept, List.mem_filterMap]

theorem projected_bound (m : Half) (r : Fin 160) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + Live516.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega

theorem projection_survives (m : Half) (r : Fin 160) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (h : Live516.live basicOps goal k ws.toFinset) :
    maybeBuild (projectedBudget m r k ws) (available m r ws) = true := by
  have hbuild := Live516.project_live (crop_goal m r) (mask_projects m r) h _ (projected_bound m r k hn)
  rw [← available_spec] at hbuild
  exact maybeBuild_complete (List.nodup_dedup _) hbuild

end Check516

namespace Check516

abbrev Claim := Nat × List W
abbrev Hint := Half × Fin 160 × Nat

def goodClaim (c : Claim) : Bool := decide c.2.Nodup && !(maybeBuild c.1 c.2)

def usable (c : Claim) (m : Half) (r : Fin 160) (n : Nat) (ws : List W) : Bool :=
  projectedBudget m r n ws ≤ c.1 &&
  ws.all (fun w => match cropOpt m r w with | none => true | some y => c.2.contains y)

theorem unusable (c : Claim) (m : Half) (r : Fin 160) {n : Nat} {ws : List W}
    (hn : ws.Nodup) (live : Live516.live basicOps goal n ws.toFinset) (hc : goodClaim c) :
    usable c m r n ws = false := by
  apply Bool.eq_false_iff.mpr
  intro u
  simp only [goodClaim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  simp only [usable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at u
  have budget := projected_bound m r n hn
  have bound : n ≤ c.1 + Live516.zeros (cropOpt m r) ws.toFinset := by omega
  have build := Live516.project_live (crop_goal m r) (mask_projects m r) live _ bound
  have sub : Live516.kept (cropOpt m r) ws.toFinset ⊆ c.2.toFinset := by
    intro y hy
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hy
    have hy' : cropOpt m r w = some y := by simpa using hv
    have hu := u.2 w (List.mem_toFinset.mp hw)
    simpa [hy'] using hu
  have ok := maybeBuild_complete hc.1 (Live516.build_mono sub build)
  exact Bool.noConfusion (hc.2.symm.trans ok)

def key (n : Nat) (ws : List W) : Nat := ws.foldl (fun h w => (65599*h+w.toNat)%1000000007) n

def matched (table : List Claim) (hint : Nat → Option Hint) (n : Nat) (ws : List W) : Bool :=
  match hint (key n ws) with
  | none => false
  | some (m,r,j) => (table[j]?).any (fun c => usable c m r n ws)

theorem matched_false {table : List Claim} (ht : table.all goodClaim = true)
    (hint : Nat → Option Hint) {n : Nat} {ws : List W} (hn : ws.Nodup)
    (h : Live516.live basicOps goal n ws.toFinset) : matched table hint n ws = false := by
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
  | 0, n, _, ws => !(matched table hint n ws)
  | depth+1, n, extra, ws =>
    !(matched table hint n ws) && (ws == [goal] ||
      (pairs ws).any (fun (a,b,r) => dispatch extra (front table hint depth (n-1)) a b r))

theorem front_complete {table : List Claim} (ht : table.all goodClaim = true) (hint : Nat → Option Hint)
    (depth n : Nat) (ws : List W) (extra : Nat) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live516.live basicOps goal n ws.toFinset) :
    front table hint depth n extra ws = true := by
  induction depth generalizing n ws extra with
  | zero => simp [front, matched_false ht hint hn h]
  | succ depth ih =>
    simp only [front, matched_false ht hint hn h, Bool.not_false, Bool.true_and]
    cases n with
    | zero => simp [singleton_list hn h]
    | succ k =>
      simp only [Nat.add_one_sub_one]
      rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
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
          have hl : Live516.live basicOps goal k (z::kept).toFinset := by
            simpa [hfin] using tail
          have hc := Live516.live_card hl
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

theorem lower_of_front (table : List Claim) (hint : Nat → Option Hint) (depth : Nat)
    (ht : table.all goodClaim = true) (check : front table hint depth 11 4 inputs = false)
    (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : 12 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 11 := by change C.gates.length ≤ s at hsize; omega
  have searched := front_complete ht hint depth 11 inputs 4 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check516

namespace Check516

def checkedSet0 : Claim := (6, [0xc0e000000d80e0000000320cc0000000cc070000c0e000000980c00000002208c00000008c0600, 0xdb0000000d930000000032a000000000cd300000db0000000d120000000032a000000000c92000, 0xdb6cc0000c0060000000300c00000000c0030000db6cc0000d126100000032ac92000000c92302, 0xdbedc00000000000000032acd3000000000000004924400000000000000032ac92000000000000, 0xdbedc0000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3c1e3ffffe7cfffffffffddf3cfffffff3cfff00180c0000041021000000108410000000410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet0_ok : goodClaim checkedSet0 = true := by decide +kernel

def checkedSet1 : Claim := (4, [0x1ed80c00600000000000000000000000000000001ed88d1261000000000000000000000000, 0x38380d80e000000000000000000000000000000038300980c0000000000000000000000000, 0x3fc00d93000000000000000000000000000000000a400d1200000000000000000000000000, 0x3ff8c0000000000000000000000000000000000035b8c00000000000000000000000000000, 0xffffffc63ffe7cffffffffffffffffffffffffff0000000608841021000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet1_ok : goodClaim checkedSet1 = true := by decide +kernel

def checkedSet2 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c000000000180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet2_ok : goodClaim checkedSet2 = true := by decide +kernel

def checkedSet3 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet3_ok : goodClaim checkedSet3 = true := by decide +kernel

def checkedSet4 : Claim := (6, [0x8100000183106000000260cf0000000cf0c000008100000081106000000000450000000450c0, 0xc3e1c0000183000000000220c30000000c300000c3e1c000038b185000000a22c30000002c30a0, 0xc7000000038f000000000e60000000003cf00000c7000000030e000000000e600000000038a000, 0xc7e3c0000000000000000e63cf00000000000000452240000000000000000e638a000000000000, 0xc7e3c000038f187800000000000000000000000082c18000038b18500000000000000000000000, 0xfff8fc3ffffff0ff87ffffff9ff0ffffffff0fff00c0e000000380180000000a02c00000002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet4_ok : goodClaim checkedSet4 = true := by decide +kernel

def checkedSet5 : Claim := (7, [0x12000000001e78000000132c0000000008fc000012000000000228000000112c00000000085c, 0x7ec00000006e180000001f00000000000b3000007ec00000006f180000001fba000000000b3a, 0xe000000000f8000000001fc0000000000ff00000e000000000d8000000000ac00000000006a0, 0xffc000000000000000001fff0000000000000000364000000000000000001fba000000000000, 0xffc0000000fff800000000000000000000000000c980000000fdd00000000000000000000000, 0xffff1e3fffffffef9fffffffff30ffffffffff3f00001e000000002708000000153800000000091a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet5_ok : goodClaim checkedSet5 = true := by decide +kernel

def checkedSet6 : Claim := (6, [0x2000006000000000040000180040000000000000000000200000000004000008004000, 0x30300c0c000000000180000000000c000000000030300c0c000020000180100200200c000002000, 0x7000001c020000000180180000001c0180000000700000180200000001001800000018010000000, 0x70301c0000000000018018020070000000000000101004000000000001801002002000000000000, 0x70301c1c020030060000000000000000000000006020181c0200300400000000000000000000000, 0xf8fffe3fffdfffff9ffffe7ffff8ffffe7ffffff0003000040000200000800002000004000002000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet6_ok : goodClaim checkedSet6 = true := by decide +kernel

def checkedSet7 : Claim := (6, [0x1306c0678000000000012019e02c00c000000000000240228000000000012008a02c00c, 0x6c1106c061800000000001ec18600000000000006c1907e071800000000001ec1c603a00a, 0x7c0007f000000000000001fc00003f0000000000240007e0000000000000016400003a000, 0x7c1f000000000000000001fc1fe0000000000000581f00000000000000000098174000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff0ff87fffffffffffc3fe1ff0fff00000006018070070000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet7_ok : goodClaim checkedSet7 = true := by decide +kernel

def checkedSet8 : Claim := (7, [0xe000000000f8000000441fc0000001100ff00000e000000000d8000000000ac00000000006a0, 0x2412000000241e78000044132c0000011008fc002412000000240228000044112c00000110085c, 0x247ec00000246e180000441f00000001100b3000247ec00000246f180000441fba000001100b3a, 0x24ffc000000000000000441fff0000000000000024364000000000000000441fba000000000000, 0x24ffc0000024fff800000000000000000000000000c980000000fdd00000000000000000000000, 0xfffb1c3ffffffbe787fffffbfc30ffffffefff0f00201c000000202700000040143000000100090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet8_ok : goodClaim checkedSet8 = true := by decide +kernel

def checkedSet9 : Claim := (6, [0x18001c0019000066000630001c00001980000b0018001c0009000026000230001400000980000900, 0x7b0000001b100000000736000000001b860000007b0000001b100000000724000000001b04000000, 0x7b006cc018000060000600000c000018000003007b006cc01b10006c100724000e00001b04000320, 0x7b007ec000000000000736001f000000000000002900364000000000000736001f00000000000000, 0x7b007ec01b10006e180000000000000000000000520048801b10006c100000000000000000000000, 0xe4ffe13ffeeffff9e7ffc9fffffffffe79ffffff6000600012000048000500000a00001200000220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet9_ok : goodClaim checkedSet9 = true := by decide +kernel

def checkedSet10 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffe3fffdfffff9ffffe7ffff0ffffe7ffffff0007020040000e0008280200600802400200a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet10_ok : goodClaim checkedSet10 = true := by decide +kernel

def checkedSet11 : Claim := (6, [0x106000000000040000000000c40000000000000000200000000004000000000044, 0x6cc000000060000000000c0000000000030000006cc000000061000000000c92000000000302, 0xe000000000f0000000000cc00000000007c00000e000000000d00000000008c0000000000680, 0xedc000000000000000000cd70000000000000000244000000000000000000c92000000000000, 0xedc0000000f1e000000000000000000000000000c980000000f1c00000000000000000000000, 0xffff1e3fffffffef9fffffffff38ffffffffff3f00000c0000000021000000000410000000000102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet11_ok : goodClaim checkedSet11 = true := by decide +kernel

def checkedSet12 : Claim := (7, [0x441100e03e01fc0ff00000000000000000000000000000e03600ac06a0, 0x12000440000ffc001fff0000000000000000000012000440000364001fba000, 0x12012000000fffffe0000000000000000000000000000000000c9bf74000000, 0x1201244110012079f32c8fc000000000000000001201244110012008b12c85c, 0x120124411007edb87f00b3000000000000000000120124411007edbc7fbab3a, 0xffffffffffffffffffdffdfbfeff1c39e1c30f0f00000000000000000100104010001c09c143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet12_ok : goodClaim checkedSet12 = true := by decide +kernel

def checkedSet13 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c000100c0018380780600f020006000000010502400000040008380700600a020002008000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet13_ok : goodClaim checkedSet13 = true := by decide +kernel

def checkedSet14 : Claim := (6, [0x4180040c40000000000000000000000000000000008004044, 0x6cd800c0030000000000000000000000000000006cd840c92302, 0xe03c00cc07c00000000000000000000000000000e034008c0680, 0xedc000cd70000000000000000000000000000000244000c92000, 0xedfc780000000000000000000000000000000000c9bc70000000, 0xffffffffffffffffffffffffffff1e3be7f38f3f00000000000000000000000000000c0840410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet14_ok : goodClaim checkedSet14 = true := by decide +kernel

def checkedSet15 : Claim := (6, [0x13600132c00079e0008fc000000000000000000001200112c00008a00085c, 0x736001f00001b86000b3000000000000000000007bf001fba001bc6000b3a, 0x7c0001fc0003e00000ff000000000000000000005c0000ac00036000006a0, 0x7ff800000003ffe00000000000000000000000007ed800000003f74000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fff9e1ffff0f00000000000000000002380014300009c000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet15_ok : goodClaim checkedSet15 = true := by decide +kernel

def checkedSet16 : Claim := (6, [0x4020000100c001820060000000200060000000004020000000400082002004008020002008000, 0x3000000c010000000380600000002c00e0000000300000080100000001004000000008004000000, 0x30702c00000000000380600400c0000000000000105024000000000003806004008000000000000, 0x30702c0c0100c0038000000000000000000000002020080c0100800100000000000000000000000, 0xfcfffd3fffefffffc7fff9fffff3fffff1ffffff0007000040000c00002800004000024000008000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet16_ok : goodClaim checkedSet16 = true := by decide +kernel

def checkedSet17 : Claim := (4, [0x30300c0c000000000180000000000c000000000030300c0c000020000180100200200c000002000, 0x7000001c000000000180180000001c0000000000700000180000000001001800000018000000000, 0x70301c0000000000018018020030000000000000101004000000000001801002002000000000000, 0x70301c1c000030000000000000000000000000006020181c0000300000000000000000000000000, 0xf8fffe3ffffffffffffffe7ffffcffffffffffff0003000040000200000800002000004000002000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet17_ok : goodClaim checkedSet17 = true := by decide +kernel

def checkedSet18 : Claim := (4, [0x6cc000000060000000000c0000000000030000006cc000000061000000000c92000000000302, 0xe000000000e0000000000cc00000000007000000e000000000c00000000008c0000000000600, 0xedc000000000000000000cd30000000000000000244000000000000000000c92000000000000, 0xedc0000000e18000000000000000000000000000c980000000e1800000000000000000000000, 0xffff1e3fffffffffffffffffff3cffffffffffff00000c0000000021000000000410000000000102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet18_ok : goodClaim checkedSet18 = true := by decide +kernel

def checkedSet19 : Claim := (4, [0x6cd800c0030000000000000000000000000000006cd840c92302, 0xe03800cc07000000000000000000000000000000e030008c0600, 0xedc000cd30000000000000000000000000000000244000c92000, 0xedf8600000000000000000000000000000000000c9b860000000, 0xffffffffffffffffffffffffffff1e3ffff3cfff00000000000000000000000000000c0840410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet19_ok : goodClaim checkedSet19 = true := by decide +kernel

def checkedSet20 : Claim := (6, [0x8100000183106000000260cf0000000cf0c000008100000081106000000000450000000450c0, 0xc360c00000000000000000000000000000000000c360c000030a081000000a2282000000282020, 0xc3e1c0000183000000000220c30000000c300000c3e1c000038b185000000a22c30000002c30a0, 0xc7000000038f000000000e60000000003cf00000c7000000030e000000000e600000000038a000, 0xc7e3c0000000000000000e63cf00000000000000452240000000000000000e638a000000000000, 0xc7e3c000038f187800000000000000000000000082c18000038b18500000000000000000000000, 0xfff8fc3ffffff0ff87ffffff9ff0ffffffff0fff00c0e000000380180000000a02c00000002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet20_ok : goodClaim checkedSet20 = true := by decide +kernel

def checkedSet21 : Claim := (6, [0x1306c0678000000000012019e02c00c000000000000240228000000000012008a02c00c, 0x6c00000000000000000000cc00000000000000006c1905a051000000000000cc144012002, 0x6c1106c061800000000001ec18600000000000006c1907e071800000000001ec1c603a00a, 0x7c0007f000000000000001fc00003f0000000000240007e0000000000000016400003a000, 0x7c1f000000000000000001fc1fe0000000000000581f00000000000000000098174000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff0ff87fffffffffffc3fe1ff0fff00000006018070070000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet21_ok : goodClaim checkedSet21 = true := by decide +kernel

def checkedSet22 : Claim := (6, [0x81000001831060000002604d0000000cf0c000008100000081106000000000450000000450c0, 0xc38100000183000000000220410000000c300000c3810000038b104000000a20410000002c3080, 0xc7000000038f000000000e60000000003cf00000c7000000030e000000000e600000000038a000, 0xc78300000000000000000e614d00000000000000450200000000000000000e6108000000000000, 0xc7830000038f106800000000000000000000000082810000038b10400000000000000000000000, 0xfff8fcfffffff0ff97ffffff9ff2ffffffff0fff00c08000000380100000000a00400000002c0080])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet22_ok : goodClaim checkedSet22 = true := by decide +kernel

def checkedSet23 : Claim := (6, [0x81000001831060000002604d0000000cf0c000008100000081106000000000450000000450c0, 0xc300000000000000000000000000000000000000c3000000030a000000000a2000000000282000, 0xc38100000183000000000220410000000c300000c3810000038b104000000a20410000002c3080, 0xc7000000038f000000000e60000000003cf00000c7000000030e000000000e600000000038a000, 0xc78300000000000000000e614d00000000000000450200000000000000000e6108000000000000, 0xc7830000038f106800000000000000000000000082810000038b10400000000000000000000000, 0xfff8fcfffffff0ff97ffffff9ff2ffffffff0fff00c08000000380100000000a00400000002c0080])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet23_ok : goodClaim checkedSet23 = true := by decide +kernel

def checkedSet24 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000, 0xfbfffcffffcfffff87fff87ffff0ffffe1ffffff030700c0c0100e0010380500600202c00400a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet24_ok : goodClaim checkedSet24 = true := by decide +kernel

def checkedSet25 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c000000000180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000, 0xfbfffcffffcfffff87fff87ffff0ffffe1ffffff030700c0c0100e0010380500600202c00400a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet25_ok : goodClaim checkedSet25 = true := by decide +kernel

def checkedSet26 : Claim := (6, [0x13600112c00079e0008dc000000000000000000001200112c00008a00085c, 0x736001100001b8600081000000000000000000007bf001128001bc6000818, 0x7c0001140003e00000cd000000000000000000005c0000040003600000480, 0x7ff800000003ffe00000000000000000000000007ed800000003f74000000, 0x7ff80116d00000000000000000000000000000007bf001128000000000000, 0xfffffffffffffffffffe387ffeb2fff9e1ffff2f00000000000000000002380010200009c0000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet26_ok : goodClaim checkedSet26 = true := by decide +kernel

def checkedSet27 : Claim := (6, [0x13600112c00079e0008dc000000000000000000001200112c00008a00085c, 0x60000000000180000000000000000000000000007ad000000001b44000000, 0x736001100001b8600081000000000000000000007bf001128001bc6000818, 0x7c0001140003e00000cd000000000000000000005c0000040003600000480, 0x7ff800000003ffe00000000000000000000000007ed800000003f74000000, 0x7ff80116d00000000000000000000000000000007bf001128000000000000, 0xfffffffffffffffffffe387ffeb2fff9e1ffff2f00000000000000000002380010200009c0000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet27_ok : goodClaim checkedSet27 = true := by decide +kernel

def checkedSet28 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70300c1c030000000380780000003c01e000000070300c1c0300a0010180580200201c014002000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet28_ok : goodClaim checkedSet28 = true := by decide +kernel

def checkedSet29 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c000000000180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70300c1c030000000380780000003c01e000000070300c1c0300a0010180580200201c014002000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet29_ok : goodClaim checkedSet29 = true := by decide +kernel

def checkedSet30 : Claim := (6, [0x13600132c00049a0008dc000000000000000000001200112c00008a00085c, 0x736001f0000008200081000000000000000000007bf001fba000082000818, 0x7c0001fc0002400000cd000000000000000000005c0000ac0002400000480, 0x7ff8000000024ba00000000000000000000000007ed800000002430000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fffbe5ffff2f0000000000000000000238001430000080000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet30_ok : goodClaim checkedSet30 = true := by decide +kernel

def checkedSet31 : Claim := (6, [0x13600132c00049a0008dc000000000000000000001200112c00008a00085c, 0x600000c0000000000000000000000000000000007ad000e92000000000000, 0x736001f0000008200081000000000000000000007bf001fba000082000818, 0x7c0001fc0002400000cd000000000000000000005c0000ac0002400000480, 0x7ff8000000024ba00000000000000000000000007ed800000002430000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fffbe5ffff2f0000000000000000000238001430000080000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet31_ok : goodClaim checkedSet31 = true := by decide +kernel

def checkedSet32 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c0c000000000380780600f00c000000000030702c0c0100a0010380700600a00c004002000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet32_ok : goodClaim checkedSet32 = true := by decide +kernel

def checkedSet33 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c000000000180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c0c000000000380780600f00c000000000030702c0c0100a0010380700600a00c004002000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet33_ok : goodClaim checkedSet33 = true := by decide +kernel

def checkedSet34 : Claim := (6, [0x13600132c00079e0008fc000000000000000000001200112c00008a00085c, 0x600000c0000180000030000000000000000000007ad000e92001b44000322, 0x736001f00001b86000b3000000000000000000007bf001fba001bc6000b3a, 0x7c0001fc0003e00000ff000000000000000000005c0000ac00036000006a0, 0x7ff800000003ffe00000000000000000000000007ed800000003f74000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fff9e1ffff0f00000000000000000002380014300009c000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet34_ok : goodClaim checkedSet34 = true := by decide +kernel

def checkedSet35 : Claim := (6, [0x1306c0678000000000012009a02c00c000000000000240228000000000012008a02c00c, 0x6c1106c0618000000000012008200000000000006c1907e07180000000000120082028008, 0x7c0007f0000000000000013000002d0000000000240007e00000000000000120000028000, 0x7c1f000000000000000001300ba0000000000000581f00000000000000000010030000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff0ff87fffffffffffcffe5ff2fff0000000601807007000000000000100080020008])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet35_ok : goodClaim checkedSet35 = true := by decide +kernel

def checkedSet36 : Claim := (6, [0x1306c0678000000000012009a02c00c000000000000240228000000000012008a02c00c, 0x6c000000000000000000000000000000000000006c1905a05100000000000000000000000, 0x6c1106c0618000000000012008200000000000006c1907e07180000000000120082028008, 0x7c0007f0000000000000013000002d0000000000240007e00000000000000120000028000, 0x7c1f000000000000000001300ba0000000000000581f00000000000000000010030000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff0ff87fffffffffffcffe5ff2fff0000000601807007000000000000100080020008])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet36_ok : goodClaim checkedSet36 = true := by decide +kernel

def checkedSet37 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0x70703c1c0300f0078180000000000c000000000070301c1c0300b0050180500200200c004002000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet37_ok : goodClaim checkedSet37 = true := by decide +kernel

def checkedSet38 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c000000000180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0x70703c1c0300f0078180000000000c000000000070301c1c0300b0050180500200200c004002000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet38_ok : goodClaim checkedSet38 = true := by decide +kernel

def checkedSet39 : Claim := (6, [0xc360c00000000000000000000000000000000000c360c000030a081000000a2282000000282020, 0xc7000000038f000000000e20000000003c300000c7000000030e000000000e2000000000382000, 0xc7e3c0000000000000000e23c300000000000000452240000000000000000e2382000000000000, 0xc7e3c000038f081800000000000000000000000082c18000038b08100000000000000000000000, 0xfff8fc3ffffff0ffe7ffffffdffcffffffffcfff00c0e000000380080000000a02c00000002c0020])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet39_ok : goodClaim checkedSet39 = true := by decide +kernel

def checkedSet40 : Claim := (6, [0x12400000400071c0000c40000000000000000000000000004000008000044, 0x60000000000180000000000000000000000000007ad000000001b44000000, 0x7c0000040003e000004c000000000000000000005c0000040003600000480, 0x7ed800000003f7c00000000000000000000000007ed800000003f74000000, 0x7ed80004500000000000000000000000000000007ad000000000000000000, 0xfffffffffffffffffffe3a7fffbafff9e3ffff3f0000000000000000000228000000000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet40_ok : goodClaim checkedSet40 = true := by decide +kernel

def checkedSet41 : Claim := (6, [0x12400000400071c0000c40000000000000000000000000004000008000044, 0x60000000000180000000000000000000000000007ad000000001b44000000, 0x724000000001b0400000000000000000000000007ad000000001b44000000, 0x7c0000040003e000004c000000000000000000005c0000040003600000480, 0x7ed800000003f7c00000000000000000000000007ed800000003f74000000, 0x7ed80004500000000000000000000000000000007ad000000000000000000, 0xfffffffffffffffffffe3a7fffbafff9e3ffff3f0000000000000000000228000000000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet41_ok : goodClaim checkedSet41 = true := by decide +kernel

def checkedSet42 : Claim := (7, [0x18001c0039c00066000638001c000039e0000b0018001c00098000260002380014000009c0000900, 0x7b006cc018000060000600000c000018000003007b006cc01b90006c1007ad000e00001b44000320, 0xe0ffe13ffe0ffff9e7ffc07ffffffffe09ffffffe0006000360000480005c0000a00003600000220, 0xff0000003ff000000007ff800000003ff6000000ff0000003ff000000007ed800000003f74000000, 0xff006cc038c000600006c9800c00003860000300ff006cc03ff0006c1007ed800e00003f74000320, 0xff007ec0000000000007ff801f0000000000000029003640000000000007bf001f00000000000000, 0xff007ec03ff0006e180000000000000000000000d60048803ff0006c100000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet42_ok : goodClaim checkedSet42 = true := by decide +kernel

def checkedSet43 : Claim := (6, [0x13600132c0004180000c4000000000000000000001200112c000008000044, 0x600000c0000000000000000000000000000000007ad000e92000000000000, 0x736001f0000000000000000000000000000000007bf001fba000000000000, 0x7c0001fc00024000004c000000000000000000005c0000ac0002400000480, 0x7ff80000000243800000000000000000000000007ed800000002430000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fffbe7ffff3f0000000000000000000238001430000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet43_ok : goodClaim checkedSet43 = true := by decide +kernel

def checkedSet44 : Claim := (6, [0x13048047000000000000000180040040000000000000000200000000000000008004004, 0x6c000000000000000000000000000000000000006c1905a05100000000000000000000000, 0x7c0005b000000000000000100000050000000000240005a00000000000000000000000000, 0x7c1f000000000000000000100380000000000000581f00000000000000000010030000000, 0x7c1f05b05f0000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff4ff8ffffffffffffeffe7ffafff0000000601805005000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet44_ok : goodClaim checkedSet44 = true := by decide +kernel

def checkedSet45 : Claim := (6, [0x13048047000000000000000180040040000000000000000200000000000000008004004, 0x6c000000000000000000000000000000000000006c1905a05100000000000000000000000, 0x6c110480410000000000000000000000000000006c1905a05100000000000000000000000, 0x7c0005b000000000000000100000050000000000240005a00000000000000000000000000, 0x7c1f000000000000000000100380000000000000581f00000000000000000010030000000, 0x7c1f05b05f0000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff4ff8ffffffffffffeffe7ffafff0000000601805005000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet45_ok : goodClaim checkedSet45 = true := by decide +kernel

def checkedSet46 : Claim := (7, [0x639cc70e78000000000001c1981c00b0000000006098470270000000000001c0981400900, 0x1ed80c00600000000000006cd800c003000000001edb9f5a6d1000000000006cdb04e00320, 0x3fc00fff000000000000007ec001f000000000000a400f7e00000000000000364001f00000, 0x3ff8cd93e18000000000006cd800c003000000003fffffdbfdd000000000006cdb04e00320, 0x3ffff000000000000000007edb8600000000000035bff00000000000000000489b04000000, 0x3fffffffffd800000000000000000000000000003fffffdbfdd00000000000000000000000, 0xfffffff83e0f80f827ffffffffffe13e79ffffff00000038360b80d8000000000000601200a00220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet46_ok : goodClaim checkedSet46 = true := by decide +kernel

def checkedSet47 : Claim := (7, [0xc0e000000f80e00000007e0cc0000001fc070000c0e000000b80c00000002a08c0000000ac0600, 0xdb6cc0000c0060000000300c00000000c0030000db6cc0000f5a610000003aac92000000e92302, 0xff0000000fff000000007fe000000001ffb00000ff0000000f7e000000007fe000000001fba000, 0xff6cc0000e6c600000007c0c00000001f0030000ff6cc0000f7e610000007fec92000001fba302, 0xffedc0000000000000007fecd3000000000000006d2440000000000000007fec92000000000000, 0xffedc0000fffe18000000000000000000000000092c980000fdbe1800000000000000000000000, 0xff381e3ffffc70fffffffff19f3cffffffc34fff00380c0000047021000000518410000001430102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet47_ok : goodClaim checkedSet47 = true := by decide +kernel

def checkedSet48 : Claim := (6, [0xc0000000000000000000000c0000000000000000f5a00000000000000000000e92000, 0xe6c02080000000000000001f0081000000000000f7e02080000000000000001fba818, 0xf0000000000000000000001f8085000000000000b0000000000000000000000a80000, 0xf7e00000000000000000001fbe00000000000000f7e00000000000000000001fba000, 0xf7e0228000000000000000000000000000000000f5a00000000000000000000000000, 0xfffffffffffcf1ffd7ffffffffffffffffc71faf0000000000047002000000000000000001430808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet48_ok : goodClaim checkedSet48 = true := by decide +kernel

def checkedSet49 : Claim := (6, [0xc0000000000000000000000c0000000000000000f5a00000000000000000000e92000, 0xd1200000000000000000000c9200000000000000f5a00000000000000000000e92000, 0xe6c02080000000000000001f0081000000000000f7e02080000000000000001fba818, 0xf0000000000000000000001f8085000000000000b0000000000000000000000a80000, 0xf7e00000000000000000001fbe00000000000000f7e00000000000000000001fba000, 0xf7e0228000000000000000000000000000000000f5a00000000000000000000000000, 0xfffffffffffcf1ffd7ffffffffffffffffc71faf0000000000047002000000000000000001430808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet49_ok : goodClaim checkedSet49 = true := by decide +kernel

def checkedSet50 : Claim := (7, [0x607c07e1fc0e03800cc070000000000000000000605c02a0ac0e030008c0600, 0x6de00300c006cd800c00300000000000000000006dfad3aae926cd840c92302, 0x7f8007fe000edc000cd300000000000000000000368007fe000244000c92000, 0x7ff367c1f006cd800c00300000000000000000007ffbf7fffba6cd840c92302, 0x7ffff800000edf86000000000000000000000000497ed800000c9b860000000, 0x7fffffffffb000000000000000000000000000007ffbf7fffba000000000000, 0xfffffffffffffffff9c638719c341e3ffff3cfff000000000000000001c2385194300c0840410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet50_ok : goodClaim checkedSet50 = true := by decide +kernel

def checkedSet51 : Claim := (6, [0x8102608e00000800c0400000000000000000000000000004000008004040, 0x6180000000000000000000000000000000000000619850a2282000000000000, 0x638000e600002000010c00000000000000000000228000e6000020000108000, 0x6398700000002000a0000000000000000000000041185000000000000000000, 0x639870e638e00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f8ff9ff1fdfff5ff3fff00000000000000000601800a0280000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet51_ok : goodClaim checkedSet51 = true := by decide +kernel

def checkedSet52 : Claim := (6, [0x8102608e00000800c0400000000000000000000000000004000008004040, 0x6180000000000000000000000000000000000000619850a2282000000000000, 0x6188102208200000000000000000000000000000619850a2282000000000000, 0x638000e600002000010c00000000000000000000228000e6000020000108000, 0x6398700000002000a0000000000000000000000041185000000000000000000, 0x639870e638e00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f8ff9ff1fdfff5ff3fff00000000000000000601800a0280000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet52_ok : goodClaim checkedSet52 = true := by decide +kernel

def checkedSet53 : Claim := (6, [0x6c000000000000000000000000000000000000006c1905a05100000000000000000000000, 0x6c1106c0618000000000012008200000000000006c1907e07180000000000120082028008, 0x7c0007f0000000000000012000002c0000000000240007e00000000000000120000028000, 0x7c0c0130180000000000000000000000000000007c1f05b05d00000000000000000000000, 0x7c1f0000000000000000012008a0000000000000581f00000000000000000000000000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff0ff87fffffffffffdfff5ff3fff0000000601807007000000000000100080020008])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet53_ok : goodClaim checkedSet53 = true := by decide +kernel

def checkedSet54 : Claim := (6, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c000000000180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet54_ok : goodClaim checkedSet54 = true := by decide +kernel

def checkedSet55 : Claim := (6, [0x12000000001e78000000132c0000000008fc000012000000000228000000112c00000000085c, 0x6cc000000060000000000c0000000000030000006cc00000006d100000000e92000000000322, 0x7ec00000006e180000001f00000000000b3000007ec00000006f180000001fba000000000b3a, 0xe000000000f8000000001fc0000000000ff00000e000000000d8000000000ac00000000006a0, 0xffc000000000000000001fff0000000000000000364000000000000000001fba000000000000, 0xffc0000000fff800000000000000000000000000c980000000fdd00000000000000000000000, 0xffff1c3fffffffe787fffffffc30ffffffffff0f00001c000000002700000000143000000000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet55_ok : goodClaim checkedSet55 = true := by decide +kernel

def checkedSet56 : Claim := (6, [0x21000008400000000639060000002240000000002100000000000000041104000000000000000000, 0x21002240000000000001060003000000000000002100224000000000041106000300000000000000, 0x21c320484000000006180000000020400000000021c3204840020800061904080200204000200000, 0x21c72240000000000639060c030000000000000021452240000000000639060c0300000000000000, 0x21c7224840020c000000000000000000000000000082000840020800000000000000000000000000, 0xfef8fdbfbffff3ffffc7f9fffffffdbfffffffff20c0200800020000060100080200200000200000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet56_ok : goodClaim checkedSet56 = true := by decide +kernel

def checkedSet57 : Claim := (6, [0x26c1e78000000000000000132c8fc000000000000240228000000000000000112c85c, 0xc0060000000000000000000c0030000000000000f5a6d100000000000000000e92322, 0xe6c6e180000000000000001f00b3000000000000f7e6f180000000000000001fbab3a, 0xf80f8000000000000000001fc0ff000000000000b80d8000000000000000000ac06a0, 0xfff00000000000000000001fff00000000000000f7e00000000000000000001fba000, 0xffffff8000000000000000000000000000000000fdbfdd00000000000000000000000, 0xfffffffffffc70e787ffffffffffffffffc30f0f000000000004702700000000000000000143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet57_ok : goodClaim checkedSet57 = true := by decide +kernel

def checkedSet58 : Claim := (6, [0x120007c00013000090000000000980000000000012000240001200000000000000000000000000, 0x120980000013018000000000000000000000000012098240001301800000000000000000000000, 0x1b120886c00000000090000000000880000000001b120886c0801201009009000000088040000000, 0x1f120980000000000090098000000000000000000900000000000000009009000000000000000000, 0x1f120987c0c0130180000000000000000000000016120987c0c01301800000000000000000000000, 0xf8fdfe7e3ffffcffffeffe7ffffffe7fffffffff1810080600801001008008000000080040000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet58_ok : goodClaim checkedSet58 = true := by decide +kernel

def checkedSet59 : Claim := (6, [0x12079f32c8fc000000000000000000000000000012008b12c85c, 0x6cd800c0030000000000000000000000000000006cdb44e92322, 0x7edb87f00b3000000000000000000000000000007edbc7fbab3a, 0xe03e01fc0ff00000000000000000000000000000e03600ac06a0, 0xffc001fff0000000000000000000000000000000364001fba000, 0xfffffe0000000000000000000000000000000000c9bf74000000, 0xffffffffffffffffffffffffffff1c39e1c30f0f00000000000000000000000000001c09c143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet59_ok : goodClaim checkedSet59 = true := by decide +kernel

def checkedSet60 : Claim := (6, [0xc70018c0020c000638000c000062c00030000000c7000840020c000228000c0000224000300000, 0x63000018c210000006390600000062c2060000006300001082100000041104000000408204000000, 0x63c360d8c000000006180000000060c00000000063c360d8c212080816190408020060c204200020, 0x63c762c0000000000639060c030000000000000021452240000000000639060c0300000000000000, 0x63c762d8c2120c0818000000000000000000000042824098c2120808100000000000000000000000, 0xfcf8fd3f3feff3ffe7c7f9fffffffd3ff9ffffff60c0601802020008060100080200600200200020])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet60_ok : goodClaim checkedSet60 = true := by decide +kernel

def checkedSet61 : Claim := (6, [0x1b0007c000130000d80000a0000dc000013000001b00024000120000480000a000044000012000, 0x1b1b0cc6c000000000d8000000000cc0000000001b1b0cc6c080120100d80900a0120cc040012002, 0x1f000007c0c0000000d8098000000dc0600000001f00000580c00000009009800000098060000000, 0x1f1b0dc00000000000d80980a013000000000000090904400000000000d80900a012000000000000, 0x1f1b0dc7c0c0130180000000000000000000000016120987c0c01301800000000000000000000000, 0xf8fcfe3e3ffffcffffe7fe7fdffcfe3fffffcfff18180c060080100100c0080080100c0040010002])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet61_ok : goodClaim checkedSet61 = true := by decide +kernel

def checkedSet62 : Claim := (6, [0x6190c60660000000000001c1981c00b0000000006090460260000000000001c0981400900, 0x1ec00e6c000000000000007ec001f000000000000a400e6c00000000000000364001f00000, 0x1ed80c00600000000000006cd800c003000000001edb1e486c1000000000006cdb04e00320, 0x1edb1000000000000000007edb86000000000000149b100000000000000000489b04000000, 0x1edb1e6c6e1800000000000000000000000000001edb1e486c100000000000000000000000, 0xfffffff93eef93f9e7ffffffffffe13e79ffffff00000018120a0048000000000000601200a00220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet62_ok : goodClaim checkedSet62 = true := by decide +kernel

def checkedSet63 : Claim := (6, [0x606c0320cc0e03800cc070000000000000000000604c02208c0e030008c0600, 0x6d80032a000edc000cd3000000000000000000002480032a000244000c92000, 0x6de00300c006cd800c00300000000000000000006de8932ac926cd840c92302, 0x6dec9800000edf86000000000000000000000000496c9800000c9b860000000, 0x6dec9b2acd3000000000000000000000000000006de8932ac92000000000000, 0xfffffffffffffffff9e73e7ddf3c1e3ffff3cfff000000000000000000c2081084100c0840410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet63_ok : goodClaim checkedSet63 = true := by decide +kernel

def checkedSet64 : Claim := (4, [0x70000c0000c0000380000000002c0000000000007000040000c00002800000000024000000000, 0x30300c0c000000000180000000000c000000000030300c0c010080010180400000000c004000000, 0x30702c0000000000038060000000000000000000105024000000000003806000000000000000000, 0x30702c0c0100c0018000000000000000000000002020080c0100800100000000000000000000000, 0xfff8fd3ffffff3ffe7ffffffffffffffffffffff0300000080100000001004000000008004000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet64_ok : goodClaim checkedSet64 = true := by decide +kernel

def checkedSet65 : Claim := (7, [0x12079f32c8fc000000000000000000000000000012008b12c85c, 0x1ec19e02c00c00000000000000000000000000001ec9cf53e95e, 0x7edb87f00b3000000000000000000000000000007edbc7fbab3a, 0xffc001fff0000000000000000000000000000000364001fba000, 0xfffffe0000000000000000000000000000000000c9bf74000000, 0xffffffffffffffffffffffffffff1c39e1c30f0f00000000000000000000000000001c09c143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet65_ok : goodClaim checkedSet65 = true := by decide +kernel

def checkedSet66 : Claim := (6, [0x3000000c010000000380600000002c00e0000000300000080100000001004000000008004000000, 0x30300c0c000000000180000000000c000000000030300c0c010080010180400000000c004000000, 0x30702c00000000000380600400c0000000000000105024000000000003806004008000000000000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100c0018380600400802c006008000, 0x30702c0c0100c0038000000000000000000000002020080c0100800100000000000000000000000, 0xfcfffd3fffefffffc7fff9fffff3fffff1ffffff0007000040000c00002800004000024000008000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet66_ok : goodClaim checkedSet66 = true := by decide +kernel

def checkedSet67 : Claim := (7, [0x12000000001e78000000132c0000000008fc000012000000000228000000112c00000000085c, 0x7ec00000006e180000001f00000000000b3000007ec00000006f180000001fba000000000b3a, 0x7bff1c3fffffffe787ffbf7ffc30ffffffffff0f00001c000000002700000000143000000000090a, 0x8000e000200000f8000040001fc0002000000ff08000e000200000d8000040000ac00020000006a0, 0x8400ffc000000000000040801fff0000000000000000364000000000000000001fba000000000000, 0x8400ffc0204000fff800000000000000000000008400c980204000fdd00000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet67_ok : goodClaim checkedSet67 = true := by decide +kernel

def checkedSet68 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x702c000000c0078000000400c00000000c000000702c040000e0038280200600e02400a00e000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet68_ok : goodClaim checkedSet68 = true := by decide +kernel

def checkedSet69 : Claim := (6, [0x600000000068000000001f00000000000b700000600000000048000000000a00000000000220, 0x6cc000000060000000000c0000000000030000006cc00000006c100000000e00000000000320, 0x7ec000000000000000001f2c0000000000000000364000000000000000001f28000000000000, 0x7ec00000006e180000001f00000000000b3000007ec00000006e180000001f28000000000b38, 0x7ec00000006e380000000000000000000000000048800000006c100000000000000000000000, 0xffff9d3ffffffff7c7fffffffcf3ffffffffff8f00001c0000000026000000001420000000000908])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet69_ok : goodClaim checkedSet69 = true := by decide +kernel

def checkedSet70 : Claim := (7, [0x12079f32c8fc000000000000000000000000000012008b12c85c, 0x7edb87f00b3000000000000000000000000000007edbc7fbab3a, 0x2020008080000000000000e03e01fc0ff00000002020008080000000000000e03600ac06a0, 0x2100008100000000000000ffc001fff0000000000000000000000000000000364001fba000, 0x2120400000000000000000fffffe0000000000002120400000000000000000c9bf74000000, 0xffffffdeffff7effffffffffffff1c39e1c30f0f00000000000000000000000000001c09c143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet70_ok : goodClaim checkedSet70 = true := by decide +kernel

def checkedSet71 : Claim := (7, [0x380600400c02c01e00c000010502400000040028380700600e02c00e00e000, 0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet71_ok : goodClaim checkedSet71 = true := by decide +kernel

def checkedSet72 : Claim := (6, [0x601a01f00b700000000000000000000000000000601200a00220, 0x6cd800c0030000000000000000000000000000006cdb04e00320, 0x7ec001f2c0000000000000000000000000000000364001f28000, 0x7edb87f00b3000000000000000000000000000007edb87f28b38, 0x7edb8e0000000000000000000000000000000000489b04000000, 0xffffffffffffffffffffffffffff9d3df1cf3f8f00000000000000000000000000001c0981420908])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet72_ok : goodClaim checkedSet72 = true := by decide +kernel

def checkedSet73 : Claim := (4, [0x1c0000000066000000001c00000000000b0000001c0000000026000000001400000000000900, 0x6cc000000060000000000c0000000000030000006cc00000006c100000000e00000000000320, 0x7ec000000000000000001f000000000000000000364000000000000000001f00000000000000, 0x7ec00000006e180000000000000000000000000048800000006c100000000000000000000000, 0xffffe13ffffffff9e7ffffffffffffffffffffff0000600000000048000000000a00000000000220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet73_ok : goodClaim checkedSet73 = true := by decide +kernel

def checkedSet74 : Claim := (4, [0x1c1981c00b0000000000000000000000000000001c0981400900, 0x6cd800c0030000000000000000000000000000006cdb04e00320, 0x7ec001f000000000000000000000000000000000364001f00000, 0x7edb860000000000000000000000000000000000489b04000000, 0xffffffffffffffffffffffffffffe13e79ffffff0000000000000000000000000000601200a00220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet74_ok : goodClaim checkedSet74 = true := by decide +kernel

def checkedSet75 : Claim := (6, [0x1206c0660000000000012019802c00c000000000000240220000000000012008802c00c, 0x641006c060000000000001e41800000000000000641807e070000000000001e41c003a00a, 0x740007f000000000000001f400003f0000000000240007e0000000000000016400003a000, 0x741e000000000000000001f41f80000000000000501e00000000000000000090170000000, 0x741e07f07e000000000000000000000000000000741e05b05c00000000000000000000000, 0xfffffffebfdff0ff9ffffffffffffcbfe7ff0fff00000006018070070000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet75_ok : goodClaim checkedSet75 = true := by decide +kernel

def checkedSet76 : Claim := (6, [0x10000130000660003400002400019c00000c000010000000000220001000002400008800000c, 0x1b001c00011000060000340000000001840000001b001c000190000700003d0000300001c400000a, 0x1f00000001f0000000003d8000000001fc0000001f00000001f0000000002d800000000174000000, 0x1f001d000000000000003d800035000000000000090014000000000000003d000030000000000000, 0x1f001d0001f00007e000000000000000000000001600090001f00005c00000000000000000000000, 0xf8fffeffffcfffff9ffffa7ffffaffffe3ffffff18001c00018000070000380000300001c000000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet76_ok : goodClaim checkedSet76 = true := by decide +kernel

def checkedSet77 : Claim := (6, [0x13600132c0005980008cc000000000000000000001200112c00008800084c, 0x736001f0000098000090000000000000000000007bf001fba0009c000090a, 0x7c0001fc0002c00000dc000000000000000000005c0000ac0002400000480, 0x7ff800000002df800000000000000000000000007ed800000002d70000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fffbe7ffff3f00000000000000000002380014300009c000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet77_ok : goodClaim checkedSet77 = true := by decide +kernel

def checkedSet78 : Claim := (6, [0x130680670000000000010019802400c000000000000200220000000000010008802400c, 0x6c11068061000000000001c018000000000000006c1907a071000000000001c01c003000a, 0x7c0007b000000000000001d00000350000000000240007a00000000000000140000030000, 0x7c1f000000000000000001d01f80000000000000581f00000000000000000090170000000, 0x7c1f07b07f0000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff4ff8ffffffffffffeffe7ffafff00000006018070070000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet78_ok : goodClaim checkedSet78 = true := by decide +kernel

def checkedSet79 : Claim := (6, [0x10000120000660003000002400019800000c000010000000000220001000002400008800000c, 0x18001c000100000600003000000000018000000018001c00018000070000380000300001c000000a, 0x1c00000001e000000000388000000001f80000001c00000001e00000000028800000000170000000, 0x1c001d00000000000000388000350000000000000800140000000000000038000030000000000000, 0x1c001d0001e00007e000000000000000000000001400090001e00005c00000000000000000000000, 0xfbfffeffffdfffff9fffff7ffffaffffe7ffffff18001c00018000070000380000300001c000000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet79_ok : goodClaim checkedSet79 = true := by decide +kernel

def checkedSet80 : Claim := (6, [0x120600660000000000010019802400c000000000000200220000000000010008802400c, 0x6010060060000000000001c018000000000000006018070070000000000001c01c003000a, 0x7000071000000000000001d00000350000000000200007000000000000000140000030000, 0x701e000000000000000001d01f80000000000000501e00000000000000000090170000000, 0x701e07107e000000000000000000000000000000701e05105c00000000000000000000000, 0xfffffffeffdffeff9ffffffffffffeffe7ffafff00000006018070070000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet80_ok : goodClaim checkedSet80 = true := by decide +kernel

def checkedSet81 : Claim := (5, [0x1800070000110000c0000080000d00000110000018000200001000004000008000040000010000, 0x18180c060000000000c0000000000c000000000018180c060080100100c0080080100c0040010002, 0x1c00000700c0000000c0088000000d00600000001c00000500c00000008008800000090060000000, 0x1c180d000000000000c008808011000000000000080804000000000000c008008010000000000000, 0x1c180d0700c011018000000000000000000000001410090700c01101800000000000000000000000, 0xfbfffefefffffeffffffff7ffffefeffffffefff18180c060080100100c0080080100c0040010002])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet81_ok : goodClaim checkedSet81 = true := by decide +kernel

def checkedSet82 : Claim := (4, [0x40000800004000030000000000280000000000004000000000400002000000000020000000000, 0x3000000800000000010000000000080000000000300000080100000001004000000008004000000, 0x3040200000000000030060000000000000000000104020000000000003006000000000000000000, 0x3040200801004000800000000000000000000000200000080100000000000000000000000000000, 0xfffbfdfffffffbfff7ffffffffffffffffffffff0300000080100000001004000000008004000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet82_ok : goodClaim checkedSet82 = true := by decide +kernel

def checkedSet83 : Claim := (3, [0x60c000000000000000000000000000000000000060c204200020, 0x62c0003000000000000000000000000000000000224000300000, 0x62c2060000000000000000000000000000000000408204000000, 0xfffffffffffffffffffffffffffffd3ff9ffffff0000000000000000000000000000600200200020])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet83_ok : goodClaim checkedSet83 = true := by decide +kernel

def checkedSet84 : Claim := (4, [0x60000c0000c000020000000000200000000000006000040000c00002000000000020000000000, 0x2020080c000000000000000000000000000000002020080c0100800100000000000000000000000, 0x2060280000000000020020000000000000000000004020000000000002002000000000000000000, 0x2060280c0100c0018000000000000000000000002020080c0100800100000000000000000000000, 0xfff9fd7ffffff3ffe7ffffffffffffffffffffff0200000080100000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet84_ok : goodClaim checkedSet84 = true := by decide +kernel

def checkedSet85 : Claim := (4, [0x10240000000008cc000000000000000000000000102400000000084c, 0x1400000000000900000000000000000000000000143000000000090a, 0x1440000000000dc00000000000000000000000000040000000000480, 0x14750000000000000000000000000000000000001430000000000000, 0xffffffffffffffffffffffffffbaffffffffff3f000000000000000000000000143000000000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet85_ok : goodClaim checkedSet85 = true := by decide +kernel

def checkedSet86 : Claim := (6, [0x100000000006000000000050000000000000000010000000000600000000005000008000000, 0x400010000e000006000098000050000780000000400010000600000600000800005000038000000, 0x1800000001c000000000280000000001600000001800000001800000000028000000000140000000, 0x1f0001000000000000002d800005000000000000090000000000000000002d000000000000000000, 0x1f00010001f000006000000000000000000000001600010001f00000400000000000000000000000, 0xe0fffeffff3ffffffffff67ffffeffff9fffffff0000000000000000200000000004000008000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet86_ok : goodClaim checkedSet86 = true := by decide +kernel

def checkedSet87 : Claim := (6, [0xc50e58000000000000000000000000000000000045025000000000000000000000000, 0xd93e180000000000000000004100000000000000fdbfdd00000000000000000041080, 0xe486c10000000000000000000000000000000000f5a6d100000000000000000000000, 0xfdb0000000000000000000004500000000000000f5a00000000000000000000000000, 0xfdbfdf0000000000000000000000000000000000fdbfdd00000000000000000000000, 0xffffffffffffa4fa0fffffffffffffffffffafff00000000000b80d8000000000000000000040080])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet87_ok : goodClaim checkedSet87 = true := by decide +kernel

def checkedSet88 : Claim := (6, [0x20000000000000000800c0000000000000000000200000000000000008004004, 0x100640628000000000012018a02c00c000000000000240228000000000012008a02c00c, 0x6000074000000000000001e000003c0000000000200007400000000000000160000038000, 0x6018000000000000000001e01ca0000000000000401800000000000000000080140000000, 0x6018074072800000000000000000000000000000601805005000000000000000000000000, 0xfffffff9feff9bf9f7ffffffffffe1fe7dffffff0000000000000000200000000000000008004004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet88_ok : goodClaim checkedSet88 = true := by decide +kernel

def checkedSet89 : Claim := (6, [0xc0e000000d80e0000000320cc0000000cc070000c0e000000980c00000002208c00000008c0600, 0xdb0000000d930000000032a000000000cd300000db0000000d120000000032a000000000c92000, 0xdb6cc0000c0060000000300c00000000c0030000db6cc0000d126100000032ac92000000c92302, 0xdbedc00000000000000032acd3000000000000004924400000000000000032ac92000000000000, 0xdbedc0000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3c1e3ffffe7cfffffffffddf3cfffffff3cfff00180c0000041021000000108410000000410102, 0xffff7efffffe7cfffffffffddf3cfffffff3cfff00db6cc0000d126100000032ac92000000c92302])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet89_ok : goodClaim checkedSet89 = true := by decide +kernel

def checkedSet90 : Claim := (5, [0x6190c60660000000000001000810008000000000609046026000000000000100081000800, 0x1ec00e6c000000000000001200011000000000000a400e6c00000000000000120001100000, 0x1ed80c00600000000000000000000000000000001edb1e486c100000000000000000000000, 0x1edb100000000000000000120082000000000000149b100000000000000000000000000000, 0x1edb1e6c6e1800000000000000000000000000001edb1e486c100000000000000000000000, 0xfffffff93eef93f9e7ffffffffffedff7dffffff00000018120a0048000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet90_ok : goodClaim checkedSet90 = true := by decide +kernel

def checkedSet91 : Claim := (6, [0x120007c00013000090000000000980000000000012000240001200000000000000000000000000, 0x120980000013018000000000000000000000000012098240001301800000000000000000000000, 0x1b120886c00000000090000000000880000000001b120886c0801201009009000000088040000000, 0x1f120980000000000090098000000000000000000900000000000000009009000000000000000000, 0x1f120987c0c0130180000000000000000000000016120987c0c01301800000000000000000000000, 0xf8fdfe7e3ffffcffffeffe7ffffffe7fffffffff1810080600801001008008000000080040000000, 0xfbfffefefffffcfffffffe7ffffffeffffffffff1b120886c0801201009009000000088040000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet91_ok : goodClaim checkedSet91 = true := by decide +kernel

def checkedSet92 : Claim := (7, [0x12079f32c8fc000000000000000000000000000012008b12c85c, 0x7edb87f00b3000000000000000000000000000007edbc7fbab3a, 0xe03e01fc0ff00000000000000000000000000000e03600ac06a0, 0xffc001fff0000000000000000000000000000000364001fba000, 0xfffffe0000000000000000000000000000000000c9bf74000000, 0xffffffffffffffffffffffffffff1ef9e7c30f0f00000000000000000000000000001ec9c753a91a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet92_ok : goodClaim checkedSet92 = true := by decide +kernel

def checkedSet93 : Claim := (6, [0x100000001006000000000050000000050000000010000000100600000000005000000005040, 0x8100000181106000000200c50000000c50c000008100000081106000000000450000000450c0, 0xc00000000381000000000a00000000002c500000c00000000300000000000a0000000000280000, 0xc0e100000000000000000a02c500000000000000402000000000000000000a0280000000000000, 0xc0e100000381186000000000000000000000000080c10000038118400000000000000000000000, 0xff3f1efffffe7efffffffffdff3efffffff3efff0000000000000000200000000004000000004040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet93_ok : goodClaim checkedSet93 = true := by decide +kernel

def checkedSet94 : Claim := (6, [0x8100000183106000000260c50000000cf0c000008100000081106000000000450000000450c0, 0x7010000000f0060000000600500000000f0000007010000000f0060000004600500000010f040, 0xc7000000038f000000000e60000000003cf00000c7000000030e000000000e600000000038a000, 0xc7e100000000000000000e62c500000000000000452000000000000000000e6280000000000000, 0xc7e10000038f186000000000000000000000000082c10000038b18400000000000000000000000, 0xff3c1efffffe7cfffffffffddf3efffffff3cfff000400000000040020000004400400000010c040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet94_ok : goodClaim checkedSet94 = true := by decide +kernel

def checkedSet95 : Claim := (3, [0x18000c000000000000000000000000000000000018000c0001000004000020000000000100000000, 0x18001c00000000000000300000000000000000000800140000000000000030000000000000000000, 0x18001c00010000060000000000000000000000001000080001000004000000000000000000000000, 0xffffe3fffffffff9ffffffffffffffffffffffff1800000001000000000020000000000100000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet95_ok : goodClaim checkedSet95 = true := by decide +kernel

def checkedSet96 : Claim := (6, [0x3000008c010000002380600000022c0060000000300000080100000001004000000008004000000, 0x30002c000100000180006000000000006000000030002c080100000181006000000008006000000, 0x3c300c8c000000002180000000020c00000000003c300c8c012080012180408000020c004200000, 0x3c702c0000000000238060c000000000000000001450240000000000238060c0000000000000000, 0x3c702c8c0120c0018000000000000000000000002820088c0120800100000000000000000000000, 0xfcf8fd3f3feff3ffe7c7f9fffffffd3ff9ffffff00c0000800020000020000080000200000200000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet96_ok : goodClaim checkedSet96 = true := by decide +kernel

def checkedSet97 : Claim := (4, [0x1fff1fffffffffffffff3fffff3fffffffffffff00c0000800010000020000020000200000080000, 0x60c060180000000006000000000060000000000060c0601800010000060080020080600000080000, 0xe0000038000000000600c0000000e00000000000e0000030000000000400c0000000c00000000000, 0xe0c0e000000000000600c00200c00000000000002040200000000000060080020080000000000000, 0xe0c0e03800018000000000000000000000000000c080c03800018000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet97_ok : goodClaim checkedSet97 = true := by decide +kernel

def checkedSet98 : Claim := (6, [0xc18260cf8104180c50c000000000000000000000408000458104180450c0, 0x380780600f010018005000000000000000000000380784610f010018005040, 0x638000e6000e100002c500000000000000000000228000e6000200000280000, 0x639c7800000e1061800000000000000000000000411c5800000c10610000000, 0x639c78e63cf00000000000000000000000000000639870e638a000000000000, 0xfffffffffffffffff9e73e7ddf3c1efffff3efff000000000000000000200204410c000008004040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet98_ok : goodClaim checkedSet98 = true := by decide +kernel

def checkedSet99 : Claim := (6, [0x470000c0000c000638000c000002c0000000000047000040000c000228000c0000024000000000, 0x20402000000000000601000c03000000000000002040200000000000060100080200000000000000, 0x234320c0c000000006180000000000c000000000234320c0c010080016190408020000c004000000, 0x234722c0000000000639060c030000000000000021452240000000000639060c0300000000000000, 0x234722c0c0100c0018000000000000000000000002020080c0100800100000000000000000000000, 0xffb8dd3ffffff3ffe7fffff3fcffffffffffffff2300000080100000041104000000008004000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet99_ok : goodClaim checkedSet99 = true := by decide +kernel

def checkedSet100 : Claim := (6, [0xc0e000000d80e00000002208c00000008c060000c0e000000980c00000002208c00000008c0600, 0xd20000000d93000000002200000000008c100000d20000000d1200000000220000000000880000, 0xd26880000c006000000020080000000080020000d26880000d1261000000220880000000880200, 0xd2e980000000000000002208c10000000000000040200000000000000000220880000000000000, 0xd2e980000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3d1e7ffffe7cfffffffffdff3efffffff3efff0010080000041021000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet100_ok : goodClaim checkedSet100 = true := by decide +kernel

def checkedSet101 : Claim := (6, [0x100e01301c000000000000000000000000000000100600100c00000000000000000000000, 0x601c070078000000000001c018000000000000006018070070000000000001c0180000000, 0x7c0007f000000000000001ec0000000000000000240007e00000000000000164000000000, 0x7c0c013018000000000000cc00000000000000007c1f05b05d000000000000cc104000000, 0x7c1f07f07d8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xffffffffffff80f827ffffffffffffffffffffff0000000581f00000000000000000088104000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet101_ok : goodClaim checkedSet101 = true := by decide +kernel

def checkedSet102 : Claim := (4, [0x8000000180100000000200c00000000c00800000800000008010000000000040000000040080, 0xc00000000380000000000a00000000002c000000c00000000300000000000a0000000000280000, 0xc0e000000000000000000a02c000000000000000402000000000000000000a0280000000000000, 0xc0e000000380180000000000000000000000000080c00000038018000000000000000000000000, 0xff3f1ffffffe7ffffffffffdff3ffffffff3ffff0000000000000000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet102_ok : goodClaim checkedSet102 = true := by decide +kernel

def checkedSet103 : Claim := (4, [0xc00200c08004000c00800000000000000000000040000040800400040080, 0x600000a0000e000002c000000000000000000000200000a0000200000280000, 0x601c0000000e0060000000000000000000000000401c0000000c00600000000, 0x601c00a02c000000000000000000000000000000601800a0280000000000000, 0xfffffffffffffffff9ff3ffdff3f1ffffff3ffff0000000000000000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet103_ok : goodClaim checkedSet103 = true := by decide +kernel

def checkedSet104 : Claim := (6, [0x800039000381000000000000008100000450000080000800030000000000000000000000000000, 0x40804018020200080000000000000000000000004080401802030008000000000000000000000000, 0xc400003906200000000040800000810418000000c400003106200000000040800000810410000000, 0xc480c100000000000000408000450000000000000000000000000000000000000000000000000000, 0xc480c13900018100000040800041810000041000c480c13906238118400040800041810410041080, 0xc480c13906238118600000000000000000000000c480c13906238118400000000000000000000000, 0xfbfffefeffdffeff9fffff7ffffafeffe7ffafffc080c03806038018000040000040800400040080])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet104_ok : goodClaim checkedSet104 = true := by decide +kernel

def checkedSet105 : Claim := (6, [0x6000000000040000000040000000000000000000200000000004000000004040, 0x8100000181106000000200c50000000c50c000008100000081106000000000450000000450c0, 0xc00000000381000000000a00000000002c500000c00000000300000000000a0000000000280000, 0xc0e100000000000000000a02c500000000000000402000000000000000000a0280000000000000, 0xc0e100000381186000000000000000000000000080c10000038118400000000000000000000000, 0xff3f1efffffe7efffffffffdff3efffffff3efff0000000000000000200000000004000000004040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet105_ok : goodClaim checkedSet105 = true := by decide +kernel

def checkedSet106 : Claim := (6, [0x8000000182100000000260c00000000ca0800000800000008010000000000040000000040080, 0x7000000000c000000000000000000000000000007000000000e0000000004600000000010a000, 0xc7000000038e000000000e60000000003ca00000c7000000030e000000000e600000000038a000, 0xc7e000000000000000000e62c000000000000000452000000000000000000e6280000000000000, 0xc7e00000038e180000000000000000000000000082c00000038a18000000000000000000000000, 0xff3c1ffffffe7dfffffffffddf3ffffffff3dfff0004000000000400000000044000000000108000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet106_ok : goodClaim checkedSet106 = true := by decide +kernel

def checkedSet107 : Claim := (6, [0xc10260ca8004000c00800000000000000000000040000040800400040080, 0x3806000000000000000000000000000000000000380704610a000000000000, 0x638000e6000e000002c000000000000000000000228000e6000200000280000, 0x639c7000000e0060000000000000000000000000411c5000000c00600000000, 0x639c70e63ca00000000000000000000000000000639870e638a000000000000, 0xfffffffffffffffff9e73efddf3d1ffffff3ffff0000000000000000002002044108000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet107_ok : goodClaim checkedSet107 = true := by decide +kernel

def checkedSet108 : Claim := (6, [0x8000050100180050000000000000000000000000800005010018005040, 0xc08200c58104180c50c000000000000000000000408000458104180450c0, 0x600000a0000e100002c500000000000000000000200000a0000200000280000, 0x601c0800000e1061800000000000000000000000401c0800000c10610000000, 0x601c08a02c500000000000000000000000000000601800a0280000000000000, 0xfffffffffffffffff9ff3f7dff3e1efffff3efff0000000000000000000000000004000008004040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet108_ok : goodClaim checkedSet108 = true := by decide +kernel

def checkedSet109 : Claim := (6, [0x1020020000002600c00000008e0400000000000000000200000000004000000004040, 0xc300000001020000000002200000000008200000c3000000030a000000000a2000000000282000, 0xc7000000030e000000000e600000000038e00000c7000000030e000000000e600000000038a000, 0xc70200000000000000000e610c00000000000000450200000000000000000e6108000000000000, 0xc7020000030e002800000000000000000000000082000000030a00000000000000000000000000, 0xfff8fdfffffff1ffd7ffffff9ff3ffffffff1fff00c00000000300000000000a0000000000280000, 0xfff8fdfffffff3fff7ffffffffffffffffffffff00c00000000300002000000a0004000000284040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet109_ok : goodClaim checkedSet109 = true := by decide +kernel

def checkedSet110 : Claim := (6, [0x8102608e00000800c0400000000000000000000000000004000008004040, 0x6188102208200000000000000000000000000000619850a2282000000000000, 0x638000e600002000010c00000000000000000000228000e6000020000108000, 0x6398700000002000a0000000000000000000000041185000000000000000000, 0x639870e638e00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f8ff9ff1fdfff5ff3fff00000000000000000601800a0280000000000000, 0xffffffffffffffffffc7f9fffffffdfffdffffff00000000000000000601800a0284000008004040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet110_ok : goodClaim checkedSet110 = true := by decide +kernel

def checkedSet111 : Claim := (6, [0x8000000180100000000200c00000000c00800000800000008010000000000040000000040080, 0xc3e0c0000180000000000200c00000000c000000c3e0c0000388181000000a02c00000002c00a0, 0xc7000000038c000000000e00000000003c000000c7000000030c000000000e0000000000380000, 0xc7e2c0000000000000000e03c000000000000000452240000000000000000e0380000000000000, 0xc7e2c000038c181800000000000000000000000082c08000038818100000000000000000000000, 0xfff8fd3ffffff3ffe7ffffffffffffffffffffff00c0e000000380180000000a02c00000002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet111_ok : goodClaim checkedSet111 = true := by decide +kernel

def checkedSet112 : Claim := (6, [0xc00200c08004000c00800000000000000000000040000040800400040080, 0x618c00200c0e0c0000c000000000000000000000619c40a02c0e0c6042c00a0, 0x638000e0000e2c0003c000000000000000000000228000e0000224000380000, 0x639c6000000e2c60600000000000000000000000411c4000000c08604000000, 0x639c60e03c000000000000000000000000000000639860e0380000000000000, 0xffffffffffffffffffc7f9fffffffd3ff9ffffff00000000000000000601c00a02c0e006002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet112_ok : goodClaim checkedSet112 = true := by decide +kernel

def checkedSet113 : Claim := (7, [0x12000000001e78000000132c0000000008fc000012000000000228000000112c00000000085c, 0x7ec00000006e180000001f00000000000b3000007ec00000006f180000001fba000000000b3a, 0xe000000000f8000000001fc0000000000ff00000e000000000d8000000000ac00000000006a0, 0xffc000000000000000001fff0000000000000000364000000000000000001fba000000000000, 0xffc0000000fff800000000000000000000000000c980000000fdd00000000000000000000000, 0xffff1c3fffffffe787fffffffc30ffffffffff0f00001c000000002700000000143000000000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet113_ok : goodClaim checkedSet113 = true := by decide +kernel

def checkedSet114 : Claim := (6, [0x26c1c70000000000000000132c0c4000000000000240020000000000000000112c044, 0xe6c6c100000000000000001f0000000000000000f7e6d100000000000000001fba000, 0xf80f8000000000000000001fc04c000000000000b80d8000000000000000000ac0480, 0xfff00000000000000000001fff00000000000000f7e00000000000000000001fba000, 0xffffdf0000000000000000000000000000000000fdbfdd00000000000000000000000, 0xfffffffffffc70e78fffffffffffffffffc30f3f0000000000047025000000000000000001430000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet114_ok : goodClaim checkedSet114 = true := by decide +kernel

def checkedSet115 : Claim := (6, [0xc38100000183000000000220410000000c300000c3810000038b104000000a20410000002c3080, 0xc7000000020c000000000c000000000030000000c7000000030e000000000e600000000038a000, 0xc7000000038f000000000e60000000003cf00000c7000000030e000000000e600000000038a000, 0xc78100000000000000000e604500000000000000450000000000000000000e6000000000000000, 0xc7810000038f106000000000000000000000000082810000038b10400000000000000000000000, 0xfff8fefffffff0ff9fffffff9ffaffffffff0fff00c08000000380100000000a00400000002c0080])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet115_ok : goodClaim checkedSet115 = true := by decide +kernel

def checkedSet116 : Claim := (5, [0xc08000000d8080000000320040000000cc040000c08000000980800000002200400000008c0400, 0xdb0000000c0000000000300000000000c0000000db0000000d120000000032a000000000c92000, 0xdb0000000d930000000032a000000000cd300000db0000000d120000000032a000000000c92000, 0xdb81000000000000000032a041000000000000004900000000000000000032a000000000000000, 0xdb8100000d938080000000000000000000000000928100000d9380800000000000000000000000, 0xff3c7efffffe7cfffffffffddfbefffffff3cfff0018000000041000000000108000000000410000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet116_ok : goodClaim checkedSet116 = true := by decide +kernel

def checkedSet117 : Claim := (4, [0x60000000020000000001020000000002020000006000000002000000000100000000000200000000, 0x60006000000000000000000000000000000000006000600002000008000100000200000200000020, 0x60006200000000000001020003000000000000002000220000000000000102000300000000000000, 0x60006200020000080800000000000000000000004000400002000008000000000000000000000000, 0xfffffdfffffffffff7fffdfffffffffffdffffff6000600002000008000100000200000200000020])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet117_ok : goodClaim checkedSet117 = true := by decide +kernel

def checkedSet118 : Claim := (3, [0x600000c000000000000000000000000000000000724000e00000000000000, 0x630001c000000000000000000000000000000000230001400000000000000, 0x7360000000000000000000000000000000000000724000000000000000000, 0xffffffffffffffffffffc9ffffffffffffffffff0000000000000000000500000a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet118_ok : goodClaim checkedSet118 = true := by decide +kernel

def checkedSet119 : Claim := (4, [0x18000060000000000000000000000000000000001b10006c100000000000000000000000, 0x190000660000000000000000800008000000000009000026000000000000000080000800, 0x1b100000000000000000000082000000000000001b100000000000000000000000000000, 0x1b10006e180000000000000000000000000000001b10006c100000000000000000000000, 0xfffffffffeeffff9e7ffffffffffffff7dffffff0000000012000048000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet119_ok : goodClaim checkedSet119 = true := by decide +kernel

def checkedSet120 : Claim := (4, [0x200000400402001800c000000000000000000000200000400402000800c000, 0x2800000000024000000000000000000000000000280000600002400000a000, 0x28008000000340180000000000000000000000000000800000010010000000, 0x28008060050000000000000000000000000000002800006000000000000000, 0xffffffffffffffffffffff7ffffaffffe7ffffff000000000000000000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet120_ok : goodClaim checkedSet120 = true := by decide +kernel

def checkedSet121 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000, 0xfbfbfcffffcff3ff87dff87fbff0fdffe1ff3fff030300c0c0100a0010180500200200c004002000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet121_ok : goodClaim checkedSet121 = true := by decide +kernel

def checkedSet122 : Claim := (6, [0x100000000006000000000050000000000000000010000000000600000000005000000000040, 0x8100000180106000000200c50000000c00c000008100000080106000000000450000000400c0, 0xc00000000380000000000a00000000002c000000c00000000300000000000a0000000000280000, 0xc0e100000000000000000a02c500000000000000402000000000000000000a0280000000000000, 0xc0e100000380186000000000000000000000000080c10000038018400000000000000000000000, 0xff3f1efffffe7ffffffffffdff3efffffff3ffff0000000000000000200000000004000000000040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet122_ok : goodClaim checkedSet122 = true := by decide +kernel

def checkedSet123 : Claim := (6, [0x13048047000000000000000180000040000000000000000200000000000000008000004, 0x6c110480410000000000000000000000000000006c1905a05100000000000000000000000, 0x7c0005b000000000000000000000000000000000240005a00000000000000000000000000, 0x7c1f000000000000000000000380000000000000581f00000000000000000000030000000, 0x7c1f05b05f0000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff4ff8fffffffffffffffe7ffffff0000000601805005000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet123_ok : goodClaim checkedSet123 = true := by decide +kernel

def checkedSet124 : Claim := (6, [0xd1200000000000000000000c9200000000000000f5a00000000000000000000e92000, 0xe6c02080000000000000001f0081000000000000f7e02080000000000000001fba818, 0xf0000000000000000000001f8085000000000000b0000000000000000000000a80000, 0xf7e02080000000000000001fbe81000000000000f7e02080000000000000001fba818, 0xf7e0228000000000000000000000000000000000f5a00000000000000000000000000, 0xfffffffffffcf1ffd7ffffffffffffffffc71faf0000000000047002000000000000000001430808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet124_ok : goodClaim checkedSet124 = true := by decide +kernel

def checkedSet125 : Claim := (6, [0xc0e000000d80e0000000320cc0000000cc070000c0e000000980c00000002208c00000008c0600, 0xdb0000000d930000000032a000000000cd300000db0000000d120000000032a000000000c92000, 0xdb6cc0000c0060000000300c00000000c0030000db6cc0000d126100000032ac92000000c92302, 0xdb6cc0000d936000000032ac00000000cd330000db6cc0000d126100000032ac92000000c92302, 0xdbedc00000000000000032acd3000000000000004924400000000000000032ac92000000000000, 0xdbedc0000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3c1e3ffffe7cfffffffffddf3cfffffff3cfff00180c0000041021000000108410000000410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet125_ok : goodClaim checkedSet125 = true := by decide +kernel

def checkedSet126 : Claim := (5, [0xc40018000204000620000c000062000030000000c40008000204000220000c0000220000300000, 0x60000018020000000621020000006202020000006000001002000000040100000000400200000000, 0x60c060180000000006000000000060000000000060c0601802020008060100080200600200200020, 0x60c46200000000000621020c030000000000000020442200000000000621020c0300000000000000, 0x60c46218020204080800000000000000000000004080401802020008000000000000000000000000, 0xfffbfdfffffffbfff7dffdfffffffdfffdffffff60c0601802020008060100080200600200200020])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet126_ok : goodClaim checkedSet126 = true := by decide +kernel

def checkedSet127 : Claim := (6, [0x8100000000818000000000c00000000004000000810000008180800000000040000000040400, 0x8100000193818000000200c00000000c04000000810000008180800000000040000000040400, 0x120980000013018000000000000000000000000012098000041321800000000000000000000000, 0xd20000000d93000000002200000000008c000000d20000000d1200000000220000000000880000, 0xd2e980000000000000002208c00000000000000040200000000000000000220880000000000000, 0xd2e980000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3d1e7ffffe7cfffffffffdff3ffffffff3ffff0010080000041021000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet127_ok : goodClaim checkedSet127 = true := by decide +kernel

def checkedSet128 : Claim := (4, [0x18ffffffffffffffffff3e7fffffffffffffffff1800000008800000000208000000000840000000, 0x7b000000180000000006000000000018000000007b00000018800000000689000000001840000000, 0xe0000000380000000006c0000000003800000000e0000000300000000004c0000000003000000000, 0xff000000000000000006c98000000000000000002900000000000000000689000000000000000000, 0xff00000038c00000000000000000000000000000d600000038c00000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet128_ok : goodClaim checkedSet128 = true := by decide +kernel

def checkedSet129 : Claim := (6, [0x18000000090000000002300000000009800000001800000009000000000220000000000900000000, 0x18001c0009000066000230001c00000980000b0018001c0009000026000230001400000980000900, 0x18006cc008000060000200000c0000080000030018006cc00900006c100220000e00000900000320, 0x18007ec000000000000230001f000000000000000800364000000000000230001f00000000000000, 0x18007ec00900006e180000000000000000000000100048800900006c100000000000000000000000, 0xe7ffe13ffefffff9e7ffcffffffffffe7fffffff0000600000000048000000000a00000000000220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet129_ok : goodClaim checkedSet129 = true := by decide +kernel

def checkedSet130 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffeffffcfffff9ffff87ffff0ffffe1ffffff000702c040000e0018280200600a02400200a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet130_ok : goodClaim checkedSet130 = true := by decide +kernel

def checkedSet131 : Claim := (6, [0x12400000400071c0000c40000000000000000000000000004000008000044, 0x724000000001b0400000000000000000000000007ad000000001b44000000, 0x7c0000040003e000004c000000000000000000005c0000040003600000480, 0x7ed800000003f7c00000000000000000000000007ed800000003f74000000, 0x7ed80004500000000000000000000000000000007ad000000000000000000, 0xfffffffffffffffffffe3a7fffbafff9e3ffff3f0000000000000000000228000000000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet131_ok : goodClaim checkedSet131 = true := by decide +kernel

def checkedSet132 : Claim := (6, [0x13600132c00071c0000c4000000000000000000001200112c000008000044, 0x736001f00001b0400000000000000000000000007bf001fba001b44000000, 0x7c0001fc0003e000004c000000000000000000005c0000ac0003600000480, 0x7ff800000003f7c00000000000000000000000007ed800000003f74000000, 0x7ff801fff00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc30fff9e3ffff3f0000000000000000000238001430000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet132_ok : goodClaim checkedSet132 = true := by decide +kernel

def checkedSet133 : Claim := (6, [0x8001c0000000066000630001c00000000000b0008001c0000000026000230001400000000000900, 0x29000000000000000007360000000000000000002900000000000000000724000000000000000000, 0x29006cc000000060000600000c0000000000030029006cc00000006c100724000e00000000000320, 0x29007ec000000000000736001f000000000000002900364000000000000736001f00000000000000, 0x29007ec00000006e180000000000000000000000000048800000006c100000000000000000000000, 0xf6ffe13ffffffff9e7ffc9ffffffffffffffffff2000600000000048000500000a00000000000220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet133_ok : goodClaim checkedSet133 = true := by decide +kernel

def checkedSet134 : Claim := (4, [0x5800000000090000000000980000000000000000000000000000000000000000000000000, 0x1b000004800000000090000000000880000000001b00000480800000009009000000088040000000, 0x1f000000000000000090098000000000000000000900000000000000009009000000000000000000, 0x1f00000580c000000000000000000000000000001600000580c00000000000000000000000000000, 0xf8fffffe7fffffffffeffe7ffffffe7fffffffff1800000400800000008008000000080040000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet134_ok : goodClaim checkedSet134 = true := by decide +kernel

def checkedSet135 : Claim := (4, [0x406c0000000c0380000000000000000000000000404c0000000c03000000000, 0x49000000000c980000000000000000000000000000000000000000000000000, 0x496000000004898000000000000000000000000049689000000489840000000, 0x496c98000000000000000000000000000000000049689000000000000000000, 0xfffffffffffffffffbef3e7fffff3e7fffffffff0000000000000000008208000000080840000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet135_ok : goodClaim checkedSet135 = true := by decide +kernel

def checkedSet136 : Claim := (6, [0x40000000000c40000000000000000000000000004000008000044, 0x12400000400071c0000c40000000000000000000000000004000008000044, 0x724000000001b0400000000000000000000000007ad000000001b44000000, 0x7c0000040003e000004c000000000000000000005c0000040003600000480, 0x7ed80004500000000000000000000000000000007ad000000000000000000, 0xfffffffffffffffffffe3a7fffbafff9e3ffff3f0000000000000000000228000000000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet136_ok : goodClaim checkedSet136 = true := by decide +kernel

def checkedSet137 : Claim := (6, [0x1000013000060000340000200001940000080000100000000002000010000020000080000008, 0x7000000003000000000058000000000140000000700000000700000000005800000000034000000, 0x1f001c000000000000003d800030000000000000090014000000000000003d000030000000000000, 0x1f001c0001f000070000000000000000000000001600080001f00005000000000000000000000000, 0xe4ffe3fffeeffff9ffffcbfffffffffe7bffffff0400000000600000000000800000000030000000, 0xffffe3fffffffff9ffffffffffffffffffffffff1f00000001f0000000002d800000000174000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet137_ok : goodClaim checkedSet137 = true := by decide +kernel

def checkedSet138 : Claim := (6, [0x130000060002400000400011c0000040000000000000000200000000004000008000004, 0x1b000000011000000000240000000001040000001b0000000190000000002d000000000144000000, 0x1f00000001f0000000002d80000000017c0000001f00000001f0000000002d800000000174000000, 0x1f0001000000000000002d800005000000000000090000000000000000002d000000000000000000, 0x1f00010001f00000e000000000000000000000001600010001f00000c00000000000000000000000, 0xf8fffeffffcfffff9ffffa7ffffaffffe3ffffff1800000001800000000028000000000140000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet138_ok : goodClaim checkedSet138 = true := by decide +kernel

def checkedSet139 : Claim := (6, [0x1f000000000000000000000000000000000012001fba000000000000, 0xc98000ba0024700000000000000000000000000040800000002430000000, 0x638001c300039600000000000000000000000000238001430000940000000, 0x7c0001f80003e0000000000000000000000000005c0000a80003600000000, 0x7ff801fba00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffff9367ff36dffc79fffffff0000000000000000000012001128000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet139_ok : goodClaim checkedSet139 = true := by decide +kernel

def checkedSet140 : Claim := (6, [0x130000060002400000400011c0000040000000000000000200000000004000008000004, 0x1b000000011000000000240000000001040000001b0000000190000000002d000000000144000000, 0x1f00000001f0000000002d80000000017c0000001f00000001f0000000002d800000000174000000, 0x1f0001000000000000002d800005000000000000090000000000000000002d000000000000000000, 0x1f00010001f00000e000000000000000000000001600010001f00000c00000000000000000000000, 0xf8fffeffffcfffff9ffffa7ffffaffffe3ffffff1800000001800000000028000000000140000000, 0xf8fffefffffffffffffffe7ffffeffffffffffff1800000001800000200028000004000148000004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet140_ok : goodClaim checkedSet140 = true := by decide +kernel

def checkedSet141 : Claim := (6, [0x12400000400071c0000c40000000000000000000000000004000008000044, 0x724000000001b0400000000000000000000000007ad000000001b44000000, 0x7c0000040003e000004c000000000000000000005c0000040003600000480, 0x7ed800000003f7c00000000000000000000000007ed800000003f74000000, 0x7ed80004500000000000000000000000000000007ad000000000000000000, 0x7ed80004500071c0000c400000000000000000007ad000004000008000044, 0xfffffffffffffffffffe3a7fffbafff9e3ffff3f0000000000000000000228000000000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet141_ok : goodClaim checkedSet141 = true := by decide +kernel

def checkedSet142 : Claim := (4, [0x1200000000060000000013000000000008000000120000000002000000001100000000000800, 0x2240000000000000000003000000000000000000224000000000000000000b00000000000000, 0x3e4000000000000000001f000000000000000000364000000000000000001f00000000000000, 0x3e40000000260000000000000000000000000000080000000024000000000000000000000000, 0xffffe1bffffffff9ffffffffffffffffffffffff0000200000000000000000000a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet142_ok : goodClaim checkedSet142 = true := by decide +kernel

def checkedSet143 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70300c1c000000000180180000001c000000000070300c1c0300a0010180580200201c014002000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet143_ok : goodClaim checkedSet143 = true := by decide +kernel

def checkedSet144 : Claim := (6, [0xc98000000024700000000000000000000000000040800000002430000000, 0x638001c000039e0000b0000000000000000000002380014000009c0000900, 0x6c9800c0000386000030000000000000000000007ed800e00003f74000320, 0x7ff800000003ff600000000000000000000000007ed800000003f74000000, 0x7ff801f0000000000000000000000000000000007bf001f00000000000000, 0xffffffffffffffffffffc07ffffffffe09ffffff00000000000000000005c0000a00003600000220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet144_ok : goodClaim checkedSet144 = true := by decide +kernel

def checkedSet145 : Claim := (7, [0x12079f32c8fc000000000000000000000000000012008b12c85c, 0x7edb87f00b3000000000000000000000000000007edbc7fbab3a, 0xe03e01fc0ff00000000000000000000000000000e03600ac06a0, 0xffc001fff0000000000000000000000000000000364001fba000, 0xfffffe0000000000000000000000000000000000c9bf74000000, 0xffffffffffffffffffffffffffff1c39e1c30f0f00000000000000000000000000001c09c143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet145_ok : goodClaim checkedSet145 = true := by decide +kernel

def checkedSet146 : Claim := (6, [0x618c18220c381000004100000000000000000000619c58a22c3810410041080, 0x638000e600081000004500000000000000000000228000e6000000000000000, 0x639060c030000000000000000000000000000000639870e638a000000000000, 0x639c780000081041800000000000000000000000411c5800000810410000000, 0x639c78e63cf00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f87f9ff0feffe7ffafff00000000000000000601c00a02c0800400040080])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet146_ok : goodClaim checkedSet146 = true := by decide +kernel

def checkedSet147 : Claim := (5, [0x606c0320cc080200004040000000000000000000604c02208c0802000040400, 0x6d80032a000810000041000000000000000000002480032a000000000000000, 0x6de00300c00000000000000000000000000000006de8932ac92000000000000, 0x6dec980000081202000000000000000000000000496c9800000812020000000, 0x6dec9b2acd3000000000000000000000000000006de8932ac92000000000000, 0xfffffffffffffffff9e73e7ddf3c7efffffbefff000000000000000000c208108410000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet147_ok : goodClaim checkedSet147 = true := by decide +kernel

def checkedSet148 : Claim := (4, [0x101081800a000000000000000000000000000000100081000800, 0x6010008002000000000000000000000000000000601200a00220, 0x720001b000000000000000000000000000000000320001b00000, 0x7212820000000000000000000000000000000000401200000000, 0xffffffffffffffffffffffffffffedff7dffffff0000000000000000000000000000601200a00220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet148_ok : goodClaim checkedSet148 = true := by decide +kernel

def checkedSet149 : Claim := (3, [0xc0000000000000000000000c0000000000000000e4800000000000000000000e00000, 0xc6000000000000000000001c000000000000000046000000000000000000001400000, 0xe6c0000000000000000000000000000000000000e4800000000000000000000000000, 0xffffffffffff93ffffffffffffffffffffffffff00000000000a0000000000000000000000a00000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet149_ok : goodClaim checkedSet149 = true := by decide +kernel

def checkedSet150 : Claim := (4, [0x18000000000000000000001800000000000000001b100000000000000000001b04000000, 0x190000020000000000000019800008000000000009000002000000000000000980000800, 0x1b100000000000000000001b86000000000000001b100000000000000000001b04000000, 0x1b100002080000000000000000000000000000001b100000000000000000000000000000, 0xfffffffffeeffffdf7fffffffffffffe79ffffff0000000012000000000000000000001200000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet150_ok : goodClaim checkedSet150 = true := by decide +kernel

def checkedSet151 : Claim := (4, [0x402000000000060000000400c000000004000000402000000000020000000400c000000004000, 0x5024000000000000000000000000000000000000502400000000000000000600a000000000000, 0x503400000000000000000600f000000000000000502400000000000000000600a000000000000, 0x50340000001006000000000000000000000000000010000000100400000000000000000000000, 0xfffffcbfffffffff9ffffffffff0ffffffffffff0005000000000000000000006000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet151_ok : goodClaim checkedSet151 = true := by decide +kernel

def checkedSet152 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70301c0c000000000180180200300c000000000030300c0c0100a0010180500200200c004002000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet152_ok : goodClaim checkedSet152 = true := by decide +kernel

def checkedSet153 : Claim := (6, [0x100180050000000000000000000000000000000010018005040, 0xc00200c08104180c50c000000000000000000000400000408104180450c0, 0x600000a0000e100002c500000000000000000000200000a0000200000280000, 0x601c0000000e1061800000000000000000000000401c0000000c10610000000, 0x601c00a02c000000000000000000000000000000601800a0280000000000000, 0xfffffffffffffffff9ff3ffdff3f1efffff3efff0000000000000000000000000000000008004040])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet153_ok : goodClaim checkedSet153 = true := by decide +kernel

def checkedSet154 : Claim := (6, [0x12400000000071c0000c40000000000000000000000000000000008000044, 0x724000000001b0400000000000000000000000007ad000000001b44000000, 0x7c0000000003e000004c000000000000000000005c0000000003600000480, 0x7ed80000000000000000000000000000000000007ad000000000000000000, 0x7ed800000003f7c00000000000000000000000007ed800000003f74000000, 0xfffffffffffffffffffe3a7ffffffff9e3ffff3f0000000000000000000228000000000940000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet154_ok : goodClaim checkedSet154 = true := by decide +kernel

def checkedSet155 : Claim := (6, [0x800c0400000000000000000000000000004000008004040, 0x8102608e00000800c0400000000000000000000000000004000008004040, 0x6188102208200000000000000000000000000000619850a2282000000000000, 0x638000e600002000010c00000000000000000000228000e6000020000108000, 0x6398700000002000a0000000000000000000000041185000000000000000000, 0xffffffffffffffffffc7f8ff9ff1fdfff5ff3fff00000000000000000601800a0280000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet155_ok : goodClaim checkedSet155 = true := by decide +kernel

def checkedSet156 : Claim := (6, [0xc0e000000d80e0000000320cc0000000cc070000c0e000000980c00000002208c00000008c0600, 0xdb0000000d930000000032a000000000cd300000db0000000d120000000032a000000000c92000, 0xdb6cc0000c0060000000300c00000000c0030000db6cc0000d126100000032ac92000000c92302, 0xdbedc00000000000000032acd3000000000000004924400000000000000032ac92000000000000, 0xdbedc0000c006000000032acd3000000c0030000db6cc0000d126100000032ac92000000c92302, 0xdbedc0000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3c1e3ffffe7cfffffffffddf3cfffffff3cfff00180c0000041021000000108410000000410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet156_ok : goodClaim checkedSet156 = true := by decide +kernel

def checkedSet157 : Claim := (6, [0x8120600c04000000000000000000000040800040812020040400, 0xc98200c08120600c04000000000000000000000040800040812020040400, 0x90098000000980600000000000000000000000009209800000098860000000, 0x69000220000e980008c00000000000000000000020000220000200000880000, 0x696c9800000e9b86000000000000000000000000496c9800000c9b860000000, 0x696c9a208c00000000000000000000000000000069689220880000000000000, 0xfffffffffffffffff9ef3e7dff3f1e7ffff3ffff0000000000000000008208000000080840000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet157_ok : goodClaim checkedSet157 = true := by decide +kernel

def checkedSet158 : Claim := (6, [0x6000460000000000000007ec001f000000000000200046000000000000000364001f00000, 0x6080400200000000000006cd800c0030000000006090440240000000000006cdb04e00320, 0x6090000000000000000007edb860000000000000409000000000000000000489b04000000, 0x6090460260000000000000000000000000000000609044024000000000000000000000000, 0x6090460260000000000001c1981c00b0000000006090460260000000000001c0981400900, 0xfffffff9feff9ff9ffffffffffffe13e79ffffff0000000000000000000000000000601200a00220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet158_ok : goodClaim checkedSet158 = true := by decide +kernel

def checkedSet159 : Claim := (6, [0x2000c60000000000000001c1981c00b0000000002000460000000000000001c0981400900, 0xa400000000000000000007edb860000000000000000000000000000000000489b04000000, 0xa400c00000000000000006cd800c003000000000a400e48000000000000006cdb04e00320, 0xa400e6c000000000000000000000000000000000a400e4800000000000000000000000000, 0xa400e6c000000000000007ec001f000000000000a400e6c00000000000000364001f00000, 0xfffffffdbfff93ffffffffffffffe13e79ffffff00000008000a0000000000000000601200a00220])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet159_ok : goodClaim checkedSet159 = true := by decide +kernel

def checkedSet160 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f02c006000000010502400000040008380700600a02c00600a000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet160_ok : goodClaim checkedSet160 = true := by decide +kernel

def checkedSet161 : Claim := (6, [0x13048047000000000000000180040040000000000000000200000000000000008004004, 0x6c110480410000000000000000000000000000006c1905a05100000000000000000000000, 0x7c0005b000000000000000100000050000000000240005a00000000000000000000000000, 0x7c1f000000000000000000100380000000000000581f00000000000000000010030000000, 0x7c1f05b05f0000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff4ff8ffffffffffffeffe7ffafff0000000601805005000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet161_ok : goodClaim checkedSet161 = true := by decide +kernel

def checkedSet162 : Claim := (4, [0x120007c00013000000000000000000000000000012000240001200000000000000000000000000, 0x12120886c000000000000000000000000000000012120886c0801201000000000000000000000000, 0x16000007c0c000000000000000000000000000001600000580c00000000000000000000000000000, 0x16120980000000000000000000000000000000000000000000000000000000000000000000000000, 0xf9fdfe7e3ffffcffffffffffffffffffffffffff1010080600801001000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet162_ok : goodClaim checkedSet162 = true := by decide +kernel

def checkedSet163 : Claim := (4, [0x19391c000000000000000000000000000000000008190c00000000000000000000000, 0xc50e58000000000000000000000000000000000045025000000000000000000000000, 0xf80f800000000000000000000000000000000000b80d8000000000000000000000000, 0xfdb0000000000000000000000000000000000000f5a00000000000000000000000000, 0xfffffffffff26c1e7fffffffffffffffffffffff0000000000000000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet163_ok : goodClaim checkedSet163 = true := by decide +kernel

def checkedSet164 : Claim := (6, [0x180040040000000000000000200000000000000008004004, 0x13048047000000000000000180040040000000000000000200000000000000008004004, 0x6c110480410000000000000000000000000000006c1905a05100000000000000000000000, 0x7c0005b000000000000000100000050000000000240005a00000000000000000000000000, 0x7c1f000000000000000000100380000000000000581f00000000000000000010030000000, 0xfffffffe3fcff4ff8ffffffffffffeffe7ffafff0000000601805005000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet164_ok : goodClaim checkedSet164 = true := by decide +kernel

def checkedSet165 : Claim := (6, [0x13068065000000000001001800200080000000000002002000000000000100080020008, 0x1c0300b0050000000000000000000000000000001c0700b00d00000000000000000000000, 0x7c0007b000000000000001c00000300000000000240007a00000000000000140000030000, 0x7c1f000000000000000001c01c00000000000000581f00000000000000000080140000000, 0xfffffff93eef97f9efffffffffffe3fe7fffffff0000000100600100c00000000000000000000000, 0xffffffffffffffffffffffffffffe3fe7fffffff00000007c1f05b05d00000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet165_ok : goodClaim checkedSet165 = true := by decide +kernel

def checkedSet166 : Claim := (6, [0xfdd0000000000000000000000000000000000081fdd00000000000000000000000, 0x26c1c5000000000000000013280000000000000002400000000000000000001128000, 0xc70e5800000000000000001c300000000000000047025000000000000000001430000, 0xf80f8000000000000000001f8000000000000000b80d8000000000000000000a80000, 0xfffffffffff19393effffffffffffffffe0fffff0000000000008190c00000000000000000000000, 0xfffffffffffffffffffffffffffffffffe0fffff00000000000fdbfdd00000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet166_ok : goodClaim checkedSet166 = true := by decide +kernel

def checkedSet167 : Claim := (6, [0x2481c7000000000000000000040c40000000000000000200000000000000000004044, 0xe486c10000000000000000000000000000000000f5a6d100000000000000000000000, 0xf80f80000000000000000000404c000000000000b80d8000000000000000000040480, 0xfdb0000000000000000000004500000000000000f5a00000000000000000000000000, 0xfdbfdf0000000000000000000000000000000000fdbfdd00000000000000000000000, 0xfffffffffffc74e78ffffffffffffffffffbaf3f0000000000045025000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet167_ok : goodClaim checkedSet167 = true := by decide +kernel

def checkedSet168 : Claim := (6, [0x40028000000000002000a00c000000000000000040028000000000002000a00c004, 0x100640628000000000012018a02c00c000000000000240228000000000012008a02c00c, 0x6000074000000000000001e000003c0000000000200007400000000000000160000038000, 0x6018000000000000000001e01ca0000000000000401800000000000000000080140000000, 0x6018074072800000000000000000000000000000601805005000000000000000000000000, 0xfffffff9feff9bf9f7ffffffffffe1fe7dffffff0000000000000000200000000000000008004004, 0xffffffffffffffffffffffffffffe1fe7dffffff0000000601805005200000000000000008004004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet168_ok : goodClaim checkedSet168 = true := by decide +kernel

def checkedSet169 : Claim := (6, [0x1f008100000000000002402080000000000000001fba818, 0xd1200000000000000000000c9200000000000000f5a00000000000000000000e92000, 0xe6c02080000000000000001f0081000000000000f7e02080000000000000001fba818, 0xf0000000000000000000001f8085000000000000b0000000000000000000000a80000, 0xf7e00000000000000000001fbe00000000000000f7e00000000000000000001fba000, 0xf7e0228000000000000000000000000000000000f5a00000000000000000000000000, 0xfffffffffffcf1ffd7ffffffffffffffffc71faf0000000000047002000000000000000001430808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet169_ok : goodClaim checkedSet169 = true := by decide +kernel

def checkedSet170 : Claim := (4, [0x120304c10000000000000000000000000000000012010441000000000000000, 0x228000c000000000000000000000000000000000228002c0000000000000000, 0x3e8007c000000000000000000000000000000000368007c0000000000000000, 0x3ea300000000000000000000000000000000000008220000000000000000000, 0xfffffffffffffffffe17cfffffffffffffffffff0000000000000000020000280000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet170_ok : goodClaim checkedSet170 = true := by decide +kernel

def checkedSet171 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70301c1c000030000180000000000c000000000070301c1c0300b0050180500200200c004002000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet171_ok : goodClaim checkedSet171 = true := by decide +kernel

def checkedSet172 : Claim := (3, [0xc006000000000000000000000000000000000000d1261000000000000000000000000, 0xd80e000000000000000000000000000000000000980c0000000000000000000000000, 0xd930000000000000000000000000000000000000d1200000000000000000000000000, 0xfffffffffffe7cffffffffffffffffffffffffff0000000000041021000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet172_ok : goodClaim checkedSet172 = true := by decide +kernel

def checkedSet173 : Claim := (6, [0x1000010000060000300000200001800000080000100000000002000010000020000080000008, 0x1b001cc0010000060000300000000001800000001b001cc0018000070000390000320001c000000a, 0x1f00000001c000000000398000000001e00000001f00000001c00000000029800000000160000000, 0x1f001dc0000000000000398000330000000000000900144000000000000039000032000000000000, 0x1f001dc001c000078000000000000000000000001600098001c00005800000000000000000000000, 0xf8fffe3ffffffffffffffe7ffffcffffffffffff18001c00018000070000380000300001c000000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet173_ok : goodClaim checkedSet173 = true := by decide +kernel

def checkedSet174 : Claim := (6, [0x10060060000000000001001800200080000000000002002000000000000100080020008, 0x6c10060060000000000001cc18000000000000006c18072070000000000001cc1c003200a, 0x7c00073000000000000001dc0000330000000000240007200000000000000144000032000, 0x7c1c000000000000000001dc1e00000000000000581c00000000000000000098160000000, 0x7c1c0730780000000000000000000000000000007c1c05305800000000000000000000000, 0xfffffffe3ffffcfffffffffffffffe3fffffcfff00000006018070070000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet174_ok : goodClaim checkedSet174 = true := by decide +kernel

def checkedSet175 : Claim := (7, [0x12079f32c8fc000000000000000000000000000012008b12c85c, 0x7edb87f00b3000000000000000000000000000007edbc7fbab3a, 0xffc001fff0000000000000000000000000000000364001fba000, 0xfffffe0000000000000000000000000000000000c9bf74000000, 0xffffffffffffffffffffffffffff1c39e1c30f0f00000000000000000000000000001c09c143090a, 0xffffffffffffffffffffffffffff1e01fe03c00f00000000000000000000000000001e09cb53c95e])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet175_ok : goodClaim checkedSet175 = true := by decide +kernel

def checkedSet176 : Claim := (6, [0x2000000000028000200000c00000a000000000002000000000028000200000c00000a000004, 0x12000100000628003200002c00018a00000c000012000000000228001200002c00008a00000c, 0x180000000180000000003a0000000001ca0000001800000001800000000028000000000140000000, 0x18001e000000000000003a00003c000000000000080016000000000000003a000038000000000000, 0x18001e00018000072800000000000000000000001000080001800005000000000000000000000000, 0xe7ffe1fffefffff9f7ffcdfffffffffe7dffffff0000000000000000200000000004000008000004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet176_ok : goodClaim checkedSet176 = true := by decide +kernel

def checkedSet177 : Claim := (4, [0x3800060000600001c0000000001c00000000000038000200006000014000000000140000000000, 0x18180c060000000000c0000000000c000000000018180c060100400400c0200000000c0100000000, 0x18381c000000000001c030000000000000000000082814000000000001c030000000000000000000, 0x18381c06010060060000000000000000000000001010080601004004000000000000000000000000, 0xffc7e3ffffff9ff9ffffffffffffffffffffffff1800000401000000008020000000080100000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet177_ok : goodClaim checkedSet177 = true := by decide +kernel

def checkedSet178 : Claim := (6, [0x1800000400c000000080080000000800600000001800000400800000008008000000080040000000, 0x1b0300c4c000000000980000000008c0000000001b0300c4c080020000980900200208c040002000, 0x1f000005c0c0000000980980000009c0600000001f00000580c00000009009800000098060000000, 0x1f0301c0000000000098098020030000000000000901004000000000009809002002000000000000, 0x1f0301c5c0c0030000000000000000000000000016020185c0c00300000000000000000000000000, 0xe0fffe3fff3ffffffffff67ffffcffff9fffffff0003000040000200000800002000004000002000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet178_ok : goodClaim checkedSet178 = true := by decide +kernel

def checkedSet179 : Claim := (6, [0x12000130000628003600002c00019e00000c000012000000000228001200002c00008a00000c, 0x70002000030000028000780000c00001e000000070002000070000028000780000c00003e000004, 0x1f00000001f0000000003f8000000001fe0000001f00000001f0000000002d800000000174000000, 0x1f001e000000000000003f80003c000000000000090016000000000000003f000038000000000000, 0x1f001e0001f000072800000000000000000000001600080001f00005000000000000000000000000, 0xe4ffe1fffeeffff9f7ffc9fffffffffe79ffffff0400000000600000200000800004000038000004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet179_ok : goodClaim checkedSet179 = true := by decide +kernel

def checkedSet180 : Claim := (6, [0x21060c43080000000000000000000000000000002002044108000000000000, 0x601c00e03c0e000000c000000000000000000000601c00a02c0e000000c0000, 0x639060c030060c00000000000000000000000000639870e638a60c000082000, 0x639c7800000e1c00000000000000000000000000411c5800000c18000000000, 0x639c78e63cb00000000000000000000000000000639870e638a000000000000, 0xfffffffffffffffffffe387ffc34ffffffffffff00000000000000000228000e6000204000082000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet180_ok : goodClaim checkedSet180 = true := by decide +kernel

def checkedSet181 : Claim := (6, [0x18001c0009000026000630001c0000098000090018001c0009000026000230001400000980000900, 0x39000000090000000007360000000009820000003900000009000000000724000000000900000000, 0x39002c4008000020000600000c0000080000010039002c4009000024000724000e00000900000100, 0x39003e4000000000000736001f000000000000002900364000000000000736001f00000000000000, 0x39003e40090000260800000000000000000000001000080009000024000000000000000000000000, 0xe6ffe1bffefffff9f7ffc9fffffffffe7dffffff2000200000000000000500000a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet181_ok : goodClaim checkedSet181 = true := by decide +kernel

def checkedSet182 : Claim := (6, [0x1010080600c010018000000000000000000000001010080600801001000000000000000000000000, 0x131308c6c000000000180000000000c000000000131308c6c080120100180100200200c000002000, 0x17000007c0c0000000180180000001c0000000001700000580c00000001001800000018000000000, 0x171309c0000000000018018020030000000000000101004000000000001801002002000000000000, 0x171309c7c0c0130180000000000000000000000016120987c0c01301800000000000000000000000, 0xe8fff63fff3ffffe7ffffe7ffffcffffffffffff0013000240001200000800002000004000002000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet182_ok : goodClaim checkedSet182 = true := by decide +kernel

def checkedSet183 : Claim := (6, [0x1306c0678000000000012018a02c00c000000000000240228000000000012008a02c00c, 0x1c0300f0078000000000002000a00c00000000001c0700f00f8000000000002000a00c004, 0x7c0007f000000000000001e000003c0000000000240007e00000000000000160000038000, 0x7c1f000000000000000001e01ca0000000000000581f00000000000000000080140000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffff93eef93f9e7ffffffffffe1fe7dffffff0000000100600100e00000000000000008004004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet183_ok : goodClaim checkedSet183 = true := by decide +kernel

def checkedSet184 : Claim := (4, [0x1000010000060000300010000001800008000000100000000002000010001000000080000800, 0x18000000090000000002300000000009800000001800000009000000000220000000000900000000, 0x18001c00000000000002300014000000000000000800140000000000000230001400000000000000, 0x18001c00090000260000000000000000000000001000080009000024000000000000000000000000, 0xe7ffe3fffefffff9ffffcffffffffffe7fffffff0000000000000000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet184_ok : goodClaim checkedSet184 = true := by decide +kernel

def checkedSet185 : Claim := (4, [0x10060060000000000001001800200080000000000002002000000000000100080020008, 0x6000070000000000000001c00000300000000000200007000000000000000140000030000, 0x6018000000000000000001c01c00000000000000401800000000000000000080140000000, 0x6018070070000000000000000000000000000000601805005000000000000000000000000, 0xfffffff9feff9ff9ffffffffffffe3fe7fffffff0000000000000000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet185_ok : goodClaim checkedSet185 = true := by decide +kernel

def checkedSet186 : Claim := (6, [0x2c00000000240001e00001c00012000002c000002c00000000240001600001c000120000028000, 0x80000000000000001e03a00000012008a0000000800000000000000008028000000000000000000, 0x80804000000000000c008008010000000000000080804000000000000c028008010000000000000, 0x82c16000000000001e03a01c03c000000000000082c16000000000001e03a01c038000000000000, 0x82c16000000240209e032000000120082000000082c16000000240209e03a01c038120082028008, 0x82c1600000024022800000000000000000000000000000000000000000000000000000000000000, 0xfffbfdfffffffbffd7dffdffbff3fdfff5ff3fff082814000000200201c038018030100080020008])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet186_ok : goodClaim checkedSet186 = true := by decide +kernel

def checkedSet187 : Claim := (6, [0x1000013000060000340000200001940000080000100000000002000010000020000080000008, 0x7000000000000000000018000000000000000000700000000700000000005800000000034000000, 0x1f00000001f0000000003d8000000001f40000001f00000001f0000000002d800000000174000000, 0x1f001c000000000000003d800030000000000000090014000000000000003d000030000000000000, 0x1f001c0001f000070000000000000000000000001600080001f00005000000000000000000000000, 0xe4ffe3fffeeffff9ffffcbfffffffffe7bffffff0400000000600000000000800000000030000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet187_ok : goodClaim checkedSet187 = true := by decide +kernel

def checkedSet188 : Claim := (6, [0x40028000000000002000a00c000000000000000040028000000000002000a00c004, 0x100640628000000000012018a02c00c000000000000240228000000000012008a02c00c, 0x6000074000000000000001e000003c0000000000200007400000000000000160000038000, 0x6018000000000000000001e01ca0000000000000401800000000000000000080140000000, 0x6018074072800000000000000000000000000000601805005000000000000000000000000, 0xfffffff9feff9bf9f7ffffffffffe1fe7dffffff0000000000000000200000000000000008004004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet188_ok : goodClaim checkedSet188 = true := by decide +kernel

def checkedSet189 : Claim := (6, [0x13068065000000000001001800200080000000000002002000000000000100080020008, 0x1c000030000000000000000000000000000000001c0700b00d00000000000000000000000, 0x7c0007b000000000000001c00000300000000000240007a00000000000000140000030000, 0x7c1f000000000000000001c01c00000000000000581f00000000000000000080140000000, 0x7c1f07b07d0000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffff93eef97f9efffffffffffe3fe7fffffff0000000100600100c00000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet189_ok : goodClaim checkedSet189 = true := by decide +kernel

def checkedSet190 : Claim := (6, [0x2000000000028000000000c000000000000000002000000000028000000000c000000004000, 0x4020000020c002800000c400c00000030c000000402000000040028000004400c00000010c000, 0xc00000000300000000000e000000000038000000c00000000300000000000a0000000000280000, 0xc70200000000000000000e600c00000000000000450200000000000000000e6008000000000000, 0xc7020000030e002800000000000000000000000082000000030a00000000000000000000000000, 0xff38fdfffffdf3fff7fffff3ffffffffffcfffff0000000000000000200000000004000000004000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet190_ok : goodClaim checkedSet190 = true := by decide +kernel

def checkedSet191 : Claim := (6, [0x601800e038000000000000000000000000000000601800a0280000000000000, 0x6188102208200000000000000000000000000000619850a2282000000000000, 0x639060c030002000200000000000000000000000639870e638a020002008000, 0x6398700000002000a0000000000000000000000041185000000000000000000, 0x639870e638e00000000000000000000000000000639870e638a000000000000, 0xfffffffffffffffffffe78fffc71fffff5ffffff00000000000000000228000e6000020000008000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet191_ok : goodClaim checkedSet191 = true := by decide +kernel

def checkedSet192 : Claim := (6, [0x21000008400000000639060000002240000000002100000000000000041104000000000000000000, 0x21002240000000000001060003000000000000002100224000000000041106000300000000000000, 0x21c320484000000006180000000020400000000021c3204840020800061904080200204000200000, 0x21c72240000000000639060c030000000000000021452240000000000639060c0300000000000000, 0x21c7224840020c000000000000000000000000000082000840020800000000000000000000000000, 0xfef8fdbfbffff3ffffc7f9fffffffdbfffffffff20c0200800020000060100080200200000200000, 0xfffbfdfffffff3ffffdff9fffffffdffffffffff21c3204840020800061904080200204000200000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet192_ok : goodClaim checkedSet192 = true := by decide +kernel

def checkedSet193 : Claim := (6, [0x8000000182102000000260cc0000000ce0c000008000000080102000000000440000000440c0, 0xc3e000000182000000000220c00000000c200000c3e00000038a180000000a22c00000002c20a0, 0xc7000000038e000000000e60000000003ce00000c7000000030e000000000e600000000038a000, 0xc7e200000000000000000e63cc00000000000000452200000000000000000e6388000000000000, 0xc7e20000038e182800000000000000000000000082c00000038a18000000000000000000000000, 0xfff8fdfffffff1ffd7ffffff9ff3ffffffff1fff00c0e000000380180000000a02c00000002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet193_ok : goodClaim checkedSet193 = true := by decide +kernel

def checkedSet194 : Claim := (6, [0x6c98008c000386000060000000000000000000007ed800ac0003f740006a0, 0x736001b00001b86000a3000000000000000000007bf001ba8001bc6000a38, 0x7c0001bc0003e00000ef000000000000000000005c0000ac00036000006a0, 0x7ff800000003ffe00000000000000000000000007ed800000003f74000000, 0x7ff801bec00000000000000000000000000000007bf001ba8000000000000, 0xfffffffffffffffffffe387ffc33fff9e1ffff0f00000000000000000002380010200009c0000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet194_ok : goodClaim checkedSet194 = true := by decide +kernel

def checkedSet195 : Claim := (6, [0xc10260ce8004080cc0c000000000000000000000400000448004080440c0, 0x618c10220c2e000000c000000000000000000000619c50a22c2e006002c00a0, 0x638000e6000e200003cc00000000000000000000228000e6000220000388000, 0x639c7000000e2060a00000000000000000000000411c5000000c00600000000, 0x639c70e63ce00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f8ff9ff1fdfff5ff3fff00000000000000000601c00a02c0e006002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet195_ok : goodClaim checkedSet195 = true := by decide +kernel

def checkedSet196 : Claim := (6, [0x8100000183106000000240cc0000000cc0c000008100000081106000000000440000000440c0, 0xc2e180000183000000000200c00000000c000000c2e18000038b185000000a02c00000002c00a0, 0xc6000000038f000000000e40000000003cc00000c6000000030e000000000e4000000000388000, 0xc6e380000000000000000e43cc00000000000000442200000000000000000e4388000000000000, 0xc6e38000038f187800000000000000000000000082c18000038b18500000000000000000000000, 0xfff9fc7ffffff0ff87ffffffbff3ffffffff3fff00c0e000000380180000000a02c00000002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet196_ok : goodClaim checkedSet196 = true := by decide +kernel

def checkedSet197 : Claim := (6, [0x8000000180102000000240cc0000000cc0c000008000000080102000000000440000000440c0, 0xc0e000000180000000000200c00000000c000000c0e000000380180000000a02c00000002c00a0, 0xc40000000384000000000e40000000003cc00000c40000000304000000000e4000000000388000, 0xc4e200000000000000000e43cc00000000000000442200000000000000000e4388000000000000, 0xc4e200000384182800000000000000000000000080c00000038018000000000000000000000000, 0xfffbfdfffffffbffd7ffffffbff3ffffffff3fff00c0e000000380180000000a02c00000002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet197_ok : goodClaim checkedSet197 = true := by decide +kernel

def checkedSet198 : Claim := (6, [0xc00240cc8004080cc0c000000000000000000000400000448004080440c0, 0x600c00200c0e000000c000000000000000000000601c00a02c0e006002c00a0, 0x620000e4000e200003cc00000000000000000000220000e4000220000388000, 0x621c2000000e2060a00000000000000000000000401c0000000c00600000000, 0x621c20e43cc00000000000000000000000000000621820e4388000000000000, 0xffffffffffffffffffdffdffbff3fdfff5ff3fff00000000000000000601c00a02c0e006002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet198_ok : goodClaim checkedSet198 = true := by decide +kernel

def checkedSet199 : Claim := (3, [0xcc00000000000000000000000000000000000000cc000000001000000000012000000000002, 0xdc0000000000000000000130000000000000000044000000000000000000012000000000000, 0xdc0000000018000000000000000000000000000098000000001800000000000000000000000, 0xfffffe3ffffffffffffffffffffcffffffffffff00000c0000000001000000000010000000000002])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet199_ok : goodClaim checkedSet199 = true := by decide +kernel

def checkedSet200 : Claim := (4, [0x4a080000000000000000000a30000000000000004a080000000000000000000a38, 0xc000000000000000000000060000000000000000d80000000000000000000006a0, 0xd8000000000000000000000ef000000000000000d80000000000000000000006a0, 0xda28000000000000000000000000000000000000d8000000000000000000000000, 0xffffffffffffffe7d7ffffffffffffffffffff0f0000000000000002000000000000000000000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet200_ok : goodClaim checkedSet200 = true := by decide +kernel

def checkedSet201 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30700c0c0000c0000380000000002c000000000030700c0c0100e0010380500600202c00400a000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet201_ok : goodClaim checkedSet201 = true := by decide +kernel

def checkedSet202 : Claim := (6, [0x26c000000000000000000013280000000000000002400000000000000000001128000, 0xe6c60000000000000000001f0030000000000000f7e61000000000000000001fba302, 0xf80e0000000000000000001fc070000000000000b80c0000000000000000000ac0600, 0xfff00000000000000000001ffb00000000000000f7e00000000000000000001fba000, 0xfffe180000000000000000000000000000000000fdbe1800000000000000000000000, 0xfffffffffffc70ffffffffffffffffffffc34fff0000000000047021000000000000000001430102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet202_ok : goodClaim checkedSet202 = true := by decide +kernel

def checkedSet203 : Claim := (4, [0x380000000c6000000000700000000001c000000038000000046000000000500000000001400000, 0xdb0000000c0000000000300000000000c0000000db0000000e4800000000380000000000e00000, 0xff0000000000000000007c0000000000000000006d0000000000000000007c0000000000000000, 0xff0000000e6c0000000000000000000000000000920000000e4800000000000000000000000000, 0xffc0ffffffff93ffffffffffffffffffffffffff00c00000000a0000000000280000000000a00000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet203_ok : goodClaim checkedSet203 = true := by decide +kernel

def checkedSet204 : Claim := (6, [0xc00000000980000000002200000000008c000000c0000000090000000000220000000000880000, 0xc06cc000080060000000200c0000000080030000c06cc000090061000000220c92000000880302, 0xc0e000000980e0000000220cc00000008c070000c0e000000980c00000002208c00000008c0600, 0xc0edc000000000000000220cd30000000000000040244000000000000000220c92000000000000, 0xc0edc0000980e18000000000000000000000000080c980000980e1800000000000000000000000, 0xff3f1e3ffffe7ffffffffffdff3cfffffff3ffff00000c0000000021000000000410000000000102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet204_ok : goodClaim checkedSet204 = true := by decide +kernel

def checkedSet205 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000, 0xf8fffe3e3fcfffffffc7f87ffffcfc3fe1ffffff0007020040000e0028280200600c02400a00e000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet205_ok : goodClaim checkedSet205 = true := by decide +kernel

def checkedSet206 : Claim := (6, [0xd1200000000000000000000c9200000000000000f5a00000000000000000000e92000, 0xe6c02080000000000000001f0081000000000000f7e02080000000000000001fba818, 0xf0000000000000000000001f8085000000000000b0000000000000000000000a80000, 0xf7e00000000000000000001fbe00000000000000f7e00000000000000000001fba000, 0xf7e0228000000000000000000000000000000000f5a00000000000000000000000000, 0xfffffffffffcf1ffd7ffffffffffffffffc71faf0000000000047002000000000000000001430808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet206_ok : goodClaim checkedSet206 = true := by decide +kernel

def checkedSet207 : Claim := (6, [0x80e000000d80e0000000000cc00000000007000080e000000980c00000000008c0000000000600, 0x920000000d930000000000000000000000000000920000000d1200000000000000000000000000, 0x926cc0000c0060000000000c0000000000030000926cc0000d1261000000000c92000000000302, 0x92edc000000000000000000cd30000000000000000244000000000000000000c92000000000000, 0x92edc0000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff7d1e3ffffe7cffffffffffff3cffffffffffff00100c0000041021000000000410000000000102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet207_ok : goodClaim checkedSet207 = true := by decide +kernel

def checkedSet208 : Claim := (6, [0xd93e1800000000000000000c9200000000000000fdbfdd00000000000000000e92000, 0xe6c6e180000000000000001f0081000000000000f7e6f180000000000000001fba818, 0xf80f8000000000000000001f8085000000000000b80d8000000000000000000a80000, 0xfff00000000000000000001fbe00000000000000f7e00000000000000000001fba000, 0xffffff8000000000000000000000000000000000fdbfdd00000000000000000000000, 0xfffffffffffc70e787ffffffffffffffffc71faf0000000000047027000000000000000001430808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet208_ok : goodClaim checkedSet208 = true := by decide +kernel

def checkedSet209 : Claim := (4, [0x4000000020c000000000c40000000003080000004000000000400000000044000000000108000, 0xc00000000300000000000e000000000038000000c00000000300000000000a0000000000280000, 0xc70000000000000000000e600000000000000000450000000000000000000e6000000000000000, 0xc7000000030e000000000000000000000000000082000000030a00000000000000000000000000, 0xff38fffffffdf3fffffffff3ffffffffffcfffff0000000000000000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet209_ok : goodClaim checkedSet209 = true := by decide +kernel

def checkedSet210 : Claim := (4, [0x2000c6000000000000000140001c000000000000200046000000000000000140001400000, 0xa400000000000000000003640000000000000000000000000000000000000000000000000, 0xa400c0000000000000000244000c000000000000a400e4800000000000000244000e00000, 0xa400e6c000000000000000000000000000000000a400e4800000000000000000000000000, 0xfffffffdbfff93ffffffffffffffe9bfffffffff00000008000a0000000000000000200000a00000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet210_ok : goodClaim checkedSet210 = true := by decide +kernel

def checkedSet211 : Claim := (6, [0x1020020000002600c00000008e0400000000000000000200000000004000000004040, 0xc300000001020000000002200000000008200000c3000000030a000000000a2000000000282000, 0xc7000000030e000000000e600000000038e00000c7000000030e000000000e600000000038a000, 0xc70200000000000000000e610c00000000000000450200000000000000000e6108000000000000, 0xc7020000030e002800000000000000000000000082000000030a00000000000000000000000000, 0xfff8fdfffffff1ffd7ffffff9ff3ffffffff1fff00c00000000300000000000a0000000000280000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet211_ok : goodClaim checkedSet211 = true := by decide +kernel

def checkedSet212 : Claim := (6, [0x8000000182100000000260c00000000ca0800000800000008010000000000040000000040080, 0x7000000000e0000000000600000000000a0000007000000000e0000000004600000000010a000, 0xc7e000000000000000000e62c000000000000000452000000000000000000e6280000000000000, 0xc7e00000038e180000000000000000000000000082c00000038a18000000000000000000000000, 0xff3c1ffffffe7dfffffffffddf3ffffffff3dfff0004000000000400000000044000000000108000, 0xffff1fffffffffffffffffffff3fffffffffffff00c7000000030e000000000e600000000038a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet212_ok : goodClaim checkedSet212 = true := by decide +kernel

def checkedSet213 : Claim := (6, [0xe180000000000000000000000000000000000081fdd00000000000000000000000, 0x26c1c5000000000000000013280000000000000002400000000000000000001128000, 0xc70e5800000000000000001c300000000000000047025000000000000000001430000, 0xf80f8000000000000000001f8000000000000000b80d8000000000000000000a80000, 0xffffdd0000000000000000000000000000000000fdbfdd00000000000000000000000, 0xfffffffffff19393effffffffffffffffe0fffff0000000000008190c00000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet213_ok : goodClaim checkedSet213 = true := by decide +kernel

def checkedSet214 : Claim := (4, [0x1600000000c000000000000000000000000000001600000008c00000000000000000000000000000, 0x19ffffffffffffffffff3fffffffffffffffffff1000000008800000000000000000000000000000, 0x8400000020c000000000c00000000020000000008400000020400000000040000000002000000000, 0xf6000000000000000004c00000000000000000002000000000000000000480000000000000000000, 0xf600000038c00000000000000000000000000000d600000038c00000000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet214_ok : goodClaim checkedSet214 = true := by decide +kernel

def checkedSet215 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30300c0c010000000380600000002c006000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet215_ok : goodClaim checkedSet215 = true := by decide +kernel

def checkedSet216 : Claim := (6, [0x40028000000000000000000c000000000000000040028000000000000000000c004, 0x100640628000000000010018002c00c000000000000240228000000000010008002c00c, 0x6000074000000000000001c000003c0000000000200007400000000000000140000038000, 0x6018000000000000000001c01c00000000000000401800000000000000000080140000000, 0x6018074072800000000000000000000000000000601805005000000000000000000000000, 0xfffffff9feff9bf9f7ffffffffffe3fe7fffffff0000000000000000200000000000000000004004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet216_ok : goodClaim checkedSet216 = true := by decide +kernel

def checkedSet217 : Claim := (6, [0x8102608e00000000c0400000000000000000000000000004000000004040, 0x6188102208200000000000000000000000000000619850a2282000000000000, 0x638000e600000000010c00000000000000000000228000e6000000000108000, 0x639870000000000000000000000000000000000041185000000000000000000, 0x639870e638e00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f8ff9ff1ffffffff3fff00000000000000000601800a0280000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet217_ok : goodClaim checkedSet217 = true := by decide +kernel

def checkedSet218 : Claim := (6, [0x1200000000060000000013000000000008000000120000000002000012001100000080000800, 0x1200010000060001360013000001800008000000120000000002000012001100000080000800, 0x21002240000000000001060003000000000000002100224000000000000506000b00000000000000, 0x39000000090000000007360000000009800000003900000009000000000724000000000900000000, 0x39003e4000000000000736001f000000000000002900364000000000000736001f00000000000000, 0x39003e40090000260000000000000000000000001000080009000024000000000000000000000000, 0xe6ffe1bffefffff9ffffc9fffffffffe7fffffff2000200000000000000500000a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet218_ok : goodClaim checkedSet218 = true := by decide +kernel

def checkedSet219 : Claim := (6, [0x6c9800c9200386000000000000000000000000007ed800e92003f74000000, 0x736001f00001b8600081000000000000000000007bf001fba001bc6000818, 0x7c0001f80003e0000085000000000000000000005c0000a80003600000000, 0x7ff800000003ffe00000000000000000000000007ed800000003f74000000, 0x7ff801fbe00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe387ffc71fff9e1ffffaf00000000000000000002380014300009c0000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet219_ok : goodClaim checkedSet219 = true := by decide +kernel

def checkedSet220 : Claim := (6, [0x1b001200011000020800360000000001860000001b0012000190000208003f0000280001c6000008, 0x1f00000000c000000000098000000000600000001f00000001f0000000002d800000000174000000, 0x1f00000001f0000000003f8000000001fe0000001f00000001f0000000002d800000000174000000, 0x1f0012000000000000003f80002c000000000000090012000000000000003f000028000000000000, 0x1f00120001f000022800000000000000000000001600000001f00000000000000000000000000000, 0xf8fffdffffcfffffd7fff87ffff3ffffe1ffffff18001000018000020000380000200001c0000008])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet220_ok : goodClaim checkedSet220 = true := by decide +kernel

def checkedSet221 : Claim := (4, [0x801004000800000000000280060000000000000080100400080000000000028006008000, 0x1800000000000000000000180000000000000000180300000000000000000018014000000, 0x18030000000000000000003801e0000000000000180300000000000000000018014000000, 0x1803004002800000000000000000000000000000180300000000000000000000000000000, 0xffffffffffcfffffd7ffffffffffffffe1ffffff0000000000000400000000000000020000008000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet221_ok : goodClaim checkedSet221 = true := by decide +kernel

def checkedSet222 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c000000000380600000000c000000000030702c0c0100a0010380700600a00c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet222_ok : goodClaim checkedSet222 = true := by decide +kernel

def checkedSet223 : Claim := (4, [0x1c630701c00000000000000000000000000000001c230501400000000000000, 0x6de00300c00000000000000000000000000000006df24380e00000000000000, 0x7f8007c000000000000000000000000000000000368007c0000000000000000, 0x7ff360000000000000000000000000000000000049724000000000000000000, 0xfffffffffffffffffe07c9ffffffffffffffffff0000000000000000060500280a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet223_ok : goodClaim checkedSet223 = true := by decide +kernel

def checkedSet224 : Claim := (6, [0x60000220000edc000cd30000000000000000000020000220000244000c92000, 0x604002008006cd800c0030000000000000000000604802208806cd840c92302, 0x604c0000000edf86000000000000000000000000404c0000000c9b860000000, 0x604c02208c00000000000000000000000000000060480220880000000000000, 0x604c02208c0e03800cc070000000000000000000604c02208c0e030008c0600, 0xfffffffffffffffff9ff3ffdff3f1e3ffff3cfff00000000000000000000000000000c0840410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet224_ok : goodClaim checkedSet224 = true := by decide +kernel

def checkedSet225 : Claim := (6, [0x406c0000000e03800cc070000000000000000000404c0000000e030008c0600, 0x49000000000edc000cd30000000000000000000000000000000244000c92000, 0x496000000006cd800c0030000000000000000000496890000006cd840c92302, 0x496c98000000000000000000000000000000000049689000000000000000000, 0x496c9800000edf86000000000000000000000000496c9800000c9b860000000, 0xfffffffffffffffffbef3e7fffff1e3ffff3cfff00000000000000000082080000000c0840410102])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet225_ok : goodClaim checkedSet225 = true := by decide +kernel

def checkedSet226 : Claim := (7, [0x380780600f02001e00c000010502400000040028380700600e02000a00c000, 0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet226_ok : goodClaim checkedSet226 = true := by decide +kernel

def checkedSet227 : Claim := (6, [0x689000c9200000000000000000000000000000007ad000e92000000000000, 0x736001f0000008200081000000000000000000007bf001fba000082000818, 0x780001f800000000008500000000000000000000580000a80000000000000, 0x7bf00000000008a00000000000000000000000007ad000000000000000000, 0x7bf001fbe00000000000000000000000000000007bf001fba000000000000, 0xfffffffffffffffffffe78fffc71fffff5ffffaf0000000000000000000238001430000080000808])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet227_ok : goodClaim checkedSet227 = true := by decide +kernel

def checkedSet228 : Claim := (4, [0x450000000000000638000c000000000000000000450000000000000228000c0000000000000000, 0x21000000000000000639060000000000000000002100000000000000041104000000000000000000, 0x21412040000000000618000000000000000000002141204000000000061904080200000000000000, 0x21452240000000000000000000000000000000000000000000000000000000000000000000000000, 0xfefafdbfffffffffffc7f9ffffffffffffffffff2040200000000000060100080200000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet228_ok : goodClaim checkedSet228 = true := by decide +kernel

def checkedSet229 : Claim := (4, [0x800140000000000000630001c000000000000000800140000000000000230001400000000000000, 0x29000000000000000007360000000000000000002900000000000000000724000000000000000000, 0x2900244000000000000600000c000000000000002900244000000000000724000e00000000000000, 0x29003640000000000000000000000000000000000000000000000000000000000000000000000000, 0xf6ffe9bfffffffffffffc9ffffffffffffffffff2000200000000000000500000a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet229_ok : goodClaim checkedSet229 = true := by decide +kernel

def checkedSet230 : Claim := (6, [0x8102608e00000800c0400000000000000000000000000004000008004040, 0x6188102208200000000000000000000000000000619850a2282000000000000, 0x638000e600002000010c00000000000000000000228000e6000020000108000, 0x6398700000002000a0000000000000000000000041185000000000000000000, 0x639870e638e00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f8ff9ff1fdfff5ff3fff00000000000000000601800a0280000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet230_ok : goodClaim checkedSet230 = true := by decide +kernel

def checkedSet231 : Claim := (6, [0xc10260ca8004000c00800000000000000000000040000040800400040080, 0x380700600a000000000000000000000000000000380704610a000000000000, 0x638000e6000e000002c000000000000000000000228000e6000200000280000, 0x639c7000000e0060000000000000000000000000411c5000000c00600000000, 0xfffffffffffffffff9e73efddf3d1ffffff3ffff0000000000000000002002044108000000000000, 0xffffffffffffffffffffffffffff1ffffff3ffff00000000000000000639870e638a000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet231_ok : goodClaim checkedSet231 = true := by decide +kernel

def checkedSet232 : Claim := (6, [0x1fba0000000000000000000000000000000012001fba000000000000, 0xc98000ba0024700000000000000000000000000040800000002430000000, 0x638001c300039600000000000000000000000000238001430000940000000, 0x7c0001f80003e0000000000000000000000000005c0000a80003600000000, 0xfffffffffffffffffff9367ff36dffc79fffffff0000000000000000000012001128000000000000, 0xffffffffffffffffffffffffffffffc79fffffff00000000000000000007bf001fba000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet232_ok : goodClaim checkedSet232 = true := by decide +kernel

def checkedSet233 : Claim := (4, [0x980600000000000000000000000000000000000098860000000, 0x8120600c04000000000000000000000000000000812020040400, 0xe980008c00000000000000000000000000000000200000880000, 0xe9b8600000000000000000000000000000000000c9b860000000, 0xffffffffffffffffffffffffffff1e7ffff3ffff0000000000000000000000000000080840000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet233_ok : goodClaim checkedSet233 = true := by decide +kernel

def checkedSet234 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018180000000000c000000000030300c0c0100a0010180500200200c004002000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet234_ok : goodClaim checkedSet234 = true := by decide +kernel

def checkedSet235 : Claim := (6, [0x2000a00c000000000000000000000000000000002000a00c004, 0x100600600000000000012018a02c00c000000000000200200000000000012008a02c00c, 0x6000070000000000000001e000003c0000000000200007000000000000000160000038000, 0x6018000000000000000001e01ca0000000000000401800000000000000000080140000000, 0x6018070070000000000000000000000000000000601805005000000000000000000000000, 0xfffffff9feff9ff9ffffffffffffe1fe7dffffff0000000000000000000000000000000008004004])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet235_ok : goodClaim checkedSet235 = true := by decide +kernel

def checkedSet236 : Claim := (6, [0x1020000000002600c00000008e0400000000000000000000000000004000000004040, 0xc300000001020000000002200000000008200000c3000000030a000000000a2000000000282000, 0xc70000000000000000000e610c00000000000000450000000000000000000e6108000000000000, 0xc7000000030e000000000000000000000000000082000000030a00000000000000000000000000, 0xc7000000030e000000000e600000000038e00000c7000000030e000000000e600000000038a000, 0xfff8fffffffff1ffffffffff9ff3ffffffff1fff00c00000000300000000000a0000000000280000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet236_ok : goodClaim checkedSet236 = true := by decide +kernel

def checkedSet237 : Claim := (6, [0x1201813008000000000000002402000000000000120081100800, 0x1026c060000000000001201813008000000000000002402000000000000120081100800, 0x840020c0000000000000022400030000000000008400a0c00000000000000224000b00000, 0xe400e6c000000000000003e4001f000000000000a400e6c00000000000000364001f00000, 0xe490000000000000000003e49800000000000000409000000000000000000080900000000, 0xe490e6c260000000000000000000000000000000e490e4824000000000000000000000000, 0xfffffff9beff93f9ffffffffffffe1be7fffffff00000008000a0000000000000000200000a00000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet237_ok : goodClaim checkedSet237 = true := by decide +kernel

def checkedSet238 : Claim := (6, [0x6c1106c0618000000000012008200000000000006c1907e07180000000000120082028008, 0x7c0007f0000000000000012000002c0000000000240007e00000000000000120000028000, 0x7c0c0130180000000000000000000000000000007c1f05b05d00000000000000000000000, 0x7c1f0000000000000000012008a0000000000000581f00000000000000000000000000000, 0x7c1f07f07f8000000000000000000000000000007c1f05b05d00000000000000000000000, 0xfffffffe3fcff0ff87fffffffffffdfff5ff3fff0000000601807007000000000000100080020008])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet238_ok : goodClaim checkedSet238 = true := by decide +kernel

def checkedSet239 : Claim := (3, [0x600000000006000000000000000000000000000060080020080600000080000, 0x600c0000000e0000000000000000000000000000400c0000000c00000000000, 0x600c00200c00000000000000000000000000000060080020080000000000000, 0xffffffffffffffffffff3fffff3fffffffffffff0000000000000000020000020000200000080000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet239_ok : goodClaim checkedSet239 = true := by decide +kernel

def checkedSet240 : Claim := (4, [0x81000000001060000000000c0000000000400000810000000010600000000004000000000040, 0xc180000000000000000000000000000000000000c18000000018500000000000000000000000, 0xc3800000000000000000010c0000000000000000020000000000000000000108000000000000, 0xc380000000187800000000000000000000000000c18000000018500000000000000000000000, 0xfffffc7fffffffff87fffffffff3ffffffffffff0000c00000000018000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet240_ok : goodClaim checkedSet240 = true := by decide +kernel

def checkedSet241 : Claim := (6, [0x1026c060000000000001201813008000000000000002402000000000000120081100800, 0x840020c0000000000000022400030000000000008400a0c00000000000000224000b00000, 0xe400e6c000000000000003e4001f000000000000a400e6c00000000000000364001f00000, 0xe490000000000000000003e49800000000000000409000000000000000000080900000000, 0xe490e6c260000000000000000000000000000000e490e4824000000000000000000000000, 0xfffffff9beff93f9ffffffffffffe1be7fffffff00000008000a0000000000000000200000a00000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet241_ok : goodClaim checkedSet241 = true := by decide +kernel

def checkedSet242 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fbfc3fffcff3ff87dff87fbff0fdffe1ff3fff0003000040000a00000800002000004000002000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet242_ok : goodClaim checkedSet242 = true := by decide +kernel

def checkedSet243 : Claim := (6, [0x8100000183106000000000cf0000000000c000008100000081106000000000450000000000c0, 0x82000000038b000000000000000000000000000082000000030a00000000000000000000000000, 0x82e1c0000183000000000000c30000000000000082e1c000038b185000000002c30000000000a0, 0x82e3c0000000000000000003cf000000000000000022400000000000000000038a000000000000, 0x82e3c000038b187800000000000000000000000082c18000038b18500000000000000000000000, 0xfffdfc3ffffff4ff87fffffffff0ffffffffffff0080e000000380180000000002c00000000000a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet243_ok : goodClaim checkedSet243 = true := by decide +kernel

def checkedSet244 : Claim := (6, [0x3126c0e1000000000001201813008000000000000002402000000000000120081100800, 0x18c2120c0810000000000022400030000000000018d21a0c48100000000000224000b00000, 0x1ec00e6c000000000000003e4001f000000000000a400e6c00000000000000364001f00000, 0x1edb1000000000000000003e4980000000000000149b100000000000000000080900000000, 0x1edb1e6c6e1000000000000000000000000000001edb1e486c100000000000000000000000, 0xfffffff93eef93f9efffffffffffe1be7fffffff00000018120a0048000000000000200000a00000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet244_ok : goodClaim checkedSet244 = true := by decide +kernel

def checkedSet245 : Claim := (6, [0x1200031000060001360013000003840008000000120000000002000012001100000080000800, 0x63002240021000000001060003000002040000006300224012100000000506000b00001204000000, 0x7b0000001b100000000736000000001b840000007b0000001b100000000724000000001b04000000, 0x7b003e4000000000000736001f000000000000002900364000000000000736001f00000000000000, 0x7b003e401b100026000000000000000000000000520008001b100024000000000000000000000000, 0xe4ffe1bffeeffff9ffffc9fffffffffe7bffffff6000200012000000000500000a00001200000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet245_ok : goodClaim checkedSet245 = true := by decide +kernel

def checkedSet246 : Claim := (6, [0x1a0007c000130000d0000080000d8000010000001a000240001200004000008000040000010000, 0x7020181c000030000100180000001800000000007020181c0400300801001800000018020000000, 0x1f000007c0c0000000d0098000000d80600000001f00000580c00000009009800000098060000000, 0x1f1a0d800000000000d009808010000000000000090804000000000000d009008010000000000000, 0x1f1a0d87c0c0130180000000000000000000000016120987c0c01301800000000000000000000000, 0xe4e5f3793fffffffff2ffffffffff37fffffffff0400010100400100800000800000010020000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet246_ok : goodClaim checkedSet246 = true := by decide +kernel

def checkedSet247 : Claim := (4, [0x185000000000000000000000000000c18000000018500000000000000000000000, 0x200000000185000000003080000000000000000020000000000000000000108000000000000, 0xe000000000180000000003800000000000000000e00000000018000000000280000000000000, 0xe3c0000000185000000000000000000000000000c18000000018500000000000000000000000, 0xffff9d3ffffffff7effffffffcffffffffffffff0000810000000010400000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet247_ok : goodClaim checkedSet247 = true := by decide +kernel

def checkedSet248 : Claim := (6, [0x1200010000060001360013000001800008000000120000000002000012001100000080000800, 0x21002240000000000001060003000000000000002100224000000000000506000b00000000000000, 0x39000000090000000007360000000009800000003900000009000000000724000000000900000000, 0x39003e4000000000000736001f000000000000002900364000000000000736001f00000000000000, 0x39003e40090000260000000000000000000000001000080009000024000000000000000000000000, 0xe6ffe1bffefffff9ffffc9fffffffffe7fffffff2000200000000000000500000a00000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet248_ok : goodClaim checkedSet248 = true := by decide +kernel

def checkedSet249 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70301c0000000000018018020030000000000000101004000000000001805002002000000000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet249_ok : goodClaim checkedSet249 = true := by decide +kernel

def checkedSet250 : Claim := (6, [0x1300c0078000000000002011e00c000000000000000040028000000000002000a00c000, 0x401c000000000000000000801600000000000000401800000000000000000080140000000, 0x4c1100c001800000000000ac10600000000000004c1900e001800000000000ac14600a000, 0x5c1f000000000000000000bc17e0000000000000581f00000000000000000098174000000, 0x5c1f00f0078000000000000000000000000000005c1f00b00500000000000000000000000, 0xfffffffffe0fffff87fffffffffffffe81ffffff0000000040000e0000000000000002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet250_ok : goodClaim checkedSet250 = true := by decide +kernel

def checkedSet251 : Claim := (6, [0xc18260cf8104180cf0c000000000000000000000408000458104180450c0, 0x618c18220c3e1c0000c300000000000000000000619c58a22c3e1c6142c30a0, 0x638000e6000e3c0003cf00000000000000000000228000e600022400038a000, 0x639c7800000e3c61e00000000000000000000000411c5800000c18614000000, 0x639c78e63cf00000000000000000000000000000639870e638a000000000000, 0xffffffffffffffffffc7f87f9ff0fc3fe1ff0fff00000000000000000601c00a02c0e006002c00a0])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet251_ok : goodClaim checkedSet251 = true := by decide +kernel

def checkedSet252 : Claim := (4, [0x58000000000140000000000000000000000001005800000018014000000, 0x20040040000200140080000000000000000000002000004000020000008000, 0x380580000003c0140000000000000000000000001005800000018014000000, 0x38058060000000000000000000000000000000003805006000000000000000, 0xffffffffffffffffffc7fbfffffffd3ffbffffff0000000000000000000000800000010010000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet252_ok : goodClaim checkedSet252 = true := by decide +kernel

def checkedSet253 : Claim := (6, [0x12000130000678003600002c00019e00000c000012000000000228001200002c00008a00000c, 0x1b001ec0011000061800360000000001860000001b001ec00190000718003f00003a0001c600000a, 0x1f00000001f0000000003f8000000001fe0000001f00000001f0000000002d800000000174000000, 0x1f001fc00000000000003f80003f000000000000090016400000000000003f00003a000000000000, 0x1f001fc001f00007f800000000000000000000001600098001f00005d00000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff18001c00018000070000380000300001c000000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet253_ok : goodClaim checkedSet253 = true := by decide +kernel

def checkedSet254 : Claim := (6, [0xc7001840020c000638000c000062400030000000c7000840020c000228000c0000224000300000, 0x107024040000c000038060000000240000000000107024040000c00003806040100024000100000, 0x61000018420000000639060000006242000000006100001002000000041104000000400200000000, 0x61c76240000000000639060c030000000000000021452240000000000639060c0300000000000000, 0x61c7625842020c080000000000000000000000004082401842020808000000000000000000000000, 0x9e3c9fa7bffffffff9e7ffffffff9fbfffffffff0004020000000400002002040100020000100000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet254_ok : goodClaim checkedSet254 = true := by decide +kernel

def checkedSet255 : Claim := (6, [0x81000001938180000002a0c00000000d24000000810000008180800000000040000000040400, 0x1b09800000130180000000a000000000012000001b09800004132180000010a000000000412000, 0xdb0000000d930000000032a000000000cd200000db0000000d120000000032a000000000c92000, 0xdbe9800000000000000032a8c0000000000000004920000000000000000032a880000000000000, 0xdbe980000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3c1e7ffffe7cfffffffffddf3ffffffff3dfff0018080000041021000000108000000000410000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet255_ok : goodClaim checkedSet255 = true := by decide +kernel

def checkedSet256 : Claim := (4, [0x3000005000000000000000000000000600018000300000500000000000000000000000, 0x200003000005000060000080000000000000000020000000000000002000008000000000000, 0x7000000003000000000070000000000000000000700000000300000000005000000000000000000, 0x70003c0003000005000000000000000000000000600018000300000500000000000000000000000, 0xfcfffd3fffefffffeffff9ffffffffffffffffff0400010000200000400000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet256_ok : goodClaim checkedSet256 = true := by decide +kernel

def checkedSet257 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x3000000c010000000380600000002c0060000000300000080100000001005000000008004000000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet257_ok : goodClaim checkedSet257 = true := by decide +kernel

def checkedSet258 : Claim := (6, [0xc98200c08120600c04000000000000000000000040800040812020040400, 0x90098000000980600000000000000000000000009209800000098860000000, 0x69000220000e980008c00000000000000000000020000220000200000880000, 0x696c9800000e9b86000000000000000000000000496c9800000c9b860000000, 0x696c9a208c00000000000000000000000000000069689220880000000000000, 0xfffffffffffffffff9ef3e7dff3f1e7ffff3ffff0000000000000000008208000000080840000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet258_ok : goodClaim checkedSet258 = true := by decide +kernel

def checkedSet259 : Claim := (6, [0x4020000000c007800000c430c00000000c000000402000000040028000004410c00000000c000, 0x402000000000000000000e038000000000000000402000000000000000000a0280000000000000, 0x4722c000000c001800000c0300000000000000004722c000000e001800000e638a00000000a000, 0x4723c0000000000000000e638f00000000000000452240000000000000000e638a000000000000, 0x4723c000000f007800000000000000000000000002018000000b00500000000000000000000000, 0xffffdc3fffffffff87fffffffc70ffffffffffff0047000000000e000000000e600000000000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet259_ok : goodClaim checkedSet259 = true := by decide +kernel

def checkedSet260 : Claim := (6, [0xc982a0d28120600c04000000000000000000000040800040812020040400, 0xd80980a012098060000000000000000000000000da0990a412098860000000, 0x6d80032a000e980008c0000000000000000000002480032a000200000880000, 0x6dec9800000e9b86000000000000000000000000496c9800000c9b860000000, 0x6dec9b2acd2000000000000000000000000000006de8932ac92000000000000, 0xfffffffffffffffff9e73e7ddf3d1e7ffff3ffff000000000000000000c208108410080840000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet260_ok : goodClaim checkedSet260 = true := by decide +kernel

def checkedSet261 : Claim := (4, [0x3000000000000000000000140000000000000180300000000000000000018014000000, 0x300c000000000000000200140080000000000000000400000000000000020000008000, 0x1c030000000000000000003c0140000000000000180300000000000000000018014000000, 0x1c0300e0000000000000000000000000000000001c0300a00000000000000000000000000, 0xffffffff3feff3fffffffffffffffd3ffbffffff0000000100200000000000000000010010000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet261_ok : goodClaim checkedSet261 = true := by decide +kernel

def checkedSet262 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018000000000000000000000002020080c0100a00100000000000000000000000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet262_ok : goodClaim checkedSet262 = true := by decide +kernel

def checkedSet263 : Claim := (3, [0xcc00000000000000000000000000000000000000cc040012002, 0xdc0000130000000000000000000000000000000044000012000, 0xdc0600000000000000000000000000000000000098060000000, 0xfffffffffffffffffffffffffffffe3fffffcfff00000000000000000000000000000c0040010002])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet263_ok : goodClaim checkedSet263 = true := by decide +kernel

def checkedSet264 : Claim := (6, [0x8100000193818000000200c00000000c04000000810000008180800000000040000000040400, 0x120980000013018000000000000000000000000012098000041321800000000000000000000000, 0xd20000000d93000000002200000000008c000000d20000000d1200000000220000000000880000, 0xd2e980000000000000002208c00000000000000040200000000000000000220880000000000000, 0xd2e980000d93e18000000000000000000000000092c980000d93e1800000000000000000000000, 0xff3d1e7ffffe7cfffffffffdff3ffffffff3ffff0010080000041021000000000000000000000000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet264_ok : goodClaim checkedSet264 = true := by decide +kernel

def checkedSet265 : Claim := (6, [0x6c0000000000000012019e02c00c000000000000240000000000000012008a02c00c, 0x2400000000000000000001fc1fe0000000000000000000000000000000000098174000000, 0x240006c000000000000001ec1860000000000000240007e000000000000001ec1c603a00a, 0x240007e000000000000000000000000000000000240005a00000000000000000000000000, 0x240007e000000000000001fc00003f0000000000240007e0000000000000016400003a000, 0xffffffffbffff1fffffffffffffffc3fe1ff0fff00000002000070000000000000001c01c003000a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet265_ok : goodClaim checkedSet265 = true := by decide +kernel

def checkedSet266 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000, 0xfffbfdffffcff3ff87dff9ffbff3fdffe1ff3fff0103004040000a00001805002002004000002000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet266_ok : goodClaim checkedSet266 = true := by decide +kernel

def checkedSet267 : Claim := (6, [0x2001e7800000000000000002008fc000000000000000228000000000000000000085c, 0xa006e180000000000000000a00b3000000000000b006f180000000000000000a80b3a, 0xb8000000000000000000000ac000000000000000b0000000000000000000000a80000, 0xb80f8000000000000000000ac0ff000000000000b80d8000000000000000000ac06a0, 0xb80fff8000000000000000000000000000000000b80fdd00000000000000000000000, 0xfffffffffffc7fe787ffffffffffffffffd3ff0f000000000000002700000000000000000000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet267_ok : goodClaim checkedSet267 = true := by decide +kernel

def checkedSet268 : Claim := (4, [0x2c00000000000a00000000000000000000000000ac00000000006a0, 0x12200000000008a80000000000000000000000001020000000000808, 0x1ec0000000000fa00000000000000000000000000ac00000000006a0, 0x1ef00000000000000000000000000000000000001eb0000000000000, 0xffffffffffffffffffffffffe1fffffffffff4df0000000000000000000000000040000000000480])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet268_ok : goodClaim checkedSet268 = true := by decide +kernel

def checkedSet269 : Claim := (6, [0x26c1e78000000000000000132c8fc000000000000240228000000000000000112c85c, 0xe6c6e180000000000000001f00b3000000000000f7e6f180000000000000001fbab3a, 0xf80f8000000000000000001fc0ff000000000000b80d8000000000000000000ac06a0, 0xfff00000000000000000001fff00000000000000f7e00000000000000000001fba000, 0xffffff8000000000000000000000000000000000fdbfdd00000000000000000000000, 0xfffffffffffc70e787ffffffffffffffffc30f0f000000000004702700000000000000000143090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet269_ok : goodClaim checkedSet269 = true := by decide +kernel

def checkedSet270 : Claim := (4, [0x180000000000000000000000a000000000000000d80000000000000000000006a0, 0x1e0000000000000000000008a80000000000000002000000000000000000000808, 0xf8000000000000000000000fa000000000000000d80000000000000000000006a0, 0xff00000000000000000000000000000000000000fd000000000000000000000000, 0xffffffffffffff91fffffffffffffffffffff4df0000000000000090000000000000000000000480])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet270_ok : goodClaim checkedSet270 = true := by decide +kernel

def checkedSet271 : Claim := (7, [0x4020000300c0078200600400c02001e00c000000402000000040028200200400c02000a00c000, 0x30702c0c0100c0018380600000002c00600000003020080c0100a00101005000000008004000000, 0x30702c0c0100c0018380600000002c006000000030702c0c0100e0018380700600a02c00600a000, 0x7000001c030000000380780000003c01e0000000700000180300000001005800000018014000000, 0x70703c00000000000380780600f000000000000010502400000000000380700600a000000000000, 0x70703c1c0300f0078000000000000000000000006020181c0300b00500000000000000000000000, 0xf8fffc3fffcfffff87fff87ffff0ffffe1ffffff0007000040000e0000280000600002400000a000])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet271_ok : goodClaim checkedSet271 = true := by decide +kernel

def checkedSet272 : Claim := (6, [0x3000132c0001800008fc000000000000000000001000112c00008000085c, 0x200001fc0000800000ff00000000000000000000000000ac00000000006a0, 0x230001f00000980000b300000000000000000000238001fba0009c0000b3a, 0x2380000000009c00000000000000000000000000228000000000940000000, 0x238001fff0000000000000000000000000000000238001fba000000000000, 0xfffffffffffffffffffffffffc30ffffffffff0f00000000000000000002380014300009c000090a])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem checkedSet272_ok : goodClaim checkedSet272 = true := by decide +kernel

def claims : List Claim := [checkedSet0, checkedSet1, checkedSet2, checkedSet3, checkedSet4, checkedSet5, checkedSet6, checkedSet7, checkedSet8, checkedSet9, checkedSet10, checkedSet11, checkedSet12, checkedSet13, checkedSet14, checkedSet15, checkedSet16, checkedSet17, checkedSet18, checkedSet19, checkedSet20, checkedSet21, checkedSet22, checkedSet23, checkedSet24, checkedSet25, checkedSet26, checkedSet27, checkedSet28, checkedSet29, checkedSet30, checkedSet31, checkedSet32, checkedSet33, checkedSet34, checkedSet35, checkedSet36, checkedSet37, checkedSet38, checkedSet39, checkedSet40, checkedSet41, checkedSet42, checkedSet43, checkedSet44, checkedSet45, checkedSet46, checkedSet47, checkedSet48, checkedSet49, checkedSet50, checkedSet51, checkedSet52, checkedSet53, checkedSet54, checkedSet55, checkedSet56, checkedSet57, checkedSet58, checkedSet59, checkedSet60, checkedSet61, checkedSet62, checkedSet63, checkedSet64, checkedSet65, checkedSet66, checkedSet67, checkedSet68, checkedSet69, checkedSet70, checkedSet71, checkedSet72, checkedSet73, checkedSet74, checkedSet75, checkedSet76, checkedSet77, checkedSet78, checkedSet79, checkedSet80, checkedSet81, checkedSet82, checkedSet83, checkedSet84, checkedSet85, checkedSet86, checkedSet87, checkedSet88, checkedSet89, checkedSet90, checkedSet91, checkedSet92, checkedSet93, checkedSet94, checkedSet95, checkedSet96, checkedSet97, checkedSet98, checkedSet99, checkedSet100, checkedSet101, checkedSet102, checkedSet103, checkedSet104, checkedSet105, checkedSet106, checkedSet107, checkedSet108, checkedSet109, checkedSet110, checkedSet111, checkedSet112, checkedSet113, checkedSet114, checkedSet115, checkedSet116, checkedSet117, checkedSet118, checkedSet119, checkedSet120, checkedSet121, checkedSet122, checkedSet123, checkedSet124, checkedSet125, checkedSet126, checkedSet127, checkedSet128, checkedSet129, checkedSet130, checkedSet131, checkedSet132, checkedSet133, checkedSet134, checkedSet135, checkedSet136, checkedSet137, checkedSet138, checkedSet139, checkedSet140, checkedSet141, checkedSet142, checkedSet143, checkedSet144, checkedSet145, checkedSet146, checkedSet147, checkedSet148, checkedSet149, checkedSet150, checkedSet151, checkedSet152, checkedSet153, checkedSet154, checkedSet155, checkedSet156, checkedSet157, checkedSet158, checkedSet159, checkedSet160, checkedSet161, checkedSet162, checkedSet163, checkedSet164, checkedSet165, checkedSet166, checkedSet167, checkedSet168, checkedSet169, checkedSet170, checkedSet171, checkedSet172, checkedSet173, checkedSet174, checkedSet175, checkedSet176, checkedSet177, checkedSet178, checkedSet179, checkedSet180, checkedSet181, checkedSet182, checkedSet183, checkedSet184, checkedSet185, checkedSet186, checkedSet187, checkedSet188, checkedSet189, checkedSet190, checkedSet191, checkedSet192, checkedSet193, checkedSet194, checkedSet195, checkedSet196, checkedSet197, checkedSet198, checkedSet199, checkedSet200, checkedSet201, checkedSet202, checkedSet203, checkedSet204, checkedSet205, checkedSet206, checkedSet207, checkedSet208, checkedSet209, checkedSet210, checkedSet211, checkedSet212, checkedSet213, checkedSet214, checkedSet215, checkedSet216, checkedSet217, checkedSet218, checkedSet219, checkedSet220, checkedSet221, checkedSet222, checkedSet223, checkedSet224, checkedSet225, checkedSet226, checkedSet227, checkedSet228, checkedSet229, checkedSet230, checkedSet231, checkedSet232, checkedSet233, checkedSet234, checkedSet235, checkedSet236, checkedSet237, checkedSet238, checkedSet239, checkedSet240, checkedSet241, checkedSet242, checkedSet243, checkedSet244, checkedSet245, checkedSet246, checkedSet247, checkedSet248, checkedSet249, checkedSet250, checkedSet251, checkedSet252, checkedSet253, checkedSet254, checkedSet255, checkedSet256, checkedSet257, checkedSet258, checkedSet259, checkedSet260, checkedSet261, checkedSet262, checkedSet263, checkedSet264, checkedSet265, checkedSet266, checkedSet267, checkedSet268, checkedSet269, checkedSet270, checkedSet271, checkedSet272]

def displaceBlock0 (i : Nat) : Nat :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x519030702053c04000e000f14071612000b030301000201161a0c041204021b010b1400000007000c0822020000021416090c22000520071700562a091a2107 else 0x90c010003002f00252003000909051b0a00000201094a0103121e0b0a05050a0200120307321529081f0007000307111104045e0700090201091608145b0600) else (if i < 3 then 0x126200905090c1b0507170101031000020a150e09040b3a02100332001302140b0311081906050b01190d212f1c000a0407450c3704000804060b0002010700 else 0x15002504001b1b09010102010201210b00070f130306300f0a0366000201161714050903000e1c022c1e0c0d0b0d1909140102161845082f270001010208060b)) else (if i < 6 then (if i < 5 then 0x30207100202040d020f06201e0408000012060d0304020312090501141c0101032c1305153300010902010a0500000d0a000a150300042b0b0c020400050012 else 0x50106050107090505070010010001020b110e0500071f1e000100070a06020e032f000305230004010200130655220004010f01090c0e0409121e0801030a1d) else (if i < 7 then 0x500040c000202000703001111060e0a1433010708130d0204011c2427702d241f0c090c030901050101010002012a030000023a281312030005010043190007 else 0x1600080306000410080a10040a04080d04040800002f0505040204000004001d229703020a020f010f25010205000f0400010800210306011102140302100800))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x31a00011b0901150002040f012a0c08000a04530101060202040207000a060101070e1100010120013e08120c0c231600015b0d0f01060b0100011a18020800 else 0xf02072109000a03010603301a030005090b290100000802022817090f29000b3c0701010701001b1504020106080b2c0a010d0504001a1008030b0208110007) else (if i < 11 then 0x70602090a05020b0b03000908000800010b000c23221600121307002a01090206070b0f062a000718030b000a020101022600090404030c001b04063101000e else 0x1519030206000a010000000c200000000b00081c0b0028000f0000000902043700031906000f0f04001a1928090c000805000017000006060130080501020005)) else (if i < 14 then (if i < 13 then 0x6030743002f05010600000001050c040617120c01000a070000000509012d0103250b02030604163402020005060408020401380f080b0005031d0b000b012b else 0x40349020603042318042d0e04340d0a060009031d0f010501020506000a2202180a0101081910192401020405140803130b1f0114000007062303090c030403) else (if i < 15 then 0xf1e05190003180204010202040a010c01011b160f060006080100010000000701030124020829010e02160301040b00010104021a0502080200070c045f0301 else 0x125030a0b020003000e2a0400090101380214000103090d0b0000060608010d0218070b000a0004000403030403180504010b200c3c29051a3900110a040100))))

def displaceBlock1 (i : Nat) : Nat :=
  (if i < 23 then (if i < 19 then (if i < 17 then 0x80110031c00110e010a0422081606050801060a0907140000010e11050010030d0513012364020001430e05120b22190508000d030303020f2602080100 else (if i < 18 then 0x3030a062215070f0223430704011006050e030701120a251a020500020005030006062314130101040003050510060103010105040312010700000107030012 else 0x5031004021f1110080a0f1811023d0b0a02030f080302044e110520050202000719050005010021003002130600140821000a030103045305020000171d0701)) else (if i < 21 then (if i < 20 then 0x723000f08000d05390d0d1c24150b101b04350c0700033b05161501300002080d03200600070b18140013020609000009000509040b0d0301121f3811190d01 else 0x6301070500106c35020f11020001080c070e110d071e0500050108003305060400011d090e040104095c12050403170128000a001001141d0903012f0a080800) else (if i < 22 then 0xb0b010503031b0801151008060a02020801000b0815070700080b0007020f0906030c2d000a0d0e011204150b0001100d00020107000300212901010a1a0b2b else 0x100010104030103382f001f0a14120604010e021a05070006031019081803040100082b092c210017190302050403060e240306071443140402111c01080020))) else (if i < 27 then (if i < 25 then (if i < 24 then 0x101030100020700020305060013010a1802120012060a1a02010a04220001040f2f5002220131080700001507070f000b0700090915044902070b0000101101 else 0x1403030103020f402d0103010516060000040003020122050403040601030a421a36004111010011010206020031001d000b0303020a081a000107083d000700) else (if i < 26 then 0x5001e1c2d062d0004070612022b0108260c0c1500000f0020000707211e050922420b10090300250a270100020706000228010902042a010a00001923000104 else 0x1060b0000060202082800060000030a0100092b06052d120801240008000d001103000313140104002913021000000c00080b210d1138062d07000a041c000a)) else (if i < 29 then (if i < 28 then 0x33140316060813000a03030103070503000005010f050a0403013a020027000c0501010502022f12001500331004110405120302c301060d2200010b010f00 else 0x40402040a0e0300093201040818160c18000d021708090a000204190202060f01001211180005011c058201000002051a04140106102f3e00170405001014) else (if i < 30 then 0x60314010b052e00000402021e010705001e0b1c00071a03150e010804030f1906052901045c00330100240012111579000402010a1a0309000725053304440a else 0x1f02252804080208220b000015000001162003410100000000016a00000000080000001c120512))))

def displace (i : Nat) : Nat :=
  let b := i / 64
  let g := b / 16
  let a := (if g < 1 then displaceBlock0 b else displaceBlock1 b)
  (a >>> ((i % 64)*8)) % 256


def slotBlock0 (i : Nat) : Nat :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x2f00476b91e9507a0a01350a84100ae40041040008268390040a000119cbca42080000006680000542f0040ad40019d490f5c800025e0110da454000147e54630000008208059000 else 0x2a0056a000080000a3022a482162080c0001008000a0049394083f0919c023f7281096c7021055a0101990ccd220800109d6a1500000001853ecf20ab5cc0204220003f2080814f0) else (if i < 3 then 0x588401067391040000051718cc81e800ce7205291166705121a4e0521c804ad02ae5745e01001223f001c838600001082000400000b91fa90000004210000801104000a00ab48292 else 0x4915000c6522b4009d5210da4d20541002412532002005200082c95200572670084924010000000a40010dc2671f80000a30280000010000400a472801a40520a900041008040008)) else (if i < 6 then (if i < 5 then 0x640008272010209400010156410690208241208fda45405001480000011a40100b9402a30000000000001149081f19c820c0001082001c904a80501001f82b33bc8d093001059000 else 0xa900441052b54800002914641390142c41008000401050021c00691f974640032004005e821146744348006801210109200828e43d521c824000012800007280014ad00320a801) else (if i < 7 then 0x42010cc0173104e4000081506920231820b900ae5484a2a0088201051dc00005680548005239082671f950043f56801a4ad518000a007280400f1009280000520101002003c14800 else 0x5690400010001d7a0225ab47a01040000001522b43e00338e4040067a8dca8152000004d008fc6281519507e3d00394000120b940002288154800000488200338ec0a5456b20ce41))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x1502002009a1a49f001c0a401008040041690008204052b400a40039800e525210023f20b487e813380000e520320760a5680108002080000001f81082a400b50960020805a601 else 0x2b5ca16692900004523947e040000000ad8490c0a100080414a433a900241491c8740400a9000ad05014040272bc0003f018217ab958a88825452000ce01091040084) else (if i < 11 then 0x208000060001419ed25b1510201041c80001000fc040072820080069011f2080800402e51fa9010002081400022a28ca800000094843000fc2e00339fc02002880800672a8000a08 else 0x208094800050fc14a400004023b1f950020020805a404218087e0700000000404004cead0001414dd000413c4301320e20800009a65e0202164000000414a45201008c85d800d0a4)) else (if i < 14 then (if i < 13 then 0x72854eec8208141ea42a000b4fc6400000a74241c24e6000000081012d8103e21804020069394bc0200a8c94026900124002a028000000395ca005c9295a7265808e802028040002 else 0x13c10d3002a000d220a9002001f8ec04a4000b410010090402015010482015210c82000028d4800522c41400013e802002095082000034802010000802055202000c80081c0412) else (if i < 15 then 0x2150000172800e88844028000a520fc7ea300008760000a11726b490014692000080000693e47e675199d4800043495a00008017400491a0004b2834800001f9dc820181804103f else 0x39c00a401002180220b219ef000bc008c872904ce0234002141002a0548007c92948014a80c001001a48e4784919c8204023495a00012b5a4a3590087e0420805f24100b494810))))

def slotBlock1 (i : Nat) : Nat :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x1eab562000100804540080002052a0017a0100004040002040040020a4802a4782907e9201378001002905a400010007e012d0015a010000482ad0085400547780150c72a2bc1401 else 0x341c0b5037300804c82a128020a00800000000000005400000a8a4340000096022740002000fd48a40080400673c0fc0001000fc820102150000800008820000a9082041f8000008) else (if i < 19 then 0x82b970249485452008e4461f80000000835002ba3421000040080190020000000010909000022a10400015180004015228c940264000ec011f804020133a90000a01104cc00 else 0x2a1c402f000b487e015210402d20019c82e7000040408000007e510080404042a0fc7ea4781a00201218047e4a02801caa433b1802021c290003f42348004156a900400588081000)) else (if i < 22 then (if i < 21 then 0x338fd46542a0012888783d400010200014d200001a4c6398055a5d5ca10d0010419c7e10338f9a40100348ce54522055a0104010d05a00021125001014c87201104cc0525a1c0066 else 0x800949001f8014800009a148000295008000080886e633801c80800290004183800044a001d008726b815fc3f20800086700290a80033928a8052a004063f25a74083f7028cce01) else (if i < 23 then 0x1f801480100040009d0000548ad0081c00100200004a40080082002500494416a2b40481000099e6d59000200000011904100951ca0020800a23f1c96c1400642900000008017201 else 0x25e2a1042c00043480600000fc00005200000a405000009d0810c000120a4c02923380148520012800e6003953a0420805484100009a4f900290e8e21186dbe1002801ca00))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x2f31dc0010000800a452000006733804088200ab0a8000004010020080004ad72805a4430000082411f80400000001404412512c0000518fc020000a9000680800c00c8021c88200 else 0x52290140a008000200690200200040f8020856805480059104a841002f9483f5915000a400005243f0000004d20081000045c99c82002880400014929002d27280004ad008054800) else (if i < 27 then 0x2900008203447e67330fd72022a15002722a00082d200841487800b48009288029ce02569dd90bd0000da4e53380476545200000001f8fc8202550000401051040a0420a580077 else 0x98101e411c804000801999ca0a2580400a401104004152015480038104020804008000400348000800004043d0c00800ad000000205329052c0000820000852005a43f521289468)) else (if i < 30 then (if i < 29 then 0x26198266700320cc002a32002a40019ccf040090c100200008cea43e804820000004000a020000000698055a008639400000401572393001002a4521280400521e00400011a002a4 else 0x287e415208c146772810d00039104a8ad25a8c0aa4003dc14ad02261ca0200005fc0120805b204008fc060802b495aae00000021000af4040a00000146853b496202690000000) else (if i < 31 then 0x1f8fc105402000ced45c800000052015460101011a4a3008c07e00521e010b9010fc1400523c0030e003c1ca075690400540095002013900c7e670039404c838008003f028000000 else 0x209056a0000a88bc9272a914804208fc02017780482a400040e839391640a5408028e40028800000800021bad34ea60003f00004865425c01a4000399c7e67000286000000007e00))))

def slotBlock2 (i : Nat) : Nat :=
  (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x5210404e60239c0a84002b4e0410000000004080400033901408050029004105ea8c00822a00146b925000003f25015146700801b46745811ae3f52805480162290ce0a392918d08 else 0x340fcd0f133b98823b690fc000200314069272808a80a008fca44149348e41669249463f001c804001fa9014084780076020039c1408021c494b1522b5463f0010002d220ae482c0) else (if i < 35 then 0xab800a4570056a0000040040000006060a000040400009c8006702808080403884a0006a10402005697808040210400680295002003400082010000004a4690099041050000001 else 0x1180814671e82924510029072d20019d1e012095000a400948e80444014000102800826808184e0042080402c8522e42a411f800aa0039001a6671f8015aa42033c7e00043940a5e)) else (if i < 38 then (if i < 37 then 0x20000010008100408252b40041000ec820000810863b000fcfcfc02000d0d200004040020804860000000e4d22a19c04540012800055d1c87e05000000000000001000000fc1004 else 0x5c9a87e000232004e60801404030000148b1012e402a32a001647220804ce4100420061020104104133b2000001f905a40178290823f2a104a839000fc820120ab402080019c1000) else (if i < 39 then 0x289559801008fcd0006900000410022124002b800e4d259000003620801f8d220849723f5200000020029000842a2b410001c801a61521a74a872003e5ca534200480676900000d2 else 0x1349743f6929002001c9c80010330100640640047e007e104028833804963d2a29010000080002a41f8fc0207001f8ce00008000041002480208568095ac73a0000000000157455))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x1d800020001021ca010800408005c8100308000000401339c802d242000043d00b200024520540000691040008008fc021000000008585000000069391a4e50084008f172b947e00 else 0x28082d20042962720001000050518190020024814b2040015af96e001dcd6011515a41001054807050400041392487eb901014020805000000133b74a200010280000520140010) else (if i < 43 then 0x1438000144008004164000006700001080a2a0000808733f000d2080000254259c8820800020102c201040ae50000000130080010a40034948000000000ad33a9000ad012100002 else 0x50eca80100015a4160933c090d0019d48050831d904151b94000059394ce8400800004b3380802410280190006900002542f3f800011f1a0000028a90b000003180400000294608)) else (if i < 46 then (if i < 45 then 0x290d000208f9e85400b48860802421460800000820a20a75c8dc20a9082434919d48080c800825400a10027200801fc00002912c3f693480a670a828d00000291a2000012ca867 else 0x692d020045234dca0034101243f3682000e538001e000258048201012b400001dae524e500008bc410029146f90819c020a05004000059008140100128020800800a8a4083940201) else (if i < 47 then 0x82104140051b9480100812c023f20910000a690949441208281401009440a00000012c084901020a302811480000004003f00800a8000202000a43000d480a4090546e80110482ad else 0xb215a0564292180072800100a00000000000a6400010080000416924ce80001291481001ab5a63f0032082fe7801000d22a04000007800402081c9012201003219001003990802))))

def slotBlock3 (i : Nat) : Nat :=
  (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x42b400af1ca90003e209c95a5100291023f20a10000005008460a2a000023f01011480000a8d5e081f9d824000134802002a9047a437e36c00d200800024b01291cad20025dca02 else 0x2814f90280c7c0133ad482410040c960004005e60008428863f00b95480000210a86700804a89256b9402000280896c8728fc000252104021669010045434348000500040cc3f) else (if i < 51 then 0x408660104d48046900082013f000960034001720000348e081691a002021f99c000a0115000c81c820001b000154600520400201000fc7e43010280002442915a00001500ac8 else 0x5690400405d0080000050000ae55229004003901000a4083208204089c95e54012b400a43901482001d800000251348246778000144b67c0c82023399c00812f0000468008fc0008)) else (if i < 54 then (if i < 53 then 0x7295002e8208fd24d309000024100000e0411480008412a001a63f4e90424410100000e5522b400d201290100069290e86700aadce543901482052081000017880010080000014c8 else 0x29082a373814020000015a4d201349a40369290d0080004000390410c2c0833b50a8f330020820034198000004000000034048a80a2002800011f805ca39568f8020a208040001) else (if i < 55 then 0x1f9a002d233394000069004020a04000f6722a0fd72010019c140049801480800001484100a9146a2733200e042000000d2019040200590418c000000144007310c08005200000cf else 0xec04413390424011c800a90e002f400000034c0072783d0c80000804e4011c808d0d2029b40400080047ee55680024510010400d20000148546781402100032c7e080b0001441))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x43020826a42090420542a0215a0200198000000a913a005ca8d7200000f9aaa48102800a40000990a4009c9840120800827600005729684000823d042910201001700103 else 0x2915af03c08d72bd0019c82003f10410000199d5a003400400410034800623a2d400020802a0a042a1f824d2010007ce4041040a4a1f80547042a04000d24e8fc00053b2b4d0a3) else (if i < 59 then 0x25104ce0100011ca926910010002098000160080094080200400545d000048120a8cfc0069001caeb041a0003f25168004152104023f6ea90003f729881010020fc0a3f5234910e0 else 0x72b480a540080048045229014b22080000a4209507ea81f81000a40400004004f92800030500002412a2b40200000fcc8002a00004a420801683f0000000372099c0a841e800bc00)) else (if i < 62 then (if i < 61 then 0x248023f33a900004000153805000293a7e2500000c8091f800031f29148041e80414012500148002f34804a405150003e0021548a420a8cce0001020a80400005a800000080000 else 0x82e40000519a0003f423980202082588204492b482010010c008408000000056ae40000000fc025400000ce040110d08000028ca8d269105488b00004020572800d01625004ce39) else (if i < 63 then 0x20804003f0000400007c8007e67008fc820000808a20020820040200801a2ad000007e74523480005001e0a8a24f010a80200105a0010800002ad000040468028fd705420b9404a4 else 0x3207ac7002c87a041f80000b9208000200000100094350008216050080204002b402000800800007a2b508011f8295a4105128a8000002008040124802013a28c003f2a00028d2))))

def slotBlock4 (i : Nat) : Nat :=
  (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x1f90402c81fb20000456ac802000080002011f80002005219c82002526000003a00000ad00020e82c0080548051f800030e0000cce00520287e051e8407e004e801fc002a004ceb9 else 0x3434c004a042d402f05180002e6041d07e0404290a8390080408015f80548d452a90a8ba01009620a2082000af00321484100000820420a58a8e50001002e42080164026100424e0) else (if i < 67 then 0x7800066000080482410280002003380002700041082c8002e482000384004670210410081f801ca040134d484156800040020a9000012a0007e00080014688492900241171a00254 else 0x20804020100828140a0021116430000000670010402725200014412090410000080000030000800000110546415c801a4ad2a000820000809a44100008b60104398e471208017201)) else (if i < 70 then (if i < 69 then 0x2081004050000876082a00400a4338115a0100bc15ad20380162a469a90004149180960100010000039290020100009a443011794854728ec0a014b04174815c99c0470001515a05 else 0x10259eba208149a0020a74bc0100028040051805720352009903e7f124000152249e83f00904ce04520000204000fcd0c3728117ab90110548e0000e40239008680e71000787e54) else (if i < 71 then 0x52001a4cf1896802000280518002f1c0dea4052880400252b87ee00080000000080802005d0008200002e55a001fa9000b049005a44100b200400521a0080000820000500a0524d2 else 0x5210402410110486ba0910c027e00801bc025d290029400001cae54401400b2443e4048b69805a4001c820ee0000004cee3000fc00000029010ad51804000052008100000ab41492))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x2055e0a00000e400051048263008402000519040000003e4a8000000948ad20b49a6a43380000d238001744a04000d04a1f804c800098055a0100291a4a4052900241000f40668 else 0x2a01000b15c21c0002520001400052b400015c80d48810030800005681148d22582000086910400054092800af00248000033b8824002500494ba002901001010fc7e00338100000) else (if i < 75 then 0x99c04e558b954802029cca8cf2a00014003a001caf01fae400b1518040001051f8023f20a20000002b3c02015190400000440c7e8b69001480e569780854002915aa06900148f0 else 0x80148005229082540290d5a050000004000099ca83f00014100400395a4040119802b90001000541fad47cad5919d48ad00b4882082080082056400000ad52198a8e5000119e04)) else (if i < 78 then (if i < 77 then 0x7328e22c800815ca087280004710500082012a0007ec80802000025200502b90000002101f8fc00003390400023905410ad0234cc001000000000040094801003dd7241848480054 else 0x80082ba040040000001054808782e80054421a4024125c0d72cd3300000d20002800c820ae402025224894085228ce8a400b94003f0280008670000482013a000005452348004a) else (if i < 79 then 0x1015cca3040014654520fc1000008141001009515a02013e42001691042c080801000000039420e5850200207003487e022029002014b000087672800006f00204008400291fc00 else 0x5cab5cad35180148d200009460072a90fc002a001cae5029287e4100005484100a10020052190104a20bc0143f01150e2084980146b2520051eb9040f408002a04150000000da43f))))

def slotBlock5 (i : Nat) : Nat :=
  (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0xa919e3f00848e0a372ad0a8080002000025c804a80004144940020800820072b4810005c92800a4000000a0000291ee410010c760a08000049200000000000221ca5446804e443 else 0x520407e0857a90140500ac802740010482c82a000cee50532000ad690fc00000000802082080148a4000008200042e548e50080082cf1f801541500800048163a500008012e4cea4) else (if i < 83 then 0x2f0402c3f5200400a3392042a085200414076902886415d3490800029a0000078005ca0501005460200004a00c300400104001291002029c8ce3f00800000165a9000005e8fc0467 else 0x390014800001c8003f521c800b10834800020090c72012080d480167950829200001480101020028700041480056bc082000441000050400482022a1b5ca41012e800b95239548b9)) else (if i < 86 then (if i < 85 then 0x29000e4030280072000800018ce000140000050fc204104009ec0000380000000001c2002a39ca8a456a900ae57800000a300001de0000119c8ba72ab40a0420951caad520055001 else 0x38002a2000107e540400400b32080014ad0080400b93f004a80a692e5265a20b489400521501401000147e4100808824100105a50e1f80002415200400544b2909454043d87e00) else (if i < 87 then 0x17d26024200c00046a004ce00209047e4126014a0007300400d2053fd9004001a0a8020034802010015000d2011a082a400004044320b20023f7800000b972950000a0012c8201 else 0x400000007e03000155000642e8e24b1f028100000a8cce04000095a00043949601008fc0000739041496040041088380fc820066128004a40b9414001fb488241491055a08))) else (if i < 92 then (if i < 90 then (if i < 89 then 0xf40277040fd5ad272804004b2a020020036b49480400001ca7220b48940201001724100049a4b2042900605020fc000056a900041018400808020056a003381400d2000140200 else 0x11fd389d0110d440020804a08800001484a0081400001f80002080000096b90019c8200700fc2cd20012c024169801a4103919e126800168f4f002b799000008018c1069000e016) else (if i < 91 then 0x1904b000000a0100248e4083902124a300001a40169a1db6087e80000d41f80400f2520217202001d402040000024002990c02005ea1002000000da4552a0fc0000341054201 else 0x1fb48ac00518047ea41f90572670404800010280020000001408e51f8e40a41691d47e670013d4841000280a6700004040000001a4d2569a002c80029044007a3988204008100002)) else (if i < 94 then (if i < 93 then 0x7280000540002014012a00082017280010012082800001f95080e500801820132105ca001b0000808000040000008107e4b0028c140a00004e45e002480067001040054023495a92 else 0x2500408035200800a4002907ed300904004100000a8003404146002510c7efe0000014415200010d2001c9480121804a2d20029148413812804d273290a854343491675208fd2400) else (if i < 95 then 0x12a4006733951740028804000000004ce00391518c1000ab41089493b4000a1f80402416929000ff64000a20520a4810d234001cafe0000148d2000fc08043f004100002811e067 else 0x82146052a304820100000a800251010a4100028005e0012d5a004302814e52a104008d208fc0204010082c015216800ba000080000021055e01000047802002b508b1640000000))))

def slotBlock6 (i : Nat) : Nat :=
  (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x2082800082080094960000000080212800e5002f544001c820d0d41f9040a0804151cc0033814000172a4882a420048005405011a8a4003200000000fd24050090402ad0299c000a else 0x119cd60020b50b40059000000a3a1047c122500000411f82805021f00002a4250fc0201208000a160090400ba0299de2002f0fda40a00904d00a3421148a301151483f51800c000) else (if i < 99 then 0x51a1c143f008047ea4008219e3e5c181084b52349240025808000002b50ce9300004080004395480003854029a728b402005cb5400d20012de0b1010014841360147e0100000a881 else 0x342e4000400001c8a32a2ec008b020010e022a00144d40095082f000000825473ac5900052020104a0004124e6008fc00434900002a45680482b1002e800103a150005409a489640)) else (if i < 102 then (if i < 101 then 0x2800000100011a83f2a000e2bd118147e003400420810099ca83e00000084a522b4b4e469000a8a36928c7e0a24904820069800140545ae820a30119d5a00000140441422480041 else 0x51104ce002a008823a00b1d5a863a125720479aa0200100978ce04000009600000041400000280001728007e54521054854010000000691280000001988210008fdca010028ca800) else (if i < 103 then 0x2ae410a420bc21400692b4020102815480a38420001000259a43f51828143d3380082b901000d0001fa2c00004900004b933004a807002e4000a04000e4ad05000f296520000201 else 0x5cc0100029ca0000004ce0500b481440003940466728e47e3f00804c400002e47a020501400001f8409e010010c008125801a41501001900001000a8012580000025200000a4))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x20904ce0a0002a0e92000407e005d34814a4000014800519c8140a00ae808080001000fe208f400417281402d351808cea469000000179020020156804a80157938a8b12500000a4 else 0x72800000052394003201004204b001dc2007519695ac8361e0820020901ca020080402a60010400a464005480000a91100000349480a330fc820100008e8a204001e010000000008) else (if i < 107 then 0x2e5485466000000005248104100000007e02008040104000a610250016240000fc000120805fc0252004a201208fc95031fb4c04000010404002080000685c91482b9000000200 else 0x5200000005210404020000008055ca90003f05001a40804001c83e00290ee0025010020000a380200808081001022f548c600290083f0900020681f800a2153a34810cf3f0141002)) else (if i < 110 then (if i < 109 then 0x81804000002b4800002abf802012899c0a011e8018e00521040000209a000542080400a400128000020b94cc0020bd080a400b95c002023940a010000010015c82002d6008280200 else 0x2a39400007f104140138005484120814023f00004102301004820020808000200169a6413900086677280000010034d720240b940000001047ea45180014a400290100a008080467) else (if i < 111 then 0x20800104b5ab4c0401000007ec40000148e70019cce012090404005200002670020000a33880046000090482a3028cd46081fb9524ad5219d480100221480002814027e4a8140201 else 0x1f80002a42502172a356800823f0000876a400800a8ad522e9720100904023f0019c00a402129a44100290e84100a900441728215aa42580008020099c0001000011010001d02067))))

def slotBlock7 (i : Nat) : Nat :=
  (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x1480002ef00998820000809ca0800020000572801ce81020140001338412e74010000001028007e001f828140052028967c02950ce045d3941041001a148a30034c00031f8048204 else 0x412800395c95064e5003e548910081400af6411800d2459a0825b0012948d2000015e540000800011515000a300001360151a495e5401001a45e380fc046400150c800011894808) else (if i < 115 then 0x9c164011fb9400a40098004a3000494401000a808cf02004820100804200069a49e000630fd487600394ce0a0399c14000090400d22180000921fb98824102901ca41003489470 else 0x569f5a4045d231726705001483d0015008f020a8c14010280082e502394000100000100051ab4a80a04001c05402005245e091507eb9040012c0005000140105009a4000a8140841)) else (if i < 118 then (if i < 117 then 0xa58020a0b001fc5452015480272ab5cc000502002a4338417a2f521052841691512410002494601000011002731a1a413002b5a43f020087e813380c02012a104e2e500ae40ae9 else 0x11a018080000400a300a9092082a2e590082a12c00a200398024156a917c028416414007284076a41f804820a728fc24045c841a40256800ce0020be02e411f82000a4013944600) else (if i < 119 then 0x292c413912dea0000014204a5699cce6700105a4a32a0053a086900000050039400a420ab40401518fc106701801e0013a0fc7ef00080148002092c04006a01400011d99c0001 else 0x20044a2080000c866800823f00000ecd22a140020000ae808000001000003bab40410012b494a4001500054252907ead000fdb8ae20bd0006852005a401783e4200200801a600))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x40040ead2a0fc020029bbc080200000020456904a80400800cea40780000e504020002300105c00a001d094d456b1948001f92e068e2a000fcb9003195a003010c02010001082b9 else 0x6c00000a400b4c000020828000a001280043012e400021f80000670500000cf72a90000a1fb980a924919d9e4169000000000828a8001ab180200009059043518000094568496402) else (if i < 123 then 0x3029000a20415002f05241804022099d481400904e46804290e8007800094e556800a8411e8095aa401150044125b1c14e50100882a44e8140241009516441519c00a004925882a4 else 0xa91cc931fa480a00000fc0000028098802728007e017aa91a40005002100400000820000b4808ad2a004000a6a00148cc0097c029220a9082645217804410000082b978010d010)) else (if i < 126 then (if i < 125 then 0x6400082ad00002060101008940055800823f02321a4081d849720400015a4430400014a42a0040e000422124c83004148030810400002d2b572e5041c172a400014821002800a802 else 0x4a000020000810003e05008723f49000006d02005469721b4946a46a3a800045d349a8ad00804025f00000ceb938a8da40500c0c00f9000096ee556b2c86022098000c8008007ed3) else (if i < 127 then 0x28c82d21fa90009200800ce015c8495a7f3380814fe0029094000004482410202086ba00ab420e5208041400000055a012a00000546900000401cb21082e0028c8200003487ea3 else 0x142a0033951a6107300010006381082a401000ce0a6432000547210546007804cce0002a914841729507e010019da44a0000000040000000f0003d802c8000fc0288208008267))))

def slotBlock8 (i : Nat) : Nat :=
  (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x19c7c013a80194010000148ba250000a01000040aa333804206720800200020b30040000b2082a40000548cf51a90a0007299c20410090400042a2900000008057241523480201 else 0x208fc02544939400a47c8054674023c15ad2002f424005210400f40019c000020b94004b00005e0ad0019c0800000007e006900000413800400d23380400a31f800bca41f8208201) else (if i < 131 then 0x1f8287e0220801ca0002a9124540095402044a248a80120904080400ae80abd2a248bc700080082d20104c7ead01028004138005484104009caa40029000080010000a4000014816 else 0xfc140056b982ac80090400000000000055219c820000000c800040000aa40024990f00000000ba72904ce00003c082670084dcc0100004504156b4882001f858007472800a85e)) else (if i < 134 then (if i < 133 then 0x179e800000015a0167801ca01340000008521054800390fc00010510c92410110548ad0098800672a004004a02904000100008865a258080001008019041391680054020000000 else 0x6900400ad009d8ce0051848ce84252b40204090080000208007e1033814043f51ac8005356a8c00ad000003a680196c144100041a400853487e00520040242001d400b2729c80a00) else (if i < 135 then 0x280000a456a5c110400000040a00001640000321a40100028046d40800a8d35201148002a001a4a43900610670800002002a000b467008fd08004b035480a2a150020000b480002 else 0x80146705e8fc020200904040000104004b029047e1600040a8000022008405200804f41fa90a83f008017a003919c024100290a8005680524a4208087e547281404010019c7e41))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x3f2918e0100008007700020000063004e4670090400a202a9000410219800e50081094415c95014043399802005201405030035c02a32a0002c100503d48ad01801485e028000041 else 0x2a0000202422b55aa40000c00045204000d2691507e72040100000690007e54010fc02000032c026701808040200004000000258d066520140407053f40200002e40000000080068) else (if i < 139 then 0x829ca3f028007e085c8008c3f20804020020c14000000001c8a400800000000000000401b4916c80101148014419c00a400000010820c0c003d0080800012180c00000119c00fa else 0x20800a800252c5ca082a040825445805e0d2000040a416919c000a520080401002e4e4434912c0002000000a015194004f90095000640028c003f3399ce80a2d1cd4800028057408)) else (if i < 142 then (if i < 141 then 0x202008002e414881c8287c721fb49f2e500000ce10781055a0000040820a09800000a002b4004179000000500a8c020833801e0d2090200241208fc04410012dca0156ab548ad else 0x1e904ce02080ac026300004e4010119c000100291d800000000a050095004e500004a84100104d000000015a00021695a0000000a90a3428c810300000dc674902814003a1d00000) else (if i < 143 then 0x51001e094209a02e0000001caa40421000b220904a8003b82094e500104828102b480041202747e003f179ca082a00000001f95004a40102800544200000b969001ce0203b48d000 else 0x100000e5090007e000800148000000000000103004017e0eca83425ab80201020d476f02080400a4440047e67251c948a42a3c8084b20905020002048947242248860078008023f))))

def slotBlock9 (i : Nat) : Nat :=
  (if i < 151 then (if i < 147 then (if i < 145 then 0x928ce0000a90a292000000a015200014701f800829237001480b00180040800000003f52005240020b9c000051b4802925e289cd00020fd5a001c8140002339b482681f8000004 else (if i < 146 then 0x6933dcae5338000016008000a00692d5a4051780002b930001caad522900a0801000820000000a8002a009dc3f0a9c8e4d251808023900000008434274020151a04041f00004023f else 0x2182000d272814724120800ce4a000fc02022a2b40000420000400522b40800692c402000900002011e90ccec852151a46600001486700009caf9029040866301a14601301a08200)) else (if i < 149 then (if i < 148 then 0x828002872928946851809a43f3b8fd100200a91ca7f023a4030352020d00063000140000820005b491e47ea4678000084002b420082a28ca200020400008000000204700010e96 else 0x88000002f375ca000281000025d0000000780007a3f003500002003495a00209040008660f8ac402f349ce4301000e8a2028012e1033804025401104ce015200010d21fb940808) else (if i < 150 then 0x20a895a040000990010100400700080800007800000882080004e5022907a1002ac9ca00521059204000412cd20801000e5002e548a41381124023399df6a426a8d4800008080043 else 0x414000010c025425151a4a423809780056b2002020080001052824948017292c0210009040468002c5a80100000821000000009256a500801009047e0a1fb49484156829ca67))) else (if i < 155 then (if i < 153 then (if i < 152 then 0xd821728400804024120848a8d0042907e63202055a720035c00a40029082012f1c9a4543037a16540120802a402028ce06021295a670000010ad52029a468002c55a102a000003f else 0x4b0000a00568281400002495acf00ab402466932000a400841cab91eb99a4432d3c002ad0080000a4690007c541cae80440008047ed205128820200151c88158804a8a4520040090) else (if i < 154 then 0x51800023f63904ce005690c006401249483f490ec00041f80408a456a900041000015a413b800941052000000005394000051128000a0000400d21d801fed200028060320a900400 else 0x7800000177b940454209502c9633800089d2a33c023f001507c94728047e0220a18000158804a201208980007000080080000115a0053104000000000b4fe080010800001048200)) else (if i < 157 then (if i < 156 then 0x528c00e50b2907e4120820003f020087e3f1f80000012a0007e004919c144a4402800160000148001c9c804d20a1040400700055a1f00000823f2a104820069005480052128d067 else 0x20ac9460549395249269048967e49904003f230214800001041400002e400945c99da4e600004a8430000c0096641c9724152000a80500029ce1000ae40023339f8010949001a400) else (if i < 158 then 0x5680082540080148022080000b2522c820000002804b91f80002000402190a351820020a0000002cf4b1a00002003480000008e408a37c8081049728d0000800104100281a900001 else 0x3f00800000f))))

def slot (i : Nat) : Nat :=
  let b := i / 64
  let g := b / 16
  let a := (if g < 5 then (if g < 2 then (if g < 1 then slotBlock0 b else slotBlock1 b) else (if g < 3 then slotBlock2 b else (if g < 4 then slotBlock3 b else slotBlock4 b))) else (if g < 7 then (if g < 6 then slotBlock5 b else slotBlock6 b) else (if g < 8 then slotBlock7 b else (if g < 9 then slotBlock8 b else slotBlock9 b))))
  (a >>> ((i % 64)*9)) % 512


def selected0 (i : Nat) : Option Hint :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then some (0xdbedc0000d93e180000032acd3000000cd3703, 0, 0) else some (0x3ff8cd93e1800000000000000000000000, 95, 1)) else (if i < 3 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 2) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 3))) else (if i < 6 then (if i < 5 then some (0xc7e3c000038f187800000e63cf0000003cf0f0, 4, 4) else some (0xffc0000000fff80000001fff000000000fff, 0, 5)) else (if i < 7 then some (0x70301c1c020030060180180200701c018007000, 12, 6) else some (0x7c1f07f07f800000000001fc1fe03f00f, 0, 7)))) else (if i < 12 then (if i < 10 then (if i < 9 then some (0x24ffc0000024fff80000441fff000001100fff, 0, 8) else some (0x7b007ec01b10006e180736001f00001b86000b30, 4, 9)) else (if i < 11 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 10) else some (0xedc0000000f1e00000000cd70000000007c7, 0, 11))) else (if i < 14 then (if i < 13 then some (0x12012441100ffffffffffff, 0, 12) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 13)) else (if i < 15 then some (0xedfc78cd77c7, 0, 14) else some (0x7ff801fff003ffe000fff, 0, 15)))))

def selected1 (i : Nat) : Option Hint :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then some (0x30702c0c0100c0038380600400c02c00e00c000, 14, 16) else some (0x70301c1c000030000180180200301c000003000, 12, 17)) else (if i < 19 then some (0xedc0000000e1800000000cd3000000000703, 0, 18) else some (0xedf860cd3703, 0, 19))) else (if i < 22 then (if i < 21 then some (0xc7e3c000038f187800000e63cf0000003cf0f0, 4, 20) else some (0x7c1f07f07f800000000001fc1fe03f00f, 0, 21)) else (if i < 23 then some (0xc7830000038f106800000e614d0000003cf0d0, 4, 22) else some (0xc7830000038f106800000e614d0000003cf0d0, 4, 23)))) else (if i < 28 then (if i < 26 then (if i < 25 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 24) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 25)) else (if i < 27 then some (0x7ff80116d003ffe000cdd, 0, 26) else some (0x7ff80116d003ffe000cdd, 0, 27))) else (if i < 30 then (if i < 29 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 28) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 29)) else (if i < 31 then some (0x7ff801fff0024ba000cdd, 0, 30) else some (0x7ff801fff0024ba000cdd, 0, 31)))))

def selected2 (i : Nat) : Option Hint :=
  (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 32) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 33)) else (if i < 35 then some (0x7ff801fff003ffe000fff, 0, 34) else some (0x7c1f07f07f800000000001300ba02d00d, 0, 35))) else (if i < 38 then (if i < 37 then some (0x7c1f07f07f800000000001300ba02d00d, 0, 36) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 37)) else (if i < 39 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 38) else some (0xc7e3c000038f081800000e23c30000003c3030, 4, 39)))) else (if i < 44 then (if i < 42 then (if i < 41 then some (0x7ed800045003f7c0004c5, 0, 40) else some (0x7ed800045003f7c0004c5, 0, 41)) else (if i < 43 then some (0xff007ec03ff0006e1807ff801f00003ff6000b30, 4, 42) else some (0x7ff801fff0024380004c5, 0, 43))) else (if i < 46 then (if i < 45 then some (0x7c1f05b05f00000000000010038005005, 0, 44) else some (0x7c1f05b05f00000000000010038005005, 0, 45)) else (if i < 47 then some (0x3fffffffffd800000000007edb87f00b30, 4, 46) else some (0xffedc0000fffe18000007fecd3000001ffb703, 0, 47)))))

def selected3 (i : Nat) : Option Hint :=
  (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then some (0xf7e02280000000000000001fbe85c, 2, 48) else some (0xf7e02280000000000000001fbe85c, 2, 49)) else (if i < 51 then some (0x7fffffffffbedf860cd3703, 0, 50) else some (0x639870e638e02000a10c050, 4, 51))) else (if i < 54 then (if i < 53 then some (0x639870e638e02000a10c050, 4, 52) else some (0x7c1f07f07f8000000000012008a02c00c, 2, 53)) else (if i < 55 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 54) else some (0xffc0000000fff80000001fff000000000fff, 0, 55)))) else (if i < 60 then (if i < 58 then (if i < 57 then some (0x21c7224840020c000639060c0300224000300000, 20, 56) else some (0xffffff80000000000000001ffffff, 0, 57)) else (if i < 59 then some (0x1f120987c0c01301809009800000098060000000, 29, 58) else some (0xffffffffffff, 0, 59))) else (if i < 62 then (if i < 61 then some (0x63c762d8c2120c081e39060c030062c206300030, 4, 60) else some (0x1f1b0dc7c0c0130180d80980a0130dc060013003, 0, 61)) else (if i < 63 then some (0x1edb1e6c6e1800000000007edb87f00b30, 4, 62) else some (0x6dec9b2acd3edf860cd3703, 0, 63)))))

def selected4 (i : Nat) : Option Hint :=
  (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then some (0x30702c0c0100c0018380600000002c006000000, 25, 64) else some (0xffffffffffff, 0, 65)) else (if i < 67 then some (0x30702c0c0100c0038380600400c02c00e00c000, 14, 66) else some (0x8400ffc0204000fff80040801fff002020000fff, 0, 67))) else (if i < 70 then (if i < 69 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 68) else some (0x7ec00000006e380000001f2c000000000b7c, 2, 69)) else (if i < 71 then some (0x2120408180800000000000ffffffffffff, 0, 70) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 71)))) else (if i < 76 then (if i < 74 then (if i < 73 then some (0x7edb8ff2cb7c, 2, 72) else some (0x7ec00000006e180000001f00000000000b30, 4, 73)) else (if i < 75 then some (0x7edb87f00b30, 4, 74) else some (0x741e07f07e000000000001f41f803f00f, 0, 75))) else (if i < 78 then (if i < 77 then some (0x1f001d0001f00007e0003d8000350001fc00000f, 0, 76) else some (0x7ff801fff002df8000dcf, 0, 77)) else (if i < 79 then some (0x7c1f07b07f000000000001d01f803500f, 0, 78) else some (0x1c001d0001e00007e000388000350001f800000f, 0, 79)))))

def selected5 (i : Nat) : Option Hint :=
  (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then some (0x701e07107e000000000001d01f803500f, 0, 80) else some (0x1c180d0700c0110180c0088080110d0060011003, 0, 81)) else (if i < 83 then some (0x304020080100400083006000000028006000000, 25, 82) else some (0x62c206300030, 4, 83))) else (if i < 86 then (if i < 85 then some (0x2060280c0100c00182002000000020002000000, 25, 84) else some (0x1475000000000dcf, 0, 85)) else (if i < 87 then some (0x1f00010001f0000060002d80000500017c000000, 26, 86) else some (0xfdbfdf000000000000000000450c0, 6, 87)))) else (if i < 92 then (if i < 90 then (if i < 89 then some (0x6018074072800000000001e01ca03c00e, 1, 88) else some (0xdbedc0000d93e180000032acd3000000cd3703, 0, 89)) else (if i < 91 then some (0x1edb1e6c6e180000000000120083100810, 4, 90) else some (0x1f120987c0c01301809009800000098060000000, 29, 91))) else (if i < 94 then (if i < 93 then some (0xffffffffffff, 0, 92) else some (0xc0e100000381186000000a02c50000002c50e0, 5, 93)) else (if i < 95 then some (0xc7e10000038f186000000e62c50000003cf0e0, 5, 94) else some (0x18001c0001000006000030000000000180000000, 31, 95)))))

def selected6 (i : Nat) : Option Hint :=
  (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then some (0x3c702c8c0120c001a38060c000022c006300000, 20, 96) else some (0xe0c0e038000180000600c00200c0e000000c0000, 18, 97)) else (if i < 99 then some (0x639c78e63cfe106182c50e0, 5, 98) else some (0x234722c0c0100c001e39060c030002c006000000, 25, 99))) else (if i < 102 then (if i < 101 then some (0xd2e980000d93e18000002208c10000008c1601, 0, 100) else some (0x7c1f07f07d800000000001ec186000000, 25, 101)) else (if i < 103 then some (0xc0e000000380180000000a02c00000002c00a0, 5, 102) else some (0x601c00a02c0e006002c00a0, 5, 103)))) else (if i < 108 then (if i < 106 then (if i < 105 then some (0xc480c139062381186000408000458104180450c0, 6, 104) else some (0xc0e100000381186000000a02c50000002c50e0, 5, 105)) else (if i < 107 then some (0xc7e00000038e180000000e62c00000003ca0a0, 5, 106) else some (0x639c70e63cae006002c00a0, 5, 107))) else (if i < 110 then (if i < 109 then some (0x601c08a02c5e106182c50e0, 5, 108) else some (0xc7020000030e002800000e610c00000038e050, 4, 109)) else (if i < 111 then some (0x639870e638e02000a10c050, 4, 110) else some (0xc7e2c000038c181800000e03c00000003c00b0, 4, 111)))))

def selected7 (i : Nat) : Option Hint :=
  (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then some (0x639c60e03c0e2c6063c00b0, 4, 112) else some (0xffc0000000fff80000001fff000000000fff, 0, 113)) else (if i < 115 then some (0xffffdf00000000000000001fff4c5, 0, 114) else some (0xc7810000038f106000000e60450000003cf0c0, 6, 115))) else (if i < 118 then (if i < 117 then some (0xdb8100000d938080000032a041000000cd3401, 0, 116) else some (0x6000620002000008080102000300000202000030, 4, 117)) else (if i < 119 then some (0x736001f00000000000000, 56, 118) else some (0x1b10006e180000000000000082000810, 4, 119)))) else (if i < 124 then (if i < 122 then (if i < 121 then some (0x280080600503401800f000, 12, 120) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 121)) else (if i < 123 then some (0xc0e100000380186000000a02c50000002c00e0, 5, 122) else some (0x7c1f05b05f00000000000000038000005, 0, 123))) else (if i < 126 then (if i < 125 then some (0xf7e02280000000000000001fbe85c, 2, 124) else some (0xdbedc0000d93e180000032acd3000000cd3703, 0, 125)) else (if i < 127 then some (0x60c46218020204080e21020c0300620202300030, 4, 126) else some (0xd2e980000d93e18000002208c00000008c0600, 9, 127)))))

def selected8 (i : Nat) : Option Hint :=
  (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then some (0xff00000038c000000006c9800000003860000000, 29, 128) else some (0x18007ec00900006e180230001f00000980000b30, 4, 129)) else (if i < 131 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 130) else some (0x7ed800045003f7c0004c5, 0, 131))) else (if i < 134 then (if i < 133 then some (0x7ff801fff003f7c0004c5, 0, 132) else some (0x29007ec00000006e180736001f00000000000b30, 4, 133)) else (if i < 135 then some (0x1f00000580c00000009009800000098060000000, 29, 134) else some (0x496c9800000c9b860000000, 29, 135)))) else (if i < 140 then (if i < 138 then (if i < 137 then some (0x7ed800045003f7c0004c5, 0, 136) else some (0x1f001c0001f0000700003d8000300001f400000a, 1, 137)) else (if i < 139 then some (0x1f00010001f00000e0002d80000500017c000005, 0, 138) else some (0x7ff801fba003f74000000, 26, 139))) else (if i < 142 then (if i < 141 then some (0x1f00010001f00000e0002d80000500017c000005, 0, 140) else some (0x7ed800045003f7c0004c5, 0, 141)) else (if i < 143 then some (0x3e4000000026000000001f00000000000900, 8, 142) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 143)))))

def selected9 (i : Nat) : Option Hint :=
  (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then some (0x7ff801f00003ff6000b30, 4, 144) else some (0xffffffffffff, 0, 145)) else (if i < 147 then some (0x639c78e63cf8104180450c0, 6, 146) else some (0x6dec9b2acd3812020041401, 0, 147))) else (if i < 150 then (if i < 149 then some (0x721283b00a30, 4, 148) else some (0xe6c00000000000000000001f00000, 20, 149)) else (if i < 151 then some (0x1b100002080000000000001b86000810, 4, 150) else some (0x503400000010060000000600f000000005000, 12, 151)))) else (if i < 156 then (if i < 154 then (if i < 153 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 152) else some (0x601c00a02c0e106182c50e0, 5, 153)) else (if i < 155 then some (0x7ed800000003f7c0004c5, 0, 154) else some (0x639870e638e02000a10c050, 4, 155))) else (if i < 158 then (if i < 157 then some (0xdbedc0000d93e180000032acd3000000cd3703, 0, 156) else some (0x696c9a208c0e9b8608c0600, 9, 157)) else (if i < 159 then some (0x6090460260000000000007edb87f00b30, 4, 158) else some (0xa400e6c000000000000007edb87f00b30, 4, 159)))))

def selected10 (i : Nat) : Option Hint :=
  (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 160) else some (0x7c1f05b05f00000000000010038005005, 0, 161)) else (if i < 163 then some (0x16120987c0c01301800000000000000000000000, 95, 162) else some (0xfdbfdd00000000000000000000000, 92, 163))) else (if i < 166 then (if i < 165 then some (0x7c1f05b05f00000000000010038005005, 0, 164) else some (0x7c1f07b07d000000000001c01c003000a, 1, 165)) else (if i < 167 then some (0xffffdd00000000000000001fba000, 13, 166) else some (0xfdbfdf000000000000000000454c5, 0, 167)))) else (if i < 172 then (if i < 170 then (if i < 169 then some (0x6018074072800000000001e01ca03c00e, 1, 168) else some (0xf7e02280000000000000001fbe85c, 2, 169)) else (if i < 171 then some (0x3ea307c1400000000000000, 58, 170) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 171))) else (if i < 174 then (if i < 173 then some (0xd93e1800000000000000000000000, 95, 172) else some (0x1f001dc001c000078000398000330001e000000b, 0, 173)) else (if i < 175 then some (0x7c1c073078000000000001dc1e003300b, 0, 174) else some (0xffffffffffff, 0, 175)))))

def selected11 (i : Nat) : Option Hint :=
  (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then some (0x18001e000180000728003a00003c0001ca00000e, 1, 176) else some (0x18381c060100600601c0300000001c0180000000, 31, 177)) else (if i < 179 then some (0x1f0301c5c0c0030000980980200309c060003000, 12, 178) else some (0x1f001e0001f0000728003f80003c0001fe00000e, 1, 179))) else (if i < 182 then (if i < 181 then some (0x639c78e63cbe1c0000c3000, 12, 180) else some (0x39003e4009000026080736001f00000982000910, 4, 181)) else (if i < 183 then some (0x171309c7c0c0130180180180200301c000003000, 12, 182) else some (0x7c1f07f07f800000000001e01ca03c00e, 1, 183)))) else (if i < 188 then (if i < 186 then (if i < 185 then some (0x18001c0009000026000230001400000980000900, 8, 184) else some (0x6018070070000000000001c01c003000a, 1, 185)) else (if i < 187 then some (0x82c16000000240229e03a01c03c12008a02c00c, 2, 186) else some (0x1f001c0001f0000700003d8000300001f400000a, 1, 187))) else (if i < 190 then (if i < 189 then some (0x6018074072800000000001e01ca03c00e, 1, 188) else some (0x7c1f07b07d000000000001c01c003000a, 1, 189)) else (if i < 191 then some (0xc7020000030e002800000e600c00000038e000, 13, 190) else some (0x639870e638e02000a00c000, 14, 191)))))

def selected12 (i : Nat) : Option Hint :=
  (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then some (0x21c7224840020c000639060c0300224000300000, 20, 192) else some (0xc7e20000038e182800000e63cc0000003ce0f0, 4, 193)) else (if i < 195 then some (0x7ff801bec003ffe000efc, 2, 194) else some (0x639c70e63cee2060a3cc0f0, 4, 195))) else (if i < 198 then (if i < 197 then some (0xc6e38000038f187800000e43cc0000003cc0f0, 4, 196) else some (0xc4e200000384182800000e43cc0000003cc0f0, 4, 197)) else (if i < 199 then some (0x621c20e43cce2060a3cc0f0, 4, 198) else some (0xdc000000001800000000013000000000003, 0, 199)))) else (if i < 204 then (if i < 202 then (if i < 201 then some (0xda280000000000000000000efc, 2, 200) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 201)) else (if i < 203 then some (0xfffe1800000000000000001ffb703, 0, 202) else some (0xff0000000e6c000000007c0000000001f00000, 20, 203))) else (if i < 206 then (if i < 205 then some (0xc0edc0000980e1800000220cd30000008c0703, 0, 204) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 205)) else (if i < 207 then some (0xf7e02280000000000000001fbe85c, 2, 206) else some (0x92edc0000d93e1800000000cd3000000000703, 0, 207)))))

def selected13 (i : Nat) : Option Hint :=
  (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then some (0xffffff80000000000000001fbe85c, 2, 208) else some (0xc7000000030e000000000e600000000038a000, 13, 209)) else (if i < 211 then some (0xa400e6c00000000000000364001f00000, 20, 210) else some (0xc7020000030e002800000e610c00000038e050, 4, 211))) else (if i < 214 then (if i < 213 then some (0xc7e00000038e180000000e62c00000003ca0a0, 5, 212) else some (0xffffdd00000000000000001fba000, 13, 213)) else (if i < 215 then some (0xf600000038c000000004c0000000003000000000, 36, 214) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 215)))) else (if i < 220 then (if i < 218 then (if i < 217 then some (0x6018074072800000000001c01c003c00e, 1, 216) else some (0x639870e638e00000010c050, 4, 217)) else (if i < 219 then some (0x39003e4009000026000736001f00000980000900, 8, 218) else some (0x7ff801fbe003ffe00085c, 2, 219))) else (if i < 222 then (if i < 221 then some (0x1f00120001f0000228003f80002c0001fe00000c, 2, 220) else some (0x18030040028000000000003801e00c000, 14, 221)) else (if i < 223 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 222) else some (0x7ff367c1f00000000000000, 56, 223)))))

def selected14 (i : Nat) : Option Hint :=
  (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then some (0x604c02208c0edf860cd3703, 0, 224) else some (0x496c9800000edf860cd3703, 0, 225)) else (if i < 227 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 226) else some (0x7bf001fbe00008a00085c, 2, 227))) else (if i < 230 then (if i < 229 then some (0x21452240000000000639060c0300000000000000, 56, 228) else some (0x2900364000000000000736001f00000000000000, 56, 229)) else (if i < 231 then some (0x639870e638e02000a10c050, 4, 230) else some (0x639c70e63cae006002c00a0, 5, 231)))) else (if i < 236 then (if i < 234 then (if i < 233 then some (0x7ff801fba003f74000000, 26, 232) else some (0xe9b8608c0600, 9, 233)) else (if i < 235 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 234) else some (0x6018070070000000000001e01ca03c00e, 1, 235))) else (if i < 238 then (if i < 237 then some (0xc7000000030e000000000e610c00000038e050, 4, 236) else some (0xe490e6c260000000000003e4981f00900, 8, 237)) else (if i < 239 then some (0x7c1f07f07f8000000000012008a02c00c, 2, 238) else some (0x600c00200c0e000000c0000, 18, 239)))))

def selected15 (i : Nat) : Option Hint :=
  (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then some (0xc3800000001878000000010c000000000050, 4, 240) else some (0xe490e6c260000000000003e4981f00900, 8, 241)) else (if i < 243 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 242) else some (0x82e3c000038b187800000003cf0000000000f0, 4, 243))) else (if i < 246 then (if i < 245 then some (0x1edb1e6c6e1000000000003e4981f00900, 8, 244) else some (0x7b003e401b100026000736001f00001b84000900, 8, 245)) else (if i < 247 then some (0x1f1a0d87c0c0130180d0098080100d8060010002, 1, 246) else some (0xe3c00000001850000000038a000000000000, 49, 247)))) else (if i < 252 then (if i < 250 then (if i < 249 then some (0x39003e4009000026000736001f00000980000900, 8, 248) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 249)) else (if i < 251 then some (0x5c1f00f007800000000000bc17e00f000, 12, 250) else some (0x639c78e63cfe3c61e3cf0f0, 4, 251))) else (if i < 254 then (if i < 253 then some (0x380580600003c01400a000, 13, 252) else some (0x1f001fc001f00007f8003f80003f0001fe00000f, 0, 253)) else (if i < 255 then some (0x61c7625842020c080639060c0300624200300020, 5, 254) else some (0xdbe980000d93e180000032a8c0000000cd2600, 9, 255)))))

def selected16 (i : Nat) : Option Hint :=
  (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then some (0x70003c00030000050000700000a000000000000, 49, 256) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 257)) else (if i < 259 then some (0x696c9a208c0e9b8608c0600, 9, 258) else some (0x4723c000000f007800000e638f00000000f000, 12, 259))) else (if i < 262 then (if i < 261 then some (0x6dec9b2acd2e9b8608c0600, 9, 260) else some (0x1c0300e0000000000000003c01400a000, 13, 261)) else (if i < 263 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 262) else some (0xdc060013003, 0, 263)))) else (if i < 268 then (if i < 266 then (if i < 265 then some (0xd2e980000d93e18000002208c00000008c0600, 9, 264) else some (0x240007e000000000000001fc1fe03f00f, 0, 265)) else (if i < 267 then some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 266) else some (0xb80fff80000000000000000ac0fff, 0, 267))) else (if i < 270 then (if i < 269 then some (0x1ef0000000000faa, 1, 268) else some (0xffffff80000000000000001ffffff, 0, 269)) else (if i < 271 then some (0xff000000000000000000000faa, 1, 270) else some (0x70703c1c0300f0078380780600f03c01e00f000, 12, 271)))))

def selected17 (i : Nat) : Option Hint :=
  some (0x238001fff0009c0000fff, 0, 272)

def advice (k : Nat) : Option Hint :=
  let d := displace (k % 1960)
  let q := slot ((k/1960 + d*(k % 104729+1)) % 10118)
  if q = 0 then none else
    let i := q-1
    let g := i/16
    (if g < 9 then (if g < 4 then (if g < 2 then (if g < 1 then selected0 i else selected1 i) else (if g < 3 then selected2 i else selected3 i)) else (if g < 6 then (if g < 5 then selected4 i else selected5 i) else (if g < 7 then selected6 i else (if g < 8 then selected7 i else selected8 i)))) else (if g < 13 then (if g < 11 then (if g < 10 then selected9 i else selected10 i) else (if g < 12 then selected11 i else selected12 i)) else (if g < 15 then (if g < 14 then selected13 i else selected14 i) else (if g < 16 then selected15 i else (if g < 17 then selected16 i else selected17 i)))))

def rootF (i : Nat) : Bool :=
  ((pairs inputs)[i]?).any (fun (a,b,rest) => dispatch 4 (front claims advice 1 10) a b rest)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier0 : rootF 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier1 : rootF 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier2 : rootF 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier3 : rootF 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier4 : rootF 4 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier5 : rootF 5 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier6 : rootF 6 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier7 : rootF 7 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier8 : rootF 8 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier9 : rootF 9 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier10 : rootF 10 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier11 : rootF 11 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier12 : rootF 12 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier13 : rootF 13 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier14 : rootF 14 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier15 : rootF 15 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier16 : rootF 16 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier17 : rootF 17 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier18 : rootF 18 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier19 : rootF 19 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier20 : rootF 20 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier21 : rootF 21 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier22 : rootF 22 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier23 : rootF 23 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier24 : rootF 24 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier25 : rootF 25 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier26 : rootF 26 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem frontier27 : rootF 27 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem all_front : front claims advice 2 11 4 inputs = false := by
  have hlen : (pairs inputs).length = 28 := by decide
  have allRoots : ∀ i : Fin 28, rootF i.val = false := by
    intro i
    fin_cases i
    · exact frontier0
    · exact frontier1
    · exact frontier2
    · exact frontier3
    · exact frontier4
    · exact frontier5
    · exact frontier6
    · exact frontier7
    · exact frontier8
    · exact frontier9
    · exact frontier10
    · exact frontier11
    · exact frontier12
    · exact frontier13
    · exact frontier14
    · exact frontier15
    · exact frontier16
    · exact frontier17
    · exact frontier18
    · exact frontier19
    · exact frontier20
    · exact frontier21
    · exact frontier22
    · exact frontier23
    · exact frontier24
    · exact frontier25
    · exact frontier26
    · exact frontier27
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [front, Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with stop | step
  · exact (by decide : (inputs == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := allRoots (Fin.cast hlen i)
    simp only [Fin.val_cast, rootF, List.getElem?_eq_getElem i.isLt, Option.any_some] at no
    rw [← hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem all_claims : claims.all goodClaim = true := by
  simp only [claims, List.all_cons, List.all_nil, Bool.true_and,
    checkedSet0_ok, checkedSet1_ok, checkedSet2_ok, checkedSet3_ok, checkedSet4_ok, checkedSet5_ok, checkedSet6_ok, checkedSet7_ok, checkedSet8_ok, checkedSet9_ok, checkedSet10_ok, checkedSet11_ok, checkedSet12_ok, checkedSet13_ok, checkedSet14_ok, checkedSet15_ok, checkedSet16_ok, checkedSet17_ok, checkedSet18_ok, checkedSet19_ok, checkedSet20_ok, checkedSet21_ok, checkedSet22_ok, checkedSet23_ok, checkedSet24_ok, checkedSet25_ok, checkedSet26_ok, checkedSet27_ok, checkedSet28_ok, checkedSet29_ok, checkedSet30_ok, checkedSet31_ok, checkedSet32_ok, checkedSet33_ok, checkedSet34_ok, checkedSet35_ok, checkedSet36_ok, checkedSet37_ok, checkedSet38_ok, checkedSet39_ok, checkedSet40_ok, checkedSet41_ok, checkedSet42_ok, checkedSet43_ok, checkedSet44_ok, checkedSet45_ok, checkedSet46_ok, checkedSet47_ok, checkedSet48_ok, checkedSet49_ok, checkedSet50_ok, checkedSet51_ok, checkedSet52_ok, checkedSet53_ok, checkedSet54_ok, checkedSet55_ok, checkedSet56_ok, checkedSet57_ok, checkedSet58_ok, checkedSet59_ok, checkedSet60_ok, checkedSet61_ok, checkedSet62_ok, checkedSet63_ok, checkedSet64_ok, checkedSet65_ok, checkedSet66_ok, checkedSet67_ok, checkedSet68_ok, checkedSet69_ok, checkedSet70_ok, checkedSet71_ok, checkedSet72_ok, checkedSet73_ok, checkedSet74_ok, checkedSet75_ok, checkedSet76_ok, checkedSet77_ok, checkedSet78_ok, checkedSet79_ok, checkedSet80_ok, checkedSet81_ok, checkedSet82_ok, checkedSet83_ok, checkedSet84_ok, checkedSet85_ok, checkedSet86_ok, checkedSet87_ok, checkedSet88_ok, checkedSet89_ok, checkedSet90_ok, checkedSet91_ok, checkedSet92_ok, checkedSet93_ok, checkedSet94_ok, checkedSet95_ok, checkedSet96_ok, checkedSet97_ok, checkedSet98_ok, checkedSet99_ok, checkedSet100_ok, checkedSet101_ok, checkedSet102_ok, checkedSet103_ok, checkedSet104_ok, checkedSet105_ok, checkedSet106_ok, checkedSet107_ok, checkedSet108_ok, checkedSet109_ok, checkedSet110_ok, checkedSet111_ok, checkedSet112_ok, checkedSet113_ok, checkedSet114_ok, checkedSet115_ok, checkedSet116_ok, checkedSet117_ok, checkedSet118_ok, checkedSet119_ok, checkedSet120_ok, checkedSet121_ok, checkedSet122_ok, checkedSet123_ok, checkedSet124_ok, checkedSet125_ok, checkedSet126_ok, checkedSet127_ok, checkedSet128_ok, checkedSet129_ok, checkedSet130_ok, checkedSet131_ok, checkedSet132_ok, checkedSet133_ok, checkedSet134_ok, checkedSet135_ok, checkedSet136_ok, checkedSet137_ok, checkedSet138_ok, checkedSet139_ok, checkedSet140_ok, checkedSet141_ok, checkedSet142_ok, checkedSet143_ok, checkedSet144_ok, checkedSet145_ok, checkedSet146_ok, checkedSet147_ok, checkedSet148_ok, checkedSet149_ok, checkedSet150_ok, checkedSet151_ok, checkedSet152_ok, checkedSet153_ok, checkedSet154_ok, checkedSet155_ok, checkedSet156_ok, checkedSet157_ok, checkedSet158_ok, checkedSet159_ok, checkedSet160_ok, checkedSet161_ok, checkedSet162_ok, checkedSet163_ok, checkedSet164_ok, checkedSet165_ok, checkedSet166_ok, checkedSet167_ok, checkedSet168_ok, checkedSet169_ok, checkedSet170_ok, checkedSet171_ok, checkedSet172_ok, checkedSet173_ok, checkedSet174_ok, checkedSet175_ok, checkedSet176_ok, checkedSet177_ok, checkedSet178_ok, checkedSet179_ok, checkedSet180_ok, checkedSet181_ok, checkedSet182_ok, checkedSet183_ok, checkedSet184_ok, checkedSet185_ok, checkedSet186_ok, checkedSet187_ok, checkedSet188_ok, checkedSet189_ok, checkedSet190_ok, checkedSet191_ok, checkedSet192_ok, checkedSet193_ok, checkedSet194_ok, checkedSet195_ok, checkedSet196_ok, checkedSet197_ok, checkedSet198_ok, checkedSet199_ok, checkedSet200_ok, checkedSet201_ok, checkedSet202_ok, checkedSet203_ok, checkedSet204_ok, checkedSet205_ok, checkedSet206_ok, checkedSet207_ok, checkedSet208_ok, checkedSet209_ok, checkedSet210_ok, checkedSet211_ok, checkedSet212_ok, checkedSet213_ok, checkedSet214_ok, checkedSet215_ok, checkedSet216_ok, checkedSet217_ok, checkedSet218_ok, checkedSet219_ok, checkedSet220_ok, checkedSet221_ok, checkedSet222_ok, checkedSet223_ok, checkedSet224_ok, checkedSet225_ok, checkedSet226_ok, checkedSet227_ok, checkedSet228_ok, checkedSet229_ok, checkedSet230_ok, checkedSet231_ok, checkedSet232_ok, checkedSet233_ok, checkedSet234_ok, checkedSet235_ok, checkedSet236_ok, checkedSet237_ok, checkedSet238_ok, checkedSet239_ok, checkedSet240_ok, checkedSet241_ok, checkedSet242_ok, checkedSet243_ok, checkedSet244_ok, checkedSet245_ok, checkedSet246_ok, checkedSet247_ok, checkedSet248_ok, checkedSet249_ok, checkedSet250_ok, checkedSet251_ok, checkedSet252_ok, checkedSet253_ok, checkedSet254_ok, checkedSet255_ok, checkedSet256_ok, checkedSet257_ok, checkedSet258_ok, checkedSet259_ok, checkedSet260_ok, checkedSet261_ok, checkedSet262_ok, checkedSet263_ok, checkedSet264_ok, checkedSet265_ok, checkedSet266_ok, checkedSet267_ok, checkedSet268_ok, checkedSet269_ok, checkedSet270_ok, checkedSet271_ok, checkedSet272_ok]

end Check516

theorem PEqualNP.Outside.L_meta_516 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s := by
  exact Check516.lower_of_front _ _ _ Check516.all_claims Check516.all_front
