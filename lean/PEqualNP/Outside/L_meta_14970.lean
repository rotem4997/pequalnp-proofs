import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Convert
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14970

-- Adapted from the checked L-meta-528: the same verified search, with the rows of this graph.
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

namespace Live

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def constants (p : α → β) (c : β) (s : Finset α) := (s.filter (fun a => p a = c)).card

theorem count_insert (p : α → β) (c : β) (s : Finset α) (a : α) :
    constants p c (insert a s) = constants p c s + (if p a = c ∧ a ∉ s then 1 else 0) := by
  by_cases val : p a = c <;> by_cases mem : a ∈ s <;>
    simp [constants,Finset.filter_insert,val,mem,Finset.card_insert_of_notMem]

def Compatible (op : α → α → Finset α) (op' : β → β → Finset β) (p : α → β) (c : β) :=
  ∀ a b z, z ∈ op a b →
    (p a = c → p b = c → p z = c) ∧
    (p z = c ∨ p z = p a ∨ p z = p b ∨
      (p a ≠ c ∧ p b ≠ c ∧ p a ≠ p b ∧ p z ∈ op' (p a) (p b)))

theorem step_counts (p : α → β) (c : β) {a b z : α} (rest : Finset α)
    (hab : a ≠ b) (fresh : z ∉ rest) (zero : p a = c → p b = c → p z = c) :
    let before := constants p c (insert a (insert b rest))
    let after := constants p c (insert z rest)
    before ≤ after + 1 ∧
    (p a ≠ c → p b ≠ c → before ≤ after) ∧
    (a ∈ rest → p a = c → before ≤ after) ∧
    (a ∈ rest → b ∈ rest → p z = c → before + 1 ≤ after) := by
  simp only [count_insert,Finset.mem_insert,hab,false_or]
  by_cases ha : p a = c <;> by_cases hb : p b = c <;> by_cases hz : p z = c <;>
    by_cases ma : a ∈ rest <;> by_cases mb : b ∈ rest <;>
    simp_all <;> omega

theorem project {op : α → α → Finset α} {op' : β → β → Finset β}
    (p : α → β) (c : β) {target : α} (nonconstant : p target ≠ c) (compat : Compatible op op' p c)
    {k : Nat} {s : Finset α} (h : live op target k s) (pool : Finset β)
    (covers : ∀ a ∈ s, p a = c ∨ p a ∈ pool) :
    ∃ j, j + constants p c s ≤ k ∧ build op' (p target) j pool := by
  induction k generalizing s pool with
  | zero =>
    change s = {target} at h
    subst s
    exact ⟨0,by simp [constants,nonconstant],(covers target (by simp)).resolve_left nonconstant⟩
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,fresh,rest,shape,tail⟩
    · obtain ⟨j,bound,build⟩ := ih skip pool covers
      exact ⟨j,by omega,build⟩
    have sub : rest ⊆ s := by rw [shape]; intro w hw; simp [hw]
    obtain ⟨zero,profile⟩ := compat a b z hz
    have counts := step_counts p c rest hab (fun h => fresh (sub h)) zero
    rw [← shape] at counts
    by_cases old : p z = c ∨ p z ∈ pool
    · obtain ⟨j,bound,build⟩ := ih tail pool (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl|hw
        · exact old
        · exact covers w (sub hw))
      exact ⟨j,by have := counts.1; omega,build⟩
    · rcases profile with v|v|v|⟨na,nb,distinct,valid⟩
      · exact (old (.inl v)).elim
      · exact (old (v ▸ covers a ha)).elim
      · exact (old (v ▸ covers b hb)).elim
      have ca := (covers a ha).resolve_left na
      have cb := (covers b hb).resolve_left nb
      obtain ⟨j,bound,build⟩ := ih tail (insert (p z) pool) (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl|hw
        · exact .inr (Finset.mem_insert_self _ _)
        · exact (covers w (sub hw)).imp_right (Finset.mem_insert_of_mem ·))
      exact ⟨j+1,by have := counts.2.1 na nb; omega,
        Or.inr ⟨p a,ca,p b,cb,distinct,p z,valid,build⟩⟩

theorem build_pad {op : α → α → Finset α} {target : α} {s : Finset α}
    {m n : ℕ} (le : m ≤ n) (h : build op target m s) : build op target n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Live

namespace Check

abbrev W := BitVec 56
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 28)).setWidth 28
def cuts (ws : List W) : BitVec 28 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 28) ++ (0 : BitVec 28)))
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
  let attempt := fun (kept : List W) (covered : BitVec 28) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0x99291e798000e7, 0x2e22f800e00f8, 0x20000000000000, 0x40000000000000, 0x1c54f290000f00, 0x80000000000000, 0x7874520707000, 0x67f888467f8000]

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
def differs (i : Fin 28) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (28+i.val)

theorem neg_differs (i : Fin 28) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 56 := by omega
  have hi : 28+i.val < 56 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 28) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 28) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (28+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (28+i.val) := by simpa [differs] using h.2
  have lo : i.val < 56 := by omega
  have hi : 28+i.val < 56 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 28) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬28 + i.val < 28 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 28) :
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
  change (cuts ws)[j] = (BitVec.allOnes 28)[j]
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

private def bit (k : Fin 56) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 56) :
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
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 56 := by
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

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

-- The number of AND and OR gates: NOT gates are not charged by the search.
def nb : List Gate → ℕ
  | [] => 0
  | g :: gs => (bif isNot g.op then 0 else 1) + nb gs

theorem nb_le (gs : List Gate) : nb gs ≤ gs.length := by
  induction gs with
  | nil => simp [nb]
  | cons g gs ih =>
    simp only [nb, List.length_cons]
    cases isNot g.op <;> simp <;> omega

theorem nb_lt (gs : List Gate) : (∃ g ∈ gs, isNot g.op = true) → nb gs + 1 ≤ gs.length := by
  induction gs with
  | nil =>
    rintro ⟨g, hg, _⟩
    simp at hg
  | cons g gs ih =>
    rintro ⟨g', hg', hn⟩
    have le := nb_le gs
    rcases List.mem_cons.mp hg' with e | hin
    · subst e
      simp only [nb, List.length_cons, hn, cond_true]
      omega
    · have small := ih ⟨g', hin, hn⟩
      simp only [nb, List.length_cons]
      cases isNot g.op <;> simp <;> omega

private def possible1 (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u)

private theorem atom1 {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible1 ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible1]
  · simp only [possible1, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inr rfl⟩

set_option maxRecDepth 2000 in
private theorem gate_table_not (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g)
    (hn : isNot g.op = true) :
    ∃ z, possible1 ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  change isNot op = true at hn
  have hop' : op = .not := by
    rcases hop with rfl | rfl | rfl
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · rfl
  subst hop'
  cases args with
  | nil => exact ⟨-1, by simp [possible1], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      exact ⟨_, atom1 (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        exact ⟨_, atom1 (mem i), by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

theorem classify1 {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible1 ws z) : canon z = 0 ∨ canon z ∈ available := by
  simp only [possible1, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, (h | h)⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact hw _ hx
  · subst z; rw [canon_neg]; exact hw _ hx

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 28) ++ (0 : BitVec 28))) :
    Live.build basicOps goal (nb gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 28) ++ (0 : BitVec 28)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 28) ++ (0 : BitVec 28)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    have appendOK (z : W) (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    cases hn : isNot g.op with
    | true =>
      obtain ⟨z,hz,hstep⟩ := gate_table_not w w (fun _ h => h) g (hg g (by simp)) hn
      have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
          bit k ((-1 : BitVec 28) ++ (0 : BitVec 28)) := by
        intro k; simpa only [List.foldl_cons,hstep] using he k
      have hcount : nb (g :: gs) = nb gs := by simp [nb, hn]
      rw [hcount]
      exact ih (fun g' h => hg g' (by simp [h])) (w ++ [z]) av (appendOK z (classify1 hw hz)) he'
    | false =>
      obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
      have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
      have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
          bit k ((-1 : BitVec 28) ++ (0 : BitVec 28)) := by
        intro k; simpa only [List.foldl_cons,hstep] using he k
      have hcount : nb (g :: gs) = nb gs + 1 := by simp [nb, hn, Nat.add_comm]
      rw [hcount]
      rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
      · exact Or.inl (fn av (appendOK z (.inl h)) he')
      · exact Or.inl (fn av (appendOK z (.inr h)) he')
      · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
        · have eq : u = z := List.mem_singleton.mp hu
          subst eq
          exact Or.inr (Finset.mem_insert_self _ _)




def graph (x : Fin 8 → Bool) : Bool :=
  ((((x 0 || x 1) && (x 4 || x 5)) || (((x 0 || x 1) || (x 4 || x 5)) && x 6)) || (((x 0 || x 4) || (x 2 || x 3)) && x 7))

def assignment (k : Fin 56) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 28) := [8, 9, 25, 26, 0, 27, 1, 2]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (28+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 56) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 56) : graph (assignment k) =
    bit k ((-1 : BitVec 28) ++ (0 : BitVec 28)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : ((((x 0 ||| x 1) &&& (x 4 ||| x 5)) ||| (((x 0 ||| x 1) ||| (x 4 ||| x 5)) &&& x 6)) ||| (((x 0 ||| x 4) ||| (x 2 ||| x 3)) &&& x 7)) = ((-1 : BitVec 28) ++ (0 : BitVec 28)) := by decide

  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 56) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 28) ++ (0 : BitVec 28)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    Live.build basicOps goal (nb C.gates) inputs.toFinset :=
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

def pickBit (i : Nat) := if i ≥ 53 then 28 else if 25 ≤ i ∧ i < 28 then 0 else i

def clip (x : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 56 => x.getLsbD (pickBit i.val)))).cast (by simp)

theorem clip_bit (x : W) {i : Nat} (hi : i < 56) :
    (clip x).getLsbD i = x.getLsbD (pickBit i) := by
  simp only [clip, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi), List.getElem_ofFn]

theorem clip_and (a b : W) : clip (a &&& b) = clip a &&& clip b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (clip (a &&& b)).getLsbD i = (clip a &&& clip b).getLsbD i
  simp only [clip_bit _ hi, BitVec.getLsbD_and]

theorem clip_not (a : W) : clip (~~~a) = ~~~(clip a) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hp : pickBit i < 56 := by unfold pickBit; split <;> first | omega | split <;> omega
  change (clip (~~~a)).getLsbD i = (~~~(clip a)).getLsbD i
  simp only [clip_bit _ hi, BitVec.getLsbD_not, hi, hp, decide_true, Bool.true_and]

theorem clip_canon (a : W) : clip (canon a) = canon (clip a) := by
  have key : (clip a).getLsbD 0 = a.getLsbD 0 := clip_bit a (by decide : 0 < 56)
  simp only [canon, key]
  split <;> simp [neg, clip_not]

theorem canon_twice (a : W) : canon (canon a) = canon a := by
  cases h : a.getLsbD 0
  · simp only [canon, h, Bool.false_eq_true, ite_false]
  · simp only [canon, h, ite_true, neg, BitVec.getLsbD_not, Bool.and_false,
      Bool.not_true, Bool.false_eq_true, ite_false]

def project (a : W) := canon (clip a)

theorem project_ops {a b z : W} (hz : z ∈ basicOps a b) :
    project z ∈ basicOps (project a) (project b) := by
  have negsign (x : W) : neg x = canon x ∨ neg x = neg (canon x) := by
    rcases sign x with h|h
    · exact Or.inr (congrArg neg h)
    · exact Or.inl ((congrArg neg h).trans (by simp [neg]))
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    simp only [project, both, neg, clip_canon, canon_twice, clip_and, clip_not]
  · exact signed_both (sign _) (sign _)
  · exact signed_both (sign _) (negsign _)
  · exact signed_both (negsign _) (sign _)
  · exact signed_both (negsign _) (negsign _)

theorem compatible (a b z : W) (hz : z ∈ basicOps a b) :
    project z = 0 ∨ project z = project a ∨ project z = project b ∨
      (project a ≠ 0 ∧ project b ≠ 0 ∧ project a ≠ project b ∧
        project z ∈ basicOps (project a) (project b)) := by
  have mem := project_ops hz
  have norm (t : W) : canon (project t) = project t := canon_twice _
  have c0 : canon 0 = 0 := by decide
  have zeroL (w : W) : (0 : W) &&& w = 0 := BitVec.zero_and
  have zeroR (w : W) : w &&& (0 : W) = 0 := BitVec.and_zero
  have onesL (w : W) : (~~~(0 : W)) &&& w = w := BitVec.allOnes_and
  have onesR (w : W) : w &&& (~~~(0 : W)) = w := BitVec.and_allOnes
  by_cases ha : project a = 0
  · simp only [ha, basicOps, ops, both, neg, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false, zeroL, onesL,
        canon_neg, norm, c0] at mem
    rcases mem with h|h|h|h <;> first | exact Or.inl h | exact Or.inr (Or.inr (Or.inl h))
  by_cases hb : project b = 0
  · simp only [hb, basicOps, ops, both, neg, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false, zeroR, onesR,
        canon_neg, norm, c0] at mem
    rcases mem with h|h|h|h <;> first | exact Or.inl h | exact Or.inr (Or.inl h)
  by_cases eq : project a = project b
  · simp only [eq, basicOps, ops, both, neg, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false, BitVec.and_self, BitVec.not_and_self,
        BitVec.and_not_self, canon_neg, norm, c0] at mem
    rcases mem with h|h|h|h <;> first | exact Or.inl h | exact Or.inr (Or.inr (Or.inl h))
  exact Or.inr (Or.inr (Or.inr ⟨ha,hb,eq,mem⟩))

def reduced : List W := [0x6d6e1807fff18, 0x2e22f800e00f8, 0xfc54f290000f00, 0x7874520707000, 0x7f888407f8000]

theorem reduced_live (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hg : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x, C.eval (List.ofFn x) = graph x)
    (small : nb C.gates ≤ 9) :
    Live.live basicOps goal 6 reduced.toFinset := by
  have full := input_live _ (get_build C hg he)
  have target : project goal = goal := by decide +kernel
  have nonzero : project goal ≠ 0 := by decide +kernel
  have verified : inputs.all (fun w => project w == 0 || reduced.contains (project w)) = true := by decide +kernel
  have covered (w : W) (hw : w ∈ inputs) : project w = 0 ∨ project w ∈ reduced := by
    simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using List.all_eq_true.mp verified w hw
  have cp : Live.Compatible basicOps basicOps project 0 := by
    intro a b z hz
    refine ⟨?_, compatible a b z hz⟩
    intro ha hb
    have mem := project_ops hz
    rw [ha,hb] at mem
    have only : ∀ w ∈ basicOps (0 : W) 0, w = 0 := by
      intro w hw
      have eq : basicOps (0 : W) 0 = {0} := by decide
      rw [eq] at hw
      exact Finset.mem_singleton.mp hw
    exact only _ mem
  obtain ⟨j,hj,built⟩ := Live.project project 0 nonzero cp full reduced.toFinset
    (by intro w hw; exact (covered w (List.mem_toFinset.mp hw)).imp_right List.mem_toFinset.mpr)
  have lost : Live.constants project 0 inputs.toFinset = 3 := by decide +kernel
  rw [lost] at hj
  rw [target] at built
  obtain ⟨s,hs,hl⟩ := Live.compress (Live.build_pad (show j ≤ 6 by omega) built)
  have eq : s = reduced.toFinset := by
    apply Finset.Subset.antisymm hs
    intro a ha
    let sites : List (Fin 28) := [8, 9, 0, 1, 2]
    have necessary : reduced.all (fun a => sites.any (fun i => reduced.all (fun b =>
       (b.getLsbD i.val == b.getLsbD (28+i.val)) || b == a))) = true := by decide +kernel
    obtain ⟨i,_,hall⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
    obtain ⟨w,hw,hd⟩ := Live.live_separates (differs i) (goal_differs i) (ops_differs i) hl
    have row := List.all_eq_true.mp hall w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at row
    exact (row.resolve_left hd) ▸ hw
  exact eq ▸ hl


theorem no_short (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hg : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x, C.eval (List.ofFn x) = graph x)
    (small : nb C.gates ≤ 9) (check : optimized 6 2 reduced = false) : False := by
  have h := optimized_complete 6 reduced 2 (by decide) (by decide)
    (reduced_live C hg he small)
  exact Bool.noConfusion (check.symm.trans h)

end Check

namespace Check
def rootF (i : Nat) : Bool :=
  ((pairs reduced)[i]?).any (fun (a,b,rest) => dispatch 2 (optimized 5) a b rest)

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
set_option maxHeartbeats 2000000 in
theorem all_front : optimized 6 2 reduced = false := by
  have hlen : (pairs reduced).length = 10 := by decide
  have allRoots : ∀ i : Fin 10, rootF i.val = false := by
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

  apply Bool.eq_false_iff.mpr
  intro h
  change (_ || _) = true at h
  simp only [Bool.or_eq_true] at h
  rcases h with stop | step
  · exact (by decide : (reduced == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := allRoots (Fin.cast hlen i)
    simp only [Fin.val_cast, rootF, List.getElem?_eq_getElem i.isLt, Option.any_some] at no
    rw [← hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

open PEqualNP.CircuitLowerBounds in
def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [11, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [15, 7]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [17, 16]⟩], 18⟩

theorem legalWitness : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem correct : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = graph x := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem same : ∀ x : Fin 8 → Bool, decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = graph x := by decide +kernel

end Check
end PEqualNP.Outside.L_meta_14970

open PEqualNP.Outside.L_meta_14970 in
theorem PEqualNP.Outside.L_meta_14970 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  by_cases big : 11 ≤ gates.length
  · exact ⟨Check.witness.gates, Check.witness.output, Check.legalWitness,
      Nat.le_trans (by decide : Check.witness.gates.length ≤ 11) big,
      fun x => (Check.correct x).trans (Check.same x).symm⟩
  by_cases hn : ∃ g ∈ gates, Check.isNot g.op = true
  · have hg : PEqualNP.MetaComplexity.FanInTwo ⟨gates,o⟩ := by
      intro g h
      exact ⟨(show g.op = .and ∨ g.op = .or ∨ g.op = .not from (legal g h).1), (legal g h).2⟩
    have hnb := Check.nb_lt gates hn
    exact (Check.no_short ⟨gates,o⟩ hg (fun x => (computes x).trans (Check.same x))
      (show Check.nb gates ≤ 9 by omega) Check.all_front).elim
  · refine ⟨gates,o,?_,Nat.le_refl _, computes⟩
    intro g h
    refine ⟨?_, (legal g h).2⟩
    rcases (legal g h).1 with ha | ho | hnot
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ⟨g, h, by rw [hnot]; rfl⟩).elim
