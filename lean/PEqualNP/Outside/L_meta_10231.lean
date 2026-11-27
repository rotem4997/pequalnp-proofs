import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10231

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

-- The paired test masks and live-wire search for the 4 × 4 minor are from L-meta-6023.
namespace Minor
abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xffffff0101010101010101, 0xffff0000000606060606060606, 0xffff00000000001818181818181818, 0xff00000000000000e0e0e0e0e0e0e0e0, 0xff00ff00000000ff0202020202020202, 0xff0000ff0000002121212121212121, 0xff0000ff004848484848484848, 0xff00009494949494949494]

def inputs : List W :=
  [0xffffff0101010101010101, 0xffff0000000606060606060606, 0xffff00000000001818181818181818, 0xff00000000000000e0e0e0e0e0e0e0e0, 0xff00ff00000000ff0202020202020202, 0xff0000ff0000002121212121212121, 0xff0000ff004848484848484848, 0xff00009494949494949494]

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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

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

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
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
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
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

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
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
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


theorem extend_live {m0 n0 : ℕ} {s : Finset W} (le : m0 ≤ n0) (h : live basicOps goal m0 s) :
    live basicOps goal n0 s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem all_front : inputs.sublists.all
    (fun l => decide (9 < l.length) || !(optimized 8 (9 - l.length) l)) = true := by
  decide +kernel

theorem no_live {k : ℕ} {S : Finset W} (hs : k ≤ 8) (hsub : S ⊆ inputs.toFinset)
    (hl : live basicOps goal k S) : False := by
  have hl3 : live basicOps goal 8 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 8 l (9 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (9 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  exact Bool.noConfusion hrow


def posL : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 2), (0, 3), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 0), (1, 3), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 8) (0, 0) else posL.getD ((k.val - 64) / 8) (0, 0)

end Minor

namespace Full

abbrev W := BitVec 132
def ops (x y : W) : List W := [x &&& y, x ||| y]
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset
def inputs : List W := [0x20000000000ffffff0101010101010101, 0xffff00000000001818181818181818, 0x100000000000000000000000000000000, 0xff00000000000000e0e0e0e0e0e0e0e0, 0xc000000ffff0000000606060606060606, 0x300ff0000ff0000002121212121212121, 0xff0000ff004848484848484848, 0x80000000000ff00009494949494949494, 0x400000000000000000000000000000000, 0xff00ff00000000ff0202020202020202]
def goal : W := 0x5ffffffffffffffff0000000000000000
def samp (i : Fin 132) : Fin 5 × Fin 5 :=
  if h : i.val < 128 then
    let pair := Minor.samp ⟨i.val,h⟩
    (![0, 4, 1, 3] pair.1, ![4, 0, 1, 2] pair.2)
  else [(2, 0), (0, 0), (4, 3), (4, 2)].getD (i.val - 128) (0,0)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 132 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 132) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 132) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 132, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 132 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 132 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 132 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 132 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 132) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 132 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def A : Fin 5 → Fin 5 → Bool := fun u v => (12060214 : ℕ).testBit (5*u.val+v.val)
theorem input_rows : ∀ k : Fin 132,
    inputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 132, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 132) :
    (C.gates.foldl step (inputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem get_live (C : Circuit) (hm : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    ∃ S ⊆ inputs.toFinset, live basicOps goal C.size S := by
  apply compress
  apply compile C.gates C.output hm inputs inputs.toFinset
  · exact fun _ hu => Or.inr (Or.inr (List.mem_toFinset.mpr hu))
  · exact rows_eval C hr

def proj (w : W) : Minor.W := w.setWidth 128
theorem proj_goal : proj goal = Minor.goal := by decide
abbrev distinguish (k : ℕ) (w : W) := w.getLsbD k = true ∧ w.getLsbD (k+1) = false
theorem separated (k : ℕ) (a b z : W) (hm : z ∈ basicOps a b) (h : distinguish k z) :
    distinguish k a ∨ distinguish k b := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hm
  unfold distinguish at *
  rcases hm with rfl | rfl <;> revert h <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or] <;>
    cases a.getLsbD k <;> cases b.getLsbD k <;> cases a.getLsbD (k+1) <;> cases b.getLsbD (k+1) <;> simp

set_option maxRecDepth 16000 in
theorem deleted {k : ℕ} {S : Finset W} (sub : S ⊆ inputs.toFinset) (h : live basicOps goal k S) :
    2 ≤ (S.filter (fun w => proj w = 0)).card := by
  obtain ⟨a,ha,sa⟩ := live_separates (distinguish 128) (by decide : distinguish 128 goal) (separated 128) h
  obtain ⟨b,hb,sb⟩ := live_separates (distinguish 130) (by decide : distinguish 130 goal) (separated 130) h
  have xa : ∀ z ∈ inputs, distinguish 128 z → z = inputs[2]! := by
    intro z hz
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have xb : ∀ z ∈ inputs, distinguish 130 z → z = inputs[8]! := by
    intro z hz
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have ea := xa a (List.mem_toFinset.mp (sub ha)) sa
  have eb := xb b (List.mem_toFinset.mp (sub hb)) sb
  apply Finset.one_lt_card.mpr
  exact ⟨a,Finset.mem_filter.mpr ⟨ha,ea ▸ (by decide)⟩,
    b,Finset.mem_filter.mpr ⟨hb,eb ▸ (by decide)⟩,by rw [ea,eb]; decide⟩

theorem image_inputs : ∀ z ∈ inputs, proj z ≠ 0 → proj z ∈ Minor.inputs := by
  intro z hz
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end Full

namespace Projection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]
theorem build_mono {ops : β → β → Finset β} {g : β} {k : ℕ} {S T : Finset β}
    (h : build ops g k S) (hst : S ⊆ T) : build ops g k T := by
  induction k generalizing S T with
  | zero => exact hst h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, ht⟩
    · exact Or.inl (ih h hst)
    · exact Or.inr ⟨a, hst ha, b, hst hb, hab, z, hz, ih ht (Finset.insert_subset_insert _ hst)⟩
def proj (f : α → β) (s : Finset α) : Finset β := (s.image f).erase 0
def zeros (f : α → β) (s : Finset α) : ℕ := (s.filter (fun a => f a = 0)).card

theorem zeros_paid (f : α → β) (a b z : α) (r : Finset α)
    (ha : f a ≠ 0) (hb : f b ≠ 0) :
    zeros f (insert a (insert b r)) ≤ zeros f (insert z r) := by
  simp only [zeros, Finset.filter_insert, if_neg ha, if_neg hb]
  split_ifs
  · exact Finset.card_le_card (Finset.subset_insert _ _)
  · exact le_rfl

theorem zeros_free (f : α → β) (a b z : α) (r : Finset α)
    (hn : z ∉ insert a (insert b r))
    (hz : f a = 0 → f b = 0 → f z = 0) :
    zeros f (insert a (insert b r)) ≤ zeros f (insert z r) + 1 := by
  have hzr : z ∉ r := fun hr => hn (by simp [hr])
  let t := r.filter (fun x => f x = 0)
  have h1 := Finset.card_insert_le a t
  have h2 := Finset.card_insert_le b t
  have h3 := Finset.card_insert_le a (insert b t)
  have h4 : t.card ≤ (insert z t).card := Finset.card_le_card (Finset.subset_insert _ _)
  have hznot : z ∉ t := by simp [t, hzr]
  have h5 := Finset.card_insert_of_notMem hznot
  dsimp [t] at h1 h2 h3 h4 h5
  by_cases ha : f a = 0 <;> by_cases hb : f b = 0 <;> by_cases hzero : f z = 0
  all_goals simp only [zeros, Finset.filter_insert, ha, hb, hzero, if_true, if_false]
  all_goals try { exfalso; exact hzero (hz ha hb) }
  all_goals omega

theorem proj_subset_insert (f : α → β) (a b z : α) (r : Finset α) :
    proj f (insert z r) ⊆ insert (f z) (proj f (insert a (insert b r))) := by
  intro x hx
  simp only [proj, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hx0, w, (rfl | hw), rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx0, w, Or.inr (Or.inr hw), rfl⟩

theorem proj_subset_free (f : α → β) (a b z : α) (r : Finset α)
    (hz : f z = 0 ∨ f z = f a ∨ f z = f b) :
    proj f (insert z r) ⊆ proj f (insert a (insert b r)) := by
  intro x hx
  simp only [proj, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hx0, w, (rfl | hw), rfl⟩
  · rcases hz with hz | hz | hz
    · exact False.elim (hx0 hz)
    · exact ⟨hx0, a, Or.inl rfl, hz.symm⟩
    · exact ⟨hx0, b, Or.inr (Or.inl rfl), hz.symm⟩
  · exact ⟨hx0, w, Or.inr (Or.inr hw), rfl⟩

theorem project_step (f : α → β) (ops : α → α → Finset α) (ops' : β → β → Finset β)
    (samezero : ∀ a b z, z ∈ ops a b → f a = 0 → f b = 0 → f z = 0)
    (casesStep : ∀ a b z, z ∈ ops a b →
      f z = 0 ∨ f z = f a ∨ f z = f b ∨
        (f a ≠ 0 ∧ f b ≠ 0 ∧ f a ≠ f b ∧ f z ∈ ops' (f a) (f b))) :
    ∀ a b z r, a ≠ b → z ∈ ops a b → z ∉ insert a (insert b r) →
      let s := insert a (insert b r)
      let t := insert z r
      ((proj f t ⊆ proj f s ∧ zeros f s ≤ zeros f t + 1) ∨
       (∃ x ∈ proj f s, ∃ y ∈ proj f s, x ≠ y ∧ ∃ v ∈ ops' x y,
         proj f t ⊆ insert v (proj f s) ∧ zeros f s ≤ zeros f t)) := by
  intro a b z r hab hz hn
  rcases casesStep a b z hz with h | h | h | ⟨ha, hb, hab', hmem⟩
  · exact Or.inl ⟨proj_subset_free f a b z r (Or.inl h), zeros_free f a b z r hn (samezero a b z hz)⟩
  · exact Or.inl ⟨proj_subset_free f a b z r (Or.inr (Or.inl h)), zeros_free f a b z r hn (samezero a b z hz)⟩
  · exact Or.inl ⟨proj_subset_free f a b z r (Or.inr (Or.inr h)), zeros_free f a b z r hn (samezero a b z hz)⟩
  · right
    refine ⟨f a, ?_, f b, ?_, hab', f z, hmem, proj_subset_insert f a b z r, zeros_paid f a b z r ha hb⟩
    · simp [proj, ha]
    · simp [proj, hb]

theorem projection {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {goal : α} (f : α → β) (hg : f goal ≠ 0)
    (step : ∀ a b z r, a ≠ b → z ∈ ops a b → z ∉ insert a (insert b r) →
      let s := insert a (insert b r)
      let t := insert z r
      ((proj f t ⊆ proj f s ∧ zeros f s ≤ zeros f t + 1) ∨
       (∃ x ∈ proj f s, ∃ y ∈ proj f s, x ≠ y ∧ ∃ v ∈ ops' x y,
         proj f t ⊆ insert v (proj f s) ∧ zeros f s ≤ zeros f t)))
    {k : ℕ} {s : Finset α} (h : live ops goal k s) :
    ∃ j, j + zeros f s ≤ k ∧ build ops' (f goal) j (proj f s) := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at h
    subst s
    refine ⟨0, ?_, ?_⟩
    · simp [zeros, hg]
    · simp [build, proj, hg]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, rfl, tail⟩
    · obtain ⟨j, hj, hbuild⟩ := ih skip
      exact ⟨j, by omega, hbuild⟩
    · obtain ⟨j, hj, hbuild⟩ := ih tail
      rcases step a b z r hab hz hout with ⟨hsub, hc⟩ | ⟨x, hx, y, hy, hxy, v, hv, hsub, hc⟩
      · exact ⟨j, by omega, build_mono hbuild hsub⟩
      · exact ⟨j+1, by omega, Or.inr ⟨x, hx, y, hy, hxy, v, hv, build_mono hbuild hsub⟩⟩
end Projection
namespace Full

theorem samezero (a b z : W) (hz : z ∈ basicOps a b) (ha : proj a = 0) (hb : proj b = 0) : proj z = 0 := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> simp_all [proj]

theorem casesStep (a b z : W) (hz : z ∈ basicOps a b) :
    proj z = 0 ∨ proj z = proj a ∨ proj z = proj b ∨
    (proj a ≠ 0 ∧ proj b ≠ 0 ∧ proj a ≠ proj b ∧ proj z ∈ Minor.basicOps (proj a) (proj b)) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;> by_cases ha : proj a = 0 <;> by_cases hb : proj b = 0 <;>
    by_cases he : proj a = proj b <;> simp_all [proj, Minor.basicOps, Minor.ops]

theorem lower (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hrun⟩ := get_live C hm hr
  have hdel := deleted hsub hrun
  obtain ⟨j, hj, hb⟩ := Projection.projection (ops' := Minor.basicOps) proj
    (by decide : proj goal ≠ 0) (Projection.project_step proj basicOps Minor.basicOps samezero casesStep) hrun
  change j + (S.filter (fun w => proj w = 0)).card ≤ C.size at hj
  rw [proj_goal] at hb
  obtain ⟨T, ht, hl⟩ := compress hb
  apply Minor.no_live (by omega : j ≤ 8) _ hl
  intro z hz
  obtain ⟨hnz, himg⟩ := Finset.mem_erase.mp (ht hz)
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp himg
  exact List.mem_toFinset.mpr (image_inputs w (List.mem_toFinset.mp (hsub hw)) hnz)

end Full
end PEqualNP.Outside.L_meta_10231

theorem PEqualNP.Outside.L_meta_10231 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12060214 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_10231.Full.lower C hm hs hr
