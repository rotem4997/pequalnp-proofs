import Mathlib.Tactic.Convert
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2964

namespace Signed2964

def Small : Prop := ∀ (n : ℕ) (op : Fin n → Bool) (a b : Fin n → ℕ × Bool) (o : ℕ × Bool)
    (v : (Fin 9 → Bool) → ℕ → Bool), n ≤ 11 →
    (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) → o.1 < 10+n →
    (∀ x (i : Fin 9), v x i.val = x i) → (∀ x, v x 9 = false) →
    (∀ x j, let read := fun u : ℕ × Bool => v x u.1 ^^ u.2
      v x (10+j.val) = if op j then read (a j) && read (b j) else read (a j) || read (b j)) →
    ∃ x, (v x o.1 ^^ o.2) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))

end Signed2964

-- Adapted from the live-wire compression argument by jackboykin in project PR 795.
-- Each stored signal represents a Boolean function up to complementation.
namespace Signed2964
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def build {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
def live {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)
theorem compress {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {available : Finset α} (h : build ops goal k available) :
    ∃ s ⊆ available, live ops goal k s := by
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
theorem live_card {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {s : Finset α} (h : live ops goal k s) : s.card ≤ k + 1 := by
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
theorem live_separates {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    (D : α → Prop) (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
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
theorem first_live {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : ℕ} {s : Finset α} (h : live ops goal (k + 1) s) :
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

abbrev m := 258
abbrev V := BitVec (2 * m)
abbrev W := V
def norm (x : W) : W := if x.getLsbD 0 then ~~~x else x
def ops (a b : W) : List W :=
  [norm (a &&& b),norm (a &&& ~~~b),norm (~~~a &&& b),norm (~~~a &&& ~~~b)]
def sep (w : W) : BitVec m := ((w >>> m) ^^^ w).setWidth m
def cuts (ws : List W) : BitVec m := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec m) ++ (0 : BitVec m)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))
def rawInputs : List W := [0x843f80211fc01f807e0f80441f80f810821108fc3f0f020882108488a1f8f83c0007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07, 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038, 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0, 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000, 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000, 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000, 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000, 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000, 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000]
def inputs : List W := rawInputs.map norm
def assignment (k : Fin (2*m)) (i : Fin 9) : Bool := (rawInputs.getD i.val 0).getLsbD k.val
def target (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
set_option maxHeartbeats 0 in
theorem target_bits : ∀ k : Fin (2*m), target (assignment k) = goal.getLsbD k.val := by decide +kernel
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
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin m) (w : W) : Prop :=
  w.getLsbD (m+i.val) ≠ w.getLsbD i.val

private theorem norm_diff (i : Fin m) (w : W) : differs i (norm w) ↔ differs i w := by
  have hi : i.val < 2*m := by have := i.isLt; omega
  have hj : m+i.val < 2*m := by have := i.isLt; omega
  unfold norm differs
  split <;> simp [BitVec.getLsbD_not,hi,hj]

theorem ops_differs (i : Fin m) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  have hi : i.val < 2*m := by have := i.isLt; omega
  have hj : m+i.val < 2*m := by have := i.isLt; omega
  by_contra! eq
  simp only [differs,not_not] at eq
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  simp [BitVec.getLsbD_eq_getElem hi,BitVec.getLsbD_eq_getElem hj] at eq
  rcases hz with rfl | rfl | rfl | rfl <;>
    rw [norm_diff] at hd <;>
    simp [differs,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hj,eq.1,eq.2] at hd

theorem goal_differs : ∀ i : Fin m, differs i goal := by unfold differs; decide +kernel

theorem cuts_spec (ws : List W) (i : Fin m) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or,Bool.or_eq_true,ih]
    have hi : i.val < 2*m := by have := i.isLt; omega
    simp [sep,i.isLt,differs,hi,Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes m)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext w
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  rw [BitVec.and_comm b a,BitVec.and_comm b (~~~a),BitVec.and_comm (~~~b) a,BitVec.and_comm (~~~b) (~~~a)]
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
    · exact List.nodup_cons.mpr ⟨fun hm => (List.nodup_cons.mp habr).1 (List.mem_cons_of_mem _ hm),
        (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2⟩
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind
theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc
theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin m) := [3, 0, 4, 7, 1, 2, 5, 8, 16]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      !(b.getLsbD (m+i.val) ^^ b.getLsbD i.val) || b == a))) = true := by decide +kernel
  obtain ⟨i, _, hAll⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    change b.getLsbD (m+i.val) ≠ b.getLsbD i.val at hd
    cases h : b.getLsbD (m+i.val) <;> cases e : b.getLsbD i.val <;> simp_all
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb
theorem input_live (k : ℕ) (hb : build basicOps goal k inputs.toFinset) :
    live basicOps goal k inputs.toFinset := by
  obtain ⟨S, hsub, hLive⟩ := compress hb
  exact full_inputs hsub hLive ▸ hLive
theorem extend_live {m n : ℕ} (le : m ≤ n) (h : live basicOps goal m inputs.toFinset) :
    live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !(w == a || w == b || r.contains w) && (
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hfresh : z ∉ a :: b :: r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · simpa [List.mem_cons, and_assoc] using hfresh
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega,
      .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega,
      .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
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
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk
          (fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm)))
          (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩


def allBad (k : ℕ) : List (ℕ × List W) → Prop
  | [] => True
  | (e,ws) :: xs => optimized k e ws = false ∧ allBad k xs

theorem bad_at {e k : ℕ} {ws : List W} {xs : List (ℕ × List W)}
    (h : allBad k xs) (hm : (e,ws) ∈ xs) : optimized k e ws = false := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    obtain ⟨j,ys⟩ := x
    rcases List.mem_cons.mp hm with eq | old
    · cases eq; exact h.1
    · exact ih h.2 old

theorem dispatch_mono (f t : ℕ → List W → Bool)
    (mono : ∀ e ws, f e ws = true → t e ws = true)
    (e : ℕ) (a b : W) (r : List W) :
    dispatch e f a b r = true → dispatch e t a b r = true := by
  intro h
  obtain ⟨x,hx,hy⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨x, hx, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hy ⊢
  grind

def oneLayer (e : ℕ) (ws : List W) (f : ℕ → List W → Bool) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch e f a b r)

theorem certify {k e : ℕ} {ws : List W} (xs : List (ℕ × List W))
    (hex : oneLayer e ws (fun j ys => !xs.contains (j,ys)) = false)
    (hbad : allBad k xs) : optimized (k+1) e ws = false := by
  cases hrun : optimized (k+1) e ws with
  | false => rfl
  | true =>
    have mono (j : ℕ) (ys : List W) (ok : optimized k j ys = true) :
        (!xs.contains (j,ys)) = true := by
      by_contra! hn
      have hm : (j,ys) ∈ xs := by simpa using hn
      have h := bad_at hbad hm
      simp_all
    have test : oneLayer e ws (fun j ys => !xs.contains (j,ys)) = true := by
      change oneLayer e ws (optimized k) = true at hrun
      simp only [oneLayer, Bool.or_eq_true, List.any_eq_true] at hrun ⊢
      rcases hrun with done | ⟨⟨a,b,r⟩,hm,hh⟩
      · exact .inl done
      · exact .inr ⟨(a,b,r),hm,dispatch_mono _ _ mono e a b r hh⟩
    exact Bool.noConfusion (hex.symm.trans test)

end Signed2964

namespace Signed2964

private def packRows {d : Nat} (bits : Fin d → Bool) : BitVec d :=
  BitVec.ofNat d (Nat.ofBits bits)

private theorem read_pack {d : Nat} (bits : Fin d → Bool) (i : Fin d) :
    (packRows bits).getLsbD i.val = bits i := by
  rw [packRows, BitVec.getLsbD_ofNat]
  simp [i.isLt]

private def phaseW {d : Nat} (a : BitVec d) (s : Bool) := if s then ~~~a else a

private theorem bit_phase {d : Nat} (a : BitVec d) (s : Bool) (j : Fin d) :
    (phaseW a s).getLsbD j.val = (a.getLsbD j.val ^^ s) := by
  cases s <;> simp [phaseW,j.isLt]

private def canonicalW {d : Nat} (a : BitVec d) := phaseW a (a.getLsbD 0)

private theorem canonical_not {d : Nat} (hd : 0 < d) (a : BitVec d) :
    canonicalW (~~~a) = canonicalW a := by
  unfold canonicalW phaseW
  rw [BitVec.getLsbD_not]
  simp only [hd,decide_true,Bool.true_and]
  cases a.getLsbD 0 <;> simp

private theorem canonical_phase {d : Nat} (hd : 0 < d) (a : BitVec d) (s : Bool) :
    canonicalW (phaseW a s) = canonicalW a := by
  cases s
  · rfl
  · exact canonical_not hd _

private theorem canonical_zero {d : Nat} : canonicalW (0 : BitVec d) = 0 := by
  simp [canonicalW,phaseW]

private theorem canonical_canonical {d : Nat} (hd : 0 < d) (a : BitVec d) :
    canonicalW (canonicalW a) = canonicalW a := canonical_phase hd _ _

private theorem signed_from {d : Nat} (a : BitVec d) (s : Bool) :
    ∃ u, phaseW a s = phaseW (canonicalW a) u := by
  refine ⟨a.getLsbD 0 ^^ s,?_⟩
  cases h : a.getLsbD 0 <;> cases s <;> simp [canonicalW,phaseW,h,BitVec.not_not]

private theorem normalize_gate {d : Nat} (hd : 0 < d) (a b : BitVec d) (op s t : Bool) :
    ∃ u v, canonicalW (if op then phaseW a s &&& phaseW b t else phaseW a s ||| phaseW b t) =
      canonicalW (phaseW (canonicalW a) u &&& phaseW (canonicalW b) v) := by
  cases op
  · obtain ⟨u,hu⟩ := signed_from a (!s)
    obtain ⟨v,hv⟩ := signed_from b (!t)
    refine ⟨u,v,?_⟩
    rw [←hu,←hv]
    change canonicalW (phaseW a s ||| phaseW b t) = _
    rw [← canonical_not hd (phaseW a s ||| phaseW b t),BitVec.not_or]
    cases s <;> cases t <;> simp [phaseW,BitVec.not_not]
  · obtain ⟨u,hu⟩ := signed_from a s
    obtain ⟨v,hv⟩ := signed_from b t
    exact ⟨u,v,by simp [hu,hv]⟩

private theorem collapsed {d : Nat} (hd : 0 < d) (x y : BitVec d) (u v : Bool)
    (h : x = 0 ∨ y = 0 ∨ x = y) :
    canonicalW (phaseW x u &&& phaseW y v) = 0 ∨
    canonicalW (phaseW x u &&& phaseW y v) = canonicalW x ∨
    canonicalW (phaseW x u &&& phaseW y v) = canonicalW y := by
  rcases h with rfl | rfl | rfl <;> cases u <;> cases v <;>
    simp [phaseW,canonical_not hd] <;> exact Or.inl canonical_zero

private def targetW (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
   (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
   (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))

theorem small_of_finite {d : Nat} (hd : 0 < d) (row : Fin d → Fin 9 → Bool)
    (start : Finset (BitVec d)) (goal : BitVec d) (nonconstant : goal ≠ 0)
    (sources : ∀ i : Fin 9, canonicalW (packRows (fun k => row k i)) ∈ start)
    (target : canonicalW (packRows (fun k => targetW (row k))) = goal)
    (Reach : Nat → Finset (BitVec d) → Prop)
    (done : ∀ s, goal ∈ s → Reach 0 s)
    (skip : ∀ k s, Reach k s → Reach (k+1) s)
    (step : ∀ k s, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ u v : Bool,
      Reach k (insert (canonicalW (phaseW x u &&& phaseW y v)) s) → Reach (k+1) s)
    (excluded : ¬ Reach 11 start) : Small := by
  intro n op a b o v hn ord outLt raw const gates
  by_contra! correct
  let wire (i : Nat) := packRows (fun k => v (row k) i)
  let word (i : Nat) := canonicalW (wire i)
  have gate (j : Fin n) :
      ∃ u t, word (10+j.val) = canonicalW (phaseW (word (a j).1) u &&& phaseW (word (b j).1) t) := by
    apply (normalize_gate hd (wire (a j).1) (wire (b j).1) (op j) (a j).2 (b j).2).imp
    intro u hu
    obtain ⟨t,eq⟩ := hu
    refine ⟨t,Eq.trans ?_ eq⟩
    apply congrArg canonicalW
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro k hk
    let w : Fin d := ⟨k,hk⟩
    have pass := gates (row w) j
    change (packRows _).getLsbD w.val = _
    rw [read_pack]
    have readPhase (i : Nat) (s : Bool) :
        (phaseW (wire i) s).getLsbD k = (v (row w) i ^^ s) := by
      change (phaseW (wire i) s).getLsbD w.val = _
      rw [bit_phase]
      change ((packRows _).getLsbD w.val ^^ s) = _
      rw [read_pack]
    cases flag : op j <;>
      simpa only [flag,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or,
        readPhase] using pass
  have hit : word o.1 = goal := by
    have eq : phaseW (wire o.1) o.2 = packRows (fun k => targetW (row k)) := by
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro k hk
      let w : Fin d := ⟨k,hk⟩
      change (phaseW _ _).getLsbD w.val = (packRows _).getLsbD w.val
      simpa only [bit_phase,wire,read_pack,targetW] using correct (row w)
    exact (canonical_phase hd _ _).symm.trans ((congrArg canonicalW eq).trans target)
  have walk : ∀ fuel j : Nat, j + fuel = n → ∀ s : Finset (BitVec d),
      (∀ i < 10+j, word i = 0 ∨ word i ∈ s) → Reach fuel s := by
    intro fuel
    induction fuel with
    | zero =>
      intro j sum s avail
      have eq : j=n := by omega
      subst j
      apply done
      obtain zero | mem := avail o.1 outLt
      · exact False.elim (nonconstant (hit.symm.trans zero))
      · exact hit ▸ mem
    | succ fuel ih =>
      intro j sum s avail
      let idx : Fin n := ⟨j,by omega⟩
      let x := word (a idx).1
      let y := word (b idx).1
      obtain ⟨u,t,rawGate⟩ := gate idx
      let z := canonicalW (phaseW x u &&& phaseW y t)
      have gz : word (10+j) = z := rawGate
      have ax : x = 0 ∨ x ∈ s := avail _ (ord idx).1
      have ay : y = 0 ∨ y ∈ s := avail _ (ord idx).2
      have ar {s' : Finset (BitVec d)} (ss : s ⊆ s') (out : z = 0 ∨ z ∈ s') :
          Reach fuel s' := by
        apply ih (j+1) (by omega) s'
        intro i hi
        by_cases old : i < 10+j
        · exact (avail i old).imp_right (fun h => ss h)
        · have now : i = 10+j := by omega
          simpa only [now,gz] using out
      by_cases bad : x = 0 ∨ y = 0 ∨ x = y
      · apply skip _ _ (ar (Finset.Subset.refl _) _)
        rcases collapsed hd x y u t bad with hz | hx | hy
        · exact Or.inl hz
        · have same : z = x := hx.trans (canonical_canonical hd _)
          simpa only [same] using ax
        · have same : z = y := hy.trans (canonical_canonical hd _)
          simpa only [same] using ay
      · push Not at bad
        exact step _ _ x (ax.resolve_left bad.1) y (ay.resolve_left bad.2.1) bad.2.2 u t
          (ar (Finset.subset_insert _ _) (Or.inr (Finset.mem_insert_self _ _)))
  have base : ∀ i < 10, word i = 0 ∨ word i ∈ start := by
    intro i hi
    by_cases h : i < 9
    · right
      let p : Fin 9 := ⟨i,h⟩
      have eq : wire i = packRows (fun k => row k p) :=
        congrArg packRows (funext (fun k => raw (row k) p))
      change canonicalW (wire i) ∈ start
      rw [eq]
      exact sources p
    · have i9 : i=9 := by omega
      subst i
      left
      have w0 : wire 9 = 0 := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro k hk
        let t : Fin d := ⟨k,hk⟩
        change (packRows _).getLsbD t.val = _
        rw [read_pack,const]
        exact BitVec.getLsbD_zero.symm
      exact (congrArg canonicalW w0).trans canonical_zero
  have b0 := walk n 0 (by omega) start (by simpa using base)
  have lift : ∀ e, Reach (n+e) start := by
    intro e
    induction e with
    | zero => exact b0
    | succ e ih => exact skip _ _ ih
  apply excluded
  exact (show n+(11-n)=11 by omega) ▸ lift (11-n)

end Signed2964

namespace Signed2964

theorem small_from_no_build (excluded : ¬ build basicOps goal 11 inputs.toFinset) : Small := by
  refine small_of_finite (d := 2*m) (by decide) assignment inputs.toFinset goal (by decide +kernel)
    ?_ ?_ (build basicOps goal) ?_ ?_ ?_ excluded
  · intro i
    have bits : packRows (fun k => assignment k i) = rawInputs.getD i.val 0 := by
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro j hj
      change (packRows _).getLsbD (⟨j,hj⟩ : Fin (2*m)).val = _
      rw [read_pack]
      rfl
    rw [bits]
    change norm (rawInputs.getD i.val 0) ∈ (rawInputs.map norm).toFinset
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    have hi : i.val < rawInputs.length := i.isLt
    simp [List.getD_eq_getElem?_getD, hi]
  · have eq : packRows (fun k => targetW (assignment k)) = goal := by
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro j hj
      change (packRows _).getLsbD (⟨j,hj⟩ : Fin (2*m)).val = _
      rw [read_pack]
      exact target_bits ⟨j,hj⟩
    rw [eq]
    decide +kernel
  · exact fun _ h => h
  · exact fun _ _ h => Or.inl h
  · intro k s x hx y hy ne u v h
    refine Or.inr ⟨x,hx,y,hy,ne,_,?_,h⟩
    cases u <;> cases v <;> simp [basicOps,ops,norm,canonicalW,phaseW]

end Signed2964

namespace Signed2964

-- The fiber propagation argument adapts AdrienDeliege, project PR 5652,
-- commit e5a59e4277eee2da434272f1db73de64631d10ed, Apache 2.0.
set_option maxHeartbeats 1600000 in
theorem of_small (small : Small) : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.true →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  classical
  intro n op a b out marked v hcard budget order outLt phase allowed inputs zero gates
  let F (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  by_contra! correct
  have raw (x : Fin 9 → Bool) : v x out.1 = !(F x) := by
    have hh := correct x
    change (v x out.1 ^^ out.2) = F x at hh
    rw [phase] at hh
    exact (show ∀ p q : Bool, (p ^^ true) = q → p = !q by decide) _ _ hh
  by_cases hs : n ≤ 11
  · obtain ⟨x,bad⟩ := small n op a b out v hs order outLt inputs zero gates
    exact bad (correct x)
  have markOut := allowed.1 phase
  have high : 10 ≤ out.1 := by
    by_contra! low
    let x : Fin 9 → Bool := fun _ => false
    have hv : v x out.1 = false := by
      by_cases h : out.1 < 9
      · exact inputs x ⟨out.1,h⟩
      · rw [show out.1 = 9 by omega,zero]
    have hr := raw x
    simp [hv,F,x] at hr
  have hm : out.1 ∈ marked := by rcases markOut with h | h | h <;> first | exact h | omega
  have sz : (marked.erase out.1).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hm]
    omega
  obtain ⟨s,source,only⟩ : ∃ s : ℕ, (s = 0 ∨ s ∈ marked.erase out.1) ∧ ∀ u ∈ marked, u ≠ out.1 → u = s := by
    by_cases h : (marked.erase out.1).Nonempty
    · obtain ⟨s,mem⟩ := h
      exact ⟨s,Or.inr mem,fun u hu hne => Finset.card_le_one.mp sz u (Finset.mem_erase.mpr ⟨hne,hu⟩) s mem⟩
    · exact ⟨0,Or.inl rfl,fun u hu hne => False.elim (h ⟨u,Finset.mem_erase.mpr ⟨hne,hu⟩⟩)⟩
  let follows (x y : Fin 9 → Bool) := ∀ i, x i ≤ y i
  have propagate (x y : Fin 9 → Bool) (le : follows x y) (same : x 0 = y 0)
      (exception : s < out.1 → v y s ≤ v x s) :
      ∀ w ≤ out.1, v x w ≤ v y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases init : w < 9
      · simpa only [inputs x ⟨w,init⟩,inputs y ⟨w,init⟩] using le ⟨w,init⟩
      by_cases c : w = 9
      · simp [c,zero]
      let j : Fin n := ⟨w-10,by omega⟩
      have eq : 10+j.val = w := by dsimp [j]; omega
      have lit (t : ℕ × Bool) (ht : t.1 < w)
          (perm : t.2 = true → t.1 = 0 ∨ t.1 = 9 ∨ t.1 ∈ marked) :
          (v x t.1 ^^ t.2) ≤ (v y t.1 ^^ t.2) := by
        cases ph : t.2 with
        | false => simpa using ih _ ht (by omega)
        | true =>
          have rev : v y t.1 ≤ v x t.1 := by
            rcases perm ph with z | z | m
            · rw [z,show v x 0 = x 0 from inputs x 0,show v y 0 = y 0 from inputs y 0,same]
            · simp [z,zero]
            · have he := only _ m (by omega)
              exact he ▸ exception (by omega)
          exact (show ∀ a b : Bool, b ≤ a → (a ^^ true) ≤ (b ^^ true) by decide) _ _ rev
      have la := lit (a j) (by have := (order j).1; omega) (allowed.2 j).1
      have lb := lit (b j) (by have := (order j).2; omega) (allowed.2 j).2
      rw [← eq,gates,gates]
      split
      · exact (show ∀ p q r s : Bool, p ≤ r → q ≤ s → (p && q) ≤ (r && s) by decide) _ _ _ _ la lb
      · exact (show ∀ p q r s : Bool, p ≤ r → q ≤ s → (p || q) ≤ (r || s) by decide) _ _ _ _ la lb
  let bot (x : Fin 9 → Bool) (i : Fin 9) := if i=0 then x 0 else false
  let top (x : Fin 9 → Bool) (i : Fin 9) := if i=0 then x 0 else true
  have botF (x : Fin 9 → Bool) : F (bot x) = false := (show ∀ z : Bool, F (fun i => if i=0 then z else false) = false by decide) (x 0)
  have topF (x : Fin 9 → Bool) : F (top x) = true := (show ∀ z : Bool, F (fun i => if i=0 then z else true) = true by decide) (x 0)
  have descent (x y : Fin 9 → Bool) (le : follows x y) (same : x 0 = y 0)
      (lo : F x = false) (hi : F y = true) : s < out.1 ∧ v x s = false ∧ v y s = true := by
    by_contra! nope
    have p := propagate x y le same (by
      intro h
      specialize nope h
      exact (show ∀ a b : Bool, (a = false → b ≠ true) → b ≤ a by decide) _ _ nope)
    have q := p _ (Nat.le_refl _)
    rw [raw,raw,lo,hi] at q
    contradiction
  have sEq (x : Fin 9 → Bool) : v x s = F x := by
    cases f : F x with
    | false => exact (descent x (top x) (fun i => by by_cases h : i=0 <;> simp [top,h])
        (by simp [top]) f (topF x)).2.1
    | true => exact (descent (bot x) x (fun i => by by_cases h : i=0 <;> simp [bot,h])
        (by simp [bot]) (botF x) f).2.2
  have earlier := (descent (bot (fun _ => false)) (top (fun _ => false))
    (fun i => by by_cases h : i=0 <;> simp [bot,top,h]) (by simp [bot,top]) (botF (fun _ => false)) (topF (fun _ => false))).1
  have sHigh : 10 ≤ s := by
    by_contra! low
    by_cases c : s=9
    · have bad := sEq (fun _ => true)
      simp [c,zero,F] at bad
    · let i : Fin 9 := ⟨s,by omega⟩
      let single : Fin 9 → Bool := fun j => decide (i=j)
      have aux : ∀ k : Fin 9, F (fun j => decide (k=j)) = false := by decide
      have noedge := aux i
      have hit := inputs single i
      change v single s = decide (i=i) at hit
      rw [sEq,noedge] at hit
      simp at hit
  have smem : s ∈ marked.erase out.1 := source.resolve_left (by omega)
  have two : 2 ≤ marked.card := by
    have pos := Finset.card_pos.mpr (show (marked.erase out.1).Nonempty from ⟨s,smem⟩)
    rw [Finset.card_erase_of_mem hm] at pos
    omega
  let m := s-9
  have mLe : m ≤ 11 := by dsimp [m]; omega
  have fits : m ≤ n := by dsimp [m]; omega
  let cast : Fin m → Fin n := Fin.castLE fits
  obtain ⟨x,bad⟩ := small m (op ∘ cast) (a ∘ cast) (b ∘ cast) (s,false) v mLe
    (fun j => order (cast j)) (by dsimp [m]; omega) inputs zero (fun x j => gates x (cast j))
  exact bad (by simpa only [Bool.xor_false] using sEq x)

end Signed2964

namespace Signed2964
def tails (xs : List W) : List (W × BitVec m) :=
  xs.foldr (fun w ys => (w, sep w ||| (ys.head?.map (·.2)).getD 0) :: ys) []
def dispatchFast (extra : Nat) (next : Nat → List W → Bool) (a b : W) (r : List W) (base : BitVec m) : Bool :=
  (ops a b).any fun w =>
    let v := sep w ||| base
    let good := !(w == a || w == b || r.contains w)
    ((v == -1) && good && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && good && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && good && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && good && next (extra - 2) (w :: a :: b :: r))
abbrev PairTest := W → W → List W → BitVec m → Bool

def scanOne (f : PairTest) (a : W) (pre : List W) (base : BitVec m) : List (W × BitVec m) → Bool
    | [] => false
    | (b,_)::bs =>
      let scov := (bs.head?.map (·.2)).getD 0
      f a b (pre.reverse ++ bs.map (·.1)) (base ||| scov) ||
        scanOne f a (b::pre) (base ||| sep b) bs

def scanRest (f : PairTest) (pre : List W) (base : BitVec m) : List (W × BitVec m) → Bool
    | [] => false
    | (a,_)::xs => scanOne f a pre base xs || scanRest f (a::pre) (base ||| sep a) xs

def anyPair (f : PairTest) (ws : List W) : Bool := scanRest f [] 0 (tails ws)
def optimizedFast : Nat → Nat → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] || anyPair (dispatchFast extra (optimizedFast k)) ws


private theorem cuts_cons (w : W) (ws : List W) : cuts (w :: ws) = sep w ||| cuts ws := rfl

private theorem orLC (x y z : BitVec m) : x ||| (y ||| z) = y ||| (x ||| z) := by ac_rfl

private theorem tails_cons (w : W) (xs : List W) :
    tails (w :: xs) = (w, sep w ||| ((tails xs).head?.map (·.2)).getD 0) :: tails xs := rfl

private theorem tails_head (xs : List W) : ((tails xs).head?.map (·.2)).getD 0 = cuts xs := by
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    change sep w ||| ((tails xs).head?.map (·.2)).getD 0 = sep w ||| cuts xs
    rw [ih]

private theorem tails_map (xs : List W) : (tails xs).map (·.1) = xs := by
  induction xs with
  | nil => rfl
  | cons w xs ih => simp [tails_cons,ih]

private theorem scanOne_correct (f : PairTest) (a : W) (pre xs : List W) :
    scanOne f a pre (cuts pre) (tails xs) = (singles xs).any (fun (b,r) =>
      f a b (pre.reverse ++ r) (cuts pre ||| cuts r)) := by
  induction xs generalizing pre with
  | nil => rfl
  | cons b bs ih =>
    simp only [tails_cons,scanOne,tails_head,tails_map,singles,List.any_cons,List.any_map,
      Function.comp_apply, List.reverse_cons]
    rw [BitVec.or_comm (cuts pre) (sep b), ←cuts_cons, ih]
    simp [List.reverse_cons,cuts_cons,orLC,BitVec.or_assoc,Function.comp_def]

private theorem scanRest_correct (f : PairTest) (pre xs : List W) :
    scanRest f pre (cuts pre) (tails xs) = (pairs xs).any (fun (a,b,r) =>
      f a b (pre.reverse ++ r) (cuts pre ||| cuts r)) := by
  induction xs generalizing pre with
  | nil => rfl
  | cons a xs ih =>
    simp only [tails_cons,scanRest,scanOne_correct,pairs,List.any_append,List.any_map]
    rw [BitVec.or_comm (cuts pre) (sep a), ←cuts_cons, ih]
    simp [List.reverse_cons,cuts_cons,orLC,BitVec.or_assoc, Function.comp_def]

private theorem anyPair_eq (f : PairTest) (ws : List W) :
    anyPair f ws = (pairs ws).any (fun (a,b,r) => f a b r (cuts r)) := by
  rw [anyPair, show (0 : BitVec m) = cuts [] by rfl, scanRest_correct]
  simp [cuts]

private theorem dispatchFast_eq (extra : Nat) (next : Nat → List W → Bool) (a b : W) (r : List W) :
    dispatchFast extra next a b r (cuts r) = dispatch extra next a b r := by
  unfold dispatchFast dispatch
  congr 1
  funext w
  cases h : (w == a || w == b || r.contains w) <;> simp [h]

theorem optimizedFast_eq (n e : Nat) (ws : List W) : optimizedFast n e ws = optimized n e ws := by
  induction n generalizing ws e with
  | zero => rfl
  | succ n ih =>
    simp only [optimizedFast, optimized,anyPair_eq]
    have heq : optimizedFast n = optimized n := funext fun j => funext fun ys => ih j ys
    simp only [heq, dispatchFast_eq]

theorem certified_fast {n e : Nat} {ws : List W} (h : optimizedFast n e ws = false) :
    optimized n e ws = false := (optimizedFast_eq n e ws).symm.trans h
end Signed2964

namespace Signed2964

theorem oneLayer_of_live (k extra : Nat) (ws : List W) (test : Nat → List W → Bool)
    (hn : ws.Nodup) (room : extra + ws.length = k + 2)
    (accept : ∀ e ys, live basicOps goal k ys.toFinset → test e ys = true)
    (h : live basicOps goal (k+1) ws.toFinset) : oneLayer extra ws test = true := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · simp [oneLayer, singleton_list hn done]
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        dispatch extra test a b r = true := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps goal k (z :: kept).toFinset := by
        simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have len := perm.length_eq
      simp only [List.length_cons] at len
      apply dispatch_complete (k := k) (extra := extra) test hop hk
        (fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm)))
        (by omega) (by omega) (cuts_full hl)
      exact accept _ _ hl
    simp only [oneLayer, Bool.or_eq_true, List.any_eq_true]
    right
    rcases hm with direct | swap
    · exact ⟨(a, b, r), direct, go hp hs hz⟩
    · exact ⟨(b, a, r), swap,
        go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def prescribed (zs : List W) : Nat → List W → Bool
  | _, [] => false
  | _, z :: xs => decide (z ∈ zs) && decide (xs.toFinset = inputs.toFinset)

theorem root_cases (zs : List W)
    (certificate : oneLayer 3 inputs (fun e xs => !prescribed zs e xs) = false)
    (reject : ∀ z ∈ zs, ¬live basicOps goal 10 (insert z inputs.toFinset)) :
    ¬build basicOps goal 11 inputs.toFinset := by
  intro h
  have go := oneLayer_of_live 10 3 inputs (fun e xs => !prescribed zs e xs)
    (by decide +kernel) (by decide) ?_ (input_live 11 h)
  · exact Bool.noConfusion (certificate.symm.trans go)
  · intro e ys liveYs
    cases ys with
    | nil => rfl
    | cons z xs =>
      simp only [prescribed,Bool.not_eq_true',Bool.and_eq_false_iff] 
      by_cases hz : z ∈ zs
      · right
        apply decide_eq_false_iff_not.mpr
        intro eq
        apply reject z hz
        simpa only [List.toFinset_cons,eq] using liveYs
      · left
        exact decide_eq_false_iff_not.mpr hz

end Signed2964

namespace Signed2964

private theorem index_zero : (decide (0 < 2*m)) = true := by decide

private def ph (a : W) (s : Bool) : W := if s then ~~~a else a

-- Transforming bits by a permutation of rows can change which output phase is canonical.
private def readRows (p : Fin (2*m) → Fin (2*m)) (x : W) : W :=
  BitVec.ofNat _ (Nat.ofBits fun i => x.getLsbD (p i).val)

private theorem read_readRows (p : Fin (2*m) → Fin (2*m)) (x : W) (i : Fin (2*m)) :
    (readRows p x).getLsbD i.val = x.getLsbD (p i).val := by
  rw [readRows,BitVec.getLsbD_ofNat]
  simp [i.isLt]

private theorem readRows_not (p : Fin (2*m) → Fin (2*m)) (x : W) :
    readRows p (~~~x) = ~~~readRows p x := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  let i : Fin (2*m) := ⟨k,hk⟩
  change (readRows p _).getLsbD i.val = (~~~readRows p x).getLsbD i.val
  simp only [read_readRows,BitVec.getLsbD_not,i.isLt,(p i).isLt,decide_true,Bool.true_and]

private theorem readRows_and (p : Fin (2*m) → Fin (2*m)) (x y : W) :
    readRows p (x &&& y) = readRows p x &&& readRows p y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  let i : Fin (2*m) := ⟨k,hk⟩
  change (readRows p _).getLsbD i.val = (readRows p x &&& readRows p y).getLsbD i.val
  simp only [read_readRows,BitVec.getLsbD_and]

private theorem readRows_inj {p : Fin (2*m) → Fin (2*m)} (hp : p.Surjective) :
    (readRows p).Injective := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  obtain ⟨j,hj⟩ := hp ⟨k,hk⟩
  have got := congrArg (fun x : W => x.getLsbD j.val) eq
  simpa only [read_readRows,hj] using got

private theorem norm_not (x : W) : norm (~~~x) = norm x := by
  unfold norm
  rw [BitVec.getLsbD_not]
  have h : 0 < 2*m := by decide
  simp only [h,decide_true,Bool.true_and]
  cases x.getLsbD 0 <;> simp

private theorem ph_undo (x : W) (s : Bool) : ph (ph x s) s = x := by
  cases s <;> simp [ph]

private theorem norm_first (x : W) : (norm x).getLsbD 0 = false := by
  unfold norm
  cases h : x.getLsbD 0 <;>
    simp only [h,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_not,index_zero,Bool.true_and,
      Bool.not_true]

-- Preserve the phase at row zero to obtain an injection on all words, including raw words.
def move (p : Fin (2*m) → Fin (2*m)) (x : W) := ph (norm (readRows p x)) (x.getLsbD 0)

private theorem move_inj {p : Fin (2*m) → Fin (2*m)} (hp : p.Surjective) :
    (move p).Injective := by
  intro a b eq
  have first (x : W) : (move p x).getLsbD 0 = x.getLsbD 0 := by
    unfold move
    cases h : x.getLsbD 0 <;>
      simp only [ph,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_not,norm_first,
        index_zero,Bool.true_and,Bool.not_false]
  have same : a.getLsbD 0 = b.getLsbD 0 := (first a).symm.trans
    ((congrArg (fun x : W => x.getLsbD 0) eq).trans (first b))
  unfold move at eq
  rw [same] at eq
  have hn := congrArg (fun x => ph x (b.getLsbD 0)) eq
  simp only [ph_undo] at hn
  unfold norm at hn
  split at hn <;> split at hn
  · exact readRows_inj hp (by simpa using congrArg (fun x : W => ~~~x) hn)
  · have h : ~~~a = b := readRows_inj hp ((readRows_not p a).trans hn)
    have := congrArg (fun x : W => x.getLsbD 0) h
    simp only [BitVec.getLsbD_not,index_zero,Bool.true_and,same] at this
    revert this
    generalize b.getLsbD 0 = t
    cases t <;> simp
  · have h : a = ~~~b := readRows_inj hp (hn.trans (readRows_not p b).symm)
    have := congrArg (fun x : W => x.getLsbD 0) h
    simp only [BitVec.getLsbD_not,index_zero,Bool.true_and,same] at this
    revert this
    generalize b.getLsbD 0 = t
    cases t <;> simp
  · exact readRows_inj hp hn

private theorem norm_read_norm (p : Fin (2*m) → Fin (2*m)) (x : W) :
    norm (readRows p (norm x)) = norm (readRows p x) := by
  by_cases h : x.getLsbD 0 = true
  · rw [show norm x = ~~~x from ite_eq_left h,readRows_not,norm_not]
  · rw [show norm x = x from ite_eq_right h]

private theorem move_norm (p : Fin (2*m) → Fin (2*m)) (x : W) :
    move p (norm x) = norm (readRows p x) := by
  simp only [move,norm_first,ph,Bool.false_eq_true,ite_false,norm_read_norm]

private theorem ops_phase (a b : W) (s t : Bool) : norm (ph a s &&& ph b t) ∈ basicOps a b := by
  cases s <;> cases t <;> simp [basicOps,ops,ph]

private theorem signed_image (p : Fin (2*m) → Fin (2*m)) (a : W) (s : Bool) :
    ∃ t, readRows p (ph a s) = ph (move p a) t := by
  refine ⟨s ^^ ((readRows p a).getLsbD 0 ^^ a.getLsbD 0),?_⟩
  cases h : (readRows p a).getLsbD 0 <;> cases e : a.getLsbD 0 <;> cases s <;>
    simp only [move,ph,norm,h,e,readRows_not,Bool.false_eq_true,ite_false,ite_true,BitVec.not_not,
      Bool.xor_false,Bool.xor_true,Bool.not_true,Bool.not_false]

private theorem move_member (p : Fin (2*m) → Fin (2*m)) {a b z : W} (h : z ∈ basicOps a b) :
    move p z ∈ basicOps (move p a) (move p b) := by
  have aux (s t : Bool) : move p (norm (ph a s &&& ph b t)) ∈ basicOps (move p a) (move p b) := by
    obtain ⟨u,hu⟩ := signed_image p a s
    obtain ⟨v,hv⟩ := signed_image p b t
    rw [move_norm,readRows_and,hu,hv]
    exact ops_phase _ _ _ _
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact aux false false
  · exact aux false true
  · exact aux true false
  · exact aux true true

-- Check a concrete canonical signal image one row at a time.
theorem move_of_bits (p : Fin (2*m) → Fin (2*m)) (a b : W)
    (h0 : a.getLsbD 0 = false)
    (h : ∀ i : Fin (2*m), (a.getLsbD (p i).val ^^ a.getLsbD (p 0).val) = b.getLsbD i.val) :
    move p a = b := by
  have first : (readRows p a).getLsbD 0 = a.getLsbD (p 0).val := read_readRows p a 0
  simp only [move,h0,ph,Bool.false_eq_true,ite_false,norm,first]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  let i : Fin (2*m) := ⟨k,hk⟩
  change (if a.getLsbD (p 0).val then ~~~readRows p a else readRows p a).getLsbD i.val = _
  cases flag : a.getLsbD (p 0).val <;>
    simpa only [flag,Bool.xor_false,Bool.xor_true,Bool.false_eq_true,ite_false,ite_true,
      BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,read_readRows] using h i

def rowImage (p : Fin (2*m) → Fin (2*m)) (x y : W) : Prop :=
  ∀ i : Fin (2*m), x.getLsbD (p i).val = y.getLsbD i.val

private theorem readRows_eq {p : Fin (2*m) → Fin (2*m)} {x y : W} (h : rowImage p x y) :
    readRows p x = y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  exact (read_readRows p x ⟨k,hk⟩).trans (h ⟨k,hk⟩)

theorem move_literal {p : Fin (2*m) → Fin (2*m)} {a b x y : W} (h : rowImage p a b)
    (hx : norm a = x) (hy : norm b = y) : move p x = y := by
  rw [←hx,move_norm,readRows_eq h,hy]

theorem move_gate {p : Fin (2*m) → Fin (2*m)} {a b a' b' x y : W}
    (s t : Bool) (ha : rowImage p a a') (hb : rowImage p b b')
    (hx : norm (ph a s &&& ph b t) = x) (hy : norm (ph a' s &&& ph b' t) = y) :
    move p x = y := by
  rw [←hx,move_norm,readRows_and,←hy]
  cases s <;> cases t <;> simp only [ph,Bool.false_eq_true,ite_false,ite_true,readRows_not,
    readRows_eq ha,readRows_eq hb]

theorem move_live (p : Fin (2*m) → Fin (2*m)) (hp : p.Surjective)
    (hg : move p goal = goal) (n : Nat) (s : Finset W) (h : live basicOps goal n s) :
    live basicOps goal n (s.image (move p)) := by
  induction n generalizing s with
  | zero => change s = {goal} at h; simp [h,live,hg]
  | succ k ih =>
    rcases h with h | ⟨a,ha,b,hb,hne,z,hz,hfresh,r,hs,hl⟩
    · exact Or.inl (ih _ h)
    · refine Or.inr ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,
        (move_inj hp).ne hne,_,move_member p hz,?_,r.image (move p),?_,?_⟩
      · intro hm
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
        exact hfresh ((move_inj hp he) ▸ hw)
      · simp [hs]
      · simpa using ih _ hl

theorem reject_image (p : Fin (2*m) → Fin (2*m)) (hp : p.Surjective)
    (hg : move p goal = goal) (hs : inputs.toFinset.image (move p) = inputs.toFinset)
    (a b : W) (he : move p a = b) (hb : ¬ live basicOps goal 10 (insert b inputs.toFinset)) :
    ¬ live basicOps goal 10 (insert a inputs.toFinset) := by
  intro h
  have h' := move_live p hp hg _ _ h
  exact hb (by simpa only [Finset.image_insert,he,hs] using h')

def rootDead (zs : List W) : Prop := ∀ z ∈ zs, ¬ live basicOps goal 10 (insert z inputs.toFinset)

theorem rootDead_cons {z : W} {zs : List W}
    (hz : ¬ live basicOps goal 10 (insert z inputs.toFinset)) (hs : rootDead zs) :
    rootDead (z :: zs) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | other
  · exact hz
  · exact hs _ other


end Signed2964

namespace Signed2964.Orbit

-- A concrete table packs each row index in a separate ten-bit field.
def rowAt (table index : Nat) : Nat := ((table >>> (10*index)) &&& 1023) % (2*m)
def rowMap (table : Nat) (i : Fin (2*m)) : Fin (2*m) :=
  ⟨rowAt table i.val,Nat.mod_lt _ (by decide)⟩

def checkRows (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n+1 => f n && checkRows f n

theorem checkRows_sound (f : Nat → Bool) (n : Nat) (h : checkRows f n = true) :
    ∀ i < n, f i = true := by
  induction n with
  | zero => exact fun _ h => by omega
  | succ n ih =>
    have ⟨hn,ht⟩ : f n = true ∧ checkRows f n = true := by simpa only [checkRows,Bool.and_eq_true] using h
    intro i hi
    by_cases eq : i=n
    · exact eq ▸ hn
    · exact ih ht i (by omega)

theorem table_onto (table : Nat)
    (h : checkRows (fun k => rowAt table (rowAt table k) == k) (2*m) = true) :
    (rowMap table).Surjective := by
  intro i
  exact ⟨rowMap table i, Fin.ext (beq_iff_eq.mp (checkRows_sound _ _ h _ i.isLt))⟩

theorem table_image (table : Nat) (x y : W)
    (h : checkRows (fun k => x.getLsbD (rowAt table k) == y.getLsbD k) (2*m) = true) :
    rowImage (rowMap table) x y := fun i => beq_iff_eq.mp (checkRows_sound _ _ h _ i.isLt)

end Signed2964.Orbit

namespace Signed2964
namespace Orbit
private def raw0 : W := 0x843f80211fc01f807e0f80441f80f810821108fc3f0f020882108488a1f8f83c0007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07
private def raw1 : W := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def raw2 : W := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def raw3 : W := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def raw4 : W := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def raw5 : W := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def raw6 : W := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def raw7 : W := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def raw8 : W := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def source0 : W := 0xf7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def source1 : W := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def source2 : W := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def source3 : W := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def source4 : W := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def source5 : W := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def source6 : W := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def source7 : W := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def source8 : W := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def gate0 : W := 0xf03c0005e0003e00080100f83e007002104221100401045f07c0178171e0001c3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def gate1 : W := 0x78007f80e03c007f01e07038007807ce79cce60380e0b80701ee0360400706001f001ff83c0f801ff07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
private def gate2 : W := 0x80208001004010800200804010808800000000040101000802000400810808240000000000000000000000000000000000000000000000000000000000000000
private def gate3 : W := 0xffbe0ffdfe07ff0ff83f0fffbf0ff8fef7deef707c1f1fdff7fef7f77df0f0fe7fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def gate4 : W := 0x108400fc2003e200100201088200903e009e0f00080f03c10042f087102010740000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def gate5 : W := 0xe7380701ce001c07e81d06f33c076040f740e07034000c1e779c073065c060083fff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def gate6 : W := 0x100200fc000000401000001001010001008083f000200000080080010f8000000000003f000000000000000000000000000000fc000000000000000003e00
private def gate7 : W := 0xf7bc17ffeefffe07f85f17fbbe17f17ff7dfeff0bfff0fff77deffb7f5e17ffc3fff81ffffffffc1ff07c1ffffc1fe1ffffffffe0fffc3fffffffffffffc1fff8
private def gate8 : W := 0x2108010842004401201f00113e07800427c402203c02008217de200225e0702000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def gate9 : W := 0xd6b406f5ac03ba06d80007ea8000707ad01aed50000d0f5d6000d7b55000005c3fff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def gate10 : W := 0x20000008001003e0000001f8000000200007c020000000210000001f8100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def gate11 : W := 0xf7bc27fdee0bfe17fbff07fbbffff07ef7feef77fc2f0fdf77fff7b775fff17c3fff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8
private def gate12 : W := 0xf780007dee000000f804007b8401001ef1000f70100003df70840007744020003ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def gate13 : W := 0x3c07800003fe07001b07803a06f06006dee0002c0f0c00075af7b001a0507c000f81e00000ffc1c007c1e00fc1fe1801fffc000f03c30001fffffe007c1c1f8
private def gate14 : W := 0x84040021110002004802004402002010800008900402020880000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def gate15 : W := 0xfffc47ffff13fe27fc9f27fffe27f27fffdeeff93c4f2fffffdef7b7ffe2727cbfff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def gate16 : W := 0x4210021084008802400802220802205ef7dee000000003df77def7b00000000000000000000000000000000000000007fffffc00000000fffffffffe000000000
private def gate17 : W := 0xb5ac05ed6a037605b81705d9b605d02000000f703c0f0c000000000775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8
private def gate18 : W := 0x80000020004001004000004004010821100200804020882108480004040100000000000000000000000000000000000000000000000000000000000000000
private def gate19 : W := 0xf7bc87fdee23fe47f91f47fbbe47f47fffffff723c8f4fffffffffff75e4747d3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def gate20 : W := 0x8420042108011004f81f07c01000401ef7deef703c0f0c04010001004080000800000000000000003f07c1e000000007fffffffe0f03c30000000000000000000
private def gate21 : W := 0x739c03dce602ee030000003bae07b06000000000000003db76def6b7356070743fff81ffffc0ffc1c000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def gate22 : W := 0x100000040008007e0f800000000010821108fc3f0f0000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def gate23 : W := 0xf7bd07fdee43fe87fffffffbbe07f07fffffffffffffffdf77def7b775e0707c3fff81ffffc0ffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def gate24 : W := 0xf7bc07c000020000f81f07fbbe07f068420844000004010822084214000000403fff81e0000000003f07c1ffffc1fe18000000000000000000000000000000000
private def gate25 : W := 0x3dee01fe070000000000000016b5d6ab703c0b0ed755d6b5a375e0703c0000001fffc0ffc1c000000000000007fffffffe0f03c3fffffffffffffc1c1f8
private def gate26 : W := 0x843f8000080000007e0f80441f80f800000000001000000000000000000080000007e000000000000f83e00003e01e0000000000000000000000000000000000
private def gate27 : W := 0xfffffffdee83fe07fffffffffffffffef7deef703d0f0fdf77def7b775e0787c3fffffffffc0ffc1fffffffffffffffffffffffe0f03c3fffffffffffffc1c1f8
private def gate28 : W := 0xf7bc07fdee03fe0780100400200400108410884020080a1044108420010040003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def gate29 : W := 0x780f03fb9e03f06e73ce67301c0705cf33ce739774e0307c00000000000000003f07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def gate30 : W := 0x843f80211fc01f802008000008000000000000402008000000000000008000000007e00003f003e0000000000000000000000000000000000000000000000000
private def gate31 : W := 0xfffffffffffffffffa1f87fbbe87f07ef7deef743e0f8fdf77def7b775e8707c3fffffffffffffffff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def gate32 : W := 0x100400042004220000000008020010020002010000110041004010811020009400000000000000000000000000000000000000000000000000000000000000000
private def gate33 : W := 0xe83a0801d0001d08082108f43d086880104020104400141e87a0074069d0800a7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def gate34 : W := 0x8010fa00fbc000104211008010813d009d0e808bee03a00002e80680011f600000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def gate35 : W := 0xf8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe7e0f801ffc3fffc00000001f0fc01e07c007c3e000ffc0ffe1f83ff1fe7c03ff8
private def gate36 : W := 0x2008000040000400002100103f080000004000004400000207e0000021f080000000000000000000000000000fc00000000000000000000001f80000007c00000
private def gate37 : W := 0xd8360805b0043b08080008ec00007882100221100011145d800017c15800009e7e0f80007c0007c00000001f00001e000000000000000007e00001f01e0000038
private def gate38 : W := 0x10021080208401123de000100f7800427a40227b8220080101f2002040f7120000000000000000000ffc000003fe00001f80001ff0000000007c0000003fc000
private def gate39 : W := 0xf93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be7e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038
private def gate40 : W := 0xf8000005f00000000800007c04000002100001100000005f80800001784000003e0000007c0000000000001f000000000000000000000007e00000001e0000000
private def gate41 : W := 0x3e080000043f08002108803b0878800042200044111400076017c001b0809e400f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def gate42 : W := 0x7c0407a0f100020f4842003c021021de9000ee9104023a0780400068602220081f0001f83c000003f000000f0000007fe0003fe000000f81e000001e18000000
private def gate43 : W := 0xfffe487fff143f28fca528ffff297a9ff9422ff9545137ffffe417c7fff2a29effff801fffc007c03f00001fffc01e07fe0003fe000000fffff801f1fffc00038
private def gate44 : W := 0x40100000800008000000002008002002104220000000005f87e017c000000000000000000000000000000000000000000000000000000007e1f801f0000000000
private def gate45 : W := 0xb82e080570043708082108dc3708588000000110441114000000000179f0809e7e0f80007c0007c00000001f0fc01e000000000000000000000000001e7c00038
private def gate46 : W := 0x200821004208042410842020042045defbdd002008043a0781fe8380004040100000000000000000000000000000007fffffc00000000f81e07fe0e000000000
private def gate47 : W := 0xfa3e8a15f424bf4a49294afe3f4a7cdffffff112449157fffffffff979f4849f7e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038
private def gate48 : W := 0x8020000100001000082108c0100040021042211044111404010001004080000800000000000000000000000000000000000000000000000000000000000000000
private def gate49 : W := 0x781e0804f0042f080000003c2f083880000000000000005b86e016c1397080967e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def gate50 : W := 0x401042008410084f7def7000000001defbddeefbbeee800000000000000000000000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def gate51 : W := 0xfc3f0c25f8453f8cfffffffc3f08789ffffffffffffffc5f87e017c179f0809e7e0f80007c0007c03fffffff0fc01e07ffffffffffffff07e1f801f01e7c00038
private def gate52 : W := 0xf83e080000000000082108fc3f087880000000000000000802000200000000003e0f8000000000000000001f0fc01e00000000000000000000000000000000000
private def gate53 : W := 0x5f0043f080000000000000002104221104411145785e015c179f0809e400000007c0007c000000000000000000000000000000007e1f801f01e7c00038
private def gate54 : W := 0x7c1f7c000820000f7def703c0f787684208440001040100200840140000084001f07fe0000000003fffffe0f03fe1f8000000000000000000000000000000000
private def gate55 : W := 0xffffffc5f0863f08ffffffffffffffea524a65104515155fa7e857d579f088de7fffffe07c0007c03ffffffffffffff80000000000000007e1f801f01e7c00038
private def gate56 : W := 0xf83e0805f0043f080000000020000000000000000000001004000400010000003e0f80007c0007c00000000000000000000000000000000000000000000000000
private def gate57 : W := 0x82108fc1f087882104221104411144f83e013c178f0809e40000000000000000000001f0fc01e000000000000000007e1f801f01e7c00038
private def gate58 : W := 0x7c1f7fa0ffbc0f782108400008400108410884422088a00401080200008400001f07fff83fff83fc000000000000000000000000000000000000000000000000
private def gate59 : W := 0xffffffffffffffff8a318cfc3f8c78929452a95466199e5fc7f097e179f8c09e7fffffffffffffffc000001f0fc01e000000000000000007e1f801f01e7c00038
private def gate60 : W := 0x80008400000420000021080040084020088220080004220020021112000000000000000000000000000000000000000000000000000000000000000000
private def gate61 : W := 0x108410f620f7a200100011088000113b001b0d8003dd03610000d88590000ed40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def gate62 : W := 0x210821004200041123bd00113def0000276000277400000217bd000025dee000000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def gate63 : W := 0x318c31fe62ffe61133ff1119bfff913f27ff0fa7ffff03e317fff887b5fffff40000001f803ff80000ffc0000fffe007c1ffc3e1ffffc0f801fffe01e07ffffc0
private def gate64 : W := 0x1080007e20100000100000088000001f00000f80004003e100000007900002000000001f800000000000000000000007c00003e0000000f800000001e00000000
private def gate65 : W := 0x4108000efe2000042110002109120009f00008bbf00000042f88000211df400000000003ff80000000000000000000007c00000ffc00000003e00000003fc0
private def gate66 : W := 0xef404001df000020ec84207744210200f90000791000201ef88400006e422000bff000007fc000003f00001ff00000003e00001e00000007fe0000001f8000000
private def gate67 : W := 0xffc450ffffffe220fcc6317fc631933ff99f0ff99bff23fff8c6f887fe633ff4bff0001ffffff8003f00001ff0000007fe07c3fe00ffc0fffe003e01ff8003fc0
private def gate68 : W := 0x1000208000000000000000001f009f0000008003e10042f8800000040000000000000000000000000000000007c007c000000000f800003e00000000000
private def gate69 : W := 0x108410ee20df6200104211088210912000000f808b7f00000000000790211bf40000001f803ff8000000000000000000000003e000ffc00000000001e00003fc0
private def gate70 : W := 0x42108200840008424108422208422440ff60f0020000401effbd077800040001000000000000000000000000000000003ff83c0000000007ffffc1fe000000000
private def gate71 : W := 0x529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff50000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0
private def gate72 : W := 0x2000410000104211000000001f009f0f808bff0000000000000000000000000000000000000000000000000007c007c3e000ffc00000000000000000000
private def gate73 : W := 0x108410de20bee200000000088210912000000000000003e10042f88790211ff40000001f803ff800000000000000000000000000000000f800003e01e00003fc0
private def gate74 : W := 0x8421040108001084efbdeec010004000ff60f07f7400fc04010001004080000800000000000000003fffffe0000000003ff83c1fff003f0000000000000000000
private def gate75 : W := 0x94a514ff28fff284ffffffc89210d13fffffffffffffffe50142f987d0a11ffc0000001f803ff8003fffffe000000007fffffffffffffff800003e01e00003fc0
private def gate76 : W := 0x108410c00082000010421108821091280008040001040100000040040000084000000000000000000000000000000000000000000000000000000000000000000
private def gate77 : W := 0x3e207de200000000000000001700970b808afb02e10042b883902117b40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def gate78 : W := 0xef7bef0000000000efbdeef77def6ec0420040000000000822080210000000003fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def gate79 : W := 0xfffffffe20ffe200ffffffffffffffff429f4f808bff03e9224afa9790211ff43fffffff803ff8003fffffffffffffffc007c3e000ffc0f800003e01e00003fc0
private def gate80 : W := 0x108410fe20ffe2000000000000000010001008000208020000008000000000000000001f803ff8000000000000000000000000000000000000000000000000000
private def gate81 : W := 0x104211088210912f008f078089f701e10042788790211ff400000000000000000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def gate82 : W := 0xef7bef01df001dff8210840020840000840080442000881044100420010840003fffffe07fc007ffc000000000000000000000000000000000000000000000000
private def gate83 : W := 0xffffffffffffffff92529508a294913f849f8fc4abff8bf14452fca791295ff43fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0
private def gate84 : W := 0x210000084200000020840011042100042100022110000082108400022442200000000000000000000000000000000000000000000000000000000000000000000
private def gate85 : W := 0x8210000084411037b00003bde800006e40006ec220000077b200001bdd120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def gate86 : W := 0xdec04077bd100020dc00206ec000021bd8000dd80040237de8000005da000200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def gate87 : W := 0xffc8617fff184431ffff207fffff821fffe40ffffc6223ffffff2007fffff320bff0001fffc000003fffc01fffffe007fff803ffff0000ffffffc001fffffc000
private def gate88 : W := 0x10800000842000427e400020000008217ff2000000400000000000000000000000000000000000001f800000000000001ffc000000000000
private def gate89 : W := 0x210821084208441122f7001137bd800000000225fc2200000000000225fbf120000000000000000000ffc0000fffe00000000001ff00000000000000007ffc000
private def gate90 : W := 0x4210821084208842400042220000245bd81bf0000080437de800dff80000040100000000000000000000000000000007fe07fc00000000fffe003ffe000000000
private def gate91 : W := 0x6318a318c628cc5363ff42333fffa45ffffff227fca243fffffffffa25fff521000000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000
private def gate92 : W := 0x23ff00001000000427e40227fc2200000100000000800000000000000000000000ffc0000000000001f80001ff00000000000000000000000
private def gate93 : W := 0x2108210842084411000000112fff8000000000000000008216ff2002257ff1200000000000000000000000000fffe000000000000000000001ffc000007ffc000
private def gate94 : W := 0x8421042108411084dc00ffc00000401bd81bfdd803ddfc04000001004000000800000000000000003f003fe000000007fe07fffe00ffff0000000000000000000
private def gate95 : W := 0xa52925294a495495ffffffd13fffc01ffffffffffffffc8617ff210265fff12800000000000000003fffffe00fffe007ffffffffffffff0001ffc000007ffc000
private def gate96 : W := 0x210821000000000023ff00113fff800002000000000000000208000000000000000000000000000000ffc0000fffe000000000000000000000000000000000000
private def gate97 : W := 0x842084411000000000000000425e40227fc22008215f7200225fff1200000000000000000000000000000000001f80001ff00000001ffc000007ffc000
private def gate98 : W := 0xdef7dec000820000dc00ffeec0007fe8400844000104010820004214000008403fffffe0000000003f003ffff0001ff8000000000000000000000000000000000
private def gate99 : W := 0xffffffc8428a4411ffffffffffffffec67ec4627fd26018a37ff621625fff9603fffffe0000000003ffffffffffffff801f80001ff00000001ffc000007ffc000
private def gate100 : W := 0x210821084208441102100000208400000400000420000000041000000108400000000000000000000000000000000000000000000000000000000000000000000
private def gate101 : W := 0x21ef00111f7b800423e40223dc22008213ef200224f7b120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def gate102 : W := 0xdef7def7bdf7bbee80008400000000108010884002088a1040008420000000003fffffffffffffffc000000000000000000000000000000000000000000000000
private def gate103 : W := 0xffffffffffffffffa3ff84113fff8014a7f48a67fe2a8a9257ffa42225fff1203fffffffffffffffc0ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def gate104 : W := 0x4200001084000000400000220000001ff9000000000003fff88400000000000000000000000000000000000000000007fe000000000000fffe000000000000000
private def gate105 : W := 0xbdc0406f7b100020bc84205dc421020000000ff91040200000000007fe422200bff0001fffc000003f00001ff0000000000003fe0000000000000001ff8000000
private def gate106 : W := 0x10820000208842010842000842244006fff00200804000077bfff8000404010000000000000000000000000000000001fffc000000000001fffffe000000000
private def gate107 : W := 0xffd0c27fff308862fd8c627fcc63265ffffffffb10c063fffffffffffe462601bff0001fffc000003f00001ff0000007fffffffe000000ffffffffffff8000000
private def gate108 : W := 0x8400002108000000fc8420400000001ff9000ff910402004000000004000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def gate109 : W := 0x7bc0405ef71000200000003fc421020000000000000003fbf8840007be422200bff0001fffc000000000001ff000000000000000000000fffe000001ff8000000
private def gate110 : W := 0x21040000411084037bdf801000400006fff006efbfdc000100010000800008000000000000000000ffffe00000000001fffc01ffffff0000000000000000000
private def gate111 : W := 0xffe1447fff5110a4ffffffffd421421ffffffffffffffffff9840107fec22208bff0001fffc000003ffffffff0000007fffffffffffffffffe000001ff8000000
private def gate112 : W := 0xffc0404000000000fc84207fc4210208400004000000010820000004000000003ff00000000000003f00001ff0000000000000000000000000000000000000000
private def gate113 : W := 0x3fff1000200000000000000017b9000bf9104022f7d8840003fe4222008000001fffc000000000000000000007fe0003fe000000fffe000001ff8000000
private def gate114 : W := 0x3fbf8000820000037bdf803bdefde002084000010400000208421000000840000fffe00000000000ffffe00ffffff8000000000000000000000000000000000
private def gate115 : W := 0xffffffffff920020fffffffffffffffffb084ff9114423fffa8c4217fe422a40bfffffffffc000003ffffffffffffffffe0003fe000000fffe000001ff8000000
private def gate116 : W := 0xffc0407fff1000208000000000000010800008400000021040000000000000003ff0001fffc000000000000000000000000000000000000000000000000000000
private def gate117 : W := 0x7c84207fc421020f790007b9104021efb8840007fe42220080000000000000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def gate118 : W := 0x3fbf8000efffdf021084002084000004108004220888000410842001084000000fffe0003fffffc000000000000000000000000000000000000000000000000
private def gate119 : W := 0xfffffffffffffffffe94a47fe4a5021ffd108ffd3248abfffc948427ff4a6200bfffffffffffffffff00001ff0000007fe0003fe000000fffe000001ff8000000
private def gate120 : W := 0x410842000000001ffffff00200804004010001000000000000000000000000000000000000000007fffffc000000000000000000000000000
private def gate121 : W := 0x4210821084208842000000220842244000000000000003fbfefffef8000404010000000000000000000000000000000000000000000000fffffffffe000000000
private def gate122 : W := 0x8421042108411084bef7bdc01000400000000ffdff7fbc00000000004080000800000000000000003fffffe000000000000003ffffffff0000000000000000000
private def gate123 : W := 0xc63186318c6198c6ffffffe21842645ffffffffffffffffffffffff84084040900000000000000003fffffe000000007fffffffffffffffffffffffe000000000
private def gate124 : W := 0x421082000000000041084222084224484208400000000108220842100000000000000000000000000000000000000000000000000000000000000000000000000
private def gate125 : W := 0x10842088420000000000000017bdf7b002008042f7ddf7bde80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def gate126 : W := 0xbdef7dc000820000bef7bdddf7bddba0000004000104000000000004000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def gate127 : W := 0xffffffd084a28842fffffffffffffffffffff402018443fffffffffc00040c413fffffe0000000003ffffffffffffffffffffc00000000fffffffffe000000000
private def gate128 : W := 0x421082108420884200000000000000108410800000000210441084200000000000000000000000000000000000000000000000000000000000000000000000000
private def gate129 : W := 0x410842220842244f7bef7002008041efbbef7bd80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def gate130 : W := 0xbdef7def7bdf77bd8210840020840000000008442208880000000000010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def gate131 : W := 0xffffffffffffffffc318c62228c6245ffffff8462288cbfffffffff8010c44013fffffffffffffffc000000000000007fffffc00000000fffffffffe000000000
private def gate132 : W := 0x8421040000000000ffffffc0100040084208440001040000000000000000000000000000000000003fffffe000000000000000000000000000000000000000000
private def gate133 : W := 0x21084110840000000000000017bdf7bbfffefbfc04010001004080000800000000000000000000000000000007ffffffffffffff0000000000000000000
private def gate134 : W := 0x7bdefbc0008200000000003fefffbfe0000000000000010822084214000008403fffffe0000000000000001ffffffff8000000000000000000000000000000000
private def gate135 : W := 0xffffffe108c31084fffffffffffffffffffffffffffffd0c23084314408008483fffffe0000000003fffffffffffffffffffffffffffff0000000000000000000
private def gate136 : W := 0x842104210841108482108400000000108410884422088800000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def gate137 : W := 0x7def7bc01000400f7bef77bbddf77404010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def gate138 : W := 0x7bdefbdef7beef7b0000000020840000000000000000021044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def gate139 : W := 0xffffffffffffffffffffffc03084401ffffffffffffffe1445108520418840083fffffffffffffffffffffe000000007ffffffffffffff0000000000000000000
private def gate140 : W := 0xffffffc0008200008210840020840000000000000000000000000000000000003fffffe0000000000000000000000000000000000000000000000000000000000
private def gate141 : W := 0x7def7bffdf7bffe84208440001040108220842140000084000000000000000003ffffffffffffff8000000000000000000000000000000000
private def gate142 : W := 0x3fff7dffff00000000000000108410884422088a1044108420010840000000001fffffffffc000000000000000000000000000000000000000000000000
private def gate143 : W := 0xfffffffffffffffffffffffffffffff8c618cc44230c8b186618c634010848403ffffffffffffffffffffffffffffff8000000000000000000000000000000000
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem inputList : inputs = [source0,source1,source2,source3,source4,source5,source6,source7,source8] := by decide +kernel
private def table1 : Nat := 0x61d85619886116e5b16d5bd6b5dd755d9785d15c5615a5655d56d565515555de97a9e679de87954c5294b535494992449523769db759d875dd9751d5745d274d324c1314cd2f43d0b4350c4390a42109701bf705c3709be6e9b96edbd6f1b56d1b66e1b76c1af6c5b36c9ac6adae6b5826018160d7f5a1695a9675ed7d5e97c5f97958d62591665955f57960585725c5735c150545535494e53e0080e01809ff69daa6a1a96999d6819e6859f671f67e5f77e1f5641926458f7edfe7f1fd7e9a3691a56899865d9966d9a64d94659957c1f47bdf27c5f37adee7b1ed6318b6358e6258a785e4789e378144519475154850d204892147d3a4f13d4ed3e4e51946d1a47118735d0739cf7312b4b12d4b92a41907415df775de77141501424fd1e475354dd364e1344511345517459104451272dc7725c8729c6711c54a12949d0240d0421483210862086c1a86b1b4691d4731d0761c85a1585815c5b1645414853154e73a0e4394e638c4a1204912c470902208c21360d9350d6354d7348d333cd0344300b82f0c42d0340902c0a03008018072f8bd2fcc1300bc2e0b72e4bb2e8b32c8b42d8b52b8ad2bcb12c0aa2a4ac2ac801f87f2047d198671a0651e47b1e07a1f077184601886418c5d1705e17c701bc711b84e13c511404c134fe404ff400fd294a8298a72909b2789c27c9d268f43dcf53d8f32389023c8d3e4fc3e8fb3e0a1288a328096254972649824492250933b8f23b4f03bcf13a4ec3a8eb2288922c8c21c8837ce2380e1378421104510c461041e0801f074380e83b0e43c0dc17064180681632cce330cd328290a82b0b0280100500cdd36cdc3683f0f8400f41c06c330d4340d8320481104c150500e03c10324c531cc6320c4308c3098270940000402
private def perm1 := rowMap table1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem onto1 : perm1.Surjective := table_onto table1 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem goal1 : move perm1 goal = goal :=
  move_literal (table_image table1 goal goal (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to0 : rowImage perm1 raw0 raw0 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source0 : move perm1 source0 = source0 :=
  move_literal raw1to0 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to1 : rowImage perm1 raw1 raw5 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source1 : move perm1 source1 = source5 :=
  move_literal raw1to1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to2 : rowImage perm1 raw2 raw8 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source2 : move perm1 source2 = source8 :=
  move_literal raw1to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to3 : rowImage perm1 raw3 raw3 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source3 : move perm1 source3 = source3 :=
  move_literal raw1to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to4 : rowImage perm1 raw4 raw4 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source4 : move perm1 source4 = source4 :=
  move_literal raw1to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to5 : rowImage perm1 raw5 raw1 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source5 : move perm1 source5 = source1 :=
  move_literal raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to6 : rowImage perm1 raw6 raw7 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source6 : move perm1 source6 = source7 :=
  move_literal raw1to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to7 : rowImage perm1 raw7 raw6 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source7 : move perm1 source7 = source6 :=
  move_literal raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw1to8 : rowImage perm1 raw8 raw2 := table_image table1 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im1source8 : move perm1 source8 = source2 :=
  move_literal raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem src1 : inputs.toFinset.image (move perm1) = inputs.toFinset := by
  rw [inputList]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,im1source0,im1source1,im1source2,im1source3,im1source4,im1source5,im1source6,im1source7,im1source8]
  decide +kernel
private def table2 : Nat := 0x6edba6f5bc6e5b66d5b86ddb46659866d9a65d9e675a06859f6719464d966557d5f17b5f9795e96458d66595625815f5855e4f53b4e93c4f9394dd364d5384d11545117459134691946d1c4611144112705c070dc26f9bf8060080e027fdfc7edfe7f5fa6a1a76a9a9699a468da5689b16c1b36c9af6b1ae6b5ab7c5f27c1f47cdef7ddf67e5f87d5ec7adee7b58d6318e62d906499163d896298661d88611855b56e5bd6b5b1e77a9e97a1e57994b5314d5254a4952648d246058260d7f601695a9675a1e2785e478de0775df779dc515475114652143501415093f485204891f4791d5d9775e1745d5595715a5755b5615555957551d776dd8769d9759d2755d474dd14c5324cd2f4c10c43d0d4390b4250a421725cd705c55154d525414f539c8725cb729c7739cd741cf731c4719c54b52b4b12e4a9284a52740d044090641d052e4b82ecba2dcb42ccb62d4b225c96264982549c26c9e27c9d268922449424c7b1e8791f0771e0621846418c601785d17c5c0ec390e03a0f0370d4340cc360c8130481505011060170641a0580f038102fcbe304c02f0bd3fcfe405003f4fa3e4fc3ecf8298a52a0a7290a2284a3280af2b8b12c0ad2a8ac2aca93bcf03b8f23c4ed3d4f43dcf63ccea3a4ec3ac8b2288c2248e2408f234872208421486208831ac6c1b4691a8e53a0e7398e3390491284b11c4808c24084221fc802047d1f8671a065198e037ce2384de36cdd370da10c4510844118410f83f1003d07c1e0801d0701b1d0751d8721cc571685816c591585315055148d5364d6360d7350d034cd2344cf0bc300c42d0b80a0340b0300901c08018701c46e1bc4f144501384d130c631cc9320c5330cb338cd328c2310c30ac290a82c0a02609c25004020000401403
private def perm2 := rowMap table2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem onto2 : perm2.Surjective := table_onto table2 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem goal2 : move perm2 goal = goal :=
  move_literal (table_image table2 goal goal (by decide +kernel)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to0 : rowImage perm2 raw0 raw1 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source0 : move perm2 source0 = source1 :=
  move_literal raw2to0 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to1 : rowImage perm2 raw1 raw0 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source1 : move perm2 source1 = source0 :=
  move_literal raw2to1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to2 : rowImage perm2 raw2 raw5 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source2 : move perm2 source2 = source5 :=
  move_literal raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to3 : rowImage perm2 raw3 raw8 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source3 : move perm2 source3 = source8 :=
  move_literal raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to4 : rowImage perm2 raw4 raw6 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source4 : move perm2 source4 = source6 :=
  move_literal raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to5 : rowImage perm2 raw5 raw2 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source5 : move perm2 source5 = source2 :=
  move_literal raw2to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to6 : rowImage perm2 raw6 raw4 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source6 : move perm2 source6 = source4 :=
  move_literal raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to7 : rowImage perm2 raw7 raw7 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source7 : move perm2 source7 = source7 :=
  move_literal raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem raw2to8 : rowImage perm2 raw8 raw3 := table_image table2 _ _ (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem im2source8 : move perm2 source8 = source3 :=
  move_literal raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem src2 : inputs.toFinset.image (move perm2) = inputs.toFinset := by
  rw [inputList]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,im2source0,im2source1,im2source2,im2source3,im2source4,im2source5,im2source6,im2source7,im2source8]
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate3 : move perm2 gate3 = gate0 :=
  move_gate false true raw2to0 raw2to1 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate16 : move perm1 gate16 = gate0 :=
  move_gate true false raw1to0 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate17 : move perm1 gate17 = gate1 :=
  move_gate true true raw1to0 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate18 : move perm1 gate18 = gate2 :=
  move_gate false false raw1to0 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate19 : move perm1 gate19 = gate3 :=
  move_gate false true raw1to0 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate24 : move perm1 gate24 = gate20 :=
  move_gate true false raw1to0 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate25 : move perm1 gate25 = gate21 :=
  move_gate true true raw1to0 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate26 : move perm1 gate26 = gate22 :=
  move_gate false false raw1to0 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate27 : move perm1 gate27 = gate23 :=
  move_gate false true raw1to0 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate28 : move perm1 gate28 = gate4 :=
  move_gate true false raw1to0 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate29 : move perm1 gate29 = gate5 :=
  move_gate true true raw1to0 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate30 : move perm1 gate30 = gate6 :=
  move_gate false false raw1to0 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate32 : move perm2 gate32 = gate18 :=
  move_gate false false raw2to1 raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate33 : move perm2 gate33 = gate19 :=
  move_gate false true raw2to1 raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate34 : move perm2 gate34 = gate16 :=
  move_gate true false raw2to1 raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate35 : move perm2 gate35 = gate17 :=
  move_gate true true raw2to1 raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate36 : move perm2 gate36 = gate30 :=
  move_gate false false raw2to1 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate38 : move perm2 gate38 = gate28 :=
  move_gate true false raw2to1 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate39 : move perm2 gate39 = gate29 :=
  move_gate true true raw2to1 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate40 : move perm2 gate40 = gate22 :=
  move_gate false false raw2to1 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate41 : move perm2 gate41 = gate23 :=
  move_gate false true raw2to1 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate42 : move perm2 gate42 = gate20 :=
  move_gate true false raw2to1 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate43 : move perm2 gate43 = gate21 :=
  move_gate true true raw2to1 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate44 : move perm2 gate44 = gate6 :=
  move_gate false false raw2to1 raw2to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate46 : move perm2 gate46 = gate4 :=
  move_gate true false raw2to1 raw2to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate47 : move perm2 gate47 = gate5 :=
  move_gate true true raw2to1 raw2to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate48 : move perm2 gate48 = gate14 :=
  move_gate false false raw2to1 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate49 : move perm2 gate49 = gate15 :=
  move_gate false true raw2to1 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate50 : move perm2 gate50 = gate12 :=
  move_gate true false raw2to1 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate51 : move perm2 gate51 = gate13 :=
  move_gate true true raw2to1 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate52 : move perm2 gate52 = gate26 :=
  move_gate false false raw2to1 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate53 : move perm2 gate53 = gate27 :=
  move_gate false true raw2to1 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate54 : move perm2 gate54 = gate24 :=
  move_gate true false raw2to1 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate55 : move perm2 gate55 = gate25 :=
  move_gate true true raw2to1 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate56 : move perm2 gate56 = gate10 :=
  move_gate false false raw2to1 raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate58 : move perm2 gate58 = gate8 :=
  move_gate true false raw2to1 raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate59 : move perm2 gate59 = gate9 :=
  move_gate true true raw2to1 raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate68 : move perm1 gate68 = gate56 :=
  move_gate false false raw1to2 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate69 : move perm1 gate69 = gate58 :=
  move_gate false true raw1to2 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate70 : move perm2 gate70 = gate69 :=
  move_gate true false raw2to2 raw2to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate71 : move perm1 gate71 = gate59 :=
  move_gate true true raw1to2 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate88 : move perm1 gate88 = gate36 :=
  move_gate false false raw1to3 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate89 : move perm1 gate89 = gate38 :=
  move_gate false true raw1to3 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate91 : move perm1 gate91 = gate39 :=
  move_gate true true raw1to3 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate104 : move perm1 gate104 = gate40 :=
  move_gate false false raw1to4 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate105 : move perm1 gate105 = gate42 :=
  move_gate false true raw1to4 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate106 : move perm1 gate106 = gate41 :=
  move_gate true false raw1to4 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate107 : move perm1 gate107 = gate43 :=
  move_gate true true raw1to4 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate110 : move perm2 gate110 = gate109 :=
  move_gate true false raw2to4 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate112 : move perm1 gate112 = gate108 :=
  move_gate false false raw1to4 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate113 : move perm1 gate113 = gate109 :=
  move_gate false true raw1to4 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate114 : move perm1 gate114 = gate110 :=
  move_gate true false raw1to4 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate115 : move perm1 gate115 = gate111 :=
  move_gate true true raw1to4 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate120 : move perm1 gate120 = gate52 :=
  move_gate false false raw1to5 raw1to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate121 : move perm1 gate121 = gate53 :=
  move_gate false true raw1to5 raw1to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate122 : move perm1 gate122 = gate54 :=
  move_gate true false raw1to5 raw1to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate123 : move perm1 gate123 = gate55 :=
  move_gate true true raw1to5 raw1to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate124 : move perm1 gate124 = gate48 :=
  move_gate false false raw1to5 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate125 : move perm1 gate125 = gate49 :=
  move_gate false true raw1to5 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate126 : move perm1 gate126 = gate50 :=
  move_gate true false raw1to5 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate127 : move perm1 gate127 = gate51 :=
  move_gate true true raw1to5 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate128 : move perm1 gate128 = gate32 :=
  move_gate false false raw1to5 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate129 : move perm1 gate129 = gate33 :=
  move_gate false true raw1to5 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate130 : move perm1 gate130 = gate34 :=
  move_gate true false raw1to5 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate131 : move perm1 gate131 = gate35 :=
  move_gate true true raw1to5 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate132 : move perm2 gate132 = gate112 :=
  move_gate false false raw2to6 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate133 : move perm2 gate133 = gate113 :=
  move_gate false true raw2to6 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate134 : move perm1 gate134 = gate133 :=
  move_gate true false raw1to6 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate135 : move perm2 gate135 = gate115 :=
  move_gate true true raw2to6 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate45 : move perm1 gate45 = gate46 :=
  move_gate false true raw1to1 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate57 : move perm1 gate57 = gate70 :=
  move_gate false true raw1to1 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate60 : move perm2 gate60 = gate128 :=
  move_gate false false raw2to2 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate61 : move perm2 gate61 = gate129 :=
  move_gate false true raw2to2 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate62 : move perm2 gate62 = gate130 :=
  move_gate true false raw2to2 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate63 : move perm2 gate63 = gate131 :=
  move_gate true true raw2to2 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate64 : move perm2 gate64 = gate120 :=
  move_gate false false raw2to2 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate65 : move perm2 gate65 = gate121 :=
  move_gate false true raw2to2 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate66 : move perm2 gate66 = gate122 :=
  move_gate true false raw2to2 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate67 : move perm2 gate67 = gate123 :=
  move_gate true true raw2to2 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate72 : move perm2 gate72 = gate104 :=
  move_gate false false raw2to2 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate73 : move perm2 gate73 = gate106 :=
  move_gate false true raw2to2 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate74 : move perm2 gate74 = gate105 :=
  move_gate true false raw2to2 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate75 : move perm2 gate75 = gate107 :=
  move_gate true true raw2to2 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate76 : move perm2 gate76 = gate124 :=
  move_gate false false raw2to2 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate77 : move perm2 gate77 = gate125 :=
  move_gate false true raw2to2 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate78 : move perm2 gate78 = gate126 :=
  move_gate true false raw2to2 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate79 : move perm2 gate79 = gate127 :=
  move_gate true true raw2to2 raw2to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate80 : move perm2 gate80 = gate88 :=
  move_gate false false raw2to2 raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate82 : move perm2 gate82 = gate89 :=
  move_gate true false raw2to2 raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate83 : move perm2 gate83 = gate91 :=
  move_gate true true raw2to2 raw2to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate100 : move perm1 gate100 = gate60 :=
  move_gate false false raw1to3 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate101 : move perm1 gate101 = gate62 :=
  move_gate false true raw1to3 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate102 : move perm1 gate102 = gate61 :=
  move_gate true false raw1to3 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate103 : move perm1 gate103 = gate63 :=
  move_gate true true raw1to3 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate116 : move perm1 gate116 = gate64 :=
  move_gate false false raw1to4 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate117 : move perm1 gate117 = gate66 :=
  move_gate false true raw1to4 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate118 : move perm1 gate118 = gate65 :=
  move_gate true false raw1to4 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate119 : move perm1 gate119 = gate67 :=
  move_gate true true raw1to4 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate136 : move perm1 gate136 = gate76 :=
  move_gate false false raw1to6 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate137 : move perm1 gate137 = gate78 :=
  move_gate false true raw1to6 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate138 : move perm1 gate138 = gate77 :=
  move_gate true false raw1to6 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate139 : move perm1 gate139 = gate79 :=
  move_gate true true raw1to6 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate140 : move perm1 gate140 = gate72 :=
  move_gate false false raw1to7 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate141 : move perm1 gate141 = gate74 :=
  move_gate false true raw1to7 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate142 : move perm1 gate142 = gate73 :=
  move_gate true false raw1to7 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate143 : move perm1 gate143 = gate75 :=
  move_gate true true raw1to7 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate7 : move perm2 gate7 = gate45 :=
  move_gate false true raw2to0 raw2to2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate11 : move perm2 gate11 = gate57 :=
  move_gate false true raw2to0 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate31 : move perm1 gate31 = gate7 :=
  move_gate false true raw1to0 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate37 : move perm2 gate37 = gate31 :=
  move_gate false true raw2to1 raw2to3 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate81 : move perm1 gate81 = gate82 :=
  move_gate false true raw1to2 raw1to8 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate84 : move perm2 gate84 = gate136 :=
  move_gate false false raw2to3 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate85 : move perm2 gate85 = gate138 :=
  move_gate false true raw2to3 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate86 : move perm2 gate86 = gate137 :=
  move_gate true false raw2to3 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate87 : move perm2 gate87 = gate139 :=
  move_gate true true raw2to3 raw2to4 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate90 : move perm1 gate90 = gate37 :=
  move_gate true false raw1to3 raw1to5 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate92 : move perm2 gate92 = gate116 :=
  move_gate false false raw2to3 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate93 : move perm2 gate93 = gate118 :=
  move_gate false true raw2to3 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate94 : move perm2 gate94 = gate117 :=
  move_gate true false raw2to3 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate95 : move perm2 gate95 = gate119 :=
  move_gate true true raw2to3 raw2to6 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate96 : move perm1 gate96 = gate92 :=
  move_gate false false raw1to3 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate97 : move perm1 gate97 = gate93 :=
  move_gate false true raw1to3 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate98 : move perm1 gate98 = gate94 :=
  move_gate true false raw1to3 raw1to7 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem imgate99 : move perm1 gate99 = gate95 :=
  move_gate true true raw1to3 raw1to7 (by decide +kernel) (by decide +kernel)
def representatives : List W := [gate0,gate1,gate2,gate4,gate5,gate6,gate8,gate9,gate10,gate12,gate13,gate14,gate15,gate20,gate21,gate22,gate23,gate108,gate109,gate111]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem of_representatives (h : rootDead representatives) : ¬build basicOps goal 11 inputs.toFinset := by
  have ngate0 : ¬live basicOps goal 10 (insert gate0 inputs.toFinset) := h _ (by decide +kernel)
  have ngate1 : ¬live basicOps goal 10 (insert gate1 inputs.toFinset) := h _ (by decide +kernel)
  have ngate2 : ¬live basicOps goal 10 (insert gate2 inputs.toFinset) := h _ (by decide +kernel)
  have ngate4 : ¬live basicOps goal 10 (insert gate4 inputs.toFinset) := h _ (by decide +kernel)
  have ngate5 : ¬live basicOps goal 10 (insert gate5 inputs.toFinset) := h _ (by decide +kernel)
  have ngate6 : ¬live basicOps goal 10 (insert gate6 inputs.toFinset) := h _ (by decide +kernel)
  have ngate8 : ¬live basicOps goal 10 (insert gate8 inputs.toFinset) := h _ (by decide +kernel)
  have ngate9 : ¬live basicOps goal 10 (insert gate9 inputs.toFinset) := h _ (by decide +kernel)
  have ngate10 : ¬live basicOps goal 10 (insert gate10 inputs.toFinset) := h _ (by decide +kernel)
  have ngate12 : ¬live basicOps goal 10 (insert gate12 inputs.toFinset) := h _ (by decide +kernel)
  have ngate13 : ¬live basicOps goal 10 (insert gate13 inputs.toFinset) := h _ (by decide +kernel)
  have ngate14 : ¬live basicOps goal 10 (insert gate14 inputs.toFinset) := h _ (by decide +kernel)
  have ngate15 : ¬live basicOps goal 10 (insert gate15 inputs.toFinset) := h _ (by decide +kernel)
  have ngate20 : ¬live basicOps goal 10 (insert gate20 inputs.toFinset) := h _ (by decide +kernel)
  have ngate21 : ¬live basicOps goal 10 (insert gate21 inputs.toFinset) := h _ (by decide +kernel)
  have ngate22 : ¬live basicOps goal 10 (insert gate22 inputs.toFinset) := h _ (by decide +kernel)
  have ngate23 : ¬live basicOps goal 10 (insert gate23 inputs.toFinset) := h _ (by decide +kernel)
  have ngate108 : ¬live basicOps goal 10 (insert gate108 inputs.toFinset) := h _ (by decide +kernel)
  have ngate109 : ¬live basicOps goal 10 (insert gate109 inputs.toFinset) := h _ (by decide +kernel)
  have ngate111 : ¬live basicOps goal 10 (insert gate111 inputs.toFinset) := h _ (by decide +kernel)
  have ngate3 := reject_image perm2 onto2 goal2 src2 _ _ imgate3 ngate0
  have ngate16 := reject_image perm1 onto1 goal1 src1 _ _ imgate16 ngate0
  have ngate17 := reject_image perm1 onto1 goal1 src1 _ _ imgate17 ngate1
  have ngate18 := reject_image perm1 onto1 goal1 src1 _ _ imgate18 ngate2
  have ngate19 := reject_image perm1 onto1 goal1 src1 _ _ imgate19 ngate3
  have ngate24 := reject_image perm1 onto1 goal1 src1 _ _ imgate24 ngate20
  have ngate25 := reject_image perm1 onto1 goal1 src1 _ _ imgate25 ngate21
  have ngate26 := reject_image perm1 onto1 goal1 src1 _ _ imgate26 ngate22
  have ngate27 := reject_image perm1 onto1 goal1 src1 _ _ imgate27 ngate23
  have ngate28 := reject_image perm1 onto1 goal1 src1 _ _ imgate28 ngate4
  have ngate29 := reject_image perm1 onto1 goal1 src1 _ _ imgate29 ngate5
  have ngate30 := reject_image perm1 onto1 goal1 src1 _ _ imgate30 ngate6
  have ngate32 := reject_image perm2 onto2 goal2 src2 _ _ imgate32 ngate18
  have ngate33 := reject_image perm2 onto2 goal2 src2 _ _ imgate33 ngate19
  have ngate34 := reject_image perm2 onto2 goal2 src2 _ _ imgate34 ngate16
  have ngate35 := reject_image perm2 onto2 goal2 src2 _ _ imgate35 ngate17
  have ngate36 := reject_image perm2 onto2 goal2 src2 _ _ imgate36 ngate30
  have ngate38 := reject_image perm2 onto2 goal2 src2 _ _ imgate38 ngate28
  have ngate39 := reject_image perm2 onto2 goal2 src2 _ _ imgate39 ngate29
  have ngate40 := reject_image perm2 onto2 goal2 src2 _ _ imgate40 ngate22
  have ngate41 := reject_image perm2 onto2 goal2 src2 _ _ imgate41 ngate23
  have ngate42 := reject_image perm2 onto2 goal2 src2 _ _ imgate42 ngate20
  have ngate43 := reject_image perm2 onto2 goal2 src2 _ _ imgate43 ngate21
  have ngate44 := reject_image perm2 onto2 goal2 src2 _ _ imgate44 ngate6
  have ngate46 := reject_image perm2 onto2 goal2 src2 _ _ imgate46 ngate4
  have ngate47 := reject_image perm2 onto2 goal2 src2 _ _ imgate47 ngate5
  have ngate48 := reject_image perm2 onto2 goal2 src2 _ _ imgate48 ngate14
  have ngate49 := reject_image perm2 onto2 goal2 src2 _ _ imgate49 ngate15
  have ngate50 := reject_image perm2 onto2 goal2 src2 _ _ imgate50 ngate12
  have ngate51 := reject_image perm2 onto2 goal2 src2 _ _ imgate51 ngate13
  have ngate52 := reject_image perm2 onto2 goal2 src2 _ _ imgate52 ngate26
  have ngate53 := reject_image perm2 onto2 goal2 src2 _ _ imgate53 ngate27
  have ngate54 := reject_image perm2 onto2 goal2 src2 _ _ imgate54 ngate24
  have ngate55 := reject_image perm2 onto2 goal2 src2 _ _ imgate55 ngate25
  have ngate56 := reject_image perm2 onto2 goal2 src2 _ _ imgate56 ngate10
  have ngate58 := reject_image perm2 onto2 goal2 src2 _ _ imgate58 ngate8
  have ngate59 := reject_image perm2 onto2 goal2 src2 _ _ imgate59 ngate9
  have ngate68 := reject_image perm1 onto1 goal1 src1 _ _ imgate68 ngate56
  have ngate69 := reject_image perm1 onto1 goal1 src1 _ _ imgate69 ngate58
  have ngate70 := reject_image perm2 onto2 goal2 src2 _ _ imgate70 ngate69
  have ngate71 := reject_image perm1 onto1 goal1 src1 _ _ imgate71 ngate59
  have ngate88 := reject_image perm1 onto1 goal1 src1 _ _ imgate88 ngate36
  have ngate89 := reject_image perm1 onto1 goal1 src1 _ _ imgate89 ngate38
  have ngate91 := reject_image perm1 onto1 goal1 src1 _ _ imgate91 ngate39
  have ngate104 := reject_image perm1 onto1 goal1 src1 _ _ imgate104 ngate40
  have ngate105 := reject_image perm1 onto1 goal1 src1 _ _ imgate105 ngate42
  have ngate106 := reject_image perm1 onto1 goal1 src1 _ _ imgate106 ngate41
  have ngate107 := reject_image perm1 onto1 goal1 src1 _ _ imgate107 ngate43
  have ngate110 := reject_image perm2 onto2 goal2 src2 _ _ imgate110 ngate109
  have ngate112 := reject_image perm1 onto1 goal1 src1 _ _ imgate112 ngate108
  have ngate113 := reject_image perm1 onto1 goal1 src1 _ _ imgate113 ngate109
  have ngate114 := reject_image perm1 onto1 goal1 src1 _ _ imgate114 ngate110
  have ngate115 := reject_image perm1 onto1 goal1 src1 _ _ imgate115 ngate111
  have ngate120 := reject_image perm1 onto1 goal1 src1 _ _ imgate120 ngate52
  have ngate121 := reject_image perm1 onto1 goal1 src1 _ _ imgate121 ngate53
  have ngate122 := reject_image perm1 onto1 goal1 src1 _ _ imgate122 ngate54
  have ngate123 := reject_image perm1 onto1 goal1 src1 _ _ imgate123 ngate55
  have ngate124 := reject_image perm1 onto1 goal1 src1 _ _ imgate124 ngate48
  have ngate125 := reject_image perm1 onto1 goal1 src1 _ _ imgate125 ngate49
  have ngate126 := reject_image perm1 onto1 goal1 src1 _ _ imgate126 ngate50
  have ngate127 := reject_image perm1 onto1 goal1 src1 _ _ imgate127 ngate51
  have ngate128 := reject_image perm1 onto1 goal1 src1 _ _ imgate128 ngate32
  have ngate129 := reject_image perm1 onto1 goal1 src1 _ _ imgate129 ngate33
  have ngate130 := reject_image perm1 onto1 goal1 src1 _ _ imgate130 ngate34
  have ngate131 := reject_image perm1 onto1 goal1 src1 _ _ imgate131 ngate35
  have ngate132 := reject_image perm2 onto2 goal2 src2 _ _ imgate132 ngate112
  have ngate133 := reject_image perm2 onto2 goal2 src2 _ _ imgate133 ngate113
  have ngate134 := reject_image perm1 onto1 goal1 src1 _ _ imgate134 ngate133
  have ngate135 := reject_image perm2 onto2 goal2 src2 _ _ imgate135 ngate115
  have ngate45 := reject_image perm1 onto1 goal1 src1 _ _ imgate45 ngate46
  have ngate57 := reject_image perm1 onto1 goal1 src1 _ _ imgate57 ngate70
  have ngate60 := reject_image perm2 onto2 goal2 src2 _ _ imgate60 ngate128
  have ngate61 := reject_image perm2 onto2 goal2 src2 _ _ imgate61 ngate129
  have ngate62 := reject_image perm2 onto2 goal2 src2 _ _ imgate62 ngate130
  have ngate63 := reject_image perm2 onto2 goal2 src2 _ _ imgate63 ngate131
  have ngate64 := reject_image perm2 onto2 goal2 src2 _ _ imgate64 ngate120
  have ngate65 := reject_image perm2 onto2 goal2 src2 _ _ imgate65 ngate121
  have ngate66 := reject_image perm2 onto2 goal2 src2 _ _ imgate66 ngate122
  have ngate67 := reject_image perm2 onto2 goal2 src2 _ _ imgate67 ngate123
  have ngate72 := reject_image perm2 onto2 goal2 src2 _ _ imgate72 ngate104
  have ngate73 := reject_image perm2 onto2 goal2 src2 _ _ imgate73 ngate106
  have ngate74 := reject_image perm2 onto2 goal2 src2 _ _ imgate74 ngate105
  have ngate75 := reject_image perm2 onto2 goal2 src2 _ _ imgate75 ngate107
  have ngate76 := reject_image perm2 onto2 goal2 src2 _ _ imgate76 ngate124
  have ngate77 := reject_image perm2 onto2 goal2 src2 _ _ imgate77 ngate125
  have ngate78 := reject_image perm2 onto2 goal2 src2 _ _ imgate78 ngate126
  have ngate79 := reject_image perm2 onto2 goal2 src2 _ _ imgate79 ngate127
  have ngate80 := reject_image perm2 onto2 goal2 src2 _ _ imgate80 ngate88
  have ngate82 := reject_image perm2 onto2 goal2 src2 _ _ imgate82 ngate89
  have ngate83 := reject_image perm2 onto2 goal2 src2 _ _ imgate83 ngate91
  have ngate100 := reject_image perm1 onto1 goal1 src1 _ _ imgate100 ngate60
  have ngate101 := reject_image perm1 onto1 goal1 src1 _ _ imgate101 ngate62
  have ngate102 := reject_image perm1 onto1 goal1 src1 _ _ imgate102 ngate61
  have ngate103 := reject_image perm1 onto1 goal1 src1 _ _ imgate103 ngate63
  have ngate116 := reject_image perm1 onto1 goal1 src1 _ _ imgate116 ngate64
  have ngate117 := reject_image perm1 onto1 goal1 src1 _ _ imgate117 ngate66
  have ngate118 := reject_image perm1 onto1 goal1 src1 _ _ imgate118 ngate65
  have ngate119 := reject_image perm1 onto1 goal1 src1 _ _ imgate119 ngate67
  have ngate136 := reject_image perm1 onto1 goal1 src1 _ _ imgate136 ngate76
  have ngate137 := reject_image perm1 onto1 goal1 src1 _ _ imgate137 ngate78
  have ngate138 := reject_image perm1 onto1 goal1 src1 _ _ imgate138 ngate77
  have ngate139 := reject_image perm1 onto1 goal1 src1 _ _ imgate139 ngate79
  have ngate140 := reject_image perm1 onto1 goal1 src1 _ _ imgate140 ngate72
  have ngate141 := reject_image perm1 onto1 goal1 src1 _ _ imgate141 ngate74
  have ngate142 := reject_image perm1 onto1 goal1 src1 _ _ imgate142 ngate73
  have ngate143 := reject_image perm1 onto1 goal1 src1 _ _ imgate143 ngate75
  have ngate7 := reject_image perm2 onto2 goal2 src2 _ _ imgate7 ngate45
  have ngate11 := reject_image perm2 onto2 goal2 src2 _ _ imgate11 ngate57
  have ngate31 := reject_image perm1 onto1 goal1 src1 _ _ imgate31 ngate7
  have ngate37 := reject_image perm2 onto2 goal2 src2 _ _ imgate37 ngate31
  have ngate81 := reject_image perm1 onto1 goal1 src1 _ _ imgate81 ngate82
  have ngate84 := reject_image perm2 onto2 goal2 src2 _ _ imgate84 ngate136
  have ngate85 := reject_image perm2 onto2 goal2 src2 _ _ imgate85 ngate138
  have ngate86 := reject_image perm2 onto2 goal2 src2 _ _ imgate86 ngate137
  have ngate87 := reject_image perm2 onto2 goal2 src2 _ _ imgate87 ngate139
  have ngate90 := reject_image perm1 onto1 goal1 src1 _ _ imgate90 ngate37
  have ngate92 := reject_image perm2 onto2 goal2 src2 _ _ imgate92 ngate116
  have ngate93 := reject_image perm2 onto2 goal2 src2 _ _ imgate93 ngate118
  have ngate94 := reject_image perm2 onto2 goal2 src2 _ _ imgate94 ngate117
  have ngate95 := reject_image perm2 onto2 goal2 src2 _ _ imgate95 ngate119
  have ngate96 := reject_image perm1 onto1 goal1 src1 _ _ imgate96 ngate92
  have ngate97 := reject_image perm1 onto1 goal1 src1 _ _ imgate97 ngate93
  have ngate98 := reject_image perm1 onto1 goal1 src1 _ _ imgate98 ngate94
  have ngate99 := reject_image perm1 onto1 goal1 src1 _ _ imgate99 ngate95
  apply root_cases [gate0,gate1,gate2,gate3,gate4,gate5,gate6,gate7,gate8,gate9,gate10,gate11,gate12,gate13,gate14,gate15,gate16,gate17,gate18,gate19,gate20,gate21,gate22,gate23,gate24,gate25,gate26,gate27,gate28,gate29,gate30,gate31,gate32,gate33,gate34,gate35,gate36,gate37,gate38,gate39,gate40,gate41,gate42,gate43,gate44,gate45,gate46,gate47,gate48,gate49,gate50,gate51,gate52,gate53,gate54,gate55,gate56,gate57,gate58,gate59,gate60,gate61,gate62,gate63,gate64,gate65,gate66,gate67,gate68,gate69,gate70,gate71,gate72,gate73,gate74,gate75,gate76,gate77,gate78,gate79,gate80,gate81,gate82,gate83,gate84,gate85,gate86,gate87,gate88,gate89,gate90,gate91,gate92,gate93,gate94,gate95,gate96,gate97,gate98,gate99,gate100,gate101,gate102,gate103,gate104,gate105,gate106,gate107,gate108,gate109,gate110,gate111,gate112,gate113,gate114,gate115,gate116,gate117,gate118,gate119,gate120,gate121,gate122,gate123,gate124,gate125,gate126,gate127,gate128,gate129,gate130,gate131,gate132,gate133,gate134,gate135,gate136,gate137,gate138,gate139,gate140,gate141,gate142,gate143]
  · decide +kernel
  · exact rootDead_cons ngate0 (rootDead_cons ngate1 (rootDead_cons ngate2 (rootDead_cons ngate3 (rootDead_cons ngate4 (rootDead_cons ngate5 (rootDead_cons ngate6 (rootDead_cons ngate7 (rootDead_cons ngate8 (rootDead_cons ngate9 (rootDead_cons ngate10 (rootDead_cons ngate11 (rootDead_cons ngate12 (rootDead_cons ngate13 (rootDead_cons ngate14 (rootDead_cons ngate15 (rootDead_cons ngate16 (rootDead_cons ngate17 (rootDead_cons ngate18 (rootDead_cons ngate19 (rootDead_cons ngate20 (rootDead_cons ngate21 (rootDead_cons ngate22 (rootDead_cons ngate23 (rootDead_cons ngate24 (rootDead_cons ngate25 (rootDead_cons ngate26 (rootDead_cons ngate27 (rootDead_cons ngate28 (rootDead_cons ngate29 (rootDead_cons ngate30 (rootDead_cons ngate31 (rootDead_cons ngate32 (rootDead_cons ngate33 (rootDead_cons ngate34 (rootDead_cons ngate35 (rootDead_cons ngate36 (rootDead_cons ngate37 (rootDead_cons ngate38 (rootDead_cons ngate39 (rootDead_cons ngate40 (rootDead_cons ngate41 (rootDead_cons ngate42 (rootDead_cons ngate43 (rootDead_cons ngate44 (rootDead_cons ngate45 (rootDead_cons ngate46 (rootDead_cons ngate47 (rootDead_cons ngate48 (rootDead_cons ngate49 (rootDead_cons ngate50 (rootDead_cons ngate51 (rootDead_cons ngate52 (rootDead_cons ngate53 (rootDead_cons ngate54 (rootDead_cons ngate55 (rootDead_cons ngate56 (rootDead_cons ngate57 (rootDead_cons ngate58 (rootDead_cons ngate59 (rootDead_cons ngate60 (rootDead_cons ngate61 (rootDead_cons ngate62 (rootDead_cons ngate63 (rootDead_cons ngate64 (rootDead_cons ngate65 (rootDead_cons ngate66 (rootDead_cons ngate67 (rootDead_cons ngate68 (rootDead_cons ngate69 (rootDead_cons ngate70 (rootDead_cons ngate71 (rootDead_cons ngate72 (rootDead_cons ngate73 (rootDead_cons ngate74 (rootDead_cons ngate75 (rootDead_cons ngate76 (rootDead_cons ngate77 (rootDead_cons ngate78 (rootDead_cons ngate79 (rootDead_cons ngate80 (rootDead_cons ngate81 (rootDead_cons ngate82 (rootDead_cons ngate83 (rootDead_cons ngate84 (rootDead_cons ngate85 (rootDead_cons ngate86 (rootDead_cons ngate87 (rootDead_cons ngate88 (rootDead_cons ngate89 (rootDead_cons ngate90 (rootDead_cons ngate91 (rootDead_cons ngate92 (rootDead_cons ngate93 (rootDead_cons ngate94 (rootDead_cons ngate95 (rootDead_cons ngate96 (rootDead_cons ngate97 (rootDead_cons ngate98 (rootDead_cons ngate99 (rootDead_cons ngate100 (rootDead_cons ngate101 (rootDead_cons ngate102 (rootDead_cons ngate103 (rootDead_cons ngate104 (rootDead_cons ngate105 (rootDead_cons ngate106 (rootDead_cons ngate107 (rootDead_cons ngate108 (rootDead_cons ngate109 (rootDead_cons ngate110 (rootDead_cons ngate111 (rootDead_cons ngate112 (rootDead_cons ngate113 (rootDead_cons ngate114 (rootDead_cons ngate115 (rootDead_cons ngate116 (rootDead_cons ngate117 (rootDead_cons ngate118 (rootDead_cons ngate119 (rootDead_cons ngate120 (rootDead_cons ngate121 (rootDead_cons ngate122 (rootDead_cons ngate123 (rootDead_cons ngate124 (rootDead_cons ngate125 (rootDead_cons ngate126 (rootDead_cons ngate127 (rootDead_cons ngate128 (rootDead_cons ngate129 (rootDead_cons ngate130 (rootDead_cons ngate131 (rootDead_cons ngate132 (rootDead_cons ngate133 (rootDead_cons ngate134 (rootDead_cons ngate135 (rootDead_cons ngate136 (rootDead_cons ngate137 (rootDead_cons ngate138 (rootDead_cons ngate139 (rootDead_cons ngate140 (rootDead_cons ngate141 (rootDead_cons ngate142 (rootDead_cons ngate143 ((by simp [rootDead])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end Orbit
end Signed2964

namespace Signed2964
namespace RootCheck
private def q0 : W := 0x0
private def q1 : W := 0x802000400000000000000000000000000000000000000000000000000000000000000000000000000
private def q2 : W := 0x10800000000000020880000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q3 : W := 0x3b8e03b06000000000000001cb32ce72973460307400000000000000000000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def q4 : W := 0x3fc421020000000000000001ebb8840007be42220080000000000000000000001ff000000000000000000000fffe000001ff8000000
private def q5 : W := 0x800000802000427c400000000008217de2000000000000000000000000000000000000000000001f800000000000001ffc000000000000
private def q6 : W := 0xb03801a02f06002ce60000c070400034a739000a0107c00000000000000000007c1e00fc1fe1801fffc000f03c30001fffffe007c1c1f8
private def q7 : W := 0x200000010800000000000040000000002000000010800000000000000000000000000000000000000000000000000000000000000000000
private def q8 : W := 0x200800000000000000000040101000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q9 : W := 0x200804010808800000000040101000802000400810808240000000000000000000000000000000000000000000000000000000000000000
private def q10 : W := 0x401000001001010001008081f000200000080080010f80000000000000000000000000000000000000000000fc000000000000000003e00
private def q11 : W := 0x800000002000000000000100000000000000000002000000000000000000000000000000000000000000000000000000000000000000000
private def q12 : W := 0x1000000004000000020000200000000002100000004000000000000000000000000000000000000000000000000000000000000000000000
private def q13 : W := 0x1004000000000010821100200804000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q14 : W := 0x1e000000178000000200003c02000000021000000178100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q15 : W := 0x3e000000000000000200007c02000000000000000000000000000000000000000f800000000000000000001f000000000000000000000000
private def q16 : W := 0x4802000000000010800008900402000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q17 : W := 0x4802004402002010800008900402020880000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def q18 : W := 0x5e07800000000010821108bc1f070000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q19 : W := 0x80100f81e007002104221100401044f03c0138170e0001c00000000000000000000001f0fc01e000000000000000007e1f801f01e7c00038
private def q20 : W := 0x100201088200902e008e0700080701c1004270871020107400000000000000000000000000000007c007c3e00003c0f800003e01e000001c0
private def q21 : W := 0x200f00111e03800423c402201c02008213ce200224e0302000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def q22 : W := 0x201f00001000000427c402203c020000010000000080000000000000000000000007c0000000000001f800000f00000000000000000000000
private def q23 : W := 0x20840000000000042100022110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q24 : W := 0x400000000000001ff900000000000004000000000000000000000000000000000000000000000007fe0000000000000000000000000000000
private def q25 : W := 0x400802000000001ef7dee00000000004010001000000000000000000000000000000000000000007fffffc000000000000000000000000000
private def q26 : W := 0x580003ea8000706a500a65100005054d200053955000005c00000000000000003f0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def q27 : W := 0x680d02f31c036040734060301400040e338c031064c0200800000000000000003f07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def q28 : W := 0x700e03038003806c638c462018060180300e60160400306000000000000000003f07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
private def q29 : W := 0x7804007b8401000e71000730100001cf308400077440200000000000000000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q30 : W := 0x780f03c01000400e73ce67301c070404010001004080000800000000000000003f07c1e000000007fffffffe0f03c30000000000000000000
private def q31 : W := 0x780f03fb9e03f06e73ce67301c0705cf33ce739774e0307c00000000000000003f07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q32 : W := 0x7c8420400000000f790007b910402004000000004000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def q33 : W := 0x7c84207fc421020f790007b9104021efb8840007fe42220080000000000000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q34 : W := 0x7c8f23ffde23f26f7bce67b91c4725efbbce7397fee2327c80000000000000003f07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q35 : W := 0x7def7bfb9e03f06f7bef77bbddf775cf33ce739774e0307c00000000000000003fffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def q36 : W := 0x7def7bffd421420f7bef77bbddf775efb9840107fec2220880000000000000003ffffffff0000007fffffffffffffffffe000001ff8000000
private def q37 : W := 0x1fe07000000000000000004d6a0002c0b0c000552b5a001a0503c000000000000ffc1c00000000000000001fffc000f03c30001fffffe007c1c1f8
private def q38 : W := 0x4000000000000000000000000000000100000000000000000008000000000000000000000000000000000000000000000000000000000000000000
private def q39 : W := 0x8000000400000001000000000000080200000000000000001010000000000000000000000000000000000000000000000000000000000000000000
private def q40 : W := 0x80010000000000000000000200007c020000000210000001f81000000000000000000000000000000000000000001f0000000000000000003e0000
private def q41 : W := 0x20000000000000000000010001000000800020000008000000040000000000000000000000000000000000000000000000000000000000000000000
private def q42 : W := 0x40000000401000000000010001008083f000000000000000000000000000000000000000000000000000000000000000fc000000000000000000000
private def q43 : W := 0x40008000000000000000010821108fc2f0f00000000000000000000000000000000000000000000000000000000001f0fc3c0000000000000000000
private def q44 : W := 0x1004010800000000000000000000000040101000802000400810808240000000000000000000000000000000000000000000000000000000000000000
private def q45 : W := 0x1ce001c070000000000000000b540a07034000c165594052065c06008000000007fc007c1c0000000000000003ff83c1e0f000307ffffc1fe1ffc1c038
private def q46 : W := 0x20010000000000000000000010000008000400020000000008000020000000000000000000000000000000000000000000000000000000000000000000
private def q47 : W := 0x2007c000000000000000000010001008082f00020000008008001078000000000003f000000000000000000000000000000fc000000000000000003e00
private def q48 : W := 0x21110002000000000000000010800008900402020880000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def q49 : W := 0x5e0003e000000000000000002104221100401045705c0158171e0001c000000007c0007c000000000000000000000000000000007e1f801f01e7c00038
private def q50 : W := 0x80000400000020000020080040084020008020080004220020020102000000000000000000000000000000000000000000000000000000000000000000
private def q51 : W := 0x842004401000000000000000425c402203c02008215d6200225e070200000000000000000000000000000000001f800000f00000001ffc000007c1c000
private def q52 : W := 0x1000008000000000000000001e009e0000000003c10042f0800000000000000000000000000000000000000007c007c000000000f800003e00000000000
private def q53 : W := 0x1ce600ee03000000000000000000000000000002d354d6b4a3356070340000001fffc0ffc1c00000000000000000000000000000fffffffffffffc1c1f8
private def q54 : W := 0x1ef7100020000000000000000000000000000002f3d8840003be4222008000001fffc00000000000000000000000000000000000fffe000001ff8000000
private def q55 : W := 0x2000000000100000000000001f00000f8000400000000000000000000000000000000000000000000000000007c00003e00000000000000000000000000
private def q56 : W := 0x2000010000100201000000001e009e0f00080f0000000000000000000000000000000000000000000000000007c007c3e00003c00000000000000000000
private def q57 : W := 0x21080000000000000000000017b9000bf910402004000000004000000000000000000000000000000000000007fe0003fe0000000000000000000000000
private def q58 : W := 0x21080110040000000000000016b5d6ab703c0b0c04010001004080000800000000000000000000000000000007fffffffe0f03c30000000000000000000
private def q59 : W := 0x35ac01ba0600000000000000129012a95000090e55400095a15000001c0000001fffc0ffc1c000000000000007fe07fffe0003c3fffe003fffff80001f8
private def q60 : W := 0x380e01c0070000000000000014a5948a60380a0a805016a022040070200000001f83c0f801c000000000000007fffffffe0f03c3f81e07fe0fe1801c1c0
private def q61 : W := 0x3c2001e200000000000000001600960b00080b02c10042b083102010340000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def q62 : W := 0x3dee0000000000000000000016b1000b70100002d750840003744020000000001fffc000000000000000000007fe0003fe000000fffe000001ff8000000
private def q63 : W := 0x3dee01fe070000000000000016b5d6ab703c0b0ed755d6b5a375e0703c0000001fffc0ffc1c000000000000007fffffffe0f03c3fffffffffffffc1c1f8
private def q64 : W := 0x3dee41fe870000000000000017bdf7bbfffefbfed755d6b5a375e0703c0000001fffc0ffc1c000000000000007fffffffffffffffffffffffffffc1c1f8
private def q65 : W := 0x3fff11fe270000000000000017bdd6abf93c4b2ef7ddd6b5a3ffe2723c8000001fffc0ffc1c000000000000007fffffffe0f03c3fffffffffffffc1c1f8
private def q66 : W := 0x3fff5110a40000000000000017bdf7bbfffefbfef7d9840103fec222088000001fffc000000000000000000007fffffffffffffffffe000001ff8000000
private def q67 : W := 0x7800003c007001a070000068060069cc000280e0800001ae03000005060000001e00000f801c007c1e00001e01801fffc000f03c3000007fe0e00001c1c0
private def q68 : W := 0x10000080000000401000001001000000000001000000000000000000080000000000000000000000000000000000000000000000000000000000000000000
private def q69 : W := 0x100000ec000000401000001001000001000083b000000000080000010d8000000000003f000000000000000000000000000000fc000000000000000003e00
private def q70 : W := 0x100200bc0000000000000010010000000000000000200000080080010f8000000000003f00000000000000000000000000000000000000000000000003e00
private def q71 : W := 0x100200dc0000004010000010010000000080837000000000000080010b8000000000003f000000000000000000000000000000fc000000000000000003e00
private def q72 : W := 0x100200f4000000001000000001010001008003d000200000080080000e8000000000003f000000000000000000000000000000fc000000000000000003e00
private def q73 : W := 0x100200f8000000401000001001010001008083e000200000080080010f0000000000003f000000000000000000000000000000fc000000000000000003e00
private def q74 : W := 0x100200fc000000000000000000000000000002000000000000000000000000000000003f00000000000000000000000000000000000000000000000000000
private def q75 : W := 0x100200fc000000401000001001010001008083f000200000080080010f8000000000003f000000000000000000000000000000fc000000000000000003e00
private def q76 : W := 0x100a00fc40000042100002108105008502808bf200a00042280280211fa000000000003f000000000000000000000000000000fc000000000000000003e00
private def q77 : W := 0x102200fd0000104211000010011f009f0f808bff00200000080080010f8000000000003f00000000000000000007c007c3e000ffc00000000000000003e00
private def q78 : W := 0x20000000000003e0000001f8000000000000000000000000000000000000000000000000000000f80000003e0000000000000000000000000000000000000
private def q79 : W := 0x20000000001003a0000001e80000002000074000000000210000001e8000000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q80 : W := 0x2000000800100000000001f80000000000000000000000210000001f8100000000000000000000000000003e00000000000000000000000000000003e0000
private def q81 : W := 0x20000008001002000000008000000000000400000000000000000008000000000000000000000000000000000000000000000000000000000000000000000
private def q82 : W := 0x20000008001002e0000001b8000000000005c020000000000000001b8100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q83 : W := 0x2000000800100360000001d8000000200006c020000000210000001d8100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q84 : W := 0x20000008001003c0000000f00000002000078020000000010000000f0100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q85 : W := 0x20000008001003e0000001f8000000200007c020000000210000001f8100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q86 : W := 0x20000008001023ff000011f8000427e40227fc22000001210000009f8100000000000000000000ffc000003e000001f80001ff000000000000000003e0000
private def q87 : W := 0x20080008401003e2000003f8800400a40207c822008000632002003f9120000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q88 : W := 0x80000020004000000000004004000000000000000020882108480004040100000000000000000000000000000000000000000000000000000000000000000
private def q89 : W := 0x80000020004001004000004004000021100200804000002108480004040100000000000000000000000000000000000000000000000000000000000000000
private def q90 : W := 0x80000020004001084000084204052fe51002008040a29fff2848000404010000000000000000000000000000000001f800000000000001ffc000000000000
private def q91 : W := 0x800000200040410842000040041ffffff00200804024892109480004040100000000000000000000000000000007fffffc000000000000000000000000000
private def q92 : W := 0x801000208040010040000040041f08bf1002008043e18863f8c80004040100000000000000000000000000000007c007c000000000f800003e00000000000
private def q93 : W := 0x100000000000007e0f8000000000000000000010000000000000000000000000000000000000000f83e0000000000000000000000000000000000000000000
private def q94 : W := 0x100000000008007a0e800000000000820100f4000f0000000000000000000000000000000000000f83e000000000000000001f0003c0000000000000000000
private def q95 : W := 0x100000040008002008000000000000000000402008000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q96 : W := 0x10000004000800360d8000000000000211006c3b0d0000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q97 : W := 0x10000004000800400f800000000010801108803d0f0000000000000000000000000000000000000003e00000000000000000000fc3c0000000000000000000
private def q98 : W := 0x100000040008006e0b800000000000000008dc370b0000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q99 : W := 0x100000040008007c0f000000000010821108f83e0e0000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q100 : W := 0x100000040008007e0f800000000010821108fc3f0f0000000000000000000000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q101 : W := 0x100000040008027fff800100000052fe512affff2f0000100000000800000000000000000000000fffe000000000001f80001fffc3c0000000000000000000
private def q102 : W := 0x100200041008017e2f9000000001f08bf1f8fcbfff0000000000000000000000000000000000000f83e0000000007c007c3e1f0fffc0000000000000000000
private def q103 : W := 0x208000004010800200800010808800000000040101000002000400010808240000000000000000000000000000000000000000000000000000000000000000
private def q104 : W := 0x3b800008000000360d80001d80d800000000001000000000000000000080000007e000000000000f83e00003e01e0000000000000000000000000000000000
private def q105 : W := 0x3b80000ec01d802008000008000000000000402008000000000000008000000007e00003f003e0000000000000000000000000000000000000000000000000
private def q106 : W := 0x400800003e2000002010002009020009e0000080f00000042f08000201074000000000000f80000000000000000000007c0000003c00000003e000000001c0
private def q107 : W := 0x4108000aee200000000000210912000000000000000000042f88000211df400000000003ff8000000000000000000000000000000000000003e00000003fc0
private def q108 : W := 0x4108000efe2000042110002109120009f00008bbf00000042f88000211df400000000003ff80000000000000000000007c00000ffc00000003e00000003fc0
private def q109 : W := 0x4108200ffe2000042110002109121009f00808bff00200042f88080211ff400000000003ff80000000000000000000007c00000ffc00000003e00000003fc0
private def q110 : W := 0x410a000efe200104211000210913f009f0f808bff00000042f88000211df400000000003ff8000000000000000007c007c3e000ffc00000003e00000003fc0
private def q111 : W := 0x8010000004401001b00003a06800006c400002c020000075a200001a0502000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def q112 : W := 0x8210000084411000000002bde80000000000000000000067b2000013dd1200000000000000000000000000fffe000000000000000000001ffc000007ffc000
private def q113 : W := 0x8210000084411037b00003bde800006e40006ec220000077b200001bdd120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q114 : W := 0x821000008441103fb00003bfe800006e40007ec220000077b200001bfd120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q115 : W := 0x821000008441123ff00003bde800427e40227fc220000077b200001bdd120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q116 : W := 0x10020000008802000802000802204006dee00000000000075af7b0000000000000000000000000000000000000000001fffc000000000001fffffe000000000
private def q117 : W := 0x1082000020884200000000084224400000000000000000067bfef80004040100000000000000000000000000000000000000000000000001fffffe000000000
private def q118 : W := 0x1082000020884201084200084224410efff002008040208f7bfff8000404010000000000000000000000000000000001fffc000000000001fffffe000000000
private def q119 : W := 0x10820000208842410842000842245ffffff00200804004077bfff80004040100000000000000000000000000000007fffffc000000000001fffffe000000000
private def q120 : W := 0x1c03800002ee03000000002a06b0600000000000000000065af6b001205074000f81e00000ffc1c00000000fc1fe18000000000000000001fffffe007c1c1f8
private def q121 : W := 0x1e080000042f08000000002b0838800000000000000000066016c001308096400f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def q122 : W := 0x1ebb8000820000000000002bdebde000000000000000000208421000000840000fffe000000000000000000ffffff8000000000000000000000000000000000
private def q123 : W := 0x1ebb8000aeef5b000000002084000000000000000000000410842001084000000fffe0003fffffc000000000000000000000000000000000000000000000000
private def q124 : W := 0x20040000011004001b07801000400006dee0002c0f0c00010001000080000800000000000000000007c1e00000000001fffc000f03c30000000000000000000
private def q125 : W := 0x21040000411084037bdf801000400006fff006efbfdc000100010000800008000000000000000000ffffe00000000001fffc01ffffff0000000000000000000
private def q126 : W := 0x2104000041108407fbff80100040010efff08feffffc000100010000800008000000000000000000ffffe00000000001fffc01ffffff0000000000000000000
private def q127 : W := 0x2c058000037605001305803204d020000000002c0f0c000000000001a0507c000f81e00000ffc1c007c1e00fc1fe18000000000f03c30000000000007c1c1f8
private def q128 : W := 0x3406800003ba060000078000007060001ae000000d0c000000d7b00000005c000f81e00000ffc1c00001e000001e180007fc000003c30000003ffe0000001f8
private def q129 : W := 0x38070000001c0700190680380660400640e00024000c000718073001804008000f81e0000007c1c007c1e00fc1fe1801f83c000f00030001ffc1fe007c1c038
private def q130 : W := 0x3c000000003e00000100803a00700000422000040104000740178001a0001c000f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def q131 : W := 0x3c078000020000001b07803a06f06002084000000400000208421000000040000f81e0000000000007c1e00fc1fe18000000000000000000000000000000000
private def q132 : W := 0x3c07800003fe07001004002004000004108000200808000410842001004000000f81e00000ffc1c000000000000000000000000000000000000000000000000
private def q133 : W := 0x3c07800003fe07001b07803a06f06006dee0002c0f0c00075af7b001a0507c000f81e00000ffc1c007c1e00fc1fe1801fffc000f03c30001fffffe007c1c1f8
private def q134 : W := 0x3d07800043fe87037bdf803a06f06006fff006efbfdc00075af7b001a0507c000f81e00000ffc1c0ffffe00fc1fe1801fffc01ffffff0001fffffe007c1c1f8
private def q135 : W := 0x3e080000043f08002108803b0878800042200044111400076017c001b0809e400f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def q136 : W := 0x4040020110002004802000402002010800008900402020080000008202020080000000000000000000000000000000000000000000000000000000000000000
private def q137 : W := 0x8000f80003c000100201008000803c009c0e00080e03800002e006000010600000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def q138 : W := 0x8010fa00fbc000104211008010813d009d0e808bee03a00002e80680011f600000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q139 : W := 0x8010fa00ffc000104211008010813d009d0e808bfe03a00002e80680011fe00000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q140 : W := 0x100010802004001201e0001000780042784022038020080101e20020400702000000000000000000007c0000001e00001f800000f0000000007c00000001c000
private def q141 : W := 0x10021080208401123de000100f7800427a40227b8220080101f2002040f7120000000000000000000ffc000003fe00001f80001ff0000000007c0000003fc000
private def q142 : W := 0x10021080208401123fe000101ff800427a40227f8220080103f2002041ff120000000000000000000ffc000003fe00001f80001ff0000000007c0000003fc000
private def q143 : W := 0x200021004008002400802020002005ce79cc00000000380701ee0300000000000000000000000000000000000000007fffffc00000000f81e07fe0e000000000
private def q144 : W := 0x200821004208042410842020042045defbdd002008043a0f83fe8780004040100000000000000000000000000000007fffffc00000000f81e07fe0e000000000
private def q145 : W := 0x38003d80602c00300000003800780600000000000000380701ee0360400706001f001ff83c0f801c0000000f001e01800000000000000f81e07fe0fe1801c1c0
private def q146 : W := 0x3c0405a0710002000000003c021020000000000000003a0780400068602220081f0001f83c0000000000000f000000000000000000000f81e000001e18000000
private def q147 : W := 0x400002008000000f48420000000001de9000ee910402000000000000000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def q148 : W := 0x400042008010004f01e07000000001ce79cce60380e0800000000000000000000000000000000003f07c1e000000007fffffffe0f03c30000000000000000000
private def q149 : W := 0x401042008410084f7def7000000001defbddeefbbeee800000000000000000000000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q150 : W := 0x401042008410084f7feff000000001defbddeeffbfef800000000000000000000000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q151 : W := 0x58005e80a034005b01605018005802000000e60380e0800000000060400706001f001ff83c0f801ff07c1e0f001e018000003fe0f03c30000000001e1801c1c0
private def q152 : W := 0x68006f00c038006d000070280000078c018cc40000c0b006000c0340000004001f001ff83c0f801ff0001e0f000001ffe07fffe0003c3f81e003e0fe180001c0
private def q153 : W := 0x70007000e000007e01c060300070040e700c06030000800701c00300400600001f001e003c00001ff07c1e0f001e0183ff83c1e0f0003001e07c00e01801c000
private def q154 : W := 0x78000780e000000f00400038001001ce1000e6010000380700400060400200001f0001f83c000003f000000f0000007fe0003fe000000f81e000001e18000000
private def q155 : W := 0x78007c000020000f01e0703800780684208440000040100200840140000004001f001e0000000003f07c1e0f001e018000000000000000000000000000000000
private def q156 : W := 0x78007f80e03c00780100400000400108410884020080a00401080200000400001f001ff83c0f801c000000000000000000000000000000000000000000000000
private def q157 : W := 0x78007f80e03c007f01e07038007807ce79cce60380e0b80701ee0360400706001f001ff83c0f801ff07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
private def q158 : W := 0x78107f80e43c087f7def7038007807defbddeefbbeeeb80701ee0360400706001f001ff83c0f801ffffffe0f001e01ffffffffffffffff81e07fe0fe1801c1c0
private def q159 : W := 0x7c0407a0f100020f4842003c021021de9000ee9104023a0780400068602220081f0001f83c000003f000000f0000007fe0003fe000000f81e000001e18000000
private def q160 : W := 0x7c047fa0f13c027f49e2703c027827def9ccee9384e2ba0781ee0368602726081f001ff83c0f801ff07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
private def q161 : W := 0x7c1447a0f5100a4f7def703c021021defbddeefbbeeeba0780400068602220081f0001f83c000003fffffe0f0000007fffffffffffffff81e000001e18000000
private def q162 : W := 0x80000001000000000000004000000000000000000000000800000000800000000000000000000000000000000000000000000000000000000000000000000000
private def q163 : W := 0x80208000000000000200804010808800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q164 : W := 0x80208001000010800200804010808800000000040001000802000400810800240000000000000000000000000000000000000000000000000000000000000000
private def q165 : W := 0x80208001004010800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q166 : W := 0x80208001004010800000004010808800000000000000000802000400810808240000000000000000000000000000000000000000000000000000000000000000
private def q167 : W := 0x80208001004010800000804000008800000000000101000800000400800008240000000000000000000000000000000000000000000000000000000000000000
private def q168 : W := 0x80208001004010800200804010808800000000040101000000000000810808240000000000000000000000000000000000000000000000000000000000000000
private def q169 : W := 0x80208001004010800200804010808800000000040101000802000400810808240000000000000000000000000000000000000000000000000000000000000000
private def q170 : W := 0x83e080010043f08002108843b0878800042200044111400876017c009b0809e400f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def q171 : W := 0x84040000000000004802004402002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q172 : W := 0x84040001100002004802004402002000800000900002000880000000a02000080000000000000000000000000000000000000000000000000000000000000000
private def q173 : W := 0x84040021110002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q174 : W := 0x84040021110002000000004402002000000000000000020880000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def q175 : W := 0x84040021110002004002004400002010800008800402020880000008a00020080000000000000000000000000000000000000000000000000000000000000000
private def q176 : W := 0x84040021110002004802004402002000000008900402000000000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def q177 : W := 0x84040021110002004802004402002010800008900402020880000008a02020080000000000000000000000000000000000000000000000000000000000000000
private def q178 : W := 0x8414002115000a007e0f804402002010821108fc3f0f020880000008a020200800000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q179 : W := 0x842f800008000000000000441f80f800000000000000000000000000000080000007e000000000000000000003e01e0000000000000000000000000000000000
private def q180 : W := 0x842f80211bc017800000000008000000000000000000000000000000008000000007e00003f003e0000000000000000000000000000000000000000000000000
private def q181 : W := 0x87fff800082000007fbff847bfeffe002084000010400000208421000000840000fffe00000000000ffffe00ffffff8000000000000000000000000000000000
private def q182 : W := 0x87fff8211ffffff021084002084000004108004220888000410842001084000000fffe0003fffffc000000000000000000000000000000000000000000000000
private def q183 : W := 0xfc0407a1f100020f4842007c021021de9000ee9104023a0f80400068e02220081f0001f83c000003f000000f0000007fe0003fe000000f81e000001e18000000
private def q184 : W := 0xfc3ffc000820000f7feff07c1ff8fe84208440001040100200840140000084001f07fe0000000003fffffe0f03fe1f8000000000000000000000000000000000
private def q185 : W := 0xfc3fffa1fffc1ff82108400008400108410884422088a00401080200008400001f07fff83fff83fc000000000000000000000000000000000000000000000000
private def q186 : W := 0x100400042000220000000008020010020002010000010041004010811020001400000000000000000000000000000000000000000000000000000000000000000
private def q187 : W := 0x1004100620fc220000401008021011030003018083f100610040188190210f9400000000003f000000000000000000000000000000fc000000000000000003e00
private def q188 : W := 0x1080005e20100000000000088000000000000000000003e100000007900002000000001f80000000000000000000000000000000000000f800000001e00000000
private def q189 : W := 0x1080007c20000000100000088000001e00000f00000003c100000007100000000000001f800000000000000000000007c00003e0000000f800000001e00000000
private def q190 : W := 0x1080007e20510000104211088000001f009f0f808bff03e100000007900002000000001f800000000000000000000007c007c3e000ffc0f800000001e00000000
private def q191 : W := 0x1080107e20fc0000104010088010011f00010f8083f003e10000080790010f800000001f803f00000000000000000007c00003e000fc00f800000001e00003e00
private def q192 : W := 0x108400c00002000010020108820090280008040000040100000040040000004000000000000000000000000000000000000000000000000000000000000000000
private def q193 : W := 0x108400dc2002e200000000088200902000000000000003c10042f087102010740000001f8000f800000000000000000000000000000000f800003e01e000001c0
private def q194 : W := 0x108400ec20036200100201088200902000000f00080f000000000007102010740000001f8000f8000000000000000000000003e00003c00000000001e000001c0
private def q195 : W := 0x108400f42003a200100001088000103a001a0d00000d03410000d085100000540000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def q196 : W := 0x108400fc2003e2000000000000000010001008000008020000008000000000000000001f8000f8000000000000000000000000000000000000000000000000000
private def q197 : W := 0x108400fc2003e200100201088200903e009e0f00080f03c10042f087102010740000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def q198 : W := 0x108400fc2043e200104211088200903f009f0f808bff03c10042f087102010740000001f8000f8000000000000000007c007c3e000ffc0f800003e01e000001c0
private def q199 : W := 0x108400fe2013e200100201088200903f009e0f80084f03e10042f087902012740000001f8000f8000000000000000007c007c3e00003c0f800003e01e000001c0
private def q200 : W := 0x108410de20fee20000401008821091210001008083f003e10042f88790211ff40000001f803ff80000000000000000000000000000fc00f800003e01e00003fc0
private def q201 : W := 0x108410de20ffe2000042110882109120009f00008bbf03e10042f88790211ff40000001f803ff80000000000000000000007c00000ffc0f800003e01e00003fc0
private def q202 : W := 0x108410ee20df6200104211088210912000000f808b7f00000000000790211bf40000001f803ff8000000000000000000000003e000ffc00000000001e00003fc0
private def q203 : W := 0x108410f620ffa200104011088010113b001b0d8083fd03610000d88590010fd40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q204 : W := 0x108410fc20efe200104211088210913e009f0f008bbf03c10042f88710211df40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q205 : W := 0x108410fe20bfe200100201088210913e009e0f00080f03e10042f88790211ff40000001f803ff8000000000000000007c007c3e00003c0f800003e01e00003fc0
private def q206 : W := 0x108410fe20f7e200100211088200913f009f0f800bdf03e10042f88790201ef40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q207 : W := 0x108410fe20fbe200104211088210913f009f0f808bef03e10042f88790211f740000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q208 : W := 0x108410fe20ffe200104211088210913f009f0f808bff03e10042f88790211ff40000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q209 : W := 0x108430fe20ffe21013e2110883f8913f00bf0f87cbff03e10063f887903f9ff40000001f803ff80000f80000003e0007c007c3e1f0ffc0f800003e01e003e3fc0
private def q210 : W := 0x108510fe20ffe28017e2f9088210913f08bf1f8fcbfff3e10042f88790211ff40000001f803ff80000f83e0000000007c007c3e1f0fffcf800003e01e00003fc0
private def q211 : W := 0x10bc17fe20fffe07105b1788ba16f17f06dfef80afff0fe1075affb791a15ffc000f81ff803fffc1c007c1e00fc1fe1fc1ffffe00fffc3f801ffffffe07c1fff8
private def q212 : W := 0x178417fe2effe207f05e170b8217917fe79fcfe0bbff0be1705ef8b794217ff401f001ff83fff801ff07c1e0f001e01ffffffffe0fffc3f81e07fe0fe1801ffc0
private def q213 : W := 0x18060804300423080020080c030818820002010040111041806010c11830809640000000000000000000000000000000000000000000000000000000000000000
private def q214 : W := 0x188618fe30ffe3081062190c831899bf009f0f80cbff13e18062f8c798319ff64000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q215 : W := 0x18c0407e311000201480200cc020021f08000f89004023e1880000079a0202008000001f800000000000000000000007c00003e0000000f800000001e00000000
private def q216 : W := 0x18c450fe31ffe22014c2310cc230933f089f0f898bff23e18842f8879a231ff48000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0
private def q217 : W := 0x18c7f8c00082000017e2f90cc3f89fa80008040001040100000040040000084000007e000000000000f83e00003e01e0000000000000000000000000000000000
private def q218 : W := 0x18c7f8fe31ffe3f802008000008000100010080402088200000080000008000000007e1f803ff83e0000000000000000000000000000000000000000000000000
private def q219 : W := 0x2008000040000400000100103e000000004000000400000207c0000021e000000000000000000000000000000fc00000000000000000000001f80000007c00000
private def q220 : W := 0x200820004008041003e100103ff8000000600007c420000207e1000021ff8100000000000000000000f800000ffe000000000001f000000001f80000007fe0000
private def q221 : W := 0x210000084200000000000011042100000000000000000082108400022442200000000000000000000000000000000000000000000000000000000000000000000
private def q222 : W := 0x210000084200000020040011040100042100022010000082108400022440200000000000000000000000000000000000000000000000000000000000000000000
private def q223 : W := 0x210000084200000020840011042100042100022110000082108400022442200000000000000000000000000000000000000000000000000000000000000000000
private def q224 : W := 0x210000084200000023ff00111421000427e40227fc2200821184000224c22000000000000000000000ffc0000000000001f80001ff00000000000000000000000
private def q225 : W := 0x210020084208001023e4001105f9000421200227d020008210a50002245fa100000000000000000000f80000003e000000000001f0000000000000000003e0000
private def q226 : W := 0x2108010000000000201f00113e0780000200000000000000020800000000000000000000000000000007c0000fc1e000000000000000000000000000000000000
private def q227 : W := 0x2108010042000401201d00113c0700002740002034000002179c000025c0600000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def q228 : W := 0x2108010842004401000000112e078000000000000000008216de2002256070200000000000000000000000000fc1e000000000000000000001ffc000007c1c000
private def q229 : W := 0x210801084200440100100000200400000400000020000000041000000100400000000000000000000000000000000000000000000000000000000000000000000
private def q230 : W := 0x21080108420044012017001136058000000002203c0200000000000225e0702000000000000000000007c0000fc1e000000000000f00000000000000007c1c000
private def q231 : W := 0x2108010842004401201f00113e07800427c402203c02008217de200225e0702000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def q232 : W := 0x2108010842004401209f00113e27800427c402213c02008217de200225e2702000000000000000000007c0000fc1e00001f800000f00000001ffc000007c1c000
private def q233 : W := 0x210801084200440123ff00113e07800427e40227fc22008217de200225e07020000000000000000000ffc0000fc1e00001f80001ff00000001ffc000007c1c000
private def q234 : W := 0x210821004208041123fd00113dff000027600027f420000217bd000025dfe100000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q235 : W := 0x210821084200441123bf00113fef800427e402277c02008217ff200225fef020000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q236 : W := 0x2108210842084411037b00113fff800006e40006ec22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q237 : W := 0x210821084208441103e000112fff800000200007c020008216ff2002257ff120000000000000000000f800000fffe00000000001f000000001ffc000007ffc000
private def q238 : W := 0x2108210842084411201f00113fff800427c402203c02008217ff200225fff12000000000000000000007c0000fffe00001f800000f00000001ffc000007ffc000
private def q239 : W := 0x210821084208441122f7001137bd800000000225fc2200000000000225fbf120000000000000000000ffc0000fffe00000000001ff00000000000000007ffc000
private def q240 : W := 0x2108210842084411237f00113fdf800427e40226fc22008217ff200225fdf120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q241 : W := 0x210821084208441123df00113ef7800427e40227bc22008217df200225ef7120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q242 : W := 0x210821084208441123ff00113fff800427e40227fc22008217ff200225fff120000000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q243 : W := 0x2108310a42fc441123ff10113fff810527e502a7fff200a217ff2802a5ffffa000000000003f000000ffc0000fffe00001f80001fffc000001ffc000007fffe00
private def q244 : W := 0x210921084248449127fff8113fff80052fe512affff2f08217ff200225fff120000000000000000000fffe000fffe00001f80001fffc3c0001ffc000007ffc000
private def q245 : W := 0x213c2788420bfe1723ff07913ffff06427fee227fc2f0c8217fff7b225fff17c000f81e00000ffc1c0ffc1e00ffffe1801fffc01ff03c30001fffffe007ffc1f8
private def q246 : W := 0x278827f84e0bc417f3ff0713bfff807ce7fcce67fc2e0b8277ffe03625fff16001f001ff83c0f801ffffc1e0ffffe01fffffffffff03c3f81ffffe0fe1fffc1c0
private def q247 : W := 0x280a080050040508002108143f080880004000004410100287e0004029f080824000000000000000000000000fc00000000000000000000001f80000007c00000
private def q248 : W := 0x290a2908520c451923ff08153fff888427e40227fc32108297ff20422dfff1a2400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q249 : W := 0x2940400a531000202484201544210205290002a9104020a298840002ae42220080000000000000000000000000000000000000000000000000000000000000000
private def q250 : W := 0x2948610a5318443127ff20157fff82052fe402affc6220a29fff2002affff320800000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000
private def q251 : W := 0x294bf9000080000027fff8157fff8f800200000001000000020800000000080000007e000000000000fffe000fffe1e0000000000000000000000000000000000
private def q252 : W := 0x294bf90a53fc45f902108000208400000400000422008000041000000108400000007e00003f003e0000000000000000000000000000000000000000000000000
private def q253 : W := 0x318c01cc6202660100000019a6059020000000000000000000000007356070743fff81ffffc0ffc1c000001fffc1fe18000000000000000000000001fffc1c1f8
private def q254 : W := 0x318c11fe62ffe601305f1119be17913f27df0fa0bfff03e317def887b5e17ff40000001f803ff8000007c0000fc1e007c1ffc3e00fffc0f801fffe01e07c1ffc0
private def q255 : W := 0x318c21fc620be61133ff0119bfff903e27fe0f27fc2f03c317fff08735fff1740000001f8000f80000ffc0000fffe007c1ffc3e1ff03c0f801fffe01e07ffc1c0
private def q256 : W := 0x39c0404e731000200000001dc4210200000000000000000000000007be422200bff0001fffc000000000001ff0000000000000000000000000000001ff8000000
private def q257 : W := 0x40100000800008000000002008002002104220000000005f07c0178000000000000000000000000000000000000000000000000000000007e1f801f0000000000
private def q258 : W := 0x40108000802008400100402008402403186330020080407f8fe11fc800040401000000000000000000000000000000000000000000000007e1f801f0000000000
private def q259 : W := 0x4200001084000000000000220000000000000000000003fbf8840000000000000000000000000000000000000000000000000000000000fffe000000000000000
private def q260 : W := 0x4200001084000000400000220000001ef1000000000003df708400000000000000000000000000000000000000000007fe000000000000fffe000000000000000
private def q261 : W := 0x4200001084000000410842220000001ffffff002008043fff98401000000000000000000000000000000000000000007fffffc00000000fffe000000000000000
private def q262 : W := 0x4200801084200040410040220040041ff9211002008043fff8a508480004040100000000000000000000000000000007fe000000000000fffe000000000000000
private def q263 : W := 0x42100200840008024008022208022040f740e0000000001e779c073000000000000000000000000000000000000000003ff83c0000000007ffffc1fe000000000
private def q264 : W := 0x4210021084008802000000220802204000000000000003db76def6b0000000000000000000000000000000000000000000000000000000fffffffffe000000000
private def q265 : W := 0x4210021084008802400002220000205ad01ae0000000035d6000d7b00000000000000000000000000000000000000007fe07fc00000000fffe003ffe000000000
private def q266 : W := 0x4210021084008802400802220802205fffdee000000003ffffdef7b00000000000000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q267 : W := 0x4210021084008802410842220802205ffffff002008043df77def7b00000000000000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q268 : W := 0x42108200842008424108422208422441ff61f0020080403effbd0f7800040401000000000000000000000000000000003ff83c0000000007ffffc1fe000000000
private def q269 : W := 0x4210821084008842410842220842245efffef002000043dffffff7f80004000100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q270 : W := 0x4210821084208842010040220842244108211002008043fbfefffef8000404010000000000000000000000000000000000000000000000fffffffffe000000000
private def q271 : W := 0x4210821084208842010842220842244006fff002008043fbfffffff8000404010000000000000000000000000000000001fffc00000000fffffffffe000000000
private def q272 : W := 0x4210821084208842400802220842245ef7dee000000003fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q273 : W := 0x4210821084208842400842220802245fffdff000008043ffffdefff80000040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q274 : W := 0x4210821084208842410042220040245bd83bf0020080437de821dff80004040100000000000000000000000000000007fe07fc00000000fffe003ffe000000000
private def q275 : W := 0x4210821084208842410842220842245ef7fff002008043df77fffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q276 : W := 0x4210821084208842410842220842245ffffff002008043ff7fdfffb80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q277 : W := 0x4210821084208842410842220842245ffffff002008043fffffffff80004040100000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q278 : W := 0x4210921284fc8842414852220852255ffffff08283f043fffffffff880050f8100000000003f00000000000000000007fffffc0000fc00fffffffffe000003e00
private def q279 : W := 0x4210a2108428885243e8422209fa245ffffff007c0a043fffffffff8001f8501000000000000000000f80000003e0007fffffc01f00000fffffffffe0003e0000
private def q280 : W := 0x42118210846088c247e8fa220842245ffffff08fc3f0f3fffffffff800040401000000000000000000f83e0000000007fffffc01f0fc3cfffffffffe000000000
private def q281 : W := 0x423c87908423fe47411b47a23a46f47ffffff0022c8f4ffffffffff801a4547d000f81e00000ffc1c007c1e00fc1fe1ffffffc000f03c3fffffffffe007c1c1f8
private def q282 : W := 0x479087f88e23c847f11e47238847a47ffffffe62388e4bfffffffffe0404746101f001ff83c0f801ff07c1e0f001e01ffffffffe0f03c3ffffffffffe1801c1c0
private def q283 : W := 0x4a128a109424894a41284a26094a2cdffffff002409053fffffffff80814848340000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q284 : W := 0x4a50c21295308862458862264862265ffffff08b00c063fffffffff88a06060180000000000000000000000000000007fffffc00000000fffffffffe000000000
private def q285 : W := 0x529402d4a402aa020000002a8000306000000000000003596000d6b5100000543fff81ffffc0ffc1c000001ff0001e1800000000000000fffe003fffff80001f8
private def q286 : W := 0x529482fca423ea42510a432a8a42b47fffffff02088f43ffffffffff102414750000001f8000f8000000000000000007ffffffe00003c0ffffffffffe000001c0
private def q287 : W := 0x529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff50000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0
private def q288 : W := 0x5ac04056b51000200000002ec00002000000000000000379e80000059a000200bff0001fffc000000000001ff000000000000000000000fffe000001ff8000000
private def q289 : W := 0x63180300c6000c03000000332c072040000000000000001a769c0630254060003fff81e07fc007c1c000001fffc1fe180000000000000007ffffc1fe1ffc1c038
private def q290 : W := 0x63188318c620cc43611f42333e47a45ffffff2223c8243fffffffffa25e4742100000000000000000007c0000fc1e007fffffc000f0000fffffffffe007c1c000
private def q291 : W := 0x6318a318c628cc5363ff42333fffa45ffffff227fca243fffffffffa25fff521000000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000
private def q292 : W := 0x6b404000d70000200000003744210200000000000000001af88400002e422000bff000007fc000000000001ff00000000000000000000007fe0000001f8000000
private def q293 : W := 0x701c0004e0002e00000000382e003000000000000000005b06c01681316000143e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q294 : W := 0x7380005ce60000000000003b8401000000000000000003db70840007344020003ff0001fffc000000000001ff000000000000000000000fffe000001ff8000000
private def q295 : W := 0x739c03c0000200000000003bae07b060000000000000010822084214000000403fff81e0000000000000001fffc1fe18000000000000000000000000000000000
private def q296 : W := 0x739c03dce602ee030000000020040000000000000000021044108420010040003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def q297 : W := 0x739c03dce602ee030000003bae07b06000000000000003db76def6b7356070743fff81ffffc0ffc1c000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def q298 : W := 0x739c13fee6ffee031042113bae17b17f009f0f808bff03fb76defeb7b5617ff43fff81ffffffffc1c000001fffc1fe1fc007c3e000ffc0fffffffffffffc1fff8
private def q299 : W := 0x739c23dce60aee1323ff003bbfffb06427e40227fc2203db77fff6b735fff1743fff81ffffc0ffc1c0ffc01ffffffe1801f80001ff0000fffffffffffffffc1f8
private def q300 : W := 0x739c83dce622ee434108423bae47b47ffffff002008043ffffffffff356474753fff81ffffc0ffc1c000001fffc1fe1ffffffc00000000fffffffffffffc1c1f8
private def q301 : W := 0x73bc07dce603fe07001b07bbbe07f06006dee0002c0f0fdb77def7b735e0707c3fff81ffffc0ffc1c007c1ffffc1fe1801fffc000f03c3fffffffffffffc1c1f8
private def q302 : W := 0x78000004f00000000000003c04000000000000000000005b80800001384000003e0000007c0000000000001f000000000000000000000007e00000001e0000000
private def q303 : W := 0x781e0804f0042f080020083c2f083880000000004010105b86e016c1397080967e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q304 : W := 0x783e0804f0043f08002108bc3f087880004220004411145b87e017c139f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q305 : W := 0x7bc04040000000000000003fc4210200000000000000010820000004000000003ff00000000000000000001ff0000000000000000000000000000000000000000
private def q306 : W := 0x7bc0405ef71000200000000000000000000000000000021040000000000000003ff0001fffc000000000000000000000000000000000000000000000000000000
private def q307 : W := 0x7bc0405ef71000200000003fc421020000000000000003fbf8840007be422200bff0001fffc000000000001ff000000000000000000000fffe000001ff8000000
private def q308 : W := 0x7bc0405ef71000200480203fc421020108000089004023fbf8840007be422200bff0001fffc000000000001ff000000000000000000000fffe000001ff8000000
private def q309 : W := 0x7bc450fef7ffe2201042113fc631933f009f0f808bff03fbf8c6f887be633ff4bff0001ffffff8000000001ff0000007c007c3e000ffc0fffe003e01ff8003fc0
private def q310 : W := 0x7bc8615ef718443123ff003fffff820427e40227fc2203fbffff2007bffff320bff0001fffc0000000ffc01fffffe00001f80001ff0000ffffffc001fffffc000
private def q311 : W := 0x7bd0c25ef73088624108423fcc63265ffffff002008043ffffffffffbe462601bff0001fffc000000000001ff0000007fffffc00000000ffffffffffff8000000
private def q312 : W := 0x7bdc43def712ee230000003fee27b26000000000000003fbfedef6b7bf627274bfff81ffffc0ffc1c000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def q313 : W := 0x7bdefbdef7beef7b0000000020840000000000000000021044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q314 : W := 0x7bdffbc00082000007e0f83fefffbfe0000000000100010822084214000008403fffffe00000000000f83e1ffffffff8000000000000000000000000000000000
private def q315 : W := 0x7bdffbdef7feeffb0200800020840000000000040200821044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q316 : W := 0x7bffffc000820000037bdfbfffffffe0020840000104010822084214000008403fffffe00000000000fffffffffffff8000000000000000000000000000000000
private def q317 : W := 0x7bffffdef7ffffff02108400208400000410800422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q318 : W := 0x800000010000000008000040000000021000011000000004000000004000000000000000000000000000000000000000000000000000000000000000000000000
private def q319 : W := 0x8020000100001000080100c0100040021042211004010404010001004080000800000000000000000000000000000000000000000000000000000000000000000
private def q320 : W := 0x80210001004010800fe1f8c0100040031863319fc7f1f4040100010040800008000000000000000000f83e000000000000000001f0fc3c0000000000000000000
private def q321 : W := 0x803e080100043f08082108c03b0878821042211044111404076017c041b0809e400f8000000007c0000000000fc01e00000000000000000001f801f0007c00038
private def q322 : W := 0x8400000000000000fc842040000000084000040000000000000000000000000000000000000000003f00000000000000000000000000000000000000000000000
private def q323 : W := 0x8400000108000000ec84204000000000f900007910002004000000004000000000000000000000003f000000000000003e00001e0000000000000000000000000
private def q324 : W := 0x840000210800000080000000000000108000084000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q325 : W := 0x8400002108000000bc8420400000000000000ff910402000000000004000000000000000000000003f00000000000000000003fe0000000000000000000000000
private def q326 : W := 0x8400002108000000dc0020400000001bd8000dd800402004000000004000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def q327 : W := 0x8400002108000000f80400400000001ef1000f7010000004000000004000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def q328 : W := 0x8400002108000000fc8420400000001ff9000ff910402004000000004000000000000000000000003f00000000000007fe0003fe0000000000000000000000000
private def q329 : W := 0x8401002108400080ffe4f8400000001ff9211fffd3f0f004000000004000000000000000000000003ff83e0000000007fe0003fff0fc3c0000000000000000000
private def q330 : W := 0x8420040000000000f81f07c0100040084208440000040000000000000000000000000000000000003f07c1e000000000000000000000000000000000000000000
private def q331 : W := 0x8420040108001004e81d06c010004000f740e07034000c04010001004080000800000000000000003f07c1e0000000003ff83c1e0f00030000000000000000000
private def q332 : W := 0x842004210801100480100400000000108410884020080800000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q333 : W := 0x8420042108011004b81705c01000400000000f703c0f0c00000000004080000800000000000000003f07c1e000000000000003fe0f03c30000000000000000000
private def q334 : W := 0x8420042108011004d80007c00000401ad01aed50000d0c04000001004000000800000000000000003f0001e000000007fe07fffe0003c30000000000000000000
private def q335 : W := 0x8420042108011004f81f07c01000401ef7deef703c0f0c04010001004080000800000000000000003f07c1e000000007fffffffe0f03c30000000000000000000
private def q336 : W := 0x8420042108011004fc9f27c01000401fffdeeff93c4f2c04010001004080000800000000000000003f07c1e000000007fffffffe0f03c30000000000000000000
private def q337 : W := 0x8421040108401084effdfec010004001ff61f0fff7f0fc04010001004080000800000000000000003fffffe0000000003ff83c1ffffc3f0000000000000000000
private def q338 : W := 0x8421042108011084ffbfefc01000401efffeff7f7c0ffc04010001004080000800000000000000003fffffe000000007ffffffffff03ff0000000000000000000
private def q339 : W := 0x842104210841108482108400000000108410884422088800000000000000000000000000000000000000000000000000000000000000000000000000000000000
private def q340 : W := 0x8421042108411084bef7bdc01000400000000ffdff7fbc00000000004080000800000000000000003fffffe000000000000003ffffffff0000000000000000000
private def q341 : W := 0x8421042108411084dc00ffc00000401bd81bfdd803ddfc04000001004000000800000000000000003f003fe000000007fe07fffe00ffff0000000000000000000
private def q342 : W := 0x8421042108411084dfe0ffc00000401bd83bfddfc3fdfc04000001004000000800000000000000003ff83fe000000007fe07fffff0ffff0000000000000000000
private def q343 : W := 0x8421042108411084fb7fdfc01000401ef7ffff76ffbfdc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q344 : W := 0x8421042108411084fc1fffc01000401fffdffff83fdffc04010001004080000800000000000000003f07ffe000000007fffffffe0fffff0000000000000000000
private def q345 : W := 0x8421042108411084ffdff7c01000401fffffffffbfefec04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q346 : W := 0x8421042108411084ffffffc01000401ffffffffffffffc04010001004080000800000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q347 : W := 0x8421142308fd1084ffffffc01010411ffffffffffffffc2401000900c0810f8800000000003f00003fffffe000000007ffffffffffffff0000000000000003e00
private def q348 : W := 0x8421242108491094ffffffc011f8401ffffffffffffffc0401210100409f810800000000000000003fffffe0003e0007ffffffffffffff00000000000003e0000
private def q349 : W := 0x843c07a10803fe07f81f07c03a06f07ef7deef703c0f0c04075af7b041a0507c000f81e00000ffc1ff07c1e00fc1fe1ffffffffe0f03c30001fffffe007c1c1f8
private def q350 : W := 0x843d07a10843fe87ffffffc03a06f07ffffffffffffffc04075af7b041a0507c000f81e00000ffc1ffffffe00fc1fe1fffffffffffffff0001fffffe007c1c1f8
private def q351 : W := 0x843fbf8000820000ffffffc03bdefde842084400010400000208421000000840000fffe0000000003fffffe00ffffff8000000000000000000000000000000000
private def q352 : W := 0x843fbfa108efffdf821084002084001084108844220888000410842001084000000fffe0003fffffc000000000000000000000000000000000000000000000000
private def q353 : W := 0x87a107f90e43d087ffffffc39007c07fffffffffffffff84711ee1364480706801f001ff83c0f801ffffffe0f001e01ffffffffffffffff81e07fe0fe1801c1c0
private def q354 : W := 0x8822080110041108082108c4110848821042211044111404812001404890808a40000000000000000000000000000000000000000000000000000000000000000
private def q355 : W := 0x8c230c211845118cffffffc41108489ffffffffffffffc04812001404890808a40000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q356 : W := 0x8c40402319100020fc8420444020021ff9000ff91040202488000000ca02020080000000000000003f00000000000007fe0003fe0000000000000000000000000
private def q357 : W := 0x8c614423195110a4ffffffc45020421ffffffffffffffc2489000100ca82020880000000000000003fffffe000000007ffffffffffffff0000000000000000000
private def q358 : W := 0x8c63fc0000800000ffffffc451f84f884208440001040000000000000000080000007e00000000003fffffe0003e01e0000000000000000000000000000000000
private def q359 : W := 0x8c63fc2319fd11fc82108400008000108410884422088800000000000008000000007e00003f003e0000000000000000000000000000000000000000000000000
private def q360 : W := 0x948410ff28ffe200fcc631488210913ff99f0ff99bff23e50042f887d0211ff40000001f803ff8003f00000000000007fe07c3fe00ffc0f800003e01e00003fc0
private def q361 : W := 0x94a404e528033204980005c88000502000000d50000d0c00000000055000005c3fff81ffffc0ffc1ff0001fff0001e18000003fe0003c30000000001ff80001f8
private def q362 : W := 0x94a414ff28fff204f85f17c89210d13ff7dfeff0bfff0fe50142f987d0a11ffc0000001f803ff8003f07c1e000000007fffffffe0fffc3f800003e01e00003fc0
private def q363 : W := 0x94a504fd2843f284ffffffc89200d03fffffffffffffffc50142f18750a0107c0000001f8000f8003fffffe000000007fffffffffffffff800003e01e000001c0
private def q364 : W := 0xa50821294a084411ffff20513fff801fffe40ffffc62208617ff200265fff12000000000000000003fffc0000fffe007fff803ffff00000001ffc000007ffc000
private def q365 : W := 0xa52805014a001405a81504d1340540000000007034000c000000000065c060083fff81e07fc007c1ff07c1ffffc1fe180000001e0f000300000000001ffc1c038
private def q366 : W := 0xa52825294a095415fbff07d13fffc01ef7feef77fc2f0c8617ff210265fff12800000000000000003fffc1e00fffe007ffffffffff03c30001ffc000007ffc000
private def q367 : W := 0xa52905294a415485ffffffd13e07c01ffffffffffffffc8617de210265e0702800000000000000003fffffe00fc1e007ffffffffffffff0001ffc000007c1c000
private def q368 : W := 0xa52925294a495495ffffffd13fffc01ffffffffffffffc8617ff210265fff12800000000000000003fffffe00fffe007ffffffffffffff0001ffc000007ffc000
private def q369 : W := 0xb02c000560003600080100d83600500000000110040104000000000171e0001c3e0f80007c0007c00000001f0fc01e000000000000000000000000001e7c00038
private def q370 : W := 0xb580006d6a000000b80400598401000000000f701000000000000007744020003ff0001fffc000003f00001ff0000000000003fe0000000000000001ff8000000
private def q371 : W := 0xb5ad05ed6a437685bef7bdd9b605d02000000ffdff7fbc000000000775e0707c3fff81ffffc0ffc1ffffffffffc1fe18000003ffffffff0000000001fffc1c1f8
private def q372 : W := 0xb82e080570043708082108dc3708588000000110441114000000000179f0809e7e0f80007c0007c00000001f0fc01e000000000000000000000000001e7c00038
private def q373 : W := 0xbdc0406f7b100020bc84205dc421020000000ff91040200000000007fe422200bff0001fffc000003f00001ff0000000000003fe0000000000000001ff8000000
private def q374 : W := 0xbde1446f7b5110a4bef7bdddd421420000000ffdff7fbc0000000007fec22208bff0001fffc000003ffffffff0000000000003ffffffff0000000001ff8000000
private def q375 : W := 0xbdec45ef7b137625bc9725ddf625d22000000ff93c4f2c0000000007ffe2727cbfff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8
private def q376 : W := 0xc61082318c208842fd8c62620842245ffffffffb10c063fffffffff84004040100000000000000003f00000000000007fffffffe000000fffffffffe000000000
private def q377 : W := 0xc63006018c001806c80006e200006040d000e05000000c1c60000730400000083fff81e07fc007c1ff0001fff0001e183e003c1e00000307fe0001fe1f8000038
private def q378 : W := 0xc63086318c219846f91f47e21842645fffffff723c8f4ffffffffff84084040900000000000000003f07c1e000000007fffffffe0f03c3fffffffffe000000000
private def q379 : W := 0xc63186318c6198c6ffffffe21842645ffffffffffffffffffffffff84084040900000000000000003fffffe000000007fffffffffffffffffffffffe000000000
private def q380 : W := 0xd0340005a0003a00080000e800007002100221100001045d000017815000001c3e0f80007c0007c00000001f00001e000000000000000007e00001f01e0000038
private def q381 : W := 0xd6800075ac000000d800006a8000001ad0000d500000035d60000005500000003ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q382 : W := 0xd6b406c000020000d80007ea80007068400844000004010820004214000000403fff81e0000000003f0001fff0001e18000000000000000000000000000000000
private def q383 : W := 0xd6b406f5ac03ba0680000400000000108010884000080a1040008420000000003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def q384 : W := 0xd6b406f5ac03ba06d80007ea8000707ad01aed50000d0f5d6000d7b55000005c3fff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def q385 : W := 0xd6b416ffacfffa06d84217ea8210f17fd09fefd08bff0ffd6042ffb7d0211ffc3fff81ffffffffc1ff0001fff0001e1ffe07fffe00ffc3fffe003fffff8003ff8
private def q386 : W := 0xd6b486f5ac23ba46d90847ea8842747ffffffd52008d4ffffffffffd5004045d3fff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8
private def q387 : W := 0xd6b506f5ac43ba86dc00ffea8000707bd81bfdd803ddff5d6000d7b55000005c3fff81ffffc0ffc1ff003ffff0001e1ffe07fffe00fffffffe003fffff80001f8
private def q388 : W := 0xd6b506f5ac43ba86ffffffea9000707fffffffffffffff5d6100d7b55080005c3fff81ffffc0ffc1fffffffff0001e1ffffffffffffffffffe003fffff80001f8
private def q389 : W := 0xd8360805b0043b08082008ec01087882100221104011145d802017c15810809e7e0f80007c0007c00000001f00001e000000000000000007e00001f01e0000038
private def q390 : W := 0xdec04077bd100020dc80206ec020021bd8000dd90040237de8000005da020200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q391 : W := 0xdee14477bd5110a4dc00ffeec000421bd81bfdd803ddff7de8000105da000208bff0001fffc000003f003ffff0000007fe07fffe00fffffffe000001ff8000000
private def q392 : W := 0xdef446f7bd13ba26dc0027eec000727bd81aedd8004d2f7de800d7b5da00025cbfff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def q393 : W := 0xdef7fec000820000dfe0ffeec1f87fe8400844000104010820004214000008403fffffe0000000003ff83ffff03e1ff8000000000000000000000000000000000
private def q394 : W := 0xdef7fef7bdffbbfe82008400008000108010884402088a1040008420000800003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q395 : W := 0xe0380001c0001c00080100f03c006000104020100400041e0780070061c000083e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q396 : W := 0xe7000001ce000000e804007304010000f10000701000001e70840000644020003ff000007fc000003f00001ff00000003e00001e00000007fe0000001f8000000
private def q397 : W := 0xe738070000000000e81d06f33c076040420040000000000822080210000000003fff81e0000000003f07c1ffffc1fe18000000000000000000000000000000000
private def q398 : W := 0xe7380701ce001c078010040020040000840080402000081044100420010040003fff81e07fc007c1c000000000000000000000000000000000000000000000000
private def q399 : W := 0xe7380701ce001c07e81d06f33c076040f740e07034000c1e779c073065c060083fff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def q400 : W := 0xe7382709ce085c17ebff06f33fffe044f7e4e277fc220c9e77ff273265fff1283fff81e07fc007c1ffffc1fffffffe183ff83c1fff000307ffffc1fe1ffffc038
private def q401 : W := 0xe7388711ce209c47e91d46f33c47645ffffff07234804ffffffffff865c464093fff81e07fc007c1ff07c1ffffc1fe1ffffffc1e0f0003fffffffffe1ffc1c038
private def q402 : W := 0xe7390701ce001c87efbdeef33c076040ff60f07f7400fc1e779c073065c060083fff81e07fc007c1ffffffffffc1fe183ff83c1fff003f07ffffc1fe1ffc1c038
private def q403 : W := 0xe7390721ce411c87fffffff33c07605ffffffffffffffc1e779c073065c060083fff81e07fc007c1ffffffffffc1fe1fffffffffffffff07ffffc1fe1ffc1c038
private def q404 : W := 0xe83a0801d0041d08082108f43d086880104020104410141e87a0074069d0808a7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q405 : W := 0xef404001df000020ec84207744210200f90000791000201ef88400006e422000bff000007fc000003f00001ff00000003e00001e00000007fe0000001f8000000
private def q406 : W := 0xef404003df100020ec84207744210201f90000f91040203ef8840000ee422200bff000007fc000003f00001ff00000003e00001e00000007fe0000001f8000000
private def q407 : W := 0xef614401df0010a4efbdeef754214200ff60f07f7400fc1ef98401006ec22008bff000007fc000003ffffffff00000003ff83c1fff003f07fe0000001f8000000
private def q408 : W := 0xef784701df001c27ec9d26f77c276240ff40e07934002c1eff9c07306fc26008bfff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def q409 : W := 0xef7bff0000800000effdfef77dff6fc0420040000100000822080210000008003fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q410 : W := 0xef7bff03dffc1dff8210840020840000840080442200881044100420010840003fffffe07fff07ffc000000000000000000000000000000000000000000000000
private def q411 : W := 0xf0000005e00000000800007804000002100001100000005f00800001704000003e0000007c0000000000001f000000000000000000000007e00000001e0000000
private def q412 : W := 0xf03c000000000000080100f83e007000000000000000000802000200000000003e0f8000000000000000001f0fc01e00000000000000000000000000000000000
private def q413 : W := 0xf03c0005e0003e000000000020000000000000000000001004000400010000003e0f80007c0007c00000000000000000000000000000000000000000000000000
private def q414 : W := 0xf03c0005e0003e00080100f83e007002104221100401045f07c0178171e0001c3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q415 : W := 0xf03c0005e0003e00082108f83e007002104221104411145f07c0178171e0001c3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q416 : W := 0xf03e0805e0043f08082108f83f087882104221104411145f07e017c171f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q417 : W := 0xf0bc10ffe0fffe00184311f8be10f13f10df2f908fff07ff07c2ff87f1e11ffc3e0f801ffc3fffc00000001f0fc01e07c007c3e000ffc0ffe1f83ff1fe7c03ff8
private def q418 : W := 0xf13c210de2087e112bff00f93ffff00637e62337fc2304df17ff378375fff13c3e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038
private def q419 : W := 0xf23c8215e420be42490942fa3e42745ffffff112048147fffffffff971e4041d3e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038
private def q420 : W := 0xf43d0425e8413e84fffffff83e00701ffffffffffffffc5f07c0178171e0001c3e0f80007c0007c03fffffff0fc01e07ffffffffffffff07e1f801f01e7c00038
private def q421 : W := 0xf780004000000000f804007b84010008400004000000010820000004000000003ff00000000000003f00001ff0000000000000000000000000000000000000000
private def q422 : W := 0xf780007dee0000008000000000000010800008400000021040000000000000003ff0001fffc000000000000000000000000000000000000000000000000000000
private def q423 : W := 0xf780007dee000000f804007b8401001ef1000f70100003df70840007744020003ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q424 : W := 0xf780007dee000000fc84207b8401001ff9000ff9104023df70840007744020003ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q425 : W := 0xf78410ffeeffe200f846117b8611913ff19f0ff09bff03ff70c6f887f4613ff43ff0001ffffff8003f00001ff0000007fe07c3fe00ffc0fffe003e01ff8003fc0
private def q426 : W := 0xf788217dee084411fbff007bbfff801ef7e40f77fc2203df77ff200775fff1203ff0001fffc000003fffc01fffffe007fff803ffff0000ffffffc001fffffc000
private def q427 : W := 0xf790827dee208842f90c427b8c43245fffffff72108043ffffffffff744424013ff0001fffc000003f00001ff0000007fffffffe000000ffffffffffff8000000
private def q428 : W := 0xf7a0047dee011004f81f07fb9401401ef7deef703c0f0fdf7184010774c020083ff0001fffc000003f07c1fff0000007fffffffe0f03c3fffe000001ff8000000
private def q429 : W := 0xf7a1047dee411084fffffffb9401401fffffffffffffffdf7184010774c020083ff0001fffc000003ffffffff0000007fffffffffffffffffe000001ff8000000
private def q430 : W := 0xf7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q431 : W := 0xf7bc07fdee03fe07fc9f27fbbe07f07fffdeeff93c4f2fdf77def7b775e0707c3fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q432 : W := 0xf7bc17ffeefffe07f85f17fbbe17f17ff7dfeff0bfff0fff77deffb7f5e17ffc3fff81ffffffffc1ff07c1ffffc1fe1ffffffffe0fffc3fffffffffffffc1fff8
private def q433 : W := 0xf7bc27fdee0bfe17fbff07fbbffff07ef7feef77fc2f0fdf77fff7b775fff17c3fff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8
private def q434 : W := 0xf7bd07c000020000fffffffbbe07f068420844000104010822084214000000403fff81e0000000003fffffffffc1fe18000000000000000000000000000000000
private def q435 : W := 0xf7bd07fdee43fe8782108400200400108410884422088a1044108420010040003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def q436 : W := 0xf7bd07fdee43fe87fffffffbbe07f07fffffffffffffffdf77def7b775e0707c3fff81ffffc0ffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def q437 : W := 0xf7bd17ffeefffe87fffffffbbe17f17fffffffffffffffff77deffb7f5e17ffc3fff81ffffffffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1fff8
private def q438 : W := 0xf7bd27fdee4bfe97fffffffbbffff07fffffffffffffffdf77fff7b775fff17c3fff81ffffc0ffc1fffffffffffffe1ffffffffffffffffffffffffffffffc1f8
private def q439 : W := 0xf7bd87fdee63fec7fffffffbbe47f47fffffffffffffffffffffffff75e4747d3fff81ffffc0ffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def q440 : W := 0xf7bfbfc000820000fb7fdffbbfdffde8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q441 : W := 0xf7bfbffdeeefffdf82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q442 : W := 0xf7c0407fef100020fc84207bc421021ff9000ff9104023ff78840007f6422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q443 : W := 0xf7fdf7c000820000ffdff7fbfef7f768420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q444 : W := 0xf7fdf7ffeffbfef782108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q445 : W := 0xf8020805f00401080820087c05080882100001104010105f80a00041785080827e0000007c0000000000001f000000000000000000000007e00000001e0000000
private def q446 : W := 0xf8200005f0001000082108fc14004002104221104411145f8180010178c000083e0000007c0000000000001f000000000000000000000007e00000001e0000000
private def q447 : W := 0xf83c0005f0003e00080100fc3e007002104221100401045f87c0178179e0001c3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q448 : W := 0xf83e0805f0003f08082108fc3f087882104221104401145f87e017c179f0801e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q449 : W := 0xf83e0805f0043f08080100fc3f087882104221100401045f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q450 : W := 0xf83e0805f0043f08080108fc3e007882104221100411145f87c017c179e0009e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q451 : W := 0xf83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e7e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q452 : W := 0xf83e0f85f007ff0f083b0ffc3f0ef8e216dee1106c1f1c5f87faf7f179f0d0fe7e0f81e07c00ffc1c007c1ff0fc1fe1801fffc000f03c307e1fffffe1e7c1c1f8
private def q453 : W := 0xf83e1807f0fc3f08086118fc3f18798310432190c7f1147f87e01fc1f9f18f9e7e0f80007c3f07c00000001f0fc01e000000000000fc0007e1f801f01e7c03e38
private def q454 : W := 0xf83e2805f00c3f180be108fc3ff8788210622117c431145f87e117c179ff819e7e0f80007c0007c000f8001f0ffe1e0000000001f0000007e1f801f01e7fe0038
private def q455 : W := 0xf83f0805f0443f880fe1f8fc3f0878831863319fc7f1f45f87e017c179f0809e7e0f80007c0007c000f83e1f0fc01e0000000001f0fc3c07e1f801f01e7c00038
private def q456 : W := 0xf8404007f11000200c80207c44200203180001990040207f88800001fa420200be0000007c0000000000001f000000000000000000000007e00000001e0000000
private def q457 : W := 0xf87e4807f1143f280ca128fc7f287a83184221994451347f8fe017c1fbf2829efe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038
private def q458 : W := 0xf87ff800008000000fe1f8fc7ff87f80000000000100000802000200000008003e0ffe000000000000f83e1f0ffe1fe0000000000000000000000000000000000
private def q459 : W := 0xf87ff807f1fc3ff80200800020800000000000040200801004000400010800003e0ffe007c3f07fe0000000000000000000000000000000000000000000000000
private def q460 : W := 0xf8be08fdf007ff08182309fcbf08f8be10de2f104c1f17df87e2f7c779f090fe7e0f801ffc00ffc00000001f0fc01e07c007c3e00003c0ffe1f83ff1fe7c001f8
private def q461 : W := 0xf8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe7e0f801ffc3fffc00000001f0fc01e07c007c3e000ffc0ffe1f83ff1fe7c03ff8
private def q462 : W := 0xf93e090df2047f09283f08fd3f0ff88637c623307c1314df97fe37c37df0f0be7e0f80007c0007c00007c01f0fc1fe0001f800000f000007e1ffc1f01e7c1c038
private def q463 : W := 0xf93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be7e0f80007c0007c000ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038
private def q464 : W := 0xfa3e8a15f424bf4a49294afe3f4a7cdffffff112449157fffffffff979f4849f7e0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038
private def q465 : W := 0xfbbe0bddf606ff0b082108ffbf0ff8e210422110441117dff7fef7f77df0f0fe7fff81ffffc0ffc1c000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def q466 : W := 0xfbfe485ff7143f28082108ffff297a8210422110441117ffffe417c7fff2a29effff801fffc007c00000001fffc01e0000000000000000fffff801f1fffc00038
private def q467 : W := 0xfc3e0825f8043f08fca528fc3f08789ff9422ff95451345f87e017c179f0809e7e0f80007c0007c03f00001f0fc01e07fe0003fe00000007e1f801f01e7c00038
private def q468 : W := 0xfc3e0c25f8053f0cf83f0ffc3f08789ef7deef707c1f1c5f87e017c179f0809e7e0f80007c0007c03f07c1ff0fc01e07fffffffe0f03c307e1f801f01e7c00038
private def q469 : W := 0xfc3f0c25f8453f8cfffffffc3f08789ffffffffffffffc5f87e017c179f0809e7e0f80007c0007c03fffffff0fc01e07ffffffffffffff07e1f801f01e7c00038
private def q470 : W := 0xfebe0ef5fc07bf0ed8210ffebf0878fad05aed50441d1f5fe7e0d7f579f080de7fff81ffffc0ffc1ff0001ffffc01e1ffe07fffe0003c3fffff83ffffffc001f8
private def q471 : W := 0xff3e0f05fe043f0fe83d0eff3f0f78c2f742e17074111c5ff7fc17f17df0e09e7fff81e07fc007c1ff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def q472 : W := 0xffbe087dfe043f08f82508ffbf09789ef1422f70541117dff7e417c77df0a09e7fff801fffc007c03f00001fffc01e07fe0003fe000000fffff801f1fffc00038
private def q473 : W := 0xffbe0ffdfe07ff0ff83f0fffbf0ff8fef7deef707c1f1fdff7fef7f77df0f0fe7fff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q474 : W := 0xffbf0ffdfe47ff8fffffffffbf0ff8ffffffffffffffffdff7fef7f77df0f0fe7fff81ffffc0ffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def q475 : W := 0xffc0407dff000020fc84207fc421021ef9000f79100023dff88400077e422000bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q476 : W := 0xffc0407fff100020f804007fc421021ef1000f70100003fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q477 : W := 0xffc0407fff100020fc04207fc401021ff9000ff8104023fff8840007fe402200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q478 : W := 0xffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q479 : W := 0xffc047ffff13c027fc9e277fc427827fff9ccff9384e2bfff89ee037fe427260bff001ffffc0f801ff07c1fff001e01ffffffffe0f03c3fffe07fe0fff801c1c0
private def q480 : W := 0xffc0507ffffc0020fcc4307fc431031ff9010ff993f023fff8840807fe432f80bff0001fffff00003f00001ff0000007fe0003fe00fc00fffe000001ff8003e00
private def q481 : W := 0xffc0607fff180030ffe4207fc5f9021ff9200fffd06023fff8a50007fe5fa300bff0001fffc000003ff8001ff03e0007fe0003fff00000fffe000001ff83e0000
private def q482 : W := 0xffc1407fff5000a0ffe4f87fc421021ff9211fffd3f0f3fff8840007fe422200bff0001fffc000003ff83e1ff0000007fe0003fff0fc3cfffe000001ff8000000
private def q483 : W := 0xffc2487fff140128fca4287fc5290a9ff9000ff9505033fff8a40047fe52a282fff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000
private def q484 : W := 0xffc3f84000800000ffe4f87fc5f90f88400004000100010820000004000008003ff07e00000000003ff83e1ff03e01e0000000000000000000000000000000000
private def q485 : W := 0xffc3f87ffffc01f88200800000800010800008440200821040000000000800003ff07e1fffff003e0000000000000000000000000000000000000000000000000
private def q486 : W := 0xffc440ffff13e220fc86217fc621923ff99e0ff9184f23fff8c6f087fe623274bff0001fffc0f8003f00001ff0000007fe07c3fe0003c0fffe003e01ff80001c0
private def q487 : W := 0xffc450ffffffe220fcc6317fc631933ff99f0ff99bff23fff8c6f887fe633ff4bff0001ffffff8003f00001ff0000007fe07c3fe00ffc0fffe003e01ff8003fc0
private def q488 : W := 0xffc8417fff104421fc9f207ffe27821fffc40ff93c4223ffffde2007ffe27220bff0001fffc000003f07c01fffc1e007fff803fe0f0000ffffffc001fffc1c000
private def q489 : W := 0xffc8617fff184431ffff207fffff821fffe40ffffc6223ffffff2007fffff320bff0001fffc000003fffc01fffffe007fff803ffff0000ffffffc001fffffc000
private def q490 : W := 0xffd0c27fff308862fd8c627fcc63265ffffffffb10c063fffffffffffe462601bff0001fffc000003f00001ff0000007fffffffe000000ffffffffffff8000000
private def q491 : W := 0xffdc43ffff12ee23fc84207fee27b27ff9000ff9104023fffedef6b7ff627274bfff81ffffc0ffc1ff00001fffc1fe1ffe0003fe000000fffffffffffffc1c1f8
private def q492 : W := 0xffe0447fff111024fc9f27ffd421421fffdeeff93c4f2ffff9840107fec22208bff0001fffc000003f07c1fff0000007fffffffe0f03c3fffe000001ff8000000
private def q493 : W := 0xffe1444000000000ffffffffd4214208420844000104010820000004000000003ff00000000000003ffffffff0000000000000000000000000000000000000000
private def q494 : W := 0xffe1447fff5110a482108400000000108410884422088a1040000000000000003ff0001fffc000000000000000000000000000000000000000000000000000000
private def q495 : W := 0xffe1447fff5110a4ffffffffd421421ffffffffffffffffff9840107fec22208bff0001fffc000003ffffffff0000007fffffffffffffffffe000001ff8000000
private def q496 : W := 0xffe554fffffff2a4ffffffffd631d33ffffffffffffffffff9c6f987fee33ffcbff0001ffffff8003ffffffff0000007fffffffffffffffffe003e01ff8003fc0
private def q497 : W := 0xffe9657fff5954b5ffffffffffffc21fffffffffffffffffffff2107fffff328bff0001fffc000003fffffffffffe007ffffffffffffffffffffc001fffffc000
private def q498 : W := 0xfff1c67fff7198e6ffffffffdc63665ffffffffffffffffffffffffffec62609bff0001fffc000003ffffffff0000007ffffffffffffffffffffffffff8000000
private def q499 : W := 0xfff446ffff13ba26fc8427ffc421727ff91aeff9104d2ffff884d7b7fe42225cbfff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def q500 : W := 0xfff8477fff101c27fc9d26fffc27625fff40eff934402fffff9c0737ffc26208bfff81ffffc007c1ff07c1ffffc1fe1ffff83ffe0f0003ffffffc1fffffc1c038
private def q501 : W := 0xfffc407fff103e20fc8520fffe21721ff9422ff9144127ffffc41787ffe2221cbfff801fffc007c03f00001fffc01e07fe0003fe000000fffff801f1fffc00038
private def q502 : W := 0xfffc47c000020000fc9f27fffe27f268420844000004010822084214000000403fff81e0000000003f07c1ffffc1fe18000000000000000000000000000000000
private def q503 : W := 0xfffc47ffff13fe2780100400200400108410884020080a1044108420010040003fff81ffffc0ffc1c000000000000000000000000000000000000000000000000
private def q504 : W := 0xfffc47ffff13fe27f81f07fffe27f27ef7deef703c0f0fffffdef7b7ffe2727cbfff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q505 : W := 0xfffc47ffff13fe27fc9f27fffe27f27fffdeeff93c4f2fffffdef7b7ffe2727cbfff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q506 : W := 0xfffc57fffffffe27fcdf37fffe37f37fffdfeff9bfff2fffffdeffb7ffe37ffcbfff81ffffffffc1ff07c1ffffc1fe1ffffffffe0fffc3fffffffffffffc1fff8
private def q507 : W := 0xfffc67ffff1bfe37ffff27fffffff27ffffeeffffc6f2ffffffff7b7fffff37cbfff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8
private def q508 : W := 0xfffcc7ffff33fe67fd9f67fffe67f67ffffffffb3ccf6fffffffffffffe6767dbfff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q509 : W := 0xfffd47ffff53fea7fffffffffe27f27fffffffffffffffffffdef7b7ffe2727cbfff81ffffc0ffc1ffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def q510 : W := 0xfffe487fff143f28fca528ffff297a9ff9422ff9545137ffffe417c7fff2a29effff801fffc007c03f00001fffc01e07fe0003fe000000fffff801f1fffc00038
private def q511 : W := 0xfffe4fffff17ff2ffcbf2fffff2ffaffffdeeff97c5f3ffffffef7f7fff2f2feffff81ffffc0ffc1ff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q512 : W := 0xfffeffc000820000f81f07ffffffffe8420844000004010822084214000008403fffffe0000000003f07c1fffffffff8000000000000000000000000000000000
private def q513 : W := 0xfffeffffffbfff7f80100400208400108410884020080a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q514 : W := 0xffff4c7fff553facffffffffff297a9fffffffffffffffffffe417c7fff2a29effff801fffc007c03fffffffffc01e07fffffffffffffffffff801f1fffc00038
private def q515 : W := 0xffffdfc000820000fc1ffffffe07ffe8420844000104010822084214000008403fffffe0000000003f07ffffffc1fff8000000000000000000000000000000000
private def q516 : W := 0xffffdffffff7ffef80108400200400108410884022088a1044108420010040003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q517 : W := 0xffffefc000020000ffbfefffffeffee8420844000004010822084214000000403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q518 : W := 0xffffeffdff03ffff82108400208400108410884420088a1044108420010840003fffffffffc0ffffc000000000000000000000000000000000000000000000000
private def q519 : W := 0xffffffc000820000ffffffffffffffe8420844000104010822084214000008403fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q520 : W := 0xffffffc00083fe07ffffffffffffffe846dee4002d0f0d08275af7b401a0587c3fffffe00000ffc1fffffffffffffff801fffc000f03c30001fffffe007c1c1f8
private def q521 : W := 0xffffffc0008a0010ffffffffffffffe842284407c124010822294214001f89403fffffe0000000003ffffffffffffff800000001f0000000000000000003e0000
private def q522 : W := 0xffffffc000c20080ffffffffffffffe94a29548fc3f4f10822084214000008403fffffe0000000003ffffffffffffff800000001f0fc3c0000000000000000000
private def q523 : W := 0xffffffc010860108ffffffffffffffe84208440041141108a2284254081088c27fffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q524 : W := 0xffffffc1ce821c07ffffffffffffffe8f748e47035040d1e779c473465c068483fffffe07fc007c1fffffffffffffff83ff83c1e0f000307ffffc1fe1ffc1c038
private def q525 : W := 0xffffffc200fe0000ffffffffffffffe94209448083f4012822084a1480010fc03fffffe0003f00003ffffffffffffff80000000000fc000000000000000003e00
private def q526 : W := 0xffffffc211920020ffffffffffffffe94a08448901442128aa0842148a020a40bfffffe0000000003ffffffffffffff8000000000000000000000000000000000
private def q527 : W := 0xffffffc5e0823e00ffffffffffffffea524a65100505055f27c8579571e0085c3fffffe07c0007c03ffffffffffffff80000000000000007e1f801f01e7c00038
private def q528 : W := 0xffffffc842824401ffffffffffffffec67cc46203d06018a37de621625e078603fffffe0000000003ffffffffffffff801f800000f00000001ffc000007c1c000
private def q529 : W := 0xffffffdce682ee03ffffffffffffffe842084400010403db76def6b7356078743fffffffffc0ffc1fffffffffffffff800000000000000fffffffffffffc1c1f8
private def q530 : W := 0xffffffdef7920020ffffffffffffffe842084400010403fbfa8c4217be422a40bfffffffffc000003ffffffffffffff800000000000000fffe000001ff8000000
private def q531 : W := 0xffffffe108820000fffffffffffffffffb084ff91144210c22084214400008403fffffe0000000003ffffffffffffffffe0003fe0000000000000000000000000
private def q532 : W := 0xffffffe108831004fffffffffffffffef7deef703d0f0d0c23084314408008483fffffe0000000003ffffffffffffffffffffffe0f03c30000000000000000000
private def q533 : W := 0xfffffff5ac83ba06fffffffffffffffad21aed50010d0f5d6208d7b55000085c3fffffffffc0ffc1fffffffffffffffffe07fffe0003c3fffe003fffff80001f8
private def q534 : W := 0xfffffff80e83c007fffffffffffffffce79cce60390e0b88721ee236040078603fffffff83c0f801fffffffffffffffffffffffe0f03c3f81e07fe0fe1801c1c0
private def q535 : W := 0xfffffffc2083e200fffffffffffffffe429e4f00090f03c9224af297102018743fffffff8000f8003fffffffffffffffc007c3e00003c0f800003e01e000001c0
private def q536 : W := 0xfffffffdee820000fffffffffffffffef3084f70110403df728c4217744028403fffffffffc000003ffffffffffffffffe0003fe000000fffe000001ff8000000
private def q537 : W := 0xfffffffdee83fe07fffffffffffffffef7deef703d0f0fdf77def7b775e0787c3fffffffffc0ffc1fffffffffffffffffffffffe0f03c3fffffffffffffc1c1f8
private def q538 : W := 0xfffffffdeec3fe87ffffffffffffffffffffffffffffffdf77def7b775e0787c3fffffffffc0ffc1fffffffffffffffffffffffffffffffffffffffffffc1c1f8
private def q539 : W := 0xffffffffff93fe27ffffffffffffffffffdeeff93d4f2fffffdef7b7ffe27a7cbfffffffffc0ffc1fffffffffffffffffffffffe0f03c3fffffffffffffc1c1f8
private def q540 : W := 0xffffffffffd310a4fffffffffffffffffffffffffffffffffb8c4317fec22a48bfffffffffc000003ffffffffffffffffffffffffffffffffe000001ff8000000
private def q541 : W := 0xffffffffffffffff82108400208400108410884422088a1044108420010840003fffffffffffffffc000000000000000000000000000000000000000000000000
private def q542 : W := 0xffffffffffffffff8210843bae87b0708410884422088bdb76def6b7356870743fffffffffffffffc000001fffc1fe1800000000000000fffffffffffffc1c1f8
private def q543 : W := 0xffffffffffffffff8210843fe4a502108410884422088bfbfc948427bf4a6200bfffffffffffffffc000001ff000000000000000000000fffe000001ff8000000
private def q544 : W := 0xffffffffffffffff821b87803a86f07086dee8442e0f8e10475af7b001a8507c3fffffffffffffffc007c1e00fc1fe1801fffc000f03c30001fffffe007c1c1f8
private def q545 : W := 0xffffffffffffffff82308c04218c08908410884462189a10c43084600918c0827fffffffffffffffc000000000000000000000000000000000000000000000000
private def q546 : W := 0xffffffffffffffff8250940020940111841188c4a3f88a3044108c2081094f803fffffffffffffffc0000000000000000000000000fc000000000000000003e00
private def q547 : W := 0xffffffffffffffff83f0840021fc001084308847e2288a1044318420011fc1003fffffffffffffffc0f80000003e000000000001f0000000000000000003e0000
private def q548 : W := 0xffffffffffffffff8690a40460a402118c1088cd2248aa30cc1084208b0a4200bfffffffffffffffc000000000000000000000000000000000000000000000000
private def q549 : W := 0xffffffffffffffff87f0fc00208400118c3198cfe3f8fa1044108420010840003fffffffffffffffc0f83e000000000000000001f0fc3c0000000000000000000
private def q550 : W := 0xffffffffffffffff8a1184f83e8470129452a95426098e5f47d097a171e8401c3fffffffffffffffc000001f0fc01e000000000000000007e1f801f01e7c00038
private def q551 : W := 0xffffffffffffffff92128508a284903e849e8f442a0f8bd14452f4a7112850743fffffffffffffffc000000000000007c007c3e00003c0f800003e01e000001c0
private def q552 : W := 0xffffffffffffffffa21f84113e878014a7d48a643e0a8a9257dea42225e870203fffffffffffffffc007c0000fc1e00001f800000f00000001ffc000007c1c000
private def q553 : W := 0xffffffffffffffffda1087eaa084707ad41aed54220d8f5d6410d7b55108405c3fffffffffffffffff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8
private def q554 : W := 0xffffffffffffffffea1d86f33c876050f750e87436088e1e779c873065c860083fffffffffffffffff07c1ffffc1fe183ff83c1e0f000307ffffc1fe1ffc1c038
private def q555 : W := 0xfffffffffffffffff21e8703a087807ce79cce643a0e8b90741ee436050870603fffffffffffffffff07c1e0f001e01ffffffffe0f03c3f81e07fe0fe1801c1c0
private def q556 : W := 0xfffffffffffffffffa14847ba485001ef5108f7432088bdf74948427754860003fffffffffffffffff00001ff0000007fe0003fe000000fffe000001ff8000000
private def q557 : W := 0xfffffffffffffffffa1f87c03084401ef7deef743e0f8e1445108520418840083fffffffffffffffff07c1e000000007fffffffe0f03c30000000000000000000
private def q558 : W := 0xfffffffffffffffffa1f87fbbe87f07ef7deef743e0f8fdf77def7b775e8707c3fffffffffffffffff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q559 : W := 0xfffffffffffffffffe94a4402084001ffd108ffd3248aa1444108420410840003fffffffffffffffff00000000000007fe0003fe0000000000000000000000000
private def q560 : W := 0xfffffffffffffffffe94a47fe4a5021ffd108ffd3248abfffc948427ff4a6200bfffffffffffffffff00001ff0000007fe0003fe000000fffe000001ff8000000
private def q561 : W := 0xfffffffffffffffffe9fa7fffea7f27fffdeeffd3e4fafffffdef7b7ffea727cbfffffffffffffffff07c1ffffc1fe1ffffffffe0f03c3fffffffffffffc1c1f8
private def q562 : W := 0xfffffffffffffffffffffffbbe87f07fffffffffffffffdf77def7b775e8707c3fffffffffffffffffffffffffc1fe1ffffffffffffffffffffffffffffc1c1f8
private def q563 : W := 0xfffffffffffffffffffffffff4a5421ffffffffffffffffffd948527ffca6208bffffffffffffffffffffffff0000007fffffffffffffffffe000001ff8000000
private def sk0 : List W := [q0,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k0 : optimized 9 0 sk0 = false := certified_fast (by decide +kernel)
private def sk1 : List W := [q0,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k1 : optimized 9 0 sk1 = false := certified_fast (by decide +kernel)
private def sk2 : List W := [q0,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k2 : optimized 9 0 sk2 = false := certified_fast (by decide +kernel)
private def sk3 : List W := [q0,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k3 : optimized 9 0 sk3 = false := certified_fast (by decide +kernel)
private def sk4 : List W := [q0,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k4 : optimized 9 0 sk4 = false := certified_fast (by decide +kernel)
private def sk5 : List W := [q0,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k5 : optimized 9 0 sk5 = false := certified_fast (by decide +kernel)
private def sk6 : List W := [q1,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k6 : optimized 9 0 sk6 = false := certified_fast (by decide +kernel)
private def sk7 : List W := [q2,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k7 : optimized 9 0 sk7 = false := certified_fast (by decide +kernel)
private def sk8 : List W := [q3,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k8 : optimized 9 0 sk8 = false := certified_fast (by decide +kernel)
private def sk9 : List W := [q4,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k9 : optimized 9 0 sk9 = false := certified_fast (by decide +kernel)
private def sk10 : List W := [q5,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k10 : optimized 9 0 sk10 = false := certified_fast (by decide +kernel)
private def sk11 : List W := [q6,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k11 : optimized 9 0 sk11 = false := certified_fast (by decide +kernel)
private def sk12 : List W := [q7,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k12 : optimized 9 0 sk12 = false := certified_fast (by decide +kernel)
private def sk13 : List W := [q7,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k13 : optimized 9 0 sk13 = false := certified_fast (by decide +kernel)
private def sk14 : List W := [q8,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k14 : optimized 9 0 sk14 = false := certified_fast (by decide +kernel)
private def sk15 : List W := [q8,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k15 : optimized 9 0 sk15 = false := certified_fast (by decide +kernel)
private def sk16 : List W := [q9,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k16 : optimized 9 0 sk16 = false := certified_fast (by decide +kernel)
private def sk17 : List W := [q10,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k17 : optimized 9 0 sk17 = false := certified_fast (by decide +kernel)
private def sk18 : List W := [q11,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k18 : optimized 9 0 sk18 = false := certified_fast (by decide +kernel)
private def sk19 : List W := [q11,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k19 : optimized 9 0 sk19 = false := certified_fast (by decide +kernel)
private def sk20 : List W := [q12,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k20 : optimized 9 0 sk20 = false := certified_fast (by decide +kernel)
private def sk21 : List W := [q13,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k21 : optimized 9 0 sk21 = false := certified_fast (by decide +kernel)
private def sk22 : List W := [q14,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k22 : optimized 9 0 sk22 = false := certified_fast (by decide +kernel)
private def sk23 : List W := [q15,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k23 : optimized 9 0 sk23 = false := certified_fast (by decide +kernel)
private def sk24 : List W := [q15,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k24 : optimized 9 0 sk24 = false := certified_fast (by decide +kernel)
private def sk25 : List W := [q16,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k25 : optimized 9 0 sk25 = false := certified_fast (by decide +kernel)
private def sk26 : List W := [q16,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k26 : optimized 9 0 sk26 = false := certified_fast (by decide +kernel)
private def sk27 : List W := [q16,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k27 : optimized 9 0 sk27 = false := certified_fast (by decide +kernel)
private def sk28 : List W := [q17,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k28 : optimized 9 0 sk28 = false := certified_fast (by decide +kernel)
private def sk29 : List W := [q18,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k29 : optimized 9 0 sk29 = false := certified_fast (by decide +kernel)
private def sk30 : List W := [q19,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k30 : optimized 9 0 sk30 = false := certified_fast (by decide +kernel)
private def sk31 : List W := [q20,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k31 : optimized 9 0 sk31 = false := certified_fast (by decide +kernel)
private def sk32 : List W := [q21,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k32 : optimized 9 0 sk32 = false := certified_fast (by decide +kernel)
private def sk33 : List W := [q22,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k33 : optimized 9 0 sk33 = false := certified_fast (by decide +kernel)
private def sk34 : List W := [q22,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k34 : optimized 9 0 sk34 = false := certified_fast (by decide +kernel)
private def sk35 : List W := [q23,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k35 : optimized 9 0 sk35 = false := certified_fast (by decide +kernel)
private def sk36 : List W := [q24,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k36 : optimized 9 0 sk36 = false := certified_fast (by decide +kernel)
private def sk37 : List W := [q25,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k37 : optimized 9 0 sk37 = false := certified_fast (by decide +kernel)
private def sk38 : List W := [q26,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k38 : optimized 9 0 sk38 = false := certified_fast (by decide +kernel)
private def sk39 : List W := [q27,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k39 : optimized 9 0 sk39 = false := certified_fast (by decide +kernel)
private def sk40 : List W := [q28,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k40 : optimized 9 0 sk40 = false := certified_fast (by decide +kernel)
private def sk41 : List W := [q29,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k41 : optimized 9 0 sk41 = false := certified_fast (by decide +kernel)
private def sk42 : List W := [q30,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k42 : optimized 9 0 sk42 = false := certified_fast (by decide +kernel)
private def sk43 : List W := [q31,q541,q297,q451,q208,q242,q478,q277,q346,q519]
private theorem k43 : optimized 9 0 sk43 = false := certified_fast (by decide +kernel)
private def sk44 : List W := [q31,q541,q384,q451,q208,q242,q478,q277,q346,q519]
private theorem k44 : optimized 9 0 sk44 = false := certified_fast (by decide +kernel)
private def sk45 : List W := [q31,q541,q436,q451,q208,q242,q478,q277,q346,q519]
private theorem k45 : optimized 9 0 sk45 = false := certified_fast (by decide +kernel)
private def sk46 : List W := [q32,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k46 : optimized 9 0 sk46 = false := certified_fast (by decide +kernel)
private def sk47 : List W := [q33,q541,q177,q430,q451,q208,q242,q277,q346,q519]
private theorem k47 : optimized 9 0 sk47 = false := certified_fast (by decide +kernel)
private def sk48 : List W := [q33,q541,q307,q430,q451,q208,q242,q277,q346,q519]
private theorem k48 : optimized 9 0 sk48 = false := certified_fast (by decide +kernel)
private def sk49 : List W := [q33,q541,q495,q430,q451,q208,q242,q277,q346,q519]
private theorem k49 : optimized 9 0 sk49 = false := certified_fast (by decide +kernel)
private def sk50 : List W := [q33,q541,q505,q430,q451,q208,q242,q277,q346,q519]
private theorem k50 : optimized 9 0 sk50 = false := certified_fast (by decide +kernel)
private def sk51 : List W := [q34,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k51 : optimized 9 0 sk51 = false := certified_fast (by decide +kernel)
private def sk52 : List W := [q35,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k52 : optimized 9 0 sk52 = false := certified_fast (by decide +kernel)
private def sk53 : List W := [q36,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k53 : optimized 9 0 sk53 = false := certified_fast (by decide +kernel)
private def sk54 : List W := [q37,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k54 : optimized 9 0 sk54 = false := certified_fast (by decide +kernel)
private def sk55 : List W := [q38,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k55 : optimized 9 0 sk55 = false := certified_fast (by decide +kernel)
private def sk56 : List W := [q38,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k56 : optimized 9 0 sk56 = false := certified_fast (by decide +kernel)
private def sk57 : List W := [q39,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k57 : optimized 9 0 sk57 = false := certified_fast (by decide +kernel)
private def sk58 : List W := [q39,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k58 : optimized 9 0 sk58 = false := certified_fast (by decide +kernel)
private def sk59 : List W := [q40,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k59 : optimized 9 0 sk59 = false := certified_fast (by decide +kernel)
private def sk60 : List W := [q41,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k60 : optimized 9 0 sk60 = false := certified_fast (by decide +kernel)
private def sk61 : List W := [q42,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k61 : optimized 9 0 sk61 = false := certified_fast (by decide +kernel)
private def sk62 : List W := [q42,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k62 : optimized 9 0 sk62 = false := certified_fast (by decide +kernel)
private def sk63 : List W := [q43,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k63 : optimized 9 0 sk63 = false := certified_fast (by decide +kernel)
private def sk64 : List W := [q44,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k64 : optimized 9 0 sk64 = false := certified_fast (by decide +kernel)
private def sk65 : List W := [q45,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k65 : optimized 9 0 sk65 = false := certified_fast (by decide +kernel)
private def sk66 : List W := [q46,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k66 : optimized 9 0 sk66 = false := certified_fast (by decide +kernel)
private def sk67 : List W := [q46,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k67 : optimized 9 0 sk67 = false := certified_fast (by decide +kernel)
private def sk68 : List W := [q47,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k68 : optimized 9 0 sk68 = false := certified_fast (by decide +kernel)
private def sk69 : List W := [q48,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k69 : optimized 9 0 sk69 = false := certified_fast (by decide +kernel)
private def sk70 : List W := [q49,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k70 : optimized 9 0 sk70 = false := certified_fast (by decide +kernel)
private def sk71 : List W := [q50,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k71 : optimized 9 0 sk71 = false := certified_fast (by decide +kernel)
private def sk72 : List W := [q50,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k72 : optimized 9 0 sk72 = false := certified_fast (by decide +kernel)
private def sk73 : List W := [q51,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k73 : optimized 9 0 sk73 = false := certified_fast (by decide +kernel)
private def sk74 : List W := [q52,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k74 : optimized 9 0 sk74 = false := certified_fast (by decide +kernel)
private def sk75 : List W := [q53,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k75 : optimized 9 0 sk75 = false := certified_fast (by decide +kernel)
private def sk76 : List W := [q54,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k76 : optimized 9 0 sk76 = false := certified_fast (by decide +kernel)
private def sk77 : List W := [q55,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k77 : optimized 9 0 sk77 = false := certified_fast (by decide +kernel)
private def sk78 : List W := [q56,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k78 : optimized 9 0 sk78 = false := certified_fast (by decide +kernel)
private def sk79 : List W := [q56,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k79 : optimized 9 0 sk79 = false := certified_fast (by decide +kernel)
private def sk80 : List W := [q57,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k80 : optimized 9 0 sk80 = false := certified_fast (by decide +kernel)
private def sk81 : List W := [q58,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k81 : optimized 9 0 sk81 = false := certified_fast (by decide +kernel)
private def sk82 : List W := [q59,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k82 : optimized 9 0 sk82 = false := certified_fast (by decide +kernel)
private def sk83 : List W := [q60,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k83 : optimized 9 0 sk83 = false := certified_fast (by decide +kernel)
private def sk84 : List W := [q61,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k84 : optimized 9 0 sk84 = false := certified_fast (by decide +kernel)
private def sk85 : List W := [q62,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k85 : optimized 9 0 sk85 = false := certified_fast (by decide +kernel)
private def sk86 : List W := [q63,q519,q399,q451,q208,q242,q478,q277,q346,q541]
private theorem k86 : optimized 9 0 sk86 = false := certified_fast (by decide +kernel)
private def sk87 : List W := [q64,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k87 : optimized 9 0 sk87 = false := certified_fast (by decide +kernel)
private def sk88 : List W := [q65,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k88 : optimized 9 0 sk88 = false := certified_fast (by decide +kernel)
private def sk89 : List W := [q66,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k89 : optimized 9 0 sk89 = false := certified_fast (by decide +kernel)
private def sk90 : List W := [q67,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k90 : optimized 9 0 sk90 = false := certified_fast (by decide +kernel)
private def sk91 : List W := [q67,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k91 : optimized 9 0 sk91 = false := certified_fast (by decide +kernel)
private def sk92 : List W := [q68,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k92 : optimized 9 0 sk92 = false := certified_fast (by decide +kernel)
private def sk93 : List W := [q69,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k93 : optimized 9 0 sk93 = false := certified_fast (by decide +kernel)
private def sk94 : List W := [q69,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k94 : optimized 9 0 sk94 = false := certified_fast (by decide +kernel)
private def sk95 : List W := [q70,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k95 : optimized 9 0 sk95 = false := certified_fast (by decide +kernel)
private def sk96 : List W := [q70,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k96 : optimized 9 0 sk96 = false := certified_fast (by decide +kernel)
private def sk97 : List W := [q71,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k97 : optimized 9 0 sk97 = false := certified_fast (by decide +kernel)
private def sk98 : List W := [q72,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k98 : optimized 9 0 sk98 = false := certified_fast (by decide +kernel)
private def sk99 : List W := [q73,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k99 : optimized 9 0 sk99 = false := certified_fast (by decide +kernel)
private def sk100 : List W := [q74,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k100 : optimized 9 0 sk100 = false := certified_fast (by decide +kernel)
private def sk101 : List W := [q75,q197,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k101 : optimized 9 0 sk101 = false := certified_fast (by decide +kernel)
private def sk102 : List W := [q75,q208,q399,q451,q242,q478,q277,q346,q519,q541]
private theorem k102 : optimized 9 0 sk102 = false := certified_fast (by decide +kernel)
private def sk103 : List W := [q75,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k103 : optimized 9 0 sk103 = false := certified_fast (by decide +kernel)
private def sk104 : List W := [q75,q430,q197,q451,q242,q478,q277,q346,q519,q541]
private theorem k104 : optimized 9 0 sk104 = false := certified_fast (by decide +kernel)
private def sk105 : List W := [q75,q430,q399,q451,q242,q478,q277,q346,q519,q541]
private theorem k105 : optimized 9 0 sk105 = false := certified_fast (by decide +kernel)
private def sk106 : List W := [q76,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k106 : optimized 9 0 sk106 = false := certified_fast (by decide +kernel)
private def sk107 : List W := [q77,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k107 : optimized 9 0 sk107 = false := certified_fast (by decide +kernel)
private def sk108 : List W := [q78,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k108 : optimized 9 0 sk108 = false := certified_fast (by decide +kernel)
private def sk109 : List W := [q79,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k109 : optimized 9 0 sk109 = false := certified_fast (by decide +kernel)
private def sk110 : List W := [q80,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k110 : optimized 9 0 sk110 = false := certified_fast (by decide +kernel)
private def sk111 : List W := [q80,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k111 : optimized 9 0 sk111 = false := certified_fast (by decide +kernel)
private def sk112 : List W := [q81,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k112 : optimized 9 0 sk112 = false := certified_fast (by decide +kernel)
private def sk113 : List W := [q82,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k113 : optimized 9 0 sk113 = false := certified_fast (by decide +kernel)
private def sk114 : List W := [q83,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k114 : optimized 9 0 sk114 = false := certified_fast (by decide +kernel)
private def sk115 : List W := [q83,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k115 : optimized 9 0 sk115 = false := certified_fast (by decide +kernel)
private def sk116 : List W := [q84,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k116 : optimized 9 0 sk116 = false := certified_fast (by decide +kernel)
private def sk117 : List W := [q85,q231,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k117 : optimized 9 0 sk117 = false := certified_fast (by decide +kernel)
private def sk118 : List W := [q85,q242,q384,q451,q208,q478,q277,q346,q519,q541]
private theorem k118 : optimized 9 0 sk118 = false := certified_fast (by decide +kernel)
private def sk119 : List W := [q85,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k119 : optimized 9 0 sk119 = false := certified_fast (by decide +kernel)
private def sk120 : List W := [q85,q430,q231,q451,q208,q478,q277,q346,q519,q541]
private theorem k120 : optimized 9 0 sk120 = false := certified_fast (by decide +kernel)
private def sk121 : List W := [q85,q430,q384,q451,q208,q478,q277,q346,q519,q541]
private theorem k121 : optimized 9 0 sk121 = false := certified_fast (by decide +kernel)
private def sk122 : List W := [q86,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k122 : optimized 9 0 sk122 = false := certified_fast (by decide +kernel)
private def sk123 : List W := [q87,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k123 : optimized 9 0 sk123 = false := certified_fast (by decide +kernel)
private def sk124 : List W := [q88,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k124 : optimized 9 0 sk124 = false := certified_fast (by decide +kernel)
private def sk125 : List W := [q89,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k125 : optimized 9 0 sk125 = false := certified_fast (by decide +kernel)
private def sk126 : List W := [q90,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k126 : optimized 9 0 sk126 = false := certified_fast (by decide +kernel)
private def sk127 : List W := [q91,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k127 : optimized 9 0 sk127 = false := certified_fast (by decide +kernel)
private def sk128 : List W := [q92,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k128 : optimized 9 0 sk128 = false := certified_fast (by decide +kernel)
private def sk129 : List W := [q93,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k129 : optimized 9 0 sk129 = false := certified_fast (by decide +kernel)
private def sk130 : List W := [q94,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k130 : optimized 9 0 sk130 = false := certified_fast (by decide +kernel)
private def sk131 : List W := [q95,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k131 : optimized 9 0 sk131 = false := certified_fast (by decide +kernel)
private def sk132 : List W := [q96,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k132 : optimized 9 0 sk132 = false := certified_fast (by decide +kernel)
private def sk133 : List W := [q96,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k133 : optimized 9 0 sk133 = false := certified_fast (by decide +kernel)
private def sk134 : List W := [q97,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k134 : optimized 9 0 sk134 = false := certified_fast (by decide +kernel)
private def sk135 : List W := [q98,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k135 : optimized 9 0 sk135 = false := certified_fast (by decide +kernel)
private def sk136 : List W := [q99,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k136 : optimized 9 0 sk136 = false := certified_fast (by decide +kernel)
private def sk137 : List W := [q100,q335,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k137 : optimized 9 0 sk137 = false := certified_fast (by decide +kernel)
private def sk138 : List W := [q100,q346,q297,q451,q208,q242,q478,q277,q519,q541]
private theorem k138 : optimized 9 0 sk138 = false := certified_fast (by decide +kernel)
private def sk139 : List W := [q100,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k139 : optimized 9 0 sk139 = false := certified_fast (by decide +kernel)
private def sk140 : List W := [q100,q346,q436,q451,q208,q242,q478,q277,q519,q541]
private theorem k140 : optimized 9 0 sk140 = false := certified_fast (by decide +kernel)
private def sk141 : List W := [q100,q430,q297,q451,q208,q242,q478,q277,q519,q541]
private theorem k141 : optimized 9 0 sk141 = false := certified_fast (by decide +kernel)
private def sk142 : List W := [q100,q430,q335,q451,q208,q242,q478,q277,q519,q541]
private theorem k142 : optimized 9 0 sk142 = false := certified_fast (by decide +kernel)
private def sk143 : List W := [q100,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k143 : optimized 9 0 sk143 = false := certified_fast (by decide +kernel)
private def sk144 : List W := [q100,q436,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k144 : optimized 9 0 sk144 = false := certified_fast (by decide +kernel)
private def sk145 : List W := [q101,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k145 : optimized 9 0 sk145 = false := certified_fast (by decide +kernel)
private def sk146 : List W := [q102,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k146 : optimized 9 0 sk146 = false := certified_fast (by decide +kernel)
private def sk147 : List W := [q103,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k147 : optimized 9 0 sk147 = false := certified_fast (by decide +kernel)
private def sk148 : List W := [q103,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k148 : optimized 9 0 sk148 = false := certified_fast (by decide +kernel)
private def sk149 : List W := [q104,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k149 : optimized 9 0 sk149 = false := certified_fast (by decide +kernel)
private def sk150 : List W := [q105,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k150 : optimized 9 0 sk150 = false := certified_fast (by decide +kernel)
private def sk151 : List W := [q106,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k151 : optimized 9 0 sk151 = false := certified_fast (by decide +kernel)
private def sk152 : List W := [q106,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k152 : optimized 9 0 sk152 = false := certified_fast (by decide +kernel)
private def sk153 : List W := [q107,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k153 : optimized 9 0 sk153 = false := certified_fast (by decide +kernel)
private def sk154 : List W := [q108,q478,q197,q430,q451,q242,q277,q346,q519,q541]
private theorem k154 : optimized 9 0 sk154 = false := certified_fast (by decide +kernel)
private def sk155 : List W := [q108,q478,q399,q430,q451,q242,q277,q346,q519,q541]
private theorem k155 : optimized 9 0 sk155 = false := certified_fast (by decide +kernel)
private def sk156 : List W := [q109,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k156 : optimized 9 0 sk156 = false := certified_fast (by decide +kernel)
private def sk157 : List W := [q110,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k157 : optimized 9 0 sk157 = false := certified_fast (by decide +kernel)
private def sk158 : List W := [q111,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k158 : optimized 9 0 sk158 = false := certified_fast (by decide +kernel)
private def sk159 : List W := [q111,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k159 : optimized 9 0 sk159 = false := certified_fast (by decide +kernel)
private def sk160 : List W := [q112,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k160 : optimized 9 0 sk160 = false := certified_fast (by decide +kernel)
private def sk161 : List W := [q113,q242,q177,q430,q451,q208,q277,q346,q519,q541]
private theorem k161 : optimized 9 0 sk161 = false := certified_fast (by decide +kernel)
private def sk162 : List W := [q113,q242,q505,q430,q451,q208,q277,q346,q519,q541]
private theorem k162 : optimized 9 0 sk162 = false := certified_fast (by decide +kernel)
private def sk163 : List W := [q113,q478,q231,q430,q451,q208,q277,q346,q519,q541]
private theorem k163 : optimized 9 0 sk163 = false := certified_fast (by decide +kernel)
private def sk164 : List W := [q113,q478,q384,q430,q451,q208,q277,q346,q519,q541]
private theorem k164 : optimized 9 0 sk164 = false := certified_fast (by decide +kernel)
private def sk165 : List W := [q114,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k165 : optimized 9 0 sk165 = false := certified_fast (by decide +kernel)
private def sk166 : List W := [q115,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k166 : optimized 9 0 sk166 = false := certified_fast (by decide +kernel)
private def sk167 : List W := [q116,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k167 : optimized 9 0 sk167 = false := certified_fast (by decide +kernel)
private def sk168 : List W := [q117,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k168 : optimized 9 0 sk168 = false := certified_fast (by decide +kernel)
private def sk169 : List W := [q118,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k169 : optimized 9 0 sk169 = false := certified_fast (by decide +kernel)
private def sk170 : List W := [q119,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k170 : optimized 9 0 sk170 = false := certified_fast (by decide +kernel)
private def sk171 : List W := [q120,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k171 : optimized 9 0 sk171 = false := certified_fast (by decide +kernel)
private def sk172 : List W := [q120,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k172 : optimized 9 0 sk172 = false := certified_fast (by decide +kernel)
private def sk173 : List W := [q120,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k173 : optimized 9 0 sk173 = false := certified_fast (by decide +kernel)
private def sk174 : List W := [q121,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k174 : optimized 9 0 sk174 = false := certified_fast (by decide +kernel)
private def sk175 : List W := [q122,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k175 : optimized 9 0 sk175 = false := certified_fast (by decide +kernel)
private def sk176 : List W := [q123,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k176 : optimized 9 0 sk176 = false := certified_fast (by decide +kernel)
private def sk177 : List W := [q124,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k177 : optimized 9 0 sk177 = false := certified_fast (by decide +kernel)
private def sk178 : List W := [q124,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k178 : optimized 9 0 sk178 = false := certified_fast (by decide +kernel)
private def sk179 : List W := [q125,q328,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k179 : optimized 9 0 sk179 = false := certified_fast (by decide +kernel)
private def sk180 : List W := [q125,q346,q307,q430,q451,q208,q242,q277,q519,q541]
private theorem k180 : optimized 9 0 sk180 = false := certified_fast (by decide +kernel)
private def sk181 : List W := [q125,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k181 : optimized 9 0 sk181 = false := certified_fast (by decide +kernel)
private def sk182 : List W := [q125,q346,q495,q430,q451,q208,q242,q277,q519,q541]
private theorem k182 : optimized 9 0 sk182 = false := certified_fast (by decide +kernel)
private def sk183 : List W := [q125,q478,q297,q430,q451,q208,q242,q277,q519,q541]
private theorem k183 : optimized 9 0 sk183 = false := certified_fast (by decide +kernel)
private def sk184 : List W := [q125,q478,q307,q430,q451,q208,q242,q277,q519,q541]
private theorem k184 : optimized 9 0 sk184 = false := certified_fast (by decide +kernel)
private def sk185 : List W := [q125,q478,q328,q430,q451,q208,q242,q277,q519,q541]
private theorem k185 : optimized 9 0 sk185 = false := certified_fast (by decide +kernel)
private def sk186 : List W := [q125,q478,q335,q430,q451,q208,q242,q277,q519,q541]
private theorem k186 : optimized 9 0 sk186 = false := certified_fast (by decide +kernel)
private def sk187 : List W := [q125,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k187 : optimized 9 0 sk187 = false := certified_fast (by decide +kernel)
private def sk188 : List W := [q125,q495,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k188 : optimized 9 0 sk188 = false := certified_fast (by decide +kernel)
private def sk189 : List W := [q126,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k189 : optimized 9 0 sk189 = false := certified_fast (by decide +kernel)
private def sk190 : List W := [q127,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k190 : optimized 9 0 sk190 = false := certified_fast (by decide +kernel)
private def sk191 : List W := [q128,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k191 : optimized 9 0 sk191 = false := certified_fast (by decide +kernel)
private def sk192 : List W := [q128,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k192 : optimized 9 0 sk192 = false := certified_fast (by decide +kernel)
private def sk193 : List W := [q129,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k193 : optimized 9 0 sk193 = false := certified_fast (by decide +kernel)
private def sk194 : List W := [q129,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k194 : optimized 9 0 sk194 = false := certified_fast (by decide +kernel)
private def sk195 : List W := [q130,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k195 : optimized 9 0 sk195 = false := certified_fast (by decide +kernel)
private def sk196 : List W := [q130,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k196 : optimized 9 0 sk196 = false := certified_fast (by decide +kernel)
private def sk197 : List W := [q131,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k197 : optimized 9 0 sk197 = false := certified_fast (by decide +kernel)
private def sk198 : List W := [q132,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k198 : optimized 9 0 sk198 = false := certified_fast (by decide +kernel)
private def sk199 : List W := [q133,q423,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k199 : optimized 9 0 sk199 = false := certified_fast (by decide +kernel)
private def sk200 : List W := [q133,q430,q177,q451,q208,q242,q277,q346,q519,q541]
private theorem k200 : optimized 9 0 sk200 = false := certified_fast (by decide +kernel)
private def sk201 : List W := [q133,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k201 : optimized 9 0 sk201 = false := certified_fast (by decide +kernel)
private def sk202 : List W := [q133,q430,q505,q451,q208,q242,q277,q346,q519,q541]
private theorem k202 : optimized 9 0 sk202 = false := certified_fast (by decide +kernel)
private def sk203 : List W := [q133,q478,q177,q451,q208,q242,q277,q346,q519,q541]
private theorem k203 : optimized 9 0 sk203 = false := certified_fast (by decide +kernel)
private def sk204 : List W := [q133,q478,q384,q451,q208,q242,q277,q346,q519,q541]
private theorem k204 : optimized 9 0 sk204 = false := certified_fast (by decide +kernel)
private def sk205 : List W := [q133,q478,q423,q451,q208,q242,q277,q346,q519,q541]
private theorem k205 : optimized 9 0 sk205 = false := certified_fast (by decide +kernel)
private def sk206 : List W := [q133,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k206 : optimized 9 0 sk206 = false := certified_fast (by decide +kernel)
private def sk207 : List W := [q133,q505,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k207 : optimized 9 0 sk207 = false := certified_fast (by decide +kernel)
private def sk208 : List W := [q134,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k208 : optimized 9 0 sk208 = false := certified_fast (by decide +kernel)
private def sk209 : List W := [q135,q478,q157,q430,q208,q242,q277,q346,q519,q541]
private theorem k209 : optimized 9 0 sk209 = false := certified_fast (by decide +kernel)
private def sk210 : List W := [q135,q478,q414,q430,q208,q242,q277,q346,q519,q541]
private theorem k210 : optimized 9 0 sk210 = false := certified_fast (by decide +kernel)
private def sk211 : List W := [q136,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k211 : optimized 9 0 sk211 = false := certified_fast (by decide +kernel)
private def sk212 : List W := [q137,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k212 : optimized 9 0 sk212 = false := certified_fast (by decide +kernel)
private def sk213 : List W := [q137,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k213 : optimized 9 0 sk213 = false := certified_fast (by decide +kernel)
private def sk214 : List W := [q138,q451,q197,q430,q242,q478,q277,q346,q519,q541]
private theorem k214 : optimized 9 0 sk214 = false := certified_fast (by decide +kernel)
private def sk215 : List W := [q138,q451,q399,q430,q242,q478,q277,q346,q519,q541]
private theorem k215 : optimized 9 0 sk215 = false := certified_fast (by decide +kernel)
private def sk216 : List W := [q139,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k216 : optimized 9 0 sk216 = false := certified_fast (by decide +kernel)
private def sk217 : List W := [q140,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k217 : optimized 9 0 sk217 = false := certified_fast (by decide +kernel)
private def sk218 : List W := [q140,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k218 : optimized 9 0 sk218 = false := certified_fast (by decide +kernel)
private def sk219 : List W := [q141,q451,q231,q430,q208,q478,q277,q346,q519,q541]
private theorem k219 : optimized 9 0 sk219 = false := certified_fast (by decide +kernel)
private def sk220 : List W := [q141,q451,q384,q430,q208,q478,q277,q346,q519,q541]
private theorem k220 : optimized 9 0 sk220 = false := certified_fast (by decide +kernel)
private def sk221 : List W := [q142,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k221 : optimized 9 0 sk221 = false := certified_fast (by decide +kernel)
private def sk222 : List W := [q143,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k222 : optimized 9 0 sk222 = false := certified_fast (by decide +kernel)
private def sk223 : List W := [q144,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k223 : optimized 9 0 sk223 = false := certified_fast (by decide +kernel)
private def sk224 : List W := [q145,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k224 : optimized 9 0 sk224 = false := certified_fast (by decide +kernel)
private def sk225 : List W := [q145,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k225 : optimized 9 0 sk225 = false := certified_fast (by decide +kernel)
private def sk226 : List W := [q146,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k226 : optimized 9 0 sk226 = false := certified_fast (by decide +kernel)
private def sk227 : List W := [q147,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k227 : optimized 9 0 sk227 = false := certified_fast (by decide +kernel)
private def sk228 : List W := [q148,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k228 : optimized 9 0 sk228 = false := certified_fast (by decide +kernel)
private def sk229 : List W := [q148,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k229 : optimized 9 0 sk229 = false := certified_fast (by decide +kernel)
private def sk230 : List W := [q149,q451,q297,q430,q208,q242,q478,q277,q519,q541]
private theorem k230 : optimized 9 0 sk230 = false := certified_fast (by decide +kernel)
private def sk231 : List W := [q149,q451,q335,q430,q208,q242,q478,q277,q519,q541]
private theorem k231 : optimized 9 0 sk231 = false := certified_fast (by decide +kernel)
private def sk232 : List W := [q150,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k232 : optimized 9 0 sk232 = false := certified_fast (by decide +kernel)
private def sk233 : List W := [q151,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k233 : optimized 9 0 sk233 = false := certified_fast (by decide +kernel)
private def sk234 : List W := [q152,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k234 : optimized 9 0 sk234 = false := certified_fast (by decide +kernel)
private def sk235 : List W := [q152,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k235 : optimized 9 0 sk235 = false := certified_fast (by decide +kernel)
private def sk236 : List W := [q153,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k236 : optimized 9 0 sk236 = false := certified_fast (by decide +kernel)
private def sk237 : List W := [q153,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k237 : optimized 9 0 sk237 = false := certified_fast (by decide +kernel)
private def sk238 : List W := [q154,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k238 : optimized 9 0 sk238 = false := certified_fast (by decide +kernel)
private def sk239 : List W := [q154,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k239 : optimized 9 0 sk239 = false := certified_fast (by decide +kernel)
private def sk240 : List W := [q155,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k240 : optimized 9 0 sk240 = false := certified_fast (by decide +kernel)
private def sk241 : List W := [q156,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k241 : optimized 9 0 sk241 = false := certified_fast (by decide +kernel)
private def sk242 : List W := [q157,q414,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k242 : optimized 9 0 sk242 = false := certified_fast (by decide +kernel)
private def sk243 : List W := [q157,q430,q169,q208,q242,q478,q277,q346,q519,q541]
private theorem k243 : optimized 9 0 sk243 = false := certified_fast (by decide +kernel)
private def sk244 : List W := [q157,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k244 : optimized 9 0 sk244 = false := certified_fast (by decide +kernel)
private def sk245 : List W := [q157,q451,q169,q208,q242,q478,q277,q346,q519,q541]
private theorem k245 : optimized 9 0 sk245 = false := certified_fast (by decide +kernel)
private def sk246 : List W := [q157,q451,q297,q208,q242,q478,q277,q346,q519,q541]
private theorem k246 : optimized 9 0 sk246 = false := certified_fast (by decide +kernel)
private def sk247 : List W := [q157,q451,q399,q208,q242,q478,q277,q346,q519,q541]
private theorem k247 : optimized 9 0 sk247 = false := certified_fast (by decide +kernel)
private def sk248 : List W := [q157,q451,q414,q208,q242,q478,q277,q346,q519,q541]
private theorem k248 : optimized 9 0 sk248 = false := certified_fast (by decide +kernel)
private def sk249 : List W := [q157,q451,q436,q208,q242,q478,q277,q346,q519,q541]
private theorem k249 : optimized 9 0 sk249 = false := certified_fast (by decide +kernel)
private def sk250 : List W := [q158,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k250 : optimized 9 0 sk250 = false := certified_fast (by decide +kernel)
private def sk251 : List W := [q159,q451,q133,q430,q208,q242,q277,q346,q519,q541]
private theorem k251 : optimized 9 0 sk251 = false := certified_fast (by decide +kernel)
private def sk252 : List W := [q159,q451,q307,q430,q208,q242,q277,q346,q519,q541]
private theorem k252 : optimized 9 0 sk252 = false := certified_fast (by decide +kernel)
private def sk253 : List W := [q159,q451,q423,q430,q208,q242,q277,q346,q519,q541]
private theorem k253 : optimized 9 0 sk253 = false := certified_fast (by decide +kernel)
private def sk254 : List W := [q159,q451,q495,q430,q208,q242,q277,q346,q519,q541]
private theorem k254 : optimized 9 0 sk254 = false := certified_fast (by decide +kernel)
private def sk255 : List W := [q160,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k255 : optimized 9 0 sk255 = false := certified_fast (by decide +kernel)
private def sk256 : List W := [q161,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k256 : optimized 9 0 sk256 = false := certified_fast (by decide +kernel)
private def sk257 : List W := [q162,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k257 : optimized 9 0 sk257 = false := certified_fast (by decide +kernel)
private def sk258 : List W := [q162,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k258 : optimized 9 0 sk258 = false := certified_fast (by decide +kernel)
private def sk259 : List W := [q163,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k259 : optimized 9 0 sk259 = false := certified_fast (by decide +kernel)
private def sk260 : List W := [q164,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k260 : optimized 9 0 sk260 = false := certified_fast (by decide +kernel)
private def sk261 : List W := [q165,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k261 : optimized 9 0 sk261 = false := certified_fast (by decide +kernel)
private def sk262 : List W := [q166,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k262 : optimized 9 0 sk262 = false := certified_fast (by decide +kernel)
private def sk263 : List W := [q166,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k263 : optimized 9 0 sk263 = false := certified_fast (by decide +kernel)
private def sk264 : List W := [q167,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k264 : optimized 9 0 sk264 = false := certified_fast (by decide +kernel)
private def sk265 : List W := [q168,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k265 : optimized 9 0 sk265 = false := certified_fast (by decide +kernel)
private def sk266 : List W := [q169,q414,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k266 : optimized 9 0 sk266 = false := certified_fast (by decide +kernel)
private def sk267 : List W := [q169,q430,q157,q208,q242,q478,q277,q346,q519,q541]
private theorem k267 : optimized 9 0 sk267 = false := certified_fast (by decide +kernel)
private def sk268 : List W := [q169,q430,q414,q208,q242,q478,q277,q346,q519,q541]
private theorem k268 : optimized 9 0 sk268 = false := certified_fast (by decide +kernel)
private def sk269 : List W := [q169,q451,q157,q208,q242,q478,q277,q346,q519,q541]
private theorem k269 : optimized 9 0 sk269 = false := certified_fast (by decide +kernel)
private def sk270 : List W := [q169,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k270 : optimized 9 0 sk270 = false := certified_fast (by decide +kernel)
private def sk271 : List W := [q170,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k271 : optimized 9 0 sk271 = false := certified_fast (by decide +kernel)
private def sk272 : List W := [q171,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k272 : optimized 9 0 sk272 = false := certified_fast (by decide +kernel)
private def sk273 : List W := [q172,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k273 : optimized 9 0 sk273 = false := certified_fast (by decide +kernel)
private def sk274 : List W := [q173,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k274 : optimized 9 0 sk274 = false := certified_fast (by decide +kernel)
private def sk275 : List W := [q174,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k275 : optimized 9 0 sk275 = false := certified_fast (by decide +kernel)
private def sk276 : List W := [q174,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k276 : optimized 9 0 sk276 = false := certified_fast (by decide +kernel)
private def sk277 : List W := [q174,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k277 : optimized 9 0 sk277 = false := certified_fast (by decide +kernel)
private def sk278 : List W := [q175,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k278 : optimized 9 0 sk278 = false := certified_fast (by decide +kernel)
private def sk279 : List W := [q176,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k279 : optimized 9 0 sk279 = false := certified_fast (by decide +kernel)
private def sk280 : List W := [q177,q423,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k280 : optimized 9 0 sk280 = false := certified_fast (by decide +kernel)
private def sk281 : List W := [q177,q430,q133,q451,q208,q242,q277,q346,q519,q541]
private theorem k281 : optimized 9 0 sk281 = false := certified_fast (by decide +kernel)
private def sk282 : List W := [q177,q430,q423,q451,q208,q242,q277,q346,q519,q541]
private theorem k282 : optimized 9 0 sk282 = false := certified_fast (by decide +kernel)
private def sk283 : List W := [q177,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k283 : optimized 9 0 sk283 = false := certified_fast (by decide +kernel)
private def sk284 : List W := [q177,q478,q133,q451,q208,q242,q277,q346,q519,q541]
private theorem k284 : optimized 9 0 sk284 = false := certified_fast (by decide +kernel)
private def sk285 : List W := [q177,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k285 : optimized 9 0 sk285 = false := certified_fast (by decide +kernel)
private def sk286 : List W := [q177,q478,q505,q451,q208,q242,q277,q346,q519,q541]
private theorem k286 : optimized 9 0 sk286 = false := certified_fast (by decide +kernel)
private def sk287 : List W := [q177,q505,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k287 : optimized 9 0 sk287 = false := certified_fast (by decide +kernel)
private def sk288 : List W := [q178,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k288 : optimized 9 0 sk288 = false := certified_fast (by decide +kernel)
private def sk289 : List W := [q179,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k289 : optimized 9 0 sk289 = false := certified_fast (by decide +kernel)
private def sk290 : List W := [q180,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k290 : optimized 9 0 sk290 = false := certified_fast (by decide +kernel)
private def sk291 : List W := [q181,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k291 : optimized 9 0 sk291 = false := certified_fast (by decide +kernel)
private def sk292 : List W := [q182,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k292 : optimized 9 0 sk292 = false := certified_fast (by decide +kernel)
private def sk293 : List W := [q183,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k293 : optimized 9 0 sk293 = false := certified_fast (by decide +kernel)
private def sk294 : List W := [q184,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k294 : optimized 9 0 sk294 = false := certified_fast (by decide +kernel)
private def sk295 : List W := [q185,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k295 : optimized 9 0 sk295 = false := certified_fast (by decide +kernel)
private def sk296 : List W := [q186,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k296 : optimized 9 0 sk296 = false := certified_fast (by decide +kernel)
private def sk297 : List W := [q186,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k297 : optimized 9 0 sk297 = false := certified_fast (by decide +kernel)
private def sk298 : List W := [q187,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k298 : optimized 9 0 sk298 = false := certified_fast (by decide +kernel)
private def sk299 : List W := [q188,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k299 : optimized 9 0 sk299 = false := certified_fast (by decide +kernel)
private def sk300 : List W := [q189,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k300 : optimized 9 0 sk300 = false := certified_fast (by decide +kernel)
private def sk301 : List W := [q189,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k301 : optimized 9 0 sk301 = false := certified_fast (by decide +kernel)
private def sk302 : List W := [q190,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k302 : optimized 9 0 sk302 = false := certified_fast (by decide +kernel)
private def sk303 : List W := [q191,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k303 : optimized 9 0 sk303 = false := certified_fast (by decide +kernel)
private def sk304 : List W := [q192,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k304 : optimized 9 0 sk304 = false := certified_fast (by decide +kernel)
private def sk305 : List W := [q193,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k305 : optimized 9 0 sk305 = false := certified_fast (by decide +kernel)
private def sk306 : List W := [q193,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k306 : optimized 9 0 sk306 = false := certified_fast (by decide +kernel)
private def sk307 : List W := [q194,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k307 : optimized 9 0 sk307 = false := certified_fast (by decide +kernel)
private def sk308 : List W := [q195,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k308 : optimized 9 0 sk308 = false := certified_fast (by decide +kernel)
private def sk309 : List W := [q195,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k309 : optimized 9 0 sk309 = false := certified_fast (by decide +kernel)
private def sk310 : List W := [q196,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k310 : optimized 9 0 sk310 = false := certified_fast (by decide +kernel)
private def sk311 : List W := [q197,q75,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k311 : optimized 9 0 sk311 = false := certified_fast (by decide +kernel)
private def sk312 : List W := [q197,q208,q399,q451,q242,q478,q277,q346,q519,q541]
private theorem k312 : optimized 9 0 sk312 = false := certified_fast (by decide +kernel)
private def sk313 : List W := [q197,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k313 : optimized 9 0 sk313 = false := certified_fast (by decide +kernel)
private def sk314 : List W := [q197,q399,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k314 : optimized 9 0 sk314 = false := certified_fast (by decide +kernel)
private def sk315 : List W := [q197,q430,q75,q451,q242,q478,q277,q346,q519,q541]
private theorem k315 : optimized 9 0 sk315 = false := certified_fast (by decide +kernel)
private def sk316 : List W := [q197,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k316 : optimized 9 0 sk316 = false := certified_fast (by decide +kernel)
private def sk317 : List W := [q198,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k317 : optimized 9 0 sk317 = false := certified_fast (by decide +kernel)
private def sk318 : List W := [q199,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k318 : optimized 9 0 sk318 = false := certified_fast (by decide +kernel)
private def sk319 : List W := [q200,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k319 : optimized 9 0 sk319 = false := certified_fast (by decide +kernel)
private def sk320 : List W := [q201,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k320 : optimized 9 0 sk320 = false := certified_fast (by decide +kernel)
private def sk321 : List W := [q202,q277,q197,q430,q451,q242,q478,q346,q519,q541]
private theorem k321 : optimized 9 0 sk321 = false := certified_fast (by decide +kernel)
private def sk322 : List W := [q202,q277,q399,q430,q451,q242,q478,q346,q519,q541]
private theorem k322 : optimized 9 0 sk322 = false := certified_fast (by decide +kernel)
private def sk323 : List W := [q203,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k323 : optimized 9 0 sk323 = false := certified_fast (by decide +kernel)
private def sk324 : List W := [q204,q177,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k324 : optimized 9 0 sk324 = false := certified_fast (by decide +kernel)
private def sk325 : List W := [q204,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k325 : optimized 9 0 sk325 = false := certified_fast (by decide +kernel)
private def sk326 : List W := [q205,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k326 : optimized 9 0 sk326 = false := certified_fast (by decide +kernel)
private def sk327 : List W := [q206,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k327 : optimized 9 0 sk327 = false := certified_fast (by decide +kernel)
private def sk328 : List W := [q207,q169,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k328 : optimized 9 0 sk328 = false := certified_fast (by decide +kernel)
private def sk329 : List W := [q207,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k329 : optimized 9 0 sk329 = false := certified_fast (by decide +kernel)
private def sk330 : List W := [q209,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k330 : optimized 9 0 sk330 = false := certified_fast (by decide +kernel)
private def sk331 : List W := [q210,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k331 : optimized 9 0 sk331 = false := certified_fast (by decide +kernel)
private def sk332 : List W := [q211,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k332 : optimized 9 0 sk332 = false := certified_fast (by decide +kernel)
private def sk333 : List W := [q212,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k333 : optimized 9 0 sk333 = false := certified_fast (by decide +kernel)
private def sk334 : List W := [q213,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k334 : optimized 9 0 sk334 = false := certified_fast (by decide +kernel)
private def sk335 : List W := [q214,q169,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k335 : optimized 9 0 sk335 = false := certified_fast (by decide +kernel)
private def sk336 : List W := [q214,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k336 : optimized 9 0 sk336 = false := certified_fast (by decide +kernel)
private def sk337 : List W := [q215,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k337 : optimized 9 0 sk337 = false := certified_fast (by decide +kernel)
private def sk338 : List W := [q216,q177,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k338 : optimized 9 0 sk338 = false := certified_fast (by decide +kernel)
private def sk339 : List W := [q216,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k339 : optimized 9 0 sk339 = false := certified_fast (by decide +kernel)
private def sk340 : List W := [q217,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k340 : optimized 9 0 sk340 = false := certified_fast (by decide +kernel)
private def sk341 : List W := [q218,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k341 : optimized 9 0 sk341 = false := certified_fast (by decide +kernel)
private def sk342 : List W := [q219,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k342 : optimized 9 0 sk342 = false := certified_fast (by decide +kernel)
private def sk343 : List W := [q219,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k343 : optimized 9 0 sk343 = false := certified_fast (by decide +kernel)
private def sk344 : List W := [q220,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k344 : optimized 9 0 sk344 = false := certified_fast (by decide +kernel)
private def sk345 : List W := [q221,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k345 : optimized 9 0 sk345 = false := certified_fast (by decide +kernel)
private def sk346 : List W := [q222,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k346 : optimized 9 0 sk346 = false := certified_fast (by decide +kernel)
private def sk347 : List W := [q222,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k347 : optimized 9 0 sk347 = false := certified_fast (by decide +kernel)
private def sk348 : List W := [q223,q242,q177,q430,q451,q208,q277,q346,q519,q541]
private theorem k348 : optimized 9 0 sk348 = false := certified_fast (by decide +kernel)
private def sk349 : List W := [q223,q242,q505,q430,q451,q208,q277,q346,q519,q541]
private theorem k349 : optimized 9 0 sk349 = false := certified_fast (by decide +kernel)
private def sk350 : List W := [q224,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k350 : optimized 9 0 sk350 = false := certified_fast (by decide +kernel)
private def sk351 : List W := [q225,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k351 : optimized 9 0 sk351 = false := certified_fast (by decide +kernel)
private def sk352 : List W := [q226,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k352 : optimized 9 0 sk352 = false := certified_fast (by decide +kernel)
private def sk353 : List W := [q227,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k353 : optimized 9 0 sk353 = false := certified_fast (by decide +kernel)
private def sk354 : List W := [q227,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k354 : optimized 9 0 sk354 = false := certified_fast (by decide +kernel)
private def sk355 : List W := [q228,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k355 : optimized 9 0 sk355 = false := certified_fast (by decide +kernel)
private def sk356 : List W := [q228,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k356 : optimized 9 0 sk356 = false := certified_fast (by decide +kernel)
private def sk357 : List W := [q229,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k357 : optimized 9 0 sk357 = false := certified_fast (by decide +kernel)
private def sk358 : List W := [q230,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k358 : optimized 9 0 sk358 = false := certified_fast (by decide +kernel)
private def sk359 : List W := [q231,q85,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k359 : optimized 9 0 sk359 = false := certified_fast (by decide +kernel)
private def sk360 : List W := [q231,q242,q384,q451,q208,q478,q277,q346,q519,q541]
private theorem k360 : optimized 9 0 sk360 = false := certified_fast (by decide +kernel)
private def sk361 : List W := [q231,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k361 : optimized 9 0 sk361 = false := certified_fast (by decide +kernel)
private def sk362 : List W := [q231,q384,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k362 : optimized 9 0 sk362 = false := certified_fast (by decide +kernel)
private def sk363 : List W := [q231,q430,q85,q451,q208,q478,q277,q346,q519,q541]
private theorem k363 : optimized 9 0 sk363 = false := certified_fast (by decide +kernel)
private def sk364 : List W := [q231,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k364 : optimized 9 0 sk364 = false := certified_fast (by decide +kernel)
private def sk365 : List W := [q232,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k365 : optimized 9 0 sk365 = false := certified_fast (by decide +kernel)
private def sk366 : List W := [q233,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k366 : optimized 9 0 sk366 = false := certified_fast (by decide +kernel)
private def sk367 : List W := [q234,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k367 : optimized 9 0 sk367 = false := certified_fast (by decide +kernel)
private def sk368 : List W := [q235,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k368 : optimized 9 0 sk368 = false := certified_fast (by decide +kernel)
private def sk369 : List W := [q236,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k369 : optimized 9 0 sk369 = false := certified_fast (by decide +kernel)
private def sk370 : List W := [q237,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k370 : optimized 9 0 sk370 = false := certified_fast (by decide +kernel)
private def sk371 : List W := [q238,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k371 : optimized 9 0 sk371 = false := certified_fast (by decide +kernel)
private def sk372 : List W := [q239,q277,q231,q430,q451,q208,q478,q346,q519,q541]
private theorem k372 : optimized 9 0 sk372 = false := certified_fast (by decide +kernel)
private def sk373 : List W := [q239,q277,q384,q430,q451,q208,q478,q346,q519,q541]
private theorem k373 : optimized 9 0 sk373 = false := certified_fast (by decide +kernel)
private def sk374 : List W := [q240,q177,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k374 : optimized 9 0 sk374 = false := certified_fast (by decide +kernel)
private def sk375 : List W := [q240,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k375 : optimized 9 0 sk375 = false := certified_fast (by decide +kernel)
private def sk376 : List W := [q241,q169,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k376 : optimized 9 0 sk376 = false := certified_fast (by decide +kernel)
private def sk377 : List W := [q241,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k377 : optimized 9 0 sk377 = false := certified_fast (by decide +kernel)
private def sk378 : List W := [q243,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k378 : optimized 9 0 sk378 = false := certified_fast (by decide +kernel)
private def sk379 : List W := [q244,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k379 : optimized 9 0 sk379 = false := certified_fast (by decide +kernel)
private def sk380 : List W := [q245,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k380 : optimized 9 0 sk380 = false := certified_fast (by decide +kernel)
private def sk381 : List W := [q246,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k381 : optimized 9 0 sk381 = false := certified_fast (by decide +kernel)
private def sk382 : List W := [q247,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k382 : optimized 9 0 sk382 = false := certified_fast (by decide +kernel)
private def sk383 : List W := [q248,q169,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k383 : optimized 9 0 sk383 = false := certified_fast (by decide +kernel)
private def sk384 : List W := [q248,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k384 : optimized 9 0 sk384 = false := certified_fast (by decide +kernel)
private def sk385 : List W := [q249,q384,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k385 : optimized 9 0 sk385 = false := certified_fast (by decide +kernel)
private def sk386 : List W := [q249,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k386 : optimized 9 0 sk386 = false := certified_fast (by decide +kernel)
private def sk387 : List W := [q250,q177,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k387 : optimized 9 0 sk387 = false := certified_fast (by decide +kernel)
private def sk388 : List W := [q250,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k388 : optimized 9 0 sk388 = false := certified_fast (by decide +kernel)
private def sk389 : List W := [q251,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k389 : optimized 9 0 sk389 = false := certified_fast (by decide +kernel)
private def sk390 : List W := [q252,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k390 : optimized 9 0 sk390 = false := certified_fast (by decide +kernel)
private def sk391 : List W := [q253,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k391 : optimized 9 0 sk391 = false := certified_fast (by decide +kernel)
private def sk392 : List W := [q254,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k392 : optimized 9 0 sk392 = false := certified_fast (by decide +kernel)
private def sk393 : List W := [q255,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k393 : optimized 9 0 sk393 = false := certified_fast (by decide +kernel)
private def sk394 : List W := [q256,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k394 : optimized 9 0 sk394 = false := certified_fast (by decide +kernel)
private def sk395 : List W := [q257,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k395 : optimized 9 0 sk395 = false := certified_fast (by decide +kernel)
private def sk396 : List W := [q258,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k396 : optimized 9 0 sk396 = false := certified_fast (by decide +kernel)
private def sk397 : List W := [q259,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k397 : optimized 9 0 sk397 = false := certified_fast (by decide +kernel)
private def sk398 : List W := [q260,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k398 : optimized 9 0 sk398 = false := certified_fast (by decide +kernel)
private def sk399 : List W := [q261,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k399 : optimized 9 0 sk399 = false := certified_fast (by decide +kernel)
private def sk400 : List W := [q262,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k400 : optimized 9 0 sk400 = false := certified_fast (by decide +kernel)
private def sk401 : List W := [q263,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k401 : optimized 9 0 sk401 = false := certified_fast (by decide +kernel)
private def sk402 : List W := [q264,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k402 : optimized 9 0 sk402 = false := certified_fast (by decide +kernel)
private def sk403 : List W := [q265,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k403 : optimized 9 0 sk403 = false := certified_fast (by decide +kernel)
private def sk404 : List W := [q266,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k404 : optimized 9 0 sk404 = false := certified_fast (by decide +kernel)
private def sk405 : List W := [q267,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k405 : optimized 9 0 sk405 = false := certified_fast (by decide +kernel)
private def sk406 : List W := [q268,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k406 : optimized 9 0 sk406 = false := certified_fast (by decide +kernel)
private def sk407 : List W := [q269,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k407 : optimized 9 0 sk407 = false := certified_fast (by decide +kernel)
private def sk408 : List W := [q270,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k408 : optimized 9 0 sk408 = false := certified_fast (by decide +kernel)
private def sk409 : List W := [q271,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k409 : optimized 9 0 sk409 = false := certified_fast (by decide +kernel)
private def sk410 : List W := [q272,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k410 : optimized 9 0 sk410 = false := certified_fast (by decide +kernel)
private def sk411 : List W := [q273,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k411 : optimized 9 0 sk411 = false := certified_fast (by decide +kernel)
private def sk412 : List W := [q274,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k412 : optimized 9 0 sk412 = false := certified_fast (by decide +kernel)
private def sk413 : List W := [q275,q177,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k413 : optimized 9 0 sk413 = false := certified_fast (by decide +kernel)
private def sk414 : List W := [q275,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k414 : optimized 9 0 sk414 = false := certified_fast (by decide +kernel)
private def sk415 : List W := [q276,q169,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k415 : optimized 9 0 sk415 = false := certified_fast (by decide +kernel)
private def sk416 : List W := [q276,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k416 : optimized 9 0 sk416 = false := certified_fast (by decide +kernel)
private def sk417 : List W := [q278,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k417 : optimized 9 0 sk417 = false := certified_fast (by decide +kernel)
private def sk418 : List W := [q279,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k418 : optimized 9 0 sk418 = false := certified_fast (by decide +kernel)
private def sk419 : List W := [q280,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k419 : optimized 9 0 sk419 = false := certified_fast (by decide +kernel)
private def sk420 : List W := [q281,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k420 : optimized 9 0 sk420 = false := certified_fast (by decide +kernel)
private def sk421 : List W := [q282,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k421 : optimized 9 0 sk421 = false := certified_fast (by decide +kernel)
private def sk422 : List W := [q283,q169,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k422 : optimized 9 0 sk422 = false := certified_fast (by decide +kernel)
private def sk423 : List W := [q283,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k423 : optimized 9 0 sk423 = false := certified_fast (by decide +kernel)
private def sk424 : List W := [q284,q177,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k424 : optimized 9 0 sk424 = false := certified_fast (by decide +kernel)
private def sk425 : List W := [q284,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k425 : optimized 9 0 sk425 = false := certified_fast (by decide +kernel)
private def sk426 : List W := [q285,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k426 : optimized 9 0 sk426 = false := certified_fast (by decide +kernel)
private def sk427 : List W := [q285,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k427 : optimized 9 0 sk427 = false := certified_fast (by decide +kernel)
private def sk428 : List W := [q286,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k428 : optimized 9 0 sk428 = false := certified_fast (by decide +kernel)
private def sk429 : List W := [q287,q277,q197,q430,q451,q242,q478,q346,q519,q541]
private theorem k429 : optimized 9 0 sk429 = false := certified_fast (by decide +kernel)
private def sk430 : List W := [q287,q277,q399,q430,q451,q242,q478,q346,q519,q541]
private theorem k430 : optimized 9 0 sk430 = false := certified_fast (by decide +kernel)
private def sk431 : List W := [q288,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k431 : optimized 9 0 sk431 = false := certified_fast (by decide +kernel)
private def sk432 : List W := [q289,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k432 : optimized 9 0 sk432 = false := certified_fast (by decide +kernel)
private def sk433 : List W := [q289,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k433 : optimized 9 0 sk433 = false := certified_fast (by decide +kernel)
private def sk434 : List W := [q290,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k434 : optimized 9 0 sk434 = false := certified_fast (by decide +kernel)
private def sk435 : List W := [q291,q277,q231,q430,q451,q208,q478,q346,q519,q541]
private theorem k435 : optimized 9 0 sk435 = false := certified_fast (by decide +kernel)
private def sk436 : List W := [q291,q277,q384,q430,q451,q208,q478,q346,q519,q541]
private theorem k436 : optimized 9 0 sk436 = false := certified_fast (by decide +kernel)
private def sk437 : List W := [q292,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k437 : optimized 9 0 sk437 = false := certified_fast (by decide +kernel)
private def sk438 : List W := [q293,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k438 : optimized 9 0 sk438 = false := certified_fast (by decide +kernel)
private def sk439 : List W := [q293,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k439 : optimized 9 0 sk439 = false := certified_fast (by decide +kernel)
private def sk440 : List W := [q294,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k440 : optimized 9 0 sk440 = false := certified_fast (by decide +kernel)
private def sk441 : List W := [q294,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k441 : optimized 9 0 sk441 = false := certified_fast (by decide +kernel)
private def sk442 : List W := [q294,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k442 : optimized 9 0 sk442 = false := certified_fast (by decide +kernel)
private def sk443 : List W := [q295,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k443 : optimized 9 0 sk443 = false := certified_fast (by decide +kernel)
private def sk444 : List W := [q296,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k444 : optimized 9 0 sk444 = false := certified_fast (by decide +kernel)
private def sk445 : List W := [q297,q335,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k445 : optimized 9 0 sk445 = false := certified_fast (by decide +kernel)
private def sk446 : List W := [q297,q346,q100,q451,q208,q242,q478,q277,q519,q541]
private theorem k446 : optimized 9 0 sk446 = false := certified_fast (by decide +kernel)
private def sk447 : List W := [q297,q346,q157,q451,q208,q242,q478,q277,q519,q541]
private theorem k447 : optimized 9 0 sk447 = false := certified_fast (by decide +kernel)
private def sk448 : List W := [q297,q346,q335,q451,q208,q242,q478,q277,q519,q541]
private theorem k448 : optimized 9 0 sk448 = false := certified_fast (by decide +kernel)
private def sk449 : List W := [q297,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k449 : optimized 9 0 sk449 = false := certified_fast (by decide +kernel)
private def sk450 : List W := [q297,q430,q100,q451,q208,q242,q478,q277,q519,q541]
private theorem k450 : optimized 9 0 sk450 = false := certified_fast (by decide +kernel)
private def sk451 : List W := [q297,q430,q436,q451,q208,q242,q478,q277,q519,q541]
private theorem k451 : optimized 9 0 sk451 = false := certified_fast (by decide +kernel)
private def sk452 : List W := [q297,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k452 : optimized 9 0 sk452 = false := certified_fast (by decide +kernel)
private def sk453 : List W := [q297,q430,q495,q451,q208,q242,q478,q277,q519,q541]
private theorem k453 : optimized 9 0 sk453 = false := certified_fast (by decide +kernel)
private def sk454 : List W := [q297,q436,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k454 : optimized 9 0 sk454 = false := certified_fast (by decide +kernel)
private def sk455 : List W := [q298,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k455 : optimized 9 0 sk455 = false := certified_fast (by decide +kernel)
private def sk456 : List W := [q299,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k456 : optimized 9 0 sk456 = false := certified_fast (by decide +kernel)
private def sk457 : List W := [q300,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k457 : optimized 9 0 sk457 = false := certified_fast (by decide +kernel)
private def sk458 : List W := [q301,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k458 : optimized 9 0 sk458 = false := certified_fast (by decide +kernel)
private def sk459 : List W := [q302,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k459 : optimized 9 0 sk459 = false := certified_fast (by decide +kernel)
private def sk460 : List W := [q303,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k460 : optimized 9 0 sk460 = false := certified_fast (by decide +kernel)
private def sk461 : List W := [q304,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k461 : optimized 9 0 sk461 = false := certified_fast (by decide +kernel)
private def sk462 : List W := [q305,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k462 : optimized 9 0 sk462 = false := certified_fast (by decide +kernel)
private def sk463 : List W := [q306,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k463 : optimized 9 0 sk463 = false := certified_fast (by decide +kernel)
private def sk464 : List W := [q307,q328,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k464 : optimized 9 0 sk464 = false := certified_fast (by decide +kernel)
private def sk465 : List W := [q307,q346,q328,q430,q451,q208,q242,q277,q519,q541]
private theorem k465 : optimized 9 0 sk465 = false := certified_fast (by decide +kernel)
private def sk466 : List W := [q307,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k466 : optimized 9 0 sk466 = false := certified_fast (by decide +kernel)
private def sk467 : List W := [q307,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k467 : optimized 9 0 sk467 = false := certified_fast (by decide +kernel)
private def sk468 : List W := [q307,q478,q495,q430,q451,q208,q242,q277,q519,q541]
private theorem k468 : optimized 9 0 sk468 = false := certified_fast (by decide +kernel)
private def sk469 : List W := [q307,q495,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k469 : optimized 9 0 sk469 = false := certified_fast (by decide +kernel)
private def sk470 : List W := [q308,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k470 : optimized 9 0 sk470 = false := certified_fast (by decide +kernel)
private def sk471 : List W := [q309,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k471 : optimized 9 0 sk471 = false := certified_fast (by decide +kernel)
private def sk472 : List W := [q310,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k472 : optimized 9 0 sk472 = false := certified_fast (by decide +kernel)
private def sk473 : List W := [q311,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k473 : optimized 9 0 sk473 = false := certified_fast (by decide +kernel)
private def sk474 : List W := [q312,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k474 : optimized 9 0 sk474 = false := certified_fast (by decide +kernel)
private def sk475 : List W := [q313,q541,q297,q430,q451,q208,q242,q478,q277,q519]
private theorem k475 : optimized 9 0 sk475 = false := certified_fast (by decide +kernel)
private def sk476 : List W := [q313,q541,q335,q430,q451,q208,q242,q478,q277,q519]
private theorem k476 : optimized 9 0 sk476 = false := certified_fast (by decide +kernel)
private def sk477 : List W := [q314,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k477 : optimized 9 0 sk477 = false := certified_fast (by decide +kernel)
private def sk478 : List W := [q315,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k478 : optimized 9 0 sk478 = false := certified_fast (by decide +kernel)
private def sk479 : List W := [q316,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k479 : optimized 9 0 sk479 = false := certified_fast (by decide +kernel)
private def sk480 : List W := [q317,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k480 : optimized 9 0 sk480 = false := certified_fast (by decide +kernel)
private def sk481 : List W := [q318,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k481 : optimized 9 0 sk481 = false := certified_fast (by decide +kernel)
private def sk482 : List W := [q319,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k482 : optimized 9 0 sk482 = false := certified_fast (by decide +kernel)
private def sk483 : List W := [q319,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k483 : optimized 9 0 sk483 = false := certified_fast (by decide +kernel)
private def sk484 : List W := [q320,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k484 : optimized 9 0 sk484 = false := certified_fast (by decide +kernel)
private def sk485 : List W := [q321,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k485 : optimized 9 0 sk485 = false := certified_fast (by decide +kernel)
private def sk486 : List W := [q322,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k486 : optimized 9 0 sk486 = false := certified_fast (by decide +kernel)
private def sk487 : List W := [q323,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k487 : optimized 9 0 sk487 = false := certified_fast (by decide +kernel)
private def sk488 : List W := [q324,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k488 : optimized 9 0 sk488 = false := certified_fast (by decide +kernel)
private def sk489 : List W := [q325,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k489 : optimized 9 0 sk489 = false := certified_fast (by decide +kernel)
private def sk490 : List W := [q326,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k490 : optimized 9 0 sk490 = false := certified_fast (by decide +kernel)
private def sk491 : List W := [q327,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k491 : optimized 9 0 sk491 = false := certified_fast (by decide +kernel)
private def sk492 : List W := [q327,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k492 : optimized 9 0 sk492 = false := certified_fast (by decide +kernel)
private def sk493 : List W := [q327,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k493 : optimized 9 0 sk493 = false := certified_fast (by decide +kernel)
private def sk494 : List W := [q328,q307,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k494 : optimized 9 0 sk494 = false := certified_fast (by decide +kernel)
private def sk495 : List W := [q328,q346,q307,q430,q451,q208,q242,q277,q519,q541]
private theorem k495 : optimized 9 0 sk495 = false := certified_fast (by decide +kernel)
private def sk496 : List W := [q328,q346,q495,q430,q451,q208,q242,q277,q519,q541]
private theorem k496 : optimized 9 0 sk496 = false := certified_fast (by decide +kernel)
private def sk497 : List W := [q328,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k497 : optimized 9 0 sk497 = false := certified_fast (by decide +kernel)
private def sk498 : List W := [q328,q478,q495,q430,q451,q208,q242,q277,q519,q541]
private theorem k498 : optimized 9 0 sk498 = false := certified_fast (by decide +kernel)
private def sk499 : List W := [q329,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k499 : optimized 9 0 sk499 = false := certified_fast (by decide +kernel)
private def sk500 : List W := [q330,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k500 : optimized 9 0 sk500 = false := certified_fast (by decide +kernel)
private def sk501 : List W := [q331,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k501 : optimized 9 0 sk501 = false := certified_fast (by decide +kernel)
private def sk502 : List W := [q331,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k502 : optimized 9 0 sk502 = false := certified_fast (by decide +kernel)
private def sk503 : List W := [q332,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k503 : optimized 9 0 sk503 = false := certified_fast (by decide +kernel)
private def sk504 : List W := [q333,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k504 : optimized 9 0 sk504 = false := certified_fast (by decide +kernel)
private def sk505 : List W := [q334,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k505 : optimized 9 0 sk505 = false := certified_fast (by decide +kernel)
private def sk506 : List W := [q334,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k506 : optimized 9 0 sk506 = false := certified_fast (by decide +kernel)
private def sk507 : List W := [q335,q100,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k507 : optimized 9 0 sk507 = false := certified_fast (by decide +kernel)
private def sk508 : List W := [q335,q297,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k508 : optimized 9 0 sk508 = false := certified_fast (by decide +kernel)
private def sk509 : List W := [q335,q346,q297,q451,q208,q242,q478,q277,q519,q541]
private theorem k509 : optimized 9 0 sk509 = false := certified_fast (by decide +kernel)
private def sk510 : List W := [q335,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k510 : optimized 9 0 sk510 = false := certified_fast (by decide +kernel)
private def sk511 : List W := [q335,q346,q436,q451,q208,q242,q478,q277,q519,q541]
private theorem k511 : optimized 9 0 sk511 = false := certified_fast (by decide +kernel)
private def sk512 : List W := [q335,q430,q100,q451,q208,q242,q478,q277,q519,q541]
private theorem k512 : optimized 9 0 sk512 = false := certified_fast (by decide +kernel)
private def sk513 : List W := [q335,q430,q436,q451,q208,q242,q478,q277,q519,q541]
private theorem k513 : optimized 9 0 sk513 = false := certified_fast (by decide +kernel)
private def sk514 : List W := [q335,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k514 : optimized 9 0 sk514 = false := certified_fast (by decide +kernel)
private def sk515 : List W := [q335,q430,q495,q451,q208,q242,q478,q277,q519,q541]
private theorem k515 : optimized 9 0 sk515 = false := certified_fast (by decide +kernel)
private def sk516 : List W := [q336,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k516 : optimized 9 0 sk516 = false := certified_fast (by decide +kernel)
private def sk517 : List W := [q337,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k517 : optimized 9 0 sk517 = false := certified_fast (by decide +kernel)
private def sk518 : List W := [q338,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k518 : optimized 9 0 sk518 = false := certified_fast (by decide +kernel)
private def sk519 : List W := [q339,q541,q297,q430,q451,q208,q242,q478,q277,q519]
private theorem k519 : optimized 9 0 sk519 = false := certified_fast (by decide +kernel)
private def sk520 : List W := [q339,q541,q335,q430,q451,q208,q242,q478,q277,q519]
private theorem k520 : optimized 9 0 sk520 = false := certified_fast (by decide +kernel)
private def sk521 : List W := [q340,q277,q297,q430,q451,q208,q242,q478,q519,q541]
private theorem k521 : optimized 9 0 sk521 = false := certified_fast (by decide +kernel)
private def sk522 : List W := [q340,q277,q335,q430,q451,q208,q242,q478,q519,q541]
private theorem k522 : optimized 9 0 sk522 = false := certified_fast (by decide +kernel)
private def sk523 : List W := [q341,q242,q297,q430,q451,q208,q478,q277,q519,q541]
private theorem k523 : optimized 9 0 sk523 = false := certified_fast (by decide +kernel)
private def sk524 : List W := [q341,q242,q335,q430,q451,q208,q478,q277,q519,q541]
private theorem k524 : optimized 9 0 sk524 = false := certified_fast (by decide +kernel)
private def sk525 : List W := [q341,q242,q495,q430,q451,q208,q478,q277,q519,q541]
private theorem k525 : optimized 9 0 sk525 = false := certified_fast (by decide +kernel)
private def sk526 : List W := [q342,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k526 : optimized 9 0 sk526 = false := certified_fast (by decide +kernel)
private def sk527 : List W := [q343,q177,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k527 : optimized 9 0 sk527 = false := certified_fast (by decide +kernel)
private def sk528 : List W := [q343,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k528 : optimized 9 0 sk528 = false := certified_fast (by decide +kernel)
private def sk529 : List W := [q344,q85,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k529 : optimized 9 0 sk529 = false := certified_fast (by decide +kernel)
private def sk530 : List W := [q344,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k530 : optimized 9 0 sk530 = false := certified_fast (by decide +kernel)
private def sk531 : List W := [q345,q169,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k531 : optimized 9 0 sk531 = false := certified_fast (by decide +kernel)
private def sk532 : List W := [q345,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k532 : optimized 9 0 sk532 = false := certified_fast (by decide +kernel)
private def sk533 : List W := [q347,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k533 : optimized 9 0 sk533 = false := certified_fast (by decide +kernel)
private def sk534 : List W := [q348,q85,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k534 : optimized 9 0 sk534 = false := certified_fast (by decide +kernel)
private def sk535 : List W := [q348,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k535 : optimized 9 0 sk535 = false := certified_fast (by decide +kernel)
private def sk536 : List W := [q349,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k536 : optimized 9 0 sk536 = false := certified_fast (by decide +kernel)
private def sk537 : List W := [q350,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k537 : optimized 9 0 sk537 = false := certified_fast (by decide +kernel)
private def sk538 : List W := [q351,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k538 : optimized 9 0 sk538 = false := certified_fast (by decide +kernel)
private def sk539 : List W := [q352,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k539 : optimized 9 0 sk539 = false := certified_fast (by decide +kernel)
private def sk540 : List W := [q353,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k540 : optimized 9 0 sk540 = false := certified_fast (by decide +kernel)
private def sk541 : List W := [q354,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k541 : optimized 9 0 sk541 = false := certified_fast (by decide +kernel)
private def sk542 : List W := [q355,q169,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k542 : optimized 9 0 sk542 = false := certified_fast (by decide +kernel)
private def sk543 : List W := [q355,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k543 : optimized 9 0 sk543 = false := certified_fast (by decide +kernel)
private def sk544 : List W := [q356,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k544 : optimized 9 0 sk544 = false := certified_fast (by decide +kernel)
private def sk545 : List W := [q357,q177,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k545 : optimized 9 0 sk545 = false := certified_fast (by decide +kernel)
private def sk546 : List W := [q357,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k546 : optimized 9 0 sk546 = false := certified_fast (by decide +kernel)
private def sk547 : List W := [q358,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k547 : optimized 9 0 sk547 = false := certified_fast (by decide +kernel)
private def sk548 : List W := [q359,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k548 : optimized 9 0 sk548 = false := certified_fast (by decide +kernel)
private def sk549 : List W := [q360,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k549 : optimized 9 0 sk549 = false := certified_fast (by decide +kernel)
private def sk550 : List W := [q361,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k550 : optimized 9 0 sk550 = false := certified_fast (by decide +kernel)
private def sk551 : List W := [q362,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k551 : optimized 9 0 sk551 = false := certified_fast (by decide +kernel)
private def sk552 : List W := [q363,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k552 : optimized 9 0 sk552 = false := certified_fast (by decide +kernel)
private def sk553 : List W := [q364,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k553 : optimized 9 0 sk553 = false := certified_fast (by decide +kernel)
private def sk554 : List W := [q365,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k554 : optimized 9 0 sk554 = false := certified_fast (by decide +kernel)
private def sk555 : List W := [q366,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k555 : optimized 9 0 sk555 = false := certified_fast (by decide +kernel)
private def sk556 : List W := [q367,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k556 : optimized 9 0 sk556 = false := certified_fast (by decide +kernel)
private def sk557 : List W := [q368,q242,q297,q430,q451,q208,q478,q277,q519,q541]
private theorem k557 : optimized 9 0 sk557 = false := certified_fast (by decide +kernel)
private def sk558 : List W := [q368,q242,q335,q430,q451,q208,q478,q277,q519,q541]
private theorem k558 : optimized 9 0 sk558 = false := certified_fast (by decide +kernel)
private def sk559 : List W := [q368,q242,q495,q430,q451,q208,q478,q277,q519,q541]
private theorem k559 : optimized 9 0 sk559 = false := certified_fast (by decide +kernel)
private def sk560 : List W := [q369,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k560 : optimized 9 0 sk560 = false := certified_fast (by decide +kernel)
private def sk561 : List W := [q370,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k561 : optimized 9 0 sk561 = false := certified_fast (by decide +kernel)
private def sk562 : List W := [q371,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k562 : optimized 9 0 sk562 = false := certified_fast (by decide +kernel)
private def sk563 : List W := [q372,q277,q157,q430,q208,q242,q478,q346,q519,q541]
private theorem k563 : optimized 9 0 sk563 = false := certified_fast (by decide +kernel)
private def sk564 : List W := [q372,q277,q414,q430,q208,q242,q478,q346,q519,q541]
private theorem k564 : optimized 9 0 sk564 = false := certified_fast (by decide +kernel)
private def sk565 : List W := [q373,q277,q133,q430,q451,q208,q242,q346,q519,q541]
private theorem k565 : optimized 9 0 sk565 = false := certified_fast (by decide +kernel)
private def sk566 : List W := [q373,q277,q423,q430,q451,q208,q242,q346,q519,q541]
private theorem k566 : optimized 9 0 sk566 = false := certified_fast (by decide +kernel)
private def sk567 : List W := [q374,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k567 : optimized 9 0 sk567 = false := certified_fast (by decide +kernel)
private def sk568 : List W := [q375,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k568 : optimized 9 0 sk568 = false := certified_fast (by decide +kernel)
private def sk569 : List W := [q376,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k569 : optimized 9 0 sk569 = false := certified_fast (by decide +kernel)
private def sk570 : List W := [q377,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k570 : optimized 9 0 sk570 = false := certified_fast (by decide +kernel)
private def sk571 : List W := [q377,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k571 : optimized 9 0 sk571 = false := certified_fast (by decide +kernel)
private def sk572 : List W := [q378,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k572 : optimized 9 0 sk572 = false := certified_fast (by decide +kernel)
private def sk573 : List W := [q379,q277,q297,q430,q451,q208,q242,q478,q519,q541]
private theorem k573 : optimized 9 0 sk573 = false := certified_fast (by decide +kernel)
private def sk574 : List W := [q379,q277,q335,q430,q451,q208,q242,q478,q519,q541]
private theorem k574 : optimized 9 0 sk574 = false := certified_fast (by decide +kernel)
private def sk575 : List W := [q380,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k575 : optimized 9 0 sk575 = false := certified_fast (by decide +kernel)
private def sk576 : List W := [q380,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k576 : optimized 9 0 sk576 = false := certified_fast (by decide +kernel)
private def sk577 : List W := [q381,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k577 : optimized 9 0 sk577 = false := certified_fast (by decide +kernel)
private def sk578 : List W := [q381,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k578 : optimized 9 0 sk578 = false := certified_fast (by decide +kernel)
private def sk579 : List W := [q382,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k579 : optimized 9 0 sk579 = false := certified_fast (by decide +kernel)
private def sk580 : List W := [q383,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k580 : optimized 9 0 sk580 = false := certified_fast (by decide +kernel)
private def sk581 : List W := [q384,q231,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k581 : optimized 9 0 sk581 = false := certified_fast (by decide +kernel)
private def sk582 : List W := [q384,q242,q85,q451,q208,q478,q277,q346,q519,q541]
private theorem k582 : optimized 9 0 sk582 = false := certified_fast (by decide +kernel)
private def sk583 : List W := [q384,q242,q133,q451,q208,q478,q277,q346,q519,q541]
private theorem k583 : optimized 9 0 sk583 = false := certified_fast (by decide +kernel)
private def sk584 : List W := [q384,q242,q231,q451,q208,q478,q277,q346,q519,q541]
private theorem k584 : optimized 9 0 sk584 = false := certified_fast (by decide +kernel)
private def sk585 : List W := [q384,q242,q399,q451,q208,q478,q277,q346,q519,q541]
private theorem k585 : optimized 9 0 sk585 = false := certified_fast (by decide +kernel)
private def sk586 : List W := [q384,q242,q505,q451,q208,q478,q277,q346,q519,q541]
private theorem k586 : optimized 9 0 sk586 = false := certified_fast (by decide +kernel)
private def sk587 : List W := [q384,q430,q85,q451,q208,q478,q277,q346,q519,q541]
private theorem k587 : optimized 9 0 sk587 = false := certified_fast (by decide +kernel)
private def sk588 : List W := [q384,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k588 : optimized 9 0 sk588 = false := certified_fast (by decide +kernel)
private def sk589 : List W := [q385,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k589 : optimized 9 0 sk589 = false := certified_fast (by decide +kernel)
private def sk590 : List W := [q386,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k590 : optimized 9 0 sk590 = false := certified_fast (by decide +kernel)
private def sk591 : List W := [q387,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k591 : optimized 9 0 sk591 = false := certified_fast (by decide +kernel)
private def sk592 : List W := [q388,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k592 : optimized 9 0 sk592 = false := certified_fast (by decide +kernel)
private def sk593 : List W := [q389,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k593 : optimized 9 0 sk593 = false := certified_fast (by decide +kernel)
private def sk594 : List W := [q390,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k594 : optimized 9 0 sk594 = false := certified_fast (by decide +kernel)
private def sk595 : List W := [q391,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k595 : optimized 9 0 sk595 = false := certified_fast (by decide +kernel)
private def sk596 : List W := [q392,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k596 : optimized 9 0 sk596 = false := certified_fast (by decide +kernel)
private def sk597 : List W := [q393,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k597 : optimized 9 0 sk597 = false := certified_fast (by decide +kernel)
private def sk598 : List W := [q394,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k598 : optimized 9 0 sk598 = false := certified_fast (by decide +kernel)
private def sk599 : List W := [q395,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k599 : optimized 9 0 sk599 = false := certified_fast (by decide +kernel)
private def sk600 : List W := [q395,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k600 : optimized 9 0 sk600 = false := certified_fast (by decide +kernel)
private def sk601 : List W := [q396,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k601 : optimized 9 0 sk601 = false := certified_fast (by decide +kernel)
private def sk602 : List W := [q396,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k602 : optimized 9 0 sk602 = false := certified_fast (by decide +kernel)
private def sk603 : List W := [q397,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k603 : optimized 9 0 sk603 = false := certified_fast (by decide +kernel)
private def sk604 : List W := [q398,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k604 : optimized 9 0 sk604 = false := certified_fast (by decide +kernel)
private def sk605 : List W := [q399,q197,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k605 : optimized 9 0 sk605 = false := certified_fast (by decide +kernel)
private def sk606 : List W := [q399,q208,q75,q451,q242,q478,q277,q346,q519,q541]
private theorem k606 : optimized 9 0 sk606 = false := certified_fast (by decide +kernel)
private def sk607 : List W := [q399,q208,q157,q451,q242,q478,q277,q346,q519,q541]
private theorem k607 : optimized 9 0 sk607 = false := certified_fast (by decide +kernel)
private def sk608 : List W := [q399,q208,q197,q451,q242,q478,q277,q346,q519,q541]
private theorem k608 : optimized 9 0 sk608 = false := certified_fast (by decide +kernel)
private def sk609 : List W := [q399,q208,q384,q451,q242,q478,q277,q346,q519,q541]
private theorem k609 : optimized 9 0 sk609 = false := certified_fast (by decide +kernel)
private def sk610 : List W := [q399,q430,q75,q451,q242,q478,q277,q346,q519,q541]
private theorem k610 : optimized 9 0 sk610 = false := certified_fast (by decide +kernel)
private def sk611 : List W := [q399,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k611 : optimized 9 0 sk611 = false := certified_fast (by decide +kernel)
private def sk612 : List W := [q400,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k612 : optimized 9 0 sk612 = false := certified_fast (by decide +kernel)
private def sk613 : List W := [q401,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k613 : optimized 9 0 sk613 = false := certified_fast (by decide +kernel)
private def sk614 : List W := [q402,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k614 : optimized 9 0 sk614 = false := certified_fast (by decide +kernel)
private def sk615 : List W := [q403,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k615 : optimized 9 0 sk615 = false := certified_fast (by decide +kernel)
private def sk616 : List W := [q404,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k616 : optimized 9 0 sk616 = false := certified_fast (by decide +kernel)
private def sk617 : List W := [q405,q208,q177,q430,q451,q242,q277,q346,q519,q541]
private theorem k617 : optimized 9 0 sk617 = false := certified_fast (by decide +kernel)
private def sk618 : List W := [q405,q208,q505,q430,q451,q242,q277,q346,q519,q541]
private theorem k618 : optimized 9 0 sk618 = false := certified_fast (by decide +kernel)
private def sk619 : List W := [q406,q197,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k619 : optimized 9 0 sk619 = false := certified_fast (by decide +kernel)
private def sk620 : List W := [q406,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k620 : optimized 9 0 sk620 = false := certified_fast (by decide +kernel)
private def sk621 : List W := [q407,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k621 : optimized 9 0 sk621 = false := certified_fast (by decide +kernel)
private def sk622 : List W := [q408,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k622 : optimized 9 0 sk622 = false := certified_fast (by decide +kernel)
private def sk623 : List W := [q409,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k623 : optimized 9 0 sk623 = false := certified_fast (by decide +kernel)
private def sk624 : List W := [q410,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k624 : optimized 9 0 sk624 = false := certified_fast (by decide +kernel)
private def sk625 : List W := [q411,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k625 : optimized 9 0 sk625 = false := certified_fast (by decide +kernel)
private def sk626 : List W := [q411,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k626 : optimized 9 0 sk626 = false := certified_fast (by decide +kernel)
private def sk627 : List W := [q412,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k627 : optimized 9 0 sk627 = false := certified_fast (by decide +kernel)
private def sk628 : List W := [q413,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k628 : optimized 9 0 sk628 = false := certified_fast (by decide +kernel)
private def sk629 : List W := [q414,q157,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k629 : optimized 9 0 sk629 = false := certified_fast (by decide +kernel)
private def sk630 : List W := [q414,q169,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k630 : optimized 9 0 sk630 = false := certified_fast (by decide +kernel)
private def sk631 : List W := [q414,q430,q169,q208,q242,q478,q277,q346,q519,q541]
private theorem k631 : optimized 9 0 sk631 = false := certified_fast (by decide +kernel)
private def sk632 : List W := [q414,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k632 : optimized 9 0 sk632 = false := certified_fast (by decide +kernel)
private def sk633 : List W := [q414,q451,q157,q208,q242,q478,q277,q346,q519,q541]
private theorem k633 : optimized 9 0 sk633 = false := certified_fast (by decide +kernel)
private def sk634 : List W := [q414,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k634 : optimized 9 0 sk634 = false := certified_fast (by decide +kernel)
private def sk635 : List W := [q415,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k635 : optimized 9 0 sk635 = false := certified_fast (by decide +kernel)
private def sk636 : List W := [q416,q177,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k636 : optimized 9 0 sk636 = false := certified_fast (by decide +kernel)
private def sk637 : List W := [q416,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k637 : optimized 9 0 sk637 = false := certified_fast (by decide +kernel)
private def sk638 : List W := [q417,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k638 : optimized 9 0 sk638 = false := certified_fast (by decide +kernel)
private def sk639 : List W := [q418,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k639 : optimized 9 0 sk639 = false := certified_fast (by decide +kernel)
private def sk640 : List W := [q419,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k640 : optimized 9 0 sk640 = false := certified_fast (by decide +kernel)
private def sk641 : List W := [q420,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k641 : optimized 9 0 sk641 = false := certified_fast (by decide +kernel)
private def sk642 : List W := [q421,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k642 : optimized 9 0 sk642 = false := certified_fast (by decide +kernel)
private def sk643 : List W := [q422,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k643 : optimized 9 0 sk643 = false := certified_fast (by decide +kernel)
private def sk644 : List W := [q423,q133,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k644 : optimized 9 0 sk644 = false := certified_fast (by decide +kernel)
private def sk645 : List W := [q423,q177,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k645 : optimized 9 0 sk645 = false := certified_fast (by decide +kernel)
private def sk646 : List W := [q423,q430,q177,q451,q208,q242,q277,q346,q519,q541]
private theorem k646 : optimized 9 0 sk646 = false := certified_fast (by decide +kernel)
private def sk647 : List W := [q423,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k647 : optimized 9 0 sk647 = false := certified_fast (by decide +kernel)
private def sk648 : List W := [q423,q430,q505,q451,q208,q242,q277,q346,q519,q541]
private theorem k648 : optimized 9 0 sk648 = false := certified_fast (by decide +kernel)
private def sk649 : List W := [q423,q478,q133,q451,q208,q242,q277,q346,q519,q541]
private theorem k649 : optimized 9 0 sk649 = false := certified_fast (by decide +kernel)
private def sk650 : List W := [q423,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k650 : optimized 9 0 sk650 = false := certified_fast (by decide +kernel)
private def sk651 : List W := [q423,q478,q505,q451,q208,q242,q277,q346,q519,q541]
private theorem k651 : optimized 9 0 sk651 = false := certified_fast (by decide +kernel)
private def sk652 : List W := [q424,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k652 : optimized 9 0 sk652 = false := certified_fast (by decide +kernel)
private def sk653 : List W := [q425,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k653 : optimized 9 0 sk653 = false := certified_fast (by decide +kernel)
private def sk654 : List W := [q426,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k654 : optimized 9 0 sk654 = false := certified_fast (by decide +kernel)
private def sk655 : List W := [q427,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k655 : optimized 9 0 sk655 = false := certified_fast (by decide +kernel)
private def sk656 : List W := [q428,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k656 : optimized 9 0 sk656 = false := certified_fast (by decide +kernel)
private def sk657 : List W := [q429,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k657 : optimized 9 0 sk657 = false := certified_fast (by decide +kernel)
private def sk658 : List W := [q431,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k658 : optimized 9 0 sk658 = false := certified_fast (by decide +kernel)
private def sk659 : List W := [q432,q75,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k659 : optimized 9 0 sk659 = false := certified_fast (by decide +kernel)
private def sk660 : List W := [q432,q208,q75,q451,q242,q478,q277,q346,q519,q541]
private theorem k660 : optimized 9 0 sk660 = false := certified_fast (by decide +kernel)
private def sk661 : List W := [q432,q208,q157,q451,q242,q478,q277,q346,q519,q541]
private theorem k661 : optimized 9 0 sk661 = false := certified_fast (by decide +kernel)
private def sk662 : List W := [q432,q208,q197,q451,q242,q478,q277,q346,q519,q541]
private theorem k662 : optimized 9 0 sk662 = false := certified_fast (by decide +kernel)
private def sk663 : List W := [q432,q208,q384,q451,q242,q478,q277,q346,q519,q541]
private theorem k663 : optimized 9 0 sk663 = false := certified_fast (by decide +kernel)
private def sk664 : List W := [q432,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k664 : optimized 9 0 sk664 = false := certified_fast (by decide +kernel)
private def sk665 : List W := [q432,q399,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k665 : optimized 9 0 sk665 = false := certified_fast (by decide +kernel)
private def sk666 : List W := [q432,q430,q197,q451,q242,q478,q277,q346,q519,q541]
private theorem k666 : optimized 9 0 sk666 = false := certified_fast (by decide +kernel)
private def sk667 : List W := [q432,q430,q399,q451,q242,q478,q277,q346,q519,q541]
private theorem k667 : optimized 9 0 sk667 = false := certified_fast (by decide +kernel)
private def sk668 : List W := [q432,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k668 : optimized 9 0 sk668 = false := certified_fast (by decide +kernel)
private def sk669 : List W := [q433,q85,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k669 : optimized 9 0 sk669 = false := certified_fast (by decide +kernel)
private def sk670 : List W := [q433,q242,q85,q451,q208,q478,q277,q346,q519,q541]
private theorem k670 : optimized 9 0 sk670 = false := certified_fast (by decide +kernel)
private def sk671 : List W := [q433,q242,q133,q451,q208,q478,q277,q346,q519,q541]
private theorem k671 : optimized 9 0 sk671 = false := certified_fast (by decide +kernel)
private def sk672 : List W := [q433,q242,q231,q451,q208,q478,q277,q346,q519,q541]
private theorem k672 : optimized 9 0 sk672 = false := certified_fast (by decide +kernel)
private def sk673 : List W := [q433,q242,q399,q451,q208,q478,q277,q346,q519,q541]
private theorem k673 : optimized 9 0 sk673 = false := certified_fast (by decide +kernel)
private def sk674 : List W := [q433,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k674 : optimized 9 0 sk674 = false := certified_fast (by decide +kernel)
private def sk675 : List W := [q433,q242,q505,q451,q208,q478,q277,q346,q519,q541]
private theorem k675 : optimized 9 0 sk675 = false := certified_fast (by decide +kernel)
private def sk676 : List W := [q433,q384,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k676 : optimized 9 0 sk676 = false := certified_fast (by decide +kernel)
private def sk677 : List W := [q433,q430,q231,q451,q208,q478,q277,q346,q519,q541]
private theorem k677 : optimized 9 0 sk677 = false := certified_fast (by decide +kernel)
private def sk678 : List W := [q433,q430,q384,q451,q208,q478,q277,q346,q519,q541]
private theorem k678 : optimized 9 0 sk678 = false := certified_fast (by decide +kernel)
private def sk679 : List W := [q433,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k679 : optimized 9 0 sk679 = false := certified_fast (by decide +kernel)
private def sk680 : List W := [q434,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k680 : optimized 9 0 sk680 = false := certified_fast (by decide +kernel)
private def sk681 : List W := [q435,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k681 : optimized 9 0 sk681 = false := certified_fast (by decide +kernel)
private def sk682 : List W := [q436,q100,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k682 : optimized 9 0 sk682 = false := certified_fast (by decide +kernel)
private def sk683 : List W := [q436,q297,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k683 : optimized 9 0 sk683 = false := certified_fast (by decide +kernel)
private def sk684 : List W := [q436,q346,q100,q451,q208,q242,q478,q277,q519,q541]
private theorem k684 : optimized 9 0 sk684 = false := certified_fast (by decide +kernel)
private def sk685 : List W := [q436,q346,q157,q451,q208,q242,q478,q277,q519,q541]
private theorem k685 : optimized 9 0 sk685 = false := certified_fast (by decide +kernel)
private def sk686 : List W := [q436,q346,q335,q451,q208,q242,q478,q277,q519,q541]
private theorem k686 : optimized 9 0 sk686 = false := certified_fast (by decide +kernel)
private def sk687 : List W := [q436,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k687 : optimized 9 0 sk687 = false := certified_fast (by decide +kernel)
private def sk688 : List W := [q436,q430,q297,q451,q208,q242,q478,q277,q519,q541]
private theorem k688 : optimized 9 0 sk688 = false := certified_fast (by decide +kernel)
private def sk689 : List W := [q436,q430,q335,q451,q208,q242,q478,q277,q519,q541]
private theorem k689 : optimized 9 0 sk689 = false := certified_fast (by decide +kernel)
private def sk690 : List W := [q436,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k690 : optimized 9 0 sk690 = false := certified_fast (by decide +kernel)
private def sk691 : List W := [q437,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k691 : optimized 9 0 sk691 = false := certified_fast (by decide +kernel)
private def sk692 : List W := [q438,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k692 : optimized 9 0 sk692 = false := certified_fast (by decide +kernel)
private def sk693 : List W := [q439,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k693 : optimized 9 0 sk693 = false := certified_fast (by decide +kernel)
private def sk694 : List W := [q440,q177,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k694 : optimized 9 0 sk694 = false := certified_fast (by decide +kernel)
private def sk695 : List W := [q440,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k695 : optimized 9 0 sk695 = false := certified_fast (by decide +kernel)
private def sk696 : List W := [q441,q177,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k696 : optimized 9 0 sk696 = false := certified_fast (by decide +kernel)
private def sk697 : List W := [q441,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k697 : optimized 9 0 sk697 = false := certified_fast (by decide +kernel)
private def sk698 : List W := [q442,q169,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k698 : optimized 9 0 sk698 = false := certified_fast (by decide +kernel)
private def sk699 : List W := [q442,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k699 : optimized 9 0 sk699 = false := certified_fast (by decide +kernel)
private def sk700 : List W := [q443,q169,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k700 : optimized 9 0 sk700 = false := certified_fast (by decide +kernel)
private def sk701 : List W := [q443,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k701 : optimized 9 0 sk701 = false := certified_fast (by decide +kernel)
private def sk702 : List W := [q444,q169,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k702 : optimized 9 0 sk702 = false := certified_fast (by decide +kernel)
private def sk703 : List W := [q444,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k703 : optimized 9 0 sk703 = false := certified_fast (by decide +kernel)
private def sk704 : List W := [q445,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k704 : optimized 9 0 sk704 = false := certified_fast (by decide +kernel)
private def sk705 : List W := [q446,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k705 : optimized 9 0 sk705 = false := certified_fast (by decide +kernel)
private def sk706 : List W := [q447,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k706 : optimized 9 0 sk706 = false := certified_fast (by decide +kernel)
private def sk707 : List W := [q448,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k707 : optimized 9 0 sk707 = false := certified_fast (by decide +kernel)
private def sk708 : List W := [q449,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k708 : optimized 9 0 sk708 = false := certified_fast (by decide +kernel)
private def sk709 : List W := [q450,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k709 : optimized 9 0 sk709 = false := certified_fast (by decide +kernel)
private def sk710 : List W := [q452,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k710 : optimized 9 0 sk710 = false := certified_fast (by decide +kernel)
private def sk711 : List W := [q453,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k711 : optimized 9 0 sk711 = false := certified_fast (by decide +kernel)
private def sk712 : List W := [q454,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k712 : optimized 9 0 sk712 = false := certified_fast (by decide +kernel)
private def sk713 : List W := [q455,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k713 : optimized 9 0 sk713 = false := certified_fast (by decide +kernel)
private def sk714 : List W := [q456,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k714 : optimized 9 0 sk714 = false := certified_fast (by decide +kernel)
private def sk715 : List W := [q457,q177,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k715 : optimized 9 0 sk715 = false := certified_fast (by decide +kernel)
private def sk716 : List W := [q457,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k716 : optimized 9 0 sk716 = false := certified_fast (by decide +kernel)
private def sk717 : List W := [q458,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k717 : optimized 9 0 sk717 = false := certified_fast (by decide +kernel)
private def sk718 : List W := [q459,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k718 : optimized 9 0 sk718 = false := certified_fast (by decide +kernel)
private def sk719 : List W := [q460,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k719 : optimized 9 0 sk719 = false := certified_fast (by decide +kernel)
private def sk720 : List W := [q461,q451,q197,q430,q242,q478,q277,q346,q519,q541]
private theorem k720 : optimized 9 0 sk720 = false := certified_fast (by decide +kernel)
private def sk721 : List W := [q461,q451,q399,q430,q242,q478,q277,q346,q519,q541]
private theorem k721 : optimized 9 0 sk721 = false := certified_fast (by decide +kernel)
private def sk722 : List W := [q462,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k722 : optimized 9 0 sk722 = false := certified_fast (by decide +kernel)
private def sk723 : List W := [q463,q451,q231,q430,q208,q478,q277,q346,q519,q541]
private theorem k723 : optimized 9 0 sk723 = false := certified_fast (by decide +kernel)
private def sk724 : List W := [q463,q451,q384,q430,q208,q478,q277,q346,q519,q541]
private theorem k724 : optimized 9 0 sk724 = false := certified_fast (by decide +kernel)
private def sk725 : List W := [q464,q277,q157,q430,q208,q242,q478,q346,q519,q541]
private theorem k725 : optimized 9 0 sk725 = false := certified_fast (by decide +kernel)
private def sk726 : List W := [q464,q277,q414,q430,q208,q242,q478,q346,q519,q541]
private theorem k726 : optimized 9 0 sk726 = false := certified_fast (by decide +kernel)
private def sk727 : List W := [q465,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k727 : optimized 9 0 sk727 = false := certified_fast (by decide +kernel)
private def sk728 : List W := [q466,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k728 : optimized 9 0 sk728 = false := certified_fast (by decide +kernel)
private def sk729 : List W := [q467,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k729 : optimized 9 0 sk729 = false := certified_fast (by decide +kernel)
private def sk730 : List W := [q468,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k730 : optimized 9 0 sk730 = false := certified_fast (by decide +kernel)
private def sk731 : List W := [q469,q451,q297,q430,q208,q242,q478,q277,q519,q541]
private theorem k731 : optimized 9 0 sk731 = false := certified_fast (by decide +kernel)
private def sk732 : List W := [q469,q451,q335,q430,q208,q242,q478,q277,q519,q541]
private theorem k732 : optimized 9 0 sk732 = false := certified_fast (by decide +kernel)
private def sk733 : List W := [q470,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k733 : optimized 9 0 sk733 = false := certified_fast (by decide +kernel)
private def sk734 : List W := [q471,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k734 : optimized 9 0 sk734 = false := certified_fast (by decide +kernel)
private def sk735 : List W := [q472,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k735 : optimized 9 0 sk735 = false := certified_fast (by decide +kernel)
private def sk736 : List W := [q473,q157,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k736 : optimized 9 0 sk736 = false := certified_fast (by decide +kernel)
private def sk737 : List W := [q473,q169,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k737 : optimized 9 0 sk737 = false := certified_fast (by decide +kernel)
private def sk738 : List W := [q473,q430,q157,q208,q242,q478,q277,q346,q519,q541]
private theorem k738 : optimized 9 0 sk738 = false := certified_fast (by decide +kernel)
private def sk739 : List W := [q473,q430,q414,q208,q242,q478,q277,q346,q519,q541]
private theorem k739 : optimized 9 0 sk739 = false := certified_fast (by decide +kernel)
private def sk740 : List W := [q473,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k740 : optimized 9 0 sk740 = false := certified_fast (by decide +kernel)
private def sk741 : List W := [q473,q451,q169,q208,q242,q478,q277,q346,q519,q541]
private theorem k741 : optimized 9 0 sk741 = false := certified_fast (by decide +kernel)
private def sk742 : List W := [q473,q451,q297,q208,q242,q478,q277,q346,q519,q541]
private theorem k742 : optimized 9 0 sk742 = false := certified_fast (by decide +kernel)
private def sk743 : List W := [q473,q451,q399,q208,q242,q478,q277,q346,q519,q541]
private theorem k743 : optimized 9 0 sk743 = false := certified_fast (by decide +kernel)
private def sk744 : List W := [q473,q451,q414,q208,q242,q478,q277,q346,q519,q541]
private theorem k744 : optimized 9 0 sk744 = false := certified_fast (by decide +kernel)
private def sk745 : List W := [q473,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k745 : optimized 9 0 sk745 = false := certified_fast (by decide +kernel)
private def sk746 : List W := [q473,q451,q436,q208,q242,q478,q277,q346,q519,q541]
private theorem k746 : optimized 9 0 sk746 = false := certified_fast (by decide +kernel)
private def sk747 : List W := [q474,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k747 : optimized 9 0 sk747 = false := certified_fast (by decide +kernel)
private def sk748 : List W := [q475,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k748 : optimized 9 0 sk748 = false := certified_fast (by decide +kernel)
private def sk749 : List W := [q476,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k749 : optimized 9 0 sk749 = false := certified_fast (by decide +kernel)
private def sk750 : List W := [q477,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k750 : optimized 9 0 sk750 = false := certified_fast (by decide +kernel)
private def sk751 : List W := [q479,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k751 : optimized 9 0 sk751 = false := certified_fast (by decide +kernel)
private def sk752 : List W := [q480,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k752 : optimized 9 0 sk752 = false := certified_fast (by decide +kernel)
private def sk753 : List W := [q481,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k753 : optimized 9 0 sk753 = false := certified_fast (by decide +kernel)
private def sk754 : List W := [q482,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k754 : optimized 9 0 sk754 = false := certified_fast (by decide +kernel)
private def sk755 : List W := [q483,q169,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k755 : optimized 9 0 sk755 = false := certified_fast (by decide +kernel)
private def sk756 : List W := [q483,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k756 : optimized 9 0 sk756 = false := certified_fast (by decide +kernel)
private def sk757 : List W := [q484,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k757 : optimized 9 0 sk757 = false := certified_fast (by decide +kernel)
private def sk758 : List W := [q485,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k758 : optimized 9 0 sk758 = false := certified_fast (by decide +kernel)
private def sk759 : List W := [q486,q197,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k759 : optimized 9 0 sk759 = false := certified_fast (by decide +kernel)
private def sk760 : List W := [q486,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k760 : optimized 9 0 sk760 = false := certified_fast (by decide +kernel)
private def sk761 : List W := [q487,q208,q177,q430,q451,q242,q277,q346,q519,q541]
private theorem k761 : optimized 9 0 sk761 = false := certified_fast (by decide +kernel)
private def sk762 : List W := [q487,q208,q505,q430,q451,q242,q277,q346,q519,q541]
private theorem k762 : optimized 9 0 sk762 = false := certified_fast (by decide +kernel)
private def sk763 : List W := [q487,q478,q197,q430,q451,q242,q277,q346,q519,q541]
private theorem k763 : optimized 9 0 sk763 = false := certified_fast (by decide +kernel)
private def sk764 : List W := [q487,q478,q399,q430,q451,q242,q277,q346,q519,q541]
private theorem k764 : optimized 9 0 sk764 = false := certified_fast (by decide +kernel)
private def sk765 : List W := [q488,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k765 : optimized 9 0 sk765 = false := certified_fast (by decide +kernel)
private def sk766 : List W := [q489,q478,q231,q430,q451,q208,q277,q346,q519,q541]
private theorem k766 : optimized 9 0 sk766 = false := certified_fast (by decide +kernel)
private def sk767 : List W := [q489,q478,q384,q430,q451,q208,q277,q346,q519,q541]
private theorem k767 : optimized 9 0 sk767 = false := certified_fast (by decide +kernel)
private def sk768 : List W := [q490,q277,q133,q430,q451,q208,q242,q346,q519,q541]
private theorem k768 : optimized 9 0 sk768 = false := certified_fast (by decide +kernel)
private def sk769 : List W := [q490,q277,q423,q430,q451,q208,q242,q346,q519,q541]
private theorem k769 : optimized 9 0 sk769 = false := certified_fast (by decide +kernel)
private def sk770 : List W := [q491,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k770 : optimized 9 0 sk770 = false := certified_fast (by decide +kernel)
private def sk771 : List W := [q492,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k771 : optimized 9 0 sk771 = false := certified_fast (by decide +kernel)
private def sk772 : List W := [q493,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k772 : optimized 9 0 sk772 = false := certified_fast (by decide +kernel)
private def sk773 : List W := [q494,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k773 : optimized 9 0 sk773 = false := certified_fast (by decide +kernel)
private def sk774 : List W := [q495,q307,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k774 : optimized 9 0 sk774 = false := certified_fast (by decide +kernel)
private def sk775 : List W := [q495,q346,q328,q430,q451,q208,q242,q277,q519,q541]
private theorem k775 : optimized 9 0 sk775 = false := certified_fast (by decide +kernel)
private def sk776 : List W := [q495,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k776 : optimized 9 0 sk776 = false := certified_fast (by decide +kernel)
private def sk777 : List W := [q495,q478,q297,q430,q451,q208,q242,q277,q519,q541]
private theorem k777 : optimized 9 0 sk777 = false := certified_fast (by decide +kernel)
private def sk778 : List W := [q495,q478,q307,q430,q451,q208,q242,q277,q519,q541]
private theorem k778 : optimized 9 0 sk778 = false := certified_fast (by decide +kernel)
private def sk779 : List W := [q495,q478,q328,q430,q451,q208,q242,q277,q519,q541]
private theorem k779 : optimized 9 0 sk779 = false := certified_fast (by decide +kernel)
private def sk780 : List W := [q495,q478,q335,q430,q451,q208,q242,q277,q519,q541]
private theorem k780 : optimized 9 0 sk780 = false := certified_fast (by decide +kernel)
private def sk781 : List W := [q496,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k781 : optimized 9 0 sk781 = false := certified_fast (by decide +kernel)
private def sk782 : List W := [q497,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k782 : optimized 9 0 sk782 = false := certified_fast (by decide +kernel)
private def sk783 : List W := [q498,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k783 : optimized 9 0 sk783 = false := certified_fast (by decide +kernel)
private def sk784 : List W := [q499,q384,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k784 : optimized 9 0 sk784 = false := certified_fast (by decide +kernel)
private def sk785 : List W := [q499,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k785 : optimized 9 0 sk785 = false := certified_fast (by decide +kernel)
private def sk786 : List W := [q500,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k786 : optimized 9 0 sk786 = false := certified_fast (by decide +kernel)
private def sk787 : List W := [q501,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k787 : optimized 9 0 sk787 = false := certified_fast (by decide +kernel)
private def sk788 : List W := [q502,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k788 : optimized 9 0 sk788 = false := certified_fast (by decide +kernel)
private def sk789 : List W := [q503,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k789 : optimized 9 0 sk789 = false := certified_fast (by decide +kernel)
private def sk790 : List W := [q504,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k790 : optimized 9 0 sk790 = false := certified_fast (by decide +kernel)
private def sk791 : List W := [q505,q133,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k791 : optimized 9 0 sk791 = false := certified_fast (by decide +kernel)
private def sk792 : List W := [q505,q177,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k792 : optimized 9 0 sk792 = false := certified_fast (by decide +kernel)
private def sk793 : List W := [q505,q430,q133,q451,q208,q242,q277,q346,q519,q541]
private theorem k793 : optimized 9 0 sk793 = false := certified_fast (by decide +kernel)
private def sk794 : List W := [q505,q430,q423,q451,q208,q242,q277,q346,q519,q541]
private theorem k794 : optimized 9 0 sk794 = false := certified_fast (by decide +kernel)
private def sk795 : List W := [q505,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k795 : optimized 9 0 sk795 = false := certified_fast (by decide +kernel)
private def sk796 : List W := [q505,q478,q177,q451,q208,q242,q277,q346,q519,q541]
private theorem k796 : optimized 9 0 sk796 = false := certified_fast (by decide +kernel)
private def sk797 : List W := [q505,q478,q384,q451,q208,q242,q277,q346,q519,q541]
private theorem k797 : optimized 9 0 sk797 = false := certified_fast (by decide +kernel)
private def sk798 : List W := [q505,q478,q423,q451,q208,q242,q277,q346,q519,q541]
private theorem k798 : optimized 9 0 sk798 = false := certified_fast (by decide +kernel)
private def sk799 : List W := [q505,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k799 : optimized 9 0 sk799 = false := certified_fast (by decide +kernel)
private def sk800 : List W := [q506,q208,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k800 : optimized 9 0 sk800 = false := certified_fast (by decide +kernel)
private def sk801 : List W := [q507,q242,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k801 : optimized 9 0 sk801 = false := certified_fast (by decide +kernel)
private def sk802 : List W := [q508,q277,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k802 : optimized 9 0 sk802 = false := certified_fast (by decide +kernel)
private def sk803 : List W := [q509,q346,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k803 : optimized 9 0 sk803 = false := certified_fast (by decide +kernel)
private def sk804 : List W := [q509,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k804 : optimized 9 0 sk804 = false := certified_fast (by decide +kernel)
private def sk805 : List W := [q509,q478,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k805 : optimized 9 0 sk805 = false := certified_fast (by decide +kernel)
private def sk806 : List W := [q510,q451,q133,q430,q208,q242,q277,q346,q519,q541]
private theorem k806 : optimized 9 0 sk806 = false := certified_fast (by decide +kernel)
private def sk807 : List W := [q510,q451,q307,q430,q208,q242,q277,q346,q519,q541]
private theorem k807 : optimized 9 0 sk807 = false := certified_fast (by decide +kernel)
private def sk808 : List W := [q510,q451,q423,q430,q208,q242,q277,q346,q519,q541]
private theorem k808 : optimized 9 0 sk808 = false := certified_fast (by decide +kernel)
private def sk809 : List W := [q510,q451,q495,q430,q208,q242,q277,q346,q519,q541]
private theorem k809 : optimized 9 0 sk809 = false := certified_fast (by decide +kernel)
private def sk810 : List W := [q510,q478,q157,q430,q208,q242,q277,q346,q519,q541]
private theorem k810 : optimized 9 0 sk810 = false := certified_fast (by decide +kernel)
private def sk811 : List W := [q510,q478,q414,q430,q208,q242,q277,q346,q519,q541]
private theorem k811 : optimized 9 0 sk811 = false := certified_fast (by decide +kernel)
private def sk812 : List W := [q511,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k812 : optimized 9 0 sk812 = false := certified_fast (by decide +kernel)
private def sk813 : List W := [q512,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k813 : optimized 9 0 sk813 = false := certified_fast (by decide +kernel)
private def sk814 : List W := [q513,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k814 : optimized 9 0 sk814 = false := certified_fast (by decide +kernel)
private def sk815 : List W := [q514,q451,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k815 : optimized 9 0 sk815 = false := certified_fast (by decide +kernel)
private def sk816 : List W := [q515,q85,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k816 : optimized 9 0 sk816 = false := certified_fast (by decide +kernel)
private def sk817 : List W := [q515,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k817 : optimized 9 0 sk817 = false := certified_fast (by decide +kernel)
private def sk818 : List W := [q516,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k818 : optimized 9 0 sk818 = false := certified_fast (by decide +kernel)
private def sk819 : List W := [q517,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k819 : optimized 9 0 sk819 = false := certified_fast (by decide +kernel)
private def sk820 : List W := [q518,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k820 : optimized 9 0 sk820 = false := certified_fast (by decide +kernel)
private def sk821 : List W := [q520,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k821 : optimized 9 0 sk821 = false := certified_fast (by decide +kernel)
private def sk822 : List W := [q521,q85,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k822 : optimized 9 0 sk822 = false := certified_fast (by decide +kernel)
private def sk823 : List W := [q521,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k823 : optimized 9 0 sk823 = false := certified_fast (by decide +kernel)
private def sk824 : List W := [q522,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k824 : optimized 9 0 sk824 = false := certified_fast (by decide +kernel)
private def sk825 : List W := [q523,q169,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k825 : optimized 9 0 sk825 = false := certified_fast (by decide +kernel)
private def sk826 : List W := [q523,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k826 : optimized 9 0 sk826 = false := certified_fast (by decide +kernel)
private def sk827 : List W := [q524,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k827 : optimized 9 0 sk827 = false := certified_fast (by decide +kernel)
private def sk828 : List W := [q525,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k828 : optimized 9 0 sk828 = false := certified_fast (by decide +kernel)
private def sk829 : List W := [q526,q177,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k829 : optimized 9 0 sk829 = false := certified_fast (by decide +kernel)
private def sk830 : List W := [q526,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k830 : optimized 9 0 sk830 = false := certified_fast (by decide +kernel)
private def sk831 : List W := [q527,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k831 : optimized 9 0 sk831 = false := certified_fast (by decide +kernel)
private def sk832 : List W := [q528,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k832 : optimized 9 0 sk832 = false := certified_fast (by decide +kernel)
private def sk833 : List W := [q529,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k833 : optimized 9 0 sk833 = false := certified_fast (by decide +kernel)
private def sk834 : List W := [q530,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k834 : optimized 9 0 sk834 = false := certified_fast (by decide +kernel)
private def sk835 : List W := [q531,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k835 : optimized 9 0 sk835 = false := certified_fast (by decide +kernel)
private def sk836 : List W := [q532,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k836 : optimized 9 0 sk836 = false := certified_fast (by decide +kernel)
private def sk837 : List W := [q533,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k837 : optimized 9 0 sk837 = false := certified_fast (by decide +kernel)
private def sk838 : List W := [q534,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k838 : optimized 9 0 sk838 = false := certified_fast (by decide +kernel)
private def sk839 : List W := [q535,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k839 : optimized 9 0 sk839 = false := certified_fast (by decide +kernel)
private def sk840 : List W := [q536,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k840 : optimized 9 0 sk840 = false := certified_fast (by decide +kernel)
private def sk841 : List W := [q537,q519,q399,q451,q208,q242,q478,q277,q346,q541]
private theorem k841 : optimized 9 0 sk841 = false := certified_fast (by decide +kernel)
private def sk842 : List W := [q538,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k842 : optimized 9 0 sk842 = false := certified_fast (by decide +kernel)
private def sk843 : List W := [q539,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k843 : optimized 9 0 sk843 = false := certified_fast (by decide +kernel)
private def sk844 : List W := [q540,q519,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k844 : optimized 9 0 sk844 = false := certified_fast (by decide +kernel)
private def sk845 : List W := [q542,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k845 : optimized 9 0 sk845 = false := certified_fast (by decide +kernel)
private def sk846 : List W := [q543,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k846 : optimized 9 0 sk846 = false := certified_fast (by decide +kernel)
private def sk847 : List W := [q544,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k847 : optimized 9 0 sk847 = false := certified_fast (by decide +kernel)
private def sk848 : List W := [q545,q169,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k848 : optimized 9 0 sk848 = false := certified_fast (by decide +kernel)
private def sk849 : List W := [q545,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k849 : optimized 9 0 sk849 = false := certified_fast (by decide +kernel)
private def sk850 : List W := [q546,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k850 : optimized 9 0 sk850 = false := certified_fast (by decide +kernel)
private def sk851 : List W := [q547,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k851 : optimized 9 0 sk851 = false := certified_fast (by decide +kernel)
private def sk852 : List W := [q548,q177,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k852 : optimized 9 0 sk852 = false := certified_fast (by decide +kernel)
private def sk853 : List W := [q548,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k853 : optimized 9 0 sk853 = false := certified_fast (by decide +kernel)
private def sk854 : List W := [q549,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k854 : optimized 9 0 sk854 = false := certified_fast (by decide +kernel)
private def sk855 : List W := [q550,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k855 : optimized 9 0 sk855 = false := certified_fast (by decide +kernel)
private def sk856 : List W := [q551,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k856 : optimized 9 0 sk856 = false := certified_fast (by decide +kernel)
private def sk857 : List W := [q552,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k857 : optimized 9 0 sk857 = false := certified_fast (by decide +kernel)
private def sk858 : List W := [q553,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k858 : optimized 9 0 sk858 = false := certified_fast (by decide +kernel)
private def sk859 : List W := [q554,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k859 : optimized 9 0 sk859 = false := certified_fast (by decide +kernel)
private def sk860 : List W := [q555,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k860 : optimized 9 0 sk860 = false := certified_fast (by decide +kernel)
private def sk861 : List W := [q556,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k861 : optimized 9 0 sk861 = false := certified_fast (by decide +kernel)
private def sk862 : List W := [q557,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k862 : optimized 9 0 sk862 = false := certified_fast (by decide +kernel)
private def sk863 : List W := [q558,q541,q297,q451,q208,q242,q478,q277,q346,q519]
private theorem k863 : optimized 9 0 sk863 = false := certified_fast (by decide +kernel)
private def sk864 : List W := [q558,q541,q384,q451,q208,q242,q478,q277,q346,q519]
private theorem k864 : optimized 9 0 sk864 = false := certified_fast (by decide +kernel)
private def sk865 : List W := [q558,q541,q436,q451,q208,q242,q478,q277,q346,q519]
private theorem k865 : optimized 9 0 sk865 = false := certified_fast (by decide +kernel)
private def sk866 : List W := [q559,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k866 : optimized 9 0 sk866 = false := certified_fast (by decide +kernel)
private def sk867 : List W := [q560,q541,q177,q430,q451,q208,q242,q277,q346,q519]
private theorem k867 : optimized 9 0 sk867 = false := certified_fast (by decide +kernel)
private def sk868 : List W := [q560,q541,q307,q430,q451,q208,q242,q277,q346,q519]
private theorem k868 : optimized 9 0 sk868 = false := certified_fast (by decide +kernel)
private def sk869 : List W := [q560,q541,q495,q430,q451,q208,q242,q277,q346,q519]
private theorem k869 : optimized 9 0 sk869 = false := certified_fast (by decide +kernel)
private def sk870 : List W := [q560,q541,q505,q430,q451,q208,q242,q277,q346,q519]
private theorem k870 : optimized 9 0 sk870 = false := certified_fast (by decide +kernel)
private def sk871 : List W := [q561,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k871 : optimized 9 0 sk871 = false := certified_fast (by decide +kernel)
private def sk872 : List W := [q562,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k872 : optimized 9 0 sk872 = false := certified_fast (by decide +kernel)
private def sk873 : List W := [q563,q541,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k873 : optimized 9 0 sk873 = false := certified_fast (by decide +kernel)
private def sk874 : List W := [q75,q399,q451,q242,q478,q277,q346,q519,q541]
private theorem k874 : optimized 9 1 sk874 = false := certified_fast (by decide +kernel)
private def sk875 : List W := [q85,q384,q451,q208,q478,q277,q346,q519,q541]
private theorem k875 : optimized 9 1 sk875 = false := certified_fast (by decide +kernel)
private def sk876 : List W := [q100,q297,q451,q208,q242,q478,q277,q519,q541]
private theorem k876 : optimized 9 1 sk876 = false := certified_fast (by decide +kernel)
private def sk877 : List W := [q125,q307,q430,q451,q208,q242,q277,q519,q541]
private theorem k877 : optimized 9 1 sk877 = false := certified_fast (by decide +kernel)
private def sk878 : List W := [q133,q177,q451,q208,q242,q277,q346,q519,q541]
private theorem k878 : optimized 9 1 sk878 = false := certified_fast (by decide +kernel)
private def sk879 : List W := [q157,q169,q208,q242,q478,q277,q346,q519,q541]
private theorem k879 : optimized 9 1 sk879 = false := certified_fast (by decide +kernel)
private def sk880 : List W := [q169,q157,q208,q242,q478,q277,q346,q519,q541]
private theorem k880 : optimized 9 1 sk880 = false := certified_fast (by decide +kernel)
private def sk881 : List W := [q177,q133,q451,q208,q242,q277,q346,q519,q541]
private theorem k881 : optimized 9 1 sk881 = false := certified_fast (by decide +kernel)
private def sk882 : List W := [q204,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k882 : optimized 9 1 sk882 = false := certified_fast (by decide +kernel)
private def sk883 : List W := [q207,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k883 : optimized 9 1 sk883 = false := certified_fast (by decide +kernel)
private def sk884 : List W := [q214,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k884 : optimized 9 1 sk884 = false := certified_fast (by decide +kernel)
private def sk885 : List W := [q216,q430,q451,q242,q478,q277,q346,q519,q541]
private theorem k885 : optimized 9 1 sk885 = false := certified_fast (by decide +kernel)
private def sk886 : List W := [q240,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k886 : optimized 9 1 sk886 = false := certified_fast (by decide +kernel)
private def sk887 : List W := [q241,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k887 : optimized 9 1 sk887 = false := certified_fast (by decide +kernel)
private def sk888 : List W := [q248,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k888 : optimized 9 1 sk888 = false := certified_fast (by decide +kernel)
private def sk889 : List W := [q249,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k889 : optimized 9 1 sk889 = false := certified_fast (by decide +kernel)
private def sk890 : List W := [q250,q430,q451,q208,q478,q277,q346,q519,q541]
private theorem k890 : optimized 9 1 sk890 = false := certified_fast (by decide +kernel)
private def sk891 : List W := [q275,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k891 : optimized 9 1 sk891 = false := certified_fast (by decide +kernel)
private def sk892 : List W := [q276,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k892 : optimized 9 1 sk892 = false := certified_fast (by decide +kernel)
private def sk893 : List W := [q283,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k893 : optimized 9 1 sk893 = false := certified_fast (by decide +kernel)
private def sk894 : List W := [q284,q430,q451,q208,q242,q478,q346,q519,q541]
private theorem k894 : optimized 9 1 sk894 = false := certified_fast (by decide +kernel)
private def sk895 : List W := [q297,q100,q451,q208,q242,q478,q277,q519,q541]
private theorem k895 : optimized 9 1 sk895 = false := certified_fast (by decide +kernel)
private def sk896 : List W := [q328,q495,q430,q451,q208,q242,q277,q519,q541]
private theorem k896 : optimized 9 1 sk896 = false := certified_fast (by decide +kernel)
private def sk897 : List W := [q335,q436,q451,q208,q242,q478,q277,q519,q541]
private theorem k897 : optimized 9 1 sk897 = false := certified_fast (by decide +kernel)
private def sk898 : List W := [q343,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k898 : optimized 9 1 sk898 = false := certified_fast (by decide +kernel)
private def sk899 : List W := [q344,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k899 : optimized 9 1 sk899 = false := certified_fast (by decide +kernel)
private def sk900 : List W := [q345,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k900 : optimized 9 1 sk900 = false := certified_fast (by decide +kernel)
private def sk901 : List W := [q348,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k901 : optimized 9 1 sk901 = false := certified_fast (by decide +kernel)
private def sk902 : List W := [q355,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k902 : optimized 9 1 sk902 = false := certified_fast (by decide +kernel)
private def sk903 : List W := [q357,q430,q451,q208,q242,q478,q277,q519,q541]
private theorem k903 : optimized 9 1 sk903 = false := certified_fast (by decide +kernel)
private def sk904 : List W := [q384,q85,q451,q208,q478,q277,q346,q519,q541]
private theorem k904 : optimized 9 1 sk904 = false := certified_fast (by decide +kernel)
private def sk905 : List W := [q399,q75,q451,q242,q478,q277,q346,q519,q541]
private theorem k905 : optimized 9 1 sk905 = false := certified_fast (by decide +kernel)
private def sk906 : List W := [q406,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k906 : optimized 9 1 sk906 = false := certified_fast (by decide +kernel)
private def sk907 : List W := [q416,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k907 : optimized 9 1 sk907 = false := certified_fast (by decide +kernel)
private def sk908 : List W := [q423,q505,q451,q208,q242,q277,q346,q519,q541]
private theorem k908 : optimized 9 1 sk908 = false := certified_fast (by decide +kernel)
private def sk909 : List W := [q432,q197,q451,q242,q478,q277,q346,q519,q541]
private theorem k909 : optimized 9 1 sk909 = false := certified_fast (by decide +kernel)
private def sk910 : List W := [q433,q231,q451,q208,q478,q277,q346,q519,q541]
private theorem k910 : optimized 9 1 sk910 = false := certified_fast (by decide +kernel)
private def sk911 : List W := [q436,q335,q451,q208,q242,q478,q277,q519,q541]
private theorem k911 : optimized 9 1 sk911 = false := certified_fast (by decide +kernel)
private def sk912 : List W := [q440,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k912 : optimized 9 1 sk912 = false := certified_fast (by decide +kernel)
private def sk913 : List W := [q441,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k913 : optimized 9 1 sk913 = false := certified_fast (by decide +kernel)
private def sk914 : List W := [q442,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k914 : optimized 9 1 sk914 = false := certified_fast (by decide +kernel)
private def sk915 : List W := [q443,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k915 : optimized 9 1 sk915 = false := certified_fast (by decide +kernel)
private def sk916 : List W := [q444,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k916 : optimized 9 1 sk916 = false := certified_fast (by decide +kernel)
private def sk917 : List W := [q457,q430,q208,q242,q478,q277,q346,q519,q541]
private theorem k917 : optimized 9 1 sk917 = false := certified_fast (by decide +kernel)
private def sk918 : List W := [q473,q414,q208,q242,q478,q277,q346,q519,q541]
private theorem k918 : optimized 9 1 sk918 = false := certified_fast (by decide +kernel)
private def sk919 : List W := [q483,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k919 : optimized 9 1 sk919 = false := certified_fast (by decide +kernel)
private def sk920 : List W := [q486,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k920 : optimized 9 1 sk920 = false := certified_fast (by decide +kernel)
private def sk921 : List W := [q495,q328,q430,q451,q208,q242,q277,q519,q541]
private theorem k921 : optimized 9 1 sk921 = false := certified_fast (by decide +kernel)
private def sk922 : List W := [q499,q430,q451,q208,q242,q277,q346,q519,q541]
private theorem k922 : optimized 9 1 sk922 = false := certified_fast (by decide +kernel)
private def sk923 : List W := [q505,q423,q451,q208,q242,q277,q346,q519,q541]
private theorem k923 : optimized 9 1 sk923 = false := certified_fast (by decide +kernel)
private def sk924 : List W := [q515,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k924 : optimized 9 1 sk924 = false := certified_fast (by decide +kernel)
private def sk925 : List W := [q521,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k925 : optimized 9 1 sk925 = false := certified_fast (by decide +kernel)
private def sk926 : List W := [q523,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k926 : optimized 9 1 sk926 = false := certified_fast (by decide +kernel)
private def sk927 : List W := [q526,q430,q451,q208,q242,q478,q277,q346,q541]
private theorem k927 : optimized 9 1 sk927 = false := certified_fast (by decide +kernel)
private def sk928 : List W := [q545,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k928 : optimized 9 1 sk928 = false := certified_fast (by decide +kernel)
private def sk929 : List W := [q548,q430,q451,q208,q242,q478,q277,q346,q519]
private theorem k929 : optimized 9 1 sk929 = false := certified_fast (by decide +kernel)
private def sk930 : List W := [q75,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k930 : optimized 10 1 sk930 = false := certify [(0,sk3),(0,sk659),(0,sk668),(0,sk56),(0,sk99),(0,sk707),(0,sk711),(0,sk0),(0,sk311),(0,sk313),(0,sk58),(0,sk98),(0,sk368),(0,sk378),(0,sk67),(0,sk94),(0,sk748),(0,sk752),(0,sk60),(0,sk97),(0,sk407),(0,sk417),(0,sk62),(0,sk96),(0,sk518),(0,sk533),(0,sk92),(0,sk68),(0,sk819),(0,sk828),(0,sk100),(0,sk17),(0,sk820),(0,sk850),(0,sk315),(1,sk905),(0,sk610),(0,sk606),(0,sk660)] (by decide +kernel) ⟨k3,k659,k668,k56,k99,k707,k711,k0,k311,k313,k58,k98,k368,k378,k67,k94,k748,k752,k60,k97,k407,k417,k62,k96,k518,k533,k92,k68,k819,k828,k100,k17,k820,k850,k315,k905,k610,k606,k660,True.intro⟩
private def sk931 : List W := [q85,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k931 : optimized 10 1 sk931 = false := certify [(0,sk3),(0,sk669),(0,sk679),(0,sk13),(0,sk116),(0,sk709),(0,sk712),(0,sk57),(0,sk109),(0,sk327),(0,sk330),(0,sk1),(0,sk359),(0,sk361),(0,sk19),(0,sk115),(0,sk750),(0,sk753),(0,sk20),(0,sk113),(0,sk411),(0,sk418),(0,sk24),(0,sk111),(1,sk899),(0,sk529),(0,sk530),(1,sk901),(0,sk534),(0,sk535),(0,sk108),(0,sk59),(1,sk924),(0,sk816),(0,sk817),(1,sk925),(0,sk822),(0,sk823),(0,sk112),(0,sk22),(0,sk818),(0,sk851),(0,sk363),(1,sk904),(0,sk587),(0,sk582),(0,sk670)] (by decide +kernel) ⟨k3,k669,k679,k13,k116,k709,k712,k57,k109,k327,k330,k1,k359,k361,k19,k115,k750,k753,k20,k113,k411,k418,k24,k111,k899,k529,k530,k901,k534,k535,k108,k59,k924,k816,k817,k925,k822,k823,k112,k22,k818,k851,k363,k904,k587,k582,k670,True.intro⟩
private def sk932 : List W := [q100,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k932 : optimized 10 1 sk932 = false := certify [(0,sk3),(0,sk682),(0,sk690),(0,sk15),(0,sk136),(0,sk708),(0,sk713),(0,sk61),(0,sk130),(0,sk326),(0,sk331),(0,sk23),(0,sk134),(0,sk371),(0,sk379),(0,sk27),(0,sk133),(0,sk749),(0,sk754),(0,sk21),(0,sk135),(0,sk410),(0,sk419),(0,sk2),(0,sk507),(0,sk510),(0,sk129),(0,sk63),(0,sk813),(0,sk824),(0,sk131),(0,sk29),(0,sk814),(0,sk854),(0,sk512),(1,sk895),(0,sk450),(0,sk446),(0,sk684)] (by decide +kernel) ⟨k3,k682,k690,k15,k136,k708,k713,k61,k130,k326,k331,k23,k134,k371,k379,k27,k133,k749,k754,k21,k135,k410,k419,k2,k507,k510,k129,k63,k813,k824,k131,k29,k814,k854,k512,k895,k450,k446,k684,True.intro⟩
private def sk933 : List W := [q133,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k933 : optimized 10 1 sk933 = false := certify [(0,sk3),(0,sk644),(0,sk647),(0,sk195),(0,sk90),(0,sk704),(0,sk710),(0,sk151),(0,sk193),(0,sk303),(0,sk332),(0,sk158),(0,sk191),(0,sk351),(0,sk380),(0,sk5),(0,sk791),(0,sk799),(0,sk167),(0,sk190),(0,sk400),(0,sk420),(0,sk177),(0,sk171),(0,sk499),(0,sk537),(0,sk197),(0,sk54),(0,sk757),(0,sk821),(0,sk198),(0,sk11),(0,sk758),(0,sk847),(0,sk583),(0,sk671),(0,sk649),(1,sk881),(0,sk281),(0,sk284),(0,sk793),(0,sk251),(0,sk806),(0,sk565),(0,sk768)] (by decide +kernel) ⟨k3,k644,k647,k195,k90,k704,k710,k151,k193,k303,k332,k158,k191,k351,k380,k5,k791,k799,k167,k190,k400,k420,k177,k171,k499,k537,k197,k54,k757,k821,k198,k11,k758,k847,k583,k671,k649,k881,k281,k284,k793,k251,k806,k565,k768,True.intro⟩
private def sk934 : List W := [q157,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k934 : optimized 10 1 sk934 = false := certify [(0,sk3),(0,sk629),(0,sk632),(0,sk4),(0,sk736),(0,sk745),(0,sk212),(0,sk236),(0,sk298),(0,sk333),(0,sk217),(0,sk234),(0,sk344),(0,sk381),(0,sk239),(0,sk91),(0,sk714),(0,sk751),(0,sk222),(0,sk233),(0,sk396),(0,sk421),(0,sk228),(0,sk224),(0,sk484),(0,sk540),(0,sk240),(0,sk83),(0,sk717),(0,sk838),(0,sk241),(0,sk40),(0,sk718),(0,sk860),(0,sk633),(1,sk880),(0,sk267),(0,sk269),(0,sk738),(0,sk607),(0,sk661),(0,sk447),(0,sk685),(0,sk209),(0,sk810),(0,sk563),(0,sk725)] (by decide +kernel) ⟨k3,k629,k632,k4,k736,k745,k212,k236,k298,k333,k217,k234,k344,k381,k239,k91,k714,k751,k222,k233,k396,k421,k228,k224,k484,k540,k240,k83,k717,k838,k241,k40,k718,k860,k633,k880,k267,k269,k738,k607,k661,k447,k685,k209,k810,k563,k725,True.intro⟩
private def sk935 : List W := [q169,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k935 : optimized 10 1 sk935 = false := certify [(0,sk3),(0,sk737),(0,sk740),(0,sk4),(0,sk630),(0,sk634),(0,sk55),(0,sk260),(1,sk883),(0,sk328),(0,sk329),(1,sk884),(0,sk335),(0,sk336),(0,sk12),(0,sk264),(1,sk887),(0,sk376),(0,sk377),(1,sk888),(0,sk383),(0,sk384),(0,sk258),(0,sk148),(1,sk914),(0,sk698),(0,sk699),(1,sk919),(0,sk755),(0,sk756),(0,sk6),(0,sk265),(1,sk892),(0,sk415),(0,sk416),(1,sk893),(0,sk422),(0,sk423),(0,sk14),(0,sk262),(1,sk900),(0,sk531),(0,sk532),(1,sk902),(0,sk542),(0,sk543),(0,sk259),(0,sk64),(1,sk915),(0,sk700),(0,sk701),(1,sk926),(0,sk825),(0,sk826),(0,sk261),(0,sk16),(1,sk916),(0,sk702),(0,sk703),(1,sk928),(0,sk848),(0,sk849),(0,sk631),(1,sk879),(0,sk243),(0,sk245),(0,sk741)] (by decide +kernel) ⟨k3,k737,k740,k4,k630,k634,k55,k260,k883,k328,k329,k884,k335,k336,k12,k264,k887,k376,k377,k888,k383,k384,k258,k148,k914,k698,k699,k919,k755,k756,k6,k265,k892,k415,k416,k893,k422,k423,k14,k262,k900,k531,k532,k902,k542,k543,k259,k64,k915,k700,k701,k926,k825,k826,k261,k16,k916,k702,k703,k928,k848,k849,k631,k879,k243,k245,k741,True.intro⟩
private def sk936 : List W := [q177,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k936 : optimized 10 1 sk936 = false := certify [(0,sk3),(0,sk792),(0,sk795),(0,sk257),(0,sk211),(1,sk907),(0,sk636),(0,sk637),(1,sk917),(0,sk715),(0,sk716),(0,sk66),(0,sk273),(1,sk882),(0,sk324),(0,sk325),(1,sk885),(0,sk338),(0,sk339),(0,sk18),(0,sk278),(1,sk886),(0,sk374),(0,sk375),(1,sk890),(0,sk387),(0,sk388),(0,sk5),(0,sk645),(0,sk650),(0,sk7),(0,sk279),(1,sk891),(0,sk413),(0,sk414),(1,sk894),(0,sk424),(0,sk425),(0,sk25),(0,sk275),(1,sk898),(0,sk527),(0,sk528),(1,sk903),(0,sk545),(0,sk546),(0,sk272),(0,sk69),(1,sk912),(0,sk694),(0,sk695),(1,sk927),(0,sk829),(0,sk830),(0,sk274),(0,sk28),(1,sk913),(0,sk696),(0,sk697),(1,sk929),(0,sk852),(0,sk853),(0,sk646),(1,sk878),(0,sk200),(0,sk203),(0,sk796),(0,sk617),(0,sk761),(0,sk348),(0,sk161),(0,sk47),(0,sk867)] (by decide +kernel) ⟨k3,k792,k795,k257,k211,k907,k636,k637,k917,k715,k716,k66,k273,k882,k324,k325,k885,k338,k339,k18,k278,k886,k374,k375,k890,k387,k388,k5,k645,k650,k7,k279,k891,k413,k414,k894,k424,k425,k25,k275,k898,k527,k528,k903,k545,k546,k272,k69,k912,k694,k695,k927,k829,k830,k274,k28,k913,k696,k697,k929,k852,k853,k646,k878,k200,k203,k796,k617,k761,k348,k161,k47,k867,True.intro⟩
private def sk937 : List W := [q197,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k937 : optimized 10 1 sk937 = false := certify [(0,sk3),(0,sk605),(0,sk611),(0,sk297),(0,sk213),(0,sk616),(0,sk719),(0,sk0),(0,sk101),(0,sk103),(0,sk72),(0,sk309),(0,sk367),(0,sk393),(0,sk301),(0,sk152),(1,sk906),(0,sk619),(0,sk620),(1,sk920),(0,sk759),(0,sk760),(0,sk74),(0,sk307),(0,sk406),(0,sk428),(0,sk79),(0,sk306),(0,sk517),(0,sk552),(0,sk304),(0,sk84),(0,sk623),(0,sk839),(0,sk310),(0,sk31),(0,sk624),(0,sk856),(0,sk608),(0,sk104),(1,sk909),(0,sk666),(0,sk662),(0,sk214),(0,sk720),(0,sk154),(0,sk763),(0,sk321),(0,sk429)] (by decide +kernel) ⟨k3,k605,k611,k297,k213,k616,k719,k0,k101,k103,k72,k309,k367,k393,k301,k152,k906,k619,k620,k920,k759,k760,k74,k307,k406,k428,k79,k306,k517,k552,k304,k84,k623,k839,k310,k31,k624,k856,k608,k104,k909,k666,k662,k214,k720,k154,k763,k321,k429,True.intro⟩
private def sk938 : List W := [q231,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k938 : optimized 10 1 sk938 = false := certify [(0,sk3),(0,sk581),(0,sk588),(0,sk343),(0,sk218),(0,sk593),(0,sk722),(0,sk71),(0,sk353),(0,sk323),(0,sk392),(0,sk1),(0,sk117),(0,sk119),(0,sk347),(0,sk159),(0,sk594),(0,sk765),(0,sk10),(0,sk358),(0,sk412),(0,sk434),(0,sk34),(0,sk356),(0,sk526),(0,sk556),(0,sk352),(0,sk73),(0,sk597),(0,sk832),(0,sk357),(0,sk32),(0,sk598),(0,sk857),(0,sk584),(0,sk120),(1,sk910),(0,sk677),(0,sk672),(0,sk219),(0,sk723),(0,sk163),(0,sk766),(0,sk372),(0,sk435)] (by decide +kernel) ⟨k3,k581,k588,k343,k218,k593,k722,k71,k353,k323,k392,k1,k117,k119,k347,k159,k594,k765,k10,k358,k412,k434,k34,k356,k526,k556,k352,k73,k597,k832,k357,k32,k598,k857,k584,k120,k910,k677,k672,k219,k723,k163,k766,k372,k435,True.intro⟩
private def sk939 : List W := [q297,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k939 : optimized 10 1 sk939 = false := certify [(0,sk3),(0,sk508),(0,sk514),(0,sk439),(0,sk225),(0,sk541),(0,sk727),(0,sk305),(0,sk432),(0,sk107),(0,sk455),(0,sk355),(0,sk426),(0,sk122),(0,sk456),(0,sk442),(0,sk173),(0,sk544),(0,sk770),(0,sk402),(0,sk391),(0,sk127),(0,sk457),(0,sk2),(0,sk683),(0,sk687),(0,sk443),(0,sk75),(0,sk547),(0,sk833),(0,sk444),(0,sk8),(0,sk548),(0,sk845),(0,sk246),(0,sk742),(0,sk509),(1,sk876),(0,sk141),(0,sk138),(0,sk688),(0,sk43),(0,sk863),(0,sk230),(0,sk731),(0,sk523),(0,sk557),(0,sk183),(0,sk777),(0,sk521),(0,sk573),(0,sk519),(0,sk475)] (by decide +kernel) ⟨k3,k508,k514,k439,k225,k541,k727,k305,k432,k107,k455,k355,k426,k122,k456,k442,k173,k544,k770,k402,k391,k127,k457,k2,k683,k687,k443,k75,k547,k833,k444,k8,k548,k845,k246,k742,k509,k876,k141,k138,k688,k43,k863,k230,k731,k523,k557,k183,k777,k521,k573,k519,k475,True.intro⟩
private def sk940 : List W := [q307,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k940 : optimized 10 1 sk940 = false := certify [(0,sk441),(0,sk276),(0,sk536),(0,sk790),(0,sk459),(0,sk226),(0,sk485),(0,sk728),(0,sk299),(0,sk437),(0,sk157),(0,sk471),(0,sk345),(0,sk431),(0,sk166),(0,sk472),(0,sk5),(0,sk494),(0,sk497),(0,sk397),(0,sk394),(0,sk170),(0,sk473),(0,sk2),(0,sk774),(0,sk776),(0,sk462),(0,sk76),(0,sk538),(0,sk834),(0,sk463),(0,sk9),(0,sk539),(0,sk846),(0,sk252),(0,sk807),(0,sk495),(1,sk877),(0,sk184),(0,sk180),(0,sk778),(0,sk48),(0,sk868)] (by decide +kernel) ⟨k441,k276,k536,k790,k459,k226,k485,k728,k299,k437,k157,k471,k345,k431,k166,k472,k5,k494,k497,k397,k394,k170,k473,k2,k774,k776,k462,k76,k538,k834,k463,k9,k539,k846,k252,k807,k495,k877,k184,k180,k778,k48,k868,True.intro⟩
private def sk941 : List W := [q328,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k941 : optimized 10 1 sk941 = false := certify [(0,sk492),(0,sk26),(0,sk458),(0,sk658),(0,sk481),(0,sk227),(0,sk461),(0,sk729),(0,sk77),(0,sk487),(0,sk320),(0,sk549),(0,sk35),(0,sk490),(0,sk369),(0,sk553),(0,sk5),(0,sk464),(0,sk467),(0,sk36),(0,sk489),(0,sk409),(0,sk569),(0,sk2),(0,sk179),(0,sk181),(0,sk486),(0,sk80),(0,sk479),(0,sk835),(0,sk488),(0,sk46),(0,sk480),(0,sk866),(0,sk465),(0,sk185),(1,sk921),(0,sk779),(0,sk775)] (by decide +kernel) ⟨k492,k26,k458,k658,k481,k227,k461,k729,k77,k487,k320,k549,k35,k490,k369,k553,k5,k464,k467,k36,k489,k409,k569,k2,k179,k181,k486,k80,k479,k835,k488,k46,k480,k866,k465,k185,k921,k779,k775,True.intro⟩
private def sk942 : List W := [q335,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k942 : optimized 10 1 sk942 = false := certify [(0,sk3),(0,sk445),(0,sk452),(0,sk483),(0,sk229),(0,sk460),(0,sk730),(0,sk78),(0,sk501),(0,sk319),(0,sk551),(0,sk33),(0,sk505),(0,sk370),(0,sk555),(0,sk493),(0,sk178),(0,sk470),(0,sk771),(0,sk37),(0,sk504),(0,sk408),(0,sk572),(0,sk2),(0,sk137),(0,sk139),(0,sk500),(0,sk81),(0,sk477),(0,sk836),(0,sk503),(0,sk42),(0,sk478),(0,sk862),(0,sk448),(0,sk142),(1,sk911),(0,sk689),(0,sk686),(0,sk231),(0,sk732),(0,sk524),(0,sk558),(0,sk186),(0,sk780),(0,sk522),(0,sk574),(0,sk520),(0,sk476)] (by decide +kernel) ⟨k3,k445,k452,k483,k229,k460,k730,k78,k501,k319,k551,k33,k505,k370,k555,k493,k178,k470,k771,k37,k504,k408,k572,k2,k137,k139,k500,k81,k477,k836,k503,k42,k478,k862,k448,k142,k911,k689,k686,k231,k732,k524,k558,k186,k780,k522,k574,k520,k476,True.intro⟩
private def sk943 : List W := [q384,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k943 : optimized 10 1 sk943 = false := certify [(0,sk3),(0,sk362),(0,sk364),(0,sk576),(0,sk235),(0,sk382),(0,sk733),(0,sk308),(0,sk570),(0,sk106),(0,sk589),(0,sk1),(0,sk676),(0,sk674),(0,sk578),(0,sk192),(1,sk889),(0,sk385),(0,sk386),(1,sk922),(0,sk784),(0,sk785),(0,sk403),(0,sk550),(0,sk126),(0,sk590),(0,sk506),(0,sk427),(0,sk145),(0,sk592),(0,sk579),(0,sk82),(0,sk389),(0,sk837),(0,sk580),(0,sk38),(0,sk390),(0,sk858),(0,sk609),(0,sk663),(0,sk360),(1,sk875),(0,sk121),(0,sk118),(0,sk678),(0,sk204),(0,sk797),(0,sk44),(0,sk864),(0,sk220),(0,sk724),(0,sk164),(0,sk767),(0,sk373),(0,sk436)] (by decide +kernel) ⟨k3,k362,k364,k576,k235,k382,k733,k308,k570,k106,k589,k1,k676,k674,k578,k192,k889,k385,k386,k922,k784,k785,k403,k550,k126,k590,k506,k427,k145,k592,k579,k82,k389,k837,k580,k38,k390,k858,k609,k663,k360,k875,k121,k118,k678,k204,k797,k44,k864,k220,k724,k164,k767,k373,k436,True.intro⟩
private def sk944 : List W := [q399,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k944 : optimized 10 1 sk944 = false := certify [(0,sk3),(0,sk314),(0,sk316),(0,sk600),(0,sk237),(0,sk334),(0,sk734),(0,sk0),(0,sk665),(0,sk664),(0,sk354),(0,sk571),(0,sk123),(0,sk612),(0,sk602),(0,sk194),(0,sk337),(0,sk786),(0,sk401),(0,sk554),(0,sk128),(0,sk613),(0,sk502),(0,sk433),(0,sk146),(0,sk615),(0,sk603),(0,sk65),(0,sk340),(0,sk827),(0,sk604),(0,sk39),(0,sk341),(0,sk859),(0,sk247),(0,sk743),(0,sk312),(1,sk874),(0,sk105),(0,sk102),(0,sk667),(0,sk585),(0,sk673),(0,sk86),(0,sk841),(0,sk215),(0,sk721),(0,sk155),(0,sk764),(0,sk322),(0,sk430)] (by decide +kernel) ⟨k3,k314,k316,k600,k237,k334,k734,k0,k665,k664,k354,k571,k123,k612,k602,k194,k337,k786,k401,k554,k128,k613,k502,k433,k146,k615,k603,k65,k340,k827,k604,k39,k341,k859,k247,k743,k312,k874,k105,k102,k667,k585,k673,k86,k841,k215,k721,k155,k764,k322,k430,True.intro⟩
private def sk945 : List W := [q414,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k945 : optimized 10 1 sk945 = false := certify [(0,sk3),(0,sk242),(0,sk244),(0,sk4),(0,sk266),(0,sk270),(0,sk296),(0,sk599),(0,sk216),(0,sk638),(0,sk342),(0,sk575),(0,sk221),(0,sk639),(0,sk626),(0,sk196),(0,sk293),(0,sk787),(0,sk395),(0,sk560),(0,sk223),(0,sk640),(0,sk482),(0,sk438),(0,sk232),(0,sk641),(0,sk627),(0,sk70),(0,sk294),(0,sk831),(0,sk628),(0,sk30),(0,sk295),(0,sk855),(0,sk248),(0,sk268),(1,sk918),(0,sk739),(0,sk744),(0,sk210),(0,sk811),(0,sk564),(0,sk726)] (by decide +kernel) ⟨k3,k242,k244,k4,k266,k270,k296,k599,k216,k638,k342,k575,k221,k639,k626,k196,k293,k787,k395,k560,k223,k640,k482,k438,k232,k641,k627,k70,k294,k831,k628,k30,k295,k855,k248,k268,k918,k739,k744,k210,k811,k564,k726,True.intro⟩
private def sk946 : List W := [q423,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k946 : optimized 10 1 sk946 = false := certify [(0,sk3),(0,sk199),(0,sk201),(0,sk625),(0,sk238),(0,sk271),(0,sk735),(0,sk300),(0,sk601),(0,sk156),(0,sk653),(0,sk346),(0,sk577),(0,sk165),(0,sk654),(0,sk5),(0,sk280),(0,sk285),(0,sk398),(0,sk561),(0,sk169),(0,sk655),(0,sk491),(0,sk440),(0,sk189),(0,sk657),(0,sk642),(0,sk85),(0,sk291),(0,sk840),(0,sk643),(0,sk41),(0,sk292),(0,sk861),(0,sk205),(0,sk282),(1,sk923),(0,sk794),(0,sk798),(0,sk253),(0,sk808),(0,sk566),(0,sk769)] (by decide +kernel) ⟨k3,k199,k201,k625,k238,k271,k735,k300,k601,k156,k653,k346,k577,k165,k654,k5,k280,k285,k398,k561,k169,k655,k491,k440,k189,k657,k642,k85,k291,k840,k643,k41,k292,k861,k205,k282,k923,k794,k798,k253,k808,k566,k769,True.intro⟩
private def sk947 : List W := [q436,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k947 : optimized 10 1 sk947 = false := certify [(0,sk144),(0,sk143),(0,sk3),(0,sk635),(0,sk250),(0,sk263),(0,sk747),(0,sk317),(0,sk614),(0,sk95),(0,sk691),(0,sk366),(0,sk591),(0,sk110),(0,sk692),(0,sk652),(0,sk208),(0,sk277),(0,sk805),(0,sk405),(0,sk562),(0,sk124),(0,sk693),(0,sk454),(0,sk449),(0,sk2),(0,sk680),(0,sk87),(0,sk289),(0,sk842),(0,sk681),(0,sk52),(0,sk290),(0,sk872),(0,sk249),(0,sk746),(1,sk897),(0,sk513),(0,sk511),(0,sk451),(0,sk140),(0,sk45),(0,sk865)] (by decide +kernel) ⟨k144,k143,k3,k635,k250,k263,k747,k317,k614,k95,k691,k366,k591,k110,k692,k652,k208,k277,k805,k405,k562,k124,k693,k454,k449,k2,k680,k87,k289,k842,k681,k52,k290,k872,k249,k746,k897,k513,k511,k451,k140,k45,k865,True.intro⟩
private def sk948 : List W := [q495,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k948 : optimized 10 1 sk948 = false := certify [(0,sk656),(0,sk288),(0,sk172),(0,sk804),(0,sk705),(0,sk256),(0,sk174),(0,sk815),(0,sk302),(0,sk621),(0,sk153),(0,sk781),(0,sk350),(0,sk595),(0,sk160),(0,sk782),(0,sk188),(0,sk187),(0,sk5),(0,sk399),(0,sk567),(0,sk168),(0,sk783),(0,sk469),(0,sk466),(0,sk2),(0,sk772),(0,sk89),(0,sk175),(0,sk844),(0,sk773),(0,sk53),(0,sk176),(0,sk873),(0,sk515),(0,sk453),(0,sk254),(0,sk809),(0,sk525),(0,sk559),(1,sk896),(0,sk498),(0,sk496),(0,sk468),(0,sk182),(0,sk49),(0,sk869)] (by decide +kernel) ⟨k656,k288,k172,k804,k705,k256,k174,k815,k302,k621,k153,k781,k350,k595,k160,k782,k188,k187,k5,k399,k567,k168,k783,k469,k466,k2,k772,k89,k175,k844,k773,k53,k176,k873,k515,k453,k254,k809,k525,k559,k896,k498,k496,k468,k182,k49,k869,True.intro⟩
private def sk949 : List W := [q505,q430,q451,q208,q242,q478,q277,q346,q519,q541]
private theorem k949 : optimized 10 1 sk949 = false := certify [(0,sk287),(0,sk283),(0,sk3),(0,sk706),(0,sk255),(0,sk147),(0,sk812),(0,sk318),(0,sk622),(0,sk93),(0,sk800),(0,sk365),(0,sk596),(0,sk114),(0,sk801),(0,sk207),(0,sk206),(0,sk5),(0,sk404),(0,sk568),(0,sk125),(0,sk802),(0,sk516),(0,sk474),(0,sk132),(0,sk803),(0,sk788),(0,sk88),(0,sk149),(0,sk843),(0,sk789),(0,sk51),(0,sk150),(0,sk871),(0,sk586),(0,sk675),(1,sk908),(0,sk648),(0,sk651),(0,sk202),(0,sk286),(0,sk618),(0,sk762),(0,sk349),(0,sk162),(0,sk50),(0,sk870)] (by decide +kernel) ⟨k287,k283,k3,k706,k255,k147,k812,k318,k622,k93,k800,k365,k596,k114,k801,k207,k206,k5,k404,k568,k125,k802,k516,k474,k132,k803,k788,k88,k149,k843,k789,k51,k150,k871,k586,k675,k908,k648,k651,k202,k286,k618,k762,k349,k162,k50,k870,True.intro⟩
private theorem absence (z : W) (hn : (z :: inputs).Nodup)
    (neg : optimized 10 1 (z :: inputs) = false) : ¬ live basicOps goal 10 (insert z inputs.toFinset) := by
  intro hl
  have yes := optimized_complete 10 (z :: inputs) 1 hn (by rfl) (by simpa using hl)
  exact Bool.noConfusion (neg.symm.trans yes)
private theorem inputs_eq : inputs = [q430,q451,q208,q242,q478,q277,q346,q519,q541] := by decide +kernel
private theorem absent0 : ¬ live basicOps goal 10 (insert q414 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k945
private theorem absent1 : ¬ live basicOps goal 10 (insert q157 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k934
private theorem absent2 : ¬ live basicOps goal 10 (insert q169 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k935
private theorem absent3 : ¬ live basicOps goal 10 (insert q197 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k937
private theorem absent4 : ¬ live basicOps goal 10 (insert q399 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k944
private theorem absent5 : ¬ live basicOps goal 10 (insert q75 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k930
private theorem absent6 : ¬ live basicOps goal 10 (insert q231 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k938
private theorem absent7 : ¬ live basicOps goal 10 (insert q384 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k943
private theorem absent8 : ¬ live basicOps goal 10 (insert q85 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k931
private theorem absent9 : ¬ live basicOps goal 10 (insert q423 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k946
private theorem absent10 : ¬ live basicOps goal 10 (insert q133 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k933
private theorem absent11 : ¬ live basicOps goal 10 (insert q177 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k936
private theorem absent12 : ¬ live basicOps goal 10 (insert q505 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k949
private theorem absent13 : ¬ live basicOps goal 10 (insert q335 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k942
private theorem absent14 : ¬ live basicOps goal 10 (insert q297 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k939
private theorem absent15 : ¬ live basicOps goal 10 (insert q100 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k932
private theorem absent16 : ¬ live basicOps goal 10 (insert q436 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k947
private theorem absent17 : ¬ live basicOps goal 10 (insert q328 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k941
private theorem absent18 : ¬ live basicOps goal 10 (insert q307 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k940
private theorem absent19 : ¬ live basicOps goal 10 (insert q495 inputs.toFinset) := by
  apply absence _ (by decide +kernel)
  rw [inputs_eq]
  exact k948
def representativeWords : List W := [q414,q157,q169,q197,q399,q75,q231,q384,q85,q423,q133,q177,q505,q335,q297,q100,q436,q328,q307,q495]
theorem deadRepresentativeWords : ∀ z ∈ representativeWords, ¬ live basicOps goal 10 (insert z inputs.toFinset) := by
  intro z hz
  simp only [representativeWords,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absent0
  · exact absent1
  · exact absent2
  · exact absent3
  · exact absent4
  · exact absent5
  · exact absent6
  · exact absent7
  · exact absent8
  · exact absent9
  · exact absent10
  · exact absent11
  · exact absent12
  · exact absent13
  · exact absent14
  · exact absent15
  · exact absent16
  · exact absent17
  · exact absent18
  · exact absent19
end RootCheck
end Signed2964

end PEqualNP.Outside.L_meta_2964

open PEqualNP.Outside.L_meta_2964.Signed2964

theorem PEqualNP.Outside.L_meta_2964 : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.true →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) :=
  of_small (small_from_no_build (Orbit.of_representatives RootCheck.deadRepresentativeWords))
