import Mathlib
import PEqualNP.Defs

-- The live-set argument, the translation from circuits and the search function dispatch are taken
-- from the checked file lean/PEqualNP/Outside/L_meta_6376.lean of this repository (author Bastian
-- Milan, pull request 12547, Apache-2.0). Added here: an ordering rule for consecutive gates with
-- the proof that a shortest derivation can be put in that order (okp to cextend), the ordered
-- search optC with its completeness, and the cut of the search into separately checked lemmas
-- (opt1 to heavyC, front1, s1_i). Changed: the instance (mask 5822, its points, the eight input
-- words), the depth (9 gates) and the explicit circuit.

namespace PEqualNP.Outside.L_meta_6376

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

-- A gate that follows a gate with output p reads p, or its own output has no smaller key.
def okp {α : Type} (key : α → ℕ) (p a b z : α) : Prop := a = p ∨ b = p ∨ ¬ key z < key p

theorem okp_swap {α : Type} {key : α → ℕ} {p a b z : α} (h : okp key p a b z) : okp key p b a z := by
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

section Canon

variable {α : Type} [DecidableEq α]

theorem build_mono {ops : α → α → Finset α} {goal : α} {k : ℕ} {s t : Finset α}
    (hst : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hst h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact .inl (ih hst skip)
    · exact .inr ⟨a, hst ha, b, hst hb, hab, z, hz, ih (Finset.insert_subset_insert z hst) tail⟩

theorem live_build {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : build ops goal k s := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at h
    change goal ∈ s
    simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs, tail⟩
    · exact .inl (ih skip)
    · refine .inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ (ih tail)⟩
      rw [hs]
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

-- A derivation of exactly k gates, none of them repeated, in which consecutive gates are in order.
def cbuild (ops : α → α → Finset α) (goal : α) (key : α → ℕ) : ℕ → α → Finset α → Prop
  | 0, _, available => goal ∈ available
  | k + 1, p, available => ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, z ∉ available ∧ okp key p a b z ∧ cbuild ops goal key k z (insert z available)

theorem cbuild_build {ops : α → α → Finset α} {goal : α} {key : α → ℕ} {k : ℕ} {p : α}
    {s : Finset α} (h : cbuild ops goal key k p s) : build ops goal k s := by
  induction k generalizing p s with
  | zero => exact h
  | succ k ih =>
    obtain ⟨a, ha, b, hb, hab, z, hz, _, _, tail⟩ := h
    exact .inr ⟨a, ha, b, hb, hab, z, hz, ih tail⟩

def minimal (ops : α → α → Finset α) (goal : α) (k : ℕ) (s : Finset α) : Prop :=
  build ops goal k s ∧ ∀ j < k, ¬ build ops goal j s

theorem minimal_tail {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α} {a b z : α}
    (hm : minimal ops goal (k + 1) s) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hz : z ∈ ops a b)
    (tail : build ops goal k (insert z s)) : minimal ops goal k (insert z s) ∧ z ∉ s := by
  refine ⟨⟨tail, fun j hj hbj => hm.2 (j + 1) (by omega) (.inr ⟨a, ha, b, hb, hab, z, hz, hbj⟩)⟩, ?_⟩
  intro hzs
  rw [Finset.insert_eq_of_mem hzs] at tail
  exact hm.2 k (by omega) tail

-- A shortest derivation can be put in order: take as first gate the one of least key among the
-- first gates of shortest derivations.
theorem canon {ops : α → α → Finset α} {goal : α} (key : α → ℕ) (p0 : α)
    (hp0 : ∀ z, ¬ key z < key p0) :
    ∀ (k : ℕ) (s : Finset α), minimal ops goal k s → cbuild ops goal key k p0 s := by
  intro k
  induction k with
  | zero => intro s hm; exact hm.1
  | succ k ih =>
    intro s hm
    have hex : ∃ n, ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, key z = n ∧
        build ops goal k (insert z s) := by
      rcases hm.1 with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
      · exact absurd skip (hm.2 k (by omega))
      · exact ⟨key z, a, ha, b, hb, hab, z, hz, rfl, tail⟩
    classical
    obtain ⟨a, ha, b, hb, hab, z, hz, hkey, tail⟩ := Nat.find_spec hex
    obtain ⟨hmt, hzs⟩ := minimal_tail hm ha hb hab hz tail
    have hc := ih (insert z s) hmt
    refine ⟨a, ha, b, hb, hab, z, hz, hzs, .inr (.inr (hp0 z)), ?_⟩
    cases k with
    | zero => exact hc
    | succ k =>
      obtain ⟨a2, ha2, b2, hb2, hab2, z2, hz2, hz2s, _, tail2⟩ := hc
      refine ⟨a2, ha2, b2, hb2, hab2, z2, hz2, hz2s, ?_, tail2⟩
      by_contra hno
      have h1 : a2 ≠ z := fun e => hno (.inl e)
      have h2 : b2 ≠ z := fun e => hno (.inr (.inl e))
      have h3 : key z2 < key z := by
        by_contra hge
        exact hno (.inr (.inr hge))
      have ha2s : a2 ∈ s := (Finset.mem_insert.mp ha2).resolve_left h1
      have hb2s : b2 ∈ s := (Finset.mem_insert.mp hb2).resolve_left h2
      have hlt : key z2 < Nat.find hex := by rw [← hkey]; exact h3
      apply Nat.find_min hex hlt
      refine ⟨a2, ha2s, b2, hb2s, hab2, z2, hz2, rfl, ?_⟩
      refine .inr ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, hab, z, hz, ?_⟩
      have hb3 := cbuild_build tail2
      rwa [Finset.insert_comm] at hb3

-- The live-set form of an ordered derivation.
def clive (ops : α → α → Finset α) (goal : α) (key : α → ℕ) : ℕ → α → Finset α → Prop
  | 0, _, s => s = {goal}
  | k + 1, p, s => clive ops goal key k p s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧ okp key p a b z ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ clive ops goal key k z (insert z rest)

theorem clive_live {ops : α → α → Finset α} {goal : α} {key : α → ℕ} {k : ℕ} {p : α}
    {s : Finset α} (h : clive ops goal key k p s) : live ops goal k s := by
  induction k generalizing p s with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, _, rest, hs, tail⟩
    · exact .inl (ih skip)
    · exact .inr ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs, ih tail⟩

theorem ccompress {ops : α → α → Finset α} {goal : α} {key : α → ℕ} {k : ℕ} {p : α}
    {available : Finset α} (hm : minimal ops goal k available)
    (h : cbuild ops goal key k p available) :
    ∃ s ⊆ available, clive ops goal key k p s := by
  induction k generalizing p available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    obtain ⟨a, ha, b, hb, hab, z, hz, hzout, hq, tail⟩ := h
    obtain ⟨hmt, _⟩ := minimal_tail hm ha hb hab hz (cbuild_build tail)
    obtain ⟨t, ht, hrun⟩ := ih hmt tail
    by_cases sub : t ⊆ available
    · exact absurd (build_mono sub (live_build (clive_live hrun))) (hm.2 k (by omega))
    · have hzmem : z ∈ t := by
        by_contra hn
        apply sub
        intro u hu
        rcases Finset.mem_insert.mp (ht hu) with rfl | ok
        · exact False.elim (hn hu)
        · exact ok
      let rest := t.erase z
      have hrest : rest ⊆ available := by
        intro u hu
        have hu' := Finset.mem_erase.mp hu
        exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
      let s := insert a (insert b rest)
      have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
      refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
        fun h => hzout (hs h), hq, rest, rfl, ?_⟩⟩
      simpa [rest, Finset.insert_erase hzmem] using hrun

theorem cfirst_live {ops : α → α → Finset α} {goal : α} {key : α → ℕ} {k : ℕ} {p : α}
    {s : Finset α} (h : clive ops goal key (k + 1) p s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧ okp key p a b z ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ clive ops goal key k z (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, hq, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, hq, r, hs, Or.inl tail⟩
    · exact .inr step

theorem cextend {ops : α → α → Finset α} {goal : α} {key : α → ℕ} {m n : ℕ} {p : α}
    {s : Finset α} (le : m ≤ n) (h : clive ops goal key m p s) : clive ops goal key n p s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Canon


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
  [0x80000000001fffff8102040810204081, 0x3ffffe000000204081020408102, 0xfffc00000000000c183060c183060c, 0x7f0000000000000070e1c3870e1c3870, 0x7f0000000fe00000850a142850a14285, 0x8001fc07f000007f1020408102040810, 0xfe000000003f802244891224489122, 0x3f8001fc0004891224489122448]

def inputs : List W := rawInputs

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

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
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

-- The ordered search. The guard is evaluated on the next list, whose head is the new wire: the gate
-- reads the previous output p or its output is not smaller, and the new wire is not already live.
def guardL (p a b : W) (r l : List W) : Bool :=
  (a == p || b == p || !(decide ((l.headD 0).toNat < p.toNat))) &&
    (l.headD 0 != a && l.headD 0 != b && !(r.contains (l.headD 0)))

def optC : ℕ → ℕ → W → List W → Bool
  | 0, _, _, ws => ws == [goal]
  | k + 1, extra, p, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) =>
      dispatch extra (fun e l => guardL p a b r l && optC k e (l.headD 0) l) a b r)

theorem optC_complete (n : ℕ) (ws : List W) (extra : ℕ) (p : W) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1)
    (h : clive basicOps goal BitVec.toNat n p ws.toFinset) :
    optC n extra p ws = true := by
  induction n generalizing ws extra p with
  | zero => simp [optC, singleton_list hn h]
  | succ k ih =>
    rcases cfirst_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, hq, needed, hs, tail⟩
    · simp [optC, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
          (hq : okp BitVec.toNat p a b z) :
          dispatch extra (fun e l => guardL p a b r l && optC k e (l.headD 0) l) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hcl : clive basicOps goal BitVec.toNat k z (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hl : live basicOps goal k (z :: kept).toFinset := clive_live hcl
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hzws : z ∉ ws := fun hmem => hout (List.mem_toFinset.mpr hmem)
        have hza : z ≠ a := fun e => hzws (perm.mem_iff.mpr (by simp [e]))
        have hzb : z ≠ b := fun e => hzws (perm.mem_iff.mpr (by simp [e]))
        have hzr : z ∉ r := fun hmem => hzws (perm.mem_iff.mpr (by simp [hmem]))
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        show (guardL p a b r (z :: kept) && optC k (k - kept.length) z (z :: kept)) = true
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · have hg : (a == p || b == p || !(decide (z.toNat < p.toNat))) = true := by
            rcases hq with h | h | h
            · simp [h]
            · simp [h]
            · simp [h]
          simp [guardL, hg, hza, hzb, hzr]
        · apply ih _ _ _ hnd _ hcl
          simp; omega
      simp only [optC, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz hq⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (ops_swap a b ▸ hz) (okp_swap hq)⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (5822 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 1), (2, 2), (3, 0)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 0), (1, 2), (2, 0), (2, 3), (3, 1), (3, 2), (3, 3)]

def pairIx (p : ℕ) : ℕ := if p < 63 then p else 0

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (pairIx k.val % 7) (0, 0) else posL.getD (pairIx (k.val - 64) / 7) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem all_front : inputs.sublists.all
    (fun l => decide (10 < l.length) || decide (l = inputs) || !(optC 9 (10 - l.length) 0 l)) = true := by
  decide +kernel

theorem all_of_chunks {β : Type} (F : β → Bool) (n : ℕ) : ∀ (m : ℕ) (L : List β), L.length ≤ n * m →
    (∀ j < m, ((L.drop (n * j)).take n).all F = true) → L.all F = true := by
  intro m
  induction m with
  | zero =>
    intro L hl _
    have h0 : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [h0]
  | succ m ih =>
    intro L hl h
    rw [← List.take_append_drop n L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ih (L.drop n) ?_ ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      generalize n * m = t at *
      omega
    · intro j hj
      have e : List.drop (n * j) (List.drop n L) = List.drop (n * (j + 1)) L := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [e]
      exact h (j + 1) (by omega)

def opt1 (c : Bool) (x : ℕ × List W) : List (ℕ × List W) := if c then [x] else []

theorem any_opt1 (c : Bool) (x : ℕ × List W) (f : ℕ × List W → Bool) :
    (opt1 c x).any f = (c && f x) := by
  cases c <;> simp [opt1]

-- The states that dispatch hands to the next level, as a list.
def wkids (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  opt1 (sep w ||| cuts r == -1) (extra, w :: r) ++
  (opt1 (extra != 0 && (sep w ||| cuts r ||| sep a == -1)) (extra - 1, w :: a :: r) ++
  (opt1 (extra != 0 && (sep w ||| cuts r ||| sep b == -1)) (extra - 1, w :: b :: r) ++
   opt1 (decide (extra ≥ 2) && (sep w ||| cuts r ||| sep a ||| sep b == -1)) (extra - 2, w :: a :: b :: r)))

def dkids (extra : ℕ) (a b : W) (r : List W) : List (ℕ × List W) :=
  (ops a b).flatMap (wkids extra a b r)

theorem bool_step (e1 e2 c1 c2 c3 c4 n1 n2 n3 n4 : Bool) :
    ((c1 && n1) || (e1 && ((c2 && n2) || (c3 && n3))) || ((e2 && c4) && n4)) =
    ((c1 && n1) || (((e1 && c2) && n2) || (((e1 && c3) && n3) || ((e2 && c4) && n4)))) := by
  cases e1 <;> cases e2 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;>
    cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> rfl

theorem wkids_any (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W) :
    (wkids extra a b r w).any (fun s => next s.1 s.2) =
    (((sep w ||| cuts r == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((sep w ||| cuts r ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((sep w ||| cuts r ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (sep w ||| cuts r ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))) := by
  simp only [wkids, List.any_append, any_opt1]
  exact (bool_step _ _ _ _ _ _ _ _ _ _).symm

theorem dispatch_eq (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) :
    dispatch extra next a b r = (dkids extra a b r).any (fun s => next s.1 s.2) := by
  unfold dkids
  rw [List.any_flatMap]
  show (ops a b).any _ = (ops a b).any _
  congr 1
  funext w
  exact (wkids_any extra next a b r w).symm

-- The next states of the ordered search: those of dispatch that pass the guard.
def kidsC (extra : ℕ) (p : W) (ws : List W) : List (ℕ × List W) :=
  (pairs ws).flatMap (fun q =>
    (dkids extra q.1 q.2.1 q.2.2).filter (fun s => guardL p q.1 q.2.1 q.2.2 s.2))

-- One level of the ordered search, written over the list of next states.
theorem optC_succ (k extra : ℕ) (p : W) (ws : List W) :
    optC (k + 1) extra p ws =
      (ws == [goal] || (kidsC extra p ws).any (fun s => optC k s.1 (s.2.headD 0) s.2)) := by
  unfold kidsC
  rw [List.any_flatMap]
  show (ws == [goal] || (pairs ws).any (fun (a, b, r) =>
      dispatch extra (fun e l => guardL p a b r l && optC k e (l.headD 0) l) a b r)) = _
  congr 2
  funext q
  obtain ⟨a, b, r⟩ := q
  show dispatch extra (fun e l => guardL p a b r l && optC k e (l.headD 0) l) a b r = _
  rw [dispatch_eq, List.any_filter]

theorem all_of_get {β : Type} (F : β → Bool) (d : β) (L : List β) (n : ℕ) (hn : L.length = n)
    (h : ∀ i < n, F (L.getD i d) = true) : L.all F = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hx2 := h i (hn ▸ hi)
  rw [List.getD_eq_getElem _ _ hi] at hx2
  exact hx2

-- A state fails when it is not the goal and all of its next states fail one level down.
theorem heavyC (k : ℕ) (s : ℕ × List W) (hg : (s.2 == [goal]) = false)
    (h : (kidsC s.1 (s.2.headD 0) s.2).all (fun t => !(optC k t.1 (t.2.headD 0) t.2)) = true) :
    (!(optC (k + 1) s.1 (s.2.headD 0) s.2)) = true := by
  rw [optC_succ, hg, Bool.false_or, Bool.not_eq_true', List.any_eq_false]
  intro t ht
  have h2 := List.all_eq_true.mp h t ht
  simpa using h2

def front1 : List (ℕ × List W) := kidsC 2 0 inputs

def okS (s : ℕ × List W) : Bool := !(optC 8 s.1 (s.2.headD 0) s.2)

def okT (t : ℕ × List W) : Bool := !(optC 7 t.1 (t.2.headD 0) t.2)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_0 : okS (front1.getD 0 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_1 : okS (front1.getD 1 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_2 : okS (front1.getD 2 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_3 : okS (front1.getD 3 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_4 : okS (front1.getD 4 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_5 : okS (front1.getD 5 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_6 : okS (front1.getD 6 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_7 : okS (front1.getD 7 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_8 : okS (front1.getD 8 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_9 : okS (front1.getD 9 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_10 : okS (front1.getD 10 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_11 : okS (front1.getD 11 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_12 : okS (front1.getD 12 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_13 : okS (front1.getD 13 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_14 : okS (front1.getD 14 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_15 : okS (front1.getD 15 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_16 : okS (front1.getD 16 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_17 : okS (front1.getD 17 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_18 : okS (front1.getD 18 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_19 : okS (front1.getD 19 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_20 : okS (front1.getD 20 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_21 : okS (front1.getD 21 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_22 : okS (front1.getD 22 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_23 : okS (front1.getD 23 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_24 : okS (front1.getD 24 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_25 : okS (front1.getD 25 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_26 : okS (front1.getD 26 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_27 : okS (front1.getD 27 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_28 : okS (front1.getD 28 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_29 : okS (front1.getD 29 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_30 : okS (front1.getD 30 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_31 : okS (front1.getD 31 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_32 : okS (front1.getD 32 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_33 : okS (front1.getD 33 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_34 : okS (front1.getD 34 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_35 : okS (front1.getD 35 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_36 : okS (front1.getD 36 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_37 : okS (front1.getD 37 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_38 : okS (front1.getD 38 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_39 : okS (front1.getD 39 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_40 : okS (front1.getD 40 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_41 : okS (front1.getD 41 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_42 : okS (front1.getD 42 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_43 : okS (front1.getD 43 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_44 : okS (front1.getD 44 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_45 : okS (front1.getD 45 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_46 : okS (front1.getD 46 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_47 : okS (front1.getD 47 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_48 : okS (front1.getD 48 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_49 : okS (front1.getD 49 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_50 : okS (front1.getD 50 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_51 : okS (front1.getD 51 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_52 : okS (front1.getD 52 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_53 : okS (front1.getD 53 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_54 : okS (front1.getD 54 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_55 : okS (front1.getD 55 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_56 : okS (front1.getD 56 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_57 : okS (front1.getD 57 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_58 : okS (front1.getD 58 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_59 : okS (front1.getD 59 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_60 : okS (front1.getD 60 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_61 : okS (front1.getD 61 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_62 : okS (front1.getD 62 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_63 : okS (front1.getD 63 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_64 : okS (front1.getD 64 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_65 : okS (front1.getD 65 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_66 : okS (front1.getD 66 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_67 : okS (front1.getD 67 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_68 : okS (front1.getD 68 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_69 : okS (front1.getD 69 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_70 : okS (front1.getD 70 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_71 : okS (front1.getD 71 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_72 : okS (front1.getD 72 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_73 : okS (front1.getD 73 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_74 : okS (front1.getD 74 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_75 : okS (front1.getD 75 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_76 : okS (front1.getD 76 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_77 : okS (front1.getD 77 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_78 : okS (front1.getD 78 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_79 : okS (front1.getD 79 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_80 : okS (front1.getD 80 (0, [])) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem s1_81 : okS (front1.getD 81 (0, [])) = true := by
  decide +kernel

theorem front1_len : front1.length = 82 := by decide +kernel

theorem front1_ok : front1.all okS = true :=
  all_of_get okS (0, []) front1 82 front1_len (fun i hi => by
    interval_cases i
    exacts [s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6, s1_7, s1_8, s1_9, s1_10, s1_11, s1_12, s1_13, s1_14, s1_15, s1_16, s1_17, s1_18, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27, s1_28, s1_29, s1_30, s1_31, s1_32, s1_33, s1_34, s1_35, s1_36, s1_37, s1_38, s1_39, s1_40, s1_41, s1_42, s1_43, s1_44, s1_45, s1_46, s1_47, s1_48, s1_49, s1_50, s1_51, s1_52, s1_53, s1_54, s1_55, s1_56, s1_57, s1_58, s1_59, s1_60, s1_61, s1_62, s1_63, s1_64, s1_65, s1_66, s1_67, s1_68, s1_69, s1_70, s1_71, s1_72, s1_73, s1_74, s1_75, s1_76, s1_77, s1_78, s1_79, s1_80, s1_81])

theorem full_search : optC 9 2 0 inputs = false := by
  have h := List.all_eq_true.mp front1_ok
  show optC (8 + 1) 2 0 inputs = false
  rw [optC_succ, Bool.or_eq_false_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.any_eq_false]
  intro s hs
  have hx := h s hs
  simpa [okS] using hx

theorem len_one : 10 - inputs.length = 2 := by decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  have hb := get_build C hm hr
  classical
  have hex : ∃ k, build basicOps goal k inputs.toFinset := ⟨_, hb⟩
  have hmin : minimal basicOps goal (Nat.find hex) inputs.toFinset :=
    ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hle : Nat.find hex ≤ 9 := (Nat.find_min' hex hb).trans hs
  obtain ⟨S, hsub, hl⟩ := ccompress hmin
    (canon BitVec.toNat (0 : W) (by intro z; simp) _ _ hmin)
  have hl3 : clive basicOps goal BitVec.toNat 9 (0 : W) S := cextend hle hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card (clive_live hl3)
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optC_complete 9 l (10 - l.length) 0 hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (10 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  have hli : l = inputs := by simpa using hrow
  rw [hli, len_one, full_search] at hsearch
  exact Bool.noConfusion hsearch

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] },
      { op := GateOp.or, inputs := [0, 2] },
      { op := GateOp.or, inputs := [9, 4] },
      { op := GateOp.or, inputs := [1, 3] },
      { op := GateOp.or, inputs := [11, 5] },
      { op := GateOp.or, inputs := [12, 6] },
      { op := GateOp.and, inputs := [13, 10] },
      { op := GateOp.or, inputs := [5, 7] },
      { op := GateOp.and, inputs := [15, 8] },
      { op := GateOp.or, inputs := [16, 14] }],
    output := 17 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_6376

theorem PEqualNP.Outside.L_meta_6376 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5822 : ℕ).testBit (4 * u.val + v.val)) 10 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5822 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨⟨PEqualNP.Outside.L_meta_6376.upperC, PEqualNP.Outside.L_meta_6376.upper_mono,
    by decide, PEqualNP.Outside.L_meta_6376.upper_rep⟩, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_6376.no_small C hm hs hr
