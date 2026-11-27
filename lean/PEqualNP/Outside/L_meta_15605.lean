import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15605

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def build {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {available : Finset α} (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
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

theorem first_live {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {s : Finset α} (h : live ops goal (k + 1) s) :
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

abbrev W (P : ℕ) := BitVec (P + P)
def ops {P : ℕ} (x y : W P) : List (W P) := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep {P : ℕ} (x : W P) : BitVec P := ((x >>> P) ^^^ x).setWidth P
def goal (P : ℕ) : W P := BitVec.allOnes P ++ (0 : BitVec P)

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

abbrev basicOps {P : ℕ} (a b : W P) : Finset (W P) := (ops a b).toFinset

def differs {P : ℕ} (i : Fin P) (w : W P) : Prop :=
  w.getLsbD (P + i.val) ≠ w.getLsbD i.val

theorem ops_differs {P : ℕ} (i : Fin P) (a b z : W P) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : P + i.val < P + P := by omega
  have hi' : i.val < P + P := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

def mkE {P : ℕ} (w : W P) : W P × BitVec P := (w, sep w)
def cutsE {P : ℕ} (ws : List (W P × BitVec P)) : BitVec P := ws.foldr (fun w v => w.2 ||| v) 0

def memW {P : ℕ} (w : W P) : List (W P × BitVec P) → Bool
  | [] => false
  | x :: xs => (w == x.1) || memW w xs

theorem memW_map_mkE {P : ℕ} (w : W P) (r : List (W P)) :
    memW w (r.map mkE) = true ↔ w ∈ r := by
  induction r with
  | nil => simp [memW]
  | cons x xs ih => simp [memW, mkE, ih]

theorem cutsE_spec {P : ℕ} (ws : List (W P)) (i : Fin P) :
    (cutsE (ws.map mkE)).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cutsE]
  | cons a rest ih =>
    change (sep a ||| cutsE (rest.map mkE)).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, bx]

theorem goal_getLsbD_lo {P : ℕ} (i : ℕ) (hi : i < P) : (goal P).getLsbD i = false := by
  simp [goal, BitVec.getLsbD_append, hi]

theorem goal_getLsbD_hi {P : ℕ} (i : ℕ) (hi : i < P) : (goal P).getLsbD (P + i) = true := by
  have h1 : ¬ (P + i < P) := by omega
  have h2 : P + i - P = i := by omega
  rw [goal, BitVec.getLsbD_append]
  simp only [h1, ↓reduceIte, h2, BitVec.getLsbD_allOnes, hi, decide_true]

theorem goal_differs {P : ℕ} {g : W P} (hg : g = goal P ∨ g = ~~~goal P) (i : Fin P) :
    differs i g := by
  unfold differs
  have hlo := goal_getLsbD_lo i.val i.isLt
  have hhi := goal_getLsbD_hi i.val i.isLt
  have h1 : P + i.val < P + P := by omega
  have h2 : i.val < P + P := by omega
  rcases hg with rfl | rfl
  · simp [hlo, hhi]
  · rw [BitVec.getLsbD_not, BitVec.getLsbD_not, hlo, hhi]
    simp [h1, h2]

theorem goal_ne_const {P : ℕ} (hP : 0 < P) {g : W P} (hg : g = goal P ∨ g = ~~~goal P) :
    g ≠ 0 ∧ g ≠ ~~~0 := by
  have hd := goal_differs hg ⟨0, hP⟩
  unfold differs at hd
  have h1 : P + 0 < P + P := by omega
  have h2 : 0 < P + P := by omega
  constructor
  · intro heq; subst heq; simp at hd
  · intro heq; subst heq; rw [BitVec.getLsbD_not, BitVec.getLsbD_not] at hd; simp [h2] at hd; omega

theorem cutsE_full {P : ℕ} {g : W P} (hg : g = goal P ∨ g = ~~~goal P) {k : ℕ} {ws : List (W P)}
    (h : live basicOps g k ws.toFinset) : cutsE (ws.map mkE) = BitVec.allOnes P := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs hg ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cutsE_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap {P : ℕ} (a b : W P) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
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

theorem singleton_list {α : Type} [DecidableEq α] {g : α} {ws : List α} (hn : ws.Nodup)
    (hs : ws.toFinset = {g}) : ws = [g] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def isGoalPair {P : ℕ} (g ng : W P) (a b : W P) : Bool :=
  (ops a b).any fun w => w == g || w == ng

def dispatchE {P : ℕ} (extra : ℕ) (next : ℕ → List (W P × BitVec P) → Bool)
    (a b : W P × BitVec P) (r : List (W P × BitVec P)) : Bool :=
  let base := cutsE r
  (ops a.1 b.1).any fun w =>
    if w == a.1 || w == b.1 || memW w r then false else
    let sw := sep w
    let v := sw ||| base
    ((v == BitVec.allOnes P) && next extra ((w, sw) :: r)) ||
    ((extra != 0) && (((v ||| a.2 == BitVec.allOnes P) && next (extra - 1) ((w, sw) :: a :: r)) ||
                       ((v ||| b.2 == BitVec.allOnes P) && next (extra - 1) ((w, sw) :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| a.2 ||| b.2 == BitVec.allOnes P) && next (extra - 2) ((w, sw) :: a :: b :: r))

def optimizedE {P : ℕ} (g ng : W P) : ℕ → ℕ → List (W P × BitVec P) → Bool
  | 0, _, ws => match ws with | [x] => x.1 == g || x.1 == ng | _ => false
  | 1, _, ws => match ws with
    | [x] => x.1 == g || x.1 == ng
    | [a, b] => isGoalPair g ng a.1 b.1
    | _ => false
  | k + 2, extra, ws =>
    (match ws with | [x] => x.1 == g || x.1 == ng | _ => false) ||
    (pairs ws).any (fun (a, b, r) => dispatchE extra (optimizedE g ng (k + 1)) a b r)

def searchE {P : ℕ} (n : ℕ) (inputs : List (W P)) : Bool :=
  let g := goal P
  let ng := ~~~g
  (inputs.map mkE).sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsE ws == BitVec.allOnes P) && optimizedE g ng n (n + 1 - ws.length) ws


theorem dispatchE_complete {P : ℕ} {k extra : ℕ} {a b z : W P} {r kept : List (W P)}
    (next : ℕ → List (W P × BitVec P) → Bool)
    (hz : z ∈ basicOps a b) (hfresh : z ≠ a ∧ z ≠ b ∧ z ∉ r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cutsE ((z :: kept).map mkE) = BitVec.allOnes P)
    (ht : next (k - kept.length) ((z :: kept).map mkE) = true) :
    dispatchE extra next (mkE a) (mkE b) (r.map mkE) = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have hcond : (z == a || z == b || memW z (r.map mkE)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨hfresh.1, hfresh.2.1⟩, by
      cases hm : memW z (r.map mkE) with
      | false => rfl
      | true => exact False.elim (hfresh.2.2 ((memW_map_mkE z r).mp hm))⟩
  simp only [mkE, hcond, Bool.false_eq_true, ↓reduceIte]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, mkE, cutsE, List.foldr_cons] at hc ht ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimizedE_complete {P : ℕ} {g : W P} (hg : g = goal P ∨ g = ~~~goal P) (n : ℕ)
    (ws : List (W P)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimizedE (goal P) (~~~goal P) n extra (ws.map mkE) = true := by
  induction n generalizing ws extra with
  | zero =>
    rw [singleton_list hn h]
    rcases hg with rfl | rfl <;> simp [optimizedE, mkE]
  | succ k ih =>
    cases k with
    | zero =>
      rcases first_live (k := 0) h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
      · rw [singleton_list hn done]
        rcases hg with rfl | rfl <;> simp [optimizedE, mkE]
      · change insert z needed = {g} at tail
        have hzg : z = g := by
          have : z ∈ insert z needed := Finset.mem_insert_self z needed
          rw [tail] at this; exact Finset.mem_singleton.mp this
        have hne_empty : needed = ∅ := by
          ext u
          simp only [Finset.notMem_empty, iff_false]
          intro hu
          have hug : u = g := by
            have : u ∈ insert z needed := Finset.mem_insert_of_mem hu
            rw [tail] at this; exact Finset.mem_singleton.mp this
          apply hout
          rw [hzg, ← hug, hs]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
        rw [hne_empty] at hs
        have hs2 : ws.toFinset = {a, b} := by simpa using hs
        have hcard : ws.length = 2 := by
          have hc := List.toFinset_card_of_nodup hn
          rw [hs2, Finset.card_pair hab] at hc
          exact hc.symm
        rcases ws with _ | ⟨u, _ | ⟨v, _ | ⟨w0, ws'⟩⟩⟩ <;> simp at hcard
        have huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
          have hu_mem : u ∈ ({a, b} : Finset (W P)) := by rw [← hs2]; simp
          have hv_mem : v ∈ ({a, b} : Finset (W P)) := by rw [← hs2]; simp
          have hne_uv : u ≠ v := by
            have := (List.nodup_cons.mp hn).1
            simpa using this
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem hv_mem
          rcases hu_mem with rfl | rfl <;> rcases hv_mem with rfl | rfl
          · exact False.elim (hne_uv rfl)
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact False.elim (hne_uv rfl)
        simp only [List.map_cons, List.map_nil, optimizedE, mkE, isGoalPair, List.any_eq_true,
          Bool.or_eq_true, beq_iff_eq]
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨z, List.mem_toFinset.mp hz, by rwa [hzg]⟩
        · rw [ops_swap] at hz; exact ⟨z, List.mem_toFinset.mp hz, by rwa [hzg]⟩
    | succ k' =>
      rcases first_live (k := k' + 1) h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
      · rw [singleton_list hn done]
        rcases hg with rfl | rfl <;> simp [optimizedE, mkE]
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go {a b : W P} (perm : ws.Perm (a :: b :: r))
            (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
            dispatchE extra (optimizedE (goal P) (~~~goal P) (k' + 1)) (mkE a) (mkE b) (r.map mkE) = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu; apply hout; rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hfresh : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
            refine ⟨?_, ?_, ?_⟩
            · intro e; apply hout; rw [List.mem_toFinset, perm.mem_iff]; simp [e]
            · intro e; apply hout; rw [List.mem_toFinset, perm.mem_iff]; simp [e]
            · intro hr; apply hout; rw [List.mem_toFinset, perm.mem_iff]; simp [hr]
          have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
          have hl : live basicOps g (k' + 1) (z :: kept).toFinset := by simpa [hfin] using tail
          have hc := live_card hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          apply dispatchE_complete (k := k' + 1) (extra := extra)
            (optimizedE (goal P) (~~~goal P) (k' + 1)) hop hfresh hk (by omega) (by omega) (cutsE_full hg hl)
          apply ih _ _ hnd _ hl
          simp; omega
        have hpairs_map : ∀ {xs : List (W P)} {x y : W P} {rest : List (W P)},
            (x, y, rest) ∈ pairs xs → (mkE x, mkE y, rest.map mkE) ∈ pairs (xs.map mkE) := by
          intro xs
          have hsing : ∀ {ys : List (W P)} {u : W P} {rs : List (W P)},
              (u, rs) ∈ singles ys → (mkE u, rs.map mkE) ∈ singles (ys.map mkE) := by
            intro ys
            induction ys with
            | nil => intro u rs h; simp [singles] at h
            | cons h0 t0 iht =>
              intro u rs h
              simp only [singles, List.map_cons, List.mem_cons, List.mem_map, Prod.mk.injEq] at h ⊢
              rcases h with ⟨rfl, rfl⟩ | ⟨⟨b0, bs0⟩, hb0, rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨(mkE b0, bs0.map mkE), iht hb0, rfl, rfl⟩
          induction xs with
          | nil => intro x y rest h; simp [pairs] at h
          | cons h0 t0 iht =>
            intro x y rest h
            simp only [pairs, List.map_cons, List.mem_append, List.mem_map, Prod.mk.injEq] at h ⊢
            rcases h with ⟨⟨b0, bs0⟩, hb0, rfl, rfl, rfl⟩ | ⟨⟨b0, c0, bs0⟩, hb0, rfl, rfl, rfl⟩
            · exact Or.inl ⟨(mkE b0, bs0.map mkE), hsing hb0, rfl, rfl, rfl⟩
            · exact Or.inr ⟨(mkE b0, mkE c0, bs0.map mkE), iht hb0, rfl, rfl, rfl⟩
        simp only [optimizedE, Bool.or_eq_true, List.any_eq_true]
        right
        rcases hm with direct | swap
        · exact ⟨(mkE a, mkE b, r.map mkE), hpairs_map direct, go hp hs hz⟩
        · exact ⟨(mkE b, mkE a, r.map mkE), hpairs_map swap,
            go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem searchE_complete {P : ℕ} {g : W P} (hg : g = goal P ∨ g = ~~~goal P) (n : ℕ)
    (inputs : List (W P)) (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) :
    searchE n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hsub : (ws.map mkE).Sublist (inputs.map mkE) := (List.filter_sublist ..).map mkE
  refine List.any_eq_true.mpr ⟨ws.map mkE, List.mem_sublists.mpr hsub, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.length_map]
  exact ⟨⟨sz, cutsE_full hg hl'⟩, optimizedE_complete hg n ws (n + 1 - ws.length) hnd (by omega) hl'⟩

def holds {P : ℕ} (av : Finset (W P)) (z : W P) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {P : ℕ} {av av' : Finset (W P)} (sub : av ⊆ av') {x : W P} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a, ha, e⟩ => ⟨a, sub ha, e⟩)

theorem holds_not {P : ℕ} {av : Finset (W P)} {z : W P} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable {P : ℕ} (av : Finset (W P)) (z : W P) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {P : ℕ} {av : Finset (W P)} {z : W P} (h : reachable av z) :
    reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem not_zero_eq {n : ℕ} : ~~~(0 : BitVec n) = BitVec.allOnes n := by
  apply BitVec.eq_of_getElem_eq; intro j hj; simp

set_option maxRecDepth 5000 in
theorem and_reach {P : ℕ} {av : Finset (W P)} {x y : W P} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W P) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W P) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · rw [not_zero_eq, BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W P) = 0 from BitVec.and_zero]; exact .inl const
  · rw [not_zero_eq, BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W P) (hw : w ∈ basicOps a b) (z : W P) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self w av, hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add (a &&& b) (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add (a &&& ~~~b) (by simp [basicOps, ops]) _ (.inl rfl)
  · exact add (b &&& ~~~a) (by simp [basicOps, ops]) _ (.inl (BitVec.and_comm _ _))
  · exact add (a ||| b) (by simp [basicOps, ops]) _ (.inr (by rw [BitVec.not_or]))

theorem or_reach {P : ℕ} {av : Finset (W P)} {x y : W P} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  have demorgan : x ||| y = ~~~(~~~x &&& ~~~y) := by rw [BitVec.not_and, BitVec.not_not, BitVec.not_not]
  rw [demorgan]
  exact reachable_not (and_reach (holds_not hx) (holds_not hy))

def legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def isBinary (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def binaryCost (gs : List Gate) : ℕ := (gs.filter isBinary).length

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def action {P : ℕ} (w : List (W P)) (g : Gate) : W P :=
  let args := g.inputs.map fun i => w.getD i 0
  match g.op with
  | GateOp.and => args.foldr (· &&& ·) (~~~0)
  | GateOp.or => args.foldr (· ||| ·) 0
  | GateOp.not => (args.head?.map (~~~·)).getD (~~~0)
  | _ => 0

def bit {P : ℕ} (k : Fin (P + P)) (w : W P) : Bool := w[k.val]

theorem read_bit {P : ℕ} (k : Fin (P + P)) (w : List (W P)) (i : ℕ) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases hi : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  · have h1 : w.length ≤ i := Nat.le_of_not_lt hi
    have h2 : (w.map (bit k)).length ≤ i := by simpa using h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2, bit]

theorem foldr_and_bit {P : ℕ} (k : Fin (P + P)) (xs : List (W P)) :
    bit k (xs.foldr (· &&& ·) (~~~0)) = (xs.map (bit k)).all id := by
  induction xs with
  | nil => simp [bit]
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, List.all_cons, id_eq, bit, BitVec.getElem_and] at ih ⊢
    rw [ih]

theorem foldr_or_bit {P : ℕ} (k : Fin (P + P)) (xs : List (W P)) :
    bit k (xs.foldr (· ||| ·) 0) = (xs.map (bit k)).any id := by
  induction xs with
  | nil => simp [bit]
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, List.any_cons, id_eq, bit, BitVec.getElem_or] at ih ⊢
    rw [ih]

theorem action_spec {P : ℕ} (w : List (W P)) (g : Gate) (hg : legal g) (k : Fin (P + P)) :
    (w ++ [action w g]).map (bit k) = step (w.map (bit k)) g := by
  simp only [List.map_append, List.map_cons, List.map_nil, step]
  congr 1; congr 1
  have read : (g.inputs.map fun i => w.getD i 0).map (bit k) =
      g.inputs.map fun i => (w.map (bit k)).getD i false := by
    rw [List.map_map]; apply List.map_congr_left; intro i _; exact (read_bit k w i).symm
  rcases hg.1 with hop | hop | hop <;> simp only [action, GateOp.eval, hop]
  · rw [foldr_and_bit, read]
  · rw [foldr_or_bit, read]
  · cases h : g.inputs with
    | nil => simp [bit]
    | cons i _ =>
      simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some,
        List.headD_cons, bit, BitVec.getElem_not]
      rw [read_bit k w i]; rfl

theorem available_read {P : ℕ} {w : List (W P)} {av : Finset (W P)}
    (hw : ∀ u ∈ w, holds av u) (i : ℕ) : holds av (w.getD i 0) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; exact .inl rfl

theorem gate_reach {P : ℕ} (w : List (W P)) (av : Finset (W P)) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [isBinary, Bool.false_eq_true, ite_false, ite_true, action, List.head?_nil,
      List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
      Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
      show ∀ x : W P, x ||| (0 : W P) = x from fun x => BitVec.or_zero,
      show ∀ x : W P, x &&& ~~~(0 : W P) = x from fun x => by rw [not_zero_eq, BitVec.and_allOnes]]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

def SignedBuild {P : ℕ} (k : ℕ) (av : Finset (W P)) (z : W P) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {P : ℕ} {av : Finset (W P)} {z : W P} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a, ha, rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not, build] using ha)))

theorem sb_wait {P : ℕ} {av : Finset (W P)} {z : W P} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k + 1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {P : ℕ} {av : Finset (W P)} {z : W P} {k l : ℕ} (hkl : k ≤ l)
    (h : SignedBuild k av z) : SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {P : ℕ} {av : Finset (W P)} {t a b z : W P} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k + 1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩) (.inr ⟨a, ha, b, hb, hne, z, hz, ·⟩)))

theorem sb_advance {P : ℕ} {av : Finset (W P)} {z t : W P} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset (W P), av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k + 1) av t := by
  rcases hz with h | ⟨a, ha, b, hb, hn, w, hw, ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {P : ℕ} {av : Finset (W P)} {x y z : W P} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

theorem mem_ops_zero {P : ℕ} {av : Finset (W P)} {x y z : W P} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have hc : holds av (0 : W P) := .inl rfl
  have absorb (v : W P) : v &&& (~~~(0 : W P)) = v :=
    (congrArg (fun u : W P => v &&& u) (BitVec.not_zero (n := P + P))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {P1 P2 : ℕ} {f : W P1 → W P2}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W P1} {k : ℕ} {s : Finset (W P1)} {av : Finset (W P2)}
    (run : live basicOps g k s) (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_wait (ih skip hav)
    · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
      intro av' sub ok
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hr
      · exact ok
      · exact holds_mono sub (hav u (by simp [he, hr]))

theorem sb_to_build {P : ℕ} (hP : 0 < P) {k : ℕ} {av : Finset (W P)} {t : W P}
    (ht : t = goal P ∨ t = ~~~goal P) (h : SignedBuild k av t) :
    ∃ u, (u = goal P ∨ u = ~~~goal P) ∧ build basicOps u k av := by
  have hne := goal_ne_const hP ht
  rcases h with c | c | run | run
  · exact False.elim (hne.1 c)
  · exact False.elim (hne.2 c)
  · exact ⟨t, ht, run⟩
  · refine ⟨~~~t, ?_, run⟩
    rcases ht with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl BitVec.not_not

theorem reject_base {P : ℕ} (hP : 0 < P) (n : ℕ) (inputs : List (W P)) (hn : inputs.Nodup)
    (hno : searchE n inputs = false) {t : W P} (ht : t = goal P ∨ t = ~~~goal P)
    (h : SignedBuild n inputs.toFinset t) : False := by
  obtain ⟨u, hu, run⟩ := sb_to_build hP ht h
  exact Bool.noConfusion (hno.symm.trans (searchE_complete hu n inputs hn run))


theorem compileTarget {P : ℕ} (target : W P) (ht0 : target ≠ 0) (ht1 : target ≠ ~~~0)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (W P)) (av : Finset (W P)) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k : Fin (P + P), (gs.foldl step (w.map (bit k))).getD out false = bit k target) :
    ∃ t, (t = target ∨ t = ~~~target) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (ht0 zero)
    · exact False.elim (ht1 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun x : W P => ~~~x) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k : Fin (P + P), (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k target := by
      intro k; rw [stepOK k]; exact he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (W P)) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

theorem mem_ops_const {P : ℕ} {av : Finset (W P)} {x y z : W P} (hx : holds av x) (hy : holds av y)
    (hconst : (x = 0 ∨ x = ~~~0) ∨ (y = 0 ∨ y = ~~~0)) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  have hc0 : holds av (0 : W P) := .inl rfl
  have hc1 : holds av (~~~(0 : W P)) := .inr (.inl rfl)
  have za (v : W P) : (0 : W P) &&& v = 0 := BitVec.zero_and
  have az (v : W P) : v &&& (0 : W P) = 0 := BitVec.and_zero
  have zo (v : W P) : (0 : W P) ||| v = v := BitVec.zero_or
  have oz (v : W P) : v ||| (0 : W P) = v := BitVec.or_zero
  have absorb (v : W P) : v &&& (~~~(0 : W P)) = v :=
    (congrArg (fun u : W P => v &&& u) not_zero_eq).trans BitVec.and_allOnes
  have absorbL (v : W P) : (~~~(0 : W P)) &&& v = v :=
    (congrArg (fun u : W P => u &&& v) not_zero_eq).trans BitVec.allOnes_and
  have or1L (v : W P) : (~~~(0 : W P)) ||| v = ~~~0 := by
    rw [not_zero_eq, BitVec.allOnes_or]
  have or1R (v : W P) : v ||| (~~~(0 : W P)) = ~~~0 := by
    rw [not_zero_eq, BitVec.or_allOnes]
  have n1 : ~~~(~~~(0 : W P)) = 0 := BitVec.not_not
  rcases hconst with (rfl | rfl) | (rfl | rfl) <;> rcases hz with rfl | rfl | rfl | rfl <;>
    first
    | (rw [za]; exact hc0)
    | (rw [az]; exact hc0)
    | (rw [zo]; exact hy)
    | (rw [oz]; exact hx)
    | (rw [absorb]; exact hx)
    | (rw [absorb]; exact hy)
    | (rw [absorbL]; exact hy)
    | (rw [absorbL]; exact holds_not hy)
    | (rw [absorbL]; exact holds_not hx)
    | (rw [or1L]; exact hc1)
    | (rw [or1R]; exact hc1)
    | (rw [n1, az]; exact hc0)

theorem live_transport_const_save {P1 P2 : ℕ} {f : W P1 → W P2}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W P1} {k : ℕ} {s : Finset (W P1)} {av : Finset (W P2)}
    (run : live basicOps g k s) (hp : p ∈ s) (hpg : p ≠ g)
    (hconst : f p = 0 ∨ f p = ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k - 1) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
    simp only [Nat.add_sub_cancel] at *
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases touches : p = a ∨ p = b
      · have zz : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
          touches.elim (fun h => .inl (h ▸ hconst)) (fun h => .inr (h ▸ hconst))
        have collapsed := mem_ops_const (hav a ha) (hav b hb) zz mapped
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
        have cost : (k - 1) + 1 = k := by omega
        rw [← cost]
        apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
        intro av' sub ok
        apply ih tail pt
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (inOld u hr)

theorem index_of_op {P : ℕ} (a b z : W P) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

def in6 : List (W 32) :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def v6 (i : Fin 6) : W 32 := in6.getD i.val 0

lemma in6_index (w : W 32) (hw : w ∈ in6) : ∃ i : Fin 6, w = v6 i := by
  simp only [in6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

theorem mem_ops_both_const {P : ℕ} {x y z : W P}
    (hx : x = 0 ∨ x = ~~~0) (hy : y = 0 ∨ y = ~~~0) (hz : z ∈ basicOps x y) :
    z = 0 ∨ z = ~~~0 := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp [BitVec.and_zero, BitVec.or_zero]

theorem live_transport_const_save2 {P1 P2 : ℕ} {f : W P1 → W P2}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p1 p2 : W P1} {k : ℕ} {s : Finset (W P1)} {av : Finset (W P2)}
    (run : live basicOps g k s)
    (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (hp12 : p1 ≠ p2)
    (hp1g : p1 ≠ g) (hp2g : p2 ≠ g)
    (hc1 : f p1 = 0 ∨ f p1 = ~~~0) (hc2 : f p2 = 0 ∨ f p2 = ~~~0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k - 2) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    exact False.elim (hp1g (by simpa [run] using hp1))
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hn, z, hz, hout, r, he, tail⟩
    · exact sb_le (by omega) (ih skip hp1 hp2 hav)
    · have mapped := hm a b z hz
      have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he, hu])
      by_cases t1 : p1 = a ∨ p1 = b
      · by_cases t2 : p2 = a ∨ p2 = b
        · have hfa : f a = 0 ∨ f a = ~~~0 := by
            rcases t1 with rfl | rfl
            · exact hc1
            · rcases t2 with rfl | h2
              · exact hc2
              · exact False.elim (hp12 h2.symm)
          have hfb : f b = 0 ∨ f b = ~~~0 := by
            rcases t1 with h1 | rfl
            · rcases t2 with h2 | rfl
              · exact False.elim (hp12 (h1.trans h2.symm))
              · exact hc2
            · exact hc1
          have hfz : f z = 0 ∨ f z = ~~~0 := mem_ops_both_const hfa hfb mapped
          by_cases hzg : z = g
          · subst hzg
            exact hfz.imp_right Or.inl
          · have hav' : ∀ u ∈ insert z r, holds av (f u) := by
              intro u hu
              rcases Finset.mem_insert.mp hu with rfl | hr
              · exact hfz.imp_right Or.inl
              · exact inOld u hr
            have hsb := live_transport_const_save hm tail (Finset.mem_insert_self z r) hzg hfz hav'
            exact sb_le (by omega) hsb
        · have p2r : p2 ∈ r := by
            rw [he] at hp2
            rcases Finset.mem_insert.mp hp2 with h | h
            · exact False.elim (t2 (.inl h))
            · rcases Finset.mem_insert.mp h with h | h
              · exact False.elim (t2 (.inr h))
              · exact h
          have zz : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
            t1.elim (fun h => .inl (h ▸ hc1)) (fun h => .inr (h ▸ hc1))
          have collapsed := mem_ops_const (hav a ha) (hav b hb) zz mapped
          have hav' : ∀ u ∈ insert z r, holds av (f u) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact collapsed
            · exact inOld u hr
          have hsb := live_transport_const_save hm tail (Finset.mem_insert_of_mem p2r) hp2g hc2 hav'
          exact sb_le (by omega) hsb
      · by_cases t2 : p2 = a ∨ p2 = b
        · have p1r : p1 ∈ r := by
            rw [he] at hp1
            rcases Finset.mem_insert.mp hp1 with h | h
            · exact False.elim (t1 (.inl h))
            · rcases Finset.mem_insert.mp h with h | h
              · exact False.elim (t1 (.inr h))
              · exact h
          have zz : (f a = 0 ∨ f a = ~~~0) ∨ (f b = 0 ∨ f b = ~~~0) :=
            t2.elim (fun h => .inl (h ▸ hc2)) (fun h => .inr (h ▸ hc2))
          have collapsed := mem_ops_const (hav a ha) (hav b hb) zz mapped
          have hav' : ∀ u ∈ insert z r, holds av (f u) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact collapsed
            · exact inOld u hr
          have hsb := live_transport_const_save hm tail (Finset.mem_insert_of_mem p1r) hp1g hc1 hav'
          exact sb_le (by omega) hsb
        · have p1r : p1 ∈ r := by
            rw [he] at hp1
            rcases Finset.mem_insert.mp hp1 with h | h
            · exact False.elim (t1 (.inl h))
            · rcases Finset.mem_insert.mp h with h | h
              · exact False.elim (t1 (.inr h))
              · exact h
          have p2r : p2 ∈ r := by
            rw [he] at hp2
            rcases Finset.mem_insert.mp hp2 with h | h
            · exact False.elim (t2 (.inl h))
            · rcases Finset.mem_insert.mp h with h | h
              · exact False.elim (t2 (.inr h))
              · exact h
          have p1t : p1 ∈ insert z r := Finset.mem_insert_of_mem p1r
          have p2t : p2 ∈ insert z r := Finset.mem_insert_of_mem p2r
          by_cases hk2 : 2 ≤ k
          · have cost : (k - 2) + 1 = (k + 1) - 2 := by omega
            rw [← cost]
            apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
            intro av' sub ok
            apply ih tail p1t p2t
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hr
            · exact ok
            · exact holds_mono sub (inOld u hr)
          · have hk01 : k = 0 ∨ k = 1 := by omega
            rcases hk01 with rfl | rfl
            · change insert z r = {g} at tail
              exact False.elim (hp1g (by simpa [tail] using p1t))
            · rcases tail with skip' | ⟨a', _, b', _, _, z', hz', _, r', he', tail'⟩
              · change insert z r = {g} at skip'
                exact False.elim (hp1g (by simpa [skip'] using p1t))
              · change insert z' r' = {g} at tail'
                have hz'g : z' = g := by simpa [tail'] using Finset.mem_insert_self z' r'
                have hr'g : ∀ u ∈ r', u = g := fun u hu => by
                  simpa [tail'] using (Finset.mem_insert_of_mem (b := z') hu)
                have hp1ab : p1 = a' ∨ p1 = b' := by
                  rw [he'] at p1t
                  rcases Finset.mem_insert.mp p1t with h | h
                  · exact .inl h
                  · rcases Finset.mem_insert.mp h with h | h
                    · exact .inr h
                    · exact False.elim (hp1g (hr'g p1 h))
                have hp2ab : p2 = a' ∨ p2 = b' := by
                  rw [he'] at p2t
                  rcases Finset.mem_insert.mp p2t with h | h
                  · exact .inl h
                  · rcases Finset.mem_insert.mp h with h | h
                    · exact .inr h
                    · exact False.elim (hp2g (hr'g p2 h))
                have hfa' : f a' = 0 ∨ f a' = ~~~0 := by
                  rcases hp1ab with rfl | rfl
                  · exact hc1
                  · rcases hp2ab with rfl | h2
                    · exact hc2
                    · exact False.elim (hp12 h2.symm)
                have hfb' : f b' = 0 ∨ f b' = ~~~0 := by
                  rcases hp1ab with h1 | rfl
                  · rcases hp2ab with h2 | rfl
                    · exact False.elim (hp12 (h1.trans h2.symm))
                    · exact hc2
                  · exact hc1
                have hfg : f g = 0 ∨ f g = ~~~0 := hz'g ▸ mem_ops_both_const hfa' hfb' (hm a' b' z' hz')
                exact hfg.imp_right Or.inl

def goal6 : W 32 := BitVec.ofNat 64 0xeaeaeaaaeaaac880

def proj6 (ps : List (ℕ × ℕ)) (w : W 32) : W 24 :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 48 =>
    if k.val < 24 then w.getLsbD (ps.getD k.val (0, 0)).1
    else w.getLsbD (ps.getD (k.val - 24) (0, 0)).2))).cast List.length_ofFn

theorem proj6_getLsbD (ps : List (ℕ × ℕ)) (w : W 32) (j : ℕ) (hj : j < 48) :
    (proj6 ps w).getLsbD j =
      if j < 24 then w.getLsbD (ps.getD j (0, 0)).1
      else w.getLsbD (ps.getD (j - 24) (0, 0)).2 := by
  simp only [proj6, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem proj6_not (ps : List (ℕ × ℕ))
    (hps : ∀ r : Fin 24, (ps.getD r.val (0, 0)).1 < 64 ∧ (ps.getD r.val (0, 0)).2 < 64)
    (u : W 32) : proj6 ps (~~~u) = ~~~proj6 ps u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hj48 : j < 48 := hj
  rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
  rw [proj6_getLsbD ps (~~~u) j hj48]
  rw [BitVec.getLsbD_not (x := proj6 ps u), proj6_getLsbD ps u j hj48]
  by_cases hj2 : j < 24
  · have hlt : (ps.getD j (0, 0)).1 < 64 := (hps ⟨j, hj2⟩).1
    simp only [hj2, ↓reduceIte, BitVec.getLsbD_not, hj48, hlt, decide_true, Bool.true_and]
  · have hsub : j - 24 < 24 := by omega
    have hlt : (ps.getD (j - 24) (0, 0)).2 < 64 := (hps ⟨j - 24, hsub⟩).2
    simp only [hj2, ↓reduceIte, BitVec.getLsbD_not, hj48, hlt, decide_true, Bool.true_and]

theorem proj6_ops (ps : List (ℕ × ℕ))
    (hps : ∀ r : Fin 24, (ps.getD r.val (0, 0)).1 < 64 ∧ (ps.getD r.val (0, 0)).2 < 64)
    (a b z : W 32) (hz : z ∈ basicOps a b) :
    proj6 ps z ∈ basicOps (proj6 ps a) (proj6 ps b) := by
  have hand (u v : W 32) : proj6 ps (u &&& v) = proj6 ps u &&& proj6 ps v := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    have hj48 : j < 48 := hj
    rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
    rw [proj6_getLsbD ps _ j hj48, BitVec.getLsbD_and (x := proj6 ps u),
      proj6_getLsbD ps u j hj48, proj6_getLsbD ps v j hj48]
    by_cases hj2 : j < 24 <;> simp only [hj2, ↓reduceIte, BitVec.getLsbD_and]
  have hor (u v : W 32) : proj6 ps (u ||| v) = proj6 ps u ||| proj6 ps v := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    have hj48 : j < 48 := hj
    rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
    rw [proj6_getLsbD ps _ j hj48, BitVec.getLsbD_or (x := proj6 ps u),
      proj6_getLsbD ps u j hj48, proj6_getLsbD ps v j hj48]
    by_cases hj2 : j < 24 <;> simp only [hj2, ↓reduceIte, BitVec.getLsbD_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, proj6_not ps hps]

def ps0 : List (ℕ × ℕ) := [(3, 7), (3, 19), (3, 35), (6, 7), (18, 19), (22, 23), (22, 54), (34, 35), (38, 39), (38, 54), (50, 51), (50, 54), (22, 7), (22, 19), (38, 7), (38, 35), (50, 19), (50, 35), (3, 54), (22, 35), (38, 19), (50, 7), (2, 7), (2, 19)]
def ps1 : List (ℕ × ℕ) := [(5, 7), (5, 21), (5, 37), (6, 7), (20, 21), (22, 23), (22, 54), (36, 37), (38, 39), (38, 54), (52, 53), (52, 54), (22, 7), (22, 21), (38, 7), (38, 37), (52, 21), (52, 37), (5, 54), (22, 37), (38, 21), (52, 7), (4, 7), (4, 21)]
def ps2 : List (ℕ × ℕ) := [(1, 33), (3, 7), (3, 11), (3, 35), (5, 7), (5, 37), (6, 7), (6, 14), (9, 11), (9, 41), (10, 11), (10, 14), (12, 14), (13, 15), (13, 45), (32, 33), (34, 35), (36, 37), (38, 39), (38, 46), (40, 41), (42, 43), (42, 46), (44, 45)]
def ps3 : List (ℕ × ℕ) := [(1, 17), (3, 7), (3, 11), (3, 19), (5, 7), (5, 21), (6, 7), (6, 14), (9, 11), (9, 25), (10, 11), (10, 14), (12, 14), (13, 15), (13, 29), (16, 17), (18, 19), (20, 21), (22, 23), (22, 30), (24, 25), (26, 27), (26, 30), (28, 29)]

def psOf : Fin 4 → List (ℕ × ℕ)
  | ⟨0, _⟩ => ps0
  | ⟨1, _⟩ => ps1
  | ⟨2, _⟩ => ps2
  | ⟨3, _⟩ => ps3

def ins0 : List (W 24) := [0xfbf5bf040007, 0x645b6918f368, 0x952e722b3c70, 0xe8fc433cf80]
def ins1 : List (W 24) := [0xfbf5bf040007, 0x645b6918f368, 0x952e722b3c70, 0xe8fc433cf80]
def ins2 : List (W 24) := [0xb7e77f00633f, 0x6d3dde6d0cce, 0xce78f28e70f0, 0xf87f84f07f00, 0xffc229ff8000]
def ins3 : List (W 24) := [0xb7e77f00633f, 0x6d3dde6d0cce, 0xce78f28e70f0, 0xf87f84f07f00, 0xffc229ff8000]

def insOf : Fin 4 → List (W 24)
  | ⟨0, _⟩ => ins0
  | ⟨1, _⟩ => ins1
  | ⟨2, _⟩ => ins2
  | ⟨3, _⟩ => ins3

def kOf : Fin 4 → ℕ
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 6
  | ⟨3, _⟩ => 6

def isConstB (w : W 24) : Bool := w == 0 || w == ~~~0

theorem isConstB_sound {w : W 24} (h : isConstB w = true) : w = 0 ∨ w = ~~~0 := by
  simpa [isConstB] using h

def holdsB (ins : List (W 24)) (w : W 24) : Bool :=
  w == 0 || w == ~~~0 || ins.any (fun u => w == u || w == ~~~u)

theorem holdsB_sound {ins : List (W 24)} {w : W 24} (h : holdsB ins w = true) :
    holds ins.toFinset w := by
  simp only [holdsB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with (rfl | rfl) | ⟨u, hu, he⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, he⟩)

lemma hps_all : ∀ idx : Fin 4, ∀ r : Fin 24,
    ((psOf idx).getD r.val (0, 0)).1 < 64 ∧ ((psOf idx).getD r.val (0, 0)).2 < 64 := by
  decide +kernel

lemma hnd_all : ∀ idx : Fin 4, (insOf idx).Nodup := by decide +kernel

lemma hgoal_all : ∀ idx : Fin 4, proj6 (psOf idx) goal6 = goal 24 := by decide +kernel

lemma hins_all : ∀ idx : Fin 4, ∀ q : Fin 6, holdsB (insOf idx) (proj6 (psOf idx) (v6 q)) = true := by
  decide +kernel

lemma hno0 : searchE 5 ins0 = false := by decide +kernel
lemma hno1 : searchE 5 ins1 = false := by decide +kernel
set_option maxHeartbeats 400000 in
lemma hno2 : searchE 6 ins2 = false := by decide +kernel
set_option maxHeartbeats 400000 in
lemma hno3 : searchE 6 ins3 = false := by decide +kernel

lemma hno_all (idx : Fin 4) : searchE (kOf idx) (insOf idx) = false := by
  fin_cases idx
  · exact hno0
  · exact hno1
  · exact hno2
  · exact hno3

theorem reject_leaf (idx : Fin 4) {t : W 32} (ht : t = goal6 ∨ t = ~~~goal6)
    (hsb : SignedBuild (kOf idx) (insOf idx).toFinset (proj6 (psOf idx) t)) : False := by
  have hpg : proj6 (psOf idx) t = goal 24 ∨ proj6 (psOf idx) t = ~~~goal 24 := by
    rcases ht with rfl | rfl
    · exact .inl (hgoal_all idx)
    · exact .inr (by rw [proj6_not (psOf idx) (hps_all idx), hgoal_all idx])
  exact reject_base (by omega) (kOf idx) (insOf idx) (hnd_all idx) (hno_all idx) hpg hsb

def differs6 (r0 r1 : ℕ) (w : W 32) : Prop := w.getLsbD r0 ≠ w.getLsbD r1

theorem ops6_differs (r0 r1 : ℕ) (hr0 : r0 < 64) (hr1 : r1 < 64)
    (a b z : W 32) (hz : z ∈ basicOps a b)
    (hd : differs6 r0 r1 z) : differs6 r0 r1 a ∨ differs6 r0 r1 b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs6 at ha hb
  simp only [not_not] at ha hb
  rcases hz with rfl | rfl | rfl | rfl
  · simp only [BitVec.getLsbD_and, ha, hb]
  · simp only [BitVec.getLsbD_or, ha, hb]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hr0, hr1, ha, hb]
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hr0, hr1, ha, hb]

theorem goal6_differs {r0 r1 : ℕ} (hr0 : r0 < 64) (hr1 : r1 < 64) {t : W 32}
    (ht : t = goal6 ∨ t = ~~~goal6) (hg : differs6 r0 r1 goal6) : differs6 r0 r1 t := by
  rcases ht with rfl | rfl
  · exact hg
  · intro heq
    apply hg
    simp only [BitVec.getLsbD_not, hr0, hr1, decide_true, Bool.true_and] at heq
    cases h0 : goal6.getLsbD r0 <;> cases h1 : goal6.getLsbD r1 <;> simp_all

def sepPairB (d : Fin 6) (z : W 32) (r0 : Fin 64) : Bool :=
  let r1 := r0.val + 2 ^ d.val
  decide (r1 < 64) &&
  (goal6.getLsbD r0.val != goal6.getLsbD r1) &&
  (z.getLsbD r0.val == z.getLsbD r1) &&
  (List.finRange 6).all (fun q => q == d || ((v6 q).getLsbD r0.val == (v6 q).getLsbD r1))

lemma sepPairB_live {t z : W 32} {k : ℕ} {r : Finset (W 32)}
    (ht : t = goal6 ∨ t = ~~~goal6) (hr_sub : r ⊆ in6.toFinset)
    (tail : live basicOps t k (insert z r))
    {d : Fin 6} {r0 : Fin 64} (hsep : sepPairB d z r0 = true) :
    v6 d ∈ insert z r ∧ z ≠ v6 d := by
  simp only [sepPairB, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq,
    List.all_eq_true, List.mem_finRange, Bool.or_eq_true, forall_true_left] at hsep
  obtain ⟨⟨⟨hr1, hgd⟩, hzeq⟩, hqeq⟩ := hsep
  let r1 := r0.val + 2 ^ d.val
  have htd : differs6 r0.val r1 t := goal6_differs r0.isLt hr1 ht hgd
  obtain ⟨w, hw, hdw⟩ := live_separates (differs6 r0.val r1) htd
    (ops6_differs r0.val r1 r0.isLt hr1) tail
  have hvd : w = v6 d := by
    rcases Finset.mem_insert.mp hw with rfl | hwr
    · exact False.elim (hdw hzeq)
    · obtain ⟨q, rfl⟩ := in6_index w (List.mem_toFinset.mp (hr_sub hwr))
      rcases hqeq q with rfl | hq
      · rfl
      · exact False.elim (hdw hq)
  subst hvd
  exact ⟨hw, fun heq => hdw (heq ▸ hzeq)⟩

def constVarB (idx : Fin 4) (d : Fin 6) : Bool :=
  match idx.val, d.val with
  | 0, 1 => true
  | 0, 3 => true
  | 1, 2 => true
  | 1, 3 => true
  | 2, 4 => true
  | 3, 5 => true
  | _, _ => false

lemma constVarB_sound : ∀ idx : Fin 4, ∀ d : Fin 6,
    constVarB idx d = true → isConstB (proj6 (psOf idx) (v6 d)) = true := by
  decide +kernel

lemma v6_injective : ∀ d1 d2 : Fin 6, d1 ≠ d2 → v6 d1 ≠ v6 d2 := by decide +kernel

def checkOp (i j : Fin 6) (o : Fin 4) : Bool :=
  let z := (ops (v6 i) (v6 j)).getD o.val 0
  (z != goal6) && (z != ~~~goal6) &&
  (List.finRange 4).any fun idx =>
    let pz := proj6 (psOf idx) z
    ((decide (7 ≤ kOf idx) && holdsB (insOf idx) pz) ||
     (decide (6 ≤ kOf idx) &&
       (isConstB pz ||
         (holdsB (insOf idx) pz &&
           (List.finRange 6).any fun d =>
             constVarB idx d &&
             (List.finRange 64).any fun r0 => sepPairB d z r0)))) ||
    (decide (5 ≤ kOf idx) &&
      ((isConstB pz &&
          (List.finRange 6).any fun d =>
            constVarB idx d &&
            (List.finRange 64).any fun r0 => sepPairB d z r0) ||
       (holdsB (insOf idx) pz &&
          (List.finRange 6).any fun d1 =>
            constVarB idx d1 &&
            (List.finRange 6).any fun d2 =>
              decide (d1.val < d2.val) &&
              (constVarB idx d2 &&
                (((List.finRange 64).any fun r0 => sepPairB d1 z r0) &&
                 ((List.finRange 64).any fun r0 => sepPairB d2 z r0))))))

lemma v6_ne_goal : ∀ d : Fin 6, v6 d ≠ goal6 ∧ v6 d ≠ ~~~goal6 := by decide +kernel

lemma checkOp_all : ∀ i j : Fin 6, i ≠ j → ∀ o : Fin 4, checkOp i j o = true := by decide +kernel

theorem no_K {t : W 32} (ht : t = goal6 ∨ t = ~~~goal6)
    (h : build basicOps t 8 in6.toFinset) : False := by
  obtain ⟨s, hs, hlive⟩ := compress h
  rcases first_live hlive with hsing | ⟨a, ha, b, hb, hab, z, hz, _, r, he, tail⟩
  · have ht_mem : t ∈ in6.toFinset := hs (by simp [hsing])
    obtain ⟨d, hd⟩ := in6_index t (List.mem_toFinset.mp ht_mem)
    rcases ht with rfl | rfl
    · exact (v6_ne_goal d).1 hd.symm
    · exact (v6_ne_goal d).2 hd.symm
  · obtain ⟨i, rfl⟩ := in6_index a (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := in6_index b (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun h => hab (congrArg v6 h)
    obtain ⟨o, ho⟩ := index_of_op (v6 i) (v6 j) z hz
    have hchk := checkOp_all i j hij o
    simp only [checkOp, ho, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, List.any_eq_true,
      List.mem_finRange, true_and, Bool.or_eq_true] at hchk
    obtain ⟨⟨hzg, hzng⟩, idx, hbranch⟩ := hchk
    have hzt : z ≠ t := by rcases ht with rfl | rfl <;> assumption
    have hr_sub : r ⊆ in6.toFinset := fun u hu => hs (by simp [he, hu])
    have hav_r : ∀ u ∈ r, holds (insOf idx).toFinset (proj6 (psOf idx) u) := by
      intro u hu
      obtain ⟨q, rfl⟩ := in6_index u (List.mem_toFinset.mp (hr_sub hu))
      exact holdsB_sound (hins_all idx q)
    rcases hbranch with (⟨hkl, hhz⟩ | ⟨hkl, hcz | ⟨hhz, d, hcd, r0, hsep⟩⟩) |
        ⟨hkl, ⟨hcz, d, hcd, r0, hsep⟩ | ⟨hhz, d1, hcd1, d2, hd12, hcd2, ⟨r01, hsep1⟩, ⟨r02, hsep2⟩⟩⟩
    · have hav : ∀ w ∈ insert z r, holds (insOf idx).toFinset (proj6 (psOf idx) w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact holdsB_sound hhz
        · exact hav_r w hwr
      have hsb := live_transport (proj6_ops (psOf idx) (hps_all idx)) tail hav
      exact reject_leaf idx ht (sb_le hkl hsb)
    · have hcz' := isConstB_sound hcz
      have hav : ∀ w ∈ insert z r, holds (insOf idx).toFinset (proj6 (psOf idx) w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact hcz'.imp_right Or.inl
        · exact hav_r w hwr
      have hsb := live_transport_const_save (proj6_ops (psOf idx) (hps_all idx))
        tail (Finset.mem_insert_self z r) hzt hcz' hav
      exact reject_leaf idx ht (sb_le (by omega) hsb)
    · obtain ⟨hvd_mem, _⟩ := sepPairB_live ht hr_sub tail hsep
      have hvdt : v6 d ≠ t := by
        rcases ht with rfl | rfl
        · exact (v6_ne_goal d).1
        · exact (v6_ne_goal d).2
      have hav : ∀ w ∈ insert z r, holds (insOf idx).toFinset (proj6 (psOf idx) w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact holdsB_sound hhz
        · exact hav_r w hwr
      have hsb := live_transport_const_save (proj6_ops (psOf idx) (hps_all idx))
        tail hvd_mem hvdt (isConstB_sound (constVarB_sound idx d hcd)) hav
      exact reject_leaf idx ht (sb_le (by omega) hsb)
    · obtain ⟨hvd_mem, hzd⟩ := sepPairB_live ht hr_sub tail hsep
      have hcz' := isConstB_sound hcz
      have hvdt : v6 d ≠ t := by
        rcases ht with rfl | rfl
        · exact (v6_ne_goal d).1
        · exact (v6_ne_goal d).2
      have hav : ∀ w ∈ insert z r, holds (insOf idx).toFinset (proj6 (psOf idx) w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact hcz'.imp_right Or.inl
        · exact hav_r w hwr
      have hsb := live_transport_const_save2 (proj6_ops (psOf idx) (hps_all idx))
        tail (Finset.mem_insert_self z r) hvd_mem hzd hzt hvdt hcz'
        (isConstB_sound (constVarB_sound idx d hcd)) hav
      exact reject_leaf idx ht (sb_le (by omega) hsb)
    · obtain ⟨hvd1_mem, _⟩ := sepPairB_live ht hr_sub tail hsep1
      obtain ⟨hvd2_mem, _⟩ := sepPairB_live ht hr_sub tail hsep2
      have hvd12 : v6 d1 ≠ v6 d2 := v6_injective d1 d2 (fun h => Nat.ne_of_lt hd12 (congrArg Fin.val h))
      have hvd1t : v6 d1 ≠ t := by
        rcases ht with rfl | rfl
        · exact (v6_ne_goal d1).1
        · exact (v6_ne_goal d1).2
      have hvd2t : v6 d2 ≠ t := by
        rcases ht with rfl | rfl
        · exact (v6_ne_goal d2).1
        · exact (v6_ne_goal d2).2
      have hav : ∀ w ∈ insert z r, holds (insOf idx).toFinset (proj6 (psOf idx) w) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwr
        · exact holdsB_sound hhz
        · exact hav_r w hwr
      have hsb := live_transport_const_save2 (proj6_ops (psOf idx) (hps_all idx))
        tail hvd1_mem hvd2_mem hvd12 hvd1t hvd2t
        (isConstB_sound (constVarB_sound idx d1 hcd1))
        (isConstB_sound (constVarB_sound idx d2 hcd2)) hav
      exact reject_leaf idx ht (sb_le (by omega) hsb)

def targetF (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3941264042 * 2 ^ 32 + 3937060992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

lemma spec_f6 : ∀ k : Fin 64, targetF (fun i => bit k (v6 i)) = bit k goal6 := by decide +kernel

theorem binary_lb (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = targetF x) :
    8 < binaryCost gs := by
  by_contra hlow
  have low : binaryCost gs ≤ 8 := by omega
  have init : ∀ u ∈ in6, holds in6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (in6.map (bit k))).getD o false = bit k goal6 := by
    let x (i : Fin 6) : Bool := bit k (v6 i)
    have same : List.ofFn x = in6.map (bit k) := by
      apply List.ext_getElem
      · simp [in6]
      · intro i hi hj
        have hlt : i < in6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, v6, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (in6.map (bit k)) = bit k goal6
    rw [← same, he]
    exact spec_f6 k
  obtain ⟨t, ht, run⟩ := compileTarget goal6 (by decide) (by decide) gs o hg in6 in6.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a in6.toFinset) :
      build basicOps t c in6.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_K ht (lift low run)

def witGates : List Gate :=
  [ { op := GateOp.or, inputs := [0, 5] }
  , { op := GateOp.and, inputs := [4, 6] }
  , { op := GateOp.and, inputs := [1, 3] }
  , { op := GateOp.or, inputs := [7, 8] }
  , { op := GateOp.or, inputs := [0, 9] }
  , { op := GateOp.or, inputs := [9, 5] }
  , { op := GateOp.and, inputs := [11, 0] }
  , { op := GateOp.and, inputs := [2, 1] }
  , { op := GateOp.and, inputs := [10, 13] }
  , { op := GateOp.or, inputs := [14, 12] } ]

def witCirc : Circuit := ⟨witGates, 15⟩

lemma witCirc_mono : Monotone2 witCirc := by
  intro g hg
  simp only [witCirc, witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma witCirc_eval : ∀ x : Fin 6 → Bool, witCirc.eval (List.ofFn x) = targetF x := by decide +kernel

lemma main_proof (s : ℕ) (h : HasCircuitSize 6 targetF s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetF x := by
  obtain ⟨C, hFan, hSize, hEval⟩ := h
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨gNot, hgNot, hopNot⟩ := hasNot
    have hbc_lt : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨gNot, hgNot, by simp [isBinary, hopNot]⟩
    have hleg : ∀ g ∈ C.gates, legal g := fun g hg => by
      obtain ⟨hop, hlen⟩ := hFan g hg
      exact ⟨by simpa using hop, hlen⟩
    have hlb : 8 < binaryCost C.gates := binary_lb C.gates C.output hleg (fun x => by
      simpa [Circuit.eval] using hEval x)
    have hwit_le : witCirc.size ≤ s := by
      have hcs : C.gates.length ≤ s := hSize
      have hwl : witCirc.size = 10 := rfl
      omega
    exact ⟨witCirc, witCirc_mono, hwit_le, witCirc_eval⟩
  · refine ⟨C, ?_, hSize, hEval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hFan g hg
    refine ⟨?_, hlen⟩
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
    rcases hop' with h1 | h2 | h3
    · simp [h1]
    · simp [h2]
    · exact False.elim (hasNot ⟨g, hg, h3⟩)

end PEqualNP.Outside.L_meta_15605

theorem PEqualNP.Outside.L_meta_15605 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3937060992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3937060992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_15605.main_proof
