import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10476

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

def searchWithZ {P : ℕ} (n : ℕ) (inputs : List (W P)) (z : W P) : Bool :=
  let g := goal P
  let ng := ~~~g
  let ez := mkE z
  (inputs.map mkE).sublists.any fun ws =>
    let ws2 := ez :: ws
    decide (ws2.length ≤ n + 1) && (cutsE ws2 == BitVec.allOnes P) && optimizedE g ng n (n + 1 - ws2.length) ws2

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

theorem searchWithZ_complete {P : ℕ} {g : W P} (hg : g = goal P ∨ g = ~~~goal P) (n : ℕ)
    (inputs : List (W P)) (z : W P) (hn : inputs.Nodup) (hzn : z ∉ inputs)
    (hno : searchE n inputs = false) (h : build basicOps g n (insert z inputs.toFinset)) :
    searchWithZ n inputs z = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  by_cases hzs : z ∈ s
  · let ws := inputs.filter (· ∈ s)
    have hzws : z ∉ ws := fun hm => hzn (List.mem_filter.mp hm).1
    have hnd : (z :: ws).Nodup := List.nodup_cons.mpr ⟨hzws, hn.filter _⟩
    have eq : (z :: ws).toFinset = s := by
      ext w
      simp only [ws, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · rintro (rfl | ⟨_, hws⟩)
        · exact hzs
        · exact hws
      · intro hws
        rcases Finset.mem_insert.mp (hs hws) with rfl | hwin
        · exact Or.inl rfl
        · exact Or.inr ⟨List.mem_toFinset.mp hwin, hws⟩
    have hl' : live basicOps g n (z :: ws).toFinset := eq.symm ▸ hl
    have sz := live_card hl'
    rw [List.toFinset_card_of_nodup hnd] at sz
    have hsub : (ws.map mkE).Sublist (inputs.map mkE) := (List.filter_sublist ..).map mkE
    refine List.any_eq_true.mpr ⟨ws.map mkE, List.mem_sublists.mpr hsub, ?_⟩
    have hmap : mkE z :: ws.map mkE = (z :: ws).map mkE := rfl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hmap, List.length_map]
    exact ⟨⟨sz, cutsE_full hg hl'⟩, optimizedE_complete hg n (z :: ws) (n + 1 - (z :: ws).length) hnd (by omega) hl'⟩
  · exfalso
    have hsub : s ⊆ inputs.toFinset := by
      intro w hw
      rcases Finset.mem_insert.mp (hs hw) with rfl | hwin
      · exact False.elim (hzs hw)
      · exact hwin
    let ws := inputs.filter (· ∈ s)
    have eq : ws.toFinset = s := by
      ext w
      simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
      exact fun hw => List.mem_toFinset.mp (hsub hw)
    have hnd : ws.Nodup := hn.filter _
    have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
    have sz := live_card hl'
    rw [List.toFinset_card_of_nodup hnd] at sz
    have hhit : searchE n inputs = true := by
      refine List.any_eq_true.mpr ⟨ws.map mkE, List.mem_sublists.mpr ((List.filter_sublist ..).map mkE), ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.length_map]
      exact ⟨⟨sz, cutsE_full hg hl'⟩, optimizedE_complete hg n ws (n + 1 - ws.length) hnd (by omega) hl'⟩
    exact Bool.noConfusion (hno.symm.trans hhit)

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

theorem compile {P : ℕ} (hP : 0 < P) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (W P)) (av : Finset (W P)) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k : Fin (P + P), (gs.foldl step (w.map (bit k))).getD out false = bit k (goal P)) :
    ∃ t, (t = goal P ∨ t = ~~~goal P) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal P := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    have hne := goal_ne_const hP (Or.inl rfl)
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim (hne.1 zero)
    · exact False.elim (hne.2 ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun x : W P => ~~~x) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k : Fin (P + P), (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (goal P) := by
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

theorem live_transport_save {P1 P2 : ℕ} {f : W P1 → W P2}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W P1} {k : ℕ} {s : Finset (W P1)} {av : Finset (W P2)}
    (run : live basicOps g k s) (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
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
      · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
        have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
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

def project {P1 P2 : ℕ} (ix : List ℕ) (w : W P1) : W P2 :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin (P2 + P2) =>
    w.getLsbD ((if k.val < P2 then 0 else P1) + ix.getD (if k.val < P2 then k.val else k.val - P2) 0)))).cast List.length_ofFn

theorem project_getLsbD {P1 P2 : ℕ} (ix : List ℕ) (w : W P1) (j : ℕ) (hj : j < P2 + P2) :
    (project (P2 := P2) ix w).getLsbD j =
      w.getLsbD ((if j < P2 then 0 else P1) + ix.getD (if j < P2 then j else j - P2) 0) := by
  simp only [project, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem project_not {P1 P2 : ℕ} (ix : List ℕ) (hix : ∀ r : Fin P2, ix.getD r.val 0 < P1) (u : W P1) :
    project (P2 := P2) ix (~~~u) = ~~~project (P2 := P2) ix u := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
  rw [project_getLsbD ix (~~~u) j hj, BitVec.getLsbD_not, BitVec.getLsbD_not, project_getLsbD ix u j hj]
  have hidx : (if j < P2 then 0 else P1) + ix.getD (if j < P2 then j else j - P2) 0 < P1 + P1 := by
    by_cases hj2 : j < P2
    · have hlt : ix.getD j 0 < P1 := hix ⟨j, hj2⟩
      simp only [hj2, ↓reduceIte]; omega
    · have hlt : ix.getD (j - P2) 0 < P1 := hix ⟨j - P2, by omega⟩
      simp only [hj2, ↓reduceIte]; omega
  simp only [hj, hidx, decide_true, Bool.true_and]

theorem project_ops {P1 P2 : ℕ} (ix : List ℕ) (hix : ∀ r : Fin P2, ix.getD r.val 0 < P1)
    (a b z : W P1) (hz : z ∈ basicOps a b) :
    project (P2 := P2) ix z ∈ basicOps (project (P2 := P2) ix a) (project (P2 := P2) ix b) := by
  have hand (u v : W P1) : project (P2 := P2) ix (u &&& v) = (project (P2 := P2) ix u &&& project (P2 := P2) ix v) := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
    rw [project_getLsbD ix _ j hj, BitVec.getLsbD_and, BitVec.getLsbD_and,
      project_getLsbD ix u j hj, project_getLsbD ix v j hj]
  have hor (u v : W P1) : project (P2 := P2) ix (u ||| v) = (project (P2 := P2) ix u ||| project (P2 := P2) ix v) := by
    apply BitVec.eq_of_getElem_eq; intro j hj
    rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
    rw [project_getLsbD ix _ j hj, BitVec.getLsbD_or, BitVec.getLsbD_or,
      project_getLsbD ix u j hj, project_getLsbD ix v j hj]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, project_not ix hix]

theorem project_goal {P1 P2 : ℕ} (ix : List ℕ) (hix : ∀ r : Fin P2, ix.getD r.val 0 < P1) :
    project (P2 := P2) ix (goal P1) = goal P2 := by
  apply BitVec.eq_of_getElem_eq; intro j hj
  rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj]
  rw [project_getLsbD ix (goal P1) j hj]
  by_cases hj2 : j < P2
  · have hlt := hix ⟨j, hj2⟩
    simp only [hj2, ↓reduceIte, Nat.zero_add]
    rw [goal_getLsbD_lo _ hlt, goal_getLsbD_lo _ hj2]
  · have hsub : j - P2 < P2 := by omega
    have hlt := hix ⟨j - P2, hsub⟩
    simp only [hj2, ↓reduceIte]
    rw [goal_getLsbD_hi _ hlt]
    have heq : j = P2 + (j - P2) := by omega
    conv_rhs => rw [heq]
    rw [goal_getLsbD_hi _ hsub]

theorem project_signs {P1 P2 : ℕ} (ix : List ℕ) (hix : ∀ r : Fin P2, ix.getD r.val 0 < P1)
    {t : W P1} (ht : t = goal P1 ∨ t = ~~~goal P1) :
    project (P2 := P2) ix t = goal P2 ∨ project (P2 := P2) ix t = ~~~goal P2 := by
  rcases ht with rfl | rfl
  · exact Or.inl (project_goal ix hix)
  · exact Or.inr (by rw [project_not ix hix, project_goal ix hix])

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

theorem reject_withZ {P : ℕ} (hP : 0 < P) (n : ℕ) (inputs : List (W P)) (z : W P)
    (hn : inputs.Nodup) (hno : searchE n inputs = false) (hnoz : searchWithZ n inputs z = false)
    {t : W P} (ht : t = goal P ∨ t = ~~~goal P)
    (h : SignedBuild n (insert z inputs.toFinset) t) : False := by
  obtain ⟨u, hu, run⟩ := sb_to_build hP ht h
  by_cases hzin : z ∈ inputs
  · have heq : insert z inputs.toFinset = inputs.toFinset :=
      Finset.insert_eq_of_mem (List.mem_toFinset.mpr hzin)
    rw [heq] at run
    exact Bool.noConfusion (hno.symm.trans (searchE_complete hu n inputs hn run))
  · exact Bool.noConfusion (hnoz.symm.trans (searchWithZ_complete hu n inputs z hn hzin hno run))

def changes {P : ℕ} (w : W P) (r : Fin P) : Bool :=
  w.getLsbD (P + r.val) != w.getLsbD r.val

theorem unchanged {P : ℕ} (w : W P) (r : Fin P) (h : changes w r = false) : ¬ differs r w := by
  simpa [changes, differs] using h

theorem index_of_op {P : ℕ} (a b z : W P) (hz : z ∈ basicOps a b) :
    ∃ o : Fin 4, (ops a b).getD o.val 0 = z := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

def k4ins : List (W 24) := [0x7cb24f1c0007, 0xed54b9e00038, 0xb669d20001c0, 0xdb8f24000e00]
def g5ains : List (W 24) := [0x2492f7000077, 0xe12e78e00e78, 0x4b8f91038f80, 0x93f42a03f000, 0xfe4944fc0000]
def g5bins : List (W 24) := [0x92495f00000f, 0xf09731700730, 0x25c7c201c7c0, 0x49fa2401f800, 0x7f24887e0000]
def g5cins : List (W 24) := [0x92499f00000f, 0xa49771000770, 0x71c78271c780, 0x49fa2401f800, 0x7f24487e0000]
def g5dins : List (W 24) := [0xc449e70000e7, 0x8b8f80038f8, 0x513f21003f00, 0xa3d24a03c000, 0x3e24943c0000]

theorem k4_nd : k4ins.Nodup := by decide +kernel
theorem g5a_nd : g5ains.Nodup := by decide +kernel
theorem g5b_nd : g5bins.Nodup := by decide +kernel
theorem g5c_nd : g5cins.Nodup := by decide +kernel
theorem g5d_nd : g5dins.Nodup := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_k4 : searchE 6 k4ins = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5a : searchE 6 g5ains = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5b : searchE 6 g5bins = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5c : searchE 6 g5cins = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d : searchE 6 g5dins = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5a_z0 : searchWithZ 6 g5ains ((ops (g5ains.getD 1 0) (g5ains.getD 4 0)).getD 0 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5a_z1 : searchWithZ 6 g5ains ((ops (g5ains.getD 1 0) (g5ains.getD 4 0)).getD 1 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5a_z2 : searchWithZ 6 g5ains ((ops (g5ains.getD 1 0) (g5ains.getD 4 0)).getD 2 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5a_z3 : searchWithZ 6 g5ains ((ops (g5ains.getD 1 0) (g5ains.getD 4 0)).getD 3 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_a0 : searchWithZ 6 g5dins ((ops (g5dins.getD 2 0) (g5dins.getD 3 0)).getD 0 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_a1 : searchWithZ 6 g5dins ((ops (g5dins.getD 2 0) (g5dins.getD 3 0)).getD 1 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_a2 : searchWithZ 6 g5dins ((ops (g5dins.getD 2 0) (g5dins.getD 3 0)).getD 2 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_a3 : searchWithZ 6 g5dins ((ops (g5dins.getD 2 0) (g5dins.getD 3 0)).getD 3 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_b0 : searchWithZ 6 g5dins ((ops (g5dins.getD 3 0) (g5dins.getD 4 0)).getD 0 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_b1 : searchWithZ 6 g5dins ((ops (g5dins.getD 3 0) (g5dins.getD 4 0)).getD 1 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_b2 : searchWithZ 6 g5dins ((ops (g5dins.getD 3 0) (g5dins.getD 4 0)).getD 2 0) = false := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem t_g5d_b3 : searchWithZ 6 g5dins ((ops (g5dins.getD 3 0) (g5dins.getD 4 0)).getD 3 0) = false := by decide +kernel

theorem reject_g5a_ops {z t : W 24} (hz : z ∈ basicOps (g5ains.getD 1 0) (g5ains.getD 4 0))
    (ht : t = goal 24 ∨ t = ~~~goal 24) (h : SignedBuild 6 (insert z g5ains.toFinset) t) : False := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  subst ho
  fin_cases o
  · exact reject_withZ (by decide) 6 g5ains _ g5a_nd t_g5a t_g5a_z0 ht h
  · exact reject_withZ (by decide) 6 g5ains _ g5a_nd t_g5a t_g5a_z1 ht h
  · exact reject_withZ (by decide) 6 g5ains _ g5a_nd t_g5a t_g5a_z2 ht h
  · exact reject_withZ (by decide) 6 g5ains _ g5a_nd t_g5a t_g5a_z3 ht h

theorem reject_g5d_a_ops {z t : W 24} (hz : z ∈ basicOps (g5dins.getD 2 0) (g5dins.getD 3 0))
    (ht : t = goal 24 ∨ t = ~~~goal 24) (h : SignedBuild 6 (insert z g5dins.toFinset) t) : False := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  subst ho
  fin_cases o
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_a0 ht h
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_a1 ht h
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_a2 ht h
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_a3 ht h

theorem reject_g5d_b_ops {z t : W 24} (hz : z ∈ basicOps (g5dins.getD 3 0) (g5dins.getD 4 0))
    (ht : t = goal 24 ∨ t = ~~~goal 24) (h : SignedBuild 6 (insert z g5dins.toFinset) t) : False := by
  obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
  subst ho
  fin_cases o
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_b0 ht h
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_b1 ht h
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_b2 ht h
  · exact reject_withZ (by decide) 6 g5dins _ g5d_nd t_g5d t_g5d_b3 ht h

def k5ins : List (W 47) := [0x44924affe258000000ffc00, 0x8925ff92a4a80003ff00000, 0x113fe9324c93007fc0000000, 0x23e391c4711c078000000000, 0x3e3c1e0781e0780000000000]
def k5v (i : Fin 5) : W 47 := k5ins.getD i.val 0
def k5src : Fin 5 → List ℕ := ![[21, 23, 26, 31, 32, 35, 40, 41, 42, 44, 45, 46, 2, 4, 5, 7, 8, 9, 25, 28, 29, 34, 37, 38], [11, 13, 16, 30, 32, 35, 39, 41, 42, 43, 45, 46, 1, 3, 5, 6, 8, 9, 15, 18, 19, 33, 36, 38], [10, 13, 16, 20, 23, 26, 39, 40, 42, 43, 44, 46, 0, 3, 4, 6, 7, 9, 14, 17, 19, 24, 27, 29], [10, 11, 16, 20, 21, 26, 30, 31, 35, 43, 44, 45, 0, 1, 2, 6, 7, 8, 12, 17, 18, 22, 27, 28], [10, 11, 13, 20, 21, 23, 30, 31, 32, 39, 40, 41, 0, 1, 2, 3, 4, 5, 12, 14, 15, 22, 24, 25]]

theorem k5_idx_ok : ∀ (d : Fin 5) (r : Fin 24), (k5src d).getD r.val 0 < 47 := by decide +kernel
theorem k5_in_ix : ∀ w ∈ k5ins, ∃ i : Fin 5, k5v i = w := by
  intro w hw
  simp only [k5ins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩
theorem k5_not_goal : ∀ i : Fin 5, k5v i ≠ goal 47 ∧ k5v i ≠ ~~~goal 47 := by decide +kernel
theorem k5_proj_zero : ∀ d : Fin 5, project (P2 := 24) (k5src d) (k5v d) = 0 := by decide +kernel
theorem k5_proj_mem : ∀ (d k : Fin 5),
    project (P2 := 24) (k5src d) (k5v k) = 0 ∨ project (P2 := 24) (k5src d) (k5v k) ∈ k4ins := by decide +kernel
set_option maxRecDepth 8000 in
theorem k5_sep : ∀ (i j : Fin 5), i ≠ j → ∀ op : Fin 4, ∃ r : Fin 47,
    changes ((ops (k5v i) (k5v j)).getD op.val 0) r = false ∧
    ∀ q : Fin 5, q ≠ i → changes (k5v q) r = false := by decide +kernel

theorem no_eight_k5 {t : W 47} (ht : t = goal 47 ∨ t = ~~~goal 47)
    (h : SignedBuild 8 k5ins.toFinset t) : False := by
  obtain ⟨u, hu, run⟩ := sb_to_build (by decide) ht h
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have huin : u ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := k5_in_ix _ (List.mem_toFinset.mp (hs huin))
    rcases hu with rfl | rfl
    · exact (k5_not_goal i).1 hi
    · exact (k5_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := k5_in_ix _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := k5_in_ix _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg k5v eq)
    have sub : rest ⊆ k5ins.toFinset := fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
    obtain ⟨r, hrz, hrq⟩ := k5_sep i j hij o
    rw [ho] at hrz
    have keep : k5v i ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (differs r) (goal_differs hu r) (ops_differs r) tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (unchanged _ _ hrz hdw)
      · obtain ⟨q, rfl⟩ := k5_in_ix _ (List.mem_toFinset.mp (sub hw))
        by_contra hn
        exact unchanged _ _ (hrq q fun eq => hn (eq ▸ hw)) hdw
    have pg : k5v i ≠ u := by rcases hu with rfl | rfl; exact (k5_not_goal i).1; exact (k5_not_goal i).2
    have hix := k5_idx_ok i
    have hav : ∀ k : Fin 5, holds k4ins.toFinset (project (P2 := 24) (k5src i) (k5v k)) := by
      intro k
      rcases k5_proj_mem i k with h0 | hm
      · exact .inl h0
      · exact .inr (.inr ⟨_, List.mem_toFinset.mpr hm, .inl rfl⟩)
    apply reject_base (by decide) 6 k4ins k4_nd t_k4 (project_signs (k5src i) hix hu)
    apply live_transport_save (project_ops (k5src i) hix) tail (Finset.mem_insert_of_mem keep) pg (k5_proj_zero i)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact mem_ops_zero (hav i) (hav j) (Or.inl (k5_proj_zero i)) (project_ops (k5src i) hix _ _ _ hz)
    · obtain ⟨k, rfl⟩ := k5_in_ix _ (List.mem_toFinset.mp (sub hw))
      exact hav k

def g4ins : List (W 42) := [0x1111122f8f40000001e3c, 0x222225e7f080000079fc0, 0xf044f1f8817c003c7e000, 0x44f0fe4112003c3f80000, 0x88ff409224803fc000000, 0xff888904483fc00000000]
def g4v (i : Fin 6) : W 42 := g4ins.getD i.val 0
def g4src0 : List ℕ := [6, 7, 8, 14, 16, 17, 18, 20, 21, 23, 24, 25, 27, 28, 29, 31, 32, 33, 35, 36, 37, 39, 40, 41]
def g4src1 : List ℕ := [2, 3, 4, 5, 13, 14, 19, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34, 36, 37, 38, 40, 41, 0]
def g4src3 : List ℕ := [27, 28, 29, 26, 7, 8, 14, 13, 17, 18, 15, 37, 35, 34, 41, 39, 38, 4, 2, 5, 11, 9, 12, 1]
def g4src4 : List ℕ := [20, 19, 21, 13, 23, 22, 25, 6, 8, 16, 15, 18, 3, 2, 5, 10, 9, 12, 36, 35, 34, 40, 39, 38]

def g4drop (i j : Fin 6) : Fin 6 :=
  if (i.val == 2 && j.val == 5) || (i.val == 5 && j.val == 2) then 0
  else if i.val == 0 || j.val == 0 then 0
  else if i.val == 1 || j.val == 1 then 1
  else if i.val == 4 || j.val == 4 then 4
  else 3

theorem g4_idx0 : ∀ r : Fin 24, g4src0.getD r.val 0 < 42 := by decide +kernel
theorem g4_idx1 : ∀ r : Fin 24, g4src1.getD r.val 0 < 42 := by decide +kernel
theorem g4_idx3 : ∀ r : Fin 24, g4src3.getD r.val 0 < 42 := by decide +kernel
theorem g4_idx4 : ∀ r : Fin 24, g4src4.getD r.val 0 < 42 := by decide +kernel
theorem g4_in_ix : ∀ w ∈ g4ins, ∃ i : Fin 6, g4v i = w := by
  intro w hw
  simp only [g4ins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩
theorem g4_not_goal : ∀ i : Fin 6, g4v i ≠ goal 42 ∧ g4v i ≠ ~~~goal 42 := by decide +kernel
theorem g4_p0_zero : project (P2 := 24) g4src0 (g4v 0) = 0 := by decide +kernel
theorem g4_p1_zero : project (P2 := 24) g4src1 (g4v 1) = 0 := by decide +kernel
theorem g4_p3_zero : project (P2 := 24) g4src3 (g4v 3) = 0 := by decide +kernel
theorem g4_p4_zero : project (P2 := 24) g4src4 (g4v 4) = 0 := by decide +kernel
theorem g4_p0_mem : ∀ k : Fin 6, project (P2 := 24) g4src0 (g4v k) = 0 ∨ project (P2 := 24) g4src0 (g4v k) ∈ g5ains := by decide +kernel
theorem g4_p1_mem : ∀ k : Fin 6, project (P2 := 24) g4src1 (g4v k) = 0 ∨ project (P2 := 24) g4src1 (g4v k) ∈ g5bins := by decide +kernel
theorem g4_p3_mem : ∀ k : Fin 6, project (P2 := 24) g4src3 (g4v k) = 0 ∨ project (P2 := 24) g4src3 (g4v k) ∈ g5bins := by decide +kernel
theorem g4_p4_mem : ∀ k : Fin 6, project (P2 := 24) g4src4 (g4v k) = 0 ∨ project (P2 := 24) g4src4 (g4v k) ∈ g5ains := by decide +kernel
theorem g4_p0_2 : project (P2 := 24) g4src0 (g4v 2) = g5ains.getD 1 0 := by decide +kernel
theorem g4_p0_5 : project (P2 := 24) g4src0 (g4v 5) = g5ains.getD 4 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem g4_sep : ∀ (i j : Fin 6), i ≠ j → ∀ op : Fin 4, ∃ r : Fin 42,
    changes ((ops (g4v i) (g4v j)).getD op.val 0) r = false ∧
    ∀ q : Fin 6, q ≠ g4drop i j → changes (g4v q) r = false := by decide +kernel

theorem no_eight_g4 {t : W 42} (ht : t = goal 42 ∨ t = ~~~goal 42)
    (h : SignedBuild 8 g4ins.toFinset t) : False := by
  obtain ⟨u, hu, run⟩ := sb_to_build (by decide) ht h
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have huin : u ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := g4_in_ix _ (List.mem_toFinset.mp (hs huin))
    rcases hu with rfl | rfl
    · exact (g4_not_goal i).1 hi
    · exact (g4_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := g4_in_ix _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := g4_in_ix _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg g4v eq)
    have sub : rest ⊆ g4ins.toFinset := fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
    obtain ⟨r, hrz, hrq⟩ := g4_sep i j hij o
    rw [ho] at hrz
    have keep : g4v (g4drop i j) ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (differs r) (goal_differs hu r) (ops_differs r) tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (unchanged _ _ hrz hdw)
      · obtain ⟨q, rfl⟩ := g4_in_ix _ (List.mem_toFinset.mp (sub hw))
        by_contra hn
        exact unchanged _ _ (hrq q fun eq => hn (eq ▸ hw)) hdw
    have pg : g4v (g4drop i j) ≠ u := by
      rcases hu with rfl | rfl; exact (g4_not_goal _).1; exact (g4_not_goal _).2
    have go_std (d : Fin 6) (ix : List ℕ) (tgt : List (W 24)) (hnd : tgt.Nodup) (hno : searchE 6 tgt = false)
        (hix : ∀ r : Fin 24, ix.getD r.val 0 < 42) (hzero : project (P2 := 24) ix (g4v d) = 0)
        (hmem : ∀ k : Fin 6, project (P2 := 24) ix (g4v k) = 0 ∨ project (P2 := 24) ix (g4v k) ∈ tgt)
        (hd : g4drop i j = d) (hin : d = i ∨ d = j) : False := by
      have hav : ∀ k : Fin 6, holds tgt.toFinset (project (P2 := 24) ix (g4v k)) := fun k =>
        (hmem k).elim .inl (fun hm => .inr (.inr ⟨_, List.mem_toFinset.mpr hm, .inl rfl⟩))
      apply reject_base (by decide) 6 tgt hnd hno (project_signs ix hix hu)
      apply live_transport_save (project_ops ix hix) tail (Finset.mem_insert_of_mem (hd ▸ keep)) (hd ▸ pg) hzero
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · have hzz : project (P2 := 24) ix (g4v i) = 0 ∨ project (P2 := 24) ix (g4v j) = 0 :=
          hin.elim (fun e => .inl (e ▸ hzero)) (fun e => .inr (e ▸ hzero))
        exact mem_ops_zero (hav i) (hav j) hzz (project_ops ix hix _ _ _ hz)
      · obtain ⟨k, rfl⟩ := g4_in_ix _ (List.mem_toFinset.mp (sub hw))
        exact hav k
    have go_p25 (hpair : (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 2)) : False := by
      have hd : g4drop i j = 0 := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      have hfz : project (P2 := 24) g4src0 z ∈ basicOps (g5ains.getD 1 0) (g5ains.getD 4 0) := by
        have h1 := project_ops g4src0 g4_idx0 _ _ _ hz
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rwa [g4_p0_2, g4_p0_5] at h1
        · rw [g4_p0_5, g4_p0_2, ops_swap] at h1; exact h1
      apply reject_g5a_ops hfz (project_signs g4src0 g4_idx0 hu)
      apply live_transport_save (project_ops g4src0 g4_idx0) tail
        (Finset.mem_insert_of_mem (hd ▸ keep)) (hd ▸ pg) g4_p0_zero
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact .inr (.inr ⟨_, Finset.mem_insert_self _ _, .inl rfl⟩)
      · obtain ⟨k, rfl⟩ := g4_in_ix _ (List.mem_toFinset.mp (sub hw))
        rcases g4_p0_mem k with h0 | hm
        · exact .inl h0
        · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (List.mem_toFinset.mpr hm), .inl rfl⟩)
    fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inr rfl)
    · exact go_std 3 g4src3 g5bins g5b_nd t_g5b g4_idx3 g4_p3_zero g4_p3_mem (by decide) (Or.inr rfl)
    · exact go_std 4 g4src4 g5ains g5a_nd t_g5a g4_idx4 g4_p4_zero g4_p4_mem (by decide) (Or.inr rfl)
    · exact go_p25 (Or.inl ⟨rfl, rfl⟩)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inr rfl)
    · exact go_std 3 g4src3 g5bins g5b_nd t_g5b g4_idx3 g4_p3_zero g4_p3_mem (by decide) (Or.inl rfl)
    · exact go_std 4 g4src4 g5ains g5a_nd t_g5a g4_idx4 g4_p4_zero g4_p4_mem (by decide) (Or.inr rfl)
    · exact go_std 3 g4src3 g5bins g5b_nd t_g5b g4_idx3 g4_p3_zero g4_p3_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inr rfl)
    · exact go_std 4 g4src4 g5ains g5a_nd t_g5a g4_idx4 g4_p4_zero g4_p4_mem (by decide) (Or.inl rfl)
    · exact go_std 4 g4src4 g5ains g5a_nd t_g5a g4_idx4 g4_p4_zero g4_p4_mem (by decide) (Or.inl rfl)
    · exact go_std 4 g4src4 g5ains g5a_nd t_g5a g4_idx4 g4_p4_zero g4_p4_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g4src0 g5ains g5a_nd t_g5a g4_idx0 g4_p0_zero g4_p0_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g4src1 g5bins g5b_nd t_g5b g4_idx1 g4_p1_zero g4_p1_mem (by decide) (Or.inr rfl)
    · exact go_p25 (Or.inr ⟨rfl, rfl⟩)
    · exact go_std 3 g4src3 g5bins g5b_nd t_g5b g4_idx3 g4_p3_zero g4_p3_mem (by decide) (Or.inr rfl)
    · exact go_std 4 g4src4 g5ains g5a_nd t_g5a g4_idx4 g4_p4_zero g4_p4_mem (by decide) (Or.inr rfl)

def g6ins : List (W 42) := [0x1111144f1fc0000001c78, 0x22222bc7e0000000f1f80, 0x4444f3f90240003cfe000, 0xf0f0fc80243c3c3f00000, 0x88ff411248803fc000000, 0xff888224913fc00000000]
def g6v (i : Fin 6) : W 42 := g6ins.getD i.val 0
def g6src0a : List ℕ := [36, 35, 37, 21, 40, 39, 41, 15, 14, 25, 23, 24, 9, 7, 8, 19, 17, 18, 29, 28, 27, 33, 32, 31]
def g6src0b : List ℕ := [28, 27, 29, 21, 32, 31, 33, 14, 15, 24, 23, 25, 8, 7, 9, 18, 17, 19, 37, 36, 35, 41, 40, 39]
def g6src1 : List ℕ := [3, 4, 5, 6, 13, 14, 15, 20, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34, 36, 37, 38, 40, 41, 0]
def g6src3a : List ℕ := [3, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 26, 27, 28, 29, 34, 35, 36, 37, 0, 1]
def g6src3b : List ℕ := [3, 6, 5, 9, 8, 10, 12, 11, 13, 15, 14, 16, 19, 18, 34, 35, 36, 37, 26, 27, 28, 29, 0, 2]

def g6drop (i j : Fin 6) : Fin 6 :=
  if (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3) ||
     (i.val == 3 && j.val == 5) || (i.val == 5 && j.val == 3) then 0
  else if (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
          (i.val == 2 && j.val == 5) || (i.val == 5 && j.val == 2) ||
          (i.val == 4 && j.val == 5) || (i.val == 5 && j.val == 4) then 3
  else if i.val == 0 || j.val == 0 then 0
  else if i.val == 1 || j.val == 1 then 1
  else 3

theorem g6_idx0a : ∀ r : Fin 24, g6src0a.getD r.val 0 < 42 := by decide +kernel
theorem g6_idx0b : ∀ r : Fin 24, g6src0b.getD r.val 0 < 42 := by decide +kernel
theorem g6_idx1 : ∀ r : Fin 24, g6src1.getD r.val 0 < 42 := by decide +kernel
theorem g6_idx3a : ∀ r : Fin 24, g6src3a.getD r.val 0 < 42 := by decide +kernel
theorem g6_idx3b : ∀ r : Fin 24, g6src3b.getD r.val 0 < 42 := by decide +kernel
theorem g6_in_ix : ∀ w ∈ g6ins, ∃ i : Fin 6, g6v i = w := by
  intro w hw
  simp only [g6ins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩
theorem g6_not_goal : ∀ i : Fin 6, g6v i ≠ goal 42 ∧ g6v i ≠ ~~~goal 42 := by decide +kernel
theorem g6_p0a_zero : project (P2 := 24) g6src0a (g6v 0) = 0 := by decide +kernel
theorem g6_p0b_zero : project (P2 := 24) g6src0b (g6v 0) = 0 := by decide +kernel
theorem g6_p1_zero : project (P2 := 24) g6src1 (g6v 1) = 0 := by decide +kernel
theorem g6_p3a_zero : project (P2 := 24) g6src3a (g6v 3) = 0 := by decide +kernel
theorem g6_p3b_zero : project (P2 := 24) g6src3b (g6v 3) = 0 := by decide +kernel
theorem g6_p0a_mem : ∀ k : Fin 6, project (P2 := 24) g6src0a (g6v k) = 0 ∨ project (P2 := 24) g6src0a (g6v k) ∈ g5ains := by decide +kernel
theorem g6_p0b_mem : ∀ k : Fin 6, project (P2 := 24) g6src0b (g6v k) = 0 ∨ project (P2 := 24) g6src0b (g6v k) ∈ g5ains := by decide +kernel
theorem g6_p1_mem : ∀ k : Fin 6, project (P2 := 24) g6src1 (g6v k) = 0 ∨ project (P2 := 24) g6src1 (g6v k) ∈ g5cins := by decide +kernel
theorem g6_p3a_mem : ∀ k : Fin 6, project (P2 := 24) g6src3a (g6v k) = 0 ∨ project (P2 := 24) g6src3a (g6v k) ∈ g5dins := by decide +kernel
theorem g6_p3b_mem : ∀ k : Fin 6, project (P2 := 24) g6src3b (g6v k) = 0 ∨ project (P2 := 24) g6src3b (g6v k) ∈ g5dins := by decide +kernel
theorem g6_p0a_3 : project (P2 := 24) g6src0a (g6v 3) = g5ains.getD 1 0 := by decide +kernel
theorem g6_p0a_4 : project (P2 := 24) g6src0a (g6v 4) = g5ains.getD 4 0 := by decide +kernel
theorem g6_p0b_3 : project (P2 := 24) g6src0b (g6v 3) = g5ains.getD 1 0 := by decide +kernel
theorem g6_p0b_5 : project (P2 := 24) g6src0b (g6v 5) = g5ains.getD 4 0 := by decide +kernel
theorem g6_p3a_2 : project (P2 := 24) g6src3a (g6v 2) = g5dins.getD 2 0 := by decide +kernel
theorem g6_p3a_4 : project (P2 := 24) g6src3a (g6v 4) = g5dins.getD 3 0 := by decide +kernel
theorem g6_p3a_5 : project (P2 := 24) g6src3a (g6v 5) = g5dins.getD 4 0 := by decide +kernel
theorem g6_p3b_2 : project (P2 := 24) g6src3b (g6v 2) = g5dins.getD 2 0 := by decide +kernel
theorem g6_p3b_5 : project (P2 := 24) g6src3b (g6v 5) = g5dins.getD 3 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem g6_sep : ∀ (i j : Fin 6), i ≠ j → ∀ op : Fin 4, ∃ r : Fin 42,
    changes ((ops (g6v i) (g6v j)).getD op.val 0) r = false ∧
    ∀ q : Fin 6, q ≠ g6drop i j → changes (g6v q) r = false := by decide +kernel

theorem no_eight_g6 {t : W 42} (ht : t = goal 42 ∨ t = ~~~goal 42)
    (h : SignedBuild 8 g6ins.toFinset t) : False := by
  obtain ⟨u, hu, run⟩ := sb_to_build (by decide) ht h
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 7) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have huin : u ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := g6_in_ix _ (List.mem_toFinset.mp (hs huin))
    rcases hu with rfl | rfl
    · exact (g6_not_goal i).1 hi
    · exact (g6_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := g6_in_ix _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := g6_in_ix _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg g6v eq)
    have sub : rest ⊆ g6ins.toFinset := fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
    obtain ⟨r, hrz, hrq⟩ := g6_sep i j hij o
    rw [ho] at hrz
    have keep : g6v (g6drop i j) ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (differs r) (goal_differs hu r) (ops_differs r) tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (unchanged _ _ hrz hdw)
      · obtain ⟨q, rfl⟩ := g6_in_ix _ (List.mem_toFinset.mp (sub hw))
        by_contra hn
        exact unchanged _ _ (hrq q fun eq => hn (eq ▸ hw)) hdw
    have pg : g6v (g6drop i j) ≠ u := by
      rcases hu with rfl | rfl; exact (g6_not_goal _).1; exact (g6_not_goal _).2
    have go_std (d : Fin 6) (ix : List ℕ) (tgt : List (W 24)) (hnd : tgt.Nodup) (hno : searchE 6 tgt = false)
        (hix : ∀ r : Fin 24, ix.getD r.val 0 < 42) (hzero : project (P2 := 24) ix (g6v d) = 0)
        (hmem : ∀ k : Fin 6, project (P2 := 24) ix (g6v k) = 0 ∨ project (P2 := 24) ix (g6v k) ∈ tgt)
        (hd : g6drop i j = d) (hin : d = i ∨ d = j) : False := by
      have hav : ∀ k : Fin 6, holds tgt.toFinset (project (P2 := 24) ix (g6v k)) := fun k =>
        (hmem k).elim .inl (fun hm => .inr (.inr ⟨_, List.mem_toFinset.mpr hm, .inl rfl⟩))
      apply reject_base (by decide) 6 tgt hnd hno (project_signs ix hix hu)
      apply live_transport_save (project_ops ix hix) tail (Finset.mem_insert_of_mem (hd ▸ keep)) (hd ▸ pg) hzero
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · have hzz : project (P2 := 24) ix (g6v i) = 0 ∨ project (P2 := 24) ix (g6v j) = 0 :=
          hin.elim (fun e => .inl (e ▸ hzero)) (fun e => .inr (e ▸ hzero))
        exact mem_ops_zero (hav i) (hav j) hzz (project_ops ix hix _ _ _ hz)
      · obtain ⟨k, rfl⟩ := g6_in_ix _ (List.mem_toFinset.mp (sub hw))
        exact hav k
    have go_spec (d : Fin 6) (ix : List ℕ) (tgt : List (W 24))
        (hix : ∀ r : Fin 24, ix.getD r.val 0 < 42) (hzero : project (P2 := 24) ix (g6v d) = 0)
        (hmem : ∀ k : Fin 6, project (P2 := 24) ix (g6v k) = 0 ∨ project (P2 := 24) ix (g6v k) ∈ tgt)
        (hd : g6drop i j = d)
        (hrej : ∀ w, w = project (P2 := 24) ix z →
          SignedBuild 6 (insert w tgt.toFinset) (project (P2 := 24) ix u) → False) : False := by
      apply hrej (project (P2 := 24) ix z) rfl
      apply live_transport_save (project_ops ix hix) tail
        (Finset.mem_insert_of_mem (hd ▸ keep)) (hd ▸ pg) hzero
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact .inr (.inr ⟨_, Finset.mem_insert_self _ _, .inl rfl⟩)
      · obtain ⟨k, rfl⟩ := g6_in_ix _ (List.mem_toFinset.mp (sub hw))
        rcases hmem k with h0 | hm
        · exact .inl h0
        · exact .inr (.inr ⟨_, Finset.mem_insert_of_mem (List.mem_toFinset.mpr hm), .inl rfl⟩)
    fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inl rfl)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inr rfl)
    · exact go_std 3 g6src3a g5dins g5d_nd t_g5d g6_idx3a g6_p3a_zero g6_p3a_mem (by decide) (Or.inr rfl)
    · exact go_spec 3 g6src3a g5dins g6_idx3a g6_p3a_zero g6_p3a_mem (by decide) (fun _ hw hsb =>
        reject_g5d_a_ops (by rw [hw]; have h1 := project_ops g6src3a g6_idx3a _ _ _ hz; change project (P2 := 24) g6src3a z ∈ basicOps (project (P2 := 24) g6src3a (g6v 2)) (project (P2 := 24) g6src3a (g6v 4)) at h1; rwa [g6_p3a_2, g6_p3a_4] at h1) (project_signs g6src3a g6_idx3a hu) hsb)
    · exact go_spec 3 g6src3b g5dins g6_idx3b g6_p3b_zero g6_p3b_mem (by decide) (fun _ hw hsb =>
        reject_g5d_a_ops (by rw [hw]; have h1 := project_ops g6src3b g6_idx3b _ _ _ hz; change project (P2 := 24) g6src3b z ∈ basicOps (project (P2 := 24) g6src3b (g6v 2)) (project (P2 := 24) g6src3b (g6v 5)) at h1; rwa [g6_p3b_2, g6_p3b_5] at h1) (project_signs g6src3b g6_idx3b hu) hsb)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inr rfl)
    · exact go_std 3 g6src3a g5dins g5d_nd t_g5d g6_idx3a g6_p3a_zero g6_p3a_mem (by decide) (Or.inl rfl)
    · exact go_spec 0 g6src0a g5ains g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (fun _ hw hsb =>
        reject_g5a_ops (by rw [hw]; have h1 := project_ops g6src0a g6_idx0a _ _ _ hz; change project (P2 := 24) g6src0a z ∈ basicOps (project (P2 := 24) g6src0a (g6v 3)) (project (P2 := 24) g6src0a (g6v 4)) at h1; rwa [g6_p0a_3, g6_p0a_4] at h1) (project_signs g6src0a g6_idx0a hu) hsb)
    · exact go_spec 0 g6src0b g5ains g6_idx0b g6_p0b_zero g6_p0b_mem (by decide) (fun _ hw hsb =>
        reject_g5a_ops (by rw [hw]; have h1 := project_ops g6src0b g6_idx0b _ _ _ hz; change project (P2 := 24) g6src0b z ∈ basicOps (project (P2 := 24) g6src0b (g6v 3)) (project (P2 := 24) g6src0b (g6v 5)) at h1; rwa [g6_p0b_3, g6_p0b_5] at h1) (project_signs g6src0b g6_idx0b hu) hsb)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inr rfl)
    · exact go_spec 3 g6src3a g5dins g6_idx3a g6_p3a_zero g6_p3a_mem (by decide) (fun _ hw hsb =>
        reject_g5d_a_ops (by rw [hw]; have h1 := project_ops g6src3a g6_idx3a _ _ _ hz; change project (P2 := 24) g6src3a z ∈ basicOps (project (P2 := 24) g6src3a (g6v 4)) (project (P2 := 24) g6src3a (g6v 2)) at h1; rw [g6_p3a_4, g6_p3a_2, ops_swap] at h1; exact h1) (project_signs g6src3a g6_idx3a hu) hsb)
    · exact go_spec 0 g6src0a g5ains g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (fun _ hw hsb =>
        reject_g5a_ops (by rw [hw]; have h1 := project_ops g6src0a g6_idx0a _ _ _ hz; change project (P2 := 24) g6src0a z ∈ basicOps (project (P2 := 24) g6src0a (g6v 4)) (project (P2 := 24) g6src0a (g6v 3)) at h1; rw [g6_p0a_4, g6_p0a_3, ops_swap] at h1; exact h1) (project_signs g6src0a g6_idx0a hu) hsb)
    · exact go_spec 3 g6src3a g5dins g6_idx3a g6_p3a_zero g6_p3a_mem (by decide) (fun _ hw hsb =>
        reject_g5d_b_ops (by rw [hw]; have h1 := project_ops g6src3a g6_idx3a _ _ _ hz; change project (P2 := 24) g6src3a z ∈ basicOps (project (P2 := 24) g6src3a (g6v 4)) (project (P2 := 24) g6src3a (g6v 5)) at h1; rwa [g6_p3a_4, g6_p3a_5] at h1) (project_signs g6src3a g6_idx3a hu) hsb)
    · exact go_std 0 g6src0a g5ains g5a_nd t_g5a g6_idx0a g6_p0a_zero g6_p0a_mem (by decide) (Or.inr rfl)
    · exact go_std 1 g6src1 g5cins g5c_nd t_g5c g6_idx1 g6_p1_zero g6_p1_mem (by decide) (Or.inr rfl)
    · exact go_spec 3 g6src3b g5dins g6_idx3b g6_p3b_zero g6_p3b_mem (by decide) (fun _ hw hsb =>
        reject_g5d_a_ops (by rw [hw]; have h1 := project_ops g6src3b g6_idx3b _ _ _ hz; change project (P2 := 24) g6src3b z ∈ basicOps (project (P2 := 24) g6src3b (g6v 5)) (project (P2 := 24) g6src3b (g6v 2)) at h1; rw [g6_p3b_5, g6_p3b_2, ops_swap] at h1; exact h1) (project_signs g6src3b g6_idx3b hu) hsb)
    · exact go_spec 0 g6src0b g5ains g6_idx0b g6_p0b_zero g6_p0b_mem (by decide) (fun _ hw hsb =>
        reject_g5a_ops (by rw [hw]; have h1 := project_ops g6src0b g6_idx0b _ _ _ hz; change project (P2 := 24) g6src0b z ∈ basicOps (project (P2 := 24) g6src0b (g6v 5)) (project (P2 := 24) g6src0b (g6v 3)) at h1; rw [g6_p0b_5, g6_p0b_3, ops_swap] at h1; exact h1) (project_signs g6src0b g6_idx0b hu) hsb)
    · exact go_spec 3 g6src3a g5dins g6_idx3a g6_p3a_zero g6_p3a_mem (by decide) (fun _ hw hsb =>
        reject_g5d_b_ops (by rw [hw]; have h1 := project_ops g6src3a g6_idx3a _ _ _ hz; change project (P2 := 24) g6src3a z ∈ basicOps (project (P2 := 24) g6src3a (g6v 5)) (project (P2 := 24) g6src3a (g6v 4)) at h1; rw [g6_p3a_5, g6_p3a_4, ops_swap] at h1; exact h1) (project_signs g6src3a g6_idx3a hu) hsb)

def g7ins : List (W 127) := [0x2042042108222492527e003fffc108b80000000000000000007c007fff80000, 0x418428463144492ffe3fffc448863350000000000000001ffc7fff800000000, 0x3e508708c639fff8fffc24a8cdacc667fc0000000003fff1fff8000000000000, 0x863e43e8421ffff004044ac893084460007c07c0003fffe0000000000000000, 0x1081083ffffe88e04988893111c108780000007ffffc00000000000000000000, 0x2103ffd107c10f008e1111c21e020f800007ff80000000000000000000000000, 0x3ffe1021f801f004f0021e03e003f0007ff80000000000000000000000000000]
def g7v (i : Fin 7) : W 127 := g7ins.getD i.val 0
def g7src0 : List ℕ := [3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 69, 70, 72, 73, 75, 76, 77, 79, 80, 81, 83, 86, 87, 89, 91, 92, 94, 96, 97, 104, 107, 108, 109, 116, 119, 120, 121]
def g7src1 : List ℕ := [2, 4, 7, 8, 11, 12, 13, 16, 17, 18, 22, 23, 25, 26, 28, 29, 30, 32, 33, 34, 68, 70, 71, 73, 74, 76, 77, 78, 80, 81, 82, 86, 87, 88, 91, 92, 93, 96, 97, 103, 107, 108, 109, 115, 119, 120, 121]
def g7src3 : List ℕ := [1, 4, 6, 8, 10, 12, 13, 15, 17, 18, 20, 23, 24, 26, 27, 29, 30, 31, 33, 34, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 82, 85, 87, 88, 90, 92, 93, 95, 97, 103, 106, 108, 109, 115, 117, 120, 121]
def g7src4 : List ℕ := [0, 9, 19, 21, 26, 30, 35, 39, 42, 46, 47, 49, 50, 51, 53, 54, 55, 58, 61, 65, 66, 67, 68, 69, 73, 77, 103, 104, 105, 109, 110, 111, 112, 114, 115, 116, 118, 121, 122, 123, 124, 126]
def g7src5 : List ℕ := [0, 5, 19, 21, 23, 30, 35, 37, 42, 46, 47, 48, 50, 51, 52, 54, 55, 56, 61, 65, 66, 67, 68, 69, 70, 77, 82, 83, 84, 92, 98, 99, 100, 102, 115, 116, 118, 120, 122, 123, 124, 125]
def g7src6 : List ℕ := [0, 4, 8, 19, 21, 23, 26, 35, 37, 39, 46, 48, 49, 51, 52, 53, 54, 55, 56, 58, 65, 66, 68, 69, 70, 73, 82, 83, 84, 87, 98, 99, 100, 101, 103, 104, 105, 108, 110, 111, 112, 113]

def g7drop (i j : Fin 7) : Fin 7 :=
  if (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3) then 4
  else if (i.val == 3 && j.val == 5) || (i.val == 5 && j.val == 3) then 5
  else if i.val == 0 || j.val == 0 then 0
  else if i.val == 1 || j.val == 1 then 1
  else if i.val == 3 || j.val == 3 then 3
  else if i.val == 4 || j.val == 4 then 4
  else if i.val == 5 || j.val == 5 then 5
  else 6

theorem g7_idx0 : ∀ r : Fin 47, g7src0.getD r.val 0 < 127 := by decide +kernel
theorem g7_idx1 : ∀ r : Fin 47, g7src1.getD r.val 0 < 127 := by decide +kernel
theorem g7_idx3 : ∀ r : Fin 47, g7src3.getD r.val 0 < 127 := by decide +kernel
theorem g7_idx4 : ∀ r : Fin 42, g7src4.getD r.val 0 < 127 := by decide +kernel
theorem g7_idx5 : ∀ r : Fin 42, g7src5.getD r.val 0 < 127 := by decide +kernel
theorem g7_idx6 : ∀ r : Fin 42, g7src6.getD r.val 0 < 127 := by decide +kernel

theorem g7_in_ix : ∀ w ∈ g7ins, ∃ i : Fin 7, g7v i = w := by
  intro w hw
  simp only [g7ins, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩

theorem g7_not_goal : ∀ i : Fin 7, g7v i ≠ goal 127 ∧ g7v i ≠ ~~~goal 127 := by decide +kernel
theorem g7_p0_zero : project (P2 := 47) g7src0 (g7v 0) = 0 := by decide +kernel
theorem g7_p1_zero : project (P2 := 47) g7src1 (g7v 1) = 0 := by decide +kernel
theorem g7_p3_zero : project (P2 := 47) g7src3 (g7v 3) = 0 := by decide +kernel
theorem g7_p4_zero : project (P2 := 42) g7src4 (g7v 4) = 0 := by decide +kernel
theorem g7_p5_zero : project (P2 := 42) g7src5 (g7v 5) = 0 := by decide +kernel
theorem g7_p6_zero : project (P2 := 42) g7src6 (g7v 6) = 0 := by decide +kernel

theorem g7_p0_mem : ∀ k : Fin 7, project (P2 := 47) g7src0 (g7v k) = 0 ∨ project (P2 := 47) g7src0 (g7v k) ∈ k5ins := by decide +kernel
theorem g7_p1_mem : ∀ k : Fin 7, project (P2 := 47) g7src1 (g7v k) = 0 ∨ project (P2 := 47) g7src1 (g7v k) ∈ k5ins := by decide +kernel
theorem g7_p3_mem : ∀ k : Fin 7, project (P2 := 47) g7src3 (g7v k) = 0 ∨ project (P2 := 47) g7src3 (g7v k) ∈ k5ins := by decide +kernel
theorem g7_p4_mem : ∀ k : Fin 7, project (P2 := 42) g7src4 (g7v k) = 0 ∨ project (P2 := 42) g7src4 (g7v k) ∈ g4ins := by decide +kernel
theorem g7_p5_mem : ∀ k : Fin 7, project (P2 := 42) g7src5 (g7v k) = 0 ∨ project (P2 := 42) g7src5 (g7v k) ∈ g4ins := by decide +kernel
theorem g7_p6_mem : ∀ k : Fin 7, project (P2 := 42) g7src6 (g7v k) = 0 ∨ project (P2 := 42) g7src6 (g7v k) ∈ g6ins := by decide +kernel

theorem g7_drop_mem : ∀ (i j : Fin 7), i ≠ j → g7drop i j = i ∨ g7drop i j = j := by decide +kernel
theorem g7_drop_vals : ∀ (i j : Fin 7), i ≠ j →
    g7drop i j = 0 ∨ g7drop i j = 1 ∨ g7drop i j = 3 ∨ g7drop i j = 4 ∨ g7drop i j = 5 ∨ g7drop i j = 6 := by decide +kernel

set_option maxRecDepth 16000 in
theorem g7_sep : ∀ (i j : Fin 7), i ≠ j → ∀ op : Fin 4, ∃ r : Fin 127,
    changes ((ops (g7v i) (g7v j)).getD op.val 0) r = false ∧
    ∀ q : Fin 7, q ≠ g7drop i j → changes (g7v q) r = false := by decide +kernel

theorem no_ten_g7 {t : W 127} (ht : t = goal 127 ∨ t = ~~~goal 127)
    (run : build basicOps t 10 g7ins.toFinset) : False := by
  obtain ⟨s, hs, hl⟩ := compress run
  rcases first_live (k := 9) hl with endcase | ⟨a, ha, b, hb, hab, z, hz, _, rest, he, tail⟩
  · have htin : t ∈ s := by simp [endcase]
    obtain ⟨i, hi⟩ := g7_in_ix _ (List.mem_toFinset.mp (hs htin))
    rcases ht with rfl | rfl
    · exact (g7_not_goal i).1 hi
    · exact (g7_not_goal i).2 hi
  · obtain ⟨i, rfl⟩ := g7_in_ix _ (List.mem_toFinset.mp (hs ha))
    obtain ⟨j, rfl⟩ := g7_in_ix _ (List.mem_toFinset.mp (hs hb))
    have hij : i ≠ j := fun eq => hab (congrArg g7v eq)
    have sub : rest ⊆ g7ins.toFinset := fun w hw => hs (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    obtain ⟨o, ho⟩ := index_of_op _ _ _ hz
    obtain ⟨r, hrz, hrq⟩ := g7_sep i j hij o
    rw [ho] at hrz
    have keep : g7v (g7drop i j) ∈ rest := by
      obtain ⟨w, hw, hdw⟩ := live_separates (differs r) (goal_differs ht r) (ops_differs r) tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (unchanged _ _ hrz hdw)
      · obtain ⟨q, rfl⟩ := g7_in_ix _ (List.mem_toFinset.mp (sub hw))
        by_contra hn
        exact unchanged _ _ (hrq q fun eq => hn (eq ▸ hw)) hdw
    have pg : g7v (g7drop i j) ≠ t := by
      rcases ht with rfl | rfl; exact (g7_not_goal _).1; exact (g7_not_goal _).2
    have hmem_ij := g7_drop_mem i j hij
    have step_down {P2 : ℕ} (d : Fin 7) (ix : List ℕ) (tgt : List (W P2))
        (hix : ∀ r : Fin P2, ix.getD r.val 0 < 127) (hzero : project (P2 := P2) ix (g7v d) = 0)
        (hmem : ∀ k : Fin 7, project (P2 := P2) ix (g7v k) = 0 ∨ project (P2 := P2) ix (g7v k) ∈ tgt)
        (hrej : ∀ u, (u = goal P2 ∨ u = ~~~goal P2) → SignedBuild 8 tgt.toFinset u → False)
        (hd : g7drop i j = d) : False := by
      have hin : d = i ∨ d = j := hd ▸ hmem_ij
      have hav : ∀ k : Fin 7, holds tgt.toFinset (project (P2 := P2) ix (g7v k)) := fun k =>
        (hmem k).elim .inl (fun hm => .inr (.inr ⟨_, List.mem_toFinset.mpr hm, .inl rfl⟩))
      apply hrej _ (project_signs ix hix ht)
      apply live_transport_save (project_ops ix hix) tail (Finset.mem_insert_of_mem (hd ▸ keep)) (hd ▸ pg) hzero
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · have hzz : project (P2 := P2) ix (g7v i) = 0 ∨ project (P2 := P2) ix (g7v j) = 0 :=
          hin.elim (fun e => .inl (e ▸ hzero)) (fun e => .inr (e ▸ hzero))
        exact mem_ops_zero (hav i) (hav j) hzz (project_ops ix hix _ _ _ hz)
      · obtain ⟨k, rfl⟩ := g7_in_ix _ (List.mem_toFinset.mp (sub hw))
        exact hav k
    rcases g7_drop_vals i j hij with h | h | h | h | h | h
    · exact step_down 0 g7src0 k5ins g7_idx0 g7_p0_zero g7_p0_mem (fun _ hu hs => no_eight_k5 hu hs) h
    · exact step_down 1 g7src1 k5ins g7_idx1 g7_p1_zero g7_p1_mem (fun _ hu hs => no_eight_k5 hu hs) h
    · exact step_down 3 g7src3 k5ins g7_idx3 g7_p3_zero g7_p3_mem (fun _ hu hs => no_eight_k5 hu hs) h
    · exact step_down 4 g7src4 g4ins g7_idx4 g7_p4_zero g7_p4_mem (fun _ hu hs => no_eight_g4 hu hs) h
    · exact step_down 5 g7src5 g4ins g7_idx5 g7_p5_zero g7_p5_mem (fun _ hu hs => no_eight_g4 hu hs) h
    · exact step_down 6 g7src6 g6ins g7_idx6 g7_p6_zero g7_p6_mem (fun _ hu hs => no_eight_g6 hu hs) h

def graphF (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 8000 in
theorem spec_g7 : ∀ k : Fin (127 + 127), graphF (fun i => bit k (g7v i)) = bit k (goal 127) := by
  decide +kernel

theorem eleven_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = graphF x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ g7ins, holds g7ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin (127 + 127)) :
      (gs.foldl step (g7ins.map (bit k))).getD o false = bit k (goal 127) := by
    let x (i : Fin 7) : Bool := bit k (g7v i)
    have same : List.ofFn x = g7ins.map (bit k) := by
      apply List.ext_getElem
      · simp [g7ins]
      · intro i hi hj
        have hlt : i < g7ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, g7v, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (g7ins.map (bit k)) = bit k (goal 127)
    rw [← same, he]
    exact spec_g7 k
  obtain ⟨t, ht, run⟩ := compile (by decide) gs o hg g7ins g7ins.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a g7ins.toFinset) :
      build basicOps t c g7ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact no_ten_g7 ht (lift low run)

def witGates : List Gate :=
  [ { op := GateOp.or,  inputs := [4, 5] }
  , { op := GateOp.or,  inputs := [1, 0] }
  , { op := GateOp.or,  inputs := [8, 6] }
  , { op := GateOp.and, inputs := [6, 8] }
  , { op := GateOp.or,  inputs := [3, 7] }
  , { op := GateOp.or,  inputs := [7, 0] }
  , { op := GateOp.and, inputs := [5, 4] }
  , { op := GateOp.and, inputs := [2, 12] }
  , { op := GateOp.and, inputs := [11, 9] }
  , { op := GateOp.or,  inputs := [13, 14] }
  , { op := GateOp.or,  inputs := [16, 10] }
  , { op := GateOp.or,  inputs := [17, 15] } ]

theorem witGates_mono : ∀ g ∈ witGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witGates_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨witGates, 18⟩ (List.ofFn x) = graphF x := by
  decide +kernel

theorem main_proof (gates : List Gate) (o : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graphF x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = graphF x := by
  by_cases hasNot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨gNot, hgNot, hopNot⟩ := hasNot
    have hbc_lt : binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨gNot, hgNot, by simp [isBinary, hopNot]⟩
    have hleg' : ∀ g ∈ gates, legal g := fun g hg => ⟨by simpa using (hleg g hg).1, (hleg g hg).2⟩
    have h11 : 10 < binaryCost gates := eleven_binary gates o hleg' heval
    have h12 : witGates.length ≤ gates.length := by
      change 12 ≤ gates.length; omega
    exact ⟨witGates, 18, witGates_mono, h12, witGates_eval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (hleg g hg).2⟩, le_refl _, heval⟩
    rcases (hleg g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_10476

theorem PEqualNP.Outside.L_meta_10476 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hleg _ heval
  exact PEqualNP.Outside.L_meta_10476.main_proof gates o hleg heval
