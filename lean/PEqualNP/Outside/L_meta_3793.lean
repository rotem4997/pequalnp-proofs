import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Constructions
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- The formula rectangle and rank arguments adapt the checked proof of L_meta_252.

namespace PEqualNP.Outside.L_meta_3793

def leafLabels {n : ℕ} : DMFormula n → List (Fin n)
  | .lit v _ => [v]
  | .and a b | .or a b => leafLabels a ++ leafLabels b

@[simp] theorem leafLabels_length {n : ℕ} (φ : DMFormula n) :
    (leafLabels φ).length = φ.leaves := by
  induction φ <;> simp [leafLabels, DMFormula.leaves, *]

def leafLabel {n : ℕ} : (φ : DMFormula n) → Fin φ.leaves → Fin n
  | .lit v _, _ => v
  | .and a b, i | .or a b, i => Fin.addCases (leafLabel a) (leafLabel b) i

theorem ofFn_leafLabel {n : ℕ} (φ : DMFormula n) :
    List.ofFn (leafLabel φ) = leafLabels φ := by
  induction φ with
  | lit => simp [leafLabel, leafLabels, DMFormula.leaves]
  | and a b hA hB | or a b hA hB =>
    change List.ofFn (Fin.append (leafLabel a) (leafLabel b)) = leafLabels a ++ leafLabels b
    rw [List.ofFn_fin_append, hA, hB]

end PEqualNP.Outside.L_meta_3793

namespace PEqualNP.Outside.L_meta_3793.Fano

abbrev point (p : Fin 7) : Fin 14 := Fin.castAdd 7 p
abbrev line (l : Fin 7) : Fin 14 := Fin.natAdd 7 l

private def oriented (a b : Fin 14) : Prop :=
  a.val < 7 ∧ 7 ≤ b.val ∧
    (a.val = b.val - 7 ∨ a.val = (b.val - 7 + 1) % 7 ∨ a.val = (b.val - 7 + 3) % 7)

private instance : DecidableRel oriented := fun a b => by unfold oriented; infer_instance

def fanoGraph : SimpleGraph (Fin 14) := SimpleGraph.fromRel oriented

instance : DecidableRel fanoGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel oriented).Adj)

private theorem point_inj : Function.Injective point := by
  intro a b h
  exact Fin.ext (congrArg (Fin.val : Fin 14 → ℕ) h)

private theorem line_inj : Function.Injective line := by
  intro a b h
  apply Fin.ext
  have e := congrArg Fin.val h
  simp only [Fin.val_natAdd] at e
  omega

private theorem point_ne_line (p l : Fin 7) : point p ≠ line l := by
  intro h
  have e := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at e
  have hp := p.isLt
  omega

private def incident (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

private instance : DecidableRel incident := fun p l => by unfold incident; infer_instance

private theorem oriented_coords : ∀ p l : Fin 7, oriented (point p) (line l) ↔ incident p l := by
  decide +kernel

private theorem oriented_iff (a b : Fin 14) :
    oriented a b ↔ ∃ p l : Fin 7, incident p l ∧ a = point p ∧ b = line l := by
  constructor
  · intro h
    let p : Fin 7 := ⟨a.val, h.1⟩
    let l : Fin 7 := ⟨b.val - 7, by have := b.isLt; omega⟩
    have ha : a = point p := Fin.ext rfl
    have hb : b = line l := by
      apply Fin.ext
      change b.val = 7 + (b.val - 7)
      have := h.2.1
      omega
    refine ⟨p, l, (oriented_coords p l).mp ?_, ha, hb⟩
    rw [← ha, ← hb]
    exact h
  · rintro ⟨p, l, h, rfl, rfl⟩
    exact (oriented_coords p l).mpr h

theorem fanoAdj_iff (a b : Fin 14) :
    fanoGraph.Adj a b ↔ ∃ p l : Fin 7,
      (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      ((a = point p ∧ b = line l) ∨ (b = point p ∧ a = line l)) := by
  constructor
  · intro h
    rcases h.2 with h | h
    · obtain ⟨p, l, hi, ha, hb⟩ := (oriented_iff a b).mp h
      exact ⟨p, l, hi, Or.inl ⟨ha, hb⟩⟩
    · obtain ⟨p, l, hi, hb, ha⟩ := (oriented_iff b a).mp h
      exact ⟨p, l, hi, Or.inr ⟨hb, ha⟩⟩
  · rintro ⟨p, l, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨point_ne_line p l, Or.inl ((oriented_coords p l).mpr h)⟩
    · exact ⟨(point_ne_line p l).symm, Or.inr ((oriented_coords p l).mpr h)⟩

private theorem adj_sides {a b : Fin 14} (h : fanoGraph.Adj a b) :
    (a.val < 7 ∧ 7 ≤ b.val) ∨ (b.val < 7 ∧ 7 ≤ a.val) :=
  h.2.imp (fun e => ⟨e.1, e.2.1⟩) (fun e => ⟨e.1, e.2.1⟩)

theorem triangleFree_fano :
    ∀ a b c : Fin 14, fanoGraph.Adj a b → fanoGraph.Adj b c → ¬ fanoGraph.Adj a c := by
  intro a b c hab hbc hac
  rcases adj_sides hab with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases adj_sides hbc with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases adj_sides hac with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

private theorem neighbors_point {p : Fin 7} {a : Fin 14} :
    fanoGraph.Adj (point p) a ↔ ∃ l : Fin 7, a = line l ∧ incident p l := by
  constructor
  · intro h
    obtain ⟨q, l, hi, ⟨hp, ha⟩ | ⟨_, hp⟩⟩ := (fanoAdj_iff _ _).mp h
    · have e := point_inj hp
      exact ⟨l, ha, e.symm ▸ hi⟩
    · exact (point_ne_line p l hp).elim
  · rintro ⟨l, rfl, h⟩
    exact (fanoAdj_iff _ _).mpr ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩

private theorem neighbors_line {l : Fin 7} {a : Fin 14} :
    fanoGraph.Adj (line l) a ↔ ∃ p : Fin 7, a = point p ∧ incident p l := by
  constructor
  · intro h
    obtain ⟨p, m, hi, ⟨hl, _⟩ | ⟨ha, hl⟩⟩ := (fanoAdj_iff _ _).mp h
    · exact (point_ne_line p l hl.symm).elim
    · have e := line_inj hl
      exact ⟨p, ha, e.symm ▸ hi⟩
  · rintro ⟨p, rfl, h⟩
    exact (fanoAdj_iff _ _).mpr ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩

private theorem point_line (p l : Fin 7) : fanoGraph.Adj (point p) (line l) ↔ incident p l := by
  constructor
  · intro h
    obtain ⟨m, hm, hi⟩ := neighbors_point.mp h
    have e := line_inj hm
    exact e.symm ▸ hi
  · intro h
    exact neighbors_point.mpr ⟨l, rfl, h⟩

private theorem unique_line : ∀ p q l m : Fin 7,
    p ≠ q → incident p l → incident q l → incident p m → incident q m → l = m := by
  decide +kernel

theorem noFour_fano :
    ∀ a b c d : Fin 14, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      fanoGraph.Adj a b → fanoGraph.Adj b c → fanoGraph.Adj c d → ¬ fanoGraph.Adj d a := by
  intro a b c d _ hac _ _ hbd _ hab hbc hcd hda
  obtain ⟨p, l, hpl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (fanoAdj_iff a b).mp hab
  · obtain ⟨q, rfl, hql⟩ := neighbors_line.mp hbc
    obtain ⟨m, rfl, hqm⟩ := neighbors_point.mp hcd
    have hpm := (point_line p m).mp hda.symm
    have hpq : p ≠ q := fun e => hac (congrArg point e)
    exact hbd (congrArg line (unique_line p q l m hpq hpl hql hpm hqm))
  · obtain ⟨m, rfl, hpm⟩ := neighbors_point.mp hbc
    obtain ⟨q, rfl, hqm⟩ := neighbors_line.mp hcd
    have hql := (point_line q l).mp hda
    by_cases e : p = q
    · exact hbd (congrArg point e)
    · exact hac (congrArg line (unique_line p q l m e hpl hql hpm hqm))

theorem edgeCard_fano : fanoGraph.edgeFinset.card = 21 := by
  decide +kernel

def points : Finset (Fin 14) := Finset.univ.image point

def lines : Finset (Fin 14) := Finset.univ.image line

theorem points_card : points.card = 7 := by
  rw [points, Finset.card_image_of_injective _ point_inj]
  simp

theorem lines_card : lines.card = 7 := by
  rw [lines, Finset.card_image_of_injective _ line_inj]
  simp

private def endpoint (S : Finset (Fin 14)) (p : Fin 7) : Fin 14 :=
  if point p ∈ S then point p else line p

private theorem endpoint_inj (S : Finset (Fin 14)) : Function.Injective (endpoint S) := by
  intro p q h
  by_cases hp : point p ∈ S <;> by_cases hq : point q ∈ S
  · exact point_inj (by simpa [endpoint, hp, hq] using h)
  · exact (point_ne_line p q (by simpa [endpoint, hp, hq] using h)).elim
  · exact (point_ne_line q p (by simpa [endpoint, hp, hq] using h.symm)).elim
  · exact line_inj (by simpa [endpoint, hp, hq] using h)

private theorem endpoint_mem (S : Finset (Fin 14)) (hcover : (∀ u v, fanoGraph.Adj u v → u ∈ S ∨ v ∈ S))
    (p : Fin 7) : endpoint S p ∈ S := by
  have hpq : fanoGraph.Adj (point p) (line p) :=
    (fanoAdj_iff _ _).mpr ⟨p, p, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  by_cases h : point p ∈ S
  · simp [endpoint, h]
  · simpa [endpoint, h] using (hcover _ _ hpq).resolve_left h

theorem vertexCover_card_ge (S : Finset (Fin 14)) (hcover : (∀ u v, fanoGraph.Adj u v → u ∈ S ∨ v ∈ S)) :
    7 ≤ S.card := by
  have hsub : Finset.univ.image (endpoint S) ⊆ S := by
    intro u h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    exact endpoint_mem S hcover p
  have h := Finset.card_le_card hsub
  simpa [Finset.card_image_of_injective _ (endpoint_inj S)] using h

private def walk (p : Fin 7) : ℕ → Fin 7
  | 0 => p
  | k + 1 => walk p k + 1

private theorem walk_reaches : ∀ p q : Fin 7, ∃ k : Fin 7, walk p k.val = q := by
  decide +kernel

theorem vertexCover_eq_side (S : Finset (Fin 14)) (hcover : (∀ u v, fanoGraph.Adj u v → u ∈ S ∨ v ∈ S))
    (hsmall : S.card ≤ 7) : S = points ∨ S = lines := by
  have hsub : Finset.univ.image (endpoint S) ⊆ S := by
    intro u h
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    exact endpoint_mem S hcover p
  have heq : Finset.univ.image (endpoint S) = S := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa [Finset.card_image_of_injective _ (endpoint_inj S)] using hsmall
  have not_line {p : Fin 7} (hp : point p ∈ S) : line p ∉ S := by
    intro hl
    have hm : line p ∈ Finset.univ.image (endpoint S) := by rwa [heq]
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hm
    by_cases h : point q ∈ S
    · exact point_ne_line q p (by simpa [endpoint, h] using hq)
    · have eq : q = p := line_inj (by simpa [endpoint, h] using hq)
      exact h (eq.symm ▸ hp)
  have advance {p : Fin 7} (hp : point p ∈ S) : point (p + 1) ∈ S := by
    have hadj : fanoGraph.Adj (point (p + 1)) (line p) :=
      (fanoAdj_iff _ _).mpr ⟨p + 1, p, Or.inr (Or.inl rfl), Or.inl ⟨rfl, rfl⟩⟩
    exact (hcover _ _ hadj).resolve_right (not_line hp)
  by_cases hex : ∃ p : Fin 7, point p ∈ S
  · obtain ⟨p, hp⟩ := hex
    have hwalk : ∀ k, point (walk p k) ∈ S := by
      intro k
      induction k with
      | zero => exact hp
      | succ _ ih => exact advance ih
    have hall (q : Fin 7) : point q ∈ S := by
      obtain ⟨k, hk⟩ := walk_reaches p q
      exact hk ▸ hwalk k.val
    refine Or.inl (heq.symm.trans ?_)
    have e : endpoint S = point := funext fun q => by simp [endpoint, hall q]
    rw [e, points]
  · have hnone (p : Fin 7) : point p ∉ S := fun hp => hex ⟨p, hp⟩
    refine Or.inr (heq.symm.trans ?_)
    have e : endpoint S = line := funext fun p => by simp [endpoint, hnone p]
    rw [e, lines]

end PEqualNP.Outside.L_meta_3793.Fano

namespace PEqualNP.Outside.L_meta_3793

open PEqualNP.CircuitLowerBounds

abbrev Positive {n : Nat} (φ : DMFormula n) : Prop :=
  DMFormula.rec (motive := fun _ : DMFormula n => Prop)
    (fun (_ : Fin n) (b : Bool) => b = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ

def labels {n : Nat} : DMFormula n → List Nat
  | .lit i _ => [i.val]
  | .and p q | .or p q => labels p ++ labels q

theorem count_labels {n : Nat} (φ : DMFormula n) (i : Fin n) :
    (labels φ).count i.val = (leafLabels φ).count i := by
  induction φ with
  | lit v b => simp [labels, leafLabels, List.count_cons, beq_iff_eq, Fin.ext_iff]
  | and p q hp hq | or p q hp hq => simp [labels, leafLabels, hp, hq]

private inductive RawFormula
  | var : Nat → RawFormula
  | and : RawFormula → RawFormula → RawFormula
  | or : RawFormula → RawFormula → RawFormula

namespace RawFormula

private def leaves : RawFormula → List Nat
  | .var i => [i]
  | .and p q | .or p q => leaves p ++ leaves q

private def eval (v : Nat → Bool) : RawFormula → Bool
  | .var i => v i
  | .and p q => p.eval v && q.eval v
  | .or p q => p.eval v || q.eval v

private def replace (i : Nat) : RawFormula → RawFormula → RawFormula
  | .var j, term => if j = i then term else .var j
  | .and p q, term => .and (replace i p term) (replace i q term)
  | .or p q, term => .or (replace i p term) (replace i q term)

private theorem eval_congr (f : RawFormula) {v w : Nat → Bool}
    (h : ∀ i ∈ f.leaves, v i = w i) : f.eval v = f.eval w := by
  induction f with
  | var i => exact h i (by simp [leaves])
  | and p q hp hq =>
    simp only [leaves, List.mem_append] at h
    simp [eval, hp (fun i hi => h i (Or.inl hi)), hq (fun i hi => h i (Or.inr hi))]
  | or p q hp hq =>
    simp only [leaves, List.mem_append] at h
    simp [eval, hp (fun i hi => h i (Or.inl hi)), hq (fun i hi => h i (Or.inr hi))]

private theorem eval_replace (f term : RawFormula) (i : Nat) (v : Nat → Bool) :
    (f.replace i term).eval v = f.eval (fun j => if j = i then term.eval v else v j) := by
  induction f with
  | var j => by_cases h : j = i <;> simp [replace, eval, h]
  | and p q hp hq => simp [replace, eval, hp, hq]
  | or p q hp hq => simp [replace, eval, hp, hq]

private theorem mem_replace (f term : RawFormula) (w i : Nat)
    (h : i ∈ (f.replace w term).leaves) : (i ∈ f.leaves ∧ i ≠ w) ∨ i ∈ term.leaves := by
  induction f with
  | var j =>
    by_cases hj : j = w
    · exact Or.inr (by simpa [replace, hj] using h)
    · have e : i = j := by simpa [replace, hj, leaves] using h
      subst i
      exact Or.inl ⟨by simp [leaves], hj⟩
  | and p q hp hq | or p q hp hq =>
    simp only [replace, leaves, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases hp h with ⟨hp, hne⟩ | ht
      · exact Or.inl ⟨Or.inl hp, hne⟩
      · exact Or.inr ht
    · rcases hq h with ⟨hq, hne⟩ | ht
      · exact Or.inl ⟨Or.inr hq, hne⟩
      · exact Or.inr ht

private theorem count_replace (f term : RawFormula) (w i : Nat) :
    (f.replace w term).leaves.count i + f.leaves.count w * [w].count i =
      f.leaves.count i + f.leaves.count w * term.leaves.count i := by
  induction f with
  | var j => by_cases hj : j = w <;> simp [replace, leaves, hj, List.count_cons, beq_iff_eq, Nat.add_comm]
  | and p q hp hq | or p q hp hq =>
    simp only [replace, leaves, List.count_append, Nat.add_mul]
    omega

private theorem length_replace (f term : RawFormula) (w : Nat) (ht : term.leaves.length = 2) :
    (f.replace w term).leaves.length = f.leaves.length + f.leaves.count w := by
  induction f with
  | var j => by_cases hj : j = w <;> simp [replace, leaves, hj, ht]
  | and p q hp hq | or p q hp hq =>
    simp only [replace, leaves, List.length_append, List.count_append, hp, hq]
    omega

private theorem restrict {n : Nat} (f : RawFormula) (h : ∀ i ∈ f.leaves, i < n) :
    ∃ φ : DMFormula n, Positive φ ∧ labels φ = f.leaves ∧ φ.leaves = f.leaves.length ∧
      ∀ (x : Fin n → Bool), φ.eval x = f.eval (fun i => (List.ofFn x).getD i false) := by
  induction f with
  | var i =>
    have hi := h i (by simp [leaves])
    refine ⟨.lit ⟨i, hi⟩ true, rfl, rfl, rfl, fun x => ?_⟩
    simp [DMFormula.eval, eval, List.getD_eq_getElem?_getD, hi]
  | and p q hp hq =>
    have hp' : ∀ i ∈ p.leaves, i < n := fun i hi => h i (by simp [leaves, hi])
    have hq' : ∀ i ∈ q.leaves, i < n := fun i hi => h i (by simp [leaves, hi])
    obtain ⟨φ, hφ, lφ, sφ, eφ⟩ := hp hp'
    obtain ⟨ψ, hψ, lψ, sψ, eψ⟩ := hq hq'
    exact ⟨.and φ ψ, ⟨hφ, hψ⟩, by simp [labels, leaves, lφ, lψ],
      by simp [DMFormula.leaves, leaves, sφ, sψ], fun x => by simp [DMFormula.eval, eval, eφ, eψ]⟩
  | or p q hp hq =>
    have hp' : ∀ i ∈ p.leaves, i < n := fun i hi => h i (by simp [leaves, hi])
    have hq' : ∀ i ∈ q.leaves, i < n := fun i hi => h i (by simp [leaves, hi])
    obtain ⟨φ, hφ, lφ, sφ, eφ⟩ := hp hp'
    obtain ⟨ψ, hψ, lψ, sψ, eψ⟩ := hq hq'
    exact ⟨.or φ ψ, ⟨hφ, hψ⟩, by simp [labels, leaves, lφ, lψ],
      by simp [DMFormula.leaves, leaves, sφ, sψ], fun x => by simp [DMFormula.eval, eval, eφ, eψ]⟩

end RawFormula

private def runWires (gs : List Gate) (ws : List Bool) : List Bool := (⟨gs, 0⟩ : Circuit).wires ws

private theorem runWires_append (gs : List Gate) (g : Gate) (ws : List Bool) :
    runWires (gs ++ [g]) ws = runWires gs ws ++ [g.op.eval (g.inputs.map fun i => (runWires gs ws).getD i false)] := by
  simp [runWires, Circuit.wires]

private theorem runWires_length (gs : List Gate) (ws : List Bool) :
    (runWires gs ws).length = ws.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runWires, Circuit.wires]
  | append_singleton gs g ih => simp [runWires_append, ih, Nat.add_assoc]

abbrev BinaryEarlier (n : Nat) (gs : List Gate) : Prop :=
  ∀ k g, gs[k]? = some g →
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n+k ∧ b < n+k

private theorem peel (n : Nat) (gs : List Gate) (shape : BinaryEarlier n gs) (f : RawFormula)
    (valid : ∀ i ∈ f.leaves, i < n + gs.length)
    (once : ∀ i, n ≤ i → (f.leaves ++ gs.flatMap Gate.inputs).count i ≤ 1) :
    ∃ (φ : DMFormula n) (used : Nat), Positive φ ∧ used ≤ gs.length ∧
      φ.leaves = f.leaves.length + used ∧
      (∀ x, φ.eval x = f.eval (fun i => (runWires gs (List.ofFn x)).getD i false)) ∧
      (∀ i, (labels φ).count i ≤ (f.leaves ++ gs.flatMap Gate.inputs).count i) ∧
      (used = gs.length → ∀ i < n, (labels φ).count i = (f.leaves ++ gs.flatMap Gate.inputs).count i) := by
  induction gs using List.reverseRecOn generalizing f with
  | nil =>
    obtain ⟨φ, hpositive, hlabels, hsize, heval⟩ := f.restrict (by simpa using valid)
    exact ⟨φ, 0, hpositive, by simp, by simpa using hsize, heval,
      fun i => by simp [hlabels], fun _ i _ => by simp [hlabels]⟩
  | append_singleton gs g ih =>
    let w := n + gs.length
    have hindex : (gs ++ [g])[gs.length]? = some g := by simp
    obtain ⟨hop, a, b, hin, ha, hb⟩ := shape gs.length g hindex
    let term := if g.op.eval [] then RawFormula.and (.var a) (.var b) else RawFormula.or (.var a) (.var b)
    have ht : term.leaves = g.inputs := by
      rcases hop with h | h <;> simp [term, h, hin, GateOp.eval, RawFormula.leaves]
    let f' := f.replace w term
    let k := f.leaves.count w
    have hvalid' : ∀ i ∈ f'.leaves, i < n + gs.length := by
      intro i hi
      rcases RawFormula.mem_replace f term w i hi with ⟨hi, hne⟩ | hi
      · have := valid i hi
        simp [List.length_append] at this
        dsimp [w] at hne
        omega
      · rw [ht, hin] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
    have hk : k ≤ 1 := by
      have := once w (by simp [w])
      simp only [List.count_append] at this
      omega
    have hstep (i : Nat) : f'.leaves.count i + k * [w].count i =
        f.leaves.count i + k * g.inputs.count i := by
      simpa only [f', k, ht] using RawFormula.count_replace f term w i
    have hcounts (i : Nat) : (f'.leaves ++ gs.flatMap Gate.inputs).count i ≤
        (f.leaves ++ (gs ++ [g]).flatMap Gate.inputs).count i := by
      have hs := hstep i
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.count_append]
      have cases_k : k = 0 ∨ k = 1 := by omega
      rcases cases_k with h0 | h1
      · simp only [h0, Nat.zero_mul, Nat.add_zero] at hs
        omega
      · simp only [h1, Nat.one_mul] at hs
        omega
    have hshape' : BinaryEarlier n gs := by
      intro i h hi
      apply shape i h
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1, hi]
    obtain ⟨φ, used, hpositive, hused, hsize, heval, hcounts', heq⟩ :=
      ih hshape' f' hvalid' (fun i hi => (hcounts i).trans (once i hi))
    refine ⟨φ, used+k, hpositive, by simp; omega, ?_, ?_,
      fun i => (hcounts' i).trans (hcounts i), ?_⟩
    · have hlen := RawFormula.length_replace f term w (by simp [ht, hin])
      change f'.leaves.length = _ at hlen
      omega
    · intro x
      rw [heval, RawFormula.eval_replace]
      apply RawFormula.eval_congr
      intro i hi
      let ws := runWires gs (List.ofFn x)
      have hwlen : ws.length = w := by simp [ws, runWires_length, w]
      rw [runWires_append]
      change (if i = w then term.eval (fun j => ws.getD j false) else ws.getD i false) =
        (ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]).getD i false
      by_cases hiw : i = w
      · subst i
        rw [ite_eq_left rfl, List.getD_append_right _ _ _ _ (by omega)]
        rcases hop with h | h <;> simp [hwlen, term, h, hin, RawFormula.eval, GateOp.eval]
      · rw [ite_eq_right hiw, List.getD_append _ _ _ _]
        have := valid i hi
        simp [List.length_append] at this
        omega
    · intro htight i hi
      have hused' : used = gs.length := by simp at htight; omega
      have hk' : k = 1 := by simp at htight; omega
      have hne : w ≠ i := by dsimp [w]; omega
      have step := hstep i
      rw [hk'] at step
      simp [hne] at step
      rw [heq hused' i hi]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.count_append]
      omega

theorem exists_formula (n : Nat) (C : Circuit) (shape : BinaryEarlier n C.gates)
    (hout : n ≤ C.output) (hvalid : C.output < n + C.size)
    (once : ((C.output :: C.gates.flatMap Gate.inputs).filter fun i => decide (n ≤ i)).Nodup) :
    ∃ φ : DMFormula n, Positive φ ∧ φ.leaves ≤ C.size+1 ∧
      (∀ x, φ.eval x = C.eval (List.ofFn x)) ∧
      (∀ i < n, (labels φ).count i ≤ (C.gates.flatMap Gate.inputs).count i) ∧
      (φ.leaves = C.size+1 → ∀ i < n, (labels φ).count i = (C.gates.flatMap Gate.inputs).count i) := by
  let f := RawFormula.var C.output
  have hvalid' : ∀ i ∈ f.leaves, i < n + C.gates.length := by
    intro i hi
    simp [f, RawFormula.leaves] at hi
    simpa only [hi, Circuit.size] using hvalid
  have honce (i : Nat) (hi : n ≤ i) : (f.leaves ++ C.gates.flatMap Gate.inputs).count i ≤ 1 := by
    have h := List.nodup_iff_count_le_one.mp once i
    rw [List.count_filter (by simpa using hi)] at h
    exact h
  obtain ⟨φ, used, hp, hu, hl, heval, hc, hn⟩ := peel n C.gates shape f hvalid' honce
  have hl' : φ.leaves = 1 + used := hl
  refine ⟨φ, hp, by simp [Circuit.size]; omega, heval, ?_, ?_⟩
  · intro i hi
    have hne : C.output ≠ i := by omega
    simpa [f, RawFormula.leaves, hne] using hc i
  · intro tight i hi
    have hs : used = C.gates.length := by simp [Circuit.size] at tight; omega
    have hne : C.output ≠ i := by omega
    simpa [f, RawFormula.leaves, hne] using hn hs i hi

end PEqualNP.Outside.L_meta_3793

namespace PEqualNP.Outside.L_meta_3793

open scoped BigOperators

private theorem splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private theorem formulaRectangles {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (leafLabel φ i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (leafLabel φ i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      refine ⟨X, Y, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by
                change x (Fin.addCases (leafLabel a) (leafLabel b) (Fin.castAdd b.leaves i)) = true
                rwa [Fin.addCases_left]⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by
                change x (Fin.addCases (leafLabel a) (leafLabel b) (Fin.natAdd a.leaves i)) = true
                rwa [Fin.addCases_right]⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by
                change y (Fin.addCases (leafLabel a) (leafLabel b) (Fin.castAdd b.leaves i)) = false
                rwa [Fin.addCases_left]⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by
                change y (Fin.addCases (leafLabel a) (leafLabel b) (Fin.natAdd a.leaves i)) = false
                rwa [Fin.addCases_right]⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      refine ⟨X, Y, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by
                change x (Fin.addCases (leafLabel a) (leafLabel b) (Fin.castAdd b.leaves i)) = true
                rwa [Fin.addCases_left]⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by
                change x (Fin.addCases (leafLabel a) (leafLabel b) (Fin.natAdd a.leaves i)) = true
                rwa [Fin.addCases_right]⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by
                change y (Fin.addCases (leafLabel a) (leafLabel b) (Fin.castAdd b.leaves i)) = false
                rwa [Fin.addCases_left]⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by
                change y (Fin.addCases (leafLabel a) (leafLabel b) (Fin.natAdd a.leaves i)) = false
                rwa [Fin.addCases_right]⟩

private lemma unit_mem {I : Type} [Fintype I] [DecidableEq I]
    (W : Submodule ℚ (I → ℚ)) (i : I) (x : I → ℚ) (hx : x ∈ W) (hi : x i = 1)
    (rest : ∀ j ≠ i, x j = 0 ∨ Pi.single j (1 : ℚ) ∈ W) :
    Pi.single i (1 : ℚ) ∈ W := by
  classical
  let part : I → ℚ := ∑ j ∈ Finset.univ.erase i, x j • Pi.single j 1
  have hp : part ∈ W := by
    apply W.sum_mem
    intro j hj
    rcases rest j (Finset.mem_erase.mp hj).1 with hz | hu
    · simp [hz]
    · exact W.smul_mem _ hu
  have eq : x - part = Pi.single i 1 := by
    ext j
    change x j - (∑ k ∈ Finset.univ.erase i, x k • Pi.single k (1 : ℚ)) j = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases he : j = i
    · subst j
      rw [Finset.sum_eq_zero]
      · simp [hi]
      · intro k hk
        simp [Pi.single_eq_of_ne (Finset.mem_erase.mp hk).1.symm]
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨he, Finset.mem_univ _⟩)]
      · simp [Pi.single_eq_of_ne he]
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk.symm]
  rw [← eq]
  exact W.sub_mem hx hp

private lemma rank_bound {I L : Type} [Fintype I] [Fintype L] [DecidableEq I]
    (R : L → I → ℚ) (hu : ∀ i, Pi.single i (1 : ℚ) ∈ Submodule.span ℚ (Set.range R)) :
    Fintype.card I ≤ Fintype.card L := by
  classical
  let W := Submodule.span ℚ (Set.range R)
  have htop : W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have eq : x = ∑ i, x i • Pi.single i (1 : ℚ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [eq]
    exact W.sum_mem fun i _ => W.smul_mem (x i) (hu i)
  have le : Module.finrank ℚ W ≤ Fintype.card L := by
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    exact Fintype.card_range_le R
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at le
  exact le

private lemma endpoints {V : Type} {G : SimpleGraph V} [Fintype G.edgeSet]
    (e : ↥G.edgeFinset) : ∃ u v, G.Adj u v ∧ Sym2.mk u v = e.val := by
  have mem := SimpleGraph.mem_edgeFinset.mp e.prop
  revert mem
  refine Sym2.inductionOn e.val ?_
  intro u v mem
  exact ⟨u,v,mem,rfl⟩

private def Independent {V : Type} (G : SimpleGraph V) (P : V → Prop) : Prop :=
  ∀ x y, P x → P y → ¬ G.Adj x y

private def pairColumn {V : Type} (G : SimpleGraph V) (u v x : V) : Prop :=
  (G.Adj u x ∨ G.Adj v x) ∧ x ≠ u ∧ x ≠ v

private theorem pairColumn_symm {V : Type} (G : SimpleGraph V) (u v : V) :
    pairColumn G u v = pairColumn G v u := by
  funext x
  apply propext
  constructor <;> rintro ⟨h, hu, hv⟩ <;> exact ⟨h.symm, hv, hu⟩

private theorem pairColumn_independent {V : Type} (G : SimpleGraph V)
    (htri : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (h4 : ∀ a b c d : V, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    {u v : V} (e : G.Adj u v) :
    Independent G (pairColumn G u v) := by
  rintro x y ⟨hux | hvx, hxu, hxv⟩ ⟨huy | hvy, hyu, hyv⟩ hxy
  · exact htri u x y hux hxy huy
  · exact h4 u x y v hxu.symm hyu.symm e.ne hxy.ne hxv hyv hux hxy hvy.symm e.symm
  · exact h4 v x y u hxv.symm hyv.symm e.ne.symm hxy.ne hxu hyu hvx hxy huy.symm e
  · exact htri v x y hvx hxy hvy

theorem formula_rank {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (φ : DMFormula n)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c)
    (h4 : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (hm : DMFormula.rec (motive := fun _ : DMFormula n => Prop)
      (fun _ c => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ)
    (hf : ∀ x, φ.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ win lose : ↥G.edgeFinset → Fin n,
      (∀ e, G.Adj (lose e) (win e) ∧ s(lose e, win e) = e.val) ∧
      ∀ v, ((Finset.univ : Finset ↥G.edgeFinset).filter (fun e => lose e = v)).card +
        (if v ∈ (Finset.univ : Finset ↥G.edgeFinset).image win then 1 else 0) ≤
        (leafLabels φ).count v := by
  classical
  let V := Fin n
  let E := ↥G.edgeFinset
  obtain ⟨X, Y, partition, goodX, goodY⟩ := formulaRectangles φ hm
  let row (u v : V) (z : V) : Bool := decide (z = u ∨ z = v)
  let col (P : V → Prop) (z : V) : Bool := decide (P z)
  have hpos {u v : V} (e : G.Adj u v) : φ.eval (row u v) = true :=
    (hf _).mpr ⟨u, v, e, by simp [row], by simp [row]⟩
  have hneg {P : V → Prop} (hP : Independent G P) : φ.eval (col P) = false := by
    apply Bool.eq_false_iff.mpr
    rintro h
    obtain ⟨u, v, he, hu, hv⟩ := (hf _).mp h
    exact hP u v (of_decide_eq_true hu) (of_decide_eq_true hv) he
  let route {u v : V} (e : G.Adj u v) {P : V → Prop} (hP : Independent G P) :=
    Classical.choose (partition (row u v) (col P) (hpos e) (hneg hP))
  have routeMem {u v : V} (e : G.Adj u v) {P : V → Prop} (hP : Independent G P) :
      X (route e hP) (row u v) ∧ Y (route e hP) (col P) :=
    (Classical.choose_spec (partition (row u v) (col P) (hpos e) (hneg hP))).1
  have routeEq {u v : V} (e : G.Adj u v) {P : V → Prop} (hP : Independent G P)
      (i : Fin φ.leaves) (hx : X i (row u v)) (hy : Y i (col P)) : i = route e hP :=
    (Classical.choose_spec (partition (row u v) (col P) (hpos e) (hneg hP))).2 i ⟨hx, hy⟩
  have force {u v : V} (e : G.Adj u v) {P : V → Prop} (hP : Independent G P) (hv : P v) :
      leafLabel φ (route e hP) = u := by
    rcases of_decide_eq_true ((goodX _ _ (routeMem e hP).1).2) with hu | he
    · exact hu
    · have hv' : ¬ P (leafLabel φ (route e hP)) :=
        of_decide_eq_false ((goodY _ _ (routeMem e hP).2).2)
      exact (hv' (he.symm ▸ hv)).elim
  choose u v huv using (fun e : E => endpoints e)
  let pairInd {a b : V} (e : G.Adj a b) := pairColumn_independent G htri h4 e
  let win (e : E) : V := leafLabel φ (route (huv e).1 (pairInd (huv e).1))
  let lose (e : E) : V := if win e = u e then v e else u e
  have ordered (e : E) :
      G.Adj (lose e) (win e) ∧ s(lose e, win e) = e.val := by
    have he : win e = u e ∨ win e = v e :=
      of_decide_eq_true ((goodX _ _ (routeMem (huv e).1 (pairInd (huv e).1)).1).2)
    rcases he with he | he
    · simpa [lose, he] using And.intro (huv e).1.symm (Sym2.eq_swap.trans (huv e).2)
    · simpa [lose, he, (huv e).1.ne.symm] using huv e
  have pairLose (e : E) :
      leafLabel φ (route (ordered e).1 (pairInd (ordered e).1)) = win e := by
    have he : win e = u e ∨ win e = v e :=
      of_decide_eq_true ((goodX _ _ (routeMem (huv e).1 (pairInd (huv e).1)).1).2)
    have hrow : row (lose e) (win e) = row (u e) (v e) := by
      rcases he with he | he
      · funext a
        simp [lose, he, row, Bool.or_comm]
      · simp [lose, he, (huv e).1.ne.symm]
    have hcol : pairColumn G (lose e) (win e) = pairColumn G (u e) (v e) := by
      rcases he with he | he
      · simpa [lose, he] using pairColumn_symm G (v e) (u e)
      · simp [lose, he, (huv e).1.ne.symm]
    have hroute := routeEq (huv e).1 (pairInd (huv e).1)
      (route (ordered e).1 (pairInd (ordered e).1))
      (hrow ▸ (routeMem (ordered e).1 (pairInd (ordered e).1)).1)
      ((congrArg col hcol) ▸ (routeMem (ordered e).1 (pairInd (ordered e).1)).2)
    exact congrArg (leafLabel φ) hroute
  refine ⟨win, lose, ordered, ?_⟩
  intro z
  let Losers := (Finset.univ : Finset E).filter (fun e => lose e = z)
  let Winners := (Finset.univ : Finset E).image win
  let A := { a : Unit // z ∈ Winners }
  let I := (↥Losers) ⊕ A
  let L := { i : Fin φ.leaves // leafLabel φ i = z }
  have loser_eq (e : ↥Losers) : lose e.val = z := (Finset.mem_filter.mp e.prop).2
  have anchorExists (a : A) : ∃ e : E, win e = z := by
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp a.prop
    exact ⟨e, he⟩
  let anchor (a : A) : E := Classical.choose (anchorExists a)
  have anchor_eq (a : A) : win (anchor a) = z := Classical.choose_spec (anchorExists a)
  let other : I → V := Sum.elim (fun e => win e.val) (fun a => lose (anchor a))
  have adjOther (i : I) : G.Adj z (other i) := by
    rcases i with e | a
    · exact loser_eq e ▸ (ordered e.val).1
    · exact anchor_eq a ▸ (ordered (anchor a)).1.symm
  have sameUnderlying (e f : E) (h : s(lose e, win e) = s(lose f, win f)) : e = f :=
    Subtype.ext ((ordered e).2.symm.trans (h.trans (ordered f).2))
  have lrNe (e : ↥Losers) (a : A) : other (.inl e) ≠ other (.inr a) := by
    intro h
    change win e.val = lose (anchor a) at h
    have ee : e.val = anchor a := sameUnderlying _ _ (by rw [loser_eq e, anchor_eq a, h, Sym2.eq_swap])
    have h' : lose e.val = win e.val := (loser_eq e).trans ((congrArg win ee).trans (anchor_eq a)).symm
    exact (ordered e.val).1.ne h'
  have other_inj : Function.Injective other := by
    rintro (e | a) (f | b) h
    · change win e.val = win f.val at h
      exact congrArg Sum.inl (Subtype.ext (sameUnderlying _ _ (by rw [loser_eq e, loser_eq f, h])))
    · exact False.elim (lrNe e b h)
    · exact False.elim (lrNe f a h.symm)
    · exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim _ _))
  let base : V → Prop := G.Adj z
  have baseInd : Independent G base := fun a b ha hb h => htri z a b ha h hb
  let R (l : L) (i : I) : ℚ := if X l.val (row z (other i)) then 1 else 0
  let W := Submodule.span ℚ (Set.range R)
  let colVec (P : V → Prop) : I → ℚ := ∑ l : L, if Y l.val (col P) then R l else 0
  have colMem (P : V → Prop) : colVec P ∈ W := by
    apply W.sum_mem
    intro l _
    split
    · exact Submodule.subset_span ⟨l, rfl⟩
    · exact W.zero_mem
  have colValue {P : V → Prop} (hP : Independent G P) (i : I) :
      colVec P i = if leafLabel φ (route (adjOther i) hP) = z then 1 else 0 := by
    simp only [colVec, Finset.sum_apply]
    by_cases hr : leafLabel φ (route (adjOther i) hP) = z
    · let l : L := ⟨route (adjOther i) hP, hr⟩
      rw [Finset.sum_eq_single l]
      · simp [R, l, hr, (routeMem (adjOther i) hP).1, (routeMem (adjOther i) hP).2]
      · intro i' _ hne
        by_cases hh : X i'.val (row z (other i)) ∧ Y i'.val (col P)
        · exact False.elim (hne (Subtype.ext (routeEq (adjOther i) hP _ hh.1 hh.2)))
        · by_cases hY : Y i'.val (col P)
          · have hX : ¬ X i'.val (row z (other i)) := fun hX => hh ⟨hX, hY⟩
            simp [hY, R, hX]
          · simp [hY]
      · simp
    · rw [ite_eq_right hr]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hY : Y j.val (col P)
      · have hX : ¬ X j.val (row z (other i)) := fun hX =>
          hr ((congrArg (leafLabel φ) (routeEq (adjOther i) hP j.val hX hY)).symm.trans j.prop)
        simp [hY, R, hX]
      · simp [hY]
  have baseValue (i : I) : colVec base i = 1 := by
    rw [colValue baseInd i, ite_eq_left (force (adjOther i) baseInd (adjOther i))]
  have edgeUnit (e : ↥Losers) : Pi.single (Sum.inl e : I) (1 : ℚ) ∈ W := by
    let i : I := .inl e
    let P := pairColumn G z (other i)
    have hP : Independent G P := pairInd (adjOther i)
    have hself : leafLabel φ (route (adjOther i) hP) = other i := by
      have hrow : row z (other i) = row (lose e.val) (win e.val) := by
        change row z (win e.val) = _
        rw [loser_eq e]
      have hcol : P = pairColumn G (lose e.val) (win e.val) := by
        change pairColumn G z (win e.val) = _
        rw [loser_eq e]
      have hroute := routeEq (ordered e.val).1 (pairInd (ordered e.val).1)
        (route (adjOther i) hP) (hrow ▸ (routeMem (adjOther i) hP).1)
        ((congrArg col hcol) ▸ (routeMem (adjOther i) hP).2)
      exact (congrArg (leafLabel φ) hroute).trans (pairLose e.val)
    have hdiff : colVec base - colVec P = Pi.single i 1 := by
      funext j
      change colVec base j - colVec P j = _
      rw [baseValue]
      by_cases hj : j = i
      · subst j
        rw [colValue hP, hself, ite_eq_right (adjOther i).ne.symm]
        simp
      · have hn : other j ≠ other i := fun h => hj (other_inj h)
        have hmember : P (other j) := ⟨Or.inl (adjOther j), (adjOther j).ne.symm, hn⟩
        rw [colValue hP, ite_eq_left (force (adjOther j) hP hmember)]
        simp [Pi.single_eq_of_ne hj]
    rw [← hdiff]
    exact W.sub_mem (colMem base) (colMem P)
  have hspan (i : I) : Pi.single i (1 : ℚ) ∈ W := by
    rcases i with e | a
    · exact edgeUnit e
    · apply unit_mem W (.inr a) (colVec base) (colMem base) (baseValue (.inr a))
      rintro (e | b) hne
      · exact Or.inr (edgeUnit e)
      · exact False.elim (hne (congrArg Sum.inr (Subtype.ext (Subsingleton.elim _ _))))
  have hc := rank_bound R hspan
  have hL : Fintype.card L = (leafLabels φ).count z := by
    rw [← ofFn_leafLabel, List.count_ofFn]
    exact Fintype.card_subtype (fun i : Fin φ.leaves => leafLabel φ i = z)
  have hI : Fintype.card I = Losers.card + (if z ∈ Winners then 1 else 0) := by
    rw [Fintype.card_sum, Fintype.card_coe]
    by_cases h : z ∈ Winners <;> simp [A, h]
  rw [hI, hL] at hc
  exact hc

end PEqualNP.Outside.L_meta_3793

namespace PEqualNP.Outside.L_meta_3793

open scoped BigOperators

theorem tight_slots {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (lose win : α → β) (labels : List β) (t : ℕ)
    (hmin : t ≤ (Finset.univ.image win).card)
    (hbudget : labels.length ≤ Fintype.card α + t)
    (hslots : ∀ v, ((Finset.univ : Finset α).filter (fun e => lose e = v)).card +
      (if v ∈ (Finset.univ.image win) then 1 else 0) ≤ labels.count v) :
    (Finset.univ.image win).card = t ∧ labels.length = Fintype.card α + t ∧
      ∀ v, labels.count v = ((Finset.univ : Finset α).filter (fun e => lose e = v)).card +
        (if v ∈ (Finset.univ.image win) then 1 else 0) := by
  let W : Finset β := Finset.univ.image win
  let d : β → ℕ := fun v => ((Finset.univ : Finset α).filter (fun e => lose e = v)).card +
    (if v ∈ W then 1 else 0)
  have hlose : (∑ v : β, ((Finset.univ : Finset α).filter (fun e => lose e = v)).card) =
      Fintype.card α := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset α)
      (Finset.univ : Finset β) lose
  have hwin : (∑ v : β, if v ∈ W then (1 : ℕ) else 0) = W.card := by
    rw [← Finset.sum_filter]
    simp
  have hd : ∑ v : β, d v = Fintype.card α + W.card := by
    simp only [d, Finset.sum_add_distrib, hlose, hwin]
  have hlabels : (∑ v : β, labels.count v) = labels.length := by
    simpa using Multiset.sum_count_eq_card (m := (labels : Multiset β)) (fun _ _ => Finset.mem_univ _)
  have hle : (∑ v : β, d v) ≤ ∑ v : β, labels.count v :=
    Finset.sum_le_sum fun v _ => hslots v
  rw [hd, hlabels] at hle
  have hW : W.card = t := by dsimp [W] at *; omega
  have hlen : labels.length = Fintype.card α + t := by omega
  refine ⟨hW, hlen, fun v => le_antisymm ?_ (hslots v)⟩
  by_contra! hn
  have hlt : (∑ i : β, d i) < ∑ i : β, labels.count i :=
    Finset.sum_lt_sum (fun i _ => hslots i) ⟨v, Finset.mem_univ _, hn⟩
  rw [hd, hlabels] at hlt
  omega

end PEqualNP.Outside.L_meta_3793

namespace PEqualNP.Outside.L_meta_3793

theorem cover_of_winners {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (lose win : ↥G.edgeFinset → V)
    (hw : ∀ e, G.Adj (lose e) (win e) ∧ s(lose e, win e) = e.val) :
    CoverPromise.IsVertexCover G ((Finset.univ : Finset ↥G.edgeFinset).image win) := by
  intro u v huv
  let e : ↥G.edgeFinset := ⟨s(u, v), by simpa using huv⟩
  have hwin : win e ∈ Finset.univ.image win :=
    Finset.mem_image_of_mem _ (Finset.mem_univ e)
  have he : s(lose e, win e) = s(u, v) := (hw e).2
  rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inr (h ▸ hwin)
  · exact Or.inl (h ▸ hwin)

theorem winner_count_once {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lose win : ↥G.edgeFinset → V) (labels : List V)
    (hw : ∀ e, G.Adj (lose e) (win e))
    (hind : ∀ u v, G.Adj u v → u ∈ Finset.univ.image win → v ∈ Finset.univ.image win → False)
    (hcount : ∀ v, labels.count v =
      ((Finset.univ : Finset (↥G.edgeFinset)).filter (fun e => lose e = v)).card +
        (if v ∈ (Finset.univ.image win) then 1 else 0))
    (v : V) (hv : v ∈ Finset.univ.image win) :
    labels.count v = 1 := by
  have noLose (e : ↥G.edgeFinset) : lose e ≠ v := by
    intro he
    have hwin : win e ∈ Finset.univ.image win :=
      Finset.mem_image_of_mem _ (Finset.mem_univ e)
    exact hind _ _ (hw e) (he.symm ▸ hv) hwin
  rw [hcount, ite_eq_left hv]
  simp [noLose]

end PEqualNP.Outside.L_meta_3793

namespace PEqualNP.Outside.L_meta_3793

open PEqualNP.CircuitLowerBounds

private def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl appendGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, appendGate, List.length_append, List.length_cons,
      List.length_nil]
    omega

private theorem fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp [appendGate]; omega

theorem output_bounds (C : Circuit)
    (eval_spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) :
    14 ≤ C.output ∧ C.output < 14 + C.size := by
  constructor
  · by_contra! ho
    let j : Fin 14 := ⟨C.output, ho⟩
    let x : Fin 14 → Bool := fun i => decide (i = j)
    have hi : C.output < (List.ofFn x).length := by simpa using ho
    have h : C.eval (List.ofFn x) = true := by
      change (C.gates.foldl appendGate (List.ofFn x)).getD C.output false = true
      rw [fold_prefix _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
      change decide (j = j) = true
      simp
    obtain ⟨p, l, _, hp, hl⟩ := (eval_spec x).mp h
    have ep : Fin.castAdd 7 p = j := by simpa [x] using hp
    have el : Fin.natAdd 7 l = j := by simpa [x] using hl
    have e := congrArg Fin.val (ep.trans el.symm)
    change p.val = 7 + l.val at e
    omega
  · by_contra! ho
    let x : Fin 14 → Bool := fun _ => true
    have h : C.eval (List.ofFn x) = true := (eval_spec x).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    change (C.gates.foldl appendGate (List.ofFn x)).getD C.output false = true at h
    rw [List.getD_eq_default] at h
    · contradiction
    · rw [fold_length, List.length_ofFn]
      exact ho

end PEqualNP.Outside.L_meta_3793

namespace PEqualNP.Outside.L_meta_3793

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3793.Fano

private theorem not_both_sides (p l : Fin 7)
    (hp : point p ∈ points) (hl : line l ∈ points) : False := by
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hl
  have h := congrArg Fin.val hq
  change q.val = 7 + l.val at h
  omega

private theorem line_side_excludes_point (p : Fin 7) : point p ∉ lines := by
  intro hp
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hp
  have h := congrArg Fin.val hl
  change 7 + l.val = p.val at h
  omega

private theorem independent_side (W : Finset (Fin 14)) (hside : W = points ∨ W = lines)
    (u v : Fin 14) (hadj : fanoGraph.Adj u v) (hu : u ∈ W) (hv : v ∈ W) : False := by
  obtain ⟨p, l, _, h⟩ := (fanoAdj_iff _ _).mp hadj
  rcases hside with rfl | rfl <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact not_both_sides p l hu hv
  · exact not_both_sides p l hv hu
  · exact line_side_excludes_point p hu
  · exact line_side_excludes_point p hv

end PEqualNP.Outside.L_meta_3793

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3793 PEqualNP.Outside.L_meta_3793.Fano

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.L_meta_3793 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)), (x1.size ≤ (27 : ℕ) ∧ (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 ≠ x8 ∧ x7 < (14 : ℕ) + x4 ∧ x8 < (14 : ℕ) + x4) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) → (List.filter (fun (x5 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x5)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → List.count (↑x2) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ≤ (1 : ℕ) ∨ List.count ((7 : ℕ) + ↑x3) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ≤ (1 : ℕ)
:= by
  intro C p l hc honce incidence
  obtain ⟨hsize, hshape, hcEval⟩ := hc
  have shape : BinaryEarlier 14 C.gates := by
    intro i g hg
    obtain ⟨hop, a, b, hs, _, ha, hb⟩ := hshape i g hg
    exact ⟨hop, a, b, hs, ha, hb⟩
  obtain ⟨hout, hvalid⟩ := output_bounds C hcEval
  obtain ⟨φ, hpos, hle, heval, _, hcount⟩ := exists_formula 14 C shape hout hvalid honce
  have hfun (x : Fin 14 → Bool) : φ.eval x = true ↔
      ∃ u v, fanoGraph.Adj u v ∧ x u = true ∧ x v = true := by
    rw [heval, hcEval]
    constructor
    · rintro ⟨p', l', hadj, hp, hl⟩
      exact ⟨point p', line l', (fanoAdj_iff _ _).mpr ⟨p', l', hadj, Or.inl ⟨rfl, rfl⟩⟩,
        hp, hl⟩
    · rintro ⟨u, v, hadj, hu, hv⟩
      obtain ⟨p', l', hi, hu'⟩ := (fanoAdj_iff _ _).mp hadj
      rcases hu' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p', l', hi, hu, hv⟩
      · exact ⟨p', l', hi, hv, hu⟩
  obtain ⟨win, lose, hw, hslots⟩ :=
    formula_rank fanoGraph φ triangleFree_fano noFour_fano hpos hfun
  let W := (Finset.univ : Finset ↥fanoGraph.edgeFinset).image win
  have hcover : CoverPromise.IsVertexCover fanoGraph W := cover_of_winners fanoGraph lose win hw
  have hmin : 7 ≤ W.card := vertexCover_card_ge W hcover
  have hedge : Fintype.card (↥fanoGraph.edgeFinset) = 21 := by
    rw [Fintype.card_coe, edgeCard_fano]
  have hbudget : (leafLabels φ).length ≤ Fintype.card (↥fanoGraph.edgeFinset) + 7 := by
    rw [leafLabels_length, hedge]
    omega
  obtain ⟨hW, hlen, hlabel⟩ := tight_slots lose win (leafLabels φ) 7 hmin hbudget hslots
  have hside := vertexCover_eq_side W hcover hW.le
  have hleaf : φ.leaves = C.size + 1 := by
    rw [leafLabels_length, hedge] at hlen
    omega
  have honceWinner (v : Fin 14) (hv : v ∈ W) : (C.gates.flatMap Gate.inputs).count v.val = 1 := by
    rw [← hcount hleaf v.val v.isLt, count_labels]
    exact winner_count_once fanoGraph lose win (leafLabels φ) (fun e => (hw e).1)
      (independent_side W hside) hlabel v hv
  have hinc : fanoGraph.Adj (point p) (line l) :=
    (fanoAdj_iff _ _).mpr ⟨p, l, incidence, Or.inl ⟨rfl, rfl⟩⟩
  rcases hcover _ _ hinc with hp | hl
  · exact Or.inl ((honceWinner (point p) hp).le)
  · exact Or.inr ((honceWinner (line l) hl).le)
