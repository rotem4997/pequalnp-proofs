import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695

open PEqualNP.CircuitLowerBounds
open Classical

-- The single-index set of a wire.
noncomputable def T {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

-- A private gate: its single-index set lies in S and has two or more indices.
def priv {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (j : ℕ) : Prop :=
  T C (n + j) ⊆ S ∧ 2 ≤ (T (n := n) C (n + j)).card

-- Gate j reads the wire of the earlier private gate j'.
def Rel {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (j j' : ℕ) : Prop :=
  j' < j ∧ (∃ g : Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) ∧ priv C S j'

noncomputable def Q {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (r : ℕ) : Finset ℕ :=
  (Finset.range C.size).filter (fun j => Relation.ReflTransGen (Rel C S) r j)

theorem rtg_le {n : ℕ} (C : Circuit) (S : Finset (Fin n)) {r j : ℕ}
    (h : Relation.ReflTransGen (Rel C S) r j) : j ≤ r := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih =>
    have := hbc.1
    omega

theorem rtg_priv {n : ℕ} (C : Circuit) (S : Finset (Fin n)) {r j : ℕ} (hr : priv C S r)
    (h : Relation.ReflTransGen (Rel C S) r j) : priv C S j := by
  induction h with
  | refl => exact hr
  | tail _ hbc _ => exact hbc.2.2

-- The labelling, wire by wire: a gate of Qs is evaluated, any other wire gets its own label.
noncomputable def step (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Qs : Finset ℕ)
    (L : List Bool) (g : Gate) : List Bool :=
  L ++ [if L.length - n ∈ Qs then g.op.eval (g.inputs.map (fun w => L.getD w false))
    else decide (¬ T C L.length ⊆ S)]

noncomputable def base (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : List Bool :=
  (List.range n).map (fun w => decide (¬ T C w ⊆ S))

noncomputable def psi (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Qs : Finset ℕ) (w : ℕ) :
    Bool :=
  if w < n + C.size then (C.gates.foldl (step n C S Qs) (base n C S)).getD w false
  else decide (¬ T C w ⊆ S)

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem sfold_length (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Qs : Finset ℕ)
    (gs : List Gate) : ∀ L : List Bool,
    (gs.foldl (step n C S Qs) L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; simp
  | cons g gs ih =>
    intro L
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [step]
    omega

theorem sfold_prefix (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Qs : Finset ℕ)
    (gs : List Gate) : ∀ (L : List Bool) (i : ℕ), i < L.length →
    (gs.foldl (step n C S Qs) L).getD i false = L.getD i false := by
  induction gs with
  | nil => intro L i _; rfl
  | cons g gs ih =>
    intro L i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem split_at {α : Type} : ∀ (l : List α) (j : ℕ) (g : α), l[j]? = some g →
    ∃ pre post : List α, l = pre ++ g :: post ∧ pre.length = j := by
  intro l
  induction l with
  | nil => intro j g h; simp at h
  | cons x xs ih =>
    intro j g h
    cases j with
    | zero =>
      simp at h
      exact ⟨[], xs, by simp [h], rfl⟩
    | succ j =>
      simp at h
      obtain ⟨pre, post, h1, h2⟩ := ih j g h
      exact ⟨x :: pre, post, by simp [h1], by simp [h2]⟩

-- The entry written by gate number j, and the list it was computed from.
theorem sentry (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Qs : Finset ℕ) (gs : List Gate)
    (L0 : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    ∃ Lpre : List Bool, Lpre.length = L0.length + j ∧
      (∀ i, i < L0.length + j →
        Lpre.getD i false = (gs.foldl (step n C S Qs) L0).getD i false) ∧
      (gs.foldl (step n C S Qs) L0).getD (L0.length + j) false
        = (if Lpre.length - n ∈ Qs then g.op.eval (g.inputs.map (fun w => Lpre.getD w false))
            else decide (¬ T C Lpre.length ⊆ S)) := by
  obtain ⟨pre, post, h1, h2⟩ := split_at gs j g hj
  subst h1
  have hlen : (pre.foldl (step n C S Qs) L0).length = L0.length + j := by
    rw [sfold_length, h2]
  refine ⟨pre.foldl (step n C S Qs) L0, hlen, ?_, ?_⟩
  · intro i hi
    simp only [List.foldl_append, List.foldl_cons]
    rw [sfold_prefix n C S Qs post _ i (by simp [step, hlen]; omega)]
    exact (List.getD_append _ _ _ _ (by omega)).symm
  · simp only [List.foldl_append, List.foldl_cons]
    rw [sfold_prefix n C S Qs post _ (L0.length + j) (by simp [step, hlen])]
    rw [← hlen]
    simp [step, List.getD_eq_getElem?_getD]

theorem base_length (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : (base n C S).length = n := by
  simp [base]

theorem base_getD (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (w : ℕ) (h : w < n) :
    (base n C S).getD w false = decide (¬ T C w ⊆ S) := by
  simp [base, List.getD_eq_getElem?_getD, h]

theorem mem_Q {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (r j : ℕ) :
    j ∈ Q C S r ↔ (j < C.size ∧ Relation.ReflTransGen (Rel C S) r j) := by
  simp [Q]

end PEqualNP.Outside.L_meta_695

open PEqualNP.Outside.L_meta_695 in
theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  intro n r S C _ hr hsub hcard
  have hpr : priv C S r := ⟨hsub, hcard⟩
  have hbl := base_length n C S
  have hsize : C.size = C.gates.length := rfl
  refine ⟨Q C S r, psi n C S (Q C S r), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_Q C S r r).mpr ⟨hr, Relation.ReflTransGen.refl⟩
  · intro j hj
    obtain ⟨h1, h2⟩ := (mem_Q C S r j).mp hj
    have hp := rtg_priv C S hpr h2
    exact ⟨h1, hp.1, hp.2⟩
  · intro j hj hne
    obtain ⟨_, h2⟩ := (mem_Q C S r j).mp hj
    rcases Relation.ReflTransGen.cases_tail h2 with h | ⟨c, hc, hrel⟩
    · exact absurd h hne
    · have hcr := rtg_le C S hc
      obtain ⟨hlt, ⟨g, hg, hin⟩, _⟩ := hrel
      exact ⟨c, (mem_Q C S r c).mpr ⟨by omega, hc⟩, hlt, g, hg, hin⟩
  · intro j hj j' hlt hread hs hc
    obtain ⟨h1, h2⟩ := (mem_Q C S r j).mp hj
    exact (mem_Q C S r j').mpr ⟨by omega, h2.tail ⟨hlt, hread, hs, hc⟩⟩
  · intro j hj g hg
    obtain ⟨Lpre, hlen, hpre, hent⟩ := sentry n C S (Q C S r) C.gates (base n C S) j g hg
    rw [hbl] at hlen hpre hent
    have hjs : j < C.size := ((mem_Q C S r j).mp hj).1
    have e1 : psi n C S (Q C S r) (n + j)
        = (C.gates.foldl (step n C S (Q C S r)) (base n C S)).getD (n + j) false := by
      unfold psi
      rw [if_pos (by omega)]
    have e2 : Lpre.length - n = j := by omega
    rw [e1, hent, e2, if_pos hj]
    congr 1
    apply List.map_congr_left
    intro w _
    by_cases hw : w < n + j
    · rw [if_pos hw, hpre w hw]
      unfold psi
      rw [if_pos (by omega)]
    · rw [if_neg hw]
      exact getD_ge _ _ (by omega)
  · intro w hw
    unfold psi
    by_cases h1 : w < n + C.size
    · rw [if_pos h1]
      by_cases h2 : w < n
      · rw [sfold_prefix n C S (Q C S r) C.gates _ w (by omega), base_getD n C S w h2]
        exact decide_eq_true_iff
      · have hj : w - n < C.gates.length := by omega
        have hg : C.gates[w - n]? = some (C.gates[w - n]) := List.getElem?_eq_getElem hj
        obtain ⟨Lpre, hlen, _, hent⟩ :=
          sentry n C S (Q C S r) C.gates (base n C S) (w - n) _ hg
        rw [hbl] at hlen hent
        have e1 : n + (w - n) = w := by omega
        have e2 : Lpre.length - n = w - n := by omega
        have hnq : w - n ∉ Q C S r := fun hq => hw (w - n) hq (by omega)
        rw [e1, e2, if_neg hnq] at hent
        rw [hent]
        have e3 : Lpre.length = w := by omega
        rw [e3]
        exact decide_eq_true_iff
    · rw [if_neg h1]
      exact decide_eq_true_iff
