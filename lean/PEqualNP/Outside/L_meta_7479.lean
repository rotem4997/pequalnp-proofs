import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7479

open PEqualNP.CircuitLowerBounds

def Dep (S : Finset (Fin 10)) (h : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 10 → Bool, (∀ i ∈ S, x i = y i) → h x = h y

def pf (x8 : Fin 10 → Bool) : Bool :=
  x8 0 && x8 1 || x8 1 && x8 2 || x8 2 && x8 3 || x8 3 && x8 4 || x8 4 && x8 0 ||
  x8 0 && x8 5 || x8 1 && x8 6 || x8 2 && x8 7 || x8 3 && x8 8 || x8 4 && x8 9 ||
  x8 5 && x8 7 || x8 7 && x8 9 || x8 9 && x8 6 || x8 6 && x8 8 || x8 8 && x8 5

def ein (a b : Fin 10) : Fin 10 → Bool := fun i => decide (i = a ∨ i = b)

def PL : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5),
   (1,0),(2,1),(3,2),(4,3),(0,4),(5,0),(6,1),(7,2),(8,3),(9,4),(7,5),(9,7),(6,9),(8,6),(5,8)]

theorem PL_card : PL.toFinset.card = 30 := by decide

theorem PL_good : ∀ p ∈ PL, p.1 ≠ p.2 ∧ pf (ein p.1 p.2) = true := by decide

theorem single_false : ∀ b : Fin 10, pf (ein b b) = false := by decide

theorem inside (S : Finset (Fin 10)) (u : (Fin 10 → Bool) → Bool) (du : Dep S u)
    (hu : ∀ x, pf x = false → u x = false) (a b : Fin 10) (h : u (ein a b) = true) :
    a ∈ S ∧ b ∈ S := by
  constructor
  · by_contra ha
    have e : u (ein a b) = u (ein b b) := by
      apply du
      intro i hi
      have : i ≠ a := fun e => ha (e ▸ hi)
      simp [ein, this]
    rw [e, hu _ (single_false b)] at h
    exact Bool.false_ne_true h
  · by_contra hb
    have e : u (ein a b) = u (ein a a) := by
      apply du
      intro i hi
      have : i ≠ b := fun e => hb (e ▸ hi)
      simp [ein, this]
    rw [e, hu _ (single_false a)] at h
    exact Bool.false_ne_true h

theorem offDiag_le (S : Finset (Fin 10)) (hS : S.card ≤ 3) : S.offDiag.card ≤ 6 := by
  rw [Finset.offDiag_card]
  generalize S.card = n at hS ⊢
  interval_cases n <;> norm_num

theorem key (S T : Finset (Fin 10)) (hS : S.card ≤ 3) (hT : T.card ≤ 3)
    (u v : (Fin 10 → Bool) → Bool) (du : Dep S u) (dv : Dep T v)
    (hu : ∀ x, pf x = false → u x = false) (hv : ∀ x, pf x = false → v x = false) :
    ∃ x, pf x = true ∧ u x = false ∧ v x = false := by
  by_contra hne
  have hsub : PL.toFinset ⊆ S.offDiag ∪ T.offDiag := by
    intro p hp
    rw [List.mem_toFinset] at hp
    obtain ⟨hne', hpf⟩ := PL_good p hp
    rw [Finset.mem_union, Finset.mem_offDiag, Finset.mem_offDiag]
    cases hu1 : u (ein p.1 p.2)
    · cases hv1 : v (ein p.1 p.2)
      · exact absurd ⟨_, hpf, hu1, hv1⟩ hne
      · right
        exact ⟨(inside T v dv hv _ _ hv1).1, (inside T v dv hv _ _ hv1).2, hne'⟩
    · left
      exact ⟨(inside S u du hu _ _ hu1).1, (inside S u du hu _ _ hu1).2, hne'⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le S.offDiag T.offDiag
  rw [PL_card] at h1
  have h3 := offDiag_le S hS
  have h4 := offDiag_le T hT
  omega

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (w.getD i false || (b && decide (w.length = i))) := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne']
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨d, rfl⟩ : ∃ d, i = w.length + (d + 1) := ⟨i - w.length - 1, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem getD_ofFn (x : Fin 10 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < 10 <;> simp [h]

def sup0 (i : ℕ) : Finset (Fin 10) := if h : i < 10 then {⟨i, h⟩} else ∅

theorem card0 (i : ℕ) : (sup0 i).card ≤ 1 := by
  unfold sup0
  split_ifs <;> simp

theorem dep0 (i : ℕ) : Dep (sup0 i) (fun x => (List.ofFn x).getD i false) := by
  intro x y hxy
  show (List.ofFn x).getD i false = (List.ofFn y).getD i false
  rw [getD_ofFn, getD_ofFn]
  by_cases h : i < 10
  · have := hxy ⟨i, h⟩ (by simp [sup0, h])
    simp [h, this]
  · simp [h]

theorem dep_gate (op : GateOp) (l : List ℕ) (u : ℕ → (Fin 10 → Bool) → Bool)
    (S : ℕ → Finset (Fin 10)) (h : ∀ i, Dep (S i) (u i)) :
    Dep (l.toFinset.biUnion S) (fun x => op.eval (l.map fun i => u i x)) := by
  intro x y hxy
  show op.eval (l.map fun i => u i x) = op.eval (l.map fun i => u i y)
  congr 1
  apply List.map_congr_left
  intro i hi
  apply h i
  intro j hj
  apply hxy
  rw [Finset.mem_biUnion]
  exact ⟨i, List.mem_toFinset.mpr hi, hj⟩

theorem card_gate (l : List ℕ) (hl : l.length ≤ 2) (S : ℕ → Finset (Fin 10))
    (hS : ∀ i, (S i).card ≤ 1) : (l.toFinset.biUnion S).card ≤ 2 := by
  have h1 := Finset.card_biUnion_le_card_mul l.toFinset S 1 (fun i _ => hS i)
  have h2 := List.toFinset_card_le l
  omega

theorem card_gate2 (l : List ℕ) (hl : l.length ≤ 2) (S : ℕ → Finset (Fin 10))
    (hS : ∀ i, i ≠ 10 → (S i).card ≤ 1) (h10 : (S 10).card ≤ 2) :
    (l.toFinset.biUnion S).card ≤ 3 := by
  have hS' : ∀ i, (S i).card ≤ 2 := by
    intro i
    by_cases hi : i = 10
    · subst hi; exact h10
    · have := hS i hi; omega
  rcases l with _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
  · simp
  · simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.singleton_biUnion]
    have := hS' c; omega
  · simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.biUnion_insert,
      Finset.singleton_biUnion]
    by_cases hc : c = 10
    · by_cases hd : d = 10
      · subst hc; subst hd; simp only [Finset.union_self]; omega
      · have := Finset.card_union_le (S c) (S d)
        have := hS' c
        have := hS d hd
        omega
    · have := Finset.card_union_le (S c) (S d)
      have := hS c hc
      have := hS' d
      omega
  · simp at hl

end PEqualNP.Outside.L_meta_7479

theorem PEqualNP.Outside.L_meta_7479 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (16 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → (¬∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[(1 : ℕ)]? = Option.some x13) → ∃ (x14 : Fin (10 : ℕ) → Bool), x8 x14 = Bool.true ∧ x9 x14 x3 = Bool.false ∧ x9 x14 x4 = Bool.false := by
  intro x1 x2 x3 x4 h1 h2 _ x8 x9 _ _ hC hD
  open PEqualNP.Outside.L_meta_7479 in
  · have hl1 : x1.inputs.length ≤ 2 := (h1 x1 (by simp)).2
    let g1v : (Fin 10 → Bool) → Bool := fun x =>
      x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false)
    have hW1 : ∀ x : Fin 10 → Bool,
        ({ gates := [x1], output := (0 : ℕ) } : PEqualNP.CircuitLowerBounds.Circuit).wires
          (List.ofFn x) = List.ofFn x ++ [g1v x] := by
      intro x
      simp [PEqualNP.CircuitLowerBounds.Circuit.wires, g1v]
    let S1 : Finset (Fin 10) := x1.inputs.toFinset.biUnion sup0
    have dS1 : Dep S1 g1v :=
      dep_gate x1.op x1.inputs (fun i x => (List.ofFn x).getD i false) sup0 dep0
    have cS1 : S1.card ≤ 2 := card_gate x1.inputs hl1 sup0 card0
    let w1 : ℕ → (Fin 10 → Bool) → Bool := fun i x => (List.ofFn x ++ [g1v x]).getD i false
    let sup1 : ℕ → Finset (Fin 10) := fun i => if i = 10 then S1 else sup0 i
    have dep1 : ∀ i, Dep (sup1 i) (w1 i) := by
      intro i x y hxy
      simp only [w1, getD_snoc, List.length_ofFn]
      by_cases hi : i = 10
      · subst hi
        have hx : (List.ofFn x).getD 10 false = false := by rw [getD_ofFn]; simp
        have hy : (List.ofFn y).getD 10 false = false := by rw [getD_ofFn]; simp
        rw [hx, hy]
        simp only [Bool.false_or, decide_true, Bool.and_true]
        exact dS1 x y (fun j hj => hxy j (by simp only [sup1, ↓reduceIte]; exact hj))
      · have hd : decide (10 = i) = false := by simp; omega
        rw [hd]
        simp only [Bool.and_false, Bool.or_false]
        exact dep0 i x y (fun j hj => hxy j (by simp only [sup1]; rw [if_neg hi]; exact hj))
    have csup1 : ∀ i, i ≠ 10 → (sup1 i).card ≤ 1 := by
      intro i hi
      simp only [sup1, hi, ite_false]
      exact card0 i
    have csup10 : (sup1 10).card ≤ 2 := by simpa [sup1] using cS1
    have hall : ∀ k, ∃ S : Finset (Fin 10), S.card ≤ 3 ∧ Dep S (fun x => x9 x k) := by
      intro k
      match hg : x2.gates with
      | [] =>
        refine ⟨sup1 k, ?_, ?_⟩
        · by_cases hk : k = 10
          · subst hk; omega
          · have := csup1 k hk; omega
        · intro x y hxy
          have e : ∀ z, x9 z k = w1 k z := by
            intro z
            show (x2.wires (PEqualNP.CircuitLowerBounds.Circuit.wires
              { gates := [x1], output := 0 } (List.ofFn z))).getD k false = _
            rw [hW1]
            unfold PEqualNP.CircuitLowerBounds.Circuit.wires
            rw [hg, List.foldl_nil]
          show x9 x k = x9 y k
          rw [e x, e y]
          exact dep1 k x y hxy
      | [g] =>
        have hl2 : g.inputs.length ≤ 2 := (h2 g (by simp [hg])).2
        let g2v : (Fin 10 → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun i => w1 i x)
        have dS2 : Dep (g.inputs.toFinset.biUnion sup1) g2v := dep_gate g.op g.inputs w1 sup1 dep1
        have cS2 : (g.inputs.toFinset.biUnion sup1).card ≤ 3 :=
          card_gate2 g.inputs hl2 sup1 csup1 csup10
        have e : ∀ z, x9 z k = (w1 k z || (g2v z && decide (11 = k))) := by
          intro z
          show (x2.wires (PEqualNP.CircuitLowerBounds.Circuit.wires
            { gates := [x1], output := 0 } (List.ofFn z))).getD k false = _
          rw [hW1]
          unfold PEqualNP.CircuitLowerBounds.Circuit.wires
          rw [hg, List.foldl_cons, List.foldl_nil, getD_snoc]
          simp only [List.length_append, List.length_ofFn, List.length_singleton]
          rfl
        by_cases hk : k = 11
        · subst hk
          refine ⟨g.inputs.toFinset.biUnion sup1, cS2, ?_⟩
          intro x y hxy
          have z11 : ∀ z, w1 11 z = false := by
            intro z
            show (List.ofFn z ++ [g1v z]).getD 11 false = false
            rw [getD_snoc, getD_ofFn, List.length_ofFn]
            simp
          show x9 x 11 = x9 y 11
          rw [e x, e y, z11 x, z11 y]
          simp only [Bool.false_or, decide_true, Bool.and_true]
          exact dS2 x y hxy
        · refine ⟨sup1 k, ?_, ?_⟩
          · by_cases hk' : k = 10
            · subst hk'; omega
            · have := csup1 k hk'; omega
          · intro x y hxy
            have hd : decide (11 = k) = false := by simp; omega
            show x9 x k = x9 y k
            rw [e x, e y, hd]
            simp only [Bool.and_false, Bool.or_false]
            exact dep1 k x y hxy
      | g :: g' :: rest =>
        exact absurd ⟨g', by simp [hg]⟩ hD
    obtain ⟨S, hS, dS⟩ := hall x3
    obtain ⟨T, hT, dT⟩ := hall x4
    exact key S T hS hT (fun x => x9 x x3) (fun x => x9 x x4) dS dT
      (fun x hx => (hC x hx).1) (fun x hx => (hC x hx).2)
