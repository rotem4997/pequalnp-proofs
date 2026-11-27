import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5900

def matA (u v : Fin 4) : Bool :=
  (15839 : ℕ).testBit (4 * u.val + v.val)

def upperCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates :=
      [ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 5] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 10] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 11] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }
      , { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] } ]
    output := 14 }

lemma upper_mono : PEqualNP.MetaComplexity.Monotone2 upperCircuit := by
  intro g hg
  simp only [upperCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma upper_size : upperCircuit.size ≤ 7 := by
  simp [upperCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]

lemma upper_rep : PEqualNP.Represents.Represents matA upperCircuit := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide

lemma upper_bound : PEqualNP.Represents.RepSizeAtMost matA 7 :=
  ⟨upperCircuit, upper_mono, upper_size, upper_rep⟩

def stepWire (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma step_getD (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) :
    (stepWire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepWire
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma core (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (h2 : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, ∃ S : Finset (Fin n), S.card ≤ W.card + gs.length ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → ∀ w ∈ W,
        (gs.foldl stepWire (List.ofFn x)).getD w false =
          (gs.foldl stepWire (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W
    refine ⟨Finset.univ.filter (fun i : Fin n => i.val ∈ W), ?_, ?_⟩
    · simp only [List.length_nil, add_zero]
      apply Finset.card_le_card_of_injOn (fun i => i.val)
      · intro i hi
        simpa using hi
      · intro i _ j _ h
        exact Fin.ext h
    · intro x y hxy w hw
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
      by_cases hwn : w < n
      · have hx : (List.ofFn x)[w]? = some (x ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]
          simp
        have hy : (List.ofFn y)[w]? = some (y ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]
          simp
        rw [hx, hy]
        simp only [Option.getD_some]
        exact hxy ⟨w, hwn⟩ (by simp [hw])
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  | append_singleton gs g ih =>
    intro W
    have h2' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => h2 g' (by simp [hg'])
    have hg : g.inputs.length ≤ 2 := h2 g (by simp)
    have key : ∀ (S : Finset (Fin n)) (W' : Finset ℕ),
        (∀ w ∈ W, w < n + gs.length → w ∈ W') →
        (n + gs.length ∈ W → ∀ k ∈ g.inputs, k ∈ W') →
        (∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → ∀ w ∈ W',
          (gs.foldl stepWire (List.ofFn x)).getD w false =
            (gs.foldl stepWire (List.ofFn y)).getD w false) →
        ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → ∀ w ∈ W,
          ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false =
            ((gs ++ [g]).foldl stepWire (List.ofFn y)).getD w false := by
      intro S W' hlow hin hval x y hxy w hw
      have hv := hval x y hxy
      have hlx := foldl_len gs (List.ofFn x)
      have hly := foldl_len gs (List.ofFn y)
      simp only [List.length_ofFn] at hlx hly
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [step_getD, step_getD, hlx, hly]
      split_ifs with h1 h3
      · exact hv w (hlow w hw h1)
      · subst h3
        congr 1
        apply List.map_congr_left
        intro k hk
        exact hv k (hin hw k hk)
      · rfl
    by_cases hin : n + gs.length ∈ W
    · obtain ⟨S, hS, hval⟩ := ih h2' (W.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, key S _ ?_ ?_ hval⟩
      · have h1 : (W.erase (n + gs.length) ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hin]
          have := List.toFinset_card_le g.inputs
          omega
        have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hin⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw hlt
        simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨by omega, hw⟩
      · intro _ k hk
        simp [hk]
    · obtain ⟨S, hS, hval⟩ := ih h2' W
      refine ⟨S, ?_, key S W ?_ ?_ hval⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw _
        exact hw
      · intro h
        exact absurd h hin

lemma foldl_mono (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hm : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
      ∀ i : ℕ, (gs.foldl stepWire w1).getD i false = true →
        (gs.foldl stepWire w2).getD i false = true := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w1 w2 hlen hle i hi
    rw [List.foldl_cons] at hi ⊢
    apply ih (fun g' hg' => hm g' (by simp [hg'])) (stepWire w1 g) (stepWire w2 g)
    · simp [stepWire, hlen]
    · intro j hj
      simp only [step_getD, hlen] at hj ⊢
      split_ifs at hj ⊢ with h1 h2
      · exact hle j hj
      · rcases hm g (by simp) with hop | hop <;> rw [hop] at hj ⊢
        · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map,
            id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hj ⊢
          intro k hk
          exact hle k (hj k hk)
        · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map,
            id_eq] at hj ⊢
          obtain ⟨b, ⟨k, hk, hkb⟩, hbt⟩ := hj
          exact ⟨true, ⟨k, hk, hle k (hkb.trans hbt)⟩, rfl⟩
    · exact hi

lemma eval_mono (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hle : ∀ i : Fin n, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply foldl_mono C.gates
  · intro g hg
    have hmem := (hC g hg).1
    simpa using hmem
  · simp
  · intro i hi
    simp only [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hin : i < n
    · have hx : (List.ofFn x)[i]? = some (x ⟨i, hin⟩) := by
        rw [List.getElem?_eq_getElem (by simpa using hin)]
        simp
      have hy : (List.ofFn y)[i]? = some (y ⟨i, hin⟩) := by
        rw [List.getElem?_eq_getElem (by simpa using hin)]
        simp
      rw [hx] at hi
      rw [hy]
      simp only [Option.getD_some] at hi ⊢
      exact hle ⟨i, hin⟩ hi
    · rw [List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi

def pairVec (u v : Fin 4) (i : Fin 8) : Bool :=
  if i.val < 4 then decide (i.val = u.val) else decide (i.val - 4 = v.val)

lemma list_ofFn_pairVec (u v : Fin 4) :
    List.ofFn (pairVec u v) = PEqualNP.Represents.oneEach u v := by
  fin_cases u <;> fin_cases v <;> decide

lemma witness_for_missing (k : Fin 8) :
    ∃ (u0 v0 u1 v1 : Fin 4), matA u0 v0 = true ∧ matA u1 v1 = false ∧
      ∀ i : Fin 8, i ≠ k → pairVec u0 v0 i = true → pairVec u1 v1 i = true := by
  fin_cases k
  · exact ⟨0, 1, 1, 1, by decide⟩
  · exact ⟨1, 2, 3, 2, by decide⟩
  · exact ⟨2, 2, 3, 2, by decide⟩
  · exact ⟨3, 1, 1, 1, by decide⟩
  · exact ⟨1, 0, 1, 1, by decide⟩
  · exact ⟨3, 1, 3, 2, by decide⟩
  · exact ⟨1, 2, 1, 1, by decide⟩
  · exact ⟨1, 3, 1, 1, by decide⟩

lemma lower_bound : ¬ PEqualNP.Represents.RepSizeAtMost matA 6 := by
  rintro ⟨C, hmono, hsize, hrep⟩
  obtain ⟨S, hScard, hSval⟩ :=
    core 8 C.gates (fun g hg => (hmono g hg).2) {C.output}
  have hSlt : S.card ≤ 7 := by
    simp only [Finset.card_singleton] at hScard
    have hs : C.gates.length ≤ 6 := hsize
    omega
  have hex : ∃ k : Fin 8, k ∉ S := by
    by_contra hall
    have hall' : ∀ k : Fin 8, k ∈ S := fun k => by
      by_contra hnk
      exact hall ⟨k, hnk⟩
    have huniv : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall'
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hSlt
    omega
  obtain ⟨k, hk⟩ := hex
  obtain ⟨u0, v0, u1, v1, hA0, hA1, hle⟩ := witness_for_missing k
  let x0 : Fin 8 → Bool := pairVec u0 v0
  let y : Fin 8 → Bool := pairVec u1 v1
  let z : Fin 8 → Bool := fun i => x0 i && y i
  have hzx0 : ∀ i ∈ S, z i = x0 i := by
    intro i hi
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    by_cases hx : x0 i = true
    · have hy : y i = true := hle i hik hx
      simp [z, hx, hy]
    · have hxf : x0 i = false := Bool.eq_false_iff.mpr hx
      simp [z, hxf]
  have hevalz : C.eval (List.ofFn z) = true := by
    have hzx := hSval z x0 hzx0 C.output (Finset.mem_singleton_self C.output)
    have hfx0 : C.eval (List.ofFn x0) = true := by
      change C.eval (List.ofFn (pairVec u0 v0)) = true
      rw [list_ofFn_pairVec, hrep u0 v0]
      exact hA0
    exact hzx.trans hfx0
  have hzy : ∀ i : Fin 8, z i = true → y i = true := by
    intro i hi
    simp [z] at hi
    exact hi.2
  have hevaly : C.eval (List.ofFn y) = true :=
    eval_mono C hmono 8 z y hzy hevalz
  have hfy : C.eval (List.ofFn y) = false := by
    change C.eval (List.ofFn (pairVec u1 v1)) = false
    rw [list_ofFn_pairVec, hrep u1 v1]
    exact hA1
  rw [hfy] at hevaly
  cases hevaly

end PEqualNP.Outside.L_meta_5900

theorem PEqualNP.Outside.L_meta_5900 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (15839 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (15839 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  exact ⟨PEqualNP.Outside.L_meta_5900.upper_bound, PEqualNP.Outside.L_meta_5900.lower_bound⟩
