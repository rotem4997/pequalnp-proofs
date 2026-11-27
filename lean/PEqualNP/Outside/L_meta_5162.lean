import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5162

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.CircuitMoves
  PEqualNP.HeptadCover

-- Section 1: PG(2, 3) incidence graph and quadrangle extension

def pgAdj (u v : Fin 26) : Bool :=
  if h1 : u.val < 13 ∧ 13 ≤ v.val then
    decide (⟨u.val, h1.1⟩ ∈ singerLines3 ⟨v.val - 13, by omega⟩)
  else if h2 : v.val < 13 ∧ 13 ≤ u.val then
    decide (⟨v.val, h2.1⟩ ∈ singerLines3 ⟨u.val - 13, by omega⟩)
  else false

def nbrs (u : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter fun v => pgAdj u v = true

def pgEdges : Finset (Fin 26 × Fin 26) :=
  Finset.univ.filter fun p => p.1.val < 13 ∧ pgAdj p.1 p.2 = true

lemma pgAdj_symm : ∀ u v : Fin 26, pgAdj u v = pgAdj v u := by decide

lemma pgAdj_irrefl : ∀ u : Fin 26, pgAdj u u = false := by decide

lemma pgAdj_bip : ∀ u v : Fin 26, pgAdj u v = true → (u.val < 13) ≠ (v.val < 13) := by decide

lemma nbrs_card : ∀ u : Fin 26, (nbrs u).card = 4 := by decide

lemma pg_no_c4 : ∀ u v : Fin 26, u ≠ v → (nbrs u ∩ nbrs v).card ≤ 1 := by decide

lemma pgEdges_card : pgEdges.card = 52 := by
  have heq : pgEdges = (Finset.univ.filter fun u : Fin 26 => u.val < 13).biUnion
      fun u => (nbrs u).image fun v => (u, v) := by
    ext ⟨u, v⟩
    simp only [pgEdges, nbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨hu, hadj⟩
      exact ⟨u, hu, v, hadj, rfl, rfl⟩
    · rintro ⟨u', hu', v', hadj, rfl, rfl⟩
      exact ⟨hu', hadj⟩
  rw [heq, Finset.card_biUnion]
  · calc ∑ u ∈ Finset.univ.filter (fun u : Fin 26 => u.val < 13), ((nbrs u).image fun v => (u, v)).card
        = ∑ u ∈ Finset.univ.filter (fun u : Fin 26 => u.val < 13), (nbrs u).card := by
          refine Finset.sum_congr rfl fun u _ => Finset.card_image_of_injective _ fun a b h => congrArg Prod.snd h
      _ = ∑ _u ∈ Finset.univ.filter (fun u : Fin 26 => u.val < 13), 4 :=
          Finset.sum_congr rfl fun u _ => nbrs_card u
      _ = (Finset.univ.filter fun u : Fin 26 => u.val < 13).card * 4 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 52 := by
          have h13 : (Finset.univ.filter fun u : Fin 26 => u.val < 13).card = 13 := by decide
          rw [h13]
  · intro u1 _ u2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p h1 h2
    obtain ⟨v1, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨v2, _, heqp⟩ := Finset.mem_image.mp h2
    exact hne (congrArg Prod.fst heqp).symm

lemma mem_nbrs_iff (u v : Fin 26) : v ∈ nbrs u ↔ pgAdj u v = true := by
  simp [nbrs]

lemma mem_pgEdges_iff (p : Fin 26 × Fin 26) :
    p ∈ pgEdges ↔ p.1.val < 13 ∧ pgAdj p.1 p.2 = true := by
  simp [pgEdges]

def qPPList : List (List (Fin 13)) :=
  [[0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 5], [0, 2, 3, 4], [0, 1, 4, 6],
   [0, 1, 2, 5], [0, 1, 2, 6], [0, 1, 2, 7], [0, 1, 4, 8], [0, 2, 4, 9],
   [0, 1, 5, 10], [0, 1, 2, 11], [0, 1, 4, 12]]

def qLLList : List (List (Fin 13)) :=
  [[2, 4, 5, 6], [5, 6, 7, 11], [4, 6, 7, 8], [2, 5, 7, 8], [2, 6, 8, 10],
   [2, 4, 7, 11], [4, 5, 8, 10], [2, 4, 5, 6], [2, 5, 6, 10], [2, 4, 6, 8],
   [2, 4, 5, 8], [2, 4, 5, 6], [4, 5, 6, 10]]

def qPLList : List (List (Fin 13)) :=
  [[0, 1, 2, 5], [0, 1, 2, 5], [2, 4, 5, 6], [0, 1, 2, 5], [2, 4, 5, 6],
   [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 7, 8], [2, 4, 5, 8], [0, 1, 2, 5],
   [2, 5, 6, 10], [2, 4, 6, 11], [2, 4, 5, 12]]

def qPP (d : Fin 13) : Finset (Fin 13) := (qPPList.getD d.val []).toFinset
def qLL (d : Fin 13) : Finset (Fin 13) := (qLLList.getD d.val []).toFinset
def qPL (d : Fin 13) : Finset (Fin 13) := (qPLList.getD d.val []).toFinset

lemma qPP_ok : ∀ d : Fin 13, IsQuadrangle singerLines3 (qPP d) ∧ (0 : Fin 13) ∈ qPP d ∧ d ∈ qPP d := by
  decide

lemma qLL_ok : ∀ d : Fin 13, IsQuadrangle singerLines3 (qLL d) ∧
    (0 : Fin 13) ∈ missLines singerLines3 (qLL d) ∧ d ∈ missLines singerLines3 (qLL d) := by
  decide

lemma qPL_ok : ∀ d : Fin 13, d ∉ singerLines3 0 →
    IsQuadrangle singerLines3 (qPL d) ∧ d ∈ qPL d ∧ (0 : Fin 13) ∈ missLines singerLines3 (qPL d) := by
  decide

lemma singerLines3_shift (k l p : Fin 13) :
    p + k ∈ singerLines3 (l + k) ↔ p ∈ singerLines3 l := by
  simp only [singerLines3, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmod : ((p + k).val + 13 - (l + k).val) % 13 = (p.val + 13 - l.val) % 13 := by
    simp only [Fin.val_add]
    omega
  rw [hmod]

lemma isQuad_shift (k : Fin 13) (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
    IsQuadrangle singerLines3 (Q.image (· + k)) := by
  have hinj : Function.Injective (fun x : Fin 13 => x + k) := fun a b h => by
    simpa using congrArg (· - k) h
  refine ⟨by rw [Finset.card_image_of_injective Q hinj]; exact hQ.1, fun l => ?_⟩
  have hsub : (Q.image (· + k) ∩ singerLines3 l) = (Q ∩ singerLines3 (l - k)).image (· + k) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxl⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      have h1 := singerLines3_shift k (l - k) y
      have h2 : l - k + k = l := sub_add_cancel l k
      rw [h2] at h1
      exact h1.mp hxl
    · rintro ⟨y, ⟨hy, hyl⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      have h1 := singerLines3_shift k (l - k) y
      have h2 : l - k + k = l := sub_add_cancel l k
      rw [h2] at h1
      exact h1.mpr hyl
  rw [hsub, Finset.card_image_of_injective _ hinj]
  exact hQ.2 (l - k)

lemma mem_missLines_shift (k : Fin 13) (Q : Finset (Fin 13)) (l : Fin 13) :
    l + k ∈ missLines singerLines3 (Q.image (· + k)) ↔ l ∈ missLines singerLines3 Q := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  constructor
  · intro h p hp hQ
    exact h ((singerLines3_shift k l p).mpr hp) (Finset.mem_image.mpr ⟨p, hQ, rfl⟩)
  · intro h q hq hQ
    obtain ⟨p, hpQ, rfl⟩ := Finset.mem_image.mp hQ
    exact h ((singerLines3_shift k l p).mp hq) hpQ

def heptFn (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  fun w => if h : w.val < 13 then decide (⟨w.val, h⟩ ∈ Q)
    else decide (⟨w.val - 13, by omega⟩ ∈ missLines singerLines3 Q)

lemma ofFn_heptFn (Q : Finset (Fin 13)) :
    List.ofFn (heptFn Q) =
      (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, heptFn]
    by_cases hi : i < 13
    · rw [List.getElem_append_left (by simp [hi]), List.getElem_ofFn]
      simp [hi]
    · have hlen : (List.ofFn fun p : Fin 13 => decide (p ∈ Q)).length = 13 := List.length_ofFn
      rw [List.getElem_append_right (by omega), List.getElem_ofFn]
      simp [hi]

lemma ofFn_pair_pt_ln (p l : Fin 13) :
    List.ofFn (pairInput (⟨p.val, by omega⟩ : Fin 26) (⟨13 + l.val, by omega⟩ : Fin 26)) =
      (List.ofFn fun x : Fin 13 => decide (x = p)) ++
      (List.ofFn fun x : Fin 13 => decide (x = l)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, pairInput]
    by_cases hi : i < 13
    · rw [List.getElem_append_left (by simp [hi]), List.getElem_ofFn]
      simp only [Fin.ext_iff]
      have : i ≠ 13 + l.val := by omega
      simp [this]
    · have hlen : (List.ofFn fun x : Fin 13 => decide (x = p)).length = 13 := List.length_ofFn
      rw [List.getElem_append_right (by omega), List.getElem_ofFn]
      simp only [Fin.ext_iff, List.length_ofFn]
      have : i ≠ p.val := by omega
      simp only [this, false_or, decide_eq_decide]
      omega

lemma nonAdj_le_quad (u v : Fin 26) (h : pgAdj u v = false) :
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      ∀ w : Fin 26, pairInput u v w = true → heptFn Q w = true := by
  have step : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      heptFn Q u = true → heptFn Q v = true →
      ∃ Q' : Finset (Fin 13), IsQuadrangle singerLines3 Q' ∧
        ∀ w : Fin 26, pairInput u v w = true → heptFn Q' w = true := by
    intro Q hQ hu hv
    refine ⟨Q, hQ, fun w hw => ?_⟩
    simp only [pairInput, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl <;> assumption
  by_cases hu : u.val < 13 <;> by_cases hv : v.val < 13
  · set p1 : Fin 13 := ⟨u.val, hu⟩
    set p2 : Fin 13 := ⟨v.val, hv⟩
    have hok := qPP_ok (p2 - p1)
    apply step ((qPP (p2 - p1)).image (· + p1)) (isQuad_shift p1 _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨0, hok.2.1, zero_add p1⟩
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨p2 - p1, hok.2.2, sub_add_cancel p2 p1⟩
  · set p : Fin 13 := ⟨u.val, hu⟩
    set l : Fin 13 := ⟨v.val - 13, by omega⟩
    have hnot : p ∉ singerLines3 l := by
      unfold pgAdj at h
      have hv' : 13 ≤ v.val := by omega
      simp only [hu, hv', and_self, ↓reduceDIte, decide_eq_false_iff_not] at h
      exact h
    have hnot0 : p - l ∉ singerLines3 0 := by
      intro hmem
      have h1 := (singerLines3_shift l 0 (p - l)).mpr hmem
      rw [sub_add_cancel, zero_add] at h1
      exact hnot h1
    have hok := qPL_ok (p - l) hnot0
    apply step ((qPL (p - l)).image (· + l)) (isQuad_shift l _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨p - l, hok.2.1, sub_add_cancel p l⟩
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l (qPL (p - l)) 0).mpr hok.2.2
      rwa [zero_add] at h1
  · set l : Fin 13 := ⟨u.val - 13, by omega⟩
    set p : Fin 13 := ⟨v.val, hv⟩
    have hnot : p ∉ singerLines3 l := by
      unfold pgAdj at h
      have hu' : 13 ≤ u.val := by omega
      have h1 : ¬ (u.val < 13 ∧ 13 ≤ v.val) := by omega
      simp only [h1, ↓reduceDIte, hv, hu', and_self, decide_eq_false_iff_not] at h
      exact h
    have hnot0 : p - l ∉ singerLines3 0 := by
      intro hmem
      have h1 := (singerLines3_shift l 0 (p - l)).mpr hmem
      rw [sub_add_cancel, zero_add] at h1
      exact hnot h1
    have hok := qPL_ok (p - l) hnot0
    apply step ((qPL (p - l)).image (· + l)) (isQuad_shift l _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l (qPL (p - l)) 0).mpr hok.2.2
      rwa [zero_add] at h1
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨p - l, hok.2.1, sub_add_cancel p l⟩
  · set l1 : Fin 13 := ⟨u.val - 13, by omega⟩
    set l2 : Fin 13 := ⟨v.val - 13, by omega⟩
    have hok := qLL_ok (l2 - l1)
    apply step ((qLL (l2 - l1)).image (· + l1)) (isQuad_shift l1 _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l1 (qLL (l2 - l1)) 0).mpr hok.2.1
      rwa [zero_add] at h1
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l1 (qLL (l2 - l1)) (l2 - l1)).mpr hok.2.2
      rwa [sub_add_cancel l2 l1] at h1

-- Section 2: Basic circuit semantics, monotonicity, cones, orSets, orIn

def ValidCirc (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack 26 C ∧
  (∀ (p l : Fin 13), p ∈ singerLines3 l →
    C.eval ((List.ofFn fun x : Fin 13 => decide (x = p)) ++
            (List.ofFn fun x : Fin 13 => decide (x = l))) = true) ∧
  (∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
    C.eval ((List.ofFn fun x : Fin 13 => decide (x ∈ Q)) ++
            (List.ofFn fun x : Fin 13 => decide (x ∈ missLines singerLines3 Q))) = false)

def IsMin (C : Circuit) : Prop :=
  ValidCirc C ∧ ∀ C' : Circuit, ValidCirc C' → C.size ≤ C'.size

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepW x := rfl

lemma foldl_stepW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

lemma foldl_stepW_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepW_len, List.length_ofFn]

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt; exact List.getD_eq_getElem C.gates _ hj

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma wireVal_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal
  rw [wires_eq_foldl, foldl_stepW_getD_lt _ _ _ (by simp; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wireVal_ge {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  exact getD_ge_len _ _ (by rw [wires_len]; exact hw)

lemma wireVal_gate {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => if i < n + j then wireVal n C i x else false) := by
  unfold wireVal
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl stepW (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    rw [foldl_stepW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.wires (List.ofFn x) = (C.gates.drop (j + 1)).foldl stepW (stepW pre (gateAt C j)) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ i < n + j, (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < pre.length by omega)]
  have hnj : (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len])]
    simp [stepW, List.getD_eq_getElem?_getD, hpre_len]
  rw [hnj]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]; exact (hpre_get i hi).symm
  · simp only [hi, ↓reduceIte]; exact getD_ge_len pre i (by omega)

lemma wireVal_gate_rb {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  rw [wireVal_gate C j hj x]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [hRB j hj i hi]

lemma wireVal_mono_m2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    {x y : Fin n → Bool} (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ w : ℕ, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hlt : w < n
    · rw [wireVal_input C w hlt x] at hwx
      rw [wireVal_input C w hlt y]
      exact hxy ⟨w, hlt⟩ hwx
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wireVal_ge C w hge x] at hwx; cases hwx
      · have hj : w - n < C.gates.length := by omega
        have heq : w = n + (w - n) := by omega
        rw [heq] at hwx ⊢
        rw [wireVal_gate_rb hRB hj] at hwx ⊢
        have hop := (hM _ (gateAt_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hwx ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hwx ⊢
          intro u hu
          exact ih u (by have := hRB (w - n) hj u hu; omega) (hwx u hu)
        · rw [hop] at hwx ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwx ⊢
          obtain ⟨u, hu, hux⟩ := hwx
          exact ⟨u, hu, ih u (by have := hRB (w - n) hj u hu; omega) hux⟩

lemma valid_eval_pairInput_true {C : Circuit} (hV : ValidCirc C) {u v : Fin 26}
    (hadj : pgAdj u v = true) :
    wireVal 26 C C.output (pairInput u v) = true := by
  have h1 : ∀ p l : Fin 13, p ∈ singerLines3 l →
      wireVal 26 C C.output (pairInput ⟨p.val, by omega⟩ ⟨13 + l.val, by omega⟩) = true := by
    intro p l hpl
    unfold wireVal
    rw [ofFn_pair_pt_ln p l]
    exact hV.2.2.1 p l hpl
  unfold pgAdj at hadj
  by_cases h1c : u.val < 13 ∧ 13 ≤ v.val
  · rw [dif_pos h1c, decide_eq_true_eq] at hadj
    have hu : (⟨u.val, by omega⟩ : Fin 26) = u := by ext; rfl
    have hv : (⟨13 + (v.val - 13), by omega⟩ : Fin 26) = v := by ext; simp; omega
    have res := h1 ⟨u.val, h1c.1⟩ ⟨v.val - 13, by omega⟩ hadj
    rwa [hu, hv] at res
  · rw [dif_neg h1c] at hadj
    by_cases h2c : v.val < 13 ∧ 13 ≤ u.val
    · rw [dif_pos h2c, decide_eq_true_eq] at hadj
      have hv : (⟨v.val, by omega⟩ : Fin 26) = v := by ext; rfl
      have hu : (⟨13 + (u.val - 13), by omega⟩ : Fin 26) = u := by ext; simp; omega
      have res := h1 ⟨v.val, h2c.1⟩ ⟨u.val - 13, by omega⟩ hadj
      rw [hv, hu] at res
      have hpeq : pairInput v u = pairInput u v := by
        funext w; simp [pairInput, or_comm]
      rwa [hpeq] at res
    · rw [dif_neg h2c] at hadj; cases hadj

lemma valid_eval_pairInput_false {C : Circuit} (hV : ValidCirc C) {u v : Fin 26}
    (hnadj : pgAdj u v = false) :
    wireVal 26 C C.output (pairInput u v) = false := by
  obtain ⟨Q, hQ, hle⟩ := nonAdj_le_quad u v hnadj
  have hQf : wireVal 26 C C.output (heptFn Q) = false := by
    unfold wireVal
    rw [ofFn_heptFn Q]
    exact hV.2.2.2 Q hQ
  cases hval : wireVal 26 C C.output (pairInput u v)
  · rfl
  · exfalso
    have ht := wireVal_mono_m2 hV.1 hV.2.1 hle C.output hval
    rw [hQf] at ht
    cases ht

-- Section 3: Cones, orSets, OrReaches, orIn

lemma foldl_coneStep_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega

lemma foldl_coneStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : j < (coneStep n cs g).length := by simp [coneStep]; omega
    rw [ih (coneStep n cs g) hlt]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma cones_len (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_coneStep_len]; simp

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (coneStep n) []
  have hpre_len : pre.length = j := by
    rw [foldl_coneStep_len, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.gates.foldl (coneStep n) [] =
      (C.gates.drop (j + 1)).foldl (coneStep n) (coneStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ k < j, (C.gates.foldl (coneStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [heq, foldl_coneStep_getD_lt _ _ _ _ (by simp [coneStep, hpre_len]; omega)]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < pre.length by omega)]
  conv_lhs => rw [heq, foldl_coneStep_getD_lt _ _ _ _ (by simp [coneStep, hpre_len])]
  conv_lhs => simp only [coneStep, List.getD_eq_getElem?_getD, hpre_len]
  conv_lhs => rw [List.getElem?_append_right (by omega), hpre_len]
  conv_lhs => simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwn : w - n < j := by omega
  have hg := hpre_get (w - n) hwn
  simp only [List.getD_eq_getElem?_getD] at hg ⊢
  congr 1
  exact hg.symm

lemma inCone_gate_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD_eq n C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩
    exact ⟨w, hw, hnw, hwn, hmem⟩
  · rintro ⟨w, hw, hnw, hwn, hmem⟩
    exact ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩

lemma inCone_ge_false (n : ℕ) (C : Circuit) (i j : ℕ) (hj : C.gates.length ≤ j) :
    ¬ InCone n C i j := by
  unfold InCone
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_len]; exact hj)]
  simp

lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < C.gates.length
    · rw [inCone_gate_iff n C i j hj] at h
      obtain ⟨w, _, hnw, hwn, rfl | hc⟩ := h
      · omega
      · have := ih (w - n) (by omega) hc; omega
    · exact (inCone_ge_false n C i j (by omega) h).elim

lemma inCone_trans (n : ℕ) (C : Circuit) (a b c : ℕ)
    (hab : InCone n C a b) (hbc : InCone n C b c) : InCone n C a c := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    by_cases hc : c < C.gates.length
    · rw [inCone_gate_iff n C b c hc] at hbc
      obtain ⟨w, hw, hnw, hwc, rfl | hbw⟩ := hbc
      · rw [inCone_gate_iff n C a c hc]
        exact ⟨w, hw, hnw, hwc, Or.inr hab⟩
      · rw [inCone_gate_iff n C a c hc]
        exact ⟨w, hw, hnw, hwc, Or.inr (ih (w - n) (by omega) hbw)⟩
    · exact (inCone_ge_false n C b c (by omega) hbc).elim

lemma foldl_orStep_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [orStep]; omega

lemma foldl_orStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < cs.length) :
    (gs.foldl (orStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : j < (orStep n cs g).length := by simp [orStep]; omega
    rw [ih (orStep n cs g) hlt]
    simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orStep_len]; simp

lemma orSets_getD_eq_or (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold orSets
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (orStep n) []
  have hpre_len : pre.length = j := by
    rw [foldl_orStep_len, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.gates.foldl (orStep n) [] =
      (C.gates.drop (j + 1)).foldl (orStep n) (orStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ k < j, (C.gates.foldl (orStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [heq, foldl_orStep_getD_lt _ _ _ _ (by simp [orStep, hpre_len]; omega)]
    simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < pre.length by omega)]
  conv_lhs => rw [heq, foldl_orStep_getD_lt _ _ _ _ (by simp [orStep, hpre_len])]
  conv_lhs => simp only [orStep, List.getD_eq_getElem?_getD, hpre_len]
  conv_lhs => rw [List.getElem?_append_right (by omega), hpre_len]
  conv_lhs => simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hor, ↓reduceIte]
  congr 1
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hg := hpre_get (w - n) (by omega)
  simp only [List.getD_eq_getElem?_getD] at hg ⊢
  exact hg.symm

lemma orSets_getD_eq_ne_or (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hne : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold orSets
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (orStep n) []
  have hpre_len : pre.length = j := by
    rw [foldl_orStep_len, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.gates.foldl (orStep n) [] =
      (C.gates.drop (j + 1)).foldl (orStep n) (orStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  rw [heq, foldl_orStep_getD_lt _ _ _ _ (by simp [orStep, hpre_len])]
  simp only [orStep, List.getD_eq_getElem?_getD, hpre_len]
  rw [List.getElem?_append_right (by omega), hpre_len]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hne, ↓reduceIte]

lemma orReaches_self (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hor : (gateAt C j).op = GateOp.or
  · rw [orSets_getD_eq_or n C j hj hor]; exact List.mem_cons_self ..
  · rw [orSets_getD_eq_ne_or n C j hj hor]; exact List.mem_singleton_self j

lemma orReaches_gate_iff (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (g : ℕ) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ OrReaches n C w g) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold OrReaches
  simp only [Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
  by_cases hop : (gateAt C j).op = GateOp.or
  · rw [orSets_getD_eq_or n C j hj hop, List.mem_cons]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hop, w, hw, hwn, hnw, hmem⟩
    · rintro (rfl | ⟨_, w, hw, hwn, hnw, hmem⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩
  · rw [orSets_getD_eq_ne_or n C j hj hop, List.mem_singleton]
    constructor
    · intro h; exact Or.inl h
    · rintro (rfl | ⟨h, _⟩); rfl; exact (hop h).elim

lemma orReaches_ge_false (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w) (g : ℕ) :
    ¬ OrReaches n C w g := by
  intro ⟨hnw, hmem⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_len]; omega)] at hmem
  cases hmem

lemma orReaches_le_aux (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length)
    (h : OrReaches n C (n + j) g) : g ≤ j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff n C hj g] at h
    rcases h with rfl | ⟨_, u, _, huj, hu⟩
    · exact le_rfl
    · have hu1 := hu.1
      have hlt : u - n < j := by omega
      have h2 := ih (u - n) hlt (by omega) (by rwa [show n + (u - n) = u by omega])
      omega

lemma orReaches_le (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    g ≤ w - n ∧ g < C.gates.length := by
  have hnw := h.1
  by_cases hge : n + C.gates.length ≤ w
  · exact (orReaches_ge_false n C hge g h).elim
  · have hj : w - n < C.gates.length := by omega
    have h1 := orReaches_le_aux n C (w - n) g hj (by rwa [show n + (w - n) = w by omega])
    omega

lemma orReaches_imp_inCone_or_eq (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (g : ℕ)
    (h : OrReaches n C (n + j) g) : g = j ∨ InCone n C g j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff n C hj g] at h
    rcases h with rfl | ⟨_, u, hu, huj, hru⟩
    · exact Or.inl rfl
    · right
      have hun := hru.1
      have huk : u - n < j := by omega
      have h1 := ih (u - n) huk (by omega) (by rwa [show n + (u - n) = u by omega])
      rw [inCone_gate_iff n C g j hj]
      exact ⟨u, hu, hun, huj, h1⟩

lemma orReaches_trans_aux (n : ℕ) (C : Circuit) (k j g : ℕ) (hk : k < C.gates.length)
    (h1 : OrReaches n C (n + k) j) (h2 : OrReaches n C (n + j) g) : OrReaches n C (n + k) g := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff n C hk j] at h1
    rcases h1 with rfl | ⟨hor, u, hu, huk, hru⟩
    · exact h2
    · rw [orReaches_gate_iff n C hk g]
      right
      refine ⟨hor, u, hu, huk, ?_⟩
      have hun := hru.1
      have hres := ih (u - n) (by omega) (by omega) (by rwa [show n + (u - n) = u by omega])
      rwa [show n + (u - n) = u by omega] at hres

lemma orReaches_trans (n : ℕ) (C : Circuit) (w j g : ℕ)
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw := h1.1
  by_cases hge : n + C.gates.length ≤ w
  · exact (orReaches_ge_false n C hge j h1).elim
  · have hk : w - n < C.gates.length := by omega
    have hres := orReaches_trans_aux n C (w - n) j g hk (by rwa [show n + (w - n) = w by omega]) h2
    rwa [show n + (w - n) = w by omega] at hres

lemma wireVal_ge_of_orReaches_aux {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (k g : ℕ) (x : Fin n → Bool)
    (hk : k < C.gates.length) (hr : OrReaches n C (n + k) g) (hg : gateVal n C g x = true) :
    wireVal n C (n + k) x = true := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff n C hk g] at hr
    rcases hr with rfl | ⟨hor, u, hu, huk, hru⟩
    · exact hg
    · rw [wireVal_gate_rb hRB hk, hor]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      have hun := hru.1
      have hval := ih (u - n) (by omega) (by omega) (by rwa [show n + (u - n) = u by omega])
      rw [show n + (u - n) = u by omega] at hval
      exact ⟨u, hu, hval⟩

lemma wireVal_ge_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w g : ℕ) (x : Fin n → Bool)
    (hr : OrReaches n C w g) (hg : gateVal n C g x = true) : wireVal n C w x = true := by
  have hnw := hr.1
  by_cases hge : n + C.gates.length ≤ w
  · exact (orReaches_ge_false n C hge g hr).elim
  · have hk : w - n < C.gates.length := by omega
    have hres := wireVal_ge_of_orReaches_aux hRB (w - n) g x hk (by rwa [show n + (w - n) = w by omega]) hg
    rwa [show n + (w - n) = w by omega] at hres

lemma orIn_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) (v : Fin n) :
    v ∈ orIn n C w ↔ (v : ℕ) = w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨_, _, hr, _, _⟩)
    · exact h
    · have := hr.1; omega
  · exact Or.inl

lemma orIn_gate_and {n : ℕ} (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext v
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_or, not_exists, not_and]
  refine ⟨by omega, fun k _ hr hor _ => ?_⟩
  rw [orReaches_gate_iff n C hj k] at hr
  rcases hr with rfl | ⟨h, _⟩
  · rw [hand] at hor; cases hor
  · rw [hand] at h; cases h

lemma orIn_gate_or_rb {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (v : Fin n) :
    v ∈ orIn n C (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, v ∈ orIn n C w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hkor, hvk⟩)
    · omega
    · rw [orReaches_gate_iff n C hj k] at hr
      rcases hr with rfl | ⟨_, w, hw, _, hwk⟩
      · exact ⟨v.val, hvk, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr ⟨k, hk, hwk, hkor, hvk⟩⟩
  · rintro ⟨w, hw, heq | ⟨k, hk, hwk, hkor, hvk⟩⟩
    · right
      refine ⟨j, hj, orReaches_self n C hj, hor, ?_⟩
      rwa [heq]
    · right
      refine ⟨k, hk, ?_, hkor, hvk⟩
      rw [orReaches_gate_iff n C hj k]
      exact Or.inr ⟨hor, w, hw, hRB j hj w hw, hwk⟩

lemma orIn_mono_of_orReaches {n : ℕ} (C : Circuit) (w j : ℕ) (hr : OrReaches n C w j) :
    orIn n C (n + j) ⊆ orIn n C w := by
  intro v hv
  unfold orIn at hv ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with h | ⟨k, hk, hjk, hkor, hvk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans n C w j k hr hjk, hkor, hvk⟩

lemma wireVal_ge_of_orIn {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w : ℕ) (v : Fin n)
    (x : Fin n → Bool) (hv : v ∈ orIn n C w) (hx : x v = true) :
    wireVal n C w x = true := by
  unfold orIn at hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with heq | ⟨k, hk, hwk, hkor, hvk⟩
  · rw [← heq, wireVal_input C v.val v.isLt x]; exact hx
  · apply wireVal_ge_of_orReaches hRB w k x hwk
    change wireVal n C (n + k) x = true
    rw [wireVal_gate_rb hRB hk, hkor]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨v.val, hvk, by rw [wireVal_input C v.val v.isLt x]; exact hx⟩

lemma wireVal_eq_orIn_or_i {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    (i : ℕ) (w : ℕ) (hw : w < n + C.gates.length)
    (honly : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → OrReaches n C w a → a = i)
    (x : Fin n → Bool) :
    wireVal n C w x = true ↔
      (OrReaches n C w i ∧ gateVal n C i x = true) ∨ ∃ v ∈ orIn n C w, x v = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    constructor
    · intro hval
      by_cases hwn : w < n
      · right
        refine ⟨⟨w, hwn⟩, (orIn_input C hwn _).mpr rfl, ?_⟩
        rwa [wireVal_input C w hwn x] at hval
      · set k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk] at hval honly ⊢
        have hop := (hM _ (gateAt_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor
        · have hki : k = i := honly k hk hand (orReaches_self n C hk)
          subst hki
          exact Or.inl ⟨orReaches_self n C hk, hval⟩
        · rw [wireVal_gate_rb hRB hk, hor] at hval
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hval
          obtain ⟨u, hu, hux⟩ := hval
          have hult := hRB k hk u hu
          have honly_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → OrReaches n C u a → a = i := by
            intro a ha haand hru
            apply honly a ha haand
            rw [orReaches_gate_iff n C hk a]
            exact Or.inr ⟨hor, u, hu, hult, hru⟩
          have hres := (ih u (by omega) (by omega) honly_u).mp hux
          rcases hres with ⟨hrui, hi⟩ | ⟨v, hvu, hvx⟩
          · left
            refine ⟨?_, hi⟩
            rw [orReaches_gate_iff n C hk i]
            exact Or.inr ⟨hor, u, hu, hult, hrui⟩
          · right
            exact ⟨v, (orIn_gate_or_rb hRB hk hor v).mpr ⟨u, hu, hvu⟩, hvx⟩
    · rintro (⟨hri, hi⟩ | ⟨v, hv, hvx⟩)
      · exact wireVal_ge_of_orReaches hRB w i x hri hi
      · exact wireVal_ge_of_orIn hRB w v x hv hvx

-- Section 4: Circuit surgery and minimality consequences

lemma eraseGate_len (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  unfold eraseGate
  simp only [hm, ↓reduceIte, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma eraseGate_gateAt_lt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length) (hj : j < m) :
    gateAt (eraseGate n C m p) j = gateAt C j := by
  unfold gateAt eraseGate
  simp only [hm, ↓reduceIte, List.getD_eq_getElem?_getD]
  have htl : j < (C.gates.take m).length := by simp; omega
  rw [List.getElem?_append_left htl, List.getElem?_take_of_lt hj]

lemma eraseGate_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj1 : m ≤ j) (hj2 : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j =
      ⟨(gateAt C (j + 1)).op, (gateAt C (j + 1)).inputs.map (eraseRedirect n m p)⟩ := by
  unfold gateAt eraseGate
  simp only [hm, ↓reduceIte, List.getD_eq_getElem?_getD]
  have htl : (C.gates.take m).length = m := by simp; omega
  rw [List.getElem?_append_right (by omega), htl, List.getElem?_map, List.getElem?_drop]
  have heq : m + 1 + (j - m) = j + 1 := by omega
  rw [heq, List.getElem?_eq_getElem hj2]
  simp

lemma eraseGate_monotone2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) {m p : ℕ}
    (hm : m < C.gates.length) : Monotone2 (eraseGate n C m p) := by
  have hlen := eraseGate_len n C m p hm
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [← gateAt_eq hj]
  by_cases hjm : j < m
  · rw [eraseGate_gateAt_lt n C m p j hm hjm]
    exact hM _ (gateAt_mem (by omega))
  · rw [eraseGate_gateAt_ge n C m p j hm (by omega) (by omega)]
    have hm1 := hM _ (gateAt_mem (show j + 1 < C.gates.length by omega))
    exact ⟨hm1.1, by simp [hm1.2]⟩

lemma eraseGate_readsBack {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) : ReadsBack n (eraseGate n C m p) := by
  have hlen := eraseGate_len n C m p hm
  intro j hj i hi
  by_cases hjm : j < m
  · rw [eraseGate_gateAt_lt n C m p j hm hjm] at hi
    exact hRB j (by omega) i hi
  · rw [eraseGate_gateAt_ge n C m p j hm (by omega) (by omega)] at hi
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
    have hult := hRB (j + 1) (by omega) u hu
    unfold eraseRedirect
    split_ifs <;> omega

lemma eraseGate_wireVal_eq {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) (x : Fin n → Bool)
    (heq_mp : wireVal n C (n + m) x = wireVal n C p x) :
    ∀ w < n + C.gates.length,
      wireVal n (eraseGate n C m p) (eraseRedirect n m p w) x = wireVal n C w x := by
  have hRB' := eraseGate_readsBack hRB hm hp
  have hlen := eraseGate_len n C m p hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hred : eraseRedirect n m p w = w := by unfold eraseRedirect; split_ifs <;> omega
      rw [hred, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      by_cases hjm : j < m
      · have hred : eraseRedirect n m p w = n + j := by unfold eraseRedirect; split_ifs <;> omega
        rw [hred, hwj]
        have hj' : j < (eraseGate n C m p).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, eraseGate_gateAt_lt n C m p j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hured : eraseRedirect n m p u = u := by unfold eraseRedirect; split_ifs <;> omega
        have := ih u (by omega) (by omega)
        rwa [hured] at this
      · by_cases heqm : j = m
        · have hw_eq : w = n + m := by omega
          have hred : eraseRedirect n m p w = p := by unfold eraseRedirect; simp [hw_eq]
          rw [hred, hw_eq, heq_mp]
          have hpred : eraseRedirect n m p p = p := by unfold eraseRedirect; split_ifs <;> omega
          have := ih p (by omega) (by omega)
          rwa [hpred] at this
        · have hgt : m < j := by omega
          have hred : eraseRedirect n m p w = n + (j - 1) := by unfold eraseRedirect; split_ifs <;> omega
          rw [hred, hwj]
          have hj' : j - 1 < (eraseGate n C m p).gates.length := by omega
          rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
            eraseGate_gateAt_ge n C m p (j - 1) hm (by omega) (by omega)]
          have hj1 : j - 1 + 1 = j := by omega
          rw [hj1]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega)

lemma min_no_eq_wire {C : Circuit} (hMin : IsMin C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < 26 + m)
    (heq : ∀ x : Fin 26 → Bool, wireVal 26 C (26 + m) x = wireVal 26 C p x) : False := by
  have hV := hMin.1
  set C' := eraseGate 26 C m p
  have hlen : C'.gates.length = C.gates.length - 1 := eraseGate_len 26 C m p hm
  have hout_C' : C'.output = eraseRedirect 26 m p C.output := by
    simp only [C', eraseGate, hm, ↓reduceIte]
  have heval : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    change wireVal 26 C' C'.output x = wireVal 26 C C.output x
    rw [hout_C']
    by_cases hout : C.output < 26 + C.gates.length
    · exact eraseGate_wireVal_eq hV.2.1 hm hp x (heq x) C.output hout
    · have hout' : 26 + C'.gates.length ≤ eraseRedirect 26 m p C.output := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [wireVal_ge C' _ hout', wireVal_ge C _ (by omega)]
  have hV' : ValidCirc C' := by
    refine ⟨eraseGate_monotone2 hV.1 hm, eraseGate_readsBack hV.2.1 hm hp, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l, heval, ofFn_pair_pt_ln a l]
      exact hV.2.2.1 a l hal
    · intro Q hQ
      rw [← ofFn_heptFn Q, heval, ofFn_heptFn Q]
      exact hV.2.2.2 Q hQ
  have hle : C.gates.length ≤ C'.gates.length := hMin.2 C' hV'
  omega

-- Delete a gate `m` by substituting constant `b : Bool`
def shiftDown (n m w : ℕ) : ℕ :=
  if n + m < w then w - 1 else w

def substConstGate (n m : ℕ) (b : Bool) (g : Gate) : Gate :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  match b with
  | false =>
    if g.op = GateOp.or then
      ⟨GateOp.or, (g.inputs.filter (fun w => decide (w ≠ n + m))).map (shiftDown n m)⟩
    else if n + m ∈ g.inputs then
      ⟨GateOp.or, []⟩
    else
      ⟨g.op, g.inputs.map (shiftDown n m)⟩
  | true =>
    if g.op = GateOp.and then
      ⟨GateOp.and, (g.inputs.filter (fun w => decide (w ≠ n + m))).map (shiftDown n m)⟩
    else if n + m ∈ g.inputs then
      ⟨GateOp.and, []⟩
    else
      ⟨g.op, g.inputs.map (shiftDown n m)⟩

def deleteConstGate (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) : Circuit :=
  { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map (substConstGate n m b)
    output := shiftDown n m C.output }

lemma deleteConstGate_len (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) (hm : m < C.gates.length) :
    (deleteConstGate n C m b).gates.length = C.gates.length - 1 := by
  unfold deleteConstGate
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma deleteConstGate_gateAt_lt (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) (j : ℕ)
    (hm : m < C.gates.length) (hj : j < m) :
    gateAt (deleteConstGate n C m b) j = gateAt C j := by
  unfold gateAt deleteConstGate
  simp only [List.getD_eq_getElem?_getD]
  have htl : j < (C.gates.take m).length := by simp; omega
  rw [List.getElem?_append_left htl, List.getElem?_take_of_lt hj]

lemma deleteConstGate_gateAt_ge (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) (j : ℕ)
    (hm : m < C.gates.length) (hj1 : m ≤ j) (hj2 : j + 1 < C.gates.length) :
    gateAt (deleteConstGate n C m b) j = substConstGate n m b (gateAt C (j + 1)) := by
  unfold gateAt deleteConstGate
  simp only [List.getD_eq_getElem?_getD]
  have htl : (C.gates.take m).length = m := by simp; omega
  rw [List.getElem?_append_right (by omega), htl, List.getElem?_map, List.getElem?_drop]
  have heq : m + 1 + (j - m) = j + 1 := by omega
  rw [heq, List.getElem?_eq_getElem hj2]
  simp

lemma deleteConstGate_monotone2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) {m : ℕ} (b : Bool)
    (hm : m < C.gates.length) : Monotone2 (deleteConstGate n C m b) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hlen := deleteConstGate_len n C m b hm
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [← gateAt_eq hj]
  by_cases hjm : j < m
  · rw [deleteConstGate_gateAt_lt n C m b j hm hjm]
    exact hM _ (gateAt_mem (by omega))
  · rw [deleteConstGate_gateAt_ge n C m b j hm (by omega) (by omega)]
    have hm1 := hM _ (gateAt_mem (show j + 1 < C.gates.length by omega))
    unfold substConstGate
    cases b <;> dsimp only <;> split_ifs
    · refine ⟨by simp, ?_⟩
      simp only [List.length_map]
      exact (List.length_filter_le _ _).trans hm1.2
    · exact ⟨by simp, by simp⟩
    · exact ⟨hm1.1, by simp [hm1.2]⟩
    · refine ⟨by simp, ?_⟩
      simp only [List.length_map]
      exact (List.length_filter_le _ _).trans hm1.2
    · exact ⟨by simp, by simp⟩
    · exact ⟨hm1.1, by simp [hm1.2]⟩

lemma deleteConstGate_readsBack {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m : ℕ} (b : Bool)
    (hm : m < C.gates.length) : ReadsBack n (deleteConstGate n C m b) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hlen := deleteConstGate_len n C m b hm
  intro j hj i hi
  by_cases hjm : j < m
  · rw [deleteConstGate_gateAt_lt n C m b j hm hjm] at hi
    exact hRB j (by omega) i hi
  · rw [deleteConstGate_gateAt_ge n C m b j hm (by omega) (by omega)] at hi
    unfold substConstGate at hi
    cases b <;> dsimp only at hi <;> split_ifs at hi
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      simp only [List.mem_filter, decide_eq_true_eq] at hu
      have hult := hRB (j + 1) (by omega) u hu.1
      unfold shiftDown; split_ifs <;> omega
    · cases hi
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      have hult := hRB (j + 1) (by omega) u hu
      have hne : u ≠ n + m := fun h => by subst h; contradiction
      unfold shiftDown; split_ifs <;> omega
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      simp only [List.mem_filter, decide_eq_true_eq] at hu
      have hult := hRB (j + 1) (by omega) u hu.1
      unfold shiftDown; split_ifs <;> omega
    · cases hi
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      have hult := hRB (j + 1) (by omega) u hu
      have hne : u ≠ n + m := fun h => by subst h; contradiction
      unfold shiftDown; split_ifs <;> omega

lemma deleteConstGate_wireVal_eq {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    {m : ℕ} (b : Bool) (hm : m < C.gates.length) (x : Fin n → Bool)
    (hconst : wireVal n C (n + m) x = b) :
    ∀ w < n + C.gates.length, w ≠ n + m →
      wireVal n (deleteConstGate n C m b) (shiftDown n m w) x = wireVal n C w x := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hRB' := deleteConstGate_readsBack hRB b hm
  have hlen := deleteConstGate_len n C m b hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    by_cases hwn : w < n
    · have hs : shiftDown n m w = w := by unfold shiftDown; split_ifs <;> omega
      rw [hs, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      have hjm_ne : j ≠ m := by omega
      by_cases hjm : j < m
      · have hs : shiftDown n m w = n + j := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j < (deleteConstGate n C m b).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, deleteConstGate_gateAt_lt n C m b j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hus : shiftDown n m u = u := by unfold shiftDown; split_ifs <;> omega
        have := ih u (by omega) (by omega) (by omega)
        rwa [hus] at this
      · have hgt : m < j := by omega
        have hs : shiftDown n m w = n + (j - 1) := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j - 1 < (deleteConstGate n C m b).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
          deleteConstGate_gateAt_ge n C m b (j - 1) hm (by omega) (by omega)]
        have hj1 : j - 1 + 1 = j := by omega
        rw [hj1]
        have hop := (hM _ (gateAt_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        unfold substConstGate
        cases b
        · -- b = false
          dsimp only
          split_ifs with hor hmem
          · rw [hor]
            simp only [GateOp.eval, List.map_map, List.any_map, List.any_filter, Function.comp_apply, id_eq]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨u, hu, hune, hval⟩
              have hult := hRB j hj u hu
              rw [ih u (by omega) (by omega) hune] at hval
              exact ⟨u, hu, hval⟩
            · rintro ⟨u, hu, hval⟩
              have hult := hRB j hj u hu
              have hune : u ≠ n + m := by
                intro heq; subst heq; dsimp only [Function.comp_apply, id_eq] at hval; rw [hconst] at hval; cases hval
              exact ⟨u, hu, hune, by rwa [ih u (by omega) (by omega) hune]⟩
          · rcases hop with hand | hor'
            · rw [hand]
              simp only [GateOp.eval, List.map_nil, List.any_nil]
              symm
              rw [List.all_eq_false]
              exact ⟨false, List.mem_map.mpr ⟨n + m, hmem, hconst⟩, by simp⟩
            · exact (hor hor').elim
          · simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hRB j hj u hu
            have hune : u ≠ n + m := fun h => hmem (h ▸ hu)
            exact ih u (by omega) (by omega) hune
        · -- b = true
          dsimp only
          split_ifs with hand hmem
          · rw [hand]
            simp only [GateOp.eval, List.map_map, List.all_map, List.all_filter, Function.comp_apply, id_eq]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
              not_not]
            constructor
            · intro hall u hu
              have hult := hRB j hj u hu
              by_cases hune : u = n + m
              · subst hune; exact hconst
              · have h1 := hall u hu
                rcases h1 with heq | hval
                · exact (hune heq).elim
                · rwa [ih u (by omega) (by omega) hune] at hval
            · intro hall u hu
              by_cases hune : u = n + m
              · exact Or.inl hune
              · right
                have hult := hRB j hj u hu
                rw [ih u (by omega) (by omega) hune]
                exact hall u hu
          · rcases hop with hand' | hor
            · exact (hand hand').elim
            · rw [hor]
              simp only [GateOp.eval, List.map_nil, List.all_nil]
              symm
              rw [List.any_eq_true]
              exact ⟨true, List.mem_map.mpr ⟨n + m, hmem, hconst⟩, by simp⟩
          · simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hRB j hj u hu
            have hune : u ≠ n + m := fun h => hmem (h ▸ hu)
            exact ih u (by omega) (by omega) hune

lemma deleteConstGate_wireVal_not_inCone {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    {m : ℕ} (hm : m < C.gates.length) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, w ≠ n + m → (∀ j, w = n + j → ¬ InCone n C m j) →
      wireVal n (deleteConstGate n C m false) (shiftDown n m w) x = wireVal n C w x := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hRB' := deleteConstGate_readsBack hRB false hm
  have hlen := deleteConstGate_len n C m false hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne hnc
    by_cases hwn : w < n
    · have hs : shiftDown n m w = w := by unfold shiftDown; split_ifs <;> omega
      rw [hs, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      have hncj : ¬ InCone n C m j := hnc j hwj
      have hnotmem : n + m ∉ (gateAt C j).inputs := by
        intro hmem
        apply hncj
        rw [inCone_gate_iff n C m j hj]
        exact ⟨n + m, hmem, Nat.le_add_right n m, hRB j hj (n + m) hmem, Or.inl (by omega)⟩
      have hsub_nc : ∀ u ∈ (gateAt C j).inputs, u ≠ n + m ∧ ∀ k, u = n + k → ¬ InCone n C m k := by
        intro u hu
        refine ⟨fun h => hnotmem (h ▸ hu), fun k huk hmk => hncj ?_⟩
        rw [inCone_gate_iff n C m j hj]
        exact ⟨u, hu, by omega, hRB j hj u hu, Or.inr (by rwa [huk, Nat.add_sub_cancel_left])⟩
      by_cases hjm : j < m
      · have hs : shiftDown n m w = n + j := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j < (deleteConstGate n C m false).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, deleteConstGate_gateAt_lt n C m false j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hus : shiftDown n m u = u := by unfold shiftDown; split_ifs <;> omega
        have := ih u (by omega) (by omega) (hsub_nc u hu).1 (hsub_nc u hu).2
        rwa [hus] at this
      · have hgt : m < j := by omega
        have hs : shiftDown n m w = n + (j - 1) := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j - 1 < (deleteConstGate n C m false).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
          deleteConstGate_gateAt_ge n C m false (j - 1) hm (by omega) (by omega)]
        have hj1 : j - 1 + 1 = j := by omega
        rw [hj1]
        unfold substConstGate
        dsimp only
        split_ifs with hor
        · rw [hor]
          have hfilt : (gateAt C j).inputs.filter (fun u => decide (u ≠ n + m)) = (gateAt C j).inputs := by
            rw [List.filter_eq_self]
            intro u hu; simp [(hsub_nc u hu).1]
          rw [hfilt, List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega) (hsub_nc u hu).1 (hsub_nc u hu).2
        · simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega) (hsub_nc u hu).1 (hsub_nc u hu).2

lemma min_output_bounds {C : Circuit} (hV : ValidCirc C) :
    26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have hf := valid_eval_pairInput_false hV (pgAdj_irrefl ⟨C.output, hlt⟩)
    rw [wireVal_input C C.output hlt] at hf
    simp [pairInput] at hf
  · by_contra hge
    push_neg at hge
    have ht := valid_eval_pairInput_true hV (u := (0 : Fin 26)) (v := (13 : Fin 26)) (by decide)
    rw [wireVal_ge C C.output hge] at ht
    cases ht

lemma min_no_const_gate {C : Circuit} (hMin : IsMin C) {m : ℕ} (hm : m < C.gates.length) (b : Bool)
    (hconst : ∀ x : Fin 26 → Bool, wireVal 26 C (26 + m) x = b) : False := by
  have hV := hMin.1
  have hne_out : C.output ≠ 26 + m := by
    intro heq
    cases b
    · have ht := valid_eval_pairInput_true hV (u := (0 : Fin 26)) (v := (13 : Fin 26)) (by decide)
      rw [heq, hconst] at ht; cases ht
    · have hf := valid_eval_pairInput_false hV (pgAdj_irrefl (0 : Fin 26))
      rw [heq, hconst] at hf; cases hf
  have hout := min_output_bounds hV
  set C' := deleteConstGate 26 C m b
  have hlen : C'.gates.length = C.gates.length - 1 := deleteConstGate_len 26 C m b hm
  have heval : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    deleteConstGate_wireVal_eq hV.1 hV.2.1 b hm x (hconst x) C.output hout.2 hne_out
  have hV' : ValidCirc C' := by
    refine ⟨deleteConstGate_monotone2 hV.1 b hm, deleteConstGate_readsBack hV.2.1 b hm, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l, heval, ofFn_pair_pt_ln a l]; exact hV.2.2.1 a l hal
    · intro Q hQ
      rw [← ofFn_heptFn Q, heval, ofFn_heptFn Q]; exact hV.2.2.2 Q hQ
  have hle : C.gates.length ≤ C'.gates.length := hMin.2 C' hV'
  omega

lemma min_in_output_cone {C : Circuit} (hMin : IsMin C) {m : ℕ} (hm : m < C.gates.length) :
    m = C.output - 26 ∨ InCone 26 C m (C.output - 26) := by
  by_contra h
  push_neg at h
  have hV := hMin.1
  have hout := min_output_bounds hV
  have hne_out : C.output ≠ 26 + m := by omega
  set C' := deleteConstGate 26 C m false
  have hlen : C'.gates.length = C.gates.length - 1 := deleteConstGate_len 26 C m false hm
  have heval : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    apply deleteConstGate_wireVal_not_inCone hV.1 hV.2.1 hm x C.output hout.2 hne_out
    intro k hk
    have : k = C.output - 26 := by omega
    rw [this]; exact h.2
  have hV' : ValidCirc C' := by
    refine ⟨deleteConstGate_monotone2 hV.1 false hm, deleteConstGate_readsBack hV.2.1 false hm, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l, heval, ofFn_pair_pt_ln a l]; exact hV.2.2.1 a l hal
    · intro Q hQ
      rw [← ofFn_heptFn Q, heval, ofFn_heptFn Q]; exact hV.2.2.2 Q hQ
  have hle : C.gates.length ≤ C'.gates.length := hMin.2 C' hV'
  omega

lemma min_isAO2 {C : Circuit} (hMin : IsMin C) : IsAO2 26 C := by
  have hV := hMin.1
  refine ⟨?_, hV.2.1, ?_⟩
  · intro g hg
    have h := (hV.1 g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · intro g hg
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq hm]
    have hle := (hV.1 _ (gateAt_mem hm)).2
    have hop := (hV.1 _ (gateAt_mem hm)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    cases hl : (gateAt C m).inputs with
    | nil =>
      exfalso
      rcases hop with hand | hor
      · apply min_no_const_gate hMin hm true
        intro x; rw [wireVal_gate_rb hV.2.1 hm, hand, hl]; rfl
      · apply min_no_const_gate hMin hm false
        intro x; rw [wireVal_gate_rb hV.2.1 hm, hor, hl]; rfl
    | cons u rest =>
      cases rest with
      | nil =>
        exfalso
        have hult : u < 26 + m := hV.2.1 m hm u (by rw [hl]; simp)
        apply min_no_eq_wire hMin hm hult
        intro x
        rw [wireVal_gate_rb hV.2.1 hm, hl]
        rcases hop with hand | hor
        · simp [hand, GateOp.eval]
        · simp [hor, GateOp.eval]
      | cons v rest' =>
        cases rest' with
        | nil => rfl
        | cons _ _ => rw [hl] at hle; simp at hle

lemma min_opnd_ne {C : Circuit} (hMin : IsMin C) {m : ℕ} (hm : m < C.gates.length) :
    opnd C m 0 ≠ opnd C m 1 := by
  intro heq
  have hAO := min_isAO2 hMin
  have hlen : (gateAt C m).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hm)
  have hinp : (gateAt C m).inputs = [opnd C m 0, opnd C m 1] := by
    unfold opnd
    cases hl : (gateAt C m).inputs with
    | nil => simp [hl] at hlen
    | cons a l =>
      cases l with
      | nil => simp [hl] at hlen
      | cons b l' =>
        cases l' with
        | nil => simp
        | cons _ _ => simp [hl] at hlen
  have h0lt : opnd C m 0 < 26 + m := hMin.1.2.1 m hm (opnd C m 0) (by rw [hinp]; simp)
  apply min_no_eq_wire hMin hm h0lt
  intro x
  rw [wireVal_gate_rb hMin.1.2.1 hm, hinp, heq]
  rcases hAO.1 _ (gateAt_mem hm) with hand | hor
  · simp [hand, GateOp.eval]
  · simp [hor, GateOp.eval]

-- Section 5: IsAO2 helpers and andPairs = 1 structure

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp
      | cons _ _ => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]; fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wireVal_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate_rb hAO.2.1 hj, gate_inputs_eq hAO hj, hand]
  simp [GateOp.eval]

lemma wireVal_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate_rb hAO.2.1 hj, gate_inputs_eq hAO hj, hor]
  simp [GateOp.eval]

lemma orIn_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext v
  rw [orIn_gate_or_rb hAO.2.1 hj hor, gate_inputs_eq hAO hj]
  simp

lemma orReaches_gate_or_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) {g : ℕ} (hne : g ≠ j) :
    OrReaches n C (n + j) g ↔ OrReaches n C (opnd C j 0) g ∨ OrReaches n C (opnd C j 1) g := by
  rw [orReaches_gate_iff n C hj g, gate_inputs_eq hAO hj]
  have h0 := opnd_lt hAO hj 0
  have h1 := opnd_lt hAO hj 1
  simp [hne, hor, h0, h1]

lemma min_pure_or_card_ge_two {C : Circuit} (hMin : IsMin C) {h : ℕ} (hh : h < C.gates.length)
    (hor : (gateAt C h).op = GateOp.or)
    (hpure : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ OrReaches 26 C (26 + h) a) :
    2 ≤ (orIn 26 C (26 + h)).card := by
  have hval : ∀ x : Fin 26 → Bool, wireVal 26 C (26 + h) x = true ↔ ∃ v ∈ orIn 26 C (26 + h), x v = true := by
    intro x
    have h1 := wireVal_eq_orIn_or_i hMin.1.1 hMin.1.2.1 C.gates.length (26 + h) (by omega)
      (fun a ha haand hru => (hpure a ha haand hru).elim) x
    have h2 : ¬ OrReaches 26 C (26 + h) C.gates.length := fun hr => by
      have := (orReaches_le 26 C (26 + h) C.gates.length hr).2; omega
    simpa [h2] using h1
  by_contra hlt
  push_neg at hlt
  by_cases h0 : (orIn 26 C (26 + h)).card = 0
  · have hemp : orIn 26 C (26 + h) = ∅ := Finset.card_eq_zero.mp h0
    apply min_no_const_gate hMin hh false
    intro x
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨v, hv, _⟩ := (hval x).mp ht
    rw [hemp] at hv; exact Finset.notMem_empty v hv
  · have h1 : (orIn 26 C (26 + h)).card = 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    apply min_no_eq_wire hMin hh (p := v.val) (by omega)
    intro x
    rw [wireVal_input C v.val v.isLt x]
    apply Bool.eq_iff_iff.mpr
    rw [hval x, hv]
    simp

lemma exists_unique_andPair {C : Circuit} (h1 : andPairs 26 C = 1) :
    ∃ i j : ℕ, i < C.gates.length ∧ j < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j ∧
      ∀ a < C.gates.length, ∀ b < C.gates.length,
        (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
        InCone 26 C a b → a = i ∧ b = j := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold andPairs at h1
  obtain ⟨⟨i, j⟩, heq⟩ := Finset.card_eq_one.mp h1
  have hmem : (i, j) ∈ (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2) := by
    rw [heq]; exact Finset.mem_singleton_self _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  refine ⟨i, j, hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2.1, hmem.2.2.2, ?_⟩
  intro a ha b hb haand hband hab
  have hmem' : (a, b) ∈ (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨ha, hb⟩, haand, hband, hab⟩
  rw [heq, Finset.mem_singleton, Prod.mk.injEq] at hmem'
  exact hmem'

def A_gates (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.and

def O_out (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or ∧ OrReaches 26 C C.output g

def T_gates (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.and ∧ OrReaches 26 C C.output g

def O_N (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or ∧ ¬ OrReaches 26 C C.output g

def O_pure (C : Circuit) (i : ℕ) : Finset ℕ :=
  (O_N C).filter fun h => ¬ OrReaches 26 C (26 + h) i

lemma mem_A_gates {C : Circuit} {g : ℕ} :
    g ∈ A_gates C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.and := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold A_gates; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_O_out {C : Circuit} {g : ℕ} :
    g ∈ O_out C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ OrReaches 26 C C.output g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold O_out; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_T_gates {C : Circuit} {g : ℕ} :
    g ∈ T_gates C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ OrReaches 26 C C.output g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold T_gates; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_O_N {C : Circuit} {g : ℕ} :
    g ∈ O_N C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ ¬ OrReaches 26 C C.output g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold O_N; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_O_pure {C : Circuit} {i h : ℕ} :
    h ∈ O_pure C i ↔ h ∈ O_N C ∧ ¬ OrReaches 26 C (26 + h) i := by
  unfold O_pure; rw [Finset.mem_filter]

lemma size_eq_A_Oout_ON {C : Circuit} (hAO : IsAO2 26 C) :
    C.gates.length = (A_gates C).card + (O_out C).card + (O_N C).card := by
  have hd1 : Disjoint (A_gates C) (O_out C) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [mem_A_gates] at hg1; rw [mem_O_out] at hg2
    rw [hg1.2] at hg2; cases hg2.2.1
  have hd2 : Disjoint (A_gates C ∪ O_out C) (O_N C) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [mem_O_N] at hg2
    rcases Finset.mem_union.mp hg1 with ha | ho
    · rw [mem_A_gates] at ha; rw [ha.2] at hg2; cases hg2.2.1
    · rw [mem_O_out] at ho; exact hg2.2.2 ho.2.2
  have hunion : A_gates C ∪ O_out C ∪ O_N C = Finset.range C.gates.length := by
    ext g
    simp only [Finset.mem_union, mem_A_gates, mem_O_out, mem_O_N, Finset.mem_range]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hg
      rcases hAO.1 _ (gateAt_mem hg) with hand | hor
      · exact Or.inl (Or.inl ⟨hg, hand⟩)
      · by_cases hr : OrReaches 26 C C.output g
        · exact Or.inl (Or.inr ⟨hg, hor, hr⟩)
        · exact Or.inr ⟨hg, hor, hr⟩
  have hc := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_range] at hc
  exact hc.symm

lemma inCone_to_orReaches {C : Circuit} (hAO : IsAO2 26 C) (a g : ℕ) (hg : g < C.gates.length)
    (hic : InCone 26 C a g)
    (hnoand : ∀ b < C.gates.length, (gateAt C b).op = GateOp.and → InCone 26 C a b →
      b ≠ g ∧ ¬ InCone 26 C b g) :
    OrReaches 26 C (26 + g) a := by
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    have hgor : (gateAt C g).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hg) with hand | hor
      · exact ((hnoand g hg hand hic).1 rfl).elim
      · exact hor
    rw [inCone_gate_iff 26 C a g hg] at hic
    obtain ⟨w, hw, h26w, hwg, rfl | hick⟩ := hic
    · rw [orReaches_gate_iff 26 C hg (w - 26)]
      right
      refine ⟨hgor, w, hw, hwg, ?_⟩
      have hself := orReaches_self 26 C (show w - 26 < C.gates.length by omega)
      rwa [show 26 + (w - 26) = w by omega] at hself
    · set k := w - 26
      have hk : k < C.gates.length := by omega
      have hnoand_k : ∀ b < C.gates.length, (gateAt C b).op = GateOp.and → InCone 26 C a b →
          b ≠ k ∧ ¬ InCone 26 C b k := by
        intro b hb hband hab
        have hbg := hnoand b hb hband hab
        have hkg : InCone 26 C k g := by
          rw [inCone_gate_iff 26 C k g hg]
          exact ⟨w, hw, h26w, hwg, Or.inl rfl⟩
        refine ⟨fun heq => hbg.2 (heq ▸ hkg), fun hbk => hbg.2 (inCone_trans 26 C b k g hbk hkg)⟩
      have hrk := ih k (by omega) hk hick hnoand_k
      rw [orReaches_gate_iff 26 C hg a]
      right
      exact ⟨hgor, w, hw, hwg, by rwa [show 26 + k = w by omega] at hrk⟩

lemma and_ne_i_in_T {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a ∈ A_gates C) (hnei : a ≠ i) : a ∈ T_gates C := by
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  rw [mem_A_gates] at ha
  rw [mem_T_gates]
  refine ⟨ha.1, ha.2, ?_⟩
  have hcone := min_in_output_cone hMin ha.1
  set out := C.output - 26
  have hout_eq : C.output = 26 + out := by omega
  have hout_lt : out < C.gates.length := by omega
  rw [hout_eq]
  rcases hcone with rfl | hic
  · exact orReaches_self 26 C ha.1
  · apply inCone_to_orReaches hAO a out hout_lt hic
    intro b hb hband hab
    exact (hnei (huniq a ha.1 b hb ha.2 hband hab).1).elim

lemma oOut_reads_ge_26 {C : Circuit} (hMin : IsMin C) {h : ℕ} (hh : h ∈ O_out C)
    {w : ℕ} (hw : w ∈ (gateAt C h).inputs) : 26 ≤ w := by
  by_contra hlt
  push_neg at hlt
  rw [mem_O_out] at hh
  have hf := valid_eval_pairInput_false hMin.1 (pgAdj_irrefl ⟨w, hlt⟩)
  have hht : gateVal 26 C h (pairInput ⟨w, hlt⟩ ⟨w, hlt⟩) = true := by
    change wireVal 26 C (26 + h) (pairInput ⟨w, hlt⟩ ⟨w, hlt⟩) = true
    rw [wireVal_gate_rb hMin.1.2.1 hh.1, hh.2.1]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨w, hw, by rw [wireVal_input C w hlt]; simp [pairInput]⟩
  have hout_t := wireVal_ge_of_orReaches hMin.1.2.1 C.output h _ hh.2.2 hht
  rw [hf] at hout_t
  cases hout_t

-- Corollary 1: No gate in O_out lies in cone(j)
lemma oOut_not_inCone_j {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hj : j < C.gates.length) (hjand : (gateAt C j).op = GateOp.and)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {h : ℕ} (hh : h ∈ O_out C) : ¬ InCone 26 C h j := by
  intro hic
  have hAO := min_isAO2 hMin
  set S := (O_out C).filter fun g => g = h ∨ InCone 26 C g h
  have hS_ne : S.Nonempty := ⟨h, Finset.mem_filter.mpr ⟨hh, Or.inl rfl⟩⟩
  set h0 := S.min' hS_ne
  have hh0_mem : h0 ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨hh0_out, hh0_rel⟩ := Finset.mem_filter.mp hh0_mem
  have hh0_info := mem_O_out.mp hh0_out
  have h0_ic_j : InCone 26 C h0 j := by
    rcases hh0_rel with heq | h0h
    · rw [heq]; exact hic
    · exact inCone_trans 26 C h0 h j h0h hic
  have hop_and : ∀ b : Fin 2, ∃ a < C.gates.length, opnd C h0 b = 26 + a ∧ (gateAt C a).op = GateOp.and := by
    intro b
    have hmem := opnd_mem hAO hh0_info.1 b
    have hge := oOut_reads_ge_26 hMin hh0_out hmem
    have hlt := opnd_lt hAO hh0_info.1 b
    set a := opnd C h0 b - 26
    have ha_lt : a < C.gates.length := by dsimp only [a]; omega
    have ha_eq : opnd C h0 b = 26 + a := by dsimp only [a]; omega
    refine ⟨a, ha_lt, ha_eq, ?_⟩
    rcases hAO.1 _ (gateAt_mem ha_lt) with hand | hor
    · exact hand
    · exfalso
      have ha_out : a ∈ O_out C := by
        rw [mem_O_out]
        refine ⟨ha_lt, hor, orReaches_trans 26 C C.output h0 a hh0_info.2.2 ?_⟩
        rw [orReaches_gate_iff 26 C hh0_info.1 a]
        right
        exact ⟨hh0_info.2.1, opnd C h0 b, hmem, hlt, by rw [ha_eq]; exact orReaches_self 26 C ha_lt⟩
      have ha_ic_h0 : InCone 26 C a h0 := by
        rw [inCone_gate_iff 26 C a h0 hh0_info.1]
        exact ⟨opnd C h0 b, hmem, hge, hlt, Or.inl rfl⟩
      have ha_S : a ∈ S := Finset.mem_filter.mpr ⟨ha_out, Or.inr (by
        rcases hh0_rel with heq | h0h
        · rwa [← heq]
        · exact inCone_trans 26 C a h0 h ha_ic_h0 h0h)⟩
      have hle : h0 ≤ a := Finset.min'_le S a ha_S
      dsimp only [a] at hle
      omega
  obtain ⟨a0, ha0_lt, ha0_eq, ha0_and⟩ := hop_and 0
  obtain ⟨a1, ha1_lt, ha1_eq, ha1_and⟩ := hop_and 1
  have ha0_ic_h0 : InCone 26 C a0 h0 := by
    rw [inCone_gate_iff 26 C a0 h0 hh0_info.1]
    exact ⟨opnd C h0 0, opnd_mem hAO hh0_info.1 0, by omega, opnd_lt hAO hh0_info.1 0, Or.inl (by omega)⟩
  have ha1_ic_h0 : InCone 26 C a1 h0 := by
    rw [inCone_gate_iff 26 C a1 h0 hh0_info.1]
    exact ⟨opnd C h0 1, opnd_mem hAO hh0_info.1 1, by omega, opnd_lt hAO hh0_info.1 1, Or.inl (by omega)⟩
  have heq0 := (huniq a0 ha0_lt j hj ha0_and hjand (inCone_trans 26 C a0 h0 j ha0_ic_h0 h0_ic_j)).1
  have heq1 := (huniq a1 ha1_lt j hj ha1_and hjand (inCone_trans 26 C a1 h0 j ha1_ic_h0 h0_ic_j)).1
  have hne := min_opnd_ne hMin hh0_info.1
  rw [ha0_eq, ha1_eq, heq0, heq1] at hne
  exact hne rfl

-- Corollary 2: ¬ OrReaches 26 C C.output i
def killWireInGate (w : ℕ) (g : Gate) : Gate :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  if g.op = GateOp.or then
    ⟨GateOp.or, g.inputs.filter (fun u => decide (u ≠ w))⟩
  else if w ∈ g.inputs then
    ⟨GateOp.or, []⟩
  else g

def killIInSet (C : Circuit) (i : ℕ) (S : Finset ℕ) : Circuit :=
  { gates := (List.range C.gates.length).map fun k =>
      if k ∈ S then killWireInGate (26 + i) (gateAt C k) else gateAt C k
    output := C.output }

lemma killIInSet_len (C : Circuit) (i : ℕ) (S : Finset ℕ) :
    (killIInSet C i S).gates.length = C.gates.length := by
  simp [killIInSet]

lemma killIInSet_gateAt (C : Circuit) (i : ℕ) (S : Finset ℕ) {k : ℕ} (hk : k < C.gates.length) :
    gateAt (killIInSet C i S) k =
      if k ∈ S then killWireInGate (26 + i) (gateAt C k) else gateAt C k := by
  conv_lhs => unfold gateAt killIInSet
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp [List.getElem_map, List.getElem_range]

lemma killIInSet_monotone2 {C : Circuit} (hM : Monotone2 C) (i : ℕ) (S : Finset ℕ) :
    Monotone2 (killIInSet C i S) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  have hk' : k < C.gates.length := by simpa [killIInSet_len] using hk
  rw [← gateAt_eq hk, killIInSet_gateAt C i S hk']
  have hm := hM _ (gateAt_mem hk')
  split_ifs with hmem
  · unfold killWireInGate
    split_ifs
    · exact ⟨by simp, (List.length_filter_le _ _).trans hm.2⟩
    · exact ⟨by simp, by simp⟩
    · exact hm
  · exact hm

lemma killIInSet_readsBack {C : Circuit} (hRB : ReadsBack 26 C) (i : ℕ) (S : Finset ℕ) :
    ReadsBack 26 (killIInSet C i S) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro k hk u hu
  have hk' : k < C.gates.length := by simpa [killIInSet_len] using hk
  rw [killIInSet_gateAt C i S hk'] at hu
  split_ifs at hu with hmem
  · unfold killWireInGate at hu
    split_ifs at hu
    · exact hRB k hk' u (List.mem_filter.mp hu).1
    · cases hu
    · exact hRB k hk' u hu
  · exact hRB k hk' u hu

lemma not_orToOutput_i {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hic_ij : InCone 26 C i j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    ¬ OrReaches 26 C C.output i := by
  intro hri_out
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  set M := (O_N C).filter fun h => OrReaches 26 C (26 + h) i ∧ InCone 26 C h j
  set S := insert j M
  set C1 := killIInSet C i S
  have hS_gt_i : ∀ k ∈ S, i < k := by
    intro k hk
    rcases Finset.mem_insert.mp hk with heq | hkM
    · rw [heq]; exact inCone_lt 26 C i j hic_ij
    · obtain ⟨hkN, hkri, _⟩ := Finset.mem_filter.mp hkM
      have hle := (orReaches_le 26 C (26 + k) i hkri).1
      have hne : i ≠ k := by
        intro heq; subst heq; rw [(mem_O_N.mp hkN).2.1] at hiand; cases hiand
      omega
  have hS_disj_Oout : ∀ k ∈ O_out C, k ∉ S := by
    intro k hk hkS
    rcases Finset.mem_insert.mp hkS with rfl | hkM
    · rw [(mem_O_out.mp hk).2.1] at hjand; cases hjand
    · exact (mem_O_N.mp (Finset.mem_filter.mp hkM).1).2.2 (mem_O_out.mp hk).2.2
  have hRB1 := killIInSet_readsBack hMin.1.2.1 i S
  have hlen1 := killIInSet_len C i S
  have heval1 : ∀ x : Fin 26 → Bool, wireVal 26 C1 C.output x = wireVal 26 C C.output x := by
    intro x
    cases hix : gateVal 26 C i x
    · -- Case gateVal C i x = false: every wire has identical value in C1 and C!
      suffices hall : ∀ w < 26 + C.gates.length, wireVal 26 C1 w x = wireVal 26 C w x from
        hall C.output hout.2
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hwn : w < 26
        · rw [wireVal_input _ w hwn, wireVal_input _ w hwn]
        · set k := w - 26
          have hk : k < C.gates.length := by omega
          have hwk : w = 26 + k := by omega
          rw [hwk, wireVal_gate_rb hRB1 (by omega), wireVal_gate_rb hMin.1.2.1 hk,
            killIInSet_gateAt C i S hk]
          split_ifs with hkS
          · unfold killWireInGate
            split_ifs with hkor hmem
            · rw [hkor]
              simp only [GateOp.eval, List.any_map, List.any_filter, Function.comp_apply, id_eq]
              apply Bool.eq_iff_iff.mpr
              simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
              constructor
              · rintro ⟨u, hu, _, huv⟩
                have hult := hMin.1.2.1 k hk u hu
                rw [ih u (by omega) (by omega)] at huv
                exact ⟨u, hu, huv⟩
              · rintro ⟨u, hu, huv⟩
                have hult := hMin.1.2.1 k hk u hu
                have hune : u ≠ 26 + i := by
                  intro heq; subst heq; change gateVal 26 C i x = true at huv
                  rw [hix] at huv; cases huv
                exact ⟨u, hu, hune, by rwa [ih u (by omega) (by omega)]⟩
            · rcases hAO.1 _ (gateAt_mem hk) with hkand | hkor'
              · rw [hkand]
                simp only [GateOp.eval, List.map_nil, List.any_nil]
                symm
                rw [List.all_eq_false]
                exact ⟨false, List.mem_map.mpr ⟨26 + i, hmem, hix⟩, by simp⟩
              · exact (hkor hkor').elim
            · congr 1
              apply List.map_congr_left
              intro u hu
              have hult := hMin.1.2.1 k hk u hu
              exact ih u (by omega) (by omega)
          · congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hMin.1.2.1 k hk u hu
            exact ih u (by omega) (by omega)
    · -- Case gateVal C i x = true: i is true in C1, and every k ∈ O_out ∪ {i} reaching i is true in C1!
      have hle_i : ∀ w ≤ 26 + i, wireVal 26 C1 w x = wireVal 26 C w x := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hwn : w < 26
          · rw [wireVal_input _ w hwn, wireVal_input _ w hwn]
          · set k := w - 26
            have hk : k < C.gates.length := by omega
            have hwk : w = 26 + k := by omega
            have hk_notS : k ∉ S := fun hkS => by have := hS_gt_i k hkS; omega
            rw [hwk, wireVal_gate_rb hRB1 (by omega), wireVal_gate_rb hMin.1.2.1 hk,
              killIInSet_gateAt C i S hk]
            simp only [hk_notS, ↓reduceIte]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hMin.1.2.1 k hk u hu
            exact ih u (by omega) (by omega)
      have hi_t1 : wireVal 26 C1 (26 + i) x = true := by
        rw [hle_i (26 + i) le_rfl]; exact hix
      have hout_t_C : wireVal 26 C C.output x = true :=
        wireVal_ge_of_orReaches hMin.1.2.1 C.output i x hri_out hix
      rw [hout_t_C]
      suffices hreach_t1 : ∀ k < C.gates.length, (k = i ∨ k ∈ O_out C) →
          OrReaches 26 C (26 + k) i → wireVal 26 C1 (26 + k) x = true by
        set out := C.output - 26
        have hout_eq : C.output = 26 + out := by omega
        rw [hout_eq] at hri_out ⊢
        apply hreach_t1 out (by omega) ?_ hri_out
        rcases hAO.1 _ (gateAt_mem (show out < C.gates.length by omega)) with hand | hor
        · left
          rw [orReaches_gate_iff 26 C (show out < C.gates.length by omega) i] at hri_out
          rcases hri_out with heq | ⟨hor', _⟩
          · exact heq.symm
          · rw [hand] at hor'; cases hor'
        · right
          exact mem_O_out.mpr ⟨by omega, hor, by rw [hout_eq]; exact orReaches_self 26 C (by omega)⟩
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hki hkri
        rcases hki with rfl | hkout
        · exact hi_t1
        · have hk_notS := hS_disj_Oout k hkout
          have hk_info := mem_O_out.mp hkout
          rw [orReaches_gate_iff 26 C hk i] at hkri
          rcases hkri with heq | ⟨_, u, hu, huk, huri⟩
          · subst heq; exact hi_t1
          · have h26u : 26 ≤ u := huri.1
            set k' := u - 26
            have hk'_lt : k' < k := by omega
            have hu_eq : u = 26 + k' := by omega
            have hk'_ki : k' = i ∨ k' ∈ O_out C := by
              rcases hAO.1 _ (gateAt_mem (show k' < C.gates.length by omega)) with hand | hor
              · left
                rw [hu_eq, orReaches_gate_iff 26 C (show k' < C.gates.length by omega) i] at huri
                rcases huri with heq | ⟨hor', _⟩
                · exact heq.symm
                · rw [hand] at hor'; cases hor'
              · right
                refine mem_O_out.mpr ⟨by omega, hor, orReaches_trans 26 C C.output k k' hk_info.2.2 ?_⟩
                rw [orReaches_gate_iff 26 C hk k']
                right
                exact ⟨hk_info.2.1, u, hu, huk, by rw [hu_eq]; exact orReaches_self 26 C (by omega)⟩
            have ht' := ih k' hk'_lt (by omega) hk'_ki (by rwa [← hu_eq])
            rw [wireVal_gate_rb hRB1 (by omega), killIInSet_gateAt C i S hk]
            simp only [hk_notS, ↓reduceIte, hk_info.2.1, GateOp.eval, List.any_map, List.any_eq_true,
              Function.comp_apply, id_eq]
            exact ⟨u, hu, by rwa [hu_eq]⟩
  -- C1 is a valid minimal circuit of the same size as C!
  have hV1 : ValidCirc C1 := by
    refine ⟨killIInSet_monotone2 hMin.1.1 i S, hRB1, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l]
      change wireVal 26 C1 C.output _ = true
      rw [heval1]
      change C.eval _ = true
      rw [ofFn_pair_pt_ln a l]
      exact hMin.1.2.2.1 a l hal
    · intro Q hQ
      rw [← ofFn_heptFn Q]
      change wireVal 26 C1 C.output _ = false
      rw [heval1]
      change C.eval _ = false
      rw [ofFn_heptFn Q]
      exact hMin.1.2.2.2 Q hQ
  have hMin1 : IsMin C1 := ⟨hV1, fun C' hC' => by
    change C1.gates.length ≤ C'.size
    rw [hlen1]
    exact hMin.2 C' hC'⟩
  have hAO1 := min_isAO2 hMin1
  -- Yet C1 has a gate in S of fan-in ≤ 1!
  have hsmall : ∃ g < C.gates.length, (gateAt C1 g).inputs.length ≤ 1 := by
    by_cases hM : M.Nonempty
    · set h0 := M.min' hM
      have hh0_M : h0 ∈ M := Finset.min'_mem M hM
      obtain ⟨hh0_N, hh0_ri, hh0_ic⟩ := Finset.mem_filter.mp hh0_M
      have hh0_info := mem_O_N.mp hh0_N
      have hreads_i : 26 + i ∈ (gateAt C h0).inputs := by
        rw [orReaches_gate_iff 26 C hh0_info.1 i] at hh0_ri
        rcases hh0_ri with heq | ⟨_, u, hu, huk, huri⟩
        · rw [heq] at hiand; rw [hh0_info.2.1] at hiand; cases hiand
        · by_cases hui : u = 26 + i
          · rwa [← hui]
          · exfalso
            have h26u := huri.1
            set k := u - 26
            have hk_lt : k < h0 := by omega
            have hu_eq : u = 26 + k := by omega
            have hk_ic_h0 : InCone 26 C k h0 := by
              rw [inCone_gate_iff 26 C k h0 hh0_info.1]
              exact ⟨u, hu, h26u, huk, Or.inl rfl⟩
            have hk_ic_j : InCone 26 C k j := inCone_trans 26 C k h0 j hk_ic_h0 hh0_ic
            rcases hAO.1 _ (gateAt_mem (show k < C.gates.length by omega)) with hand | hor
            · rw [hu_eq, orReaches_gate_iff 26 C (show k < C.gates.length by omega) i] at huri
              rcases huri with heq | ⟨hor', _⟩
              · exact hui (by omega)
              · rw [hand] at hor'; cases hor'
            · have hk_not_out : ¬ OrReaches 26 C C.output k := fun hko =>
                oOut_not_inCone_j hMin hj hjand huniq (mem_O_out.mpr ⟨by omega, hor, hko⟩) hk_ic_j
              have hk_M : k ∈ M := Finset.mem_filter.mpr
                ⟨mem_O_N.mpr ⟨by omega, hor, hk_not_out⟩, by rwa [← hu_eq], hk_ic_j⟩
              have hle := Finset.min'_le M k hk_M
              omega
      refine ⟨h0, hh0_info.1, ?_⟩
      rw [killIInSet_gateAt C i S hh0_info.1]
      have hh0_S : h0 ∈ S := Finset.mem_insert_of_mem hh0_M
      simp only [hh0_S, ↓reduceIte, killWireInGate, hh0_info.2.1, ↓reduceIte]
      have hlen2 : (gateAt C h0).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hh0_info.1)
      have hlt : ((gateAt C h0).inputs.filter (fun u => decide (u ≠ 26 + i))).length <
          (gateAt C h0).inputs.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨26 + i, hreads_i, by simp⟩
      omega
    · -- M is empty, so j directly reads 26 + i!
      have hM_emp : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
      have hj_reads_i : 26 + i ∈ (gateAt C j).inputs := by
        rw [inCone_gate_iff 26 C i j hj] at hic_ij
        obtain ⟨w, hw, h26w, hwj, hiw | hick⟩ := hic_ij
        · rwa [show 26 + i = w by omega]
        · exfalso
          set k := w - 26
          have hk_lt : k < j := by omega
          have hk_ic_j : InCone 26 C k j := by
            rw [inCone_gate_iff 26 C k j hj]
            exact ⟨w, hw, h26w, hwj, Or.inl rfl⟩
          have hk_or : (gateAt C k).op = GateOp.or := by
            rcases hAO.1 _ (gateAt_mem (show k < C.gates.length by omega)) with hand | hor
            · have := (huniq k (by omega) j hj hand hjand hk_ic_j).1
              have := inCone_lt 26 C i k hick
              omega
            · exact hor
          have hk_ri : OrReaches 26 C (26 + k) i := by
            apply inCone_to_orReaches hAO i k (by omega) hick
            intro b hb hband hib
            have heq := (huniq i hi b hb hiand hband hib).2
            rw [heq]
            refine ⟨by omega, fun hjk => ?_⟩
            have := inCone_lt 26 C j k hjk
            omega
          have hk_not_out : ¬ OrReaches 26 C C.output k := fun hko =>
            oOut_not_inCone_j hMin hj hjand huniq (mem_O_out.mpr ⟨by omega, hk_or, hko⟩) hk_ic_j
          have hk_M : k ∈ M := Finset.mem_filter.mpr
            ⟨mem_O_N.mpr ⟨by omega, hk_or, hk_not_out⟩, hk_ri, hk_ic_j⟩
          rw [hM_emp] at hk_M
          exact Finset.notMem_empty k hk_M
      refine ⟨j, hj, ?_⟩
      rw [killIInSet_gateAt C i S hj]
      have hjS : j ∈ S := Finset.mem_insert_self j M
      simp only [hjS, ↓reduceIte, killWireInGate, hjand, reduceCtorEq, hj_reads_i,
        List.length_nil, Nat.zero_le]
  obtain ⟨g, hg, hle1⟩ := hsmall
  have heq2 : (gateAt C1 g).inputs.length = 2 := hAO1.2.2 _ (gateAt_mem (by rw [hlen1]; exact hg))
  omega

lemma oPure_no_and {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {h : ℕ} (hh : h ∈ O_pure C i) :
    ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ OrReaches 26 C (26 + h) a := by
  intro a ha haand hha
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  obtain ⟨hhN, hnotri⟩ := mem_O_pure.mp hh
  have hh_info := mem_O_N.mp hhN
  have hah_ic : InCone 26 C a h := by
    rcases orReaches_imp_inCone_or_eq 26 C hh_info.1 a hha with rfl | hic
    · rw [hh_info.2.1] at haand; cases haand
    · exact hic
  -- Since h ∉ O_out, h must lie in the cone of some AND gate b
  set out := C.output - 26
  have hout_eq : C.output = 26 + out := by omega
  have hout_lt : out < C.gates.length := by omega
  have hh_ne_out : h ≠ out := by
    intro heq; apply hh_info.2.2; rw [hout_eq, ← heq]; exact orReaches_self 26 C hh_info.1
  have hh_ic_out : InCone 26 C h out := (min_in_output_cone hMin hh_info.1).resolve_left hh_ne_out
  have hex_b : ∃ b < C.gates.length, (gateAt C b).op = GateOp.and ∧ InCone 26 C h b := by
    by_contra hno
    push_neg at hno
    apply hh_info.2.2
    rw [hout_eq]
    apply inCone_to_orReaches hAO h out hout_lt hh_ic_out
    intro b hb hband hhb
    exact (hno b hb hband hhb).elim
  obtain ⟨b, hb, hband, hhb⟩ := hex_b
  have hab : InCone 26 C a b := inCone_trans 26 C a h b hah_ic hhb
  have hai := (huniq a ha b hb haand hband hab).1
  subst hai
  exact hnotri hha

-- Section 6: Abstract spanning-component bound and OR-gate partition

def EdgeReach {α : Type*} (E : List (α × α)) : α → α → Prop :=
  Relation.ReflTransGen fun u v => (u, v) ∈ E ∨ (v, u) ∈ E

lemma edgeReach_symm {α : Type*} {E : List (α × α)} {u v : α} (h : EdgeReach E u v) :
    EdgeReach E v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head
      (by rcases hstep with h1 | h2 <;> [exact Or.inr h1; exact Or.inl h2]) ih

lemma graph_spanning_bound {α : Type*} [DecidableEq α] (E : List (α × α)) :
    ∀ (L R : Finset α), (∀ u ∈ L, ∃ r ∈ R, EdgeReach E u r) →
      L.card ≤ E.length + R.card := by
  classical
  induction E with
  | nil =>
    intro L R hcov
    have hsub : L ⊆ R := by
      intro u hu
      obtain ⟨r, hr, hreach⟩ := hcov u hu
      cases hreach with
      | refl => exact hr
      | tail _ hstep => simp at hstep
    have := Finset.card_le_card hsub
    simp; omega
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    intro L R hcov
    have hsplit_path : ∀ u r, EdgeReach ((a, b) :: rest) u r →
        EdgeReach rest u r ∨
        (EdgeReach rest u a ∧ (EdgeReach rest a r ∨ EdgeReach rest b r)) ∨
        (EdgeReach rest u b ∧ (EdgeReach rest a r ∨ EdgeReach rest b r)) := by
      intro u r hreach
      induction hreach with
      | refl => exact Or.inl Relation.ReflTransGen.refl
      | @tail x y _ hstep ih' =>
        simp only [List.mem_cons] at hstep
        rcases hstep with (heq | hmem) | (heq | hmem)
        · have hxa : x = a := congrArg Prod.fst heq
          have hyb : y = b := congrArg Prod.snd heq
          subst hxa; subst hyb
          rcases ih' with hr | ⟨hu1, _⟩ | ⟨hu2, _⟩
          · exact Or.inr (Or.inl ⟨hr, Or.inr Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inr Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inr Relation.ReflTransGen.refl⟩)
        · rcases ih' with hr | ⟨hu1, ha | hb⟩ | ⟨hu2, ha | hb⟩
          · exact Or.inl (Relation.ReflTransGen.tail hr (Or.inl hmem))
          · exact Or.inr (Or.inl ⟨hu1, Or.inl (Relation.ReflTransGen.tail ha (Or.inl hmem))⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inr (Relation.ReflTransGen.tail hb (Or.inl hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inl (Relation.ReflTransGen.tail ha (Or.inl hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inr (Relation.ReflTransGen.tail hb (Or.inl hmem))⟩)
        · have hya : y = a := congrArg Prod.fst heq
          have hxb : x = b := congrArg Prod.snd heq
          subst hya; subst hxb
          rcases ih' with hr | ⟨hu1, _⟩ | ⟨hu2, _⟩
          · exact Or.inr (Or.inr ⟨hr, Or.inl Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inl Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inl Relation.ReflTransGen.refl⟩)
        · rcases ih' with hr | ⟨hu1, ha | hb⟩ | ⟨hu2, ha | hb⟩
          · exact Or.inl (Relation.ReflTransGen.tail hr (Or.inr hmem))
          · exact Or.inr (Or.inl ⟨hu1, Or.inl (Relation.ReflTransGen.tail ha (Or.inr hmem))⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inr (Relation.ReflTransGen.tail hb (Or.inr hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inl (Relation.ReflTransGen.tail ha (Or.inr hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inr (Relation.ReflTransGen.tail hb (Or.inr hmem))⟩)
    by_cases haR : ∃ r ∈ R, EdgeReach rest a r
    · obtain ⟨ra, hra, hrea⟩ := haR
      have hcov' : ∀ u ∈ L, ∃ r ∈ insert b R, EdgeReach rest u r := by
        intro u hu
        obtain ⟨r, hr, hreach⟩ := hcov u hu
        rcases hsplit_path u r hreach with hr' | ⟨hua, _⟩ | ⟨hub, _⟩
        · exact ⟨r, Finset.mem_insert_of_mem hr, hr'⟩
        · exact ⟨ra, Finset.mem_insert_of_mem hra, hua.trans hrea⟩
        · exact ⟨b, Finset.mem_insert_self b R, hub⟩
      have := ih L (insert b R) hcov'
      have hcard := Finset.card_insert_le b R
      simp only [List.length_cons]; omega
    · by_cases hbR : ∃ r ∈ R, EdgeReach rest b r
      · obtain ⟨rb, hrb, hreb⟩ := hbR
        have hcov' : ∀ u ∈ L, ∃ r ∈ insert a R, EdgeReach rest u r := by
          intro u hu
          obtain ⟨r, hr, hreach⟩ := hcov u hu
          rcases hsplit_path u r hreach with hr' | ⟨hua, _⟩ | ⟨hub, _⟩
          · exact ⟨r, Finset.mem_insert_of_mem hr, hr'⟩
          · exact ⟨a, Finset.mem_insert_self a R, hua⟩
          · exact ⟨rb, Finset.mem_insert_of_mem hrb, hub.trans hreb⟩
        have := ih L (insert a R) hcov'
        have hcard := Finset.card_insert_le a R
        simp only [List.length_cons]; omega
      · have hcov' : ∀ u ∈ L, ∃ r ∈ R, EdgeReach rest u r := by
          intro u hu
          obtain ⟨r, hr, hreach⟩ := hcov u hu
          rcases hsplit_path u r hreach with hr' | ⟨_, ha' | hb'⟩ | ⟨_, ha' | hb'⟩
          · exact ⟨r, hr, hr'⟩
          · exact (haR ⟨r, hr, ha'⟩).elim
          · exact (hbR ⟨r, hr, hb'⟩).elim
          · exact (haR ⟨r, hr, ha'⟩).elim
          · exact (hbR ⟨r, hr, hb'⟩).elim
        have := ih L R hcov'
        simp only [List.length_cons]; omega

lemma dag_conn {α : Type*} [DecidableEq α] {C : Circuit} (hAO : IsAO2 26 C)
    (f : ℕ → Finset α)
    (hf_in : ∀ w < 26, (f w).card ≤ 1)
    (hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (f (26 + g)).card ≤ 1)
    (hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
      f (26 + g) = f (opnd C g 0) ∪ f (opnd C g 1))
    (S : Finset ℕ) (L : Finset α) (W : Finset ℕ)
    (hW_lt : ∀ w ∈ W, w < 26 + C.gates.length)
    (hS_cov : ∀ w ∈ W, ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or →
      2 ≤ (f (26 + h) ∩ L).card →
      (f (opnd C h 0) ∩ L).Nonempty → (f (opnd C h 1) ∩ L).Nonempty → h ∈ S) :
    ∃ E : List (α × α), E.length ≤ S.card ∧
      ∀ w ∈ W, ∀ u ∈ f w ∩ L, ∀ v ∈ f w ∩ L, EdgeReach E u v := by
  classical
  let mkEdge : ℕ → Option (α × α) := fun h =>
    if hh : (f (opnd C h 0) ∩ L).Nonempty ∧ (f (opnd C h 1) ∩ L).Nonempty then
      some (hh.1.choose, hh.2.choose)
    else none
  let E : List (α × α) := S.toList.filterMap mkEdge
  refine ⟨E, (List.length_filterMap_le _ _).trans (Finset.length_toList S).le, ?_⟩
  have hconn : ∀ x < 26 + C.gates.length,
      (∃ w ∈ W, x = w ∨ (26 ≤ x ∧ OrReaches 26 C w (x - 26))) →
      ∀ u ∈ f x ∩ L, ∀ v ∈ f x ∩ L, EdgeReach E u v := by
    intro x
    induction x using Nat.strong_induction_on with
    | ind x ih =>
      intro hx hreach_w u hu v hv
      by_cases huv : u = v
      · rw [huv]; exact Relation.ReflTransGen.refl
      · by_cases hxn : x < 26
        · have hle1 := (Finset.card_le_card (Finset.inter_subset_left (s₂ := L))).trans (hf_in x hxn)
          have hgt1 := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
          omega
        · set h := x - 26
          have hxh : x = 26 + h := by omega
          have hh_lt : h < C.gates.length := by omega
          rw [hxh] at hu hv
          rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
          · have hle1 := (Finset.card_le_card (Finset.inter_subset_left (s₂ := L))).trans (hf_and h hh_lt hand)
            have hgt1 := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
            omega
          · have hwh : ∃ w ∈ W, OrReaches 26 C w h := by
              obtain ⟨w, hw, hw_eq | ⟨_, hwr⟩⟩ := hreach_w
              · exact ⟨w, hw, hw_eq ▸ hxh ▸ orReaches_self 26 C hh_lt⟩
              · exact ⟨w, hw, hwr⟩
            obtain ⟨w, hw, hwr⟩ := hwh
            have hsub_conn : ∀ b : Fin 2, ∀ a1 ∈ f (opnd C h b) ∩ L,
                ∀ a2 ∈ f (opnd C h b) ∩ L, EdgeReach E a1 a2 := by
              intro b a1 ha1 a2 ha2
              have hblt := opnd_lt hAO hh_lt b
              by_cases hbn : opnd C h b < 26
              · by_cases heq : a1 = a2
                · rw [heq]; exact Relation.ReflTransGen.refl
                · have hle1 := (Finset.card_le_card (Finset.inter_subset_left (s₂ := L))).trans (hf_in _ hbn)
                  have hgt1 := Finset.one_lt_card.mpr ⟨a1, ha1, a2, ha2, heq⟩
                  omega
              · apply ih (opnd C h b) (by omega) (by omega)
                · refine ⟨w, hw, Or.inr ⟨by omega, orReaches_trans 26 C w h (opnd C h b - 26) hwr ?_⟩⟩
                  rw [orReaches_gate_iff 26 C hh_lt]
                  right
                  refine ⟨hor, opnd C h b, opnd_mem hAO hh_lt b, hblt, ?_⟩
                  have hself := orReaches_self 26 C (show opnd C h b - 26 < C.gates.length by omega)
                  rwa [show 26 + (opnd C h b - 26) = opnd C h b by omega] at hself
                · exact ha1
                · exact ha2
            have hcard2 : 2 ≤ (f (26 + h) ∩ L).card :=
              Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
            rw [hf_or h hh_lt hor, Finset.union_inter_distrib_right] at hu hv
            rcases Finset.mem_union.mp hu with hu0 | hu1 <;> rcases Finset.mem_union.mp hv with hv0 | hv1
            · exact hsub_conn 0 u hu0 v hv0
            · have hne0 : (f (opnd C h 0) ∩ L).Nonempty := ⟨u, hu0⟩
              have hne1 : (f (opnd C h 1) ∩ L).Nonempty := ⟨v, hv1⟩
              have hhS : h ∈ S := hS_cov w hw h hwr hor hcard2 hne0 hne1
              have hh_mem : (hne0.choose, hne1.choose) ∈ E := by
                simp only [E, List.mem_filterMap]
                refine ⟨h, Finset.mem_toList.mpr hhS, ?_⟩
                simp only [mkEdge, hne0, hne1, and_self, ↓reduceDIte]
              have hr1 := hsub_conn 0 u hu0 _ hne0.choose_spec
              have hr2 : EdgeReach E hne0.choose hne1.choose :=
                Relation.ReflTransGen.single (Or.inl hh_mem)
              have hr3 := hsub_conn 1 _ hne1.choose_spec v hv1
              exact (hr1.trans hr2).trans hr3
            · have hne0 : (f (opnd C h 0) ∩ L).Nonempty := ⟨v, hv0⟩
              have hne1 : (f (opnd C h 1) ∩ L).Nonempty := ⟨u, hu1⟩
              have hhS : h ∈ S := hS_cov w hw h hwr hor hcard2 hne0 hne1
              have hh_mem : (hne0.choose, hne1.choose) ∈ E := by
                simp only [E, List.mem_filterMap]
                refine ⟨h, Finset.mem_toList.mpr hhS, ?_⟩
                simp only [mkEdge, hne0, hne1, and_self, ↓reduceDIte]
              have hr1 := hsub_conn 1 u hu1 _ hne1.choose_spec
              have hr2 : EdgeReach E hne1.choose hne0.choose :=
                Relation.ReflTransGen.single (Or.inr hh_mem)
              have hr3 := hsub_conn 0 _ hne0.choose_spec v hv0
              exact (hr1.trans hr2).trans hr3
            · exact hsub_conn 1 u hu1 v hv1
  intro w hw u hu v hv
  exact hconn w (hW_lt w hw) ⟨w, hw, Or.inl rfl⟩ u hu v hv

lemma oOut_card_bound {C : Circuit} (hMin : IsMin C) :
    (T_gates C).card ≤ (O_out C).card + 1 := by
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  by_cases hTe : (T_gates C).Nonempty
  · let f : ℕ → Finset ℕ := fun w => (T_gates C).filter fun a => OrReaches 26 C w a
    have hf_in : ∀ w < 26, (f w).card ≤ 1 := by
      intro w hw
      have hemp : f w = ∅ := by
        ext a; simp only [f, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hr; have := hr.1; omega
      rw [hemp]; simp
    have hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (f (26 + g)).card ≤ 1 := by
      intro g hg hand
      have hsub : f (26 + g) ⊆ {g} := by
        intro a ha
        simp only [f, Finset.mem_filter, Finset.mem_singleton] at ha ⊢
        rw [orReaches_gate_iff 26 C hg a] at ha
        rcases ha.2 with rfl | ⟨hor, _⟩
        · rfl
        · rw [hand] at hor; cases hor
      exact (Finset.card_le_card hsub).trans (by simp)
    have hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
        f (26 + g) = f (opnd C g 0) ∪ f (opnd C g 1) := by
      intro g hg hor
      ext a
      simp only [f, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ⟨haT, hrg⟩
        have hne : a ≠ g := by
          intro heq; subst heq; rw [(mem_T_gates.mp haT).2.1] at hor; cases hor
        rw [orReaches_gate_or_iff hAO hg hor hne] at hrg
        rcases hrg with h0 | h1
        · exact Or.inl ⟨haT, h0⟩
        · exact Or.inr ⟨haT, h1⟩
      · rintro (⟨haT, h0⟩ | ⟨haT, h1⟩)
        · have hne : a ≠ g := by
            intro heq; subst heq; rw [(mem_T_gates.mp haT).2.1] at hor; cases hor
          exact ⟨haT, (orReaches_gate_or_iff hAO hg hor hne).mpr (Or.inl h0)⟩
        · have hne : a ≠ g := by
            intro heq; subst heq; rw [(mem_T_gates.mp haT).2.1] at hor; cases hor
          exact ⟨haT, (orReaches_gate_or_iff hAO hg hor hne).mpr (Or.inr h1)⟩
    obtain ⟨E, hElen, hconn⟩ := dag_conn hAO f hf_in hf_and hf_or (O_out C) (T_gates C) {C.output}
      (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hout.2)
      (fun w hw h hwr hor _ _ _ => by
        rw [Finset.mem_singleton.mp hw] at hwr
        exact mem_O_out.mpr ⟨(orReaches_le 26 C C.output h hwr).2, hor, hwr⟩)
    obtain ⟨r0, hr0⟩ := hTe
    have hf_out : f C.output ∩ T_gates C = T_gates C := by
      ext a; simp only [f, Finset.mem_inter, Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro ha; exact ⟨⟨ha, (mem_T_gates.mp ha).2.2⟩, ha⟩
    have hcov : ∀ u ∈ T_gates C, ∃ r ∈ ({r0} : Finset ℕ), EdgeReach E u r := by
      intro u hu
      refine ⟨r0, Finset.mem_singleton_self r0, ?_⟩
      apply hconn C.output (Finset.mem_singleton_self _)
      · rw [hf_out]; exact hu
      · rw [hf_out]; exact hr0
    have hb := graph_spanning_bound E (T_gates C) {r0} hcov
    rw [Finset.card_singleton] at hb
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hTe]; simp

def O_c (C : Circuit) (i : ℕ) (c : Fin 26) : Finset ℕ :=
  (O_pure C i).filter fun h => orIn 26 C (26 + h) ⊆ nbrs c

def O_extra (C : Circuit) (i : ℕ) : Finset ℕ :=
  O_N C \ (Finset.univ : Finset (Fin 26)).biUnion (O_c C i)

lemma oC_pairwiseDisjoint {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 26))) (O_c C i) := by
  intro c1 _ c2 _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro h h1 h2
  obtain ⟨hpure, hsub1⟩ := Finset.mem_filter.mp h1
  obtain ⟨_, hsub2⟩ := Finset.mem_filter.mp h2
  have hhN := (mem_O_pure.mp hpure).1
  have hh_info := mem_O_N.mp hhN
  have hge2 := min_pure_or_card_ge_two hMin hh_info.1 hh_info.2.1 (oPure_no_and hMin huniq hpure)
  have hsub_inter : orIn 26 C (26 + h) ⊆ nbrs c1 ∩ nbrs c2 := Finset.subset_inter hsub1 hsub2
  have hle1 := (Finset.card_le_card hsub_inter).trans (pg_no_c4 c1 c2 hne)
  omega

lemma oN_card_eq {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    (O_N C).card = (O_extra C i).card + ∑ c : Fin 26, (O_c C i c).card := by
  have hsub : (Finset.univ : Finset (Fin 26)).biUnion (O_c C i) ⊆ O_N C := by
    intro h hh
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hh
    exact (mem_O_pure.mp (Finset.mem_filter.mp hc).1).1
  have hcard_bi : ((Finset.univ : Finset (Fin 26)).biUnion (O_c C i)).card =
      ∑ c : Fin 26, (O_c C i c).card :=
    Finset.card_biUnion (oC_pairwiseDisjoint hMin huniq)
  unfold O_extra
  have hs := Finset.card_sdiff_add_card_eq_card hsub
  omega

lemma pure_star_center_bound {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (c : Fin 26) (W : Finset ℕ)
    (hW_lt : ∀ w ∈ W, w < 26 + C.gates.length)
    (hW_sub : ∀ w ∈ W, orIn 26 C w ⊆ nbrs c)
    (hW_pure : ∀ w ∈ W, ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i) :
    (W.biUnion (orIn 26 C)).card ≤ (O_c C i c).card + W.card := by
  classical
  have hAO := min_isAO2 hMin
  set U := W.biUnion (orIn 26 C)
  have hf_in : ∀ w < 26, (orIn 26 C w).card ≤ 1 := by
    intro w hw
    have heq : orIn 26 C w = {⟨w, hw⟩} := by
      ext v; simp [orIn_input C hw v, Fin.ext_iff]
    rw [heq]; simp
  have hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (orIn 26 C (26 + g)).card ≤ 1 := by
    intro g hg hand; rw [orIn_gate_and C hg hand]; simp
  have hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
      orIn 26 C (26 + g) = orIn 26 C (opnd C g 0) ∪ orIn 26 C (opnd C g 1) :=
    fun g hg hor => orIn_gate_or hAO hg hor
  obtain ⟨E, hElen, hconn⟩ := dag_conn hAO (orIn 26 C) hf_in hf_and hf_or (O_c C i c) U W hW_lt
    (fun w hw h hwr hor _ _ _ => Finset.mem_filter.mpr
      ⟨hW_pure w hw h hwr hor, (orIn_mono_of_orReaches C w h hwr).trans (hW_sub w hw)⟩)
  let Wne := W.filter fun w => (orIn 26 C w).Nonempty
  let R : Finset (Fin 26) := Wne.attach.image fun w => (Finset.mem_filter.mp w.2).2.choose
  have hR_card : R.card ≤ W.card :=
    Finset.card_image_le.trans (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
  have hcov : ∀ u ∈ U, ∃ r ∈ R, EdgeReach E u r := by
    intro u hu
    obtain ⟨w, hwW, huw⟩ := Finset.mem_biUnion.mp hu
    have hne : (orIn 26 C w).Nonempty := ⟨u, huw⟩
    have hwne : w ∈ Wne := Finset.mem_filter.mpr ⟨hwW, hne⟩
    let r := (Finset.mem_filter.mp hwne).2.choose
    have hr_mem : r ∈ orIn 26 C w := (Finset.mem_filter.mp hwne).2.choose_spec
    have hr_U : r ∈ U := Finset.mem_biUnion.mpr ⟨w, hwW, hr_mem⟩
    have hr_R : r ∈ R := Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩
    exact ⟨r, hr_R, hconn w hwW u (Finset.mem_inter.mpr ⟨huw, hu⟩) r (Finset.mem_inter.mpr ⟨hr_mem, hr_U⟩)⟩
  have hb := graph_spanning_bound E U R hcov
  omega

def fMix (C : Circuit) (i : ℕ) (w : ℕ) : Finset (Option (Fin 26)) :=
  (orIn 26 C w).image some ∪ if OrReaches 26 C w i then {none} else ∅

lemma mixed_center_conn {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hiand : (gateAt C i).op = GateOp.and)
    (c0 : Fin 26) (L : Finset (Option (Fin 26)))
    (hL_sub : L ⊆ (nbrs c0).image some ∪ {some c0, none})
    (W : Finset ℕ) (hW_lt : ∀ w ∈ W, w < 26 + C.gates.length)
    (hW_oN : ∀ w ∈ W, ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_N C) :
    ∃ E : List (Option (Fin 26) × Option (Fin 26)),
      E.length ≤ (O_c C i c0 ∪ O_extra C i).card ∧
      ∀ w ∈ W, ∀ u ∈ fMix C i w ∩ L, ∀ v ∈ fMix C i w ∩ L, EdgeReach E u v := by
  have hAO := min_isAO2 hMin
  have hf_in : ∀ w < 26, (fMix C i w).card ≤ 1 := by
    intro w hw
    have hnr : ¬ OrReaches 26 C w i := fun hr => by have := hr.1; omega
    have heq : orIn 26 C w = {⟨w, hw⟩} := by ext v; simp [orIn_input C hw v, Fin.ext_iff]
    simp [fMix, hnr, heq]
  have hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (fMix C i (26 + g)).card ≤ 1 := by
    intro g hg hand
    simp only [fMix, orIn_gate_and C hg hand, Finset.image_empty, Finset.empty_union]
    split_ifs <;> simp
  have hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
      fMix C i (26 + g) = fMix C i (opnd C g 0) ∪ fMix C i (opnd C g 1) := by
    intro g hg hor
    have hne : i ≠ g := fun heq => by subst heq; rw [hiand] at hor; cases hor
    ext x
    simp only [fMix, orIn_gate_or hAO hg hor, Finset.image_union, Finset.mem_union,
      orReaches_gate_or_iff hAO hg hor hne]
    cases x <;>
      by_cases h0 : OrReaches 26 C (opnd C g 0) i <;>
      by_cases h1 : OrReaches 26 C (opnd C g 1) i <;>
      simp [h0, h1]
  apply dag_conn hAO (fMix C i) hf_in hf_and hf_or (O_c C i c0 ∪ O_extra C i) L W hW_lt
  intro w hw h hwr hor hcard2 _ _
  have hhN : h ∈ O_N C := hW_oN w hw h hwr hor
  by_cases hex : h ∈ O_extra C i
  · exact Finset.mem_union_right _ hex
  · apply Finset.mem_union_left
    unfold O_extra at hex
    rw [Finset.mem_sdiff] at hex
    push_neg at hex
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp (hex hhN)
    by_cases hcc0 : c = c0
    · rwa [hcc0] at hhc
    · exfalso
      obtain ⟨hhpure, hsub_c⟩ := Finset.mem_filter.mp hhc
      have hnotri := (mem_O_pure.mp hhpure).2
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard2
      obtain ⟨hxf, hxL⟩ := Finset.mem_inter.mp hx
      obtain ⟨hyf, hyL⟩ := Finset.mem_inter.mp hy
      simp only [fMix, hnotri, ↓reduceIte, Finset.union_empty, Finset.mem_image] at hxf hyf
      obtain ⟨u, hu, rfl⟩ := hxf
      obtain ⟨v, hv, rfl⟩ := hyf
      have huv : u ≠ v := fun heq => hxy (congrArg some heq)
      have huc : u ∈ nbrs c := hsub_c hu
      have hvc : v ∈ nbrs c := hsub_c hv
      have huL : u ∈ nbrs c0 ∨ u = c0 := by
        have h1 := hL_sub hxL
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
          Option.some.injEq, reduceCtorEq, or_false] at h1
        rcases h1 with ⟨u', hu', heq⟩ | heq
        · left; rwa [← heq]
        · exact Or.inr heq
      have hvL : v ∈ nbrs c0 ∨ v = c0 := by
        have h1 := hL_sub hyL
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
          Option.some.injEq, reduceCtorEq, or_false] at h1
        rcases h1 with ⟨v', hv', heq⟩ | heq
        · left; rwa [← heq]
        · exact Or.inr heq
      rcases huL with hu0 | rfl <;> rcases hvL with hv0 | rfl
      · have hpair : ({u, v} : Finset (Fin 26)) ⊆ nbrs c ∩ nbrs c0 := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by assumption, by assumption⟩
        have := (Finset.card_le_card hpair).trans (pg_no_c4 c c0 hcc0)
        rw [Finset.card_pair huv] at this; omega
      · have hb1 := pgAdj_bip c u (mem_nbrs_iff c u |>.mp huc)
        have hb2 := pgAdj_bip c v (mem_nbrs_iff c v |>.mp hvc)
        have hb3 := pgAdj_bip v u (mem_nbrs_iff v u |>.mp hu0)
        tauto
      · have hb1 := pgAdj_bip c u (mem_nbrs_iff c u |>.mp huc)
        have hb2 := pgAdj_bip c v (mem_nbrs_iff c v |>.mp hvc)
        have hb3 := pgAdj_bip u v (mem_nbrs_iff u v |>.mp hv0)
        tauto
      · exact huv rfl

-- Section 7: Star decomposition, Case 1, Case 2, and main proof

def dirEdge (u v : Fin 26) : Fin 26 × Fin 26 :=
  if u.val < 13 then (u, v) else (v, u)

lemma dirEdge_mem_pgEdges {u v : Fin 26} (h : pgAdj u v = true) : dirEdge u v ∈ pgEdges := by
  have hbip := pgAdj_bip u v h
  rw [mem_pgEdges_iff]
  unfold dirEdge
  split_ifs with hu
  · exact ⟨hu, h⟩
  · have hv : v.val < 13 := by tauto
    exact ⟨hv, by rwa [pgAdj_symm]⟩

lemma dirEdge_symm {u v : Fin 26} (h : pgAdj u v = true) : dirEdge u v = dirEdge v u := by
  have hbip := pgAdj_bip u v h
  unfold dirEdge
  by_cases hu : u.val < 13 <;> by_cases hv : v.val < 13
  · exact (hbip (propext (iff_of_true hu hv))).elim
  · simp [hu, hv]
  · simp [hu, hv]
  · exact (hbip (propext (iff_of_false hu hv))).elim

lemma dirEdge_eq_of_mem_pgEdges {e : Fin 26 × Fin 26} (he : e ∈ pgEdges) :
    dirEdge e.1 e.2 = e := by
  rw [mem_pgEdges_iff] at he
  unfold dirEdge
  simp [he.1]

def starEdgesOf (c : Fin 26) (L : Finset (Fin 26)) : Finset (Fin 26 × Fin 26) :=
  L.image (dirEdge c)

lemma starEdgesOf_card (c : Fin 26) (L : Finset (Fin 26)) :
    (starEdgesOf c L).card = L.card := by
  unfold starEdgesOf
  apply Finset.card_image_of_injective
  intro x y hxy
  unfold dirEdge at hxy
  split_ifs at hxy
  · exact congrArg Prod.snd hxy
  · exact congrArg Prod.fst hxy

lemma starEdgesOf_card_le_four {c : Fin 26} {L : Finset (Fin 26)} (hL : L ⊆ nbrs c) :
    (starEdgesOf c L).card ≤ 4 := by
  rw [starEdgesOf_card]
  exact (Finset.card_le_card hL).trans (nbrs_card c).le

lemma mem_starEdgesOf_left {c v : Fin 26} {L : Finset (Fin 26)} (hv : v ∈ L) :
    dirEdge c v ∈ starEdgesOf c L :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

lemma mem_starEdgesOf_right {c u : Fin 26} {L : Finset (Fin 26)} (hadj : pgAdj u c = true) (hu : u ∈ L) :
    dirEdge u c ∈ starEdgesOf c L := by
  rw [dirEdge_symm hadj]
  exact mem_starEdgesOf_left hu

lemma biclique_is_star {S0 S1 : Finset (Fin 26)}
    (hadj : ∀ u ∈ S0, ∀ v ∈ S1, pgAdj u v = true) :
    S0.card ≤ 1 ∨ S1.card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp h.2
  have hsub : ({v1, v2} : Finset (Fin 26)) ⊆ nbrs u1 ∩ nbrs u2 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with heq | heq
    · rw [heq]; exact Finset.mem_inter.mpr ⟨(mem_nbrs_iff u1 v1).mpr (hadj u1 hu1 v1 hv1),
        (mem_nbrs_iff u2 v1).mpr (hadj u2 hu2 v1 hv1)⟩
    · rw [heq]; exact Finset.mem_inter.mpr ⟨(mem_nbrs_iff u1 v2).mpr (hadj u1 hu1 v2 hv2),
        (mem_nbrs_iff u2 v2).mpr (hadj u2 hu2 v2 hv2)⟩
  have hle := (Finset.card_le_card hsub).trans (pg_no_c4 u1 u2 hune)
  rw [Finset.card_pair hvne] at hle
  omega

lemma oOut_not_inCone_any_and {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {b : ℕ} (hb : b < C.gates.length) (hband : (gateAt C b).op = GateOp.and)
    {h : ℕ} (hh : h ∈ O_out C) : ¬ InCone 26 C h b := by
  intro hic
  have hAO := min_isAO2 hMin
  set S := (O_out C).filter fun g => g = h ∨ InCone 26 C g h
  have hS_ne : S.Nonempty := ⟨h, Finset.mem_filter.mpr ⟨hh, Or.inl rfl⟩⟩
  set h0 := S.min' hS_ne with hh0_def
  obtain ⟨hh0_out, hh0_rel⟩ := Finset.mem_filter.mp (Finset.min'_mem S hS_ne)
  have hh0_info := mem_O_out.mp hh0_out
  have h0_ic_b : InCone 26 C h0 b := by
    rcases hh0_rel with heq | h0h
    · rw [← hh0_def] at heq; rw [heq]; exact hic
    · exact inCone_trans 26 C h0 h b h0h hic
  have hop_and : ∀ s : Fin 2, ∃ a < C.gates.length, opnd C h0 s = 26 + a ∧ (gateAt C a).op = GateOp.and := by
    intro s
    have hh0_lt : h0 < C.gates.length := hh0_info.1
    have hmem : opnd C h0 s ∈ (gateAt C h0).inputs := opnd_mem hAO hh0_lt s
    have hge : 26 ≤ opnd C h0 s := oOut_reads_ge_26 hMin hh0_out hmem
    have hlt : opnd C h0 s < 26 + h0 := opnd_lt hAO hh0_lt s
    set a := opnd C h0 s - 26 with ha_def
    have ha_lt : a < C.gates.length := by rw [ha_def]; omega
    have ha_eq : opnd C h0 s = 26 + a := by rw [ha_def]; omega
    refine ⟨a, ha_lt, ha_eq, ?_⟩
    rcases hAO.1 _ (gateAt_mem ha_lt) with hand | hor
    · exact hand
    · exfalso
      have ha_out : a ∈ O_out C := by
        rw [mem_O_out]
        refine ⟨ha_lt, hor, orReaches_trans 26 C C.output h0 a hh0_info.2.2 ?_⟩
        rw [orReaches_gate_iff 26 C hh0_info.1 a]
        right
        exact ⟨hh0_info.2.1, opnd C h0 s, hmem, hlt, by rw [ha_eq]; exact orReaches_self 26 C ha_lt⟩
      have ha_ic_h0 : InCone 26 C a h0 := by
        rw [inCone_gate_iff 26 C a h0 hh0_info.1]
        exact ⟨opnd C h0 s, hmem, hge, hlt, Or.inl rfl⟩
      have ha_S : a ∈ S := Finset.mem_filter.mpr ⟨ha_out, Or.inr (by
        rcases hh0_rel with heq | h0h
        · rw [← hh0_def] at heq; rwa [← heq]
        · exact inCone_trans 26 C a h0 h ha_ic_h0 h0h)⟩
      have hle : h0 ≤ a := Finset.min'_le S a ha_S
      rw [ha_def] at hle
      omega
  obtain ⟨a0, ha0_lt, ha0_eq, ha0_and⟩ := hop_and 0
  obtain ⟨a1, ha1_lt, ha1_eq, ha1_and⟩ := hop_and 1
  have ha0_ic : InCone 26 C a0 b := inCone_trans 26 C a0 h0 b (by
    rw [inCone_gate_iff 26 C a0 h0 hh0_info.1]
    exact ⟨opnd C h0 0, opnd_mem hAO hh0_info.1 0, by omega, opnd_lt hAO hh0_info.1 0, Or.inl (by omega)⟩) h0_ic_b
  have ha1_ic : InCone 26 C a1 b := inCone_trans 26 C a1 h0 b (by
    rw [inCone_gate_iff 26 C a1 h0 hh0_info.1]
    exact ⟨opnd C h0 1, opnd_mem hAO hh0_info.1 1, by omega, opnd_lt hAO hh0_info.1 1, Or.inl (by omega)⟩) h0_ic_b
  have heq0 := (huniq a0 ha0_lt b hb ha0_and hband ha0_ic).1
  have heq1 := (huniq a1 ha1_lt b hb ha1_and hband ha1_ic).1
  have hne := min_opnd_ne hMin hh0_info.1
  rw [ha0_eq, ha1_eq, heq0, heq1] at hne
  exact hne rfl

lemma opnd_or_in_ON {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    {h : ℕ} (hhr : OrReaches 26 C (opnd C a s) h) (hhor : (gateAt C h).op = GateOp.or) :
    h ∈ O_N C := by
  have hAO := min_isAO2 hMin
  have hh_lt := (orReaches_le 26 C (opnd C a s) h hhr).2
  have hh_ic : InCone 26 C h a := by
    have h26 := hhr.1
    have hlt := opnd_lt hAO ha s
    have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C a s - 26 < C.gates.length by omega) h
      (by rwa [show 26 + (opnd C a s - 26) = opnd C a s by omega])
    rw [inCone_gate_iff 26 C h a ha]
    exact ⟨opnd C a s, opnd_mem hAO ha s, h26, hlt, hsub⟩
  refine mem_O_N.mpr ⟨hh_lt, hhor, fun hro => ?_⟩
  exact oOut_not_inCone_any_and hMin huniq ha haand (mem_O_out.mpr ⟨hh_lt, hhor, hro⟩) hh_ic

lemma opnd_or_in_Opure_of_ne_j {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hiand : (gateAt C i).op = GateOp.and)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (hnej : a ≠ j)
    (s : Fin 2) {h : ℕ} (hhr : OrReaches 26 C (opnd C a s) h) (hhor : (gateAt C h).op = GateOp.or) :
    h ∈ O_pure C i := by
  have hAO := min_isAO2 hMin
  have hhN := opnd_or_in_ON hMin huniq ha haand s hhr hhor
  refine mem_O_pure.mpr ⟨hhN, fun hhi => ?_⟩
  have hri : OrReaches 26 C (opnd C a s) i := orReaches_trans 26 C (opnd C a s) h i hhr hhi
  have h26 := hri.1
  have hlt := opnd_lt hAO ha s
  have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C a s - 26 < C.gates.length by omega) i
    (by rwa [show 26 + (opnd C a s - 26) = opnd C a s by omega])
  have hic : InCone 26 C i a := by
    rw [inCone_gate_iff 26 C i a ha]
    exact ⟨opnd C a s, opnd_mem hAO ha s, h26, hlt, hsub⟩
  exact hnej (huniq i hi a ha hiand haand hic).2

lemma opnd_or_in_Opure_of_not_reach_i {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hnri : ¬ OrReaches 26 C (opnd C a s) i)
    {h : ℕ} (hhr : OrReaches 26 C (opnd C a s) h) (hhor : (gateAt C h).op = GateOp.or) :
    h ∈ O_pure C i :=
  mem_O_pure.mpr ⟨opnd_or_in_ON hMin huniq ha haand s hhr hhor,
    fun hhi => hnri (orReaches_trans 26 C (opnd C a s) h i hhr hhi)⟩

lemma pure_and_eval {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (hnej : a ≠ j)
    (x : Fin 26 → Bool) :
    gateVal 26 C a x = true ↔
      (∃ u ∈ side (n := 26) C a 0, x u = true) ∧ (∃ v ∈ side (n := 26) C a 1, x v = true) := by
  have hAO := min_isAO2 hMin
  change wireVal 26 C (26 + a) x = true ↔ _
  unfold side
  rw [wireVal_gate_and hAO ha haand, Bool.and_eq_true]
  have hside : ∀ s : Fin 2, wireVal 26 C (opnd C a s) x = true ↔ ∃ u ∈ orIn 26 C (opnd C a s), x u = true := by
    intro s
    have hlt := opnd_lt hAO ha s
    have hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ OrReaches 26 C (opnd C a s) k := by
      intro k hk hkand hrk
      have h26 := hrk.1
      have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C a s - 26 < C.gates.length by omega) k
        (by rwa [show 26 + (opnd C a s - 26) = opnd C a s by omega])
      have hic : InCone 26 C k a := by
        rw [inCone_gate_iff 26 C k a ha]
        exact ⟨opnd C a s, opnd_mem hAO ha s, h26, hlt, hsub⟩
      exact hnej (huniq k hk a ha hkand haand hic).2
    have h1 := wireVal_eq_orIn_or_i hMin.1.1 hMin.1.2.1 C.gates.length (opnd C a s) (by omega)
      (fun k hk hkand hrk => (hno k hk hkand hrk).elim) x
    have h2 : ¬ OrReaches 26 C (opnd C a s) C.gates.length := fun hr => by
      have := (orReaches_le 26 C (opnd C a s) C.gates.length hr).2; omega
    simpa [h2] using h1
  rw [hside 0, hside 1]

lemma j_eval {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hj : j < C.gates.length) (hjand : (gateAt C j).op = GateOp.and)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (x : Fin 26 → Bool) :
    gateVal 26 C j x = true ↔
      ((OrReaches 26 C (opnd C j 0) i ∧ gateVal 26 C i x = true) ∨
        ∃ u ∈ side (n := 26) C j 0, x u = true) ∧
      ((OrReaches 26 C (opnd C j 1) i ∧ gateVal 26 C i x = true) ∨
        ∃ v ∈ side (n := 26) C j 1, x v = true) := by
  have hAO := min_isAO2 hMin
  change wireVal 26 C (26 + j) x = true ↔ _
  unfold side
  rw [wireVal_gate_and hAO hj hjand, Bool.and_eq_true]
  have hside : ∀ s : Fin 2, wireVal 26 C (opnd C j s) x = true ↔
      (OrReaches 26 C (opnd C j s) i ∧ gateVal 26 C i x = true) ∨
      ∃ u ∈ orIn 26 C (opnd C j s), x u = true := by
    intro s
    have hlt := opnd_lt hAO hj s
    apply wireVal_eq_orIn_or_i hMin.1.1 hMin.1.2.1 i (opnd C j s) (by omega)
    intro k hk hkand hrk
    have h26 := hrk.1
    have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C j s - 26 < C.gates.length by omega) k
      (by rwa [show 26 + (opnd C j s - 26) = opnd C j s by omega])
    have hic : InCone 26 C k j := by
      rw [inCone_gate_iff 26 C k j hj]
      exact ⟨opnd C j s, opnd_mem hAO hj s, h26, hlt, hsub⟩
    exact (huniq k hk j hj hkand hjand hic).1
  rw [hside 0, hside 1]

lemma j_orReaches_i {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hic : InCone 26 C i j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    OrReaches 26 C (opnd C j 0) i ∨ OrReaches 26 C (opnd C j 1) i := by
  have hAO := min_isAO2 hMin
  rw [inCone_gate_iff 26 C i j hj, gate_inputs_eq hAO hj] at hic
  obtain ⟨w, hw, h26w, hwj, hiw | hick⟩ := hic
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hself := orReaches_self 26 C hi
    rw [show 26 + i = w by omega] at hself
    rcases hw with rfl | rfl
    · exact Or.inl hself
    · exact Or.inr hself
  · set k := w - 26
    have hk_lt : k < C.gates.length := by omega
    have hrk : OrReaches 26 C (26 + k) i := by
      apply inCone_to_orReaches hAO i k hk_lt hick
      intro b hb hband hib
      have hbj := (huniq i hi b hb hiand hband hib).2
      rw [hbj]
      refine ⟨by omega, fun hjk => ?_⟩
      have := inCone_lt 26 C j k hjk
      omega
    rw [show 26 + k = w by omega] at hrk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hrk
    · exact Or.inr hrk

lemma edge_accepted_by_T {C : Circuit} (hMin : IsMin C) {e : Fin 26 × Fin 26} (he : e ∈ pgEdges) :
    ∃ a ∈ T_gates C, gateVal 26 C a (pairInput e.1 e.2) = true := by
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  have ht : wireVal 26 C C.output (pairInput e.1 e.2) = true :=
    valid_eval_pairInput_true hMin.1 (mem_pgEdges_iff e |>.mp he).2
  suffices hrec : ∀ w < 26 + C.gates.length, (w = C.output ∨ (26 ≤ w ∧ OrReaches 26 C C.output (w - 26))) →
      wireVal 26 C w (pairInput e.1 e.2) = true →
      ∃ a ∈ T_gates C, gateVal 26 C a (pairInput e.1 e.2) = true from
    hrec C.output hout.2 (Or.inl rfl) ht
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hreach hval
    have h26w : 26 ≤ w := by
      rcases hreach with rfl | ⟨h26, _⟩
      · exact hout.1
      · exact h26
    set k := w - 26
    have hk_lt : k < C.gates.length := by omega
    have hwk : w = 26 + k := by omega
    have hro : OrReaches 26 C C.output k := by
      rcases hreach with rfl | ⟨_, hr⟩
      · rw [hwk]; exact orReaches_self 26 C hk_lt
      · exact hr
    rcases hAO.1 _ (gateAt_mem hk_lt) with hand | hor
    · exact ⟨k, mem_T_gates.mpr ⟨hk_lt, hand, hro⟩, by change wireVal 26 C (26 + k) _ = true; rwa [← hwk]⟩
    · rw [hwk, wireVal_gate_or hAO hk_lt hor, Bool.or_eq_true] at hval
      have hkout : k ∈ O_out C := mem_O_out.mpr ⟨hk_lt, hor, hro⟩
      rcases hval with h0 | h1
      · have h0lt := opnd_lt hAO hk_lt 0
        have h0ge := oOut_reads_ge_26 hMin hkout (opnd_mem hAO hk_lt 0)
        apply ih (opnd C k 0) (by omega) (by omega) ?_ h0
        right; refine ⟨h0ge, orReaches_trans 26 C C.output k (opnd C k 0 - 26) hro ?_⟩
        rw [orReaches_gate_iff 26 C hk_lt]
        right
        refine ⟨hor, opnd C k 0, opnd_mem hAO hk_lt 0, h0lt, ?_⟩
        have hself := orReaches_self 26 C (show opnd C k 0 - 26 < C.gates.length by omega)
        rwa [show 26 + (opnd C k 0 - 26) = opnd C k 0 by omega] at hself
      · have h1lt := opnd_lt hAO hk_lt 1
        have h1ge := oOut_reads_ge_26 hMin hkout (opnd_mem hAO hk_lt 1)
        apply ih (opnd C k 1) (by omega) (by omega) ?_ h1
        right; refine ⟨h1ge, orReaches_trans 26 C C.output k (opnd C k 1 - 26) hro ?_⟩
        rw [orReaches_gate_iff 26 C hk_lt]
        right
        refine ⟨hor, opnd C k 1, opnd_mem hAO hk_lt 1, h1lt, ?_⟩
        have hself := orReaches_self 26 C (show opnd C k 1 - 26 < C.gates.length by omega)
        rwa [show 26 + (opnd C k 1 - 26) = opnd C k 1 by omega] at hself

lemma pure_star_spec {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (hnej : a ≠ j)
    (hbelow : ∀ u v : Fin 26, pgAdj u v = false → gateVal 26 C a (pairInput u v) = false) :
    ∃ (c : Fin 26) (s : Fin 2),
      side (n := 26) C a (1 - s) = {c} ∧
      side (n := 26) C a s ⊆ nbrs c ∧
      (side (n := 26) C a s).Nonempty ∧
      ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
        e ∈ starEdgesOf c (side (n := 26) C a s) := by
  have hadj : ∀ u ∈ side (n := 26) C a 0, ∀ v ∈ side (n := 26) C a 1, pgAdj u v = true := by
    intro u hu v hv
    cases h : pgAdj u v
    · exfalso
      have hf := hbelow u v h
      have ht : gateVal 26 C a (pairInput u v) = true :=
        (pure_and_eval hMin huniq ha haand hnej (pairInput u v)).mpr
          ⟨⟨u, hu, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩
      rw [hf] at ht; cases ht
    · rfl
  have hne0 : (side (n := 26) C a 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply min_no_const_gate hMin ha false
    intro x
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨⟨u, hu, _⟩, _⟩ := (pure_and_eval hMin huniq ha haand hnej x).mp ht
    rw [h] at hu; exact Finset.notMem_empty u hu
  have hne1 : (side (n := 26) C a 1).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply min_no_const_gate hMin ha false
    intro x
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨_, ⟨v, hv, _⟩⟩ := (pure_and_eval hMin huniq ha haand hnej x).mp ht
    rw [h] at hv; exact Finset.notMem_empty v hv
  rcases biclique_is_star hadj with h0 | h1
  · have h0eq : (side (n := 26) C a 0).card = 1 := le_antisymm h0 (Finset.card_pos.mpr hne0)
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h0eq
    refine ⟨c, 1, by simpa using hc, ?_, hne1, ?_⟩
    · intro v hv
      exact (mem_nbrs_iff c v).mpr (hadj c (by rw [hc]; simp) v hv)
    · intro e he hgt
      obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩ := (pure_and_eval hMin huniq ha haand hnej _).mp hgt
      rw [hc, Finset.mem_singleton] at hu; subst u
      simp only [pairInput, decide_eq_true_eq] at hup hvp
      have hne_cv : c ≠ v := fun heq => by
        subst heq; have := hadj c (by rw [hc]; simp) c hv; rw [pgAdj_irrefl] at this; cases this
      have hadj_e := (mem_pgEdges_iff e).mp he |>.2
      rw [← dirEdge_eq_of_mem_pgEdges he]
      rcases hup with h1c | h2c <;> rcases hvp with h1' | h2'
      · exact (hne_cv (h1c.trans h1'.symm)).elim
      · rw [← h1c, ← h2']; exact mem_starEdgesOf_left hv
      · rw [← h1', ← h2c] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hv
      · exact (hne_cv (h2c.trans h2'.symm)).elim
  · have h1eq : (side (n := 26) C a 1).card = 1 := le_antisymm h1 (Finset.card_pos.mpr hne1)
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1eq
    refine ⟨c, 0, by simpa using hc, ?_, hne0, ?_⟩
    · intro u hu
      exact (mem_nbrs_iff c u).mpr (by rw [pgAdj_symm]; exact hadj u hu c (by rw [hc]; simp))
    · intro e he hgt
      obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩ := (pure_and_eval hMin huniq ha haand hnej _).mp hgt
      rw [hc, Finset.mem_singleton] at hv; subst v
      simp only [pairInput, decide_eq_true_eq] at hup hvp
      have hne_uc : u ≠ c := fun heq => by
        subst heq; have := hadj u hu u (by rw [hc]; simp); rw [pgAdj_irrefl] at this; cases this
      have hadj_e := (mem_pgEdges_iff e).mp he |>.2
      rw [← dirEdge_eq_of_mem_pgEdges he]
      rcases hup with h1u | h2u <;> rcases hvp with h1' | h2'
      · exact (hne_uc (h1u.trans h1'.symm)).elim
      · rw [← h1u, ← h2'] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hu
      · rw [← h2u, ← h1']; exact mem_starEdgesOf_left hu
      · exact (hne_uc (h2u.trans h2'.symm)).elim

lemma below_of_mem_T {C : Circuit} (hMin : IsMin C) {a : ℕ} (ha : a ∈ T_gates C) :
    ∀ u v : Fin 26, pgAdj u v = false → gateVal 26 C a (pairInput u v) = false := by
  intro u v hnadj
  rw [Bool.eq_false_iff]
  intro ht
  have hf := valid_eval_pairInput_false hMin.1 hnadj
  have hout := wireVal_ge_of_orReaches hMin.1.2.1 C.output a (pairInput u v) (mem_T_gates.mp ha).2.2 ht
  rw [hf] at hout
  cases hout

lemma extra_of_mixed_bipartite {C : Circuit} (hMin : IsMin C) {i : ℕ}
    {w : ℕ} (hw : w < 26 + C.gates.length)
    (hwoN : ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_N C)
    {u v : Fin 26} (hu : u ∈ orIn 26 C w) (hv : v ∈ orIn 26 C w)
    (hbip : (u.val < 13) ≠ (v.val < 13)) :
    1 ≤ (O_extra C i).card := by
  have hAO := min_isAO2 hMin
  have hne : u ≠ v := fun heq => hbip (by rw [heq])
  have h26 : 26 ≤ w := by
    by_contra hlt; push_neg at hlt
    have e1 := (orIn_input C hlt u).mp hu
    have e2 := (orIn_input C hlt v).mp hv
    exact hne (Fin.ext (e1.trans e2.symm))
  set h := w - 26
  have hh_lt : h < C.gates.length := by omega
  have hwh : w = 26 + h := by omega
  rw [hwh] at hu hv hwoN
  have hhor : (gateAt C h).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
    · rw [orIn_gate_and C hh_lt hand] at hu; exact (Finset.notMem_empty u hu).elim
    · exact hor
  have hhN : h ∈ O_N C := hwoN h (orReaches_self 26 C hh_lt) hhor
  have hhex : h ∈ O_extra C i := by
    unfold O_extra
    rw [Finset.mem_sdiff]
    refine ⟨hhN, ?_⟩
    intro hbi
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp hbi
    have hsub := (Finset.mem_filter.mp hhc).2
    have hb1 := pgAdj_bip c u ((mem_nbrs_iff c u).mp (hsub hu))
    have hb2 := pgAdj_bip c v ((mem_nbrs_iff c v).mp (hsub hv))
    tauto
  exact Finset.card_pos.mpr ⟨h, hhex⟩

lemma extra_of_reaches_i_and_input {C : Circuit} (hMin : IsMin C) {i : ℕ}
    (hiand : (gateAt C i).op = GateOp.and)
    {w : ℕ} (hw : w < 26 + C.gates.length)
    (hri : OrReaches 26 C w i) (hne : (orIn 26 C w).Nonempty)
    (hwoN : ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_N C) :
    1 ≤ (O_extra C i).card := by
  have hAO := min_isAO2 hMin
  have h26 := hri.1
  set h := w - 26
  have hh_lt : h < C.gates.length := by omega
  have hwh : w = 26 + h := by omega
  rw [hwh] at hri hne hwoN
  have hhor : (gateAt C h).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
    · rw [orIn_gate_and C hh_lt hand] at hne; exact (Finset.not_nonempty_empty hne).elim
    · exact hor
  have hhN : h ∈ O_N C := hwoN h (orReaches_self 26 C hh_lt) hhor
  have hhex : h ∈ O_extra C i := by
    unfold O_extra
    rw [Finset.mem_sdiff]
    refine ⟨hhN, ?_⟩
    intro hbi
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp hbi
    exact (mem_O_pure.mp (Finset.mem_filter.mp hhc).1).2 hri
  exact Finset.card_pos.mpr ⟨h, hhex⟩

lemma card_filter_sum {α β : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    (s : Finset α) (f : α → β) :
    ∑ b : β, (s.filter fun a => f a = b).card = s.card := by
  rw [← Finset.card_biUnion]
  · congr 1; ext a; simp
  · intro b1 _ b2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

-- General pure star family summing bound
lemma pure_family_sum_bound {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (Idx : Finset ℕ) (ctr : ℕ → Fin 26) (wire : ℕ → ℕ)
    (hW_lt : ∀ k ∈ Idx, wire k < 26 + C.gates.length)
    (hW_sub : ∀ k ∈ Idx, orIn 26 C (wire k) ⊆ nbrs (ctr k))
    (hW_pure : ∀ k ∈ Idx, ∀ h, OrReaches 26 C (wire k) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i)
    (hcov : ∀ e ∈ pgEdges, ∃ k ∈ Idx, e ∈ starEdgesOf (ctr k) (orIn 26 C (wire k))) :
    52 ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
  let Wc : Fin 26 → Finset ℕ := fun c => (Idx.filter fun k => ctr k = c).image wire
  let Uc : Fin 26 → Finset (Fin 26) := fun c => (Wc c).biUnion (orIn 26 C)
  have hper_c : ∀ c : Fin 26, (Uc c).card ≤ (O_c C i c).card + (Idx.filter fun k => ctr k = c).card := by
    intro c
    have hb := pure_star_center_bound hMin huniq c (Wc c)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_lt k (Finset.mem_filter.mp hk).1)
      (fun w hw => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨hkI, hkc⟩ := Finset.mem_filter.mp hk
        rw [← hkc]; exact hW_sub k hkI)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_pure k (Finset.mem_filter.mp hk).1)
    have hwc_le : (Wc c).card ≤ (Idx.filter fun k => ctr k = c).card := Finset.card_image_le
    exact hb.trans (Nat.add_le_add_left hwc_le _)
  have hsum_U : ∑ c : Fin 26, (Uc c).card ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
    have h1 := Finset.sum_le_sum (s := Finset.univ) fun c _ => hper_c c
    rw [Finset.sum_add_distrib, card_filter_sum Idx ctr] at h1
    exact h1
  have hcov_bi : pgEdges ⊆ (Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c) := by
    intro e he
    obtain ⟨k, hk, hke⟩ := hcov e he
    refine Finset.mem_biUnion.mpr ⟨ctr k, Finset.mem_univ _, ?_⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hke
    refine Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨wire k, ?_, hv⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩
  have h52 : 52 ≤ ∑ c : Fin 26, (Uc c).card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ ((Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c)).card :=
          Finset.card_le_card hcov_bi
      _ ≤ ∑ c : Fin 26, (starEdgesOf c (Uc c)).card := Finset.card_biUnion_le
      _ = ∑ c : Fin 26, (Uc c).card := by congr 1; ext c; exact starEdgesOf_card c (Uc c)
  omega

-- One-center-mixed summing bound
lemma one_mixed_center_bound {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (Idx : Finset ℕ) (ctr : ℕ → Fin 26) (wire : ℕ → ℕ)
    (hW_lt : ∀ k ∈ Idx, wire k < 26 + C.gates.length)
    (hW_sub : ∀ k ∈ Idx, orIn 26 C (wire k) ⊆ nbrs (ctr k))
    (hW_pure : ∀ k ∈ Idx, ∀ h, OrReaches 26 C (wire k) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i)
    (c0 : Fin 26) (L0 : Finset (Fin 26)) (bonus extra_r : ℕ)
    (hcov : ∀ e ∈ pgEdges, (∃ k ∈ Idx, e ∈ starEdgesOf (ctr k) (orIn 26 C (wire k))) ∨
      e ∈ starEdgesOf c0 L0)
    (hc0_bound : (((Idx.filter fun k => ctr k = c0).image wire).biUnion (orIn 26 C) ∪ L0).card + bonus ≤
      (O_c C i c0).card + (O_extra C i).card + (Idx.filter fun k => ctr k = c0).card + extra_r) :
    52 + bonus ≤ (O_N C).card + Idx.card + extra_r := by
  let Wc : Fin 26 → Finset ℕ := fun c => (Idx.filter fun k => ctr k = c).image wire
  let Uc : Fin 26 → Finset (Fin 26) := fun c =>
    if c = c0 then (Wc c0).biUnion (orIn 26 C) ∪ L0 else (Wc c).biUnion (orIn 26 C)
  have hper_ne : ∀ c ∈ (Finset.univ : Finset (Fin 26)).erase c0,
      (Uc c).card ≤ (O_c C i c).card + (Idx.filter fun k => ctr k = c).card := by
    intro c hc
    have hne : c ≠ c0 := (Finset.mem_erase.mp hc).1
    simp only [Uc, hne, ↓reduceIte]
    have hb := pure_star_center_bound hMin huniq c (Wc c)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_lt k (Finset.mem_filter.mp hk).1)
      (fun w hw => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨hkI, hkc⟩ := Finset.mem_filter.mp hk
        rw [← hkc]; exact hW_sub k hkI)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_pure k (Finset.mem_filter.mp hk).1)
    have hwc_le : (Wc c).card ≤ (Idx.filter fun k => ctr k = c).card := Finset.card_image_le
    exact hb.trans (Nat.add_le_add_left hwc_le _)
  have hsum_ne := Finset.sum_le_sum hper_ne
  rw [Finset.sum_add_distrib] at hsum_ne
  have hsum_all : ∑ c : Fin 26, (Uc c).card + bonus ≤ (O_N C).card + Idx.card + extra_r := by
    have h1 : ∑ c : Fin 26, (Uc c).card = (Uc c0).card + ∑ c ∈ Finset.univ.erase c0, (Uc c).card :=
      (Finset.add_sum_erase Finset.univ (fun c => (Uc c).card) (Finset.mem_univ c0)).symm
    have h2 : ∑ c : Fin 26, (O_c C i c).card =
        (O_c C i c0).card + ∑ c ∈ Finset.univ.erase c0, (O_c C i c).card :=
      (Finset.add_sum_erase Finset.univ (fun c => (O_c C i c).card) (Finset.mem_univ c0)).symm
    have h3 : ∑ c : Fin 26, (Idx.filter fun k => ctr k = c).card =
        (Idx.filter fun k => ctr k = c0).card +
        ∑ c ∈ Finset.univ.erase c0, (Idx.filter fun k => ctr k = c).card :=
      (Finset.add_sum_erase Finset.univ (fun c => (Idx.filter fun k => ctr k = c).card) (Finset.mem_univ c0)).symm
    have hpart := card_filter_sum Idx ctr
    have hoN := oN_card_eq hMin huniq
    have hc0_eq : (Uc c0).card = (((Idx.filter fun k => ctr k = c0).image wire).biUnion (orIn 26 C) ∪ L0).card := by
      simp [Uc, Wc]
    omega
  have hcov_bi : pgEdges ⊆ (Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c) := by
    intro e he
    rcases hcov e he with ⟨k, hk, hke⟩ | he0
    · refine Finset.mem_biUnion.mpr ⟨ctr k, Finset.mem_univ _, ?_⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hke
      refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
      have hmem_bi : v ∈ (Wc (ctr k)).biUnion (orIn 26 C) :=
        Finset.mem_biUnion.mpr ⟨wire k, Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩, hv⟩
      by_cases hkc : ctr k = c0
      · simp only [Uc, hkc, ↓reduceIte]
        exact Finset.mem_union_left _ (hkc ▸ hmem_bi)
      · simp only [Uc, hkc, ↓reduceIte]; exact hmem_bi
    · refine Finset.mem_biUnion.mpr ⟨c0, Finset.mem_univ _, ?_⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he0
      refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
      simp only [Uc, ↓reduceIte]
      exact Finset.mem_union_right _ hv
  have h52 : 52 ≤ ∑ c : Fin 26, (Uc c).card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ ((Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c)).card :=
          Finset.card_le_card hcov_bi
      _ ≤ ∑ c : Fin 26, (starEdgesOf c (Uc c)).card := Finset.card_biUnion_le
      _ = ∑ c : Fin 26, (Uc c).card := by congr 1; ext c; exact starEdgesOf_card c (Uc c)
  omega

-- Helper for disjointness of O_c c0 and O_extra
lemma oC_disj_oExtra (C : Circuit) (i : ℕ) (c0 : Fin 26) :
    (O_c C i c0 ∪ O_extra C i).card = (O_c C i c0).card + (O_extra C i).card := by
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro h h1 h2
  unfold O_extra at h2
  rw [Finset.mem_sdiff] at h2
  exact h2.2 (Finset.mem_biUnion.mpr ⟨c0, Finset.mem_univ _, h1⟩)

-- Helper: lower bound on |A_gates| from edge count of j
lemma aGates_card_of_j_edges {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (Astar : Finset ℕ) (hAstar : Astar = ((A_gates C).erase i).erase j)
    (ctr : ℕ → Fin 26) (leaf : ℕ → Finset (Fin 26))
    (hleaf_le : ∀ a ∈ Astar, (leaf a).card ≤ 4)
    (hcov_a : ∀ a ∈ Astar, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (leaf a))
    (Ej : Finset (Fin 26 × Fin 26))
    (hcov_j : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true → e ∈ Ej) :
    52 ≤ 4 * Astar.card + Ej.card := by
  have hsub : pgEdges ⊆ Astar.biUnion (fun a => starEdgesOf (ctr a) (leaf a)) ∪ Ej := by
    intro e he
    obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
    by_cases haj : a = j
    · subst haj; exact Finset.mem_union_right _ (hcov_j e he hga)
    · apply Finset.mem_union_left
      have haS : a ∈ Astar := by
        rw [hAstar, Finset.mem_erase, ← hT_eq]
        exact ⟨haj, haT⟩
      exact Finset.mem_biUnion.mpr ⟨a, haS, hcov_a a haS e he hga⟩
  have h1 : 52 ≤ (Astar.biUnion fun a => starEdgesOf (ctr a) (leaf a)).card + Ej.card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ (Astar.biUnion (fun a => starEdgesOf (ctr a) (leaf a)) ∪ Ej).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  have h2 : (Astar.biUnion fun a => starEdgesOf (ctr a) (leaf a)).card ≤ 4 * Astar.card := by
    calc (Astar.biUnion fun a => starEdgesOf (ctr a) (leaf a)).card
        ≤ ∑ a ∈ Astar, (starEdgesOf (ctr a) (leaf a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Astar, 4 := Finset.sum_le_sum fun a ha => by rw [starEdgesOf_card]; exact hleaf_le a ha
      _ = 4 * Astar.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

-- Case 1: Both operands of j reach i
lemma case_both_reach {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (hOout_ge : (A_gates C).card ≤ (O_out C).card + 2)
    (hr0 : OrReaches 26 C (opnd C j 0) i) (hr1 : OrReaches 26 C (opnd C j 1) i) :
    64 ≤ C.size := by
  classical
  have hAO := min_isAO2 hMin
  have hjT : j ∈ T_gates C := by
    rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩
  have hj_below := below_of_mem_T hMin hjT
  have hi_below : ∀ u v : Fin 26, pgAdj u v = false → gateVal 26 C i (pairInput u v) = false := by
    intro u v hnadj
    rw [Bool.eq_false_iff]
    intro hit
    have hjt : gateVal 26 C j (pairInput u v) = true :=
      (j_eval hMin hj hjand huniq _).mpr ⟨Or.inl ⟨hr0, hit⟩, Or.inl ⟨hr1, hit⟩⟩
    rw [hj_below u v hnadj] at hjt; cases hjt
  -- Set up pure stars for A_not_j = (A_gates C).erase j (which includes i!)
  set Anj := (A_gates C).erase j
  have hAnj_card : Anj.card = (A_gates C).card - 1 := by
    rw [Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hj, hjand⟩)]
  have hAnj_spec : ∀ a ∈ Anj, ∃ (c : Fin 26) (s : Fin 2),
      side (n := 26) C a (1 - s) = {c} ∧ side (n := 26) C a s ⊆ nbrs c ∧
      (side (n := 26) C a s).Nonempty ∧
      ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
        e ∈ starEdgesOf c (side (n := 26) C a s) := by
    intro a ha
    obtain ⟨hanej, haA⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp haA
    apply pure_star_spec hMin huniq ha_lt ha_and hanej
    by_cases hai : a = i
    · subst hai; exact hi_below
    · exact below_of_mem_T hMin (by rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hai, haA⟩)
  let ctr : ℕ → Fin 26 := fun a => if h : a ∈ Anj then (hAnj_spec a h).choose else 0
  let sfn : ℕ → Fin 2 := fun a => if h : a ∈ Anj then (hAnj_spec a h).choose_spec.choose else 0
  let wire : ℕ → ℕ := fun a => opnd C a (sfn a)
  have hW_lt : ∀ a ∈ Anj, wire a < 26 + C.gates.length := by
    intro a ha
    have ha_lt := (mem_A_gates.mp (Finset.mem_erase.mp ha).2).1
    have := opnd_lt hAO ha_lt (sfn a)
    dsimp only [wire]; omega
  have hW_sub : ∀ a ∈ Anj, orIn 26 C (wire a) ⊆ nbrs (ctr a) := by
    intro a ha
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAnj_spec a ha).choose_spec.choose_spec.2.1
  have hW_pure : ∀ a ∈ Anj, ∀ h, OrReaches 26 C (wire a) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i := by
    intro a ha h hhr hhor
    obtain ⟨hanej, haA⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp haA
    exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq ha_lt ha_and hanej (sfn a) hhr hhor
  have hcov_Anj : ∀ a ∈ Anj, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
    intro a ha e he hga
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAnj_spec a ha).choose_spec.choose_spec.2.2.2 e he hga
  -- Analyze (side j 0, side j 1)
  set Aj := side (n := 26) C j 0
  set Bj := side (n := 26) C j 1
  have hAB_adj : ∀ u ∈ Aj, ∀ v ∈ Bj, pgAdj u v = true := by
    intro u hu v hv
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true :=
        (j_eval hMin hj hjand huniq _).mpr ⟨Or.inr ⟨u, hu, by simp [pairInput]⟩, Or.inr ⟨v, hv, by simp [pairInput]⟩⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  -- Note: opnd j 0 ≠ 26 + i and opnd j 1 ≠ 26 + i (else j(x) = i(x), contradicting minimality!)
  have hop_ne_i : ∀ s : Fin 2, opnd C j s ≠ 26 + i := by
    intro s heq
    have hilt : 26 + i < 26 + j := by have := opnd_lt hAO hj s; omega
    apply min_no_eq_wire hMin hj hilt
    intro x
    apply Bool.eq_iff_iff.mpr
    change gateVal 26 C j x = true ↔ gateVal 26 C i x = true
    rw [j_eval hMin hj hjand huniq x]
    fin_cases s
    · have heq0 : opnd C j 0 = 26 + i := heq
      have hemp : side (n := 26) C j 0 = ∅ := by
        change orIn 26 C (opnd C j 0) = ∅; rw [heq0]; exact orIn_gate_and C hi hiand
      simp only [hemp, Finset.notMem_empty, false_and, exists_false, or_false, hr0, hr1, true_and]
      tauto
    · have heq1 : opnd C j 1 = 26 + i := heq
      have hemp : side (n := 26) C j 1 = ∅ := by
        change orIn 26 C (opnd C j 1) = ∅; rw [heq1]; exact orIn_gate_and C hi hiand
      simp only [hemp, Finset.notMem_empty, false_and, exists_false, or_false, hr0, hr1, true_and]
      tauto
  -- Both opnd j 0 and opnd j 1 are distinct gates in O_extra!
  have hop_extra : ∀ s : Fin 2, ∃ h ∈ O_extra C i, opnd C j s = 26 + h := by
    intro s
    have hri_s : OrReaches 26 C (opnd C j s) i := by fin_cases s <;> assumption
    have h26 := hri_s.1
    have hlt := opnd_lt hAO hj s
    set h := opnd C j s - 26
    have hh_lt : h < C.gates.length := by omega
    have hwh : opnd C j s = 26 + h := by omega
    have hhor : (gateAt C h).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
      · exfalso
        rw [hwh, orReaches_gate_iff 26 C hh_lt i] at hri_s
        rcases hri_s with rfl | ⟨hor', _⟩
        · exact hop_ne_i s hwh
        · rw [hand] at hor'; cases hor'
      · exact hor
    have hhN := opnd_or_in_ON hMin huniq hj hjand s (by rw [hwh]; exact orReaches_self 26 C hh_lt) hhor
    refine ⟨h, ?_, hwh⟩
    unfold O_extra
    rw [Finset.mem_sdiff]
    refine ⟨hhN, fun hbi => ?_⟩
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp hbi
    exact (mem_O_pure.mp (Finset.mem_filter.mp hhc).1).2 (by rwa [← hwh])
  have hex_ge2 : 2 ≤ (O_extra C i).card := by
    obtain ⟨h0, hh0, heq0⟩ := hop_extra 0
    obtain ⟨h1, hh1, heq1⟩ := hop_extra 1
    have hne : h0 ≠ h1 := by
      intro heq; apply min_opnd_ne hMin hj; rw [heq0, heq1, heq]
    have hsub : ({h0, h1} : Finset ℕ) ⊆ O_extra C i := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({h0, h1} : Finset ℕ).card := (Finset.card_pair hne).symm
      _ ≤ (O_extra C i).card := Finset.card_le_card hsub
  have hsize := size_eq_A_Oout_ON hAO
  have hoN := oN_card_eq hMin huniq
  by_cases hAB_ne : Aj.Nonempty ∧ Bj.Nonempty
  · -- Case 1b: (Aj, Bj) is a nonempty star!
    have hstar_j : ∃ (c0 : Fin 26) (s0 : Fin 2),
        side (n := 26) C j (1 - s0) = {c0} ∧ side (n := 26) C j s0 ⊆ nbrs c0 ∧
        ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
          gateVal 26 C i (pairInput e.1 e.2) = true ∨ e ∈ starEdgesOf c0 (side (n := 26) C j s0) := by
      rcases biclique_is_star hAB_adj with h0 | h1
      · have h0eq : Aj.card = 1 := le_antisymm h0 (Finset.card_pos.mpr hAB_ne.1)
        obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h0eq
        refine ⟨c0, 1, by simpa using hc0, fun v hv => (mem_nbrs_iff c0 v).mpr (hAB_adj c0 (by rw [hc0]; simp) v hv), ?_⟩
        intro e he hjt
        obtain ⟨hleft, hright⟩ := (j_eval hMin hj hjand huniq _).mp hjt
        rcases hleft with ⟨_, hit⟩ | ⟨u, hu, hup⟩
        · exact Or.inl hit
        · rcases hright with ⟨_, hit⟩ | ⟨v, hv, hvp⟩
          · exact Or.inl hit
          · right
            change u ∈ Aj at hu
            rw [hc0, Finset.mem_singleton] at hu; subst u
            simp only [pairInput, decide_eq_true_eq] at hup hvp
            have hne_cv : c0 ≠ v := fun heq => by
              subst heq; have := hAB_adj c0 (by rw [hc0]; simp) c0 hv; rw [pgAdj_irrefl] at this; cases this
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hup with h1c | h2c <;> rcases hvp with h1' | h2'
            · exact (hne_cv (h1c.trans h1'.symm)).elim
            · rw [← h1c, ← h2']; exact mem_starEdgesOf_left hv
            · rw [← h1', ← h2c] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hv
            · exact (hne_cv (h2c.trans h2'.symm)).elim
      · have h1eq : Bj.card = 1 := le_antisymm h1 (Finset.card_pos.mpr hAB_ne.2)
        obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h1eq
        refine ⟨c0, 0, by simpa using hc0, fun u hu => (mem_nbrs_iff c0 u).mpr (by rw [pgAdj_symm]; exact hAB_adj u hu c0 (by rw [hc0]; simp)), ?_⟩
        intro e he hjt
        obtain ⟨hleft, hright⟩ := (j_eval hMin hj hjand huniq _).mp hjt
        rcases hleft with ⟨_, hit⟩ | ⟨u, hu, hup⟩
        · exact Or.inl hit
        · rcases hright with ⟨_, hit⟩ | ⟨v, hv, hvp⟩
          · exact Or.inl hit
          · right
            change v ∈ Bj at hv
            rw [hc0, Finset.mem_singleton] at hv; subst v
            simp only [pairInput, decide_eq_true_eq] at hup hvp
            have hne_uc : u ≠ c0 := fun heq => by
              subst heq; have := hAB_adj u hu u (by rw [hc0]; simp); rw [pgAdj_irrefl] at this; cases this
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hup with h1u | h2u <;> rcases hvp with h1' | h2'
            · exact (hne_uc (h1u.trans h1'.symm)).elim
            · rw [← h1u, ← h2'] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hu
            · rw [← h2u, ← h1']; exact mem_starEdgesOf_left hu
            · exact (hne_uc (h2u.trans h2'.symm)).elim
    obtain ⟨c0, s0, hs0_ctr, hs0_sub, hcov_j⟩ := hstar_j
    set L0 := side (n := 26) C j s0
    -- |A_gates| >= 13 since Anj + 1 star at (c0, L0) cover all 52 edges!
    have hA_ge13 : 13 ≤ (A_gates C).card := by
      have hsub : pgEdges ⊆ Anj.biUnion (fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))) ∪ starEdgesOf c0 L0 := by
        intro e he
        obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
        by_cases haj : a = j
        · subst haj
          rcases hcov_j e he hga with hit | hej
          · apply Finset.mem_union_left
            have hiAnj : i ∈ Anj := Finset.mem_erase.mpr ⟨hij_ne, mem_A_gates.mpr ⟨hi, hiand⟩⟩
            exact Finset.mem_biUnion.mpr ⟨i, hiAnj, hcov_Anj i hiAnj e he hit⟩
          · exact Finset.mem_union_right _ hej
        · apply Finset.mem_union_left
          have haAnj : a ∈ Anj := Finset.mem_erase.mpr ⟨haj, (Finset.mem_erase.mp (hT_eq ▸ haT)).2⟩
          exact Finset.mem_biUnion.mpr ⟨a, haAnj, hcov_Anj a haAnj e he hga⟩
      have h1 : 52 ≤ (Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))).card + (starEdgesOf c0 L0).card := by
        calc 52 = pgEdges.card := pgEdges_card.symm
          _ ≤ _ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 : (Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))).card ≤ 4 * Anj.card := by
        calc _ ≤ ∑ a ∈ Anj, (starEdgesOf (ctr a) (orIn 26 C (wire a))).card := Finset.card_biUnion_le
          _ ≤ ∑ _a ∈ Anj, 4 := Finset.sum_le_sum fun a ha => starEdgesOf_card_le_four (hW_sub a ha)
          _ = 4 * Anj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have h3 : (starEdgesOf c0 L0).card ≤ 4 := starEdgesOf_card_le_four hs0_sub
      omega
    -- Apply one_mixed_center_bound with bonus = 2, extra_r = 1!
    have hmb : 52 + 2 ≤ (O_N C).card + Anj.card + 1 := by
      apply one_mixed_center_bound hMin huniq Anj ctr wire hW_lt hW_sub hW_pure c0 L0 2 1
      · intro e he
        obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
        by_cases haj : a = j
        · subst haj
          rcases hcov_j e he hga with hit | hej
          · left
            have hiAnj : i ∈ Anj := Finset.mem_erase.mpr ⟨hij_ne, mem_A_gates.mpr ⟨hi, hiand⟩⟩
            exact ⟨i, hiAnj, hcov_Anj i hiAnj e he hit⟩
          · exact Or.inr hej
        · left
          have haAnj : a ∈ Anj := Finset.mem_erase.mpr ⟨haj, (Finset.mem_erase.mp (hT_eq ▸ haT)).2⟩
          exact ⟨a, haAnj, hcov_Anj a haAnj e he hga⟩
      · -- Center c0 bound: (U0 ∪ L0).card + 2 ≤ |O_c c0| + |O_extra| + r_c0 + 1
        set Anj0 := Anj.filter fun a => ctr a = c0
        set W0 := Anj0.image wire
        set U0 := W0.biUnion (orIn 26 C) ∪ L0
        have hU0_nbr : U0 ⊆ nbrs c0 := Finset.union_subset (by
          intro v hv
          obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨haAnj, hac⟩ := Finset.mem_filter.mp ha
          rw [← hac]; exact hW_sub a haAnj hvw) hs0_sub
        set Lmix : Finset (Option (Fin 26)) := U0.image some ∪ {some c0, none}
        have hLmix_card : Lmix.card = U0.card + 2 := by
          have hc0_not : c0 ∉ U0 := fun hmem => by
            have := (mem_nbrs_iff c0 c0).mp (hU0_nbr hmem); rw [pgAdj_irrefl] at this; cases this
          have hdisj : Disjoint (U0.image some) ({some c0, none} : Finset (Option (Fin 26))) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx1
            simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, reduceCtorEq, or_false] at hx2
            exact hc0_not (hx2 ▸ hu)
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (Option.some_injective (Fin 26)),
            Finset.card_pair (by simp)]
        set Wall := W0 ∪ {opnd C j 0, opnd C j 1}
        obtain ⟨E, hElen, hconn⟩ := mixed_center_conn hMin (j := j) hi hiand c0 Lmix
          (Finset.union_subset_union_left (Finset.image_subset_image hU0_nbr))
          Wall
          (fun w hw => by
            rcases Finset.mem_union.mp hw with hw0 | hwj
            · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
              exact hW_lt a (Finset.mem_filter.mp ha).1
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hwj
              rcases hwj with rfl | rfl
              · have := opnd_lt hAO hj 0; omega
              · have := opnd_lt hAO hj 1; omega)
          (fun w hw h hwr hor => by
            rcases Finset.mem_union.mp hw with hw0 | hwj
            · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
              exact (mem_O_pure.mp (hW_pure a (Finset.mem_filter.mp ha).1 h hwr hor)).1
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hwj
              rcases hwj with rfl | rfl
              · exact opnd_or_in_ON hMin huniq hj hjand 0 hwr hor
              · exact opnd_or_in_ON hMin huniq hj hjand 1 hwr hor)
        let W0ne := W0.filter fun w => (orIn 26 C w).Nonempty
        let R0 : Finset (Option (Fin 26)) := W0ne.attach.image fun w => some (Finset.mem_filter.mp w.2).2.choose
        let R : Finset (Option (Fin 26)) := insert none R0
        have hR_card : R.card ≤ Anj0.card + 1 := by
          have h1 : R0.card ≤ W0.card := Finset.card_image_le.trans
            (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
          have h2 : W0.card ≤ Anj0.card := Finset.card_image_le
          have h3 : R.card ≤ R0.card + 1 := Finset.card_insert_le _ _
          omega
        have hr_s0 : OrReaches 26 C (opnd C j s0) i := by fin_cases s0 <;> assumption
        have hr_1s0 : OrReaches 26 C (opnd C j (1 - s0)) i := by fin_cases s0 <;> assumption
        have hmem_s0 : opnd C j s0 ∈ Wall := by
          apply Finset.mem_union_right; fin_cases s0 <;> simp
        have hmem_1s0 : opnd C j (1 - s0) ∈ Wall := by
          apply Finset.mem_union_right; fin_cases s0 <;> simp
        have hnone_L : (none : Option (Fin 26)) ∈ Lmix := by simp [Lmix]
        have hcov_R : ∀ x ∈ Lmix, ∃ r ∈ R, EdgeReach E x r := by
          intro x hx
          rcases Finset.mem_union.mp hx with hxu | hx2
          · obtain ⟨u, huU0, rfl⟩ := Finset.mem_image.mp hxu
            rcases Finset.mem_union.mp huU0 with huW | huL0
            · obtain ⟨w, hwW0, huw⟩ := Finset.mem_biUnion.mp huW
              have hwne : w ∈ W0ne := Finset.mem_filter.mpr ⟨hwW0, ⟨u, huw⟩⟩
              let r0 := (Finset.mem_filter.mp hwne).2.choose
              have hr0_w : r0 ∈ orIn 26 C w := (Finset.mem_filter.mp hwne).2.choose_spec
              have hr0_U0 : r0 ∈ U0 := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w, hwW0, hr0_w⟩)
              refine ⟨some r0, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩), ?_⟩
              apply hconn w (Finset.mem_union_left _ hwW0)
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huw, rfl⟩), hx⟩
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, hr0_w, rfl⟩),
                  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, hr0_U0, rfl⟩)⟩
            · refine ⟨none, Finset.mem_insert_self _ _, ?_⟩
              apply hconn (opnd C j s0) hmem_s0
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huL0, rfl⟩), hx⟩
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (by simp [hr_s0]), hnone_L⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
            rcases hx2 with rfl | rfl
            · refine ⟨none, Finset.mem_insert_self _ _, ?_⟩
              apply hconn (opnd C j (1 - s0)) hmem_1s0
              · have hc0_mem : c0 ∈ orIn 26 C (opnd C j (1 - s0)) := by
                  change c0 ∈ side (n := 26) C j (1 - s0); rw [hs0_ctr]; simp
                exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c0, hc0_mem, rfl⟩), hx⟩
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (by simp [hr_1s0]), hnone_L⟩
            · exact ⟨none, Finset.mem_insert_self _ _, Relation.ReflTransGen.refl⟩
        have hb := graph_spanning_bound E Lmix R hcov_R
        rw [hLmix_card] at hb
        rw [oC_disj_oExtra] at hElen
        omega
    change 64 ≤ C.gates.length
    omega
  · -- Case 1a: Aj = ∅ or Bj = ∅! So Anj (size |A| - 1) covers ALL 52 edges!
    have hcov_all : ∀ e ∈ pgEdges, ∃ a ∈ Anj, e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
      intro e he
      obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
      by_cases haj : a = j
      · subst haj
        obtain ⟨hleft, hright⟩ := (j_eval hMin hj hjand huniq _).mp hga
        have hit : gateVal 26 C i (pairInput e.1 e.2) = true := by
          by_cases hAj : Aj.Nonempty
          · have hBj : Bj = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h => hAB_ne ⟨hAj, h⟩
            rcases hright with ⟨_, h⟩ | ⟨v, hv, _⟩
            · exact h
            · change v ∈ Bj at hv; rw [hBj] at hv; exact (Finset.notMem_empty v hv).elim
          · have hAj' : Aj = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAj
            rcases hleft with ⟨_, h⟩ | ⟨u, hu, _⟩
            · exact h
            · change u ∈ Aj at hu; rw [hAj'] at hu; exact (Finset.notMem_empty u hu).elim
        have hiAnj : i ∈ Anj := Finset.mem_erase.mpr ⟨hij_ne, mem_A_gates.mpr ⟨hi, hiand⟩⟩
        exact ⟨i, hiAnj, hcov_Anj i hiAnj e he hit⟩
      · have haAnj : a ∈ Anj := Finset.mem_erase.mpr ⟨haj, (Finset.mem_erase.mp (hT_eq ▸ haT)).2⟩
        exact ⟨a, haAnj, hcov_Anj a haAnj e he hga⟩
    have hA_ge14 : 14 ≤ (A_gates C).card := by
      have hsub : pgEdges ⊆ Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
        intro e he; obtain ⟨a, ha, hmem⟩ := hcov_all e he
        exact Finset.mem_biUnion.mpr ⟨a, ha, hmem⟩
      have h52 : 52 ≤ 4 * Anj.card := by
        calc 52 = pgEdges.card := pgEdges_card.symm
          _ ≤ (Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))).card := Finset.card_le_card hsub
          _ ≤ ∑ a ∈ Anj, (starEdgesOf (ctr a) (orIn 26 C (wire a))).card := Finset.card_biUnion_le
          _ ≤ ∑ _a ∈ Anj, 4 := Finset.sum_le_sum fun a ha => starEdgesOf_card_le_four (hW_sub a ha)
          _ = 4 * Anj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have hpf := pure_family_sum_bound hMin huniq Anj ctr wire hW_lt hW_sub hW_pure hcov_all
    change 64 ≤ C.gates.length
    omega

-- Helper for Case 2, Subcase 2.2 (E1 nonempty, E2 nonempty, E3 empty, |Bj| >= 2, |Ai ∩ Bj| = 1)
lemma case2_sub22 {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (hOout_ge : (A_gates C).card ≤ (O_out C).card + 2)
    (b : Fin 2) (hb_r : OrReaches 26 C (opnd C j b) i) (hnb_r : ¬ OrReaches 26 C (opnd C j (1 - b)) i)
    (Astar : Finset ℕ) (hAstar : Astar = ((A_gates C).erase i).erase j)
    (ctr : ℕ → Fin 26) (wire : ℕ → ℕ)
    (hW_lt : ∀ a ∈ Astar, wire a < 26 + C.gates.length)
    (hW_sub : ∀ a ∈ Astar, orIn 26 C (wire a) ⊆ nbrs (ctr a))
    (hW_pure : ∀ a ∈ Astar, ∀ h, OrReaches 26 C (wire a) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i)
    (hcov_Astar : ∀ a ∈ Astar, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)))
    (si : Fin 2) (c1 c2 : Fin 26)
    (hc1_mem : c1 ∈ side (n := 26) C j b ∪ (side (n := 26) C i si ∩ side (n := 26) C i (1 - si)))
    (hc2_mem : c2 ∈ side (n := 26) C i si ∩ side (n := 26) C j (1 - b))
    (hBj_sub : side (n := 26) C j (1 - b) ⊆ nbrs c1)
    (hBi_sub : side (n := 26) C i (1 - si) ⊆ nbrs c2)
    (hcov_j : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf c1 (side (n := 26) C j (1 - b)) ∪ starEdgesOf c2 (side (n := 26) C i (1 - si))) :
    64 ≤ C.size := by
  have hAO := min_isAO2 hMin
  have hAstar_card : Astar.card = (A_gates C).card - 2 := by
    rw [hAstar, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩),
      Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hi, hiand⟩)]
    omega
  -- |Ej| ≤ 7!
  have hEj_le7 : (starEdgesOf c1 (side (n := 26) C j (1 - b)) ∪
      starEdgesOf c2 (side (n := 26) C i (1 - si))).card ≤ 7 := by
    have hadj12 : pgAdj c1 c2 = true := (mem_nbrs_iff c1 c2).mp (hBj_sub (Finset.mem_inter.mp hc2_mem).2)
    by_cases hc1_in : c1 ∈ side (n := 26) C i (1 - si)
    · have hsh : dirEdge c1 c2 ∈ starEdgesOf c1 (side (n := 26) C j (1 - b)) ∩
          starEdgesOf c2 (side (n := 26) C i (1 - si)) := by
        refine Finset.mem_inter.mpr ⟨mem_starEdgesOf_left (Finset.mem_inter.mp hc2_mem).2, ?_⟩
        exact mem_starEdgesOf_right hadj12 hc1_in
      have hinter_pos : 1 ≤ (starEdgesOf c1 (side (n := 26) C j (1 - b)) ∩
          starEdgesOf c2 (side (n := 26) C i (1 - si))).card := Finset.card_pos.mpr ⟨_, hsh⟩
      have hu := Finset.card_union_add_card_inter (starEdgesOf c1 (side (n := 26) C j (1 - b)))
        (starEdgesOf c2 (side (n := 26) C i (1 - si)))
      have h4a := starEdgesOf_card_le_four hBj_sub
      have h4b := starEdgesOf_card_le_four hBi_sub
      omega
    · have hsub_er : side (n := 26) C i (1 - si) ⊆ (nbrs c2).erase c1 := by
        intro v hv
        exact Finset.mem_erase.mpr ⟨fun heq => hc1_in (heq ▸ hv), hBi_sub hv⟩
      have hc1_nbr : c1 ∈ nbrs c2 := (mem_nbrs_iff c2 c1).mpr (by rw [pgAdj_symm]; exact hadj12)
      have h3 : (side (n := 26) C i (1 - si)).card ≤ 3 := by
        have := Finset.card_le_card hsub_er
        rw [Finset.card_erase_of_mem hc1_nbr, nbrs_card c2] at this; omega
      have h4a := starEdgesOf_card_le_four hBj_sub
      have hu := Finset.card_union_le (starEdgesOf c1 (side (n := 26) C j (1 - b)))
        (starEdgesOf c2 (side (n := 26) C i (1 - si)))
      rw [starEdgesOf_card c2] at hu
      omega
  have h52 := aGates_card_of_j_edges hMin hi hj hiand hjand hij_ne hT_eq Astar hAstar
    ctr (fun a => orIn 26 C (wire a))
    (fun a ha => (Finset.card_le_card (hW_sub a ha)).trans (nbrs_card _).le)
    hcov_Astar _ hcov_j
  have hA_ge14 : 14 ≤ (A_gates C).card := by omega
  -- Extra gate in O_extra!
  have hex_ge1 : 1 ≤ (O_extra C i).card := by
    rcases Finset.mem_union.mp hc1_mem with hc1Aj | hc1AiBi
    · apply extra_of_reaches_i_and_input hMin hiand (w := opnd C j b) (by have := opnd_lt hAO hj b; omega)
        hb_r ⟨c1, hc1Aj⟩
      intro h hhr hor; exact opnd_or_in_ON hMin huniq hj hjand b hhr hor
    · have hadj12 : pgAdj c1 c2 = true := (mem_nbrs_iff c1 c2).mp (hBj_sub (Finset.mem_inter.mp hc2_mem).2)
      apply extra_of_mixed_bipartite hMin (w := opnd C i si) (by have := opnd_lt hAO hi si; omega)
        (fun h hhr hor => opnd_or_in_ON hMin huniq hi hiand si hhr hor)
        (Finset.mem_inter.mp hc1AiBi).1 (Finset.mem_inter.mp hc2_mem).1 (pgAdj_bip c1 c2 hadj12)
  -- Add 2 fresh indices (i and j!) to Astar to form A_gates C!
  have hi_notA : i ∉ Astar := by rw [hAstar]; simp
  have hj_notA : j ∉ Astar := by rw [hAstar]; simp
  set Idx := insert i (insert j Astar)
  have hIdx_card : Idx.card = (A_gates C).card := by
    have heq : Idx = A_gates C := by
      ext x
      simp only [Idx, hAstar, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | rfl | ⟨_, _, hx⟩)
        · exact mem_A_gates.mpr ⟨hi, hiand⟩
        · exact mem_A_gates.mpr ⟨hj, hjand⟩
        · exact hx
      · intro hx
        by_cases hxi : x = i
        · exact Or.inl hxi
        · by_cases hxj : x = j
          · exact Or.inr (Or.inl hxj)
          · exact Or.inr (Or.inr ⟨hxj, hxi, hx⟩)
    rw [heq]
  let ctr' : ℕ → Fin 26 := fun k => if k = i then c2 else if k = j then c1 else ctr k
  let wire' : ℕ → ℕ := fun k => if k = i then opnd C i (1 - si) else if k = j then opnd C j (1 - b) else wire k
  have hpf : 52 ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
    apply pure_family_sum_bound hMin huniq Idx ctr' wire'
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · simp only [wire', ↓reduceIte]; have := opnd_lt hAO hi (1 - si); omega
      · rcases Finset.mem_insert.mp hk1 with rfl | hkA
        · simp only [wire', hij_ne.symm, ↓reduceIte]; have := opnd_lt hAO hj (1 - b); omega
        · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
          have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
          simp only [wire', hki, hkj, ↓reduceIte]; exact hW_lt k hkA
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · simp only [wire', ctr', ↓reduceIte]; exact hBi_sub
      · rcases Finset.mem_insert.mp hk1 with rfl | hkA
        · simp only [wire', ctr', hij_ne.symm, ↓reduceIte]; exact hBj_sub
        · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
          have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
          simp only [wire', ctr', hki, hkj, ↓reduceIte]; exact hW_sub k hkA
    · intro k hk h hhr hor
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · simp only [wire', ↓reduceIte] at hhr
        exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq hi hiand hij_ne (1 - si) hhr hor
      · rcases Finset.mem_insert.mp hk1 with rfl | hkA
        · simp only [wire', hij_ne.symm, ↓reduceIte] at hhr
          exact opnd_or_in_Opure_of_not_reach_i hMin huniq hj hjand (1 - b) hnb_r hhr hor
        · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
          have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
          simp only [wire', hki, hkj, ↓reduceIte] at hhr
          exact hW_pure k hkA h hhr hor
    · intro e he
      obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
      by_cases haj : a = j
      · subst a
        rcases Finset.mem_union.mp (hcov_j e he hga) with he1 | he2
        · refine ⟨j, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
          simp only [ctr', wire', hij_ne.symm, ↓reduceIte]; exact he1
        · refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
          simp only [ctr', wire', ↓reduceIte]; exact he2
      · have haA : a ∈ Astar := by rw [hAstar, Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
        have hai : a ≠ i := fun h => hi_notA (h ▸ haA)
        refine ⟨a, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haA), ?_⟩
        simp only [ctr', wire', hai, haj, ↓reduceIte]
        exact hcov_Astar a haA e he hga
  have hsize := size_eq_A_Oout_ON hAO
  have hoN := oN_card_eq hMin huniq
  change 64 ≤ C.gates.length
  omega

-- Case 2: Exactly one operand b of j reaches i
lemma case_one_reach {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (hOout_ge : (A_gates C).card ≤ (O_out C).card + 2)
    (b : Fin 2) (hb_r : OrReaches 26 C (opnd C j b) i) (hnb_r : ¬ OrReaches 26 C (opnd C j (1 - b)) i) :
    64 ≤ C.size := by
  classical
  have hAO := min_isAO2 hMin
  have hjT : j ∈ T_gates C := by
    rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩
  have hj_below := below_of_mem_T hMin hjT
  -- Set up pure stars for Astar = (A_gates \ {i, j})
  set Astar := ((A_gates C).erase i).erase j
  have hAstar_card : Astar.card = (A_gates C).card - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩),
      Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hi, hiand⟩)]
    omega
  have hAstar_spec : ∀ a ∈ Astar, ∃ (c : Fin 26) (s : Fin 2),
      side (n := 26) C a (1 - s) = {c} ∧ side (n := 26) C a s ⊆ nbrs c ∧
      (side (n := 26) C a s).Nonempty ∧
      ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
        e ∈ starEdgesOf c (side (n := 26) C a s) := by
    intro a ha
    obtain ⟨hanej, haei⟩ := Finset.mem_erase.mp ha
    obtain ⟨hanei, haA⟩ := Finset.mem_erase.mp haei
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp haA
    exact pure_star_spec hMin huniq ha_lt ha_and hanej
      (below_of_mem_T hMin (by rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hanei, haA⟩))
  let ctr : ℕ → Fin 26 := fun a => if h : a ∈ Astar then (hAstar_spec a h).choose else 0
  let sfn : ℕ → Fin 2 := fun a => if h : a ∈ Astar then (hAstar_spec a h).choose_spec.choose else 0
  let wire : ℕ → ℕ := fun a => opnd C a (sfn a)
  have hW_lt : ∀ a ∈ Astar, wire a < 26 + C.gates.length := by
    intro a ha
    have ha_lt := (mem_A_gates.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2).1
    have := opnd_lt hAO ha_lt (sfn a)
    dsimp only [wire]; omega
  have hW_sub : ∀ a ∈ Astar, orIn 26 C (wire a) ⊆ nbrs (ctr a) := by
    intro a ha
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAstar_spec a ha).choose_spec.choose_spec.2.1
  have hW_pure : ∀ a ∈ Astar, ∀ h, OrReaches 26 C (wire a) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i := by
    intro a ha h hhr hhor
    obtain ⟨hanej, haei⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp (Finset.mem_erase.mp haei).2
    exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq ha_lt ha_and hanej (sfn a) hhr hhor
  have hcov_Astar : ∀ a ∈ Astar, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
    intro a ha e he hga
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAstar_spec a ha).choose_spec.choose_spec.2.2.2 e he hga
  -- Analyze j's evaluation
  set Aj := side (n := 26) C j b
  set Bj := side (n := 26) C j (1 - b)
  set Ai := side (n := 26) C i 0
  set Bi := side (n := 26) C i 1
  set C1 := Aj ∪ (Ai ∩ Bi)
  have hj_ev : ∀ x : Fin 26 → Bool, gateVal 26 C j x = true ↔
      (((∃ u ∈ Ai, x u = true) ∧ (∃ v ∈ Bi, x v = true)) ∨ ∃ u ∈ Aj, x u = true) ∧
      ∃ v ∈ Bj, x v = true := by
    intro x
    rw [j_eval hMin hj hjand huniq x, pure_and_eval hMin huniq hi hiand hij_ne x]
    fin_cases b
    · have h0r : OrReaches 26 C (opnd C j 0) i := hb_r
      have h1r : ¬ OrReaches 26 C (opnd C j 1) i := hnb_r
      change (((OrReaches 26 C (opnd C j 0) i ∧ _) ∨ _) ∧ ((OrReaches 26 C (opnd C j 1) i ∧ _) ∨ _)) ↔ _
      simp only [Aj, Bj, Ai, Bi, h0r, h1r, true_and, false_and, false_or, Fin.isValue]
      rfl
    · have h1r : OrReaches 26 C (opnd C j 1) i := hb_r
      have h0r : ¬ OrReaches 26 C (opnd C j 0) i := hnb_r
      have hsub1 : (1 : Fin 2) - 1 = 0 := rfl
      simp only [Aj, Bj, Ai, Bi, h0r, h1r, hsub1, true_and, false_and, false_or, Fin.isValue]
      exact and_comm
  have hE1 : ∀ u ∈ C1, ∀ v ∈ Bj, pgAdj u v = true := by
    intro u hu v hv
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true := by
        rw [hj_ev]
        refine ⟨?_, v, hv, by simp [pairInput]⟩
        rcases Finset.mem_union.mp hu with huAj | huAB
        · exact Or.inr ⟨u, huAj, by simp [pairInput]⟩
        · obtain ⟨huA, huB⟩ := Finset.mem_inter.mp huAB
          exact Or.inl ⟨⟨u, huA, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  have hE2 : ∀ u ∈ Ai ∩ Bj, ∀ v ∈ Bi, pgAdj u v = true := by
    intro u hu v hv
    obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true := by
        rw [hj_ev]
        exact ⟨Or.inl ⟨⟨u, huA, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩,
          u, huB, by simp [pairInput]⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  have hE3 : ∀ u ∈ Bi ∩ Bj, ∀ v ∈ Ai, pgAdj u v = true := by
    intro u hu v hv
    obtain ⟨huB, huBj⟩ := Finset.mem_inter.mp hu
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true := by
        rw [hj_ev]
        exact ⟨Or.inl ⟨⟨v, hv, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩,
          u, huBj, by simp [pairInput]⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  have hEdge_split : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
      (e.1 ∈ C1 ∧ e.2 ∈ Bj) ∨ (e.2 ∈ C1 ∧ e.1 ∈ Bj) ∨
      (e.1 ∈ Ai ∩ Bj ∧ e.2 ∈ Bi) ∨ (e.2 ∈ Ai ∩ Bj ∧ e.1 ∈ Bi) ∨
      (e.1 ∈ Bi ∩ Bj ∧ e.2 ∈ Ai) ∨ (e.2 ∈ Bi ∩ Bj ∧ e.1 ∈ Ai) := by
    intro e he hjt
    rw [hj_ev] at hjt
    obtain ⟨hL, w, hwBj, hwp⟩ := hjt
    simp only [pairInput, decide_eq_true_eq] at hwp
    have hnot_self : ∀ z ∈ Bj, z ∉ C1 := fun z hzB hzC => by
      have := hE1 z hzC z hzB; rw [pgAdj_irrefl] at this; cases this
    have hnot_i_self : ∀ z ∈ Bj, ¬ (z ∈ Ai ∧ z ∈ Bi) := fun z hzB h =>
      hnot_self z hzB (Finset.mem_union_right _ (Finset.mem_inter.mpr h))
    rcases hwp with rfl | rfl
    · rcases hL with ⟨⟨u, huA, hup⟩, ⟨v, hvB, hvp⟩⟩ | ⟨u, huAj, hup⟩
      · simp only [pairInput, decide_eq_true_eq] at hup hvp
        rcases hup with rfl | rfl <;> rcases hvp with h1 | h2
        · exact (hnot_i_self e.1 hwBj ⟨huA, h1 ▸ hvB⟩).elim
        · subst h2; exact Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨huA, hwBj⟩, hvB⟩))
        · subst h1; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨hvB, hwBj⟩, huA⟩))))
        · subst h2; exact Or.inr (Or.inl ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huA, hvB⟩), hwBj⟩)
      · simp only [pairInput, decide_eq_true_eq] at hup
        rcases hup with rfl | rfl
        · exact (hnot_self e.1 hwBj (Finset.mem_union_left _ huAj)).elim
        · exact Or.inr (Or.inl ⟨Finset.mem_union_left _ huAj, hwBj⟩)
    · rcases hL with ⟨⟨u, huA, hup⟩, ⟨v, hvB, hvp⟩⟩ | ⟨u, huAj, hup⟩
      · simp only [pairInput, decide_eq_true_eq] at hup hvp
        rcases hup with rfl | rfl <;> rcases hvp with h1 | h2
        · subst h1; exact Or.inl ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huA, hvB⟩), hwBj⟩
        · subst h2; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Finset.mem_inter.mpr ⟨hvB, hwBj⟩, huA⟩))))
        · subst h1; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨huA, hwBj⟩, hvB⟩)))
        · exact (hnot_i_self e.2 hwBj ⟨huA, h2 ▸ hvB⟩).elim
      · simp only [pairInput, decide_eq_true_eq] at hup
        rcases hup with rfl | rfl
        · exact Or.inl ⟨Finset.mem_union_left _ huAj, hwBj⟩
        · exact (hnot_self e.2 hwBj (Finset.mem_union_left _ huAj)).elim
  -- Helper for Subcase 2.3: when j's covered edges lie in a SINGLE star (c0, L0) with L0 ⊆ nbrs c0!
  have hsingle_star : ∀ (c0 : Fin 26) (L0 : Finset (Fin 26)), L0 ⊆ nbrs c0 →
      (∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true → e ∈ starEdgesOf c0 L0) →
      (∀ v ∈ L0, gateVal 26 C j (pairInput c0 v) = true) →
      64 ≤ C.size := by
    intro c0 L0 hL0_sub hcov_j hL0_real
    have h52 := aGates_card_of_j_edges hMin hi hj hiand hjand hij_ne hT_eq Astar rfl
      ctr (fun a => orIn 26 C (wire a))
      (fun a ha => (Finset.card_le_card (hW_sub a ha)).trans (nbrs_card _).le)
      hcov_Astar (starEdgesOf c0 L0) hcov_j
    have hL0_le4 : (starEdgesOf c0 L0).card ≤ 4 := starEdgesOf_card_le_four hL0_sub
    have hA_ge14 : 14 ≤ (A_gates C).card := by omega
    have hsize := size_eq_A_Oout_ON hAO
    -- Case A: L0 ⊆ orIn w0 for some wire w0 (all OR gates in O_N)
    have hsub_single_wire : ∀ w0 < 26 + C.gates.length,
        (∀ h, OrReaches 26 C w0 h → (gateAt C h).op = GateOp.or → h ∈ O_N C) →
        L0 ⊆ orIn 26 C w0 → 64 ≤ C.size := by
      intro w0 hw0_lt hw0_oN hL0_w0
      have hmb : 52 + 0 ≤ (O_N C).card + Astar.card + 1 := by
        apply one_mixed_center_bound hMin huniq Astar ctr wire hW_lt hW_sub hW_pure c0 L0 0 1
        · intro e he
          obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
          by_cases haj : a = j
          · subst haj; exact Or.inr (hcov_j e he hga)
          · left
            have haA : a ∈ Astar := by rw [Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
            exact ⟨a, haA, hcov_Astar a haA e he hga⟩
        · set A0 := Astar.filter fun a => ctr a = c0
          set W0 := A0.image wire
          set U0 := W0.biUnion (orIn 26 C) ∪ L0
          have hU0_nbr : U0 ⊆ nbrs c0 := Finset.union_subset (by
            intro v hv
            obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
            rw [← hac]; exact hW_sub a haA hvw) hL0_sub
          set Lmix : Finset (Option (Fin 26)) := U0.image some
          set Wall := insert w0 W0
          obtain ⟨E, hElen, hconn⟩ := mixed_center_conn hMin (j := j) hi hiand c0 Lmix
            (Finset.Subset.trans (Finset.image_subset_image hU0_nbr) Finset.subset_union_left)
            Wall
            (fun w hw => by
              rcases Finset.mem_insert.mp hw with rfl | hw0
              · exact hw0_lt
              · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                exact hW_lt a (Finset.mem_filter.mp ha).1)
            (fun w hw h hwr hor => by
              rcases Finset.mem_insert.mp hw with rfl | hw0
              · exact hw0_oN h hwr hor
              · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                exact (mem_O_pure.mp (hW_pure a (Finset.mem_filter.mp ha).1 h hwr hor)).1)
          let Wne := Wall.filter fun w => (fMix C i w ∩ Lmix).Nonempty
          let R : Finset (Option (Fin 26)) := Wne.attach.image fun w => (Finset.mem_filter.mp w.2).2.choose
          have hR_card : R.card ≤ A0.card + 1 := by
            have h1 : R.card ≤ Wall.card := Finset.card_image_le.trans
              (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
            have h2 : Wall.card ≤ W0.card + 1 := Finset.card_insert_le _ _
            have h3 : W0.card ≤ A0.card := Finset.card_image_le
            omega
          have hcov_R : ∀ x ∈ Lmix, ∃ r ∈ R, EdgeReach E x r := by
            intro x hx
            obtain ⟨u, huU0, rfl⟩ := Finset.mem_image.mp hx
            have hex_w : ∃ w ∈ Wall, some u ∈ fMix C i w ∩ Lmix := by
              rcases Finset.mem_union.mp huU0 with huW | huL0
              · obtain ⟨w, hwW0, huw⟩ := Finset.mem_biUnion.mp huW
                exact ⟨w, Finset.mem_insert_of_mem hwW0,
                  Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huw, rfl⟩), hx⟩⟩
              · exact ⟨w0, Finset.mem_insert_self _ _,
                  Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hL0_w0 huL0, rfl⟩), hx⟩⟩
            obtain ⟨w, hwWall, huw⟩ := hex_w
            have hwne : w ∈ Wne := Finset.mem_filter.mpr ⟨hwWall, ⟨some u, huw⟩⟩
            let r := (Finset.mem_filter.mp hwne).2.choose
            have hr_spec := (Finset.mem_filter.mp hwne).2.choose_spec
            exact ⟨r, Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩,
              hconn w hwWall (some u) huw r hr_spec⟩
          have hb := graph_spanning_bound E Lmix R hcov_R
          rw [Finset.card_image_of_injective _ (Option.some_injective (Fin 26))] at hb
          rw [oC_disj_oExtra] at hElen
          omega
      change 64 ≤ C.gates.length
      omega
    -- Check whether c0 ∈ Bj!
    by_cases hc0Bj : c0 ∈ Bj
    · -- c0 ∈ Bj!
      have hc0_notAB : ¬ (c0 ∈ Ai ∧ c0 ∈ Bi) := fun h => by
        have := hE1 c0 (Finset.mem_union_right _ (Finset.mem_inter.mpr h)) c0 hc0Bj
        rw [pgAdj_irrefl] at this; cases this
      by_cases hLB : (L0 ∩ Bj).Nonempty
      · -- Some v0 ∈ L0 ∩ Bj! Then Bj has c0 and v0 ∈ nbrs c0 -> C1 = ∅!
        obtain ⟨v0, hv0⟩ := hLB
        obtain ⟨hv0L, hv0Bj⟩ := Finset.mem_inter.mp hv0
        have hC1_emp : C1 = ∅ := by
          ext z; simp only [Finset.notMem_empty, iff_false]
          intro hz
          have hb1 := pgAdj_bip z c0 (hE1 z hz c0 hc0Bj)
          have hb2 := pgAdj_bip z v0 (hE1 z hz v0 hv0Bj)
          have hb3 := pgAdj_bip c0 v0 ((mem_nbrs_iff c0 v0).mp (hL0_sub hv0L))
          tauto
        by_cases hc0Ai : c0 ∈ Ai
        · -- All v ∈ L0 must be in Bi!
          have hc0_notBi : c0 ∉ Bi := fun h => hc0_notAB ⟨hc0Ai, h⟩
          apply hsub_single_wire (opnd C i 1) (by have := opnd_lt hAO hi 1; omega)
            (fun h hhr hor => opnd_or_in_ON hMin huniq hi hiand 1 hhr hor)
          intro v hvL0
          have hadj_cv := (mem_nbrs_iff c0 v).mp (hL0_sub hvL0)
          have hjt := hL0_real v hvL0
          rw [hj_ev] at hjt
          obtain ⟨hL, _⟩ := hjt
          rcases hL with ⟨_, ⟨y, hyBi, hyp⟩⟩ | ⟨y, hyAj, _⟩
          · simp only [pairInput, decide_eq_true_eq] at hyp
            rcases hyp with rfl | rfl
            · exact (hc0_notBi hyBi).elim
            · exact hyBi
          · have : y ∈ C1 := Finset.mem_union_left _ hyAj
            rw [hC1_emp] at this; exact (Finset.notMem_empty y this).elim
        · -- c0 ∉ Ai, so all v ∈ L0 must be in Ai!
          apply hsub_single_wire (opnd C i 0) (by have := opnd_lt hAO hi 0; omega)
            (fun h hhr hor => opnd_or_in_ON hMin huniq hi hiand 0 hhr hor)
          intro v hvL0
          have hjt := hL0_real v hvL0
          rw [hj_ev] at hjt
          obtain ⟨hL, _⟩ := hjt
          rcases hL with ⟨⟨y, hyAi, hyp⟩, _⟩ | ⟨y, hyAj, _⟩
          · simp only [pairInput, decide_eq_true_eq] at hyp
            rcases hyp with rfl | rfl
            · exact (hc0Ai hyAi).elim
            · exact hyAi
          · have : y ∈ C1 := Finset.mem_union_left _ hyAj
            rw [hC1_emp] at this; exact (Finset.notMem_empty y this).elim
      · -- L0 ∩ Bj = ∅!
        set LA := L0 ∩ Aj
        set Li := L0 \ Aj
        have hLi_in_si : ∃ si : Fin 2, Li ⊆ side (n := 26) C i si := by
          by_cases hc0Ai : c0 ∈ Ai
          · refine ⟨1, fun v hv => ?_⟩
            obtain ⟨hvL0, hv_notAj⟩ := Finset.mem_sdiff.mp hv
            have hc0_notBi : c0 ∉ Bi := fun h => hc0_notAB ⟨hc0Ai, h⟩
            have hjt := hL0_real v hvL0
            rw [hj_ev] at hjt
            rcases hjt.1 with ⟨_, ⟨y, hyBi, hyp⟩⟩ | ⟨y, hyAj, hyp⟩
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with rfl | rfl
              · exact (hc0_notBi hyBi).elim
              · exact hyBi
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with heq | heq
              · rw [heq] at hyAj
                have := hE1 c0 (Finset.mem_union_left _ hyAj) c0 hc0Bj
                rw [pgAdj_irrefl] at this; cases this
              · rw [heq] at hyAj; exact (hv_notAj hyAj).elim
          · refine ⟨0, fun v hv => ?_⟩
            obtain ⟨hvL0, hv_notAj⟩ := Finset.mem_sdiff.mp hv
            have hjt := hL0_real v hvL0
            rw [hj_ev] at hjt
            rcases hjt.1 with ⟨⟨y, hyAi, hyp⟩, _⟩ | ⟨y, hyAj, hyp⟩
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with rfl | rfl
              · exact (hc0Ai hyAi).elim
              · exact hyAi
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with heq | heq
              · rw [heq] at hyAj
                have := hE1 c0 (Finset.mem_union_left _ hyAj) c0 hc0Bj
                rw [pgAdj_irrefl] at this; cases this
              · rw [heq] at hyAj; exact (hv_notAj hyAj).elim
        obtain ⟨si, hLi_sub⟩ := hLi_in_si
        by_cases hLi_ne : Li.Nonempty
        · -- Sub-subcase (β): Li nonempty! Use Lmix = insert none (U0.image some), R <= A0.card + 2!
          have hmb : 52 + 1 ≤ (O_N C).card + Astar.card + 2 := by
            apply one_mixed_center_bound hMin huniq Astar ctr wire hW_lt hW_sub hW_pure c0 L0 1 2
            · intro e he
              obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
              by_cases haj : a = j
              · subst haj; exact Or.inr (hcov_j e he hga)
              · left
                have haA : a ∈ Astar := by rw [Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
                exact ⟨a, haA, hcov_Astar a haA e he hga⟩
            · set A0 := Astar.filter fun a => ctr a = c0
              set W0 := A0.image wire
              set U0 := W0.biUnion (orIn 26 C) ∪ L0
              have hU0_nbr : U0 ⊆ nbrs c0 := Finset.union_subset (by
                intro v hv
                obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
                obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
                obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
                rw [← hac]; exact hW_sub a haA hvw) hL0_sub
              set Lmix : Finset (Option (Fin 26)) := insert none (U0.image some)
              have hLmix_card : Lmix.card = U0.card + 1 := by
                rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (Option.some_injective (Fin 26))]
              set Wall := insert (opnd C j b) (insert (opnd C i si) W0)
              obtain ⟨E, hElen, hconn⟩ := mixed_center_conn hMin (j := j) hi hiand c0 Lmix
                (by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with rfl | hxu
                  · simp
                  · exact Finset.mem_union_left _ (Finset.image_subset_image hU0_nbr hxu))
                Wall
                (fun w hw => by
                  rcases Finset.mem_insert.mp hw with rfl | hw1
                  · have := opnd_lt hAO hj b; omega
                  · rcases Finset.mem_insert.mp hw1 with rfl | hw0
                    · have := opnd_lt hAO hi si; omega
                    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                      exact hW_lt a (Finset.mem_filter.mp ha).1)
                (fun w hw h hwr hor => by
                  rcases Finset.mem_insert.mp hw with rfl | hw1
                  · exact opnd_or_in_ON hMin huniq hj hjand b hwr hor
                  · rcases Finset.mem_insert.mp hw1 with rfl | hw0
                    · exact opnd_or_in_ON hMin huniq hi hiand si hwr hor
                    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                      exact (mem_O_pure.mp (hW_pure a (Finset.mem_filter.mp ha).1 h hwr hor)).1)
              let W0ne := W0.filter fun w => (orIn 26 C w).Nonempty
              let R0 : Finset (Option (Fin 26)) := W0ne.attach.image fun w => some (Finset.mem_filter.mp w.2).2.choose
              let r_i : Fin 26 := hLi_ne.choose
              have hr_i_mem : r_i ∈ Li := hLi_ne.choose_spec
              let R : Finset (Option (Fin 26)) := insert none (insert (some r_i) R0)
              have hR_card : R.card ≤ A0.card + 2 := by
                have h1 : R0.card ≤ W0.card := Finset.card_image_le.trans
                  (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
                have h2 : W0.card ≤ A0.card := Finset.card_image_le
                have h3 : R.card ≤ (insert (some r_i) R0).card + 1 := Finset.card_insert_le _ _
                have h4 : (insert (some r_i) R0).card ≤ R0.card + 1 := Finset.card_insert_le _ _
                omega
              have hcov_R : ∀ x ∈ Lmix, ∃ r ∈ R, EdgeReach E x r := by
                intro x hx
                rcases Finset.mem_insert.mp hx with rfl | hxu
                · exact ⟨none, Finset.mem_insert_self _ _, Relation.ReflTransGen.refl⟩
                · obtain ⟨u, huU0, rfl⟩ := Finset.mem_image.mp hxu
                  rcases Finset.mem_union.mp huU0 with huW | huL0
                  · obtain ⟨w, hwW0, huw⟩ := Finset.mem_biUnion.mp huW
                    have hwne : w ∈ W0ne := Finset.mem_filter.mpr ⟨hwW0, ⟨u, huw⟩⟩
                    let r0 := (Finset.mem_filter.mp hwne).2.choose
                    have hr0_w : r0 ∈ orIn 26 C w := (Finset.mem_filter.mp hwne).2.choose_spec
                    have hr0_U0 : r0 ∈ U0 := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w, hwW0, hr0_w⟩)
                    refine ⟨some r0, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                      (Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩)), ?_⟩
                    apply hconn w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwW0))
                    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huw, rfl⟩), hx⟩
                    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, hr0_w, rfl⟩),
                        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r0, hr0_U0, rfl⟩)⟩
                  · by_cases huAj : u ∈ Aj
                    · refine ⟨none, Finset.mem_insert_self _ _, ?_⟩
                      apply hconn (opnd C j b) (Finset.mem_insert_self _ _)
                      · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huAj, rfl⟩), hx⟩
                      · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (by simp [hb_r]), Finset.mem_insert_self _ _⟩
                    · have huLi : u ∈ Li := Finset.mem_sdiff.mpr ⟨huL0, huAj⟩
                      refine ⟨some r_i, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
                      apply hconn (opnd C i si) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                      · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hLi_sub huLi, rfl⟩), hx⟩
                      · have hri_U0 : r_i ∈ U0 := Finset.mem_union_right _ (Finset.mem_sdiff.mp hr_i_mem).1
                        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r_i, hLi_sub hr_i_mem, rfl⟩),
                          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r_i, hri_U0, rfl⟩)⟩
              have hb := graph_spanning_bound E Lmix R hcov_R
              rw [hLmix_card] at hb
              rw [oC_disj_oExtra] at hElen
              omega
          change 64 ≤ C.gates.length
          omega
        · -- Li = ∅, so L0 ⊆ Aj = orIn (opnd C j b)!
          have hLi_emp : Li = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLi_ne
          apply hsub_single_wire (opnd C j b) (by have := opnd_lt hAO hj b; omega)
            (fun h hhr hor => opnd_or_in_ON hMin huniq hj hjand b hhr hor)
          intro v hvL0
          by_contra hv_notAj
          have : v ∈ Li := Finset.mem_sdiff.mpr ⟨hvL0, hv_notAj⟩
          rw [hLi_emp] at this; exact Finset.notMem_empty v this
    · -- c0 ∉ Bj! So every v ∈ L0 must be in Bj = orIn (opnd C j (1 - b))!
      apply hsub_single_wire (opnd C j (1 - b)) (by have := opnd_lt hAO hj (1 - b); omega)
        (fun h hhr hor => opnd_or_in_ON hMin huniq hj hjand (1 - b) hhr hor)
      intro v hvL0
      have hjt := hL0_real v hvL0
      rw [hj_ev] at hjt
      obtain ⟨_, w, hwBj, hwp⟩ := hjt
      simp only [pairInput, decide_eq_true_eq] at hwp
      rcases hwp with rfl | rfl
      · exact (hc0Bj hwBj).elim
      · exact hwBj
  -- Now classify the edges of j!
  -- First, helper to pass from covering by a star (c0, S) with S ⊆ nbrs c0 to hsingle_star by filtering real leaves!
  have hsingle_star_cover : ∀ (c0 : Fin 26) (S : Finset (Fin 26)), S ⊆ nbrs c0 →
      (∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true → e ∈ starEdgesOf c0 S) →
      64 ≤ C.size := by
    intro c0 S hS_sub hcov_S
    set L0 := S.filter fun v => gateVal 26 C j (pairInput c0 v) = true
    apply hsingle_star c0 L0 ((Finset.filter_subset _ _).trans hS_sub)
    · intro e he hjt
      have heS := hcov_S e he hjt
      obtain ⟨v, hvS, hdeq⟩ := Finset.mem_image.mp heS
      have hv_real : gateVal 26 C j (pairInput c0 v) = true := by
        have heq_p : pairInput c0 v = pairInput e.1 e.2 := by
          unfold dirEdge at hdeq
          split_ifs at hdeq
          · have h1 : c0 = e.1 := congrArg Prod.fst hdeq
            have h2 : v = e.2 := congrArg Prod.snd hdeq
            rw [h1, h2]
          · have h1 : v = e.1 := congrArg Prod.fst hdeq
            have h2 : c0 = e.2 := congrArg Prod.snd hdeq
            rw [← h1, ← h2]; funext w; simp [pairInput, or_comm]
        rwa [heq_p]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hvS, hv_real⟩, hdeq⟩
    · intro v hv; exact (Finset.mem_filter.mp hv).2
  -- Case split on |Bj| <= 1 vs |Bj| >= 2
  by_cases hBj1 : Bj.card ≤ 1
  · by_cases hBj0 : Bj.card = 0
    · have hBj_emp : Bj = ∅ := Finset.card_eq_zero.mp hBj0
      apply hsingle_star_cover 0 ∅ (Finset.empty_subset _)
      intro e he hjt
      rw [hj_ev] at hjt
      obtain ⟨_, w, hw, _⟩ := hjt
      rw [hBj_emp] at hw; exact (Finset.notMem_empty w hw).elim
    · have hBjeq1 : Bj.card = 1 := by omega
      obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp hBjeq1
      apply hsingle_star_cover c0 (nbrs c0) (Finset.Subset.refl _)
      intro e he hjt
      rw [hj_ev] at hjt
      obtain ⟨_, w, hw, hwp⟩ := hjt
      rw [hc0, Finset.mem_singleton] at hw; subst hw
      simp only [pairInput, decide_eq_true_eq] at hwp
      have hadj_e := (mem_pgEdges_iff e).mp he |>.2
      rw [← dirEdge_eq_of_mem_pgEdges he]
      rcases hwp with h1 | h2
      · subst h1; exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
      · subst h2; exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
  · -- |Bj| >= 2!
    push_neg at hBj1
    by_cases hE23 : ((Ai ∩ Bj).Nonempty ∧ Bi.Nonempty) ∧ ((Bi ∩ Bj).Nonempty ∧ Ai.Nonempty)
    · -- Both E2 and E3 are nonempty!
      obtain ⟨⟨⟨p, hp⟩, _⟩, ⟨⟨l, hl⟩, _⟩⟩ := hE23
      have hadj_pl : pgAdj p l = true := hE2 p hp l (Finset.mem_inter.mp hl).1
      have hC1_emp : C1 = ∅ := by
        ext z; simp only [Finset.notMem_empty, iff_false]
        intro hz
        have hb1 := pgAdj_bip z p (hE1 z hz p (Finset.mem_inter.mp hp).2)
        have hb2 := pgAdj_bip z l (hE1 z hz l (Finset.mem_inter.mp hl).2)
        have hb3 := pgAdj_bip p l hadj_pl
        tauto
      by_cases hAiBj : (Ai ∩ Bj).card ≤ 1
      · by_cases hBiBj : (Bi ∩ Bj).card ≤ 1
        · -- Subcase 2.1: Ai ∩ Bj = {p}, Bi ∩ Bj = {l}, E1 = ∅!
          have hp_eq : Ai ∩ Bj = {p} := by
            have h1 : (Ai ∩ Bj).card = 1 := le_antisymm hAiBj (Finset.card_pos.mpr ⟨p, hp⟩)
            obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp h1
            have : p = p' := Finset.mem_singleton.mp (hp' ▸ hp)
            rwa [← this] at hp'
          have hl_eq : Bi ∩ Bj = {l} := by
            have h1 : (Bi ∩ Bj).card = 1 := le_antisymm hBiBj (Finset.card_pos.mpr ⟨l, hl⟩)
            obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp h1
            have : l = l' := Finset.mem_singleton.mp (hl' ▸ hl)
            rwa [← this] at hl'
          have hBi_sub : Bi ⊆ nbrs p := fun v hv => (mem_nbrs_iff p v).mpr (hE2 p hp v hv)
          have hAi_sub : Ai ⊆ nbrs l := fun v hv => (mem_nbrs_iff l v).mpr (hE3 l hl v hv)
          have hcov_j21 : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
              e ∈ starEdgesOf p Bi ∪ starEdgesOf l Ai := by
            intro e he hjt
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hEdge_split e he hjt with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
            · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
            · rw [hp_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_left _ (mem_starEdgesOf_left h2)
            · rw [hp_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_left _ (mem_starEdgesOf_right hadj_e h2)
            · rw [hl_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_right _ (mem_starEdgesOf_left h2)
            · rw [hl_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_right _ (mem_starEdgesOf_right hadj_e h2)
          -- |starEdgesOf p Bi ∪ starEdgesOf l Ai| ≤ 7 because dirEdge p l is in BOTH!
          have hEj_le7 : (starEdgesOf p Bi ∪ starEdgesOf l Ai).card ≤ 7 := by
            have hsh : dirEdge p l ∈ starEdgesOf p Bi ∩ starEdgesOf l Ai :=
              Finset.mem_inter.mpr ⟨mem_starEdgesOf_left (Finset.mem_inter.mp hl).1,
                mem_starEdgesOf_right hadj_pl (Finset.mem_inter.mp hp).1⟩
            have hpos : 1 ≤ (starEdgesOf p Bi ∩ starEdgesOf l Ai).card := Finset.card_pos.mpr ⟨_, hsh⟩
            have hu := Finset.card_union_add_card_inter (starEdgesOf p Bi) (starEdgesOf l Ai)
            have h4a := starEdgesOf_card_le_four hBi_sub
            have h4b := starEdgesOf_card_le_four hAi_sub
            omega
          have h52 := aGates_card_of_j_edges hMin hi hj hiand hjand hij_ne hT_eq Astar rfl
            ctr (fun a => orIn 26 C (wire a))
            (fun a ha => (Finset.card_le_card (hW_sub a ha)).trans (nbrs_card _).le)
            hcov_Astar _ hcov_j21
          have hA_ge14 : 14 ≤ (A_gates C).card := by omega
          -- Extra gate in O_extra from opnd j (1 - b) having both p and l!
          have hex_ge1 : 1 ≤ (O_extra C i).card :=
            extra_of_mixed_bipartite hMin (w := opnd C j (1 - b)) (by have := opnd_lt hAO hj (1 - b); omega)
              (fun h hhr hor => opnd_or_in_ON hMin huniq hj hjand (1 - b) hhr hor)
              (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hl).2 (pgAdj_bip p l hadj_pl)
          -- Pure family bound on A_gates C (i ↦ (p, opnd i 1), j ↦ (l, opnd i 0), a ∈ Astar ↦ (ctr a, wire a))
          have hi_notA : i ∉ Astar := by simp [Astar]
          have hj_notA : j ∉ Astar := by simp [Astar]
          set Idx := insert i (insert j Astar)
          have hIdx_card : Idx.card = (A_gates C).card := by
            have heq : Idx = A_gates C := by
              ext x; simp only [Idx, Astar, Finset.mem_insert, Finset.mem_erase]
              constructor
              · rintro (rfl | rfl | ⟨_, _, hx⟩)
                · exact mem_A_gates.mpr ⟨hi, hiand⟩
                · exact mem_A_gates.mpr ⟨hj, hjand⟩
                · exact hx
              · intro hx
                by_cases hxi : x = i; · exact Or.inl hxi
                by_cases hxj : x = j; · exact Or.inr (Or.inl hxj)
                exact Or.inr (Or.inr ⟨hxj, hxi, hx⟩)
            rw [heq]
          let ctr' : ℕ → Fin 26 := fun k => if k = i then p else if k = j then l else ctr k
          let wire' : ℕ → ℕ := fun k => if k = i then opnd C i 1 else if k = j then opnd C i 0 else wire k
          have hpf : 52 ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
            apply pure_family_sum_bound hMin huniq Idx ctr' wire'
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | hk1
              · simp only [wire', ↓reduceIte]; have := opnd_lt hAO hi 1; omega
              · rcases Finset.mem_insert.mp hk1 with rfl | hkA
                · simp only [wire', hij_ne.symm, ↓reduceIte]; have := opnd_lt hAO hi 0; omega
                · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
                  have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
                  simp only [wire', hki, hkj, ↓reduceIte]; exact hW_lt k hkA
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | hk1
              · simp only [wire', ctr', ↓reduceIte]; exact hBi_sub
              · rcases Finset.mem_insert.mp hk1 with rfl | hkA
                · simp only [wire', ctr', hij_ne.symm, ↓reduceIte]; exact hAi_sub
                · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
                  have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
                  simp only [wire', ctr', hki, hkj, ↓reduceIte]; exact hW_sub k hkA
            · intro k hk h hhr hor
              rcases Finset.mem_insert.mp hk with rfl | hk1
              · simp only [wire', ↓reduceIte] at hhr
                exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq hi hiand hij_ne 1 hhr hor
              · rcases Finset.mem_insert.mp hk1 with rfl | hkA
                · simp only [wire', hij_ne.symm, ↓reduceIte] at hhr
                  exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq hi hiand hij_ne 0 hhr hor
                · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
                  have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
                  simp only [wire', hki, hkj, ↓reduceIte] at hhr
                  exact hW_pure k hkA h hhr hor
            · intro e he
              obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
              by_cases haj : a = j
              · subst a
                rcases Finset.mem_union.mp (hcov_j21 e he hga) with he1 | he2
                · refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
                  simp only [ctr', wire', ↓reduceIte]; exact he1
                · refine ⟨j, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
                  simp only [ctr', wire', hij_ne.symm, ↓reduceIte]; exact he2
              · have haA : a ∈ Astar := by rw [Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
                have hai : a ≠ i := fun h => hi_notA (h ▸ haA)
                refine ⟨a, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haA), ?_⟩
                simp only [ctr', wire', hai, haj, ↓reduceIte]
                exact hcov_Astar a haA e he hga
          have hsize := size_eq_A_Oout_ON hAO
          have hoN := oN_card_eq hMin huniq
          change 64 ≤ C.gates.length
          omega
        · -- |Bi ∩ Bj| >= 2 -> |Ai| = 1 -> Ai = {p}, so E3 ⊆ E2 -> single star at p!
          push_neg at hBiBj
          have hAi1 : Ai.card = 1 := by
            rcases biclique_is_star hE3 with h1 | h2
            · omega
            · exact le_antisymm h2 (Finset.card_pos.mpr ⟨p, (Finset.mem_inter.mp hp).1⟩)
          have hAi_eq : Ai = {p} := by
            obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hAi1
            have : p = p' := Finset.mem_singleton.mp (hp' ▸ (Finset.mem_inter.mp hp).1)
            rwa [← this] at hp'
          apply hsingle_star_cover p (nbrs p) (Finset.Subset.refl _)
          intro e he hjt
          have hadj_e := (mem_pgEdges_iff e).mp he |>.2
          rw [← dirEdge_eq_of_mem_pgEdges he]
          rcases hEdge_split e he hjt with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
          · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
          · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
          · have : e.1 = p := Finset.mem_singleton.mp (hAi_eq ▸ (Finset.mem_inter.mp h1).1)
            subst this; exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
          · have : e.2 = p := Finset.mem_singleton.mp (hAi_eq ▸ (Finset.mem_inter.mp h1).1)
            subst this; exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
          · rw [hAi_eq, Finset.mem_singleton] at h2; subst h2
            exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
          · rw [hAi_eq, Finset.mem_singleton] at h2; subst h2
            exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
      · -- |Ai ∩ Bj| >= 2 -> |Bi| = 1 -> Bi = {l}, so E2 ⊆ E3 -> single star at l!
        push_neg at hAiBj
        have hBi1 : Bi.card = 1 := by
          rcases biclique_is_star hE2 with h1 | h2
          · omega
          · exact le_antisymm h2 (Finset.card_pos.mpr ⟨l, (Finset.mem_inter.mp hl).1⟩)
        have hBi_eq : Bi = {l} := by
          obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp hBi1
          have : l = l' := Finset.mem_singleton.mp (hl' ▸ (Finset.mem_inter.mp hl).1)
          rwa [← this] at hl'
        apply hsingle_star_cover l (nbrs l) (Finset.Subset.refl _)
        intro e he hjt
        have hadj_e := (mem_pgEdges_iff e).mp he |>.2
        rw [← dirEdge_eq_of_mem_pgEdges he]
        rcases hEdge_split e he hjt with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
        · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
        · rw [hBi_eq, Finset.mem_singleton] at h2; subst h2
          exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
        · rw [hBi_eq, Finset.mem_singleton] at h2; subst h2
          exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
        · have : e.1 = l := Finset.mem_singleton.mp (hBi_eq ▸ (Finset.mem_inter.mp h1).1)
          subst this; exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
        · have : e.2 = l := Finset.mem_singleton.mp (hBi_eq ▸ (Finset.mem_inter.mp h1).1)
          subst this; exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
    · -- At least one of E2, E3 is empty!
      -- Helper for when one of E2, E3 is empty (parameterized by si : Fin 2)
      have hone_empty : ∀ (si : Fin 2),
          ¬ ((side (n := 26) C i (1 - si) ∩ Bj).Nonempty ∧ (side (n := 26) C i si).Nonempty) →
          64 ≤ C.size := by
        intro si hEother_emp
        set Si := side (n := 26) C i si
        set Ti := side (n := 26) C i (1 - si)
        have hEsi : ∀ u ∈ Si ∩ Bj, ∀ v ∈ Ti, pgAdj u v = true := by
          fin_cases si <;> assumption
        have hEdge_s : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
            (e.1 ∈ C1 ∧ e.2 ∈ Bj) ∨ (e.2 ∈ C1 ∧ e.1 ∈ Bj) ∨
            (e.1 ∈ Si ∩ Bj ∧ e.2 ∈ Ti) ∨ (e.2 ∈ Si ∩ Bj ∧ e.1 ∈ Ti) := by
          intro e he hjt
          rcases hEdge_split e he hjt with h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · fin_cases si
            · exact Or.inr (Or.inr (Or.inl h))
            · exact (hEother_emp ⟨⟨e.1, h.1⟩, ⟨e.2, h.2⟩⟩).elim
          · fin_cases si
            · exact Or.inr (Or.inr (Or.inr h))
            · exact (hEother_emp ⟨⟨e.2, h.1⟩, ⟨e.1, h.2⟩⟩).elim
          · fin_cases si
            · exact (hEother_emp ⟨⟨e.1, h.1⟩, ⟨e.2, h.2⟩⟩).elim
            · exact Or.inr (Or.inr (Or.inl h))
          · fin_cases si
            · exact (hEother_emp ⟨⟨e.2, h.1⟩, ⟨e.1, h.2⟩⟩).elim
            · exact Or.inr (Or.inr (Or.inr h))
        by_cases hC1_ne : C1.Nonempty
        · -- C1 nonempty and |Bj| >= 2 -> C1 = {c1} and Bj ⊆ nbrs c1!
          have hC1_1 : C1.card = 1 := by
            rcases biclique_is_star hE1 with h1 | h2
            · exact le_antisymm h1 (Finset.card_pos.mpr hC1_ne)
            · omega
          obtain ⟨c1, hc1_eq⟩ := Finset.card_eq_one.mp hC1_1
          have hc1_mem : c1 ∈ C1 := by rw [hc1_eq]; simp
          have hBj_sub : Bj ⊆ nbrs c1 := fun v hv => (mem_nbrs_iff c1 v).mpr (hE1 c1 hc1_mem v hv)
          by_cases hE2_ne : (Si ∩ Bj).Nonempty ∧ Ti.Nonempty
          · by_cases hSiBj1 : (Si ∩ Bj).card ≤ 1
            · -- Subcase 2.2!
              have h1 : (Si ∩ Bj).card = 1 := le_antisymm hSiBj1 (Finset.card_pos.mpr hE2_ne.1)
              obtain ⟨c2, hc2_eq⟩ := Finset.card_eq_one.mp h1
              have hc2_mem : c2 ∈ Si ∩ Bj := by rw [hc2_eq]; simp
              have hTi_sub : Ti ⊆ nbrs c2 := fun v hv => (mem_nbrs_iff c2 v).mpr (hEsi c2 hc2_mem v hv)
              have hc1_mem' : c1 ∈ Aj ∪ (Si ∩ Ti) := by
                fin_cases si
                · exact hc1_mem
                · simpa [C1, Si, Ti, Finset.inter_comm] using hc1_mem
              apply case2_sub22 hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge b hb_r hnb_r
                Astar rfl ctr wire hW_lt hW_sub hW_pure hcov_Astar si c1 c2 hc1_mem' hc2_mem hBj_sub hTi_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_left _ (mem_starEdgesOf_left h2')
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_left _ (mem_starEdgesOf_right hadj_e h2')
              · rw [hc2_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_right _ (mem_starEdgesOf_left h2')
              · rw [hc2_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_right _ (mem_starEdgesOf_right hadj_e h2')
            · -- |Si ∩ Bj| >= 2 -> Ti = {c1}, so E2 ⊆ E1 -> single star at c1!
              push_neg at hSiBj1
              have hTi_sub_c1 : Ti ⊆ {c1} := by
                intro v hv
                rw [Finset.mem_singleton]
                obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hSiBj1
                by_contra hvc1
                have hpair : ({u1, u2} : Finset (Fin 26)) ⊆ nbrs c1 ∩ nbrs v := by
                  intro z hz
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with heq | heq
                  · rw [heq]; exact Finset.mem_inter.mpr ⟨hBj_sub (Finset.mem_inter.mp hu1).2,
                      (mem_nbrs_iff v u1).mpr (by rw [pgAdj_symm]; exact hEsi u1 hu1 v hv)⟩
                  · rw [heq]; exact Finset.mem_inter.mpr ⟨hBj_sub (Finset.mem_inter.mp hu2).2,
                      (mem_nbrs_iff v u2).mpr (by rw [pgAdj_symm]; exact hEsi u2 hu2 v hv)⟩
                have hle := (Finset.card_le_card hpair).trans (pg_no_c4 c1 v (Ne.symm hvc1))
                rw [Finset.card_pair hune] at hle; omega
              apply hsingle_star_cover c1 Bj hBj_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_left h2'
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_right hadj_e h2'
              · have := Finset.mem_singleton.mp (hTi_sub_c1 h2'); subst this
                exact mem_starEdgesOf_right hadj_e (Finset.mem_inter.mp h1').2
              · have := Finset.mem_singleton.mp (hTi_sub_c1 h2'); subst this
                exact mem_starEdgesOf_left (Finset.mem_inter.mp h1').2
          · -- E2 is also empty -> single star at c1!
            apply hsingle_star_cover c1 Bj hBj_sub
            intro e he hjt
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hEdge_s e he hjt with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_left h2'
            · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_right hadj_e h2'
            · exact (hE2_ne ⟨⟨e.1, h1'⟩, ⟨e.2, h2'⟩⟩).elim
            · exact (hE2_ne ⟨⟨e.2, h1'⟩, ⟨e.1, h2'⟩⟩).elim
        · -- C1 = ∅ -> only E2 remains, which is a single biclique = single star!
          have hC1_emp : C1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC1_ne
          by_cases hE2_ne : (Si ∩ Bj).Nonempty ∧ Ti.Nonempty
          · rcases biclique_is_star hEsi with h1 | h2
            · have h1eq : (Si ∩ Bj).card = 1 := le_antisymm h1 (Finset.card_pos.mpr hE2_ne.1)
              obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h1eq
              have hTi_sub : Ti ⊆ nbrs c0 := fun v hv => (mem_nbrs_iff c0 v).mpr (hEsi c0 (by rw [hc0]; simp) v hv)
              apply hsingle_star_cover c0 Ti hTi_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', _⟩ | ⟨h1', _⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hc0, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_left h2'
              · rw [hc0, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_right hadj_e h2'
            · have h2eq : Ti.card = 1 := le_antisymm h2 (Finset.card_pos.mpr hE2_ne.2)
              obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h2eq
              have hSi_sub : Si ∩ Bj ⊆ nbrs c0 := fun u hu =>
                (mem_nbrs_iff c0 u).mpr (by rw [pgAdj_symm]; exact hEsi u hu c0 (by rw [hc0]; simp))
              apply hsingle_star_cover c0 (Si ∩ Bj) hSi_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', _⟩ | ⟨h1', _⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hc0, Finset.mem_singleton] at h2'; subst h2'; exact mem_starEdgesOf_right hadj_e h1'
              · rw [hc0, Finset.mem_singleton] at h2'; subst h2'; exact mem_starEdgesOf_left h1'
          · -- All of E1, E2, E3 are empty!
            apply hsingle_star_cover 0 ∅ (Finset.empty_subset _)
            intro e he hjt
            rcases hEdge_s e he hjt with ⟨h1', _⟩ | ⟨h1', _⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
            · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
            · exact (hE2_ne ⟨⟨e.1, h1'⟩, ⟨e.2, h2'⟩⟩).elim
            · exact (hE2_ne ⟨⟨e.2, h1'⟩, ⟨e.1, h2'⟩⟩).elim
      by_cases hE3 : (Bi ∩ Bj).Nonempty ∧ Ai.Nonempty
      · exact hone_empty 1 (fun h => hE23 ⟨h, hE3⟩)
      · exact hone_empty 0 hE3

lemma main_proof (C : Circuit) (hV : ValidCirc C) (hMinAll : ∀ C', ValidCirc C' → C.size ≤ C'.size)
    (hand1 : andPairs 26 C = 1) : 64 ≤ C.size := by
  have hMin : IsMin C := ⟨hV, hMinAll⟩
  obtain ⟨i, j, hi, hj, hiand, hjand, hic_ij, huniq⟩ := exists_unique_andPair hand1
  have hij_ne : i ≠ j := by have := inCone_lt 26 C i j hic_ij; omega
  have hnot_i_out := not_orToOutput_i hMin hi hj hiand hjand hic_ij huniq
  have hT_eq : T_gates C = (A_gates C).erase i := by
    ext a
    simp only [Finset.mem_erase, mem_A_gates]
    constructor
    · intro haT
      have ha_info := mem_T_gates.mp haT
      refine ⟨fun heq => hnot_i_out (heq ▸ ha_info.2.2), ha_info.1, ha_info.2.1⟩
    · rintro ⟨hnei, ha_lt, ha_and⟩
      exact and_ne_i_in_T hMin huniq (mem_A_gates.mpr ⟨ha_lt, ha_and⟩) hnei
  have hOout_ge : (A_gates C).card ≤ (O_out C).card + 2 := by
    have h1 := oOut_card_bound hMin
    rw [hT_eq, Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hi, hiand⟩)] at h1
    omega
  rcases j_orReaches_i hMin hi hj hiand hjand hic_ij huniq with hr0 | hr1
  · by_cases hr1' : OrReaches 26 C (opnd C j 1) i
    · exact case_both_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge hr0 hr1'
    · exact case_one_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge 0 hr0 hr1'
  · by_cases hr0' : OrReaches 26 C (opnd C j 0) i
    · exact case_both_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge hr0' hr1
    · exact case_one_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge 1 hr1 hr0'

end PEqualNP.Outside.L_meta_5162

theorem PEqualNP.Outside.L_meta_5162 :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (1 : ℕ) → (64 : ℕ) ≤ x3.size := by
  intro x1 x2 C hV hMin hand1
  exact PEqualNP.Outside.L_meta_5162.main_proof C hV hMin hand1
