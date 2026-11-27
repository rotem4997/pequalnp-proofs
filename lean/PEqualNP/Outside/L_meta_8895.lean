import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8895

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def df (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem df_len (gs : List Gate) : ∀ d : List ℕ, (df gs d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp [df]
  | cons g gs ih =>
    intro d
    have := ih (d ++ [g.lineDegree d])
    simp only [df, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_mono (gs : List Gate) (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (wf gs w1).getD i false = true → (wf gs w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ hle i hi; exact hle i hi
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hM g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (by simp [hg'])
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    have hval : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
      rcases hop with h | h <;> rw [h]
      · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        intro h1 i hi
        exact hle i (h1 i hi)
      · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        rintro ⟨i, hi, hv⟩
        exact ⟨i, hi, hle i hv⟩
    apply ih hgs
    · simp [hlen]
    · intro i hi
      by_cases hlt : i < w1.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        exact hle i (by rwa [List.getD_eq_getElem?_getD])
      · by_cases heq : i = w1.length
        · subst heq
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero] at hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
            show w1.length - w2.length = 0 by omega, List.getElem?_cons_zero]
          exact hval hi
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          cases hi

def restrictList (n : ℕ) (x : List Bool) (marked S : Finset ℕ) : List Bool :=
  (List.range n).map fun i => if i ∈ marked then (decide (i ∈ S) && x.getD i false) else x.getD i false

theorem restrictList_len (n : ℕ) (x : List Bool) (marked S : Finset ℕ) :
    (restrictList n x marked S).length = n := by
  simp [restrictList]

theorem restrictList_getD (n : ℕ) (x : List Bool) (marked S : Finset ℕ) (i : ℕ) (hi : i < n) :
    (restrictList n x marked S).getD i false =
      if i ∈ marked then (decide (i ∈ S) && x.getD i false) else x.getD i false := by
  rw [List.getD_eq_getElem _ _ (by rw [restrictList_len]; exact hi)]
  simp [restrictList, hi]

theorem restrictList_mono (n : ℕ) (x : List Bool) (marked S1 S2 : Finset ℕ) (hsub : S1 ⊆ S2) :
    ∀ i, (restrictList n x marked S1).getD i false = true →
      (restrictList n x marked S2).getD i false = true := by
  intro i hi
  by_cases hlt : i < n
  · rw [restrictList_getD n x marked S1 i hlt] at hi
    rw [restrictList_getD n x marked S2 i hlt]
    split_ifs at hi ⊢ with hm
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hi ⊢
      exact ⟨hsub hi.1, hi.2⟩
    · exact hi
  · rw [List.getD_eq_default _ _ (by rw [restrictList_len]; omega)] at hi
    cases hi

theorem foldr_max_ge (l : List ℕ) (a : ℕ) (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
    simp only [List.mem_cons] at ha
    simp only [List.foldr_cons]
    rcases ha with rfl | ht
    · exact le_max_left _ _
    · exact le_trans (ih ht) (le_max_right _ _)

theorem lineDegree_witness (n : ℕ) (marked : Finset ℕ) (x : List Bool) (hx : x.length = n)
    (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ w, (wf gs x).getD w false = true →
      ∃ S : Finset ℕ, S ⊆ marked ∧
        S.card ≤ (df gs ((List.range n).map fun i => if i ∈ marked then 1 else 0)).getD w 0 ∧
        (wf gs (restrictList n x marked S)).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [wf, df, List.foldl_nil] at hw ⊢
    have hwn : w < n := by
      by_contra hge
      rw [List.getD_eq_default _ _ (by omega)] at hw
      cases hw
    have hdeg : (((List.range n).map fun i => if i ∈ marked then 1 else 0)).getD w 0 =
        if w ∈ marked then 1 else 0 := by
      rw [List.getD_eq_getElem _ _ (by simp [hwn])]
      simp [hwn]
    rw [hdeg]
    by_cases hm : w ∈ marked
    · refine ⟨{w}, by simpa using hm, by simp [hm], ?_⟩
      rw [restrictList_getD n x marked {w} w hwn, if_pos hm]
      simp [hw]
      exact hw
    · refine ⟨∅, Finset.empty_subset _, by simp [hm], ?_⟩
      rw [restrictList_getD n x marked ∅ w hwn, if_neg hm]
      exact hw
  | append_singleton gs g ih =>
    have hMgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (by simp [hg'])
    have hg := hM g (by simp)
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    have ih' := ih hMgs
    have hwf_snoc : ∀ y : List Bool,
        wf (gs ++ [g]) y = wf gs y ++ [g.op.eval (g.inputs.map fun i => (wf gs y).getD i false)] := by
      intro y; simp [wf, List.foldl_append]
    have hdf_snoc :
        df (gs ++ [g]) ((List.range n).map fun i => if i ∈ marked then 1 else 0) =
          df gs ((List.range n).map fun i => if i ∈ marked then 1 else 0) ++
            [g.lineDegree (df gs ((List.range n).map fun i => if i ∈ marked then 1 else 0))] := by
      simp [df, List.foldl_append]
    set dprev := df gs ((List.range n).map fun i => if i ∈ marked then 1 else 0)
    have hdlen : dprev.length = n + gs.length := by
      rw [df_len]; simp
    have hwlen : ∀ y : List Bool, y.length = n → (wf gs y).length = n + gs.length := by
      intro y hy; rw [wf_len, hy]
    intro w hw
    rw [hwf_snoc x] at hw
    rw [hdf_snoc]
    by_cases hlt : w < n + gs.length
    · have hw1 : (wf gs x).getD w false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hwlen x hx]; exact hlt)] at hw
        rwa [List.getD_eq_getElem?_getD]
      obtain ⟨S, hSsub, hScard, hSval⟩ := ih' w hw1
      refine ⟨S, hSsub, ?_, ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hdlen]; exact hlt)]
        rwa [← List.getD_eq_getElem?_getD]
      · rw [hwf_snoc, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [hwlen _ (restrictList_len n x marked S)]; exact hlt)]
        rwa [← List.getD_eq_getElem?_getD]
    · by_cases heq : w = n + gs.length
      · subst heq
        have hw1 : g.op.eval (g.inputs.map fun i => (wf gs x).getD i false) = true := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hwlen x hx]),
            show n + gs.length - (wf gs x).length = 0 by rw [hwlen x hx]; omega,
            List.getElem?_cons_zero] at hw
          exact hw
        have hdeg_eq : (dprev ++ [g.lineDegree dprev]).getD (n + gs.length) 0 = g.lineDegree dprev := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
            show n + gs.length - dprev.length = 0 by omega, List.getElem?_cons_zero]
          rfl
        rw [hdeg_eq]
        have hret : ∀ S : Finset ℕ,
            (wf (gs ++ [g]) (restrictList n x marked S)).getD (n + gs.length) false =
              g.op.eval (g.inputs.map fun i => (wf gs (restrictList n x marked S)).getD i false) := by
          intro S
          rw [hwf_snoc, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by rw [hwlen _ (restrictList_len n x marked S)]),
            show n + gs.length - (wf gs (restrictList n x marked S)).length = 0 by
              rw [hwlen _ (restrictList_len n x marked S)]; omega,
            List.getElem?_cons_zero]
          rfl
        rcases hop with hand | hor
        · have hld : g.lineDegree dprev = (g.inputs.map fun i => dprev.getD i 0).sum := by
            unfold Gate.lineDegree; rw [hand]; simp
          rw [hld]
          rcases hins : g.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
          · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
            rw [hret ∅, hand, hins]; rfl
          · rw [hand, hins] at hw1
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id] at hw1
            obtain ⟨Su, hSu_sub, hSu_card, hSu_val⟩ := ih' u hw1
            refine ⟨Su, hSu_sub, by simpa using hSu_card, ?_⟩
            rw [hret Su, hand, hins]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id]
            exact hSu_val
          · rw [hand, hins] at hw1
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, Bool.and_eq_true, id] at hw1
            obtain ⟨Su, hSu_sub, hSu_card, hSu_val⟩ := ih' u hw1.1
            obtain ⟨Sv, hSv_sub, hSv_card, hSv_val⟩ := ih' v hw1.2
            refine ⟨Su ∪ Sv, Finset.union_subset hSu_sub hSv_sub, ?_, ?_⟩
            · have hcu := Finset.card_union_le Su Sv
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
              omega
            · rw [hret (Su ∪ Sv), hand, hins]
              have hmu := wf_mono gs hMgs (restrictList n x marked Su) (restrictList n x marked (Su ∪ Sv))
                (by simp [restrictList_len]) (restrictList_mono n x marked Su (Su ∪ Sv) Finset.subset_union_left) u hSu_val
              have hmv := wf_mono gs hMgs (restrictList n x marked Sv) (restrictList n x marked (Su ∪ Sv))
                (by simp [restrictList_len]) (restrictList_mono n x marked Sv (Su ∪ Sv) Finset.subset_union_right) v hSv_val
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                Bool.and_true, Bool.and_eq_true, id]
              exact ⟨hmu, hmv⟩
          · simp [hins] at hg
        · have hld : g.lineDegree dprev = (g.inputs.map fun i => dprev.getD i 0).foldr max 0 := by
            unfold Gate.lineDegree; rw [hor]; simp
          rw [hld]
          rw [hor] at hw1
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hw1
          obtain ⟨u, hu_mem, hu_val⟩ := hw1
          obtain ⟨Su, hSu_sub, hSu_card, hSu_val⟩ := ih' u hu_val
          refine ⟨Su, hSu_sub, ?_, ?_⟩
          · exact le_trans hSu_card (foldr_max_ge _ _ (List.mem_map.mpr ⟨u, hu_mem, rfl⟩))
          · rw [hret Su, hor]
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
            exact ⟨u, hu_mem, hSu_val⟩
      · rw [List.getD_eq_default _ _ (by simp [hwlen x hx]; omega)] at hw
        cases hw

theorem incidenceInput_len (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
  simp [incidenceInput]

theorem incidenceInput_getD_lt13 (X Y : Finset (Fin 13)) (i : ℕ) (hi : i < 13) :
    (incidenceInput X Y).getD i false = decide ((⟨i, hi⟩ : Fin 13) ∈ X) := by
  unfold incidenceInput
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_ofFn, List.length_ofFn]; omega)]
  rw [List.getElem_append_left (by rw [List.length_ofFn]; exact hi)]
  rw [List.getElem_ofFn]

theorem incidenceInput_getD_ge13 (X Y : Finset (Fin 13)) (i : ℕ) (hi1 : 13 ≤ i) (hi2 : i < 26) :
    (incidenceInput X Y).getD i false = decide ((⟨i - 13, by omega⟩ : Fin 13) ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_ofFn, List.length_ofFn]; omega)]
  rw [List.getElem_append_right (by rw [List.length_ofFn]; exact hi1)]
  simp only [List.length_ofFn]
  rw [List.getElem_ofFn]

theorem eval_mono_incidence (C : Circuit) (hM : Monotone2 C) (X X' Y Y' : Finset (Fin 13))
    (hX : X ⊆ X') (hY : Y ⊆ Y')
    (hT : C.eval (incidenceInput X Y) = true) : C.eval (incidenceInput X' Y') = true := by
  apply wf_mono C.gates hM (incidenceInput X Y) (incidenceInput X' Y')
  · simp [incidenceInput_len]
  · intro i hi
    by_cases hlt13 : i < 13
    · rw [incidenceInput_getD_lt13 X Y i hlt13] at hi
      rw [incidenceInput_getD_lt13 X' Y' i hlt13]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hX hi
    · by_cases hlt26 : i < 26
      · rw [incidenceInput_getD_ge13 X Y i (by omega) hlt26] at hi
        rw [incidenceInput_getD_ge13 X' Y' i (by omega) hlt26]
        simp only [decide_eq_true_eq] at hi ⊢
        exact hY hi
      · rw [List.getD_eq_default _ _ (by rw [incidenceInput_len]; omega)] at hi
        cases hi
  · exact hT

theorem restrict_Ico_eq (X Y : Finset (Fin 13)) (S : Finset ℕ) :
    restrictList 26 (incidenceInput X Y) (Finset.Ico 13 26) S =
      incidenceInput X (Y.filter fun l => 13 + l.val ∈ S) := by
  apply List.ext_getElem (by rw [restrictList_len, incidenceInput_len])
  intro i hi1 hi2
  have hi26 : i < 26 := by rw [restrictList_len] at hi1; exact hi1
  rw [← List.getD_eq_getElem _ false hi1, ← List.getD_eq_getElem _ false hi2,
    restrictList_getD 26 _ _ _ i hi26]
  by_cases hlt13 : i < 13
  · have hnot : i ∉ Finset.Ico 13 26 := by simp; omega
    rw [if_neg hnot, incidenceInput_getD_lt13 X Y i hlt13,
      incidenceInput_getD_lt13 X _ i hlt13]
  · have hmem : i ∈ Finset.Ico 13 26 := by simp; omega
    rw [if_pos hmem, incidenceInput_getD_ge13 X Y i (by omega) hi26,
      incidenceInput_getD_ge13 X _ i (by omega) hi26]
    have heq : 13 + (i - 13) = i := by omega
    by_cases hS : i ∈ S <;> by_cases hY : (⟨i - 13, by omega⟩ : Fin 13) ∈ Y <;>
      simp [hS, hY, heq]

theorem restrict_range_eq (X Y : Finset (Fin 13)) (S : Finset ℕ) :
    restrictList 26 (incidenceInput X Y) (Finset.range 13) S =
      incidenceInput (X.filter fun p => p.val ∈ S) Y := by
  apply List.ext_getElem (by rw [restrictList_len, incidenceInput_len])
  intro i hi1 hi2
  have hi26 : i < 26 := by rw [restrictList_len] at hi1; exact hi1
  rw [← List.getD_eq_getElem _ false hi1, ← List.getD_eq_getElem _ false hi2,
    restrictList_getD 26 _ _ _ i hi26]
  by_cases hlt13 : i < 13
  · have hmem : i ∈ Finset.range 13 := by simp [hlt13]
    rw [if_pos hmem, incidenceInput_getD_lt13 X Y i hlt13,
      incidenceInput_getD_lt13 _ Y i hlt13]
    by_cases hS : i ∈ S <;> by_cases hX : (⟨i, hlt13⟩ : Fin 13) ∈ X <;> simp [hS, hX]
  · have hnot : i ∉ Finset.range 13 := by simp; omega
    rw [if_neg hnot, incidenceInput_getD_ge13 X Y i (by omega) hi26,
      incidenceInput_getD_ge13 _ Y i (by omega) hi26]

theorem card_le_two_cases {α : Type*} [DecidableEq α] (A : Finset α) (hA : A.card ≤ 2) :
    A = ∅ ∨ ∃ a b : α, A = {a, b} := by
  rcases Finset.eq_empty_or_nonempty A with rfl | ⟨a, ha⟩
  · exact Or.inl rfl
  · rcases Finset.eq_empty_or_nonempty (A.erase a) with hemp | ⟨b, hb⟩
    · right
      refine ⟨a, a, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_self]
      constructor
      · intro hx
        by_contra hne
        have : x ∈ A.erase a := Finset.mem_erase.mpr ⟨hne, hx⟩
        rw [hemp] at this
        simp at this
      · rintro rfl; exact ha
    · right
      refine ⟨a, b, ?_⟩
      have hsub : ({a, b} : Finset α) ⊆ A := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact Finset.mem_of_mem_erase hb
      have hne : a ≠ b := (Finset.mem_erase.mp hb).1.symm
      have hcard : ({a, b} : Finset α).card = 2 := Finset.card_pair hne
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem pencil_empty : ¬ InNoPencil singerLines3 (missLines singerLines3 (zeroSet singerLines3 ∅)) := by
  decide

theorem pencil_pair : ∀ l1 l2 : Fin 13,
    ¬ InNoPencil singerLines3 (missLines singerLines3 (zeroSet singerLines3 {l1, l2})) := by
  decide

theorem line_empty : ¬ InNoLine singerLines3 (zeroSet singerLines3 (missLines singerLines3 ∅)) := by
  decide

theorem line_pair : ∀ p1 p2 : Fin 13,
    ¬ InNoLine singerLines3 (zeroSet singerLines3 (missLines singerLines3 {p1, p2})) := by
  decide

theorem main (C : Circuit) (hM : Monotone2 C) (hRight : RightOnIncidentPairs singerLines3 C)
    (hNonGen : ∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l ∈ missLines singerLines3 P, p ∈ singerLines3 l) →
      (¬ InNoLine singerLines3 P ∨ ¬ InNoPencil singerLines3 (missLines singerLines3 P)) →
      C.eval (incidenceInput P (missLines singerLines3 P)) = false)
    (hDeg : HasLineDegree 26 (Finset.Ico 13 26) C 2 ∨ HasLineDegree 26 (Finset.range 13) C 2) :
    ComputesIncidence singerLines3 C := by
  intro X Y
  cases hfun : incidenceFun singerLines3 X Y
  · cases hev : C.eval (incidenceInput X Y)
    · rfl
    · exfalso
      have hFalse : ∀ p ∈ X, ∀ l ∈ Y, p ∉ singerLines3 l := by
        unfold incidenceFun at hfun
        simp only [decide_eq_false_iff_not, not_exists, not_and] at hfun
        exact hfun
      rcases hDeg with hLineDeg | hPtDeg
      · obtain ⟨S, hSsub, hScard, hSval⟩ :=
          lineDegree_witness 26 (Finset.Ico 13 26) (incidenceInput X Y) (incidenceInput_len X Y)
            C.gates hM C.output hev
        have hSc2 : S.card ≤ 2 := le_trans hScard hLineDeg
        rw [restrict_Ico_eq] at hSval
        let L' := Y.filter fun l => 13 + l.val ∈ S
        have hL'_card : L'.card ≤ 2 := by
          have hinj : L'.card ≤ S.card := by
            have h1 : (L'.image fun l : Fin 13 => 13 + l.val) ⊆ S := by
              intro z hz
              obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
              exact (Finset.mem_filter.mp hl).2
            have h2 := Finset.card_le_card h1
            rwa [Finset.card_image_of_injective L' (fun a b hab => Fin.ext (by omega))] at h2
          omega
        let P' := zeroSet singerLines3 L'
        have hXsub : X ⊆ P' := by
          intro p hp
          simp only [P', zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
          intro l hl
          exact hFalse p hp l (Finset.mem_filter.mp hl).1
        have hL'sub : L' ⊆ missLines singerLines3 P' := by
          intro l hl
          simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
          intro p hpl hpP
          exact (Finset.mem_filter.mp hpP).2 l hl hpl
        have hMax : ∀ p ∉ P', ∃ l ∈ missLines singerLines3 P', p ∈ singerLines3 l := by
          intro p hp
          simp only [P', zeroSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
            not_not] at hp
          obtain ⟨l, hl, hpl⟩ := hp
          exact ⟨l, hL'sub hl, hpl⟩
        have hNP : ¬ InNoPencil singerLines3 (missLines singerLines3 P') := by
          rcases card_le_two_cases L' hL'_card with h0 | ⟨l1, l2, h2⟩
          · dsimp only [P']; rw [h0]; exact pencil_empty
          · dsimp only [P']; rw [h2]; exact pencil_pair l1 l2
        have hcf := hNonGen P' hMax (Or.inr hNP)
        have hct : C.eval (incidenceInput P' (missLines singerLines3 P')) = true :=
          eval_mono_incidence C hM X P' L' (missLines singerLines3 P') hXsub hL'sub hSval
        rw [hcf] at hct
        cases hct
      · obtain ⟨S, hSsub, hScard, hSval⟩ :=
          lineDegree_witness 26 (Finset.range 13) (incidenceInput X Y) (incidenceInput_len X Y)
            C.gates hM C.output hev
        have hSc2 : S.card ≤ 2 := le_trans hScard hPtDeg
        rw [restrict_range_eq] at hSval
        let P' := X.filter fun p => p.val ∈ S
        have hP'_card : P'.card ≤ 2 := by
          have hinj : P'.card ≤ S.card := by
            have h1 : (P'.image fun p : Fin 13 => p.val) ⊆ S := by
              intro z hz
              obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
              exact (Finset.mem_filter.mp hp).2
            have h2 := Finset.card_le_card h1
            rwa [Finset.card_image_of_injective P' (fun a b hab => Fin.ext hab)] at h2
          omega
        let L' := missLines singerLines3 P'
        let P'' := zeroSet singerLines3 L'
        have hP'sub : P' ⊆ P'' := by
          intro p hp
          simp only [P'', zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
          intro l hl hpl
          have hdisj := (Finset.mem_filter.mp hl).2
          exact Finset.disjoint_left.mp hdisj hpl hp
        have hYsub : Y ⊆ L' := by
          intro l hl
          simp only [L', missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
          intro p hpl hp
          exact hFalse p (Finset.mem_filter.mp hp).1 l hl hpl
        have hL'sub : L' ⊆ missLines singerLines3 P'' := by
          intro l hl
          simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
          intro p hpl hpP
          exact (Finset.mem_filter.mp hpP).2 l hl hpl
        have hMax : ∀ p ∉ P'', ∃ l ∈ missLines singerLines3 P'', p ∈ singerLines3 l := by
          intro p hp
          simp only [P'', zeroSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
            not_not] at hp
          obtain ⟨l, hl, hpl⟩ := hp
          exact ⟨l, hL'sub hl, hpl⟩
        have hNL : ¬ InNoLine singerLines3 P'' := by
          rcases card_le_two_cases P' hP'_card with h0 | ⟨p1, p2, h2⟩
          · dsimp only [P'', L']; rw [h0]; exact line_empty
          · dsimp only [P'', L']; rw [h2]; exact line_pair p1 p2
        have hcf := hNonGen P'' hMax (Or.inl hNL)
        have hct : C.eval (incidenceInput P'' (missLines singerLines3 P'')) = true :=
          eval_mono_incidence C hM P' P'' Y (missLines singerLines3 P'')
            hP'sub (Finset.Subset.trans hYsub hL'sub) hSval
        rw [hcf] at hct
        cases hct
  · unfold incidenceFun at hfun
    simp only [decide_eq_true_eq] at hfun
    obtain ⟨p, hp, l, hl, hpl⟩ := hfun
    exact eval_mono_incidence C hM {p} X {l} Y
      (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
      (hRight l p hpl)

end PEqualNP.Outside.L_meta_8895

theorem PEqualNP.Outside.L_meta_8895 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∉ x2, ∃ x5 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2, x3 ∈ PEqualNP.HeptadCover.singerLines3 x5) → ¬PEqualNP.GenericRejection.InNoLine PEqualNP.HeptadCover.singerLines3 x2 ∨ ¬PEqualNP.GenericRejection.InNoPencil PEqualNP.HeptadCover.singerLines3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2) → x1.eval (PEqualNP.GenericRejection.incidenceInput x2 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)) = Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x2 → x1 x2 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x2 := by
  dsimp only
  intro C hM hRight hNonGen hDeg
  exact PEqualNP.Outside.L_meta_8895.main C hM hRight hNonGen hDeg
