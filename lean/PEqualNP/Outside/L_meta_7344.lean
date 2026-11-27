import Mathlib
import PEqualNP.Defs

-- Credits: scan, scan_append, scan_length, scan_prefix, boolStep, scan_bool_mono are copied from
-- the merged file L_meta_2970; the getD helpers follow the merged file L_meta_4342.

namespace PEqualNP.Outside.L_meta_7344

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma scan_bool_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lx ly : List Bool) (hlen : lx.length = ly.length)
    (hle : ∀ i, lx.getD i false = true → ly.getD i false = true) :
    (scan boolStep gs lx).length = (scan boolStep gs ly).length ∧
      ∀ w, (scan boolStep gs lx).getD w false = true → (scan boolStep gs ly).getD w false = true := by
  induction gs generalizing lx ly with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    have hstep : boolStep lx g = true → boolStep ly g = true := by
      intro h
      rcases hg with hop | hop
      · simp only [boolStep, hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
        intro i hi
        exact hle i (h i hi)
      · simp only [boolStep, hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
        rcases h with ⟨i, hi, hit⟩
        exact ⟨i, hi, hle i hit⟩
    have hlen' : (lx ++ [boolStep lx g]).length = (ly ++ [boolStep ly g]).length := by
      simp [hlen]
    have hle' : ∀ i, (lx ++ [boolStep lx g]).getD i false = true →
        (ly ++ [boolStep ly g]).getD i false = true := by
      intro i hi
      by_cases hil : i < lx.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle i hi
      · by_cases heq : i = lx.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    exact ih hgs (lx ++ [boolStep lx g]) (ly ++ [boolStep ly g]) hlen' hle'

lemma scan_two {α : Type} (step : List α → Gate → α) (gs : List Gate) (g1 g2 : Gate)
    (w : List α) :
    scan step (gs ++ [g1, g2]) w =
      (scan step gs w ++ [step (scan step gs w) g1]) ++
        [step (scan step gs w ++ [step (scan step gs w) g1]) g2] := by
  rw [scan_append]
  rfl

lemma getD_init {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_last' {α : Type} (z : α) (l : List α) (b : α) (m : ℕ) (hm : l.length = m) :
    (l ++ [b]).getD m z = b := by
  subst hm
  exact getD_last z l b

lemma eval_mono (D : Circuit) (hD : Monotone2 D) (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    D.eval x = true → D.eval y = true := by
  have hAO : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hD g hg).1
    simpa using this
  exact (scan_bool_mono D.gates hAO x y hlen hle).2 D.output

-- One step of readVectors.
def rstep (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = scan (rstep k S) C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  rw [readVectors_eq, scan_length]
  simp

lemma readVectors_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (a : ℕ) (ha : a < n) :
    (readVectors C n S k).getD a [] = leafVectors S k a := by
  rw [readVectors_eq, scan_prefix _ _ _ _ _ (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, ha]

lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

lemma mem_andStep (k : ℕ) (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

lemma mem_orFold (v : List ℕ) (ins : List (List (List ℕ))) (acc : List (List ℕ)) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ A ∈ ins, v ∈ A := by
  induction ins generalizing acc with
  | nil => simp
  | cons A ins ih =>
    simp only [List.foldl_cons, ih, mem_fold_insertNew, List.mem_cons, exists_eq_or_imp]
    tauto

lemma mem_rstep_or (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (v : List ℕ)
    (h : v ∈ R.getD i [] ∨ v ∈ R.getD j []) :
    v ∈ rstep k S R ⟨GateOp.or, [i, j]⟩ := by
  show v ∈ ([i, j].map fun t => R.getD t []).foldl (fun acc A => A.foldl insertNew acc) []
  rw [mem_orFold]
  right
  rcases h with h | h
  · exact ⟨R.getD i [], by simp, h⟩
  · exact ⟨R.getD j [], by simp, h⟩

lemma mem_rstep_and (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (u w : List ℕ)
    (hu : u ∈ R.getD i []) (hw : w ∈ R.getD j []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) w ∈ rstep k S R ⟨GateOp.and, [i, j]⟩ := by
  show _ ∈ andStep k (andStep k [S.map fun _ => 0] (R.getD i [])) (R.getD j [])
  rw [mem_andStep]
  exact ⟨_, (mem_andStep _ _ _ _).mpr ⟨_, by simp, u, hu, rfl⟩, w, hw, rfl⟩

lemma capAdd_map (k : ℕ) (S : List ℕ) (f g : ℕ → ℕ) :
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    simp only [capAdd, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

-- The circuit with the product of wires a and b joined to the output by an OR.
def ext (n : ℕ) (D : Circuit) (a b : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + D.gates.length]⟩],
    n + D.gates.length + 1⟩

lemma ext_eval (n : ℕ) (D : Circuit) (a b : ℕ) (x : List Bool) (hx : x.length = n)
    (ha : a < n) (hb : b < n) (ho : D.output < n + D.gates.length) :
    (ext n D a b).eval x = (D.eval x || (x.getD a false && x.getD b false)) := by
  have hlen : (scan boolStep D.gates x).length = n + D.gates.length := by rw [scan_length, hx]
  have hE : D.eval x = (scan boolStep D.gates x).getD D.output false := rfl
  have hA : (scan boolStep D.gates x).getD a false = x.getD a false :=
    scan_prefix _ _ _ _ _ (by omega)
  have hB : (scan boolStep D.gates x).getD b false = x.getD b false :=
    scan_prefix _ _ _ _ _ (by omega)
  show (scan boolStep (D.gates ++ [⟨GateOp.and, [a, b]⟩,
    ⟨GateOp.or, [D.output, n + D.gates.length]⟩]) x).getD (n + D.gates.length + 1) false = _
  rw [scan_two, getD_last' _ _ _ _ (by simp [hlen])]
  show (((scan boolStep D.gates x ++ [_]).getD D.output false) ||
    (((scan boolStep D.gates x ++ [_]).getD (n + D.gates.length) false) || false)) = _
  rw [getD_init _ _ _ _ (by omega), getD_last' _ _ _ _ hlen, ← hE]
  show (D.eval x || ((((scan boolStep D.gates x).getD a false) &&
    (((scan boolStep D.gates x).getD b false) && true)) || false)) = _
  rw [hA, hB]
  simp

lemma ext_out (n : ℕ) (D : Circuit) (a b : ℕ) (T : List ℕ) (k : ℕ) :
    (readVectors (ext n D a b) n T k).getD (ext n D a b).output [] =
      rstep k T (readVectors D n T k ++ [rstep k T (readVectors D n T k) ⟨GateOp.and, [a, b]⟩])
        ⟨GateOp.or, [D.output, n + D.gates.length]⟩ := by
  have hlen := readVectors_length D n T k
  rw [readVectors_eq] at hlen ⊢
  show (scan (rstep k T) (D.gates ++ [⟨GateOp.and, [a, b]⟩,
    ⟨GateOp.or, [D.output, n + D.gates.length]⟩]) _).getD (n + D.gates.length + 1) [] = _
  rw [scan_two, getD_last' _ _ _ _ (by simp [hlen])]
  rfl

lemma ext_pass (n : ℕ) (D : Circuit) (a b : ℕ) (T : List ℕ) (k : ℕ) (v : List ℕ)
    (hv : v ∈ (readVectors D n T k).getD D.output []) :
    v ∈ (readVectors (ext n D a b) n T k).getD (ext n D a b).output [] := by
  rw [ext_out]
  apply mem_rstep_or
  left
  by_cases ho : D.output < (readVectors D n T k).length
  · rw [getD_init _ _ _ _ ho]
    exact hv
  · rw [List.getD_eq_default _ _ (by omega)] at hv
    simp at hv

lemma ext_new (n : ℕ) (D : Circuit) (a b : ℕ) (T : List ℕ) (k : ℕ) (v : List ℕ)
    (hv : v ∈ rstep k T (readVectors D n T k) ⟨GateOp.and, [a, b]⟩) :
    v ∈ (readVectors (ext n D a b) n T k).getD (ext n D a b).output [] := by
  rw [ext_out]
  apply mem_rstep_or
  right
  rw [getD_last' _ _ _ _ (readVectors_length D n T k)]
  exact hv

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (a : ℕ) :
    a ∈ setList S ↔ ∃ i ∈ S, i.val = a := by
  simp [setList]

lemma setList_nodup {n : ℕ} (S : Finset (Fin n)) : (setList S).Nodup :=
  List.Nodup.map Fin.val_injective ((List.nodup_finRange n).filter _)

lemma setList_length {n : ℕ} (S : Finset (Fin n)) : (setList S).length = S.card := by
  have h : ((List.finRange n).filter fun i => decide (i ∈ S)).toFinset = S := by
    ext i
    simp
  calc (setList S).length
      = ((List.finRange n).filter fun i => decide (i ∈ S)).length := by simp [setList]
    _ = ((List.finRange n).filter fun i => decide (i ∈ S)).toFinset.card :=
        (List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)).symm
    _ = S.card := by rw [h]

lemma step (n : ℕ) (D : Circuit) (hD : Monotone2 D) (S : Finset (Fin n)) (hc : S.card = 2)
    (hS : D.eval (List.ofFn (setInput S)) = true) :
    ∃ D' : Circuit, Monotone2 D' ∧
      (∀ x : Fin n → Bool, D'.eval (List.ofFn x) = D.eval (List.ofFn x)) ∧
      D'.size = D.size + 2 ∧
      (∀ T : List ℕ, readsAtMost D n T 1 = true → readsAtMost D' n T 1 = true) ∧
      readsAtMost D' n (setList S) 1 = true := by
  have hl := setList_length S
  rw [hc] at hl
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have hnd := setList_nodup S
  rw [hab] at hnd
  have hne : a ≠ b := by simpa using hnd
  have ha : a ∈ setList S := by rw [hab]; simp
  have hb : b ∈ setList S := by rw [hab]; simp
  have han : a < n := by
    obtain ⟨i, _, hi⟩ := (mem_setList S a).mp ha
    rw [← hi]
    exact i.isLt
  have hbn : b < n := by
    obtain ⟨i, _, hi⟩ := (mem_setList S b).mp hb
    rw [← hi]
    exact i.isLt
  have ho : D.output < n + D.gates.length := by
    by_contra hcon
    have hf : D.eval (List.ofFn (setInput S)) = false :=
      List.getD_eq_default _ _ (by
        show (scan boolStep D.gates _).length ≤ _
        rw [scan_length]
        simp
        omega)
    rw [hf] at hS
    exact Bool.false_ne_true hS
  refine ⟨ext n D a b, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [ext, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hD g hg
    · simp
    · simp
  · intro x
    rw [ext_eval n D a b _ (by simp) han hbn ho]
    cases h : ((List.ofFn x).getD a false && (List.ofFn x).getD b false) with
    | false => simp
    | true =>
      rw [Bool.and_eq_true] at h
      have hle : ∀ i, (List.ofFn (setInput S)).getD i false = true →
          (List.ofFn x).getD i false = true := by
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at hi
          have hiS : (⟨i, hin⟩ : Fin n) ∈ S := by simpa [setInput] using hi
          have hmem : i ∈ setList S := (mem_setList S i).mpr ⟨⟨i, hin⟩, hiS, rfl⟩
          rw [hab] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · exact h.1
          · exact h.2
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          exact absurd hi Bool.false_ne_true
      rw [eval_mono D hD _ _ (by simp) hle hS]
      rfl
  · simp [ext, Circuit.size]
  · intro T hT
    unfold readsAtMost at hT ⊢
    rw [List.any_eq_true] at hT ⊢
    obtain ⟨v, hv, hvk⟩ := hT
    exact ⟨v, ext_pass n D a b T 1 v hv, hvk⟩
  · unfold readsAtMost
    rw [List.any_eq_true]
    have hua : ((setList S).map fun j => if j = a then min 1 (1 + 1) else 0) ∈
        (readVectors D n (setList S) 1).getD a [] := by
      rw [readVectors_leaf D n _ 1 a han]
      simp [leafVectors, ha]
    have hub : ((setList S).map fun j => if j = b then min 1 (1 + 1) else 0) ∈
        (readVectors D n (setList S) 1).getD b [] := by
      rw [readVectors_leaf D n _ 1 b hbn]
      simp [leafVectors, hb]
    have hmem := mem_rstep_and 1 (setList S) (readVectors D n (setList S) 1) a b _ _ hua hub
    refine ⟨_, ext_new n D a b (setList S) 1 _ hmem, ?_⟩
    rw [capAdd_map, capAdd_map, List.all_eq_true]
    intro t ht
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    by_cases h1 : j = a
    · have h2 : j ≠ b := fun h => hne (h1.symm.trans h)
      simp [h1, h2, hne]
    · by_cases h2 : j = b
      · subst h2
        simp [h1]
      · simp [h1, h2]

lemma extend (n : ℕ) (C : Circuit) : ∀ (L : List (Finset (Fin n))) (D : Circuit),
    Monotone2 D → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    (∀ S ∈ L, S.card = 2 ∧ C.eval (List.ofFn (setInput S)) = true) →
    ∃ D' : Circuit, Monotone2 D' ∧
      (∀ x : Fin n → Bool, D'.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      D'.size = D.size + 2 * L.length ∧
      (∀ T : List ℕ, readsAtMost D n T 1 = true → readsAtMost D' n T 1 = true) ∧
      ∀ S ∈ L, readsAtMost D' n (setList S) 1 = true := by
  intro L
  induction L with
  | nil =>
    intro D hD hf _
    exact ⟨D, hD, hf, by simp, fun _ h => h, by simp⟩
  | cons S L ih =>
    intro D hD hf hL
    have hS := hL S (by simp)
    obtain ⟨D1, hD1, hf1, hs1, hp1, hn1⟩ := step n D hD S hS.1 (by rw [hf]; exact hS.2)
    obtain ⟨D2, hD2, hf2, hs2, hp2, hn2⟩ := ih D1 hD1 (fun x => by rw [hf1, hf])
      (fun S' hS' => hL S' (by simp [hS']))
    refine ⟨D2, hD2, hf2, ?_, fun T hT => hp2 T (hp1 T hT), ?_⟩
    · rw [hs2, hs1, List.length_cons]
      omega
    · intro S' hS'
      rcases List.mem_cons.mp hS' with rfl | h
      · exact hp2 _ hn1
      · exact hn2 S' h

end PEqualNP.Outside.L_meta_7344

theorem PEqualNP.Outside.L_meta_7344 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Finset (Fin x1)), PEqualNP.ReadK.IsPrimeImplicant x1 x2 x4 → x4.card = (2 : ℕ)) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ PEqualNP.ReadK.IsReadK x1 x5 (1 : ℕ) ∧ x5.size + (1 : ℕ) ≤ (3 : ℕ) * (x2.size + {x6 ∈ (List.finRange x1).toFinset.powerset | PEqualNP.ReadK.IsPrimeImplicant x1 x2 x6 ∧ PEqualNP.ReadK.readsAtMost x2 x1 (PEqualNP.ReadK.setList x6) (1 : ℕ) = Bool.false}.card + (1 : ℕ)) ∧ ∀ (x6 : Fin x1 → Bool), x5.eval (List.ofFn x6) = x2.eval (List.ofFn x6) := by
  intro n C hC hcard
  obtain ⟨D, hD, hf, hs, hp, hn⟩ := PEqualNP.Outside.L_meta_7344.extend n C
    ({x6 ∈ (List.finRange n).toFinset.powerset | PEqualNP.ReadK.IsPrimeImplicant n C x6 ∧
      PEqualNP.ReadK.readsAtMost C n (PEqualNP.ReadK.setList x6) (1 : ℕ) = Bool.false}).toList
    C hC (fun _ => rfl) (by
      intro S hS
      rw [Finset.mem_toList, Finset.mem_filter] at hS
      exact ⟨hcard S hS.2.1, hS.2.1.1⟩)
  refine ⟨D, hD, ?_, ?_, hf⟩
  · intro S hS
    have hSC : PEqualNP.ReadK.IsPrimeImplicant n C S := by
      have hfun : PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C :=
        funext hf
      unfold PEqualNP.ReadK.IsPrimeImplicant at hS ⊢
      rw [hfun] at hS
      exact hS
    cases hr : PEqualNP.ReadK.readsAtMost C n (PEqualNP.ReadK.setList S) 1 with
    | true => exact hp _ hr
    | false =>
      apply hn S
      rw [Finset.mem_toList, Finset.mem_filter]
      refine ⟨?_, hSC, hr⟩
      rw [Finset.mem_powerset]
      intro i _
      simp
  · rw [hs, Finset.length_toList]
    omega
