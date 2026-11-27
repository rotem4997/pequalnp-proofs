import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Move the supplied negation to the front and bypass any gate that negates it.
-- With no such gate, the remaining circuit needs both a binary reader and a NOT.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4035_1
    (lower : ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 18)
    (one : let graph := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      let readers := fun C : Circuit =>
        (Finset.univ : Finset (Fin C.gates.length)).filter fun i =>
          (C.gates.get i).op.eval [false] = false ∧ 10 ∈ (C.gates.get i).inputs
      ∀ D : Circuit, FanInTwo D → D.size ≤ 18 →
        (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = graph x) →
        (∀ j : Fin D.gates.length,
          ((D.gates.get j).op = GateOp.not → (D.gates.get j).inputs.head? ≠ some 0) ∧
          ((D.gates.get j).op ≠ GateOp.not → 0 ∉ (D.gates.get j).inputs)) →
        (∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.head? ≠ some 10) →
        (∃ g ∈ D.gates, g.op = GateOp.not) → (readers D).card = 1 → False)
    (two : let graph := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      let readers := fun C : Circuit =>
        (Finset.univ : Finset (Fin C.gates.length)).filter fun i =>
          (C.gates.get i).op.eval [false] = false ∧ 10 ∈ (C.gates.get i).inputs
      ∀ D : Circuit, FanInTwo D → D.size ≤ 18 →
        (∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = graph x) →
        (∀ j : Fin D.gates.length,
          ((D.gates.get j).op = GateOp.not → (D.gates.get j).inputs.head? ≠ some 0) ∧
          ((D.gates.get j).op ≠ GateOp.not → 0 ∉ (D.gates.get j).inputs)) →
        (∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.head? ≠ some 10) →
        (∃ g ∈ D.gates, g.op = GateOp.not) → (readers D).card = 2 → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step w g)).length = _
      rw [ih]
      simp [step]
      omega
  have run_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have map_value (r : ℕ → ℕ) (g : Gate) (w v : List Bool)
      (h : ∀ i, w.getD i false = v.getD (r i) false) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (((g.inputs.map r).map fun i => v.getD i false)) := by
    rw [List.map_map]
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i _
    exact h i
  have simulate_gap (k : ℕ) (hk : 0 < k) :
      let r := fun i : ℕ => if i = k then 0 else if k < i then i - 1 else i
      let mapped := fun g : Gate => Gate.mk g.op (g.inputs.map r)
      ∀ (gs : List Gate) (w v : List Bool),
        k ≤ v.length → w.length = v.length + 1 →
        (∀ i, w.getD i false = v.getD (r i) false) →
        ∀ i, (run gs w).getD i false = (run (gs.map mapped) v).getD (r i) false := by
    dsimp only
    let r := fun i : ℕ => if i = k then 0 else if k < i then i - 1 else i
    let mapped := fun g : Gate => Gate.mk g.op (g.inputs.map r)
    change ∀ (gs : List Gate) (w v : List Bool), k ≤ v.length → w.length = v.length + 1 →
      (∀ i, w.getD i false = v.getD (r i) false) →
      ∀ i, (run gs w).getD i false = (run (gs.map mapped) v).getD (r i) false
    intro gs
    induction gs with
    | nil => intro w v _ _ h; exact h
    | cons g gs ih =>
      intro w v hkv hl hlook i
      change (run gs (step w g)).getD i false =
        (run (gs.map mapped) (step v (mapped g))).getD (r i) false
      apply ih _ _ (by simp [step]; omega)
      · simp [step, hl]
      · let b := g.op.eval (g.inputs.map fun u => w.getD u false)
        have hg : step v (mapped g) = v ++ [b] := by
          change v ++ [g.op.eval ((g.inputs.map r).map fun i => v.getD i false)] = _
          rw [← map_value r g w v hlook]
        intro j
        change (w ++ [b]).getD j false = (step v (mapped g)).getD (r j) false
        rw [hg]
        by_cases hj : j < w.length
        · have hmap : r j < v.length := by
            dsimp only [r]
            split_ifs <;> omega
          rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hmap]
          exact hlook j
        · have hkj : k < j := by omega
          have hr : r j = j - 1 := by simp [r, hkj, show j ≠ k by omega]
          rw [hr, List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega)]
          congr 1
          omega
  have reroute (D : Circuit) (hD : FanInTwo D) (hsize : D.size ≤ 18)
      (a : Gate) (ha : a ∈ D.gates) (hao : a.op = .not) (hai : a.inputs.head? = some 10)
      (f : (Fin 10 → Bool) → Bool)
      (hEval : ∀ x, D.eval (List.ofFn x ++ [!x 0]) = f x) :
      HasCircuitSize 10 f 18 := by
    obtain ⟨pre, post, hgs⟩ := List.append_of_mem ha
    let k := 11 + pre.length
    let r := fun i : ℕ => if i = k then 0 else if k < i then i - 1 else i
    let mapped := fun g : Gate => Gate.mk g.op (g.inputs.map r)
    let first : Gate := ⟨.not, [0]⟩
    refine ⟨⟨first :: pre ++ post.map mapped, r D.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: pre ++ post.map mapped at hg
      rcases List.mem_cons.mp hg with he | hg
      · subst g
        simp [first]
      · rcases List.mem_append.mp hg with hp | hp
        · exact hD g (by rw [hgs]; simp [hp])
        · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hp
          have horig := hD g₀ (by rw [hgs]; simp [hg₀])
          simpa [mapped] using horig
    · change (first :: pre ++ post.map mapped).length ≤ 18
      change D.gates.length ≤ 18 at hsize
      rw [hgs] at hsize
      simp at hsize ⊢
      omega
    · intro x
      let seed := List.ofFn x ++ [!x 0]
      have hseedLen : seed.length = 11 := by simp [seed]
      have hFirst : step (List.ofFn x) first = seed := by
        simp only [step, first, List.map_cons, List.map_nil, seed]
        change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
        simp [List.getD_eq_getElem?_getD]
      let v := run pre seed
      have hvLen : v.length = k := by simp [v, run_len, hseedLen, k]
      have hv0 : v.getD 0 false = x 0 := by
        rw [run_preserves pre seed 0 (by omega)]
        simp [seed, List.getD_eq_getElem?_getD]
      have hv10 : v.getD 10 false = !x 0 := by
        rw [run_preserves pre seed 10 (by omega)]
        simp [seed, List.getD_eq_getElem?_getD]
      have haStep : step v a = v ++ [x 0] := by
        have haHead : ∃ tail, a.inputs = 10 :: tail := by
          cases h : a.inputs with
          | nil => rw [h] at hai; cases hai
          | cons u tail =>
            rw [h, List.head?_cons, Option.some.injEq] at hai
            exact ⟨tail, by rw [hai]⟩
        obtain ⟨tail, htail⟩ := haHead
        simp only [step, hao, htail, List.map_cons]
        change v ++ [!v.getD 10 false] = _
        rw [hv10, Bool.not_not]
      have hLook (i : ℕ) : (v ++ [x 0]).getD i false = v.getD (r i) false := by
        obtain h | h | h := lt_trichotomy i k
        · rw [List.getD_append _ _ _ _ (by omega)]
          simp [r, show i ≠ k by omega, show ¬ k < i by omega]
        · subst i
          have hAt : (v ++ [x 0]).getD k false = x 0 := by
            rw [← hvLen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
            rfl
          rw [hAt]
          rw [show r k = 0 by simp [r]]
          exact hv0.symm
        · have hi : i ≠ k := by omega
          have hil : v.length + 1 ≤ i := by omega
          have hir : v.length ≤ i - 1 := by omega
          rw [List.getD_eq_default _ _ (by simpa using hil)]
          rw [show r i = i - 1 by simp [r, hi, h]]
          exact (List.getD_eq_default _ _ hir).symm
      have hs := simulate_gap k (by dsimp [k]; omega) post (v ++ [x 0]) v
        hvLen.ge (by simp) hLook D.output
      have hNew : (Circuit.mk (first :: pre ++ post.map mapped) (r D.output)).eval (List.ofFn x) =
          (run (post.map mapped) v).getD (r D.output) false := by
        change ((pre ++ post.map mapped).foldl step (step (List.ofFn x) first)).getD _ false = _
        rw [hFirst, List.foldl_append]
      have hOld : D.eval seed = (run post (v ++ [x 0])).getD D.output false := by
        change (D.gates.foldl step seed).getD D.output false = _
        rw [hgs, List.foldl_append, List.foldl_cons]
        change (run post (step v a)).getD D.output false = _
        rw [haStep]
      rw [hNew, ← hs, ← hOld]
      exact hEval x
  have follow_relation (R : Bool → Bool → Prop) (hfalse : R false false)
      (keep : ℕ → Prop) (gs : List Gate)
      (hgate : ∀ g ∈ gs, ∀ w v : List Bool,
        (∀ i, keep i → R (w.getD i false) (v.getD i false)) →
        R (g.op.eval (g.inputs.map fun i => w.getD i false))
          (g.op.eval (g.inputs.map fun i => v.getD i false)))
      (w v : List Bool) (hlen : w.length = v.length)
      (hlook : ∀ i, keep i → R (w.getD i false) (v.getD i false)) :
      ∀ i, keep i → R ((run gs w).getD i false) ((run gs v).getD i false) := by
    induction gs generalizing w v with
    | nil => exact hlook
    | cons g gs ih =>
      change ∀ i, keep i → R ((run gs (step w g)).getD i false)
        ((run gs (step v g)).getD i false)
      apply ih (fun f hf => hgate f (List.mem_cons_of_mem _ hf))
      · simp [step, hlen]
      · intro i hi
        obtain h | h | h := lt_trichotomy i w.length
        · have hv : i < v.length := by omega
          change R ((w ++ [_]).getD i false) ((v ++ [_]).getD i false)
          rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ hv]
          exact hlook i hi
        · change R ((w ++ [_]).getD i false) ((v ++ [_]).getD i false)
          have he : i = v.length := h.trans hlen
          rw [List.getD_append_right _ _ _ _ h.ge, List.getD_append_right _ _ _ _ he.ge,
            h, hlen, Nat.sub_self]
          exact hgate g (by simp) w v hlook
        · have hw : (step w g).length ≤ i := by simp [step]; omega
          have hv : (step v g).length ≤ i := by simp [step]; omega
          rw [List.getD_eq_default _ _ hw, List.getD_eq_default _ _ hv]
          exact hfalse
  have gate_mono (g : Gate) (hop : g.op = .and ∨ g.op = .or) (w v : List Bool)
      (h : ∀ i ∈ g.inputs, w.getD i false = true → v.getD i false = true) :
      g.op.eval (g.inputs.map fun i => w.getD i false) = true →
        g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
    rcases hop with hop | hop
    · rw [hop]
      change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
      simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, id_eq]
      intro hw i hi
      exact h i hi (hw i hi)
    · rw [hop]
      change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
      simp only [List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
      rintro ⟨i,hi,hv⟩
      exact ⟨i,hi,h i hi hv⟩
  intro D hD hsize hEval hNoRaw hCovered
  obtain ⟨p,q,hCover⟩ := hCovered
  let graph := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let row := fun x : Fin 10 → Bool => List.ofFn x ++ [!x 0]
  have noDirect (g : Gate) (hg : g ∈ D.gates) (ho : g.op = .not) :
      g.inputs.head? ≠ some 10 := by
    intro hi
    exact lower (reroute D hD hsize g hg ho hi graph hEval)
  have rawAvoid (g : Gate) (hg : g ∈ D.gates) :
      (g.op = .not → g.inputs.head? ≠ some 0) ∧ (g.op ≠ .not → 0 ∉ g.inputs) := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    exact hNoRaw ⟨i,hi⟩
  have out0 : D.output ≠ 0 := by
    intro h
    let x : Fin 10 → Bool := fun i => decide (i = 0)
    have hx : (row x).length = 11 := by simp [row]
    have he : (run D.gates (row x)).getD D.output false = graph x := hEval x
    rw [h, run_preserves _ _ _ (by omega)] at he
    exact (by decide : (row x).getD 0 false ≠ graph x) he
  have out10 : D.output ≠ 10 := by
    intro h
    let x : Fin 10 → Bool := fun _ => false
    have hx : (row x).length = 11 := by simp [row]
    have he : (run D.gates (row x)).getD D.output false = graph x := hEval x
    rw [h, run_preserves _ _ _ (by omega)] at he
    exact (by decide : (row x).getD 10 false ≠ graph x) he
  let high : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
  let low : Fin 10 → Bool := fun i => decide (i = 1)
  have hHigh : (run D.gates (row high)).getD D.output false = true :=
    (hEval high).trans (by decide : graph high = true)
  have hLow : (run D.gates (row low)).getD D.output false = false :=
    (hEval low).trans (by decide : graph low = false)
  have lenHigh : (row high).length = 11 := by simp [row]
  have lenLow : (row low).length = 11 := by simp [row]
  have hNotExists : ∃ g ∈ D.gates, g.op = .not := by
    by_contra hNone
    have monoStart (i : ℕ) (hi : i ≠ 0) :
        (row high).getD i false = true → (row low).getD i false = true := by
      have finite : ∀ j : Fin 11, j.val ≠ 0 →
          (row high).getD j.val false = true → (row low).getD j.val false = true := by decide
      by_cases h : i < 11
      · exact finite ⟨i,h⟩ hi
      · rw [List.getD_eq_default _ _ (by omega : (row high).length ≤ i)]
        exact fun hf => Bool.noConfusion hf
    have hGates (g : Gate) (hg : g ∈ D.gates) (w v : List Bool)
        (h : ∀ i, i ≠ 0 → w.getD i false = true → v.getD i false = true) :
        g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
      have hn : g.op ≠ .not := fun he => hNone ⟨g,hg,he⟩
      have ho := (hD g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hn, or_false] at ho
      exact gate_mono g ho w v (fun i hi => h i (fun he => (rawAvoid g hg).2 hn (he ▸ hi)))
    have h := follow_relation (fun a b => a = true → b = true) (by decide)
      (fun i => i ≠ 0) D.gates hGates (row high) (row low) (lenHigh.trans lenLow.symm)
      monoStart D.output out0 hHigh
    rw [hLow] at h
    exact Bool.noConfusion h
  let readers := fun C : Circuit =>
    (Finset.univ : Finset (Fin C.gates.length)).filter fun i =>
      (C.gates.get i).op.eval [false] = false ∧ 10 ∈ (C.gates.get i).inputs
  have read_ok (g : Gate) (hg : g ∈ D.gates) (hn : g.op ≠ .not) :
      g.op.eval [false] = false := by
    have h := (hD g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hn, or_false] at h
    rcases h with h | h <;> rw [h] <;> rfl
  have readCap : (readers D).card ≤ 2 := by
    have hSub : readers D ⊆ ({p,q} : Finset (Fin D.gates.length)) := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton]
      have hm := (Finset.mem_filter.mp hi).2
      have hn : (D.gates.get i).op ≠ .not := by
        intro h
        rw [h] at hm
        exact (by decide : GateOp.not.eval [false] ≠ false) hm.1
      exact (hCover i).2 hn hm.2
    exact (Finset.card_le_card hSub).trans Finset.card_le_two
  have hasReader : 0 < (readers D).card := by
    apply Finset.card_pos.mpr
    by_contra hEmpty
    have noBinaryRead (g : Gate) (hg : g ∈ D.gates) (hn : g.op ≠ .not) : 10 ∉ g.inputs := by
      intro hi
      obtain ⟨i, hlt, rfl⟩ := List.mem_iff_getElem.mp hg
      exact hEmpty ⟨⟨i,hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        read_ok _ hg hn, hi⟩⟩
    have sameStart (i : ℕ) (hi : i ≠ 0 ∧ i ≠ 10) :
        (row high).getD i false = (row low).getD i false := by
      have finite : ∀ j : Fin 11, j.val ≠ 0 → j.val ≠ 10 →
          (row high).getD j.val false = (row low).getD j.val false := by decide
      by_cases h : i < 11
      · exact finite ⟨i,h⟩ hi.1 hi.2
      · rw [List.getD_eq_default _ _ (by omega : (row high).length ≤ i),
          List.getD_eq_default _ _ (by omega : (row low).length ≤ i)]
    have hGates (g : Gate) (hg : g ∈ D.gates) (w v : List Bool)
        (h : ∀ i, (i ≠ 0 ∧ i ≠ 10) → w.getD i false = v.getD i false) :
        g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => v.getD i false) := by
      by_cases hn : g.op = .not
      · rw [hn]
        cases hgInputs : g.inputs with
        | nil => rfl
        | cons i tail =>
          have hr := (rawAvoid g hg).1 hn
          have hd := noDirect g hg hn
          rw [hgInputs, List.head?_cons, Ne, Option.some.injEq] at hr hd
          exact congrArg Bool.not (h i ⟨hr,hd⟩)
      · apply congrArg g.op.eval
        apply List.map_congr_left
        intro i hi
        exact h i ⟨fun he => (rawAvoid g hg).2 hn (he ▸ hi),
          fun he => noBinaryRead g hg hn (he ▸ hi)⟩
    have he := follow_relation Eq rfl (fun i => i ≠ 0 ∧ i ≠ 10) D.gates hGates
      (row high) (row low) (lenHigh.trans lenLow.symm) sameStart D.output ⟨out0,out10⟩
    rw [hHigh, hLow] at he
    exact Bool.noConfusion he
  by_cases hOne : (readers D).card = 1
  · exact one D hD hsize hEval hNoRaw noDirect hNotExists hOne
  · have hTwo : (readers D).card = 2 := by omega
    exact two D hD hsize hEval hNoRaw noDirect hNotExists hTwo
