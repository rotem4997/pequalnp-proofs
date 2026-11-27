import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2245_aux

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

private theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private def rename (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

private def skip (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private theorem opposite {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

private theorem bool_flow (t b b' c c' : Bool)
    (hb : b = t → b' = t) (hc : c = t → c' = t) :
    ((b && c) = t → (b' && c') = t) ∧ ((b || c) = t → (b' || c') = t) := by
  cases t <;> cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

private theorem gate_flow (t : Bool) (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (p q : ℕ → Bool)
    (h : ∀ i, p i = t → q i = t) :
    op.eval (ins.map p) = t → op.eval (ins.map q) = t := by
  induction ins with
  | nil => exact id
  | cons i ins ih =>
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.all_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).1
    · simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq] at ih ⊢
      exact (bool_flow t _ _ _ _ (h i) ih).2

private theorem run_flow (t : Bool) (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hp : ∀ i < w.length, f i < v.length)
    (hs : ∀ i, w.length ≤ i → f i = v.length + (i - w.length))
    (hf : ∀ i, w.getD i false = t → v.getD (f i) false = t) :
    ∀ i, (run gs w).getD i false = t →
      (run (gs.map (rename f)) v).getD (f i) false = t := by
  induction gs generalizing w v with
  | nil => exact hf
  | cons g gs ih =>
    have ht (a : Gate) (ha : a ∈ gs) : a.op = .and ∨ a.op = .or := hops a (List.mem_cons_of_mem _ ha)
    have hstep : value g w = t → value (rename f g) v = t := by
      simpa only [value, rename, List.map_map, Function.comp_def] using
        gate_flow t g.op (hops g List.mem_cons_self) g.inputs
          (fun i => w.getD i false) (fun i => v.getD (f i) false) hf
    simp only [List.map_cons, run_cons]
    have hw : (w ++ [value g w]).length = w.length + 1 := by simp
    have hv : (v ++ [value (rename f g) v]).length = v.length + 1 := by simp
    apply ih _ _ ht
    · intro i hi
      rw [hw] at hi
      rw [hv]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
      · exact (hp i hlt).trans (Nat.lt_succ_self _)
      · rw [hs _ le_rfl, Nat.sub_self, Nat.add_zero]
        omega
    · intro i hi
      rw [hw] at hi
      rw [hw, hv, hs i (by omega)]
      omega
    · intro i
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hp i hi)]
        exact hf i
      · rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with rfl | hi'
        · rw [hs _ le_rfl, Nat.sub_self, Nat.add_zero]
          simpa using hstep
        · rw [List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by rw [hs _ (by omega)]; omega)]
          exact id

private theorem local_flow (g : Gate) (w : List Bool) (a : ℕ) (ha : a ∈ g.inputs)
    (hop : g.op = .and ∨ g.op = .or) :
    value g w = g.op.eval [] → w.getD a false = g.op.eval [] := by
  rcases hop with h | h
  · simp only [value, h, GateOp.eval, List.all_eq_true, id_eq, List.all_nil]
    exact fun ho => ho _ (List.mem_map_of_mem ha)
  · simp only [value, h, GateOp.eval, List.any_nil, id_eq]
    intro hf
    by_contra! ht
    have hv : (g.inputs.map fun i => w.getD i false).any id = true := by
      apply List.any_eq_true.mpr
      exact ⟨_, List.mem_map_of_mem ha, by simpa using ht⟩
    rw [hf] at hv
    contradiction

private theorem bypass (S : Bool → List Bool → Prop) (C : Circuit)
    (hlength : ∀ t w, S t w → w.length = 26)
    (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (hfit : ∀ t w, S t w → C.eval w = t)
    (j : ℕ) (hj : j < C.gates.length) (a : ℕ) (ha : a ∈ (gateAt C j).inputs)
    (hmiss : ¬ ∃ w, S (!(gateAt C j).op.eval []) w ∧
      (C.wires w).getD a false = !(!(gateAt C j).op.eval []) ∧
      (C.wires w).getD (26+j) false = !(gateAt C j).op.eval []) :
    ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧ (∀ t w, S t w → D.eval w = t)) ∧
      D.size < C.size := by
  let front := C.gates.take j
  let tail := C.gates.drop (j+1)
  let g := C.gates[j]
  let k := 26+j
  let f := skip k a
  let new := front ++ tail.map (rename f)
  have hg : gateAt C j = g := List.getD_eq_getElem _ _ hj
  have hmema : a ∈ g.inputs := hg ▸ ha
  have hlt : a < k := hb j hj a ha
  have hop : g.op = .and ∨ g.op = .or := by simpa using (hm g (List.getElem_mem hj)).1
  have hfront : front.length = j := by simp [front, Nat.min_eq_left hj.le]
  have hsplit : C.gates = front ++ g :: tail := by
    rw [show g :: tail = C.gates.drop j from (List.drop_eq_getElem_cons hj).symm]
    exact (List.take_append_drop j C.gates).symm
  have hnew : new.length = C.gates.length - 1 := by
    simp [new, hfront, tail]
    omega
  refine ⟨⟨new, f C.output⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro b hmem
    change b ∈ front ++ tail.map (rename f) at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hm b (List.mem_of_mem_take hmem)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      have hh := hm q (List.mem_of_mem_drop hq)
      exact ⟨hh.1, by simpa [rename] using hh.2⟩
  · intro i hi u hu
    change i < new.length at hi
    change u ∈ (new.getD i ⟨.or, []⟩).inputs at hu
    rw [List.getD_eq_getElem _ _ hi] at hu
    by_cases hif : i < front.length
    · change u ∈ ((front ++ tail.map (rename f))[i]'hi).inputs at hu
      rw [List.getElem_append_left hif] at hu
      have ho : i < C.gates.length := by omega
      have hh : u ∈ (gateAt C i).inputs := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ ho]
        simpa [front] using hu
      exact hb i ho u hh
    · change u ∈ ((front ++ tail.map (rename f))[i]'hi).inputs at hu
      rw [List.getElem_append_right (by omega)] at hu
      simp only [List.getElem_map] at hu
      have hv : i + 1 < C.gates.length := by omega
      have he : i - front.length + (j+1) = i+1 := by omega
      have hu' : u ∈ (rename f C.gates[i+1]).inputs := by
        simpa only [tail, List.getElem_drop, Nat.add_comm (j+1), he] using hu
      obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hu'
      have hvGate : gateAt C (i+1) = C.gates[i+1] := List.getD_eq_getElem _ _ hv
      have hq := hb (i+1) hv v (by rwa [hvGate])
      dsimp [f, skip]
      split_ifs <;> omega
  · intro t w hw
    let pre := run front w
    let both := pre ++ [value g pre]
    have hp : pre.length = k := by simp [pre, run_length, hlength t w hw, hfront, k]
    have hp' : both.length = k+1 := by simp [both,hp]
    have hW : C.wires w = run tail both := by
      change run C.gates w = _
      rw [hsplit, run_append, run_cons]
    have hgate : (C.wires w).getD k false = value g pre := by
      rw [hW, run_preserves _ _ _ (by omega)]
      change (pre ++ [value g pre]).getD k false = _
      rw [← hp]
      simp
    have hwire : (C.wires w).getD a false = pre.getD a false := by
      rw [hW, run_preserves _ _ _ (by omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hlocal : value g pre = t → pre.getD a false = t := by
      intro hv
      by_cases ht : t = g.op.eval []
      · rw [ht] at hv ⊢
        exact local_flow g pre a hmema hop hv
      · have he : t = !g.op.eval [] := opposite ht
        by_contra hn
        have hn' : pre.getD a false = !t := opposite hn
        apply hmiss
        refine ⟨w, ?_, ?_, ?_⟩
        · simpa only [hg, ← he] using hw
        · rw [hg, ← he, hwire, hn']
        · rw [hg, ← he]
          exact hgate.trans hv
    have hflow : ∀ i, both.getD i false = t → pre.getD (f i) false = t := by
      intro i hi
      by_cases hi' : i < k
      · have hix : f i = i := by simp [f, skip, hi']
        rw [hix]
        exact (List.getD_append _ _ _ _ (by omega : i < pre.length)) ▸ hi
      · by_cases hi'' : i = k
        · subst i
          have hix : f k = a := by simp [f, skip]
          rw [hix]
          apply hlocal
          change (pre ++ [value g pre]).getD k false = t at hi
          simpa [← hp] using hi
        · have hix : f i = i-1 := by simp [f, skip, hi', hi'']
          rw [hix, List.getD_eq_default _ _ (by omega)]
          rwa [List.getD_eq_default _ _ (by omega : both.length ≤ i)] at hi
    have hresult := run_flow t f tail both pre
      (fun z hz => by simpa using (hm z (List.mem_of_mem_drop hz)).1)
      (by intro i hi; dsimp [f, skip]; split_ifs <;> omega)
      (by intro i hi; dsimp [f, skip]; split_ifs <;> omega)
      hflow C.output
    change (run new w).getD (f C.output) false = t
    rw [show new = front ++ tail.map (rename f) from rfl, run_append]
    apply hresult
    rw [← hW]
    exact hfit t w hw
  · change new.length < C.gates.length
    omega

private theorem result (S : Bool → List Bool → Prop) (hlength : ∀ t w, S t w → w.length = 26)
    (C : Circuit) (h : Monotone2 C ∧ ReadsBack 26 C ∧ ∀ t w, S t w → C.eval w = t) :
    (∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧ (∀ t w, S t w → D.eval w = t)) ∧
      D.size < C.size) ∨
    ∀ j < C.gates.length, ∀ a ∈ (gateAt C j).inputs, ∃ w,
      S (!(gateAt C j).op.eval []) w ∧
      (C.wires w).getD a false = !(!(gateAt C j).op.eval []) ∧
      (C.wires w).getD (26+j) false = !(gateAt C j).op.eval [] := by
  by_cases hs : ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧
      (∀ t w, S t w → D.eval w = t)) ∧ D.size < C.size
  · exact Or.inl hs
  · right
    intro j hj a ha
    by_contra hn
    exact hs (bypass S C hlength h.1 h.2.1 h.2.2 j hj a ha hn)

end PEqualNP.Outside.L_meta_2245_aux

theorem PEqualNP.Outside.L_meta_2245 :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x4 x6 ∨ x5 x6 := by
  intro offsets S fits smaller essential C h
  apply L_meta_2245_aux.result S _ C h
  intro t w hw
  cases t
  · have hh : ∃ A : Finset (Fin 13), A.card = 4 ∧
        (∀ l : Fin 13, {p ∈ A | p - l ∈ offsets}.card ≤ 2) ∧
        w = List.ofFn (fun p : Fin 13 => decide (p ∈ A)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ A, p - l ∉ offsets)) := hw
    obtain ⟨A, _, _, rfl⟩ := hh
    simp
  · have hh : ∃ p l : Fin 13, p - l ∈ offsets ∧
        w = List.ofFn (fun q : Fin 13 => decide (q = p)) ++
          List.ofFn (fun q : Fin 13 => decide (q = l)) := hw
    obtain ⟨p, l, _, rfl⟩ := hh
    simp

