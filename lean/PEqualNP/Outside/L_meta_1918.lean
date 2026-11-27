import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1918_aux

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

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
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp <;> omega

private theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def shape (k : ℕ) (g : Gate) : Prop :=
  (∃ a b : ℕ, a ≤ b ∧ b ≤ k ∧ (g = ⟨.and, [a,b]⟩ ∨ g = ⟨.or, [a,b]⟩)) ∨
  ∃ a : ℕ, a ≤ k ∧ g = ⟨.not, [a]⟩

private theorem shape_mono {k l : ℕ} {g : Gate} (h : shape k g) (hkl : k ≤ l) :
    shape l g := by
  rcases h with ⟨a, b, hab, hb, hg⟩ | ⟨a, ha, hg⟩
  · exact Or.inl ⟨a, b, hab, hb.trans hkl, hg⟩
  · exact Or.inr ⟨a, ha.trans hkl, hg⟩

private def binary (op : GateOp) (k a b : ℕ) : Gate :=
  let i := min a k
  let j := min b k
  ⟨op, [min i j, max i j]⟩

private def normalizeGate (k : ℕ) : Gate → Gate
  | ⟨.and, []⟩ => ⟨.not, [k]⟩
  | ⟨.or, []⟩ => ⟨.or, [k,k]⟩
  | ⟨.and, [a]⟩ => binary .and k a a
  | ⟨.or, [a]⟩ => binary .or k a a
  | ⟨.and, a :: b :: _⟩ => binary .and k a b
  | ⟨.or, a :: b :: _⟩ => binary .or k a b
  | ⟨.not, []⟩ => ⟨.not, [k]⟩
  | ⟨.not, a :: _⟩ => ⟨.not, [min a k]⟩
  | g => g

private theorem binary_shape (k a b : ℕ) {op : GateOp}
    (hop : op = .and ∨ op = .or) : shape k (binary op k a b) := by
  apply Or.inl
  refine ⟨min (min a k) (min b k), max (min a k) (min b k), ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (le_max_left _ _)
  · exact max_le (min_le_right _ _) (min_le_right _ _)
  · rcases hop with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem normalizeGate_shape (k : ℕ) (g : Gate) (hg : allowed g) :
    shape k (normalizeGate k g) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact Or.inr ⟨k, le_rfl, rfl⟩
    · exact binary_shape k a a (Or.inl rfl)
    · exact binary_shape k a b (Or.inl rfl)
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact Or.inl ⟨k, k, le_rfl, le_rfl, Or.inr rfl⟩
    · exact binary_shape k a a (Or.inr rfl)
    · exact binary_shape k a b (Or.inr rfl)
  | not =>
    cases ins with
    | nil => exact Or.inr ⟨k, le_rfl, rfl⟩
    | cons a _ => exact Or.inr ⟨min a k, min_le_right _ _, rfl⟩
  | mod _ => simp [allowed] at hg
  | maj => simp [allowed] at hg

private theorem clipped (w : List Bool) (i : ℕ) :
    w.getD (min i w.length) false = w.getD i false := by
  by_cases hi : i ≤ w.length
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (le_refl _),
      List.getD_eq_default _ _ (by omega : w.length ≤ i)]

private theorem binary_value (w : List Bool) (a b : ℕ) {op : GateOp}
    (hop : op = .and ∨ op = .or) :
    value (binary op w.length a b) w =
      op.eval [w.getD a false, w.getD b false] := by
  by_cases h : min a w.length ≤ min b w.length
  · simp [binary, value, min_eq_left h, max_eq_right h, clipped, -List.getD_eq_getElem?_getD]
  · have h' : min b w.length ≤ min a w.length := by omega
    rcases hop with rfl | rfl
    · simp [binary, value, min_eq_right h', max_eq_left h', clipped, GateOp.eval,
        Bool.and_comm, -List.getD_eq_getElem?_getD]
    · simp [binary, value, min_eq_right h', max_eq_left h', clipped, GateOp.eval,
        Bool.or_comm, -List.getD_eq_getElem?_getD]

private theorem normalizeGate_value (w : List Bool) (g : Gate) (hg : allowed g) :
    value (normalizeGate w.length g) w = value g w := by
  have hd : w.getD w.length false = false := List.getD_eq_default _ _ le_rfl
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [normalizeGate, value, GateOp.eval, hd]
    · change value (binary .and w.length a a) w = _
      rw [binary_value w a a (Or.inl rfl)]
      simp [value, GateOp.eval]
    · exact binary_value w a b (Or.inl rfl)
    · have : (c :: rest).length + 2 ≤ 2 := hg.2
      simp at this
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [normalizeGate, value, GateOp.eval, hd]
    · change value (binary .or w.length a a) w = _
      rw [binary_value w a a (Or.inr rfl)]
      simp [value, GateOp.eval]
    · exact binary_value w a b (Or.inr rfl)
    · have : (c :: rest).length + 2 ≤ 2 := hg.2
      simp at this
  | not =>
    cases ins <;> simp [normalizeGate, value, GateOp.eval, hd, clipped, -List.getD_eq_getElem?_getD]
  | mod _ => simp [allowed] at hg
  | maj => simp [allowed] at hg

private def normalize (k : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => normalizeGate k g :: normalize (k + 1) gs

private theorem normalize_length (gs : List Gate) (k : ℕ) :
    (normalize k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [normalize, ih]

private theorem normalize_run (gs : List Gate) (h : ∀ g ∈ gs, allowed g) (w : List Bool) :
    run (normalize w.length gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have ht : ∀ a ∈ gs, allowed a := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hv := normalizeGate_value w g (h g List.mem_cons_self)
    rw [normalize, run_cons, run_cons, hv]
    simpa using ih ht (w ++ [value g w])

private theorem normalize_shape (gs : List Gate) (h : ∀ g ∈ gs, allowed g) (k : ℕ)
    (j : Fin (normalize k gs).length) : shape (k + j.val) ((normalize k gs).get j) := by
  induction gs generalizing k with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    change Fin ((normalize (k+1) gs).length + 1) at j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [normalize] using normalizeGate_shape k g (h g List.mem_cons_self)
    · have hj := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) (k+1) j'
      have he : k + (j'.val + 1) = k + 1 + j'.val := by omega
      simpa [normalize, Fin.val_succ, he] using hj

private def copy (i : ℕ) : Gate := ⟨.or, [i,i]⟩

private theorem pad_run (r i : ℕ) (w : List Bool) (hi : i < w.length) :
    run (List.replicate r (copy i)) w = w ++ List.replicate r (w.getD i false) := by
  induction r generalizing w with
  | zero => simp [run, Circuit.wires]
  | succ r ih =>
    rw [List.replicate_succ, run_cons, ih _ (by simp; omega)]
    rw [List.getD_append _ _ _ _ hi]
    simp [copy, value, GateOp.eval, List.replicate_succ, List.append_assoc]

private theorem make (first : Gate) (hshape : shape 9 first) (C : Circuit)
    (hfan : FanInTwo C)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false =
      value first (List.ofFn x))
    (hsize : C.size ≤ 15)
    (hsat : ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) = true)
    (hsingle : ∀ i : Fin 9, C.eval (List.ofFn fun k => decide (k = i)) = false) :
    ∃ gs : List Gate, gs.length = 15 ∧ gs.head? = some first ∧
      (∀ j : Fin gs.length, shape (9 + j.val) (gs.get j)) ∧
      ∀ x : Fin 9 → Bool, (Circuit.mk gs 23).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hle : 9 ≤ C.output := by
    by_contra! h
    let i : Fin 9 := ⟨C.output, h⟩
    let x : Fin 9 → Bool := fun k => decide (k = i)
    have hw : C.output < (List.ofFn x).length := by simpa using h
    have hf := hsingle i
    change (run C.gates (List.ofFn x)).getD C.output false = false at hf
    rw [run_preserves _ _ _ hw, List.getD_eq_getElem _ _ hw, List.getElem_ofFn] at hf
    have ht : x ⟨C.output, h⟩ = true := by simp [x, i]
    exact Bool.noConfusion (ht.symm.trans hf)
  have hlt : C.output < 9 + C.gates.length := by
    by_contra! h
    obtain ⟨x, hx⟩ := hsat
    change (run C.gates (List.ofFn x)).getD C.output false = true at hx
    rw [List.getD_eq_default _ _ (by simpa [run_length] using h)] at hx
    contradiction
  let m := C.output + 1 - 9
  have hm : m ≤ C.gates.length := by dsimp [m]; omega
  have hmpos : 0 < m := by dsimp [m]; omega
  have hms : m ≤ 15 := hm.trans hsize
  have hp : (C.gates.take m).length = m := by simp [List.length_take, min_eq_left hm]
  obtain ⟨g, gs, he⟩ : ∃ g gs, C.gates.take m = g :: gs := by
    cases h : C.gates.take m with
    | nil => rw [h] at hp; simp at hp; omega
    | cons g gs => exact ⟨g, gs, rfl⟩
  have hpre : (g :: gs) ++ C.gates.drop m = C.gates := by
    rw [← he, List.take_append_drop]
  have ht (a : Gate) (ha : a ∈ gs) : allowed a := by
    apply hfan
    rw [← hpre]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
  let core := first :: normalize 10 gs
  let rest := List.replicate (15 - m) (copy C.output)
  have hcore : core.length = m := by
    simp only [core, List.length_cons, normalize_length]
    simpa [he] using hp
  have hrest : rest.length = 15 - m := List.length_replicate
  have hindex : 9 + m = C.output + 1 := by dsimp [m]; omega
  refine ⟨core ++ rest, by simp [hcore, hrest]; omega, rfl, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < core.length
    · rw [List.get_eq_getElem, List.getElem_append_left hj]
      let k : Fin core.length := ⟨j.val, hj⟩
      change shape (9 + k.val) (core.get k)
      change Fin ((normalize 10 gs).length + 1) at k
      refine Fin.cases ?_ (fun q => ?_) k
      · simpa [core] using hshape
      · have he : 9 + (q.val + 1) = 10 + q.val := by omega
        simpa [core, Fin.val_succ, he] using normalize_shape gs ht 10 q
    · rw [List.get_eq_getElem, List.getElem_append_right (by omega)]
      simp only [rest, List.getElem_replicate]
      exact shape_mono (k := C.output) (Or.inl ⟨_, _, le_rfl, le_rfl, Or.inr rfl⟩)
        (by rw [hcore] at hj; omega)
  · intro x
    let w := List.ofFn x
    have hw : w.length = 9 := List.length_ofFn
    have hg : value g w = value first w := by
      have hv := hfirst x
      change (run C.gates w).getD 9 false = value first w at hv
      rw [← hpre, run_append, run_cons,
        run_preserves _ _ _ (by rw [run_length]; simp [hw]; omega),
        run_preserves _ _ _ (by simp [hw]), List.getD_append_right _ _ _ _ (by omega)] at hv
      simpa [hw] using hv
    have hr : run core w = run (g :: gs) w := by
      change run (first :: normalize 10 gs) w = run (g :: gs) w
      rw [run_cons, run_cons, hg]
      simpa [hw] using normalize_run gs ht (w ++ [value first w])
    have hlen : (run core w).length = 9 + m := by rw [run_length, hw, hcore]
    have hout : C.output < (run core w).length := by omega
    have hcorrect : (run core w).getD C.output false = (run C.gates w).getD C.output false := by
      conv_rhs => rw [← hpre, run_append, ← hr,
        run_preserves _ _ _ hout]
    change (run (core ++ rest) w).getD 23 false = (run C.gates w).getD C.output false
    dsimp only [rest]
    rw [← hcorrect, run_append, pad_run _ _ _ hout]
    by_cases hz : m = 15
    · have ho : C.output = 23 := by omega
      rw [hz, Nat.sub_self, List.replicate_zero, List.append_nil, ho]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      exact List.getD_replicate _ (by omega)

end PEqualNP.Outside.L_meta_1918_aux

theorem PEqualNP.Outside.L_meta_1918 :
    ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !x 4) →
      C.size ≤ 15 → (∃ x : Fin 9 → Bool, C.eval (List.ofFn x) = true) →
      (∀ i : Fin 9, C.eval (List.ofFn fun k => decide (k = i)) = false) →
      ∃ gs : List Gate, gs.length = 15 ∧ gs.head? = some ⟨.not, [4]⟩ ∧
        (∀ j : Fin gs.length,
          (∃ a b : ℕ, a ≤ b ∧ b ≤ 9 + j.val ∧
            (gs.get j = ⟨.and, [a,b]⟩ ∨ gs.get j = ⟨.or, [a,b]⟩)) ∨
          ∃ a : ℕ, a ≤ 9 + j.val ∧ gs.get j = ⟨.not, [a]⟩) ∧
        ∀ x : Fin 9 → Bool, (Circuit.mk gs 23).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro C hfan hfirst hsize hsat hsingle
  apply L_meta_1918_aux.make ⟨.not, [4]⟩ (Or.inr ⟨4, by decide, rfl⟩)
    C hfan _ hsize hsat hsingle
  intro x
  simpa [L_meta_1918_aux.value, GateOp.eval, List.getD_eq_getElem, List.getElem_ofFn]
    using hfirst x
