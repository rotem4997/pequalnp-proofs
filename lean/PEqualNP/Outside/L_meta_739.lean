import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_739_aux

open PEqualNP.CircuitLowerBounds

def step {α : Type} (F : GateOp → List α → α) (d : α) (w : List α) (g : Gate) :=
  w ++ [F g.op (g.inputs.map fun i => w.getD i d)]

def deg (op : GateOp) (xs : List ℕ) :=
  @ite ℕ (op = GateOp.and) (lineDegreeGateOpDecEq op GateOp.and) xs.sum (xs.foldr max 0)

theorem step_deg (w : List ℕ) (g : Gate) :
    step deg 0 w g = w ++ [g.lineDegree w] := rfl

theorem run_length {α : Type} (F : GateOp → List α → α) (d : α) (gs : List Gate) (w : List α) :
    (gs.foldl (step F d) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih]; omega

def rename (k a : ℕ) : ℕ := if k < a then a - 1 else a

theorem read_erase {α : Type} (d : α) (w : List α) {k a : ℕ} (hne : a ≠ k) :
    (w.eraseIdx k).getD (rename k a) d = w.getD a d := by
  simp only [List.getD_eq_getElem?_getD, rename]
  by_cases h : k < a
  · have ha : a - 1 + 1 = a := by omega
    simp [h, List.getElem?_eraseIdx_of_ge (show k ≤ a - 1 by omega), ha]
  · simp [h, List.getElem?_eraseIdx_of_lt (show a < k by omega)]

def renamed (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename k)⟩

theorem run_erase {α : Type} (F : GateOp → List α → α) (d : α) (gs : List Gate)
    (k : ℕ) (w : List α) (hk : k < w.length) (hn : ∀ g ∈ gs, k ∉ g.inputs) :
    (gs.map (renamed k)).foldl (step F d) (w.eraseIdx k) =
      (gs.foldl (step F d) w).eraseIdx k := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hreads : (g.inputs.map (rename k)).map (fun i => (w.eraseIdx k).getD i d) =
        g.inputs.map (fun i => w.getD i d) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact read_erase _ _ (fun e => hn g (by simp) (e ▸ ha))
    have hstep : step F d (w.eraseIdx k) (renamed k g) = (step F d w g).eraseIdx k := by
      simp only [step, renamed, hreads, List.eraseIdx_append_of_lt_length hk]
    simp only [List.map_cons, List.foldl_cons, hstep]
    exact ih _ (by simp [step]; omega) (fun h hh => hn h (by simp [hh]))

def erase (n : ℕ) (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (renamed (n + j)), rename (n + j) C.output⟩

theorem erase_run {α : Type} (F : GateOp → List α → α) (d : α)
    (C : Circuit) (w : List α) (j : ℕ) (hj : j < C.gates.length)
    (hn : ∀ g ∈ C.gates.drop (j + 1), w.length + j ∉ g.inputs) :
    ((erase w.length C j).gates.foldl (step F d) w) =
        (C.gates.foldl (step F d) w).eraseIdx (w.length + j) := by
  let b := (C.gates.take j).foldl (step F d) w
  have hb : b.length = w.length + j := by
    simp [b, run_length, List.length_take, Nat.min_eq_left hj.le]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp [List.take_append_drop]
  have hlen : w.length + j < (step F d b C.gates[j]).length := by simp [step, hb]
  unfold erase
  simp only [List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  change ((C.gates.drop (j + 1)).map (renamed (w.length + j))).foldl (step F d) b =
    ((C.gates.drop (j + 1)).foldl (step F d) (step F d b C.gates[j])).eraseIdx (w.length + j)
  rw [← run_erase F d _ _ _ hlen hn]
  congr 1
  simp [step, ← hb, List.eraseIdx_append_of_length_le]

abbrev edge (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ i : Fin C.gates.length, b = n + i.val ∧ a ∈ (C.gates.get i).inputs

theorem erase_data (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (ho : C.output ≠ n + j) (hdead : ∀ b, ¬ edge n C (n + j) b)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    IsMonotoneCircuit (erase n C j) ∧ (∀ g ∈ (erase n C j).gates, g.inputs.length ≤ 2) ∧
    (erase n C j).size < C.size ∧
    (∀ x : List Bool, x.length = n → (erase n C j).eval x = C.eval x) ∧
    ∀ marks, (erase n C j).lineDeg n marks = C.lineDeg n marks := by
  have hn : ∀ g ∈ C.gates.drop (j + 1), n + j ∉ g.inputs := by
    intro g hg ha
    obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hg
    have hk' : j + 1 + k < C.gates.length := by simp at hk; omega
    apply hdead (n + (j + 1 + k))
    refine ⟨by omega, ⟨j + 1 + k, hk'⟩, rfl, ?_⟩
    rw [← hkg] at ha
    simpa using ha
  have hshape : ∀ g ∈ (erase n C j).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simp only [erase, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact ⟨hm _ (List.mem_of_mem_take hg), hf _ (List.mem_of_mem_take hg)⟩
    · have hh := List.mem_of_mem_drop hg'
      simpa [renamed] using And.intro (hm _ hh) (hf _ hh)
  refine ⟨fun g hg => (hshape g hg).1, fun g hg => (hshape g hg).2, ?_, ?_, ?_⟩
  · simp [erase, Circuit.size, List.length_take, Nat.min_eq_left hj.le]
    omega
  · intro x hx
    have h := erase_run GateOp.eval false C x j hj (by simpa [hx] using hn)
    rw [hx] at h
    change (((erase n C j).gates.foldl (step GateOp.eval false) x)).getD
      (rename (n + j) C.output) false = _
    rw [h, read_erase _ _ ho]
    rfl
  · intro marks
    let w := (List.range n).map fun i => if i ∈ marks then 1 else 0
    have hw : w.length = n := by simp [w]
    have h := erase_run deg 0 C w j hj (by simpa [hw] using hn)
    rw [hw] at h
    unfold Circuit.lineDeg Circuit.lineDegrees
    change ((erase n C j).gates.foldl _ w).getD (rename (n + j) C.output) 0 = _
    simp only [← step_deg]
    rw [h, read_erase _ _ ho]

theorem live_circuit (n : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ D : Circuit, IsMonotoneCircuit D ∧ (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      D.size ≤ C.size ∧ (∀ j : Fin D.gates.length, Relation.ReflTransGen (edge n D) (n + j.val) D.output) ∧
      (∀ x : List Bool, x.length = n → D.eval x = C.eval x) ∧
      ∀ marks, D.lineDeg n marks = C.lineDeg n marks := by
  classical
  induction hs : C.size using Nat.strong_induction_on generalizing C with
  | ind s ih =>
    let bad := Finset.univ.filter fun j : Fin C.gates.length =>
      ¬ Relation.ReflTransGen (edge n C) (n + j.val) C.output
    by_cases hb : bad.Nonempty
    · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image bad Fin.val hb
      have hnot := (Finset.mem_filter.mp hj).2
      have hout : C.output ≠ n + j.val := fun h => hnot (h ▸ Relation.ReflTransGen.refl)
      have hd : ∀ b, ¬ edge n C (n + j.val) b := by
        rintro b ⟨hlt, i, rfl, hi⟩
        let he : edge n C (n + j.val) (n + i.val) := ⟨hlt, i, rfl, hi⟩
        have hi' : i ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun hp => hnot (hp.head he)⟩
        have hle := hmax i hi'
        omega
      obtain ⟨hm', hf', hsz, he, hd'⟩ := erase_data n C j.val j.isLt hout hd hm hf
      obtain ⟨D, hD, hDf, hsD, hl, heD, hdD⟩ :=
        ih _ (hs ▸ hsz) _ hm' hf' rfl
      exact ⟨D, hD, hDf, hsD.trans (hs ▸ hsz.le), hl, fun x hx => (heD x hx).trans (he x hx),
        fun m => (hdD m).trans (hd' m)⟩
    · refine ⟨C, hm, hf, hs.le, ?_, fun _ _ => rfl, fun _ => rfl⟩
      intro j
      by_contra h
      exact hb ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩⟩

abbrev Signal := Bool ⊕ ℕ

def signalValue (w : List Bool) : Signal → Bool
  | .inl b => b
  | .inr i => w.getD i false

def bounded (n : ℕ) (s : Signal) : Prop := ∀ i, s = Sum.inr i → i < n

def binary (isAnd : Bool) (next : ℕ) : Signal → Signal → Signal × List Gate
  | .inl a, .inl b => (.inl (if isAnd then a && b else a || b), [])
  | .inl a, .inr b => if a == isAnd then (.inr b, []) else (.inl a, [])
  | .inr a, .inl b => if b == isAnd then (.inr a, []) else (.inl b, [])
  | .inr a, .inr b => (.inr next, [⟨if isAnd then GateOp.and else GateOp.or, [a, b]⟩])

def normalizeGate (isAnd : Bool) (next : ℕ) : List Signal → Signal × List Gate
  | [] => (.inl isAnd, [])
  | [a] => (a, [])
  | a :: b :: _ => binary isAnd next a b

def exactGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem getD_append_keep {α : Type} (d : α) (w t : List α) {i : ℕ} (hi : i < w.length) :
    (w ++ t).getD i d = w.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_new {α : Type} (d : α) (w : List α) (v : α) :
    (w ++ [v]).getD w.length d = v := by
  simp [List.getD_eq_getElem?_getD]

theorem binary_ok (isAnd : Bool) (w : List Bool) (a b : Signal)
    (ha : bounded w.length a) (hb : bounded w.length b) :
    let r := binary isAnd w.length a b
    let w' := r.2.foldl (step GateOp.eval false) w
    r.2.length ≤ 1 ∧ (∀ g ∈ r.2, exactGate g) ∧ bounded w'.length r.1 ∧
      signalValue w' r.1 =
        if isAnd then signalValue w a && signalValue w b else signalValue w a || signalValue w b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => cases isAnd <;> simp [binary, signalValue, bounded]
    | inr b => cases isAnd <;> cases a <;> simp [binary, signalValue, bounded] at * <;> assumption
  | inr a =>
    cases b with
    | inl b => cases isAnd <;> cases b <;> simp [binary, signalValue, bounded] at * <;> assumption
    | inr b =>
      cases isAnd <;>
        simp [binary, exactGate, bounded, signalValue, step, GateOp.eval]

theorem normGate_ok (isAnd : Bool) (w : List Bool) (s : List Signal)
    (hs : s.length ≤ 2) (hbound : ∀ a ∈ s, bounded w.length a) :
    let r := normalizeGate isAnd w.length s
    let w' := r.2.foldl (step GateOp.eval false) w
    r.2.length ≤ 1 ∧ (∀ g ∈ r.2, exactGate g) ∧ bounded w'.length r.1 ∧
      signalValue w' r.1 =
        (if isAnd then GateOp.and else GateOp.or).eval (s.map (signalValue w)) := by
  rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · cases isAnd <;> simp [normalizeGate, signalValue, GateOp.eval, bounded]
  · cases isAnd <;> simpa [normalizeGate, GateOp.eval] using hbound a (by simp)
  · have h := binary_ok isAnd w a b (hbound a (by simp)) (hbound b (by simp))
    cases isAnd <;> simpa [normalizeGate, GateOp.eval] using h
  · simp at hs

def normalize (n : ℕ) : List Gate → List Signal → List Gate → List Signal × List Gate
  | [], status, done => (status, done)
  | g :: gs, status, done =>
    let sig := g.inputs.map (fun i => status.getD i (.inl false))
    let r := normalizeGate (@decide (g.op = GateOp.and) (lineDegreeGateOpDecEq g.op GateOp.and))
      (n + done.length) sig
    normalize n gs (status ++ [r.1]) (done ++ r.2)

theorem prefix_keep (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl (step GateOp.eval false) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [step]; omega)]
    apply getD_append_keep _ _ _ hi

theorem status_read (status : List Signal) (w : List Bool) (i : ℕ) :
    (status.map (signalValue w)).getD i false =
      signalValue w (status.getD i (.inl false)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases status[i]? <;> rfl

theorem normalize_ok (n : ℕ) (gs : List Gate) (status : List Signal) (done : List Gate)
    (x : List Bool) (hx : x.length = n)
    (hbound : ∀ a ∈ status, bounded (n + done.length) a)
    (hdone : ∀ g ∈ done, exactGate g)
    (hs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    let r := normalize n gs status done
    let w := r.2.foldl (step GateOp.eval false) x
    r.2.length ≤ done.length + gs.length ∧
    (∀ g ∈ r.2, exactGate g) ∧
    r.1.map (signalValue w) =
      gs.foldl (step GateOp.eval false) (status.map (signalValue (done.foldl (step GateOp.eval false) x))) := by
  induction gs generalizing status done with
  | nil => exact ⟨by simp [normalize], hdone, rfl⟩
  | cons g gs ih =>
    let w := done.foldl (step GateOp.eval false) x
    have hw : w.length = n + done.length := by simp [w, hx, run_length]
    let sig := g.inputs.map (fun i => status.getD i (.inl false))
    let b := @decide (g.op = GateOp.and) (lineDegreeGateOpDecEq g.op GateOp.and)
    let r := normalizeGate b (n + done.length) sig
    have hsig : ∀ a ∈ sig, bounded w.length a := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      rw [List.getD_eq_getElem?_getD]
      cases h : status[i]? with
      | none => simp [bounded]
      | some u => simpa [hw] using hbound u (List.mem_of_getElem? h)
    have hlen : sig.length ≤ 2 := by simpa [sig] using (hs g (by simp)).2
    have hgate := normGate_ok b w sig hlen hsig
    rw [hw] at hgate
    change r.2.length ≤ 1 ∧ _ ∧ _ ∧ _ at hgate
    obtain ⟨hl, hex, hbr, hval⟩ := hgate
    have hop : (if b then GateOp.and else GateOp.or) = g.op := by
      rcases (hs g (by simp)).1 with he | he <;> simp [b, he]
    have hbound' : ∀ a ∈ status ++ [r.1], bounded (n + (done ++ r.2).length) a := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · intro i hi
        have := hbound a ha i hi
        simp
        omega
      · simp only [List.mem_singleton] at ha
        subst a
        simpa [hw, run_length, Nat.add_assoc] using hbr
    have hdone' : ∀ h ∈ done ++ r.2, exactGate h := by
      intro h hh
      exact (List.mem_append.mp hh).elim (hdone h) (hex h)
    have hmap : status.map (signalValue (r.2.foldl (step GateOp.eval false) w)) =
        status.map (signalValue w) := by
      apply List.map_congr_left
      intro a ha
      cases a with
      | inl v => rfl
      | inr i => exact prefix_keep _ _ (hw ▸ hbound _ ha i rfl)
    have hreads : sig.map (signalValue w) =
        g.inputs.map (fun i => (status.map (signalValue w)).getD i false) := by
      simp only [sig, List.map_map, Function.comp_def, ← status_read]
    have hstep : (status ++ [r.1]).map
        (signalValue ((done ++ r.2).foldl (step GateOp.eval false) x)) =
        step GateOp.eval false (status.map (signalValue w)) g := by
      simp only [List.foldl_append, List.map_append, List.map_cons, List.map_nil]
      change status.map (signalValue (r.2.foldl (step GateOp.eval false) w)) ++ [_] = _
      rw [hmap, hval, hop, hreads]
      rfl
    obtain ⟨hb', he', hv'⟩ := ih (status ++ [r.1]) (done ++ r.2) hbound' hdone'
      (fun h hh => hs h (by simp [hh]))
    refine ⟨?_, he', ?_⟩
    · change (normalize n gs (status ++ [r.1]) (done ++ r.2)).2.length ≤ _
      simp only [List.length_append] at hb'
      simp only [List.length_cons]
      omega
    · change _ = gs.foldl (step GateOp.eval false) (step GateOp.eval false (status.map (signalValue w)) g)
      rw [← hstep]
      exact hv'

theorem normalize_circuit (n : ℕ) (C : Circuit)
    (hm : IsMonotoneCircuit C) (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ D : Circuit, (∀ g ∈ D.gates, exactGate g) ∧ D.size ≤ C.size ∧
      ∃ σ : ℕ → Signal, ∀ (x : Fin n → Bool) a,
        (C.wires (List.ofFn x)).getD a false = signalValue (D.wires (List.ofFn x)) (σ a) := by
  let t : List Signal := (List.range n).map Sum.inr
  let r := normalize n C.gates t []
  let D : Circuit := ⟨r.2, 0⟩
  have hb : ∀ a ∈ t, bounded (n + ([] : List Gate).length) a := by
    intro a ha i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simpa [List.mem_range, Sum.inr.inj hi] using hj
  have hinit (x : Fin n → Bool) : t.map (signalValue (List.ofFn x)) = List.ofFn x := by
    apply List.ext_getElem
    · simp [t]
    · intro i hi hi'
      simp [t, signalValue, List.getElem?_eq_getElem hi', List.getD_eq_getElem?_getD]
  have hnormal (x : Fin n → Bool) := normalize_ok n C.gates t [] (List.ofFn x) (by simp)
    hb (by simp) (fun g hg => ⟨hm g hg, hf g hg⟩)
  refine ⟨D, (hnormal (fun _ => false)).2.1, ?_, fun a => r.1.getD a (.inl false), ?_⟩
  · simpa [D, r, Circuit.size] using (hnormal (fun _ => false)).1
  · intro x a
    have h := (hnormal x).2.2
    change r.1.map (signalValue (D.wires (List.ofFn x))) =
        C.gates.foldl (step GateOp.eval false) (t.map (signalValue (List.ofFn x))) at h
    rw [hinit] at h
    change _ = C.wires (List.ofFn x) at h
    rw [← h, status_read]

def value (C : Circuit) (x : List Bool) (i : ℕ) := (C.wires x).getD i false

theorem value_gate (C : Circuit) (x : List Bool) (j : Fin C.gates.length) :
    value C x (x.length + j.val) =
      (C.gates.get j).op.eval
        ((C.gates.get j).inputs.map fun i => if i < x.length + j.val then value C x i else false) := by
  let gs := C.gates
  let w := (gs.take j.val).foldl (step GateOp.eval false) x
  have hlen : w.length = x.length + j.val := by
    simp [w, gs, run_length, List.length_take, Nat.min_eq_left j.isLt.le]
  have hs : gs = gs.take j.val ++ gs.get j :: gs.drop (j.val + 1) := by
    simp [List.take_append_drop]
  have hrun : C.wires x =
      ((gs.drop (j.val + 1)).foldl (step GateOp.eval false) (step GateOp.eval false w (gs.get j))) := by
    change gs.foldl (step _ _) x = _
    conv_lhs => rw [hs, List.foldl_append, List.foldl_cons]
  have hread (i : ℕ) (hi : i < w.length) : value C x i = w.getD i false := by
    change (gs.foldl (step _ _) x).getD i false = _
    conv_lhs => rw [← List.take_append_drop j.val gs, List.foldl_append]
    exact prefix_keep _ _ hi
  unfold value
  conv_lhs => rw [hrun]
  rw [prefix_keep _ _ (by simp [step, hlen])]
  rw [← hlen]
  simp only [step, getD_append_new]
  apply congrArg _
  apply List.map_congr_left
  intro i _
  split
  · rename_i hi
    exact (hread i hi).symm
  · rename_i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by omega : w.length ≤ i)]

theorem changed_wire {n : ℕ} (C : Circuit) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n) :
    ∀ j, value C x j ≠ value C y j →
      ∃ i < n, x.getD i false ≠ y.getD i false ∧ Relation.ReflTransGen (edge n C) i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    by_cases hj : j < n
    · refine ⟨j, hj, ?_, .refl⟩
      intro he
      apply h
      change (C.gates.foldl (step _ _) x).getD j false =
        (C.gates.foldl (step _ _) y).getD j false
      rw [prefix_keep _ _ (by omega : j < x.length), prefix_keep _ _ (by omega : j < y.length), he]
    by_cases hk : j < n + C.gates.length
    · let i : Fin C.gates.length := ⟨j - n, by omega⟩
      have hji : j = n + i.val := by dsimp [i]; omega
      have hdiff : ∃ a ∈ (C.gates.get i).inputs, a < j ∧ value C x a ≠ value C y a := by
        by_contra! hn
        apply h
        rw [hji, ← hx, value_gate, hx, ← hy, value_gate, hy]
        apply congrArg _
        apply List.map_congr_left
        intro a ha
        split
        · exact hn a ha (hji.symm ▸ ‹a < n + i.val›)
        · rfl
      obtain ⟨a, ha, hlt, hd⟩ := hdiff
      obtain ⟨p, hp, hxy, hpath⟩ := ih a hlt hd
      exact ⟨p, hp, hxy, hpath.tail ⟨hlt, i, hji, ha⟩⟩
    · apply False.elim
      apply h
      have hzero (w : List Bool) (hw : w.length = n) : value C w j = false := by
        change (C.gates.foldl (step _ _) w).getD j false = false
        have hh : (C.gates.foldl (step GateOp.eval false) w).length ≤ j := by
          rw [run_length, hw]
          omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 hh]
      rw [hzero x hx, hzero y hy]

def single {n : ℕ} (p : Fin n) : Fin n → Bool := fun v => decide (v = p)

theorem single_count {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun v => single p v = true)).card = 1 := by
  have h : Finset.univ.filter (fun v => single p v = true) = {p} := by
    ext v
    simp [single]
  simp [h]

theorem changed_line {P L : ℕ} (C : Circuit) (x : Fin P → Bool) (w : Fin L)
    (h : C.eval (List.ofFn x ++ List.ofFn (single w)) ≠
      C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))) :
    Relation.ReflTransGen (edge (P + L) C) (P + w.val) C.output := by
  obtain ⟨i, hi, hchange, hpath⟩ := changed_wire (n := P + L) C
    (List.ofFn x ++ List.ofFn (single w))
    (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))
    (by simp) (by simp) C.output h
  have hi' : P ≤ i := by
    by_contra! hpt
    apply hchange
    rw [getD_append_keep _ _ _ (by simpa using hpt), getD_append_keep _ _ _ (by simpa using hpt)]
  let u : Fin L := ⟨i - P, by omega⟩
  have hu : i = P + u.val := by dsimp [u]; omega
  have read (y : Fin L → Bool) :
      (List.ofFn x ++ List.ofFn y).getD i false = y u := by
    have hApp : (List.ofFn x).length ≤ i := by simpa using hi'
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hApp, List.length_ofFn]
    simp [u, List.getElem?_ofFn, show i - P < L by omega]
  rw [read, read] at hchange
  have huw : u = w := by simpa [single] using hchange
  simpa [hu, huw] using hpath

end PEqualNP.Outside.L_meta_739_aux

open PEqualNP.Outside.L_meta_739_aux PEqualNP.CircuitLowerBounds in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_739 :
(∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → ∀ (P2 L2 k2 q2 : ℕ) (S2 : Fin L2 → Finset (Fin P2)) (C2 : PEqualNP.CircuitLowerBounds.Circuit), 1 ≤ k2 → 2 ≤ q2 → (∀ w2 : Fin L2, (S2 w2).card = q2) → (∀ w3 w4 : Fin L2, w3 ≠ w4 → (S2 w3 ∩ S2 w4).card ≤ 1) → (∀ (w5 : Fin L2) (p2 : Fin P2), p2 ∈ S2 w5 → ∃ u2 : Fin L2, p2 ∉ S2 u2) → PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C2 → (∀ g2 ∈ C2.gates, g2.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P2 + L2) (Finset.Ico P2 (P2 + L2)) C2 1 → (∀ (x2 : Fin P2 → Bool) (y2 : Fin L2 → Bool), (Finset.univ.filter (fun u3 : Fin L2 => y2 u3 = true)).card = 1 → (Finset.univ.filter (fun p3 : Fin P2 => x2 p3 = true)).card ≤ k2 → C2.eval (List.ofFn x2 ++ List.ofFn y2) = decide (∃ w6 : Fin L2, y2 w6 = true ∧ ∃ p4 ∈ S2 w6, x2 p4 = true)) → ∀ c2 : ℕ, c2 ≤ k2 → c2 + 1 ≤ q2 → L2 * c2 + L2 ≤ C2.size + 1 := by
  classical
  intro count extract P L k q S C hk hq hs hp ha hm hf hd htest c hck hcq
  by_cases hL : L = 0
  · simp [hL]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  obtain ⟨A, hmA, hfA, hsA, hlA, heA, hdA⟩ := live_circuit (P + L) C hm hf
  let N : Finset (Fin L) := Finset.univ.filter fun w =>
    Relation.ReflTransGen (edge (P + L) A) (P + w.val) A.output
  have hN (w : Fin L) : w ∈ N ↔
      Relation.ReflTransGen (edge (P + L) A) (P + w.val) A.output := by
    simp [N]
  have hdegree : HasLineDegree (P + L) (Finset.Ico P (P + L)) A 1 := by
    unfold HasLineDegree at hd ⊢
    rw [hdA]
    exact hd
  obtain ⟨D, T, o, hmD, hfD, hsD, heD⟩ := extract P L A N hmA hfA hdegree hlA hN
  let base (x : Fin P → Bool) := A.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))
  let coeff (w : Fin L) (x : Fin P → Bool) := (D.wires (List.ofFn x)).getD (o w) false
  have he (x : Fin P → Bool) (w : Fin L) :
      A.eval (List.ofFn x ++ List.ofFn (single w)) =
        (base x || decide (w ∈ T ∨ coeff w x = true)) := by
    rw [heD]
    simp [base, coeff, single]
  have hcheck (x : Fin P → Bool) (w : Fin L)
      (hx : (Finset.univ.filter (fun p => x p = true)).card ≤ k) :
      A.eval (List.ofFn x ++ List.ofFn (single w)) = decide (∃ p ∈ S w, x p = true) := by
    rw [heA _ (by simp), htest x (single w) (single_count w) hx]
    simp [single]
  have hzero (w : Fin L) : A.eval (List.ofFn (fun _ : Fin P => false) ++
      List.ofFn (single w)) = false := by
    simpa using hcheck (fun _ => false) w (by simp)
  have hno (w : Fin L) : w ∉ T ∧ coeff w (fun _ => false) = false := by
    have hz := hzero w
    rw [he] at hz
    refine ⟨fun h => by simp [h] at hz, ?_⟩
    cases h : coeff w (fun _ => false)
    · rfl
    · simp [h] at hz
  have hpoint (p : Fin P) : base (single p) = false := by
    let w₀ : Fin L := ⟨0, hLpos⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin L, p ∉ S v := by
      by_cases h : p ∈ S w₀
      · exact ha w₀ p h
      · exact ⟨w₀, h⟩
    have h := hcheck (single p) v ((single_count p).symm ▸ hk)
    rw [he] at h
    by_contra! hb
    simpa [hb, single, hv] using h
  have hone (w : Fin L) (p : Fin P) : coeff w (single p) = true ↔ p ∈ S w := by
    have h := hcheck (single p) w ((single_count p).symm ▸ hk)
    rw [he] at h
    have h' : coeff w (single p) = decide (p ∈ S w) := by
      simpa [hpoint p, (hno w).1, single] using h
    simp [h']
  have hfalse (w : Fin L) (x : Fin P → Bool)
      (hx : (Finset.univ.filter (fun p => x p = true)).card ≤ k)
      (hoff : ∀ p ∈ S w, x p = false) : coeff w x = false := by
    have h := hcheck x w hx
    rw [he] at h
    have hn : ¬ ∃ p ∈ S w, x p = true := by
      rintro ⟨p, hp, ht⟩
      simp [hoff p hp] at ht
    cases hv : coeff w x
    · rfl
    · simp [hv, hn] at h
  have hS (w : Fin L) : (S w).Nonempty :=
    Finset.card_pos.mp (by rw [hs]; omega)
  have hfull : N = Finset.univ := by
    ext w
    simp only [Finset.mem_univ, iff_true]
    apply (hN w).2
    obtain ⟨p, hp⟩ := hS w
    apply changed_line A (single p) w
    have h := hcheck (single p) w ((single_count p).symm ▸ hk)
    change _ ≠ base (single p)
    rw [hpoint p, h]
    simp [single, hp]
  obtain ⟨E, heE, hsE, σ, hn⟩ := normalize_circuit P D hmD hfD
  have hwire (w : Fin L) : ∃ i : ℕ, σ (o w) = Sum.inr i := by
    cases h : σ (o w) with
    | inr i => exact ⟨i, rfl⟩
    | inl b =>
      obtain ⟨p, hp⟩ := hS w
      have h1 := (hone w p).2 hp
      have h2 := (hno w).2
      change (D.wires _).getD (o w) false = true at h1
      change (D.wires _).getD (o w) false = false at h2
      rw [hn, h] at h1 h2
      exact Bool.noConfusion (h2.symm.trans h1)
  choose j hj using hwire
  have hw (w : Fin L) (x : Fin P → Bool) :
      (E.wires (List.ofFn x)).getD (j w) false = coeff w x := by
    dsimp [coeff]
    rw [hn, hj]
    rfl
  have hcost := count P L k S E j (fun _ => c) hp
    (fun w => by rw [hs]; exact hq) heE
    (fun w p => by rw [hw]; exact hone w p)
    (fun w x hx h => by rw [hw]; exact hfalse w x hx h)
    (fun _ => hck) (fun w => by rw [hs]; exact hcq)
  have hmul : L * c ≤ E.size := by simpa using hcost
  rw [hfull] at hsD
  simp only [Finset.card_univ, Fintype.card_fin] at hsD
  omega
