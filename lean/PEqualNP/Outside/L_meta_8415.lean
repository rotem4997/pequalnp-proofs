import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8415

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma runWires_len (gs : List Gate) (init : List Bool) :
    (runWires gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).length = init.length + (gs.length + 1)
    rw [ih, stepWire, List.length_append, List.length_singleton]
    omega

lemma runWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (runWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire init g)).getD i false = init.getD i false
    have hlt : i < (stepWire init g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire init g) hlt, stepWire, getD_append_singleton, ite_eq_left hi]

lemma runWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (runWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (runWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runWires gs (stepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (runWires gs (stepWire init g)).getD i false else false)
      have hlen : init.length < (stepWire init g).length := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, runWires_getD_prefix gs (stepWire init g) init.length hlen]
      have hhead : (stepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [stepWire, getD_append_singleton, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [ite_eq_left hi]
        have hi' : i < (stepWire init g).length := by
          simp only [stepWire, List.length_append, List.length_singleton]
          omega
        rw [runWires_getD_prefix gs (stepWire init g) i hi', stepWire,
          getD_append_singleton, ite_eq_left hi]
      · rw [ite_eq_right hi, getD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (stepWire init g).length + k := by
        simp only [stepWire, List.length_append, List.length_singleton]
        omega
      change (runWires gs (stepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (runWires gs (stepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (stepWire init g) k hk

def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal C x i = x ⟨i, hi⟩ := by
  unfold wireVal
  change (runWires C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [runWires_getD_prefix C.gates (List.ofFn x) i (by simp [hi])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wireVal C x (n + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + j then wireVal C x i else false) := by
  unfold wireVal
  have h := runWires_getD_gate C.gates (List.ofFn x) j hj
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [hlen] at h
  exact h

lemma wireVal_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wireVal C x w = false := by
  unfold wireVal
  apply getD_of_ge
  change (runWires C.gates (List.ofFn x)).length ≤ w
  rw [runWires_len, List.length_ofFn]
  exact hw

def shiftIdx (cut rep i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then rep else i - 1

lemma shiftIdx_lt (cut rep i : ℕ) (h : i < cut) : shiftIdx cut rep i = i := by
  unfold shiftIdx; exact ite_eq_left h

lemma shiftIdx_eq (cut rep : ℕ) : shiftIdx cut rep cut = rep := by
  unfold shiftIdx; rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]

lemma shiftIdx_gt (cut rep i : ℕ) (h : ¬i < cut) (hne : i ≠ cut) :
    shiftIdx cut rep i = i - 1 := by
  unfold shiftIdx; rw [ite_eq_right h, ite_eq_right hne]

lemma deleteGate {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (rep : ℕ)
    (hrep : rep < n + j ∨ rep = n + C.gates.length)
    (heq : ∀ x : Fin n → Bool, wireVal C x (n + j) = wireVal C x rep) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size = C.size - 1 ∧
      ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let gs' : List Gate :=
    C.gates.take j ++ (C.gates.drop (j + 1)).map fun g =>
      ⟨g.op, g.inputs.map (shiftIdx (n + j) rep)⟩
  let C' : Circuit := ⟨gs', shiftIdx (n + j) rep C.output⟩
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs', hlen_take]
    omega
  have hm' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    simp only [C', gs', List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hm g (List.mem_of_mem_take h1)
    · obtain ⟨hop, hlen⟩ := hm g0 (List.mem_of_mem_drop hg0)
      exact ⟨hop, by simpa using hlen⟩
  have hagree : ∀ (x : Fin n → Bool) (w : ℕ),
      (w < n + j → wireVal C' x w = wireVal C x w) ∧
      (∀ k < C.gates.length - (j + 1), w = n + j + k → wireVal C' x w = wireVal C x (n + j + 1 + k)) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      constructor
      · intro hlt
        by_cases hlt_n : w < n
        · rw [wireVal_input C' x w hlt_n, wireVal_input C x w hlt_n]
        · have hj1 : w - n < j := by omega
          have hj1' : w - n < C'.gates.length := by omega
          have hj1c : w - n < C.gates.length := by omega
          have hw_eq : n + (w - n) = w := by omega
          rw [← hw_eq, wireVal_gate C' x (w - n) hj1', wireVal_gate C x (w - n) hj1c]
          have hg_eq : C'.gates[w - n] = C.gates[w - n] := by
            simp only [C', gs']
            rw [List.getElem_append_left (by rw [hlen_take]; exact hj1)]
            simp
          rw [hg_eq]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil, ite_eq_left hil]
            exact (ih i (by omega)).1 (by omega)
          · rw [ite_eq_right hil, ite_eq_right hil]
      · intro k hk hw
        subst hw
        have hk' : j + k < C'.gates.length := by omega
        have hkc : j + 1 + k < C.gates.length := by omega
        have hidx1 : n + (j + k) = n + j + k := by omega
        have hidx2 : n + (j + 1 + k) = n + j + 1 + k := by omega
        rw [← hidx1, ← hidx2, wireVal_gate C' x (j + k) hk', wireVal_gate C x (j + 1 + k) hkc]
        have hg_eq : C'.gates[j + k] =
            ⟨(C.gates[j + 1 + k]).op, (C.gates[j + 1 + k]).inputs.map (shiftIdx (n + j) rep)⟩ := by
          simp only [C', gs']
          rw [List.getElem_append_right (by rw [hlen_take]; omega)]
          simp only [hlen_take, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_drop]
        rw [hg_eq, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        by_cases h1 : i < n + j
        · simp only [shiftIdx_lt _ _ _ h1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          exact (ih i (by omega)).1 h1
        · by_cases h2 : i = n + j
          · subst h2
            simp only [shiftIdx_eq]
            rw [ite_eq_left (show n + j < n + (j + 1 + k) by omega), heq x]
            rcases hrep with hrl | hre
            · rw [ite_eq_left (by omega)]
              exact (ih rep (by omega)).1 hrl
            · rw [hre, ite_eq_right (by omega), wireVal_ge C x (n + C.gates.length) (le_refl _)]
          · simp only [shiftIdx_gt _ _ _ h1 h2]
            by_cases h3 : i < n + (j + 1 + k)
            · rw [ite_eq_left (by omega), ite_eq_left h3]
              have h4 := (ih (i - 1) (by omega)).2 (i - 1 - (n + j)) (by omega) (by omega)
              have h5 : n + j + 1 + (i - 1 - (n + j)) = i := by omega
              rw [h5] at h4
              exact h4
            · rw [ite_eq_right (by omega), ite_eq_right h3]
  refine ⟨C', hm', hlen', ?_⟩
  intro x
  change wireVal C' x (shiftIdx (n + j) rep C.output) = wireVal C x C.output
  simp only [shiftIdx]
  by_cases h1 : C.output < n + j
  · rw [ite_eq_left h1]
    exact (hagree x C.output).1 h1
  · rw [ite_eq_right h1]
    by_cases h2 : C.output = n + j
    · rw [ite_eq_left h2, h2, heq x]
      rcases hrep with hrl | hre
      · exact (hagree x rep).1 hrl
      · rw [hre, wireVal_ge C' x (n + C.gates.length) (by omega),
            wireVal_ge C x (n + C.gates.length) (le_refl _)]
    · rw [ite_eq_right h2]
      by_cases h3 : C.output < n + C.gates.length
      · have h4 := (hagree x (C.output - 1)).2 (C.output - 1 - (n + j)) (by omega) (by omega)
        have h5 : n + j + 1 + (C.output - 1 - (n + j)) = C.output := by omega
        rw [h5] at h4
        exact h4
      · rw [wireVal_ge C' x (C.output - 1) (by omega), wireVal_ge C x C.output (by omega)]

lemma blank {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length)
    (hnr : ∀ k (hk : k < C.gates.length), j < k → n + j ∉ (C.gates[k]).inputs) :
    ∃ C1 : Circuit, PEqualNP.MetaComplexity.Monotone2 C1 ∧ C1.gates.length = C.gates.length ∧
      C1.output = C.output ∧
      (∀ x : Fin n → Bool, wireVal C1 x (n + j) = false) ∧
      ∀ (x : Fin n → Bool) (w : ℕ), w ≠ n + j → wireVal C1 x w = wireVal C x w := by
  have hlen : (C.gates.set j ⟨GateOp.or, []⟩).length = C.gates.length := List.length_set
  refine ⟨⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩, ?_, hlen, rfl, ?_, ?_⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hm g h
    · subst h; simp
  · intro x
    have hj1 : j < (C.gates.set j ⟨GateOp.or, []⟩).length := by rw [hlen]; exact hj
    have h := wireVal_gate (n := n) ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ x j hj1
    rw [h]
    simp [GateOp.eval]
  · intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hlt : w < n
      · rw [wireVal_input _ x w hlt, wireVal_input C x w hlt]
      · by_cases hlt2 : w < n + C.gates.length
        · have hk : w - n < C.gates.length := by omega
          have hk1 : w - n < (C.gates.set j ⟨GateOp.or, []⟩).length := by rw [hlen]; exact hk
          have heq : n + (w - n) = w := by omega
          rw [← heq, wireVal_gate (n := n) ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ x (w - n) hk1,
            wireVal_gate C x (w - n) hk]
          have hg : (C.gates.set j ⟨GateOp.or, []⟩)[w - n] = C.gates[w - n] := by
            rw [List.getElem_set_ne (by omega)]
          show GateOp.eval ((C.gates.set j ⟨GateOp.or, []⟩)[w - n]).op _ = _
          rw [hg]
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases hil : i < n + (w - n)
          · rw [if_pos hil, if_pos hil]
            apply ih i (by omega)
            intro hij
            subst hij
            exact hnr (w - n) hk (by omega) hi
          · rw [if_neg hil, if_neg hil]
        · rw [wireVal_ge _ x w (by show n + (C.gates.set j ⟨GateOp.or, []⟩).length ≤ w; rw [hlen]; omega),
            wireVal_ge C x w (by omega)]

lemma unread_false {n : ℕ} (C : Circuit) (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (j : ℕ) (hj : j < C.gates.length) (hne : C.output ≠ n + j) :
    ∃ k, ∃ hk : k < C.gates.length, j < k ∧ n + j ∈ (C.gates[k]).inputs := by
  by_contra hcon
  have hnr : ∀ k (hk : k < C.gates.length), j < k → n + j ∉ (C.gates[k]).inputs := by
    intro k hk hjk hmem
    exact hcon ⟨k, hk, hjk, hmem⟩
  obtain ⟨C1, hm1, hl1, ho1, hf1, hag1⟩ := blank C hmin.1 j hj hnr
  have hj1 : j < C1.gates.length := by rw [hl1]; exact hj
  obtain ⟨C2, hm2, hs2, he2⟩ := deleteGate (n := n) C1 hm1 j hj1 (n + C1.gates.length) (Or.inr rfl)
    (fun x => by rw [hf1 x, wireVal_ge C1 x (n + C1.gates.length) (le_refl _)])
  have hfun : PEqualNP.MetaComplexity.circuitFun n C2 = PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    show C2.eval (List.ofFn x) = C.eval (List.ofFn x)
    rw [he2 x]
    show wireVal C1 x C1.output = wireVal C x C.output
    rw [ho1]
    exact hag1 x C.output hne
  have hle := hmin.2 C2 hm2 hfun
  have hs1 : C1.size = C.size := hl1
  have hpos : 0 < C.size := lt_of_le_of_lt (Nat.zero_le _) hj
  omega

lemma walk {n : ℕ} (C : Circuit) (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (x : Fin n → Bool) (hout : wireVal C x C.output = false) :
    ∀ m j, j < C.gates.length → C.gates.length - j = m → wireVal C x (n + j) = true →
      ∃ (a : ℕ) (b : ℕ), j ≤ a ∧ a < b ∧ b < C.size ∧
        n + a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b).inputs ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C b).op = GateOp.and ∧
        PEqualNP.EdgeOwnership.gateVal n C a x = true ∧
        PEqualNP.EdgeOwnership.gateVal n C b x = false := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro j hj hm hv
    have hne : C.output ≠ n + j := by
      intro h
      rw [h, hv] at hout
      exact Bool.noConfusion hout
    obtain ⟨k, hk, hjk, hmem⟩ := unread_false C hmin j hj hne
    by_cases hkv : wireVal C x (n + k) = true
    · obtain ⟨a, b, h1, h2, h3, h4, h5, h6, h7⟩ := ih (C.gates.length - k) (by omega) k hk rfl hkv
      exact ⟨a, b, by omega, h2, h3, h4, h5, h6, h7⟩
    · have hkf : wireVal C x (n + k) = false := by simpa using hkv
      have hop : (C.gates[k]).op = GateOp.and ∨ (C.gates[k]).op = GateOp.or := by
        have := (hmin.1 (C.gates[k]) (List.getElem_mem hk)).1
        simpa using this
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        rfl
      rcases hop with hop | hop
      · exact ⟨j, k, le_refl _, hjk, hk, by rw [hga]; exact hmem, by rw [hga]; exact hop, hv, hkf⟩
      · exfalso
        have hany : GateOp.or.eval ((C.gates[k]).inputs.map fun i =>
            if i < n + k then wireVal C x i else false) = true := by
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          exact ⟨n + j, hmem, by rw [if_pos (show n + j < n + k by omega)]; exact hv⟩
        rw [wireVal_gate C x k hk, hop, hany] at hkf
        exact Bool.noConfusion hkf

end PEqualNP.Outside.L_meta_8415

open PEqualNP.Outside.L_meta_8415 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8415 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Bool) (x4 : ℕ), (0 : ℕ) < x1 → PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x2 → x4 < x2.size → PEqualNP.EdgeOwnership.gateVal x1 x2 x4 x3 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x3 = Bool.false → ∃ (x10 : ℕ) (x11 : ℕ), x4 ≤ x10 ∧ x10 < x11 ∧ x11 < x2.size ∧ x1 + x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.gateVal x1 x2 x10 x3 = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x2 x11 x3 = Bool.false := by
  intro n C x j _ hmin hj hv hout
  exact walk C hmin x hout _ j hj rfl hv
