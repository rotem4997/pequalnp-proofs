import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_693

open PEqualNP.CircuitLowerBounds

def reads693 (C : Circuit) (j : ℕ) : Finset ℕ :=
  ((C.gates[j]?.map Gate.inputs).getD []).toFinset

def outside693 (n : ℕ) (C : Circuit) (Q : Finset ℕ) : Finset ℕ :=
  Q.biUnion (reads693 C) \ Q.image (fun j => n + j)

theorem mem_outside693 {n j w : ℕ} {C : Circuit} {Q : Finset ℕ} {g : Gate}
    (hj : j ∈ Q) (hg : C.gates[j]? = some g) (hw : w ∈ g.inputs)
    (hnot : ∀ i ∈ Q, w ≠ n + i) : w ∈ outside693 n C Q := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩, ?_⟩
  · simpa [reads693, hg] using hw
  · intro h
    obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp h
    exact hnot i hi eq.symm

theorem not_internal693 {n w : ℕ} {C : Circuit} {Q : Finset ℕ}
    (hw : w ∈ outside693 n C Q) : ∀ i ∈ Q, w ≠ n + i := by
  intro i hi eq
  exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_image.mpr ⟨i, hi, eq.symm⟩)

theorem outside_card693 {n r : ℕ} {C : Circuit} {Q : Finset ℕ}
    (hfan : ∀ g ∈ C.gates, g.inputs.length = 2) (hr : r ∈ Q)
    (hparent : ∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : Gate,
      C.gates[j']? = some g ∧ n + j ∈ g.inputs) :
    (outside693 n C Q).card ≤ Q.card + 1 := by
  let P := Q.biUnion (reads693 C)
  let N := Q.image (fun j => n + j)
  have htotal : P.card ≤ Q.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro j _
    cases hg : C.gates[j]? with
    | none => simp [reads693, hg]
    | some g =>
      have hsize := hfan g (List.mem_of_getElem? hg)
      simpa [reads693, hg, ← hsize] using g.inputs.toFinset_card_le
  have internal : (Q.erase r).image (fun j => n + j) ⊆ P ∩ N := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.mp hj
    obtain ⟨j', hj', _, g, hg, hread⟩ := hparent j hQ hne
    refine Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨j', hj', ?_⟩,
      Finset.mem_image.mpr ⟨j, hQ, rfl⟩⟩
    simpa [reads693, hg] using hread
  have hinside := Finset.card_le_card internal
  rw [Finset.card_image_of_injective _ (fun a b (h : n + a = n + b) => Nat.add_left_cancel h)] at hinside
  have herase := Finset.card_erase_add_one hr
  have hpartition := Finset.card_sdiff_add_card_inter P N
  change (P \ N).card ≤ Q.card + 1
  omega

open PEqualNP.CircuitLowerBounds

-- Monotonicity of wire evaluation from the project proof of L-meta-616.
namespace InputCircuit693

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

end InputCircuit693

theorem input693 {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (F : Finset ℕ) (ψ : ℕ → Bool)
    (hm : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hw : ∀ w ∈ F, ψ w = true → ∃ p : Fin n,
      p ∉ S ∧ (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true) :
    ∃ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ F.card ∧
      (∀ q ∈ S, x q = false) ∧ ∀ w ∈ F, ψ w = true →
        (C.wires (List.ofFn x)).getD w false = true := by
  classical
  let H := F.filter (fun w => ψ w = true)
  have witness (w : H) := hw w.1 (Finset.mem_filter.mp w.2).1 (Finset.mem_filter.mp w.2).2
  let p (w : H) := (witness w).choose
  let T := H.attach.image p
  let x (q : Fin n) := decide (q ∈ T)
  refine ⟨x, ?_, ?_, ?_⟩
  · have hs : Finset.univ.filter (fun q => x q = true) = T := by
      ext q
      simp [x]
    rw [hs]
    calc
      T.card ≤ H.attach.card := Finset.card_image_le
      _ = H.card := Finset.card_attach
      _ ≤ F.card := Finset.card_filter_le _ _
  · intro q hq
    apply decide_eq_false
    intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
    exact (witness w).choose_spec.1 hq
  · intro w hwF hwψ
    let a : H := ⟨w, Finset.mem_filter.mpr ⟨hwF, hwψ⟩⟩
    have hp : p a ∈ T := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
    have mono : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨hop, hl⟩ := hm g hg
      exact ⟨by simpa using hop, by omega⟩
    apply InputCircuit693.wires_mono C mono (fun q => decide (q = p a)) x _ w (witness a).choose_spec.2
    intro q hq
    have eq := of_decide_eq_true hq
    subst q
    exact decide_eq_true hp

open PEqualNP.CircuitLowerBounds

-- Generic wire evaluation lemmas from the project proof of L-meta-697.
def transferStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem transferWires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl transferStep x := rfl

theorem foldl_transferStep_length (G : List Gate) (w : List Bool) :
    (G.foldl transferStep w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [transferStep]; omega

theorem transferGetD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem transferGetD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_transferStep_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl transferStep w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [transferStep]; omega)]
    exact transferGetD_append_lt _ _ _ hi

theorem foldl_transferStep_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl transferStep w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl transferStep w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_transferStep_getD _ _ _ (by simp only [transferStep, List.length_append, List.length_singleton, foldl_transferStep_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [transferStep]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_transferStep_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_transferStep_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl transferStep w).length) :
    (G.foldl transferStep w).getD i false = ((G.take t).foldl transferStep w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_transferStep_getD _ _ _ hi


theorem transfer693 (n : ℕ) (C : Circuit) (Q F : Finset ℕ) (ψ : ℕ → Bool) (x : Fin n → Bool)
    (mono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (bound : ∀ j ∈ Q, j < C.size)
    (consistent : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n+j) = g.op.eval (g.inputs.map fun w => if w < n+j then ψ w else false))
    (boundary : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g → ∀ w ∈ g.inputs,
      (∀ a ∈ Q, w ≠ n+a) → w ∈ F)
    (good : ∀ w ∈ F, ψ w = true → (C.wires (List.ofFn x)).getD w false = true) :
    ∀ j ∈ Q, ψ (n+j) = true → (C.wires (List.ofFn x)).getD (n+j) false = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj htrue
    have hjl : j < C.gates.length := bound j hj
    let g := C.gates[j]
    have hget : C.gates[j]? = some g := List.getElem?_eq_getElem hjl
    have hmono := mono g (List.getElem_mem hjl)
    have hl := (consistent j hj g hget).symm.trans htrue
    let ins := List.ofFn x
    let pref := (C.gates.take j).foldl transferStep ins
    have plen : pref.length = n+j := by
      simp [pref,ins,foldl_transferStep_length,Nat.min_eq_left hjl.le]
    have pw (w : ℕ) (hw : w ∈ g.inputs) :
        (if w < n+j then ψ w else false) = true → pref.getD w false = true := by
      intro hp
      by_cases hwj : w < n+j
      · simp only [hwj, ↓reduceIte] at hp
        have he : (C.wires ins).getD w false = pref.getD w false :=
          foldl_take_getD C.gates ins j w (plen ▸ hwj)
        rw [← he]
        by_cases ext : ∀ a ∈ Q, w ≠ n+a
        · exact good w (boundary j hj g hget w hw ext) hp
        · push Not at ext
          obtain ⟨a,ha,rfl⟩ := ext
          exact ih a (by omega) ha hp
      · simp [hwj] at hp
    have out : (C.wires ins).getD (n+j) false =
        g.op.eval (g.inputs.map fun i => pref.getD i false) := by
      simpa only [transferWires_eq,g,pref,ins,List.length_ofFn] using foldl_transferStep_getD_gate C.gates ins j hjl
    change (C.wires ins).getD (n+j) false = true
    rw [out]
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hmono.2
    have pa := pw a (by simp [hab])
    have pb := pw b (by simp [hab])
    rcases hmono.1 with hop | hop
    · simp [hop,hab,GateOp.eval] at hl ⊢
      exact ⟨pa (by simpa using hl.1),pb (by simpa using hl.2)⟩
    · simp [hop,hab,GateOp.eval] at hl ⊢
      exact hl.elim (fun h => Or.inl (pa (by simpa using h))) (fun h => Or.inr (pb (by simpa using h)))

end PEqualNP.Outside.L_meta_693

open PEqualNP.Outside.L_meta_693

theorem PEqualNP.Outside.L_meta_693 : ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card := by
  classical
  intro n k r S C Q ψ hmono hpromise hr hbound hparent hconsistent houtside hroot
  let F := outside693 n C Q
  have hcount : F.card ≤ Q.card + 1 :=
    outside_card693 (fun g hg => (hmono g hg).2) hr hparent
  have witness : ∀ w ∈ F, ψ w = true → ∃ p : Fin n, p ∉ S ∧
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true := by
    intro w hw hit
    obtain ⟨p, hp, hS⟩ := Finset.not_subset.mp (houtside w (not_internal693 hw) hit)
    exact ⟨p, hS, (Finset.mem_filter.mp hp).2⟩
  obtain ⟨x, hcard, hS, hgood⟩ := input693 C S F ψ hmono witness
  have hreal := transfer693 n C Q F ψ x hmono hbound hconsistent
    (fun _ hj _ hg _ hw hnot => mem_outside693 hj hg hw hnot) hgood r hr hroot
  by_contra! small
  have hzero := hpromise x (by omega) hS
  rw [hzero] at hreal
  contradiction
