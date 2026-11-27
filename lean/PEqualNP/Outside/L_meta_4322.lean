import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4322

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.EdgeOwnership

def zstepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma zwires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl zstepWire x := rfl

lemma zfoldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl zstepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [zstepWire]
    omega

lemma zfoldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl zstepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (zstepWire w g).length := by simp [zstepWire]; omega
    rw [ih (zstepWire w g) hlt]
    simp [zstepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma zgetD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma zwires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [zwires_eq_foldl, zfoldl_stepWire_length, List.length_ofFn]

lemma zsplit_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def zW (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma zgateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma zW_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    zW n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then zW n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := zsplit_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [zgateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl zstepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, zfoldl_stepWire_length, hpre_len]
  have hCj : zW n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [zW]
    rw [zwires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [zfoldl_stepWire_getD_lt post (zstepWire w0 gj) (n + k) (by simp [zstepWire]; omega)]
    simp [zstepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [zW]
    rw [zwires_eq_foldl, hgs, List.foldl_append]
    exact (zfoldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact zgetD_ge_length w0 i (by omega)

lemma zW_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    zW n C x u = x ⟨u, hu⟩ := by
  simp only [zW]
  rw [zwires_eq_foldl, zfoldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma zorFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma zorStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma zorStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma zorFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact zorStep_getD_lt n cs g k hk

lemma zorSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := zsplit_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [zgateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [zorFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, zorFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, zorFold_getD_lt n post _ m (by omega)]
    exact zorStep_getD_lt n _ gk m (by omega)
  have h3 := zorStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma zqorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [zorFold_length]
  simp

lemma zqreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (zorSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (zorSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma zqreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [zqorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma zqreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (zqreach_iff n C k k hk).2 (Or.inl rfl)

lemma zqreach_le (n : ℕ) (C : Circuit) (g : ℕ) : ∀ w : ℕ, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := zqreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (zqreach_iff n C k g hk).1 h with h3 | ⟨_, w', _, hlt, hr⟩
    · omega
    · have := ih w' hlt hr
      omega

lemma zqreach_trans (n : ℕ) (C : Circuit) (i g : ℕ) (hg : OrReaches n C (n + i) g) :
    ∀ w : ℕ, OrReaches n C w i → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := zqreach_bound n C w i h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (zqreach_iff n C k i hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hg
    · exact (zqreach_iff n C k g hk).2 (Or.inr ⟨hop, w', hw', hlt, ih w' hlt hr⟩)

lemma zqmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma zqorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (zqmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := zqreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (zqreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma zqorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := zqorIn_eq_self n C w hw a ha
  have h2 := zqorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma zqorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, zqmem_orIn, zqmem_orIn, zqmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (zqreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, zqreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (zqreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, zqreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (zqreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma zqorIn_sub (n : ℕ) (C : Circuit) (i w : ℕ) (hr : OrReaches n C w i) :
    PEqualNP.TopForm.orIn n C (n + i) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro b hb
  rcases (zqmem_orIn n C (n + i) b).1 hb with h | ⟨k, hk, hr', hop, hi⟩
  · exfalso
    have := b.2
    omega
  · exact (zqmem_orIn n C w b).2 (Or.inr ⟨k, hk, zqreach_trans n C i k hr' w hr, hop, hi⟩)

lemma zqval_reach (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : zW n C x (n + g) = true) :
    ∀ w : ℕ, OrReaches n C w g → zW n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := zqreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (zqreach_iff n C k g hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hv
    · rw [zW_gate n C x k hk, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨w', hw', by simp only [hlt, ite_true]; exact ih w' hlt hr⟩

lemma zqval_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C w) :
    zW n C (fun r : Fin n => decide (r = b)) w = true := by
  rcases (zqmem_orIn n C w b).1 hb with h | ⟨k, hk, hr, hop, hi⟩
  · rw [← h, zW_input n C _ (b : ℕ) b.2]
    simp
  · refine zqval_reach n C _ k ?_ w hr
    rw [zW_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    have hlt : (b : ℕ) < n + k := by
      have := b.2
      omega
    refine ⟨(b : ℕ), hi, ?_⟩
    simp only [hlt, ite_true]
    rw [zW_input n C _ (b : ℕ) b.2]
    simp
lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

lemma fin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

lemma s10 : (1 : Fin 2) - 0 = 1 := by decide

lemma s11 : (1 : Fin 2) - 1 = 0 := by decide

lemma fin2b : ∀ i b : Fin 2, i = b ∨ i = 1 - b := by decide

lemma fin2ne : ∀ c c' : Fin 2, c ≠ c' → 1 - c = c' := by decide

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [zgateAt_eq C j hj]; exact List.getElem_mem hj

lemma inputs_eq {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have h := hC.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  generalize (gateAt C j).inputs = l at h ⊢
  match l, h with
  | [a, b], _ => rfl

lemma opnd_mem {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (i : Fin 2) : opnd C j i ∈ (gateAt C j).inputs := by
  rw [inputs_eq hC hj]
  rcases fin2 i with rfl | rfl <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (i : Fin 2) : opnd C j i < n + j := hC.2.1 j hj _ (opnd_mem hC hj i)

lemma mem_inputs {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    {w : ℕ} (hw : w ∈ (gateAt C j).inputs) : ∃ i : Fin 2, w = opnd C j i := by
  rw [inputs_eq hC hj] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

lemma orIn_or {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) :=
  zqorIn_or n C j _ _ hj hop (inputs_eq hC hj) (opnd_lt hC hj 0) (opnd_lt hC hj 1)

lemma orIn_sub {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (i : Fin 2) :
    orIn n C (opnd C j i) ⊆ orIn n C (n + j) := by
  rw [orIn_or hC hj hop]
  rcases fin2 i with rfl | rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma orIn_split {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) {y : Fin n} (hy : y ∈ orIn n C (n + j)) :
    ∃ i : Fin 2, y ∈ orIn n C (opnd C j i) := by
  rw [orIn_or hC hj hop, Finset.mem_union] at hy
  rcases hy with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

lemma val_orIn (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (b : Fin n)
    (hb : b ∈ orIn n C w) (hx : x b = true) : zW n C x w = true := by
  rcases (zqmem_orIn n C w b).1 hb with h | ⟨k, hk, hr, hop, hi⟩
  · rw [← h, zW_input n C _ (b : ℕ) b.2]
    exact hx
  · refine zqval_reach n C _ k ?_ w hr
    rw [zW_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    have hlt : (b : ℕ) < n + k := by
      have := b.2
      omega
    refine ⟨(b : ℕ), hi, ?_⟩
    simp only [hlt, ite_true]
    rw [zW_input n C _ (b : ℕ) b.2]
    exact hx

lemma val_and {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool)
    (h : ∀ i : Fin 2, zW n C x (opnd C j i) = true) : zW n C x (n + j) = true := by
  have h0 := opnd_lt hC hj 0
  have h1 := opnd_lt hC hj 1
  rw [zW_gate n C x j hj, hop, inputs_eq hC hj]
  simp [GateOp.eval, h0, h1, h 0, h 1]

def SLr {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u : Fin n) (j : ℕ) : Prop :=
  ∀ p ∈ side (n := n) C j 0, ∀ q ∈ side (n := n) C j 1, G.Adj u p ∨ G.Adj u q ∨ G.Adj p q

def Ctx {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (u : Fin n) (x : ℕ) : Prop :=
  ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and → OrReaches n C x j → SLr G C u j

lemma top_ctx {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (hC : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (hopa : (gateAt C a).op = GateOp.and)
    (hbel : BelowF G C a) (b : Fin 2) {u : Fin n} (hu : u ∈ side (n := n) C a b) :
    Ctx G C u (opnd C a (1 - b)) := by
  intro j hj hopj hr p hp q hq
  have hxx : ∃ x : Fin n → Bool, x = fun r => decide (r = u ∨ r = p ∨ r = q) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hxx
  have xu : x u = true := by simp [hx]
  have xp : x p = true := by simp [hx]
  have xq : x q = true := by simp [hx]
  have vj : zW n C x (n + j) = true := by
    apply val_and hC hj hopj
    intro i
    rcases fin2 i with rfl | rfl
    · exact val_orIn n C x _ p hp xp
    · exact val_orIn n C x _ q hq xq
  have vw := zqval_reach n C x j vj _ hr
  have va : zW n C x (n + a) = true := by
    apply val_and hC ha hopa
    intro i
    rcases fin2b i b with rfl | rfl
    · exact val_orIn n C x _ u hu xu
    · exact vw
  have hF := hbel x va
  unfold graphFun at hF
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq] at hF
  obtain ⟨s, t, hst, hs, ht⟩ := hF
  simp only [hx, decide_eq_true_eq] at hs ht
  rcases hs with h | h | h <;> rcases ht with h' | h' | h' <;> rw [h, h'] at hst <;>
    first
    | exact (G.ne_of_adj hst rfl).elim
    | exact Or.inl hst
    | exact Or.inl hst.symm
    | exact Or.inr (Or.inl hst)
    | exact Or.inr (Or.inl hst.symm)
    | exact Or.inr (Or.inr hst)
    | exact Or.inr (Or.inr hst.symm)

def C4free {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b x y : Fin n, a ≠ b → x ≠ y → G.Adj a x → G.Adj a y → G.Adj b x → G.Adj b y → False

lemma SLsym {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {u : Fin n} {j : ℕ}
    (h : SLr G C u j) (c : Fin 2) :
    ∀ p ∈ side (n := n) C j c, ∀ q ∈ side (n := n) C j (1 - c),
      G.Adj u p ∨ G.Adj u q ∨ G.Adj p q := by
  rcases fin2 c with rfl | rfl
  · rw [s10]; exact h
  · rw [s11]
    intro p hp q hq
    rcases h q hq p hp with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)

section comb

open Classical

variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}

noncomputable def sm {α : Type} (k : ℕ) (A : Finset α) : Finset α := if A.card ≤ k then A else ∅

lemma sm_card {α : Type} {k : ℕ} {A : Finset α} : (sm k A).card ≤ k := by
  unfold sm
  split_ifs with h
  · exact h
  · simp

lemma mem_sm {α : Type} {k : ℕ} {A : Finset α} {x : α} (h : A.card ≤ k) (hx : x ∈ A) :
    x ∈ sm k A := by
  unfold sm
  rw [if_pos h]
  exact hx

lemma bi2_card {α : Type} [DecidableEq α] (f : Fin 2 → Finset α) (k : ℕ) (h : ∀ i, (f i).card ≤ k) :
    ((Finset.univ : Finset (Fin 2)).biUnion f).card ≤ 2 * k := by
  have := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 2)) f k (fun i _ => h i)
  simpa using this

lemma img_card (A B : Finset (Fin n)) (a b : ℕ) (hA : A.card ≤ a) (hB : B.card ≤ b) :
    ((A ×ˢ B).image fun p => s(p.1, p.2)).card ≤ a * b := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product]
  exact Nat.mul_le_mul hA hB

lemma uniq_cn (h4 : C4free G) (A : Finset (Fin n)) (hA : 2 ≤ A.card) :
    (Finset.univ.filter fun z => ∀ x ∈ A, G.Adj z x).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz z' hz'
  rw [Finset.mem_filter] at hz hz'
  by_contra hne
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hA
  exact h4 z z' x y hne hxy (hz.2 x hx) (hz.2 y hy) (hz'.2 x hx) (hz'.2 y hy)

lemma uniq_kappa (h4 : C4free G) (A : Finset (Fin n)) (hA : 4 ≤ A.card) :
    (Finset.univ.filter fun z => (A.filter fun x => ¬ G.Adj z x).card ≤ 1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz z' hz'
  rw [Finset.mem_filter] at hz hz'
  by_contra hne
  have h1 := Finset.le_card_sdiff
    ((A.filter fun x => ¬ G.Adj z x) ∪ (A.filter fun x => ¬ G.Adj z' x)) A
  have h2 := Finset.card_union_le (A.filter fun x => ¬ G.Adj z x)
    (A.filter fun x => ¬ G.Adj z' x)
  have h3 : 1 < (A \ ((A.filter fun x => ¬ G.Adj z x) ∪
      (A.filter fun x => ¬ G.Adj z' x))).card := by
    have := hz.2
    have := hz'.2
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h3
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, not_or, not_and,
    not_not] at hx hy
  exact h4 z z' x y hne hxy (hx.2.1 hx.1) (hy.2.1 hy.1) (hx.2.2 hx.1) (hy.2.2 hy.1)

lemma descK (hC : IsAO2 n C) (z y : Fin n) :
    ∀ w, y ∈ orIn n C w → 4 ≤ (orIn n C w).card →
      ((orIn n C w).filter fun x => ¬ G.Adj z x).card ≤ 1 →
      ∃ g, g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ 4 ≤ (orIn n C (n + g)).card ∧
        ((orIn n C (n + g)).filter fun x => ¬ G.Adj z x).card ≤ 1 ∧
        ∃ i : Fin 2, y ∈ orIn n C (opnd C g i) ∧ (orIn n C (opnd C g i)).card ≤ 3 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hy hbig ht
    by_cases hw : n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or
    · obtain ⟨h1, h2, hop⟩ := hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have e : n + k - n = k := by omega
      rw [e] at h2 hop
      obtain ⟨i, hi⟩ := orIn_split hC h2 hop hy
      by_cases hs : (orIn n C (opnd C k i)).card ≤ 3
      · exact ⟨k, h2, hop, hbig, ht, i, hi, hs⟩
      · exact ih _ (opnd_lt hC h2 i) hi (by omega)
          ((Finset.card_le_card (Finset.filter_subset_filter _ (orIn_sub hC h2 hop i))).trans ht)
    · have := zqorIn_small n C w hw
      omega

def Q (G : SimpleGraph (Fin n)) (C : Circuit) (u : Fin n) (j : ℕ) (v : Fin n) : Prop :=
  G.Adj u v ∧ ((side (n := n) C j 0 ∩ side (n := n) C j 1 = {v}) ∨
    ∃ c : Fin 2, u ∈ side (n := n) C j (1 - c) ∧ side (n := n) C j c = {v} ∧
      2 ≤ ((side (n := n) C j (1 - c)).filter fun p => ¬ G.Adj v p).card)

lemma Q_uniq {u v v' : Fin n} {j : ℕ} (h : Q G C u j v) (h' : Q G C u j v') : v = v' := by
  obtain ⟨ha, h⟩ := h
  obtain ⟨ha', h'⟩ := h'
  have aux : ∀ (w w' : Fin n) (c' : Fin 2), side (n := n) C j 0 ∩ side (n := n) C j 1 = {w} →
      side (n := n) C j c' = {w'} → w = w' := by
    intro w w' c' hD hc'
    have hv : w ∈ side (n := n) C j 0 ∩ side (n := n) C j 1 := by
      rw [hD]; exact Finset.mem_singleton_self w
    rw [Finset.mem_inter] at hv
    have : w ∈ side (n := n) C j c' := by
      rcases fin2 c' with rfl | rfl
      · exact hv.1
      · exact hv.2
    rw [hc'] at this
    exact Finset.mem_singleton.mp this
  rcases h with hD | ⟨c, huc, hc, -⟩ <;> rcases h' with hD' | ⟨c', huc', hc', -⟩
  · exact Finset.singleton_injective (hD.symm.trans hD')
  · exact aux v v' c' hD hc'
  · exact (aux v' v c hD' hc).symm
  · by_cases hcc : c = c'
    · subst hcc
      exact Finset.singleton_injective (hc.symm.trans hc')
    · rw [fin2ne c c' hcc, hc'] at huc
      have := Finset.mem_singleton.mp huc
      rw [this] at ha'
      exact (G.ne_of_adj ha' rfl).elim

noncomputable def Phi (G : SimpleGraph (Fin n)) (C : Circuit) (u : Fin n) (x : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    OrReaches n C x j ∧ Q G C u j v

lemma mem_Phi {u v : Fin n} {x : ℕ} : v ∈ Phi G C u x ↔
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C x j ∧ Q G C u j v := by
  simp [Phi]

lemma Phi_and_card {u : Fin n} {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : (Phi G C u (n + j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have aux : ∀ v ∈ Phi G C u (n + j), Q G C u j v := by
    intro v hv
    obtain ⟨j', _, _, hr, hq⟩ := mem_Phi.1 hv
    rcases (zqreach_iff n C j j' hj).1 hr with h | h
    · rw [← h]; exact hq
    · have e := hop.symm.trans h.1
      cases e
  intro v hv v' hv'
  exact Q_uniq (aux v hv) (aux v' hv')

lemma Phi_step (hC : IsAO2 n C) {u v : Fin n} {g : ℕ} (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.or) (hv : v ∈ Phi G C u (n + g)) :
    ∃ i : Fin 2, v ∈ Phi G C u (opnd C g i) := by
  obtain ⟨j, hj, hopj, hr, hq⟩ := mem_Phi.1 hv
  rcases (zqreach_iff n C g j hg).1 hr with h | ⟨_, w, hw, _, hr'⟩
  · rw [h] at hopj
    have e := hop.symm.trans hopj
    cases e
  · obtain ⟨i, rfl⟩ := mem_inputs hC hg hw
    exact ⟨i, mem_Phi.2 ⟨j, hj, hopj, hr', hq⟩⟩

lemma descW (hC : IsAO2 n C) (u v : Fin n) :
    ∀ x, v ∈ Phi G C u x → 2 ≤ (Phi G C u x).card →
      ∃ g, g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ OrReaches n C x g ∧
        2 ≤ (Phi G C u (n + g)).card ∧
        ∃ i : Fin 2, v ∈ Phi G C u (opnd C g i) ∧ (Phi G C u (opnd C g i)).card ≤ 1 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hv hbig
    obtain ⟨j, hj, hopj, hr, hq⟩ := mem_Phi.1 hv
    obtain ⟨h1, h2⟩ := zqreach_bound n C x j hr
    obtain ⟨k, rfl⟩ : ∃ k, x = n + k := ⟨x - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases hC.1 (gateAt C k) (gateAt_mem hk) with hop | hop
    · have := Phi_and_card (G := G) (u := u) hk hop
      omega
    · obtain ⟨i, hi⟩ := Phi_step hC hk hop hv
      by_cases hs : (Phi G C u (opnd C k i)).card ≤ 1
      · exact ⟨k, hk, hop, zqreach_self n C k hk, hbig, i, hi, hs⟩
      · obtain ⟨g, hg, hopg, hrg, hbg, rest⟩ := ih _ (opnd_lt hC hk i) hi (by omega)
        exact ⟨g, hg, hopg, (zqreach_iff n C k g hk).2
          (Or.inr ⟨hop, _, opnd_mem hC hk i, opnd_lt hC hk i, hrg⟩), hbg, rest⟩

lemma ZL (h4 : C4free G) {u0 v : Fin n} {j x : ℕ} (hj : j < C.gates.length)
    (hopj : (gateAt C j).op = GateOp.and) (hr : OrReaches n C x j) (hq : Q G C u0 j v) :
    ∃ Z : Finset (Fin n), Z.card ≤ 1 ∧ ∀ u, Ctx G C u x → G.Adj u v ∨ u ∈ Z := by
  obtain ⟨-, hD | ⟨c, -, hc, hT⟩⟩ := hq
  · refine ⟨∅, by simp, fun u hu => Or.inl ?_⟩
    have hv : v ∈ side (n := n) C j 0 ∩ side (n := n) C j 1 := by
      rw [hD]; exact Finset.mem_singleton_self v
    rw [Finset.mem_inter] at hv
    rcases hu j hj hopj hr v hv.1 v hv.2 with h | h | h
    · exact h
    · exact h
    · exact (G.ne_of_adj h rfl).elim
  · refine ⟨Finset.univ.filter fun y =>
        ∀ p ∈ (side (n := n) C j (1 - c)).filter (fun p => ¬ G.Adj v p), G.Adj y p,
      uniq_cn h4 _ hT, fun u hu => ?_⟩
    by_cases huv : G.Adj u v
    · exact Or.inl huv
    · refine Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun p hp => ?_⟩)
      rw [Finset.mem_filter] at hp
      have hvc : v ∈ side (n := n) C j c := by rw [hc]; exact Finset.mem_singleton_self v
      rcases SLsym (hu j hj hopj hr) c v hvc p hp.1 with h | h | h
      · exact absurd h huv
      · exact h
      · exact absurd h hp.2

noncomputable def UU (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => Ctx G C u (n + g) ∧ 2 ≤ (Phi G C u (n + g)).card

lemma mem_UU {g : ℕ} {u : Fin n} :
    u ∈ UU G C g ↔ Ctx G C u (n + g) ∧ 2 ≤ (Phi G C u (n + g)).card := by
  simp [UU]

lemma UU_card (h4 : C4free G) (g : ℕ) : (UU G C g).card ≤ 3 := by
  by_cases hne : (UU G C g).Nonempty
  · obtain ⟨u0, hu0⟩ := hne
    have hu0' := mem_UU.1 hu0
    obtain ⟨v, hv, v', hv', hvv⟩ := Finset.one_lt_card.mp hu0'.2
    obtain ⟨j, hj, hopj, hr, hq⟩ := mem_Phi.1 hv
    obtain ⟨j', hj', hopj', hr', hq'⟩ := mem_Phi.1 hv'
    obtain ⟨Z, hZ, hZp⟩ := ZL h4 hj hopj hr hq
    obtain ⟨Z', hZ', hZp'⟩ := ZL h4 hj' hopj' hr' hq'
    obtain ⟨A, hA, hAp⟩ : ∃ A : Finset (Fin n), A.card ≤ 1 ∧
        ∀ y, G.Adj y v → G.Adj y v' → y ∈ A := by
      refine ⟨Finset.univ.filter fun y => ∀ p ∈ ({v, v'} : Finset (Fin n)), G.Adj y p,
        uniq_cn h4 _ (by rw [Finset.card_pair hvv]), fun y h h' => ?_⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun p hp => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact h
      · exact h'
    have hsub : UU G C g ⊆ A ∪ Z ∪ Z' := by
      intro u hu
      have hc := (mem_UU.1 hu).1
      rcases hZp u hc with h | h
      · rcases hZp' u hc with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hAp u h h'))
        · exact Finset.mem_union_right _ h'
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    have a1 := Finset.card_union_le (A ∪ Z) Z'
    have a2 := Finset.card_union_le A Z
    have a3 := Finset.card_le_card hsub
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

noncomputable def FK (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Finset (Sym2 (Fin n)) :=
  if 4 ≤ (orIn n C (n + g)).card then
    ((Finset.univ.filter fun z => ((orIn n C (n + g)).filter fun x => ¬ G.Adj z x).card ≤ 1) ×ˢ
      ((Finset.univ : Finset (Fin 2)).biUnion fun i => sm 3 (orIn n C (opnd C g i)))).image
        fun p => s(p.1, p.2)
  else ∅

lemma FK_card (h4 : C4free G) (g : ℕ) : (FK G C g).card ≤ 6 := by
  unfold FK
  split_ifs with h
  · have := img_card _ _ 1 6 (uniq_kappa h4 _ h)
      (bi2_card (fun i => sm 3 (orIn n C (opnd C g i))) 3 (fun i => sm_card))
    omega
  · simp

noncomputable def FW (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Finset (Sym2 (Fin n)) :=
  (UU G C g).biUnion fun u =>
    ((Finset.univ : Finset (Fin 2)).biUnion fun i => sm 1 (Phi G C u (opnd C g i))).image
      fun v => s(u, v)

lemma FW_card (h4 : C4free G) (g : ℕ) : (FW G C g).card ≤ 6 := by
  unfold FW
  refine (Finset.card_biUnion_le_card_mul _ _ 2 ?_).trans ?_
  · intro u _
    exact Finset.card_image_le.trans
      (bi2_card (fun i => sm 1 (Phi G C u (opnd C g i))) 1 (fun i => sm_card))
  · have := UU_card (C := C) h4 g
    omega

noncomputable def FT (G : SimpleGraph (Fin n)) (C : Circuit) (a : ℕ) : Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin 2)).biUnion fun b =>
    (sm 3 (side (n := n) C a b)).biUnion fun u =>
      (sm 1 (Phi G C u (opnd C a (1 - b)))).image fun v => s(u, v)

lemma FT_card (a : ℕ) : (FT G C a).card ≤ 6 := by
  unfold FT
  refine bi2_card _ 3 (fun b => ?_)
  refine (Finset.card_biUnion_le_card_mul _ _ 1 ?_).trans ?_
  · intro u _
    exact Finset.card_image_le.trans sm_card
  · rw [Nat.mul_one]
    exact sm_card

noncomputable def star (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  if 2 ≤ A.card then
    ((Finset.univ.filter fun z => ∀ x ∈ A, G.Adj z x) ×ˢ sm 3 A).image fun p => s(p.1, p.2)
  else ∅

lemma star_card (h4 : C4free G) (A : Finset (Fin n)) : (star G A).card ≤ 3 := by
  unfold star
  split_ifs with h
  · exact img_card _ _ 1 3 (uniq_cn h4 A h) sm_card
  · simp

lemma mem_star {A : Finset (Fin n)} {u v : Fin n} (h2 : 2 ≤ A.card) (h3 : A.card ≤ 3)
    (hu : ∀ x ∈ A, G.Adj u x) (hv : v ∈ A) : s(u, v) ∈ star G A := by
  unfold star
  rw [if_pos h2]
  exact Finset.mem_image.2 ⟨(u, v), Finset.mem_product.2
    ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩, mem_sm h3 hv⟩, rfl⟩

noncomputable def one (A B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (sm 3 A ×ˢ sm 1 B).image fun p => s(p.1, p.2)

lemma one_card (A B : Finset (Fin n)) : (one A B).card ≤ 3 :=
  img_card _ _ 3 1 sm_card sm_card

lemma mem_one {A B : Finset (Fin n)} {u v : Fin n} (hA : A.card ≤ 3) (hB : B.card ≤ 1)
    (hu : u ∈ A) (hv : v ∈ B) : s(u, v) ∈ one A B :=
  Finset.mem_image.2 ⟨(u, v), Finset.mem_product.2 ⟨mem_sm hA hu, mem_sm hB hv⟩, rfl⟩

noncomputable def FJ (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) : Finset (Sym2 (Fin n)) :=
  ((Finset.univ : Finset (Fin 2)).biUnion fun c =>
    star G (side (n := n) C j c) ∪ one (side (n := n) C j (1 - c)) (side (n := n) C j c)) ∪
  star G (side (n := n) C j 0 ∩ side (n := n) C j 1)

lemma FJ_card (h4 : C4free G) (j : ℕ) : (FJ G C j).card ≤ 15 := by
  unfold FJ
  have h1 := bi2_card (fun c : Fin 2 =>
    star G (side (n := n) C j c) ∪ one (side (n := n) C j (1 - c)) (side (n := n) C j c)) 6
    (fun c => by
      have a := Finset.card_union_le (star G (side (n := n) C j c))
        (one (side (n := n) C j (1 - c)) (side (n := n) C j c))
      have b := star_card h4 (side (n := n) C j c)
      have d := one_card (side (n := n) C j (1 - c)) (side (n := n) C j c)
      omega)
  have h2 := star_card h4 (side (n := n) C j 0 ∩ side (n := n) C j 1)
  have h3 := Finset.card_union_le ((Finset.univ : Finset (Fin 2)).biUnion fun c =>
    star G (side (n := n) C j c) ∪ one (side (n := n) C j (1 - c)) (side (n := n) C j c))
    (star G (side (n := n) C j 0 ∩ side (n := n) C j 1))
  omega

noncomputable def F (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Finset (Sym2 (Fin n)) :=
  if (gateAt C g).op = GateOp.or then FK G C g ∪ FW G C g else FT G C g ∪ FJ G C g

lemma F_card (h4 : C4free G) (g : ℕ) : (F G C g).card ≤ 27 := by
  unfold F
  split_ifs with h
  · have a := Finset.card_union_le (FK G C g) (FW G C g)
    have b := FK_card (C := C) h4 g
    have c := FW_card (C := C) h4 g
    omega
  · have a := Finset.card_union_le (FT G C g) (FJ G C g)
    have b := FT_card (G := G) (C := C) g
    have c := FJ_card (C := C) h4 g
    omega

lemma mem_F_or {g : ℕ} {e : Sym2 (Fin n)} (hop : (gateAt C g).op = GateOp.or)
    (h : e ∈ FK G C g ∨ e ∈ FW G C g) : e ∈ F G C g := by
  unfold F
  rw [if_pos hop]
  exact Finset.mem_union.2 h

lemma mem_F_and {g : ℕ} {e : Sym2 (Fin n)} (hop : (gateAt C g).op = GateOp.and)
    (h : e ∈ FT G C g ∨ e ∈ FJ G C g) : e ∈ F G C g := by
  unfold F
  rw [if_neg (by rw [hop]; intro h'; cases h')]
  exact Finset.mem_union.2 h

lemma Kgood (hC : IsAO2 n C) (z y : Fin n) (x0 : ℕ) (hy : y ∈ orIn n C x0)
    (hb : 4 ≤ (orIn n C x0).card)
    (ht : ((orIn n C x0).filter fun x => ¬ G.Adj z x).card ≤ 1) :
    ∃ g, g < C.gates.length ∧ s(z, y) ∈ F G C g := by
  obtain ⟨g, hg, hop, hbig, htg, i, hyi, hsm⟩ := descK hC z y x0 hy hb ht
  refine ⟨g, hg, mem_F_or hop (Or.inl ?_)⟩
  unfold FK
  rw [if_pos hbig]
  exact Finset.mem_image.2 ⟨(z, y), Finset.mem_product.2
    ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, htg⟩,
      Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, mem_sm hsm hyi⟩⟩, rfl⟩

lemma Wcharge (hC : IsAO2 n C) {a j : ℕ} {u v : Fin n} (ha : a < C.gates.length)
    (hopa : (gateAt C a).op = GateOp.and) (b : Fin 2) (hu : u ∈ side (n := n) C a b)
    (hU : (side (n := n) C a b).card ≤ 3) (hctx : Ctx G C u (opnd C a (1 - b)))
    (hj : j < C.gates.length) (hopj : (gateAt C j).op = GateOp.and)
    (hr : OrReaches n C (opnd C a (1 - b)) j) (hq : Q G C u j v) :
    ∃ g, g < C.gates.length ∧ s(u, v) ∈ F G C g := by
  have hv : v ∈ Phi G C u (opnd C a (1 - b)) := mem_Phi.2 ⟨j, hj, hopj, hr, hq⟩
  by_cases hs : (Phi G C u (opnd C a (1 - b))).card ≤ 1
  · refine ⟨a, ha, mem_F_and hopa (Or.inl ?_)⟩
    unfold FT
    exact Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, Finset.mem_biUnion.2
      ⟨u, mem_sm hU hu, Finset.mem_image.2 ⟨v, mem_sm hs hv, rfl⟩⟩⟩
  · obtain ⟨g, hg, hopg, hrg, hbg, i, hvi, hsi⟩ := descW hC u v _ hv (by omega)
    refine ⟨g, hg, mem_F_or hopg (Or.inr ?_)⟩
    unfold FW
    refine Finset.mem_biUnion.2 ⟨u, mem_UU.2 ⟨?_, hbg⟩, Finset.mem_image.2
      ⟨v, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, mem_sm hsi hvi⟩, rfl⟩⟩
    intro j' hj' hopj' hr'
    exact hctx j' hj' hopj' (zqreach_trans n C g j' hr' _ hrg)

lemma memFJ_star {j : ℕ} {e : Sym2 (Fin n)} (c : Fin 2)
    (h : e ∈ star G (side (n := n) C j c)) : e ∈ FJ G C j := by
  unfold FJ
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2
    ⟨c, Finset.mem_univ _, Finset.mem_union_left _ h⟩)

lemma memFJ_one {j : ℕ} {e : Sym2 (Fin n)} (c : Fin 2)
    (h : e ∈ one (side (n := n) C j (1 - c)) (side (n := n) C j c)) : e ∈ FJ G C j := by
  unfold FJ
  exact Finset.mem_union_left _ (Finset.mem_biUnion.2
    ⟨c, Finset.mem_univ _, Finset.mem_union_right _ h⟩)

lemma memFJ_D {j : ℕ} {e : Sym2 (Fin n)}
    (h : e ∈ star G (side (n := n) C j 0 ∩ side (n := n) C j 1)) : e ∈ FJ G C j := by
  unfold FJ
  exact Finset.mem_union_right _ h

lemma mainCase (h4 : C4free G) (hC : IsAO2 n C) {a j : ℕ} {u v : Fin n}
    (ha : a < C.gates.length) (hopa : (gateAt C a).op = GateOp.and) (b : Fin 2)
    (hall : ∀ u' ∈ side (n := n) C a b, Ctx G C u' (opnd C a (1 - b)))
    (hj : j < C.gates.length) (hopj : (gateAt C j).op = GateOp.and)
    (hr : OrReaches n C (opnd C a (1 - b)) j) (hadj : G.Adj u v)
    (hu : u ∈ side (n := n) C a b)
    (h0 : u ∈ side (n := n) C j 0 ∨ v ∈ side (n := n) C j 0)
    (h1 : u ∈ side (n := n) C j 1 ∨ v ∈ side (n := n) C j 1) :
    ∃ g, g < C.gates.length ∧ s(u, v) ∈ F G C g := by
  by_contra hno
  have kbs : ∀ (z y : Fin n) (k : ℕ) (c : Fin 2), s(z, y) = s(u, v) →
      y ∈ side (n := n) C k c →
      ((side (n := n) C k c).filter fun x => ¬ G.Adj z x).card ≤ 1 →
      (side (n := n) C k c).card ≤ 3 := by
    intro z y k c he hy ht
    by_contra hc
    obtain ⟨g, hg, hm⟩ := Kgood hC z y (opnd C k c) hy (not_le.1 hc) ht
    rw [he] at hm
    exact hno ⟨g, hg, hm⟩
  have sl : ∀ u' ∈ side (n := n) C a b, SLr G C u' j :=
    fun u' hu' => hall u' hu' j hj hopj hr
  have caseX : ∀ c : Fin 2, u ∈ side (n := n) C j (1 - c) → v ∈ side (n := n) C j c → False := by
    intro c huc hvc
    have hN : ∀ q ∈ side (n := n) C j c, G.Adj u q := by
      intro q hq
      rcases SLsym (sl u hu) c q hq u huc with h | h | h
      · exact h
      · exact (G.ne_of_adj h rfl).elim
      · exact h.symm
    have hSc : (side (n := n) C j c).card ≤ 3 := by
      apply kbs u v j c rfl hvc
      rw [Finset.filter_eq_empty_iff.2 (fun x hx h => h (hN x hx))]
      simp
    by_cases h2 : 2 ≤ (side (n := n) C j c).card
    · exact hno ⟨j, hj, mem_F_and hopj (Or.inr (memFJ_star c (mem_star h2 hSc hN hvc)))⟩
    · have hc1 : (side (n := n) C j c).card ≤ 1 := by omega
      have hsing : side (n := n) C j c = {v} :=
        Finset.eq_singleton_iff_unique_mem.2
          ⟨hvc, fun x hx => Finset.card_le_one.1 hc1 x hx v hvc⟩
      by_cases hT : ((side (n := n) C j (1 - c)).filter fun p => ¬ G.Adj v p).card ≤ 1
      · have hS' := kbs v u j (1 - c) Sym2.eq_swap huc hT
        exact hno ⟨j, hj, mem_F_and hopj (Or.inr (memFJ_one c (mem_one hS' hc1 huc hvc)))⟩
      · have hq : Q G C u j v := ⟨hadj, Or.inr ⟨c, huc, hsing, by omega⟩⟩
        have hU : (side (n := n) C a b).card ≤ 3 := by
          apply kbs v u a b Sym2.eq_swap hu
          rw [Finset.card_le_one]
          intro u1 h1 u2 h2
          rw [Finset.mem_filter] at h1 h2
          by_contra hne
          obtain ⟨p1, hp1, p2, hp2, hpp⟩ := Finset.one_lt_card.mp (not_le.1 hT)
          rw [Finset.mem_filter] at hp1 hp2
          have key : ∀ u' ∈ side (n := n) C a b, ¬ G.Adj v u' →
              ∀ p ∈ side (n := n) C j (1 - c), ¬ G.Adj v p → G.Adj u' p := by
            intro u' hu' hnv p hp hnp
            rcases SLsym (sl u' hu') c v hvc p hp with h | h | h
            · exact absurd h.symm hnv
            · exact h
            · exact absurd h hnp
          exact h4 u1 u2 p1 p2 hne hpp (key u1 h1.1 h1.2 p1 hp1.1 hp1.2)
            (key u1 h1.1 h1.2 p2 hp2.1 hp2.2) (key u2 h2.1 h2.2 p1 hp1.1 hp1.2)
            (key u2 h2.1 h2.2 p2 hp2.1 hp2.2)
        obtain ⟨g, hg, hm⟩ := Wcharge hC ha hopa b hu hU (hall u hu) hj hopj hr hq
        exact hno ⟨g, hg, hm⟩
  have caseD : v ∈ side (n := n) C j 0 → v ∈ side (n := n) C j 1 → False := by
    intro hv0 hv1
    have hvD : v ∈ side (n := n) C j 0 ∩ side (n := n) C j 1 := Finset.mem_inter.2 ⟨hv0, hv1⟩
    have hUv : ∀ u' ∈ side (n := n) C a b, G.Adj u' v := by
      intro u' hu'
      rcases sl u' hu' v hv0 v hv1 with h | h | h
      · exact h
      · exact h
      · exact (G.ne_of_adj h rfl).elim
    have hU : (side (n := n) C a b).card ≤ 3 := by
      apply kbs v u a b Sym2.eq_swap hu
      rw [Finset.filter_eq_empty_iff.2 (fun x hx h => h (hUv x hx).symm)]
      simp
    have hDu : ∀ d ∈ side (n := n) C j 0 ∩ side (n := n) C j 1, G.Adj u d := by
      intro d hd
      rw [Finset.mem_inter] at hd
      rcases sl u hu d hd.1 d hd.2 with h | h | h
      · exact h
      · exact h
      · exact (G.ne_of_adj h rfl).elim
    by_cases hD : (side (n := n) C j 0 ∩ side (n := n) C j 1).card ≤ 1
    · have hsing : side (n := n) C j 0 ∩ side (n := n) C j 1 = {v} :=
        Finset.eq_singleton_iff_unique_mem.2
          ⟨hvD, fun x hx => Finset.card_le_one.1 hD x hx v hvD⟩
      obtain ⟨g, hg, hm⟩ := Wcharge hC ha hopa b hu hU (hall u hu) hj hopj hr
        ⟨hadj, Or.inl hsing⟩
      exact hno ⟨g, hg, hm⟩
    · have hD3 : (side (n := n) C j 0 ∩ side (n := n) C j 1).card ≤ 3 := by
        by_cases hP : ((side (n := n) C j 0).filter fun p => ¬ G.Adj u p).card ≤ 1
        · exact (Finset.card_le_card Finset.inter_subset_left).trans (kbs u v j 0 rfl hv0 hP)
        · by_cases hQ : ((side (n := n) C j 1).filter fun p => ¬ G.Adj u p).card ≤ 1
          · exact (Finset.card_le_card Finset.inter_subset_right).trans
              (kbs u v j 1 rfl hv1 hQ)
          · exfalso
            obtain ⟨p1, hp1, p2, hp2, hpp⟩ := Finset.one_lt_card.mp (not_le.1 hP)
            obtain ⟨q1, hq1, q2, hq2, hqq⟩ := Finset.one_lt_card.mp (not_le.1 hQ)
            rw [Finset.mem_filter] at hp1 hp2 hq1 hq2
            have key : ∀ p ∈ side (n := n) C j 0, ¬ G.Adj u p →
                ∀ q ∈ side (n := n) C j 1, ¬ G.Adj u q → G.Adj p q := by
              intro p hp hnp q hq hnq
              rcases sl u hu p hp q hq with h | h | h
              · exact absurd h hnp
              · exact absurd h hnq
              · exact h
            exact h4 p1 p2 q1 q2 hpp hqq (key p1 hp1.1 hp1.2 q1 hq1.1 hq1.2)
              (key p1 hp1.1 hp1.2 q2 hq2.1 hq2.2) (key p2 hp2.1 hp2.2 q1 hq1.1 hq1.2)
              (key p2 hp2.1 hp2.2 q2 hq2.1 hq2.2)
      exact hno ⟨j, hj, mem_F_and hopj (Or.inr (memFJ_D
        (mem_star (not_le.1 hD) hD3 hDu hvD)))⟩
  rcases h0 with h0 | h0
  · rcases h1 with h1 | h1
    · rcases sl u hu u h0 u h1 with h | h | h <;> exact G.ne_of_adj h rfl
    · exact caseX 1 (by rw [s11]; exact h0) h1
  · rcases h1 with h1 | h1
    · exact caseX 0 (by rw [s10]; exact h1) h0
    · exact caseD h0 h1

lemma count (h4 : C4free G) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ e ∈ E, ∃ g, g < C.gates.length ∧ e ∈ F G C g) : E.card ≤ 27 * C.size := by
  have hsub : E ⊆ (Finset.range C.gates.length).biUnion (F G C) := by
    intro e he
    obtain ⟨g, hg, hm⟩ := hE e he
    exact Finset.mem_biUnion.2 ⟨g, Finset.mem_range.2 hg, hm⟩
  have hb := Finset.card_biUnion_le_card_mul (Finset.range C.gates.length) (F G C) 27
    (fun g _ => F_card h4 g)
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at hb
  unfold Circuit.size
  omega

end comb

end PEqualNP.Outside.L_meta_4322

theorem PEqualNP.Outside.L_meta_4322 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → PEqualNP.TopForm.IsAO2 x1 x4 → {x7 ∈ x2.edgeFinset | ∃ (x8 : Fin x1) (x9 : Fin x1), x7 = s(x8, x9) ∧ ∃ x10 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x11 : Fin (2 : ℕ)), ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, x8 ∈ PEqualNP.TopForm.side x4 x10 x11 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x10 ((1 : Fin (2 : ℕ)) - x11)) x12 ∧ (x8 ∈ PEqualNP.TopForm.side x4 x12 (0 : Fin (2 : ℕ)) ∨ x9 ∈ PEqualNP.TopForm.side x4 x12 (0 : Fin (2 : ℕ))) ∧ (x8 ∈ PEqualNP.TopForm.side x4 x12 (1 : Fin (2 : ℕ)) ∨ x9 ∈ PEqualNP.TopForm.side x4 x12 (1 : Fin (2 : ℕ)))}.card ≤ (27 : ℕ) * x4.size := by
  intro n G _ C hg hC
  have h4 : PEqualNP.Outside.L_meta_4322.C4free G := by
    intro a b x y hab hxy hax hay hbx hby
    exact PEqualNP.Outside.L_meta_4322.no4 G hg a x b y hax hbx.symm hby hay.symm hab hxy
  apply PEqualNP.Outside.L_meta_4322.count h4
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨hedge, u, v, rfl, a, hat, b, j, hjj, hu, hr, h0, h1⟩ := he
  have hadj : G.Adj u v := by simpa using hedge
  simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
    Finset.mem_range] at hat
  simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
    Finset.mem_range] at hjj
  exact PEqualNP.Outside.L_meta_4322.mainCase h4 hC hat.1 hat.2.1 b
    (fun u' hu' => PEqualNP.Outside.L_meta_4322.top_ctx G hC hat.1 hat.2.1 hat.2.2 b hu')
    hjj.1 hjj.2.1 hr hadj hu h0 h1
