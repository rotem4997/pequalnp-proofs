import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]


lemma mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv



def nG (C : Circuit) (g b d : ℕ) : Gate := ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩

def md (C : Circuit) (g b d : ℕ) : Circuit := ⟨C.gates.set g (nG C g b d), C.output⟩

lemma md_len (C : Circuit) (g b d : ℕ) : (md C g b d).gates.length = C.gates.length := by
  simp [md]

lemma md_ne (C : Circuit) (g b d k : ℕ) (hk : k ≠ g) : gateAt (md C g b d) k = gateAt C k := by
  simp [md, gateAt, List.getD_eq_getElem?_getD, Ne.symm hk]

lemma md_eq (C : Circuit) (g b d : ℕ) (hg : g < C.gates.length) :
    gateAt (md C g b d) g = nG C g b d := by
  simp [md, gateAt, List.getD_eq_getElem?_getD, hg]

lemma getD_mem2 (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b < 2) : l.getD b 0 ∈ l := by
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hl
  interval_cases b <;> simp

lemma two_step (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (hl : l.length = 2) (b d : ℕ) (hb : b < 2) (f f2 : ℕ → Bool)
    (hall : ∀ i ∈ l, f2 i = true → f i = true) (hd : f2 d = true → f (l.getD b 0) = true)
    (h : op.eval ((l.set b d).map f2) = true) : op.eval (l.map f) = true := by
  obtain ⟨a0, a1, rfl⟩ := List.length_eq_two.mp hl
  have h0 := hall a0 (by simp)
  have h1 := hall a1 (by simp)
  clear hall
  rcases hop with rfl | rfl <;> interval_cases b <;>
    (cases e1 : f2 d <;> cases e2 : f2 a1 <;> cases e3 : f a0 <;> cases e4 : f a1 <;>
      cases e5 : f2 a0 <;> simp_all [GateOp.eval])

lemma md_ao2 (n : ℕ) (C : Circuit) (g b d : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (hd : d < n + g) : PEqualNP.TopForm.IsAO2 n (md C g b d) := by
  obtain ⟨h1, h2, h3⟩ := hAO
  refine ⟨?_, ?_, ?_⟩
  · intro G hG
    rcases List.mem_or_eq_of_mem_set hG with hG | hG
    · exact h1 G hG
    · rw [hG]
      exact h1 (gateAt C g) (gateAt_mem hg)
  · intro j hj i hi
    rw [md_len] at hj
    by_cases hjg : j = g
    · subst hjg
      rw [md_eq C j b d hg] at hi
      rcases List.mem_or_eq_of_mem_set hi with hi | hi
      · exact h2 j hj i hi
      · rw [hi]; exact hd
    · rw [md_ne C g b d j hjg] at hi
      exact h2 j hj i hi
  · intro G hG
    rcases List.mem_or_eq_of_mem_set hG with hG | hG
    · exact h3 G hG
    · rw [hG]
      show ((gateAt C g).inputs.set b d).length = 2
      rw [List.length_set]
      exact h3 _ (gateAt_mem hg)

lemma narrow (n : ℕ) (C : Circuit) (g b c d : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (hb : b < 2)
    (hc : (gateAt C g).inputs.getD b 0 = c) (hd : d < n + g)
    (hdc : ∀ x : Fin n → Bool, val C (List.ofFn x) d = true → val C (List.ofFn x) c = true)
    (x : Fin n → Bool) :
    ∀ w, val (md C g b d) (List.ofFn x) w = true → val C (List.ofFn x) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    have hx : (List.ofFn x).length = n := by simp
    by_cases hw : w < n
    · rw [val_input hx hw] at hv ⊢
      exact hv
    · by_cases hl : n + C.gates.length ≤ w
      · rw [val_ge hx (by rw [md_len]; exact hl)] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate hx (by rw [md_len]; exact hk)] at hv
        rw [val_gate hx hk]
        by_cases hkg : k = g
        · subst hkg
          rw [md_eq C k b d hg] at hv
          have hlen2 : (gateAt C k).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hk)
          have hrb : ∀ i ∈ (gateAt C k).inputs, i < n + k := hAO.2.1 k hk
          have hcm : c < n + k := by
            rw [← hc]
            exact hrb _ (getD_mem2 _ hlen2 b hb)
          refine two_step (gateAt C k).op (hAO.1 _ (gateAt_mem hk)) (gateAt C k).inputs hlen2 b d hb
            (fun i => if i < n + k then val C (List.ofFn x) i else false)
            (fun i => if i < n + k then val (md C k b d) (List.ofFn x) i else false) ?_ ?_ hv
          · intro i hi h1
            have hi2 := hrb i hi
            simp only [if_pos hi2] at h1 ⊢
            exact ih i hi2 h1
          · intro h1
            simp only [if_pos hd] at h1
            simp only [hc, if_pos hcm]
            exact hdc x (ih d hd h1)
        · rw [md_ne C g b d k hkg] at hv
          refine opMono_imp (gateAt C k).op (hAO.1 _ (gateAt_mem hk)) (gateAt C k).inputs
            (fun i => if i < n + k then val (md C g b d) (List.ofFn x) i else false)
            (fun i => if i < n + k then val C (List.ofFn x) i else false) ?_ hv
          intro i _
          by_cases hi : i < n + k
          · simp only [if_pos hi]
            exact ih i hi
          · simp [hi]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

lemma tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

lemma exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  classical
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

lemma all4 (n : ℕ) (C : Circuit) (g b c d : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (hb : b < 2)
    (hc : (gateAt C g).inputs.getD b 0 = c) (hd : d < n + g)
    (hdc : ∀ x : Fin n → Bool, val C (List.ofFn x) d = true → val C (List.ofFn x) c = true) :
    PEqualNP.TopForm.IsAO2 n (md C g b d) ∧ (md C g b d).size = C.size ∧
    (∀ x : Fin n → Bool, circuitFun n (md C g b d) x = true → circuitFun n C x = true) ∧
    (circuitFun n (md C g b d) = circuitFun n C ↔
      (∀ x : Fin n → Bool, (circuitFun n C x = true ∧ ∀ y : Fin n → Bool,
        (∀ i, y i = true → x i = true) → y ≠ x → circuitFun n C y = false) →
        circuitFun n (md C g b d) x = true)) := by
  have hA2 := md_ao2 n C g b d hAO hg hd
  have h3 : ∀ x : Fin n → Bool, circuitFun n (md C g b d) x = true → circuitFun n C x = true :=
    fun x h => narrow n C g b c d hAO hg hb hc hd hdc x C.output h
  refine ⟨hA2, md_len C g b d, h3, ?_⟩
  constructor
  · intro hE x hx
    rw [hE]
    exact hx.1
  · intro H
    funext x
    cases h' : circuitFun n (md C g b d) x
    · cases h : circuitFun n C x
      · rfl
      · exfalso
        obtain ⟨y, hyx, hy, hmin⟩ := exists_min (circuitFun n C) x h
        have h1 : circuitFun n (md C g b d) y = true := H y ⟨hy, hmin⟩
        have h2 : circuitFun n (md C g b d) x = true :=
          mono n (md C g b d) hA2.1 y x hyx (md C g b d).output h1
        rw [h'] at h2
        exact Bool.false_ne_true h2
    · exact (h3 x h').symm

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) := by
  intro n C g b c d h
  obtain ⟨hAO, _, hg, hb, hc, hd, hdc⟩ := h
  exact all4 n C g b c d hAO hg hb hc hd hdc

end PEqualNP.Outside.L_meta_2852

theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) :=
  PEqualNP.Outside.L_meta_2852.main_aux
