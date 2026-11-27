import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L613

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

private theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

private theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

private theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

private def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

private def e2 {n : ℕ} (c t : Fin n) : Fin n → Bool := fun i => decide (i = c ∨ i = t)

private def ne1 {n : ℕ} (c : Fin n) : Fin n → Bool := fun i => decide (i ≠ c)

private def Rd (C : Circuit) (n : ℕ) (a b : ℕ) : Prop :=
  b < a ∧ ∃ h : Gate, C.gates[a]? = some h ∧ n + b ∈ h.inputs

private def Lin (C : Circuit) (n : ℕ) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C n x w = true ↔ ∃ i : Fin n, x i = true ∧ val C n (e1 i) w = true

private def Low (C : Circuit) (n : ℕ) (A : Finset ℕ) (b : ℕ) : Prop :=
  b ∉ A ∧ ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) b i

private def Sing (C : Circuit) (n : ℕ) (w : ℕ) : Prop :=
  ∃ t : Fin n, ∀ i : Fin n, val C n (e1 i) w = true ↔ i = t

private def Subst (C : Circuit) (n : ℕ) (k : ℕ) : Prop :=
  (∃ x : Fin n → Bool, val C n x (n + k) = true) ∧ ¬ Sing C n (n + k)

private def InS (C : Circuit) (n : ℕ) (o g : ℕ) : Prop :=
  Relation.ReflTransGen (fun a b => Rd C n a b ∧ Subst C n b) o g

private theorem card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (Q : α → β → Prop)
    (h1 : ∀ a ∈ s, ∃ b ∈ t, Q a b)
    (h2 : ∀ a1 ∈ s, ∀ a2 ∈ s, ∀ b, Q a1 b → Q a2 b → a1 = a2) : s.card ≤ t.card := by
  classical
  have hsub : s ⊆ t.biUnion (fun b => s.filter (fun a => Q a b)) := by
    intro a ha
    obtain ⟨b, hb, hq⟩ := h1 a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hq⟩⟩
  calc s.card ≤ (t.biUnion fun b => s.filter fun a => Q a b).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ t, (s.filter fun a => Q a b).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ t, 1 := Finset.sum_le_sum (fun b _ => Finset.card_le_one.mpr (by
        intro a1 h1' a2 h2'
        rw [Finset.mem_filter] at h1' h2'
        exact h2 a1 h1'.1 a2 h2'.1 b h1'.2 h2'.2))
    _ = t.card := by simp

private theorem two_mem (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ w ∈ l, w = a ∨ w = b := by
  intro w hw
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hw
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hw
    omega
  · simp at hl

private theorem gate_or (C : Circuit) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hj : j ∉ A) : h.op = GateOp.or := by
  have hmem : h ∈ C.gates := List.mem_of_getElem? hg
  have hop := (hMono h hmem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · exact absurd ((hA j).mpr ⟨h, hg, hop⟩) hj
  · exact hop

private theorem input_e1 (C : Circuit) (n : ℕ) (w : ℕ) (hw : w < n) (t : Fin n)
    (hv : val C n (e1 t) w = true) : (⟨w, hw⟩ : Fin n) = t := by
  rw [val_input C n _ w hw] at hv
  simpa [e1] using hv

private theorem lin_input (C : Circuit) (n : ℕ) (w : ℕ) (hw : w < n) : Lin C n w := by
  intro x
  rw [val_input C n x w hw]
  constructor
  · intro hx
    exact ⟨⟨w, hw⟩, hx, by rw [val_input C n _ w hw]; simp [e1]⟩
  · rintro ⟨i, hi, hv⟩
    rw [input_e1 C n w hw i hv]
    exact hi

private theorem low_down (C : Circuit) (n : ℕ) (A : Finset ℕ) (b k : ℕ)
    (hb : Low C n A b) (hr : Rd C n b k) : Low C n A k :=
  ⟨fun hk => hb.2 k hk (Relation.TransGen.single hr),
   fun i hi ht => hb.2 i hi (Relation.TransGen.head hr ht)⟩

private theorem low_lin (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and) :
    ∀ (b : ℕ) (h : Gate), C.gates[b]? = some h → Low C n A b → Lin C n (n + b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hg hlow
    have hop := gate_or C A hMono hA b h hg hlow.1
    have hread : ∀ w ∈ h.inputs, w < n + b → Lin C n w := by
      intro w hw hlt
      by_cases hwn : w < n
      · exact lin_input C n w hwn
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hkb : k < b := by omega
        have hblen : b < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
        have hklen : k < C.gates.length := by omega
        exact ih k hkb _ (List.getElem?_eq_getElem hklen)
          (low_down C n A b k hlow ⟨hkb, h, hg, hw⟩)
    intro x
    constructor
    · intro hx
      obtain ⟨w, hw, hlt, hv⟩ := (val_or C n x b h hg hop).mp hx
      obtain ⟨i, hi, hiv⟩ := (hread w hw hlt x).mp hv
      exact ⟨i, hi, (val_or C n _ b h hg hop).mpr ⟨w, hw, hlt, hiv⟩⟩
    · rintro ⟨i, hi, hiv⟩
      obtain ⟨w, hw, hlt, hv⟩ := (val_or C n _ b h hg hop).mp hiv
      exact (val_or C n x b h hg hop).mpr ⟨w, hw, hlt, (hread w hw hlt x).mpr ⟨i, hi, hv⟩⟩

private theorem and_reads_low (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hjA : j ∈ A)
    (k : ℕ) (hw : n + k ∈ h.inputs) (hkj : k < j) : Low C n A k :=
  ⟨fun hk => h5 j hjA k hk (Relation.TransGen.single ⟨hkj, h, hg, hw⟩),
   fun i hi ht => h5 j hjA i hi (Relation.TransGen.head ⟨hkj, h, hg, hw⟩ ht)⟩

private theorem and_reads_lin (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hjA : j ∈ A)
    (w : ℕ) (hw : w ∈ h.inputs) (hlt : w < n + j) : Lin C n w := by
  by_cases hwn : w < n
  · exact lin_input C n w hwn
  · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hkj : k < j := by omega
    have hjlen : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
    have hklen : k < C.gates.length := by omega
    exact low_lin C n A hMono hA k _ (List.getElem?_eq_getElem hklen)
      (and_reads_low C n A h5 j h hg hjA k hw hkj)

private theorem no_edge_e1 {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) :
    ¬ ∃ u v : Fin n, G.Adj u v ∧ e1 c u = true ∧ e1 c v = true := by
  rintro ⟨u, v, hadj, hu, hv⟩
  have hu' : u = c := by simpa [e1] using hu
  have hv' : v = c := by simpa [e1] using hv
  exact hadj.ne (hu'.trans hv'.symm)

private theorem edge_e2 {n : ℕ} (G : SimpleGraph (Fin n)) (c i : Fin n)
    (h : ∃ u v : Fin n, G.Adj u v ∧ e2 c i u = true ∧ e2 c i v = true) : G.Adj c i := by
  obtain ⟨u, v, hadj, hu, hv⟩ := h
  have hu' : u = c ∨ u = i := by simpa [e2] using hu
  have hv' : v = c ∨ v = i := by simpa [e2] using hv
  rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
  · exact absurd (hu'.trans hv'.symm) hadj.ne
  · rw [hu', hv'] at hadj; exact hadj
  · rw [hu', hv'] at hadj; exact hadj.symm
  · exact absurd (hu'.trans hv'.symm) hadj.ne

private theorem center_read (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (cen : ℕ → Fin n) (G : SimpleGraph (Fin n))
    (h4 : ∀ j ∈ A, ∀ x : Fin n → Bool, val C n x (n + j) = true →
      (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and)
    (x0 : Fin n → Bool) (hx0 : val C n x0 (n + j) = true) :
    ∃ w ∈ h.inputs, w < n + j ∧ ∀ i : Fin n, val C n (e1 i) w = true ↔ i = cen j := by
  have hjA : j ∈ A := (hA j).mpr ⟨h, hg, hop⟩
  by_contra hne
  have hall := (val_and C n x0 j h hg hop).mp hx0
  have hy : val C n (ne1 (cen j)) (n + j) = true := by
    refine (val_and C n _ j h hg hop).mpr (fun w hw => ?_)
    obtain ⟨hlt, hv⟩ := hall w hw
    have hl := and_reads_lin C n A hMono hA h5 j h hg hjA w hw hlt
    obtain ⟨i0, hi0, hi0v⟩ := (hl x0).mp hv
    refine ⟨hlt, ?_⟩
    by_cases hall' : ∀ i : Fin n, val C n (e1 i) w = true → i = cen j
    · exfalso
      exact hne ⟨w, hw, hlt, fun i => ⟨hall' i, fun hi => by
        rw [hi, ← hall' i0 hi0v]; exact hi0v⟩⟩
    · push Not at hall'
      obtain ⟨i, hiv, hic⟩ := hall'
      exact (hl _).mpr ⟨i, by simp [ne1, hic], hiv⟩
  have hc := (h4 j hjA _ hy).2
  simp [ne1] at hc

private theorem upper (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (o : ℕ) (x : Fin n → Bool) :
    ∀ g : ℕ, InS C n o g → (∀ i : Fin n, val C n (e1 i) (n + g) ≠ true) →
      val C n x (n + g) = true → ∃ j ∈ A, InS C n o j ∧ val C n x (n + j) = true := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hS hV hx
    by_cases hgA : g ∈ A
    · exact ⟨g, hgA, hS, hx⟩
    · cases hg : C.gates[g]? with
      | none =>
        rw [val_none C n x g hg] at hx
        simp at hx
      | some h =>
        have hop := gate_or C A hMono hA g h hg hgA
        obtain ⟨w, hw, hlt, hv⟩ := (val_or C n x g h hg hop).mp hx
        have hup : ∀ y : Fin n → Bool, val C n y w = true → val C n y (n + g) = true :=
          fun y hy => (val_or C n y g h hg hop).mpr ⟨w, hw, hlt, hy⟩
        by_cases hwn : w < n
        · exfalso
          refine hV ⟨w, hwn⟩ (hup _ ?_)
          rw [val_input C n _ w hwn]
          simp [e1]
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hsub : Subst C n k :=
            ⟨⟨x, hv⟩, fun ⟨t, ht⟩ => hV t (hup _ ((ht t).mpr rfl))⟩
          exact ih k (by omega) (hS.tail ⟨⟨by omega, h, hg, hw⟩, hsub⟩)
            (fun i hi => hV i (hup _ hi)) hv

private theorem leaf (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (G : SimpleGraph (Fin n)) (o : ℕ) (c t : Fin n) :
    ∀ k : ℕ, InS C n o k → Low C n A k →
      (∀ i : Fin n, val C n (e1 i) (n + k) = true → G.Adj c i) →
      val C n (e1 t) (n + k) = true →
      (∃ t' : Fin n, t' ≠ t ∧ val C n (e1 t') (n + k) = true) →
      ∃ g w : ℕ, InS C n o g ∧ g ∉ A ∧
        (∃ h : Gate, C.gates[g]? = some h ∧ w ∈ h.inputs ∧ w < n + g) ∧
        (∀ i : Fin n, val C n (e1 i) w = true ↔ i = t) ∧
        (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + g) = true ∧
          val C n (e1 b) (n + g) = true) ∧
        (∀ i : Fin n, val C n (e1 i) (n + g) = true → G.Adj c i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hS hlow hadj ht hex
    cases hg : C.gates[k]? with
    | none =>
      rw [val_none C n _ k hg] at ht
      simp at ht
    | some h =>
      have hop := gate_or C A hMono hA k h hg hlow.1
      obtain ⟨w, hw, hlt, hv⟩ := (val_or C n _ k h hg hop).mp ht
      have hup : ∀ y : Fin n → Bool, val C n y w = true → val C n y (n + k) = true :=
        fun y hy => (val_or C n y k h hg hop).mpr ⟨w, hw, hlt, hy⟩
      by_cases hs : ∀ i : Fin n, val C n (e1 i) w = true → i = t
      · obtain ⟨t', ht', hv'⟩ := hex
        exact ⟨k, w, hS, hlow.1, ⟨h, hg, hw, hlt⟩,
          fun i => ⟨hs i, fun hi => by rw [hi]; exact hv⟩, ⟨t', t, ht', hv', ht⟩, hadj⟩
      · push Not at hs
        obtain ⟨t2, ht2v, ht2⟩ := hs
        have hwn : ¬ w < n := by
          intro hwn
          have a1 := input_e1 C n w hwn t hv
          have a2 := input_e1 C n w hwn t2 ht2v
          exact ht2 (a2.symm.trans a1)
        obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have hr : Rd C n k k' := ⟨by omega, h, hg, hw⟩
        have hsub : Subst C n k' :=
          ⟨⟨_, hv⟩, fun ⟨t0, ht0⟩ => ht2 (((ht0 t2).mp ht2v).trans ((ht0 t).mp hv).symm)⟩
        exact ih k' (by omega) (hS.tail ⟨hr, hsub⟩) (low_down C n A k k' hlow hr)
          (fun i hi => hadj i (hup _ hi)) hv ⟨t2, ht2, ht2v⟩

private theorem edge_pair (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (cen : ℕ → Fin n) (G : SimpleGraph (Fin n))
    (h4 : ∀ j ∈ A, ∀ x : Fin n → Bool, val C n x (n + j) = true →
      (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (o j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and)
    (hS : InS C n o j) (t : Fin n) (hadj : G.Adj (cen j) t)
    (hx : val C n (e2 (cen j) t) (n + j) = true) :
    ∃ g w : ℕ, InS C n o g ∧
      (∃ h' : Gate, C.gates[g]? = some h' ∧ w ∈ h'.inputs ∧ w < n + g) ∧
      (∀ i : Fin n, val C n (e1 i) w = true ↔ i = t) ∧
      ((g ∈ A ∧ cen g = cen j) ∨ (g ∉ A ∧
        (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + g) = true ∧
          val C n (e1 b) (n + g) = true) ∧
        (∀ i : Fin n, val C n (e1 i) (n + g) = true → G.Adj (cen j) i))) := by
  have hjA : j ∈ A := (hA j).mpr ⟨h, hg, hop⟩
  have hall := (val_and C n _ j h hg hop).mp hx
  have hlin : ∀ w ∈ h.inputs, w < n + j → Lin C n w :=
    fun w hw hlt => and_reads_lin C n A hMono hA h5 j h hg hjA w hw hlt
  have hw0 : ∃ w0 ∈ h.inputs, val C n (e1 t) w0 = true := by
    by_contra hno
    have hc : val C n (e1 (cen j)) (n + j) = true := by
      refine (val_and C n _ j h hg hop).mpr (fun w hw => ?_)
      obtain ⟨hlt, hv⟩ := hall w hw
      obtain ⟨i, hi, hiv⟩ := (hlin w hw hlt _).mp hv
      have hi' : i = cen j ∨ i = t := by simpa [e2] using hi
      rcases hi' with hi' | hi'
      · rw [hi'] at hiv
        exact ⟨hlt, hiv⟩
      · rw [hi'] at hiv
        exact absurd ⟨w, hw, hiv⟩ hno
    exact no_edge_e1 G (cen j) (h4 j hjA _ hc).1
  obtain ⟨w0, hw0, hv0⟩ := hw0
  obtain ⟨hlt0, _⟩ := hall w0 hw0
  by_cases hs : ∀ i : Fin n, val C n (e1 i) w0 = true → i = t
  · exact ⟨j, w0, hS, ⟨h, hg, hw0, hlt0⟩,
      fun i => ⟨hs i, fun hi => by rw [hi]; exact hv0⟩, Or.inl ⟨hjA, rfl⟩⟩
  · push Not at hs
    obtain ⟨t2, ht2v, ht2⟩ := hs
    have hwn : ¬ w0 < n := by
      intro hwn
      have a1 := input_e1 C n w0 hwn t hv0
      have a2 := input_e1 C n w0 hwn t2 ht2v
      exact ht2 (a2.symm.trans a1)
    obtain ⟨k, rfl⟩ : ∃ k, w0 = n + k := ⟨w0 - n, by omega⟩
    have hkj : k < j := by omega
    have hlowk : Low C n A k := and_reads_low C n A h5 j h hg hjA k hw0 hkj
    obtain ⟨w1, hw1, hlt1, hiff1⟩ :=
      center_read C n A hMono hA cen G h4 h5 j h hg hop _ hx
    have hne01 : n + k ≠ w1 := by
      intro heq
      rw [← heq] at hiff1
      exact hadj.ne ((hiff1 t).mp hv0).symm
    have hmem : ∀ w ∈ h.inputs, w = n + k ∨ w = w1 :=
      two_mem h.inputs (hMono h (List.mem_of_getElem? hg)).2 (n + k) w1 hw0 hw1 hne01
    have hadjk : ∀ i : Fin n, val C n (e1 i) (n + k) = true → G.Adj (cen j) i := by
      intro i hi
      have hy : val C n (e2 (cen j) i) (n + j) = true := by
        refine (val_and C n _ j h hg hop).mpr (fun w hw => ?_)
        rcases hmem w hw with hww | hww
        · rw [hww]
          exact ⟨hlt0, (hlin _ hw0 hlt0 _).mpr ⟨i, by simp [e2], hi⟩⟩
        · rw [hww]
          exact ⟨hlt1, (hlin _ hw1 hlt1 _).mpr ⟨cen j, by simp [e2], (hiff1 _).mpr rfl⟩⟩
      exact edge_e2 G _ _ (h4 j hjA _ hy).1
    have hsub : Subst C n k :=
      ⟨⟨_, hv0⟩, fun ⟨t0, ht0⟩ => ht2 (((ht0 t2).mp ht2v).trans ((ht0 t).mp hv0).symm)⟩
    have hSk : InS C n o k := hS.tail ⟨⟨hkj, h, hg, hw0⟩, hsub⟩
    obtain ⟨g, w, hSg, hgA, hrd, hiff, hab, hadjg⟩ :=
      leaf C n A hMono hA G o (cen j) t k hSk hlowk hadjk hv0 ⟨t2, ht2, ht2v⟩
    exact ⟨g, w, hSg, hrd, hiff, Or.inr ⟨hgA, hab, hadjg⟩⟩

private theorem main_thm (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (cen : ℕ → Fin n)
    (A : Finset ℕ)
    (hC4 : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (hMono : Monotone2 C)
    (hf : ∀ x : Fin n → Bool, (val C n x C.output = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (h4 : ∀ j ∈ A, ∀ x : Fin n → Bool, val C n x (n + j) = true →
      (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i) :
    G.edgeSet.ncard + (A.image cen).card ≤ C.size + 1 := by
  classical
  have hAlt : ∀ j ∈ A, j < C.size := by
    intro j hj
    obtain ⟨g, hg, _⟩ := (hA j).mp hj
    exact (List.getElem?_eq_some_iff.mp hg).1
  by_cases hE : G.edgeSet = ∅
  · rw [hE, Set.ncard_empty, zero_add]
    have h1 : (A.image cen).card ≤ A.card := Finset.card_image_le
    have h2 : A.card ≤ (Finset.range C.size).card :=
      Finset.card_le_card (fun j hj => Finset.mem_range.mpr (hAlt j hj))
    rw [Finset.card_range] at h2
    omega
  · obtain ⟨e0, he0⟩ := Set.nonempty_iff_ne_empty.mpr hE
    induction e0 using Sym2.ind with
    | _ u0 v0 =>
    have hadj0 : G.Adj u0 v0 := by simpa using he0
    have hx0 : val C n (e2 u0 v0) C.output = true :=
      (hf _).mpr ⟨u0, v0, hadj0, by simp [e2], by simp [e2]⟩
    have hout : ¬ C.output < n := by
      intro hlt
      have h1 : val C n (e1 ⟨C.output, hlt⟩) C.output = true := by
        rw [val_input C n _ _ hlt]
        simp [e1]
      exact no_edge_e1 G _ ((hf _).mp h1)
    obtain ⟨o, ho⟩ : ∃ o, C.output = n + o := ⟨C.output - n, by omega⟩
    rw [ho] at hf hx0
    have hVo : ∀ i : Fin n, val C n (e1 i) (n + o) ≠ true :=
      fun i hi => no_edge_e1 G i ((hf _).mp hi)
    have hsubo : Subst C n o := ⟨⟨_, hx0⟩, fun ⟨t, ht⟩ => hVo t ((ht t).mpr rfl)⟩
    have hSsub : ∀ g, InS C n o g → Subst C n g := by
      intro g hg
      rcases Relation.ReflTransGen.cases_tail hg with heq | ⟨p, _, hr⟩
      · rw [heq]; exact hsubo
      · exact hr.2
    have hSgate : ∀ g, InS C n o g → ∃ h : Gate, C.gates[g]? = some h := by
      intro g hg
      obtain ⟨⟨x, hx⟩, _⟩ := hSsub g hg
      cases hgg : C.gates[g]? with
      | none =>
        rw [val_none C n x g hgg] at hx
        simp at hx
      | some h => exact ⟨h, rfl⟩
    let S : Finset ℕ := (Finset.range C.size).filter (fun g => InS C n o g)
    have hSmem : ∀ g, g ∈ S ↔ InS C n o g := by
      intro g
      simp only [S, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
      intro hg
      obtain ⟨h, hh⟩ := hSgate g hg
      exact (List.getElem?_eq_some_iff.mp hh).1
    let rd : ℕ → Finset ℕ := fun g =>
      (Finset.range (n + g)).filter (fun w => ∃ h : Gate, C.gates[g]? = some h ∧ w ∈ h.inputs)
    have hrd : ∀ g, (rd g).card ≤ 2 := by
      intro g
      cases hgg : C.gates[g]? with
      | none =>
        have : rd g = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro w hw
          simp only [rd, Finset.mem_filter, hgg] at hw
          obtain ⟨_, h, hh, _⟩ := hw
          exact absurd hh (by simp)
        rw [this]; simp
      | some h =>
        have hsub : rd g ⊆ h.inputs.toFinset := by
          intro w hw
          simp only [rd, Finset.mem_filter, hgg] at hw
          obtain ⟨_, h', hh, hw'⟩ := hw
          rw [← Option.some.inj hh] at hw'
          exact List.mem_toFinset.mpr hw'
        calc (rd g).card ≤ h.inputs.toFinset.card := Finset.card_le_card hsub
          _ ≤ h.inputs.length := List.toFinset_card_le _
          _ ≤ 2 := (hMono h (List.mem_of_getElem? hgg)).2
    let Z : Finset (ℕ × ℕ) := S.biUnion (fun g => (rd g).image (fun w => (g, w)))
    have hZcard : Z.card ≤ 2 * S.card := by
      calc Z.card ≤ ∑ g ∈ S, ((rd g).image (fun w => (g, w))).card := Finset.card_biUnion_le
        _ ≤ ∑ g ∈ S, 2 := Finset.sum_le_sum (fun g _ => Finset.card_image_le.trans (hrd g))
        _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hZmem : ∀ g w, InS C n o g →
        (∃ h : Gate, C.gates[g]? = some h ∧ w ∈ h.inputs ∧ w < n + g) → (g, w) ∈ Z := by
      intro g w hg hr
      obtain ⟨h, hh, hw, hlt⟩ := hr
      refine Finset.mem_biUnion.mpr ⟨g, (hSmem g).mpr hg, Finset.mem_image.mpr ⟨w, ?_, rfl⟩⟩
      simp only [rd, Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, h, hh, hw⟩
    let P2 : ℕ × ℕ → Prop := fun z =>
      z.1 ∈ A ∧ ∀ i : Fin n, val C n (e1 i) z.2 = true ↔ i = cen z.1
    let Z1 : Finset (ℕ × ℕ) := Z.filter (fun z => ¬ Sing C n z.2)
    let Zs : Finset (ℕ × ℕ) := Z.filter (fun z => Sing C n z.2)
    let Z2 : Finset (ℕ × ℕ) := Zs.filter (fun z => P2 z)
    let Z3 : Finset (ℕ × ℕ) := Zs.filter (fun z => ¬ P2 z)
    have hsplit1 : Zs.card + Z1.card = Z.card :=
      Finset.card_filter_add_card_filter_not (s := Z) (fun z : ℕ × ℕ => Sing C n z.2)
    have hsplit2 : Z2.card + Z3.card = Zs.card :=
      Finset.card_filter_add_card_filter_not (s := Zs) (fun z : ℕ × ℕ => P2 z)
    have hoS : o ∈ S := (hSmem o).mpr Relation.ReflTransGen.refl
    have hb1 : (S.erase o).card ≤ Z1.card := by
      apply card_le_of_rel _ _ (fun k z => z.2 = n + k)
      · intro k hk
        obtain ⟨hko, hkS⟩ := Finset.mem_erase.mp hk
        have hkS' := (hSmem k).mp hkS
        rcases Relation.ReflTransGen.cases_tail hkS' with heq | ⟨p, hp, hr⟩
        · exact absurd heq hko
        · obtain ⟨⟨hlt, h, hh, hmem⟩, hsub⟩ := hr
          refine ⟨(p, n + k), Finset.mem_filter.mpr ⟨hZmem p (n + k) hp ⟨h, hh, hmem, by omega⟩, hsub.2⟩, rfl⟩
      · intro k1 _ k2 _ z hz1 hz2
        have : n + k1 = n + k2 := hz1.symm.trans hz2
        omega
    have hb2 : (A ∩ S).card ≤ Z2.card := by
      apply card_le_of_rel _ _ (fun j z => z.1 = j)
      · intro j hj
        obtain ⟨hjA, hjS⟩ := Finset.mem_inter.mp hj
        have hjS' := (hSmem j).mp hjS
        obtain ⟨h, hg, hop⟩ := (hA j).mp hjA
        obtain ⟨⟨x, hx⟩, _⟩ := hSsub j hjS'
        obtain ⟨w, hw, hlt, hiff⟩ := center_read C n A hMono hA cen G h4 h5 j h hg hop x hx
        refine ⟨(j, w), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZmem j w hjS' ⟨h, hg, hw, hlt⟩, ⟨cen j, hiff⟩⟩, hjA, hiff⟩
      · intro j1 _ j2 _ z hz1 hz2
        exact hz1.symm.trans hz2
    have hfin : G.edgeSet.Finite := Set.toFinite _
    have hb3 : G.edgeSet.ncard ≤ Z3.card := by
      rw [Set.ncard_eq_toFinset_card G.edgeSet hfin]
      apply card_le_of_rel _ _ (fun (e : Sym2 (Fin n)) (z : ℕ × ℕ) => ∃ c t : Fin n,
        e = s(c, t) ∧ (∀ i : Fin n, val C n (e1 i) z.2 = true ↔ i = t) ∧
        ((z.1 ∈ A ∧ cen z.1 = c) ∨ (z.1 ∉ A ∧
          (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + z.1) = true ∧
            val C n (e1 b) (n + z.1) = true) ∧
          (∀ i : Fin n, val C n (e1 i) (n + z.1) = true → G.Adj c i))))
      · intro e he
        have he' : e ∈ G.edgeSet := (Set.Finite.mem_toFinset hfin).mp he
        induction e using Sym2.ind with
        | _ u v =>
        have hadj : G.Adj u v := by simpa using he'
        have hxe : val C n (e2 u v) (n + o) = true :=
          (hf _).mpr ⟨u, v, hadj, by simp [e2], by simp [e2]⟩
        obtain ⟨j, hjA, hjS, hjx⟩ :=
          upper C n A hMono hA o (e2 u v) o Relation.ReflTransGen.refl hVo hxe
        obtain ⟨h, hg, hop⟩ := (hA j).mp hjA
        have hcen : cen j = u ∨ cen j = v := by
          have := (h4 j hjA _ hjx).2
          simpa [e2] using this
        have key : ∀ c t : Fin n, cen j = c → G.Adj c t → val C n (e2 c t) (n + j) = true →
            ∃ z ∈ Z3, ∃ c' t' : Fin n,
              s(c, t) = s(c', t') ∧ (∀ i : Fin n, val C n (e1 i) z.2 = true ↔ i = t') ∧
              ((z.1 ∈ A ∧ cen z.1 = c') ∨ (z.1 ∉ A ∧
                (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + z.1) = true ∧
                  val C n (e1 b) (n + z.1) = true) ∧
                (∀ i : Fin n, val C n (e1 i) (n + z.1) = true → G.Adj c' i))) := by
          intro c t hc hadjct hval
          subst hc
          obtain ⟨g, w, hSg, hrdw, hiff, hor⟩ :=
            edge_pair C n A hMono hA cen G h4 h5 o j h hg hop hjS t hadjct hval
          refine ⟨(g, w), ?_, cen j, t, rfl, hiff, hor⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZmem g w hSg hrdw, ⟨t, hiff⟩⟩, ?_⟩
          rintro ⟨hgA, hcg⟩
          rcases hor with ⟨_, hc'⟩ | ⟨hng, _⟩
          · have : t = cen g := (hcg t).mp ((hiff t).mpr rfl)
            rw [hc'] at this
            exact hadjct.ne this.symm
          · exact hng hgA
        rcases hcen with hc | hc
        · exact key u v hc hadj hjx
        · have hswap : e2 v u = e2 u v := by
            funext i
            simp [e2, or_comm]
          have := key v u hc hadj.symm (by rw [hswap]; exact hjx)
          rw [Sym2.eq_swap] at this
          exact this
      · rintro ea _ eb _ z ⟨c1, t1, rfl, hi1, hor1⟩ ⟨c2, t2, rfl, hi2, hor2⟩
        have ht : t1 = t2 := (hi2 t1).mp ((hi1 t1).mpr rfl)
        have hc : c1 = c2 := by
          rcases hor1 with ⟨hzA1, hc1⟩ | ⟨hzA1, ⟨a, b, hab, hva, hvb⟩, hadj1⟩
          · rcases hor2 with ⟨_, hc2⟩ | ⟨hzA2, _, _⟩
            · exact hc1.symm.trans hc2
            · exact absurd hzA1 hzA2
          · rcases hor2 with ⟨hzA2, _⟩ | ⟨_, _, hadj2⟩
            · exact absurd hzA2 hzA1
            · by_contra hne
              have ha1 := hadj1 a hva
              have hb1' := hadj1 b hvb
              have ha2 := hadj2 a hva
              have hb2' := hadj2 b hvb
              exact hC4 c1 a c2 b ha1.ne hne hb1'.ne ha2.ne.symm hab hb2'.ne
                ha1 ha2.symm hb2' hb1'.symm
        rw [ht, hc]
    have hU : (A \ S).card + S.card = (A ∪ S).card := Finset.card_sdiff_add_card A S
    have hI : (A \ S).card + (A ∩ S).card = A.card := Finset.card_sdiff_add_card_inter A S
    have hsubR : (A ∪ S).card ≤ C.size := by
      have : A ∪ S ⊆ Finset.range C.size := by
        intro g hg
        rcases Finset.mem_union.mp hg with hgA | hgS
        · exact Finset.mem_range.mpr (hAlt g hgA)
        · exact (Finset.mem_filter.mp hgS).1
      have h := Finset.card_le_card this
      rwa [Finset.card_range] at h
    have himg : (A.image cen).card ≤ A.card := Finset.card_image_le
    have hero : (S.erase o).card = S.card - 1 := Finset.card_erase_of_mem hoS
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨o, hoS⟩
    omega

end PEqualNP.Outside.L613

theorem PEqualNP.Outside.L_meta_613 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (cen : ℕ → Fin n) (A : Finset ℕ), (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ j ∈ A, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = true → (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true) → (∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (fun a b : ℕ => b < a ∧ ∃ h : PEqualNP.CircuitLowerBounds.Gate, C.gates[a]? = some h ∧ n + b ∈ h.inputs) j i) → G.edgeSet.ncard + (A.image cen).card ≤ C.size + 1 := by
  intro n G C cen A hC4 hMono hf hA h4 h5
  exact PEqualNP.Outside.L613.main_thm n G C cen A hC4 hMono hf hA h4 h5
