import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L598

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
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

def Wv (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem Wv_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    Wv C n x i = x i := by
  unfold Wv
  rw [wires_eq, foldl_step_getD _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem Wv_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t : ℕ) (ht : t < C.gates.length) :
    Wv C n x (n + t) = (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
      if i < n + t then Wv C n x i else false) := by
  have := gate_value C.gates (List.ofFn x) t ht
  rw [List.length_ofFn] at this
  exact this

theorem Wv_big (C : Circuit) (n : ℕ) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : Wv C n x i = false := by
  unfold Wv
  rw [wires_eq]
  apply getD_of_length_le
  rw [foldl_step_length, List.length_ofFn]
  exact hi

def Rd (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t i : ℕ) : Bool :=
  if i < n + t then Wv C n x i else false

def DomZ {n : ℕ} (Z : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∀ z ∈ Z, x z = false

def NI (C : Circuit) (n : ℕ) (Z : Finset (Fin n)) (t : ℕ) : Prop :=
  ∃ g, C.gates[t]? = some g ∧ g.op = GateOp.or ∧ 2 ≤ g.inputs.length ∧
    ∀ i ∈ g.inputs, ∃ x, DomZ Z x ∧ Wv C n x (n + t) ≠ Rd C n x t i

theorem NI_mono (C : Circuit) (n : ℕ) (Z : Finset (Fin n)) (v : Fin n) (t : ℕ)
    (h : NI C n (insert v Z) t) : NI C n Z t := by
  obtain ⟨g, hg, hop, hlen, hi⟩ := h
  refine ⟨g, hg, hop, hlen, fun i hi' => ?_⟩
  obtain ⟨x, hx, hne⟩ := hi i hi'
  exact ⟨x, fun z hz => hx z (Finset.mem_insert_of_mem hz), hne⟩

def Killed (C : Circuit) (n : ℕ) (Z : Finset (Fin n)) (v : Fin n) (i : ℕ) : Prop :=
  ∀ x, DomZ (insert v Z) x → Wv C n x i = false

def Indep (C : Circuit) (n : ℕ) (Z : Finset (Fin n)) (v : Fin n) (i : ℕ) : Prop :=
  ∀ x, DomZ Z x → Wv C n x i = Wv C n (Function.update x v false) i

theorem dich (C : Circuit) (n : ℕ) (hmono : Monotone2 C) (Z : Finset (Fin n)) (v : Fin n)
    (H : ∀ t, NI C n Z t → NI C n (insert v Z) t) :
    ∀ i, Killed C n Z v i ∨ Indep C n Z v i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  have hdomu : ∀ x, DomZ Z x → DomZ Z (Function.update x v false) := by
    intro x hx z hz
    by_cases hzv : z = v
    · subst hzv; simp
    · rw [Function.update_of_ne hzv]; exact hx z hz
  have hdomZ : ∀ x, DomZ (insert v Z) x → DomZ Z x :=
    fun x hx z hz => hx z (Finset.mem_insert_of_mem hz)
  by_cases hin : i < n
  · by_cases hiv : (⟨i, hin⟩ : Fin n) = v
    · left
      intro x hx
      have h1 := Wv_input C n x ⟨i, hin⟩
      simp only at h1
      rw [h1, hiv]
      exact hx v (Finset.mem_insert_self v Z)
    · right
      intro x hx
      have h1 := Wv_input C n x ⟨i, hin⟩
      have h2 := Wv_input C n (Function.update x v false) ⟨i, hin⟩
      simp only at h1 h2
      rw [h1, h2, Function.update_of_ne hiv]
  · by_cases hbig : n + C.gates.length ≤ i
    · right
      intro x hx
      rw [Wv_big C n x i hbig, Wv_big C n _ i hbig]
    · obtain ⟨t, rfl⟩ : ∃ t, i = n + t := ⟨i - n, by omega⟩
      have ht : t < C.gates.length := by omega
      have hrd : ∀ j, (∀ x, DomZ (insert v Z) x → Rd C n x t j = false) ∨
          (∀ x, DomZ Z x → Rd C n x t j = Rd C n (Function.update x v false) t j) := by
        intro j
        by_cases hj : j < n + t
        · rcases ih j hj with h | h
          · left; intro x hx; simp only [Rd, hj, ite_true]; exact h x hx
          · right; intro x hx; simp only [Rd, hj, ite_true]; exact h x hx
        · right; intro x hx; simp only [Rd, hj, ite_false]
      have hval : ∀ x, Wv C n x (n + t) =
          (C.gates[t]).op.eval ((C.gates[t]).inputs.map (Rd C n x t)) := by
        intro x; rw [Wv_gate C n x t ht]; rfl
      have hg : C.gates[t]? = some (C.gates[t]) := List.getElem?_eq_getElem ht
      obtain ⟨hop, hlen⟩ := hmono (C.gates[t]) (List.getElem_mem ht)
      have hallI : (∀ j ∈ (C.gates[t]).inputs, ∀ x, DomZ Z x →
          Rd C n x t j = Rd C n (Function.update x v false) t j) → Indep C n Z v (n + t) := by
        intro h x hx
        rw [hval, hval]
        congr 1
        apply List.map_congr_left
        intro j hj
        exact h j hj x hx
      have hop' : (C.gates[t]).op = GateOp.and ∨ (C.gates[t]).op = GateOp.or := by
        simpa using hop
      rcases hop' with hand | hor
      · by_cases hk : ∃ j ∈ (C.gates[t]).inputs,
            ∀ x, DomZ (insert v Z) x → Rd C n x t j = false
        · left
          obtain ⟨j, hj, hjk⟩ := hk
          intro x hx
          rw [hval, hand]
          simp only [GateOp.eval]
          rw [Bool.eq_false_iff]
          intro hall
          rw [List.all_eq_true] at hall
          have := hall (Rd C n x t j) (List.mem_map_of_mem hj)
          rw [hjk x hx] at this
          exact Bool.false_ne_true this
        · right
          apply hallI
          intro j hj
          rcases hrd j with h | h
          · exact absurd ⟨j, hj, h⟩ hk
          · exact h
      · by_cases hP : NI C n Z t
        · by_cases hk : ∃ j ∈ (C.gates[t]).inputs,
              ∀ x, DomZ (insert v Z) x → Rd C n x t j = false
          · exfalso
            obtain ⟨g', hg', _, hlen', hne⟩ := H t hP
            rw [hg] at hg'
            cases hg'
            obtain ⟨j, hj, hjk⟩ := hk
            obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by omega : (C.gates[t]).inputs.length = 2)
            rw [hab] at hj hne
            have hv2 : ∀ x, Wv C n x (n + t) = (Rd C n x t a || Rd C n x t b) := by
              intro x
              rw [hval, hor, hab]
              simp [GateOp.eval]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
            rcases hj with rfl | rfl
            · obtain ⟨x, hx, hx2⟩ := hne b (by simp)
              apply hx2
              rw [hv2, hjk x hx]
              simp
            · obtain ⟨x, hx, hx2⟩ := hne a (by simp)
              apply hx2
              rw [hv2, hjk x hx]
              simp
          · right
            apply hallI
            intro j hj
            rcases hrd j with h | h
            · exact absurd ⟨j, hj, h⟩ hk
            · exact h
        · have hcase : (C.gates[t]).inputs = [] ∨ ∃ j ∈ (C.gates[t]).inputs,
              ∀ x, DomZ Z x → Wv C n x (n + t) = Rd C n x t j := by
            by_cases hl2 : 2 ≤ (C.gates[t]).inputs.length
            · right
              by_contra hno
              push_neg at hno
              apply hP
              refine ⟨C.gates[t], hg, hor, hl2, fun j hj => ?_⟩
              obtain ⟨x, hx, hne⟩ := hno j hj
              exact ⟨x, hx, hne⟩
            · match hl : (C.gates[t]).inputs with
              | [] => exact Or.inl rfl
              | [a] =>
                right
                refine ⟨a, by simp, fun x _ => ?_⟩
                rw [hval, hor, hl]
                simp [GateOp.eval]
              | a :: b :: l =>
                rw [hl] at hl2
                simp at hl2
          rcases hcase with hnil | ⟨j, hj, hjv⟩
          · right
            apply hallI
            intro j hj
            rw [hnil] at hj
            simp at hj
          · rcases hrd j with h | h
            · left
              intro x hx
              rw [hjv x (hdomZ x hx), h x hx]
            · right
              intro x hx
              rw [hjv x hx, hjv _ (hdomu x hx), h x hx]

theorem key {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (hmono : Monotone2 C)
    (hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (Z : Finset (Fin n)) (v u a b : Fin n) (hv : v ∉ Z) (hu : u ∉ Z) (hvu : G.Adj v u)
    (ha : a ∉ insert v Z) (hb : b ∉ insert v Z) (hab : G.Adj a b) :
    ∃ t, NI C n Z t ∧ ¬ NI C n (insert v Z) t := by
  by_contra hcon
  push_neg at hcon
  have hd := dich C n hmono Z v hcon C.output
  have heval : ∀ x, C.eval (List.ofFn x) = Wv C n x C.output := fun x => rfl
  rcases hd with hk | hi
  · have hx : DomZ (insert v Z) (fun w => decide (w = a ∨ w = b)) := by
      intro z hz
      simp only [decide_eq_false_iff_not, not_or]
      exact ⟨fun h => ha (h ▸ hz), fun h => hb (h ▸ hz)⟩
    have h1 := (hf (fun w => decide (w = a ∨ w = b))).2 ⟨a, b, hab, by simp, by simp⟩
    rw [heval, hk _ hx] at h1
    exact Bool.false_ne_true h1
  · have hx : DomZ Z (fun w => decide (w = u ∨ w = v)) := by
      intro z hz
      simp only [decide_eq_false_iff_not, not_or]
      exact ⟨fun h => hu (h ▸ hz), fun h => hv (h ▸ hz)⟩
    have h1 := (hf (fun w => decide (w = u ∨ w = v))).2 ⟨u, v, hvu.symm, by simp, by simp⟩
    have h2 : C.eval (List.ofFn (Function.update (fun w => decide (w = u ∨ w = v)) v false))
        = true → False := by
      intro h
      obtain ⟨p, q, hpq, hp, hq⟩ := (hf _).1 h
      have hp' : p = u := by
        by_cases hpv : p = v
        · subst hpv; simp at hp
        · rw [Function.update_of_ne hpv] at hp
          simp only [decide_eq_true_eq] at hp
          rcases hp with hp | hp
          · exact hp
          · exact absurd hp hpv
      have hq' : q = u := by
        by_cases hqv : q = v
        · subst hqv; simp at hq
        · rw [Function.update_of_ne hqv] at hq
          simp only [decide_eq_true_eq] at hq
          rcases hq with hq | hq
          · exact hq
          · exact absurd hq hqv
      rw [hp', hq'] at hpq
      exact G.ne_of_adj hpq rfl
    rw [heval, hi _ hx] at h1
    exact h2 (by rw [heval]; exact h1)

end PEqualNP.Outside.L598

theorem PEqualNP.Outside.L_meta_598 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → {v : Fin n | ∃ w : Fin n, G.Adj v w}.ncard ≤ A.card + {K : G.ConnectedComponent | ∃ v w : Fin n, G.connectedComponentMk v = K ∧ G.Adj v w}.ncard + 1 := by
  intro n G C A hmono hf hA
  classical
  have hNlt : ∀ (Z : Finset (Fin n)) (v u a b : Fin n), v ∉ Z → u ∉ Z → G.Adj v u →
      a ∉ insert v Z → b ∉ insert v Z → G.Adj a b →
      (A.filter (fun t => PEqualNP.Outside.L598.NI C n (insert v Z) t)).card <
        (A.filter (fun t => PEqualNP.Outside.L598.NI C n Z t)).card := by
    intro Z v u a b hv hu hvu ha hb hab
    obtain ⟨t, ht1, ht2⟩ := PEqualNP.Outside.L598.key G C hmono hf Z v u a b hv hu hvu ha hb hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨t, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, ht1⟩
        obtain ⟨g, hg, hop, _⟩ := ht1
        exact hA t g hg hop
      · rw [Finset.mem_filter]; exact fun h => ht2 h.2
    · intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, PEqualNP.Outside.L598.NI_mono C n Z v t ht.2⟩
  let root : Fin n → Fin n := fun v => (G.connectedComponentMk v).out
  have hroot : ∀ v, G.connectedComponentMk (root v) = G.connectedComponentMk v :=
    fun v => Quot.out_eq _
  have hroot2 : ∀ v w, G.Adj v w → root w = root v := by
    intro v w h
    show (G.connectedComponentMk w).out = (G.connectedComponentMk v).out
    rw [SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable h).symm]
  let φ : Fin n → ℕ := fun v => G.dist (root v) v
  let V' : Finset (Fin n) := Finset.univ.filter (fun v => ∃ w, G.Adj v w)
  let R : Finset (Fin n) := V'.image root
  have hφ : ∀ v ∈ V', v ∉ R → ∃ w, G.Adj v w ∧ φ w < φ v := by
    intro v hv hvR
    have hne : v ≠ root v := by
      intro h
      apply hvR
      rw [Finset.mem_image]
      exact ⟨v, hv, h.symm⟩
    have hreach : G.Reachable v (root v) :=
      (SimpleGraph.ConnectedComponent.eq.mp (hroot v)).symm
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    obtain ⟨w, h, q, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne p
    refine ⟨w, h, ?_⟩
    show G.dist (root w) w < G.dist (root v) v
    rw [hroot2 v w h, SimpleGraph.dist_comm (u := root v) (v := w),
      SimpleGraph.dist_comm (u := root v) (v := v), ← hp]
    have := SimpleGraph.dist_le q
    simp only [SimpleGraph.Walk.length_cons]
    omega
  have hind : ∀ k (Z : Finset (Fin n)), ((V' \ R) \ Z).card = k →
      (∀ v ∈ V', v ∉ R → v ∉ Z → ∃ w, w ∉ Z ∧ G.Adj v w ∧ φ w < φ v) →
      k ≤ (A.filter (fun t => PEqualNP.Outside.L598.NI C n Z t)).card + 1 := by
    intro k
    induction k with
    | zero => intro Z _ _; omega
    | succ k ih =>
      intro Z hcard hI
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · omega
      · have hSne : ((V' \ R) \ Z).Nonempty := by
          rw [← Finset.card_pos, hcard]; omega
        obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image _ φ hSne
        have hvS' := hvS
        simp only [Finset.mem_sdiff] at hvS'
        obtain ⟨⟨hvV, hvR⟩, hvZ⟩ := hvS'
        obtain ⟨u, huZ, hvu, _⟩ := hI v hvV hvR hvZ
        have hcard' : ((V' \ R) \ insert v Z).card = k := by
          have : (V' \ R) \ insert v Z = ((V' \ R) \ Z).erase v := by
            ext y
            simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
            tauto
          rw [this, Finset.card_erase_of_mem hvS, hcard]
          rfl
        have hI' : ∀ y ∈ V', y ∉ R → y ∉ insert v Z →
            ∃ w, w ∉ insert v Z ∧ G.Adj y w ∧ φ w < φ y := by
          intro y hyV hyR hyZ
          rw [Finset.mem_insert, not_or] at hyZ
          obtain ⟨w, hwZ, hyw, hφw⟩ := hI y hyV hyR hyZ.2
          refine ⟨w, ?_, hyw, hφw⟩
          rw [Finset.mem_insert, not_or]
          refine ⟨?_, hwZ⟩
          intro hwv
          have := hvmax y (by simp only [Finset.mem_sdiff]; exact ⟨⟨hyV, hyR⟩, hyZ.2⟩)
          rw [hwv] at hφw
          omega
        have hS'ne : ((V' \ R) \ insert v Z).Nonempty := by
          rw [← Finset.card_pos, hcard']; omega
        obtain ⟨y, hyS⟩ := hS'ne
        simp only [Finset.mem_sdiff] at hyS
        obtain ⟨⟨hyV, hyR⟩, hyZ⟩ := hyS
        obtain ⟨w, hwZ, hyw, _⟩ := hI' y hyV hyR hyZ
        have hlt := hNlt Z v u y w hvZ huZ hvu hyZ hwZ hyw
        have := ih (insert v Z) hcard' hI'
        omega
  have h1 : (V' \ R).card ≤ A.card + 1 := by
    have := hind (V' \ R).card ∅ (by rw [Finset.sdiff_empty]) (by
      intro v hv hvR _
      obtain ⟨w, hw, hφw⟩ := hφ v hv hvR
      exact ⟨w, by simp, hw, hφw⟩)
    have h2 := Finset.card_filter_le A (fun t => PEqualNP.Outside.L598.NI C n ∅ t)
    omega
  have h2 : R.card ≤ {K : G.ConnectedComponent |
      ∃ v w : Fin n, G.connectedComponentMk v = K ∧ G.Adj v w}.ncard := by
    rw [← Set.ncard_coe_finset R]
    apply Set.ncard_le_ncard_of_injOn G.connectedComponentMk
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_image] at hr
      obtain ⟨v, hv, rfl⟩ := hr
      rw [Finset.mem_filter] at hv
      obtain ⟨w, hw⟩ := hv.2
      exact ⟨v, w, (hroot v).symm, hw⟩
    · intro r1 hr1 r2 hr2 heq
      rw [Finset.mem_coe, Finset.mem_image] at hr1 hr2
      obtain ⟨v1, _, rfl⟩ := hr1
      obtain ⟨v2, _, rfl⟩ := hr2
      rw [hroot, hroot] at heq
      show (G.connectedComponentMk v1).out = (G.connectedComponentMk v2).out
      rw [heq]
  have h3 : {v : Fin n | ∃ w : Fin n, G.Adj v w}.ncard = V'.card := by
    rw [← Set.ncard_coe_finset V']
    congr 1
    ext v
    simp [V']
  have h4 := Finset.card_le_card_sdiff_add_card (s := V') (t := R)
  omega
