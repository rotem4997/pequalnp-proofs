import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1762

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


lemma ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
    (if c then b else false) = true ↔ c ∧ b = true := by
  by_cases h : c <;> simp [h]

lemma W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h w hw
    exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
  · rintro h b ⟨w, hw, rfl⟩
    exact (ite_true_iff _ _).mpr (h w hw)

lemma W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hi
    obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
    rcases h with h | h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have hg := hM (C.gates[k]) (List.getElem_mem hk)
  rw [← gateAt_eq C k hk] at hg
  have h1 := hg.1
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, hg.2⟩

def Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P t.val →
    (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

lemma reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

lemma reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
    (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
  fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

lemma reach_inv (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (h : Reach n C t w) :
    w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  have h2 := h (fun w => Reach n C t w ∧ (w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      (gateAt C k).op = GateOp.or ∧ ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a))
    ⟨reach_refl n C t, Or.inl rfl⟩
    (fun k hk hop a ha hlt ih => ⟨reach_step n C t k hk hop a ha hlt ih.1,
      Or.inr ⟨k, hk, rfl, hop, a, ha, hlt, ih.1⟩⟩)
  exact h2.2

lemma reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
    (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
  h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
    (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

open PEqualNP.EdgeOwnership in
lemma descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → W n C x (n + k) = true →
      (gateAt C k).op = GateOp.and ∨
      (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
      (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hx
    rcases (gate_mono2 C hM k hk).1 with hop | hop
    · exact Or.inl hop
    · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
      by_cases hwn : w < n
      · right; right
        refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · rw [← W_input n C x w hwn]; exact hwx
        · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have he : n + k' - n = k' := by omega
        rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
        · right; left
          exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
            h, hwx⟩
        · right; left
          exact ⟨i, (inCone_iff n C i k hk).mpr
            ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
        · right; right
          exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

open PEqualNP.EdgeOwnership in
lemma owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
    ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
  obtain ⟨_, _, hval, hno⟩ := ho
  intro w hw
  have hval' : W n C (pairInput p q) (n + j) = true := hval
  obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
  refine ⟨hlt, ?_⟩
  by_cases hwn : w < n
  · rw [W_input n C _ w hwn] at hwx
    have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
    rcases h' with h | h
    · left
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
    · right
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
  · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
    have he : n + k' - n = k' := by omega
    have hk'j : k' < j := by omega
    have hc : InCone n C k' j :=
      (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
    rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
    · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
      rw [hwx] at hf
      exact absurd hf (by simp)
    · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
        ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
      have hij := inCone_lt n C j hj i hc2
      have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
      rw [hix] at hf
      exact absurd hf (by simp)
    · have h' : t = p ∨ t = q := of_decide_eq_true ht
      rcases h' with h | h
      · left; rw [← h]; exact hdom
      · right; rw [← h]; exact hdom

noncomputable def R (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun t => Reach n C t w)

lemma mem_R (n : ℕ) (C : Circuit) (w : ℕ) (t : Fin n) : t ∈ R n C w ↔ Reach n C t w := by
  unfold R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma R_card_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) : (R n C w).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
  have h1 : w = a.val := by
    rcases reach_inv n C a w ((mem_R n C w a).mp ha) with h | ⟨k, _, h, _⟩
    · exact h
    · omega
  have h2 : w = b.val := by
    rcases reach_inv n C b w ((mem_R n C w b).mp hb) with h | ⟨k, _, h, _⟩
    · exact h
    · omega
  exact Fin.ext (h1.symm.trans h2)

lemma R_gate (n : ℕ) (C : Circuit) (k : ℕ) (t : Fin n) (ht : t ∈ R n C (n + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  rcases reach_inv n C t (n + k) ((mem_R n C (n + k) t).mp ht) with h | ⟨k', hk', h, hop, hex⟩
  · have := t.isLt
    omega
  · have hkk : k = k' := by omega
    rw [hkk]
    exact ⟨hk', hop, hex⟩

noncomputable def cw (n : ℕ) (C : Circuit) (j : ℕ) : ℕ :=
  if (R n C ((gateAt C j).inputs.getD 0 0)).card ≤ 1 then (gateAt C j).inputs.getD 0 0
  else (gateAt C j).inputs.getD 1 0

noncomputable def lw (n : ℕ) (C : Circuit) (j : ℕ) : ℕ :=
  if (R n C ((gateAt C j).inputs.getD 0 0)).card ≤ 1 then (gateAt C j).inputs.getD 1 0
  else (gateAt C j).inputs.getD 0 0

lemma cw_pos (n : ℕ) (C : Circuit) (j a b : ℕ) (hin : (gateAt C j).inputs = [a, b])
    (h : (R n C a).card ≤ 1) : cw n C j = a ∧ lw n C j = b := by
  unfold cw lw
  rw [hin]
  simp [h]

lemma cw_neg (n : ℕ) (C : Circuit) (j a b : ℕ) (hin : (gateAt C j).inputs = [a, b])
    (h : ¬ (R n C a).card ≤ 1) : cw n C j = b ∧ lw n C j = a := by
  unfold cw lw
  rw [hin]
  simp [h]

open PEqualNP.EdgeOwnership in
lemma star (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hclean : ∀ p q : Fin n, gateVal n C j (pairInput p q) = true → G.Adj p q)
    (u v : Fin n) (ho : Owns n C j u v) :
    lw n C j < n + j ∧ ∃ c : Fin n, R n C (cw n C j) = {c} ∧
      (∀ t ∈ R n C (lw n C j), G.Adj c t) ∧
      ((u = c ∧ v ∈ R n C (lw n C j)) ∨ (v = c ∧ u ∈ R n C (lw n C j))) := by
  have F1 := owns_reach n C hM j hj hop
  have F3 : ∀ s t : Fin n,
      (∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C s w ∨ Reach n C t w)) → G.Adj s t := by
    intro s t h
    have hs : pairInput s t s = true := by simp [pairInput]
    have ht : pairInput s t t = true := by simp [pairInput]
    have hv : W n C (pairInput s t) (n + j) = true :=
      (W_and_iff n C _ j hj hop).mpr (fun w hw => ⟨(h w hw).1,
        (h w hw).2.elim (fun d => reach_val n C s w _ hs d) (fun d => reach_val n C t w _ ht d)⟩)
    exact hclean s t hv
  have hlen := (gate_mono2 C hM j hj).2
  have hF0 := F1 u v ho
  rcases hin : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · have hadj := F3 u u (by rw [hin]; intro w hw; simp at hw)
    exact absurd rfl hadj.ne
  · have h1 := hF0 a (by rw [hin]; simp)
    rcases h1.2 with d | d
    · have hadj := F3 u u (by
        rw [hin]; intro w hw
        have hwa : w = a := by simpa using hw
        rw [hwa]; exact ⟨h1.1, Or.inl d⟩)
      exact absurd rfl hadj.ne
    · have hadj := F3 v v (by
        rw [hin]; intro w hw
        have hwa : w = a := by simpa using hw
        rw [hwa]; exact ⟨h1.1, Or.inl d⟩)
      exact absurd rfl hadj.ne
  · have hlta : a < n + j := (hF0 a (by rw [hin]; simp)).1
    have hltb : b < n + j := (hF0 b (by rw [hin]; simp)).1
    have hbip : ∀ s t, Reach n C s a → Reach n C t b → G.Adj s t := by
      intro s t da db
      refine F3 s t ?_
      rw [hin]; intro w hw
      have hwab : w = a ∨ w = b := by simpa using hw
      rcases hwab with hwa | hwb
      · rw [hwa]; exact ⟨hlta, Or.inl da⟩
      · rw [hwb]; exact ⟨hltb, Or.inr db⟩
    have hloop : ∀ t, Reach n C t a → Reach n C t b → False :=
      fun t da db => absurd rfl (hbip t t da db).ne
    have hA : (Reach n C u a ∧ Reach n C v b) ∨ (Reach n C v a ∧ Reach n C u b) := by
      have h1 := hF0 a (by rw [hin]; simp)
      have h2 := hF0 b (by rw [hin]; simp)
      rcases h1.2 with pa | qa <;> rcases h2.2 with pb | qb
      · exact (hloop u pa pb).elim
      · exact Or.inl ⟨pa, qb⟩
      · exact Or.inr ⟨qa, pb⟩
      · exact (hloop v qa qb).elim
    by_cases hc : (R n C a).card ≤ 1
    · obtain ⟨e1, e2⟩ := cw_pos n C j a b hin hc
      rw [e1, e2]
      refine ⟨hltb, ?_⟩
      have huniq : ∀ s s', Reach n C s a → Reach n C s' a → s = s' := fun s s' hs hs' =>
        Finset.card_le_one.mp hc s ((mem_R n C a s).mpr hs) s' ((mem_R n C a s').mpr hs')
      obtain ⟨s0, hs0⟩ : ∃ s0, Reach n C s0 a := by
        rcases hA with h | h
        · exact ⟨u, h.1⟩
        · exact ⟨v, h.1⟩
      refine ⟨s0, ?_, fun t ht => hbip s0 t hs0 ((mem_R n C b t).mp ht), ?_⟩
      · exact Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_R n C a s0).mpr hs0,
          fun x hx => huniq x s0 ((mem_R n C a x).mp hx) hs0⟩
      · rcases hA with h | h
        · exact Or.inl ⟨huniq u s0 h.1 hs0, (mem_R n C b v).mpr h.2⟩
        · exact Or.inr ⟨huniq v s0 h.1 hs0, (mem_R n C b u).mpr h.2⟩
    · obtain ⟨e1, e2⟩ := cw_neg n C j a b hin hc
      rw [e1, e2]
      refine ⟨hlta, ?_⟩
      obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp (not_le.mp hc)
      have ha1' := (mem_R n C a a1).mp ha1
      have ha2' := (mem_R n C a a2).mp ha2
      have huniq : ∀ t t', Reach n C t b → Reach n C t' b → t = t' := by
        intro t t' ht ht'
        by_contra hne'
        exact h4 a1 t a2 t' hne hne' ⟨hbip a1 t ha1' ht, (hbip a2 t ha2' ht).symm,
          hbip a2 t' ha2' ht', (hbip a1 t' ha1' ht').symm⟩
      obtain ⟨s0, hs0⟩ : ∃ s0, Reach n C s0 b := by
        rcases hA with h | h
        · exact ⟨v, h.2⟩
        · exact ⟨u, h.2⟩
      refine ⟨s0, ?_, fun t ht => (hbip t s0 ((mem_R n C a t).mp ht) hs0).symm, ?_⟩
      · exact Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_R n C b s0).mpr hs0,
          fun x hx => huniq x s0 ((mem_R n C b x).mp hx) hs0⟩
      · rcases hA with h | h
        · exact Or.inr ⟨huniq v s0 h.2 hs0, (mem_R n C a u).mpr h.1⟩
        · exact Or.inl ⟨huniq u s0 h.2 hs0, (mem_R n C a v).mpr h.1⟩
  · have hl : (a :: b :: c :: r).length ≤ 2 := hin ▸ hlen
    simp only [List.length_cons] at hl
    omega

noncomputable def F (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (c : Fin n) (w : ℕ) :
    Finset (Fin n) := by
  classical exact (R n C w).filter (fun _ => ∀ t ∈ R n C w, G.Adj c t)

lemma mem_F (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (c : Fin n) (w : ℕ) (x : Fin n) :
    x ∈ F n G C c w ↔ x ∈ R n C w ∧ ∀ t ∈ R n C w, G.Adj c t := by
  unfold F
  simp only [Finset.mem_filter]

lemma F_sub (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (c : Fin n) (w : ℕ) :
    F n G C c w ⊆ R n C w := fun x hx => ((mem_F n G C c w x).mp hx).1

lemma F_split (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (hM : Monotone2 C) (c : Fin n)
    (m : ℕ) (h2 : 2 ≤ (F n G C c m).card) :
    ∃ ch : Finset ℕ, ch.card ≤ 2 ∧ (∀ a ∈ ch, a < m) ∧ F n G C c m ⊆ ch.biUnion (F n G C c) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
  have hadj : ∀ t ∈ R n C m, G.Adj c t := ((mem_F n G C c m x).mp hx).2
  by_cases hmn : m < n
  · exact absurd (Finset.card_le_one.mp (R_card_input n C m hmn) x (F_sub n G C c m hx) y
      (F_sub n G C c m hy)) hxy
  · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    obtain ⟨hk, hop, _⟩ := R_gate n C k x (F_sub n G C c (n + k) hx)
    refine ⟨((gateAt C k).inputs.filter (fun a => decide (a < n + k))).toFinset, ?_, ?_, ?_⟩
    · exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans
        (gate_mono2 C hM k hk).2)
    · intro a ha
      rw [List.mem_toFinset, List.mem_filter] at ha
      exact of_decide_eq_true ha.2
    · intro t ht
      obtain ⟨_, _, a, ha, hlt, hr⟩ := R_gate n C k t (F_sub n G C c (n + k) ht)
      refine Finset.mem_biUnion.mpr ⟨a, ?_, ?_⟩
      · rw [List.mem_toFinset, List.mem_filter]
        exact ⟨ha, decide_eq_true hlt⟩
      · refine (mem_F n G C c a t).mpr ⟨(mem_R n C a t).mpr hr, fun s hs => ?_⟩
        exact hadj s ((mem_R n C (n + k) s).mpr
          (reach_step n C s k hk hop a ha hlt ((mem_R n C a s).mp hs)))

lemma count_abs {α : Type} [DecidableEq α] (f : ℕ → Finset α)
    (h : ∀ m, 2 ≤ (f m).card →
      ∃ ch : Finset ℕ, ch.card ≤ 2 ∧ (∀ a ∈ ch, a < m) ∧ f m ⊆ ch.biUnion f) :
    ∀ (m : ℕ) (W : Finset ℕ), (∀ w ∈ W, w < m) →
      (W.biUnion f).card ≤ W.card + ((Finset.range m).filter (fun w => 2 ≤ (f w).card)).card := by
  intro m
  induction m with
  | zero =>
    intro W hW
    have hW0 : W = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    rw [hW0]
    simp
  | succ m ih =>
    intro W hW
    have hmono : ((Finset.range m).filter (fun w => 2 ≤ (f w).card)).card ≤
        ((Finset.range (m + 1)).filter (fun w => 2 ≤ (f w).card)).card := by
      refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
      intro w hw
      rw [Finset.mem_range] at hw ⊢
      omega
    by_cases hm : m ∈ W
    · have hWpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hm⟩
      have hcardE : (W.erase m).card = W.card - 1 := Finset.card_erase_of_mem hm
      by_cases hb : 2 ≤ (f m).card
      · obtain ⟨ch, hch2, hchlt, hsub⟩ := h m hb
        have hW' : ∀ w ∈ W.erase m ∪ ch, w < m := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · have h1 := hW w (Finset.mem_of_mem_erase hw)
            have h2 := Finset.ne_of_mem_erase hw
            omega
          · exact hchlt w hw
        have h1 := ih (W.erase m ∪ ch) hW'
        have h3 : W.biUnion f ⊆ (W.erase m ∪ ch).biUnion f := by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
          by_cases hwm : w = m
          · rw [hwm] at hxw
            obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp (hsub hxw)
            exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _ ha, hxa⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), hxw⟩
        have h4 := Finset.card_le_card h3
        have h5 : (W.erase m ∪ ch).card ≤ (W.erase m).card + ch.card := Finset.card_union_le _ _
        have h6 : ((Finset.range (m + 1)).filter (fun w => 2 ≤ (f w).card)).card =
            ((Finset.range m).filter (fun w => 2 ≤ (f w).card)).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert]
          simp only [hb, ↓reduceIte]
          rw [Finset.card_insert_of_notMem]
          simp
        omega
      · have hW' : ∀ w ∈ W.erase m, w < m := by
          intro w hw
          have h1 := hW w (Finset.mem_of_mem_erase hw)
          have h2 := Finset.ne_of_mem_erase hw
          omega
        have h1 := ih (W.erase m) hW'
        have h3 : W.biUnion f ⊆ (W.erase m).biUnion f ∪ f m := by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
          by_cases hwm : w = m
          · rw [hwm] at hxw
            exact Finset.mem_union_right _ hxw
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_erase.mpr ⟨hwm, hw⟩, hxw⟩)
        have h4 := Finset.card_le_card h3
        have h5 : ((W.erase m).biUnion f ∪ f m).card ≤ ((W.erase m).biUnion f).card + (f m).card :=
          Finset.card_union_le _ _
        omega
    · have hW' : ∀ w ∈ W, w < m := by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ m := fun e => hm (e ▸ hw)
        omega
      have h1 := ih W hW'
      omega

open PEqualNP.EdgeOwnership in
theorem key (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hM : Monotone2 C) (T : Finset (Sym2 (Fin n)))
    (hT : ∀ e ∈ T, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j : Fin C.gates.length,
      Owns n C (↑j) u v ∧
        ∀ p q : Fin n, gateVal n C (↑j) (pairInput p q) = true → G.Adj p q) :
    T.card ≤ C.gates.length := by
  classical
  let J : Fin n → Finset ℕ := fun c => (Finset.range C.gates.length).filter
    (fun j => (gateAt C j).op = GateOp.and ∧ R n C (cw n C j) = {c})
  let Wc : Fin n → Finset ℕ := fun c =>
    ((J c).image (lw n C)).filter (fun w => w < n + C.gates.length)
  let Bc : Fin n → Finset ℕ := fun c =>
    (Finset.range (n + C.gates.length)).filter (fun w => 2 ≤ (F n G C c w).card)
  let Jall : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => (gateAt C j).op = GateOp.and)
  let Big : Finset ℕ := (Finset.range C.gates.length).filter
    (fun k => 2 ≤ (R n C (n + k)).card)
  have step1 : T ⊆ Finset.univ.biUnion
      (fun c => ((Wc c).biUnion (F n G C c)).image (fun l => s(c, l))) := by
    intro e he
    obtain ⟨u, v, rfl, j, ho, hcl⟩ := hT e he
    obtain ⟨hlt, c, hRc, hadj, hcase⟩ := star n G h4 C hM j j.isLt ho.2.1 hcl u v ho
    have hmemW : lw n C j ∈ Wc c := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, ?_, rfl⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, ho.2.1, hRc⟩
      · have := j.isLt
        omega
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, ?_⟩
    rcases hcase with ⟨huc, hv⟩ | ⟨hvc, hu⟩
    · refine Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨lw n C j, hmemW,
        (mem_F n G C c _ v).mpr ⟨hv, hadj⟩⟩, ?_⟩
      rw [huc]
    · refine Finset.mem_image.mpr ⟨u, Finset.mem_biUnion.mpr ⟨lw n C j, hmemW,
        (mem_F n G C c _ u).mpr ⟨hu, hadj⟩⟩, ?_⟩
      rw [hvc]
      exact Sym2.eq_swap
  have step2 : T.card ≤ ∑ c : Fin n, ((Wc c).card + (Bc c).card) := by
    refine (Finset.card_le_card step1).trans (Finset.card_biUnion_le.trans ?_)
    refine Finset.sum_le_sum (fun c _ => Finset.card_image_le.trans ?_)
    exact count_abs (F n G C c) (fun m hm => F_split n G C hM c m hm) (n + C.gates.length) (Wc c)
      (fun w hw => (Finset.mem_filter.mp hw).2)
  have step3 : ∑ c : Fin n, (Wc c).card ≤ Jall.card := by
    have h1 : ∑ c : Fin n, (Wc c).card ≤ ∑ c : Fin n, (J c).card :=
      Finset.sum_le_sum (fun c _ => (Finset.card_filter_le _ _).trans Finset.card_image_le)
    have h2 : (Finset.univ.biUnion J).card = ∑ c : Fin n, (J c).card := by
      refine Finset.card_biUnion (fun c _ c' _ hne => ?_)
      show Disjoint (J c) (J c')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := (Finset.mem_filter.mp hj).2.2
      have e2 := (Finset.mem_filter.mp hj').2.2
      exact hne (Finset.singleton_injective (e1.symm.trans e2))
    have h3 : Finset.univ.biUnion J ⊆ Jall := by
      intro j hj
      obtain ⟨c, _, hjc⟩ := Finset.mem_biUnion.mp hj
      have hjc' := Finset.mem_filter.mp hjc
      exact Finset.mem_filter.mpr ⟨hjc'.1, hjc'.2.1⟩
    have h5 := Finset.card_le_card h3
    omega
  have step4 : ∑ c : Fin n, (Bc c).card ≤ Big.card := by
    have h2 : (Finset.univ.biUnion Bc).card = ∑ c : Fin n, (Bc c).card := by
      refine Finset.card_biUnion (fun c _ c' _ hne => ?_)
      show Disjoint (Bc c) (Bc c')
      rw [Finset.disjoint_left]
      intro w hw hw'
      have e1 := (Finset.mem_filter.mp hw).2
      have e2 := (Finset.mem_filter.mp hw').2
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp e1
      obtain ⟨z, hz, _⟩ := Finset.one_lt_card.mp e2
      have hx' := (mem_F n G C c w x).mp hx
      have hy' := (mem_F n G C c w y).mp hy
      have hz' := (mem_F n G C c' w z).mp hz
      exact h4 c x c' y hne hxy ⟨hx'.2 x hx'.1, (hz'.2 x hx'.1).symm, hz'.2 y hy'.1,
        (hx'.2 y hy'.1).symm⟩
    have h3 : Finset.univ.biUnion Bc ⊆ Big.image (fun k => n + k) := by
      intro w hw
      obtain ⟨c, _, hwc⟩ := Finset.mem_biUnion.mp hw
      have e1 := (Finset.mem_filter.mp hwc).2
      have e2 : 2 ≤ (R n C w).card := e1.trans (Finset.card_le_card (F_sub n G C c w))
      have hnw : ¬ w < n := fun hlt => by
        have := R_card_input n C w hlt
        omega
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨x, hx, _⟩ := Finset.one_lt_card.mp e2
      obtain ⟨hk, _, _⟩ := R_gate n C k x hx
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, e2⟩, rfl⟩
    have h5 := (Finset.card_le_card h3).trans Finset.card_image_le
    omega
  have step5 : Jall.card + Big.card ≤ C.gates.length := by
    have hd : Disjoint Jall Big := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := (Finset.mem_filter.mp hj).2
      have e2 := (Finset.mem_filter.mp hj').2
      obtain ⟨x, hx, _⟩ := Finset.one_lt_card.mp e2
      obtain ⟨_, hor, _⟩ := R_gate n C j x hx
      rw [e1] at hor
      cases hor
    have h1 : (Jall ∪ Big).card = Jall.card + Big.card := Finset.card_union_of_disjoint hd
    have h2 : Jall ∪ Big ⊆ Finset.range C.gates.length :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h3 := Finset.card_le_card h2
    rw [Finset.card_range] at h3
    omega
  have hsum : ∑ c : Fin n, ((Wc c).card + (Bc c).card) =
      ∑ c : Fin n, (Wc c).card + ∑ c : Fin n, (Bc c).card := Finset.sum_add_distrib
  omega

end PEqualNP.Outside.L_meta_1762

theorem PEqualNP.Outside.L_meta_1762 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  refine ⟨1, fun n G _ _ hg C hM _ => ?_⟩
  have h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    let W : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have hW : W.IsCycle := by
      refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
      simp only [W, SimpleGraph.Walk.tail_cons]
      simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, hac.symm, hbd]
    have h5 := hg a W hW
    have h4 : W.length = 4 := rfl
    omega
  refine le_trans (PEqualNP.Outside.L_meta_1762.key n G h4 C hM _
    (fun e he => (Finset.mem_filter.mp he).2)) ?_
  have hs : C.size = C.gates.length := rfl
  omega
