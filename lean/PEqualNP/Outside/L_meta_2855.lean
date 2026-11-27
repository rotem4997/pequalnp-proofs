import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2855_aux

-- evaluation toolkit (step, val, val_gate, mono) copied from the L_meta_1406 file
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h

lemma wv {n : ℕ} (C : Circuit) (z : Fin n → Bool) (i : ℕ) :
    (C.wires (List.ofFn z)).getD i false = val C.gates z i := rfl

def ga (G : List Gate) (j : ℕ) : Gate := G.getD j ⟨GateOp.or, []⟩

lemma ga_lt (G : List Gate) (j : ℕ) (hj : j < G.length) : ga G j = G[j] := by
  unfold ga
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma ga_ge (G : List Gate) (j : ℕ) (hj : G.length ≤ j) : ga G j = ⟨GateOp.or, []⟩ := by
  unfold ga
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  rfl

lemma val_ga {n : ℕ} (G : List Gate) (x : Fin n → Bool) (k : ℕ) :
    val G x (n + k) =
      (ga G k).op.eval ((ga G k).inputs.map fun j => if j < n + k then val G x j else false) := by
  by_cases hk : k < G.length
  · rw [ga_lt G k hk]
    exact val_gate G x k hk
  · rw [ga_ge G k (by omega), val_ge G x _ (by omega)]
    rfl

lemma ga_new (G : List Gate) (m : ℕ) (g1 g2 g3 : Gate) (j : ℕ) :
    ga (G.set m g1 ++ [g2, g3]) j =
      if j < G.length then (if j = m then g1 else ga G j)
      else if j = G.length then g2 else if j = G.length + 1 then g3 else ⟨GateOp.or, []⟩ := by
  unfold ga
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : j < G.length
  · rw [if_pos h1, List.getElem?_append_left (by simpa using h1), List.getElem?_set]
    by_cases h2 : j = m
    · subst h2
      simp [h1]
    · rw [if_neg h2, if_neg (Ne.symm h2)]
  · rw [if_neg h1, List.getElem?_append_right (by simpa using h1)]
    simp only [List.length_set]
    by_cases h2 : j = G.length
    · subst h2
      simp
    · rw [if_neg h2]
      by_cases h3 : j = G.length + 1
      · subst h3
        simp
      · rw [if_neg h3]
        obtain ⟨t, rfl⟩ : ∃ t, j = G.length + 2 + t := ⟨j - (G.length + 2), by omega⟩
        have e : G.length + 2 + t - G.length = t + 2 := by omega
        rw [e]
        rfl

lemma op_ao (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) (j : ℕ) :
    (ga C.gates j).op = GateOp.and ∨ (ga C.gates j).op = GateOp.or := by
  by_cases hj : j < C.gates.length
  · rw [ga_lt _ _ hj]
    have h := (hM _ (List.getElem_mem hj)).1
    simpa using h
  · rw [ga_ge _ _ (by omega)]
    exact Or.inr rfl

lemma mem_ao (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
  simpa using h

lemma ev_and2 (f : ℕ → Bool) (a b : ℕ) : GateOp.and.eval ([a, b].map f) = (f a && f b) := by
  simp [GateOp.eval]

lemma ev_or2 (f : ℕ → Bool) (a b : ℕ) : GateOp.or.eval ([a, b].map f) = (f a || f b) := by
  simp [GateOp.eval]

lemma vpt {N : ℕ} (G : List Gate) (z : Fin (N + N) → Bool) (q : Fin N) :
    val G z q.val = z (Fin.castAdd N q) := by
  have h := q.isLt
  exact val_lt G z q.val (by omega)

lemma vln {N : ℕ} (G : List Gate) (z : Fin (N + N) → Bool) (l : Fin N) :
    val G z (N + l.val) = z (Fin.natAdd N l) := by
  have h := l.isLt
  exact val_lt G z (N + l.val) (by omega)

lemma vln2 {N : ℕ} (G : List Gate) (z : Fin (N + N) → Bool) (a : ℕ) (h1 : N ≤ a) (h2 : a < N + N) :
    val G z a = z (Fin.natAdd N ⟨a - N, by omega⟩) := by
  rw [val_lt G z a h2]
  congr 1
  apply Fin.ext
  show a = N + (a - N)
  omega

def T (N : ℕ) (I : Fin N → Fin N → Prop) (z : Fin (N + N) → Bool) : Prop :=
  ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

def CleanV (N : ℕ) (I : Fin N → Fin N → Prop) (G : List Gate) (j : ℕ) : Prop :=
  (∀ z : Fin (N + N) → Bool, val G z (N + N + j) = true →
      val G (fun k : Fin (N + N) => decide (k.val < N) && z k) (N + N + j) = true ∨
      val G (fun k : Fin (N + N) => decide (N ≤ k.val) && z k) (N + N + j) = true ∨ T N I z) ∧
  ((∀ p : Fin N, val G (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)) (N + N + j) = false) ∧
    ∀ l : Fin N, val G (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)) (N + N + j) = false)

def PtS (N : ℕ) (G : List Gate) (u : ℕ) : Prop :=
  u < N ∨ (N + N ≤ u ∧ (ga G (u - (N + N))).op = GateOp.or ∧
    ∃ a b : ℕ, (ga G (u - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)

def LnS (N : ℕ) (G : List Gate) (v : ℕ) : Prop :=
  (N ≤ v ∧ v < N + N) ∨ (N + N ≤ v ∧ (ga G (v - (N + N))).op = GateOp.or ∧
    ∃ a b : ℕ, (ga G (v - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N)

def Small (N : ℕ) (G : List Gate) (j : ℕ) : Prop :=
  ∃ u v : ℕ, (ga G j).inputs = [u, v] ∧
    ((PtS N G u ∧ LnS N G v) ∨ (LnS N G u ∧ PtS N G v))

lemma notT_pt {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) :
    ¬ T N I (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)) := by
  rintro ⟨p', l, _, _, h⟩
  have h1 := p.isLt
  simp [Fin.ext_iff] at h
  omega

lemma notT_ln {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) :
    ¬ T N I (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)) := by
  rintro ⟨p', l', _, h, _⟩
  have h1 := p'.isLt
  simp [Fin.ext_iff] at h
  omega

lemma clean_of_le {N : ℕ} (I : Fin N → Fin N → Prop) (G : List Gate) (j : ℕ)
    (h : ∀ z : Fin (N + N) → Bool, val G z (N + N + j) = true → T N I z) : CleanV N I G j := by
  refine ⟨fun z hz => Or.inr (Or.inr (h z hz)), fun p => ?_, fun l => ?_⟩
  · rw [Bool.eq_false_iff]
    exact fun hh => notT_pt I p (h _ hh)
  · rw [Bool.eq_false_iff]
    exact fun hh => notT_ln I l (h _ hh)

lemma pt_val {N : ℕ} (G : List Gate) (u : ℕ) (h : PtS N G u) :
    ∃ a b : Fin N, ∀ z : Fin (N + N) → Bool,
      val G z u = (z (Fin.castAdd N a) || z (Fin.castAdd N b)) := by
  rcases h with h | ⟨h1, hop, a, b, hin, ha, hb⟩
  · refine ⟨⟨u, h⟩, ⟨u, h⟩, fun z => ?_⟩
    rw [Bool.or_self]
    exact val_lt G z u (by omega)
  · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun z => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, u = N + N + k := ⟨u - (N + N), by omega⟩
    have hk : N + N + k - (N + N) = k := by omega
    rw [hk] at hop hin
    rw [val_ga G z k, hop, hin, ev_or2, if_pos (by omega), if_pos (by omega)]
    rw [val_lt G z a (by omega), val_lt G z b (by omega)]
    rfl

lemma ln_val {N : ℕ} (G : List Gate) (v : ℕ) (h : LnS N G v) :
    ∃ c d : Fin N, ∀ z : Fin (N + N) → Bool,
      val G z v = (z (Fin.natAdd N c) || z (Fin.natAdd N d)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, hop, a, b, hin, ha1, ha2, hb1, hb2⟩
  · refine ⟨⟨v - N, by omega⟩, ⟨v - N, by omega⟩, fun z => ?_⟩
    rw [Bool.or_self]
    exact vln2 G z v h1 h2
  · refine ⟨⟨a - N, by omega⟩, ⟨b - N, by omega⟩, fun z => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, v = N + N + k := ⟨v - (N + N), by omega⟩
    have hk : N + N + k - (N + N) = k := by omega
    rw [hk] at hop hin
    rw [val_ga G z k, hop, hin, ev_or2, if_pos (by omega), if_pos (by omega)]
    rw [vln2 G z a ha1 ha2, vln2 G z b hb1 hb2]

lemma gm_val {N : ℕ} (G : List Gate) (m : ℕ) (hop : (ga G m).op = GateOp.and)
    (hrb : ∀ i ∈ (ga G m).inputs, i < N + N + m) (hs : Small N G m) :
    ∃ (a b c d : Fin N) (vl : ℕ), vl < N + N + m ∧
      (∀ z : Fin (N + N) → Bool, val G z vl = (z (Fin.natAdd N c) || z (Fin.natAdd N d))) ∧
      (∀ z : Fin (N + N) → Bool, val G z (N + N + m) =
        ((z (Fin.castAdd N a) || z (Fin.castAdd N b)) &&
          (z (Fin.natAdd N c) || z (Fin.natAdd N d)))) := by
  obtain ⟨u, v, hin, hcase⟩ := hs
  have hu : u < N + N + m := hrb u (by simp [hin])
  have hv : v < N + N + m := hrb v (by simp [hin])
  have hval : ∀ z : Fin (N + N) → Bool, val G z (N + N + m) = (val G z u && val G z v) := by
    intro z
    rw [val_ga G z m, hop, hin, ev_and2, if_pos hu, if_pos hv]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨a, b, hab⟩ := pt_val G u h1
    obtain ⟨c, d, hcd⟩ := ln_val G v h2
    exact ⟨a, b, c, d, v, hv, hcd, fun z => by rw [hval, hab, hcd]⟩
  · obtain ⟨c, d, hcd⟩ := ln_val G u h1
    obtain ⟨a, b, hab⟩ := pt_val G v h2
    exact ⟨a, b, c, d, u, hu, hcd, fun z => by rw [hval, hab, hcd, Bool.and_comm]⟩

lemma single_val {N : ℕ} (G : List Gate) (z : Fin (N + N) → Bool) (q c : Fin N) :
    GateOp.and.eval ([q.val, N + c.val].map (val G z)) =
      (z (Fin.castAdd N q) && z (Fin.natAdd N c)) := by
  rw [ev_and2, vpt, vln]

lemma star {N : ℕ} (I : Fin N → Fin N → Prop) (G : List Gate) (m : ℕ) (q c d : Fin N) (vl : ℕ)
    (hvl : vl < N + N + m)
    (hv : ∀ z : Fin (N + N) → Bool, val G z vl = (z (Fin.natAdd N c) || z (Fin.natAdd N d))) :
    ∃ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧
      (∀ i ∈ g.inputs, i < N + N + m) ∧
      (∀ z : Fin (N + N) → Bool, g.op.eval (g.inputs.map (val G z)) = true → T N I z) ∧
      (∀ (z : Fin (N + N) → Bool) (l : Fin N), I q l → (l = c ∨ l = d) →
        z (Fin.castAdd N q) = true → z (Fin.natAdd N l) = true →
        g.op.eval (g.inputs.map (val G z)) = true) := by
  classical
  have hq := q.isLt
  have hc' := c.isLt
  have hd' := d.isLt
  by_cases hc : I q c
  · by_cases hd : I q d
    · refine ⟨⟨GateOp.and, [q.val, vl]⟩, Or.inl rfl, by simp, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · intro z hz
        dsimp only at hz
        rw [ev_and2, vpt, hv] at hz
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hz
        rcases hz with ⟨h1, h2 | h2⟩
        · exact ⟨q, c, hc, h1, h2⟩
        · exact ⟨q, d, hd, h1, h2⟩
      · intro z l _ hcd h1 h2
        dsimp only
        rw [ev_and2, vpt, hv, h1]
        rcases hcd with rfl | rfl
        · rw [h2]
          rfl
        · rw [h2]
          simp
    · refine ⟨⟨GateOp.and, [q.val, N + c.val]⟩, Or.inl rfl, by simp, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · intro z hz
        dsimp only at hz
        rw [single_val] at hz
        simp only [Bool.and_eq_true] at hz
        exact ⟨q, c, hc, hz.1, hz.2⟩
      · intro z l hl hcd h1 h2
        dsimp only
        rw [single_val, h1]
        rcases hcd with rfl | rfl
        · rw [h2]
          rfl
        · exact absurd hl hd
  · by_cases hd : I q d
    · refine ⟨⟨GateOp.and, [q.val, N + d.val]⟩, Or.inl rfl, by simp, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · intro z hz
        dsimp only at hz
        rw [single_val] at hz
        simp only [Bool.and_eq_true] at hz
        exact ⟨q, d, hd, hz.1, hz.2⟩
      · intro z l hl hcd h1 h2
        dsimp only
        rw [single_val, h1]
        rcases hcd with rfl | rfl
        · exact absurd hl hc
        · rw [h2]
          rfl
    · refine ⟨⟨GateOp.or, []⟩, Or.inr rfl, by simp, ?_, ?_, ?_⟩
      · intro i hi
        simp at hi
      · intro z hz
        simp [GateOp.eval] at hz
      · intro z l hl hcd _ _
        rcases hcd with rfl | rfl
        · exact absurd hl hc
        · exact absurd hl hd

lemma ev_rel (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f1 f2 : ℕ → Bool) (P : Prop) (h : ∀ i ∈ l, f1 i = true → f2 i = true ∨ P) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true ∨ P := by
  intro h1
  rcases hop with rfl | rfl
  · by_cases hP : P
    · exact Or.inr hP
    · left
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at h1 ⊢
      intro i hi
      rcases h i hi (h1 i hi) with h2 | h2
      · exact h2
      · exact absurd h2 hP
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at h1 ⊢
    obtain ⟨i, hi, h2⟩ := h1
    rcases h i hi h2 with h3 | h3
    · exact Or.inl ⟨i, hi, h3⟩
    · exact Or.inr h3

lemma rel {n : ℕ} (G1 G2 : List Gate) (z : Fin n → Bool) (P : Prop) (k : ℕ)
    (h : ∀ i, i < k → (ga G1 i = ga G2 i ∧ ((ga G1 i).op = GateOp.and ∨ (ga G1 i).op = GateOp.or)) ∨
        (val G1 z (n + i) = true → val G2 z (n + i) = true ∨ P)) :
    ∀ w, w < n + k → val G1 z w = true → val G2 z w = true ∨ P := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases h1 : w < n
    · rw [val_lt G1 z w h1] at hv
      rw [val_lt G2 z w h1]
      exact Or.inl hv
    · obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
      have hi : i < k := by omega
      rcases h i hi with ⟨heq, hop⟩ | hd
      · rw [val_ga G1 z i] at hv
        rw [val_ga G2 z i, ← heq]
        refine ev_rel _ hop _ _ _ P ?_ hv
        intro j _ hj
        by_cases hlt : j < n + i
        · rw [if_pos hlt] at hj ⊢
          exact ih j hlt (by omega) hj
        · rw [if_neg hlt] at hj
          exact absurd hj Bool.false_ne_true
      · exact hd hv

lemma card_lt (P' P : ℕ → Prop) (L' L m : ℕ) (hm : m < L ∧ P m)
    (h : ∀ j, j < L' ∧ P' j → (j < L ∧ P j) ∧ j ≠ m) :
    Nat.card {j : ℕ // j < L' ∧ P' j} < Nat.card {j : ℕ // j < L ∧ P j} := by
  have e1 : Nat.card {j : ℕ // j < L' ∧ P' j} = Set.ncard {j : ℕ | j < L' ∧ P' j} :=
    Nat.card_coe_set_eq {j : ℕ | j < L' ∧ P' j}
  have e2 : Nat.card {j : ℕ // j < L ∧ P j} = Set.ncard {j : ℕ | j < L ∧ P j} :=
    Nat.card_coe_set_eq {j : ℕ | j < L ∧ P j}
  rw [e1, e2]
  apply Set.ncard_lt_ncard
  · rw [Set.ssubset_def]
    exact ⟨fun j hj => (h j hj).1, fun hsub => (h m (hsub hm)).2 rfl⟩
  · exact (Set.finite_lt_nat L).subset (fun j hj => hj.1)

lemma pts_tr {N : ℕ} (G G' : List Gate)
    (hk : ∀ k a b, (ga G k).op = GateOp.or → (ga G k).inputs = [a, b] → ga G' k = ga G k)
    (u : ℕ) (h : PtS N G u) : PtS N G' u := by
  rcases h with h | ⟨h1, hop, a, b, hin, ha, hb⟩
  · exact Or.inl h
  · have e := hk _ a b hop hin
    exact Or.inr ⟨h1, by rw [e]; exact hop, a, b, by rw [e]; exact hin, ha, hb⟩

lemma lns_tr {N : ℕ} (G G' : List Gate)
    (hk : ∀ k a b, (ga G k).op = GateOp.or → (ga G k).inputs = [a, b] → ga G' k = ga G k)
    (v : ℕ) (h : LnS N G v) : LnS N G' v := by
  rcases h with h | ⟨h1, hop, a, b, hin, hab⟩
  · exact Or.inl h
  · have e := hk _ a b hop hin
    exact Or.inr ⟨h1, by rw [e]; exact hop, a, b, by rw [e]; exact hin, hab⟩

lemma small_tr {N : ℕ} (G G' : List Gate)
    (hk : ∀ k a b, (ga G k).op = GateOp.or → (ga G k).inputs = [a, b] → ga G' k = ga G k)
    (j : ℕ) (hj : ga G' j = ga G j) (h : Small N G j) : Small N G' j := by
  obtain ⟨u, v, hin, hcase⟩ := h
  refine ⟨u, v, by rw [hj]; exact hin, ?_⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨pts_tr G G' hk u h1, lns_tr G G' hk v h2⟩
  · exact Or.inr ⟨lns_tr G G' hk u h1, pts_tr G G' hk v h2⟩

theorem main (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (m : ℕ)
    (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    (hf : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ T N I z)
    (hall : ∀ j < C.gates.length, (ga C.gates j).op = GateOp.and →
      CleanV N I C.gates j ∨ Small N C.gates j)
    (hm : m < C.gates.length)
    (hmu : (ga C.gates m).op = GateOp.and ∧ ¬ CleanV N I C.gates m) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C' ∧ C'.size ≤ C.size + 2 ∧
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C' z = true ↔ T N I z) ∧
      (∀ j < C'.gates.length, (ga C'.gates j).op = GateOp.and →
        CleanV N I C'.gates j ∨ Small N C'.gates j) ∧
      Nat.card {j : ℕ // j < C'.gates.length ∧
        ((ga C'.gates j).op = GateOp.and ∧ ¬ CleanV N I C'.gates j)} <
      Nat.card {j : ℕ // j < C.gates.length ∧
        ((ga C.gates j).op = GateOp.and ∧ ¬ CleanV N I C.gates j)} := by
  by_cases ho : C.output < N + N + C.gates.length
  swap
  · refine ⟨⟨[], C.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      cases hg
    · intro j hj
      exact absurd hj (Nat.not_lt_zero _)
    · exact Nat.zero_le _
    · intro z
      rw [← hf z]
      show val [] z C.output = true ↔ val C.gates z C.output = true
      have e0 : ([] : List Gate).length = 0 := rfl
      rw [val_ge [] z _ (by omega), val_ge C.gates z _ (by omega)]
    · intro j hj
      exact absurd hj (Nat.not_lt_zero _)
    · exact card_lt (fun j => (ga ([] : List Gate) j).op = GateOp.and ∧ ¬ CleanV N I [] j)
        (fun j => (ga C.gates j).op = GateOp.and ∧ ¬ CleanV N I C.gates j) 0 C.gates.length m
        ⟨hm, hmu⟩ (fun j hj => absurd hj.1 (Nat.not_lt_zero _))
  have hsm : Small N C.gates m := (hall m hm hmu.1).resolve_left hmu.2
  obtain ⟨a, b, c, d, vl, hvl, hv, hgm⟩ := gm_val C.gates m hmu.1 (hR m hm) hsm
  obtain ⟨g1, hop1, hlen1, hin1, hT1, hcov1⟩ := star I C.gates m a c d vl hvl hv
  obtain ⟨g2, hop2, hlen2, hin2, hT2, hcov2⟩ := star I C.gates m b c d vl hvl hv
  obtain ⟨G', hG'⟩ : ∃ G' : List Gate, G' = C.gates.set m g1 ++
      [g2, ⟨GateOp.or, [C.output, N + N + C.gates.length]⟩] := ⟨_, rfl⟩
  have hlen : G'.length = C.gates.length + 2 := by
    rw [hG']
    simp
  have hga : ∀ j, ga G' j = if j < C.gates.length then (if j = m then g1 else ga C.gates j)
      else if j = C.gates.length then g2 else if j = C.gates.length + 1 then
        ⟨GateOp.or, [C.output, N + N + C.gates.length]⟩ else ⟨GateOp.or, []⟩ := by
    intro j
    rw [hG']
    exact ga_new _ _ _ _ _ _
  have hga1 : ∀ j, j < C.gates.length → j ≠ m → ga G' j = ga C.gates j := by
    intro j h1 h2
    rw [hga, if_pos h1, if_neg h2]
  have hgam : ga G' m = g1 := by
    rw [hga, if_pos hm, if_pos rfl]
  have hgaL : ga G' C.gates.length = g2 := by
    rw [hga, if_neg (lt_irrefl _), if_pos rfl]
  have hgaL1 : ga G' (C.gates.length + 1) =
      ⟨GateOp.or, [C.output, N + N + C.gates.length]⟩ := by
    rw [hga, if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hpre : ∀ (z : Fin (N + N) → Bool) (w : ℕ), w < N + N + m →
      val G' z w = val C.gates z w := by
    intro z w hw
    rw [Bool.eq_iff_iff]
    constructor
    · intro h
      exact (rel G' C.gates z False m (fun i hi => Or.inl ⟨hga1 i (by omega) (by omega),
        by rw [hga1 i (by omega) (by omega)]; exact op_ao C hM i⟩) w hw h).resolve_right id
    · intro h
      exact (rel C.gates G' z False m (fun i hi => Or.inl ⟨(hga1 i (by omega) (by omega)).symm,
        op_ao C hM i⟩) w hw h).resolve_right id
  have hE : ∀ (g : Gate) (k : ℕ), m ≤ k → (∀ i ∈ g.inputs, i < N + N + m) → ga G' k = g →
      ∀ z : Fin (N + N) → Bool,
        val G' z (N + N + k) = g.op.eval (g.inputs.map (val C.gates z)) := by
    intro g k hk hin hg z
    rw [val_ga G' z k, hg]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hjm := hin j hj
    rw [if_pos (by omega), hpre z j hjm]
  have hE1 := hE g1 m le_rfl hin1 hgam
  have hE2 := hE g2 C.gates.length (le_of_lt hm) hin2 hgaL
  have hE3 : ∀ z : Fin (N + N) → Bool, val G' z (N + N + (C.gates.length + 1)) =
      (val G' z C.output || g2.op.eval (g2.inputs.map (val C.gates z))) := by
    intro z
    rw [val_ga G' z (C.gates.length + 1), hgaL1]
    dsimp only
    rw [ev_or2, if_pos (by omega), if_pos (by omega), hE2 z]
  have hU : ∀ (z : Fin (N + N) → Bool) (w : ℕ), w < N + N + C.gates.length →
      val G' z w = true → val C.gates z w = true ∨ T N I z := by
    intro z
    apply rel G' C.gates z (T N I z) C.gates.length
    intro i hi
    by_cases him : i = m
    · right
      rw [him]
      intro h
      rw [hE1 z] at h
      exact Or.inr (hT1 z h)
    · left
      exact ⟨hga1 i hi him, by rw [hga1 i hi him]; exact op_ao C hM i⟩
  have hLo : ∀ (z : Fin (N + N) → Bool),
      (val C.gates z (N + N + m) = true → g1.op.eval (g1.inputs.map (val C.gates z)) = true) →
      ∀ w : ℕ, w < N + N + C.gates.length → val C.gates z w = true → val G' z w = true := by
    intro z hz w hw h
    refine (rel C.gates G' z False C.gates.length ?_ w hw h).resolve_right id
    intro i hi
    by_cases him : i = m
    · right
      rw [him]
      intro h'
      left
      rw [hE1 z]
      exact hz h'
    · left
      exact ⟨(hga1 i hi him).symm, op_ao C hM i⟩
  have hgmP : ∀ z : Fin (N + N) → Bool,
      val C.gates (fun k : Fin (N + N) => decide (k.val < N) && z k) (N + N + m) = false := by
    intro z
    rw [hgm]
    simp
  have hgmL : ∀ z : Fin (N + N) → Bool,
      val C.gates (fun k : Fin (N + N) => decide (N ≤ k.val) && z k) (N + N + m) = false := by
    intro z
    rw [hgm]
    simp [Nat.not_le.mpr a.isLt, Nat.not_le.mpr b.isLt]
  have htr : ∀ j : ℕ, j < C.gates.length → CleanV N I C.gates j → CleanV N I G' j := by
    intro j hj hc
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases hU z _ (by omega) hz with h | h
      · rcases hc.1 z h with h1 | h1 | h1
        · exact Or.inl (hLo _ (fun h' => by rw [hgmP z] at h'; exact absurd h' Bool.false_ne_true)
            _ (by omega) h1)
        · exact Or.inr (Or.inl (hLo _
            (fun h' => by rw [hgmL z] at h'; exact absurd h' Bool.false_ne_true) _ (by omega) h1))
        · exact Or.inr (Or.inr h1)
      · exact Or.inr (Or.inr h)
    · intro p
      rw [Bool.eq_false_iff]
      intro h
      rcases hU _ _ (by omega) h with h1 | h1
      · rw [hc.2.1 p] at h1
        exact absurd h1 Bool.false_ne_true
      · exact notT_pt I p h1
    · intro l
      rw [Bool.eq_false_iff]
      intro h
      rcases hU _ _ (by omega) h with h1 | h1
      · rw [hc.2.2 l] at h1
        exact absurd h1 Bool.false_ne_true
      · exact notT_ln I l h1
  have hkey : ∀ j : ℕ, j < G'.length → (ga G' j).op = GateOp.and →
      CleanV N I G' j ∨ (j < C.gates.length ∧ j ≠ m ∧ ga G' j = ga C.gates j) := by
    intro j hj hop
    rw [hlen] at hj
    by_cases h1 : j < C.gates.length
    · by_cases h2 : j = m
      · left
        rw [h2]
        exact clean_of_le I G' m (fun z hz => hT1 z (by rw [← hE1 z]; exact hz))
      · right
        exact ⟨h1, h2, hga1 j h1 h2⟩
    · by_cases h2 : j = C.gates.length
      · left
        rw [h2]
        exact clean_of_le I G' _ (fun z hz => hT2 z (by rw [← hE2 z]; exact hz))
      · have h3 : j = C.gates.length + 1 := by omega
        rw [h3, hgaL1] at hop
        exact absurd hop (by simp)
  have hkeep : ∀ k a b, (ga C.gates k).op = GateOp.or → (ga C.gates k).inputs = [a, b] →
      ga G' k = ga C.gates k := by
    intro k a' b' hop hin
    by_cases h1 : k < C.gates.length
    · by_cases h2 : k = m
      · rw [h2, hmu.1] at hop
        exact absurd hop (by simp)
      · exact hga1 k h1 h2
    · rw [ga_ge _ _ (by omega)] at hin
      exact absurd hin (by simp)
  have hao : ∀ g ∈ G', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rw [hG'] at hg
    rcases List.mem_append.1 hg with h | h
    · rcases List.mem_or_eq_of_mem_set h with h | h
      · have h' := hM g h
        exact ⟨by simpa using h'.1, h'.2⟩
      · rw [h]
        exact ⟨hop1, hlen1⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with h | h
      · rw [h]
        exact ⟨hop2, hlen2⟩
      · rw [h]
        exact ⟨Or.inr rfl, by simp⟩
  refine ⟨⟨G', N + N + (C.gates.length + 1)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have h := hao g hg
    exact ⟨mem_ao g h.1, h.2⟩
  · intro j hj i hi
    have hj' : j < G'.length := hj
    have hi' : i ∈ (ga G' j).inputs := hi
    rw [hlen] at hj'
    rw [hga] at hi'
    by_cases h1 : j < C.gates.length
    · rw [if_pos h1] at hi'
      by_cases h2 : j = m
      · rw [if_pos h2] at hi'
        have h3 := hin1 i hi'
        omega
      · rw [if_neg h2] at hi'
        exact hR j h1 i hi'
    · rw [if_neg h1] at hi'
      by_cases h2 : j = C.gates.length
      · rw [if_pos h2] at hi'
        have h3 := hin2 i hi'
        omega
      · rw [if_neg h2, if_pos (by omega)] at hi'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi'
        rcases hi' with rfl | rfl <;> omega
  · show G'.length ≤ C.gates.length + 2
    omega
  · intro z
    show val G' z (N + N + (C.gates.length + 1)) = true ↔ T N I z
    constructor
    · intro h
      rw [hE3 z, Bool.or_eq_true] at h
      rcases h with h | h
      · rcases hU z _ ho h with h1 | h1
        · exact (hf z).1 h1
        · exact h1
      · exact hT2 z h
    · rintro ⟨p, l, hI, hp, hl⟩
      obtain ⟨e, he⟩ : ∃ e : Fin (N + N) → Bool,
          e = fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) := ⟨_, rfl⟩
      have hep : ∀ q : Fin N, e (Fin.castAdd N q) = true ↔ q = p := by
        intro q
        have h1 := q.isLt
        have h2 := p.isLt
        rw [he]
        simp [Fin.ext_iff]
        omega
      have hel : ∀ q : Fin N, e (Fin.natAdd N q) = true ↔ q = l := by
        intro q
        have h1 := q.isLt
        have h2 := p.isLt
        rw [he]
        simp [Fin.ext_iff]
        omega
      have hle : ∀ k, e k = true → z k = true := by
        intro k hk
        rw [he] at hk
        simp only [decide_eq_true_eq] at hk
        rcases hk with rfl | rfl
        · exact hp
        · exact hl
      apply mono G' hao e z hle
      rw [hE3 e, Bool.or_eq_true]
      have hCe : val C.gates e C.output = true :=
        (hf e).2 ⟨p, l, hI, (hep p).2 rfl, (hel l).2 rfl⟩
      by_cases hc : val C.gates e (N + N + m) = true →
          g1.op.eval (g1.inputs.map (val C.gates e)) = true
      · exact Or.inl (hLo e hc _ ho hCe)
      · right
        rw [Classical.not_imp] at hc
        obtain ⟨h1, h2⟩ := hc
        rw [hgm e] at h1
        simp only [Bool.and_eq_true, Bool.or_eq_true, hep, hel] at h1
        obtain ⟨hab, hcd⟩ := h1
        have hcd' : l = c ∨ l = d := by
          rcases hcd with h | h
          · exact Or.inl h.symm
          · exact Or.inr h.symm
        rcases hab with h | h
        · exact absurd (hcov1 e l (by rw [h]; exact hI) hcd' ((hep a).2 h) ((hel l).2 rfl)) h2
        · exact hcov2 e l (by rw [h]; exact hI) hcd' ((hep b).2 h) ((hel l).2 rfl)
  · intro j hj hop
    rcases hkey j hj hop with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · rcases hall j h1 (by rw [← h3]; exact hop) with h | h
      · exact Or.inl (htr j h1 h)
      · exact Or.inr (small_tr C.gates G' hkeep j h3 h)
  · refine card_lt (fun j => (ga G' j).op = GateOp.and ∧ ¬ CleanV N I G' j)
      (fun j => (ga C.gates j).op = GateOp.and ∧ ¬ CleanV N I C.gates j) G'.length
      C.gates.length m ⟨hm, hmu⟩ ?_
    rintro j ⟨hj, hop, hnc⟩
    rcases hkey j hj hop with h | ⟨h1, h2, h3⟩
    · exact absurd h hnc
    · exact ⟨⟨h1, by rw [← h3]; exact hop, fun hc => hnc (htr j h1 hc)⟩, h2⟩

end PEqualNP.Outside.L_meta_2855_aux

theorem PEqualNP.Outside.L_meta_2855 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka0 : Fin (N + N) => decide (ka0.val < N) && z ka0))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb1 : Fin (N + N) => decide (N ≤ kb1.val) && z kb1))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C.wires (List.ofFn (fun kc2 : Fin (N + N) => decide (kc2 = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd3 : Fin (N + N) => decide (kd3 = Fin.natAdd N l)))).getD (N + N + j) false = false)) ∨ (∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [u, v] ∧ (((u < N ∨ (N + N ≤ u ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)) ∧ ((N ≤ v ∧ v < N + N) ∨ (N + N ≤ v ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N))) ∨ (((N ≤ u ∧ u < N + N) ∨ (N + N ≤ u ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N)) ∧ (v < N ∨ (N + N ≤ v ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)))))) → m < C.gates.length → ((PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + m) false = true → (C.wires (List.ofFn (fun ka4 : Fin (N + N) => decide (ka4.val < N) && z ka4))).getD (N + N + m) false = true ∨ (C.wires (List.ofFn (fun kb5 : Fin (N + N) => decide (N ≤ kb5.val) && z kb5))).getD (N + N + m) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C.wires (List.ofFn (fun kc6 : Fin (N + N) => decide (kc6 = Fin.castAdd N p)))).getD (N + N + m) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd7 : Fin (N + N) => decide (kd7 = Fin.natAdd N l)))).getD (N + N + m) false = false))) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C' ∧ C'.size ≤ C.size + 2 ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C' z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < C'.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∀ z : Fin (N + N) → Bool, (C'.wires (List.ofFn z)).getD (N + N + j) false = true → (C'.wires (List.ofFn (fun ka8 : Fin (N + N) => decide (ka8.val < N) && z ka8))).getD (N + N + j) false = true ∨ (C'.wires (List.ofFn (fun kb9 : Fin (N + N) => decide (N ≤ kb9.val) && z kb9))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C'.wires (List.ofFn (fun kc10 : Fin (N + N) => decide (kc10 = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C'.wires (List.ofFn (fun kd11 : Fin (N + N) => decide (kd11 = Fin.natAdd N l)))).getD (N + N + j) false = false)) ∨ (∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).inputs = [u, v] ∧ (((u < N ∨ (N + N ≤ u ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (u - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C' (u - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)) ∧ ((N ≤ v ∧ v < N + N) ∨ (N + N ≤ v ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (v - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C' (v - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N))) ∨ (((N ≤ u ∧ u < N + N) ∨ (N + N ≤ u ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (u - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C' (u - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N)) ∧ (v < N ∨ (N + N ≤ v ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' (v - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C' (v - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)))))) ∧ Nat.card {j : ℕ // j < C'.gates.length ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∀ z : Fin (N + N) → Bool, (C'.wires (List.ofFn z)).getD (N + N + j) false = true → (C'.wires (List.ofFn (fun ka12 : Fin (N + N) => decide (ka12.val < N) && z ka12))).getD (N + N + j) false = true ∨ (C'.wires (List.ofFn (fun kb13 : Fin (N + N) => decide (N ≤ kb13.val) && z kb13))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C'.wires (List.ofFn (fun kc14 : Fin (N + N) => decide (kc14 = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C'.wires (List.ofFn (fun kd15 : Fin (N + N) => decide (kd15 = Fin.natAdd N l)))).getD (N + N + j) false = false)))} < Nat.card {j : ℕ // j < C.gates.length ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka16 : Fin (N + N) => decide (ka16.val < N) && z ka16))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb17 : Fin (N + N) => decide (N ≤ kb17.val) && z kb17))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C.wires (List.ofFn (fun kc18 : Fin (N + N) => decide (kc18 = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd19 : Fin (N + N) => decide (kd19 = Fin.natAdd N l)))).getD (N + N + j) false = false)))} := by
  intro N I _ C m _ hM hR hf hall hm hmu
  exact PEqualNP.Outside.L_meta_2855_aux.main N I C m hM hR hf hall hm hmu
