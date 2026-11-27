import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3777

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

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

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

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega


lemma W_gate' (n : ℕ) (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => W n C x i) := by
  rw [W_gate n C x k hk]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp [hR k hk i hi]

lemma erase_ok (n : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C) (k i : ℕ)
    (hk : k < C.gates.length) (hi : i < n + k)
    (h : (∀ x : Fin n → Bool, W n C x i = W n C x (n + k)) ∨
      ((∀ k', k < k' → k' < C.gates.length → n + k ∉ (gateAt C k').inputs) ∧
        C.output ≠ n + k)) :
    Monotone2 (eraseC n C k i) ∧ ReadsBack n (eraseC n C k i) ∧
      (eraseC n C k i).gates.length + 1 = C.gates.length ∧
      ∀ x : Fin n → Bool, (eraseC n C k i).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hlen := erase_length n C k i hk
  refine ⟨?_, ?_, hlen, ?_⟩
  · intro g hg
    simp only [eraseC, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hM g (List.mem_of_mem_take hg)
    · have := hM g' (List.mem_of_mem_drop hg')
      simpa [aliasGate] using this
  · intro t ht u hu
    by_cases htk : t < k
    · rw [erase_gateAt_lt n C k i t hk htk] at hu
      have := hR t (by omega) u hu
      omega
    · rw [erase_gateAt_ge n C k i t hk (by omega) (by omega)] at hu
      simp only [aliasGate, List.mem_map] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      have := hR (t + 1) (by omega) v hv
      exact alias_lt (n + k) i v (n + t) (by omega) hi (by omega)
  · intro x
    have hh : W n C x i = W n C x (n + k) ∨
        ∀ k', k < k' → k' < C.gates.length → n + k ∉ (gateAt C k').inputs := by
      rcases h with h | h
      · exact Or.inl (h x)
      · exact Or.inr h.1
    have := erase_wires n C k i hk hi x hh C.output (by
      intro ho
      rcases h with h | h
      · exact h x
      · exact absurd ho h.2)
    exact this

lemma gate_cases (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have := hM (gateAt C k) (by rw [gateAt_eq C k hk]; exact List.getElem_mem hk)
  simpa using this

lemma reader_copy {X : Type} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (a : ℕ) (ha : a ∈ l) (f : X → ℕ → Bool) (c : Bool)
    (hc : ∀ x, f x a = c) :
    ∃ i ∈ l, ∀ x, op.eval (l.map (f x)) = f x i := by
  match l, hl, ha with
  | [p], _, ha =>
    refine ⟨p, by simp, fun x => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [p, q], _, ha =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rcases hop with rfl | rfl <;> cases c
      · exact ⟨a, by simp, fun x => by simp [GateOp.eval, hc x]⟩
      · exact ⟨q, by simp, fun x => by simp [GateOp.eval, hc x]⟩
      · exact ⟨q, by simp, fun x => by simp [GateOp.eval, hc x]⟩
      · exact ⟨a, by simp, fun x => by simp [GateOp.eval, hc x]⟩
    · rcases hop with rfl | rfl <;> cases c
      · exact ⟨a, by simp, fun x => by simp [GateOp.eval, hc x]⟩
      · exact ⟨p, by simp, fun x => by simp [GateOp.eval, hc x]⟩
      · exact ⟨p, by simp, fun x => by simp [GateOp.eval, hc x]⟩
      · exact ⟨a, by simp, fun x => by simp [GateOp.eval, hc x]⟩

lemma reduce (n : ℕ) (hn : 0 < n) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hnc : ∀ c : Bool, ¬ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c)
    (j : ℕ) (hj : j < C.gates.length)
    (hdeg : (gateAt C j).inputs.length < 2 ∨
      (gateAt C j).inputs.getD 0 0 = (gateAt C j).inputs.getD 1 0) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.gates.length < C.gates.length ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have fin : ∀ k i, k < C.gates.length → i < n + k →
      ((∀ x : Fin n → Bool, W n C x i = W n C x (n + k)) ∨
        ((∀ k', k < k' → k' < C.gates.length → n + k ∉ (gateAt C k').inputs) ∧
          C.output ≠ n + k)) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.gates.length < C.gates.length ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro k i hk hi h
    obtain ⟨h1, h2, h3, h4⟩ := erase_ok n C hM hR k i hk hi h
    exact ⟨eraseC n C k i, h1, h2, by omega, h4⟩
  obtain ⟨hop, hl⟩ := gate_cases C hM j hj
  have hWj := W_gate' n C hR
  have hRj := hR j hj
  generalize hg : gateAt C j = g at hop hl hdeg hRj
  obtain ⟨op, l⟩ := g
  simp only at hop hl hdeg hRj
  match l, hl, hdeg, hRj with
  | [], _, _, _ =>
    have hc : ∀ x, W n C x (n + j) = op.eval [] := by
      intro x; rw [hWj x j hj, hg]; rfl
    by_cases hread : ∃ k', j < k' ∧ k' < C.gates.length ∧ n + j ∈ (gateAt C k').inputs
    · obtain ⟨k', hjk, hk', hin⟩ := hread
      obtain ⟨hop', hl'⟩ := gate_cases C hM k' hk'
      obtain ⟨i, hi, hv⟩ := reader_copy (gateAt C k').op hop' (gateAt C k').inputs hl' (n + j)
        hin (fun x u => W n C x u) (op.eval []) hc
      refine fin k' i hk' (hR k' hk' i hi) (Or.inl fun x => ?_)
      rw [hWj x k' hk']
      exact (hv x).symm
    · by_cases hout : C.output = n + j
      · exfalso
        apply hnc (op.eval [])
        intro x
        have := hc x
        simp only [W] at this
        rw [← hout] at this
        exact this
      · refine fin j 0 hj (by omega) (Or.inr ⟨fun k' h1 h2 h3 => hread ⟨k', h1, h2, h3⟩, hout⟩)
  | [a], _, _, hRj =>
    refine fin j a hj (hRj a (by simp)) (Or.inl fun x => ?_)
    rw [hWj x j hj, hg]
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _, hdeg, hRj =>
    simp at hdeg
    subst hdeg
    refine fin j a hj (hRj a (by simp)) (Or.inl fun x => ?_)
    rw [hWj x j hj, hg]
    rcases hop with rfl | rfl <;> simp [GateOp.eval]


lemma ofFn_of_length (n : ℕ) (y : List Bool) (h : y.length = n) :
    ∃ x : Fin n → Bool, y = List.ofFn x := by
  subst h
  exact ⟨y.get, (List.ofFn_get y).symm⟩

lemma quad_ok : ∀ (x5 : Fin 13),
    ({x6 ∈ ({0, 1, 2, 5} : Finset (Fin 13)) | x6 - x5 ∈
      ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2 := by
  decide

end PEqualNP.Outside.L_meta_3777

theorem PEqualNP.Outside.L_meta_3777 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → x4.size < (64 : ℕ) → (∃ x7 ∈ x4.gates, x7.inputs.length < (2 : ℕ) ∨ x7.inputs.getD (0 : ℕ) (0 : ℕ) = x7.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x3 x8 ∧ x8.size < x4.size := by
  intro x1 x2 x3 C hC _ hdeg
  obtain ⟨hM, hR, hS⟩ := hC
  obtain ⟨g, hg, hd⟩ := hdeg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  have hlen : ∀ b y, x2 b y → y.length = 26 := by
    intro b y hy
    cases b
    · obtain ⟨S, _, _, rfl⟩ := hy
      simp
    · obtain ⟨a, b, _, rfl⟩ := hy
      simp
  have hT : x2 true ((List.ofFn fun (x6 : Fin 13) => decide (x6 = 1)) ++
      List.ofFn fun (x6 : Fin 13) => decide (x6 = 0)) := by
    show ∃ (x4 : Fin 13) (x5 : Fin 13), x4 - x5 ∈ x1 ∧ _
    exact ⟨1, 0, by decide, rfl⟩
  have hF : x2 false ((List.ofFn fun (x5 : Fin 13) => decide (x5 ∈ ({0, 1, 2, 5} : Finset (Fin 13)))) ++
      List.ofFn fun (x5 : Fin 13) => decide (∀ x6 ∈ ({0, 1, 2, 5} : Finset (Fin 13)), x6 - x5 ∉ x1)) := by
    show ∃ (x4 : Finset (Fin 13)), x4.card = 4 ∧ (∀ (x5 : Fin 13), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ 2) ∧ _
    exact ⟨{0, 1, 2, 5}, by decide, L_meta_3777.quad_ok, rfl⟩
  have hnc : ∀ c : Bool, ¬ ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = c := by
    intro c hc
    obtain ⟨xT, hxT⟩ := L_meta_3777.ofFn_of_length 26 _ (hlen _ _ hT)
    obtain ⟨xF, hxF⟩ := L_meta_3777.ofFn_of_length 26 _ (hlen _ _ hF)
    have e1 := hS _ _ hT
    have e2 := hS _ _ hF
    rw [hxT, hc] at e1
    rw [hxF, hc] at e2
    rw [e1] at e2
    exact Bool.noConfusion e2
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
    L_meta_3777.gateAt_eq C j hj
  obtain ⟨D, hDM, hDR, hDs, hDe⟩ := L_meta_3777.reduce 26 (by norm_num) C hM hR hnc j hj (by rw [hga]; exact hd)
  refine ⟨D, ⟨hDM, hDR, ?_⟩, hDs⟩
  intro b y hy
  obtain ⟨x, rfl⟩ := L_meta_3777.ofFn_of_length 26 y (hlen _ _ hy)
  rw [hDe x]
  exact hS b _ hy
