import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7249

-- The circuit evaluation and wire-deletion lemmas adapt the existing one-junk argument.
namespace M1528
namespace P1
namespace S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership
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
lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]
lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
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
def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length
def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true
lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega
lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)
lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk
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
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩
lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩
lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩
lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl
end S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩
end P1
namespace P2
open P1.S98 (W W_gate W_input W_or W_and AO gateAt_eq split_gates inCone_c1 inCone_c2 inCone_iff)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
lemma fin2_sub : ∀ b : Fin 2, (b = 0 ∧ 1 - b = 1) ∨ (b = 1 ∧ 1 - b = 0) := by decide
lemma fin2_ne : ∀ b c : Fin 2, c ≠ b → c = 1 - b := by decide
lemma fin2_both (p : Fin 2 → Prop) (b : Fin 2) (h1 : p b) (h2 : p (1 - b)) : p 0 ∧ p 1 := by
  rcases fin2_sub b with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h1, h2⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h2, h1⟩
def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)
def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and
lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega
lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega
lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]
lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih
lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
lemma orR_leaf (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ u, u < n + C.gates.length → ∃ v, OrR n C u v ∧ Leaf n C v := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩⟩
      · obtain ⟨v, hv1, hv2⟩ := ih a ha (by omega)
        exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2⟩
open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin
lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩
lemma opnd_lt (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) : ∀ b : Fin 2, o b < n + a := by
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  rw [hin] at hab
  simp only [List.cons.injEq, and_true] at hab
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
lemma top_true (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (x : Fin n → Bool)
    (h : ∀ b : Fin 2, W n C x (o b) = true) : W n C x (n + a) = true := by
  have hlt := opnd_lt n C hA a ha o hin
  rw [W_and n C x a ha hop (o 0) (o 1) hin (hlt 0) (hlt 1), h 0, h 1]
  rfl
open PEqualNP.EdgeOwnership in
lemma sem_adj (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (u v : Fin n)
    (hu : OrR n C (o 0) u.val) (hv : OrR n C (o 1) v.val) :
    W n C (pairInput u v) (n + a) = true := by
  apply top_true n C hA a ha hop o hin
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · refine orR_mono n C hA _ _ _ hu ?_
    rw [W_input n C _ u.val u.isLt]; simp [pairInput]
  · refine orR_mono n C hA _ _ _ hv ?_
    rw [W_input n C _ v.val v.isLt]; simp [pairInput]
open PEqualNP.EdgeOwnership in
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk
lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h
lemma orReaches_orR (n : ℕ) (C : Circuit) :
    ∀ w, w < n + C.gates.length → ∀ g, OrReaches n C w g → OrR n C w (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (orReaches_iff n C g k hk).mp hr with h | ⟨hop, c, hc, hcn, hclt, hcr⟩
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ (ih c hclt (by omega) g hcr)
lemma orR_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (hg : g < C.gates.length) :
    ∀ w, w < n + C.gates.length → OrR n C w (n + g) → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨k, hk1, hk, hop, hc⟩, hcr⟩
    · rw [h]
      exact (orReaches_iff n C g g hg).mpr (Or.inl rfl)
    · subst hk1
      have hle := orR_le n C hA _ _ hcr
      have hclt : c < n + k := by
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      exact (orReaches_iff n C g k hk).mpr
        (Or.inr ⟨hop, c, hc, by omega, hclt, ih c hclt (by omega) hcr⟩)
lemma mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (u : Fin n) : u ∈ orIn n C w ↔ OrR n C w u.val := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hu⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (orReaches_orR n C w hw k hr) ⟨k, rfl, hk, hop, hu⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, ⟨k, rfl, hk, hop, hu⟩⟩
    · left
      exact h1
    · right
      exact ⟨k, hk, orR_orReaches n C hA k hk w hw hc, hop, hu⟩
lemma opnd_eq (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) :
    (gateAt C a).inputs = [opnd C a 0, opnd C a 1] := by
  obtain ⟨_, p, q, hpq, _, _⟩ := hA a ha
  simp [opnd, hpq]
lemma nfc (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : NoFourCycle G) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
  have h0 := h a c hac
  have h5 : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w).card :=
    Finset.one_lt_card.mpr ⟨b, by simp [h1, h2.symm], d, by simp [h4.symm, h3], hbd⟩
  omega
end P2
end M1528
namespace M1529
theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  intro n G _ hG P Q W hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw hwP
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwQ
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro q hq
      rcases h w hwP q hq with h1 | h1 | h1
      · exact h1
      · exact absurd h1 G.irrefl
      · exact h1.symm
  · intro w hw hwQ
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwP
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro p hp
      rcases h p hp w hwQ with h1 | h1 | h1
      · exact h1.symm
      · exact h1.symm
      · exact absurd h1 G.irrefl
  · intro s hs w hw
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW w).1 hw s hsP s hsQ with h1 | h1 | h1
    · exact absurd h1 G.irrefl
    · exact h1
    · exact h1
  · intro s hs hsW
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW s).1 hsW s hsP s hsQ with h1 | h1 | h1 <;> exact G.irrefl h1
  · intro h2
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.1 h2
    have key : ∀ u ∈ P ∩ Q, ∀ w ∈ W, G.Adj u w := by
      intro u hu w hw
      have huP := (Finset.mem_inter.1 hu).1
      have huQ := (Finset.mem_inter.1 hu).2
      rcases (hW w).1 hw u huP u huQ with h1 | h1 | h1
      · exact absurd h1 G.irrefl
      · exact h1
      · exact h1
    refine le_trans (Finset.card_le_card ?_) (hG s t hst)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨key s hs w hw, key t ht w hw⟩
end M1529
theorem thm_1529 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) :=
  PEqualNP.Outside.L_meta_7249.M1529.main_aux

namespace M1530
theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) :
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  have kP : ∀ w ∈ W, w ∈ P → ∀ q ∈ Q, G.Adj w q := by
    intro w hw hwP q hq
    rcases (hW w).1 hw w hwP q hq with h | h | h
    · exact h
    · exact absurd h (G.loopless.irrefl w)
    · exact h.symm
  have kQ : ∀ w ∈ W, w ∈ Q → ∀ p ∈ P, G.Adj w p := by
    intro w hw hwQ p hp
    rcases (hW w).1 hw p hp w hwQ with h | h | h
    · exact h.symm
    · exact h.symm
    · exact absurd h (G.loopless.irrefl w)
  have h3 : ∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w := by
    intro s hs w hw
    obtain ⟨hsP, hsQ⟩ := Finset.mem_inter.1 hs
    rcases (hW w).1 hw s hsP s hsQ with h | h | h
    · exact absurd h (G.loopless.irrefl s)
    · exact h
    · exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h2
    obtain ⟨q, hq, q', hq', hqq⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' q q' hne hqq (kP w hw.1 hw.2 q hq) (kP w' hw'.1 hw'.2 q hq)
      (kP w hw.1 hw.2 q' hq') (kP w' hw'.1 hw'.2 q' hq')
  · intro h2
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' p p' hne hpp (kQ w hw.1 hw.2 p hp) (kQ w' hw'.1 hw'.2 p hp)
      (kQ w hw.1 hw.2 p' hp') (kQ w' hw'.1 hw'.2 p' hp')
  · intro a b _ hP hQ haW
    have nPQ : a ∈ P → a ∉ Q := fun haP haQ => G.loopless.irrefl a (kP a haW haP a haQ)
    refine ⟨fun haP => ?_, fun haQ => ?_, fun haP haQ => ?_⟩
    · rcases hQ with h | h
      · exact absurd h (nPQ haP)
      · exact h
    · rcases hP with h | h
      · exact absurd haQ (nPQ h)
      · exact h
    · rcases hP with h | h
      · exact absurd h haP
      · rcases hQ with h' | h'
        · exact absurd h' haQ
        · exact Finset.mem_inter.2 ⟨h, h'⟩
  · intro s hs u hus
    have hsm : s ∈ P ∩ Q := by rw [hs]; simp
    apply Finset.card_le_one.2
    intro w hw w' hw'
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    by_contra hne
    exact hno s u w w' (Ne.symm hus) hne (h3 s hsm w hw.2) hw.1 (h3 s hsm w' hw'.2) hw'.1
end M1530
theorem thm_1530 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  intro n G _ hnf P Q W hW
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  exact PEqualNP.Outside.L_meta_7249.M1530.core n G hno P Q W hW

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Close
open M1528.P1.S98 (W AO Least Bel aliasWire aliasGate eraseC erase_length erase_AO
  erase_wires erase_W_lt erase_gateAt_lt erase_gateAt_ge W_gate W_input W_or W_and
  gateAt_eq AO_of_IsAO2 IsAO2_of_AO prefix_W)
open M1528.P2 (OrStep OrR Leaf orStep_lt orR_le orStep_mono orR_mono orR_leaf_true orR_leaf
  orR_cone pairInput_true graphFun_pair orReaches_orR orR_orReaches mem_orIn opnd_eq nfc)
def OrStepOut (n : ℕ) (C : Circuit) (B : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ k ∉ B ∧
    v ∈ (gateAt C k).inputs
def OrROut (n : ℕ) (C : Circuit) (B : Finset ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (OrStepOut n C B)
lemma orROut_to_orR {n : ℕ} {C : Circuit} {B : Finset ℕ} {u v : ℕ}
    (h : OrROut n C B u v) : OrR n C u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih =>
    obtain ⟨k, rfl, hk, hop, _, hin⟩ := h2
    exact Relation.ReflTransGen.tail ih ⟨k, rfl, hk, hop, hin⟩
lemma orStepOut_lt {n : ℕ} {C : Circuit} (hA : AO n C) {B : Finset ℕ} {u v : ℕ}
    (h : OrStepOut n C B u v) : v < u := by
  obtain ⟨k, rfl, hk, hop, _, hin⟩ := h
  exact orStep_lt n C hA (n + k) v ⟨k, rfl, hk, hop, hin⟩
lemma orROut_le {n : ℕ} {C : Circuit} (hA : AO n C) {B : Finset ℕ} {u v : ℕ}
    (h : OrROut n C B u v) : v ≤ u :=
  orR_le n C hA u v (orROut_to_orR h)
open Classical in
theorem or_dag_leaf_bound {n : ℕ} (C : Circuit) (hA : AO n C)
    (T : Finset (Fin n)) (B : Finset ℕ)
    (hB : ∀ h ∈ B, ((orIn n C (n + h)) ∩ T).card ≤ 1)
    (R : Finset ℕ)
    (hR_lt : ∀ w ∈ R, w < n + C.gates.length)
    (hnoAnd : ∀ w ∈ R, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) :
    let F := (Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ w ∈ R, OrR n C w (n + h)
    ((R.biUnion fun w => orIn n C w) ∩ T).card ≤ R.card + F.card := by
  classical
  intro F
  let Fout : Finset ℕ → Finset ℕ := fun R0 =>
    (Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ w ∈ R0, OrROut n C B w (n + h)
  have hFout_sub : Fout R ⊆ F := by
    intro h hh
    simp only [Fout, F, Finset.mem_filter] at hh ⊢
    obtain ⟨hrng, hop, hnotB, w, hwR, hr⟩ := hh
    exact ⟨hrng, hop, hnotB, w, hwR, orROut_to_orR hr⟩
  suffices hmain : ∀ m : ℕ, ∀ R0 : Finset ℕ,
      (∀ w ∈ R0, w < n + C.gates.length) →
      (∀ w ∈ R0, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) →
      (Fout R0).card = m →
      ((R0.biUnion fun w => orIn n C w) ∩ T).card ≤ R0.card + m by
    exact (hmain (Fout R).card R hR_lt hnoAnd rfl).trans
      (Nat.add_le_add_left (Finset.card_le_card hFout_sub) R.card)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro R0 hR0_lt hR0_noAnd hm
    by_cases hFempty : Fout R0 = ∅
    · have hm0 : m = 0 := by rw [← hm, hFempty, Finset.card_empty]
      rw [hm0, add_zero]
      calc ((R0.biUnion fun w => orIn n C w) ∩ T).card
          = (R0.biUnion fun w => (orIn n C w) ∩ T).card := by
              congr 1
              ext u
              simp only [Finset.mem_inter, Finset.mem_biUnion]
              constructor
              · rintro ⟨⟨w,hw,hu⟩,ht⟩
                exact ⟨w,hw,hu,ht⟩
              · rintro ⟨w,hw,hu,ht⟩
                exact ⟨⟨w,hw,hu⟩,ht⟩
        _ ≤ ∑ w ∈ R0, ((orIn n C w) ∩ T).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ R0, 1 := by
              refine Finset.sum_le_sum fun w hw => ?_
              by_cases hwn : w < n
              · have hsub : (orIn n C w) ∩ T ⊆ {⟨w, hwn⟩} := by
                  intro u hu
                  have hu1 := (mem_orIn n C hA w (hR0_lt w hw) u).mp (Finset.mem_inter.mp hu).1
                  rcases Relation.ReflTransGen.cases_head hu1 with heq | ⟨c, ⟨k, hk, _⟩, _⟩
                  · exact Finset.mem_singleton.mpr (Fin.ext heq.symm)
                  · omega
                exact (Finset.card_le_card hsub).trans (by simp)
              · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
                have hk : k < C.gates.length := by have := hR0_lt (n + k) hw; omega
                rcases (hA k hk).1 with hop | hop
                · exact absurd Relation.ReflTransGen.refl (hR0_noAnd (n + k) hw k hk hop)
                · have hkB : k ∈ B := by
                    by_contra hkNotB
                    have : k ∈ Fout R0 := Finset.mem_filter.mpr
                      ⟨Finset.mem_range.mpr hk, hop, hkNotB, n + k, hw, Relation.ReflTransGen.refl⟩
                    rw [hFempty] at this
                    exact Finset.notMem_empty _ this
                  exact hB k hkB
        _ = R0.card := by simp
    · have hFne : (Fout R0).Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
      let h := (Fout R0).max' hFne
      have hhF : h ∈ Fout R0 := Finset.max'_mem (Fout R0) hFne
      have hh_lt : h < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hhF).1
      have hh_op : (gateAt C h).op = GateOp.or := (Finset.mem_filter.mp hhF).2.1
      have hh_notB : h ∉ B := (Finset.mem_filter.mp hhF).2.2.1
      obtain ⟨w0, hw0R, hw0_reach⟩ := (Finset.mem_filter.mp hhF).2.2.2
      have hreach_eq : ∀ w ∈ R0, OrROut n C B w (n + h) → w = n + h := by
        intro w hw hr
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hstep, hrest⟩
        · exact heq
        · obtain ⟨k, rfl, hk, hkop, hkB, hkin⟩ := hstep
          have hlt1 := orStepOut_lt hA ⟨k, rfl, hk, hkop, hkB, hkin⟩
          have hle2 := orROut_le hA hrest
          have hkF : k ∈ Fout R0 := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, hkop, hkB, n + k, hw, Relation.ReflTransGen.refl⟩
          have hk_le : k ≤ h := Finset.le_max' (Fout R0) k hkF
          omega
      have hhR : n + h ∈ R0 := by
        have := hreach_eq w0 hw0R hw0_reach
        rwa [← this]
      obtain ⟨_, a, b, hab, ha_lt, hb_lt⟩ := hA h hh_lt
      let R' := (R0.erase (n + h)) ∪ {a, b}
      have hstep_a : OrStep n C (n + h) a := ⟨h, rfl, hh_lt, hh_op, by rw [hab]; simp⟩
      have hstep_b : OrStep n C (n + h) b := ⟨h, rfl, hh_lt, hh_op, by rw [hab]; simp⟩
      have hstepOut_a : OrStepOut n C B (n + h) a :=
        ⟨h, rfl, hh_lt, hh_op, hh_notB, by rw [hab]; simp⟩
      have hstepOut_b : OrStepOut n C B (n + h) b :=
        ⟨h, rfl, hh_lt, hh_op, hh_notB, by rw [hab]; simp⟩
      have hR'_lt : ∀ w ∈ R', w < n + C.gates.length := by
        intro w hw
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨_, hwR⟩ | rfl | rfl
        · exact hR0_lt w hwR
        · omega
        · omega
      have hR'_noAnd : ∀ w ∈ R', ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
          ¬ OrR n C w (n + k) := by
        intro w hw k hk hop hr
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨_, hwR⟩ | rfl | rfl
        · exact hR0_noAnd w hwR k hk hop hr
        · exact hR0_noAnd (n + h) hhR k hk hop (Relation.ReflTransGen.head hstep_a hr)
        · exact hR0_noAnd (n + h) hhR k hk hop (Relation.ReflTransGen.head hstep_b hr)
      have hF'_sub : Fout R' ⊆ (Fout R0).erase h := by
        intro k hk
        simp only [Fout, Finset.mem_filter] at hk
        obtain ⟨hkrng, hkop, hkB, w, hwR', hwk⟩ := hk
        have hwk_orig : ∃ w' ∈ R0, OrROut n C B w' (n + k) := by
          simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton] at hwR'
          rcases hwR' with ⟨_, hwR⟩ | rfl | rfl
          · exact ⟨w, hwR, hwk⟩
          · exact ⟨n + h, hhR, Relation.ReflTransGen.head hstepOut_a hwk⟩
          · exact ⟨n + h, hhR, Relation.ReflTransGen.head hstepOut_b hwk⟩
        have hkF0 : k ∈ Fout R0 := Finset.mem_filter.mpr ⟨hkrng, hkop, hkB, hwk_orig⟩
        refine Finset.mem_erase.mpr ⟨?_, hkF0⟩
        intro hkh
        subst hkh
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hwR'
        rcases hwR' with ⟨hne, hwR⟩ | rfl | rfl
        · exact hne (hreach_eq w hwR hwk)
        · have := orROut_le hA hwk; omega
        · have := orROut_le hA hwk; omega
      have hF'_lt : (Fout R').card < m := by
        have h1 : (Fout R').card ≤ ((Fout R0).erase h).card := Finset.card_le_card hF'_sub
        have h2 : ((Fout R0).erase h).card + 1 = (Fout R0).card := Finset.card_erase_add_one hhF
        omega
      have hR'_card : R'.card ≤ R0.card + 1 := by
        have h1 : R'.card ≤ (R0.erase (n + h)).card + ({a, b} : Finset ℕ).card :=
          Finset.card_union_le _ _
        have h2 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        have h3 : (R0.erase (n + h)).card + 1 = R0.card := Finset.card_erase_add_one hhR
        omega
      have hunion_sub : R0.biUnion (fun w => orIn n C w) ⊆ R'.biUnion (fun w => orIn n C w) := by
        intro u hu
        simp only [Finset.mem_biUnion] at hu ⊢
        obtain ⟨w, hwR, huw⟩ := hu
        by_cases hwh : w = n + h
        · subst hwh
          have hr := (mem_orIn n C hA (n + h) (by omega) u).mp huw
          rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hst, hrest⟩
          · have := u.isLt; omega
          · obtain ⟨k, hk_eq, _, _, hc⟩ := hst
            have hkh : k = h := by omega
            subst hkh
            rw [hab] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact ⟨c, Finset.mem_union_right _ (by simp),
                (mem_orIn n C hA c (by omega) u).mpr hrest⟩
            · exact ⟨c, Finset.mem_union_right _ (by simp),
                (mem_orIn n C hA c (by omega) u).mpr hrest⟩
        · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwh, hwR⟩), huw⟩
      have hih := ih (Fout R').card hF'_lt R' hR'_lt hR'_noAnd rfl
      have hsub_card : ((R0.biUnion fun w => orIn n C w) ∩ T).card ≤
          ((R'.biUnion fun w => orIn n C w) ∩ T).card :=
        Finset.card_le_card (Finset.inter_subset_inter_right hunion_sub)
      omega
lemma opnd_lt' {n : ℕ} {C : Circuit} (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  M1528.P2.opnd_lt n C hA a ha (opnd C a) (opnd_eq n C hA a ha) b
lemma W_eq_gateVal {n : ℕ} (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    W n C x (n + k) = gateVal n C k x := rfl
lemma W_mono_input {n : ℕ} (C : Circuit) (hA : AO n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, u < n + C.gates.length → W n C x u = true → W n C y u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · rw [W_input n C x u h1] at hx
      rw [W_input n C y u h1]
      exact hxy ⟨u, h1⟩ hx
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · rw [W_and n C x k hk hop a b hab ha hb, Bool.and_eq_true] at hx
        rw [W_and n C y k hk hop a b hab ha hb, Bool.and_eq_true]
        exact ⟨ih a ha (by omega) hx.1, ih b hb (by omega) hx.2⟩
      · rw [W_or n C x k hk hop a b hab ha hb, Bool.or_eq_true] at hx
        rw [W_or n C y k hk hop a b hab ha hb, Bool.or_eq_true]
        rcases hx with hx | hx
        · exact Or.inl (ih a ha (by omega) hx)
        · exact Or.inr (ih b hb (by omega) hx)
lemma least_of_isLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) : Least n C := by
  refine ⟨AO_of_IsAO2 n C hL.1, fun D hAD hDeq => ?_⟩
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← hL.2.1]
    exact hDeq x
  exact hL.2.2 D (IsAO2_of_AO n D hAD) hfun
lemma graphFun_single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (pairInput u u) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_pair]
  exact G.irrefl
lemma junk_single_props {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ ¬ BelowF G C g ∧
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = g) ∧
    (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False) ∧
    (∀ a ∈ tops G C, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h a → h = g) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hmem_iff : ∀ k, k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
    intro k
    have h1 := M1528.P1.junk_iff G C k
    simpa [BelowF] using h1
  have hgmem : g ∈ junk G C := by rw [hg]; simp
  obtain ⟨hg_lt, hg_op, hg_notB⟩ := (hmem_iff g).mp hgmem
  have huniq : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = g := by
    intro k hk hop hnotB
    have : k ∈ junk G C := (hmem_iff k).mpr ⟨hk, hop, hnotB⟩
    rw [hg, Finset.mem_singleton] at this
    exact this
  have hno_in_g : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False := by
    intro h hh hop hc
    by_cases hB : BelowF G C h
    · exact hT h hh g hg_lt hop hB hg_op hc
    · have heq := huniq h hh hop hB
      subst heq
      have hlt : ∀ i k, k < C.gates.length → InCone n C i k → i < k := by
        intro i k
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          intro hk hic
          rw [M1528.P1.S98.inCone_iff n C i k hk] at hic
          obtain ⟨w, hwin, hnw, hwlt, hcase⟩ := hic
          rcases hcase with rfl | hc'
          · omega
          · have hlt' := ihk (w - n) (by omega) (by omega) hc'
            omega
      exact Nat.lt_irrefl h (hlt h h hg_lt hc)
  have htop_cone : ∀ a ∈ tops G C, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and →
      InCone n C h a → h = g := by
    intro a ha h hh hop hc
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
    by_cases hB : BelowF G C h
    · exact absurd hc (hT h hh a ha.1 hop hB ha.2.1)
    · exact huniq h hh hop hB
  exact ⟨hg_lt, hg_op, hg_notB, huniq, hno_in_g, htop_cone⟩
lemma no_and_in_g_opnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) :
    opnd C g b < n + g ∧
    ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (opnd C g b) (n + h) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, _, _, hno_in_g, _⟩ := junk_single_props G C hL hT g hg
  have hlt := opnd_lt' hA g hg_lt b
  refine ⟨hlt, fun h hh hop hr => ?_⟩
  have hmem : opnd C g b ∈ (gateAt C g).inputs := by
    have := M1528.P2.opnd_eq n C hA g hg_lt
    fin_cases b <;> rw [this] <;> simp
  have hic : InCone n C h g := by
    by_cases hw : opnd C g b < n
    · have := orR_le n C hA _ _ hr; omega
    · obtain ⟨k, hk_eq⟩ : ∃ k, opnd C g b = n + k := ⟨opnd C g b - n, by omega⟩
      rcases orR_cone n C hA h (opnd C g b) hr k hk_eq (by omega) with rfl | hc
      · exact M1528.P1.S98.inCone_c1 n C hA h g hg_lt (hk_eq ▸ hmem)
      · exact M1528.P1.S98.inCone_c2 n C hA h k g hg_lt hc (hk_eq ▸ hmem)
  exact hno_in_g h hh hop hic
lemma pure_or_wire_eval {n : ℕ} (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hnoAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) :
    (orIn n C w).Nonempty ∧
    ∀ x : Fin n → Bool, W n C x w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  constructor
  · obtain ⟨v, hrv, hleaf⟩ := orR_leaf n C hA w hw
    rcases hleaf with hvn | ⟨h, rfl, hh, hop⟩
    · exact ⟨⟨v, hvn⟩, (mem_orIn n C hA w hw ⟨v, hvn⟩).mpr hrv⟩
    · exact absurd hrv (hnoAnd h hh hop)
  · intro x
    constructor
    · intro hW
      obtain ⟨v, hrv, hleaf, hWv⟩ := orR_leaf_true n C hA x w hw hW
      rcases hleaf with hvn | ⟨h, rfl, hh, hop⟩
      · rw [M1528.P1.S98.W_input n C x v hvn] at hWv
        exact ⟨⟨v, hvn⟩, (mem_orIn n C hA w hw ⟨v, hvn⟩).mpr hrv, hWv⟩
      · exact absurd hrv (hnoAnd h hh hop)
    · rintro ⟨u, hu, hxu⟩
      have hru := (mem_orIn n C hA w hw u).mp hu
      refine orR_mono n C hA x w u.val hru ?_
      rw [M1528.P1.S98.W_input n C x u.val u.isLt]
      exact hxu
lemma g_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    let P := side (n := n) C g 0
    let Q := side (n := n) C g 1
    let Wg := wmax G C g
    P.Nonempty ∧ Q.Nonempty ∧
    (∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ P, x p = true) ∧ (∃ q ∈ Q, x q = true)) ∧
    (∀ w : Fin n, w ∈ Wg ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) ∧
    (∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, hg_notB, _, _, _⟩ := junk_single_props G C hL hT g hg
  obtain ⟨h0_lt, h0_no⟩ := no_and_in_g_opnd G C hL hT g hg 0
  obtain ⟨h1_lt, h1_no⟩ := no_and_in_g_opnd G C hL hT g hg 1
  obtain ⟨hPne, hPeval⟩ := pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no
  obtain ⟨hQne, hQeval⟩ := pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no
  have hgeval : ∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ side (n := n) C g 0, x p = true) ∧ (∃ q ∈ side (n := n) C g 1, x q = true) := by
    intro x
    rw [W_and n C x g hg_lt hg_op (opnd C g 0) (opnd C g 1) (opnd_eq n C hA g hg_lt) h0_lt h1_lt,
      Bool.and_eq_true, hPeval x, hQeval x]
    rfl
  refine ⟨hPne, hQne, hgeval, ?_, ?_⟩
  · intro w
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw p hp q hq
      let x : Fin n → Bool := fun i => decide (i = p ∨ i = q ∨ i = w)
      have hgx : gateVal n C g x = true := by
        rw [← W_eq_gateVal, hgeval x]
        exact ⟨⟨p, hp, by simp [x]⟩, ⟨q, hq, by simp [x]⟩⟩
      have hxw : x w = true := by simp [x]
      have hF := hw x hgx hxw
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hF
      obtain ⟨a, b, hab, hxa, hxb⟩ := hF
      simp only [x, decide_eq_true_eq] at hxa hxb
      rcases hxa with rfl | rfl | rfl <;> rcases hxb with rfl | rfl | rfl
      · exact (G.irrefl hab).elim
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
      · exact Or.inl hab.symm
      · exact (G.irrefl hab).elim
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inl hab.symm)
      · exact Or.inr (Or.inr hab.symm)
      · exact (G.irrefl hab).elim
    · intro hcond x hgx hxw
      rw [← W_eq_gateVal, hgeval x] at hgx
      obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      rcases hcond p hp q hq with h | h | h
      · exact ⟨p, q, h, hxp, hxq⟩
      · exact ⟨p, w, h, hxp, hxw⟩
      · exact ⟨q, w, h, hxq, hxw⟩
  · simp only [BelowF, not_forall] at hg_notB
    obtain ⟨x, hx⟩ := hg_notB
    push Not at hx
    obtain ⟨hgx, hFx⟩ := hx
    rw [← W_eq_gateVal, hgeval x] at hgx
    obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
    refine ⟨p, hp, q, hq, fun hadj => hFx ?_⟩
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨p, q, hadj, hxp, hxq⟩
lemma lam_has_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (h : ℕ) (hh : h ∈ lam G C) :
    ∃ c : Fin n, ∀ u ∈ orIn n C (n + h), G.Adj c u ∧ s(c, u) ∈ starEdges G C := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  simp only [lam, Finset.mem_filter] at hh
  obtain ⟨_, _, _, a, ha, b, hcard1, hreach⟩ := hh
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨c, fun u hu => ?_⟩
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  have hreach_orR := orReaches_orR n C (opnd C a b) (by have := opnd_lt' hA a ha.1 b; omega) h hreach
  have hhu : OrR n C (n + h) u.val := (mem_orIn n C hA (n + h) (by
    have hlt := orR_le n C hA _ _ hreach_orR
    have := opnd_lt' hA a ha.1 b
    omega) u).mp hu
  have hu_side : u ∈ side (n := n) C a b :=
    (mem_orIn n C hA (opnd C a b) (by have := opnd_lt' hA a ha.1 b; omega) u).mpr
      (hreach_orR.trans hhu)
  have hc_side : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
  have hadj : G.Adj c u := by
    have hr_c := (mem_orIn n C hA (opnd C a (1 - b))
      (by have := opnd_lt' hA a ha.1 (1 - b); omega) c).mp hc_side
    have hr_u := (mem_orIn n C hA (opnd C a b)
      (by have := opnd_lt' hA a ha.1 b; omega) u).mp hu_side
    have hpair : W n C (pairInput c u) (n + a) = true := by
      have h0 : W n C (pairInput c u) (opnd C a b) = true :=
        orR_mono n C hA _ _ _ hr_u (by rw [M1528.P1.S98.W_input n C _ u.val u.isLt]; simp [pairInput])
      have h1 : W n C (pairInput c u) (opnd C a (1 - b)) = true :=
        orR_mono n C hA _ _ _ hr_c (by rw [M1528.P1.S98.W_input n C _ c.val c.isLt]; simp [pairInput])
      rw [W_and n C _ a ha.1 ha.2.1 (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha.1)
        (opnd_lt' hA a ha.1 0) (opnd_lt' hA a ha.1 1), Bool.and_eq_true]
      fin_cases b <;> simp_all
    have hF := ha.2.2 (pairInput c u) hpair
    rwa [graphFun_pair] at hF
  have hstar : s(c, u) ∈ starEdges G C := by
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
    refine ⟨a, by simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]; exact ha, ?_⟩
    fin_cases b
    · exact ⟨(u, c), ⟨hu_side, by simpa using hc_side⟩, Sym2.eq_swap⟩
    · exact ⟨(c, u), ⟨by simpa using hc_side, hu_side⟩, rfl⟩
  exact ⟨hadj, hstar⟩
lemma lam_card_le_one_of_common_nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (z : Fin n) (T : Finset (Fin n))
    (hadj : ∀ u ∈ T, G.Adj z u)
    (hnotStar : ∀ u v, u ∈ T → v ∈ T → u ≠ v → s(z, u) ∉ starEdges G C ∨ s(z, v) ∉ starEdges G C)
    (h : ℕ) (hh : h ∈ lam G C) :
    ((orIn n C (n + h)) ∩ T).card ≤ 1 := by
  obtain ⟨c, hc⟩ := lam_has_center G C hL h hh
  refine Finset.card_le_one.mpr fun u hu v hv => ?_
  by_contra hne
  have hu1 := (Finset.mem_inter.mp hu).1
  have huT := (Finset.mem_inter.mp hu).2
  have hv1 := (Finset.mem_inter.mp hv).1
  have hvT := (Finset.mem_inter.mp hv).2
  have hcz : c = z := by
    by_contra hcz_ne
    exact nfc n G h4 c u z v hcz_ne hne
      ⟨(hc u hu1).1, (hadj u huT).symm, hadj v hvT, (hc v hv1).1.symm⟩
  subst hcz
  rcases hnotStar u v huT hvT hne with hns | hns
  · exact hns (hc u hu1).2
  · exact hns (hc v hv1).2
lemma pure_or_gate_in_orN_not_mixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (w : ℕ) (_hw : w < n + C.gates.length)
    (hnoAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h))
    (k : ℕ) (hk : k < C.gates.length) (hkop : (gateAt C k).op = GateOp.or)
    (hr : OrR n C w (n + k)) :
    k ∈ orN G C ∧ k ∉ mixing G C := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hk_noAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (n + k) (n + h) :=
    fun h hh hop hkr => hnoAnd h hh hop (hr.trans hkr)
  have hkne : (orIn n C (n + k)).Nonempty := (pure_or_wire_eval C hA (n + k) (by omega) hk_noAnd).1
  have hnotB : ¬ BelowF G C k := by
    intro hB
    obtain ⟨u, hu⟩ := hkne
    have hWu : W n C (pairInput u u) (n + k) = true :=
      (pure_or_wire_eval C hA (n + k) (by omega) hk_noAnd).2 (pairInput u u) |>.mpr
        ⟨u, hu, by simp [pairInput]⟩
    have hF := hB (pairInput u u) hWu
    rw [graphFun_single_false G u] at hF
    exact Bool.noConfusion hF
  have horN : k ∈ orN G C := by
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, hkop, hnotB⟩
  have hnotMix : k ∉ mixing G C := by
    simp only [mixing, Finset.mem_filter, not_and]
    intro _
    have hop_ne : ∀ b : Fin 2, (orIn n C (opnd C k b)).Nonempty := by
      intro b
      have hlt := opnd_lt' hA k hk b
      have hmem : opnd C k b ∈ (gateAt C k).inputs := by
        have := opnd_eq n C hA k hk
        fin_cases b <;> rw [this] <;> simp
      have hstep : OrStep n C (n + k) (opnd C k b) := ⟨k, rfl, hk, hkop, hmem⟩
      exact (pure_or_wire_eval C hA (opnd C k b) (by omega) (fun h hh hop hbr =>
        hk_noAnd h hh hop (Relation.ReflTransGen.head hstep hbr))).1
    have h0 := Finset.nonempty_iff_ne_empty.mp (hop_ne 0)
    have h1 := Finset.nonempty_iff_ne_empty.mp (hop_ne 1)
    simp [h0, h1]
  exact ⟨horN, hnotMix⟩
lemma crossPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2} {u v : Fin n}
    (hu : u ∈ side C a b) (hv : v ∈ side C a (1-b)) : s(u,v) ∈ starEdges G C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, Finset.mem_image.mpr ?_⟩
  fin_cases b
  · exact ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, rfl⟩
  · exact ⟨(v,u), Finset.mem_product.mpr ⟨hv,hu⟩, Sym2.eq_swap⟩

lemma coverAssemble {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (K X : Finset (Fin n))
    (hK : ∀ e ∈ starEdges G C, ∃ z ∈ K, z ∈ e)
    (hX : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ X, z ∈ e) :
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (K ∪ X) := by
  intro u v hadj
  have hE : s(u,v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
  have h : ∃ z ∈ K ∪ X, z ∈ s(u,v) := by
    by_cases hs : s(u,v) ∈ starEdges G C
    · obtain ⟨z,hz,he⟩ := hK _ hs
      exact ⟨z, Finset.mem_union_left _ hz, he⟩
    · exact hX _ (Finset.mem_sdiff.mpr ⟨hE,hs⟩)
  obtain ⟨z,hz,he⟩ := h
  rcases Sym2.mem_iff.mp he with rfl | rfl
  · exact Or.inl hz
  · exact Or.inr hz

lemma bothStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C) (h4 : NoFourCycle G) {a : ℕ}
    (ha : a ∈ tops G C \ centreless G C) :
    ∃ b : Fin 2, ∃ u : Fin n, side C a b = {u} := by
  have ht := (Finset.mem_sdiff.mp ha).1
  obtain ⟨hl, ho, hb⟩ : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ht
  have hn : ∀ b : Fin 2, (side (n := n) C a b).Nonempty := by
    intro b
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply (Finset.mem_sdiff.mp ha).2
    refine Finset.mem_filter.mpr ⟨ht, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  have hc : ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, G.Adj u v := by
    intro u hu v hv
    have h := M1528.P2.sem_adj n C hA a hl ho (opnd C a) (opnd_eq n C hA a hl) u v
      ((mem_orIn n C hA _ (by have := opnd_lt' hA a hl 0; omega) u).mp hu)
      ((mem_orIn n C hA _ (by have := opnd_lt' hA a hl 1; omega) v).mp hv)
    exact (graphFun_pair G u v).mp (hb _ h)
  rcases M1528.P2.biclique_star G (nfc n G h4) (side C a 0) (side C a 1) hc with h | h
  · obtain ⟨u,hu⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr (hn 0)))
    exact ⟨0,u,hu⟩
  · obtain ⟨u,hu⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr (hn 1)))
    exact ⟨1,u,hu⟩

lemma coverSelected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (centres : ℕ → Fin n)
    (hcentres : ∀ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, side C a b = {centres a}) :
    ∀ e ∈ starEdges G C, ∃ z ∈ (tops G C \ centreless G C).image centres, z ∈ e := by
  intro e he
  obtain ⟨a,ha,hcross⟩ := Finset.mem_biUnion.mp he
  obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hcross
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
  have has : a ∈ tops G C \ centreless G C := by
    refine Finset.mem_sdiff.mpr ⟨ha, fun hf => ?_⟩
    rcases (Finset.mem_filter.mp hf).2 with h | h
    · rw [h] at hu
      exact Finset.notMem_empty _ hu
    · rw [h] at hv
      exact Finset.notMem_empty _ hv
  refine ⟨centres a, Finset.mem_image.mpr ⟨a,has,rfl⟩, ?_⟩
  obtain ⟨b,hb⟩ := hcentres a has
  fin_cases b
  · change side C a 0 = {centres a} at hb
    change u ∈ side C a 0 at hu
    rw [hb, Finset.mem_singleton] at hu
    exact hu ▸ Sym2.mem_mk_left u v
  · change side C a 1 = {centres a} at hb
    change v ∈ side C a 1 at hv
    rw [hb, Finset.mem_singleton] at hv
    exact hv ▸ Sym2.mem_mk_right u v

lemma ntMixSubset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    mixing G C ⊆ orN G C \ lam G C := by
  intro h hm
  obtain ⟨hor, hx⟩ := Finset.mem_filter.mp hm
  refine Finset.mem_sdiff.mpr ⟨hor, fun hl => ?_⟩
  obtain ⟨_,h0,h1,_⟩ := Finset.mem_filter.mp hl
  exact hx (propext ⟨fun h => (h0.ne_empty h).elim, fun h => (h1.ne_empty h).elim⟩)

-- Count only OR gates whose support contains at least two selected leaves.
noncomputable def pureBudget {n : ℕ} (C : Circuit)
    (R : Finset ℕ) (T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun h =>
    (gateAt C h).op = GateOp.or ∧ 1 < (orIn n C (n+h) ∩ T).card ∧
    ∃ r ∈ R, OrR n C r (n+h)

lemma pureBudget_le {n : ℕ} (C : Circuit) (hA : AO n C)
    (R : Finset ℕ) (T : Finset (Fin n))
    (hR : ∀ r ∈ R, r < n + C.gates.length)
    (hno : ∀ r ∈ R, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h))
    (hT : T ⊆ R.biUnion (fun r => orIn n C r)) :
    T.card ≤ R.card + (pureBudget C R T).card := by
  classical
  let B := (Finset.range C.gates.length).filter fun h => (orIn n C (n+h) ∩ T).card ≤ 1
  have hb := or_dag_leaf_bound C hA T B (fun h hh => (Finset.mem_filter.mp hh).2) R hR hno
  rw [Finset.inter_eq_right.mpr hT] at hb
  have hP : ((Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ r ∈ R, OrR n C r (n+h)) = pureBudget C R T := by
    ext j
    by_cases h : j < C.gates.length <;> simp [pureBudget,B,h]
  rwa [hP] at hb

lemma pureBudget_sub {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (R : Finset ℕ) (T : Finset (Fin n))
    (hR : ∀ r ∈ R, r < n + C.gates.length)
    (hno : ∀ r ∈ R, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h))
    (hlam : ∀ h ∈ lam G C, (orIn n C (n+h) ∩ T).card ≤ 1) :
    pureBudget C R T ⊆ (orN G C \ lam G C) \ mixing G C := by
  classical
  intro h hh
  obtain ⟨hl, ho, hbig, r, hr, hreach⟩ := Finset.mem_filter.mp hh
  obtain ⟨hN, hM⟩ := pure_or_gate_in_orN_not_mixing G C hL r (hR r hr)
    (hno r hr) h (Finset.mem_range.mp hl) ho hreach
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hN, fun hL => (Nat.not_le_of_lt hbig) (hlam h hL)⟩, hM⟩

lemma budgetScoped {n : ℕ} (C : Circuit) (hA : AO n C) {R : Finset ℕ} {T : Finset (Fin n)}
    {h : ℕ} (hh : h ∈ pureBudget C R T) {S : Finset (Fin n)}
    (hR : ∀ r ∈ R, r < n + C.gates.length ∧ orIn n C r ⊆ S) :
    orIn n C (n+h) ⊆ S := by
  classical
  obtain ⟨_,_,_,r,hr,hreach⟩ := Finset.mem_filter.mp hh
  intro u hu
  obtain ⟨hrl,hrs⟩ := hR r hr
  have hhl := orR_le n C hA _ _ hreach
  exact hrs ((mem_orIn n C hA r hrl u).mpr
    (hreach.trans ((mem_orIn n C hA (n+h) (by omega) u).mp hu)))

lemma bigBudget {n : ℕ} (C : Circuit) {R : Finset ℕ} {T : Finset (Fin n)}
    {h : ℕ} (hh : h ∈ pureBudget C R T) : 1 < (orIn n C (n+h)).card := by
  classical
  exact (Finset.mem_filter.mp hh).2.2.1.trans_le (Finset.card_le_card Finset.inter_subset_left)



lemma topProps {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma topAnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hA : AO n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) (x : Fin n → Bool)
    (hx : W n C x (opnd C a b) = true) (hy : W n C x (opnd C a (1-b)) = true) :
    graphFun G ∅ x = true := by
  obtain ⟨hl,ho,hbel⟩ := topProps ha
  apply hbel
  rw [← W_eq_gateVal, W_and n C x a hl ho (opnd C a 0) (opnd C a 1)
    (opnd_eq n C hA a hl) (opnd_lt' hA a hl 0) (opnd_lt' hA a hl 1), Bool.and_eq_true]
  fin_cases b
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

lemma sideImp {n : ℕ} {C : Circuit} (hA : AO n C) {w : ℕ} (hw : w < n + C.gates.length)
    {u : Fin n} {x : Fin n → Bool} (hu : u ∈ orIn n C w) (hx : x u = true) :
    W n C x w = true :=
  orR_mono n C hA x w u.val ((mem_orIn n C hA w hw u).mp hu)
    ((W_input n C x u.val u.isLt).trans hx)

lemma topAdj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hA : AO n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) {u v : Fin n}
    (hu : u ∈ side C a b) (hv : v ∈ side C a (1-b)) :
    G.Adj u v := by
  have hl := (topProps ha).1
  exact (graphFun_pair G u v).mp (topAnd hA ha b (pairInput u v)
    (sideImp hA ((opnd_lt' hA a hl b).trans (by omega)) hu (by simp [pairInput]))
    (sideImp hA ((opnd_lt' hA a hl (1-b)).trans (by omega)) hv (by simp [pairInput])))

def mixTarget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g m : ℕ) (w : Fin n) : Prop :=
  m ∈ mixing G C ∧ n + g ∈ (gateAt C m).inputs ∧
  ∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2,
    OrReaches n C (opnd C a b) m ∧ OrReaches n C (opnd C a b) g ∧
    w ∈ side C a (1-b) ∧ side (n := n) C a (1-b) ⊆ wmax G C g

def filterTarget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (w : Fin n) : Prop :=
  ∃ a ∈ centreless G C, ∃ b : Fin 2,
    opnd C a b = n + g ∧ w ∈ side C a (1-b)



lemma reachableAnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a j : ℕ} (ha : a ∈ tops G C) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (hr : OrR n C (opnd C a b) (n+j)) : j = g := by
  have hA := AO_of_IsAO2 n C hL.1
  have ha' := (topProps ha).1
  have hl := opnd_lt' hA a ha' b
  have hr' := orR_le n C hA _ _ hr
  have hm : opnd C a b ∈ (gateAt C a).inputs := by
    rw [opnd_eq n C hA a ha']
    fin_cases b <;> simp
  let k := opnd C a b - n
  have hk : opnd C a b = n+k := by dsimp [k]; omega
  have hc : InCone n C j a := by
    rcases orR_cone n C hA j (opnd C a b) hr k hk (by omega) with h | h
    · rw [← h] at hk
      exact M1528.P1.S98.inCone_c1 n C hA j a ha' (hk ▸ hm)
    · exact M1528.P1.S98.inCone_c2 n C hA j k a ha' h (hk ▸ hm)
  exact (junk_single_props G C hL hT g hg).2.2.2.2.2 a ha j hj hop hc

lemma emptyOrIsJunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrR n C (opnd C a b) (n+g)) (he : side (n := n) C a b = ∅) :
    opnd C a b = n+g := by
  have hA := AO_of_IsAO2 n C hL.1
  have hle := orR_le n C hA _ _ hrg
  have hal := (topProps ha).1
  have hl := opnd_lt' hA a hal b
  by_contra hne
  let j := opnd C a b - n
  have hj : opnd C a b = n+j := by dsimp [j]; omega
  have hbound : j < C.gates.length := by omega
  obtain ⟨x,hx⟩ := M1528.P1.S98.least_nodup n C (least_of_isLeastAO G C hL) (n+g) j
    (by omega) hbound
  rw [← hj] at hx
  apply hx
  cases hf : W n C x (n+g)
  · cases hval : W n C x (opnd C a b)
    · rfl
    · obtain ⟨w,hp,hs,hw⟩ := orR_leaf_true n C hA x _ (by omega) hval
      rcases hs with hlt | ⟨k,rfl,hk,hkop⟩
      · have hn : (⟨w,hlt⟩ : Fin n) ∈ side C a b :=
          (mem_orIn n C hA _ (by omega) _).mpr hp
        rw [he] at hn
        exact (Finset.notMem_empty _ hn).elim
      · have hkg := reachableAnd G C hL hT g hg ha hk hkop b hp
        subst k
        rw [hf] at hw
        contradiction
  · exact (orR_mono n C hA x _ _ hrg hf).symm
lemma directInputWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {m a : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hrm : OrReaches n C (opnd C a b) m)
    (hm_lt : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n+g ∈ (gateAt C m).inputs) :
    ∃ y ∈ (gateAt C m).inputs, y < n+m ∧ ∃ u ∈ orIn n C y,
      gateVal n C g (pairInput u u) = false ∧
      ∀ a ∈ tops G C, ∀ b : Fin 2, OrReaches n C (opnd C a b) m →
        u ∈ side C a b := by
  have hA := AO_of_IsAO2 n C hL.1
  obtain ⟨_, p, q, hin, hp, hq⟩ := hA m hm_lt
  have hGlt : n+g < n+m := by
    rw [hin] at hgm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgm
    omega
  obtain ⟨y,hy,hylt,hmor⟩ : ∃ y ∈ (gateAt C m).inputs, y < n+m ∧
      ∀ x : Fin n → Bool, W n C x (n+m) = (W n C x (n+g) || W n C x y) := by
    rw [hin] at hgm ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgm ⊢
    rcases hgm with h | h
    · exact ⟨q,Or.inr rfl,hq,fun x => (W_or n C x m hm_lt hmop p q hin hp hq).trans (by rw [h])⟩
    · exact ⟨p,Or.inl rfl,hp,fun x => (W_or n C x m hm_lt hmop p q hin hp hq).trans (by rw [h,Bool.or_comm])⟩
  have hx : ∃ x : Fin n → Bool, W n C x (n+m) = true ∧ W n C x (n+g) = false := by
    obtain ⟨x,hx⟩ := M1528.P1.S98.least_nodup n C (least_of_isLeastAO G C hL) (n+g) m hGlt hm_lt
    refine ⟨x,?_⟩
    rw [hmor]
    cases hgx : W n C x (n+g) <;> cases hyx : W n C x y <;> simp_all
  obtain ⟨x,hx,hgx⟩ := hx
  have hxy : W n C x y = true := by simpa only [hmor,hgx,Bool.false_or] using hx
  have hmPath : OrR n C (n+m) y := Relation.ReflTransGen.single ⟨m,rfl,hm_lt,hmop,hy⟩
  obtain ⟨w,hw,hl,hval⟩ := orR_leaf_true n C hA x y (by omega) hxy
  have hlo : ∀ a ∈ tops G C, ∀ b : Fin 2, opnd C a b < n+C.gates.length := by
    intro d hd i
    have hd' := (topProps hd).1
    have := opnd_lt' hA d hd' i
    omega
  rcases hl with hlt | ⟨j,rfl,hj,hjop⟩
  · let u : Fin n := ⟨w,hlt⟩
    have xu : x u = true := by rwa [W_input n C _ _ hlt] at hval
    refine ⟨y,hy,hylt,u,(mem_orIn n C hA _ (by omega) u).mpr hw,?_,?_⟩
    · cases hh : gateVal n C g (pairInput u u)
      · rfl
      · have himp (t : Fin n) (ht : pairInput u u t = true) : x t = true := by
          rcases (pairInput_true u u t).mp ht with rfl | rfl <;> exact xu
        have hp := W_mono_input C hA _ x himp (n+g) (by omega) hh
        exact (Bool.false_ne_true (hgx.symm.trans hp)).elim
    · intro d hd i hmi
      exact (mem_orIn n C hA _ (hlo d hd i) u).mpr
        ((orReaches_orR n C _ (hlo d hd i) _ hmi).trans (hmPath.trans hw))
  · have hjg : j = g := reachableAnd G C hL hT g hg ha hj hjop b
      ((orReaches_orR n C _ (hlo a ha b) _ hrm).trans (hmPath.trans hw))
    subst j
    rw [hgx] at hval
    contradiction





lemma junkWireEmpty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    orIn n C (n+g) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hgl,hgop,_⟩ := junk_single_props G C hL hT g hg
  have hr := (mem_orIn n C (AO_of_IsAO2 n C hL.1) (n+g) (by omega) u).mp hu
  rcases Relation.ReflTransGen.cases_head hr with he | ⟨_,⟨i,hi,_,hop,_⟩,_⟩
  · have := u.isLt
    omega
  · have hi' : i = g := by omega
    subst i
    rw [hgop] at hop
    contradiction

lemma firstMix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrR n C (opnd C a b) (n+g)) (hs : (side (n := n) C a b).Nonempty) :
    ∃ m ∈ mixing G C, OrReaches n C (opnd C a b) m ∧ n+g ∈ (gateAt C m).inputs := by
  have hA := AO_of_IsAO2 n C hL.1
  have ha' := (topProps ha).1
  have hlo := opnd_lt' hA a ha' b
  have hge := junkWireEmpty G C hL hT g hg
  rcases Relation.ReflTransGen.cases_tail hrg with he | ⟨w,hw,hstep⟩
  · change (orIn n C (opnd C a b)).Nonempty at hs
    have he' : opnd C a b = n+g := by omega
    rw [he',hge] at hs
    exact (Finset.not_nonempty_empty hs).elim
  · obtain ⟨m,rfl,hm,hmor,hgm⟩ := hstep
    have hmr := orR_orReaches n C hA m hm (opnd C a b) (by omega) hw
    obtain ⟨y,hy,hylt,u,hu,_,_⟩ := directInputWitness G C hL hT g hg ha hmr hm hmor hgm
    have hye : orIn n C y ≠ ∅ := (show (orIn n C y).Nonempty from ⟨u,hu⟩).ne_empty
    have hyne : y ≠ n+g := fun h => hye (h.symm ▸ hge)
    refine ⟨m,Finset.mem_filter.mpr ⟨?_,?_⟩,hmr,hgm⟩
    · let _ : DecidableEq GateOp := gateOpDecEq
      unfold orN gatesWhere
      rw [Finset.mem_filter,Finset.mem_range]
      refine ⟨hm,hmor,fun hB => ?_⟩
      have htrue : W n C (pairInput u u) (n+m) = true :=
        orR_mono n C hA _ _ _ (Relation.ReflTransGen.single ⟨m,rfl,hm,hmor,hy⟩)
          (sideImp hA (by omega) hu (by simp [pairInput]))
      have hh := hB (pairInput u u) htrue
      rw [graphFun_single_false] at hh
      contradiction
    · obtain ⟨_,p,q,hin,_,_⟩ := hA m hm
      have hp : opnd C m 0 = p := by simp [opnd,hin]
      have hq : opnd C m 1 = q := by simp [opnd,hin]
      rw [hp,hq]
      rw [hin] at hgm hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hgm hy
      rcases hgm with hg' | hg' <;> rcases hy with hy' | hy'
      · exact (hyne (hy'.trans hg'.symm)).elim
      · rw [← hg',← hy',hge]
        simp [hye]
      · rw [← hg',← hy',hge]
        simp [hye]
      · exact (hyne (hy'.trans hg'.symm)).elim

lemma mixedWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {m a : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hrm : OrReaches n C (opnd C a b) m)
    (hm : m ∈ mixing G C) (hgm : n+g ∈ (gateAt C m).inputs) :
    ∃ u : Fin n, gateVal n C g (pairInput u u) = false ∧
      ∀ a ∈ tops G C, ∀ b : Fin 2, OrReaches n C (opnd C a b) m →
        u ∈ side C a b := by
  have hmdata : m < C.gates.length ∧ (gateAt C m).op = GateOp.or := by
    simp only [mixing,orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at hm
    exact ⟨hm.1.1,hm.1.2.1⟩
  obtain ⟨_,_,_,u,_,hx,hs⟩ :=
    directInputWitness G C hL hT g hg ha hrm hmdata.1 hmdata.2 hgm
  exact ⟨u,hx,hs⟩

lemma residualToward {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (_h4 : NoFourCycle G) (_hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) :
    (∀ b : Fin 2, u ∈ side C g b ∨ v ∈ side C g b) ∧
    ∃ w ∈ wmax G C g, w ∈ s(u,v) ∧
      (filterTarget G C g w ∨ ∃ m, mixTarget G C g m w) := by
  have hadj := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  let x := pairInput u v
  have hA := AO_of_IsAO2 n C hL.1
  have hcalc (z : Fin n → Bool) : W n C z C.output = graphFun G ∅ z := congrFun hL.2.1 z
  have hx : W n C x C.output = true := (hcalc x).trans ((graphFun_pair G u v).mpr hadj)
  have hOut : C.output < n + C.gates.length := by
    by_contra! hh
    rw [W, M1528.P1.S98.getD_ge_length _ _ (by rw [M1528.P1.S98.wires_length]; exact hh)] at hx
    contradiction
  obtain ⟨w,hr,hl,hw⟩ := orR_leaf_true n C hA x C.output hOut hx
  rcases hl with hlt | ⟨a,rfl,ha,hop⟩
  · exfalso
    let t : Fin n := ⟨w,hlt⟩
    have ht : W n C (pairInput t t) w = true := by
      rw [W_input n C _ _ hlt]
      simp [pairInput,t]
    have hout := orR_mono n C hA _ _ _ hr ht
    rw [hcalc,graphFun_single_false] at hout
    contradiction
  have hb : BelowF G C a := by
    intro y hy
    rw [← hcalc]
    exact orR_mono n C hA y _ _ hr hy
  have htop : a ∈ tops G C := by
    simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using And.intro ha ⟨hop,hb⟩
  have hbound (i : Fin 2) : opnd C a i < n+C.gates.length := by
    have := opnd_lt' hA a ha i
    omega
  rw [W_and n C x a ha hop (opnd C a 0) (opnd C a 1)
    (opnd_eq n C hA a ha) (opnd_lt' hA a ha 0) (opnd_lt' hA a ha 1), Bool.and_eq_true] at hw
  have trace (i : Fin 2) :
      (∃ z ∈ side C a i, x z = true) ∨
      (OrR n C (opnd C a i) (n+g) ∧ gateVal n C g x = true) := by
    have hi : W n C x (opnd C a i) = true := by
      fin_cases i
      · exact hw.1
      · exact hw.2
    obtain ⟨r,hp,hl,hv⟩ := orR_leaf_true n C hA x _ (hbound i) hi
    rcases hl with hlt | ⟨j,rfl,hj,hjop⟩
    · refine Or.inl ⟨⟨r,hlt⟩,(mem_orIn n C hA _ (hbound i) _).mpr hp,?_⟩
      rwa [W_input n C _ _ hlt] at hv
    · have heq := reachableAnd G C hL hT g hg htop hj hjop i hp
      subst j
      exact Or.inr ⟨hp,hv⟩
  have done (b : Fin 2) (hrg : OrR n C (opnd C a b) (n+g)) (hgx : gateVal n C g x = true)
      (z : Fin n) (hz : z ∈ side C a (1-b)) (hxz : x z = true) :
      ∃ w ∈ wmax G C g, w ∈ s(u,v) ∧
        (filterTarget G C g w ∨ ∃ m, mixTarget G C g m w) := by
    have hset : side (n := n) C a (1-b) ⊆ wmax G C g := by
      intro t ht
      simp only [wmax,Finset.mem_filter,Finset.mem_univ,true_and]
      intro y hgval htval
      exact topAnd hA htop b y (orR_mono n C hA y _ _ hrg hgval) (sideImp hA (hbound (1-b)) ht htval)
    by_cases hc : a ∈ centreless G C
    · have he : side (n := n) C a b = ∅ := by
        rcases M1528.P2.fin2_sub b with ⟨rfl,hopp⟩ | ⟨rfl,hopp⟩
        · rcases (Finset.mem_filter.mp hc).2 with hh | hh
          · exact hh
          · rw [hopp,hh] at hz
            exact (Finset.notMem_empty _ hz).elim
        · rcases (Finset.mem_filter.mp hc).2 with hh | hh
          · rw [hopp,hh] at hz
            exact (Finset.notMem_empty _ hz).elim
          · exact hh
      have hgz := emptyOrIsJunk G C hL hT g hg htop b hrg he
      exact ⟨z,hset hz,Sym2.mem_iff.mpr ((pairInput_true u v z).mp hxz),
        Or.inl ⟨a,hc,b,hgz,hz⟩⟩
    · have hn : (side (n := n) C a b).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hs
        apply hc
        refine Finset.mem_filter.mpr ⟨htop,?_⟩
        fin_cases b
        · exact Or.inl hs
        · exact Or.inr hs
      have hgl := (junk_single_props G C hL hT g hg).1
      have hrg' := orR_orReaches n C hA g hgl _ (hbound b) hrg
      obtain ⟨m,hm,hrm,hgm⟩ := firstMix G C hL hT g hg htop b hrg hn
      exact ⟨z,hset hz,Sym2.mem_iff.mpr ((pairInput_true u v z).mp hxz),
        Or.inr ⟨m,hm,hgm,a,Finset.mem_sdiff.mpr ⟨htop,hc⟩,b,hrm,hrg',hz,hset⟩⟩
  have both (hgtrue : gateVal n C g x = true) :
      ∀ b : Fin 2, u ∈ side C g b ∨ v ∈ side C g b := by
    have hsem := (g_semantics G C hL hT g hg).2.2.1 x
    rw [W_eq_gateVal] at hsem
    obtain ⟨⟨z,hzs,hzx⟩,⟨r,hrs,hrx⟩⟩ := hsem.mp hgtrue
    change pairInput u v z = true at hzx
    change pairInput u v r = true at hrx
    rw [pairInput_true] at hzx hrx
    intro i
    fin_cases i
    · rcases hzx with rfl | rfl
      · exact Or.inl hzs
      · exact Or.inr hzs
    · rcases hrx with rfl | rfl
      · exact Or.inl hrs
      · exact Or.inr hrs
  rcases trace 0 with ⟨y,hy,hyx⟩ | ⟨hyg,hyx⟩ <;> rcases trace 1 with ⟨z,hz,hzx⟩ | ⟨hzg,hzx⟩
  · exfalso
    have hne := (topAdj hA htop 0 hy hz).ne
    change pairInput u v y = true at hyx
    change pairInput u v z = true at hzx
    rw [pairInput_true] at hyx hzx
    apply (Finset.mem_sdiff.mp he).2
    rcases hyx with rfl | rfl <;> rcases hzx with rfl | rfl
    · exact (hne rfl).elim
    · exact crossPair G C htop (b := 0) hy hz
    · rw [Sym2.eq_swap]
      exact crossPair G C htop (b := 0) hy hz
    · exact (hne rfl).elim
  · exact ⟨both hzx,done 1 hzg hzx y hy hyx⟩
  · exact ⟨both hyx,done 0 hyg hyx z hz hzx⟩
  · exact ((junk_single_props G C hL hT g hg).2.2.1 (fun y hgy =>
      topAnd hA htop 0 y (orR_mono n C hA y _ _ hyg hgy) (orR_mono n C hA y _ _ hzg hgy))).elim


lemma notTwoCommon {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {a b v w : Fin n} (hab : a ≠ b) (hvw : v ≠ w)
    (hav : G.Adj a v) (hbv : G.Adj b v) (haw : G.Adj a w) (hbw : G.Adj b w) : False :=
  hvw (Finset.card_le_one.mp (h4 a b hab) v (by simp [hav,hbv]) w (by simp [haw,hbw]))

lemma mixedTargetUnique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (_hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {v : Fin n}
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) {m : ℕ} {x y : Fin n}
    (hx : mixTarget G C g m x) (hy : mixTarget G C g m y) :
    x = y := by
  obtain ⟨hm,hgm,a,ha,b,hmb,_,hxs,hxW⟩ := hx
  obtain ⟨_,_,a',ha',b',hmb',_,hys,hyW⟩ := hy
  obtain ⟨u,huf,hux⟩ := mixedWitness G C hL hT g hg (Finset.mem_sdiff.mp ha).1 hmb hm hgm
  have hA := AO_of_IsAO2 n C hL.1
  have hs := g_semantics G C hL hT g hg
  have hne : u ≠ v := by
    rintro rfl
    have hgv := (hs.2.2.1 (pairInput u u)).mpr
      ⟨⟨u,hv0,by simp [pairInput]⟩,⟨u,hv1,by simp [pairInput]⟩⟩
    rw [W_eq_gateVal,huf] at hgv
    contradiction
  have hvW := (thm_1529 n G h4 _ _ _ hs.2.2.2.1).2.2.1
    v (Finset.mem_inter.mpr ⟨hv0,hv1⟩)
  by_contra hxy
  exact notTwoCommon h4 hne hxy
    (topAdj hA (Finset.mem_sdiff.mp ha).1 b (hux a (Finset.mem_sdiff.mp ha).1 b hmb) hxs) (hvW x (hxW hxs))
    (topAdj hA (Finset.mem_sdiff.mp ha').1 b' (hux a' (Finset.mem_sdiff.mp ha').1 b' hmb') hys) (hvW y (hyW hys))

lemma mixedForcesCentre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {v : Fin n}
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1)
    {a m : ℕ} {b : Fin 2} {w : Fin n} (ha : a ∈ tops G C \ centreless G C)
    (hm : m ∈ mixing G C) (hgm : n + g ∈ (gateAt C m).inputs)
    (hrm : OrReaches n C (opnd C a b) m) (hrg : OrReaches n C (opnd C a b) g)
    (hw : w ∈ side C a (1-b)) (hs : side (n := n) C a (1-b) ⊆ wmax G C g) :
    side C a (1-b) = {w} := by
  ext x
  rw [Finset.mem_singleton]
  refine ⟨fun hx => ?_, fun h => h.symm ▸ hw⟩
  exact mixedTargetUnique G C h4 hE hL hT g hg hv0 hv1
    ⟨hm,hgm,a,ha,b,hrm,hrg,hx,hs⟩ ⟨hm,hgm,a,ha,b,hrm,hrg,hw,hs⟩



lemma filterWireUnique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a : ℕ} (ha : a ∈ tops G C) {b d : Fin 2}
    (hb : opnd C a b = n+g) (hd : opnd C a d = n+g) : b = d := by
  by_contra hne
  have hd' : d = 1-b := M1528.P2.fin2_ne b d (Ne.symm hne)
  subst d
  exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx =>
    topAnd (AO_of_IsAO2 n C hL.1) ha b x (by rwa [hb]) (by rwa [hd]))

noncomputable def filterRoots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) : Finset ℕ :=
  (centreless G C).biUnion fun a =>
    ((Finset.univ : Finset (Fin 2)).filter fun b => opnd C a b = n + g).image fun b => opnd C a (1-b)

lemma filterRootsCard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    (filterRoots G C g).card ≤ (centreless G C).card := by
  unfold filterRoots
  refine Finset.card_biUnion_le.trans ?_
  trans ∑ _a ∈ centreless G C, (1 : ℕ)
  · refine Finset.sum_le_sum fun a ha => Finset.card_image_le.trans (Finset.card_le_one.mpr ?_)
    intro x hx y hy
    exact filterWireUnique G C hL hT g hg (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  · simp

lemma filterRootsData {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (_hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {r : ℕ}
    (hr : r ∈ filterRoots G C g) :
    r < n + C.gates.length ∧ orIn n C r ⊆ wmax G C g ∧
    (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h)) := by
  obtain ⟨a,ha,hr⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hr
  have hb := (Finset.mem_filter.mp hb).2
  have ht := (Finset.mem_filter.mp ha).1
  have hl := (topProps ht).1
  have hA := AO_of_IsAO2 n C hL.1
  have hlt := opnd_lt' hA a hl (1-b)
  refine ⟨by omega,?_,?_⟩
  · intro w hw
    simp only [wmax,Finset.mem_filter,Finset.mem_univ,true_and]
    intro x hx hwx
    exact topAnd hA ht b x (by rwa [hb]) (sideImp hA (by omega) hw hwx)
  · intro h hh hop hpath
    have hhg := reachableAnd G C hL hT g hg ht hh hop (1-b) hpath
    subst h
    exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx =>
      topAnd hA ht b x (by rwa [hb]) (orR_mono n C hA x _ _ hpath hx))
lemma filterTarget_leaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) {w : Fin n} (hw : filterTarget G C g w) :
    w ∈ (filterRoots G C g).biUnion (fun r => orIn n C r) := by
  obtain ⟨a,ha,b,hb,hw⟩ := hw
  exact Finset.mem_biUnion.mpr ⟨opnd C a (1-b), Finset.mem_biUnion.mpr
    ⟨a,ha,Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩⟩,hw⟩

lemma residualLamBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (v : Fin n) (T : Finset (Fin n))
    (hadj : ∀ x ∈ T, G.Adj v x) (hpair : ∀ x y, x ∈ T → y ∈ T → x ≠ y →
      s(v,x) ∈ Ustar G C ∨ s(v,y) ∈ Ustar G C) :
    ∀ h ∈ lam G C, (orIn n C (n+h) ∩ T).card ≤ 1 := by
  apply lam_card_le_one_of_common_nbr G h4 C hL v T hadj
  intro x y hx hy hxy
  rcases hpair x y hx hy hxy with hx' | hy'
  · exact Or.inl (Finset.mem_sdiff.mp hx').2
  · exact Or.inr (Finset.mem_sdiff.mp hy').2

lemma oneRoot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) (v : Fin n) (T : Finset (Fin n)) (hsub : T ⊆ side C g b)
    (hadj : ∀ x ∈ T, G.Adj v x)
    (hpair : ∀ x y, x ∈ T → y ∈ T → x ≠ y → s(v,x) ∈ Ustar G C ∨ s(v,y) ∈ Ustar G C) :
    let P := pureBudget C {opnd C g b} T
    T.card ≤ P.card + 1 ∧ P ⊆ (orN G C \ lam G C) \ mixing G C ∧
      ∀ h ∈ P, orIn n C (n+h) ⊆ side C g b := by
  intro P
  have hA := AO_of_IsAO2 n C hL.1
  obtain ⟨hbound,hno⟩ := no_and_in_g_opnd G C hL hT g hg b
  have hl := (junk_single_props G C hL hT g hg).1
  have hR (r : ℕ) (hr : r ∈ ({opnd C g b} : Finset ℕ)) : r < n+C.gates.length := by
    rw [Finset.mem_singleton] at hr
    omega
  have hN (r : ℕ) (hr : r ∈ ({opnd C g b} : Finset ℕ)) :
      ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h) := by
    rwa [Finset.mem_singleton.mp hr]
  refine ⟨?_, pureBudget_sub G C hL _ T hR hN (residualLamBound G C h4 hL v T hadj hpair), ?_⟩
  · have hh := pureBudget_le C hA {opnd C g b} T hR hN (by simpa only [Finset.singleton_biUnion,side] using hsub)
    simpa [P,Nat.add_comm] using hh
  · intro h hh
    exact budgetScoped C hA hh (fun r hr => ⟨hR r hr, by rw [Finset.mem_singleton.mp hr]; exact Finset.Subset.rfl⟩)

lemma filterBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (v : Fin n)
    (T : Finset (Fin n)) (he : ∀ w ∈ T, s(v,w) ∈ Ustar G C)
    (hcert : ∀ w ∈ T, filterTarget G C g w ∨ ∃ m, mixTarget G C g m w)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) :
    ∃ P ⊆ (orN G C \ lam G C) \ mixing G C,
      T.card ≤ P.card + (centreless G C).card + (mixing G C).card ∧
      ∀ h ∈ P, 1 < (orIn n C (n+h)).card ∧ orIn n C (n+h) ⊆ wmax G C g := by
  classical
  have hA := AO_of_IsAO2 n C hL.1
  let S := T.filter (filterTarget G C g)
  let R := filterRoots G C g
  let P := pureBudget C R S
  have hR r (hr : r ∈ R) := filterRootsData G C hE hL hT g hg hr
  have hR' r (hr : r ∈ R) := (hR r hr).1
  have hN r (hr : r ∈ R) := (hR r hr).2.2
  have hSE : ∀ w ∈ S, s(v,w) ∈ Ustar G C := fun w hw => he w (Finset.mem_filter.mp hw).1
  have ha : ∀ w ∈ S, G.Adj v w := fun w hw =>
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hSE w hw)).1
  have hcut := residualLamBound G C h4 hL v S ha (fun x _ hx _ _ => Or.inl (hSE x hx))
  have hp := pureBudget_sub G C hL R S hR' hN hcut
  have hc := pureBudget_le C hA R S hR' hN
    (fun w hw => filterTarget_leaves G C g (Finset.mem_filter.mp hw).2)
  have hc' := filterRootsCard G C hL hT g hg
  have hmex (w : Fin n) (hw : w ∈ T \ S) : ∃ m, mixTarget G C g m w := by
    obtain ⟨hwT,hwS⟩ := Finset.mem_sdiff.mp hw
    exact (hcert w hwT).resolve_left (fun hf => hwS (Finset.mem_filter.mpr ⟨hwT,hf⟩))
  have hmc : (T \ S).card ≤ (mixing G C).card := by
    let f (w : Fin n) := if h : w ∈ T \ S then (hmex w h).choose else 0
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro w hw
      change f w ∈ mixing G C
      rw [show f w = (hmex w hw).choose by
        dsimp only [f]
        exact dite_eq_left (show w ∈ T \ S from hw)]
      exact (hmex w hw).choose_spec.1
    · intro w hw z hz heq
      have hf (w : Fin n) (hw : w ∈ T \ S) : f w = (hmex w hw).choose := by
        dsimp only [f]; rw [dite_eq_left hw]
      rw [hf w hw,hf z hz] at heq
      exact mixedTargetUnique G C h4 hE hL hT g hg hv0 hv1
        (hmex w hw).choose_spec (heq.symm ▸ (hmex z hz).choose_spec)
  have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (filterTarget G C g) T)
  change (T \ S).card + S.card = T.card at hsplit
  change R.card ≤ (centreless G C).card at hc'
  change S.card ≤ R.card + P.card at hc
  refine ⟨P,hp,by omega,?_⟩
  intro h hh
  exact ⟨bigBudget C hh, budgetScoped C hA hh (fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩)⟩



lemma edgeAdj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {u v : Fin n} (h : s(u,v) ∈ Ustar G C) : G.Adj u v :=
  SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp h).1

lemma reverseEdge {n : ℕ} {E : Finset (Sym2 (Fin n))} {u v : Fin n}
    (h : s(u,v) ∈ E) : s(v,u) ∈ E := Sym2.eq_swap ▸ h

lemma budgetCombine {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset ℕ) (hS : S ⊆ (orN G C \ lam G C) \ mixing G C) :
    S.card + (mixing G C).card ≤ (orN G C \ lam G C).card := by
  rw [← Finset.card_union_of_disjoint (show Disjoint S (mixing G C) from Finset.disjoint_left.mpr (fun i hi hm => (Finset.mem_sdiff.mp (hS hi)).2 hm))]
  exact Finset.card_le_card (Finset.union_subset (hS.trans Finset.sdiff_subset) (ntMixSubset G C))

lemma residualResourcePositive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty) :
    1 ≤ 2 * (centreless G C).card + (mixing G C).card := by
  obtain ⟨e,he⟩ := hU
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨_,w,_,_,hw⟩ := residualToward G C h4 hE hL hT g hg he
    rcases hw with ⟨a,ha,_⟩ | ⟨m,hm,_⟩
    · have := Finset.card_pos.mpr ⟨a,ha⟩
      omega
    · have := Finset.card_pos.mpr ⟨m,hm⟩
      omega

lemma scopedDisjoint {n : ℕ} (C : Circuit)
    {R S : Finset ℕ} {T U A B : Finset (Fin n)}
    (hAB : (A ∩ B).card ≤ 1)
    (hA : ∀ h ∈ pureBudget C R T, orIn n C (n+h) ⊆ A)
    (hB : ∀ h ∈ pureBudget C S U, orIn n C (n+h) ⊆ B) :
    Disjoint (pureBudget C R T) (pureBudget C S U) := by
  apply Finset.disjoint_left.mpr
  intro h h1 h2
  exact (Nat.not_le_of_lt (bigBudget C h1))
    ((Finset.card_le_card (Finset.subset_inter (hA h h1) (hB h h2))).trans hAB)



lemma witnessSelected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (v : Fin n)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) (hcl : (centreless G C).card = 0) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card := by
  classical
  let A := tops G C \ centreless G C
  let Cert (a : ℕ) (b : Fin 2) := ∃ m ∈ mixing G C, n+g ∈ (gateAt C m).inputs ∧
    OrReaches n C (opnd C a b) m ∧ OrReaches n C (opnd C a b) g ∧
    (side (n := n) C a (1-b)).Nonempty ∧ side (n := n) C a (1-b) ⊆ wmax G C g
  have hneq (a : ℕ) (ha : a ∈ A) (b d : Fin 2) (hb : Cert a b) (hd : Cert a d) : b = d := by
    by_contra hn
    have hd' := M1528.P2.fin2_ne b d (Ne.symm hn)
    subst d
    obtain ⟨_,_,_,_,hrb,_,_⟩ := hb
    obtain ⟨_,_,_,_,hrd,_,_⟩ := hd
    have hA := AO_of_IsAO2 n C hL.1
    have htop := (Finset.mem_sdiff.mp ha).1
    have hbound (i : Fin 2) : opnd C a i < n+C.gates.length := by
      have hlt := opnd_lt' hA a (topProps htop).1 i
      have hh := (topProps htop).1
      omega
    exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx =>
      topAnd hA htop b x (orR_mono n C hA x _ _ (orReaches_orR n C _ (hbound b) _ hrb) hx)
        (orR_mono n C hA x _ _ (orReaches_orR n C _ (hbound (1-b)) _ hrd) hx))
  have hsingleton (a : ℕ) (ha : a ∈ A) (b : Fin 2) (hb : Cert a b) :
      ∃ w : Fin n, side C a (1-b) = {w} := by
    obtain ⟨m,hm,hgm,hrm,hrg,⟨w,hw⟩,hs⟩ := hb
    exact ⟨w,mixedForcesCentre G C h4 hE hL hT g hg hv0 hv1 ha hm hgm hrm hrg hw hs⟩
  have hchoose (a : ℕ) (ha : a ∈ A) :
      ∃ w : Fin n, (∃ b : Fin 2, side C a b = {w}) ∧
        ∀ b, Cert a b → side C a (1-b) = {w} := by
    by_cases hh : ∃ b, Cert a b
    · obtain ⟨b,hb⟩ := hh
      obtain ⟨w,hw⟩ := hsingleton a ha b hb
      exact ⟨w,⟨1-b,hw⟩,fun d hd => hneq a ha b d hb hd ▸ hw⟩
    · obtain ⟨b,w,hw⟩ := bothStar G C (AO_of_IsAO2 n C hL.1) h4 ha
      exact ⟨w,⟨b,hw⟩,fun d hd => (hh ⟨d,hd⟩).elim⟩
  let f a := if ha : a ∈ A then (hchoose a ha).choose else v
  have hf (a : ℕ) (ha : a ∈ A) : f a = (hchoose a ha).choose := by
    dsimp only [f]; rw [dite_eq_left ha]
  let K := A.image f
  have hK := coverSelected G C f (fun a ha => by
    rw [hf a ha]; exact (hchoose a ha).choose_spec.1)
  have hKU : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ ∅, z ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨_,w,_,hwe,hc⟩ := residualToward G C h4 hE hL hT g hg he
      rcases hc with ⟨a,ha,_⟩ | ⟨m,hm,hgm,a,ha,b,hrm,hrg,hw,hs⟩
      · have := Finset.card_pos.mpr ⟨a,ha⟩
        omega
      · have hh := (hchoose a ha).choose_spec.2 b ⟨m,hm,hgm,hrm,hrg,⟨w,hw⟩,hs⟩
        rw [hh,Finset.mem_singleton] at hw
        rw [← hf a ha] at hw
        subst w
        exact ⟨f a,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩),hwe⟩
  exact ⟨K,by simpa using coverAssemble G C K ∅ hK hKU,Finset.card_image_le⟩

lemma specialTwoCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C) (h4 : NoFourCycle G) (p q : Fin n)
    (hU : ∀ e ∈ Ustar G C, p ∈ e ∨ q ∈ e)
    (hcan : (∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, side C a b = {p} ∨ side C a b = {q}) ∨
      ∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, side (n := n) C a b ⊆ {p,q}) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card + 1 ∧ p ∈ K ∧ q ∈ K := by
  classical
  let A := tops G C \ centreless G C
  have ex (a : ℕ) (ha : a ∈ A) : ∃ w : Fin n, ∃ b : Fin 2, side C a b = {w} := by
    obtain ⟨b,w,hw⟩ := bothStar G C hA h4 ha
    exact ⟨w,b,hw⟩
  let f a := if ha : a ∈ A then (ex a ha).choose else p
  have hf (a : ℕ) (ha : a ∈ A) : ∃ b : Fin 2, side C a b = {f a} := by
    have he : f a = (ex a ha).choose := by dsimp only [f]; rw [dite_eq_left ha]
    rw [he]
    exact (ex a ha).choose_spec
  obtain ⟨a,ha,b,hb,hmode⟩ : ∃ a ∈ A, ∃ b : Fin 2, side (n := n) C a b ⊆ {p,q} ∧
      ((∃ z ∈ ({p,q} : Finset (Fin n)), side C a b = {z}) ∨ True) := by
    rcases hcan with ⟨a,ha,b,hb | hb⟩ | ⟨a,ha,b,hb⟩
    · exact ⟨a,ha,b,by simp [hb],Or.inr trivial⟩
    · exact ⟨a,ha,b,by simp [hb],Or.inr trivial⟩
    · exact ⟨a,ha,b,hb,Or.inr trivial⟩
  let K := (A.erase a).image f ∪ {p,q}
  have hK : ∀ e ∈ starEdges G C, ∃ z ∈ K, z ∈ e := by
    intro e he
    obtain ⟨d,hd,hcross⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hcross
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
    change u ∈ side C d 0 at hu
    change v ∈ side C d 1 at hv
    have hdA : d ∈ A := by
      refine Finset.mem_sdiff.mpr ⟨hd,fun hc => ?_⟩
      rcases (Finset.mem_filter.mp hc).2 with h | h
      · rw [h] at hu; exact Finset.notMem_empty _ hu
      · rw [h] at hv; exact Finset.notMem_empty _ hv
    by_cases hda : d = a
    · subst d
      fin_cases b
      · exact ⟨u,Finset.mem_union_right _ (hb hu),Sym2.mem_mk_left _ _⟩
      · exact ⟨v,Finset.mem_union_right _ (hb hv),Sym2.mem_mk_right _ _⟩
    · have hfK : f d ∈ K := Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨d,Finset.mem_erase.mpr ⟨hda,hdA⟩,rfl⟩)
      obtain ⟨i,hi⟩ := hf d hdA
      fin_cases i
      · change side C d 0 = {f d} at hi
        rw [hi,Finset.mem_singleton] at hu
        exact ⟨f d,hfK,hu ▸ Sym2.mem_mk_left _ _⟩
      · change side C d 1 = {f d} at hi
        rw [hi,Finset.mem_singleton] at hv
        exact ⟨f d,hfK,hv ▸ Sym2.mem_mk_right _ _⟩
  have hKU : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ ∅, z ∈ e := by
    intro e he
    rcases hU e he with hh | hh
    · exact ⟨p,by simp [K],hh⟩
    · exact ⟨q,by simp [K],hh⟩
  refine ⟨K,by simpa using coverAssemble G C K ∅ hK hKU,?_,by simp [K],by simp [K]⟩
  have hb := (Finset.card_union_le (s := (A.erase a).image f) (t := {p,q})).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_le_two)
  have hcard := Finset.card_erase_add_one ha
  change K.card ≤ A.card + 1
  change K.card ≤ (A.erase a).card + 2 at hb
  omega



lemma residualCases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (p q : Fin n)
    (hp : ∀ w ∈ wmax G C g, w ∈ side C g 0 → w = p)
    (hq : ∀ w ∈ wmax G C g, w ∈ side C g 1 → w = q)
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
    (p ∈ wmax G C g ∩ side C g 0 ∧ ∃ y ∈ side C g 1, e = s(p,y)) ∨
    (q ∈ wmax G C g ∩ side C g 1 ∧ ∃ y ∈ side C g 0, e = s(q,y)) ∨
    ∃ w ∈ wmax G C g, ∃ z ∈ side C g 0 ∩ side C g 1,
      (filterTarget G C g w ∨ ∃ m, mixTarget G C g m w) ∧
      w ∉ side C g 0 ∧ w ∉ side C g 1 ∧ e = s(z,w) := by
  have hsem := (g_semantics G C hL hT g hg).2.2.2.1
  have hc := (thm_1530 n G h4 _ _ _ hsem).2.2.1
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hs,w,hw,hm,hcert⟩ := residualToward G C h4 hE hL hT g hg he
    have step (x y : Fin n) (hxy : G.Adj x y) (hW : x ∈ wmax G C g)
        (s0 : x ∈ side C g 0 ∨ y ∈ side C g 0) (s1 : x ∈ side C g 1 ∨ y ∈ side C g 1)
        (hc' : filterTarget G C g x ∨ ∃ m, mixTarget G C g m x) :
        (p ∈ wmax G C g ∩ side C g 0 ∧ ∃ t ∈ side C g 1, s(x,y) = s(p,t)) ∨
        (q ∈ wmax G C g ∩ side C g 1 ∧ ∃ t ∈ side C g 0, s(x,y) = s(q,t)) ∨
        ∃ z ∈ wmax G C g, ∃ t ∈ side C g 0 ∩ side C g 1,
          (filterTarget G C g z ∨ ∃ m, mixTarget G C g m z) ∧ z ∉ side C g 0 ∧ z ∉ side C g 1 ∧ s(x,y)=s(t,z) := by
      obtain ⟨h0,h1,h2⟩ := hc x y hxy s0 s1 hW
      by_cases hx0 : x ∈ side C g 0
      · obtain rfl := hp x hW hx0
        exact Or.inl ⟨Finset.mem_inter.mpr ⟨hW,hx0⟩,y,h0 hx0,rfl⟩
      by_cases hx1 : x ∈ side C g 1
      · obtain rfl := hq x hW hx1
        exact Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨hW,hx1⟩,y,h1 hx1,rfl⟩)
      exact Or.inr (Or.inr ⟨x,hW,y,h2 hx0 hx1,hc',hx0,hx1,Sym2.eq_swap⟩)
    rcases Sym2.mem_iff.mp hm with h | h
    · subst w
      exact step u v (edgeAdj he) hw (hs 0) (hs 1) hcert
    · subst w
      exact Sym2.eq_swap ▸ step v u (edgeAdj he).symm hw (hs 0).symm (hs 1).symm hcert

-- If the central edge is residual and there is just one mixing gate,
-- a centred top can be covered by the two residual centres instead of its usual centre.
lemma rareMixCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (p q x y : Fin n) (hpW : p ∈ wmax G C g ∩ side C g 0) (hqW : q ∈ wmax G C g ∩ side C g 1)
    (hx : x ∈ side C g 0) (hy : y ∈ side C g 1) (hxp : x ≠ p) (hyq : y ≠ q)
    (hxe : s(q,x) ∈ Ustar G C) (hye : s(p,y) ∈ Ustar G C) (hpq : s(p,q) ∈ Ustar G C)
    (hrep0 : ∀ w ∈ wmax G C g, w ∈ side C g 0 → w = p)
    (hrep1 : ∀ w ∈ wmax G C g, w ∈ side C g 1 → w = q)
    (hcl : (centreless G C).card = 0) (hmc : (mixing G C).card ≤ 1)
    (hU : ∀ e ∈ Ustar G C, p ∈ e ∨ q ∈ e) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card + 1 ∧ p ∈ K ∧ q ∈ K := by
  have hA := AO_of_IsAO2 n C hL.1
  have hps := (Finset.mem_inter.mp hpW).2
  have hqs := (Finset.mem_inter.mp hqW).2
  have hsem := (g_semantics G C hL hT g hg).2.2.2.1
  have cert {a b : Fin n} (he : s(a,b) ∈ Ustar G C)
      (hb : b ∉ wmax G C g) : ∃ m, mixTarget G C g m a := by
    obtain ⟨_,w,hw,hm,hc⟩ := residualToward G C h4 hE hL hT g hg he
    have hwa : w = a := (Sym2.mem_iff.mp hm).resolve_right (fun h => hb (h ▸ hw))
    subst w
    rcases hc with ⟨i,hi,_⟩ | hm
    · have := Finset.card_pos.mpr ⟨i,hi⟩
      omega
    · exact hm
  obtain ⟨m,hm,hgm,a,ha,b,hrm,_,hpb,hpsub⟩ := cert hye (fun h => hyq (hrep1 y h hy))
  obtain ⟨k,hk,_,a',ha',b',hrk,_,hqb,_⟩ := cert hxe (fun h => hxp (hrep0 x h hx))
  have heq := Finset.card_le_one.mp hmc k hk m hm
  subst k
  have hat := (Finset.mem_sdiff.mp ha).1
  have hat' := (Finset.mem_sdiff.mp ha').1
  obtain ⟨u,_,hu⟩ := mixedWitness G C hL hT g hg hat hrm hm hgm
  have hua := hu a hat b hrm
  have hua' := hu a' hat' b' hrk
  have hup := topAdj hA hat b hua hpb
  have huq := topAdj hA hat' b' hua' hqb
  have hux : u ≠ x := fun h => (Finset.mem_sdiff.mp hxe).2
    (reverseEdge (h ▸ crossPair G C hat' hua' hqb))
  have huy : u ≠ y := fun h => (Finset.mem_sdiff.mp hye).2
    (reverseEdge (h ▸ crossPair G C hat hua hpb))
  have hxy : ¬ G.Adj x y := fun h =>
    notTwoCommon h4 hxp hyq.symm (edgeAdj hxe).symm (edgeAdj hpq) h (edgeAdj hye)
  apply specialTwoCover G C hA h4 p q hU
  right
  refine ⟨a,ha,1-b,?_⟩
  intro r hr
  by_cases hrp : r = p
  · simp [hrp]
  by_cases hrq : r = q
  · simp [hrq]
  have hur := topAdj hA hat b hua hr
  rcases (hsem r).mp (hpsub hr) x hx y hy with hh | hh | hh
  · exact (hxy hh).elim
  · exact (notTwoCommon h4 hrq hux hur.symm huq.symm hh.symm (edgeAdj hxe)).elim
  · exact (notTwoCommon h4 hrp huy hur.symm hup.symm hh.symm (edgeAdj hye)).elim



lemma rootWithPad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) (c v : Fin n) (S : Finset (Fin n)) (hv : v ∈ side C g b)
    (hS : S ⊆ side C g b) (hres : ∀ z ∈ S, s(c,z) ∈ Ustar G C)
    (ha : S.Nonempty → G.Adj c v) :
    ∃ P ⊆ (orN G C \ lam G C) \ mixing G C,
      S.card ≤ P.card + (if v ∈ S then 1 else 0) ∧
      ∀ i ∈ P, 1 < (orIn n C (n+i)).card ∧ orIn n C (n+i) ⊆ side C g b := by
  by_cases hn : S.Nonempty
  · let T := insert v S
    have ht : T ⊆ side C g b := Finset.insert_subset hv hS
    have he : ∀ x ∈ T, G.Adj c x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha hn
      · exact edgeAdj (hres x hx)
    obtain ⟨hb,hsub,hsc⟩ := oneRoot G C h4 hL hT g hg b c T ht he (by
      intro x y hx hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr (hres y ((Finset.mem_insert.mp hy).resolve_left (Ne.symm hxy)))
      · exact Or.inl (hres x hx))
    refine ⟨pureBudget C {opnd C g b} T,hsub,?_,fun i hi => ⟨bigBudget C hi,hsc i hi⟩⟩
    by_cases hvm : v ∈ S
    · rw [ite_eq_left hvm]
      have ht' : T = S := Finset.insert_eq_of_mem hvm
      simpa only [ht'] using hb
    · rw [ite_eq_right hvm]
      have ht' : T.card = S.card + 1 := Finset.card_insert_of_notMem hvm
      omega
  · have hS0 := Finset.not_nonempty_iff_eq_empty.mp hn
    refine ⟨∅, by simp, by simp [hS0],by simp⟩

lemma overlapFilter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {v : Fin n}
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) :
    let T := (wmax G C g).filter (fun w => s(v,w) ∈ Ustar G C)
    ∃ P ⊆ (orN G C \ lam G C) \ mixing G C,
      T.card ≤ P.card + (centreless G C).card + (mixing G C).card ∧
      ∀ i ∈ P, 1 < (orIn n C (n+i)).card ∧ orIn n C (n+i) ⊆ wmax G C g := by
  intro T
  have hs := (g_semantics G C hL hT g hg).2.2.2.1
  have hvW := (thm_1529 n G h4 _ _ _ hs).2.2.2.1 v (Finset.mem_inter.mpr ⟨hv0,hv1⟩)
  apply filterBudget G C h4 hE hL hT g hg v T (fun w hw => (Finset.mem_filter.mp hw).2) _ hv0 hv1
  intro w hw
  obtain ⟨_,z,hz,hm,hc⟩ := residualToward G C h4 hE hL hT g hg (Finset.mem_filter.mp hw).2
  rcases Sym2.mem_iff.mp hm with rfl | rfl
  · exact (hvW hz).elim
  · exact hc


open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.CoverPromise

abbrev plane : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun (a b : Fin 26) =>
  ↑a < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑b ∧
    (↑a + (26 : ℕ) - ↑b) % (13 : ℕ) ∈ [(0 : ℕ), 1, 3, 9]

abbrev planeDec : DecidableRel plane.Adj := inferInstance

def lower (i : Fin 13) : Fin 26 := ⟨i.val, by omega⟩
def upper (i : Fin 13) : Fin 26 := ⟨i.val + 13, by omega⟩
def index (v : Fin 26) : Fin 13 := ⟨v.val % 13, by omega⟩
def next (i : Fin 13) : Fin 13 := i + 1

lemma lower_index {v : Fin 26} (hv : v.val < 13) : lower (index v) = v := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hv

lemma upper_index {v : Fin 26} (hv : 13 ≤ v.val) : upper (index v) = v := by
  apply Fin.ext
  change v.val % 13 + 13 = v.val
  omega

lemma index_lower (i : Fin 13) : index (lower i) = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma index_upper (i : Fin 13) : index (upper i) = i := by
  apply Fin.ext
  change (i.val + 13) % 13 = i.val
  omega

lemma matched : ∀ i, plane.Adj (lower i) (upper i) := by decide
lemma shifted : ∀ i, plane.Adj (lower (next i)) (upper i) := by decide

lemma plane_parts {a b : Fin 26} (h : plane.Adj a b) :
    a.val < 13 ∧ 13 ≤ b.val ∨ b.val < 13 ∧ 13 ≤ a.val := by
  rcases h.2 with h | h
  · exact Or.inl ⟨h.1,h.2.1⟩
  · exact Or.inr ⟨h.1,h.2.1⟩

lemma plane_no_triangle {a b c : Fin 26}
    (hab : plane.Adj a b) (hac : plane.Adj a c) (hbc : plane.Adj b c) : False := by
  rcases plane_parts hab with h | h <;>
    rcases plane_parts hac with h' | h' <;>
    rcases plane_parts hbc with h'' | h'' <;> omega

lemma index_image (K : Finset (Fin 26)) (hK : IsVertexCover plane K) :
    K.image index = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  rcases hK _ _ (matched i) with h | h
  · exact Finset.mem_image.mpr ⟨_,h,index_lower i⟩
  · exact Finset.mem_image.mpr ⟨_,h,index_upper i⟩

lemma cover_lower_bound (K : Finset (Fin 26)) (hK : IsVertexCover plane K) : 13 ≤ K.card := by
  have h := Finset.card_image_le (s := K) (f := index)
  simpa only [index_image K hK, Finset.card_univ, Fintype.card_fin] using h

lemma index_injective (K : Finset (Fin 26)) (hK : IsVertexCover plane K) (hc : K.card ≤ 13) :
    Set.InjOn index K := by
  apply Finset.injOn_of_card_image_eq
  rw [index_image K hK, Finset.card_univ, Fintype.card_fin]
  exact (le_antisymm hc (cover_lower_bound K hK)).symm

lemma orbit (a b : Fin 13) : ∃ k : Fin 13, (next^[k.val]) a = b := by
  have hiter (k : ℕ) : (next^[k]) a = a + k • (1 : Fin 13) := by
    induction k with
    | zero => simp
    | succ k ih => simp only [Function.iterate_succ_apply', ih, next, succ_nsmul, add_assoc]
  have hsmul : ∀ x : Fin 13, x.val • (1 : Fin 13) = x := by decide
  refine ⟨b - a, ?_⟩
  rw [hiter, hsmul, add_comm, sub_add_cancel]

-- Matched edges enforce one vertex per matched pair. Shifted edges propagate the side choice.
lemma cover_one_side (K : Finset (Fin 26)) (hK : IsVertexCover plane K)
    (hc : K.card ≤ 13) : ∀ a ∈ K, ∀ b ∈ K, ¬ plane.Adj a b := by
  have hpair (i : Fin 13) (hl : lower i ∈ K) (hr : upper i ∈ K) : False :=
    (show lower i ≠ upper i from by intro e; have := congrArg Fin.val e; simp [lower,upper] at this)
      (index_injective K hK hc hl hr ((index_lower i).trans (index_upper i).symm))
  have hstep (i : Fin 13) (hi : lower i ∈ K) : lower (next i) ∈ K :=
    (hK _ _ (shifted i)).resolve_right (hpair i hi)
  have horbit (i : Fin 13) (hi : lower i ∈ K) (k : ℕ) : lower ((next^[k]) i) ∈ K := by
    induction k with
    | zero => exact hi
    | succ k ih => simpa only [Function.iterate_succ_apply'] using hstep _ ih
  have forbid (a b : Fin 26) (ha : a ∈ K) (hb : b ∈ K)
      (ha' : a.val < 13) (hb' : 13 ≤ b.val) : False := by
    obtain ⟨k,hk⟩ := orbit (index a) (index b)
    have haL : lower (index a) ∈ K := by rwa [lower_index ha']
    have hbU : upper (index b) ∈ K := by rwa [upper_index hb']
    have hl := horbit (index a) haL k.val
    rw [hk] at hl
    exact hpair (index b) hl hbU
  intro a ha b hb hab
  rcases plane_parts hab with h | h
  · exact forbid a b ha hb h.1 h.2
  · exact forbid b a hb ha h.1 h.2

def incidentEdges (v : Fin 26) : Finset (Sym2 (Fin 26)) :=
  (Finset.univ.filter (plane.Adj v)).image fun w => s(v,w)

lemma degree_four : ∀ v, (Finset.univ.filter (plane.Adj v)).card = 4 := by decide

lemma incident_count (v : Fin 26) : (incidentEdges v).card ≤ 4 :=
  Finset.card_image_le.trans (degree_four v).le

lemma incident_mem {v w : Fin 26} (h : plane.Adj v w) : s(v,w) ∈ incidentEdges v :=
  Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩

lemma edge_incident {e : Sym2 (Fin 26)} (he : e ∈ plane.edgeSet) {v : Fin 26} (hv : v ∈ e) :
    e ∈ incidentEdges v := by
  induction e using Sym2.ind with
  | _ a b =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact incident_mem (show plane.Adj v b from he)
    · rw [Sym2.eq_swap]
      exact incident_mem (show plane.Adj a v from he).symm

lemma two_incident_count {a b : Fin 26} (hab : plane.Adj a b) :
    (incidentEdges a ∪ incidentEdges b).card ≤ 7 := by
  have ha := incident_mem hab
  have hb : s(a,b) ∈ incidentEdges b := Sym2.eq_swap ▸ incident_mem hab.symm
  have h := Finset.card_union_add_card_inter (incidentEdges a) (incidentEdges b)
  have hi := Finset.card_pos.mpr ⟨_,Finset.mem_inter.mpr ⟨ha,hb⟩⟩
  have hca := incident_count a
  have hcb := incident_count b
  omega


def residue (i : Fin 4) : ℕ := ([0,1,3,9] : List ℕ).getD i.val 0

lemma residue_cases {x : ℕ} (hx : x ∈ ([0,1,3,9] : List ℕ)) : ∃ i, residue i = x := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

lemma residue_unique (p q r s : Fin 4) (hpq : residue p ≠ residue q)
    (he : (residue p + residue s) % 13 = (residue r + residue q) % 13) :
    residue p = residue r := by
  revert p q r s
  decide

def delta (a b : Fin 26) : ℕ := (a.val + (26 - b.val)) % 13

lemma delta_mem {a b : Fin 26} (h : plane.Adj a b) (ha : a.val < 13) :
    delta a b ∈ ([0,1,3,9] : List ℕ) := by
  rcases h.2 with h | h
  · have he : a.val + (26 - b.val) = a.val + 26 - b.val := by omega
    simpa only [delta,he] using h.2.2
  · exact (Nat.not_le_of_lt ha h.2.1).elim

-- The nonzero differences of the four incidence residues are distinct modulo thirteen.
lemma plane_no_rectangle {a b c d : Fin 26}
    (ha : a.val < 13) (hb : b.val < 13) (hc : 13 ≤ c.val) (hd : 13 ≤ d.val)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : plane.Adj a c) (hbc : plane.Adj b c)
    (had : plane.Adj a d) (hbd : plane.Adj b d) : False := by
  have hne : delta a c ≠ delta b c := by
    intro h
    apply hab
    apply Fin.ext
    unfold delta at h
    omega
  have hmod : (delta a c + delta b d) % 13 = (delta a d + delta b c) % 13 := by
    unfold delta
    simp only [Nat.mod_add_mod,Nat.add_mod_mod]
    congr 1
    omega
  obtain ⟨p,hp⟩ := residue_cases (delta_mem hac ha)
  obtain ⟨q,hq⟩ := residue_cases (delta_mem hbc hb)
  obtain ⟨r,hr⟩ := residue_cases (delta_mem had ha)
  obtain ⟨s,hs⟩ := residue_cases (delta_mem hbd hb)
  rw [← hp,← hq,← hr,← hs] at hmod
  have he := residue_unique p q r s (by simpa only [hp,hq] using hne) hmod
  rw [hp,hr] at he
  apply hcd
  apply Fin.ext
  unfold delta at he
  omega

lemma plane_no_four : NoFourCycle plane := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro c hc d hd
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hc hd
  by_contra hcd
  obtain ⟨hac,hbc⟩ := hc
  obtain ⟨had,hbd⟩ := hd
  have h1 := plane_parts hac
  have h2 := plane_parts hbc
  have h3 := plane_parts had
  by_cases ha : a.val < 13
  · exact plane_no_rectangle ha (by omega) (by omega) (by omega) hab hcd hac hbc had hbd
  · exact plane_no_rectangle (by omega) (by omega) (by omega) (by omega) hcd hab
      hac.symm had.symm hbc.symm hbd.symm


lemma plane_edges_nonempty : plane.edgeFinset.Nonempty :=
  ⟨s(lower 0,upper 0),SimpleGraph.mem_edgeFinset.mpr (matched 0)⟩

lemma residual_one (C : Circuit) (c : Fin 26)
    (h : ∀ e ∈ Ustar plane C, c ∈ e) : (Ustar plane C).card ≤ 4 := by
  apply (Finset.card_le_card (t := incidentEdges c) ?_).trans (incident_count c)
  intro e he
  exact edge_incident (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1) (h e he)

lemma residual_two (C : Circuit) {c d : Fin 26} (hcd : plane.Adj c d)
    (h : ∀ e ∈ Ustar plane C, c ∈ e ∨ d ∈ e) : (Ustar plane C).card ≤ 7 := by
  apply (Finset.card_le_card (t := incidentEdges c ∪ incidentEdges d) ?_).trans (two_incident_count hcd)
  intro e he
  have hadj := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  rcases h e he with hh | hh
  · exact Finset.mem_union_left _ (edge_incident hadj hh)
  · exact Finset.mem_union_right _ (edge_incident hadj hh)

lemma selectCentres (C : Circuit) (hA : AO 26 C) :
    ∃ S : Finset (Fin 26), S.card ≤ (tops plane C \ centreless plane C).card ∧
      ∀ e ∈ starEdges plane C, ∃ z ∈ S, z ∈ e := by
  classical
  let f a := if ha : a ∈ tops plane C \ centreless plane C then
    (bothStar plane C hA plane_no_four ha).choose_spec.choose else 0
  refine ⟨(tops plane C \ centreless plane C).image f,Finset.card_image_le,?_⟩
  apply coverSelected plane C f
  intro a ha
  refine ⟨(bothStar plane C hA plane_no_four ha).choose,?_⟩
  have he : f a = (bothStar plane C hA plane_no_four ha).choose_spec.choose := by
    dsimp only [f]; rw [dite_eq_left ha]
  rw [he]
  exact (bothStar plane C hA plane_no_four ha).choose_spec.choose_spec

lemma singleStarCase (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (hU : (Ustar plane C).Nonempty)
    (c : Fin 26) (b : Fin 2)
    (hs : ∀ e ∈ Ustar plane C, ∃ x ∈ side C g b, e = s(c,x))
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcard : 2 ≤ (Ustar plane C).card) : False := by
  let T := (side (n := 26) C g b).filter fun x => s(c,x) ∈ Ustar plane C
  have he (x : Fin 26) (hx : x ∈ T) := (Finset.mem_filter.mp hx).2
  have hu : (Ustar plane C).card ≤ T.card := by
    apply (Finset.card_le_card (t := T.image fun x => s(c,x)) ?_).trans Finset.card_image_le
    intro e hem
    obtain ⟨x,hx,rfl⟩ := hs e hem
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hem⟩,rfl⟩
  obtain ⟨hc,hsub,_⟩ := oneRoot plane C h4 hL hT g hg b c T
    (Finset.filter_subset _ _) (fun x hx => edgeAdj (he x hx)) (fun x _ hx _ _ => Or.inl (he x hx))
  have hr := residualResourcePositive plane C h4 hE hL hT g hg hU
  have hb := budgetCombine plane C _ hsub
  have ht : (tops plane C \ centreless plane C).card ≤ 12 := by omega
  have hA := AO_of_IsAO2 26 C hL.1
  obtain ⟨S,hS,hcover⟩ := selectCentres C hA
  have hK : IsVertexCover plane (S ∪ {c}) := by
    apply coverAssemble plane C S {c} hcover
    intro e hem
    obtain ⟨x,_,rfl⟩ := hs e hem
    exact ⟨c,Finset.mem_union_right _ (Finset.mem_singleton_self _),Sym2.mem_mk_left _ _⟩
  have hkc : (S ∪ {c}).card ≤ 13 :=
    (Finset.card_union_le _ _).trans (by rw [Finset.card_singleton]; omega)
  have hKls : (S ∪ {c}).card ≤ S.card + 1 := by
    simpa only [Finset.card_singleton] using Finset.card_union_le S {c}
  have ht' := cover_lower_bound _ hK
  have hcs : c ∉ S := by
    intro h
    have hEq : S ∪ {c} = S := Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr h)
    rw [hEq] at ht'
    omega
  -- The added vertex is in the minimum cover, but is absent from the selected centres.
  have hnos (x : Fin 26) (ha : plane.Adj c x) (hstar : s(c,x) ∈ starEdges plane C) : False := by
    obtain ⟨z,hz,hm⟩ := hcover _ hstar
    rcases Sym2.mem_iff.mp hm with rfl | rfl
    · exact hcs hz
    · exact cover_one_side _ hK hkc c (by simp) _ (Finset.mem_union_left _ hz) ha
  by_cases hcl : (centreless plane C).card = 0
  · have mix (x : Fin 26) (hx : x ∈ T) : ∃ m, mixTarget plane C g m x := by
      obtain ⟨_,w,_,hw,hcert⟩ := residualToward plane C h4 hE hL hT g hg (he x hx)
      have hm : ∃ m, mixTarget plane C g m w := hcert.resolve_left (by
        rintro ⟨a,ha,_⟩
        have := Finset.card_pos.mpr ⟨a,ha⟩
        omega)
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · obtain ⟨m,hm,hgm,a,ha,b,hrm,_,hw,_⟩ := hm
        have ha' := (Finset.mem_sdiff.mp ha).1
        obtain ⟨u,_,hu⟩ := mixedWitness plane C hL hT g hg ha' hrm hm hgm
        have huu := hu a ha' b hrm
        exact (hnos u (topAdj hA ha' b huu hw).symm
          (reverseEdge (crossPair plane C ha' huu hw))).elim
      · exact hm
    have htwo : 1 < T.card := by omega
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp htwo
    obtain ⟨m,hm⟩ := mix x hx
    obtain ⟨k,hk⟩ := mix y hy
    have hmk : m ≠ k := by
      rintro rfl
      obtain ⟨hm,hgm,a,ha,b,hrm,_,hx',_⟩ := hm
      obtain ⟨_,_,d,hd,i,hri,_,hy',_⟩ := hk
      have ha' := (Finset.mem_sdiff.mp ha).1
      have hd' := (Finset.mem_sdiff.mp hd).1
      obtain ⟨u,_,hu⟩ := mixedWitness plane C hL hT g hg ha' hrm hm hgm
      have hua := hu a ha' b hrm
      have huc : u ≠ c := fun e => (Finset.mem_sdiff.mp (he x hx)).2
        (e ▸ crossPair plane C ha' hua hx')
      exact notTwoCommon h4 huc hxy (topAdj hA ha' b hua hx') (edgeAdj (he x hx))
        (topAdj hA hd' i (hu d hd' i hri) hy') (edgeAdj (he y hy))
    have hmix := Finset.one_lt_card.mpr ⟨m,hm.1,k,hk.1,hmk⟩
    omega
  · omega
lemma noOverlapCase (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (hU : (Ustar plane C).Nonempty)
    (p q : Fin 26)
    (hp : ∀ w ∈ wmax plane C g, w ∈ side C g 0 → w = p)
    (hq : ∀ w ∈ wmax plane C g, w ∈ side C g 1 → w = q)
    (hd : side (n := 26) C g 0 ∩ side C g 1 = ∅)
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcoverage : 52 ≤ 4 * (tops plane C \ centreless plane C).card + (Ustar plane C).card)
    (hcard : 2 ≤ (Ustar plane C).card) : False := by
  classical
  let E := Ustar plane C
  have hs (e : Sym2 (Fin 26)) (he : e ∈ E) :
      (p ∈ wmax plane C g ∩ side C g 0 ∧ ∃ y ∈ side C g 1, e = s(p,y)) ∨
      (q ∈ wmax plane C g ∩ side C g 1 ∧ ∃ x ∈ side C g 0, e = s(q,x)) := by
    rcases residualCases plane C h4 hE hL hT g hg p q hp hq he with h | h | ⟨_,_,z,hz,_⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (Finset.notMem_empty z (hd ▸ hz)).elim
  by_cases hpAll : ∀ e ∈ E, ∃ y ∈ side C g 1, e = s(p,y)
  · exact singleStarCase C h4 hE hL hT g hg hU p 1 hpAll hbudget hcard
  by_cases hqAll : ∀ e ∈ E, ∃ x ∈ side C g 0, e = s(q,x)
  · exact singleStarCase C h4 hE hL hT g hg hU q 0 hqAll hbudget hcard
  push Not at hpAll hqAll
  obtain ⟨e,he,hno⟩ := hpAll
  obtain ⟨f,hf,hno'⟩ := hqAll
  obtain ⟨hqW,x,hx,rfl⟩ := (hs e he).resolve_left (fun ⟨_,z,hz,heq⟩ => hno z hz heq)
  obtain ⟨hpW,y,hy,rfl⟩ := (hs f hf).resolve_right (fun ⟨_,z,hz,heq⟩ => hno' z hz heq)
  have hps := (Finset.mem_inter.mp hpW).2
  have hqs := (Finset.mem_inter.mp hqW).2
  have hxp : x ≠ p := fun h => hno q hqs (by rw [h,Sym2.eq_swap])
  have hyq : y ≠ q := fun h => hno' p hps (by rw [h,Sym2.eq_swap])
  have hsem := (g_semantics plane C hL hT g hg).2.2.2.1
  have hpfill : ∀ z ∈ side C g 1, plane.Adj p z :=
    (thm_1529 26 plane h4 _ _ _ hsem).1 p (Finset.mem_inter.mp hpW).1 hps |>.2
  have hqfill : ∀ z ∈ side C g 0, plane.Adj q z :=
    (thm_1529 26 plane h4 _ _ _ hsem).2.1 q (Finset.mem_inter.mp hqW).1 hqs |>.2
  let X := (side (n := 26) C g 0).filter fun z => s(q,z) ∈ E ∧ z ≠ p
  let Y := (side (n := 26) C g 1).filter fun z => s(p,z) ∈ E
  let T := insert p X
  let V := insert q Y
  have hxE (z : Fin 26) (hz : z ∈ X) := (Finset.mem_filter.mp hz).2.1
  have hyE (z : Fin 26) (hz : z ∈ Y) := (Finset.mem_filter.mp hz).2
  have hT : T ⊆ side C g 0 := Finset.insert_subset hps (Finset.filter_subset _ _)
  have hV : V ⊆ side C g 1 := Finset.insert_subset hqs (Finset.filter_subset _ _)
  obtain ⟨ht,htsub,htsc⟩ := oneRoot plane C h4 hL ‹TopForm plane C› g hg 0 q T hT
    (fun z hz => hqfill z (hT hz)) (by
      intro u v hu hv hne
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Or.inr (hxE _ ((Finset.mem_insert.mp hv).resolve_left (Ne.symm hne)))
      · exact Or.inl (hxE _ hu))
  obtain ⟨hv,hvsub,hvsc⟩ := oneRoot plane C h4 hL ‹TopForm plane C› g hg 1 p V hV
    (fun z hz => hpfill z (hV hz)) (by
      intro u v hu hv hne
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Or.inr (hyE _ ((Finset.mem_insert.mp hv).resolve_left (Ne.symm hne)))
      · exact Or.inl (hyE _ hu))
  have hid : (side (n := 26) C g 0 ∩ side C g 1).card ≤ 1 := by simp [hd]
  have hdisj := scopedDisjoint C hid htsc hvsc
  have hsum := budgetCombine plane C _ (Finset.union_subset htsub hvsub)
  rw [Finset.card_union_of_disjoint hdisj] at hsum
  have hpc : T.card = X.card + 1 :=
    Finset.card_insert_of_notMem (fun hh => (Finset.mem_filter.mp hh).2.2 rfl)
  rw [hpc] at ht
  have hyV : Y.card ≤ V.card := Finset.card_le_card (Finset.subset_insert q Y)
  have hcount : E.card ≤ X.card + Y.card := by
    apply (Finset.card_le_card (show E ⊆ (X.image fun z => s(q,z)) ∪ (Y.image fun z => s(p,z)) from ?_)).trans
      (Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
    intro e he
    rcases hs e he with ⟨_,z,hz,rfl⟩ | ⟨_,z,hz,rfl⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,he⟩,rfl⟩)
    · by_cases hzp : z = p
      · subst z
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨q,Finset.mem_filter.mpr ⟨hqs,reverseEdge he⟩,Sym2.eq_swap⟩)
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨z,Finset.mem_filter.mpr ⟨hz,he,hzp⟩,rfl⟩)
  have hcv (e : Sym2 (Fin 26)) (he : e ∈ E) : p ∈ e ∨ q ∈ e := by
    rcases hs e he with ⟨_,z,_,rfl⟩ | ⟨_,z,_,rfl⟩
    · exact Or.inl (Sym2.mem_mk_left _ _)
    · exact Or.inr (Sym2.mem_mk_left _ _)

  have hpq := hpfill q hqs
  have hu7 := residual_two C hpq hcv
  change 52 ≤ 4 * (tops plane C \ centreless plane C).card + E.card at hcoverage
  have ht12 : 12 ≤ (tops plane C \ centreless plane C).card := by
    change E.card ≤ 7 at hu7
    omega
  have hpos := residualResourcePositive plane C h4 hE hL ‹TopForm plane C› g hg hU
  -- With the central edge present, the only remaining budget allows one mixing gate.
  by_cases hcen : s(p,q) ∈ E
  · have hsmall : 2 * (centreless plane C).card + (mixing plane C).card ≤ 1 := by
      change (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
        (orN plane C \ lam plane C).card ≤ 12 + E.card at hbudget
      omega
    have hzero : (centreless plane C).card = 0 := by omega
    have hm : (mixing plane C).card ≤ 1 := by omega
    obtain ⟨K,hK,hKc,hpK,hqK⟩ := rareMixCover plane C h4 hE hL ‹TopForm plane C› g hg p q x y hpW hqW
      hx hy hxp hyq he hf hcen hp hq hzero hm hcv
    have hkc : K.card ≤ 13 := by
      change 52 ≤ 4 * (tops plane C \ centreless plane C).card + E.card at hcoverage
      change (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
        (orN plane C \ lam plane C).card ≤ 12 + E.card at hbudget
      omega
    exact cover_one_side K hK hkc p hpK q hqK hpq
  · have hvc : V.card = Y.card + 1 :=
      Finset.card_insert_of_notMem (fun hh => hcen (hyE q hh))
    rw [hvc] at hv
    change (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + E.card at hbudget
    omega

lemma overlapSmallSide (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (v : Fin 26)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) (b : Fin 2) (hb : side C g b = {v})
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcoverage : 52 ≤ 4 * (tops plane C \ centreless plane C).card + (Ustar plane C).card)
    (hcard : 2 ≤ (Ustar plane C).card) : False := by
  let T := (wmax plane C g).filter (fun w => s(v,w) ∈ Ustar plane C)
  have hs := (g_semantics plane C hL hT g hg).2.2.2.1
  have hvW := (thm_1529 26 plane h4 _ _ _ hs).2.2.2.1 v (Finset.mem_inter.mpr ⟨hv0,hv1⟩)
  have hsplit (e : Sym2 (Fin 26)) (he : e ∈ Ustar plane C) : ∃ w ∈ T, e = s(v,w) := by
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hh,w,hw,hm,_⟩ := residualToward plane C h4 hE hL hT g hg he
      have ht := hh b
      rw [hb,Finset.mem_singleton,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · have hwy := (Sym2.mem_iff.mp hm).resolve_left (fun h => hvW (h ▸ hw))
        subst w
        exact ⟨y,Finset.mem_filter.mpr ⟨hw,he⟩,rfl⟩
      · have hwx := (Sym2.mem_iff.mp hm).resolve_right (fun h => hvW (h ▸ hw))
        subst w
        exact ⟨x,Finset.mem_filter.mpr ⟨hw,reverseEdge he⟩,Sym2.eq_swap⟩
  have hc : (Ustar plane C).card ≤ T.card := (Finset.card_le_card
    (show Ustar plane C ⊆ T.image (fun w => s(v,w)) from by
      intro e he
      obtain ⟨w,hw,rfl⟩ := hsplit e he
      exact Finset.mem_image.mpr ⟨w,hw,rfl⟩)).trans Finset.card_image_le
  obtain ⟨P,hP,hcard,_⟩ := overlapFilter plane C h4 hE hL hT g hg hv0 hv1
  change T.card ≤ _ at hcard
  have hsum := budgetCombine plane C P hP

  have hu4 := residual_one C v (fun e he => by
    obtain ⟨_,_,rfl⟩ := hsplit e he
    exact Sym2.mem_mk_left _ _)
  by_cases hcl : (centreless plane C).card = 0
  · obtain ⟨K,hK,hKc⟩ := witnessSelected plane C h4 hE hL hT g hg v hv0 hv1 hcl
    have hkc := cover_lower_bound K hK
    omega
  · omega

lemma overlapSingleton (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (v p q : Fin 26)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1)
    (hv : side (n := 26) C g 0 ∩ side C g 1 = {v})
    (hp : ∀ w ∈ wmax plane C g, w ∈ side C g 0 → w = p)
    (hq : ∀ w ∈ wmax plane C g, w ∈ side C g 1 → w = q)
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcoverage : 52 ≤ 4 * (tops plane C \ centreless plane C).card + (Ustar plane C).card)
    (_hcard : 2 ≤ (Ustar plane C).card) : False := by
  classical
  let A := side (n := 26) C g 0
  let B := side (n := 26) C g 1
  let E := Ustar plane C
  let W' := wmax plane C g
  let T := W'.filter (fun w => s(v,w) ∈ E)
  let Z := T.filter (fun w => w ∉ A ∧ w ∉ B)
  let X := A.filter (fun x => s(q,x) ∈ E ∧ q ∈ W' ∩ B ∧ ¬(p ∈ W' ∩ A ∧ x = p))
  let Y := B.filter (fun y => s(p,y) ∈ E ∧ p ∈ W' ∩ A)
  have hsem := (g_semantics plane C hL hT g hg).2.2.2.1
  have hi := thm_1529 26 plane h4 _ _ _ hsem
  have hvA : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨hv0,hv1⟩
  have hvW : v ∉ W' := hi.2.2.2.1 v hvA
  have hcommon : ∀ w ∈ W', plane.Adj v w := hi.2.2.1 v hvA
  have hI : (A ∩ B).card ≤ 1 := by change (side (n := 26) C g 0 ∩ side C g 1).card ≤ 1; simp [hv]
  have hwq : (W' ∩ B).card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    (hq x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2).trans
      (hq y (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2).symm)
  have hwp : (W' ∩ A).card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    (hp x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2).trans
      (hp y (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2).symm)
  have hcases (e : Sym2 (Fin 26)) (he : e ∈ E) :
      (∃ x ∈ X, e = s(q,x)) ∨ (∃ y ∈ Y, e = s(p,y)) ∨ (∃ w ∈ Z, e = s(v,w)) := by
    rcases residualCases plane C h4 hE hL hT g hg p q hp hq he with
      ⟨hpW,y,hy,rfl⟩ | ⟨hqW,x,hx,rfl⟩ | ⟨w,hw,t,ht,_,hwA,hwB,rfl⟩
    · exact Or.inr (Or.inl ⟨y,Finset.mem_filter.mpr ⟨hy,he,hpW⟩,rfl⟩)
    · by_cases ht : p ∈ W' ∩ A ∧ x = p
      · rcases ht with ⟨hpW,rfl⟩
        exact Or.inr (Or.inl ⟨q,Finset.mem_filter.mpr
          ⟨(Finset.mem_inter.mp hqW).2,reverseEdge he,hpW⟩,Sym2.eq_swap⟩)
      · exact Or.inl ⟨x,Finset.mem_filter.mpr ⟨hx,he,hqW,ht⟩,rfl⟩
    · rw [hv,Finset.mem_singleton] at ht
      subst t
      exact Or.inr (Or.inr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw,he⟩,hwA,hwB⟩,rfl⟩)
  have hX (x : Fin 26) (hx : x ∈ X) := (Finset.mem_filter.mp hx).2
  have hY (y : Fin 26) (hy : y ∈ Y) := (Finset.mem_filter.mp hy).2
  have hpic (h : p ∈ W' ∩ A) : p ∈ T → p ∉ Z := fun _ hz => (Finset.mem_filter.mp hz).2.1 (Finset.mem_inter.mp h).2
  have hqic (h : q ∈ W' ∩ B) : q ∈ T → q ∉ Z := fun _ hz => (Finset.mem_filter.mp hz).2.2 (Finset.mem_inter.mp h).2
  have hsumT : Z.card + (if v ∈ X then 1 else 0) + (if v ∈ Y then 1 else 0) ≤ T.card := by
    have hpT (hy : v ∈ Y) : p ∈ T :=
      Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hY v hy).2).1,reverseEdge (hY v hy).1⟩
    have hqT (hx : v ∈ X) : q ∈ T :=
      Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hX v hx).2.1).1,reverseEdge (hX v hx).1⟩
    have hzT : Z ⊆ T := Finset.filter_subset _ _
    by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp only [hx,hy,ite_true,ite_false,Nat.add_zero]
    · have hpZ := hpic (hY v hy).2 (hpT hy)
      have hqZ := hqic (hX v hx).2.1 (hqT hx)
      have hpq : p ≠ q := by
        intro h
        have hpB := (Finset.mem_inter.mp (hX v hx).2.1).2
        rw [← h] at hpB
        have hh : p ∈ A ∩ B := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hY v hy).2).2,hpB⟩
        rw [hv,Finset.mem_singleton] at hh
        exact hvW (hh ▸ (Finset.mem_inter.mp (hY v hy).2).1)
      have hh : insert p (insert q Z) ⊆ T := Finset.insert_subset (hpT hy) (Finset.insert_subset (hqT hx) hzT)
      have hc := Finset.card_le_card hh
      rw [Finset.card_insert_of_notMem (by simp [hpq,hpZ]),Finset.card_insert_of_notMem hqZ] at hc
      exact hc
    · have hh := Finset.card_le_card (Finset.insert_subset (hqT hx) hzT)
      rwa [Finset.card_insert_of_notMem (hqic (hX v hx).2.1 (hqT hx))] at hh
    · have hh := Finset.card_le_card (Finset.insert_subset (hpT hy) hzT)
      rwa [Finset.card_insert_of_notMem (hpic (hY v hy).2 (hpT hy))] at hh
    · exact Finset.card_le_card hzT
  have hcount : E.card ≤ X.card + Y.card + Z.card := by
    refine (Finset.card_le_card (show E ⊆
      ((X.image fun x => s(q,x)) ∪ (Y.image fun y => s(p,y))) ∪ (Z.image fun w => s(v,w)) from ?_)).trans ?_
    · intro e he
      rcases hcases e he with ⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩ | ⟨w,hw,rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    · exact Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add
        (Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
        Finset.card_image_le)
  obtain ⟨D,hD,hDc,hDs⟩ := rootWithPad plane C h4 hL hT g hg 0 q v X hv0
    (Finset.filter_subset _ _) (fun x hx => (hX x hx).1)
    (fun ⟨x,hx⟩ => (hcommon q (Finset.mem_inter.mp (hX x hx).2.1).1).symm)
  obtain ⟨F,hF,hFc,hFs⟩ := rootWithPad plane C h4 hL hT g hg 1 p v Y hv1
    (Finset.filter_subset _ _) (fun y hy => (hY y hy).1)
    (fun ⟨y,hy⟩ => (hcommon p (Finset.mem_inter.mp (hY y hy).2).1).symm)
  obtain ⟨L,hLp,hLc,hLs⟩ := overlapFilter plane C h4 hE hL hT g hg hv0 hv1
  change T.card ≤ _ at hLc
  have hdis (S R : Finset ℕ) (a b : Finset (Fin 26)) (hs : (a ∩ b).card ≤ 1)
      (hp : ∀ i ∈ S, 1 < (orIn 26 C (26+i)).card ∧ orIn 26 C (26+i) ⊆ a)
      (hq : ∀ i ∈ R, orIn 26 C (26+i) ⊆ b) : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Nat.not_le_of_lt (hp i hi).1)
      ((Finset.card_le_card (Finset.subset_inter (hp i hi).2 (hq i hj))).trans hs)
  have df := hdis D F A B hI hDs (fun i hi => (hFs i hi).2)
  have dl := hdis D L A W' (by simpa [Finset.inter_comm] using hwp) hDs (fun i hi => (hLs i hi).2)
  have fl := hdis F L B W' (by simpa [Finset.inter_comm] using hwq) hFs (fun i hi => (hLs i hi).2)
  have hcards := budgetCombine plane C _ (Finset.union_subset (Finset.union_subset hD hF) hLp)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dl,fl⟩),
    Finset.card_union_of_disjoint df] at hcards
  have hbound : E.card ≤ (orN plane C \ lam plane C).card + (centreless plane C).card := by omega

  have hvp (hpW : p ∈ W' ∩ A) : plane.Adj v p := hcommon p (Finset.mem_inter.mp hpW).1
  have hvq (hqW : q ∈ W' ∩ B) : plane.Adj v q := hcommon q (Finset.mem_inter.mp hqW).1
  have hexcl (hx : X.Nonempty) (hy : Y.Nonempty) : False := by
    obtain ⟨x,hx⟩ := hx
    obtain ⟨y,hy⟩ := hy
    have hpW := (hY y hy).2
    have hqW := (hX x hx).2.1
    have hpq := (hi.1 p (Finset.mem_inter.mp hpW).1 (Finset.mem_inter.mp hpW).2).2
      q (Finset.mem_inter.mp hqW).2
    exact plane_no_triangle (hvp hpW) (hvq hqW) hpq
  have hu7 : E.card ≤ 7 := by
    by_cases hx : X.Nonempty
    · obtain ⟨x,hx'⟩ := hx
      apply residual_two C (hvq (hX x hx').2.1)
      intro e he
      rcases hcases e he with ⟨_,_,rfl⟩ | ⟨y,hy,_⟩ | ⟨_,_,rfl⟩
      · exact Or.inr (Sym2.mem_mk_left _ _)
      · exact (hexcl ⟨x,hx'⟩ ⟨y,hy⟩).elim
      · exact Or.inl (Sym2.mem_mk_left _ _)
    by_cases hy : Y.Nonempty
    · obtain ⟨y,hy'⟩ := hy
      apply residual_two C (hvp (hY y hy').2)
      intro e he
      rcases hcases e he with ⟨x,hx',_⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩
      · exact (hx ⟨x,hx'⟩).elim
      · exact Or.inr (Sym2.mem_mk_left _ _)
      · exact Or.inl (Sym2.mem_mk_left _ _)
    apply (residual_one C v ?_).trans (by decide)
    intro e he
    rcases hcases e he with ⟨x,hx',_⟩ | ⟨y,hy',_⟩ | ⟨_,_,rfl⟩
    · exact (hx ⟨x,hx'⟩).elim
    · exact (hy ⟨y,hy'⟩).elim
    · exact Sym2.mem_mk_left _ _
  change (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
    (orN plane C \ lam plane C).card ≤ 12 + E.card at hbudget
  change 52 ≤ 4 * (tops plane C \ centreless plane C).card + E.card at hcoverage
  by_cases hcl : (centreless plane C).card = 0
  · obtain ⟨K,hK,hKc⟩ := witnessSelected plane C h4 hE hL hT g hg v hv0 hv1 hcl
    have hkc := cover_lower_bound K hK
    omega
  · omega

lemma largeOverlap (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (hU : (Ustar plane C).Nonempty)
    (hI : 2 ≤ (side (n := 26) C g 0 ∩ side C g 1).card)
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcard : 2 ≤ (Ustar plane C).card) : False := by
  have hs := (g_semantics plane C hL hT g hg).2.2.2.1
  have hl := (thm_1529 26 plane h4 _ _ _ hs).2.2.2.2 hI
  obtain ⟨w,hw⟩ : (wmax plane C g).Nonempty := by
    obtain ⟨e,he⟩ := hU
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨_,w,hw,_,_⟩ := residualToward plane C h4 hE hL hT g hg he
      exact ⟨w,hw⟩
  have hu (x : Fin 26) (hx : x ∈ wmax plane C g) : x = w := Finset.card_le_one.mp hl x hx w hw
  have hrep (e : Sym2 (Fin 26)) (he : e ∈ Ustar plane C) :=
    residualCases plane C h4 hE hL hT g hg w w (fun x hx _ => hu x hx) (fun x hx _ => hu x hx) he
  by_cases hw0 : w ∈ side C g 0
  · apply singleStarCase C h4 hE hL hT g hg hU w 1 ?_ hbudget hcard
    intro e he
    rcases hrep e he with ⟨_,x,hx,rr⟩ | ⟨hm,_⟩ | ⟨u,hU',_,_,_,hn,_,_⟩
    · exact ⟨x,hx,rr⟩
    · exact ((thm_1529 26 plane h4 _ _ _ hs).1 w hw hw0).1 (Finset.mem_inter.mp hm).2 |>.elim
    · exact (hn ((hu u hU').symm ▸ hw0)).elim
  · apply singleStarCase C h4 hE hL hT g hg hU w 0 ?_ hbudget hcard
    intro e he
    rcases hrep e he with ⟨hm,_⟩ | ⟨_,x,hx,rr⟩ | ⟨u,hU',x,hx,_,_,_,rr⟩
    · exact (hw0 (Finset.mem_inter.mp hm).2).elim
    · exact ⟨x,hx,rr⟩
    · exact ⟨x,(Finset.mem_inter.mp hx).1,by simpa only [hu u hU'] using rr.trans Sym2.eq_swap⟩

lemma thinSide (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (hU : (Ustar plane C).Nonempty)
    (b : Fin 2) (v : Fin 26) (hv : side C g b = {v})
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcoverage : 52 ≤ 4 * (tops plane C \ centreless plane C).card + (Ustar plane C).card)
    (hcard : 2 ≤ (Ustar plane C).card) : False := by
  by_cases hv' : v ∈ side C g (1-b)
  · have hvs : v ∈ side C g b := by simp [hv]
    rcases M1528.P2.fin2_both (fun d => v ∈ side C g d) b hvs hv' with ⟨h0,h1⟩
    exact overlapSmallSide C h4 hE hL hT g hg v h0 h1 b hv hbudget hcoverage hcard
  · apply singleStarCase C h4 hE hL hT g hg hU v (1-b) ?_ hbudget hcard
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hs,_⟩ := residualToward plane C h4 hE hL hT g hg he
      have hh := hs b
      rw [hv,Finset.mem_singleton,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact ⟨y,(hs (1-b)).resolve_left hv',rfl⟩
      · exact ⟨x,(hs (1-b)).resolve_right hv',Sym2.eq_swap⟩

lemma finalCover (C : Circuit)
    (h4 : NoFourCycle plane) (hE : plane.edgeFinset.Nonempty) (hL : IsLeastAO plane C)
    (hT : TopForm plane C) (g : ℕ) (hg : junk plane C = {g}) (hU : (Ustar plane C).Nonempty)
    (hbudget : (tops plane C \ centreless plane C).card + 2 * (centreless plane C).card +
      (orN plane C \ lam plane C).card ≤ 12 + (Ustar plane C).card)
    (hcoverage : 52 ≤ 4 * (tops plane C \ centreless plane C).card + (Ustar plane C).card)
    (hcard : 2 ≤ (Ustar plane C).card) : False := by
  classical
  obtain ⟨hP,hQ,_,hW,_⟩ := g_semantics plane C hL hT g hg
  by_cases hP' : (side (n := 26) C g 0).card ≤ 1
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (le_antisymm hP' (Finset.card_pos.mpr hP))
    exact thinSide C h4 hE hL hT g hg hU 0 p hp hbudget hcoverage hcard
  by_cases hQ' : (side (n := 26) C g 1).card ≤ 1
  · obtain ⟨q,hq⟩ := Finset.card_eq_one.mp (le_antisymm hQ' (Finset.card_pos.mpr hQ))
    exact thinSide C h4 hE hL hT g hg hU 1 q hq hbudget hcoverage hcard
  let I := side (n := 26) C g 0 ∩ side C g 1
  by_cases hBig : 2 ≤ I.card
  · exact largeOverlap C h4 hE hL hT g hg hU hBig hbudget hcard
  obtain ⟨fallback,_⟩ := hP
  have hCard := thm_1530 26 plane h4 _ _ _ hW
  have rep (b : Fin 2) (h : (wmax plane C g ∩ side C g b).card ≤ 1) :
      ∃ z : Fin 26, ∀ w ∈ wmax plane C g, w ∈ side C g b → w = z := by
    by_cases hn : (wmax plane C g ∩ side C g b).Nonempty
    · obtain ⟨z,hz⟩ := hn
      exact ⟨z,fun w hw hs => Finset.card_le_one.mp h w (Finset.mem_inter.mpr ⟨hw,hs⟩) z hz⟩
    · exact ⟨fallback,fun w hw hs => (hn ⟨w,Finset.mem_inter.mpr ⟨hw,hs⟩⟩).elim⟩
  obtain ⟨p,hp⟩ := rep 0 (hCard.1 (by omega))
  obtain ⟨q,hq⟩ := rep 1 (hCard.2.1 (by omega))
  by_cases hne : I.Nonempty
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (le_antisymm (by omega) (Finset.card_pos.mpr hne))
    have hvm : v ∈ I := by rw [hv]; simp
    exact overlapSingleton C h4 hE hL hT g hg v p q
      (Finset.mem_inter.mp hvm).1 (Finset.mem_inter.mp hvm).2 hv hp hq hbudget hcoverage hcard
  · exact noOverlapCase C h4 hE hL hT g hg hU p q hp hq (Finset.not_nonempty_iff_eq_empty.mp hne) hbudget hcoverage hcard

end Close
end PEqualNP.Outside.L_meta_7249

theorem PEqualNP.Outside.L_meta_7249 :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   (x1 = SimpleGraph.fromRel fun (x5 x6 : Fin (26 : ℕ)) => ↑x5 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x6 ∧ (↑x5 + (26 : ℕ) - ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size ≤ (64 : ℕ) →           PEqualNP.TopForm.junk x1 x3 = {x4} →             have x10 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;             have x11 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x12 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             (x10 \ x11).card + (2 : ℕ) * x11.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ (12 : ℕ) + x12.card → (52 : ℕ) ≤ (4 : ℕ) * (x10 \ x11).card + x12.card → (2 : ℕ) ≤ x12.card → False := by
  intro G d C g hgraph hL hT _ hg
  dsimp only
  intro hbudget hcoverage hcard
  change G = PEqualNP.Outside.L_meta_7249.Close.plane at hgraph
  subst G
  have hd : d = PEqualNP.Outside.L_meta_7249.Close.planeDec := Subsingleton.elim _ _
  subst d
  exact PEqualNP.Outside.L_meta_7249.Close.finalCover C
    PEqualNP.Outside.L_meta_7249.Close.plane_no_four
    PEqualNP.Outside.L_meta_7249.Close.plane_edges_nonempty hL hT g hg
    (Finset.card_pos.mp (by omega)) hbudget hcoverage hcard
