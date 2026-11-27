import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2856_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Basic wire identities follow the argument in L-meta-2051.
def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

abbrev value {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool := val C.gates w z

lemma gateAt_eq_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj

lemma gateValue {n : ℕ} (C : Circuit) (rb : ReadsBack n C)
    (z : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C z (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => value C z i) := by
  have h := gate_val C.gates (List.ofFn z) j hj
  simp only [List.length_ofFn] at h
  change value C z (n + j) = _ at h
  rw [h, gateAt_eq_get C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hh := rb j hj i (by simpa only [gateAt_eq_get C j hj] using hi)
  have hh' : i < (List.ofFn z).length + j := by simpa using hh
  exact (wire_take C.gates (List.ofFn z) j i hh' hj.le).symm

lemma inputValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (i : Fin n) :
    value C z i.val = z i := val_input C.gates z i.val i.isLt

lemma andOr {C : Circuit} (mono : Monotone2 C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
  rw [gateAt_eq_get C j hj]
  simpa using (mono C.gates[j] (List.getElem_mem hj)).1

lemma evalIncreasing (op : GateOp) (hop : op = .and ∨ op = .or)
    (ins : List ℕ) (a b : ℕ → Bool) (h : ∀ i ∈ ins, a i = true → b i = true) :
    op.eval (ins.map a) = true → op.eval (ins.map b) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun ha i hi => h i hi (ha i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, h i hi ha⟩

lemma valueIncreasing {n : ℕ} (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack n C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    ∀ i, value C x i = true → value C y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < n
    · exact inputValue C x ⟨i, hi⟩ ▸ inputValue C y ⟨i, hi⟩ ▸ h ⟨i, hi⟩
    by_cases hb : n + C.gates.length ≤ i
    · have vx : value C x i = false := val_big C.gates x i hb
      simp [vx]
    obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [gateValue C rb x j hj, gateValue C rb y j hj]
    exact evalIncreasing _ (andOr mono j hj) _ _ _ (fun k hk => ih k (rb j hj k hk))

def reindex (n i : ℕ) : ℕ := if i < n then i else n + 3 * (i - n) + 2

lemma reindex_input {n i : ℕ} (hi : i < n) : reindex n i = i := by simp [reindex, hi]

lemma reindex_gate (n j : ℕ) : reindex n (n + j) = n + 3*j + 2 := by
  simp [reindex]

lemma reindex_lt {n j i : ℕ} (h : i < n + j) : reindex n i < n + 3*j := by
  unfold reindex
  split <;> omega

def pad : Gate := ⟨.or, []⟩

def remap (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (reindex n)⟩

def assemble (n k : ℕ) (blocks : ℕ → Fin 3 → Gate) (out : ℕ) : Circuit :=
  ⟨List.ofFn (fun i : Fin (3*k) => blocks (i.val / 3) ⟨Nat.mod i.val 3, Nat.mod_lt _ (by decide)⟩),
    reindex n out⟩

@[local simp] lemma assemble_length (n k : ℕ) (blocks : ℕ → Fin 3 → Gate) (out : ℕ) :
    (assemble n k blocks out).gates.length = 3*k := by simp [assemble]

lemma assemble_gate (n k : ℕ) (blocks : ℕ → Fin 3 → Gate) (out j : ℕ) (t : Fin 3) (hj : j < k) :
    gateAt (assemble n k blocks out) (3*j + t.val) = blocks j t := by
  have ht := t.isLt
  have hidx : 3*j + t.val < (assemble n k blocks out).gates.length := by simp; omega
  rw [gateAt_eq_get _ _ hidx]
  let f (i : Fin (3*k)) := blocks (i.val / 3) ⟨Nat.mod i.val 3, Nat.mod_lt _ (by decide)⟩
  have hbound : 3*j+t.val < (List.ofFn f).length := by simp; omega
  have eq : (List.ofFn f)[3*j+t.val]'hbound = blocks j t := by
    rw [List.getElem_ofFn]
    have hd : (3*j + t.val) / 3 = j := by omega
    have hm : (⟨Nat.mod (3*j + t.val) 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = t := by
      apply Fin.ext
      change (3*j+t.val) % 3 = t.val
      omega
    exact congrArg₂ blocks hd hm
  exact eq

lemma assemble_wf {n k : ℕ} (blocks : ℕ → Fin 3 → Gate) (out : ℕ)
    (ok : ∀ j < k, ∀ t : Fin 3,
      (blocks j t).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (blocks j t).inputs.length ≤ 2 ∧ ∀ i ∈ (blocks j t).inputs, i < n + 3*j + t.val) :
    Monotone2 (assemble n k blocks out) ∧ ReadsBack n (assemble n k blocks out) := by
  let D := assemble n k blocks out
  have splitIndex (i : ℕ) (hi : i < D.gates.length) :
      ∃ j < k, ∃ t : Fin 3, i = 3*j + t.val ∧ gateAt D i = blocks j t := by
    have hi' : i < 3*k := by simpa [D] using hi
    let t : Fin 3 := ⟨Nat.mod i 3, Nat.mod_lt _ (by decide)⟩
    have hi2 : i = 3*(i/3) + t.val := by
      change i = 3*(i/3) + i % 3
      omega
    refine ⟨i/3, by omega, t, hi2, ?_⟩
    calc
      gateAt D i = gateAt D (3*(i/3) + t.val) := congrArg (gateAt D) hi2
      _ = blocks (i/3) t := assemble_gate _ _ _ _ _ t (by omega)
  constructor
  · intro g hg
    obtain ⟨i, hi, hg'⟩ := List.mem_iff_getElem.mp hg
    have eq : gateAt D i = g := (gateAt_eq_get D i hi).trans hg'
    obtain ⟨j, hj, t, -, hgt⟩ := splitIndex i hi
    rw [← eq, hgt]
    exact ⟨(ok j hj t).1, (ok j hj t).2.1⟩
  · intro i hi a ha
    obtain ⟨j, hj, t, eq, hgt⟩ := splitIndex i hi
    rw [eq]
    simpa only [Nat.add_assoc] using (ok j hj t).2.2 a (hgt ▸ ha)

def coord {N : ℕ} (right : Bool) (i : Fin N) : Fin (N+N) :=
  if right then Fin.natAdd N i else Fin.castAdd N i

def raw {N : ℕ} (right : Bool) (i : Fin N) : ℕ := (coord right i).val

@[local simp] lemma raw_left {N : ℕ} (i : Fin N) : raw false i = i.val := rfl
@[local simp] lemma raw_right {N : ℕ} (i : Fin N) : raw true i = N+i.val := rfl

lemma raw_lt {N : ℕ} (right : Bool) (i : Fin N) : raw right i < N+N :=
  (coord right i).isLt

def smallLeft (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  w < N ∨ (N+N ≤ w ∧ (gateAt C (w-(N+N))).op = .or ∧
    ∃ a b : ℕ, (gateAt C (w-(N+N))).inputs = [a,b] ∧ a<N ∧ b<N)

def smallRight (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  (N ≤ w ∧ w < N+N) ∨ (N+N ≤ w ∧ (gateAt C (w-(N+N))).op = .or ∧
    ∃ a b : ℕ, (gateAt C (w-(N+N))).inputs = [a,b] ∧
      N≤a ∧ a<N+N ∧ N≤b ∧ b<N+N)

def side (N : ℕ) (C : Circuit) (right : Bool) (w : ℕ) (a b : Fin N) : Prop :=
  (w = raw right a ∧ b = a) ∨
    ∃ j < C.gates.length, w = N+N+j ∧ (gateAt C j).op = .or ∧
      (gateAt C j).inputs = [raw right a, raw right b]

lemma sideLeft {N : ℕ} {C : Circuit} {w : ℕ}
    (hw : w < N+N+C.gates.length) (h : smallLeft N C w) :
    ∃ a b : Fin N, side N C false w a b := by
  rcases h with h | ⟨hN, hop, a, b, harg, ha, hb⟩
  · exact ⟨⟨w,h⟩, ⟨w,h⟩, Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨⟨a,ha⟩, ⟨b,hb⟩, Or.inr ⟨w-(N+N), by omega, by omega, hop, harg⟩⟩

lemma sideRight {N : ℕ} {C : Circuit} {w : ℕ}
    (hw : w < N+N+C.gates.length) (h : smallRight N C w) :
    ∃ a b : Fin N, side N C true w a b := by
  rcases h with ⟨hle,hlt⟩ | ⟨hN, hop, a, b, harg, hal, har, hbl, hbr⟩
  · let a : Fin N := ⟨w-N, by omega⟩
    exact ⟨a, a, Or.inl ⟨by simp [a]; omega, rfl⟩⟩
  · let A : Fin N := ⟨a-N, by omega⟩
    let B : Fin N := ⟨b-N, by omega⟩
    have eA : raw true A = a := by simp [A]; omega
    have eB : raw true B = b := by simp [B]; omega
    exact ⟨A, B, Or.inr ⟨w-(N+N), by omega, by omega, hop, by rwa [eA,eB]⟩⟩

abbrev SideInputs (N : ℕ) := ℕ × Fin N × Fin N
abbrev Rectangle (N : ℕ) := SideInputs N × SideInputs N

def rectAt (N : ℕ) (C : Circuit) (j : ℕ) (r : Rectangle N) : Prop :=
  (gateAt C j).op = .and ∧
    ((gateAt C j).inputs = [r.1.1,r.2.1] ∨ (gateAt C j).inputs = [r.2.1,r.1.1]) ∧
    side N C false r.1.1 r.1.2.1 r.1.2.2 ∧
    side N C true r.2.1 r.2.2.1 r.2.2.2

noncomputable def rectangle (N : ℕ) (C : Circuit) (j : ℕ) : Option (Rectangle N) := by
  classical
  exact if h : ∃ r, rectAt N C j r then some h.choose else none

lemma rect_selected {N : ℕ} {C : Circuit} {j : ℕ} {r : Rectangle N}
    (h : rectangle N C j = some r) : rectAt N C j r := by
  classical
  unfold rectangle at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Classical.choose_spec _
  · simp at h

lemma rect_absent {N : ℕ} {C : Circuit} {j : ℕ}
    (h : rectangle N C j = none) : ¬ ∃ r, rectAt N C j r := by
  classical
  intro hr
  simp [rectangle, hr] at h

lemma rect_none_of_or {N : ℕ} {C : Circuit} {j : ℕ} (h : (gateAt C j).op = .or) :
    rectangle N C j = none := by
  classical
  have hn : ¬ ∃ r, rectAt N C j r := by
    rintro ⟨r,hr⟩
    have := hr.1
    simp [h] at this
  simp [rectangle, hn]

lemma rect_bounds {N : ℕ} {C : Circuit} (rb : ReadsBack (N+N) C) {j : ℕ}
    (hj : j < C.gates.length) {r : Rectangle N} (h : rectAt N C j r) :
    r.1.1 < N+N+j ∧ r.2.1 < N+N+j := by
  constructor
  · apply rb j hj
    rcases h.2.1 with hp | hp <;> simp [hp]
  · apply rb j hj
    rcases h.2.1 with hp | hp <;> simp [hp]

lemma rectFromSmall {N : ℕ} {C : Circuit} (rb : ReadsBack (N+N) C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (h : ∃ u v, (gateAt C j).inputs = [u,v] ∧
      ((smallLeft N C u ∧ smallRight N C v) ∨ (smallRight N C u ∧ smallLeft N C v))) :
    ∃ r, rectAt N C j r := by
  obtain ⟨u,v,hi,h⟩ := h
  have hu := rb j hj u (by simp [hi])
  have hv := rb j hj v (by simp [hi])
  rcases h with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · obtain ⟨a,b,ha⟩ := sideLeft (by omega) hl
    obtain ⟨c,d,hc⟩ := sideRight (by omega) hr
    exact ⟨((u,a,b),(v,c,d)), hop, Or.inl hi, ha, hc⟩
  · obtain ⟨a,b,ha⟩ := sideLeft (by omega) hl
    obtain ⟨c,d,hc⟩ := sideRight (by omega) hr
    exact ⟨((v,a,b),(u,c,d)), hop, Or.inr hi, ha, hc⟩

def row {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l t : Fin N) (lineWire : ℕ) : Gate :=
  if I p l then
    if I p t then ⟨.and,[raw false p, reindex (N+N) lineWire]⟩
    else ⟨.and,[raw false p,raw true l]⟩
  else
    if I p t then ⟨.and,[raw false p,raw true t]⟩
    else pad

def lastOfBlock (n j : ℕ) : Gate := ⟨.or, [n+3*j, n+3*j+1]⟩

noncomputable def plan {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (j : ℕ) (i : Fin 3) : Gate :=
  match rectangle N C j with
  | none => if i.val = 2 then remap (N+N) (gateAt C j) else pad
  | some r =>
    if i.val = 0 then row I r.1.2.1 r.2.2.1 r.2.2.2 r.2.1
    else if i.val = 1 then row I r.1.2.2 r.2.2.1 r.2.2.2 r.2.1
    else lastOfBlock (N+N) j

noncomputable def rewriteCircuit {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) : Circuit :=
  assemble (N+N) C.gates.length (plan I C) C.output

lemma row_wf {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l t : Fin N) {w j : ℕ} (hw : w < N+N+j) :
    (row I p l t w).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (row I p l t w).inputs.length ≤ 2 ∧
    ∀ i ∈ (row I p l t w).inputs, i < N+N+3*j := by
  have hwp := reindex_lt hw
  have hp := raw_lt false p
  have hl := raw_lt true l
  have ht := raw_lt true t
  by_cases h1 : I p l <;> by_cases h2 : I p t
  all_goals simp [row, pad, h1, h2] at *
  all_goals omega

lemma plan_wf {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack (N+N) C)
    (j : ℕ) (hj : j < C.gates.length) (i : Fin 3) :
    (plan I C j i).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    (plan I C j i).inputs.length ≤ 2 ∧
    ∀ u ∈ (plan I C j i).inputs, u < N+N+3*j+i.val := by
  cases h : rectangle N C j with
  | none =>
    by_cases hi : i.val = 2
    · have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq_get C j hj]; exact List.getElem_mem hj
      have ok := mono _ hg
      refine ⟨by simpa [plan,h,hi,remap] using ok.1, by simpa [plan,h,hi,remap] using ok.2, ?_⟩
      simp only [plan,h,hi,ite_true,remap,List.mem_map]
      rintro u ⟨a,ha,rfl⟩
      have h' := reindex_lt (rb j hj a ha)
      omega
    · simp [plan,h,hi,pad]
  | some r =>
    have hr := rect_bounds rb hj (rect_selected h)
    by_cases h0 : i.val = 0
    · have ok := row_wf I r.1.2.1 r.2.2.1 r.2.2.2 hr.2
      simp only [plan,h,h0,ite_true,Nat.add_zero]
      exact ok
    · by_cases h1 : i.val = 1
      · have ok := row_wf I r.1.2.2 r.2.2.1 r.2.2.2 hr.2
        simp only [plan,h,h1,ite_true]
        exact ⟨ok.1,ok.2.1, fun u hu => (ok.2.2 u hu).trans_le (by omega)⟩
      · have h2 : i.val = 2 := by have := i.isLt; omega
        simp [plan,h,h2,lastOfBlock]

lemma rewritten_wf {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack (N+N) C) :
    Monotone2 (rewriteCircuit I C) ∧ ReadsBack (N+N) (rewriteCircuit I C) :=
  assemble_wf (plan I C) C.output (plan_wf I C mono rb)

lemma slotValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length) (t : Fin 3) :
    value (rewriteCircuit I C) z (N+N+(3*j+t.val)) =
      (plan I C j t).op.eval ((plan I C j t).inputs.map (value (rewriteCircuit I C) z)) := by
  have ht := t.isLt
  have hk : 3*j+t.val < (rewriteCircuit I C).gates.length := by
    simp [rewriteCircuit]; omega
  rw [gateValue (rewriteCircuit I C) rb z _ hk]
  have hg : gateAt (rewriteCircuit I C) (3*j+t.val) = plan I C j t :=
    assemble_gate _ _ _ _ _ _ hj
  rw [hg]

lemma copyValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hn : rectangle N C j = none) :
    value (rewriteCircuit I C) z (reindex (N+N) (N+N+j)) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map
        fun i => value (rewriteCircuit I C) z (reindex (N+N) i)) := by
  have h := slotValue I C rb z j hj (2 : Fin 3)
  rw [reindex_gate]
  simpa [plan, hn, remap, List.map_map, Function.comp_def, Nat.add_assoc] using h

lemma rawValue {N : ℕ} (C : Circuit) (z : Fin (N+N) → Bool) (b : Bool) (p : Fin N) :
    value C z (raw b p) = z (coord b p) := inputValue C z (coord b p)

lemma oldSideValue {N : ℕ} (C : Circuit) (rb : ReadsBack (N+N) C)
    (z : Fin (N+N) → Bool) {b w p q} (h : side N C b w p q) :
    value C z w = (z (coord b p) || z (coord b q)) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨j,hj,rfl,hop,hargs⟩
  · rw [rawValue, Bool.or_self]
  · rw [gateValue C rb z j hj, hop, hargs]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, rawValue]

lemma newSideValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) {b w p q} (h : side N C b w p q) :
    value (rewriteCircuit I C) z (reindex (N+N) w) = (z (coord b p) || z (coord b q)) := by
  rcases h with ⟨hw,hq⟩ | ⟨j,hj,rfl,hop,hargs⟩
  · subst w
    subst q
    rw [reindex_input (raw_lt b p), rawValue, Bool.or_self]
  · rw [copyValue I C rb z j hj (rect_none_of_or hop), hop, hargs]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
      List.any_nil, id_eq, Bool.or_false, reindex_input (raw_lt _ _), rawValue]

lemma oldRectValue {N : ℕ} (C : Circuit) (rb : ReadsBack (N+N) C)
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length)
    {r : Rectangle N} (hr : rectAt N C j r) :
    value C z (N+N+j) = ((z (coord false r.1.2.1) || z (coord false r.1.2.2)) &&
      (z (coord true r.2.2.1) || z (coord true r.2.2.2))) := by
  rw [gateValue C rb z j hj, hr.1]
  have ha := oldSideValue C rb z hr.2.2.1
  have hb := oldSideValue C rb z hr.2.2.2
  rcases hr.2.1 with he | he <;>
    rw [he] <;>
    simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,
      Bool.and_true, ha, hb]
  apply Bool.and_comm

def rowBool {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l t : Fin N) (z : Fin (N+N) → Bool) : Bool :=
  z (coord false p) &&
    ((decide (I p l) && z (coord true l)) || (decide (I p t) && z (coord true t)))

lemma rowValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) (rewriteCircuit I C)) (z : Fin (N+N) → Bool)
    (p l t : Fin N) (w : ℕ) (hs : side N C true w l t) :
    (row I p l t w).op.eval ((row I p l t w).inputs.map (value (rewriteCircuit I C) z)) =
      rowBool I p l t z := by
  have hw := newSideValue I C rb z hs
  have hp := rawValue (rewriteCircuit I C) z false p
  have hl := rawValue (rewriteCircuit I C) z true l
  have ht := rawValue (rewriteCircuit I C) z true t
  simp only [raw_left] at hp
  simp only [raw_right] at hl ht
  by_cases h1 : I p l <;> by_cases h2 : I p t
  all_goals simp [row, rowBool, h1, h2, pad, GateOp.eval, hw, hp, hl, ht]

lemma rowSlotValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length)
    {r : Rectangle N} (hr : rectangle N C j = some r) :
    value (rewriteCircuit I C) z (N+N+3*j) = rowBool I r.1.2.1 r.2.2.1 r.2.2.2 z ∧
      value (rewriteCircuit I C) z (N+N+3*j+1) = rowBool I r.1.2.2 r.2.2.1 r.2.2.2 z := by
  have hs := (rect_selected hr).2.2.2
  constructor
  · have hv := slotValue I C rb z j hj (0 : Fin 3)
    simp only [plan, hr, Fin.val_zero, Nat.add_zero] at hv
    rw [hv]
    exact rowValue I C rb z _ _ _ _ hs
  · have hv := slotValue I C rb z j hj (1 : Fin 3)
    simp only [plan, hr, Fin.val_one, Nat.one_ne_zero, ite_false] at hv
    rw [Nat.add_assoc, hv]
    exact rowValue I C rb z _ _ _ _ hs

lemma newRectValue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length)
    {r : Rectangle N} (hr : rectangle N C j = some r) :
    value (rewriteCircuit I C) z (reindex (N+N) (N+N+j)) =
      (rowBool I r.1.2.1 r.2.2.1 r.2.2.2 z || rowBool I r.1.2.2 r.2.2.1 r.2.2.2 z) := by
  have hv := slotValue I C rb z j hj (2 : Fin 3)
  have hparts := rowSlotValue I C rb z j hj hr
  rw [reindex_gate, Nat.add_assoc]
  simpa [plan, hr, lastOfBlock, GateOp.eval, hparts.1, hparts.2] using hv

def hits {N : ℕ} (I : Fin N → Fin N → Prop) (z : Fin (N+N) → Bool) : Prop :=
  ∃ p l : Fin N, I p l ∧ z (coord false p) = true ∧ z (coord true l) = true

def onlySide {N : ℕ} (right : Bool) (z : Fin (N+N) → Bool) (i : Fin (N+N)) : Bool :=
  if right then decide (N ≤ i.val) && z i else decide (i.val < N) && z i

def singleton {N : ℕ} (right : Bool) (p : Fin N) (i : Fin (N+N)) : Bool :=
  decide (i = coord right p)

def edgePair {N : ℕ} (p l : Fin N) (i : Fin (N+N)) : Bool :=
  decide (i = coord false p ∨ i = coord true l)

def tests {N : ℕ} (I : Fin N → Fin N → Prop) (z : Fin (N+N) → Bool) : Prop :=
  (∀ p : Fin N, z (coord false p) = false) ∨ (∀ l : Fin N, z (coord true l) = false) ∨
    ∃ p l : Fin N, I p l ∧ z = edgePair p l

lemma separated {N : ℕ} (p l : Fin N) : coord false p ≠ coord true l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N+l.val at he
  have hp := p.isLt
  omega

lemma coord_inj {N : ℕ} (b : Bool) : Function.Injective (@coord N b) := by
  intro p q h
  apply Fin.ext
  have h' : raw b p = raw b q := congrArg Fin.val h
  cases b <;> simp only [raw_left, raw_right] at h' <;> omega

lemma pairLeft {N : ℕ} (p l q : Fin N) : edgePair p l (coord false q) = decide (q = p) := by
  simp only [edgePair, separated q l, or_false]
  congr 1
  exact propext ((coord_inj false).eq_iff)

lemma pairRight {N : ℕ} (p l q : Fin N) : edgePair p l (coord true q) = decide (q = l) := by
  simp only [edgePair, (separated p q).symm, false_or]
  congr 1
  exact propext ((coord_inj true).eq_iff)

lemma onlyLeft_right_zero {N : ℕ} (z : Fin (N+N) → Bool) (l : Fin N) :
    onlySide false z (coord true l) = false := by
  have h : ¬ (coord true l).val < N := by change ¬ N+l.val < N; omega
  simp [onlySide, h]

lemma onlyRight_left_zero {N : ℕ} (z : Fin (N+N) → Bool) (p : Fin N) :
    onlySide true z (coord false p) = false := by
  have h : ¬ N ≤ (coord false p).val := Nat.not_le.mpr p.isLt
  simp [onlySide, h]

lemma singleton_left_zero {N : ℕ} (p l : Fin N) :
    singleton false p (coord true l) = false := by simp [singleton, (separated p l).symm]

lemma singleton_right_zero {N : ℕ} (p l : Fin N) :
    singleton true l (coord false p) = false := by simp [singleton, separated p l]

lemma rowTrue {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l t : Fin N) (z : Fin (N+N) → Bool) :
    rowBool I p l t z = true ↔ z (coord false p) = true ∧
      ((I p l ∧ z (coord true l) = true) ∨ (I p t ∧ z (coord true t) = true)) := by
  simp only [rowBool, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

lemma rowHits {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    {p l t : Fin N} {z : Fin (N+N) → Bool} (h : rowBool I p l t z = true) : hits I z := by
  obtain ⟨hp,hpt | hpt⟩ := (rowTrue I p l t z).mp h
  · exact ⟨p,l,hpt.1,hp,hpt.2⟩
  · exact ⟨p,t,hpt.1,hp,hpt.2⟩

lemma rectImplies {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) C) (drb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length)
    {r : Rectangle N} (hr : rectangle N C j = some r) :
    value (rewriteCircuit I C) z (reindex (N+N) (N+N+j)) = true → value C z (N+N+j) = true := by
  rw [newRectValue I C drb z j hj hr, oldRectValue C rb z j hj (rect_selected hr)]
  simp only [Bool.or_eq_true, Bool.and_eq_true, rowTrue]
  rintro (⟨hp, hl | hl⟩ | ⟨hp, hl | hl⟩)
  · exact ⟨Or.inl hp, Or.inl hl.2⟩
  · exact ⟨Or.inl hp, Or.inr hl.2⟩
  · exact ⟨Or.inr hp, Or.inl hl.2⟩
  · exact ⟨Or.inr hp, Or.inr hl.2⟩

lemma rectOnTests {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (rb : ReadsBack (N+N) C) (drb : ReadsBack (N+N) (rewriteCircuit I C))
    (z : Fin (N+N) → Bool) (j : ℕ) (hj : j < C.gates.length)
    {r : Rectangle N} (hr : rectangle N C j = some r) (hz : tests I z) :
    value (rewriteCircuit I C) z (reindex (N+N) (N+N+j)) = value C z (N+N+j) := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨rectImplies I C rb drb z j hj hr, ?_⟩
  rw [newRectValue I C drb z j hj hr, oldRectValue C rb z j hj (rect_selected hr)]
  simp only [Bool.or_eq_true, Bool.and_eq_true, rowTrue]
  rcases hz with hz | hz | ⟨p,l,hI,rfl⟩
  · simp [hz]
  · simp [hz]
  · simp only [pairLeft, pairRight, decide_eq_true_eq]
    rintro ⟨hp | hp, hl | hl⟩
    · exact Or.inl ⟨hp, Or.inl ⟨hp.symm ▸ hl.symm ▸ hI, hl⟩⟩
    · exact Or.inl ⟨hp, Or.inr ⟨hp.symm ▸ hl.symm ▸ hI, hl⟩⟩
    · exact Or.inr ⟨hp, Or.inl ⟨hp.symm ▸ hl.symm ▸ hI, hl⟩⟩
    · exact Or.inr ⟨hp, Or.inr ⟨hp.symm ▸ hl.symm ▸ hI, hl⟩⟩

-- On arbitrary inputs the replacement can only remove true values. On side-only
-- inputs and positive edge pairs every old wire keeps its value.
lemma simulation {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack (N+N) C)
    (drb : ReadsBack (N+N) (rewriteCircuit I C)) (z : Fin (N+N) → Bool) (i : ℕ) :
    (value (rewriteCircuit I C) z (reindex (N+N) i) = true → value C z i = true) ∧
    (tests I z → value (rewriteCircuit I C) z (reindex (N+N) i) = value C z i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hin : i < N+N
    · rw [reindex_input hin, inputValue (rewriteCircuit I C) z ⟨i,hin⟩, inputValue C z ⟨i,hin⟩]
      exact ⟨id, fun _ => rfl⟩
    by_cases hb : N+N+C.gates.length ≤ i
    · have dv : N+N+(rewriteCircuit I C).gates.length ≤ reindex (N+N) i := by
        simp [rewriteCircuit, reindex, hin]
        omega
      have ho : value C z i = false := val_big C.gates z i hb
      have hn : value (rewriteCircuit I C) z (reindex (N+N) i) = false :=
        val_big (rewriteCircuit I C).gates z _ dv
      simp [ho,hn]
    obtain ⟨j, rfl⟩ : ∃ j, i = N+N+j := ⟨i-(N+N), by omega⟩
    have hj : j < C.gates.length := by omega
    cases hrect : rectangle N C j with
    | none =>
      rw [copyValue I C drb z j hj hrect, gateValue C rb z j hj]
      constructor
      · exact evalIncreasing _ (andOr mono j hj) _ _ _
          (fun k hk => (ih k (rb j hj k hk)).1)
      · intro hz
        congr 1
        exact List.map_congr_left (fun k hk => (ih k (rb j hj k hk)).2 hz)
    | some r =>
      exact ⟨rectImplies I C rb drb z j hj hrect, rectOnTests I C rb drb z j hj hrect⟩

def good {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) : Prop :=
  (∀ z : Fin (N+N) → Bool, value C z (N+N+j) = true →
    value C (onlySide false z) (N+N+j) = true ∨
    value C (onlySide true z) (N+N+j) = true ∨ hits I z) ∧
  ((∀ p : Fin N, value C (singleton false p) (N+N+j) = false) ∧
   ∀ l : Fin N, value C (singleton true l) (N+N+j) = false)

def small {N : ℕ} (C : Circuit) (j : ℕ) : Prop :=
  ∃ u v, (gateAt C j).inputs = [u,v] ∧
    ((smallLeft N C u ∧ smallRight N C v) ∨ (smallRight N C u ∧ smallLeft N C v))

lemma goodFromHits {N : ℕ} {I : Fin N → Fin N → Prop} (D : Circuit) (j : ℕ)
    (h : ∀ z : Fin (N+N) → Bool, value D z (N+N+j) = true → hits I z) : good I D j := by
  refine ⟨fun z hz => Or.inr (Or.inr (h z hz)), ?_, ?_⟩
  · intro p
    apply Bool.eq_false_of_not_eq_true
    intro hp
    obtain ⟨_,l,_,_,hl⟩ := h _ hp
    simp only [singleton_left_zero, Bool.false_eq_true] at hl
  · intro l
    apply Bool.eq_false_of_not_eq_true
    intro hl
    obtain ⟨p,_,_,hp,_⟩ := h _ hl
    simp only [singleton_right_zero, Bool.false_eq_true] at hp

lemma goodCopied {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack (N+N) C)
    (drb : ReadsBack (N+N) (rewriteCircuit I C)) (j : ℕ) (hg : good I C j) :
    good I (rewriteCircuit I C) (3*j+2) := by
  let D := rewriteCircuit I C
  have compare (z : Fin (N+N) → Bool) :
      (value D z (N+N+(3*j+2)) = true → value C z (N+N+j) = true) ∧
      (tests I z → value D z (N+N+(3*j+2)) = value C z (N+N+j)) := by
    have h := simulation I C mono rb drb z (N+N+j)
    rw [reindex_gate] at h
    simpa only [D, Nat.add_assoc] using h
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases hg.1 z ((compare z).1 hz) with hl | hr | hh
    · exact Or.inl (((compare _).2 (Or.inr (Or.inl (onlyLeft_right_zero z)))).trans hl)
    · exact Or.inr (Or.inl (((compare _).2 (Or.inl (onlyRight_left_zero z))).trans hr))
    · exact Or.inr (Or.inr hh)
  · intro p
    exact ((compare _).2 (Or.inr (Or.inl (singleton_left_zero p)))).trans (hg.2.1 p)
  · intro l
    exact ((compare _).2 (Or.inl (fun p => singleton_right_zero p l))).trans (hg.2.2 l)

lemma goodInBlocks {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack (N+N) C)
    (drb : ReadsBack (N+N) (rewriteCircuit I C))
    (hc : ∀ j < C.gates.length, (gateAt C j).op = .and → good I C j ∨ small (N := N) C j)
    (j : ℕ) (hj : j < C.gates.length) (t : Fin 3)
    (hop : (plan I C j t).op = .and) :
    good I (rewriteCircuit I C) (3*j+t.val) := by
  cases hrect : rectangle N C j with
  | none =>
    by_cases ht : t.val = 2
    · have hop' : (gateAt C j).op = .and := by simpa [plan,hrect,ht,remap] using hop
      rcases hc j hj hop' with hg | hs
      · rw [ht]; exact goodCopied I C mono rb drb j hg
      · exact (rect_absent hrect (rectFromSmall rb hj hop' hs)).elim
    · simp [plan,hrect,ht,pad] at hop
  | some r =>
    by_cases h0 : t.val = 0
    · apply goodFromHits
      intro z hz
      have hv := (rowSlotValue I C drb z j hj hrect).1
      have hb : rowBool I r.1.2.1 r.2.2.1 r.2.2.2 z = true := hv.symm.trans (by simpa [h0] using hz)
      exact rowHits I hb
    by_cases h1 : t.val = 1
    · apply goodFromHits
      intro z hz
      have hv := (rowSlotValue I C drb z j hj hrect).2
      have hb : rowBool I r.1.2.2 r.2.2.1 r.2.2.2 z = true :=
        hv.symm.trans (by simpa [h1,Nat.add_assoc] using hz)
      exact rowHits I hb
    · simp [plan,hrect,h0,h1,lastOfBlock] at hop

theorem cleanRewrite {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack (N+N) C)
    (hf : ∀ z : Fin (N+N) → Bool, value C z C.output = true ↔ hits I z)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = .and → good I C j ∨ small (N := N) C j) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ 3*C.size ∧
      (∀ z : Fin (N+N) → Bool, value D z D.output = true ↔ hits I z) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and → good I D j := by
  let D := rewriteCircuit I C
  obtain ⟨dm,drb⟩ := rewritten_wf I C mono rb
  refine ⟨D, dm, drb, ?_, ?_, ?_⟩
  · simp [D,rewriteCircuit,Circuit.size]
  · intro z
    constructor
    · intro hv
      exact (hf z).mp ((simulation I C mono rb drb z C.output).1 hv)
    · rintro ⟨p,l,hI,hp,hl⟩
      let x := edgePair p l
      have hx : hits I x := ⟨p,l,hI,by simp [x,pairLeft],by simp [x,pairRight]⟩
      have tx : tests I x := Or.inr (Or.inr ⟨p,l,hI,rfl⟩)
      have hold : value C x C.output = true := (hf x).2 hx
      have hnew : value D x D.output = true :=
        ((simulation I C mono rb drb x C.output).2 tx).trans hold
      apply valueIncreasing D dm drb x z ?_ D.output hnew
      intro i hi
      have hcase : i = coord false p ∨ i = coord true l := of_decide_eq_true hi
      exact hcase.elim (fun h => h.symm ▸ hp) (fun h => h.symm ▸ hl)
  · intro k hk hop
    have hlen : k < 3*C.gates.length := by simpa [D,rewriteCircuit] using hk
    let t : Fin 3 := ⟨Nat.mod k 3, Nat.mod_lt _ (by decide)⟩
    have hj : k / 3 < C.gates.length := by omega
    have hki : k = 3*(k/3)+t.val := by
      change k = 3*(k/3) + k % 3
      omega
    have hgat : gateAt D k = plan I C (k/3) t := by
      calc
        gateAt D k = gateAt D (3*(k/3)+t.val) := congrArg (gateAt D) hki
        _ = plan I C (k/3) t := assemble_gate _ _ _ _ _ _ hj
    have hfinal := goodInBlocks I C mono rb drb hc (k/3) hj t (hgat ▸ hop)
    exact hki.symm ▸ hfinal


end PEqualNP.Outside.L_meta_2856_aux

theorem PEqualNP.Outside.L_meta_2856 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka20 : Fin (N + N) => decide (ka20.val < N) && z ka20))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb21 : Fin (N + N) => decide (N ≤ kb21.val) && z kb21))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C.wires (List.ofFn (fun kc22 : Fin (N + N) => decide (kc22 = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd23 : Fin (N + N) => decide (kd23 = Fin.natAdd N l)))).getD (N + N + j) false = false)) ∨ (∃ u v : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [u, v] ∧ (((u < N ∨ (N + N ≤ u ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)) ∧ ((N ≤ v ∧ v < N + N) ∨ (N + N ≤ v ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N))) ∨ (((N ≤ u ∧ u < N + N) ∨ (N + N ≤ u ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - (N + N))).inputs = [a, b] ∧ N ≤ a ∧ a < N + N ∧ N ≤ b ∧ b < N + N)) ∧ (v < N ∨ (N + N ≤ v ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - (N + N))).inputs = [a, b] ∧ a < N ∧ b < N)))))) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C' ∧ C'.size ≤ 3 * C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C' z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < C'.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∀ z : Fin (N + N) → Bool, (C'.wires (List.ofFn z)).getD (N + N + j) false = true → (C'.wires (List.ofFn (fun ka24 : Fin (N + N) => decide (ka24.val < N) && z ka24))).getD (N + N + j) false = true ∨ (C'.wires (List.ofFn (fun kb25 : Fin (N + N) => decide (N ≤ kb25.val) && z kb25))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ ((∀ p : Fin N, (C'.wires (List.ofFn (fun kc26 : Fin (N + N) => decide (kc26 = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C'.wires (List.ofFn (fun kd27 : Fin (N + N) => decide (kd27 = Fin.natAdd N l)))).getD (N + N + j) false = false))) := by
  intro N I _ C _ mono rb hf hc
  exact PEqualNP.Outside.L_meta_2856_aux.cleanRewrite I C mono rb hf hc
