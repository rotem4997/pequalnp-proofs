import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_717_aux

open PEqualNP.CircuitLowerBounds

def stepWires (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def runWires (m : ℕ) (gs : List Gate) (x : Fin m → Bool) : List Bool :=
  gs.foldl stepWires (List.ofFn x)

def wireVal (m : ℕ) (gs : List Gate) (x : Fin m → Bool) (i : ℕ) : Bool :=
  (runWires m gs x).getD i false

def wireAt (m : ℕ) (gs : List Gate) (bound i : ℕ) (x : Fin m → Bool) : Bool :=
  if i < bound then wireVal m gs x i else false

lemma foldl_stepWires_length (gs : List Gate) (ws : List Bool) :
    (gs.foldl stepWires ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, stepWires, List.length_append]
    simp only [List.length_nil]
    omega

lemma runWires_length (m : ℕ) (gs : List Gate) (x : Fin m → Bool) :
    (runWires m gs x).length = m + gs.length := by
  unfold runWires
  rw [foldl_stepWires_length, List.length_ofFn]

lemma foldl_stepWires_getD_lt (gs : List Gate) (ws : List Bool) {i : ℕ} (hi : i < ws.length) :
    (gs.foldl stepWires ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWires ws g).length := by
      simp only [stepWires, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWires ws g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [stepWires, List.getElem_append_left hi]

lemma wireVal_input (m : ℕ) (gs : List Gate) (x : Fin m → Bool) (v : Fin m) :
    wireVal m gs x v.val = x v := by
  unfold wireVal runWires
  have hv : v.val < (List.ofFn x).length := by simp
  rw [foldl_stepWires_getD_lt gs (List.ofFn x) hv, List.getD_eq_getElem _ _ hv, List.getElem_ofFn]

lemma wireVal_of_ge (m : ℕ) (gs : List Gate) (x : Fin m → Bool) {i : ℕ} (hi : m + gs.length ≤ i) :
    wireVal m gs x i = false := by
  unfold wireVal
  rw [List.getD_eq_default]
  rw [runWires_length]
  exact hi

lemma wireVal_gate (m : ℕ) (gs : List Gate) (x : Fin m → Bool) {k : ℕ} (hk : k < gs.length) :
    wireVal m gs x (m + k) =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => wireAt m gs (m + k) i x) := by
  unfold wireVal runWires
  have hsplit : gs = gs.take k ++ (gs[k]'hk) :: gs.drop (k + 1) := by
    simp
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set ws := (gs.take k).foldl stepWires (List.ofFn x)
  have hws_len : ws.length = m + k := by
    rw [foldl_stepWires_length, List.length_ofFn, List.length_take]
    omega
  have hstep_len : (stepWires ws (gs[k]'hk)).length = m + k + 1 := by
    simp [stepWires, hws_len]
  have hlt : m + k < (stepWires ws (gs[k]'hk)).length := by omega
  rw [foldl_stepWires_getD_lt (gs.drop (k + 1)) (stepWires ws (gs[k]'hk)) hlt]
  have hlast : (stepWires ws (gs[k]'hk)).getD (m + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => ws.getD i false) := by
    rw [List.getD_eq_getElem _ _ hlt]
    simp [stepWires, hws_len]
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  unfold wireAt
  split_ifs with hi
  · have hi_ws : i < ws.length := by omega
    have hsplit2 : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    symm
    unfold wireVal runWires
    rw [hsplit2, List.foldl_append]
    exact foldl_stepWires_getD_lt (gs.drop k) ws hi_ws
  · rw [List.getD_eq_default]
    omega

-- Deleting gate j when wire (n + 1 + j) always equals input wire n.

def remapIdx (n j i : ℕ) : ℕ :=
  if i = n + 1 + j then n
  else if n + 1 + j < i then i - 1
  else i

def remapGate (n j : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapIdx n j)⟩

def deleteCopyGate (n j : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (remapGate n j), remapIdx n j C.output⟩

lemma deleteCopyGate_size (n j : ℕ) (C : Circuit) (hj : j < C.gates.length) :
    (deleteCopyGate n j C).size = C.size - 1 := by
  simp only [Circuit.size, deleteCopyGate, List.length_append, List.length_take,
    List.length_map, List.length_drop]
  omega

lemma deleteCopyGate_fanInTwo (n j : ℕ) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (deleteCopyGate n j C) := by
  intro g hg
  simp only [deleteCopyGate, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, hg0, rfl⟩
  · exact hf g (List.mem_of_mem_take h1)
  · have h0 := hf g0 (List.mem_of_mem_drop hg0)
    simpa [remapGate] using h0

lemma deleteCopyGate_wires (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (x : Fin (n + 1) → Bool)
    (hcopy : wireVal (n + 1) C.gates x (n + 1 + j) = wireVal (n + 1) C.gates x n) :
    ∀ i : ℕ, wireVal (n + 1) (deleteCopyGate n j C).gates x (remapIdx n j i) =
      wireVal (n + 1) C.gates x i := by
  set gs' := (deleteCopyGate n j C).gates
  have hlen' : gs'.length = C.gates.length - 1 := by
    simp only [gs', deleteCopyGate, List.length_append, List.length_take,
      List.length_map, List.length_drop]
    omega
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases h1 : i < n + 1
    · have hrem : remapIdx n j i = i := by
        unfold remapIdx
        simp [show i ≠ n + 1 + j by omega, show ¬ n + 1 + j < i by omega]
      rw [hrem]
      have h1' := wireVal_input (n + 1) gs' x ⟨i, h1⟩
      have h2' := wireVal_input (n + 1) C.gates x ⟨i, h1⟩
      exact h1'.trans h2'.symm
    · by_cases h2 : i < n + 1 + j
      · have hrem : remapIdx n j i = i := by
          unfold remapIdx
          simp [show i ≠ n + 1 + j by omega, show ¬ n + 1 + j < i by omega]
        rw [hrem]
        set k := i - (n + 1)
        have hk : k < j := by omega
        have hk_c : k < C.gates.length := by omega
        have hk_c' : k < gs'.length := by omega
        have hgate_eq : gs'[k]'hk_c' = C.gates[k]'hk_c := by
          simp only [gs', deleteCopyGate]
          rw [List.getElem_append_left (by simp; omega), List.getElem_take]
        have heq_i : n + 1 + k = i := by omega
        rw [← heq_i, wireVal_gate (n + 1) gs' x hk_c', wireVal_gate (n + 1) C.gates x hk_c,
            hgate_eq]
        congr 1
        apply List.map_congr_left
        intro a _
        unfold wireAt
        split_ifs with ha
        · have ha_rem : remapIdx n j a = a := by
            unfold remapIdx
            simp [show a ≠ n + 1 + j by omega, show ¬ n + 1 + j < a by omega]
          have h1 := ih a (by omega)
          rwa [ha_rem] at h1
        · rfl
      · by_cases h3 : i = n + 1 + j
        · subst h3
          have hrem : remapIdx n j (n + 1 + j) = n := by simp [remapIdx]
          rw [hrem, hcopy]
          have h1' := wireVal_input (n + 1) gs' x ⟨n, by omega⟩
          have h2' := wireVal_input (n + 1) C.gates x ⟨n, by omega⟩
          exact h1'.trans h2'.symm
        · by_cases h4 : i < n + 1 + C.gates.length
          · have hrem : remapIdx n j i = i - 1 := by
              unfold remapIdx
              simp [show i ≠ n + 1 + j by omega, show n + 1 + j < i by omega]
            rw [hrem]
            set k := i - (n + 1)
            have hk_gt : j < k := by omega
            have hk_c : k < C.gates.length := by omega
            set k' := k - 1
            have hk'_c' : k' < gs'.length := by omega
            have hgate_eq : gs'[k']'hk'_c' = remapGate n j (C.gates[k]'hk_c) := by
              simp only [gs', deleteCopyGate]
              have htake_len : (C.gates.take j).length = j := by rw [List.length_take]; omega
              rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_drop]
              congr 2
              omega
            have heq1 : n + 1 + k' = i - 1 := by omega
            have heq2 : n + 1 + k = i := by omega
            rw [← heq1, ← heq2, wireVal_gate (n + 1) gs' x hk'_c',
                wireVal_gate (n + 1) C.gates x hk_c, hgate_eq]
            simp only [remapGate, List.map_map]
            congr 1
            apply List.map_congr_left
            intro a _
            dsimp only [Function.comp]
            unfold wireAt
            by_cases ha : a < n + 1 + k
            · have ha' : remapIdx n j a < n + 1 + k' := by
                unfold remapIdx
                split_ifs <;> omega
              simp only [ha, ha', ↓reduceIte]
              exact ih a (by omega)
            · have ha' : ¬ remapIdx n j a < n + 1 + k' := by
                unfold remapIdx
                split_ifs <;> omega
              simp only [ha, ha', ↓reduceIte]
          · have hrem : remapIdx n j i = i - 1 := by
              unfold remapIdx
              simp [show i ≠ n + 1 + j by omega, show n + 1 + j < i by omega]
            rw [hrem]
            rw [wireVal_of_ge (n + 1) gs' x (by omega),
                wireVal_of_ge (n + 1) C.gates x (by omega)]

lemma deleteCopyGate_eval (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (x : Fin (n + 1) → Bool)
    (hcopy : wireVal (n + 1) C.gates x (n + 1 + j) = wireVal (n + 1) C.gates x n) :
    (deleteCopyGate n j C).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  deleteCopyGate_wires n j C hj x hcopy C.output

-- Agreement of wires not reading wire n on Fin.snoc y false vs Fin.snoc y true.

lemma wires_indep_of_last (n j : ℕ) (C : Circuit) (y : Fin n → Bool)
    (huniq : ∀ (j' : ℕ) (h' : Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j)
    (hskip : wireVal (n + 1) C.gates (Fin.snoc y false) (n + 1 + j) =
             wireVal (n + 1) C.gates (Fin.snoc y true) (n + 1 + j)) :
    ∀ i : ℕ, i ≠ n →
      wireVal (n + 1) C.gates (Fin.snoc y false) i =
      wireVal (n + 1) C.gates (Fin.snoc y true) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hne
    by_cases h1 : i < n + 1
    · have hi_lt : i < n := by omega
      have hL := wireVal_input (n + 1) C.gates (Fin.snoc y false) ⟨i, h1⟩
      have hR := wireVal_input (n + 1) C.gates (Fin.snoc y true) ⟨i, h1⟩
      change wireVal (n + 1) C.gates (Fin.snoc y false) i = _ at hL
      change wireVal (n + 1) C.gates (Fin.snoc y true) i = _ at hR
      rw [hL, hR]
      have hcast : (⟨i, h1⟩ : Fin (n + 1)) = (⟨i, hi_lt⟩ : Fin n).castSucc := by
        ext; rfl
      rw [hcast, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · by_cases h2 : i < n + 1 + C.gates.length
      · set k := i - (n + 1)
        have hk : k < C.gates.length := by omega
        by_cases hkj : k = j
        · subst hkj
          have heq : i = n + 1 + k := by omega
          rw [heq]
          exact hskip
        · have heq : n + 1 + k = i := by omega
          rw [← heq, wireVal_gate (n + 1) C.gates (Fin.snoc y false) hk,
              wireVal_gate (n + 1) C.gates (Fin.snoc y true) hk]
          congr 1
          apply List.map_congr_left
          intro a ha
          have ha_ne : a ≠ n := by
            intro heqa
            subst heqa
            have hget : C.gates[k]? = some (C.gates[k]'hk) := List.getElem?_eq_getElem hk
            exact hkj (huniq k (C.gates[k]'hk) hget ha)
          unfold wireAt
          split_ifs with hlt
          · exact ih a (by omega) ha_ne
          · rfl
      · rw [wireVal_of_ge (n + 1) C.gates _ (by omega),
            wireVal_of_ge (n + 1) C.gates _ (by omega)]

lemma wires_indep_before (n j : ℕ) (C : Circuit) (y : Fin n → Bool)
    (huniq : ∀ (j' : ℕ) (h' : Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j) :
    ∀ i : ℕ, i < n + 1 + j → i ≠ n →
      wireVal (n + 1) C.gates (Fin.snoc y false) i =
      wireVal (n + 1) C.gates (Fin.snoc y true) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hlt hne
    by_cases h1 : i < n + 1
    · have hi_lt : i < n := by omega
      have hL := wireVal_input (n + 1) C.gates (Fin.snoc y false) ⟨i, h1⟩
      have hR := wireVal_input (n + 1) C.gates (Fin.snoc y true) ⟨i, h1⟩
      change wireVal (n + 1) C.gates (Fin.snoc y false) i = _ at hL
      change wireVal (n + 1) C.gates (Fin.snoc y true) i = _ at hR
      rw [hL, hR]
      have hcast : (⟨i, h1⟩ : Fin (n + 1)) = (⟨i, hi_lt⟩ : Fin n).castSucc := by
        ext; rfl
      rw [hcast, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · by_cases h2 : i < n + 1 + C.gates.length
      · set k := i - (n + 1)
        have hk : k < C.gates.length := by omega
        have hkj : k ≠ j := by omega
        have heq : n + 1 + k = i := by omega
        rw [← heq, wireVal_gate (n + 1) C.gates (Fin.snoc y false) hk,
            wireVal_gate (n + 1) C.gates (Fin.snoc y true) hk]
        congr 1
        apply List.map_congr_left
        intro a ha
        have ha_ne : a ≠ n := by
          intro heqa
          subst heqa
          have hget : C.gates[k]? = some (C.gates[k]'hk) := List.getElem?_eq_getElem hk
          exact hkj (huniq k (C.gates[k]'hk) hget ha)
        unfold wireAt
        split_ifs with ha_lt
        · exact ih a (by omega) (by omega) ha_ne
        · rfl
      · rw [wireVal_of_ge (n + 1) C.gates _ (by omega),
            wireVal_of_ge (n + 1) C.gates _ (by omega)]

lemma snoc_eq_self {n : ℕ} (x : Fin (n + 1) → Bool) :
    Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n)) = x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro k; simp

end PEqualNP.Outside.L_meta_717_aux

open PEqualNP.Outside.L_meta_717_aux

theorem PEqualNP.Outside.L_meta_717 : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ y y' : Fin n → Bool, g y ≠ g y') → PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' → (∀ x : Fin (n + 1) → Bool, C'.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → C.size ≤ C'.size) → ¬ ∃ (j : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some h ∧ (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n ∈ h.inputs ∧ ∀ (j' : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j := by
  classical
  intro n g C ⟨y0, y1, hne_g⟩ hfan heval hmin
  rintro ⟨j, h, hget, hop, hmem, huniq⟩
  have hj : j < C.gates.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hget
    simp at hget
  have hgate_eq : C.gates[j]'hj = h := by
    rw [List.getElem?_eq_getElem hj] at hget
    exact Option.some.inj hget
  have hout_ne : C.output ≠ n := by
    intro hout
    have h0 := heval (Fin.snoc y0 false)
    have h1 := heval (Fin.snoc y1 false)
    change wireVal (n + 1) C.gates (Fin.snoc y0 false) C.output = _ at h0
    change wireVal (n + 1) C.gates (Fin.snoc y1 false) C.output = _ at h1
    rw [hout] at h0 h1
    have hw0 := wireVal_input (n + 1) C.gates (Fin.snoc y0 false) (Fin.last n)
    have hw1 := wireVal_input (n + 1) C.gates (Fin.snoc y1 false) (Fin.last n)
    change wireVal (n + 1) C.gates (Fin.snoc y0 false) n = _ at hw0
    change wireVal (n + 1) C.gates (Fin.snoc y1 false) n = _ at hw1
    rw [hw0] at h0
    rw [hw1] at h1
    simp only [Fin.snoc_last, Fin.snoc_castSucc, Bool.false_xor] at h0 h1
    exact hne_g (h0.symm.trans h1)
  have hcontra_of_copy :
      (∀ x : Fin (n + 1) → Bool,
        wireVal (n + 1) C.gates x (n + 1 + j) = wireVal (n + 1) C.gates x n) → False := by
    intro hcopy
    let C' := deleteCopyGate n j C
    have hfan' := deleteCopyGate_fanInTwo n j C hfan
    have heval' : ∀ x : Fin (n + 1) → Bool,
        C'.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc)) := by
      intro x
      rw [deleteCopyGate_eval n j C hj x (hcopy x)]
      exact heval x
    have hle := hmin C' hfan' heval'
    have hsz := deleteCopyGate_size n j C hj
    change C.gates.length ≤ C'.size at hle
    change C'.size = C.gates.length - 1 at hsz
    omega
  have hcontra_of_skip : ∀ y : Fin n → Bool,
      wireVal (n + 1) C.gates (Fin.snoc y false) (n + 1 + j) =
      wireVal (n + 1) C.gates (Fin.snoc y true) (n + 1 + j) → False := by
    intro y hskip
    have heq := wires_indep_of_last n j C y huniq hskip C.output hout_ne
    have h0 := heval (Fin.snoc y false)
    have h1 := heval (Fin.snoc y true)
    change wireVal (n + 1) C.gates (Fin.snoc y false) C.output = _ at h0
    change wireVal (n + 1) C.gates (Fin.snoc y true) C.output = _ at h1
    rw [heq, h1] at h0
    simp only [Fin.snoc_last, Fin.snoc_castSucc] at h0
    cases g y <;> simp at h0
  have hlen_le : h.inputs.length ≤ 2 := (hfan h (hgate_eq ▸ List.getElem_mem hj)).2
  have hwire_n : ∀ x : Fin (n + 1) → Bool, wireAt (n + 1) C.gates (n + 1 + j) n x = wireVal (n + 1) C.gates x n := by
    intro x
    unfold wireAt
    simp [show n < n + 1 + j by omega]
  cases hin : h.inputs with
  | nil => rw [hin] at hmem; simp at hmem
  | cons a l =>
    cases l with
    | nil =>
      rw [hin] at hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      apply hcontra_of_copy
      intro x
      rw [wireVal_gate (n + 1) C.gates x hj, hgate_eq, hin]
      rcases hop with hand | hor
      · rw [hand]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hwire_n]
      · rw [hor]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hwire_n]
    | cons b l2 =>
      cases l2 with
      | nil =>
        have hstep_two : ∀ (a' : ℕ),
            (∀ x, wireVal (n + 1) C.gates x (n + 1 + j) =
              if h.op = PEqualNP.CircuitLowerBounds.GateOp.and then
                wireVal (n + 1) C.gates x n && wireAt (n + 1) C.gates (n + 1 + j) a' x
              else
                wireVal (n + 1) C.gates x n || wireAt (n + 1) C.gates (n + 1 + j) a' x) → False := by
          intro a' hform
          by_cases ha_eq : a' = n
          · subst ha_eq
            apply hcontra_of_copy
            intro x
            rw [hform x, hwire_n x]
            rcases hop with hand | hor
            · simp [hand]
            · simp [hor]
          · have ha_indep : ∀ y : Fin n → Bool,
                wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) =
                wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y true) := by
              intro y
              unfold wireAt
              split_ifs with hlt
              · exact wires_indep_before n j C y huniq a' hlt ha_eq
              · rfl
            rcases hop with hand | hor
            · by_cases hall : ∀ y : Fin n → Bool,
                  wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) = true
              · apply hcontra_of_copy
                intro x
                have hax : wireAt (n + 1) C.gates (n + 1 + j) a' x = true := by
                  set y := fun i : Fin n => x i.castSucc
                  have hx_eq : x = Fin.snoc y (x (Fin.last n)) := (snoc_eq_self x).symm
                  rw [hx_eq]
                  cases x (Fin.last n)
                  · exact hall y
                  · rw [← ha_indep y]; exact hall y
                rw [hform x, hand, hax]
                simp
              · push Not at hall
                obtain ⟨y, hy⟩ := hall
                have hyf : wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) = false := by
                  cases h1 : wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) <;> simp_all
                apply hcontra_of_skip y
                rw [hform (Fin.snoc y false), hform (Fin.snoc y true), hand]
                simp [← ha_indep y, hyf]
            · by_cases hall : ∀ y : Fin n → Bool,
                  wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) = false
              · apply hcontra_of_copy
                intro x
                have hax : wireAt (n + 1) C.gates (n + 1 + j) a' x = false := by
                  set y := fun i : Fin n => x i.castSucc
                  have hx_eq : x = Fin.snoc y (x (Fin.last n)) := (snoc_eq_self x).symm
                  rw [hx_eq]
                  cases x (Fin.last n)
                  · exact hall y
                  · rw [← ha_indep y]; exact hall y
                rw [hform x, hor, hax]
                simp
              · push Not at hall
                obtain ⟨y, hy⟩ := hall
                have hyt : wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) = true := by
                  cases h1 : wireAt (n + 1) C.gates (n + 1 + j) a' (Fin.snoc y false) <;> simp_all
                apply hcontra_of_skip y
                rw [hform (Fin.snoc y false), hform (Fin.snoc y true), hor]
                simp [← ha_indep y, hyt]
        rw [hin] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · apply hstep_two b
          intro x
          rw [wireVal_gate (n + 1) C.gates x hj, hgate_eq, hin]
          rcases hop with hand | hor
          · simp [hand, PEqualNP.CircuitLowerBounds.GateOp.eval, hwire_n]
          · simp [hor, PEqualNP.CircuitLowerBounds.GateOp.eval, hwire_n]
        · apply hstep_two a
          intro x
          rw [wireVal_gate (n + 1) C.gates x hj, hgate_eq, hin]
          rcases hop with hand | hor
          · simp [hand, PEqualNP.CircuitLowerBounds.GateOp.eval, hwire_n, Bool.and_comm]
          · simp [hor, PEqualNP.CircuitLowerBounds.GateOp.eval, hwire_n, Bool.or_comm]
      | cons c l3 =>
        rw [hin] at hlen_le; simp at hlen_le
