import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3684
open PEqualNP.CircuitLowerBounds

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

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

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

theorem rep_false (n i : ℕ) : (List.replicate n false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

open PEqualNP.EdgeOwnership in
theorem core (N : ℕ) (C C3 : Circuit) (hout : C.output = C3.output)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hA : C.eval (List.ofFn fun x6 : Fin (N + N) =>
      Fin.addCases (fun _ : Fin N => true) (fun _ : Fin N => false) x6) = false)
    (p l : Fin N)
    (h2 : C.eval (List.ofFn (pairInput (Fin.castAdd N p) (Fin.natAdd N l))) = true)
    (h3 : C3.eval (List.ofFn (pairInput (Fin.castAdd N p) (Fin.natAdd N l))) = false) :
    ∃ k : Fin C.size, (C.wires (List.replicate (N + N) false)).getD (N + N + k.1) false = false ∧
      gateVal (N + N) C k.1 (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true ∧
      ∃ j : Fin 2, (C.gates[k.1]'k.2).inputs[j.1]? = some (N + l.1) := by
  obtain ⟨P, hPdef⟩ : ∃ P : Fin (N + N) → Bool,
      P = pairInput (Fin.castAdd N p) (Fin.natAdd N l) := ⟨_, rfl⟩
  obtain ⟨Sg, hSdef⟩ : ∃ Sg : Fin (N + N) → Bool,
      Sg = fun v => decide (v = Fin.castAdd N p) := ⟨_, rfl⟩
  rw [← hPdef] at h2 h3 ⊢
  have hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hC g hg).2⟩
    rcases (hC g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have mono : ∀ (x y : Fin (N + N) → Bool), (∀ v, x v = true → y v = true) → ∀ i,
      (wf C.gates (List.ofFn x)).getD i false = true →
      (wf C.gates (List.ofFn y)).getD i false = true := by
    intro x y hxy i
    exact mono2 C.gates hleg _ _ (by simp) (ofFn_mono (N + N) x y hxy) i
  have hSP : ∀ v, Sg v = true → P v = true := by
    intro v hv
    rw [hSdef] at hv
    rw [hPdef]
    exact decide_eq_true (Or.inl (of_decide_eq_true hv))
  have hPout : (wf C.gates (List.ofFn P)).getD C.output false = true := h2
  have hA' : (wf C.gates (List.ofFn fun x6 : Fin (N + N) =>
      Fin.addCases (fun _ : Fin N => true) (fun _ : Fin N => false) x6)).getD C.output false
        = false := hA
  have hSout : (wf C.gates (List.ofFn Sg)).getD C.output false = false := by
    cases hh : (wf C.gates (List.ofFn Sg)).getD C.output false with
    | false => rfl
    | true =>
      have := mono Sg (fun x6 : Fin (N + N) =>
          Fin.addCases (fun _ : Fin N => true) (fun _ : Fin N => false) x6) (by
        intro v hv
        rw [hSdef] at hv
        rw [of_decide_eq_true hv]
        exact Fin.addCases_left _) _ hh
      rw [hA'] at this
      exact absurd this (by decide)
  have hn : N + N ≤ C.output := by
    by_contra hlt
    have h3' : (wf C3.gates (List.ofFn P)).getD C3.output false = false := h3
    rw [← hout, wf_keep _ _ _ (by rw [List.length_ofFn]; omega)] at h3'
    rw [wf_keep _ _ _ (by rw [List.length_ofFn]; omega), h3'] at hPout
    exact absurd hPout (by decide)
  have hk0 : C.output - (N + N) < C.gates.length := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_ofFn]; omega)] at hPout
    exact absurd hPout (by decide)
  have e0 : N + N + (C.output - (N + N)) = C.output := by omega
  have hex : ∃ k, k < C.gates.length ∧ (wf C.gates (List.ofFn P)).getD (N + N + k) false = true ∧
      (wf C.gates (List.ofFn Sg)).getD (N + N + k) false = false :=
    ⟨C.output - (N + N), hk0, by rw [e0]; exact hPout, by rw [e0]; exact hSout⟩
  classical
  have hk := Nat.find_spec hex
  have hmin : ∀ h, h < Nat.find hex → ¬ (h < C.gates.length ∧
      (wf C.gates (List.ofFn P)).getD (N + N + h) false = true ∧
      (wf C.gates (List.ofFn Sg)).getD (N + N + h) false = false) :=
    fun h hh => Nat.find_min hex hh
  generalize Nat.find hex = k at hk hmin
  obtain ⟨hkl, hkP, hkS⟩ := hk
  have gP := gate_val C.gates (List.ofFn P) k hkl
  have gS := gate_val C.gates (List.ofFn Sg) k hkl
  rw [List.length_ofFn] at gP gS
  have hin : N + l.1 ∈ (C.gates[k]).inputs := by
    by_contra hnot
    have heq : (C.gates[k].inputs.map fun i => (wf (C.gates.take k) (List.ofFn P)).getD i false)
        = (C.gates[k].inputs.map fun i => (wf (C.gates.take k) (List.ofFn Sg)).getD i false) := by
      apply List.map_congr_left
      intro i hi
      have hne : i ≠ N + l.1 := fun e => hnot (e ▸ hi)
      by_cases h1 : i < N + N
      · rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact h1),
          wf_keep _ _ i (by rw [List.length_ofFn]; exact h1),
          show (List.ofFn P).getD i false = P ⟨i, h1⟩ from getD_ofFn P ⟨i, h1⟩,
          show (List.ofFn Sg).getD i false = Sg ⟨i, h1⟩ from getD_ofFn Sg ⟨i, h1⟩]
        have hne2 : (⟨i, h1⟩ : Fin (N + N)) ≠ Fin.natAdd N l := by
          intro e
          have := congrArg Fin.val e
          simp at this
          exact hne (by omega)
        rw [hPdef, hSdef]
        show decide (_ ∨ _) = decide _
        exact decide_eq_decide.2 ⟨fun h => h.resolve_right hne2, Or.inl⟩
      · by_cases h2 : i < N + N + k
        · rw [← wire_take C.gates (List.ofFn P) k i (by rw [List.length_ofFn]; exact h2) (le_of_lt hkl),
            ← wire_take C.gates (List.ofFn Sg) k i (by rw [List.length_ofFn]; exact h2) (le_of_lt hkl)]
          have e : N + N + (i - (N + N)) = i := by omega
          apply Bool.eq_iff_iff.2
          constructor
          · intro hp
            cases hs : (wf C.gates (List.ofFn Sg)).getD i false with
            | true => rfl
            | false =>
              exact absurd ⟨by omega, by rw [e]; exact hp, by rw [e]; exact hs⟩
                (hmin (i - (N + N)) (by omega))
          · exact mono Sg P hSP i
        · rw [List.getD_eq_default _ _ (by
              rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hkl)]; omega),
            List.getD_eq_default _ _ (by
              rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hkl)]; omega)]
    rw [gP, heq, ← gS, hkS] at hkP
    exact absurd hkP (by decide)
  refine ⟨⟨k, hkl⟩, ?_, hkP, ?_⟩
  · cases hz : (C.wires (List.replicate (N + N) false)).getD (N + N + k) false with
    | false => rfl
    | true =>
      have := mono2 C.gates hleg (List.replicate (N + N) false) (List.ofFn Sg) (by simp)
        (fun i hi => absurd hi (by rw [rep_false]; decide)) (N + N + k) hz
      rw [hkS] at this
      exact absurd this (by decide)
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hin
    have hj2 := (List.getElem?_eq_some_iff.1 hj).1
    have := (hC _ (List.getElem_mem hkl)).2
    exact ⟨⟨j, by omega⟩, hj⟩

end PEqualNP.Outside.L_meta_3684

open PEqualNP.Outside.L_meta_3684 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3684 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x2.output = x3.output →     PEqualNP.MetaComplexity.Monotone2 x2 →       x2.eval (List.ofFn fun (x6 : Fin (x1 + x1)) => Fin.addCases (fun (x7 : Fin x1) => Bool.true) (fun (x7 : Fin x1) => Bool.false) x6) = Bool.false →         have x7 : Fin x1 → Fin x1 → Fin (x1 + x1) → Bool := fun (x7 x8 : Fin x1) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x1 x7) (Fin.natAdd x1 x8);         ∀ (x8 : Fin x1 → Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x10 ∈ x8 x9 → x2.eval (List.ofFn (x7 x10 x9)) = Bool.true ∧ x3.eval (List.ofFn (x7 x10 x9)) = Bool.false) → Fintype.card { x10 : Fin x1 // (x8 x10).Nonempty } ≤ (2 : ℕ) * Fintype.card { x10 : Fin x2.size // (x2.wires (List.replicate (x1 + x1) Bool.false)).getD (x1 + x1 + ↑x10) Bool.false = Bool.false ∧ ∃ (x11 : Fin x1), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (x1 + x1) x2 (↑x10) (x7 x12 x11) = Bool.true } := by
  intro N C C3 hout hC hA F S hS
  have key : ∀ l : {l : Fin N // (S l).Nonempty},
      ∃ (t : {x10 : Fin C.size // (C.wires (List.replicate (N + N) false)).getD (N + N + x10.1) false
          = false ∧ ∃ x11 : Fin N, ∃ x12 ∈ S x11,
            PEqualNP.EdgeOwnership.gateVal (N + N) C x10.1 (F x12 x11) = true}) (j : Fin 2),
        (C.gates[t.1.1]'t.1.2).inputs[j.1]? = some (N + l.1.1) := by
    intro ⟨l, p, hp⟩
    obtain ⟨k, h1, h2, j, hj⟩ := core N C C3 hout hC hA p l (hS l p hp).1 (hS l p hp).2
    exact ⟨⟨k, h1, l, p, hp, h2⟩, j, hj⟩
  choose g j hgj using key
  have inj : Function.Injective (fun l => (g l, j l)) := by
    intro a b hab
    have h1 : g a = g b := (Prod.ext_iff.1 hab).1
    have h2 : j a = j b := (Prod.ext_iff.1 hab).2
    have ha := hgj a
    have hb := hgj b
    rw [h1, h2] at ha
    rw [ha] at hb
    have := Option.some.inj hb
    apply Subtype.ext
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective _ inj
  rw [Fintype.card_prod, Fintype.card_fin] at hcard
  exact le_trans hcard (le_of_eq (Nat.mul_comm _ _))
