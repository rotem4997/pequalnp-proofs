import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264_aux
open PEqualNP.CircuitLowerBounds

-- evaluation toolkit (step, val, val_snoc, val_ge, val_lt) copied from the L_meta_2986 / L_meta_1406 files

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

lemma val_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = val ([] : List Gate) x i := by
  rw [val_lt gs x i hi, val_lt [] x i hi]

/-- re-indexing of the wires: the first `a` inputs stay, everything else moves up by `n`. -/
def phi (a n : ℕ) (w : ℕ) : ℕ := if w < a then w else w + n

def rho (a n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi a n)⟩

lemma phi_lt (a n : ℕ) (ha : a ≤ n) (i : ℕ) (hi : i < n) : phi a n i < n + n := by
  unfold phi
  split_ifs <;> omega

def zof (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) : Fin n → Bool :=
  fun i => x ⟨phi a n i.val, phi_lt a n ha i.val i.isLt⟩

lemma reidx (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) (z : Fin n → Bool)
    (hz : ∀ (i : ℕ) (hi : i < n) (h2 : phi a n i < n + n), z ⟨i, hi⟩ = x ⟨phi a n i, h2⟩) :
    ∀ (gs : List Gate) (w : ℕ), val (gs.map (rho a n)) x (phi a n w) = val gs z w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil]
    rw [val_nil, val_nil]
    by_cases hw : w < n
    · have hp := phi_lt a n ha w hw
      rw [dif_pos hp, dif_pos hw]
      exact (hz w hw hp).symm
    · have hp : ¬ phi a n w < n + n := by
        unfold phi
        split_ifs <;> omega
      rw [dif_neg hp, dif_neg hw]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_cons, List.map_nil, val_snoc, val_snoc, List.length_map]
    have key : phi a n w = n + n + gs.length ↔ w = n + gs.length := by
      unfold phi
      split_ifs <;> omega
    by_cases hw : w = n + gs.length
    · rw [if_pos (key.2 hw), if_pos hw]
      show g.op.eval (List.map (fun j => val (gs.map (rho a n)) x j) (g.inputs.map (phi a n))) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [if_neg (fun h => hw (key.1 h)), if_neg hw]
      exact ih w

/-- well-formed gate lists: AND/OR, two inputs, each input earlier. -/
def WF (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m + j

lemma wf_two (m : ℕ) (gs : List Gate) (a b c : ℕ) (hwf : WF m gs)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    WF m (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) := by
  intro j g hj
  rcases lt_or_ge j gs.length with h | h
  · rw [List.getElem?_append_left h] at hj
    exact hwf j g hj
  · rw [List.getElem?_append_right h] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = gs.length + k := ⟨j - gs.length, by omega⟩
    rw [Nat.add_sub_cancel_left] at hj
    match k, hj with
    | 0, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inl rfl, rfl, by intro i hi; simp at hi; omega⟩
    | 1, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inr rfl, rfl, by intro i hi; simp at hi; omega⟩
    | k + 2, hj => simp at hj

lemma val_two_new {m : ℕ} (gs : List Gate) (a b c : ℕ) (x : Fin m → Bool)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    val (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) x (m + gs.length + 1)
      = (val gs x c || (val gs x a && val gs x b)) := by
  have happ : gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [c, m + gs.length]⟩]
      = (gs ++ [⟨GateOp.and, [a, b]⟩]) ++ [⟨GateOp.or, [c, m + gs.length]⟩] := by simp
  have hl1 : (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length = gs.length + 1 := by simp
  rw [happ, val_snoc, if_pos (by omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [val_snoc, if_neg (by omega), val_snoc, if_pos rfl]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true]

/-- append two gates per extra pair. -/
def ext (n : ℕ) : List (ℕ × ℕ) → List Gate → ℕ → List Gate × ℕ
  | [], gs, out => (gs, out)
  | e :: E, gs, out =>
    ext n E (gs ++ [⟨GateOp.and, [e.1, n + e.2]⟩, ⟨GateOp.or, [out, n + n + gs.length]⟩])
      (n + n + gs.length + 1)

lemma ext_cons (n : ℕ) (e : ℕ × ℕ) (E : List (ℕ × ℕ)) (gs : List Gate) (out : ℕ) :
    ext n (e :: E) gs out =
      ext n E (gs ++ [⟨GateOp.and, [e.1, n + e.2]⟩, ⟨GateOp.or, [out, n + n + gs.length]⟩])
        (n + n + gs.length + 1) := rfl

lemma ext_struct (n : ℕ) : ∀ (E : List (ℕ × ℕ)) (gs : List Gate) (out : ℕ),
    out < n + n + gs.length → (∀ e ∈ E, e.1 < n ∧ e.2 < n) → WF (n + n) gs →
    (ext n E gs out).1.length = gs.length + 2 * E.length ∧
    (ext n E gs out).2 < n + n + (ext n E gs out).1.length ∧
    WF (n + n) (ext n E gs out).1 := by
  intro E
  induction E with
  | nil =>
    intro gs out hout _ hwf
    exact ⟨by simp [ext], hout, hwf⟩
  | cons e E ih =>
    intro gs out hout hE hwf
    rw [ext_cons]
    obtain ⟨he1, he2⟩ := hE e (by simp)
    have hl2 : (gs ++ [(⟨GateOp.and, [e.1, n + e.2]⟩ : Gate),
        ⟨GateOp.or, [out, n + n + gs.length]⟩]).length = gs.length + 2 := by simp
    obtain ⟨h1, h2, h3⟩ := ih (gs ++ [⟨GateOp.and, [e.1, n + e.2]⟩,
        ⟨GateOp.or, [out, n + n + gs.length]⟩]) (n + n + gs.length + 1) (by omega)
      (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))
      (wf_two (n + n) gs e.1 (n + e.2) out hwf (by omega) (by omega) hout)
    refine ⟨?_, h2, h3⟩
    rw [h1, hl2, List.length_cons]
    omega

lemma ext_val (n : ℕ) (x : Fin (n + n) → Bool) : ∀ (E : List (ℕ × ℕ)) (gs : List Gate) (out : ℕ),
    out < n + n + gs.length → (∀ e ∈ E, e.1 < n ∧ e.2 < n) →
    val (ext n E gs out).1 x (ext n E gs out).2 =
      (val gs x out ||
        E.any (fun e => val ([] : List Gate) x e.1 && val ([] : List Gate) x (n + e.2))) := by
  intro E
  induction E with
  | nil =>
    intro gs out _ _
    simp [ext]
  | cons e E ih =>
    intro gs out hout hE
    rw [ext_cons]
    obtain ⟨he1, he2⟩ := hE e (by simp)
    have hl2 : (gs ++ [(⟨GateOp.and, [e.1, n + e.2]⟩ : Gate),
        ⟨GateOp.or, [out, n + n + gs.length]⟩]).length = gs.length + 2 := by simp
    rw [ih (gs ++ [(⟨GateOp.and, [e.1, n + e.2]⟩ : Gate),
        (⟨GateOp.or, [out, n + n + gs.length]⟩ : Gate)]) (n + n + gs.length + 1) (by omega)
      (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))]
    rw [val_two_new gs e.1 (n + e.2) out x (by omega) (by omega) hout]
    rw [List.any_cons, ← Bool.or_assoc, val_in gs x e.1 (by omega),
      val_in gs x (n + e.2) (by omega)]

lemma wf_map (a n : ℕ) (ha : a ≤ n) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    WF (n + n) (C.gates.map (rho a n)) := by
  obtain ⟨hC1, hC2, hC3⟩ := hC
  intro j g hj
  rw [List.getElem?_map] at hj
  cases h : C.gates[j]? with
  | none =>
    rw [h] at hj
    simp at hj
  | some g0 =>
    rw [h] at hj
    simp at hj
    subst hj
    have hmem : g0 ∈ C.gates := List.mem_of_getElem? h
    have hjl : j < C.gates.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at h
      cases h
    refine ⟨hC1 g0 hmem, ?_, ?_⟩
    · show (g0.inputs.map (phi a n)).length = 2
      rw [List.length_map]
      exact hC3 g0 hmem
    · intro i hi
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
      have hwl : w < n + j := hC2 j hjl w (by
        show w ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs
        rw [List.getD_eq_getElem?_getD, h]
        exact hw)
      unfold phi
      split_ifs <;> omega

lemma isAO2_of_wf (m : ℕ) (gs : List Gate) (out : ℕ) (hwf : WF m gs) :
    PEqualNP.TopForm.IsAO2 m (⟨gs, out⟩ : Circuit) := by
  unfold PEqualNP.TopForm.IsAO2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have hi' : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hi'
    exact (hwf j _ (List.getElem?_eq_getElem hj')).2.2 i hi'
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).2.1

noncomputable def pairs {n : ℕ} (S : Finset (Fin n × Fin n)) : List (ℕ × ℕ) :=
  S.toList.map (fun e => (e.1.val, e.2.val))

lemma pairs_length {n : ℕ} (S : Finset (Fin n × Fin n)) : (pairs S).length = S.card := by
  unfold pairs
  rw [List.length_map, Finset.length_toList]

lemma pairs_lt {n : ℕ} (S : Finset (Fin n × Fin n)) : ∀ e ∈ pairs S, e.1 < n ∧ e.2 < n := by
  intro e he
  obtain ⟨e0, _, rfl⟩ := List.mem_map.1 he
  exact ⟨e0.1.isLt, e0.2.isLt⟩

lemma pairs_any {n : ℕ} (S : Finset (Fin n × Fin n)) (x : Fin (n + n) → Bool) :
    (pairs S).any (fun e => val ([] : List Gate) x e.1 && val ([] : List Gate) x (n + e.2)) = true
      ↔ ∃ (u v : Fin n), (u, v) ∈ S ∧ x (Fin.castAdd n u) = true ∧ x (Fin.natAdd n v) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.1 he
    rw [Bool.and_eq_true] at h
    have h1 : val ([] : List Gate) x u.val = true := h.1
    have h2 : val ([] : List Gate) x (n + v.val) = true := h.2
    have hu := u.isLt
    have hv := v.isLt
    rw [val_lt [] x u.val (by omega)] at h1
    rw [val_lt [] x (n + v.val) (by omega)] at h2
    exact ⟨u, v, Finset.mem_toList.1 huv, h1, h2⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨(u.val, v.val), List.mem_map.2 ⟨(u, v), Finset.mem_toList.2 huv, rfl⟩, ?_⟩
    have hu' := u.isLt
    have hv' := v.isLt
    show (val ([] : List Gate) x u.val && val ([] : List Gate) x (n + v.val)) = true
    rw [val_lt [] x u.val (by omega), val_lt [] x (n + v.val) (by omega), Bool.and_eq_true]
    exact ⟨hu, hv⟩

lemma zof_cast (x1 x2 : ℕ) (ha : x1 ≤ x1 + x2) (x : Fin (x1 + x2 + (x1 + x2)) → Bool)
    (p : Fin x1) :
    zof x1 (x1 + x2) ha x (Fin.castAdd x2 p) = x (Fin.castAdd (x1 + x2) (Fin.castAdd x2 p)) := by
  unfold zof
  congr 1
  apply Fin.ext
  show phi x1 (x1 + x2) (Fin.castAdd x2 p).val = (Fin.castAdd (x1 + x2) (Fin.castAdd x2 p)).val
  simp only [Fin.val_castAdd]
  have hp := p.isLt
  unfold phi
  rw [if_pos hp]

lemma zof_nat (x1 x2 : ℕ) (ha : x1 ≤ x1 + x2) (x : Fin (x1 + x2 + (x1 + x2)) → Bool)
    (l : Fin x2) :
    zof x1 (x1 + x2) ha x (Fin.natAdd x1 l) = x (Fin.natAdd (x1 + x2) (Fin.natAdd x1 l)) := by
  unfold zof
  congr 1
  apply Fin.ext
  show phi x1 (x1 + x2) (Fin.natAdd x1 l).val = (Fin.natAdd (x1 + x2) (Fin.natAdd x1 l)).val
  simp only [Fin.val_natAdd]
  unfold phi
  rw [if_neg (by omega)]
  omega

lemma old_iff (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (ha : x1 ≤ x1 + x2)
    (x : Fin (x1 + x2 + (x1 + x2)) → Bool) :
    (∃ (p : Fin x1) (l : Fin x2), (p, l) ∈ x3 ∧
        zof x1 (x1 + x2) ha x (Fin.castAdd x2 p) = true ∧
        zof x1 (x1 + x2) ha x (Fin.natAdd x1 l) = true) ↔
      ∃ (u v : Fin (x1 + x2)), (u, v) ∈ Finset.image
          (fun (e : Fin x1 × Fin x2) => (Fin.castAdd x2 e.1, Fin.natAdd x1 e.2)) x3 ∧
        x (Fin.castAdd (x1 + x2) u) = true ∧ x (Fin.natAdd (x1 + x2) v) = true := by
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    refine ⟨Fin.castAdd x2 p, Fin.natAdd x1 l, Finset.mem_image.2 ⟨(p, l), hpl, rfl⟩, ?_, ?_⟩
    · rw [← zof_cast x1 x2 ha x p]
      exact hp
    · rw [← zof_nat x1 x2 ha x l]
      exact hl
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨⟨p, l⟩, hpl, heq⟩ := Finset.mem_image.1 huv
    have h1 : Fin.castAdd x2 p = u := congrArg Prod.fst heq
    have h2 : Fin.natAdd x1 l = v := congrArg Prod.snd heq
    subst h1
    subst h2
    refine ⟨p, l, hpl, ?_, ?_⟩
    · rw [zof_cast x1 x2 ha x p]
      exact hu
    · rw [zof_nat x1 x2 ha x l]
      exact hv

theorem main (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (C : Circuit)
    (hne : x3.Nonempty) (hC : PEqualNP.TopForm.IsAO2 (x1 + x2) C)
    (hf : ∀ (z : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z =
      decide (∃ (p : Fin x1) (l : Fin x2), (p, l) ∈ x3 ∧ z (Fin.castAdd x2 p) = true ∧
        z (Fin.natAdd x1 l) = true))
    (x10 : Finset (Fin (x1 + x2) × Fin (x1 + x2))) :
    ∃ (D : Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2 + (x1 + x2)) D ∧
      D.size ≤ C.size + 2 * x10.card ∧
      ∀ (x : Fin (x1 + x2 + (x1 + x2)) → Bool),
        PEqualNP.MetaComplexity.circuitFun (x1 + x2 + (x1 + x2)) D x =
          decide (∃ (u v : Fin (x1 + x2)), (u, v) ∈ Finset.image
              (fun (e : Fin x1 × Fin x2) => (Fin.castAdd x2 e.1, Fin.natAdd x1 e.2)) x3 ∪ x10 ∧
            x (Fin.castAdd (x1 + x2) u) = true ∧ x (Fin.natAdd (x1 + x2) v) = true) := by
  have ha : x1 ≤ x1 + x2 := by omega
  have hout : C.output < x1 + x2 + C.gates.length := by
    by_contra hc
    obtain ⟨⟨p, l⟩, hpl⟩ := hne
    have h := hf (fun _ => true)
    have h2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C (fun _ => true)
        = val C.gates (fun _ : Fin (x1 + x2) => true) C.output := rfl
    rw [h2, val_ge _ _ _ (by omega)] at h
    exact of_decide_eq_false h.symm ⟨p, l, hpl, rfl, rfl⟩
  have hwf0 := wf_map x1 (x1 + x2) ha C hC
  have hout' : phi x1 (x1 + x2) C.output
      < x1 + x2 + (x1 + x2) + (C.gates.map (rho x1 (x1 + x2))).length := by
    rw [List.length_map]
    unfold phi
    split_ifs <;> omega
  obtain ⟨hl, ho, hw⟩ := ext_struct (x1 + x2) (pairs x10) _ _ hout' (pairs_lt x10) hwf0
  refine ⟨⟨(ext (x1 + x2) (pairs x10) (C.gates.map (rho x1 (x1 + x2)))
      (phi x1 (x1 + x2) C.output)).1, (ext (x1 + x2) (pairs x10) (C.gates.map (rho x1 (x1 + x2)))
      (phi x1 (x1 + x2) C.output)).2⟩, isAO2_of_wf _ _ _ hw, ?_, ?_⟩
  · show (ext (x1 + x2) (pairs x10) (C.gates.map (rho x1 (x1 + x2)))
      (phi x1 (x1 + x2) C.output)).1.length ≤ C.gates.length + 2 * x10.card
    rw [hl, List.length_map, pairs_length]
  · intro x
    show val (ext (x1 + x2) (pairs x10) (C.gates.map (rho x1 (x1 + x2)))
      (phi x1 (x1 + x2) C.output)).1 x (ext (x1 + x2) (pairs x10)
      (C.gates.map (rho x1 (x1 + x2))) (phi x1 (x1 + x2) C.output)).2 = _
    rw [ext_val (x1 + x2) x (pairs x10) _ _ hout' (pairs_lt x10)]
    rw [reidx x1 (x1 + x2) ha x (zof x1 (x1 + x2) ha x) (fun i hi h2 => rfl) C.gates C.output]
    have h2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C (zof x1 (x1 + x2) ha x)
        = val C.gates (zof x1 (x1 + x2) ha x) C.output := rfl
    rw [← h2, hf (zof x1 (x1 + x2) ha x), Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [old_iff x1 x2 x3 ha x, pairs_any x10 x]
    constructor
    · rintro (⟨u, v, h, hu, hv⟩ | ⟨u, v, h, hu, hv⟩)
      · exact ⟨u, v, Finset.mem_union_left _ h, hu, hv⟩
      · exact ⟨u, v, Finset.mem_union_right _ h, hu, hv⟩
    · rintro ⟨u, v, h, hu, hv⟩
      rcases Finset.mem_union.1 h with h | h
      · exact Or.inl ⟨u, v, h, hu, hv⟩
      · exact Or.inr ⟨u, v, h, hu, hv⟩

end PEqualNP.Outside.L_meta_3264_aux

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro x1 x2 x3 x4 h1 h2 h3
  exact PEqualNP.Outside.L_meta_3264_aux.main x1 x2 x3 x4 h1 h2 h3
