import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6973

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih]; simp; omega

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false = value gs[j] (run gs w) := by
  have hsplit : gs.take j ++ gs[j] :: gs.drop (j+1) = gs := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hp : (run (gs.take j) w).length = w.length + j := by
    rw [run_length, List.length_take]; omega
  have heq : run gs w = run (gs.drop (j+1))
      (run (gs.take j) w ++ [value gs[j] (run (gs.take j) w)]) := by
    rw [← run_cons, ← run_append, hsplit]
  have hpre : ∀ i, i < w.length + j + 1 → (run gs w).getD i false =
      (run (gs.take j) w ++ [value gs[j] (run (gs.take j) w)]).getD i false := by
    intro i hi
    rw [heq]
    exact run_preserves _ _ _ (by simp; omega)
  rw [hpre _ (by omega)]
  have h1 : (run (gs.take j) w ++ [value gs[j] (run (gs.take j) w)]).getD (w.length + j) false
      = value gs[j] (run (gs.take j) w) := by
    rw [← hp]
    simp [List.getD_eq_getElem?_getD]
  rw [h1]
  unfold value
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hrb i hi
  rw [hpre i (by omega)]
  exact (List.getD_append _ _ _ _ (by omega)).symm

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq, run_length]; rfl

theorem wires_gate (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.size) :
    (C.wires x).getD (n + j) false = value (gateAt C j) (C.wires x) := by
  rw [gateAt_eq C j hj, wires_eq, ← hx]
  apply run_gate
  intro i hi
  have := hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  omega

theorem gate_mono {C : Circuit} (hmono : Monotone2 C) (j : ℕ) (hj : j < C.size) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length ≤ 2 := by
  have h := hmono (gateAt C j) (by rw [gateAt_eq C j hj]; exact List.getElem_mem hj)
  simpa using h

theorem shape (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ p, l = [p]) ∨ (∃ p q, l = [p, q]) := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [p], _ => exact Or.inr (Or.inl ⟨p, rfl⟩)
  | [p, q], _ => exact Or.inr (Or.inr ⟨p, q, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h <;> omega

theorem noteq {n : ℕ} {C : Circuit} {S : Bool → List Bool → Prop}
    (H : ∀ j < C.size, ∀ c ≤ n + j, ∃ (b : Bool) (x : List Bool), S b x ∧
      (C.wires x).getD (n + j) false = b ∧
      (if c = n + j then false else (C.wires x).getD c false) = !b)
    (j : ℕ) (hj : j < C.size) (c : ℕ) (hc : c < n + j)
    (heq : ∀ b x, S b x → (C.wires x).getD (n + j) false = (C.wires x).getD c false) :
    False := by
  obtain ⟨b, x, hS, h1, h2⟩ := H j hj c hc.le
  rw [if_neg (by omega)] at h2
  rw [heq b x hS] at h1
  rw [h1] at h2
  cases b <;> simp at h2

theorem notfalse {n : ℕ} {C : Circuit} {S : Bool → List Bool → Prop}
    (H : ∀ j < C.size, ∀ c ≤ n + j, ∃ (b : Bool) (x : List Bool), S b x ∧
      (C.wires x).getD (n + j) false = b ∧
      (if c = n + j then false else (C.wires x).getD c false) = !b)
    (j : ℕ) (hj : j < C.size)
    (hconst : ∀ b x, S b x → (C.wires x).getD (n + j) false = false) : False := by
  obtain ⟨b, x, hS, h1, h2⟩ := H j hj (n + j) le_rfl
  rw [if_pos rfl] at h2
  rw [hconst b x hS] at h1
  subst h1
  simp at h2

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool → List Bool → Prop),   (∀ (x4 : Bool) (x5 : List Bool), x3 x4 x5 → x5.length = x1) →     (∃ (x5 : List Bool), x3 Bool.true x5) →       (∃ (x6 : List Bool), x3 Bool.false x6) →         (0 : ℕ) < x2.size →           PEqualNP.MetaComplexity.Monotone2 x2 →             PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 →               (∀ (x10 : Bool) (x11 : List Bool), x3 x10 x11 → x2.eval x11 = x10) →                 (∀ x11 < x2.size, ∀ x13 ≤ x1 + x11, ∃ (x15 : Bool) (x16 : List Bool), x3 x15 x16 ∧ (x2.wires x16).getD (x1 + x11) Bool.false = x15 ∧ (if x13 = x1 + x11 then Bool.false else (x2.wires x16).getD x13 Bool.false) = !x15) →                   x2.output + (1 : ℕ) = x1 + x2.size ∧                     ∀ x12 < x2.size,                       have x14 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12;                       (∃ (x15 : ℕ) (x16 : ℕ), x15 ≠ x16 ∧ x14.inputs = [x15, x16]) ∨ x14.inputs = [] ∧ x2.output ≠ x1 + x12 ∧ (∀ x15 < x2.size, x1 + x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs) ∧ ∀ x15 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs = [] → x15 = x12 := by
  intro n C S hlen ht hf hsize hmono hrb hcorr H
  have hlast : C.size - 1 < C.size := by omega
  have part1 : C.output + 1 = n + C.size := by
    obtain ⟨t, htS⟩ := ht
    by_contra hne
    rcases Nat.lt_or_ge C.output (n + (C.size - 1)) with hlt | hge
    · obtain ⟨b, x, hS, h1, h2⟩ := H (C.size - 1) hlast C.output hlt.le
      rw [if_neg (by omega)] at h2
      have he := hcorr b x hS
      unfold Circuit.eval at he
      rw [he] at h2
      cases b <;> simp at h2
    · have hgt : n + C.size ≤ C.output := by omega
      have he := hcorr true t htS
      unfold Circuit.eval at he
      have hnone : (C.wires t).getD C.output false = false := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [wires_len, hlen true t htS]; omega)]
        rfl
      rw [hnone] at he
      exact absurd he (by decide)
  refine ⟨part1, ?_⟩
  intro j hj
  dsimp only
  have gv : ∀ k < C.size, ∀ b x, S b x →
      (C.wires x).getD (n + k) false = value (gateAt C k) (C.wires x) :=
    fun k hk b x hS => wires_gate n C hrb x (hlen b x hS) k hk
  have empty_true : ∀ k < C.size, (gateAt C k).inputs = [] →
      ∀ b x, S b x → (C.wires x).getD (n + k) false = true := by
    intro k hk he
    rcases (gate_mono hmono k hk).1 with hop | hop
    · intro b x hS
      rw [gv k hk b x hS]
      simp [value, hop, he, GateOp.eval]
    · exfalso
      apply notfalse H k hk
      intro b x hS
      rw [gv k hk b x hS]
      simp [value, hop, he, GateOp.eval]
  have hmj := gate_mono hmono j hj
  rcases shape _ hmj.2 with hg | ⟨a, hg⟩ | ⟨a, a', hg⟩
  · right
    refine ⟨hg, ?_, ?_, ?_⟩
    · intro hout
      obtain ⟨f, hfS⟩ := hf
      have h1 := hcorr false f hfS
      unfold Circuit.eval at h1
      rw [hout, empty_true j hj hg false f hfS] at h1
      exact absurd h1 (by decide)
    · intro k hk hmem
      have hlt : n + j < n + k := hrb k hk (n + j) hmem
      have hmk := gate_mono hmono k hk
      rcases shape _ hmk.2 with hgk | ⟨p, hgk⟩ | ⟨p, q, hgk⟩
      · rw [hgk] at hmem
        simp at hmem
      · rw [hgk] at hmem
        have hmem' : n + j = p := by simpa using hmem
        subst hmem'
        apply noteq H k hk (n + j) hlt
        intro b x hS
        rw [gv k hk b x hS]
        rcases hmk.1 with hop | hop <;> simp [value, hop, hgk, GateOp.eval]
      · rw [hgk] at hmem
        have hp : p < n + k := hrb k hk p (by rw [hgk]; simp)
        have hq : q < n + k := hrb k hk q (by rw [hgk]; simp)
        have hmem' : n + j = p ∨ n + j = q := by simpa using hmem
        rcases hmk.1 with hop | hop
        · rcases hmem' with e | e
          · apply noteq H k hk q hq
            intro b x hS
            rw [gv k hk b x hS]
            have hT := empty_true j hj hg b x hS
            rw [e] at hT
            simp only [List.getD_eq_getElem?_getD] at hT
            simp [value, hop, hgk, GateOp.eval, hT]
          · apply noteq H k hk p hp
            intro b x hS
            rw [gv k hk b x hS]
            have hT := empty_true j hj hg b x hS
            rw [e] at hT
            simp only [List.getD_eq_getElem?_getD] at hT
            simp [value, hop, hgk, GateOp.eval, hT]
        · apply noteq H k hk (n + j) hlt
          intro b x hS
          rw [gv k hk b x hS]
          have hT := empty_true j hj hg b x hS
          rw [hT]
          rcases hmem' with e | e
          · rw [e, List.getD_eq_getElem?_getD] at hT
            simp [value, hop, hgk, GateOp.eval, hT]
          · rw [e, List.getD_eq_getElem?_getD] at hT
            simp [value, hop, hgk, GateOp.eval, hT]
    · intro k hk hek
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hkj | hkj
      · apply noteq H j hj (n + k) (by omega)
        intro b x hS
        rw [empty_true j hj hg b x hS, empty_true k hk hek b x hS]
      · apply noteq H k hk (n + j) (by omega)
        intro b x hS
        rw [empty_true j hj hg b x hS, empty_true k hk hek b x hS]
  · exfalso
    have ha : a < n + j := hrb j hj a (by rw [hg]; simp)
    apply noteq H j hj a ha
    intro b x hS
    rw [gv j hj b x hS]
    rcases hmj.1 with hop | hop <;> simp [value, hop, hg, GateOp.eval]
  · by_cases haa : a = a'
    · exfalso
      subst haa
      have ha : a < n + j := hrb j hj a (by rw [hg]; simp)
      apply noteq H j hj a ha
      intro b x hS
      rw [gv j hj b x hS]
      rcases hmj.1 with hop | hop <;> simp [value, hop, hg, GateOp.eval]
    · left
      exact ⟨a, a', haa, hg⟩

end PEqualNP.Outside.L_meta_6973

theorem PEqualNP.Outside.L_meta_6973 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool → List Bool → Prop),   (∀ (x4 : Bool) (x5 : List Bool), x3 x4 x5 → x5.length = x1) →     (∃ (x5 : List Bool), x3 Bool.true x5) →       (∃ (x6 : List Bool), x3 Bool.false x6) →         (0 : ℕ) < x2.size →           PEqualNP.MetaComplexity.Monotone2 x2 →             PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 →               (∀ (x10 : Bool) (x11 : List Bool), x3 x10 x11 → x2.eval x11 = x10) →                 (∀ x11 < x2.size, ∀ x13 ≤ x1 + x11, ∃ (x15 : Bool) (x16 : List Bool), x3 x15 x16 ∧ (x2.wires x16).getD (x1 + x11) Bool.false = x15 ∧ (if x13 = x1 + x11 then Bool.false else (x2.wires x16).getD x13 Bool.false) = !x15) →                   x2.output + (1 : ℕ) = x1 + x2.size ∧                     ∀ x12 < x2.size,                       have x14 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12;                       (∃ (x15 : ℕ) (x16 : ℕ), x15 ≠ x16 ∧ x14.inputs = [x15, x16]) ∨ x14.inputs = [] ∧ x2.output ≠ x1 + x12 ∧ (∀ x15 < x2.size, x1 + x12 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs) ∧ ∀ x15 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs = [] → x15 = x12 := by
  exact PEqualNP.Outside.L_meta_6973.main
