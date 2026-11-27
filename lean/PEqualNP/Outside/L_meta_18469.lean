import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18469

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

private abbrev bank {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

private theorem bankLength {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (bank gs x).length = n + gs.length := by
  have len (l : List Bool) (q : List Gate) :
      ((Circuit.mk q 0).wires l).length = l.length + q.length := by
    induction q generalizing l with
    | nil => simp [Circuit.wires]
    | cons g q ih =>
      simp only [Circuit.wires, List.foldl_cons] at ih ⊢
      rw [ih]
      simp
      omega
  simpa using len (List.ofFn x) gs

private theorem bankSnoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    bank (gs ++ [g]) x = bank gs x ++
      [g.op.eval (g.inputs.map fun j => (bank gs x).getD j false)] := by
  simp [Circuit.wires, List.foldl_append]

private abbrev Fits {n : ℕ} (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ b, ∀ x, f x = b) ∨
    ∃ i < n + gs.length, ∀ x, f x = (bank gs x).getD i false

private theorem extend {n : ℕ} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (g : Gate) (h : Fits gs f) : Fits (gs ++ [g]) f := by
  rcases h with h | ⟨i, hi, he⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, by simp; omega, fun x => ?_⟩
    rw [bankSnoc, List.getD_append _ _ _ _ (by simpa only [bankLength] using hi)]
    exact he x

private theorem addGate {n : ℕ} (gs : List Gate) (g : Gate)
    (hs : IsAO2 n (Circuit.mk gs 0))
    (ho : g.op = .and ∨ g.op = .or) (hq : g.inputs.length = 2)
    (hr : ∀ i ∈ g.inputs, i < n + gs.length) :
    IsAO2 n (Circuit.mk (gs ++ [g]) 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hs.1 a ha
    · rwa [List.mem_singleton.mp ha]
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at hi
    by_cases h : j < gs.length
    · apply hs.2.1 j h
      simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_append_left h] using hi
    · have he : j = gs.length := by simp at hj; omega
      subst j
      have hi' : i ∈ g.inputs := by simpa using hi
      exact hr i hi'
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hs.2.2 a ha
    · rwa [List.mem_singleton.mp ha]

private theorem combine {n : ℕ} (gs : List Gate) (hs : IsAO2 n (Circuit.mk gs 0))
    (op : GateOp) (ho : op = .and ∨ op = .or)
    (a b : (Fin n → Bool) → Bool) (ha : Fits gs a) (hb : Fits gs b) :
    ∃ extra : List Gate, extra.length ≤ 1 ∧
      IsAO2 n (Circuit.mk (gs ++ extra) 0) ∧ Fits (gs ++ extra) (fun x => op.eval [a x, b x]) := by
  have reuse (f : (Fin n → Bool) → Bool) (hf : Fits gs f)
      (he : ∀ x, op.eval [a x, b x] = f x) :
      ∃ extra : List Gate, extra.length ≤ 1 ∧ IsAO2 n (Circuit.mk (gs ++ extra) 0) ∧
        Fits (gs ++ extra) (fun x => op.eval [a x, b x]) := by
    refine ⟨[], by simp, by simpa using hs, ?_⟩
    simpa only [List.append_nil, funext he] using hf
  have constant (v : Bool) : Fits gs (fun _ : Fin n → Bool => v) := Or.inl ⟨v, fun _ => rfl⟩
  rcases ha with ⟨u, hu⟩ | ⟨i, hi, hai⟩
  · rcases ho with rfl | rfl <;> cases u
    · exact reuse _ (constant false) fun x => by simp [GateOp.eval, hu]
    · exact reuse b hb fun x => by simp [GateOp.eval, hu]
    · exact reuse b hb fun x => by simp [GateOp.eval, hu]
    · exact reuse _ (constant true) fun x => by simp [GateOp.eval, hu]
  · rcases hb with ⟨v, hv⟩ | ⟨j, hj, hbj⟩
    · have ha : Fits gs a := Or.inr ⟨i, hi, hai⟩
      rcases ho with rfl | rfl <;> cases v
      · exact reuse _ (constant false) fun x => by simp [GateOp.eval, hv]
      · exact reuse a ha fun x => by simp [GateOp.eval, hv]
      · exact reuse a ha fun x => by simp [GateOp.eval, hv]
      · exact reuse _ (constant true) fun x => by simp [GateOp.eval, hv]
    · let g : Gate := ⟨op, [i, j]⟩
      refine ⟨[g], by simp, addGate gs g hs ho rfl ?_, Or.inr ⟨n + gs.length, by simp, ?_⟩⟩
      · intro k hk
        simp [g] at hk
        rcases hk with rfl | rfl <;> assumption
      · intro x
        rw [bankSnoc, ← bankLength gs x, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        simp [g, hai, hbj]

private theorem normalize (n : ℕ) (source : List Gate) (hsource : Monotone2 (Circuit.mk source 0)) :
    ∃ target : List Gate, IsAO2 n (Circuit.mk target 0) ∧ target.length ≤ source.length ∧
      ∀ j, Fits target (fun x : Fin n → Bool => (bank source x).getD j false) := by
  have empty : IsAO2 n (Circuit.mk [] 0) :=
    ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly], by simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack],
      by simp⟩
  induction source using List.reverseRecOn with
  | nil =>
    refine ⟨[], empty, le_rfl, fun j => ?_⟩
    by_cases h : j < n
    · exact Or.inr ⟨j, by simpa using h, fun _ => rfl⟩
    · refine Or.inl ⟨false, fun x => List.getD_eq_default _ _ ?_⟩
      rw [bankLength]; simp; omega
  | append_singleton gs g ih =>
    obtain ⟨ds, hd, hs, rep⟩ := ih (fun q hq => hsource q (List.mem_append_left _ hq))
    have hGate := hsource g (List.mem_append_right _ (by simp))
    have hop : g.op = .and ∨ g.op = .or := by simpa using hGate.1
    have add : ∃ extra : List Gate, extra.length ≤ 1 ∧ IsAO2 n (Circuit.mk (ds ++ extra) 0) ∧
        Fits (ds ++ extra) (fun x : Fin n → Bool => g.op.eval (g.inputs.map fun j => (bank gs x).getD j false)) := by
      have hlen := hGate.2
      match hin : g.inputs, hlen with
      | [], _ => exact ⟨[], by simp, by simpa using hd, Or.inl ⟨g.op.eval [], fun x => by simp [hin]⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, by simpa using hd, ?_⟩
        rcases hop with ho | ho <;> simpa [hin, ho, GateOp.eval] using rep a
      | [a, b], _ => simpa [hin] using combine ds hd g.op hop _ _ (rep a) (rep b)
    obtain ⟨extra, he, ho, hr⟩ := add
    refine ⟨ds ++ extra, ho, by simp; omega, fun j => ?_⟩
    by_cases h : j < n + gs.length
    · have e (x : Fin n → Bool) : (bank (gs ++ [g]) x).getD j false = (bank gs x).getD j false := by
        rw [bankSnoc, List.getD_append _ _ _ _ (by simpa only [bankLength] using h)]
      simp only [e]
      match extra, he with
      | [], _ => simpa using rep j
      | [q], _ => exact extend q (rep j)
    · by_cases eq : j = n + gs.length
      · have e (x : Fin n → Bool) : (bank (gs ++ [g]) x).getD j false =
            g.op.eval (g.inputs.map fun k => (bank gs x).getD k false) := by
          rw [bankSnoc, eq, ← bankLength gs x, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          rfl
        simpa only [e] using hr
      · apply Or.inl
        refine ⟨false, fun x => List.getD_eq_default _ _ ?_⟩
        rw [bankLength]; simp; omega

theorem result (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    (∃ b, ∀ x : Fin n → Bool, circuitFun n C x = b) ∨
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C x := by
  obtain ⟨gs, h, hs, rep⟩ := normalize n C.gates hC
  rcases rep C.output with hc | ⟨i, _, hi⟩
  · exact Or.inl hc
  · exact Or.inr ⟨⟨gs, i⟩, h, hs, fun x => (hi x).symm⟩

end PEqualNP.Outside.L_meta_18469

theorem PEqualNP.Outside.L_meta_18469 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Bool), ∀ (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = x4) ∨ ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 ∧ x4.size ≤ x2.size ∧ ∀ (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 x5 := PEqualNP.Outside.L_meta_18469.result
