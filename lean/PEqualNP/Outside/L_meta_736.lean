import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_736_aux
open PEqualNP.CircuitLowerBounds

noncomputable def rename {n n' : ℕ} (e : Fin n' → Fin n) (G i : ℕ) : ℕ := by
  classical
  exact if hi : i < n then
    if h : ∃ j, e j = ⟨i,hi⟩ then (Classical.choose h).val else n'
  else if i < n + G then n' + 1 + (i-n) else n' + 1 + G

lemma rename_gate {n n' : ℕ} (e : Fin n' → Fin n) (G t i : ℕ) (ht : t < G) :
    rename e G i = n' + 1 + t ↔ i = n + t := by
  classical
  unfold rename
  split
  · rename_i hi
    split
    · rename_i h
      have hj := (Classical.choose h).isLt
      constructor <;> intro he <;> omega
    · constructor <;> intro he <;> omega
  · rename_i hi
    split <;> rename_i hg <;> constructor <;> intro he <;> omega

lemma rename_input {n n' : ℕ} (e : Fin n' → Fin n) (hinj : Function.Injective e)
    (G : ℕ) (j : Fin n') : rename e G (e j).val = j.val := by
  classical
  have hj : ∃ z, e z = ⟨(e j).val,(e j).isLt⟩ := ⟨j,rfl⟩
  simp only [rename,dite_eq_left (e j).isLt,dite_eq_left hj]
  have he : Classical.choose hj = j := hinj (Classical.choose_spec hj)
  exact congrArg Fin.val he

lemma append_get (w : List Bool) (b : Bool) (i : ℕ) :
    (w++[b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · rw [List.getD_append _ _ _ _ h,ite_eq_right (by omega)]
  · subst i; simp
  · rw [List.getD_eq_default _ _ (by simp;omega),ite_eq_right (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma rename_initial {n n' : ℕ} (Z : Finset (Fin n)) (e : Fin n' → Fin n)
    (hrange : ∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k)
    (G : ℕ) (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n')
    (hz : ∀ k ∈ Z, x.getD (k : ℕ) false = true)
    (he : ∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) :
    ∀ i, (x'++[true]).getD (rename e G i) false = x.getD i false := by
  classical
  intro i
  unfold rename
  split
  · rename_i hi
    split
    · rename_i h
      rw [List.getD_append _ _ _ _ (by rw [hx'];exact (Classical.choose h).isLt)]
      have hj := he (Classical.choose h)
      have hval := congrArg Fin.val (Classical.choose_spec h)
      simpa only [hval] using hj.symm
    · rename_i h
      have hk : (⟨i,hi⟩ : Fin n) ∈ Z := by
        by_contra hh
        exact h ((hrange ⟨i,hi⟩).1 hh)
      rw [hz ⟨i,hi⟩ hk,append_get]
      simp [hx']
  · rename_i hi
    rw [List.getD_eq_default x _ (by omega)]
    apply List.getD_eq_default
    simp only [List.length_append,List.length_singleton,hx']
    split <;> omega

def run (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w

def mapGate (phi : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map phi⟩

lemma fold_rename {n n' G : ℕ} (e : Fin n' → Fin n) (gs : List Gate) :
    ∀ t old new, t + gs.length ≤ G → old.length = n+t → new.length = n'+1+t →
    (∀ i, new.getD (rename e G i) false = old.getD i false) →
    ∀ i, (run (gs.map (mapGate (rename e G))) new).getD (rename e G i) false =
      (run gs old).getD i false := by
  induction gs with
  | nil => intro t old new ht ho hn hr; exact hr
  | cons g gs ih =>
    intro t old new ht ho hn hr
    let b := g.op.eval (g.inputs.map fun i => old.getD i false)
    have hb : (mapGate (rename e G) g).op.eval
        ((mapGate (rename e G) g).inputs.map fun i => new.getD i false) = b := by
      simp only [mapGate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hr i
    have step : ∀ i, (new++[b]).getD (rename e G i) false = (old++[b]).getD i false := by
      intro i
      rw [append_get,append_get,ho,hn]
      simp only [rename_gate e G t i (by simp at ht;omega),hr i]
    have hh := ih (t+1) (old++[b]) (new++[b]) (by simp at ht;omega)
      (by simp [ho];omega) (by simp [hn];omega) step
    simpa only [run,List.map_cons,List.foldl_cons,hb] using hh

end PEqualNP.Outside.L_meta_736_aux

open PEqualNP.Outside.L_meta_736_aux


theorem PEqualNP.Outside.L_meta_736 :
∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  intro n n' Z e he hrange hcard gates
  refine ⟨rename e gates.length,?_⟩
  intro x x' hx hx' hz hmatch
  have hr := rename_initial Z e hrange gates.length x x' hx hx' hz hmatch
  have hf := fold_rename e gates 0 x (x'++[true]) (by omega)
    (by simpa using hx) (by simp [hx']) hr
  exact ⟨hf,hf⟩
