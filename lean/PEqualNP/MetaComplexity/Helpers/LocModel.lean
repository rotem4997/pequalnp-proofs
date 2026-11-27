import PEqualNP.MetaComplexity.Helpers.Readers

/-!
# Local class, model layer: circuits without NOT gates, least circuits, readers, removal

Shared definitions of the last-gate line on graphs with long threads (`L-meta-115` and the
full-basis bound on the same graphs). Proofs only use them; no statement of a row does. Each
notion is basis-neutral where it can be: the condition "no NOT gate" is the separate predicate
`NotFree`, and `LeastIn Q` is a least clean gate list inside any class `Q` of gate lists
(`Q = NotFree` for monotone circuits, `Q = fun _ => True` for the full basis).

Wires, values and clean lists are those of `Parity3.lean` and `Parity4.lean` (`CleanL`, `vl`);
`Reads` is that of `Readers.lean`. Gate number `p` of a list on `m` inputs is wire `m + p`.
-/

namespace PEqualNP.MetaComplexity.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- No gate of the list is a NOT gate. -/
def NotFree (gs : List Gate) : Prop := ∀ g ∈ gs, g.op ≠ GateOp.not

/-- `f` on `n` inputs has a circuit of AND and OR gates of fan-in at most two, with no NOT
gate and at most `s` gates. -/
def HasMonoSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ NotFree C.gates ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

theorem HasMonoSize.has {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ} (h : HasMonoSize n f s) :
    HasCircuitSize n f s := by
  obtain ⟨C, h1, _, h3, h4⟩ := h
  exact ⟨C, h1, h3, h4⟩

theorem HasMonoSize.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ} (h : HasMonoSize n f s)
    (hs : s ≤ s') : HasMonoSize n f s' := by
  obtain ⟨C, h1, h2, h3, h4⟩ := h
  exact ⟨C, h1, h2, le_trans h3 hs, h4⟩

/-- A clean gate list with no NOT gate: every gate is an AND or an OR of two earlier wires. -/
def MClean (m : ℕ) (gs : List Gate) : Prop := CleanL m gs ∧ NotFree gs

/-- Wire `o` of the gate list computes `f`. -/
def Computes (m : ℕ) (gs : List Gate) (o : ℕ) (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ x : Fin m → Bool, vl gs x o = f x

/-- A clean gate list in the class `Q` computing `f` at wire `o`, of least length among the
clean lists of `Q` computing `f`. -/
def LeastIn (Q : List Gate → Prop) (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate)
    (o : ℕ) : Prop :=
  CleanL m gs ∧ Q gs ∧ Computes m gs o f ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → Q gs' → Computes m gs' o' f →
      gs.length ≤ gs'.length

/-- A least clean circuit with no NOT gate for `f`. -/
def MLeast (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  LeastIn NotFree m f gs o

theorem MLeast.clean {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (h : MLeast m f gs o) : MClean m gs := ⟨h.1, h.2.1⟩

/-- The set of gates of `gs` that read wire `w`. -/
noncomputable def RdSet (gs : List Gate) (w : ℕ) : Finset ℕ := by
  classical exact (Finset.range gs.length).filter (fun q => Reads gs q w)

theorem mem_rdSet {gs : List Gate} {w q : ℕ} : q ∈ RdSet gs w ↔ Reads gs q w := by
  classical
  unfold RdSet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨reads_len h, h⟩⟩

/-- The input point that is true exactly on `S`. -/
def pt {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool := fun i => decide (i ∈ S)

/-- Gate `q` is an OR gate reading the wires `v` and `w`. -/
def OrRd (gs : List Gate) (q v w : ℕ) : Prop :=
  ∃ g, gs[q]? = some g ∧ g.op = GateOp.or ∧ (g.inputs = [v, w] ∨ g.inputs = [w, v])

/-- Gate `q` is an AND gate reading the wires `v` and `w`. -/
def AndRd (gs : List Gate) (q v w : ℕ) : Prop :=
  ∃ g, gs[q]? = some g ∧ g.op = GateOp.and ∧ (g.inputs = [v, w] ∨ g.inputs = [w, v])

/-- The set `S` of gates can be removed on the set `P` of input points, with targets `tgt`.
Each gate `p` of `S` is an alias: `tgt p = some j` for an earlier wire `j` with the same value
as gate `p` at every point of `P`; or an orphan: `tgt p = none`, it is not the output, every
gate that reads it is in `S`, and it is the target of no gate of `S`. -/
def Removable (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ) : Prop :=
  ∀ p ∈ S, p < gs.length ∧
    ((∃ j, tgt p = some j ∧ j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j) ∨
      (tgt p = none ∧ o ≠ m + p ∧ (∀ q, Reads gs q (m + p) → q ∈ S) ∧
        ∀ q ∈ S, tgt q ≠ some (m + p)))

end PEqualNP.MetaComplexity.Loc
