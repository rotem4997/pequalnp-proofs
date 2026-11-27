import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class: cleaning tools that keep NOT-freeness

Builder file of `L-meta-115` for the pieces `ToolOfClean`, `ToolLeast`, `ToolRestrict` and
`ToolSnoc` of `LocPlan.lean`. The simplifier `elim` of `Elim.lean` emits an AND gate only from an
AND gate and an OR gate only from an OR gate (`simplify_op`), so the pass of a list with no NOT
gate has no NOT gate (`elim_mono`). The checked lemmas `Parity3.clean_of`, `Readers.save` and
`PermInputs.relabel_size` hide the circuit behind an existential, so their proofs are restated
here with NOT-freeness carried along.
-/

namespace PEqualNP.MetaComplexity.Loc.Clean

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Loc

/-! ## The simplifier keeps the operation -/

/-- Every gate the simplifier emits for an operation `op` has the operation `op`. -/
theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

/-- The pass of a list with no NOT gate emits no NOT gate. -/
theorem elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    NotFree gs → NotFree acc.2 → NotFree (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · rw [simplify_op _ _ _ g' (by simpa using h1)]
      exact hgs g List.mem_cons_self

/-! ## ToolOfClean -/

theorem ToolOfClean_proof : ToolOfClean := by
  intro m gs o h
  refine ⟨⟨gs, o⟩, ?_, h.2, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok m gs h.1 g hg).1

/-! ## ToolLeast -/

/-- A clean NOT-free list with at most `s` gates computes `f`. -/
def HasMClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ NotFree gs ∧ gs.length ≤ s ∧ Computes n gs o f

/-- A NOT-free circuit for a non-constant function can be cleaned without growing and without
creating a NOT gate. Copy of `Parity3.clean_of`. -/
theorem mclean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasMonoSize n f s) : HasMClean n f s := by
  obtain ⟨C, ok, hnf, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · exact elim_mono n C.gates _ hnf (by intro g hg; simp at hg)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem ToolLeast_proof : ToolLeast := by
  classical
  intro n f s hnc h
  have hc := mclean_of n f s hnc h
  have hex : ∃ t, HasMClean n f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hnf, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hnf, hev, ?_⟩, by omega⟩
  intro gs' o' hc' hn' he'
  have := Nat.find_min' hex ⟨gs', o', hc', hn', le_refl _, he'⟩
  omega

/-! ## ToolRestrict -/

/-- Renaming inputs keeps NOT-free circuit size. Copy of `PermInputs.relabel_size`. -/
theorem relabel_mono {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasMonoSize n h s) : HasMonoSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hnf, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact hnf g0 hg0
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

/-- Fixing input `i` of a clean NOT-free list on `n + 1` inputs. Copy of `Readers.save` at the
empty set of gates. -/
theorem restrict_succ (n : ℕ) (gs : List Gate) (o : ℕ) (i : Fin (n + 1)) (b : Bool)
    (h : MClean (n + 1) gs)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      vl gs (Function.update x i b) o ≠ vl gs (Function.update y i b) o) :
    HasMonoSize (n + 1) (fun x => vl gs (Function.update x i b) o) gs.length := by
  have hcl := h.1
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl (fun _ => rfl) i b c hst x).trans
      (restr_const hcl (fun _ => rfl) i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have hnf : NotFree (passG n gs i b) :=
      elim_mono n gs _ h.2 (by intro g hg; simp at hg)
    have hlen : (passG n gs i b).length ≤ gs.length := by
      have := elim_len n gs (statAt n i b, [])
      simp only [List.length_nil, zero_add] at this
      exact this
    have h2 := relabel_mono (Fin.succAbove i) _ _
      ((ToolOfClean_proof n (passG n gs i b) j ⟨hc, hnf⟩).mono hlen)
    have e : (fun x : Fin (n + 1) → Bool => vl gs (Function.update x i b) o)
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, st_val_wire n gs hcl i b o j hst]
      rfl
    rw [e]
    exact h2

theorem ToolRestrict_proof : ToolRestrict := by
  intro m gs o i b h hnc
  cases m with
  | zero => exact i.elim0
  | succ n => exact restrict_succ n gs o i b h hnc

/-! ## ToolSnoc -/

theorem ToolSnoc_proof : ToolSnoc := by
  intro m gs j k h hj hk
  set g : Gate := ⟨GateOp.or, [j, k]⟩ with hg
  have hcl : CleanL m (gs ++ [g]) := by
    intro p g' hp
    by_cases hlt : p < gs.length
    · rw [List.getElem?_append_left hlt] at hp
      exact h.1 p g' hp
    · rw [List.getElem?_append_right (by omega)] at hp
      have hp0 : p - gs.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hp
        cases hp
      rw [hp0] at hp
      simp at hp
      subst hp
      have hpl : p = gs.length := by omega
      subst hpl
      exact Or.inr ⟨Or.inr rfl, j, k, hj, hk, rfl⟩
  have hnf : NotFree (gs ++ [g]) := by
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h.2 g' h1
    · simp at h1; subst h1; simp [hg]
  have low : ∀ (x : Fin m → Bool) (i : ℕ), i < m + gs.length → vl (gs ++ [g]) x i = vl gs x i := by
    intro x i hi
    unfold vl
    rw [wiresFrom_append, getD_wiresFrom _ _ i (by rw [length_wiresFrom]; simpa using hi)]
  refine ⟨⟨hcl, hnf⟩, fun x => ⟨?_, low x⟩⟩
  rw [vl_gate (gs ++ [g]) hcl x gs.length g (by simp), hg]
  simp only [GateOp.eval, List.map_cons, List.map_nil]
  rw [low x j hj, low x k hk]
  simp

end PEqualNP.MetaComplexity.Loc.Clean
