import PEqualNP.Defs
import PEqualNP.Library.Universal.CompileBool

/-!
# A length-defined language that no machine decides

Helper module (proofs only, no statement may use it).

* `lenLang A`: the binary strings whose length lies in the set `A` of natural numbers.
* `lenLang_mem_PPoly`: every such language is in P/poly. At each length the slice is constant:
  one AND gate with no inputs gives `true`, and a missing output wire gives `false`.
* `codeLang c`: the language accepted by a micro-instruction code `c`.
* `exists_code_of_mem_DTIME`: every language in some `DTIME t` is `codeLang c` for a code `c`
  (through `compileBool`).
* `code_countable`: codes form a countable type.
* `exists_lenLang_not_decided`: some `lenLang A` is outside every `DTIME t`, since `A ↦ lenLang A`
  is injective on the uncountably many sets `A` (Cantor).
-/

namespace PEqualNP.MetaComplexity.Helpers.UndecUnary

open PEqualNP.CircuitLowerBounds PEqualNP.Library PEqualNP.Library.Universal

/-- The binary strings whose length lies in `A`. -/
def lenLang (A : Set ℕ) : Language Bool := {x : List Bool | x.length ∈ A}

theorem mem_lenLang (A : Set ℕ) (x : List Bool) : x ∈ lenLang A ↔ x.length ∈ A := Iff.rfl

theorem lenLang_injective : Function.Injective lenLang := by
  intro A B h
  ext n
  have := congrArg (fun L : Language Bool => List.replicate n false ∈ L) h
  simpa [mem_lenLang] using this

theorem lenLang_mem_PPoly (A : Set ℕ) : lenLang A ∈ PPoly := by
  refine ⟨Polynomial.C 1, fun n => ?_⟩
  by_cases hn : n ∈ A
  · refine ⟨⟨[⟨GateOp.and, []⟩], n⟩, ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      exact ⟨Or.inl rfl, by simp⟩
    · simp [Circuit.size]
    · intro x hx
      subst hx
      simp [Circuit.eval, Circuit.wires, GateOp.eval, mem_lenLang, hn]
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_⟩
    · intro g hg
      cases hg
    · simp [Circuit.size]
    · intro x hx
      subst hx
      simp [Circuit.eval, Circuit.wires, mem_lenLang, hn]

/-- The language accepted by a code: at some time it has halted with output `[1]`. -/
def codeLang (c : Code) : Language Bool :=
  {x : List Bool | ∃ t, c.outputsWithin (x.map (fun b => cond b 1 0)) t [1]}

theorem exists_code_of_mem_DTIME {t : ℕ → ℕ} {L : Language Bool} (h : L ∈ DTIME t) :
    ∃ c : Code, codeLang c = L := by
  obtain ⟨f, hf, ⟨comp, -⟩⟩ := h
  obtain ⟨c, d, hc⟩ := compileBool comp.tm comp.inputAlphabet comp.outputAlphabet
  refine ⟨c, ?_⟩
  ext x
  obtain ⟨⟨n, hn⟩, -⟩ := comp.outputsFun x
  have key := hc x (f x) n hn
  show (∃ t, c.outputsWithin (x.map (fun b => cond b 1 0)) t [1]) ↔ x ∈ L
  refine Iff.trans ?_ (hf x).symm
  constructor
  · rintro ⟨s, hs⟩
    by_contra hfx
    rw [Bool.not_eq_true] at hfx
    rw [hfx] at key
    have h1 := Code.outputsWithin_mono c _ (le_max_left s (d * n + d)) _ hs
    have h2 := Code.outputsWithin_mono c _ (le_max_right s (d * n + d)) _ key
    have := h1.2.symm.trans h2.2
    simp [bitCode] at this
  · intro hfx
    rw [hfx] at key
    exact ⟨_, key⟩

theorem instr_countable : Countable Instr := by
  let f : Instr → ℕ × List ℕ × ℕ × ℕ × ℕ := fun i =>
    match i with
    | Instr.push k tbl next => (0, tbl, k, next, 0)
    | Instr.pop k tbl w next => (1, tbl, k, w, next)
    | Instr.peek k tbl w next => (2, tbl, k, w, next)
    | Instr.load tbl next => (3, tbl, next, 0, 0)
    | Instr.branch tbl n₁ n₂ => (4, tbl, n₁, n₂, 0)
    | Instr.goto tbl => (5, tbl, 0, 0, 0)
    | Instr.halt => (6, [], 0, 0, 0)
  refine Function.Injective.countable (f := f) ?_
  intro a b h
  cases a <;> cases b <;> simp_all [f]

theorem code_countable : Countable Code := by
  have := instr_countable
  let f : Code → List Instr × ℕ × ℕ × ℕ × ℕ × ℕ := fun c =>
    (c.prog, c.nstk, c.pc₀, c.state₀, c.kin, c.kout)
  refine Function.Injective.countable (f := f) ?_
  intro a b h
  cases a; cases b
  simp_all [f]

theorem exists_lenLang_not_decided : ∃ A : Set ℕ, ∀ t : ℕ → ℕ, lenLang A ∉ DTIME t := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not] at hcon
  have hex : ∀ A : Set ℕ, ∃ c : Code, codeLang c = lenLang A := fun A => by
    obtain ⟨t, ht⟩ := hcon A
    exact exists_code_of_mem_DTIME ht
  choose g hg using hex
  have hginj : Function.Injective g := fun A B hAB =>
    lenLang_injective (by rw [← hg A, ← hg B, hAB])
  have := code_countable
  obtain ⟨e, he⟩ := exists_injective_nat Code
  exact Function.cantor_injective (fun A => e (g A)) (he.comp hginj)

end PEqualNP.MetaComplexity.Helpers.UndecUnary
