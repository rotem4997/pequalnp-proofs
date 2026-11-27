import PEqualNP.Library.Universal.Compile
import PEqualNP.Library.Universal.Pair
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.L045
import PEqualNP.Library.L055

/-!
# From a polynomial-time interpreter to an NP-complete language

Helper module (proofs only, no statement may use it). Given an encoding of micro-instruction
codes as bit strings and a polynomial-time verifier `V` that, on a code, an input, a unary
clock and a witness, answers whether the code accepts the input with the witness within the
clock, the language of all strings that have an accepted witness no longer than themselves is
NP-complete.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

private abbrev sid : List Bool → List Bool := fun x => x

/-- Appending two polynomial-time computable strings. -/
private theorem cpt_app {f g : List Bool → List Bool}
    (hf : ComputableInPolyTime sid sid f) (hg : ComputableInPolyTime sid sid g) :
    ComputableInPolyTime sid sid (fun x => f x ++ g x) :=
  cpt_comp (cpt_pair hf hg) cpt_append

/-- The length of the input in unary. -/
private theorem cpt_unLen : ComputableInPolyTime sid sid (fun x : List Bool => un x.length) := by
  refine filterMap_polyTime _ _ _ (fun _ : Bool => some true) ?_
  intro x
  induction x with
  | nil => rfl
  | cons a l ih =>
    simp only [un, List.length_cons, List.replicate_succ, List.filterMap_cons] at ih ⊢
    exact congrArg (List.cons true) ih

/-- The reduction map is polynomial-time computable. -/
private theorem cpt_reduction (a : List Bool) (q : Polynomial ℕ) :
    ComputableInPolyTime sid sid
      (fun x : List Bool => pairB a (pairB x (un (q.eval x.length)))) := by
  have hclock : ComputableInPolyTime sid sid (fun x : List Bool => un (q.eval x.length)) :=
    L055 q
  have hconst : ∀ l : List Bool, ComputableInPolyTime sid sid (fun _ : List Bool => l) :=
    fun l => constList_polyTime l
  have h := cpt_app (hconst (un a.length ++ false :: a))
    (cpt_app cpt_unLen (cpt_app (hconst [false]) (cpt_app cpt_id hclock)))
  have e : (fun x : List Bool => pairB a (pairB x (un (q.eval x.length)))) =
      (fun x : List Bool => (un a.length ++ false :: a) ++
        (un x.length ++ ([false] ++ (x ++ un (q.eval x.length))))) := by
    funext x
    simp [pairB]
  rw [e]
  exact h

private theorem map_symIn_encodePair (x w : List Bool) :
    (encodePair (x, w)).map symIn =
      x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2) := by
  simp only [encodePair, List.map_append, List.map_map]
  congr 1 <;> (apply List.map_congr_left; intro b _; cases b <;> rfl)

private theorem length_reduction (a x : List Bool) (t : ℕ) :
    t ≤ (pairB a (pairB x (un t))).length := by
  simp [pairB, un]
  omega

theorem npComplete_of_interp (encCode : Code → List Bool) (V : List Bool × List Bool → Bool)
    (hV : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool V)
    (hspec : ∀ (c : Code) (x w : List Bool) (t : ℕ),
      V (pairB (encCode c) (pairB x (un t)), w) = true ↔
        (w.length ≤ t ∧ c.outputsWithin
          (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2)) t [1])) :
    ∃ L : Language Bool, PEqualNP.Library.NPComplete L := by
  let U : Language Bool := {z | ∃ w : List Bool, w.length ≤ z.length ∧ V (z, w) = true}
  have hU : ∀ z, z ∈ U ↔ ∃ w : List Bool, w.length ≤ z.length ∧ V (z, w) = true :=
    fun _ => Iff.rfl
  refine ⟨U, ?_, ?_⟩
  · refine ⟨{p | V p = true}, Polynomial.X, ⟨V, fun _ => Iff.rfl, hV⟩, fun x => ?_⟩
    rw [hU, Polynomial.eval_X]
    exact Iff.rfl
  · intro L' hL'
    obtain ⟨R, p, ⟨fR, hfR, ⟨cR⟩⟩, hbound, hL⟩ := L045 L' hL'
    obtain ⟨c, d, hc⟩ := compile cR.tm cR.inputAlphabet cR.outputAlphabet
    have hrun : ∀ x w : List Bool, ∃ n, n ≤ cR.time.eval (x.length + w.length) ∧
        c.outputsWithin (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2))
          (d * n + d) [bitCode (fR (x, w))] := by
      intro x w
      obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cR.time.eval (encodePair (x, w)).length ∧
          (flip bind (Turing.TM2.step cR.tm.m))^[n]
            (some (Turing.initList cR.tm ((encodePair (x, w)).map cR.inputAlphabet.invFun))) =
          some (Turing.haltList cR.tm [cR.outputAlphabet.invFun (fR (x, w))]) :=
        ⟨(cR.outputsFun (x, w)).steps, (cR.outputsFun (x, w)).steps_le_m,
          (cR.outputsFun (x, w)).evals_in_steps⟩
      have h := hc (encodePair (x, w)) (fR (x, w)) n hev
      rw [map_symIn_encodePair] at h
      refine ⟨n, ?_, h⟩
      simpa [encodePair] using hn
    let q : Polynomial ℕ :=
      p + Polynomial.C d * cR.time.comp (Polynomial.X + p) + Polynomial.C d
    have hq : ∀ n : ℕ, q.eval n = p.eval n + d * cR.time.eval (n + p.eval n) + d := by
      intro n
      simp [q, Polynomial.eval_comp]
    refine ⟨fun x => pairB (encCode c) (pairB x (un (q.eval x.length))),
      cpt_reduction (encCode c) q, fun x => ?_⟩
    rw [hU]
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := (hL x).1 hx
      have hwl : w.length ≤ p.eval x.length := hbound x w hw
      have hwt : w.length ≤ q.eval x.length := by rw [hq]; omega
      refine ⟨w, hwt.trans (length_reduction _ _ _), (hspec c x w _).2 ⟨hwt, ?_⟩⟩
      obtain ⟨n, hn, ho⟩ := hrun x w
      have hfw : fR (x, w) = true := (hfR (x, w)).1 hw
      rw [hfw] at ho
      have hle : d * n + d ≤ q.eval x.length := by
        rw [hq]
        have h1 : n ≤ cR.time.eval (x.length + p.eval x.length) :=
          hn.trans (eval_mono _ (by omega))
        have h2 : d * n ≤ d * cR.time.eval (x.length + p.eval x.length) :=
          Nat.mul_le_mul_left d h1
        omega
      exact Code.outputsWithin_mono c _ hle _ ho
    · rintro ⟨w, -, hVw⟩
      obtain ⟨-, ho⟩ := (hspec c x w _).1 hVw
      obtain ⟨n, -, ho'⟩ := hrun x w
      have h1 := Code.outputsWithin_mono c _ (le_max_left (q.eval x.length) (d * n + d)) _ ho
      have h2 := Code.outputsWithin_mono c _ (le_max_right (q.eval x.length) (d * n + d)) _ ho'
      have heq : [1] = [bitCode (fR (x, w))] := h1.2.symm.trans h2.2
      have hfw : fR (x, w) = true := by
        cases hb : fR (x, w) with
        | true => rfl
        | false => rw [hb] at heq; simp [bitCode] at heq
      exact (hL x).2 ⟨w, (hfR (x, w)).2 hfw⟩

end PEqualNP.Library.Universal
