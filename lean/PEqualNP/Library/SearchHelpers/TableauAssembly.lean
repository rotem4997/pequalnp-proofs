import PEqualNP.Library.SearchHelpers.TableauDefs
import PEqualNP.Library.SearchHelpers.Encoding
import PEqualNP.Library.Universal.Compile
import PEqualNP.Library.Machines.Run
import PEqualNP.Library.L029
import PEqualNP.Library.L045

/-!
# Helpers: SAT is NP-complete, from the three properties of the tableau formula

Helper module (proofs only, no statement may use it). Given soundness and completeness of the
tableau formula of a micro-instruction code and the polynomial-time computability of its
encoding, every language in NP reduces to SAT by `x ↦ encodeCNF (tableau c x' m T)` where `c`
is the compiled verifier, `m` the witness bound and `T` a polynomial time bound.
-/

namespace PEqualNP.Library.SearchHelpers.Tab

namespace Edge

open PEqualNP.Library PEqualNP.Library.Universal

/-- The symbol codes of an encoded pair: the input as `0`/`1`, the witness as `2`/`3`. -/
theorem map_symIn_encodePair (x w : List Bool) :
    (encodePair (x, w)).map symIn =
      x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2) := by
  simp only [encodePair, List.map_append, List.map_map]
  congr 1 <;> (apply List.map_congr_left; intro b _; cases b <;> rfl)

end Edge

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Search in
theorem npComplete_SAT_of
    (hsound : ∀ (c : PEqualNP.Library.Universal.Code) (zs : List ℕ) (m T : ℕ), (∀ z ∈ zs, z < 4) →
      PEqualNP.Search.Satisfiable (tableau c zs m T) →
      ∃ w : List Bool, w.length ≤ m ∧ c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1])
    (hcomplete : ∀ (c : PEqualNP.Library.Universal.Code) (zs : List ℕ) (m T : ℕ), (∀ z ∈ zs, z < 4) →
      ∀ w : List Bool, w.length ≤ m →
      c.outputsWithin (zs ++ w.map (fun b => cond b 3 2)) T [1] →
      PEqualNP.Search.Satisfiable (tableau c zs m T))
    (hcpt : ∀ (c : PEqualNP.Library.Universal.Code) (p q : Polynomial ℕ),
      PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => PEqualNP.Search.encodeCNF
          (tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length)))) :
    PEqualNP.Library.NPComplete PEqualNP.Search.SAT := by
  refine ⟨PEqualNP.Library.L029, ?_⟩
  intro L' hL'
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
    rw [Edge.map_symIn_encodePair] at h
    refine ⟨n, ?_, h⟩
    simpa [encodePair] using hn
  let q : Polynomial ℕ :=
    p + Polynomial.C d * cR.time.comp (Polynomial.X + p) + Polynomial.C d
  have hq : ∀ n : ℕ, q.eval n = p.eval n + d * cR.time.eval (n + p.eval n) + d := by
    intro n
    simp [q, Polynomial.eval_comp]
  have hzs : ∀ x : List Bool, ∀ z ∈ x.map (fun b => cond b 1 0), z < 4 := by
    intro x z hz
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hz
    cases b <;> simp
  refine ⟨fun x => encodeCNF
    (tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length)),
    hcpt c p q, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := (hL x).1 hx
    have hwl : w.length ≤ p.eval x.length := hbound x w hw
    refine ⟨_, rfl, hcomplete c _ _ _ (hzs x) w hwl ?_⟩
    obtain ⟨n, hn, ho⟩ := hrun x w
    have hfw : fR (x, w) = true := (hfR (x, w)).1 hw
    rw [hfw] at ho
    have hle : d * n + d ≤ q.eval x.length := by
      rw [hq]
      have h1 : n ≤ cR.time.eval (x.length + p.eval x.length) :=
        hn.trans (PEqualNP.Library.Machines.eval_mono _ (by omega))
      have h2 : d * n ≤ d * cR.time.eval (x.length + p.eval x.length) :=
        Nat.mul_le_mul_left d h1
      omega
    exact Code.outputsWithin_mono c _ hle _ ho
  · rintro ⟨φ, hφ, hsat⟩
    have hφ' : φ = tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length) :=
      PEqualNP.Library.SearchHelpers.encodeCNF_injective hφ
    rw [hφ'] at hsat
    obtain ⟨w, -, ho⟩ := hsound c _ _ _ (hzs x) hsat
    obtain ⟨n, -, ho'⟩ := hrun x w
    have h1 := Code.outputsWithin_mono c _ (le_max_left (q.eval x.length) (d * n + d)) _ ho
    have h2 := Code.outputsWithin_mono c _ (le_max_right (q.eval x.length) (d * n + d)) _ ho'
    have heq : [1] = [bitCode (fR (x, w))] := h1.2.symm.trans h2.2
    have hfw : fR (x, w) = true := by
      cases hb : fR (x, w) with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    exact (hL x).2 ⟨w, (hfR (x, w)).2 hfw⟩

end PEqualNP.Library.SearchHelpers.Tab
