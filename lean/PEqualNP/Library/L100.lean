import PEqualNP.Library.Helpers.PadMap

/-- Linear clock: a one-state transducer writes one `true` per input symbol. -/
theorem PEqualNP.Library.L100 : ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => List.replicate x.length true) (fun n : ℕ => c * n + c) := by
  refine ⟨3, ?_⟩
  obtain ⟨c, hc⟩ := PEqualNP.Library.Helpers.fst2_time (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => List.replicate x.length true)
    (fun (_ : Unit) (_ : Bool) => ((), some true, none)) (fun _ => none) ()
    (fun a => by
      induction a with
      | nil => rfl
      | cons b l ih =>
        simp only [List.length_cons, List.replicate_succ, PEqualNP.Library.Machines.fstRun2]
        simpa using ih)
  exact ⟨c, fun n => (hc n).trans (by show 2 * n + 3 ≤ 3 * n + 3; omega)⟩
