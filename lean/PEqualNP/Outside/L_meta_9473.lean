import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9473_aux

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type} [DecidableEq V]

def replay (db : List (List (Literal V))) (fs : List (Literal V)) : List Nat → Bool
  | [] => false
  | i :: trail =>
    match db[i]? with
    | none => false
    | some d =>
      match d.filter (fun l => !fs.contains l) with
      | [] => true
      | [l] => replay db (negLit l :: fs) trail
      | _ => false

theorem replay_sound (db : List (List (Literal V))) (Γ : Set (Clause V))
    (A : Set (Literal V)) (hd : ∀ d ∈ db, d.toFinset ∈ Γ)
    (trail : List Nat) (fs : List (Literal V))
    (hf : ∀ l ∈ fs, UPForces Γ A (negLit l)) (h : replay db fs trail = true) :
    ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  induction trail generalizing fs with
  | nil => simp [replay] at h
  | cons i trail ih =>
    simp only [replay] at h
    split at h
    · contradiction
    next d he =>
      have hm := hd d (List.mem_of_getElem? he)
      split at h
      next hnil =>
        refine ⟨d.toFinset, hm, ?_⟩
        intro l hl
        have hld : l ∈ d := List.mem_toFinset.mp hl
        apply hf
        by_contra hn
        have : l ∈ d.filter (fun l => !fs.contains l) := by simp [hld, hn]
        rw [hnil] at this
        exact List.not_mem_nil this
      next l hsingle =>
        have hld : l ∈ d.filter (fun v => !fs.contains v) := by
          rw [hsingle]
          exact List.mem_cons_self
        have hu : UPForces Γ A l := by
          apply UPForces.unit hm (List.mem_toFinset.mpr (List.mem_filter.mp hld).1)
          intro v hv hne
          apply hf
          by_contra hn
          have hvd : v ∈ d := List.mem_toFinset.mp hv
          have : v ∈ d.filter (fun x => !fs.contains x) := by simp [hvd, hn]
          rw [hsingle] at this
          exact hne (List.mem_singleton.mp this)
        apply ih (negLit l :: fs) _ h
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simpa [negLit] using hu
        · exact hf v hv
      next => contradiction

def verify (db : List (List (Literal V))) :
    List (List (Literal V) × List Nat) → Bool
  | [] => true
  | (c, trail) :: steps => replay db c trail && verify (db ++ [c]) steps

def learned (s : List (List (Literal V) × List Nat)) (ρ : List (Clause V)) :=
  s.foldl (fun acc p => p.1.toFinset :: acc) ρ

theorem verify_sound (F : Set (Clause V)) (steps : List (List (Literal V) × List Nat))
    (db : List (List (Literal V))) (ρ : List (Clause V)) (hr : IsRUPRun F ρ)
    (hd : ∀ d ∈ db, d.toFinset ∈ F ∪ {D | D ∈ ρ}) (h : verify db steps = true) :
    IsRUPRun F (learned steps ρ) := by
  induction steps generalizing db ρ with
  | nil => exact hr
  | cons head steps ih =>
    obtain ⟨c, trail⟩ := head
    have ⟨ht, hs⟩ := Bool.and_eq_true_iff.mp h
    have hc : IsRUP (F ∪ {D | D ∈ ρ}) c.toFinset := by
      apply replay_sound db _ _ hd trail c _ ht
      intro l hl
      exact UPForces.hyp ⟨l, List.mem_toFinset.mpr hl, rfl⟩
    apply ih (db ++ [c]) (c.toFinset :: ρ) (IsRUPRun.learn hr hc) _ hs
    intro d hmem
    rcases List.mem_append.mp hmem with hm | hm
    · rcases hd d hm with hF | hρ
      · exact Or.inl hF
      · exact Or.inr (List.mem_cons_of_mem _ hρ)
    · have he : d = c := by simpa using hm
      exact Or.inr (he ▸ List.mem_cons_self)

abbrev Board := Fin 6 × Fin 5

def row (p : Fin 6) : List (Literal Board) :=
  (List.finRange 5).map (fun h => ((p, h), true))

def block (p q : Fin 6) (h : Fin 5) : List (Literal Board) :=
  [((p, h), false), ((q, h), false)]

def input : List (List (Literal Board)) :=
  (List.finRange 6).map row ++ (List.finRange 5).flatMap (fun h =>
    (List.finRange 6).flatMap (fun p =>
      ((List.finRange 6).filter (fun q => p < q)).map (fun q => block p q h)))

theorem input_sound (d : List (Literal Board)) (hd : d ∈ input) :
    d.toFinset ∈ PHP 6 5 := by
  rcases List.mem_append.mp hd with hr | hb
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    left
    refine ⟨p, ?_⟩
    ext l
    simp [row]
  · obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp hb
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    right
    exact ⟨p, q, h, ne_of_lt (of_decide_eq_true (List.mem_filter.mp hq).2), by simp [block]⟩

def readLiteral (k : Nat) : Literal Board :=
  ((Fin.ofNat 6 (k / 2 / 5), Fin.ofNat 5 (k / 2)), decide (k % 2 = 0))

def steps : List (List (Literal Board) × List Nat) :=
  ([
    ([30, 34, 38, 40, 44, 48, 53], [34, 35, 3, 4, 63]),
    ([15, 20, 22, 26, 30, 40, 50], [41, 42, 43, 44, 2, 75, 76, 77, 81, 5, 64, 65, 3, 4, 33]),
    ([5, 12, 16, 20, 22, 26], [36, 37, 38, 39, 40, 2, 71, 75, 76, 77, 1, 12, 13, 14, 81, 5, 64, 65, 3, 4, 33]),
    ([2, 6, 11, 12, 16, 22, 26], [6, 11, 12, 13, 14, 83, 0, 67, 68, 69, 70, 2, 45, 46, 47, 81, 5, 64, 65, 3, 4, 33]),
    ([5, 12, 16, 22, 26], [36, 38, 39, 40, 83, 11, 15, 16, 17, 1, 72, 73, 74, 81, 5, 64, 65, 3, 4, 33]),
    ([1, 12, 16, 22, 26], [6, 7, 8, 9, 10, 82, 1, 71, 72, 73, 74, 2, 45, 46, 47, 81, 5, 64, 65, 3, 4, 33]),
    ([33, 50, 54, 58], [23, 27, 30, 33, 34, 5, 55, 59, 62, 65, 84, 85, 86, 0, 66, 67, 69, 1, 41, 43, 2, 4, 16]),
    ([30, 38, 45, 50, 58], [39, 43, 48, 50, 87, 3, 53, 57, 60, 64, 5, 25, 29, 32, 84, 86, 0, 1, 66]),
    ([30, 34, 49, 50, 54], [69, 78, 80, 87, 3, 53, 57, 60, 64, 5, 25, 29, 32, 85, 86, 0]),
    ([7, 10, 14, 18, 20, 24, 28], [51, 52, 1, 2, 26]),
    ([32, 36, 42, 46, 48, 51], [10, 14, 17, 19, 20, 4, 39, 43, 46, 48, 3, 68, 72, 75, 90, 0, 21, 22, 1, 2, 56]),
    ([33, 40, 44, 48], [23, 27, 30, 33, 4, 54, 58, 61, 84, 85, 86, 0, 66, 67, 70, 1, 41, 44, 87, 2, 17]),
    ([40, 42, 44, 48, 50, 54, 58], [4, 54, 58, 61, 65, 5, 25, 29, 32, 84, 85, 86, 0, 66, 67, 68, 1, 41, 42, 81, 2, 15]),
    ([30, 34, 38, 40, 44, 48], [81, 92, 3, 53, 57, 60, 63, 64, 4, 24, 28, 31, 84, 85, 86, 0, 66, 67, 70, 1, 41, 44, 2, 5, 17]),
    ([21, 38, 48, 58], [7, 11, 15, 16, 17, 88, 94, 38, 42, 49, 93, 24, 28, 35, 5, 55, 59, 0, 1, 66]),
    ([4, 14, 24, 41, 52, 54, 56], [9, 13, 16, 20, 5, 70, 74, 77, 90, 0, 21, 22, 1, 2, 56]),
    ([35, 42, 46, 52, 56], [38, 42, 45, 48, 49, 96, 4, 69, 73, 76, 80, 5, 10, 14, 17, 90, 0, 21, 22, 1, 2, 56]),
    ([0, 10, 20, 45, 50, 52, 56], [39, 43, 46, 50, 5, 70, 74, 77, 90, 0, 21, 22, 1, 2, 56]),
    ([31, 42, 46, 52, 56], [8, 12, 15, 18, 19, 98, 4, 69, 73, 76, 80, 5, 40, 44, 47, 90, 0, 21, 22, 1, 2, 56]),
    ([31, 44, 48, 54, 58], [8, 12, 15, 18, 19, 93, 24, 28, 31, 35, 5, 55, 59, 62, 83, 0, 66, 67, 1, 2, 41]),
    ([29, 34, 44, 54], [67, 75, 76, 77, 95, 100, 94, 9, 20, 87, 3, 53, 57, 60, 64, 5, 25, 29, 32, 83, 0]),
    ([5, 22, 26], [37, 38, 39, 40, 101, 2, 15, 16, 17, 89, 94, 79, 93, 28, 35, 85, 5, 59]),
    ([25, 30, 40, 50], [37, 45, 46, 47, 89, 94, 68, 79, 93, 24, 28, 31, 35, 5, 55, 59, 62, 86, 0]),
    ([1, 22, 26], [7, 8, 9, 10, 103, 2, 75, 76, 77, 88, 94, 49, 93, 28, 35, 86, 5, 59]),
    ([2, 6, 22, 26], [102, 104, 0, 66, 67, 68, 69, 70, 95, 2, 41, 45, 46, 47, 100, 94, 13, 20, 87, 3, 57, 64, 1, 5, 29]),
    ([7, 32, 42, 52], [53, 54, 55, 97, 99, 3, 72, 75, 78, 79, 91, 5, 44, 47, 50, 4, 13, 16, 90]),
    ([3, 36, 46, 56], [21, 22, 23, 24, 25, 97, 99, 3, 72, 75, 78, 79, 91, 5, 44, 47, 50, 4, 13, 16, 1, 2, 56]),
    ([17], [51, 56, 57, 58, 59, 107, 105, 30, 31, 32, 97, 99, 3, 68, 78, 79, 91, 5, 40, 50, 0, 4, 9]),
    ([19, 34, 44, 54], [72, 73, 74, 100, 94, 20, 87, 3, 53, 60, 64, 5, 25, 32, 105]),
    ([13], [21, 26, 27, 28, 29, 106, 105, 60, 61, 62, 97, 99, 3, 68, 78, 79, 91, 5, 40, 50, 0, 4, 9]),
    ([15, 30, 40, 50], [42, 43, 44, 89, 94, 79, 93, 24, 31, 35, 5, 55, 62, 105]),
    ([1], [6, 8, 9, 10, 108, 110, 111, 1, 72, 73, 74, 88, 94, 49, 93, 31, 35, 86, 5, 62]),
    ([9, 10], [66, 67, 68, 69, 70, 95, 108, 110, 1, 41, 42, 43, 44, 100, 94, 20, 87, 3, 60, 64, 2, 5, 32]),
    ([9], [67, 68, 69, 70, 95, 113, 12, 13, 14, 88, 94, 103, 49, 93, 31, 35, 2, 5, 62]),
    ([27], [52, 56, 60, 61, 62, 107, 110, 112, 114, 0, 36, 38, 39, 40, 109, 1, 12, 13, 14, 89, 94, 4, 35, 79, 5]),
    ([19, 22], [71, 72, 73, 74, 95, 115, 2, 45, 46, 47, 109]),
    ([15, 22], [41, 42, 43, 44, 101, 115, 2, 15, 16, 17, 111]),
    ([23], [22, 26, 30, 31, 32, 106, 108, 112, 114, 0, 36, 38, 39, 40, 109, 1, 12, 13, 14, 89, 93, 94, 79]),
    ([], [108, 110, 115, 118, 116, 117, 1, 11, 12, 13, 14, 103, 2, 75, 76, 77, 88, 94, 49, 93, 24, 35, 84, 5, 55])] : List (List Nat × List Nat)).map (fun p =>
      (p.1.map readLiteral, p.2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checked : verify input steps = true := by decide +kernel

theorem run : IsRUPRun (PHP 6 5) (learned steps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked

theorem containsEmpty : (∅ : Clause Board) ∈ learned steps [] := by decide +kernel

theorem count : (learned steps []).length = 39 := by decide +kernel

end PEqualNP.Outside.L_meta_9473_aux

theorem PEqualNP.Outside.L_meta_9473 : (∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (5 + 1) 5) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)) ∈ ρ ∧ ρ.length ≤ 40) := by
  exact ⟨_, L_meta_9473_aux.run, L_meta_9473_aux.containsEmpty, L_meta_9473_aux.count.le.trans (by decide)⟩
