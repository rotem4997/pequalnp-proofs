import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9477_aux

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

-- With t holes available, designate pigeon 5 - t. For each available hole
-- except the last one, exclude that pigeon from the hole when all later
-- pigeons are confined to the available holes. Occupying the excluded hole
-- reduces their available set by one. At one hole, two forced pigeons collide.
def steps : List (List (Literal Board) × List Nat) :=
  ([
    ([31, 44, 46, 48, 54, 56, 58], [18, 19, 4, 5, 35]),
    ([31, 42, 46, 48, 52, 56, 58], [18, 19, 4, 5, 50]),
    ([31, 42, 44, 48, 52, 54, 58], [18, 19, 4, 5, 65]),
    ([31, 42, 44, 46, 52, 54, 56], [18, 19, 4, 5, 80]),
    ([33, 40, 46, 48, 50, 56, 58], [33, 34, 4, 5, 50]),
    ([33, 40, 44, 48, 50, 54, 58], [33, 34, 4, 5, 65]),
    ([33, 40, 44, 46, 50, 54, 56], [33, 34, 4, 5, 80]),
    ([35, 40, 42, 48, 50, 52, 58], [48, 49, 4, 5, 65]),
    ([35, 40, 42, 46, 50, 52, 56], [48, 49, 4, 5, 80]),
    ([37, 40, 42, 44, 50, 52, 54], [63, 64, 4, 5, 80]),
    ([21, 36, 38, 46, 48, 56, 58], [15, 16, 17, 85, 3, 48, 49, 4, 5, 35]),
    ([23, 36, 38, 46, 48, 56, 58], [30, 31, 32, 82, 3, 48, 49, 4, 5, 20]),
    ([21, 34, 38, 44, 48, 54, 58], [15, 16, 17, 86, 3, 63, 64, 4, 5, 35]),
    ([23, 34, 38, 44, 48, 54, 58], [30, 31, 32, 83, 3, 63, 64, 4, 5, 20]),
    ([21, 34, 36, 44, 46, 54, 56], [15, 16, 17, 87, 3, 78, 79, 4, 5, 35]),
    ([23, 34, 36, 44, 46, 54, 56], [30, 31, 32, 84, 3, 78, 79, 4, 5, 20]),
    ([21, 32, 38, 42, 48, 52, 58], [15, 16, 17, 88, 3, 63, 64, 4, 5, 50]),
    ([25, 32, 38, 42, 48, 52, 58], [45, 46, 47, 83, 3, 63, 64, 4, 5, 20]),
    ([21, 32, 36, 42, 46, 52, 56], [15, 16, 17, 89, 3, 78, 79, 4, 5, 50]),
    ([25, 32, 36, 42, 46, 52, 56], [45, 46, 47, 84, 3, 78, 79, 4, 5, 20]),
    ([21, 32, 34, 42, 44, 52, 54], [15, 16, 17, 90, 3, 78, 79, 4, 5, 65]),
    ([27, 32, 34, 42, 44, 52, 54], [60, 61, 62, 84, 3, 78, 79, 4, 5, 20]),
    ([23, 30, 38, 40, 48, 50, 58], [30, 31, 32, 88, 3, 63, 64, 4, 5, 50]),
    ([25, 30, 38, 40, 48, 50, 58], [45, 46, 47, 86, 3, 63, 64, 4, 5, 35]),
    ([23, 30, 36, 40, 46, 50, 56], [30, 31, 32, 89, 3, 78, 79, 4, 5, 50]),
    ([25, 30, 36, 40, 46, 50, 56], [45, 46, 47, 87, 3, 78, 79, 4, 5, 35]),
    ([23, 30, 34, 40, 44, 50, 54], [30, 31, 32, 90, 3, 78, 79, 4, 5, 65]),
    ([27, 30, 34, 40, 44, 50, 54], [60, 61, 62, 87, 3, 78, 79, 4, 5, 35]),
    ([25, 30, 32, 40, 42, 50, 52], [45, 46, 47, 90, 3, 78, 79, 4, 5, 65]),
    ([27, 30, 32, 40, 42, 50, 52], [60, 61, 62, 89, 3, 78, 79, 4, 5, 50]),
    ([11, 28, 38, 48, 58], [11, 12, 13, 14, 103, 104, 2, 60, 61, 62, 85, 3, 48, 49, 4, 5, 35]),
    ([13, 28, 38, 48, 58], [26, 27, 28, 29, 97, 98, 2, 60, 61, 62, 82, 3, 48, 49, 4, 5, 20]),
    ([15, 28, 38, 48, 58], [41, 42, 43, 44, 93, 94, 2, 60, 61, 62, 81, 3, 33, 34, 4, 5, 20]),
    ([11, 26, 36, 46, 56], [11, 12, 13, 14, 105, 106, 2, 75, 76, 77, 85, 3, 48, 49, 4, 5, 35]),
    ([13, 26, 36, 46, 56], [26, 27, 28, 29, 99, 100, 2, 75, 76, 77, 82, 3, 48, 49, 4, 5, 20]),
    ([15, 26, 36, 46, 56], [41, 42, 43, 44, 95, 96, 2, 75, 76, 77, 81, 3, 33, 34, 4, 5, 20]),
    ([11, 24, 34, 44, 54], [11, 12, 13, 14, 107, 108, 2, 75, 76, 77, 86, 3, 63, 64, 4, 5, 35]),
    ([13, 24, 34, 44, 54], [26, 27, 28, 29, 101, 102, 2, 75, 76, 77, 83, 3, 63, 64, 4, 5, 20]),
    ([17, 24, 34, 44, 54], [56, 57, 58, 59, 95, 96, 2, 75, 76, 77, 81, 3, 33, 34, 4, 5, 20]),
    ([11, 22, 32, 42, 52], [11, 12, 13, 14, 109, 110, 2, 75, 76, 77, 88, 3, 63, 64, 4, 5, 50]),
    ([15, 22, 32, 42, 52], [41, 42, 43, 44, 101, 102, 2, 75, 76, 77, 83, 3, 63, 64, 4, 5, 20]),
    ([17, 22, 32, 42, 52], [56, 57, 58, 59, 99, 100, 2, 75, 76, 77, 82, 3, 48, 49, 4, 5, 20]),
    ([13, 20, 30, 40, 50], [26, 27, 28, 29, 109, 110, 2, 75, 76, 77, 88, 3, 63, 64, 4, 5, 50]),
    ([15, 20, 30, 40, 50], [41, 42, 43, 44, 107, 108, 2, 75, 76, 77, 86, 3, 63, 64, 4, 5, 35]),
    ([17, 20, 30, 40, 50], [56, 57, 58, 59, 105, 106, 2, 75, 76, 77, 85, 3, 48, 49, 4, 5, 35]),
    ([1], [6, 7, 8, 9, 10, 123, 124, 125, 1, 71, 72, 73, 74, 103, 104, 2, 60, 61, 62, 85, 3, 48, 49, 4, 5, 35]),
    ([3], [21, 22, 23, 24, 25, 120, 121, 122, 1, 71, 72, 73, 74, 97, 98, 2, 60, 61, 62, 82, 3, 48, 49, 4, 5, 20]),
    ([5], [36, 37, 38, 39, 40, 117, 118, 119, 1, 71, 72, 73, 74, 93, 94, 2, 60, 61, 62, 81, 3, 33, 34, 4, 5, 20]),
    ([7], [51, 52, 53, 54, 55, 114, 115, 116, 1, 71, 72, 73, 74, 91, 92, 2, 45, 46, 47, 81, 3, 33, 34, 4, 5, 20]),
    ([], [126, 127, 128, 129, 0, 66, 67, 68, 69, 70, 111, 112, 113, 1, 56, 57, 58, 59, 91, 92, 2, 45, 46, 47, 81, 3, 33, 34, 4, 5, 20])] : List (List Nat × List Nat)).map (fun p =>
      (p.1.map readLiteral, p.2))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem checked : verify input steps = true := by decide +kernel

theorem run : IsRUPRun (PHP 6 5) (learned steps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked

theorem containsEmpty : (∅ : Clause Board) ∈ learned steps [] := by decide +kernel

theorem count : (learned steps []).length = 50 := by decide +kernel

end PEqualNP.Outside.L_meta_9477_aux

theorem PEqualNP.Outside.L_meta_9477 : ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (5 + 1) 5) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)) ∈ ρ ∧ ρ.length ≤ 64 := by
  exact ⟨_, L_meta_9477_aux.run, L_meta_9477_aux.containsEmpty, L_meta_9477_aux.count.le.trans (by decide)⟩
