import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7784_aux

def S (g : (Fin 26 → Bool) → Bool) : Bool → Set (Fin 26 → Bool) := fun b => {x | g x = b}

theorem orStep (g1 g2 : (Fin 26 → Bool) → Bool) : ∀ b : Bool,
    S (fun x => g1 x || g2 x) b ⊆ if b = true then S g1 b ∪ S g2 b else S g1 b ∩ S g2 b := by
  intro b x hx
  rcases Bool.eq_false_or_eq_true (g1 x) with h | h <;> cases b <;> simp_all [S]

theorem andStep (g1 g2 : (Fin 26 → Bool) → Bool) : ∀ b : Bool,
    S (fun x => g1 x && g2 x) b ⊆ if b = false then S g1 b ∪ S g2 b else S g1 b ∩ S g2 b := by
  intro b x hx
  rcases Bool.eq_false_or_eq_true (g1 x) with h | h <;> cases b <;> simp_all [S]

def v (k : Fin 26) : (Fin 26 → Bool) → Bool := fun x => x k
def e : (Fin 26 → Bool) → Bool := fun x => x 0 || x 1
def o (g1 g2 : (Fin 26 → Bool) → Bool) : (Fin 26 → Bool) → Bool := fun x => g1 x || g2 x
def a (g1 g2 : (Fin 26 → Bool) → Bool) : (Fin 26 → Bool) → Bool := fun x => g1 x && g2 x

def g0 := o e (v 3)
def g1 := o g0 (v 9)
def g2 := o (v 12) (v 0)
def g3 := o g2 (v 2)
def g4 := o g3 (v 8)
def g5 := o (v 10) (v 11)
def g6 := o g5 (v 0)
def g7 := o g6 (v 6)
def g8 := o (v 4) (v 5)
def g9 := o g8 (v 7)
def g10 := o g9 (v 0)
def g11 := a (v 13) g1
def g12 := a (v 14) g4
def g13 := a (v 16) g7
def g14 := a (v 22) g10
def g15 := o g11 g12
def g16 := o g15 g13
def g17 := o g16 g14

def L : List (Bool → Set (Fin 26 → Bool)) :=
  [S g0, S g1, S g2, S g3, S g4, S g5, S g6, S g7, S g8, S g9, S g10, S g11, S g12, S g13,
    S g14, S g15, S g16, S g17]

theorem final (x : Fin 26 → Bool) :
    (∃ (x3 : Fin 13) (x4 : Fin 13), (x4 : ℕ) ∈ [0, 1, 3, 9] ∧ ((x3 : ℕ) + x4) % 13 ∈ [0, 1, 3, 9] ∧
      x (Fin.castAdd 13 x3) = true ∧ x (Fin.natAdd 13 x4) = true) ↔ g17 x = true := by
  simp [Fin.exists_fin_succ, g17, g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3,
    g2, g1, g0, o, a, v, e, Fin.castAdd, Fin.natAdd, Fin.castLE]
  constructor
  · intro h
    rcases h with ((h|h|h|h)|h|h|h|h|h|h|h|h|h|h|h|h) <;> simp [h]
  · intro h
    rcases h with (((⟨h1, (((h2|h2)|h2)|h2)⟩|⟨h1, (((h2|h2)|h2)|h2)⟩)|⟨h1, (((h2|h2)|h2)|h2)⟩)|⟨h1, (((h2|h2)|h2)|h2)⟩) <;> simp [h1, h2]

end PEqualNP.Outside.L_meta_7784_aux

theorem PEqualNP.Outside.L_meta_7784 : have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x1 : (Fin (26 : ℕ) → Bool) → Bool) (x2 : Bool) => {x3 : Fin (26 : ℕ) → Bool | x1 x3 = x2}) ((List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), ↑x4 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x4 : Bool → Set (Fin (26 : ℕ) → Bool)),   x3.length ≤ (18 : ℕ) ∧     x4 ∈ x1 ++ x3 ∧       (∀ (x5 : Fin x3.length),           have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑x5) x3;           ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x3.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10) ∧         ∀ (x5 : Fin (26 : ℕ) → Bool), (x2 x5 → x5 ∈ x4 Bool.true) ∧ (¬x2 x5 → x5 ∈ x4 Bool.false) := by
  intro x1 x2
  have hin : ∀ k : Fin 26, L_meta_7784_aux.S (L_meta_7784_aux.v k) ∈ x1 := by
    intro k
    exact List.mem_map.mpr ⟨fun x => x k, List.mem_append_left _ (List.mem_ofFn.mpr ⟨k, rfl⟩), rfl⟩
  have he : L_meta_7784_aux.S L_meta_7784_aux.e ∈ x1 :=
    List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  refine ⟨L_meta_7784_aux.L, L_meta_7784_aux.S L_meta_7784_aux.g17, by decide,
    List.mem_append_right _ (List.get_mem L_meta_7784_aux.L ⟨17, by decide⟩), ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.e, List.mem_append_left _ he, L_meta_7784_aux.S (L_meta_7784_aux.v 3), List.mem_append_left _ (hin 3), true, L_meta_7784_aux.orStep L_meta_7784_aux.e (L_meta_7784_aux.v 3)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g0, List.mem_append_right _ (List.get_mem (List.take 1 L_meta_7784_aux.L) ⟨0, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 9), List.mem_append_left _ (hin 9), true, L_meta_7784_aux.orStep L_meta_7784_aux.g0 (L_meta_7784_aux.v 9)⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 12), List.mem_append_left _ (hin 12), L_meta_7784_aux.S (L_meta_7784_aux.v 0), List.mem_append_left _ (hin 0), true, L_meta_7784_aux.orStep (L_meta_7784_aux.v 12) (L_meta_7784_aux.v 0)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g2, List.mem_append_right _ (List.get_mem (List.take 3 L_meta_7784_aux.L) ⟨2, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 2), List.mem_append_left _ (hin 2), true, L_meta_7784_aux.orStep L_meta_7784_aux.g2 (L_meta_7784_aux.v 2)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g3, List.mem_append_right _ (List.get_mem (List.take 4 L_meta_7784_aux.L) ⟨3, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 8), List.mem_append_left _ (hin 8), true, L_meta_7784_aux.orStep L_meta_7784_aux.g3 (L_meta_7784_aux.v 8)⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 10), List.mem_append_left _ (hin 10), L_meta_7784_aux.S (L_meta_7784_aux.v 11), List.mem_append_left _ (hin 11), true, L_meta_7784_aux.orStep (L_meta_7784_aux.v 10) (L_meta_7784_aux.v 11)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g5, List.mem_append_right _ (List.get_mem (List.take 6 L_meta_7784_aux.L) ⟨5, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 0), List.mem_append_left _ (hin 0), true, L_meta_7784_aux.orStep L_meta_7784_aux.g5 (L_meta_7784_aux.v 0)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g6, List.mem_append_right _ (List.get_mem (List.take 7 L_meta_7784_aux.L) ⟨6, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 6), List.mem_append_left _ (hin 6), true, L_meta_7784_aux.orStep L_meta_7784_aux.g6 (L_meta_7784_aux.v 6)⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 4), List.mem_append_left _ (hin 4), L_meta_7784_aux.S (L_meta_7784_aux.v 5), List.mem_append_left _ (hin 5), true, L_meta_7784_aux.orStep (L_meta_7784_aux.v 4) (L_meta_7784_aux.v 5)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g8, List.mem_append_right _ (List.get_mem (List.take 9 L_meta_7784_aux.L) ⟨8, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 7), List.mem_append_left _ (hin 7), true, L_meta_7784_aux.orStep L_meta_7784_aux.g8 (L_meta_7784_aux.v 7)⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g9, List.mem_append_right _ (List.get_mem (List.take 10 L_meta_7784_aux.L) ⟨9, by decide⟩), L_meta_7784_aux.S (L_meta_7784_aux.v 0), List.mem_append_left _ (hin 0), true, L_meta_7784_aux.orStep L_meta_7784_aux.g9 (L_meta_7784_aux.v 0)⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 13), List.mem_append_left _ (hin 13), L_meta_7784_aux.S L_meta_7784_aux.g1, List.mem_append_right _ (List.get_mem (List.take 11 L_meta_7784_aux.L) ⟨1, by decide⟩), false, L_meta_7784_aux.andStep (L_meta_7784_aux.v 13) L_meta_7784_aux.g1⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 14), List.mem_append_left _ (hin 14), L_meta_7784_aux.S L_meta_7784_aux.g4, List.mem_append_right _ (List.get_mem (List.take 12 L_meta_7784_aux.L) ⟨4, by decide⟩), false, L_meta_7784_aux.andStep (L_meta_7784_aux.v 14) L_meta_7784_aux.g4⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 16), List.mem_append_left _ (hin 16), L_meta_7784_aux.S L_meta_7784_aux.g7, List.mem_append_right _ (List.get_mem (List.take 13 L_meta_7784_aux.L) ⟨7, by decide⟩), false, L_meta_7784_aux.andStep (L_meta_7784_aux.v 16) L_meta_7784_aux.g7⟩
    · exact ⟨L_meta_7784_aux.S (L_meta_7784_aux.v 22), List.mem_append_left _ (hin 22), L_meta_7784_aux.S L_meta_7784_aux.g10, List.mem_append_right _ (List.get_mem (List.take 14 L_meta_7784_aux.L) ⟨10, by decide⟩), false, L_meta_7784_aux.andStep (L_meta_7784_aux.v 22) L_meta_7784_aux.g10⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g11, List.mem_append_right _ (List.get_mem (List.take 15 L_meta_7784_aux.L) ⟨11, by decide⟩), L_meta_7784_aux.S L_meta_7784_aux.g12, List.mem_append_right _ (List.get_mem (List.take 15 L_meta_7784_aux.L) ⟨12, by decide⟩), true, L_meta_7784_aux.orStep L_meta_7784_aux.g11 L_meta_7784_aux.g12⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g15, List.mem_append_right _ (List.get_mem (List.take 16 L_meta_7784_aux.L) ⟨15, by decide⟩), L_meta_7784_aux.S L_meta_7784_aux.g13, List.mem_append_right _ (List.get_mem (List.take 16 L_meta_7784_aux.L) ⟨13, by decide⟩), true, L_meta_7784_aux.orStep L_meta_7784_aux.g15 L_meta_7784_aux.g13⟩
    · exact ⟨L_meta_7784_aux.S L_meta_7784_aux.g16, List.mem_append_right _ (List.get_mem (List.take 17 L_meta_7784_aux.L) ⟨16, by decide⟩), L_meta_7784_aux.S L_meta_7784_aux.g14, List.mem_append_right _ (List.get_mem (List.take 17 L_meta_7784_aux.L) ⟨14, by decide⟩), true, L_meta_7784_aux.orStep L_meta_7784_aux.g16 L_meta_7784_aux.g14⟩
  · intro x
    have h := L_meta_7784_aux.final x
    cases hg : L_meta_7784_aux.g17 x
    · exact ⟨fun hx => absurd (h.mp hx) (by simp [hg]), fun _ => hg⟩
    · exact ⟨fun _ => hg, fun hx => absurd (h.mpr hg) hx⟩
