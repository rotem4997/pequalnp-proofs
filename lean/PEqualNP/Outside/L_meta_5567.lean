import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5567

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem snocRead (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

def rises (s : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ s, x.getD i false = true → y.getD i false = true

theorem gateMono (g : Gate) (x y : List Bool)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hxy : rises g.inputs.toFinset x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases g with ⟨op, ins⟩
  rcases (show op = .and ∨ op = .or from h) with rfl | rfl
  · simp [GateOp.eval]
    intro ha i hi
    exact hxy i (List.mem_toFinset.mpr hi) (ha i hi)
  · simp [GateOp.eval]
    intro i hi hv
    exact ⟨i, hi, hxy i (List.mem_toFinset.mpr hi) hv⟩

theorem supportBound (gs : List Gate) (n out : ℕ)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ s : Finset ℕ, s.card ≤ gs.length + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → rises s x y →
      (gs.foldl step x).getD out false = true → (gs.foldl step y).getD out false = true := by
  induction gs generalizing n with
  | nil =>
    exact ⟨{out}, by simp, fun x y _ _ h => h out (by simp)⟩
  | cons g gs ih =>
    obtain ⟨s, hs, hy⟩ := ih (n+1) (fun a ha => hm a (by simp [ha]))
    obtain ⟨hop, hlen⟩ := hm g (by simp)
    by_cases hn : n ∈ s
    · refine ⟨s.erase n ∪ g.inputs.toFinset, ?_, ?_⟩
      · have h1 := Finset.card_union_le (s.erase n) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hn
        have h3 := List.toFinset_card_le g.inputs
        have h4 := Finset.card_pos.mpr ⟨n, hn⟩
        simp only [List.length_cons]
        omega
      · intro x y hx hy' hr
        apply hy (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy'])
        intro i hi
        simp only [step, snocRead, hx, hy']
        by_cases he : i = n
        · simp only [he, ite_eq_left]
          apply gateMono _ _ _ hop
          exact fun j hj => hr j (Finset.mem_union_right _ hj)
        · simp only [ite_eq_right he]
          exact hr i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hi⟩))
    · refine ⟨s, by simp only [List.length_cons]; omega, ?_⟩
      intro x y hx hy' hr
      apply hy (step x g) (step y g) (by simp [step, hx]) (by simp [step, hy'])
      intro i hi
      have he : i ≠ n := fun h => hn (h ▸ hi)
      simpa only [step, snocRead, hx, hy', ite_eq_right he] using hr i hi

def adj (u v : Fin 4) := (4591 : ℕ).testBit (4 * u.val + v.val)

theorem separation : ∀ i : Fin 8, ∃ a b c d : Fin 4,
    adj a b = true ∧ adj c d = false ∧ ∀ j : Fin 8, j ≠ i →
    (oneEach a b).getD j false = true → (oneEach c d).getD j false = true := by
  decide +kernel

theorem lower : ¬ RepSizeAtMost adj 6 := by
  rintro ⟨C, hm, hsz, rep⟩
  obtain ⟨s, hs, mono⟩ := supportBound C.gates 8 C.output hm
  have sub : Finset.range 8 ⊆ s := by
    intro i hi
    have hi' : i < 8 := Finset.mem_range.mp hi
    by_contra hn
    obtain ⟨a,b,c,d,hab,hcd,hpair⟩ := separation ⟨i, hi'⟩
    have hxy : rises s (oneEach a b) (oneEach c d) := by
      intro j hj
      by_cases hj' : j < 8
      · apply hpair ⟨j,hj'⟩
        exact fun e => hn ((Fin.mk.inj e) ▸ hj)
      · rw [List.getD_eq_default _ _ (by simp [oneEach]; omega)]
        simp
    have h := mono _ _ (by simp [oneEach]) (by simp [oneEach]) hxy ((rep a b).trans hab)
    change C.eval (oneEach c d) = true at h
    rw [rep c d, hcd] at h
    contradiction
  have hcard := Finset.card_le_card sub
  simp only [Finset.card_range] at hcard
  change C.gates.length ≤ 6 at hsz
  omega

theorem upper : RepSizeAtMost adj 7 := by
  refine ⟨⟨[⟨GateOp.or, [2,3]⟩, ⟨GateOp.and, [8,4]⟩, ⟨GateOp.or, [5,6]⟩,
    ⟨GateOp.or, [10,7]⟩, ⟨GateOp.and, [1,11]⟩, ⟨GateOp.or, [0,9]⟩,
    ⟨GateOp.or, [12,13]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5567

theorem PEqualNP.Outside.L_meta_5567 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  exact ⟨PEqualNP.Outside.L_meta_5567.upper, PEqualNP.Outside.L_meta_5567.lower⟩
