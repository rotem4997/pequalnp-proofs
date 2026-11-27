import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5994_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4700 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.or, [14, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

abbrev BE : BinaryTree ℕ := BinaryTree.nil
abbrev BN (v : ℕ) (l r : BinaryTree ℕ) : BinaryTree ℕ := BinaryTree.node v l r
abbrev BL (v : ℕ) : BinaryTree ℕ := BinaryTree.node v BinaryTree.nil BinaryTree.nil

def InTree (x : ℕ) : BinaryTree ℕ → Prop
  | BinaryTree.nil => False
  | BinaryTree.node v l r => x = v ∨ InTree x l ∨ InTree x r

def treeMem (x : ℕ) : BinaryTree ℕ → Bool
  | BinaryTree.nil => false
  | BinaryTree.node v l r =>
    if x == v then true
    else if x < v then treeMem x l
    else treeMem x r

theorem treeMem_imp {x : ℕ} : ∀ t : BinaryTree ℕ, treeMem x t = true → InTree x t
  | BinaryTree.nil, h => by simp [treeMem] at h
  | BinaryTree.node v l r, h => by
    unfold treeMem at h
    by_cases h1 : x == v
    · exact Or.inl (beq_iff_eq.mp h1)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : x < v
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inl (treeMem_imp l h))
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inr (treeMem_imp r h))

def checkTree (f : ℕ → Bool) : BinaryTree ℕ → Bool
  | BinaryTree.nil => true
  | BinaryTree.node v l r => f v && checkTree f l && checkTree f r

theorem checkTree_node {f : ℕ → Bool} {v : ℕ} {l r : BinaryTree ℕ}
    (hv : f v = true) (hl : checkTree f l = true) (hr : checkTree f r = true) :
    checkTree f (BN v l r) = true := by
  simp [checkTree, hv, hl, hr]

theorem checkTree_sound {f : ℕ → Bool} : ∀ t : BinaryTree ℕ, checkTree f t = true → ∀ x, InTree x t → f x = true
  | BinaryTree.nil, _, _, hx => hx.elim
  | BinaryTree.node v l r, h, x, hx => by
    simp only [checkTree, Bool.and_eq_true] at h
    rcases hx with rfl | hl | hr
    · exact h.1.1
    · exact checkTree_sound l h.1.2 x hl
    · exact checkTree_sound r h.2 x hr

def freeM (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = 65535 ∨ v ∈ S

def combM : Fin 2 → ℕ → ℕ → ℕ
  | 0, a, b => a &&& b
  | 1, a, b => a ||| b

def CanM (f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => freeM S f
  | k+1, S => ∃ (o : Fin 2) (a b : ℕ), freeM S a ∧ freeM S b ∧ CanM f k (insert (combM o a b) S)

theorem freeMMono {v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : freeM S v) : freeM T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem freeMSub {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) {v : ℕ} (hv : freeM S v) : freeM T v := by
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact h v hv

theorem monoCM_free {f k : ℕ} {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) (hc : CanM f k S) : CanM f k T := by
  induction k generalizing S T with
  | zero => exact freeMSub h hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, a, b, freeMSub h ha, freeMSub h hb, ih ?_ hh⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · exact freeMMono (Finset.subset_insert _ _) (h x hx)

theorem monoCM {f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : CanM f k S) : CanM f k T :=
  monoCM_free (fun x hx => Or.inr (Or.inr (h hx))) hc

theorem stepUpM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) : CanM f (k+1) S :=
  ⟨0, 0, 0, Or.inl rfl, Or.inl rfl, monoCM (Finset.subset_insert _ _) hc⟩

theorem smallM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) :
    ∃ T ⊆ S, T.card ≤ k+1 ∧ CanM f k T := by
  induction k generalizing S with
  | zero =>
    rcases hc with h | h | h
    · exact ⟨∅, by simp, by simp, Or.inl h⟩
    · exact ⟨∅, by simp, by simp, Or.inr (Or.inl h)⟩
    · exact ⟨{f}, by simpa, by simp, Or.inr (Or.inr (by simp))⟩
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    let v := combM o a b
    obtain ⟨T, hT, hn, hc'⟩ := ih hh
    change T ⊆ insert v S at hT
    by_cases hv : v ∈ T
    · let U := T.erase v ∪ ({a, b} ∩ S)
      have hu : T.erase v ⊆ S := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hU : U ⊆ S := Finset.union_subset hu Finset.inter_subset_right
      have liftWire : ∀ w ∈ ({a, b} : Finset ℕ), freeM S w → freeM U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a, b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a, b} ∩ S) ⊆ {a, b})
      have htwo : ({a, b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U, hU, by dsimp [U]; omega, o, a, b, liftWire a (by simp) ha, liftWire b (by simp) hb, monoCM ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hx⟩)))
    · refine ⟨T, ?_, by omega, stepUpM hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem agreeM {f k a b : ℕ} {S : Finset ℕ} (hb16 : b < 16) (hc : CanM f k S)
    (hs : ∀ v ∈ S, v.testBit a = true → v.testBit b = true) :
    f.testBit a = true → f.testBit b = true := by
  have h65535 : ∀ i < 16, (65535 : ℕ).testBit i = true := by
    intro i hi
    exact (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨i, hi⟩
  induction k generalizing S with
  | zero =>
    rcases hc with rfl | rfl | h
    · simp
    · intro _; exact h65535 b hb16
    · exact hs _ h
  | succ k ih =>
    have w {v} (hv : freeM S v) : v.testBit a = true → v.testBit b = true := by
      rcases hv with rfl | rfl | h
      · simp
      · intro _; exact h65535 b hb16
      · exact hs _ h
    obtain ⟨o, x, y, hx, hy, hh⟩ := hc
    have hg : (combM o x y).testBit a = true → (combM o x y).testBit b = true := by
      fin_cases o
      · intro h
        simp only [combM, Nat.testBit_land, Bool.and_eq_true] at h ⊢
        exact ⟨w hx h.1, w hy h.2⟩
      · intro h
        simp only [combM, Nat.testBit_lor, Bool.or_eq_true] at h ⊢
        exact h.imp (w hx) (w hy)
    apply ih hh
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact hg
    · exact hs _ h

def gtM : GateOp → List ℕ → ℕ
  | GateOp.and, [] => 65535
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | _, _ => 0

def tstepM (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gtM g.op (g.inputs.map fun i => T.getD i 0)]

def tabsM (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl tstepM T0

def GOkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem gtM_testBit (p : Fin 16) (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (l : List ℕ) (hl : l.length ≤ 2) :
    (gtM op l).testBit p.val = op.eval (l.map fun t => t.testBit p.val) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have h6 : (65535 : ℕ).testBit p.val = true :=
    (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) p
  match l, hl with
  | [], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval, h6]
  | [a], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval]
  | [a, b], _ => rcases hop with rfl | rfl <;> simp [gtM, GateOp.eval]

theorem gtM_bit_false (p : ℕ) (hp : 16 ≤ p) (op : GateOp) (l : List ℕ)
    (hl : ∀ x ∈ l, x.testBit p = false) : (gtM op l).testBit p = false := by
  have h6 : (65535 : ℕ).testBit p = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by decide) hp))
  cases op <;> cases l with
  | nil => simp [gtM, h6]
  | cons a t =>
    cases t with
    | nil => simp [gtM, hl a (by simp)]
    | cons b t' => simp [gtM, hl a (by simp), hl b (by simp)]

theorem getD_map_testBitM (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

theorem wires_tabsM (p : Fin 16) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOkM g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p.val)
        = (tabsM T0 gs).map fun t => t.testBit p.val := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p.val) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p.val).getD i false)]
        = (tstepM T0 g).map fun t => t.testBit p.val := by
      simp only [tstepM, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gtM_testBit p g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBitM T0 p.val i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

theorem tabsM_bit_false (p : ℕ) (hp : 16 ≤ p) :
    ∀ (gs : List Gate) (T0 : List ℕ),
      (∀ t ∈ T0, t.testBit p = false) →
      ∀ t ∈ tabsM T0 gs, t.testBit p = false := by
  intro gs
  induction gs with
  | nil => intro T0 hT0; exact hT0
  | cons g gs ih =>
    intro T0 hT0
    apply ih (tstepM T0 g)
    intro t ht
    simp only [tstepM, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hT0 t ht
    · apply gtM_bit_false p hp g.op
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [List.getD_eq_getElem?_getD]
      cases h : T0[i]? with
      | none => simp
      | some v => exact hT0 v (List.mem_of_getElem? h)

theorem getWireM (T : List ℕ) (i : ℕ) : freeM T.toFinset (T.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => exact Or.inl rfl
  | some t => exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? h)))

theorem gateChoiceM (T : List ℕ) (g : Gate) (hg : GOkM g) :
    ∃ (o : Fin 2) (a b : ℕ), freeM T.toFinset a ∧ freeM T.toFinset b ∧
      gtM g.op (g.inputs.map fun i => T.getD i 0) = combM o a b := by
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  generalize g.inputs = ins at hl ⊢
  have z : freeM T.toFinset 0 := Or.inl rfl
  have u : freeM T.toFinset 65535 := Or.inr (Or.inl rfl)
  match ins, hl with
  | [], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨1, 65535, 0, u, z, by simp [gtM, combM]⟩
    · exact ⟨1, 0, 0, z, z, rfl⟩
  | [i], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨1, _, 0, getWireM T i, z, by simp [gtM, combM]⟩
    · exact ⟨1, _, 0, getWireM T i, z, by simp [gtM, combM]⟩
  | [i, j], _ =>
    rcases hop with h | h <;> rw [h]
    · exact ⟨0, _, _, getWireM T i, getWireM T j, rfl⟩
    · exact ⟨1, _, _, getWireM T i, getWireM T j, rfl⟩

theorem fromTabsM (f : ℕ) (gs : List Gate) (T : List ℕ) (ok : ∀ g ∈ gs, GOkM g)
    (h : freeM (tabsM T gs).toFinset f) : CanM f gs.length T.toFinset := by
  induction gs generalizing T with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨o, a, b, ha, hb, e⟩ := gateChoiceM T g (ok g (by simp))
    have hh := ih (tstepM T g) (fun g' hg' => ok _ (by simp [hg'])) h
    refine ⟨o, a, b, ha, hb, ?_⟩
    rw [← e]
    simpa [tstepM] using hh

def cuts : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | k, x :: xs => if (x :: xs).length ≤ k then [x :: xs] else
      match k with
      | 0 => [[]]
      | j+1 => (cuts j xs).map (x :: ·) ++ cuts (j+1) xs
termination_by _ l => l.length

theorem cutsSpec (k : ℕ) (l : List ℕ) (T : Finset ℕ) (h : T ⊆ l.toFinset) (n : T.card ≤ k) :
    ∃ U ∈ cuts k l, T ⊆ U.toFinset := by
  induction l generalizing k T with
  | nil => exact ⟨[], by simp [cuts], h⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], by simp [cuts], by simp [he]⟩
    | succ j =>
      rw [cuts]
      split
      · exact ⟨_, by simp, h⟩
      ·
        by_cases hx : x ∈ T
        · have hs : T.erase x ⊆ xs.toFinset := by
            intro y hy
            have hh := h (Finset.mem_of_mem_erase hy)
            simpa [Finset.ne_of_mem_erase hy] using hh
          obtain ⟨U, hU, sub⟩ := ih j (T.erase x) hs (by rw [Finset.card_erase_of_mem hx]; omega)
          refine ⟨x::U, List.mem_append_left _ (List.mem_map.mpr ⟨U, hU, rfl⟩), ?_⟩
          intro y hy
          by_cases e : y = x
          · simp [e]
          · simpa [e] using sub (Finset.mem_erase.mpr ⟨e, hy⟩)
        · have hs : T ⊆ xs.toFinset := by
            intro y hy
            have e : y ≠ x := fun he => hx (he ▸ hy)
            simpa [e] using h hy
          obtain ⟨U, hU, sub⟩ := ih (j+1) T hs n
          exact ⟨U, List.mem_append_right _ hU, sub⟩

theorem cuts_mem_sub : ∀ (l : List ℕ) (k : ℕ) (U : List ℕ), U ∈ cuts k l → ∀ y ∈ U, y ∈ l
  | [], k, U, hU, y, hy => by simp [cuts] at hU; subst hU; simp at hy
  | z :: zs, k, U, hU, y, hy => by
    unfold cuts at hU
    split at hU
    · simp at hU; subst hU; exact hy
    · cases k with
      | zero => simp at hU; subst hU; simp at hy
      | succ j =>
        simp only [List.mem_append, List.mem_map] at hU
        rcases hU with ⟨V, hV, rfl⟩ | hU
        · rcases List.mem_cons.mp hy with rfl | hy
          · simp
          · exact List.mem_cons_of_mem _ (cuts_mem_sub zs j V hV y hy)
        · exact List.mem_cons_of_mem _ (cuts_mem_sub zs (j + 1) U hU y hy)

def sepFold (p0Mask a : ℕ) (U : List ℕ) : ℕ :=
  U.foldl (fun acc v => if v.testBit a then acc &&& v else acc) p0Mask

theorem sepFold_bit_true (a b : ℕ) : ∀ (U : List ℕ) (acc : ℕ),
    (U.foldl (fun acc v => if v.testBit a then acc &&& v else acc) acc).testBit b = true →
    acc.testBit b = true ∧ ∀ v ∈ U, v.testBit a = true → v.testBit b = true
  | [], acc, h => ⟨h, by simp⟩
  | v :: vs, acc, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨hstep, hvs⟩ := sepFold_bit_true a b vs _ h
    by_cases hva : v.testBit a = true
    · simp only [hva, ↓reduceIte, Nat.testBit_land, Bool.and_eq_true] at hstep
      refine ⟨hstep.1, fun w hw hwa => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hstep.2
      · exact hvs w hw hwa
    · simp only [hva, ↓reduceIte] at hstep
      refine ⟨hstep, fun w hw hwa => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hwa hva
      · exact hvs w hw hwa

def sepOk (p1List : List ℕ) (p0Mask : ℕ) (U : List ℕ) : Bool :=
  p1List.all fun a => sepFold p0Mask a U == 0

theorem coveredM {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {U : List ℕ}
    (hc : CanM f k U.toFinset)
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false) :
    sepOk p1List p0Mask U = true := by
  rw [sepOk, List.all_eq_true]
  intro a ha
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.zero_testBit]
  cases htb : (sepFold p0Mask a U).testBit b with
  | false => rfl
  | true =>
    obtain ⟨hb0, hall⟩ := sepFold_bit_true a b U p0Mask htb
    have hfa := hp1 a ha
    have ⟨hb16, hfb⟩ := hp0 b hb0
    have hfb' := agreeM hb16 hc (fun v hv => hall v (List.mem_toFinset.mp hv)) hfa
    exact absurd (hfb'.symm.trans hfb) (by decide)

def insOne (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x == y then y :: ys else if x < y then x :: y :: ys else y :: insOne x ys

def sortU : List ℕ → List ℕ
  | [] => []
  | x :: xs => insOne x (sortU xs)

theorem mem_insOne (x z : ℕ) : ∀ l : List ℕ, z ∈ insOne x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insOne]
  | y :: ys => by
    unfold insOne
    by_cases h1 : x == y
    · simp only [h1, ↓reduceIte]
      have hxy := beq_iff_eq.mp h1; subst hxy; simp
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : x < y
      · simp only [h2, ↓reduceIte]; simp
      · simp only [h2, ↓reduceIte]; simp [mem_insOne x z ys]; tauto

theorem mem_sortU (z : ℕ) : ∀ l : List ℕ, z ∈ sortU l ↔ z ∈ l
  | [] => by simp [sortU]
  | x :: xs => by simp [sortU, mem_insOne, mem_sortU z xs]

def pack : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 65536 * pack xs

def unpack (n : ℕ) : List ℕ :=
  if n = 0 then []
  else (n &&& 65535) :: unpack (n >>> 16)
termination_by n
decreasing_by
  have h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
  omega

theorem unpack_lt : ∀ (n x : ℕ), x ∈ unpack n → x < 65536 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro x hx
    unfold unpack at hx
    by_cases h0 : n = 0
    · simp [h0] at hx
    · simp only [h0, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      · have hlt : n >>> 16 < n := by
          have h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
          omega
        exact ih (n >>> 16) hlt x hx

theorem unpack_pack : ∀ l : List ℕ, (∀ x ∈ l, 0 < x ∧ x < 65536) → unpack (pack l) = l
  | [], _ => by unfold unpack; simp [pack]
  | x :: xs, hl => by
    have hx := hl x (by simp)
    have hne : x + 65536 * pack xs ≠ 0 := by omega
    rw [pack, unpack]
    simp only [hne, ↓reduceIte]
    have hlo : (x + 65536 * pack xs) &&& 65535 = x := by
      rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hhi : (x + 65536 * pack xs) >>> 16 = pack xs := by
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [hlo, hhi, unpack_pack xs (fun y hy => hl y (by simp [hy]))]

def normList (U : List ℕ) : List ℕ :=
  sortU (U.filter (fun x => decide (0 < x) && decide (x < 65535)))

def packSet (U : List ℕ) : ℕ := pack (normList U)

theorem normList_bounds (U : List ℕ) : ∀ x ∈ normList U, 0 < x ∧ x < 65536 := by
  intro x hx
  rw [normList, mem_sortU, List.mem_filter] at hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  omega

theorem unpack_packSet (U : List ℕ) : unpack (packSet U) = normList U :=
  unpack_pack (normList U) (normList_bounds U)

theorem freeM_packSet {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    ∀ x ∈ U.toFinset, freeM (unpack (packSet U)).toFinset x := by
  intro x hx
  have hxm := List.mem_toFinset.mp hx
  have hlt := hU x hxm
  by_cases h0 : x = 0
  · exact Or.inl h0
  · by_cases h1 : x = 65535
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      rw [unpack_packSet, List.mem_toFinset, normList, mem_sortU, List.mem_filter]
      exact ⟨hxm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩

def opPairsM : List ℕ → List ℕ
  | [] => []
  | a :: t => t.flatMap (fun b => [a &&& b, a ||| b]) ++ opPairsM t

theorem mem_opPairsM : ∀ (w : List ℕ) (a b : ℕ), a ∈ w → b ∈ w →
    a &&& b ∈ w ++ opPairsM w ∧ a ||| b ∈ w ++ opPairsM w
  | [], _, _, ha, _ => by simp at ha
  | x :: t, a, b, ha, hb => by
    simp only [List.mem_cons] at ha hb
    simp only [opPairsM, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false]
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact ⟨Or.inl (Or.inl (Nat.and_self _)), Or.inl (Or.inl (Nat.or_self _))⟩
    · exact ⟨Or.inr (Or.inl ⟨b, hb, Or.inl rfl⟩), Or.inr (Or.inl ⟨b, hb, Or.inr rfl⟩)⟩
    · exact ⟨Or.inr (Or.inl ⟨a, ha, Or.inl (Nat.land_comm _ _)⟩),
             Or.inr (Or.inl ⟨a, ha, Or.inr (Nat.lor_comm _ _)⟩)⟩
    · have ih := mem_opPairsM t a b ha hb
      simp only [List.mem_append] at ih
      refine ⟨?_, ?_⟩
      · rcases ih.1 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
      · rcases ih.2 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

def valsNew (S : List ℕ) : List ℕ :=
  ((opPairsM S).filter (fun v => decide (0 < v) && decide (v < 65535) && !S.contains v)).eraseDups

theorem and_65535_of_lt {x : ℕ} (hx : x < 65536) : x &&& 65535 = x := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hx

theorem or_65535_of_lt {x : ℕ} (hx : x < 65536) : x ||| 65535 = 65535 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor]
  by_cases hi : i < 16
  · have h6 : (65535 : ℕ).testBit i = true :=
      (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨i, hi⟩
    simp [h6]
  · have h2 : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hx0 : x.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx h2)
    have h60 : (65535 : ℕ).testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) h2)
    simp [hx0, h60]

theorem combM_lt {o : Fin 2} {a b : ℕ} (ha : a < 65536) (hb : b < 65536) : combM o a b < 65536 := by
  fin_cases o
  · exact Nat.and_lt_two_pow (n := 16) a hb
  · exact Nat.or_lt_two_pow (n := 16) ha hb

theorem combM_case {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) {o : Fin 2} {a b : ℕ}
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b) :
    freeM S.toFinset (combM o a b) ∨ combM o a b ∈ valsNew S := by
  have free_lt {w : ℕ} (hw : freeM S.toFinset w) : w < 65536 := by
    rcases hw with rfl | rfl | h
    · decide
    · decide
    · exact hS w (List.mem_toFinset.mp h)
  have hlt : combM o a b < 65536 := combM_lt (free_lt ha) (free_lt hb)
  rcases ha with rfl | rfl | ha'
  · left; fin_cases o
    · simp only [combM, Nat.zero_and]; exact Or.inl rfl
    · simp only [combM, Nat.zero_or]; exact hb
  · left; fin_cases o
    · simp only [combM, Nat.land_comm 65535, and_65535_of_lt (free_lt hb)]; exact hb
    · simp only [combM, Nat.lor_comm 65535, or_65535_of_lt (free_lt hb)]; exact Or.inr (Or.inl rfl)
  · rcases hb with rfl | rfl | hb'
    · left; fin_cases o
      · simp only [combM, Nat.and_zero]; exact Or.inl rfl
      · simp only [combM, Nat.or_zero]; exact Or.inr (Or.inr ha')
    · left; fin_cases o
      · simp only [combM, and_65535_of_lt (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inr ha')
      · simp only [combM, or_65535_of_lt (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inl rfl)
    · have haL := List.mem_toFinset.mp ha'
      have hbL := List.mem_toFinset.mp hb'
      have hpair := mem_opPairsM S a b haL hbL
      have hmem : combM o a b ∈ S ∨ combM o a b ∈ opPairsM S := by
        fin_cases o
        · exact List.mem_append.mp hpair.1
        · exact List.mem_append.mp hpair.2
      by_cases h0 : combM o a b = 0
      · exact Or.inl (Or.inl h0)
      · by_cases h1 : combM o a b = 65535
        · exact Or.inl (Or.inr (Or.inl h1))
        · by_cases hin : combM o a b ∈ S
          · exact Or.inl (Or.inr (Or.inr (List.mem_toFinset.mpr hin)))
          · right
            rcases hmem with h | hop
            · exact absurd h hin
            · simp only [valsNew, List.mem_eraseDups, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
              refine ⟨hop, ⟨by omega, by omega⟩, ?_⟩
              cases hc : S.contains (combM o a b) with
              | false => rfl
              | true => exact absurd (List.contains_iff_mem.mp hc) hin

theorem can1M_case {f : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) (hc : CanM f 1 S.toFinset) :
    freeM S.toFinset f ∨ f ∈ valsNew S := by
  obtain ⟨o, a, b, ha, hb, h0⟩ := hc
  rcases h0 with rfl | rfl | hm
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · rcases Finset.mem_insert.mp hm with rfl | hf
    · exact combM_case hS ha hb
    · exact Or.inl (Or.inr (Or.inr hf))

def permWGo : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | idx :: rest, k, w => (((w >>> idx) &&& 1) <<< k) ||| permWGo rest (k + 1) w

def permW (p : List ℕ) (w : ℕ) : ℕ := permWGo p 0 w

theorem permWGo_testBit : ∀ (p : List ℕ) (k w i : ℕ),
    (permWGo p k w).testBit i =
      if k ≤ i ∧ i - k < p.length then w.testBit (p.getD (i - k) 0) else false
  | [], k, w, i => by simp [permWGo]
  | idx :: rest, k, w, i => by
    simp only [permWGo, Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_land, Nat.testBit_shiftRight,
      permWGo_testBit rest (k + 1) w i]
    by_cases hlt : i < k
    · have h1 : ¬ k ≤ i := by omega
      have h2 : ¬ k + 1 ≤ i := by omega
      simp [h1, h2]
    · by_cases heq : i = k
      · subst heq
        have h2 : ¬ i + 1 ≤ i := by omega
        simp [h2]
      · have hgt : k + 1 ≤ i := by omega
        have hge : k ≤ i := by omega
        have h1f : (1 : ℕ).testBit (i - k) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega)))
        have hlen : i - k < (idx :: rest).length ↔ i - (k + 1) < rest.length := by simp; omega
        have hget : (idx :: rest).getD (i - k) 0 = rest.getD (i - (k + 1)) 0 := by
          cases hd : i - k with
          | zero => omega
          | succ m =>
            have hm : i - (k + 1) = m := by omega
            simp [hm]
        simp only [hge, hgt, h1f, Bool.and_false, Bool.false_or, decide_true, Bool.true_and, true_and, ↓reduceIte, hlen, hget]

theorem permW_testBit (p : List ℕ) (hp : p.length = 16) (w i : ℕ) :
    (permW p w).testBit i = if i < 16 then w.testBit (p.getD i 0) else false := by
  simp [permW, permWGo_testBit, hp]

theorem permW_zero (p : List ℕ) (hp : p.length = 16) : permW p 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; simp [permW_testBit p hp]

theorem permW_all (p : List ℕ) (hp : p.length = 16) (hb : ∀ x ∈ p, x < 16) : permW p 65535 = 65535 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [permW_testBit p hp]
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    have hgi : p.getD i 0 < 16 := by
      rw [List.getD_eq_getElem?_getD]
      cases hg : p[i]? with
      | none => decide
      | some v => exact hb v (List.mem_of_getElem? hg)
    have h6 : ∀ j < 16, (65535 : ℕ).testBit j = true := fun j hj =>
      (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) ⟨j, hj⟩
    rw [h6 _ hgi, h6 _ hi]
  · simp only [hi, ↓reduceIte]
    symm
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (by omega)))

theorem permWGo_lt : ∀ (p : List ℕ) (k w : ℕ), permWGo p k w < 2 ^ (k + p.length)
  | [], k, _ => by simp [permWGo]
  | idx :: rest, k, w => by
    have h1 : (((w >>> idx) &&& 1) <<< k) < 2 ^ (k + 1) := by
      rw [Nat.shiftLeft_eq]
      have hb : (w >>> idx) &&& 1 < 2 := by
        rw [show (1 : ℕ) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      have hmul : ((w >>> idx) &&& 1) * 2 ^ k < 2 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      omega
    have h1' : (((w >>> idx) &&& 1) <<< k) < 2 ^ (k + (idx :: rest).length) :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by simp))
    have h2 : permWGo rest (k + 1) w < 2 ^ (k + (idx :: rest).length) := by
      have := permWGo_lt rest (k + 1) w
      have heq : k + 1 + rest.length = k + (idx :: rest).length := by simp; omega
      rwa [heq] at this
    exact Nat.or_lt_two_pow h1' h2

theorem permW_lt (p : List ℕ) (hp : p.length = 16) (w : ℕ) : permW p w < 65536 := by
  have h := permWGo_lt p 0 w
  simp [hp] at h
  exact h

theorem permW_comb (p : List ℕ) (hp : p.length = 16) (o : Fin 2) (a b : ℕ) :
    permW p (combM o a b) = combM o (permW p a) (permW p b) := by
  apply Nat.eq_of_testBit_eq; intro i
  fin_cases o <;> simp only [combM, Nat.testBit_land, Nat.testBit_lor, permW_testBit p hp] <;> split <;> simp

theorem canM_perm (p : List ℕ) (hp : p.length = 16) (hb : ∀ x ∈ p, x < 16) {f k : ℕ} {S : Finset ℕ}
    (hc : CanM f k S) : CanM (permW p f) k (S.image (permW p)) := by
  have hfree {T : Finset ℕ} {v : ℕ} (hv : freeM T v) : freeM (T.image (permW p)) (permW p v) := by
    rcases hv with rfl | rfl | h
    · exact Or.inl (permW_zero p hp)
    · exact Or.inr (Or.inl (permW_all p hp hb))
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
  induction k generalizing S with
  | zero => exact hfree hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb', hh⟩ := hc
    refine ⟨o, permW p a, permW p b, hfree ha, hfree hb', ?_⟩
    have h' := ih hh
    rw [Finset.image_insert, permW_comb p hp] at h'
    exact h'

def treeHit (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (U : List ℕ) : Bool :=
  treeMem (packSet U) nextTree || auts.any (fun p => treeMem (packSet (U.map (permW p))) nextTree)

theorem treeHit_sound {auts : List (List ℕ)} {f k : ℕ} {nextTree : BinaryTree ℕ} {U : List ℕ}
    (hU : ∀ x ∈ U, x < 65536)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hh : treeHit auts nextTree U = true)
    (hc : CanM f k U.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  simp only [treeHit, Bool.or_eq_true, List.any_eq_true] at hh
  rcases hh with h0 | ⟨p, hp, hm⟩
  · exact ⟨packSet U, treeMem_imp nextTree h0, monoCM_free (freeM_packSet hU) hc⟩
  · obtain ⟨hlen, hbd, hfix⟩ := haut p hp
    have hcp : CanM f k (U.map (permW p)).toFinset := by
      have h1 := canM_perm p hlen hbd hc
      have heq : (U.map (permW p)).toFinset = U.toFinset.image (permW p) := by
        ext y; simp
      rw [hfix, ← heq] at h1
      exact h1
    have hUp : ∀ y ∈ U.map (permW p), y < 65536 := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
      exact permW_lt p hlen x
    exact ⟨packSet (U.map (permW p)), treeMem_imp nextTree hm, monoCM_free (freeM_packSet hUp) hcp⟩

def checkCuts (p1List : List ℕ) (p0Mask k : ℕ) (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (l : List ℕ) : Bool :=
  (cuts (k + 1) l).all fun U => !sepOk p1List p0Mask U || treeHit auts nextTree U

def verifyNode (p1List : List ℕ) (p0Mask k : ℕ) (auts : List (List ℕ)) (nextTree : BinaryTree ℕ) (packedS : ℕ) : Bool :=
  let S := unpack packedS
  checkCuts p1List p0Mask k auts nextTree S &&
  (valsNew S).all fun v => checkCuts p1List p0Mask k auts nextTree (v :: S)

theorem checkCuts_sound {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {auts : List (List ℕ)} {nextTree : BinaryTree ℕ} {l : List ℕ}
    (hl : ∀ x ∈ l, x < 65536)
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hchk : checkCuts p1List p0Mask k auts nextTree l = true)
    (hc : CanM f k l.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  obtain ⟨T, hT, hn, ht⟩ := smallM hc
  obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) l T hT hn
  have hcU := monoCM hu ht
  have htest := List.all_eq_true.mp hchk U hU
  have hcov := coveredM hcU hp1 hp0
  simp only [hcov, Bool.not_true, Bool.false_or] at htest
  have hU_lt : ∀ x ∈ U, x < 65536 := fun x hx => hl x (cuts_mem_sub l (k + 1) U hU x hx)
  exact treeHit_sound hU_lt haut htest hcU

theorem advanceNode {f k : ℕ} {p1List : List ℕ} {p0Mask : ℕ} {auts : List (List ℕ)} {nextTree : BinaryTree ℕ} {packedS : ℕ}
    (hp1 : ∀ a ∈ p1List, f.testBit a = true)
    (hp0 : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ f.testBit b = false)
    (haut : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p f = f)
    (hv : verifyNode p1List p0Mask k auts nextTree packedS = true)
    (hc : CanM f (k + 1) (unpack packedS).toFinset) :
    ∃ x, InTree x nextTree ∧ CanM f k (unpack x).toFinset := by
  simp only [verifyNode, Bool.and_eq_true] at hv
  obtain ⟨o, a, b, ha, hb, hh⟩ := hc
  have hS_lt : ∀ x ∈ unpack packedS, x < 65536 := unpack_lt packedS
  rcases combM_case hS_lt ha hb with hfree | hnew
  · have hh' : CanM f k (unpack packedS).toFinset := by
      refine monoCM_free (fun x hx => ?_) hh
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hfree
      · exact Or.inr (Or.inr hx)
    exact checkCuts_sound hS_lt hp1 hp0 haut hv.1 hh'
  · have hv_lt : combM o a b < 65536 := by
      simp only [valsNew, List.mem_eraseDups, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hnew
      omega
    have hvl : ∀ x ∈ combM o a b :: unpack packedS, x < 65536 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv_lt
      · exact hS_lt x hx
    have hchk := List.all_eq_true.mp hv.2 (combM o a b) hnew
    exact checkCuts_sound hvl hp1 hp0 haut hchk (by simpa using hh)

abbrev targetNat : ℕ := 4700
abbrev p0Mask : ℕ := 60835
def p1List : List ℕ := [2, 3, 4, 6, 9, 12]
def inputs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
def auts : List (List ℕ) := [[0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]]

def row2 : BinaryTree ℕ := BE
def row3 : BinaryTree ℕ := BN 17293973169014838047 (BN 9869713642533945359 (BN 4919076518851707120 (BL 4919075518121771520) (BL 9869713642532901151)) (BN 11022635147124998656 (BL 9869731234704196096) (BE))) (BN 17908638977408041712 (BN 17293975368038093087 (BL 17293975368004539167) (BL 17438088357057139487)) (BN 18052754165483897072 (BL 17908641176397742832) (BE)))
def row4_c0 : BinaryTree ℕ := BN 644755517940849188012047 (BN 644755517939814369329664 (BN 322377758979319748103936 (BL 322376533154597626183920) (BE)) (BL 644755517940780740051184)) (BN 644755517959412323975183 (BL 644755517955147436130319) (BL 644755517977004728188943))
def row4_c1 : BinaryTree ℕ := BN 646821553274905652363279 (BN 644756310610538910515215 (BN 644756310592946707628047 (BL 644756310592109205852400) (BE)) (BL 644756670861318725566704)) (BN 646821553277036208914447 (BL 646821553276069823382016) (BL 646822706197514065805327))
def row4_LL : BinaryTree ℕ := BN 644756310592109189005552 row4_c0 row4_c1
def row4_c2 : BinaryTree ℕ := BN 1133377794077160011399920 (BN 720314174318023529267440 (BN 677813236260166911983856 (BN 677812083338662305140976 (BL 677812083338662288294128) (BE)) (BL 720313381665728442138864)) (BN 722379417001923782377487 (BL 720314174318861047889935) (BL 722379417020688748187392))) (BN 1133377825604556391776783 (BN 1133377825602357369438720 (BL 1133377794079359001101040) (BL 1133377825602357402993152)) (BN 1133377825604556425330703 (BL 1133377825604556392694272) (BL 1133377825604556678107423)))
def row4_L : BinaryTree ℕ := BN 646822706216279031615232 row4_LL row4_c2
def row4_c3 : BinaryTree ℕ := BN 1142822558568096659869440 (BN 1133377969719744467632143 (BN 1133377969717545445294592 (BN 1133377969717545444377103 (BL 1133377938194547076956400) (BE)) (BL 1133377969717545477931023)) (BN 1142822558568096658948623 (BL 1137805044180047661826560) (BL 1142822558568096659866112))) (BN 1147286670633934605320207 (BN 1143449747866602817257487 (BL 1142822558568096692502543) (BL 1143449747866603018588447)) (BN 1153521670094212128771840 (BL 1153521670074613939306736) (BL 1173660564021154268840463)))
def row4_c4 : BinaryTree ℕ := BN 1173661356674346988404751 (BN 1173660564040812604751887 (BN 1173660564023353292095503 (BN 1173660564021214600758000 (BL 1173660564021214398382592) (BE)) (BL 1173660564023413405909232)) (BN 1173660708136342344695823 (BL 1173660564040812806082847) (BL 1173660708156000647053327))) (BN 1175727392010602458185743 (BN 1175726599357469852434672 (BL 1173665514659339030168064) (BL 1175726599377068041899776)) (BN 1183105296986893544521968 (BL 1175731549995594499949056) (BL 1183105296986953673081072)))
def row4_R : BinaryTree ℕ := BN 1173660564021214382653680 row4_c3 row4_c4
def row4 : BinaryTree ℕ := BN 1133377938192348087255280 row4_L row4_R
def row5_c0 : BinaryTree ℕ := BN 42254697623767006519864852495 (BN 42254697623699733858714910735 (BN 42254697623627378365727506447 (BL 21127348812468697980947398896) (BE)) (BL 42254697623703673477596709104)) (BN 42254697624929513567111086095 (BN 42254697624929498234077843200 (BL 42254697624708541343459180559) (BE)) (BL 42254697624933156244806435056))
def row5_c1 : BinaryTree ℕ := BN 42254749570960808635970617359 (BN 42254697626082435071449497615 (BN 42254697624988060362251173903 (BL 42254697624988043865265012751) (BE)) (BL 42254697626140966473678454799)) (BN 42254749570964468914727158000 (BL 42254749570960809740045647887) (BL 42254749571019356535185735695))
def row5_LLL : BinaryTree ℕ := BN 42254697624933157348645539584 row5_c0 row5_c1
def row5_c2 : BinaryTree ℕ := BN 42390097315496571295489851407 (BN 42254773182796883262936449264 (BN 42254773182793224148368752880 (BL 42254773181563443349065564175) (BE)) (BL 42254773182851770883395026959)) (BN 42390097317879258146089730063 (BN 42390097316726336701629206272 (BL 42390097316726335537676288015) (BE)) (BL 42390172874590062555806302223))
def row5_c3 : BinaryTree ℕ := BN 47206457780841238534338641935 (BN 44421092694831835159360176143 (BN 44421092693682572829703274736 (BL 44421092693678913655021764623) (BE)) (BL 44421168251542639569076748303)) (BN 47206457782074678448209527024 (BL 47206457782071019333641830640) (BL 47206457782129566068668104719))
def row5_LLR : BinaryTree ℕ := BN 44421092693678912550946734095 row5_c2 row5_c3
def row5_LL : BinaryTree ℕ := BN 42254749572113731244384059407 row5_LLL row5_LLR
def row5_c4 : BinaryTree ℕ := BN 74277047112640756308284277488 (BN 74277047112640756308066173168 (BN 74277047112640756247952359951 (BL 47341857473867857741079379983) (BE)) (BL 74277047112640756308081902080)) (BN 74277047112640771641115148303 (BN 74277047112640758507089428720 (BL 74277047112640758446975614991) (BE)) (BL 74277047112640775906288271375))
def row5_c5 : BinaryTree ℕ := BN 74277047113433409440671924239 (BN 74277047112784871436028215311 (BN 74277047112640775906541903633 (BL 74277047112640775906489602335) (BE)) (BL 74277047112784891094330572815)) (BN 74277049178676092503406411791 (BL 74277047113433409440906805263) (BL 74277049178676092503407395328))
def row5_LRL : BinaryTree ℕ := BN 74277047112640775906489597967 row5_c4 row5_c5
def row5_c6 : BinaryTree ℕ := BN 74277049178676094702429667343 (BN 74277049178676092563754058240 (BN 74277049178676092563535954160 (BL 74277049178676092563535953935) (BE)) (BL 74277049178676092563788726784)) (BN 74277049178676111268372221696 (BL 74277049178676111268372218368) (BL 74277049178676111268404854799))
def row5_c7 : BinaryTree ℕ := BN 74277049178820226456447156239 (BN 74277049178676112161959378959 (BN 74277049178676112161725419264 (BL 74277049178676111324206796544) (BE)) (BL 74277049178820207691482267663)) (BN 74277049179468782332499071263 (BL 74277049179468745696141705231) (BL 74277049183595205490791875072))
def row5_LRR : BinaryTree ℕ := BN 74277049178676111268606185759 row5_c6 row5_c7
def row5_LR : BinaryTree ℕ := BN 74277049178676092503624516111 row5_LRL row5_LRR
def row5_L : BinaryTree ℕ := BN 47206509728102330839373709327 row5_LL row5_LR
def row5_c8 : BinaryTree ℕ := BN 74277056557517837175285088271 (BN 74277056557373740752192864496 (BN 74277056557373724186232487951 (BL 74277056557373722047356600560) (BE)) (BL 74277056557373740808026521840)) (BN 74277080169206155156252590320 (BN 74277080169206136335454109936 (BL 74277058623409058242696839183) (BE)) (BL 74277080169206155156253507824))
def row5_c9 : BinaryTree ℕ := BN 74277080174156774520515596575 (BN 74277080169998788690669797616 (BN 74277080169206155994058395921 (BL 74277080169206155994006093839) (BE)) (BL 74277080169998789528188420111)) (BN 74277369487940188456190214384 (BL 74277080174156774520516448529) (BL 74277369487940208054613639183))
def row5_RLL : BinaryTree ℕ := BN 74277080169206155156487471344 row5_c8 row5_c9
def row5_c10 : BinaryTree ℕ := BN 74277383655832290197731606543 (BN 74277383655039655825795776752 (BN 74277369488732841588795965455 (BL 74277369488732840751277342960) (BE)) (BL 74277383655832289360212984048)) (BN 74567191375383622270535663631 (BN 74567191375383622270301703936 (BL 74567191375383603505335894031) (BE)) (BL 74567191376176255804717989903))
def row5_c11 : BinaryTree ℕ := BN 74937122676185680093178302208 (BN 74937122676185680032795983887 (BN 74896019198318782641074077711 (BL 74896019198318782640855973903) (BE)) (BL 74937122676185680033014087695)) (BN 74937122676185695426211545103 (BL 74937122676185695425940946959) (BL 74937153666715739257987661839))
def row5_RLR : BinaryTree ℕ := BN 74567222365913666158182072560 row5_c10 row5_c11
def row5_RL : BinaryTree ℕ := BN 74277369488732840695443685616 row5_RLL row5_RLR
def row5_c12 : BinaryTree ℕ := BN 75597196171294286011061764111 (BN 75597196170005958476732301327 (BN 75188579246665522901352972303 (BL 74937609232458006380706467584) (BE)) (BL 75597196171235739276035490032)) (BN 76917018723690366162727600143 (BN 76917018723690365196359958768 (BL 76917018723690365131917623311) (BE)) (BL 76917018723690379425587593456))
def row5_c13 : BinaryTree ℕ := BN 76917018724978692666028982287 (BN 76917018724920145931220812016 (BN 76917018723694320075260559600 (BL 76917018723694305781591572495) (BE)) (BL 76917018724920161264289644784)) (BN 76917018724978692726376628464 (BL 76917018724978692666247086095) (BL 76917018724978692726411300608))
def row5_RRL : BinaryTree ℕ := BN 76917018723690379425602338831 row5_c12 row5_c13
def row5_c14 : BinaryTree ℕ := BN 76917341103471759558230212623 (BN 76917341102679106425624461552 (BN 76917070671010004232344436751 (BL 76917070671010004232108507151) (BE)) (BL 76917341103471758720711590128)) (BN 76917343168714461385930510080 (BL 76917343168714442620964700175) (BL 76917343168714461441764167424))
def row5_c15 : BinaryTree ℕ := BN 77052470362748295904519782415 (BN 77052418416716984398787903728 (BN 77052418415487203599484715023 (BL 76917374159244505273810878704) (BE)) (BL 77052418416775531133814177807)) (BN 77052742860511299853497601792 (BL 77052742860511281088531791887) (BL 77535988743333055269367185423))
def row5_RRR : BinaryTree ℕ := BN 76917374159244505217977221360 row5_c14 row5_c15
def row5_RR : BinaryTree ℕ := BN 76917018724978708059444543503 row5_RRL row5_RRR
def row5_R : BinaryTree ℕ := BN 74937153666715743523160784911 row5_RL row5_RR
def row5 : BinaryTree ℕ := BN 74277056557373721987228041456 row5_L row5_R
def row6_c0 : BinaryTree ℕ := BN 2769203863551216515094176652591119 (BN 2769203863547379596267494739804400 (BN 2769203863547379519986676303659023 (BL 2769203863466785690610745994117135) (BL 2769203863547379592327875858006031)) (BN 2769203863547619399999803290026224 (BL 2769203863547380601133161360916495) (BE))) (BN 2769208815307536733846844914794511 (BN 2769207267882487627122600802517007 (BL 2769203863622937456051659641716751) (BE)) (BN 2911180730772941285294475588927503 (BL 2778077417748977198137321988292623) (BE)))
def row6_c1 : BinaryTree ℕ := BN 4867820559574024605405424724738063 (BN 4867820559574024601465805860765711 (BN 4867820559574024601464839493124336 (BL 4867820559574024601464775050788879) (BE)) (BN 4867820559574024601479068735504399 (BL 4867820559574024601479068720759024) (BE))) (BN 4867820559574025831245574353977584 (BN 4867820559574025610271091581779983 (BL 4867820559574024605419718393725168) (BE)) (BN 4867820559574025831260907422810352 (BL 4867820559574025831260907151294479) (BE)))
def row6_LL : BinaryTree ℕ := BN 3093722417205806319108901338873871 row6_c0 row6_c1
def row6_c2 : BinaryTree ℕ := BN 4867820559574025889807702577709071 (BN 4867820559574025889792369544466176 (BN 4867820559574025889792309380251663 (BL 4867820559574025889792309162147855) (BL 4867820559574025889792369509794032)) (BN 4867820559574025889807702543040527 (BL 4867820559574025889807702307110927) (BE))) (BN 4867820559625971921103875241672719 (BN 4867820559574025889811129961615104 (BL 4867820559574025889811074361917455) (BE)) (BN 4867820694973716398303242617880591 (BL 4867820559625971921103875477602319) (BE)))
def row6_c3 : BinaryTree ℕ := BN 4867820694973717628099374718386191 (BN 4867820694973717628084041921069071 (BN 4867820694973717628083981791526927 (BL 4867820694973717628083981573423119) (BE)) (BN 4867820694973717628084041955741440 (BL 4867820694973717628084041921069296) (BE))) (BN 4867820694973717686630776947343375 (BN 4867820694973717631743156488765455 (BL 4867820694973717628099374988984335) (BE)) (BN 4867820695025666118942659133374479 (BL 4867820695025663659395547652947983) (BE)))
def row6_LR : BinaryTree ℕ := BN 4867820694973716398317536286867471 row6_c2 row6_c3
def row6_L : BinaryTree ℕ := BN 4867820559574025834920082084462832 row6_LL row6_LR
def row6_c4 : BinaryTree ℕ := BN 4867822725969094580661055191515151 (BN 4867821178544045473935651438067727 (BN 4867820695296095387063296994643712 (BL 4867820695296095387063241160986368) (BL 4867821178544044244154912500350991)) (BN 4867822725969094580660995061973007 (BL 4867822725969093350880256124256271) (BE))) (BN 4867822725969094584320169995141360 (BN 4867822725969094584320169759211535 (BL 4867822725969094580676388224761871) (BE)) (BN 4867822725969094639207790453719055 (BL 4867822725969094584338934741926128) (BE)))
def row6_c5 : BinaryTree ℕ := BN 4867841686761649416505031519109360 (BN 4867822726291472339640310501015792 (BN 4867822726291472339640254667358448 (BL 4867822726021040611972561159323663) (BE)) (BN 4867841686761648186724232215920655 (BL 4867822726293538374976510136221711) (BE))) (BN 4867841686761649475051766545383439 (BN 4867841686761649420164146086805744 (BL 4867841686761649416520364316426255) (BE)) (BN 4867842615216678880540177327980559 (BL 4867841686813595447816537250988047) (BE)))
def row6_RL : BinaryTree ℕ := BN 4867822725969094639226555200503823 row6_c4 row6_c5
def row6_c6 : BinaryTree ℕ := BN 4911081302701881679220624772300815 (BN 4911079271706504726643611265925135 (BN 4886837484972518021683445610053647 (BL 4886835453977141069106432339607567) (BE)) (BN 4911079272028883715370551410163727 (BL 4911079271706505956410056788410383) (BE))) (BN 5040833739075772706035244100222991 (BN 4954337848278105405253612200787983 (BL 4911111158658367906165918930042895) (BE)) (BN 5040833739156366683748487136280591 (BL 5040833739156366679807837462331407) (BE)))
def row6_c7 : BinaryTree ℕ := BN 5040854866505179203096609367785487 (BN 5040854866505177914769075038322703 (BN 5040833739160204832341614571552783 (BL 5040833739160203602575169049067535) (BE)) (BN 5040854866505179148208988909207792 (BL 5040854866505179144549874341511408) (BE))) (BN 5040857032900247893965295049506831 (BN 5040855001904870941388281779060751 (BL 5040854866557125175861380073390095) (BE)) (BN 5049728556106468547198758701498383 (BL 5049707293357964285618314384769039) (BE)))
def row6_RR : BinaryTree ℕ := BN 5040833739156367688616426031022095 row6_c6 row6_c7
def row6_R : BinaryTree ℕ := BN 4867842615268624911851743425331215 row6_RL row6_RR
def row6 : BinaryTree ℕ := BN 4867820695296095387044476195176463 row6_L row6_R
def row7 : BinaryTree ℕ := BN 319017488192243360714658553989710217231 (BN 319017488192243356876509960862274945039 (BN 319017488192243276282532247619238887439 (BL 181482544401441068962732118235887435791) (BL 319017488192243356876506020212600995855)) (BN 319017488192243356877514828801169686543 (BL 319017488192243356877514826529131986959) (BL 319017488192243360713428787544187731983))) (BN 319017630190237931250663729819873705999 (BN 319017497086924907286576572666273071119 (BL 319017497065797558474111830689523433487) (BL 319017630169110582438198987843359997967)) (BN 330357464531283420417216624195617685519 (BL 319018872783611456160069804986677067791) (BE)))
def row8 : BinaryTree ℕ := BL 319017488192243356876506020212600995855

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit : checkCuts p1List p0Mask 8 auts row8 inputs = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk3 : checkTree (verifyNode p1List p0Mask 2 auts row2) row3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4LLL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4LLR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk4LLV : (verifyNode p1List p0Mask 3 auts row3) 644756310592109189005552 = true := by decide +kernel
theorem chk4LL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_LL = true := checkTree_node chk4LLV chk4LLL chk4LLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4LR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk4LV : (verifyNode p1List p0Mask 3 auts row3) 646822706216279031615232 = true := by decide +kernel
theorem chk4L : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_L = true := checkTree_node chk4LV chk4LL chk4LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4RL : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4RR : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_c4 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk4RV : (verifyNode p1List p0Mask 3 auts row3) 1173660564021214382653680 = true := by decide +kernel
theorem chk4R : checkTree (verifyNode p1List p0Mask 3 auts row3) row4_R = true := checkTree_node chk4RV chk4RL chk4RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk4V : (verifyNode p1List p0Mask 3 auts row3) 1133377938192348087255280 = true := by decide +kernel
theorem chk4 : checkTree (verifyNode p1List p0Mask 3 auts row3) row4 = true := checkTree_node chk4V chk4L chk4R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LLLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LLLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LLLV : (verifyNode p1List p0Mask 4 auts row4) 42254697624933157348645539584 = true := by decide +kernel
theorem chk5LLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_LLL = true := checkTree_node chk5LLLV chk5LLLL chk5LLLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LLRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LLRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LLRV : (verifyNode p1List p0Mask 4 auts row4) 44421092693678912550946734095 = true := by decide +kernel
theorem chk5LLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_LLR = true := checkTree_node chk5LLRV chk5LLRL chk5LLRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LLV : (verifyNode p1List p0Mask 4 auts row4) 42254749572113731244384059407 = true := by decide +kernel
theorem chk5LL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_LL = true := checkTree_node chk5LLV chk5LLL chk5LLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LRLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c4 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LRLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c5 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LRLV : (verifyNode p1List p0Mask 4 auts row4) 74277047112640775906489597967 = true := by decide +kernel
theorem chk5LRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_LRL = true := checkTree_node chk5LRLV chk5LRLL chk5LRLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LRRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c6 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LRRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c7 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LRRV : (verifyNode p1List p0Mask 4 auts row4) 74277049178676111268606185759 = true := by decide +kernel
theorem chk5LRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_LRR = true := checkTree_node chk5LRRV chk5LRRL chk5LRRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LRV : (verifyNode p1List p0Mask 4 auts row4) 74277049178676092503624516111 = true := by decide +kernel
theorem chk5LR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_LR = true := checkTree_node chk5LRV chk5LRL chk5LRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LV : (verifyNode p1List p0Mask 4 auts row4) 47206509728102330839373709327 = true := by decide +kernel
theorem chk5L : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_L = true := checkTree_node chk5LV chk5LL chk5LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RLLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RLLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c9 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RLLV : (verifyNode p1List p0Mask 4 auts row4) 74277080169206155156487471344 = true := by decide +kernel
theorem chk5RLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_RLL = true := checkTree_node chk5RLLV chk5RLLL chk5RLLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RLRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c10 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RLRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c11 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RLRV : (verifyNode p1List p0Mask 4 auts row4) 74567222365913666158182072560 = true := by decide +kernel
theorem chk5RLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_RLR = true := checkTree_node chk5RLRV chk5RLRL chk5RLRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RLV : (verifyNode p1List p0Mask 4 auts row4) 74277369488732840695443685616 = true := by decide +kernel
theorem chk5RL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_RL = true := checkTree_node chk5RLV chk5RLL chk5RLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RRLL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c12 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RRLR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c13 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RRLV : (verifyNode p1List p0Mask 4 auts row4) 76917018723690379425602338831 = true := by decide +kernel
theorem chk5RRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_RRL = true := checkTree_node chk5RRLV chk5RRLL chk5RRLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RRRL : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c14 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RRRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_c15 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RRRV : (verifyNode p1List p0Mask 4 auts row4) 76917374159244505217977221360 = true := by decide +kernel
theorem chk5RRR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_RRR = true := checkTree_node chk5RRRV chk5RRRL chk5RRRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RRV : (verifyNode p1List p0Mask 4 auts row4) 76917018724978708059444543503 = true := by decide +kernel
theorem chk5RR : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_RR = true := checkTree_node chk5RRV chk5RRL chk5RRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RV : (verifyNode p1List p0Mask 4 auts row4) 74937153666715743523160784911 = true := by decide +kernel
theorem chk5R : checkTree (verifyNode p1List p0Mask 4 auts row4) row5_R = true := checkTree_node chk5RV chk5RL chk5RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5V : (verifyNode p1List p0Mask 4 auts row4) 74277056557373721987228041456 = true := by decide +kernel
theorem chk5 : checkTree (verifyNode p1List p0Mask 4 auts row4) row5 = true := checkTree_node chk5V chk5L chk5R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6LLL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6LLR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6LLV : (verifyNode p1List p0Mask 5 auts row5) 3093722417205806319108901338873871 = true := by decide +kernel
theorem chk6LL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_LL = true := checkTree_node chk6LLV chk6LLL chk6LLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6LRL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6LRR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6LRV : (verifyNode p1List p0Mask 5 auts row5) 4867820694973716398317536286867471 = true := by decide +kernel
theorem chk6LR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_LR = true := checkTree_node chk6LRV chk6LRL chk6LRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6LV : (verifyNode p1List p0Mask 5 auts row5) 4867820559574025834920082084462832 = true := by decide +kernel
theorem chk6L : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_L = true := checkTree_node chk6LV chk6LL chk6LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6RLL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c4 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6RLR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c5 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6RLV : (verifyNode p1List p0Mask 5 auts row5) 4867822725969094639226555200503823 = true := by decide +kernel
theorem chk6RL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_RL = true := checkTree_node chk6RLV chk6RLL chk6RLR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6RRL : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c6 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6RRR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_c7 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6RRV : (verifyNode p1List p0Mask 5 auts row5) 5040833739156367688616426031022095 = true := by decide +kernel
theorem chk6RR : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_RR = true := checkTree_node chk6RRV chk6RRL chk6RRR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6RV : (verifyNode p1List p0Mask 5 auts row5) 4867842615268624911851743425331215 = true := by decide +kernel
theorem chk6R : checkTree (verifyNode p1List p0Mask 5 auts row5) row6_R = true := checkTree_node chk6RV chk6RL chk6RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6V : (verifyNode p1List p0Mask 5 auts row5) 4867820695296095387044476195176463 = true := by decide +kernel
theorem chk6 : checkTree (verifyNode p1List p0Mask 5 auts row5) row6 = true := checkTree_node chk6V chk6L chk6R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk7 : checkTree (verifyNode p1List p0Mask 6 auts row6) row7 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk8 : checkTree (verifyNode p1List p0Mask 7 auts row7) row8 = true := by decide +kernel

theorem hp1_proof : ∀ a ∈ p1List, targetNat.testBit a = true := by decide +kernel
theorem hp0_fin : ∀ b : Fin 16, p0Mask.testBit b.val = true → targetNat.testBit b.val = false := by decide +kernel
theorem hp0_proof : ∀ b : ℕ, p0Mask.testBit b = true → b < 16 ∧ targetNat.testBit b = false := by
  intro b hb
  by_cases h16 : b < 16
  · exact ⟨h16, hp0_fin ⟨b, h16⟩ hb⟩
  · have hf : p0Mask.testBit b = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : p0Mask < 2 ^ 16) (Nat.pow_le_pow_right (by decide) (by omega)))
    exact absurd hb (by simp [hf])
theorem haut_proof : ∀ p ∈ auts, p.length = 16 ∧ (∀ x ∈ p, x < 16) ∧ permW p targetNat = targetNat := by decide +kernel
theorem inputs_lt : ∀ t ∈ inputs, t < 65536 := by decide
theorem targetNat_lt : targetNat < 2 ^ 16 := by decide

theorem excluded (hc : CanM targetNat 8 inputs.toFinset) : False := by
  obtain ⟨x8, hx8, c8⟩ := checkCuts_sound inputs_lt hp1_proof hp0_proof haut_proof chkInit hc
  obtain ⟨x7, hx7, c7⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row8 chk8 x8 hx8) c8
  obtain ⟨x6, hx6, c6⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row7 chk7 x7 hx7) c7
  obtain ⟨x5, hx5, c5⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row6 chk6 x6 hx6) c6
  obtain ⟨x4, hx4, c4⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row5 chk5 x5 hx5) c5
  obtain ⟨x3, hx3, c3⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row4 chk4 x4 hx4) c4
  obtain ⟨x2, hx2, c2⟩ := advanceNode hp1_proof hp0_proof haut_proof (checkTree_sound row3 chk3 x3 hx3) c3
  exact hx2

theorem oneEach_map (p : Fin 16) :
    oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4) =
    inputs.map (fun t => t.testBit p.val) := by
  revert p; decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (4700 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hok : ∀ g ∈ C.gates, GOkM g := hC
  let out := (tabsM inputs C.gates).getD C.output 0
  have obs (p : Fin 16) : out.testBit p.val = targetNat.testBit p.val := by
    have hval := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
    unfold Circuit.eval Circuit.wires at hval
    rw [oneEach_map p, wires_tabsM p C.gates inputs hok, getD_map_testBitM] at hval
    dsimp only at hval
    have he : 4 * (p.val / 4) + p.val % 4 = p.val := Nat.div_add_mod p.val 4
    rw [he] at hval
    exact hval
  have hout_eq : out = targetNat := by
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < 16
    · exact obs ⟨p, hp⟩
    · have h2 : 2 ^ 16 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
      have hT : targetNat.testBit p = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le targetNat_lt h2)
      have hI : ∀ v ∈ inputs, v.testBit p = false := fun v hv => Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (inputs_lt v hv) h2)
      have hall := tabsM_bit_false p (by omega) C.gates inputs hI
      have hout_f : out.testBit p = false := by
        dsimp [out]
        rw [List.getD_eq_getElem?_getD]
        cases hget : (tabsM inputs C.gates)[C.output]? with
        | none => simp
        | some v => exact hall v (List.mem_of_getElem? hget)
      rw [hout_f, hT]
  have hc := fromTabsM out C.gates inputs hok (getWireM _ C.output)
  rw [hout_eq] at hc
  have pad {k j : ℕ} (hj : k ≤ j) (ha : CanM targetNat k inputs.toFinset) : CanM targetNat j inputs.toFinset := by
    induction hj with
    | refl => exact ha
    | step _ ih => exact stepUpM ih
  change C.gates.length ≤ _ at hs
  exact excluded (pad hs hc)

end PEqualNP.Outside.L_meta_5994_aux

theorem PEqualNP.Outside.L_meta_5994 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4700 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4700 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_5994_aux.upper, PEqualNP.Outside.L_meta_5994_aux.lower⟩
