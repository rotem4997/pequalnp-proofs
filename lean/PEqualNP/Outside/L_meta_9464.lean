import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9464_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev targetNat : ℕ := 30825
abbrev maskParam : ℕ := 30825
abbrev fullVal : ℕ := 0x78697869786978697869786978697869
def bits : List ℕ := [2, 4, 16, 128, 256, 512, 1024, 32768]
def inputs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

abbrev E : BinaryTree (ℕ × ℕ) := BinaryTree.nil
abbrev N (v h : ℕ) (l r : BinaryTree (ℕ × ℕ)) : BinaryTree (ℕ × ℕ) := BinaryTree.node (v, h) l r
abbrev L (v h : ℕ) : BinaryTree (ℕ × ℕ) := BinaryTree.node (v, h) BinaryTree.nil BinaryTree.nil

def InTree (x : ℕ) : BinaryTree (ℕ × ℕ) → Prop
  | BinaryTree.nil => False
  | BinaryTree.node vh l r => x = vh.1 ∨ InTree x l ∨ InTree x r

def treeMem (x : ℕ) : BinaryTree (ℕ × ℕ) → Bool
  | BinaryTree.nil => false
  | BinaryTree.node vh l r =>
    if x == vh.1 then true
    else if x < vh.1 then treeMem x l
    else treeMem x r

theorem treeMem_imp {x : ℕ} : ∀ t : BinaryTree (ℕ × ℕ), treeMem x t = true → InTree x t
  | BinaryTree.nil, h => by simp [treeMem] at h
  | BinaryTree.node vh l r, h => by
    unfold treeMem at h
    by_cases h1 : x == vh.1
    · exact Or.inl (beq_iff_eq.mp h1)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : x < vh.1
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inl (treeMem_imp l h))
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inr (treeMem_imp r h))

def checkTree (f : ℕ → ℕ → Bool) : BinaryTree (ℕ × ℕ) → Bool
  | BinaryTree.nil => true
  | BinaryTree.node vh l r => f vh.1 vh.2 && checkTree f l && checkTree f r

theorem checkTree_node {f : ℕ → ℕ → Bool} {v h : ℕ} {l r : BinaryTree (ℕ × ℕ)}
    (hv : f v h = true) (hl : checkTree f l = true) (hr : checkTree f r = true) :
    checkTree f (N v h l r) = true := by
  simp [checkTree, hv, hl, hr]

theorem checkTree_sound {f : ℕ → ℕ → Bool} :
    ∀ t : BinaryTree (ℕ × ℕ), checkTree f t = true → ∀ x, InTree x t → ∃ h, f x h = true
  | BinaryTree.nil, _, _, hx => hx.elim
  | BinaryTree.node vh l r, hc, x, hx => by
    simp only [checkTree, Bool.and_eq_true] at hc
    rcases hx with rfl | hl | hr
    · exact ⟨vh.2, hc.1.1⟩
    · exact checkTree_sound l hc.1.2 x hl
    · exact checkTree_sound r hc.2 x hr

def freeM (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = 65535 ∨ v ∈ S

def combM : Fin 2 → ℕ → ℕ → ℕ
  | 0, a, b => a &&& b
  | 1, a, b => a ||| b

theorem combM_comm (o : Fin 2) (a b : ℕ) : combM o a b = combM o b a := by
  fin_cases o
  · exact Nat.land_comm a b
  · exact Nat.lor_comm a b

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

def foldLor (f : ℕ → ℕ) (l : List ℕ) : ℕ := l.foldl (fun a x => a ||| f x) 0

theorem foldl_lor_shift (f : ℕ → ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    l.foldl (fun a x => a ||| f x) acc = acc ||| l.foldl (fun a x => a ||| f x) 0
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, Nat.zero_or]
    rw [foldl_lor_shift f xs (acc ||| f x), foldl_lor_shift f xs (f x), Nat.lor_assoc]

theorem foldLor_cons (f : ℕ → ℕ) (x : ℕ) (xs : List ℕ) :
    foldLor f (x :: xs) = f x ||| foldLor f xs := by
  simp only [foldLor, List.foldl_cons, Nat.zero_or]
  exact foldl_lor_shift f xs (f x)

theorem foldLor_testBit (f : ℕ → ℕ) (i : ℕ) : ∀ l : List ℕ,
    (foldLor f l).testBit i = true ↔ ∃ x ∈ l, (f x).testBit i = true
  | [] => by simp [foldLor]
  | x :: xs => by
    rw [foldLor_cons, Nat.testBit_lor, Bool.or_eq_true, foldLor_testBit f i xs]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨x, by simp, h⟩
      · exact ⟨y, by simp [hy], h⟩
    · rintro ⟨y, hy, h⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h⟩

def cutsM : ℕ → List (ℕ × ℕ) → List (List ℕ × ℕ)
  | _, [] => [([], 0)]
  | k, (x, mx) :: xs =>
    if ((x, mx) :: xs).length ≤ k then
      [(((x, mx) :: xs).map Prod.fst, ((x, mx) :: xs).foldl (fun a p => a ||| p.2) 0)]
    else
      match k with
      | 0 => [([], 0)]
      | j + 1 =>
        (cutsM j xs).map (fun p => (x :: p.1, mx ||| p.2)) ++ cutsM (j + 1) xs
termination_by _ l => l.length

theorem cutsM_spec (f : ℕ → ℕ) : ∀ (l : List ℕ) (k : ℕ) (U : List ℕ),
    U ∈ cuts k l → (U, foldLor f U) ∈ cutsM k (l.map fun x => (x, f x))
  | [], k, U, hU => by
    simp [cuts] at hU; subst hU; simp [cutsM, foldLor]
  | x :: xs, k, U, hU => by
    unfold cuts at hU
    simp only [List.map_cons]
    unfold cutsM
    have hlen : ((x, f x) :: xs.map fun y => (y, f y)).length ≤ k ↔ (x :: xs).length ≤ k := by simp
    by_cases hl : (x :: xs).length ≤ k
    · simp only [hl, ↓reduceIte, List.mem_singleton] at hU
      subst hU
      have hl' : ((x, f x) :: xs.map fun y => (y, f y)).length ≤ k := hlen.mpr hl
      simp only [hl', ↓reduceIte, List.mem_singleton, Prod.mk.injEq]
      constructor
      · simp [Function.comp_def]
      · simp only [foldLor, List.foldl_cons, Nat.zero_or, List.foldl_map]
    · simp only [hl, ↓reduceIte] at hU
      have hl' : ¬ ((x, f x) :: xs.map fun y => (y, f y)).length ≤ k := fun h => hl (hlen.mp h)
      simp only [hl', ↓reduceIte]
      cases k with
      | zero => simp at hU; subst hU; simp [foldLor]
      | succ j =>
        simp only [List.mem_append, List.mem_map] at hU ⊢
        rcases hU with ⟨V, hV, rfl⟩ | hU
        · left
          refine ⟨(V, foldLor f V), cutsM_spec f xs j V hV, ?_⟩
          simp [foldLor_cons]
        · right
          exact cutsM_spec f xs (j + 1) U hU

def isStrict : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && isStrict (b :: t)

theorem isStrict_gt : ∀ (a : ℕ) (t : List ℕ), isStrict (a :: t) = true → ∀ z ∈ t, a < z
  | _, [], _, _, hz => by simp at hz
  | a, b :: t, h, z, hz => by
    simp only [isStrict, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact Nat.lt_trans h.1 (isStrict_gt b t h.2 z hz)

theorem isStrict_nodup : ∀ (l : List ℕ), isStrict l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_singleton a
  | a :: b :: t, h => by
    have hgt := isStrict_gt a (b :: t) h
    simp only [isStrict, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.nodup_cons.mpr ⟨fun ha => Nat.lt_irrefl a (hgt a ha), isStrict_nodup (b :: t) h.2⟩

theorem mem_erase_of_nodup : ∀ {l : List ℕ}, l.Nodup → ∀ {x z : ℕ}, z ∈ l.erase x ↔ z ∈ l ∧ z ≠ x
  | [], _, _, _ => by simp
  | a :: t, hnd, x, z => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    by_cases hax : a = x
    · subst hax
      simp only [List.erase_cons_head, List.mem_cons]
      constructor
      · intro hz; exact ⟨Or.inr hz, fun h => ha (h ▸ hz)⟩
      · rintro ⟨rfl | hz, hne⟩
        · exact absurd rfl hne
        · exact hz
    · have hbeq : ¬ (a == x) = true := by simp [hax]
      simp only [List.erase_cons_tail hbeq, List.mem_cons, mem_erase_of_nodup ht]
      constructor
      · rintro (rfl | ⟨hz, hne⟩)
        · exact ⟨Or.inl rfl, hax⟩
        · exact ⟨Or.inr hz, hne⟩
      · rintro ⟨rfl | hz, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hz, hne⟩

def drop1M : List (ℕ × ℕ) → List (ℕ × ℕ × List ℕ × ℕ)
  | [] => []
  | (x, mx) :: xs =>
    (x, mx, xs.map Prod.fst, xs.foldl (fun a p => a ||| p.2) 0) ::
      (drop1M xs).map (fun p => (p.1, p.2.1, x :: p.2.2.1, mx ||| p.2.2.2))

theorem drop1M_spec (f : ℕ → ℕ) : ∀ (l : List ℕ), l.Nodup → ∀ x ∈ l,
    (x, f x, l.erase x, foldLor f (l.erase x)) ∈ drop1M (l.map fun w => (w, f w))
  | [], _, _, hx => by simp at hx
  | a :: t, hnd, x, hx => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, drop1M, List.mem_cons, List.mem_map]
    rcases List.mem_cons.mp hx with rfl | hxt
    · left
      simp [List.erase_cons_head, Function.comp_def, foldLor, List.foldl_map]
    · right
      have hne : a ≠ x := fun h => ha (h ▸ hxt)
      have hbeq : ¬ (a == x) = true := by simp [hne]
      refine ⟨(x, f x, t.erase x, foldLor f (t.erase x)), drop1M_spec f t ht x hxt, ?_⟩
      simp [List.erase_cons_tail hbeq, foldLor_cons]

theorem drop1M_tagged_aux (f : ℕ → ℕ) (fullVal : ℕ) : ∀ (l : List ℕ), l.Nodup → ∀ (acc : ℕ),
    (drop1M (l.map fun w => (w, f w))).map (fun p => (p.1, p.2.1, (acc ||| p.2.2.2) != fullVal)) =
      l.map (fun w => (w, f w, (acc ||| foldLor f (l.erase w)) != fullVal))
  | [], _, _ => rfl
  | a :: t, hnd, acc => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, drop1M, List.map_map]
    congr 1
    · simp [List.erase_cons_head, foldLor, List.foldl_map]
    · have ih := drop1M_tagged_aux f fullVal t ht (acc ||| f a)
      have h1 : (fun p : ℕ × ℕ × List ℕ × ℕ => (p.1, p.2.1, (acc ||| (f a ||| p.2.2.2)) != fullVal))
          = (fun p : ℕ × ℕ × List ℕ × ℕ => (p.1, p.2.1, ((acc ||| f a) ||| p.2.2.2) != fullVal)) := by
        funext p; rw [Nat.lor_assoc]
      change (drop1M (t.map fun w => (w, f w))).map
          (fun p => (p.1, p.2.1, (acc ||| (f a ||| p.2.2.2)) != fullVal)) = _
      rw [h1, ih]
      apply List.map_congr_left
      intro w hw
      have hne : a ≠ w := fun h => ha (h ▸ hw)
      have hbeq : ¬ (a == w) = true := by simp [hne]
      rw [List.erase_cons_tail hbeq, foldLor_cons, Nat.lor_assoc]

theorem drop1M_tagged (f : ℕ → ℕ) (fullVal : ℕ) (l : List ℕ) (hnd : l.Nodup) :
    (drop1M (l.map fun w => (w, f w))).map (fun p => (p.1, p.2.1, p.2.2.2 != fullVal)) =
      l.map (fun w => (w, f w, foldLor f (l.erase w) != fullVal)) := by
  have h := drop1M_tagged_aux f fullVal l hnd 0
  simpa only [Nat.zero_or] using h

def drop2Only : List (ℕ × ℕ) → List (ℕ × ℕ × List ℕ × ℕ)
  | [] => []
  | (x, mx) :: xs =>
    (drop1M xs).map (fun p => (x, p.1, p.2.2.1, p.2.2.2)) ++
      (drop2Only xs).map (fun p => (p.1, p.2.1, x :: p.2.2.1, mx ||| p.2.2.2))

theorem drop2Only_spec (f : ℕ → ℕ) : ∀ (l : List ℕ), l.Nodup → ∀ x ∈ l, ∀ y ∈ l, x ≠ y →
    (x, y, (l.erase x).erase y, foldLor f ((l.erase x).erase y)) ∈ drop2Only (l.map fun w => (w, f w)) ∨
    (y, x, (l.erase y).erase x, foldLor f ((l.erase y).erase x)) ∈ drop2Only (l.map fun w => (w, f w))
  | [], _, _, hx, _, _, _ => by simp at hx
  | a :: t, hnd, x, hx, y, hy, hxy => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, drop2Only, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp hx with rfl | hxt <;> rcases List.mem_cons.mp hy with rfl | hyt
    · exact absurd rfl hxy
    · left; left
      refine ⟨(y, f y, t.erase y, foldLor f (t.erase y)), drop1M_spec f t ht y hyt, ?_⟩
      simp [List.erase_cons_head]
    · right; left
      refine ⟨(x, f x, t.erase x, foldLor f (t.erase x)), drop1M_spec f t ht x hxt, ?_⟩
      simp [List.erase_cons_head]
    · have hax : a ≠ x := fun h => ha (h ▸ hxt)
      have hay : a ≠ y := fun h => ha (h ▸ hyt)
      have hbx : ¬ (a == x) = true := by simp [hax]
      have hby : ¬ (a == y) = true := by simp [hay]
      rcases drop2Only_spec f t ht x hxt y hyt hxy with h1 | h2
      · left; right
        refine ⟨(x, y, (t.erase x).erase y, foldLor f ((t.erase x).erase y)), h1, ?_⟩
        simp [List.erase_cons_tail hbx, List.erase_cons_tail hby, foldLor_cons]
      · right; right
        refine ⟨(y, x, (t.erase y).erase x, foldLor f ((t.erase y).erase x)), h2, ?_⟩
        simp [List.erase_cons_tail hby, List.erase_cons_tail hbx, foldLor_cons]

def drop1BAdj : List (ℕ × ℕ × Bool × List (ℕ × ℕ)) → List (ℕ × Bool × List (ℕ × ℕ) × List ℕ × ℕ)
  | [] => []
  | (x, mx, ex, ax) :: xs =>
    (x, ex, ax, xs.map Prod.fst, xs.foldl (fun a p => a ||| p.2.1) 0) ::
      (drop1BAdj xs).map (fun p => (p.1, p.2.1, p.2.2.1, x :: p.2.2.2.1, mx ||| p.2.2.2.2))

theorem drop1BAdj_spec (f : ℕ → ℕ) (e : ℕ → Bool) (adj : ℕ → List (ℕ × ℕ)) :
    ∀ (l : List ℕ), l.Nodup → ∀ x ∈ l,
      (x, e x, adj x, l.erase x, foldLor f (l.erase x)) ∈ drop1BAdj (l.map fun w => (w, f w, e w, adj w))
  | [], _, _, hx => by simp at hx
  | a :: t, hnd, x, hx => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, drop1BAdj, List.mem_cons, List.mem_map]
    rcases List.mem_cons.mp hx with rfl | hxt
    · left
      simp [List.erase_cons_head, Function.comp_def, foldLor, List.foldl_map]
    · right
      have hne : a ≠ x := fun h => ha (h ▸ hxt)
      have hbeq : ¬ (a == x) = true := by simp [hne]
      refine ⟨(x, e x, adj x, t.erase x, foldLor f (t.erase x)), drop1BAdj_spec f e adj t ht x hxt, ?_⟩
      simp [List.erase_cons_tail hbeq, foldLor_cons]

def drop2BAdj : List (ℕ × ℕ × Bool × List (ℕ × ℕ)) →
    List (ℕ × Bool × List (ℕ × ℕ) × ℕ × Bool × List (ℕ × ℕ) × List ℕ × ℕ)
  | [] => []
  | (x, mx, ex, ax) :: xs =>
    (drop1BAdj xs).map (fun p => (x, ex, ax, p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2)) ++
      (drop2BAdj xs).map (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
        x :: p.2.2.2.2.2.2.1, mx ||| p.2.2.2.2.2.2.2))

def countNonEss : List (ℕ × ℕ × Bool) → ℕ
  | [] => 0
  | (_, _, e) :: rest => (if e then 0 else 1) + countNonEss rest

theorem countNonEss_eq_zero (f : ℕ → ℕ) (e : ℕ → Bool) : ∀ (l : List ℕ),
    countNonEss (l.map fun w => (w, f w, e w)) = 0 → ∀ w ∈ l, e w = true
  | [], _, _, hw => by simp at hw
  | a :: t, hz, w, hw => by
    simp only [List.map_cons, countNonEss] at hz
    have ha : e a = true := by cases hea : e a <;> simp_all
    have ht : countNonEss (t.map fun w => (w, f w, e w)) = 0 := by simp [ha] at hz; omega
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ha
    · exact countNonEss_eq_zero f e t ht w hw

theorem countNonEss_ge_one (f : ℕ → ℕ) (e : ℕ → Bool) : ∀ (l : List ℕ) (x : ℕ),
    x ∈ l → e x = false → 1 ≤ countNonEss (l.map fun w => (w, f w, e w))
  | [], _, hx, _ => by simp at hx
  | a :: t, x, hx, hex => by
    simp only [List.map_cons, countNonEss]
    rcases List.mem_cons.mp hx with rfl | hxt
    · simp [hex]
    · have ih := countNonEss_ge_one f e t x hxt hex; omega

theorem countNonEss_ge_two (f : ℕ → ℕ) (e : ℕ → Bool) : ∀ (l : List ℕ), l.Nodup →
    ∀ (x y : ℕ), x ∈ l → y ∈ l → x ≠ y → e x = false → e y = false →
      2 ≤ countNonEss (l.map fun w => (w, f w, e w))
  | [], _, _, _, hx, _, _, _, _ => by simp at hx
  | a :: t, hnd, x, y, hx, hy, hxy, hex, hey => by
    obtain ⟨_, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, countNonEss]
    rcases List.mem_cons.mp hx with rfl | hxt <;> rcases List.mem_cons.mp hy with rfl | hyt
    · exact absurd rfl hxy
    · have h1 := countNonEss_ge_one f e t y hyt hey
      simp [hex]; omega
    · have h1 := countNonEss_ge_one f e t x hxt hex
      simp [hey]; omega
    · have ih := countNonEss_ge_two f e t ht x y hxt hyt hxy hex hey
      omega

theorem and_two_pow_ne_zero_iff (v a : ℕ) : (v &&& 2 ^ a != 0) = v.testBit a := by
  cases hv : v.testBit a with
  | true =>
    simp only [bne_iff_ne, ne_eq]
    intro h0
    have ht := congrArg (fun n => n.testBit a) h0
    simp [Nat.testBit_two_pow_self, hv] at ht
  | false =>
    simp only [bne_eq_false_iff_eq]
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : a = i
    · subst hi; simp [hv]
    · simp [hi]

def sepM (M : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | bitB :: rest, w => (if w &&& bitB == 0 then w &&& M else 0) ||| (sepM M rest w <<< 16)

def fullM (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: rest => M ||| (fullM M rest <<< 16)

theorem sepM_lt_bit_false (M : ℕ) (hM : M < 2 ^ 16) (bitB w i : ℕ) (hi : 16 ≤ i) :
    (if w &&& bitB == 0 then w &&& M else 0).testBit i = false := by
  split
  · have hlt : w &&& M < 2 ^ 16 := Nat.and_lt_two_pow w hM
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hi))
  · simp

theorem coveredM_sepM {M k : ℕ} (hM : M < 2 ^ 16) {U : List ℕ} (hc : CanM M k U.toFinset) :
    ∀ (p0Bits : List ℕ), (∀ bitB ∈ p0Bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ M.testBit b = false) →
      foldLor (sepM M p0Bits) U = fullM M p0Bits
  | [], _ => by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [fullM, Nat.zero_testBit]
    cases h : (foldLor (sepM M []) U).testBit i with
    | false => rfl
    | true =>
      obtain ⟨w, _, hw⟩ := (foldLor_testBit (sepM M []) i U).mp h
      simp [sepM] at hw
  | bitB :: rest, hp0 => by
    obtain ⟨b, rfl, hb16, hMb⟩ := hp0 bitB (by simp)
    have hrest := coveredM_sepM hM hc rest (fun x hx => hp0 x (by simp [hx]))
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 16
    · have hsh : ∀ n : ℕ, (n <<< 16).testBit i = false := by
        intro n; rw [Nat.testBit_shiftLeft]; simp [show ¬ 16 ≤ i by omega]
      simp only [fullM, Nat.testBit_lor, hsh, Bool.or_false]
      cases hMi : M.testBit i with
      | false =>
        cases hL : (foldLor (sepM M (2 ^ b :: rest)) U).testBit i with
        | false => rfl
        | true =>
          obtain ⟨w, _, hw⟩ := (foldLor_testBit _ i U).mp hL
          simp only [sepM, Nat.testBit_lor, hsh, Bool.or_false] at hw
          split at hw <;> simp [hMi] at hw
      | true =>
        cases hL : (foldLor (sepM M (2 ^ b :: rest)) U).testBit i with
        | true => rfl
        | false =>
          exfalso
          have hall : ∀ w ∈ U, w.testBit i = true → w.testBit b = true := by
            intro w hwU hwi
            by_contra hwb
            have hwb0 : w.testBit b = false := by cases hwv : w.testBit b <;> simp_all
            have hand0 : (w &&& 2 ^ b == 0) = true := by
              have hne := and_two_pow_ne_zero_iff w b
              rw [hwb0] at hne
              simpa [bne] using hne
            have hbit : (sepM M (2 ^ b :: rest) w).testBit i = true := by
              simp [sepM, hand0, hsh, hwi, hMi]
            have htrue := (foldLor_testBit (sepM M (2 ^ b :: rest)) i U).mpr ⟨w, hwU, hbit⟩
            rw [hL] at htrue; exact Bool.false_ne_true htrue
          have hMb' := agreeM hb16 hc (fun v hv => hall v (List.mem_toFinset.mp hv)) hMi
          rw [hMb] at hMb'; exact Bool.false_ne_true hMb'
    · have hge : 16 ≤ i := by omega
      have hM0 : M.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) hge))
      have hR : (fullM M (2 ^ b :: rest)).testBit i = (fullM M rest).testBit (i - 16) := by
        simp [fullM, hM0, Nat.testBit_shiftLeft, hge]
      rw [hR, ← hrest]
      cases h1 : (foldLor (sepM M rest) U).testBit (i - 16) with
      | true =>
        obtain ⟨w, hwU, hw⟩ := (foldLor_testBit _ (i - 16) U).mp h1
        apply (foldLor_testBit _ i U).mpr
        refine ⟨w, hwU, ?_⟩
        simp [sepM, Nat.testBit_shiftLeft, hge, hw]
      | false =>
        cases h2 : (foldLor (sepM M (2 ^ b :: rest)) U).testBit i with
        | false => rfl
        | true =>
          obtain ⟨w, hwU, hw⟩ := (foldLor_testBit _ i U).mp h2
          simp only [sepM, Nat.testBit_lor, sepM_lt_bit_false M hM (2 ^ b) w i hge, Bool.false_or,
            Nat.testBit_shiftLeft, hge, decide_true, Bool.true_and] at hw
          have ht := (foldLor_testBit _ (i - 16) U).mpr ⟨w, hwU, hw⟩
          rw [h1] at ht; exact absurd ht (by decide)

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
  have _h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
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
          have _h1 : n >>> 16 = n / 65536 := Nat.shiftRight_eq_div_pow n 16
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
  sortU (U.filter (fun x => x != 0 && x != 65535))

def packSet (U : List ℕ) : ℕ := pack (normList U)

theorem normList_bounds {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) : ∀ x ∈ normList U, 0 < x ∧ x < 65536 := by
  intro x hx
  rw [normList, mem_sortU, List.mem_filter] at hx
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
  have hlt := hU x hx.1
  omega

theorem unpack_packSet {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) : unpack (packSet U) = normList U :=
  unpack_pack (normList U) (normList_bounds hU)

theorem freeM_packSet {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    ∀ x ∈ U.toFinset, freeM (unpack (packSet U)).toFinset x := by
  intro x hx
  have hxm := List.mem_toFinset.mp hx
  by_cases h0 : x = 0
  · exact Or.inl h0
  · by_cases h1 : x = 65535
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      rw [unpack_packSet hU, List.mem_toFinset, normList, mem_sortU, List.mem_filter]
      exact ⟨hxm, by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]; exact ⟨h0, h1⟩⟩

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
  (opPairsM S).filter (fun v => v != 0 && v != 65535 && !S.contains v)

theorem opPairsM_lt : ∀ (S : List ℕ), (∀ x ∈ S, x < 65536) → ∀ v ∈ opPairsM S, v < 65536
  | [], _, _, hv => by simp [opPairsM] at hv
  | a :: t, hS, v, hv => by
    simp only [opPairsM, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hv
    have ha := hS a (by simp)
    rcases hv with ⟨b, hb, rfl | rfl⟩ | hv
    · exact Nat.and_lt_two_pow (n := 16) a (hS b (by simp [hb]))
    · exact Nat.or_lt_two_pow (n := 16) ha (hS b (by simp [hb]))
    · exact opPairsM_lt t (fun x hx => hS x (by simp [hx])) v hv

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

theorem combM_case {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) {o : Fin 2} {a b : ℕ}
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b) :
    freeM S.toFinset (combM o a b) ∨ combM o a b ∈ valsNew S := by
  have free_lt {w : ℕ} (hw : freeM S.toFinset w) : w < 65536 := by
    rcases hw with rfl | rfl | h
    · decide
    · decide
    · exact hS w (List.mem_toFinset.mp h)
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
            · simp only [valsNew, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
              refine ⟨hop, ⟨h0, h1⟩, ?_⟩
              cases hc : S.contains (combM o a b) with
              | false => rfl
              | true => exact absurd (List.contains_iff_mem.mp hc) hin

theorem valsNew_props {S : List ℕ} {v : ℕ} (hv : v ∈ valsNew S) :
    v ≠ 0 ∧ v ≠ 65535 ∧ S.contains v = false ∧ v ∉ S := by
  simp only [valsNew, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hv
  have hnotS : v ∉ S := fun hm => by
    rw [List.contains_iff_mem.mpr hm] at hv; exact absurd hv.2.2 (by decide)
  exact ⟨hv.2.1.1, hv.2.1.2, hv.2.2, hnotS⟩

theorem combM_new_other_mem {S : List ℕ} (hS : ∀ w ∈ S, w < 65536) {o : Fin 2} {x z : ℕ}
    (hx : x ∈ S) (hz : freeM S.toFinset z) (hnew : combM o x z ∈ valsNew S) :
    z ∈ S ∧ z ≠ x := by
  obtain ⟨h0, h1, _, hnotS⟩ := valsNew_props hnew
  rcases hz with rfl | rfl | hz'
  · fin_cases o
    · simp only [combM, Nat.and_zero] at h0; exact absurd rfl h0
    · simp only [combM, Nat.or_zero] at hnotS; exact absurd hx hnotS
  · fin_cases o
    · simp only [combM, and_65535_of_lt (hS x hx)] at hnotS; exact absurd hx hnotS
    · simp only [combM, or_65535_of_lt (hS x hx)] at h1; exact absurd rfl h1
  · refine ⟨List.mem_toFinset.mp hz', ?_⟩
    intro heq; subst heq
    fin_cases o
    · simp only [combM, Nat.and_self] at hnotS; exact absurd hx hnotS
    · simp only [combM, Nat.or_self] at hnotS; exact absurd hx hnotS

theorem combM_new_both_mem {S : List ℕ} (hS : ∀ w ∈ S, w < 65536) {o : Fin 2} {a b : ℕ}
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b) (hnew : combM o a b ∈ valsNew S) :
    a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  obtain ⟨h0, h1, _, hnotS⟩ := valsNew_props hnew
  have free_lt {w : ℕ} (hw : freeM S.toFinset w) : w < 65536 := by
    rcases hw with rfl | rfl | h
    · decide
    · decide
    · exact hS w (List.mem_toFinset.mp h)
  rcases ha with rfl | rfl | ha'
  · fin_cases o
    · simp only [combM, Nat.zero_and] at h0; exact absurd rfl h0
    · simp only [combM, Nat.zero_or] at h0 h1 hnotS
      rcases hb with rfl | rfl | hb'
      · exact absurd rfl h0
      · exact absurd rfl h1
      · exact absurd (List.mem_toFinset.mp hb') hnotS
  · fin_cases o
    · simp only [combM, Nat.land_comm 65535, and_65535_of_lt (free_lt hb)] at h0 h1 hnotS
      rcases hb with rfl | rfl | hb'
      · exact absurd rfl h0
      · exact absurd rfl h1
      · exact absurd (List.mem_toFinset.mp hb') hnotS
    · simp only [combM, Nat.lor_comm 65535, or_65535_of_lt (free_lt hb)] at h1; exact absurd rfl h1
  · have haS := List.mem_toFinset.mp ha'
    obtain ⟨hbS, hba⟩ := combM_new_other_mem hS haS hb hnew
    exact ⟨haS, hbS, Ne.symm hba⟩

theorem can1M_case {f : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x < 65536) (hc : CanM f 1 S.toFinset) :
    freeM S.toFinset f ∨ f ∈ valsNew S := by
  obtain ⟨o, a, b, ha, hb, h0⟩ := hc
  rcases h0 with rfl | rfl | hm
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · rcases Finset.mem_insert.mp hm with rfl | hf
    · exact combM_case hS ha hb
    · exact Or.inl (Or.inr (Or.inr hf))

def pairCand (maskParam : ℕ) (bits : List ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  let v1 := a &&& b
  let v2 := a ||| b
  let l2 := if v2 == 65535 || v2 == a || v2 == b then [] else [(v2, sepM maskParam bits v2)]
  if v1 == 0 || v1 == a || v1 == b then l2 else (v1, sepM maskParam bits v1) :: l2

theorem mem_pairCand (maskParam : ℕ) (bits : List ℕ) {S : List ℕ} {o : Fin 2} {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hnew : combM o a b ∈ valsNew S) :
    (combM o a b, sepM maskParam bits (combM o a b)) ∈ pairCand maskParam bits a b := by
  obtain ⟨h0, h1, _, hnotS⟩ := valsNew_props hnew
  have hna : combM o a b ≠ a := fun h => hnotS (by rw [h]; exact ha)
  have hnb : combM o a b ≠ b := fun h => hnotS (by rw [h]; exact hb)
  unfold pairCand
  fin_cases o
  · simp only [combM] at h0 hna hnb ⊢
    have hcond : ((a &&& b) == 0 || (a &&& b) == a || (a &&& b) == b) = false := by
      simp only [beq_false_of_ne h0, beq_false_of_ne hna, beq_false_of_ne hnb, Bool.false_or]
    simp [hcond]
  · simp only [combM] at h1 hna hnb ⊢
    have hcond : ((a ||| b) == 65535 || (a ||| b) == a || (a ||| b) == b) = false := by
      simp only [beq_false_of_ne h1, beq_false_of_ne hna, beq_false_of_ne hnb, Bool.false_or]
    split <;> simp [hcond]

def mkPairMat (maskParam : ℕ) (bits : List ℕ) : List ℕ → List (ℕ × ℕ × List (ℕ × ℕ))
  | [] => []
  | a :: t => t.map (fun b => (a, b, pairCand maskParam bits a b)) ++ mkPairMat maskParam bits t

theorem mkPairMat_val (maskParam : ℕ) (bits : List ℕ) : ∀ (l : List ℕ) (p : ℕ × ℕ × List (ℕ × ℕ)),
    p ∈ mkPairMat maskParam bits l → p.2.2 = pairCand maskParam bits p.1 p.2.1
  | [], _, hp => by simp [mkPairMat] at hp
  | a :: t, p, hp => by
    simp only [mkPairMat, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨b, _, rfl⟩ | hp
    · rfl
    · exact mkPairMat_val maskParam bits t p hp

theorem mkPairMat_spec (maskParam : ℕ) (bits : List ℕ) : ∀ (l : List ℕ), l.Nodup →
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y →
      (x, y, pairCand maskParam bits x y) ∈ mkPairMat maskParam bits l ∨
      (y, x, pairCand maskParam bits y x) ∈ mkPairMat maskParam bits l
  | [], _, _, hx, _, _, _ => by simp at hx
  | a :: t, hnd, x, hx, y, hy, hxy => by
    obtain ⟨_, ht⟩ := List.nodup_cons.mp hnd
    simp only [mkPairMat, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp hx with rfl | hxt <;> rcases List.mem_cons.mp hy with rfl | hyt
    · exact absurd rfl hxy
    · left; left; exact ⟨y, hyt, rfl⟩
    · right; left; exact ⟨x, hxt, rfl⟩
    · rcases mkPairMat_spec maskParam bits t ht x hxt y hyt hxy with h1 | h2
      · left; right; exact h1
      · right; right; exact h2

theorem drop2BAdj_mkPairMat_spec (maskParam : ℕ) (bits : List ℕ) (e : ℕ → Bool) (adj : ℕ → List (ℕ × ℕ)) :
    ∀ (l : List ℕ), l.Nodup → ∀ x ∈ l, ∀ y ∈ l, x ≠ y →
      ((x, e x, adj x, y, e y, adj y, (l.erase x).erase y, foldLor (sepM maskParam bits) ((l.erase x).erase y))
          ∈ drop2BAdj (l.map fun w => (w, sepM maskParam bits w, e w, adj w)) ∧
       (x, y, pairCand maskParam bits x y) ∈ mkPairMat maskParam bits l) ∨
      ((y, e y, adj y, x, e x, adj x, (l.erase y).erase x, foldLor (sepM maskParam bits) ((l.erase y).erase x))
          ∈ drop2BAdj (l.map fun w => (w, sepM maskParam bits w, e w, adj w)) ∧
       (y, x, pairCand maskParam bits y x) ∈ mkPairMat maskParam bits l)
  | [], _, _, hx, _, _, _ => by simp at hx
  | a :: t, hnd, x, hx, y, hy, hxy => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, drop2BAdj, mkPairMat, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp hx with rfl | hxt <;> rcases List.mem_cons.mp hy with rfl | hyt
    · exact absurd rfl hxy
    · left
      refine ⟨Or.inl ⟨(y, e y, adj y, t.erase y, foldLor (sepM maskParam bits) (t.erase y)),
        drop1BAdj_spec (sepM maskParam bits) e adj t ht y hyt, ?_⟩, Or.inl ⟨y, hyt, rfl⟩⟩
      simp [List.erase_cons_head]
    · right
      refine ⟨Or.inl ⟨(x, e x, adj x, t.erase x, foldLor (sepM maskParam bits) (t.erase x)),
        drop1BAdj_spec (sepM maskParam bits) e adj t ht x hxt, ?_⟩, Or.inl ⟨x, hxt, rfl⟩⟩
      simp [List.erase_cons_head]
    · have hax : a ≠ x := fun h => ha (h ▸ hxt)
      have hay : a ≠ y := fun h => ha (h ▸ hyt)
      have hbx : ¬ (a == x) = true := by simp [hax]
      have hby : ¬ (a == y) = true := by simp [hay]
      rcases drop2BAdj_mkPairMat_spec maskParam bits e adj t ht x hxt y hyt hxy with ⟨h1, hm1⟩ | ⟨h2, hm2⟩
      · left
        refine ⟨Or.inr ⟨(x, e x, adj x, y, e y, adj y, (t.erase x).erase y, foldLor (sepM maskParam bits) ((t.erase x).erase y)), h1, ?_⟩, Or.inr hm1⟩
        simp [List.erase_cons_tail hbx, List.erase_cons_tail hby, foldLor_cons]
      · right
        refine ⟨Or.inr ⟨(y, e y, adj y, x, e x, adj x, (t.erase y).erase x, foldLor (sepM maskParam bits) ((t.erase y).erase x)), h2, ?_⟩, Or.inr hm2⟩
        simp [List.erase_cons_tail hby, List.erase_cons_tail hbx, foldLor_cons]

def lookupPair (x y : ℕ) : List (ℕ × ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
  | [] => []
  | (a, b, vs) :: rest => if a == x && b == y then vs else lookupPair x y rest

theorem lookupPair_eq {x y : ℕ} {vs : List (ℕ × ℕ)} :
    ∀ (pm : List (ℕ × ℕ × List (ℕ × ℕ))),
      (∀ p ∈ pm, p.1 = x ∧ p.2.1 = y → p.2.2 = vs) →
      (x, y, vs) ∈ pm → lookupPair x y pm = vs
  | [], _, hm => by simp at hm
  | (a, b, vs0) :: rest, hall, hm => by
    unfold lookupPair
    by_cases hcond : (a == x && b == y) = true
    · simp only [hcond, ↓reduceIte]
      have hp := Bool.and_eq_true _ _ |>.mp hcond
      exact hall (a, b, vs0) (by simp) ⟨beq_iff_eq.mp hp.1, beq_iff_eq.mp hp.2⟩
    · simp only [hcond, ↓reduceIte]
      rcases List.mem_cons.mp hm with heq | hm
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        simp at hcond
      · exact lookupPair_eq rest (fun p hp => hall p (by simp [hp])) hm

def adjOf (x : ℕ) : List (ℕ × ℕ × List (ℕ × ℕ)) → List (ℕ × ℕ)
  | [] => []
  | (a, b, vs) :: rest =>
    if a == x || b == x then vs ++ adjOf x rest else adjOf x rest

theorem mem_adjOf {x a b : ℕ} {vs : List (ℕ × ℕ)} {q : ℕ × ℕ} :
    ∀ (pm : List (ℕ × ℕ × List (ℕ × ℕ))),
      (a, b, vs) ∈ pm → (a = x ∨ b = x) → q ∈ vs → q ∈ adjOf x pm
  | [], hm, _, _ => by simp at hm
  | (a0, b0, vs0) :: rest, hm, hab, hq => by
    unfold adjOf
    rcases List.mem_cons.mp hm with heq | hm
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      have hcond : (a == x || b == x) = true := by
        rcases hab with rfl | rfl <;> simp
      simp only [hcond, ↓reduceIte, List.mem_append]
      exact Or.inl hq
    · split
      · exact List.mem_append_right _ (mem_adjOf rest hm hab hq)
      · exact mem_adjOf rest hm hab hq

theorem ess_forces_input {f k : ℕ} {bits S U' : List ℕ} {o : Fin 2} {a b x : ℕ}
    (hM : f < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ f.testBit b = false)
    (hess : (foldLor (sepM f bits) (S.erase x) != fullM f bits) = true)
    (hU' : ∀ z ∈ U', z ∈ S.erase x)
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b)
    (hcU : CanM f k (combM o a b :: U').toFinset) :
    a = x ∨ b = x := by
  by_contra hne
  have hax : a ≠ x := fun h => hne (Or.inl h)
  have hbx : b ≠ x := fun h => hne (Or.inr h)
  have lift : ∀ {w : ℕ}, w ≠ x → freeM S.toFinset w → freeM (S.erase x).toFinset w := by
    intro w hwx hw
    rcases hw with rfl | rfl | hw
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (List.mem_toFinset.mpr ((List.mem_erase_of_ne hwx).mpr (List.mem_toFinset.mp hw))))
  have hsub : (combM o a b :: U').toFinset ⊆ insert (combM o a b) (S.erase x).toFinset := by
    intro z hz
    rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hU' z hz))
  have hc1 : CanM f (k + 1) (S.erase x).toFinset := ⟨o, a, b, lift hax ha, lift hbx hb, monoCM hsub hcU⟩
  exact bne_iff_ne.mp hess (coveredM_sepM hM hc1 bits hbits)

def PermOk (g : ℕ → ℕ) : Prop :=
  g 0 = 0 ∧ g 65535 = 65535 ∧ (∀ w, w < 65536 → g w < 65536) ∧ (∀ o a b, g (combM o a b) = combM o (g a) (g b))

theorem PermOk_id : PermOk id := ⟨rfl, rfl, fun _ h => h, fun _ _ _ => rfl⟩

theorem PermOk_comp {g1 g2 : ℕ → ℕ} (h1 : PermOk g1) (h2 : PermOk g2) : PermOk (fun w => g1 (g2 w)) :=
  ⟨by dsimp only; rw [h2.1, h1.1], by dsimp only; rw [h2.2.1, h1.2.1],
   fun w hw => h1.2.2.1 _ (h2.2.2.1 w hw),
   fun o a b => by dsimp only; rw [h2.2.2.2, h1.2.2.2]⟩

def transp16 (w : ℕ) : ℕ :=
  let t := (w &&& 0xcc33) ||| ((w &&& 0x00cc) <<< 6) ||| ((w &&& 0x3300) >>> 6)
  (t &&& 0xa5a5) ||| ((t &&& 0x0a0a) <<< 3) ||| ((t &&& 0x5050) >>> 3)

def rowPerm16 (r0 r1 r2 r3 w : ℕ) : ℕ :=
  ((w >>> r0) &&& 15) ||| (((w >>> r1) &&& 15) <<< 4) |||
  (((w >>> r2) &&& 15) <<< 8) ||| (((w >>> r3) &&& 15) <<< 12)

def colPerm16 (c0 c1 c2 c3 w : ℕ) : ℕ :=
  ((w >>> c0) &&& 0x1111) ||| (((w >>> c1) &&& 0x1111) <<< 1) |||
  (((w >>> c2) &&& 0x1111) <<< 2) ||| (((w >>> c3) &&& 0x1111) <<< 3)

theorem testBit_mask_ge16 (m i : ℕ) (hm : m < 2 ^ 16) (hi : 16 ≤ i) : m.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))

theorem perm_ok_of_testBit (g : ℕ → ℕ) (idx : ℕ → ℕ)
    (hidx : ∀ i < 16, idx i < 16)
    (htb : ∀ w i, (g w).testBit i = if i < 16 then w.testBit (idx i) else false) : PermOk g := by
  have h6 : ∀ j < 16, (65535 : ℕ).testBit j = true := fun j hj =>
    (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) ⟨j, hj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq; intro i; simp [htb]
  · apply Nat.eq_of_testBit_eq; intro i
    rw [htb]
    by_cases hi : i < 16
    · simp [hi, h6 _ (hidx i hi), h6 _ hi]
    · simp only [hi, ↓reduceIte]
      symm; exact testBit_mask_ge16 _ _ (by decide) (by omega)
  · intro w _
    have hlt : g w < 2 ^ 16 := by
      have heq : g w &&& (2 ^ 16 - 1) = g w := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_land, htb]
        by_cases hi : i < 16
        · simp [hi, h6 i hi]
        · simp [hi]
      rw [← heq, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    exact hlt
  · intro o a b
    apply Nat.eq_of_testBit_eq; intro i
    fin_cases o <;> simp only [combM, Nat.testBit_land, Nat.testBit_lor, htb] <;> split <;> simp

theorem transp16_testBit (w i : ℕ) :
    (transp16 w).testBit i = if i < 16 then w.testBit (4 * (i % 4) + i / 4) else false := by
  have h1 : ∀ k < 26, (0xcc33 : ℕ).testBit k = decide (k ∈ [0,1,4,5,10,11,14,15]) := fun k hk =>
    (show ∀ q : Fin 26, (0xcc33 : ℕ).testBit q.val = decide (q.val ∈ [0,1,4,5,10,11,14,15]) by decide) ⟨k, hk⟩
  have h2 : ∀ k < 26, (0x00cc : ℕ).testBit k = decide (k ∈ [2,3,6,7]) := fun k hk =>
    (show ∀ q : Fin 26, (0x00cc : ℕ).testBit q.val = decide (q.val ∈ [2,3,6,7]) by decide) ⟨k, hk⟩
  have h3 : ∀ k < 26, (0x3300 : ℕ).testBit k = decide (k ∈ [8,9,12,13]) := fun k hk =>
    (show ∀ q : Fin 26, (0x3300 : ℕ).testBit q.val = decide (q.val ∈ [8,9,12,13]) by decide) ⟨k, hk⟩
  have h4 : ∀ k < 26, (0xa5a5 : ℕ).testBit k = decide (k ∈ [0,2,5,7,8,10,13,15]) := fun k hk =>
    (show ∀ q : Fin 26, (0xa5a5 : ℕ).testBit q.val = decide (q.val ∈ [0,2,5,7,8,10,13,15]) by decide) ⟨k, hk⟩
  have h5 : ∀ k < 26, (0x0a0a : ℕ).testBit k = decide (k ∈ [1,3,9,11]) := fun k hk =>
    (show ∀ q : Fin 26, (0x0a0a : ℕ).testBit q.val = decide (q.val ∈ [1,3,9,11]) by decide) ⟨k, hk⟩
  have h6 : ∀ k < 26, (0x5050 : ℕ).testBit k = decide (k ∈ [4,6,12,14]) := fun k hk =>
    (show ∀ q : Fin 26, (0x5050 : ℕ).testBit q.val = decide (q.val ∈ [4,6,12,14]) by decide) ⟨k, hk⟩
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    interval_cases i <;>
      simp [transp16, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h1, h2, h3, h4, h5, h6]
  · simp only [hi, ↓reduceIte]
    have hge : 16 ≤ i := by omega
    have ha : (0xa5a5 : ℕ).testBit i = false := testBit_mask_ge16 _ _ (by decide) hge
    have hb : (0x0a0a : ℕ).testBit (i - 3) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x0a0a < 2 ^ 12) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hc : (0x5050 : ℕ).testBit (3 + i) = false := testBit_mask_ge16 _ _ (by decide) (by omega)
    simp [transp16, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ha, hb, hc]

theorem transp16_ok : PermOk transp16 :=
  perm_ok_of_testBit transp16 (fun i => 4 * (i % 4) + i / 4) (fun i hi => by omega) transp16_testBit

theorem rowPerm16_testBit (r0 r1 r2 r3 w i : ℕ) :
    (rowPerm16 r0 r1 r2 r3 w).testBit i =
      if i < 16 then
        w.testBit ((if i < 4 then r0 else if i < 8 then r1 else if i < 12 then r2 else r3) + i % 4)
      else false := by
  have h15 : ∀ k < 16, (15 : ℕ).testBit k = decide (k < 4) := fun k hk =>
    (show ∀ q : Fin 16, (15 : ℕ).testBit q.val = decide (q.val < 4) by decide) ⟨k, hk⟩
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    interval_cases i <;>
      simp [rowPerm16, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h15]
  · simp only [hi, ↓reduceIte]
    have hf : ∀ k : ℕ, k ≤ 12 → (15 : ℕ).testBit (i - k) = false := fun k hk =>
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 15 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hf0 : (15 : ℕ).testBit i = false := by simpa using hf 0 (by decide)
    simp [rowPerm16, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      hf0, hf 4 (by decide), hf 8 (by decide), hf 12 (by decide)]

theorem rowPerm16_ok (r0 r1 r2 r3 : ℕ) (h0 : r0 ≤ 12) (h1 : r1 ≤ 12) (h2 : r2 ≤ 12) (h3 : r3 ≤ 12) :
    PermOk (rowPerm16 r0 r1 r2 r3) :=
  perm_ok_of_testBit _ _ (fun i hi => by split_ifs <;> omega) (rowPerm16_testBit r0 r1 r2 r3)

theorem colPerm16_testBit (c0 c1 c2 c3 w i : ℕ) :
    (colPerm16 c0 c1 c2 c3 w).testBit i =
      if i < 16 then
        w.testBit (4 * (i / 4) + if i % 4 = 0 then c0 else if i % 4 = 1 then c1 else if i % 4 = 2 then c2 else c3)
      else false := by
  have h11 : ∀ k < 16, (0x1111 : ℕ).testBit k = decide (k % 4 = 0) := fun k hk =>
    (show ∀ q : Fin 16, (0x1111 : ℕ).testBit q.val = decide (q.val % 4 = 0) by decide) ⟨k, hk⟩
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    interval_cases i <;>
      simp [colPerm16, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h11, Nat.add_comm]
  · simp only [hi, ↓reduceIte]
    have hf : ∀ k : ℕ, k ≤ 3 → (0x1111 : ℕ).testBit (i - k) = false := fun k hk =>
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x1111 < 2 ^ 13) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hf0 : (0x1111 : ℕ).testBit i = false := by simpa using hf 0 (by decide)
    simp [colPerm16, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      hf0, hf 1 (by decide), hf 2 (by decide), hf 3 (by decide)]

theorem colPerm16_ok (c0 c1 c2 c3 : ℕ) (h0 : c0 < 4) (h1 : c1 < 4) (h2 : c2 < 4) (h3 : c3 < 4) :
    PermOk (colPerm16 c0 c1 c2 c3) :=
  perm_ok_of_testBit _ _ (fun i hi => by split_ifs <;> omega) (colPerm16_testBit c0 c1 c2 c3)

theorem canM_permOk {g : ℕ → ℕ} (hg : PermOk g) {f k : ℕ} {S : Finset ℕ}
    (hc : CanM f k S) : CanM (g f) k (S.image g) := by
  have hfree {T : Finset ℕ} {v : ℕ} (hv : freeM T v) : freeM (T.image g) (g v) := by
    rcases hv with rfl | rfl | h
    · exact Or.inl hg.1
    · exact Or.inr (Or.inl hg.2.1)
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
  induction k generalizing S with
  | zero => exact hfree hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, g a, g b, hfree ha, hfree hb, ?_⟩
    have h' := ih hh
    rw [Finset.image_insert, hg.2.2.2] at h'
    exact h'

def permAut : ℕ → ℕ → ℕ
  | 0, w => w
  | 1, w => colPerm16 0 2 1 3 w
  | _, w => w

theorem permAut_ok : ∀ idx, PermOk (permAut idx)
  | 0 => PermOk_id
  | 1 => by change PermOk (fun w => colPerm16 0 2 1 3 w); exact colPerm16_ok 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
  | _ + 2 => PermOk_id

theorem permAut_fix : ∀ idx, permAut idx targetNat = targetNat
  | 0 => rfl
  | 1 => by decide +kernel
  | _ + 2 => rfl

def stepUHint (nextTree : BinaryTree (ℕ × ℕ)) (U : List ℕ) (h : ℕ) : Option ℕ :=
  let idx := h &&& 1
  let ok := if idx == 0 then treeMem (packSet U) nextTree
            else treeMem (packSet (U.map (permAut idx))) nextTree
  if ok then some (h >>> 1) else none

theorem stepUHint_sound {k : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {U : List ℕ} {a b : ℕ}
    (hU : ∀ x ∈ U, x < 65536)
    (hs : stepUHint nextTree U a = some b)
    (hc : CanM targetNat k U.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM targetNat k (unpack x).toFinset := by
  unfold stepUHint at hs
  dsimp only at hs
  by_cases h0 : (a &&& 1) == 0
  · simp only [h0, ↓reduceIte] at hs
    cases hm : treeMem (packSet U) nextTree with
    | false => simp [hm] at hs
    | true => exact ⟨packSet U, treeMem_imp nextTree hm, monoCM_free (freeM_packSet hU) hc⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hs
    set idx := a &&& 1
    have hok := permAut_ok idx
    have hfix := permAut_fix idx
    cases hm : treeMem (packSet (U.map (permAut idx))) nextTree with
    | false => simp [hm] at hs
    | true =>
      have hcp : CanM targetNat k (U.map (permAut idx)).toFinset := by
        have h1 := canM_permOk hok hc
        have heq : (U.map (permAut idx)).toFinset = U.toFinset.image (permAut idx) := by ext y; simp
        rw [hfix, ← heq] at h1
        exact h1
      have hUp : ∀ y ∈ U.map (permAut idx), y < 65536 := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact hok.2.2.1 x (hU x hx)
      exact ⟨packSet (U.map (permAut idx)), treeMem_imp nextTree hm, monoCM_free (freeM_packSet hUp) hcp⟩

def checkCutsM (fullVal : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) : List (List ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (U, mU) :: rest, h =>
    if mU == fullVal then
      match stepUHint nextTree U h with
      | none => none
      | some h' => checkCutsM fullVal nextTree rest h'
    else checkCutsM fullVal nextTree rest h

theorem checkCutsM_sound {fullVal : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} :
    ∀ (cs : List (List ℕ × ℕ)) (h h' : ℕ), checkCutsM fullVal nextTree cs h = some h' →
      ∀ p ∈ cs, p.2 = fullVal → ∃ a b, stepUHint nextTree p.1 a = some b
  | [], _, _, _, _, hp, _ => by simp at hp
  | (U, mU) :: rest, h, h', hall, p, hp, hpeq => by
    unfold checkCutsM at hall
    by_cases hm : mU == fullVal
    · simp only [hm, ↓reduceIte] at hall
      cases hs : stepUHint nextTree U h with
      | none => simp [hs] at hall
      | some h1 =>
        simp only [hs] at hall
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨h, h1, hs⟩
        · exact checkCutsM_sound rest h1 h' hall p hp hpeq
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hall
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd (beq_iff_eq.mpr hpeq) hm
      · exact checkCutsM_sound rest h h' hall p hp hpeq

def checkDrop1 (fullVal : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) : List (ℕ × ℕ × List ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (_, _, U, mU) :: rest, h =>
    if mU == fullVal then
      match stepUHint nextTree U h with
      | none => none
      | some h' => checkDrop1 fullVal nextTree rest h'
    else checkDrop1 fullVal nextTree rest h

theorem checkDrop1_sound {fullVal : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} :
    ∀ (ds : List (ℕ × ℕ × List ℕ × ℕ)) (h h' : ℕ), checkDrop1 fullVal nextTree ds h = some h' →
      ∀ p ∈ ds, p.2.2.2 = fullVal → ∃ a b, stepUHint nextTree p.2.2.1 a = some b
  | [], _, _, _, _, hp, _ => by simp at hp
  | (x, mx, U, mU) :: rest, h, h', hall, p, hp, hpeq => by
    unfold checkDrop1 at hall
    by_cases hm : mU == fullVal
    · simp only [hm, ↓reduceIte] at hall
      cases hs : stepUHint nextTree U h with
      | none => simp [hs] at hall
      | some h1 =>
        simp only [hs] at hall
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨h, h1, hs⟩
        · exact checkDrop1_sound rest h1 h' hall p hp hpeq
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hall
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd (beq_iff_eq.mpr hpeq) hm
      · exact checkDrop1_sound rest h h' hall p hp hpeq

def scanVsM (fullVal : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (U' : List ℕ) (mU : ℕ) :
    List (ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (v, mv) :: rest, h =>
    if (mU ||| mv) == fullVal then
      match stepUHint nextTree (v :: U') h with
      | none => none
      | some h' => scanVsM fullVal nextTree U' mU rest h'
    else scanVsM fullVal nextTree U' mU rest h

theorem scanVsM_sound {fullVal : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {U' : List ℕ} {mU : ℕ} :
    ∀ (vs : List (ℕ × ℕ)) (h h' : ℕ), scanVsM fullVal nextTree U' mU vs h = some h' →
      ∀ q ∈ vs, (mU ||| q.2) = fullVal → ∃ a b, stepUHint nextTree (q.1 :: U') a = some b
  | [], _, _, _, _, hq, _ => by simp at hq
  | (v, mv) :: rest, h, h', hall, q, hq, hqeq => by
    unfold scanVsM at hall
    by_cases hm : (mU ||| mv) == fullVal
    · simp only [hm, ↓reduceIte] at hall
      cases hs : stepUHint nextTree (v :: U') h with
      | none => simp [hs] at hall
      | some h1 =>
        simp only [hs] at hall
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨h, h1, hs⟩
        · exact scanVsM_sound rest h1 h' hall q hq hqeq
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hall
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd (beq_iff_eq.mpr hqeq) hm
      · exact scanVsM_sound rest h h' hall q hq hqeq

def scanCutsM (fullVal : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (vsM : List (ℕ × ℕ)) :
    List (List ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (U', mU) :: rest, h =>
    match scanVsM fullVal nextTree U' mU vsM h with
    | none => none
    | some h' => scanCutsM fullVal nextTree vsM rest h'

theorem scanCutsM_sound {fullVal : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {vsM : List (ℕ × ℕ)} :
    ∀ (cs : List (List ℕ × ℕ)) (h h' : ℕ), scanCutsM fullVal nextTree vsM cs h = some h' →
      ∀ p ∈ cs, ∃ a b, scanVsM fullVal nextTree p.1 p.2 vsM a = some b
  | [], _, _, _, _, hp => by simp at hp
  | (U', mU) :: rest, h, h', hall, p, hp => by
    unfold scanCutsM at hall
    cases hs : scanVsM fullVal nextTree U' mU vsM h with
    | none => simp [hs] at hall
    | some h1 =>
      simp only [hs] at hall
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨h, h1, hs⟩
      · exact scanCutsM_sound rest h1 h' hall p hp

def scanAllEss (maskParam fullVal : ℕ) (bits : List ℕ) (nextTree : BinaryTree (ℕ × ℕ)) :
    List (ℕ × ℕ × List ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (x, y, U', mU) :: rest, h =>
    match scanVsM fullVal nextTree U' mU (pairCand maskParam bits x y) h with
    | none => none
    | some h' => scanAllEss maskParam fullVal bits nextTree rest h'

theorem scanAllEss_sound {maskParam fullVal : ℕ} {bits : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} :
    ∀ (ps : List (ℕ × ℕ × List ℕ × ℕ)) (h h' : ℕ),
      scanAllEss maskParam fullVal bits nextTree ps h = some h' →
      ∀ (x y : ℕ) (U' : List ℕ) (mU : ℕ), (x, y, U', mU) ∈ ps →
        ∃ a b, scanVsM fullVal nextTree U' mU (pairCand maskParam bits x y) a = some b
  | [], _, _, _, _, _, _, _, hp => by simp at hp
  | (x0, y0, U0, mU0) :: rest, h, h', hall, x, y, U', mU, hp => by
    unfold scanAllEss at hall
    cases hs : scanVsM fullVal nextTree U0 mU0 (pairCand maskParam bits x0 y0) h with
    | none => simp [hs] at hall
    | some h1 =>
      simp only [hs] at hall
      rcases List.mem_cons.mp hp with heq | hp
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨h, h1, hs⟩
      · exact scanAllEss_sound rest h1 h' hall x y U' mU hp

def scanPairsPre (fullVal : ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (pm : List (ℕ × ℕ × List (ℕ × ℕ))) (vsM : List (ℕ × ℕ)) :
    List (ℕ × Bool × List (ℕ × ℕ) × ℕ × Bool × List (ℕ × ℕ) × List ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (x, ex, ax, y, ey, ay, U', mU) :: rest, h =>
    let vs := if ex && ey then lookupPair x y pm
              else if ex then ax
              else if ey then ay
              else vsM
    match scanVsM fullVal nextTree U' mU vs h with
    | none => none
    | some h' => scanPairsPre fullVal nextTree pm vsM rest h'

theorem scanPairsPre_sound {fullVal : ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {pm : List (ℕ × ℕ × List (ℕ × ℕ))} {vsM : List (ℕ × ℕ)} :
    ∀ (ps : List (ℕ × Bool × List (ℕ × ℕ) × ℕ × Bool × List (ℕ × ℕ) × List ℕ × ℕ)) (h h' : ℕ),
      scanPairsPre fullVal nextTree pm vsM ps h = some h' →
      ∀ (x y : ℕ) (ex ey : Bool) (ax ay : List (ℕ × ℕ)) (U' : List ℕ) (mU : ℕ),
        (x, ex, ax, y, ey, ay, U', mU) ∈ ps →
        ∃ a b, scanVsM fullVal nextTree U' mU
          (if ex && ey then lookupPair x y pm else if ex then ax else if ey then ay else vsM) a = some b
  | [], _, _, _, _, _, _, _, _, _, _, _, hp => by simp at hp
  | (x0, ex0, ax0, y0, ey0, ay0, U0, mU0) :: rest, h, h', hall, x, y, ex, ey, ax, ay, U', mU, hp => by
    unfold scanPairsPre at hall
    dsimp only at hall
    cases hs : scanVsM fullVal nextTree U0 mU0
        (if ex0 && ey0 then lookupPair x0 y0 pm else if ex0 then ax0 else if ey0 then ay0 else vsM) h with
    | none => rw [hs] at hall; simp at hall
    | some h1 =>
      rw [hs] at hall
      dsimp only at hall
      rcases List.mem_cons.mp hp with heq | hp
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact ⟨h, h1, hs⟩
      · exact scanPairsPre_sound rest h1 h' hall x y ex ey ax ay U' mU hp

def verifyNode (maskParam fullVal k : ℕ) (bits : List ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (packedS h : ℕ) : Bool :=
  let S := unpack packedS
  let SM := S.map (fun w => (w, sepM maskParam bits w))
  if isStrict S && (S.length == k + 2) then
    let d1 := drop1M SM
    match checkDrop1 fullVal nextTree d1 h with
    | none => false
    | some h1 =>
      let tagged := d1.map (fun p => (p.1, p.2.1, p.2.2.2 != fullVal))
      let nonEss := countNonEss tagged
      if nonEss == 0 then
        (scanAllEss maskParam fullVal bits nextTree (drop2Only SM) h1).isSome
      else
        let pm := mkPairMat maskParam bits S
        let taggedA := tagged.map (fun p => (p.1, p.2.1, p.2.2, if p.2.2 then adjOf p.1 pm else []))
        let vsM := if 2 ≤ nonEss then (pm.flatMap fun p => p.2.2).filter (fun q => !S.contains q.1) else []
        (scanPairsPre fullVal nextTree pm vsM (drop2BAdj taggedA) h1).isSome
  else
    match checkCutsM fullVal nextTree (cutsM (k + 1) SM) h with
    | none => false
    | some h1 =>
      let vsM := (valsNew S).map (fun v => (v, sepM maskParam bits v))
      (scanCutsM fullVal nextTree vsM (cutsM k SM) h1).isSome

theorem checkCutsInit_sound {k : ℕ} {bits : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {l : List ℕ} {h h' : ℕ}
    (hl : ∀ x ∈ l, x < 65536)
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hchk : checkCutsM (fullM targetNat bits) nextTree (cutsM (k + 1) (l.map fun w => (w, sepM targetNat bits w))) h = some h')
    (hc : CanM targetNat k l.toFinset) :
    ∃ x, InTree x nextTree ∧ CanM targetNat k (unpack x).toFinset := by
  obtain ⟨T, hT, hn, ht⟩ := smallM hc
  obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) l T hT hn
  have hcU := monoCM hu ht
  have hmem := cutsM_spec (sepM targetNat bits) l (k + 1) U hU
  have hcov := coveredM_sepM hM hcU bits hbits
  obtain ⟨a, b, hs⟩ := checkCutsM_sound _ h h' hchk (U, foldLor (sepM targetNat bits) U) hmem hcov
  have hU_lt : ∀ x ∈ U, x < 65536 := fun x hx => hl x (cuts_mem_sub l (k + 1) U hU x hx)
  exact stepUHint_sound hU_lt hs hcU

theorem advanceNode {k : ℕ} {bits : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {packedS h : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hv : verifyNode targetNat (fullM targetNat bits) k bits nextTree packedS h = true)
    (hc : CanM targetNat (k + 1) (unpack packedS).toFinset) :
    ∃ x, InTree x nextTree ∧ CanM targetNat k (unpack x).toFinset := by
  unfold verifyNode at hv
  dsimp only at hv
  set S := unpack packedS with hS_def
  have hS_lt : ∀ x ∈ S, x < 65536 := unpack_lt packedS
  by_cases hfast : (isStrict S && (S.length == k + 2)) = true
  · simp only [hfast, ↓reduceIte] at hv
    have hfp := Bool.and_eq_true _ _ |>.mp hfast
    have hnd : S.Nodup := isStrict_nodup S hfp.1
    have hlen : S.length = k + 2 := beq_iff_eq.mp hfp.2
    cases hd1 : checkDrop1 (fullM targetNat bits) nextTree (drop1M (S.map fun w => (w, sepM targetNat bits w))) h with
    | none => simp [hd1] at hv
    | some h1 =>
      simp only [hd1] at hv
      have hdrop1_finish : ∀ {T : Finset ℕ}, T ⊆ S.toFinset → T.card ≤ k + 1 → CanM targetNat k T →
          ∃ x, InTree x nextTree ∧ CanM targetNat k (unpack x).toFinset := by
        intro T hTS hTcard hTk
        have hScard : S.toFinset.card = k + 2 := by rw [List.toFinset_card_of_nodup hnd, hlen]
        have hsum : (S.toFinset \ T).card + T.card = S.toFinset.card := by
          rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hTS]
        obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < (S.toFinset \ T).card)
        have hx0S : x0 ∈ S := List.mem_toFinset.mp (Finset.mem_sdiff.mp hx0).1
        have hx0T : x0 ∉ T := (Finset.mem_sdiff.mp hx0).2
        have hTsub : T ⊆ (S.erase x0).toFinset := by
          intro z hz
          have hzS : z ∈ S := List.mem_toFinset.mp (hTS hz)
          have hzx : z ≠ x0 := fun he => hx0T (he ▸ hz)
          exact List.mem_toFinset.mpr ((mem_erase_of_nodup hnd).mpr ⟨hzS, hzx⟩)
        have hcU := monoCM hTsub hTk
        have hcov := coveredM_sepM hM hcU bits hbits
        have hmem := drop1M_spec (sepM targetNat bits) S hnd x0 hx0S
        obtain ⟨a, b, hs⟩ := checkDrop1_sound _ h h1 hd1 _ hmem hcov
        have hUlt : ∀ z ∈ S.erase x0, z < 65536 := fun z hz => hS_lt z (List.mem_of_mem_erase hz)
        exact stepUHint_sound hUlt hs hcU
      obtain ⟨o, a, b, ha, hb, hh⟩ := hc
      rcases combM_case hS_lt ha hb with hfree | hnew
      · have hh' : CanM targetNat k S.toFinset := by
          refine monoCM_free (fun z hz => ?_) hh
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hfree
          · exact Or.inr (Or.inr hz)
        obtain ⟨T, hT, hn, ht⟩ := smallM hh'
        exact hdrop1_finish hT hn ht
      · obtain ⟨T, hT, hn, ht⟩ := smallM hh
        by_cases hvT : combM o a b ∈ T
        · have hTe : T.erase (combM o a b) ⊆ S.toFinset := by
            intro z hz
            exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hz))).resolve_left (Finset.ne_of_mem_erase hz)
          have hcard : (T.erase (combM o a b)).card ≤ k := by
            rw [Finset.card_erase_of_mem hvT]; omega
          set T' := T.erase (combM o a b)
          have hScard : S.toFinset.card = k + 2 := by rw [List.toFinset_card_of_nodup hnd, hlen]
          have hsum : (S.toFinset \ T').card + T'.card = S.toFinset.card := by
            rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hTe]
          obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < (S.toFinset \ T').card)
          have hD2pos : 0 < ((S.toFinset \ T').erase x0).card := by
            rw [Finset.card_erase_of_mem hx0]; omega
          obtain ⟨y0, hy0⟩ := Finset.card_pos.mp hD2pos
          have hyx : y0 ≠ x0 := Finset.ne_of_mem_erase hy0
          have hy0D : y0 ∈ S.toFinset \ T' := Finset.mem_of_mem_erase hy0
          have hx0S : x0 ∈ S := List.mem_toFinset.mp (Finset.mem_sdiff.mp hx0).1
          have hx0T : x0 ∉ T' := (Finset.mem_sdiff.mp hx0).2
          have hy0S : y0 ∈ S := List.mem_toFinset.mp (Finset.mem_sdiff.mp hy0D).1
          have hy0T : y0 ∉ T' := (Finset.mem_sdiff.mp hy0D).2
          set efn : ℕ → Bool := fun w => foldLor (sepM targetNat bits) (S.erase w) != fullM targetNat bits
          have htag : (drop1M (S.map fun w => (w, sepM targetNat bits w))).map (fun p => (p.1, p.2.1, p.2.2.2 != fullM targetNat bits))
              = S.map (fun w => (w, sepM targetNat bits w, efn w)) := drop1M_tagged (sepM targetNat bits) (fullM targetNat bits) S hnd
          rw [htag] at hv
          have hv_lt : combM o a b < 65536 := by
            simp only [valsNew, List.mem_filter] at hnew
            exact opPairsM_lt S hS_lt _ hnew.1
          by_cases hne0 : (countNonEss (S.map fun w => (w, sepM targetNat bits w, efn w)) == 0) = true
          · simp only [hne0, ↓reduceIte, Option.isSome_iff_exists] at hv
            obtain ⟨h2, hall2⟩ := hv
            have halle := countNonEss_eq_zero (sepM targetNat bits) efn S (beq_iff_eq.mp hne0)
            have handle_all : ∀ (p q : ℕ), p ∈ S → q ∈ S → p ≠ q → p ∉ T' → q ∉ T' →
                (p, q, (S.erase p).erase q, foldLor (sepM targetNat bits) ((S.erase p).erase q))
                  ∈ drop2Only (S.map fun w => (w, sepM targetNat bits w)) →
                ∃ x, InTree x nextTree ∧ CanM targetNat k (unpack x).toFinset := by
              intro p q hpS hqS hpq hpT hqT hpmem
              set U' := (S.erase p).erase q
              have hndp : (S.erase p).Nodup := hnd.erase p
              have hU'mem : ∀ z, z ∈ U' ↔ z ∈ S ∧ z ≠ p ∧ z ≠ q := by
                intro z; rw [mem_erase_of_nodup hndp, mem_erase_of_nodup hnd]; tauto
              have hU'p : ∀ z ∈ U', z ∈ S.erase p := fun z hz => List.mem_of_mem_erase hz
              have hU'q : ∀ z ∈ U', z ∈ S.erase q := fun z hz =>
                (mem_erase_of_nodup hnd).mpr ⟨((hU'mem z).mp hz).1, ((hU'mem z).mp hz).2.2⟩
              have hsubT : T ⊆ (combM o a b :: U').toFinset := by
                intro z hz
                by_cases ez : z = combM o a b
                · simp [ez]
                · have hzT' : z ∈ T' := Finset.mem_erase.mpr ⟨ez, hz⟩
                  exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((hU'mem z).mpr ⟨List.mem_toFinset.mp (hTe hzT'), fun h => hpT (h ▸ hzT'), fun h => hqT (h ▸ hzT')⟩))
              have hcU := monoCM hsubT ht
              have hcov : foldLor (sepM targetNat bits) U' ||| sepM targetNat bits (combM o a b) = fullM targetNat bits := by
                rw [Nat.lor_comm, ← foldLor_cons]; exact coveredM_sepM hM hcU bits hbits
              have hU_lt : ∀ z ∈ combM o a b :: U', z < 65536 := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hv_lt
                · exact hS_lt z ((hU'mem z).mp hz).1
              have hpab := ess_forces_input hM hbits (halle p hpS) hU'p ha hb hcU
              have hqab := ess_forces_input hM hbits (halle q hqS) hU'q ha hb hcU
              have hce : combM o a b = combM o p q := by
                rcases hpab with hap | hbp <;> rcases hqab with haq | hbq
                · exact absurd (hap.symm.trans haq) hpq
                · rw [hap, hbq]
                · rw [hbp, haq, combM_comm]
                · exact absurd (hbp.symm.trans hbq) hpq
              have hnew' : combM o p q ∈ valsNew S := by rw [← hce]; exact hnew
              have hpc : (combM o a b, sepM targetNat bits (combM o a b)) ∈ pairCand targetNat bits p q := by
                rw [hce]; exact mem_pairCand targetNat bits hpS hqS hnew'
              obtain ⟨a1, b1, hsc⟩ := scanAllEss_sound _ h1 h2 hall2 p q U' (foldLor (sepM targetNat bits) U') hpmem
              obtain ⟨a2, b2, hst⟩ := scanVsM_sound _ a1 b1 hsc _ hpc hcov
              exact stepUHint_sound hU_lt hst hcU
            rcases drop2Only_spec (sepM targetNat bits) S hnd x0 hx0S y0 hy0S (Ne.symm hyx) with h1' | h2'
            · exact handle_all x0 y0 hx0S hy0S (Ne.symm hyx) hx0T hy0T h1'
            · exact handle_all y0 x0 hy0S hx0S hyx hy0T hx0T h2'
          · simp only [if_neg hne0, Option.isSome_iff_exists] at hv
            obtain ⟨h2, hall2⟩ := hv
            set pm := mkPairMat targetNat bits S
            set adj : ℕ → List (ℕ × ℕ) := fun w => if efn w then adjOf w pm else []
            have hmapA : (S.map fun w => (w, sepM targetNat bits w, efn w)).map
                (fun p => (p.1, p.2.1, p.2.2, if p.2.2 then adjOf p.1 pm else [])) =
                S.map (fun w => (w, sepM targetNat bits w, efn w, adj w)) := by
              simp [List.map_map, adj, Function.comp_def]
            rw [hmapA] at hall2
            have handle_pair : ∀ (p q : ℕ), p ∈ S → q ∈ S → p ≠ q → p ∉ T' → q ∉ T' →
                (p, efn p, adj p, q, efn q, adj q, (S.erase p).erase q, foldLor (sepM targetNat bits) ((S.erase p).erase q))
                  ∈ drop2BAdj (S.map fun w => (w, sepM targetNat bits w, efn w, adj w)) →
                (p, q, pairCand targetNat bits p q) ∈ pm →
                ∃ x, InTree x nextTree ∧ CanM targetNat k (unpack x).toFinset := by
              intro p q hpS hqS hpq hpT hqT hpmem hpq_pm
              set U' := (S.erase p).erase q
              have hndp : (S.erase p).Nodup := hnd.erase p
              have hU'mem : ∀ z, z ∈ U' ↔ z ∈ S ∧ z ≠ p ∧ z ≠ q := by
                intro z; rw [mem_erase_of_nodup hndp, mem_erase_of_nodup hnd]; tauto
              have hU'p : ∀ z ∈ U', z ∈ S.erase p := fun z hz => List.mem_of_mem_erase hz
              have hU'q : ∀ z ∈ U', z ∈ S.erase q := fun z hz =>
                (mem_erase_of_nodup hnd).mpr ⟨((hU'mem z).mp hz).1, ((hU'mem z).mp hz).2.2⟩
              have hsubT : T ⊆ (combM o a b :: U').toFinset := by
                intro z hz
                by_cases ez : z = combM o a b
                · simp [ez]
                · have hzT' : z ∈ T' := Finset.mem_erase.mpr ⟨ez, hz⟩
                  exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((hU'mem z).mpr ⟨List.mem_toFinset.mp (hTe hzT'), fun h => hpT (h ▸ hzT'), fun h => hqT (h ▸ hzT')⟩))
              have hcU := monoCM hsubT ht
              have hcov : foldLor (sepM targetNat bits) U' ||| sepM targetNat bits (combM o a b) = fullM targetNat bits := by
                rw [Nat.lor_comm, ← foldLor_cons]; exact coveredM_sepM hM hcU bits hbits
              have hU_lt : ∀ z ∈ combM o a b :: U', z < 65536 := by
                intro z hz
                rcases List.mem_cons.mp hz with rfl | hz
                · exact hv_lt
                · exact hS_lt z ((hU'mem z).mp hz).1
              obtain ⟨a1, b1, hsc⟩ := scanPairsPre_sound _ h1 h2 hall2 p q (efn p) (efn q) (adj p) (adj q) U' (foldLor (sepM targetNat bits) U') hpmem
              cases hep : efn p <;> cases heq : efn q
              · simp only [hep, heq, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hsc
                have hge2 : 2 ≤ countNonEss (S.map fun w => (w, sepM targetNat bits w, efn w)) :=
                  countNonEss_ge_two (sepM targetNat bits) efn S hnd p q hpS hqS hpq hep heq
                simp only [hge2, ↓reduceIte] at hsc
                obtain ⟨haS, hbS, hab⟩ := combM_new_both_mem hS_lt ha hb hnew
                obtain ⟨_, _, hvnc, _⟩ := valsNew_props hnew
                have hpm_ab : (combM o a b, sepM targetNat bits (combM o a b)) ∈ (pm.flatMap fun p => p.2.2).filter (fun q => !S.contains q.1) := by
                  simp only [List.mem_filter, List.mem_flatMap, Bool.not_eq_true']
                  refine ⟨?_, hvnc⟩
                  rcases mkPairMat_spec targetNat bits S hnd a haS b hbS hab with h1m | h2m
                  · exact ⟨(a, b, pairCand targetNat bits a b), h1m, mem_pairCand targetNat bits haS hbS hnew⟩
                  · have hnew' : combM o b a ∈ valsNew S := by rw [combM_comm]; exact hnew
                    refine ⟨(b, a, pairCand targetNat bits b a), h2m, ?_⟩
                    rw [combM_comm o a b]; exact mem_pairCand targetNat bits hbS haS hnew'
                obtain ⟨a2, b2, hst⟩ := scanVsM_sound _ a1 b1 hsc _ hpm_ab hcov
                exact stepUHint_sound hU_lt hst hcU
              · simp only [hep, heq, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hsc
                have hqab := ess_forces_input hM hbits heq hU'q ha hb hcU
                have hcomb_q : ∃ z, z ∈ S ∧ z ≠ q ∧ combM o a b = combM o q z := by
                  rcases hqab with haq | hbq
                  · have hnew' : combM o q b ∈ valsNew S := by rw [← haq]; exact hnew
                    obtain ⟨hbS, hbq'⟩ := combM_new_other_mem hS_lt hqS hb hnew'
                    exact ⟨b, hbS, hbq', by rw [haq]⟩
                  · have hnew' : combM o q a ∈ valsNew S := by rw [combM_comm, ← hbq]; exact hnew
                    obtain ⟨haS, haq'⟩ := combM_new_other_mem hS_lt hqS ha hnew'
                    exact ⟨a, haS, haq', by rw [hbq, combM_comm]⟩
                obtain ⟨z, hzS, hzq, hce⟩ := hcomb_q
                have hnew' : combM o q z ∈ valsNew S := by rw [← hce]; exact hnew
                have hadj : (combM o a b, sepM targetNat bits (combM o a b)) ∈ adj q := by
                  simp only [adj, heq, ↓reduceIte]
                  rcases mkPairMat_spec targetNat bits S hnd q hqS z hzS (Ne.symm hzq) with h1m | h2m
                  · rw [hce]; exact mem_adjOf pm h1m (Or.inl rfl) (mem_pairCand targetNat bits hqS hzS hnew')
                  · have hnew'' : combM o z q ∈ valsNew S := by rw [combM_comm]; exact hnew'
                    rw [hce, combM_comm]; exact mem_adjOf pm h2m (Or.inr rfl) (mem_pairCand targetNat bits hzS hqS hnew'')
                obtain ⟨a2, b2, hst⟩ := scanVsM_sound _ a1 b1 hsc _ hadj hcov
                exact stepUHint_sound hU_lt hst hcU
              · simp only [hep, heq, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hsc
                have hpab := ess_forces_input hM hbits hep hU'p ha hb hcU
                have hcomb_p : ∃ z, z ∈ S ∧ z ≠ p ∧ combM o a b = combM o p z := by
                  rcases hpab with hap | hbp
                  · have hnew' : combM o p b ∈ valsNew S := by rw [← hap]; exact hnew
                    obtain ⟨hbS, hbp'⟩ := combM_new_other_mem hS_lt hpS hb hnew'
                    exact ⟨b, hbS, hbp', by rw [hap]⟩
                  · have hnew' : combM o p a ∈ valsNew S := by rw [combM_comm, ← hbp]; exact hnew
                    obtain ⟨haS, hap'⟩ := combM_new_other_mem hS_lt hpS ha hnew'
                    exact ⟨a, haS, hap', by rw [hbp, combM_comm]⟩
                obtain ⟨z, hzS, hzp, hce⟩ := hcomb_p
                have hnew' : combM o p z ∈ valsNew S := by rw [← hce]; exact hnew
                have hadj : (combM o a b, sepM targetNat bits (combM o a b)) ∈ adj p := by
                  simp only [adj, hep, ↓reduceIte]
                  rcases mkPairMat_spec targetNat bits S hnd p hpS z hzS (Ne.symm hzp) with h1m | h2m
                  · rw [hce]; exact mem_adjOf pm h1m (Or.inl rfl) (mem_pairCand targetNat bits hpS hzS hnew')
                  · have hnew'' : combM o z p ∈ valsNew S := by rw [combM_comm]; exact hnew'
                    rw [hce, combM_comm]; exact mem_adjOf pm h2m (Or.inr rfl) (mem_pairCand targetNat bits hzS hpS hnew'')
                obtain ⟨a2, b2, hst⟩ := scanVsM_sound _ a1 b1 hsc _ hadj hcov
                exact stepUHint_sound hU_lt hst hcU
              · simp only [hep, heq, Bool.and_true, ↓reduceIte] at hsc
                have hpab := ess_forces_input hM hbits hep hU'p ha hb hcU
                have hqab := ess_forces_input hM hbits heq hU'q ha hb hcU
                have hce : combM o a b = combM o p q := by
                  rcases hpab with hap | hbp <;> rcases hqab with haq | hbq
                  · exact absurd (hap.symm.trans haq) hpq
                  · rw [hap, hbq]
                  · rw [hbp, haq, combM_comm]
                  · exact absurd (hbp.symm.trans hbq) hpq
                have hlk : lookupPair p q pm = pairCand targetNat bits p q :=
                  lookupPair_eq pm (fun e he ⟨h1e, h2e⟩ => by rw [mkPairMat_val targetNat bits S e he, h1e, h2e]) hpq_pm
                rw [hlk] at hsc
                have hnew' : combM o p q ∈ valsNew S := by rw [← hce]; exact hnew
                have hpc : (combM o a b, sepM targetNat bits (combM o a b)) ∈ pairCand targetNat bits p q := by
                  rw [hce]; exact mem_pairCand targetNat bits hpS hqS hnew'
                obtain ⟨a2, b2, hst⟩ := scanVsM_sound _ a1 b1 hsc _ hpc hcov
                exact stepUHint_sound hU_lt hst hcU
            rcases drop2BAdj_mkPairMat_spec targetNat bits efn adj S hnd x0 hx0S y0 hy0S (Ne.symm hyx) with ⟨h1', hm1'⟩ | ⟨h2', hm2'⟩
            · exact handle_pair x0 y0 hx0S hy0S (Ne.symm hyx) hx0T hy0T h1' hm1'
            · exact handle_pair y0 x0 hy0S hx0S hyx hy0T hx0T h2' hm2'
        · have hTS : T ⊆ S.toFinset := by
            intro z hz
            exact (Finset.mem_insert.mp (hT hz)).resolve_left (fun ez => hvT (ez ▸ hz))
          exact hdrop1_finish hTS hn ht
  · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at hv
    cases hc1 : checkCutsM (fullM targetNat bits) nextTree (cutsM (k + 1) (S.map fun w => (w, sepM targetNat bits w))) h with
    | none => simp [hc1] at hv
    | some h1 =>
      simp only [hc1, Option.isSome_iff_exists] at hv
      obtain ⟨h2, hall2⟩ := hv
      obtain ⟨o, a, b, ha, hb, hh⟩ := hc
      rcases combM_case hS_lt ha hb with hfree | hnew
      · have hh' : CanM targetNat k S.toFinset := by
          refine monoCM_free (fun x hx => ?_) hh
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hfree
          · exact Or.inr (Or.inr hx)
        exact checkCutsInit_sound hS_lt hM hbits hc1 hh'
      · obtain ⟨T, hT, hn, ht⟩ := smallM hh
        by_cases hvT : combM o a b ∈ T
        · have hTe : T.erase (combM o a b) ⊆ S.toFinset := by
            intro y hy
            exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hy))).resolve_left (Finset.ne_of_mem_erase hy)
          have hcard : (T.erase (combM o a b)).card ≤ k := by
            rw [Finset.card_erase_of_mem hvT]; omega
          obtain ⟨U', hU', hu'⟩ := cutsSpec k S (T.erase (combM o a b)) hTe hcard
          have hsub : T ⊆ (combM o a b :: U').toFinset := by
            intro y hy
            by_cases ey : y = combM o a b
            · simp [ey]
            · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hu' (Finset.mem_erase.mpr ⟨ey, hy⟩))))
          have hcU := monoCM hsub ht
          have hUmem := cutsM_spec (sepM targetNat bits) S k U' hU'
          obtain ⟨a1, b1, hUstep⟩ := scanCutsM_sound _ h1 h2 hall2 (U', foldLor (sepM targetNat bits) U') hUmem
          have hvmem : (combM o a b, sepM targetNat bits (combM o a b)) ∈ (valsNew S).map (fun v => (v, sepM targetNat bits v)) :=
            List.mem_map.mpr ⟨combM o a b, hnew, rfl⟩
          have hcov : foldLor (sepM targetNat bits) U' ||| sepM targetNat bits (combM o a b) = fullM targetNat bits := by
            rw [Nat.lor_comm, ← foldLor_cons]
            exact coveredM_sepM hM hcU bits hbits
          obtain ⟨a2, b2, hvstep⟩ := scanVsM_sound _ a1 b1 hUstep _ hvmem hcov
          have hv_lt : combM o a b < 65536 := by
            simp only [valsNew, List.mem_filter] at hnew
            exact opPairsM_lt S hS_lt _ hnew.1
          have hU_lt : ∀ x ∈ combM o a b :: U', x < 65536 := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hv_lt
            · exact hS_lt x (cuts_mem_sub S k U' hU' x hx)
          exact stepUHint_sound hU_lt hvstep hcU
        · have hTS : T ⊆ S.toFinset := by
            intro y hy
            exact (Finset.mem_insert.mp (hT hy)).resolve_left (fun ey => hvT (ey ▸ hy))
          exact checkCutsInit_sound hS_lt hM hbits hc1 (monoCM hTS ht)

def row2 : BinaryTree (ℕ × ℕ) := E
def row3 : BinaryTree (ℕ × ℕ) := N 0xf888666f191100f0 0 (N 0xf00088f86e6f1111 0 (N 0xf000666f11f10808 0 (L 0xf000666f11110868 0) (L 0xf00088886e6f11f1 0)) (N 0xf888666f11710f00 0 (L 0xf88860601f11000f 0) E)) (N 0xf8e866661f11000f 0 (N 0xf88868601111000f 0 (L 0xf888666f1f1111f1 0) (L 0xf8886e6f111100f0 0)) (N 0xf8e86f661111000f 0 (L 0xf8e8666f11110f00 0) E))
def row4_c0 : BinaryTree (ℕ × ℕ) := N 0xf00088f8444f2a221111 0 (N 0xf0008888666f191100f0 0 (N 0xf000888860601f11000f 0 (N 0xf000666f1111080800f0 0 (N 0xf000666611f10808000f 0 (L 0xf0004444222f11f10808 0) E) (N 0xf0008888444f2a2211f1 0 (L 0xf000888844442a2f11f1 0) E)) (N 0xf0008888666f11f10800 0 (N 0xf0008888666f11710f00 0 (L 0xf0008888666611f1080f 0) E) (N 0xf0008888666f11f10f0f 0 (L 0xf0008888666f11f10f00 0) E))) (N 0xf00088886f66666f11f1 0 (N 0xf0008888666f2f2f11f1 0 (N 0xf0008888666f2f2211f1 0 (L 0xf0008888666f1f1111f1 0) E) (N 0xf00088886e6f111100f0 0 (L 0xf00088886e6611f1000f 0) E)) (N 0xf00088e8666f11110f00 0 (N 0xf00088e866661f11000f 0 (L 0xf00088886f6f666f11f1 0) E) (N 0xf00088f844442a2f1111 0 (L 0xf00088e86f661111000f 0) E)))) (N 0xf00088f86f661111000f 0 (N 0xf00088f8666f11110f00 0 (N 0xf00088f8444f2f2f1111 0 (N 0xf00088f8444f2f2211f1 0 (L 0xf00088f8444f2f221111 0) E) (N 0xf00088f8666f11110800 0 (L 0xf00088f866661111080f 0) E)) (N 0xf00088f8666f2f221111 0 (N 0xf00088f8666f11f10f00 0 (L 0xf00088f8666f11110f0f 0) E) (N 0xf00088f86e661111000f 0 (L 0xf00088f8666f2f2f1111 0) E))) (N 0xf00088f86f6f222f1111 0 (N 0xf00088f86f66222f1111 0 (N 0xf00088f86f661f11000f 0 (L 0xf00088f86f6611f1000f 0) E) (N 0xf00088f86f6f1111000f 0 (L 0xf00088f86f66666f1111 0) E)) (N 0xf0608888666f11110f00 0 (N 0xf060888866661f11000f 0 (L 0xf00088f86f6f666f1111 0) E) (N 0xf8884444222f191100f0 0 (L 0xf06088886f661111000f 0) E))))
def row4_c1 : BinaryTree (ℕ × ℕ) := N 0xf8886f66111100f0000f 0 (N 0xf88866661f1111f1000f 0 (N 0xf888606011110f00000f 0 (N 0xf888444f2a22111100f0 0 (N 0xf888444f222f1f1100f0 0 (L 0xf88844442a2f111100f0 0) E) (N 0xf888444f2f2f111100f0 0 (L 0xf888444f2f22111100f0 0) E)) (N 0xf8886666191100f0000f 0 (N 0xf888666611710f00000f 0 (L 0xf88866661111080f00f0 0) E) (N 0xf88866661f1100f0000f 0 (L 0xf88866661f110060000f 0) E))) (N 0xf888666f1f1100f0000f 0 (N 0xf888666f11110f0000f0 0 (N 0xf888666f11110f000060 0 (L 0xf888666f1111080000f0 0) E) (N 0xf888666f11f111110f00 0 (L 0xf888666f11110f0f00f0 0) E)) (N 0xf888666f2f2f111100f0 0 (N 0xf888666f2f22111100f0 0 (L 0xf888666f1f11111100f0 0) E) (N 0xf8886f6611110060000f 0 (L 0xf8886e66111100f0000f 0) E)))) (N 0xf888f0f0444f2f221111 0 (N 0xf8886f6f666f111100f0 0 (N 0xf8886f66666f111100f0 0 (N 0xf8886f66222f111100f0 0 (L 0xf8886f661f1100f0000f 0) E) (N 0xf8886f6f222f111100f0 0 (L 0xf8886f6f111100f0000f 0) E)) (N 0xf88888f8666f11110f00 0 (N 0xf88888f866661f11000f 0 (L 0xf88888f8444f2f221111 0) E) (N 0xf888f000666f11f10f00 0 (L 0xf88888f86f661111000f 0) E))) (N 0xf8f8f000666f11110f00 0 (N 0xf888f0f06f661111000f 0 (N 0xf888f0f0666f11110f00 0 (L 0xf888f0f066661f11000f 0) E) (N 0xf8f8f000444f2f221111 0 (L 0xf8e8666611110f00000f 0) E)) (N 0xf8f8f88866661f11000f 0 (N 0xf8f8f888444f2f221111 0 (L 0xf8f8f0006f661111000f 0) E) (N 0xf8f8f8886f661111000f 0 (L 0xf8f8f888666f11110f00 0) E))))
def row4 : BinaryTree (ℕ × ℕ) := N 0xf8884444222f1f1111f1 0 row4_c0 row4_c1
def row5_c0 : BinaryTree (ℕ × ℕ) := N 0xf000888866661111080f00f0 0 (N 0xf000888844442a2f111100f0 0 (N 0xf00088884444222f11f10f00 0 (N 0xf00066661111080800f0000f 0 (N 0xf0004444222f1111080800f0 0 (L 0xf0004444222211f10808000f 2) E) (N 0xf00088884444222f11f10800 2 (L 0xf00088884444222211f1080f 2) E)) (N 0xf00088884444222f1f1111f1 0 (N 0xf00088884444222f191100f0 0 (L 0xf00088884444222f11f10f0f 0) E) (L 0xf000888844442a2211f1000f 0))) (N 0xf0008888444f2f22111100f0 0 (N 0xf0008888444f222f11f10f00 0 (N 0xf000888844442f2f222f11f1 0 (L 0xf000888844442f22222f11f1 0) E) (N 0xf0008888444f2a22111100f0 0 (L 0xf0008888444f222f1f1100f0 0) E)) (N 0xf0008888444f2f2f111100f0 0 (N 0xf0008888444f2f22222211f1 0 (L 0xf0008888444f2f2211f100f0 0) E) (L 0xf0008888606011110f00000f 0)))) (N 0xf0008888666f1111080000f0 0 (N 0xf000888866661f110060000f 0 (N 0xf0008888666611f10f00000f 0 (N 0xf0008888666611f10800000f 0 (L 0xf0008888666611710f00000f 0) E) (N 0xf00088886666191100f0000f 0 (L 0xf0008888666611f10f0f000f 0) E)) (N 0xf00088886666222f11f10f00 0 (N 0xf000888866661f1111f1000f 0 (L 0xf000888866661f1100f0000f 0) E) (L 0xf000888866662f2211f1000f 0))) (N 0xf0008888666f11f10f0000f0 0 (N 0xf0008888666f11110f0f00f0 0 (N 0xf0008888666f11110f0000f0 0 (L 0xf0008888666f11110f000060 0) E) (L 0xf0008888666f11f10f00000f 0)) (N 0xf0008888666f1f11111100f0 0 (N 0xf0008888666f1f1100f0000f 0 (L 0xf0008888666f11f111110f00 0) E) (L 0xf0008888666f222211f10f00 0))))
def row5_c1 : BinaryTree (ℕ × ℕ) := N 0xf00088f844442a221111000f 0 (N 0xf00088886f66666f111100f0 0 (N 0xf00088886f66111100f0000f 0 (N 0xf0008888666f666611f10f00 0 (N 0xf0008888666f2f2f111100f0 0 (L 0xf0008888666f2f22111100f0 0) E) (N 0xf00088886f6611110060000f 0 (L 0xf00088886e66111100f0000f 0) E)) (N 0xf00088886f66222f111100f0 0 (N 0xf00088886f661f1100f0000f 0 (L 0xf00088886f6611f100f0000f 0) E) (L 0xf00088886f66666611f1000f 0))) (N 0xf00088f8444422221111080f 2 (N 0xf00088886f6f666f111100f0 0 (N 0xf00088886f6f222f111100f0 0 (L 0xf00088886f6f111100f0000f 0) E) (L 0xf00088e8666611110f00000f 0)) (N 0xf00088f84444222f11110f0f 1 (N 0xf00088f84444222f11110f00 1 (L 0xf00088f84444222f11110800 2) E) (L 0xf00088f84444222f11f10f00 1)))) (N 0xf00088f8444f2f2222221111 2 (N 0xf00088f844442f2f222f1111 0 (N 0xf00088f844442f221f11000f 0 (N 0xf00088f844442f2211f1000f 0 (L 0xf00088f844442f221111000f 0) E) (N 0xf00088f844442f2f1111000f 0 (L 0xf00088f844442f22222f1111 0) E)) (N 0xf00088f8444f2f22111100f0 4 (N 0xf00088f8444f2f221111000f 4 (L 0xf00088f8444f222f11110f00 2) E) (L 0xf00088f8444f2f2211110f00 2))) (N 0xf00088f8666611110f0f000f 0 (N 0xf00088f8666611110800000f 0 (N 0xf00088f84f442f221111000f 0 (L 0xf00088f8444f44442f221111 6) E) (L 0xf00088f8666611110f00000f 0)) (N 0xf00088f86666222f11110f00 0 (N 0xf00088f866661f110f00000f 0 (L 0xf00088f8666611f10f00000f 0) E) (L 0xf00088f866662f221111000f 0))))
def row5_L : BinaryTree (ℕ × ℕ) := N 0xf0008888666f222f11f10f00 0 row5_c0 row5_c1
def row5_c2 : BinaryTree (ℕ × ℕ) := N 0xf888444422221f1100f0000f 0 (N 0xf00088f8888866661f11000f 0 (N 0xf00088f86f6611110f00000f 0 (N 0xf00088f8666f222f11110f00 0 (N 0xf00088f8666f222211110f00 0 (L 0xf00088f8666f11110f0000f0 0) E) (N 0xf00088f86f66111100f0000f 0 (L 0xf00088f8666f666611110f00 0) E)) (N 0xf00088f86f6666661111000f 0 (N 0xf00088f86f662f221111000f 0 (L 0xf00088f86f6622221111000f 0) E) (L 0xf00088f88888444f2f221111 2))) (N 0xf0f0f000888866661f11000f 0 (N 0xf0608888666611110f00000f 0 (N 0xf00088f888886f661111000f 0 (L 0xf00088f88888666f11110f00 0) E) (L 0xf0f0f0008888444f2f221111 0)) (N 0xf888444422221111080f00f0 2 (N 0xf0f0f00088886f661111000f 0 (L 0xf0f0f0008888666f11110f00 0) E) (L 0xf88844442222191100f0000f 2)))) (N 0xf88844442f22222f111100f0 0 (N 0xf8884444222f1f1100f0000f 0 (N 0xf8884444222f11110f0000f0 1 (N 0xf8884444222f1111080000f0 4 (L 0xf888444422221f1111f1000f 2) E) (N 0xf8884444222f11f111110f00 0 (L 0xf8884444222f11110f0f00f0 1) E)) (N 0xf88844442f22111100f0000f 0 (N 0xf88844442a22111100f0000f 0 (L 0xf8884444222f1f11111100f0 0) E) (L 0xf88844442f221f1100f0000f 0))) (N 0xf888444f2f2211110f0000f0 4 (N 0xf888444f222f11110f0000f0 4 (N 0xf88844442f2f222f111100f0 0 (L 0xf88844442f2f111100f0000f 0) E) (L 0xf888444f2f22111100f0000f 8)) (N 0xf8884f442f22111100f0000f 0 (N 0xf888444f44442f22111100f0 12 (L 0xf888444f2f222222111100f0 4) E) (L 0xf88866661111080000f0000f 0))))
def row5_c3 : BinaryTree (ℕ × ℕ) := N 0xf88888f8444422221f11000f 0 (N 0xf888666f222f11110f0000f0 0 (N 0xf888666622221f1100f0000f 0 (N 0xf888666611f111110f00000f 0 (N 0xf888666611110f0f00f0000f 0 (L 0xf888666611110f0000f0000f 0) E) (N 0xf88866661f11111100f0000f 0 (L 0xf88866661f110f0000f0000f 0) E)) (N 0xf888666f11110f0000f0000f 0 (N 0xf88866662f22111100f0000f 0 (L 0xf8886666222f11110f0000f0 0) E) (L 0xf888666f222211110f0000f0 0))) (N 0xf8886f666666111100f0000f 0 (N 0xf8886f662222111100f0000f 0 (N 0xf8886f6611110f0000f0000f 0 (L 0xf888666f666611110f0000f0 0) E) (L 0xf8886f662f22111100f0000f 0)) (N 0xf8888888666f11110f0000f0 0 (N 0xf888888866661f1100f0000f 0 (L 0xf8888888444f2f22111100f0 8) E) (L 0xf88888886f66111100f0000f 0)))) (N 0xf888f0f04444222f11110f00 1 (N 0xf888f000666611f10f00000f 0 (N 0xf88888f8666611110f00000f 0 (N 0xf88888f844442f221111000f 0 (L 0xf88888f84444222f11110f00 1) E) (N 0xf888f000444f2f22111100f0 16 (L 0xf888f0004444222f11f10f00 0) E)) (N 0xf888f0006f66111100f0000f 0 (N 0xf888f000666f11110f0000f0 0 (L 0xf888f00066661f1100f0000f 0) E) (L 0xf888f0f0444422221f11000f 0))) (N 0xf8f8f000666611110f00000f 0 (N 0xf8f8f0004444222f11110f00 1 (N 0xf888f0f0666611110f00000f 0 (L 0xf888f0f044442f221111000f 0) E) (L 0xf8f8f00044442f221111000f 0)) (N 0xf8f8f88844442f221111000f 0 (N 0xf8f8f8884444222f11110f00 1 (L 0xf8f8f888444422221f11000f 0) E) (L 0xf8f8f888666611110f00000f 0))))
def row5_R : BinaryTree (ℕ × ℕ) := N 0xf888666611110f000060000f 0 row5_c2 row5_c3
def row5 : BinaryTree (ℕ × ℕ) := N 0xf00088f8666f11110f00000f 0 row5_L row5_R
def row6_c0 : BinaryTree (ℕ × ℕ) := N 0xf000888844442f2f222f111100f0 0 (N 0xf00088884444222f11f10f0000f0 276 (N 0xf0008888444422221f1100f0000f 0 (N 0xf00088884444222211f10f00000f 2 (N 0xf0008888444422221111080f00f0 8 (L 0xf000444422221111080800f0000f 2) (L 0xf00088884444222211f10800000f 20)) (N 0xf000888844442222191100f0000f 2 (L 0xf00088884444222211f10f0f000f 2) E)) (N 0xf00088884444222f11110f0000f0 4 (N 0xf00088884444222f1111080000f0 16 (L 0xf0008888444422221f1111f1000f 2) E) (N 0xf00088884444222f11f10f00000f 40 (L 0xf00088884444222f11110f0f00f0 4) E))) (N 0xf000888844442f22111100f0000f 0 (N 0xf00088884444222f1f11111100f0 0 (N 0xf00088884444222f1f1100f0000f 0 (L 0xf00088884444222f11f111110f00 40) E) (N 0xf000888844442a22111100f0000f 0 (L 0xf00088884444222f222211f10f00 40) E)) (N 0xf000888844442f22222211f1000f 0 (N 0xf000888844442f221f1100f0000f 0 (L 0xf000888844442f2211f100f0000f 0) E) (N 0xf000888844442f2f111100f0000f 0 (L 0xf000888844442f22222f111100f0 0) E)))) (N 0xf0008888666611f111110f00000f 0 (N 0xf00088884f442f22111100f0000f 0 (N 0xf0008888444f2f2211110f0000f0 32 (N 0xf0008888444f2f22111100f0000f 32 (L 0xf0008888444f222f11110f0000f0 16) E) (N 0xf0008888444f44442f22111100f0 96 (L 0xf0008888444f2f222222111100f0 64) E)) (N 0xf0008888666611110f0000f0000f 0 (N 0xf0008888666611110f000060000f 0 (L 0xf000888866661111080000f0000f 0) E) (N 0xf0008888666611f10f0000f0000f 0 (L 0xf0008888666611110f0f00f0000f 0) E))) (N 0xf000888866662f22111100f0000f 0 (N 0xf00088886666222211f10f00000f 0 (N 0xf000888866661f11111100f0000f 0 (L 0xf000888866661f110f0000f0000f 0) E) (N 0xf00088886666222f11110f0000f0 0 (L 0xf0008888666622221f1100f0000f 0) E)) (N 0xf0008888666f222f11110f0000f0 0 (N 0xf0008888666f222211110f0000f0 0 (L 0xf0008888666f11110f0000f0000f 0) E) (N 0xf00088886f6611110f0000f0000f 0 (L 0xf0008888666f666611110f0000f0 0) E))))
def row6_c1 : BinaryTree (ℕ × ℕ) := N 0xf888444422221111080000f0000f 36 (N 0xf00088f844442f2211110f00000f 32 (N 0xf00088f84444222211f10f00000f 10 (N 0xf00088f84444222211110800000f 20 (N 0xf00088886f666666111100f0000f 0 (L 0xf00088886f662f22111100f0000f 0) E) (N 0xf00088f84444222211110f0f000f 10 (L 0xf00088f84444222211110f00000f 10) E)) (N 0xf00088f84444222f11110f0000f0 612 (N 0xf00088f84444222f11110f00000f 2216 (L 0xf00088f8444422221f110f00000f 2) E) (N 0xf00088f844442f22111100f0000f 32 (L 0xf00088f84444222f222211110f00 232) E))) (N 0xf00088f8888844442f221111000f 32 (N 0xf00088f86666222211110f00000f 0 (N 0xf00088f8666611110f0000f0000f 0 (L 0xf00088f844442f2222221111000f 32) E) (N 0xf00088f888884444222f11110f00 394 (L 0xf00088f88888444422221f11000f 0) E)) (N 0xf0f0f00088884444222f11110f00 1 (N 0xf0f0f0008888444422221f11000f 0 (L 0xf00088f88888666611110f00000f 0) E) (N 0xf0f0f0008888666611110f00000f 0 (L 0xf0f0f000888844442f221111000f 0) E)))) (N 0xf88888884444222f11110f0000f0 6288 (N 0xf8884444222f11110f0000f0000f 17728 (N 0xf8884444222211f111110f00000f 2 (N 0xf8884444222211110f0f00f0000f 10 (L 0xf8884444222211110f0000f0000f 18) E) (N 0xf888444422221f11111100f0000f 196 (L 0xf888444422221f110f0000f0000f 112) E)) (N 0xf88844442f222222111100f0000f 64 (N 0xf88844442f2211110f0000f0000f 64 (L 0xf8884444222f222211110f0000f0 1856) E) (N 0xf8888888444422221f1100f0000f 96 (L 0xf8886666222211110f0000f0000f 0) E))) (N 0xf888f0004444222f11110f0000f0 12864 (N 0xf88888f84444222211110f00000f 18 (N 0xf8888888666611110f0000f0000f 0 (L 0xf888888844442f22111100f0000f 128) E) (N 0xf888f000444422221f1100f0000f 96 (L 0xf888f0004444222211f10f00000f 2) E)) (N 0xf888f0f04444222211110f00000f 18 (N 0xf888f000666611110f0000f0000f 0 (L 0xf888f00044442f22111100f0000f 256) E) (N 0xf8f8f8884444222211110f00000f 18 (L 0xf8f8f0004444222211110f00000f 10) E))))
def row6 : BinaryTree (ℕ × ℕ) := N 0xf00088886f662222111100f0000f 0 row6_c0 row6_c1
def row7 : BinaryTree (ℕ × ℕ) := N 0xf00088884444222f222211110f0000f0 27136 (N 0xf00088884444222211f111110f00000f 6420 (N 0xf00088884444222211110f0f00f0000f 34 (N 0xf00088884444222211110f0000f0000f 66 (L 0xf0008888444422221111080000f0000f 132) E) (L 0xf00088884444222211f10f0000f0000f 68756)) (N 0xf0008888444422221f11111100f0000f 388 (L 0xf0008888444422221f110f0000f0000f 448) (L 0xf00088884444222f11110f0000f0000f 2102400))) (N 0xf00088f888884444222211110f00000f 918676 (N 0xf00088886666222211110f0000f0000f 0 (N 0xf000888844442f222222111100f0000f 1024 (L 0xf000888844442f2211110f0000f0000f 512) E) (L 0xf00088f84444222211110f0000f0000f 581780)) (N 0xf88888884444222211110f0000f0000f 14697492 (L 0xf0f0f00088884444222211110f00000f 18) (L 0xf888f0004444222211110f0000f0000f 29429780)))
def row8 : BinaryTree (ℕ × ℕ) := L 0xf00088884444222211110f0000f0000f 2130480

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit : (checkCutsM fullVal row8 (cutsM 9 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel

abbrev vf3 := verifyNode maskParam fullVal 2 bits row2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk3 : checkTree (vf3) row3 = true := by decide +kernel

abbrev vf4 := verifyNode maskParam fullVal 3 bits row3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4L : checkTree (vf4) row4_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk4R : checkTree (vf4) row4_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk4V : (vf4) 0xf8884444222f1f1111f1 0 = true := by decide +kernel
theorem chk4 : checkTree (vf4) row4 = true := checkTree_node chk4V chk4L chk4R

abbrev vf5 := verifyNode maskParam fullVal 4 bits row4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LL : checkTree (vf5) row5_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5LR : checkTree (vf5) row5_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5LV : (vf5) 0xf0008888666f222f11f10f00 0 = true := by decide +kernel
theorem chk5L : checkTree (vf5) row5_L = true := checkTree_node chk5LV chk5LL chk5LR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RL : checkTree (vf5) row5_c2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5RR : checkTree (vf5) row5_c3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5RV : (vf5) 0xf888666611110f000060000f 0 = true := by decide +kernel
theorem chk5R : checkTree (vf5) row5_R = true := checkTree_node chk5RV chk5RL chk5RR

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk5V : (vf5) 0xf00088f8666f11110f00000f 0 = true := by decide +kernel
theorem chk5 : checkTree (vf5) row5 = true := checkTree_node chk5V chk5L chk5R

abbrev vf6 := verifyNode maskParam fullVal 5 bits row5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6L : checkTree (vf6) row6_c0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6R : checkTree (vf6) row6_c1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem chk6V : (vf6) 0xf00088886f662222111100f0000f 0 = true := by decide +kernel
theorem chk6 : checkTree (vf6) row6 = true := checkTree_node chk6V chk6L chk6R

abbrev vf7 := verifyNode maskParam fullVal 6 bits row6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk7 : checkTree (vf7) row7 = true := by decide +kernel

abbrev vf8 := verifyNode maskParam fullVal 7 bits row7
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk8 : checkTree (vf8) row8 = true := by decide +kernel

theorem fullVal_eq : fullVal = fullM maskParam bits := by decide +kernel
theorem hbits_proof : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false := by
  intro bitB h
  simp only [bits, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, rfl, by decide, by decide⟩
  · exact ⟨2, rfl, by decide, by decide⟩
  · exact ⟨4, rfl, by decide, by decide⟩
  · exact ⟨7, rfl, by decide, by decide⟩
  · exact ⟨8, rfl, by decide, by decide⟩
  · exact ⟨9, rfl, by decide, by decide⟩
  · exact ⟨10, rfl, by decide, by decide⟩
  · exact ⟨15, rfl, by decide, by decide⟩
theorem inputs_lt : ∀ t ∈ inputs, t < 65536 := by decide
theorem targetNat_lt : targetNat < 2 ^ 16 := by decide

theorem excluded (hc : CanM targetNat 8 inputs.toFinset) : False := by
  obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit
  rw [fullVal_eq] at hh0
  obtain ⟨x8, hx8, c8⟩ := checkCutsInit_sound inputs_lt targetNat_lt hbits_proof hh0 hc
  obtain ⟨hh8, hchk8⟩ := checkTree_sound row8 chk8 x8 hx8
  dsimp only [vf8] at hchk8
  rw [fullVal_eq] at hchk8
  obtain ⟨x7, hx7, c7⟩ := advanceNode targetNat_lt hbits_proof hchk8 c8
  obtain ⟨hh7, hchk7⟩ := checkTree_sound row7 chk7 x7 hx7
  dsimp only [vf7] at hchk7
  rw [fullVal_eq] at hchk7
  obtain ⟨x6, hx6, c6⟩ := advanceNode targetNat_lt hbits_proof hchk7 c7
  obtain ⟨hh6, hchk6⟩ := checkTree_sound row6 chk6 x6 hx6
  dsimp only [vf6] at hchk6
  rw [fullVal_eq] at hchk6
  obtain ⟨x5, hx5, c5⟩ := advanceNode targetNat_lt hbits_proof hchk6 c6
  obtain ⟨hh5, hchk5⟩ := checkTree_sound row5 chk5 x5 hx5
  dsimp only [vf5] at hchk5
  rw [fullVal_eq] at hchk5
  obtain ⟨x4, hx4, c4⟩ := advanceNode targetNat_lt hbits_proof hchk5 c5
  obtain ⟨hh4, hchk4⟩ := checkTree_sound row4 chk4 x4 hx4
  dsimp only [vf4] at hchk4
  rw [fullVal_eq] at hchk4
  obtain ⟨x3, hx3, c3⟩ := advanceNode targetNat_lt hbits_proof hchk4 c4
  obtain ⟨hh3, hchk3⟩ := checkTree_sound row3 chk3 x3 hx3
  dsimp only [vf3] at hchk3
  rw [fullVal_eq] at hchk3
  obtain ⟨x2, hx2, c2⟩ := advanceNode targetNat_lt hbits_proof hchk3 c3
  exact hx2


def inputsN : List ℕ := [15, 240, 3840, 61440, 0, 4369, 8738, 17476, 0, 34952]

def embedR : Fin 4 → Fin 5
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨3, by decide⟩

def embedC : Fin 4 → Fin 5
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨4, by decide⟩

theorem inputsN_lt : ∀ t ∈ inputsN, t < 65536 := by decide
theorem inputsN_free : ∀ t ∈ inputsN, freeM inputs.toFinset t := by
  have h : ∀ t ∈ inputsN, t = 0 ∨ t = 65535 ∨ t ∈ inputs := by decide
  intro t ht
  rcases h t ht with rfl | rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (List.mem_toFinset.mpr hm))
theorem oneEachN_map (p : Fin 16) :
    oneEach (embedR ⟨p.val / 4, by omega⟩) (embedC ⟨p.val % 4, by omega⟩) =
    inputsN.map (fun t => t.testBit p.val) := by
  revert p; decide

theorem proj_bit_eq (p : Fin 16) :
    (7586009 : ℕ).testBit (5 * (embedR ⟨p.val / 4, by omega⟩).val + (embedC ⟨p.val % 4, by omega⟩).val) =
    targetNat.testBit p.val := by
  revert p; decide

theorem proj_freeM_sub {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) {v : ℕ} (hv : freeM S v) : freeM T v := by
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact h v hv

theorem proj_monoCM_free {f k : ℕ} {S T : Finset ℕ} (h : ∀ x ∈ S, freeM T x) (hc : CanM f k S) : CanM f k T := by
  induction k generalizing S T with
  | zero => exact proj_freeM_sub h hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, a, b, proj_freeM_sub h ha, proj_freeM_sub h hb, ih ?_ hh⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · exact (h x hx).imp_right (Or.imp_right (fun e => Finset.mem_insert_of_mem e))

theorem proj_stepUpM {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) : CanM f (k + 1) S :=
  ⟨0, 0, 0, Or.inl rfl, Or.inl rfl, proj_monoCM_free (fun x hx => Or.inr (Or.inr (Finset.mem_insert_of_mem hx))) hc⟩

theorem proj_padCM {f k j : ℕ} {S : Finset ℕ} (hj : k ≤ j) (hc : CanM f k S) : CanM f j S := by
  induction hj with
  | refl => exact hc
  | step _ ih => exact proj_stepUpM ih

def gateHasZero (T : List ℕ) (g : Gate) : Bool :=
  g.inputs.any (fun i => Nat.beq (T.getD i 0) 0)

def zcount (T : List ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if gateHasZero T g then 1 else 0) + zcount (tstepM T g) gs

theorem zcount_le (gs : List Gate) : ∀ T, zcount T gs ≤ gs.length := by
  induction gs with
  | nil => intro T; simp [zcount]
  | cons g gs ih =>
    intro T
    simp only [zcount, List.length_cons]
    have h := ih (tstepM T g)
    split <;> omega

theorem gtM_free_of_zero (T : List ℕ) (g : Gate) (hg : GOkM g) (hz : gateHasZero T g = true) :
    freeM T.toFinset (gtM g.op (g.inputs.map fun i => T.getD i 0)) := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  cases hin : g.inputs with
  | nil => simp [gateHasZero, hin] at hz
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [gateHasZero, hin, List.any_cons, List.any_nil, Bool.or_false] at hz
      have ha : T.getD a 0 = 0 := Nat.eq_of_beq_eq_true hz
      rcases hop with hop | hop <;> (rw [hop]; simp only [List.map_cons, List.map_nil, gtM, ha]; exact Or.inl rfl)
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        simp only [gateHasZero, hin, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hz
        rcases hz with ha | hb
        · have ha0 : T.getD a 0 = 0 := Nat.eq_of_beq_eq_true ha
          rcases hop with hop | hop
          · rw [hop]; simp only [List.map_cons, List.map_nil, gtM, ha0, Nat.zero_and]; exact Or.inl rfl
          · rw [hop]; simp only [List.map_cons, List.map_nil, gtM, ha0, Nat.zero_or]; exact getWireM T b
        · have hb0 : T.getD b 0 = 0 := Nat.eq_of_beq_eq_true hb
          rcases hop with hop | hop
          · rw [hop]; simp only [List.map_cons, List.map_nil, gtM, hb0, Nat.and_zero]; exact Or.inl rfl
          · rw [hop]; simp only [List.map_cons, List.map_nil, gtM, hb0, Nat.or_zero]; exact getWireM T a
      | cons c rest3 => simp [hin] at hlen

theorem fromTabsM_zcount (f : ℕ) (gs : List Gate) :
    ∀ T : List ℕ, (∀ g ∈ gs, GOkM g) → freeM (tabsM T gs).toFinset f →
    CanM f (gs.length - zcount T gs) T.toFinset := by
  induction gs with
  | nil => intro T _ hf; exact hf
  | cons g gs ih =>
    intro T hok hf
    have hg : GOkM g := hok g (by simp)
    have hgs : ∀ g' ∈ gs, GOkM g' := fun g' hg' => hok g' (by simp [hg'])
    have hsub := ih (tstepM T g) hgs (by simpa [tabsM] using hf)
    have hzl : zcount (tstepM T g) gs ≤ gs.length := zcount_le gs (tstepM T g)
    by_cases hz : gateHasZero T g = true
    · have hlen_eq : (g :: gs).length - zcount T (g :: gs) = gs.length - zcount (tstepM T g) gs := by
        simp only [zcount, hz, ↓reduceIte, List.length_cons]; omega
      rw [hlen_eq]
      have hfree_nv := gtM_free_of_zero T g hg hz
      refine proj_monoCM_free ?_ hsub
      intro x hx
      have hx' : x ∈ T ∨ x = gtM g.op (g.inputs.map fun i => T.getD i 0) := by
        simpa [tstepM] using List.mem_toFinset.mp hx
      rcases hx' with hm | rfl
      · exact Or.inr (Or.inr (List.mem_toFinset.mpr hm))
      · exact hfree_nv
    · have hzf : gateHasZero T g = false := Bool.eq_false_iff.mpr hz
      have hlen_eq : (g :: gs).length - zcount T (g :: gs) = (gs.length - zcount (tstepM T g) gs) + 1 := by
        simp only [zcount, hzf, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      rw [hlen_eq]
      have hstep : ∀ (v : ℕ), freeM (tstepM T g).toFinset v →
          freeM (insert (gtM g.op (g.inputs.map fun i => T.getD i 0)) T.toFinset) v := by
        intro v hv
        rcases hv with rfl | rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · have hm : v ∈ T ∨ v = gtM g.op (g.inputs.map fun i => T.getD i 0) := by
            simpa [tstepM] using List.mem_toFinset.mp hv
          rcases hm with hm | rfl
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hm)))
          · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
      have hsub' : CanM f (gs.length - zcount (tstepM T g) gs)
          (insert (gtM g.op (g.inputs.map fun i => T.getD i 0)) T.toFinset) :=
        proj_monoCM_free (fun x hx => hstep x (Or.inr (Or.inr hx))) hsub
      rcases hg with ⟨hop, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      cases hin : g.inputs with
      | nil =>
        have hfr : freeM T.toFinset (gtM g.op (g.inputs.map fun i => T.getD i 0)) := by
          rcases hop with hop | hop
          · rw [hop, hin]; exact Or.inr (Or.inl rfl)
          · rw [hop, hin]; exact Or.inl rfl
        exact proj_stepUpM (proj_monoCM_free (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hfr
          · exact Or.inr (Or.inr hx)) hsub')
      | cons a rest =>
        cases rest with
        | nil =>
          have hfr : freeM T.toFinset (gtM g.op (g.inputs.map fun i => T.getD i 0)) := by
            rcases hop with hop | hop <;> simpa [hop, gtM, hin] using getWireM T a
          exact proj_stepUpM (proj_monoCM_free (fun x hx => by
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hfr
            · exact Or.inr (Or.inr hx)) hsub')
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            rcases hop with hop | hop
            · exact ⟨0, T.getD a 0, T.getD b 0, getWireM T a, getWireM T b, by simpa [hop, gtM, hin, combM] using hsub'⟩
            · exact ⟨1, T.getD a 0, T.getD b 0, getWireM T a, getWireM T b, by simpa [hop, gtM, hin, combM] using hsub'⟩
          | cons c rest3 => simp [hin] at hlen

theorem tabsM_append (T : List ℕ) (gs1 gs2 : List Gate) :
    tabsM T (gs1 ++ gs2) = tabsM (tabsM T gs1) gs2 := by
  simp [tabsM, List.foldl_append]

theorem tabsM_prefix (gs : List Gate) : ∀ T : List ℕ,
    ∃ t : List ℕ, tabsM T gs = T ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro T; exact ⟨[], by simp [tabsM], rfl⟩
  | cons g gs ih =>
    intro T
    obtain ⟨t, ht, hl⟩ := ih (tstepM T g)
    refine ⟨gtM g.op (g.inputs.map fun i => T.getD i 0) :: t, ?_, by simp [hl]⟩
    change tabsM (tstepM T g) gs = _
    rw [ht]; simp [tstepM]

theorem tabsM_getD_lt (gs : List Gate) (T : List ℕ) (i : ℕ) (hi : i < T.length) :
    (tabsM T gs).getD i 0 = T.getD i 0 := by
  obtain ⟨t, ht, _⟩ := tabsM_prefix gs T
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem tabsM_length (gs : List Gate) (T : List ℕ) :
    (tabsM T gs).length = T.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := tabsM_prefix gs T
  rw [ht, List.length_append, hl]

theorem gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (h : ∀ k (hk : k < l1.length), l1[k] ≤ l2[k]'(by omega)) :
    op.eval l1 ≤ op.eval l2 := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval]
    cases h1 : l1.all id with
    | false => simp
    | true =>
      have h2 : l2.all id = true := by
        rw [List.all_eq_true]
        intro b hb
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        have hk1 : k < l1.length := by omega
        have ha1 : l1[k] = true := List.all_eq_true.mp h1 l1[k] (List.getElem_mem hk1)
        have hle := h k hk1
        rw [ha1] at hle
        cases hb2 : l2[k] with
        | true => rfl
        | false => rw [hb2] at hle; exact absurd hle (by decide)
      simp [h2]
  · simp only [GateOp.eval]
    cases h1 : l1.any id with
    | false => simp
    | true =>
      have h2 : l2.any id = true := by
        obtain ⟨b, hb, hbt⟩ := List.any_eq_true.mp h1
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        have hle := h k hk
        rw [show l1[k] = true from hbt] at hle
        have hb2 : l2[k]'(by omega) = true := by
          cases hv : l2[k]'(by omega) with
          | true => rfl
          | false => rw [hv] at hle; exact absurd hle (by decide)
        exact List.any_eq_true.mpr ⟨l2[k]'(by omega), List.getElem_mem (by omega), hb2⟩
      simp [h2]

theorem wires_mono_avoid (B : ℕ → Prop) (gs : List Gate) :
    ∀ (x y : List Bool), x.length = y.length →
    (∀ g ∈ gs, GOkM g) →
    (∀ i, ¬ B i → x.getD i false ≤ y.getD i false) →
    (∀ (k : ℕ) (hk : k < gs.length), ¬ B (x.length + k) → ∀ i ∈ gs[k].inputs, ¬ B i) →
    ∀ i, ¬ B i →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false ≤
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) y).getD i false := by
  induction gs with
  | nil => intro x y _ _ hxy _ i hi; exact hxy i hi
  | cons g gs ih =>
    intro x y hlen hok hxy havoid i hi
    have hg : GOkM g := hok g (by simp)
    let x' := x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)]
    let y' := y ++ [g.op.eval (g.inputs.map fun j => y.getD j false)]
    apply ih x' y' (by simp [x', y', hlen]) (fun g' hg' => hok g' (by simp [hg']))
    · intro j hj
      by_cases hlt : j < x.length
      · have hlt' : j < y.length := by omega
        simp only [x', y', List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_append_left hlt']
        exact hxy j hj
      · by_cases heq : j = x.length
        · subst heq
          have hav : ∀ w ∈ g.inputs, ¬ B w := havoid 0 (by simp) (by simpa using hj)
          have hxa : x'.getD x.length false = g.op.eval (g.inputs.map fun j => x.getD j false) := by
            simp [x', List.getD_eq_getElem?_getD]
          have hya : y'.getD x.length false = g.op.eval (g.inputs.map fun j => y.getD j false) := by
            rw [hlen]; simp [y', List.getD_eq_getElem?_getD]
          rw [hxa, hya]
          refine gateOp_mono g.op hg.1 _ _ (by simp) ?_
          intro k hk
          simp only [List.length_map] at hk
          simp only [List.getElem_map]
          exact hxy g.inputs[k] (hav g.inputs[k] (List.getElem_mem hk))
        · have hgt : x.length < j := by omega
          have hxnone : x'[j]? = none := List.getElem?_eq_none (by simp [x']; omega)
          simp [List.getD_eq_getElem?_getD, hxnone]
    · intro k hk hnb w hw
      have hlen' : x'.length = x.length + 1 := by simp [x']
      have hk' : k + 1 < (g :: gs).length := by simp; omega
      have hnb' : ¬ B (x.length + (k + 1)) := by
        rw [hlen'] at hnb
        convert hnb using 2; omega
      exact havoid (k + 1) hk' hnb' w (by simpa using hw)
    · exact hi

theorem zcount_eq_zero (gs : List Gate) :
    ∀ T : List ℕ, zcount T gs = 0 →
    ∀ (k : ℕ) (hk : k < gs.length), gateHasZero (tabsM T (gs.take k)) gs[k] = false := by
  induction gs with
  | nil => intro T _ k hk; simp at hk
  | cons g gs ih =>
    intro T hz k hk
    simp only [zcount] at hz
    have hg0 : gateHasZero T g = false := by
      cases h : gateHasZero T g <;> simp [h] at hz ⊢
    have hgs0 : zcount (tstepM T g) gs = 0 := by simp [hg0] at hz; exact hz
    cases k with
    | zero => simpa [tabsM] using hg0
    | succ k' =>
      simpa [tabsM] using ih (tstepM T g) hgs0 k' (by simpa using hk)

theorem zcount_eq_one (gs : List Gate) :
    ∀ T : List ℕ, zcount T gs = 1 →
    ∃ (t : ℕ) (ht : t < gs.length),
      gateHasZero (tabsM T (gs.take t)) gs[t] = true ∧
      ∀ (k : ℕ) (hk : k < gs.length), k ≠ t → gateHasZero (tabsM T (gs.take k)) gs[k] = false := by
  induction gs with
  | nil => intro T hz; simp [zcount] at hz
  | cons g gs ih =>
    intro T hz
    simp only [zcount] at hz
    cases hg : gateHasZero T g with
    | true =>
      have hgs0 : zcount (tstepM T g) gs = 0 := by simp [hg] at hz; omega
      refine ⟨0, by simp, by simpa [tabsM] using hg, ?_⟩
      intro k hk hne
      cases k with
      | zero => exact absurd rfl hne
      | succ k' =>
        simpa [tabsM] using zcount_eq_zero gs (tstepM T g) hgs0 k' (by simpa using hk)
    | false =>
      have hgs1 : zcount (tstepM T g) gs = 1 := by simp [hg] at hz; exact hz
      obtain ⟨t', ht', htrue, hrest⟩ := ih (tstepM T g) hgs1
      refine ⟨t' + 1, by simp; omega, by simpa [tabsM] using htrue, ?_⟩
      intro k hk hne
      cases k with
      | zero => simpa [tabsM] using hg
      | succ k' =>
        simpa [tabsM] using hrest k' (by simpa using hk) (by omega)

theorem wit0_len : (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).length = 10 ∧ (oneEach (⟨1, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).length = 10 := by decide
theorem wit0_inp_le (i : ℕ) (hi : i ≠ 4) : (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).getD i false ≤ (oneEach (⟨1, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).getD i false := by
  by_cases hlt : i < 10
  · exact (show ∀ j : Fin 10, j.val ≠ 4 → (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).getD j.val false ≤ (oneEach (⟨1, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).getD j.val false by decide) ⟨i, hlt⟩ hi
  · have hx : (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)).getD i false = false := List.getD_eq_default _ false (by rw [wit0_len.1]; omega)
    rw [hx]; exact Bool.false_le _
theorem wit0_vals : (7586009 : ℕ).testBit (5 * 4 + 0) = true ∧ (7586009 : ℕ).testBit (5 * 1 + 0) = false := by decide
theorem wit0_zero : inputsN.getD 4 0 = 0 ∧ 4 < inputsN.length := by decide

theorem wit1_len : (oneEach (⟨0, by decide⟩ : Fin 5) (⟨3, by decide⟩ : Fin 5)).length = 10 ∧ (oneEach (⟨0, by decide⟩ : Fin 5) (⟨1, by decide⟩ : Fin 5)).length = 10 := by decide
theorem wit1_inp_le (i : ℕ) (hi : i ≠ 8) : (oneEach (⟨0, by decide⟩ : Fin 5) (⟨3, by decide⟩ : Fin 5)).getD i false ≤ (oneEach (⟨0, by decide⟩ : Fin 5) (⟨1, by decide⟩ : Fin 5)).getD i false := by
  by_cases hlt : i < 10
  · exact (show ∀ j : Fin 10, j.val ≠ 8 → (oneEach (⟨0, by decide⟩ : Fin 5) (⟨3, by decide⟩ : Fin 5)).getD j.val false ≤ (oneEach (⟨0, by decide⟩ : Fin 5) (⟨1, by decide⟩ : Fin 5)).getD j.val false by decide) ⟨i, hlt⟩ hi
  · have hx : (oneEach (⟨0, by decide⟩ : Fin 5) (⟨3, by decide⟩ : Fin 5)).getD i false = false := List.getD_eq_default _ false (by rw [wit1_len.1]; omega)
    rw [hx]; exact Bool.false_le _
theorem wit1_vals : (7586009 : ℕ).testBit (5 * 0 + 3) = true ∧ (7586009 : ℕ).testBit (5 * 0 + 1) = false := by decide
theorem wit1_zero : inputsN.getD 8 0 = 0 ∧ 8 < inputsN.length := by decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 5 => (7586009 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hok : ∀ g ∈ C.gates, GOkM g := hC
  let out := (tabsM inputsN C.gates).getD C.output 0
  have obs (p : Fin 16) : out.testBit p.val = targetNat.testBit p.val := by
    have hval := hrep (embedR ⟨p.val / 4, by omega⟩) (embedC ⟨p.val % 4, by omega⟩)
    unfold Circuit.eval Circuit.wires at hval
    rw [oneEachN_map p, wires_tabsM p C.gates inputsN hok, getD_map_testBitM] at hval
    dsimp only at hval
    rw [hval, proj_bit_eq p]
  have hout_eq : out = targetNat := by
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < 16
    · exact obs ⟨p, hp⟩
    · have h2 : 2 ^ 16 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
      have hT : targetNat.testBit p = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : targetNat < 2 ^ 16) h2)
      have hI : ∀ v ∈ inputsN, v.testBit p = false := fun v hv => Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (inputsN_lt v hv) h2)
      have hall := tabsM_bit_false p (by omega) C.gates inputsN hI
      have hout_f : out.testBit p = false := by
        dsimp [out]
        rw [List.getD_eq_getElem?_getD]
        cases hget : (tabsM inputsN C.gates)[C.output]? with
        | none => simp
        | some v => exact hall v (List.mem_of_getElem? hget)
      rw [hout_f, hT]
  have hz_ge : 2 ≤ zcount inputsN C.gates := by
    have hout_nz : out ≠ 0 := by rw [hout_eq]; decide
    have hno_wire : ∀ (w0 : ℕ) (B : ℕ → Prop) (x y : List Bool),
        x.length = 10 → y.length = 10 →
        C.eval x = true → C.eval y = false →
        (∀ i, ¬ B i → x.getD i false ≤ y.getD i false) →
        (∀ i, B i → (tabsM inputsN C.gates).getD i 0 = 0) →
        (∀ (k : ℕ) (hk : k < C.gates.length), ¬ B (10 + k) → ∀ i ∈ C.gates[k].inputs, ¬ B i) → False := by
      intro w0 B x y hlx hly hcx hcy hxy hB0 havoid
      by_cases hBo : B C.output
      · exact hout_nz (hB0 C.output hBo)
      · have hle := wires_mono_avoid B C.gates x y (by omega) hok hxy (by simpa [hlx] using havoid) C.output hBo
        change C.eval x ≤ C.eval y at hle
        rw [hcx, hcy] at hle; exact absurd hle (by decide)
    by_contra hlt
    have hcases : zcount inputsN C.gates = 0 ∨ zcount inputsN C.gates = 1 := by omega
    rcases hcases with hz0 | hz1
    · have hzg := zcount_eq_zero C.gates inputsN hz0
      refine hno_wire 4 (· = 4) (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)) (oneEach (⟨1, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)) wit0_len.1 wit0_len.2 ((hrep ⟨4, by decide⟩ ⟨0, by decide⟩).trans wit0_vals.1) ((hrep ⟨1, by decide⟩ ⟨0, by decide⟩).trans wit0_vals.2) wit0_inp_le ?_ ?_
      · rintro i rfl; rw [tabsM_getD_lt C.gates inputsN _ wit0_zero.2]; exact wit0_zero.1
      · intro k hk _ i hi heq; subst heq
        have hf := hzg k hk
        have hmem : gateHasZero (tabsM inputsN (C.gates.take k)) C.gates[k] = true := by
          refine List.any_eq_true.mpr ⟨_, hi, ?_⟩
          rw [tabsM_getD_lt _ inputsN _ wit0_zero.2, wit0_zero.1]; rfl
        rw [hmem] at hf; cases hf
    · obtain ⟨t, ht, hzt, hzrest⟩ := zcount_eq_one C.gates inputsN hz1
      by_cases hw0 : 4 ∈ C.gates[t].inputs
      · by_cases hw1 : 8 ∈ C.gates[t].inputs
        · have hgt_ok : GOkM C.gates[t] := hok C.gates[t] (List.getElem_mem ht)
          have hne01 : (4 : ℕ) ≠ 8 := by decide
          have hgt_zero : gtM C.gates[t].op (C.gates[t].inputs.map fun j => (tabsM inputsN (C.gates.take t)).getD j 0) = 0 := by
            rcases hgt_ok with ⟨hop, hlen⟩
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            cases hin : C.gates[t].inputs with
            | nil => simp [hin] at hw0
            | cons a rest =>
              cases rest with
              | nil => simp [hin] at hw0 hw1; exact absurd (hw0.trans hw1.symm) hne01
              | cons b rest2 =>
                cases rest2 with
                | nil =>
                  have ha0 : (tabsM inputsN (C.gates.take t)).getD a 0 = 0 := by
                    simp [hin] at hw0 hw1
                    rcases hw0 with rfl | rfl
                    · rw [tabsM_getD_lt _ inputsN _ wit0_zero.2]; exact wit0_zero.1
                    · rcases hw1 with rfl | h1'
                      · rw [tabsM_getD_lt _ inputsN _ wit1_zero.2]; exact wit1_zero.1
                      · exact absurd h1'.symm hne01
                  have hb0 : (tabsM inputsN (C.gates.take t)).getD b 0 = 0 := by
                    simp [hin] at hw0 hw1
                    rcases hw1 with rfl | rfl
                    · rcases hw0 with h0' | rfl
                      · exact absurd h0' hne01
                      · rw [tabsM_getD_lt _ inputsN _ wit0_zero.2]; exact wit0_zero.1
                    · rw [tabsM_getD_lt _ inputsN _ wit1_zero.2]; exact wit1_zero.1
                  rcases hop with hop | hop <;> (rw [hop]; simp only [List.map_cons, List.map_nil, gtM, ha0, hb0]; rfl)
                | cons c rest3 => simp [hin] at hlen
          have hwt_val : ∀ (m : ℕ), (tabsM inputsN (C.gates.take m)).getD (inputsN.length + t) 0 = 0 := by
            intro m
            by_cases hmt : m ≤ t
            · exact List.getD_eq_default _ 0 (by rw [tabsM_length, List.length_take]; omega)
            · have hsplit : C.gates.take m = C.gates.take t ++ [C.gates[t]] ++ (C.gates.take m).drop (t + 1) := by
                have h1 : C.gates.take m = (C.gates.take m).take (t + 1) ++ (C.gates.take m).drop (t + 1) := (List.take_append_drop (t + 1) _).symm
                have h2 : (C.gates.take m).take (t + 1) = C.gates.take (t + 1) := by rw [List.take_take, Nat.min_eq_left (by omega)]
                have h3 : C.gates.take (t + 1) = C.gates.take t ++ [C.gates[t]] := List.take_succ_eq_append_getElem ht
                conv_lhs => rw [h1, h2, h3]
              rw [hsplit, tabsM_append, tabsM_append]
              have hlen_t1 : inputsN.length + t < (tabsM (tabsM inputsN (C.gates.take t)) [C.gates[t]]).length := by
                rw [tabsM_length, tabsM_length, List.length_take]; simp; omega
              rw [tabsM_getD_lt _ _ _ hlen_t1]
              change (tabsM inputsN (C.gates.take t) ++ [gtM C.gates[t].op (C.gates[t].inputs.map fun j => (tabsM inputsN (C.gates.take t)).getD j 0)]).getD (inputsN.length + t) 0 = 0
              rw [hgt_zero, List.getD_eq_getElem?_getD]
              have hlt_eq : (tabsM inputsN (C.gates.take t)).length = inputsN.length + t := by
                rw [tabsM_length, List.length_take]; omega
              rw [← hlt_eq, List.getElem?_append_right (le_refl _), Nat.sub_self]; simp
          have hlenN : inputsN.length = 10 := by decide
          refine hno_wire 4 (fun i => i = 4 ∨ i = 10 + t) (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)) (oneEach (⟨1, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)) wit0_len.1 wit0_len.2 ((hrep ⟨4, by decide⟩ ⟨0, by decide⟩).trans wit0_vals.1) ((hrep ⟨1, by decide⟩ ⟨0, by decide⟩).trans wit0_vals.2) (fun i hi => wit0_inp_le i (fun e => hi (Or.inl e))) ?_ ?_
          · intro i hi; rcases hi with rfl | rfl
            · rw [tabsM_getD_lt C.gates inputsN _ wit0_zero.2]; exact wit0_zero.1
            · have h := hwt_val C.gates.length; rw [List.take_length, hlenN] at h; exact h
          · intro k hk hnb i hi hBi
            have hkt : k ≠ t := fun e => hnb (Or.inr (by omega))
            have hf := hzrest k hk hkt
            have hzi : (tabsM inputsN (C.gates.take k)).getD i 0 = 0 := by
              rcases hBi with rfl | rfl
              · rw [tabsM_getD_lt _ inputsN _ wit0_zero.2]; exact wit0_zero.1
              · have h := hwt_val k; rw [hlenN] at h; exact h
            have hmem : gateHasZero (tabsM inputsN (C.gates.take k)) C.gates[k] = true := by
              refine List.any_eq_true.mpr ⟨i, hi, by rw [hzi]; rfl⟩
            rw [hmem] at hf; cases hf
        · refine hno_wire 8 (· = 8) (oneEach (⟨0, by decide⟩ : Fin 5) (⟨3, by decide⟩ : Fin 5)) (oneEach (⟨0, by decide⟩ : Fin 5) (⟨1, by decide⟩ : Fin 5)) wit1_len.1 wit1_len.2 ((hrep ⟨0, by decide⟩ ⟨3, by decide⟩).trans wit1_vals.1) ((hrep ⟨0, by decide⟩ ⟨1, by decide⟩).trans wit1_vals.2) wit1_inp_le ?_ ?_
          · rintro i rfl; rw [tabsM_getD_lt C.gates inputsN _ wit1_zero.2]; exact wit1_zero.1
          · intro k hk _ i hi heq; subst heq
            by_cases hkt : k = t
            · subst hkt; exact hw1 hi
            · have hf := hzrest k hk hkt
              have hmem : gateHasZero (tabsM inputsN (C.gates.take k)) C.gates[k] = true := by
                refine List.any_eq_true.mpr ⟨_, hi, ?_⟩
                rw [tabsM_getD_lt _ inputsN _ wit1_zero.2, wit1_zero.1]; rfl
              rw [hmem] at hf; cases hf
      · refine hno_wire 4 (· = 4) (oneEach (⟨4, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)) (oneEach (⟨1, by decide⟩ : Fin 5) (⟨0, by decide⟩ : Fin 5)) wit0_len.1 wit0_len.2 ((hrep ⟨4, by decide⟩ ⟨0, by decide⟩).trans wit0_vals.1) ((hrep ⟨1, by decide⟩ ⟨0, by decide⟩).trans wit0_vals.2) wit0_inp_le ?_ ?_
        · rintro i rfl; rw [tabsM_getD_lt C.gates inputsN _ wit0_zero.2]; exact wit0_zero.1
        · intro k hk _ i hi heq; subst heq
          by_cases hkt : k = t
          · subst hkt; exact hw0 hi
          · have hf := hzrest k hk hkt
            have hmem : gateHasZero (tabsM inputsN (C.gates.take k)) C.gates[k] = true := by
              refine List.any_eq_true.mpr ⟨_, hi, ?_⟩
              rw [tabsM_getD_lt _ inputsN _ wit0_zero.2, wit0_zero.1]; rfl
            rw [hmem] at hf; cases hf
  have hc0 := fromTabsM_zcount out C.gates inputsN hok (getWireM _ C.output)
  rw [hout_eq] at hc0
  have hc1 : CanM targetNat (C.gates.length - zcount inputsN C.gates) inputs.toFinset :=
    proj_monoCM_free (fun w hw => inputsN_free w (List.mem_toFinset.mp hw)) hc0
  change C.gates.length ≤ _ at hs
  exact excluded (proj_padCM (show C.gates.length - zcount inputsN C.gates ≤ 8 by omega) hc1)

end PEqualNP.Outside.L_meta_9464_aux

theorem PEqualNP.Outside.L_meta_9464 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7586009 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_9464_aux.lower
