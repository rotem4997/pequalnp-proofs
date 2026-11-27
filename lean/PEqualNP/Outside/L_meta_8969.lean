import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8969_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev targetNat : ℕ := 13726
abbrev maskParam : ℕ := 13726
abbrev fullVal : ℕ := 0x359e359e359e359e359e359e359e
def bits : List ℕ := [1, 32, 64, 512, 2048, 16384, 32768]
def inputs : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

def forceNat {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) n

theorem forceNat_eq {α : Type} (n : ℕ) (k : ℕ → α) : forceNat n k = k n := by
  cases n <;> rfl

theorem nat_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

def forceListN {α : Type} (xs : List ℕ) (k : List ℕ → α) : α :=
  (List.rec (motive := fun _ => (List ℕ → α) → α)
    (fun k => k [])
    (fun w _ next k => forceNat w fun v => next fun r => k (v :: r)) xs) k

theorem forceListN_eq {α : Type} (xs : List ℕ) (k : List ℕ → α) : forceListN xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceNat w (fun v => forceListN ws (fun r => k (v :: r))) = k (w :: ws)
    rw [forceNat_eq]
    exact ih (fun r => k (w :: r))

def forceListP {α : Type} (xs : List (ℕ × ℕ)) (k : List (ℕ × ℕ) → α) : α :=
  (List.rec (motive := fun _ => (List (ℕ × ℕ) → α) → α)
    (fun k => k [])
    (fun p _ next k => forceNat p.1 fun a => forceNat p.2 fun b => next fun r => k ((a, b) :: r)) xs) k

theorem forceListP_eq {α : Type} (xs : List (ℕ × ℕ)) (k : List (ℕ × ℕ) → α) : forceListP xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons p ps ih =>
    change forceNat p.1 (fun a => forceNat p.2 (fun b => forceListP ps (fun r => k ((a, b) :: r)))) = k (p :: ps)
    rw [forceNat_eq, forceNat_eq]
    exact ih (fun r => k (p :: r))

def ofSortedF {α : Type} : ℕ → ℕ → List α → BinaryTree α × List α
  | 0, _, xs => (BinaryTree.nil, xs)
  | _ + 1, 0, xs => (BinaryTree.nil, xs)
  | d + 1, n + 1, xs =>
    forceNat (n >>> 1) fun ln =>
    match ofSortedF d ln xs with
    | (lt, []) => (lt, [])
    | (lt, v :: xs2) =>
      forceNat (n - ln) fun rn =>
      match ofSortedF d rn xs2 with
      | (rt, xs3) => (BinaryTree.node v lt rt, xs3)

def ofSorted {α : Type} (xs : List α) : BinaryTree α := (ofSortedF 16 xs.length xs).1

def unDeltaFlat (acc : ℕ) : List ℕ → List (ℕ × ℕ)
  | d :: h :: rest => forceNat (acc + d) fun v => (v, h) :: unDeltaFlat v rest
  | _ => []

def ofDeltaFlat (xs : List ℕ) : BinaryTree (ℕ × ℕ) := ofSorted (unDeltaFlat 0 xs)

def unDeltaZ (acc : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | d :: rest => forceNat (acc + d) fun v => (v, 0) :: unDeltaZ v rest

def ofDeltaZ (xs : List ℕ) : BinaryTree (ℕ × ℕ) := ofSorted (unDeltaZ 0 xs)

def unDeltaN (acc : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: rest => forceNat (acc + d) fun v => v :: unDeltaN v rest

def ofDeltaN (xs : List ℕ) : BinaryTree ℕ := ofSorted (unDeltaN 0 xs)

abbrev E : BinaryTree (ℕ × ℕ) := BinaryTree.nil
abbrev N (v h : ℕ) (l r : BinaryTree (ℕ × ℕ)) : BinaryTree (ℕ × ℕ) := BinaryTree.node (v, h) l r
abbrev L (v h : ℕ) : BinaryTree (ℕ × ℕ) := BinaryTree.node (v, h) BinaryTree.nil BinaryTree.nil

def InTree (x : ℕ) : BinaryTree (ℕ × ℕ) → Prop
  | BinaryTree.nil => False
  | BinaryTree.node vh l r => x = vh.1 ∨ InTree x l ∨ InTree x r

def treeMemGo (x : ℕ) : BinaryTree (ℕ × ℕ) → Bool
  | BinaryTree.nil => false
  | BinaryTree.node vh l r =>
    if Nat.beq x vh.1 then true
    else if Nat.ble vh.1 x then treeMemGo x r
    else treeMemGo x l

def treeMem (x : ℕ) (t : BinaryTree (ℕ × ℕ)) : Bool := forceNat x (fun x => treeMemGo x t)

theorem treeMemGo_imp {x : ℕ} : ∀ t : BinaryTree (ℕ × ℕ), treeMemGo x t = true → InTree x t
  | BinaryTree.nil, h => by simp [treeMemGo] at h
  | BinaryTree.node vh l r, h => by
    unfold treeMemGo at h
    by_cases h1 : Nat.beq x vh.1 = true
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : Nat.ble vh.1 x = true
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inr (treeMemGo_imp r h))
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inl (treeMemGo_imp l h))

theorem treeMem_imp {x : ℕ} (t : BinaryTree (ℕ × ℕ)) (h : treeMem x t = true) : InTree x t :=
  treeMemGo_imp t (by rw [treeMem, forceNat_eq] at h; exact h)

def checkTree (f : ℕ → ℕ → Bool) : BinaryTree (ℕ × ℕ) → Bool
  | BinaryTree.nil => true
  | BinaryTree.node vh l r => f vh.1 vh.2 && checkTree f l && checkTree f r

def chkRoot (f : ℕ → ℕ → Bool) : BinaryTree (ℕ × ℕ) → Bool
  | BinaryTree.node vh _ _ => f vh.1 vh.2
  | BinaryTree.nil => true

theorem checkTree_node {f : ℕ → ℕ → Bool} {v h : ℕ} {l r : BinaryTree (ℕ × ℕ)}
    (hv : f v h = true) (hl : checkTree f l = true) (hr : checkTree f r = true) :
    checkTree f (N v h l r) = true := by
  simp [checkTree, hv, hl, hr]

theorem checkTree_nodeR {f : ℕ → ℕ → Bool} {v h : ℕ} {l r : BinaryTree (ℕ × ℕ)}
    (hv : chkRoot f (N v h l r) = true) (hl : checkTree f l = true) (hr : checkTree f r = true) :
    checkTree f (N v h l r) = true :=
  checkTree_node hv hl hr

theorem checkTree_sound {f : ℕ → ℕ → Bool} :
    ∀ t : BinaryTree (ℕ × ℕ), checkTree f t = true → ∀ x, InTree x t → ∃ h, f x h = true
  | BinaryTree.nil, _, _, hx => hx.elim
  | BinaryTree.node vh l r, hc, x, hx => by
    simp only [checkTree, Bool.and_eq_true] at hc
    rcases hx with rfl | hl | hr
    · exact ⟨vh.2, hc.1.1⟩
    · exact checkTree_sound l hc.1.2 x hl
    · exact checkTree_sound r hc.2 x hr

abbrev E0 : BinaryTree ℕ := BinaryTree.nil
abbrev N0 (v : ℕ) (l r : BinaryTree ℕ) : BinaryTree ℕ := BinaryTree.node v l r

def InTree0 (x : ℕ) : BinaryTree ℕ → Prop
  | BinaryTree.nil => False
  | BinaryTree.node v l r => x = v ∨ InTree0 x l ∨ InTree0 x r

def treeMem0Go (x : ℕ) : BinaryTree ℕ → Bool
  | BinaryTree.nil => false
  | BinaryTree.node v l r =>
    if Nat.beq x v then true
    else if Nat.ble v x then treeMem0Go x r
    else treeMem0Go x l

def treeMem0 (x : ℕ) (t : BinaryTree ℕ) : Bool := forceNat x (fun x => treeMem0Go x t)

theorem treeMem0Go_imp {x : ℕ} : ∀ t : BinaryTree ℕ, treeMem0Go x t = true → InTree0 x t
  | BinaryTree.nil, h => by simp [treeMem0Go] at h
  | BinaryTree.node v l r, h => by
    unfold treeMem0Go at h
    by_cases h1 : Nat.beq x v = true
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : Nat.ble v x = true
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inr (treeMem0Go_imp r h))
      · simp only [h2, ↓reduceIte] at h
        exact Or.inr (Or.inl (treeMem0Go_imp l h))

theorem treeMem0_imp {x : ℕ} (t : BinaryTree ℕ) (h : treeMem0 x t = true) : InTree0 x t :=
  treeMem0Go_imp t (by rw [treeMem0, forceNat_eq] at h; exact h)

def checkTree0 (f : ℕ → Bool) : BinaryTree ℕ → Bool
  | BinaryTree.nil => true
  | BinaryTree.node v l r => f v && checkTree0 f l && checkTree0 f r

def chkRoot0 (f : ℕ → Bool) : BinaryTree ℕ → Bool
  | BinaryTree.node v _ _ => f v
  | BinaryTree.nil => true

theorem checkTree0_node {f : ℕ → Bool} {v : ℕ} {l r : BinaryTree ℕ}
    (hv : f v = true) (hl : checkTree0 f l = true) (hr : checkTree0 f r = true) :
    checkTree0 f (N0 v l r) = true := by
  simp [checkTree0, hv, hl, hr]

theorem checkTree0_nodeR {f : ℕ → Bool} {v : ℕ} {l r : BinaryTree ℕ}
    (hv : chkRoot0 f (N0 v l r) = true) (hl : checkTree0 f l = true) (hr : checkTree0 f r = true) :
    checkTree0 f (N0 v l r) = true :=
  checkTree0_node hv hl hr

theorem checkTree0_sound {f : ℕ → Bool} : ∀ t : BinaryTree ℕ, checkTree0 f t = true → ∀ x, InTree0 x t → f x = true
  | BinaryTree.nil, _, _, hx => hx.elim
  | BinaryTree.node v l r, hc, x, hx => by
    simp only [checkTree0, Bool.and_eq_true] at hc
    rcases hx with rfl | hl | hr
    · exact hc.1.1
    · exact checkTree0_sound l hc.1.2 x hl
    · exact checkTree0_sound r hc.2 x hr

def freeMD (top : ℕ) (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = top ∨ v ∈ S

abbrev freeM (S : Finset ℕ) (v : ℕ) : Prop := freeMD 65535 S v

def combM : Fin 2 → ℕ → ℕ → ℕ
  | 0, a, b => a &&& b
  | 1, a, b => a ||| b

theorem combM_comm (o : Fin 2) (a b : ℕ) : combM o a b = combM o b a := by
  fin_cases o
  · exact Nat.land_comm a b
  · exact Nat.lor_comm a b

theorem combM_and_distrib (dom : ℕ) (o : Fin 2) (a b : ℕ) :
    combM o a b &&& dom = combM o (a &&& dom) (b &&& dom) := by
  apply Nat.eq_of_testBit_eq; intro i
  fin_cases o <;> simp [combM, Nat.testBit_land, Nat.testBit_lor, Bool.and_or_distrib_right, Bool.and_assoc, Bool.and_left_comm]

def CanMD (top f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => freeMD top S f
  | k+1, S => ∃ (o : Fin 2) (a b : ℕ), freeMD top S a ∧ freeMD top S b ∧ CanMD top f k (insert (combM o a b) S)

abbrev CanM (f : ℕ) : ℕ → Finset ℕ → Prop := CanMD 65535 f

theorem freeMDMono {top v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : freeMD top S v) : freeMD top T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem freeMDSub {top : ℕ} {S T : Finset ℕ} (h : ∀ x ∈ S, freeMD top T x) {v : ℕ} (hv : freeMD top S v) : freeMD top T v := by
  rcases hv with rfl | rfl | hv
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact h v hv

theorem monoCMD_free {top f k : ℕ} {S T : Finset ℕ} (h : ∀ x ∈ S, freeMD top T x) (hc : CanMD top f k S) : CanMD top f k T := by
  induction k generalizing S T with
  | zero => exact freeMDSub h hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, a, b, freeMDSub h ha, freeMDSub h hb, ih ?_ hh⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · exact freeMDMono (Finset.subset_insert _ _) (h x hx)

theorem monoCMD {top f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : CanMD top f k S) : CanMD top f k T :=
  monoCMD_free (fun x hx => Or.inr (Or.inr (h hx))) hc

theorem stepUpMD {top f k : ℕ} {S : Finset ℕ} (hc : CanMD top f k S) : CanMD top f (k+1) S :=
  ⟨0, 0, 0, Or.inl rfl, Or.inl rfl, monoCMD (Finset.subset_insert _ _) hc⟩

theorem padCMD {top f k j : ℕ} {S : Finset ℕ} (hj : k ≤ j) (hc : CanMD top f k S) : CanMD top f j S := by
  induction hj with
  | refl => exact hc
  | step _ ih => exact stepUpMD ih

theorem smallMD {top f k : ℕ} {S : Finset ℕ} (hc : CanMD top f k S) :
    ∃ T ⊆ S, T.card ≤ k+1 ∧ CanMD top f k T := by
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
      have liftWire : ∀ w ∈ ({a, b} : Finset ℕ), freeMD top S w → freeMD top U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a, b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a, b} ∩ S) ⊆ {a, b})
      have htwo : ({a, b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U, hU, by dsimp [U]; omega, o, a, b, liftWire a (by simp) ha, liftWire b (by simp) hb, monoCMD ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hx⟩)))
    · refine ⟨T, ?_, by omega, stepUpMD hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem agreeMD {top f k a b : ℕ} {S : Finset ℕ} (htopb : top.testBit b = true) (hc : CanMD top f k S)
    (hs : ∀ v ∈ S, v.testBit a = true → v.testBit b = true) :
    f.testBit a = true → f.testBit b = true := by
  induction k generalizing S with
  | zero =>
    rcases hc with rfl | rfl | h
    · simp
    · intro _; exact htopb
    · exact hs _ h
  | succ k ih =>
    have w {v} (hv : freeMD top S v) : v.testBit a = true → v.testBit b = true := by
      rcases hv with rfl | rfl | h
      · simp
      · intro _; exact htopb
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

theorem agreeM {f k a b : ℕ} {S : Finset ℕ} (hb16 : b < 16) (hc : CanM f k S)
    (hs : ∀ v ∈ S, v.testBit a = true → v.testBit b = true) :
    f.testBit a = true → f.testBit b = true :=
  agreeMD ((show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨b, hb16⟩) hc hs

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
      · by_cases hx : x ∈ T
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

theorem cuts_nodup : ∀ (l : List ℕ) (k : ℕ) (U : List ℕ), l.Nodup → U ∈ cuts k l → U.Nodup
  | [], _, U, _, hU => by simp [cuts] at hU; subst hU; exact List.nodup_nil
  | z :: zs, k, U, hnd, hU => by
    obtain ⟨hz, hzs⟩ := List.nodup_cons.mp hnd
    unfold cuts at hU
    split at hU
    · simp at hU; subst hU; exact hnd
    · cases k with
      | zero => simp at hU; subst hU; exact List.nodup_nil
      | succ j =>
        simp only [List.mem_append, List.mem_map] at hU
        rcases hU with ⟨V, hV, rfl⟩ | hU
        · exact List.nodup_cons.mpr ⟨fun h => hz (cuts_mem_sub zs j V hV z h), cuts_nodup zs j V hzs hV⟩
        · exact cuts_nodup zs (j + 1) U hzs hU

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

theorem foldLor_append (f : ℕ → ℕ) : ∀ (a b : List ℕ), foldLor f (a ++ b) = foldLor f a ||| foldLor f b
  | [], b => by simp [foldLor]
  | x :: xs, b => by simp only [List.cons_append, foldLor_cons, foldLor_append f xs b, Nat.lor_assoc]

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

def zipN : List ℕ → List ℕ → List (ℕ × ℕ)
  | a :: as, b :: bs => (a, b) :: zipN as bs
  | _, _ => []

def sufOrs : List (ℕ × ℕ) → List ℕ
  | [] => [0]
  | (_, m) :: rest =>
    match sufOrs rest with
    | [] => [m]
    | s :: ss => forceNat (m ||| s) fun ms => ms :: s :: ss

def sufList (f : ℕ → ℕ) : List ℕ → List ℕ
  | [] => [0]
  | w :: rest => foldLor f (w :: rest) :: sufList f rest

theorem sufList_head_tail (f : ℕ → ℕ) (t : List ℕ) : sufList f t = foldLor f t :: (sufList f t).tail := by
  cases t <;> rfl

theorem sufOrs_eq (f : ℕ → ℕ) : ∀ l : List ℕ, sufOrs (l.map fun w => (w, f w)) = sufList f l
  | [] => rfl
  | w :: rest => by
    simp only [List.map_cons, sufOrs, sufOrs_eq f rest]
    rw [sufList_head_tail f rest]
    dsimp only
    rw [forceNat_eq, ← foldLor_cons, ← sufList_head_tail f rest]
    rfl

def cutsMP : ℕ → List (ℕ × ℕ) → List (List (ℕ × ℕ) × ℕ)
  | _, [] => [([], 0)]
  | k, (x, mx) :: xs =>
    if ((x, mx) :: xs).length ≤ k then
      [((x, mx) :: xs, ((x, mx) :: xs).foldl (fun a p => a ||| p.2) 0)]
    else
      match k with
      | 0 => [([], 0)]
      | j + 1 =>
        (cutsMP j xs).map (fun p => ((x, mx) :: p.1, mx ||| p.2)) ++ cutsMP (j + 1) xs
termination_by _ l => l.length

theorem cutsMP_spec (f : ℕ → ℕ) : ∀ (l : List ℕ) (k : ℕ) (U : List ℕ),
    U ∈ cuts k l → (U.map fun w => (w, f w), foldLor f U) ∈ cutsMP k (l.map fun x => (x, f x))
  | [], k, U, hU => by simp [cuts] at hU; subst hU; simp [cutsMP, foldLor]
  | x :: xs, k, U, hU => by
    unfold cuts at hU
    simp only [List.map_cons]
    unfold cutsMP
    have hlen : ((x, f x) :: xs.map fun y => (y, f y)).length ≤ k ↔ (x :: xs).length ≤ k := by simp
    by_cases hl : (x :: xs).length ≤ k
    · simp only [hl, ↓reduceIte, List.mem_singleton] at hU
      subst hU
      have hl' : ((x, f x) :: xs.map fun y => (y, f y)).length ≤ k := hlen.mpr hl
      simp only [hl', ↓reduceIte, List.mem_singleton, Prod.mk.injEq]
      exact ⟨rfl, by simp only [foldLor, List.foldl_cons, Nat.zero_or, List.foldl_map]⟩
    · simp only [hl, ↓reduceIte] at hU
      have hl' : ¬ ((x, f x) :: xs.map fun y => (y, f y)).length ≤ k := fun h => hl (hlen.mp h)
      simp only [hl', ↓reduceIte]
      cases k with
      | zero => simp at hU; subst hU; simp [foldLor]
      | succ j =>
        simp only [List.mem_append, List.mem_map] at hU ⊢
        rcases hU with ⟨V, hV, rfl⟩ | hU
        · left
          refine ⟨(V.map fun w => (w, f w), foldLor f V), cutsMP_spec f xs j V hV, ?_⟩
          simp [foldLor_cons]
        · right
          exact cutsMP_spec f xs (j + 1) U hU

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
  | [], k, U, hU => by simp [cuts] at hU; subst hU; simp [cutsM, foldLor]
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
      exact ⟨by simp [Function.comp_def], by simp only [foldLor, List.foldl_cons, Nat.zero_or, List.foldl_map]⟩
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
  | a :: b :: t => !(Nat.ble b a) && isStrict (b :: t)

theorem isStrict_gt : ∀ (a : ℕ) (t : List ℕ), isStrict (a :: t) = true → ∀ z ∈ t, a < z
  | _, [], _, _, hz => by simp at hz
  | a, b :: t, h, z, hz => by
    simp only [isStrict, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hab : a < b := by
      have hnot : ¬ (b ≤ a) := fun hle => by rw [Nat.ble_eq.mpr hle] at h; simp at h
      omega
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hab
    · exact Nat.lt_trans hab (isStrict_gt b t h.2 z hz)

theorem isStrict_nodup : ∀ (l : List ℕ), isStrict l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_singleton a
  | a :: b :: t, h => by
    have hgt := isStrict_gt a (b :: t) h
    simp only [isStrict, Bool.and_eq_true, Bool.not_eq_true'] at h
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

def memNat (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => if Nat.beq x y then true else memNat x ys

theorem memNat_iff (x : ℕ) : ∀ l : List ℕ, memNat x l = true ↔ x ∈ l
  | [] => by simp [memNat]
  | y :: ys => by
    unfold memNat
    by_cases h : Nat.beq x y = true
    · simp [h, Nat.eq_of_beq_eq_true h]
    · have hne : x ≠ y := fun he => h (he ▸ Nat.beq_refl x)
      simp only [h, Bool.false_eq_true, ↓reduceIte, memNat_iff x ys, List.mem_cons, hne, false_or]

def isInput (w : ℕ) : Bool :=
  Nat.beq w 15 || Nat.beq w 240 || Nat.beq w 3840 || Nat.beq w 61440 ||
  Nat.beq w 4369 || Nat.beq w 8738 || Nat.beq w 17476 || Nat.beq w 34952

theorem isInput_iff (w : ℕ) : isInput w = true ↔ w ∈ inputs := by
  simp only [isInput, inputs, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true, Nat.beq_eq]
  tauto

def countNonEss : List (ℕ × ℕ × Bool) → ℕ
  | [] => 0
  | (_, _, e) :: rest => (if e then 0 else 1) + countNonEss rest

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
    · have h1 := countNonEss_ge_one f e t y hyt hey; simp [hex]; omega
    · have h1 := countNonEss_ge_one f e t x hxt hex; simp [hey]; omega
    · have ih := countNonEss_ge_two f e t ht x y hxt hyt hxy hex hey; omega

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

def sepMD (Md : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | bitB :: rest, w => (if Nat.beq (w &&& bitB) 0 then w &&& Md else 0) ||| (sepMD Md rest w <<< 16)

def fullMD (Md : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: rest => Md ||| (fullMD Md rest <<< 16)

theorem sepMD_lt_bit_false (Md : ℕ) (hM : Md < 2 ^ 16) (bitB w i : ℕ) (hi : 16 ≤ i) :
    (if Nat.beq (w &&& bitB) 0 then w &&& Md else 0).testBit i = false := by
  split
  · have hlt : w &&& Md < 2 ^ 16 := Nat.and_lt_two_pow w hM
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hi))
  · simp

theorem coveredMD_sepMD {top Md k : ℕ} (hM : Md < 2 ^ 16) {U : List ℕ} (hc : CanMD top Md k U.toFinset) :
    ∀ (p0Bits : List ℕ), (∀ bitB ∈ p0Bits, ∃ b, bitB = 2 ^ b ∧ top.testBit b = true ∧ Md.testBit b = false) →
      foldLor (sepMD Md p0Bits) U = fullMD Md p0Bits
  | [], _ => by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [fullMD, Nat.zero_testBit]
    cases h : (foldLor (sepMD Md []) U).testBit i with
    | false => rfl
    | true =>
      obtain ⟨w, _, hw⟩ := (foldLor_testBit (sepMD Md []) i U).mp h
      simp [sepMD] at hw
  | bitB :: rest, hp0 => by
    obtain ⟨b, rfl, htopb, hMb⟩ := hp0 bitB (by simp)
    have hrest := coveredMD_sepMD hM hc rest (fun x hx => hp0 x (by simp [hx]))
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 16
    · have hsh : ∀ n : ℕ, (n <<< 16).testBit i = false := by
        intro n; rw [Nat.testBit_shiftLeft]; simp [show ¬ 16 ≤ i by omega]
      simp only [fullMD, Nat.testBit_lor, hsh, Bool.or_false]
      cases hMi : Md.testBit i with
      | false =>
        cases hL : (foldLor (sepMD Md (2 ^ b :: rest)) U).testBit i with
        | false => rfl
        | true =>
          obtain ⟨w, _, hw⟩ := (foldLor_testBit _ i U).mp hL
          simp only [sepMD, Nat.testBit_lor, hsh, Bool.or_false] at hw
          split at hw <;> simp [hMi] at hw
      | true =>
        cases hL : (foldLor (sepMD Md (2 ^ b :: rest)) U).testBit i with
        | true => rfl
        | false =>
          exfalso
          have hall : ∀ w ∈ U, w.testBit i = true → w.testBit b = true := by
            intro w hwU hwi
            by_contra hwb
            have hwb0 : w.testBit b = false := by cases hwv : w.testBit b <;> simp_all
            have hand0 : Nat.beq (w &&& 2 ^ b) 0 = true := by
              have hne := and_two_pow_ne_zero_iff w b
              rw [hwb0] at hne
              have heq : w &&& 2 ^ b = 0 := by simpa [bne] using hne
              rw [heq]; rfl
            have hbit : (sepMD Md (2 ^ b :: rest) w).testBit i = true := by
              simp [sepMD, hand0, hsh, hwi, hMi]
            have htrue := (foldLor_testBit (sepMD Md (2 ^ b :: rest)) i U).mpr ⟨w, hwU, hbit⟩
            rw [hL] at htrue; exact Bool.false_ne_true htrue
          have hMb' := agreeMD htopb hc (fun v hv => hall v (List.mem_toFinset.mp hv)) hMi
          rw [hMb] at hMb'; exact Bool.false_ne_true hMb'
    · have hge : 16 ≤ i := by omega
      have hM0 : Md.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) hge))
      have hR : (fullMD Md (2 ^ b :: rest)).testBit i = (fullMD Md rest).testBit (i - 16) := by
        simp [fullMD, hM0, Nat.testBit_shiftLeft, hge]
      rw [hR, ← hrest]
      cases h1 : (foldLor (sepMD Md rest) U).testBit (i - 16) with
      | true =>
        obtain ⟨w, hwU, hw⟩ := (foldLor_testBit _ (i - 16) U).mp h1
        apply (foldLor_testBit _ i U).mpr
        refine ⟨w, hwU, ?_⟩
        simp [sepMD, Nat.testBit_shiftLeft, hge, hw]
      | false =>
        cases h2 : (foldLor (sepMD Md (2 ^ b :: rest)) U).testBit i with
        | false => rfl
        | true =>
          obtain ⟨w, hwU, hw⟩ := (foldLor_testBit _ i U).mp h2
          simp only [sepMD, Nat.testBit_lor, sepMD_lt_bit_false Md hM (2 ^ b) w i hge, Bool.false_or,
            Nat.testBit_shiftLeft, hge, decide_true, Bool.true_and] at hw
          have ht := (foldLor_testBit _ (i - 16) U).mpr ⟨w, hwU, hw⟩
          rw [h1] at ht; exact absurd ht (by decide)

abbrev sepM := sepMD
abbrev fullM := fullMD

theorem coveredM_sepM {M k : ℕ} (hM : M < 2 ^ 16) {U : List ℕ} (hc : CanM M k U.toFinset)
    (p0Bits : List ℕ) (hp0 : ∀ bitB ∈ p0Bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ M.testBit b = false) :
    foldLor (sepM M p0Bits) U = fullM M p0Bits :=
  coveredMD_sepMD hM hc p0Bits (fun bitB h => by
    obtain ⟨b, rfl, hb16, hMb⟩ := hp0 bitB h
    exact ⟨b, rfl, (show ∀ j : Fin 16, (65535 : ℕ).testBit j.val = true by decide) ⟨b, hb16⟩, hMb⟩)

def insOneGo (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if Nat.beq x y then y :: ys else if Nat.ble y x then y :: insOneGo x ys else x :: y :: ys

def insOne (x : ℕ) (l : List ℕ) : List ℕ := forceNat x (fun x => insOneGo x l)

def sortU : List ℕ → List ℕ
  | [] => []
  | x :: xs => insOne x (sortU xs)

theorem mem_insOneGo (x z : ℕ) : ∀ l : List ℕ, z ∈ insOneGo x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insOneGo]
  | y :: ys => by
    unfold insOneGo
    by_cases h1 : Nat.beq x y = true
    · simp only [h1, ↓reduceIte]
      have hxy := Nat.eq_of_beq_eq_true h1; subst hxy; simp
    · simp only [h1, ↓reduceIte]
      by_cases h2 : Nat.ble y x = true
      · simp only [h2, ↓reduceIte]; simp [mem_insOneGo x z ys]; tauto
      · simp only [h2, ↓reduceIte]; simp

theorem mem_insOne (x z : ℕ) (l : List ℕ) : z ∈ insOne x l ↔ z = x ∨ z ∈ l := by
  rw [insOne, forceNat_eq]; exact mem_insOneGo x z l

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

def normListTop (top : ℕ) (U : List ℕ) : List ℕ :=
  sortU (U.filter (fun x => !(Nat.beq x 0) && !(Nat.beq x top)))

def packSetTop (top : ℕ) (U : List ℕ) : ℕ := pack (normListTop top U)

abbrev normList (U : List ℕ) : List ℕ := normListTop 65535 U
abbrev packSet (U : List ℕ) : ℕ := packSetTop 65535 U

theorem normListTop_bounds {top : ℕ} {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    ∀ x ∈ normListTop top U, 0 < x ∧ x < 65536 := by
  intro x hx
  rw [normListTop, mem_sortU, List.mem_filter] at hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
  have h0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hlt := hU x hx.1
  omega

theorem unpack_packSetTop {top : ℕ} {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    unpack (packSetTop top U) = normListTop top U :=
  unpack_pack (normListTop top U) (normListTop_bounds hU)

theorem freeMD_packSetTop {top : ℕ} {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    ∀ x ∈ U.toFinset, freeMD top (unpack (packSetTop top U)).toFinset x := by
  intro x hx
  have hxm := List.mem_toFinset.mp hx
  by_cases h0 : x = 0
  · exact Or.inl h0
  · by_cases h1 : x = top
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      rw [unpack_packSetTop hU, List.mem_toFinset, normListTop, mem_sortU, List.mem_filter]
      exact ⟨hxm, by simp [nat_beq_false h0, nat_beq_false h1]⟩

theorem unpack_packSet_sub {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) :
    (unpack (packSet U)).toFinset ⊆ U.toFinset := by
  intro x hx
  rw [unpack_packSetTop hU, List.mem_toFinset, normListTop, mem_sortU, List.mem_filter] at hx
  exact List.mem_toFinset.mpr hx.1

def opPairsM : List ℕ → List ℕ
  | [] => []
  | a :: t => t.flatMap (fun b => forceNat (a &&& b) fun v1 => forceNat (a ||| b) fun v2 => [v1, v2]) ++ opPairsM t

theorem mem_opPairsM : ∀ (w : List ℕ) (a b : ℕ), a ∈ w → b ∈ w →
    a &&& b ∈ w ++ opPairsM w ∧ a ||| b ∈ w ++ opPairsM w
  | [], _, _, ha, _ => by simp at ha
  | x :: t, a, b, ha, hb => by
    simp only [List.mem_cons] at ha hb
    simp only [opPairsM, forceNat_eq, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false]
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

def valsNewD (top : ℕ) (S : List ℕ) : List ℕ :=
  (opPairsM S).filter (fun v => !(Nat.beq v 0) && !(Nat.beq v top) && !(memNat v S))

abbrev valsNew (S : List ℕ) : List ℕ := valsNewD 65535 S

theorem opPairsM_lt : ∀ (S : List ℕ), (∀ x ∈ S, x < 65536) → ∀ v ∈ opPairsM S, v < 65536
  | [], _, _, hv => by simp [opPairsM] at hv
  | a :: t, hS, v, hv => by
    simp only [opPairsM, forceNat_eq, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hv
    have ha := hS a (by simp)
    rcases hv with ⟨b, hb, rfl | rfl⟩ | hv
    · exact Nat.and_lt_two_pow (n := 16) a (hS b (by simp [hb]))
    · exact Nat.or_lt_two_pow (n := 16) ha (hS b (by simp [hb]))
    · exact opPairsM_lt t (fun x hx => hS x (by simp [hx])) v hv

theorem or_top_of_sub {top x : ℕ} (hx : x &&& top = x) : x ||| top = top := by
  apply Nat.eq_of_testBit_eq; intro i
  have hxi := congrArg (fun n => n.testBit i) hx
  simp only [Nat.testBit_land, Nat.testBit_lor] at hxi ⊢
  cases ht : top.testBit i <;> cases hx0 : x.testBit i <;> simp_all

theorem and_65535_of_lt {x : ℕ} (hx : x < 65536) : x &&& 65535 = x := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hx

theorem combMD_case {top : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x &&& top = x) {o : Fin 2} {a b : ℕ}
    (ha : freeMD top S.toFinset a) (hb : freeMD top S.toFinset b) :
    freeMD top S.toFinset (combM o a b) ∨ combM o a b ∈ valsNewD top S := by
  have free_sub {w : ℕ} (hw : freeMD top S.toFinset w) : w &&& top = w := by
    rcases hw with rfl | hwt | h
    · simp
    · rw [hwt]; exact Nat.and_self top
    · exact hS w (List.mem_toFinset.mp h)
  rcases ha with rfl | hat | ha'
  · left; fin_cases o
    · simp only [combM, Nat.zero_and]; exact Or.inl rfl
    · simp only [combM, Nat.zero_or]; exact hb
  · left; rw [hat]; fin_cases o
    · simp only [combM, Nat.land_comm top, free_sub hb]; exact hb
    · simp only [combM, Nat.lor_comm top, or_top_of_sub (free_sub hb)]; exact Or.inr (Or.inl rfl)
  · rcases hb with rfl | hbt | hb'
    · left; fin_cases o
      · simp only [combM, Nat.and_zero]; exact Or.inl rfl
      · simp only [combM, Nat.or_zero]; exact Or.inr (Or.inr ha')
    · left; rw [hbt]; fin_cases o
      · simp only [combM, hS _ (List.mem_toFinset.mp ha')]; exact Or.inr (Or.inr ha')
      · simp only [combM, or_top_of_sub (hS _ (List.mem_toFinset.mp ha'))]; exact Or.inr (Or.inl rfl)
    · have haL := List.mem_toFinset.mp ha'
      have hbL := List.mem_toFinset.mp hb'
      have hpair := mem_opPairsM S a b haL hbL
      have hmem : combM o a b ∈ S ∨ combM o a b ∈ opPairsM S := by
        fin_cases o
        · exact List.mem_append.mp hpair.1
        · exact List.mem_append.mp hpair.2
      by_cases h0 : combM o a b = 0
      · exact Or.inl (Or.inl h0)
      · by_cases h1 : combM o a b = top
        · exact Or.inl (Or.inr (Or.inl h1))
        · by_cases hin : combM o a b ∈ S
          · exact Or.inl (Or.inr (Or.inr (List.mem_toFinset.mpr hin)))
          · right
            rcases hmem with h | hop
            · exact absurd h hin
            · simp only [valsNewD, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
              refine ⟨hop, ⟨?_, ?_⟩, ?_⟩
              · cases h : Nat.beq (combM o a b) 0 with
                | false => rfl
                | true => exact absurd (Nat.eq_of_beq_eq_true h) h0
              · cases h : Nat.beq (combM o a b) top with
                | false => rfl
                | true => exact absurd (Nat.eq_of_beq_eq_true h) h1
              · cases hc : memNat (combM o a b) S with
                | false => rfl
                | true => exact absurd ((memNat_iff _ _).mp hc) hin

theorem valsNewD_props {top : ℕ} {S : List ℕ} {v : ℕ} (hv : v ∈ valsNewD top S) :
    v ≠ 0 ∧ v ≠ top ∧ memNat v S = false ∧ v ∉ S := by
  simp only [valsNewD, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hv
  have h0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have h1 : v ≠ top := fun h => by rw [h] at hv; simp at hv
  have hnotS : v ∉ S := fun hm => by
    rw [(memNat_iff v S).mpr hm] at hv; exact absurd hv.2.2 (by decide)
  exact ⟨h0, h1, hv.2.2, hnotS⟩

theorem combM_new_other_mem {S : List ℕ} (hS : ∀ w ∈ S, w < 65536) {o : Fin 2} {x z : ℕ}
    (hx : x ∈ S) (hz : freeM S.toFinset z) (hnew : combM o x z ∈ valsNew S) :
    z ∈ S ∧ z ≠ x := by
  obtain ⟨h0, h1, _, hnotS⟩ := valsNewD_props hnew
  rcases hz with rfl | rfl | hz'
  · fin_cases o
    · simp only [combM, Nat.and_zero] at h0; exact absurd rfl h0
    · simp only [combM, Nat.or_zero] at hnotS; exact absurd hx hnotS
  · fin_cases o
    · simp only [combM, and_65535_of_lt (hS x hx)] at hnotS; exact absurd hx hnotS
    · simp only [combM, or_top_of_sub (and_65535_of_lt (hS x hx))] at h1; exact absurd rfl h1
  · refine ⟨List.mem_toFinset.mp hz', ?_⟩
    intro heq; subst heq
    fin_cases o
    · simp only [combM, Nat.and_self] at hnotS; exact absurd hx hnotS
    · simp only [combM, Nat.or_self] at hnotS; exact absurd hx hnotS

theorem combM_new_both_mem {S : List ℕ} (hS : ∀ w ∈ S, w < 65536) {o : Fin 2} {a b : ℕ}
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b) (hnew : combM o a b ∈ valsNew S) :
    a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  obtain ⟨h0, h1, _, hnotS⟩ := valsNewD_props hnew
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
    · simp only [combM, Nat.lor_comm 65535, or_top_of_sub (and_65535_of_lt (free_lt hb))] at h1; exact absurd rfl h1
  · have haS := List.mem_toFinset.mp ha'
    obtain ⟨hbS, hba⟩ := combM_new_other_mem hS haS hb hnew
    exact ⟨haS, hbS, Ne.symm hba⟩

theorem can1MD_case {top f : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x &&& top = x) (hc : CanMD top f 1 S.toFinset) :
    freeMD top S.toFinset f ∨ f ∈ valsNewD top S := by
  obtain ⟨o, a, b, ha, hb, h0⟩ := hc
  rcases h0 with rfl | rfl | hm
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · rcases Finset.mem_insert.mp hm with rfl | hf
    · exact combMD_case hS ha hb
    · exact Or.inl (Or.inr (Or.inr hf))

def checkCutsMD (top fullVal : ℕ) (nextTree : BinaryTree ℕ) (cs : List (List ℕ × ℕ)) : Bool :=
  cs.all fun p => !(Nat.beq p.2 fullVal) || treeMem0 (packSetTop top p.1) nextTree

def scanVsMD (top fullVal : ℕ) (nextTree : BinaryTree ℕ) (U' : List ℕ) (mU : ℕ) (vsM : List (ℕ × ℕ)) : Bool :=
  vsM.all fun q => !(Nat.beq (mU ||| q.2) fullVal) || treeMem0 (packSetTop top (q.1 :: U')) nextTree

def verifyNodeD (top Md fullVal k : ℕ) (bitsD : List ℕ) (nextTree : BinaryTree ℕ) (packedS : ℕ) : Bool :=
  forceListN (unpack packedS) fun S =>
  forceListP (S.map (fun w => (w, sepMD Md bitsD w))) fun SM =>
  S.all (fun w => Nat.beq (w &&& top) w) &&
  checkCutsMD top fullVal nextTree (cutsM (k + 1) SM) &&
  (forceListP ((valsNewD top S).map (fun v => (v, sepMD Md bitsD v))) fun vsM =>
   (cutsM k SM).all fun p => scanVsMD top fullVal nextTree p.1 p.2 vsM)

theorem checkCutsInitD_sound {top Md k : ℕ} {bitsD : List ℕ} {nextTree : BinaryTree ℕ} {l : List ℕ}
    (hl : ∀ x ∈ l, x < 65536) (hMd : Md < 2 ^ 16)
    (hbits : ∀ bitB ∈ bitsD, ∃ b, bitB = 2 ^ b ∧ top.testBit b = true ∧ Md.testBit b = false)
    (hchk : checkCutsMD top (fullMD Md bitsD) nextTree (cutsM (k + 1) (l.map fun w => (w, sepMD Md bitsD w))) = true)
    (hc : CanMD top Md k l.toFinset) :
    ∃ x, InTree0 x nextTree ∧ CanMD top Md k (unpack x).toFinset := by
  obtain ⟨T, hT, hn, ht⟩ := smallMD hc
  obtain ⟨U, hU, hu⟩ := cutsSpec (k + 1) l T hT hn
  have hcU := monoCMD hu ht
  have hmem := cutsM_spec (sepMD Md bitsD) l (k + 1) U hU
  have hcov := coveredMD_sepMD hMd hcU bitsD hbits
  have htest := List.all_eq_true.mp hchk (U, foldLor (sepMD Md bitsD) U) hmem
  simp only [hcov, Nat.beq_refl, Bool.not_true, Bool.false_or] at htest
  have hU_lt : ∀ x ∈ U, x < 65536 := fun x hx => hl x (cuts_mem_sub l (k + 1) U hU x hx)
  exact ⟨packSetTop top U, treeMem0_imp nextTree htest, monoCMD_free (freeMD_packSetTop hU_lt) hcU⟩

theorem advanceNodeD {top Md k : ℕ} {bitsD : List ℕ} {nextTree : BinaryTree ℕ} {packedS : ℕ}
    (hMd : Md < 2 ^ 16)
    (hbits : ∀ bitB ∈ bitsD, ∃ b, bitB = 2 ^ b ∧ top.testBit b = true ∧ Md.testBit b = false)
    (hv : verifyNodeD top Md (fullMD Md bitsD) k bitsD nextTree packedS = true)
    (hc : CanMD top Md (k + 1) (unpack packedS).toFinset) :
    ∃ x, InTree0 x nextTree ∧ CanMD top Md k (unpack x).toFinset := by
  unfold verifyNodeD at hv
  simp only [forceListN_eq, forceListP_eq, Bool.and_eq_true] at hv
  set S := unpack packedS with hS_def
  have hS_lt : ∀ x ∈ S, x < 65536 := unpack_lt packedS
  have hS_sub : ∀ x ∈ S, x &&& top = x := fun x hx => Nat.eq_of_beq_eq_true (List.all_eq_true.mp hv.1.1 x hx)
  obtain ⟨o, a, b, ha, hb, hh⟩ := hc
  rcases combMD_case hS_sub ha hb with hfree | hnew
  · have hh' : CanMD top Md k S.toFinset := by
      refine monoCMD_free (fun x hx => ?_) hh
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hfree
      · exact Or.inr (Or.inr hx)
    exact checkCutsInitD_sound hS_lt hMd hbits hv.1.2 hh'
  · obtain ⟨T, hT, hn, ht⟩ := smallMD hh
    by_cases hvT : combM o a b ∈ T
    · have hTe : T.erase (combM o a b) ⊆ S.toFinset := by
        intro y hy
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hy))).resolve_left (Finset.ne_of_mem_erase hy)
      have hcard : (T.erase (combM o a b)).card ≤ k := by rw [Finset.card_erase_of_mem hvT]; omega
      obtain ⟨U', hU', hu'⟩ := cutsSpec k S (T.erase (combM o a b)) hTe hcard
      have hsub : T ⊆ (combM o a b :: U').toFinset := by
        intro y hy
        by_cases ey : y = combM o a b
        · simp [ey]
        · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hu' (Finset.mem_erase.mpr ⟨ey, hy⟩))))
      have hcU := monoCMD hsub ht
      have hUmem := cutsM_spec (sepMD Md bitsD) S k U' hU'
      have hUchk := List.all_eq_true.mp hv.2 (U', foldLor (sepMD Md bitsD) U') hUmem
      have hvmem : (combM o a b, sepMD Md bitsD (combM o a b)) ∈ (valsNewD top S).map (fun v => (v, sepMD Md bitsD v)) :=
        List.mem_map.mpr ⟨combM o a b, hnew, rfl⟩
      have hvchk := List.all_eq_true.mp hUchk _ hvmem
      have hcov : foldLor (sepMD Md bitsD) U' ||| sepMD Md bitsD (combM o a b) = fullMD Md bitsD := by
        rw [Nat.lor_comm, ← foldLor_cons]; exact coveredMD_sepMD hMd hcU bitsD hbits
      simp only [hcov, Nat.beq_refl, Bool.not_true, Bool.false_or] at hvchk
      have hv_lt : combM o a b < 65536 := by
        simp only [valsNewD, List.mem_filter] at hnew
        exact opPairsM_lt S hS_lt _ hnew.1
      have hU_lt : ∀ x ∈ combM o a b :: U', x < 65536 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hv_lt
        · exact hS_lt x (cuts_mem_sub S k U' hU' x hx)
      exact ⟨packSetTop top (combM o a b :: U'), treeMem0_imp nextTree hvchk, monoCMD_free (freeMD_packSetTop hU_lt) hcU⟩
    · have hTS : T ⊆ S.toFinset := by
        intro y hy
        exact (Finset.mem_insert.mp (hT hy)).resolve_left (fun ey => hvT (ey ▸ hy))
      exact checkCutsInitD_sound hS_lt hMd hbits hv.1.2 (monoCMD hTS ht)

def PermOk (g : ℕ → ℕ) : Prop :=
  g 0 = 0 ∧ g 65535 = 65535 ∧ (∀ w, w < 65536 → g w < 65536) ∧
  (∀ o a b, g (combM o a b) = combM o (g a) (g b)) ∧
  (∀ a b, a < 65536 → b < 65536 → g a = g b → a = b)

theorem PermOk_id : PermOk id := ⟨rfl, rfl, fun _ h => h, fun _ _ _ => rfl, fun _ _ _ _ h => h⟩

theorem PermOk_comp {g1 g2 : ℕ → ℕ} (h1 : PermOk g1) (h2 : PermOk g2) : PermOk (fun w => g1 (g2 w)) :=
  ⟨by dsimp only; rw [h2.1, h1.1],
   by dsimp only; rw [h2.2.1, h1.2.1],
   fun w hw => h1.2.2.1 _ (h2.2.2.1 w hw),
   fun o a b => by dsimp only; rw [h2.2.2.2.1, h1.2.2.2.1],
   fun a b ha hb heq => h2.2.2.2.2 a b ha hb (h1.2.2.2.2 _ _ (h2.2.2.1 a ha) (h2.2.2.1 b hb) heq)⟩

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
    (hsurj : ∀ j : Fin 16, ∃ i : Fin 16, idx i.val = j.val)
    (htb : ∀ w i, (g w).testBit i = if i < 16 then w.testBit (idx i) else false) : PermOk g := by
  have h6 : ∀ j < 16, (65535 : ℕ).testBit j = true := fun j hj =>
    (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) ⟨j, hj⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
  · intro a b ha hb heq
    apply Nat.eq_of_testBit_eq; intro j
    by_cases hj : j < 16
    · obtain ⟨i, hi⟩ := hsurj ⟨j, hj⟩
      have htb_eq := congrArg (fun n => n.testBit i.val) heq
      simp only [htb, i.isLt, ↓reduceIte, hi] at htb_eq
      exact htb_eq
    · rw [testBit_mask_ge16 a j ha (by omega), testBit_mask_ge16 b j hb (by omega)]

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
  perm_ok_of_testBit transp16 (fun i => 4 * (i % 4) + i / 4) (fun i hi => by omega) (by decide) transp16_testBit

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

theorem rowPerm16_ok (r0 r1 r2 r3 : ℕ) (h0 : r0 ≤ 12) (h1 : r1 ≤ 12) (h2 : r2 ≤ 12) (h3 : r3 ≤ 12)
    (hsurj : ∀ j : Fin 16, ∃ i : Fin 16, (if i.val < 4 then r0 else if i.val < 8 then r1 else if i.val < 12 then r2 else r3) + i.val % 4 = j.val) :
    PermOk (rowPerm16 r0 r1 r2 r3) :=
  perm_ok_of_testBit _ _ (fun i hi => by split_ifs <;> omega) hsurj (rowPerm16_testBit r0 r1 r2 r3)

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

theorem colPerm16_ok (c0 c1 c2 c3 : ℕ) (h0 : c0 < 4) (h1 : c1 < 4) (h2 : c2 < 4) (h3 : c3 < 4)
    (hsurj : ∀ j : Fin 16, ∃ i : Fin 16, 4 * (i.val / 4) + (if i.val % 4 = 0 then c0 else if i.val % 4 = 1 then c1 else if i.val % 4 = 2 then c2 else c3) = j.val) :
    PermOk (colPerm16 c0 c1 c2 c3) :=
  perm_ok_of_testBit _ _ (fun i hi => by split_ifs <;> omega) hsurj (colPerm16_testBit c0 c1 c2 c3)

theorem canMD_permOk {g : ℕ → ℕ} (hg : PermOk g) {top f k : ℕ} {S : Finset ℕ}
    (hc : CanMD top f k S) : CanMD (g top) (g f) k (S.image g) := by
  have hfree {T : Finset ℕ} {v : ℕ} (hv : freeMD top T v) : freeMD (g top) (T.image g) (g v) := by
    rcases hv with rfl | rfl | h
    · exact Or.inl hg.1
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
  induction k generalizing S with
  | zero => exact hfree hc
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    refine ⟨o, g a, g b, hfree ha, hfree hb, ?_⟩
    have h' := ih hh
    rw [Finset.image_insert, hg.2.2.2.1] at h'
    exact h'

theorem inputs_lt : ∀ t ∈ inputs, t < 65536 := by decide
theorem inputs_nodup : inputs.Nodup := by decide
theorem targetNat_lt : targetNat < 2 ^ 16 := by decide

def permAut : ℕ → ℕ → ℕ
  | 0, w => w
  | 1, w => rowPerm16 0 4 12 8 (colPerm16 0 2 1 3 w)
  | 2, w => rowPerm16 0 8 4 12 (colPerm16 0 1 3 2 w)
  | 3, w => rowPerm16 0 8 12 4 (colPerm16 0 3 1 2 w)
  | 4, w => rowPerm16 0 12 4 8 (colPerm16 0 2 3 1 w)
  | 5, w => rowPerm16 0 12 8 4 (colPerm16 0 3 2 1 w)
  | 6, w => transp16 w
  | 7, w => transp16 (rowPerm16 0 4 12 8 (colPerm16 0 2 1 3 w))
  | 8, w => transp16 (rowPerm16 0 8 4 12 (colPerm16 0 1 3 2 w))
  | 9, w => transp16 (rowPerm16 0 8 12 4 (colPerm16 0 3 1 2 w))
  | 10, w => transp16 (rowPerm16 0 12 4 8 (colPerm16 0 2 3 1 w))
  | 11, w => transp16 (rowPerm16 0 12 8 4 (colPerm16 0 3 2 1 w))
  | _, w => w

theorem permAut_ok : ∀ idx, PermOk (permAut idx)
  | 0 => PermOk_id
  | 1 => by change PermOk (fun w => rowPerm16 0 4 12 8 (colPerm16 0 2 1 3 w)); exact PermOk_comp (rowPerm16_ok 0 4 12 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  | 2 => by change PermOk (fun w => rowPerm16 0 8 4 12 (colPerm16 0 1 3 2 w)); exact PermOk_comp (rowPerm16_ok 0 8 4 12 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  | 3 => by change PermOk (fun w => rowPerm16 0 8 12 4 (colPerm16 0 3 1 2 w)); exact PermOk_comp (rowPerm16_ok 0 8 12 4 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
  | 4 => by change PermOk (fun w => rowPerm16 0 12 4 8 (colPerm16 0 2 3 1 w)); exact PermOk_comp (rowPerm16_ok 0 12 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide))
  | 5 => by change PermOk (fun w => rowPerm16 0 12 8 4 (colPerm16 0 3 2 1 w)); exact PermOk_comp (rowPerm16_ok 0 12 8 4 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 3 2 1 (by decide) (by decide) (by decide) (by decide) (by decide))
  | 6 => by change PermOk (fun w => transp16 w); exact transp16_ok
  | 7 => by change PermOk (fun w => transp16 (rowPerm16 0 4 12 8 (colPerm16 0 2 1 3 w))); exact PermOk_comp (transp16_ok) (PermOk_comp (rowPerm16_ok 0 4 12 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide)))
  | 8 => by change PermOk (fun w => transp16 (rowPerm16 0 8 4 12 (colPerm16 0 1 3 2 w))); exact PermOk_comp (transp16_ok) (PermOk_comp (rowPerm16_ok 0 8 4 12 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)))
  | 9 => by change PermOk (fun w => transp16 (rowPerm16 0 8 12 4 (colPerm16 0 3 1 2 w))); exact PermOk_comp (transp16_ok) (PermOk_comp (rowPerm16_ok 0 8 12 4 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)))
  | 10 => by change PermOk (fun w => transp16 (rowPerm16 0 12 4 8 (colPerm16 0 2 3 1 w))); exact PermOk_comp (transp16_ok) (PermOk_comp (rowPerm16_ok 0 12 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)))
  | 11 => by change PermOk (fun w => transp16 (rowPerm16 0 12 8 4 (colPerm16 0 3 2 1 w))); exact PermOk_comp (transp16_ok) (PermOk_comp (rowPerm16_ok 0 12 8 4 (by decide) (by decide) (by decide) (by decide) (by decide)) (colPerm16_ok 0 3 2 1 (by decide) (by decide) (by decide) (by decide) (by decide)))
  | _ + 12 => PermOk_id

theorem permAut_fix : ∀ idx, permAut idx targetNat = targetNat
  | 0 => rfl
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | 3 => by decide +kernel
  | 4 => by decide +kernel
  | 5 => by decide +kernel
  | 6 => by decide +kernel
  | 7 => by decide +kernel
  | 8 => by decide +kernel
  | 9 => by decide +kernel
  | 10 => by decide +kernel
  | 11 => by decide +kernel
  | _ + 12 => rfl

theorem permAut_inputs_mem : ∀ idx, ∀ x ∈ inputs, permAut idx x ∈ inputs
  | 0 => fun _ hx => hx
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | 3 => by decide +kernel
  | 4 => by decide +kernel
  | 5 => by decide +kernel
  | 6 => by decide +kernel
  | 7 => by decide +kernel
  | 8 => by decide +kernel
  | 9 => by decide +kernel
  | 10 => by decide +kernel
  | 11 => by decide +kernel
  | _ + 12 => fun _ hx => hx

theorem permAut_inputs_eq (idx : ℕ) : inputs.toFinset.image (permAut idx) = inputs.toFinset := by
  have hsub : inputs.toFinset.image (permAut idx) ⊆ inputs.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact List.mem_toFinset.mpr (permAut_inputs_mem idx x (List.mem_toFinset.mp hx))
  have hinj : Set.InjOn (permAut idx) (inputs.toFinset : Set ℕ) := by
    intro a ha b hb heq
    exact (permAut_ok idx).2.2.2.2 a b (inputs_lt a (List.mem_toFinset.mp ha)) (inputs_lt b (List.mem_toFinset.mp hb)) heq
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])

theorem domLB_prep {dom Md fv kd : ℕ} {inps bits : List ℕ} {t0 : BinaryTree ℕ}
    (hfreeL : ∀ w ∈ inputs, w &&& dom = 0 ∨ w &&& dom = dom ∨ w &&& dom ∈ inps)
    (hmd : targetNat &&& dom = Md) (hltI : ∀ x ∈ inps, x < 65536) (hMd : Md < 2 ^ 16)
    (hfv : fv = fullMD Md bits)
    (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ dom.testBit b = true ∧ Md.testBit b = false)
    (hinit : checkCutsMD dom fv t0 (cutsM (kd + 1) (inps.map fun w => (w, sepMD Md bits w))) = true)
    (hc : CanMD dom (targetNat &&& dom) kd (inputs.toFinset.image (· &&& dom))) :
    ∃ x, InTree0 x t0 ∧ CanMD dom Md kd (unpack x).toFinset := by
  have hfreeI : ∀ x ∈ inputs.toFinset.image (· &&& dom), freeMD dom inps.toFinset x := by
    intro x hx; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact (hfreeL w (List.mem_toFinset.mp hw)).imp_right (Or.imp_right List.mem_toFinset.mpr)
  have hc' : CanMD dom Md kd inps.toFinset := by rw [← hmd]; exact monoCMD_free hfreeI hc
  rw [hfv] at hinit
  exact checkCutsInitD_sound hltI hMd hbits hinit hc'

theorem domLB_step {dom Md fv k : ℕ} {bits : List ℕ} {t1 t0 : BinaryTree ℕ}
    (hMd : Md < 2 ^ 16) (hfv : fv = fullMD Md bits)
    (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ dom.testBit b = true ∧ Md.testBit b = false)
    (hchk : checkTree0 (verifyNodeD dom Md fv k bits t0) t1 = true)
    {x : ℕ} (hx : InTree0 x t1) (hc : CanMD dom Md (k + 1) (unpack x).toFinset) :
    ∃ y, InTree0 y t0 ∧ CanMD dom Md k (unpack y).toFinset := by
  have h := checkTree0_sound t1 hchk x hx
  rw [hfv] at h
  exact advanceNodeD hMd hbits h hc

theorem domLB_base1 {dom Md : ℕ} {t1 : BinaryTree ℕ}
    (hchk : checkTree0 (fun x => let S := unpack x; S.all (fun w => w &&& dom == w) && Md != 0 && Md != dom && !S.contains Md && !(valsNewD dom S).contains Md) t1 = true)
    {x : ℕ} (hx : InTree0 x t1) (hc : CanMD dom Md 1 (unpack x).toFinset) : False := by
  have hb := checkTree0_sound t1 hchk x hx
  simp only [Bool.and_eq_true] at hb
  have hsub1 : ∀ w ∈ unpack x, w &&& dom = w := fun w hw => beq_iff_eq.mp (List.all_eq_true.mp hb.1.1.1.1 w hw)
  rcases can1MD_case hsub1 hc with hfree | hnew
  · rcases hfree with h0 | h1 | hm
    · simp [h0] at hb
    · simp [h1] at hb
    · simp [List.contains_iff_mem, List.mem_toFinset.mp hm] at hb
  · simp [List.contains_iff_mem, hnew] at hb

theorem domLB_base0 {dom Md : ℕ} {t0 : BinaryTree ℕ}
    (hchk : checkTree0 (fun x => Md != 0 && Md != dom && !(unpack x).contains Md) t0 = true)
    {x : ℕ} (hx : InTree0 x t0) (hc : CanMD dom Md 0 (unpack x).toFinset) : False := by
  have hb := checkTree0_sound t0 hchk x hx
  simp only [Bool.and_eq_true] at hb
  rcases hc with h0 | h1 | hm
  · simp [h0] at hb
  · simp [h1] at hb
  · simp [List.contains_iff_mem, List.mem_toFinset.mp hm] at hb

abbrev domR0 : ℕ := 65295
abbrev mdR0 : ℕ := 13582
abbrev fvR0 : ℕ := 0x350e350e350e350e350e
def bitsR0 : List ℕ := [1, 512, 2048, 16384, 32768]
def inpsR0 : List ℕ := [15, 3840, 4353, 8706, 17412, 34824, 61440]
def dR0_r1 : BinaryTree ℕ := E0
def dR0_r2 : BinaryTree ℕ := ofDeltaN [0xf4042f0a110f,34359214080]
def dR0_r3 : BinaryTree ℕ := ofDeltaN [0xf00044042f0a110f,34359214080,0x7fff800000000,0x3fbddfde20cfdf9,34359738360,0xcf7fffff108,34358820871,97848448323840,7696581394432,29695403884544,5497558138880,31894427140096,0x755f5e20cfdf1,0xcfffff1f10f,0x3fcc5021e011100,0x404000000000000]
def dR0_r4 : BinaryTree ℕ := ofDeltaN [0xf00044042202110f0f08,34359738360,0xcf7fffff108,34358820871,0x7f2f8000e0ef1,0xcfffff1f10f,0x43fc15021e011100,0x6fffffff3000000,218103808,0x1b02000000000000,0x4fffffff3000000,218103808,0x1d02000000000000,0x777f7ddfde20cfdf1,0xcfffff1f10f,0x3fbddfde1fefe070000,60129017849,0x7fff200000007,0xcf7fffff10efff9,0x5906110111000ef8,0xcfffff1f10f,917504,3825,513,284360718,23098552221696,0x6ffddfde20cfdf1,0xcfffff1f10f,23098619400448,0x1b01ddfdef0cfdf1,0xcfffff1f10f,0x500000000000000,0x1d01f300000e0ef1,0xcfffff1f10f,0x23f459061e011100,0x7320188f8dffdef00,0x3fc22021101020f0ef1,0xd0010f3020f,0x4b04150200000000,0x60f800000d000000,0x403ddfde20cfdf1,0xcfffff1f10f,0x4034ffff300000e0ef1,0xb000000000000000,0xcfffff1f10f]
def dR0_r5 : BinaryTree ℕ := ofDeltaN [0xf0004404220211010f08000f,60129017849,0x7fff200000007,0xcf7fffff10efff9,0x7f30000000ef10007,0x43fc22021101020f0ef1,0xcfffff1f10f,917504,3825,513,284360718,0x6fffffff2ffeefeef00,917504,3825,513,0xcfffff1ef0e,0x4404150211011100,0x1b01bbfbddfdef0cfdf1,0xcfffff1f10f,0x4fffffff30000000000,0xd0000000000,0x1d01fffff300000e0ef1,0xcfffff1f10f,0x777f7ddfde1fefdff0000,0x3fbddfdeefefdfef10efff9,0x6606110102010ef10007,60129542144,33623793,0xcfffff1fdfef10f,18696026259456,0x15020000000e0ef1,0xcfffff1f10f,0x6ffddfde1fefdff0000,0x2202110102010000,0x1b01ddfdeefefdff0000,0x22020000000000000000,0x23f466061101020f0ef1,0xcfffff1f10f,0x403540399f9e1fefdff0000,60129542144,33623793,0xd0010f2fffff10f,0x440415020000000e0ef1,0x6fffffffffffff1f10f,0x60f800000000000e0ef1,0xcfffff1f10f,0x403ddfde1fefdff0000,0x40350000000000000000000,0xb0000000000000000000]
def dR0_r6 : BinaryTree ℕ := ofDeltaN [0xf0004404220211010f00000f0008,0x44042202110102010ef10007,60129542144,33623793,0xcfffff1fdfef10f,18696026259456,0x6fffffff2ffeefefdff0000,0x44042202110102010000,0x1b01bbfbddfdeefefdff0000,0x220200000000000000000000,0x403bbfc00000000000000000000,0x67f844040000000000000000,0x4039807bbfc0000000000000000,0x67f800000000000000000000]
def dR0_r7 : BinaryTree ℕ := ofDeltaN [0xf00088084404220211010f00000f]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_init : checkCutsMD domR0 fvR0 dR0_r7 (cutsM 8 (inpsR0.map fun w => (w, sepMD mdR0 bitsR0 w))) = true := by decide +kernel
abbrev vfdR0_2 := verifyNodeD domR0 mdR0 fvR0 1 bitsR0 dR0_r1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_r2 : checkTree0 (vfdR0_2) dR0_r2 = true := by decide +kernel
abbrev vfdR0_3 := verifyNodeD domR0 mdR0 fvR0 2 bitsR0 dR0_r2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_r3 : checkTree0 (vfdR0_3) dR0_r3 = true := by decide +kernel
abbrev vfdR0_4 := verifyNodeD domR0 mdR0 fvR0 3 bitsR0 dR0_r3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_r4 : checkTree0 (vfdR0_4) dR0_r4 = true := by decide +kernel
abbrev vfdR0_5 := verifyNodeD domR0 mdR0 fvR0 4 bitsR0 dR0_r4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_r5 : checkTree0 (vfdR0_5) dR0_r5 = true := by decide +kernel
abbrev vfdR0_6 := verifyNodeD domR0 mdR0 fvR0 5 bitsR0 dR0_r5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_r6 : checkTree0 (vfdR0_6) dR0_r6 = true := by decide +kernel
abbrev vfdR0_7 := verifyNodeD domR0 mdR0 fvR0 6 bitsR0 dR0_r6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR0_r7 : checkTree0 (vfdR0_7) dR0_r7 = true := by decide +kernel
theorem fvR0_eq : fvR0 = fullMD mdR0 bitsR0 := by decide +kernel
theorem hbitsR0 : ∀ bitB ∈ bitsR0, ∃ b, bitB = 2 ^ b ∧ domR0.testBit b = true ∧ mdR0.testBit b = false := by
  intro bitB h; simp only [bitsR0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨9, rfl, by decide, by decide⟩
  · exact ⟨11, rfl, by decide, by decide⟩
  · exact ⟨14, rfl, by decide, by decide⟩
  · exact ⟨15, rfl, by decide, by decide⟩
theorem domLB_rep0 : ¬ CanMD domR0 (targetNat &&& domR0) 7 (inputs.toFinset.image (· &&& domR0)) := by
  intro hc
  obtain ⟨x7, hx7, c7⟩ := domLB_prep (by decide) (by decide) (by decide) (by decide) fvR0_eq hbitsR0 chkDR0_init hc
  obtain ⟨x6, hx6, c6⟩ := domLB_step (by decide) fvR0_eq hbitsR0 chkDR0_r7 hx7 c7
  obtain ⟨x5, hx5, c5⟩ := domLB_step (by decide) fvR0_eq hbitsR0 chkDR0_r6 hx6 c6
  obtain ⟨x4, hx4, c4⟩ := domLB_step (by decide) fvR0_eq hbitsR0 chkDR0_r5 hx5 c5
  obtain ⟨x3, hx3, c3⟩ := domLB_step (by decide) fvR0_eq hbitsR0 chkDR0_r4 hx4 c4
  obtain ⟨x2, hx2, c2⟩ := domLB_step (by decide) fvR0_eq hbitsR0 chkDR0_r3 hx3 c3
  obtain ⟨x1, hx1, c1⟩ := domLB_step (by decide) fvR0_eq hbitsR0 chkDR0_r2 hx2 c2
  exact hx1

abbrev domR1 : ℕ := 56589
abbrev mdR1 : ℕ := 5388
abbrev fvR1 : ℕ := 0x150c150c150c150c
def bitsR1 : List ℕ := [1, 2048, 16384, 32768]
def inpsR1 : List ℕ := [13, 3328, 4353, 17412, 34824, 53248]
def dR1_r1 : BinaryTree ℕ := E0
def dR1_r2 : BinaryTree ℕ := ofDeltaN [74784457625869,17626344782835,62656106398733,0xffff0000000,60455104609275,34359738360]
def dR1_r3 : BinaryTree ℕ := ofDeltaN [0x4404110d10080d00,0x440432f70cf8040d,0xffff40cfbf3,0x4ffeffffff2f30d,856051,0xffffff3f00d,0xafff000000c0cf3,0x4fffffffff3f30d,0x32f80000000c0cfb,34359738360,80248024007693,0x7b6fbcd08fbf3,0x3fbccfcfbf2f30c,524289,51539083259,0x76fb040d0cf8,5497558138880,855049229,69285557369843,0x744f4fbf2f30d,0x3fc3303040d0cf3,80282383746061,78047290653683,0x403700000000000,0x900000000000,0xf3b90432f7040d,0x7b6fbcd08fbf3,80282383746061]
def dR1_r4 : BinaryTree ℕ := ofDeltaN [0x8808440411000d00000d,55884909811,0xbf30100f30d,0xffff400fbff0000,0x4fff000000003000000,0xafffffffffffd000000,0x37f7ffffffffffffffff,524289,51539083259,0x7fff400000005,0x43fc3303040d0cf3,0x4fffffffff3f30d,786432,3315,1025,74784825606156,0x3f03bbfbcd08fbf3,0x777f7ccfcfbf2f30d,0x3fbccfcfbfef30cfffb,0x770704010cf30005,51539607552,67177715,56036439097344,0x4ffccfcfbf2f30d,56088045092864,0x3f03ccfcfbff0000,0x3f47707040d0cf3,0x403740388f8fbf2f30d,51539607552,67177715,0x440432f7000c0000,0x4fffffffff3f30d,0x42f80000000c0cf3,0x403ccfcfbf2f30d,0x4037000000000000000,0x9000000000000000,0xf3b4043303040d0cf3,0x4fffffffff3f30d,0x7b6fbccfcfbff0000,0x4904330304010000]
def dR1_r5 : BinaryTree ℕ := ofDeltaN [0x88084404110110000d00000d,0x47f7fffffffffcfff30cfffb,0x4404330304010cf30005,51539607552,67177715,0x4fffffffff3fbfef30d,0x4404330304010000,0x3f03bbfbccfcfbff0000,0x403bbfc0000000000000000,0x47f84404000000000000,0x403b807bbfc000000000000,0x47f80000000000000000,0x4f7b8080000000000000000]
def dR1_r6 : BinaryTree ℕ := ofDeltaN [0xd0008808440411010d00000d]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR1_init : checkCutsMD domR1 fvR1 dR1_r6 (cutsM 7 (inpsR1.map fun w => (w, sepMD mdR1 bitsR1 w))) = true := by decide +kernel
abbrev vfdR1_2 := verifyNodeD domR1 mdR1 fvR1 1 bitsR1 dR1_r1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR1_r2 : checkTree0 (vfdR1_2) dR1_r2 = true := by decide +kernel
abbrev vfdR1_3 := verifyNodeD domR1 mdR1 fvR1 2 bitsR1 dR1_r2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR1_r3 : checkTree0 (vfdR1_3) dR1_r3 = true := by decide +kernel
abbrev vfdR1_4 := verifyNodeD domR1 mdR1 fvR1 3 bitsR1 dR1_r3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR1_r4 : checkTree0 (vfdR1_4) dR1_r4 = true := by decide +kernel
abbrev vfdR1_5 := verifyNodeD domR1 mdR1 fvR1 4 bitsR1 dR1_r4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR1_r5 : checkTree0 (vfdR1_5) dR1_r5 = true := by decide +kernel
abbrev vfdR1_6 := verifyNodeD domR1 mdR1 fvR1 5 bitsR1 dR1_r5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR1_r6 : checkTree0 (vfdR1_6) dR1_r6 = true := by decide +kernel
theorem fvR1_eq : fvR1 = fullMD mdR1 bitsR1 := by decide +kernel
theorem hbitsR1 : ∀ bitB ∈ bitsR1, ∃ b, bitB = 2 ^ b ∧ domR1.testBit b = true ∧ mdR1.testBit b = false := by
  intro bitB h; simp only [bitsR1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨11, rfl, by decide, by decide⟩
  · exact ⟨14, rfl, by decide, by decide⟩
  · exact ⟨15, rfl, by decide, by decide⟩
theorem domLB_rep1 : ¬ CanMD domR1 (targetNat &&& domR1) 6 (inputs.toFinset.image (· &&& domR1)) := by
  intro hc
  obtain ⟨x6, hx6, c6⟩ := domLB_prep (by decide) (by decide) (by decide) (by decide) fvR1_eq hbitsR1 chkDR1_init hc
  obtain ⟨x5, hx5, c5⟩ := domLB_step (by decide) fvR1_eq hbitsR1 chkDR1_r6 hx6 c6
  obtain ⟨x4, hx4, c4⟩ := domLB_step (by decide) fvR1_eq hbitsR1 chkDR1_r5 hx5 c5
  obtain ⟨x3, hx3, c3⟩ := domLB_step (by decide) fvR1_eq hbitsR1 chkDR1_r4 hx4 c4
  obtain ⟨x2, hx2, c2⟩ := domLB_step (by decide) fvR1_eq hbitsR1 chkDR1_r3 hx3 c3
  obtain ⟨x1, hx1, c1⟩ := domLB_step (by decide) fvR1_eq hbitsR1 chkDR1_r2 hx2 c2
  exact hx1

abbrev domR2 : ℕ := 30471
abbrev mdR2 : ℕ := 13574
abbrev fvR2 : ℕ := 0x350635063506
def bitsR2 : List ℕ := [1, 512, 16384]
def inpsR2 : List ℕ := [7, 1792, 4353, 8706, 17412, 28672]
def dR2_r1 : BinaryTree ℕ := E0
def dR2_r2 : BinaryTree ℕ := ofDeltaN [0x740427021107]
def dR2_r3 : BinaryTree ℕ := ofDeltaN [0x7000440427021107,0x403ddfdea04f5f9,5497557743879,393216,1785,2561,284884998,31894511026176,48361331752960]
def dR2_r4 : BinaryTree ℕ := ofDeltaN [0x70004404220211070700,5497557743879,393216,1785,2561,284884998,0x403ddfde9fee4fdef00,25769803776,167839481,0x4fffff9f5fef907,18696160477184,0x1d020000000606f9,5497557743879,0x2bfbfb00000606f9,5497557743879]
def dR2_r5 : BinaryTree ℕ := ofDeltaN [0x700044042202110107000007,25769803776,167839481,0x4fffff9f5fef907,18696160477184,0x403fffffaffeefef5ff0000,0x2bfc0000000000000000]
def dR2_r6 : BinaryTree ℕ := ofDeltaN [0x700044042202110107000007]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR2_init : checkCutsMD domR2 fvR2 dR2_r6 (cutsM 7 (inpsR2.map fun w => (w, sepMD mdR2 bitsR2 w))) = true := by decide +kernel
abbrev vfdR2_2 := verifyNodeD domR2 mdR2 fvR2 1 bitsR2 dR2_r1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR2_r2 : checkTree0 (vfdR2_2) dR2_r2 = true := by decide +kernel
abbrev vfdR2_3 := verifyNodeD domR2 mdR2 fvR2 2 bitsR2 dR2_r2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR2_r3 : checkTree0 (vfdR2_3) dR2_r3 = true := by decide +kernel
abbrev vfdR2_4 := verifyNodeD domR2 mdR2 fvR2 3 bitsR2 dR2_r3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR2_r4 : checkTree0 (vfdR2_4) dR2_r4 = true := by decide +kernel
abbrev vfdR2_5 := verifyNodeD domR2 mdR2 fvR2 4 bitsR2 dR2_r4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR2_r5 : checkTree0 (vfdR2_5) dR2_r5 = true := by decide +kernel
abbrev vfdR2_6 := verifyNodeD domR2 mdR2 fvR2 5 bitsR2 dR2_r5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkDR2_r6 : checkTree0 (vfdR2_6) dR2_r6 = true := by decide +kernel
theorem fvR2_eq : fvR2 = fullMD mdR2 bitsR2 := by decide +kernel
theorem hbitsR2 : ∀ bitB ∈ bitsR2, ∃ b, bitB = 2 ^ b ∧ domR2.testBit b = true ∧ mdR2.testBit b = false := by
  intro bitB h; simp only [bitsR2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨9, rfl, by decide, by decide⟩
  · exact ⟨14, rfl, by decide, by decide⟩
theorem domLB_rep2 : ¬ CanMD domR2 (targetNat &&& domR2) 6 (inputs.toFinset.image (· &&& domR2)) := by
  intro hc
  obtain ⟨x6, hx6, c6⟩ := domLB_prep (by decide) (by decide) (by decide) (by decide) fvR2_eq hbitsR2 chkDR2_init hc
  obtain ⟨x5, hx5, c5⟩ := domLB_step (by decide) fvR2_eq hbitsR2 chkDR2_r6 hx6 c6
  obtain ⟨x4, hx4, c4⟩ := domLB_step (by decide) fvR2_eq hbitsR2 chkDR2_r5 hx5 c5
  obtain ⟨x3, hx3, c3⟩ := domLB_step (by decide) fvR2_eq hbitsR2 chkDR2_r4 hx4 c4
  obtain ⟨x2, hx2, c2⟩ := domLB_step (by decide) fvR2_eq hbitsR2 chkDR2_r3 hx3 c3
  obtain ⟨x1, hx1, c1⟩ := domLB_step (by decide) fvR2_eq hbitsR2 chkDR2_r2 hx2 c2
  exact hx1

def domMask : ℕ → ℕ
  | 0 => 65295
  | 1 => 61695
  | 2 => 4095
  | 3 => 56797
  | 4 => 48059
  | 5 => 30583
  | 6 => 30471
  | 7 => 45243
  | 8 => 3549
  | 9 => 56589
  | 10 => 47883
  | 11 => 53469
  | 12 => 3003
  | 13 => 28791
  | 14 => 1911
  | _ => 0

def domKd : ℕ → ℕ
  | 0 => 7
  | 1 => 7
  | 2 => 7
  | 3 => 7
  | 4 => 7
  | 5 => 7
  | 6 => 6
  | 7 => 6
  | 8 => 6
  | 9 => 6
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 6
  | 14 => 6
  | _ => 0

def domInps : ℕ → List ℕ
  | 0 => [15, 3840, 4353, 8706, 17412, 34824, 61440]
  | 1 => [15, 240, 4113, 8226, 16452, 32904, 61440]
  | 2 => [15, 240, 273, 546, 1092, 2184, 3840]
  | 3 => [13, 208, 3328, 4369, 17476, 34952, 53248]
  | 4 => [11, 176, 2816, 4369, 8738, 34952, 45056]
  | 5 => [7, 112, 1792, 4369, 8738, 17476, 28672]
  | 6 => [7, 1792, 4353, 8706, 17412, 28672]
  | 7 => [11, 176, 4113, 8226, 32904, 45056]
  | 8 => [13, 208, 273, 1092, 2184, 3328]
  | 9 => [13, 3328, 4353, 17412, 34824, 53248]
  | 10 => [11, 2816, 4353, 8706, 34824, 45056]
  | 11 => [13, 208, 4113, 16452, 32904, 53248]
  | 12 => [11, 176, 273, 546, 2184, 2816]
  | 13 => [7, 112, 4113, 8226, 16452, 28672]
  | 14 => [7, 112, 273, 546, 1092, 1792]
  | _ => []

theorem domMask_lt : ∀ d < 15, domMask d < 65536
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | _ + 15, h => by omega

theorem domInps_mem : (List.range 15).all (fun d => (domInps d).all (fun w => (inputs.map (· &&& domMask d)).contains w)) = true := by decide +kernel
theorem domInps_sound (d : ℕ) (hd : d < 15) (w : ℕ) (hw : w ∈ domInps d) : w ∈ inputs.toFinset.image (· &&& domMask d) := by
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp domInps_mem d (List.mem_range.mpr hd)) w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h1)
  exact Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, rfl⟩

theorem domTarget_nonconst : ∀ d < 15, targetNat &&& domMask d ≠ 0 ∧ targetNat &&& domMask d ≠ domMask d
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | _ + 15, h => by omega

theorem domLB_of_aut {dom repDom kd : ℕ} (ia : ℕ) (hd : permAut ia dom = repDom)
    (hrep : ¬ CanMD repDom (targetNat &&& repDom) kd (inputs.toFinset.image (· &&& repDom))) :
    ¬ CanMD dom (targetNat &&& dom) kd (inputs.toFinset.image (· &&& dom)) := by
  intro hc
  have h1 := canMD_permOk (permAut_ok ia) hc
  have hmd : permAut ia (targetNat &&& dom) = targetNat &&& repDom := by
    rw [show targetNat &&& dom = combM 0 targetNat dom from rfl, (permAut_ok ia).2.2.2.1 0 targetNat dom, permAut_fix ia, hd]; rfl
  have him : (inputs.toFinset.image (· &&& dom)).image (permAut ia) = inputs.toFinset.image (· &&& repDom) := by
    rw [Finset.image_image]
    have hfn : (permAut ia ∘ fun x => x &&& dom) = (fun x => x &&& repDom) ∘ permAut ia := by
      funext x; dsimp only [Function.comp_def]
      rw [show x &&& dom = combM 0 x dom from rfl, (permAut_ok ia).2.2.2.1 0 x dom, hd]; rfl
    rw [hfn, ← Finset.image_image, permAut_inputs_eq ia]
  rw [hd, hmd, him] at h1
  exact hrep h1

theorem domLB_all : ∀ d < 15, ¬ CanMD (domMask d) (targetNat &&& domMask d) (domKd d) (inputs.toFinset.image (· &&& domMask d))
  | 0, _ => domLB_rep0
  | 1, _ => domLB_of_aut 2 (by decide +kernel) domLB_rep0
  | 2, _ => domLB_of_aut 4 (by decide +kernel) domLB_rep0
  | 3, _ => domLB_of_aut 6 (by decide +kernel) domLB_rep0
  | 4, _ => domLB_of_aut 7 (by decide +kernel) domLB_rep0
  | 5, _ => domLB_of_aut 9 (by decide +kernel) domLB_rep0
  | 6, _ => domLB_rep2
  | 7, _ => domLB_of_aut 2 (by decide +kernel) domLB_rep2
  | 8, _ => domLB_of_aut 4 (by decide +kernel) domLB_rep2
  | 9, _ => domLB_rep1
  | 10, _ => domLB_of_aut 1 (by decide +kernel) domLB_rep1
  | 11, _ => domLB_of_aut 2 (by decide +kernel) domLB_rep1
  | 12, _ => domLB_of_aut 4 (by decide +kernel) domLB_rep1
  | 13, _ => domLB_of_aut 3 (by decide +kernel) domLB_rep1
  | 14, _ => domLB_of_aut 5 (by decide +kernel) domLB_rep1
  | _ + 15, h => by omega

def stepVal (st : Fin 2 × ℕ × ℕ) : ℕ := combM st.1 st.2.1 st.2.2
def stepAt (seq : List (Fin 2 × ℕ × ℕ)) (i : ℕ) : Fin 2 × ℕ × ℕ := seq.getD i (0, 0, 0)

def ValidSeq : Finset ℕ → List (Fin 2 × ℕ × ℕ) → Prop
  | _, [] => True
  | S, st :: rest => freeM S st.2.1 ∧ freeM S st.2.2 ∧ ValidSeq (insert (stepVal st) S) rest

def endSet : Finset ℕ → List (Fin 2 × ℕ × ℕ) → Finset ℕ
  | S, [] => S
  | S, st :: rest => endSet (insert (stepVal st) S) rest

def usedBy (q : List (Fin 2 × ℕ × ℕ)) : Finset ℕ :=
  (q.flatMap fun st => [st.2.1, st.2.2]).toFinset

def MinimalFor (f : ℕ) (S0 : Finset ℕ) (seq : List (Fin 2 × ℕ × ℕ)) : Prop :=
  ValidSeq S0 seq ∧ freeM (endSet S0 seq) f ∧
  ∀ seq', ValidSeq S0 seq' → freeM (endSet S0 seq') f → seq.length ≤ seq'.length

theorem canM_to_validSeq {f k : ℕ} {S : Finset ℕ} (hc : CanM f k S) :
    ∃ seq : List (Fin 2 × ℕ × ℕ), seq.length = k ∧ ValidSeq S seq ∧ freeM (endSet S seq) f := by
  induction k generalizing S with
  | zero => exact ⟨[], rfl, trivial, hc⟩
  | succ k ih =>
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    obtain ⟨seq, hl, hv, he⟩ := ih hh
    exact ⟨(o, a, b) :: seq, by simp [hl], ⟨ha, hb, hv⟩, he⟩

theorem validSeq_to_canM {f : ℕ} : ∀ (seq : List (Fin 2 × ℕ × ℕ)) (S : Finset ℕ),
    ValidSeq S seq → freeM (endSet S seq) f → CanM f seq.length S
  | [], _, _, he => he
  | (o, a, b) :: rest, S, ⟨ha, hb, hv⟩, he => ⟨o, a, b, ha, hb, validSeq_to_canM rest _ hv he⟩

theorem exists_minimal_seq {f K : ℕ} {S0 : Finset ℕ} (hc : CanM f K S0) :
    ∃ seq : List (Fin 2 × ℕ × ℕ), seq.length ≤ K ∧ MinimalFor f S0 seq := by
  classical
  have hex : ∃ n, ∃ seq : List (Fin 2 × ℕ × ℕ), seq.length = n ∧ ValidSeq S0 seq ∧ freeM (endSet S0 seq) f := by
    obtain ⟨seq, hl, hv, he⟩ := canM_to_validSeq hc
    exact ⟨K, seq, hl, hv, he⟩
  let n0 := Nat.find hex
  obtain ⟨seq, hl, hv, he⟩ := Nat.find_spec hex
  have hleK : n0 ≤ K := by
    apply Nat.find_min' hex
    exact canM_to_validSeq hc
  refine ⟨seq, by omega, hv, he, ?_⟩
  intro seq' hv' he'
  have hle := Nat.find_min' hex ⟨seq', rfl, hv', he'⟩
  omega

theorem endSet_append (S : Finset ℕ) : ∀ p q, endSet S (p ++ q) = endSet (endSet S p) q
  | [], _ => rfl
  | st :: p, q => endSet_append (insert (stepVal st) S) p q

theorem validSeq_append (S : Finset ℕ) : ∀ p q, ValidSeq S (p ++ q) ↔ ValidSeq S p ∧ ValidSeq (endSet S p) q
  | [], q => by simp [ValidSeq, endSet]
  | st :: p, q => by
    simp only [List.cons_append, ValidSeq, endSet, validSeq_append]
    tauto

theorem endSet_sub (S : Finset ℕ) : ∀ seq, S ⊆ endSet S seq
  | [] => Finset.Subset.refl _
  | st :: rest => Finset.Subset.trans (Finset.subset_insert _ _) (endSet_sub _ rest)

theorem endSet_lt : ∀ (seq : List (Fin 2 × ℕ × ℕ)) (S : Finset ℕ),
    (∀ x ∈ S, x < 65536) → ValidSeq S seq → ∀ x ∈ endSet S seq, x < 65536
  | [], _, hS, _, x, hx => hS x hx
  | (o, a, b) :: rest, S, hS, ⟨ha, hb, hv⟩, x, hx => by
    have flt {w : ℕ} (hw : freeM S w) : w < 65536 := by
      rcases hw with rfl | rfl | h
      · decide
      · decide
      · exact hS w h
    have hcab : combM o a b < 65536 := by
      fin_cases o
      · exact Nat.and_lt_two_pow (n := 16) a (flt hb)
      · exact Nat.or_lt_two_pow (n := 16) (flt ha) (flt hb)
    apply endSet_lt rest (insert (combM o a b) S) _ hv x hx
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hcab
    · exact hS y hy

theorem validSeq_mono_free : ∀ (seq : List (Fin 2 × ℕ × ℕ)) (S T : Finset ℕ),
    (∀ x ∈ S, freeM T x) → ValidSeq S seq →
    ValidSeq T seq ∧ (∀ x ∈ endSet S seq, freeM (endSet T seq) x)
  | [], S, T, h, _ => ⟨trivial, h⟩
  | st :: rest, S, T, h, ⟨ha, hb, hv⟩ => by
    have h1 : ∀ x ∈ insert (stepVal st) S, freeM (insert (stepVal st) T) x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
      · exact freeMDMono (Finset.subset_insert _ _) (h x hx)
    obtain ⟨hv', he'⟩ := validSeq_mono_free rest _ _ h1 hv
    exact ⟨⟨freeMDSub h ha, freeMDSub h hb, hv'⟩, he'⟩

theorem validSeq_erase (v : ℕ) : ∀ (q : List (Fin 2 × ℕ × ℕ)) (S : Finset ℕ),
    v ∉ usedBy q → ValidSeq (insert v S) q →
    ValidSeq S q ∧ (∀ x ∈ endSet (insert v S) q, x = v ∨ x ∈ endSet S q)
  | [], S, _, _ => ⟨trivial, fun x hx => Finset.mem_insert.mp hx⟩
  | st :: rest, S, hnu, ⟨ha, hb, hv⟩ => by
    have ha_ne : st.2.1 ≠ v := fun he => hnu (by simp [usedBy, he])
    have hb_ne : st.2.2 ≠ v := fun he => hnu (by simp [usedBy, he])
    have hnu_r : v ∉ usedBy rest := fun hr => hnu (by
      simp only [usedBy, List.mem_toFinset, List.flatMap_cons, List.mem_append] at hr ⊢
      exact Or.inr hr)
    have dropv {w : ℕ} (hne : w ≠ v) (hw : freeM (insert v S) w) : freeM S w := by
      rcases hw with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((Finset.mem_insert.mp h).resolve_left hne))
    have hswap : insert (stepVal st) (insert v S) = insert v (insert (stepVal st) S) := Finset.insert_comm _ _ _
    rw [hswap] at hv
    obtain ⟨hvr, her⟩ := validSeq_erase v rest (insert (stepVal st) S) hnu_r hv
    refine ⟨⟨dropv ha_ne ha, dropv hb_ne hb, hvr⟩, ?_⟩
    intro x hx
    simp only [endSet, hswap] at hx
    exact her x hx

theorem stepAt_eq_take_drop (seq : List (Fin 2 × ℕ × ℕ)) (m : ℕ) (hm : m < seq.length) :
    seq = seq.take m ++ [stepAt seq m] ++ seq.drop (m + 1) := by
  have hget : stepAt seq m = seq[m] := by
    simp only [stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  rw [hget]
  have h1 := List.take_append_drop m seq
  have h2 : seq.drop m = seq[m] :: seq.drop (m + 1) := List.drop_eq_getElem_cons hm
  rw [h2] at h1
  simpa [List.append_assoc] using h1.symm

theorem take_succ_stepAt (seq : List (Fin 2 × ℕ × ℕ)) (m : ℕ) (hm : m < seq.length) :
    seq.take (m + 1) = seq.take m ++ [stepAt seq m] := by
  have hget : stepAt seq m = seq[m] := by
    simp only [stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  rw [hget, List.take_succ_eq_append_getElem hm]

theorem mem_endSet_take_iff (S0 : Finset ℕ) (seq : List (Fin 2 × ℕ × ℕ)) (m : ℕ) (hm : m ≤ seq.length) (x : ℕ) :
    x ∈ endSet S0 (seq.take m) ↔ x ∈ S0 ∨ ∃ j < m, stepVal (stepAt seq j) = x := by
  induction m generalizing x with
  | zero => simp [endSet]
  | succ m ih =>
    rw [take_succ_stepAt seq m (by omega), endSet_append, endSet, endSet, Finset.mem_insert, ih (by omega)]
    constructor
    · rintro (rfl | h | ⟨j, hj, rfl⟩)
      · exact Or.inr ⟨m, by omega, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, rfl⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact Or.inr (Or.inl h)
      · by_cases ej : j = m
        · subst ej; exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨j, by omega, rfl⟩)

theorem minimal_new {f : ℕ} {S0 : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)} (hmin : MinimalFor f S0 seq)
    {m : ℕ} (hm : m < seq.length) :
    ¬ freeM (endSet S0 (seq.take m)) (stepVal (stepAt seq m)) := by
  intro hfree
  have hsplit := stepAt_eq_take_drop seq m hm
  have hv := hmin.1
  have he := hmin.2.1
  rw [hsplit, validSeq_append, validSeq_append] at hv
  rw [hsplit, endSet_append, endSet_append] at he
  simp only [ValidSeq, endSet, endSet_append] at hv he
  have hsub : ∀ x ∈ insert (stepVal (stepAt seq m)) (endSet S0 (seq.take m)), freeM (endSet S0 (seq.take m)) x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hfree
    · exact Or.inr (Or.inr hx)
  obtain ⟨hvq, heq⟩ := validSeq_mono_free (seq.drop (m + 1)) _ _ hsub hv.2
  have hv_short : ValidSeq S0 (seq.take m ++ seq.drop (m + 1)) := (validSeq_append S0 _ _).mpr ⟨hv.1.1, hvq⟩
  have he_short : freeM (endSet S0 (seq.take m ++ seq.drop (m + 1))) f := by
    rw [endSet_append]; exact freeMDSub heq he
  have hle := hmin.2.2 _ hv_short he_short
  simp only [List.length_append, List.length_take, List.length_drop] at hle
  omega

theorem minimal_distinct {f : ℕ} {S0 : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)} (hmin : MinimalFor f S0 seq)
    {i j : ℕ} (hi : i < j) (hj : j < seq.length) :
    stepVal (stepAt seq i) ≠ stepVal (stepAt seq j) := by
  intro heq
  apply minimal_new hmin hj
  rw [← heq]
  exact Or.inr (Or.inr ((mem_endSet_take_iff S0 seq j (by omega) _).mpr (Or.inr ⟨i, hi, rfl⟩)))

theorem minimal_no_early_target {f : ℕ} {S0 : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)} (hmin : MinimalFor f S0 seq)
    {m : ℕ} (hm : m < seq.length) (hlt : m + 1 < seq.length) :
    stepVal (stepAt seq m) ≠ f := by
  intro heq
  have hv : ValidSeq S0 (seq.take (m + 1)) := by
    have hs := hmin.1
    rw [← List.take_append_drop (m + 1) seq, validSeq_append] at hs
    exact hs.1
  have hf : freeM (endSet S0 (seq.take (m + 1))) f :=
    Or.inr (Or.inr ((mem_endSet_take_iff S0 seq (m + 1) (by omega) f).mpr (Or.inr ⟨m, by omega, heq⟩)))
  have hle := hmin.2.2 _ hv hf
  simp only [List.length_take] at hle
  omega

theorem minimal_used {f : ℕ} {S0 : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)} (hmin : MinimalFor f S0 seq)
    {m : ℕ} (hm : m < seq.length) (hne : stepVal (stepAt seq m) ≠ f) :
    stepVal (stepAt seq m) ∈ usedBy (seq.drop (m + 1)) := by
  by_contra hnu
  have hsplit := stepAt_eq_take_drop seq m hm
  have hv := hmin.1
  have he := hmin.2.1
  rw [hsplit, validSeq_append, validSeq_append] at hv
  rw [hsplit, endSet_append, endSet_append] at he
  simp only [ValidSeq, endSet, endSet_append] at hv he
  obtain ⟨hvq, heq⟩ := validSeq_erase (stepVal (stepAt seq m)) (seq.drop (m + 1)) (endSet S0 (seq.take m)) hnu hv.2
  have hv_short : ValidSeq S0 (seq.take m ++ seq.drop (m + 1)) := (validSeq_append S0 _ _).mpr ⟨hv.1.1, hvq⟩
  have he_short : freeM (endSet S0 (seq.take m ++ seq.drop (m + 1))) f := by
    rw [endSet_append]
    rcases he with rfl | rfl | hf
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rcases heq f hf with h1 | h2
      · exact absurd h1.symm hne
      · exact Or.inr (Or.inr h2)
  have hle := hmin.2.2 _ hv_short he_short
  simp only [List.length_append, List.length_take, List.length_drop] at hle
  omega

theorem usedBy_card_le (q : List (Fin 2 × ℕ × ℕ)) : (usedBy q).card ≤ 2 * q.length := by
  induction q with
  | nil => simp [usedBy]
  | cons st rest ih =>
    have heq : usedBy (st :: rest) = insert st.2.1 (insert st.2.2 (usedBy rest)) := by
      ext x; simp [usedBy]
    rw [heq, List.length_cons]
    have h1 := Finset.card_insert_le st.2.1 (insert st.2.2 (usedBy rest))
    have h2 := Finset.card_insert_le st.2.2 (usedBy rest)
    omega

theorem mem_usedBy_drop_iff (seq : List (Fin 2 × ℕ × ℕ)) (m : ℕ) (w : ℕ) :
    w ∈ usedBy (seq.drop m) ↔ ∃ j, m ≤ j ∧ j < seq.length ∧ ((stepAt seq j).2.1 = w ∨ (stepAt seq j).2.2 = w) := by
  simp only [usedBy, List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨st, hst, hw⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hst
    have hlen : m + k < seq.length := by simp only [List.length_drop] at hk; omega
    refine ⟨m + k, by omega, hlen, ?_⟩
    have hstep : stepAt seq (m + k) = st := by
      simp only [stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
      rw [← hget, List.getElem_drop]
    rw [hstep]; exact hw.imp Eq.symm Eq.symm
  · rintro ⟨j, hmj, hj, hw⟩
    have hk : j - m < (seq.drop m).length := by simp only [List.length_drop]; omega
    refine ⟨stepAt seq j, ?_, hw.imp Eq.symm Eq.symm⟩
    have hstep : stepAt seq j = (seq.drop m)[j - m] := by
      simp only [stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, List.getElem_drop]
      congr 1; omega
    rw [hstep]; exact List.getElem_mem hk

theorem usedWires_card {f : ℕ} {S0 : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)} (hmin : MinimalFor f S0 seq)
    {m r : ℕ} (hmr : m + r = seq.length) :
    (endSet S0 (seq.take m) ∩ usedBy (seq.drop m)).card ≤ r + 1 := by
  by_cases hr0 : r = 0
  · subst hr0
    have hdrop : seq.drop m = [] := List.drop_eq_nil_of_le (by omega)
    simp [hdrop, usedBy]
  · set T := endSet S0 (seq.take m) ∩ usedBy (seq.drop m)
    set I := (Finset.Ico m (seq.length - 1)).image (fun i => stepVal (stepAt seq i))
    have hIsub : I ⊆ usedBy (seq.drop m) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi1 : m ≤ i ∧ i < seq.length - 1 := Finset.mem_Ico.mp hi
      have hne := minimal_no_early_target hmin (m := i) (by omega) (by omega)
      have hu := minimal_used hmin (m := i) (by omega) hne
      rw [mem_usedBy_drop_iff] at hu ⊢
      obtain ⟨j, hj1, hj2, hread⟩ := hu
      exact ⟨j, by omega, hj2, hread⟩
    have hdisj : Disjoint T I := by
      rw [Finset.disjoint_left]
      intro x hxT hxI
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxI
      have hi1 : m ≤ i ∧ i < seq.length - 1 := Finset.mem_Ico.mp hi
      have hxSm : stepVal (stepAt seq i) ∈ endSet S0 (seq.take m) := (Finset.mem_inter.mp hxT).1
      have hxSi : stepVal (stepAt seq i) ∈ endSet S0 (seq.take i) := by
        have htk : seq.take i = seq.take m ++ (seq.take i).drop m := by
          have h1 := List.take_append_drop m (seq.take i)
          rw [List.take_take, Nat.min_eq_left hi1.1] at h1
          exact h1.symm
        rw [htk, endSet_append]
        exact endSet_sub _ _ hxSm
      exact minimal_new hmin (by omega) (Or.inr (Or.inr hxSi))
    have hIcard : I.card = r - 1 := by
      have hinj : Set.InjOn (fun i => stepVal (stepAt seq i)) (Finset.Ico m (seq.length - 1) : Set ℕ) := by
        intro a ha b hb heq
        have ha' := Finset.mem_Ico.mp ha
        have hb' := Finset.mem_Ico.mp hb
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact minimal_distinct hmin hlt (by omega) heq
        · exact minimal_distinct hmin hgt (by omega) heq.symm
      rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]; omega
    have hun : T ∪ I ⊆ usedBy (seq.drop m) := Finset.union_subset Finset.inter_subset_right hIsub
    have hle := Finset.card_le_card hun
    rw [Finset.card_union_of_disjoint hdisj, hIcard] at hle
    have h2r := usedBy_card_le (seq.drop m)
    simp only [List.length_drop] at h2r
    omega

theorem usedWires_canM {f : ℕ} {S0 : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)} (hmin : MinimalFor f S0 seq)
    {m r : ℕ} (hmr : m + r = seq.length) (hr : 1 ≤ r) :
    CanM f r (endSet S0 (seq.take m) ∩ usedBy (seq.drop m)) := by
  have haux : ∀ (q : List (Fin 2 × ℕ × ℕ)) (A B : Finset ℕ),
      ValidSeq A q → A ∩ usedBy q ⊆ B → ValidSeq B q ∧ (∀ x ∈ endSet A q, x ∈ A ∨ x ∈ endSet B q) := by
    intro q
    induction q with
    | nil => intro A B _ _; exact ⟨trivial, fun x hx => Or.inl hx⟩
    | cons st rest ih =>
      intro A B ⟨ha, hb, hv⟩ hsub
      have lift {w : ℕ} (hw : freeM A w) (hu : w ∈ usedBy (st :: rest)) : freeM B w := by
        rcases hw with rfl | rfl | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (hsub (Finset.mem_inter.mpr ⟨h, hu⟩)))
      have haB : freeM B st.2.1 := lift ha (by simp [usedBy])
      have hbB : freeM B st.2.2 := lift hb (by simp [usedBy])
      have hsub' : insert (stepVal st) A ∩ usedBy rest ⊆ insert (stepVal st) B := by
        intro x hx
        obtain ⟨hxA, hxU⟩ := Finset.mem_inter.mp hx
        rcases Finset.mem_insert.mp hxA with rfl | hxA
        · exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem (hsub (Finset.mem_inter.mpr ⟨hxA, ?_⟩))
          simp only [usedBy, List.mem_toFinset, List.flatMap_cons, List.mem_append] at hxU ⊢
          exact Or.inr hxU
      obtain ⟨hvr, her⟩ := ih (insert (stepVal st) A) (insert (stepVal st) B) hv hsub'
      refine ⟨⟨haB, hbB, hvr⟩, ?_⟩
      intro x hx
      rcases her x hx with hx1 | hx2
      · rcases Finset.mem_insert.mp hx1 with rfl | hxA
        · exact Or.inr (endSet_sub _ rest (Finset.mem_insert_self _ _))
        · exact Or.inl hxA
      · exact Or.inr hx2
  have hv0 := hmin.1
  have he0 := hmin.2.1
  rw [← List.take_append_drop m seq, validSeq_append] at hv0
  rw [← List.take_append_drop m seq, endSet_append] at he0
  obtain ⟨hvB, heB⟩ := haux (seq.drop m) (endSet S0 (seq.take m)) (endSet S0 (seq.take m) ∩ usedBy (seq.drop m)) hv0.2 (Finset.Subset.refl _)
  have hnf : ¬ freeM (endSet S0 (seq.take m)) f := by
    intro hf
    have hle := hmin.2.2 (seq.take m) hv0.1 hf
    simp only [List.length_take] at hle; omega
  have hfB : freeM (endSet (endSet S0 (seq.take m) ∩ usedBy (seq.drop m)) (seq.drop m)) f := by
    rcases he0 with rfl | rfl | hf
    · exact absurd (Or.inl rfl) hnf
    · exact absurd (Or.inr (Or.inl rfl)) hnf
    · rcases heB f hf with hA | hB
      · exact absurd (Or.inr (Or.inr hA)) hnf
      · exact Or.inr (Or.inr hB)
  have hcan := validSeq_to_canM (seq.drop m) _ hvB hfB
  have hlen : (seq.drop m).length = r := by simp only [List.length_drop]; omega
  rw [hlen] at hcan
  exact hcan

def isFreeAt (dom : ℕ) (S0 : Finset ℕ) (seq : List (Fin 2 × ℕ × ℕ)) (i : ℕ) : Prop :=
  (stepVal (stepAt seq i) &&& dom) = 0 ∨
  (stepVal (stepAt seq i) &&& dom) = dom ∨
  (stepVal (stepAt seq i) &&& dom) ∈ (endSet S0 (seq.take i)).image (· &&& dom)

instance instDecIsFreeAt (dom : ℕ) (S0 : Finset ℕ) (seq : List (Fin 2 × ℕ × ℕ)) (i : ℕ) :
    Decidable (isFreeAt dom S0 seq i) := by
  unfold isFreeAt; infer_instance

theorem canMD_of_validSeq {dom f : ℕ} (hdom : dom < 65536) :
    ∀ (seq : List (Fin 2 × ℕ × ℕ)) (S0 : Finset ℕ),
      ValidSeq S0 seq → freeM (endSet S0 seq) f →
      CanMD dom (f &&& dom) (seq.length - ((Finset.range seq.length).filter (isFreeAt dom S0 seq)).card) (S0.image (· &&& dom))
  | [], S0, _, hf => by
    simp only [List.length_nil, Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.sub_zero, CanMD]
    rcases hf with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by rw [Nat.land_comm, and_65535_of_lt hdom]))
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hm))
  | st :: rest, S0, ⟨ha, hb, hv⟩, he => by
    have ih := canMD_of_validSeq hdom rest (insert (stepVal st) S0) hv he
    set F := (Finset.range (st :: rest).length).filter (isFreeAt dom S0 (st :: rest))
    set F' := (Finset.range rest.length).filter (isFreeAt dom (insert (stepVal st) S0) rest)
    have hF'le : F'.card ≤ rest.length := by
      calc F'.card ≤ (Finset.range rest.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = rest.length := Finset.card_range _
    have hstep_succ : ∀ j, isFreeAt dom S0 (st :: rest) (j + 1) ↔ isFreeAt dom (insert (stepVal st) S0) rest j := by
      intro j; rfl
    have hF_split : F = (if isFreeAt dom S0 (st :: rest) 0 then {0} else ∅) ∪ F'.image Nat.succ := by
      ext i
      simp only [F, F', List.length_cons, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
      cases i with
      | zero =>
        by_cases h0 : isFreeAt dom S0 (st :: rest) 0 <;> simp [h0]
      | succ j =>
        have hne : j + 1 ≠ 0 := Nat.succ_ne_zero j
        by_cases h0 : isFreeAt dom S0 (st :: rest) 0
        · simp [h0, hne, hstep_succ]
        · simp [h0, hstep_succ]
    have hdisj : Disjoint (if isFreeAt dom S0 (st :: rest) 0 then ({0} : Finset ℕ) else ∅) (F'.image Nat.succ) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx2
      split_ifs at hx1 <;> simp at hx1
    have hFcard : F.card = (if isFreeAt dom S0 (st :: rest) 0 then 1 else 0) + F'.card := by
      rw [hF_split, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Nat.succ_injective]
      split_ifs <;> simp
    have hfree_map {w : ℕ} (hw : freeM S0 w) : freeMD dom (S0.image (· &&& dom)) (w &&& dom) := by
      rcases hw with rfl | rfl | hm
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (by rw [Nat.land_comm, and_65535_of_lt hdom]))
      · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hm))
    by_cases h0 : isFreeAt dom S0 (st :: rest) 0
    · have hlen_eq : (st :: rest).length - F.card = rest.length - F'.card := by
        simp only [List.length_cons, hFcard, h0, ↓reduceIte]; omega
      rw [hlen_eq]
      refine monoCMD_free (fun x hx => ?_) ih
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact h0
      · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hy))
    · have hlen_eq : (st :: rest).length - F.card = (rest.length - F'.card) + 1 := by
        simp only [List.length_cons, hFcard, h0, ↓reduceIte]; omega
      rw [hlen_eq]
      refine ⟨st.1, st.2.1 &&& dom, st.2.2 &&& dom, hfree_map ha, hfree_map hb, ?_⟩
      have him : insert (combM st.1 (st.2.1 &&& dom) (st.2.2 &&& dom)) (S0.image (· &&& dom)) =
          (insert (stepVal st) S0).image (· &&& dom) := by
        rw [Finset.image_insert, ← combM_and_distrib]; rfl
      rw [him]
      exact ih

def lossOnDomAux (dom : ℕ) (inpsDom : List ℕ) : List ℕ → List ℕ → ℕ → ℕ
  | [], _, loss => loss
  | w :: rest, seen, loss =>
    if isInput w then lossOnDomAux dom inpsDom rest seen loss
    else
      forceNat (w &&& dom) fun wd =>
      if Nat.beq wd 0 || Nat.beq wd dom || memNat wd inpsDom || memNat wd seen then
        lossOnDomAux dom inpsDom rest seen (loss + 1)
      else
        lossOnDomAux dom inpsDom rest (wd :: seen) loss

def lossOnDom (dom : ℕ) (inpsDom : List ℕ) (Sv : List ℕ) : ℕ :=
  lossOnDomAux dom inpsDom Sv [] 0

theorem lossOnDomAux_eq (dom : ℕ) (inpsDom : List ℕ) :
    ∀ (L seen : List ℕ) (acc : ℕ), L.Nodup →
      lossOnDomAux dom inpsDom L seen acc +
        (((L.toFinset \ inputs.toFinset).image (· &&& dom)) \ ({0, dom} ∪ inpsDom.toFinset ∪ seen.toFinset)).card
        = (L.toFinset \ inputs.toFinset).card + acc
  | [], seen, acc, _ => by simp [lossOnDomAux]
  | w :: rest, seen, acc, hnd => by
    obtain ⟨hw_nr, hnd_r⟩ := List.nodup_cons.mp hnd
    unfold lossOnDomAux
    simp only [forceNat_eq]
    by_cases hin : isInput w = true
    · simp only [hin, ↓reduceIte]
      have hwI : w ∈ inputs.toFinset := List.mem_toFinset.mpr ((isInput_iff w).mp hin)
      have heq : (w :: rest).toFinset \ inputs.toFinset = rest.toFinset \ inputs.toFinset := by
        ext x; simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hni⟩
          · exact absurd hwI hni
          · exact ⟨hx, hni⟩
        · rintro ⟨hx, hni⟩; exact ⟨Or.inr hx, hni⟩
      rw [heq]
      exact lossOnDomAux_eq dom inpsDom rest seen acc hnd_r
    · simp only [hin, Bool.false_eq_true, ↓reduceIte]
      have hwNI : w ∉ inputs.toFinset := fun hm => hin ((isInput_iff w).mpr (List.mem_toFinset.mp hm))
      have hwNR : w ∉ rest.toFinset \ inputs.toFinset := fun hm => hw_nr (List.mem_toFinset.mp (Finset.mem_sdiff.mp hm).1)
      have hnew_eq : (w :: rest).toFinset \ inputs.toFinset = insert w (rest.toFinset \ inputs.toFinset) := by
        ext x; simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hx, hni⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hx, hni⟩
        · rintro (rfl | ⟨hx, hni⟩)
          · exact ⟨Or.inl rfl, hwNI⟩
          · exact ⟨Or.inr hx, hni⟩
      have hnew_card : ((w :: rest).toFinset \ inputs.toFinset).card = (rest.toFinset \ inputs.toFinset).card + 1 := by
        rw [hnew_eq, Finset.card_insert_of_notMem hwNR]
      set wd := w &&& dom
      set B : Finset ℕ := {0, dom} ∪ inpsDom.toFinset ∪ seen.toFinset
      by_cases hcond : (Nat.beq wd 0 || Nat.beq wd dom || memNat wd inpsDom || memNat wd seen) = true
      · simp only [hcond, ↓reduceIte]
        have hwdB : wd ∈ B := by
          simp only [B, Bool.or_eq_true, Nat.beq_eq, memNat_iff, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, List.mem_toFinset] at hcond ⊢
          tauto
        have hval_eq : (((w :: rest).toFinset \ inputs.toFinset).image (· &&& dom)) \ B =
            ((rest.toFinset \ inputs.toFinset).image (· &&& dom)) \ B := by
          rw [hnew_eq, Finset.image_insert]
          ext y; simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, hnb⟩
            · exact absurd hwdB hnb
            · exact ⟨hy, hnb⟩
          · rintro ⟨hy, hnb⟩; exact ⟨Or.inr hy, hnb⟩
        have ih := lossOnDomAux_eq dom inpsDom rest seen (acc + 1) hnd_r
        dsimp only [B] at hval_eq
        rw [hval_eq, hnew_card]
        omega
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        have hwdNB : wd ∉ B := by
          intro hm
          apply hcond
          simp only [B, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset] at hm
          simp only [Bool.or_eq_true, Nat.beq_eq, memNat_iff]
          tauto
        have hB2 : {0, dom} ∪ inpsDom.toFinset ∪ (wd :: seen).toFinset = insert wd B := by
          ext y; simp only [B, List.toFinset_cons, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (((rfl | rfl) | h1) | (rfl | h2))
            · exact Or.inr (Or.inl (Or.inl (Or.inl rfl)))
            · exact Or.inr (Or.inl (Or.inl (Or.inr rfl)))
            · exact Or.inr (Or.inl (Or.inr h1))
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h2)
          · rintro (rfl | (((rfl | rfl) | h1) | h2))
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl (Or.inl (Or.inl rfl))
            · exact Or.inl (Or.inl (Or.inr rfl))
            · exact Or.inl (Or.inr h1)
            · exact Or.inr (Or.inr h2)
        have hval_eq : (((w :: rest).toFinset \ inputs.toFinset).image (· &&& dom)) \ B =
            insert wd (((rest.toFinset \ inputs.toFinset).image (· &&& dom)) \ ({0, dom} ∪ inpsDom.toFinset ∪ (wd :: seen).toFinset)) := by
          rw [hnew_eq, Finset.image_insert, show w &&& dom = wd from rfl, hB2]
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          by_cases ey : y = wd
          · subst ey; simp [hwdNB]
          · simp [ey]
        have hwdNI_val : wd ∉ ((rest.toFinset \ inputs.toFinset).image (· &&& dom)) \ ({0, dom} ∪ inpsDom.toFinset ∪ (wd :: seen).toFinset) := by
          simp
        have ih := lossOnDomAux_eq dom inpsDom rest (wd :: seen) acc hnd_r
        dsimp only [B] at hval_eq
        rw [hval_eq, Finset.card_insert_of_notMem hwdNI_val, hnew_card]
        omega

theorem prefix_free_ge_loss {dom m : ℕ} {inpsDom L : List ℕ} {seq : List (Fin 2 × ℕ × ℕ)}
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hm : m ≤ seq.length)
    (hinps : ∀ w ∈ inpsDom, w ∈ inputs.toFinset.image (· &&& dom))
    (hnd : L.Nodup) (hLsub : L.toFinset ⊆ endSet inputs.toFinset (seq.take m)) :
    lossOnDom dom inpsDom L ≤ ((Finset.range m).filter (isFreeAt dom inputs.toFinset seq)).card := by
  set Lnew := L.toFinset \ inputs.toFinset
  set V := (Lnew.image (· &&& dom)) \ ({0, dom} ∪ inpsDom.toFinset)
  have hloss_eq : lossOnDom dom inpsDom L + V.card = Lnew.card := by
    have h := lossOnDomAux_eq dom inpsDom L [] 0 hnd
    simpa [lossOnDom, Lnew, V] using h
  set J := (Finset.range m).filter (fun j => stepVal (stepAt seq j) ∈ Lnew)
  have hJcard : J.card = Lnew.card := by
    have him : J.image (fun j => stepVal (stepAt seq j)) = Lnew := by
      ext x
      simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨j, ⟨_, hj⟩, rfl⟩; exact hj
      · intro hx
        have hxS : x ∈ endSet inputs.toFinset (seq.take m) := hLsub (Finset.mem_sdiff.mp hx).1
        have hxNI : x ∉ inputs.toFinset := (Finset.mem_sdiff.mp hx).2
        rcases (mem_endSet_take_iff inputs.toFinset seq m hm x).mp hxS with hI | ⟨j, hj, rfl⟩
        · exact absurd hI hxNI
        · exact ⟨j, ⟨hj, hx⟩, rfl⟩
    have hinj : Set.InjOn (fun j => stepVal (stepAt seq j)) (J : Set ℕ) := by
      intro a ha b hb heq
      have ha' := (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      have hb' := (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact minimal_distinct hmin hlt (by omega) heq
      · exact minimal_distinct hmin hgt (by omega) heq.symm
    rw [← him, Finset.card_image_of_injOn hinj]
  set G := J.filter (fun j => ¬ isFreeAt dom inputs.toFinset seq j)
  set F := J.filter (fun j => isFreeAt dom inputs.toFinset seq j)
  have hG_le_V : G.card ≤ V.card := by
    apply Finset.card_le_card_of_injOn (fun j => stepVal (stepAt seq j) &&& dom)
    · intro j hj
      have hjJ := (Finset.mem_filter.mp hj).1
      have hnf := (Finset.mem_filter.mp hj).2
      have hjm := Finset.mem_range.mp (Finset.mem_filter.mp hjJ).1
      have hjL := (Finset.mem_filter.mp hjJ).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hjL, ?_⟩
      intro hbad
      apply hnf
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset] at hbad
      rcases hbad with (h0 | h1) | hi
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr ?_)
        have himI := hinps _ hi
        obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp himI
        exact Finset.mem_image.mpr ⟨u, endSet_sub _ _ hu, heu⟩
    · intro a ha b hb heq
      have haJ := (Finset.mem_filter.mp ha).1
      have hbJ := (Finset.mem_filter.mp hb).1
      have ham := Finset.mem_range.mp (Finset.mem_filter.mp haJ).1
      have hbm := Finset.mem_range.mp (Finset.mem_filter.mp hbJ).1
      have hna := (Finset.mem_filter.mp ha).2
      have hnb := (Finset.mem_filter.mp hb).2
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · apply hnb
        refine Or.inr (Or.inr (Finset.mem_image.mpr ⟨stepVal (stepAt seq a), ?_, heq⟩))
        exact (mem_endSet_take_iff inputs.toFinset seq b (by omega) _).mpr (Or.inr ⟨a, hlt, rfl⟩)
      · apply hna
        refine Or.inr (Or.inr (Finset.mem_image.mpr ⟨stepVal (stepAt seq b), ?_, heq.symm⟩))
        exact (mem_endSet_take_iff inputs.toFinset seq a (by omega) _).mpr (Or.inr ⟨b, hgt, rfl⟩)
  have hFG : F.card + G.card = J.card := by
    have hdj : Disjoint F G := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
    have hun : F ∪ G = J := by
      ext j; simp only [F, G, Finset.mem_union, Finset.mem_filter]
      by_cases h : isFreeAt dom inputs.toFinset seq j <;> simp [h]
    rw [← Finset.card_union_of_disjoint hdj, hun]
  have hFsub : F ⊆ (Finset.range m).filter (isFreeAt dom inputs.toFinset seq) := by
    intro j hj
    have hj1 := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj1.1).1, hj1.2⟩
  have hFle := Finset.card_le_card hFsub
  omega

theorem suffix_free_ge_nconst {dom m : ℕ} {Cw : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)}
    (hdom : dom < 65536) (hTnc : targetNat &&& dom ≠ 0 ∧ targetNat &&& dom ≠ dom)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hm : m ≤ seq.length)
    (hCw_sub : Cw ⊆ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m))
    (hCw_const : ∀ w ∈ Cw, w &&& dom = 0 ∨ w &&& dom = dom) :
    Cw.card ≤ ((Finset.Ico m seq.length).filter (isFreeAt dom inputs.toFinset seq)).card := by
  set isC : ℕ → Prop := fun w => w &&& dom = 0 ∨ w &&& dom = dom
  set Fc := (Finset.Ico m seq.length).filter (fun j => isC (stepVal (stepAt seq j)))
  set Fn := (Finset.Ico m seq.length).filter (fun j => ¬ isC (stepVal (stepAt seq j)) ∧
    (isC (stepAt seq j).2.1 ∨ isC (stepAt seq j).2.2))
  have hdisjF : Disjoint Fc Fn := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact (Finset.mem_filter.mp hj2).2.1 (Finset.mem_filter.mp hj1).2
  have hF_free : Fc ∪ Fn ⊆ (Finset.Ico m seq.length).filter (isFreeAt dom inputs.toFinset seq) := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1 | h2
    · obtain ⟨hjI, hjC⟩ := Finset.mem_filter.mp h1
      refine Finset.mem_filter.mpr ⟨hjI, ?_⟩
      rcases hjC with h0 | htop
      · exact Or.inl h0
      · exact Or.inr (Or.inl htop)
    · obtain ⟨hjI, _, hab⟩ := Finset.mem_filter.mp h2
      have hjm : j < seq.length := (Finset.mem_Ico.mp hjI).2
      have hv := hmin.1
      rw [stepAt_eq_take_drop seq j hjm, validSeq_append, validSeq_append] at hv
      simp only [ValidSeq] at hv
      obtain ⟨ha, hb, _⟩ := hv.1.2
      have hmap_free {w : ℕ} (hw : freeM (endSet inputs.toFinset (seq.take j)) w) :
          freeMD dom ((endSet inputs.toFinset (seq.take j)).image (· &&& dom)) (w &&& dom) := by
        rcases hw with rfl | rfl | hm'
        · exact Or.inl (by simp)
        · exact Or.inr (Or.inl (by rw [Nat.land_comm, and_65535_of_lt hdom]))
        · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hm'))
      have hcomb_const {o : Fin 2} {x y : ℕ} (hx : isC x) :
          combM o (x &&& dom) (y &&& dom) = 0 ∨ combM o (x &&& dom) (y &&& dom) = dom ∨
          combM o (x &&& dom) (y &&& dom) = y &&& dom := by
        have hy_sub : (y &&& dom) &&& dom = y &&& dom := by rw [Nat.land_assoc, Nat.and_self]
        rcases hx with h0 | htop
        · rw [h0]; fin_cases o
          · left; simp [combM]
          · right; right; simp [combM]
        · rw [htop]; fin_cases o
          · right; right; simp only [combM]; rw [Nat.land_comm, hy_sub]
          · right; left; simp only [combM]; rw [Nat.lor_comm, or_top_of_sub hy_sub]
      refine Finset.mem_filter.mpr ⟨hjI, ?_⟩
      unfold isFreeAt stepVal
      rw [combM_and_distrib]
      rcases hab with hca | hcb
      · rcases hcomb_const (o := (stepAt seq j).1) (y := (stepAt seq j).2.2) hca with h0 | htop | heq
        · exact Or.inl h0
        · exact Or.inr (Or.inl htop)
        · rw [heq]; exact hmap_free hb
      · rw [combM_comm]
        rcases hcomb_const (o := (stepAt seq j).1) (y := (stepAt seq j).2.1) hcb with h0 | htop | heq
        · exact Or.inl h0
        · exact Or.inr (Or.inl htop)
        · rw [heq]; exact hmap_free ha
  set Vconst := Cw ∪ Fc.image (fun j => stepVal (stepAt seq j))
  have hdisjV : Disjoint Cw (Fc.image (fun j => stepVal (stepAt seq j))) := by
    rw [Finset.disjoint_left]
    intro x hxC hxF
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxF
    have hjm := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
    have hxSm : stepVal (stepAt seq j) ∈ endSet inputs.toFinset (seq.take m) := (Finset.mem_inter.mp (hCw_sub hxC)).1
    have hxSj : stepVal (stepAt seq j) ∈ endSet inputs.toFinset (seq.take j) := by
      have htk : seq.take j = seq.take m ++ (seq.take j).drop m := by
        have h1 := List.take_append_drop m (seq.take j)
        rw [List.take_take, Nat.min_eq_left hjm.1] at h1
        exact h1.symm
      rw [htk, endSet_append]; exact endSet_sub _ _ hxSm
    exact minimal_new hmin hjm.2 (Or.inr (Or.inr hxSj))
  have hFcinj : Set.InjOn (fun j => stepVal (stepAt seq j)) (Fc : Set ℕ) := by
    intro a ha b hb heq
    have ham := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    have hbm := Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact minimal_distinct hmin hlt hbm.2 heq
    · exact minimal_distinct hmin hgt ham.2 heq.symm
  have hVcard : Vconst.card = Cw.card + Fc.card := by
    rw [Finset.card_union_of_disjoint hdisjV, Finset.card_image_of_injOn hFcinj]
  let slots : ℕ → Finset ℕ := fun j =>
    (if isC (stepAt seq j).2.1 then {(stepAt seq j).2.1} else ∅) ∪
    (if isC (stepAt seq j).2.2 then {(stepAt seq j).2.2} else ∅)
  have hVsub : Vconst ⊆ (Fc ∪ Fn).biUnion slots := by
    intro x hx
    have ⟨hxC, hxU⟩ : isC x ∧ x ∈ usedBy (seq.drop m) := by
      rcases Finset.mem_union.mp hx with h1 | h2
      · exact ⟨hCw_const x h1, (Finset.mem_inter.mp (hCw_sub h1)).2⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h2
        have him := Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1
        have hiC : isC (stepVal (stepAt seq i)) := (Finset.mem_filter.mp hi).2
        have hneT : stepVal (stepAt seq i) ≠ targetNat := by
          intro he; rw [he] at hiC; rcases hiC with h0 | h1
          · exact hTnc.1 h0
          · exact hTnc.2 h1
        have hu := minimal_used hmin him.2 hneT
        rw [mem_usedBy_drop_iff] at hu ⊢
        obtain ⟨j, hj1, hj2, hread⟩ := hu
        exact ⟨hiC, j, by omega, hj2, hread⟩
    obtain ⟨j, hjm, hjlen, hread⟩ := (mem_usedBy_drop_iff seq m x).mp hxU
    refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
    · by_cases hjC : isC (stepVal (stepAt seq j))
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hjm, hjlen⟩, hjC⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hjm, hjlen⟩, hjC, ?_⟩)
        rcases hread with ha | hb
        · left; rw [ha]; exact hxC
        · right; rw [hb]; exact hxC
    · simp only [slots, Finset.mem_union]
      rcases hread with ha | hb
      · left; rw [ha]; simp [hxC]
      · right; rw [hb]; simp [hxC]
  have hslot_c : ∀ j ∈ Fc, (slots j).card ≤ 2 := by
    intro j _
    calc (slots j).card
        ≤ (if isC (stepAt seq j).2.1 then ({(stepAt seq j).2.1} : Finset ℕ) else ∅).card +
          (if isC (stepAt seq j).2.2 then ({(stepAt seq j).2.2} : Finset ℕ) else ∅).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := by split_ifs <;> simp
  have hslot_n : ∀ j ∈ Fn, (slots j).card ≤ 1 := by
    intro j hj
    have hnotC : ¬ isC (stepVal (stepAt seq j)) := (Finset.mem_filter.mp hj).2.1
    by_cases ha : isC (stepAt seq j).2.1
    · by_cases hb : isC (stepAt seq j).2.2
      · exfalso; apply hnotC
        unfold isC stepVal
        rw [combM_and_distrib]
        generalize (stepAt seq j).1 = opj
        rcases ha with h0a | hta <;> rcases hb with h0b | htb
        · rw [h0a, h0b]; fin_cases opj <;> simp [combM]
        · rw [h0a, htb]; fin_cases opj <;> simp [combM]
        · rw [hta, h0b]; fin_cases opj <;> simp [combM]
        · rw [hta, htb]; fin_cases opj <;> simp [combM, Nat.and_self, Nat.or_self]
      · simp [slots, ha, hb]
    · by_cases hb : isC (stepAt seq j).2.2
      · simp [slots, ha, hb]
      · simp [slots, ha, hb]
  have hbi := Finset.card_le_card hVsub |>.trans Finset.card_biUnion_le
  rw [Finset.sum_union hdisjF] at hbi
  have hs1 : ∑ j ∈ Fc, (slots j).card ≤ ∑ _j ∈ Fc, 2 := Finset.sum_le_sum hslot_c
  have hs2 : ∑ j ∈ Fn, (slots j).card ≤ ∑ _j ∈ Fn, 1 := Finset.sum_le_sum hslot_n
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs1 hs2
  have hFl := Finset.card_le_card hF_free
  rw [Finset.card_union_of_disjoint hdisjF] at hFl
  omega

theorem budget_contradiction {d m : ℕ} {Sv : List ℕ} {Cw : Finset ℕ} {seq : List (Fin 2 × ℕ × ℕ)}
    (hd : d < 15) (hmin : MinimalFor targetNat inputs.toFinset seq) (hm : m ≤ seq.length)
    (hSv_nd : Sv.Nodup) (hSv_sub : Sv.toFinset ⊆ endSet inputs.toFinset (seq.take m))
    (hCw_sub : Cw ⊆ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m))
    (hCw_const : ∀ w ∈ Cw, w &&& domMask d = 0 ∨ w &&& domMask d = domMask d)
    (hgt : seq.length < domKd d + 1 + lossOnDom (domMask d) (domInps d) Sv + Cw.card) : False := by
  have hdom := domMask_lt d hd
  have h1 := prefix_free_ge_loss hmin hm (domInps_sound d hd) hSv_nd hSv_sub
  have h2 := suffix_free_ge_nconst hdom (domTarget_nonconst d hd) hmin hm hCw_sub hCw_const
  set Fpre := (Finset.range m).filter (isFreeAt (domMask d) inputs.toFinset seq)
  set Fsuf := (Finset.Ico m seq.length).filter (isFreeAt (domMask d) inputs.toFinset seq)
  set Fall := (Finset.range seq.length).filter (isFreeAt (domMask d) inputs.toFinset seq)
  have hdisj : Disjoint Fpre Fsuf := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1' := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
    have h2' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj2).1).1
    omega
  have hun : Fpre ∪ Fsuf ⊆ Fall := by
    intro j hj
    rcases Finset.mem_union.mp hj with h1' | h2'
    · obtain ⟨hjm, hfr⟩ := Finset.mem_filter.mp h1'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hjm; omega), hfr⟩
    · obtain ⟨hjm, hfr⟩ := Finset.mem_filter.mp h2'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hjm).2, hfr⟩
  have hsum_le : Fpre.card + Fsuf.card ≤ Fall.card := by
    rw [← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_card hun
  have hcan := canMD_of_validSeq hdom seq inputs.toFinset hmin.1 hmin.2.1
  have hle : seq.length - ((Finset.range seq.length).filter (isFreeAt (domMask d) inputs.toFinset seq)).card ≤ domKd d := by
    change seq.length - Fall.card ≤ domKd d
    omega
  exact domLB_all d hd (padCMD hle hcan)

def ReachMin (K r : ℕ) (S : Finset ℕ) : Prop :=
  ∃ (seq : List (Fin 2 × ℕ × ℕ)) (m : ℕ),
    seq.length ≤ K ∧
    MinimalFor targetNat inputs.toFinset seq ∧
    m + r = seq.length ∧
    S ⊆ endSet inputs.toFinset (seq.take m) ∧
    (endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)) ⊆ S

theorem reachMin_permAut {K r : ℕ} {S : Finset ℕ} (idx : ℕ) (hr : ReachMin K r S) :
    ReachMin K r (S.image (permAut idx)) := by
  obtain ⟨seq, m, hlenK, hmin, hmr, hSsub, hTsub⟩ := hr
  have hg := permAut_ok idx
  have hfix := permAut_fix idx
  have hinps := permAut_inputs_eq idx
  set g := permAut idx
  let mapSt : Fin 2 × ℕ × ℕ → Fin 2 × ℕ × ℕ := fun st => (st.1, g st.2.1, g st.2.2)
  set seq' := seq.map mapSt
  have hmap_end : ∀ (q : List (Fin 2 × ℕ × ℕ)) (A : Finset ℕ),
      endSet (A.image g) (q.map mapSt) = (endSet A q).image g := by
    intro q
    induction q with
    | nil => intro A; rfl
    | cons st rest ih =>
      intro A
      have hst : stepVal (mapSt st) = g (stepVal st) := (hg.2.2.2.1 st.1 st.2.1 st.2.2).symm
      simp only [List.map_cons, endSet]
      rw [hst, ← Finset.image_insert]
      exact ih (insert (stepVal st) A)
  have hmap_val : ∀ (q : List (Fin 2 × ℕ × ℕ)) (A : Finset ℕ),
      ValidSeq A q → ValidSeq (A.image g) (q.map mapSt) := by
    intro q
    induction q with
    | nil => intro A _; trivial
    | cons st rest ih =>
      intro A ⟨ha, hb, hv⟩
      have hfg {w : ℕ} (hw : freeM A w) : freeM (A.image g) (g w) := by
        rcases hw with rfl | rfl | hm
        · exact Or.inl hg.1
        · exact Or.inr (Or.inl hg.2.1)
        · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hm))
      have hst : stepVal (mapSt st) = g (stepVal st) := (hg.2.2.2.1 st.1 st.2.1 st.2.2).symm
      refine ⟨hfg ha, hfg hb, ?_⟩
      rw [hst, ← Finset.image_insert]
      exact ih _ hv
  have hmin' : MinimalFor targetNat inputs.toFinset seq' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hinps]; exact hmap_val seq inputs.toFinset hmin.1
    · rw [← hinps, hmap_end, ← hfix]
      rcases hmin.2.1 with h0 | h1 | hm
      · rw [h0]; exact Or.inl hg.1
      · rw [h1]; exact Or.inr (Or.inl hg.2.1)
      · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hm))
    · intro seq2 hv2 he2
      simpa [seq'] using hmin.2.2 seq2 hv2 he2
  have htk : seq'.take m = (seq.take m).map mapSt := List.map_take.symm
  have hdr : seq'.drop m = (seq.drop m).map mapSt := List.map_drop.symm
  have hend_m : endSet inputs.toFinset (seq'.take m) = (endSet inputs.toFinset (seq.take m)).image g := by
    rw [htk]; simpa only [hinps] using hmap_end (seq.take m) inputs.toFinset
  have hused_m : usedBy (seq'.drop m) = (usedBy (seq.drop m)).image g := by
    rw [hdr]
    ext y
    simp only [usedBy, List.mem_toFinset, List.mem_flatMap, List.mem_map, Finset.mem_image, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨st', ⟨st, hst, rfl⟩, hy⟩
      rcases hy with rfl | rfl
      · exact ⟨st.2.1, ⟨st, hst, Or.inl rfl⟩, rfl⟩
      · exact ⟨st.2.2, ⟨st, hst, Or.inr rfl⟩, rfl⟩
    · rintro ⟨x, ⟨st, hst, hx⟩, rfl⟩
      exact ⟨mapSt st, ⟨st, hst, rfl⟩, hx.imp (congrArg g) (congrArg g)⟩
  refine ⟨seq', m, by simpa [seq'] using hlenK, hmin', by simpa [seq'] using hmr, ?_, ?_⟩
  · rw [hend_m]; exact Finset.image_subset_image hSsub
  · rw [hend_m, hused_m]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_inter.mp hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hy2
    have hv_tk : ValidSeq inputs.toFinset (seq.take m) := by
      have hs := hmin.1; rw [← List.take_append_drop m seq, validSeq_append] at hs; exact hs.1
    have ha_lt : a < 65536 := endSet_lt (seq.take m) inputs.toFinset (fun x hx => inputs_lt x (List.mem_toFinset.mp hx)) hv_tk a ha
    have hb_lt : b < 65536 := by
      obtain ⟨j, hjm, hjlen, hread⟩ := (mem_usedBy_drop_iff seq m b).mp hb
      have hs := hmin.1; rw [stepAt_eq_take_drop seq j hjlen, validSeq_append, validSeq_append] at hs
      simp only [ValidSeq] at hs
      have hfree_b : freeM (endSet inputs.toFinset (seq.take j)) b := by
        rcases hread with h | h <;> rw [← h]
        · exact hs.1.2.1
        · exact hs.1.2.2.1
      rcases hfree_b with rfl | rfl | hm'
      · decide
      · decide
      · exact endSet_lt (seq.take j) inputs.toFinset (fun x hx => inputs_lt x (List.mem_toFinset.mp hx)) hs.1.1 b hm'
    have hab : b = a := hg.2.2.2.2 b a hb_lt ha_lt hba
    subst hab
    exact Finset.mem_image_of_mem g (hTsub (Finset.mem_inter.mpr ⟨ha, hb⟩))

def essConstGo (dom fullVal forcedV : ℕ) (preOr : ℕ) : List (ℕ × ℕ) → List ℕ → ℕ
  | [], _ => 0
  | (w, mw) :: rest, suf :: sufs =>
    forceNat (w &&& dom) fun wd =>
    let add :=
      if Nat.beq wd 0 || Nat.beq wd dom then
        if Nat.beq w forcedV || !(Nat.beq (preOr ||| suf) fullVal) then 1 else 0
      else 0
    forceNat (preOr ||| mw) fun nextPre =>
    add + essConstGo dom fullVal forcedV nextPre rest sufs
  | _, [] => 0

def essConstM (dom fullVal forcedV : ℕ) (UM : List (ℕ × ℕ)) : ℕ :=
  essConstGo dom fullVal forcedV 0 UM (sufOrs UM).tail

def domKillsStep (d K : ℕ) (S : List ℕ) (v : ℕ) (UM : List (ℕ × ℕ)) (fullVal : ℕ) : Bool :=
  forceNat (domMask d) fun dom =>
  forceNat (domKd d) fun kd =>
  forceNat (lossOnDom dom (domInps d) (v :: S)) fun ls =>
  if Nat.ble (kd + 1 + ls) K then !(Nat.ble (kd + 1 + ls + essConstM dom fullVal v UM) K)
  else true

def domKillsInit (d s : ℕ) (UM : List (ℕ × ℕ)) (fullVal : ℕ) : Bool :=
  forceNat (domMask d) fun dom =>
  forceNat (domKd d) fun kd =>
  if Nat.ble (kd + 1) s then !(Nat.ble (kd + 1 + essConstM dom fullVal 0 UM) s)
  else true

theorem essConstGo_spec {f : ℕ → ℕ} {dom fullVal forcedV : ℕ} {P : ℕ → Prop} :
    ∀ (rest : List ℕ) (preOr : ℕ),
      rest.Nodup →
      (∀ w ∈ rest, (preOr ||| foldLor f (rest.erase w)) ≠ fullVal → P w) →
      (∀ w ∈ rest, w = forcedV → P w) →
      ∃ Cw : Finset ℕ, Cw ⊆ rest.toFinset ∧
        (∀ w ∈ Cw, (w &&& dom = 0 ∨ w &&& dom = dom) ∧ P w) ∧
        Cw.card = essConstGo dom fullVal forcedV preOr (rest.map fun w => (w, f w)) (sufList f rest).tail
  | [], _, _, _, _ => ⟨∅, by simp, by simp, rfl⟩
  | w :: t, preOr, hnd, hEss, hF => by
    obtain ⟨hw_nt, ht_nd⟩ := List.nodup_cons.mp hnd
    have hEss_t : ∀ u ∈ t, ((preOr ||| f w) ||| foldLor f (t.erase u)) ≠ fullVal → P u := by
      intro u hu hne
      apply hEss u (List.mem_cons_of_mem _ hu)
      have hne_wu : w ≠ u := fun h => hw_nt (h ▸ hu)
      have hbeq : ¬ (w == u) = true := by simp [hne_wu]
      rw [List.erase_cons_tail hbeq, foldLor_cons, ← Nat.lor_assoc]
      exact hne
    obtain ⟨Cw', hsub', hP', hcard'⟩ :=
      essConstGo_spec t (preOr ||| f w) ht_nd hEss_t (fun u hu => hF u (List.mem_cons_of_mem _ hu))
    have hw_nCw' : w ∉ Cw' := fun hm => hw_nt (List.mem_toFinset.mp (hsub' hm))
    have hsub_wt : Cw' ⊆ (w :: t).toFinset := fun u hu => List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hsub' hu)))
    rw [sufList, List.tail_cons, sufList_head_tail f t]
    simp only [List.map_cons, essConstGo, forceNat_eq]
    by_cases hcd : (Nat.beq (w &&& dom) 0 || Nat.beq (w &&& dom) dom) = true
    · simp only [hcd, ↓reduceIte]
      have hwd : w &&& dom = 0 ∨ w &&& dom = dom := by simpa [Bool.or_eq_true, Nat.beq_eq] using hcd
      by_cases hfe : (Nat.beq w forcedV || !(Nat.beq (preOr ||| foldLor f t) fullVal)) = true
      · simp only [hfe, ↓reduceIte]
        have hPw : P w := by
          rcases Bool.or_eq_true _ _ |>.mp hfe with hf | he
          · exact hF w (by simp) (Nat.eq_of_beq_eq_true hf)
          · apply hEss w (by simp)
            rw [List.erase_cons_head]
            intro heq; rw [heq, Nat.beq_refl] at he; simp at he
        refine ⟨insert w Cw', ?_, ?_, ?_⟩
        · intro u hu; rcases Finset.mem_insert.mp hu with rfl | hu
          · exact List.mem_toFinset.mpr (by simp)
          · exact hsub_wt hu
        · intro u hu; rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ⟨hwd, hPw⟩
          · exact hP' u hu
        · rw [Finset.card_insert_of_notMem hw_nCw', hcard']; omega
      · simp only [hfe, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ⟨Cw', hsub_wt, hP', hcard'⟩
    · simp only [hcd, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ⟨Cw', hsub_wt, hP', hcard'⟩

theorem essConstM_spec {r : ℕ} {bits U : List ℕ} {seq : List (Fin 2 × ℕ × ℕ)} {m dom forcedV : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hmr : m + r = seq.length) (hr : 1 ≤ r)
    (hU_nd : U.Nodup) (hTsub : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ U.toFinset)
    (hforced : forcedV = 0 ∨ forcedV ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m))
    (hU_nz : ∀ w ∈ U, w ≠ 0) :
    ∃ Cw : Finset ℕ, Cw ⊆ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ∧
      (∀ w ∈ Cw, w &&& dom = 0 ∨ w &&& dom = dom) ∧
      Cw.card = essConstM dom (fullM targetNat bits) forcedV (U.map fun w => (w, sepM targetNat bits w)) := by
  have hEss : ∀ w ∈ U, (0 ||| foldLor (sepM targetNat bits) (U.erase w)) ≠ fullM targetNat bits →
      w ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
    intro w _ hne
    rw [Nat.zero_or] at hne
    by_contra hnotT
    have hsubT : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ (U.erase w).toFinset := by
      intro z hz
      exact List.mem_toFinset.mpr ((mem_erase_of_nodup hU_nd).mpr ⟨List.mem_toFinset.mp (hTsub hz), fun he => hnotT (he ▸ hz)⟩)
    have hcU : CanM targetNat r (U.erase w).toFinset := monoCMD hsubT (usedWires_canM hmin hmr hr)
    exact hne (coveredM_sepM hM hcU bits hbits)
  have hF : ∀ w ∈ U, w = forcedV → w ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
    intro w hw heq
    rcases hforced with hf0 | hfm
    · exact absurd (heq.trans hf0) (hU_nz w hw)
    · exact heq ▸ hfm
  obtain ⟨Cw, _, hP, hcard⟩ := essConstGo_spec (f := sepM targetNat bits) (dom := dom) (fullVal := fullM targetNat bits)
    (forcedV := forcedV) (P := fun w => w ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)) U 0 hU_nd hEss hF
  exact ⟨Cw, fun w hw => (hP w hw).2, fun w hw => (hP w hw).1, by rw [essConstM, sufOrs_eq]; exact hcard⟩

theorem ess_forces_input {k : ℕ} {bits S U' : List ℕ} {o : Fin 2} {a b x : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hess : (!(Nat.beq (foldLor (sepM targetNat bits) (S.erase x)) (fullM targetNat bits))) = true)
    (hU' : ∀ z ∈ U', z ∈ S.erase x)
    (ha : freeM S.toFinset a) (hb : freeM S.toFinset b)
    (hcU : CanM targetNat k (combM o a b :: U').toFinset) :
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
  have hc1 : CanM targetNat (k + 1) (S.erase x).toFinset := ⟨o, a, b, lift hax ha, lift hbx hb, monoCMD hsub hcU⟩
  have hcov := coveredM_sepM hM hc1 bits hbits
  rw [hcov, Nat.beq_refl] at hess
  simp at hess

def IsRO : ℕ → Finset ℕ → ℕ → Prop
  | 0, _, _ => False
  | 1, U, f => U = {f}
  | n + 2, U, f =>
    ∃ (o : Fin 2) (U1 U2 : Finset ℕ) (f1 f2 : ℕ)
      (_ : U1.card ≤ n + 1) (_ : U2.card ≤ n + 1),
      Disjoint U1 U2 ∧ U1 ∪ U2 = U ∧ U1.Nonempty ∧ U2.Nonempty ∧
      U1.card + U2.card = n + 2 ∧
      IsRO U1.card U1 f1 ∧ IsRO U2.card U2 f2 ∧ f = combM o f1 f2
termination_by n _ _ => n
decreasing_by
  all_goals omega


theorem isRO_mono : ∀ (n : ℕ) {U : Finset ℕ} {f : ℕ}, IsRO n U f →
    ∀ a b, (∀ w ∈ U, w.testBit a = true → w.testBit b = true) →
      f.testBit a = true → f.testBit b = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U f hro a b hU ha
    match n with
    | 0 => unfold IsRO at hro; exact hro.elim
    | 1 =>
      unfold IsRO at hro
      exact hU f (hro ▸ Finset.mem_singleton_self f) ha
    | m + 2 =>
      unfold IsRO at hro
      obtain ⟨o, U1, U2, f1, f2, h1le, h2le, _, hun, _, _, _, hr1, hr2, rfl⟩ := hro
      have hU1 : ∀ w ∈ U1, w.testBit a = true → w.testBit b = true :=
        fun w hw => hU w (hun ▸ Finset.mem_union_left _ hw)
      have hU2 : ∀ w ∈ U2, w.testBit a = true → w.testBit b = true :=
        fun w hw => hU w (hun ▸ Finset.mem_union_right _ hw)
      have hm1 := ih U1.card (by omega) hr1 a b hU1
      have hm2 := ih U2.card (by omega) hr2 a b hU2
      fin_cases o
      · simp only [combM, Nat.testBit_land, Bool.and_eq_true] at ha ⊢
        exact ⟨hm1 ha.1, hm2 ha.2⟩
      · simp only [combM, Nat.testBit_lor, Bool.or_eq_true] at ha ⊢
        exact ha.imp hm1 hm2

theorem isRO_lt : ∀ (n : ℕ) {U : Finset ℕ} {f : ℕ}, (∀ w ∈ U, w < 65536) → IsRO n U f → f < 65536 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U f hlt hro
    match n with
    | 0 => unfold IsRO at hro; exact hro.elim
    | 1 =>
      unfold IsRO at hro
      exact hlt f (hro ▸ Finset.mem_singleton_self f)
    | m + 2 =>
      unfold IsRO at hro
      obtain ⟨o, U1, U2, f1, f2, h1le, h2le, _, hun, _, _, _, hr1, hr2, rfl⟩ := hro
      have hf1 := ih U1.card (by omega) (fun w hw => hlt w (hun ▸ Finset.mem_union_left _ hw)) hr1
      have hf2 := ih U2.card (by omega) (fun w hw => hlt w (hun ▸ Finset.mem_union_right _ hw)) hr2
      fin_cases o
      · exact Nat.and_lt_two_pow (n := 16) f1 hf2
      · exact Nat.or_lt_two_pow (n := 16) hf1 hf2

theorem isRO_permOk : ∀ (n : ℕ) {U : Finset ℕ} {f : ℕ} {g : ℕ → ℕ},
    PermOk g → (∀ w ∈ U, w < 65536) → IsRO n U f → IsRO n (U.image g) (g f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U f g hg hlt hro
    match n with
    | 0 => unfold IsRO at hro; exact hro.elim
    | 1 =>
      unfold IsRO at hro ⊢
      rw [hro, Finset.image_singleton]
    | m + 2 =>
      unfold IsRO at hro ⊢
      obtain ⟨o, U1, U2, f1, f2, h1le, h2le, hdisj, hun, h1ne, h2ne, hsum, hr1, hr2, rfl⟩ := hro
      have hlt1 : ∀ w ∈ U1, w < 65536 := fun w hw => hlt w (hun ▸ Finset.mem_union_left _ hw)
      have hlt2 : ∀ w ∈ U2, w < 65536 := fun w hw => hlt w (hun ▸ Finset.mem_union_right _ hw)
      have hinj1 : Set.InjOn g (U1 : Set ℕ) := fun a ha b hb h => hg.2.2.2.2 a b (hlt1 a ha) (hlt1 b hb) h
      have hinj2 : Set.InjOn g (U2 : Set ℕ) := fun a ha b hb h => hg.2.2.2.2 a b (hlt2 a ha) (hlt2 b hb) h
      have hc1 : (U1.image g).card = U1.card := Finset.card_image_of_injOn hinj1
      have hc2 : (U2.image g).card = U2.card := Finset.card_image_of_injOn hinj2
      have hdisj' : Disjoint (U1.image g) (U2.image g) := by
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hy2
        have hab : b = a := hg.2.2.2.2 b a (hlt2 b hb) (hlt1 a ha) hba
        exact Finset.disjoint_left.mp hdisj ha (hab ▸ hb)
      refine ⟨o, U1.image g, U2.image g, g f1, g f2, by omega, by omega, hdisj', by rw [← Finset.image_union, hun],
        h1ne.image g, h2ne.image g, by omega, ?_, ?_, hg.2.2.2.1 o f1 f2⟩
      · rw [hc1]; exact ih U1.card (by omega) hg hlt1 hr1
      · rw [hc2]; exact ih U2.card (by omega) hg hlt2 hr2

def IsRORoot (T : Finset ℕ) : Prop :=
  ∃ (o : Fin 2) (U1 U2 : Finset ℕ) (f1 f2 : ℕ),
    Disjoint U1 U2 ∧ U1 ∪ U2 = T ∧ U1.Nonempty ∧ U2.Nonempty ∧
    IsRO U1.card U1 f1 ∧ IsRO U2.card U2 f2 ∧
    targetNat = combM o f1 f2 ∧ f1 ≠ targetNat ∧ f2 ≠ targetNat

theorem isRORoot_permAut {T : Finset ℕ} (idx : ℕ) (hlt : ∀ w ∈ T, w < 65536) (h : IsRORoot T) :
    IsRORoot (T.image (permAut idx)) := by
  obtain ⟨o, U1, U2, f1, f2, hdisj, hun, h1ne, h2ne, hr1, hr2, heq, hne1, hne2⟩ := h
  have hg := permAut_ok idx
  have hfix := permAut_fix idx
  have hlt1 : ∀ w ∈ U1, w < 65536 := fun w hw => hlt w (hun ▸ Finset.mem_union_left _ hw)
  have hlt2 : ∀ w ∈ U2, w < 65536 := fun w hw => hlt w (hun ▸ Finset.mem_union_right _ hw)
  have hf1lt : f1 < 65536 := isRO_lt U1.card hlt1 hr1
  have hf2lt : f2 < 65536 := isRO_lt U2.card hlt2 hr2
  have hinj1 : Set.InjOn (permAut idx) (U1 : Set ℕ) := fun a ha b hb he => hg.2.2.2.2 a b (hlt1 a ha) (hlt1 b hb) he
  have hinj2 : Set.InjOn (permAut idx) (U2 : Set ℕ) := fun a ha b hb he => hg.2.2.2.2 a b (hlt2 a ha) (hlt2 b hb) he
  have hc1 : (U1.image (permAut idx)).card = U1.card := Finset.card_image_of_injOn hinj1
  have hc2 : (U2.image (permAut idx)).card = U2.card := Finset.card_image_of_injOn hinj2
  have hdisj' : Disjoint (U1.image (permAut idx)) (U2.image (permAut idx)) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hy2
    have hab : b = a := hg.2.2.2.2 b a (hlt2 b hb) (hlt1 a ha) hba
    exact Finset.disjoint_left.mp hdisj ha (hab ▸ hb)
  refine ⟨o, U1.image (permAut idx), U2.image (permAut idx), permAut idx f1, permAut idx f2,
    hdisj', by rw [← Finset.image_union, hun], h1ne.image _, h2ne.image _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc1]; exact isRO_permOk U1.card hg hlt1 hr1
  · rw [hc2]; exact isRO_permOk U2.card hg hlt2 hr2
  · rw [← hfix, heq, hg.2.2.2.1]
  · intro he; exact hne1 (hg.2.2.2.2 f1 targetNat hf1lt targetNat_lt (he.trans hfix.symm))
  · intro he; exact hne2 (hg.2.2.2.2 f2 targetNat hf2lt targetNat_lt (he.trans hfix.symm))

theorem nodup_of_toFinset_card_ge : ∀ (l : List ℕ), l.length ≤ l.toFinset.card → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    by_cases hx : x ∈ xs
    · have heq : (x :: xs).toFinset = xs.toFinset := by
        ext y; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
        exact ⟨fun h1 => h1.elim (fun e => e ▸ hx) id, Or.inr⟩
      rw [heq, List.length_cons] at h
      have hle := List.toFinset_card_le xs
      omega
    · have hni : x ∉ xs.toFinset := by simpa [List.mem_toFinset] using hx
      rw [List.toFinset_cons, Finset.card_insert_of_notMem hni, List.length_cons] at h
      exact List.nodup_cons.mpr ⟨hx, nodup_of_toFinset_card_ge xs (by omega)⟩

theorem minimal_readOnce {seq : List (Fin 2 × ℕ × ℕ)} {m r : ℕ}
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hmr : m + r = seq.length) (hr : 1 ≤ r)
    (hcard : (endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)).card = r + 1) :
    IsRORoot (endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)) := by
  set T := endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)
  set I := (Finset.Ico m (seq.length - 1)).image (fun i => stepVal (stepAt seq i))
  have hIsub : I ⊆ usedBy (seq.drop m) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi1 : m ≤ i ∧ i < seq.length - 1 := Finset.mem_Ico.mp hi
    have hne := minimal_no_early_target hmin (m := i) (by omega) (by omega)
    have hu := minimal_used hmin (m := i) (by omega) hne
    rw [mem_usedBy_drop_iff] at hu ⊢
    obtain ⟨j, hj1, hj2, hread⟩ := hu
    exact ⟨j, by omega, hj2, hread⟩
  have hdisj : Disjoint T I := by
    rw [Finset.disjoint_left]
    intro x hxT hxI
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxI
    have hi1 : m ≤ i ∧ i < seq.length - 1 := Finset.mem_Ico.mp hi
    have hxSm : stepVal (stepAt seq i) ∈ endSet inputs.toFinset (seq.take m) := (Finset.mem_inter.mp hxT).1
    have hxSi : stepVal (stepAt seq i) ∈ endSet inputs.toFinset (seq.take i) := by
      have htk : seq.take i = seq.take m ++ (seq.take i).drop m := by
        have h1 := List.take_append_drop m (seq.take i)
        rw [List.take_take, Nat.min_eq_left hi1.1] at h1
        exact h1.symm
      rw [htk, endSet_append]
      exact endSet_sub _ _ hxSm
    exact minimal_new hmin (by omega) (Or.inr (Or.inr hxSi))
  have hIcard : I.card = r - 1 := by
    have hinj : Set.InjOn (fun i => stepVal (stepAt seq i)) (Finset.Ico m (seq.length - 1) : Set ℕ) := by
      intro a ha b hb heq
      have ha' := Finset.mem_Ico.mp ha
      have hb' := Finset.mem_Ico.mp hb
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact minimal_distinct hmin hlt (by omega) heq
      · exact minimal_distinct hmin hgt (by omega) heq.symm
    rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]; omega
  have hun : T ∪ I ⊆ usedBy (seq.drop m) := Finset.union_subset Finset.inter_subset_right hIsub
  set slots := (seq.drop m).flatMap fun st => [st.2.1, st.2.2]
  have hslots_len : slots.length = 2 * r := by
    have hmap : ∀ (q : List (Fin 2 × ℕ × ℕ)), (q.flatMap fun st => [st.2.1, st.2.2]).length = 2 * q.length := by
      intro q; induction q with | nil => rfl | cons _ t ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
    rw [hmap, List.length_drop]; omega
  have hTI_card : (T ∪ I).card = 2 * r := by rw [Finset.card_union_of_disjoint hdisj, hcard, hIcard]; omega
  have hle_slots : 2 * r ≤ slots.toFinset.card := hTI_card ▸ Finset.card_le_card hun
  have hslots_nd : slots.Nodup := nodup_of_toFinset_card_ge slots (by omega)
  have hused_eq : T ∪ I = usedBy (seq.drop m) :=
    Finset.eq_of_subset_of_card_le hun (by change slots.toFinset.card ≤ (T ∪ I).card; have := List.toFinset_card_le slots; omega)
  have hwalk : ∀ (k : ℕ), k < r →
      ∃ (live : Finset ℕ) (supp : ℕ → Finset ℕ),
        live.card = r - k + 1 ∧
        live ⊆ endSet inputs.toFinset (seq.take (m + k)) ∧
        (∀ w ∈ live, (supp w).Nonempty ∧ IsRO (supp w).card (supp w) w) ∧
        (∀ x ∈ live, ∀ y ∈ live, x ≠ y → Disjoint (supp x) (supp y)) ∧
        live.biUnion supp = T ∧
        usedBy (seq.drop (m + k)) ⊆ live ∪ (Finset.Ico (m + k) (seq.length - 1)).image (fun i => stepVal (stepAt seq i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨T, fun w => {w}, by omega, Finset.inter_subset_left, ?_, ?_, ?_, ?_⟩
      · intro w _; exact ⟨Finset.singleton_nonempty w, by unfold IsRO; simp⟩
      · intro x _ y _ hxy; exact Finset.disjoint_singleton.mpr hxy
      · ext z; simp
      · simp [I, hused_eq]
    | succ k ih =>
      intro hk
      obtain ⟨live, supp, hlc, hlA, hro, hdj, hbi, hsub⟩ := ih (by omega)
      have hmk_lt : m + k < seq.length := by omega
      have hdrop_eq : seq.drop (m + k) = stepAt seq (m + k) :: seq.drop (m + k + 1) := by
        have hget : stepAt seq (m + k) = seq[m + k] := by
          simp only [stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmk_lt, Option.getD_some]
        rw [hget]; exact List.drop_eq_getElem_cons hmk_lt
      set st := stepAt seq (m + k)
      set a := st.2.1
      set b := st.2.2
      set v := stepVal st
      have hslots_tail_nd : ((seq.drop (m + k)).flatMap fun s => [s.2.1, s.2.2]).Nodup := by
        have hsp : seq.drop m = (seq.drop m).take k ++ seq.drop (m + k) := by
          have h1 := List.take_append_drop k (seq.drop m)
          rw [List.drop_drop] at h1; exact h1.symm
        have hnd := hslots_nd
        change ((seq.drop m).flatMap fun s => [s.2.1, s.2.2]).Nodup at hnd
        rw [hsp, List.flatMap_append] at hnd
        exact (List.nodup_append.mp hnd).2.1
      rw [hdrop_eq, List.flatMap_cons] at hslots_tail_nd
      have hab_nd := List.nodup_append.mp hslots_tail_nd
      have hab_ne : a ≠ b := by
        have h1 := (List.nodup_cons.mp hab_nd.1).1
        simp only [List.mem_singleton] at h1; exact h1
      have ha_nrest : a ∉ usedBy (seq.drop (m + k + 1)) := by
        intro hm; exact hab_nd.2.2 a (by simp [a]) a (List.mem_toFinset.mp hm) rfl
      have hb_nrest : b ∉ usedBy (seq.drop (m + k + 1)) := by
        intro hm; exact hab_nd.2.2 b (by simp [b]) b (List.mem_toFinset.mp hm) rfl
      have hv_step := hmin.1
      rw [stepAt_eq_take_drop seq (m + k) hmk_lt, validSeq_append, validSeq_append] at hv_step
      simp only [ValidSeq] at hv_step
      have hnot_future : ∀ w, freeM (endSet inputs.toFinset (seq.take (m + k))) w →
          w ∉ (Finset.Ico (m + k) (seq.length - 1)).image (fun i => stepVal (stepAt seq i)) := by
        intro w hw hm
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
        have hi1 := Finset.mem_Ico.mp hi
        have hmono : endSet inputs.toFinset (seq.take (m + k)) ⊆ endSet inputs.toFinset (seq.take i) := by
          have htk : seq.take i = seq.take (m + k) ++ (seq.take i).drop (m + k) := by
            have h1 := List.take_append_drop (m + k) (seq.take i)
            rw [List.take_take, Nat.min_eq_left hi1.1] at h1; exact h1.symm
          rw [htk, endSet_append]; exact endSet_sub _ _
        exact minimal_new hmin (by omega) (freeMDMono hmono hw)
      have ha_live : a ∈ live := by
        have haU : a ∈ usedBy (seq.drop (m + k)) := by rw [hdrop_eq]; simp [usedBy, a]
        exact (Finset.mem_union.mp (hsub haU)).resolve_right (hnot_future a hv_step.1.2.1)
      have hb_live : b ∈ live := by
        have hbU : b ∈ usedBy (seq.drop (m + k)) := by rw [hdrop_eq]; simp [usedBy, b]
        exact (Finset.mem_union.mp (hsub hbU)).resolve_right (hnot_future b hv_step.1.2.2.1)
      have hv_nlive : v ∉ live := fun hvl => minimal_new hmin hmk_lt (Or.inr (Or.inr (hlA hvl)))
      set live' := insert v ((live.erase a).erase b)
      set supp' : ℕ → Finset ℕ := fun w => if w = v then supp a ∪ supp b else supp w
      have hb_ea : b ∈ live.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab_ne, hb_live⟩
      have hv_neab : v ∉ (live.erase a).erase b := fun h => hv_nlive (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
      have hlc' : live'.card = r - (k + 1) + 1 := by
        rw [Finset.card_insert_of_notMem hv_neab, Finset.card_erase_of_mem hb_ea, Finset.card_erase_of_mem ha_live]; omega
      have htake_succ : endSet inputs.toFinset (seq.take (m + (k + 1))) = insert v (endSet inputs.toFinset (seq.take (m + k))) := by
        rw [show m + (k + 1) = (m + k) + 1 by omega, take_succ_stepAt seq (m + k) hmk_lt, endSet_append, endSet, endSet]
      have hlA' : live' ⊆ endSet inputs.toFinset (seq.take (m + (k + 1))) := by
        rw [htake_succ]; intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hlA (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)))
      have hdj_ab : Disjoint (supp a) (supp b) := hdj a ha_live b hb_live hab_ne
      have hro_v : (supp a ∪ supp b).Nonempty ∧ IsRO (supp a ∪ supp b).card (supp a ∪ supp b) v := by
        have h1ne := (hro a ha_live).1
        have h2ne := (hro b hb_live).1
        have h1c : 1 ≤ (supp a).card := Finset.card_pos.mpr h1ne
        have h2c : 1 ≤ (supp b).card := Finset.card_pos.mpr h2ne
        have huc : (supp a ∪ supp b).card = (supp a).card + (supp b).card := Finset.card_union_of_disjoint hdj_ab
        refine ⟨h1ne.mono Finset.subset_union_left, ?_⟩
        obtain ⟨n0, hn0⟩ : ∃ n0, (supp a ∪ supp b).card = n0 + 2 := ⟨(supp a).card + (supp b).card - 2, by omega⟩
        rw [hn0]; unfold IsRO
        exact ⟨st.1, supp a, supp b, a, b, by omega, by omega, hdj_ab, rfl, h1ne, h2ne, by omega, (hro a ha_live).2, (hro b hb_live).2, rfl⟩
      have hro' : ∀ w ∈ live', (supp' w).Nonempty ∧ IsRO (supp' w).card (supp' w) w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa [supp'] using hro_v
        · have hwv : w ≠ v := fun he => hv_neab (he ▸ hw)
          simpa [supp', hwv] using hro w (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))
      have hdj' : ∀ x ∈ live', ∀ y ∈ live', x ≠ y → Disjoint (supp' x) (supp' y) := by
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
        · exact absurd rfl hxy
        · have hyv : y ≠ v := Ne.symm hxy
          have hyl : y ∈ live := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
          have hyb : y ≠ b := Finset.ne_of_mem_erase hy
          have hya : y ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
          simp only [supp', ↓reduceIte, hyv]
          exact Finset.disjoint_union_left.mpr ⟨hdj a ha_live y hyl (Ne.symm hya), hdj b hb_live y hyl (Ne.symm hyb)⟩
        · have hxv : x ≠ v := hxy
          have hxl : x ∈ live := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
          have hxb : x ≠ b := Finset.ne_of_mem_erase hx
          have hxa : x ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
          simp only [supp', ↓reduceIte, hxv]
          exact Finset.disjoint_union_right.mpr ⟨hdj x hxl a ha_live hxa, hdj x hxl b hb_live hxb⟩
        · have hxv : x ≠ v := fun he => hv_neab (he ▸ hx)
          have hyv : y ≠ v := fun he => hv_neab (he ▸ hy)
          simp only [supp', hxv, hyv, ↓reduceIte]
          exact hdj x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)) hxy
      have hbi' : live'.biUnion supp' = T := by
        rw [← hbi]; ext z
        simp only [Finset.mem_biUnion, live', Finset.mem_insert]
        constructor
        · rintro ⟨w, rfl | hw, hz⟩
          · simp only [supp', ↓reduceIte, Finset.mem_union] at hz
            rcases hz with hza | hzb
            · exact ⟨a, ha_live, hza⟩
            · exact ⟨b, hb_live, hzb⟩
          · have hwv : w ≠ v := fun he => hv_neab (he ▸ hw)
            simp only [supp', hwv, ↓reduceIte] at hz
            exact ⟨w, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw), hz⟩
        · rintro ⟨w, hwl, hz⟩
          by_cases hwa : w = a
          · subst hwa; exact ⟨v, Or.inl rfl, by simp [supp', hz]⟩
          · by_cases hwb : w = b
            · subst hwb; exact ⟨v, Or.inl rfl, by simp [supp', hz]⟩
            · have hwm : w ∈ (live.erase a).erase b := Finset.mem_erase.mpr ⟨hwb, Finset.mem_erase.mpr ⟨hwa, hwl⟩⟩
              have hwv : w ≠ v := fun he => hv_nlive (he ▸ hwl)
              exact ⟨w, Or.inr hwm, by simp [supp', hwv, hz]⟩
      have hsub' : usedBy (seq.drop (m + (k + 1))) ⊆ live' ∪ (Finset.Ico (m + (k + 1)) (seq.length - 1)).image (fun i => stepVal (stepAt seq i)) := by
        intro x hx
        have hx' : x ∈ usedBy (seq.drop (m + k + 1)) := by simpa [Nat.add_assoc] using hx
        have hxa : x ≠ a := fun he => ha_nrest (he ▸ hx')
        have hxb : x ≠ b := fun he => hb_nrest (he ▸ hx')
        have hxprev : x ∈ usedBy (seq.drop (m + k)) := by
          rw [hdrop_eq]; simp only [usedBy, List.mem_toFinset, List.flatMap_cons, List.mem_append] at hx' ⊢; exact Or.inr hx'
        rcases Finset.mem_union.mp (hsub hxprev) with hxl | hxi
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hxl⟩⟩))
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxi
          have hi1 := Finset.mem_Ico.mp hi
          by_cases eim : i = m + k
          · subst eim; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨by omega, hi1.2⟩, rfl⟩)
      exact ⟨live', supp', hlc', hlA', hro', hdj', hbi', hsub'⟩
  obtain ⟨live, supp, hlc, hlA, hro, hdj, hbi, hsub⟩ := hwalk (r - 1) (by omega)
  have hlast_idx : m + (r - 1) = seq.length - 1 := by omega
  have hlast_lt : seq.length - 1 < seq.length := by omega
  have hdrop_last : seq.drop (m + (r - 1)) = [stepAt seq (seq.length - 1)] := by
    rw [hlast_idx]
    have hget : stepAt seq (seq.length - 1) = seq[seq.length - 1] := by
      simp only [stepAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlast_lt, Option.getD_some]
    rw [hget, List.drop_eq_getElem_cons hlast_lt, List.drop_eq_nil_of_le (by omega)]
  set st := stepAt seq (seq.length - 1)
  set a := st.2.1
  set b := st.2.2
  have hI_empty : (Finset.Ico (m + (r - 1)) (seq.length - 1)).image (fun i => stepVal (stepAt seq i)) = ∅ := by
    rw [hlast_idx]; simp
  rw [hI_empty, Finset.union_empty, hdrop_last] at hsub
  have ha_live : a ∈ live := hsub (by simp [usedBy, a])
  have hb_live : b ∈ live := hsub (by simp [usedBy, b])
  have hab_ne : a ≠ b := by
    have hsp : seq.drop m = (seq.drop m).take (r - 1) ++ seq.drop (m + (r - 1)) := by
      have h1 := List.take_append_drop (r - 1) (seq.drop m)
      rw [List.drop_drop] at h1; exact h1.symm
    have hnd := hslots_nd
    change ((seq.drop m).flatMap fun s => [s.2.1, s.2.2]).Nodup at hnd
    rw [hsp, List.flatMap_append, hdrop_last] at hnd
    have h1 := (List.nodup_append.mp hnd).2.1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nodup_cons, List.mem_singleton] at h1
    exact h1.1
  have hlive_eq : live = {a, b} := by
    have hsub2 : ({a, b} : Finset ℕ) ⊆ live := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha_live
      · rw [Finset.mem_singleton.mp hx]; exact hb_live
    have hcard2 : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab_ne
    exact (Finset.eq_of_subset_of_card_le hsub2 (by omega)).symm
  have hnf_prev : ¬ freeM (endSet inputs.toFinset (seq.take (seq.length - 1))) targetNat := by
    intro hf
    have hv := hmin.1
    rw [← List.take_append_drop (seq.length - 1) seq, validSeq_append] at hv
    have hle := hmin.2.2 (seq.take (seq.length - 1)) hv.1 hf
    simp only [List.length_take] at hle; omega
  have htarget_eq : targetNat = stepVal st := by
    have htake_full : seq = seq.take (seq.length - 1) ++ [st] := by
      have h1 := take_succ_stepAt seq (seq.length - 1) hlast_lt
      rw [show seq.length - 1 + 1 = seq.length by omega, List.take_length] at h1
      exact h1
    have he := hmin.2.1
    rw [htake_full, endSet_append, endSet, endSet] at he
    rcases he with h0 | h1 | hm
    · exact absurd (Or.inl h0) hnf_prev
    · exact absurd (Or.inr (Or.inl h1)) hnf_prev
    · rcases Finset.mem_insert.mp hm with heq | hprev
      · exact heq
      · exact absurd (Or.inr (Or.inr hprev)) hnf_prev
  have ha_ne : a ≠ targetNat := fun he => hnf_prev (Or.inr (Or.inr (he ▸ hlast_idx ▸ hlA ha_live)))
  have hb_ne : b ≠ targetNat := fun he => hnf_prev (Or.inr (Or.inr (he ▸ hlast_idx ▸ hlA hb_live)))
  have hun_ab : supp a ∪ supp b = T := by rw [← hbi, hlive_eq]; simp
  exact ⟨st.1, supp a, supp b, a, b, hdj a ha_live b hb_live hab_ne, hun_ab,
    (hro a ha_live).1, (hro b hb_live).1, (hro a ha_live).2, (hro b hb_live).2, htarget_eq, ha_ne, hb_ne⟩


def onceTwice (p1m bitB : ℕ) : List ℕ → ℕ → ℕ → ℕ × ℕ
  | [], o, t => (o, t)
  | w :: ws, o, t =>
    if Nat.beq (w &&& bitB) 0 then
      forceNat (w &&& p1m) fun wm =>
      forceNat (o ||| wm) fun o1 =>
      forceNat (t ||| (o &&& wm)) fun t1 =>
      onceTwice p1m bitB ws o1 t1
    else onceTwice p1m bitB ws o t

def buildReq (p1m : ℕ) (U : List ℕ) : List ℕ → Option (List (ℕ × ℕ))
  | [] => some []
  | bitB :: rest =>
    let ot := onceTwice p1m bitB U 0 0
    if Nat.beq ot.1 p1m then
      forceNat (ot.1 ^^^ ot.2) fun uq =>
      match buildReq p1m U rest with
      | none => none
      | some acc => if Nat.beq uq 0 then some acc else some ((bitB, uq) :: acc)
    else none

def touches (bitB uq : ℕ) : List ℕ → Bool
  | [] => false
  | w :: ws => (Nat.beq (w &&& bitB) 0 && !(Nat.beq (w &&& uq) 0)) || touches bitB uq ws

def partEdges (front : List ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ) × List (ℕ × ℕ)
  | [], act, unu => (act, unu)
  | p :: es, act, unu =>
    if touches p.1 p.2 front then partEdges front es (p :: act) unu
    else partEdges front es act (p :: unu)

def anyEdge (w : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | (b, u) :: es => (Nat.beq (w &&& b) 0 && !(Nat.beq (w &&& u) 0)) || anyEdge w es

def partRem (act : List (ℕ × ℕ)) : List ℕ → List ℕ → List ℕ → List ℕ × List ℕ
  | [], hit, rest => (hit, rest)
  | w :: ws, hit, rest =>
    if anyEdge w act then partRem act ws (w :: hit) rest
    else partRem act ws hit (w :: rest)

def expandF : ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ → List ℕ × List ℕ × List (ℕ × ℕ)
  | 0, es, front, comp, rem => (front ++ comp, rem, es)
  | fuel + 1, es, front, comp, rem =>
    let comp' := front ++ comp
    match rem with
    | [] => (comp', [], es)
    | _ :: _ =>
      let au := partEdges front es [] []
      match au.1 with
      | [] => (comp', rem, au.2)
      | _ :: _ =>
        let hr := partRem au.1 rem [] []
        match hr.1 with
        | [] => (comp', rem, au.2)
        | _ :: _ => expandF fuel au.2 hr.1 comp' hr.2

def splitComps : ℕ → List (ℕ × ℕ) → List ℕ → List (List ℕ)
  | _, _, [] => []
  | 0, _, rem => [rem]
  | fuel + 1, es, x :: xs =>
    let cr := expandF (xs.length + 1) es [x] [] xs
    cr.1 :: splitComps fuel cr.2.2 cr.2.1

def foldOr (p1m bitB : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | w :: ws, acc =>
    if Nat.beq (w &&& bitB) 0 then
      forceNat (acc ||| (w &&& p1m)) fun a1 => foldOr p1m bitB ws a1
    else foldOr p1m bitB ws acc

def splitP (p1m : ℕ) (U1 U2 : List ℕ) : List ℕ → ℕ → List ℕ → ℕ → List ℕ → Bool → Bool → Option ((ℕ × List ℕ) × (ℕ × List ℕ) × Bool × Bool)
  | [], m1, b1, m2, b2, h1, h2 => some ((m1, b1), (m2, b2), h1, h2)
  | bitB :: rest, m1, b1, m2, b2, h1, h2 =>
    let s1 := Nat.beq (foldOr p1m bitB U1 0) p1m
    let s2 := Nat.beq (foldOr p1m bitB U2 0) p1m
    if !s1 && !s2 then none
    else
      forceNat (if s2 then m1 else m1 ||| bitB) fun m1' =>
      let b1' := if s2 then b1 else bitB :: b1
      forceNat (if s1 then m2 else m2 ||| bitB) fun m2' =>
      let b2' := if s1 then b2 else bitB :: b2
      splitP p1m U1 U2 rest m1' b1' m2' b2' (h1 || s1) (h2 || s2)

def trySplits (chk : List ℕ → List ℕ → Bool) (U1 U2 : List ℕ) : List (List ℕ) → Bool
  | [] => match U2 with | [] => false | _ :: _ => chk U1 U2
  | c :: rest => trySplits chk (c ++ U1) U2 rest || trySplits chk U1 (c ++ U2) rest

def complList : List ℕ → List ℕ
  | [] => []
  | w :: ws => forceNat (65535 ^^^ w) fun cw => cw :: complList ws

def canROSide (sub : List ℕ → ℕ → List ℕ → Bool) (U : List ℕ) (p1m : ℕ) (p0Bits : List ℕ) (isRoot : Bool) : Bool :=
  match buildReq p1m U p0Bits with
  | none => false
  | some u0 =>
    match splitComps U.length u0 U with
    | [] => false
    | [_] => false
    | c0 :: cs =>
      trySplits (fun U1 U2 =>
        match splitP p1m U1 U2 p0Bits 0 [] 0 [] false false with
        | none => false
        | some ((m1, b1), (m2, b2), h1, h2) =>
          if isRoot && (!h1 || !h2) then false
          else sub U1 m1 b1 && sub U2 m2 b2) c0 [] cs

def canRO : ℕ → List ℕ → ℕ → ℕ → List ℕ → List ℕ → Bool → Bool
  | fuel, U, p1m, p0m, p1Bits, p0Bits, isRoot =>
    if Nat.beq p1m 0 || Nat.beq p0m 0 then true
    else
      match U with
      | [] => false
      | [w] => Nat.beq (w &&& p1m) p1m && Nat.beq (w &&& p0m) 0
      | _ :: _ :: _ =>
        match fuel with
        | 0 => true
        | f + 1 =>
          if canROSide (fun L m b => canRO f L p1m m p1Bits b false) U p1m p0Bits isRoot then true
          else canROSide (fun L m b => canRO f L p0m m p0Bits b false) (complList U) p0m p1Bits isRoot


def BitsRep (m : ℕ) (bs : List ℕ) : Prop :=
  (∀ i, m.testBit i = true ↔ 2 ^ i ∈ bs) ∧ (∀ x ∈ bs, ∃ i < 16, x = 2 ^ i)

theorem bitsRep_lt16 {m : ℕ} {bs : List ℕ} (h : BitsRep m bs) {i : ℕ} (hi : m.testBit i = true) : i < 16 := by
  obtain ⟨j, hj16, heq⟩ := h.2 (2 ^ i) (h.1 i |>.mp hi)
  have hij : i = j := Nat.pow_right_injective (by decide : 1 < 2) heq
  omega

theorem and_two_pow_eq_zero_iff (v a : ℕ) : Nat.beq (v &&& 2 ^ a) 0 = true ↔ v.testBit a = false := by
  have h := and_two_pow_ne_zero_iff v a
  cases hv : v.testBit a with
  | false =>
    rw [hv] at h
    simp only [bne_eq_false_iff_eq] at h
    simp [h]
  | true =>
    rw [hv] at h
    simp only [bne_iff_ne, ne_eq] at h
    simp [Nat.beq_eq, h]

theorem and_ne_zero_iff (x y : ℕ) : (!(Nat.beq (x &&& y) 0)) = true ↔ ∃ a, x.testBit a = true ∧ y.testBit a = true := by
  constructor
  · intro hne
    have hne0 : x &&& y ≠ 0 := fun heq => by rw [heq] at hne; simp at hne
    by_contra hall
    apply hne0
    apply Nat.eq_of_testBit_eq; intro a
    simp only [Nat.testBit_land, Nat.zero_testBit, Bool.and_eq_false_iff]
    by_cases hx : x.testBit a = true
    · right; cases hy : y.testBit a with
      | false => rfl
      | true => exact absurd ⟨a, hx, hy⟩ hall
    · left; cases hx0 : x.testBit a <;> simp_all
  · rintro ⟨a, hx, hy⟩
    cases hb : Nat.beq (x &&& y) 0 with
    | false => rfl
    | true =>
      have heq := Nat.eq_of_beq_eq_true hb
      have ht := congrArg (fun n => n.testBit a) heq
      simp [Nat.testBit_land, hx, hy] at ht

theorem xor_65535_testBit {w b : ℕ} (hb : b < 16) : (65535 ^^^ w).testBit b = !w.testBit b := by
  have h6 : (65535 : ℕ).testBit b = true :=
    (show ∀ q : Fin 16, (65535 : ℕ).testBit q.val = true by decide) ⟨b, hb⟩
  simp [Nat.testBit_xor, h6]


theorem onceTwice_spec (p1m b : ℕ) : ∀ (U : List ℕ) (o0 t0 : ℕ), U.Nodup →
    (∀ a, (onceTwice p1m (2 ^ b) U o0 t0).1.testBit a = true ↔
      o0.testBit a = true ∨ (p1m.testBit a = true ∧ ∃ w ∈ U, w.testBit b = false ∧ w.testBit a = true)) ∧
    (∀ a, (onceTwice p1m (2 ^ b) U o0 t0).2.testBit a = true ↔
      t0.testBit a = true ∨
      (o0.testBit a = true ∧ p1m.testBit a = true ∧ ∃ w ∈ U, w.testBit b = false ∧ w.testBit a = true) ∨
      (p1m.testBit a = true ∧ ∃ w1 ∈ U, ∃ w2 ∈ U, w1 ≠ w2 ∧
        w1.testBit b = false ∧ w1.testBit a = true ∧ w2.testBit b = false ∧ w2.testBit a = true))
  | [], o0, t0, _ => by simp [onceTwice]
  | w :: ws, o0, t0, hnd => by
    obtain ⟨hw_nws, hws_nd⟩ := List.nodup_cons.mp hnd
    unfold onceTwice
    simp only [forceNat_eq]
    by_cases hwb : Nat.beq (w &&& 2 ^ b) 0 = true
    · simp only [hwb, ↓reduceIte]
      have hwb0 : w.testBit b = false := (and_two_pow_eq_zero_iff w b).mp hwb
      obtain ⟨ih1, ih2⟩ := onceTwice_spec p1m b ws (o0 ||| (w &&& p1m)) (t0 ||| (o0 &&& (w &&& p1m))) hws_nd
      refine ⟨fun a => ?_, fun a => ?_⟩
      · rw [ih1 a]; simp only [Nat.testBit_lor, Nat.testBit_land, Bool.or_eq_true, Bool.and_eq_true, List.mem_cons]
        constructor
        · rintro ((ho | ⟨hwa, hpa⟩) | ⟨hpa, u, hu, hub, hua⟩)
          · exact Or.inl ho
          · exact Or.inr ⟨hpa, w, Or.inl rfl, hwb0, hwa⟩
          · exact Or.inr ⟨hpa, u, Or.inr hu, hub, hua⟩
        · rintro (ho | ⟨hpa, u, rfl | hu, hub, hua⟩)
          · exact Or.inl (Or.inl ho)
          · exact Or.inl (Or.inr ⟨hua, hpa⟩)
          · exact Or.inr ⟨hpa, u, hu, hub, hua⟩
      · rw [ih2 a]; simp only [Nat.testBit_lor, Nat.testBit_land, Bool.or_eq_true, Bool.and_eq_true, List.mem_cons]
        constructor
        · rintro ((ht | ⟨ho, hwa, hpa⟩) | ⟨ho | ⟨hwa, _⟩, hpa, u, hu, hub, hua⟩ | ⟨hpa, u1, hu1, u2, hu2, hne, h1b, h1a, h2b, h2a⟩)
          · exact Or.inl ht
          · exact Or.inr (Or.inl ⟨ho, hpa, w, Or.inl rfl, hwb0, hwa⟩)
          · exact Or.inr (Or.inl ⟨ho, hpa, u, Or.inr hu, hub, hua⟩)
          · exact Or.inr (Or.inr ⟨hpa, w, Or.inl rfl, u, Or.inr hu, fun he => hw_nws (he ▸ hu), hwb0, hwa, hub, hua⟩)
          · exact Or.inr (Or.inr ⟨hpa, u1, Or.inr hu1, u2, Or.inr hu2, hne, h1b, h1a, h2b, h2a⟩)
        · rintro (ht | ⟨ho, hpa, u, rfl | hu, hub, hua⟩ | ⟨hpa, u1, rfl | hu1, u2, rfl | hu2, hne, h1b, h1a, h2b, h2a⟩)
          · exact Or.inl (Or.inl ht)
          · exact Or.inl (Or.inr ⟨ho, hua, hpa⟩)
          · exact Or.inr (Or.inl ⟨Or.inl ho, hpa, u, hu, hub, hua⟩)
          · exact absurd rfl hne
          · exact Or.inr (Or.inl ⟨Or.inr ⟨h1a, hpa⟩, hpa, u2, hu2, h2b, h2a⟩)
          · exact Or.inr (Or.inl ⟨Or.inr ⟨h2a, hpa⟩, hpa, u1, hu1, h1b, h1a⟩)
          · exact Or.inr (Or.inr ⟨hpa, u1, hu1, u2, hu2, hne, h1b, h1a, h2b, h2a⟩)
    · simp only [hwb, Bool.false_eq_true, ↓reduceIte]
      have hwb1 : w.testBit b = true := by
        cases hv : w.testBit b with
        | true => rfl
        | false => exact absurd ((and_two_pow_eq_zero_iff w b).mpr hv) hwb
      obtain ⟨ih1, ih2⟩ := onceTwice_spec p1m b ws o0 t0 hws_nd
      refine ⟨fun a => ?_, fun a => ?_⟩
      · rw [ih1 a]; simp only [List.mem_cons]
        constructor
        · rintro (ho | ⟨hpa, u, hu, hub, hua⟩)
          · exact Or.inl ho
          · exact Or.inr ⟨hpa, u, Or.inr hu, hub, hua⟩
        · rintro (ho | ⟨hpa, u, rfl | hu, hub, hua⟩)
          · exact Or.inl ho
          · rw [hwb1] at hub; simp at hub
          · exact Or.inr ⟨hpa, u, hu, hub, hua⟩
      · rw [ih2 a]; simp only [List.mem_cons]
        constructor
        · rintro (ht | ⟨ho, hpa, u, hu, hub, hua⟩ | ⟨hpa, u1, hu1, u2, hu2, hne, h1b, h1a, h2b, h2a⟩)
          · exact Or.inl ht
          · exact Or.inr (Or.inl ⟨ho, hpa, u, Or.inr hu, hub, hua⟩)
          · exact Or.inr (Or.inr ⟨hpa, u1, Or.inr hu1, u2, Or.inr hu2, hne, h1b, h1a, h2b, h2a⟩)
        · rintro (ht | ⟨ho, hpa, u, rfl | hu, hub, hua⟩ | ⟨hpa, u1, rfl | hu1, u2, rfl | hu2, hne, h1b, h1a, h2b, h2a⟩)
          · exact Or.inl ht
          · rw [hwb1] at hub; simp at hub
          · exact Or.inr (Or.inl ⟨ho, hpa, u, hu, hub, hua⟩)
          · exact absurd rfl hne
          · rw [hwb1] at h1b; simp at h1b
          · rw [hwb1] at h2b; simp at h2b
          · exact Or.inr (Or.inr ⟨hpa, u1, hu1, u2, hu2, hne, h1b, h1a, h2b, h2a⟩)


def PureEdge (U1 U2 : Finset ℕ) (U : List ℕ) (p : ℕ × ℕ) : Prop :=
  (∀ w ∈ U, (Nat.beq (w &&& p.1) 0 && !(Nat.beq (w &&& p.2) 0)) = true → w ∈ U1) ∨
  (∀ w ∈ U, (Nat.beq (w &&& p.1) 0 && !(Nat.beq (w &&& p.2) 0)) = true → w ∈ U2)


theorem buildReq_spec {p1m f1 f2 : ℕ} {U1 U2 : Finset ℕ} {U : List ℕ}
    (hnd : U.Nodup) (hun : U1 ∪ U2 = U.toFinset)
    (hm1 : ∀ a b, (∀ w ∈ U1, w.testBit a = true → w.testBit b = true) → f1.testBit a = true → f1.testBit b = true)
    (hm2 : ∀ a b, (∀ w ∈ U2, w.testBit a = true → w.testBit b = true) → f2.testBit a = true → f2.testBit b = true)
    (hp1 : ∀ a, p1m.testBit a = true → (f1 &&& f2).testBit a = true) :
    ∀ bs : List ℕ, (∀ x ∈ bs, ∃ b, x = 2 ^ b ∧ (f1 &&& f2).testBit b = false) →
      ∃ u0, buildReq p1m U bs = some u0 ∧ ∀ p ∈ u0, PureEdge U1 U2 U p
  | [], _ => ⟨[], rfl, fun _ h => by simp at h⟩
  | x :: rest, hbs => by
    obtain ⟨b, rfl, hfb⟩ := hbs x (by simp)
    obtain ⟨u0, hrec, hpure⟩ := buildReq_spec hnd hun hm1 hm2 hp1 rest (fun y hy => hbs y (by simp [hy]))
    obtain ⟨h1, h2⟩ := onceTwice_spec p1m b U 0 0 hnd
    have hfb_or : f1.testBit b = false ∨ f2.testBit b = false := by
      simp only [Nat.testBit_land, Bool.and_eq_false_iff] at hfb; exact hfb
    have hsep : ∀ a, p1m.testBit a = true → ∃ w ∈ U, w.testBit b = false ∧ w.testBit a = true := by
      intro a ha
      have hfa := hp1 a ha
      simp only [Nat.testBit_land, Bool.and_eq_true] at hfa
      rcases hfb_or with h10 | h20
      · by_contra hno
        have hall : ∀ w ∈ U1, w.testBit a = true → w.testBit b = true := by
          intro w hw hwa
          cases hwb : w.testBit b with
          | true => rfl
          | false => exact absurd ⟨w, List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ hw), hwb, hwa⟩ hno
        have := hm1 a b hall hfa.1; rw [h10] at this; simp at this
      · by_contra hno
        have hall : ∀ w ∈ U2, w.testBit a = true → w.testBit b = true := by
          intro w hw hwa
          cases hwb : w.testBit b with
          | true => rfl
          | false => exact absurd ⟨w, List.mem_toFinset.mp (hun ▸ Finset.mem_union_right _ hw), hwb, hwa⟩ hno
        have := hm2 a b hall hfa.2; rw [h20] at this; simp at this
    have ho_eq : (onceTwice p1m (2 ^ b) U 0 0).1 = p1m := by
      apply Nat.eq_of_testBit_eq; intro a
      cases hpa : p1m.testBit a with
      | false =>
        cases ho : (onceTwice p1m (2 ^ b) U 0 0).1.testBit a with
        | false => rfl
        | true => have := (h1 a).mp ho; simp [hpa] at this
      | true => exact (h1 a).mpr (Or.inr ⟨hpa, hsep a hpa⟩)
    unfold buildReq; simp only [forceNat_eq]
    rw [ho_eq, Nat.beq_refl]; simp only [↓reduceIte, hrec]
    set uq := p1m ^^^ (onceTwice p1m (2 ^ b) U 0 0).2
    have hpuq : PureEdge U1 U2 U (2 ^ b, uq) := by
      have uniq_side : ∀ (S : Finset ℕ) (g : ℕ), S ⊆ U.toFinset →
          (∀ a b, (∀ w ∈ S, w.testBit a = true → w.testBit b = true) → g.testBit a = true → g.testBit b = true) →
          (∀ a, p1m.testBit a = true → g.testBit a = true) → g.testBit b = false →
          ∀ w ∈ U, (Nat.beq (w &&& 2 ^ b) 0 && !(Nat.beq (w &&& uq) 0)) = true → w ∈ S := by
        intro S g hSU hmg hgp1 hgb w hwU htouch
        simp only [Bool.and_eq_true, and_two_pow_eq_zero_iff, and_ne_zero_iff] at htouch
        obtain ⟨hwb, a, hwa, huqa⟩ := htouch
        have hpa : p1m.testBit a = true := by
          by_contra hnp
          have hpf : p1m.testBit a = false := by cases hv : p1m.testBit a <;> simp_all
          have ht0 : (onceTwice p1m (2 ^ b) U 0 0).2.testBit a = false := by
            cases hv : (onceTwice p1m (2 ^ b) U 0 0).2.testBit a with
            | false => rfl
            | true => have := (h2 a).mp hv; simp [hpf] at this
          simp [uq, Nat.testBit_xor, hpf, ht0] at huqa
        have ht0 : (onceTwice p1m (2 ^ b) U 0 0).2.testBit a = false := by
          simp only [uq, Nat.testBit_xor, hpa] at huqa
          cases hv : (onceTwice p1m (2 ^ b) U 0 0).2.testBit a <;> simp_all
        have hex : ∃ u ∈ S, u.testBit b = false ∧ u.testBit a = true := by
          by_contra hno
          have hall : ∀ u ∈ S, u.testBit a = true → u.testBit b = true := by
            intro u hu hua; cases hub : u.testBit b with
            | true => rfl | false => exact absurd ⟨u, hu, hub, hua⟩ hno
          have := hmg a b hall (hgp1 a hpa); rw [hgb] at this; simp at this
        obtain ⟨u, huS, hub, hua⟩ := hex
        by_cases heq : u = w
        · exact heq ▸ huS
        · exfalso
          have ht1 := (h2 a).mpr (Or.inr (Or.inr ⟨hpa, u, List.mem_toFinset.mp (hSU huS), w, hwU, heq, hub, hua, hwb, hwa⟩))
          rw [ht0] at ht1; simp at ht1
      rcases hfb_or with h10 | h20
      · left; exact uniq_side U1 f1 (hun ▸ Finset.subset_union_left) hm1 (fun a ha => by have := hp1 a ha; simp [Nat.testBit_land] at this; exact this.1) h10
      · right; exact uniq_side U2 f2 (hun ▸ Finset.subset_union_right) hm2 (fun a ha => by have := hp1 a ha; simp [Nat.testBit_land] at this; exact this.2) h20
    by_cases h0 : Nat.beq uq 0 = true
    · simp only [h0, ↓reduceIte]; exact ⟨u0, rfl, hpure⟩
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      refine ⟨(2 ^ b, uq) :: u0, rfl, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hpuq
      · exact hpure p hp


theorem touches_iff (b u : ℕ) : ∀ l : List ℕ, touches b u l = true ↔
    ∃ w ∈ l, (Nat.beq (w &&& b) 0 && !(Nat.beq (w &&& u) 0)) = true
  | [] => by simp [touches]
  | w :: ws => by simp [touches, touches_iff b u ws]


theorem anyEdge_iff (w : ℕ) : ∀ es : List (ℕ × ℕ), anyEdge w es = true ↔
    ∃ p ∈ es, (Nat.beq (w &&& p.1) 0 && !(Nat.beq (w &&& p.2) 0)) = true
  | [] => by simp [anyEdge]
  | (b, u) :: es => by simp [anyEdge, anyEdge_iff w es]


theorem partEdges_spec (front : List ℕ) : ∀ (es act unu : List (ℕ × ℕ)),
    (∀ p ∈ (partEdges front es act unu).1, p ∈ act ∨ (p ∈ es ∧ touches p.1 p.2 front = true)) ∧
    (∀ p ∈ (partEdges front es act unu).2, p ∈ unu ∨ p ∈ es)
  | [], act, unu => ⟨fun _ h => Or.inl h, fun _ h => Or.inl h⟩
  | p :: es, act, unu => by
    unfold partEdges
    by_cases ht : touches p.1 p.2 front = true
    · simp only [ht, ↓reduceIte]
      obtain ⟨h1, h2⟩ := partEdges_spec front es (p :: act) unu
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · rcases h1 q hq with hqa | ⟨hqe, hqt⟩
        · rcases List.mem_cons.mp hqa with rfl | hqa
          · exact Or.inr ⟨by simp, ht⟩
          · exact Or.inl hqa
        · exact Or.inr ⟨List.mem_cons_of_mem _ hqe, hqt⟩
      · rcases h2 q hq with hqu | hqe
        · exact Or.inl hqu
        · exact Or.inr (List.mem_cons_of_mem _ hqe)
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2⟩ := partEdges_spec front es act (p :: unu)
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · rcases h1 q hq with hqa | ⟨hqe, hqt⟩
        · exact Or.inl hqa
        · exact Or.inr ⟨List.mem_cons_of_mem _ hqe, hqt⟩
      · rcases h2 q hq with hqu | hqe
        · rcases List.mem_cons.mp hqu with rfl | hqu
          · exact Or.inr (by simp)
          · exact Or.inl hqu
        · exact Or.inr (List.mem_cons_of_mem _ hqe)


theorem partRem_spec (act : List (ℕ × ℕ)) : ∀ (rem hit rest : List ℕ),
    (rem ++ hit ++ rest).Nodup →
    let r := partRem act rem hit rest
    (r.1 ++ r.2).Nodup ∧
    r.1.length + r.2.length = rem.length + hit.length + rest.length ∧
    (∀ w, w ∈ r.1 ∨ w ∈ r.2 ↔ w ∈ rem ∨ w ∈ hit ∨ w ∈ rest) ∧
    (∀ w ∈ r.1, w ∈ hit ∨ (w ∈ rem ∧ anyEdge w act = true))
  | [], hit, rest, hnd => by
    simp only [partRem]
    refine ⟨by simpa using hnd, by simp, fun w => by simp, fun w hw => Or.inl hw⟩
  | w :: ws, hit, rest, hnd => by
    have hnd_step : (ws ++ (w :: hit) ++ rest).Nodup ∧ (ws ++ hit ++ (w :: rest)).Nodup := by
      have h1 := List.nodup_append.mp hnd
      have h2 := List.nodup_append.mp h1.1
      obtain ⟨hw_nws, hws_nd⟩ := List.nodup_cons.mp h2.1
      have hw_nhit : w ∉ hit := fun h => h2.2.2 w (by simp) w h rfl
      have hw_nrest : w ∉ rest := fun h => h1.2.2 w (by simp) w h rfl
      constructor
      · refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hws_nd, List.nodup_cons.mpr ⟨hw_nhit, h2.2.1⟩, ?_⟩, h1.2.1, ?_⟩
        · intro a ha b hb he; subst he; rcases List.mem_cons.mp hb with rfl | hb
          · exact hw_nws ha
          · exact h2.2.2 a (List.mem_cons_of_mem _ ha) a hb rfl
        · intro a ha b hb he; subst he; rcases List.mem_append.mp ha with ha1 | ha2
          · exact h1.2.2 a (List.mem_append_left _ (List.mem_cons_of_mem _ ha1)) a hb rfl
          · rcases List.mem_cons.mp ha2 with rfl | ha2
            · exact hw_nrest hb
            · exact h1.2.2 a (List.mem_append_right _ ha2) a hb rfl
      · refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hws_nd, h2.2.1, fun a ha b hb he => h2.2.2 a (List.mem_cons_of_mem _ ha) b hb he⟩,
          List.nodup_cons.mpr ⟨hw_nrest, h1.2.1⟩, ?_⟩
        · intro a ha b hb he; subst he; rcases List.mem_cons.mp hb with rfl | hb
          · rcases List.mem_append.mp ha with ha1 | ha2
            · exact hw_nws ha1
            · exact hw_nhit ha2
          · rcases List.mem_append.mp ha with ha1 | ha2
            · exact h1.2.2 a (List.mem_append_left _ (List.mem_cons_of_mem _ ha1)) a hb rfl
            · exact h1.2.2 a (List.mem_append_right _ ha2) a hb rfl
    unfold partRem
    by_cases ha : anyEdge w act = true
    · simp only [ha, ↓reduceIte]
      obtain ⟨hnd', hlen', hmem', hhit'⟩ := partRem_spec act ws (w :: hit) rest hnd_step.1
      refine ⟨hnd', by simp only [List.length_cons] at hlen' ⊢; omega, fun z => ?_, fun z hz => ?_⟩
      · rw [hmem' z]; simp only [List.mem_cons]; tauto
      · rcases hhit' z hz with hzh | ⟨hzw, hza⟩
        · rcases List.mem_cons.mp hzh with rfl | hzh
          · exact Or.inr ⟨by simp, ha⟩
          · exact Or.inl hzh
        · exact Or.inr ⟨List.mem_cons_of_mem _ hzw, hza⟩
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hnd', hlen', hmem', hhit'⟩ := partRem_spec act ws hit (w :: rest) hnd_step.2
      refine ⟨hnd', by simp only [List.length_cons] at hlen' ⊢; omega, fun z => ?_, fun z hz => ?_⟩
      · rw [hmem' z]; simp only [List.mem_cons]; tauto
      · rcases hhit' z hz with hzh | ⟨hzw, hza⟩
        · exact Or.inl hzh
        · exact Or.inr ⟨List.mem_cons_of_mem _ hzw, hza⟩


theorem expandF_spec {U1 U2 : Finset ℕ} {U : List ℕ} (hdisj : Disjoint U1 U2)
    (Side : Finset ℕ) (hSide : Side = U1 ∨ Side = U2) :
    ∀ (fuel : ℕ) (es : List (ℕ × ℕ)) (front comp rem : List ℕ),
      (∀ p ∈ es, PureEdge U1 U2 U p) →
      (∀ w ∈ front ++ comp ++ rem, w ∈ U) →
      (front ++ comp ++ rem).Nodup →
      front ≠ [] →
      (∀ w ∈ front ++ comp, w ∈ Side) →
      let r := expandF fuel es front comp rem
      r.1 ≠ [] ∧ (r.1 ++ r.2.1).Nodup ∧
      r.1.length + r.2.1.length = front.length + comp.length + rem.length ∧
      (∀ w, w ∈ r.1 ∨ w ∈ r.2.1 ↔ w ∈ front ∨ w ∈ comp ∨ w ∈ rem) ∧
      (∀ w ∈ r.1, w ∈ Side) ∧
      (∀ p ∈ r.2.2, p ∈ es)
  | 0, es, front, comp, rem, _, _, hnd, hfne, hfc => by
    dsimp only [expandF]
    refine ⟨by intro h; exact hfne (List.append_eq_nil_iff.mp h).1, hnd, by simp, fun w => by simp [List.mem_append, or_assoc], hfc, fun _ h => h⟩
  | fuel + 1, es, front, comp, rem, hpure, hsubU, hnd, hfne, hfc => by
    unfold expandF; dsimp only
    have hcomp'_ne : front ++ comp ≠ [] := fun h => hfne (List.append_eq_nil_iff.mp h).1
    cases rem with
    | nil =>
      refine ⟨hcomp'_ne, by simpa using hnd, by simp, fun w => by simp [List.mem_append, or_assoc], hfc, fun _ h => h⟩
    | cons r0 rs =>
      set au := partEdges front es [] []
      obtain ⟨hau1, hau2⟩ := partEdges_spec front es [] []
      cases ha1 : au.1 with
      | nil =>
        dsimp only
        refine ⟨hcomp'_ne, hnd, by simp, fun w => by simp [List.mem_append, or_assoc], hfc,
          fun p hp => (hau2 p hp).resolve_left (by simp)⟩
      | cons e0 es0 =>
        dsimp only
        have hrem_nd : ((r0 :: rs) ++ [] ++ []).Nodup := by
          have := (List.nodup_append.mp hnd).2.1
          simpa using this
        have hpr := partRem_spec (e0 :: es0) (r0 :: rs) [] [] hrem_nd
        set hr := partRem (e0 :: es0) (r0 :: rs) [] []
        cases hhr1 : hr.1 with
        | nil =>
          refine ⟨hcomp'_ne, hnd, by simp, fun w => by simp [List.mem_append, or_assoc], hfc,
            fun p hp => (hau2 p hp).resolve_left (by simp)⟩
        | cons h0 hs0 =>
          have hhr1_side : ∀ w ∈ hr.1, w ∈ Side := by
            intro w hw
            have hw2 := (hpr.2.2.2 w hw).resolve_left (by simp)
            obtain ⟨p, hp_act, htouch_w⟩ := (anyEdge_iff w (e0 :: es0)).mp hw2.2
            have hp_act' : p ∈ au.1 := ha1 ▸ hp_act
            obtain ⟨hp_es, htf⟩ := (hau1 p hp_act').resolve_left (by simp)
            obtain ⟨u, hu_f, htouch_u⟩ := (touches_iff p.1 p.2 front).mp htf
            have hu_U : u ∈ U := hsubU u (List.mem_append_left _ (List.mem_append_left _ hu_f))
            have hw_U : w ∈ U := hsubU w (List.mem_append_right _ hw2.1)
            have hu_Side : u ∈ Side := hfc u (List.mem_append_left _ hu_f)
            rcases hpure p hp_es with hp1 | hp2
            · rcases hSide with rfl | rfl
              · exact hp1 w hw_U htouch_w
              · exact absurd (hp1 u hu_U htouch_u) (Finset.disjoint_right.mp hdisj hu_Side)
            · rcases hSide with rfl | rfl
              · exact absurd (hp2 u hu_U htouch_u) (Finset.disjoint_left.mp hdisj hu_Side)
              · exact hp2 w hw_U htouch_w
          have hnd_next : (hr.1 ++ (front ++ comp) ++ hr.2).Nodup := by
            have h1 := List.nodup_append.mp hnd
            have hhr_nd := List.nodup_append.mp hpr.1
            have hmem_hr : ∀ z, z ∈ hr.1 ∨ z ∈ hr.2 ↔ z ∈ r0 :: rs := fun z => by
              have := hpr.2.2.1 z; simpa using this
            refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hhr_nd.1, h1.1, ?_⟩, hhr_nd.2.1, ?_⟩
            · intro a ha b hb he; subst he
              exact h1.2.2 a hb a ((hmem_hr a).mp (Or.inl ha)) rfl
            · intro a ha b hb he; subst he
              rcases List.mem_append.mp ha with ha1' | ha2'
              · exact hhr_nd.2.2 a ha1' a hb rfl
              · exact h1.2.2 a ha2' a ((hmem_hr a).mp (Or.inr hb)) rfl
          have hsubU_next : ∀ w ∈ hr.1 ++ (front ++ comp) ++ hr.2, w ∈ U := by
            intro w hw
            simp only [List.mem_append] at hw
            rcases hw with (hw1 | hw2) | hw3
            · have := (hpr.2.2.1 w).mp (Or.inl hw1); apply hsubU; simp only [List.mem_append]; tauto
            · apply hsubU; simp only [List.mem_append]; tauto
            · have := (hpr.2.2.1 w).mp (Or.inr hw3); apply hsubU; simp only [List.mem_append]; tauto
          have ih := expandF_spec hdisj Side hSide fuel au.2 hr.1 (front ++ comp) hr.2
            (fun p hp => hpure p ((hau2 p hp).resolve_left (by simp))) hsubU_next hnd_next
            (by rw [hhr1]; simp)
            (fun w hw => by rcases List.mem_append.mp hw with h1 | h2; exact hhr1_side w h1; exact hfc w h2)
          rw [hhr1] at ih
          refine ⟨ih.1, ih.2.1, ?_, fun w => ?_, ih.2.2.2.2.1, fun p hp => (hau2 p (ih.2.2.2.2.2 p hp)).resolve_left (by simp)⟩
          · have hlen_hr := hpr.2.1; simp only [List.length_nil, Nat.add_zero] at hlen_hr
            have hlen_ih := ih.2.2.1; simp only [List.length_append] at hlen_ih
            rw [hhr1] at hlen_hr; simp only [List.length_cons] at hlen_hr hlen_ih ⊢; omega
          · rw [ih.2.2.2.1 w, ← hhr1]; simp only [List.mem_append]
            have hm := hpr.2.2.1 w; simp only [List.not_mem_nil, or_false] at hm; tauto


theorem splitComps_spec {U1 U2 : Finset ℕ} {U : List ℕ} (hdisj : Disjoint U1 U2) (hun : U1 ∪ U2 = U.toFinset) :
    ∀ (fuel : ℕ) (es : List (ℕ × ℕ)) (L : List ℕ),
      L.length ≤ fuel → L.Nodup → (∀ w ∈ L, w ∈ U) → (∀ p ∈ es, PureEdge U1 U2 U p) →
      let cs := splitComps fuel es L
      (∀ c ∈ cs, c ≠ [] ∧ ((∀ w ∈ c, w ∈ U1) ∨ (∀ w ∈ c, w ∈ U2))) ∧
      cs.flatten.Nodup ∧ (∀ w, w ∈ cs.flatten ↔ w ∈ L)
  | _, _, [], _, _, _, _ => ⟨by simp [splitComps], by simp [splitComps], by simp [splitComps]⟩
  | 0, _, x :: xs, hle, _, _, _ => by simp at hle
  | fuel + 1, es, x :: xs, hle, hnd, hsubU, hpure => by
    unfold splitComps; dsimp only
    have hxU : x ∈ U1 ∪ U2 := hun ▸ List.mem_toFinset.mpr (hsubU x (by simp))
    set cr := expandF (xs.length + 1) es [x] [] xs
    have hcr : cr.1 ≠ [] ∧ (cr.1 ++ cr.2.1).Nodup ∧
        cr.1.length + cr.2.1.length = [x].length + ([] : List ℕ).length + xs.length ∧
        (∀ w, w ∈ cr.1 ∨ w ∈ cr.2.1 ↔ w ∈ [x] ∨ w ∈ ([] : List ℕ) ∨ w ∈ xs) ∧
        ((∀ w ∈ cr.1, w ∈ U1) ∨ (∀ w ∈ cr.1, w ∈ U2)) ∧
        (∀ p ∈ cr.2.2, p ∈ es) := by
      rcases Finset.mem_union.mp hxU with hx1 | hx2
      · have r := expandF_spec hdisj U1 (Or.inl rfl) (xs.length + 1) es [x] [] xs hpure
          (by simpa using hsubU) (by simpa using hnd) (by simp) (by simpa using hx1)
        exact ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, Or.inl r.2.2.2.2.1, r.2.2.2.2.2⟩
      · have r := expandF_spec hdisj U2 (Or.inr rfl) (xs.length + 1) es [x] [] xs hpure
          (by simpa using hsubU) (by simpa using hnd) (by simp) (by simpa using hx2)
        exact ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, Or.inr r.2.2.2.2.1, r.2.2.2.2.2⟩
    obtain ⟨hcne, hcr_nd, hcr_len, hcr_mem, hc_side, hes'⟩ := hcr
    have hc_pos : 1 ≤ cr.1.length := List.length_pos_of_ne_nil hcne
    have hrem_le : cr.2.1.length ≤ fuel := by simp only [List.length_cons, List.length_nil] at hle hcr_len; omega
    have hcr_nd2 := List.nodup_append.mp hcr_nd
    have hrem_subU : ∀ w ∈ cr.2.1, w ∈ U := fun w hw => by
      have hm := (hcr_mem w).mp (Or.inr hw)
      simp only [List.mem_singleton, List.not_mem_nil, false_or] at hm
      exact hsubU w (by simp [hm])
    obtain ⟨ih1, ih2, ih3⟩ := splitComps_spec hdisj hun fuel cr.2.2 cr.2.1 hrem_le hcr_nd2.2.1 hrem_subU (fun p hp => hpure p (hes' p hp))
    refine ⟨fun c hc => ?_, ?_, fun w => ?_⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hcne, hc_side⟩
      · exact ih1 c hc
    · rw [List.flatten_cons]
      refine List.nodup_append.mpr ⟨hcr_nd2.1, ih2, fun a ha b hb he => ?_⟩
      subst he
      exact hcr_nd2.2.2 a ha a ((ih3 a).mp hb) rfl
    · rw [List.flatten_cons, List.mem_append, ih3 w, hcr_mem w]
      simp


theorem trySplits_sound {chk : List ℕ → List ℕ → Bool} {U1 U2 : Finset ℕ}
    (hdisj : Disjoint U1 U2) (h2ne : U2.Nonempty)
    (hchk : ∀ L1 L2 : List ℕ, L1.Nodup → L2.Nodup → L1.toFinset = U1 → L2.toFinset = U2 → chk L1 L2 = true) :
    ∀ (cs : List (List ℕ)) (A1 A2 : List ℕ),
      (A1 ++ A2 ++ cs.flatten).Nodup →
      (∀ w ∈ A1, w ∈ U1) → (∀ w ∈ A2, w ∈ U2) →
      (∀ c ∈ cs, (∀ w ∈ c, w ∈ U1) ∨ (∀ w ∈ c, w ∈ U2)) →
      (∀ w, w ∈ U1 ∨ w ∈ U2 ↔ w ∈ A1 ∨ w ∈ A2 ∨ w ∈ cs.flatten) →
      trySplits chk A1 A2 cs = true
  | [], A1, A2, hnd, h1, h2, _, hcov => by
    have hnd2 := List.nodup_append.mp (by simpa using hnd : (A1 ++ A2).Nodup)
    have hA1 : A1.toFinset = U1 := by
      ext w; simp only [List.mem_toFinset]
      constructor
      · exact h1 w
      · intro hw
        rcases (hcov w).mp (Or.inl hw) with ha | ha | hc
        · exact ha
        · exact absurd (h2 w ha) (Finset.disjoint_left.mp hdisj hw)
        · simp at hc
    have hA2 : A2.toFinset = U2 := by
      ext w; simp only [List.mem_toFinset]
      constructor
      · exact h2 w
      · intro hw
        rcases (hcov w).mp (Or.inr hw) with ha | ha | hc
        · exact absurd (h1 w ha) (Finset.disjoint_right.mp hdisj hw)
        · exact ha
        · simp at hc
    unfold trySplits
    cases hA2e : A2 with
    | nil =>
      obtain ⟨w, hw⟩ := h2ne
      rw [← hA2, hA2e] at hw; simp at hw
    | cons a2 t2 =>
      subst hA2e
      exact hchk A1 (a2 :: t2) hnd2.1 hnd2.2.1 hA1 hA2
  | c :: rest, A1, A2, hnd, h1, h2, hcs, hcov => by
    rw [List.flatten_cons] at hnd hcov
    have hnd_p : (c ++ A1 ++ A2 ++ rest.flatten).Nodup ∧ (A1 ++ (c ++ A2) ++ rest.flatten).Nodup := by
      have ha := List.nodup_append.mp hnd
      have hb := List.nodup_append.mp ha.1
      have hc := List.nodup_append.mp ha.2.1
      constructor
      · refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hc.1, hb.1, ?_⟩, hb.2.1, ?_⟩, hc.2.1, ?_⟩
        · intro x hx y hy he; subst he; exact ha.2.2 x (List.mem_append_left _ hy) x (List.mem_append_left _ hx) rfl
        · intro x hx y hy he; subst he; rcases List.mem_append.mp hx with hx1 | hx2
          · exact ha.2.2 x (List.mem_append_right _ hy) x (List.mem_append_left _ hx1) rfl
          · exact hb.2.2 x hx2 x hy rfl
        · intro x hx y hy he; subst he; rcases List.mem_append.mp hx with hx1 | hx2
          · rcases List.mem_append.mp hx1 with hx11 | hx12
            · exact hc.2.2 x hx11 x hy rfl
            · exact ha.2.2 x (List.mem_append_left _ hx12) x (List.mem_append_right _ hy) rfl
          · exact ha.2.2 x (List.mem_append_right _ hx2) x (List.mem_append_right _ hy) rfl
      · refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hb.1, List.nodup_append.mpr ⟨hc.1, hb.2.1, ?_⟩, ?_⟩, hc.2.1, ?_⟩
        · intro x hx y hy he; subst he; exact ha.2.2 x (List.mem_append_right _ hy) x (List.mem_append_left _ hx) rfl
        · intro x hx y hy he; subst he; rcases List.mem_append.mp hy with hy1 | hy2
          · exact ha.2.2 x (List.mem_append_left _ hx) x (List.mem_append_left _ hy1) rfl
          · exact hb.2.2 x hx x hy2 rfl
        · intro x hx y hy he; subst he; rcases List.mem_append.mp hx with hx1 | hx2
          · exact ha.2.2 x (List.mem_append_left _ hx1) x (List.mem_append_right _ hy) rfl
          · rcases List.mem_append.mp hx2 with hx21 | hx22
            · exact hc.2.2 x hx21 x hy rfl
            · exact ha.2.2 x (List.mem_append_right _ hx22) x (List.mem_append_right _ hy) rfl
    unfold trySplits; simp only [Bool.or_eq_true]
    rcases hcs c (by simp) with hc1 | hc2
    · left
      exact trySplits_sound hdisj h2ne hchk rest (c ++ A1) A2 hnd_p.1
        (fun w hw => by rcases List.mem_append.mp hw with h | h; exact hc1 w h; exact h1 w h)
        h2 (fun d hd => hcs d (by simp [hd]))
        (fun w => by rw [hcov w]; simp only [List.mem_append]; tauto)
    · right
      exact trySplits_sound hdisj h2ne hchk rest A1 (c ++ A2) hnd_p.2
        h1 (fun w hw => by rcases List.mem_append.mp hw with h | h; exact hc2 w h; exact h2 w h)
        (fun d hd => hcs d (by simp [hd]))
        (fun w => by rw [hcov w]; simp only [List.mem_append]; tauto)


theorem foldOr_testBit (p1m b : ℕ) : ∀ (L : List ℕ) (acc a : ℕ),
    (foldOr p1m (2 ^ b) L acc).testBit a = true ↔
      acc.testBit a = true ∨ (p1m.testBit a = true ∧ ∃ w ∈ L, w.testBit b = false ∧ w.testBit a = true)
  | [], acc, a => by simp [foldOr]
  | w :: ws, acc, a => by
    unfold foldOr
    simp only [forceNat_eq]
    by_cases hwb : Nat.beq (w &&& 2 ^ b) 0 = true
    · simp only [hwb, ↓reduceIte]
      have hwb0 : w.testBit b = false := (and_two_pow_eq_zero_iff w b).mp hwb
      rw [foldOr_testBit p1m b ws (acc ||| (w &&& p1m)) a]
      simp only [Nat.testBit_lor, Nat.testBit_land, Bool.or_eq_true, Bool.and_eq_true, List.mem_cons]
      constructor
      · rintro ((ha | ⟨hwa, hpa⟩) | ⟨hpa, u, hu, hub, hua⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨hpa, w, Or.inl rfl, hwb0, hwa⟩
        · exact Or.inr ⟨hpa, u, Or.inr hu, hub, hua⟩
      · rintro (ha | ⟨hpa, u, rfl | hu, hub, hua⟩)
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr ⟨hua, hpa⟩)
        · exact Or.inr ⟨hpa, u, hu, hub, hua⟩
    · simp only [hwb, Bool.false_eq_true, ↓reduceIte]
      have hwb1 : w.testBit b = true := by
        cases hv : w.testBit b with | true => rfl | false => exact absurd ((and_two_pow_eq_zero_iff w b).mpr hv) hwb
      rw [foldOr_testBit p1m b ws acc a]
      simp only [List.mem_cons]
      constructor
      · rintro (ha | ⟨hpa, u, hu, hub, hua⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨hpa, u, Or.inr hu, hub, hua⟩
      · rintro (ha | ⟨hpa, u, rfl | hu, hub, hua⟩)
        · exact Or.inl ha
        · rw [hwb1] at hub; simp at hub
        · exact Or.inr ⟨hpa, u, hu, hub, hua⟩


theorem bitsRep_insert {m b : ℕ} {bs : List ℕ} (hb : b < 16) (hr : BitsRep m bs) :
    BitsRep (m ||| 2 ^ b) (2 ^ b :: bs) := by
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, hr.1 i]
    constructor
    · rintro (hm | rfl)
      · exact Or.inr hm
      · exact Or.inl rfl
    · rintro (heq | hm)
      · exact Or.inr (Nat.pow_right_injective (by decide : 1 < 2) heq).symm
      · exact Or.inl hm
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb, rfl⟩
    · exact hr.2 x hx


theorem splitP_spec {p1m f1 f2 : ℕ} {L1 L2 : List ℕ}
    (hm1 : ∀ a b, (∀ w ∈ L1, w.testBit a = true → w.testBit b = true) → f1.testBit a = true → f1.testBit b = true)
    (hm2 : ∀ a b, (∀ w ∈ L2, w.testBit a = true → w.testBit b = true) → f2.testBit a = true → f2.testBit b = true)
    (hp1 : ∀ a, p1m.testBit a = true → (f1 &&& f2).testBit a = true) :
    ∀ (bs : List ℕ) (m1 : ℕ) (b1 : List ℕ) (m2 : ℕ) (b2 : List ℕ) (h1 h2 : Bool),
      (∀ x ∈ bs, ∃ b < 16, x = 2 ^ b ∧ (f1 &&& f2).testBit b = false) →
      BitsRep m1 b1 → BitsRep m2 b2 →
      (∀ b, m1.testBit b = true → f1.testBit b = false) →
      (∀ b, m2.testBit b = true → f2.testBit b = false) →
      ∃ m1' b1' m2' b2' h1' h2',
        splitP p1m L1 L2 bs m1 b1 m2 b2 h1 h2 = some ((m1', b1'), (m2', b2'), h1', h2') ∧
        BitsRep m1' b1' ∧ BitsRep m2' b2' ∧
        (∀ b, m1'.testBit b = true → f1.testBit b = false) ∧
        (∀ b, m2'.testBit b = true → f2.testBit b = false) ∧
        (h1 = true ∨ (∃ b, 2 ^ b ∈ bs ∧ f1.testBit b = false) → h1' = true) ∧
        (h2 = true ∨ (∃ b, 2 ^ b ∈ bs ∧ f2.testBit b = false) → h2' = true)
  | [], m1, b1, m2, b2, h1, h2, _, hr1, hr2, hf1, hf2 =>
    ⟨m1, b1, m2, b2, h1, h2, rfl, hr1, hr2, hf1, hf2, fun h => h.elim id (fun ⟨_, hm, _⟩ => by simp at hm),
     fun h => h.elim id (fun ⟨_, hm, _⟩ => by simp at hm)⟩
  | x :: rest, m1, b1, m2, b2, h1, h2, hbs, hr1, hr2, hf1, hf2 => by
    obtain ⟨b, hb16, rfl, hfb⟩ := hbs x (by simp)
    have hfb_or : f1.testBit b = false ∨ f2.testBit b = false := by
      simp only [Nat.testBit_land, Bool.and_eq_false_iff] at hfb; exact hfb
    have hs1_of : f1.testBit b = false → Nat.beq (foldOr p1m (2 ^ b) L1 0) p1m = true := by
      intro h10; rw [Nat.beq_eq]; apply Nat.eq_of_testBit_eq; intro a
      cases hpa : p1m.testBit a with
      | false =>
        cases ho : (foldOr p1m (2 ^ b) L1 0).testBit a with
        | false => rfl
        | true => have := (foldOr_testBit p1m b L1 0 a).mp ho; simp [hpa] at this
      | true =>
        apply (foldOr_testBit p1m b L1 0 a).mpr; right; refine ⟨hpa, ?_⟩
        by_contra hno
        have hall : ∀ w ∈ L1, w.testBit a = true → w.testBit b = true := by
          intro w hw hwa; cases hwb : w.testBit b with | true => rfl | false => exact absurd ⟨w, hw, hwb, hwa⟩ hno
        have hfa := hp1 a hpa; simp only [Nat.testBit_land, Bool.and_eq_true] at hfa
        have := hm1 a b hall hfa.1; rw [h10] at this; simp at this
    have hs2_of : f2.testBit b = false → Nat.beq (foldOr p1m (2 ^ b) L2 0) p1m = true := by
      intro h20; rw [Nat.beq_eq]; apply Nat.eq_of_testBit_eq; intro a
      cases hpa : p1m.testBit a with
      | false =>
        cases ho : (foldOr p1m (2 ^ b) L2 0).testBit a with
        | false => rfl
        | true => have := (foldOr_testBit p1m b L2 0 a).mp ho; simp [hpa] at this
      | true =>
        apply (foldOr_testBit p1m b L2 0 a).mpr; right; refine ⟨hpa, ?_⟩
        by_contra hno
        have hall : ∀ w ∈ L2, w.testBit a = true → w.testBit b = true := by
          intro w hw hwa; cases hwb : w.testBit b with | true => rfl | false => exact absurd ⟨w, hw, hwb, hwa⟩ hno
        have hfa := hp1 a hpa; simp only [Nat.testBit_land, Bool.and_eq_true] at hfa
        have := hm2 a b hall hfa.2; rw [h20] at this; simp at this
    set s1 := Nat.beq (foldOr p1m (2 ^ b) L1 0) p1m
    set s2 := Nat.beq (foldOr p1m (2 ^ b) L2 0) p1m
    have hs_or : s1 = true ∨ s2 = true := hfb_or.imp hs1_of hs2_of
    have hnot_both : (!s1 && !s2) = false := by rcases hs_or with h | h <;> simp [h]
    have h1_next : BitsRep (if s2 then m1 else m1 ||| 2 ^ b) (if s2 then b1 else 2 ^ b :: b1) ∧
        (∀ j, (if s2 then m1 else m1 ||| 2 ^ b).testBit j = true → f1.testBit j = false) := by
      cases hs2v : s2 with
      | true => exact ⟨hr1, hf1⟩
      | false =>
        have h10 : f1.testBit b = false := hfb_or.resolve_right (fun h20 => by have := hs2_of h20; rw [hs2v] at this; simp at this)
        refine ⟨bitsRep_insert hb16 hr1, fun j hj => ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hj
        rcases hj with hjm | rfl
        · exact hf1 j hjm
        · exact h10
    have h2_next : BitsRep (if s1 then m2 else m2 ||| 2 ^ b) (if s1 then b2 else 2 ^ b :: b2) ∧
        (∀ j, (if s1 then m2 else m2 ||| 2 ^ b).testBit j = true → f2.testBit j = false) := by
      cases hs1v : s1 with
      | true => exact ⟨hr2, hf2⟩
      | false =>
        have h20 : f2.testBit b = false := hfb_or.resolve_left (fun h10 => by have := hs1_of h10; rw [hs1v] at this; simp at this)
        refine ⟨bitsRep_insert hb16 hr2, fun j hj => ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hj
        rcases hj with hjm | rfl
        · exact hf2 j hjm
        · exact h20
    obtain ⟨m1', b1', m2', b2', h1', h2', hrec, hr1', hr2', hf1', hf2', hh1', hh2'⟩ :=
      splitP_spec hm1 hm2 hp1 rest _ _ _ _ (h1 || s1) (h2 || s2)
        (fun y hy => hbs y (by simp [hy])) h1_next.1 h2_next.1 h1_next.2 h2_next.2
    unfold splitP; simp only [forceNat_eq]
    rw [show (!s1 && !s2) = false from hnot_both]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨m1', b1', m2', b2', h1', h2', hrec, hr1', hr2', hf1', hf2', ?_, ?_⟩
    · rintro (hh | ⟨j, hj, hfj⟩)
      · exact hh1' (Or.inl (by simp [hh]))
      · rcases List.mem_cons.mp hj with heq | hjr
        · have hjb : j = b := Nat.pow_right_injective (by decide : 1 < 2) heq
          subst hjb; exact hh1' (Or.inl (by simp [hs1_of hfj]))
        · exact hh1' (Or.inr ⟨j, hjr, hfj⟩)
    · rintro (hh | ⟨j, hj, hfj⟩)
      · exact hh2' (Or.inl (by simp [hh]))
      · rcases List.mem_cons.mp hj with heq | hjr
        · have hjb : j = b := Nat.pow_right_injective (by decide : 1 < 2) heq
          subst hjb; exact hh2' (Or.inl (by simp [hs2_of hfj]))
        · exact hh2' (Or.inr ⟨j, hjr, hfj⟩)


theorem bitsRep_zero : BitsRep 0 [] := ⟨fun _ => by simp, fun _ h => by simp at h⟩

theorem xor65535_lt {w : ℕ} (hw : w < 65536) : 65535 ^^^ w < 65536 :=
  Nat.xor_lt_two_pow (n := 16) (by decide) hw

theorem xor65535_inv {w : ℕ} (hw : w < 65536) : 65535 ^^^ (65535 ^^^ w) = w := by
  apply Nat.eq_of_testBit_eq; intro b
  by_cases hb : b < 16
  · rw [xor_65535_testBit hb, xor_65535_testBit hb, Bool.not_not]
  · rw [testBit_mask_ge16 _ b (xor65535_lt (xor65535_lt hw)) (by omega), testBit_mask_ge16 _ b hw (by omega)]

theorem xor65535_inj {a b : ℕ} (ha : a < 65536) (hb : b < 65536) (h : 65535 ^^^ a = 65535 ^^^ b) : a = b := by
  rw [← xor65535_inv ha, h, xor65535_inv hb]

theorem xor65535_and {a b : ℕ} (ha : a < 65536) (hb : b < 65536) :
    65535 ^^^ (a &&& b) = (65535 ^^^ a) ||| (65535 ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 16
  · simp [xor_65535_testBit hi, Nat.testBit_land, Nat.testBit_lor, Bool.not_and]
  · rw [testBit_mask_ge16 _ i (xor65535_lt (Nat.and_lt_two_pow (n := 16) a hb)) (by omega),
        testBit_mask_ge16 _ i (Nat.or_lt_two_pow (n := 16) (xor65535_lt ha) (xor65535_lt hb)) (by omega)]

theorem xor65535_or {a b : ℕ} (ha : a < 65536) (hb : b < 65536) :
    65535 ^^^ (a ||| b) = (65535 ^^^ a) &&& (65535 ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 16
  · simp [xor_65535_testBit hi, Nat.testBit_land, Nat.testBit_lor, Bool.not_or]
  · rw [testBit_mask_ge16 _ i (xor65535_lt (Nat.or_lt_two_pow (n := 16) ha hb)) (by omega),
        testBit_mask_ge16 _ i (Nat.and_lt_two_pow (n := 16) _ (xor65535_lt hb)) (by omega)]

theorem isRO_compl : ∀ (n : ℕ) {U : Finset ℕ} {f : ℕ},
    (∀ w ∈ U, w < 65536) → IsRO n U f → IsRO n (U.image (65535 ^^^ ·)) (65535 ^^^ f) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U f hlt hro
    match n with
    | 0 => unfold IsRO at hro; exact hro.elim
    | 1 => unfold IsRO at hro ⊢; rw [hro, Finset.image_singleton]
    | m + 2 =>
      unfold IsRO at hro ⊢
      obtain ⟨o, U1, U2, f1, f2, h1le, h2le, hdisj, hun, h1ne, h2ne, hsum, hr1, hr2, rfl⟩ := hro
      have hlt1 : ∀ w ∈ U1, w < 65536 := fun w hw => hlt w (hun ▸ Finset.mem_union_left _ hw)
      have hlt2 : ∀ w ∈ U2, w < 65536 := fun w hw => hlt w (hun ▸ Finset.mem_union_right _ hw)
      have hf1 : f1 < 65536 := isRO_lt U1.card hlt1 hr1
      have hf2 : f2 < 65536 := isRO_lt U2.card hlt2 hr2
      have hinj1 : Set.InjOn (65535 ^^^ ·) (U1 : Set ℕ) := fun a ha b hb h => xor65535_inj (hlt1 a ha) (hlt1 b hb) h
      have hinj2 : Set.InjOn (65535 ^^^ ·) (U2 : Set ℕ) := fun a ha b hb h => xor65535_inj (hlt2 a ha) (hlt2 b hb) h
      have hc1 : (U1.image (65535 ^^^ ·)).card = U1.card := Finset.card_image_of_injOn hinj1
      have hc2 : (U2.image (65535 ^^^ ·)).card = U2.card := Finset.card_image_of_injOn hinj2
      have hdisj' : Disjoint (U1.image (65535 ^^^ ·)) (U2.image (65535 ^^^ ·)) := by
        rw [Finset.disjoint_left]; intro y hy1 hy2
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hy2
        exact Finset.disjoint_left.mp hdisj ha ((xor65535_inj (hlt2 b hb) (hlt1 a ha) hba) ▸ hb)
      fin_cases o
      · refine ⟨1, U1.image (65535 ^^^ ·), U2.image (65535 ^^^ ·), 65535 ^^^ f1, 65535 ^^^ f2,
          by omega, by omega, hdisj', by rw [← Finset.image_union, hun], h1ne.image _, h2ne.image _, by omega,
          ?_, ?_, xor65535_and hf1 hf2⟩
        · rw [hc1]; exact ih U1.card (by omega) hlt1 hr1
        · rw [hc2]; exact ih U2.card (by omega) hlt2 hr2
      · refine ⟨0, U1.image (65535 ^^^ ·), U2.image (65535 ^^^ ·), 65535 ^^^ f1, 65535 ^^^ f2,
          by omega, by omega, hdisj', by rw [← Finset.image_union, hun], h1ne.image _, h2ne.image _, by omega,
          ?_, ?_, xor65535_or hf1 hf2⟩
        · rw [hc1]; exact ih U1.card (by omega) hlt1 hr1
        · rw [hc2]; exact ih U2.card (by omega) hlt2 hr2

theorem complList_eq : ∀ U : List ℕ, complList U = U.map (65535 ^^^ ·)
  | [] => rfl
  | w :: ws => by simp only [complList, forceNat_eq, List.map_cons, complList_eq ws]

theorem complList_nodup {U : List ℕ} (hU : ∀ w ∈ U, w < 65536) (hnd : U.Nodup) : (complList U).Nodup := by
  rw [complList_eq]
  exact hnd.map_on (fun a ha b hb h => xor65535_inj (hU a ha) (hU b hb) h)

theorem complList_lt {U : List ℕ} (hU : ∀ w ∈ U, w < 65536) : ∀ w ∈ complList U, w < 65536 := by
  rw [complList_eq]; intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
  exact xor65535_lt (hU x hx)

theorem canROSide_sound {sub : List ℕ → ℕ → List ℕ → Bool}
    {U : List ℕ} {p1m : ℕ} {p0Bits : List ℕ} {isRoot : Bool}
    {U1 U2 : Finset ℕ} {f1 f2 : ℕ}
    (hnd : U.Nodup) (hdisj : Disjoint U1 U2) (hun : U1 ∪ U2 = U.toFinset)
    (h1ne : U1.Nonempty) (h2ne : U2.Nonempty)
    (hr1 : IsRO U1.card U1 f1) (hr2 : IsRO U2.card U2 f2)
    (hp1 : ∀ a, p1m.testBit a = true → (f1 &&& f2).testBit a = true)
    (hbs0 : ∀ x ∈ p0Bits, ∃ b < 16, x = 2 ^ b ∧ (f1 &&& f2).testBit b = false)
    (hroot : isRoot = true → (∃ b, 2 ^ b ∈ p0Bits ∧ f1.testBit b = false) ∧ (∃ b, 2 ^ b ∈ p0Bits ∧ f2.testBit b = false))
    (hsub : ∀ (L : List ℕ) (S : Finset ℕ) (g m : ℕ) (bs : List ℕ),
      (S = U1 ∧ g = f1 ∨ S = U2 ∧ g = f2) → L.Nodup → L.toFinset = S →
      BitsRep m bs → (∀ b, m.testBit b = true → g.testBit b = false) → sub L m bs = true) :
    canROSide sub U p1m p0Bits isRoot = true := by
  unfold canROSide
  obtain ⟨u0, hbreq, hpure⟩ := buildReq_spec hnd hun (isRO_mono U1.card hr1) (isRO_mono U2.card hr2) hp1 p0Bits
    (fun x hx => by obtain ⟨b, _, rfl, hf⟩ := hbs0 x hx; exact ⟨b, rfl, hf⟩)
  rw [hbreq]; dsimp only
  obtain ⟨hcs_spec, hcs_nd, hcs_mem⟩ := splitComps_spec hdisj hun U.length u0 U (le_refl _) hnd (fun _ h => h) hpure
  cases hcs : splitComps U.length u0 U with
  | nil =>
    obtain ⟨w, hw1⟩ := h1ne
    have := (hcs_mem w).mpr (List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ hw1))
    rw [hcs] at this; simp at this
  | cons c0 cs =>
    cases cs with
    | nil =>
      have hc0_all : ∀ w, w ∈ c0 ↔ w ∈ U := fun w => by have := hcs_mem w; rw [hcs] at this; simpa using this
      rcases (hcs_spec c0 (by rw [hcs]; simp)).2 with hsub1 | hsub2
      · obtain ⟨w, hw2⟩ := h2ne
        exact absurd (hsub1 w ((hc0_all w).mpr (List.mem_toFinset.mp (hun ▸ Finset.mem_union_right _ hw2)))) (Finset.disjoint_right.mp hdisj hw2)
      · obtain ⟨w, hw1⟩ := h1ne
        exact absurd (hsub2 w ((hc0_all w).mpr (List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ hw1)))) (Finset.disjoint_left.mp hdisj hw1)
    | cons c1 cs' =>
      dsimp only
      have hrun : ∀ (S1 S2 : Finset ℕ) (g1 g2 : ℕ),
          Disjoint S1 S2 → S1 ∪ S2 = U.toFinset → S2.Nonempty →
          IsRO S1.card S1 g1 → IsRO S2.card S2 g2 →
          g1 &&& g2 = f1 &&& f2 →
          (S1 = U1 ∧ g1 = f1 ∨ S1 = U2 ∧ g1 = f2) →
          (S2 = U1 ∧ g2 = f1 ∨ S2 = U2 ∧ g2 = f2) →
          (isRoot = true → (∃ b, 2 ^ b ∈ p0Bits ∧ g1.testBit b = false) ∧ (∃ b, 2 ^ b ∈ p0Bits ∧ g2.testBit b = false)) →
          (∀ w ∈ c0, w ∈ S1) →
          (∀ c ∈ c1 :: cs', (∀ w ∈ c, w ∈ S1) ∨ (∀ w ∈ c, w ∈ S2)) →
          trySplits (fun L1 L2 =>
            match splitP p1m L1 L2 p0Bits 0 [] 0 [] false false with
            | none => false
            | some ((m1, b1), (m2, b2), h1, h2) =>
              if isRoot && (!h1 || !h2) then false
              else sub L1 m1 b1 && sub L2 m2 b2) c0 [] (c1 :: cs') = true := by
        intro S1 S2 g1 g2 hdj hunS h2neS hrg1 hrg2 hgand hS1 hS2 hrt hc0S hcsS
        apply trySplits_sound hdj h2neS _ (c1 :: cs') c0 []
        · have := hcs_nd; rw [hcs, List.flatten_cons] at this; simpa using this
        · exact hc0S
        · simp
        · exact hcsS
        · intro w; rw [← Finset.mem_union, hunS, List.mem_toFinset, ← hcs_mem w, hcs, List.flatten_cons, List.mem_append]; simp
        · intro L1 L2 hL1nd hL2nd hL1eq hL2eq
          have hmL1 : ∀ a b, (∀ w ∈ L1, w.testBit a = true → w.testBit b = true) → g1.testBit a = true → g1.testBit b = true :=
            fun a b h => isRO_mono S1.card hrg1 a b (fun w hw => h w (List.mem_toFinset.mp (hL1eq.symm ▸ hw)))
          have hmL2 : ∀ a b, (∀ w ∈ L2, w.testBit a = true → w.testBit b = true) → g2.testBit a = true → g2.testBit b = true :=
            fun a b h => isRO_mono S2.card hrg2 a b (fun w hw => h w (List.mem_toFinset.mp (hL2eq.symm ▸ hw)))
          have hp1g : ∀ a, p1m.testBit a = true → (g1 &&& g2).testBit a = true := fun a ha => hgand ▸ hp1 a ha
          have hbsg : ∀ x ∈ p0Bits, ∃ b < 16, x = 2 ^ b ∧ (g1 &&& g2).testBit b = false := fun x hx => by
            obtain ⟨b, hb16, rfl, hf⟩ := hbs0 x hx; exact ⟨b, hb16, rfl, hgand ▸ hf⟩
          obtain ⟨m1', b1', m2', b2', h1', h2', hsp, hmr1, hmr2, hfg1, hfg2, hh1', hh2'⟩ :=
            splitP_spec hmL1 hmL2 hp1g p0Bits 0 [] 0 [] false false hbsg bitsRep_zero bitsRep_zero (by simp) (by simp)
          rw [hsp]; dsimp only
          have hcond : (isRoot && (!h1' || !h2')) = false := by
            cases isRoot with
            | false => rfl
            | true =>
              obtain ⟨he1, he2⟩ := hrt rfl
              rw [hh1' (Or.inr he1), hh2' (Or.inr he2)]; rfl
          rw [hcond]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
          exact ⟨hsub L1 S1 g1 m1' b1' hS1 hL1nd hL1eq hmr1 hfg1,
                 hsub L2 S2 g2 m2' b2' hS2 hL2nd hL2eq hmr2 hfg2⟩
      rcases (hcs_spec c0 (by rw [hcs]; simp)).2 with hc0_1 | hc0_2
      · exact hrun U1 U2 f1 f2 hdisj hun h2ne hr1 hr2 rfl (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hroot hc0_1
          (fun c hc => (hcs_spec c (by rw [hcs]; exact List.mem_cons_of_mem _ hc)).2)
      · exact hrun U2 U1 f2 f1 hdisj.symm (by rw [Finset.union_comm, hun]) h1ne hr2 hr1 (Nat.land_comm f2 f1)
          (Or.inr ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (fun hr => (hroot hr).symm) hc0_2
          (fun c hc => ((hcs_spec c (by rw [hcs]; exact List.mem_cons_of_mem _ hc)).2).symm)

theorem isRO_imp_canRO : ∀ (fuel : ℕ) (U : List ℕ) (p1m p0m : ℕ) (p1Bits p0Bits : List ℕ) (f : ℕ),
    (∀ w ∈ U, w < 65536) → U.Nodup → U.length ≤ fuel →
    BitsRep p1m p1Bits → BitsRep p0m p0Bits →
    (∀ a, p1m.testBit a = true → f.testBit a = true) →
    (∀ b, p0m.testBit b = true → f.testBit b = false) →
    IsRO U.toFinset.card U.toFinset f →
    canRO fuel U p1m p0m p1Bits p0Bits false = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro U _ _ _ _ _ _ _ hlen _ _ _ _ hro
    have hnil : U = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; simp [IsRO] at hro
  | succ f' ih =>
    intro U p1m p0m p1Bits p0Bits fn hUlt hnd hlen hbr1 hbr0 hp1 hp0 hro
    unfold canRO
    by_cases hz : (Nat.beq p1m 0 || Nat.beq p0m 0) = true
    · simp only [hz, ↓reduceIte]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      match U with
      | [] => simp [IsRO] at hro
      | [w] =>
        have hw_eq : fn = w := (Finset.singleton_injective (by simpa [IsRO] using hro)).symm
        subst hw_eq
        have h1 : fn &&& p1m = p1m := by
          apply Nat.eq_of_testBit_eq; intro a; simp only [Nat.testBit_land]
          cases hpa : p1m.testBit a with | false => simp | true => simp [hp1 a hpa]
        have h2 : fn &&& p0m = 0 := by
          apply Nat.eq_of_testBit_eq; intro b; simp only [Nat.testBit_land, Nat.zero_testBit]
          cases hpb : p0m.testBit b with | false => simp | true => simp [hp0 b hpb]
        simp [h1, h2]
      | w1 :: w2 :: ws =>
        set U0 := w1 :: w2 :: ws
        have hlen_ws : ws.length + 2 ≤ f' + 1 := hlen
        have hcard_ge : U0.toFinset.card = ws.length + 2 := by rw [List.toFinset_card_of_nodup hnd]; simp [U0]
        rw [hcard_ge] at hro; unfold IsRO at hro
        obtain ⟨o, U1, U2, f1, f2, h1le, h2le, hdisj, hun, h1ne, h2ne, _, hr1, hr2, rfl⟩ := hro
        have hlt1 : ∀ w ∈ U1, w < 65536 := fun w hw => hUlt w (List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ hw))
        have hlt2 : ∀ w ∈ U2, w < 65536 := fun w hw => hUlt w (List.mem_toFinset.mp (hun ▸ Finset.mem_union_right _ hw))
        change (if canROSide (fun L m b => canRO f' L p1m m p1Bits b false) U0 p1m p0Bits false = true then true
                else canROSide (fun L m b => canRO f' L p0m m p0Bits b false) (complList U0) p0m p1Bits false) = true
        fin_cases o
        · simp only [combM] at hp1 hp0
          have hok : canROSide (fun L m b => canRO f' L p1m m p1Bits b false) U0 p1m p0Bits false = true := by
            apply canROSide_sound hnd hdisj hun h1ne h2ne hr1 hr2 hp1
            · intro x hx; obtain ⟨b, hb16, rfl⟩ := hbr0.2 x hx
              exact ⟨b, hb16, rfl, hp0 b ((hbr0.1 b).mpr hx)⟩
            · intro h; simp at h
            · intro L S g m bs hSg hLnd hLeq hmr hfg
              have hLlt : ∀ w ∈ L, w < 65536 := fun w hw => by
                rcases hSg with ⟨rfl, _⟩ | ⟨rfl, _⟩
                · exact hlt1 w (hLeq ▸ List.mem_toFinset.mpr hw)
                · exact hlt2 w (hLeq ▸ List.mem_toFinset.mpr hw)
              rcases hSg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact ih L p1m m p1Bits bs g hLlt hLnd (by rw [← List.toFinset_card_of_nodup hLnd, hLeq]; omega) hbr1 hmr
                  (fun a ha => (Bool.and_eq_true _ _ |>.mp (Nat.testBit_land .. ▸ hp1 a ha)).1) hfg (hLeq ▸ hr1)
              · exact ih L p1m m p1Bits bs g hLlt hLnd (by rw [← List.toFinset_card_of_nodup hLnd, hLeq]; omega) hbr1 hmr
                  (fun a ha => (Bool.and_eq_true _ _ |>.mp (Nat.testBit_land .. ▸ hp1 a ha)).2) hfg (hLeq ▸ hr2)
          simp only [hok, ↓reduceIte]
        · simp only [combM] at hp1 hp0
          by_cases hokA : canROSide (fun L m b => canRO f' L p1m m p1Bits b false) U0 p1m p0Bits false = true
          · simp only [hokA, ↓reduceIte]
          · simp only [hokA, Bool.false_eq_true, ↓reduceIte]
            set cU1 := U1.image (65535 ^^^ ·)
            set cU2 := U2.image (65535 ^^^ ·)
            have hf1lt : f1 < 65536 := isRO_lt U1.card hlt1 hr1
            have hf2lt : f2 < 65536 := isRO_lt U2.card hlt2 hr2
            have hc1 : cU1.card = U1.card := Finset.card_image_of_injOn (fun a ha b hb h => xor65535_inj (hlt1 a ha) (hlt1 b hb) h)
            have hc2 : cU2.card = U2.card := Finset.card_image_of_injOn (fun a ha b hb h => xor65535_inj (hlt2 a ha) (hlt2 b hb) h)
            have hdj' : Disjoint cU1 cU2 := by
              rw [Finset.disjoint_left]; intro y hy1 hy2
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
              obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hy2
              exact Finset.disjoint_left.mp hdisj ha ((xor65535_inj (hlt2 b hb) (hlt1 a ha) hba) ▸ hb)
            have hun' : cU1 ∪ cU2 = (complList U0).toFinset := by
              ext y; rw [complList_eq, List.mem_toFinset, List.mem_map, Finset.mem_union, Finset.mem_image, Finset.mem_image]
              constructor
              · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
                · exact ⟨a, List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ ha), rfl⟩
                · exact ⟨a, List.mem_toFinset.mp (hun ▸ Finset.mem_union_right _ ha), rfl⟩
              · rintro ⟨a, ha, rfl⟩
                rcases Finset.mem_union.mp (hun.symm ▸ List.mem_toFinset.mpr ha) with h1 | h2
                · exact Or.inl ⟨a, h1, rfl⟩
                · exact Or.inr ⟨a, h2, rfl⟩
            have hor_eq : (65535 ^^^ f1) &&& (65535 ^^^ f2) = 65535 ^^^ (f1 ||| f2) := (xor65535_or hf1lt hf2lt).symm
            apply canROSide_sound (complList_nodup hUlt hnd) hdj' hun' (h1ne.image _) (h2ne.image _)
              (hc1 ▸ isRO_compl U1.card hlt1 hr1) (hc2 ▸ isRO_compl U2.card hlt2 hr2)
            · intro b hb; rw [hor_eq, xor_65535_testBit (bitsRep_lt16 hbr0 hb), hp0 b hb]; rfl
            · intro x hx; obtain ⟨a, ha16, rfl⟩ := hbr1.2 x hx
              exact ⟨a, ha16, rfl, by rw [hor_eq, xor_65535_testBit ha16, hp1 a ((hbr1.1 a).mpr hx)]; rfl⟩
            · intro h; simp at h
            · intro L S g m bs hSg hLnd hLeq hmr hfg
              have hLlt : ∀ w ∈ L, w < 65536 := fun w hw => by
                have hw' : w ∈ (complList U0).toFinset := by
                  rw [← hun']; rcases hSg with ⟨rfl, _⟩ | ⟨rfl, _⟩
                  · exact Finset.mem_union_left _ (hLeq ▸ List.mem_toFinset.mpr hw)
                  · exact Finset.mem_union_right _ (hLeq ▸ List.mem_toFinset.mpr hw)
                exact complList_lt hUlt w (List.mem_toFinset.mp hw')
              rcases hSg with ⟨hS, hg⟩ | ⟨hS, hg⟩
              · subst hS; subst hg
                exact ih L p0m m p0Bits bs (65535 ^^^ f1) hLlt hLnd
                  (by rw [← List.toFinset_card_of_nodup hLnd, hLeq, hc1]; omega) hbr0 hmr
                  (fun b hb => by
                    have := hp0 b hb; simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at this
                    rw [xor_65535_testBit (bitsRep_lt16 hbr0 hb), this.1]; rfl)
                  hfg (hLeq ▸ hc1 ▸ isRO_compl U1.card hlt1 hr1)
              · subst hS; subst hg
                exact ih L p0m m p0Bits bs (65535 ^^^ f2) hLlt hLnd
                  (by rw [← List.toFinset_card_of_nodup hLnd, hLeq, hc2]; omega) hbr0 hmr
                  (fun b hb => by
                    have := hp0 b hb; simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at this
                    rw [xor_65535_testBit (bitsRep_lt16 hbr0 hb), this.2]; rfl)
                  hfg (hLeq ▸ hc2 ▸ isRO_compl U2.card hlt2 hr2)

theorem isRORoot_imp_canRO {U : List ℕ} {p0m : ℕ} {p1Bits p0Bits : List ℕ}
    (hU_lt : ∀ w ∈ U, w < 65536) (hnd : U.Nodup)
    (hp0m_eq : ∀ b < 16, p0m.testBit b = !targetNat.testBit b)
    (hbr1 : BitsRep targetNat p1Bits) (hbr0 : BitsRep p0m p0Bits)
    (hro : IsRORoot U.toFinset) :
    canRO U.length U targetNat p0m p1Bits p0Bits true = true := by
  obtain ⟨o, U1, U2, f1, f2, hdisj, hun, h1ne, h2ne, hr1, hr2, hteq, hne1, hne2⟩ := hro
  have h1pos := Finset.card_pos.mpr h1ne
  have h2pos := Finset.card_pos.mpr h2ne
  have hcard_eq : U.length = U1.card + U2.card := by
    rw [← List.toFinset_card_of_nodup hnd, ← hun, Finset.card_union_of_disjoint hdisj]
  have hlt1 : ∀ w ∈ U1, w < 65536 := fun w hw => hU_lt w (List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ hw))
  have hlt2 : ∀ w ∈ U2, w < 65536 := fun w hw => hU_lt w (List.mem_toFinset.mp (hun ▸ Finset.mem_union_right _ hw))
  have hf1lt : f1 < 65536 := isRO_lt U1.card hlt1 hr1
  have hf2lt : f2 < 65536 := isRO_lt U2.card hlt2 hr2
  have hp0 : ∀ b, p0m.testBit b = true → targetNat.testBit b = false := fun b hb => by
    have := hp0m_eq b (bitsRep_lt16 hbr0 hb); rw [hb] at this; cases hv : targetNat.testBit b <;> simp_all
  cases hU : U with
  | nil => rw [hU] at hcard_eq; simp at hcard_eq; omega
  | cons w1 t1 =>
    cases t1 with
    | nil => rw [hU] at hcard_eq; simp at hcard_eq; omega
    | cons w2 ws =>
      rw [hU] at hnd hun hcard_eq hU_lt
      set U0 := w1 :: w2 :: ws
      set f' := ws.length + 1
      have hlen_ws : f' + 1 = U1.card + U2.card := hcard_eq
      unfold canRO
      by_cases hz : (Nat.beq targetNat 0 || Nat.beq p0m 0) = true
      · simp only [hz, ↓reduceIte]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have hsplit : U0.length = f' + 1 := rfl
        conv_lhs => rw [hsplit]
        dsimp only
        change (if canROSide (fun L m b => canRO f' L targetNat m p1Bits b false) U0 targetNat p0Bits true = true then true
                else canROSide (fun L m b => canRO f' L p0m m p0Bits b false) (complList U0) p0m p1Bits true) = true
        fin_cases o
        · simp only [combM] at hteq
          have hp1_and : ∀ a, targetNat.testBit a = true → (f1 &&& f2).testBit a = true := fun a ha => hteq ▸ ha
          have hex_side : ∀ g1 g2, g1 < 65536 → g2 < 65536 → targetNat = g1 &&& g2 → g2 ≠ targetNat →
              ∃ b, 2 ^ b ∈ p0Bits ∧ g1.testBit b = false := by
            intro g1 g2 _ hg2lt hte hne
            by_contra hno; apply hne; apply Nat.eq_of_testBit_eq; intro b
            by_cases hb16 : b < 16
            · cases ht : targetNat.testBit b with
              | true => have := hte ▸ ht; simp [Nat.testBit_land] at this; exact this.2
              | false =>
                have hbp0 : 2 ^ b ∈ p0Bits := (hbr0.1 b).mp (by rw [hp0m_eq b hb16, ht]; rfl)
                have hg1t : g1.testBit b = true := by cases hv : g1.testBit b with | true => rfl | false => exact absurd ⟨b, hbp0, hv⟩ hno
                have htb : (g1 &&& g2).testBit b = false := hte ▸ ht
                simp [Nat.testBit_land, hg1t] at htb; exact htb
            · rw [testBit_mask_ge16 g2 b hg2lt (by omega), testBit_mask_ge16 targetNat b targetNat_lt (by omega)]
          have hok : canROSide (fun L m b => canRO f' L targetNat m p1Bits b false) U0 targetNat p0Bits true = true := by
            apply canROSide_sound hnd hdisj hun h1ne h2ne hr1 hr2 hp1_and
            · intro x hx; obtain ⟨b, hb16, rfl⟩ := hbr0.2 x hx
              exact ⟨b, hb16, rfl, hteq ▸ hp0 b ((hbr0.1 b).mpr hx)⟩
            · intro _; exact ⟨hex_side f1 f2 hf1lt hf2lt hteq hne2,
                hex_side f2 f1 hf2lt hf1lt (hteq.trans (Nat.land_comm f1 f2)) hne1⟩
            · intro L S g m bs hSg hLnd hLeq hmr hfg
              have hLlt : ∀ w ∈ L, w < 65536 := fun w hw => by
                rcases hSg with ⟨rfl, _⟩ | ⟨rfl, _⟩
                · exact hlt1 w (hLeq ▸ List.mem_toFinset.mpr hw)
                · exact hlt2 w (hLeq ▸ List.mem_toFinset.mpr hw)
              rcases hSg with ⟨hS, hg⟩ | ⟨hS, hg⟩
              · subst hS; subst hg
                exact isRO_imp_canRO f' L targetNat m p1Bits bs g hLlt hLnd
                  (by rw [← List.toFinset_card_of_nodup hLnd, hLeq]; omega) hbr1 hmr
                  (fun a ha => (Bool.and_eq_true _ _ |>.mp (Nat.testBit_land .. ▸ hp1_and a ha)).1) hfg (hLeq ▸ hr1)
              · subst hS; subst hg
                exact isRO_imp_canRO f' L targetNat m p1Bits bs g hLlt hLnd
                  (by rw [← List.toFinset_card_of_nodup hLnd, hLeq]; omega) hbr1 hmr
                  (fun a ha => (Bool.and_eq_true _ _ |>.mp (Nat.testBit_land .. ▸ hp1_and a ha)).2) hfg (hLeq ▸ hr2)
          simp only [hok, ↓reduceIte]
        · simp only [combM] at hteq
          by_cases hokA : canROSide (fun L m b => canRO f' L targetNat m p1Bits b false) U0 targetNat p0Bits true = true
          · simp only [hokA, ↓reduceIte]
          · simp only [hokA, Bool.false_eq_true, ↓reduceIte]
            set cU1 := U1.image (65535 ^^^ ·)
            set cU2 := U2.image (65535 ^^^ ·)
            have hc1 : cU1.card = U1.card := Finset.card_image_of_injOn (fun a ha b hb h => xor65535_inj (hlt1 a ha) (hlt1 b hb) h)
            have hc2 : cU2.card = U2.card := Finset.card_image_of_injOn (fun a ha b hb h => xor65535_inj (hlt2 a ha) (hlt2 b hb) h)
            have hdj' : Disjoint cU1 cU2 := by
              rw [Finset.disjoint_left]; intro y hy1 hy2
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
              obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hy2
              exact Finset.disjoint_left.mp hdisj ha ((xor65535_inj (hlt2 b hb) (hlt1 a ha) hba) ▸ hb)
            have hun' : cU1 ∪ cU2 = (complList U0).toFinset := by
              ext y; rw [complList_eq, List.mem_toFinset, List.mem_map, Finset.mem_union, Finset.mem_image, Finset.mem_image]
              constructor
              · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
                · exact ⟨a, List.mem_toFinset.mp (hun ▸ Finset.mem_union_left _ ha), rfl⟩
                · exact ⟨a, List.mem_toFinset.mp (hun ▸ Finset.mem_union_right _ ha), rfl⟩
              · rintro ⟨a, ha, rfl⟩
                rcases Finset.mem_union.mp (hun.symm ▸ List.mem_toFinset.mpr ha) with h1 | h2
                · exact Or.inl ⟨a, h1, rfl⟩
                · exact Or.inr ⟨a, h2, rfl⟩
            have hor_eq : (65535 ^^^ f1) &&& (65535 ^^^ f2) = 65535 ^^^ targetNat := by rw [hteq, xor65535_or hf1lt hf2lt]
            have hex_side : ∀ g1 g2, g1 < 65536 → g2 < 65536 → targetNat = g1 ||| g2 → g2 ≠ targetNat →
                ∃ a, 2 ^ a ∈ p1Bits ∧ (65535 ^^^ g1).testBit a = false := by
              intro g1 g2 _ hg2lt hte hne
              by_contra hno; apply hne; apply Nat.eq_of_testBit_eq; intro a
              by_cases ha16 : a < 16
              · cases ht : targetNat.testBit a with
                | false => have := hte ▸ ht; simp [Nat.testBit_lor] at this; exact this.2
                | true =>
                  have hap1 : 2 ^ a ∈ p1Bits := (hbr1.1 a).mp ht
                  have hg1f : g1.testBit a = false := by
                    cases hv : g1.testBit a with
                    | false => rfl
                    | true => exact absurd ⟨a, hap1, by rw [xor_65535_testBit ha16, hv]; rfl⟩ hno
                  have hta : (g1 ||| g2).testBit a = true := hte ▸ ht
                  simp [Nat.testBit_lor, hg1f] at hta; exact hta
              · rw [testBit_mask_ge16 g2 a hg2lt (by omega), testBit_mask_ge16 targetNat a targetNat_lt (by omega)]
            apply canROSide_sound (complList_nodup hU_lt hnd) hdj' hun' (h1ne.image _) (h2ne.image _)
              (hc1 ▸ isRO_compl U1.card hlt1 hr1) (hc2 ▸ isRO_compl U2.card hlt2 hr2)
            · intro b hb; rw [hor_eq, xor_65535_testBit (bitsRep_lt16 hbr0 hb), hp0 b hb]; rfl
            · intro x hx; obtain ⟨a, ha16, rfl⟩ := hbr1.2 x hx
              exact ⟨a, ha16, rfl, by rw [hor_eq, xor_65535_testBit ha16, (hbr1.1 a).mpr hx]; rfl⟩
            · intro _; exact ⟨hex_side f1 f2 hf1lt hf2lt hteq hne2,
                hex_side f2 f1 hf2lt hf1lt (hteq.trans (Nat.lor_comm f1 f2)) hne1⟩
            · intro L S g m bs hSg hLnd hLeq hmr hfg
              have hLlt : ∀ w ∈ L, w < 65536 := fun w hw => by
                have hw' : w ∈ (complList U0).toFinset := by
                  rw [← hun']; rcases hSg with ⟨rfl, _⟩ | ⟨rfl, _⟩
                  · exact Finset.mem_union_left _ (hLeq ▸ List.mem_toFinset.mpr hw)
                  · exact Finset.mem_union_right _ (hLeq ▸ List.mem_toFinset.mpr hw)
                exact complList_lt hU_lt w (List.mem_toFinset.mp hw')
              rcases hSg with ⟨hS, hg⟩ | ⟨hS, hg⟩
              · subst hS; subst hg
                exact isRO_imp_canRO f' L p0m m p0Bits bs (65535 ^^^ f1) hLlt hLnd
                  (by rw [← List.toFinset_card_of_nodup hLnd, hLeq, hc1]; omega) hbr0 hmr
                  (fun b hb => by
                    have := hteq ▸ hp0 b hb; simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at this
                    rw [xor_65535_testBit (bitsRep_lt16 hbr0 hb), this.1]; rfl)
                  hfg (hLeq ▸ hc1 ▸ isRO_compl U1.card hlt1 hr1)
              · subst hS; subst hg
                exact isRO_imp_canRO f' L p0m m p0Bits bs (65535 ^^^ f2) hLlt hLnd
                  (by rw [← List.toFinset_card_of_nodup hLnd, hLeq, hc2]; omega) hbr0 hmr
                  (fun b hb => by
                    have := hteq ▸ hp0 b hb; simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at this
                    rw [xor_65535_testBit (bitsRep_lt16 hbr0 hb), this.2]; rfl)
                  hfg (hLeq ▸ hc2 ▸ isRO_compl U2.card hlt2 hr2)



abbrev p0MaskRO : ℕ := 51809
def p1Bits0 : List ℕ := [2, 4, 8, 16, 128, 256, 1024, 4096, 8192]
def p0Bits0 : List ℕ := [1, 32, 64, 512, 2048, 16384, 32768]
theorem p0MaskRO_lt : p0MaskRO < 2 ^ 16 := by decide
theorem hp0m_fin : ∀ b : Fin 16, p0MaskRO.testBit b.val = !targetNat.testBit b.val := by decide
theorem hp0m_eq_proof (b : ℕ) (hb : b < 16) : p0MaskRO.testBit b = !targetNat.testBit b := hp0m_fin ⟨b, hb⟩
theorem hbr1_fin : ∀ i : Fin 16, targetNat.testBit i.val = true ↔ 2 ^ i.val ∈ p1Bits0 := by decide
theorem hbr1_mem : ∀ x ∈ p1Bits0, ∃ i < 16, x = 2 ^ i := by
  intro x hx; simp only [p1Bits0, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨10, by decide, rfl⟩
  · exact ⟨12, by decide, rfl⟩
  · exact ⟨13, by decide, rfl⟩
theorem hbr1_proof : BitsRep targetNat p1Bits0 := by
  refine ⟨fun i => ?_, hbr1_mem⟩
  by_cases hi : i < 16
  · exact hbr1_fin ⟨i, hi⟩
  · constructor
    · intro ht; have := testBit_mask_ge16 targetNat i targetNat_lt (by omega); rw [this] at ht; simp at ht
    · intro hm; obtain ⟨j, hj16, heq⟩ := hbr1_mem (2 ^ i) hm
      have := Nat.pow_right_injective (by decide : 1 < 2) heq; omega
theorem hbr0_fin : ∀ i : Fin 16, p0MaskRO.testBit i.val = true ↔ 2 ^ i.val ∈ p0Bits0 := by decide
theorem hbr0_mem : ∀ x ∈ p0Bits0, ∃ i < 16, x = 2 ^ i := by
  intro x hx; simp only [p0Bits0, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨9, by decide, rfl⟩
  · exact ⟨11, by decide, rfl⟩
  · exact ⟨14, by decide, rfl⟩
  · exact ⟨15, by decide, rfl⟩
theorem hbr0_proof : BitsRep p0MaskRO p0Bits0 := by
  refine ⟨fun i => ?_, hbr0_mem⟩
  by_cases hi : i < 16
  · exact hbr0_fin ⟨i, hi⟩
  · constructor
    · intro ht; have := testBit_mask_ge16 p0MaskRO i p0MaskRO_lt (by omega); rw [this] at ht; simp at ht
    · intro hm; obtain ⟨j, hj16, heq⟩ := hbr0_mem (2 ^ i) hm
      have := Nat.pow_right_injective (by decide : 1 < 2) heq; omega

def roBadTree_c0 : BinaryTree ℕ := ofDeltaN [0x44442092111f10080f00,0xff61ed301170000,78532163046408192,97671816619556864,0xc8e000011d3021f,0x4444356c43bc0c300000,0x27221393ffffe1fcefd1,0x449a2722144455d7102f,0x44433fba80dd9a69aa28fde1,0x444410450000000000000000,0x2ffffe99ee2cefd0f10f,270598369,0xde1e03000e0000,0x1444000000000000,0xb02ffffffffff1ff1f,0x27221393ffffe1eeefdf0000,0x4055ffffd0b01e11102f0ef1,234881567,893118316001,234881567,0x106b150220201e03,0x6ffef94dd2dd1d1d0ed,917490,2,2,1,6,3,7,6,212,1,14,29,888,2908,13762863,917504,220201184,13762336,4331732992,51539607552,837233209058,14,225,3600,15,514,233963534,917504,50528256,0xcffeefceef0,225,3840,289,285409294,13631488,3577694126080,51539607552,18713186140160,204472320,13631488,282230659219456,0xa000000000000,218103808,0xaf4fffff3000000,47244640256,0x56afff5111d1103,0x95fffffbe2eefd,0xafff3000000,0x9f50000000000,3584,218100224,0xafff3000000,0x9f5f50000000000,0x671000000000000,851968,285474816,786432,0x8ffffeee30000,0x87000000000000,851968,285474816,786432,46957527040,18648747999232,42949672960,0x8eef500000000,0xa172189106b22d21e03,0x6000700009ffffff300,0xb0b00001066ffffeefd,618475290624,0x4fff8ffffffff500000,0x700000000b00000,0x1d21f8ffddfdea2e0000,37391985278976,0x6ffee68f3d00000,19340224102400,13631488,0x2f8ffddfe0c300000,0x2d07002201f3000000,0x2ffffffddfe00000000,47244640256,18691697672192,0x1ef1ffffeef500000000,0x100000000000000000,0x1000000000000000000,0xf00020000000000d00000,0xe10000000000000c300000,0x20fffffffffffff3d00000,0xe00000000000000000000,0x3249f87f9002201ff300000,0x2021ffffddfe00000000,218103808,37391480844016,0x88874fff80559a69aa28fdef0000,34672369,0x3f30d0e11d3000e0000,0xc0000000000000000,0x2ffffc00ff21ee1eefd0f10f,0x14440000000000000000,0x67781443fffff3d000000e100000,60129542130,2,2,1,3,1,2,3,7,4,110,104,1,14,69121,917504,14745600,15,901962989553,60129542144,0xd1200000000,240,60129541904,240,14679824,901928452096,284777806561280,0xc000000000000,0xc22fffffffff101,14,225,4129,285409294,0xcfee2cecddefd1,15,901978721793,60129542144,18635863097344,15,233964048,917504,55599693281,0x4010cf300000000,0xbf30000000000,0xd0000000000,0xbf3f30000000000,0x104510c2ffffff1f0,0xa0000000000000000,299044911,0xa4dddde1fcec1cfde1,14745600,15,0xdf2012f00e1,60129541904,240,14679824,901928452096,0xcff12dfdf00000,0xe0002100000,0xc2ff1f1fde0f10f,983040,60128559090,14,225,15,982800,225,3600,33685504,15,901944049649,60129542144,0xd11fff1f10f,917504,225,3600,529,60128620286,917504,225,3600,529,3311419784687,15,233964048,917504,0xcfeeeeefe0eef0,983040,60128559104,225,15732240,18939904,0xdf1fffff10f,3371550248689,893353197568,0xc3000000000,0x145200000000000f,233964048,917504,56103206912,837015109089,0xf411e03021f,51539607552,0xaefeffffffff2,0xb00a4fff2e1eefdfe,0xaf4fffff300000dfff1,15,233964048,917504,0xafffff1fffde1,0x56aff451d1d1e02f1f0,0x960bafe2e2e1fd0e10,0xa0000000000000000,0x9f5f500000000000000,0x72893000022221e03021f,47244640242,0x6f8bc6bdd2dccc1d0eceef0,2,2,1,6,14745603,65536,917504,235929840,14745360,59863138290,14745600,983054,225,234946575,15728400,225,18939919,3825,901943128095,917504,225,3600,529,60128620286,917504,225,3600,529,0xd1200d1eefe,962057994240,283884453363712,0xc000000000000,917504,225,4129,0xc2eeeeeeefeef0,14745614,235929600,983040,0xe0002020000,3371549327360,0xcffeeeeefdf0000,251658240,18764731056128,893353197568,0x340ff3000000000,917504,225,4129,0xbfffffff1eefe,917504,225,4129,0x1104ffffffffefee,3600,225,13762863,917504,219283456,917504,55885103104,837232291568,0xc3000000000,893353197568,3577994088720,51539607552,0xaeeeffffffff2,0x100a4fff2eeeeeefe,0xa0000000000000000,3840,913664,225,3600,529,0xcfffff1eefe,23236059402512,0xaf4ffffddddeeeeeef0,917504,225,3600,529,37529709641742,0xaddddeeeeeef0,0x560fff5111111110000,0x9ff50000c000000e1,0x9600afeee2eefd0e10,233959695,0xcfff2000000,0xafff30000000000,0x9f500000000000000,917504,225,3600,0x9f5fffffffffff1f10f,0x670ff500000000e00e1,55834574848,18708877541376,51539607552,0xaeee300000000,0xa4fffffff1ff1f,917504,225]
def roBadTree_c1 : BinaryTree ℕ := ofDeltaN [0xf0008f88666644f42222111f1111,55833652990,18708877541376,18764998447376,0x1060ddddeefcefd1,0xa000000000000,0x8eee5000000000000,0xaffffffff1ff1f,0x870000000000000000,917504,225,3600,529,55833652990,18708877541376,18764998447376,0xaddddeeeeeef0,0x10f6000000000000,0x8eeff000000000000,0x21890b0022d211111110,0x560ff5000d00000,0xa000000000000,0x1107000000000000,755900612608,0x8fff5000000000,13631488,755900612608,0x706ffde08fffffffffff2,0xa09f900105600000cffeefe,0x111100001110ffffe1fd0ef1,0x8fff5000000000,755914244096,0x6ffff6ffffffff1f10f,0x90000000000000,0x4ff8ffffffff50000e0ef1,0x4affffffffffffffff1f10f,0x700000000b000000000,0x1d21f8ffdd4dea2e11e11110,0xafffffee1eeef0,917504,225,3600,529,285409294,23235991175168,0x2171eadde1fcefd1,0x8ffffffff1ff1f,0x6ddfe000000000000,0x6f91060f3d000000000,0x11a0ff3000000000,893353197568,0x2f8ffddfe0c3000000000,0x2d07002201f30000000000,0x2ffffffddfe000000000000,917504,225,0xafffffff1ff1f,0x1ef1f8ffff4500d0000e0ef1,0x70000afff2ffff1f10f,0xff8ffff5000d0000e0ef1,0x70000afff2ffff1f10f,0x10000000000000000000000,0xf00020000000000d000000000,0xe10000000000000c3000000000,0x20fffffffffffff3d000000000,0x3329f87f8ffff50000011111110,0x22b1ff2feeeeeef0,0x2021ffffddfe000000000000,0xd0000000000,0x88874fff8448a777ddfde1eefdef0000,0x677844441050f221ee1efdeef1f00000,0xdfffffffffff2,2,3,9,65761,917504,0xf00e010000,15,0xd2012efffffff1,15732240,0xdffffff0ff1f0,15732240,0xd2000dfff0ff1f0,0xd1ff2000000000,0xcff11ffde0f10eff11,2,2,1,3,1,2,7929859,6815744,65536,917504,4529913856,60129542144,240,966367641360,983040,0xdff0ff0fffff2,14745600,983054,225,64659455775,225,966367641375,225,1241245548559,986625,14745600,0xd1ffffff0ff10f,60129542144,225,34672144,0xdfff1fdeef10f,60129542144,225,34672144,0xd11fff1fdeef10f,15728640,60113813504,225,34672144,901908459791,0xdff2000000000,60129542144,225,34672144,0xd1fff1fdeef10f,0x231000e000000f0,986625,14745600,901962989568,60129542144,0xd1200000000,60129542144,0x100cff1f1fde0f10f,0xc0000000000000000,60129542144,225,34672144,18704583491584,0xc22ffffeeeeeeeff101,14745614,18764982714368,0xcfee1eecddefdf0000,983040,0xdfffffff10000,0xf00e1000e1,1241245548544,0xd1ffffffffff1f,0x1031000e000000e1,0xcffff1ffffff1f,983040,60128559104,34672369,0xdf1fffff10f,3371550248689,0xceeeefde0f10f,0x4010cf3000000000000,0xbf300000000000000,60129542144,225,0xbf3fffffff1ffffff1f,0x104510c2ffffff1f00000,0xa00000000000000000000,60129542144,235929825,34668544,18704583491584,55833657344,837518622495,0xd0c30000000e1,0xa4dddde1e1dfecfdeeff1f,240,966367641360,983040,0xdff1efff10000,225,966367641375,225,1241246535184,14745600,0xdf1fffffffff10f,0xdffffff100000,60129542144,225,34672144,0xd1fff1fdeef10f,0xcff11ffdfe00000000,0xc2ffffffff0f10efff2,14745614,983040,64423526400,235929600,0xe0020200000000,0xd1ffffff1f00000,235929600,0x311000000000000,983040,0xe0002020000,0xcfeeeeefeeefdf0000,0xf00e100000,0x1111012100000000,0xd0000000000000,0xc30000000000000,0x1451f300000e000f0ef1,14745600,0xe00012f0000,0xcfff1f1fdeff10f,0xe0002020000,0xd101100000000,0xc2e1eefdef0000,0xf411e1102110000,0xb00afe2eee1eefdfe0ef1,0xaf4fffffffffffffff0f10f,983040,60128559104,225,34672144,0xdf1fffff10f,0x22220311000e0ef1,0xaddddeeeefde0f10f,0x6010af50000000000000000,0x9fff5000000000000000000,0x72892ff5b222211e102110ef1,0xa500000c2ffffff10f,0x6f8bc6bdd2dccccd1cdeefdfff2,64439255054,0xe01000f0000,0xeffff10000,0xe0012100000000,235929600,0xd1030fffff1f00000,0x11040000000000000000,0x111100000000000f0000,235929600,14745600,962091614208,0xd2000000000,0xd031100000000,0x1104000000000000,0xb00afeeeeeeeeefdf0000,235929600,0x2222111102110000,0xaf4ffffddddeeeeefdf0000,235929600,0x2222111102110000,0x560ff4feeeeffffefdf0000,0xa000afeeeeeeef0e100000,0x1070ff4ffffffffff1f00000,60129542144,235929825,34668544,0xcfff1efdeff1f,0x1104000000000000,0xaeeef000000000000,0xa50000000000000000,235929600,0x2222111102110000,0x1060ddddeeeeefdf0000,0x8eeef0000000000000000,0x8700b00000000000000000,235929600,0x2222111102110000,0x21920b0000b0000000000000,0x560ff5000d000000000,0x1110ffffff30000e00e1,893352279839,0xafff3000000000,0x8fff50000000000000,893353197568,0xafff3000000000,0x1b21ffffff6fff4feefcfdef00e1,0xaffff1ffffff1f,0x8fff50000000000000,0xb0000000000000,0x4fffffffffff50000000000000,0x21d1ffffdd4deade11e102110000,0xafffffee1eefdf0000,235929600,18764746784768,0x15220d0000000000,0x2171eadde1eeefdf0000,0x33006ffde8df300000000000000,0x1ef1f8ffff500000000e0e1000e1,0xcffff1ffffff1f,0x10000000000000000000000000,0x443a08a000000000000111102110000,0xefff9443b4bb9999ccccec0ddecdeefdfff2,2,3,4309712905,60129542144,0xf0e01000f00e1,0xe0fffffff0ff1f,983040,0xdff0ff1efff0ffff2,64439255054,0xf00e0100000000,81346268270362849,0xf00e010000,0xd1ffffff0ff1efff1f,0xf00e100000,0xdff0ff1f00000,2272273629409,0xdfff1fdeef1efff1f,0xe000000000000,2272273629409,0xd1200d1fdeef1efff1f,0xdfff20000000000000,0xcff11ffdeef1efff1efff2,64439255054,0xf0e0100000000,0xe1000000000000,0xe00121000000000000,0xd200000000000000000,0x31100000000000f0000,64659456000,966367641600,0xe0012100000000,0xd20000000000000,0xd00cff1fffdeef1f00000,0x111102110e100000,0xcf2ee1eedcdfdeef1f00000,0x11110121000000000000,0xd0111102110e100000,0xb14520c2feeeefdeef1f00000,0x1111021100000000,0xa4dddde1eeececfdef00000000,0xe1000000000000,0x222211110121000f0e100000,966367641600,0xb0000afffffffffff0ff1f00000,0x2222111102110e100000,0x7001671ff4fddddeeeefdeef1f00000,0x2222222222221111021100000000,0x1b21ffffffffffffeeeefdef00000000,0x4443ffffddddddde0000000000000000]
def roBadTree : BinaryTree ℕ := N0 0xf0008f88666644f42222111f0f00 roBadTree_c0 roBadTree_c1
abbrev vfbRO := fun (x : ℕ) => forceListN (unpack x) fun U => isStrict U && !canRO U.length U targetNat p0MaskRO p1Bits0 p0Bits0 true
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkROBadL : checkTree0 (vfbRO) roBadTree_c0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkROBadR : checkTree0 (vfbRO) roBadTree_c1 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem chkROBadV : (vfbRO) 0xf0008f88666644f42222111f0f00 = true := by decide +kernel
theorem chkROBad : checkTree0 (vfbRO) roBadTree = true := checkTree0_node chkROBadV chkROBadL chkROBadR
theorem roBad_sound {x : ℕ} (hx : InTree0 x roBadTree) : ¬ IsRORoot (unpack x).toFinset := by
  intro hro
  have hc := checkTree0_sound roBadTree chkROBad x hx
  dsimp only [vfbRO] at hc
  simp only [forceListN_eq, Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hcan := isRORoot_imp_canRO (unpack_lt x) (isStrict_nodup _ hc.1) hp0m_eq_proof hbr1_proof hbr0_proof hro
  rw [hcan] at hc; simp at hc

theorem roBad_aut_sound {U : List ℕ} {ai : ℕ}
    (hU_lt : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535)
    (ht : (if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree) = true) :
    ¬ IsRORoot U.toFinset := by
  intro hro
  by_cases h0 : Nat.beq ai 0 = true
  · simp only [h0, ↓reduceIte] at ht
    have heq : (unpack (packSet U)).toFinset = U.toFinset := by
      ext x; rw [unpack_packSetTop hU_lt, List.mem_toFinset, List.mem_toFinset, normListTop, mem_sortU, List.mem_filter]
      exact ⟨fun h => h.1, fun hx => ⟨hx, by have := hU_nz x hx; simp [nat_beq_false this.1, nat_beq_false this.2]⟩⟩
    exact roBad_sound (treeMem0_imp roBadTree ht) (heq.symm ▸ hro)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at ht
    have hok := permAut_ok ai
    have hUp_lt : ∀ y ∈ U.map (permAut ai), y < 65536 := by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hok.2.2.1 x (hU_lt x hx)
    have hUp_nz : ∀ y ∈ U.map (permAut ai), y ≠ 0 ∧ y ≠ 65535 := by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; have hnz := hU_nz x hx
      exact ⟨fun h => hnz.1 (hok.2.2.2.2 x 0 (hU_lt x hx) (by decide) (h.trans hok.1.symm)),
             fun h => hnz.2 (hok.2.2.2.2 x 65535 (hU_lt x hx) (by decide) (h.trans hok.2.1.symm))⟩
    have heq : (unpack (packSet (U.map (permAut ai)))).toFinset = U.toFinset.image (permAut ai) := by
      ext y; rw [unpack_packSetTop hUp_lt, List.mem_toFinset, normListTop, mem_sortU, List.mem_filter, Finset.mem_image]
      constructor
      · intro hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy.1; exact ⟨x, List.mem_toFinset.mpr hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hm : permAut ai x ∈ U.map (permAut ai) := List.mem_map.mpr ⟨x, List.mem_toFinset.mp hx, rfl⟩
        exact ⟨hm, by have := hUp_nz _ hm; simp [nat_beq_false this.1, nat_beq_false this.2]⟩
    exact roBad_sound (treeMem0_imp roBadTree ht) (heq.symm ▸ isRORoot_permAut ai (fun w hw => hU_lt w (List.mem_toFinset.mp hw)) hro)

def findNonEssGo (fullVal forcedV preOr : ℕ) : List (ℕ × ℕ) → List ℕ → List ℕ
  | [], _ => []
  | (w, mw) :: rest, suf :: sufs =>
    forceNat (preOr ||| mw) fun nextPre =>
    let restL := findNonEssGo fullVal forcedV nextPre rest sufs
    if !(Nat.beq w forcedV) && Nat.beq (preOr ||| suf) fullVal then w :: restL else restL
  | _, [] => []

def findNonEss (fullVal forcedV : ℕ) (UM : List (ℕ × ℕ)) : List ℕ :=
  findNonEssGo fullVal forcedV 0 UM (sufOrs UM).tail

theorem findNonEssGo_spec {f : ℕ → ℕ} {fullVal forcedV : ℕ} {P : ℕ → Prop} :
    ∀ (rest : List ℕ) (preOr : ℕ),
      rest.Nodup →
      (∀ w ∈ rest, (preOr ||| foldLor f (rest.erase w)) ≠ fullVal → P w) →
      (∀ w ∈ rest, w = forcedV → P w) →
      ∀ w ∈ rest, w ∉ findNonEssGo fullVal forcedV preOr (rest.map fun u => (u, f u)) (sufList f rest).tail → P w
  | [], _, _, _, _, _, hw, _ => by simp at hw
  | a :: t, preOr, hnd, hEss, hF, w, hw, hnot => by
    obtain ⟨ha_nt, ht_nd⟩ := List.nodup_cons.mp hnd
    have hEss_t : ∀ u ∈ t, ((preOr ||| f a) ||| foldLor f (t.erase u)) ≠ fullVal → P u := by
      intro u hu hne
      apply hEss u (List.mem_cons_of_mem _ hu)
      have hne_au : a ≠ u := fun h => ha_nt (h ▸ hu)
      have hbeq : ¬ (a == u) = true := by simp [hne_au]
      rw [List.erase_cons_tail hbeq, foldLor_cons, ← Nat.lor_assoc]
      exact hne
    rw [sufList, List.tail_cons, sufList_head_tail f t] at hnot
    simp only [List.map_cons, findNonEssGo, forceNat_eq] at hnot
    rcases List.mem_cons.mp hw with rfl | hwt
    · by_cases hc : (!(Nat.beq w forcedV) && Nat.beq (preOr ||| foldLor f t) fullVal) = true
      · simp only [hc, ↓reduceIte, List.mem_cons, true_or, not_true_eq_false] at hnot
      · by_cases hf : Nat.beq w forcedV = true
        · exact hF w (by simp) (Nat.eq_of_beq_eq_true hf)
        · apply hEss w (by simp)
          rw [List.erase_cons_head]
          intro heq
          apply hc
          simp [hf, heq]
    · apply findNonEssGo_spec t (preOr ||| f a) ht_nd hEss_t (fun u hu => hF u (List.mem_cons_of_mem _ hu)) w hwt
      intro hm
      apply hnot
      split_ifs
      · exact List.mem_cons_of_mem _ hm
      · exact hm

theorem findNonEss_mem_T {r : ℕ} {bits U : List ℕ} {seq : List (Fin 2 × ℕ × ℕ)} {m forcedV : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hmr : m + r = seq.length) (hr : 1 ≤ r)
    (hU_nd : U.Nodup) (hTsub : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ U.toFinset)
    (hforced : forcedV = 0 ∨ forcedV ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m))
    (hU_nz : ∀ w ∈ U, w ≠ 0) :
    ∀ w ∈ U, w ∉ findNonEss (fullM targetNat bits) forcedV (U.map fun u => (u, sepM targetNat bits u)) →
      w ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
  have hEss : ∀ w ∈ U, (0 ||| foldLor (sepM targetNat bits) (U.erase w)) ≠ fullM targetNat bits →
      w ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
    intro w _ hne
    rw [Nat.zero_or] at hne
    by_contra hnotT
    have hsubT : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ (U.erase w).toFinset := by
      intro z hz
      exact List.mem_toFinset.mpr ((mem_erase_of_nodup hU_nd).mpr ⟨List.mem_toFinset.mp (hTsub hz), fun he => hnotT (he ▸ hz)⟩)
    have hcU : CanM targetNat r (U.erase w).toFinset := monoCMD hsubT (usedWires_canM hmin hmr hr)
    exact hne (coveredM_sepM hM hcU bits hbits)
  have hF : ∀ w ∈ U, w = forcedV → w ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
    intro w hw heq
    rcases hforced with hf0 | hfm
    · exact absurd (heq.trans hf0) (hU_nz w hw)
    · exact heq ▸ hfm
  intro w hw hnot
  rw [findNonEss, sufOrs_eq] at hnot
  exact findNonEssGo_spec (f := sepM targetNat bits) (fullVal := fullM targetNat bits) (forcedV := forcedV) U 0 hU_nd hEss hF w hw hnot

def nextHint (h : ℕ) : ℕ × ℕ := (if Nat.beq (h &&& 1) 0 then (if Nat.beq (h &&& 2) 0 then (if Nat.beq (h &&& 4) 0 then (if Nat.beq (h &&& 8) 0 then (if Nat.beq (h &&& 16) 0 then (if Nat.beq (h &&& 32) 0 then (if Nat.beq (h &&& 64) 0 then (if Nat.beq (h &&& 128) 0 then (8, h >>> 8) else (9, h >>> 8)) else (if Nat.beq (h &&& 128) 0 then (36, h >>> 8) else (6, h >>> 8))) else (28, h >>> 6)) else (if Nat.beq (h &&& 32) 0 then (2, h >>> 6) else (if Nat.beq (h &&& 64) 0 then (if Nat.beq (h &&& 128) 0 then (10, h >>> 8) else (7, h >>> 8)) else (1, h >>> 7)))) else (27, h >>> 4)) else (if Nat.beq (h &&& 8) 0 then (if Nat.beq (h &&& 16) 0 then (if Nat.beq (h &&& 32) 0 then (23, h >>> 6) else (37, h >>> 6)) else (if Nat.beq (h &&& 32) 0 then (17, h >>> 6) else (if Nat.beq (h &&& 64) 0 then (38, h >>> 7) else (4, h >>> 7)))) else (12, h >>> 4))) else (if Nat.beq (h &&& 4) 0 then (if Nat.beq (h &&& 8) 0 then (if Nat.beq (h &&& 16) 0 then (25, h >>> 5) else (16, h >>> 5)) else (22, h >>> 4)) else (if Nat.beq (h &&& 8) 0 then (if Nat.beq (h &&& 16) 0 then (0, h >>> 5) else (20, h >>> 5)) else (if Nat.beq (h &&& 16) 0 then (19, h >>> 5) else (29, h >>> 5))))) else (if Nat.beq (h &&& 2) 0 then (if Nat.beq (h &&& 4) 0 then (if Nat.beq (h &&& 8) 0 then (15, h >>> 4) else (if Nat.beq (h &&& 16) 0 then (18, h >>> 5) else (33, h >>> 5))) else (14, h >>> 3)) else (if Nat.beq (h &&& 4) 0 then (13, h >>> 3) else (if Nat.beq (h &&& 8) 0 then (21, h >>> 4) else (if Nat.beq (h &&& 16) 0 then (if Nat.beq (h &&& 32) 0 then (39, h >>> 6) else (35, h >>> 6)) else (if Nat.beq (h &&& 32) 0 then (if Nat.beq (h &&& 64) 0 then (if Nat.beq (h &&& 128) 0 then (3, h >>> 8) else (30, h >>> 8)) else (if Nat.beq (h &&& 128) 0 then (if Nat.beq (h &&& 256) 0 then (11, h >>> 9) else (if Nat.beq (h &&& 512) 0 then (26, h >>> 10) else (32, h >>> 10))) else (31, h >>> 8))) else (if Nat.beq (h &&& 64) 0 then (34, h >>> 7) else (if Nat.beq (h &&& 128) 0 then (5, h >>> 8) else (24, h >>> 8)))))))))
def readAut (h : ℕ) : ℕ × ℕ := (h &&& 15, h >>> 4)

def stepUHintV8 (fullVal r : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (S : List ℕ) (v : ℕ) (UM : List (ℕ × ℕ)) (h : ℕ) : Option ℕ :=
  forceNat h fun h =>
  let ch := nextHint h
  forceNat ch.1 fun code =>
  forceNat ch.2 fun h2 =>
  if Nat.ble 12 code then
    forceNat (code - 12) fun d =>
    if Nat.ble 15 d then
      forceNat (code - 27) fun ai =>
      if Nat.ble 12 ai then
        if Nat.beq code 39 then
          let a1 := readAut h2
          forceNat a1.1 fun ai1 =>
          forceNat a1.2 fun ha1 =>
          let a2 := readAut ha1
          forceNat a2.1 fun ai2 =>
          forceNat a2.2 fun ha2 =>
          if Nat.beq UM.length (r + 1) then
            match findNonEss fullVal v UM with
            | [wDrop] =>
              let U := UM.map Prod.fst
              let okBad := if Nat.beq ai1 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai1))) roBadTree
              if okBad then
                let U2 := U.erase wDrop
                let ok2 := if Nat.beq ai2 0 then treeMem (packSet U2) nextTree else treeMem (packSet (U2.map (permAut ai2))) nextTree
                if ok2 then some ha2 else none
              else none
            | _ => none
          else none
        else none
      else
        if Nat.beq UM.length (r + 1) then
          let U := UM.map Prod.fst
          match findNonEss fullVal v UM with
          | [] =>
            let ok := if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree
            if ok then some h2 else none
          | [wDrop] =>
            let okBad := if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree
            if okBad then
              let U2 := U.erase wDrop
              let ok2 := if Nat.beq ai 0 then treeMem (packSet U2) nextTree else treeMem (packSet (U2.map (permAut ai))) nextTree
              if ok2 then some h2 else none
            else none
          | _ => none
        else none
    else
      if domKillsStep d 10 S v UM fullVal then some h2 else none
  else
    let U := UM.map Prod.fst
    let ok := if Nat.beq code 0 then treeMem (packSet U) nextTree else treeMem (packSet (U.map (permAut code))) nextTree
    if ok then some h2 else none

def stepInitHintV8 (fullVal s : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (UM : List (ℕ × ℕ)) (h : ℕ) : Option ℕ :=
  forceNat h fun h =>
  let ch := nextHint h
  forceNat ch.1 fun code =>
  forceNat ch.2 fun h2 =>
  if Nat.ble 12 code then
    forceNat (code - 12) fun d =>
    if Nat.ble 15 d then
      forceNat (code - 27) fun ai =>
      if Nat.ble 12 ai then
        if Nat.beq code 39 then
          let a1 := readAut h2
          forceNat a1.1 fun ai1 =>
          forceNat a1.2 fun ha1 =>
          let a2 := readAut ha1
          forceNat a2.1 fun ai2 =>
          forceNat a2.2 fun ha2 =>
          if Nat.beq UM.length (s + 1) then
            match findNonEss fullVal 0 UM with
            | [wDrop] =>
              let U := UM.map Prod.fst
              let okBad := if Nat.beq ai1 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai1))) roBadTree
              if okBad then
                let U2 := U.erase wDrop
                let ok2 := if Nat.beq ai2 0 then treeMem (packSet U2) nextTree else treeMem (packSet (U2.map (permAut ai2))) nextTree
                if ok2 then some ha2 else none
              else none
            | _ => none
          else none
        else none
      else
        if Nat.beq UM.length (s + 1) then
          let U := UM.map Prod.fst
          match findNonEss fullVal 0 UM with
          | [] =>
            let ok := if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree
            if ok then some h2 else none
          | [wDrop] =>
            let okBad := if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree
            if okBad then
              let U2 := U.erase wDrop
              let ok2 := if Nat.beq ai 0 then treeMem (packSet U2) nextTree else treeMem (packSet (U2.map (permAut ai))) nextTree
              if ok2 then some h2 else none
            else none
          | _ => none
        else none
    else
      if domKillsInit d s UM fullVal then some h2 else none
  else
    let U := UM.map Prod.fst
    let ok := if Nat.beq code 0 then treeMem (packSet U) nextTree else treeMem (packSet (U.map (permAut code))) nextTree
    if ok then some h2 else none

theorem reachMin_packSet {K r : ℕ} {U : List ℕ} (hU : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535)
    (hr : ReachMin K r U.toFinset) : ReachMin K r (unpack (packSet U)).toFinset := by
  have heq : (unpack (packSet U)).toFinset = U.toFinset := by
    ext x
    rw [unpack_packSetTop hU, List.mem_toFinset, List.mem_toFinset, normListTop, mem_sortU, List.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hx; exact ⟨hx, by have hnz := hU_nz x hx; simp [nat_beq_false hnz.1, nat_beq_false hnz.2]⟩
  rw [heq]; exact hr

theorem stepAut_sound {r : ℕ} {U : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {code : ℕ}
    (hU_lt : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535)
    (hrm : ReachMin 10 r U.toFinset)
    (ht : (if Nat.beq code 0 then treeMem (packSet U) nextTree else treeMem (packSet (U.map (permAut code))) nextTree) = true) :
    ∃ x, InTree x nextTree ∧ ReachMin 10 r (unpack x).toFinset := by
  by_cases h0 : Nat.beq code 0 = true
  · simp only [h0, ↓reduceIte] at ht
    exact ⟨packSet U, treeMem_imp nextTree ht, reachMin_packSet hU_lt hU_nz hrm⟩
  · simp only [h0, ↓reduceIte] at ht
    have hok := permAut_ok code
    have hUp_lt : ∀ y ∈ U.map (permAut code), y < 65536 := by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hok.2.2.1 x (hU_lt x hx)
    have hUp_nz : ∀ y ∈ U.map (permAut code), y ≠ 0 ∧ y ≠ 65535 := by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      have hnz := hU_nz x hx
      refine ⟨fun h => hnz.1 (hok.2.2.2.2 x 0 (hU_lt x hx) (by decide) (h.trans hok.1.symm)),
              fun h => hnz.2 (hok.2.2.2.2 x 65535 (hU_lt x hx) (by decide) (h.trans hok.2.1.symm))⟩
    have hrmp : ReachMin 10 r (U.map (permAut code)).toFinset := by
      have heq : (U.map (permAut code)).toFinset = U.toFinset.image (permAut code) := by ext y; simp
      rw [heq]; exact reachMin_permAut code hrm
    exact ⟨packSet (U.map (permAut code)), treeMem_imp nextTree ht, reachMin_packSet hUp_lt hUp_nz hrmp⟩

theorem roKill_contra {r : ℕ} {bits U : List ℕ} {seq : List (Fin 2 × ℕ × ℕ)} {m forcedV ai : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hU_lt : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535) (hU_nd : U.Nodup)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hmr : m + r = seq.length) (hr1 : 1 ≤ r)
    (hTsub : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ U.toFinset)
    (hforced : forcedV = 0 ∨ forcedV ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m))
    (hlen : U.length = r + 1)
    (hnil : findNonEss (fullM targetNat bits) forcedV (U.map fun w => (w, sepM targetNat bits w)) = [])
    (hbad : (if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree) = true) : False := by
  have hmemT := findNonEss_mem_T hM hbits hmin hmr hr1 hU_nd hTsub hforced (fun w hw => (hU_nz w hw).1)
  have hUsubT : U.toFinset ⊆ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
    intro w hw; exact hmemT w (List.mem_toFinset.mp hw) (by rw [hnil]; simp)
  have hTeq : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) = U.toFinset := Finset.Subset.antisymm hTsub hUsubT
  have hTcard : (endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)).card = r + 1 := by
    rw [hTeq, List.toFinset_card_of_nodup hU_nd, hlen]
  have hro := minimal_readOnce hmin hmr hr1 hTcard
  rw [hTeq] at hro
  exact roBad_aut_sound hU_lt hU_nz hbad hro

theorem roShrink1_sound {r : ℕ} {bits U : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {seq : List (Fin 2 × ℕ × ℕ)} {m forcedV wDrop ai1 ai2 : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hU_lt : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535) (hU_nd : U.Nodup)
    (hseq_le : seq.length ≤ 10) (hmin : MinimalFor targetNat inputs.toFinset seq) (hmr : m + r = seq.length) (hr1 : 1 ≤ r)
    (hUsub : U.toFinset ⊆ endSet inputs.toFinset (seq.take m))
    (hTsub : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ U.toFinset)
    (hforced : forcedV = 0 ∨ forcedV ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m))
    (hlen : U.length = r + 1)
    (hsingle : findNonEss (fullM targetNat bits) forcedV (U.map fun w => (w, sepM targetNat bits w)) = [wDrop])
    (hbad : (if Nat.beq ai1 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai1))) roBadTree) = true)
    (hnext : (if Nat.beq ai2 0 then treeMem (packSet (U.erase wDrop)) nextTree else treeMem (packSet ((U.erase wDrop).map (permAut ai2))) nextTree) = true) :
    ∃ x, InTree x nextTree ∧ ReachMin 10 r (unpack x).toFinset := by
  have hmemT := findNonEss_mem_T hM hbits hmin hmr hr1 hU_nd hTsub hforced (fun w hw => (hU_nz w hw).1)
  have hnotT : wDrop ∉ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
    intro hwdT
    have hUsubT : U.toFinset ⊆ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) := by
      intro w hw
      by_cases ew : w = wDrop
      · exact ew ▸ hwdT
      · exact hmemT w (List.mem_toFinset.mp hw) (by rw [hsingle]; simp [ew])
    have hTeq : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) = U.toFinset := Finset.Subset.antisymm hTsub hUsubT
    have hTcard : (endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)).card = r + 1 := by
      rw [hTeq, List.toFinset_card_of_nodup hU_nd, hlen]
    have hro := minimal_readOnce hmin hmr hr1 hTcard
    rw [hTeq] at hro
    exact roBad_aut_sound hU_lt hU_nz hbad hro
  have hU2_lt : ∀ x ∈ U.erase wDrop, x < 65536 := fun x hx => hU_lt x (List.mem_of_mem_erase hx)
  have hU2_nz : ∀ x ∈ U.erase wDrop, x ≠ 0 ∧ x ≠ 65535 := fun x hx => hU_nz x (List.mem_of_mem_erase hx)
  have hU2_sub : (U.erase wDrop).toFinset ⊆ endSet inputs.toFinset (seq.take m) := fun x hx =>
    hUsub (List.mem_toFinset.mpr (List.mem_of_mem_erase (List.mem_toFinset.mp hx)))
  have hT_U2 : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ (U.erase wDrop).toFinset := fun x hx =>
    List.mem_toFinset.mpr ((mem_erase_of_nodup hU_nd).mpr ⟨List.mem_toFinset.mp (hTsub hx), fun he => hnotT (he ▸ hx)⟩)
  exact stepAut_sound hU2_lt hU2_nz ⟨seq, m, hseq_le, hmin, hmr, hU2_sub, hT_U2⟩ hnext

theorem stepInitHintV8_sound {s : ℕ} {bits U : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {a b : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hU_lt : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535) (hU_nd : U.Nodup)
    (hs : stepInitHintV8 (fullM targetNat bits) s nextTree (U.map fun w => (w, sepM targetNat bits w)) a = some b)
    (seq : List (Fin 2 × ℕ × ℕ)) (hseq_len : seq.length = s) (hseq_le : s ≤ 10)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hs1 : 1 ≤ s)
    (hUsub : U.toFinset ⊆ inputs.toFinset) (hTsub : inputs.toFinset ∩ usedBy seq ⊆ U.toFinset) :
    ∃ x, InTree x nextTree ∧ ReachMin 10 s (unpack x).toFinset := by
  have hrm : ReachMin 10 s U.toFinset :=
    ⟨seq, 0, by omega, hmin, by simpa using hseq_len.symm, by simpa [endSet] using hUsub, by simpa [endSet] using hTsub⟩
  unfold stepInitHintV8 at hs; simp only [forceNat_eq] at hs
  set code := (nextHint a).1
  have hmapfst : (U.map fun w => (w, sepM targetNat bits w)).map Prod.fst = U := by simp [Function.comp_def]
  have hmaplen : (U.map fun w => (w, sepM targetNat bits w)).length = U.length := List.length_map _
  by_cases hc : Nat.ble 12 code = true
  · simp only [hc, ↓reduceIte] at hs
    set d := code - 12
    by_cases hd : Nat.ble 15 d = true
    · simp only [hd, ↓reduceIte] at hs
      set ai := code - 27
      by_cases hai : Nat.ble 12 ai = true
      · simp only [hai, ↓reduceIte] at hs
        by_cases hrd : Nat.beq code 39 = true
        · simp only [hrd, ↓reduceIte, hmaplen, hmapfst] at hs
          by_cases hlen : Nat.beq U.length (s + 1) = true
          · simp only [hlen, ↓reduceIte] at hs
            cases hne : findNonEss (fullM targetNat bits) 0 (U.map fun w => (w, sepM targetNat bits w)) with
            | nil => rw [hne] at hs; simp at hs
            | cons wDrop tail =>
              cases tail with
              | cons _ _ => rw [hne] at hs; simp at hs
              | nil =>
                rw [hne] at hs; dsimp only at hs
                cases hbad : (if Nat.beq (readAut (nextHint a).2).1 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut (readAut (nextHint a).2).1))) roBadTree) with
                | false => rw [hbad] at hs; simp at hs
                | true =>
                  rw [hbad] at hs; simp only [↓reduceIte] at hs
                  cases hok2 : (if Nat.beq (readAut (readAut (nextHint a).2).2).1 0 then treeMem (packSet (U.erase wDrop)) nextTree else treeMem (packSet ((U.erase wDrop).map (permAut (readAut (readAut (nextHint a).2).2).1))) nextTree) with
                  | false => rw [hok2] at hs; simp at hs
                  | true =>
                    exact roShrink1_sound hM hbits hU_lt hU_nz hU_nd (by omega) hmin (m := 0) (r := s) (by simpa using hseq_len.symm) hs1 (by simpa [endSet] using hUsub) (by simpa [endSet] using hTsub) (Or.inl rfl) (Nat.eq_of_beq_eq_true hlen) hne hbad hok2
          · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hs; simp at hs
        · simp only [hrd, Bool.false_eq_true, ↓reduceIte] at hs; simp at hs
      · simp only [hai, Bool.false_eq_true, ↓reduceIte, hmaplen, hmapfst] at hs
        by_cases hlen : Nat.beq U.length (s + 1) = true
        · simp only [hlen, ↓reduceIte] at hs
          cases hne : findNonEss (fullM targetNat bits) 0 (U.map fun w => (w, sepM targetNat bits w)) with
          | nil =>
            rw [hne] at hs; dsimp only at hs
            cases hok : (if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree) with
            | false => rw [hok] at hs; simp at hs
            | true =>
              exact False.elim (roKill_contra hM hbits hU_lt hU_nz hU_nd hmin (m := 0) (r := s) (by simpa using hseq_len.symm) hs1
                (by simpa [endSet] using hTsub) (Or.inl rfl) (Nat.eq_of_beq_eq_true hlen) hne hok)
          | cons wDrop tail =>
            cases tail with
            | cons _ _ => rw [hne] at hs; simp at hs
            | nil =>
              rw [hne] at hs; dsimp only at hs
              cases hbad : (if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree) with
              | false => rw [hbad] at hs; simp at hs
              | true =>
                rw [hbad] at hs; simp only [↓reduceIte] at hs
                cases hok2 : (if Nat.beq ai 0 then treeMem (packSet (U.erase wDrop)) nextTree else treeMem (packSet ((U.erase wDrop).map (permAut ai))) nextTree) with
                | false => rw [hok2] at hs; simp at hs
                | true =>
                  exact roShrink1_sound hM hbits hU_lt hU_nz hU_nd (by omega) hmin (m := 0) (r := s)
                    (by simpa using hseq_len.symm) hs1 (by simpa [endSet] using hUsub) (by simpa [endSet] using hTsub)
                    (Or.inl rfl) (Nat.eq_of_beq_eq_true hlen) hne hbad hok2
        · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hs; simp at hs
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at hs
      have hd_lt : d < 15 := by
        have hnot : ¬ (15 ≤ d) := fun h => hd (Nat.ble_eq.mpr h)
        omega
      cases hdk : domKillsInit d s (U.map fun w => (w, sepM targetNat bits w)) (fullM targetNat bits) with
      | false => simp [hdk] at hs
      | true =>
        exfalso; unfold domKillsInit at hdk; simp only [forceNat_eq] at hdk
        obtain ⟨Cw, hCw_sub, hCw_const, hCw_card⟩ :=
          essConstM_spec hM hbits hmin (m := 0) (r := s) (dom := domMask d) (by simpa using hseq_len.symm) hs1 hU_nd
            (by simpa [endSet] using hTsub) (Or.inl rfl) (fun w hw => (hU_nz w hw).1)
        have hgt : seq.length < domKd d + 1 + lossOnDom (domMask d) (domInps d) [] + Cw.card := by
          have hls0 : lossOnDom (domMask d) (domInps d) [] = 0 := rfl
          rw [hls0, hCw_card, hseq_len]
          cases h1 : Nat.ble (domKd d + 1) s with
          | false =>
            have hnot : ¬ (domKd d + 1 ≤ s) := fun h => by rw [Nat.ble_eq.mpr h] at h1; simp at h1
            omega
          | true =>
            simp only [h1, ↓reduceIte, Bool.not_eq_true'] at hdk
            have hnot : ¬ (domKd d + 1 + essConstM (domMask d) (fullM targetNat bits) 0 (U.map fun w => (w, sepM targetNat bits w)) ≤ s) :=
              fun h => by rw [Nat.ble_eq.mpr h] at hdk; simp at hdk
            omega
        exact budget_contradiction hd_lt hmin (by omega) List.nodup_nil (by simp) hCw_sub hCw_const hgt
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, hmapfst] at hs
    cases ht : (if Nat.beq code 0 then treeMem (packSet U) nextTree else treeMem (packSet (U.map (permAut code))) nextTree) with
    | false => rw [ht] at hs; simp at hs
    | true => exact stepAut_sound hU_lt hU_nz hrm ht

theorem stepUHintV8_sound {r : ℕ} {bits S U : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {v a b : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hS_nd : S.Nodup) (hv_notS : v ∉ S)
    (hU_lt : ∀ x ∈ U, x < 65536) (hU_nz : ∀ x ∈ U, x ≠ 0 ∧ x ≠ 65535) (hU_nd : U.Nodup)
    (hs : stepUHintV8 (fullM targetNat bits) r nextTree S v (U.map fun w => (w, sepM targetNat bits w)) a = some b)
    (seq : List (Fin 2 × ℕ × ℕ)) (m : ℕ) (hseq_le : seq.length ≤ 10)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hmr : m + r = seq.length) (hr1 : 1 ≤ r)
    (hSv_sub : (v :: S).toFinset ⊆ endSet inputs.toFinset (seq.take m))
    (hUsub : U.toFinset ⊆ endSet inputs.toFinset (seq.take m))
    (hTsub : endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m) ⊆ U.toFinset)
    (hvT : v ∈ endSet inputs.toFinset (seq.take m) ∩ usedBy (seq.drop m)) :
    ∃ x, InTree x nextTree ∧ ReachMin 10 r (unpack x).toFinset := by
  have hrm : ReachMin 10 r U.toFinset := ⟨seq, m, hseq_le, hmin, hmr, hUsub, hTsub⟩
  unfold stepUHintV8 at hs; simp only [forceNat_eq] at hs
  set code := (nextHint a).1
  have hmapfst : (U.map fun w => (w, sepM targetNat bits w)).map Prod.fst = U := by simp [Function.comp_def]
  have hmaplen : (U.map fun w => (w, sepM targetNat bits w)).length = U.length := List.length_map _
  by_cases hc : Nat.ble 12 code = true
  · simp only [hc, ↓reduceIte] at hs
    set d := code - 12
    by_cases hd : Nat.ble 15 d = true
    · simp only [hd, ↓reduceIte] at hs
      set ai := code - 27
      by_cases hai : Nat.ble 12 ai = true
      · simp only [hai, ↓reduceIte] at hs
        by_cases hrd : Nat.beq code 39 = true
        · simp only [hrd, ↓reduceIte, hmaplen, hmapfst] at hs
          by_cases hlen : Nat.beq U.length (r + 1) = true
          · simp only [hlen, ↓reduceIte] at hs
            cases hne : findNonEss (fullM targetNat bits) v (U.map fun w => (w, sepM targetNat bits w)) with
            | nil => rw [hne] at hs; simp at hs
            | cons wDrop tail =>
              cases tail with
              | cons _ _ => rw [hne] at hs; simp at hs
              | nil =>
                rw [hne] at hs; dsimp only at hs
                cases hbad : (if Nat.beq (readAut (nextHint a).2).1 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut (readAut (nextHint a).2).1))) roBadTree) with
                | false => rw [hbad] at hs; simp at hs
                | true =>
                  rw [hbad] at hs; simp only [↓reduceIte] at hs
                  cases hok2 : (if Nat.beq (readAut (readAut (nextHint a).2).2).1 0 then treeMem (packSet (U.erase wDrop)) nextTree else treeMem (packSet ((U.erase wDrop).map (permAut (readAut (readAut (nextHint a).2).2).1))) nextTree) with
                  | false => rw [hok2] at hs; simp at hs
                  | true =>
                    exact roShrink1_sound hM hbits hU_lt hU_nz hU_nd hseq_le hmin hmr hr1 hUsub hTsub (Or.inr hvT) (Nat.eq_of_beq_eq_true hlen) hne hbad hok2
          · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hs; simp at hs
        · simp only [hrd, Bool.false_eq_true, ↓reduceIte] at hs; simp at hs
      · simp only [hai, Bool.false_eq_true, ↓reduceIte, hmaplen, hmapfst] at hs
        by_cases hlen : Nat.beq U.length (r + 1) = true
        · simp only [hlen, ↓reduceIte] at hs
          cases hne : findNonEss (fullM targetNat bits) v (U.map fun w => (w, sepM targetNat bits w)) with
          | nil =>
            rw [hne] at hs; dsimp only at hs
            cases hok : (if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree) with
            | false => rw [hok] at hs; simp at hs
            | true =>
              exact False.elim (roKill_contra hM hbits hU_lt hU_nz hU_nd hmin hmr hr1 hTsub (Or.inr hvT) (Nat.eq_of_beq_eq_true hlen) hne hok)
          | cons wDrop tail =>
            cases tail with
            | cons _ _ => rw [hne] at hs; simp at hs
            | nil =>
              rw [hne] at hs; dsimp only at hs
              cases hbad : (if Nat.beq ai 0 then treeMem0 (packSet U) roBadTree else treeMem0 (packSet (U.map (permAut ai))) roBadTree) with
              | false => rw [hbad] at hs; simp at hs
              | true =>
                rw [hbad] at hs; simp only [↓reduceIte] at hs
                cases hok2 : (if Nat.beq ai 0 then treeMem (packSet (U.erase wDrop)) nextTree else treeMem (packSet ((U.erase wDrop).map (permAut ai))) nextTree) with
                | false => rw [hok2] at hs; simp at hs
                | true =>
                  exact roShrink1_sound hM hbits hU_lt hU_nz hU_nd hseq_le hmin hmr hr1 hUsub hTsub (Or.inr hvT) (Nat.eq_of_beq_eq_true hlen) hne hbad hok2
        · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hs; simp at hs
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at hs
      have hd_lt : d < 15 := by
        have hnot : ¬ (15 ≤ d) := fun h => hd (Nat.ble_eq.mpr h)
        omega
      cases hdk : domKillsStep d 10 S v (U.map fun w => (w, sepM targetNat bits w)) (fullM targetNat bits) with
      | false => simp [hdk] at hs
      | true =>
        exfalso; unfold domKillsStep at hdk; simp only [forceNat_eq] at hdk
        obtain ⟨Cw, hCw_sub, hCw_const, hCw_card⟩ :=
          essConstM_spec hM hbits hmin (dom := domMask d) hmr hr1 hU_nd hTsub (Or.inr hvT) (fun w hw => (hU_nz w hw).1)
        have hgt : seq.length < domKd d + 1 + lossOnDom (domMask d) (domInps d) (v :: S) + Cw.card := by
          rw [hCw_card]
          cases h1 : Nat.ble (domKd d + 1 + lossOnDom (domMask d) (domInps d) (v :: S)) 10 with
          | false =>
            have hnot : ¬ (domKd d + 1 + lossOnDom (domMask d) (domInps d) (v :: S) ≤ 10) := fun h => by rw [Nat.ble_eq.mpr h] at h1; simp at h1
            omega
          | true =>
            simp only [h1, ↓reduceIte, Bool.not_eq_true'] at hdk
            have hnot : ¬ (domKd d + 1 + lossOnDom (domMask d) (domInps d) (v :: S) + essConstM (domMask d) (fullM targetNat bits) v (U.map fun w => (w, sepM targetNat bits w)) ≤ 10) :=
              fun h => by rw [Nat.ble_eq.mpr h] at hdk; simp at hdk
            omega
        exact budget_contradiction hd_lt hmin (by omega) (List.nodup_cons.mpr ⟨hv_notS, hS_nd⟩) hSv_sub hCw_sub hCw_const hgt
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, hmapfst] at hs
    cases ht : (if Nat.beq code 0 then treeMem (packSet U) nextTree else treeMem (packSet (U.map (permAut code))) nextTree) with
    | false => rw [ht] at hs; simp at hs
    | true => exact stepAut_sound hU_lt hU_nz hrm ht

def checkCutsInitV8 (fullVal s : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) : List (List (ℕ × ℕ) × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (UM, mU) :: rest, h =>
    if Nat.beq mU fullVal then
      match stepInitHintV8 fullVal s nextTree UM h with
      | none => none
      | some h' => checkCutsInitV8 fullVal s nextTree rest h'
    else checkCutsInitV8 fullVal s nextTree rest h

theorem checkCutsInitV8_sound {fullVal s : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} :
    ∀ (cs : List (List (ℕ × ℕ) × ℕ)) (h h' : ℕ), checkCutsInitV8 fullVal s nextTree cs h = some h' →
      ∀ p ∈ cs, p.2 = fullVal → ∃ a b, stepInitHintV8 fullVal s nextTree p.1 a = some b
  | [], _, _, _, _, hp, _ => by simp at hp
  | (UM, mU) :: rest, h, h', hall, p, hp, hpeq => by
    unfold checkCutsInitV8 at hall
    by_cases hm : Nat.beq mU fullVal = true
    · simp only [hm, ↓reduceIte] at hall
      cases hs : stepInitHintV8 fullVal s nextTree UM h with
      | none => simp [hs] at hall
      | some h1 =>
        simp only [hs] at hall
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨h, h1, hs⟩
        · exact checkCutsInitV8_sound rest h1 h' hall p hp hpeq
    · simp only [hm, ↓reduceIte] at hall
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd (hpeq ▸ Nat.beq_refl fullVal) hm
      · exact checkCutsInitV8_sound rest h h' hall p hp hpeq

def scanVsV8 (fullVal r : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (S : List ℕ) (U'M : List (ℕ × ℕ)) (mU : ℕ) :
    List (ℕ × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (v, mv) :: rest, h =>
    if Nat.beq (mU ||| mv) fullVal then
      match stepUHintV8 fullVal r nextTree S v ((v, mv) :: U'M) h with
      | none => none
      | some h' => scanVsV8 fullVal r nextTree S U'M mU rest h'
    else scanVsV8 fullVal r nextTree S U'M mU rest h

theorem scanVsV8_sound {fullVal r : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {S : List ℕ} {U'M : List (ℕ × ℕ)} {mU : ℕ} :
    ∀ (vs : List (ℕ × ℕ)) (h h' : ℕ), scanVsV8 fullVal r nextTree S U'M mU vs h = some h' →
      ∀ q ∈ vs, (mU ||| q.2) = fullVal → ∃ a b, stepUHintV8 fullVal r nextTree S q.1 (q :: U'M) a = some b
  | [], _, _, _, _, hq, _ => by simp at hq
  | (v, mv) :: rest, h, h', hall, q, hq, hqeq => by
    unfold scanVsV8 at hall
    by_cases hm : Nat.beq (mU ||| mv) fullVal = true
    · simp only [hm, ↓reduceIte] at hall
      cases hs : stepUHintV8 fullVal r nextTree S v ((v, mv) :: U'M) h with
      | none => simp [hs] at hall
      | some h1 =>
        simp only [hs] at hall
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨h, h1, hs⟩
        · exact scanVsV8_sound rest h1 h' hall q hq hqeq
    · simp only [hm, ↓reduceIte] at hall
      rcases List.mem_cons.mp hq with rfl | hq
      · exact absurd (hqeq ▸ Nat.beq_refl fullVal) hm
      · exact scanVsV8_sound rest h h' hall q hq hqeq

def scanCutsV8 (fullVal r : ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (S : List ℕ) (vsM : List (ℕ × ℕ)) :
    List (List (ℕ × ℕ) × ℕ) → ℕ → Option ℕ
  | [], h => some h
  | (U'M, mU) :: rest, h =>
    match scanVsV8 fullVal r nextTree S U'M mU vsM h with
    | none => none
    | some h' => scanCutsV8 fullVal r nextTree S vsM rest h'

theorem scanCutsV8_sound {fullVal r : ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {S : List ℕ} {vsM : List (ℕ × ℕ)} :
    ∀ (cs : List (List (ℕ × ℕ) × ℕ)) (h h' : ℕ), scanCutsV8 fullVal r nextTree S vsM cs h = some h' →
      ∀ p ∈ cs, ∃ a b, scanVsV8 fullVal r nextTree S p.1 p.2 vsM a = some b
  | [], _, _, _, _, hp => by simp at hp
  | (U'M, mU) :: rest, h, h', hall, p, hp => by
    unfold scanCutsV8 at hall
    cases hs : scanVsV8 fullVal r nextTree S U'M mU vsM h with
    | none => simp [hs] at hall
    | some h1 =>
      simp only [hs] at hall
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨h, h1, hs⟩
      · exact scanCutsV8_sound rest h1 h' hall p hp

def scanPairV (maskParam fullVal r : ℕ) (bits S : List ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (U'M : List (ℕ × ℕ)) (mU a b h : ℕ) : Option ℕ :=
  forceNat (a &&& b) fun v1 =>
  let h1 : Option ℕ :=
    if Nat.beq v1 0 || Nat.beq v1 65535 || memNat v1 S then some h
    else
      forceNat (sepM maskParam bits v1) fun mv1 =>
      if Nat.beq (mU ||| mv1) fullVal then stepUHintV8 fullVal r nextTree S v1 ((v1, mv1) :: U'M) h
      else some h
  match h1 with
  | none => none
  | some h' =>
    forceNat (a ||| b) fun v2 =>
    if Nat.beq v2 0 || Nat.beq v2 65535 || memNat v2 S then some h'
    else
      forceNat (sepM maskParam bits v2) fun mv2 =>
      if Nat.beq (mU ||| mv2) fullVal then stepUHintV8 fullVal r nextTree S v2 ((v2, mv2) :: U'M) h'
      else some h'

theorem scanPairV_sound {maskParam fullVal r : ℕ} {bits S : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {U'M : List (ℕ × ℕ)} {mU a b h h' : ℕ} {o : Fin 2}
    (hs : scanPairV maskParam fullVal r bits S nextTree U'M mU a b h = some h')
    (hnew : combM o a b ∈ valsNew S)
    (hcov : (mU ||| sepM maskParam bits (combM o a b)) = fullVal) :
    ∃ x y, stepUHintV8 fullVal r nextTree S (combM o a b) ((combM o a b, sepM maskParam bits (combM o a b)) :: U'M) x = some y := by
  obtain ⟨h0, h1, _, hnotS⟩ := valsNewD_props hnew
  unfold scanPairV at hs; simp only [forceNat_eq] at hs
  fin_cases o
  · simp only [combM] at h0 h1 hnotS hcov ⊢
    have hcf : (Nat.beq (a &&& b) 0 || Nat.beq (a &&& b) 65535 || memNat (a &&& b) S) = false := by
      cases hc : (Nat.beq (a &&& b) 0 || Nat.beq (a &&& b) 65535 || memNat (a &&& b) S) with
      | false => rfl
      | true => simp [Bool.or_eq_true, Nat.beq_eq, memNat_iff, h0, h1, hnotS] at hc
    rw [hcf] at hs
    simp only [Bool.false_eq_true, ↓reduceIte, hcov, Nat.beq_refl] at hs
    cases hst : stepUHintV8 fullVal r nextTree S (a &&& b) ((a &&& b, sepM maskParam bits (a &&& b)) :: U'M) h with
    | none => rw [hst] at hs; simp at hs
    | some h2 => exact ⟨h, h2, hst⟩
  · simp only [combM] at h0 h1 hnotS hcov ⊢
    have hcf : (Nat.beq (a ||| b) 0 || Nat.beq (a ||| b) 65535 || memNat (a ||| b) S) = false := by
      cases hc : (Nat.beq (a ||| b) 0 || Nat.beq (a ||| b) 65535 || memNat (a ||| b) S) with
      | false => rfl
      | true => simp [Bool.or_eq_true, Nat.beq_eq, memNat_iff, h0, h1, hnotS] at hc
    generalize h1eq : (if (Nat.beq (a &&& b) 0 || Nat.beq (a &&& b) 65535 || memNat (a &&& b) S) = true then some h
      else if Nat.beq (mU ||| sepM maskParam bits (a &&& b)) fullVal = true then
        stepUHintV8 fullVal r nextTree S (a &&& b) ((a &&& b, sepM maskParam bits (a &&& b)) :: U'M) h
      else some h) = r1 at hs
    cases r1 with
    | none => simp at hs
    | some h1v =>
      dsimp only at hs
      rw [hcf] at hs
      simp only [Bool.false_eq_true, ↓reduceIte, hcov, Nat.beq_refl] at hs
      exact ⟨h1v, h', hs⟩

def scanWithA (maskParam fullVal r : ℕ) (bits S : List ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (U'M : List (ℕ × ℕ)) (mU a : ℕ) : List ℕ → ℕ → Option ℕ
  | [], h => some h
  | b :: bs, h =>
    match scanPairV maskParam fullVal r bits S nextTree U'M mU a b h with
    | none => none
    | some h' => scanWithA maskParam fullVal r bits S nextTree U'M mU a bs h'

theorem scanWithA_sound {maskParam fullVal r : ℕ} {bits S : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {U'M : List (ℕ × ℕ)} {mU a : ℕ} :
    ∀ (bs : List ℕ) (h h' : ℕ), scanWithA maskParam fullVal r bits S nextTree U'M mU a bs h = some h' →
      ∀ b ∈ bs, ∃ x y, scanPairV maskParam fullVal r bits S nextTree U'M mU a b x = some y
  | [], _, _, _, _, hb => by simp at hb
  | b0 :: bs, h, h', hall, b, hb => by
    unfold scanWithA at hall
    cases hs : scanPairV maskParam fullVal r bits S nextTree U'M mU a b0 h with
    | none => simp [hs] at hall
    | some h1 =>
      simp only [hs] at hall
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨h, h1, hs⟩
      · exact scanWithA_sound bs h1 h' hall b hb

def scanTouchLoop (maskParam fullVal r : ℕ) (bits S : List ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (U'M : List (ℕ × ℕ)) (mU x : ℕ) : List ℕ → ℕ → Option ℕ
  | [], h => some h
  | a :: t, h =>
    if Nat.beq a x then scanWithA maskParam fullVal r bits S nextTree U'M mU a t h
    else
      match scanPairV maskParam fullVal r bits S nextTree U'M mU a x h with
      | none => none
      | some h' => scanTouchLoop maskParam fullVal r bits S nextTree U'M mU x t h'

theorem scanTouchLoop_sound {maskParam fullVal r : ℕ} {bits S : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {U'M : List (ℕ × ℕ)} {mU x : ℕ} :
    ∀ (l : List ℕ) (h h' : ℕ), l.Nodup → x ∈ l →
      scanTouchLoop maskParam fullVal r bits S nextTree U'M mU x l h = some h' →
      ∀ y ∈ l, y ≠ x →
        ∃ a b, scanPairV maskParam fullVal r bits S nextTree U'M mU x y a = some b ∨
               scanPairV maskParam fullVal r bits S nextTree U'M mU y x a = some b
  | [], _, _, _, hx, _, _, _, _ => by simp at hx
  | a :: t, h, h', hnd, hx, hall, y, hy, hyx => by
    obtain ⟨_, ht⟩ := List.nodup_cons.mp hnd
    unfold scanTouchLoop at hall
    by_cases hax : Nat.beq a x = true
    · simp only [hax, ↓reduceIte] at hall
      have haxe := Nat.eq_of_beq_eq_true hax; subst haxe
      rcases List.mem_cons.mp hy with rfl | hyt
      · exact absurd rfl hyx
      · obtain ⟨u, v, huv⟩ := scanWithA_sound t h h' hall y hyt
        exact ⟨u, v, Or.inl huv⟩
    · simp only [hax, ↓reduceIte] at hall
      have haxne : a ≠ x := fun he => hax (he ▸ Nat.beq_refl a)
      have hxt : x ∈ t := (List.mem_cons.mp hx).resolve_left (Ne.symm haxne)
      cases hs : scanPairV maskParam fullVal r bits S nextTree U'M mU a x h with
      | none => simp [hs] at hall
      | some h1 =>
        simp only [hs] at hall
        rcases List.mem_cons.mp hy with rfl | hyt
        · exact ⟨h, h1, Or.inr hs⟩
        · exact scanTouchLoop_sound t h1 h' ht hxt hall y hyt hyx

def tagEss (fullVal : ℕ) (preOr : ℕ) : List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ × Bool)
  | [], _ => []
  | (w, mw) :: rest, suf :: sufs =>
    forceNat (preOr ||| mw) fun nextPre =>
    (w, mw, !(Nat.beq (preOr ||| suf) fullVal)) :: tagEss fullVal nextPre rest sufs
  | _, [] => []

theorem tagEss_eq (f : ℕ → ℕ) (fullVal : ℕ) : ∀ (l : List ℕ) (preOr : ℕ), l.Nodup →
    tagEss fullVal preOr (l.map fun w => (w, f w)) (sufList f l).tail =
      l.map (fun w => (w, f w, !(Nat.beq (preOr ||| foldLor f (l.erase w)) fullVal)))
  | [], _, _ => rfl
  | a :: t, preOr, hnd => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, sufList, List.tail_cons]
    rw [sufList_head_tail f t]
    simp only [tagEss, forceNat_eq, List.erase_cons_head]
    congr 1
    rw [tagEss_eq f fullVal t (preOr ||| f a) ht]
    apply List.map_congr_left
    intro w hw
    have hne : a ≠ w := fun h => ha (h ▸ hw)
    have hbeq : ¬ (a == w) = true := by simp [hne]
    rw [List.erase_cons_tail hbeq, foldLor_cons, Nat.lor_assoc]

def goDrop1 (maskParam fullVal r : ℕ) (bits S : List ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (vsM : List (ℕ × ℕ)) (preM : List (ℕ × ℕ)) (preOr : ℕ) :
    List (ℕ × ℕ × Bool) → List ℕ → ℕ → Option ℕ
  | [], _, h => some h
  | (x, mx, ex) :: rest, suf :: sufs, h =>
    forceNat (preOr ||| suf) fun mU =>
    let U'M := preM ++ rest.map (fun p => (p.1, p.2.1))
    let res :=
      if ex then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU x S h
      else scanVsV8 fullVal r nextTree S U'M mU vsM h
    match res with
    | none => none
    | some h' => forceNat (preOr ||| mx) fun nextPre => goDrop1 maskParam fullVal r bits S nextTree vsM ((x, mx) :: preM) nextPre rest sufs h'
  | _, [], _ => none

theorem goDrop1_sound {maskParam fullVal r : ℕ} {bits S : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {vsM : List (ℕ × ℕ)} {f : ℕ → ℕ} {efn : ℕ → Bool} :
    ∀ (l pre : List ℕ) (h h' : ℕ), l.Nodup → pre.Nodup → (∀ z ∈ pre, z ∉ l) →
      goDrop1 maskParam fullVal r bits S nextTree vsM
        (pre.map fun w => (w, f w)) (foldLor f pre)
        (l.map fun w => (w, f w, efn w)) (sufList f l).tail h = some h' →
      ∀ x ∈ l, ∃ (U' : List ℕ) (a b : ℕ),
        U'.Nodup ∧ (∀ z, z ∈ U' ↔ z ∈ pre ∨ (z ∈ l ∧ z ≠ x)) ∧
        (let U'M := U'.map fun w => (w, f w)
         let mU := foldLor f U'
         (if efn x then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU x S a
          else scanVsV8 fullVal r nextTree S U'M mU vsM a) = some b)
  | [], _, _, _, _, _, _, _, _, hx => by simp at hx
  | a :: t, pre, h, h', hnd, hpre_nd, hdisj, hall, x, hx => by
    obtain ⟨ha_nt, ht_nd⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, sufList, List.tail_cons] at hall
    rw [sufList_head_tail f t] at hall
    unfold goDrop1 at hall; simp only [forceNat_eq] at hall
    have hmap_t : (t.map fun w => (w, f w, efn w)).map (fun p => (p.1, p.2.1)) = t.map (fun w => (w, f w)) := by
      simp [List.map_map, Function.comp_def]
    rw [hmap_t, ← List.map_append, ← foldLor_append] at hall
    cases hres : (if efn a then scanTouchLoop maskParam fullVal r bits S nextTree ((pre ++ t).map fun w => (w, f w)) (foldLor f (pre ++ t)) a S h
        else scanVsV8 fullVal r nextTree S ((pre ++ t).map fun w => (w, f w)) (foldLor f (pre ++ t)) vsM h) with
    | none => rw [hres] at hall; simp at hall
    | some h1 =>
      rw [hres] at hall; dsimp only at hall
      rcases List.mem_cons.mp hx with rfl | hxt
      · refine ⟨pre ++ t, h, h1, ?_, ?_, hres⟩
        · exact List.nodup_append.mpr ⟨hpre_nd, ht_nd, fun z hz w hw he => hdisj z hz (he ▸ List.mem_cons_of_mem _ hw)⟩
        · intro z; simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro (hzp | hzt)
            · exact Or.inl hzp
            · exact Or.inr ⟨Or.inr hzt, fun he => ha_nt (he ▸ hzt)⟩
          · rintro (hzp | ⟨rfl | hzt, hne⟩)
            · exact Or.inl hzp
            · exact absurd rfl hne
            · exact Or.inr hzt
      · have hap : a ∉ pre := fun hm => hdisj a hm (by simp)
        have hpre'_nd : (a :: pre).Nodup := List.nodup_cons.mpr ⟨hap, hpre_nd⟩
        have hdisj' : ∀ z ∈ a :: pre, z ∉ t := by
          intro z hz; rcases List.mem_cons.mp hz with rfl | hzp
          · exact ha_nt
          · exact fun hzt => hdisj z hzp (List.mem_cons_of_mem _ hzt)
        have hlor' : foldLor f pre ||| f a = foldLor f (a :: pre) := by rw [Nat.lor_comm, ← foldLor_cons]
        rw [hlor', show (a, f a) :: pre.map (fun w => (w, f w)) = (a :: pre).map (fun w => (w, f w)) from rfl] at hall
        obtain ⟨U', u, v, hU'nd, hU'mem, hU'res⟩ := goDrop1_sound t (a :: pre) h1 h' ht_nd hpre'_nd hdisj' hall x hxt
        have hxa : x ≠ a := fun he => ha_nt (he ▸ hxt)
        refine ⟨U', u, v, hU'nd, ?_, hU'res⟩
        intro z; rw [hU'mem z]; simp only [List.mem_cons]
        constructor
        · rintro ((rfl | hzp) | ⟨hzt, hzx⟩)
          · exact Or.inr ⟨Or.inl rfl, Ne.symm hxa⟩
          · exact Or.inl hzp
          · exact Or.inr ⟨Or.inr hzt, hzx⟩
        · rintro (hzp | ⟨rfl | hzt, hzx⟩)
          · exact Or.inl (Or.inr hzp)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨hzt, hzx⟩

def goDrop2Inner (maskParam fullVal r : ℕ) (bits S : List ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (vsM : List (ℕ × ℕ)) (x : ℕ) (ex : Bool) (preM : List (ℕ × ℕ)) (preOr : ℕ) :
    List (ℕ × ℕ × Bool) → List ℕ → ℕ → Option ℕ
  | [], _, h => some h
  | (y, my, ey) :: rest, suf :: sufs, h =>
    forceNat (preOr ||| suf) fun mU =>
    let U'M := preM ++ rest.map (fun p => (p.1, p.2.1))
    let res :=
      if ex && ey then scanPairV maskParam fullVal r bits S nextTree U'M mU x y h
      else if ex then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU x S h
      else if ey then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU y S h
      else scanVsV8 fullVal r nextTree S U'M mU vsM h
    match res with
    | none => none
    | some h' => forceNat (preOr ||| my) fun nextPre => goDrop2Inner maskParam fullVal r bits S nextTree vsM x ex ((y, my) :: preM) nextPre rest sufs h'
  | _, [], _ => none

def goDrop2Outer (maskParam fullVal r : ℕ) (bits S : List ℕ) (nextTree : BinaryTree (ℕ × ℕ))
    (vsM : List (ℕ × ℕ)) (preM : List (ℕ × ℕ)) (preOr : ℕ) :
    List (ℕ × ℕ × Bool) → List ℕ → ℕ → Option ℕ
  | [], _, h => some h
  | (x, mx, ex) :: rest, _ :: sufs, h =>
    match goDrop2Inner maskParam fullVal r bits S nextTree vsM x ex preM preOr rest sufs h with
    | none => none
    | some h' => forceNat (preOr ||| mx) fun nextPre => goDrop2Outer maskParam fullVal r bits S nextTree vsM ((x, mx) :: preM) nextPre rest sufs h'
  | _, [], _ => none

theorem goDrop2Inner_sound {maskParam fullVal r : ℕ} {bits S : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {vsM : List (ℕ × ℕ)} {f : ℕ → ℕ} {efn : ℕ → Bool} {x : ℕ} {ex : Bool} :
    ∀ (l pre : List ℕ) (h h' : ℕ), l.Nodup → pre.Nodup → (∀ z ∈ pre, z ∉ l) →
      goDrop2Inner maskParam fullVal r bits S nextTree vsM x ex
        (pre.map fun w => (w, f w)) (foldLor f pre)
        (l.map fun w => (w, f w, efn w)) (sufList f l).tail h = some h' →
      ∀ y ∈ l, ∃ (U' : List ℕ) (a b : ℕ),
        U'.Nodup ∧ (∀ z, z ∈ U' ↔ z ∈ pre ∨ (z ∈ l ∧ z ≠ y)) ∧
        (let U'M := U'.map fun w => (w, f w)
         let mU := foldLor f U'
         (if ex && efn y then scanPairV maskParam fullVal r bits S nextTree U'M mU x y a
          else if ex then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU x S a
          else if efn y then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU y S a
          else scanVsV8 fullVal r nextTree S U'M mU vsM a) = some b)
  | [], _, _, _, _, _, _, _, _, hy => by simp at hy
  | a :: t, pre, h, h', hnd, hpre_nd, hdisj, hall, y, hy => by
    obtain ⟨ha_nt, ht_nd⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, sufList, List.tail_cons] at hall
    rw [sufList_head_tail f t] at hall
    unfold goDrop2Inner at hall; simp only [forceNat_eq] at hall
    have hmap_t : (t.map fun w => (w, f w, efn w)).map (fun p => (p.1, p.2.1)) = t.map (fun w => (w, f w)) := by
      simp [List.map_map, Function.comp_def]
    rw [hmap_t, ← List.map_append, ← foldLor_append] at hall
    cases hres : (if ex && efn a then scanPairV maskParam fullVal r bits S nextTree ((pre ++ t).map fun w => (w, f w)) (foldLor f (pre ++ t)) x a h
        else if ex then scanTouchLoop maskParam fullVal r bits S nextTree ((pre ++ t).map fun w => (w, f w)) (foldLor f (pre ++ t)) x S h
        else if efn a then scanTouchLoop maskParam fullVal r bits S nextTree ((pre ++ t).map fun w => (w, f w)) (foldLor f (pre ++ t)) a S h
        else scanVsV8 fullVal r nextTree S ((pre ++ t).map fun w => (w, f w)) (foldLor f (pre ++ t)) vsM h) with
    | none => rw [hres] at hall; simp at hall
    | some h1 =>
      rw [hres] at hall; dsimp only at hall
      rcases List.mem_cons.mp hy with rfl | hyt
      · refine ⟨pre ++ t, h, h1, ?_, ?_, hres⟩
        · exact List.nodup_append.mpr ⟨hpre_nd, ht_nd, fun z hz w hw he => hdisj z hz (he ▸ List.mem_cons_of_mem _ hw)⟩
        · intro z; simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro (hzp | hzt)
            · exact Or.inl hzp
            · exact Or.inr ⟨Or.inr hzt, fun he => ha_nt (he ▸ hzt)⟩
          · rintro (hzp | ⟨rfl | hzt, hne⟩)
            · exact Or.inl hzp
            · exact absurd rfl hne
            · exact Or.inr hzt
      · have hap : a ∉ pre := fun hm => hdisj a hm (by simp)
        have hpre'_nd : (a :: pre).Nodup := List.nodup_cons.mpr ⟨hap, hpre_nd⟩
        have hdisj' : ∀ z ∈ a :: pre, z ∉ t := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hzp
          · exact ha_nt
          · exact fun hzt => hdisj z hzp (List.mem_cons_of_mem _ hzt)
        have hlor' : foldLor f pre ||| f a = foldLor f (a :: pre) := by rw [Nat.lor_comm, ← foldLor_cons]
        rw [hlor', show (a, f a) :: pre.map (fun w => (w, f w)) = (a :: pre).map (fun w => (w, f w)) from rfl] at hall
        obtain ⟨U', u, v, hU'nd, hU'mem, hU'res⟩ := goDrop2Inner_sound t (a :: pre) h1 h' ht_nd hpre'_nd hdisj' hall y hyt
        have hya : y ≠ a := fun he => ha_nt (he ▸ hyt)
        refine ⟨U', u, v, hU'nd, ?_, hU'res⟩
        intro z; rw [hU'mem z]; simp only [List.mem_cons]
        constructor
        · rintro ((rfl | hzp) | ⟨hzt, hzy⟩)
          · exact Or.inr ⟨Or.inl rfl, Ne.symm hya⟩
          · exact Or.inl hzp
          · exact Or.inr ⟨Or.inr hzt, hzy⟩
        · rintro (hzp | ⟨rfl | hzt, hzy⟩)
          · exact Or.inl (Or.inr hzp)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨hzt, hzy⟩

theorem goDrop2Outer_sound {maskParam fullVal r : ℕ} {bits S : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)}
    {vsM : List (ℕ × ℕ)} {f : ℕ → ℕ} {efn : ℕ → Bool} :
    ∀ (l pre : List ℕ) (h h' : ℕ), l.Nodup → pre.Nodup → (∀ z ∈ pre, z ∉ l) →
      goDrop2Outer maskParam fullVal r bits S nextTree vsM
        (pre.map fun w => (w, f w)) (foldLor f pre)
        (l.map fun w => (w, f w, efn w)) (sufList f l).tail h = some h' →
      ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∃ (p q : ℕ) (U' : List ℕ) (a b : ℕ),
        ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) ∧
        U'.Nodup ∧ (∀ z, z ∈ U' ↔ z ∈ pre ∨ (z ∈ l ∧ z ≠ p ∧ z ≠ q)) ∧
        (let U'M := U'.map fun w => (w, f w)
         let mU := foldLor f U'
         (if efn p && efn q then scanPairV maskParam fullVal r bits S nextTree U'M mU p q a
          else if efn p then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU p S a
          else if efn q then scanTouchLoop maskParam fullVal r bits S nextTree U'M mU q S a
          else scanVsV8 fullVal r nextTree S U'M mU vsM a) = some b)
  | [], _, _, _, _, _, _, _, _, hx, _, _, _ => by simp at hx
  | a :: t, pre, h, h', hnd, hpre_nd, hdisj, hall, x, hx, y, hy, hxy => by
    obtain ⟨ha_nt, ht_nd⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, sufList, List.tail_cons] at hall
    rw [sufList_head_tail f t] at hall
    unfold goDrop2Outer at hall; simp only [forceNat_eq] at hall
    cases hin : goDrop2Inner maskParam fullVal r bits S nextTree vsM a (efn a) (pre.map fun w => (w, f w)) (foldLor f pre)
        (t.map fun w => (w, f w, efn w)) (sufList f t).tail h with
    | none => rw [hin] at hall; simp at hall
    | some h1 =>
      rw [hin] at hall
      have hdisj_t : ∀ z ∈ pre, z ∉ t := fun z hz hzt => hdisj z hz (List.mem_cons_of_mem _ hzt)
      rcases List.mem_cons.mp hx with rfl | hxt <;> rcases List.mem_cons.mp hy with rfl | hyt
      · exact absurd rfl hxy
      · obtain ⟨U', u, v, hU'nd, hU'mem, hU'res⟩ := goDrop2Inner_sound t pre h h1 ht_nd hpre_nd hdisj_t hin y hyt
        refine ⟨x, y, U', u, v, Or.inl ⟨rfl, rfl⟩, hU'nd, ?_, hU'res⟩
        intro z; rw [hU'mem z]; simp only [List.mem_cons]
        constructor
        · rintro (hzp | ⟨hzt, hzy⟩)
          · exact Or.inl hzp
          · exact Or.inr ⟨Or.inr hzt, fun he => ha_nt (he ▸ hzt), hzy⟩
        · rintro (hzp | ⟨rfl | hzt, hza, hzy⟩)
          · exact Or.inl hzp
          · exact absurd rfl hza
          · exact Or.inr ⟨hzt, hzy⟩
      · obtain ⟨U', u, v, hU'nd, hU'mem, hU'res⟩ := goDrop2Inner_sound t pre h h1 ht_nd hpre_nd hdisj_t hin x hxt
        refine ⟨y, x, U', u, v, Or.inr ⟨rfl, rfl⟩, hU'nd, ?_, hU'res⟩
        intro z; rw [hU'mem z]; simp only [List.mem_cons]
        constructor
        · rintro (hzp | ⟨hzt, hzx⟩)
          · exact Or.inl hzp
          · exact Or.inr ⟨Or.inr hzt, fun he => ha_nt (he ▸ hzt), hzx⟩
        · rintro (hzp | ⟨rfl | hzt, hza, hzx⟩)
          · exact Or.inl hzp
          · exact absurd rfl hza
          · exact Or.inr ⟨hzt, hzx⟩
      · have hap : a ∉ pre := fun hm => hdisj a hm (by simp)
        have hpre'_nd : (a :: pre).Nodup := List.nodup_cons.mpr ⟨hap, hpre_nd⟩
        have hdisj' : ∀ z ∈ a :: pre, z ∉ t := by
          intro z hz; rcases List.mem_cons.mp hz with rfl | hzp
          · exact ha_nt
          · exact fun hzt => hdisj z hzp (List.mem_cons_of_mem _ hzt)
        have hlor' : foldLor f pre ||| f a = foldLor f (a :: pre) := by rw [Nat.lor_comm, ← foldLor_cons]
        rw [hlor', show (a, f a) :: pre.map (fun w => (w, f w)) = (a :: pre).map (fun w => (w, f w)) from rfl] at hall
        obtain ⟨p, q, U', u, v, hpq, hU'nd, hU'mem, hU'res⟩ := goDrop2Outer_sound t (a :: pre) h1 h' ht_nd hpre'_nd hdisj' hall x hxt y hyt hxy
        have hpa : p ≠ a := by rcases hpq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> intro he <;> exact ha_nt (he ▸ ‹_›)
        have hqa : q ≠ a := by rcases hpq with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> intro he <;> exact ha_nt (he ▸ ‹_›)
        refine ⟨p, q, U', u, v, hpq, hU'nd, ?_, hU'res⟩
        intro z; rw [hU'mem z]; simp only [List.mem_cons]
        constructor
        · rintro ((rfl | hzp) | ⟨hzt, hzp', hzq'⟩)
          · exact Or.inr ⟨Or.inl rfl, Ne.symm hpa, Ne.symm hqa⟩
          · exact Or.inl hzp
          · exact Or.inr ⟨Or.inr hzt, hzp', hzq'⟩
        · rintro (hzp | ⟨rfl | hzt, hzp', hzq'⟩)
          · exact Or.inl (Or.inr hzp)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨hzt, hzp', hzq'⟩

def verifyNodeV8 (maskParam fullVal k : ℕ) (bits : List ℕ) (nextTree : BinaryTree (ℕ × ℕ)) (packedS h : ℕ) : Bool :=
  forceListN (unpack packedS) fun S =>
  forceListP (S.map (fun w => (w, sepM maskParam bits w))) fun SM =>
  if isStrict S && S.all (fun w => !(Nat.beq w 0) && !(Nat.beq w 65535)) then
    if Nat.beq S.length (k + 2) then
      match sufOrs SM with
      | [] => false
      | _ :: sufs =>
        let tagged := tagEss fullVal 0 SM sufs
        forceListP (if Nat.ble 2 (countNonEss tagged) then (valsNew S).map (fun v => (v, sepM maskParam bits v)) else []) fun vsM =>
        (goDrop2Outer maskParam fullVal k bits S nextTree vsM [] 0 tagged sufs h).isSome
    else if Nat.beq S.length (k + 1) then
      match sufOrs SM with
      | [] => false
      | _ :: sufs =>
        let tagged := tagEss fullVal 0 SM sufs
        forceListP (if Nat.ble 1 (countNonEss tagged) then (valsNew S).map (fun v => (v, sepM maskParam bits v)) else []) fun vsM =>
        (goDrop1 maskParam fullVal k bits S nextTree vsM [] 0 tagged sufs h).isSome
    else
      forceListP ((valsNew S).map (fun v => (v, sepM maskParam bits v))) fun vsM =>
      (scanCutsV8 fullVal k nextTree S vsM (cutsMP k SM) h).isSome
  else false

theorem initV8_sound {s : ℕ} {bits : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {h h' : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false)
    (hchk : checkCutsInitV8 (fullM targetNat bits) s nextTree (cutsMP (s + 1) (inputs.map fun w => (w, sepM targetNat bits w))) h = some h')
    (seq : List (Fin 2 × ℕ × ℕ)) (hseq_len : seq.length = s) (hseq_le : s ≤ 10)
    (hmin : MinimalFor targetNat inputs.toFinset seq) (hs1 : 1 ≤ s) :
    ∃ x, InTree x nextTree ∧ ReachMin 10 s (unpack x).toFinset := by
  have hTcard : (inputs.toFinset ∩ usedBy seq).card ≤ s + 1 := by
    simpa [endSet] using usedWires_card hmin (m := 0) (r := s) (by simpa using hseq_len.symm)
  obtain ⟨U, hU, hTU⟩ := cutsSpec (s + 1) inputs (inputs.toFinset ∩ usedBy seq) Finset.inter_subset_left hTcard
  have hUsub_l : ∀ z ∈ U, z ∈ inputs := cuts_mem_sub inputs (s + 1) U hU
  have hUsub : U.toFinset ⊆ inputs.toFinset := fun z hz => List.mem_toFinset.mpr (hUsub_l z (List.mem_toFinset.mp hz))
  have hU_lt : ∀ z ∈ U, z < 65536 := fun z hz => inputs_lt z (hUsub_l z hz)
  have hI_nz : ∀ z ∈ inputs, z ≠ 0 ∧ z ≠ 65535 := by decide
  have hU_nz : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 65535 := fun z hz => hI_nz z (hUsub_l z hz)
  have hU_nd : U.Nodup := cuts_nodup inputs (s + 1) U inputs_nodup hU
  have hcT : CanM targetNat s (inputs.toFinset ∩ usedBy seq) := by
    simpa [endSet] using usedWires_canM hmin (m := 0) (r := s) (by simpa using hseq_len.symm) hs1
  have hcU : CanM targetNat s U.toFinset := monoCMD hTU hcT
  have hcov := coveredM_sepM hM hcU bits hbits
  have hmem := cutsMP_spec (sepM targetNat bits) inputs (s + 1) U hU
  obtain ⟨a, b, hs⟩ := checkCutsInitV8_sound _ h h' hchk _ hmem hcov
  exact stepInitHintV8_sound hM hbits hU_lt hU_nz hU_nd hs seq hseq_len hseq_le hmin hs1 hUsub hTU

theorem advanceNodeV8 {k : ℕ} {bits : List ℕ} {nextTree : BinaryTree (ℕ × ℕ)} {packedS h : ℕ}
    (hM : targetNat < 2 ^ 16) (hbits : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false) (hk1 : 1 ≤ k)
    (hv : verifyNodeV8 targetNat (fullM targetNat bits) k bits nextTree packedS h = true)
    (hrm : ReachMin 10 (k + 1) (unpack packedS).toFinset) :
    ∃ x, InTree x nextTree ∧ ReachMin 10 k (unpack x).toFinset := by
  unfold verifyNodeV8 at hv; simp only [forceListN_eq, forceListP_eq] at hv
  set S := unpack packedS with hS_def
  have hS_lt : ∀ x ∈ S, x < 65536 := unpack_lt packedS
  by_cases hvalid : (isStrict S && S.all fun w => !(Nat.beq w 0) && !(Nat.beq w 65535)) = true
  · simp only [hvalid, ↓reduceIte] at hv
    have hvp := Bool.and_eq_true _ _ |>.mp hvalid
    have hnd : S.Nodup := isStrict_nodup S hvp.1
    have hS_nz : ∀ w ∈ S, w ≠ 0 ∧ w ≠ 65535 := by
      intro w hw
      have h1 := List.all_eq_true.mp hvp.2 w hw
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      exact ⟨fun he => by rw [he] at h1; simp at h1, fun he => by rw [he] at h1; simp at h1⟩
    obtain ⟨seq, m, hlenK, hmin, hmr, hSsub, hTsub⟩ := hrm
    have hm_lt : m < seq.length := by omega
    set st := stepAt seq m
    set v := stepVal st
    have hv_step : ValidSeq inputs.toFinset seq := hmin.1
    rw [stepAt_eq_take_drop seq m hm_lt, validSeq_append, validSeq_append] at hv_step
    simp only [ValidSeq] at hv_step
    obtain ⟨haSm, hbSm, _⟩ := hv_step.1.2
    have liftToS : ∀ {w : ℕ}, freeM (endSet inputs.toFinset (seq.take m)) w → w ∈ usedBy (seq.drop m) → freeM S.toFinset w := by
      intro w hw hu
      rcases hw with rfl | rfl | hm'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hTsub (Finset.mem_inter.mpr ⟨hm', hu⟩)))
    have ha : freeM S.toFinset st.2.1 := liftToS haSm ((mem_usedBy_drop_iff seq m _).mpr ⟨m, le_refl m, hm_lt, Or.inl rfl⟩)
    have hb : freeM S.toFinset st.2.2 := liftToS hbSm ((mem_usedBy_drop_iff seq m _).mpr ⟨m, le_refl m, hm_lt, Or.inr rfl⟩)
    have hv_not_Sm : ¬ freeM (endSet inputs.toFinset (seq.take m)) v := minimal_new hmin hm_lt
    have hv_not_freeS : ¬ freeM S.toFinset v := fun hf => hv_not_Sm (freeMDMono hSsub hf)
    have hnew : v ∈ valsNew S := by
      have hSsub65 : ∀ x ∈ S, x &&& 65535 = x := fun x hx => and_65535_of_lt (hS_lt x hx)
      rcases combMD_case hSsub65 ha hb with hfr | hnw
      · exact absurd hfr hv_not_freeS
      · exact hnw
    obtain ⟨hv0, hv65, _, hv_notS⟩ := valsNewD_props hnew
    have hv_lt : v < 65536 := by
      simp only [valsNew, valsNewD, List.mem_filter] at hnew
      exact opPairsM_lt S hS_lt _ hnew.1
    have hSm1 : endSet inputs.toFinset (seq.take (m + 1)) = insert v (endSet inputs.toFinset (seq.take m)) := by
      rw [take_succ_stepAt seq m hm_lt, endSet_append, endSet, endSet]
    have hSv_sub : (v :: S).toFinset ⊆ endSet inputs.toFinset (seq.take (m + 1)) := by
      rw [hSm1]; intro z hz
      rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hSsub (List.mem_toFinset.mpr hz))
    set T1 := endSet inputs.toFinset (seq.take (m + 1)) ∩ usedBy (seq.drop (m + 1))
    have hT1_card : T1.card ≤ k + 1 := usedWires_card hmin (m := m + 1) (r := k) (by omega)
    have hT1_can : CanM targetNat k T1 := usedWires_canM hmin (m := m + 1) (r := k) (by omega) hk1
    have hvT1 : v ∈ T1 := by
      refine Finset.mem_inter.mpr ⟨by rw [hSm1]; exact Finset.mem_insert_self _ _,
        minimal_used hmin hm_lt (minimal_no_early_target hmin hm_lt (by omega))⟩
    have hT1_erase_sub : T1.erase v ⊆ S.toFinset := by
      intro z hz
      have hne : z ≠ v := Finset.ne_of_mem_erase hz
      have hz1 := Finset.mem_inter.mp (Finset.mem_of_mem_erase hz)
      rw [hSm1] at hz1
      have hzSm : z ∈ endSet inputs.toFinset (seq.take m) := (Finset.mem_insert.mp hz1.1).resolve_left hne
      have hzUm : z ∈ usedBy (seq.drop m) := by
        obtain ⟨j, hj1, hj2, hread⟩ := (mem_usedBy_drop_iff seq (m + 1) z).mp hz1.2
        exact (mem_usedBy_drop_iff seq m z).mpr ⟨j, by omega, hj2, hread⟩
      exact hTsub (Finset.mem_inter.mpr ⟨hzSm, hzUm⟩)
    have hT1_erase_card : (T1.erase v).card ≤ k := by rw [Finset.card_erase_of_mem hvT1]; omega
    by_cases hlen : Nat.beq S.length (k + 2) = true
    · simp only [hlen, ↓reduceIte] at hv
      have hlen_eq : S.length = k + 2 := Nat.eq_of_beq_eq_true hlen
      set T' := T1.erase v
      have hScard : S.toFinset.card = k + 2 := by rw [List.toFinset_card_of_nodup hnd, hlen_eq]
      have hsum : (S.toFinset \ T').card + T'.card = S.toFinset.card := by
        rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hT1_erase_sub]
      obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < (S.toFinset \ T').card)
      obtain ⟨y0, hy0⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx0]; omega : 0 < ((S.toFinset \ T').erase x0).card)
      have hyx : y0 ≠ x0 := Finset.ne_of_mem_erase hy0
      have hy0D : y0 ∈ S.toFinset \ T' := Finset.mem_of_mem_erase hy0
      have hx0S : x0 ∈ S := List.mem_toFinset.mp (Finset.mem_sdiff.mp hx0).1
      have hx0T : x0 ∉ T' := (Finset.mem_sdiff.mp hx0).2
      have hy0S : y0 ∈ S := List.mem_toFinset.mp (Finset.mem_sdiff.mp hy0D).1
      have hy0T : y0 ∉ T' := (Finset.mem_sdiff.mp hy0D).2
      rw [sufOrs_eq (sepM targetNat bits) S, sufList_head_tail] at hv
      dsimp only at hv
      set efn : ℕ → Bool := fun w => !(Nat.beq (foldLor (sepM targetNat bits) (S.erase w)) (fullM targetNat bits))
      have hte := tagEss_eq (sepM targetNat bits) (fullM targetNat bits) S 0 hnd
      simp only [Nat.zero_or] at hte
      rw [hte, Option.isSome_iff_exists] at hv
      obtain ⟨h2, hall2⟩ := hv
      have hpre0 : (0 : ℕ) = foldLor (sepM targetNat bits) [] := rfl
      rw [hpre0, show ([] : List (ℕ × ℕ)) = ([] : List ℕ).map (fun w => (w, sepM targetNat bits w)) from rfl] at hall2
      obtain ⟨p, q, U', a1, b1, hpq_or, hndU', hU'mem0, hsc⟩ :=
        goDrop2Outer_sound S [] h h2 hnd List.nodup_nil (by simp) hall2 x0 hx0S y0 hy0S (Ne.symm hyx)
      have ⟨hpS, hqS, hpq, hpT, hqT⟩ : p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ∉ T' ∧ q ∉ T' := by
        rcases hpq_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hx0S, hy0S, Ne.symm hyx, hx0T, hy0T⟩
        · exact ⟨hy0S, hx0S, hyx, hy0T, hx0T⟩
      have hU'mem : ∀ z, z ∈ U' ↔ z ∈ S ∧ z ≠ p ∧ z ≠ q := fun z => by simpa using hU'mem0 z
      have hU'p : ∀ z ∈ U', z ∈ S.erase p := fun z hz => (mem_erase_of_nodup hnd).mpr ⟨((hU'mem z).mp hz).1, ((hU'mem z).mp hz).2.1⟩
      have hU'q : ∀ z ∈ U', z ∈ S.erase q := fun z hz => (mem_erase_of_nodup hnd).mpr ⟨((hU'mem z).mp hz).1, ((hU'mem z).mp hz).2.2⟩
      have hsubT : T1 ⊆ (v :: U').toFinset := by
        intro z hz; by_cases ez : z = v
        · simp [ez]
        · have hzT' : z ∈ T' := Finset.mem_erase.mpr ⟨ez, hz⟩
          exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((hU'mem z).mpr ⟨List.mem_toFinset.mp (hT1_erase_sub hzT'), fun h => hpT (h ▸ hzT'), fun h => hqT (h ▸ hzT')⟩))
      have hUsub : (v :: U').toFinset ⊆ endSet inputs.toFinset (seq.take (m + 1)) := by
        intro z hz; apply hSv_sub; rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
        · simp
        · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((hU'mem z).mp hz).1)
      have hU_lt : ∀ z ∈ v :: U', z < 65536 := fun z hz => by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hv_lt
        · exact hS_lt z ((hU'mem z).mp hz).1
      have hU_nz : ∀ z ∈ v :: U', z ≠ 0 ∧ z ≠ 65535 := fun z hz => by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hv0, hv65⟩
        · exact hS_nz z ((hU'mem z).mp hz).1
      have hU_nd : (v :: U').Nodup := List.nodup_cons.mpr ⟨fun h => hv_notS ((hU'mem v).mp h).1, hndU'⟩
      have hcU := monoCMD hsubT hT1_can
      have hcov : foldLor (sepM targetNat bits) U' ||| sepM targetNat bits v = fullM targetNat bits := by
        rw [Nat.lor_comm, ← foldLor_cons]; exact coveredM_sepM hM hcU bits hbits
      have finish_pair : ∀ (x1 x2 : ℕ), v = combM st.1 x1 x2 →
          (∃ u1 u2, scanPairV targetNat (fullM targetNat bits) k bits S nextTree (U'.map fun w => (w, sepM targetNat bits w)) (foldLor (sepM targetNat bits) U') x1 x2 u1 = some u2 ∨
                    scanPairV targetNat (fullM targetNat bits) k bits S nextTree (U'.map fun w => (w, sepM targetNat bits w)) (foldLor (sepM targetNat bits) U') x2 x1 u1 = some u2) →
          ∃ x, InTree x nextTree ∧ ReachMin 10 k (unpack x).toFinset := by
        intro x1 x2 hce ⟨u1, u2, hsp⟩
        have hst : ∃ a2 b2, stepUHintV8 (fullM targetNat bits) k nextTree S v ((v, sepM targetNat bits v) :: U'.map fun w => (w, sepM targetNat bits w)) a2 = some b2 := by
          rcases hsp with hsp1 | hsp2
          · rw [hce] at hnew hcov ⊢; exact scanPairV_sound hsp1 hnew hcov
          · have hce2 : v = combM st.1 x2 x1 := by rw [hce, combM_comm]
            rw [hce2] at hnew hcov ⊢; exact scanPairV_sound hsp2 hnew hcov
        obtain ⟨a2, b2, hst'⟩ := hst
        exact stepUHintV8_sound hM hbits hnd hv_notS hU_lt hU_nz hU_nd hst' seq (m + 1) hlenK hmin (by omega) hk1 hSv_sub hUsub hsubT hvT1
      cases hep : efn p <;> cases heq : efn q
      · dsimp only [efn] at hep heq
        simp only [hep, heq, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hsc
        have hge2 : Nat.ble 2 (countNonEss (S.map fun w => (w, sepM targetNat bits w, efn w))) = true :=
          Nat.ble_eq.mpr (countNonEss_ge_two (sepM targetNat bits) efn S hnd p q hpS hqS hpq hep heq)
        dsimp only [efn] at hge2
        simp only [hge2, ↓reduceIte] at hsc
        have hvmem : (v, sepM targetNat bits v) ∈ (valsNew S).map (fun w => (w, sepM targetNat bits w)) := List.mem_map.mpr ⟨v, hnew, rfl⟩
        obtain ⟨a2, b2, hst⟩ := scanVsV8_sound _ a1 b1 hsc _ hvmem hcov
        exact stepUHintV8_sound hM hbits hnd hv_notS hU_lt hU_nz hU_nd hst seq (m + 1) hlenK hmin (by omega) hk1 hSv_sub hUsub hsubT hvT1
      · dsimp only [efn] at hep heq
        simp only [hep, heq, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hsc
        have hqab := ess_forces_input hM hbits heq hU'q ha hb hcU
        obtain ⟨z, hzS, hzq, hce⟩ : ∃ z, z ∈ S ∧ z ≠ q ∧ v = combM st.1 q z := by
          rcases hqab with haq | hbq
          · obtain ⟨hbS, hbq'⟩ := combM_new_other_mem hS_lt hqS hb (by rw [← haq]; exact hnew)
            exact ⟨st.2.2, hbS, hbq', by change combM st.1 st.2.1 st.2.2 = _; rw [haq]⟩
          · obtain ⟨haS, haq'⟩ := combM_new_other_mem hS_lt hqS ha (by rw [combM_comm, ← hbq]; exact hnew)
            exact ⟨st.2.1, haS, haq', by change combM st.1 st.2.1 st.2.2 = _; rw [hbq, combM_comm]⟩
        exact finish_pair q z hce (scanTouchLoop_sound S a1 b1 hnd hqS hsc z hzS hzq)
      · dsimp only [efn] at hep heq
        simp only [hep, heq, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hsc
        have hpab := ess_forces_input hM hbits hep hU'p ha hb hcU
        obtain ⟨z, hzS, hzp, hce⟩ : ∃ z, z ∈ S ∧ z ≠ p ∧ v = combM st.1 p z := by
          rcases hpab with hap | hbp
          · obtain ⟨hbS, hbp'⟩ := combM_new_other_mem hS_lt hpS hb (by rw [← hap]; exact hnew)
            exact ⟨st.2.2, hbS, hbp', by change combM st.1 st.2.1 st.2.2 = _; rw [hap]⟩
          · obtain ⟨haS, hap'⟩ := combM_new_other_mem hS_lt hpS ha (by rw [combM_comm, ← hbp]; exact hnew)
            exact ⟨st.2.1, haS, hap', by change combM st.1 st.2.1 st.2.2 = _; rw [hbp, combM_comm]⟩
        exact finish_pair p z hce (scanTouchLoop_sound S a1 b1 hnd hpS hsc z hzS hzp)
      · dsimp only [efn] at hep heq
        simp only [hep, heq, Bool.and_true, ↓reduceIte] at hsc
        have hpab := ess_forces_input hM hbits hep hU'p ha hb hcU
        have hqab := ess_forces_input hM hbits heq hU'q ha hb hcU
        have hce : v = combM st.1 p q := by
          rcases hpab with hap | hbp <;> rcases hqab with haq | hbq
          · exact absurd (hap.symm.trans haq) hpq
          · change combM st.1 st.2.1 st.2.2 = _; rw [hap, hbq]
          · change combM st.1 st.2.1 st.2.2 = _; rw [hbp, haq, combM_comm]
          · exact absurd (hbp.symm.trans hbq) hpq
        exact finish_pair p q hce ⟨a1, b1, Or.inl hsc⟩
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hv
      by_cases hlen1 : (Nat.beq S.length (k + 1)) = true
      · simp only [hlen1, ↓reduceIte] at hv
        have hlen1_eq : S.length = k + 1 := Nat.eq_of_beq_eq_true hlen1
        set T' := T1.erase v
        have hScard : S.toFinset.card = k + 1 := by rw [List.toFinset_card_of_nodup hnd, hlen1_eq]
        have hsum : (S.toFinset \ T').card + T'.card = S.toFinset.card := by
          rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hT1_erase_sub]
        obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < (S.toFinset \ T').card)
        have hx0S : x0 ∈ S := List.mem_toFinset.mp (Finset.mem_sdiff.mp hx0).1
        have hx0T : x0 ∉ T' := (Finset.mem_sdiff.mp hx0).2
        rw [sufOrs_eq (sepM targetNat bits) S, sufList_head_tail] at hv
        dsimp only at hv
        set efn : ℕ → Bool := fun w => !(Nat.beq (foldLor (sepM targetNat bits) (S.erase w)) (fullM targetNat bits))
        have hte := tagEss_eq (sepM targetNat bits) (fullM targetNat bits) S 0 hnd
        simp only [Nat.zero_or] at hte
        rw [hte, Option.isSome_iff_exists] at hv
        obtain ⟨h2, hall2⟩ := hv
        have hpre0 : (0 : ℕ) = foldLor (sepM targetNat bits) [] := rfl
        rw [hpre0, show ([] : List (ℕ × ℕ)) = ([] : List ℕ).map (fun w => (w, sepM targetNat bits w)) from rfl] at hall2
        obtain ⟨U', a1, b1, hndU', hU'mem0, hsc⟩ := goDrop1_sound S [] h h2 hnd List.nodup_nil (by simp) hall2 x0 hx0S
        have hU'mem : ∀ z, z ∈ U' ↔ z ∈ S ∧ z ≠ x0 := fun z => by simpa using hU'mem0 z
        have hU'x : ∀ z ∈ U', z ∈ S.erase x0 := fun z hz => (mem_erase_of_nodup hnd).mpr ⟨((hU'mem z).mp hz).1, ((hU'mem z).mp hz).2⟩
        have hsubT : T1 ⊆ (v :: U').toFinset := by
          intro z hz; by_cases ez : z = v
          · simp [ez]
          · have hzT' : z ∈ T' := Finset.mem_erase.mpr ⟨ez, hz⟩
            exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((hU'mem z).mpr ⟨List.mem_toFinset.mp (hT1_erase_sub hzT'), fun h => hx0T (h ▸ hzT')⟩))
        have hUsub : (v :: U').toFinset ⊆ endSet inputs.toFinset (seq.take (m + 1)) := by
          intro z hz; apply hSv_sub; rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
          · simp
          · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ((hU'mem z).mp hz).1)
        have hU_lt : ∀ z ∈ v :: U', z < 65536 := fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hv_lt
          · exact hS_lt z ((hU'mem z).mp hz).1
        have hU_nz : ∀ z ∈ v :: U', z ≠ 0 ∧ z ≠ 65535 := fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ⟨hv0, hv65⟩
          · exact hS_nz z ((hU'mem z).mp hz).1
        have hU_nd : (v :: U').Nodup := List.nodup_cons.mpr ⟨fun h => hv_notS ((hU'mem v).mp h).1, hndU'⟩
        have hcU := monoCMD hsubT hT1_can
        have hcov : foldLor (sepM targetNat bits) U' ||| sepM targetNat bits v = fullM targetNat bits := by
          rw [Nat.lor_comm, ← foldLor_cons]; exact coveredM_sepM hM hcU bits hbits
        cases hex : efn x0
        · dsimp only [efn] at hex
          simp only [hex, Bool.false_eq_true, ↓reduceIte] at hsc
          have hge1 : Nat.ble 1 (countNonEss (S.map fun w => (w, sepM targetNat bits w, efn w))) = true :=
            Nat.ble_eq.mpr (countNonEss_ge_one (sepM targetNat bits) efn S x0 hx0S hex)
          dsimp only [efn] at hge1
          simp only [hge1, ↓reduceIte] at hsc
          have hvmem : (v, sepM targetNat bits v) ∈ (valsNew S).map (fun w => (w, sepM targetNat bits w)) := List.mem_map.mpr ⟨v, hnew, rfl⟩
          obtain ⟨a2, b2, hst⟩ := scanVsV8_sound _ a1 b1 hsc _ hvmem hcov
          exact stepUHintV8_sound hM hbits hnd hv_notS hU_lt hU_nz hU_nd hst seq (m + 1) hlenK hmin (by omega) hk1 hSv_sub hUsub hsubT hvT1
        · dsimp only [efn] at hex
          simp only [hex, ↓reduceIte] at hsc
          have hxab := ess_forces_input hM hbits hex hU'x ha hb hcU
          obtain ⟨z, hzS, hzx, hce⟩ : ∃ z, z ∈ S ∧ z ≠ x0 ∧ v = combM st.1 x0 z := by
            rcases hxab with hax | hbx
            · obtain ⟨hbS, hbx'⟩ := combM_new_other_mem hS_lt hx0S hb (by rw [← hax]; exact hnew)
              exact ⟨st.2.2, hbS, hbx', by change combM st.1 st.2.1 st.2.2 = _; rw [hax]⟩
            · obtain ⟨haS, hax'⟩ := combM_new_other_mem hS_lt hx0S ha (by rw [combM_comm, ← hbx]; exact hnew)
              exact ⟨st.2.1, haS, hax', by change combM st.1 st.2.1 st.2.2 = _; rw [hbx, combM_comm]⟩
          obtain ⟨u1, u2, hsp⟩ := scanTouchLoop_sound S a1 b1 hnd hx0S hsc z hzS hzx
          have hst : ∃ a2 b2, stepUHintV8 (fullM targetNat bits) k nextTree S v ((v, sepM targetNat bits v) :: U'.map fun w => (w, sepM targetNat bits w)) a2 = some b2 := by
            rcases hsp with hsp1 | hsp2
            · rw [hce] at hnew hcov ⊢; exact scanPairV_sound hsp1 hnew hcov
            · have hce2 : v = combM st.1 z x0 := by rw [hce, combM_comm]
              rw [hce2] at hnew hcov ⊢; exact scanPairV_sound hsp2 hnew hcov
          obtain ⟨a2, b2, hst'⟩ := hst
          exact stepUHintV8_sound hM hbits hnd hv_notS hU_lt hU_nz hU_nd hst' seq (m + 1) hlenK hmin (by omega) hk1 hSv_sub hUsub hsubT hvT1
      · simp only [hlen1, Bool.false_eq_true, ↓reduceIte, Option.isSome_iff_exists] at hv
        obtain ⟨h2, hall2⟩ := hv
        obtain ⟨U', hU', hu'⟩ := cutsSpec k S (T1.erase v) hT1_erase_sub hT1_erase_card
        have hU'sub_l : ∀ z ∈ U', z ∈ S := cuts_mem_sub S k U' hU'
        have hsubT : T1 ⊆ (v :: U').toFinset := by
          intro z hz; by_cases ez : z = v
          · simp [ez]
          · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hu' (Finset.mem_erase.mpr ⟨ez, hz⟩))))
        have hUsub : (v :: U').toFinset ⊆ endSet inputs.toFinset (seq.take (m + 1)) := by
          intro z hz; apply hSv_sub; rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
          · simp
          · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (hU'sub_l z hz))
        have hU_lt : ∀ z ∈ v :: U', z < 65536 := fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hv_lt
          · exact hS_lt z (hU'sub_l z hz)
        have hU_nz : ∀ z ∈ v :: U', z ≠ 0 ∧ z ≠ 65535 := fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ⟨hv0, hv65⟩
          · exact hS_nz z (hU'sub_l z hz)
        have hU_nd : (v :: U').Nodup := List.nodup_cons.mpr ⟨fun h => hv_notS (hU'sub_l v h), cuts_nodup S k U' hnd hU'⟩
        have hcU := monoCMD hsubT hT1_can
        have hUmem := cutsMP_spec (sepM targetNat bits) S k U' hU'
        obtain ⟨a1, b1, hUstep⟩ := scanCutsV8_sound _ h h2 hall2 _ hUmem
        have hvmem : (v, sepM targetNat bits v) ∈ (valsNew S).map (fun w => (w, sepM targetNat bits w)) :=
          List.mem_map.mpr ⟨v, hnew, rfl⟩
        have hcov : foldLor (sepM targetNat bits) U' ||| sepM targetNat bits v = fullM targetNat bits := by
          rw [Nat.lor_comm, ← foldLor_cons]; exact coveredM_sepM hM hcU bits hbits
        obtain ⟨a2, b2, hst⟩ := scanVsV8_sound _ a1 b1 hUstep _ hvmem hcov
        exact stepUHintV8_sound hM hbits hnd hv_notS hU_lt hU_nz hU_nd hst seq (m + 1) hlenK hmin (by omega) hk1 hSv_sub hUsub hsubT hvT1
  · simp [hvalid] at hv

def row1 : BinaryTree (ℕ × ℕ) := E
def row2 : BinaryTree (ℕ × ℕ) := E
def row3 : BinaryTree (ℕ × ℕ) := E
def row4 : BinaryTree (ℕ × ℕ) := E
def row5 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0x4444308822f2111f0f00,0xce635f888,0x444443bc0c2ffffff1f0,136,0x67781b4415d21103102f,0,13631488,0,218103808,1529,0xefff9f87b56bddfdf2300000,0,0xc3000d00000,193,893353197568,1529]
def row6_c0 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0x88884444300022f2111f0f00,0xf5f7fdaafd,0x2fffff21ee1eefd0f10f,34952,0x67781444152211e1102f0ef1,0x193c50f82f,0xc3011d3021f,0x2fcc49ece7df9,0xafffffee2cfde1,4038456,15,6333475,233964048,821915,917504,405410617,893118316001,0x17811f9c811f28,0x6fffffff22ffff1f10f,131727,917490,0xd2c962ad7ce324be14540c9e88,254,0x34b56aad5dbe497c2aa71754aa71cc,3825,0x3492056ad55abb7c9288554e3266370364,13762863,0x696ad55abb7c92f8558f925f0aa9c724,917504,0x696ad55abb7c768aa9c64be15538c9e,56105304064,0xb5b58ab5f0a2868b1cb5f0a286046de81,837232291568,136,0xd0000000000,391560,3577994088720,0x5ad6d62ad69353068b1cb5f0a284446de81,51539607552,0x2d6b6b156b484a50d16396be1450dbd036,0xb11b500000000,0x695da2ab556be7035925f0aaaaa06488a,0xaf5000000000000,0xac96aaad55a88c41ac9288564aa1064a8,0x60b000000000000,0x1034aed123ead55af9a835925f0aa06488a8,0x1067000000000000,0x2d6d7ced6a84468b1cb5f0948aa11be8,0x90000000000000,0x5adac0ad6a868bcb5f0948aa11b54588,0x3d44219200000d000000,0x7fa8c73de,0x33006fffffff3000000,0x49456ad5ac089d6496c08555035ea8,0xefff988774479f99ddfdeefcefd1,0x17e01b9f6353efcc49ece7df9a,0xafffffee2cfdf00e10,0xde0a4236db,0xdf202100000,0x3791536db,60129542144,0x6f054236f39,3311419785216,0x2023fc8059f9f38,893353197568,0x7777b0983867b08c4,0xd0000000000000,0x77777bc08fc99f2047b8,0xc3000000000,0x12f023f280823132047b8,0x1452000000000000,0x763fcfc80f7f0f39f3738,15,0xe739cdd8293a423,233964048,0x739ce791539b73,917504,0x739ce782a74847672e,0x6ffffffdddde1fce0efeee2,0x34b258ab5f38c92f85150327948940c9e88,14745600,0x886964b156be71925f0a2a064f6464649e888,14,0x4434b258ab5f38c92f85150327b232324f2912818,983040,0xd2d5aab576f925f0aa9c5d52a9c7324f295271,225,0x6634b56aad5dbe497c2aa71754aa71ccccccccc,234946560,0x1e8f434b258ab5f38c92f851502d21f9f9c9ec8c8c8,15,0xf29e696ad55abb7c92f8554e2d29f9f9baa5538e65,15728400,0x869240ad5aab576f92510aa9c64cc6e06c92094a938d,225,0x4634923056ad55abb7c9288554e3266370364ccccccc,18939679,0xd2c962ad7ce324be14540c95a393224f2912818,225,0x221a592c55af9c6497c28a8192b4726449ec8c8c8c,15,0xc696ad55abb7c92f8554e32568eb1dd52a9c73324,3825,0x1a49102b56aad5dbe49442aa719289d63c998dc0d9224,901944045599,0x21a5ab556aedf24be1563e497c2aa71c924f295271c8,225,0xcc696ad55abb7c92f854f925f0aa9c724ccccccc,3600,0x7bcd2d5aab576f925f0ab1f24be15538e48d29f9c3f3,529,0xd2d5aab576f925f0ab1f24be15538e495a3ac7,60129538015,0xcc696ad55abb7c768aa9c64be15538e6666649e,3600,0xbde696ad55abb7c768aa9c64be15538b4a7e75f9c9e8,0xd1022fffff10f,0x16b6b156be1450d16396be145088dbca4486de811,225,0xf6b6b156be1450d16396be1450c08d9f1f1f1f2de817,4129,0x8b5b58ab5f0a2868b1cb5f0a286046d5a3930606de81,0xc2eefcefd0eefe,0xbed5aa7aeef17c2aa77ccccc8f295271c]
def row6_c1 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0xf0008f8844f422f2111f0f0000f0,0x8be4023efb56a9ebbbc5f0aa9dfd4e1c3cccccc,34668319,0x5f6ad53d777c8be1553bc5f3ac7c8f2952718,225,0x5f6ad53d7778be1553bc5f3ac7cccccccc,3600,0x2f9008f8bed5aa7aeef917c2aa778be758f9ea70e1c3,18704582570255,1141186310,917504,0xb5b5aab5771c1a2c72d7c2aa7711b794a93888df6ad53d777cb576f917c2aa77718f29527171,225,0x5adad55abb88d16396be1553b88e666665f6ad53d777b576f917c2aa7771cccccc,3600,0x5f2011e25adad55abb8e0d16396be1553b88da9c31188efb56a9ebbbe5abb7c8be1553bb8fa9c311c3,529,0xb5b5aab5771c1a2c72d7c2aa7711b568eb1f06fb56a9ebbbe5abb7c8be1553bb8c5f3ac7c7,0xc3000cffff1eefe,0x182e23886,0xd0000000000000,3207532294,0x340ff30000e0000,0x161b5adac55ad26a60d16396be1450888dbca4486046de811,225,0x167b5adac55ad26a60d16396be1450888d9f1f1f1f2de817,4129,0xb5ad6d62ad69353068b1cb5f0a284446d5a3932de81,0xbffffffffefdf,0xb3dad6d62ad69094a1a2c72d7c28a1b3e3e3e3e5bd02f6,0x1105000000000000,0x94991234b258a92b476be719125f0a2a4940c9ecc8c8c8,15,0xaa934b56aaad3b576f8f25f0aaaa4e2ea9555271cc,3585,0x1567fa46964b152568ed7ce3224be14549281690dcfcfcc80f,15,0x39c2b25153ab9da88c4c7494428a74841c10ac9d2105b,225,0x39a490e62b56a9d5ced5dbe3a4a21553a4e326636e503648,13762863,0x55634b56aaad3b576f8f25f0ab2b1f24be155549c724,917504,0x1552696ad555a76aedf1dda2aaa938c97c2aaa938c9e,219283456,0x39c2b25153ab9da88c4c734a2714e6239288514e9082e4,917504,0x39c2b25153ab9da88c4c76510ad3a420c94428a74841690e,55885103104,0x4925adac5495a3b5f0a2a243458e0daf85152486046de881,837233209072,0xaacaabed5aaab4debbbe3e45f0aaaa4ef1e52a55271,225,0x5556665f6ad555a6f5dddf22f85555277cccccc,3600,0x5f2011f55957dab55569bd777c7c8be155549dfd4dce1c38,529,0x2ab2aafb56aaad37aeef8f917c2aaa93bc5f3aca7c,285409294,0x15596b6b55569dabb8e0e0d163836be155549dc46ab2afb56aaad37aeef8f96aedf1e2f8555527771,0xc2feefceef0,0x738573454eae62511894e7ea21453a4209e1291274841,225,0x1ce734cbb21c2b9a2a75731288c4a73f510a29d21048166011f9ec8,3600,0xe70ae68a9d5cc4a2094e7ea21453a4208db6db,529,0xe70ae68a9d5cc4a23129cfd4428a748413d44e31c23,285409294,0x1ceb5b5153ab9da8b129cc68b1c1b510a29d21041170ae68a9d5cc4a23129ced446263bd4428a74841041,4471060955136,0x92d25ad6d62a4ad1dad26a6283458e0daf85152484446de881,51539607552,0x92d25ad6d62a4ad1dad21294a4868b1c1b5f0a2a490dbd10368,0xb00afeee2eefceef0,0x1a5768aad55af9c0d6497c2aaaa8193ca4a06488a,3825,0x179a5768aad55af9c0d6497c2aaaa81695d3f3f39222a080f,529,0x14d2bb4556aad7ce06b24be1555540c95a3a92b22488a,0xaf4ffffffffffffeefe,0xac96aaad55a88c41ac9288564aa106412965521064a88,3825,0x31592d555aab511883592510ac95420b6db72543,529,0x1592d555aab511883592510ac95420c944e24ac124a88,0x600fffffffffffffdef,0xf34b251155aab5f3532b24be1555540b4874fcfce4922a080f,0xa0000000000000000,0x5cff40d2bb448fab556be6a0d6497c2a81695d3f3f39222a080f88,0x1066fffffffffffff10f,0x5adaf9dad5088d16396be129154236f29115211be88,225,0x63dadaf9dad5088d16396be1291542367c1c7c7cbe87,3600,0xeb5b5f3b5aa111a2c72d7c2522a845ce6e6e6e77d0e,529,0x2d6d7ced6a84468b1cb5f0948aa11b568d4ac1be88,37529709641742,0x252b5b5f3b5aa1195931a2c72d7c2522aa5211be8,0x8fffffddddeefceef0,0xb5b5815ad50d1796be129154236f29115211b5445888,3825,0x4b5b5815ad50d1796be12915423611d31188ed516204,529,0x5adac0ad6a868bcb5f0948aa11b568d4cac1b5445888,37529709641742,0x2aad6d6056b555698d17836be1291555211b54588,0x21920000000000d00000,0x4a53549c96626937d4dab549cab4d2f5dd38f8f917c24a9555277,0xb0000afff300000,0x425054564b554a55aaacb5118820d64944212964aa106a4a8,0x1672000000000000,0x2e8f696ad2daf9c5ad556088d162396be1345148aa11be88,0x90000000000000,0x5a1ed2d5a5b581465ad5560d16396be1345148aa11b5445888,0x3d43ffffddfdea2deefcfde1,0x3bfd462e7373767bce,23236276584991,0x252ff524d8cb3de,0x33006ffffffdddde1fceef0,0x152515ab56b02275925b0215540c9604a54a06bdea88]
def row6 : BinaryTree (ℕ × ℕ) := N 0xf0008f8844f422f2111f0f00000f 0x8be4023efb56a9ebbbe45f0aa9dfd4e1c38f2952718 row6_c0 row6_c1
def row7_c0 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0x88884444300022f211110f00000f,0x7afbfed857ed8,0x677844441443ff30000e000000e1,0xb67a51fafcfefc1e8393ca0f173c18f,0xcffff1ffffff1f,0x64f143e08bc18f,60129542130,0x101d20bfa582efc16fcce416f53328740bdb9c386ffd988,254,0xe9c3c98210e960a97a9c7c82a54a93ba025b9bb86d29a93be65,986625,0x8080163ddd2c15d05163b20a251d287c128e7516d89b6db6802743,14745600,0x163fa582a5ea71d9054a8e93be52a3a4ddcb4b6db6ef4b8,901962989568,0xe9c3d0474b054bd4e3e4153958f9054a95277cca025b9bb870d0,60129542144,0x1d3827d0474b054bd4e3e3a94d49de0a952a4ee8096e6eeb8702610,0xd1200000000,0x8080173fa582ba0a2c762051373878289474a1de589b6db6802743,60129542144,0x40400b1eee960ae828b1d9944a39d5e0a251d287626db6d01c802743,0xd03d300000000,0x70c8b9fd2c177ddbd80fcc9ebe3e416f5332777740bdb9d6ee1c17e5e208f,0xc22fffffff1f10f,0x2fcc49ece7df988,0xcfee2cfdef00e1,0xbfd98bfd2f65488,19597971361296,0xb1fd2c15d9a251d27af8ec8289474ae5dd89b6dbce3a2f138,0x40d000000000000,0x238645cfe960bbec18f9301ea49ebe3e416f5332740bdb9d6ee1c17e5e1ffa08f,0xb10450c2ffffff1f0,0x2c3fffeffdd7d47fb2ffb7bc8927ff6f525e94bc25272b259595961afe659c0,0xa4dddde1fcfdf00e10,0x9030ac14596a209905129050838252c8416da0db6db688443,14745600,0x61220fe1a6d54e5aa5f20a952a9c5fa546e06bf6836db6f2838,0xe00012f0000,0x120615828b2d441332894b420c144a41420b41b6db699688443,0xcfff1f1fde0f10f,0x3d19f3888,983040,0x11829091988,0xe0002020000,0x322a719cb88,0xcff1fffdef0000,0x17811f98c811f2888,0xb0015021111021f0ef1,0x8c2afe894ab596a208359051295fd5082d06db6dfc3338,0x6fff4ffdd2deeeeeeeff101,0x18c1a592c55af9c6495a393224f291281349e88,15728654,0x6696ad55abb7c92b4758eea954e31249e52a4e26893c6,250675200,0x1a490615ab556aedf24a2758f26637031248252a4e268a6,962091614208,0x1a5ab556aedf24be1563e495a3ac793ca549c620d127b0c6,0xd103100000000,0x5adac55af85143458e5ab4726440dbca4484d16f409ac6,0x1104000000000000,0x2d6b6b156b49a983458e5ab47265bca44a2044d16f40d8c6,0xb11c1000000000000,0x34aed155aab5f381ac92b471256449e52502689220d06,0xaf50000000000000000,0x2b25aaab556a23106b24a271256092094b2a90826892a20c6,0x1671ff500000000e00e1,0x3fdadacfb95931a2ed67c4a4fca42367c7c363e3e6bee0d7d0e6,0xaffffffff1ff1f,0x2d6d7ced6a84468b1cb568d4ac1b79488a9089a2fa20c6,0x900000000000000000,0x5adac0ad6a868bcb568d4cac1b79488a9089a2d5116220c6,0x3d44219200000d0000000000,0x7fa8c633de888,0x33006fffffff30000000000,0x928ad5ab58113ac928c827591258129528134534f5490630,0xefff988774479369cc2aecddeefdfff2,0x38407482f80e905fd2c177e0b7e6720b7a99943a05edce1c383ca665030ffd988,14745600,0x70f40748337f4e1e8330874b05df82df99c82dea6650e817b73870e04e339f9190ffd9888,14,0x1c3d01d20cdfd387a0cc21d2c177e0b7e6720b7a99943a05edce1c38138ce7e46441e53328188,983040,0x1c3d01d13027a70f260843a582a5ea71f20a952a4ee8096e6ee1b4a6a4ef99604a952718,225,0xe0874e18983310e9c3c983210e960a97a9c7c82a54a93ba025b9bb86d29a93be65cccccccc,64659455775,0x203a40e140400b1eee960ae828b1d905128e943e09473a8b6c4db6db804a3a502802743,225,0x74e1e81d97ef2101002c7b980fe960ae828b1d905128e943e09473a8b6c4db6db8138ce7e46568027438,966367641375,0x407481200002c7f4b054bd4e3b20a951d277ca54749bb9696db6dc0951d271aef4b88,225,0x3a70c83333100000163f3a582a5ea71d9054a8e93be52a3a4ddcb4b6db6f3333332f4b8,1241245548319,0x380c9e287c101d20bef80e9074b05df82df99c82dea6650efedf9ce205edce1c3870794cca0622f,225,0x70e9c3d0663c84074833d2c177e0b7e6720b7a99943bfb7e738817b73870e1c09c673f232322f,15,0x3874e1e4c11e4203a260ce960a97a9c7c82a54a93bbfa9a7c404b73770e1b4a6a4ef9999a9,986625,0x8080163dd01d2073e960ae828b1d905128e943bfa2767304a39d45b79626db6db680274362,14745600,0x2c7c07483a582a5ea71d9054a8e93bbfa973e652a3a4ddcc65a5b6db6dde97109,0xd2000dff0ff10f,0xe101d208f27a70f411d2c152f538f9054e563e4152a549df328096e6ee1c3812a549c72210,225,0x70e9c320cc410e9c3d06474b054bd4e3e4153958f054a95277cca025b9bb870f333333310,34672144,0x7080e9074e1e823a582a5ea71f20a9cac7c82a54a93be3fa9a7c404b73770e1c3f250,0xdfffffdeef1f0,0x1c3a704e4198821d3827d06474b054bd4e3e3a94d49de0a952a4ee8096e6eeb87999999902610,0xd11ffffffffff1f,0x4074820501002e7f4b05741458ec40a26e70f05128e943bcb136db6e0128e940b86802743,225,0x3a70f4197ef2101002e7e7a582ba0a2c762051373878289474a1de589b6db702719cfc8c8c68027438,34672144,0x80e9040400b9fd2c15d05163b10289b9c3c144a3a50edfd13b38c4db6db624013a1b,0xdfffffdeef1f0,0x3a70f40ecbf7908080163dcc07f4b05741458ecca251ceaf05128e943b136db702719cfcb918d01d08027438,0x303000000000000,0xe160b67a51fafcfefc1d387a0cc790393ca0f40c00ff870c0c8b9fd2c177e0b7e672d6fcc16f533287c8a05edce1811ee1c09c673f32322f8,15,0xe0fd38793047907007e09e0e3d2c152f538f96a9782a54a93bb8a025b9bb770da53527771cca97,986625,0x240400b1ee001387073ba582ba0a2c765a88e8289474a1c41c128e751105b626db6236d004e811884,14745600,0x380000b1e00fc3839f4b054bd4e3b2d52e82a54749ddc72951d26d8dcb4b6db76dde96f097,901962989568,0x707e9c3d04003f0e0f9d2c152f538f96a9782a72b1f1f20a952a4eee399404b7376ee1c3f20e97,60129542144,0x1c1fa704fa08007e09e0e3d2c152f538f96a977529a93bb8c152a549ddc5012dcddbbae1c098f20e97,0xd1200000000,0x901002e78009c383ba582ba0a2c765a88e40a26e70e238289474a1c4179626db6236d004e811884,60129542144,0x12020058f70009c3839dd2c15d05163b2d44765128e7571060a251d28710589b6d88da039004e811884,0xd00cff1fffde0f10f,0x1c203a660bc038645cfe960bbeedec07e64f5f1f20b7a9993bbba05edceb770e0f29990c417e5e208f,34672369,0x7080e9981c038645cfe960bbeedec07e64f5f1f20b7a9993bbbbfb7e5f2f8817b73addc38705f978be08f,0xc22fffffff1efdef10f,0x17e01b9f6353fd7e624f673efcd4141e68,60129542144,0x302c2cfe018101617e68030002c2fb57fa9b54ba76a9cce60daa54a90823be66566666592a5484171c80b6162d6f623b57cce38dadea664208ef64e563e3e5bca44841717,235929825,0xc0e9c1eceff6107c4c1cc00c00042c2f42d5fea6d52e9daa7339836a952a4208ef611b9e311e665666666006040601ba5b575adedced5f1d8c6d44a3a4208eec4db6dbb271f1e3e3c9a02d858b5bd88ed5f338e36b7a9990823bd84dcdd88ec9cac7c7c7,34668319,0x302fcc49ece7df900c080b0bf2018101617e602d858b5bd88ed5f338e36b7a9990823bdadf911be5bca44841718,225,0x302c2cfe018001617dabfd4daa5d3b54e67306d52a548411ded534237ccccaccccccc00c080b0bf35016c2c5adec476af99c71b5bd4cc8411ded6fc88df2c9cac7c7c7c,18704583491359,0x60006040585f900c080b0bf3016c2c5adec476af99c71a236b7a9990823b88dbca448417111,225,0x1803803e3e2018001617dabfd4daa5d3b54e6730688daa54a90823b88e665666666006040585f9a80b6162d6f623b57cce38d11b5bd4cc8411dc46c9cac7cc7c,4129,0xc000c080b0bf2018101617e602d858b5bd88ed5f338e3446d6f53321047711b5bf2237c1,0xcfffffeefcfde0eefe,0x203a4020000163fa582bb344a3a4f5f1d905128e95cbbb136db7009474a8b8bce3a22f1388,225,0xe9c1e07bfd98410bfcfc00002c79ba582bb344a3a4f5f1d905128e95cbbb136db6e9c7c7c79c7467222f138,34672144,0x80e9000000b1fd2c15d9a251d27af8ec8289474ae5ddfd13a32f8c4db6db79c7440af1388,0xb14520c2fffffefdef10f,0x2c3fec1fe59b0ffffbff75f51fecbfedef2249ffdbd494a5e12939592cacacffbd49786ac35fccb32c0]
def row7_c1 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0xf0008888444f44442f22111f111100f0,0x587fd83ffa561ffff7feebea3fd97fdbde4493ffb7a92f4a5e13fedf2f4af749cac96565656586bf996659c0,18704583491584,0x499e81803f603f7d87fffdffbafa8ff65ff6f79124ed6fc8cbfedea4bd29784bc6939592cac8cacb0d7f39966519c08,0xa4dddde1fcececfde0ff1f,0x483420be240c2b05165a88264144a41420e094b2105b6836db6e012904841688443,225,0x12cfe9be6824f28420240cc078ac14596a209905129050838252c8416da0db6db81399c832b6884438,966367641375,0x48942198be61220fe1a6d54e5aa5f20a952a9c5fa546e06bf6836db6e04a95271af28388,225,0x1874c3643c32061220fe1e26d54e5aa5f20a952a9c5fa546e06bf6836db6f33333332838,1241246535184,0x240c241b15828b2d441320a2520a1060a27f826094b2105b6fda0db6db6d0868844365f,14745600,0x24309107f0d28434daa9cb54be4152a5538c15358efd2a37035fc3f6836db6db36507105f,0xe00000dff0ff1f0,0x12cfe9be6829e50840481980f15828b2d441332894b420c144a41420b41b6db81399cb906369986884438,0xcfff1f1fdefffffff1f,0x1b71829090db667988,0xdfff0f1f00000,0x8211941c43f41fc6507102afe8b04a23129fd1299a104ca0db86fd391918df894cc84188,2272273629184,0xf20867ce2232838884055fd1609446253fa253342099a2ce08f2836e1c37e2533210623283888,225,0xfd07f08650710840abfa2c1288c4a7f44a6684133459c11e506dc386fd39191918f28388,0xdf1ffffffffff1f,0x36f22a6dc3ce5b8668,0x311000000000000,0x4047fa08402cfcf9c40b9f06,60129542144,0x904102fe5071024056d4596a23128688e5a89482841045a0db6dd84a412104458abfa2c1288c4ab5104c7f44a66841041ca0db70df894cc841106328388,225,0x7e8e6b3f41fc3a086507024056d4596a23128688e5a89482841045a0db6dd93918f8f8c55fd1609446255a88263fa2533420820e506db86fd3918f918f2838,34672144,0x482024056d4596a23128688e5a89482841046d44ff0462d06db6db157f45825118956a2098fe894cd0820839a2ce08c4ca0db70e1a05fca0e2328388,0xcffff1fdeef10f,0x3bbbd84c1c710cf6118823886,0xd00000000000000000,0xeeeef7811f97833e408f710f06,0xc30000000000000,0x97811f9121010462099023dc40906,0x1451f300000e000f0ef1,0x27206138ce15828b1d5d6a2098e82894829d210704a593a420b6d06db6db66334421d0cc60e,14745600,0x90c1d220fe1a5c6734daa9c754daa5f1d054a954e938bf4a8db940d7ed06db6db70636506e1c60e,0xe00012f0000,0x9c8184e338560a2c7575a88263b2894b4e908305129053a420b41b6db6ccd32e334421d0cc60e,0xcfff1f1fde0f10f,0x763fd0fc80f7f0f39f3738cc660d9,983040,0x7439ce6ec149d2121cecc3a0ce,60128559104,0xc042c0d610f3941b9c66300c2afe8b2c2c094462539bfa25335990826506db9c37e25332cc8418ffb56b2c2c7fdf3aa93ffbe52ab32813283737387ff0a54b32818,225,0x7fff7603f41f8fe4587f9bfed54e3fd97fd4baa93ffa952aa52f08e73739373cccccccccb0879ca0dce300c2afe8b2c2c094462539bfa25335990826506db9c37e9cc8c8c71ff6ad65858ffbe75527ff7ca55665026506e6e70e93995958e,0xdf20210ff1f,0x39ce73c8a9cdb9d19cb9c3a1c6,0xb0000aff2fff20dfdef0000,0x483317c46157f44a55acb51041ac82894afea8416836db70094b2a9082dfc433388,34672369,0x120c46157f44a55acb51041ac82894afea841828a1fd608d06db6db7f10cc5f3388,0x6fff4ffdd2deeeeefd0eefdf101,0x106318419a592c55af9c6495a393224f6464649e5225026893d1106,64439255054,0xc3619a5ab556aedf24ad1d63baa5538c4999999992794a9389a0c693c6,0xe0100000000,0x3d06f420d2c962ad7ce324ad1c990d21f9f9c9ec8c8c893ca44a04d1e83190,983040,0xf194f20d2d5aab576f92568eb1da53f3f3754aa71892c9e52a4e268f1a4f1a10,0xeffff10000,0x1186692461856ad55abb7c9289d63c998dc0c4999999992094a9389a2e18c6,0xdff1000000000,0x1032066964b156be71925f0a2a05a4341f9c9ec3646449e522503e86922066964b156be71925f0a2a05a4341f9c9ec3646449e522503e86964a047d5af9c6559f7c28a023c5a4341f9c9ec3646011f567f9489011e3e8,2272037699584,0x8319a592c55af9c6497c28a8192b4726449ec8c8c8c93ca44a0621a592c55af9c6497c28a8192b4726449ec36464649e5225031066964b156be71925f0a2a064b647b93224f61b232324f291281886964a147d5af9c6494acf1051f5032568e4c893d86c8c8c93ca44a0428f8,235929825,0x69220640cd2c962ad7ce324be14540c96c8f7264348683f3f393d86c8c8c840cd2c9408fab5f38cab3ef85140478d59f5a3a03f008f690d07e7e727b0d91918047b4b250a3ead7ce324a5678828fa8192b47264348683f3f393d86c8c8c8,0xd1fffff1efff1f,0x186c696ad55abb7c92f854f92568eb1f3333324f2952718834649ecc318c6,235929600,0x790f34b56aad5dbe497c2ac7c92b4758ed29f9c3f393ca549c620d1e93d90640c6,0xd1030fffff1f00000,0x39ad6d62ad7c28a1a2c72d5a3932206cf8f8f8f96f29121343dbd0e2631ac6,0xc2eeeefdef00000000,0x835f2011e6bed5aa7aeef17ceb1f3d4e1c3cccccc8f295271344618c6,0x1111021100000000,0x18d6b6b556aee23458e5ab4758f839999996f295271113465f6ad53d777b576f917ceb1f1f3333323ca549c5c4d186318c6,235929600,0x5f2011e2206b5b5aab5771c1a2c72d5a3ac7c1b53862311dbca549c444d025f6ad53d777cb576f917ceb1f1fd4e188e1c794a938b89a20c818c6,0x1040fffffffff1f00000,0x59cd6b5b58ab5a4d4c1a2c72d5a3932cf8f8f8f96f29128811343dbd0e36318c6,0x11110000000000000000,0x949913e691a592c5495a3b5f38c892b472649127b3232324f291292502688830393cc630,983040,0x51aa4d2d5aaab4ed5dbe3c95a3aca7754aaa938c492794a9549c4d061278c630,234946560,0x2acff21234b258a92b476be71912568e4c921a4373f3f393ca44a49409a3c4079820630,983040,0x720e15928a9d5ced446263a4a2726384c10ac9d2107cd2412912748413418348720630,14745600,0x734920ce62b56a9d5ced5dbe3a4a2758e79331b7281892412952749c4d160c0c630,59877883904,0x918618c1a592c518568ed7ce3224be1454928193d986c8c93ca44a4940c18c3fed5aa9593b576f92ffb3e2aa949c733333333fe7d4a94a4e38d2c9628c2b476be719125f0a2a4940c9ecc364649e522524a060cd2c9428fa30ad1daf9c64494acf1051f524a064f661b23242b3d489492818,235929600,0x5f40c1a592c518568ed7ce3224be14549281690dcd07e727948949281f18bed2c9408fa2fd68ed7ce322acfbe145559f2023c5a437341f9d59fe5225567c808f1f19a592851f4615a3b5f38c892959e20a3ea4940b486e666407b90acf522524a0480f,225,0x7f7183491cec40c61ff6ad54ac9dabb7c97fd9f1554a4e2e73937373ccccccccc6964b14615a3b5f38c892f851524a05a437341f9c9ecc3646418c5f6964a047d17eb476be7191567df0a2aacf9011e2d21b9a0fce4f661b23008f319a592851f4615a3b5f38c892959e20a3ea4940b486e666407b93d986c8c8,901977800479,0x2ab1a5ab55569dabb7c792f855958f92568eb29e4f2952a938c41a324f618c0c606,0xd2000000000,0xe70ac9454eae76a23131cd289c53988e4a2726384904a449d2107d06868e1c81820606,0xd031100000000,0x12496b6b152568ed7c28a890d163836ad1c992440dbca44a4909a2de8813185a0c606,0xc2eeeeefdf0000,0x61aaab332b2fb56aaad37aeeef917ceb29f33333323ca54aa4e268c3618c6,235929600,0x5f2011e6aacaabed5aaab4debbbe3e45f3aca7cf5373870e3ca54aa4e26888318c6,18764746784768,0x5565adad555a76aee38383458e0dab47594f836f2952a938889a2ab2aafb56aaad37aeef8f96aedf1e2f9d653e3c794a9549c5c4d0630318c0c6,0xc2feeeeefdf0000,0x1ce734cbb21c838573454eae62511894e7ea2718e11c0b3008fcf6784a449d21050f7a0ce40c6,235929600,0xe41c2b9a2a757312882539fa89c63846db6dbf094893a420a1e6640c6,18764746784768,0x39d6b6a2a7573b51625398d163836a27263846361291274841113438573454eae62511894e76a23131dea2718e1189e12912748411050f2060640c0c6,0x411000000000000,0x24b496b5b58a92b476b49a98a0d163836ad1c9925bca44a4944089a2de881b418c0c606,0xb00afeeeeeeeefdef0000,0x2f20d2bb4556aad7ce06b24ad1c49590d2ba7e7e727949409a3d2444101e640d068,0xaf500000000000000000000,0xd01592d555aab511883592513892b046db6e41296552104d0e4a886640c6,0x60100000000000000000000,0x7906964a22ab556be6a656495a3c8690e9f9f9c9e5222a50268f49244101f241820630,0x1070ff500000000df1f00000,0x12d7cce6067fb5b59f72b26345dacf8949f94846cf8f86c7c7cb4fa913f2908bebee0d17d0f06,235929825,0x3fb9fdc673bfdadacfb95931a2ed67c4a4fca422e73937373b3e3e1b1f1f1dafb866be87398c6,34668544,0x25af99dfed6d67dcac98d176b3e2527e5211b5406a486cf8f86c7c7c7cd7dc41afa21cc0c6,0xaffffffff1efdeff1f,0x31cd6b6be76b54223458e5ab46a560d9f071f1f2de5222a422687be878318c6,235929600,0x390b5b5f3b5aa111a2c72d5a352b05ce6e6e6e76f29115211343afa1d0640c6,0x2222111102110000,0x94ad6d7ced6a846564c68b1cb568d4ac90dbca4454a5211345f441818c0c6,0x8fffffddddeeeefdef0000,0x2216b6b02b5aa1a2f2d5a3532b06c23a62311dbca4454844d025aa22c4090640c6,0x2222111102110000,0x555adac0ad6aaad31a2f06d5a3532b286de5222a55211345aa22c441818c0c6,0x21920000000000d000000000,0x1294d52725989a4d26fa9b56a939569a5ebba71f1f22f9a6b29f23ca254a9549c4d064a064a06,0xb0000afff3000000000,0x1094151592d552956aab2d44620835925131449582482504a59548413454951062f98be6,0x1671ff500000000e00e1,0x9f7f9f90da9a9f6d67dcfcac9c868b1b59f12028a4fca42367c4e3e1b1f1f35fd7debf0643d7de8740d06179a00f,0xaffffffff1ff1f,0xba3da5ab4b6be716b55582234588e5ab46d14ac1b79468a4454844d17d11062f98be6,0x900000000000000000,0x1687b4b5696d605196b55583458e5ab46d14cac1b79468a4454844d16a888b111062f98be6,0x3d43ffffddfdea2deeeefdef0000,0x39dfea31739b9ba1d9ef3a21c68,0x15221e1102110000,0x252ff524d8ca259ef44a2506]
def row7 : BinaryTree (ℕ × ℕ) := N 0xf0008888444f44442f22111f0f0000f0 0x1fffdd803ee7587fbbfeffdd7d47fb2ffb7bc8927ff6f525e94bc239cdce4dce939592cacac7586bf993b26c0c0 row7_c0 row7_c1
def row8 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0xf000888844442222111f0f0000f00001,0xbe60fe3fd382068000b0c07fbd2c96b7e77ea028fe5919f1f6e683f38139c30d9191be80ff3e8,983279,0x74e9d104f4e0819041fef4a9b54befd4a952719f1f6e683f3694d49c732e6670c36666409e06c8,0xf00e010000,0xc0004300d0819fef4a9b54bb7ea54749c72951d281b963edb41b7999c30d9997a0d0f670c68,0xd2012f00000000,0x61d0c003a7040cff7a54daa5e0a9cac7cdfa952a4e3999f1f6e68387e7999c30d9998008409e06c8,0xe000000000000,0xe9d3a250e9c1033fde9536a977529a938efd4a952719f1f6e683afcf333861b33204c208409e06c8,0xcfff11fde0f10eff11,0x101d2035f81d2c177e0b7e671fdbf39c40bdb9c3870794cca04d0ffd988,15728654,0x74e1e4c10643a582a5ea71f1fd4d3e2025b9bb86d29a93bc66c0952a4e268881268,64659456000,0x101002c7b8dd2c15d05163b1fd13b398251cea319626db6dc0251d281342009d0d01c6,966367641600,0xb1e6e960a97a9c763fa973e652a3a4dc65a5b6db70254749c4d15de97106,0xe0012100000000,0x3a70f411d2c152f538f9054e563e3fa9a7c404b73770e1c0952a4e3106887e9c83206,0xd20000000000000,0x40400b9fd2c15d05163b10289b9c3bfa2767189b6db804a3a503106879719004e866,0xd03e1000000000000,0x70c8b9fd2c177ddbd80fcc9ebe3e3fb7e632f8817b73addc383ca664268882fcc1a08f83c6,0xcf2ee1efdeef1f00000,0x17fb3117fa5ef6548888,0x11e102110e100000,0x58fe960aecd128e93d7c763fa27465f189b6db804a3a545c4d0f38e8835e27106,0xb14520c2ffffff1f00000,0x2c3fffeffdd7d47fb2ffb7bc8927ff6fcfa57ba4e564b2b2b3fef525e143d561afe7323607a506,0xa4dddde1eefdfe0e100000,0x90318560a2cb5104c8289fe098252c84187ed06db6dc025209083c206884436906,966367641600,0x184883f8664daa9cb54be415358efd2a37030fda0db6db812a549c78415e507106,0xb0022d21111012100000000,0x11855fd12956b2d44106b20a287f582341b6db804a5954841e1037f10cc67106,0x7001671ff4ffffffffff1f00000,0x3fdadacfb95931a2ed501a921b3e3e1b1f1f2d3ea44fca4223f3efafb8345f43c18c6,0xefff9887b4bbbbbbccdaecddefdeff1efff2,0xffd07d0e062f983f8ff4e081a0002c300be60fe3fd382068000b0c07fbd2c96b7e77ea028fe5919f1f6e683f38139c30d9191be80a3f9647d1be80ff3e8,64439255054,0x1d3a20817cc1fc7d3d382068000e06b0c0e9d3a209e9c1032083fde9536a97dfa952a4e33e3edcd07e6d29a938e65ccce186ccccdf4a95271f409e06c8,0xf00e0100000000,0xc02f983f8ff4e108190420000c6b0c000c0004300d0819fef4a9b54bb7ea54749c72951d281b963edb41b7999c30d999be951d271af2f41a1ef670c688,81346268269379584,0x7fe8b67a51fafcfefc1e82f983f8ff4e08187d0393ca0f8000e06173c18fb0c02f983f8ff4e0819fef4b25adf9dfa80a3f96477ea03fccf8fb7341f9f9c09ce186c8c8c8df4051fcb231e88000b0c0,983265,0x1d3a74e9d104f4e0819041040be60fe3e9e9c10363fde9536a97dfa952a4e3bf534f3e3edcd07e7e6d29a938e6666e6670c36666664000703409e06cc8b0c0,0xf00e010000,0x1800180008601a10317cc1fc7fa70840cff7a54daa5dbf52a3a4e3bf52e7ca5474a06e632c7db6836dbccce186ccccc410bd0687bd000063670c688b0c0,0xd2000dff0ff1efff1f,0x61d0be60fe3fd3820680042000381ac3030c3a180074e0819fef4a9b54bc153958f9bf52a549c7333e3edcd070fcf333861b33337d2a549c723d8008409e06c8,2272273629409,0x18742f983f8ff4e0818c3a180074e0819fef4a9b54bc153958f9bf52a549c737ea69e7c7db9a0e1f9f9e6670c366666002100000087035860409e06cc8,0xcfff1ffde0efdef10eff11,0x387a03a41935e6c0e9c3d0660c874b05df82df99c7f6fce7102f6e70e1c09c673f23220f2999409a21ffb31106,64439255054,0x3821d386260cc321d38793064190e960a97a9c7c7f534f88096e6ee1b4a6a4ef19b999999990254a9389a20c681268,0xf0e0100000000,0x74e1e81d966f7908080163dcc079ba582ba0a2c763fa2767304a39d4632c4db6db8138ce7e4657009474a04d10802743831901c68,0xe1000000000000,0xe9c320ccc362000002c7e1ba582a5ea71d8fea5cf994a8e93719696db6de66666640951d271345797a5c418c6,0xe0121000000000000,0x70e9c3d0663a704386042082101d386074b05df82df99c82dea6650efedf9ce205edce1c38702719cfc8c8c883ca66503111d2f0bbf05bf33905bd4cca1dfdbf39c40006e70e1c38139619191910794cca062200003821c3023a5e177e0b7e6720b7a99943bfb7e73880837333870e04e5864646441e5332818880080bc2efc16fcce416f5332063ddfdbf39c40006e70e1c38139619191910794cca0418f88,0xd20000000000000000,0xe1d38641986410e9c3d06474b054bd4e3e4153958efea69f1012dcddc38799999990254a938c41a231fa7230c818c6,0xd200000000000000000,0x74e1e832cdef20e02005cfcf4b05741458ec40a26e70efe89d9c626db6e04e339f91918e0128e940c41a1c65d064013a1c18c6,0x3110000000000000000,0x1c2c16cf4a3f5f9fdf83a70f4198f4190393ca0f40c00ff870c0c8b9fd2c177e0b7e672d6fcbfb7e739940bdb9c3023dc38138ce7e646441e533281c89a22302f8063cc6c0,983040,0xe0fd38793041bc83803f04f071e960a97a9c7cb54bbfa9a7c7404b7376ee1b4a6a4eee319b0254a938b89a23012f024d06c0,64659456000,0x240400b1ee30009c3839dd2c15d05163b2d4473fa276704c128e75110632c4db6c46dc0251d281104d1808027408c422038c6c0,966367641600,0x380000b1e6007e1c1cfa582a5ea71d96a973fa973e3e52a3a4db18cb4b6db76dc0951d271713457817a5bc425cc6c0,0xdff0ff1f00000,0xe1605f307f1fe9c3a70438604208400020600b0e1c303361d2f0bbf05bf3396b7e60b7a99943e450001b9c341c3813961991910794cca07231000600b0e0870c07fbd2a6d5399c1a236a952a4ee2361f6e70d0623ccce19999964a9527111133a5e177e0b7e672d6fcc16f533287c8a020dccccce1c09cb0cc8c883ca665039188003405b0bbf05bf3032d6fcc16f5332063df228000dce1a0e1c09cc0cc8c883ca665039188,0xd202110e100000,0x383f4e1e82001f8707ce960a97a9c7cb54bc153958f8f8fea69f1d012dcddbb870e04a95271718834463f4e41b03c83a5cd806,0xd20000000000000,0x240400b9e00270e0ee960ae828b1d96a2390289b9c388dfd13b3823136db11b804a3a50220c41a1e5c6c04013a046210d806,0xc3000cff1fffdeef1f00000,0x181d383d9dfec20f8983986400300010b0bd0b57fa9b54ba76a9cce60daa6846f9611b9e311e665666666592a548417143c261803020300dd2dabad6f6e76af8ec636a2708df189b6db764e3e3c7c76128e9082e2686f9321016c2c5adec476af99c71b5bf2237cb09b9bb11d93958f8f8f6f2912105c4d0239903190,0x1111021100000000,0xc01c01f1f100c000b0bed5fea6d52e9daa733983446d534237c1cccaccccccb254a9082e22287b000c018101617e6a02d858b5bd88ed5f338e3446d6fc88df06c9cac7cc7cb79489082e22268730018c6,0xcfffffeeeefdef00000000,0x74e0f03dfecc1a1042ff3f78000058f374b05766894749ebe3b1fd13a32f8c4db6dba71f1f1c0251d2a2e2686f9c746722220d789c41a0c6,0xb14520c300000000000000000,0x1fffdd803ee72161feeffbff75f51fecbfedef2249ffdbf3e95edce6e726e749cac9656563bfef525e143ceab0d7f2ecc8c6c0c04246f4a0ce,0x1111021100000000,0x499e81803f603f7d87fffdffbafa8ff65ff6f79124ed6fc8cbfedf9f4af77d272b259591959ff7a92f0de287aac35fce7320034a33810012f4a20c6,0xa4dddde1eeececfdef00000000,0x259fd37cd049e7821080903301e615828b2d441320a27f826094b21061fb41b6db70273390657009482420f0820688443837069068,0xe1000000000000,0x30e986c879c0c8184883f87864daa9cb54be415358efd2a37030fda0db6dbccccccc812a549c78415e6507106e06,0xd0011110121000000000000,0x1fa39acfd07f0fc0c821941c409015b5165a88c4a1a2396a27f82316836db764e463e3e3b0948242088f081b8abfa2c1288c4ab5104ccd16704626506db86fd3918f918df894cc841104d1106ca0e23818c6,0x152200000000000f0e100000,0x13903184e338560a2c7575a88263a0a27f8e1304a593a420c3f6836db6db804a41274841e101ac0cd10874331839a438c6b0,966367641600,0x90c1d220fe1992e339a6d54e3aa6d52f8e82a6b1cefd2a36e5030fda0db6db6e04a952749c78415c1ac0d941b8871838c6b0,0xcffffffff0ff1f00000,0x7fff7603f41f8fe4206b0ff37fdaa9c7fb2ffa975527ff53592bdb9cdce4dcf333333333fd2a54a52f0a1e765843ce506e7198c0c030abfa2cb0b02511894e79a2ce6447941b6e70dfa7323231bf12999664209a2220dff6ad65858ffbe75527ff7d59987941b9b9c3a4e656563bfe14a9665038198a40c6c0c0,0x6fffffffffff3000000000000000000,0xfee3069239d88187cc61ff6ad54ac9dabb7c97fd4075927739c9b9b9e666666667fcfa952949c47e7dd8d2c9628c2b476be719125b23dc99243486e683f393d986c8c893ca44a49409a3d06318bed2c9408fa2fd68ed7ce322acfad1d01f9567811ed21b9a0fce4f661b23008fab3fca44aacf9011e28011fe8318cd2c9428fa30ad1daf9c64495a393248690dcccc80f727b30d91912159ea44a494098051e407c0f98c605f,0x2172000000000000000000000000,0xfee7f719ce3eff6b6b3ee564c68bb5406a485ce726e6e767c7c363e3e3ad3ea44fca4223f3ee7d7dc3345f439e0c63187cc6,0x2222222222221111021100000000,0x13eff3f21b5353edacfb9f959390d1636a80d01490d9f138f86c7c7cb4fa880a44fca4223f3efafebef5f83421ebef43c2068034185e6803cd006]
def row9 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0xf00088884444222211110f0000f0000f,0xff7a592d6fcefd407f99f1f6e683f38139c30d9191be80a3f9644d1e8,0xefff9887bbbbddddeeeefdeef1efff1efff2,0x5f307f1fe9c1031a0002c30301fef4b25adf9dfa80ff33e3edcd07e70273861b23237d0147f2c89bd1be80ff3e8,64439255054,0xe9d3a209e9c10319041fef4a9b54befd4d3cf8fb7341f9b4a6a4e319b999c30d9999be952a4e268f409e06c881268,0xf00e0100000000,0x180008601a10319fef4a9b54bb7ea5cf94a8e940c658fb6d06de6670c36666fa54749c4d15e5e8343dece18d106,0xe0121000000000000,0xbe60fe3fd382067fbd2c96b7e77ea028fe591dfa80ff33e3edcd07e7e70273861b2323237d0147f2c8c7a1fef4b25adf9dfa80a3f96477ea03fccf8fb7341f9f9c09ce186c8c8c8df4051fcb231e88000b0c02fd30b25adf9dfa80a3f96477ea03fccfc0373007e7e70272c33032323237d0147f2c8831fe8,0xd20000000000000000,0x30e86001d382067fbd2a6d52f054e563e6fd4d3cf8fb7341c3f3ccce186cccdf4a9527188347b204c618010813c0d906,0xd010310000000000000000,0x2c3821c301fef4a9b54e670688daa69f06c3edce1a0c47999c333332c952a4e22268133a5e177e0b7e672d6fcbfb7e73994041b99999c3813961991910794cca072268883001a02d85df82df98196b7e5fdbf39cca000373868387027303323220f299940e470018f88c0]
def row10 : BinaryTree (ℕ × ℕ) := ofDeltaFlat [0xf00088884444222211110f0000f0000f,0xff7a530b500c0e9602c3007c7db9a0d07c139c30d86c3748052c2580263206]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_1 : (checkCutsInitV8 fullVal 1 row1 (cutsMP 2 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_2 : (checkCutsInitV8 fullVal 2 row2 (cutsMP 3 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_3 : (checkCutsInitV8 fullVal 3 row3 (cutsMP 4 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_4 : (checkCutsInitV8 fullVal 4 row4 (cutsMP 5 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_5 : (checkCutsInitV8 fullVal 5 row5 (cutsMP 6 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_6 : (checkCutsInitV8 fullVal 6 row6 (cutsMP 7 (inputs.map fun w => (w, sepM maskParam bits w))) 0).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_7 : (checkCutsInitV8 fullVal 7 row7 (cutsMP 8 (inputs.map fun w => (w, sepM maskParam bits w))) 12).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_8 : (checkCutsInitV8 fullVal 8 row8 (cutsMP 9 (inputs.map fun w => (w, sepM maskParam bits w))) 12).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_9 : (checkCutsInitV8 fullVal 9 row9 (cutsMP 10 (inputs.map fun w => (w, sepM maskParam bits w))) 6).isSome = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chkInit_10 : (checkCutsInitV8 fullVal 10 row10 (cutsMP 11 (inputs.map fun w => (w, sepM maskParam bits w))) 6).isSome = true := by decide +kernel

abbrev vf5 := verifyNodeV8 maskParam fullVal 4 bits row4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk5 : checkTree (vf5) row5 = true := by decide +kernel
abbrev vf6 := verifyNodeV8 maskParam fullVal 5 bits row5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6L : checkTree (vf6) row6_c0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk6R : checkTree (vf6) row6_c1 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem chk6V : (vf6) 0xf0008f8844f422f2111f0f00000f 0x8be4023efb56a9ebbbe45f0aa9dfd4e1c38f2952718 = true := by decide +kernel
theorem chk6 : checkTree (vf6) row6 = true := checkTree_node chk6V chk6L chk6R
abbrev vf7 := verifyNodeV8 maskParam fullVal 6 bits row6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk7L : checkTree (vf7) row7_c0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk7R : checkTree (vf7) row7_c1 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem chk7V : (vf7) 0xf0008888444f44442f22111f0f0000f0 0x1fffdd803ee7587fbbfeffdd7d47fb2ffb7bc8927ff6f525e94bc239cdce4dce939592cacac7586bf993b26c0c0 = true := by decide +kernel
theorem chk7 : checkTree (vf7) row7 = true := checkTree_node chk7V chk7L chk7R
abbrev vf8 := verifyNodeV8 maskParam fullVal 7 bits row7
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk8 : checkTree (vf8) row8 = true := by decide +kernel
abbrev vf9 := verifyNodeV8 maskParam fullVal 8 bits row8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk9 : checkTree (vf9) row9 = true := by decide +kernel
abbrev vf10 := verifyNodeV8 maskParam fullVal 9 bits row9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem chk10 : checkTree (vf10) row10 = true := by decide +kernel
theorem fullVal_eq : fullVal = fullM maskParam bits := by decide +kernel
theorem hbits_proof : ∀ bitB ∈ bits, ∃ b, bitB = 2 ^ b ∧ b < 16 ∧ targetNat.testBit b = false := by
  intro bitB h; simp only [bits, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨5, rfl, by decide, by decide⟩
  · exact ⟨6, rfl, by decide, by decide⟩
  · exact ⟨9, rfl, by decide, by decide⟩
  · exact ⟨11, rfl, by decide, by decide⟩
  · exact ⟨14, rfl, by decide, by decide⟩
  · exact ⟨15, rfl, by decide, by decide⟩

theorem excl_1 {x : ℕ} (hx : InTree x row1) (_ : ReachMin 10 1 (unpack x).toFinset) : False := hx
theorem excl_2 {x : ℕ} (hx : InTree x row2) (_ : ReachMin 10 2 (unpack x).toFinset) : False := hx
theorem excl_3 {x : ℕ} (hx : InTree x row3) (_ : ReachMin 10 3 (unpack x).toFinset) : False := hx
theorem excl_4 {x : ℕ} (hx : InTree x row4) (_ : ReachMin 10 4 (unpack x).toFinset) : False := hx
theorem excl_5 {x : ℕ} (hx : InTree x row5) (hr : ReachMin 10 5 (unpack x).toFinset) : False := by
  obtain ⟨hh, hchk⟩ := checkTree_sound row5 chk5 x hx
  dsimp only [vf5] at hchk; rw [fullVal_eq] at hchk
  obtain ⟨y, hy, hry⟩ := advanceNodeV8 targetNat_lt hbits_proof (by decide) hchk hr
  exact excl_4 hy hry
theorem excl_6 {x : ℕ} (hx : InTree x row6) (hr : ReachMin 10 6 (unpack x).toFinset) : False := by
  obtain ⟨hh, hchk⟩ := checkTree_sound row6 chk6 x hx
  dsimp only [vf6] at hchk; rw [fullVal_eq] at hchk
  obtain ⟨y, hy, hry⟩ := advanceNodeV8 targetNat_lt hbits_proof (by decide) hchk hr
  exact excl_5 hy hry
theorem excl_7 {x : ℕ} (hx : InTree x row7) (hr : ReachMin 10 7 (unpack x).toFinset) : False := by
  obtain ⟨hh, hchk⟩ := checkTree_sound row7 chk7 x hx
  dsimp only [vf7] at hchk; rw [fullVal_eq] at hchk
  obtain ⟨y, hy, hry⟩ := advanceNodeV8 targetNat_lt hbits_proof (by decide) hchk hr
  exact excl_6 hy hry
theorem excl_8 {x : ℕ} (hx : InTree x row8) (hr : ReachMin 10 8 (unpack x).toFinset) : False := by
  obtain ⟨hh, hchk⟩ := checkTree_sound row8 chk8 x hx
  dsimp only [vf8] at hchk; rw [fullVal_eq] at hchk
  obtain ⟨y, hy, hry⟩ := advanceNodeV8 targetNat_lt hbits_proof (by decide) hchk hr
  exact excl_7 hy hry
theorem excl_9 {x : ℕ} (hx : InTree x row9) (hr : ReachMin 10 9 (unpack x).toFinset) : False := by
  obtain ⟨hh, hchk⟩ := checkTree_sound row9 chk9 x hx
  dsimp only [vf9] at hchk; rw [fullVal_eq] at hchk
  obtain ⟨y, hy, hry⟩ := advanceNodeV8 targetNat_lt hbits_proof (by decide) hchk hr
  exact excl_8 hy hry
theorem excl_10 {x : ℕ} (hx : InTree x row10) (hr : ReachMin 10 10 (unpack x).toFinset) : False := by
  obtain ⟨hh, hchk⟩ := checkTree_sound row10 chk10 x hx
  dsimp only [vf10] at hchk; rw [fullVal_eq] at hchk
  obtain ⟨y, hy, hry⟩ := advanceNodeV8 targetNat_lt hbits_proof (by decide) hchk hr
  exact excl_9 hy hry

theorem excluded (hc : CanM targetNat 10 inputs.toFinset) : False := by
  obtain ⟨seq, hlenK, hmin⟩ := exists_minimal_seq hc
  generalize hs_eq : seq.length = s at hlenK
  have hs_le : s ≤ 10 := hlenK
  interval_cases s
  · have hnil : seq = [] := List.eq_nil_of_length_eq_zero hs_eq
    have hf := hmin.2.1; rw [hnil] at hf; simp only [endSet, freeM, freeMD, List.mem_toFinset] at hf
    have hno : ¬ (targetNat = 0 ∨ targetNat = 65535 ∨ targetNat ∈ inputs) := by decide
    exact hno hf
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_1
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_1 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_2
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_2 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_3
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_3 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_4
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_4 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_5
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_5 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_6
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_6 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_7
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_7 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_8
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_8 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_9
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_9 hx hrm
  · obtain ⟨h0, hh0⟩ := Option.isSome_iff_exists.mp chkInit_10
    rw [fullVal_eq] at hh0
    obtain ⟨x, hx, hrm⟩ := initV8_sound targetNat_lt hbits_proof hh0 seq hs_eq (by decide) hmin (by decide)
    exact excl_10 hx hrm

theorem oneEach_map (p : Fin 16) :
    oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4) =
    inputs.map (fun t => t.testBit p.val) := by
  revert p; decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (13726 : ℕ).testBit (4 * u.val + v.val)) 10 := by
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
  change C.gates.length ≤ _ at hs
  exact excluded (padCMD hs hc)

end PEqualNP.Outside.L_meta_8969_aux

theorem PEqualNP.Outside.L_meta_8969 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13726 : ℕ).testBit (4 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_8969_aux.lower
