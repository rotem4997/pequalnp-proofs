import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3783_487
    (classify : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      0 < q → n = q^2 + q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (b : Bool) (S : Set (Fin n)) (p r : Fin n),
        let R := fun u v => cond b (I u v) (I v u)
        p ∈ S → r ∈ S → p ≠ r →
          (∃ l : Fin n, (∀ v ∈ S, R v l) ∧ S.ncard ≤ q+1 ∧
            ∀ k : Fin n, k ≠ l → (S ∩ {v | R v k}).ncard ≤ 1) ∨
          ∃ t ∈ S, t ≠ p ∧ t ≠ r ∧ ∀ l : Fin n, ¬(R p l ∧ R r l ∧ R t l))
    (pencil : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        100 < q → n = q^2 + q + 1 → (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → q % 2 = 1 →
        ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
        let one := fun (u v : Fin n) => decide (v = u)
        let A := fun (b : Bool) (i : ℕ) => {u : Fin n | ite (b=true)
          (one u,fun _ => false) (fun _ => false,one u) ∈ W i}
        o < n+n+s →
        (∀ u : Fin n, W u.val = {z | z.1 u = true} ∧ W (n+u.val) = {z | z.2 u = true}) →
        (∀ j < s, ∃ u v, max u v < n+n+j ∧ W (n+n+j) ∈ [W u ∪ W v,W u,∅,W u ∩ W v]) →
        (∀ p l, I p l → (one p,one l) ∈ W o) →
        (∀ y : Fin n → Bool, Fintype.card {v // y v = true} ≤ q →
          (fun p => decide (¬∃ l, I p l ∧ y l = true), y) ∉ W o) →
        (∃ j < s, ∃ b : Bool,
          let S := A b (n+n+j)
          (¬∃ u < n+n+j, ∃ v < n+n+j, S = A b u ∪ A b v) ∧
          ∃ l : Fin n, (∀ u ∈ S, cond b (I u l) (I l u)) ∧ S.ncard ≤ q+1 ∧
            ∀ k : Fin n, k ≠ l → (S ∩ {u | cond b (I u k) (I k u)}).ncard ≤ 1) → n*q ≤ 100*s)
    (triangle : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        100 < q → n = q^2 + q + 1 → (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → q % 2 = 1 →
        ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
        let one := fun (u v : Fin n) => decide (v = u)
        let A := fun (b : Bool) (i : ℕ) => {u : Fin n | ite (b=true)
          (one u,fun _ => false) (fun _ => false,one u) ∈ W i}
        o < n+n+s →
        (∀ u : Fin n, W u.val = {z | z.1 u = true} ∧ W (n+u.val) = {z | z.2 u = true}) →
        (∀ j < s, ∃ u v, max u v < n+n+j ∧ W (n+n+j) ∈ [W u ∪ W v,W u,∅,W u ∩ W v]) →
        (∀ p l, I p l → (one p,one l) ∈ W o) →
        (∀ y : Fin n → Bool, Fintype.card {v // y v = true} ≤ q →
          (fun p => decide (¬∃ l, I p l ∧ y l = true), y) ∉ W o) →
        (∃ j < s, ∃ b : Bool,
          let S := A b (n+n+j)
          (¬∃ u < n+n+j, ∃ v < n+n+j, S = A b u ∪ A b v) ∧
          (∀ l : Fin n, ∃ u ∈ S, ¬cond b (I u l) (I l u))) → n*q ≤ 100*s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (1 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x22 : Bool) (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 x22 (x13 + x21) ∧ x24 ∈ x20 x22 (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 x22 (x13 + x21) = x20 x22 x25 ∪ x20 x22 x26) →                           x2 * x1 ≤ (100 : ℕ) * x10 := by
  dsimp only
  intro q n I inst large plane cardinal unique odd s o W range inputs gates positive negative hasDirty
  classical
  let one (u v : Fin n) := decide (v=u)
  let A (b : Bool) (i : ℕ) : Set (Fin n) :=
    {u | ite (b=true) (one u,fun _ => false) (fun _ => false,one u) ∈ W i}
  let primary (b : Bool) (u : Fin n) := cond b u.val (n+u.val)
  have base (b : Bool) (u : Fin n) : primary b u < n+n := by
    have h := u.isLt
    cases b
    · change n+u.val < n+n
      omega
    · change u.val < n+n
      omega
  have sig (b : Bool) (u : Fin n) : A b (primary b u) = {u} := by
    cases b with
    | false =>
      change {v : Fin n | ((fun _ => false),one v) ∈ W (n+u.val)} = {u}
      rw [(inputs u).2]
      ext v
      change decide (u = v) = true ↔ v = u
      rw [decide_eq_true_eq]
      exact eq_comm
    | true =>
      change {v : Fin n | (one v,fun _ => false) ∈ W u.val} = {u}
      rw [(inputs u).1]
      ext v
      change decide (u = v) = true ↔ v = u
      rw [decide_eq_true_eq]
      exact eq_comm
  have nNonzero : 0 < n := by omega
  let origin : Fin n := ⟨0,nNonzero⟩
  have empty (b : Bool) : A b (primary (!b) origin) = ∅ := by
    cases b with
    | false =>
      change {v : Fin n | ((fun _ => false),one v) ∈ W origin.val} = ∅
      rw [(inputs origin).1]
      ext v
      simp
    | true =>
      change {v : Fin n | (one v,fun _ => false) ∈ W (n+origin.val)} = ∅
      rw [(inputs origin).2]
      ext v
      simp
  obtain ⟨j,hj,b,_p,_r,_different,_hp,_hr,broken⟩ := hasDirty
  let bad (i : ℕ) := i < s ∧ ¬∃ u < n+n+i, ∃ v < n+n+i, A b (n+n+i) = A b u ∪ A b v
  have existsBad : ∃ i, bad i := ⟨j,hj,broken⟩
  let t := Nat.find existsBad
  have ht : t < s := (Nat.find_spec existsBad).1
  have badT : ¬∃ u < n+n+t, ∃ v < n+n+t, A b (n+n+t) = A b u ∪ A b v := (Nat.find_spec existsBad).2
  let S := A b (n+n+t)
  have basis (u : Fin n) : primary b u < n+n+t := (base b u).trans_le (by omega)
  have zeroBasis : primary (!b) origin < n+n+t := (base (!b) origin).trans_le (by omega)
  have S_nonempty : S.Nonempty := by
    by_contra no
    have eq : S = ∅ := Set.not_nonempty_iff_eq_empty.mp no
    apply badT
    refine ⟨primary (!b) origin,zeroBasis,primary (!b) origin,zeroBasis,?_⟩
    change S = A b (primary (!b) origin) ∪ A b (primary (!b) origin)
    rw [eq,empty]
    simp
  obtain ⟨x,hx⟩ := S_nonempty
  have second : ∃ y ∈ S, y ≠ x := by
    by_contra! no
    have eq : S = {x} := by
      ext y
      exact ⟨fun h => no y h,fun h => (Set.mem_singleton_iff.mp h).symm ▸ hx⟩
    apply badT
    refine ⟨primary b x,basis x,primary b x,basis x,?_⟩
    change S = A b (primary b x) ∪ A b (primary b x)
    rw [eq,sig]
    simp
  obtain ⟨y,hy,ne⟩ := second
  rcases classify q n I (by omega) plane cardinal unique b S x y hx hy ne.symm with pencilShape | triangleShape
  · exact pencil q n I large plane cardinal unique odd s o W range inputs gates positive negative
      ⟨t,ht,b,badT,pencilShape⟩
  · obtain ⟨r,hr,_rx,_ry,off⟩ := triangleShape
    have noCommon (l : Fin n) : ∃ u ∈ S, ¬cond b (I u l) (I l u) := by
      by_contra! all
      exact off l ⟨all x hx,all y hy,all r hr⟩
    exact triangle q n I large plane cardinal unique odd s o W range inputs gates positive negative
      ⟨t,ht,b,badT,noCommon⟩
