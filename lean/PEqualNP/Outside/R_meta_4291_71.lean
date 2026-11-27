import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4291_71
    (certificates : ∀ (q n s : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
      0 < q →
      (∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true}) →
      (∀ j < s, ∃ a b, max a b < n+n+j ∧ W (n+n+j) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      ∃ F : ℕ → Set (Finset (Fin n) × Finset (Fin n)),
        (∀ p : Fin n, F p.val = {({p}, ∅)} ∧ F (n+p.val) = {(∅, {p})}) ∧
        (∀ j < s, ∃ a b, max a b < n+n+j ∧ F (n+n+j) ∈
          [F a ∪ F b, F a, ∅, {t ∈ Set.image2 (· ⊔ ·) (F a) (F b) | t.2.card ≤ q}]) ∧
        ∀ w < n+n+s, ∀ P L : Fin n → Bool, Fintype.card {l : Fin n // L l = true} ≤ q →
          ((P,L) ∈ W w ↔ ∃ t ∈ F w, (∀ p ∈ t.1, P p = true) ∧ ∀ l ∈ t.2, L l = true))
    (count : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      100 < q → n = q^2+q+1 → (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (F : ℕ → Set (Finset (Fin n) × Finset (Fin n))),
      o < n+n+s →
      (∀ p : Fin n, F p.val = {({p}, ∅)} ∧ F (n+p.val) = {(∅, {p})}) →
      (∀ j < s, ∃ a b, max a b < n+n+j ∧ F (n+n+j) ∈
        [F a ∪ F b, F a, ∅, {t ∈ Set.image2 (· ⊔ ·) (F a) (F b) | t.2.card ≤ q}]) →
      (∀ p l, I p l → ({p}, {l}) ∈ F o) →
      (∀ t ∈ F o, ∃ p ∈ t.1, ∃ l ∈ t.2, I p l) →
      (let S (w : ℕ) := {l : Fin n | ∃ t ∈ F w, t ≤ (∅, {l})}
       ∃ j < s, ∃ p r : Fin n, p ≠ r ∧ p ∈ S (n+n+j) ∧ r ∈ S (n+n+j) ∧
         ¬∃ a < n+n+j, ∃ b < n+n+j, S (n+n+j) = S a ∪ S b) →
      n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.false (x12 + x20) ∧ x22 ∈ x19 Bool.false (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.false (x12 + x20) = x19 Bool.false x23 ∪ x19 Bool.false x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  dsimp only
  intro q n I inst hq hn degree unique s o W ho hraw hgate positive negative witness
  obtain ⟨F, raw, gate, eval⟩ := certificates q n s W (by omega) hraw hgate
  have bounded : ∀ w < n+n+s, ∀ t ∈ F w, t.2.card ≤ q := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw t ht
      by_cases hp : w < n
      · rw [(raw ⟨w,hp⟩).1] at ht
        obtain rfl := Set.mem_singleton_iff.mp ht
        simp
      by_cases hl : w < n+n
      · let l : Fin n := ⟨w-n, by omega⟩
        have he : w = n+l.val := by dsimp [l]; omega
        rw [he, (raw l).2] at ht
        obtain rfl := Set.mem_singleton_iff.mp ht
        simpa using (show 1 ≤ q by omega)
      let j := w-(n+n)
      have he : n+n+j = w := by dsimp [j]; omega
      obtain ⟨a,b,hab,rule⟩ := gate j (by omega)
      rw [he] at hab rule
      simp only [List.mem_cons, List.not_mem_nil, or_false] at rule
      have ha := ih a (lt_of_le_of_lt (le_max_left _ _) hab) (by omega) t
      have hb := ih b (lt_of_le_of_lt (le_max_right _ _) hab) (by omega) t
      rcases rule with eq | eq | eq | eq <;> rw [eq] at ht
      · exact ht.elim ha hb
      · exact ha ht
      · exact False.elim ht
      · exact ht.2
  have sound (t) (ht : t ∈ F o) : ∃ p ∈ t.1, ∃ l ∈ t.2, I p l := by
    let L (l : Fin n) := decide (l ∈ t.2)
    have hL : Fintype.card {l : Fin n // L l = true} ≤ q := by
      simpa [L, Fintype.card_subtype] using bounded o ho t ht
    by_contra noEdge
    apply negative L hL
    apply (eval o ho _ L hL).2
    refine ⟨t,ht,?_,?_⟩
    · intro p hp
      apply decide_eq_true
      rintro ⟨l, edge, on⟩
      exact noEdge ⟨p,hp,l,of_decide_eq_true on,edge⟩
    · intro l hl
      exact decide_eq_true hl
  refine count q n I hq hn degree unique s o F ho raw gate ?_ sound ?_
  · intro p l edge
    have sparse : Fintype.card {i : Fin n // decide (i=l) = true} ≤ q := by
      simpa [Fintype.card_subtype] using (show 1 ≤ q by omega)
    obtain ⟨t,ht,hp,hl⟩ := (eval o ho _ _ sparse).1 (positive p l edge)
    obtain ⟨u,hu,v,hv,_⟩ := sound t ht
    have hP : t.1 = {p} := by
      ext i
      simp only [Finset.mem_singleton]
      exact ⟨fun h => of_decide_eq_true (hp i h), fun e => e ▸ (of_decide_eq_true (hp u hu)) ▸ hu⟩
    have hL : t.2 = {l} := by
      ext i
      simp only [Finset.mem_singleton]
      exact ⟨fun h => of_decide_eq_true (hl i h), fun e => e ▸ (of_decide_eq_true (hl v hv)) ▸ hv⟩
    rwa [← hP, ← hL]
  · let S (w : ℕ) := {l : Fin n | ∃ t ∈ F w, t ≤ (∅, {l})}
    let A (w : ℕ) := {l : Fin n | ((fun _ => false), (fun i => decide (i=l))) ∈ W w}
    have hS (w) (hw : w < n+n+s) : A w = S w := by
      ext l
      have sparse : Fintype.card {i : Fin n // decide (i=l) = true} ≤ q := by
        simpa [Fintype.card_subtype] using (show 1 ≤ q by omega)
      change ((fun _ => false), (fun i => decide (i=l))) ∈ W w ↔ _
      rw [eval w hw _ _ sparse]
      constructor
      · rintro ⟨t,ht,hp,hl⟩
        refine ⟨t,ht,fun i hi => ?_,fun i hi => ?_⟩
        · exact Bool.noConfusion (hp i hi)
        · exact Finset.mem_singleton.mpr (of_decide_eq_true (hl i hi))
      · rintro ⟨t,ht,hp,hl⟩
        refine ⟨t,ht,fun i hi => ?_,fun i hi => ?_⟩
        · exact False.elim (Finset.notMem_empty i (hp hi))
        · exact decide_eq_true (Finset.mem_singleton.mp (hl hi))
    simp only [Bool.false_eq_true, ite_false] at witness
    change ∃ j < s, ∃ p r, p ≠ r ∧ p ∈ A (n+n+j) ∧ r ∈ A (n+n+j) ∧
      ¬∃ a < n+n+j, ∃ b < n+n+j, A (n+n+j) = A a ∪ A b at witness
    obtain ⟨j,hj,p,r,hpr,hp,hr,hnew⟩ := witness
    have hg := hS (n+n+j) (by omega)
    rw [hg] at hp hr
    refine ⟨j,hj,p,r,hpr,hp,hr,?_⟩
    rintro ⟨a,ha,b,hb,eq⟩
    exact hnew ⟨a,ha,b,hb,by rw [hg,hS a (by omega),hS b (by omega)]; exact eq⟩
