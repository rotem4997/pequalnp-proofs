import PEqualNP.Defs

-- A false certificate lists primary bits whose simultaneous absence forces rejection.
-- The output certificates cover all flags, and include each sparse-line minimal cover.
theorem PEqualNP.Outside.R_meta_2794_601
    (certificates : ∀ (Z : Type) (m s : ℕ) (X : ℕ → Set Z), (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        X (m+g) = X a ∪ X b ∨ X (m+g) = X a ∨ X (m+g) = ∅ ∨ X (m+g) = X a ∩ X b) →
      ∃ F : ℕ → Set (Finset ℕ), (∀ v < m, F v = {{v}}) ∧
        (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
        F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) ∧
        ∀ w < m+s, (∀ A ∈ F w, ∀ v ∈ A, v < m) ∧
          ∀ z, z ∉ X w ↔ ∃ A ∈ F w, ∀ v ∈ A, z ∉ X v)
    (freshPoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ T : Finset (Fin N), T.card ≤ q → ∀ l : Fin N, l ∉ T →
        ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (coverBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N+N+s → (∀ v < N+N, F v = {{v}}) →
      (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
        F (N+N+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (N+N+g) = F a ∨
        F (N+N+g) = {∅} ∨ F (N+N+g) = F a ∪ F b) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N+l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
        (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) → N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
      (100 : ℕ) < x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
      ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),
      x10 < x2 + x2 + x9 →
      (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →
      (∀ x15 < x9,
      ∃ x17 < x2 + x2 + x15,
      ∃ x18 < x2 + x2 + x15,
      have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);
      x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →
      (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I inst hq hN degrees unique s o tags X ho inputs steps pos neg _
  obtain ⟨F, leaves, gates, spec⟩ := certificates _ (N+N) s X (by
    intro g hg
    obtain ⟨a, ha, b, hb, law⟩ := steps g hg
    exact ⟨a, ha, b, hb, law.imp_right (Or.imp_right (Or.imp_right And.left))⟩)
  have cover (A : Finset ℕ) (hA : A ∈ F o) (p l : Fin N) (h : I p l) : p.val ∈ A ∨ N+l.val ∈ A := by
    by_contra! miss
    apply ((spec o ho).2 _).mpr ⟨A,hA,?_⟩ (pos p l h)
    intro v hv
    have hvb := (spec o ho).1 A hA v hv
    by_cases small : v < N
    · let k : Fin N := ⟨v,small⟩
      rw [(inputs k).1]
      change ¬ decide (k = p) = true
      exact fun e => miss.1 ((congrArg Fin.val (of_decide_eq_true e)) ▸ hv)
    · let k : Fin N := ⟨v-N,by omega⟩
      have e : v = N + k.val := by dsimp [k]; omega
      rw [e,(inputs k).2]
      change ¬ decide (k = l) = true
      intro eq
      have : v = N+l.val := e.trans (congrArg (fun a : Fin N => N+a.val) (of_decide_eq_true eq))
      exact miss.2 (this ▸ hv)
  have saturated : ∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
      (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T) := by
    intro T ht
    let y := fun l : Fin N => decide (l ∈ T)
    let x := fun p : Fin N => decide (¬ ∃ l, I p l ∧ y l = true)
    have cy : Fintype.card {l : Fin N // y l = true} ≤ q := by
      simpa [Fintype.card_subtype, y] using ht
    obtain ⟨A,hA,zero⟩ := ((spec o ho).2 (x,y)).mp (neg y cy)
    have pl (p : Fin N) (h : p.val ∈ A) : ∃ l ∈ T, I p l := by
      have hh := zero p.val h
      rw [(inputs p).1] at hh
      change ¬ x p = true at hh
      simpa [x,y,and_comm] using hh
    have ln (l : Fin N) (h : N+l.val ∈ A) : l ∉ T := by
      have hh := zero _ h
      rw [(inputs l).2] at hh
      exact fun m => hh (show y l = true from decide_eq_true m)
    refine ⟨A,hA,fun p => ⟨⟨pl p,?_⟩,⟨ln p,?_⟩⟩⟩
    · rintro ⟨l,hl,inc⟩
      exact (cover A hA p l inc).resolve_right (fun bad => ln l bad hl)
    · intro hp
      obtain ⟨a, ha, avoid⟩ := freshPoint q N I degrees unique T ht p hp
      apply (cover A hA a p ha).resolve_left
      intro bad
      obtain ⟨l,hl,inc⟩ := pl a bad
      exact avoid l hl inc
  by_cases large : 200 ≤ q
  · exact coverBound q N I large hN degrees unique s o F ho leaves gates cover saturated
  have propagate (g : ℕ) (hg : g < s) : ∃ a < N+N+g, ∃ b < N+N+g,
      ∀ A ∈ F (N+N+g), ∀ v ∈ A, ∃ B, (B ∈ F a ∨ B ∈ F b) ∧ v ∈ B := by
    obtain ⟨a,ha,b,hb,law⟩ := gates g hg
    refine ⟨a,ha,b,hb,?_⟩
    intro A hA v hv
    rcases law with join|copy|empty|meet
    · rw [join] at hA
      obtain ⟨U,hU,V,hV,rfl⟩ := hA
      exact (Finset.mem_union.mp hv).elim (fun h => ⟨U,Or.inl hU,h⟩) (fun h => ⟨V,Or.inr hV,h⟩)
    · exact ⟨A,Or.inl (copy ▸ hA),hv⟩
    · have e : A = ∅ := Set.mem_singleton_iff.mp (empty ▸ hA)
      exact False.elim (Finset.notMem_empty _ (e ▸ hv))
    · rw [meet] at hA; exact ⟨A,hA,hv⟩
  have reach (k : ℕ) (hk : k ≤ s) (W : Finset ℕ) (hw : ∀ w ∈ W, w < N+N+k) :
      ∃ S : Finset ℕ, S.card ≤ W.card+k ∧ ∀ w ∈ W, ∀ A ∈ F w, A ⊆ S := by
    induction k generalizing W with
    | zero =>
      refine ⟨W,by omega,?_⟩
      intro w mem A cert
      rw [leaves w (by simpa using hw w mem)] at cert
      have : A = {w} := Set.mem_singleton_iff.mp cert
      simpa [this] using mem
    | succ k ih =>
      let w := N+N+k
      by_cases use : w ∈ W
      · obtain ⟨a,ha,b,hb,parent⟩ := propagate k (by omega)
        let U := insert a (insert b (W.erase w))
        have bounds : ∀ u ∈ U, u < w := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl|h
          · exact ha
          rcases Finset.mem_insert.mp h with rfl|h
          · exact hb
          obtain ⟨ne,inc⟩ := Finset.mem_erase.mp h
          have bound := hw u inc
          change u ≠ N+N+k at ne
          change u < N+N+k
          omega
        obtain ⟨S,c,dep⟩ := ih (by omega) U bounds
        have uc : U.card ≤ W.card+1 := by
          have c1 := Finset.card_insert_le a (insert b (W.erase w))
          have c2 := Finset.card_insert_le b (W.erase w)
          rw [Finset.card_erase_of_mem use] at c2
          have := Finset.card_pos.mpr ⟨_,use⟩
          dsimp [U]; omega
        refine ⟨S,by omega,?_⟩
        intro u hu A cert v hv
        by_cases eq : u=w
        · subst u
          obtain ⟨B,anc,hv'⟩ := parent A cert v hv
          rcases anc with h|h
          · exact dep a (by simp [U]) B h hv'
          · exact dep b (by simp [U]) B h hv'
        · exact dep u (by simp [U,eq,hu]) A cert hv
      · have bounds : ∀ u ∈ W, u < w := by
          intro u hu
          have ne : u ≠ w := fun eq => use (eq ▸ hu)
          have bound := hw u hu
          change u ≠ N+N+k at ne
          change u < N+N+k
          omega
        obtain ⟨S,c,h⟩ := ih (by omega) W bounds
        exact ⟨S,by omega,h⟩
  obtain ⟨S,card,dep⟩ := reach s le_rfl {o} (by simpa using ho)
  have allBits : Finset.range (N+N) ⊆ S := by
    intro v hv
    have bound := Finset.mem_range.mp hv
    by_cases point : v < N
    · let p : Fin N := ⟨v,point⟩
      have big : 2 ≤ N := by nlinarith [Nat.zero_le (q^2)]
      let p' : Fin N := if p.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have ne : p ≠ p' := by
        intro e
        have eq := congrArg Fin.val e
        unfold p' at eq
        split at eq
        · change p.val = 1 at eq; omega
        · change p.val = 0 at eq; contradiction
      obtain ⟨l,hl,_⟩ := unique p p' ne
      obtain ⟨A,hA,eq⟩ := saturated {l} (by simp; omega)
      exact dep o (by simp) A hA ((eq p).1.mpr ⟨l,by simp,hl.1⟩)
    · let l : Fin N := ⟨v-N,by omega⟩
      obtain ⟨A,hA,eq⟩ := saturated ∅ (by simp)
      have inc := dep o (by simp) A hA ((eq l).2.mpr (by simp))
      have e : N+l.val=v := by dsimp [l]; omega
      exact e ▸ inc
  have count := Finset.card_le_card allBits
  simp only [Finset.card_range] at count
  simp only [Finset.card_singleton] at card
  have qmax : q ≤ 199 := by omega
  have := Nat.mul_le_mul_left N qmax
  have nn : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
  omega
