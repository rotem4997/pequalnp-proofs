import PEqualNP.Defs

-- The circuit's compulsory input dependencies settle all orders through 198.
-- For higher orders, truncate at the first wire separating the promised tests and use one
-- star per line. The remaining intersection case has a marked root: a product of point and line
-- assignment sets cannot separate incident pairs from the one-line negative tests.
theorem PEqualNP.Outside.R_meta_3364_1
  (connectivity : ∀ (Z : Type) (n s o : ℕ) (W : ℕ → Set Z), o < n+s →
    (∀ i < s, ∃ a < n+i, ∃ b < n+i,
      W (n+i) = W a ∪ W b ∨ W (n+i) = W a ∨ W (n+i) = ∅ ∨ W (n+i) = W a ∩ W b) →
    (∀ j < n, ∃ x y : Z, (∀ k < n, k ≠ j → (x ∈ W k ↔ y ∈ W k)) ∧
      x ∈ W o ∧ y ∉ W o) → n ≤ s+1)
  (unionRoot : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    199 ≤ q → N = q^2+q+1 →
    (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (g : ℕ) (E : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let n := N+N
      let o := n+g-1
      let one := fun (p t : Fin N) => decide (t=p)
      let hit := fun j => ∀ p l, I p l → (one p,one l) ∈ W j
      let safe := fun j => ∀ L : Fin N → Bool, Fintype.card {l : Fin N // L l = true} ≤ q →
        (fun p => decide (¬∃ l, I p l ∧ L l = true), L) ∉ W j
      n ≤ g+1 → g < N*(q/100+1) →
      (∀ p : Fin N, W p.val = {z | z.1 p=true} ∧ W (N+p.val) = {z | z.2 p=true}) →
      (∀ i < g, ∃ a b, max a b < n+i ∧
        (W (n+i) ∈ [W a ∪ W b, W a, ∅] ∨
         W (n+i) = W a ∩ W b ∧ (i ∈ E ∨
          ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B))) →
      hit o ∧ safe o → (∀ j < o, ¬(hit j ∧ safe j)) →
      (∃ a b, max a b < o ∧ W o = W a ∪ W b ∧ ¬hit a ∧ ¬hit b) →
      100*E.card < N*q → N*(q+1) ≤ 100*g)
  (interRoot : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    199 ≤ q → N = q^2+q+1 →
    (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (g : ℕ) (E : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let n := N+N
      let o := n+g-1
      let one := fun (p t : Fin N) => decide (t=p)
      let hit := fun j => ∀ p l, I p l → (one p,one l) ∈ W j
      let safe := fun j => ∀ L : Fin N → Bool, Fintype.card {l : Fin N // L l = true} ≤ q →
        (fun p => decide (¬∃ l, I p l ∧ L l = true), L) ∉ W j
      n ≤ g+1 → g < N*(q/100+1) →
      (∀ p : Fin N, W p.val = {z | z.1 p=true} ∧ W (N+p.val) = {z | z.2 p=true}) →
      (∀ i < g, ∃ a b, max a b < n+i ∧
        (W (n+i) ∈ [W a ∪ W b, W a, ∅] ∨
         W (n+i) = W a ∩ W b ∧ (i ∈ E ∨
          ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B))) →
      hit o ∧ safe o → (∀ j < o, ¬(hit j ∧ safe j)) →
      (∃ a b, max a b < o ∧ W o = W a ∩ W b ∧ ¬safe a ∧ ¬safe b) → g-1 ∈ E →
      100*E.card < N*q → N*(q+1) ≤ 100*g)
  : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  have canonical_cover {N q g : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (lineSize : ∀ l, Fintype.card {p : Fin N // I p l} = q + 1)
      (slots : N ≤ g) :
      ∃ A B : Fin g → Finset (Fin N),
        (∀ t, ∀ p ∈ A t, ∀ l ∈ B t, I p l) ∧
        (∀ p l, I p l → ∃ t, p ∈ A t ∧ l ∈ B t) ∧
        ∑ t : Fin g, ((A t).card + (B t).card) = N * (q + 2) := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le slots
    let A : Fin (N+d) → Finset (Fin N) := Fin.addCases
      (fun l : Fin N => Finset.univ.filter (fun p => I p l)) (fun _ : Fin d => ∅)
    let B : Fin (N+d) → Finset (Fin N) := Fin.addCases
      (fun l : Fin N => {l}) (fun _ : Fin d => ∅)
    refine ⟨A,B,?_,?_,?_⟩
    · intro t
      refine Fin.addCases (fun l => ?_) (fun j => ?_) t
      · simp [A,B]
      · simp [A]
    · intro p l inc
      exact ⟨l.castAdd d, by simpa [A] using inc, by simp [B]⟩
    · have cards (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q+1 := by
        rw [← Fintype.card_subtype]
        exact lineSize l
      rw [Fin.sum_univ_add]
      simp [A,B,cards]

  have cover_of_gate_bound {N q g : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hq : 100 < q) (lineSize : ∀ l, Fintype.card {p : Fin N // I p l} = q + 1)
      (gateBound : N * (q+1) ≤ 100 * g) :
      ∃ A B : Fin g → Finset (Fin N),
        (∀ t, ∀ p ∈ A t, ∀ l ∈ B t, I p l) ∧
        (∀ p l, I p l → ∃ t, p ∈ A t ∧ l ∈ B t) ∧
        ∑ t : Fin g, ((A t).card + (B t).card) ≤ 100*g + N := by
    have lim : 100 * N ≤ 100 * g := calc
      100 * N = N * 100 := Nat.mul_comm _ _
      _ ≤ N * (q+1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := gateBound
    have slots : N ≤ g := by omega
    obtain ⟨A,B,pure,covers,weight⟩ := canonical_cover I lineSize slots
    refine ⟨A,B,pure,covers,?_⟩
    rw [weight,show N*(q+2) = N*(q+1)+N by ring]
    omega
  have mono_wire {Z : Type} (n : ℕ) (W : ℕ → Set Z) (s : ℕ) (x y : Z)
      (steps : ∀ i<s, ∃ a<n+i, ∃ b<n+i,
         W (n+i)=W a∪W b ∨ W (n+i)=W a ∨ W (n+i)=∅ ∨ W (n+i)=W a∩W b)
      (base : ∀ j<n, x∈W j → y∈W j) : ∀ j<n+s, x∈W j → y∈W j := by
    induction s with
    | zero => simpa using base
    | succ s ih =>
      intro j hj
      have prev := ih (fun i hi => steps i (by omega))
      by_cases h : j<n+s
      · exact prev j h
      have eq : j=n+s := by omega
      subst j
      obtain ⟨a,ha,b,hb,op⟩ := steps s (by omega)
      rcases op with h|h|h|h
      · rw [h]; exact Or.imp (prev a ha) (prev b hb)
      · rw [h]; exact prev a ha
      · rw [h]; exact id
      · rw [h]; exact And.imp (prev a ha) (prev b hb)
  let oneN {N : ℕ} (p i : Fin N) : Bool := decide (i=p)

  have raw_imp {N : ℕ} (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)))
      (raw : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
      (x y : (Fin N → Bool) × (Fin N → Bool))
      (hp : ∀ p, x.1 p=true → y.1 p=true) (hl : ∀ l, x.2 l=true → y.2 l=true) :
      ∀ j<N+N, x ∈ W j → y ∈ W j := by
    intro j hj
    by_cases h : j<N
    · let p : Fin N := ⟨j,h⟩
      change x ∈ W p.val → y ∈ W p.val
      rw [(raw p).1]
      exact hp p
    · let l : Fin N := ⟨j-N,by omega⟩
      have e : j = N + l.val := by dsimp [l]; omega
      rw [e,(raw l).2]
      exact hl l

  have plane_essential (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hq : 100 < q) (hN : N=q^2+q+1)
      (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (join : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o<N+N+s)
      (raw : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
      (steps : ∀ i<s, ∃ a<N+N+i, ∃ b<N+N+i,
         W (N+N+i)=W a∪W b ∨ W (N+N+i)=W a ∨ W (N+N+i)=∅ ∨ W (N+N+i)=W a∩W b)
      (pos : ∀ p l : Fin N, I p l → (fun r => decide (r=p), fun r => decide (r=l)) ∈ W o)
      (neg : ∀ y : Fin N → Bool, Fintype.card {r : Fin N // y r = true} ≤ q →
        (fun p : Fin N => decide (¬∃ l : Fin N, I p l ∧ y l=true), y) ∉ W o) :
      ∀ j<N+N, ∃ x y : (Fin N → Bool) × (Fin N → Bool),
        (∀ k<N+N, k≠j → (x∈W k ↔ y∈W k)) ∧ x∈W o ∧ y∉W o := by
    classical
    let zero : Fin N → Bool := fun _ => false
    let allowed (z : Fin N → Bool) (p : Fin N) := decide (¬∃ l : Fin N, I p l ∧ z l=true)
    have zeroCard : Fintype.card {l : Fin N // zero l=true} ≤ q := by simp [zero]
    have oneCard (l : Fin N) : Fintype.card {r : Fin N // oneN l r=true} ≤ q := by
      simp [oneN]; omega
    have lineOnly (l : Fin N) : (zero,oneN l) ∉ W o := by
      intro yes
      have imp := raw_imp W raw (zero,oneN l) (allowed (oneN l),oneN l)
        (fun p => by simp [zero]) (fun _ => id)
      exact neg (oneN l) (oneCard l) (mono_wire (N+N) W s _ _ steps imp o ho yes)
    have pointOnly (p : Fin N) : (oneN p,zero) ∉ W o := by
      intro yes
      have imp := raw_imp W raw (oneN p,zero) (allowed zero,zero)
        (fun _ _ => by simp [allowed,zero]) (fun _ => id)
      exact neg zero zeroCard (mono_wire (N+N) W s _ _ steps imp o ho yes)
    intro j hj
    by_cases pt : j<N
    · let p : Fin N := ⟨j,pt⟩
      let : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨r,hr⟩ := exists_ne p
      obtain ⟨l,hit,_⟩ := join p r hr.symm
      refine ⟨(oneN p,oneN l),(zero,oneN l),?_,pos p l hit.1,lineOnly l⟩
      intro k hk kj
      by_cases x : k<N
      · let b : Fin N := ⟨k,x⟩
        have bp : b ≠ p := fun eq => kj (congrArg Fin.val eq)
        change _ ∈ W b.val ↔ _ ∈ W b.val
        rw [(raw b).1]
        simp [oneN,zero,bp]
      · let b : Fin N := ⟨k-N,by omega⟩
        have e : k=N+b.val := by dsimp [b]; omega
        rw [e,(raw b).2]
        rfl
    · let l : Fin N := ⟨j-N,by omega⟩
      have jl : j=N+l.val := by dsimp [l]; omega
      have hpos : 0 < Fintype.card {p : Fin N // I p l} := by rw [degree]; omega
      obtain ⟨p,hp⟩ := Classical.choice (Fintype.card_pos_iff.mp hpos)
      refine ⟨(oneN p,oneN l),(oneN p,zero),?_,pos p l hp,pointOnly p⟩
      intro k hk kj
      by_cases x : k<N
      · let b : Fin N := ⟨k,x⟩
        change _ ∈ W b.val ↔ _ ∈ W b.val
        rw [(raw b).1]
        rfl
      · let b : Fin N := ⟨k-N,by omega⟩
        have e : k=N+b.val := by dsimp [b]; omega
        have bl : b≠l := fun eq => kj (e.trans ((congrArg (fun i : Fin N => N+i.val) eq).trans jl.symm))
        rw [e,(raw b).2]
        simp [oneN,zero,bl]
  have output_not_product (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (hq : 100 < q) (hN : N=q^2+q+1)
      (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
      (join : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o<N+N+s)
      (raw : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
      (steps : ∀ i<s, ∃ a<N+N+i, ∃ b<N+N+i,
         W (N+N+i)=W a∪W b ∨ W (N+N+i)=W a ∨ W (N+N+i)=∅ ∨ W (N+N+i)=W a∩W b)
      (pos : ∀ p l : Fin N, I p l → (fun r => decide (r=p), fun r => decide (r=l)) ∈ W o)
      (neg : ∀ y : Fin N → Bool, Fintype.card {r : Fin N // y r = true} ≤ q →
        (fun p : Fin N => decide (¬∃ l : Fin N, I p l ∧ y l=true), y) ∉ W o) :
      ¬∃ A B, W o = A ×ˢ B := by
    classical
    rintro ⟨A,B,shape⟩
    let l : Fin N := ⟨0,by omega⟩
    have sparse : ¬∀ p, I p l := by
      intro full
      have card := degree l
      rw [Fintype.card_subtype] at card
      simp [full] at card
      nlinarith [Nat.mul_pos (show 0 < q by omega) (show 0 < q by omega)]
    obtain ⟨p,hpl⟩ := Classical.not_forall.mp sparse
    let : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨r,hr⟩ := exists_ne p
    obtain ⟨t,ht,_⟩ := join p r hr.symm
    have nonempty : 0 < Fintype.card {v : Fin N // I v l} := by rw [degree]; omega
    obtain ⟨u,hu⟩ := Classical.choice (Fintype.card_pos_iff.mp nonempty)
    have left : (oneN p,oneN t) ∈ A ×ˢ B := shape ▸ pos p t ht.1
    have right : (oneN u,oneN l) ∈ A ×ˢ B := shape ▸ pos u l hu
    have cross : (oneN p,oneN l) ∈ W o := shape ▸ (show (oneN p,oneN l) ∈ A ×ˢ B from ⟨left.1,right.2⟩)
    let allowed (v : Fin N) := decide (¬∃ e, I v e ∧ oneN l e=true)
    have enlarge : ∀ v, oneN p v=true → allowed v=true := by
      intro v hv
      have eq : v=p := by simpa [oneN] using hv
      subst v
      simp [allowed,oneN,hpl]
    have counts : Fintype.card {v : Fin N // oneN l v=true} ≤ q := by simp [oneN]; omega
    apply neg (oneN l) counts
    exact mono_wire (N+N) W s _ _ steps
      (raw_imp W raw (oneN p,oneN l) (allowed,oneN l) enlarge (fun _ => id)) o ho cross
  intro q N I inst hq hN lineSize plane g o E W hout hraw hgate hpositive hnegative hsparse
  have simple (i : ℕ) (hi : i < g) : ∃ a < N+N+i, ∃ b < N+N+i,
      W (N+N+i) = W a ∪ W b ∨ W (N+N+i) = W a ∨ W (N+N+i) = ∅ ∨
      W (N+N+i) = W a ∩ W b := by
    obtain ⟨a,ha,b,hb,op⟩ := hgate i hi
    refine ⟨a,ha,b,hb,?_⟩
    rcases op with un | cp | empty | ⟨andOp,_⟩
    · exact Or.inl un
    · exact Or.inr (Or.inl cp)
    · exact Or.inr (Or.inr (Or.inl empty))
    · exact Or.inr (Or.inr (Or.inr andOp))
  classical
  let hit (w : ℕ) := ∀ p l, I p l → (oneN p,oneN l) ∈ W w
  let safe (w : ℕ) := ∀ L : Fin N → Bool, Fintype.card {l : Fin N // L l = true} ≤ q →
    (fun p => decide (¬∃ l, I p l ∧ L l=true), L) ∉ W w
  have existsSep : ∃ w, hit w ∧ safe w := ⟨o,hpositive,hnegative⟩
  let r := Nat.find existsSep
  have ok : hit r ∧ safe r := Nat.find_spec existsSep
  have early : r ≤ o := Nat.find_min' existsSep ⟨hpositive,hnegative⟩
  have first (j : ℕ) (hj : j < r) : ¬(hit j ∧ safe j) := Nat.find_min existsSep hj
  have essentialAt := plane_essential q N I hq hN lineSize plane g r W
    (by omega) hraw simple ok.1 ok.2
  have internal : N+N ≤ r := by
    by_contra! before
    have bound := connectivity _ (N+N) 0 r W (by omega) (by simp) essentialAt
    omega
  let s := r + 1 - (N+N)
  have smaller : s ≤ g := by dsimp [s]; omega
  have last : N+N+s-1 = r := by dsimp [s]; omega
  have lastStep : N+N+(s-1) = r := by dsimp [s]; omega
  have fanin := connectivity _ (N+N) s r W (by omega)
    (fun i hi => simple i (hi.trans_le smaller)) essentialAt
  have sizeBound : N*(q+1) ≤ 100*s := by
    by_cases high : 199 ≤ q
    · by_cases window : s < N*(q/100+1)
      · have gates (i : ℕ) (hi : i < s) : ∃ a b, max a b < N+N+i ∧
            (W (N+N+i) ∈ [W a ∪ W b, W a, ∅] ∨
             W (N+N+i) = W a ∩ W b ∧ (i ∈ E ∨
               ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B)) := by
          obtain ⟨a,ha,b,hb,op⟩ := hgate i (hi.trans_le smaller)
          refine ⟨a,b,max_lt ha hb,?_⟩
          rcases op with un | cp | empty | both
          · exact Or.inl (by simp [un])
          · exact Or.inl (by simp [cp])
          · exact Or.inl (by simp [empty])
          · exact Or.inr both
        have lastOK : hit (N+N+s-1) ∧ safe (N+N+s-1) := by simpa only [last] using ok
        have earlier : ∀ j < N+N+s-1, ¬(hit j ∧ safe j) := by simpa only [last] using first
        obtain ⟨a,ha,b,hb,op⟩ := hgate (s-1) (by dsimp [s] at *; omega)
        rw [lastStep] at ha hb op
        rcases op with un | cp | empty | ⟨inter,markedOrPure⟩
        · have sa : safe a := fun L h x => ok.2 L h (un ▸ Or.inl x)
          have sb : safe b := fun L h x => ok.2 L h (un ▸ Or.inr x)
          apply unionRoot q N I high hN lineSize plane s E W fanin window hraw gates
            lastOK earlier _ hsparse
          exact ⟨a,b,last ▸ max_lt ha hb,last ▸ un,
            (fun yes => first a ha ⟨yes,sa⟩),(fun yes => first b hb ⟨yes,sb⟩)⟩
        · have ready : hit a ∧ safe a := by simpa only [hit,safe,cp] using ok
          exact (first a ha ready).elim
        · obtain ⟨x,y,_,yes,_⟩ := essentialAt 0 (by omega)
          simp only [empty,Set.mem_empty_iff_false] at yes
        · have pa : hit a := fun p l hp => (inter ▸ ok.1 p l hp : _ ∈ W a ∩ W b).1
          have pb : hit b := fun p l hp => (inter ▸ ok.1 p l hp : _ ∈ W a ∩ W b).2
          have marked : s-1 ∈ E := by
            rcases markedOrPure with marked | ⟨A,B,wa,wb⟩
            · exact marked
            · have forbid := output_not_product q N I hq hN lineSize plane g r W
                (by omega) hraw simple ok.1 ok.2
              apply False.elim (forbid ⟨A,B,?_⟩)
              rw [inter,wa,wb]
              ext z
              simp
          apply interRoot q N I high hN lineSize plane s E W fanin window hraw gates
            lastOK earlier _ marked hsparse
          exact ⟨a,b,last ▸ max_lt ha hb,last ▸ inter,
            (fun yes => first a ha ⟨pa,yes⟩),(fun yes => first b hb ⟨pb,yes⟩)⟩
      · calc
          N*(q+1) ≤ N*(100*(q/100+1)) := Nat.mul_le_mul_left _ (by omega)
          _ = 100*(N*(q/100+1)) := by ring
          _ ≤ 100*s := Nat.mul_le_mul_left _ (by omega)
    · calc
        N*(q+1) ≤ N*199 := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 100*s := by omega
  exact cover_of_gate_bound I hq lineSize (sizeBound.trans (Nat.mul_le_mul_left 100 smaller))
