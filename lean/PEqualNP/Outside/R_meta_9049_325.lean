import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_9049_325
    (centers : let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      let U := Ustar G C
      let A := (tops G C \ centreless G C).card
      ∃ P L : Finset (Fin 13), 26 ≤ A + P.card + L.card ∧
        (∀ p ∈ P, ∀ l ∈ L, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
          s(Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ U))
    (service : let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size ≤ 63 →
      2 ≤ (junk G C).card →
      let U := Ustar G C
      let H := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let A := (tops G C \ centreless G C).card
      U.card ≤ H + (A-13))
    (boundary : let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size ≤ 63 →
      2 ≤ (junk G C).card →
      let U := Ustar G C
      let H := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let A := (tops G C \ centreless G C).card
      ∀ P L : Finset (Fin 13),
        (∀ p ∈ P, ∀ l ∈ L, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
          s(Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ U) →
        A + P.card + L.card = 26 → 13 < P.card + L.card → (P.card ≤ 2 ∨ L.card ≤ 2) →
        P.card + L.card + U.card ≤ 13 + H)
    (interior : let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
        u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → C.size ≤ 63 →
      2 ≤ (junk G C).card →
      let U := Ustar G C
      let H := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let A := (tops G C \ centreless G C).card
      ∀ P L : Finset (Fin 13),
        (∀ p ∈ P, ∀ l ∈ L, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
          s(Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ U) →
        A + P.card + L.card = 26 → 13 < P.card + L.card → 3 ≤ P.card → 3 ≤ L.card → 8 ≤ U.card →
        P.card + L.card + U.card ≤ 13 + H)
    : (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [_x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → x3.size ≤ (63 : ℕ) → (13 : ℕ) + (PEqualNP.TopForm.Ustar x1 x3).card ≤ (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) := by
  have spread (P L : Finset (Fin 13)) (bad : Finset (Sym2 (Fin 26)))
      (hp : 3 ≤ P.card) (hl : 3 ≤ L.card) (defect : 13 < P.card + L.card)
      (inc : ∀ p ∈ P, ∀ l ∈ L, (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ) →
        s(Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ bad) : 8 ≤ bad.card := by
    have uniqueLine : ∀ p q l m : Fin 13, p ≠ q →
        (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) → (q.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) → (p.val+m.val)%13 ∈ ([0,1,3,9] : List ℕ) → (q.val+m.val)%13 ∈ ([0,1,3,9] : List ℕ) → l = m := by
      have key : ∀ a ∈ ([0,1,3,9] : List ℕ), ∀ b ∈ ([0,1,3,9] : List ℕ),
        ∀ c ∈ ([0,1,3,9] : List ℕ), ∀ d ∈ ([0,1,3,9] : List ℕ),
          a≠b → (a+13-b)%13=(c+13-d)%13 → a=c := by decide +kernel
      intro p q l m h h₁ h₂ h₃ h₄
      have values : p.val ≠ q.val := fun eq => h (Fin.ext eq)
      have nz : (p.val+l.val)%13 ≠ (q.val+l.val)%13 := by omega
      have eq : (((p.val+l.val)%13)+13-((q.val+l.val)%13))%13 =
          (((p.val+m.val)%13)+13-((q.val+m.val)%13))%13 := by omega
      have same := key _ h₁ _ h₂ _ h₃ _ h₄ nz eq
      apply Fin.ext
      omega
    let adj (p l : Fin 13) : Prop := (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
    let relDec (p l : Fin 13) : Decidable (adj p l) := inferInstanceAs (Decidable ((p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)))
    let nb (S : Finset (Fin 13)) (l : Fin 13) := S.filter fun p => adj p l
    let count (P L : Finset (Fin 13)) := ∑ l ∈ L, (nb P l).card
    have comm (P L : Finset (Fin 13)) : count P L = count L P := by
      simp only [count,nb,Finset.card_filter]
      rw [Finset.sum_comm]
      simp [adj, Nat.add_comm]
    have four : ∀ p : Fin 13, (nb Finset.univ p).card = 4 := by decide +kernel

    have moment (P T : Finset (Fin 13)) :
        4 * count P T ≤ 6 * T.card + P.card * (P.card-1) := by
      let pairs (l : Fin 13) := (nb P l).offDiag
      have sub : ∀ l, nb P l ⊆ P := fun _ => Finset.filter_subset _ _
      have pairBound := Finset.card_le_card_of_injOn (s := T.sigma pairs) (t := P.offDiag)
          (fun z => z.2)
          (by
            intro z hz
            obtain ⟨_,h⟩ := Finset.mem_sigma.mp hz
            obtain ⟨a,b,c⟩ := Finset.mem_offDiag.mp h
            exact Finset.mem_offDiag.mpr ⟨sub _ a,sub _ b,c⟩)
          (by
            rintro ⟨l,x⟩ hl ⟨m,y⟩ hm eq
            change x = y at eq
            subst y
            obtain ⟨_,a⟩ := Finset.mem_sigma.mp hl
            obtain ⟨_,b⟩ := Finset.mem_sigma.mp hm
            obtain ⟨u,v,hne⟩ := Finset.mem_offDiag.mp a
            obtain ⟨w,z,_⟩ := Finset.mem_offDiag.mp b
            have h := uniqueLine x.1 x.2 l m hne (Finset.mem_filter.mp u).2
              (Finset.mem_filter.mp v).2 (Finset.mem_filter.mp w).2 (Finset.mem_filter.mp z).2
            subst m
            rfl)
      rw [Finset.card_sigma, Finset.offDiag_card] at pairBound
      have piece (l : Fin 13) : 4*(nb P l).card ≤ 6+(pairs l).card := by
        simp only [pairs,Finset.offDiag_card]
        have hc : (nb P l).card ≤ 13 := by simpa using Finset.card_le_univ (nb P l)
        generalize (nb P l).card = k at hc ⊢
        interval_cases k <;> decide
      have res := Finset.sum_le_sum (fun l (_ : l ∈ T) => piece l)
      rw [←Finset.mul_sum, Finset.sum_add_distrib] at res
      simp only [Finset.sum_const,smul_eq_mul] at res
      change 4 * (∑ l ∈ T, (nb P l).card) ≤ 6*T.card + P.card * (P.card-1)
      rw [Nat.mul_comm 6 T.card, Nat.mul_sub, Nat.mul_one]
      omega
    have rectangleLower (P L : Finset (Fin 13)) (hp : 3 ≤ P.card) (hl : 3 ≤ L.card)
        (hpl : 13 < P.card + L.card) : 8 ≤ count P L := by
      have total (S : Finset (Fin 13)) : count S Finset.univ = 4*S.card := by
        rw [comm]
        simp only [count, four, Finset.sum_const, smul_eq_mul]
        omega
      have split (S T : Finset (Fin 13)) : count S T + count S Tᶜ = 4*S.card := by
        simpa only [count, Finset.sum_add_sum_compl] using total S
      have oneSide (S T : Finset (Fin 13)) (low : count S T ≤ 7) :
          4*(4*S.card-7) ≤ 6*(13-T.card)+S.card*(S.card-1) := by
        have part := split S T
        have upper := moment S Tᶜ
        simp only [Finset.card_compl, Fintype.card_fin] at upper
        omega
      have finite : ∀ p l : Fin 14, 3 ≤ p.val → 3 ≤ l.val → 13 < p.val+l.val →
          4*(4*p.val-7) ≤ 6*(13-l.val)+p.val*(p.val-1) →
          4*(4*l.val-7) ≤ 6*(13-p.val)+l.val*(l.val-1) → False := by decide +kernel
      have small (S : Finset (Fin 13)) : S.card < 14 := by
        have bound : S.card ≤ 13 := by simpa using Finset.card_le_univ S
        omega
      by_contra! no
      exact finite ⟨_,small P⟩ ⟨_,small L⟩ hp hl hpl (oneSide P L (by omega))
        (oneSide L P (by rw [comm]; omega))
    have lower := rectangleLower P L hp hl defect
    let label (x : (l : Fin 13) × Fin 13) : Sym2 (Fin 26) :=
      s(Fin.castAdd 13 x.2, Fin.natAdd 13 x.1)
    have pairInj : Function.Injective label := by
      rintro ⟨l,p⟩ ⟨m,q⟩ h
      change s(Fin.castAdd 13 p,Fin.natAdd 13 l) = s(Fin.castAdd 13 q,Fin.natAdd 13 m) at h
      rcases Sym2.eq_iff.mp h with ⟨a,b⟩ | ⟨a,_⟩
      · have hpq : p = q := Fin.ext (congrArg (fun z : Fin 26 => z.val) a)
        have hlm : l = m := Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin 26 => z.val) b))
        subst q
        subst m
        rfl
      · have badEq := congrArg (fun z : Fin 26 => z.val) a
        change p.val = 13 + m.val at badEq
        omega
    have upper := Finset.card_le_card_of_injOn (s := L.sigma (nb P)) (t := bad) label
      (by
        intro z hz
        obtain ⟨l,p⟩ := z
        obtain ⟨hL,hN⟩ := Finset.mem_sigma.mp hz
        obtain ⟨hP,hAdj⟩ := Finset.mem_filter.mp hN
        exact inc p hP l hL hAdj) pairInj.injOn
    rw [Finset.card_sigma] at upper
    exact lower.trans upper
  let G₀ := SimpleGraph.fromRel (fun u v : Fin 26 =>
    u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
  let dec : DecidableRel G₀.Adj := inferInstanceAs (DecidableRel
    (SimpleGraph.fromRel (fun u v : Fin 26 =>
      u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ))).Adj)
  intro G inst C hg least top junkCount small
  subst G
  have eqInst : inst = dec := Subsingleton.elim _ _
  subst inst
  let U := Ustar G₀ C
  let A := (tops G₀ C \ centreless G₀ C).card
  let H := 2 * (centreless G₀ C).card + (junk G₀ C).card + (orN G₀ C \ lam G₀ C).card
  suffices b : 13 + U.card ≤ A + H by
    change 13 + U.card ≤ A + 2 * (centreless G₀ C).card + (junk G₀ C).card +
      (orN G₀ C \ lam G₀ C).card
    dsimp only [H] at b
    omega
  have basic : U.card ≤ H + (A-13) := service C least top small junkCount
  by_cases enough : 13 ≤ A
  · omega
  obtain ⟨P,L,count,inside⟩ := centers C least top
  change 26 ≤ A + P.card + L.card at count
  have pointBound : P.card ≤ 13 := by simpa using Finset.card_le_univ P
  obtain ⟨L',sub,cardL⟩ := Finset.exists_subset_card_eq (s := L)
    (show 26 - A - P.card ≤ L.card by omega)
  have normalized : A + P.card + L'.card = 26 := by omega
  have deficient : 13 < P.card + L'.card := by omega
  have inherited : ∀ p ∈ P, ∀ l ∈ L', (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) →
      s(Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ U :=
    fun p hp l hl => inside p hp l (sub hl)
  have reserve : P.card + L'.card + U.card ≤ 13 + H := by
    by_cases corner : P.card ≤ 2 ∨ L'.card ≤ 2
    · exact boundary C least top small junkCount P L' inherited normalized deficient corner
    · have hp : 3 ≤ P.card := by omega
      have hl : 3 ≤ L'.card := by omega
      exact interior C least top small junkCount P L' inherited normalized deficient hp hl
        (spread P L' U hp hl deficient inherited)
  omega
