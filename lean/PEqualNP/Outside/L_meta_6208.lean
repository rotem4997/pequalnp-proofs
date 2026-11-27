import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6208

open PEqualNP.HeptadCover

def fibP (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) : Finset (Fin 13 × Fin 13) :=
  X.filter (fun x => x.1 = P)

def tgtP (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun Q => ∀ x ∈ fibP X P, Q ∈ singerLines3 x.2)

def suppP (X : Finset (Fin 13 × Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun P => (fibP X P).Nonempty)

lemma g_nine : ∀ P : Fin 13,
    (Finset.univ.filter (fun l : Fin 13 => P ∉ singerLines3 l)).card ≤ 9 := by
  decide

lemma g_three : ∀ P Q : Fin 13,
    (Finset.univ.filter (fun l : Fin 13 => P ∉ singerLines3 l ∧ Q ∈ singerLines3 l)).card ≤ 3 := by
  decide

lemma g_one : ∀ Q1 Q2 : Fin 13, Q1 ≠ Q2 →
    (Finset.univ.filter (fun l : Fin 13 => Q1 ∈ singerLines3 l ∧ Q2 ∈ singerLines3 l)).card ≤ 1 := by
  decide

lemma g_four : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide

lemma g_line : ∀ Q1 Q2 : Fin 13, ∃ h : Fin 13, Q1 ∈ singerLines3 h ∧ Q2 ∈ singerLines3 h := by
  decide

lemma mem_fibP {X : Finset (Fin 13 × Fin 13)} {P : Fin 13} {x : Fin 13 × Fin 13} :
    x ∈ fibP X P ↔ x ∈ X ∧ x.1 = P := by
  unfold fibP; exact Finset.mem_filter

lemma mem_tgtP {X : Finset (Fin 13 × Fin 13)} {P Q : Fin 13} :
    Q ∈ tgtP X P ↔ ∀ x ∈ fibP X P, Q ∈ singerLines3 x.2 := by
  unfold tgtP; simp

lemma mem_suppP {X : Finset (Fin 13 × Fin 13)} {P : Fin 13} :
    P ∈ suppP X ↔ (fibP X P).Nonempty := by
  unfold suppP; simp

lemma fib_card_le (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) (p : Fin 13 → Prop) [DecidablePred p]
    (h : ∀ x ∈ fibP X P, p x.2) :
    (fibP X P).card ≤ (Finset.univ.filter p).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_coe.mp hx)⟩)
  · intro x hx y hy hxy
    have hx' := (mem_fibP.mp (Finset.mem_coe.mp hx)).2
    have hy' := (mem_fibP.mp (Finset.mem_coe.mp hy)).2
    exact Prod.ext (hx'.trans hy'.symm) hxy

lemma w_le9 (X : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2) (P : Fin 13) :
    (fibP X P).card ≤ 9 := by
  refine le_trans (fib_card_le X P (fun l => P ∉ singerLines3 l) ?_) (g_nine P)
  intro x hx
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  have := hX x hxX
  rw [hx1] at this
  exact this

lemma w_le3 (X : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2) (P Q : Fin 13)
    (hQ : Q ∈ tgtP X P) : (fibP X P).card ≤ 3 := by
  refine le_trans (fib_card_le X P (fun l => P ∉ singerLines3 l ∧ Q ∈ singerLines3 l) ?_) (g_three P Q)
  intro x hx
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  have := hX x hxX
  rw [hx1] at this
  exact ⟨this, mem_tgtP.mp hQ x hx⟩

lemma w_le1 (X : Finset (Fin 13 × Fin 13)) (P Q1 Q2 : Fin 13) (h1 : Q1 ∈ tgtP X P)
    (h2 : Q2 ∈ tgtP X P) (hne : Q1 ≠ Q2) : (fibP X P).card ≤ 1 := by
  refine le_trans (fib_card_le X P (fun l => Q1 ∈ singerLines3 l ∧ Q2 ∈ singerLines3 l) ?_)
    (g_one Q1 Q2 hne)
  intro x hx
  exact ⟨mem_tgtP.mp h1 x hx, mem_tgtP.mp h2 x hx⟩

lemma tgt_sub (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) (x : Fin 13 × Fin 13)
    (hx : x ∈ fibP X P) : tgtP X P ⊆ singerLines3 x.2 := by
  intro Q hQ; exact mem_tgtP.mp hQ x hx

lemma tgt_card (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) (hP : P ∈ suppP X) :
    (tgtP X P).card ≤ 4 := by
  obtain ⟨x, hx⟩ := mem_suppP.mp hP
  have := Finset.card_le_card (tgt_sub X P x hx)
  rw [g_four] at this; exact this

lemma line_unique (Q1 Q2 l l' : Fin 13) (hne : Q1 ≠ Q2) (h1 : Q1 ∈ singerLines3 l)
    (h2 : Q2 ∈ singerLines3 l) (h1' : Q1 ∈ singerLines3 l') (h2' : Q2 ∈ singerLines3 l') :
    l = l' := by
  have := Finset.card_le_one.mp (g_one Q1 Q2 hne)
  exact this l (by simp [h1, h2]) l' (by simp [h1', h2'])

lemma cross (X Y : Finset (Fin 13 × Fin 13))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2)
    (P Q : Fin 13) : Q ∈ tgtP X P ∨ P ∈ tgtP Y Q := by
  by_contra hcon
  rw [not_or, mem_tgtP, mem_tgtP] at hcon
  obtain ⟨h1, h2⟩ := hcon
  push_neg at h1 h2
  obtain ⟨x, hx, hxQ⟩ := h1
  obtain ⟨y, hy, hyP⟩ := h2
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  obtain ⟨hyY, hy1⟩ := mem_fibP.mp hy
  rcases hXY x hxX y hyY with h | h
  · rw [hx1] at h; exact hyP h
  · rw [hy1] at h; exact hxQ h

lemma not_self (X : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2) (P : Fin 13)
    (hP : P ∈ suppP X) : P ∉ tgtP X P := by
  intro h
  obtain ⟨x, hx⟩ := mem_suppP.mp hP
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  have h1 := mem_tgtP.mp h x hx
  have h2 := hX x hxX
  rw [hx1] at h2
  exact h2 h1

lemma card_supp_add (X Y : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2)
    (hY : ∀ x ∈ Y, x.1 ∉ singerLines3 x.2)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2) :
    (suppP X).card + (suppP Y).card ≤ 13 := by
  have hd : Disjoint (suppP X) (suppP Y) := by
    rw [Finset.disjoint_left]
    intro P hPX hPY
    rcases cross X Y hXY P P with h | h
    · exact not_self X hX P hPX h
    · exact not_self Y hY P hPY h
  rw [← Finset.card_union_of_disjoint hd]
  exact le_trans (Finset.card_le_univ _) (by simp)

lemma card_eq_sum (X : Finset (Fin 13 × Fin 13)) :
    X.card = ∑ P ∈ suppP X, (fibP X P).card := by
  have H : ((X : Set (Fin 13 × Fin 13))).MapsTo Prod.fst (suppP X) := by
    intro x hx
    rw [Finset.mem_coe, mem_suppP]
    exact ⟨x, mem_fibP.mpr ⟨Finset.mem_coe.mp hx, rfl⟩⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  rfl

lemma aimed_bound (X Y : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2)
    (P : Fin 13) (hP : P ∈ suppP X) (hT : (tgtP X P).Nonempty) :
    2 * ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card + 3 * (fibP X P).card ≤ 11 := by
  obtain ⟨Q0, hQ0⟩ := hT
  have hw3 := w_le3 X hX P Q0 hQ0
  have hsub : (suppP Y).filter (fun Q => Q ∈ tgtP X P) ⊆ tgtP X P := by
    intro Q hQ; exact (Finset.mem_filter.mp hQ).2
  have ha4 : ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card ≤ 4 :=
    le_trans (Finset.card_le_card hsub) (tgt_card X P hP)
  by_cases h2 : 1 < ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    have hw1 := w_le1 X P a b (hsub ha) (hsub hb) hab
    omega
  · omega

lemma edge_count (X Y : Finset (Fin 13 × Fin 13))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2) :
    (suppP X).card * (suppP Y).card ≤
      ∑ P ∈ suppP X, ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card
      + ∑ Q ∈ suppP Y, ((suppP X).filter (fun P => P ∈ tgtP Y Q)).card := by
  have h1 : ∑ P ∈ suppP X, ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card
      = ((suppP X ×ˢ suppP Y).filter (fun pq => pq.2 ∈ tgtP X pq.1)).card := by
    simp only [Finset.card_filter, Finset.sum_product]
  have h2 : ∑ Q ∈ suppP Y, ((suppP X).filter (fun P => P ∈ tgtP Y Q)).card
      = ((suppP X ×ˢ suppP Y).filter (fun pq => pq.1 ∈ tgtP Y pq.2)).card := by
    simp only [Finset.card_filter, Finset.sum_product_right]
  rw [h1, h2, ← Finset.card_product]
  calc (suppP X ×ˢ suppP Y).card
      ≤ ((suppP X ×ˢ suppP Y).filter (fun pq => pq.2 ∈ tgtP X pq.1) ∪
          (suppP X ×ˢ suppP Y).filter (fun pq => pq.1 ∈ tgtP Y pq.2)).card := by
        apply Finset.card_le_card
        intro pq hpq
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases cross X Y hXY pq.1 pq.2 with h | h
        · exact Or.inl ⟨hpq, h⟩
        · exact Or.inr ⟨hpq, h⟩
    _ ≤ _ := Finset.card_union_le _ _

lemma aimed (A B : Finset (Fin 13 × Fin 13)) (hA : ∀ x ∈ A, x.1 ∉ singerLines3 x.2)
    (hB : ∀ x ∈ B, x.1 ∉ singerLines3 x.2)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2)
    (hA13 : 13 ≤ A.card) (hB13 : 13 ≤ B.card)
    (hTA : ∀ P ∈ suppP A, (tgtP A P).Nonempty) (hTB : ∀ Q ∈ suppP B, (tgtP B Q).Nonempty) :
    False := by
  have hs := card_supp_add A B hA hB hAB
  have he := edge_count A B hAB
  have sA : 2 * ∑ P ∈ suppP A, ((suppP B).filter (fun Q => Q ∈ tgtP A P)).card + 3 * A.card
      ≤ 11 * (suppP A).card := by
    rw [card_eq_sum A, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ P ∈ suppP A, 11 :=
          Finset.sum_le_sum (fun P hP => aimed_bound A B hA P hP (hTA P hP))
      _ = 11 * (suppP A).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have sB : 2 * ∑ Q ∈ suppP B, ((suppP A).filter (fun P => P ∈ tgtP B Q)).card + 3 * B.card
      ≤ 11 * (suppP B).card := by
    rw [card_eq_sum B, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ Q ∈ suppP B, 11 :=
          Finset.sum_le_sum (fun Q hQ => aimed_bound B A hB Q hQ (hTB Q hQ))
      _ = 11 * (suppP B).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have wA : A.card ≤ 3 * (suppP A).card := by
    rw [card_eq_sum A]
    calc _ ≤ ∑ P ∈ suppP A, 3 := Finset.sum_le_sum (fun P hP => by
          obtain ⟨Q, hQ⟩ := hTA P hP
          exact w_le3 A hA P Q hQ)
      _ = 3 * (suppP A).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have wB : B.card ≤ 3 * (suppP B).card := by
    rw [card_eq_sum B]
    calc _ ≤ ∑ Q ∈ suppP B, 3 := Finset.sum_le_sum (fun Q hQ => by
          obtain ⟨P, hP⟩ := hTB Q hQ
          exact w_le3 B hB Q P hP)
      _ = 3 * (suppP B).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨u, hu⟩ : ∃ u, (suppP A).card = 5 + u := ⟨(suppP A).card - 5, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, (suppP B).card = 5 + v := ⟨(suppP B).card - 5, by omega⟩
  rw [hu, hv] at he
  rw [hu] at sA
  rw [hv] at sB
  rw [hu, hv] at hs
  nlinarith [Nat.zero_le (u * v)]

lemma unaimed (X Y : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2)
    (hY : ∀ x ∈ Y, x.1 ∉ singerLines3 x.2)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2)
    (hX13 : 13 ≤ X.card) (hY13 : 13 ≤ Y.card)
    (P0 : Fin 13) (hP0 : P0 ∈ suppP X) (hT0 : tgtP X P0 = ∅) : False := by
  have hs := card_supp_add X Y hX hY hXY
  have hall : ∀ Q, P0 ∈ tgtP Y Q := by
    intro Q
    rcases cross X Y hXY P0 Q with h | h
    · rw [hT0] at h; simp at h
    · exact h
  have wY3 : ∀ Q, (fibP Y Q).card ≤ 3 := fun Q => w_le3 Y hY Q P0 (hall Q)
  have hYsum := card_eq_sum Y
  have hXsplit : X.card = (fibP X P0).card + ∑ P ∈ (suppP X).erase P0, (fibP X P).card := by
    rw [card_eq_sum X, Finset.add_sum_erase (suppP X) (fun P => (fibP X P).card) hP0]
  have hw0 := w_le9 X hX P0
  have hce : ((suppP X).erase P0).card = (suppP X).card - 1 := Finset.card_erase_of_mem hP0
  have hcpos : 1 ≤ (suppP X).card := Finset.card_pos.mpr ⟨P0, hP0⟩
  have hYb : Y.card ≤ (suppP Y).card + 2 * ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card := by
    rw [hYsum]
    calc ∑ Q ∈ suppP Y, (fibP Y Q).card
        ≤ ∑ Q ∈ suppP Y, (1 + 2 * (if 2 ≤ (fibP Y Q).card then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro Q _
          have := wY3 Q
          split_ifs with h <;> omega
      _ = (suppP Y).card + 2 * ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.card_filter]
          simp
  by_cases hH : ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card ≤ 1
  · have hsX : (suppP X).card ≤ 2 := by omega
    have hex : ∃ P1 ∈ (suppP X).erase P0, 4 ≤ (fibP X P1).card := by
      by_contra hno
      push_neg at hno
      have : ∑ P ∈ (suppP X).erase P0, (fibP X P).card ≤ ∑ P ∈ (suppP X).erase P0, 3 :=
        Finset.sum_le_sum (fun P hP => by have := hno P hP; omega)
      rw [Finset.sum_const, smul_eq_mul] at this
      omega
    obtain ⟨P1, hP1e, hP1w⟩ := hex
    obtain ⟨hne, hP1⟩ := Finset.mem_erase.mp hP1e
    have hce1 : 1 ≤ ((suppP X).erase P0).card := Finset.card_pos.mpr ⟨P1, hP1e⟩
    have hall1 : ∀ Q, P1 ∈ tgtP Y Q := by
      intro Q
      rcases cross X Y hXY P1 Q with h | h
      · have := w_le3 X hX P1 Q h; omega
      · exact h
    have hY1 : Y.card ≤ (suppP Y).card := by
      rw [hYsum]
      calc _ ≤ ∑ Q ∈ suppP Y, 1 := Finset.sum_le_sum (fun Q _ => w_le1 Y Q P0 P1 (hall Q) (hall1 Q)
              (Ne.symm hne))
        _ = (suppP Y).card := by simp
    omega
  · have h2 : 1 < ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card := by omega
    obtain ⟨Q1, hQ1, Q2, hQ2, hQ12⟩ := Finset.one_lt_card.mp h2
    have hQ1' := Finset.mem_filter.mp hQ1
    have hQ2' := Finset.mem_filter.mp hQ2
    have honly : ∀ Q ∈ (suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card), ∀ P, P ∈ tgtP Y Q → P = P0 := by
      intro Q hQ P hP
      by_contra hPne
      have := w_le1 Y Q P0 P (hall Q) hP (Ne.symm hPne)
      have := (Finset.mem_filter.mp hQ).2
      omega
    have haim : ∀ P ∈ (suppP X).erase P0, Q1 ∈ tgtP X P ∧ Q2 ∈ tgtP X P := by
      intro P hP
      obtain ⟨hne, _⟩ := Finset.mem_erase.mp hP
      constructor
      · rcases cross X Y hXY P Q1 with h | h
        · exact h
        · exact absurd (honly Q1 hQ1 P h) hne
      · rcases cross X Y hXY P Q2 with h | h
        · exact h
        · exact absurd (honly Q2 hQ2 P h) hne
    have hsum1 : ∑ P ∈ (suppP X).erase P0, (fibP X P).card ≤ ((suppP X).erase P0).card := by
      calc _ ≤ ∑ P ∈ (suppP X).erase P0, 1 := Finset.sum_le_sum (fun P hP =>
              w_le1 X P Q1 Q2 (haim P hP).1 (haim P hP).2 hQ12)
        _ = _ := by simp
    have hs5 : 5 ≤ (suppP X).card := by omega
    obtain ⟨h, hh1, hh2⟩ := g_line Q1 Q2
    have hsubh : ∀ P ∈ (suppP X).erase P0, tgtP X P ⊆ singerLines3 h := by
      intro P hP
      obtain ⟨_, hPS⟩ := Finset.mem_erase.mp hP
      obtain ⟨x, hx⟩ := mem_suppP.mp hPS
      have e1 := mem_tgtP.mp (haim P hP).1 x hx
      have e2 := mem_tgtP.mp (haim P hP).2 x hx
      have hxh : x.2 = h := line_unique Q1 Q2 x.2 h hQ12 e1 e2 hh1 hh2
      rw [← hxh]
      exact tgt_sub X P x hx
    have hYh : suppP Y ⊆ singerLines3 h := by
      intro Q hQ
      by_contra hQh
      have hsub : suppP X ⊆ tgtP Y Q := by
        intro P hP
        by_cases hPe : P = P0
        · rw [hPe]; exact hall Q
        · rcases cross X Y hXY P Q with hc | hc
          · exact absurd (hsubh P (Finset.mem_erase.mpr ⟨hPe, hP⟩) hc) hQh
          · exact hc
      have := le_trans (Finset.card_le_card hsub) (tgt_card Y Q hQ)
      omega
    have hsY : (suppP Y).card ≤ 4 := by
      have := Finset.card_le_card hYh
      rw [g_four] at this; exact this
    have hY3 : Y.card ≤ 3 * (suppP Y).card := by
      rw [hYsum]
      calc _ ≤ ∑ Q ∈ suppP Y, 3 := Finset.sum_le_sum (fun Q _ => wY3 Q)
        _ = 3 * (suppP Y).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega

end PEqualNP.Outside.L_meta_6208

theorem PEqualNP.Outside.L_meta_6208 : ∀ (x1 x2 : Finset (Fin (13 : ℕ) × Fin (13 : ℕ))), (∀ x3 ∈ x1 ∪ x2, x3.1 ∉ PEqualNP.HeptadCover.singerLines3 x3.2) → (∀ x4 ∈ x1, ∀ x6 ∈ x2, x4.1 ∈ PEqualNP.HeptadCover.singerLines3 x6.2 ∨ x6.1 ∈ PEqualNP.HeptadCover.singerLines3 x4.2) → x1.card ≤ (12 : ℕ) ∨ x2.card ≤ (12 : ℕ) := by
  intro A B hU hAB
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA13, hB13⟩ := hcon
  have hA : ∀ x ∈ A, x.1 ∉ PEqualNP.HeptadCover.singerLines3 x.2 :=
    fun x hx => hU x (Finset.mem_union_left _ hx)
  have hB : ∀ x ∈ B, x.1 ∉ PEqualNP.HeptadCover.singerLines3 x.2 :=
    fun x hx => hU x (Finset.mem_union_right _ hx)
  have hBA : ∀ y ∈ B, ∀ x ∈ A, y.1 ∈ PEqualNP.HeptadCover.singerLines3 x.2 ∨
      x.1 ∈ PEqualNP.HeptadCover.singerLines3 y.2 :=
    fun y hy x hx => (hAB x hx y hy).symm
  by_cases h1 : ∃ P ∈ PEqualNP.Outside.L_meta_6208.suppP A, PEqualNP.Outside.L_meta_6208.tgtP A P = ∅
  · obtain ⟨P, hP, hT⟩ := h1
    exact PEqualNP.Outside.L_meta_6208.unaimed A B hA hB hAB (by omega) (by omega) P hP hT
  by_cases h2 : ∃ Q ∈ PEqualNP.Outside.L_meta_6208.suppP B, PEqualNP.Outside.L_meta_6208.tgtP B Q = ∅
  · obtain ⟨Q, hQ, hT⟩ := h2
    exact PEqualNP.Outside.L_meta_6208.unaimed B A hB hA hBA (by omega) (by omega) Q hQ hT
  push_neg at h1 h2
  exact PEqualNP.Outside.L_meta_6208.aimed A B hA hB hAB (by omega) (by omega)
    (fun P hP => h1 P hP)
    (fun Q hQ => h2 Q hQ)
