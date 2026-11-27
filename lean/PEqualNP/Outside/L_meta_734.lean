import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_734_aux

theorem small_color {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Colorable 2)
    (T : Set (Fin n)) [DecidablePred (· ∈ T)] (hT : T.ncard ≤ 5) :
    ∃ (c : Fin n → Fin 2) (k : Fin 2),
      (∀ {x y : Fin n}, G.Adj x y → c x ≠ c y) ∧
      (Finset.univ.filter (fun x => x ∈ T ∧ c x = k)).card ≤ 2 := by
  obtain ⟨c⟩ := hG
  let S := Finset.univ.filter (fun x => x ∈ T)
  have hcoe : (S : Set (Fin n)) = T := by ext; simp [S]
  have hsize : S.card ≤ 5 := by simpa only [← hcoe, Set.ncard_coe_finset] using hT
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun x => c x = 0)
  have lone : ∀ i : Fin 2, i ≠ 0 ↔ i = 1 := by decide
  simp only [S, Finset.filter_filter, lone] at hsplit
  by_cases h : (Finset.univ.filter (fun x => x ∈ T ∧ c x = 0)).card ≤ 2
  · exact ⟨c, 0, fun ha => c.valid ha, h⟩
  · refine ⟨c, 1, fun ha => c.valid ha, ?_⟩
    change (Finset.univ.filter (fun x => x ∈ T)).card ≤ 5 at hsize
    omega

lemma escape {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hdeg : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (B : Finset (Fin n)) (hB : B.card ≤ 2) (y : Fin n) (hy : y ∉ B) :
    ∃ x, G.Adj y x ∧ ∀ b ∈ B, ¬ G.Adj b x := by
  classical
  by_contra! blocked
  let N : Set (Fin n) := {w | G.Adj y w}
  have chooseBlock (x : N) : ∃ b : B, G.Adj b.val x.val := by
    obtain ⟨b, hb, hbx⟩ := blocked x.val x.property
    exact ⟨⟨b, hb⟩, hbx⟩
  let f (x : N) : B := (chooseBlock x).choose
  have adj (x : N) : G.Adj (f x).val x.val := (chooseBlock x).choose_spec
  have inj : Function.Injective f := by
    intro x z hxz
    have hz : G.Adj (f x).val z.val := hxz ▸ adj z
    obtain he | he := h4 y x.val (f x).val z.val x.property (adj x).symm hz z.property.symm
    · exact False.elim (hy (he ▸ (f x).property))
    · exact Subtype.ext he
  have upper := Fintype.card_le_of_injective f inj
  rw [Set.fintypeCard_eq_ncard, Fintype.card_coe] at upper
  have lower : 3 ≤ N.ncard := hdeg y
  omega

def completed {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (k : Fin 2) (X : Set (Fin n)) : Set (Fin n) :=
  X ∪ {y | c y ≠ k ∧ ∀ x ∈ X, ¬ G.Adj y x}

lemma maximal_completion {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin 2)
    (hc : ∀ {x y}, G.Adj x y → c x ≠ c y) (k : Fin 2) (B X : Set (Fin n))
    (hB : ∀ b ∈ B, c b ≠ k)
    (hX : ∀ x, x ∈ X ↔ c x = k ∧ ∀ b ∈ B, ¬ G.Adj x b) :
    (∀ u ∈ completed G c k X, ∀ v ∈ completed G c k X, ¬ G.Adj u v) ∧
    (∀ v, v ∉ completed G c k X → ∃ u ∈ completed G c k X, G.Adj v u) := by
  have other : ∀ a b k : Fin 2, a ≠ k → b ≠ k → a = b := by decide
  have incl : B ⊆ completed G c k X := by
    intro b hb
    exact Or.inr ⟨hB b hb, fun x hx hbx => ((hX x).mp hx).2 b hb hbx.symm⟩
  constructor
  · intro u hu v hv huv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hc huv (((hX u).mp hu).1.trans ((hX v).mp hv).1.symm)
    · exact hv.2 u hu huv.symm
    · exact hu.2 v hv huv
    · exact hc huv (other _ _ k hu.1 hv.1)
  · intro v hv
    by_contra hn
    apply hv
    by_cases hk : c v = k
    · exact Or.inl ((hX v).mpr ⟨hk, fun b hb hvb => hn ⟨b, incl hb, hvb⟩⟩)
    · exact Or.inr ⟨hk, fun x hx hvx => hn ⟨x, Or.inl hx, hvx⟩⟩

end PEqualNP.Outside.L_meta_734_aux

open PEqualNP.Outside.L_meta_734_aux

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  intro n G hcolor hfour hdegree T hsize hmeets
  obtain ⟨c, k, proper, hsmall⟩ := small_color G hcolor T hsize
  by_contra hclosed
  push Not at hclosed
  let S : Finset (Fin n) := Finset.univ.filter (fun x => x ∈ T ∧ c x = k)
  have outside (x : S) : ∃ b, G.Adj x.val b ∧ b ∉ T :=
    hclosed x.val (Finset.mem_filter.mp x.property).2.1
  let pick (x : S) : Fin n := (outside x).choose
  have picked (x : S) : G.Adj x.val (pick x) ∧ pick x ∉ T := (outside x).choose_spec
  let B : Finset (Fin n) := S.attach.image pick
  have hcount : B.card ≤ 2 := calc
    B.card ≤ S.attach.card := Finset.card_image_le
    _ = S.card := Finset.card_attach
    _ ≤ 2 := hsmall
  have properties (b : Fin n) (hb : b ∈ B) : c b ≠ k ∧ b ∉ T := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
    have hx : c x.val = k := (Finset.mem_filter.mp x.property).2.2
    exact ⟨hx ▸ (proper (picked x).1).symm, (picked x).2⟩
  let X : Set (Fin n) := {x | c x = k ∧ ∀ b ∈ B, ¬ G.Adj x b}
  obtain ⟨hind, hdom⟩ := maximal_completion G c proper k (B : Set (Fin n)) X
    (fun b hb => (properties b hb).1) (fun _ => Iff.rfl)
  obtain ⟨t, ht, hI⟩ := hmeets (completed G c k X) hind hdom
  rcases hI with hx | hy
  · have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hx.1⟩
    let s : S := ⟨t, htS⟩
    have hb : pick s ∈ B := Finset.mem_image.mpr ⟨s, Finset.mem_attach _ _, rfl⟩
    exact hx.2 _ hb (picked s).1
  · have htB : t ∉ B := fun hb => (properties t hb).2 ht
    obtain ⟨x, htx, hxb⟩ := escape G hfour hdegree B hcount t htB
    have hcx : c x = k := by
      have h₁ := proper htx
      have h₂ : c t ≠ k := hy.1
      omega
    have hx : x ∈ X := ⟨hcx, fun b hb h => hxb b hb h.symm⟩
    exact hy.2 x hx htx
