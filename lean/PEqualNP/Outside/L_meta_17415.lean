import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace PEqualNP.Outside.L_meta_17415_aux

namespace FanoCover

open scoped Fin.NatCast

theorem classify (P L : Finset (Fin 7))
    (cover : ∀ u t : Fin 7, (u=t ∨ u=t+1 ∨ u=t+3) → u∈P ∨ t∈L)
    (budget : P.card + L.card ≤ 7) :
    (P=Finset.univ ∧ L=∅) ∨ (P=∅ ∧ L=Finset.univ) := by
  have sub : Pᶜ ⊆ L := by
    intro t ht
    exact (cover t t (Or.inl rfl)).resolve_left (Finset.mem_compl.mp ht)
  have count : P.card + Pᶜ.card=7 := by simp
  have eq : Pᶜ = L := Finset.eq_of_subset_of_card_le sub (by omega)
  subst L
  have advance (t : Fin 7) (ht : t∈P) : t+1∈P :=
    (cover (t+1) t (Or.inr (Or.inl rfl))).resolve_right (by simpa using ht)
  by_cases empty : P=∅
  · right
    simp [empty]
  · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have reach (k : ℕ) : a+(k : Fin 7)∈P := by
      induction k with
      | zero => simpa using ha
      | succ k ih => simpa [Nat.cast_succ,add_assoc] using advance _ ih
    have all : P=Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      simpa [sub_eq_add_neg,add_comm,add_left_comm] using reach (u-a).val
    left
    simp [all]

end FanoCover

namespace FanoGeometry

abbrev point (u : Fin 7) : Fin 14 := Fin.castAdd 7 u
abbrev line (t : Fin 7) : Fin 14 := Fin.natAdd 7 t
abbrev incident (u t : Fin 7) : Prop := u=t ∨ u=t+1 ∨ u=t+3

abbrev cross (a b : Fin 14) : Prop :=
  a.val<7 ∧ 7≤b.val ∧ incident (Fin.ofNat 7 a.val) (Fin.ofNat 7 b.val)


abbrev graph : SimpleGraph (Fin 14) where
  Adj a b := cross a b ∨ cross b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => by rcases h with h|h <;> exact (Nat.not_le.mpr h.1) h.2.1⟩


theorem adj_point_line : ∀ u t : Fin 7, graph.Adj (point u) (line t) ↔ incident u t := by decide
theorem no_point_point : ∀ u v : Fin 7, ¬ graph.Adj (point u) (point v) := by decide
theorem no_line_line : ∀ s t : Fin 7, ¬ graph.Adj (line s) (line t) := by decide

theorem adj_iff (a b : Fin 14) : graph.Adj a b ↔
    ∃ u t, incident u t ∧ ((a=point u ∧ b=line t) ∨ (a=line t ∧ b=point u)) := by
  constructor
  · refine Fin.addCases (m:=7) (n:=7) (motive := fun a => ∀ b, graph.Adj a b →
      ∃ u t, incident u t ∧ ((a=point u ∧ b=line t) ∨ (a=line t ∧ b=point u))) ?_ ?_ a b
    · intro u b
      refine Fin.addCases (m:=7) (n:=7) ?_ ?_ b
      · intro v h; exact (no_point_point u v h).elim
      · intro t h; exact ⟨u,t,(adj_point_line u t).mp h,Or.inl ⟨rfl,rfl⟩⟩
    · intro t b
      refine Fin.addCases (m:=7) (n:=7) ?_ ?_ b
      · intro u h; exact ⟨u,t,(adj_point_line u t).mp h.symm,Or.inr ⟨rfl,rfl⟩⟩
      · intro s h; exact (no_line_line t s h).elim
  · rintro ⟨u,t,hi,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact (adj_point_line _ _).mpr hi
    · exact ((adj_point_line _ _).mpr hi).symm

theorem edgeHit_iff (x : Fin 14 → Bool) :
    (∃ a b, graph.Adj a b ∧ x a=true ∧ x b=true) ↔
    (∃ u t, incident u t ∧ x (point u)=true ∧ x (line t)=true) := by
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    obtain ⟨u,t,hi,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj_iff a b).mp h
    · exact ⟨u,t,hi,ha,hb⟩
    · exact ⟨u,t,hi,hb,ha⟩
  · rintro ⟨u,t,hi,hu,ht⟩
    exact ⟨point u,line t,(adj_point_line u t).mpr hi,hu,ht⟩

private theorem common : ∀ a c : Fin 14, a≠c →
    (Finset.univ.filter (fun z => graph.Adj a z ∧ graph.Adj c z)).card≤1 := by
  decide +kernel

theorem noFour (a b c d : Fin 14) (hac : a≠c) (hbd : b≠d) :
    ¬(graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  rintro ⟨ab,bc,cd,da⟩
  apply hbd
  apply Finset.card_le_one.mp (common a c hac) b _ d _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,da.symm,cd⟩

theorem degree_three (a : Fin 14) : graph.degree a=3 := by
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  revert a
  decide +kernel

theorem edgeCount : graph.edgeFinset.card=21 := by
  have h := graph.sum_degrees_eq_twice_card_edges
  simp only [degree_three] at h
  simp at h
  omega

def points : Finset (Fin 14) := (Finset.univ : Finset (Fin 7)).map (Fin.castAddEmb 7)
def lines : Finset (Fin 14) := (Finset.univ : Finset (Fin 7)).map (Fin.natAddEmb 7)

theorem distinct : ∀ u t : Fin 7, point u ≠ line t := by decide

theorem point_mem (u : Fin 7) : point u∈points := Finset.mem_map.mpr ⟨u,Finset.mem_univ _,rfl⟩
theorem line_mem (t : Fin 7) : line t∈lines := Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩
theorem point_not_line (u : Fin 7) : point u∉lines := by
  intro h
  obtain ⟨t,_,ht⟩ := Finset.mem_map.mp h
  exact distinct u t ht.symm
theorem line_not_point (t : Fin 7) : line t∉points := by
  intro h
  obtain ⟨u,_,hu⟩ := Finset.mem_map.mp h
  exact distinct u t hu

theorem neighbor_line {a b : Fin 14} (ha : a∈points) (hab : graph.Adj a b) : b∈lines := by
  obtain ⟨u,t,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj_iff a b).mp hab
  · exact line_mem t
  · exact (line_not_point _ ha).elim

theorem neighbor_point {a b : Fin 14} (ha : a∈lines) (hab : graph.Adj a b) : b∈points := by
  obtain ⟨u,t,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj_iff a b).mp hab
  · exact (point_not_line _ ha).elim
  · exact point_mem u

private def combine (P L : Finset (Fin 7)) :=
  P.map (Fin.castAddEmb 7) ∪ L.map (Fin.natAddEmb 7)

private lemma combine_point (P L : Finset (Fin 7)) (u : Fin 7) :
    point u∈combine P L ↔ u∈P := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hp|hl
    · obtain ⟨v,hv,he⟩ := Finset.mem_map.mp hp
      exact (Fin.castAdd_injective 7 7 he) ▸ hv
    · obtain ⟨t,_,he⟩ := Finset.mem_map.mp hl
      exact (distinct u t he.symm).elim
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨u,h,rfl⟩)

private lemma combine_line (P L : Finset (Fin 7)) (t : Fin 7) :
    line t∈combine P L ↔ t∈L := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hp|hl
    · obtain ⟨u,_,he⟩ := Finset.mem_map.mp hp
      exact (distinct u t he).elim
    · obtain ⟨s,hs,he⟩ := Finset.mem_map.mp hl
      exact ((Fin.natAddEmb 7).injective he) ▸ hs
  · intro h
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨t,h,rfl⟩)

private lemma card_combine (P L : Finset (Fin 7)) : (combine P L).card=P.card+L.card := by
  have h : Disjoint (P.map (Fin.castAddEmb 7)) (L.map (Fin.natAddEmb 7)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨t,_,eq⟩ := Finset.mem_map.mp hb
    exact distinct u t eq.symm
  simp [combine,Finset.card_union_of_disjoint h]

theorem classifyCover (K : Finset (Fin 14)) (cover : ∀ a b, graph.Adj a b → a∈K ∨ b∈K)
    (budget : K.card≤7) : K=points ∨ K=lines := by
  let P := Finset.univ.filter (fun u : Fin 7 => point u∈K)
  let L := Finset.univ.filter (fun t : Fin 7 => line t∈K)
  have parts : combine P L=K := by
    ext w
    refine Fin.addCases (m:=7) (n:=7) ?_ ?_ w
    · intro u; simpa [P] using combine_point P L u
    · intro t; simpa [L] using combine_line P L t
  have hv (u t : Fin 7) (hi : incident u t) : u∈P ∨ t∈L := by
    simpa [P,L] using cover (point u) (line t) ((adj_point_line u t).mpr hi)
  have size : P.card+L.card≤7 := by rwa [←card_combine,parts]
  rcases FanoCover.classify P L hv size with ⟨hp,hl⟩|⟨hp,hl⟩
  · left
    rw [←parts,hp,hl]; simp [combine,points]
  · right
    rw [←parts,hp,hl]; simp [combine,lines]

theorem cards : points.card=7 ∧ lines.card=7 := by simp [points,lines]

theorem coverMin (K : Finset (Fin 14)) (cover : ∀ a b, graph.Adj a b → a∈K ∨ b∈K) :
    7≤K.card := by
  by_contra! less
  have hc := cards
  rcases classifyCover K cover less.le with rfl | rfl <;> omega

theorem coverIndependent (K : Finset (Fin 14))
    (cover : ∀ a b, graph.Adj a b → a∈K ∨ b∈K) (budget : K.card≤7) :
    ∀ u∈K, ∀ v∈K, ¬graph.Adj u v := by
  rcases classifyCover K cover budget with rfl | rfl
  · intro u hu v hv e
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hv
    exact no_point_point i j e
  · intro u hu v hv e
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hv
    exact no_line_line i j e

end FanoGeometry

namespace FanoCount
theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem productiveEdgeBound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ (S (a w)).Nonempty ∧ (S (b w)).Nonempty)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card ∧ S (a w) ≠ S w ∧ S (b w) ≠ S w)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧ (S (a w)).Nonempty ∧ (S (b w)).Nonempty)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card ∧ S (a w) ≠ S w ∧ S (b w) ≠ S w)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA, _, _⟩ : w < N ∧ k ≤ w ∧ A w = true ∧ (S (a w)).Nonempty ∧ (S (b w)).Nonempty := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        by_cases ea : S (a i) = S i
        · left
          exact ⟨a i,ha,by simp [hf,hfa,ea]⟩
        by_cases eb : S (b i) = S i
        · left
          exact ⟨b i,hb,by simp [hf,hfb,eb]⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, ea, eb, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have active : (S (a w)).Nonempty ∧ (S (b w)).Nonempty := by
          rcases how with h|h
          · exact ⟨⟨u,h.1⟩,⟨v,h.2⟩⟩
          · exact ⟨⟨v,h.1⟩,⟨u,h.2⟩⟩
        have hw : w ∈ AS := by simp [AS,hN,hk,hA,active.1,active.2]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]


end FanoCount

namespace FanoCount

theorem gateBudget {n k N : ℕ} (S f : ℕ → Finset (Fin n)) (K : Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool) (size : N-k ≤ 27) (seven : 7 ≤ K.card)
    (hit : 21 ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧
        (S (a w)).Nonempty ∧ (S (b w)).Nonempty)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧
        1 < (S w).card ∧ S (a w) ≠ S w ∧ S (b w) ≠ S w)).card)
    (cost : K.card ≤ 1 + ((Finset.range N).filter (fun w =>
      k ≤ w ∧ A w = false ∧ (S w).card ≤ 1 ∧ f w ⊆ K)).card) :
    K.card = 7 ∧ ∀ w, k ≤ w → w < N →
      (A w = true → (S (a w)).Nonempty ∧ (S (b w)).Nonempty) ∧
      (A w = false → (S w).card ≤ 1 → f w ⊆ K) ∧
      (A w = false → 1 < (S w).card → S (a w) ≠ S w ∧ S (b w) ≠ S w) := by
  classical
  let av := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true ∧
    (S (a w)).Nonempty ∧ (S (b w)).Nonempty)
  let ov := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧
    1 < (S w).card ∧ S (a w) ≠ S w ∧ S (b w) ≠ S w)
  let tv := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧
    (S w).card ≤ 1 ∧ f w ⊆ K)
  change 21 ≤ av.card + ov.card at hit
  change K.card ≤ 1 + tv.card at cost
  have ad : Disjoint av ov := by
    apply Finset.disjoint_left.mpr
    intro w ha ho
    have h := (Finset.mem_filter.mp ha).2.2.1
    have h' := (Finset.mem_filter.mp ho).2.2.1
    simp_all
  have atd : Disjoint av tv := by
    apply Finset.disjoint_left.mpr
    intro w ha ht
    have h := (Finset.mem_filter.mp ha).2.2.1
    have h' := (Finset.mem_filter.mp ht).2.2.1
    simp_all
  have ot : Disjoint ov tv := by
    apply Finset.disjoint_left.mpr
    intro w ho ht
    exact (Nat.not_lt.mpr (Finset.mem_filter.mp ht).2.2.2.1) (Finset.mem_filter.mp ho).2.2.2.1
  have inside : av ∪ ov ∪ tv ⊆ Finset.Ico k N := by
    intro w hw
    rcases Finset.mem_union.mp hw with h|h
    · rcases Finset.mem_union.mp h with h|h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  have tally : (av ∪ ov ∪ tv).card = av.card + ov.card + tv.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨atd,ot⟩),Finset.card_union_of_disjoint ad]
  have cap := Finset.card_le_card inside
  rw [tally,Nat.card_Ico] at cap
  have eq : av ∪ ov ∪ tv = Finset.Ico k N := by
    apply Finset.eq_of_subset_of_card_le inside
    rw [tally,Nat.card_Ico]
    omega
  refine ⟨by omega,?_⟩
  intro w hkw hN
  have hw := Finset.mem_Ico.mpr ⟨hkw,hN⟩
  rw [←eq] at hw
  simp only [Finset.mem_union] at hw
  rcases hw with (h|h)|h
  · obtain ⟨_,_,op,left,right⟩ := Finset.mem_filter.mp h
    exact ⟨fun _ => ⟨left,right⟩,fun hn => by simp_all,fun hn => by simp_all⟩
  · obtain ⟨_,_,op,wide,left,right⟩ := Finset.mem_filter.mp h
    exact ⟨fun hn => by simp_all,fun _ thin => False.elim (Nat.not_lt.mpr thin wide),fun _ _ => ⟨left,right⟩⟩
  · obtain ⟨_,_,op,thin,sub⟩ := Finset.mem_filter.mp h
    exact ⟨fun hn => by simp_all,fun _ _ => sub,fun _ wide => False.elim (Nat.not_lt.mpr thin wide)⟩

end FanoCount

namespace FanoCount

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem productiveCoverBound (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v) :
    let f := coverCert k N S a b A ha hb
    (∀ u v, G.Adj u v → u ∈ f r ∨ v ∈ f r) ∧
      (f r).card ≤ 1 + ((Finset.range N).filter (fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1 ∧ f w ⊆ f r)).card := by
  classical
  let f := coverCert k N S a b A ha hb
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  let g (w : ℕ) : Finset (Fin n) := if f w ⊆ f r then f w else ∅
  let B := (Finset.range N).filter (fun w =>
    k ≤ w ∧ A w = false ∧ (S w).card ≤ 1 ∧ f w ⊆ f r)
  have keep (w : ℕ) (hw : f w ⊆ f r) : g w = f w := ite_eq_left hw
  have hstep (w : ℕ) (hw : 1 < (g w).card) :
      (∃ j < w, g w ⊆ g j) ∨
      (w ∈ B ∧ ∃ i < w, ∃ j < w, g w ⊆ g i ∪ g j) := by
    have hkeep : f w ⊆ f r := by
      by_contra h
      simp [g,h] at hw
    rw [keep w hkeep] at hw
    have ht : (S w).card ≤ 1 := by
      by_contra h
      rw [feq, ite_eq_right h] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      have he : f w = f (a w) ∪ f (b w) := by
        rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
        simp
      have hka : f (a w) ⊆ f r :=
        Finset.subset_union_left.trans (he ▸ hkeep)
      have hkb : f (b w) ⊆ f r :=
        Finset.subset_union_right.trans (he ▸ hkeep)
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht, hkeep⟩,
        a w, hia, b w, hib, ?_⟩
      rw [keep w hkeep,keep (a w) hka,keep (b w) hkb,he]
    | true =>
      left
      by_cases hA : (S (a w)).card ≤ 1
      · have he : f w = f (a w) := by
          rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left hA]
        refine ⟨a w, hia, ?_⟩
        rw [keep w hkeep,keep (a w) (he ▸ hkeep),he]
      · have he : f w = f (b w) := by
          rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right hA]
        refine ⟨b w, hib, ?_⟩
        rw [keep w hkeep,keep (b w) (he ▸ hkeep),he]
  have root : g r = f r := keep r (Finset.Subset.refl _)
  simpa [B,root] using dag_union_bound g {r} B hstep

end FanoCount

namespace FanoCount

def coverVisited {n : ℕ} (N r : ℕ) (S f : ℕ → Finset (Fin n)) (w : ℕ) : Prop :=
  w < N ∧ (S w).card ≤ 1 ∧ f w ⊆ f r

theorem visitRoot {n N r : ℕ} (S f : ℕ → Finset (Fin n)) (hr : r < N)
    (empty : S r = ∅) : coverVisited N r S f r :=
  ⟨hr, by simp [empty], Finset.Subset.refl _⟩

variable {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
variable (ha : ∀ w, k ≤ w → w < N → a w < w) (hb : ∀ w, k ≤ w → w < N → b w < w)

private theorem thinRaw (w : ℕ) (ht : (S w).card ≤ 1) (hw : w < k) :
    coverCert k N S a b A ha hb w = S w := by
  rw [coverCert.eq_1]
  simp [ht, Nat.not_le.mpr hw]

private theorem thinOr (w : ℕ) (hg : k ≤ w ∧ w < N) (ht : (S w).card ≤ 1)
    (op : A w=false) :
    coverCert k N S a b A ha hb w =
      coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w) := by
  rw [coverCert.eq_1]
  simp [ht,hg,op]

private theorem thinAnd (w : ℕ) (hg : k ≤ w ∧ w < N) (ht : (S w).card ≤ 1)
    (op : A w=true) :
    coverCert k N S a b A ha hb w = coverCert k N S a b A ha hb
      (if (S (a w)).card ≤ 1 then a w else b w) := by
  rw [coverCert.eq_1]
  by_cases h : (S (a w)).card ≤ 1 <;> simp [ht,hg,op,h]

theorem visitRaw (r w : ℕ)
    (v : coverVisited N r S (coverCert k N S a b A ha hb) w) (hw : w < k) :
    S w ⊆ coverCert k N S a b A ha hb r := by
  have h := v.2.2
  rwa [thinRaw k N S a b A ha hb w v.2.1 hw] at h

theorem visitOr (r w : ℕ)
    (v : coverVisited N r S (coverCert k N S a b A ha hb) w) (gate : k ≤ w)
    (op : A w=false) (hunion : S w = S (a w) ∪ S (b w)) :
    coverVisited N r S (coverCert k N S a b A ha hb) (a w) ∧
    coverVisited N r S (coverCert k N S a b A ha hb) (b w) := by
  have h := v.2.2
  rw [thinOr k N S a b A ha hb w ⟨gate,v.1⟩ v.2.1 op] at h
  have ht := v.2.1
  rw [hunion] at ht
  exact ⟨⟨(ha w gate v.1).trans v.1,
      (Finset.card_le_card Finset.subset_union_left).trans ht,Finset.subset_union_left.trans h⟩,
    ⟨(hb w gate v.1).trans v.1,
      (Finset.card_le_card Finset.subset_union_right).trans ht,Finset.subset_union_right.trans h⟩⟩

theorem visitAnd (r w : ℕ)
    (v : coverVisited N r S (coverCert k N S a b A ha hb) w) (gate : k ≤ w)
    (op : A w=true) (hside : (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1) :
    coverVisited N r S (coverCert k N S a b A ha hb)
      (if (S (a w)).card ≤ 1 then a w else b w) := by
  have h := v.2.2
  rw [thinAnd k N S a b A ha hb w ⟨gate,v.1⟩ v.2.1 op] at h
  by_cases left : (S (a w)).card ≤ 1
  · rw [ite_eq_left left] at h ⊢
    exact ⟨(ha w gate v.1).trans v.1,left,h⟩
  · rw [ite_eq_right left] at h ⊢
    exact ⟨(hb w gate v.1).trans v.1,hside.resolve_left left,h⟩

theorem certContainsSupport
    (hor : ∀ w, k ≤ w → w < N → A w=false → S w = S (a w) ∪ S (b w))
    (hand : ∀ w, k ≤ w → w < N → A w=true → S w=∅)
    (w : ℕ) (hw : w < N) (ht : (S w).card ≤ 1) :
    S w ⊆ coverCert k N S a b A ha hb w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases gate : k ≤ w
    · cases op : A w with
      | false =>
        have u := hor w gate hw op
        rw [thinOr k N S a b A ha hb w ⟨gate,hw⟩ ht op,u]
        rw [u] at ht
        have la := ha w gate hw
        have lb := hb w gate hw
        exact Finset.union_subset_union
          (ih (a w) la (la.trans hw) ((Finset.card_le_card Finset.subset_union_left).trans ht))
          (ih (b w) lb (lb.trans hw) ((Finset.card_le_card Finset.subset_union_right).trans ht))
      | true => rw [hand w gate hw op]; exact Finset.empty_subset _
    · rw [thinRaw k N S a b A ha hb w ht (Nat.lt_of_not_ge gate)]

theorem visitSupport
    (hor : ∀ w, k ≤ w → w < N → A w=false → S w = S (a w) ∪ S (b w))
    (hand : ∀ w, k ≤ w → w < N → A w=true → S w=∅)
    (r w : ℕ) (v : coverVisited N r S (coverCert k N S a b A ha hb) w) :
    S w ⊆ coverCert k N S a b A ha hb r :=
  (certContainsSupport k N S a b A ha hb hor hand w v.1 v.2.1).trans v.2.2

end FanoCount

namespace DegreeRigidity

variable {n : ℕ} {α : Type*} [DecidableEq α]

def Local (S : Fin n → Finset α) (d : Fin n → ℕ) (K : Finset α)
    (V : Set (Fin n)) (w : Fin n) : Prop :=
  (∃ v, S w={v} ∧ d w=(if v∈K then 1 else 0) ∧ (w∈V → v∈K)) ∨
  ∃ a b : Fin n, a<w ∧ b<w ∧
    ((S w=∅ ∧ d w=d a+d b ∧
      (w∈V → a∈V ∧ (S b).Nonempty ∧ Disjoint (S b) K)) ∨
    (S w=S a ∪ S b ∧ d w=max (d a) (d b) ∧
      ((S w).card≤1 → w∈V) ∧ (w∈V → a∈V ∧ b∈V) ∧
      (1<(S w).card → (S a).Nonempty ∧ (S b).Nonempty)))

theorem propagate (S : Fin n → Finset α) (d : Fin n → ℕ) (K : Finset α)
    (V : Set (Fin n)) (step : ∀ w, Local S d K V w) (w : Fin n) :
    (w∈V → S w⊆K) ∧ ((S w).Nonempty → Disjoint (S w) K → d w=0) ∧
    (w∈V → d w≤1) := by
  induction w using Fin.strong_induction_on with
  | h w ih =>
    rcases step w with ⟨v,hs,hd,hv⟩ | ⟨a,b,ha,hb,gate⟩
    · refine ⟨?_,?_,?_⟩
      · intro vis
        simpa [hs] using hv vis
      · intro _ dis
        have outside : v∉K := Finset.disjoint_left.mp dis (by simp [hs])
        simp [hd,outside]
      · intro _
        rw [hd]
        split <;> decide
    · obtain ⟨asub,azero,adeg⟩ := ih a ha
      obtain ⟨bsub,bzero,bdeg⟩ := ih b hb
      rcases gate with ⟨hs,hd,hv⟩ | ⟨hs,hd,thin,hv,wide⟩
      · refine ⟨by simp [hs],by simp [hs],?_⟩
        intro vis
        obtain ⟨av,bn,bo⟩ := hv vis
        simpa [hd,bzero bn bo] using adeg av
      · have sub (vis : w∈V) : S w⊆K := by
          obtain ⟨av,bv⟩ := hv vis
          intro t ht
          rw [hs] at ht
          exact (Finset.mem_union.mp ht).elim (fun h => asub av h) (fun h => bsub bv h)
        refine ⟨sub,?_,?_⟩
        · intro ne dis
          by_cases small : (S w).card≤1
          · obtain ⟨v,hm⟩ := ne
            exact False.elim (Finset.disjoint_left.mp dis hm (sub (thin small) hm))
          · obtain ⟨an,bn⟩ := wide (by omega)
            rw [hs] at dis
            have ao : Disjoint (S a) K := dis.mono_left Finset.subset_union_left
            have bo : Disjoint (S b) K := dis.mono_left Finset.subset_union_right
            simp [hd,azero an ao,bzero bn bo]
        · intro vis
          obtain ⟨av,bv⟩ := hv vis
          rw [hd]
          exact max_le (adeg av) (bdeg bv)

theorem output_le_one (S : Fin n → Finset α) (d : Fin n → ℕ) (K : Finset α)
    (V : Set (Fin n)) (step : ∀ w, Local S d K V w) (out : Fin n) (visit : out∈V) :
    d out≤1 := (propagate S d K V step out).2.2 visit

end DegreeRigidity

namespace FanoCount
theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)


theorem modelCount {n k N r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ u v x y : Fin n, u ≠ x → v ≠ y →
      ¬ (G.Adj u v ∧ G.Adj v x ∧ G.Adj x y ∧ G.Adj y u))
    (edges : G.edgeFinset.card = 21)
    (coverMin : ∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → 7 ≤ T.card)
    (size : N-k ≤ 27) (hr : r<N) (empty : S r=∅) (hits : ∀ u v, G.Adj u v → H r u v)
    (small : ∀ w<k, (S w).card≤1)
    (input : ∀ w u v, w<k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k≤w → w<N → a w<w) (hb : ∀ w, k≤w → w<N → b w<w)
    (ors : ∀ w, k≤w → w<N → A w=false → S w=S (a w) ∪ S (b w))
    (orh : ∀ w u v, k≤w → w<N → A w=false → H w u v → H (a w) u v ∨ H (b w) u v)
    (ands : ∀ w, k≤w → w<N → A w=true → S w=∅)
    (andh : ∀ w u v, k≤w → w<N → A w=true → H w u v → H (a w) u v ∧ H (b w) u v)
    (cross : ∀ w, k≤w → w<N → A w=true → ∀ u∈S (a w), ∀ v∈S (b w), G.Adj u v) :
    let f := coverCert k N S a b A ha hb
    let K := f r
    (∀ u v, G.Adj u v → u∈K ∨ v∈K) ∧ K.card=7 ∧
    (∀ w, k≤w → w<N → A w=true → (S (a w)).card≤1 ∨ (S (b w)).card≤1) ∧
    ∀ w, k≤w → w<N →
      (A w=true → (S (a w)).Nonempty ∧ (S (b w)).Nonempty) ∧
      (A w=false → (S w).card≤1 → f w ⊆ K) ∧
      (A w=false → 1<(S w).card → S (a w)≠S w ∧ S (b w)≠S w) := by
  classical
  let f := coverCert k N S a b A ha hb
  have sep (w : ℕ) (lo : k≤w) (hi : w<N) (op : A w=true) :
      Disjoint (S (a w)) (S (b w)) := by
    exact Finset.disjoint_left.mpr fun u hu hv => G.loopless.irrefl u (cross w lo hi op u hu u hv)
  have side (w : ℕ) (lo : k≤w) (hi : w<N) (op : A w=true) :
      (S (a w)).card≤1 ∨ (S (b w)).card≤1 := by
    by_contra! h
    obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp h.1
    obtain ⟨x,hx,y,hy,xy⟩ := Finset.one_lt_card.mp h.2
    have ax := cross w lo hi op
    exact hc4 u x v y uv xy ⟨ax u hu x hx,(ax v hv x hx).symm,ax v hv y hy,(ax u hu y hy).symm⟩
  have born (u v : Fin n) (uv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hits u v uv) (by simp [empty]) (by simp [empty]) input ha hb ors orh andh sep
  have e := productiveEdgeBound n k N G S a b A hc4 small
    (fun w lo hi => ⟨ha w lo hi,hb w lo hi⟩) ands ors cross side born
  rw [edges] at e
  obtain ⟨cov,cost⟩ := productiveCoverBound n k N r G S H a b A hr empty hits input ha hb ors orh side andh
  obtain ⟨card,paid⟩ := gateBudget S f (f r) a b A size (coverMin _ cov) e cost
  exact ⟨cov,card,side,paid⟩

end FanoCount

namespace FanoCount

theorem modelDegree {n k N r : ℕ} (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (d a b : ℕ → ℕ) (A : ℕ → Bool)
    (hr : r<N) (empty : S r=∅)
    (ha : ∀ w, k≤w → w<N → a w<w) (hb : ∀ w, k≤w → w<N → b w<w)
    (ors : ∀ w, k≤w → w<N → A w=false → S w=S (a w) ∪ S (b w))
    (ands : ∀ w, k≤w → w<N → A w=true → S w=∅)
    (cross : ∀ w, k≤w → w<N → A w=true → ∀ u∈S (a w), ∀ v∈S (b w), G.Adj u v)
    (orD : ∀ w, k≤w → w<N → A w=false → d w=max (d (a w)) (d (b w)))
    (andD : ∀ w, k≤w → w<N → A w=true → d w=d (a w)+d (b w))
    (side : ∀ w, k≤w → w<N → A w=true → (S (a w)).card≤1 ∨ (S (b w)).card≤1)
    (paid : let f := coverCert k N S a b A ha hb
      ∀ w, k≤w → w<N →
        (A w=true → (S (a w)).Nonempty ∧ (S (b w)).Nonempty) ∧
        (A w=false → (S w).card≤1 → f w⊆f r) ∧
        (A w=false → 1<(S w).card → S (a w)≠S w ∧ S (b w)≠S w))
    (raw : ∀ w<k, ∃ v, S w={v} ∧
      d w=(if v∈coverCert k N S a b A ha hb r then 1 else 0))
    (independent : let K := coverCert k N S a b A ha hb r
      ∀ u∈K, ∀ v∈K, ¬G.Adj u v) : d r≤1 := by
  classical
  let f := coverCert k N S a b A ha hb
  let K := f r
  let SS (w : Fin N) := S w.val
  let dd (w : Fin N) := d w.val
  let V : Set (Fin N) := {w : Fin N | coverVisited N r S f w.val}
  have opposite (i j : ℕ) (vi : coverVisited N r S f i) (ni : (S i).Nonempty)
      (adj : ∀ u∈S i, ∀ v∈S j, G.Adj u v) : Disjoint (S j) K := by
    obtain ⟨u,hu⟩ := ni
    have uk := visitSupport k N S a b A ha hb ors ands r i vi hu
    exact Finset.disjoint_left.mpr fun v hv vk => independent u uk v vk (adj u hu v hv)
  have step (w : Fin N) : DegreeRigidity.Local SS dd K V w := by
    by_cases gate : k ≤ w.val
    · have la := ha w gate w.isLt
      have lb := hb w gate w.isLt
      let ia : Fin N := ⟨a w,la.trans w.isLt⟩
      let ib : Fin N := ⟨b w,lb.trans w.isLt⟩
      obtain ⟨nonempty,thin,wide⟩ := paid w gate w.isLt
      cases op : A w with
      | false =>
        have u := ors w gate w.isLt op
        refine Or.inr ⟨ia,ib,la,lb,Or.inr ⟨u,orD w gate w.isLt op,?_,?_,?_⟩⟩
        · exact fun h => ⟨w.isLt,h,thin op h⟩
        · exact fun v => visitOr k N S a b A ha hb r w v gate op u
        · intro h
          obtain ⟨pa,pb⟩ := wide op h
          constructor
          · apply Finset.nonempty_iff_ne_empty.mpr
            intro ea
            change S (a w) = ∅ at ea
            exact pb (by simpa [ea] using u.symm)
          · apply Finset.nonempty_iff_ne_empty.mpr
            intro eb
            change S (b w) = ∅ at eb
            exact pa (by simpa [eb] using u.symm)
      | true =>
        have nv := nonempty op
        have neigh := cross w gate w.isLt op
        have chosen (vis : w ∈ V) := visitAnd k N S a b A ha hb r w vis gate op (side w gate w.isLt op)
        by_cases left : (S (a w)).card≤1
        · refine Or.inr ⟨ia,ib,la,lb,Or.inl ⟨ands w gate w.isLt op,andD w gate w.isLt op,?_⟩⟩
          intro vis
          have va : ia∈V := by
            change coverVisited N r S (coverCert k N S a b A ha hb) (a w)
            simpa only [ite_eq_left left] using chosen vis
          exact ⟨va,nv.2,opposite (a w) (b w) va nv.1 neigh⟩
        · refine Or.inr ⟨ib,ia,lb,la,Or.inl ⟨ands w gate w.isLt op,
            (andD w gate w.isLt op).trans (Nat.add_comm _ _),?_⟩⟩
          intro vis
          have vb : ib∈V := by
            change coverVisited N r S (coverCert k N S a b A ha hb) (b w)
            simpa only [ite_eq_right left] using chosen vis
          exact ⟨vb,nv.1,opposite (b w) (a w) vb nv.2 (fun u hu v hv => (neigh v hv u hu).symm)⟩
    · have input := Nat.lt_of_not_ge gate
      obtain ⟨v,hs,hd⟩ := raw w input
      refine Or.inl ⟨v,hs,hd,?_⟩
      intro vis
      exact visitRaw k N S a b A ha hb r w vis input (by simp [hs])
  exact DegreeRigidity.output_le_one SS dd K V step ⟨r,hr⟩ (visitRoot S f hr empty)

end FanoCount

namespace ConcreteModel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace Fold
def stepG {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (w : List α) (g : Gate) : List α :=
  w ++ [F (fun i => w.getD i d) g]

def Loc {α : Type} (F : (ℕ → α) → Gate → α) : Prop :=
  ∀ V V' : ℕ → α, ∀ g : Gate, (∀ i ∈ g.inputs, V i = V' i) → F V g = F V' g

lemma gfoldl_length {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (gs : List Gate) (w : List α) :
    (gs.foldl (stepG F d) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepG]
    omega

lemma gfoldl_getD_lt {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (gs : List Gate) (w : List α)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (stepG F d) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepG F d w g).length := by simp [stepG]; omega
    rw [ih (stepG F d w g) hlt]
    simp [stepG, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ggetD_ge {α : Type} (w : List α) (d : α) (i : ℕ) (hi : w.length ≤ i) : w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma gfoldl_getD_gate {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (hF : Loc F)
    (gs : List Gate) (w : List α) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (stepG F d) w).getD (w.length + j) d =
      F (fun i => if i < w.length + j then (gs.foldl (stepG F d) w).getD i d else d) gs[j] := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepG F d w g).length := by simp [stepG]
      rw [Nat.add_zero, gfoldl_getD_lt F d gs (stepG F d w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepG F d w g).getD w.length d = F (fun i => w.getD i d) g := by
        simp [stepG, List.getD_eq_getElem?_getD]
      rw [h2]
      apply hF
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, gfoldl_getD_lt F d gs (stepG F d w g) i (by simp [stepG]; omega)]
        simp [stepG, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact ggetD_ge w d i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepG F d w g) j hj'
      have hl : (stepG F d w g).length = w.length + 1 := by simp [stepG]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gate_val {α : Type} (F : (ℕ → α) → Gate → α) (d : α) (hF : Loc F) (n : ℕ) (C : Circuit)
    (hRB : ReadsBack n C) (w : List α) (hw : w.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (stepG F d) w).getD (n + j) d =
      F (fun i => (C.gates.foldl (stepG F d) w).getD i d) C.gates[j] := by
  subst hw
  rw [gfoldl_getD_gate F d hF C.gates w j hj]
  apply hF
  intro i hi
  have : i < w.length + j := hRB j hj i (by rw [gateAt_eq hj]; exact hi)
  rw [ite_eq_left this]

def Fw (V : ℕ → Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map V)

def comb : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.sum
  | _, l => l.foldr max 0

def Fd (V : ℕ → ℕ) (g : Gate) : ℕ := comb g.op (g.inputs.map V)

lemma loc_w : Loc Fw := by
  intro V V' g h; unfold Fw; rw [List.map_congr_left h]

lemma loc_d : Loc Fd := by
  intro V V' g h; unfold Fd; rw [List.map_congr_left h]

lemma lineDegrees_eq (C : Circuit) (n : ℕ) (m : Finset ℕ) :
    C.lineDegrees n m = C.gates.foldl (stepG Fd 0)
      ((List.range n).map fun i => if i ∈ m then 1 else 0) := by
  unfold Circuit.lineDegrees
  congr 1
  funext w g
  obtain ⟨op, l⟩ := g
  cases op <;> simp [stepG, Fd, comb, Gate.lineDegree]


end Fold

def Valid (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i k : ℕ, g.inputs = [i,k] ∧ i ≠ k ∧ i < 14+j ∧ k < 14+j

def Computes (G : SimpleGraph (Fin 14)) (C : Circuit) : Prop :=
  ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def W (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def S (C : Circuit) (w : ℕ) : Finset (Fin 14) :=
  Finset.univ.filter fun u => W C (pairInput u u) w = true

def H (C : Circuit) (w : ℕ) (u v : Fin 14) : Prop := W C (pairInput u v) w = true

def A (C : Circuit) (w : ℕ) : Bool :=
  match (gateAt C (w-14)).op with
  | .and => true
  | _ => false

def a (C : Circuit) (w : ℕ) : ℕ := (gateAt C (w-14)).inputs.getD 0 0
def b (C : Circuit) (w : ℕ) : ℕ := (gateAt C (w-14)).inputs.getD 1 0
def d (C : Circuit) (K : Finset (Fin 14)) (w : ℕ) : ℕ :=
  (C.lineDegrees 14 (K.image Fin.val)).getD w 0

theorem mem_S {C : Circuit} {w : ℕ} {u : Fin 14} : u ∈ S C w ↔ H C w u u := by
  simp [S,H]

theorem readsBack (C : Circuit) (h : Valid C) : ReadsBack 14 C := by
  intro j hj i hi
  rw [Fold.gateAt_eq hj] at hi
  obtain ⟨_, l,r,hp,_,hl,hr⟩ := h j C.gates[j] (List.getElem?_eq_getElem hj)
  simpa [hp] using (show ∀ i ∈ C.gates[j].inputs, i < 14+j from by
    rw [hp]; simpa using And.intro hl hr) i hi

theorem W_raw (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) (hw : w < 14) :
    W C x w = x ⟨w,hw⟩ := by
  unfold W
  change (C.gates.foldl (Fold.stepG Fold.Fw false) _).getD w false = _
  rw [Fold.gfoldl_getD_lt _ _ _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]

theorem S_raw (C : Circuit) (w : ℕ) (hw : w < 14) :
    S C w = {⟨w,hw⟩} := by
  ext u
  simp [S,W_raw C _ w hw,pairInput,eq_comm]

theorem H_raw (C : Circuit) (w : ℕ) (hw : w < 14) (u v : Fin 14) :
    H C w u v ↔ u ∈ S C w ∨ v ∈ S C w := by
  change W C (pairInput u v) w = true ↔ _
  rw [W_raw C _ w hw,S_raw C w hw]
  simp only [pairInput,decide_eq_true_eq,Finset.mem_singleton]
  exact or_congr eq_comm eq_comm

theorem d_raw (C : Circuit) (K : Finset (Fin 14)) (w : ℕ) (hw : w < 14) :
    d C K w = if ⟨w,hw⟩ ∈ K then 1 else 0 := by
  unfold d
  rw [Fold.lineDegrees_eq, Fold.gfoldl_getD_lt _ _ _ _ _ (by simpa using hw)]
  have e : w ∈ K.image Fin.val ↔ (⟨w,hw⟩ : Fin 14) ∈ K := by
    simp only [Finset.mem_image]
    exact ⟨fun ⟨u,hu,hv⟩ => (Fin.ext hv : u = ⟨w,hw⟩) ▸ hu, fun h => ⟨_,h,rfl⟩⟩
  rw [List.getD_eq_getElem _ _ (by simpa using hw),List.getElem_map,List.getElem_range]
  simp only [e]

theorem parents (C : Circuit) (h : Valid C) (w : ℕ)
    (lo : 14 ≤ w) (hi : w < 14+C.gates.length) :
    a C w < w ∧ b C w < w ∧ a C w ≠ b C w := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lo
  have hj : j < C.gates.length := by omega
  obtain ⟨_,l,r,hp,hn,hl,hr⟩ := h j C.gates[j] (List.getElem?_eq_getElem hj)
  simpa [a,b,Fold.gateAt_eq hj,hp] using And.intro hl (And.intro hr hn)

theorem gate_eq (C : Circuit) (h : Valid C) (w : ℕ)
    (lo : 14 ≤ w) (hi : w < 14+C.gates.length) (x : Fin 14 → Bool) (K : Finset (Fin 14)) :
    (W C x w = if A C w then W C x (a C w) && W C x (b C w) else
      W C x (a C w) || W C x (b C w)) ∧
    (d C K w = if A C w then d C K (a C w) + d C K (b C w) else
      max (d C K (a C w)) (d C K (b C w))) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le lo
  have hj : j < C.gates.length := by omega
  obtain ⟨hop,l,r,hp,_,_,_⟩ := h j C.gates[j] (List.getElem?_eq_getElem hj)
  have eW : W C x (14+j) = Fold.Fw (W C x) C.gates[j] :=
    Fold.gate_val Fold.Fw false Fold.loc_w 14 C (readsBack C h) _ (by simp) j hj
  have eD : d C K (14+j) = Fold.Fd (d C K) C.gates[j] := by
    unfold d
    rw [Fold.lineDegrees_eq]
    exact Fold.gate_val Fold.Fd 0 Fold.loc_d 14 C (readsBack C h) _ (by simp) j hj
  rw [eW,eD]
  rcases hop with op|op <;>
    simp [A,a,b,Fold.gateAt_eq hj,op,hp,Fold.Fw,Fold.Fd,Fold.comb,GateOp.eval]

theorem S_or (C : Circuit) (h : Valid C) (w : ℕ) (lo : 14 ≤ w)
    (hi : w < 14+C.gates.length) (op : A C w = false) :
    S C w = S C (a C w) ∪ S C (b C w) := by
  ext u
  simp [S,(gate_eq C h w lo hi (pairInput u u) ∅).1,op]

theorem H_or (C : Circuit) (h : Valid C) (w : ℕ) (lo : 14 ≤ w)
    (hi : w < 14+C.gates.length) (op : A C w = false) (u v : Fin 14) :
    H C w u v ↔ H C (a C w) u v ∨ H C (b C w) u v := by
  simp [H,(gate_eq C h w lo hi (pairInput u v) ∅).1,op]

theorem H_and (C : Circuit) (h : Valid C) (w : ℕ) (lo : 14 ≤ w)
    (hi : w < 14+C.gates.length) (op : A C w = true) (u v : Fin 14) :
    H C w u v ↔ H C (a C w) u v ∧ H C (b C w) u v := by
  simp [H,(gate_eq C h w lo hi (pairInput u v) ∅).1,op]

theorem S_and (C : Circuit) (h : Valid C) (w : ℕ) (lo : 14 ≤ w)
    (hi : w < 14+C.gates.length) (op : A C w = true) :
    S C w = S C (a C w) ∩ S C (b C w) := by
  ext u
  simp [S,(gate_eq C h w lo hi (pairInput u u) ∅).1,op]

theorem output_hits (G : SimpleGraph (Fin 14)) (C : Circuit) (hc : Computes G C)
    (u v : Fin 14) (edge : G.Adj u v) : H C C.output u v := by
  exact (hc _).2 ⟨u,v,edge,by simp [pairInput],by simp [pairInput]⟩

theorem output_support (G : SimpleGraph (Fin 14)) (C : Circuit) (hc : Computes G C) :
    S C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨u,v,edge,hu,hv⟩ := (hc (pairInput z z)).1 (mem_S.mp hz)
  simp [pairInput] at hu hv
  subst u; subst v
  exact G.loopless.irrefl z edge

theorem output_lt (G : SimpleGraph (Fin 14)) (C : Circuit) (hc : Computes G C)
    (u v : Fin 14) (edge : G.Adj u v) : C.output < 14+C.gates.length := by
  by_contra! far
  have on := output_hits G C hc u v edge
  change (C.gates.foldl (Fold.stepG Fold.Fw false) _).getD C.output false = true at on
  rw [Fold.ggetD_ge _ _ _ (by simpa [Fold.gfoldl_length] using far)] at on
  contradiction

theorem W_mono (C : Circuit) (h : Valid C) (x y : Fin 14 → Bool)
    (ord : ∀ i, x i = true → y i = true) (w : ℕ) (hw : w < 14+C.gates.length) :
    W C x w = true → W C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < 14
    · simpa only [W_raw C _ w raw] using ord ⟨w,raw⟩
    have lo : 14 ≤ w := by omega
    obtain ⟨ha,hb,_⟩ := parents C h w lo hw
    have left := ih _ ha (ha.trans hw)
    have right := ih _ hb (hb.trans hw)
    rw [(gate_eq C h w lo hw x ∅).1,(gate_eq C h w lo hw y ∅).1]
    cases op : A C w <;> simp <;> tauto

def PairClean (G : SimpleGraph (Fin 14)) (C : Circuit) : Prop :=
  ∀ w, 14 ≤ w → w < 14+C.gates.length → A C w = true →
    ∀ u v, H C w u v → G.Adj u v

theorem clean_empty (G : SimpleGraph (Fin 14)) (C : Circuit) (clean : PairClean G C)
    (w : ℕ) (lo : 14 ≤ w) (hi : w < 14+C.gates.length) (op : A C w = true) :
    S C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact G.loopless.irrefl u (clean w lo hi op u u (mem_S.mp hu))

theorem clean_cross (G : SimpleGraph (Fin 14)) (C : Circuit) (h : Valid C)
    (clean : PairClean G C) (w : ℕ) (lo : 14 ≤ w)
    (hi : w < 14+C.gates.length) (op : A C w = true) :
    ∀ u ∈ S C (a C w), ∀ v ∈ S C (b C w), G.Adj u v := by
  intro u hu v hv
  obtain ⟨ha,hb,_⟩ := parents C h w lo hi
  apply clean w lo hi op u v
  apply (H_and C h w lo hi op u v).2
  constructor
  · apply W_mono C h (pairInput u u) (pairInput u v) _ _ (ha.trans hi) (mem_S.mp hu)
    intro i on
    simp only [pairInput,decide_eq_true_eq,or_self] at on ⊢
    exact Or.inl on
  · apply W_mono C h (pairInput v v) (pairInput u v) _ _ (hb.trans hi) (mem_S.mp hv)
    intro i on
    simp only [pairInput,decide_eq_true_eq,or_self] at on ⊢
    exact Or.inr on

theorem d_output (C : Circuit) (K : Finset (Fin 14)) :
    d C K C.output = C.lineDeg 14 (K.image Fin.val) := rfl

end ConcreteModel

namespace ConcreteRigidity
open PEqualNP.CircuitLowerBounds
open ConcreteModel

theorem rigidity (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (four : ∀ u v x y : Fin 14, u ≠ x → v ≠ y →
      ¬ (G.Adj u v ∧ G.Adj v x ∧ G.Adj x y ∧ G.Adj y u))
    (edges : G.edgeFinset.card = 21)
    (minCover : ∀ T : Finset (Fin 14),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → 7 ≤ T.card)
    (indCover : ∀ T : Finset (Fin 14),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → T.card = 7 →
      ∀ u ∈ T, ∀ v ∈ T, ¬G.Adj u v)
    (C : Circuit) (valid : Valid C) (computes : Computes G C)
    (size : C.size ≤ 27) (clean : PairClean G C) :
    ∃ K : Finset (Fin 14), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      K.card = 7 ∧ C.lineDeg 14 (K.image Fin.val) ≤ 1 := by
  have exists_edge : ∃ u v, G.Adj u v := by
    by_contra! none
    have bad := minCover ∅ (fun u v huv => (none u v huv).elim)
    simp at bad
  obtain ⟨u,v,edge⟩ := exists_edge
  let N := 14+C.gates.length
  have hr : C.output < N := output_lt G C computes u v edge
  have ha : ∀ w, 14 ≤ w → w < N → a C w < w :=
    fun w lo hi => (parents C valid w lo hi).1
  have hb : ∀ w, 14 ≤ w → w < N → b C w < w :=
    fun w lo hi => (parents C valid w lo hi).2.1
  let K := FanoCount.coverCert 14 N (S C) (a C) (b C) (A C) ha hb C.output
  have counted := FanoCount.modelCount G (S C) (H C) (a C) (b C) (A C) four edges minCover
    (show N-14 ≤ 27 by simpa [N,Circuit.size] using size)
    hr (output_support G C computes) (output_hits G C computes)
    (fun w hw => by simp [S_raw C w hw])
    (fun w u v hw hh => (H_raw C w hw u v).1 hh)
    ha hb (S_or C valid) (fun w u v lo hi op => (H_or C valid w lo hi op u v).1)
    (clean_empty G C clean) (fun w u v lo hi op => (H_and C valid w lo hi op u v).1)
    (clean_cross G C valid clean)
  obtain ⟨cover,card,side,paid⟩ := counted
  refine ⟨K,cover,card,?_⟩
  change d C K C.output ≤ 1
  exact FanoCount.modelDegree G (S C) (d C K) (a C) (b C) (A C)
    hr (output_support G C computes) ha hb (S_or C valid) (clean_empty G C clean)
    (clean_cross G C valid clean)
    (fun w lo hi op => by simpa only [op, Bool.false_eq_true, ite_false] using
      (gate_eq C valid w lo hi (fun _ => false) K).2)
    (fun w lo hi op => by simpa only [op, ite_true] using
      (gate_eq C valid w lo hi (fun _ => false) K).2)
    side paid (fun w hw => ⟨⟨w,hw⟩,S_raw C w hw,d_raw C K w hw⟩)
    (indCover K cover card)

end ConcreteRigidity

namespace FanoMarks
open PEqualNP.CircuitLowerBounds

abbrev LeList := List.Forall₂ (fun a b : ℕ => a ≤ b)

theorem read_le {xs ys : List ℕ} (h : LeList xs ys) (i : ℕ) :
    xs.getD i 0 ≤ ys.getD i 0 := by
  induction h generalizing i with
  | nil => simp [List.getD]
  | cons hh _ ih => cases i with
    | zero => exact hh
    | succ j => exact ih j

theorem gate_le (g : Gate) {xs ys : List ℕ} (h : LeList xs ys) :
    g.lineDegree xs ≤ g.lineDegree ys := by
  have both (ps : List ℕ) :
      (ps.map (fun i => xs.getD i 0)).sum ≤ (ps.map (fun i => ys.getD i 0)).sum ∧
      (ps.map (fun i => xs.getD i 0)).foldr max 0 ≤ (ps.map (fun i => ys.getD i 0)).foldr max 0 := by
    induction ps with
    | nil => exact ⟨le_rfl,le_rfl⟩
    | cons i ps ih => exact ⟨Nat.add_le_add (read_le h i) ih.1,max_le_max (read_le h i) ih.2⟩
  unfold Gate.lineDegree
  split
  · exact (both g.inputs).1
  · exact (both g.inputs).2

theorem mono (C : Circuit) (n : ℕ) {K L : Finset ℕ} (sub : K ⊆ L) :
    C.lineDeg n K ≤ C.lineDeg n L := by
  let init (T : Finset ℕ) (xs : List ℕ) := xs.map fun i => if i ∈ T then 1 else 0
  have base (xs : List ℕ) : LeList (init K xs) (init L xs) := by
    induction xs with
    | nil => exact .nil
    | cons j js ih =>
      apply List.Forall₂.cons _ ih
      by_cases h : j∈K
      · simp [h,sub h]
      · simp [h]
  let step := fun (s : List ℕ) (g : Gate) => s ++ [g.lineDegree s]
  have run (gs : List Gate) (x y : List ℕ) (h : LeList x y) :
      LeList (gs.foldl step x) (gs.foldl step y) := by
    induction gs generalizing x y with
    | nil => exact h
    | cons g gs ih =>
      apply ih
      exact List.rel_append h (List.Forall₂.cons (gate_le g h) List.Forall₂.nil)
  exact read_le (run C.gates _ _ (base (List.range n))) C.output

end FanoMarks

namespace FanoFlag
open PEqualNP.CircuitLowerBounds

theorem flag (C : Circuit) (valid : ConcreteModel.Valid C) (size : C.size≤27)
    (eval : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔
      ∃ u t : Fin 7, FanoGeometry.incident u t ∧
        x (FanoGeometry.point u)=true ∧ x (FanoGeometry.line t)=true)
    (clean : ConcreteModel.PairClean FanoGeometry.graph C)
    (u t : Fin 7) (edge : FanoGeometry.incident u t) :
    C.lineDeg 14 {u.val} ≤ 1 ∨ C.lineDeg 14 {7+t.val} ≤ 1 := by
  have computes : ConcreteModel.Computes FanoGeometry.graph C :=
    fun x => (eval x).trans (FanoGeometry.edgeHit_iff x).symm
  obtain ⟨K, cover, _, cost⟩ := ConcreteRigidity.rigidity FanoGeometry.graph
    FanoGeometry.noFour FanoGeometry.edgeCount FanoGeometry.coverMin
    (fun T h hc => FanoGeometry.coverIndependent T h hc.le) C valid computes size clean
  have mono (i : Fin 14) (hi : i∈K) : C.lineDeg 14 {i.val} ≤ 1 := by
    apply le_trans (FanoMarks.mono C 14 (K:={i.val}) (L:=K.image Fin.val) ?_) cost
    exact Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ hi)
  rcases cover _ _ ((FanoGeometry.adj_point_line u t).mpr edge) with a|a
  · exact Or.inl (mono _ a)
  · exact Or.inr (mono _ a)

end FanoFlag

namespace FanoExternal
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

theorem clean_of_tests (C : Circuit) (G : SimpleGraph (Fin 14))
    (computes : ConcreteModel.Computes G C)
    (tests : ∀ j, ReadTwo.isAnd C j → ∀ a b : Fin 14,
      let x := pairInput a b
      gateVal 14 C j x = true → C.eval (List.ofFn x) = true) :
    ConcreteModel.PairClean G C := by
  intro w lo hi op a b active
  have hw : 14+(w-14)=w := by omega
  have hand : ReadTwo.isAnd C (w-14) := by
    refine ⟨by omega,?_⟩
    cases h : (gateAt C (w-14)).op <;> simp_all [ConcreteModel.A]
  have on : gateVal 14 C (w-14) (pairInput a b)=true := by
    simpa only [gateVal,hw,ConcreteModel.H,ConcreteModel.W] using active
  obtain ⟨u,v,uv,hu,hv⟩ := (computes _).mp (tests _ hand a b on)
  simp only [pairInput,decide_eq_true_iff] at hu hv
  rcases hu with hu|hu <;> rcases hv with hv|hv <;> rw [hu,hv] at uv
  · exact (G.loopless.irrefl _ uv).elim
  · exact uv
  · exact uv.symm
  · exact (G.loopless.irrefl _ uv).elim

theorem flagTests (C : Circuit) (valid : ConcreteModel.Valid C) (size : C.size≤27)
    (eval : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔
      ∃ u t : Fin 7, FanoGeometry.incident u t ∧ x (FanoGeometry.point u)=true ∧
        x (FanoGeometry.line t)=true)
    (tests : ∀ j, ReadTwo.isAnd C j → ∀ a b : Fin 14, let x := pairInput a b
      gateVal 14 C j x = true → C.eval (List.ofFn x) = true)
    (u t : Fin 7) (edge : FanoGeometry.incident u t) :
    C.lineDeg 14 {u.val} ≤ 1 ∨ C.lineDeg 14 {7+t.val} ≤ 1 :=
  FanoFlag.flag C valid size eval (clean_of_tests C FanoGeometry.graph
    (fun x => (eval x).trans (FanoGeometry.edgeHit_iff x).symm) tests) u t edge

end FanoExternal

end PEqualNP.Outside.L_meta_17415_aux

open PEqualNP.Outside.L_meta_17415_aux

theorem PEqualNP.Outside.L_meta_17415 : (
have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x2 x3 →     (∀ (x5 : ℕ),         PEqualNP.ReadTwo.isAnd x3 x5 →           ∀ (x7 x8 : Fin (14 : ℕ)),             have x9 : Fin (14 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput x7 x8;             PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x3 x5 x9 = Bool.true → x3.eval (List.ofFn x9) = Bool.true) →       ∀ (x6 x7 : Fin (7 : ℕ)), x1 x6 x7 → x3.lineDeg (14 : ℕ) {↑x6} ≤ (1 : ℕ) ∨ x3.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x7} ≤ (1 : ℕ)
) := by
  intro inc valid C hC tests p t edge
  exact FanoExternal.flagTests C hC.2.1 hC.1 hC.2.2 tests p t edge
