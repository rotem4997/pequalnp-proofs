import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_705_aux

open PEqualNP.AndCount

lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

lemma fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

lemma gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

def retained {k : ℕ} (g : Fin k) := Finset.univ.erase g

def liftGate {k : ℕ} (g : Fin k) :
    Fin (retained g).card ↪o Fin k := (retained g).orderEmbOfFin rfl

lemma lift_ne {k : ℕ} (g : Fin k) (i : Fin (retained g).card) :
    liftGate g i ≠ g :=
  (Finset.mem_erase.mp ((retained g).orderEmbOfFin_mem rfl i)).1

lemma lift_exists {k : ℕ} {g j : Fin k} (h : j ≠ g) :
    ∃ i, liftGate g i = j := by
  have hr : Set.range (liftGate g) = (retained g : Set (Fin k)) :=
    Finset.range_orderEmbOfFin _ rfl
  exact Set.mem_range.mp (hr.symm ▸ Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)

def redirectVars {n k : ℕ} (g : Fin k) (N V B : Finset (Fin n))
    (F : Finset (Fin k)) : Finset (Fin n) :=
  (B ∪ (if g ∈ F then V else ∅)) \ N

def redirectGates {k : ℕ} (g : Fin k)
    (Q F : Finset (Fin k)) : Finset (Fin (retained g).card) :=
  Finset.univ.filter fun j => liftGate g j ∈ F ∨ g ∈ F ∧ liftGate g j ∈ Q

def splice {n : ℕ} (C : AndCountCircuit n) (g : Fin C.size) (N V : Finset (Fin n))
    (Q : Finset (Fin C.size)) : AndCountCircuit n where
  size := (retained g).card
  leftVars i := redirectVars g N V (C.leftVars (liftGate g i)) (C.leftGates (liftGate g i))
  leftGates i := redirectGates g Q (C.leftGates (liftGate g i))
  rightVars i := redirectVars g N V (C.rightVars (liftGate g i)) (C.rightGates (liftGate g i))
  rightGates i := redirectGates g Q (C.rightGates (liftGate g i))
  outVars := redirectVars g N V C.outVars C.outGates
  outGates := redirectGates g Q C.outGates

lemma redirect_lt {k : ℕ} (g : Fin k)
    (Q F : Finset (Fin k)) (i j : Fin (retained g).card)
    (hQ : ∀ k ∈ Q, k < g) (hF : ∀ k ∈ F, k < liftGate g i)
    (hj : j ∈ redirectGates g Q F) : j < i := by
  apply (liftGate g).lt_iff_lt.mp
  rcases (Finset.mem_filter.mp hj).2 with h | ⟨hg, hq⟩
  · exact hF _ h
  · exact (hQ _ hq).trans (hF _ hg)

lemma splice_wf {n : ℕ} (C : AndCountCircuit n) (g : Fin C.size) (N V : Finset (Fin n))
    (Q : Finset (Fin C.size)) (hC : C.WellFormed) (hQ : ∀ k ∈ Q, k < g) :
    (splice C g N V Q).WellFormed := by
  intro i
  exact ⟨fun j hj => redirect_lt g _ _ i j hQ (hC (liftGate g i)).1 hj,
    fun j hj => redirect_lt g _ _ i j hQ (hC (liftGate g i)).2 hj⟩

def orValue {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (f : Fin k → Bool) : Prop :=
  (∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, f j = true

lemma side_as_or {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (f : Fin k → Bool) (hF : ∀ j ∈ F, j < i) :
    AndCountCircuit.sideTrue U B F i f = true ↔ orValue U B F f := by
  simp only [AndCountCircuit.sideTrue, decide_eq_true_eq, orValue]
  constructor
  · rintro (h | ⟨j, hj, _, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hv⟩
  · rintro (h | ⟨j, hj, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hF _ hj, hv⟩

lemma redirect_spec {n k : ℕ} (g : Fin k)
    (I N V B : Finset (Fin n)) (Q F : Finset (Fin k))
    (f : Fin k → Bool) (f' : Fin (retained g).card → Bool)
    (hQ : ∀ k ∈ Q, k < g)
    (gone : f g = true ↔ orValue (I \ N) V Q f)
    (hval : ∀ j ∈ redirectGates g Q F, f' j = f (liftGate g j)) :
    orValue I (redirectVars g N V B F) (redirectGates g Q F) f' ↔ orValue (I \ N) B F f := by
  constructor
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, hf⟩)
    · have hn := (Finset.mem_sdiff.mp hv).2
      have hU := Finset.mem_sdiff.mpr ⟨hI, hn⟩
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hb | hv'
      · exact Or.inl ⟨v, hb, hU⟩
      · by_cases hg : g ∈ F
        · have hV : v ∈ V := by simpa [hg] using hv'
          exact Or.inr ⟨g, hg, gone.mpr (Or.inl ⟨v, hV, hU⟩)⟩
        · simp [hg] at hv'
    · rw [hval j hj] at hf
      rcases (Finset.mem_filter.mp hj).2 with h | ⟨hg, hq⟩
      · exact Or.inr ⟨liftGate g j, h, hf⟩
      · exact Or.inr ⟨g, hg, gone.mpr (Or.inr ⟨liftGate g j, hq, hf⟩)⟩
  · rintro (⟨v, hv, hU⟩ | ⟨j, hj, hf⟩)
    · obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hU
      exact Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hv, hn⟩, hi⟩
    · by_cases he : j = g
      · subst j
        rcases gone.mp hf with ⟨v, hv, hU⟩ | ⟨r, hr, hfr⟩
        · obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hU
          have hu : v ∈ B ∪ (if g ∈ F then V else ∅) :=
            Finset.mem_union_right _ (by simpa [hj] using hv)
          exact Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨hu, hn⟩, hi⟩
        · obtain ⟨i, rfl⟩ := lift_exists (ne_of_lt (hQ _ hr))
          have hi : i ∈ redirectGates g Q F :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hj, hr⟩⟩
          exact Or.inr ⟨i, hi, (hval i hi).trans hfr⟩
      · obtain ⟨i, rfl⟩ := lift_exists he
        have hi : i ∈ redirectGates g Q F :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hj⟩
        exact Or.inr ⟨i, hi, (hval i hi).trans hf⟩

lemma splice_eval {n : ℕ} (C : AndCountCircuit n) (g : Fin C.size)
    (I N V : Finset (Fin n)) (Q : Finset (Fin C.size)) (hC : C.WellFormed)
    (hQ : ∀ k ∈ Q, k < g)
    (gone : C.gateVal (I \ N) g = true ↔ orValue (I \ N) V Q (C.gateVal (I \ N))) :
    (splice C g N V Q).eval I = C.eval (I \ N) := by
  let C' := splice C g N V Q
  have hC' := splice_wf C g N V Q hC hQ
  have bound (b : ℕ) : ∀ i : Fin C'.size, i.val < b →
      C'.gateVal I i = C.gateVal (I \ N) (liftGate g i) := by
    induction b with
    | zero => intro i hi; omega
    | succ b ih =>
      intro i hi
      have hbefore (j : Fin C'.size) (hj : j < i) :
          C'.gateVal I j = C.gateVal (I \ N) (liftGate g j) := by
        apply ih
        have : j.val < i.val := hj
        omega
      have left := redirect_spec g I N V (C.leftVars (liftGate g i)) Q
        (C.leftGates (liftGate g i)) (C.gateVal (I \ N)) (C'.gateVal I) hQ gone
        (fun j hj => hbefore j ((hC' i).1 j hj))
      have right := redirect_spec g I N V (C.rightVars (liftGate g i)) Q
        (C.rightGates (liftGate g i)) (C.gateVal (I \ N)) (C'.gateVal I) hQ gone
        (fun j hj => hbefore j ((hC' i).2 j hj))
      apply Bool.eq_iff_iff.mpr
      rw [gateVal_eq C' I i, gateVal_eq C (I \ N) (liftGate g i)]
      rw [Bool.and_eq_true, Bool.and_eq_true,
        side_as_or I (C'.leftVars i) (C'.leftGates i) i (C'.gateVal I) (hC' i).1,
        side_as_or I (C'.rightVars i) (C'.rightGates i) i (C'.gateVal I) (hC' i).2,
        side_as_or _ _ _ _ _ (hC (liftGate g i)).1, side_as_or _ _ _ _ _ (hC (liftGate g i)).2]
      exact and_congr left right
  change C'.eval I = C.eval (I \ N)
  apply Bool.eq_iff_iff.mpr
  simp only [AndCountCircuit.eval, decide_eq_true_eq]
  exact redirect_spec g I N V C.outVars Q C.outGates (C.gateVal (I \ N)) (C'.gateVal I)
    hQ gone (fun j _ => bound C'.size j j.isLt)

def Independent {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

def Dominates {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ x ∉ I, ∃ v ∈ I, G.Adj x v

lemma independent_extends {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n) :
    ∃ I : Finset (Fin n), w ∈ I ∧ Independent G I ∧ Dominates G I := by
  classical
  let pool := Finset.univ.filter fun I : Finset (Fin n) => w ∈ I ∧ Independent G I
  have hpool : pool.Nonempty := ⟨{w}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Independent]⟩⟩
  obtain ⟨I, hi, hmax⟩ := Finset.exists_max_image pool Finset.card hpool
  have h := (Finset.mem_filter.mp hi).2
  refine ⟨I, h.1, h.2, ?_⟩
  intro x hx
  by_contra hbad
  have hxadj (v : Fin n) (hv : v ∈ I) : ¬ G.Adj x v :=
    fun ha => hbad ⟨v, hv, ha⟩
  have hind : Independent G (insert x I) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | hA
    · rcases Finset.mem_insert.mp hb with rfl | hB
      · exact G.loopless.irrefl _
      · exact hxadj _ hB
    · rcases Finset.mem_insert.mp hb with rfl | hB
      · exact fun hab => hxadj _ hA hab.symm
      · exact h.2 _ hA _ hB
  have hm : insert x I ∈ pool :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_of_mem h.1, hind⟩
  have hc := hmax _ hm
  rw [Finset.card_insert_of_notMem hx] at hc
  omega

lemma side_insert_same {n k : ℕ} (I B : Finset (Fin n)) (u : Fin n)
    (F : Finset (Fin k)) (i : Fin k) (f : Fin k → Bool) (hB : u ∉ B) :
    AndCountCircuit.sideTrue (insert u I) B F i f =
      AndCountCircuit.sideTrue I B F i f := by
  simp only [AndCountCircuit.sideTrue, decide_eq_decide]
  have h (v : Fin n) (hv : v ∈ B) : v ∈ insert u I ↔ v ∈ I := by
    simp [Finset.mem_insert, show v ≠ u from fun he => hB (he ▸ hv)]
  exact or_congr ⟨fun ⟨v, hv, hi⟩ => ⟨v, hv, (h v hv).mp hi⟩,
    fun ⟨v, hv, hi⟩ => ⟨v, hv, (h v hv).mpr hi⟩⟩ Iff.rfl

lemma has_bare {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (u w : Fin n) (huw : G.Adj u w)
    (hC : ∀ I, Independent G I → Dominates G I →
      C.eval I = false ∧ ∀ x ∉ I, C.eval (insert x I) = true) :
    ∃ g : Fin C.size, u ∈ C.leftVars g ∨ u ∈ C.rightVars g := by
  obtain ⟨J, hj, hind, hdom⟩ := independent_extends G u
  have hout : u ∉ C.outVars := by
    intro h
    have he : C.eval J = true := by
      unfold AndCountCircuit.eval
      exact decide_eq_true (Or.inl ⟨u, h, hj⟩)
    rw [(hC J hind hdom).1] at he
    contradiction
  obtain ⟨I, hi, hind, hdom⟩ := independent_extends G w
  have hu : u ∉ I := fun huu => hind u huu w hi huw
  by_contra h
  have hval : ∀ b (g : Fin C.size), C.gateValFuel (insert u I) b g = C.gateValFuel I b g := by
    intro b
    induction b with
    | zero => intro g; rfl
    | succ b ih =>
      intro g
      have hl : u ∉ C.leftVars g := fun hh => h ⟨g, Or.inl hh⟩
      have hr : u ∉ C.rightVars g := fun hh => h ⟨g, Or.inr hh⟩
      simp only [AndCountCircuit.gateValFuel]
      rw [funext ih, side_insert_same I _ u _ g _ hl, side_insert_same I _ u _ g _ hr]
  have he : C.eval (insert u I) = C.eval I := by
    unfold AndCountCircuit.eval
    rw [decide_eq_decide]
    simp only [AndCountCircuit.gateVal, hval]
    have hh (v : Fin n) (hv : v ∈ C.outVars) : v ∈ insert u I ↔ v ∈ I := by
      simp [Finset.mem_insert, show v ≠ u from fun eq => hout (eq ▸ hv)]
    exact or_congr ⟨fun ⟨v, hv, hi⟩ => ⟨v, hv, (hh v hv).mp hi⟩,
      fun ⟨v, hv, hi⟩ => ⟨v, hv, (hh v hv).mpr hi⟩⟩ Iff.rfl
  rw [(hC I hind hdom).2 u hu, (hC I hind hdom).1] at he
  contradiction

end PEqualNP.Outside.L_meta_705_aux

open PEqualNP.Outside.L_meta_705_aux PEqualNP.AndCount in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_705 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n), (∃ w : Fin n, G.Adj u w) →
    ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        C.eval I = false ∧ ∀ x : Fin n, x ∉ I → C.eval (insert x I) = true) →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n, C'.WellFormed ∧ C'.size + 1 ≤ C.size ∧
        ∀ I : Finset (Fin n),
          (∀ v ∈ I, ∀ w ∈ I, ¬ (G.Adj v w ∧ v ≠ u ∧ ¬ G.Adj u v ∧ w ≠ u ∧ ¬ G.Adj u w)) →
          (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v ∧ x ≠ u ∧ ¬ G.Adj u x ∧ v ≠ u ∧ ¬ G.Adj u v) →
          C'.eval I = false ∧ ∀ x : Fin n, x ∉ I → C'.eval (insert x I) = true := by
  classical
  rintro n G u ⟨w, hw⟩ C hC htest
  obtain ⟨g, hbare⟩ := has_bare G C u w hw htest
  have replacement :
      ∃ (V : Finset (Fin n)) (Q : Finset (Fin C.size)), (∀ i ∈ Q, i < g) ∧
        ∀ J : Finset (Fin n), u ∈ J →
          (C.gateVal J g = true ↔ orValue J V Q (C.gateVal J)) := by
    rcases hbare with hl | hr
    · refine ⟨C.rightVars g, C.rightGates g, (hC g).2, ?_⟩
      intro J hu
      have hleft : AndCountCircuit.sideTrue J (C.leftVars g) (C.leftGates g) g (C.gateVal J) = true :=
        (side_as_or _ _ _ _ _ (hC g).1).mpr (Or.inl ⟨u, hl, hu⟩)
      rw [gateVal_eq C J g, hleft, Bool.true_and, side_as_or _ _ _ _ _ (hC g).2]
    · refine ⟨C.leftVars g, C.leftGates g, (hC g).1, ?_⟩
      intro J hu
      have hright : AndCountCircuit.sideTrue J (C.rightVars g) (C.rightGates g) g (C.gateVal J) = true :=
        (side_as_or _ _ _ _ _ (hC g).2).mpr (Or.inl ⟨u, hr, hu⟩)
      rw [gateVal_eq C J g, hright, Bool.and_true, side_as_or _ _ _ _ _ (hC g).1]
  obtain ⟨V, Q, hQ, hreplace⟩ := replacement
  let N := Finset.univ.filter (G.Adj u)
  have neigh (v : Fin n) : v ∈ N ↔ G.Adj u v := by simp [N]
  have huN : u ∉ N := fun h => G.loopless.irrefl u ((neigh u).mp h)
  let C' := splice C g N V Q
  refine ⟨C', splice_wf C g N V Q hC hQ, ?_, ?_⟩
  · change (retained g).card + 1 ≤ C.size
    have hg : 0 < C.size := Fin.pos g
    simp [retained]
    omega
  · intro I hind hmax
    have huI : u ∈ I := by
      by_contra hm
      obtain ⟨_, _, _, hne, _⟩ := hmax u hm
      exact hne rfl
    let J := I \ N
    have huJ : u ∈ J := Finset.mem_sdiff.mpr ⟨huI, huN⟩
    have hJind : Independent G J := by
      intro a ha b hb hadj
      obtain ⟨hai, han⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hbi, hbn⟩ := Finset.mem_sdiff.mp hb
      by_cases hae : a = u
      · subst a
        exact hbn ((neigh b).mpr hadj)
      by_cases hbe : b = u
      · subst b
        exact han ((neigh a).mpr hadj.symm)
      exact hind a hai b hbi ⟨hadj, hae, fun h => han ((neigh a).mpr h),
        hbe, fun h => hbn ((neigh b).mpr h)⟩
    have hJmax : Dominates G J := by
      intro x hx
      by_cases hn : x ∈ N
      · exact ⟨u, huJ, ((neigh x).mp hn).symm⟩
      · have hi : x ∉ I := fun h => hx (Finset.mem_sdiff.mpr ⟨h, hn⟩)
        obtain ⟨v, hv, ha, _, _, _, hn'⟩ := hmax x hi
        exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, fun h => hn' ((neigh v).mp h)⟩, ha⟩
    have heval (T : Finset (Fin n)) (huT : u ∈ T) : C'.eval T = C.eval (T \ N) :=
      splice_eval C g T N V Q hC hQ (hreplace _ (Finset.mem_sdiff.mpr ⟨huT, huN⟩))
    obtain ⟨hfalse, htrue⟩ := htest J hJind hJmax
    refine ⟨(heval I huI).trans hfalse, ?_⟩
    intro x hx
    have hxn : x ∉ N := by
      obtain ⟨_, _, _, _, hn, _⟩ := hmax x hx
      exact fun h => hn ((neigh x).mp h)
    have hdiff : insert x I \ N = insert x J := by
      ext y
      by_cases hy : y = x
      · simp [hy, hxn]
      · simp [hy, J]
    rw [heval _ (Finset.mem_insert_of_mem huI), hdiff]
    exact htrue x (fun h => hx (Finset.mem_sdiff.mp h).1)
