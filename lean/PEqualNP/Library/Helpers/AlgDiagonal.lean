import PEqualNP.Defs
import PEqualNP.Library.L060
import PEqualNP.Library.Helpers.BGSDiagonal
import PEqualNP.Library.Helpers.AlgDiagonalParse

/-!
# The algebrization diagonal

Helper module (proofs only, no statement may use it). From deciders `g i`, uniform in the
oracle, each depending on the oracle through at most `q i (length of x)` strings, and from an
injective naming of field elements, an oracle `A` and a multiquadratic extension `E` of `A` are
built in stages so that no `g i` relative to `extOracle codes E` is the length test of `A`
(Aaronson and Wigderson 2009, Theorem 5.3). With `L060` this gives `of_enum`.

Stage `i` holds the oracle so far, its extension (zero at every length not fixed yet) and a
bound `N` above every fixed length and every arity named by an earlier query. It picks
`n ≥ N` with `q i n < 2 ^ n` and asks `g i` about the string of `n` trues. If `g i` says yes,
length `n` stays empty. Otherwise one cube point `w` and polynomials vanishing on every queried
point of arity `n` are chosen (`L064`), and length `n` gets the string of `w`.
-/

namespace PEqualNP.Library.Helpers.AlgDiagonal

open Classical PEqualNP.Library PEqualNP.Library.Helpers.AlgDiagonalParse

/-- The state after a stage. -/
structure St where
  /-- The oracle so far. -/
  A : Language Bool
  /-- Its extension so far. -/
  E : AlgExtension
  /-- The bound. -/
  N : ℕ

/-- The oracle `A` with the string `w` added. -/
def addStr (A : Language Bool) (w : List Bool) : Language Bool := {y | y ∈ A ∨ y = w}

theorem mem_addStr {A : Language Bool} {w y : List Bool} : y ∈ addStr A w ↔ y ∈ A ∨ y = w :=
  Iff.rfl

/-- The empty oracle. -/
def noStr : Language Bool := {_y | False}

theorem not_mem_noStr (y : List Bool) : y ∉ noStr := fun h => h

/-- The arity a string names, `0` when it names none. -/
noncomputable def arity (s : List Bool) : ℕ := ((hdr s).map fun t => t.2.2).getD 0

/-- The extension `s.E` with arity `n` replaced by `P`. -/
noncomputable def newE (s : St) (n : ℕ)
    (P : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), MvPolynomial (Fin n) (GaloisField p k)) :
    AlgExtension :=
  fun (p : ℕ) [Fact p.Prime] (k m : ℕ) => if h : n = m then h ▸ P p k else s.E p k m

theorem newE_self (s : St) (n : ℕ)
    (P : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), MvPolynomial (Fin n) (GaloisField p k))
    (p : ℕ) [Fact p.Prime] (k : ℕ) : newE s n P p k n = P p k := by
  simp [newE]

theorem newE_ne (s : St) (n : ℕ)
    (P : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), MvPolynomial (Fin n) (GaloisField p k))
    (p : ℕ) [Fact p.Prime] (k m : ℕ) (h : m ≠ n) : newE s n P p k m = s.E p k m := by
  simp [newE, Ne.symm h]

variable (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ)
  (Qf : ℕ → Language Bool → List Bool → Finset (List Bool)) (codes : FieldCodes)

/-- The cube point chosen at length `n` against the queries `Qs`. -/
noncomputable def wOf (n : ℕ) (Qs : Finset (List Bool)) : Fin n → Bool :=
  if h : ∃ w : Fin n → Bool, ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), ∃ P, Good (Yq codes n Qs p k) w P
  then Classical.choose h else fun _ => false

/-- The polynomial chosen at length `n` against the queries `Qs`. -/
noncomputable def polyOf (n : ℕ) (Qs : Finset (List Bool)) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    MvPolynomial (Fin n) (GaloisField p k) :=
  if h : ∃ P, Good (Yq codes n Qs p k) (wOf codes n Qs) P then Classical.choose h else 0

theorem polyOf_good (n : ℕ) (Qs : Finset (List Bool)) (hQ : Qs.card < 2 ^ n) (p : ℕ)
    [Fact p.Prime] (k : ℕ) : Good (Yq codes n Qs p k) (wOf codes n Qs) (polyOf codes n Qs p k) := by
  have hex : ∃ w : Fin n → Bool, ∀ (p : ℕ) [Fact p.Prime] (k : ℕ),
      ∃ P, Good (Yq codes n Qs p k) w P :=
    evade n (names Qs) (names_prime Qs)
      (fun pk => (Qs.filter fun s => hdr s = some (pk.1, pk.2, n)).card) (Yq codes n Qs)
      (fun p _ k => card_Yq codes n Qs p k) (fun p _ k h => Yq_empty codes n Qs p k h)
      (lt_of_le_of_lt (sum_filter_le _ Qs n) hQ)
  have hw : wOf codes n Qs = Classical.choose hex := dite_eq_left_of_eq_true (eq_true hex) ..
  have h1 : ∃ P, Good (Yq codes n Qs p k) (wOf codes n Qs) P := by
    rw [hw]; exact Classical.choose_spec hex p k
  unfold polyOf
  rw [dite_eq_left_of_eq_true (eq_true h1)]
  exact Classical.choose_spec h1

/-- The length stage `i` works at. -/
noncomputable def nOf (i : ℕ) (s : St) : ℕ := BGS.len q i s.N

/-- The input stage `i` diagonalizes on. -/
noncomputable def xOf (i : ℕ) (s : St) : List Bool := List.replicate (nOf q i s) true

/-- The strings stage `i` depends on. -/
noncomputable def qOf (i : ℕ) (s : St) : Finset (List Bool) :=
  Qf i (extOracle codes s.E) (xOf q i s)

/-- One stage. -/
noncomputable def stepSt (i : ℕ) (s : St) : St :=
  if xOf q i s ∈ g i (extOracle codes s.E) then
    ⟨s.A, s.E, max (nOf q i s) ((qOf q Qf codes i s).sup arity) + 1⟩
  else
    ⟨addStr s.A (List.ofFn (wOf codes (nOf q i s) (qOf q Qf codes i s))),
      newE s (nOf q i s) (polyOf codes (nOf q i s) (qOf q Qf codes i s)),
      max (nOf q i s) ((qOf q Qf codes i s).sup arity) + 1⟩

/-- The states after each stage. -/
noncomputable def stages : ℕ → St
  | 0 => ⟨noStr, fun (p : ℕ) [Fact p.Prime] (k m : ℕ) => (0 : MvPolynomial (Fin m) (GaloisField p k)), 0⟩
  | i + 1 => stepSt g q Qf codes i (stages i)

theorem stages_succ (i : ℕ) :
    stages g q Qf codes (i + 1) = stepSt g q Qf codes i (stages g q Qf codes i) := rfl

theorem stepSt_N (i : ℕ) (s : St) :
    (stepSt g q Qf codes i s).N = max (nOf q i s) ((qOf q Qf codes i s).sup arity) + 1 := by
  unfold stepSt; split_ifs <;> rfl

/-- Two states agree at length `m`. -/
def AgreeAt (s t : St) (m : ℕ) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), s.E p k m = t.E p k m) ∧
    ∀ x : List Bool, x.length = m → (x ∈ s.A ↔ x ∈ t.A)

theorem AgreeAt.trans {s t u : St} {m : ℕ} (h1 : AgreeAt s t m) (h2 : AgreeAt t u m) :
    AgreeAt s u m :=
  ⟨fun p _ k => (h1.1 p k).trans (h2.1 p k), fun x hx => (h1.2 x hx).trans (h2.2 x hx)⟩

theorem AgreeAt.symm {s t : St} {m : ℕ} (h : AgreeAt s t m) : AgreeAt t s m :=
  ⟨fun p _ k => (h.1 p k).symm, fun x hx => (h.2 x hx).symm⟩

theorem step_agree (i : ℕ) (s : St) (m : ℕ) (hm : m ≠ nOf q i s) :
    AgreeAt (stepSt g q Qf codes i s) s m := by
  unfold stepSt
  split_ifs
  · exact ⟨fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩
  · refine ⟨fun p _ k => newE_ne s _ _ p k m hm, fun x hx => ?_⟩
    rw [mem_addStr]
    have : x ≠ List.ofFn (wOf codes (nOf q i s) (qOf q Qf codes i s)) := by
      intro h
      have := congrArg List.length h
      rw [List.length_ofFn, hx] at this
      exact hm this
    simp [this]

theorem n_lt_N_succ (i : ℕ) :
    nOf q i (stages g q Qf codes i) < (stages g q Qf codes (i + 1)).N := by
  rw [stages_succ, stepSt_N]
  exact Nat.lt_succ_of_le (le_max_left _ _)

theorem N_le_n (i : ℕ) (s : St) : s.N ≤ nOf q i s := BGS.len_ge q i s.N

theorem N_le_succ (i : ℕ) : (stages g q Qf codes i).N ≤ (stages g q Qf codes (i + 1)).N :=
  (N_le_n q i _).trans (n_lt_N_succ g q Qf codes i).le

theorem N_mono {i j : ℕ} (h : i ≤ j) : (stages g q Qf codes i).N ≤ (stages g q Qf codes j).N :=
  monotone_nat_of_le_succ (fun k => N_le_succ g q Qf codes k) h

theorem index_le_N (i : ℕ) : i ≤ (stages g q Qf codes i).N := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have := (N_le_n q k (stages g q Qf codes k)).trans_lt (n_lt_N_succ g q Qf codes k)
    omega

theorem agree_later {i j : ℕ} (hij : i ≤ j) {m : ℕ} (hm : m < (stages g q Qf codes i).N) :
    AgreeAt (stages g q Qf codes j) (stages g q Qf codes i) m := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨fun _ _ _ => rfl, fun _ _ => Iff.rfl⟩
  | succ j hij ih =>
    refine AgreeAt.trans ?_ ih
    rw [stages_succ]
    apply step_agree
    have h1 := N_mono g q Qf codes hij
    have h2 := N_le_n q j (stages g q Qf codes j)
    omega

/-- The final oracle. -/
noncomputable def finA : Language Bool := {x | x ∈ (stages g q Qf codes (x.length + 1)).A}

/-- The final extension. -/
noncomputable def finE : AlgExtension :=
  fun (p : ℕ) [Fact p.Prime] (k m : ℕ) => (stages g q Qf codes (m + 1)).E p k m

theorem fin_agree {i m : ℕ} (hm : m < (stages g q Qf codes i).N) :
    (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), finE g q Qf codes p k m = (stages g q Qf codes i).E p k m) ∧
      ∀ x : List Bool, x.length = m → (x ∈ finA g q Qf codes ↔ x ∈ (stages g q Qf codes i).A) := by
  have hm1 : m < (stages g q Qf codes (m + 1)).N := by
    have := index_le_N g q Qf codes (m + 1); omega
  have h1 := agree_later g q Qf codes (le_max_left i (m + 1)) hm
  have h2 := agree_later g q Qf codes (le_max_right i (m + 1)) hm1
  have h3 := h2.symm.trans h1
  refine ⟨fun p _ k => h3.1 p k, fun x hx => ?_⟩
  show x ∈ (stages g q Qf codes (x.length + 1)).A ↔ _
  rw [hx]
  exact h3.2 x hx

/-- The invariant of every stage. -/
def Inv (s : St) : Prop :=
  (∀ y ∈ s.A, y.length < s.N) ∧
    (∀ (p : ℕ) [Fact p.Prime] (k m : ℕ), s.N ≤ m → s.E p k m = 0) ∧
    ∀ (p : ℕ) [Fact p.Prime] (k m : ℕ), (∀ i : Fin m, MvPolynomial.degreeOf i (s.E p k m) ≤ 2) ∧
      ∀ x : Fin m → Bool,
        MvPolynomial.eval (fun i => if x i then (1 : GaloisField p k) else 0) (s.E p k m) =
          if List.ofFn x ∈ s.A then 1 else 0

section
variable (hQcard : ∀ i A x, (Qf i A x).card ≤ (q i).eval x.length)
include hQcard

theorem card_lt (i : ℕ) (s : St) : (qOf q Qf codes i s).card < 2 ^ nOf q i s := by
  have h := hQcard i (extOracle codes s.E) (xOf q i s)
  have hl : (xOf q i s).length = nOf q i s := List.length_replicate
  rw [hl] at h
  exact lt_of_le_of_lt h (BGS.len_lt q i s.N)

theorem inv_step (i : ℕ) (s : St) (hs : Inv s) : Inv (stepSt g q Qf codes i s) := by
  obtain ⟨hA, hE, hM⟩ := hs
  have hn := N_le_n q i s
  unfold stepSt
  split_ifs with hx
  · refine ⟨fun y hy => ?_, fun p _ k m hm => hE p k m (by simp only at hm; omega), hM⟩
    have := hA y hy
    show y.length < max _ _ + 1
    omega
  · set n := nOf q i s with hn_def
    set Qs := qOf q Qf codes i s
    have hgood := polyOf_good codes n Qs (card_lt q Qf codes hQcard i s)
    refine ⟨fun y hy => ?_, fun p _ k m hm => ?_, fun p _ k m => ?_⟩
    · show y.length < max _ _ + 1
      rcases mem_addStr.mp hy with hy | rfl
      · have := hA y hy; omega
      · rw [List.length_ofFn]; omega
    · simp only at hm
      show newE s n (polyOf codes n Qs) p k m = 0
      rw [newE_ne s n _ p k m (by omega)]
      exact hE p k m (by omega)
    · by_cases hm : m = n
      · subst hm
        show (∀ i, MvPolynomial.degreeOf i (newE s n (polyOf codes n Qs) p k n) ≤ 2) ∧ ∀ x : Fin n → Bool,
          MvPolynomial.eval (fun i => if x i then (1 : GaloisField p k) else 0)
            (newE s n (polyOf codes n Qs) p k n) =
          if List.ofFn x ∈ addStr s.A (List.ofFn (wOf codes n Qs)) then 1 else 0
        rw [newE_self]
        obtain ⟨hdeg, -, hcube⟩ := hgood p k
        refine ⟨hdeg, fun x => ?_⟩
        rw [hcube x]
        have hiff : List.ofFn x ∈ addStr s.A (List.ofFn (wOf codes n Qs))
            ↔ x = wOf codes n Qs := by
          rw [mem_addStr]
          constructor
          · rintro (h | h)
            · have := hA _ h; rw [List.length_ofFn] at this; omega
            · exact List.ofFn_injective h
          · intro h; exact Or.inr (by rw [h])
        by_cases hxw : x = wOf codes n Qs
        · rw [ite_eq_left hxw, ite_eq_left (hiff.mpr hxw)]
        · rw [ite_eq_right hxw, ite_eq_right (fun h => hxw (hiff.mp h))]
      · show (∀ i, MvPolynomial.degreeOf i (newE s n (polyOf codes n Qs) p k m) ≤ 2) ∧ ∀ x : Fin m → Bool,
          MvPolynomial.eval (fun i => if x i then (1 : GaloisField p k) else 0)
            (newE s n (polyOf codes n Qs) p k m) =
          if List.ofFn x ∈ addStr s.A (List.ofFn (wOf codes n Qs)) then 1 else 0
        rw [newE_ne s n _ p k m hm]
        obtain ⟨hdeg, hcube⟩ := hM p k m
        refine ⟨hdeg, fun x => ?_⟩
        rw [hcube x]
        have hne : List.ofFn x ≠ List.ofFn (wOf codes n Qs) := by
          intro h
          have := congrArg List.length h
          rw [List.length_ofFn, List.length_ofFn] at this
          exact hm this
        have hiff : List.ofFn x ∈ addStr s.A (List.ofFn (wOf codes n Qs))
            ↔ List.ofFn x ∈ s.A := by
          rw [mem_addStr]
          simp [hne]
        by_cases hx' : List.ofFn x ∈ s.A
        · rw [ite_eq_left hx', ite_eq_left (hiff.mpr hx')]
        · rw [ite_eq_right hx', ite_eq_right (fun h => hx' (hiff.mp h))]

theorem inv_stages (i : ℕ) : Inv (stages g q Qf codes i) := by
  induction i with
  | zero =>
    refine ⟨fun y hy => absurd hy (not_mem_noStr y), fun _ _ _ _ _ => rfl, fun p _ k m => ?_⟩
    refine ⟨fun i => by simp [stages], fun x => ?_⟩
    have : List.ofFn x ∉ (stages g q Qf codes 0).A := not_mem_noStr _
    rw [ite_eq_right this]
    simp [stages]
  | succ k ih => exact inv_step g q Qf codes hQcard k _ ih

end

/-- The diagonal. -/
theorem diagonal
    (henc : ∀ (a b : ℕ) (s t : List Bool),
      algEncodeNat a ++ s = algEncodeNat b ++ t → a = b ∧ s = t)
    (hloc : ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool),
      Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') →
        (x ∈ g i A ↔ x ∈ g i A'))
    (hc : FieldCodes.Injective codes) :
    ∃ (A : Language Bool) (E : AlgExtension), IsMultiquadraticExtension A E ∧
      ∀ i, g i (extOracle codes E) ≠ {x : List Bool | ∃ w ∈ A, w.length = x.length} := by
  choose Qf hQcard hQagree using hloc
  refine ⟨finA g q Qf codes, finE g q Qf codes, fun p _ k m => ?_, fun i heq => ?_⟩
  · have hm1 : m < (stages g q Qf codes (m + 1)).N := by
      have := index_le_N g q Qf codes (m + 1); omega
    obtain ⟨hdeg, hcube⟩ := (inv_stages g q Qf codes hQcard (m + 1)).2.2 p k m
    refine ⟨hdeg, fun x => ?_⟩
    have hfin := (fin_agree g q Qf codes hm1).2 (List.ofFn x) (List.length_ofFn)
    show MvPolynomial.eval _ ((stages g q Qf codes (m + 1)).E p k m) = _
    rw [hcube x]
    by_cases hx' : List.ofFn x ∈ (stages g q Qf codes (m + 1)).A
    · rw [ite_eq_left hx', ite_eq_left (hfin.mpr hx')]
    · rw [ite_eq_right hx', ite_eq_right (fun h => hx' (hfin.mp h))]
  · set s := stages g q Qf codes i with hs_def
    set n := nOf q i s
    set x := xOf q i s
    set Qs := qOf q Qf codes i s
    have hinv := inv_stages g q Qf codes hQcard i
    rw [← hs_def] at hinv
    have hN1 : (stages g q Qf codes (i + 1)).N = max n (Qs.sup arity) + 1 := by
      rw [stages_succ, ← hs_def, stepSt_N]
    have hnN : s.N ≤ n := N_le_n q i s
    have hxlen : x.length = n := List.length_replicate
    -- The final extension agrees with stage `i` on the queries of stage `i`.
    have agree : ∀ y ∈ Qs, y ∈ extOracle codes s.E ↔ y ∈ extOracle codes (finE g q Qf codes) := by
      intro y hyQ
      apply extOracle_congr
      intro p _ k m pt j hy
      have hmle : m < (stages g q Qf codes (i + 1)).N := by
        have h1 : arity y = m := by
          rw [arity, hy, hdr_qstr henc]; rfl
        have h2 : arity y ≤ Qs.sup arity := Finset.le_sup (f := arity) hyQ
        omega
      have hfin := (fin_agree g q Qf codes hmle).1 p k
      rw [hfin, stages_succ, ← hs_def]
      by_cases hmn : m = n
      · subst hmn
        rw [hinv.2.1 p k _ hnN]
        unfold stepSt
        split_ifs
        · simp only [hinv.2.1 p k _ hnN]
        · simp only
          rw [newE_self]
          rw [hy] at hyQ
          rw [map_zero, (polyOf_good codes _ Qs (card_lt q Qf codes hQcard i s) p k).2.1 pt
            (mem_Yq henc codes _ Qs p k (hc p k) pt j hyQ)]
      · rw [(step_agree g q Qf codes i s m hmn).1 p k]
    have hg := hQagree i (extOracle codes s.E) x (extOracle codes (finE g q Qf codes)) agree
    have hL : x ∈ g i (extOracle codes (finE g q Qf codes)) ↔
        ∃ w ∈ (stages g q Qf codes (i + 1)).A, w.length = n := by
      rw [heq]
      show (∃ w ∈ finA g q Qf codes, w.length = x.length) ↔ _
      rw [hxlen]
      have hnlt : n < (stages g q Qf codes (i + 1)).N := by rw [hN1]; omega
      have hfin := (fin_agree g q Qf codes hnlt).2
      constructor
      · rintro ⟨w, hw, hwl⟩; exact ⟨w, (hfin w hwl).mp hw, hwl⟩
      · rintro ⟨w, hw, hwl⟩; exact ⟨w, (hfin w hwl).mpr hw, hwl⟩
    rw [stages_succ, ← hs_def] at hL
    unfold stepSt at hL
    by_cases hx : x ∈ g i (extOracle codes s.E)
    · rw [ite_eq_left hx] at hL
      obtain ⟨w, hw, hwl⟩ := hL.mp (hg.mp hx)
      have := hinv.1 w hw
      omega
    · rw [ite_eq_right hx] at hL
      apply hx
      apply hg.mpr
      apply hL.mpr
      exact ⟨_, Or.inr rfl, List.length_ofFn⟩

/-- The algebrization diagonal from the oracle machine enumeration. -/
theorem of_enum (henc : ∀ (a b : ℕ) (s t : List Bool), PEqualNP.Library.algEncodeNat a ++ s = PEqualNP.Library.algEncodeNat b ++ t → a = b ∧ s = t) : (∃ (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ), (∀ (A L : Language Bool), L ∈ PEqualNP.Library.OracleP A → ∃ i : ℕ, g i A = L) ∧ ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool), Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') → (x ∈ g i A ↔ x ∈ g i A')) → ∀ codes : PEqualNP.Library.FieldCodes, PEqualNP.Library.FieldCodes.Injective codes → ∃ (A : Language Bool) (E : PEqualNP.Library.AlgExtension), PEqualNP.Library.IsMultiquadraticExtension A E ∧ ¬ PEqualNP.Library.OracleNP A ⊆ PEqualNP.Library.OracleP (PEqualNP.Library.extOracle codes E) := by
  rintro ⟨g, q, hcov, hloc⟩ codes hc
  obtain ⟨A, E, hAE, hB⟩ := diagonal g q codes henc hloc hc
  refine ⟨A, E, hAE, fun hsub => ?_⟩
  obtain ⟨i, hi⟩ := hcov _ _ (hsub (PEqualNP.Library.L060 A))
  exact hB i hi

end PEqualNP.Library.Helpers.AlgDiagonal
