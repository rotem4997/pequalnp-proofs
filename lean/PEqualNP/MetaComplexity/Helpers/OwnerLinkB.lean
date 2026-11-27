import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkDefs

/-!
# The owner link, clause (b): every owner list has at least two entries, all below the count

Conjecture until a seat's checker accepts a row. `OWN` is restated through named pieces
(`OWN_eq`, by `rfl`), then the two facts are proved for any formula whose positions fit below
`E` and whose literal variables are at most `E` (`own_len_bound`), and those two conditions are
proved for `REN φ` with `E` the code length (`gOwnB`).
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

/-- The slot index of the term. -/
def Xf (E k u v t : ℕ) : ℕ := 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + t - 1

/-- The `inner` triples of the term. -/
def innerF (E k u v : ℕ) (inT : Bool) : List (List ℕ) :=
  ((List.range (2 * k)).filter (fun s : ℕ => decide ((s + 1) % 2 = 0 ↔ inT = true))).map
    (fun s : ℕ => [Xf E k u v (s + 1), if s = 0 then u else Xf E k u v s,
      if s + 1 = 2 * k then v else Xf E k u v (s + 2)])

def offF (ψ : CNF) (i : ℕ) : ℕ := ((ψ.take i).map (fun c : Clause => c.length + 1)).sum
def posF (E : ℕ) (ψ : CNF) (i j : ℕ) : ℕ := 2 * (E + 1) + offF ψ i + j
def litF (ψ : CNF) (i j : ℕ) : Literal := (ψ.getD i []).getD j (0, false)
def wF (ψ : CNF) (i : ℕ) : ℕ := (ψ.getD i []).length
def fF (ψ : CNF) (i : ℕ) : ℕ := (ψ.getD i []).findIdx (fun l : Literal => l.2)

/-- The hub owner list of item `(i, j)` (present when `j ≠ f i`). -/
def hubL (E k : ℕ) (ψ : CNF) (i j : ℕ) : List ℕ :=
  posF E ψ i j :: ((if j < wF ψ i ∧ (litF ψ i j).2 = false then
      [Xf E k (2 * (litF ψ i j).1) (posF E ψ i j) (2 * k)] else []) ++
    (if fF ψ i < j then [Xf E k (posF E ψ i (fF ψ i)) (posF E ψ i j) (2 * k)] else []) ++
    ((List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l))).map
      (fun l : ℕ => Xf E k (posF E ψ i j) (posF E ψ i l) 1))

/-- The variable owner list of item `(i, j)` (present at the earliest occurrence). -/
def varL (E k : ℕ) (ψ : CNF) (i j : ℕ) : List ℕ :=
  (2 * (litF ψ i j).1 + 1) :: Xf E k (2 * (litF ψ i j).1) (2 * (litF ψ i j).1 + 1) (2 * k) ::
    (List.range ψ.length).flatMap (fun i' : ℕ => ((List.range (wF ψ i')).filter
      (fun j' : ℕ => decide ((litF ψ i' j').1 = (litF ψ i j).1 ∧ (litF ψ i' j').2 = true))).map
        (fun j' : ℕ => Xf E k (2 * (litF ψ i j).1 + 1) (posF E ψ i' j') 1))

/-- The lists of item `(i, j)`. -/
def itemF (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  (if j < wF ψ i then
      innerF E k (2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0)) (posF E ψ i j)
        (litF ψ i j).2
    else innerF E k (2 * E + 1) (posF E ψ i j) true) ++
  ((List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l))).flatMap
      (fun l : ℕ => innerF E k (posF E ψ i j) (posF E ψ i l) (decide (j ≠ fF ψ i))) ++
  (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then
      innerF E k (2 * (litF ψ i j).1) (2 * (litF ψ i j).1 + 1) false else []) ++
  (if j ≠ fF ψ i then [hubL E k ψ i j] else []) ++
  (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then [varL E k ψ i j] else [])

/-- `OWN` through the named pieces (same grouping: `++` is left associative). -/
def OWN' (E k : ℕ) (ψ : CNF) : List (List ℕ) :=
  (List.range ψ.length).flatMap (fun i : ℕ =>
    (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => itemF E k ψ i j)) ++
  innerF E k (2 * E) (2 * E + 1) false ++ innerF E k (2 * E) (3 * E + 2) false ++
    [(2 * E + 1) :: Xf E k (2 * E) (2 * E + 1) (2 * k) ::
      (List.range ψ.length).map (fun i : ℕ => Xf E k (2 * E + 1) (posF E ψ i (wF ψ i)) 1)] ++
    [[3 * E + 2, Xf E k (2 * E) (3 * E + 2) (2 * k)]]

theorem OWN_eq (E k : ℕ) (ψ : CNF) : OWN E k ψ = OWN' E k ψ := by
  delta OWN OWN' itemF hubL varL innerF Xf offF posF litF wF fF
  rfl

/-- The slot index stays below the vertex count. -/
theorem Xf_lt {E k u v t : ℕ} (hu : u < 3 * (E + 1)) (hv : v < 3 * (E + 1)) (ht1 : 1 ≤ t)
    (ht : t ≤ 2 * k) :
    Xf E k u v t < 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) := by
  unfold Xf
  generalize 3 * (E + 1) = N at *
  have h1 : u * N + v + 1 ≤ N * N := by nlinarith
  have h2 : 2 * k * (u * N + v + 1) ≤ 2 * k * (N * N) := Nat.mul_le_mul_left _ h1
  have h3 : 2 * k * (u * N + v + 1) = 2 * k * (u * N + v) + 2 * k := by ring
  have h4 : 2 * k * (N * N) = 2 * k * N * N := by ring
  omega

theorem innerF_mem {E k u v : ℕ} {b : Bool} {l : List ℕ} (h : l ∈ innerF E k u v b)
    (hu : u < 3 * (E + 1)) (hv : v < 3 * (E + 1)) :
    2 ≤ l.length ∧ ∀ x ∈ l, x < 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) := by
  unfold innerF at h
  simp only [List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨s, ⟨hs, -⟩, rfl⟩ := h
  refine ⟨by simp, ?_⟩
  have hM : 3 * (E + 1) ≤ 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) := by omega
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Xf_lt hu hv (by omega) (by omega)
  · split_ifs
    · omega
    · exact Xf_lt hu hv (by omega) (by omega)
  · split_ifs with h
    · omega
    · exact Xf_lt hu hv (by omega) (by omega)

/-- Clause (b) for any formula whose positions and variables fit. -/
theorem own_len_bound (E k : ℕ) (ψ : CNF) (hk : 1 ≤ k)
    (hpos : ∀ i, i < ψ.length → ∀ j, j ≤ wF ψ i → offF ψ i + j ≤ E)
    (hvar : ∀ i, i < ψ.length → ∀ j, j < wF ψ i → (litF ψ i j).1 ≤ E) :
    ∀ l ∈ OWN E k ψ, 2 ≤ l.length ∧
      ∀ x ∈ l, x < 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) := by
  have hM : 3 * (E + 1) ≤ 3 * (E + 1) + 2 * k * (3 * (E + 1)) * (3 * (E + 1)) := by omega
  have hP : ∀ i, i < ψ.length → ∀ j, j ≤ wF ψ i → posF E ψ i j < 3 * (E + 1) := by
    intro i hi j hj; have := hpos i hi j hj; unfold posF; omega
  intro l hl
  rw [OWN_eq] at hl
  simp only [OWN', List.mem_append, List.mem_flatMap, List.mem_range, List.mem_singleton] at hl
  rcases hl with (((⟨i, hi, j, hj, hl⟩ | hl) | hl) | rfl) | rfl
  · have hj' : j ≤ wF ψ i := by omega
    have hpij := hP i hi j hj'
    simp only [itemF, List.mem_append] at hl
    rcases hl with (((hl | hl) | hl) | hl) | hl
    · split_ifs at hl with hjw
      all_goals first
        | exact innerF_mem hl (by have := hvar i hi j hjw; omega) hpij
        | exact innerF_mem hl (by omega) hpij
    · simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
      obtain ⟨l', ⟨hl', -⟩, hl⟩ := hl
      exact innerF_mem hl hpij (hP i hi l' (by omega))
    · split_ifs at hl with hc
      · have := hvar i hi j hc.1
        exact innerF_mem hl (by omega) (by omega)
      · simp at hl
    · split_ifs at hl with hc
      · simp only [List.mem_singleton] at hl
        subst hl
        have hf : fF ψ i ≤ wF ψ i := List.findIdx_le_length
        refine ⟨?_, ?_⟩
        · by_cases hjw : j < wF ψ i
          · have : wF ψ i ∈ (List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l)) := by
              simp [hjw]
            obtain ⟨as, bs, hab⟩ := List.mem_iff_append.mp this
            simp only [hubL, hab, List.map_append, List.map_cons, List.length_cons,
              List.length_append]
            omega
          · have hlt : fF ψ i < j := by omega
            simp only [hubL, hlt, if_true, List.length_cons, List.length_append,
              List.length_singleton]
            omega
        · intro x hx
          simp only [hubL, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter,
            List.mem_range, decide_eq_true_eq] at hx
          rcases hx with rfl | (hx | hx) | hx
          · omega
          · split_ifs at hx with hc'
            · simp only [List.mem_singleton] at hx; subst hx
              have := hvar i hi j hc'.1
              exact Xf_lt (by omega) hpij (by omega) (by omega)
            · simp at hx
          · split_ifs at hx with hc'
            · simp only [List.mem_singleton] at hx; subst hx
              exact Xf_lt (hP i hi _ hf) hpij (by omega) (by omega)
            · simp at hx
          · obtain ⟨l', ⟨hl', -⟩, rfl⟩ := hx
            exact Xf_lt hpij (hP i hi l' (by omega)) (by omega) (by omega)
      · simp at hl
    · split_ifs at hl with hc
      · simp only [List.mem_singleton] at hl
        subst hl
        have hz := hvar i hi j hc.1
        refine ⟨by simp [varL], ?_⟩
        intro x hx
        simp only [varL, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter,
          List.mem_range] at hx
        rcases hx with rfl | rfl | ⟨i', hi', j', ⟨hj', -⟩, rfl⟩
        · omega
        · exact Xf_lt (by omega) (by omega) (by omega) (by omega)
        · exact Xf_lt (by omega) (hP i' hi' j' (by omega)) (by omega) (by omega)
      · simp at hl
  · exact innerF_mem hl (by omega) (by omega)
  · exact innerF_mem hl (by omega) (by omega)
  · refine ⟨by simp, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hx
    rcases hx with rfl | rfl | ⟨i, hi, rfl⟩
    · omega
    · exact Xf_lt (by omega) (by omega) (by omega) (by omega)
    · exact Xf_lt (by omega) (hP i hi _ le_rfl) (by omega) (by omega)
  · refine ⟨by simp, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · omega
    · exact Xf_lt (by omega) (by omega) (by omega) (by omega)

/-- The total item count `I` of a formula. -/
def itemsF (φ : CNF) : ℕ := (φ.map (fun c : Clause => c.length + 1)).sum

theorem off_add_le (φ : CNF) : ∀ i, i < φ.length → offF φ i + wF φ i + 1 ≤ itemsF φ := by
  induction φ with
  | nil => intro i hi; simp at hi
  | cons c φ ih =>
    intro i hi
    cases i with
    | zero => simp [offF, wF, itemsF]
    | succ i =>
      have := ih i (by simpa using hi)
      simp only [offF, wF, itemsF, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getD_cons_succ] at this ⊢
      omega

theorem encodeClause_len (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  unfold encodeClause
  have : c.length ≤ (c.flatMap encodeLiteral).length := by
    induction c with
    | nil => simp
    | cons l c ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
      omega
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem items_le_encode (φ : CNF) : itemsF φ ≤ (encodeCNF φ).length := by
  unfold encodeCNF itemsF
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    have := encodeClause_len c
    omega

theorem items_list_len (φ : CNF) :
    (φ.flatMap (fun c : Clause => c.map some ++ [none])).length = itemsF φ := by
  unfold itemsF
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_singleton,
      ih, List.map_cons, List.sum_cons]

theorem ren_length (φ : CNF) : (REN φ).length = φ.length := by simp [REN]

theorem ren_getD_length (φ : CNF) (i : ℕ) :
    ((REN φ).getD i []).length = (φ.getD i []).length := by
  simp only [REN, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases φ[i]? <;> simp

theorem ren_off (φ : CNF) (i : ℕ) : offF (REN φ) i = offF φ i := by
  simp only [offF, REN, ← List.map_take, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp

theorem ren_var_le (φ : CNF) (i j : ℕ) : (litF (REN φ) i j).1 ≤ itemsF φ := by
  rw [← items_list_len]
  unfold litF
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [REN, List.getElem?_map]
  cases (φ[i]?) with
  | none => simp
  | some cl =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases (cl[j]?) with
    | none => simp
    | some l => exact List.findIdx_le_length

/-- Clause (b) of G-OWN. -/
theorem gOwnB : GOwnB := by
  intro φ E k off e hk hE hoff he num h1 h2 h3 h4 H hH T hT S hS F hF ol hol
  subst hol
  have hI : itemsF φ ≤ E := hE ▸ items_le_encode φ
  have key := own_len_bound E k (REN φ) hk
    (by
      intro i hi j hj
      rw [ren_length] at hi
      have := off_add_le φ i hi
      have hw : wF (REN φ) i = wF φ i := ren_getD_length φ i
      rw [ren_off]; omega)
    (by intro i _ j _; have := ren_var_le φ i j; omega)
  exact ⟨fun l hl => (key l hl).1, fun l hl => (key l hl).2⟩

end PEqualNP.MetaComplexity.Helpers.OwnerLink
