import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_271

open PEqualNP.CircuitLowerBounds

-- A list of wire values grown one gate at a time, each new value computed from the list so far.
def run (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem run_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    run F (g :: gs) w = run F gs (w ++ [F w g]) := rfl

theorem run_length (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) :
    (run F gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem run_getD_lt (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run F gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact getD_append_lt _ _ _ hi

theorem run_append (F : List Bool → Gate → Bool) (gs1 gs2 : List Gate) (w : List Bool) :
    run F (gs1 ++ gs2) w = run F gs2 (run F gs1 w) := by
  simp [run, List.foldl_append]

theorem run_gate (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (j : ℕ)
    (g : Gate) (hj : gs[j]? = some g) :
    ∃ pre : List Bool, pre.length = w.length + j ∧
      (∀ i, pre.getD i false = if i < w.length + j then (run F gs w).getD i false else false) ∧
      (run F gs w).getD (w.length + j) false = F pre g := by
  obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hj
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [← hg]; simp
  have hlen : (run F (gs.take j) w).length = w.length + j := by
    rw [run_length, List.length_take, Nat.min_eq_left hlt.le]
  have hrun : run F gs w =
      run F (gs.drop (j + 1)) (run F (gs.take j) w ++ [F (run F (gs.take j) w) g]) := by
    conv_lhs => rw [hsplit]
    rw [run_append, run_cons]
  refine ⟨run F (gs.take j) w, hlen, ?_, ?_⟩
  · intro i
    split_ifs with hi
    · rw [hrun, run_getD_lt F (gs.drop (j + 1)) _ i
          (by rw [List.length_append, hlen, List.length_singleton]; omega),
        getD_append_lt _ _ _ (by omega)]
    · exact getD_ge _ _ (by omega)
  · rw [hrun, run_getD_lt F (gs.drop (j + 1)) _ (w.length + j)
        (by rw [List.length_append, hlen, List.length_singleton]; omega), ← hlen]
    simp [List.getD_eq_getElem?_getD]

def Fw (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run Fw C.gates x := rfl

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def cut (b : ℕ) (f : ℕ → Bool) (a : ℕ) : Bool := if a < b then f a else false

theorem cut_true {b : ℕ} {f : ℕ → Bool} {a : ℕ} (h : cut b f a = true) : a < b ∧ f a = true := by
  unfold cut at h
  split_ifs at h with hab
  exact ⟨hab, h⟩

theorem cut_of_lt {b : ℕ} {f : ℕ → Bool} {a : ℕ} (h : a < b) : cut b f a = f a := by
  simp [cut, h]

theorem eval_and (u v : Bool) : GateOp.and.eval [u, v] = (u && v) := by
  simp [GateOp.eval]

theorem eval_or (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
  simp [GateOp.eval]

theorem ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

theorem val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, run_getD_lt _ _ _ _ (by simp [hw]), ofFn_getD_lt]

theorem val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : val C x w = false := by
  unfold val
  rw [wires_eq]
  exact getD_ge _ _ (by rw [run_length]; simpa using hw)

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {j : ℕ} {g : Gate} {a b : ℕ}
    (hj : C.gates[j]? = some g) (hin : g.inputs = [a, b]) :
    val C x (n + j) = g.op.eval [cut (n + j) (val C x) a, cut (n + j) (val C x) b] := by
  obtain ⟨pre, -, hpre, hv⟩ := run_gate Fw C.gates (List.ofFn x) j g hj
  simp only [List.length_ofFn] at hpre hv
  unfold val
  rw [wires_eq, hv]
  simp only [Fw, hin, List.map_cons, List.map_nil, hpre]
  rfl

theorem ginfo (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {j : ℕ} (hj : j < C.gates.length) :
    ∃ (g : Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.inputs = [a, b] ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hg _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  exact ⟨C.gates[j], a, b, List.getElem?_eq_getElem hj, hab, hop⟩

theorem val_mono {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_in C _ w h1] at hw ⊢
      exact hxy _ hw
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        obtain ⟨g, a, b, hgj, hin, hop⟩ := ginfo C hg (show j < C.gates.length by omega)
        rw [val_gate C _ hgj hin] at hw ⊢
        have hc : ∀ a, cut (n + j) (val C x) a = true → cut (n + j) (val C y) a = true := by
          intro a ha
          obtain ⟨ha1, ha2⟩ := cut_true ha
          rw [cut_of_lt ha1]
          exact ih a ha1 ha2
        rcases hop with hop | hop
        · rw [hop, eval_and, Bool.and_eq_true] at hw ⊢
          exact ⟨hc _ hw.1, hc _ hw.2⟩
        · rw [hop, eval_or, Bool.or_eq_true] at hw ⊢
          exact hw.imp (hc _) (hc _)
      · rw [val_out C x w (by omega)] at hw
        exact absurd hw (by simp)

def single {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

-- The points whose one-point input makes wire w true.
def Sing {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val C (single p) w = true)

theorem mem_Sing {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ Sing C w ↔ val C (single p) w = true := by
  simp [Sing]

theorem Sing_in {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (Sing C w : Finset (Fin n)) = {⟨w, hw⟩} := by
  ext p
  rw [mem_Sing, val_in C _ w hw, Finset.mem_singleton]
  simp [single, eq_comm]

theorem Sing_out {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (Sing C w : Finset (Fin n)) = ∅ := by
  ext p
  rw [mem_Sing, val_out C _ w hw]
  simp

-- A wire is private to S when its one-point set lies inside S and has at least two points.
abbrev priv {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  Sing C w ⊆ S ∧ 2 ≤ (Sing C w : Finset (Fin n)).card

theorem priv_gate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) (h : priv C S w) :
    ∃ j, w = n + j ∧ j < C.gates.length := by
  by_cases h1 : w < n
  · have := h.2
    rw [Sing_in C w h1] at this
    simp at this
  · by_cases h2 : w < n + C.gates.length
    · exact ⟨w - n, by omega, by omega⟩
    · have := h.2
      rw [Sing_out C w (by omega)] at this
      simp at this

-- The value of a wire when wires leaving S are set to true and wires with at most one point,
-- all inside S, are set to false.
def Fm {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : List Bool) (g : Gate) : Bool :=
  if Sing C w.length ⊆ S then
    (if 2 ≤ (Sing C w.length : Finset (Fin n)).card then g.op.eval (g.inputs.map fun i => w.getD i false)
      else false)
  else true

def mv {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Bool :=
  (run (Fm C S) C.gates (List.ofFn fun p : Fin n => decide (p ∉ S))).getD w false

theorem mv_in {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) (hw : w < n) :
    mv C S w = decide ((⟨w, hw⟩ : Fin n) ∉ S) := by
  unfold mv
  rw [run_getD_lt _ _ _ _ (by simp [hw]), ofFn_getD_lt _ w hw]

theorem mv_out {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : mv C S w = false := by
  unfold mv
  exact getD_ge _ _ (by rw [run_length]; simpa using hw)

theorem mv_gate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) {j : ℕ} {g : Gate} {a b : ℕ}
    (hj : C.gates[j]? = some g) (hin : g.inputs = [a, b]) :
    mv C S (n + j) =
      if Sing C (n + j) ⊆ S then
        (if 2 ≤ (Sing C (n + j) : Finset (Fin n)).card then
          g.op.eval [cut (n + j) (mv C S) a, cut (n + j) (mv C S) b] else false)
      else true := by
  obtain ⟨pre, hlen, hpre, hv⟩ :=
    run_gate (Fm C S) C.gates (List.ofFn fun p : Fin n => decide (p ∉ S)) j g hj
  simp only [List.length_ofFn] at hlen hpre hv
  unfold mv
  rw [hv]
  simp only [Fm, hlen, hin, List.map_cons, List.map_nil, hpre]
  rfl

theorem mv_true_cases {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (w : ℕ) (h : mv C S w = true) : ¬ (Sing C w ⊆ S) ∨ priv C S w := by
  by_cases h1 : w < n
  · left
    rw [mv_in C S w h1] at h
    rw [Sing_in C w h1]
    simpa using h
  · by_cases h2 : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      obtain ⟨g, a, b, hgj, hin, -⟩ := ginfo C hg (show j < C.gates.length by omega)
      rw [mv_gate C S hgj hin] at h
      by_cases hs : Sing C (n + j) ⊆ S
      · by_cases hc : 2 ≤ (Sing C (n + j) : Finset (Fin n)).card
        · exact Or.inr ⟨hs, hc⟩
        · rw [if_pos hs, if_neg hc] at h
          exact absurd h (by simp)
      · exact Or.inl hs
    · rw [mv_out C S w (by omega)] at h
      exact absurd h (by simp)

theorem leaving_mv {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (w : ℕ) (h : ¬ (Sing C w ⊆ S)) : mv C S w = true := by
  by_cases h1 : w < n
  · rw [mv_in C S w h1]
    rw [Sing_in C w h1] at h
    simpa using h
  · by_cases h2 : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      obtain ⟨g, a, b, hgj, hin, -⟩ := ginfo C hg (show j < C.gates.length by omega)
      rw [mv_gate C S hgj hin, if_neg h]
    · rw [Sing_out C w (by omega)] at h
      exact absurd (Finset.empty_subset S) h

-- The gates private to S.
def P {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => priv C S (n + j))

-- First case: the private region is true once the wires leaving S are true.
theorem case1 {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (k o : ℕ) (hmv : mv C S o = true) (hpo : priv C S o)
    (H2 : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val C x o = false) :
    k ≤ (P C S).card := by
  have key : ∀ d j, j + d = C.gates.length → ∃ F A : Finset ℕ,
      (∀ w ∈ F, mv C S w = true) ∧ (∀ w ∈ F, priv C S w → w < n + j) ∧ A ⊆ P C S ∧
      (∀ a ∈ A, j ≤ a) ∧ F.card ≤ A.card + 1 ∧
      ∀ x : Fin n → Bool, (∀ w ∈ F, val C x w = true) → val C x o = true := by
    intro d
    induction d with
    | zero =>
      intro j hj
      refine ⟨{o}, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw
        rw [Finset.mem_singleton] at hw
        rw [hw]; exact hmv
      · intro w hw _
        rw [Finset.mem_singleton] at hw
        obtain ⟨t, ht, ht2⟩ := priv_gate C S o hpo
        omega
      · exact Finset.empty_subset _
      · intro a ha
        exact absurd ha (Finset.notMem_empty a)
      · simp
      · intro x hx
        exact hx o (Finset.mem_singleton_self o)
    | succ d ih =>
      intro j hj
      obtain ⟨F, A, h1, h2, h3, h4, h5, h6⟩ := ih (j + 1) (by omega)
      have hjlt : j < C.gates.length := by omega
      by_cases hc : n + j ∈ F ∧ priv C S (n + j)
      · obtain ⟨hF, hp⟩ := hc
        obtain ⟨g, a, b, hgj, hin, hop⟩ := ginfo C hg hjlt
        have hm := h1 _ hF
        rw [mv_gate C S hgj hin, if_pos hp.1, if_pos hp.2] at hm
        have hFpos : 1 ≤ F.card := Finset.card_pos.mpr ⟨_, hF⟩
        have herase : (F.erase (n + j)).card = F.card - 1 := Finset.card_erase_of_mem hF
        rcases hop with hop | hop
        · rw [hop, eval_and, Bool.and_eq_true] at hm
          obtain ⟨ha1, ha2⟩ := cut_true hm.1
          obtain ⟨hb1, hb2⟩ := cut_true hm.2
          have hjA : j ∉ A := fun hjA => by have := h4 j hjA; omega
          refine ⟨insert a (insert b (F.erase (n + j))), insert j A, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro w hw
            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | rfl | ⟨-, hw⟩
            · exact ha2
            · exact hb2
            · exact h1 w hw
          · intro w hw hpw
            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | rfl | ⟨hne, hw⟩
            · exact ha1
            · exact hb1
            · have := h2 w hw hpw
              omega
          · apply Finset.insert_subset _ h3
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hp⟩
          · intro t ht
            rw [Finset.mem_insert] at ht
            rcases ht with rfl | ht
            · exact le_rfl
            · have := h4 t ht; omega
          · have c1 := Finset.card_insert_le a (insert b (F.erase (n + j)))
            have c2 := Finset.card_insert_le b (F.erase (n + j))
            rw [Finset.card_insert_of_notMem hjA]
            omega
          · intro x hx
            apply h6 x
            intro w hw
            by_cases e : w = n + j
            · rw [e, val_gate C x hgj hin, hop, eval_and, cut_of_lt ha1, cut_of_lt hb1,
                hx a (by simp), hx b (by simp)]
              rfl
            · exact hx w (by simp [e, hw])
        · rw [hop, eval_or, Bool.or_eq_true] at hm
          have hchild : ∃ a', a' < n + j ∧ mv C S a' = true ∧
              ∀ x : Fin n → Bool, val C x a' = true → val C x (n + j) = true := by
            rcases hm with hm | hm
            · obtain ⟨ha1, ha2⟩ := cut_true hm
              refine ⟨a, ha1, ha2, fun x hx => ?_⟩
              rw [val_gate C x hgj hin, hop, eval_or, cut_of_lt ha1, hx]
              rfl
            · obtain ⟨hb1, hb2⟩ := cut_true hm
              refine ⟨b, hb1, hb2, fun x hx => ?_⟩
              rw [val_gate C x hgj hin, hop, eval_or, cut_of_lt hb1, hx]
              simp
          obtain ⟨a', ha1, ha2, ha3⟩ := hchild
          refine ⟨insert a' (F.erase (n + j)), A, ?_, ?_, h3, ?_, ?_, ?_⟩
          · intro w hw
            rw [Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | ⟨-, hw⟩
            · exact ha2
            · exact h1 w hw
          · intro w hw hpw
            rw [Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | ⟨hne, hw⟩
            · exact ha1
            · have := h2 w hw hpw
              omega
          · intro t ht
            have := h4 t ht; omega
          · have c1 := Finset.card_insert_le a' (F.erase (n + j))
            omega
          · intro x hx
            apply h6 x
            intro w hw
            by_cases e : w = n + j
            · rw [e]
              exact ha3 x (hx a' (by simp))
            · exact hx w (by simp [e, hw])
      · refine ⟨F, A, h1, ?_, h3, ?_, h5, h6⟩
        · intro w hw hpw
          have := h2 w hw hpw
          have hne : w ≠ n + j := fun e => hc ⟨e ▸ hw, e ▸ hpw⟩
          omega
        · intro t ht
          have := h4 t ht; omega
  obtain ⟨F, A, h1, h2, h3, -, h5, h6⟩ := key C.gates.length 0 (by simp)
  have hleave : ∀ w ∈ F, ∃ p : Fin n, p ∈ Sing C w ∧ p ∉ S := by
    intro w hw
    rcases mv_true_cases C hg S w (h1 w hw) with hl | hp
    · exact Finset.not_subset.mp hl
    · have := h2 w hw hp
      obtain ⟨t, ht, -⟩ := priv_gate C S w hp
      omega
  obtain ⟨p0, hp0⟩ : ∃ p0 : Fin n, p0 ∈ Sing C o :=
    Finset.card_pos.mp (by have := hpo.2; omega)
  haveI : Nonempty (Fin n) := ⟨p0⟩
  choose! pt hpt using hleave
  have hx : ∀ w ∈ F, val C (fun q : Fin n => decide (q ∈ F.image pt)) w = true := by
    intro w hw
    apply val_mono C hg (single (pt w)) _ _ w ((mem_Sing C w _).mp (hpt w hw).1)
    intro q hq
    have hqe : q = pt w := by simpa [single] using hq
    simp only [decide_eq_true_eq]
    exact Finset.mem_image.mpr ⟨w, hw, hqe.symm⟩
  have hout := h6 _ hx
  have hnot : ¬ (Finset.univ.filter
      (fun q : Fin n => (fun q : Fin n => decide (q ∈ F.image pt)) q = true)).card ≤ k := by
    intro hle
    have := H2 _ hle (by
      intro q hq
      simp only [decide_eq_false_iff_not]
      intro hmem
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hmem
      exact (hpt w hw).2 hq)
    rw [this] at hout
    exact absurd hout (by simp)
  have hfilter : (Finset.univ.filter
      (fun q : Fin n => (fun q : Fin n => decide (q ∈ F.image pt)) q = true)) = F.image pt := by
    ext q; simp
  rw [hfilter] at hnot
  have c1 := Finset.card_image_le (s := F) (f := pt)
  have c2 := Finset.card_le_card h3
  omega

-- Second case: the private region is false, so the points of S are joined one gate at a time.
theorem case2 {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (o : ℕ) (hmv : mv C S o = false) (hpo : priv C S o)
    (hS : Sing C o = S) :
    S.card ≤ (P C S).card + 1 := by
  have key : ∀ j, j ≤ C.gates.length → ∃ col : Fin n → ℕ,
      S.card ≤ (S.image col).card +
        ((Finset.range j).filter (fun t => priv C S (n + t))).card ∧
      ∀ w, w < n + j → priv C S w → mv C S w = false →
        ∀ p ∈ Sing C w, ∀ q ∈ Sing C w, col p = col q := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun p => p.val, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ Fin.val_injective]
        omega
      · intro w hw hp
        obtain ⟨t, ht, -⟩ := priv_gate C S w hp
        omega
    | succ j ih =>
      intro hj
      obtain ⟨col, hcard, hmono⟩ := ih (by omega)
      have hjlt : j < C.gates.length := by omega
      have hcount : ((Finset.range j).filter (fun t => priv C S (n + t))).card ≤
          ((Finset.range (j + 1)).filter (fun t => priv C S (n + t))).card :=
        Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.range_subset_range.mpr (by omega)))
      by_cases hc : priv C S (n + j) ∧ mv C S (n + j) = false
      · obtain ⟨hp, hmf⟩ := hc
        have hcount1 : ((Finset.range (j + 1)).filter (fun t => priv C S (n + t))).card =
            ((Finset.range j).filter (fun t => priv C S (n + t))).card + 1 := by
          rw [Finset.range_add_one, Finset.filter_insert, if_pos hp,
            Finset.card_insert_of_notMem (by simp)]
        obtain ⟨g, a, b, hgj, hin, hop⟩ := ginfo C hg hjlt
        rw [mv_gate C S hgj hin, if_pos hp.1, if_pos hp.2] at hmf
        have hin_mono : ∀ a', cut (n + j) (mv C S) a' = false →
            ∀ p q : Fin n, cut (n + j) (val C (single p)) a' = true →
              cut (n + j) (val C (single q)) a' = true → col p = col q := by
          intro a' ha' p q hpa hqa
          obtain ⟨hlt, hpv⟩ := cut_true hpa
          obtain ⟨-, hqv⟩ := cut_true hqa
          rw [cut_of_lt hlt] at ha'
          have hsub : Sing C a' ⊆ S := by
            by_contra hns
            rw [leaving_mv C hg S a' hns] at ha'
            exact absurd ha' (by simp)
          have hpS := (mem_Sing C a' p).mpr hpv
          have hqS := (mem_Sing C a' q).mpr hqv
          by_cases h2 : 2 ≤ (Sing C a' : Finset (Fin n)).card
          · exact hmono a' (by omega) ⟨hsub, h2⟩ ha' p hpS q hqS
          · have h1 : (Sing C a' : Finset (Fin n)).card ≤ 1 := by omega
            rw [Finset.card_le_one.mp h1 p hpS q hqS]
        rcases hop with hop | hop
        · refine ⟨col, by omega, ?_⟩
          intro w hw hpw hmw p hpS q hqS
          by_cases e : w = n + j
          · subst e
            rw [mem_Sing, val_gate C _ hgj hin, hop, eval_and, Bool.and_eq_true] at hpS hqS
            rw [hop, eval_and, Bool.and_eq_false_iff] at hmf
            rcases hmf with hmf | hmf
            · exact hin_mono a hmf p q hpS.1 hqS.1
            · exact hin_mono b hmf p q hpS.2 hqS.2
          · exact hmono w (by omega) hpw hmw p hpS q hqS
        · rw [hop, eval_or, Bool.or_eq_false_iff] at hmf
          have hA := hin_mono a hmf.1
          have hB := hin_mono b hmf.2
          by_cases hne : (∃ p : Fin n, cut (n + j) (val C (single p)) a = true) ∧
              (∃ q : Fin n, cut (n + j) (val C (single q)) b = true)
          · obtain ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩⟩ := hne
            refine ⟨fun r => if col r = col pb then col pa else col r, ?_, ?_⟩
            · have himg : S.image col ⊆ insert (col pb)
                  (S.image (fun r => if col r = col pb then col pa else col r)) := by
                intro c hc
                obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
                by_cases e : col r = col pb
                · rw [e]; exact Finset.mem_insert_self _ _
                · apply Finset.mem_insert_of_mem
                  exact Finset.mem_image.mpr ⟨r, hr, by simp [e]⟩
              have c1 := Finset.card_le_card himg
              have c2 := Finset.card_insert_le (col pb)
                (S.image (fun r => if col r = col pb then col pa else col r))
              omega
            · intro w hw hpw hmw p hpS q hqS
              by_cases e : w = n + j
              · subst e
                rw [mem_Sing, val_gate C _ hgj hin, hop, eval_or, Bool.or_eq_true] at hpS hqS
                have hcol : ∀ r : Fin n, (cut (n + j) (val C (single r)) a = true ∨
                    cut (n + j) (val C (single r)) b = true) →
                    (if col r = col pb then col pa else col r) = col pa := by
                  intro r hr
                  rcases hr with hr | hr
                  · rw [hA r pa hr hpa]
                    split_ifs <;> rfl
                  · rw [if_pos (hB r pb hr hpb)]
                simp only [hcol p hpS, hcol q hqS]
              · have := hmono w (by omega) hpw hmw p hpS q hqS
                simp only [this]
          · refine ⟨col, by omega, ?_⟩
            intro w hw hpw hmw p hpS q hqS
            by_cases e : w = n + j
            · subst e
              rw [mem_Sing, val_gate C _ hgj hin, hop, eval_or, Bool.or_eq_true] at hpS hqS
              rcases hpS with hpS | hpS
              · rcases hqS with hqS | hqS
                · exact hA p q hpS hqS
                · exact absurd ⟨⟨p, hpS⟩, ⟨q, hqS⟩⟩ hne
              · rcases hqS with hqS | hqS
                · exact absurd ⟨⟨q, hqS⟩, ⟨p, hpS⟩⟩ hne
                · exact hB p q hpS hqS
            · exact hmono w (by omega) hpw hmw p hpS q hqS
      · refine ⟨col, by omega, ?_⟩
        intro w hw hpw hmw
        by_cases e : w = n + j
        · exact absurd ⟨e ▸ hpw, e ▸ hmw⟩ hc
        · exact hmono w (by omega) hpw hmw
  obtain ⟨col, hcard, hmono⟩ := key C.gates.length le_rfl
  obtain ⟨t, ht, ht2⟩ := priv_gate C S o hpo
  have hone : (S.image col).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro c hc d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    exact hmono o (by omega) hpo hmv p (hS ▸ hp) q (hS ▸ hq)
  have : (P C S).card = ((Finset.range C.gates.length).filter
      (fun t => priv C S (n + t))).card := rfl
  omega

end PEqualNP.Outside.L_meta_271

theorem PEqualNP.Outside.L_meta_271 : ∀ (n k : ℕ) (S₁ S₂ : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o₁ o₂ : ℕ), (S₁ ∩ S₂).card ≤ 1 → 2 ≤ S₁.card → 2 ≤ S₂.card → S₁.card ≤ k + 1 → S₂.card ≤ k + 1 → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o₁ false = true ↔ p ∈ S₁) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o₂ false = true ↔ p ∈ S₂) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S₁, x q = false) → (C.wires (List.ofFn x)).getD o₁ false = false) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S₂, x q = false) → (C.wires (List.ofFn x)).getD o₂ false = false) → S₁.card + S₂.card ≤ C.size + 2 := by
  intro n k S₁ S₂ C o₁ o₂ hinter h1 h2 hk1 hk2 hg hs1 hs2 hH1 hH2
  have hS1 : PEqualNP.Outside.L_meta_271.Sing C o₁ = S₁ := by
    ext p
    rw [PEqualNP.Outside.L_meta_271.mem_Sing]
    exact hs1 p
  have hS2 : PEqualNP.Outside.L_meta_271.Sing C o₂ = S₂ := by
    ext p
    rw [PEqualNP.Outside.L_meta_271.mem_Sing]
    exact hs2 p
  have hp1 : PEqualNP.Outside.L_meta_271.priv C S₁ o₁ := ⟨by rw [hS1], by rw [hS1]; exact h1⟩
  have hp2 : PEqualNP.Outside.L_meta_271.priv C S₂ o₂ := ⟨by rw [hS2], by rw [hS2]; exact h2⟩
  have m1 : S₁.card ≤ (PEqualNP.Outside.L_meta_271.P C S₁).card + 1 := by
    cases hmv : PEqualNP.Outside.L_meta_271.mv C S₁ o₁ with
    | false => exact PEqualNP.Outside.L_meta_271.case2 C hg S₁ o₁ hmv hp1 hS1
    | true =>
      have := PEqualNP.Outside.L_meta_271.case1 C hg S₁ k o₁ hmv hp1 hH1
      omega
  have m2 : S₂.card ≤ (PEqualNP.Outside.L_meta_271.P C S₂).card + 1 := by
    cases hmv : PEqualNP.Outside.L_meta_271.mv C S₂ o₂ with
    | false => exact PEqualNP.Outside.L_meta_271.case2 C hg S₂ o₂ hmv hp2 hS2
    | true =>
      have := PEqualNP.Outside.L_meta_271.case1 C hg S₂ k o₂ hmv hp2 hH2
      omega
  have hdisj : Disjoint (PEqualNP.Outside.L_meta_271.P C S₁) (PEqualNP.Outside.L_meta_271.P C S₂) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    have a1 := (Finset.mem_filter.mp ht1).2
    have a2 := (Finset.mem_filter.mp ht2).2
    have hsub := Finset.card_le_card (Finset.subset_inter a1.1 a2.1)
    have := a1.2
    omega
  have hu := Finset.card_union_of_disjoint hdisj
  have hc : (PEqualNP.Outside.L_meta_271.P C S₁ ∪ PEqualNP.Outside.L_meta_271.P C S₂).card ≤ (Finset.range C.gates.length).card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
  rw [Finset.card_range] at hc
  have hsz : C.size = C.gates.length := rfl
  omega
