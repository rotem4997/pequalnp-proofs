import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517

open PEqualNP.CircuitLowerBounds

def isAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def gv {α : Type} (z : α) (A O : α → α → α) (g : Gate) (w : List α) : α :=
  if isAnd g = true then A (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)
  else O (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)

def grun {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) : List α :=
  gs.foldl (fun w g => w ++ [gv z A O g w]) x

theorem grun_snoc {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (g : Gate) (x : List α) :
    grun z A O (gs ++ [g]) x = grun z A O gs x ++ [gv z A O g (grun z A O gs x)] := by
  simp [grun, List.foldl_append]

theorem grun_length {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) :
    (grun z A O gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [grun]
  | append_singleton gs g ih => rw [grun_snoc]; simp [ih]; omega

theorem getD_lt {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
    ∃ a b, gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j

theorem good_init {n : ℕ} {gs : List Gate} {g : Gate} (h : Good n (gs ++ [g])) :
    Good n gs ∧ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + gs.length ∧ b < n + gs.length) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · simpa using h gs.length (by simp)

theorem grun_input {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) (i : ℕ)
    (hi : i < x.length) : (grun z A O gs x).getD i z = x.getD i z := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [grun_snoc, getD_lt _ _ _ _ (by rw [grun_length]; omega), ih]

theorem grun_gate {α : Type} (z : α) (A O : α → α → α) (n : ℕ) (gs : List Gate) (hgs : Good n gs)
    (x : List α) (hx : x.length = n) : ∀ (j : ℕ) (hj : j < gs.length),
      (grun z A O gs x).getD (n + j) z = gv z A O gs[j] (grun z A O gs x) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    obtain ⟨hg0, hop, a, b, hab, ha, hb⟩ := good_init hgs
    have hlen : (grun z A O gs x).length = n + gs.length := by rw [grun_length, hx]
    intro j hj
    have hin : ∀ (g' : Gate) (a b : ℕ), g'.inputs = [a, b] → a < n + gs.length →
        b < n + gs.length → gv z A O g' (grun z A O (gs ++ [g]) x) =
          gv z A O g' (grun z A O gs x) := by
      intro g' a b h ha hb
      unfold gv
      simp only [h, List.getD_cons_zero, List.getD_cons_succ]
      rw [grun_snoc, getD_lt _ _ _ _ (by rw [hlen]; exact ha),
        getD_lt _ _ _ _ (by rw [hlen]; exact hb)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h]
      obtain ⟨-, a', b', h1, h2, h3⟩ := hg0 j h
      rw [hin _ a' b' h1 (by omega) (by omega), grun_snoc, getD_lt _ _ _ _ (by rw [hlen]; omega)]
      exact ih hg0 j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, hin g a b hab ha hb, grun_snoc, ← hlen, getD_at]

theorem fold_congr {α : Type} (f g : List α → Gate → List α) (gs : List Gate)
    (h : ∀ q ∈ gs, ∀ w, f w q = g w q) : ∀ x, gs.foldl f x = gs.foldl g x := by
  induction gs with
  | nil => intro x; rfl
  | cons q gs ih =>
    intro x
    simp only [List.foldl_cons]
    rw [h q (by simp), ih (fun q' hq' => h q' (by simp [hq']))]

theorem wires_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (x : List Bool) :
    C.wires x = grun false (· && ·) (· || ·) C.gates x := by
  unfold Circuit.wires grun
  refine fold_congr _ _ _ (fun q hq w => ?_) x
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  obtain ⟨hop, a, b, hab, -, -⟩ := h j hj
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, GateOp.eval]


def em (i : ℕ) : ℕ := if i < 10 then [0, 1, 2, 3, 5, 6, 7, 8, 9, 12].getD i 0 else i + 4

theorem em_lt {i k : ℕ} (h : i < 10 + k) : em i < 14 + k := by
  unfold em
  split_ifs with h1
  · interval_cases i <;> simp <;> omega
  · omega

theorem em_inj {i j : ℕ} (h : em i = em j) : i = j := by
  unfold em at h
  split_ifs at h with h1 h2 h2
  · interval_cases i <;> interval_cases j <;> simp_all
  · interval_cases i <;> simp at h <;> omega
  · interval_cases j <;> simp at h <;> omega
  · omega

def emG (g : Gate) : Gate := ⟨g.op, g.inputs.map em⟩

theorem rel (gs : List Gate) (hgs : Good 10 gs) (x y : List Bool) (hx : x.length = 10)
    (hy : y.length = 14) (h : ∀ i < 10, x.getD i false = y.getD (em i) false) :
    ∀ i < 10 + gs.length, (grun false (· && ·) (· || ·) gs x).getD i false =
      (grun false (· && ·) (· || ·) (gs.map emG) y).getD (em i) false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [grun] using h
  | append_singleton gs g ih =>
    obtain ⟨hg0, hop, a, b, hab, ha, hb⟩ := good_init hgs
    have ih' := ih hg0
    have l1 : (grun false (· && ·) (· || ·) gs x).length = 10 + gs.length := by
      rw [grun_length, hx]
    have l2 : (grun false (· && ·) (· || ·) (gs.map emG) y).length = 14 + gs.length := by
      rw [grun_length, hy, List.length_map]
    intro i hi
    rw [List.map_append, List.map_singleton, grun_snoc, grun_snoc]
    rcases Nat.lt_or_ge i (10 + gs.length) with h1 | h1
    · rw [getD_lt _ _ _ _ (by rw [l1]; exact h1), getD_lt _ _ _ _ (by rw [l2]; exact em_lt h1)]
      exact ih' i h1
    · have hi' : i = 10 + gs.length := by simp at hi; omega
      have he : em i = 14 + gs.length := by unfold em; rw [if_neg (by omega)]; omega
      rw [he, hi', ← l1, getD_at, ← l2, getD_at]
      have e : isAnd (emG g) = isAnd g := rfl
      unfold gv
      rw [e]
      simp only [emG, hab, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
      rw [ih' a ha, ih' b hb]

def ext (b o : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [b, 5]⟩, ⟨GateOp.and, [10, b + 1]⟩, ⟨GateOp.or, [1, 2]⟩,
   ⟨GateOp.or, [4, b + 3]⟩, ⟨GateOp.and, [13, b + 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [6, b + 6]⟩,
   ⟨GateOp.and, [11, b + 7]⟩, ⟨GateOp.or, [b + 2, b + 5]⟩, ⟨GateOp.or, [b + 8, b + 9]⟩,
   ⟨GateOp.or, [o, b + 10]⟩]

theorem ext_good (m o : ℕ) (gs : List Gate) (hgs : Good 14 gs) (hm : gs.length = m)
    (ho : o < 14 + m) : Good 14 (gs ++ ext (14 + m) o) := by
  subst hm
  intro j hj
  rcases Nat.lt_or_ge j gs.length with h | h
  · rw [List.getElem_append_left h]; exact hgs j h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hk : k < 12 := by simp [ext] at hj; omega
    rw [List.getElem_append_right (by omega)]
    have : gs.length + k - gs.length = k := by omega
    simp only [this]
    interval_cases k <;> simp [ext] <;> omega

end PEqualNP.Outside.L_meta_3517

theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro C hC hnd
  obtain ⟨c1, c2, c3⟩ := hC
  have hG : PEqualNP.Outside.L_meta_3517.Good 10 C.gates := by
    intro j hj
    have hm := List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (c3 _ hm)
    have hr := c2 j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hr
    rw [List.getD_eq_getElem _ _ hj, hab] at hr
    exact ⟨c1 _ hm, a, b, hab, hr a (by simp), hr b (by simp)⟩
  have hG' : PEqualNP.Outside.L_meta_3517.Good 14 (C.gates.map PEqualNP.Outside.L_meta_3517.emG) := by
    intro j hj
    have hj' : j < C.gates.length := by simpa using hj
    obtain ⟨hop, a, b, hab, ha, hb⟩ := hG j hj'
    refine ⟨by simpa [PEqualNP.Outside.L_meta_3517.emG] using hop, PEqualNP.Outside.L_meta_3517.em a, PEqualNP.Outside.L_meta_3517.em b, by simp [PEqualNP.Outside.L_meta_3517.emG, hab],
      PEqualNP.Outside.L_meta_3517.em_lt ha, PEqualNP.Outside.L_meta_3517.em_lt hb⟩
  set m := C.gates.length with hm
  have hmapl : (C.gates.map PEqualNP.Outside.L_meta_3517.emG).length = m := by simp [hm]
  obtain ⟨o, out, ho, hoo⟩ : ∃ o out : ℕ, o < 14 + m ∧
      ((C.output < 10 + m ∧ o = PEqualNP.Outside.L_meta_3517.em C.output ∧ out = 14 + m + 11) ∨
        (10 + m ≤ C.output ∧ out = 14 + m + 10)) := by
    by_cases h : C.output < 10 + m
    · exact ⟨_, _, PEqualNP.Outside.L_meta_3517.em_lt h, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨0, _, by omega, Or.inr ⟨by omega, rfl⟩⟩
  set gs := C.gates.map PEqualNP.Outside.L_meta_3517.emG ++ PEqualNP.Outside.L_meta_3517.ext (14 + m) o with hgs
  have hGood : PEqualNP.Outside.L_meta_3517.Good 14 gs := PEqualNP.Outside.L_meta_3517.ext_good m o _ hG' hmapl ho
  have hgl : gs.length = m + 12 := by simp [hgs, hmapl, PEqualNP.Outside.L_meta_3517.ext]
  refine ⟨⟨gs, out⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    exact (hGood j hj).1
  · intro j hj
    obtain ⟨-, a, b, hab, ha, hb⟩ := hGood j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hj, hab]
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact ha
    · rw [List.mem_singleton.1 hi]; exact hb
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨-, a, b, hab, -, -⟩ := hGood j hj
    rw [hab]; rfl
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      exact (hnd g0 hg0).map fun i j hij => PEqualNP.Outside.L_meta_3517.em_inj hij
    · simp only [PEqualNP.Outside.L_meta_3517.ext, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp <;> omega
  · change 2 ≤ gs.length
    omega
  · change gs.length ≤ m + 12
    omega
  · intro z
    have hzl : (List.ofFn z).length = 14 := by simp
    set V : ℕ → Bool := fun w =>
      (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) gs (List.ofFn z)).getD w false with hV
    have hz : ∀ (i : ℕ) (hi : i < 14), V i = z ⟨i, hi⟩ := by
      intro i hi
      change (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) gs (List.ofFn z)).getD i false = _
      rw [PEqualNP.Outside.L_meta_3517.grun_input _ _ _ _ _ _ (by rw [hzl]; exact hi),
        List.getD_eq_getElem _ _ (by rw [hzl]; exact hi), List.getElem_ofFn]
    have hex : ∀ (k : ℕ) (hk : k < 12), V (14 + m + k) = PEqualNP.Outside.L_meta_3517.gv false (· && ·) (· || ·)
        ((PEqualNP.Outside.L_meta_3517.ext (14 + m) o)[k]'(by simpa [PEqualNP.Outside.L_meta_3517.ext] using hk))
        (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) gs (List.ofFn z)) := by
      intro k hk
      have h := PEqualNP.Outside.L_meta_3517.grun_gate false (· && ·) (· || ·) 14 gs hGood (List.ofFn z) hzl (m + k)
        (by omega)
      have hg : gs[m + k]'(by omega) = (PEqualNP.Outside.L_meta_3517.ext (14 + m) o)[k]'(by simpa [PEqualNP.Outside.L_meta_3517.ext] using hk) := by
        simp only [hgs]
        rw [List.getElem_append_right (by omega)]
        congr 1
        omega
      rw [hg] at h
      rw [← h, hV]
      simp only [Nat.add_assoc]
    have e0 : V (14 + m) = (V 0 || V 4) := hex 0 (by omega)
    have e1 : V (14 + m + 1) = (V (14 + m) || V 5) := hex 1 (by omega)
    have e2 : V (14 + m + 2) = (V 10 && V (14 + m + 1)) := hex 2 (by omega)
    have e3 : V (14 + m + 3) = (V 1 || V 2) := hex 3 (by omega)
    have e4 : V (14 + m + 4) = (V 4 || V (14 + m + 3)) := hex 4 (by omega)
    have e5 : V (14 + m + 5) = (V 13 && V (14 + m + 4)) := hex 5 (by omega)
    have e6 : V (14 + m + 6) = (V 3 || V 4) := hex 6 (by omega)
    have e7 : V (14 + m + 7) = (V 6 || V (14 + m + 6)) := hex 7 (by omega)
    have e8 : V (14 + m + 8) = (V 11 && V (14 + m + 7)) := hex 8 (by omega)
    have e9 : V (14 + m + 9) = (V (14 + m + 2) || V (14 + m + 5)) := hex 9 (by omega)
    have e10 : V (14 + m + 10) = (V (14 + m + 8) || V (14 + m + 9)) := hex 10 (by omega)
    have e11 : V (14 + m + 11) = (V o || V (14 + m + 10)) := hex 11 (by omega)
    have hD : (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, out⟩ (List.ofFn z)) = V out := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [PEqualNP.Outside.L_meta_3517.wires_eq ⟨gs, out⟩ hGood]
    have hstar : V (14 + m + 10) = decide (∃ (x6 : Fin 14) (x7 : Fin 14), ((x6 : ℕ), (x7 : ℕ)) ∈
        [(0, 10), (1, 13), (2, 13), (3, 11), (4, 10), (4, 11), (4, 13), (5, 10), (6, 11)] ∧
        z x6 = true ∧ z x7 = true) := by
      rw [e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0, hz 0 (by omega), hz 1 (by omega),
        hz 2 (by omega), hz 3 (by omega), hz 4 (by omega), hz 5 (by omega), hz 6 (by omega),
        hz 10 (by omega), hz 11 (by omega), hz 13 (by omega)]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      constructor
      · intro h
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ⟨h1, h | h | h⟩ | ⟨h1, (h | h) | h⟩ | ⟨h1, h | h | h⟩
        · exact ⟨6, 11, by simp, h, h1⟩
        · exact ⟨3, 11, by simp, h, h1⟩
        · exact ⟨4, 11, by simp, h, h1⟩
        · exact ⟨0, 10, by simp, h, h1⟩
        · exact ⟨4, 10, by simp, h, h1⟩
        · exact ⟨5, 10, by simp, h, h1⟩
        · exact ⟨4, 13, by simp, h, h1⟩
        · exact ⟨1, 13, by simp, h, h1⟩
        · exact ⟨2, 13, by simp, h, h1⟩
      · rintro ⟨a, b, hab, ha, hb⟩
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hab
        have pin : ∀ (c : Fin 14) (i : ℕ) (hi : i < 14), (c : ℕ) = i → z c = true →
            z ⟨i, hi⟩ = true := by
          rintro c i hi rfl hc
          exact hc
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          have p1 := pin a _ (by omega) h1 ha <;>
          have p2 := pin b _ (by omega) h2 hb <;>
          rw [p1, p2] <;> simp
    rw [hD]
    rcases hoo with ⟨hlt, ho', hout⟩ | ⟨hge, hout⟩
    · rw [hout, e11, hstar]
      congr 1
      have hxl : (List.ofFn fun (x6 : Fin 10) => z ([0, 1, 2, 3, 5, 6, 7, 8, 9, 12].getD
          (x6 : ℕ) 0)).length = 10 := by simp
      have hr := PEqualNP.Outside.L_meta_3517.rel C.gates hG (List.ofFn fun (x6 : Fin 10) =>
        z ([0, 1, 2, 3, 5, 6, 7, 8, 9, 12].getD (x6 : ℕ) 0)) (List.ofFn z) hxl hzl (by
          intro i hi
          have he : PEqualNP.Outside.L_meta_3517.em i < 14 := by simpa using PEqualNP.Outside.L_meta_3517.em_lt (k := 0) (by simpa using hi)
          rw [List.getD_eq_getElem _ _ (by rw [hxl]; exact hi),
            List.getD_eq_getElem _ _ (by rw [hzl]; exact he), List.getElem_ofFn,
            List.getElem_ofFn]
          congr 1
          interval_cases i <;> rfl) C.output hlt
      have hpre : V o = (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) (C.gates.map PEqualNP.Outside.L_meta_3517.emG)
          (List.ofFn z)).getD o false := by
        change (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) gs (List.ofFn z)).getD o false = _
        have : ∀ (ex base : List PEqualNP.CircuitLowerBounds.Gate), o < 14 + base.length →
            (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) (base ++ ex) (List.ofFn z)).getD o false =
            (PEqualNP.Outside.L_meta_3517.grun false (· && ·) (· || ·) base (List.ofFn z)).getD o false := by
          intro ex base hb
          induction ex using List.reverseRecOn with
          | nil => simp
          | append_singleton ex g ih =>
            rw [← List.append_assoc, PEqualNP.Outside.L_meta_3517.grun_snoc, PEqualNP.Outside.L_meta_3517.getD_lt _ _ _ _ (by
              rw [PEqualNP.Outside.L_meta_3517.grun_length, hzl, List.length_append]; omega), ih]
        exact this _ _ (by rw [hmapl]; exact ho)
      rw [hpre, ho', ← hr, ← PEqualNP.Outside.L_meta_3517.wires_eq C hG]
      rfl
    · rw [hout, hstar]
      have hf : C.eval (List.ofFn fun (x6 : Fin 10) => z ([0, 1, 2, 3, 5, 6, 7, 8, 9, 12].getD
          (x6 : ℕ) 0)) = false := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [PEqualNP.Outside.L_meta_3517.wires_eq C hG]
        exact List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3517.grun_length, List.length_ofFn]; omega)
      rw [hf, Bool.false_or]
