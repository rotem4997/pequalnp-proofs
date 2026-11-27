import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18396

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def val (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [val w g]

theorem block (gs : List Gate) : ∀ pre ext : List Bool,
    (∀ g ∈ gs, ∀ j ∈ g.inputs, j < pre.length) →
    gs.foldl step (pre ++ ext) = pre ++ ext ++ gs.map (val pre) := by
  induction gs with
  | nil => intro pre ext _; simp
  | cons g t ih =>
    intro pre ext h
    have hv : val (pre ++ ext) g = val pre g := by
      unfold val
      congr 1
      apply List.map_congr_left
      intro j hj
      exact List.getD_append _ _ _ _ (h g (List.mem_cons_self ..) j hj)
    have hs : step (pre ++ ext) g = pre ++ (ext ++ [val pre g]) := by
      unfold step
      rw [hv, List.append_assoc]
    rw [List.foldl_cons, hs, ih pre _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    simp

theorem get_map_range (m i : ℕ) (f : ℕ → Bool) (h : i < m) :
    ((List.range m).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem get_right (A B : List Bool) (i j : ℕ) (h : i = A.length + j) :
    (A ++ B).getD i false = B.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

def zGate (n k a : ℕ) : Gate := ⟨.or, [a, n + (a + k) % n]⟩

def oGate (n k c : ℕ) : Gate := ⟨.or, [2 * n + (c + k) % n, 2 * n + (c + n - k) % n]⟩

def aGate (n c : ℕ) : Gate := ⟨.and, [2 * n + c, 3 * n + c]⟩

def cGate (n k j : ℕ) : Gate :=
  ⟨.or, [if j = 0 then 3 * n + k else 3 * n + 2 * k + j - 1, 3 * n + k + j + 1]⟩

def circ (n k : ℕ) : Circuit :=
  ⟨(List.range n).map (zGate n k) ++ (List.range k).map (oGate n k) ++
    (List.range k).map (aGate n) ++ (List.range (k - 1)).map (cGate n k), 3 * n + 3 * k - 2⟩

theorem chain (n k : ℕ) (W : List Bool) (hW : W.length = 3 * n + 2 * k) (m : ℕ) (hm : m < k) :
    ((List.range m).map (cGate n k)).foldl step W =
      W ++ (List.range m).map
        (fun j => (List.range (j + 2)).any fun i => W.getD (3 * n + k + i) false) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega), List.map_append,
      ← List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    congr 1
    congr 1
    set L := (List.range m).map
      (fun j => (List.range (j + 2)).any fun i => W.getD (3 * n + k + i) false) with hL
    have h2 : (W ++ L).getD (3 * n + k + m + 1) false = W.getD (3 * n + k + (m + 1)) false := by
      rw [List.getD_append _ _ _ _ (by omega)]
      rfl
    have h1 : (W ++ L).getD (if m = 0 then 3 * n + k else 3 * n + 2 * k + m - 1) false =
        (List.range (m + 1)).any fun i => W.getD (3 * n + k + i) false := by
      by_cases h0 : m = 0
      · subst h0
        rw [if_pos rfl, List.getD_append _ _ _ _ (by omega)]
        simp
      · rw [if_neg h0, get_right W L _ (m - 1) (by omega), hL,
          get_map_range m (m - 1) _ (by omega)]
        have e : m - 1 + 2 = m + 1 := by omega
        rw [e]
    have h3 : ((List.range (m + 2)).any fun i => W.getD (3 * n + k + i) false) =
        (((List.range (m + 1)).any fun i => W.getD (3 * n + k + i) false) ||
          W.getD (3 * n + k + (m + 1)) false) := by
      rw [List.range_succ, List.any_append]
      simp
    unfold val cGate
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, h1, h2, h3]

def zv (n k : ℕ) (X : List Bool) (a : ℕ) : Bool :=
  X.getD a false || X.getD (n + (a + k) % n) false

def ov (n k : ℕ) (X : List Bool) (c : ℕ) : Bool :=
  zv n k X ((c + k) % n) || zv n k X ((c + n - k) % n)

theorem eval_circ (n k : ℕ) (hn : n + 1 = 2 * k) (hk : 3 ≤ k) (X : List Bool)
    (hX : X.length = 2 * n) :
    (circ n k).eval X = (List.range k).any (fun i => zv n k X i && ov n k X i) := by
  have hn0 : 0 < n := by omega
  have e1 : ((List.range n).map (zGate n k)).foldl step X =
      X ++ (List.range n).map (zv n k X) := by
    have h := block ((List.range n).map (zGate n k)) X [] (by
      intro g hg j hj
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
      rw [List.mem_range] at ha
      have := Nat.mod_lt (a + k) hn0
      simp only [zGate, List.mem_cons, List.not_mem_nil, or_false] at hj
      omega)
    rw [List.append_nil] at h
    rw [h, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    simp [val, zGate, zv, GateOp.eval]
  set W1 := X ++ (List.range n).map (zv n k X) with hW1
  have l1 : W1.length = 3 * n := by simp [hW1, hX]; omega
  have z1 : ∀ a, a < n → W1.getD (2 * n + a) false = zv n k X a := by
    intro a ha
    rw [hW1, get_right _ _ _ a (by omega), get_map_range n a _ ha]
  have e2 : ((List.range k).map (oGate n k)).foldl step W1 =
      W1 ++ (List.range k).map (ov n k X) := by
    have h := block ((List.range k).map (oGate n k)) W1 [] (by
      intro g hg j hj
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
      have := Nat.mod_lt (a + k) hn0
      have := Nat.mod_lt (a + n - k) hn0
      simp only [oGate, List.mem_cons, List.not_mem_nil, or_false] at hj
      omega)
    rw [List.append_nil] at h
    rw [h, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply, val, oGate, GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false, z1 _ (Nat.mod_lt _ hn0), ov]
  set W2 := W1 ++ (List.range k).map (ov n k X) with hW2
  have l2 : W2.length = 3 * n + k := by simp [hW2, l1]
  have z2 : ∀ a, a < k → W2.getD (2 * n + a) false = zv n k X a := by
    intro a ha
    rw [hW2, List.getD_append _ _ _ _ (by omega), z1 a (by omega)]
  have o2 : ∀ a, a < k → W2.getD (3 * n + a) false = ov n k X a := by
    intro a ha
    rw [hW2, get_right _ _ _ a (by omega), get_map_range k a _ ha]
  have e3 : ((List.range k).map (aGate n)).foldl step W2 =
      W2 ++ (List.range k).map (fun i => zv n k X i && ov n k X i) := by
    have h := block ((List.range k).map (aGate n)) W2 [] (by
      intro g hg j hj
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
      rw [List.mem_range] at ha
      simp only [aGate, List.mem_cons, List.not_mem_nil, or_false] at hj
      omega)
    rw [List.append_nil] at h
    rw [h, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [List.mem_range] at hc
    simp only [Function.comp_apply, val, aGate, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true, z2 c hc, o2 c hc]
  set W3 := W2 ++ (List.range k).map (fun i => zv n k X i && ov n k X i) with hW3
  have l3 : W3.length = 3 * n + 2 * k := by simp [hW3, l2]; omega
  have a3 : ∀ a, a < k → W3.getD (3 * n + k + a) false = (zv n k X a && ov n k X a) := by
    intro a ha
    rw [hW3, get_right _ _ _ a (by omega), get_map_range k a _ ha]
  have e4 := chain n k W3 l3 (k - 1) (by omega)
  have hw : (circ n k).wires X = W3 ++ (List.range (k - 1)).map
      (fun j => (List.range (j + 2)).any fun i => W3.getD (3 * n + k + i) false) := by
    have : (circ n k).wires X = (circ n k).gates.foldl step X := rfl
    rw [this]
    unfold circ
    simp only [List.foldl_append]
    rw [e1, e2, e3, e4]
  unfold Circuit.eval
  rw [hw]
  show (W3 ++ _).getD (3 * n + 3 * k - 2) false = _
  rw [get_right _ _ _ (k - 2) (by omega), get_map_range (k - 1) (k - 2) _ (by omega)]
  have e : k - 2 + 2 = k := by omega
  rw [e, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    rwa [a3 i (List.mem_range.1 hi)] at h
  · rintro ⟨i, hi, h⟩
    refine ⟨i, hi, ?_⟩
    rwa [a3 i (List.mem_range.1 hi)]

theorem zv_iff (n k : ℕ) (hn0 : 0 < n) (u v : Fin n) (a : ℕ) (ha : a < n) :
    zv n k (oneEach u v) a = true ↔ a = u.val ∨ (a + k) % n = v.val := by
  have h1 : (oneEach u v).getD a false = decide (a = u.val) := by
    unfold oneEach
    rw [List.getD_append _ _ _ _ (by simpa using ha)]
    simp [List.getD_eq_getElem?_getD, ha, Fin.ext_iff]
  have h2 : ∀ b, b < n → (oneEach u v).getD (n + b) false = decide (b = v.val) := by
    intro b hb
    unfold oneEach
    rw [get_right _ _ _ b (by simp)]
    simp [List.getD_eq_getElem?_getD, hb, Fin.ext_iff]
  unfold zv
  rw [h1, h2 _ (Nat.mod_lt _ hn0)]
  simp

theorem md (n a : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end PEqualNP.Outside.L_meta_18396

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_18396 : (∀ n : ℕ, 5 ≤ n → n % 2 = 1 → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (v.val = u.val ∨ v.val = (u.val + 1) % n)) ((5 * n + 1) / 2)) := by
  intro n h5 hodd
  obtain ⟨k, hk⟩ : ∃ k, n + 1 = 2 * k := ⟨(n + 1) / 2, by omega⟩
  have hk3 : 3 ≤ k := by omega
  have hn0 : 0 < n := by omega
  refine ⟨PEqualNP.Outside.L_meta_18396.circ n k, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_18396.circ, List.mem_append, List.mem_map] at hg
    rcases hg with ((⟨a, _, rfl⟩ | ⟨a, _, rfl⟩) | ⟨a, _, rfl⟩) | ⟨a, _, rfl⟩ <;>
      simp [PEqualNP.Outside.L_meta_18396.zGate, PEqualNP.Outside.L_meta_18396.oGate,
        PEqualNP.Outside.L_meta_18396.aGate, PEqualNP.Outside.L_meta_18396.cGate]
  · show (PEqualNP.Outside.L_meta_18396.circ n k).gates.length ≤ (5 * n + 1) / 2
    simp [PEqualNP.Outside.L_meta_18396.circ]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    rw [PEqualNP.Outside.L_meta_18396.eval_circ n k hk hk3 _
      (by simp [PEqualNP.Represents.oneEach]; omega), Bool.eq_iff_iff, decide_eq_true_iff,
      List.any_eq_true]
    have Z := PEqualNP.Outside.L_meta_18396.zv_iff n k hn0 u v
    have M := PEqualNP.Outside.L_meta_18396.md n
    have key : ∀ i, i < k →
        ((PEqualNP.Outside.L_meta_18396.zv n k (PEqualNP.Represents.oneEach u v) i &&
          PEqualNP.Outside.L_meta_18396.ov n k (PEqualNP.Represents.oneEach u v) i) = true ↔
        (i = u.val ∨ (i + k) % n = v.val) ∧
          (((i + k) % n = u.val ∨ ((i + k) % n + k) % n = v.val) ∨
           ((i + n - k) % n = u.val ∨ ((i + n - k) % n + k) % n = v.val))) := by
      intro i hi
      unfold PEqualNP.Outside.L_meta_18396.ov
      rw [Bool.and_eq_true, Bool.or_eq_true, Z i (by omega), Z _ (Nat.mod_lt _ hn0),
        Z _ (Nat.mod_lt _ hn0)]
    have hu1 : (u.val + 1) % n = if u.val + 1 < n then u.val + 1 else u.val + 1 - n :=
      M _ (by omega)
    constructor
    · rintro ⟨i, hi, h⟩
      rw [List.mem_range] at hi
      rw [key i hi] at h
      have a1 : (i + k) % n = if i + k < n then i + k else i + k - n := M _ (by omega)
      have a2 : (i + n - k) % n = if i + n - k < n then i + n - k else i + n - k - n :=
        M _ (by omega)
      have b1 : ((i + k) % n + k) % n =
          if (i + k) % n + k < n then (i + k) % n + k else (i + k) % n + k - n :=
        M _ (by have := Nat.mod_lt (i + k) hn0; omega)
      have b2 : ((i + n - k) % n + k) % n =
          if (i + n - k) % n + k < n then (i + n - k) % n + k else (i + n - k) % n + k - n :=
        M _ (by have := Nat.mod_lt (i + n - k) hn0; omega)
      rw [b1, b2, a1, a2] at h
      rw [hu1]
      split_ifs at h ⊢ <;> omega
    · intro h
      rw [hu1] at h
      have wit : ∃ i, i < k ∧ ((i = u.val ∨ (i + k) % n = v.val) ∧
          (((i + k) % n = u.val ∨ ((i + k) % n + k) % n = v.val) ∨
           ((i + n - k) % n = u.val ∨ ((i + n - k) % n + k) % n = v.val))) := by
        have go : ∀ i, i < k →
            ((i = u.val ∨ (if i + k < n then i + k else i + k - n) = v.val) ∧
              ((((if i + k < n then i + k else i + k - n) = u.val ∨
                  ((i + k) % n + k) % n = v.val)) ∨
               ((if i + n - k < n then i + n - k else i + n - k - n) = u.val ∨
                  ((i + n - k) % n + k) % n = v.val))) →
            ((i = u.val ∨ (i + k) % n = v.val) ∧
              (((i + k) % n = u.val ∨ ((i + k) % n + k) % n = v.val) ∨
               ((i + n - k) % n = u.val ∨ ((i + n - k) % n + k) % n = v.val))) := by
          intro i hi hh
          have a1 : (i + k) % n = if i + k < n then i + k else i + k - n := M _ (by omega)
          have a2 : (i + n - k) % n = if i + n - k < n then i + n - k else i + n - k - n :=
            M _ (by omega)
          rw [← a1, ← a2] at hh
          exact hh
        have c1 : ∀ i, ((i + k) % n + k) % n =
            if (i + k) % n + k < n then (i + k) % n + k else (i + k) % n + k - n := fun i =>
          M _ (by have := Nat.mod_lt (i + k) hn0; omega)
        have c2 : ∀ i, ((i + n - k) % n + k) % n =
            if (i + n - k) % n + k < n then (i + n - k) % n + k
            else (i + n - k) % n + k - n := fun i =>
          M _ (by have := Nat.mod_lt (i + n - k) hn0; omega)
        have d1 : ∀ i, i < k → (i + k) % n = if i + k < n then i + k else i + k - n :=
          fun i _ => M _ (by omega)
        have d2 : ∀ i, i < k →
            (i + n - k) % n = if i + n - k < n then i + n - k else i + n - k - n :=
          fun i _ => M _ (by omega)
        by_cases hlt : u.val < k
        · refine ⟨u.val, hlt, Or.inl rfl, ?_⟩
          rw [c1, c2, d1 _ hlt, d2 _ hlt]
          split_ifs at h ⊢ <;> omega
        · rcases h with h | h
          · have hi : u.val - k < k := by omega
            refine ⟨u.val - k, hi, ?_⟩
            rw [c1, c2, d1 _ hi, d2 _ hi]
            split_ifs <;> omega
          · have hi : u.val + 1 - k < k := by omega
            refine ⟨u.val + 1 - k, hi, ?_⟩
            rw [c1, c2, d1 _ hi, d2 _ hi]
            split_ifs at h ⊢ <;> omega
      obtain ⟨i, hi, hh⟩ := wit
      exact ⟨i, List.mem_range.2 hi, (key i hi).2 hh⟩
