import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7025

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)

private def isAnd (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

private theorem isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = .and := by
  cases g with
  | mk op ins => cases op <;> simp [isAnd]

private def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [gateValue g w]

-- Record the value of the first input of each AND gate.
private def trace : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    if isAnd g then w.getD (g.inputs.headD w.length) false :: trace gs (step w g)
    else trace gs (step w g)

private theorem traceLength (gs : List Gate) (w : List Bool) :
    (trace gs w).length = gs.countP isAnd := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [trace, List.countP_cons]
    split <;> simp [*]

private theorem count_eq (C : Circuit) : C.gates.countP isAnd =
    {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard := by
  classical
  let S := Finset.univ.filter (fun i : Fin C.gates.length => isAnd (C.gates.get i) = true)
  have hs : (S : Set (Fin C.gates.length)) = {i | (C.gates.get i).op = .and} := by
    ext i
    simp [S, isAnd_iff]
  rw [← hs, Set.ncard_coe_finset]
  calc
    C.gates.countP isAnd = (List.ofFn C.gates.get).countP isAnd :=
      congrArg (List.countP isAnd) (List.ofFn_get C.gates).symm
    _ = S.card := List.countP_ofFn C.gates.get isAnd

private def Bounds (a b z : List Bool) : Prop :=
  ∀ i, z.getD i false = true → a.getD i false = true ∨ b.getD i false = true

private theorem bounds_append {a b z : List Bool} (ha : a.length = z.length)
    (hb : b.length = z.length) (h : Bounds a b z) {x y t : Bool}
    (hbit : t = true → x = true ∨ y = true) :
    Bounds (a ++ [x]) (b ++ [y]) (z ++ [t]) := by
  intro i
  by_cases hi : i < z.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (ha ▸ hi),
      List.getD_append _ _ _ _ (hb ▸ hi)]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega : z.length ≤ i),
      List.getD_append_right _ _ _ _ (by omega : a.length ≤ i),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), ha, hb]
    cases i - z.length with
    | zero => simpa using hbit
    | succ n => simp

private theorem and_bounds {ins : List Nat} (hlen : ins.length ≤ 2)
    {a b z : List Bool} (h : Bounds a b z)
    (heq : a.getD (ins.headD a.length) false = b.getD (ins.headD b.length) false) :
    gateValue ⟨.and, ins⟩ z = true →
      gateValue ⟨.and, ins⟩ a = true ∨ gateValue ⟨.and, ins⟩ b = true := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
  · simp [gateValue, GateOp.eval]
  · simpa [gateValue, GateOp.eval] using h i
  · simp only [List.headD_cons] at heq
    simp only [gateValue, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
    rintro ⟨hi, hj⟩
    have ha : a.getD i false = true := (h i hi).elim id (fun hb => heq.trans hb)
    have hb : b.getD i false = true := heq.symm.trans ha
    exact (h j hj).imp (fun hja => ⟨ha, hja⟩) (fun hjb => ⟨hb, hjb⟩)
  · simp at hlen

private theorem or_bounds {ins : List Nat} {a b z : List Bool} (h : Bounds a b z) :
    gateValue ⟨.or, ins⟩ z = true →
      gateValue ⟨.or, ins⟩ a = true ∨ gateValue ⟨.or, ins⟩ b = true := by
  simp only [gateValue, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  rintro ⟨_, ⟨i, hi, rfl⟩, hz⟩
  exact (h i hz).imp (fun ha => ⟨_, ⟨i, hi, rfl⟩, ha⟩)
    (fun hb => ⟨_, ⟨i, hi, rfl⟩, hb⟩)

-- Equal records ensure that a wire false on both inputs stays false on their union.
private theorem runBounds (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (a b z : List Bool) (ha : a.length = z.length) (hb : b.length = z.length)
    (h : Bounds a b z) (ht : trace gs a = trace gs b) :
    Bounds (gs.foldl step a) (gs.foldl step b) (gs.foldl step z) := by
  induction gs generalizing a b z with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hm g (by simp)
    have htail : ∀ k ∈ gs,
        k.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ k.inputs.length ≤ 2 :=
      fun k hk => hm k (List.mem_cons_of_mem _ hk)
    rcases g with ⟨op, ins⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl
    · simp only [trace, isAnd, ite_true, List.cons.injEq] at ht
      exact ih htail _ _ _ (by simp [step, ha]) (by simp [step, hb])
        (bounds_append ha hb h (and_bounds hlen h ht.1)) ht.2
    · simp only [trace, isAnd, Bool.false_eq_true, ite_false] at ht
      exact ih htail _ _ _ (by simp [step, ha]) (by simp [step, hb])
        (bounds_append ha hb h (or_bounds h)) ht

private theorem evalBounds (C : Circuit) (hm : Monotone2 C) (a b : Fin 42 → Bool)
    (ht : trace C.gates (List.ofFn a) = trace C.gates (List.ofFn b))
    (hz : C.eval (List.ofFn fun i => a i || b i) = true) :
    C.eval (List.ofFn a) = true ∨ C.eval (List.ofFn b) = true := by
  have h : Bounds (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
    intro i hi
    by_cases hi' : i < 42
    · rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn]
      simpa using hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi')] at hi
      cases hi
  exact runBounds C.gates hm _ _ _ (by simp) (by simp) h ht C.output hz

private def point (p : Fin 21) : Fin 42 := Fin.castAdd 21 p
private def line (l : Fin 21) : Fin 42 := Fin.natAdd 21 l

private def offset : Fin 5 → Fin 21 := ![20, 0, 5, 7, 17]

private abbrev Inc (p l : Fin 21) : Prop := ∃ i, p + offset i = l

private def edgesAt (p : Nat) : List (Nat × Nat) :=
  [(p, 21 + (p + 20) % 21), (p, 21 + p), (p, 21 + (p + 5) % 21),
   (p, 21 + (p + 7) % 21), (p, 21 + (p + 17) % 21)]

private def edges : List (Nat × Nat) := (List.range 21).flatMap edgesAt

private theorem edgesAt_point (p : Fin 21) :
    edgesAt p.val = List.ofFn (fun i => ((point p).val, (line (p + offset i)).val)) := by
  simp [edgesAt, List.ofFn_succ, point, line, offset, Fin.val_add,
    Nat.mod_eq_of_lt p.isLt, Nat.add_comm 21]

private theorem edge_forward {u v : Fin 42} (h : (u.val, v.val) ∈ edges) :
    ∃ p l, u = point p ∧ v = line l ∧ Inc p l := by
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp h
  let p : Fin 21 := ⟨n, List.mem_range.mp hn⟩
  change (u.val, v.val) ∈ edgesAt p.val at hm
  rw [edgesAt_point, List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact ⟨p, p + offset i, Fin.ext (congrArg Prod.fst hi).symm,
    Fin.ext (congrArg Prod.snd hi).symm, i, rfl⟩

private theorem edge_backward {p l : Fin 21} (h : Inc p l) :
    ((point p).val, (line l).val) ∈ edges := by
  obtain ⟨i, rfl⟩ := h
  refine List.mem_flatMap.mpr ⟨p.val, List.mem_range.mpr p.isLt, ?_⟩
  rw [edgesAt_point, List.mem_ofFn]
  exact ⟨i, rfl⟩

private theorem translate (p q : Fin 21) (i : Fin 5) :
    Inc q (p + offset i) ↔ Inc 0 ((p - q) + offset i) := by
  unfold Inc
  simp only [zero_add]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    calc
      offset j = (q + offset j) - q := by abel
      _ = (p - q) + offset i := by rw [hj]; abel
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [hj]; abel⟩

-- Check the differences of the five cyclic offsets.
set_option maxRecDepth 2048 in
private theorem unique_slot :
    ∀ (d : Fin 21) (i j : Fin 5), d ≠ 0 →
      Inc 0 (d + offset i) → Inc 0 (d + offset j) → i = j := by
  decide +kernel

private theorem free_line (P : Finset (Fin 21)) (hP : P.card = 3)
    (p : Fin 21) (hp : p ∉ P) :
    ∃ l, Inc p l ∧ ∀ q ∈ P, ¬ Inc q l := by
  classical
  by_contra! hn
  have blocks (i : Fin 5) : ∃ q ∈ P, Inc q (p + offset i) :=
    hn _ ⟨i, rfl⟩
  choose f hf hi using blocks
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ) (t := P) f
    (fun i _ => hf i) (fun i _ j _ hij => by
      have hd : p - f i ≠ 0 := sub_ne_zero.mpr (fun h => hp (h ▸ hf i))
      exact unique_slot _ i j hd ((translate p (f i) i).mp (hi i))
        ((translate p (f i) j).mp (hij ▸ hi j)))
  simp [hP] at hcard

private noncomputable def input (P : Finset (Fin 21)) (v : Fin 42) : Bool := by
  classical
  exact decide ((∃ p ∈ P, point p = v) ∨
    (∃ l, line l = v ∧ ∀ q ∈ P, ¬ Inc q l))

private theorem point_inj : Function.Injective point :=
  fun _ _ h => Fin.ext (congrArg (fun v : Fin 42 => v.val) h)

private theorem line_inj : Function.Injective line := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 21 + a.val = 21 + b.val at hv
  omega

private theorem point_ne_line (p l : Fin 21) : point p ≠ line l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = 21 + l.val at hv
  omega

private theorem input_point (P : Finset (Fin 21)) (p : Fin 21) :
    input P (point p) = true ↔ p ∈ P := by
  classical
  simp only [input, decide_eq_true_eq]
  constructor
  · rintro (⟨q, hq, he⟩ | ⟨l, he, _⟩)
    · exact (point_inj he) ▸ hq
    · exact (point_ne_line p l he.symm).elim
  · exact fun h => Or.inl ⟨p, h, rfl⟩

private theorem input_line (P : Finset (Fin 21)) (l : Fin 21) :
    input P (line l) = true ↔ ∀ q ∈ P, ¬ Inc q l := by
  classical
  simp only [input, decide_eq_true_eq]
  constructor
  · rintro (⟨p, _, he⟩ | ⟨k, he, h⟩)
    · exact (point_ne_line p l he).elim
    · exact (line_inj he) ▸ h
  · exact fun h => Or.inr ⟨l, rfl, h⟩

private def Computes (C : Circuit) : Prop :=
  ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

private theorem negative {C : Circuit} (hc : Computes C) (P : Finset (Fin 21)) :
    C.eval (List.ofFn (input P)) ≠ true := by
  intro h
  obtain ⟨u, v, he, hu, hv⟩ := (hc _).mp h
  obtain ⟨p, l, rfl, rfl, hi⟩ := edge_forward he
  exact (input_line P l).mp hv p ((input_point P p).mp hu) hi

private theorem union_positive {C : Circuit} (hc : Computes C) {P Q : Finset (Fin 21)}
    (hP : P.card = 3) (hQ : Q.card = 3) (hne : P ≠ Q) :
    C.eval (List.ofFn fun i => input P i || input Q i) = true := by
  have hs : ¬ P ⊆ Q := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
  obtain ⟨p, hp, hpn⟩ : ∃ p ∈ P, p ∉ Q := by
    simpa [Finset.subset_iff] using hs
  obtain ⟨l, he, hl⟩ := free_line Q hQ p hpn
  exact (hc _).mpr ⟨point p, line l, edge_backward he,
    by simp [(input_point P p).mpr hp], by simp [(input_line Q l).mpr hl]⟩

private theorem lower_bound (C : Circuit) (hm : Monotone2 C) (hc : Computes C) :
    10 < {i : Fin C.gates.length | (C.gates.get i).op = GateOp.and}.ncard := by
  classical
  let triples := (Finset.univ : Finset (Fin 21)).powersetCard 3
  let k := C.gates.countP isAnd
  let f (P : triples) : Fin k → Bool :=
    fun i => (trace C.gates (List.ofFn (input P.val))).getD i.val false
  have hf : Function.Injective f := by
    intro P Q he
    apply Subtype.ext
    by_contra hn
    have plen := traceLength C.gates (List.ofFn (input P.val))
    have qlen := traceLength C.gates (List.ofFn (input Q.val))
    have ht : trace C.gates (List.ofFn (input P.val)) =
        trace C.gates (List.ofFn (input Q.val)) := by
      apply List.ext_getElem (plen.trans qlen.symm)
      intro i hi hj
      have hz := congrFun he (⟨i, by simpa only [k, ← plen] using hi⟩ : Fin k)
      simpa only [f, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hz
    have hP := (Finset.mem_powersetCard.mp P.property).2
    have hQ := (Finset.mem_powersetCard.mp Q.property).2
    exact (evalBounds C hm _ _ ht (union_positive hc hP hQ hn)).elim
      (negative hc P.val) (negative hc Q.val)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    triples, Finset.card_powersetCard, Finset.card_univ] at hcard
  rw [← count_eq C]
  by_contra! hk
  have hpow : 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hk
  have hchoose : Nat.choose 21 3 = 1330 := by decide
  omega

end PEqualNP.Outside.L_meta_7025

theorem PEqualNP.Outside.L_meta_7025 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (10 : ℕ) → (21 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hm hc hk
  exact (Nat.not_lt_of_ge hk (PEqualNP.Outside.L_meta_7025.lower_bound C hm hc)).elim
