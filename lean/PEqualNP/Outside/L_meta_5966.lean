import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5966

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma gateAnd (ha : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ ∀ w ∈ (gateAt C j).inputs, val C (List.ofFn x) w = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) hj hop]
  exact ⟨fun h w hw => (h w hw).2, fun h w hw => ⟨ha.2.1 j hj w hw, h w hw⟩⟩

lemma inputsTwo (ha : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ∃ p q, (gateAt C j).inputs = [p,q] :=
  List.length_eq_two.mp (ha.2.2 _ (gateAt_mem hj))

lemma wireAllTrue (ha : IsAO2 n C) :
    ∀ w < n + C.gates.length, val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h : w < n
    · exact val_ofFn C _ ⟨w,h⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases ha.1 _ (gateAt_mem hj) with hop | hop
      · apply (val_and (n := n) (by simp) hj hop).mpr
        intro i hi
        have hi' := ha.2.1 j hj i hi
        exact ⟨hi', ih i hi' (by omega)⟩
      · obtain ⟨p,q,hpq⟩ := inputsTwo ha hj
        have hp : p ∈ (gateAt C j).inputs := by simp [hpq]
        have hp' := ha.2.1 j hj p hp
        exact (val_or (n := n) (by simp) hj hop).mpr ⟨p,hp,hp',ih p hp' (by omega)⟩

lemma junkData {j : ℕ} (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
  obtain ⟨_, hop, hlt, hx⟩ := Finset.mem_filter.mp hj
  exact ⟨hlt, hop, hx⟩

lemma topData {j : ℕ} (hj : j ∈ tops G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ BelowF G C j := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using hj

lemma coneLt {i j : ℕ} (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨_, k, hkj, _, hik⟩ := (inCone_iff n C i j).mp h
    rcases hik with rfl | hik
    · exact hkj
    · exact (ih k hkj hik).trans hkj

lemma coneTrans {i j k : ℕ} (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨hk,l,hl,hm,hjl⟩ := (inCone_iff n C j k).mp hjk
    apply (inCone_iff n C i k).mpr
    refine ⟨hk,l,hl,hm,Or.inr ?_⟩
    rcases hjl with rfl | hjl
    · exact hij
    · exact ih l hl hjl

lemma lowerAndJunk (ht : TopForm G C) {i j : ℕ}
    (hj : (gateAt C j).op = GateOp.and) (hi : (gateAt C i).op = GateOp.and)
    (hcone : InCone n C i j) : i ∈ junk G C := by
  classical
  have hj' := ((inCone_iff n C i j).mp hcone).1
  have hi' := (coneLt hcone).trans hj'
  have hnb : ¬ BelowF G C i := fun h => ht i hi' j hj' hi h hj hcone
  have hex : ∃ x : Fin n → Bool, gateVal n C i x = true ∧ graphFun G ∅ x = false := by
    by_contra h
    exact hnb (fun x hx => Bool.eq_true_of_not_eq_false fun hf => h ⟨x,hx,hf⟩)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi', hi, hi', hex⟩

lemma pairMember {i j k : ℕ} (h : junk G C = {j,k}) (hi : i ∈ junk G C) :
    i = j ∨ i = k := by
  simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hi

def OrPath (n : ℕ) (C : Circuit) (p q : ℕ) : Prop :=
  Relation.ReflTransGen (OrStep n C) p q

lemma gateFromOr (ha : IsAO2 n C) (ht : TopForm G C)
    {j t : ℕ}
    (hblock : ∀ k ∈ junk G C, ¬ InCone n C j k)
    (hto : (gateAt C t).op = GateOp.and) (hit : InCone n C j t) :
    ∃ w ∈ (gateAt C t).inputs, OrPath n C w (n+j) := by
  have route : ∀ i, InCone n C i t → InCone n C j i → OrPath n C (n+i) (n+j) := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi hji
      obtain ⟨hil,k,hki,hk,hjk⟩ := (inCone_iff n C j i).mp hji
      have hor : (gateAt C i).op = GateOp.or := by
        rcases ha.1 _ (gateAt_mem hil) with hia | hio
        · exact (hblock i (lowerAndJunk ht hto hia hi) hji).elim
        · exact hio
      apply Relation.ReflTransGen.head (r := OrStep n C)
        ⟨i,hil,rfl,hor,hk,by omega⟩
      rcases hjk with rfl | hjk
      · exact Relation.ReflTransGen.refl
      · have hkt : InCone n C k t :=
          coneTrans ((inCone_iff n C k i).mpr ⟨hil,k,hki,hk,Or.inl rfl⟩) hi
        exact ih k hki hkt hjk
  obtain ⟨htl,k,hkt,hk,hjk⟩ := (inCone_iff n C j t).mp hit
  refine ⟨n+k,hk,?_⟩
  rcases hjk with rfl | hjk
  · exact Relation.ReflTransGen.refl
  · exact route k ((inCone_iff n C k t).mpr ⟨htl,k,hkt,hk,Or.inl rfl⟩) hjk

lemma noConeJunk {j k : ℕ} (h : junk G C = {j,k}) (hn : ¬ InCone n C j k) :
    ∀ i ∈ junk G C, ¬ InCone n C j i := by
  intro i hi hi'
  rcases pairMember h hi with rfl | rfl
  · exact (Nat.lt_irrefl _ (coneLt hi'))
  · exact hn hi'

lemma noJunkBelow {j k : ℕ} (h : junk G C = {j,k}) (hn : ¬ InCone n C k j) :
    ∀ i ∈ junk G C, ¬ InCone n C i j := by
  intro i hi hi'
  rcases pairMember h hi with rfl | rfl
  · exact (Nat.lt_irrefl _ (coneLt hi'))
  · exact hn hi'

lemma wireSupport (ha : IsAO2 n C) {w : ℕ} {x : Fin n → Bool}
    (hx : val C (List.ofFn x) w = true) :
    (∃ v : Fin n, OrPath n C w v.val ∧ x v = true) ∨
    (∃ i < C.gates.length, (gateAt C i).op = GateOp.and ∧
      OrPath n C w (n+i) ∧ gateVal n C i x = true) := by
  obtain ⟨z,hp,hz,ht⟩ := or_trace (n := n) (by simp) w hx
  rcases ht with h | ⟨i,hi,rfl,ho⟩
  · left
    refine ⟨⟨z,h⟩,hp,?_⟩
    exact (val_ofFn C x ⟨z,h⟩).symm.trans hz
  · exact Or.inr ⟨i,hi,(ha.1 _ (gateAt_mem hi)).resolve_right ho,hp,hz⟩

def fires {n : ℕ} (a b : Fin n → Bool) (x : Fin n → Bool) : Prop :=
  (∃ u, a u = true ∧ x u = true) ∧ (∃ v, b v = true ∧ x v = true)

lemma pureJunk (ha : IsAO2 n C) (ht : TopForm G C) {j : ℕ}
    (hj : j ∈ junk G C) (hn : ∀ i ∈ junk G C, ¬ InCone n C i j) :
    ∃ a b : Fin n → Bool, ∀ x, gateVal n C j x = true ↔ fires a b x := by
  classical
  obtain ⟨hjl,hjo,_⟩ := junkData hj
  obtain ⟨p,q,hpq⟩ := inputsTwo ha hjl
  let A (w : ℕ) (v : Fin n) : Bool := decide (OrPath n C w v.val)
  have wire (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
      val C (List.ofFn x) w = true ↔ ∃ v, A w v = true ∧ x v = true := by
    constructor
    · intro h
      rcases wireSupport ha h with ⟨v,hr,hv⟩ | ⟨i,hi,hop,hr,_⟩
      · exact ⟨v,decide_eq_true hr,hv⟩
      · have hc := operand_cone hjl hw (ha.2.1 j hjl w hw) hr
        exact (hn i (lowerAndJunk ht hjo hop hc) hc).elim
    · rintro ⟨v,hr,hv⟩
      exact orStep_up (n := n) (by simp) (of_decide_eq_true hr)
        ((val_ofFn C x v).trans hv)
  refine ⟨A p,A q,fun x => ?_⟩
  rw [gateAnd ha hjl hjo, hpq]
  have hp : p ∈ (gateAt C j).inputs := by simp [hpq]
  have hq : q ∈ (gateAt C j).inputs := by simp [hpq]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [wire p hp, wire q hq]
  rfl

def Joint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true

lemma jointOrCommon (ha : IsAO2 n C) (ht : TopForm G C) {j k t : ℕ}
    (hpair : junk G C = {j,k}) (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (htop : t ∈ tops G C) (hjt : InCone n C j t) (hkt : InCone n C k t) :
    Joint G C j k ∨ (wmax G C j ∩ wmax G C k).Nonempty := by
  have hj : j ∈ junk G C := by simp [hpair]
  have hk : k ∈ junk G C := by simp [hpair]
  have hpair' : junk G C = {k,j} := by rw [hpair, Finset.pair_comm]
  obtain ⟨htl,hto,htb⟩ := topData htop
  obtain ⟨p,q,hpq⟩ := inputsTwo ha htl
  obtain ⟨u,hu,hrj⟩ := gateFromOr ha ht (noConeJunk hpair hjk) hto hjt
  obtain ⟨v,hv,hrk⟩ := gateFromOr ha ht (noConeJunk hpair' hkj) hto hkt
  have topTrue (x : Fin n → Bool) (hp : val C (List.ofFn x) p = true)
      (hq : val C (List.ofFn x) q = true) : graphFun G ∅ x = true := by
    apply htb x ∘ (gateAnd ha htl hto x).mpr
    intro w hw
    simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hp
    · exact hq
  have up (x : Fin n → Bool) {w z : ℕ} (hr : OrPath n C w z)
      (h : val C (List.ofFn x) z = true) : val C (List.ofFn x) w = true :=
    orStep_up (n := n) (by simp) hr h
  have hw (w z : ℕ) (hwi : w ∈ (gateAt C t).inputs)
      (hrj : OrPath n C z (n+j)) (hrk : OrPath n C z (n+k))
      (hF : ∀ x : Fin n → Bool, val C (List.ofFn x) z = true →
        val C (List.ofFn x) w = true → graphFun G ∅ x = true) :
      Joint G C j k ∨ (wmax G C j ∩ wmax G C k).Nonempty := by
    have hlt := ha.2.1 t htl w hwi
    have hv := wireAllTrue ha w (by omega)
    rcases wireSupport ha hv with ⟨a,hr,_⟩ | ⟨i,hi,hop,hr,_⟩
    · right
      refine ⟨a,Finset.mem_inter.mpr ⟨?_,?_⟩⟩ <;>
        apply Finset.mem_filter.mpr <;> refine ⟨Finset.mem_univ _,fun x hx hax => ?_⟩
      · exact hF x (up x hrj hx) (up x hr ((val_ofFn C x a).trans hax))
      · exact hF x (up x hrk hx) (up x hr ((val_ofFn C x a).trans hax))
    · have hc := operand_cone htl hwi hlt hr
      left
      intro x hxj hxk
      rcases pairMember hpair (lowerAndJunk ht hto hop hc) with rfl | rfl
      · exact hF x (up x hrk hxk) (up x hr hxj)
      · exact hF x (up x hrj hxj) (up x hr hxk)
  simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu] at hrj <;> rw [hv] at hrk
  · exact hw q p (by simp [hpq]) hrj hrk topTrue
  · exact Or.inl fun x hxj hxk => topTrue x (up x hrj hxj) (up x hrk hxk)
  · exact Or.inl fun x hxj hxk => topTrue x (up x hrk hxk) (up x hrj hxj)
  · exact hw p q (by simp [hpq]) hrj hrk (fun x hq hp => topTrue x hp hq)

lemma hitsMiss {a b : Fin 11 → Bool} {x : Fin 11 → Bool} (h : ¬ fires a b x) :
    (¬ ∃ u, a u = true ∧ x u = true) ∨ (¬ ∃ u, b u = true ∧ x u = true) := by
  classical
  by_cases ha : ∃ u, a u = true ∧ x u = true
  · exact Or.inr fun hb => h ⟨ha,hb⟩
  · exact Or.inl ha

def hits (a x : Fin 11 → Bool) : Prop := ∃ u, a u = true ∧ x u = true

def inputMask (m : ℕ) (v : Fin 11) : Bool := m.testBit v.val

def ends (i : Fin 16) : Fin 11 × Fin 11 :=
  ([ (0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7),
     (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9) ] :
    List (Fin 11 × Fin 11)).getD i.val (0,0)

def edgeSym (i : Fin 16) : Sym2 (Fin 11) := s((ends i).1,(ends i).2)

def edgeInput (i : Fin 16) : Fin 11 → Bool := pairInput (ends i).1 (ends i).2

abbrev fixedGraph : SimpleGraph (Fin 11) :=
  edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def independentRow (i : Fin 24) : ℕ :=
  [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,
    1066,1186,1288,1408,1546].getD i.val 0

def unpack (p n w : ℕ) : ℕ := (p >>> n) &&& (2^w-1)

def rowOf (p : ℕ) (i : ℕ) : Fin 24 := Fin.ofNat 24 (unpack p (5*i) 5)

def unionContains (r s : ℕ) (e : Fin 16) : Bool :=
  inputMask (r ||| s) (ends e).1 && inputMask (r ||| s) (ends e).2

lemma hitTransfer {a : Fin 11 → Bool} {r s : ℕ} {e : Fin 16}
    (h : hits a (edgeInput e)) (he : unionContains r s e = true) :
    hits a (inputMask r) ∨ hits a (inputMask s) := by
  obtain ⟨x,hx,hxe⟩ := h
  have hxe' : x = (ends e).1 ∨ x = (ends e).2 := by
    simpa [edgeInput, pairInput] using hxe
  have hu : inputMask (r ||| s) x = true := by
    rcases Bool.and_eq_true_iff.mp he with ⟨h₁,h₂⟩
    rcases hxe' with h | h
    · simpa only [h] using h₁
    · simpa only [h] using h₂
  simp only [inputMask, Nat.testBit_or, Bool.or_eq_true] at hu
  exact hu.elim (fun h => Or.inl ⟨x,hx,h⟩) (fun h => Or.inr ⟨x,hx,h⟩)

-- A row is colored by an operand that misses it. An edge in the union of two
-- rows forces every operand to hit at least one of the rows.
lemma cliqueNoColor {k : ℕ} (side : Fin k → Fin 11 → Bool)
    (row : Fin (k+1) → ℕ)
    (miss : ∀ i, ∃ j, ¬ hits (side j) (inputMask (row i)))
    (edge : ∀ i j, i < j → ∃ e : Fin 16,
      unionContains (row i) (row j) e = true ∧ ∀ a, hits (side a) (edgeInput e)) : False := by
  classical
  choose color hcolor using miss
  have collide (i j : Fin (k+1)) (hij : i < j) (heq : color i = color j) : False := by
    obtain ⟨e,he,hs⟩ := edge i j hij
    rcases hitTransfer (hs (color i)) he with h | h
    · exact hcolor i h
    · exact hcolor j (heq ▸ h)
  have hinj : Function.Injective color := by
    intro i j h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (collide i j hlt h).elim
    · exact heq
    · exact (collide j i hgt h.symm).elim
  have h := Fintype.card_le_of_injective color hinj
  simp at h

def MaskLe (n : ℕ) (a b : ℕ) : Prop :=
  ∀ i : Fin n, a.testBit i.val = true → b.testBit i.val = true

def clearMask (n h i : ℕ) : ℕ := h &&& ((2^n-1) ^^^ (1 <<< i))

lemma maskLe_zero (n m : ℕ) : MaskLe n 0 m := by
  intro i hi
  simp at hi

lemma maskLe_full (n m : ℕ) : MaskLe n m (2^n-1) := by
  intro i _
  simp [i.isLt]

lemma maskLe_set {n lo m i : ℕ} (h : MaskLe n lo m) (hi : m.testBit i = true) :
    MaskLe n (lo ||| (1 <<< i)) m := by
  intro j hj
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at hj
  rcases hj with hj | hj
  · exact h j hj
  · simpa only [← hj] using hi

lemma maskLe_clear {n m hi i : ℕ} (h : MaskLe n m hi) (hi' : m.testBit i = false) :
    MaskLe n m (clearMask n hi i) := by
  intro j hj
  have hne : i ≠ j.val := fun e => by rw [e,hj] at hi'; contradiction
  simp [clearMask, Nat.testBit_and, Nat.testBit_xor, Nat.one_shiftLeft,
    hne, j.isLt, h j hj]

lemma maskCoding : ∀ {n : ℕ} (a : Fin n → Bool), ∃ m : ℕ, ∀ i, m.testBit i.val = a i := by
  intro n
  induction n with
  | zero =>
    intro a
    exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro a
    obtain ⟨m,hm⟩ := ih (fun i => a i.succ)
    refine ⟨(m <<< 1) ||| (a 0).toNat, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · cases a 0 <;> simp
    · have hb : (a 0).toNat.testBit (j.val+1) = false := by
        apply Nat.testBit_lt_two_pow
        have hp : 0 < 2^j.val := Nat.pow_pos (by decide)
        rw [pow_succ]
        have hq : (a 0).toNat ≤ 1 := by cases a 0 <;> decide
        omega
      change ((m <<< 1) ||| (a 0).toNat).testBit (j.val+1) = _
      simp [Nat.testBit_or, Nat.testBit_shiftLeft, hb, hm j]

def checkTree (n : ℕ) (leaf : ℕ → ℕ → ℕ → Bool) :
    ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)
  | _, _, _, [] => none
  | 0, lo, hi, t :: ts => if t == 0 then none else if leaf lo hi t then some ts else none
  | d+1, lo, hi, t :: ts =>
    if t == 0 then
      (checkTree n leaf d lo (clearMask n hi d) ts).bind
        (checkTree n leaf d (lo ||| (1 <<< d)) hi)
    else if leaf lo hi t then some ts else none

lemma checkTreeSound {n : ℕ} {leaf : ℕ → ℕ → ℕ → Bool} {P : ℕ → Prop}
    (leafSound : ∀ lo hi t m, leaf lo hi t = true → MaskLe n lo m → MaskLe n m hi → P m) :
    ∀ d lo hi t rest m, checkTree n leaf d lo hi t = some rest →
      MaskLe n lo m → MaskLe n m hi → P m := by
  intro d
  induction d with
  | zero =>
    intro lo hi t rest m h hl hh
    cases t with
    | nil => simp [checkTree] at h
    | cons t ts =>
      by_cases ht : t = 0
      · simp [checkTree, ht] at h
      · by_cases hleaf : leaf lo hi t = true
        · exact leafSound lo hi t m hleaf hl hh
        · simp [checkTree, ht, hleaf] at h
  | succ d ih =>
    intro lo hi t rest m h hl hh
    cases t with
    | nil => simp [checkTree] at h
    | cons t ts =>
      by_cases ht : t = 0
      · simp only [checkTree, ht] at h
        change (checkTree n leaf d lo (clearMask n hi d) ts).bind
          (checkTree n leaf d (lo ||| (1 <<< d)) hi) = some rest at h
        cases hp : checkTree n leaf d lo (clearMask n hi d) ts with
        | none => simp [hp] at h
        | some next =>
          have hn : checkTree n leaf d (lo ||| (1 <<< d)) hi next = some rest := by
            rw [hp] at h
            exact h
          cases hb : m.testBit d
          · exact ih _ _ _ _ _ hp hl (maskLe_clear hh hb)
          · exact ih _ _ _ _ _ hn (maskLe_set hl hb) hh
      · by_cases hleaf : leaf lo hi t = true
        · exact leafSound lo hi t m hleaf hl hh
        · simp [checkTree, ht, hleaf] at h

def allFin {n : ℕ} (f : Fin n → Bool) : Bool := (List.finRange n).all f

lemma allFin_eq {n : ℕ} {f : Fin n → Bool} : allFin f = true ↔ ∀ i, f i = true := by
  simp [allFin, List.all_eq_true]

lemma fin_any_eq {n : ℕ} {f : Fin n → Bool} :
    (List.finRange n).any f = true ↔ ∃ i, f i = true := by
  simp [List.any_eq_true]

lemma rowSmall : ∀ r : Fin 24, independentRow r < 2^11 := by decide

lemma edgesAll : (Finset.univ.image edgeSym) = fixedGraph.edgeFinset := by decide +kernel

lemma rowIndependent : ∀ r : Fin 24,
    graphFun fixedGraph ∅ (inputMask (independentRow r)) = false := by decide +kernel

def touches (m : ℕ) (e : Fin 16) : Bool :=
  inputMask m (ends e).1 || inputMask m (ends e).2

lemma touchesMono {m h : ℕ} (hl : MaskLe 11 m h) {e : Fin 16} (he : touches m e = true) :
    touches h e = true := by
  apply Bool.or_eq_true_iff.mpr
  exact (Bool.or_eq_true_iff.mp he).imp (hl _) (hl _)

def meetsRow (m : ℕ) (r : Fin 24) : Bool := !((m &&& independentRow r) == 0)

lemma meetsRowSpec {m : ℕ} {r : Fin 24} :
    meetsRow m r = true ↔ ∃ v : Fin 11, m.testBit v.val = true ∧
      inputMask (independentRow r) v = true := by
  constructor
  · intro h
    by_contra hn
    have hz : m &&& independentRow r = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hi : i < 11
      · cases hm : m.testBit i
        · rfl
        · have hr : (independentRow r).testBit i = false :=
            Bool.eq_false_iff.mpr fun h' => hn ⟨⟨i,hi⟩,hm,h'⟩
          simp [hr]
      · have hr : (independentRow r).testBit i = false :=
          Nat.testBit_lt_two_pow ((rowSmall r).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hr]
    simp [meetsRow,hz] at h
  · rintro ⟨v,hm,hr⟩
    have h : (m &&& independentRow r).testBit v.val = true := by
      rw [Nat.testBit_and, hm]
      exact hr
    have hn : m &&& independentRow r ≠ 0 := by
      intro hz
      simp [hz] at h
    simp [meetsRow, hn]

def starPairCheck (lo : ℕ) (e f : Fin 16) (p : ℕ) : Bool :=
  allFin (n := 3) (fun i => meetsRow lo (rowOf p i.val)) &&
  allFin (n := 3) (fun i => allFin (n := 3) fun j => !decide (i < j) ||
    unionContains (independentRow (rowOf p i.val)) (independentRow (rowOf p j.val)) e ||
    unionContains (independentRow (rowOf p i.val)) (independentRow (rowOf p j.val)) f)

lemma starPairSound {lo m p : ℕ} (hlo : MaskLe 11 lo m) {e f : Fin 16}
    {a b : Fin 11 → Bool} (h : starPairCheck lo e f p = true)
    (hmiss : ∀ r, meetsRow m r = true → ¬ fires a b (inputMask (independentRow r)))
    (he : fires a b (edgeInput e)) (hf : fires a b (edgeInput f)) : False := by
  obtain ⟨hrows,hpairs⟩ := Bool.and_eq_true_iff.mp h
  let side (i : Fin 2) : Fin 11 → Bool := if i = 0 then a else b
  have hs (x : Fin 11 → Bool) (hx : fires a b x) (i : Fin 2) : hits (side i) x := by
    fin_cases i
    · exact hx.1
    · exact hx.2
  refine cliqueNoColor side (fun i => independentRow (rowOf p i.val)) ?_ ?_
  · intro i
    have hr := allFin_eq.mp hrows i
    have hm : meetsRow m (rowOf p i.val) = true := by
      obtain ⟨v,hv,hrv⟩ := meetsRowSpec.mp hr
      exact meetsRowSpec.mpr ⟨v,hlo v hv,hrv⟩
    rcases hitsMiss (hmiss _ hm) with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  · intro i j hij
    have hp := allFin_eq.mp (allFin_eq.mp hpairs i) j
    simp only [hij, decide_true, Bool.not_true, Bool.false_or] at hp
    rcases Bool.or_eq_true_iff.mp hp with h | h
    · exact ⟨e,h,hs _ he⟩
    · exact ⟨f,h,hs _ hf⟩

def groupEdge (p : ℕ) (i : Fin 3) : Fin 16 := Fin.ofNat 16 (unpack p (2+4*i.val) 4)

def groupHas (p : ℕ) (e : Fin 16) : Bool :=
  (List.finRange 3).any fun i => decide (i.val < p % 4) && decide (groupEdge p i = e)

def groupCheck (lo p : ℕ) : Bool :=
  allFin (n := 3) fun i => allFin (n := 3) fun j =>
    !decide (i < j ∧ j.val < p % 4) ||
      starPairCheck lo (groupEdge p i) (groupEdge p j) (unpack p (14+15*(i.val+j.val-1)) 15)

lemma groupSafe {lo m p : ℕ} (hlo : MaskLe 11 lo m) {e f : Fin 16}
    {a b : Fin 11 → Bool} (h : groupCheck lo p = true)
    (hmiss : ∀ r, meetsRow m r = true → ¬ fires a b (inputMask (independentRow r)))
    (he : groupHas p e = true) (hf : groupHas p f = true)
    (hfe : fires a b (edgeInput e)) (hff : fires a b (edgeInput f)) : e = f := by
  obtain ⟨i,his⟩ := fin_any_eq.mp he
  obtain ⟨j,hjs⟩ := fin_any_eq.mp hf
  obtain ⟨hib,hi'⟩ := Bool.and_eq_true_iff.mp his
  obtain ⟨hjb,hj'⟩ := Bool.and_eq_true_iff.mp hjs
  have hiBound : i.val < p % 4 := of_decide_eq_true hib
  have hjBound : j.val < p % 4 := of_decide_eq_true hjb
  obtain rfl := (of_decide_eq_true hi').symm
  obtain rfl := (of_decide_eq_true hj').symm
  have sep (i j : Fin 3) (hij : i < j) (hj : j.val < p % 4)
      (hi' : fires a b (edgeInput (groupEdge p i)))
      (hj' : fires a b (edgeInput (groupEdge p j))) : False := by
    have ht := allFin_eq.mp (allFin_eq.mp h i) j
    simp only [hij, hj, and_self, decide_true, Bool.not_true, Bool.false_or] at ht
    exact starPairSound hlo ht hmiss hi' hj'
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact (sep i j hlt hjBound hfe hff).elim
  · rfl
  · exact (sep j i hgt hiBound hff hfe).elim

-- A star leaf packs seven edge groups, each with witnesses for its edge pairs.
def starGroup (p : ℕ) (i : Fin 7) : ℕ := unpack (p-1) (64*i.val) 64

def starLeaf (lo hi p : ℕ) : Bool :=
  (allFin (n := 16) fun e => !touches hi e ||
    (List.finRange 7).any (fun i => groupHas (starGroup p i) e)) &&
  (allFin (n := 7) fun i => groupCheck lo (starGroup p i))

lemma starLeafSound {lo hi p m : ℕ} (h : starLeaf lo hi p = true)
    (hlo : MaskLe 11 lo m) (hhi : MaskLe 11 m hi)
    {a b : Fin 11 → Bool} {E : Finset (Fin 16)}
    (hedge : ∀ e ∈ E, fires a b (edgeInput e))
    (htouch : ∀ e ∈ E, touches m e = true)
    (hmiss : ∀ r, meetsRow m r = true → ¬ fires a b (inputMask (independentRow r))) :
    E.card ≤ 7 := by
  classical
  obtain ⟨hcover,hgroup⟩ := Bool.and_eq_true_iff.mp h
  have choice (e : E) : ∃ i : Fin 7, groupHas (starGroup p i) e.val = true := by
    have ht := touchesMono hhi (htouch e e.property)
    have h := allFin_eq.mp hcover e.val
    rw [ht, Bool.not_true, Bool.false_or] at h
    exact fin_any_eq.mp h
  choose color hc using choice
  have hinj : Function.Injective color := by
    intro e f hef
    apply Subtype.ext
    exact groupSafe hlo (allFin_eq.mp hgroup (color e)) hmiss (hc e)
      (hef.symm ▸ hc f) (hedge e e.property) (hedge f f.property)
  simpa using Fintype.card_le_of_injective color hinj

def edgeFlags (m : ℕ) : Finset (Fin 16) := Finset.univ.filter fun e => m.testBit e.val

-- A joint leaf either bounds the remaining edge set or gives five rows and
-- one edge in the union of each pair.
def jointEdge (p : ℕ) (i j : Fin 5) : Fin 16 :=
  Fin.ofNat 16 (unpack p (25+4*(5*i.val+j.val)) 4)

def jointLeaf (lo hi p : ℕ) : Bool :=
  if p = 1 then decide ((edgeFlags hi).card ≤ 8)
  else
    allFin (n := 5) fun i => allFin (n := 5) fun j =>
      !decide (i < j) ||
      (lo.testBit (jointEdge (p-2) i j).val &&
        unionContains (independentRow (rowOf (p-2) i.val))
          (independentRow (rowOf (p-2) j.val)) (jointEdge (p-2) i j))

lemma jointLeafSound {lo hi p m : ℕ} (h : jointLeaf lo hi p = true)
    (hlo : MaskLe 16 lo m) (hhi : MaskLe 16 m hi)
    {a b c d : Fin 11 → Bool}
    (hedge : ∀ e ∈ edgeFlags m, fires a b (edgeInput e) ∧ fires c d (edgeInput e))
    (hmiss : ∀ r, ¬ (fires a b (inputMask (independentRow r)) ∧
      fires c d (inputMask (independentRow r)))) : (edgeFlags m).card ≤ 8 := by
  classical
  by_cases hp : p = 1
  · have hc : (edgeFlags hi).card ≤ 8 := by simpa [jointLeaf,hp] using h
    apply (Finset.card_le_card ?_).trans hc
    intro e he
    simp only [edgeFlags, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact hhi e he
  · exfalso
    simp only [jointLeaf, hp, ite_false] at h
    let side (i : Fin 4) : Fin 11 → Bool :=
      if i = 0 then a else if i = 1 then b else if i = 2 then c else d
    refine cliqueNoColor side (fun i => independentRow (rowOf (p-2) i.val)) ?_ ?_
    · intro i
      have hm := hmiss (rowOf (p-2) i.val)
      rcases not_and_or.mp hm with hab | hcd
      · rcases hitsMiss hab with ha | hb
        · exact ⟨0,ha⟩
        · exact ⟨1,hb⟩
      · rcases hitsMiss hcd with hc | hd
        · exact ⟨2,hc⟩
        · exact ⟨3,hd⟩
    · intro i j hij
      have ht := allFin_eq.mp (allFin_eq.mp h i) j
      simp only [hij, decide_true, Bool.not_true, Bool.false_or] at ht
      obtain ⟨hb,hu⟩ := Bool.and_eq_true_iff.mp ht
      let e := jointEdge (p-2) i j
      have he : e ∈ edgeFlags m :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlo e hb⟩
      obtain ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ := hedge e he
      refine ⟨e,hu,fun v => ?_⟩
      fin_cases v
      · exact ha
      · exact hb
      · exact hc
      · exact hd


-- Each zero splits on the next bit. A positive entry certifies one leaf.
def starProgram0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0,
  0, 0x150000000000000011000000000000000d000000000000000900000000000000050000000000000002, 0x1d000000000000001903040988136010c704c209bc0f081484, 0, 0x2500000000000000210000000000000015000000000000000d000000000000000900000000000000050000000010184103, 0x1504c60acc2c10250f0142099413081887031217b02f4821c4, 0,
  0, 0x2d000000000000002900000000000000150000000000000011000000000000000d00000000131880860000000000000002, 0x1360014e000000000208010a03cc2bcc13302d87031427b04f5029c4, 0x2900000000000000250000000000000021000000000000000d000000000310410a041229c053486dc704ca181433805944, 0, 0, 0,
  0x35000000000000003100000000000000190000000000000015000000000000000d0000000000000005018a489891291084, 0x31000000000000001d000000001568034e008209881308108704c8079013781944, 0x3500000000000000250000000000000015000000000d49030e010612902418590b000000000000000503521834304861c4, 0x25000000000000001504cc49b48d20b50f044c288c4418ad8b035469a89368b287035638b47150a1c4, 0, 0, 0,
  0x390000000000000031000000000000001d0000000000000019000000001472014e02928a29144a10870000000000000002, 0x5061b502e40e50f051054a0b440714b04a08a411428798703921838304061c4, 0x39000000000000002d000000000e30829a04d03b4c6e40a50f0510649c5340f14b039229b87340a1c70000000000000002, 0x1d00000000000000190000000000000015050e4b50ad31250f05226a14923936cb045caa4516a13a87039248a091697204, 0, 0, 0,
  0, 0, 0, 0x3d00000000000000290000000000000021000000000000000d000000000000000900000000000000050000000000000002, 0x290000000000000011000000000000000d041ecabd95083c87055817b035782144, 0xc10010e05ea083d93083d4b03582acc13682987039817b02f7021c4, 0x1560c2960000000015184252000000000000000d0000000000000009049a1ac195287d8703121830304861c4,
  0x3d000000000000002d000000001360c252000000001560814e030c260c4618a98b039629b07350a1c70000000000000002, 0x3d000000001539425205626ab49161b6cf055846149529194b039a6ab89561b287039858b0b17321c4, 0, 0, 0x3d0000000000000039000000000d62829a05168ad12c52250f051a86a5144a314b03989a31346221c70000000000000002, 0, 0,
  0x3d0000000000000039000000000000002d035027344c40b10f0558260c5340e94b039229b07340a1c70000000000000002, 0x3d000000000000002d03d027b10c10390f04cc03041308194b039a29a0d5983287039207b02f4021c4, 0x2d00000000106083d204e0983915987a4f04ca12883340594b039a29a0b598728703101830304061c4, 0x3d052298a0d4393a53051846b09461194f05226a14923936cb03944a2095a13287039858b0b16221c4, 0, 0, 0,
  0, 0, 0, 0, 0x3d0000000000000039000000000000002d000000000000000d000000000000000900000000000000050000000000000002, 0x3d0000000000000039000000000000002d000000000000001100000000176000c605c20bbc0f081484, 0x39000000000000002d000000000000001d000000000c10010e041ecbd413083c8704e208bc13781944,
  0x3d00000000178243a60000000000000021000000000000000d000000001078c2ca02461ba437185d0705ca179437785944, 0, 0x3d00000000000000390000000000000029000000000000000d000000000f18810a03d429bc5350adc704de679857789944, 0, 0x3d000000000000002900000000179842e60000000000000021000000000000000d03d22bd03310790704de19bc2f105484, 0x3d000000000000002905e817a453183a5304ca06141360194f04060bcc13082c87031217b02f4821c4, 0,
  0x390000000000000031000000000000001d05e0d8bdb7813e5b05de67b4d7692d4f018a4b989729108705da5bc48f697604, 0x3d04c839906620a59305e847b55369394f05e229906f18b6cb035469a89368b287035637b46f50a1c4, 0x3d000000000000003900000000115203120522f8bdd472194f05e2aa45305a36cb03dc9a39347a21c705a897b957822a44, 0, 0, 0, 0,
  0, 0, 0x3d000000000000002d00000000000000290000000000000021000000000000000d0000000017b3038600000000107b0083, 0x3d000000000000002d00000000000000290000000000000011000000000000000d04120bd815083887055817b035782144, 0x3d0000000000000029000000000f70839204da06b01360194f04060bcc13082c87039817b02f7021c4, 0x3d000000000000003905461bd42f60e50f05de383c75786d4b034e1ab075286987031217b02f4861c4, 0xf6083d205e027b05598ee4f04d8630c5378d94b03dcabd05360ba87039627b06f50a1c4,
  0x3d045eebd895613997054e5bd4ac31250f05626a94903936cb039a6ab89561b287039857b0af7321c4, 0x3d05e087a9145a3a53051ac6b11462194f05e2aa45305a36cb039aaa3515a23287041887b12f6221c4, 0, 0, 0, 0, 0,
  0, 0, 0, 0x3500000000000000250000000000000015000000000000000d000000000000000900000000000000050000000000000002, 0x250000000000000015000000000000001100000000136000c604c81bc40f083484, 0x350000000000000019000000001598424e008209881308108705260a3c13781d44, 0x3500000000000000250000000000000015000000001318410a05665994359858c705521ac0304861c4,
  0x1599836a000000000000002100000000000000150000000000000011000000001598c24e05d42bcc5350adc701862b9857189884, 0x35000000000000001904ce4accad31250f05e6491c93292d4b05aa6acc949929c7051a5a4491697204, 0x350000000000000031000000000000001905e89ba9135a3a5305e68bb953722d4f04dc99b9349a21c70396abb9574a2884, 0, 0, 0, 0,
  0, 0, 0x159b436a0000000000000025000000000000002100000000159b014e00000000000000090000000017ab03c60000000000000002, 0x3500000000159842a6000000001360010e041ecbd413083c8704d817b033782144, 0x3504c60acc2c10250f05ea083d93083d4b03582acc13682987039817b02f7021c4, 0x350000000000000025000000001598414e04183bc193187d0b034e1acc3328698703121830304861c4, 0x3d000000001360c252000000001560814e05e669987718b6cb030c29b05330a98703962bb07750a1c4,
  0x5ea48b0d3313f5305e658b0d5996e4f04d846149329194b051c49b895993287039858b0b17321c4, 0x17a343b600000000176b03da04d68acd2c52250f05e68ba9334a2d4b039aa9b5159a328703989bb1376221c4, 0, 0, 0, 0x2105eb0ad1f49c3e5f05a8fbd1f59bfa9704e2fac5f59bd90f05e719c61383f6cb00000000000000050000000000000002, 0x3d04e0499c8f31259305e84a3db369394f05e64994903936cb05aa6acc949929c7051a5a448f697204,
  0x3d0000000000000039000000001152031204e2f8bdd372194f05e2a9c5305a36cb056089b9347a21c7056697b957822a44, 0x3d000000000000002900000000137b839205e709bd959c2e4f04dac9459383d94b041cd9b9b58332070526dbc58f7335c4]

def starProgram : List ℕ := starProgram0

def jointProgram0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 1, 0, 1, 0,
  1, 0xa0000ac000b0c00ad0c136b0a3, 0, 0, 1, 0, 1,
  0, 1, 0, 1, 0xc0000880012c80088c81331062, 0, 0,
  1, 0, 1, 0xa0000ac000b0c00ad0c136b0a3, 0, 0, 1,
  0xe0000aa000ab000aaee149b922, 0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0,
  0, 0, 1, 0, 1, 0, 1,
  0x140000aa000cd400aacc159b4c2, 0, 0, 1, 0, 1, 0xa0000ac000b0c00ad0c136b0a3,
  0, 0, 1, 0xe0000aa000ab000aaee149b922, 0, 0, 1,
  0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0, 0, 0, 1, 0x140000cc000cd40132cc159b4c3,
  0xe00014e000f2e012f2e15a4d23, 0, 0, 0, 1, 0, 1,
  0x140000a800112800a908159b063, 0x140000cc000cd40132cc159b4c3, 0xe00014e000f2e012f2e15a4d23, 0, 0, 0, 0,
  1, 0, 1, 0, 1, 0x160000aa000cd600aacc179c4c2, 0,
  0, 1, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0, 0,
  1, 0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23, 0, 0, 0, 1,
  0x160000aa000ab0013370179c185, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0, 0, 0,
  1, 0, 1, 0x140000aa000cd400aacc159b4c2, 0, 0, 1,
  0xe00014e000aaa00aaae15a4d02, 0, 0, 1, 0, 1, 0x60000680006c80068c80c31042,
  0x140000aa000cd400aacc159b4c2, 0, 0, 0, 1, 0, 1,
  0, 1, 0x60001660006a600a6a617acd82, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0]

def jointProgram1 : List ℕ := [
  0, 0, 1, 0, 1, 0, 1,
  0x60001660006a600a6a617acd82, 0x140000cc000cd40132cc159b4c3, 0xe00014e000f2e012f2e15a4d23, 0, 0, 0, 0,
  1, 0, 1, 0x600016600133201333617ace05, 0x160000aa000ab0013370179c185, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125,
  0, 0, 0, 0, 0, 1, 0,
  1, 0, 1, 0xe0000aa000ab800aaec149a082, 0, 0, 1,
  0, 1, 0xa0000ac000b0c00ad0c136b0a3, 0, 0, 1, 0xe0000aa000ab000aaee149b922,
  0x1800011000111800ecec0e6a4a2, 0, 0, 0, 1, 0, 1,
  0, 1, 0xc0000880012c80088c81331062, 0, 0, 1, 0,
  1, 0x12000088000ee80088e8145a042, 0xe00012e0018d800f2ec149a483, 0, 0, 0, 1,
  0xa0000b8000b1000b1181373527, 0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0,
  0, 0, 1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0x1800011000111800ecec0e6a4a2, 0,
  0, 0, 0, 1, 0, 1, 0x140000aa000cd400aacc159b4c2,
  0, 0, 1, 0xe00014e000aaa00aaae15a4d02, 0x1800015400155800ecec0e6a8c2, 0, 0,
  0, 1, 0xa0000b8000b1000b1181373527, 0, 0, 1, 0x80001080008c800c8c80d31442,
  0xa0000ac000b0c00ad0c136b0a3, 0, 0, 0, 1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922,
  0x1800011000111800ecec0e6a4a2, 0x1400019400133801595816a3528, 0, 0, 0, 0, 0,
  1, 0, 1, 0x160000aa000cd600aacc179c4c2, 0, 0, 1,
  0xe00016e000aaa00aaae17a4d02, 0xc00018e0016d800d6ec117a0c4, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0, 0, 0,
  0, 0, 1, 0x140000aa000ab801595815a3508, 0, 0, 1,
  0, 1, 0x60000680006c80068c80c31042, 0x140000aa000cd400aacc159b4c2, 0, 0, 0]

def jointProgram2 : List ℕ := [
  1, 0, 1, 0x60000680006e80068e80c52042, 0xe00014e000aaa00aaae15a4d02, 0x1800015400155800ecec0e6a8c2, 0x100001180019100171181273529,
  0x1400019400133801595816a3528, 0, 0, 0, 0, 0, 0,
  1, 0, 1, 0, 1, 0, 1,
  0xe000088001ba80088e8149a0c2, 0, 0, 1, 0, 1, 0xa0000ac000b0c00ad0c136b0a3,
  0xe0001ba0010f000f10e16ab523, 0, 0, 0, 1, 0, 1,
  0, 1, 0xc0000880012c80088c81331062, 0, 0, 1, 0,
  1, 0x12000088000ee80088e8145a042, 0, 0, 1, 0xc0000880012c80088c81331062, 0,
  0, 1, 0x600006c000a6600a66c136b082, 0xc0000880012c80088c81331062, 0, 0, 0,
  1, 0, 1, 0, 1, 0x60001a60007a6006868159b4c2, 0,
  0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0, 0,
  0, 0, 1, 0, 1, 0x140000aa000cd400aacc159b4c2, 0xe0001ba0014f400f54e16ab544,
  0, 0, 0, 1, 0, 1, 0x140001a80015a8010908159b4c3,
  0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0,
  0, 0, 0, 1, 0, 1, 0,
  1, 0x60001a60007a6006868159b4c2, 0x140000cc000cd40132cc159b4c3, 0xe00014e000f2e012f2e15a4d23, 0, 0, 0,
  0, 1, 0x140001a80015a8010908159b4c3, 0, 0, 1, 0,
  1, 0x140001b40015b4014544159b4c5, 0x140001a80015a8010908159b4c3, 0x140000cc000cd40132cc159b4c3, 0xe0001ba0010f000f10e16ab523, 0, 0,
  0, 0, 0, 1, 0, 1, 0x160000aa000cd600aacc179c4c2,
  0xe00016e001b76017bb617a4e28, 0x160001b6001bb0017b70179c9a9, 0, 0, 0, 0, 1,
  0, 1, 0, 1, 0x60001a60007a6006868159b4c2, 0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23]

def jointProgram3 : List ℕ := [
  0x160001b6001bb0017b70179c9a9, 0, 0, 0, 0, 0, 1,
  0, 1, 0, 1, 0x60001a60007a6006868159b4c2, 0, 0,
  1, 0, 1, 0x60000680006c80068c80c31042, 0x140000aa000cd400aacc159b4c2, 0xe0001ba0014f400f54e16ab544, 0x160001b6001bb0017b70179c9a9,
  0, 0, 0, 0, 0, 1, 0,
  1, 0x60001a60007a6006868159b4c2, 0, 0, 1, 0x60001660006a600a6a617acd82, 0,
  0, 1, 0x1a0000440004480088441330c22, 0x60001a60007a6006868159b4c2, 0x140000cc000cd40132cc159b4c3, 0xe00014e000f2e012f2e15a4d23, 0x160001b6001bb0017b70179c9a9,
  0, 0, 0, 0, 0, 0, 1,
  0, 1, 0, 1, 0, 1, 0x60000680006c80068c80c31042,
  0, 0, 1, 0, 1, 0xe000088001ba80088e8149a0c2, 0,
  0, 1, 0xe000088001ba80088e8149a0c2, 0xe0000aa000ab800aaec149a082, 0, 0, 0,
  1, 0xa0000b8000b1000b1181373527, 0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3,
  0xe0001ba0010f000f10e16ab523, 0, 0, 0, 0, 1, 0,
  1, 0x12000088001988008988145a0c6, 0, 0, 1, 0xc0000880012c80088c81331062, 0,
  0, 1, 0x600006c000a6600a66c136b082, 0xc0000880012c80088c81331062, 0, 0, 0,
  1, 0x12000088000ee80088e8145a042, 0, 0, 1, 0x600006e000a6600a66e1373102, 0x12000088000ee80088e8145a042,
  0xe00012e0018d800f2ec149a483, 0, 0, 0, 0, 1, 0x180000880008980110880e6a8c3,
  0xa0000b8000b1000b1181373527, 0, 0, 0, 1, 0x60000c60006c60132cc159b483, 0x80001080008c800c8c80d31442,
  0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0, 0, 0, 0, 0,
  1, 0x140000aa000ab801595815a3508, 0, 0, 1, 0, 1,
  0x60000680006c80068c80c31042, 0x140000aa000cd400aacc159b4c2, 0xe0001ba0014f400f54e16ab544, 0, 0, 0, 0]

def jointProgram4 : List ℕ := [
  1, 0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527, 0, 0, 0, 1,
  0, 1, 0x14000144000cc400c4c40d39822, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0x1400019400133801595816a3528,
  0, 0, 0, 0, 0, 0, 1,
  0x160000aa000ab801797817a4508, 0, 0, 1, 0, 1, 0x60000680006c80068c80c31042,
  0x160000aa000cd600aacc179c4c2, 0xe00016e001b76017bb617a4e28, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 0x180000660006780066880e6a8c2,
  0x140000aa000ab801595815a3508, 0, 0, 0, 1, 0x600006c00166600c66c116b0c2, 0,
  0, 1, 0x400008400048400c4840418822, 0x60000680006c80068c80c31042, 0x140000aa000cd400aacc159b4c2, 0xe0001ba0014f400f54e16ab544, 0x100001180019100171181273529,
  0x1400019400133801595816a3528, 0, 0, 0, 0, 0, 0,
  0, 1, 0, 1, 0, 1, 0x1c0000aa000aac00abdc17a45ea,
  0, 0, 1, 0xc00010c000d0c01dd10128358b, 0, 0, 1,
  0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0, 0, 0, 1, 0x1c0000dc00132c0133dc17a460b,
  0, 0, 1, 0, 1, 0x12000088000ee80088e8145a042, 0x1c0000dc00132c0133dc17a460b,
  0, 0, 0, 1, 0x1c0000aa000ab000abd017a418b, 0xc00010c000d0c01dd10128358b, 0,
  0, 0, 1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0,
  0, 0, 0, 1, 0, 1, 0x140000aa000cd400aacc159b4c2,
  0, 0, 1, 0xe00014e000aaa00aaae15a4d02, 0x1c0000ce001d4e00cf4e1173144, 0, 0,
  0, 1, 0x1c0000aa000ab000abd017a418b, 0xc00010c000d0c01dd10128358b, 0, 0, 0,
  1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0x1c0001d400133201333c17b520b, 0, 0,
  0, 0, 0, 1, 0, 1, 0x160000aa000cd600aacc179c4c2]

def jointProgram5 : List ℕ := [
  0, 0, 1, 0xe00016e000aaa00aaae17a4d02, 0, 0, 1,
  0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2, 0, 0, 0, 1, 0x1c0000aa000ab000abd017a418b,
  0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0, 0, 0, 1,
  0, 1, 0x1c000128001c9c01328817a4105, 0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23, 0, 0,
  0, 0, 1, 0x1c000128001c9c01328817a4105, 0x1c0000aa000ab000abd017a418b, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125,
  0, 0, 0, 0, 0, 1, 0x1c0001d4000aaa00aabc17b51ea,
  0xc0001dc0016d400d74c117b8c4, 0, 0, 0, 1, 0, 1,
  0x60000680006e80068e80c52042, 0xe00014e000aaa00aaae15a4d02, 0x1c0000ce001d4e00cf4e1173144, 0, 0, 0, 0,
  1, 0, 1, 0, 1, 0x1c0000880004440044481048c42, 0x1c0000aa000ab000abd017a418b,
  0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0x1c0001d400133201333c17b520b, 0, 0, 0, 0,
  0, 0, 1, 0, 1, 0x1c0000aa000aac00abdc17a45ea, 0,
  0, 1, 0, 1, 0, 1, 0x60000680006e80068e80c52042,
  0, 0, 1, 0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0, 0,
  0, 1, 0xa0000b8000b1000b1181373527, 0xc00010c000d0c01dd10128358b, 0, 0, 0,
  1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0, 0, 0,
  0, 1, 0, 1, 0x12000088001988008988145a0c6, 0x1c0000dc00132c0133dc17a460b, 0,
  0, 0, 1, 0x12000088000ee80088e8145a042, 0, 0, 1,
  0x600006e000a6600a66e1373102, 0x12000088000ee80088e8145a042, 0x1c0000dc00132c0133dc17a460b, 0, 0, 0, 0,
  1, 0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527, 0xc00010c000d0c01dd10128358b, 0, 0, 0,
  0, 1, 0x60000e600132e006e6e16a3122, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0]

def jointProgram6 : List ℕ := [
  0, 0, 0, 0, 1, 0x140000aa000ab801595815a3508, 0x1c0000d8001d5400d5580f73548,
  0, 0, 0, 1, 0, 1, 0x60000680006e80068e80c52042,
  0xe00014e000aaa00aaae15a4d02, 0x1800015400155800ecec0e6a8c2, 0, 0, 0, 0, 1,
  0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527, 0xc00010c000d0c01dd10128358b, 0, 0, 0, 0,
  1, 0, 1, 0x14000144000ee400e4e40e5a822, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b,
  0x1400019400133801595816a3528, 0, 0, 0, 0, 0, 0,
  1, 0x160000aa000ab801797817a4508, 0, 0, 1, 0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2,
  0, 0, 0, 1, 0, 1, 0x60000680006e80068e80c52042,
  0xe00016e000aaa00aaae17a4d02, 0xc00018e0016d800d6ec117a0c4, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 0x180000660006780066880e6a8c2,
  0x140000aa000ab801595815a3508, 0xc0001dc0016d400d74c117b8c4, 0, 0, 0, 0, 1,
  0x600006e000e6601666e0f73104, 0, 0, 1, 0x400008400048400e4840818822, 0x60000680006e80068e80c52042, 0xe00014e000aaa00aaae15a4d02,
  0x1800015400155800ecec0e6a8c2, 0x100001180019100171181273529, 0x1400019400133801595816a3528, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 0x1c0000aa000aac00abdc17a45ea,
  0, 0, 1, 0, 1, 0xe000088001ba80088e8149a0c2, 0,
  0, 1, 0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0x1c0001b0001bb001d1d017b49ab, 0, 0,
  0, 0, 1, 0, 1, 0x1c000128001c9c01328817a4105, 0x1c0000dc00132c0133dc17a460b,
  0, 0, 0, 1, 0x12000088000ee80088e8145a042, 0, 0,
  1, 0x600006e000a6600a66e1373102, 0x12000088000ee80088e8145a042, 0x1c0000dc00132c0133dc17a460b, 0x1c0001b0001bb001d1d017b49ab, 0x1c0001d4001bb401b5b417b51a8, 0,
  0, 0, 0, 0, 0, 1, 0]

def jointProgram7 : List ℕ := [
  1, 0x1c0001a8001c9c01ba8817a4508, 0, 0, 1, 0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2,
  0xe00016e001b76017bb617a4e28, 0x160001b6001bb0017b70179c9a9, 0, 0, 0, 0, 0,
  1, 0x1c000128001c9c01328817a4105, 0, 0, 1, 0x60001660006a600a6a617acd82, 0x1c000128001c9c01328817a4105,
  0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23, 0x160001b6001bb0017b70179c9a9, 0x1c0001d4001bb401b5b417b51a8, 0, 0, 0,
  0, 0, 0, 0, 1, 0, 1,
  0x1c0001a8001c9c01ba8817a4508, 0, 0, 1, 0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0,
  0, 0, 1, 0xe000088001ba80088e8149a0c2, 0, 0, 1,
  0x600006e000a6600a66e1373102, 0xe000088001ba80088e8149a0c2, 0, 0, 0, 1, 0xc00006600066c01dc66117b58a,
  0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0x1c0001b0001bb001d1d017b49ab, 0, 0, 0, 0,
  0, 1, 0x12000088001988008988145a0c6, 0, 0, 1, 0x60000a6000a78006a66159b9a2,
  0x12000088001988008988145a0c6, 0x1c0000dc00132c0133dc17a460b, 0, 0, 0, 0, 1,
  0x60000e600132e006e6e16a3122, 0x12000088000ee80088e8145a042, 0, 0, 0, 1, 0x40000a40004e400a4e4134a022,
  0x600006e000a6600a66e1373102, 0x12000088000ee80088e8145a042, 0x1c0000dc00132c0133dc17a460b, 0x1c0001b0001bb001d1d017b49ab, 0x1c0001d4001bb401b5b417b51a8, 0, 0,
  0, 0, 0, 0, 0, 1, 0x1c0001a8001c9c01ba8817a4508,
  0x160000aa000ab801797817a4508, 0, 0, 0, 1, 0x600006c00166600c66c116b0c2, 0xc0001dc00088800888c117a0c4,
  0x160000aa000cd600aacc179c4c2, 0xe00016e001b76017bb617a4e28, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0x1c0001d4001bb401b5b417b51a8, 0, 0,
  0, 0, 0, 0, 0, 0, 1,
  0, 1, 0, 1, 0x1e0000aa000abe00aacc17ac5a2, 0, 0,
  1, 0, 1, 0xa0000ac000b0c00ad0c136b0a3, 0, 0, 1,
  0xe0000aa000ab000aaee149b922, 0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0]

def jointProgram8 : List ℕ := [
  0, 0, 1, 0x1e0000cc000cde0132cc17ac5a3, 0x1e0000ee000ef20132ee17ad123, 0, 0,
  0, 1, 0, 1, 0x1e0000aa000abe01328817abd85, 0x1e0000cc000cde0132cc17ac5a3, 0x1e0000ee000ef20132ee17ad123,
  0, 0, 0, 0, 1, 0, 1,
  0x140000aa000cd400aacc159b4c2, 0, 0, 1, 0xe00014e000aaa00aaae15a4d02, 0, 0,
  1, 0x1e00008800088c00cc881169842, 0x140000aa000cd400aacc159b4c2, 0, 0, 0, 1,
  0, 1, 0, 1, 0, 1, 0x40001fe000848004884107b064,
  0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0, 0,
  0, 1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0, 0, 0,
  1, 0, 1, 0x14000144000cc400c4c40d39822, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0,
  0, 0, 0, 1, 0, 1, 0x1e0000aa000abe01328817abd85,
  0x140000cc000cd40132cc159b4c3, 0xe00014e000f2e012f2e15a4d23, 0, 0, 0, 0, 1,
  0, 1, 0, 1, 0x40001fe000848004884107b064, 0, 0,
  1, 0, 1, 0x1e00004a000aa400abfe17ac1ee, 0x1e0000aa000abe01328817abd85, 0x140000cc000cd40132cc159b4c3, 0xe00014e000f2e012f2e15a4d23,
  0, 0, 0, 0, 0, 1, 0,
  1, 0x160000aa000cd600aacc179c4c2, 0, 0, 1, 0xe00016e000aaa00aaae17a4d02, 0,
  0, 1, 0x1e00008800088c00cc881169842, 0x160000aa000cd600aacc179c4c2, 0, 0, 0,
  1, 0x1e0000aa000abe01717017abd85, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0, 0,
  0, 1, 0, 1, 0x1e0000aa000abe01328817abd85, 0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23,
  0, 0, 0, 0, 1, 0x16000128001e9e013288179c185, 0x160000aa000ab0013370179c185,
  0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0, 0, 0, 0]

def jointProgram9 : List ℕ := [
  1, 0x1e0000aa000abe01757417abd84, 0xc0001ec000d4c016d4c0f6b0c4, 0xe0001ee000f4e016f4e0f73144, 0, 0, 0,
  0, 1, 0, 1, 0, 1, 0x40001fe000848004884107b064,
  0x1e0000aa000abe01717017abd85, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0x16000132001f5e013374179c185, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 0x1e0000aa000abe00aacc17ac5a2,
  0, 0, 1, 0x1e0000ee000aaa00aaae17ad102, 0xc0001ec000dec018f8e117b58a, 0, 0,
  0, 1, 0xa0000b8000b1000b1181373527, 0, 0, 1, 0x80001080008c800c8c80d31442,
  0xa0000ac000b0c00ad0c136b0a3, 0, 0, 0, 1, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922,
  0x1800011000111800ecec0e6a4a2, 0x1e000132001f9e01339817b49ab, 0, 0, 0, 0, 0,
  1, 0x140000aa000ab801595815a3508, 0, 0, 1, 0x1e00008800088c00cc881169842, 0x140000aa000cd400aacc159b4c2,
  0, 0, 0, 1, 0x1e000088000ee80088e80f62904, 0xe00014e000aaa00aaae15a4d02, 0x1800015400155800ecec0e6a8c2,
  0, 0, 0, 0, 1, 0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527,
  0, 0, 0, 1, 0, 1, 0x14000144000cc400c4c40d39822,
  0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0, 0, 0, 0, 1,
  0, 1, 0x14000144000ee400e4e40e5a822, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0x1800011000111800ecec0e6a4a2, 0x1400019400133801595816a3528,
  0, 0, 0, 0, 0, 0, 1,
  0x160000aa000ab801797817a4508, 0, 0, 1, 0x1e00008800088c00cc881169842, 0x160000aa000cd600aacc179c4c2, 0,
  0, 0, 1, 0x1e000088000ee80088e80f62904, 0xe00016e000aaa00aaae17a4d02, 0xc00018e0016d800d6ec117a0c4, 0x100001180019100171181273529,
  0x1600013200133801797817a4928, 0x1e0001f80017540175580f73548, 0, 0, 0, 0, 0,
  0, 0, 1, 0, 1, 0x1e0000aa000abe00aacc17ac5a2, 0x1e0000ee001bba01bbbe17ad22f,
  0, 0, 0, 1, 0, 1, 0x1e0001ba001bbe01ba8817ac5a8]

def jointProgram10 : List ℕ := [
  0, 0, 1, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0,
  0, 0, 0, 1, 0, 1, 0x1e0001ba001bbe01ba8817ac5a8,
  0x1e0000cc000cde0132cc17ac5a3, 0x1e0000ee000ef20132ee17ad123, 0, 0, 0, 0, 1,
  0x1e0001ba001bbe01ba8817ac5a8, 0, 0, 1, 0, 1, 0x1e00004a000aa400abfe17ac1ee,
  0x1e0001ba001bbe01ba8817ac5a8, 0x1e0000cc000cde0132cc17ac5a3, 0xe0001ba0010f000f10e16ab523, 0, 0, 0, 0,
  0, 1, 0, 1, 0x1e0001ba001bbe01ba8817ac5a8, 0, 0,
  1, 0x1e00008800088c00cc881169842, 0x140000aa000cd400aacc159b4c2, 0xe0001ba0014f400f54e16ab544, 0, 0, 0,
  0, 1, 0x1e0001ba001bbe01ba8817ac5a8, 0, 0, 1, 0,
  1, 0x1e00004a000aa400abfe17ac1ee, 0x1e0001ba001bbe01ba8817ac5a8, 0, 0, 0, 1,
  0, 1, 0x14000144000cc400c4c40d39822, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0,
  0, 0, 0, 0, 1, 0x1e0001ba001bbe01ba8817ac5a8, 0,
  0, 1, 0, 1, 0x1e00004a000aa400abfe17ac1ee, 0x1e0001ba001bbe01ba8817ac5a8, 0x140000cc000cd40132cc159b4c3,
  0xe00014e000f2e012f2e15a4d23, 0, 0, 0, 0, 0, 1,
  0, 1, 0x140001b40015b4014544159b4c5, 0x1e0001ba001bbe01ba8817ac5a8, 0, 0, 0,
  1, 0x1e00004a000aa400abfe17ac1ee, 0, 0, 1, 0, 1,
  0x600006a000a60006a06159bd82, 0x1e00004a000aa400abfe17ac1ee, 0x1e0001ba001bbe01ba8817ac5a8, 0x140000cc000cd40132cc159b4c3, 0xe0001ba0010f000f10e16ab523, 0, 0,
  0, 0, 0, 0, 1, 0, 1,
  0x1e0001ba001bbe01ba8817ac5a8, 0, 0, 1, 0x1e00008800088c00cc881169842, 0x160000aa000cd600aacc179c4c2, 0xe00016e001b76017bb617a4e28,
  0x160001b6001bb0017b70179c9a9, 0, 0, 0, 0, 0, 1,
  0x1e0001ba001bbe01ba8817ac5a8, 0, 0, 1, 0x60001660006a600a6a617acd82, 0x1e0001ba001bbe01ba8817ac5a8, 0x160000cc000cd60132cc179c4c3]

def jointProgram11 : List ℕ := [
  0xe00016e000f2e012f2e17a4d23, 0x160001b6001bb0017b70179c9a9, 0x1e0001ba001bbe01757417ac5a4, 0, 0, 0, 0,
  0, 0, 0, 1, 0x1e0000aa000abe00ab9817ac5aa, 0, 0,
  1, 0x1e00008800088c00cc881169842, 0x1e0000aa000abe00aacc17ac5a2, 0x1e0000ee001bba01bbbe17ad22f, 0, 0, 0,
  0, 1, 0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527, 0, 0, 0,
  1, 0, 1, 0x40001fe000c4c004cc4128b422, 0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523,
  0x1e000132001f9e01339817b49ab, 0, 0, 0, 0, 0, 0,
  1, 0x1e000088001988008988116a908, 0x140000aa000ab801595815a3508, 0, 0, 0, 1,
  0, 1, 0x14000144000cc400c4c40d39822, 0x1e00008800088c00cc881169842, 0x140000aa000cd400aacc159b4c2, 0xe0001ba0014f400f54e16ab544, 0,
  0, 0, 0, 0, 1, 0, 1,
  0x180001540015580154440e6ace4, 0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527, 0, 0, 0, 0,
  1, 0x14000144000cc400c4c40d39822, 0, 0, 1, 0x200002c00026600266c136b082, 0x14000144000cc400c4c40d39822,
  0x80001080008c800c8c80d31442, 0xa0000ac000b0c00ad0c136b0a3, 0xe0001ba0010f000f10e16ab523, 0x1400019400133801595816a3528, 0, 0, 0,
  0, 0, 0, 0, 1, 0x1e000088001988008988116a908, 0x160000aa000ab801797817a4508,
  0, 0, 0, 1, 0x600006c00166600c66c116b0c2, 0x1e00008800088c00cc881169842, 0x160000aa000cd600aacc179c4c2,
  0xe00016e001b76017bb617a4e28, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0x1e0001f80017540175580f73548, 0, 0, 0,
  0, 0, 0, 0, 0, 1, 0,
  1, 0x1c0000aa000aac00abdc17a45ea, 0, 0, 1, 0x1e0000ee000aaa00aaae17ad102, 0,
  0, 1, 0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0, 0, 0,
  1, 0x1c0000aa000ab000abd017a418b, 0xc00010c000d0c01dd10128358b, 0, 0, 0, 1,
  0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0, 0, 0, 0]

def jointProgram12 : List ℕ := [
  1, 0, 1, 0x1c000128001c9c01328817a4105, 0x1c0000dc00132c0133dc17a460b, 0x1e0000ee000ef20132ee17ad123, 0,
  0, 0, 0, 1, 0x1c000128001c9c01328817a4105, 0x1c0000aa000ab000abd017a418b, 0xc00010c000d0c01dd10128358b,
  0x1e0000ee000ef20132ee17ad123, 0, 0, 0, 0, 0, 1,
  0x1c0001d4000aaa00aabc17b51ea, 0xc0001ec000dec01dd54117b58c, 0, 0, 0, 1, 0x1e000088000ee80088e80f62904,
  0xe00014e000aaa00aaae15a4d02, 0x1c0000ce001d4e00cf4e1173144, 0, 0, 0, 0, 1,
  0, 1, 0, 1, 0x1c0000880004440044481048c42, 0x1c0000aa000ab000abd017a418b, 0xc00010c000d0c01dd10128358b,
  0, 0, 0, 0, 1, 0, 1,
  0x14000144000ee400e4e40e5a822, 0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0x1c0001d400133201333c17b520b, 0, 0,
  0, 0, 0, 0, 1, 0, 1,
  0, 1, 0x60001660006a600a6a617acd82, 0, 0, 1, 0xc0001dc00088800888c117a0c4,
  0x160000aa000cd600aacc179c4c2, 0, 0, 0, 1, 0x1e000088000ee80088e80f62904, 0xe00016e000aaa00aaae17a4d02,
  0, 0, 0, 1, 0x600006c00166600c66c116b0c2, 0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2,
  0, 0, 0, 0, 1, 0, 1,
  0, 1, 0x1c0000880004440044481048c42, 0x1c0000aa000ab000abd017a418b, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0,
  0, 0, 0, 0, 1, 0x1c000128001c9c01328817a4105, 0,
  0, 1, 0x60001660006a600a6a617acd82, 0x1c000128001c9c01328817a4105, 0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23, 0,
  0, 0, 0, 0, 1, 0x600016600133201333617ace05, 0x1c000128001c9c01328817a4105,
  0x1c0000aa000ab000abd017a418b, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0, 0, 0, 0,
  0, 0, 1, 0, 1, 0, 1,
  0x1c0000880004440044481048c42, 0x1c0001d4000aaa00aabc17b51ea, 0xc0001dc0016d400d74c117b8c4, 0xe0001ee000f4e016f4e0f73144, 0, 0, 0]

def jointProgram13 : List ℕ := [
  0, 0, 1, 0, 1, 0x40001dc001c54005d44107b96c, 0,
  0, 1, 0x1c0000880004440044481048c42, 0, 0, 1, 0x6000022000226002268159b042,
  0x1c0000880004440044481048c42, 0x1c0000aa000ab000abd017a418b, 0x100000cc00170c00cd0c126b0e3, 0xe00010e000f0e016f0e1073125, 0x1c0001d400133201333c17b520b, 0, 0,
  0, 0, 0, 0, 0, 1, 0x1e0000aa000abe00ab9817ac5aa,
  0, 0, 1, 0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0, 0,
  0, 1, 0x1e000088000ee80088e80f62904, 0x1e0000ee000aaa00aaae17ad102, 0xc0001ec000dec018f8e117b58a, 0, 0,
  0, 0, 1, 0x180000880008980110880e6a8c3, 0xa0000b8000b1000b1181373527, 0xc00010c000d0c01dd10128358b, 0,
  0, 0, 0, 1, 0, 1, 0x40001fe000e4e004ee4107b12a,
  0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0x1e000132001f9e01339817b49ab, 0, 0, 0,
  0, 0, 0, 1, 0x1e000088001988008988116a908, 0x140000aa000ab801595815a3508, 0x1c0000d8001d5400d5580f73548,
  0, 0, 0, 0, 1, 0, 1,
  0x14000144000ee400e4e40e5a822, 0x1e000088000ee80088e80f62904, 0xe00014e000aaa00aaae15a4d02, 0x1800015400155800ecec0e6a8c2, 0, 0, 0,
  0, 0, 1, 0, 1, 0x180001540015580154440e6ace4, 0x180000880008980110880e6a8c3,
  0xa0000b8000b1000b1181373527, 0xc00010c000d0c01dd10128358b, 0, 0, 0, 0, 0,
  1, 0x14000144000ee400e4e40e5a822, 0, 0, 1, 0x200002e00026600266e1373102, 0x14000144000ee400e4e40e5a822,
  0x80001080008e800e8e80e52442, 0xe0000aa000ab000aaee149b922, 0xc00010c000d0c01dd10128358b, 0x1400019400133801595816a3528, 0, 0, 0,
  0, 0, 0, 0, 1, 0x1e000088001988008988116a908, 0x160000aa000ab801797817a4508,
  0, 0, 0, 1, 0x600006c00166600c66c116b0c2, 0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2,
  0, 0, 0, 0, 1, 0x600006e000e6601666e0f73104, 0x1e000088000ee80088e80f62904,
  0xe00016e000aaa00aaae17a4d02, 0xc00018e0016d800d6ec117a0c4, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0x1e0001f80017540175580f73548, 0, 0]

def jointProgram14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 1,
  0, 1, 0x1c0001a8001c9c01ba8817a4508, 0, 0, 1, 0xc0001dc00088800888c117a0c4,
  0x1c0000aa000aac00abdc17a45ea, 0x1e0000ee001bba01bbbe17ad22f, 0x1c0001b0001bb001d1d017b49ab, 0, 0, 0, 0,
  0, 1, 0x1c000128001c9c01328817a4105, 0, 0, 1, 0x60001c60006a600a6a617ad182,
  0x1c000128001c9c01328817a4105, 0x1c0000dc00132c0133dc17a460b, 0x1e0000ee000ef20132ee17ad123, 0x1c0001b0001bb001d1d017b49ab, 0x1c0001d4001bb401b5b417b51a8, 0, 0,
  0, 0, 0, 0, 0, 1, 0x1c0001a8001c9c01ba8817a4508,
  0, 0, 1, 0x60001660006a600a6a617acd82, 0x1c0001a8001c9c01ba8817a4508, 0, 0,
  0, 1, 0x600006c00166600c66c116b0c2, 0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2, 0xe00016e001b76017bb617a4e28, 0x160001b6001bb0017b70179c9a9,
  0, 0, 0, 0, 0, 0, 1,
  0x600016600133201333617ace05, 0x1c000128001c9c01328817a4105, 0, 0, 0, 1, 0x1600004400045600aa44179c062,
  0x60001660006a600a6a617acd82, 0x1c000128001c9c01328817a4105, 0x160000cc000cd60132cc179c4c3, 0xe00016e000f2e012f2e17a4d23, 0x160001b6001bb0017b70179c9a9, 0x1c0001d4001bb401b5b417b51a8, 0,
  0, 0, 0, 0, 0, 0, 0,
  1, 0x1e000088001988008988116a908, 0x1e0000aa000abe00ab9817ac5aa, 0, 0, 0, 1,
  0xc00006600066c01dc66117b58a, 0xc0001dc00088800888c117a0c4, 0x1c0000aa000aac00abdc17a45ea, 0x1e0000ee001bba01bbbe17ad22f, 0x1c0001b0001bb001d1d017b49ab, 0x1e000132001f9e01339817b49ab, 0x1c0001d4001bb401b5b417b51a8,
  0, 0, 0, 0, 0, 0, 0,
  0, 1, 0x60000780018660166781173508, 0x1e000088001988008988116a908, 0x160000aa000ab801797817a4508, 0, 0,
  0, 0, 1, 0x16000044000cc40044c41239022, 0x600006c00166600c66c116b0c2, 0xc0001dc00088800888c117a0c4, 0x160000aa000cd600aacc179c4c2,
  0xe00016e001b76017bb617a4e28, 0x100001180019100171181273529, 0x1600013200133801797817a4928, 0x1c0001d4001bb401b5b417b51a8]

def jointProgram : List ℕ := jointProgram0 ++ jointProgram1 ++ jointProgram2 ++ jointProgram3 ++ jointProgram4 ++ jointProgram5 ++ jointProgram6 ++ jointProgram7 ++ jointProgram8 ++ jointProgram9 ++ jointProgram10 ++ jointProgram11 ++ jointProgram12 ++ jointProgram13 ++ jointProgram14


set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma starVerified : checkTree 11 starLeaf 11 0 2047 starProgram = some [] := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma jointVerified : checkTree 16 jointLeaf 16 0 65535 jointProgram = some [] := by
  decide +kernel

abbrev fixedDec : DecidableRel fixedGraph.Adj := inferInstance

def indexed (S : Finset (Sym2 (Fin 11))) : Finset (Fin 16) :=
  Finset.univ.filter fun i => edgeSym i ∈ S

lemma indexMem {S : Finset (Sym2 (Fin 11))} {i : Fin 16} :
    i ∈ indexed S ↔ edgeSym i ∈ S := by simp [indexed]

lemma cardIndexed {S : Finset (Sym2 (Fin 11))} (h : S ⊆ fixedGraph.edgeFinset) :
    S.card ≤ (indexed S).card := by
  have he : (indexed S).image edgeSym = S := by
    ext e
    constructor
    · rintro he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      exact indexMem.mp hi
    · intro he
      have hx := h he
      rw [← edgesAll] at hx
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨i,indexMem.mpr (hi ▸ he),hi⟩
  calc
    S.card = ((indexed S).image edgeSym).card := congrArg Finset.card he.symm
    _ ≤ (indexed S).card := Finset.card_image_le

lemma gammaSubset (C : Circuit) (j : ℕ) :
    gammaE fixedGraph C j ⊆ fixedGraph.edgeFinset := Finset.filter_subset _ _

lemma samePair {u v a b : Fin 11} (h : s(u,v) = s(a,b)) :
    pairInput u v = pairInput a b := by
  funext w
  simp only [pairInput, ← Sym2.mem_iff, h]

lemma gammaTrue {C : Circuit} {j : ℕ} {i : Fin 16}
    (h : edgeSym i ∈ gammaE fixedGraph C j) :
    gateVal 11 C j (edgeInput i) = true := by
  obtain ⟨_,u,v,huv,hv⟩ := Finset.mem_filter.mp h
  change gateVal 11 C j (pairInput (ends i).1 (ends i).2) = true
  rw [← samePair huv.symm]
  exact hv

lemma starBound (C : Circuit) (j : ℕ) {a b : Fin 11 → Bool}
    (hs : ∀ x, gateVal 11 C j x = true ↔ fires a b x) :
    {e ∈ gammaE fixedGraph C j | ∃ v ∈ wmax fixedGraph C j, v ∈ e}.card ≤ 7 := by
  let S := {e ∈ gammaE fixedGraph C j | ∃ v ∈ wmax fixedGraph C j, v ∈ e}
  have hS : S ⊆ fixedGraph.edgeFinset := (Finset.filter_subset _ _).trans (gammaSubset C j)
  apply (cardIndexed hS).trans
  let E := indexed S
  obtain ⟨m,hm⟩ := maskCoding (fun v : Fin 11 => decide (v ∈ wmax fixedGraph C j))
  have hgate (e : Fin 16) (he : e ∈ E) : fires a b (edgeInput e) :=
    (hs _).mp (gammaTrue (Finset.mem_filter.mp (indexMem.mp he)).1)
  have htouch (e : Fin 16) (he : e ∈ E) : touches m e = true := by
    obtain ⟨_,v,hv,he⟩ := Finset.mem_filter.mp (indexMem.mp he)
    have hv' : inputMask m v = true := (hm v).trans (decide_eq_true hv)
    have hp : v = (ends e).1 ∨ v = (ends e).2 := Sym2.mem_iff.mp he
    apply Bool.or_eq_true_iff.mpr
    rcases hp with h | h
    · exact Or.inl (by rwa [← h])
    · exact Or.inr (by rwa [← h])
  have hmiss (r : Fin 24) (hr : meetsRow m r = true) :
      ¬ fires a b (inputMask (independentRow r)) := by
    intro hf
    obtain ⟨v,hv,hrv⟩ := meetsRowSpec.mp hr
    have hw := of_decide_eq_true ((hm v).symm.trans hv)
    have hbelow := (Finset.mem_filter.mp hw).2
    exact Bool.false_ne_true ((rowIndependent r).symm.trans
      (hbelow _ ((hs _).mpr hf) hrv))
  exact checkTreeSound (P := fun w =>
    (∀ e ∈ E, touches w e = true) →
    (∀ r, meetsRow w r = true → ¬ fires a b (inputMask (independentRow r))) →
    E.card ≤ 7)
    (fun _ _ _ _ h hl hh ht hn => starLeafSound h hl hh hgate ht hn)
    11 0 2047 starProgram [] m starVerified (maskLe_zero 11 _) (maskLe_full 11 _)
    htouch hmiss

lemma jointBound (C : Circuit) (j k : ℕ) {a b c d : Fin 11 → Bool}
    (hj : ∀ x, gateVal 11 C j x = true ↔ fires a b x)
    (hk : ∀ x, gateVal 11 C k x = true ↔ fires c d x)
    (hjoint : Joint fixedGraph C j k) :
    (gammaE fixedGraph C j ∩ gammaE fixedGraph C k).card ≤ 8 := by
  let S := gammaE fixedGraph C j ∩ gammaE fixedGraph C k
  have hS : S ⊆ fixedGraph.edgeFinset := fun _ he =>
    gammaSubset C j (Finset.mem_inter.mp he).1
  apply (cardIndexed hS).trans
  let E := indexed S
  obtain ⟨m,hm⟩ := maskCoding (fun e : Fin 16 => decide (e ∈ E))
  have hE : edgeFlags m = E := by
    ext e
    simp [edgeFlags,hm e]
  have hgate (e : Fin 16) (he : e ∈ edgeFlags m) :
      fires a b (edgeInput e) ∧ fires c d (edgeInput e) := by
    rw [hE] at he
    obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp (indexMem.mp he)
    exact ⟨(hj _).mp (gammaTrue h₁), (hk _).mp (gammaTrue h₂)⟩
  have hmiss (r : Fin 24) :
      ¬ (fires a b (inputMask (independentRow r)) ∧ fires c d (inputMask (independentRow r))) := by
    rintro ⟨h₁,h₂⟩
    exact Bool.false_ne_true ((rowIndependent r).symm.trans
      (hjoint _ ((hj _).mpr h₁) ((hk _).mpr h₂)))
  change E.card ≤ 8
  rw [← hE]
  exact checkTreeSound (P := fun w =>
    (∀ e ∈ edgeFlags w, fires a b (edgeInput e) ∧ fires c d (edgeInput e)) →
    (edgeFlags w).card ≤ 8)
    (fun _ _ _ _ h hl hh he => jointLeafSound h hl hh he hmiss)
    16 0 65535 jointProgram [] m jointVerified (maskLe_zero 16 _) (maskLe_full 16 _) hgate

end PEqualNP.Outside.L_meta_5966

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_5966


theorem PEqualNP.Outside.L_meta_5966 :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x4 →               (∃ x12 ∈ PEqualNP.TopForm.tops x1 x3, PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x12 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x12) →                 have x13 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x13 : ℕ) => {x14 ∈ PEqualNP.TopForm.gammaE x1 x3 x13 | ∃ x15 ∈ PEqualNP.TopForm.wmax x1 x3 x13, x15 ∈ x14};                 have x14 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x3 x4 ∩ PEqualNP.TopForm.gammaE x1 x3 x5;                 have x15 : Prop := ∀ (x15 : Fin (11 : ℕ) → Bool), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 x15 = Bool.true → PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 x15 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x15 = Bool.true;                 (x13 x4).card ≤ (7 : ℕ) ∧ (x13 x5).card ≤ (7 : ℕ) ∧ (x15 → x14.card ≤ (8 : ℕ)) ∧ (x15 ∨ (PEqualNP.TopForm.wmax x1 x3 x4 ∩ PEqualNP.TopForm.wmax x1 x3 x5).Nonempty) := by
  intro G inst C j k hG hAO hT hpair hjk hkj htop
  dsimp only
  subst G
  have hi : inst = fixedDec := Subsingleton.elim _ _
  subst inst
  change TopForm fixedGraph C at hT
  change junk fixedGraph C = {j,k} at hpair
  have hj : j ∈ junk fixedGraph C := by simp [hpair]
  have hk : k ∈ junk fixedGraph C := by simp [hpair]
  have hpair' : junk fixedGraph C = {k,j} := hpair.trans (Finset.pair_comm j k)
  obtain ⟨a,b,ha⟩ := pureJunk hAO hT hj (noJunkBelow hpair hkj)
  obtain ⟨c,d,hc⟩ := pureJunk hAO hT hk (noJunkBelow hpair' hjk)
  obtain ⟨t,ht,hjt,hkt⟩ := htop
  exact ⟨starBound C j ha, starBound C k hc, jointBound C j k ha hc,
    jointOrCommon hAO hT hpair hjk hkj ht hjt hkt⟩

