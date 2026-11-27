import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6921

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

private def pgD : Finset (Fin 13) := {0, 1, 3, 9}

private def pgPairInput (p l : Fin 13) : List Bool :=
  (List.ofFn fun x : Fin 13 => Decidable.decide (x = p)) ++
    List.ofFn fun x : Fin 13 => Decidable.decide (x = l)

private def pgQuadInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun x : Fin 13 => Decidable.decide (x ∈ Q)) ++
    List.ofFn fun x : Fin 13 => Decidable.decide (∀ q ∈ Q, q - x ∉ pgD)

private abbrev isQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, {q ∈ Q | q - l ∈ pgD}.card ≤ 2

private abbrev missesLine (Q : Finset (Fin 13)) (l : Fin 13) : Prop :=
  ∀ q ∈ Q, q - l ∉ pgD

private def shiftQuad (t : Fin 13) (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Q.image (· + t)

private def baseQuad : Fin 6 → Finset (Fin 13)
  | 0 => {0, 1, 4, 6}
  | 1 => {0, 1, 2, 5}
  | 2 => {0, 1, 2, 6}
  | 3 => {0, 1, 4, 8}
  | 4 => {0, 2, 3, 4}
  | 5 => {0, 3, 5, 6}

private lemma pg_edges_card :
    (Finset.univ.filter fun e : Fin 13 × Fin 13 => e.1 - e.2 ∈ pgD).card = 52 := by
  decide

private lemma pg_no_c4 :
    ∀ p1 p2 l1 l2 : Fin 13, p1 ≠ p2 → l1 ≠ l2 →
      ¬ (p1 - l1 ∈ pgD ∧ p1 - l2 ∈ pgD ∧ p2 - l1 ∈ pgD ∧ p2 - l2 ∈ pgD) := by
  decide

private lemma pg_zero_mem_D : (0 : Fin 13) ∈ pgD := by
  decide

private lemma baseQuad_isQuad : ∀ b : Fin 6, isQuad (baseQuad b) := by
  decide

private lemma baseQuad_mem_zero : ∀ b : Fin 6, (0 : Fin 13) ∈ baseQuad b := by
  decide

private lemma baseQuad_zero_misses_two : missesLine (baseQuad 0) 2 := by
  decide

private lemma baseQuad_pt_diff :
    ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ a ∈ baseQuad b, a + d ∈ baseQuad b := by
  decide

private lemma baseQuad_line_diff :
    ∀ d : Fin 13, d ≠ 0 → ∃ b : Fin 6, ∃ l : Fin 13,
      missesLine (baseQuad b) l ∧ missesLine (baseQuad b) (l + d) := by
  decide

private lemma baseQuad_noninc :
    ∀ d : Fin 13, (0 - d) ∉ pgD → ∃ b : Fin 6, missesLine (baseQuad b) d := by
  decide

private lemma isQuad_shift (t : Fin 13) {Q : Finset (Fin 13)} (hQ : isQuad Q) :
    isQuad (shiftQuad t Q) := by
  refine ⟨?_, ?_⟩
  · unfold shiftQuad
    rw [Finset.card_image_of_injective Q (fun a b h => add_right_cancel h)]
    exact hQ.1
  · intro l
    have hbij : {q ∈ shiftQuad t Q | q - l ∈ pgD} =
        ({q ∈ Q | q - (l - t) ∈ pgD}).image (· + t) := by
      ext x
      simp only [shiftQuad, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hmem⟩
        refine ⟨a, ⟨ha, ?_⟩, rfl⟩
        have heq : a - (l - t) = a + t - l := by abel
        rwa [heq]
      · rintro ⟨a, ⟨ha, hmem⟩, rfl⟩
        refine ⟨⟨a, ha, rfl⟩, ?_⟩
        have heq : a + t - l = a - (l - t) := by abel
        rwa [heq]
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hQ.2 (l - t)

private lemma missesLine_shift (t : Fin 13) {Q : Finset (Fin 13)} {l : Fin 13}
    (hm : missesLine Q l) : missesLine (shiftQuad t Q) (l + t) := by
  intro q hq
  simp only [shiftQuad, Finset.mem_image] at hq
  rcases hq with ⟨a, ha, rfl⟩
  have heq : a + t - (l + t) = a - l := by abel
  rw [heq]
  exact hm a ha

private lemma quad_has_pt (p : Fin 13) : ∃ Q : Finset (Fin 13), isQuad Q ∧ p ∈ Q := by
  refine ⟨shiftQuad p (baseQuad 0), isQuad_shift p (baseQuad_isQuad 0), ?_⟩
  simp only [shiftQuad, Finset.mem_image]
  exact ⟨0, baseQuad_mem_zero 0, zero_add p⟩

private lemma quad_misses_line (l : Fin 13) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ missesLine Q l := by
  refine ⟨shiftQuad (l - 2) (baseQuad 0), isQuad_shift (l - 2) (baseQuad_isQuad 0), ?_⟩
  have h := missesLine_shift (l - 2) baseQuad_zero_misses_two
  have heq : (2 : Fin 13) + (l - 2) = l := by abel
  rwa [heq] at h

private lemma quad_has_two_pts {p1 p2 : Fin 13} (hne : p1 ≠ p2) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ p1 ∈ Q ∧ p2 ∈ Q := by
  have hd : p2 - p1 ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases baseQuad_pt_diff (p2 - p1) hd with ⟨b, a, ha, had⟩
  refine ⟨shiftQuad (p1 - a) (baseQuad b), isQuad_shift (p1 - a) (baseQuad_isQuad b), ?_, ?_⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨a, ha, by abel⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨a + (p2 - p1), had, by abel⟩

private lemma quad_misses_two_lines {l1 l2 : Fin 13} (hne : l1 ≠ l2) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ missesLine Q l1 ∧ missesLine Q l2 := by
  have hd : l2 - l1 ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases baseQuad_line_diff (l2 - l1) hd with ⟨b, l, hm1, hm2⟩
  refine ⟨shiftQuad (l1 - l) (baseQuad b), isQuad_shift (l1 - l) (baseQuad_isQuad b), ?_, ?_⟩
  · have h := missesLine_shift (l1 - l) hm1
    have heq : l + (l1 - l) = l1 := by abel
    rwa [heq] at h
  · have h := missesLine_shift (l1 - l) hm2
    have heq : l + (l2 - l1) + (l1 - l) = l2 := by abel
    rwa [heq] at h

private lemma quad_noninc {p l : Fin 13} (hni : p - l ∉ pgD) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ p ∈ Q ∧ missesLine Q l := by
  have hni' : (0 : Fin 13) - (l - p) ∉ pgD := by
    have heq : (0 : Fin 13) - (l - p) = p - l := by abel
    rwa [heq]
  rcases baseQuad_noninc (l - p) hni' with ⟨b, hm⟩
  refine ⟨shiftQuad p (baseQuad b), isQuad_shift p (baseQuad_isQuad b), ?_, ?_⟩
  · simp only [shiftQuad, Finset.mem_image]
    exact ⟨0, baseQuad_mem_zero b, zero_add p⟩
  · have h := missesLine_shift p hm
    have heq : l - p + p = l := by abel
    rwa [heq] at h

private lemma pgPairInput_length (p l : Fin 13) : (pgPairInput p l).length = 26 := by
  unfold pgPairInput
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

private lemma pgQuadInput_length (Q : Finset (Fin 13)) : (pgQuadInput Q).length = 26 := by
  unfold pgQuadInput
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

private lemma pgPairInput_getD_pt (p l x : Fin 13) :
    (pgPairInput p l).getD x.val false = Decidable.decide (x = p) := by
  unfold pgPairInput
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hx, List.getElem?_eq_getElem hx,
    Option.getD_some, List.getElem_ofFn]

private lemma pgPairInput_getD_ln (p l x : Fin 13) :
    (pgPairInput p l).getD (13 + x.val) false = Decidable.decide (x = l) := by
  unfold pgPairInput
  have h1 : (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length = 13 :=
    List.length_ofFn
  have hge : (List.ofFn fun y : Fin 13 => Decidable.decide (y = p)).length ≤ 13 + x.val := by
    omega
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y = l)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, h1, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hx, Option.getD_some, List.getElem_ofFn]

private lemma pgQuadInput_getD_pt (Q : Finset (Fin 13)) (x : Fin 13) :
    (pgQuadInput Q).getD x.val false = Decidable.decide (x ∈ Q) := by
  unfold pgQuadInput
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hx, List.getElem?_eq_getElem hx,
    Option.getD_some, List.getElem_ofFn]

private lemma pgQuadInput_getD_ln (Q : Finset (Fin 13)) (x : Fin 13) :
    (pgQuadInput Q).getD (13 + x.val) false = Decidable.decide (∀ q ∈ Q, q - x ∉ pgD) := by
  unfold pgQuadInput
  have h1 : (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length = 13 :=
    List.length_ofFn
  have hge : (List.ofFn fun y : Fin 13 => Decidable.decide (y ∈ Q)).length ≤ 13 + x.val := by
    omega
  have hx : x.val < (List.ofFn fun y : Fin 13 => Decidable.decide (∀ q ∈ Q, q - y ∉ pgD)).length := by
    rw [List.length_ofFn]; exact x.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, h1, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem hx, Option.getD_some, List.getElem_ofFn]

private def toPt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p

private def toLn (l : Fin 13) : Fin 26 := Fin.natAdd 13 l

private def adj26 (u v : Fin 26) : Prop :=
  ∃ p l : Fin 13, p - l ∈ pgD ∧ ((u = toPt p ∧ v = toLn l) ∨ (u = toLn l ∧ v = toPt p))

private lemma toPt_val (p : Fin 13) : (toPt p).val = p.val := rfl

private lemma toLn_val (l : Fin 13) : (toLn l).val = 13 + l.val := by
  simp [toLn]
  omega

private lemma toPt_ne_toLn (p l : Fin 13) : toPt p ≠ toLn l := by
  intro h
  have hv := congrArg Fin.val h
  rw [toPt_val, toLn_val] at hv
  omega

private lemma toPt_inj {p1 p2 : Fin 13} (h : toPt p1 = toPt p2) : p1 = p2 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [toPt_val] using hv

private lemma toLn_inj {l1 l2 : Fin 13} (h : toLn l1 = toLn l2) : l1 = l2 := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [toLn_val, toLn_val] at hv
  omega

private lemma adj26_no_c4 {c1 c2 u1 u2 : Fin 26} (hc : c1 ≠ c2) (hu : u1 ≠ u2)
    (h11 : adj26 c1 u1) (h12 : adj26 c1 u2) (h21 : adj26 c2 u1) (h22 : adj26 c2 u2) : False := by
  rcases h11 with ⟨p11, l11, hd11, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · rcases h12 with ⟨p12, l12, hd12, ⟨hp1, rfl⟩ | ⟨hbad, _⟩⟩
    · have hp : p11 = p12 := toPt_inj hp1
      subst hp
      rcases h21 with ⟨p21, l21, hd21, ⟨rfl, hl1⟩ | ⟨_, hbad⟩⟩
      · have hl : l11 = l21 := toLn_inj hl1
        subst hl
        rcases h22 with ⟨p22, l22, hd22, ⟨hp2, hl2⟩ | ⟨hbad, _⟩⟩
        · have hp' : p21 = p22 := toPt_inj hp2
          have hl' : l12 = l22 := toLn_inj hl2
          subst hp'; subst hl'
          exact pg_no_c4 p11 p21 l11 l12 (fun h => hc (congrArg toPt h))
            (fun h => hu (congrArg toLn h)) ⟨hd11, hd12, hd21, hd22⟩
        · exact toPt_ne_toLn p21 l22 hbad
      · exact toPt_ne_toLn p21 l11 hbad.symm
    · exact toPt_ne_toLn p11 l12 hbad
  · rcases h12 with ⟨p12, l12, hd12, ⟨hbad, _⟩ | ⟨hl1, rfl⟩⟩
    · exact toPt_ne_toLn p12 l11 hbad.symm
    · have hl : l11 = l12 := toLn_inj hl1
      subst hl
      rcases h21 with ⟨p21, l21, hd21, ⟨_, hbad⟩ | ⟨rfl, hp1⟩⟩
      · exact toPt_ne_toLn p11 l21 hbad
      · have hp : p11 = p21 := toPt_inj hp1
        subst hp
        rcases h22 with ⟨p22, l22, hd22, ⟨hbad, _⟩ | ⟨hl2, hp2⟩⟩
        · exact toPt_ne_toLn p22 l21 hbad.symm
        · have hl' : l21 = l22 := toLn_inj hl2
          have hp' : p12 = p22 := toPt_inj hp2
          subst hl'; subst hp'
          exact pg_no_c4 p11 p12 l11 l21 (fun h => hu (congrArg toPt h))
            (fun h => hc (congrArg toLn h)) ⟨hd11, hd21, hd12, hd22⟩

private def mkEdge (c u : Fin 26) : Fin 13 × Fin 13 :=
  if h : c.val < 13 then
    (⟨c.val, h⟩, ⟨u.val % 13, Nat.mod_lt _ (by decide)⟩)
  else
    (⟨u.val % 13, Nat.mod_lt _ (by decide)⟩, ⟨c.val % 13, Nat.mod_lt _ (by decide)⟩)

private lemma mkEdge_pt_ln (p l : Fin 13) : mkEdge (toPt p) (toLn l) = (p, l) := by
  unfold mkEdge
  have hp : (toPt p).val < 13 := p.isLt
  simp only [hp, ↓reduceDIte]
  apply Prod.ext
  · exact Fin.ext rfl
  · apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt l.isLt

private lemma mkEdge_ln_pt (l p : Fin 13) : mkEdge (toLn l) (toPt p) = (p, l) := by
  unfold mkEdge
  have hl : ¬ (toLn l).val < 13 := by rw [toLn_val]; omega
  simp only [hl, ↓reduceDIte]
  apply Prod.ext
  · apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  · apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt l.isLt

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

private lemma lt_gates_of_and {C : Circuit} {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    j < C.gates.length := by
  by_contra hge
  push Not at hge
  have hdef : gateAt C j = ⟨GateOp.or, []⟩ := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl
  rw [hdef] at hop
  cases hop

private lemma gateOp_and_or {C : Circuit} (hMono : Monotone2 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  have h := (hMono (gateAt C j) (gateAt_mem hj)).1
  simpa using h

private lemma gate_inputs_len_le {C : Circuit} (hMono : Monotone2 C) {j : ℕ}
    (hj : j < C.gates.length) :
    (gateAt C j).inputs.length ≤ 2 :=
  (hMono (gateAt C j) (gateAt_mem hj)).2

private lemma wires_getD_input (C : Circuit) (inp : List Bool) {w : ℕ} (hw : w < inp.length) :
    (C.wires inp).getD w false = inp.getD w false := by
  unfold Circuit.wires
  exact foldl_append_getD_lt _ C.gates inp false w hw

private lemma wires_getD_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    (inp : List Bool) (hlen : inp.length = n) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires inp).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => (C.wires inp).getD w false) := by
  unfold Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates inp false j hj ⟨GateOp.or, []⟩
  rw [hlen] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          inp).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          inp).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < inp.length + j := by
    rw [hlen]
    exact hRB j hj i hi
  exact foldl_append_take_getD _ C.gates inp false j i (Nat.le_of_lt hj) hilt

private lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

private lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

private lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

private lemma orReaches_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ u ∈ (gateAt C j).inputs, OrReaches n C u g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        exact ⟨hop, u, hu.1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, u, hu, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨u, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hu, hnu, hRB j hj u hu⟩

private lemma orReaches_self {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hRB (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

private lemma orReaches_le {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, u, hu, hug⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : u < n + j := hRB j hj u hu
      have hrec := ih _ hlt g hug
      exact ⟨by omega, hrec.2⟩

private lemma orReaches_trans {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact hgh
    · have hrec := ih _ (hRB j hj u hu) g h hug hgh
      exact (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hrec⟩⟩

private lemma orReaches_parent {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          n + g ∈ (gateAt C h).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hRB] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, u, hu, hug⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (hRB j hj u hu) g hug with rfl | ⟨h, hh, hhop, hreach, hmem⟩
      · exact ⟨j, hj, hop, orReaches_self hRB hj, hu⟩
      · exact ⟨h, hh, hhop,
          (orReaches_iff hRB (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, u, hu, hreach⟩⟩, hmem⟩

private lemma cones_length (n : ℕ) (C : Circuit) :
    (cones n C).length = C.gates.length := by
  unfold cones coneStep
  rw [foldl_append_length]
  simp

private lemma cones_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (cones n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [cones_length]; exact hj

private lemma cones_getD_lt (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones coneStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change (((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
      (fun w => (w - n) :: pre.getD (w - n) [])) = _
  rw [hprelen]
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma inCone_iff {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (i j : ℕ) :
    InCone n C i j ↔
      j < C.gates.length ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  constructor
  · intro hmem
    have hj : j < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [cones_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨hj, ?_⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap] at hmem
    rcases hmem with ⟨w, hw, hiw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    rw [List.mem_cons] at hiw
    exact ⟨w, hw.1, hw.2.1, hiw⟩
  · rintro ⟨hj, w, hw, hnw, hiw⟩
    rw [cones_getD_lt n C hj, List.mem_flatMap]
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hw, hnw, hRB j hj w hw⟩
    · rw [List.mem_cons]
      exact hiw

private lemma inCone_lt {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ j i : ℕ, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    rw [inCone_iff hRB] at hij
    rcases hij with ⟨hj, w, hw, hnw, rfl | hrec⟩
    · have hwlt := hRB j hj w hw
      exact ⟨by omega, hj⟩
    · have hwlt := hRB j hj w hw
      have hsub := ih (w - n) (by omega) i hrec
      exact ⟨by omega, hj⟩

private lemma inCone_trans {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ c a b : ℕ, InCone n C a b → InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    intro a b hab hbc
    rw [inCone_iff hRB] at hbc
    rcases hbc with ⟨hc, w, hw, hnw, rfl | hrec⟩
    · exact (inCone_iff hRB a c).mpr ⟨hc, w, hw, hnw, Or.inr hab⟩
    · have hwlt := hRB c hc w hw
      have hsub := ih (w - n) (by omega) a b hab hrec
      exact (inCone_iff hRB a c).mpr ⟨hc, w, hw, hnw, Or.inr hsub⟩

private lemma inCone_of_orReaches_ne {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) :
    ∀ j i : ℕ, OrReaches n C (n + j) i → i ≠ j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hji hne
    rw [orReaches_iff hRB] at hji
    rcases hji with ⟨j', hj', heq, rfl | ⟨_, u, hu, hui⟩⟩
    · exact absurd (by omega) hne
    · rcases (by omega : j = j') with rfl
      have hnu : n ≤ u := hui.1
      have hult : u < n + j := hRB j hj' u hu
      by_cases hiu : i = u - n
      · exact (inCone_iff hRB i j).mpr ⟨hj', u, hu, hnu, Or.inl hiu⟩
      · have hui' : OrReaches n C (n + (u - n)) i := by
          have : n + (u - n) = u := by omega
          rwa [this]
        have hsub := ih (u - n) (by omega) i hui' hiu
        exact (inCone_iff hRB i j).mpr ⟨hj', u, hu, hnu, Or.inr hsub⟩

private lemma inCone_of_input_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {j w i : ℕ} (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hwi : OrReaches n C w i) :
    InCone n C i j := by
  have hnw : n ≤ w := hwi.1
  by_cases hiw : i = w - n
  · exact (inCone_iff hRB i j).mpr ⟨hj, w, hw, hnw, Or.inl hiw⟩
  · have hwi' : OrReaches n C (n + (w - n)) i := by
      have : n + (w - n) = w := by omega
      rwa [this]
    exact (inCone_iff hRB i j).mpr ⟨hj, w, hw, hnw, Or.inr (inCone_of_orReaches_ne hRB (w - n) i hwi' hiw)⟩

private lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

private lemma orIn_ge {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hRB] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

private lemma orIn_and {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hRB] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

private lemma mem_orIn_or {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (u : Fin n) :
    u ∈ orIn n C (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, u ∈ orIn n C w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hRB] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, w, hw, hwk⟩
      · exact ⟨u.val, huk, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr ⟨k, hk, hwk, hkop, huk⟩⟩
  · rintro ⟨w, hw, hEq | ⟨k, hk, hwk, hkop, huk⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hRB hj, hop, ?_⟩
      rwa [hEq]
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hRB (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, w, hw, hwk⟩⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hRB w g k hwg hgk, hkop, huk⟩

private lemma wires_iff_orIn_inCone {n : ℕ} {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack n C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone n C i j)
    {g : ℕ} (hgop : (gateAt C g).op = GateOp.and)
    (inp : List Bool) (hlen : inp.length = n) :
    ∀ w : ℕ, (w < n ∨ (n ≤ w ∧ InCone n C (w - n) g)) →
      ((C.wires inp).getD w false = true ↔ ∃ i ∈ orIn n C w, inp.getD i.val false = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hw with hlt | ⟨hnw, hcone⟩
    · rw [wires_getD_input C inp (hlen.symm ▸ hlt)]
      have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq]
      simp
    · set k := w - n
      have hwk : w = n + k := by omega
      have hkt := inCone_lt hRB g k hcone
      have hk : k < C.gates.length := by omega
      have hkop : (gateAt C k).op = GateOp.or := by
        rcases gateOp_and_or hMono hk with hand | hor
        · exfalso
          exact hNoAnd ⟨k, g, hand, hgop, hcone⟩
        · exact hor
      rw [hwk, wires_getD_gate hRB inp hlen hk, hkop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
      constructor
      · rintro ⟨u, hu, hut⟩
        have hult : u < w := by
          have := hRB k hk u hu
          omega
        have hucond : u < n ∨ (n ≤ u ∧ InCone n C (u - n) g) := by
          by_cases h1 : u < n
          · exact Or.inl h1
          · right
            refine ⟨by omega, ?_⟩
            have hku : InCone n C (u - n) k :=
              (inCone_iff hRB (u - n) k).mpr ⟨hk, u, hu, by omega, Or.inl rfl⟩
            exact inCone_trans hRB g (u - n) k hku hcone
        rcases (ih u hult hucond).mp hut with ⟨i, hi, hit⟩
        exact ⟨i, (mem_orIn_or hRB hk hkop i).mpr ⟨u, hu, hi⟩, hit⟩
      · rintro ⟨i, hi, hit⟩
        rcases (mem_orIn_or hRB hk hkop i).mp hi with ⟨u, hu, hui⟩
        have hult : u < w := by
          have := hRB k hk u hu
          omega
        have hucond : u < n ∨ (n ≤ u ∧ InCone n C (u - n) g) := by
          by_cases h1 : u < n
          · exact Or.inl h1
          · right
            refine ⟨by omega, ?_⟩
            have hku : InCone n C (u - n) k :=
              (inCone_iff hRB (u - n) k).mpr ⟨hk, u, hu, by omega, Or.inl rfl⟩
            exact inCone_trans hRB g (u - n) k hku hcone
        exact ⟨u, hu, (ih u hult hucond).mpr ⟨i, hui, hit⟩⟩

private lemma and_gate_eval_iff {n : ℕ} {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack n C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone n C i j)
    {g : ℕ} (hgop : (gateAt C g).op = GateOp.and)
    (inp : List Bool) (hlen : inp.length = n) :
    (C.wires inp).getD (n + g) false = true ↔
      ∀ w ∈ (gateAt C g).inputs, ∃ i ∈ orIn n C w, inp.getD i.val false = true := by
  have hg : g < C.gates.length := lt_gates_of_and hgop
  rw [wires_getD_gate hRB inp hlen hg, hgop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h w hw
    have hwcond : w < n ∨ (n ≤ w ∧ InCone n C (w - n) g) := by
      by_cases h1 : w < n
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, (inCone_iff hRB (w - n) g).mpr ⟨hg, w, hw, by omega, Or.inl rfl⟩⟩
    exact (wires_iff_orIn_inCone hMono hRB hNoAnd hgop inp hlen w hwcond).mp (h w hw)
  · intro h w hw
    have hwcond : w < n ∨ (n ≤ w ∧ InCone n C (w - n) g) := by
      by_cases h1 : w < n
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, (inCone_iff hRB (w - n) g).mpr ⟨hg, w, hw, by omega, Or.inl rfl⟩⟩
    exact (wires_iff_orIn_inCone hMono hRB hNoAnd hgop inp hlen w hwcond).mpr (h w hw)

open Classical in
private noncomputable def bigOrReach (n : ℕ) (C : Circuit) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (orIn n C (n + g)).card ∧ ∃ w ∈ W, OrReaches n C w g

private lemma leaf_count_bound {n : ℕ} {C : Circuit} (hMono : Monotone2 C) (hRB : ReadsBack n C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReach n C W).card = k →
      (W.biUnion (orIn n C)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReach n C W).Nonempty
    · set M := bigOrReach n C W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (orIn n C (n + m)).card ∧ ∃ w ∈ W, OrReaches n C w m := by
        simpa [M, bigOrReach, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches n C w m → w = n + m := by
        intro w hw hwm
        have hle := orReaches_le hRB w m hwm
        rw [orReaches_iff hRB] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, u, hu, hug⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, n + j, hw, orReaches_self hRB hj⟩
            have hsub : orIn n C (n + m) ⊆ orIn n C (n + j) :=
              orIn_subset_of_orReaches hRB
                ((orReaches_iff hRB (n + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, u, hu, hug⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : n + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := (gateAt C m).inputs.toFinset ∪ (W.erase (n + m))
      have hbi : W.biUnion (orIn n C) ⊆ W'.biUnion (orIn n C) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = n + m
        · subst hwm
          rcases (mem_orIn_or hRB hm_props.1 hm_props.2.1 u).mp huw with ⟨v, hv, huv⟩
          exact ⟨v, Finset.mem_union_left _ (List.mem_toFinset.mpr hv), huv⟩
        · exact ⟨w, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hwm, hw⟩), huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (gateAt C m).inputs.toFinset.card + (W.erase (n + m)).card :=
          Finset.card_union_le _ _
        have h2 : (gateAt C m).inputs.toFinset.card ≤ (gateAt C m).inputs.length :=
          List.toFinset_card_le _
        have h3 : (gateAt C m).inputs.length ≤ 2 := gate_inputs_len_le hMono hm_props.1
        have h4 : (W.erase (n + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReach n C W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          rw [Finset.mem_union] at hw'
          rcases hw' with hmem | herase
          · rw [List.mem_toFinset] at hmem
            exact ⟨n + m, hnmW,
              (orReaches_iff hRB (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, w', hmem, hw'g⟩⟩⟩
          · exact ⟨w', (Finset.mem_erase.mp herase).2, hw'g⟩
        refine ⟨?_, hgM⟩
        intro hgm
        subst hgm
        rw [Finset.mem_union] at hw'
        rcases hw' with hmem | herase
        · rw [List.mem_toFinset] at hmem
          have hle := (orReaches_le hRB _ _ hw'g).1
          have hlt := hRB m hm_props.1 w' hmem
          omega
        · rcases Finset.mem_erase.mp herase with ⟨hne', hw'W⟩
          exact hne' (hmax_unique w' hw'W hw'g)
      have hM'card_le : (bigOrReach n C W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReach n C W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (orIn n C)).card ≤ (W'.biUnion (orIn n C)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (orIn n C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (orIn n C w).card := hgt
        by_cases hlt : w < n
        · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
          rw [heq, Finset.card_singleton] at hge2
          omega
        · by_cases hge : n + C.gates.length ≤ w
          · rw [orIn_ge hRB hge, Finset.card_empty] at hge2
            omega
          · set j := w - n
            have hwEq : w = n + j := by omega
            have hj : j < C.gates.length := by omega
            rw [hwEq] at hge2 hw
            rcases gateOp_and_or hMono hj with hop | hop
            · rw [orIn_and hRB hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReach n C W := by
                simp only [bigOrReach, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, n + j, hw, orReaches_self hRB hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (orIn n C)).card ≤ ∑ w ∈ W, (orIn n C w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (orIn n C w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega

private lemma clean_and_structure {C : Circuit}
    (hMono : Monotone2 C) (hRB : ReadsBack 26 C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j)
    {g : ℕ} (hgop : (gateAt C g).op = GateOp.and)
    (hquad : ∀ Q : Finset (Fin 13), isQuad Q → (C.wires (pgQuadInput Q)).getD (26 + g) false = false)
    (hpos : ∃ p l : Fin 13, p - l ∈ pgD ∧ (C.wires (pgPairInput p l)).getD (26 + g) false = true) :
    ∃ (c : Fin 26) (w : ℕ), w ∈ (gateAt C g).inputs ∧
      (∀ u ∈ orIn 26 C w, adj26 c u) ∧
      (∀ p l : Fin 13, (C.wires (pgPairInput p l)).getD (26 + g) false = true →
        (c = toPt p ∧ toLn l ∈ orIn 26 C w) ∨ (c = toLn l ∧ toPt p ∈ orIn 26 C w)) := by
  have hg : g < C.gates.length := lt_gates_of_and hgop
  have hlen : (gateAt C g).inputs.length ≤ 2 := gate_inputs_len_le hMono hg
  have eval_quad_false : ∀ Q : Finset (Fin 13), isQuad Q →
      ¬ ∀ w ∈ (gateAt C g).inputs, ∃ i ∈ orIn 26 C w, (pgQuadInput Q).getD i.val false = true := by
    intro Q hQ hall
    have ht := (and_gate_eval_iff hMono hRB hNoAnd hgop (pgQuadInput Q) (pgQuadInput_length Q)).mpr hall
    have hf := hquad Q hQ
    rw [ht] at hf
    cases hf
  have hquad_on : ∀ i : Fin 26, ∃ Q : Finset (Fin 13), isQuad Q ∧ (pgQuadInput Q).getD i.val false = true := by
    intro i
    by_cases hi : i.val < 13
    · rcases quad_has_pt ⟨i.val, hi⟩ with ⟨Q, hQ, hp⟩
      refine ⟨Q, hQ, ?_⟩
      have hget := pgQuadInput_getD_pt Q ⟨i.val, hi⟩
      simpa [hp] using hget
    · have hl : i.val - 13 < 13 := by omega
      rcases quad_misses_line ⟨i.val - 13, hl⟩ with ⟨Q, hQ, hm⟩
      refine ⟨Q, hQ, ?_⟩
      have hget := pgQuadInput_getD_ln Q ⟨i.val - 13, hl⟩
      have heq : 13 + (i.val - 13) = i.val := by omega
      rw [heq] at hget
      rw [hget]
      exact decide_eq_true hm
  rcases h : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · exfalso
    apply eval_quad_false (baseQuad 0) (baseQuad_isQuad 0)
    intro w hw
    rw [h] at hw
    cases hw
  · exfalso
    rcases hpos with ⟨p0, l0, _, hpt⟩
    have ha := (and_gate_eval_iff hMono hRB hNoAnd hgop (pgPairInput p0 l0) (pgPairInput_length p0 l0)).mp hpt
    rw [h] at ha
    rcases ha a (List.mem_singleton_self a) with ⟨i, hi, _⟩
    rcases hquad_on i with ⟨Q, hQ, hQi⟩
    apply eval_quad_false Q hQ
    intro w hw
    rw [h, List.mem_singleton] at hw
    subst hw
    exact ⟨i, hi, hQi⟩
  · have hpair_ab : ∀ p l : Fin 13, (C.wires (pgPairInput p l)).getD (26 + g) false = true ↔
        (∃ i ∈ orIn 26 C a, (pgPairInput p l).getD i.val false = true) ∧
        (∃ j ∈ orIn 26 C b, (pgPairInput p l).getD j.val false = true) := by
      intro p l
      rw [and_gate_eval_iff hMono hRB hNoAnd hgop (pgPairInput p l) (pgPairInput_length p l), h]
      simp
    have hquad_ab : ∀ Q : Finset (Fin 13), isQuad Q →
        ¬ ((∃ i ∈ orIn 26 C a, (pgQuadInput Q).getD i.val false = true) ∧
           (∃ j ∈ orIn 26 C b, (pgQuadInput Q).getD j.val false = true)) := by
      intro Q hQ ⟨hi, hj⟩
      apply eval_quad_false Q hQ
      intro w hw
      rw [h] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hi
      · exact hj
    have hne : (orIn 26 C a).Nonempty ∧ (orIn 26 C b).Nonempty := by
      rcases hpos with ⟨p0, l0, _, hpt⟩
      rcases (hpair_ab p0 l0).mp hpt with ⟨⟨i, hi, _⟩, ⟨j, hj, _⟩⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hno_two_pts : ∀ p1 p2 : Fin 13, toPt p1 ∈ orIn 26 C a → toPt p2 ∈ orIn 26 C b → False := by
      intro p1 p2 hp1 hp2
      by_cases heq : p1 = p2
      · subst heq
        rcases quad_has_pt p1 with ⟨Q, hQ, hmem⟩
        apply hquad_ab Q hQ
        have hv : (pgQuadInput Q).getD (toPt p1).val false = true := by
          rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem
        exact ⟨⟨toPt p1, hp1, hv⟩, ⟨toPt p1, hp2, hv⟩⟩
      · rcases quad_has_two_pts heq with ⟨Q, hQ, hmem1, hmem2⟩
        apply hquad_ab Q hQ
        have hv1 : (pgQuadInput Q).getD (toPt p1).val false = true := by
          rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem1
        have hv2 : (pgQuadInput Q).getD (toPt p2).val false = true := by
          rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem2
        exact ⟨⟨toPt p1, hp1, hv1⟩, ⟨toPt p2, hp2, hv2⟩⟩
    have hno_two_lns : ∀ l1 l2 : Fin 13, toLn l1 ∈ orIn 26 C a → toLn l2 ∈ orIn 26 C b → False := by
      intro l1 l2 hl1 hl2
      by_cases heq : l1 = l2
      · subst heq
        rcases quad_misses_line l1 with ⟨Q, hQ, hm⟩
        apply hquad_ab Q hQ
        have hv : (pgQuadInput Q).getD (toLn l1).val false = true := by
          rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm
        exact ⟨⟨toLn l1, hl1, hv⟩, ⟨toLn l1, hl2, hv⟩⟩
      · rcases quad_misses_two_lines heq with ⟨Q, hQ, hm1, hm2⟩
        apply hquad_ab Q hQ
        have hv1 : (pgQuadInput Q).getD (toLn l1).val false = true := by
          rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm1
        have hv2 : (pgQuadInput Q).getD (toLn l2).val false = true := by
          rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm2
        exact ⟨⟨toLn l1, hl1, hv1⟩, ⟨toLn l2, hl2, hv2⟩⟩
    have hcross_adj : ∀ i ∈ orIn 26 C a, ∀ j ∈ orIn 26 C b, adj26 i j := by
      intro i hi j hj
      by_cases h1 : i.val < 13
      · have hiEq : i = toPt ⟨i.val, h1⟩ := Fin.ext rfl
        rw [hiEq] at hi ⊢
        by_cases h2 : j.val < 13
        · have hjEq : j = toPt ⟨j.val, h2⟩ := Fin.ext rfl
          rw [hjEq] at hj
          exact False.elim (hno_two_pts _ _ hi hj)
        · have hjEq : j = toLn ⟨j.val - 13, by omega⟩ := by
            apply Fin.ext; rw [toLn_val]; dsimp; omega
          rw [hjEq] at hj ⊢
          have hinc : ⟨i.val, h1⟩ - ⟨j.val - 13, by omega⟩ ∈ pgD := by
            by_contra hni
            rcases quad_noninc hni with ⟨Q, hQ, hmem, hm⟩
            apply hquad_ab Q hQ
            have hv1 : (pgQuadInput Q).getD (toPt ⟨i.val, h1⟩).val false = true := by
              rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem
            have hv2 : (pgQuadInput Q).getD (toLn ⟨j.val - 13, by omega⟩).val false = true := by
              rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm
            exact ⟨⟨toPt ⟨i.val, h1⟩, hi, hv1⟩, ⟨toLn ⟨j.val - 13, by omega⟩, hj, hv2⟩⟩
          exact ⟨⟨i.val, h1⟩, ⟨j.val - 13, by omega⟩, hinc, Or.inl ⟨rfl, rfl⟩⟩
      · have hiEq : i = toLn ⟨i.val - 13, by omega⟩ := by
          apply Fin.ext; rw [toLn_val]; dsimp; omega
        rw [hiEq] at hi ⊢
        by_cases h2 : j.val < 13
        · have hjEq : j = toPt ⟨j.val, h2⟩ := Fin.ext rfl
          rw [hjEq] at hj ⊢
          have hinc : ⟨j.val, h2⟩ - ⟨i.val - 13, by omega⟩ ∈ pgD := by
            by_contra hni
            rcases quad_noninc hni with ⟨Q, hQ, hmem, hm⟩
            apply hquad_ab Q hQ
            have hv1 : (pgQuadInput Q).getD (toLn ⟨i.val - 13, by omega⟩).val false = true := by
              rw [toLn_val, pgQuadInput_getD_ln]; exact decide_eq_true hm
            have hv2 : (pgQuadInput Q).getD (toPt ⟨j.val, h2⟩).val false = true := by
              rw [toPt_val, pgQuadInput_getD_pt]; exact decide_eq_true hmem
            exact ⟨⟨toLn ⟨i.val - 13, by omega⟩, hi, hv1⟩, ⟨toPt ⟨j.val, h2⟩, hj, hv2⟩⟩
          exact ⟨⟨j.val, h2⟩, ⟨i.val - 13, by omega⟩, hinc, Or.inr ⟨rfl, rfl⟩⟩
        · have hjEq : j = toLn ⟨j.val - 13, by omega⟩ := by
            apply Fin.ext; rw [toLn_val]; dsimp; omega
          rw [hjEq] at hj
          exact False.elim (hno_two_lns _ _ hi hj)
    have hcard_one : (orIn 26 C a).card = 1 ∨ (orIn 26 C b).card = 1 := by
      by_contra hboth
      push Not at hboth
      have h1a : 1 < (orIn 26 C a).card := by
        have hposa := Finset.card_pos.mpr hne.1
        omega
      have h1b : 1 < (orIn 26 C b).card := by
        have hposb := Finset.card_pos.mpr hne.2
        omega
      rcases Finset.one_lt_card.mp h1a with ⟨u1, hu1, u2, hu2, hune⟩
      rcases Finset.one_lt_card.mp h1b with ⟨v1, hv1, v2, hv2, hvne⟩
      exact adj26_no_c4 hune hvne (hcross_adj u1 hu1 v1 hv1) (hcross_adj u1 hu1 v2 hv2)
        (hcross_adj u2 hu2 v1 hv1) (hcross_adj u2 hu2 v2 hv2)
    have hpair_getD : ∀ (p l : Fin 13) (i : Fin 26),
        (pgPairInput p l).getD i.val false = true → i = toPt p ∨ i = toLn l := by
      intro p l i hi
      by_cases hlt : i.val < 13
      · left
        have hget := pgPairInput_getD_pt p l ⟨i.val, hlt⟩
        rw [hi] at hget
        have heq : (⟨i.val, hlt⟩ : Fin 13) = p := of_decide_eq_true hget.symm
        have hval : i.val = p.val := congrArg Fin.val heq
        exact Fin.ext hval
      · right
        have hget := pgPairInput_getD_ln p l ⟨i.val - 13, by omega⟩
        have heqv : 13 + (i.val - 13) = i.val := by omega
        rw [heqv, hi] at hget
        have heq : (⟨i.val - 13, by omega⟩ : Fin 13) = l := of_decide_eq_true hget.symm
        apply Fin.ext
        rw [toLn_val]
        have := congrArg Fin.val heq
        dsimp at this
        omega
    rcases hcard_one with ha1 | hb1
    · rcases Finset.card_eq_one.mp ha1 with ⟨c, hc⟩
      refine ⟨c, b, by simp, ?_, ?_⟩
      · intro u hu
        exact hcross_adj c (by rw [hc]; exact Finset.mem_singleton_self c) u hu
      · intro p l hpl
        rcases (hpair_ab p l).mp hpl with ⟨⟨i, hi, hit⟩, ⟨j, hj, hjt⟩⟩
        rw [hc, Finset.mem_singleton] at hi
        rcases hi with rfl
        have hci : i = toPt p ∨ i = toLn l := hpair_getD p l i hit
        have hjj : j = toPt p ∨ j = toLn l := hpair_getD p l j hjt
        rcases hci with hpt | hln <;> rcases hjj with rfl | rfl
        · exfalso
          rw [hpt] at hc
          exact hno_two_pts p p (by rw [hc]; exact Finset.mem_singleton_self _) hj
        · exact Or.inl ⟨hpt, hj⟩
        · exact Or.inr ⟨hln, hj⟩
        · exfalso
          rw [hln] at hc
          exact hno_two_lns l l (by rw [hc]; exact Finset.mem_singleton_self _) hj
    · rcases Finset.card_eq_one.mp hb1 with ⟨c, hc⟩
      refine ⟨c, a, by simp, ?_, ?_⟩
      · intro u hu
        have hadj := hcross_adj u hu c (by rw [hc]; exact Finset.mem_singleton_self c)
        rcases hadj with ⟨p, l, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨p, l, hd, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨p, l, hd, Or.inl ⟨rfl, rfl⟩⟩
      · intro p l hpl
        rcases (hpair_ab p l).mp hpl with ⟨⟨i, hi, hit⟩, ⟨j, hj, hjt⟩⟩
        rw [hc, Finset.mem_singleton] at hj
        rcases hj with rfl
        have hcj : j = toPt p ∨ j = toLn l := hpair_getD p l j hjt
        have hii : i = toPt p ∨ i = toLn l := hpair_getD p l i hit
        rcases hcj with hpt | hln <;> rcases hii with rfl | rfl
        · exfalso
          rw [hpt] at hc
          exact hno_two_pts p p hi (by rw [hc]; exact Finset.mem_singleton_self _)
        · exact Or.inl ⟨hpt, hi⟩
        · exact Or.inr ⟨hln, hi⟩
        · exfalso
          rw [hln] at hc
          exact hno_two_lns l l hi (by rw [hc]; exact Finset.mem_singleton_self _)
  · simp [h] at hlen

private lemma main_bound (C : Circuit) (x6 x7 : ℕ)
    (hMono : Monotone2 C) (hRB : ReadsBack 26 C)
    (hNoAnd : ¬ ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j)
    (hCov : ∀ p l : Fin 13, p - l ∈ pgD → ∃ g : ℕ,
      ((gateAt C g).op = GateOp.and ∧
        (OrReaches 26 C x6 g ∨ OrReaches 26 C x7 g) ∧
        ∀ Q : Finset (Fin 13), isQuad Q → (C.wires (pgQuadInput Q)).getD (26 + g) false = false) ∧
      (C.wires (pgPairInput p l)).getD (26 + g) false = true) :
    63 ≤ C.size := by
  classical
  let good : ℕ → Prop := fun g =>
    (gateAt C g).op = GateOp.and ∧
    (OrReaches 26 C x6 g ∨ OrReaches 26 C x7 g) ∧
    (∀ Q : Finset (Fin 13), isQuad Q → (C.wires (pgQuadInput Q)).getD (26 + g) false = false) ∧
    (∃ p l : Fin 13, p - l ∈ pgD ∧ (C.wires (pgPairInput p l)).getD (26 + g) false = true)
  let A : Finset ℕ := (Finset.range C.gates.length).filter good
  let OrTop : Finset ℕ := (Finset.range C.gates.length).filter fun h =>
    (gateAt C h).op = GateOp.or ∧
    (OrReaches 26 C x6 h ∨ OrReaches 26 C x7 h) ∧
    ∃ g ∈ A, OrReaches 26 C (26 + h) g
  let OrBot : Finset ℕ := (Finset.range C.gates.length).filter fun h =>
    (gateAt C h).op = GateOp.or ∧
    ∃ g ∈ A, InCone 26 C h g
  have hA_prop : ∀ g ∈ A, g < C.gates.length ∧ good g := by
    intro g hg
    simpa [A, Finset.mem_filter, Finset.mem_range] using hg
  have hA_struct : ∀ g ∈ A, ∃ (c : Fin 26) (w : ℕ), w ∈ (gateAt C g).inputs ∧
      (∀ u ∈ orIn 26 C w, adj26 c u) ∧
      (∀ p l : Fin 13, (C.wires (pgPairInput p l)).getD (26 + g) false = true →
        (c = toPt p ∧ toLn l ∈ orIn 26 C w) ∨ (c = toLn l ∧ toPt p ∈ orIn 26 C w)) := by
    intro g hg
    rcases hA_prop g hg with ⟨_, hgop, _, hquad, hpos⟩
    exact clean_and_structure hMono hRB hNoAnd hgop hquad hpos
  let ctr : ℕ → Fin 26 := fun g =>
    if h : g ∈ A then (hA_struct g h).choose else 0
  let leafOpnd : ℕ → ℕ := fun g =>
    if h : g ∈ A then (hA_struct g h).choose_spec.choose else 0
  have hspec : ∀ g (hg : g ∈ A),
      leafOpnd g ∈ (gateAt C g).inputs ∧
      (∀ u ∈ orIn 26 C (leafOpnd g), adj26 (ctr g) u) ∧
      (∀ p l : Fin 13, (C.wires (pgPairInput p l)).getD (26 + g) false = true →
        (ctr g = toPt p ∧ toLn l ∈ orIn 26 C (leafOpnd g)) ∨
        (ctr g = toLn l ∧ toPt p ∈ orIn 26 C (leafOpnd g))) := by
    intro g hg
    simpa [ctr, leafOpnd, hg] using (hA_struct g hg).choose_spec.choose_spec
  have hdisj_A_Top : Disjoint A OrTop := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (hA_prop g hg1).2.1
    have h2 : (gateAt C g).op = GateOp.or := (Finset.mem_filter.mp hg2).2.1
    rw [h1] at h2
    cases h2
  have hdisj_A_Bot : Disjoint A OrBot := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have h1 := (hA_prop g hg1).2.1
    have h2 : (gateAt C g).op = GateOp.or := (Finset.mem_filter.mp hg2).2.1
    rw [h1] at h2
    cases h2
  have hdisj_Top_Bot : Disjoint OrTop OrBot := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    have htop := (Finset.mem_filter.mp h1).2
    have hbot := (Finset.mem_filter.mp h2).2
    rcases htop.2.2 with ⟨g1, hg1, hreach⟩
    rcases hbot.2 with ⟨g2, hg2, hcone2⟩
    have hg1op := (hA_prop g1 hg1).2.1
    have hg2op := (hA_prop g2 hg2).2.1
    have hne : g1 ≠ h := by
      intro heq
      subst heq
      rw [hg1op] at htop
      cases htop.1
    have hcone1 : InCone 26 C g1 h := inCone_of_orReaches_ne hRB h g1 hreach hne
    exact hNoAnd ⟨g1, g2, hg1op, hg2op, inCone_trans hRB g2 g1 h hcone1 hcone2⟩
  have htotal : A.card + OrTop.card + OrBot.card ≤ C.gates.length := by
    have hdisj1 : Disjoint (A ∪ OrTop) OrBot :=
      Finset.disjoint_union_left.mpr ⟨hdisj_A_Bot, hdisj_Top_Bot⟩
    rw [← Finset.card_union_of_disjoint hdisj_A_Top, ← Finset.card_union_of_disjoint hdisj1]
    calc (A ∪ OrTop ∪ OrBot).card
        ≤ (Finset.range C.gates.length).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_union] at hx
          rcases hx with (hx | hx) | hx
          · exact (Finset.mem_filter.mp hx).1
          · exact (Finset.mem_filter.mp hx).1
          · exact (Finset.mem_filter.mp hx).1
      _ = C.gates.length := Finset.card_range _
  have h13_le_A : 13 ≤ A.card := by
    let S : Finset (Fin 26) := A.image ctr
    have hcover : ∀ i : Fin 13, toPt i ∈ S ∨ toLn i ∈ S := by
      intro i
      have hiD : i - i ∈ pgD := by simpa using pg_zero_mem_D
      rcases hCov i i hiD with ⟨g, ⟨hgop, hreach, hquad⟩, hval⟩
      have hgA : g ∈ A := by
        simp only [A, good, Finset.mem_filter, Finset.mem_range]
        exact ⟨lt_gates_of_and hgop, hgop, hreach, hquad, ⟨i, i, hiD, hval⟩⟩
      rcases (hspec g hgA).2.2 i i hval with ⟨hctr, _⟩ | ⟨hctr, _⟩
      · left; exact Finset.mem_image.mpr ⟨g, hgA, hctr⟩
      · right; exact Finset.mem_image.mpr ⟨g, hgA, hctr⟩
    let f : Fin 13 → Fin 26 := fun i => if toPt i ∈ S then toPt i else toLn i
    have hfinj : Function.Injective f := by
      intro i j hij
      dsimp only [f] at hij
      split_ifs at hij with h1 h2 h2
      · exact toPt_inj hij
      · exact False.elim (toPt_ne_toLn i j hij)
      · exact False.elim (toPt_ne_toLn j i hij.symm)
      · exact toLn_inj hij
    have hfmem : (Finset.univ : Finset (Fin 13)).image f ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      dsimp only [f]
      split_ifs with h1
      · exact h1
      · rcases hcover i with hpt | hln
        · exact absurd hpt h1
        · exact hln
    calc 13 = (Finset.univ : Finset (Fin 13)).card := by simp
      _ = ((Finset.univ : Finset (Fin 13)).image f).card :=
          (Finset.card_image_of_injective _ hfinj).symm
      _ ≤ S.card := Finset.card_le_card hfmem
      _ ≤ A.card := Finset.card_image_le
  have hA_le_Top : A.card ≤ OrTop.card + 2 := by
    let U : Finset ℕ := (A ∪ OrTop).image (fun j => 26 + j)
    let U' : Finset ℕ := (U.erase x6).erase x7
    have hUcard : U.card = A.card + OrTop.card := by
      rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_union_of_disjoint hdisj_A_Top
    have hU'card : U.card ≤ U'.card + 2 := by
      have h1 : U.card ≤ (U.erase x6).card + 1 := by
        by_cases hm : x6 ∈ U
        · rw [Finset.card_erase_add_one hm]
        · rw [Finset.erase_eq_of_notMem hm]; omega
      have h2 : (U.erase x6).card ≤ U'.card + 1 := by
        by_cases hm : x7 ∈ U.erase x6
        · rw [Finset.card_erase_add_one hm]
        · simp only [U', Finset.erase_eq_of_notMem hm]; omega
      omega
    have hU'sub : U' ⊆ OrTop.biUnion (fun h => (gateAt C h).inputs.toFinset) := by
      intro u hu
      have hu7 : u ≠ x7 := (Finset.mem_erase.mp hu).1
      have hu6mem := (Finset.mem_erase.mp hu).2
      have hu6 : u ≠ x6 := (Finset.mem_erase.mp hu6mem).1
      have huU : u ∈ U := (Finset.mem_erase.mp hu6mem).2
      rcases Finset.mem_image.mp huU with ⟨j, hj, rfl⟩
      have hreach_top : OrReaches 26 C x6 j ∨ OrReaches 26 C x7 j := by
        rw [Finset.mem_union] at hj
        rcases hj with hjA | hjT
        · exact (hA_prop j hjA).2.2.1
        · exact (Finset.mem_filter.mp hjT).2.2.1
      have hreach_A : ∃ g ∈ A, OrReaches 26 C (26 + j) g := by
        rw [Finset.mem_union] at hj
        rcases hj with hjA | hjT
        · exact ⟨j, hjA, orReaches_self hRB (hA_prop j hjA).1⟩
        · exact (Finset.mem_filter.mp hjT).2.2.2
      rcases hreach_A with ⟨g, hgA, hjg⟩
      have hstep : ∀ r : ℕ, (r = x6 ∨ r = x7) → OrReaches 26 C r j →
          26 + j ∈ OrTop.biUnion (fun h => (gateAt C h).inputs.toFinset) := by
        intro r hr hrj
        rcases orReaches_parent hRB r j hrj with rfl | ⟨h, hh, hhop, hrh, hmem⟩
        · rcases hr with rfl | rfl
          · exact absurd rfl hu6
          · exact absurd rfl hu7
        · rw [Finset.mem_biUnion]
          refine ⟨h, ?_, List.mem_toFinset.mpr hmem⟩
          simp only [OrTop, Finset.mem_filter, Finset.mem_range]
          refine ⟨hh, hhop, ?_, g, hgA,
            (orReaches_iff hRB (26 + h) g).mpr ⟨h, hh, rfl, Or.inr ⟨hhop, 26 + j, hmem, hjg⟩⟩⟩
          rcases hr with rfl | rfl
          · exact Or.inl hrh
          · exact Or.inr hrh
      rcases hreach_top with h6 | h7
      · exact hstep x6 (Or.inl rfl) h6
      · exact hstep x7 (Or.inr rfl) h7
    have hU'le : U'.card ≤ 2 * OrTop.card := by
      calc U'.card
          ≤ (OrTop.biUnion (fun h => (gateAt C h).inputs.toFinset)).card := Finset.card_le_card hU'sub
        _ ≤ ∑ h ∈ OrTop, (gateAt C h).inputs.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ h ∈ OrTop, (gateAt C h).inputs.length :=
            Finset.sum_le_sum fun h _ => List.toFinset_card_le _
        _ ≤ ∑ _h ∈ OrTop, 2 :=
            Finset.sum_le_sum fun h hh =>
              gate_inputs_len_le hMono (Finset.mem_range.mp (Finset.mem_filter.mp hh).1)
        _ = OrTop.card * 2 := by simp
        _ = 2 * OrTop.card := Nat.mul_comm _ _
    omega
  have h52_le_AB : 52 ≤ A.card + OrBot.card := by
    let Kc : Fin 26 → Finset ℕ := fun c => A.filter fun g => ctr g = c
    let Wc : Fin 26 → Finset ℕ := fun c => (Kc c).image leafOpnd
    let Lc : Fin 26 → Finset (Fin 26) := fun c => (Wc c).biUnion (orIn 26 C)
    let Mc : Fin 26 → Finset ℕ := fun c => bigOrReach 26 C (Wc c)
    let E : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun e => e.1 - e.2 ∈ pgD
    let F : Finset (Fin 13 × Fin 13) :=
      (Finset.univ : Finset (Fin 26)).biUnion fun c => (Lc c).image (mkEdge c)
    have hEF : E ⊆ F := by
      intro e he
      rcases Finset.mem_filter.mp he with ⟨_, hinc⟩
      rcases hCov e.1 e.2 hinc with ⟨g, ⟨hgop, hreach, hquad⟩, hval⟩
      have hgA : g ∈ A := by
        simp only [A, good, Finset.mem_filter, Finset.mem_range]
        exact ⟨lt_gates_of_and hgop, hgop, hreach, hquad, ⟨e.1, e.2, hinc, hval⟩⟩
      have hgK : g ∈ Kc (ctr g) := Finset.mem_filter.mpr ⟨hgA, rfl⟩
      have hwW : leafOpnd g ∈ Wc (ctr g) := Finset.mem_image.mpr ⟨g, hgK, rfl⟩
      rcases (hspec g hgA).2.2 e.1 e.2 hval with ⟨hctr, hleaf⟩ | ⟨hctr, hleaf⟩
      · rw [Finset.mem_biUnion]
        refine ⟨ctr g, Finset.mem_univ _, Finset.mem_image.mpr ⟨toLn e.2, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨leafOpnd g, hwW, hleaf⟩
        · rw [hctr, mkEdge_pt_ln]
      · rw [Finset.mem_biUnion]
        refine ⟨ctr g, Finset.mem_univ _, Finset.mem_image.mpr ⟨toPt e.1, ?_, ?_⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨leafOpnd g, hwW, hleaf⟩
        · rw [hctr, mkEdge_ln_pt]
    have h52_F : 52 ≤ F.card := by
      have hE : E.card = 52 := pg_edges_card
      have hle := Finset.card_le_card hEF
      omega
    have hF_le : F.card ≤ ∑ c : Fin 26, (Lc c).card := by
      calc F.card ≤ ∑ c : Fin 26, ((Lc c).image (mkEdge c)).card := Finset.card_biUnion_le
        _ ≤ ∑ c : Fin 26, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
    have hLc_le : ∀ c : Fin 26, (Lc c).card ≤ (Kc c).card + (Mc c).card := by
      intro c
      have h1 := leaf_count_bound hMono hRB (Mc c).card (Wc c) rfl
      have h2 : (Wc c).card ≤ (Kc c).card := Finset.card_image_le
      exact le_trans h1 (Nat.add_le_add_right h2 _)
    have hsum_L : ∑ c : Fin 26, (Lc c).card ≤
        (∑ c : Fin 26, (Kc c).card) + ∑ c : Fin 26, (Mc c).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun c _ => hLc_le c
    have hK_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Kc := by
      intro c1 _ c2 _ hcne
      change Disjoint (Kc c1) (Kc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      have h1 := (Finset.mem_filter.mp hg1).2
      have h2 := (Finset.mem_filter.mp hg2).2
      exact hcne (h1.symm.trans h2)
    have hsum_K : ∑ c : Fin 26, (Kc c).card ≤ A.card := by
      rw [← Finset.card_biUnion (by intro a _ b _ hab; exact hK_disj (by simp) (by simp) hab)]
      apply Finset.card_le_card
      intro g hg
      rcases Finset.mem_biUnion.mp hg with ⟨c, _, hgc⟩
      exact (Finset.mem_filter.mp hgc).1
    have hM_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin 26)) Mc := by
      intro c1 _ c2 _ hcne
      change Disjoint (Mc c1) (Mc c2)
      rw [Finset.disjoint_left]
      intro h hh1 hh2
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hh1 hh2
      rcases hh1 with ⟨_, _, hhcard, w1, hw1, hw1h⟩
      rcases hh2 with ⟨_, _, _, w2, hw2, hw2h⟩
      rcases Finset.mem_image.mp hw1 with ⟨g1, hg1, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨g2, hg2, rfl⟩
      rcases Finset.mem_filter.mp hg1 with ⟨hg1A, hctr1⟩
      rcases Finset.mem_filter.mp hg2 with ⟨hg2A, hctr2⟩
      have hlt : 1 < (orIn 26 C (26 + h)).card := by omega
      rcases Finset.one_lt_card.mp hlt with ⟨u1, hu1, u2, hu2, hune⟩
      have hsub1 : orIn 26 C (26 + h) ⊆ orIn 26 C (leafOpnd g1) :=
        orIn_subset_of_orReaches hRB hw1h
      have hsub2 : orIn 26 C (26 + h) ⊆ orIn 26 C (leafOpnd g2) :=
        orIn_subset_of_orReaches hRB hw2h
      have ha11 := (hspec g1 hg1A).2.1 u1 (hsub1 hu1)
      have ha12 := (hspec g1 hg1A).2.1 u2 (hsub1 hu2)
      have ha21 := (hspec g2 hg2A).2.1 u1 (hsub2 hu1)
      have ha22 := (hspec g2 hg2A).2.1 u2 (hsub2 hu2)
      rw [hctr1] at ha11 ha12
      rw [hctr2] at ha21 ha22
      exact adj26_no_c4 hcne hune ha11 ha12 ha21 ha22
    have hsum_M : ∑ c : Fin 26, (Mc c).card ≤ OrBot.card := by
      rw [← Finset.card_biUnion (by intro a _ b _ hab; exact hM_disj (by simp) (by simp) hab)]
      apply Finset.card_le_card
      intro h hh
      rcases Finset.mem_biUnion.mp hh with ⟨c, _, hhc⟩
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hhc
      rcases hhc with ⟨hhlt, hhop, _, w, hw, hwh⟩
      rcases Finset.mem_image.mp hw with ⟨g, hg, rfl⟩
      rcases Finset.mem_filter.mp hg with ⟨hgA, _⟩
      simp only [OrBot, Finset.mem_filter, Finset.mem_range]
      exact ⟨hhlt, hhop, g, hgA,
        inCone_of_input_orReaches hRB (hA_prop g hgA).1 (hspec g hgA).1 hwh⟩
    omega
  change 63 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_6921

theorem PEqualNP.Outside.L_meta_6921 :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   have x8 : ℕ → List Bool → Bool := fun (x8 : ℕ) (x9 : List Bool) => (x5.wires x9).getD x8 Bool.false;   have x9 : ℕ → Prop := fun (x9 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x5 x6 x9 ∨ PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x5 x7 x9) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x4 x10 → x8 ((26 : ℕ) + x9) (x3 x10) = Bool.false;   PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → (¬∃ (x12 : ℕ) (x13 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x12 x13) → (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x1 → ∃ (x16 : ℕ), x9 x16 ∧ x8 ((26 : ℕ) + x16) (x2 x13 x14) = Bool.true) → (63 : ℕ) ≤ x5.size :=
  fun x5 x6 x7 hMono hRB hNoAnd hCov =>
    PEqualNP.Outside.L_meta_6921.main_bound x5 x6 x7 hMono hRB hNoAnd hCov
