import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_19000

def evalWires (gs : List Gate) (x : Fin 26 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def ValidGates (gs : List Gate) : Prop :=
  ∀ k g, gs[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b : Fin (26 + k), g.inputs = [a.val, b.val] ∧ a ≠ b

def AndHasInput (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op = GateOp.and → ∃ c : Fin 26, c.val ∈ g.inputs

lemma foldl_wires_append (gs : List Gate) (w : List Bool) :
    ∃ ext : List Bool, ext.length = gs.length ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ ext := by
  induction gs generalizing w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    obtain ⟨ext, hlen, heq⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: ext, by simp [hlen], ?_⟩
    rw [heq]; simp

lemma evalWires_length (gs : List Gate) (x : Fin 26 → Bool) :
    (evalWires gs x).length = 26 + gs.length := by
  obtain ⟨ext, hlen, heq⟩ := foldl_wires_append gs (List.ofFn x)
  rw [evalWires, heq, List.length_append, List.length_ofFn, hlen]

lemma evalWires_append_getD_lt (gs1 gs2 : List Gate) (x : Fin 26 → Bool) {i : ℕ}
    (hi : i < 26 + gs1.length) :
    (evalWires (gs1 ++ gs2) x).getD i false = (evalWires gs1 x).getD i false := by
  rw [evalWires, List.foldl_append]
  obtain ⟨ext, _, heq⟩ := foldl_wires_append gs2 (evalWires gs1 x)
  change (gs2.foldl _ (evalWires gs1 x)).getD i false = _
  rw [heq]
  have hlen : (evalWires gs1 x).length = 26 + gs1.length := evalWires_length gs1 x
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < (evalWires gs1 x).length)]

lemma evalWires_snoc (gs : List Gate) (g : Gate) (x : Fin 26 → Bool) :
    evalWires (gs ++ [g]) x =
      evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)] := by
  simp [evalWires, List.foldl_append]

lemma evalWires_snoc_last (gs : List Gate) (g : Gate) (x : Fin 26 → Bool) :
    (evalWires (gs ++ [g]) x).getD (26 + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
  rw [evalWires_snoc]
  have hlen : (evalWires gs x).length = 26 + gs.length := evalWires_length gs x
  simp [List.getD_eq_getElem?_getD, ← hlen]

lemma evalWires_input (gs : List Gate) (x : Fin 26 → Bool) (v : Fin 26) :
    (evalWires gs x).getD v.val false = x v := by
  have h := evalWires_append_getD_lt [] gs x (i := v.val) (by simp)
  rw [List.nil_append] at h
  rw [h]
  simp only [evalWires, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt,
    ↓reduceDIte, Option.getD_some, Fin.eta]

lemma validGates_snoc {gs : List Gate} (hvg : ValidGates gs) {op : GateOp} {a b : ℕ}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (ha : a < 26 + gs.length) (hb : b < 26 + gs.length) (hne : a ≠ b) :
    ValidGates (gs ++ [⟨op, [a, b]⟩]) := by
  intro k g hkg
  by_cases hlt : k < gs.length
  · rw [List.getElem?_append_left hlt] at hkg
    exact hvg k g hkg
  · have hkeq : k = gs.length := by
      have hle : gs.length ≤ k := Nat.le_of_not_lt hlt
      by_contra hne'
      have hgt : (gs ++ [Gate.mk op [a, b]]).length ≤ k := by simp; omega
      rw [List.getElem?_eq_none hgt] at hkg
      cases hkg
    subst hkeq
    have hgeq : g = Gate.mk op [a, b] := (by simpa using hkg : Gate.mk op [a, b] = g).symm
    subst hgeq
    refine ⟨hop, ⟨a, ha⟩, ⟨b, hb⟩, rfl, ?_⟩
    intro heq
    exact hne (congrArg Fin.val heq)

def orChain (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws => orChain (gs ++ [⟨GateOp.or, [acc, w]⟩]) (26 + gs.length) ws

lemma orChain_spec (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (hvg : ValidGates gs) (hahi : AndHasInput gs)
    (hacc : acc < 26 + gs.length) (hws : ∀ w ∈ ws, w < 26 + gs.length ∧ w ≠ acc) :
    let res := orChain gs acc ws
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = ws.length) ∧
    ValidGates res.1 ∧
    AndHasInput res.1 ∧
    res.2 < 26 + res.1.length ∧
    (ws ≠ [] → 26 ≤ res.2) ∧
    ∀ x : Fin 26 → Bool,
      (evalWires res.1 x).getD res.2 false = true ↔
        (evalWires gs x).getD acc false = true ∨ ∃ w ∈ ws, (evalWires gs x).getD w false = true := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨⟨[], by simp [orChain]⟩, hvg, hahi, hacc, fun h => (h rfl).elim, ?_⟩
    intro x; simp [orChain]
  | cons w ws ih =>
    have hw : w < 26 + gs.length ∧ w ≠ acc := hws w (by simp)
    let gs1 := gs ++ [⟨GateOp.or, [acc, w]⟩]
    let idx := 26 + gs.length
    have hvg1 : ValidGates gs1 :=
      validGates_snoc hvg (Or.inr rfl) hacc hw.1 hw.2.symm
    have hahi1 : AndHasInput gs1 := by
      intro g hg hand
      simp only [gs1, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hahi g hg hand
      · cases hand
    have hidx : idx < 26 + gs1.length := by simp [gs1, idx]
    have hws1 : ∀ w' ∈ ws, w' < 26 + gs1.length ∧ w' ≠ idx := by
      intro w' hw'
      have h' := (hws w' (by simp [hw'])).1
      exact ⟨by simp [gs1]; omega, by omega⟩
    obtain ⟨⟨ext, heq, hlen⟩, hvg2, hahi2, houtlt, hge26, heval⟩ :=
      ih gs1 idx hvg1 hahi1 hidx hws1
    have hres1 : (orChain gs acc (w :: ws)).1 = gs ++ (⟨GateOp.or, [acc, w]⟩ :: ext) := by
      show (orChain gs1 idx ws).1 = _
      rw [heq]; simp [gs1]
    refine ⟨⟨⟨GateOp.or, [acc, w]⟩ :: ext, hres1, by simp [hlen]⟩, hvg2, hahi2, houtlt, ?_, ?_⟩
    · intro _
      cases ws with
      | nil => show 26 ≤ idx; omega
      | cons _ _ => exact hge26 (by simp)
    · intro x
      show (evalWires (orChain gs1 idx ws).1 x).getD (orChain gs1 idx ws).2 false = true ↔ _
      rw [heval x]
      have hlast : (evalWires gs1 x).getD idx false = true ↔
          (evalWires gs x).getD acc false = true ∨ (evalWires gs x).getD w false = true := by
        rw [evalWires_snoc_last gs ⟨GateOp.or, [acc, w]⟩ x]
        have hOr : ∀ b1 b2 : Bool, GateOp.eval GateOp.or [b1, b2] = (b1 || b2) := by decide
        simp only [List.map_cons, List.map_nil]
        rw [hOr]
        simp [Bool.or_eq_true]
      rw [hlast]
      constructor
      · rintro ((ha | hw') | ⟨w', hw'in, hw't⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨w, by simp, hw'⟩
        · have hw'lt := (hws w' (by simp [hw'in])).1
          rw [evalWires_append_getD_lt gs [⟨GateOp.or, [acc, w]⟩] x hw'lt] at hw't
          exact Or.inr ⟨w', by simp [hw'in], hw't⟩
      · rintro (ha | ⟨w', hw'in, hw't⟩)
        · exact Or.inl (Or.inl ha)
        · simp only [List.mem_cons] at hw'in
          rcases hw'in with rfl | hw'in
          · exact Or.inl (Or.inr hw't)
          · right
            refine ⟨w', hw'in, ?_⟩
            have hw'lt := (hws w' (by simp [hw'in])).1
            rw [evalWires_append_getD_lt gs [⟨GateOp.or, [acc, w]⟩] x hw'lt]
            exact hw't

def buildStars (gs : List Gate) : List (Fin 26 × List (Fin 26)) → List Gate × List ℕ
  | [] => (gs, [])
  | (c, []) :: rest => buildStars gs rest
  | (c, w0 :: ws) :: rest =>
    let p := orChain gs w0.val (ws.map Fin.val)
    let gs2 := p.1 ++ [⟨GateOp.and, [c.val, p.2]⟩]
    let starW := 26 + p.1.length
    let q := buildStars gs2 rest
    (q.1, starW :: q.2)

lemma buildStars_spec (gs : List Gate) (items : List (Fin 26 × List (Fin 26)))
    (hvg : ValidGates gs) (hahi : AndHasInput gs)
    (hitems : ∀ it ∈ items, it.2 ≠ [] ∧ it.2.Nodup ∧ ∀ w ∈ it.2, w ≠ it.1) :
    let res := buildStars gs items
    (∃ ext, res.1 = gs ++ ext ∧ ext.length = (items.map fun it => it.2.length).sum) ∧
    ValidGates res.1 ∧
    AndHasInput res.1 ∧
    res.2.length = items.length ∧
    res.2.Nodup ∧
    (∀ w ∈ res.2, 26 + gs.length ≤ w ∧ w < 26 + res.1.length) ∧
    ∀ x : Fin 26 → Bool,
      (∃ w ∈ res.2, (evalWires res.1 x).getD w false = true) ↔
        ∃ it ∈ items, x it.1 = true ∧ ∃ u ∈ it.2, x u = true := by
  induction items generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [buildStars]⟩, hvg, hahi, rfl, List.nodup_nil, by simp [buildStars], ?_⟩
    intro x; simp [buildStars]
  | cons hd rest ih =>
    rcases hd with ⟨c, nbrs⟩
    have hhd := hitems (c, nbrs) (by simp)
    cases nbrs with
    | nil => exact (hhd.1 rfl).elim
    | cons w0 ws =>
      have hnd : (w0 :: ws).Nodup := hhd.2.1
      have hne_c : ∀ w ∈ w0 :: ws, w ≠ c := hhd.2.2
      have hws_lt : ∀ w ∈ ws.map Fin.val, w < 26 + gs.length ∧ w ≠ w0.val := by
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        have hu_ne : u ≠ w0 := fun h => by
          subst h
          exact (List.nodup_cons.mp hnd).1 hu
        exact ⟨by have := u.isLt; omega, fun heq => hu_ne (Fin.ext heq)⟩
      obtain ⟨⟨ext1, heq1, hlen1⟩, hvg1, hahi1, horlt, hge26, heval1⟩ :=
        orChain_spec gs w0.val (ws.map Fin.val) hvg hahi (by have := w0.isLt; omega) hws_lt
      set p := orChain gs w0.val (ws.map Fin.val)
      have hcne : c.val ≠ p.2 := by
        cases hws_eq : ws with
        | nil =>
          have hp2 : p.2 = w0.val := by simp [p, hws_eq, orChain]
          rw [hp2]
          intro h
          exact hne_c w0 (by simp) (Fin.ext h.symm)
        | cons _ _ =>
          have h26 : 26 ≤ p.2 := hge26 (by simp [hws_eq])
          have := c.isLt
          omega
      let gs2 := p.1 ++ [⟨GateOp.and, [c.val, p.2]⟩]
      let starW := 26 + p.1.length
      have hvg2 : ValidGates gs2 :=
        validGates_snoc hvg1 (Or.inl rfl) (by have := c.isLt; omega) horlt hcne
      have hahi2 : AndHasInput gs2 := by
        intro g hg hand
        simp only [gs2, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hahi1 g hg hand
        · exact ⟨c, by simp⟩
      have hrest : ∀ it ∈ rest, it.2 ≠ [] ∧ it.2.Nodup ∧ ∀ w ∈ it.2, w ≠ it.1 :=
        fun it hit => hitems it (by simp [hit])
      obtain ⟨⟨ext2, heq2, hlen2⟩, hvg3, hahi3, hlenw, hndw, hwbounds, heval2⟩ :=
        ih gs2 hvg2 hahi2 hrest
      set q := buildStars gs2 rest
      have hq1 : (buildStars gs ((c, w0 :: ws) :: rest)).1 =
          gs ++ (ext1 ++ [Gate.mk GateOp.and [c.val, p.2]] ++ ext2) := by
        show q.1 = _
        rw [heq2]; simp [gs2, heq1, List.append_assoc]
      have hstar_val : ∀ x : Fin 26 → Bool,
          (evalWires q.1 x).getD starW false = true ↔
            x c = true ∧ ∃ u ∈ w0 :: ws, x u = true := by
        intro x
        have hlt2 : starW < 26 + gs2.length := by simp [gs2, starW]
        rw [heq2, evalWires_append_getD_lt gs2 ext2 x hlt2]
        rw [evalWires_snoc_last p.1 ⟨GateOp.and, [c.val, p.2]⟩ x]
        have hAnd : ∀ b1 b2 : Bool, GateOp.eval GateOp.and [b1, b2] = (b1 && b2) := by decide
        simp only [List.map_cons, List.map_nil]
        rw [hAnd, Bool.and_eq_true, evalWires_input, heval1 x]
        constructor
        · rintro ⟨hxc, hw0 | ⟨w, hwin, hwt⟩⟩
          · refine ⟨hxc, w0, by simp, ?_⟩
            rwa [evalWires_input] at hw0
          · rw [List.mem_map] at hwin
            obtain ⟨u, hu, rfl⟩ := hwin
            refine ⟨hxc, u, by simp [hu], ?_⟩
            rwa [evalWires_input] at hwt
        · rintro ⟨hxc, u, hu, hxu⟩
          refine ⟨hxc, ?_⟩
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · left; rwa [evalWires_input]
          · right
            refine ⟨u.val, List.mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
            rwa [evalWires_input]
      refine ⟨⟨ext1 ++ [⟨GateOp.and, [c.val, p.2]⟩] ++ ext2, hq1, ?_⟩, hvg3, hahi3, ?_, ?_, ?_, ?_⟩
      · simp [hlen1, hlen2]; omega
      · show (starW :: q.2).length = (rest.length + 1); simp [hlenw]
      · show (starW :: q.2).Nodup
        rw [List.nodup_cons]
        refine ⟨?_, hndw⟩
        intro hmem
        have hb := (hwbounds starW hmem).1
        have hlen_gs2 : gs2.length = p.1.length + 1 := by simp [gs2]
        have hstar : starW = 26 + p.1.length := rfl
        omega
      · intro w hw
        show 26 + gs.length ≤ w ∧ w < 26 + q.1.length
        simp only [buildStars, List.mem_cons] at hw
        have hp1len : p.1.length = gs.length + ext1.length := by
          simpa [p, List.length_append] using congrArg List.length heq1
        have hgs2len : gs2.length = p.1.length + 1 := by simp [gs2]
        have hq1len : q.1.length = gs2.length + ext2.length := by
          simpa [q, List.length_append] using congrArg List.length heq2
        rcases hw with rfl | hw
        · exact ⟨by show 26 + gs.length ≤ 26 + p.1.length; omega,
            by show 26 + p.1.length < 26 + q.1.length; omega⟩
        · obtain ⟨hlo, hhi⟩ := hwbounds w hw
          exact ⟨by omega, hhi⟩
      · intro x
        show (∃ w ∈ starW :: q.2, (evalWires q.1 x).getD w false = true) ↔ _
        constructor
        · rintro ⟨w, hw, hwt⟩
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact ⟨(c, w0 :: ws), by simp, (hstar_val x).mp hwt⟩
          · obtain ⟨it, hit, hspec⟩ := (heval2 x).mp ⟨w, hw, hwt⟩
            exact ⟨it, by simp [hit], hspec⟩
        · rintro ⟨it, hit, hspec⟩
          simp only [List.mem_cons] at hit
          rcases hit with rfl | hit
          · exact ⟨starW, by simp, (hstar_val x).mpr hspec⟩
          · obtain ⟨w, hw, hwt⟩ := (heval2 x).mpr ⟨it, hit, hspec⟩
            exact ⟨w, by simp [hw], hwt⟩

lemma hasStarProfile_of_andHasInput (G : SimpleGraph (Fin 26)) (A : Circuit)
    (hahi : AndHasInput A.gates) : HasStarProfile 26 G A := by
  intro j hj hand
  have hgj : gateAt A j ∈ A.gates := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  obtain ⟨c, hc⟩ := hahi (gateAt A j) hgj hand
  right
  refine ⟨c, ?_⟩
  intro u v _ howns
  have hval : (evalWires A.gates (pairInput u v)).getD (26 + j) false = true := howns.2.2.1
  have hsplit : A.gates = A.gates.take j ++ gateAt A j :: A.gates.drop (j + 1) := by
    have hg : A.gates[j] = gateAt A j := by
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [← hg, ← List.drop_eq_getElem_cons hj]
    exact (List.take_append_drop j A.gates).symm
  have hgate : (evalWires A.gates (pairInput u v)).getD (26 + j) false =
      (gateAt A j).op.eval ((gateAt A j).inputs.map fun i => (evalWires (A.gates.take j) (pairInput u v)).getD i false) := by
    have htake : (A.gates.take j).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    conv_lhs => rw [hsplit]
    have hlt : 26 + j < 26 + (A.gates.take j ++ [gateAt A j]).length := by simp [htake]
    have h1 : A.gates.take j ++ gateAt A j :: A.gates.drop (j + 1) =
        (A.gates.take j ++ [gateAt A j]) ++ A.gates.drop (j + 1) := by simp
    have h2 := evalWires_snoc_last (A.gates.take j) (gateAt A j) (pairInput u v)
    rw [htake] at h2
    rw [h1, evalWires_append_getD_lt _ _ _ hlt, h2]
  rw [hgate, hand, GateOp.eval, List.all_eq_true] at hval
  have hcval : (evalWires (A.gates.take j) (pairInput u v)).getD c.val false = true := by
    have := hval true (List.mem_map.mpr ⟨c.val, hc, by
      cases h : (evalWires (A.gates.take j) (pairInput u v)).getD c.val false
      · exfalso
        have hfalse := hval false (List.mem_map.mpr ⟨c.val, hc, h⟩)
        exact Bool.false_ne_true hfalse
      · rfl⟩)
    cases h : (evalWires (A.gates.take j) (pairInput u v)).getD c.val false
    · exfalso
      have hfalse := hval false (List.mem_map.mpr ⟨c.val, hc, h⟩)
      exact Bool.false_ne_true hfalse
    · rfl
  rw [evalWires_input] at hcval
  simp only [pairInput, decide_eq_true_eq] at hcval
  rcases hcval with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma main (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (S : Finset (Fin 26))
    (hcov : ∀ u v : Fin 26, G.Adj u v → u ∈ S ∨ v ∈ S) :
    ∃ A : Circuit,
      ValidGates A.gates ∧
      circuitFun 26 A = graphFun G ∅ ∧
      HasStarProfile 26 G A ∧
      A.size ≤ G.edgeFinset.card + S.card - 1 := by
  classical
  by_cases hempty : G.edgeFinset = ∅
  · refine ⟨⟨[], 26⟩, ?_, ?_, ?_, by show ([] : List Gate).length ≤ _; simp⟩
    · intro k g hkg; simp at hkg
    · funext x
      have hno : ∀ u v : Fin 26, ¬ G.Adj u v := by
        intro u v huv
        have : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
        rw [hempty] at this
        exact Finset.notMem_empty _ this
      have hl : (⟨[], 26⟩ : Circuit).eval (List.ofFn x) = false := by
        simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
      have hr : graphFun G ∅ x = false := by
        simp [graphFun, hno]
      exact hl.trans hr.symm
    · intro j hj; simp at hj
  · let N : Fin 26 → Finset (Fin 26) := fun c =>
      Finset.univ.filter fun w => G.Adj c w ∧ (w ∉ S ∨ c < w)
    have hsum : ∑ c ∈ S, (N c).card = G.edgeFinset.card := by
      have hsig : (S.sigma N).card = ∑ c ∈ S, (N c).card := Finset.card_sigma S N
      rw [← hsig]
      refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_sigma] at hp
        have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp.2).2.1
        exact SimpleGraph.mem_edgeFinset.mpr hadj
      · intro p1 hp1 p2 hp2 heq
        rcases p1 with ⟨a1, b1⟩
        rcases p2 with ⟨a2, b2⟩
        rw [Finset.mem_sigma] at hp1 hp2
        have h1 := (Finset.mem_filter.mp hp1.2).2
        have h2 := (Finset.mem_filter.mp hp2.2).2
        simp only [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨heq1, heq2⟩
        · rfl
        · exfalso
          have h1lt : a1 < b1 := by
            rcases h1.2 with hnot | hlt
            · exact (hnot (heq2 ▸ hp2.1)).elim
            · exact hlt
          have h2lt : a2 < b2 := by
            rcases h2.2 with hnot | hlt
            · exact (hnot (heq1 ▸ hp1.1)).elim
            · exact hlt
          rw [heq1, heq2] at h1lt
          exact lt_asymm h1lt h2lt
      · intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
          have hne : u ≠ v := huv.ne
          rcases hcov u v huv with huS | hvS
          · by_cases hvS' : v ∈ S
            · rcases lt_or_gt_of_ne hne with hlt | hgt
              · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Or.inr hlt⟩⟩, rfl⟩
              · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvS', Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, Or.inr hgt⟩⟩, Sym2.eq_swap⟩
            · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Or.inl hvS'⟩⟩, rfl⟩
          · by_cases huS' : u ∈ S
            · rcases lt_or_gt_of_ne hne with hlt | hgt
              · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huS', Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Or.inr hlt⟩⟩, rfl⟩
              · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, Or.inr hgt⟩⟩, Sym2.eq_swap⟩
            · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, Or.inl huS'⟩⟩, Sym2.eq_swap⟩
    let S' := S.filter fun c => (N c).Nonempty
    have hS'sub : S' ⊆ S := Finset.filter_subset _ _
    have hS'card_le : S'.card ≤ S.card := Finset.card_le_card hS'sub
    have hsum' : ∑ c ∈ S', (N c).card = G.edgeFinset.card := by
      rw [← hsum]
      apply Finset.sum_subset hS'sub
      intro c hcS hcnot
      have hem : ¬ (N c).Nonempty := fun hne => hcnot (Finset.mem_filter.mpr ⟨hcS, hne⟩)
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      simp [hem]
    have hS'ne : S'.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty] at hsum'
      exact hempty (Finset.card_eq_zero.mp hsum'.symm)
    let items : List (Fin 26 × List (Fin 26)) := S'.toList.map fun c => (c, (N c).toList)
    have hitems : ∀ it ∈ items, it.2 ≠ [] ∧ it.2.Nodup ∧ ∀ w ∈ it.2, w ≠ it.1 := by
      intro it hit
      rw [List.mem_map] at hit
      obtain ⟨c, hc, rfl⟩ := hit
      have hc' : c ∈ S' := Finset.mem_toList.mp hc
      have hne : (N c).Nonempty := (Finset.mem_filter.mp hc').2
      refine ⟨?_, Finset.nodup_toList _, ?_⟩
      · intro hnil
        dsimp only at hnil
        obtain ⟨w, hw⟩ := hne
        have : w ∈ (N c).toList := Finset.mem_toList.mpr hw
        rw [hnil] at this
        cases this
      · intro w hw
        have hw' : w ∈ N c := Finset.mem_toList.mp hw
        exact (Finset.mem_filter.mp hw').2.1.ne.symm
    obtain ⟨⟨extS, heqS, hlenS⟩, hvgS, hahiS, hlenW, hndW, hboundsW, hevalS⟩ :=
      buildStars_spec [] items (by intro k g h; simp at h) (by intro g h; cases h) hitems
    set resS := buildStars [] items
    have hitems_len : items.length = S'.card := by simp [items]
    have hWne : resS.2 ≠ [] := by
      intro hnil
      have h0 : S'.card = 0 := by
        have h1 : resS.2.length = 0 := by rw [hnil]; rfl
        have h2 : resS.2.length = items.length := hlenW
        omega
      exact (Finset.card_pos.mpr hS'ne).ne' h0
    cases hW : resS.2 with
    | nil => exact (hWne hW).elim
    | cons w0 ws =>
      have hw0_lt : w0 < 26 + resS.1.length := (hboundsW w0 (by simp [hW])).2
      have hws_lt : ∀ w ∈ ws, w < 26 + resS.1.length ∧ w ≠ w0 := by
        intro w hw
        have hlt := (hboundsW w (by simp [hW, hw])).2
        have hne : w ≠ w0 := fun h => by
          subst h
          rw [hW] at hndW
          exact (List.nodup_cons.mp hndW).1 hw
        exact ⟨hlt, hne⟩
      obtain ⟨⟨extO, heqO, hlenO⟩, hvgO, hahiO, _, _, hevalO⟩ :=
        orChain_spec resS.1 w0 ws hvgS hahiS hw0_lt hws_lt
      set resO := orChain resS.1 w0 ws
      refine ⟨⟨resO.1, resO.2⟩, hvgO, ?_, hasStarProfile_of_andHasInput G ⟨resO.1, resO.2⟩ hahiO, ?_⟩
      · funext x
        apply Bool.eq_iff_iff.mpr
        change (evalWires resO.1 x).getD resO.2 false = true ↔ graphFun G ∅ x = true
        rw [hevalO x]
        have hlhs : ((evalWires resS.1 x).getD w0 false = true ∨
            ∃ w ∈ ws, (evalWires resS.1 x).getD w false = true) ↔
            ∃ w ∈ resS.2, (evalWires resS.1 x).getD w false = true := by
          rw [hW]
          constructor
          · rintro (h | ⟨w, hw, hwt⟩)
            · exact ⟨w0, by simp, h⟩
            · exact ⟨w, by simp [hw], hwt⟩
          · rintro ⟨w, hw, hwt⟩
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact Or.inl hwt
            · exact Or.inr ⟨w, hw, hwt⟩
        rw [hlhs, hevalS x]
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq]
        constructor
        · rintro ⟨it, hit, hxc, u, hu, hxu⟩
          rw [List.mem_map] at hit
          obtain ⟨c, _, rfl⟩ := hit
          have hu' : u ∈ N c := Finset.mem_toList.mp hu
          exact ⟨c, u, (Finset.mem_filter.mp hu').2.1, hxc, hxu⟩
        · rintro ⟨u, v, huv, hxu, hxv⟩
          have hne : u ≠ v := huv.ne
          have hpair : ∃ c ∈ S', ∃ w ∈ N c, x c = true ∧ x w = true := by
            rcases hcov u v huv with huS | hvS
            · by_cases hvS' : v ∈ S
              · rcases lt_or_gt_of_ne hne with hlt | hgt
                · have hvN : v ∈ N u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Or.inr hlt⟩
                  exact ⟨u, Finset.mem_filter.mpr ⟨huS, ⟨v, hvN⟩⟩, v, hvN, hxu, hxv⟩
                · have huN : u ∈ N v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, Or.inr hgt⟩
                  exact ⟨v, Finset.mem_filter.mpr ⟨hvS', ⟨u, huN⟩⟩, u, huN, hxv, hxu⟩
              · have hvN : v ∈ N u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Or.inl hvS'⟩
                exact ⟨u, Finset.mem_filter.mpr ⟨huS, ⟨v, hvN⟩⟩, v, hvN, hxu, hxv⟩
            · by_cases huS' : u ∈ S
              · rcases lt_or_gt_of_ne hne with hlt | hgt
                · have hvN : v ∈ N u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, Or.inr hlt⟩
                  exact ⟨u, Finset.mem_filter.mpr ⟨huS', ⟨v, hvN⟩⟩, v, hvN, hxu, hxv⟩
                · have huN : u ∈ N v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, Or.inr hgt⟩
                  exact ⟨v, Finset.mem_filter.mpr ⟨hvS, ⟨u, huN⟩⟩, u, huN, hxv, hxu⟩
              · have huN : u ∈ N v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, Or.inl huS'⟩
                exact ⟨v, Finset.mem_filter.mpr ⟨hvS, ⟨u, huN⟩⟩, u, huN, hxv, hxu⟩
          obtain ⟨c, hcS', w, hwN, hxc, hxw⟩ := hpair
          refine ⟨(c, (N c).toList), List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hcS', rfl⟩, hxc,
            w, Finset.mem_toList.mpr hwN, hxw⟩
      · have hlen_sum : (items.map fun it => it.2.length).sum = G.edgeFinset.card := by
          rw [← hsum']
          have hmap : (items.map fun it => it.2.length) = S'.toList.map (fun c => (N c).card) := by
            simp [items, List.map_map, Function.comp_def]
          rw [hmap]
          change (Multiset.map (fun c => (N c).card) (S'.toList : Multiset (Fin 26))).sum = ∑ c ∈ S', (N c).card
          rw [Finset.coe_toList]
          rfl
        have hresS_len : resS.1.length = G.edgeFinset.card := by
          rw [heqS, List.nil_append, hlenS, hlen_sum]
        have hws_len : ws.length = S'.card - 1 := by
          have : (w0 :: ws).length = S'.card := by rw [← hW, hlenW, hitems_len]
          simp at this
          omega
        have hresO_len : resO.1.length = resS.1.length + ws.length := by
          rw [heqO, List.length_append, hlenO]
        have hS'pos : 1 ≤ S'.card := Finset.card_pos.mpr hS'ne
        show resO.1.length ≤ G.edgeFinset.card + S.card - 1
        omega

end PEqualNP.Outside.L_meta_19000

theorem PEqualNP.Outside.L_meta_19000 : (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : Finset (Fin (26 : ℕ))), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 → x4 ∈ x3 ∨ x5 ∈ x3) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : Fin ((26 : ℕ) + x6)) (x10 : Fin ((26 : ℕ) + x6)), x7.inputs = [↑x9, ↑x10] ∧ x9 ≠ x10) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x1 x5 ∧ x5.size ≤ x1.edgeFinset.card + x3.card - (1 : ℕ)) := by
  exact fun G _ S hcov => PEqualNP.Outside.L_meta_19000.main G S hcov
