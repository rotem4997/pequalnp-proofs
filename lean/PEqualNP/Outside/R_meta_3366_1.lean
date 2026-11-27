import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3366_1
    (h2537 : ∀ (x1 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ))) x1 → (13 : ℕ) ≤ x1)
    (single : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]) =
        (([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2)) →
      (∀ (i j : ℕ) (g h : PEqualNP.CircuitLowerBounds.Gate), i < j → C.gates[i]? = some g → C.gates[j]? = some h →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (0 ∈ g.inputs ∨ 4 ∈ g.inputs) →
        (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (0 ∈ h.inputs ∨ 4 ∈ h.inputs) → False) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  intro f C hf hs hC
  let fp : (Fin 9 → Bool) → Bool := fun y =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
  let J : (Fin 9 → Bool) → List Bool := fun y =>
    [false, y 1, y 2, y 3, false, y 5, y 6, y 7, y 8, y 0, y 0 || y 3]
  let cVal : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)
  let cRun : List Gate → List Bool → List Bool := fun l w => l.foldl (fun v g => v ++ [cVal v g]) w
  let cRho : ℕ → ℕ → ℕ → ℕ := fun m r i => if i < m then i else if i = m then r else i-1
  let cMap : (ℕ → ℕ) → Gate → Gate := fun p g => ⟨g.op, g.inputs.map p⟩
  let phi : ℕ → ℕ → ℕ := fun M i =>
    if i = 0 ∨ i = 4 then M else if i = 9 then 0 else if i = 10 then 9 else if 11 ≤ i then i - 1 else i
  have cRun_cons : ∀ (g : Gate) (l : List Gate) (w : List Bool), cRun (g :: l) w = cRun l (w ++ [cVal w g]) :=
    fun _ _ _ => rfl
  have evalRun : ∀ (D : Circuit) (x : List Bool), D.eval x = (cRun D.gates x).getD D.output false :=
    fun _ _ => rfl
  have cRun_app : ∀ (a b : List Gate) (w : List Bool), cRun (a ++ b) w = cRun b (cRun a w) :=
    fun a b w => List.foldl_append
  have cPrefix : ∀ (l : List Gate) (w : List Bool), ∃ t, cRun l w = w ++ t ∧ t.length = l.length := by
    intro l
    induction l with
    | nil => exact fun w => ⟨[], by simp [cRun], rfl⟩
    | cons g l ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [cVal w g])
      refine ⟨cVal w g :: t, ?_, by simp [hl]⟩
      rw [cRun_cons, ht]; simp
  have hand : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hor : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have cCollapse : ∀ g : Gate, g.inputs.length ≤ 2 → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      (0 ∈ g.inputs ∨ 4 ∈ g.inputs) →
      ∃ r : ℕ, ∀ f : ℕ → Bool, f 0 = false → f 4 = false → g.op.eval (g.inputs.map f) = f r := by
    rintro ⟨o, is⟩ len ho hr
    change is.length ≤ 2 at len
    change o = GateOp.and ∨ o = GateOp.or at ho
    change 0 ∈ is ∨ 4 ∈ is at hr
    rcases is with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp at hr
    · simp at hr
      refine ⟨0, ?_⟩
      intro f h0 h4
      rcases ho with rfl | rfl <;> rcases hr with e | e <;> subst a <;> simp [hand, hor, *]
    · simp at hr
      rcases ho with rfl | rfl
      · refine ⟨0, ?_⟩
        intro f h0 h4
        rcases hr with (e | e) | (e | e) <;> subst e <;> simp [hand, hor, *]
      · rcases hr with (e | e) | (e | e)
        · subst e; exact ⟨b, fun f h0 h4 => by simp [hand, hor, *]⟩
        · subst e; exact ⟨a, fun f h0 h4 => by simp [hand, hor, *]⟩
        · subst e; exact ⟨b, fun f h0 h4 => by simp [hand, hor, *]⟩
        · subst e; exact ⟨a, fun f h0 h4 => by simp [hand, hor, *]⟩
    · simp at len
  have cSnoc : ∀ (w : List Bool) (a : Bool) (i : ℕ), i ≠ w.length →
      (w ++ [a]).getD i false = w.getD i false := by
    intro w a i h
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have cTail : ∀ (m r : ℕ), r < m → ∀ (l : List Gate) (u v : List Bool),
      m ≤ v.length → u.length = v.length + 1 →
      (∀ i, u.getD i false = v.getD (cRho m r i) false) →
      ∀ i, (cRun l u).getD i false = (cRun (l.map (cMap (cRho m r))) v).getD (cRho m r i) false := by
    intro m r hr l
    induction l with
    | nil => exact fun u v _ _ rel => rel
    | cons g l ih =>
      intro u v hm hl rel
      have hg : cVal u g = cVal v (cMap (cRho m r) g) := by
        simp only [cVal,cMap,List.map_map, Function.comp_def]
        congr 1
        exact List.map_congr_left (fun i _ => rel i)
      rw [List.map_cons, cRun_cons, cRun_cons]
      apply ih (u ++ [cVal u g]) (v ++ [cVal v (cMap (cRho m r) g)]) (by simp; omega) (by simp [hl])
      intro i
      by_cases hi : i = u.length
      · subst i
        have : cRho m r u.length = v.length := by simp only [cRho]; split_ifs <;> omega
        rw [this, hg]
        simp
      · rw [cSnoc _ _ _ hi, cSnoc _ _ _ (by simp only [cRho]; split_ifs <;> omega)]
        exact rel i
  have cDelete : ∀ (a b : List Gate) (g : Gate) (out s : ℕ),
      (∀ f : ℕ → Bool, f 0 = false → f 4 = false → g.op.eval (g.inputs.map f) = f s) →
      ∀ y : Fin 9 → Bool,
        (Circuit.mk (a ++ g :: b) out).eval (J y) =
        (Circuit.mk (a ++ b.map (cMap (cRho (11 + a.length) (if s < 11 + a.length then s else 0))))
          (cRho (11 + a.length) (if s < 11 + a.length then s else 0) out)).eval (J y) := by
    intro a b g out s hs y
    obtain ⟨t, ht, htlen⟩ := cPrefix a (J y)
    have hx : (J y).length = 11 := rfl
    have hl : (cRun a (J y)).length = 11 + a.length := by rw [ht]; simp [hx, htlen]
    have hget : ∀ i, i < 11 → (cRun a (J y)).getD i false = (J y).getD i false := by
      intro i hi
      rw [ht, List.getD_append _ _ _ _ (by omega)]
    have h0 : (cRun a (J y)).getD 0 false = false := by rw [hget 0 (by decide)]; rfl
    have h4 : (cRun a (J y)).getD 4 false = false := by rw [hget 4 (by decide)]; rfl
    have hr : (if s < 11 + a.length then s else 0) < 11 + a.length := by split_ifs <;> omega
    have hv : cVal (cRun a (J y)) g = (cRun a (J y)).getD (if s < 11 + a.length then s else 0) false := by
      show g.op.eval (g.inputs.map fun i => (cRun a (J y)).getD i false) = _
      rw [hs _ h0 h4]
      split_ifs with hi
      · rfl
      · rw [List.getD_eq_default _ _ (by omega), h0]
    have rel : ∀ i, (cRun a (J y) ++ [cVal (cRun a (J y)) g]).getD i false =
        (cRun a (J y)).getD (cRho (11 + a.length) (if s < 11 + a.length then s else 0) i) false := by
      intro i
      by_cases hi : i < 11 + a.length
      · rw [cSnoc _ _ _ (show i ≠ (cRun a (J y)).length by omega)]
        simp only [cRho, hi, ↓reduceIte]
      · by_cases he : i = 11 + a.length
        · subst i
          simp only [cRho, lt_irrefl, ↓reduceIte]
          rw [← hv, ← hl]
          simp
        · rw [List.getD_eq_default _ _ (by simp; omega)]
          simp only [cRho, hi, he, ↓reduceIte]
          rw [List.getD_eq_default _ _ (by omega)]
    rw [evalRun, evalRun]
    show (cRun (a ++ g :: b) (J y)).getD out false = (cRun (a ++ _) (J y)).getD _ false
    rw [cRun_app, cRun_app, cRun_cons]
    exact cTail _ _ hr b _ _ (by omega) (by simp) rel out
  have remapTail : ∀ (M : ℕ) (l : List Gate) (u v : List Bool),
      v.length + l.length ≤ M → 10 ≤ v.length → u.length = v.length + 1 →
      (∀ i, u.getD i false = v.getD (phi M i) false) →
      ∀ i, (cRun l u).getD i false = (cRun (l.map (cMap (phi M))) v).getD (phi M i) false := by
    intro M l
    induction l with
    | nil => exact fun u v _ _ _ rel => rel
    | cons g l ih =>
      intro u v hM h10 hl rel
      have hg : cVal u g = cVal v (cMap (phi M) g) := by
        simp only [cVal,cMap,List.map_map, Function.comp_def]
        congr 1
        exact List.map_congr_left (fun i _ => rel i)
      simp only [List.length_cons] at hM
      rw [List.map_cons, cRun_cons, cRun_cons]
      apply ih (u ++ [cVal u g]) (v ++ [cVal v (cMap (phi M) g)]) (by simp; omega) (by simp; omega) (by simp [hl])
      intro i
      by_cases hi : i = u.length
      · subst i
        have : phi M u.length = v.length := by simp only [phi]; split_ifs <;> omega
        rw [this, hg]
        simp
      · rw [cSnoc _ _ _ hi, cSnoc _ _ _ (by simp only [phi]; split_ifs <;> omega)]
        exact rel i
  have remapBase : ∀ (M : ℕ), 10 ≤ M → ∀ (y : Fin 9 → Bool) (i : ℕ),
      (J y).getD i false = (List.ofFn y ++ [y 0 || y 3]).getD (phi M i) false := by
    intro M hM y i
    by_cases hi : i < 11
    · interval_cases i <;> simp [J, phi, List.ofFn_succ, hM]
    · have : phi M i = i - 1 := by simp only [phi]; split_ifs <;> omega
      rw [this, List.getD_eq_default _ _ (by simp [J]; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hJ : ∀ y, C.eval (J y) = fp y := by
    intro y
    have h := hC (Function.update y 4 false)
    have e1 : List.ofFn (Function.update (Function.update y 4 false) 0 false) ++
        [Function.update y 4 false 0 || Function.update y 4 false 4,
         Function.update y 4 false 0 || Function.update y 4 false 3] = J y := by
      simp [J, List.ofFn_succ, Function.update]
    rw [e1] at h
    rw [h]
    simp [f, fp, Function.update, Bool.or_assoc]
  apply single C hf hs hC
  intro i j g h hij hgi hhj hgo hgr hho hhr
  obtain ⟨gs, out⟩ := C
  change gs[i]? = some g at hgi
  change gs[j]? = some h at hhj
  obtain ⟨hjl, hjh⟩ := List.getElem?_eq_some_iff.mp hhj
  have hsplit : gs = gs.take j ++ h :: gs.drop (j + 1) := by
    rw [← hjh, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
  have hga : g ∈ gs.take j := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_take_of_lt hij, hgi]
  obtain ⟨a1, a2, ha⟩ := List.append_of_mem hga
  generalize gs.drop (j + 1) = b at hsplit
  rw [ha] at hsplit
  subst hsplit
  have hfan : ∀ k ∈ a1 ++ g :: a2 ++ h :: b, (k.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ k.inputs.length ≤ 2) := hf
  obtain ⟨s1, hs1⟩ := cCollapse h (hfan h (by simp)).2 hho hhr
  obtain ⟨s2, hs2⟩ := cCollapse g (hfan g (by simp)).2 hgo hgr
  have d1 := cDelete (a1 ++ g :: a2) b h out s1 hs1
  generalize cRho (11 + (a1 ++ g :: a2).length) (if s1 < 11 + (a1 ++ g :: a2).length then s1 else 0) = p1 at d1
  have d2 := cDelete a1 (a2 ++ b.map (cMap p1)) g (p1 out) s2 hs2
  generalize cRho (11 + a1.length) (if s2 < 11 + a1.length then s2 else 0) = p2 at d2
  generalize hDg : a1 ++ (a2 ++ b.map (cMap p1)).map (cMap p2) = dg at d2
  have hDv : ∀ y, (Circuit.mk dg (p2 (p1 out))).eval (J y) = fp y := by
    intro y
    rw [← d2 y]
    have e1 := d1 y
    have e0 := hJ y
    simp only [List.append_assoc, List.cons_append] at e0 e1 ⊢
    rw [← e1]
    exact e0
  have hDf : ∀ k ∈ dg, (k.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ k.inputs.length ≤ 2) := by
    intro k hk
    rw [← hDg] at hk
    simp only [List.map_append, List.map_map, List.mem_append, List.mem_map] at hk
    rcases hk with hk | ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩
    · exact hfan k (by simp [hk])
    · simpa [cMap] using hfan k' (by simp [hk'])
    · simpa [cMap] using hfan k' (by simp [hk'])
  have hsz : dg.length + 2 = (a1 ++ g :: a2 ++ h :: b).length := by
    rw [← hDg]; simp; omega
  have hs' : (a1 ++ g :: a2 ++ h :: b).length ≤ 13 := hs
  have hfin := h2537 (dg.length + 1)
    ⟨⟨⟨GateOp.or, [0, 3]⟩ :: dg.map (cMap (phi (11 + dg.length))), phi (11 + dg.length) (p2 (p1 out))⟩, ?_, ?_, ?_⟩
  · omega
  · intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · simp
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      simpa [cMap] using hDf k' hk'
  · show (_ :: List.map _ dg).length ≤ dg.length + 1
    simp
  · intro y
    show _ = fp y
    rw [← hDv y]
    have ht := remapTail (11 + dg.length) dg (J y) (List.ofFn y ++ [y 0 || y 3])
      (by simp) (by simp) (by simp [J]) (remapBase _ (by omega) y) (p2 (p1 out))
    rw [evalRun, evalRun]
    show (cRun (_ :: _) (List.ofFn y)).getD _ false = _
    rw [cRun_cons]
    have e2 : (List.ofFn y ++ [cVal (List.ofFn y) ⟨GateOp.or, [0, 3]⟩]) = List.ofFn y ++ [y 0 || y 3] := by
      simp [cVal, hor, List.ofFn_succ]
    rw [e2]
    exact ht.symm
