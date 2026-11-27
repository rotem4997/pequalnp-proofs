import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_3295_1
    (lower : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)) 12)
    (notFirst :
      let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (j : ℕ), FanInTwo p → FanInTwo t →
        p.size + t.size = 13 → 8 ≤ j → j < 8 + p.size →
        (∃ g : Gate, t.gates.head? = some g ∧ g.op = GateOp.not ∧ g.inputs.head? = some (8 + p.size)) →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let q := fun x => (w x).getD j false
        (∀ x, f x = false → (x 0 || x 3) = true → q x = true) →
        (∀ x, t.eval (w x ++ [q x]) = f x) →
        ∃ x, t.eval (w x ++ [false]) ≠ (f x || x 0 || x 3))
    (andFirst :
      let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (j : ℕ), FanInTwo p → FanInTwo t →
        p.size + t.size = 13 → 8 ≤ j → j < 8 + p.size →
        (∃ g : Gate, t.gates.head? = some g ∧ g.op = GateOp.and ∧ 8 + p.size ∈ g.inputs) →
        (∃ n ∈ t.gates, n.op = GateOp.not) →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let q := fun x => (w x).getD j false
        (∀ x, f x = false → (x 0 || x 3) = true → q x = true) →
        (∀ x, t.eval (w x ++ [q x]) = f x) →
        ∃ x, t.eval (w x ++ [false]) ≠ (f x || x 0 || x 3))
    (orFirst :
      let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
      ∀ (p t : Circuit) (j : ℕ), FanInTwo p → FanInTwo t →
        p.size + t.size = 13 → 8 ≤ j → j < 8 + p.size →
        (∃ g : Gate, t.gates.head? = some g ∧ g.op = GateOp.or ∧ 8 + p.size ∈ g.inputs) →
        (∃ n ∈ t.gates, n.op = GateOp.not) →
        let w := fun x : Fin 8 → Bool => p.wires (List.ofFn x)
        let q := fun x => (w x).getD j false
        (∀ x, f x = false → (x 0 || x 3) = true → q x = true) →
        (∀ x, t.eval (w x ++ [q x]) = f x) →
        ∃ x, t.eval (w x ++ [false]) ≠ (f x || x 0 || x 3))
    : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         (8 : ℕ) ≤ x4 →           x4 < (8 : ℕ) + x2.size →             have x10 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x10 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x10);             have x11 : (Fin (8 : ℕ) → Bool) → Bool := fun (x11 : Fin (8 : ℕ) → Bool) => (x10 x11).getD x4 Bool.false;             (∀ (x12 : Fin (8 : ℕ) → Bool), x1 x12 = Bool.false → (x12 (0 : Fin (8 : ℕ)) || x12 (3 : Fin (8 : ℕ))) = Bool.true → x11 x12 = Bool.true) → (∀ (x13 : Fin (8 : ℕ) → Bool), x3.eval (x10 x13 ++ [x11 x13]) = x1 x13) → ∃ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x10 x14 ++ [Bool.false]) ≠ (x1 x14 || x14 (0 : Fin (8 : ℕ)) || x14 (3 : Fin (8 : ℕ))) := by
  classical
  let f := fun x : Fin 8 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  let run := fun (gs : List Gate) (w : List Bool) =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  let remap := fun (s : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map s)
  have snocOther (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have snocLast (w : List Bool) (b : Bool) :
      (w ++ [b]).getD w.length false = b := by simp
  have bankLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (w ++ [_])).length = _
      rw [ih]
      simp
      omega
  have prefixLength (p : Circuit) (x : Fin 8 → Bool) :
      (p.wires (List.ofFn x)).length = 8 + p.size := by
    change (run p.gates (List.ofFn x)).length = 8 + p.gates.length
    rw [bankLength]
    simp
  have remapFan (s : ℕ → ℕ) (g : Gate)
      (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (remap s g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (remap s g).inputs.length ≤ 2 := by simpa only [remap, List.length_map]
  have runMap (s : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
      (hr : ∀ i, v.getD (s i) false = w.getD i false)
      (hs : ∀ k i, s i = v.length + k ↔ i = w.length + k) (i : ℕ) :
      (run (gs.map (remap s)) v).getD (s i) false = (run gs w).getD i false := by
    induction gs generalizing w v with
    | nil => exact hr i
    | cons g gs ih =>
      have eq : (remap s g).op.eval ((remap s g).inputs.map fun j => v.getD j false) =
          g.op.eval (g.inputs.map fun j => w.getD j false) := by
        simp only [remap, List.map_map, Function.comp_def, hr]
      let b := g.op.eval (g.inputs.map fun j => w.getD j false)
      change (run (gs.map (remap s)) (v ++ [_])).getD (s i) false =
        (run gs (w ++ [b])).getD i false
      rw [eq]
      apply ih
      · intro j
        by_cases h : j = w.length
        · have hh : s j = v.length := by simpa using (hs 0 j).2 (by simpa)
          rw [hh, h, snocLast, snocLast]
        · have hh : s j ≠ v.length := by simpa using mt (hs 0 j).1 (by simpa)
          rw [snocOther _ _ _ hh, snocOther _ _ _ h, hr]
      · intro k j
        simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs (1 + k) j
  have lowerBudget (p t : Circuit) (j : ℕ) (hp : FanInTwo p) (ht : FanInTwo t)
      (hj : j < 8 + p.size) (h13 : p.size + t.size ≤ 13)
      (lo : ∀ x : Fin 8 → Bool,
        let w := p.wires (List.ofFn x)
        t.eval (w ++ [w.getD j false]) = f x) :
      p.size + t.size = 13 := by
    let k := 8 + p.size
    let s := fun i : ℕ => if i = k then j else if k < i then i - 1 else i
    let C : Circuit := ⟨p.gates ++ t.gates.map (remap s), s t.output⟩
    have hC : FanInTwo C := by
      intro g hg
      change g ∈ p.gates ++ t.gates.map (remap s) at hg
      rcases List.mem_append.mp hg with hm | hm
      · exact hp g hm
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hm
        exact remapFan s g' (ht g' hg')
    have hsize : C.size = p.size + t.size := by
      change (p.gates ++ t.gates.map (remap s)).length = p.gates.length + t.gates.length
      simp only [List.length_append, List.length_map]
    by_contra hne
    apply lower
    refine ⟨C, hC, by omega, ?_⟩
    intro x
    let w := p.wires (List.ofFn x)
    have hk : w.length = k := prefixLength p x
    have hr : ∀ i, w.getD (s i) false = (w ++ [w.getD j false]).getD i false := by
      intro i
      by_cases hi : i = k
      · rw [hi, ← hk, snocLast]
        simp only [hk, s, ite_eq_left rfl]
      · rw [snocOther _ _ _ (by omega)]
        by_cases hil : k < i
        · have hd : i - 1 ≥ w.length := by omega
          simp only [s, ite_eq_right hi, ite_eq_left hil]
          rw [List.getD_eq_default _ _ hd, List.getD_eq_default _ _ (by omega)]
        · simp [s, hi, hil]
    have hs : ∀ m i, s i = w.length + m ↔ i = (w ++ [w.getD j false]).length + m := by
      intro m i
      simp only [s, hk, List.length_append, List.length_singleton]
      split_ifs <;> omega
    have hrun := runMap s t.gates (w ++ [w.getD j false]) w hr hs t.output
    change (run (p.gates ++ t.gates.map (remap s)) (List.ofFn x)).getD (s t.output) false = f x
    rw [show run (p.gates ++ t.gates.map (remap s)) (List.ofFn x) =
        run (t.gates.map (remap s)) w from List.foldl_append]
    exact hrun.trans (lo x)
  let reads := fun g : Gate => if g.op = GateOp.not then g.inputs.take 1 else g.inputs
  have step (p t : Circuit) (g : Gate) (gs : List Gate) (hgs : t.gates = g :: gs)
      (hread : 8 + p.size ∉ reads g)
      (x : Fin 8 → Bool) (b : Bool) :
      let k := 8 + p.size
      let s := fun i : ℕ => if i = k then k+1 else if i = k+1 then k else i
      let p' : Circuit := ⟨p.gates ++ [g], p.output⟩
      let t' : Circuit := ⟨gs.map (remap s), s t.output⟩
      t'.eval (p'.wires (List.ofFn x) ++ [b]) =
        t.eval (p.wires (List.ofFn x) ++ [b]) := by
    dsimp only
    let w := p.wires (List.ofFn x)
    let k := 8 + p.size
    let s := fun i : ℕ => if i = k then k+1 else if i = k+1 then k else i
    have hk : w.length = k := prefixLength p x
    let d := g.op.eval (g.inputs.map fun i => w.getD i false)
    have hd : g.op.eval (g.inputs.map fun i => (w ++ [b]).getD i false) = d := by
      by_cases hn : g.op = GateOp.not
      · change _ = g.op.eval (g.inputs.map fun i => w.getD i false)
        rw [hn]
        cases h : g.inputs with
        | nil => rfl
        | cons i is =>
          have hne : i ≠ w.length := by
            intro he
            apply hread
            simp [reads, hn, h, he, show 8 + p.size = w.length from hk.symm]
          change (!(w ++ [b]).getD i false) = (!w.getD i false)
          rw [snocOther _ _ _ hne]
      · apply congrArg g.op.eval
        apply List.map_congr_left
        intro i hi
        apply snocOther
        intro he
        apply hread
        simp only [reads, ite_eq_right hn]
        change k ∈ g.inputs
        rw [← hk, ← he]
        exact hi
    have hr : ∀ i, ((w ++ [d]) ++ [b]).getD (s i) false =
        ((w ++ [b]) ++ [d]).getD i false := by
      intro i
      have hdlen : (w ++ [d]).length = k+1 := by simp [hk]
      have hblen : (w ++ [b]).length = k+1 := by simp [hk]
      by_cases hi : i = k
      · subst i
        have hsw : s k = k+1 := by simp [s]
        rw [hsw, ← hdlen, snocLast, snocOther _ _ _ (by rw [hblen]; omega), ← hk, snocLast]
      · by_cases hi' : i = k+1
        · subst i
          have hsw : s (k+1) = k := by
            simp [s]
          rw [hsw, snocOther _ _ _ (by rw [hdlen]; omega), ← hblen, snocLast, ← hk, snocLast]
        · have hsw : s i = i := by simp [s, hi, hi']
          rw [hsw, snocOther (w ++ [d]) b i (by rwa [hdlen]),
            snocOther (w ++ [b]) d i (by rwa [hblen]),
            snocOther w d i (by rwa [hk]), snocOther w b i (by rwa [hk])]
    have hs : ∀ m i, s i = ((w ++ [d]) ++ [b]).length + m ↔
        i = ((w ++ [b]) ++ [d]).length + m := by
      intro m i
      simp only [s, hk, List.length_append, List.length_singleton]
      split_ifs <;> omega
    change (run (gs.map (remap _)) (run (p.gates ++ [g]) (List.ofFn x) ++ [b])).getD _ false =
      (run t.gates (w ++ [b])).getD _ false
    rw [hgs, show run (p.gates ++ [g]) (List.ofFn x) = w ++ [d] from List.foldl_append]
    change (run (gs.map (remap s)) ((w ++ [d]) ++ [b])).getD (s t.output) false =
      (run gs ((w ++ [b]) ++ [_])).getD t.output false
    rw [hd]
    exact runMap s gs ((w ++ [b]) ++ [d]) ((w ++ [d]) ++ [b]) hr hs t.output
  change ∀ (p t : Circuit) (j : ℕ), FanInTwo p → FanInTwo t →
    p.size + t.size ≤ 13 → 8 ≤ j → j < 8 + p.size →
    (∀ x : Fin 8 → Bool, f x = false → (x 0 || x 3) = true →
      (p.wires (List.ofFn x)).getD j false = true) →
    (∀ x : Fin 8 → Bool,
      let w := p.wires (List.ofFn x)
      t.eval (w ++ [w.getD j false]) = f x) →
    ∃ x : Fin 8 → Bool, t.eval (p.wires (List.ofFn x) ++ [false]) ≠ (f x || x 0 || x 3)
  intro p t j hp ht hb hj hlast cover low
  have hbEq := lowerBudget p t j hp ht hlast hb low
  let a := fun i : Fin 8 => decide (i = 0)
  have fa : f a = false := rfl
  have aa : (a 0 || a 3) = true := rfl
  have ha : (f a || a 0 || a 3) = true := rfl
  have monotoneRun (gs : List Gate) (w v : List Bool)
      (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (hlen : w.length = v.length)
      (hr : ∀ i, w.getD i false = true → v.getD i false = true) (i : ℕ) :
      (run gs w).getD i false = true → (run gs v).getD i false = true := by
    induction gs generalizing w v with
    | nil => exact hr i
    | cons g gs ih =>
      let gw := g.op.eval (g.inputs.map fun j => w.getD j false)
      let gv := g.op.eval (g.inputs.map fun j => v.getD j false)
      have hgate : gw = true → gv = true := by
        change g.op.eval (g.inputs.map fun j => w.getD j false) = true →
          g.op.eval (g.inputs.map fun j => v.getD j false) = true
        rcases hops g List.mem_cons_self with hand | hor
        · rw [hand]
          change (g.inputs.map fun j => w.getD j false).all id = true →
            (g.inputs.map fun j => v.getD j false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          exact fun h j hj => hr j (h j hj)
        · rw [hor]
          change (g.inputs.map fun j => w.getD j false).any id = true →
            (g.inputs.map fun j => v.getD j false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨j, hj, h⟩
          exact ⟨j, hj, hr j h⟩
      change (run gs (w ++ [gw])).getD i false = true →
        (run gs (v ++ [gv])).getD i false = true
      apply ih (w ++ [gw]) (v ++ [gv]) (fun d hd => hops d (List.mem_cons_of_mem _ hd))
      · simp only [List.length_append, List.length_singleton, hlen]
      · intro j
        by_cases hj : j = w.length
        · have hj' : j = v.length := hj.trans hlen
          rw [show (w ++ [gw]).getD j false = gw by rw [hj, snocLast],
            show (v ++ [gv]).getD j false = gv by rw [hj', snocLast]]
          exact hgate
        · rw [snocOther _ _ _ hj, snocOther _ _ _ (by rwa [← hlen])]
          exact hr j
  have withoutNot (p t : Circuit) (j : ℕ) (ht : FanInTwo t)
      (hNot : ¬ ∃ g ∈ t.gates, g.op = GateOp.not)
      (cover : ∀ x : Fin 8 → Bool, f x = false → (x 0 || x 3) = true →
        (p.wires (List.ofFn x)).getD j false = true)
      (low : ∀ x : Fin 8 → Bool,
        let w := p.wires (List.ofFn x)
        t.eval (w ++ [w.getD j false]) = f x) :
      ∃ x : Fin 8 → Bool, t.eval (p.wires (List.ofFn x) ++ [false]) ≠ (f x || x 0 || x 3) := by
    refine ⟨a, ?_⟩
    let w := p.wires (List.ofFn a)
    have hqa : w.getD j false = true := cover a fa aa
    have hlo : (run t.gates (w ++ [true])).getD t.output false = false := by
      have h := low a
      change (run t.gates (w ++ [w.getD j false])).getD t.output false = f a at h
      rwa [hqa, fa] at h
    have hpos : ∀ g ∈ t.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have hop := (ht g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact hop.imp_right fun h => h.resolve_right fun h => hNot ⟨g, hg, h⟩
    have hr : ∀ i, (w ++ [false]).getD i false = true →
        (w ++ [true]).getD i false = true := by
      intro i
      by_cases hi : i = w.length
      · rw [hi, snocLast, snocLast]
        simp
      · rw [snocOther _ _ _ hi, snocOther _ _ _ hi]
        exact id
    change (run t.gates (w ++ [false])).getD t.output false ≠ _
    rw [ha]
    intro h
    have htrue := monotoneRun t.gates (w ++ [false]) (w ++ [true]) hpos (by simp) hr t.output h
    rw [hlo] at htrue
    contradiction
  have firstReader : ∀ (m : ℕ) (p t : Circuit) (j : ℕ), t.size = m →
      FanInTwo p → FanInTwo t → p.size + t.size = 13 → 8 ≤ j → j < 8 + p.size →
      (∀ x : Fin 8 → Bool, f x = false → (x 0 || x 3) = true →
        (p.wires (List.ofFn x)).getD j false = true) →
      (∀ x : Fin 8 → Bool,
        let w := p.wires (List.ofFn x)
        t.eval (w ++ [w.getD j false]) = f x) →
      ∃ x : Fin 8 → Bool, t.eval (p.wires (List.ofFn x) ++ [false]) ≠ (f x || x 0 || x 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro p t j hm hp ht hb hj hlast cover low
      cases hgs : t.gates with
      | nil =>
        let w := p.wires (List.ofFn a)
        have hqa : w.getD j false = true := cover a fa aa
        have hlow : (w ++ [true]).getD t.output false = false := by
          have he := low a
          change (run t.gates (w ++ [w.getD j false])).getD t.output false = f a at he
          rw [hgs, hqa, fa] at he
          exact he
        by_cases he : t.output = w.length
        · rw [he, snocLast] at hlow
          contradiction
        · refine ⟨a, ?_⟩
          change (run t.gates (w ++ [false])).getD t.output false ≠ (f a || a 0 || a 3)
          rw [hgs, ha]
          change (w ++ [false]).getD t.output false ≠ true
          rw [snocOther _ _ _ he, ← snocOther w true _ he, hlow]
          decide
      | cons g gs =>
        let k := 8 + p.size
        by_cases hread : k ∈ reads g
        · have hop := (ht g (by rw [hgs]; exact List.mem_cons_self)).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          have hh : t.gates.head? = some g := by simp [hgs]
          rcases hop with h | h | h
          · by_cases hNot : ∃ g ∈ t.gates, g.op = GateOp.not
            · exact andFirst p t j hp ht hb hj hlast
                ⟨g, hh, h, by simpa [reads, h] using hread⟩ hNot cover low
            · exact withoutNot p t j ht hNot cover low
          · by_cases hNot : ∃ g ∈ t.gates, g.op = GateOp.not
            · exact orFirst p t j hp ht hb hj hlast
                ⟨g, hh, h, by simpa [reads, h] using hread⟩ hNot cover low
            · exact withoutNot p t j ht hNot cover low
          · apply notFirst p t j hp ht hb hj hlast _ cover low
            refine ⟨g, hh, h, ?_⟩
            cases hi : g.inputs with
            | nil => simp [reads, h, hi] at hread
            | cons j js =>
              have hbase : k = j := by simpa [reads, h, hi] using hread
              simpa [hi] using hbase.symm
        · let s := fun i : ℕ => if i = k then k+1 else if i = k+1 then k else i
          let p' : Circuit := ⟨p.gates ++ [g], p.output⟩
          let t' : Circuit := ⟨gs.map (remap s), s t.output⟩
          have hp' : FanInTwo p' := by
            intro g' hg
            change g' ∈ p.gates ++ [g] at hg
            rcases List.mem_append.mp hg with hin | hin
            · exact hp g' hin
            · have he := List.mem_singleton.mp hin
              subst g'
              exact ht g (by rw [hgs]; exact List.mem_cons_self)
          have ht' : FanInTwo t' := by
            intro g' hg
            obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hg
            apply remapFan
            exact ht d (by rw [hgs]; exact List.mem_cons_of_mem _ hd)
          have hpSize : p'.size = p.size + 1 := by
            change (p.gates ++ [g]).length = p.gates.length + 1
            simp only [List.length_append, List.length_singleton]
          have htSize : t'.size + 1 = t.size := by
            change (gs.map (remap s)).length + 1 = t.gates.length
            simp only [List.length_map, hgs, List.length_cons]
          have keep (x : Fin 8 → Bool) :
              (p'.wires (List.ofFn x)).getD j false = (p.wires (List.ofFn x)).getD j false := by
            let w := p.wires (List.ofFn x)
            let b := g.op.eval (g.inputs.map fun i => w.getD i false)
            change (run (p.gates ++ [g]) (List.ofFn x)).getD j false = w.getD j false
            rw [show run (p.gates ++ [g]) (List.ofFn x) = w ++ [b] from List.foldl_append]
            exact snocOther _ _ _ (by rw [prefixLength]; omega)
          have moved (x : Fin 8 → Bool) (b : Bool) :
              t'.eval (p'.wires (List.ofFn x) ++ [b]) =
                t.eval (p.wires (List.ofFn x) ++ [b]) := step p t g gs hgs hread x b
          obtain ⟨x, hx⟩ := ih t'.size (by omega) p' t' j rfl hp' ht' (by omega)
            hj (by omega) (by intro x hf h03; rw [keep]; exact cover x hf h03)
            (by intro x; dsimp only; rw [keep, moved]; exact low x)
          exact ⟨x, by rwa [moved] at hx⟩
  exact firstReader t.size p t j rfl hp ht hbEq hj hlast cover low
