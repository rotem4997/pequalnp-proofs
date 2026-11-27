import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two variants share every opcode and unswitched pin. A pair of Boolean
-- marks on each original pin records exactly which of the two variants rewires it.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2016_726
    (reify :
      let R := fun (a b : ℕ) (g h : Gate) => g.op = h.op ∧
        List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs
      let G := fun (k : Option Bool) (g : GateOp × List (ℕ × Bool × Bool)) =>
        Gate.mk g.1 (g.2.map fun v => Option.elim k v.1 (fun b => cond (cond b v.2.2 v.2.1) 0 (v.1+1)))
      ∀ (c : List Gate) (d : Bool → List Gate) (a b : Bool → ℕ),
        (∀ k, List.Forall₂ (R (a k) (b k)) c (d k)) →
        ∃ (p : List (GateOp × List (ℕ × Bool × Bool))),
          p.map (G none) = c.map (fun g => Gate.mk g.op (g.inputs.map (min 18))) ∧
          (∀ k, p.map (G (some k)) = (d k).map (fun g => Gate.mk g.op (g.inputs.map (min 19)))) ∧
          ∀ k g, g ∈ p → ∀ v ∈ g.2, (cond k v.2.2 v.2.1) = true →
            v.1 = min 18 (a k) ∨ v.1 = min 18 (b k))
    (exclude :
      let G := fun (k : Option Bool) (g : GateOp × List (ℕ × Bool × Bool)) =>
        Gate.mk g.1 (g.2.map fun v => Option.elim k v.1 (fun b => cond (cond b v.2.2 v.2.1) 0 (v.1+1)))
      let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e =>
        x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      ∀ (p : List (GateOp × List (ℕ × Bool × Bool))) (o : ℕ) (a b : Bool → ℕ),
        p.length = 11 → o < 18 → FanInTwo ⟨p.map (G none),o⟩ →
        (∀ k g, g ∈ p → ∀ v ∈ g.2, v.1 ≤ 18 ∧
          ((cond k v.2.2 v.2.1) = true → v.1 = a k ∨ v.1 = b k)) →
        circuitFun 7 ⟨p.map (G none),o⟩ = F →
        (∀ (k : Bool) (x : Fin 7 → Bool), (⟨p.map (G (some k)),o+1⟩ : Circuit).eval (true :: List.ofFn x) =
          (F x || (cond k (x 0 || x 3) (x 2)))) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  let clipGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (min n)⟩

  have unchanged (n : ℕ) (gs : List Gate) (out : ℕ) (w : List Bool)
      (h : w.length + gs.length ≤ n) :
      (⟨gs.map (clipGate n),out⟩ : Circuit).wires w = (⟨gs,out⟩ : Circuit).wires w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      have agree (i : ℕ) : w.getD (min n i) false = w.getD i false := by
        by_cases hi : i ≤ n
        · rw [min_eq_right hi]
        · rw [min_eq_left (by omega), List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have eq : (clipGate n g).op.eval ((clipGate n g).inputs.map fun i => w.getD i false) = v := by
        simp only [clipGate, v, List.map_map, Function.comp_def, agree]
      change (⟨gs.map (clipGate n),out⟩ : Circuit).wires (w ++ [_]) =
        (⟨gs,out⟩ : Circuit).wires (w ++ [v])
      rw [eq]
      exact ih (w ++ [v]) (by simp at h ⊢; omega)

  have wiresLength (gs : List Gate) (out : ℕ) (w : List Bool) :
      ((⟨gs,out⟩ : Circuit).wires w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((⟨gs,out⟩ : Circuit).wires (w ++ [_])).length = _
      rw [ih]
      simp
      omega
  have clipEval (n : ℕ) (C : Circuit) (w : List Bool) (h : w.length + C.size ≤ n) :
      (⟨C.gates.map (clipGate n),C.output⟩ : Circuit).eval w = C.eval w := by
    change ((⟨C.gates.map (clipGate n),C.output⟩ : Circuit).wires w).getD C.output false =
      (C.wires w).getD C.output false
    rw [unchanged n C.gates C.output w h]

  have clipFan (n : ℕ) (C : Circuit) (h : FanInTwo C) : FanInTwo ⟨C.gates.map (clipGate n),C.output⟩ := by
    intro g hg
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hg
    exact ⟨(h h' hh').1, by simpa [clipGate] using (h h' hh').2⟩
  intro graph
  rintro ⟨c, fan, len, base, ext⟩
  choose a b D out ports vals using ext
  let G := fun (k : Option Bool) (g : GateOp × List (ℕ × Bool × Bool)) =>
    Gate.mk g.1 (g.2.map fun v => Option.elim k v.1 (fun b => cond (cond b v.2.2 v.2.1) 0 (v.1+1)))
  let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e =>
    x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  have low (x : Fin 7 → Bool) : graph (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = F x := by
    exact (by decide +kernel : ∀ x : Fin 7 → Bool,
      graph (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = F x) x
  have high : ∀ (k : Bool) (x : Fin 7 → Bool),
      graph (Fin.insertNth 0 k (Fin.insertNth 3 (!k) x)) = (F x || cond k (x 0 || x 3) (x 2)) := by
    decide +kernel
  change c.gates.length = 11 at len
  have outputValid : c.output < 18 := by
    by_contra! hbad
    let x : Fin 7 → Bool := fun _ => true
    have zero : c.eval (List.ofFn x) = false := by
      change (c.wires (List.ofFn x)).getD c.output false = false
      apply List.getD_eq_default
      change ((⟨c.gates,c.output⟩ : Circuit).wires (List.ofFn x)).length ≤ c.output
      rw [wiresLength]
      simp only [List.length_ofFn]
      omega
    have yes := (congrFun base x).trans (low x)
    change c.eval (List.ofFn x) = true at yes
    rw [zero] at yes
    contradiction
  obtain ⟨p, clips, mixed, flags⟩ := reify c.gates (fun k => (D k).gates) a b ports
  change p.map (G none) = c.gates.map (clipGate 18) at clips
  change (∀ k, p.map (G (some k)) = (D k).gates.map (clipGate 19)) at mixed
  have pl : p.length = 11 := by
    have eq := congrArg List.length clips
    simpa [len] using eq
  have bounded (g : GateOp × List (ℕ × Bool × Bool)) (hg : g ∈ p) (v : ℕ × Bool × Bool) (hv : v ∈ g.2) : v.1 ≤ 18 := by
    have hit : G none g ∈ c.gates.map (clipGate 18) :=
      clips ▸ List.mem_map_of_mem hg
    obtain ⟨g',_,same⟩ := List.mem_map.mp hit
    have pin : v.1 ∈ (G none g).inputs := List.mem_map_of_mem hv
    rw [← same] at pin
    obtain ⟨w,_,eq⟩ := List.mem_map.mp pin
    rw [← eq]
    exact min_le_left _ _
  apply exclude p c.output (fun k => min 18 (a k)) (fun k => min 18 (b k)) pl outputValid
  · rw [clips]
    exact clipFan 18 c fan
  · intro k g hg v hv
    exact ⟨bounded g hg v hv, flags k g hg v hv⟩
  · funext x
    change (⟨p.map (G none),c.output⟩ : Circuit).eval (List.ofFn x) = F x
    rw [clips, clipEval 18 c _ (by change (List.ofFn x).length + c.gates.length ≤ 18; simp [len])]
    exact (congrFun base x).trans (low x)
  · intro k x
    have gatesLen : (D k).gates.length = 11 := (ports k).length_eq.symm.trans len
    rw [mixed k, ← out k, clipEval 19 (D k) _ (by change (true :: List.ofFn x).length + (D k).gates.length ≤ 19; simp [gatesLen])]
    exact (vals k x).trans (high k x)
