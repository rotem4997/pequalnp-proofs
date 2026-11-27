import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_651_2
    (hWire : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (b : Bool), PEqualNP.MetaComplexity.FanInTwo ⟨[g],0⟩ → PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5);
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (((⟨[g],0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)))).getD p false;
      ∃ x, (if b then !(w x u) else w x u) ≠ f x)
    (hOr : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ), PEqualNP.MetaComplexity.FanInTwo ⟨[g],0⟩ → PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5);
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (((⟨[g],0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)))).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = false → w x u = false ∧ w x v = false) →
      ∃ x, f x = true ∧ w x u = false ∧ w x v = false)
    (hAnd : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ), PEqualNP.MetaComplexity.FanInTwo ⟨[g],0⟩ → PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 17 →
      let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5);
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (D.wires (((⟨[g],0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)))).getD p false;
      (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
      (∀ x, f x = true → w x u = true ∧ w x v = true) →
      ∃ x, f x = false ∧ w x u = true ∧ w x v = true)
    : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  classical
  let f := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  rintro ⟨C,ok,small,correct⟩
  change ∀ x, C.eval (List.ofFn x) = f x at correct
  have nonconst (b : Bool) : ¬ ∀ x, f x = b := by
    intro h
    have a : false=b := h (fun _ => false)
    have z : true=b := h (fun _ => true)
    exact Bool.noConfusion (a.trans z.symm)
  have snoc (l : List Bool) (o : ℕ) (b : Bool) (h : o ≠ l.length) :
      (l++[b]).getD o false = l.getD o false := by
    by_cases earlier : o < l.length
    · exact List.getD_append _ _ _ _ earlier
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
  have listlen (l : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
      (((⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires l)).length = l.length+gs.length := by
    induction gs generalizing l with
    | nil => change l.length=l.length+0;omega
    | cons g tail ih =>
      change (((⟨tail,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (l++[_]))).length = _
      rw [ih];simp;omega
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil =>
    let g : PEqualNP.CircuitLowerBounds.Gate := ⟨.or,[]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[],0⟩
    obtain ⟨x,h⟩ := hWire g D o false (by
      intro h hh;obtain rfl : h=g := by simpa using hh
      change PEqualNP.CircuitLowerBounds.GateOp.or ∈ ({.and,.or,.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ 0≤2
      simp) (by intro h hh;change h ∈ ([] : List PEqualNP.CircuitLowerBounds.Gate) at hh;cases hh) (by decide)
    apply h
    change ((List.ofFn x)++[false]).getD o false = f x
    have e := correct x
    change (List.ofFn x).getD o false = _ at e
    by_cases k : o=(List.ofFn x).length
    · rw [k,List.getD_eq_default _ _ (by omega)] at e
      rw [k];simpa using e
    · exact (snoc _ _ _ k).trans e
  | cons g gs =>
    have gOk : PEqualNP.MetaComplexity.FanInTwo ⟨[g],0⟩ := by
      intro h hh;obtain rfl : h=g := by simpa using hh
      exact ok _ List.mem_cons_self
    let init := fun (x : Fin 10 → Bool) => (⟨[g],0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)
    have gsOk (v : PEqualNP.CircuitLowerBounds.Gate) (hv : v ∈ gs) := ok v (List.mem_cons_of_mem _ hv)
    have size : gs.length+1 ≤ 19 := small
    by_cases short : gs.length ≤ 17
    · let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs,o⟩
      obtain ⟨x,wrong⟩ := hWire g D o false gOk gsOk short
      exact wrong (correct x)
    · have nonempty : gs ≠ [] := by rintro rfl;simp at short
      let z := gs.getLast nonempty
      let mid := gs.dropLast
      have e : mid++[z] = gs := List.dropLast_concat_getLast nonempty
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨mid,0⟩
      have legal : PEqualNP.MetaComplexity.FanInTwo D := fun h hh => gsOk h (e ▸ List.mem_append_left _ hh)
      have budget : D.size ≤ 17 := by change gs.dropLast.length ≤ 17;rw [List.length_dropLast];omega
      let W := fun x => D.wires (init x)
      let w := fun (x : Fin 10 → Bool) (p : ℕ) => (W x).getD p false
      have val (x : Fin 10 → Bool) : (W x ++ [z.op.eval (z.inputs.map (w x))]).getD o false = f x := by
        have orig := correct x
        change (gs.foldl _ (init x)).getD o false = _ at orig
        rw [← e,List.foldl_append] at orig
        exact orig
      have len (x : Fin 10 → Bool) : (W x).length = 11+mid.length := by
        have l := listlen (init x) mid
        have k := listlen (List.ofFn x) [g]
        change (init x).length = _ at k;simpa [W,D,k] using l
      have noWire (p : ℕ) (b : Bool) : ¬ ∀ x, (if b then !(w x p) else w x p) = f x := by
        obtain ⟨x,bad⟩ := hWire g D p b gOk legal budget;exact fun h => bad (h x)
      by_cases last : o=11+mid.length
      · have out (x : Fin 10 → Bool) : z.op.eval (z.inputs.map (w x)) = f x := by
          have h := val x;rw [last,← len x] at h;simpa using h
        have zop := gsOk z (e ▸ List.mem_append_right _ (List.mem_singleton.mpr rfl))
        change z.op ∈ _ ∧ z.inputs.length ≤ 2 at zop
        have bound := zop.2
        have lor (u v : ℕ) (join : ∀ x, (w x u || w x v) = f x) : False := by
          by_cases l : ∃ x, w x u = true ∧ w x v = false
          · by_cases r : ∃ x, w x u = false ∧ w x v = true
            · obtain ⟨x,hf,hu,hv⟩ := hOr g D u v gOk legal budget l r (by
                intro x hx;change f x = false at hx;change w x u=false ∧ w x v=false;have e := join x;rw [hx] at e;simpa using e)
              change f x=true at hf;change w x u=false at hu;change w x v=false at hv
              have e := join x;rw [hu,hv,hf] at e;contradiction
            · apply noWire u false;intro x;rw [← join];cases a : w x u <;> cases b : w x v <;> simp <;> exact r ⟨x,a,b⟩
          · apply noWire v false;intro x;rw [← join];cases a : w x u <;> cases b : w x v <;> simp <;> exact l ⟨x,a,b⟩
        have land (u v : ℕ) (join : ∀ x, (w x u && w x v) = f x) : False := by
          by_cases l : ∃ x, w x u = true ∧ w x v = false
          · by_cases r : ∃ x, w x u = false ∧ w x v = true
            · obtain ⟨x,hf,hu,hv⟩ := hAnd g D u v gOk legal budget l r (by
                intro x hx;change f x = true at hx;change w x u=true ∧ w x v=true;have e := join x;rw [hx] at e;simpa using e)
              change f x=false at hf;change w x u=true at hu;change w x v=true at hv
              have e := join x;rw [hu,hv,hf] at e;contradiction
            · apply noWire v false;intro x;rw [← join];cases a : w x u <;> cases b : w x v <;> simp <;> exact r ⟨x,a,b⟩
          · apply noWire u false;intro x;rw [← join];cases a : w x u <;> cases b : w x v <;> simp <;> exact l ⟨x,a,b⟩
        rcases zop.1 with hop | hop | hop
        all_goals change z.op = _ at hop
        all_goals cases ins : z.inputs with
        | nil => exact nonconst _ (fun x => (by simpa only [hop,ins,List.map_nil] using (out x).symm))
        | cons p ps => cases ps with
          | nil => first
            | apply noWire p false;intro x;rw [← out x,hop,ins];simp only [List.map_cons,List.map_nil];cases w x p <;> rfl
            | apply noWire p true;intro x;rw [← out x,hop,ins];simp only [List.map_cons,List.map_nil];cases w x p <;> rfl
          | cons q qs => cases qs with
            | nil => first
              | apply land p q;intro x;have h := out x;rw [hop,ins] at h;change (w x p && (w x q && true)) = f x at h;simpa only [Bool.and_true] using h
              | apply lor p q;intro x;have h := out x;rw [hop,ins] at h;change (w x p || (w x q || false)) = f x at h;simpa only [Bool.or_false] using h
              | apply noWire p true;intro x;have h := out x;rw [hop,ins] at h;exact h
            | cons r rs => simp [ins] at bound
      · apply noWire o false;intro x
        exact (snoc _ _ _ (by simpa [len] using last)).symm.trans (val x)
