import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1951

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

theorem difn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ifn (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ifn (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (fd stpF W1 gs).getD i false = true → (fd stpF W2 gs).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa [fd] using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    have := ih (W1 ++ [stpF g W1]) (W2 ++ [stpF g W2]) (by simp [hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) (by
        intro i
        simp only [getD_snoc, hl]
        split_ifs
        · unfold stpF
          rcases hop g List.mem_cons_self with ha | ho
          · rw [ev_and g _ ha, ev_and g _ ha]
            intro h k hk
            exact H k (h k hk)
          · rw [ev_or g _ ho, ev_or g _ ho]
            rintro ⟨k, hk, h⟩
            exact ⟨k, hk, H k h⟩
        · exact H i)
    simpa only [fd, List.foldl_cons] using this

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem app_getD {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) :
    (List.ofFn (Fin.append x y)).getD i false =
      if h : i < n then x ⟨i, h⟩ else if h2 : i - n < m then y ⟨i - n, h2⟩ else false := by
  rw [ofFn_getD]
  by_cases h : i < n
  · rw [difp (by omega), difp h]
    exact Fin.append_left x y ⟨i, h⟩
  · rw [difn h]
    by_cases h2 : i - n < m
    · rw [difp (by omega), difp h2]
      have hh : (⟨i, by omega⟩ : Fin (n + m)) = Fin.natAdd n ⟨i - n, h2⟩ := by
        apply Fin.ext
        show i = n + (i - n)
        omega
      rw [hh, Fin.append_right]
    · rw [difn (by omega), difn h2]

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem wmono (N : ℕ) (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : Fin N → Bool) (hx : ∀ a, x a = true → x' a = true) (y : Fin N → Bool) (i : ℕ)
    (h : (C.wires (List.ofFn (Fin.append x y))).getD i false = true) :
    (C.wires (List.ofFn (Fin.append x' y))).getD i false = true := by
  rw [wires_fd] at h ⊢
  refine mono C.gates _ _ (by simp) hg ?_ i h
  intro k
  rw [app_getD, app_getD]
  split_ifs
  · exact hx _
  · exact id
  · exact id

theorem rmono {α : Type} {r q : α → α → Prop} (hq : ∀ a b, r a b → q a b) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen q a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hq _ _ hbc)

end PEqualNP.Outside.L_meta_1951

theorem PEqualNP.Outside.L_meta_1951 : (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → ∀ (N240 : ℕ) (I240 : Fin N240 → Fin N240 → Prop) [DecidableRel I240] (C240 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g240 ∈ C240.gates, (g240.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g240.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g240.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N240 + N240) C240) → (∀ j240 < C240.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240 0 = 0) ∨ (∀ h240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240 0 = 0)) → (∀ p240 p240x1 w240 w240x1 : Fin N240, p240 ≠ p240x1 → w240 ≠ w240x1 → I240 p240 w240 → I240 p240x1 w240 → I240 p240 w240x1 → I240 p240x1 w240x1 → False) → (∃ p240x2 w240x2 : Fin N240, I240 p240x2 w240x2) → (∀ p240x3 w240x3 : Fin N240, I240 p240x3 w240x3 → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append (fun a240 : Fin N240 => decide (a240 = p240x3)) (fun a240x1 : Fin N240 => decide (a240x1 = w240x3))) = true) → (∀ x240 y240 : Fin N240 → Bool, (Finset.univ.filter (fun l240 : Fin N240 => y240 l240 = true)).card ≤ 1 → (¬ ∃ p240x4 w240x4 : Fin N240, I240 p240x4 w240x4 ∧ x240 p240x4 = true ∧ y240 w240x4 = true) → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append x240 y240) = false) → ∀ mixed240 : ℕ → Prop, mixed240 = (fun i240x1 : ℕ => 0 < (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD i240x1 0 ∧ 0 < (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x1 0) → ∀ cone240 : ℕ → Prop, cone240 = (fun j240x1 : ℕ => j240x1 < C240.gates.length ∧ mixed240 (N240 + N240 + j240x1) ∧ Relation.ReflTransGen (fun a240x2 b240 : ℕ => a240x2 < b240 ∧ ∃ f240 : Fin C240.gates.length, b240 = N240 + N240 + f240.val ∧ a240x2 ∈ (C240.gates.get f240).inputs) (N240 + N240 + j240x1) C240.output) → ∀ gok240 : (Fin N240 → Bool) → ℕ → Prop, gok240 = (fun (x240x1 : Fin N240 → Bool) (j240x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i240x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x2 0 = 0 ∧ (C240.wires (List.ofFn (Fin.append x240x1 (fun u240 : Fin N240 => false)))).getD i240x2 false = true) → ∀ step240 : (Fin N240 → Bool) → ℕ → ℕ → Prop, step240 = (fun (x240x2 : Fin N240 → Bool) (j240x3 j240x4 : ℕ) => cone240 j240x4 ∧ N240 + N240 + j240x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x4).inputs ∧ gok240 x240x2 j240x4) → ∀ slot240 : ℕ → ℕ → Prop, slot240 = (fun h240x1 j240x5 : ℕ => cone240 j240x5 ∧ h240x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x5).inputs ∧ (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240x1 0 = 0) → ∀ lh240 : ℕ → Fin N240 → Prop, lh240 = (fun (h240x2 : ℕ) (w240x5 : Fin N240) => (C240.wires (List.ofFn (Fin.append (fun u240x1 : Fin N240 => false) (fun a240x3 : Fin N240 => decide (a240x3 = w240x5))))).getD h240x2 false = true) → ∀ (h240x3 j240x6 j240x7 : ℕ) (w240x6 p240x5 : Fin N240), slot240 h240x3 j240x6 → lh240 h240x3 w240x6 → gok240 (fun a240x4 : Fin N240 => decide (¬ I240 a240x4 w240x6)) j240x6 → Relation.ReflTransGen (step240 (fun a240x5 : Fin N240 => decide (¬ I240 a240x5 w240x6))) j240x6 j240x7 → ¬ I240 p240x5 w240x6 → ∀ j240x8 : ℕ, N240 + N240 + j240x8 = C240.output → ¬ Relation.ReflTransGen (step240 (fun a240x6 : Fin N240 => decide (a240x6 = p240x5))) j240x7 j240x8 := by
  intro H N I _ C h1 hkm hno4 hedge htrue hfalse mixed hmixed cone hcone gok hgok step hstep slot hslot
    lh hlh h j0 j w p hsl hlhw hg0 hch1 hpw jout hout hch2
  have H4 := (H N I C h1 hkm hno4 hedge htrue hfalse mixed hmixed cone hcone gok hgok step hstep
    _ rfl slot hslot _ rfl lh hlh _ rfl _ rfl _ rfl _ rfl).2.2.2.1
  subst hmixed hcone hgok hstep hslot hlh
  refine H4 h j0 w hsl hlhw ⟨hsl.1, hg0, jout, hout, hch1.trans ?_⟩
  refine PEqualNP.Outside.L_meta_1951.rmono ?_ hch2
  intro a b hab
  obtain ⟨hc, hm, hg⟩ := hab
  refine ⟨hc, hm, ?_⟩
  rcases hg with hg | ⟨i, hi, hd, hv⟩
  · exact Or.inl hg
  · refine Or.inr ⟨i, hi, hd, ?_⟩
    refine PEqualNP.Outside.L_meta_1951.wmono N C (fun g hg => (h1.1 g hg).1) _ _ ?_ _ i hv
    intro a ha
    have : a = p := by simpa using ha
    subst this
    simpa using hpw
