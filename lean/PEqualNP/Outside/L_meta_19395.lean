import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19395_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stp]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl stp x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [stp]; omega), stp, getD_snoc, if_pos h]

theorem oe {n m : ℕ} (u : Fin n) (v : Fin m) (w : ℕ) :
    (oneEach u v).getD w false = true ↔ (w = u.val ∨ w = n + v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs with h1 h2 <;> simp [Fin.ext_iff] <;> omega

def chain (b a : ℕ) : List ℕ → List Gate
  | [] => []
  | c :: L => ⟨GateOp.or, [a, c]⟩ :: chain (b + 1) b L

def last (b a : ℕ) : List ℕ → ℕ
  | [] => a
  | _ :: L => last (b + 1) b L

theorem chain_good (b a : ℕ) (L : List ℕ) :
    ∀ g ∈ chain b a L, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction L generalizing b a with
  | nil => simp [chain]
  | cons c L ih =>
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact ih _ _ g hg

theorem chain_len (b a : ℕ) (L : List ℕ) : (chain b a L).length = L.length := by
  induction L generalizing b a with
  | nil => rfl
  | cons c L ih => simp [chain, ih]

theorem last_lt (L : List ℕ) : ∀ b a : ℕ, a < b → last b a L < b + L.length := by
  induction L with
  | nil => intro b a h; simpa [last] using h
  | cons c L ih => intro b a _; have := ih (b + 1) b (by omega); simp [last]; omega

theorem anyc {f g : ℕ → Bool} : ∀ (L : List ℕ), (∀ c ∈ L, f c = g c) → L.any f = L.any g
  | [], _ => rfl
  | c :: L, h => by
    rw [List.any_cons, List.any_cons, h c (by simp), anyc L fun c' h' => h c' (by simp [h'])]

theorem chain_val (L : List ℕ) : ∀ (x : List Bool) (a : ℕ), (∀ c ∈ L, c < x.length) →
    a < x.length →
    ((chain x.length a L).foldl stp x).getD (last x.length a L) false =
      (x.getD a false || L.any fun c => x.getD c false) := by
  induction L with
  | nil => intro x a _ ha; simp [chain, last]
  | cons c L ih =>
    intro x a hc ha
    have hl : (stp x ⟨GateOp.or, [a, c]⟩).length = x.length + 1 := by simp [stp]
    have hc' : ∀ c' ∈ L, c' < (stp x ⟨GateOp.or, [a, c]⟩).length := fun c' h => by
      have := hc c' (by simp [h]); omega
    have h2 := ih (stp x ⟨GateOp.or, [a, c]⟩) x.length hc' (by omega)
    simp only [chain, last, List.foldl_cons]
    rw [hl] at h2
    have : ∀ c' ∈ L, (stp x ⟨GateOp.or, [a, c]⟩).getD c' false = x.getD c' false :=
      fun c' h => by rw [stp, getD_snoc, if_pos (hc c' (by simp [h]))]
    rw [h2, anyc L this, stp, getD_snoc, if_neg (lt_irrefl _), if_pos rfl]
    simp [GateOp.eval, Bool.or_assoc]

def rl (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem copy (f : ℕ → ℕ) (n0 B : ℕ) (h2 : ∀ k, n0 ≤ k → f k = B + (k - n0)) :
    ∀ (gs : List Gate) (S W : List Bool), n0 ≤ S.length → W.length + n0 = S.length + B →
    (∀ k < n0, f k < B ∨ W.length + gs.length ≤ f k) →
    (∀ k, W.getD (f k) false = S.getD k false) →
    ∀ k, ((gs.map (rl f)).foldl stp W).getD (f k) false = (gs.foldl stp S).getD k false
  | [], S, W, _, _, _, hI => by simpa using hI
  | g :: gs, S, W, hS, hL, h1, hI => by
    have hv : g.op.eval ((g.inputs.map f).map fun i => W.getD i false) =
        g.op.eval (g.inputs.map fun i => S.getD i false) := by
      rw [List.map_map]; congr 1; exact List.map_congr_left (fun i _ => hI i)
    have e1 : stp W (rl f g) = W ++ [g.op.eval (g.inputs.map fun i => S.getD i false)] := by
      show W ++ [g.op.eval ((g.inputs.map f).map fun i => W.getD i false)] = _
      rw [hv]
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e1]
    apply copy f n0 B h2 gs
    · simp [stp]; omega
    · simp [stp]; omega
    · intro k hk
      rcases h1 k hk with h | h
      · exact Or.inl h
      · right; simp at h ⊢; omega
    · intro k
      rw [stp, getD_snoc, getD_snoc]
      rcases lt_trichotomy k S.length with hk | hk | hk
      · have hne : f k ≠ W.length := by
          by_cases hk0 : k < n0
          · rcases h1 k hk0 with h | h <;> (try simp only [List.length_cons] at h) <;> omega
          · rw [h2 k (by omega)]; omega
        rw [if_pos hk, ← hI k]
        by_cases ha : f k < W.length
        · rw [if_pos ha]
        · rw [if_neg ha, if_neg hne, getD_ge _ _ (by omega)]
      · subst hk
        have : f S.length = W.length := by rw [h2 _ hS]; omega
        rw [this]; simp
      · rw [h2 k (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]

end PEqualNP.Outside.L_meta_19395_aux

open PEqualNP.Outside.L_meta_19395_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19395 : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (U : Finset (Fin n)) (W : Finset (Fin m)) (u0 : Fin n) (v0 : Fin m), u0 ∈ U → v0 ∈ W → (∀ u ∈ U, ∀ v : Fin m, A u v = A u0 v) → (∀ v ∈ W, ∀ u : Fin n, A u v = A u v0) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ (u : Fin n) (v : Fin m), (u ∉ U ∨ u = u0) → (v ∉ W ∨ v = v0) → C.eval (PEqualNP.Represents.oneEach u v) = A u v) → PEqualNP.Represents.RepSizeAtMost A (s + (U.card - 1) + (W.card - 1)) := by
  intro n m s A U W u0 v0 hu0 hv0 hU hW ⟨C, hM, hs, hC⟩
  let N := n + m
  let LU : List ℕ := (U.erase u0).toList.map (fun u => u.val)
  let LW : List ℕ := (W.erase v0).toList.map (fun v => n + v.val)
  let aU := last N u0.val LU
  let aW := last (N + LU.length) (n + v0.val) LW
  let B := N + LU.length + LW.length
  let f : ℕ → ℕ := fun k => if k = u0.val then aU else if k = n + v0.val then aW else
    if k < N then (if k ∈ LU ∨ k ∈ LW then B + C.gates.length else k) else B + (k - N)
  have hLU : LU.length = U.card - 1 := by simp [LU, Finset.card_erase_of_mem hu0]
  have hLW : LW.length = W.card - 1 := by simp [LW, Finset.card_erase_of_mem hv0]
  have mLU : ∀ c, c ∈ LU ↔ ∃ a ∈ U, a ≠ u0 ∧ a.val = c := by
    intro c; simp only [LU, List.mem_map, Finset.mem_toList, Finset.mem_erase]
    exact ⟨fun ⟨a, ⟨h1, h2⟩, h3⟩ => ⟨a, h2, h1, h3⟩, fun ⟨a, h2, h1, h3⟩ => ⟨a, ⟨h1, h2⟩, h3⟩⟩
  have mLW : ∀ c, c ∈ LW ↔ ∃ a ∈ W, a ≠ v0 ∧ n + a.val = c := by
    intro c; simp only [LW, List.mem_map, Finset.mem_toList, Finset.mem_erase]
    exact ⟨fun ⟨a, ⟨h1, h2⟩, h3⟩ => ⟨a, h2, h1, h3⟩, fun ⟨a, h2, h1, h3⟩ => ⟨a, ⟨h1, h2⟩, h3⟩⟩
  have hu0n := u0.isLt
  have hv0m := v0.isLt
  have hLUb : ∀ c ∈ LU, c < n := by
    intro c hc; obtain ⟨a, -, -, rfl⟩ := (mLU c).1 hc; exact a.isLt
  have hLWb : ∀ c ∈ LW, n ≤ c ∧ c < N := by
    intro c hc; obtain ⟨a, -, -, rfl⟩ := (mLW c).1 hc; have := a.isLt; omega
  have haU : aU < N + LU.length := last_lt LU N u0.val (by omega)
  have haW : aW < B := last_lt LW (N + LU.length) (n + v0.val) (by omega)
  refine ⟨⟨chain N u0.val LU ++ chain (N + LU.length) (n + v0.val) LW ++ C.gates.map (rl f),
    f C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with (hg | hg) | ⟨g0, hg0, rfl⟩
    · have := chain_good _ _ _ g hg; simp [this.1, this.2]
    · have := chain_good _ _ _ g hg; simp [this.1, this.2]
    · obtain ⟨h1, h2⟩ := hM g0 hg0
      exact ⟨h1, by simpa [rl] using h2⟩
  · simp only [Circuit.size, List.length_append, chain_len, List.length_map]
    simp only [Circuit.size] at hs
    omega
  · intro u v
    let u' := if u ∈ U then u0 else u
    let v' := if v ∈ W then v0 else v
    have hA : A u v = A u' v' := by
      by_cases hu : u ∈ U <;> by_cases hv : v ∈ W <;> simp only [u', v', hu, hv, if_true, if_false]
      · rw [hU u hu, hW v hv]
      · rw [hU u hu]
      · rw [hW v hv]
    have hc := hC u' v' (by by_cases hu : u ∈ U <;> simp [u', hu])
      (by by_cases hv : v ∈ W <;> simp [v', hv])
    rw [hA, ← hc]
    have hud : (u ∈ U ∧ u' = u0) ∨ (u ∉ U ∧ u' = u) := by by_cases hu : u ∈ U <;> simp [u', hu]
    have hvd : (v ∈ W ∧ v' = v0) ∨ (v ∉ W ∧ v' = v) := by by_cases hv : v ∈ W <;> simp [v', hv]
    clear_value u' v'
    have hun := u.isLt
    have hvm := v.isLt
    have hun' := u'.isLt
    have hvm' := v'.isLt
    simp only [Circuit.eval, Circuit.wires]
    change ((chain N u0.val LU ++ chain (N + LU.length) (n + v0.val) LW ++ C.gates.map (rl f)).foldl
      stp (oneEach u v)).getD (f C.output) false = (C.gates.foldl stp (oneEach u' v')).getD C.output false
    have hx : (oneEach u v).length = N := by simp [oneEach, N]
    have hx' : (oneEach u' v').length = N := by simp [oneEach, N]
    rw [List.foldl_append, List.foldl_append]
    obtain ⟨x1, hx1⟩ : ∃ x1, (chain N u0.val LU).foldl stp (oneEach u v) = x1 := ⟨_, rfl⟩
    obtain ⟨Wp, hWp⟩ : ∃ Wp, (chain (N + LU.length) (n + v0.val) LW).foldl stp x1 = Wp := ⟨_, rfl⟩
    have hl1 : x1.length = N + LU.length := by rw [← hx1, len, hx, chain_len]
    have hlW : Wp.length = B := by rw [← hWp, len, hl1, chain_len]
    have vU : x1.getD aU false = ((oneEach u v).getD u0.val false ||
        LU.any fun c => (oneEach u v).getD c false) := by
      have := chain_val LU (oneEach u v) u0.val (fun c hc => by have := hLUb c hc; omega) (by omega)
      rw [hx] at this; rw [← hx1]; exact this
    have p1 : ∀ i < N, x1.getD i false = (oneEach u v).getD i false := by
      intro i hi; rw [← hx1]; exact pre _ _ _ (by omega)
    have vW : Wp.getD aW false = (x1.getD (n + v0.val) false ||
        LW.any fun c => x1.getD c false) := by
      have := chain_val LW x1 (n + v0.val) (fun c hc => by have := hLWb c hc; omega) (by omega)
      rw [hl1] at this; rw [← hWp]; exact this
    have p2 : ∀ i < N + LU.length, Wp.getD i false = x1.getD i false := by
      intro i hi; rw [← hWp]; exact pre _ _ _ (by omega)
    rw [hx1, hWp]
    refine copy f N B (fun k hk => by simp only [f]; rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]) C.gates (oneEach u' v') Wp (by omega) (by omega) ?_ ?_ C.output
    · intro k hk
      simp only [f]
      split_ifs <;> omega
    · intro k
      simp only [f]
      split_ifs with h1 h2 h3 h4
      · subst h1
        rw [p2 _ haU, vU]
        rcases hud with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;> rw [hu'] <;> apply Bool.eq_iff_iff.2 <;>
          simp only [Bool.or_eq_true, List.any_eq_true, oe]
        · refine ⟨fun _ => Or.inl trivial, fun _ => ?_⟩
          by_cases he : u = u0
          · exact Or.inl (Or.inl (by rw [he]))
          · exact Or.inr ⟨u.val, (mLU _).2 ⟨u, hu, he, rfl⟩, Or.inl rfl⟩
        · have hne' : u0.val ≠ u.val := fun e => hu (Fin.ext e ▸ hu0)
          constructor
          · rintro ((h | h) | ⟨c, hc, h | h⟩)
            · exact absurd h hne'
            · omega
            · obtain ⟨a, ha, -, rfl⟩ := (mLU c).1 hc; exact (hu (by rwa [← Fin.ext h])).elim
            · have := hLUb c hc; omega
          · rintro (h | h)
            · exact absurd h hne'
            · omega
      · subst h2
        rw [vW, p1 _ (by omega), anyc LW (fun c hc => p1 c (hLWb c hc).2)]
        rcases hvd with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;> rw [hv'] <;> apply Bool.eq_iff_iff.2 <;>
          simp only [Bool.or_eq_true, List.any_eq_true, oe]
        · refine ⟨fun _ => Or.inr trivial, fun _ => ?_⟩
          by_cases he : v = v0
          · exact Or.inl (Or.inr (by rw [he]))
          · exact Or.inr ⟨n + v.val, (mLW _).2 ⟨v, hv, he, rfl⟩, Or.inr rfl⟩
        · have hne' : v0.val ≠ v.val := fun e => hv (Fin.ext e ▸ hv0)
          constructor
          · rintro ((h | h) | ⟨c, hc, h | h⟩)
            · omega
            · exact absurd (by omega) hne'
            · have := (hLWb c hc).1; omega
            · obtain ⟨a, ha, -, rfl⟩ := (mLW c).1 hc
              exact (hv (by rwa [← Fin.ext (by omega : a.val = v.val)])).elim
          · rintro (h | h)
            · omega
            · exact absurd (by omega) hne'
      · rw [getD_ge _ _ (by omega)]
        symm; rw [Bool.eq_false_iff]; intro h; rw [oe] at h
        rcases h4 with hk | hk
        · obtain ⟨a, ha, hne, rfl⟩ := (mLU k).1 hk
          rcases h with h | h
          · rcases hud with ⟨-, hu'⟩ | ⟨hu, hu'⟩ <;> rw [hu'] at h
            · exact hne (Fin.ext h)
            · exact hu (by rwa [← Fin.ext h])
          · have := a.isLt; omega
        · obtain ⟨a, ha, hne, rfl⟩ := (mLW k).1 hk
          rcases h with h | h
          · omega
          · rcases hvd with ⟨-, hv'⟩ | ⟨hv, hv'⟩ <;> rw [hv'] at h
            · exact hne (Fin.ext (by omega))
            · exact hv (by rwa [← Fin.ext (by omega : a.val = v.val)])
      · rw [p2 _ (by omega), p1 _ h3]
        apply Bool.eq_iff_iff.2
        rw [oe, oe]
        have E1 : k = u.val ↔ k = u'.val := by
          rcases hud with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;> rw [hu']
          constructor
          · intro h
            by_cases he : u = u0
            · rw [← he]; exact h
            · exact absurd (Or.inl ((mLU k).2 ⟨u, hu, he, h.symm⟩)) h4
          · intro h; exact absurd h h1
        have E2 : k = n + v.val ↔ k = n + v'.val := by
          rcases hvd with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;> rw [hv']
          constructor
          · intro h
            by_cases he : v = v0
            · rw [← he]; exact h
            · exact absurd (Or.inr ((mLW k).2 ⟨v, hv, he, h.symm⟩)) h4
          · intro h; exact absurd h h2
        rw [E1, E2]
      · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
