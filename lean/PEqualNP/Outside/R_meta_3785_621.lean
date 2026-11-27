import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 24000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3785_621
    (matrix : ∃ U : Circuit, Monotone2 U ∧ U.size ≤ 28 ∧ U.output < 23+U.size ∧
      ∀ x : Fin 17 → Bool, U.eval (List.ofFn x ++ [
          x 13 || x 14, (x 13 || x 14) || x 9,
          x 15 || x 11, (x 15 || x 11) || x 10,
          x 16 || x 12, (x 16 || x 12) || x 8]) = true ↔
        ∃ (a : Fin 6) (b : Fin 4), x (Fin.ofNat 17 a.val) = true ∧
          x (Fin.ofNat 17 (if b.val=0 then 6+a.val/3 else
            8+(if a.val<3 then 3*a.val+(b.val-1) else 3*(b.val-1)+(a.val-3)))) = true)
    (combine : ∀ (n N : ℕ) (f : Fin n → Fin N) (U S : Circuit),
      Monotone2 U → Monotone2 S → U.output<n+U.size → S.output<N+S.size →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ U.size+S.size+1 ∧ C.output<N+C.size ∧
        ∀ x : Fin N → Bool, C.eval (List.ofFn x) =
          (U.eval (List.ofFn (x ∘ f)) || S.eval (List.ofFn x))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (43 : ℕ) ∧       x1.output < (21 : ℕ) + x1.size ∧         have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];         have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.map (x3 x5 x6) x2) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x4 x7 x8 := by
  let emb : Fin 17 → Fin 21 := ![0,5,8,3,6,7,9,11,15,20,19,16,14,13,18,12,10]
  let pt (a : Fin 6) := emb (Fin.ofNat 17 a.val)
  let ln (a : Fin 6) (b : Fin 4) := emb (Fin.ofNat 17 (if b.val=0 then 6+a.val/3 else
    8+(if a.val<3 then 3*a.val+(b.val-1) else 3*(b.val-1)+(a.val-3))))
  let rp : Fin 3 → Fin 21 := ![1,2,4]
  let rl : Fin 3 → Fin 4 → Fin 21 := ![![13,17,18,20],![12,16,17,19],![10,14,15,17]]
  let label : Fin 21 → Fin 26 := ![2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25]
  let index (j : Fin 21) := Fin.ofNat 13 (label j).val
  let near (p l : Fin 13) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
  let inside (p : Fin 13) := p.val ∉ ([0,1,3,9] : List ℕ)
  have geometry : ∀ p l : Fin 13, inside p ∧ near p l ↔
      (∃ (a : Fin 6) (b : Fin 4), index (pt a)=p ∧ index (ln a b)=l) ∨
      (∃ (a : Fin 3) (b : Fin 4), index (rp a)=p ∧ index (rl a b)=l) := by decide +kernel
  have sides : (∀ a, (label (pt a)).val < 13) ∧ (∀ a b, ¬(label (ln a b)).val < 13) ∧
      (∀ a, (label (rp a)).val < 13) ∧ (∀ a b, ¬(label (rl a b)).val < 13) := by decide +kernel
  let g (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩
  let S : Circuit := ⟨[g .or 13 18, g .or 21 20, g .or 22 17, g .and 1 23,
      g .or 12 16, g .or 25 19, g .or 26 17, g .and 2 27,
      g .or 10 14, g .or 29 15, g .or 30 17, g .and 4 31, g .or 24 28, g .or 33 32],34⟩
  have sMono : Monotone2 S := by
    intro z hz
    simp only [S,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [g]
  let bank35 (x : Fin 21 → Bool) : Fin 35 → Bool :=
    let h0 := x 13 || x 18
    let t0 := h0 || x 20
    let v0 := t0 || x 17
    let r0 := x 1 && v0
    let h1 := x 12 || x 16
    let t1 := h1 || x 19
    let v1 := t1 || x 17
    let r1 := x 2 && v1
    let h2 := x 10 || x 14
    let t2 := h2 || x 15
    let v2 := t2 || x 17
    let r2 := x 4 && v2
    ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, h0, t0, v0, r0, h1, t1, v1, r1, h2, t2, v2, r2, r0 || r1, (r0 || r1) || r2]
  let push (w : List Bool) (z : Gate) := w ++ [z.op.eval (z.inputs.map (fun i => w.getD i false))]
  have andBit (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
  have orBit (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  have bankSpec (x : Fin 21 → Bool) : S.wires (List.ofFn x) = List.ofFn (bank35 x) := by
    have input : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20] := rfl
    change S.gates.foldl push (List.ofFn x) = List.ofFn (bank35 x)
    rw [input]
    simp (config := { maxSteps := 600000 }) [S, push, g, andBit, orBit, List.getD, bank35, List.ofFn_succ]
  let F : Fin 23 → Fin 35 := ![0,5,8,3,6,7,9,11,15,20,19,16,14,13,18,12,10,21,22,25,26,29,30]
  have feeds (x : Fin 21 → Bool) : List.ofFn (bank35 x ∘ F) =
      List.ofFn (x ∘ emb) ++ [
        (x ∘ emb) 13 || (x ∘ emb) 14, ((x ∘ emb) 13 || (x ∘ emb) 14) || (x ∘ emb) 9,
        (x ∘ emb) 15 || (x ∘ emb) 11, ((x ∘ emb) 15 || (x ∘ emb) 11) || (x ∘ emb) 10,
        (x ∘ emb) 16 || (x ∘ emb) 12, ((x ∘ emb) 16 || (x ∘ emb) 12) || (x ∘ emb) 8] := by
    rfl
  let B : Circuit := ⟨[],34⟩
  have row (x : Fin 21 → Bool) : B.eval (List.ofFn (bank35 x)) = true ↔
      ∃ (a : Fin 3) (b : Fin 4), x (rp a) = true ∧ x (rl a b) = true := by
    let z (a : Fin 3) := x (rp a) && ((x (rl a 0) || x (rl a 1)) || (x (rl a 2) || x (rl a 3)))
    have value : B.eval (List.ofFn (bank35 x)) = ((z 0 || z 1) || z 2) := by
      change (((x 1 && (((x 13 || x 18) || x 20) || x 17)) ||
        (x 2 && (((x 12 || x 16) || x 19) || x 17))) ||
        (x 4 && (((x 10 || x 14) || x 15) || x 17))) = _
      dsimp [z,rp,rl]
      ac_rfl
    have three : ∀ f : Fin 3 → Bool, ((f 0 || f 1) || f 2)=true ↔ ∃ a, f a=true := by decide +kernel
    have four : ∀ (k : Bool) (f : Fin 4 → Bool),
        (k && ((f 0 || f 1) || (f 2 || f 3)))=true ↔ ∃ b, k=true ∧ f b=true := by decide +kernel
    rw [value,three]
    exact exists_congr (fun a => four (x (rp a)) (fun b => x (rl a b)))
  obtain ⟨U,um,us,uo,uc⟩ := matrix
  have bm : Monotone2 B := by intro q h; simp [B] at h
  obtain ⟨T,tm,ts,to_,te⟩ := combine 23 35 F U B um bm uo (by decide +kernel)
  let C : Circuit := ⟨S.gates ++ T.gates,T.output⟩
  have cm : Monotone2 C := by
    intro q h
    rcases List.mem_append.mp h with h|h
    · exact sMono q h
    · exact tm q h
  have sz : C.size = 14 + T.size := by
    change (S.gates ++ T.gates).length = 14 + T.gates.length
    rw [List.length_append]
    rfl
  have tb : T.size ≤ U.size + 0 + 1 := ts
  have ce (x : Fin 21 → Bool) : C.eval (List.ofFn x) =
      (U.eval (List.ofFn (bank35 x ∘ F)) || B.eval (List.ofFn (bank35 x))) := by
    have cat : C.eval (List.ofFn x) = T.eval (S.wires (List.ofFn x)) := by
      change ((S.gates ++ T.gates).foldl push (List.ofFn x)).getD T.output false =
        (T.gates.foldl push (S.gates.foldl push (List.ofFn x))).getD T.output false
      rw [List.foldl_append]
    rw [cat,bankSpec,te]
  refine ⟨C,cm,by omega,by change T.output < 21 + C.size; omega,?_⟩
  intro _ _ _ s t
  let v (i : Fin 26) := if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s)
    else decide (Fin.ofNat 13 i.val ∈ t)
  let x (j : Fin 21) := v (label j)
  have dataList : ([2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25] : List (Fin 26)) =
      List.ofFn label := by decide +kernel
  have bank : List.map v ([2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25] : List (Fin 26)) =
      List.ofFn x := by rw [dataList,List.map_ofFn]; rfl
  have up (w : Fin 21) (h : (label w).val<13) : x w=true ↔ index w∈s := by simp [x,v,index,h]
  have down (w : Fin 21) (h : ¬(label w).val<13) : x w=true ↔ index w∈t := by simp [x,v,index,h]
  change C.eval (List.map v _) = true ↔ ∃ p ∈ s, inside p ∧ ∃ l ∈ t, near p l
  rw [bank,ce,feeds,Bool.or_eq_true,uc,row]
  change ((∃ (a : Fin 6) (b : Fin 4), x (pt a)=true ∧ x (ln a b)=true) ∨
      (∃ (a : Fin 3) (b : Fin 4), x (rp a)=true ∧ x (rl a b)=true)) ↔ _
  constructor
  · rintro (⟨a,b,ha,hb⟩|⟨a,b,ha,hb⟩)
    · have h := (geometry (index (pt a)) (index (ln a b))).mpr (Or.inl ⟨a,b,rfl,rfl⟩)
      exact ⟨_,(up _ (sides.1 a)).mp ha,h.1,_,(down _ (sides.2.1 a b)).mp hb,h.2⟩
    · have h := (geometry (index (rp a)) (index (rl a b))).mpr (Or.inr ⟨a,b,rfl,rfl⟩)
      exact ⟨_,(up _ (sides.2.2.1 a)).mp ha,h.1,_,(down _ (sides.2.2.2 a b)).mp hb,h.2⟩
  · rintro ⟨p,hp,ok,l,hl,inc⟩
    rcases (geometry p l).mp ⟨ok,inc⟩ with ⟨a,b,rfl,rfl⟩|⟨a,b,rfl,rfl⟩
    · exact Or.inl ⟨a,b,(up _ (sides.1 a)).mpr hp,(down _ (sides.2.1 a b)).mpr hl⟩
    · exact Or.inr ⟨a,b,(up _ (sides.2.2.1 a)).mpr hp,(down _ (sides.2.2.2 a b)).mpr hl⟩
