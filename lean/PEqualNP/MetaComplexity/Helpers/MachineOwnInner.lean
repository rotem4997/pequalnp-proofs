import PEqualNP.MetaComplexity.Helpers.MachineOwnGeneric
import PEqualNP.MetaComplexity.Helpers.MachineOwnDefs

/-!
# Helper module (proofs only): the slot vertices and the slot triples of one subdivided edge

`XO E k u v t` is `3 E + 2 + 2 k (u (3 E + 3) + v) + t` (the subtraction never truncates), a
fixed polynomial of unary numbers. The parity filter of `innerO` keeps, for `m < k`, exactly
`s = 2 m + [inT]`, so `innerO` is a loop over `m < k` writing one triple each.
-/

namespace PEqualNP.MetaComplexity.MachineOwn

open PEqualNP.Library PEqualNP.Library.Universal

def tripleO (E k u v s : ℕ) : List ℕ :=
  [XO E k u v (s + 1), if s = 0 then u else XO E k u v s,
    if s + 1 = 2 * k then v else XO E k u v (s + 2)]

theorem filter_parity (n : ℕ) (inT : Bool) :
    (List.range (2 * n)).filter (fun s : ℕ => decide ((s + 1) % 2 = 0 ↔ inT = true)) =
      (List.range n).map (fun m => 2 * m + (if inT then 1 else 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, List.range_succ, List.range_succ, List.filter_append, List.filter_append, ih,
      List.range_succ, List.map_append]
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1 + 1) % 2 = 0 := by omega
    cases inT <;> simp [h1, h2]

theorem innerO_range (E k u v : ℕ) (inT : Bool) :
    innerO E k u v inT = (List.range k).map (fun m => tripleO E k u v (2 * m + (if inT then 1 else 0))) := by
  have : innerO E k u v inT =
      ((List.range (2 * k)).filter (fun s : ℕ => decide ((s + 1) % 2 = 0 ↔ inT = true))).map
        (tripleO E k u v) := rfl
  rw [this, filter_parity, List.map_map]
  rfl

section

variable {α : Type} {D : α → Prop} {ea : α → List Bool}

theorem sp_X {E K U V T : α → ℕ} (hE : SP D ea (fun a => un (E a))) (hK : SP D ea (fun a => un (K a)))
    (hU : SP D ea (fun a => un (U a))) (hV : SP D ea (fun a => un (V a)))
    (hT : SP D ea (fun a => un (T a))) :
    SP D ea (fun a => un (XO (E a) (K a) (U a) (V a) (T a))) := by
  have h3 : SP D ea (fun a => un (3 * (E a) + 2)) := ((sp_num 3).mul hE).add (sp_num 2)
  have hP : SP D ea (fun a => un (2 * K a * (U a * (3 * (E a + 1)) + V a))) :=
    ((sp_num 2).mul hK).mul ((hU.mul (((sp_num 3).mul (hE.add (sp_num 1))))).add hV)
  refine ((h3.add hP).add hT).congr (fun a _ => ?_)
  unfold XO
  generalize 2 * K a * (U a * (3 * (E a + 1)) + V a) = P
  congr 1
  omega

theorem bflag_un (b : Bool) : bflag b = un (if b then 1 else 0) := by
  cases b <;> rfl

theorem sp_inner {E K U V : α → ℕ} {B : α → Bool} (hE : SP D ea (fun a => un (E a)))
    (hK : SP D ea (fun a => un (K a))) (hU : SP D ea (fun a => un (U a)))
    (hV : SP D ea (fun a => un (V a))) (hB : SP D ea (fun a => bflag (B a))) :
    SP D ea (fun a => flatS (innerO (E a) (K a) (U a) (V a) (B a))) := by
  let D' : α × ℕ → Prop := fun q => D q.1 ∧ q.2 < K q.1
  have up : ∀ {A : α → ℕ}, SP D ea (fun a => un (A a)) → SP D' (ext ea) (fun q => un (A q.1)) :=
    fun h => h.up (fun q hq => hq.1)
  have hS : SP D' (ext ea) (fun q => un (2 * q.2 + (if B q.1 then 1 else 0))) :=
    ((sp_num 2).mul sp_idx).add ((hB.up (D' := D') (fun q hq => hq.1)).congr
      (fun q _ => bflag_un _))
  have hX : ∀ {T : α × ℕ → ℕ}, SP D' (ext ea) (fun q => un (T q)) →
      SP D' (ext ea) (fun q => un (XO (E q.1) (K q.1) (U q.1) (V q.1) (T q))) :=
    fun hT => sp_X (up hE) (up hK) (up hU) (up hV) hT
  have hs1 := hX (hS.add (sp_num 1))
  have hs0 := hX hS
  have hs2 := hX (hS.add (sp_num 2))
  have c2 : SP D' (ext ea) (fun q => un (if 2 * q.2 + (if B q.1 then 1 else 0) = 0 then U q.1
      else XO (E q.1) (K q.1) (U q.1) (V q.1) (2 * q.2 + (if B q.1 then 1 else 0)))) :=
    (SP.ite (hS.eqN (sp_num 0)) (up hU) hs0).congr (fun q _ => by split_ifs <;> rfl)
  have c3 : SP D' (ext ea) (fun q => un (if 2 * q.2 + (if B q.1 then 1 else 0) + 1 = 2 * K q.1
      then V q.1
      else XO (E q.1) (K q.1) (U q.1) (V q.1) (2 * q.2 + (if B q.1 then 1 else 0) + 2))) :=
    (SP.ite ((hS.add (sp_num 1)).eqN ((sp_num 2).mul (up hK))) (up hV) hs2).congr
      (fun q _ => by split_ifs <;> rfl)
  have body : SP D' (ext ea) (fun q => flatS [tripleO (E q.1) (K q.1) (U q.1) (V q.1)
      (2 * q.2 + (if B q.1 then 1 else 0))]) :=
    ((sp_const [true]).app ((hs1.encN.app (c2.encN.app c3.encN)).app (sp_const [false]))).congr
      (fun q _ => by simp [flatS_single, tripleO, encNs_cons, List.append_assoc])
  refine (SP.loop (B := fun a m => flatS [tripleO (E a) (K a) (U a) (V a)
      (2 * m + (if B a then 1 else 0))]) hK body).congr (fun a _ => ?_)
  rw [innerO_range, flatS_map]

end

end PEqualNP.MetaComplexity.MachineOwn
