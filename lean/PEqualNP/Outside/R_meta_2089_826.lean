import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.LowMerge
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2089_826
    (replacement : ∀ (n : ℕ) (C : Circuit) (j k : ℕ), Monotone2 C → j < C.size →
    (k < n+j ∨ k = n+C.size) →
    let D := eraseGate n C j k
    Monotone2 D ∧ D.size + 1 = C.size ∧ ∀ (x : List Bool), x.length = n → ∀ s : Bool,
      (wireVal C x (n+j) = s → wireVal C x k = s) →
      ∀ i, wireVal C x i = s → wireVal D x (eraseRedirect n j k i) = s)
    (quota : ∀ (C : Circuit), Monotone2 C → ∀ (a : ℕ),
    (∀ p l, p ∈ singerLines3 l → wireVal C (pointLineInput 13 13 p l) a = true) →
    ∀ X : Finset (Fin 13), let Y := missLines singerLines3 X
    let x := incidenceInput X Y
    X = zeroSet singerLines3 Y → wireVal C x a = false → ∃ I : Finset ℕ, x.count false ≤ I.card + 1 ∧ ∀ i ∈ I,
      26 ≤ i ∧ i ≤ a ∧ (gateAt C (i-26)).op = GateOp.or ∧ wireVal C x i = false)
    (core : let T := fun (s : Bool) (x : List Bool) => if s then
      ∃ p l, p ∈ singerLines3 l ∧ x = pointLineInput 13 13 p l
    else ∃ X, let Y := missLines singerLines3 X
              X = zeroSet singerLines3 Y ∧ ¬IsGeneric singerLines3 0 X Y ∧ x = incidenceInput X Y
    let F := fun (p l : Fin 13) =>
      let X := (singerLines3 l).erase p
      incidenceInput X (missLines singerLines3 X)
    ∀ (C : Circuit), Monotone2 C → ∀ (a b : Fin (26+C.size)), a ≠ b →
      (∀ s x, T s x → (wireVal C x a && wireVal C x b) = s) →
      (wireVal C (F 0 0) a = false) →
      (∀ x, T false x → ∀ w : ℕ, (w = a ∨ w = b) → wireVal C x w = false →
        ∃ I : Finset ℕ, x.count false ≤ I.card+1 ∧ ∀ i ∈ I, 26 ≤ i ∧ i ≤ w ∧
          (gateAt C (i-26)).op = GateOp.or ∧ wireVal C x i = false) →
      (∀ j < C.size, 26+j ≠ a → 26+j ≠ b → ∀ k, (k < 26+j ∨ k = 26+C.size) →
        ∃ s x, T s x ∧ wireVal C x (26+j) = s ∧ wireVal C x k ≠ s) → 63 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  classical
  intro diff inc avoids pair neg value C hC hBudget u v huv hPos hNeg
  let T := fun (s : Bool) (x : List Bool) => if s then
      ∃ p l, p ∈ singerLines3 l ∧ x = pointLineInput 13 13 p l
    else ∃ X, let Y := missLines singerLines3 X
              X = zeroSet singerLines3 Y ∧ ¬IsGeneric singerLines3 0 X Y ∧ x = incidenceInput X Y
  have incident : ∀ p l, p ∈ singerLines3 l ↔ inc p l := by decide +kernel
  have pairRow : ∀ p l, pointLineInput 13 13 p l = List.ofFn (pair p l) := by decide +kernel
  have missing (X : Finset (Fin 13)) (l : Fin 13) : l ∈ missLines singerLines3 X ↔ avoids X l := by
    change l ∈ Finset.univ.filter _ ↔ ∀ p ∈ X, ¬inc p l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
    constructor
    · intro h p hp hi; exact h ((incident p l).mpr hi) hp
    · intro h p hi hp; exact h p hp ((incident p l).mp hi)
  have negativeRow (X : Finset (Fin 13)) :
      incidenceInput X (missLines singerLines3 X) = List.ofFn (neg X) := by
    rw [List.ofFn_add]
    change (List.ofFn (fun p => decide (p ∈ X)) ++ List.ofFn (fun l => decide (l ∈ missLines singerLines3 X))) = _
    congr 1
    · apply congrArg List.ofFn; funext p
      apply decide_eq_decide.mpr
      change p ∈ X ↔ (∃ q ∈ X, Fin.castAdd 13 p = Fin.castAdd 13 q) ∨ ∃ l, Fin.castAdd 13 p = Fin.natAdd 13 l ∧ _
      constructor
      · exact fun hp => Or.inl ⟨p,hp,rfl⟩
      · rintro (⟨q,hq,eq⟩ | ⟨l,eq,_⟩)
        · have e := congrArg Fin.val eq; have pq : p = q := Fin.ext e; simpa [pq] using hq
        · have e := congrArg Fin.val eq; change p.val = 13+l.val at e; omega
    · apply congrArg List.ofFn; funext l
      apply decide_eq_decide.mpr
      change l ∈ missLines singerLines3 X ↔ (∃ q ∈ X, Fin.natAdd 13 l = Fin.castAdd 13 q) ∨ ∃ z, Fin.natAdd 13 l = Fin.natAdd 13 z ∧ avoids X z
      constructor
      · exact fun h => Or.inr ⟨l,rfl,(missing X l).mp h⟩
      · rintro (⟨q,_,eq⟩ | ⟨z,eq,hz⟩)
        · have e := congrArg Fin.val eq; change 13+l.val=q.val at e; omega
        · have e := congrArg Fin.val eq; change 13+l.val=13+z.val at e
          have e' : l=z := Fin.ext (by omega); exact e' ▸ (missing X z).mpr hz
  have fits (s : Bool) (x : List Bool) (h : T s x) : (wireVal C x u && wireVal C x v) = s := by
    cases s
    · change ∃ X, X = zeroSet singerLines3 (missLines singerLines3 X) ∧ _ ∧ _ at h
      obtain ⟨X,hclosed,hd,rfl⟩ := h
      have hmax (p : Fin 13) (hp : p ∉ X) : ∃ l, avoids X l ∧ inc p l := by
        have hout : p ∉ zeroSet singerLines3 (missLines singerLines3 X) := by rwa [← hclosed]
        change p ∉ Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ missLines singerLines3 X, p ∉ singerLines3 l) at hout
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hout
        push Not at hout
        obtain ⟨l,hl,hp⟩ := hout
        exact ⟨l,(missing X l).mp hl,(incident p l).mp hp⟩
      have heither : (∃ l, ∀ p ∈ X, inc p l) ∨ (∃ p, ∀ l, avoids X l → inc p l) := by
        by_contra! h
        apply hd
        refine ⟨Nat.zero_le _,Nat.zero_le _,?_,?_⟩
        · intro l hs; obtain ⟨p,hp,hn⟩ := h.1 l; exact hn ((incident p l).mp (hs hp))
        · intro p hs; obtain ⟨l,hl,hn⟩ := h.2 p; exact hn ((incident p l).mp (hs l ((missing X l).mpr hl)))
      rw [negativeRow X]
      have h := hNeg X hmax heither
      change (wireVal C (List.ofFn (neg X)) u && (wireVal C (List.ofFn (neg X)) v && true)) = false at h
      simpa only [Bool.and_true] using h
    · change ∃ p l, p ∈ singerLines3 l ∧ _ at h
      obtain ⟨p,l,hi,rfl⟩ := h
      rw [pairRow]
      have h := hPos p l ((incident p l).mp hi)
      change (wireVal C (List.ofFn (pair p l)) u && (wireVal C (List.ofFn (pair p l)) v && true)) = true at h
      simpa only [Bool.and_true] using h
  have rowLen (s x) (ht : T s x) : List.length x = 26 := by
    cases s
    · obtain ⟨X,_,_,rfl⟩ := ht; rw [negativeRow,List.length_ofFn]
    · obtain ⟨p,l,_,rfl⟩ := ht; rw [pairRow,List.length_ofFn]
  let feasible (m : ℕ) := ∃ D : Circuit, Monotone2 D ∧ D.size = m ∧ ∃ a b : Fin (26+D.size),
    a ≠ b ∧ ∀ s x, T s x → (wireVal D x a && wireVal D x b) = s
  have existsSize : ∃ m, feasible m := ⟨C.size,C,hC,rfl,u,v,huv,fits⟩
  obtain ⟨D,hm,hsize,a₀,b₀,hab₀,hd₀⟩ := Nat.find_spec existsSize
  let F := fun (p l : Fin 13) =>
      let X := (singerLines3 l).erase p
      incidenceInput X (missLines singerLines3 X)
  have allFlags : ∀ p l : Fin 13, p ∈ singerLines3 l →
      let X := (singerLines3 l).erase p
      let Y := missLines singerLines3 X
      X = zeroSet singerLines3 Y ∧ ¬IsGeneric singerLines3 0 X Y := by decide +kernel
  have fixed : T false (F 0 0) := by
    refine ⟨(singerLines3 0).erase 0,?_⟩
    have h := allFlags 0 0 (by decide)
    exact ⟨h.1,h.2,rfl⟩
  have orient : ∃ a b : Fin (26+D.size), a ≠ b ∧
      (∀ s x, T s x → (wireVal D x a && wireVal D x b) = s) ∧ wireVal D (F 0 0) a = false := by
    cases eq : wireVal D (F 0 0) a₀ with
    | false => exact ⟨a₀,b₀,hab₀,hd₀,eq⟩
    | true =>
      refine ⟨b₀,a₀,Ne.symm hab₀,fun s x hx => (Bool.and_comm _ _).trans (hd₀ s x hx),?_⟩
      simpa only [eq,Bool.true_and] using hd₀ false (F 0 0) fixed
  obtain ⟨a,b,hab,hd,haoff⟩ := orient
  have quotas (x : List Bool) (hx : T false x) (w : ℕ) (hw : w = a ∨ w = b)
      (off : wireVal D x w = false) : ∃ I : Finset ℕ, x.count false ≤ I.card+1 ∧ ∀ i ∈ I,
          26 ≤ i ∧ i ≤ w ∧ (gateAt D (i-26)).op = GateOp.or ∧ wireVal D x i = false := by
    have ok (q r : Fin 13) (hr : q ∈ singerLines3 r) : wireVal D (pointLineInput 13 13 q r) w = true := by
      have test : T true (pointLineInput 13 13 q r) := ⟨q,r,hr,rfl⟩
      have hits := Bool.and_eq_true_iff.mp (hd true _ test)
      rcases hw with rfl | rfl
      · exact hits.1
      · exact hits.2
    obtain ⟨X,closed,_,rfl⟩ := hx
    exact quota D hm w ok X closed off
  have least : ∀ m, feasible m → D.size ≤ m := by intro m h; rw [hsize]; exact Nat.find_min' existsSize h
  have small := least _ (show feasible C.size from ⟨C,hC,rfl,u,v,huv,fits⟩)
  apply Nat.not_succ_le_self 62
  refine (core D hm a b hab hd haoff quotas ?_).trans (small.trans hBudget)
  intro j hj hja hjb k hk
  by_contra none
  have dom (s x) (ht : T s x) (hval : wireVal D x (26+j) = s) : wireVal D x k = s := by
    by_contra hv
    exact none ⟨s,x,ht,hval,hv⟩
  let E := eraseGate 26 D j k
  obtain ⟨hmE,hsizeE,htransfer⟩ := replacement 26 D j k hm hj hk
  let r := eraseRedirect 26 j k
  have valid (i : Fin (26+D.size)) (h : 26+j ≠ i.val) : r i < 26+E.size := by
    change (eraseGate 26 D j k).size + 1 = D.size at hsizeE
    change eraseRedirect 26 j k i.val < 26+(eraseGate 26 D j k).size
    have hi := i.isLt
    unfold eraseRedirect; split_ifs <;> omega
  let a' : Fin (26+E.size) := ⟨r a,valid a hja⟩
  let b' : Fin (26+E.size) := ⟨r b,valid b hjb⟩
  have distinct : a' ≠ b' := by
    intro eq
    have h := congrArg Fin.val eq
    change eraseRedirect 26 j k a.val = eraseRedirect 26 j k b.val at h
    apply hab; apply Fin.ext; unfold eraseRedirect at h; split_ifs at h <;> omega
  have fitE (s x) (ht : T s x) : (wireVal E x a' && wireVal E x b') = s := by
    have tr := htransfer x (rowLen s x ht) s (dom s x ht)
    have ta := tr a; have tb := tr b
    change (wireVal E x (r a) && wireVal E x (r b)) = s
    change wireVal D x a = s → wireVal E x (r a) = s at ta
    change wireVal D x b = s → wireVal E x (r b) = s at tb
    have ok := hd s x ht
    cases s
    · cases ha : wireVal D x a with
      | false => simp [ta ha]
      | true =>
        cases hb : wireVal D x b with
        | false => simp [tb hb]
        | true => simp [ha,hb] at ok
    · have hh := Bool.and_eq_true_iff.mp ok
      simp [ta hh.1,tb hh.2]
  have contradiction := least E.size ⟨E,hmE,rfl,a',b',distinct,fitE⟩
  change E.size+1=D.size at hsizeE
  omega
