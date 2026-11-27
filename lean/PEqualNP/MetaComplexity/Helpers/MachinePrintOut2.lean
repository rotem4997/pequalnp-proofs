import PEqualNP.MetaComplexity.Helpers.MachinePrintOut

/-!
# Writing the relative gates: the four copies of a tuple segment

Helper module (proofs only, no statement may use it). Continues `MachinePrintOut`.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.CircuitLowerBounds

/-- The code of one reference and of one relative gate in the input of D02. -/
def refE : ℕ ⊕ ℕ → List Bool :=
  Sum.elim (fun a : ℕ => false :: (List.replicate a true ++ [false]))
    (fun d : ℕ => true :: (List.replicate d true ++ [false]))

def gE (g : RG) : List Bool := true :: g.1 :: (refE g.2.1 ++ refE g.2.2)

theorem d02enc_eq (n : ℕ) (L : List RG) :
    d02enc (n, L) = List.replicate n true ++ false :: (L.flatMap gE ++ [false]) := by
  simp [d02enc, encodeList]
  rfl

/-! ## Entry runs -/

theorem tokE_run1 (q q' : FS) (r : Role) (a : ℕ) (o1 o3 : List Bool)
    (h1 : δF q (.ES r) = (q', o1)) (h2 : δF q' (.O r) = (q', [true]))
    (h3 : δF q' (.EE r) = (q', o3)) :
    out q (tokE r a) = o1 ++ List.replicate a true ++ o3 ∧ nxt q (tokE r a) = q' := by
  have hr := rep_one q' (.O r) true h2 a
  simp only [tokE, out_cons, nxt_cons, h1, out_append, nxt_append, hr.1, hr.2, out_cons,
    nxt_cons, h3, out_nil]
  exact ⟨by simp, rfl⟩

theorem tokE_run0 (q : FS) (r : Role) (a : ℕ)
    (h1 : δF q (.ES r) = (q, [])) (h2 : δF q (.O r) = (q, []))
    (h3 : δF q (.EE r) = (q, [])) :
    out q (tokE r a) = [] ∧ nxt q (tokE r a) = q := by
  have hr := rep_none q (.O r) h2 a
  simp only [tokE, out_cons, nxt_cons, h1, out_append, nxt_append, hr.1, hr.2, out_cons,
    nxt_cons, h3, out_nil]
  exact ⟨by simp, rfl⟩

/-! ## Copy 2 -/

theorem c2_idle (lead xf : Bool) (k : Kc) (hk : k = .k0 ∨ k = .k1) (L : List Tok)
    (hL : ∀ x ∈ L, plainTok x ∨ x = .TS) :
    out (.tu, lead, .c2, k, xf) L = [] ∧ nxt (.tu, lead, .c2, k, xf) L = (.tu, lead, .c2, k, xf) := by
  refine idle _ L (fun x hx => ?_)
  rcases hL x hx with h | rfl
  · rcases hk with rfl | rfl <;> cases x <;> simp [plainTok] at h <;> rfl
  · rcases hk with rfl | rfl <;> rfl

theorem c2_xs (lead : Bool) : ∀ xs : List ℕ,
    out (.tu, lead, .c2, .k3, false) (elemsTok .x xs) =
      xs.flatMap (fun y => [true, true, true, true, false, false] ++ List.replicate y true ++ [false]) ∧
    nxt (.tu, lead, .c2, .k3, false) (elemsTok .x xs) = (.tu, lead, .c2, .k3, false)
  | [] => ⟨rfl, rfl⟩
  | y :: xs => by
    have h := tokE_run1 (.tu, lead, .c2, .k3, false) (.tu, lead, .c2, .k3, false) .x y
      [true, true, true, true, false, false] [false] rfl rfl rfl
    have ih := c2_xs lead xs
    simp only [elemsTok, Role.next, out_append, nxt_append, h.1, h.2, ih.1, ih.2]
    exact ⟨by simp, by first | rfl | trivial⟩

/-! ## Copy 3 -/

theorem c3_notT (lead xf : Bool) (k : Kc) (L : List Tok) (hL : ∀ x ∈ L, notT x) :
    out (.tu, lead, .c3, k, xf) L = [] ∧ nxt (.tu, lead, .c3, k, xf) L = (.tu, lead, .c3, k, xf) := by
  refine idle _ L (fun x hx => ?_)
  have h := hL x hx
  cases x with
  | ES r => cases r <;> simp [notT] at h <;> cases k <;> rfl
  | O r => cases r <;> simp [notT] at h <;> cases k <;> rfl
  | EE r => cases r <;> simp [notT] at h <;> cases k <;> rfl
  | _ => simp [notT] at h

theorem c3_idle (lead xf : Bool) (k : Kc) (hk : k ≠ .k3) (L : List Tok)
    (hL : ∀ x ∈ L, plainTok x ∨ x = .TS) :
    out (.tu, lead, .c3, k, xf) L = [] ∧ nxt (.tu, lead, .c3, k, xf) L = (.tu, lead, .c3, k, xf) := by
  refine idle _ L (fun x hx => ?_)
  rcases hL x hx with h | rfl
  · cases k <;> simp at hk <;> cases x <;> simp [plainTok] at h <;> rfl
  · cases k <;> rfl

/-! ## Copy 4 -/

theorem c4_run (lead xf : Bool) (k : Kc) : ∀ (L : List Tok), (∀ x ∈ L, plainTok x) →
    out (.tu, lead, .c4, k, xf) L =
      (if (k.ge2 && !lead) = true then List.replicate (L.countP Tok.isES) true else []) ∧
    nxt (.tu, lead, .c4, k, xf) L = (.tu, lead, .c4, k, xf)
  | [], _ => by simp [out_nil, nxt]
  | x :: L, hL => by
    have ih := c4_run lead xf k L (fun y hy => hL y (by simp [hy]))
    have hx := hL x (by simp)
    rw [out_cons, nxt_cons]
    cases x with
    | ES r =>
      simp only [δF, δtu, ih.1, ih.2]
      refine ⟨?_, by first | rfl | trivial⟩
      cases h : (k.ge2 && !lead) <;> simp [e4, h, List.countP_cons, Tok.isES, List.replicate_succ]
    | O r =>
      simp only [δF, δtu, ih.1, ih.2]
      refine ⟨?_, by first | rfl | trivial⟩
      cases h : (k.ge2 && !lead) <;> simp [e4, h, List.countP_cons, Tok.isES]
    | EE r =>
      simp only [δF, δtu, ih.1, ih.2]
      refine ⟨?_, by first | rfl | trivial⟩
      cases h : (k.ge2 && !lead) <;> simp [e4, h, List.countP_cons, Tok.isES]
    | _ => simp [plainTok] at hx

theorem c4_seg (lead xf : Bool) (k : Kc) (l : List ℕ) :
    out (.tu, lead, .c4, k, xf) (segT l) =
      (if (k.ge2 && !lead) = true then [true, true, true] ++ List.replicate l.length true else []) ∧
    nxt (.tu, lead, .c4, k, xf) (segT l) = (.tu, lead, .c4, k, xf) := by
  have h := c4_run lead xf k (elemsTok .t l) (elemsTok_plain .t l)
  rw [count_elemsTok] at h
  simp only [segT, out_cons, nxt_cons]
  cases hc : (k.ge2 && !lead)
  · simp only [δF, δtu, e4, hc, Bool.false_eq_true, if_false] at h ⊢
    exact ⟨by simp [h.1], h.2⟩
  · simp only [δF, δtu, e4, hc, if_true] at h ⊢
    exact ⟨by simp [h.1], h.2⟩

/-! ## One tuple segment, all four copies -/

/-- A segment after two mirrors. -/
def mm (s : List Tok) : List Tok := s.reverse ++ Tok.M :: (s ++ Tok.M :: (s.reverse ++ Tok.M :: s))

theorem mm_eq (s : List Tok) : mirSeg Tok.M (mirSeg Tok.M s) = mm s := by
  simp [mirSeg, mm]

theorem sg_tu (lead : Bool) (x : Tok) (hx : x ≠ .LE) :
    δF (.sg, lead, .c1, .k0, true) x = δF (.tu, lead, .c1, .k0, true) x := by
  cases x <;> first | rfl | exact absurd rfl hx

theorem block_gen (lead : Bool) (l : List ℕ) (K : Kc) (hK : kOf l.length = K) (xf2 : Bool)
    (O2 O3 : List Bool)
    (h2 : out (.tu, lead, .c2, K, true) (segT l) = O2 ∧
      nxt (.tu, lead, .c2, K, true) (segT l) = (.tu, lead, .c2, K, xf2))
    (h3 : out (.tu, lead, .c3, K, xf2) (segT l).reverse = O3 ∧
      nxt (.tu, lead, .c3, K, xf2) (segT l).reverse = (.tu, lead, .c3, K, xf2)) :
    out (.sg, lead, .c1, .k0, true) (mm (segT l) ++ [Tok.TE]) =
      O2 ++ O3 ++ (if (K.ge2 && !lead) = true then
        [true, true, true] ++ List.replicate l.length true ++ [false, true, true, false] else []) ∧
    nxt (.sg, lead, .c1, .k0, true) (mm (segT l) ++ [Tok.TE]) =
      (.sg, lead && !K.ge2, .c1, .k0, true) := by
  have h1 := copy1_seg lead l
  rw [hK] at h1
  have h4 := c4_seg lead xf2 K l
  -- the first symbol
  obtain ⟨x, L', hxL⟩ : ∃ x L', (segT l).reverse = x :: L' := by
    cases h : (segT l).reverse with
    | nil => simp [segT] at h
    | cons x L' => exact ⟨x, L', rfl⟩
  have hx : x ≠ .LE := by
    intro hxe
    have : x ∈ segT l := List.mem_reverse.mp (by rw [hxL]; simp)
    rcases segT_tok l x this with h | h
    · rw [hxe] at h; exact h
    · rw [hxe] at h; cases h
  have hsg : ∀ L : List Tok, out (.sg, lead, .c1, .k0, true) ((segT l).reverse ++ L) =
      out (.tu, lead, .c1, .k0, true) ((segT l).reverse ++ L) ∧
      nxt (.sg, lead, .c1, .k0, true) ((segT l).reverse ++ L) =
      nxt (.tu, lead, .c1, .k0, true) ((segT l).reverse ++ L) := by
    intro L
    rw [hxL, List.cons_append, out_cons, out_cons, nxt_cons, nxt_cons, sg_tu lead x hx]
    exact ⟨rfl, rfl⟩
  unfold mm
  rw [List.append_assoc, (hsg _).1, (hsg _).2]
  simp only [out_append, nxt_append, h1.1, h1.2, List.cons_append, out_cons, nxt_cons]
  try simp only [δF, δtu, Cp.next]
  simp only [out_append, nxt_append, h2.1, h2.2, List.cons_append, out_cons, nxt_cons]
  try simp only [δF, δtu, Cp.next]
  simp only [out_append, nxt_append, h3.1, h3.2, List.cons_append, out_cons, nxt_cons]
  try simp only [δF, δtu, Cp.next]
  simp only [out_append, nxt_append, h4.1, h4.2, out_cons, nxt_cons, out_nil]
  try simp only [δF, δtu]
  refine ⟨?_, rfl⟩
  cases hc : (K.ge2 && !lead) <;> simp [hc]

theorem tokE_rev (r : Role) (a : ℕ) :
    (tokE r a).reverse = Tok.EE r :: (List.replicate a (Tok.O r) ++ [Tok.ES r]) := by
  simp [tokE, List.reverse_replicate]

theorem block (lead : Bool) (l : List ℕ) :
    out (.sg, lead, .c1, .k0, true) (mm (segT l) ++ [Tok.TE]) = (relBlock lead l).flatMap gE ∧
    nxt (.sg, lead, .c1, .k0, true) (mm (segT l) ++ [Tok.TE]) =
      (.sg, lead && decide (l.length < 2), .c1, .k0, true) := by
  match l with
  | [] =>
    have h2 := c2_idle lead true .k0 (Or.inl rfl) (segT []) (segT_tok [])
    have h3 := c3_idle lead true .k0 (by simp) (segT []).reverse
      (fun x hx => segT_tok [] x (List.mem_reverse.mp hx))
    have := block_gen lead [] .k0 rfl true [] [] h2 h3
    simp only [Kc.ge2, Bool.false_and, Bool.false_eq_true, if_false, List.append_nil] at this
    refine ⟨this.1, ?_⟩
    rw [this.2]; simp
  | [t] =>
    have h2 := c2_idle lead true .k1 (Or.inr rfl) (segT [t]) (segT_tok [t])
    have h3 := c3_idle lead true .k1 (by simp) (segT [t]).reverse
      (fun x hx => segT_tok [t] x (List.mem_reverse.mp hx))
    have := block_gen lead [t] .k1 rfl true [] [] h2 h3
    simp only [Kc.ge2, Bool.false_and, Bool.false_eq_true, if_false, List.append_nil] at this
    refine ⟨this.1, ?_⟩
    rw [this.2]; simp
  | [t, v] =>
    have r1 := tokE_run1 (.tu, lead, .c2, .k2, true) (.tu, lead, .c2, .k2, true) .t t
      [true, false, false] [false] rfl rfl rfl
    have r2 := tokE_run1 (.tu, lead, .c2, .k2, true) (.tu, lead, .c2, .k2, true) .v v
      [false] [false] rfl rfl rfl
    have h2 : out (.tu, lead, .c2, .k2, true) (segT [t, v]) =
        [true, false, false] ++ List.replicate t true ++ [false] ++
          ([false] ++ List.replicate v true ++ [false]) ∧
        nxt (.tu, lead, .c2, .k2, true) (segT [t, v]) = (.tu, lead, .c2, .k2, true) := by
      simp only [segT, elemsTok, Role.next, List.append_nil, out_cons, nxt_cons]
      simp only [δF, δtu, MachinePrint.e2, List.nil_append]
      rw [out_append, nxt_append, r1.1, r1.2, r2.1, r2.2]
      exact ⟨rfl, rfl⟩
    have h3 := c3_idle lead true .k2 (by simp) (segT [t, v]).reverse
      (fun x hx => segT_tok [t, v] x (List.mem_reverse.mp hx))
    have := block_gen lead [t, v] .k2 rfl true _ [] h2 h3
    refine ⟨?_, ?_⟩
    · rw [this.1]
      cases lead <;> simp [relBlock, chainG, gE, refE, Kc.ge2]
    · rw [this.2]; simp [Kc.ge2]
  | t :: v :: y :: ys =>
    have r1 : out (.tu, lead, .c2, .k3, true) (tokE .t t) = [] ∧
        nxt (.tu, lead, .c2, .k3, true) (tokE .t t) = (.tu, lead, .c2, .k3, true) :=
      tokE_run0 _ .t t rfl rfl rfl
    have r2 := tokE_run1 (.tu, lead, .c2, .k3, true) (.tu, lead, .c2, .k3, true) .v v
      [true, true, false] [false] rfl rfl rfl
    have r3 := tokE_run1 (.tu, lead, .c2, .k3, true) (.tu, lead, .c2, .k3, false) .x y
      [false] [false] rfl rfl rfl
    have r4 := c2_xs lead ys
    have h2 : out (.tu, lead, .c2, .k3, true) (segT (t :: v :: y :: ys)) =
        [true, true, false] ++ List.replicate v true ++ [false] ++
          ([false] ++ List.replicate y true ++ [false] ++
            ys.flatMap (fun y => [true, true, true, true, false, false] ++
              List.replicate y true ++ [false])) ∧
        nxt (.tu, lead, .c2, .k3, true) (segT (t :: v :: y :: ys)) =
          (.tu, lead, .c2, .k3, false) := by
      simp only [segT, elemsTok, Role.next, out_cons, nxt_cons]
      simp only [δF, δtu, MachinePrint.e2, List.nil_append]
      rw [out_append, nxt_append, r1.1, r1.2, out_append, nxt_append, r2.1, r2.2,
        out_append, nxt_append, r3.1, r3.2, r4.1, r4.2]
      exact ⟨by simp, rfl⟩
    have h3 : out (.tu, lead, .c3, .k3, false) (segT (t :: v :: y :: ys)).reverse =
        [true, false, false] ++ List.replicate t true ++ [false, true, true, false] ∧
        nxt (.tu, lead, .c3, .k3, false) (segT (t :: v :: y :: ys)).reverse =
          (.tu, lead, .c3, .k3, false) := by
      have hn := c3_notT lead false .k3 (elemsTok .v (v :: y :: ys)).reverse
        (fun x hx => elemsTok_notT .v _ (by simp) x (List.mem_reverse.mp hx))
      have hr := rep_one (.tu, lead, .c3, .k3, false) (.O .t) true rfl t
      have hs : segT (t :: v :: y :: ys) = Tok.TS :: (tokE .t t ++ elemsTok .v (v :: y :: ys)) := rfl
      rw [hs, List.reverse_cons, List.reverse_append, tokE_rev]
      simp only [List.append_assoc, out_append, nxt_append, hn.1, hn.2, List.cons_append,
        out_cons, nxt_cons]
      simp only [δF, δtu, MachinePrint.e3]
      simp only [out_append, nxt_append, hr.1, hr.2, List.singleton_append, out_cons,
        nxt_cons, out_nil]
      simp [nxt, δF, δtu, MachinePrint.e3]
    have := block_gen lead (t :: v :: y :: ys) .k3 rfl false _ _ h2 h3
    refine ⟨?_, ?_⟩
    · rw [this.1]
      cases lead <;> simp [relBlock, chainG, gE, refE, Kc.ge2, List.flatMap_map]
    · rw [this.2]; simp [Kc.ge2]

end PEqualNP.MetaComplexity.Helpers.MachinePrint
