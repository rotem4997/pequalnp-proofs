import PEqualNP.Defs

-- On the finite test family, false sets of conjunctions are free unions. Each binary OR adds a single intersection.
theorem PEqualNP.Outside.R_meta_4055_619
  (compile : ∀ (X : Type) (W : X → List Bool) (n : ℕ), (∀ x, (W x).length = n) →
    ∀ (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ),
    let close := fun (F : Set (Set X)) => {s : Set X | ∃ A ⊆ F, s = ⋃₀ A}
    let step := fun (F : Set (Set X)) (q : Set X × Set X) =>
      F ∪ {s | q.1 ∈ close F ∧ q.2 ∈ close F ∧ s = q.1 ∩ q.2}
    let pred := fun (V : X → List Bool) (i : ℕ) => {x | (V x).getD i false = false}
    let run := fun x => R.foldl (fun v r => v ++ [decide (∀ i ∈ r.1, v.getD i false = true) ||
                    decide (∀ i ∈ r.2, v.getD i false = true)]) (W x)
    ∃ Q : List (Set X × Set X), Q.length = R.length ∧
      {x | ∃ i ∈ out, (run x).getD i false = false} ∈ close (Q.foldl step (Set.range (pred W))))
  (obstruction : let adj := fun (p l : Fin 21) => (l.val+21-p.val)%21 ∈ ([20,0,5,7,17] : List ℕ)
    let closed := fun (P L : Finset (Fin 21)) =>
      (∀ p, p ∈ P ↔ ∀ l ∈ L, ¬adj p l) ∧ (∀ l, l ∈ L ↔ ∀ p ∈ P, ¬adj p l)
    let X := {t : Finset (Fin 21) × Finset (Fin 21) //
      (∃ p l, adj p l ∧ t = ({p},{l})) ∨
      ((t.1.card ≤ 5 ∨ t.2.card ≤ 5 ∨ (t.1.card = 6 ∧ t.2.card = 6)) ∧ closed t.1 t.2)}
    let repr : X → Finset (Fin 21) × Finset (Fin 21) := Subtype.val
    let close := fun (F : Set (Set X)) => {s : Set X | ∃ A ⊆ F, s = ⋃₀ A}
    let step := fun (F : Set (Set X)) (q : Set X × Set X) =>
      F ∪ {s | q.1 ∈ close F ∧ q.2 ∈ close F ∧ s = q.1 ∩ q.2}
    let F : Set (Set X) := {Set.univ} ∪
      (Set.range fun (p : Fin 21) => {x : X | p ∉ (repr x).1}) ∪
      (Set.range fun (l : Fin 21) => {x : X | l ∉ (repr x).2})
    ∀ Q : List (Set X × Set X), {x : X | closed (repr x).1 (repr x).2} ∈ close (Q.foldl step F) → 104 ≤ Q.length) :
  ∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (104 : ℕ) ≤ x1.length := by
  intro R out
  classical
  intro _ _ _ valid outValid pos neg
  let adj := fun (p l : Fin 21) => (l.val+21-p.val)%21 ∈ ([20,0,5,7,17] : List ℕ)
  let actual := fun (p l : Fin 21) => ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List ℕ).contains l.val
  have relation : ∀ p l, adj p l ↔ actual p l = true := by decide +kernel
  let closed := fun (P L : Finset (Fin 21)) =>
    (∀ p, p ∈ P ↔ ∀ l ∈ L, ¬adj p l) ∧ (∀ l, l ∈ L ↔ ∀ p ∈ P, ¬adj p l)
  let X := {t : Finset (Fin 21) × Finset (Fin 21) //
    (∃ p l, adj p l ∧ t = ({p},{l})) ∨
    ((t.1.card ≤ 5 ∨ t.2.card ≤ 5 ∨ (t.1.card = 6 ∧ t.2.card = 6)) ∧ closed t.1 t.2)}
  let val := fun (t : X) => Fin.append (fun p => decide (p ∈ t.val.1)) (fun l => decide (l ∈ t.val.2))
  let init := fun t : X => List.ofFn (val t) ++ [false]
  let close := fun (F : Set (Set X)) => {s : Set X | ∃ A ⊆ F, s = ⋃₀ A}
  let step := fun (F : Set (Set X)) (q : Set X × Set X) => F ∪ {s | q.1 ∈ close F ∧ q.2 ∈ close F ∧ s = q.1 ∩ q.2}
  let F : Set (Set X) := {Set.univ} ∪ (Set.range fun (p : Fin 21) => {x : X | p ∉ x.val.1}) ∪
      (Set.range fun (l : Fin 21) => {x : X | l ∉ x.val.2})
  let pred := fun (i : ℕ) => {x : X | (init x).getD i false = false}
  have raw (i : Fin 42) (t : X) : (init t).getD i false = val t i := by
    simp only [init,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,ite_eq_left i.isLt,
      List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
  have far (i : ℕ) (hi : 42 ≤ i) (t : X) : (init t).getD i false = false := by
    by_cases eq : i = 42
    · subst i; simp [init,List.getD_eq_getElem?_getD]
    · have big : (init t).length ≤ i := by simp [init]; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none big]
  have leftRaw (p : Fin 21) : pred (Fin.castAdd 21 p).val = {x : X | p ∉ x.val.1} := by
    ext t
    change (init t).getD (Fin.castAdd 21 p).val false = false ↔ _
    rw [raw]
    simp only [val,Fin.append_left,decide_eq_false_iff_not,Set.mem_ofPred_eq]
  have rightRaw (l : Fin 21) : pred (Fin.natAdd 21 l).val = {x : X | l ∉ x.val.2} := by
    ext t
    change (init t).getD (Fin.natAdd 21 l).val false = false ↔ _
    rw [raw]
    simp only [val,Fin.append_right,decide_eq_false_iff_not,Set.mem_ofPred_eq]
  have farRaw (i : ℕ) (h : 42 ≤ i) : pred i = Set.univ := by
    ext t
    change (init t).getD i false = false ↔ True
    exact iff_true_intro (far i h t)
  have seedEq : Set.range pred = F := by
    ext S
    constructor
    · rintro ⟨i,rfl⟩
      by_cases small : i < 42
      · let k : Fin (21+21) := ⟨i,small⟩
        change pred k ∈ F
        induction k using Fin.addCases with
        | left p =>
          apply Or.inl ∘ Or.inr
          exact ⟨p,(leftRaw p).symm⟩
        | right l => exact Or.inr ⟨l,(rightRaw l).symm⟩
      · apply Or.inl ∘ Or.inl
        exact Set.mem_singleton_iff.mpr (farRaw i (by omega))
    · rintro ((h|⟨p,rfl⟩)|⟨l,rfl⟩)
      · rw [Set.mem_singleton_iff.mp h]
        exact ⟨42,farRaw 42 (by decide)⟩
      · exact ⟨_,leftRaw p⟩
      · exact ⟨_,rightRaw l⟩
  let run := fun (x : Fin 42 → Bool) => R.foldl (fun (v : List Bool) (r : Finset ℕ × Finset ℕ) =>
    v ++ [decide (∀ i ∈ r.1, v.getD i false = true) || decide (∀ i ∈ r.2, v.getD i false = true)]) (List.ofFn x ++ [false])
  let eval := fun x => decide (∀ i ∈ out, (run x).getD i false = true)
  obtain ⟨Q,len,mem⟩ := compile X init 43 (fun t => by simp [init]) R out
  change {x : X | ∃ i ∈ out, (run (val x)).getD i false = false} ∈ close (Q.foldl step (Set.range pred)) at mem
  have valL (t : X) (p : Fin 21) : val t (Fin.castAdd 21 p) = true ↔ p ∈ t.val.1 := by simp only [val,Fin.append_left,decide_eq_true_eq]
  have valR (t : X) (l : Fin 21) : val t (Fin.natAdd 21 l) = true ↔ l ∈ t.val.2 := by simp only [val,Fin.append_right,decide_eq_true_eq]
  have exactValue (t : X) : eval (val t) = false ↔ closed t.val.1 t.val.2 := by
    rcases t.property with ⟨p,l,edge,pair⟩|⟨_,cl⟩
    · have one : val t = fun i => decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l) := by
        funext i
        induction i using Fin.addCases (m := 21) (n := 21) with
        | left a =>
          have ne : Fin.castAdd 21 a ≠ Fin.natAdd 21 l := by intro h; have := congrArg Fin.val h; simp at this; omega
          simp only [val,Fin.append_left,pair,Finset.mem_singleton,Fin.castAdd_inj,ne,or_false]
        | right b =>
          have ne : Fin.natAdd 21 b ≠ Fin.castAdd 21 p := by intro h; have := congrArg Fin.val h; simp at this; omega
          simp only [val,Fin.append_right,pair,Finset.mem_singleton,Fin.natAdd_inj,ne,false_or]
      have yes := pos p l ((relation p l).mp edge)
      change eval _ = true at yes
      rw [one,yes]
      have fail : ¬closed t.val.1 t.val.2 := by
        intro h
        exact (h.1 p |>.mp (by simp [pair])) l (by simp [pair]) edge
      simp [fail]
    · have safe : ∀ p l, actual p l = true → val t (Fin.castAdd 21 p) = false ∨ val t (Fin.natAdd 21 l) = false := by
        intro p l e
        by_cases rp : p ∈ t.val.1
        · have rl := cl.1 p |>.mp rp
          right; exact Bool.eq_false_iff.mpr (fun hl => rl l ((valR t l).mp hl) ((relation p l).mpr e))
        · left; exact Bool.eq_false_iff.mpr (fun h => rp ((valL t p).mp h))
      have maximal : ∀ y : Fin 42 → Bool,
          (∀ p l, actual p l = true → y (Fin.castAdd 21 p) = false ∨ y (Fin.natAdd 21 l) = false) →
          (∀ i, val t i = true → y i = true) → y = val t := by
        intro y independent ext
        funext i
        apply Bool.eq_iff_iff.mpr
        refine ⟨?_,ext i⟩
        induction i using Fin.addCases (m := 21) (n := 21) with
        | left p =>
          intro yp; apply (valL t p).mpr; apply (cl.1 p).mpr
          intro l hl e
          have yl := ext _ ((valR t l).mpr hl)
          rcases independent p l ((relation p l).mp e) with hp|hb <;> simp_all only [Bool.false_eq_true,Bool.true_eq_false]
        | right l =>
          intro yl; apply (valR t l).mpr; apply (cl.2 l).mpr
          intro p hp e
          have yp := ext _ ((valL t p).mpr hp)
          rcases independent p l ((relation p l).mp e) with ha|hb <;> simp_all only [Bool.false_eq_true,Bool.true_eq_false]
      exact ⟨fun _ => cl,fun _ => neg (val t) safe maximal⟩
  have identifies : {x : X | ∃ i ∈ out, (run (val x)).getD i false = false} = {x : X | closed x.val.1 x.val.2} := by
    ext x
    have h := exactValue x
    simpa [eval] using h
  rw [seedEq,identifies] at mem
  have bound := obstruction Q mem
  omega
