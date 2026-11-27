import PEqualNP.Defs

-- A factorization on empty and singleton point inputs is sufficient. Each point is
-- incident to its own labeled line, which forces its masked aggregator input to be live.
-- The 21 line summaries and the point aggregator then require separate groups of OR gates.
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4055_524
  (factor :
    let E := fun (r : List (Finset ℕ × Finset ℕ)) (o : Finset ℕ) (x : List Bool) =>
      let w := r.foldl (fun v g => v ++ [decide (∀ i ∈ g.1, v.getD i false = true) ||
        decide (∀ i ∈ g.2, v.getD i false = true)]) (x ++ [false])
      decide (∀ i ∈ o, w.getD i false = true)
    let inc := fun (p l : Fin 21) =>
      ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List ℕ).contains l.val
    ∀ R o, (∀ z : Fin 42 → Bool, E R o (List.ofFn z) = true ↔
      ∃ p l, inc p l = true ∧ z (Fin.castAdd 21 p) = true ∧ z (Fin.natAdd 21 l) = true) →
      ∃ (S A : List (Finset ℕ × Finset ℕ)) (u : Fin 21 → Finset ℕ) (a : Finset ℕ),
        S.length + A.length ≤ R.length ∧
        ∀ x y : Fin 21 → Bool, (x = (fun _ => false) ∨ ∃ p : Fin 21, x = fun i => decide (i = p)) →
          E A a (List.ofFn fun p => x p && E S (u p) (List.ofFn y)) = E R o (List.ofFn (Fin.append x y)))
  (joint :
    let EV := fun (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ) (x : Fin 21 → Bool) =>
      let w := R.foldl (fun (v : List Bool) (r : Finset ℕ × Finset ℕ) =>
        v ++ [decide (∀ i ∈ r.1, v.getD i false = true) || decide (∀ i ∈ r.2, v.getD i false = true)])
        (List.ofFn x ++ [false])
      decide (∀ i ∈ out, w.getD i false = true)
    let inc := fun (p l : Fin 21) =>
      ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List ℕ).contains l.val
    let one := fun (l i : Fin 21) => decide (i = l)
    let outside := fun (p l : Fin 21) => !(inc p l)
    ∀ (R : List (Finset ℕ × Finset ℕ)) (out : Fin 21 → Finset ℕ),
      (∀ p l, inc p l = true → EV R (out p) (one l) = true) →
      (∀ p, EV R (out p) (outside p) = false) → 84 ≤ R.length)
  (aggregator :
    let ev := fun (A : List (Finset ℕ × Finset ℕ)) (c : Finset ℕ) (x : Fin 21 → Bool) =>
      let w := A.foldl (fun w r => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
                                          decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
      decide (∀ i ∈ c, w.getD i false = true)
    ∀ A c, ev A c (fun _ => false) = false →
      (∀ l : Fin 21, ev A c (fun j => decide (j = l)) = true) → 20 ≤ A.length) :
  (∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (104 : ℕ) ≤ x1.length) := by
  classical
  intro R o
  dsimp only
  intro _ _ hpos hneg
  let w := fun (R : List (Finset ℕ × Finset ℕ)) (x : Fin 42 → Bool) =>
      R.foldl (fun w r => w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
        decide (∀ i ∈ r.2, w.getD i false = true)]) (List.ofFn x ++ [false])
  let ev := fun (R : List (Finset ℕ × Finset ℕ)) (o : Finset ℕ) (x : Fin 42 → Bool) =>
      decide (∀ i ∈ o, (w R x).getD i false = true)
  let adj := fun (p l : Fin 21) => [(p.val + 20) % 21, p.val, (p.val + 5) % 21,
      (p.val + 7) % 21, (p.val + 17) % 21].contains l.val
  let F := fun (x : Fin 42 → Bool) => ∃ p l : Fin 21, adj p l = true ∧
      x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true
  let lew := fun (a b : List Bool) => a.length = b.length ∧
    ∀ i : ℕ, a.getD i false = true → b.getD i false = true
  have mono (x y : Fin 42 → Bool) (hxy : x ≤ y) (r : List (Finset ℕ × Finset ℕ)) :
      lew (w r x) (w r y) := by
    have base : lew (List.ofFn x ++ [false]) (List.ofFn y ++ [false]) := by
      refine ⟨by simp, ?_⟩
      intro i hi
      by_cases h : i < 42
      · have raw (z : Fin 42 → Bool) (j : Fin 42) : (List.ofFn z ++ [false]).getD j.val false = z j := by
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,ite_eq_left j.isLt,
            List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some]
        let j : Fin 42 := ⟨i,h⟩
        have hx : x j = true := (raw x j).symm.trans hi
        apply (raw y j).trans
        cases hy : y j
        · have hbad := hxy j
          rw [hx,hy] at hbad
          exact False.elim ((by decide : ¬ (true ≤ false)) hbad)
        · rfl
      · simpa only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,ite_eq_right h] using hi
    let step := fun (a : List Bool) (u : Finset ℕ × Finset ℕ) =>
      a ++ [decide (∀ i ∈ u.1, a.getD i false = true) || decide (∀ i ∈ u.2, a.getD i false = true)]
    have advance (a b : List Bool) (hab : lew a b) (u : Finset ℕ × Finset ℕ) :
        lew (step a u) (step b u) := by
      refine ⟨by simp [step, hab.1], ?_⟩
      intro i hi
      by_cases h : i < a.length
      · have hb : i < b.length := hab.1 ▸ h
        simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,h,hb] using
          (hab.2 i (by simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,h] using hi))
      · have hb : ¬i < b.length := hab.1 ▸ h
        by_cases he : i = a.length
        · subst i
          have hp : (∀ i ∈ u.1, a.getD i false = true) ∨ (∀ i ∈ u.2, a.getD i false = true) := by
            simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append] using hi
          have hq : (∀ i ∈ u.1, b.getD i false = true) ∨ (∀ i ∈ u.2, b.getD i false = true) :=
            hp.imp (fun h i hi => hab.2 i (h i hi)) (fun h i hi => hab.2 i (h i hi))
          simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append,hab.1] using hq
        · have ht : (step a u).length ≤ i := by simp [step]; omega
          simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none ht] at hi
    have go (q : List (Finset ℕ × Finset ℕ)) (a b : List Bool) (h : lew a b) :
        lew (q.foldl step a) (q.foldl step b) := by
      induction q generalizing a b with
      | nil => simpa using h
      | cons u q ih => exact ih _ _ (advance a b h u)
    exact go r _ _ base
  have output_mono (x y : Fin 42 → Bool) (hxy : x ≤ y) (hx : ev R o x = true) : ev R o y = true :=
    decide_eq_true (fun i hi => (mono x y hxy R).2 i ((of_decide_eq_true hx) i hi))
  have exactR (x : Fin 42 → Bool) : ev R o x = true ↔ F x := by
    constructor
    · intro hx
      by_contra hn
      obtain ⟨y,hxy,hm⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬ F z) x hn
      have ind (z : Fin 42 → Bool) : ¬ F z ↔ ∀ p l : Fin 21, adj p l = true →
          z (Fin.castAdd 21 p) = false ∨ z (Fin.natAdd 21 l) = false := by
        constructor
        · intro hn p l hpl
          by_cases hp : z (Fin.castAdd 21 p) = true
          · exact Or.inr (Bool.eq_false_iff.mpr (fun hl => hn ⟨p,l,hpl,hp,hl⟩))
          · exact Or.inl (Bool.eq_false_iff.mpr hp)
        · rintro h ⟨p,l,hpl,hp,hl⟩
          rcases h p l hpl with hq | hq
          · exact Bool.false_ne_true (hq.symm.trans hp)
          · exact Bool.false_ne_true (hq.symm.trans hl)
      have leB {a b : Bool} (h : a = true → b = true) : a ≤ b := by
        cases a <;> cases b
        · decide
        · decide
        · exact (Bool.false_ne_true (h rfl)).elim
        · decide
      have hy := hneg y ((ind y).1 hm.1) (by
        intro z hz h
        have hyz : y ≤ z := fun i => leB (h i)
        exact le_antisymm (hm.2 ((ind z).2 hz) hyz) hyz)
      exact Bool.false_ne_true (hy.symm.trans (output_mono x y hxy hx))
    · rintro ⟨p,l,h,ha,hb⟩
      apply output_mono _ _ _ (hpos p l h)
      intro i
      change decide (i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l) ≤ x i
      by_cases f : i = Fin.castAdd 21 p ∨ i = Fin.natAdd 21 l
      · rw [decide_eq_true f]
        rcases f with rfl | rfl
        · rw [ha]
        · rw [hb]
      · rw [decide_eq_false f]
        exact bot_le
  let E := fun (r : List (Finset ℕ × Finset ℕ)) (o : Finset ℕ) (x : List Bool) =>
    let vs := r.foldl (fun v g => v ++ [decide (∀ i ∈ g.1, v.getD i false = true) ||
      decide (∀ i ∈ g.2, v.getD i false = true)]) (x ++ [false])
    decide (∀ i ∈ o, vs.getD i false = true)
  obtain ⟨S,A,u,a,size,compose⟩ := factor R o exactR
  let ag := fun (x : Fin 21 → Bool) => E A a (List.ofFn x)
  let su := fun (p : Fin 21) (y : Fin 21 → Bool) => E S (u p) (List.ofFn y)
  let z : Fin 21 → Bool := fun _ => false
  let one := fun (p i : Fin 21) => decide (i=p)
  have link (x y : Fin 21 → Bool) (h : x=z ∨ ∃ p, x=one p) :
      ag (fun i => x i && su i y) = true ↔
      ∃ p l, adj p l = true ∧ x p = true ∧ y l = true := by
    have cp : ag (fun i => x i && su i y) = ev R o (Fin.append x y) := compose x y h
    rw [cp,exactR]
    simp only [F, Fin.append_left, Fin.append_right]
  have zero : ag z = false := by
    apply Bool.eq_false_iff.mpr
    intro on
    have mask : (fun i => z i && su i z) = z := by funext i; simp [z]
    obtain ⟨p,l,_,hp,_⟩ := (link z z (.inl rfl)).mp (mask ▸ on)
    exact Bool.false_ne_true hp
  have single (p : Fin 21) (y : Fin 21 → Bool) :
      ag (if su p y = true then one p else z) = true ↔ ∃ l, adj p l = true ∧ y l = true := by
    have mask : (fun i => one p i && su i y) = if su p y = true then one p else z := by
      funext i
      by_cases eq : i=p <;> cases h : su p y <;> simp [one,z,eq,h]
    rw [← mask, link (one p) y (.inr ⟨p,rfl⟩)]
    constructor
    · rintro ⟨q,l,hp,hq,hl⟩
      have eq : q=p := of_decide_eq_true hq
      exact ⟨l,eq ▸ hp,hl⟩
    · rintro ⟨l,hp,hl⟩
      exact ⟨p,l,hp,by simp [one],hl⟩
  have both (p : Fin 21) (y : Fin 21 → Bool) (hit : ∃ l, adj p l = true ∧ y l = true) :
      su p y = true ∧ ag (one p) = true := by
    have pass := (single p y).mpr hit
    by_cases h : su p y = true
    · exact ⟨h,by simpa only [ite_eq_left h] using pass⟩
    · rw [ite_eq_right h,zero] at pass
      contradiction
  have accepts (p : Fin 21) : ag (one p) = true :=
    (both p (one p) ⟨p,by simp [adj],by simp [one]⟩).2
  have trueIff (p : Fin 21) (y : Fin 21 → Bool) :
      su p y = true ↔ ∃ l, adj p l = true ∧ y l = true := by
    constructor
    · intro h
      exact (single p y).mp (by rw [ite_eq_left h]; exact accepts p)
    · exact fun h => (both p y h).1
  have plus (p l : Fin 21) (h : adj p l = true) : su p (one l) = true :=
    (trueIff p (one l)).mpr ⟨l,h,by simp [one]⟩
  have minus (p : Fin 21) : su p (fun l => !(adj p l)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨l,yes,no⟩ := (trueIff p _).mp h
    simp [yes] at no
  have hs := joint S u plus minus
  have ha := aggregator A a zero accepts
  omega
