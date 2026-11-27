import Mathlib.Tactic
import PEqualNP.Defs

-- The search verifier follows the merged file L_meta_6339.lean of this repository, with the mask,
-- the symmetries and the certificate replaced; the certificate data are new.

namespace PEqualNP.Outside.L_meta_10157

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Mask := BitVec 25
def target : Mask := 8127577
def sources : List Mask := [31, 992, 31744, 1015808, 32505856, 1082401, 2164802, 4329604, 8659208, 17318416]
def allBits : Mask := BitVec.allOnes 25

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def act (isOr : Bool) (x y : Mask) : Mask :=
  if isOr then x ||| y else x &&& y

theorem act_bits (o : Bool) (a b : Mask) (i : Fin 25) :
    (act o a b)[i.val] = if o then a[i.val] || b[i.val] else a[i.val] && b[i.val] := by
  cases o <;> simp [act]

def gateMask (g : Gate) (w : List Mask) : Mask :=
  match g.inputs with
  | [] => if isAnd g.op then allBits else 0
  | [a] => w.getD a 0
  | a :: b :: _ => act (!(isAnd g.op)) (w.getD a 0) (w.getD b 0)

theorem gateMask_bits (g : Gate) (w : List Mask) (i : Fin 25)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    (gateMask g w)[i.val] =
      g.op.eval (g.inputs.map fun a => (w.map (fun v : Mask => v[i.val])).getD a false) := by
  have bitGet (a : ℕ) : (w.getD a 0)[i.val] = (w.map (fun v : Mask => v[i.val])).getD a false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    change (w[a]?.getD (0 : Mask)).getLsbD i.val = _
    generalize w[a]? = q
    cases q <;> simp
  rcases g with ⟨o,l⟩
  simp only at op arity
  rcases op with rfl | rfl <;>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil, gateMask, isAnd, ite_true, ite_false,
       Bool.not_true, Bool.not_false, act, GateOp.eval, List.map_cons, List.map_nil,
       List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
       Bool.or_false, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero, bitGet] at arity ⊢
  all_goals first
    | omega
    | exact BitVec.getElem_allOnes _ i.isLt
    | simp
  have fromSome (q : Option Mask) :
      (q.getD (0#25)).getLsbD i.val = (q.map (fun v : Mask => v.getLsbD i.val)).getD false := by
    cases q <;> simp
  simp only [← BitVec.getLsbD_eq_getElem i.isLt, fromSome]

def stage (w : List Mask) (g : Gate) := w ++ [gateMask g w]

theorem wireProjection (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List Mask) (i : Fin 25) :
    ((gs.foldl stage w).map (fun v : Mask => v[i.val])) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
        (w.map (fun v : Mask => v[i.val])) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hm => mono h (List.mem_cons_of_mem _ hm))]
    simp only [stage, List.map_append, List.map_cons, List.map_nil]
    rw [gateMask_bits g w i (mono g (by simp)).1 (mono g (by simp)).2]

def row (i : Fin 25) : List Bool :=
  oneEach (⟨i.val / 5, by omega⟩ : Fin 5) (⟨i.val % 5, by omega⟩ : Fin 5)

theorem source_projection : ∀ i : Fin 25, sources.map (fun v : Mask => v[i.val]) = row i := by
  decide

theorem evalMask (C : Circuit) (mono : Monotone2 C) (i : Fin 25) :
    ((C.gates.foldl stage sources).getD C.output 0)[i.val] = C.eval (row i) := by
  rw [Circuit.eval, Circuit.wires, ← source_projection i, ← wireProjection]
  · cases h : (C.gates.foldl stage sources)[C.output]? <;>
      simp [List.getD_eq_getElem?_getD, h]
  · intro g hg
    simpa using mono g hg

theorem evalTarget (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (8127577 : ℕ).testBit (5*u.val+v.val)) C) :
    (C.gates.foldl stage sources).getD C.output 0 = target := by
  apply BitVec.eq_of_getElem_eq
  intro i ilt
  rw [evalMask C mono ⟨i,ilt⟩]
  change C.eval (oneEach (⟨i / 5, by omega⟩ : Fin 5) (⟨i % 5, by omega⟩ : Fin 5)) = _
  rw [computes]
  have eq : 5*(i/5)+i % 5 = i := by omega
  change (8127577 : ℕ).testBit (5 * (i / 5) + i % 5) = _
  rw [eq]
  rfl

inductive Build : Finset Mask → ℕ → Prop
  | done {W} : target ∈ W → Build W 0
  | advance {W a b o k} : a ∈ W → b ∈ W → act o a b ∉ W →
      act o a b ≠ 0 → act o a b ≠ allBits →
      Build (insert (act o a b) W) k → Build W (k+1)

theorem basicGate (g : Gate) (w : List Mask)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    gateMask g w = 0 ∨ gateMask g w = allBits ∨ gateMask g w ∈ w ∨
      ∃ a ∈ w, ∃ b ∈ w, ∃ o : Bool, gateMask g w = act o a b := by
  have getMem (j : ℕ) : w.getD j 0 = 0 ∨ w.getD j 0 ∈ w := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : w[j]? with
    | none => simp
    | some v => exact Or.inr (List.mem_of_getElem? h)
  rcases g with ⟨op', l⟩
  change op' = .and ∨ op' = .or at op
  change l.length ≤ 2 at arity
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  · rcases op with rfl | rfl <;> simp [gateMask, isAnd]
  · rcases getMem a with z | m
    · exact Or.inl z
    · exact Or.inr (Or.inr (Or.inl m))
  · simp only [gateMask]
    rcases getMem a with ha | ha <;> rcases getMem b with hb | hb
    · rw [ha,hb]
      rcases op with rfl | rfl <;> simp [act, isAnd]
    · rw [ha]
      rcases op with rfl | rfl
      · simp [act, isAnd]
      · exact Or.inr (Or.inr (Or.inl (by
        change ((0 : Mask) ||| w.getD b 0) ∈ w
        rw [show (0 : Mask) ||| w.getD b 0 = w.getD b 0 from BitVec.zero_or]
        exact hb)))
    · rw [hb]
      rcases op with rfl | rfl
      · simp [act, isAnd]
      · exact Or.inr (Or.inr (Or.inl (by
        change (w.getD a 0 ||| (0 : Mask)) ∈ w
        rw [show w.getD a 0 ||| (0 : Mask) = w.getD a 0 from BitVec.or_zero]
        exact ha)))
    · exact Or.inr (Or.inr (Or.inr ⟨_,ha,_,hb,_,rfl⟩))
  · simp at arity

theorem buildFrom (gs : List Gate)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (w : List Mask) (W : Finset Mask)
    (inv : ∀ v ∈ w, v = 0 ∨ v = allBits ∨ v ∈ W)
    (endMem : target ∈ gs.foldl stage w) :
    ∃ k ≤ gs.length, Build W k := by
  induction gs generalizing w W with
  | nil =>
    have h : target ∈ w := endMem
    rcases inv target h with z | t | mem
    · contradiction
    · contradiction
    · exact ⟨0, by simp, .done mem⟩
  | cons g gs ih =>
    have mono' : ∀ h ∈ gs, (h.op = .and ∨ h.op = .or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => mono h (List.mem_cons_of_mem _ hh)
    by_cases already : gateMask g w = 0 ∨ gateMask g w = allBits ∨ gateMask g w ∈ W
    · have extend : ∀ v ∈ stage w g, v = 0 ∨ v = allBits ∨ v ∈ W := by
        intro v hv
        simp only [stage, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact inv _ hv
        · exact already
      obtain ⟨k,hk,b⟩ := ih mono' _ W extend endMem
      exact ⟨k, by simp; omega, b⟩
    · obtain ⟨a,ha,b,hb,o,eq⟩ : ∃ a ∈ w, ∃ b ∈ w, ∃ o : Bool,
          gateMask g w = act o a b := by
        have gate := mono g (by simp)
        rcases basicGate g w gate.1 gate.2 with z | t | mem | ex
        · exact (already (Or.inl z)).elim
        · exact (already (Or.inr (Or.inl t))).elim
        · exact (already (inv _ mem)).elim
        · exact ex
      have hz : act o a b ≠ 0 := fun h => already (Or.inl (eq.trans h))
      have ht : act o a b ≠ allBits := fun h => already (Or.inr (Or.inl (eq.trans h)))
      have hm : act o a b ∉ W := fun h => already (Or.inr (Or.inr (eq ▸ h)))
      have aw : a ∈ W := by
        rcases inv a ha with h | h | h
        · subst a
          cases o
          · exact (hz (by simp [act])).elim
          · have e : gateMask g w = b := eq.trans (by simp [act])
            exact (already (e ▸ inv _ hb)).elim
        · subst a
          cases o
          · have e : gateMask g w = b := eq.trans (by exact BitVec.allOnes_and)
            exact (already (e ▸ inv _ hb)).elim
          · exact (ht (by exact BitVec.allOnes_or)).elim
        · exact h
      have bw : b ∈ W := by
        rcases inv b hb with h | h | h
        · subst b
          cases o
          · exact (hz (by simp [act])).elim
          · have e : gateMask g w = a := eq.trans (by simp [act])
            exact (already (e ▸ inv _ ha)).elim
        · subst b
          cases o
          · have e : gateMask g w = a := eq.trans (by exact BitVec.and_allOnes)
            exact (already (e ▸ inv _ ha)).elim
          · exact (ht (by exact BitVec.or_allOnes)).elim
        · exact h
      have extend : ∀ v ∈ stage w g, v = 0 ∨ v = allBits ∨ v ∈ insert (act o a b) W := by
        intro v hv
        simp only [stage, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact (inv _ hv).imp_right (Or.imp_right (fun h => Finset.mem_insert_of_mem h))
        · simp [eq]
      obtain ⟨k,hk,d⟩ := ih mono' _ _ extend endMem
      exact ⟨k+1, by simpa using hk, .advance aw bw hm hz ht d⟩

theorem representsBuild (C : Circuit) (mono : Monotone2 C)
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (8127577 : ℕ).testBit (5*u.val+v.val)) C) :
    ∃ k ≤ C.size, Build sources.toFinset k := by
  have targetOutput := evalTarget C mono computes
  have targetMem : target ∈ C.gates.foldl stage sources := by
    simp only [List.getD_eq_getElem?_getD] at targetOutput
    cases h : (C.gates.foldl stage sources)[C.output]? with
    | none => simp [h, target] at targetOutput
    | some x =>
      simp only [h, Option.getD_some] at targetOutput
      exact targetOutput ▸ List.mem_of_getElem? h
  exact buildFrom C.gates (by intro g hg; simpa using mono g hg) _ _
    (by intro v hv; exact Or.inr (Or.inr (List.mem_toFinset.mpr hv))) targetMem


inductive Reach : Finset Mask → ℕ → Prop
  | done : Reach {target} 0
  | advance {W R a b o k} : a ∈ W → b ∈ W → act o a b ∉ W →
      act o a b ≠ 0 → act o a b ≠ allBits →
      R ⊆ W → W ⊆ insert a (insert b R) →
      Reach (insert (act o a b) R) k → Reach W (k+1)

theorem buildReach {W : Finset Mask} {k : ℕ} (b : Build W k) :
    ∃ U ⊆ W, ∃ j ≤ k, Reach U j := by
  induction b with
  | done h => exact ⟨{target}, by simpa, 0, le_rfl, .done⟩
  | @advance W a b o k aw bw fresh nz nt _ ih =>
    obtain ⟨D, sub, j, jle, reach⟩ := ih
    let v := act o a b
    by_cases hv : v ∈ D
    · let R := D.erase v
      let U := insert a (insert b R)
      have rsub : R ⊆ W := by
        intro x hx
        have xx := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (sub xx.2)).resolve_left xx.1
      have usub : U ⊆ W := Finset.insert_subset_iff.mpr ⟨aw,
        Finset.insert_subset_iff.mpr ⟨bw,rsub⟩⟩
      have dEq : insert v R = D := Finset.insert_erase hv
      refine ⟨U,usub,j+1,Nat.succ_le_succ jle,.advance (R := R) (a := a) (b := b) (o := o) (by simp [U]) (by simp [U])
        (fun h => fresh (usub h)) nz nt (fun x hx => by simp [U,hx]) (by rfl) ?_⟩
      exact dEq ▸ reach
    · refine ⟨D, ?_, j, by omega, reach⟩
      intro x hx
      exact (Finset.mem_insert.mp (sub hx)).resolve_left (fun e => hv (e ▸ hx : act o a b ∈ D))

theorem reachCard {W : Finset Mask} {k : ℕ} (h : Reach W k) : W.card ≤ k+1 := by
  induction h with
  | done => simp
  | @advance W R a b o k _ _ fresh _ _ sub small _ ih =>
    rw [Finset.card_insert_of_notMem (fun h => fresh (sub h))] at ih
    have ub := (Finset.card_le_card small).trans
      ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _)))
    omega

def Separates (W : Finset Mask) : Prop :=
  ∀ p n : Fin 25, target[p.val] = true → target[n.val] = false →
    ∃ w ∈ W, w[p.val] = true ∧ w[n.val] = false

theorem splitSeparation {o : Bool} {a b : Mask} {p n : Fin 25}
    (yes : (act o a b)[p.val] = true) (no : (act o a b)[n.val] = false) :
    (a[p.val] = true ∧ a[n.val] = false) ∨ (b[p.val] = true ∧ b[n.val] = false) := by
  rw [act_bits] at yes no
  cases o <;> simp_all only [ite_true, ite_false, Bool.false_eq_true,
    Bool.and_eq_true, Bool.and_eq_false_iff, Bool.or_eq_true, Bool.or_eq_false_iff] <;> tauto

theorem reachSeparates {W : Finset Mask} {k : ℕ} (h : Reach W k) : Separates W := by
  intro p n hp hn
  induction h with
  | done => exact ⟨target, by simp, hp, hn⟩
  | @advance W R a b o k am bm _ _ _ sub _ _ ih =>
    obtain ⟨w, hw, yes, no⟩ := ih
    rcases Finset.mem_insert.mp hw with rfl | old
    · rcases splitSeparation yes no with h | h
      · exact ⟨a,am,h⟩
      · exact ⟨b,bm,h⟩
    · exact ⟨w,sub old,yes,no⟩

def criticalPairs : List (Fin 25 × Fin 25) :=
  [(0,5), (6,1), (10,5), (18,8), (20,5), (0,1), (6,5), (22,23), (3,1), (4,1)]

theorem essentialData : ∀ i : Fin 10,
    let (p,n) := criticalPairs[i.val]'(by exact i.isLt)
    target[p.val] = true ∧ target[n.val] = false ∧
    ∀ j : Fin 10, (sources[j.val]'(by exact j.isLt))[p.val] = true →
      (sources[j.val]'(by exact j.isLt))[n.val] = false → j = i := by
  decide +kernel

theorem allSources (W : Finset Mask) (hW : W ⊆ sources.toFinset)
    (sep : Separates W) : W = sources.toFinset := by
  apply Finset.Subset.antisymm hW
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
  let j : Fin 10 := ⟨i, by simpa [sources] using hi⟩
  have key := essentialData j
  obtain ⟨v, hv, yes, no⟩ := sep _ _ key.1 key.2.1
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp (hW hv))
  let q : Fin 10 := ⟨t, by simpa [sources] using ht⟩
  have equal := key.2.2 q yes no
  have hv' : sources[q.val]'q.isLt ∈ W := hv
  change sources[j.val]'j.isLt ∈ W
  exact (congrArg (fun i : Fin 10 => sources[i.val]'i.isLt) equal) ▸ hv'

def positive (i : Fin 10) : ℕ := ([0,3,4,6,10,18,19,20,21,22] : List ℕ)[i.val]'i.isLt
def negative (i : Fin 15) : ℕ := ([1,2,5,7,8,9,11,12,13,14,15,16,17,23,24] : List ℕ)[i.val]'i.isLt

def active (b : Bool) (w : BitVec 150) : BitVec 150 := if b then w else 0

theorem active_bit (b : Bool) (w : BitVec 150) (i : ℕ) :
    (active b w).getLsbD i = (b && w.getLsbD i) := by cases b <;> simp [active]

def spreadYes (x : Mask) : BitVec 150 :=
  active (x.getLsbD 0) 32767 |||
  active (x.getLsbD 3) 1073709056 |||
  active (x.getLsbD 4) 35183298347008 |||
  active (x.getLsbD 6) 1152886320234758144 |||
  active (x.getLsbD 10) 37777778941452554862592 |||
  active (x.getLsbD 18) 1237902260353517317737414656 |||
  active (x.getLsbD 19) 40563581267264055467619603447808 |||
  active (x.getLsbD 20) 1329187430965708569562959165777772544 |||
  active (x.getLsbD 21) 43554813737884338407439045944206050721792 |||
  active (x.getLsbD 22) 1427204136562994000934962657499743870051680256

def spreadNo (x : Mask) : BitVec 150 :=
  active (!x.getLsbD 1) 43557472234441965424307564606143227527169 |||
  active (!x.getLsbD 2) 87114944468883930848615129212286455054338 |||
  active (!x.getLsbD 5) 174229888937767861697230258424572910108676 |||
  active (!x.getLsbD 7) 348459777875535723394460516849145820217352 |||
  active (!x.getLsbD 8) 696919555751071446788921033698291640434704 |||
  active (!x.getLsbD 9) 1393839111502142893577842067396583280869408 |||
  active (!x.getLsbD 11) 2787678223004285787155684134793166561738816 |||
  active (!x.getLsbD 12) 5575356446008571574311368269586333123477632 |||
  active (!x.getLsbD 13) 11150712892017143148622736539172666246955264 |||
  active (!x.getLsbD 14) 22301425784034286297245473078345332493910528 |||
  active (!x.getLsbD 15) 44602851568068572594490946156690664987821056 |||
  active (!x.getLsbD 16) 89205703136137145188981892313381329975642112 |||
  active (!x.getLsbD 17) 178411406272274290377963784626762659951284224 |||
  active (!x.getLsbD 23) 356822812544548580755927569253525319902568448 |||
  active (!x.getLsbD 24) 713645625089097161511855138507050639805136896

def spread (x : Mask) : BitVec 150 := spreadYes x &&& spreadNo x

theorem active_get (b : Bool) (w : BitVec 150) (i : ℕ) (h : i < 150) :
    (active b w)[i] = (b && w[i]) := by
  cases b <;> simp [active]

theorem yes_bit (x : Mask) (i : Fin 10) (j : Fin 15) :
    (spreadYes x).getLsbD (15*i.val+j.val) = x.getLsbD (positive i) := by
  fin_cases i <;> fin_cases j <;>
    simp [spreadYes, positive, active_bit, active_get, BitVec.getLsbD_or]

theorem no_bit (x : Mask) (i : Fin 10) (j : Fin 15) :
    (spreadNo x).getLsbD (15*i.val+j.val) = !(x.getLsbD (negative j)) := by
  fin_cases i <;> fin_cases j <;>
    simp [spreadNo, negative, active_bit, active_get, BitVec.getLsbD_or]

def coverage : List Mask → BitVec 150 :=
  List.rec 0 (fun a _ cov => spread a ||| cov)

theorem coverageBit (W : List Mask) (i : Fin 10) (j : Fin 15) :
    (coverage W).getLsbD (15*i.val+j.val) = true ↔
      ∃ w ∈ W, w.getLsbD (positive i) = true ∧ w.getLsbD (negative j) = false := by
  induction W with
  | nil => simp [coverage]
  | cons a W ih =>
    change ((spread a ||| coverage W).getLsbD (15*i.val+j.val) = true) ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    rw [show (spread a).getLsbD (15*i.val+j.val) =
        (a.getLsbD (positive i) && !a.getLsbD (negative j)) by
      simp only [spread, BitVec.getLsbD_and, yes_bit, no_bit]]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.mem_cons]
    constructor
    · rintro (ha | ⟨v,vm,hv⟩)
      · exact ⟨a,Or.inl rfl,ha⟩
      · exact ⟨v,Or.inr vm,hv⟩
    · rintro ⟨v, rfl | vm, hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨v,vm,hv⟩

theorem listedPositions : ∀ (i : Fin 10) (j : Fin 15),
    positive i < 25 ∧ negative j < 25 ∧
      target.getLsbD (positive i) = true ∧ target.getLsbD (negative j) = false := by decide

theorem covered {W : List Mask} (sep : Separates W.toFinset) :
    coverage W = BitVec.allOnes 150 := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  let i : Fin 10 := ⟨k/15, by omega⟩
  let j : Fin 15 := ⟨k % 15, by omega⟩
  have h := listedPositions i j
  have p := h.2.2.1
  have n := h.2.2.2
  rw [BitVec.getLsbD_eq_getElem h.1] at p
  rw [BitVec.getLsbD_eq_getElem h.2.1] at n
  obtain ⟨w,wm,a,b⟩ := sep ⟨positive i,h.1⟩ ⟨negative j,h.2.1⟩ p n
  have hit := (coverageBit W i j).mpr ⟨w,List.mem_toFinset.mp wm,
    by rw [BitVec.getLsbD_eq_getElem h.1]; exact a,
    by rw [BitVec.getLsbD_eq_getElem h.2.1]; exact b⟩
  change (coverage W).getLsbD (15*(k/15)+k % 15) = true at hit
  rw [show 15*(k/15)+k % 15 = k by omega, BitVec.getLsbD_eq_getElem hk] at hit
  rw [hit, BitVec.getElem_allOnes]

theorem act_comm (o : Bool) (a b : Mask) : act o a b = act o b a := by
  cases o <;> simp [act, BitVec.and_comm, BitVec.or_comm]

theorem act_self (o : Bool) (a : Mask) : act o a a = a := by
  cases o <;> simp [act]

inductive Keys where
  | leaf (keys : List ℕ)
  | branch (boundary : ℕ) (left right : Keys)

noncomputable def Keys.all (T : Keys) (test : ℕ → Bool) : Bool :=
  Keys.rec (fun xs => xs.all test) (fun _ _ _ a b => a && b) T

noncomputable def Keys.find (T : Keys) (q : ℕ) : Bool :=
  Keys.rec (fun xs => xs.any (Nat.beq q))
    (fun b _ _ left right => if q < b then left else right) T

theorem searched {T : Keys} {test : ℕ → Bool} {q : ℕ}
    (pass : T.all test = true) (hit : T.find q = true) :
    test q = true := by
  induction T with
  | leaf xs =>
    obtain ⟨k,mem,found⟩ := List.any_eq_true.mp hit
    have eq : q = k := Nat.eq_of_beq_eq_true found
    exact eq ▸ List.all_eq_true.mp pass k mem
  | branch b l r il ir =>
    have passes : l.all test = true ∧ r.all test = true := by simpa only [Keys.all, Keys.rec, Bool.and_eq_true] using pass
    by_cases cut : q < b
    · exact il passes.1 (by simpa [Keys.find, cut] using hit)
    · exact ir passes.2 (by simpa [Keys.find, cut] using hit)

def key (W : List Mask) : ℕ :=
  W.foldr (fun x k => x.toNat + 33554432 * k) 1

def decodeFixed : ℕ → ℕ → List Mask :=
  Nat.rec (fun _ => []) (fun _ rec x =>
    if x ≤ 1 then [] else BitVec.ofNat 25 (x % 33554432) :: rec (x / 33554432))

def decodeKey (x : ℕ) : List Mask := decodeFixed 13 x

def insertW (a : Mask) : List Mask → List Mask :=
  List.rec [a] (fun b bs put => Bool.rec (b :: put) (a :: b :: bs) (Nat.ble a.toNat b.toNat))

def sortW : List Mask → List Mask :=
  List.rec [] (fun a _ ws => insertW a ws)

theorem insertMem (x a : Mask) (ws : List Mask) : x ∈ insertW a ws ↔ x = a ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertW]
  | cons b bs ih =>
    change x ∈ Bool.rec (motive := fun _ => List Mask) (b :: insertW a bs) (a :: b :: bs) (Nat.ble a.toNat b.toNat) ↔ _
    cases Nat.ble a.toNat b.toNat
    · simp only [Bool.rec, List.mem_cons, ih]
      tauto
    · simp [List.mem_cons]

theorem sortFinset (W : List Mask) : (sortW W).toFinset = W.toFinset := by
  ext x
  simp only [List.mem_toFinset]
  induction W with
  | nil => rfl
  | cons w W ih =>
    change x ∈ insertW w (sortW W) ↔ _
    simp only [insertMem, ih, List.mem_cons]

def Rejects (k : ℕ) (T : Keys) : Prop :=
  ∀ q, T.find q = true → ∀ j ≤ k, ¬ Reach (decodeKey q).toFinset j

def automPositions : List (List (Fin 25)) := [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,2,4,3,5,6,7,9,8,10,11,12,14,13,15,16,17,19,18,20,21,22,24,23]]

def coord (s : Fin 2) (i : Fin 25) : Fin 25 :=
  (automPositions[s.val]'s.isLt)[i.val]'(by fin_cases s <;> exact i.isLt)

theorem coordInj : ∀ (s : Fin 2) (i j : Fin 25), coord s i = coord s j → i = j := by
  decide +kernel

def remap (s : Fin 2) (x : Mask) : Mask :=
  (BitVec.ofBoolListLE (List.ofFn fun i => x[(coord s i).val])).cast (by simp)

theorem remapBit (s : Fin 2) (x : Mask) (i : Fin 25) :
    (remap s x)[i.val] = x[(coord s i).val] := by
  rw [← BitVec.getLsbD_eq_getElem i.isLt, remap, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]

theorem remapInj (s : Fin 2) : Function.Injective (remap s) := by
  intro x y e
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp (coordInj s)) ⟨j,hj⟩
  have b := congrArg (fun a : Mask => a[i.val]) e
  simpa only [remapBit, hi] using b

theorem remapAct (s : Fin 2) (o : Bool) (a b : Mask) :
    remap s (act o a b) = act o (remap s a) (remap s b) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  change (remap s (act o a b))[(⟨j,hj⟩ : Fin 25).val] =
    (act o (remap s a) (remap s b))[(⟨j,hj⟩ : Fin 25).val]
  let i : Fin 25 := ⟨j,hj⟩
  rw [remapBit s (act o a b) i, act_bits o a b (coord s i), act_bits o _ _ i,
    remapBit s a i, remapBit s b i]

theorem remapFixed :
    ∀ s : Fin 2, remap s target = target ∧ remap s 0 = 0 ∧ remap s allBits = allBits := by
  decide +kernel

theorem mappedReach (s : Fin 2) {W : Finset Mask} {k : ℕ} (h : Reach W k) :
    Reach (W.image (remap s)) k := by
  induction h with
  | done =>
    simpa only [Finset.image_singleton, (remapFixed s).1] using Reach.done
  | @advance W R a b o k am bm fresh nz nt sub bound h ih =>
    have result := remapAct s o a b
    rw [Finset.image_insert, result] at ih
    apply Reach.advance (Finset.mem_image_of_mem _ am) (Finset.mem_image_of_mem _ bm)
      (R := R.image (remap s)) (o := o) _ _ _ (Finset.image_subset_image sub) _ ih
    · rw [← result]
      intro h
      obtain ⟨x,xm,eq⟩ := Finset.mem_image.mp h
      exact fresh ((remapInj s eq) ▸ xm)
    · rw [← result, ← (remapFixed s).2.1]
      exact fun h => nz (remapInj s h)
    · rw [← result, ← (remapFixed s).2.2]
      exact fun h => nt (remapInj s h)
    · simpa only [Finset.image_insert] using Finset.image_subset_image (f := remap s) bound

def remapFast (s : Fin 2) (x : Mask) : Mask :=
  match s.val with
  | 0 => (x &&& 33554431)
  | _ => ((x &&& 17318416) >>> (1 : ℕ)) ||| (x &&& 7576807) ||| ((x &&& 8659208) <<< (1 : ℕ))

set_option maxHeartbeats 0 in
theorem remapFast_bit (s : Fin 2) (x : Mask) (j : Fin 25) :
    (remapFast s x).getLsbD j.val = x.getLsbD (coord s j).val := by
  fin_cases s <;> fin_cases j <;>
    simp [remapFast, coord, automPositions, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_and]

theorem remapFast_eq (s : Fin 2) (x : Mask) : remapFast s x = remap s x := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let i : Fin 25 := ⟨j,hj⟩
  calc
    (remapFast s x)[j] = (remapFast s x).getLsbD j := (BitVec.getLsbD_eq_getElem hj).symm
    _ = x.getLsbD (coord s i).val := remapFast_bit s x i
    _ = x[(coord s i).val] := BitVec.getLsbD_eq_getElem (coord s i).isLt
    _ = (remap s x)[j] := (remapBit s x i).symm

abbrev Wire := ℕ × ℕ × ℕ

def natAct (o : Bool) (a b : ℕ) : ℕ := Bool.rec (Nat.land a b) (Nat.lor a b) o

def fuse (o : Bool) (a b : Wire) : Wire :=
  (natAct o a.1 b.1, natAct o a.2.1 b.2.1, natAct (!o) a.2.2 b.2.2)

def mark (x : ℕ) : Wire :=
  let m := BitVec.ofNat 25 x
  (x, (spreadYes m).toNat, (spreadNo m).toNat)

def coverWire (w : Wire) : ℕ := Nat.land w.2.1 w.2.2
def all64 : ℕ := 1427247692705959881058285969449495136382746623

def stripAB (a b : ℕ) : List Wire → List Wire × ℕ :=
  List.rec ([], 0) (fun w _ p =>
    Bool.rec (w :: p.1, Nat.lor (coverWire w) p.2) p
       (Nat.beq a w.1 || Nat.beq b w.1))

def includeWire (x : Wire) (keep : Bool) (xs : List Wire) : List Wire :=
  Bool.rec xs (x :: xs) keep

def coverExtra (x : Wire) (keep : Bool) (c : ℕ) : ℕ :=
  Bool.rec c (Nat.lor (coverWire x) c) keep

noncomputable def fastChild (k : ℕ) (T : List Wire → Bool) (W : List Wire)
    (a b g : Wire) (strip : List Wire × ℕ) (ka kb : Bool) : Bool :=
  let c := Nat.lor (coverWire g) (coverExtra a ka (coverExtra b kb strip.2))
  Bool.rec false
    (let V := g :: includeWire a ka (includeWire b kb strip.1)
     if V.length > k+1 then false
     else if V.any (fun w => Nat.beq w.1 8127577) then true
     else if k == 0 then false
     else !(T V))
    (Nat.beq c all64)

noncomputable def fastAct (k : ℕ) (T : List Wire → Bool) (W : List Wire)
    (a b : Wire) (strip : List Wire × ℕ) (o : Bool) : Bool :=
  let g := fuse o a b
  Bool.rec
    (fastChild k T W a b g strip false false ||
     fastChild k T W a b g strip false true ||
     fastChild k T W a b g strip true false ||
     fastChild k T W a b g strip true true)
    false (Nat.beq g.1 0 || Nat.beq g.1 33554431 || W.any (fun w => Nat.beq w.1 g.1))

noncomputable def fastPair (k : ℕ) (T : List Wire → Bool) (W : List Wire) (a b : Wire) : Bool :=
  Bool.rec false
    (let strip := stripAB a.1 b.1 W
     fastAct k T W a b strip false || fastAct k T W a b strip true)
    (Nat.blt a.1 b.1)

noncomputable def checkWires (k : ℕ) (T : List Wire → Bool) (W : List Wire) : Bool :=
  !(W.any (fun w => Nat.beq w.1 8127577) || W.any (fun a => W.any (fastPair k T W a)))

def marked (m : Mask) : Wire := mark m.toNat

theorem marked_form (m : Mask) :
    marked m = (m.toNat, (spreadYes m).toNat, (spreadNo m).toNat) := by
  simp [marked, mark]

theorem bit64Matrix (k : ℕ) (hk : k < 150) :
    ∃ (i : Fin 10) (j : Fin 15), 15*i.val+j.val = k :=
  ⟨⟨k/15, by omega⟩, ⟨k % 15, by omega⟩, by change 15*(k/15)+k % 15 = k; omega⟩

theorem spreadYesAct (o : Bool) (a b : Mask) :
    spreadYes (act o a b) =
      if o then spreadYes a ||| spreadYes b else spreadYes a &&& spreadYes b := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  obtain ⟨i,j,rfl⟩ := bit64Matrix k hk
  simp only [← BitVec.getLsbD_eq_getElem hk]
  cases o <;> simp only [Bool.false_eq_true, ite_true, ite_false, yes_bit, act,
    BitVec.getLsbD_or, BitVec.getLsbD_and]

theorem spreadNoAct (o : Bool) (a b : Mask) :
    spreadNo (act o a b) =
      if o then spreadNo a &&& spreadNo b else spreadNo a ||| spreadNo b := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  obtain ⟨i,j,rfl⟩ := bit64Matrix k hk
  simp only [← BitVec.getLsbD_eq_getElem hk]
  cases o <;> simp only [Bool.false_eq_true, ite_true, ite_false, no_bit, act,
    BitVec.getLsbD_or, BitVec.getLsbD_and, Bool.not_and, Bool.not_or]

theorem fuse_mark (o : Bool) (a b : Mask) :
    fuse o (marked a) (marked b) = marked (act o a b) := by
  rw [marked_form a, marked_form b, marked_form (act o a b), spreadYesAct, spreadNoAct]
  cases o <;> simp [fuse, natAct, act, BitVec.toNat_and, BitVec.toNat_or]

def coverN : List Wire → ℕ :=
  List.rec 0 (fun w _ c => Nat.lor (coverWire w) c)

theorem cover_marked (L : List Mask) : coverN (L.map marked) = (coverage L).toNat := by
  induction L with
  | nil => rfl
  | cons m L ih =>
    change Nat.lor (coverWire (marked m)) (coverN (L.map marked)) =
      (spread m ||| coverage L).toNat
    rw [ih]
    simp [coverWire, marked_form, spread, BitVec.toNat_and, BitVec.toNat_or]

theorem strip_spec (a b : ℕ) (W : List Wire) :
    (stripAB a b W).1 = W.filter (fun x => !(Nat.beq a x.1 || Nat.beq b x.1)) ∧
    (stripAB a b W).2 = coverN (stripAB a b W).1 := by
  induction W with
  | nil => exact ⟨rfl,rfl⟩
  | cons x W ih =>
    let p := stripAB a b W
    let out := Bool.rec (motive := fun _ => List Wire × ℕ)
      (x :: p.1, Nat.lor (coverWire x) p.2) p (Nat.beq a x.1 || Nat.beq b x.1)
    change out.1 = _ ∧ out.2 = coverN out.1
    cases h : (Nat.beq a x.1 || Nat.beq b x.1)
    · have L : out.1 = x :: p.1 := by simp only [out,h,Bool.rec]
      have c : out.2 = Nat.lor (coverWire x) p.2 := by simp only [out,h,Bool.rec]
      rw [L,c,List.filter_cons, h]
      exact ⟨congrArg (x :: ·) ih.1, congrArg (Nat.lor (coverWire x)) ih.2⟩
    · have L : out.1 = p.1 := by simp only [out,h,Bool.rec]
      have c : out.2 = p.2 := by simp only [out,h,Bool.rec]
      rw [L,c,List.filter_cons,h]
      exact ih

def addIf {α : Type} (a : α) (b : Bool) (L : List α) : List α :=
  Bool.rec L (a :: L) b

theorem addIf_map {α β : Type} (f : α → β) (a : α) (b : Bool) (L : List α) :
    (addIf a b L).map f = addIf (f a) b (L.map f) := by cases b <;> rfl

theorem coverExtra_eq (a : Wire) (b : Bool) (L : List Wire) :
    coverExtra a b (coverN L) = coverN (includeWire a b L) := by cases b <;> rfl

theorem naturalMask (m : Mask) : BitVec.ofNat 25 (marked m).1 = m := by simp [marked_form]
theorem markedNat (m : Mask) : (marked m).1 = m.toNat := by simp [marked_form]

theorem targetMarked (L : List Mask) :
    ((L.map marked).any (fun w => Nat.beq w.1 8127577)) = true ↔ target ∈ L := by
  simp only [List.any_eq_true, List.mem_map, target, markedNat]
  constructor
  · rintro ⟨w, ⟨m,hm,rfl⟩,he⟩
    exact (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true he :
      m.toNat = (8127577 : Mask).toNat)) ▸ hm
  · intro h
    exact ⟨marked 8127577,⟨8127577,h,rfl⟩,rfl⟩

def SoundK (k : ℕ) (T : List Wire → Bool) : Prop :=
  ∀ L : List Mask, L.Nodup → ∀ j ≤ k, Reach L.toFinset j → T (L.map marked) = false

theorem fastChild_true {k : ℕ} {T : List Wire → Bool} (pr : SoundK k T)
    (W : List Wire) (a b g : Wire) (strip : List Wire × ℕ)
    (ha : strip.2 = coverN strip.1) (ka kb : Bool) (L : List Mask)
    (eq : g :: includeWire a ka (includeWire b kb strip.1) = L.map marked)
    (distinct : L.Nodup) (j : ℕ) (le : j ≤ k) (reach : Reach L.toFinset j) :
    fastChild k T W a b g strip ka kb = true := by
  have m := covered (reachSeparates reach)
  have digest :
      Nat.lor (coverWire g) (coverExtra a ka (coverExtra b kb strip.2)) = all64 := by
    rw [ha, coverExtra_eq, coverExtra_eq]
    change coverN (g :: includeWire a ka (includeWire b kb strip.1)) = all64
    rw [eq, cover_marked, m]
    rfl
  have bound : L.length ≤ k+1 := by
    rw [← List.toFinset_card_of_nodup distinct]
    exact (reachCard reach).trans (by omega)
  unfold fastChild
  simp only [digest, show Nat.beq all64 all64 = true from rfl, Bool.rec, eq, List.length_map,
    bound.not_gt, ite_false]
  by_cases mem : target ∈ L
  · rw [if_pos ((targetMarked L).mpr mem)]
  have lacks : ((L.map marked).any (fun w => Nat.beq w.1 8127577)) = false :=
    Bool.eq_false_iff.mpr (fun h => mem ((targetMarked L).mp h))
  have nk : k ≠ 0 := by
    intro z
    have jz : j = 0 := by omega
    subst j
    generalize hs : L.toFinset = U at reach
    cases reach
    apply mem
    apply List.mem_toFinset.mp
    rw [hs]
    exact Finset.mem_singleton_self _
  rw [lacks]
  simp only [Bool.false_eq_true, ite_false, beq_eq_false_iff_ne.mpr nk,
    pr L distinct j le reach, Bool.not_false]


def withoutAB (L : List Mask) (a b : Mask) : List Mask :=
  L.filter (fun x => !(Nat.beq a.toNat x.toNat || Nat.beq b.toNat x.toNat))

theorem without_mem (L : List Mask) (a b x : Mask) :
    x ∈ withoutAB L a b ↔ x ∈ L ∧ x ≠ a ∧ x ≠ b := by
  simp only [withoutAB, List.mem_filter, Bool.not_eq_true', Bool.or_eq_false_iff,
    show ∀ a b : ℕ, a.beq b = false ↔ a ≠ b from by
      intro a b
      constructor
      · exact Nat.ne_of_beq_eq_false
      · intro ne
        apply Bool.eq_false_iff.mpr
        exact fun eq => ne (Nat.eq_of_beq_eq_true eq),
    show ∀ p q : Mask, p.toNat ≠ q.toNat ↔ p ≠ q from fun p q =>
      not_congr ⟨BitVec.eq_of_toNat_eq, congrArg BitVec.toNat⟩, ne_comm]

theorem strip_marked (L : List Mask) (a b : Mask) :
    (stripAB a.toNat b.toNat (L.map marked)).1 = (withoutAB L a b).map marked := by
  rw [(strip_spec _ _ _).1]
  induction L with
  | nil => rfl
  | cons v L ih =>
    unfold withoutAB at *
    simp only [List.map_cons, List.filter_cons, markedNat, ih]
    split <;> rfl

theorem filteredRest (L : List Mask) (R : Finset Mask) (a b : Mask)
    (am : a ∈ L) (bm : b ∈ L) (ab : a ≠ b) (distinct : L.Nodup)
    (sub : R ⊆ L.toFinset) (bound : L.toFinset ⊆ insert a (insert b R)) :
    let K := addIf a (decide (a ∈ R)) (addIf b (decide (b ∈ R)) (withoutAB L a b))
    K.toFinset = R ∧ K.Nodup ∧ ∀ x ∈ K, x ∈ L := by
  let base := withoutAB L a b
  have baseND : base.Nodup := distinct.filter _
  have offA : a ∉ base := fun h => (without_mem L a b a).mp h |>.2.1 rfl
  have offB : b ∉ base := fun h => (without_mem L a b b).mp h |>.2.2 rfl
  have oldOnly (x : Mask) : x ∈ base → x ∈ R := by
    intro h
    obtain ⟨m,xneA,xneB⟩ := (without_mem L a b x).mp h
    have hm := bound (List.mem_toFinset.mpr m)
    exact (Finset.mem_insert.mp ((Finset.mem_insert.mp hm).resolve_left xneA)).resolve_left xneB
  have ca (x : Mask) (hx : x ∈ R) : x ∈ L := List.mem_toFinset.mp (sub hx)
  change (addIf a _ (addIf b _ base)).toFinset = R ∧ (addIf a _ (addIf b _ base)).Nodup ∧ _
  constructor
  · ext x
    rw [List.mem_toFinset]
    simp only [addIf]
    by_cases aa : a ∈ R <;> by_cases bb : b ∈ R
    all_goals
      simp only [aa, bb, decide_true, decide_false, Bool.rec, List.mem_cons]
      constructor
      · intro h
        first
        | exact oldOnly x h
        | rcases h with rfl | rfl | h <;> first | assumption | exact oldOnly x h
        | rcases h with rfl | h <;> first | assumption | exact oldOnly x h
      · intro hx
        by_cases xa : x = a
        · subst x
          first | exact Or.inl rfl | exact (aa hx).elim
        by_cases xb : x = b
        · subst x
          first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact (bb hx).elim
        have hb : x ∈ base := (without_mem L a b x).mpr ⟨ca x hx,xa,xb⟩
        first | exact hb | exact Or.inr hb | exact Or.inr (Or.inr hb)
  · by_cases aa : a ∈ R <;> by_cases bb : b ∈ R <;>
      simp only [addIf, aa, bb, decide_true, decide_false, Bool.rec]
    all_goals
      constructor
      · simp [List.nodup_cons, offA, offB, ab, baseND]
      · intro x hx
        try simp only [List.mem_cons] at hx
        first
        | exact ((without_mem L a b x).mp hx).1
        | rcases hx with rfl | rfl | h <;> first | assumption | exact ((without_mem L a b x).mp h).1
        | rcases hx with rfl | h <;> first | assumption | exact ((without_mem L a b x).mp h).1

theorem fastPair_true {k : ℕ} {T : List Wire → Bool} (pr : SoundK k T)
    (L : List Mask) (R : Finset Mask) (distinct : L.Nodup) (a b : Mask)
    (am : a ∈ L) (bm : b ∈ L) (ord : a.toNat < b.toNat) (o : Bool)
    (fresh : act o a b ∉ L) (nz : act o a b ≠ 0) (nt : act o a b ≠ allBits)
    (sub : R ⊆ L.toFinset) (bound : L.toFinset ⊆ insert a (insert b R))
    (j : ℕ) (le : j ≤ k) (reach : Reach (insert (act o a b) R) j) :
    fastPair k T (L.map marked) (marked a) (marked b) = true := by
  let g := act o a b
  have ab : a ≠ b := fun e => (show ¬ a.toNat < a.toNat from Nat.lt_irrefl _) (e ▸ ord)
  let ka := decide (a ∈ R)
  let kb := decide (b ∈ R)
  let K := addIf a ka (addIf b kb (withoutAB L a b))
  obtain ⟨Kset,Knd,Ksub⟩ := filteredRest L R a b am bm ab distinct sub bound
  let Tgt := g :: K
  have TgtNd : Tgt.Nodup := List.nodup_cons.mpr ⟨fun h => fresh (Ksub _ h),Knd⟩
  have TgtEq : Tgt.toFinset = insert (act o a b) R := by
    rw [show Tgt = g :: K from rfl,List.toFinset_cons]
    rw [Kset]
  have child :=
    fastChild_true pr (L.map marked) (marked a) (marked b) (marked g)
      (stripAB a.toNat b.toNat (L.map marked)) (strip_spec _ _ _).2 ka kb Tgt
      (by rw [strip_marked, show Tgt = g :: K from rfl, List.map_cons]
          change _ = marked g :: (addIf a ka (addIf b kb (withoutAB L a b))).map marked
          simp only [addIf_map]
          cases ka <;> cases kb <;> rfl)
      TgtNd j le (TgtEq.symm ▸ reach)
  have cmp := (Nat.blt_eq.mpr ord : Nat.blt a.toNat b.toNat = true)
  have clear (x : Mask) (hx : g ≠ x) : Nat.beq g.toNat x.toNat = false :=
    beq_eq_false_iff_ne.mpr (fun e => hx (BitVec.eq_of_toNat_eq e))
  have none : ((L.map marked).any (fun w => Nat.beq w.1 g.toNat)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [List.any_eq_true, List.mem_map] at h
    obtain ⟨x,⟨v,vm,rfl⟩,hit⟩ := h
    have n : v.toNat = g.toNat := Nat.eq_of_beq_eq_true hit
    have e : v = g := BitVec.eq_of_toNat_eq n
    apply fresh
    change g ∈ L
    simpa only [e] using vm
  have oneGate : fastAct k T (L.map marked) (marked a) (marked b)
      (stripAB a.toNat b.toNat (L.map marked)) o = true := by
    unfold fastAct
    simp only [fuse_mark, ← show g = act o a b from rfl, markedNat]
    have z : Nat.beq g.toNat 0 = false := clear 0 nz
    have n : Nat.beq g.toNat 33554431 = false := clear allBits nt
    simp only [z, n, none, Bool.false_or, Bool.rec]
    cases hka : ka <;> cases hkb : kb
    all_goals
      rw [hka,hkb] at child
      simp only [Bool.or_eq_true]
      first
      | exact Or.inl (Or.inl (Or.inl child))
      | exact Or.inl (Or.inl (Or.inr child))
      | exact Or.inl (Or.inr child)
      | exact Or.inr child
  unfold fastPair
  simp only [markedNat, cmp, Bool.rec]
  cases o
  · rw [Bool.or_eq_true]
    exact Or.inl oneGate
  · rw [Bool.or_eq_true]
    exact Or.inr oneGate

theorem verifyWires (k : ℕ) (T : List Wire → Bool) (ih : SoundK k T) : SoundK (k+1) (checkWires k T) := by
  intro W nd j le reach
  by_contra hne
  have passed : checkWires k T (W.map marked) = true := by
    cases h : checkWires k T (W.map marked)
    · exact absurd h hne
    · rfl
  let t0 := (W.map marked).any (fun w => Nat.beq w.1 8127577)
  let t1 := (W.map marked).any (fun a => (W.map marked).any (fastPair k T (W.map marked) a))
  have record : W.Nodup ∧ (t0 || t1) = false := by
    change (!(t0 || t1)) = true at passed
    exact ⟨nd, by simpa only [Bool.not_eq_true'] using passed⟩
  have noTarget : target ∉ W := fun h => by
    have ht : t0 = true := (targetMarked W).mpr h
    have impossible := record.2
    rw [ht, Bool.true_or] at impossible
    exact Bool.noConfusion impossible
  generalize e : W.toFinset = S at reach
  cases reach with
  | done =>
    exact noTarget (List.mem_toFinset.mp (e.symm ▸ Finset.mem_singleton_self _))
  | @advance _ R a b o t am bm fresh nz nt sub bound prior =>
    have aW : a ∈ W := List.mem_toFinset.mp (e.symm ▸ am)
    have bW : b ∈ W := List.mem_toFinset.mp (e.symm ▸ bm)
    have ab : a ≠ b := by
      rintro rfl
      rw [act_self] at fresh
      exact fresh am
    have ordered (a' b' : Mask) (ap : a' ∈ W) (bp : b' ∈ W)
        (ord : a'.toNat < b'.toNat) (value : act o a' b' = act o a b)
        (bound' : S ⊆ insert a' (insert b' R)) : False := by
      have m : act o a' b' ∉ W := fun x => fresh (by rwa [← value, ← e, List.mem_toFinset])
      have yes := fastPair_true ih W R record.1 a' b' ap bp ord o m
        (value ▸ nz) (value ▸ nt) (e.symm ▸ sub) (e.symm ▸ bound') t (by omega)
        (value ▸ prior)
      have full : t1 = true := List.any_eq_true.mpr ⟨marked a',List.mem_map_of_mem ap,
        List.any_eq_true.mpr ⟨marked b',List.mem_map_of_mem bp,yes⟩⟩
      rw [full, Bool.or_true] at record
      exact Bool.noConfusion record.2
    rcases lt_or_gt_of_ne (fun z : a.toNat = b.toNat =>
      ab (BitVec.eq_of_toNat_eq z)) with lt | gt
    · exact ordered a b aW bW lt rfl bound
    · exact ordered b a bW aW gt (act_comm _ _ _) (by simpa [Finset.insert_comm] using bound)

noncomputable def dfs (b : ℕ) (T : List Wire → Bool) (n : ℕ) : List Wire → Bool :=
  Nat.rec T (fun i prev => checkWires (b+i) prev) n

theorem dfsSound (b : ℕ) (T : List Wire → Bool) (h : SoundK b T) : ∀ n, SoundK (b+n) (dfs b T n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact verifyWires (b+n) (dfs b T n) ih

theorem noneSound : SoundK 0 (fun _ => false) := fun _ _ _ _ _ => rfl

noncomputable def tableKill (U : Keys) (V : List Wire) : Bool :=
  (List.finRange 2).any (fun s =>
    let sorted := sortW (V.map (fun w => remapFast s (BitVec.ofNat 25 w.1)))
    let q := key sorted
    U.find q && (decodeKey q == sorted))

theorem tableSound (k : ℕ) (U : Keys) (pr : Rejects k U) : SoundK k (tableKill U) := by
  intro L nd j le reach
  by_contra hne
  have hit : tableKill U (L.map marked) = true := by
    cases h : tableKill U (L.map marked)
    · exact absurd h hne
    · rfl
  obtain ⟨s, _, hs⟩ := List.any_eq_true.mp hit
  have e0 : (L.map marked).map (fun w => remapFast s (BitVec.ofNat 25 w.1)) = L.map (remap s) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, naturalMask, remapFast_eq]
  simp only [e0, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨found, eq⟩ := hs
  have h := mappedReach s reach
  apply pr _ found j le
  rw [eq, sortFinset]
  have eqSet : (L.map (remap s)).toFinset = L.toFinset.image (remap s) := by
    ext a
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  exact eqSet.symm ▸ h

noncomputable def checkQ (k : ℕ) (T : List Wire → Bool) (q : ℕ) : Bool :=
  decide (decodeKey q).Nodup && checkWires k T ((decodeKey q).map (fun w => mark w.toNat))

theorem verifyTable (k : ℕ) (T : List Wire → Bool) (U : Keys) (ih : SoundK k T)
    (ok : U.all (checkQ k T) = true) : Rejects (k+1) U := by
  intro q hit j le reach
  have passed := searched ok hit
  simp only [checkQ, Bool.and_eq_true, decide_eq_true_eq] at passed
  have h := verifyWires k T ih (decodeKey q) passed.1 j le reach
  have p2 : checkWires k T ((decodeKey q).map marked) = true := passed.2
  rw [h] at p2
  exact Bool.noConfusion p2

theorem allBranch (b : ℕ) (l r : Keys) (f : ℕ → Bool) :
    (Keys.branch b l r).all f = (l.all f && r.all f) := rfl


def r6p0 : Keys := .leaf [
0x7e000018c631827c842084217c210fc2007c00,0x7e000018c631827c842085f108210fc200001f,0x7e000018c63f8213e42084217c2108420f8000,0x7e000018c63f8213e420be210821084200001f,0x7e000018c7f182109f208421083f084200001f,0x7f8c63042109f17c421042108400f8000003e0,0x7f8c6304f908410842f842108400f8000003e0,0xfc00000842108210842084210830006000f83e0003e0,0xfc000008421082108420843f0830006000f80000001f,0xfc0000084210821085f084210830006000f8000003e0,0xfc00000842108217c4208421083000600007c000001f,0xfc0000084213e210842084210830006000f8000003e0,0xfc000008427c8210842084210830006000f80000001f,0xfc0000084f90821084208421083000600007c000001f,0xfc0000210842084210820000f885f108210fc20f8000,0xfc00002108420842108203e00084217c210fc20f8000]

def r6p1 : Keys := .leaf [
0xfc00002108420842108210842084317c210fc20f8000,0xfc00002108420842108210842085f17c210fc20f801f,0xfc000021084208421082108420be217c42f8be1087e1,0xfc0000210842084210821084f885f1082108c20f8000,0xfc0000210842084210821084f885f108210fc20f801f,0xfc0000210842084210821084f885f1083f08421087e1,0xfc0000210842084210821084f885f17c210fc20f8000,0xfc000021084208421082109f208421083f084200041f,0xfc00002108420842108210a4f8be21082108420003e0,0xfc00002108420842108213e42084217c2108c20f8000,0xfc00002108420842108213e42084217c3f08421087e1,0xfc00002108420842108213e4f8be217c2108420003e0,0xfc0000210842084210827c000084217c210fc2007c00,0xfc0000210842084210827c000085f108210fc200001f,0xfc0000210842084210827c8420842108210fc200041f,0xfc0000210842084210827c842084217c2108c2007c00]

def r6p2 : Keys := .leaf [
0xfc0000210842084210827c842084217c210fc2000400,0xfc0000210842084210827c842084217c210fc2007c1f,0xfc0000210842084210827c8420843108210fc200001f,0xfc0000210842084210827c842084317c2108420003e0,0xfc0000210842084210827c842085f1082108c200001f,0xfc0000210842084210827c842085f1084210be1087e1,0xfc0000210842084210827c842085f17c210fc200001f,0xfc0000210842084210827c842085f17c4210be1087e1,0xfc0000210842084210827c84f8842108210fc2007c1f,0xfc0000210842084210827c84f884217c210fc2007c00,0xfc0000210842084210827c84f885f108210fc200001f,0xfc0000210842084210827c84f885f17c2108420003e0,0xfc000021084208421082843f0884217c1f0000007c00,0xfc000021084208421082843f0885f1081f000000001f,0xfc000021084208421082fca52884217c210fc2007c00,0xfc000021084208421082fca52885f108210fc200001f]

def r6p3 : Keys := .leaf [
0xfc0000210842084210830842f8421f841f0000007c00,0xfc0000210842084210830be210421f841f000000001f,0xfc00002108420842108318c6f84211841f0000007c00,0xfc00002108420842108318c6f885f17c210fc20f8000,0xfc00002108420842108318c6f8be217c210fc2007c00,0xfc0000210842084210831be6304211841f000000001f,0xfc0000210842084210831be6f8be217c2108420003e0,0xfc0000210842084210837cc63084217c210fc2007c00,0xfc0000210842084210837cc63085f108210fc200001f,0xfc0000210842084210837cc6f884217c210fc2007c00,0xfc0000210842084210837cc6f885f17c2108420003e0,0xfc000021084a084210821084f8be2108210842007c00,0xfc000021084a0842108213e42084217c2108420f8000,0xfc000021084a0842108213e420be210821084200001f,0xfc000021084a084210827c842084217c210842007c00,0xfc000021084a0842108318c6307e108400f80000001f]

def r6p4 : Keys := .leaf [
0xfc000021084a0842108318c6f84210841f0000007c00,0xfc000021084a084210837cc63042108400f80000001f,0xfc000021087e084210820000f8be2108210842007c00,0xfc000021087e0842108203e00084217c2108420f8000,0xfc000021087e0842108203e000be210821084200001f,0xfc000021087e0842108210842084317c2108420f8000,0xfc000021087e08421082108420be210821084200041f,0xfc000021087e08421082108420be217c210842007c1f,0xfc000021087e08421082108420be217c42f8be108421,0xfc000021087e084210821084f8be2108210842007c1f,0xfc000021087e084210821084f8be217c210842007c00,0xfc000021087e0842108210a42084217c2108420f8000,0xfc000021087e0842108210a420be210821084200001f,0xfc000021087e0842108213e42084217c2108420f801f,0xfc000021087e0842108213e420be21084210be108421,0xfc000021087e0842108213e420be217c21084200001f]

def r6p5 : Keys := .leaf [
0xfc000021087e0842108213e420be217c4210be108421,0xfc000021087e0842108213e4f88421082108420f801f,0xfc000021087e0842108213e4f884217c2108420f8000,0xfc000021087e0842108213e4f8be210821084200001f,0xfc000021087e084210827c000084217c210842007c00,0xfc000021087e0842108284210884217c1f0000007c00,0xfc000021087e08421082842108be210800f80000001f,0xfc000021087e084210830842f84210841f0000007c00,0xfc000021087e0842108318c6f885f17c2108420f8000,0xfc000021087e0842108318c6f8be217c210842007c00,0xfc000021087e084210831be63084217c2108420f8000,0xfc000021087e084210831be630be210821084200001f,0xfc000021087e084210831be6f884217c2108420f8000,0xfc000021087e084210837c421042108400f80000001f,0xfc000021087e08423e8213e42084217c2108420f8000,0xfc000021087e08423e8213e420be210821084200001f]

def r6p6 : Keys := .leaf [
0xfc00002108c2084210821084f8be21082108420003e0,0xfc00002108c208421082109f208421083f084200001f,0xfc00002108c2084210827c842084217c2108420003e0,0xfc00002108c208423e8210842084217c2108420f8000,0xfc00002108c208423e82108420be210821084200001f,0xfc0000210fc2084210820000f88421083f08420003e0,0xfc0000210fc208421082001f008421083f084200001f,0xfc0000210fc2084210821084208001003f084200001f,0xfc0000210fc2084210821084f884217c3f08420003e0,0xfc0000210fc2084210821086208421083f084200001f,0xfc0000210fc20842108294bf288421083f084200001f,0xfc0000210fc208421082fc21088421080007c000001f,0xfc0000210fc2084210830842107e10840007c000001f,0xfc0000210fc20842108318c6304211841f000000001f,0xfc0000210fc20842108318c6307e108400008000001f,0xfc0000210fc2084214821084208421083f084200001f]

def r6p7 : Keys := .leaf [
0xfc0000210fc20842148318c6304210841f000000001f,0xfc0000210fc208423e820000f88421082108420f8000,0xfc0000210fc208423e8210842084217c2108420f801f,0xfc0000210fc208423e82108420be21083f084200001f,0xfc0000210fc208423e821084f88421082108420f801f,0xfc0000210fc208423e821084f884217c2108420f8000,0xfc0000210fc208423e827c000084210821084200001f,0xfc0000210fc208423e827c84208421083f084200001f,0xfc0000210fc208423e827c8420be210821084200001f,0xfc0000210fc208423e828421088421081f000000001f,0xfc0000210fc208423e830842104210841f000000001f,0xfc0000210fc20847d082109f208421083f084200001f,0xfc0000210fc210843f0421084108427c5f1084108421,0xfc0000210fc210843f042108413e42104210be108421,0xfc0000318c63040000010842f8421f841f0000007c00,0xfc0000318c63040000010be210421f841f000000001f]

def r6p8 : Keys := .leaf [
0xfc0000318c63040001f1084210421f841f0000007c00,0xfc0000318c63040001f10842107e108400f8000003e0,0xfc0000318c63040001f10be2104210841f00000003e0,0xfc0000318c63040001f17c421042108400f8000003e0,0xfc0000318c6304003e010842107e108400f80000001f,0xfc0000318c6304003e010842f84210841f0000007c00,0xfc0000318c6304003e010be2104210841f000000001f,0xfc0000318c6304003e017c421042108400f80000001f,0xfc0000318c630407c001084210421f841f000000001f,0xfc0000318c630407c0010842107e10840007c000001f,0xfc0000318c630407c0010842f84210841f00000003e0,0xfc0000318c630407c0017c42104210840007c000001f,0xfc0000318c63042108410002007e108400f80000001f,0xfc0000318c6304210841084210421f8418003e007c00,0xfc0000318c6304210841084210421f841f000000041f,0xfc0000318c6304210841084210421f841f003e007c1f]

def r6p9 : Keys := .leaf [
0xfc0000318c63042108410842107e108400083e0003e0,0xfc0000318c63042108410842f84211841f0000007c00,0xfc0000318c63042108410842f8421f84180000007c00,0xfc0000318c63042108410842f8421f841f0000000400,0xfc0000318c63042108410842f8421f841f0000007c1f,0xfc0000318c63042108410842f8421f841f003e007c00,0xfc0000318c63042108410842f872108400f8000003e0,0xfc0000318c63042108410842f87e108400f83e0003e0,0xfc0000318c63042108410842f87e1084210fc2007c00,0xfc0000318c6304210841086210421f841f000000001f,0xfc0000318c63042108410862f84210841f00000003e0,0xfc0000318c63042108410be21042108418003e0003e0,0xfc0000318c63042108410be2104211841f000000001f,0xfc0000318c63042108410be210421f8418000000001f,0xfc0000318c63042108410be210421f841f003e00001f,0xfc0000318c63042108410be2107210840007c000001f]

def r6p10 : Keys := .leaf [
0xfc0000318c63042108410be2107e1084210fc200001f,0xfc0000318c63042108410be21084217c210fc20f8000,0xfc0000318c63042108410be2f84210841f003e0003e0,0xfc0000318c63042108410be2f8421f841f000000001f,0xfc0000318c63042108410be2f884217c210fc20f8000,0xfc0000318c6304210841684210421f8400f80000001f,0xfc0000318c63042108416842f842108400f8000003e0,0xfc0000318c63042108417c421042108400083e0003e0,0xfc0000318c63042108417c421084217c210fc2007c00,0xfc0000318c63042108417c421085f108210fc200001f,0xfc0000318c63042108417c42f842108400f83e0003e0,0xfc0000318c63042108417c42f884217c210fc2007c00,0xfc0000318c63042108417c42f885f17c2108420003e0,0xfc0000318c63042109f10002004210841f0000007c00,0xfc0000318c63042109f10842104211841f0000007c00,0xfc0000318c63042109f1084210421f841f0000007c1f]

def r6p11 : Keys := .leaf [
0xfc0000318c63042109f1084210421f841f003e007c00,0xfc0000318c63042109f108421072108400f8000003e0,0xfc0000318c63042109f10842107e108400f83e0003e0,0xfc0000318c63042109f10842107e1084210fc2007c00,0xfc0000318c63042109f10842f8421f841f0000007c00,0xfc0000318c63042109f10842f87e108400f8000003e0,0xfc0000318c63042109f10862104210841f00000003e0,0xfc0000318c63042109f10be2104210841800000003e0,0xfc0000318c63042109f10be2104210841f0000000040,0xfc0000318c63042109f10be2104210841f003e0003e0,0xfc0000318c63042109f10be210421f841f000000001f,0xfc0000318c63042109f10be210421f842108420f8000,0xfc0000318c63042109f10be2107e10842108420003e0,0xfc0000318c63042109f10be2f84210841f00000003e0,0xfc0000318c63042109f168421042108400f8000003e0,0xfc0000318c63042109f17c42104210840008000003e0]

def r6p12 : Keys := .leaf [
0xfc0000318c63042109f17c421042108400f800000040,0xfc0000318c63042109f17c421042108400f83e0003e0,0xfc0000318c63042109f17c421085f1082108420003e0,0xfc0000318c63042109f17c42f842108400f8000003e0,0xfc0000318c6304210c410842107e108400f80000001f,0xfc0000318c6304213e4108421042108418003e007c00,0xfc0000318c6304213e410842104210841f000000041f,0xfc0000318c6304213e410842104210841f003e007c1f,0xfc0000318c6304213e4108421072108400f80000001f,0xfc0000318c6304213e410842107e108400080000001f,0xfc0000318c6304213e410842107e108400f83e00001f,0xfc0000318c6304213e410842f8421f841f0000007c00,0xfc0000318c6304213e410862104210841f000000001f,0xfc0000318c6304213e410be210421f841f000000001f,0xfc0000318c6304213e410be21084217c2108420f8000,0xfc0000318c6304213e4168421042108400f80000001f]

def r6p13 : Keys := .leaf [
0xfc0000318c6304213e417c4210421f8400f80000001f,0xfc0000318c6304213e417c421084217c210842007c00,0xfc0000318c6304213e417c421085f10821084200001f,0xfc0000318c63042148410842f84210841f00000003e0,0xfc0000318c63042148417c42104210840007c000001f,0xfc0000318c63042149f10842104210841f00000003e0,0xfc0000318c630427c8410002004210841f000000001f,0xfc0000318c630427c84108421042108418003e0003e0,0xfc0000318c630427c8410842104211841f000000001f,0xfc0000318c630427c8410842107210840007c000001f,0xfc0000318c630427c8410842107e1084210fc200001f,0xfc0000318c630427c8410842f84210841800000003e0,0xfc0000318c630427c8410842f84210841f0000000040,0xfc0000318c630427c8410842f84210841f003e0003e0,0xfc0000318c630427c8410842f8421f841f0000007c00,0xfc0000318c630427c8410842f8421f842108420f8000]

def r6p14 : Keys := .leaf [
0xfc0000318c630427c8410842f87e10842108420003e0,0xfc0000318c630427c8410be210421f841f000000001f,0xfc0000318c630427c8410be2107e10840007c000001f,0xfc0000318c630427c8416842104210840007c000001f,0xfc0000318c630427c8417c421042108400008000001f,0xfc0000318c630427c8417c421084217c2108420003e0,0xfc0000318c630427c8417c42f84210840007c000001f,0xfc0000318c630427c8417c42f884217c2108420003e0,0xfc0000318c630427c8421084f8be21082108420003e0,0xfc0000318c630427c9f10842104210841f003e0003e0,0xfc0000318c630427c9f10842f84210841f00000003e0,0xfc0000318c630427c9f17c42104210840007c000001f,0xfc0000318c630427c9f21084f8be21082108420003e0,0xfc0000318c6304e10841084210421f8400f80000001f,0xfc0000318c6304e108410842f842108400f8000003e0,0xfc0000318c6304e108410be2104210840007c000001f]

def r6p15 : Keys := .leaf [
0xfc0000318c6304e109f108421042108400f8000003e0,0xfc0000318c6304f80001084210421f8400f80000001f,0xfc0000318c6304f800010842f842108400f8000003e0,0xfc0000318c6304f800010be2104210840007c000001f,0xfc0000318c6304f9084100020042108400f80000001f,0xfc0000318c6304f9084108421042108400083e0003e0,0xfc0000318c6304f9084108421042118400f80000001f,0xfc0000318c6304f90841084210421f8400080000001f,0xfc0000318c6304f90841084210421f8400f83e00001f,0xfc0000318c6304f908410842f84210840008000003e0,0xfc0000318c6304f908410842f842108400f800000040,0xfc0000318c6304f908410842f842108400f83e0003e0,0xfc0000318c6304f908410842f8421f8400f80000001f,0xfc0000318c6304f908410842f8421f8400f8000003e0,0xfc0000318c6304f908410842f8421f841f0000007c00,0xfc0000318c6304f908410842f8421f84210842007c00]

def r6p16 : Keys := .leaf [
0xfc0000318c6304f908410842f8842108210fc2007c00,0xfc0000318c6304f908410862104210840007c000001f,0xfc0000318c6304f908410be21042108400008000001f,0xfc0000318c6304f908410be210421f840007c000001f,0xfc0000318c6304f908410be210421f8400f80000001f,0xfc0000318c6304f908410be210421f841f000000001f,0xfc0000318c6304f908410be210421f8421084200001f,0xfc0000318c6304f908410be210842108210fc200001f,0xfc0000318c6304f908410be21084217c2108420003e0,0xfc0000318c6304f908410be2f84210840007c000001f,0xfc0000318c6304f908410be2f884217c2108420003e0,0xfc0000318c6304f9084210842084217c210fc2007c00,0xfc0000318c6304f9084210842085f108210fc200001f,0xfc0000318c6304f908421084f885f1082108420003e0,0xfc0000318c6304f9084213e42084217c2108420003e0,0xfc0000318c6304f909f108421042108400f83e0003e0]

def r6p17 : Keys := .leaf [
0xfc0000318c6304f909f1084210421f8400f80000001f,0xfc0000318c6304f909f10842f842108400f8000003e0,0xfc0000318c6304f909f10be2104210840007c000001f,0xfc0000318c6304f909f21084f885f1082108420003e0,0xfc0000318c6304f909f213e4f88421082108420003e0,0xfc0000318c63050842110842f83e000000f8000003e0,0xfc0000318c63050842110be2103e00000007c000001f,0xfc0000318c63050842117c421001f0000007c000001f,0xfc0000318c6305087e110842103e000000f80000001f,0xfc0000318c6305294a510842f8421f841f0000007c00,0xfc0000318c6305294a510842f87e108400f8000003e0,0xfc0000318c6305294a510be210421f841f000000001f,0xfc0000318c6305294a510be2107e10840007c000001f,0xfc0000318c6305297e510842107e108400f80000001f,0xfc0000318c6305297e510842f8421f841f0000007c00,0xfc0000318c6305297e510be210421f841f000000001f]

def r6p18 : Keys := .leaf [
0xfc0000318c6305f8421108421001f0000007c000001f,0xfc0000318c6305f94a51084210421f8400f80000001f,0xfc0000318c6305f94a510842f842108400f8000003e0,0xfc0000318c6305f94a510be2104210840007c000001f,0xfc0000318c6306108420843f083e000000f80000001f,0xfc0000318c6306108420fc210801f0000007c000001f,0xfc0000318c63061085f08421083e000000f8000003e0,0xfc0000318c630617c4208421083e00000007c000001f,0xfc0000318c6306318c608423083e000000f80000001f,0xfc0000318c6306318c60fc210801f00000008000001f,0xfc0000318c6306318c610842f8421f841f0000007c00,0xfc0000318c6306318c610be210421f841f000000001f,0xfc0000318c6306318c617c4210421f8400f80000001f,0xfc0000318c6306318df08421083e000000f800000040,0xfc0000318c6306318df10842f8421f841f0000007c00,0xfc0000318c6306318df10be2104210841f00000003e0]

def r6p19 : Keys := .leaf [
0xfc0000318c6306318df10be2f84210841f00000003e0,0xfc0000318c6306318df17c421042108400f8000003e0,0xfc0000318c6306318df17c42f842108400f8000003e0,0xfc0000318c630637cc608421083e000000008000001f,0xfc0000318c630637cc610842f84210841f00000003e0,0xfc0000318c630637cc610be210421f841f000000001f,0xfc0000318c630637cc617c42104210840007c000001f,0xfc0000318c630637cdf10842f84210841f00000003e0,0xfc0000318c6306f8842084210801f0000007c000001f,0xfc0000318c6306f98c6084210801f00000008000001f,0xfc0000318c6306f98c61084210421f8400f80000001f,0xfc0000318c6306f98c610842f842108400f8000003e0,0xfc0000318c6306f98c610be2104210840007c000001f,0xfc0000318c6306f98df10842f842108400f8000003e0,0xfc0000318c63084210827c842084217c210fc2007c00,0xfc0000318c63084210827c842085f108210fc200001f]

def r6p20 : Keys := .leaf [
0xfc0000318c6308423e821084f8be2108210842007c00,0xfc0000318c6308423e8213e42084217c2108420f8000,0xfc0000318c6308423e8213e420be210821084200001f,0xfc0000318c6308423e827c842084217c210842007c00,0xfc0000318c630847d0821084f8be21082108420003e0,0xfc0000318c630847d082109f208421083f084200001f,0xfc0000318c630847d0827c842084217c2108420003e0,0xfc0000318c6b042108410842107e108400f80000001f,0xfc0000318c6b042108410842f84210841f0000007c00,0xfc0000318c6b042108417c421042108400f80000001f,0xfc0000318c6b042109f10842104210841f0000007c00,0xfc0000318c6b0427c8410842104210841f000000001f,0xfc0000318c6b04f9084108421042108400f80000001f,0xfc0000318c6b06318c608421083e000000f80000001f,0xfc0000318c7f040000010842f84210841f0000007c00,0xfc0000318c7f040000017c421042108400f80000001f]

def r6p21 : Keys := .leaf [
0xfc0000318c7f040001f10842104210841f0000007c00,0xfc0000318c7f0407c0010842104210841f000000001f,0xfc0000318c7f0421084108421042108418003e007c00,0xfc0000318c7f042108410842104210841f000000041f,0xfc0000318c7f042108410842104210841f003e007c1f,0xfc0000318c7f042108410842f8421084180000007c00,0xfc0000318c7f042108410842f84210841f0000000400,0xfc0000318c7f042108410842f84210841f0000007c00,0xfc0000318c7f042108410842f84210841f0000007c1f,0xfc0000318c7f042108410842f84210841f003e007c00,0xfc0000318c7f042108410842f8421f841f0000007c00,0xfc0000318c7f042108410862104210841f000000001f,0xfc0000318c7f042108410be210421f841f000000001f,0xfc0000318c7f042108410be21084217c2108420f8000,0xfc0000318c7f042108410be2f884217c2108420f8000,0xfc0000318c7f0421084168421042108400f80000001f]

def r6p22 : Keys := .leaf [
0xfc0000318c7f042108417c421042108400080000001f,0xfc0000318c7f042108417c421042108400f80000001f,0xfc0000318c7f042108417c421042108400f83e00001f,0xfc0000318c7f042108417c4210421f8400f80000001f,0xfc0000318c7f042108417c42107e108400f80000001f,0xfc0000318c7f042108417c421084217c210842007c00,0xfc0000318c7f042108417c421085f10821084200001f,0xfc0000318c7f042108417c42f842108400f80000001f,0xfc0000318c7f042108417c42f884217c210842007c00,0xfc0000318c7f042109f10842104210841f0000007c1f,0xfc0000318c7f042109f10842104210841f003e007c00,0xfc0000318c7f042109f10842f84210841f0000007c00,0xfc0000318c7f042109f17c421042108400f80000001f,0xfc0000318c7f04213e410842f84210841f0000007c00,0xfc0000318c7f04213e410be2104210841f000000001f,0xfc0000318c7f04213e417c421042108400f80000001f]

def r6p23 : Keys := .leaf [
0xfc0000318c7f042148410842104210841f000000001f,0xfc0000318c7f0427c84108421042108418000000001f,0xfc0000318c7f0427c8410842104210841f000000001f,0xfc0000318c7f0427c8410842104210841f003e00001f,0xfc0000318c7f0427c8410842f84210841f000000001f,0xfc0000318c7f0427c8410842f84210841f00000003e0,0xfc0000318c7f0427c8410842f84210841f0000007c00,0xfc0000318c7f0427c8410842f88421082108420f8000,0xfc0000318c7f0427c8417c42104210840007c000001f,0xfc0000318c7f0427c8417c421042108400f80000001f,0xfc0000318c7f0427c8417c42104210841f000000001f,0xfc0000318c7f0427c8417c421084210821084200001f,0xfc0000318c7f0427c84210842084217c2108420f8000,0xfc0000318c7f0427c842108420be210821084200001f,0xfc0000318c7f0427c9f10842104210841f000000001f,0xfc0000318c7f04f8000108421042108400f80000001f]

def r6p24 : Keys := .leaf [
0xfc0000318c7f04f908410842107e108400f80000001f,0xfc0000318c7f04f908410842f84210841f0000007c00,0xfc0000318c7f04f908417c421042108400f80000001f,0xfc0000318c7f050842110842103e000000f80000001f,0xfc0000318c7f05294a510842f84210841f0000007c00,0xfc0000318c7f05294a517c421042108400f80000001f,0xfc0000318c7f061084208421083e000000f80000001f,0xfc0000318c7f06318c610842f84210841f0000007c00,0xfc0000318c7f06318c610be2104210841f000000001f,0xfc0000318c7f06318c617c421042108400f80000001f,0xfc0000318c7f06318df10842f84210841f0000007c00,0xfc0000318c7f0637cc610842104210841f000000001f,0xfc0000318c7f06f98c617c421042108400f80000001f,0xfc0000318c7f0842108213e42084217c2108420f8000,0xfc0000318c7f0842108213e420be210821084200001f,0xfc0000318c7f08423e8213e42084217c2108420f8000]

def r6p25 : Keys := .leaf [
0xfc0000318c7f08423e8213e420be210821084200001f,0xfc0000318c7f0847d08210842084217c2108420f8000,0xfc0000318c7f0847d082108420be210821084200001f,0xfc0000318c7f18c631821084f8be2108210842007c00,0xfc0000318c7f18c6318213e42084217c2108420f8000,0xfc0000318c7f18c6318213e420be210821084200001f,0xfc0000318c7f18c631827c842084217c210842007c00,0xfc0000318ce3042108410842107e10840007c000001f,0xfc0000318ce3042108410842f84210841f00000003e0,0xfc0000318ce3042108417c42104210840007c000001f,0xfc0000318ce3042109f10842104210841f00000003e0,0xfc0000318ce304213e410842104210841f000000001f,0xfc0000318ce304f908410842104210840007c000001f,0xfc0000318fe3040000010842107e10840007c000001f,0xfc0000318fe3040001f10842104210841f00000003e0,0xfc0000318fe304003e010842104210841f000000001f]

def r6p26 : Keys := .leaf [
0xfc0000318fe3042108410002004210841f000000001f,0xfc0000318fe30421084108421042108418003e0003e0,0xfc0000318fe3042108410842104211841f000000001f,0xfc0000318fe3042108410842107210840007c000001f,0xfc0000318fe3042108410842107e108400008000001f,0xfc0000318fe3042108410842107e10840007c000001f,0xfc0000318fe3042108410842107e1084210fc200001f,0xfc0000318fe3042108410842f84210841f003e0003e0,0xfc0000318fe3042108410842f87e10840007c000001f,0xfc0000318fe3042108410be210421f841f000000001f,0xfc0000318fe3042108410be2107e10840007c000001f,0xfc0000318fe3042108417c42107e10840007c000001f,0xfc0000318fe3042109f10842104210841f003e0003e0,0xfc0000318fe3042109f10842107e10840007c000001f,0xfc0000318fe3042109f10842f84210841f00000003e0,0xfc0000318fe304210c410842104210841f000000001f]

def r6p27 : Keys := .leaf [
0xfc0000318fe304213e4108421042108418000000001f,0xfc0000318fe304213e410842104210841f000000001f,0xfc0000318fe304213e410842104210841f003e00001f,0xfc0000318fe304213e410842107e10840007c000001f,0xfc0000318fe304213e410842107e108400f80000001f,0xfc0000318fe304213e410842107e10841f000000001f,0xfc0000318fe304213e410842107e108421084200001f,0xfc0000318fe304213e421084208421083f084200001f,0xfc0000318fe30427c841084210421f841f000000001f,0xfc0000318fe30427c8410842107e10840007c000001f,0xfc0000318fe304f800010842104210840007c000001f,0xfc0000318fe304f908410842107e10840007c000001f,0xfc0000318fe304f908417c42104210840007c000001f,0xfc0000318fe3050842110842103e00000007c000001f,0xfc0000318fe305294a51084210421f841f000000001f,0xfc0000318fe305294a510842107e10840007c000001f]

def r6p28 : Keys := .leaf [
0xfc0000318fe305297e510842104210841f000000001f,0xfc0000318fe305f94a510842107e10840007c000001f,0xfc0000318fe3061084208421083e00000007c000001f,0xfc0000318fe306318c608421083e000000008000001f,0xfc0000318fe306318c610842107e10840007c000001f,0xfc0000318fe308421082109f208421083f084200001f,0xfc0000318fe308423e821084208421083f084200001f,0xfc0000318fe30847d082109f208421083f084200001f,0xfc0000318fe318c631821084f8be21082108420003e0,0xfc0000318fe318c63182109f208421083f084200001f,0xfc0000318fe318c631827c842084217c2108420003e0,0xfc0000318fe318c63f821084208421083f084200001f,0xfc0000318fe318c63f8210842084217c2108420f8000,0xfc0000318fe318c63f82108420be210821084200001f,0xfc0000318fe318c63f821084f88421082108420f8000,0xfc0000318fe318c63f827c842084210821084200001f]

def r6p29 : Keys := .leaf [
0xfc0010210842084210821084f885f1082108420f8000,0xfc0010210842084210821084f8be2108210842007c00,0xfc00102108420842108213e42084217c2108420f8000,0xfc00102108420842108213e420be210821084200001f,0xfc0010210842084210827c842084217c210842007c00,0xfc0010210842084210827c842085f10821084200001f,0xfc00102108420842108318c6307e108400f80000001f,0xfc00102108420842108318c6f84210841f0000007c00,0xfc0010210842084210831be6304210841f000000001f,0xfc0010210842084210837cc63042108400f80000001f,0xfc0010210fc2084210821084208421083f084200001f,0xfc0010210fc20842108318c6304210841f000000001f,0xfc0010318c63042108410842107e108400f80000001f,0xfc0010318c63042108410842f84210841f0000007c00,0xfc0010318c63042108410be2104210841f000000001f,0xfc0010318c63042108417c421042108400f80000001f]

def r6p30 : Keys := .leaf [
0xfc0010318c63042109f10842104210841f0000007c00,0xfc0010318c630427c8410842104210841f000000001f,0xfc0010318c6304f9084108421042108400f80000001f,0xfc0010318c6306318c608421083e000000f80000001f,0xfc0010318fe3042108410842104210841f000000001f,0xfc00f83e000018c631821084f885f1082108420f8000,0xfc00f83e000018c631821084f8be2108210842007c00,0xfc00f83e000018c6318213e42084217c2108420f8000,0xfc00f83e000018c6318213e420be210821084200001f,0xfc00f83e000018c631827c842084217c210842007c00,0xfc00f83e000018c631827c842085f10821084200001f,0xfc00f83e000018c7f1821084208421083f084200001f,0xfc01002108420842108210842084217c210fc20f8000,0xfc0100210842084210821084f8be21082108420003e0,0xfc010021084208421082109f208421083f084200001f,0xfc0100210842084210827c8420842108210fc200001f]

def r6p31 : Keys := .leaf [
0xfc0100210842084210827c842084217c2108420003e0,0xfc010021087e0842108210842084217c2108420f8000,0xfc010021087e08421082108420be210821084200001f,0xfc0100318c6304210841084210421f841f000000001f,0xfc0100318c63042108410842107e10840007c000001f,0xfc0100318c63042108410842f84210841f00000003e0,0xfc0100318c63042108417c42104210840007c000001f,0xfc0100318c63042109f10842104210841f00000003e0,0xfc0100318c6304213e410842104210841f000000001f,0xfc0100318c6304f908410842104210840007c000001f,0xfc0100318c7f042108410842104210841f000000001f,0xfc1f003e0000108421042108413e42104210be1087e1,0xfc1f003e000018c6318210842084217c210fc20f8000,0xfc1f003e000018c631821084f8be21082108420003e0,0xfc1f003e000018c63182109f208421083f084200001f,0xfc1f003e000018c631827c8420842108210fc200001f]

def r6p32 : Keys := .leaf [
0xfc1f003e000018c631827c842084217c2108420003e0,0xfc1f003e000018c63f8210842084217c2108420f8000,0xfc1f003e000018c63f82108420be210821084200001f,0xfc1f003e007c1084210421084108427c5f1084108421,0xfc1f003e007c108421042108413e42104210be108421,0xfc1f003e007c18c631821084208421083f084200001f,0xfc1f003e007c18c6318210842084217c2108420f8000,0xfc1f003e007c18c63182108420be210821084200001f,0xfc1f003e007c18c631821084f88421082108420f8000,0xfc1f003e007c18c631827c842084210821084200001f,0xfd0842210fc208423e821084208421083f084200001f,0xfd0842318c63042109f17c421042108400f8000003e0,0xfd0842318c6304f908410842f842108400f8000003e0,0xfd0842318c7f042108410842f84210841f0000007c00,0xfd0842318c7f042108417c421042108400f80000001f,0xfd0842318fe3042108410842107e10840007c000001f]

def r6p33 : Keys := .leaf [
0xfe1084108421040001f10842107e108400f8000003e0,0xfe1084108421040001f17c421042108400f8000003e0,0xfe1084108421042108410002007e108400f80000001f,0xfe1084108421042108410842107e108400083e0003e0,0xfe1084108421042108410842f84211841f0000007c00,0xfe1084108421042108410842f87e108400f83e0003e0,0xfe1084108421042108410842f87e1084210fc2007c00,0xfe1084108421042108410862f84210841f00000003e0,0xfe1084108421042108417c421042108400083e0003e0,0xfe1084108421042108417c42f842108400f83e0003e0,0xfe1084108421042108417c42f885f17c2108420003e0,0xfe1084108421042109f10002004210841f0000007c00,0xfe1084108421042109f10842104211841f0000007c00,0xfe1084108421042109f10842107e108400f83e0003e0,0xfe1084108421042109f10842107e1084210fc2007c00,0xfe1084108421042109f10842f87e108400f8000003e0]

def r6p34 : Keys := .leaf [
0xfe1084108421042109f10862104210841f00000003e0,0xfe1084108421042109f17c42104210840008000003e0,0xfe1084108421042109f17c421042108400f800000040,0xfe1084108421042109f17c421042108400f83e0003e0,0xfe1084108421042109f17c421085f1082108420003e0,0xfe1084108421042109f17c42f842108400f8000003e0,0xfe108410842104210c410842107e108400f80000001f,0xfe1084108421042148410842f84210841f00000003e0,0xfe1084108421042148417c42104210840007c000001f,0xfe1084108421042149f10842104210841f00000003e0,0xfe10841084210427c8421084f8be21082108420003e0,0xfe10841084210427c9f21084f8be21082108420003e0,0xfe108410842104f800010842f842108400f8000003e0,0xfe108410842104f9084100020042108400f80000001f,0xfe108410842104f9084108421042108400083e0003e0,0xfe108410842104f9084108421042118400f80000001f]

def r6p35 : Keys := .leaf [
0xfe108410842104f908410842f84210840008000003e0,0xfe108410842104f908410842f842108400f800000040,0xfe108410842104f908410842f842108400f83e0003e0,0xfe108410842104f908410842f8421f84210842007c00,0xfe108410842104f908410862104210840007c000001f,0xfe108410842104f908410be21084217c2108420003e0,0xfe108410842104f908410be2f884217c2108420003e0,0xfe108410842104f9084213e42084217c2108420003e0,0xfe108410842104f909f108421042108400f83e0003e0,0xfe108410842104f909f10842f842108400f8000003e0,0xfe108410842104f909f213e4f88421082108420003e0,0xfe1084108421050842110842f83e000000f8000003e0,0xfe1084108421050842117c421001f0000007c000001f,0xfe108410842105294a510842f8421f841f0000007c00,0xfe108410842105294a510842f87e108400f8000003e0,0xfe108410842105f8421108421001f0000007c000001f]

def r6p36 : Keys := .leaf [
0xfe108410842105f94a51084210421f8400f80000001f,0xfe108410842105f94a510842f842108400f8000003e0,0xfe108410842106108420fc210801f0000007c000001f,0xfe1084108421061085f08421083e000000f8000003e0,0xfe108410842106318c608423083e000000f80000001f,0xfe108410842106318c60fc210801f00000008000001f,0xfe108410842106318df08421083e000000f800000040,0xfe108410842106318df10be2104210841f00000003e0,0xfe108410842106318df10be2f84210841f00000003e0,0xfe108410842106318df17c421042108400f8000003e0,0xfe108410842106318df17c42f842108400f8000003e0,0xfe108410842106f8842084210801f0000007c000001f,0xfe108410842106f98c6084210801f00000008000001f,0xfe108410842106f98c610842f842108400f8000003e0,0xfe108410842106f98c610be2104210840007c000001f,0xfe108410842106f98df10842f842108400f8000003e0]

def r6p37 : Keys := .leaf [
0xfe1084108429042108410842107e108400f80000001f,0xfe1084108429042108410842f84210841f0000007c00,0xfe1084108429042108417c421042108400f80000001f,0xfe1084108429042109f10842104210841f0000007c00,0xfe108410842904f9084108421042108400f80000001f,0xfe108410842906318c608421083e000000f80000001f,0xfe108410847d040000010842f84210841f0000007c00,0xfe108410847d040000017c421042108400f80000001f,0xfe108410847d040001f10842104210841f0000007c00,0xfe108410847d042108410842104210841f000000041f,0xfe108410847d042108410842104210841f003e007c1f,0xfe108410847d042108410842f84210841f0000000400,0xfe108410847d042108410842f84210841f0000007c1f,0xfe108410847d042108410842f84210841f003e007c00,0xfe108410847d042108410862104210841f000000001f,0xfe108410847d042108410be21084217c2108420f8000]

def r6p38 : Keys := .leaf [
0xfe108410847d042108410be2f884217c2108420f8000,0xfe108410847d042108417c421042108400080000001f,0xfe108410847d042108417c421042108400f83e00001f,0xfe108410847d042108417c42107e108400f80000001f,0xfe108410847d042108417c421084217c210842007c00,0xfe108410847d042108417c421085f10821084200001f,0xfe108410847d042108417c42f842108400f80000001f,0xfe108410847d042108417c42f884217c210842007c00,0xfe108410847d042109f10842104210841f0000007c1f,0xfe108410847d042109f10842104210841f003e007c00,0xfe108410847d042109f10842f84210841f0000007c00,0xfe108410847d042109f17c421042108400f80000001f,0xfe108410847d042148410842104210841f000000001f,0xfe108410847d0427c84210842084217c2108420f8000,0xfe108410847d0427c842108420be210821084200001f,0xfe108410847d04f8000108421042108400f80000001f]

def r6p39 : Keys := .leaf [
0xfe108410847d04f908410842107e108400f80000001f,0xfe108410847d04f908410842f84210841f0000007c00,0xfe108410847d04f908417c421042108400f80000001f,0xfe108410847d050842110842103e000000f80000001f,0xfe108410847d05294a510842f84210841f0000007c00,0xfe108410847d05294a517c421042108400f80000001f,0xfe108410847d061084208421083e000000f80000001f,0xfe108410847d06318c610842f84210841f0000007c00,0xfe108410847d06318c610be2104210841f000000001f,0xfe108410847d06318c617c421042108400f80000001f,0xfe108410847d06318df10842f84210841f0000007c00,0xfe108410847d06f98c617c421042108400f80000001f,0xfe108410847d084210821084f8be2108210842007c00,0xfe108410847d084210827c842084217c210842007c00,0xfe10841084a1042108410842107e10840007c000001f,0xfe10841084a1042108410842f84210841f00000003e0]

def r6p40 : Keys := .leaf [
0xfe10841084a1042108417c42104210840007c000001f,0xfe10841084a1042109f10842104210841f00000003e0,0xfe10841084a104f908410842104210840007c000001f,0xfe1084108fa1040000010842107e10840007c000001f,0xfe1084108fa1040001f10842104210841f00000003e0,0xfe1084108fa1042108410002004210841f000000001f,0xfe1084108fa1042108410842104211841f000000001f,0xfe1084108fa1042108410842107e108400008000001f,0xfe1084108fa1042108410842107e1084210fc200001f,0xfe1084108fa1042108410842f84210841f003e0003e0,0xfe1084108fa1042108410842f87e10840007c000001f,0xfe1084108fa1042108417c42107e10840007c000001f,0xfe1084108fa1042109f10842104210841f003e0003e0,0xfe1084108fa1042109f10842107e10840007c000001f,0xfe1084108fa1042109f10842f84210841f00000003e0,0xfe1084108fa104210c410842104210841f000000001f]

def r6p41 : Keys := .leaf [
0xfe1084108fa104213e421084208421083f084200001f,0xfe1084108fa104f800010842104210840007c000001f,0xfe1084108fa104f908410842107e10840007c000001f,0xfe1084108fa104f908417c42104210840007c000001f,0xfe1084108fa1050842110842103e00000007c000001f,0xfe1084108fa105294a51084210421f841f000000001f,0xfe1084108fa105294a510842107e10840007c000001f,0xfe1084108fa105f94a510842107e10840007c000001f,0xfe1084108fa1061084208421083e00000007c000001f,0xfe1084108fa106318c608421083e000000008000001f,0xfe1084108fa106318c610842107e10840007c000001f,0xfe1084108fa1084210821084f8be21082108420003e0,0xfe1084108fa1084210827c842084217c2108420003e0,0xfe1084108fa108423e821084208421083f084200001f,0xfe1084108fa108423e8210842084217c2108420f8000,0xfe1084108fa108423e82108420be210821084200001f]

def r6p42 : Keys := .leaf [
0xfe1084108fa108423e821084f88421082108420f8000,0xfe1084108fa108423e827c842084210821084200001f,0xfe108421087e084210821084f8be2108210842007c00,0xfe108421087e084210827c842084217c210842007c00,0xfe1084210fc2084210821084f8be21082108420003e0,0xfe1084210fc2084210827c842084217c2108420003e0,0xfe1084210fc208423e8210842084217c2108420f8000,0xfe1084210fc208423e82108420be210821084200001f,0xfe10843e0000084210827c842084217c210fc2007c00,0xfe10843e0000084210827c842085f108210fc200001f,0xfe10843e000008423e8213e42084217c2108420f8000,0xfe10843e000008423e8213e420be210821084200001f,0xfe10843e00000847d082109f208421083f084200001f,0xfe10843e007c084210821084f885f1082108420f8000,0xfe10843e007c084210821084f8be2108210842007c00,0xfe10843e007c0842108213e42084217c2108420f8000]

def r6p43 : Keys := .leaf [
0xfe10843e007c0842108213e420be210821084200001f,0xfe10843e007c084210827c842084217c210842007c00,0xfe10843e007c084210827c842085f10821084200001f,0xfe10843e007c0847d0821084208421083f084200001f,0xfe10843e0f800842108210842084217c210fc20f8000,0xfe10843e0f80084210821084f8be21082108420003e0,0xfe10843e0f8008421082109f208421083f084200001f,0xfe10843e0f80084210827c8420842108210fc200001f,0xfe10843e0f80084210827c842084217c2108420003e0,0xfe10843e0f8008423e8210842084217c2108420f8000,0xfe10843e0f8008423e82108420be210821084200001f,0xfe10843e8421042108410842f8421f841f0000007c00,0xfe10843e8421042108410be210421f841f000000001f,0xfe10843e8421042109f10be2104210841f00000003e0,0xfe10843e8421042109f17c421042108400f8000003e0,0xfe10843e842104213e410842107e108400f80000001f]

def r6p44 : Keys := .leaf [
0xfe10843e84210427c8410842f84210841f00000003e0,0xfe10843e84210427c8417c42104210840007c000001f,0xfe10843e842104f90841084210421f8400f80000001f,0xfe10843e842104f908410842f842108400f8000003e0,0xfe10843e842104f908410be2104210840007c000001f,0xfe1094108421042108410842107e108400f80000001f,0xfe1094108421042108410842f84210841f0000007c00,0xfe1094108421042108417c421042108400f80000001f,0xfe1094108421042109f10842104210841f0000007c00,0xfe109410842104f9084108421042108400f80000001f,0xfe109410842106318c608421083e000000f80000001f,0xfe1094108fa1042108410842104210841f000000001f,0xfe10fc3e00000842108213e42084217c2108420f8000,0xfe10fc3e00000842108213e420be210821084200001f,0xfe10fc3e0f800842108210842084217c2108420f8000,0xfe10fc3e0f8008421082108420be210821084200001f]

def r6p45 : Keys := .leaf [
0xfe10fc3e8421042108410842f84210841f0000007c00,0xfe10fc3e8421042108417c421042108400f80000001f,0xfe10fc3e84210427c8410842104210841f000000001f,0xfe10fc3f0842084210821084f8be2108210842007c00,0xfe10fc3f0842084210827c842084217c210842007c00,0xfe10fc3f08420847d0821084208421083f084200001f,0xfe1184108421042108410842107e10840007c000001f,0xfe1184108421042108410842f84210841f00000003e0,0xfe1184108421042108417c42104210840007c000001f,0xfe1184108421042109f10842104210841f00000003e0,0xfe118410842104f908410842104210840007c000001f,0xfe118410847d042108410842104210841f000000001f,0xfe1f843e000008421082109f208421083f084200001f,0xfe1f843e007c084210821084208421083f084200001f,0xfe1f843e8421042108410842107e10840007c000001f,0xfe1f843e842104213e410842104210841f000000001f]

def r6p46 : Keys := .leaf [
0xfe1f843e847d042108410842104210841f000000001f,0xfe1f843f0842084210821084f8be21082108420003e0,0xfe1f843f0842084210827c842084217c2108420003e0,0xfe1f843f084208423e8210842084217c2108420f8000,0xfe1f843f084208423e82108420be210821084200001f,0xfe1f843f087e084210821084208421083f084200001f,0xfe1f843f087e0842108210842084217c2108420f8000,0xfe1f843f087e08421082108420be210821084200001f,0xfe1f843f087e084210821084f88421082108420f8000,0xfe1f843f087e084210827c842084210821084200001f,0xff18c608000002108420fc210801f0000007c000001f,0xff18c6080000021085f08421083e000000f8000003e0,0xff18c608000002f8842084210801f0000007c000001f,0xff18c6080003e21084208421083e000000f8000003e0,0xff18c6084210820004008421083e000000f80000001f,0xff18c60842108210842084210830007c00f8000003e0]

def r6p47 : Keys := .leaf [
0xff18c6084210821084208421083e000000083e0003e0,0xff18c6084210821084208421083e007c00f83e0003e0,0xff18c6084210821084208423083e000000f80000001f,0xff18c608421082108420e4210801f0000007c000001f,0xff18c608421082108420fc21080010000007c000001f,0xff18c608421082108420fc210801f00000008000001f,0xff18c608421082108420fc210801f0000007c000001f,0xff18c608421082108420fc210801f07c0007c000001f,0xff18c608421082108420fc2108421f8400f80000001f,0xff18c6084210821085f084210830000000f8000003e0,0xff18c6084210821085f08421083e00000008000003e0,0xff18c6084210821085f08421083e000000f800000040,0xff18c6084210821085f08421083e000000f8000003e0,0xff18c6084210821085f08421083e000000f83e0003e0,0xff18c6084210821085f08421083e007c00f8000003e0,0xff18c6084210821085f0843f084210841f0000007c00]

def r6p48 : Keys := .leaf [
0xff18c6084210821085f0fc210801f0000007c000001f,0xff18c6084210821085f0fc210842108400f8000003e0,0xff18c60842108210c4208421083e00000007c000001f,0xff18c60842108217c4210842f84210841f00000003e0,0xff18c60842108217c5f10842f84210841f00000003e0,0xff18c608421082d0842084210801f0000007c000001f,0xff18c608421082f884208421080010000007c000001f,0xff18c608421082f8842084210801f00000008000001f,0xff18c608421082f8842084210801f0000007c000001f,0xff18c608421082f8842084210801f07c0007c000001f,0xff18c608421082f88420fc210801f0000007c000001f,0xff18c608421082f884210842f842108400f8000003e0,0xff18c608421082f884210be2104210840007c000001f,0xff18c608421082f885f084210801f0000007c000001f,0xff18c608421082f885f10842f842108400f8000003e0,0xff18c6084213e210842084210830000000f8000003e0]

def r6p49 : Keys := .leaf [
0xff18c6084213e21084208421083e00000008000003e0,0xff18c6084213e21084208421083e000000f800000040,0xff18c6084213e21084208421083e000000f8000003e0,0xff18c6084213e21084208421083e000000f83e0003e0,0xff18c6084213e21084208421083e007c00f8000003e0,0xff18c6084213e2108420843f084210841f0000007c00,0xff18c6084213e2108420fc210801f0000007c000001f,0xff18c6084213e2108420fc210842108400f8000003e0,0xff18c6084213e21085f08421083e000000f8000003e0,0xff18c6084213e217c4210842104210841f00000003e0,0xff18c6084213e2f8842084210801f0000007c000001f,0xff18c6084213e2f884208421083e000000f8000003e0,0xff18c6084213e2f8842108421042108400f8000003e0,0xff18c6084213e42108417c421042108400f8000003e0,0xff18c6084218821084208421083e000000f80000001f,0xff18c608427c842108410842107e108400f80000001f]

def r6p50 : Keys := .leaf [
0xff18c608427c842109f10842104210841f0000007c00,0xff18c6084290821084208421083e00000007c000001f,0xff18c6084f90842108410842f84210841f00000003e0,0xff18c6084f90842108417c42104210840007c000001f,0xff18c6084f90842109f10842104210841f00000003e0,0xff18c6084f9084213e410842104210841f000000001f,0xff18c6084f93e42109f10842104210841f00000003e0,0xff18c60980000210842084210801f0000007c000001f,0xff18c609c2108210842084210801f0000007c000001f,0xff18c609f0000210842084210801f0000007c000001f,0xff18c609f210821084208421080010000007c000001f,0xff18c609f2108210842084210801f00000008000001f,0xff18c609f2108210842084210801f0000007c000001f,0xff18c609f2108210842084210801f07c0007c000001f,0xff18c609f21082108420843f0842108400f80000001f,0xff18c609f21082108420fc210801f0000007c000001f]

def r6p51 : Keys := .leaf [
0xff18c609f210821085f084210801f0000007c000001f,0xff18c609f210821085f08421083e000000f8000003e0,0xff18c609f210821085f108421042108400f8000003e0,0xff18c609f2108217c4210842104210840007c000001f,0xff18c609f21082f8842084210801f0000007c000001f,0xff18c609f210842108410842f842108400f8000003e0,0xff18c609f210842109f108421042108400f8000003e0,0xff18c609f21084213e4108421042108400f80000001f,0xff18c609f2108427c8410842104210840007c000001f,0xff18c609f213e210842084210801f0000007c000001f,0xff18c609f213e42109f108421042108400f8000003e0,0xff18c60a1084221084207c000001f0000007c000001f,0xff18c60a5294a2108420843f083e000000f80000001f,0xff18c60a5294a2108420fc210801f0000007c000001f,0xff18c60a5294a21085f08421083e000000f8000003e0,0xff18c60a5294a2f8842084210801f0000007c000001f]

def r6p52 : Keys := .leaf [
0xff18c60bf294a210842084210801f0000007c000001f,0xff18c60bf294a2108420fc210801f0000007c000001f,0xff18c60c2108410842107c000001f0000007c000001f,0xff18c60c6318c10842107c000001f00000008000001f,0xff18c60c6318c2108420fc210801f0000007c000001f,0xff18c60c6318c21085f08421083e000000f8000003e0,0xff18c60c6318c217c4208421083e00000007c000001f,0xff18c60c6318c2f8842084210801f0000007c000001f,0xff18c60c631be21084208421083e000000f8000003e0,0xff18c60c631be21085f08421083e000000f8000003e0,0xff18c60df318c210842084210801f0000007c000001f,0xff18c60df318c2f8842084210801f0000007c000001f,0xff18c6108421042109f17c421042108400f8000003e0,0xff18c610842104f908410842f842108400f8000003e0,0xff18c610847d042108410842107e108400f80000001f,0xff18c610847d042108410842f84210841f0000007c00]

def r6p53 : Keys := .leaf [
0xff18c610847d042108417c421042108400f80000001f,0xff18c610847d042109f10842104210841f0000007c00,0xff18c610847d04f9084108421042108400f80000001f,0xff18c6108fa1042108410842107e10840007c000001f,0xff18c6108fa1042108410842f84210841f00000003e0,0xff18c6108fa1042108417c42104210840007c000001f,0xff18c6108fa1042109f10842104210841f00000003e0,0xff18c6108fa104f908410842104210840007c000001f,0xff18c6318c63042109f17c421042108400f8000003e0,0xff18c6318c6304f908410842f842108400f8000003e0,0xff18c6318c7f042108410842107e108400f80000001f,0xff18c6318c7f042108410842f84210841f0000007c00,0xff18c6318c7f042108417c421042108400f80000001f,0xff18c6318c7f042109f10842104210841f0000007c00,0xff18c6318c7f04f9084108421042108400f80000001f,0xff18c6318fe3042108410842107e10840007c000001f]

def r6p54 : Keys := .leaf [
0xff18c6318fe3042108410842f84210841f00000003e0,0xff18c6318fe3042108417c42104210840007c000001f,0xff18c6318fe3042109f10842104210841f00000003e0,0xff18c6318fe304f908410842104210840007c000001f,0xff18c63e0000042108410842f8421f841f0000007c00,0xff18c63e0000042108410be210421f841f000000001f,0xff18c63e0000042109f10be2104210841f00000003e0,0xff18c63e0000042109f17c421042108400f8000003e0,0xff18c63e000004213e410842107e108400f80000001f,0xff18c63e00000427c8410842f84210841f00000003e0,0xff18c63e00000427c8417c42104210840007c000001f,0xff18c63e000004f90841084210421f8400f80000001f,0xff18c63e000004f908410842f842108400f8000003e0,0xff18c63e000004f908410be2104210840007c000001f,0xff18c63e007c042108410842107e108400f80000001f,0xff18c63e007c042108410842f84210841f0000007c00]

def r6p55 : Keys := .leaf [
0xff18c63e007c042108410be2104210841f000000001f,0xff18c63e007c042108417c421042108400f80000001f,0xff18c63e007c042109f10842104210841f0000007c00,0xff18c63e007c0427c8410842104210841f000000001f,0xff18c63e007c04f9084108421042108400f80000001f,0xff18c63e0f8004210841084210421f841f000000001f,0xff18c63e0f80042108410842107e10840007c000001f,0xff18c63e0f80042108410842f84210841f00000003e0,0xff18c63e0f80042108417c42104210840007c000001f,0xff18c63e0f80042109f10842104210841f00000003e0,0xff18c63e0f8004213e410842104210841f000000001f,0xff18c63e0f8004f908410842104210840007c000001f,0xff18c63e8421042109f17c421042108400f8000003e0,0xff18c63e842104f908410842f842108400f8000003e0,0xff18c63e847d042108410842107e108400f80000001f,0xff18c63e847d042108410842f84210841f0000007c00]

def r6p56 : Keys := .leaf [
0xff18c63e847d042108417c421042108400f80000001f,0xff18c63e847d042109f10842104210841f0000007c00,0xff18c63e847d04f9084108421042108400f80000001f,0xff18c63e8fa1042108410842107e10840007c000001f,0xff18c63e8fa1042108410842f84210841f00000003e0,0xff18c63e8fa1042108417c42104210840007c000001f,0xff18c63e8fa1042109f10842104210841f00000003e0,0xff18c63e8fa104f908410842104210840007c000001f,0xff18d6084210821084208421083e000000f80000001f,0xff18fe3e0000042108410842f84210841f0000007c00,0xff18fe3e0000042108417c421042108400f80000001f,0xff18fe3e00000427c8410842104210841f000000001f,0xff18fe3e0f80042108410842104210841f000000001f,0xff18fe3e8421042108410842f84210841f0000007c00,0xff18fe3e8421042108417c421042108400f80000001f,0xff18fe3e8fa1042108410842104210841f000000001f]

def r6p57 : Keys := .leaf [
0xff18fe3f8c63042108410842107e108400f80000001f,0xff18fe3f8c63042108410842f84210841f0000007c00,0xff18fe3f8c63042108417c421042108400f80000001f,0xff18fe3f8c63042109f10842104210841f0000007c00,0xff18fe3f8c6304f9084108421042108400f80000001f,0xff19c6084210821084208421083e00000007c000001f,0xff1fc63e0000042108410842107e10840007c000001f,0xff1fc63e000004213e410842104210841f000000001f,0xff1fc63e007c042108410842104210841f000000001f,0xff1fc63e8421042108410842107e10840007c000001f,0xff1fc63e847d042108410842104210841f000000001f,0xff1fc63f8c63042108410842107e10840007c000001f,0xff1fc63f8c63042108410842f84210841f00000003e0,0xff1fc63f8c63042108417c42104210840007c000001f,0xff1fc63f8c63042109f10842104210841f00000003e0,0xff1fc63f8c6304f908410842104210840007c000001f]

def r6p58 : Keys := .leaf [
0xff1fc63f8c7f042108410842104210841f000000001f]

def r6 : Keys := (.branch 0xfc0010210842084210821084f885f1082108420f8000 (.branch 0xfc0000318c630427c8410842f87e10842108420003e0 (.branch 0xfc0000210fc20842148318c6304210841f000000001f (.branch 0xfc0000210842084210830842f8421f841f0000007c00 (.branch 0xfc00002108420842108210842084317c210fc20f8000 r6p0 (.branch 0xfc0000210842084210827c842084217c210fc2000400 r6p1 r6p2)) (.branch 0xfc000021087e0842108213e420be217c4210be108421 (.branch 0xfc000021084a0842108318c6f84210841f0000007c00 r6p3 r6p4) (.branch 0xfc00002108c2084210821084f8be21082108420003e0 r6p5 r6p6))) (.branch 0xfc0000318c63042108410be2107e1084210fc200001f (.branch 0xfc0000318c63040001f1084210421f841f0000007c00 r6p7 (.branch 0xfc0000318c63042108410842107e108400083e0003e0 r6p8 r6p9)) (.branch 0xfc0000318c63042109f17c421042108400f800000040 (.branch 0xfc0000318c63042109f1084210421f841f003e007c00 r6p10 r6p11) (.branch 0xfc0000318c6304213e417c4210421f8400f80000001f r6p12 r6p13)))) (.branch 0xfc0000318c7f040001f10842104210841f0000007c00 (.branch 0xfc0000318c6304f909f1084210421f8400f80000001f (.branch 0xfc0000318c6304e109f108421042108400f8000003e0 r6p14 (.branch 0xfc0000318c6304f908410842f8842108210fc2007c00 r6p15 r6p16)) (.branch 0xfc0000318c6306318df10be2f84210841f00000003e0 (.branch 0xfc0000318c6305f8421108421001f0000007c000001f r6p17 r6p18) (.branch 0xfc0000318c6308423e821084f8be2108210842007c00 r6p19 r6p20))) (.branch 0xfc0000318c7f08423e8213e420be210821084200001f (.branch 0xfc0000318c7f042148410842104210841f000000001f (.branch 0xfc0000318c7f042108417c421042108400080000001f r6p21 r6p22) (.branch 0xfc0000318c7f04f908410842107e108400f80000001f r6p23 r6p24)) (.branch 0xfc0000318fe304213e4108421042108418000000001f (.branch 0xfc0000318fe3042108410002004210841f000000001f r6p25 r6p26) (.branch 0xfc0000318fe305297e510842104210841f000000001f r6p27 r6p28))))) (.branch 0xfe10843e84210427c8410842f84210841f00000003e0 (.branch 0xfe108410842105f94a51084210421f8400f80000001f (.branch 0xfc1f003e000018c631827c842084217c2108420003e0 (.branch 0xfc0010318c63042109f10842104210841f0000007c00 r6p29 (.branch 0xfc0100210842084210827c842084217c2108420003e0 r6p30 r6p31)) (.branch 0xfe1084108421042109f10862104210841f00000003e0 (.branch 0xfe1084108421040001f10842107e108400f8000003e0 r6p32 r6p33) (.branch 0xfe108410842104f908410842f84210840008000003e0 r6p34 r6p35))) (.branch 0xfe10841084a1042108417c42104210840007c000001f (.branch 0xfe108410847d042108410be2f884217c2108420f8000 (.branch 0xfe1084108429042108410842107e108400f80000001f r6p36 r6p37) (.branch 0xfe108410847d04f908410842107e108400f80000001f r6p38 r6p39)) (.branch 0xfe1084108fa108423e821084f88421082108420f8000 (.branch 0xfe1084108fa104213e421084208421083f084200001f r6p40 r6p41) (.branch 0xfe10843e007c0842108213e420be210821084200001f r6p42 r6p43)))) (.branch 0xff18c609f210821085f084210801f0000007c000001f (.branch 0xff18c6084210821084208421083e000000083e0003e0 (.branch 0xfe10fc3e8421042108410842f84210841f0000007c00 r6p44 (.branch 0xfe1f843e847d042108410842104210841f000000001f r6p45 r6p46)) (.branch 0xff18c6084213e21084208421083e00000008000003e0 (.branch 0xff18c6084210821085f0fc210801f0000007c000001f r6p47 r6p48) (.branch 0xff18c608427c842109f10842104210841f0000007c00 r6p49 r6p50))) (.branch 0xff18c63e007c042108410be2104210841f000000001f (.branch 0xff18c610847d042108417c421042108400f80000001f (.branch 0xff18c60bf294a210842084210801f0000007c000001f r6p51 r6p52) (.branch 0xff18c6318fe3042108410842f84210841f00000003e0 r6p53 r6p54)) (.branch 0xff18fe3f8c63042108410842107e108400f80000001f (.branch 0xff18c63e847d042108417c421042108400f80000001f r6p55 r6p56) (.branch 0xff1fc63f8c7f042108410842104210841f000000001f r6p57 r6p58))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p0 : r6p0.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p1 : r6p1.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p2 : r6p2.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p3 : r6p3.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p4 : r6p4.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p5 : r6p5.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p6 : r6p6.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p7 : r6p7.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p8 : r6p8.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p9 : r6p9.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p10 : r6p10.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p11 : r6p11.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p12 : r6p12.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p13 : r6p13.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p14 : r6p14.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p15 : r6p15.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p16 : r6p16.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p17 : r6p17.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p18 : r6p18.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p19 : r6p19.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p20 : r6p20.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p21 : r6p21.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p22 : r6p22.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p23 : r6p23.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p24 : r6p24.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p25 : r6p25.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p26 : r6p26.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p27 : r6p27.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p28 : r6p28.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p29 : r6p29.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p30 : r6p30.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p31 : r6p31.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p32 : r6p32.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p33 : r6p33.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p34 : r6p34.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p35 : r6p35.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p36 : r6p36.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p37 : r6p37.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p38 : r6p38.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p39 : r6p39.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p40 : r6p40.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p41 : r6p41.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p42 : r6p42.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p43 : r6p43.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p44 : r6p44.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p45 : r6p45.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p46 : r6p46.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p47 : r6p47.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p48 : r6p48.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p49 : r6p49.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p50 : r6p50.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p51 : r6p51.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p52 : r6p52.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p53 : r6p53.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p54 : r6p54.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p55 : r6p55.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p56 : r6p56.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p57 : r6p57.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p58 : r6p58.all (checkQ 5 (dfs 0 (fun _ => false) 5)) = true := by decide +kernel

theorem badr6 : Rejects 6 r6 :=
  verifyTable 5 (dfs 0 (fun _ => false) 5) r6 (dfsSound 0 (fun _ => false) noneSound 5) (by
    unfold r6
    simp only [allBranch, Bool.and_true, goodr6p0, goodr6p1, goodr6p2, goodr6p3, goodr6p4, goodr6p5, goodr6p6, goodr6p7, goodr6p8, goodr6p9, goodr6p10, goodr6p11, goodr6p12, goodr6p13, goodr6p14, goodr6p15, goodr6p16, goodr6p17, goodr6p18, goodr6p19, goodr6p20, goodr6p21, goodr6p22, goodr6p23, goodr6p24, goodr6p25, goodr6p26, goodr6p27, goodr6p28, goodr6p29, goodr6p30, goodr6p31, goodr6p32, goodr6p33, goodr6p34, goodr6p35, goodr6p36, goodr6p37, goodr6p38, goodr6p39, goodr6p40, goodr6p41, goodr6p42, goodr6p43, goodr6p44, goodr6p45, goodr6p46, goodr6p47, goodr6p48, goodr6p49, goodr6p50, goodr6p51, goodr6p52, goodr6p53, goodr6p54, goodr6p55, goodr6p56, goodr6p57, goodr6p58])

def r8p0 : Keys := .leaf [
0x1f80000421084108421042108410842f8421f841f0000007c00,0x1f80000421084108421042108410be210421f841f000000001f,0x1f80000421084108421042109f10be2104210841f00000003e0,0x1f80000421084108421042109f17c421042108400f8000003e0,0x1f8000042108410842104213e410842107e108400f80000001f,0x1f800004210841084210427c8410842f84210841f00000003e0,0x1f800004210841084210427c8417c42104210840007c000001f,0x1f8000042108410842104f90841084210421f8400f80000001f,0x1f8000042108410842104f908410842f842108400f8000003e0,0x1f8000042108410842104f908410be2104210840007c000001f,0x1f800004210fc108421042108410842f84210841f0000007c00,0x1f800004210fc108421042108417c421042108400f80000001f,0x1f800004210fc1084210427c8410842104210841f000000001f,0x1f80000421f84108421042108410842107e10840007c000001f,0x1f80000421f8410842104213e410842104210841f000000001f,0x1f80000421f8410847d042108410842104210841f000000001f]

def r8p1 : Keys := .leaf [
0x1f800006318c608421082108420843f083e000000f80000001f,0x1f800006318c608421082108420fc210801f0000007c000001f,0x1f800006318c6084210821085f08421083e000000f8000003e0,0x1f800006318c60842108217c4208421083e00000007c000001f,0x1f800006318c608421082f8842084210801f0000007c000001f,0x1f800006318c6084213e21084208421083e000000f8000003e0,0x1f800006318c608427c821084208421083e000000f80000001f,0x1f800006318c6084f90821084208421083e00000007c000001f,0x1f800006318c609f2108210842084210801f0000007c000001f,0x1f800006318fe084210821084208421083e000000f80000001f,0x1f80000631fc6084210821084208421083e00000007c000001f,0x1fc210821084208421082108420fc210801f0000007c000001f,0x1fc2108210842084210821085f08421083e000000f8000003e0,0x1fc210821084208421082f8842084210801f0000007c000001f,0x1fc2108210842084213e21084208421083e000000f8000003e0,0x1fc210821084209f2108210842084210801f0000007c000001f]

def r8p2 : Keys := .leaf [
0x1fc21082108fa084210821084208421083e000000f80000001f,0x1fc2108211f42084210821084208421083e00000007c000001f,0x1fe318c108421042108410842107c000001f0000007c000001f,0x3f0000084210821084208000002108420843f083e000000f80000001f,0x3f0000084210821084208000002108420fc210801f0000007c000001f,0x3f00000842108210842080000021085f08421083e000000f8000003e0,0x3f000008421082108420800000217c4208421083e00000007c000001f,0x3f0000084210821084208000002f8842084210801f0000007c000001f,0x3f00000842108210842080003e21084208421083e000000f8000003e0,0x3f0000084210821084208007c021084208421083e000000f80000001f,0x3f00000842108210842080f80021084208421083e00000007c000001f,0x3f00000842108210842084210820004008421083e000000f80000001f,0x3f00000842108210842084210821084208421083e000000083e0003e0,0x3f00000842108210842084210821084208421083e007c00f83e0003e0,0x3f00000842108210842084210821084208423083e000000f80000001f,0x3f0000084210821084208421082108420843f083e000000080000001f]

def r8p3 : Keys := .leaf [
0x3f0000084210821084208421082108420843f083e000000f83e00001f,0x3f0000084210821084208421082108420843f083e007c00f80000001f,0x3f0000084210821084208421082108420fc21080010000007c000001f,0x3f0000084210821084208421082108420fc210801f00000008000001f,0x3f0000084210821084208421082108420fc210801f07c0007c000001f,0x3f0000084210821084208421082108420fc2108421f8400f80000001f,0x3f00000842108210842084210821085f08421083e00000008000003e0,0x3f00000842108210842084210821085f08421083e000000f800000040,0x3f00000842108210842084210821085f08421083e000000f83e0003e0,0x3f00000842108210842084210821085f08421083e007c00f8000003e0,0x3f00000842108210842084210821085f0843f083e000000f80000001f,0x3f00000842108210842084210821085f0843f083e000000f8000003e0,0x3f00000842108210842084210821085f0843f084210841f0000007c00,0x3f00000842108210842084210821085f0fc210801f0000007c000001f,0x3f00000842108210842084210821085f0fc210842108400f8000003e0,0x3f00000842108210842084210821085f1084210421f841f0000007c00]

def r8p4 : Keys := .leaf [
0x3f000008421082108420842108210c4208421083e00000007c000001f,0x3f000008421082108420842108217c4208421083e000000008000001f,0x3f000008421082108420842108217c4208421083e007c0007c000001f,0x3f000008421082108420842108217c420843f083e00000007c000001f,0x3f000008421082108420842108217c420843f083e000000f80000001f,0x3f000008421082108420842108217c420843f084210841f000000001f,0x3f000008421082108420842108217c420fc210801f0000007c000001f,0x3f000008421082108420842108217c420fc21084210840007c000001f,0x3f000008421082108420842108217c421084210421f841f000000001f,0x3f000008421082108420842108217c4210842f84210841f00000003e0,0x3f000008421082108420842108217c5f08421083e00000007c000001f,0x3f000008421082108420842108217c5f10842f84210841f00000003e0,0x3f0000084210821084208421082f884208421080010000007c000001f,0x3f0000084210821084208421082f8842084210801f00000008000001f,0x3f0000084210821084208421082f8842084210801f07c0007c000001f,0x3f0000084210821084208421082f88420843f0801f0000007c000001f]

def r8p5 : Keys := .leaf [
0x3f0000084210821084208421082f88420fc210801f0000007c000001f,0x3f0000084210821084208421082f88421084210421f8400f80000001f,0x3f0000084210821084208421082f884210842f842108400f8000003e0,0x3f0000084210821084208421082f884210be2104210840007c000001f,0x3f0000084210821084208421082f885f084210801f0000007c000001f,0x3f0000084210821084208421082f885f10842f842108400f8000003e0,0x3f00000842108210842084213e21084208421083e00000008000003e0,0x3f00000842108210842084213e21084208421083e000000f800000040,0x3f00000842108210842084213e21084208421083e000000f83e0003e0,0x3f00000842108210842084213e21084208421083e007c00f8000003e0,0x3f00000842108210842084213e2108420843f083e000000f80000001f,0x3f00000842108210842084213e2108420843f084210841f0000007c00,0x3f00000842108210842084213e2108420fc210801f0000007c000001f,0x3f00000842108210842084213e2108420fc210842108400f8000003e0,0x3f00000842108210842084213e21085f08421083e000000f8000003e0,0x3f00000842108210842084213e217c4208421083e00000007c000001f]

def r8p6 : Keys := .leaf [
0x3f00000842108210842084213e217c4208421083e000000f8000003e0,0x3f00000842108210842084213e217c4210842104210841f00000003e0,0x3f00000842108210842084213e2f8842084210801f0000007c000001f,0x3f00000842108210842084213e2f884208421083e000000f8000003e0,0x3f00000842108210842084213e2f8842108421042108400f8000003e0,0x3f00000842108210842084213e42108410be2104210841f00000003e0,0x3f00000842108210842084213e42108417c421042108400f8000003e0,0x3f00000842108210842084218821084208421083e000000f80000001f,0x3f0000084210821084208427c821084208421083e000000080000001f,0x3f0000084210821084208427c821084208421083e000000f83e00001f,0x3f0000084210821084208427c821084208421083e007c00f80000001f,0x3f0000084210821084208427c82108420843f083e000000f80000001f,0x3f0000084210821084208427c82108420fc210801f0000007c000001f,0x3f0000084210821084208427c82108420fc21083e000000f80000001f,0x3f0000084210821084208427c82108420fc210842108400f80000001f,0x3f0000084210821084208427c821085f08421083e000000f8000003e0]

def r8p7 : Keys := .leaf [
0x3f0000084210821084208427c821085f10842104210841f0000007c00,0x3f0000084210821084208427c8217c4208421083e00000007c000001f,0x3f0000084210821084208427c8217c4210842104210841f000000001f,0x3f0000084210821084208427c82f8842084210801f0000007c000001f,0x3f0000084210821084208427c82f8842108421042108400f80000001f,0x3f0000084210821084208427c842108410842107e108400f80000001f,0x3f0000084210821084208427c842109f10842104210841f0000007c00,0x3f00000842108210842084290821084208421083e00000007c000001f,0x3f00000842108210842084f90821084208421083e000000008000001f,0x3f00000842108210842084f90821084208421083e007c0007c000001f,0x3f00000842108210842084f9082108420843f083e000000f80000001f,0x3f00000842108210842084f9082108420843f084210841f000000001f,0x3f00000842108210842084f9082108420fc210801f0000007c000001f,0x3f00000842108210842084f9082108420fc21084210840007c000001f,0x3f00000842108210842084f90821085f08421083e00000007c000001f,0x3f00000842108210842084f90821085f08421083e000000f8000003e0]

def r8p8 : Keys := .leaf [
0x3f00000842108210842084f90821085f10842104210841f00000003e0,0x3f00000842108210842084f908217c4208421083e00000007c000001f,0x3f00000842108210842084f9082f8842084210801f0000007c000001f,0x3f00000842108210842084f9082f884208421083e00000007c000001f,0x3f00000842108210842084f9082f884210842104210840007c000001f,0x3f00000842108210842084f90842108410842f84210841f00000003e0,0x3f00000842108210842084f90842108417c42104210840007c000001f,0x3f00000842108210842084f90842109f10842104210841f00000003e0,0x3f00000842108210842084f9084213e410842104210841f000000001f,0x3f00000842108210842084f93e21084208421083e00000007c000001f,0x3f00000842108210842084f93e42109f10842104210841f00000003e0,0x3f0000084210821084209f0000210842084210801f0000007c000001f,0x3f0000084210821084209f210821084208421080010000007c000001f,0x3f0000084210821084209f2108210842084210801f00000008000001f,0x3f0000084210821084209f2108210842084210801f07c0007c000001f,0x3f0000084210821084209f21082108420843f0801f0000007c000001f]

def r8p9 : Keys := .leaf [
0x3f0000084210821084209f21082108420843f083e000000f80000001f,0x3f0000084210821084209f21082108420843f0842108400f80000001f,0x3f0000084210821084209f21082108420fc210801f0000007c000001f,0x3f0000084210821084209f210821085f084210801f0000007c000001f,0x3f0000084210821084209f210821085f08421083e000000f8000003e0,0x3f0000084210821084209f210821085f108421042108400f8000003e0,0x3f0000084210821084209f2108217c42084210801f0000007c000001f,0x3f0000084210821084209f2108217c4208421083e00000007c000001f,0x3f0000084210821084209f2108217c4210842104210840007c000001f,0x3f0000084210821084209f21082f8842084210801f0000007c000001f,0x3f0000084210821084209f21084210841084210421f8400f80000001f,0x3f0000084210821084209f210842108410842f842108400f8000003e0,0x3f0000084210821084209f210842108410be2104210840007c000001f,0x3f0000084210821084209f210842109f108421042108400f8000003e0,0x3f0000084210821084209f21084213e4108421042108400f80000001f,0x3f0000084210821084209f2108427c8410842104210840007c000001f]

def r8p10 : Keys := .leaf [
0x3f0000084210821084209f213e210842084210801f0000007c000001f,0x3f0000084210821084209f213e42109f108421042108400f8000003e0,0x3f000008421082108420a1084221084207c000001f0000007c000001f,0x3f000008421082108420a5294a2108420843f083e000000f80000001f,0x3f000008421082108420a5294a2108420fc210801f0000007c000001f,0x3f000008421082108420a5294a21085f08421083e000000f8000003e0,0x3f000008421082108420a5294a217c4208421083e00000007c000001f,0x3f000008421082108420a5294a2f8842084210801f0000007c000001f,0x3f000008421082108420a52fca21084208421083e000000f80000001f,0x3f000008421082108420a52fca2108420843f083e000000f80000001f,0x3f000008421082108420bf294a210842084210801f0000007c000001f,0x3f000008421082108420bf294a2108420fc210801f0000007c000001f,0x3f000008421082108420c2108410842107c000001f0000007c000001f,0x3f000008421082108420c6318c10842107c000001f00000008000001f,0x3f000008421082108420c6318c2108420843f083e000000f80000001f,0x3f000008421082108420c6318c2108420fc210801f0000007c000001f]

def r8p11 : Keys := .leaf [
0x3f000008421082108420c6318c21085f08421083e000000f8000003e0,0x3f000008421082108420c6318c217c4208421083e00000007c000001f,0x3f000008421082108420c6318c2f8842084210801f0000007c000001f,0x3f000008421082108420c631be21084208421083e000000f8000003e0,0x3f000008421082108420c631be21085f08421083e000000f8000003e0,0x3f000008421082108420c6f98c21084208421083e00000007c000001f,0x3f000008421082108420c6f98c217c4208421083e00000007c000001f,0x3f000008421082108420df318c210842084210801f0000007c000001f,0x3f000008421082108420df318c2f8842084210801f0000007c000001f,0x3f000008421082108fa108421042108410842107e108400f80000001f,0x3f000008421082108fa108421042108410842f84210841f0000007c00,0x3f000008421082108fa108421042108417c421042108400f80000001f,0x3f000008421082108fa108421042109f10842104210841f0000007c00,0x3f000008421082108fa1084210427c8410842104210841f000000001f,0x3f000008421082108fa10842104f9084108421042108400f80000001f,0x3f00000842108211f42108421042108410842107e10840007c000001f]

def r8p12 : Keys := .leaf [
0x3f00000842108211f42108421042108410842f84210841f00000003e0,0x3f00000842108211f42108421042108417c42104210840007c000001f,0x3f00000842108211f42108421042109f10842104210841f00000003e0,0x3f00000842108211f4210842104213e410842104210841f000000001f,0x3f00000842108211f4210842104f908410842104210840007c000001f,0x3f00000842128210842084210821084208421083e000000f80000001f,0x3f000008421f8210842080000021084208421083e000000f80000001f,0x3f000008421f8210842084210821084208421083e000000080000001f,0x3f000008421f8210842084210821084208421083e000000f83e00001f,0x3f000008421f8210842084210821084208421083e007c00f80000001f,0x3f000008421f821084208421082108420843f083e000000f80000001f,0x3f000008421f821084208421082108420fc21083e000000f80000001f,0x3f000008421f8210842084210821085f08421083e000000f80000001f,0x3f000008421f8210842084210821085f08421083e000000f8000003e0,0x3f000008421f8210842084210821085f10842104210841f0000007c00,0x3f000008421f82108420842108217c4208421083e00000007c000001f]

def r8p13 : Keys := .leaf [
0x3f000008421f82108420842108217c4210842104210841f000000001f,0x3f000008421f821084208421082f8842084210801f0000007c000001f,0x3f000008421f821084208421082f884208421083e000000f80000001f,0x3f000008421f821084208421082f8842108421042108400f80000001f,0x3f000008421f8210842084213e21084208421083e000000f80000001f,0x3f000008421f821084208427c821084208421083e000000f80000001f,0x3f000008421f8210842084f90821084208421083e00000007c000001f,0x3f000008421f8210842084f90821084208421083e000000f80000001f,0x3f000008421f8210842084f90842108410842104210841f000000001f,0x3f000008421f821084209f210821084208421083e000000f80000001f,0x3f000008421f82108420a5294a21084208421083e000000f80000001f,0x3f000008421f82108420c6318c21084208421083e000000f80000001f,0x3f000008421f82108fa084210821084208421083e000000f80000001f,0x3f000008421f8211f42108421042108410842104210841f000000001f,0x3f00000842308210842084210821084208421083e00000007c000001f,0x3f00000843f08210842080000021084208421083e00000007c000001f]

def r8p14 : Keys := .leaf [
0x3f00000843f08210842084210821084208421083e000000008000001f,0x3f00000843f08210842084210821084208421083e007c0007c000001f,0x3f00000843f0821084208421082108420843f083e000000f80000001f,0x3f00000843f0821084208421082108420843f084210841f000000001f,0x3f00000843f0821084208421082108420fc210801f0000007c000001f,0x3f00000843f0821084208421082108420fc21083e00000007c000001f,0x3f00000843f0821084208421082108420fc21084210840007c000001f,0x3f00000843f08210842084210821085f08421083e00000007c000001f,0x3f00000843f082108420842108217c4208421083e00000007c000001f,0x3f00000843f0821084208421082f884208421083e00000007c000001f,0x3f00000843f08210842084213e21084208421083e00000007c000001f,0x3f00000843f0821084208427c821084208421083e00000007c000001f,0x3f00000843f0821084208427c821084208421083e000000f80000001f,0x3f00000843f0821084208427c842108410842104210841f000000001f,0x3f00000843f08210842084f90821084208421083e00000007c000001f,0x3f00000843f0821084209f210821084208421083e00000007c000001f]

def r8p15 : Keys := .leaf [
0x3f00000843f082108420a5294a21084208421083e00000007c000001f,0x3f00000843f082108420c6318c21084208421083e00000007c000001f,0x3f00000843f082108fa084210821084208421083e00000007c000001f,0x3f00000843f082108fa084210821084208421083e000000f80000001f,0x3f00000843f082108fa108421042108410842104210841f000000001f,0x3f00000843f08211f42084210821084208421083e00000007c000001f,0x3f00000843f084210fc108421042108410842104210841f000000001f,0x3f00000c6318c100000042108410842107c000001f0000007c000001f,0x3f00000c6318c1084210421084108421060000001f0000007c000001f,0x3f00000c6318c108421042108410842107c00000010000007c000001f,0x3f00000c6318c108421042108410842107c000001f00000008000001f,0x3f00000c6318c108421042108410842107c000001f07c0007c000001f,0x3f00000c6318c108421042108410842107c00f801f0000007c000001f,0x3f00000c6318c10842104210841087e107c000001f0000007c000001f,0x3f00000c6318c10842104210841087e108421083e000000f80000001f,0x3f00000c6318c10842104210841f842107c000001f0000007c000001f]

def r8p16 : Keys := .leaf [
0x3f00000c6318c10842104210841f8421084210801f0000007c000001f,0x3f00000c6318c10842104210be10842107c000001f0000007c000001f,0x3f00000c6318c10842104210be21084208421083e000000f8000003e0,0x3f00000c6318c108421042f88410842107c000001f0000007c000001f,0x3f00000c6318c108421042f88421084208421083e00000007c000001f,0x3f00000c6318c10842105f108410842107c000001f0000007c000001f,0x3f00000c6318c10842105f1084210842084210801f0000007c000001f,0x3f00000c6318c108427c42108410842107c000001f0000007c000001f,0x3f00000c6318c108427c84210821084208421083e000000f8000003e0,0x3f00000c6318c1084f9042108410842107c000001f0000007c000001f,0x3f00000c6318c1084f9084210821084208421083e000000f80000001f,0x3f00000c6318c109f21042108410842107c000001f0000007c000001f,0x3f00000c6318c109f21084210821084208421083e00000007c000001f,0x3f00000c6318c13e421042108410842107c000001f0000007c000001f,0x3f00000c6318c13e4210842108210842084210801f0000007c000001f,0x3f00000c6318c14a529442108410842107c000001f0000007c000001f]

def r8p17 : Keys := .leaf [
0x3f00000c6318c18c631842108410842107c000001f0000007c000001f,0x3f00000c6318c21084208421082108420843f083e000000f80000001f,0x3f00000c6318c21084208421082108420fc210801f0000007c000001f,0x3f00000c6318c210842084210821085f08421083e000000f8000003e0,0x3f00000c6318c2108420842108217c4208421083e00000007c000001f,0x3f00000c6318c21084208421082f8842084210801f0000007c000001f,0x3f00000c6318c210842084213e21084208421083e000000f8000003e0,0x3f00000c6318c21084208427c821084208421083e000000f80000001f,0x3f00000c6318c210842084f90821084208421083e00000007c000001f,0x3f00000c6318c21084209f2108210842084210801f0000007c000001f,0x3f00000c6318c2108fa084210821084208421083e000000f80000001f,0x3f00000c6318c211f42084210821084208421083e00000007c000001f,0x3f00000c631fc108421042108410842107c000001f0000007c000001f,0x3f00000c631fc210842084210821084208421083e000000f80000001f,0x3f00000c631fc2108fa084210821084208421083e000000f80000001f,0x3f00000c631fc6318c6084210821084208421083e000000f80000001f]

def r8p18 : Keys := .leaf [
0x3f00000c63f8c108421042108410842107c000001f0000007c000001f,0x3f00000c63f8c210842084210821084208421083e00000007c000001f,0x3f00000c63f8c211f42084210821084208421083e00000007c000001f,0x3f00000c63f8c6318c6084210821084208421083e00000007c000001f,0x3f00040842108210842084210821084208421083e000000f80000001f,0x3f003e0f80000421084108421042108410842107e108400f80000001f,0x3f003e0f80000421084108421042108410842f84210841f0000007c00,0x3f003e0f80000421084108421042108410be2104210841f000000001f,0x3f003e0f80000421084108421042108417c421042108400f80000001f,0x3f003e0f80000421084108421042109f10842104210841f0000007c00,0x3f003e0f800004210841084210427c8410842104210841f000000001f,0x3f003e0f8000042108410842104f9084108421042108400f80000001f,0x3f003e0f80000421f84108421042108410842104210841f000000001f,0x3f003e0f800006318c6084210821084208421083e000000f80000001f,0x3f00400842108210842084210821084208421083e00000007c000001f,0x3f07c00f8000042108410842104210841084210421f841f000000001f]

def r8p19 : Keys := .leaf [
0x3f07c00f80000421084108421042108410842107e10840007c000001f,0x3f07c00f80000421084108421042108410842f84210841f00000003e0,0x3f07c00f80000421084108421042108417c42104210840007c000001f,0x3f07c00f80000421084108421042109f10842104210841f00000003e0,0x3f07c00f8000042108410842104213e410842104210841f000000001f,0x3f07c00f8000042108410842104f908410842104210840007c000001f,0x3f07c00f800004210fc108421042108410842104210841f000000001f,0x3f07c00f800006318c6084210821084208421083e00000007c000001f,0x3f07c00f801f0421084108421042108410842104210841f000000001f,0x3f4210884210821084208421082108420fc210801f0000007c000001f,0x3f42108842108210842084210821085f08421083e000000f8000003e0,0x3f4210884210821084208421082f8842084210801f0000007c000001f,0x3f42108842108210842084213e21084208421083e000000f8000003e0,0x3f4210884210821084209f2108210842084210801f0000007c000001f,0x3f421088421f8210842084210821084208421083e000000f80000001f,0x3f42108843f08210842084210821084208421083e00000007c000001f]

def r8p20 : Keys := .leaf [
0x3f42108c6318c108421042108410842107c000001f0000007c000001f,0x3f84210421084100000042108410842107c000001f0000007c000001f,0x3f84210421084108421042108410842107c00000010000007c000001f,0x3f84210421084108421042108410842107c000001f00000008000001f,0x3f84210421084108421042108410842107c000001f07c0007c000001f,0x3f84210421084108421042108410842107c00f801f0000007c000001f,0x3f8421042108410842104210841087e108421083e000000f80000001f,0x3f8421042108410842104210841f842107c000001f0000007c000001f,0x3f8421042108410842104210841f8421084210801f0000007c000001f,0x3f8421042108410842104210be10842107c000001f0000007c000001f,0x3f8421042108410842104210be21084208421083e000000f8000003e0,0x3f84210421084108421042f88421084208421083e00000007c000001f,0x3f8421042108410842105f108410842107c000001f0000007c000001f,0x3f8421042108410842105f1084210842084210801f0000007c000001f,0x3f84210421084108427c42108410842107c000001f0000007c000001f,0x3f84210421084108427c84210821084208421083e000000f8000003e0]

def r8p21 : Keys := .leaf [
0x3f842104210841084f9084210821084208421083e000000f80000001f,0x3f84210421084109f21084210821084208421083e00000007c000001f,0x3f8421042108413e421042108410842107c000001f0000007c000001f,0x3f8421042108413e4210842108210842084210801f0000007c000001f,0x3f8421042108414a529442108410842107c000001f0000007c000001f,0x3f8421042108418c631842108410842107c000001f0000007c000001f,0x3f842104211f4108421042108410842107c000001f0000007c000001f,0x3f842104211f4210842084210821084208421083e000000f80000001f,0x3f84210423e84108421042108410842107c000001f0000007c000001f,0x3f84210423e84210842084210821084208421083e00000007c000001f,0x3f842108421f8210842084210821084208421083e000000f80000001f,0x3f84210843f08210842084210821084208421083e00000007c000001f,0x3f84210f8000021084208421082108420843f083e000000f80000001f,0x3f84210f8000021084208421082108420fc210801f0000007c000001f,0x3f84210f80000210842084210821085f08421083e000000f8000003e0,0x3f84210f800002108420842108217c4208421083e00000007c000001f]

def r8p22 : Keys := .leaf [
0x3f84210f8000021084208421082f8842084210801f0000007c000001f,0x3f84210f80000210842084213e21084208421083e000000f8000003e0,0x3f84210f8000021084208427c821084208421083e000000f80000001f,0x3f84210f80000210842084f90821084208421083e00000007c000001f,0x3f84210f8000021084209f2108210842084210801f0000007c000001f,0x3f84210f800002108fa084210821084208421083e000000f80000001f,0x3f84210f80000211f42084210821084208421083e00000007c000001f,0x3f84210f801f0210842084210821084208421083e000000f80000001f,0x3f84210f83e00210842084210821084208421083e00000007c000001f,0x3f84210fa1084108421042108410842107c000001f0000007c000001f,0x3f843f0f80000210842084210821084208421083e000000f80000001f,0x3f843f0fc2108210842084210821084208421083e000000f80000001f,0x3f87e10f80000210842084210821084208421083e00000007c000001f,0x3f87e10fc2108210842084210821084208421083e00000007c000001f,0x3fc6318421084108421042108410842107c000001f0000007c000001f,0x3fc6318c6318c108421042108410842107c000001f0000007c000001f]

def r8p23 : Keys := .leaf [
0x3fc6318f80000108421042108410842107c000001f0000007c000001f,0x3fc6318fa1084108421042108410842107c000001f0000007c000001f]

def r8 : Keys := (.branch 0x3f00000842108211f42108421042108410842f84210841f00000003e0 (.branch 0x3f00000842108210842084213e217c4208421083e000000f8000003e0 (.branch 0x3f0000084210821084208421082108420843f083e000000f83e00001f (.branch 0x1f800006318c608421082108420843f083e000000f80000001f r8p0 (.branch 0x1fc21082108fa084210821084208421083e000000f80000001f r8p1 r8p2)) (.branch 0x3f000008421082108420842108210c4208421083e00000007c000001f r8p3 (.branch 0x3f0000084210821084208421082f88420fc210801f0000007c000001f r8p4 r8p5))) (.branch 0x3f0000084210821084209f21082108420843f083e000000f80000001f (.branch 0x3f0000084210821084208427c821085f10842104210841f0000007c00 r8p6 (.branch 0x3f00000842108210842084f90821085f10842104210841f00000003e0 r8p7 r8p8)) (.branch 0x3f0000084210821084209f213e210842084210801f0000007c000001f r8p9 (.branch 0x3f000008421082108420c6318c21085f08421083e000000f8000003e0 r8p10 r8p11)))) (.branch 0x3f00000c63f8c108421042108410842107c000001f0000007c000001f (.branch 0x3f00000843f082108420a5294a21084208421083e00000007c000001f (.branch 0x3f000008421f82108420842108217c4210842104210841f000000001f r8p12 (.branch 0x3f00000843f08210842084210821084208421083e000000008000001f r8p13 r8p14)) (.branch 0x3f00000c6318c10842104210841f8421084210801f0000007c000001f r8p15 (.branch 0x3f00000c6318c18c631842108410842107c000001f0000007c000001f r8p16 r8p17))) (.branch 0x3f842104210841084f9084210821084208421083e000000f80000001f (.branch 0x3f07c00f80000421084108421042108410842107e10840007c000001f r8p18 (.branch 0x3f42108c6318c108421042108410842107c000001f0000007c000001f r8p19 r8p20)) (.branch 0x3f84210f8000021084208421082f8842084210801f0000007c000001f r8p21 (.branch 0x3fc6318f80000108421042108410842107c000001f0000007c000001f r8p22 r8p23)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p0 : r8p0.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p1 : r8p1.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p2 : r8p2.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p3 : r8p3.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p4 : r8p4.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p5 : r8p5.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p6 : r8p6.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p7 : r8p7.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p8 : r8p8.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p9 : r8p9.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p10 : r8p10.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p11 : r8p11.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p12 : r8p12.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p13 : r8p13.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p14 : r8p14.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p15 : r8p15.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p16 : r8p16.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p17 : r8p17.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p18 : r8p18.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p19 : r8p19.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p20 : r8p20.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p21 : r8p21.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p22 : r8p22.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p23 : r8p23.all (checkQ 7 (dfs 6 (tableKill r6) 1)) = true := by decide +kernel

theorem badr8 : Rejects 8 r8 :=
  verifyTable 7 (dfs 6 (tableKill r6) 1) r8 (dfsSound 6 (tableKill r6) (tableSound 6 r6 badr6) 1) (by
    unfold r8
    simp only [allBranch, Bool.and_true, goodr8p0, goodr8p1, goodr8p2, goodr8p3, goodr8p4, goodr8p5, goodr8p6, goodr8p7, goodr8p8, goodr8p9, goodr8p10, goodr8p11, goodr8p12, goodr8p13, goodr8p14, goodr8p15, goodr8p16, goodr8p17, goodr8p18, goodr8p19, goodr8p20, goodr8p21, goodr8p22, goodr8p23])

def r10p0 : Keys := .leaf [
0x7e00001084210421084108421042108410842107c000001f0000007c000001f]

def r10 : Keys := r10p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr10p0 : r10p0.all (checkQ 9 (dfs 8 (tableKill r8) 1)) = true := by decide +kernel

theorem badr10 : Rejects 10 r10 :=
  verifyTable 9 (dfs 8 (tableKill r8) 1) r10 (dfsSound 8 (tableKill r8) (tableSound 8 r8 badr8) 1) (by
    unfold r10
    simp only [allBranch, Bool.and_true, goodr10p0])

theorem lower :
    ¬ RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (8127577 : ℕ).testBit (5*u.val+v.val)) 10 := by
  rintro ⟨C, mono, size, computes⟩
  obtain ⟨k,hk,build⟩ := representsBuild C mono computes
  obtain ⟨W,sub,j,jk,reach⟩ := buildReach build
  rw [allSources W sub (reachSeparates reach)] at reach
  have same : (decodeKey 3561963710422844759837215754900201654275826917327189221308241152903380729887).toFinset = sources.toFinset := by decide +kernel
  rw [← same] at reach
  exact badr10 3561963710422844759837215754900201654275826917327189221308241152903380729887 (by decide +kernel) j (jk.trans (hk.trans size)) reach

end PEqualNP.Outside.L_meta_10157

theorem PEqualNP.Outside.L_meta_10157 :
    ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (8127577 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_10157.lower
