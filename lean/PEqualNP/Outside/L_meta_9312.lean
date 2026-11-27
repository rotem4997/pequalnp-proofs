import Mathlib.Tactic
import PEqualNP.Defs

-- The search verifier follows the merged file L_meta_6339.lean of this repository, with the mask,
-- the symmetries and the certificate replaced; the certificate data are new.

namespace PEqualNP.Outside.L_meta_9312

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Mask := BitVec 25
def target : Mask := 3258290
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
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (3258290 : ℕ).testBit (5*u.val+v.val)) C) :
    (C.gates.foldl stage sources).getD C.output 0 = target := by
  apply BitVec.eq_of_getElem_eq
  intro i ilt
  rw [evalMask C mono ⟨i,ilt⟩]
  change C.eval (oneEach (⟨i / 5, by omega⟩ : Fin 5) (⟨i % 5, by omega⟩ : Fin 5)) = _
  rw [computes]
  have eq : 5*(i/5)+i % 5 = i := by omega
  change (3258290 : ℕ).testBit (5 * (i / 5) + i % 5) = _
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
    (computes : Represents (fun (u : Fin 5) (v : Fin 5) => (3258290 : ℕ).testBit (5*u.val+v.val)) C) :
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
  [(1,6), (5,0), (10,0), (15,0), (20,0), (5,6), (1,0), (7,6), (8,6), (4,0)]

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

def positive (i : Fin 13) : ℕ := ([1,4,5,7,8,9,10,12,13,15,16,20,21] : List ℕ)[i.val]'i.isLt
def negative (i : Fin 12) : ℕ := ([0,2,3,6,11,14,17,18,19,22,23,24] : List ℕ)[i.val]'i.isLt

def active (b : Bool) (w : BitVec 156) : BitVec 156 := if b then w else 0

theorem active_bit (b : Bool) (w : BitVec 156) (i : ℕ) :
    (active b w).getLsbD i = (b && w.getLsbD i) := by cases b <;> simp [active]

def spreadYes (x : Mask) : BitVec 156 :=
  active (x.getLsbD 1) 4095 |||
  active (x.getLsbD 4) 16773120 |||
  active (x.getLsbD 5) 68702699520 |||
  active (x.getLsbD 7) 281406257233920 |||
  active (x.getLsbD 8) 1152640029630136320 |||
  active (x.getLsbD 9) 4721213561365038366720 |||
  active (x.getLsbD 10) 19338090747351197150085120 |||
  active (x.getLsbD 12) 79208819701150503526748651520 |||
  active (x.getLsbD 13) 324439325495912462445562476625920 |||
  active (x.getLsbD 15) 1328903477231257446177023904259768320 |||
  active (x.getLsbD 16) 5443188642739230499541089911848011038720 |||
  active (x.getLsbD 20) 22295300680659888126120304278929453214597120 |||
  active (x.getLsbD 21) 91321551587982901764588766326495040366989803520

def spreadNo (x : Mask) : BitVec 156 :=
  active (!x.getLsbD 0) 22306191045953951743035482794815064402563073 |||
  active (!x.getLsbD 2) 44612382091907903486070965589630128805126146 |||
  active (!x.getLsbD 3) 89224764183815806972141931179260257610252292 |||
  active (!x.getLsbD 6) 178449528367631613944283862358520515220504584 |||
  active (!x.getLsbD 11) 356899056735263227888567724717041030441009168 |||
  active (!x.getLsbD 14) 713798113470526455777135449434082060882018336 |||
  active (!x.getLsbD 17) 1427596226941052911554270898868164121764036672 |||
  active (!x.getLsbD 18) 2855192453882105823108541797736328243528073344 |||
  active (!x.getLsbD 19) 5710384907764211646217083595472656487056146688 |||
  active (!x.getLsbD 22) 11420769815528423292434167190945312974112293376 |||
  active (!x.getLsbD 23) 22841539631056846584868334381890625948224586752 |||
  active (!x.getLsbD 24) 45683079262113693169736668763781251896449173504

def spread (x : Mask) : BitVec 156 := spreadYes x &&& spreadNo x

theorem active_get (b : Bool) (w : BitVec 156) (i : ℕ) (h : i < 156) :
    (active b w)[i] = (b && w[i]) := by
  cases b <;> simp [active]

theorem yes_bit (x : Mask) (i : Fin 13) (j : Fin 12) :
    (spreadYes x).getLsbD (12*i.val+j.val) = x.getLsbD (positive i) := by
  fin_cases i <;> fin_cases j <;>
    simp [spreadYes, positive, active_bit, active_get, BitVec.getLsbD_or]

theorem no_bit (x : Mask) (i : Fin 13) (j : Fin 12) :
    (spreadNo x).getLsbD (12*i.val+j.val) = !(x.getLsbD (negative j)) := by
  fin_cases i <;> fin_cases j <;>
    simp [spreadNo, negative, active_bit, active_get, BitVec.getLsbD_or]

def coverage : List Mask → BitVec 156 :=
  List.rec 0 (fun a _ cov => spread a ||| cov)

theorem coverageBit (W : List Mask) (i : Fin 13) (j : Fin 12) :
    (coverage W).getLsbD (12*i.val+j.val) = true ↔
      ∃ w ∈ W, w.getLsbD (positive i) = true ∧ w.getLsbD (negative j) = false := by
  induction W with
  | nil => simp [coverage]
  | cons a W ih =>
    change ((spread a ||| coverage W).getLsbD (12*i.val+j.val) = true) ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    rw [show (spread a).getLsbD (12*i.val+j.val) =
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

theorem listedPositions : ∀ (i : Fin 13) (j : Fin 12),
    positive i < 25 ∧ negative j < 25 ∧
      target.getLsbD (positive i) = true ∧ target.getLsbD (negative j) = false := by decide

theorem covered {W : List Mask} (sep : Separates W.toFinset) :
    coverage W = BitVec.allOnes 156 := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  let i : Fin 13 := ⟨k/12, by omega⟩
  let j : Fin 12 := ⟨k % 12, by omega⟩
  have h := listedPositions i j
  have p := h.2.2.1
  have n := h.2.2.2
  rw [BitVec.getLsbD_eq_getElem h.1] at p
  rw [BitVec.getLsbD_eq_getElem h.2.1] at n
  obtain ⟨w,wm,a,b⟩ := sep ⟨positive i,h.1⟩ ⟨negative j,h.2.1⟩ p n
  have hit := (coverageBit W i j).mpr ⟨w,List.mem_toFinset.mp wm,
    by rw [BitVec.getLsbD_eq_getElem h.1]; exact a,
    by rw [BitVec.getLsbD_eq_getElem h.2.1]; exact b⟩
  change (coverage W).getLsbD (12*(k/12)+k % 12) = true at hit
  rw [show 12*(k/12)+k % 12 = k by omega, BitVec.getLsbD_eq_getElem hk] at hit
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

def automPositions : List (List (Fin 25)) := [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0,1,3,2,4,5,6,8,7,9,10,11,13,12,14,15,16,18,17,19,20,21,23,22,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,20,21,22,23,24,15,16,17,18,19],[0,1,3,2,4,5,6,8,7,9,10,11,13,12,14,20,21,23,22,24,15,16,18,17,19]]

def coord (s : Fin 4) (i : Fin 25) : Fin 25 :=
  (automPositions[s.val]'s.isLt)[i.val]'(by fin_cases s <;> exact i.isLt)

theorem coordInj : ∀ (s : Fin 4) (i j : Fin 25), coord s i = coord s j → i = j := by
  decide +kernel

def remap (s : Fin 4) (x : Mask) : Mask :=
  (BitVec.ofBoolListLE (List.ofFn fun i => x[(coord s i).val])).cast (by simp)

theorem remapBit (s : Fin 4) (x : Mask) (i : Fin 25) :
    (remap s x)[i.val] = x[(coord s i).val] := by
  rw [← BitVec.getLsbD_eq_getElem i.isLt, remap, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]

theorem remapInj (s : Fin 4) : Function.Injective (remap s) := by
  intro x y e
  apply BitVec.eq_of_getElem_eq
  intro j hj
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp (coordInj s)) ⟨j,hj⟩
  have b := congrArg (fun a : Mask => a[i.val]) e
  simpa only [remapBit, hi] using b

theorem remapAct (s : Fin 4) (o : Bool) (a b : Mask) :
    remap s (act o a b) = act o (remap s a) (remap s b) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  change (remap s (act o a b))[(⟨j,hj⟩ : Fin 25).val] =
    (act o (remap s a) (remap s b))[(⟨j,hj⟩ : Fin 25).val]
  let i : Fin 25 := ⟨j,hj⟩
  rw [remapBit s (act o a b) i, act_bits o a b (coord s i), act_bits o _ _ i,
    remapBit s a i, remapBit s b i]

theorem remapFixed :
    ∀ s : Fin 4, remap s target = target ∧ remap s 0 = 0 ∧ remap s allBits = allBits := by
  decide +kernel

theorem mappedReach (s : Fin 4) {W : Finset Mask} {k : ℕ} (h : Reach W k) :
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

noncomputable def Keys.findAlias (T : Keys) (q : ℕ) : Bool :=
  Keys.rec (fun xs => xs.any (fun e => Nat.beq q (e / 4)))
    (fun b _ _ left right => Bool.rec right left (Nat.blt q b)) T

theorem searchedAlias {T : Keys} {test : ℕ → Bool} {q : ℕ}
    (pass : T.all test = true) (hit : T.findAlias q = true) :
    ∃ e, e / 4 = q ∧ test e = true := by
  induction T with
  | leaf xs =>
    obtain ⟨e,mem,found⟩ := List.any_eq_true.mp hit
    exact ⟨e,(Nat.eq_of_beq_eq_true found).symm,List.all_eq_true.mp pass e mem⟩
  | branch b l r il ir =>
    have both : l.all test = true ∧ r.all test = true := by
      simpa only [Keys.all, Keys.rec, Bool.and_eq_true] using pass
    cases cut : Nat.blt q b
    · exact ir both.2 (by simpa only [Keys.findAlias, Keys.rec, cut, Bool.rec] using hit)
    · exact il both.1 (by simpa only [Keys.findAlias, Keys.rec, cut, Bool.rec] using hit)

def remapFast (s : Fin 4) (x : Mask) : Mask :=
  match s.val with
  | 0 => (x &&& 33554431)
  | 1 => ((x &&& 8659208) >>> (1 : ℕ)) ||| (x &&& 20565619) ||| ((x &&& 4329604) <<< (1 : ℕ))
  | 2 => ((x &&& 32505856) >>> (5 : ℕ)) ||| (x &&& 32767) ||| ((x &&& 1015808) <<< (5 : ℕ))
  | _ => ((x &&& 8388608) >>> (6 : ℕ)) ||| ((x &&& 19922944) >>> (5 : ℕ)) ||| ((x &&& 4194304) >>> (4 : ℕ)) ||| ((x &&& 8456) >>> (1 : ℕ)) ||| (x &&& 20083) ||| ((x &&& 4228) <<< (1 : ℕ)) ||| ((x &&& 262144) <<< (4 : ℕ)) ||| ((x &&& 622592) <<< (5 : ℕ)) ||| ((x &&& 131072) <<< (6 : ℕ))

set_option maxHeartbeats 0 in
theorem remapFast_bit (s : Fin 4) (x : Mask) (j : Fin 25) :
    (remapFast s x).getLsbD j.val = x.getLsbD (coord s j).val := by
  fin_cases s <;> fin_cases j <;>
    simp [remapFast, coord, automPositions, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_and]

theorem remapFast_eq (s : Fin 4) (x : Mask) : remapFast s x = remap s x := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let i : Fin 25 := ⟨j,hj⟩
  calc
    (remapFast s x)[j] = (remapFast s x).getLsbD j := (BitVec.getLsbD_eq_getElem hj).symm
    _ = x.getLsbD (coord s i).val := remapFast_bit s x i
    _ = x[(coord s i).val] := BitVec.getLsbD_eq_getElem (coord s i).isLt
    _ = (remap s x)[j] := (remapBit s x i).symm

noncomputable def checkAlias (T : Keys) (e : ℕ) : Bool :=
  let W := decodeKey (e / 4)
  let V := sortW (W.map (remapFast (Fin.ofNat 4 e)))
  let q := key V
  T.find q && decodeKey q == V

def RejectsAlias (k : ℕ) (T : Keys) : Prop :=
  ∀ q, T.findAlias q = true → ∀ j ≤ k, ¬ Reach (decodeKey q).toFinset j

theorem verifyAliases (k : ℕ) (T U : Keys) (pr : Rejects k T)
    (check : U.all (checkAlias T) = true) : RejectsAlias k U := by
  intro q hit j le reach
  obtain ⟨e,eq,v⟩ := searchedAlias check hit
  simp only [checkAlias, eq, remapFast_eq, Bool.and_eq_true, beq_iff_eq] at v
  obtain ⟨found,eqMatch⟩ := v
  have h := mappedReach (Fin.ofNat 4 e) reach
  apply pr _ found j le
  rw [eqMatch, sortFinset, show remapFast (Fin.ofNat 4 e) = remap (Fin.ofNat 4 e) from funext (remapFast_eq _)]
  have eqSet : ((decodeKey q).map (remap (Fin.ofNat 4 e))).toFinset =
      (decodeKey q).toFinset.image (remap (Fin.ofNat 4 e)) := by
    ext a
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  exact eqSet.symm ▸ h

theorem rejectAliasNil : RejectsAlias 0 (.leaf []) := by intro q h; contradiction

abbrev Wire := ℕ × ℕ × ℕ

def natAct (o : Bool) (a b : ℕ) : ℕ := Bool.rec (Nat.land a b) (Nat.lor a b) o

def fuse (o : Bool) (a b : Wire) : Wire :=
  (natAct o a.1 b.1, natAct o a.2.1 b.2.1, natAct (!o) a.2.2 b.2.2)

def mark (x : ℕ) : Wire :=
  let m := BitVec.ofNat 25 x
  (x, (spreadYes m).toNat, (spreadNo m).toNat)

def coverWire (w : Wire) : ℕ := Nat.land w.2.1 w.2.2
def all64 : ℕ := 91343852333181432387730302044767688728495783935

def stripAB (a b : ℕ) : List Wire → List Wire × ℕ :=
  List.rec ([], 0) (fun w _ p =>
    Bool.rec (w :: p.1, Nat.lor (coverWire w) p.2) p
       (Nat.beq a w.1 || Nat.beq b w.1))

def includeWire (x : Wire) (keep : Bool) (xs : List Wire) : List Wire :=
  Bool.rec xs (x :: xs) keep

def coverExtra (x : Wire) (keep : Bool) (c : ℕ) : ℕ :=
  Bool.rec c (Nat.lor (coverWire x) c) keep

noncomputable def matchKey (T : Keys) (xs : List Wire) : Bool :=
  let sorted := sortW (xs.map (fun w => BitVec.ofNat 25 w.1))
  let q := key sorted
  T.findAlias q && (decodeKey q == sorted)

noncomputable def fastChild (k : ℕ) (T : Keys) (W : List Wire)
    (a b g : Wire) (strip : List Wire × ℕ) (ka kb : Bool) : Bool :=
  let c := Nat.lor (coverWire g) (coverExtra a ka (coverExtra b kb strip.2))
  Bool.rec false
    (let V := g :: includeWire a ka (includeWire b kb strip.1)
     if V.length > k+1 then false
     else if V.any (fun w => Nat.beq w.1 3258290) then true
     else if k == 0 then false
     else !(matchKey T V))
    (Nat.beq c all64)

noncomputable def fastAct (k : ℕ) (T : Keys) (W : List Wire)
    (a b : Wire) (strip : List Wire × ℕ) (o : Bool) : Bool :=
  let g := fuse o a b
  Bool.rec
    (fastChild k T W a b g strip false false ||
     fastChild k T W a b g strip false true ||
     fastChild k T W a b g strip true false ||
     fastChild k T W a b g strip true true)
    false (Nat.beq g.1 0 || Nat.beq g.1 33554431 || W.any (fun w => Nat.beq w.1 g.1))

noncomputable def fastPair (k : ℕ) (T : Keys) (W : List Wire) (a b : Wire) : Bool :=
  Bool.rec false
    (let strip := stripAB a.1 b.1 W
     fastAct k T W a b strip false || fastAct k T W a b strip true)
    (Nat.blt a.1 b.1)

noncomputable def checkFast (k : ℕ) (T : Keys) (q : ℕ) : Bool :=
  let L := decodeKey q
  let W := L.map (fun w => mark w.toNat)
  decide L.Nodup && !(W.any (fun w => Nat.beq w.1 3258290) ||
    W.any (fun a => W.any (fastPair k T W a)))


def marked (m : Mask) : Wire := mark m.toNat

theorem marked_form (m : Mask) :
    marked m = (m.toNat, (spreadYes m).toNat, (spreadNo m).toNat) := by
  simp [marked, mark]

theorem bit64Matrix (k : ℕ) (hk : k < 156) :
    ∃ (i : Fin 13) (j : Fin 12), 12*i.val+j.val = k :=
  ⟨⟨k/12, by omega⟩, ⟨k % 12, by omega⟩, by change 12*(k/12)+k % 12 = k; omega⟩

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
    ((L.map marked).any (fun w => Nat.beq w.1 3258290)) = true ↔ target ∈ L := by
  simp only [List.any_eq_true, List.mem_map, target, markedNat]
  constructor
  · rintro ⟨w, ⟨m,hm,rfl⟩,he⟩
    exact (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true he :
      m.toNat = (3258290 : Mask).toNat)) ▸ hm
  · intro h
    exact ⟨marked 3258290,⟨3258290,h,rfl⟩,rfl⟩

theorem match_rejects (k : ℕ) (T : Keys) (pr : RejectsAlias k T) (L : List Mask)
    (j : ℕ) (le : j ≤ k) (reach : Reach L.toFinset j) :
    matchKey T (L.map marked) = false := by
  apply Bool.eq_false_iff.mpr
  have m : ((L.map marked).map (fun w => BitVec.ofNat 25 w.1)) = L := by
    clear reach
    induction L with
    | nil => rfl
    | cons a L ih => simp only [List.map_cons, naturalMask, ih]
  unfold matchKey
  simp only [m, Bool.and_eq_true, beq_iff_eq]
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨found,eq⟩ := h
  apply pr _ found j le
  rwa [eq, sortFinset]

theorem fastChild_true {k : ℕ} {T : Keys} (pr : RejectsAlias k T)
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
  have lacks : ((L.map marked).any (fun w => Nat.beq w.1 3258290)) = false :=
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
    match_rejects k T pr L j le reach, Bool.not_false]


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

theorem fastPair_true {k : ℕ} {T : Keys} (pr : RejectsAlias k T)
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

theorem verifyFast (k : ℕ) (T U : Keys) (ih : RejectsAlias k T)
    (ok : U.all (checkFast k T) = true) : Rejects (k+1) U := by
  intro q hit j le reach
  let W := decodeKey q
  have passed := searched ok hit
  let t0 := (W.map marked).any (fun w => Nat.beq w.1 3258290)
  let t1 := (W.map marked).any (fun a => (W.map marked).any (fastPair k T (W.map marked) a))
  have record : W.Nodup ∧ (t0 || t1) = false := by
    change (decide W.Nodup && !(t0 || t1)) = true at passed
    simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] using passed
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



theorem allBranch (b : ℕ) (l r : Keys) (f : ℕ → Bool) :
    (Keys.branch b l r).all f = (l.all f && r.all f) := rfl


def a0 : Keys := .leaf []

def r1p0 : Keys := .leaf [
]

def r1 : Keys := r1p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr1p0 : r1p0.all (checkFast 0 a0) = true := by decide +kernel

theorem badR1 : Rejects 1 r1 :=
  verifyFast 0 a0 r1 rejectAliasNil (by
    unfold r1
    simp only [allBranch, Bool.and_true, goodr1p0])

def a1p0 : Keys := .leaf [
]

def a1 : Keys := a1p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda1p0 : a1p0.all (checkAlias r1) = true := by decide +kernel

theorem badA1 : RejectsAlias 1 a1 :=
  verifyAliases 1 r1 a1 badR1 (by
    unfold a1
    simp only [allBranch, Bool.and_true, gooda1p0])

def r2p0 : Keys := .leaf [
]

def r2 : Keys := r2p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr2p0 : r2p0.all (checkFast 1 a1) = true := by decide +kernel

theorem badR2 : Rejects 2 r2 :=
  verifyFast 1 a1 r2 badA1 (by
    unfold r2
    simp only [allBranch, Bool.and_true, goodr2p0])

def a2p0 : Keys := .leaf [
]

def a2 : Keys := a2p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda2p0 : a2p0.all (checkAlias r2) = true := by decide +kernel

theorem badA2 : RejectsAlias 2 a2 :=
  verifyAliases 2 r2 a2 badR2 (by
    unfold a2
    simp only [allBranch, Bool.and_true, gooda2p0])

def r3p0 : Keys := .leaf [
]

def r3 : Keys := r3p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr3p0 : r3p0.all (checkFast 2 a2) = true := by decide +kernel

theorem badR3 : Rejects 3 r3 :=
  verifyFast 2 a2 r3 badA2 (by
    unfold r3
    simp only [allBranch, Bool.and_true, goodr3p0])

def a3p0 : Keys := .leaf [
]

def a3 : Keys := a3p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda3p0 : a3p0.all (checkAlias r3) = true := by decide +kernel

theorem badA3 : RejectsAlias 3 a3 :=
  verifyAliases 3 r3 a3 badR3 (by
    unfold a3
    simp only [allBranch, Bool.and_true, gooda3p0])

def r4p0 : Keys := .leaf [
0x3ffc2104a529f94a52fc4217c4007c00,0x3ffc2106318c60842f8821087e007c00,0x3ffc2106318c60842f8821087e007fe0,0x3ffc2106318c6085f1084217c410843f,0x3ffc2106318c6085ff884217c410843f,0x3ffc2106318cf8842f8821087e007c00,0x3ffc21067d8c60842f8821087e007c00,0x3ffc2106b5ad68842f8821087e007c00,0x3ffc2106b5adf8842f8821087e007c00,0x3ffc210843f08318c6304217c410843f,0x3ffc210843f08318c67c4217c4108421,0x3ffc210ffd8c60842f8821087e007c00,0x3ffc210ffd8c6085f10821087e0003e0]

def r4 : Keys := r4p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr4p0 : r4p0.all (checkFast 3 a3) = true := by decide +kernel

theorem badR4 : Rejects 4 r4 :=
  verifyFast 3 a3 r4 badA3 (by
    unfold r4
    simp only [allBranch, Bool.and_true, goodr4p0])

def a4p0 : Keys := .leaf [
0xfff0841294a7e5294bf1085f1001f000,0xfff08418c6318210be208421f801f000,0xfff08418c6318210be208421f801ff80,0xfff08418c6318217c421085f104210fc,0xfff08418c6318217fe21085f104210fc,0xfff08418c633e210be208421f801f000,0xfff08419f6318210be208421f801f000,0xfff0841ad6b5a210be208421f801f000,0xfff0841ad6b7e210be208421f801f000,0xfff084210fc20c6318c1085f104210fc,0xfff084210fc20c6319f1085f10421084,0xfff0843ec6318210be208421f801f002,0xfff0843ff6318210be208421f801f000,0xfff0843ff6318217c4208421f8000f80]

def a4 : Keys := a4p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda4p0 : a4p0.all (checkAlias r4) = true := by decide +kernel

theorem badA4 : RejectsAlias 4 a4 :=
  verifyAliases 4 r4 a4 badR4 (by
    unfold a4
    simp only [allBranch, Bool.and_true, gooda4p0])

def r5p0 : Keys := .leaf [
0x3ffc2106318c60842f8821087e007c00,0x7f084208fa10827c8420842f8821087e007c00,0x7f0842094a52927c8420842f8821087e007c00,0x7f0842094a53f294a5f8842f881f0000007c00,0x7f08420c6318c1085f104210fc1f0000007fe0,0x7f08420c6318c10be210842f8821087e0f8000,0x7f08420c6318c10bff10842f8821087e0f8000,0x7f08420c6319f1085f104210fc1f0000007c00,0x7f08420cfb18c1085f1042108400f80000001f,0x7f08420cfb18c1085f1042108400ffc000001f,0x7f08420cfb18c1085f104210fc1f0000007c00,0x7f08420cfb18c1085f104210fc210842007c00,0x7f08420cfb18c10be210842f8821084200001f,0x7f08420cfb18c10bff10842f8821084200001f,0x7f08420d6b5ad1085f104210fc1f0000007c00,0x7f08420d6b5bf1085f104210fc1f0000007c00,0x7f08421087e106318c60842f8821087e0f8000,0x7f08421087e106318cf8842f882108420f8000,0x7f084210fc2106318c60842f8821087e007c00,0x7f084210fc2106318cf8842f88210842007c00,0x7f08421f6318c1085f104210fc1f0000007c00,0x7f08421f6318c10be2104210fc1f00000003e0,0x7ff00010842104a529f94a52944217c4007c00,0x7ff00010842104a529f94a529442f8840003e0,0x7ff00010842104a529f94a52fc4217c4007c00,0x7ff00010842104a529f94a52fc42f8840003e0,0x7ff00010842106318c60842f8821087e007fe0,0x7ff00010842106318c6085f1084217c410843f,0x7ff00010842106318c6085ff8821087e0003e0,0x7ff00010842106318c6085ff884217c410843f,0x7ff00010842106318cf8842f88210842007c00,0x7ff00010842106318cf8842f88210842007fe0,0x7ff00010842106318cf8842f8821087e007c00,0x7ff00010842106318cf885f1082108420003e0,0x7ff00010842106318cf885f10821087e0003e0,0x7ff00010842106318cf885f1084217c4108421,0x7ff00010842106318cf885ff882108420003e0,0x7ff00010842106318cf885ff884217c4108421,0x7ff000108421067d8c60842f8821087e007c00,0x7ff000108421067d8c6085f10821087e0003e0,0x7ff00010842106b5ad68842f8821087e007c00,0x7ff00010842106b5ad6885f10821087e0003e0,0x7ff00010842106b5adf8842f88210842007c00,0x7ff00010842106b5adf8842f8821087e007c00,0x7ff00010842106b5adf885f1082108420003e0,0x7ff00010842106b5adf885f10821087e0003e0,0x7ff0001087e104a529f94a52944210840003e0,0x7ff0001087e104a529f94a52fc4210840003e0]

def r5p1 : Keys := .leaf [
0x7ff0001087e106318c60842f8821087e0003e0,0x7ff0001087e106318c6085f10821087e0003e0,0x7ff0001087e106318cf88421082108420003e0,0x7ff0001087e106318cf884210821087e0003e0,0x7ff0001087e106318cf8842f882108420003e0,0x7ff0001087e106318cf885f1082108420003e0,0x7ff0001087e106b5ad6884210821087e0003e0,0x7ff0001087e106b5adf88421082108420003e0,0x7ff0001087e106b5adf884210821087e0003e0,0x7ff0001087e10842108318c6304217c410843f,0x7ff0001087e10842108318c67c4217c4108421,0x7ff00010fc2106318c60842f8821087e007c00,0x7ff00010fc2106318c6085f10821087e0003e0,0x7ff21090842106318cf8842f88210842007c00,0x7ff21090842106318cf885f1082108420003e0,0x7ff2109087e106318cf88421082108420003e0,0x7ff421108421021084f8842f88210842007c00,0x7ff421108421021084f8842f88210842007fe0,0x7ff421108421021084f885f1082108420003e0,0x7ff421108421021084f885f1084217c4108421,0x7ff421108421021084f885ff882108420003e0,0x7ff421108421021084f885ff884217c4108421,0x7ff4211084210294a528842f8821087e007c00,0x7ff4211084210294a52885f10821087e0003e0,0x7ff4211084210294a5f8842f88210842007c00,0x7ff4211084210294a5f885f1082108420003e0,0x7ff4211087e1021084f885f1082108420003e0,0x7ff4211ff90848421080842f8821087e007c00,0x7ff4211ff9084842108085f10821087e0003e0,0x7ff63190842101085f1042108400f80000001f,0x7ff63190842101085f1042108400ffc000001f,0x7ff63190842101085f104210fc210842007c00,0x7ff631908421010be2104210840007c000001f,0x7ff631908421010be2104210fc2108420003e0,0x7ff631908421010be210842f8821084200001f,0x7ff631908421010bff104210840007c000001f,0x7ff631908421010bff10842f8821084200001f,0x7ff631908421021084f8842f88210842007c00,0x7ff631908421021084f885f1082108420003e0,0x7ff63190842106318cf8842f88210842007c00,0x7ff63190842106318cf885f1082108420003e0,0x7ff6319087e1010be2104210840007c000001f,0x7ff6319087e106318cf88421082108420003e0,0x7ff63190fc2101085f1042108400f80000001f,0x7ff63190fc21010be2104210840007c000001f,0x7ff6319ff80008421080842f8821087e007c00,0x7ff6319ff8000842108085f10821087e0003e0,0x7ff84208421082108420842f8821087e007c00]

def r5p2 : Keys := .leaf [
0x7ff84208421082108420842f8821087e007fe0,0x7ff8420842108210842085f1084217c410843f,0x7ff8420842108210842085ff884217c410843f,0x7ff842084211f2108420842f8821087e007c00,0x7ff842084211f21084f8842f88210842007c00,0x7ff84208fa1082108420842f8821087e007c00,0x7ff842094a5292108420842f8821087e007c00,0x7ff842094a529294a528842f8800f80000001f,0x7ff842094a53f2108420842f8821087e007c00,0x7ff842094a53f294a5f884210800f8000003e0,0x7ff8420c6318c10842104210fc00f8000003e0,0x7ff8420c6318c10842104210fc00ffc00003e0,0x7ff8420c6318c1085f1042108400f80000001f,0x7ff8420c6318c1085f1042108400ffc000001f,0x7ff8420c6318c1085f104210fc00f80000001f,0x7ff8420c6318c1085f104210fc00f8000003e0,0x7ff8420c6318c1085f104210fc1f0000007c00,0x7ff8420c6318c1085f104210fc210842007c00,0x7ff8420c6318c1085f1084210821087e007c00,0x7ff8420c6318c10be21084210821087e0003e0,0x7ff8420c6318c10be210842f8821084200001f,0x7ff8420c6318c10bff10842f8821084200001f,0x7ff8420c6318c2108420842f8821087e007c00,0x7ff8420c6319f10842104210fc00f8000003e0,0x7ff8420c6319f1085f1042108400f80000001f,0x7ff8420cfb18c10842104210fc00f8000003e0,0x7ff8420cfb18c1085f1042108400f80000001f,0x7ff8420d6b5ad10842104210fc00f8000003e0,0x7ff8420d6b5ad1085f1042108400f80000001f,0x7ff8420d6b5bf10842104210fc00f8000003e0,0x7ff84210842106318c60842f8821087e007c00,0x7ff84210842106318cf8842f88210842007c00,0x7ff8421087e1042108410842104217c410843f,0x7ff8421087e1042108f90842104217c4108421,0x7ff8421087e106318c6084210821087e0003e0,0x7ff8421087e106318c60842f8821084200001f,0x7ff8421087e106318cf88421082108420003e0,0x7ff84210fc2106318c60842f8821087e007c00,0x7ff8421ff80006318c60842f8821087e007c00,0x7ff8421ff80006318c6085f10821087e0003e0,0x7ff8421ffa1082108420842f8821087e007c00,0x7ff8421ffa108210842085f10821087e0003e0,0x7ff8421ffb18c10842104210fc00f8000003e0,0x7ff8421ffb18c1085f1042108400f80000001f,0x7ff8421ffb18c10be2104210840007c000001f]

def r5 : Keys := (.branch 0x7ff0001087e106318c60842f8821087e0003e0 r5p0 (.branch 0x7ff84208421082108420842f8821087e007fe0 r5p1 r5p2))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr5p0 : r5p0.all (checkFast 4 a4) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr5p1 : r5p1.all (checkFast 4 a4) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr5p2 : r5p2.all (checkFast 4 a4) = true := by decide +kernel

theorem badR5 : Rejects 5 r5 :=
  verifyFast 4 a4 r5 badA4 (by
    unfold r5
    simp only [allBranch, Bool.and_true, goodr5p0, goodr5p1, goodr5p2])

def a5p0 : Keys := .leaf [
0xfff08418c6318210be208421f801f000,0x1f8000043f0841294a7e5294bf1085f1001f002,0x1f8000043f08418c6318210be208421f801ff82,0x1f8000043f08418c6318217c421085f104210fe,0x1f8000043f08418c6318217fe21085f104210fe,0x1f8000043f08418c633e210be208421f801f002,0x1f8000043f08419f6318210be208421f801f002,0x1f8000043f08419f6318217c4208421f8000f82,0x1f8000043f0841ad6b5a210be208421f801f002,0x1f8000043f0841ad6b7e210be208421f801f002,0x1f8000043f084210fc20c6318c1085f104210fe,0x1f8000043f084210fc20c6319f1085f10421086,0x1fa108443f0840a5294a210be208421f801f003,0x1fa10847c842121f8420210be208421f801f002,0x1fb18c643f08404217c4108421003e00000007e,0x1fb18c643f08404217c4108421003ff0000007e,0x1fb18c643f08404217c410843f084210801f002,0x1fb18c643f084042f884210be2084210800007e,0x1fb18c643f084042ffc4210be2084210800007e,0x1fc210823e84209f2108210be208421f801f000,0x1fc210823e8420a5294a210be208421f801f001,0x1fc210825294a49f2108210be208421f801f000,0x1fc210825294fca5297e210be207c000001f000,0x1fc2108318c6304217c410843f07c000001ff80,0x1fc2108318c63042f884210be208421f83e0000,0x1fc2108318c63042ffc4210be208421f83e0000,0x1fc2108318c67c4217c410843f07c000001f000,0x1fc210833ec6304217c4108421003e00000007c,0x1fc210833ec6304217c4108421003ff0000007c,0x1fc210833ec6304217c410843f07c000001f000,0x1fc210833ec6304217c410843f084210801f000,0x1fc210833ec63042f884210be2084210800007c,0x1fc210833ec63042ffc4210be2084210800007c,0x1fc210835ad6b44217c410843f07c000001f000,0x1fc210835ad6fc4217c410843f07c000001f000,0x1fc2108421f8418c6318210be208421f83e0000,0x1fc2108421f8418c633e210be208421083e0000,0x1fc210843f08418c6318210be208421f801f000,0x1fc210843f08418c633e210be2084210801f000,0x1fc21087d8c6304217c410843f07c000001f000,0x1fc21087d8c63042f88410843f07c0000000f80,0x1ffc0004210841294a525294bf1085f1001f001,0x1ffc0004210841294a525294bf10be210000f81,0x1ffc0004210841294a7e5294a51085f1001f000,0x1ffc0004210841294a7e5294a510be210000f80,0x1ffc0004210841294a7e5294bf1085f1001f000,0x1ffc0004210841294a7e5294bf10be210000f80,0x1ffc00042108418c6318210be208421f801ff80]

def a5p1 : Keys := .leaf [
0x1ffc00042108418c6318217c421085f104210fc,0x1ffc00042108418c6318217fe208421f8000f80,0x1ffc00042108418c6318217fe21085f104210fc,0x1ffc00042108418c633e210be2084210801f000,0x1ffc00042108418c633e210be2084210801ff80,0x1ffc00042108418c633e210be208421f801f000,0x1ffc00042108418c633e217c420842108000f80,0x1ffc00042108418c633e217c4208421f8000f80,0x1ffc00042108418c633e217c421085f10421084,0x1ffc00042108418c633e217fe20842108000f80,0x1ffc00042108418c633e217fe21085f10421084,0x1ffc00042108419f6318210be208421f801f000,0x1ffc00042108419f6318217c4208421f8000f80,0x1ffc0004210841ad6b5a210be208421f801f000,0x1ffc0004210841ad6b5a217c4208421f8000f80,0x1ffc0004210841ad6b7e210be2084210801f000,0x1ffc0004210841ad6b7e210be208421f801f000,0x1ffc0004210841ad6b7e217c420842108000f80,0x1ffc0004210841ad6b7e217c4208421f8000f80,0x1ffc000421f841294a525294bf1084210000f81,0x1ffc000421f841294a7e5294a51084210000f80,0x1ffc000421f841294a7e5294bf1084210000f80,0x1ffc000421f8418c6318210be208421f8000f80,0x1ffc000421f8418c6318217c4208421f8000f80,0x1ffc000421f8418c633e2108420842108000f80,0x1ffc000421f8418c633e21084208421f8000f80,0x1ffc000421f8418c633e210be20842108000f80,0x1ffc000421f8418c633e217c420842108000f80,0x1ffc000421f841ad6b5a21084208421f8000f80,0x1ffc000421f841ad6b7e2108420842108000f80,0x1ffc000421f841ad6b7e21084208421f8000f80,0x1ffc000421f842108420c6318c1085f104210fc,0x1ffc000421f842108420c6319f1085f10421084,0x1ffc00043f08418c6318210be208421f801f000,0x1ffc00043f08418c6318217c4208421f8000f80,0x1ffc842421084108423e210be2084210801ff81,0x1ffc842421084108423e217c421085f10421085,0x1ffc842421084108423e217fe20842108000f81,0x1ffc842421084108423e217fe21085f10421085,0x1ffc8424210841294a52210be208421f801f001,0x1ffc8424210841294a52217c4208421f8000f81,0x1ffc8424210841294a7e210be2084210801f001,0x1ffc8424210841294a7e217c420842108000f81,0x1ffc84242108418c633e210be2084210801f000,0x1ffc84242108418c633e217c420842108000f80,0x1ffc842421f84108423e217c420842108000f81,0x1ffc842421f8418c633e2108420842108000f80,0x1ffd084421084084213e210be2084210801f000]

def a5p2 : Keys := .leaf [
0x1ffd084421084084213e210be2084210801ff80,0x1ffd084421084084213e217c420842108000f80,0x1ffd084421084084213e217c421085f10421084,0x1ffd084421084084213e217fe20842108000f80,0x1ffd084421084084213e217fe21085f10421084,0x1ffd0844210840a5294a210be208421f801f000,0x1ffd0844210840a5294a217c4208421f8000f80,0x1ffd0844210840a5297e210be2084210801f000,0x1ffd0844210840a5297e217c420842108000f80,0x1ffd08442108418c633e210be2084210801f001,0x1ffd08442108418c633e217c420842108000f81,0x1ffd084421f84084213e217c420842108000f80,0x1ffd084421f8418c633e2108420842108000f81,0x1ffd0847fe4212108420210be208421f801f000,0x1ffd0847fe4212108420217c4208421f8000f80,0x1ffd8c642108404217c4108421003e00000007c,0x1ffd8c642108404217c4108421003ff0000007c,0x1ffd8c642108404217c410843f084210801f000,0x1ffd8c6421084042f8841084210001f0000007c,0x1ffd8c6421084042f88410843f0842108000f80,0x1ffd8c6421084042f884210be2084210800007c,0x1ffd8c6421084042ffc41084210001f0000007c,0x1ffd8c6421084042ffc4210be2084210800007c,0x1ffd8c6421084084213e210be2084210801f000,0x1ffd8c6421084084213e217c420842108000f80,0x1ffd8c6421084108423e210be2084210801f001,0x1ffd8c6421084108423e217c420842108000f81,0x1ffd8c642108418c633e210be2084210801f000,0x1ffd8c642108418c633e217c420842108000f80,0x1ffd8c6421f84042f8841084210001f0000007c,0x1ffd8c6421f8418c633e2108420842108000f80,0x1ffd8c643f08404217c4108421003e00000007c,0x1ffd8c643f084042f8841084210001f0000007c,0x1ffd8c67e108404217c4108421003e00000007e,0x1ffd8c67e1084042f8841084210001f0000007e,0x1ffd8c67fe0002108420210be208421f801f000,0x1ffd8c67fe0002108420217c4208421f8000f80,0x1ffe1082108420842108210be208421f801f000,0x1ffe1082108420842108210be208421f801ff80,0x1ffe1082108420842108217c421085f104210fc,0x1ffe1082108420842108217fe21085f104210fc,0x1ffe108210842084213e210be208421f801f001,0x1ffe10821084209f2108210be208421f801f001,0x1ffe1082108420a5294a210be208421f801f001,0x1ffe1082108420a5297e210be208421f801f001,0x1ffe108210847c842108210be208421f801f000,0x1ffe108210847c84213e210be2084210801f000,0x1ffe10823e8420842108210be208421f801f000]

def a5p3 : Keys := .leaf [
0x1ffe10825294a4842108210be208421f801f000,0x1ffe10825294a4a5294a210be2003e00000007c,0x1ffe10825294fc842108210be208421f801f000,0x1ffe10825294fca5297e210842003e000000f80,0x1ffe108318c63042108410843f003e000000f80,0x1ffe108318c63042108410843f003ff00000f80,0x1ffe108318c6304217c4108421003e00000007c,0x1ffe108318c6304217c4108421003ff0000007c,0x1ffe108318c6304217c410843f003e00000007c,0x1ffe108318c6304217c410843f003e000000f80,0x1ffe108318c6304217c410843f07c000001f000,0x1ffe108318c6304217c410843f084210801f000,0x1ffe108318c6304217c421084208421f801f000,0x1ffe108318c63042f88421084208421f8000f80,0x1ffe108318c63042f884210be2084210800007c,0x1ffe108318c63042ffc4210be2084210800007c,0x1ffe108318c630842108210be208421f801f000,0x1ffe108318c631084210210be208421f801f001,0x1ffe108318c67c42108410843f003e000000f80,0x1ffe108318c67c4217c4108421003e00000007c,0x1ffe10833ec63042108410843f003e000000f80,0x1ffe10833ec6304217c4108421003e00000007c,0x1ffe10835ad6b442108410843f003e000000f80,0x1ffe10835ad6b44217c4108421003e00000007c,0x1ffe10835ad6fc42108410843f003e000000f80,0x1ffe10842108418c6318210be208421f801f000,0x1ffe10842108418c633e210be2084210801f000,0x1ffe108421f8410842104210841085f104210fc,0x1ffe108421f84108421042109f1085f10421085,0x1ffe108421f84108423e4210841085f10421084,0x1ffe108421f8418c631821084208421f8000f80,0x1ffe108421f8418c6318210be2084210800007c,0x1ffe108421f8418c633e2108420842108000f80,0x1ffe10843f08418c6318210be208421f801f000,0x1ffe1087d08420842108210be208421f801f002,0x1ffe1087d8c63042108410843f003e000000f82,0x1ffe1087d8c6304217c4108421003e00000007e,0x1ffe1087e108418c6318210be208421f801f002,0x1ffe1087fe00018c6318210be208421f801f000,0x1ffe1087fe00018c6318217c4208421f8000f80,0x1ffe1087fe4211084210210be208421f801f001,0x1ffe1087fe4211084210217c4208421f8000f81,0x1ffe1087fe8420842108210be208421f801f000,0x1ffe1087fe8420842108217c4208421f8000f80,0x1ffe1087fec63042108410843f003e000000f80,0x1ffe1087fec6304217c4108421003e00000007c,0x1ffe1087fec63042f8841084210001f0000007c]

def a5 : Keys := (.branch 0x7ff421108421021084f8842f88210842007fe0 (.branch 0x7ff00010842106318c6085f1084217c410843f a5p0 a5p1) (.branch 0x7ff842094a5292108420842f8821087e007c00 a5p2 a5p3))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda5p0 : a5p0.all (checkAlias r5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda5p1 : a5p1.all (checkAlias r5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda5p2 : a5p2.all (checkAlias r5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda5p3 : a5p3.all (checkAlias r5) = true := by decide +kernel

theorem badA5 : RejectsAlias 5 a5 :=
  verifyAliases 5 r5 a5 badR5 (by
    unfold a5
    simp only [allBranch, Bool.and_true, gooda5p0, gooda5p1, gooda5p2, gooda5p3])

def r6p0 : Keys := .leaf [
0x7f08420c6318c1085f104210fc1f0000007c00,0x7f08420cfb18c1085f1042108400f80000001f,0x7ff00010842106318c60842f8821087e007c00,0x7ff00010842106318c6085f10821087e0003e0,0x7ff00010842106318cf8842f88210842007c00,0x7ff00010842106318cf885f1082108420003e0,0x7ff0001087e106318c6084210821087e0003e0,0x7ff0001087e106318cf88421082108420003e0,0x7ff421108421021084f8842f88210842007c00,0x7ff421108421021084f885f1082108420003e0,0x7ff63190842101085f1042108400f80000001f,0x7ff631908421010be2104210840007c000001f,0x7ff84208421082108420842f8821087e007c00,0x7ff8420c6318c10842104210fc00f8000003e0,0x7ff8420c6318c1085f1042108400f80000001f,0xfc0000210842094a53f294a528842f881f0000007c00,0xfc0000210842094a53f294a52885f1081f00000003e0,0xfc0000210842094a53f294a5f8842f881f0000007c00,0xfc0000210842094a53f294a5f885f1081f00000003e0,0xfc00002108420c6318c1085f104210fc1f0000007fe0,0xfc00002108420c6318c10be210842f8821087e0f8000,0xfc00002108420c6318c10bff104210fc1f00000003e0,0xfc00002108420c6318c10bff10842f8821087e0f8000,0xfc00002108420c6319f1085f104210841f0000007c00,0xfc00002108420c6319f1085f104210841f0000007fe0,0xfc00002108420c6319f1085f104210fc1f0000007c00,0xfc00002108420c6319f10be2104210841f00000003e0,0xfc00002108420c6319f10be2104210fc1f00000003e0,0xfc00002108420c6319f10be210842f882108420f8000,0xfc00002108420c6319f10bff104210841f00000003e0,0xfc00002108420c6319f10bff10842f882108420f8000,0xfc00002108420cfb18c1085f104210fc1f0000007c00,0xfc00002108420cfb18c10be2104210fc1f00000003e0,0xfc00002108420d6b5ad1085f104210fc1f0000007c00,0xfc00002108420d6b5ad10be2104210fc1f00000003e0,0xfc00002108420d6b5bf1085f104210841f0000007c00,0xfc00002108420d6b5bf1085f104210fc1f0000007c00,0xfc00002108420d6b5bf10be2104210841f00000003e0,0xfc00002108420d6b5bf10be2104210fc1f00000003e0,0xfc0000210fc2094a53f294a5288421081f00000003e0,0xfc0000210fc2094a53f294a5f88421081f00000003e0,0xfc0000210fc20c6318c1085f104210fc1f00000003e0,0xfc0000210fc20c6318c10be2104210fc1f00000003e0,0xfc0000210fc20c6319f10842104210841f00000003e0,0xfc0000210fc20c6319f10842104210fc1f00000003e0,0xfc0000210fc20c6319f1085f104210841f00000003e0,0xfc0000210fc20c6319f10be2104210841f00000003e0,0xfc0000210fc20d6b5ad10842104210fc1f00000003e0]

def r6p1 : Keys := .leaf [
0xfc0000210fc20d6b5bf10842104210841f00000003e0,0xfc0000210fc20d6b5bf10842104210fc1f00000003e0,0xfc0000210fc210842106318c60842f8821087e0f8000,0xfc0000210fc210842106318cf8842f882108420f8000,0xfc000021f8420c6318c1085f104210fc1f0000007c00,0xfc000021f8420c6318c10be2104210fc1f00000003e0,0xfc84212108420c6319f1085f104210841f0000007c00,0xfc84212108420c6319f10be2104210841f00000003e0,0xfc8421210fc20c6319f10842104210841f00000003e0,0xfd0842210842042109f1085f104210841f0000007fe0,0xfd0842210842042109f10be210842f882108420f8000,0xfd0842210842042109f10bff104210841f00000003e0,0xfd0842210842042109f10bff10842f882108420f8000,0xfd084221084204f90841085f1042108400ffc000001f,0xfd084221084204f90841085f104210fc210842007c00,0xfd084221084204f908410be2104210fc2108420003e0,0xfd084221084204f908410be210842f8821084200001f,0xfd084221084204f908410bff104210840007c000001f,0xfd084221084204f908410bff10842f8821084200001f,0xfd084221084204f908421084f8842f88210842007c00,0xfd084221084204f908421084f885f1082108420003e0,0xfd084221084205294a51085f104210fc1f0000007c00,0xfd084221084205294a510be2104210fc1f00000003e0,0xfd084221084205294bf1085f104210841f0000007c00,0xfd084221084205294bf10be2104210841f00000003e0,0xfd084221084208fa10821084f8842f88210842007c00,0xfd084221084208fa10821084f885f1082108420003e0,0xfd0842210fc2042109f10be2104210841f00000003e0,0xfd0842210fc204f908410be2104210840007c000001f,0xfd0842210fc208fa10821084f88421082108420003e0,0xfd084221f84204f90841085f1042108400f80000001f,0xfd084221f84204f908410be2104210840007c000001f,0xfd08423e421090842101085f104210fc1f0000007c00,0xfd08423e4210908421010be2104210fc1f00000003e0,0xfd8c632108420210be208421083e000000f80000001f,0xfd8c632108420210be208421083e000000ffc000001f,0xfd8c632108420210be208421f84210841f0000007c00,0xfd8c632108420217c4208421083e00000007c000001f,0xfd8c632108420217c4208421f84210841f00000003e0,0xfd8c632108420217c421085f104210841f000000001f,0xfd8c632108420217fe208421083e00000007c000001f,0xfd8c632108420217fe21085f104210841f000000001f,0xfd8c63210842042109f1085f104210841f0000007c00,0xfd8c63210842042109f10be2104210841f00000003e0,0xfd8c6321084204f90841085f1042108400f80000001f,0xfd8c6321084204f908410be2104210840007c000001f,0xfd8c632108420c6319f1085f104210841f0000007c00,0xfd8c632108420c6319f10be2104210841f00000003e0]

def r6p2 : Keys := .leaf [
0xfd8c632108420cfb18c1085f1042108400f80000001f,0xfd8c632108420cfb18c10be2104210840007c000001f,0xfd8c63210fc20217c4208421083e00000007c000001f,0xfd8c63210fc20c6319f10842104210841f00000003e0,0xfd8c63210fc20cfb18c10842104210840007c000001f,0xfd8c6321f8420210be208421083e000000f80000001f,0xfd8c6321f8420217c4208421083e00000007c000001f,0xfe108410842104210841085f104210fc1f0000007fe0,0xfe1084108421042108410be210842f8821087e0f8000,0xfe1084108421042108410bff10842f8821087e0f8000,0xfe1084108423e4210841085f104210fc1f0000007c00,0xfe1084108423e42109f1085f104210841f0000007c00,0xfe108411f42104210841085f1042108400ffc000001f,0xfe108411f42104210841085f104210fc1f0000007c00,0xfe108411f42104210841085f104210fc210842007c00,0xfe108411f421042108410be210842f8821084200001f,0xfe108411f421042108410bff10842f8821084200001f,0xfe108411f421042109f1085f1042108400f80000001f,0xfe108411f42104f908410842104210fc00f8000003e0,0xfe108411f42104f90841085f1042108400f80000001f,0xfe10841294a524210841085f104210fc1f0000007c00,0xfe10841294a524f908410842104210fc00f8000003e0,0xfe10841294a524f90841085f1042108400f80000001f,0xfe10841294a525294a51085f103e000000f80000001f,0xfe10841294a7e4210841085f104210fc1f0000007c00,0xfe10841294a7e5294bf10842103e000000f8000003e0,0xfe108418c631821084208421f83e000000ffc00003e0,0xfe108418c6318210be208421083e000000ffc000001f,0xfe108418c6318210be208421f83e000000f80000001f,0xfe108418c6318210be208421f83e000000f8000003e0,0xfe108418c6318210be208421f84210841f0000007c00,0xfe108418c6318210be210842104210fc1f0000007c00,0xfe108418c6318217c4210842104210fc1f00000003e0,0xfe108418c6318217c421085f104210841f000000001f,0xfe108418c6318217fe21085f104210841f000000001f,0xfe108418c63184210841085f104210fc1f0000007c00,0xfe108418c63184f90841085f1042108400f80000001f,0xfe108418c633e21084208421f83e000000f8000003e0,0xfe108418c633e210be208421083e000000f80000001f,0xfe108419f6318210842084210801f0000007c000001f,0xfe108419f6318210842084210801ff800007c000001f,0xfe108419f631821084208421f83e000000f8000003e0,0xfe108419f631821084208421f842108400f8000003e0,0xfe108419f6318210be2084210801f0000007c000001f,0xfe108419f6318210be208421083e000000f80000001f,0xfe108419f6318210be2108421042108400f80000001f,0xfe108419f6318217c4210842104210840007c000001f,0xfe108419f63184210841085f1042108400f80000001f]

def r6p3 : Keys := .leaf [
0xfe108419f63184f90841085f1042108400f80000001f,0xfe108419f6318c6318c1085f1042108400f80000001f,0xfe10841ad6b5a21084208421f83e000000f8000003e0,0xfe10841ad6b5a210be208421083e000000f80000001f,0xfe10841ad6b7e21084208421f83e000000f8000003e0,0xfe108421084208fa10821084f8842f88210842007c00,0xfe10842108420c6318c1085f104210fc1f0000007c00,0xfe10842108420c6319f1085f104210841f0000007c00,0xfe10842108420cfb18c1085f1042108400f80000001f,0xfe1084210fc208421082108420842f8821087e0f8000,0xfe1084210fc2084211f2108420842f882108420f8000,0xfe1084210fc20c6318c10842104210fc1f00000003e0,0xfe1084210fc20c6318c1085f104210841f000000001f,0xfe1084210fc20c6319f10842104210841f00000003e0,0xfe108421f84208421082108420842f8821087e007c00,0xfe108421f842084211f2108420842f88210842007c00,0xfe108421f8420c6318c10842104210fc00f8000003e0,0xfe108421f8420c6318c1085f1042108400f80000001f,0xfe108421f8420c6319f108421042108400f8000003e0,0xfe10843e842104210841085f104210fc1f0000007c00,0xfe10843e8421042108410be2104210fc1f00000003e0,0xfe10843ec631821084208421f83e000000f8000003e0,0xfe10843ec6318210be208421083e000000f80000001f,0xfe10843ec6318217c4208421083e00000007c000001f,0xffe00021084208421082108420842f8821087e007fe0,0xffe0002108420842108210842085f1084217c410843f,0xffe0002108420842108210842085ff8821087e0003e0,0xffe0002108420842108210842085ff884217c410843f,0xffe000210842084211f2108420842f88210842007fe0,0xffe000210842084211f2108420842f8821087e007c00,0xffe000210842084211f210842085f10821087e0003e0,0xffe000210842084211f210842085f1084217c4108421,0xffe000210842084211f210842085ff882108420003e0,0xffe000210842084211f210842085ff884217c4108421,0xffe000210842084211f21084f8842f88210842007c00,0xffe000210842084211f21084f885f1082108420003e0,0xffe00021084208fa1082108420842f8821087e007c00,0xffe00021084208fa108210842085f10821087e0003e0,0xffe00021084208fa10821084f8842f88210842007c00,0xffe00021084208fa10821084f885f1082108420003e0,0xffe000210842094a5292108420842f8821087e007c00,0xffe000210842094a529210842085f10821087e0003e0,0xffe000210842094a52921084f8842f88210842007c00,0xffe000210842094a52921084f885f1082108420003e0,0xffe000210842094a529294a528842f8800f80000001f,0xffe000210842094a529294a52885f1080007c000001f,0xffe000210842094a53f2108420842f88210842007c00,0xffe000210842094a53f2108420842f8821087e007c00]

def r6p4 : Keys := .leaf [
0xffe000210842094a53f210842085f1082108420003e0,0xffe000210842094a53f210842085f10821087e0003e0,0xffe000210842094a53f294a52884210800f8000003e0,0xffe000210842094a53f294a5f884210800f8000003e0,0xffe0002108420c6318c10842104210fc00ffc00003e0,0xffe0002108420c6318c1085f1042108400ffc000001f,0xffe0002108420c6318c1085f104210fc00f80000001f,0xffe0002108420c6318c1085f104210fc00f8000003e0,0xffe0002108420c6318c1085f104210fc1f0000007c00,0xffe0002108420c6318c1085f104210fc210842007c00,0xffe0002108420c6318c1085f1084210821087e007c00,0xffe0002108420c6318c10be2104210fc0007c000001f,0xffe0002108420c6318c10be2104210fc00f8000003e0,0xffe0002108420c6318c10be2104210fc1f00000003e0,0xffe0002108420c6318c10be2104210fc2108420003e0,0xffe0002108420c6318c10be21084210821087e0003e0,0xffe0002108420c6318c10be210842f8821084200001f,0xffe0002108420c6318c10bff104210840007c000001f,0xffe0002108420c6318c10bff10842f8821084200001f,0xffe0002108420c6318c2108420842f8821087e007c00,0xffe0002108420c6318c210842085f10821087e0003e0,0xffe0002108420c6318c21084f8842f88210842007c00,0xffe0002108420c6318c21084f885f1082108420003e0,0xffe0002108420c6319f108421042108400f8000003e0,0xffe0002108420c6319f108421042108400ffc00003e0,0xffe0002108420c6319f10842104210fc00f8000003e0,0xffe0002108420c6319f1085f1042108400f80000001f,0xffe0002108420c6319f1085f1042108400f8000003e0,0xffe0002108420c6319f1085f104210841f0000007c00,0xffe0002108420c6319f1085f10842108210842007c00,0xffe0002108420c6319f10be2104210840007c000001f,0xffe0002108420c6319f10be21042108400f8000003e0,0xffe0002108420c6319f10be2104210841f00000003e0,0xffe0002108420c6319f10be2108421082108420003e0,0xffe0002108420c6319f2108420842f88210842007c00,0xffe0002108420c6319f210842085f1082108420003e0,0xffe0002108420c6319f21084f8842f88210842007c00,0xffe0002108420c6319f21084f885f1082108420003e0,0xffe0002108420c6319f6318c60842f88210842007c00,0xffe0002108420c6319f6318c6085f1082108420003e0,0xffe0002108420cfb18c10842104210fc00f8000003e0,0xffe0002108420cfb18c1085f1042108400f80000001f,0xffe0002108420cfb18c10be2104210840007c000001f,0xffe0002108420d6b5ad10842104210fc00f8000003e0,0xffe0002108420d6b5ad1085f1042108400f80000001f,0xffe0002108420d6b5ad10be2104210840007c000001f,0xffe0002108420d6b5bf108421042108400f8000003e0,0xffe0002108420d6b5bf10842104210fc00f8000003e0]

def r6p5 : Keys := .leaf [
0xffe000210fc208421082108420842f8821087e0003e0,0xffe000210fc20842108210842085f10821087e0003e0,0xffe000210fc2084211f210842084210821087e0003e0,0xffe000210fc2084211f2108420842f882108420003e0,0xffe000210fc2084211f210842085f1082108420003e0,0xffe000210fc2084211f21084f88421082108420003e0,0xffe000210fc2094a529210842084210821087e0003e0,0xffe000210fc2094a52921084f88421082108420003e0,0xffe000210fc2094a529294a5288421080007c000001f,0xffe000210fc2094a53f21084208421082108420003e0,0xffe000210fc2094a53f210842084210821087e0003e0,0xffe000210fc20c6318c10842104210fc0007c000001f,0xffe000210fc20c6318c10842104210fc00f8000003e0,0xffe000210fc20c6318c10842104210fc1f00000003e0,0xffe000210fc20c6318c10842104210fc2108420003e0,0xffe000210fc20c6318c1085f104210840007c000001f,0xffe000210fc20c6318c10be2104210840007c000001f,0xffe000210fc20c6318c210842084210821087e0003e0,0xffe000210fc20c6318c21084f88421082108420003e0,0xffe000210fc20c6319f10842104210840007c000001f,0xffe000210fc20c6319f108421042108400f8000003e0,0xffe000210fc20c6319f10842104210841f00000003e0,0xffe000210fc20c6319f21084208421082108420003e0,0xffe000210fc20c6319f21084f88421082108420003e0,0xffe000210fc20c6319f6318c608421082108420003e0,0xffe000210fc20d6b5ad10842104210840007c000001f,0xffe000210fc2108421042108410842104217c410843f,0xffe000210fc2108421042108f90842104217c4108421,0xffe000210fc210842106318c6084210821087e0003e0,0xffe000210fc210842106318c60842f8821084200001f,0xffe000210fc210842106318cf88421082108420003e0,0xffe00021f84208421082108420842f8821087e007c00,0xffe00021f8420842108210842085f10821087e0003e0,0xffe00021f8420c6318c10842104210fc00f8000003e0,0xffe00021f8420c6318c1085f1042108400f80000001f,0xffe00021f8420c6318c10be2104210840007c000001f,0xffe421210842084211f2108420842f88210842007c00,0xffe421210842084211f210842085f1082108420003e0,0xffe4212108420c6318c1085f1042108400f80000001f,0xffe4212108420c6318c10be2104210840007c000001f,0xffe4212108420c6319f108421042108400f8000003e0,0xffe4212108420cfb18c1085f1042108400f80000001f,0xffe4212108420cfb18c10be2104210840007c000001f,0xffe421210fc2084211f21084208421082108420003e0,0xffe421210fc20c6318c10842104210840007c000001f,0xffe84221084204210841085f1042108400f80000001f,0xffe84221084204210841085f1042108400ffc000001f,0xffe84221084204210841085f104210fc210842007c00]

def r6p6 : Keys := .leaf [
0xffe842210842042108410be2104210840007c000001f,0xffe842210842042108410be2104210fc2108420003e0,0xffe842210842042108410be210842f8821084200001f,0xffe842210842042108410bff104210840007c000001f,0xffe842210842042108410bff10842f8821084200001f,0xffe842210842042109f108421042108400f8000003e0,0xffe842210842042109f108421042108400ffc00003e0,0xffe842210842042109f1085f1042108400f80000001f,0xffe842210842042109f1085f1042108400f8000003e0,0xffe842210842042109f1085f104210841f0000007c00,0xffe842210842042109f1085f10842108210842007c00,0xffe842210842042109f10be2104210840007c000001f,0xffe842210842042109f10be21042108400f8000003e0,0xffe842210842042109f10be2104210841f00000003e0,0xffe842210842042109f10be2108421082108420003e0,0xffe842210842042109f2108420842f88210842007c00,0xffe842210842042109f210842085f1082108420003e0,0xffe84221084204f90841085f1042108400f80000001f,0xffe84221084204f908410be2104210840007c000001f,0xffe84221084205294a510842104210fc00f8000003e0,0xffe84221084205294a51085f1042108400f80000001f,0xffe84221084205294a510be2104210840007c000001f,0xffe84221084205294bf108421042108400f8000003e0,0xffe842210842084211f2108420842f88210842007c00,0xffe842210842084211f210842085f1082108420003e0,0xffe84221084208fa10821084f8842f88210842007c00,0xffe84221084208fa10821084f885f1082108420003e0,0xffe842210fc2042108410be2104210840007c000001f,0xffe842210fc2042109f108421042108400f8000003e0,0xffe842210fc2084211f21084208421082108420003e0,0xffe84221f84204210841085f1042108400f80000001f,0xffe84221f842042108410be2104210840007c000001f,0xffe8423ff00010842102108420842f8821087e007c00,0xffe8423ff0001084210210842085f10821087e0003e0,0xffe8423ff000108421021084f8842f88210842007c00,0xffe8423ff000108421021084f885f1082108420003e0,0xffe8423ff210908421010842104210fc00f8000003e0,0xffe8423ff21090842101085f1042108400f80000001f,0xffe8423ff210908421010be2104210840007c000001f,0xffec632108420210842084210801f0000007c000001f,0xffec632108420210842084210801ff800007c000001f,0xffec63210842021084208421f842108400f8000003e0,0xffec632108420210be2084210801f0000007c000001f,0xffec632108420210be208421083e000000f80000001f,0xffec632108420210be2108421042108400f80000001f,0xffec632108420217c42084210801f0000007c000001f,0xffec632108420217c4208421083e00000007c000001f,0xffec632108420217c4210842104210840007c000001f]

def r6p7 : Keys := .leaf [
0xffec6321084204210841085f1042108400f80000001f,0xffec63210842042108410be2104210840007c000001f,0xffec63210842042109f108421042108400f8000003e0,0xffec6321084204f90841085f1042108400f80000001f,0xffec6321084204f908410be2104210840007c000001f,0xffec632108420c6318c1085f1042108400f80000001f,0xffec632108420c6318c10be2104210840007c000001f,0xffec632108420c6319f108421042108400f8000003e0,0xffec632108420cfb18c1085f1042108400f80000001f,0xffec632108420cfb18c10be2104210840007c000001f,0xffec63210fc20210842084210801f0000007c000001f,0xffec63210fc20c6318c10842104210840007c000001f,0xffec6321f8420210842084210801f0000007c000001f,0xffec633ff000108421010842104210fc00f8000003e0,0xffec633ff00010842101085f1042108400f80000001f,0xffec633ff000108421010be2104210840007c000001f,0xffec633ff21090842101085f1042108400f80000001f,0xffec633ff210908421010be2104210840007c000001f,0xfff084108421042108410842104210fc00f8000003e0,0xfff084108421042108410842104210fc00ffc00003e0,0xfff08410842104210841085f1042108400f80000001f,0xfff08410842104210841085f1042108400ffc000001f,0xfff08410842104210841085f104210fc00f80000001f,0xfff08410842104210841085f104210fc00f8000003e0,0xfff08410842104210841085f104210fc1f0000007c00,0xfff08410842104210841085f104210fc210842007c00,0xfff08410842104210841085f1084210821087e007c00,0xfff084108421042108410be21084210821087e0003e0,0xfff084108421042108410be210842f8821084200001f,0xfff084108421042108410bff10842f8821084200001f,0xfff084108423e42108410842104210fc00f8000003e0,0xfff084108423e4210841085f1042108400f80000001f,0xfff084108423e42109f108421042108400f8000003e0,0xfff08411f421042108410842104210fc00f8000003e0,0xfff08411f42104210841085f1042108400f80000001f,0xfff0841294a5242108410842104210fc00f8000003e0,0xfff0841294a524210841085f1042108400f80000001f,0xfff0841294a525294a5108421001f0000007c000001f,0xfff0841294a7e42108410842104210fc00f8000003e0,0xfff08418c6318210842084210801f0000007c000001f,0xfff08418c6318210842084210801ff800007c000001f,0xfff08418c631821084208421f801f0000007c000001f,0xfff08418c631821084208421f83e000000f8000003e0,0xfff08418c631821084208421f842108400f8000003e0,0xfff08418c6318210be2084210801f0000007c000001f,0xfff08418c6318210be208421083e000000f80000001f,0xfff08418c6318210be2108421042108400f80000001f,0xfff08418c6318217c4210842104210840007c000001f]

def r6p8 : Keys := .leaf [
0xfff08418c631842108410842104210fc00f8000003e0,0xfff08418c63184210841085f1042108400f80000001f,0xfff08418c633e210842084210801f0000007c000001f,0xfff08419f6318210842084210801f0000007c000001f,0xfff0841ad6b5a210842084210801f0000007c000001f,0xfff08421084208421082108420842f8821087e007c00,0xfff084210842084211f2108420842f88210842007c00,0xfff0842108420c6318c10842104210fc00f8000003e0,0xfff0842108420c6318c1085f1042108400f80000001f,0xfff0842108420c6319f108421042108400f8000003e0,0xfff084210fc20842108210842084210821087e0003e0,0xfff084210fc208421082108420842f8821084200001f,0xfff084210fc2084211f21084208421082108420003e0,0xfff084210fc20c6318c10842104210840007c000001f,0xfff08421f84208421082108420842f8821087e007c00,0xfff08421f8420c6318c10842104210fc00f8000003e0,0xfff08421f8420c6318c1085f1042108400f80000001f,0xfff0843ff00008421082108420842f8821087e007c00,0xfff0843ff0000842108210842085f10821087e0003e0,0xfff0843ff0000c6318c10842104210fc00f8000003e0,0xfff0843ff0000c6318c1085f1042108400f80000001f,0xfff0843ff0000c6318c10be2104210840007c000001f,0xfff0843ff421042108410842104210fc00f8000003e0,0xfff0843ff42104210841085f1042108400f80000001f,0xfff0843ff421042108410be2104210840007c000001f,0xfff0843ff6318210842084210801f0000007c000001f]

def r6 : Keys := (.branch 0xffe000210842094a53f210842085f1082108420003e0 (.branch 0xfd8c632108420cfb18c1085f1042108400f80000001f (.branch 0xfc0000210fc20d6b5bf10842104210841f00000003e0 r6p0 r6p1) (.branch 0xfe108419f63184f90841085f1042108400f80000001f r6p2 r6p3)) (.branch 0xffe842210842042108410be2104210840007c000001f (.branch 0xffe000210fc208421082108420842f8821087e0003e0 r6p4 r6p5) (.branch 0xffec6321084204210841085f1042108400f80000001f r6p6 (.branch 0xfff08418c631842108410842104210fc00f8000003e0 r6p7 r6p8))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p0 : r6p0.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p1 : r6p1.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p2 : r6p2.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p3 : r6p3.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p4 : r6p4.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p5 : r6p5.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p6 : r6p6.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p7 : r6p7.all (checkFast 5 a5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr6p8 : r6p8.all (checkFast 5 a5) = true := by decide +kernel

theorem badR6 : Rejects 6 r6 :=
  verifyFast 5 a5 r6 badA5 (by
    unfold r6
    simp only [allBranch, Bool.and_true, goodr6p0, goodr6p1, goodr6p2, goodr6p3, goodr6p4, goodr6p5, goodr6p6, goodr6p7, goodr6p8])

def a6p0 : Keys := .leaf [
0x1f8000043f08418c6318210be208421f801f002,0x1fb18c643f08404217c4108421003e00000007e,0x1fc2108318c6304217c410843f07c000001f000,0x1fc210833ec6304217c4108421003e00000007c,0x1ffc00042108418c6318210be208421f801f000,0x1ffc00042108418c6318217c4208421f8000f80,0x1ffc00042108418c633e210be2084210801f000,0x1ffc00042108418c633e217c420842108000f80,0x1ffc000421f8418c631821084208421f8000f80,0x1ffc000421f8418c633e2108420842108000f80,0x1ffc842421084108423e210be2084210801f001,0x1ffc842421084108423e217c420842108000f81,0x1ffd084421084084213e210be2084210801f000,0x1ffd084421084084213e217c420842108000f80,0x1ffd8c642108404217c4108421003e00000007c,0x1ffd8c6421084042f8841084210001f0000007c,0x1ffe1082108420842108210be208421f801f000,0x1ffe108318c63042108410843f003e000000f80,0x1ffe108318c6304217c4108421003e00000007c,0x3f00000842108210847c9f2108210be2084210801ff83,0x3f00000842108210847c9f2108217c421085f10421087,0x3f00000842108210847c9f2108217fe20842108000f83,0x3f00000842108210847c9f2108217fe21085f10421087,0x3f0000084210823e84209f2108210be208421f801f002,0x3f0000084210823e84209f2108217c4208421f8000f82,0x3f0000084210825294a49f2108210be208421f801f003,0x3f0000084210825294a49f2108217c4208421f8000f83,0x3f0000084210825294a4a5297e210be207c000001f001,0x3f0000084210825294a4a5297e217c4207c0000000f81,0x3f0000084210825294fc9f2108210be2084210801f003,0x3f0000084210825294fc9f2108217c420842108000f83,0x3f0000084210825294fca5294a210be207c000001f000,0x3f0000084210825294fca5294a217c4207c0000000f80,0x3f0000084210825294fca5297e210be207c000001f000,0x3f0000084210825294fca5297e217c4207c0000000f80,0x3f00000842108318c6304217c410843f07c000001ff80,0x3f00000842108318c63042f884210be208421f83e0000,0x3f00000842108318c63042ffc410843f07c0000000f80,0x3f00000842108318c63042ffc4210be208421f83e0000,0x3f00000842108318c67c4217c410842107c000001f000,0x3f00000842108318c67c4217c410842107c000001ff80,0x3f00000842108318c67c4217c410843f07c000001f000,0x3f00000842108318c67c42f88410842107c0000000f80,0x3f00000842108318c67c42f88410843f07c0000000f80,0x3f00000842108318c67c42f884210be208421083e0000,0x3f00000842108318c67c42ffc410842107c0000000f80,0x3f00000842108318c67c42ffc4210be208421083e0000,0x3f00000842108318c67c9f2108210be2084210801f002]

def a6p1 : Keys := .leaf [
0x3f00000842108318c67c9f2108217c420842108000f82,0x3f0000084210833ec6304217c4108421003ff0000007e,0x3f0000084210833ec6304217c410843f07c000001f000,0x3f0000084210833ec6304217c410843f084210801f002,0x3f0000084210833ec63042f88410843f07c0000000f80,0x3f0000084210833ec63042f88410843f0842108000f82,0x3f0000084210833ec63042f884210be2084210800007e,0x3f0000084210833ec63042ffc41084210001f0000007e,0x3f0000084210833ec63042ffc4210be2084210800007e,0x3f0000084210833ec63084213e210be2084210801f002,0x3f0000084210833ec63084213e217c420842108000f82,0x3f0000084210833ec6318c633e210be2084210801f002,0x3f0000084210833ec6318c633e217c420842108000f82,0x3f0000084210835ad6b44217c410843f07c000001f000,0x3f0000084210835ad6b442f88410843f07c0000000f80,0x3f0000084210835ad6fc4217c410842107c000001f000,0x3f0000084210835ad6fc4217c410843f07c000001f000,0x3f0000084210835ad6fc42f88410842107c0000000f80,0x3f0000084210835ad6fc42f88410843f07c0000000f80,0x3f00000843f08210847c9f2108217c420842108000f83,0x3f00000843f0825294a4a5297e21084207c0000000f81,0x3f00000843f0825294fca5294a21084207c0000000f80,0x3f00000843f0825294fca5297e21084207c0000000f80,0x3f00000843f08318c6304217c410843f07c0000000f80,0x3f00000843f08318c63042f88410843f07c0000000f80,0x3f00000843f08318c67c42108410842107c0000000f80,0x3f00000843f08318c67c42108410843f07c0000000f80,0x3f00000843f08318c67c4217c410842107c0000000f80,0x3f00000843f08318c67c42f88410842107c0000000f80,0x3f00000843f08318c67c9f21082108420842108000f82,0x3f00000843f0833ec63042f8841084210001f0000007e,0x3f00000843f0833ec6318c633e2108420842108000f82,0x3f00000843f0835ad6b442108410843f07c0000000f80,0x3f00000843f0835ad6fc42108410842107c0000000f80,0x3f00000843f0835ad6fc42108410843f07c0000000f80,0x3f00000843f0842108418c6318210be208421f83e0000,0x3f00000843f0842108418c633e210be208421083e0000,0x3f0000087e1082108420842108210be208421f801ff82,0x3f0000087e1082108420842108217c421085f104210fe,0x3f0000087e1082108420842108217fe21085f104210fe,0x3f0000087e10821084209f2108210be208421f801f003,0x3f0000087e10821084209f2108217c4208421f8000f83,0x3f0000087e108210847c842108210be208421f801f002,0x3f0000087e108210847c84213e210be2084210801f002,0x3f0000087e10823e8420842108210be208421f801f002,0x3f0000087e10823e8420842108217c4208421f8000f82,0x3f0000087e10825294a4842108210be208421f801f002,0x3f0000087e10825294a4a5294a210be2003e00000007e]

def a6p2 : Keys := .leaf [
0x3f0000087e10825294fc842108210be208421f801f002,0x3f0000087e10825294fca5297e210842003e000000f82,0x3f0000087e108318c63042108410843f003ff00000f82,0x3f0000087e108318c6304217c4108421003ff0000007e,0x3f0000087e108318c6304217c410843f003e00000007e,0x3f0000087e108318c6304217c410843f003e000000f82,0x3f0000087e108318c6304217c410843f07c000001f000,0x3f0000087e108318c6304217c410843f084210801f002,0x3f0000087e108318c6304217c421084208421f801f002,0x3f0000087e108318c63042f88410843f07c0000000f80,0x3f0000087e108318c63042f88421084208421f8000f82,0x3f0000087e108318c63042f884210be2084210800007e,0x3f0000087e108318c63042ffc4210be2084210800007e,0x3f0000087e108318c630842108210be208421f801f002,0x3f0000087e108318c67c42108410843f003e000000f82,0x3f0000087e108318c67c4217c4108421003e00000007e,0x3f0000087e10833ec63042108410843f003e000000f82,0x3f0000087e10833ec6304217c4108421003e00000007e,0x3f0000087e10833ec63042f8841084210001f0000007e,0x3f0000087e10835ad6b442108410843f003e000000f82,0x3f0000087e10835ad6b44217c4108421003e00000007e,0x3f0000087e10835ad6fc42108410843f003e000000f82,0x3f0000087e10842108418c6318210be208421f801f002,0x3f0000087e10842108418c633e210be2084210801f002,0x3f0000087e108421f8410842104210841085f104210fe,0x3f0000087e108421f84108423e4210841085f10421086,0x3f0000087e108421f8418c631821084208421f8000f82,0x3f0000087e108421f8418c6318210be2084210800007e,0x3f0000087e108421f8418c633e2108420842108000f82,0x3f21084842108210847c4217c410842107c000001ff81,0x3f21084842108210847c42f884210be208421083e0001,0x3f21084842108210847c42ffc410842107c0000000f81,0x3f21084842108210847c42ffc4210be208421083e0001,0x3f21084842108210847c9f2108210be2084210801f001,0x3f21084842108210847c9f2108217c420842108000f81,0x3f2108484210825294a44217c410843f07c000001f001,0x3f2108484210825294a442f88410843f07c0000000f81,0x3f2108484210825294fc4217c410842107c000001f001,0x3f2108484210825294fc42f88410842107c0000000f81,0x3f21084842108318c67c4217c410842107c000001f000,0x3f21084842108318c67c42f88410842107c0000000f80,0x3f2108484210833ec6304217c4108421003e00000007e,0x3f2108484210833ec63042f8841084210001f0000007e,0x3f21084843f08210847c42f88410842107c0000000f81,0x3f21084843f08210847c9f21082108420842108000f81,0x3f21084843f08318c67c42108410842107c0000000f80,0x3f2108487e108318c6304217c4108421003e00000007e,0x3f42108842108108427c4217c410842107c000001ff80]

def a6p3 : Keys := .leaf [
0x3f42108842108108427c42f884210be208421083e0000,0x3f42108842108108427c42ffc410842107c0000000f80,0x3f42108842108108427c42ffc4210be208421083e0000,0x3f4210884210813e42104217c4108421003ff0000007c,0x3f4210884210813e42104217c410843f084210801f000,0x3f4210884210813e421042f88410843f0842108000f80,0x3f4210884210813e421042f884210be2084210800007c,0x3f4210884210813e421042ffc41084210001f0000007c,0x3f4210884210813e421042ffc4210be2084210800007c,0x3f4210884210813e421084213e210be2084210801f000,0x3f4210884210813e421084213e217c420842108000f80,0x3f4210884210814a52944217c410843f07c000001f000,0x3f4210884210814a529442f88410843f07c0000000f80,0x3f4210884210814a52fc4217c410842107c000001f000,0x3f4210884210814a52fc42f88410842107c0000000f80,0x3f42108842108210847c9f2108210be2084210801f003,0x3f42108842108210847c9f2108217c420842108000f83,0x3f4210884210823e842084213e210be2084210801f000,0x3f4210884210823e842084213e217c420842108000f80,0x3f42108842108318c67c4217c410842107c000001f001,0x3f42108842108318c67c42f88410842107c0000000f81,0x3f4210884210833ec6304217c4108421003e00000007f,0x3f4210884210833ec63042f8841084210001f0000007f,0x3f42108843f08108427c42f88410842107c0000000f80,0x3f42108843f0813e421042f8841084210001f0000007c,0x3f42108843f0823e842084213e2108420842108000f80,0x3f42108843f08318c67c42108410842107c0000000f81,0x3f4210887e10810842104217c4108421003ff0000007e,0x3f4210887e10810842104217c410843f084210801f002,0x3f4210887e108108421042f884210be2084210800007e,0x3f4210887e108108421042ffc4210be2084210800007e,0x3f4210887e108108427c4217c4108421003e00000007e,0x3f4210887e10813e42104217c4108421003e00000007c,0x3f4210887e10813e421042f8841084210001f0000007c,0x3f4210887e10814a529442108410843f003e000000f83,0x3f4210887e10814a52944217c4108421003e00000007f,0x3f4210887e108421084084213e210be2084210801f002,0x3f42108f9084242108404217c410843f07c000001f000,0x3f42108f90842421084042f88410843f07c0000000f80,0x3f42108f9084243f084042108410843f003e000000f82,0x3f42108f9084243f08404217c4108421003e00000007e,0x3f6318c8421080842f882108420f8000003e00000007c,0x3f6318c8421080842f882108420f8000003ff0000007c,0x3f6318c8421080842f8821087e10842107c000001f000,0x3f6318c842108085f1082108420f80000001f0000007c,0x3f6318c842108085f10821087e10842107c0000000f80,0x3f6318c842108085f1084217c410842107c000000007c,0x3f6318c842108085ff882108420f80000001f0000007c]

def a6p4 : Keys := .leaf [
0x3f6318c842108085ff884217c410842107c000000007c,0x3f6318c842108108427c4217c410842107c000001f000,0x3f6318c842108108427c42f88410842107c0000000f80,0x3f6318c84210813e42104217c4108421003e00000007c,0x3f6318c84210813e421042f8841084210001f0000007c,0x3f6318c842108210847c4217c410842107c000001f001,0x3f6318c842108210847c42f88410842107c0000000f81,0x3f6318c84210823e84204217c4108421003e00000007d,0x3f6318c84210823e842042f8841084210001f0000007d,0x3f6318c842108318c67c4217c410842107c000001f000,0x3f6318c842108318c67c42f88410842107c0000000f80,0x3f6318c84210833ec6304217c4108421003e00000007c,0x3f6318c84210833ec63042f8841084210001f0000007c,0x3f6318c843f08085f1082108420f80000001f0000007c,0x3f6318c843f08318c67c42108410842107c0000000f80,0x3f6318c843f0833ec6304210841084210001f0000007c,0x3f6318c87e1080842108210842007c000001f0000007e,0x3f6318c87e1080842108210842007fe00001f0000007e,0x3f6318c87e108084210821087e108421003e000000f82,0x3f6318c87e1080842f88210842007c000001f0000007e,0x3f6318c87e1080842f882108420f8000003e00000007c,0x3f6318c87e1080842f88421084108421003e00000007e,0x3f6318c87e108085f1082108420f80000001f0000007c,0x3f6318c87e108085f1084210841084210001f0000007e,0x3f6318c87e10810842104217c4108421003e00000007e,0x3f6318c87e108318c6304217c4108421003e00000007e,0x3f6318c87e10842108404217c4108421003e00000007e,0x3f6318cf8000042108404217c410843f07c000001f002,0x3f6318cf80000421084042f88410843f07c0000000f82,0x3f6318cf9084243f08404217c4108421003e00000007e,0x3f8421042108410842104217c410843f07c000001ff80,0x3f84210421084108421042f884210be208421f83e0000,0x3f84210421084108421042ffc4210be208421f83e0000,0x3f84210421084108427c4217c410843f07c000001f001,0x3f8421042108413e42104217c4108421003ff0000007d,0x3f8421042108413e42104217c410843f07c000001f001,0x3f8421042108413e42104217c410843f084210801f001,0x3f8421042108413e421042f884210be2084210800007d,0x3f8421042108413e421042ffc4210be2084210800007d,0x3f8421042108414a52944217c410843f07c000001f001,0x3f8421042108414a52fc4217c410843f07c000001f001,0x3f8421042108f90842104217c410843f07c000001f000,0x3f8421042108f908427c4217c410842107c000001f000,0x3f8421042108f93e42104217c4108421003e00000007d,0x3f8421047d08410842104217c4108421003ff0000007c,0x3f8421047d08410842104217c410843f07c000001f000,0x3f8421047d08410842104217c410843f084210801f000,0x3f8421047d084108421042f884210be2084210800007c]

def a6p5 : Keys := .leaf [
0x3f8421047d084108421042ffc4210be2084210800007c,0x3f8421047d084108427c4217c4108421003e00000007c,0x3f8421047d08413e421042108410843f003e000000f80,0x3f8421047d08413e42104217c4108421003e00000007c,0x3f8421047d08414a529442108410843f003e000000f81,0x3f8421047d08414a52944217c4108421003e00000007d,0x3f842104a529490842104217c410843f07c000001f000,0x3f842104a529493e421042108410843f003e000000f80,0x3f842104a529493e42104217c4108421003e00000007c,0x3f842104a529494a52944217c40f8000003e00000007c,0x3f842104a529f90842104217c410843f07c000001f000,0x3f842104a529f94a52fc4210840f8000003e000000f80,0x3f842106318c6084210821087e0f8000003ff00000f80,0x3f842106318c60842f882108420f8000003ff0000007c,0x3f842106318c60842f8821087e0f8000003e00000007c,0x3f842106318c60842f8821087e0f8000003e000000f80,0x3f842106318c60842f8821087e10842107c000001f000,0x3f842106318c60842f8842108410843f07c000001f000,0x3f842106318c6085f10842108410843f07c0000000f80,0x3f842106318c6085f1084217c410842107c000000007c,0x3f842106318c6085ff884217c410842107c000000007c,0x3f842106318c610842104217c410843f07c000001f000,0x3f842106318c613e42104217c4108421003e00000007c,0x3f842106318c621084204217c410843f07c000001f001,0x3f842106318cf884210821087e0f8000003e000000f80,0x3f842106318cf8842f882108420f8000003e00000007c,0x3f8421067d8c60842108210842007c000001f0000007c,0x3f8421067d8c60842108210842007fe00001f0000007c,0x3f8421067d8c6084210821087e0f8000003e000000f80,0x3f8421067d8c6084210821087e108421003e000000f80,0x3f8421067d8c60842f88210842007c000001f0000007c,0x3f8421067d8c60842f882108420f8000003e00000007c,0x3f8421067d8c60842f88421084108421003e00000007c,0x3f8421067d8c6085f1084210841084210001f0000007c,0x3f8421067d8c610842104217c4108421003e00000007c,0x3f8421067d8c613e42104217c4108421003e00000007c,0x3f8421067d8c623e84204217c4108421003e00000007d,0x3f8421067d8c6318c6304217c4108421003e00000007c,0x3f842106b5ad6884210821087e0f8000003e000000f80,0x3f842106b5ad68842f882108420f8000003e00000007c,0x3f842106b5adf884210821087e0f8000003e000000f80,0x3f84210842108210847c9f2108210be2084210801f001,0x3f8421084210823e842084213e210be2084210801f000,0x3f84210842108318c6304217c410843f07c000001f000,0x3f84210842108318c67c4217c410842107c000001f000,0x3f8421084210833ec6304217c4108421003e00000007c,0x3f84210843f082108420842108210be208421f83e0000,0x3f84210843f08210842084213e210be208421083e0001]

def a6p6 : Keys := .leaf [
0x3f84210843f08210847c842108210be208421083e0000,0x3f84210843f08318c63042108410843f07c0000000f80,0x3f84210843f08318c6304217c410842107c000000007c,0x3f84210843f08318c67c42108410842107c0000000f80,0x3f8421087e1082108420842108210be208421f801f000,0x3f8421087e108210842084213e210be2084210801f001,0x3f8421087e108210847c842108210be2084210801f000,0x3f8421087e108318c63042108410843f003e000000f80,0x3f8421087e108318c6304217c4108421003e00000007c,0x3f8421087e108318c67c421084108421003e000000f80,0x3f84210f80000318c6304217c410843f07c000001f002,0x3f84210f80000318c63042f88410843f07c0000000f82,0x3f84210fa108410842104217c410843f07c000001f000,0x3f84210fa1084108421042f88410843f07c0000000f80,0x3f84210fa108413e42104217c4108421003e00000007f,0x3f84210fa108413e421042f8841084210001f0000007f,0x3f84210fb18c6084210821087e0f8000003e000000f80,0x3f84210fb18c60842f882108420f8000003e00000007c,0x3f84210fb18c6085f1082108420f80000001f0000007c,0x3ff80008421082108420842108210be208421f801ff80,0x3ff80008421082108420842108217c421085f104210fc,0x3ff80008421082108420842108217fe208421f8000f80,0x3ff80008421082108420842108217fe21085f104210fc,0x3ff8000842108210842084213e210be2084210801ff81,0x3ff8000842108210842084213e210be208421f801f001,0x3ff8000842108210842084213e217c4208421f8000f81,0x3ff8000842108210842084213e217c421085f10421085,0x3ff8000842108210842084213e217fe20842108000f81,0x3ff8000842108210842084213e217fe21085f10421085,0x3ff800084210821084209f2108210be208421f801f001,0x3ff800084210821084209f2108217c4208421f8000f81,0x3ff80008421082108420a5294a210be208421f801f001,0x3ff80008421082108420a5294a217c4208421f8000f81,0x3ff80008421082108420a5297e210be2084210801f001,0x3ff80008421082108420a5297e210be208421f801f001,0x3ff80008421082108420a5297e217c420842108000f81,0x3ff80008421082108420a5297e217c4208421f8000f81,0x3ff8000842108210847c842108210be2084210801ff80,0x3ff8000842108210847c842108210be208421f801f000,0x3ff8000842108210847c842108217c4208421f8000f80,0x3ff8000842108210847c842108217c421085f10421084,0x3ff8000842108210847c842108217fe20842108000f80,0x3ff8000842108210847c842108217fe21085f10421084,0x3ff8000842108210847c84213e210be2084210801f000,0x3ff8000842108210847c84213e217c420842108000f80,0x3ff8000842108210847c9f2108210be2084210801f001,0x3ff8000842108210847c9f2108217c420842108000f81,0x3ff8000842108210847ca5294a210be2084210801f001]

def a6p7 : Keys := .leaf [
0x3ff8000842108210847ca5294a217c420842108000f81,0x3ff800084210823e8420842108210be208421f801f000,0x3ff800084210823e8420842108217c4208421f8000f80,0x3ff800084210823e842084213e210be2084210801f000,0x3ff800084210823e842084213e217c420842108000f80,0x3ff800084210825294a4842108210be208421f801f000,0x3ff800084210825294a4842108217c4208421f8000f80,0x3ff800084210825294a484213e210be2084210801f000,0x3ff800084210825294a484213e217c420842108000f80,0x3ff800084210825294a4a5294a210be2003e00000007c,0x3ff800084210825294a4a5294a217c420001f0000007c,0x3ff800084210825294a4a5297e210842003e000000f81,0x3ff800084210825294fc842108210be2084210801f000,0x3ff800084210825294fc842108210be208421f801f000,0x3ff800084210825294fc842108217c420842108000f80,0x3ff800084210825294fc842108217c4208421f8000f80,0x3ff800084210825294fca5294a210842003e000000f80,0x3ff800084210825294fca5297e210842003e000000f80,0x3ff8000842108318c63042108410843f003ff00000f80,0x3ff8000842108318c6304217c4108421003ff0000007c,0x3ff8000842108318c6304217c410843f003e00000007c,0x3ff8000842108318c6304217c410843f003e000000f80,0x3ff8000842108318c6304217c410843f07c000001f000,0x3ff8000842108318c6304217c410843f084210801f000,0x3ff8000842108318c6304217c421084208421f801f000,0x3ff8000842108318c63042f88410843f0001f0000007c,0x3ff8000842108318c63042f88410843f003e000000f80,0x3ff8000842108318c63042f88410843f07c0000000f80,0x3ff8000842108318c63042f88410843f0842108000f80,0x3ff8000842108318c63042f88421084208421f8000f80,0x3ff8000842108318c63042f884210be2084210800007c,0x3ff8000842108318c63042ffc41084210001f0000007c,0x3ff8000842108318c63042ffc4210be2084210800007c,0x3ff8000842108318c630842108210be208421f801f000,0x3ff8000842108318c630842108217c4208421f8000f80,0x3ff8000842108318c63084213e210be2084210801f000,0x3ff8000842108318c63084213e217c420842108000f80,0x3ff8000842108318c631084210210be208421f801f001,0x3ff8000842108318c631084210217c4208421f8000f81,0x3ff8000842108318c67c421084108421003e000000f80,0x3ff8000842108318c67c421084108421003ff00000f80,0x3ff8000842108318c67c42108410843f003e000000f80,0x3ff8000842108318c67c4217c4108421003e00000007c,0x3ff8000842108318c67c4217c4108421003e000000f80,0x3ff8000842108318c67c4217c410842107c000001f000,0x3ff8000842108318c67c4217c4210842084210801f000,0x3ff8000842108318c67c42f8841084210001f0000007c,0x3ff8000842108318c67c42f884108421003e000000f80]

def a6p8 : Keys := .leaf [
0x3ff8000842108318c67c42f88410842107c0000000f80,0x3ff8000842108318c67c42f8842108420842108000f80,0x3ff8000842108318c67c842108210be2084210801f000,0x3ff8000842108318c67c842108217c420842108000f80,0x3ff8000842108318c67c84213e210be2084210801f000,0x3ff8000842108318c67c84213e217c420842108000f80,0x3ff8000842108318c67d08423e210be2084210801f001,0x3ff8000842108318c67d08423e217c420842108000f81,0x3ff8000842108318c67d8c6318210be2084210801f000,0x3ff8000842108318c67d8c6318217c420842108000f80,0x3ff800084210833ec63042108410843f003e000000f80,0x3ff800084210833ec6304217c4108421003e00000007c,0x3ff800084210833ec63042f8841084210001f0000007c,0x3ff800084210835ad6b442108410843f003e000000f80,0x3ff800084210835ad6b44217c4108421003e00000007c,0x3ff800084210835ad6b442f8841084210001f0000007c,0x3ff800084210835ad6fc421084108421003e000000f80,0x3ff800084210835ad6fc42108410843f003e000000f80,0x3ff8000843f082108420842108210be208421f8000f80,0x3ff8000843f082108420842108217c4208421f8000f80,0x3ff8000843f08210842084213e21084208421f8000f81,0x3ff8000843f08210842084213e210be20842108000f81,0x3ff8000843f08210842084213e217c420842108000f81,0x3ff8000843f082108420a5294a21084208421f8000f81,0x3ff8000843f082108420a5297e2108420842108000f81,0x3ff8000843f082108420a5297e21084208421f8000f81,0x3ff8000843f08210847c84210821084208421f8000f80,0x3ff8000843f08210847c842108210be20842108000f80,0x3ff8000843f08210847c842108217c420842108000f80,0x3ff8000843f08210847c84213e2108420842108000f80,0x3ff8000843f08210847ca5294a2108420842108000f81,0x3ff8000843f0825294a484210821084208421f8000f80,0x3ff8000843f0825294a484213e2108420842108000f80,0x3ff8000843f0825294a4a5294a2108420001f0000007c,0x3ff8000843f0825294fc8421082108420842108000f80,0x3ff8000843f0825294fc84210821084208421f8000f80,0x3ff8000843f08318c63042108410843f0001f0000007c,0x3ff8000843f08318c63042108410843f003e000000f80,0x3ff8000843f08318c63042108410843f07c0000000f80,0x3ff8000843f08318c63042108410843f0842108000f80,0x3ff8000843f08318c6304217c41084210001f0000007c,0x3ff8000843f08318c63042f8841084210001f0000007c,0x3ff8000843f08318c63084210821084208421f8000f80,0x3ff8000843f08318c63084213e2108420842108000f80,0x3ff8000843f08318c63108421021084208421f8000f81,0x3ff8000843f08318c67c4210841084210001f0000007c,0x3ff8000843f08318c67c421084108421003e000000f80,0x3ff8000843f08318c67c42108410842107c0000000f80]

def a6p9 : Keys := .leaf [
0x3ff8000843f08318c67c8421082108420842108000f80,0x3ff8000843f08318c67c84213e2108420842108000f80,0x3ff8000843f08318c67d08423e2108420842108000f81,0x3ff8000843f08318c67d8c63182108420842108000f80,0x3ff8000843f0835ad6b44210841084210001f0000007c,0x3ff8000843f0842108410842104210841085f104210fc,0x3ff8000843f08421084108421042109f1085f10421085,0x3ff8000843f08421084108423e4210841085f10421084,0x3ff8000843f0842108418c631821084208421f8000f80,0x3ff8000843f0842108418c6318210be2084210800007c,0x3ff8000843f0842108418c633e2108420842108000f80,0x3ff800087e1082108420842108210be208421f801f000,0x3ff800087e1082108420842108217c4208421f8000f80,0x3ff800087e108318c63042108410843f003e000000f80,0x3ff800087e108318c6304217c4108421003e00000007c,0x3ff800087e108318c63042f8841084210001f0000007c,0x3ff8000f8000042108418c6318210be208421f801f002,0x3ff8000f8000042108418c6318217c4208421f8000f82,0x3ff8000f8000042108418c633e210be2084210801f002,0x3ff8000f8000042108418c633e217c420842108000f82,0x3ff8000f80000421f8418c631821084208421f8000f82,0x3ff8000f80000421f8418c633e2108420842108000f82,0x3ff908484210821084204217c4108421003ff0000007d,0x3ff908484210821084204217c410843f084210801f001,0x3ff9084842108210842042f88410843f0842108000f81,0x3ff9084842108210842042f884210be2084210800007d,0x3ff9084842108210842042ffc41084210001f0000007d,0x3ff9084842108210842042ffc4210be2084210800007d,0x3ff9084842108210842084213e210be2084210801f001,0x3ff9084842108210842084213e217c420842108000f81,0x3ff9084842108210847c421084108421003ff00000f81,0x3ff9084842108210847c4217c4108421003e00000007d,0x3ff9084842108210847c4217c4108421003e000000f81,0x3ff9084842108210847c4217c410842107c000001f001,0x3ff9084842108210847c4217c4210842084210801f001,0x3ff9084842108210847c42f8841084210001f0000007d,0x3ff9084842108210847c42f884108421003e000000f81,0x3ff9084842108210847c42f88410842107c0000000f81,0x3ff9084842108210847c42f8842108420842108000f81,0x3ff9084842108210847c842108210be2084210801f000,0x3ff9084842108210847c842108217c420842108000f80,0x3ff908484210823e84204217c4108421003e00000007d,0x3ff908484210823e842042f8841084210001f0000007d,0x3ff908484210825294a442108410843f003e000000f81,0x3ff908484210825294a44217c4108421003e00000007d,0x3ff908484210825294a442f8841084210001f0000007d,0x3ff908484210825294fc421084108421003e000000f81,0x3ff9084842108318c6304217c4108421003e00000007c]

def a6p10 : Keys := .leaf [
0x3ff9084842108318c63042f8841084210001f0000007c,0x3ff9084842108318c67c421084108421003e000000f80,0x3ff908484210833ec6304217c4108421003e00000007c,0x3ff908484210833ec63042f8841084210001f0000007c,0x3ff9084843f08210842042f8841084210001f0000007d,0x3ff9084843f08210842084213e2108420842108000f81,0x3ff9084843f08210847c421084108421003e000000f81,0x3ff9084843f08210847c8421082108420842108000f80,0x3ff9084843f08318c6304210841084210001f0000007c,0x3ff908487e10821084204217c4108421003e00000007d,0x3ff908487e108210842042f8841084210001f0000007d,0x3ff9084fa108442108404217c4108421003e00000007f,0x3ff9084fa1084421084042f8841084210001f0000007f,0x3ff9084fb18c642108404217c4108421003e00000007e,0x3ff9084fb18c6421084042f8841084210001f0000007e,0x3ff9084ffc0004210841084210210be208421f801f001,0x3ff9084ffc0004210841084210217c4208421f8000f81,0x3ff9084ffc000421084108423e210be2084210801f001,0x3ff9084ffc000421084108423e217c420842108000f81,0x3ffa10884210810842104217c4108421003e00000007c,0x3ffa10884210810842104217c4108421003ff0000007c,0x3ffa10884210810842104217c410843f084210801f000,0x3ffa108842108108421042f8841084210001f0000007c,0x3ffa108842108108421042f88410843f0842108000f80,0x3ffa108842108108421042f884210be2084210800007c,0x3ffa108842108108421042ffc41084210001f0000007c,0x3ffa108842108108421042ffc4210be2084210800007c,0x3ffa108842108108427c421084108421003e000000f80,0x3ffa108842108108427c421084108421003ff00000f80,0x3ffa108842108108427c4217c4108421003e00000007c,0x3ffa108842108108427c4217c4108421003e000000f80,0x3ffa108842108108427c4217c410842107c000001f000,0x3ffa108842108108427c4217c4210842084210801f000,0x3ffa108842108108427c42f8841084210001f0000007c,0x3ffa108842108108427c42f884108421003e000000f80,0x3ffa108842108108427c42f88410842107c0000000f80,0x3ffa108842108108427c42f8842108420842108000f80,0x3ffa108842108108427c842108210be2084210801f000,0x3ffa108842108108427c842108217c420842108000f80,0x3ffa10884210813e42104217c4108421003e00000007c,0x3ffa10884210813e421042f8841084210001f0000007c,0x3ffa10884210814a529442108410843f003e000000f80,0x3ffa10884210814a52944217c4108421003e00000007c,0x3ffa10884210814a529442f8841084210001f0000007c,0x3ffa10884210814a52fc421084108421003e000000f80,0x3ffa108842108210847c842108210be2084210801f000,0x3ffa108842108210847c842108217c420842108000f80,0x3ffa10884210823e842084213e210be2084210801f000]

def a6p11 : Keys := .leaf [
0x3ffa10884210823e842084213e217c420842108000f80,0x3ffa108842108318c67c421084108421003e000000f81,0x3ffa10884210833ec6304217c4108421003e00000007d,0x3ffa10884210833ec63042f8841084210001f0000007d,0x3ffa108843f08108421042f8841084210001f0000007c,0x3ffa108843f08108427c421084108421003e000000f80,0x3ffa108843f08210847c8421082108420842108000f80,0x3ffa10887e10810842104217c4108421003e00000007c,0x3ffa10887e108108421042f8841084210001f0000007c,0x3ffa108f9084242108404217c4108421003e00000007e,0x3ffa108f90842421084042f8841084210001f0000007e,0x3ffa108fa1084421084084213e210be2084210801f002,0x3ffa108fa1084421084084213e217c420842108000f82,0x3ffa108fc210810842104217c4108421003e00000007e,0x3ffa108fc2108108421042f8841084210001f0000007e,0x3ffa108ffc0004210840842108210be208421f801f000,0x3ffa108ffc0004210840842108217c4208421f8000f80,0x3ffa108ffc000421084084213e210be2084210801f000,0x3ffa108ffc000421084084213e217c420842108000f80,0x3ffa108ffc842421084042108410843f003e000000f80,0x3ffa108ffc84242108404217c4108421003e00000007c,0x3ffa108ffc842421084042f8841084210001f0000007c,0x3ffb18c8421080842108210842007c000001f0000007c,0x3ffb18c8421080842108210842007fe00001f0000007c,0x3ffb18c842108084210821087e108421003e000000f80,0x3ffb18c8421080842f88210842007c000001f0000007c,0x3ffb18c8421080842f882108420f8000003e00000007c,0x3ffb18c8421080842f88421084108421003e00000007c,0x3ffb18c842108085f108210842007c000001f0000007c,0x3ffb18c842108085f1082108420f80000001f0000007c,0x3ffb18c842108085f1084210841084210001f0000007c,0x3ffb18c84210810842104217c4108421003e00000007c,0x3ffb18c842108108421042f8841084210001f0000007c,0x3ffb18c842108108427c421084108421003e000000f80,0x3ffb18c84210813e42104217c4108421003e00000007c,0x3ffb18c84210813e421042f8841084210001f0000007c,0x3ffb18c842108210847c421084108421003e000000f81,0x3ffb18c84210823e84204217c4108421003e00000007d,0x3ffb18c84210823e842042f8841084210001f0000007d,0x3ffb18c842108318c6304217c4108421003e00000007c,0x3ffb18c842108318c63042f8841084210001f0000007c,0x3ffb18c842108318c67c421084108421003e000000f80,0x3ffb18c84210833ec6304217c4108421003e00000007c,0x3ffb18c84210833ec63042f8841084210001f0000007c,0x3ffb18c843f080842108210842007c000001f0000007c,0x3ffb18c843f08318c6304210841084210001f0000007c,0x3ffb18c87e1080842108210842007c000001f0000007c,0x3ffb18cf9084242108404217c4108421003e00000007e]

def a6p12 : Keys := .leaf [
0x3ffb18cf90842421084042f8841084210001f0000007e,0x3ffb18cfa108442108404217c4108421003e00000007f,0x3ffb18cfa1084421084042f8841084210001f0000007f,0x3ffb18cfb18c642108404217c4108421003e00000007e,0x3ffb18cfb18c6421084042f8841084210001f0000007e,0x3ffb18cfc21080842108210842007c000001f0000007e,0x3ffb18cffc000421084042108410843f003e000000f80,0x3ffb18cffc00042108404217c4108421003e00000007c,0x3ffb18cffc000421084042f8841084210001f0000007c,0x3ffb18cffc84242108404217c4108421003e00000007c,0x3ffb18cffc842421084042f8841084210001f0000007c,0x3ffb18cffd08442108404217c4108421003e00000007d,0x3ffb18cffd084421084042f8841084210001f0000007d,0x3ffc210421084108421042108410843f003e000000f80,0x3ffc210421084108421042108410843f003ff00000f80,0x3ffc21042108410842104217c4108421003e00000007c,0x3ffc21042108410842104217c4108421003ff0000007c,0x3ffc21042108410842104217c410843f003e00000007c,0x3ffc21042108410842104217c410843f003e000000f80,0x3ffc21042108410842104217c410843f07c000001f000,0x3ffc21042108410842104217c410843f084210801f000,0x3ffc21042108410842104217c421084208421f801f000,0x3ffc210421084108421042f88421084208421f8000f80,0x3ffc210421084108421042f884210be2084210800007c,0x3ffc210421084108421042ffc4210be2084210800007c,0x3ffc210421084108427c42108410843f003e000000f81,0x3ffc210421084108427c4217c4108421003e00000007d,0x3ffc21042108413e421042108410843f003e000000f81,0x3ffc21042108413e42104217c4108421003e00000007d,0x3ffc21042108414a529442108410843f003e000000f81,0x3ffc21042108414a52944217c4108421003e00000007d,0x3ffc21042108414a52fc42108410843f003e000000f81,0x3ffc21042108f908421042108410843f003e000000f80,0x3ffc21042108f90842104217c4108421003e00000007c,0x3ffc21042108f908427c421084108421003e000000f80,0x3ffc21047d084108421042108410843f003e000000f80,0x3ffc21047d08410842104217c4108421003e00000007c,0x3ffc2104a5294908421042108410843f003e000000f80,0x3ffc2104a529490842104217c4108421003e00000007c,0x3ffc2104a529494a5294421084007c000001f0000007c,0x3ffc2104a529f908421042108410843f003e000000f80,0x3ffc2106318c60842108210842007c000001f0000007c,0x3ffc2106318c60842108210842007fe00001f0000007c,0x3ffc2106318c6084210821087e007c000001f0000007c,0x3ffc2106318c6084210821087e0f8000003e000000f80,0x3ffc2106318c6084210821087e108421003e000000f80,0x3ffc2106318c60842f88210842007c000001f0000007c,0x3ffc2106318c60842f882108420f8000003e00000007c]

def a6p13 : Keys := .leaf [
0x3ffc2106318c60842f88421084108421003e00000007c,0x3ffc2106318c6085f1084210841084210001f0000007c,0x3ffc2106318c6108421042108410843f003e000000f80,0x3ffc2106318c610842104217c4108421003e00000007c,0x3ffc2106318c6210842042108410843f003e000000f81,0x3ffc2106318c621084204217c4108421003e00000007d,0x3ffc2106318cf8842108210842007c000001f0000007c,0x3ffc21067d8c60842108210842007c000001f0000007c,0x3ffc2106b5ad68842108210842007c000001f0000007c,0x3ffc2108421082108420842108210be208421f801f000,0x3ffc210842108210842084213e210be2084210801f001,0x3ffc210842108210847c842108210be2084210801f000,0x3ffc210842108318c63042108410843f003e000000f80,0x3ffc210842108318c6304217c4108421003e00000007c,0x3ffc210842108318c67c421084108421003e000000f80,0x3ffc210843f08210842084210821084208421f8000f80,0x3ffc210843f082108420842108210be2084210800007c,0x3ffc210843f08210842084213e2108420842108000f81,0x3ffc210843f08210847c8421082108420842108000f80,0x3ffc210843f08318c6304210841084210001f0000007c,0x3ffc21087e1082108420842108210be208421f801f000,0x3ffc21087e108318c63042108410843f003e000000f80,0x3ffc21087e108318c6304217c4108421003e00000007c,0x3ffc210fa1084108421042108410843f003e000000f82,0x3ffc210fa108410842104217c4108421003e00000007e,0x3ffc210fb18c60842108210842007c000001f0000007e,0x3ffc210fc21082108420842108210be208421f801f002,0x3ffc210fc2108318c63042108410843f003e000000f82,0x3ffc210fc2108318c6304217c4108421003e00000007e,0x3ffc210ffc0002108420842108210be208421f801f000,0x3ffc210ffc0002108420842108217c4208421f8000f80,0x3ffc210ffc000318c63042108410843f003e000000f80,0x3ffc210ffc000318c6304217c4108421003e00000007c,0x3ffc210ffc000318c63042f8841084210001f0000007c,0x3ffc210ffc842210842042108410843f003e000000f81,0x3ffc210ffc84221084204217c4108421003e00000007d,0x3ffc210ffc842210842042f8841084210001f0000007d,0x3ffc210ffd084108421042108410843f003e000000f80,0x3ffc210ffd08410842104217c4108421003e00000007c,0x3ffc210ffd084108421042f8841084210001f0000007c,0x3ffc210ffd8c60842108210842007c000001f0000007c]

def a6 : Keys := (.branch 0xffe000210842084211f294a52885f1082108420003e0 (.branch 0xfd0842210842042109f10be210842f882108420f8000 (.branch 0xfc00002108420c6319f27c842085f1082108420003e0 a6p0 (.branch 0xfc000021f842094a53f2108420842f8821087e007c00 a6p1 a6p2)) (.branch 0xfe108411f421042108410bff10842f8821084200001f (.branch 0xfd8c632108420217fe21085f104210841f000000001f a6p3 a6p4) (.branch 0xfe1084210fc2084211f2108420842f882108420f8000 a6p5 a6p6))) (.branch 0xffe4212108420c6318c10be2104210840007c000001f (.branch 0xffe0002108420c6319f10be2104210841f00000003e0 a6p7 (.branch 0xffe000210fc20c6319f21084208421082108420003e0 a6p8 a6p9)) (.branch 0xffec633e4210908421010be2104210840007c000001f (.branch 0xffe84221084208fa10821084f885f1082108420003e0 a6p10 a6p11) (.branch 0xfff08418c6318210be2108421042108400f80000001f a6p12 a6p13))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p0 : a6p0.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p1 : a6p1.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p2 : a6p2.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p3 : a6p3.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p4 : a6p4.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p5 : a6p5.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p6 : a6p6.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p7 : a6p7.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p8 : a6p8.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p9 : a6p9.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p10 : a6p10.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p11 : a6p11.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p12 : a6p12.all (checkAlias r6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda6p13 : a6p13.all (checkAlias r6) = true := by decide +kernel

theorem badA6 : RejectsAlias 6 a6 :=
  verifyAliases 6 r6 a6 badR6 (by
    unfold a6
    simp only [allBranch, Bool.and_true, gooda6p0, gooda6p1, gooda6p2, gooda6p3, gooda6p4, gooda6p5, gooda6p6, gooda6p7, gooda6p8, gooda6p9, gooda6p10, gooda6p11, gooda6p12, gooda6p13])

def r7p0 : Keys := .leaf [
0xfc00002108420c6318c1085f104210fc1f0000007c00,0xfc00002108420c6318c10be2104210fc1f00000003e0,0xfc00002108420c6319f1085f104210841f0000007c00,0xfc00002108420c6319f10be2104210841f00000003e0,0xfc0000210fc20c6318c10842104210fc1f00000003e0,0xfc0000210fc20c6319f10842104210841f00000003e0,0xfd0842210842042109f1085f104210841f0000007c00,0xfd0842210842042109f10be2104210841f00000003e0,0xfd084221084204f90841085f1042108400f80000001f,0xfd084221084204f908410be2104210840007c000001f,0xfd8c632108420210be208421083e000000f80000001f,0xfd8c632108420217c4208421083e00000007c000001f,0xfe108410842104210841085f104210fc1f0000007c00,0xfe108411f42104210841085f1042108400f80000001f,0xfe108418c631821084208421f83e000000f8000003e0,0xfe108418c6318210be208421083e000000f80000001f,0xfe108419f6318210842084210801f0000007c000001f,0xffe00021084208421082108420842f8821087e007c00,0xffe0002108420842108210842085f10821087e0003e0,0xffe000210842084211f2108420842f88210842007c00,0xffe000210842084211f210842085f1082108420003e0,0xffe0002108420c6318c10842104210fc00f8000003e0,0xffe0002108420c6318c1085f1042108400f80000001f,0xffe0002108420c6318c10be2104210840007c000001f,0xffe0002108420c6319f108421042108400f8000003e0,0xffe000210fc20842108210842084210821087e0003e0,0xffe000210fc2084211f21084208421082108420003e0,0xffe000210fc20c6318c10842104210840007c000001f,0xffe84221084204210841085f1042108400f80000001f,0xffe842210842042108410be2104210840007c000001f,0xffe842210842042109f108421042108400f8000003e0,0xffec632108420210842084210801f0000007c000001f,0xfff084108421042108410842104210fc00f8000003e0,0xfff08410842104210841085f1042108400f80000001f,0xfff08418c6318210842084210801f0000007c000001f,0x1f8000042108410842104210841085f104210fc1f0000007fe0,0x1f80000421084108421042108410be210842f8821087e0f8000,0x1f80000421084108421042108410bff104210fc1f00000003e0,0x1f80000421084108421042108410bff10842f8821087e0f8000,0x1f80000421084108423e4210841085f104210841f0000007fe0,0x1f80000421084108423e4210841085f104210fc1f0000007c00,0x1f80000421084108423e42108410be2104210fc1f00000003e0,0x1f80000421084108423e42108410be210842f882108420f8000,0x1f80000421084108423e42108410bff104210841f00000003e0,0x1f80000421084108423e42108410bff10842f882108420f8000,0x1f80000421084108423e42109f1085f104210841f0000007c00,0x1f80000421084108423e42109f10be2104210841f00000003e0,0x1f8000042108411f42104210841085f104210fc1f0000007c00]

def r7p1 : Keys := .leaf [
0x1f8000042108411f421042108410be2104210fc1f00000003e0,0x1f8000042108411f421042109f1085f104210841f0000007c00,0x1f8000042108411f421042109f10be2104210841f00000003e0,0x1f800004210841294a524210841085f104210fc1f0000007c00,0x1f800004210841294a5242108410be2104210fc1f00000003e0,0x1f800004210841294a5242109f1085f104210841f0000007c00,0x1f800004210841294a5242109f10be2104210841f00000003e0,0x1f800004210841294a525294a51085f103e000000f80000001f,0x1f800004210841294a525294a510be2103e00000007c000001f,0x1f800004210841294a7e4210841085f104210841f0000007c00,0x1f800004210841294a7e4210841085f104210fc1f0000007c00,0x1f800004210841294a7e42108410be2104210841f00000003e0,0x1f800004210841294a7e42108410be2104210fc1f00000003e0,0x1f800004210841294a7e5294a510842103e000000f8000003e0,0x1f800004210841294a7e5294bf10842103e000000f8000003e0,0x1f8000042108418c631821084208421f83e000000ffc00003e0,0x1f8000042108418c6318210be208421083e000000ffc000001f,0x1f8000042108418c6318210be208421f83e000000f80000001f,0x1f8000042108418c6318210be208421f83e000000f8000003e0,0x1f8000042108418c6318210be208421f84210841f0000007c00,0x1f8000042108418c6318210be210842104210fc1f0000007c00,0x1f8000042108418c6318217c4208421f83e00000007c000001f,0x1f8000042108418c6318217c4208421f83e000000f8000003e0,0x1f8000042108418c6318217c4208421f84210841f00000003e0,0x1f8000042108418c6318217c4210842104210fc1f00000003e0,0x1f8000042108418c6318217c421085f104210841f000000001f,0x1f8000042108418c6318217fe208421083e00000007c000001f,0x1f8000042108418c6318217fe21085f104210841f000000001f,0x1f8000042108418c63184210841085f104210fc1f0000007c00,0x1f8000042108418c631842108410be2104210fc1f00000003e0,0x1f8000042108418c631842109f1085f104210841f0000007c00,0x1f8000042108418c631842109f10be2104210841f00000003e0,0x1f8000042108418c633e21084208421083e000000f8000003e0,0x1f8000042108418c633e21084208421083e000000ffc00003e0,0x1f8000042108418c633e21084208421f83e000000f8000003e0,0x1f8000042108418c633e210be208421083e000000f80000001f,0x1f8000042108418c633e210be208421083e000000f8000003e0,0x1f8000042108418c633e210be210842104210841f0000007c00,0x1f8000042108418c633e217c4208421083e00000007c000001f,0x1f8000042108418c633e217c4208421083e000000f8000003e0,0x1f8000042108418c633e217c4210842104210841f00000003e0,0x1f8000042108418c633e4210841085f104210841f0000007c00,0x1f8000042108418c633e42108410be2104210841f00000003e0,0x1f8000042108418c633e42109f1085f104210841f0000007c00,0x1f8000042108418c633e42109f10be2104210841f00000003e0,0x1f8000042108418c633ec6318c1085f104210841f0000007c00,0x1f8000042108418c633ec6318c10be2104210841f00000003e0,0x1f8000042108419f631821084208421f83e000000f8000003e0]

def r7p2 : Keys := .leaf [
0x1f8000042108419f6318210be208421083e000000f80000001f,0x1f8000042108419f6318217c4208421083e00000007c000001f,0x1f800004210841ad6b5a21084208421f83e000000f8000003e0,0x1f800004210841ad6b5a210be208421083e000000f80000001f,0x1f800004210841ad6b5a217c4208421083e00000007c000001f,0x1f800004210841ad6b7e21084208421083e000000f8000003e0,0x1f800004210841ad6b7e21084208421f83e000000f8000003e0,0x1f80000421f8410842104210841085f104210fc1f00000003e0,0x1f80000421f84108421042108410be2104210fc1f00000003e0,0x1f80000421f84108423e42108410842104210fc1f00000003e0,0x1f80000421f84108423e4210841085f104210841f00000003e0,0x1f80000421f84108423e42108410be2104210841f00000003e0,0x1f80000421f84108423e42109f10842104210841f00000003e0,0x1f80000421f841294a5242108410842104210fc1f00000003e0,0x1f80000421f841294a5242109f10842104210841f00000003e0,0x1f80000421f841294a525294a510842103e00000007c000001f,0x1f80000421f841294a7e42108410842104210841f00000003e0,0x1f80000421f841294a7e42108410842104210fc1f00000003e0,0x1f80000421f8418c631821084208421f83e00000007c000001f,0x1f80000421f8418c631821084208421f83e000000f8000003e0,0x1f80000421f8418c631821084208421f84210841f00000003e0,0x1f80000421f8418c6318210be208421083e00000007c000001f,0x1f80000421f8418c6318217c4208421083e00000007c000001f,0x1f80000421f8418c631842108410842104210fc1f00000003e0,0x1f80000421f8418c631842109f10842104210841f00000003e0,0x1f80000421f8418c633e21084208421083e00000007c000001f,0x1f80000421f8418c633e21084208421083e000000f8000003e0,0x1f80000421f8418c633e42108410842104210841f00000003e0,0x1f80000421f8418c633e42109f10842104210841f00000003e0,0x1f80000421f8418c633ec6318c10842104210841f00000003e0,0x1f80000421f841ad6b5a21084208421083e00000007c000001f,0x1f80000421f8421084208421082108420842f8821087e0f8000,0x1f80000421f84210842084211f2108420842f882108420f8000,0x1f80000421f842108420c6318c10842104210fc1f00000003e0,0x1f80000421f842108420c6318c1085f104210841f000000001f,0x1f80000421f842108420c6319f10842104210841f00000003e0,0x1f8000043f08410842104210841085f104210fc1f0000007c00,0x1f8000043f084108421042108410be2104210fc1f00000003e0,0x1f8000043f08418c631821084208421f83e000000f8000003e0,0x1f8000043f08418c6318210be208421083e000000f80000001f,0x1f8000043f08418c6318217c4208421083e00000007c000001f,0x1f90842421084108423e4210841085f104210841f0000007c00,0x1f90842421084108423e42108410be2104210841f00000003e0,0x1f9084242108418c6318210be208421083e000000f80000001f,0x1f9084242108418c6318217c4208421083e00000007c000001f,0x1f9084242108418c633e21084208421083e000000f8000003e0,0x1f90842421f84108423e42108410842104210841f00000003e0,0x1f90842421f8418c631821084208421083e00000007c000001f]

def r7p3 : Keys := .leaf [
0x1fa10844210840842108210be208421083e000000ffc000001f,0x1fa10844210840842108210be208421f84210841f0000007c00,0x1fa10844210840842108217c4208421f84210841f00000003e0,0x1fa10844210840842108217c421085f104210841f000000001f,0x1fa10844210840842108217fe208421083e00000007c000001f,0x1fa10844210840842108217fe21085f104210841f000000001f,0x1fa1084421084084213e21084208421083e000000ffc00003e0,0x1fa1084421084084213e210be208421083e000000f80000001f,0x1fa1084421084084213e210be208421083e000000f8000003e0,0x1fa1084421084084213e210be210842104210841f0000007c00,0x1fa1084421084084213e217c4208421083e00000007c000001f,0x1fa1084421084084213e217c4208421083e000000f8000003e0,0x1fa1084421084084213e217c4210842104210841f00000003e0,0x1fa1084421084084213e4210841085f104210841f0000007c00,0x1fa1084421084084213e42108410be2104210841f00000003e0,0x1fa108442108409f2108210842084210801ff800007c000001f,0x1fa108442108409f210821084208421f842108400f8000003e0,0x1fa108442108409f2108210be2084210801f0000007c000001f,0x1fa108442108409f2108210be208421083e000000f80000001f,0x1fa108442108409f2108210be2108421042108400f80000001f,0x1fa108442108409f2108217c42084210801f0000007c000001f,0x1fa108442108409f2108217c4208421083e00000007c000001f,0x1fa108442108409f2108217c4210842104210840007c000001f,0x1fa108442108409f21084210841085f1042108400f80000001f,0x1fa108442108409f210842108410be2104210840007c000001f,0x1fa108442108409f210842109f108421042108400f8000003e0,0x1fa10844210840a5294a21084208421f83e000000f8000003e0,0x1fa10844210840a5294a210be208421083e000000f80000001f,0x1fa10844210840a5294a217c4208421083e00000007c000001f,0x1fa10844210840a5297e21084208421083e000000f8000003e0,0x1fa1084421084108423e4210841085f104210841f0000007c00,0x1fa1084421084108423e42108410be2104210841f00000003e0,0x1fa108442108411f42104210841085f1042108400f80000001f,0x1fa108442108411f421042108410be2104210840007c000001f,0x1fa108442108411f421042109f108421042108400f8000003e0,0x1fa1084421f840842108217c4208421083e00000007c000001f,0x1fa1084421f84084213e21084208421083e000000f8000003e0,0x1fa1084421f8409f2108210842084210801f0000007c000001f,0x1fa1084421f84108423e42108410842104210841f00000003e0,0x1fa1084421f8411f421042108410842104210840007c000001f,0x1fa108443f0840842108210be208421083e000000f80000001f,0x1fa108443f0840842108217c4208421083e00000007c000001f,0x1fa108443f08409f2108210842084210801f0000007c000001f,0x1fa10847c8421210842021084208421f83e000000f8000003e0,0x1fa10847c84212108420210be208421083e000000f80000001f,0x1fa10847c84212108420217c4208421083e00000007c000001f,0x1fb18c6421084042108410842107c000001f0000007c000001f,0x1fb18c6421084042108410842107c000001ff800007c000001f]

def r7p4 : Keys := .leaf [
0x1fb18c6421084042108410843f08421083e000000f8000003e0,0x1fb18c642108404217c410842107c000001f0000007c000001f,0x1fb18c642108404217c421084208421083e000000f80000001f,0x1fb18c6421084042f88410842107c000001f0000007c000001f,0x1fb18c6421084042f88421084208421083e00000007c000001f,0x1fb18c64210840842108210be208421083e000000f80000001f,0x1fb18c64210840842108217c4208421083e00000007c000001f,0x1fb18c6421084084213e21084208421083e000000f8000003e0,0x1fb18c642108409f2108210842084210801f0000007c000001f,0x1fb18c642108418c6318210be208421083e000000f80000001f,0x1fb18c642108418c6318217c4208421083e00000007c000001f,0x1fb18c642108418c633e21084208421083e000000f8000003e0,0x1fb18c642108419f6318210842084210801f0000007c000001f,0x1fb18c6421f84042108410842107c000001f0000007c000001f,0x1fb18c6421f8418c631821084208421083e00000007c000001f,0x1fb18c643f084042108410842107c000001f0000007c000001f,0x1fb18c67c84212108420210be208421083e000000f80000001f,0x1fb18c67c84212108420217c4208421083e00000007c000001f,0x1fc2108210842084210821084208421f83e000000ffc00003e0,0x1fc21082108420842108210be208421083e000000ffc000001f,0x1fc21082108420842108210be208421f83e000000f80000001f,0x1fc21082108420842108210be208421f83e000000f8000003e0,0x1fc21082108420842108210be208421f84210841f0000007c00,0x1fc21082108420842108210be210842104210fc1f0000007c00,0x1fc21082108420842108217c4210842104210fc1f00000003e0,0x1fc21082108420842108217c421085f104210841f000000001f,0x1fc21082108420842108217fe21085f104210841f000000001f,0x1fc210821084209f21084210841085f1042108400f80000001f,0x1fc2108210847c84210821084208421f83e000000f8000003e0,0x1fc2108210847c842108210be208421083e000000f80000001f,0x1fc2108210847c84213e21084208421083e000000f8000003e0,0x1fc210823e8420842108210842084210801ff800007c000001f,0x1fc210823e842084210821084208421f83e000000f8000003e0,0x1fc210823e842084210821084208421f842108400f8000003e0,0x1fc210823e8420842108210be2084210801f0000007c000001f,0x1fc210823e8420842108210be208421083e000000f80000001f,0x1fc210823e8420842108210be2108421042108400f80000001f,0x1fc210823e8420842108217c4210842104210840007c000001f,0x1fc210823e842084213e210842084210801f0000007c000001f,0x1fc210823e84209f2108210842084210801f0000007c000001f,0x1fc210825294a484210821084208421f83e000000f8000003e0,0x1fc210825294a4842108210be208421083e000000f80000001f,0x1fc210825294a49f2108210842084210801f0000007c000001f,0x1fc210825294a4a5294a21084207c000001f0000007c000001f,0x1fc210825294fc84210821084208421f83e000000f8000003e0,0x1fc2108318c63042108410842107c000001ff800007c000001f,0x1fc2108318c63042108410843f07c000001f0000007c000001f,0x1fc2108318c63042108410843f08421083e000000f8000003e0]

def r7p5 : Keys := .leaf [
0x1fc2108318c6304217c410842107c000001f0000007c000001f,0x1fc2108318c6304217c421084208421083e000000f80000001f,0x1fc2108318c63042f88421084208421083e00000007c000001f,0x1fc2108318c63084210821084208421f83e000000f8000003e0,0x1fc2108318c630842108210be208421083e000000f80000001f,0x1fc2108318c6309f2108210842084210801f0000007c000001f,0x1fc2108318c67c42108410842107c000001f0000007c000001f,0x1fc210833ec63042108410842107c000001f0000007c000001f,0x1fc210833ec630842108210842084210801f0000007c000001f,0x1fc210833ec6309f2108210842084210801f0000007c000001f,0x1fc210833ec6318c6318210842084210801f0000007c000001f,0x1fc210835ad6b442108410842107c000001f0000007c000001f,0x1fc210842108410842104210841085f104210fc1f0000007c00,0x1fc2108421084108423e4210841085f104210841f0000007c00,0x1fc210842108411f42104210841085f1042108400f80000001f,0x1fc210842108411f421042109f108421042108400f8000003e0,0x1fc210842108418c631821084208421f83e000000f8000003e0,0x1fc210842108418c6318210be208421083e000000f80000001f,0x1fc210842108418c633e21084208421083e000000f8000003e0,0x1fc210842108419f6318210842084210801f0000007c000001f,0x1fc2108421f84108421042108410842104210fc1f00000003e0,0x1fc2108421f8410842104210841085f104210841f000000001f,0x1fc2108421f84108423e42108410842104210841f00000003e0,0x1fc2108421f8418c631821084208421083e00000007c000001f,0x1fc210843f084108421042108410842104210fc00f8000003e0,0x1fc210843f08410842104210841085f1042108400f80000001f,0x1fc210843f084108423e421084108421042108400f8000003e0,0x1fc210843f08418c6318210842084210801f0000007c000001f,0x1fc21087d0842084210821084208421f83e000000f8000003e0,0x1fc21087d08420842108210be208421083e000000f80000001f,0x1fc21087d08420842108217c4208421083e00000007c000001f,0x1fc21087d8c63042108410842107c000001f0000007c000001f,0x1ffc000421084108421042108410842104210fc00ffc00003e0,0x1ffc00042108410842104210841085f1042108400ffc000001f,0x1ffc00042108410842104210841085f104210fc00f80000001f,0x1ffc00042108410842104210841085f104210fc00f8000003e0,0x1ffc00042108410842104210841085f104210fc1f0000007c00,0x1ffc00042108410842104210841085f104210fc210842007c00,0x1ffc00042108410842104210841085f1084210821087e007c00,0x1ffc000421084108421042108410be2104210fc0007c000001f,0x1ffc000421084108421042108410be2104210fc00f8000003e0,0x1ffc000421084108421042108410be2104210fc1f00000003e0,0x1ffc000421084108421042108410be2104210fc2108420003e0,0x1ffc000421084108421042108410be21084210821087e0003e0,0x1ffc000421084108421042108410be210842f8821084200001f,0x1ffc000421084108421042108410bff104210840007c000001f,0x1ffc000421084108421042108410bff10842f8821084200001f,0x1ffc000421084108421042109f2108420842f88210842007c00]

def r7p6 : Keys := .leaf [
0x1ffc000421084108421042109f210842085f1082108420003e0,0x1ffc000421084108423e421084108421042108400ffc00003e0,0x1ffc000421084108423e42108410842104210fc00f8000003e0,0x1ffc000421084108423e4210841085f1042108400f80000001f,0x1ffc000421084108423e4210841085f1042108400f8000003e0,0x1ffc000421084108423e4210841085f104210841f0000007c00,0x1ffc000421084108423e4210841085f10842108210842007c00,0x1ffc000421084108423e42108410be2104210840007c000001f,0x1ffc000421084108423e42108410be21042108400f8000003e0,0x1ffc000421084108423e42108410be2104210841f00000003e0,0x1ffc000421084108423e42108410be2108421082108420003e0,0x1ffc000421084108423e42109f108421042108400f8000003e0,0x1ffc00042108411f421042108410842104210fc00f8000003e0,0x1ffc00042108411f42104210841085f1042108400f80000001f,0x1ffc00042108411f421042108410be2104210840007c000001f,0x1ffc00042108411f421042109f108421042108400f8000003e0,0x1ffc0004210841294a5242108410842104210fc00f8000003e0,0x1ffc0004210841294a524210841085f1042108400f80000001f,0x1ffc0004210841294a5242108410be2104210840007c000001f,0x1ffc0004210841294a5242109f108421042108400f8000003e0,0x1ffc0004210841294a525294a5108421001f0000007c000001f,0x1ffc0004210841294a7e421084108421042108400f8000003e0,0x1ffc0004210841294a7e42108410842104210fc00f8000003e0,0x1ffc00042108418c6318210842084210801ff800007c000001f,0x1ffc00042108418c631821084208421f801f0000007c000001f,0x1ffc00042108418c631821084208421f83e000000f8000003e0,0x1ffc00042108418c631821084208421f842108400f8000003e0,0x1ffc00042108418c6318210be2084210801f0000007c000001f,0x1ffc00042108418c6318210be208421083e000000f80000001f,0x1ffc00042108418c6318210be2108421042108400f80000001f,0x1ffc00042108418c6318217c42084210801f0000007c000001f,0x1ffc00042108418c6318217c4208421083e00000007c000001f,0x1ffc00042108418c6318217c4210842104210840007c000001f,0x1ffc00042108418c631842108410842104210fc00f8000003e0,0x1ffc00042108418c63184210841085f1042108400f80000001f,0x1ffc00042108418c631842108410be2104210840007c000001f,0x1ffc00042108418c631842109f108421042108400f8000003e0,0x1ffc00042108418c633e210842084210801f0000007c000001f,0x1ffc00042108418c633e21084208421083e000000f8000003e0,0x1ffc00042108418c633e421084108421042108400f8000003e0,0x1ffc00042108418c633e42109f108421042108400f8000003e0,0x1ffc00042108418c633ec6318c108421042108400f8000003e0,0x1ffc00042108419f6318210842084210801f0000007c000001f,0x1ffc0004210841ad6b5a210842084210801f0000007c000001f,0x1ffc000421f84108421042108410842104210fc0007c000001f,0x1ffc000421f84108421042108410842104210fc00f8000003e0,0x1ffc000421f84108421042108410842104210fc1f00000003e0,0x1ffc000421f84108421042108410842104210fc2108420003e0]

def r7p7 : Keys := .leaf [
0x1ffc000421f8410842104210841085f104210840007c000001f,0x1ffc000421f84108421042108410be2104210840007c000001f,0x1ffc000421f84108421042109f21084208421082108420003e0,0x1ffc000421f84108423e42108410842104210840007c000001f,0x1ffc000421f84108423e421084108421042108400f8000003e0,0x1ffc000421f84108423e42108410842104210841f00000003e0,0x1ffc000421f841294a5242108410842104210840007c000001f,0x1ffc000421f8418c6318210842084210801f0000007c000001f,0x1ffc000421f8418c631821084208421083e00000007c000001f,0x1ffc000421f8418c631842108410842104210840007c000001f,0x1ffc000421f842108420842108210842084210821087e0003e0,0x1ffc000421f8421084208421082108420842f8821084200001f,0x1ffc000421f84210842084211f21084208421082108420003e0,0x1ffc000421f842108420c6318c10842104210840007c000001f,0x1ffc00043f084108421042108410842104210fc00f8000003e0,0x1ffc00043f08410842104210841085f1042108400f80000001f,0x1ffc00043f084108421042108410be2104210840007c000001f,0x1ffc00043f08418c6318210842084210801f0000007c000001f,0x1ffc84242108410842104210841085f1042108400f80000001f,0x1ffc842421084108421042108410be2104210840007c000001f,0x1ffc842421084108423e421084108421042108400f8000003e0,0x1ffc84242108418c6318210842084210801f0000007c000001f,0x1ffc84242108419f6318210842084210801f0000007c000001f,0x1ffc842421f84108421042108410842104210840007c000001f,0x1ffd0844210840842108210842084210801f0000007c000001f,0x1ffd0844210840842108210842084210801ff800007c000001f,0x1ffd084421084084210821084208421f842108400f8000003e0,0x1ffd0844210840842108210be2084210801f0000007c000001f,0x1ffd0844210840842108210be208421083e000000f80000001f,0x1ffd0844210840842108210be2108421042108400f80000001f,0x1ffd0844210840842108217c42084210801f0000007c000001f,0x1ffd0844210840842108217c4208421083e00000007c000001f,0x1ffd0844210840842108217c4210842104210840007c000001f,0x1ffd084421084084213e210842084210801f0000007c000001f,0x1ffd084421084084213e21084208421083e000000f8000003e0,0x1ffd084421084084213e421084108421042108400f8000003e0,0x1ffd08442108409f2108210842084210801f0000007c000001f,0x1ffd0844210840a5294a210842084210801f0000007c000001f,0x1ffd084421084108423e421084108421042108400f8000003e0,0x1ffd08442108411f42104210841085f1042108400f80000001f,0x1ffd08442108411f421042108410be2104210840007c000001f,0x1ffd08442108411f421042109f108421042108400f8000003e0,0x1ffd084421f840842108210842084210801f0000007c000001f,0x1ffd08443f0840842108210842084210801f0000007c000001f,0x1ffd0847fe000210842042108410842104210fc00f8000003e0,0x1ffd0847fe00021084204210841085f1042108400f80000001f,0x1ffd0847fe000210842042108410be2104210840007c000001f,0x1ffd0847fe000210842042109f108421042108400f8000003e0]

def r7p8 : Keys := .leaf [
0x1ffd0847fe4212108420210842084210801f0000007c000001f,0x1ffd8c6421084042108410842107c000001f0000007c000001f,0x1ffd8c64210840842108210842084210801f0000007c000001f,0x1ffd8c642108409f2108210842084210801f0000007c000001f,0x1ffd8c642108418c6318210842084210801f0000007c000001f,0x1ffd8c642108419f6318210842084210801f0000007c000001f,0x1ffd8c67fe0002108420210842084210801f0000007c000001f,0x1ffd8c67fe4212108420210842084210801f0000007c000001f,0x1ffe1082108420842108210842084210801f0000007c000001f,0x1ffe1082108420842108210842084210801ff800007c000001f,0x1ffe108210842084210821084208421f801f0000007c000001f,0x1ffe108210842084210821084208421f83e000000f8000003e0,0x1ffe108210842084210821084208421f842108400f8000003e0,0x1ffe1082108420842108210be2084210801f0000007c000001f,0x1ffe1082108420842108210be208421083e000000f80000001f,0x1ffe1082108420842108210be2108421042108400f80000001f,0x1ffe1082108420842108217c4210842104210840007c000001f,0x1ffe108210847c842108210842084210801f0000007c000001f,0x1ffe10823e8420842108210842084210801f0000007c000001f,0x1ffe10825294a4842108210842084210801f0000007c000001f,0x1ffe108318c63042108410842107c000001f0000007c000001f,0x1ffe108318c630842108210842084210801f0000007c000001f,0x1ffe108421084108421042108410842104210fc00f8000003e0,0x1ffe10842108410842104210841085f1042108400f80000001f,0x1ffe108421084108423e421084108421042108400f8000003e0,0x1ffe10842108418c6318210842084210801f0000007c000001f,0x1ffe108421f84108421042108410842104210840007c000001f,0x1ffe10843f084108421042108410842104210fc00f8000003e0,0x1ffe10843f08410842104210841085f1042108400f80000001f,0x1ffe10843f08418c6318210842084210801f0000007c000001f,0x1ffe1087fe000108421042108410842104210fc00f8000003e0,0x1ffe1087fe00010842104210841085f1042108400f80000001f,0x1ffe1087fe000108421042108410be2104210840007c000001f,0x1ffe1087fe00018c6318210842084210801f0000007c000001f,0x1ffe1087fe8420842108210842084210801f0000007c000001f]

def r7 : Keys := (.branch 0x1fb18c6421084042108410843f08421083e000000f8000003e0 (.branch 0x1f8000042108419f6318210be208421083e000000f80000001f (.branch 0x1f8000042108411f421042108410be2104210fc1f00000003e0 r7p0 r7p1) (.branch 0x1fa10844210840842108210be208421083e000000ffc000001f r7p2 r7p3)) (.branch 0x1ffc000421084108421042109f210842085f1082108420003e0 (.branch 0x1fc2108318c6304217c410842107c000001f0000007c000001f r7p4 r7p5) (.branch 0x1ffc000421f8410842104210841085f104210840007c000001f r7p6 (.branch 0x1ffd0847fe4212108420210842084210801f0000007c000001f r7p7 r7p8))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p0 : r7p0.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p1 : r7p1.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p2 : r7p2.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p3 : r7p3.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p4 : r7p4.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p5 : r7p5.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p6 : r7p6.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p7 : r7p7.all (checkFast 6 a6) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr7p8 : r7p8.all (checkFast 6 a6) = true := by decide +kernel

theorem badR7 : Rejects 7 r7 :=
  verifyFast 6 a6 r7 badA6 (by
    unfold r7
    simp only [allBranch, Bool.and_true, goodr7p0, goodr7p1, goodr7p2, goodr7p3, goodr7p4, goodr7p5, goodr7p6, goodr7p7, goodr7p8])

def a7p0 : Keys := .leaf [
0x3f00000842108210847c9f2108210be2084210801f003,0x3f00000842108210847c9f2108217c420842108000f83,0x3f00000842108318c6304217c410843f07c000001f000,0x3f00000842108318c63042f88410843f07c0000000f80,0x3f00000842108318c67c4217c410842107c000001f000,0x3f00000842108318c67c42f88410842107c0000000f80,0x3f0000084210833ec6304217c4108421003e00000007e,0x3f0000084210833ec63042f8841084210001f0000007e,0x3f00000843f08318c63042108410843f07c0000000f80,0x3f00000843f08318c67c42108410842107c0000000f80,0x3f0000087e1082108420842108210be208421f801f002,0x3f0000087e108318c63042108410843f003e000000f82,0x3f0000087e108318c6304217c4108421003e00000007e,0x3f21084842108210847c4217c410842107c000001f001,0x3f21084842108210847c42f88410842107c0000000f81,0x3f42108842108108427c4217c410842107c000001f000,0x3f42108842108108427c42f88410842107c0000000f80,0x3f4210884210813e42104217c4108421003e00000007c,0x3f4210884210813e421042f8841084210001f0000007c,0x3f4210887e10810842104217c4108421003e00000007e,0x3f6318c8421080842f882108420f8000003e00000007c,0x3f6318c842108085f1082108420f80000001f0000007c,0x3f6318c87e1080842108210842007c000001f0000007e,0x3f8421042108410842104217c410843f07c000001f000,0x3f8421042108413e42104217c4108421003e00000007d,0x3f8421047d08410842104217c4108421003e00000007c,0x3f842106318c6084210821087e0f8000003e000000f80,0x3f842106318c60842f882108420f8000003e00000007c,0x3f8421067d8c60842108210842007c000001f0000007c,0x3ff80008421082108420842108210be208421f801f000,0x3ff80008421082108420842108217c4208421f8000f80,0x3ff8000842108210842084213e210be2084210801f001,0x3ff8000842108210842084213e217c420842108000f81,0x3ff8000842108210847c842108210be2084210801f000,0x3ff8000842108210847c842108217c420842108000f80,0x3ff8000842108318c63042108410843f003e000000f80,0x3ff8000842108318c6304217c4108421003e00000007c,0x3ff8000842108318c63042f8841084210001f0000007c,0x3ff8000842108318c67c421084108421003e000000f80,0x3ff8000843f08210842084210821084208421f8000f80,0x3ff8000843f08210842084213e2108420842108000f81,0x3ff8000843f08210847c8421082108420842108000f80,0x3ff8000843f08318c6304210841084210001f0000007c,0x3ff908484210821084204217c4108421003e00000007d,0x3ff9084842108210842042f8841084210001f0000007d,0x3ff9084842108210847c421084108421003e000000f81,0x3ffa10884210810842104217c4108421003e00000007c,0x3ffa108842108108421042f8841084210001f0000007c]

def a7p1 : Keys := .leaf [
0x3ffa108842108108427c421084108421003e000000f80,0x3ffb18c8421080842108210842007c000001f0000007c,0x3ffc210421084108421042108410843f003e000000f80,0x3ffc21042108410842104217c4108421003e00000007c,0x3ffc2106318c60842108210842007c000001f0000007c,0x7e0000108421042108410842104217c410843f07c000001ff80,0x7e00001084210421084108421042f884210be208421f83e0000,0x7e00001084210421084108421042ffc410843f07c0000000f80,0x7e00001084210421084108421042ffc4210be208421f83e0000,0x7e00001084210421084108427c4217c410842107c000001ff81,0x7e00001084210421084108427c4217c410843f07c000001f001,0x7e00001084210421084108427c42f88410843f07c0000000f81,0x7e00001084210421084108427c42f884210be208421083e0001,0x7e00001084210421084108427c42ffc410842107c0000000f81,0x7e00001084210421084108427c42ffc4210be208421083e0001,0x7e0000108421042108413e42104217c4108421003ff0000007f,0x7e0000108421042108413e42104217c410843f07c000001f001,0x7e0000108421042108413e42104217c410843f084210801f003,0x7e0000108421042108413e421042f88410843f07c0000000f81,0x7e0000108421042108413e421042f88410843f0842108000f83,0x7e0000108421042108413e421042f884210be2084210800007f,0x7e0000108421042108413e421042ffc41084210001f0000007f,0x7e0000108421042108413e421042ffc4210be2084210800007f,0x7e0000108421042108413e421084213e210be2084210801f003,0x7e0000108421042108413e421084213e217c420842108000f83,0x7e0000108421042108414a52944217c410843f07c000001f001,0x7e0000108421042108414a529442f88410843f07c0000000f81,0x7e0000108421042108414a52fc4217c410842107c000001f001,0x7e0000108421042108414a52fc4217c410843f07c000001f001,0x7e0000108421042108414a52fc42f88410842107c0000000f81,0x7e0000108421042108414a52fc42f88410843f07c0000000f81,0x7e0000108421042108f90842104217c410842107c000001ff80,0x7e0000108421042108f90842104217c410843f07c000001f000,0x7e0000108421042108f908421042f88410843f07c0000000f80,0x7e0000108421042108f908421042f884210be208421083e0000,0x7e0000108421042108f908421042ffc410842107c0000000f80,0x7e0000108421042108f908421042ffc4210be208421083e0000,0x7e0000108421042108f908427c4217c410842107c000001f000,0x7e0000108421042108f908427c42f88410842107c0000000f80,0x7e0000108421042108f93e4210421084108421003ff00000f83,0x7e0000108421042108f93e42104217c4108421003e00000007f,0x7e0000108421042108f93e42104217c4108421003e000000f83,0x7e0000108421042108f93e42104217c410842107c000001f001,0x7e0000108421042108f93e42104217c4210842084210801f003,0x7e0000108421042108f93e421042f8841084210001f0000007f,0x7e0000108421042108f93e421042f884108421003e000000f83,0x7e0000108421042108f93e421042f88410842107c0000000f81,0x7e0000108421042108f93e421042f8842108420842108000f83]

def a7p2 : Keys := .leaf [
0x7e0000108421042108f93e4210842108210be2084210801f002,0x7e0000108421042108f93e4210842108217c420842108000f82,0x7e0000108421042108f94a52944217c410842107c000001f001,0x7e0000108421042108f94a529442f88410842107c0000000f81,0x7e0000108421047d08410842104217c4108421003ff0000007e,0x7e0000108421047d08410842104217c410843f07c000001f000,0x7e0000108421047d08410842104217c410843f084210801f002,0x7e0000108421047d084108421042f88410843f07c0000000f80,0x7e0000108421047d084108421042f88410843f0842108000f82,0x7e0000108421047d084108421042f884210be2084210800007e,0x7e0000108421047d084108421042ffc41084210001f0000007e,0x7e0000108421047d084108421042ffc4210be2084210800007e,0x7e0000108421047d084108427c4217c410842107c000001f000,0x7e0000108421047d084108427c42f88410842107c0000000f80,0x7e0000108421047d084108427c842108210be2084210801f002,0x7e0000108421047d084108427c842108217c420842108000f82,0x7e0000108421047d08413e421042108410843f003e000000f82,0x7e0000108421047d08413e42104217c4108421003e00000007e,0x7e0000108421047d08413e421042f8841084210001f0000007e,0x7e000010842104a529490842104217c410843f07c000001f000,0x7e000010842104a5294908421042f88410843f07c0000000f80,0x7e000010842104a5294908427c4217c410842107c000001f000,0x7e000010842104a5294908427c42f88410842107c0000000f80,0x7e000010842104a529493e421042108410843f003e000000f83,0x7e000010842104a529493e42104217c4108421003e00000007f,0x7e000010842104a529493e421042f8841084210001f0000007f,0x7e000010842104a529494a52944217c40f8000003e00000007c,0x7e000010842104a529494a529442f8840f80000001f0000007c,0x7e000010842104a529494a52fc4210840f8000003e000000f81,0x7e000010842104a529f90842104217c410842107c000001f000,0x7e000010842104a529f90842104217c410843f07c000001f000,0x7e000010842104a529f908421042f88410842107c0000000f80,0x7e000010842104a529f908421042f88410843f07c0000000f80,0x7e000010842104a529f93e4210421084108421003e000000f83,0x7e000010842104a529f94a52944210840f8000003e000000f80,0x7e000010842104a529f94a52fc4210840f8000003e000000f80,0x7e000010842106318c6084210821087e0f8000003ff00000f80,0x7e000010842106318c60842f882108420f8000003ff0000007c,0x7e000010842106318c60842f8821087e0f8000003e00000007c,0x7e000010842106318c60842f8821087e0f8000003e000000f80,0x7e000010842106318c60842f8821087e10842107c000001f000,0x7e000010842106318c60842f8842108410843f07c000001f000,0x7e000010842106318c6085f10821087e0f80000001f0000007c,0x7e000010842106318c6085f10821087e0f8000003e000000f80,0x7e000010842106318c6085f10821087e10842107c0000000f80,0x7e000010842106318c6085f10842108410843f07c0000000f80,0x7e000010842106318c6085f1084217c410842107c000000007c,0x7e000010842106318c6085ff882108420f80000001f0000007c]

def a7p3 : Keys := .leaf [
0x7e000010842106318c6085ff884217c410842107c000000007c,0x7e000010842106318c610842104217c410843f07c000001f000,0x7e000010842106318c6108421042f88410843f07c0000000f80,0x7e000010842106318c6108427c4217c410842107c000001f000,0x7e000010842106318c6108427c42f88410842107c0000000f80,0x7e000010842106318c613e42104217c4108421003e00000007e,0x7e000010842106318c613e421042f8841084210001f0000007e,0x7e000010842106318c621084204217c410843f07c000001f001,0x7e000010842106318c6210842042f88410843f07c0000000f81,0x7e000010842106318cf88421082108420f8000003e000000f80,0x7e000010842106318cf88421082108420f8000003ff00000f80,0x7e000010842106318cf884210821087e0f8000003e000000f80,0x7e000010842106318cf8842f882108420f8000003e00000007c,0x7e000010842106318cf8842f882108420f8000003e000000f80,0x7e000010842106318cf8842f8842108410842107c000001f000,0x7e000010842106318cf885f1082108420f80000001f0000007c,0x7e000010842106318cf885f1082108420f8000003e000000f80,0x7e000010842106318cf885f10842108410842107c0000000f80,0x7e000010842106318cf90842104217c410842107c000001f000,0x7e000010842106318cf908421042f88410842107c0000000f80,0x7e000010842106318cf908427c4217c410842107c000001f000,0x7e000010842106318cf908427c42f88410842107c0000000f80,0x7e000010842106318cf93e4210421084108421003e000000f82,0x7e000010842106318cfa10847c4217c410842107c000001f001,0x7e000010842106318cfa10847c42f88410842107c0000000f81,0x7e000010842106318cfb18c6304217c410842107c000001f000,0x7e000010842106318cfb18c63042f88410842107c0000000f80,0x7e0000108421067d8c60842108210842007fe00001f0000007e,0x7e0000108421067d8c6084210821087e0f8000003e000000f80,0x7e0000108421067d8c6084210821087e108421003e000000f82,0x7e0000108421067d8c60842f88210842007c000001f0000007e,0x7e0000108421067d8c60842f882108420f8000003e00000007c,0x7e0000108421067d8c60842f88421084108421003e00000007e,0x7e0000108421067d8c6085f108210842007c000001f0000007e,0x7e0000108421067d8c6085f1082108420f80000001f0000007c,0x7e0000108421067d8c6085f1084210841084210001f0000007e,0x7e0000108421067d8c610842104217c4108421003e00000007e,0x7e0000108421067d8c6108421042f8841084210001f0000007e,0x7e0000108421067d8c6108427c421084108421003e000000f82,0x7e0000108421067d8c6318c6304217c4108421003e00000007e,0x7e0000108421067d8c6318c63042f8841084210001f0000007e,0x7e0000108421067d8c6318c67c421084108421003e000000f82,0x7e000010842106b5ad6884210821087e0f8000003e000000f80,0x7e000010842106b5ad68842f882108420f8000003e00000007c,0x7e000010842106b5ad6885f1082108420f80000001f0000007c,0x7e000010842106b5adf88421082108420f8000003e000000f80,0x7e000010842106b5adf884210821087e0f8000003e000000f80,0x7e00001087e1042108410842104217c410843f07c0000000f80]

def a7p4 : Keys := .leaf [
0x7e00001087e10421084108421042f88410843f07c0000000f80,0x7e00001087e10421084108427c42108410843f07c0000000f81,0x7e00001087e10421084108427c4217c410842107c0000000f81,0x7e00001087e10421084108427c42f88410842107c0000000f81,0x7e00001087e1042108413e421042f8841084210001f0000007f,0x7e00001087e1042108413e421084213e2108420842108000f83,0x7e00001087e1042108414a529442108410843f07c0000000f81,0x7e00001087e1042108414a52fc42108410842107c0000000f81,0x7e00001087e1042108414a52fc42108410843f07c0000000f81,0x7e00001087e1042108f908421042108410843f07c0000000f80,0x7e00001087e1042108f90842104217c410842107c0000000f80,0x7e00001087e1042108f908421042f88410842107c0000000f80,0x7e00001087e1042108f908427c42108410842107c0000000f80,0x7e00001087e1042108f93e4210421084108421003e000000f83,0x7e00001087e1042108f93e42108421082108420842108000f82,0x7e00001087e1042108f94a529442108410842107c0000000f81,0x7e00001087e1047d084108421042f8841084210001f0000007e,0x7e00001087e104a5294908421042108410843f07c0000000f80,0x7e00001087e104a5294908427c42108410842107c0000000f80,0x7e00001087e104a529494a52944210840f80000001f0000007c,0x7e00001087e104a529f908421042108410842107c0000000f80,0x7e00001087e104a529f908421042108410843f07c0000000f80,0x7e00001087e106318c6084210821087e0f80000001f0000007c,0x7e00001087e106318c6084210821087e0f8000003e000000f80,0x7e00001087e106318c6084210821087e10842107c0000000f80,0x7e00001087e106318c60842f882108420f80000001f0000007c,0x7e00001087e106318c6085f1082108420f80000001f0000007c,0x7e00001087e106318c6108421042108410843f07c0000000f80,0x7e00001087e106318c6108427c42108410842107c0000000f80,0x7e00001087e106318c613e42104210841084210001f0000007e,0x7e00001087e106318c6210842042108410843f07c0000000f81,0x7e00001087e106318cf88421082108420f80000001f0000007c,0x7e00001087e106318cf88421082108420f8000003e000000f80,0x7e00001087e106318cf908421042108410842107c0000000f80,0x7e00001087e106318cf908427c42108410842107c0000000f80,0x7e00001087e106318cfa10847c42108410842107c0000000f81,0x7e00001087e106318cfb18c63042108410842107c0000000f80,0x7e00001087e1067d8c60842108210842007c000001f0000007e,0x7e00001087e1067d8c6318c6304210841084210001f0000007e,0x7e00001087e106b5ad688421082108420f80000001f0000007c,0x7e00001087e108421082108420842108210be208421f83e0000,0x7e00001087e10842108210842084213e210be208421083e0001,0x7e00001087e10842108210847c842108210be208421083e0000,0x7e00001087e10842108318c63042108410843f07c0000000f80,0x7e00001087e10842108318c6304217c410842107c000000007c,0x7e00001087e10842108318c67c42108410842107c0000000f80,0x7e000010fc210421084108421042108410843f003ff00000f82,0x7e000010fc21042108410842104217c4108421003ff0000007e]

def a7p5 : Keys := .leaf [
0x7e000010fc21042108410842104217c410843f003e00000007e,0x7e000010fc21042108410842104217c410843f003e000000f82,0x7e000010fc21042108410842104217c410843f07c000001f000,0x7e000010fc21042108410842104217c410843f084210801f002,0x7e000010fc21042108410842104217c421084208421f801f002,0x7e000010fc210421084108421042f88410843f07c0000000f80,0x7e000010fc210421084108421042f88421084208421f8000f82,0x7e000010fc210421084108421042f884210be2084210800007e,0x7e000010fc210421084108421042ffc4210be2084210800007e,0x7e000010fc21042108413e421042108410843f003e000000f83,0x7e000010fc21042108413e42104217c4108421003e00000007f,0x7e000010fc21042108413e421042f8841084210001f0000007f,0x7e000010fc21042108f908421042108410843f003e000000f82,0x7e000010fc21042108f90842104217c4108421003e00000007e,0x7e000010fc21042108f908427c421084108421003e000000f82,0x7e000010fc21047d084108421042108410843f003e000000f82,0x7e000010fc21047d08410842104217c4108421003e00000007e,0x7e000010fc21047d084108421042f8841084210001f0000007e,0x7e000010fc2104a5294908421042108410843f003e000000f82,0x7e000010fc2104a529490842104217c4108421003e00000007e,0x7e000010fc2104a529494a5294421084007c000001f0000007e,0x7e000010fc2104a529f908421042108410843f003e000000f82,0x7e000010fc2106318c60842108210842007fe00001f0000007e,0x7e000010fc2106318c6084210821087e007c000001f0000007e,0x7e000010fc2106318c6084210821087e0f8000003e000000f80,0x7e000010fc2106318c6084210821087e108421003e000000f82,0x7e000010fc2106318c60842f88210842007c000001f0000007e,0x7e000010fc2106318c60842f882108420f8000003e00000007c,0x7e000010fc2106318c60842f88421084108421003e00000007e,0x7e000010fc2106318c6085f1082108420f80000001f0000007c,0x7e000010fc2106318c6085f1084210841084210001f0000007e,0x7e000010fc2106318c6108421042108410843f003e000000f82,0x7e000010fc2106318c610842104217c4108421003e00000007e,0x7e000010fc2106318cf8842108210842007c000001f0000007e,0x7e000010fc21067d8c60842108210842007c000001f0000007e,0x7e000010fc2106b5ad68842108210842007c000001f0000007e,0x7e000010fc2108421082108420842108210be208421f801f002,0x7e000010fc210842108210847c842108210be2084210801f002,0x7e000010fc210842108318c63042108410843f003e000000f82,0x7e000010fc210842108318c6304217c4108421003e00000007e,0x7e000010fc210842108318c67c421084108421003e000000f82,0x7e000010fc210843f08210842084210821084208421f8000f82,0x7e000010fc210843f082108420842108210be2084210800007e,0x7e000010fc210843f08210847c8421082108420842108000f82,0x7e000010fc210843f08318c6304210841084210001f0000007e,0x7e421090842104210840842f882108420f8000003ff0000007d,0x7e421090842104210840842f8821087e10842107c000001f001,0x7e42109084210421084085f10821087e10842107c0000000f81]

def a7p6 : Keys := .leaf [
0x7e42109084210421084085f1084217c410842107c000000007d,0x7e42109084210421084085ff882108420f80000001f0000007d,0x7e42109084210421084085ff884217c410842107c000000007d,0x7e42109084210421084108427c4217c410842107c000001f001,0x7e42109084210421084108427c42f88410842107c0000000f81,0x7e4210908421042108413e42104217c4108421003e00000007d,0x7e4210908421042108413e421042f8841084210001f0000007d,0x7e4210908421042108f88421082108420f8000003ff00000f81,0x7e4210908421042108f8842f882108420f8000003e00000007d,0x7e4210908421042108f8842f882108420f8000003e000000f81,0x7e4210908421042108f8842f8842108410842107c000001f001,0x7e4210908421042108f885f1082108420f80000001f0000007d,0x7e4210908421042108f885f1082108420f8000003e000000f81,0x7e4210908421042108f885f10842108410842107c0000000f81,0x7e4210908421042108f90842104217c410842107c000001f000,0x7e4210908421042108f908421042f88410842107c0000000f80,0x7e4210908421042108f93e4210421084108421003e000000f81,0x7e4210908421047d0840842f882108420f8000003e00000007d,0x7e4210908421047d084085f1082108420f80000001f0000007d,0x7e4210908421047d08410842104217c4108421003e00000007e,0x7e4210908421047d084108421042f8841084210001f0000007e,0x7e421090842104a5294884210821087e0f8000003e000000f81,0x7e421090842104a52948842f882108420f8000003e00000007d,0x7e421090842104a5294885f1082108420f80000001f0000007d,0x7e421090842104a529f88421082108420f8000003e000000f81,0x7e421090842106318c60842f882108420f8000003e00000007c,0x7e421090842106318c6085f1082108420f80000001f0000007c,0x7e421090842106318cf88421082108420f8000003e000000f80,0x7e4210908421067d8c60842108210842007c000001f0000007e,0x7e42109087e10421084085f1082108420f80000001f0000007d,0x7e42109087e10421084108427c42108410842107c0000000f81,0x7e42109087e1042108413e42104210841084210001f0000007d,0x7e42109087e1042108f88421082108420f8000003e000000f81,0x7e42109087e1042108f908421042108410842107c0000000f80,0x7e42109087e106318c608421082108420f80000001f0000007c,0x7e421090fc2104210840842f882108420f8000003e00000007d,0x7e421090fc210421084085f1082108420f80000001f0000007d,0x7e421090fc21042108410842104217c4108421003e00000007e,0x7e421090fc2106318c60842108210842007c000001f0000007e,0x7e42109f0000084210821084204217c410843f07c000001f003,0x7e42109f00000842108210842042f88410843f07c0000000f83,0x7e42109f00000842108210847c4217c410842107c000001f003,0x7e42109f00000842108210847c42f88410842107c0000000f83,0x7e842110842102108420842f882108420f8000003ff0000007c,0x7e842110842102108420842f8821087e10842107c000001f000,0x7e84211084210210842085f10821087e10842107c0000000f80,0x7e84211084210210842085f1084217c410842107c000000007c,0x7e84211084210210842085ff882108420f80000001f0000007c]

def a7p7 : Keys := .leaf [
0x7e84211084210210842085ff884217c410842107c000000007c,0x7e8421108421021084f88421082108420f8000003ff00000f80,0x7e8421108421021084f8842f882108420f8000003e00000007c,0x7e8421108421021084f8842f882108420f8000003e000000f80,0x7e8421108421021084f8842f8842108410842107c000001f000,0x7e8421108421021084f885f1082108420f80000001f0000007c,0x7e8421108421021084f885f1082108420f8000003e000000f80,0x7e8421108421021084f885f10842108410842107c0000000f80,0x7e8421108421021084f90842104217c410842107c000001f000,0x7e8421108421021084f908421042f88410842107c0000000f80,0x7e8421108421027c8420842108210842007fe00001f0000007c,0x7e8421108421027c842084210821087e108421003e000000f80,0x7e8421108421027c8420842f88210842007c000001f0000007c,0x7e8421108421027c8420842f882108420f8000003e00000007c,0x7e8421108421027c8420842f88421084108421003e00000007c,0x7e8421108421027c842085f108210842007c000001f0000007c,0x7e8421108421027c842085f1082108420f80000001f0000007c,0x7e8421108421027c842085f1084210841084210001f0000007c,0x7e8421108421027c84210842104217c4108421003e00000007c,0x7e8421108421027c842108421042f8841084210001f0000007c,0x7e8421108421027c842108427c421084108421003e000000f80,0x7e84211084210294a52884210821087e0f8000003e000000f80,0x7e84211084210294a528842f882108420f8000003e00000007c,0x7e84211084210294a52885f1082108420f80000001f0000007c,0x7e84211084210294a5f88421082108420f8000003e000000f80,0x7e8421108421042108f90842104217c410842107c000001f000,0x7e8421108421042108f908421042f88410842107c0000000f80,0x7e8421108421042108f93e4210421084108421003e000000f83,0x7e8421108421047d08410842104217c4108421003e00000007c,0x7e8421108421047d084108421042f8841084210001f0000007c,0x7e8421108421047d084108427c421084108421003e000000f80,0x7e842110842106318cf88421082108420f8000003e000000f81,0x7e8421108421067d8c60842108210842007c000001f0000007f,0x7e84211087e10210842085f1082108420f80000001f0000007c,0x7e84211087e1021084f88421082108420f8000003e000000f80,0x7e84211087e1027c8420842108210842007c000001f0000007c,0x7e84211087e1042108f908421042108410842107c0000000f80,0x7e84211087e1047d08410842104210841084210001f0000007c,0x7e842110fc2102108420842108210842007fe00001f0000007e,0x7e842110fc210210842084210821087e108421003e000000f82,0x7e842110fc2102108420842f88210842007c000001f0000007e,0x7e842110fc2102108420842f882108420f8000003e00000007c,0x7e842110fc2102108420842f88421084108421003e00000007e,0x7e842110fc210210842085f1082108420f80000001f0000007c,0x7e842110fc210210842085f1084210841084210001f0000007e,0x7e842110fc21021084f8842108210842007c000001f0000007e,0x7e842110fc21027c8420842108210842007c000001f0000007c,0x7e842110fc210294a528842108210842007c000001f0000007f]

def a7p8 : Keys := .leaf [
0x7e842110fc21084210810842104217c4108421003e00000007e,0x7e842110fc210842108108427c421084108421003e000000f82,0x7e84211f0000084210810842104217c410843f07c000001f002,0x7e84211f00000842108108421042f88410843f07c0000000f82,0x7e84211f21084842108084210821087e0f8000003e000000f80,0x7e84211f210848421080842f882108420f8000003e00000007c,0x7e84211f21084842108085f1082108420f80000001f0000007c,0x7e84211f2108487e1080842108210842007c000001f0000007e,0x7ec631908421010842104210841f0000007c000001f0000007c,0x7ec631908421010842104210841f0000007fe00001f0000007c,0x7ec631908421010842104210fc2108420f8000003e000000f80,0x7ec63190842101085f104210841f0000007c000001f0000007c,0x7ec63190842101085f108421082108420f8000003e00000007c,0x7ec631908421010be2104210841f0000007c000001f0000007c,0x7ec631908421010be2108421082108420f80000001f0000007c,0x7ec63190842102108420842f882108420f8000003e00000007c,0x7ec6319084210210842085f1082108420f80000001f0000007c,0x7ec631908421021084f88421082108420f8000003e000000f80,0x7ec631908421027c8420842108210842007c000001f0000007c,0x7ec631908421042108f88421082108420f8000003e000000f81,0x7ec631908421047d0840842108210842007c000001f0000007d,0x7ec63190842106318c60842f882108420f8000003e00000007c,0x7ec63190842106318c6085f1082108420f80000001f0000007c,0x7ec63190842106318cf88421082108420f8000003e000000f80,0x7ec631908421067d8c60842108210842007c000001f0000007c,0x7ec6319087e1010842104210841f0000007c000001f0000007c,0x7ec6319087e106318c608421082108420f80000001f0000007c,0x7ec63190fc21010842104210841f0000007c000001f0000007c,0x7ec63190fc2102108420842108210842007c000001f0000007e,0x7ec63190fc2106318c60842108210842007c000001f0000007e,0x7ec63190fc2108421080842108210842007c000001f0000007e,0x7ec6319f00000842108084210821087e0f8000003e000000f82,0x7ec6319f000008421080842f882108420f8000003e00000007e,0x7ec6319f00000842108085f1082108420f80000001f0000007e,0x7ec6319f210848421080842f882108420f8000003e00000007c,0x7ec6319f21084842108085f1082108420f80000001f0000007c,0x7ec6319f2108487e1080842108210842007c000001f0000007e,0x7ec6319f421088421080842f882108420f8000003e00000007d,0x7ec6319f42108842108085f1082108420f80000001f0000007d,0x7f08420842108210842084210821087e0f8000003ff00000f80,0x7f084208421082108420842f882108420f8000003ff0000007c,0x7f084208421082108420842f8821087e0f8000003e00000007c,0x7f084208421082108420842f8821087e0f8000003e000000f80,0x7f084208421082108420842f8821087e10842107c000001f000,0x7f084208421082108420842f8842108410843f07c000001f000,0x7f08420842108210842085f10842108410843f07c0000000f80,0x7f08420842108210842085f1084217c410842107c000000007c,0x7f08420842108210842085ff884217c410842107c000000007c]

def a7p9 : Keys := .leaf [
0x7f0842084210821084f884210821087e0f8000003e000000f81,0x7f0842084210821084f8842f882108420f8000003e00000007d,0x7f0842084210827c8420842108210842007fe00001f0000007d,0x7f0842084210827c842084210821087e0f8000003e000000f81,0x7f0842084210827c842084210821087e108421003e000000f81,0x7f0842084210827c8420842f88210842007c000001f0000007d,0x7f0842084210827c8420842f882108420f8000003e00000007d,0x7f0842084210827c8420842f88421084108421003e00000007d,0x7f0842084210827c842085f1084210841084210001f0000007d,0x7f0842084210827c84210842104217c4108421003e00000007c,0x7f08420842108294a52884210821087e0f8000003e000000f81,0x7f08420842108294a528842f882108420f8000003e00000007d,0x7f08420842108294a5f884210821087e0f8000003e000000f81,0x7f0842084211f210842084210821087e0f8000003e000000f80,0x7f0842084211f2108420842f882108420f8000003e00000007c,0x7f0842084211f21084f88421082108420f8000003e000000f80,0x7f0842084211f27c8420842108210842007c000001f0000007d,0x7f084208fa1082108420842108210842007fe00001f0000007c,0x7f084208fa108210842084210821087e0f8000003e000000f80,0x7f084208fa108210842084210821087e108421003e000000f80,0x7f084208fa1082108420842f88210842007c000001f0000007c,0x7f084208fa1082108420842f882108420f8000003e00000007c,0x7f084208fa1082108420842f88421084108421003e00000007c,0x7f084208fa108210842085f1084210841084210001f0000007c,0x7f084208fa10821084f8842108210842007c000001f0000007c,0x7f084208fa10827c8420842108210842007c000001f0000007c,0x7f084208fa108294a528842108210842007c000001f0000007d,0x7f084208fa10842108410842104217c4108421003e00000007d,0x7f0842094a529210842084210821087e0f8000003e000000f80,0x7f0842094a5292108420842f882108420f8000003e00000007c,0x7f0842094a52927c8420842108210842007c000001f0000007c,0x7f0842094a529294a5288421081f0000007c000001f0000007c,0x7f0842094a53f210842084210821087e0f8000003e000000f80,0x7f08420c6318c10842104210841f0000007fe00001f0000007c,0x7f08420c6318c10842104210fc1f0000007c000001f0000007c,0x7f08420c6318c10842104210fc2108420f8000003e000000f80,0x7f08420c6318c1085f104210841f0000007c000001f0000007c,0x7f08420c6318c1085f108421082108420f8000003e00000007c,0x7f08420c6318c10be2108421082108420f80000001f0000007c,0x7f08420c6318c210842084210821087e0f8000003e000000f80,0x7f08420c6318c2108420842f882108420f8000003e00000007c,0x7f08420c6318c27c8420842108210842007c000001f0000007c,0x7f08420c6318c421084084210821087e0f8000003e000000f81,0x7f08420c6318c4210840842f882108420f8000003e00000007d,0x7f08420c6319f10842104210841f0000007c000001f0000007c,0x7f08420cfb18c10842104210841f0000007c000001f0000007c,0x7f08420cfb18c2108420842108210842007c000001f0000007c,0x7f08420cfb18c47d0840842108210842007c000001f0000007d]

def a7p10 : Keys := .leaf [
0x7f08420cfb18c6318c60842108210842007c000001f0000007c,0x7f08420d6b5ad10842104210841f0000007c000001f0000007c,0x7f0842108421042108410842104217c410843f07c000001f000,0x7f08421084210421084108427c4217c410842107c000001f001,0x7f0842108421042108413e42104217c4108421003e00000007d,0x7f0842108421042108f90842104217c410842107c000001f000,0x7f0842108421042108f93e4210421084108421003e000000f81,0x7f0842108421047d08410842104217c4108421003e00000007c,0x7f0842108421047d084108427c421084108421003e000000f80,0x7f084210842106318c6084210821087e0f8000003e000000f80,0x7f084210842106318c60842f882108420f8000003e00000007c,0x7f084210842106318cf88421082108420f8000003e000000f80,0x7f0842108421067d8c60842108210842007c000001f0000007c,0x7f08421087e10421084108421042108410843f07c0000000f80,0x7f08421087e1042108410842104217c410842107c000000007c,0x7f08421087e10421084108427c42108410842107c0000000f81,0x7f08421087e1042108f908421042108410842107c0000000f80,0x7f08421087e106318c608421082108420f80000001f0000007c,0x7f084210fc210421084108421042108410843f003e000000f80,0x7f084210fc21042108410842104217c4108421003e00000007c,0x7f084210fc210421084108427c421084108421003e000000f81,0x7f084210fc21042108f9084210421084108421003e000000f80,0x7f084210fc2106318c60842108210842007c000001f0000007c,0x7f08421f0000042108410842104217c410843f07c000001f002,0x7f08421f00000421084108421042f88410843f07c0000000f82,0x7f08421f000006318c6084210821087e0f8000003e000000f82,0x7f08421f000006318c60842f882108420f8000003e00000007e,0x7f08421f000006318c6085f1082108420f80000001f0000007e,0x7f08421f42108210842084210821087e0f8000003e000000f80,0x7f08421f421082108420842f882108420f8000003e00000007c,0x7f08421f42108210842085f1082108420f80000001f0000007c,0x7f08421f4210827c8420842108210842007c000001f0000007f,0x7f08421f6318c10842104210841f0000007c000001f0000007c,0x7ff0001084210421084108421042108410843f003ff00000f80,0x7ff000108421042108410842104217c4108421003ff0000007c,0x7ff000108421042108410842104217c410843f003e00000007c,0x7ff000108421042108410842104217c410843f003e000000f80,0x7ff000108421042108410842104217c410843f07c000001f000,0x7ff000108421042108410842104217c410843f084210801f000,0x7ff000108421042108410842104217c421084208421f801f000,0x7ff0001084210421084108421042f88410843f0001f0000007c,0x7ff0001084210421084108421042f88410843f003e000000f80,0x7ff0001084210421084108421042f88410843f07c0000000f80,0x7ff0001084210421084108421042f88410843f0842108000f80,0x7ff0001084210421084108421042f88421084208421f8000f80,0x7ff0001084210421084108421042f884210be2084210800007c,0x7ff0001084210421084108421042ffc41084210001f0000007c,0x7ff0001084210421084108421042ffc4210be2084210800007c]

def a7p11 : Keys := .leaf [
0x7ff0001084210421084108427c421084108421003ff00000f81,0x7ff0001084210421084108427c42108410843f003e000000f81,0x7ff0001084210421084108427c4217c4108421003e00000007d,0x7ff0001084210421084108427c4217c4108421003e000000f81,0x7ff0001084210421084108427c4217c410842107c000001f001,0x7ff0001084210421084108427c4217c4210842084210801f001,0x7ff0001084210421084108427c42f8841084210001f0000007d,0x7ff0001084210421084108427c42f884108421003e000000f81,0x7ff0001084210421084108427c42f88410842107c0000000f81,0x7ff0001084210421084108427c42f8842108420842108000f81,0x7ff0001084210421084108427c842108210be2084210801f000,0x7ff0001084210421084108427c842108217c420842108000f80,0x7ff000108421042108413e421042108410843f003e000000f81,0x7ff000108421042108413e42104217c4108421003e00000007d,0x7ff000108421042108413e421042f8841084210001f0000007d,0x7ff000108421042108414a529442108410843f003e000000f81,0x7ff000108421042108414a52944217c4108421003e00000007d,0x7ff000108421042108414a529442f8841084210001f0000007d,0x7ff000108421042108414a52fc421084108421003e000000f81,0x7ff000108421042108414a52fc42108410843f003e000000f81,0x7ff000108421042108f9084210421084108421003ff00000f80,0x7ff000108421042108f908421042108410843f003e000000f80,0x7ff000108421042108f90842104217c4108421003e00000007c,0x7ff000108421042108f90842104217c4108421003e000000f80,0x7ff000108421042108f90842104217c410842107c000001f000,0x7ff000108421042108f90842104217c4210842084210801f000,0x7ff000108421042108f908421042f8841084210001f0000007c,0x7ff000108421042108f908421042f884108421003e000000f80,0x7ff000108421042108f908421042f88410842107c0000000f80,0x7ff000108421042108f908421042f8842108420842108000f80,0x7ff000108421042108f908427c421084108421003e000000f80,0x7ff000108421042108f93e4210421084108421003e000000f81,0x7ff000108421042108f94a5294421084108421003e000000f81,0x7ff000108421042108fa108420842108210be2084210801f001,0x7ff000108421042108fa108420842108217c420842108000f81,0x7ff000108421047d084108421042108410843f003e000000f80,0x7ff000108421047d08410842104217c4108421003e00000007c,0x7ff000108421047d084108421042f8841084210001f0000007c,0x7ff000108421047d084108427c421084108421003e000000f80,0x7ff00010842104a5294908421042108410843f003e000000f80,0x7ff00010842104a529490842104217c4108421003e00000007c,0x7ff00010842104a5294908421042f8841084210001f0000007c,0x7ff00010842104a5294908427c421084108421003e000000f80,0x7ff00010842104a529494a5294421084007c000001f0000007c,0x7ff00010842104a529f9084210421084108421003e000000f80,0x7ff00010842104a529f908421042108410843f003e000000f80,0x7ff00010842106318c60842108210842007fe00001f0000007c,0x7ff00010842106318c6084210821087e007c000001f0000007c]

def a7p12 : Keys := .leaf [
0x7ff00010842106318c6084210821087e0f8000003e000000f80,0x7ff00010842106318c6084210821087e108421003e000000f80,0x7ff00010842106318c60842f88210842007c000001f0000007c,0x7ff00010842106318c60842f882108420f8000003e00000007c,0x7ff00010842106318c60842f88421084108421003e00000007c,0x7ff00010842106318c6085f108210842007c000001f0000007c,0x7ff00010842106318c6085f1082108420f80000001f0000007c,0x7ff00010842106318c6085f1084210841084210001f0000007c,0x7ff00010842106318c6108421042108410843f003e000000f80,0x7ff00010842106318c610842104217c4108421003e00000007c,0x7ff00010842106318c6108421042f8841084210001f0000007c,0x7ff00010842106318c6108427c421084108421003e000000f80,0x7ff00010842106318c6210842042108410843f003e000000f81,0x7ff00010842106318c621084204217c4108421003e00000007d,0x7ff00010842106318c6210842042f8841084210001f0000007d,0x7ff00010842106318cf8842108210842007c000001f0000007c,0x7ff00010842106318cf88421082108420f8000003e000000f80,0x7ff00010842106318cf9084210421084108421003e000000f80,0x7ff00010842106318cf908427c421084108421003e000000f80,0x7ff00010842106318cfa10847c421084108421003e000000f81,0x7ff00010842106318cfb18c630421084108421003e000000f80,0x7ff000108421067d8c60842108210842007c000001f0000007c,0x7ff00010842106b5ad68842108210842007c000001f0000007c,0x7ff0001087e10421084108421042108410843f0001f0000007c,0x7ff0001087e10421084108421042108410843f003e000000f80,0x7ff0001087e10421084108421042108410843f07c0000000f80,0x7ff0001087e10421084108421042108410843f0842108000f80,0x7ff0001087e1042108410842104217c41084210001f0000007c,0x7ff0001087e10421084108421042f8841084210001f0000007c,0x7ff0001087e10421084108427c4210841084210001f0000007d,0x7ff0001087e10421084108427c421084108421003e000000f81,0x7ff0001087e10421084108427c42108410842107c0000000f81,0x7ff0001087e10421084108427c8421082108420842108000f80,0x7ff0001087e1042108414a52944210841084210001f0000007d,0x7ff0001087e1042108f90842104210841084210001f0000007c,0x7ff0001087e1042108f9084210421084108421003e000000f80,0x7ff0001087e1042108f908421042108410842107c0000000f80,0x7ff0001087e1042108fa1084208421082108420842108000f81,0x7ff0001087e104a529490842104210841084210001f0000007c,0x7ff0001087e106318c60842108210842007c000001f0000007c,0x7ff0001087e106318c608421082108420f80000001f0000007c,0x7ff0001087e106318c610842104210841084210001f0000007c,0x7ff0001087e106318c621084204210841084210001f0000007d,0x7ff0001087e10842108210842084210821084208421f8000f80,0x7ff0001087e108421082108420842108210be2084210800007c,0x7ff0001087e10842108210842084213e2108420842108000f81,0x7ff0001087e10842108210847c8421082108420842108000f80,0x7ff0001087e10842108318c6304210841084210001f0000007c]

def a7p13 : Keys := .leaf [
0x7ff00010fc210421084108421042108410843f003e000000f80,0x7ff00010fc21042108410842104217c4108421003e00000007c,0x7ff00010fc210421084108421042f8841084210001f0000007c,0x7ff00010fc2106318c60842108210842007c000001f0000007c,0x7ff0001f000008421082108420842108210be208421f801f002,0x7ff0001f000008421082108420842108217c4208421f8000f82,0x7ff0001f00000842108210847c842108210be2084210801f002,0x7ff0001f00000842108210847c842108217c420842108000f82,0x7ff0001f00000842108318c63042108410843f003e000000f82,0x7ff0001f00000842108318c6304217c4108421003e00000007e,0x7ff0001f00000842108318c63042f8841084210001f0000007e,0x7ff0001f00000842108318c67c421084108421003e000000f82,0x7ff0001f00000843f08210842084210821084208421f8000f82,0x7ff0001f00000843f08210847c8421082108420842108000f82,0x7ff0001f00000843f08318c6304210841084210001f0000007e,0x7ff21090842104210840842108210842007fe00001f0000007d,0x7ff2109084210421084084210821087e108421003e000000f81,0x7ff21090842104210840842f88210842007c000001f0000007d,0x7ff21090842104210840842f882108420f8000003e00000007d,0x7ff21090842104210840842f88421084108421003e00000007d,0x7ff2109084210421084085f108210842007c000001f0000007d,0x7ff2109084210421084085f1082108420f80000001f0000007d,0x7ff2109084210421084085f1084210841084210001f0000007d,0x7ff210908421042108410842104217c4108421003e00000007c,0x7ff2109084210421084108421042f8841084210001f0000007c,0x7ff2109084210421084108427c421084108421003e000000f81,0x7ff210908421042108f8842108210842007c000001f0000007d,0x7ff210908421042108f88421082108420f8000003e000000f81,0x7ff210908421042108f9084210421084108421003e000000f80,0x7ff210908421047d0840842108210842007c000001f0000007d,0x7ff21090842104a52948842108210842007c000001f0000007d,0x7ff21090842106318c60842108210842007c000001f0000007c,0x7ff2109087e104210840842108210842007c000001f0000007d,0x7ff2109087e1042108410842104210841084210001f0000007c,0x7ff21090fc2104210840842108210842007c000001f0000007d,0x7ff2109f421088421080842108210842007c000001f0000007f,0x7ff2109f6318c8421080842108210842007c000001f0000007e,0x7ff2109ff8000842108210842042108410843f003e000000f81,0x7ff2109ff800084210821084204217c4108421003e00000007d,0x7ff2109ff8000842108210842042f8841084210001f0000007d,0x7ff2109ff8000842108210847c421084108421003e000000f81,0x7ff42110842102108420842108210842007c000001f0000007c,0x7ff42110842102108420842108210842007fe00001f0000007c,0x7ff4211084210210842084210821087e108421003e000000f80,0x7ff42110842102108420842f88210842007c000001f0000007c,0x7ff42110842102108420842f882108420f8000003e00000007c,0x7ff42110842102108420842f88421084108421003e00000007c,0x7ff4211084210210842085f108210842007c000001f0000007c]

def a7p14 : Keys := .leaf [
0x7ff4211084210210842085f1082108420f80000001f0000007c,0x7ff4211084210210842085f1084210841084210001f0000007c,0x7ff421108421021084f8842108210842007c000001f0000007c,0x7ff421108421021084f88421082108420f8000003e000000f80,0x7ff421108421021084f9084210421084108421003e000000f80,0x7ff421108421027c8420842108210842007c000001f0000007c,0x7ff4211084210294a528842108210842007c000001f0000007c,0x7ff421108421042108410842104217c4108421003e00000007d,0x7ff4211084210421084108421042f8841084210001f0000007d,0x7ff421108421042108f9084210421084108421003e000000f80,0x7ff421108421047d08410842104217c4108421003e00000007c,0x7ff421108421047d084108421042f8841084210001f0000007c,0x7ff421108421047d084108427c421084108421003e000000f80,0x7ff421108421067d8c60842108210842007c000001f0000007d,0x7ff4211087e102108420842108210842007c000001f0000007c,0x7ff4211087e1042108410842104210841084210001f0000007d,0x7ff42110fc2102108420842108210842007c000001f0000007c,0x7ff4211f210848421080842108210842007c000001f0000007e,0x7ff4211f4210884210810842104217c4108421003e00000007e,0x7ff4211f42108842108108421042f8841084210001f0000007e,0x7ff4211f42108842108108427c421084108421003e000000f82,0x7ff4211f842102108420842108210842007c000001f0000007e,0x7ff4211ff8000842108108421042108410843f003e000000f80,0x7ff4211ff800084210810842104217c4108421003e00000007c,0x7ff4211ff8000842108108421042f8841084210001f0000007c,0x7ff4211ff8000842108108427c421084108421003e000000f80,0x7ff4211ff90848421080842108210842007c000001f0000007c,0x7ff631908421010842104210841f0000007c000001f0000007c,0x7ff63190842102108420842108210842007c000001f0000007c,0x7ff631908421027c8420842108210842007c000001f0000007c,0x7ff631908421047d0840842108210842007c000001f0000007d,0x7ff63190842106318c60842108210842007c000001f0000007c,0x7ff6319f210848421080842108210842007c000001f0000007e,0x7ff6319f421088421080842108210842007c000001f0000007f,0x7ff6319f6318c8421080842108210842007c000001f0000007e,0x7ff6319ff80008421080842108210842007c000001f0000007c,0x7ff6319ffa1088421080842108210842007c000001f0000007d,0x7ff84208421082108420842108210842007c000001f0000007c,0x7ff84208421082108420842108210842007fe00001f0000007c,0x7ff8420842108210842084210821087e007c000001f0000007c,0x7ff8420842108210842084210821087e0f8000003e000000f80,0x7ff8420842108210842084210821087e108421003e000000f80,0x7ff84208421082108420842f88210842007c000001f0000007c,0x7ff84208421082108420842f882108420f8000003e00000007c,0x7ff84208421082108420842f88421084108421003e00000007c,0x7ff8420842108210842085f1084210841084210001f0000007c,0x7ff842084210821084f8842108210842007c000001f0000007d,0x7ff842084210827c8420842108210842007c000001f0000007d]

def a7p15 : Keys := .leaf [
0x7ff8420842108294a528842108210842007c000001f0000007d,0x7ff842084211f2108420842108210842007c000001f0000007c,0x7ff84208fa1082108420842108210842007c000001f0000007c,0x7ff842094a5292108420842108210842007c000001f0000007c,0x7ff8420c6318c10842104210841f0000007c000001f0000007c,0x7ff8420c6318c2108420842108210842007c000001f0000007c,0x7ff8420c6318c4210840842108210842007c000001f0000007d,0x7ff8421084210421084108421042108410843f003e000000f80,0x7ff842108421042108410842104217c4108421003e00000007c,0x7ff8421084210421084108427c421084108421003e000000f81,0x7ff842108421042108f9084210421084108421003e000000f80,0x7ff84210842106318c60842108210842007c000001f0000007c,0x7ff8421087e1042108410842104210841084210001f0000007c,0x7ff84210fc210421084108421042108410843f003e000000f80,0x7ff84210fc21042108410842104217c4108421003e00000007c,0x7ff84210fc2106318c60842108210842007c000001f0000007c,0x7ff8421f421082108420842108210842007c000001f0000007e,0x7ff8421f84210421084108421042108410843f003e000000f82,0x7ff8421f8421042108410842104217c4108421003e00000007e,0x7ff8421f842106318c60842108210842007c000001f0000007e,0x7ff8421ff8000421084108421042108410843f003e000000f80,0x7ff8421ff800042108410842104217c4108421003e00000007c,0x7ff8421ff8000421084108421042f8841084210001f0000007c,0x7ff8421ff80006318c60842108210842007c000001f0000007c,0x7ff8421ff90844210840842108210842007c000001f0000007d,0x7ff8421ffa1082108420842108210842007c000001f0000007c]

def a7 : Keys := (.branch 0x1fa108443f08421084204210841085f1042108400f80000001f (.branch 0x1f80000421f84108421042108410be2104210fc1f00000003e0 (.branch 0x1f80000421084108423e4f90842108420842f88210842007c00 (.branch 0xffe842210842042109f108421042108400f8000003e0 a7p0 a7p1) (.branch 0x1f8000042108418c6318217fe21085f104210841f000000001f a7p2 a7p3)) (.branch 0x1f908424210841084210217c421085f104210841f000000001f (.branch 0x1f8000043f08410842104210841085f104210fc00f80000001f a7p4 a7p5) (.branch 0x1fa10844210840842108217fe21085f104210841f000000001f a7p6 a7p7))) (.branch 0x1ffc00042108418c631821084208421f83e000000f8000003e0 (.branch 0x1fc210833ec6318c6318210842084210801f0000007c000001f (.branch 0x1fc2108210842084213e21084208421f83e000000f8000003e0 a7p8 a7p9) (.branch 0x1ffc000421084108421042109f108421042108400ffc00003e0 a7p10 a7p11)) (.branch 0x1ffd0844210840842108217c4208421083e00000007c000001f (.branch 0x1ffc00043f084108421042108410842104210fc00f8000003e0 a7p12 a7p13) (.branch 0x1ffe1082108420a5294a210842084210801f0000007c000001f a7p14 a7p15))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p0 : a7p0.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p1 : a7p1.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p2 : a7p2.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p3 : a7p3.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p4 : a7p4.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p5 : a7p5.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p6 : a7p6.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p7 : a7p7.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p8 : a7p8.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p9 : a7p9.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p10 : a7p10.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p11 : a7p11.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p12 : a7p12.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p13 : a7p13.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p14 : a7p14.all (checkAlias r7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda7p15 : a7p15.all (checkAlias r7) = true := by decide +kernel

theorem badA7 : RejectsAlias 7 a7 :=
  verifyAliases 7 r7 a7 badR7 (by
    unfold a7
    simp only [allBranch, Bool.and_true, gooda7p0, gooda7p1, gooda7p2, gooda7p3, gooda7p4, gooda7p5, gooda7p6, gooda7p7, gooda7p8, gooda7p9, gooda7p10, gooda7p11, gooda7p12, gooda7p13, gooda7p14, gooda7p15])

def r8p0 : Keys := .leaf [
0x1f8000042108410842104210841085f104210fc1f0000007c00,0x1f80000421084108421042108410be2104210fc1f00000003e0,0x1f80000421084108423e4210841085f104210841f0000007c00,0x1f80000421084108423e42108410be2104210841f00000003e0,0x1f8000042108418c631821084208421f83e000000f8000003e0,0x1f8000042108418c6318210be208421083e000000f80000001f,0x1f8000042108418c6318217c4208421083e00000007c000001f,0x1f8000042108418c633e21084208421083e000000f8000003e0,0x1f80000421f84108421042108410842104210fc1f00000003e0,0x1f80000421f84108423e42108410842104210841f00000003e0,0x1f80000421f8418c631821084208421083e00000007c000001f,0x1fa10844210840842108210be208421083e000000f80000001f,0x1fa10844210840842108217c4208421083e00000007c000001f,0x1fa1084421084084213e21084208421083e000000f8000003e0,0x1fa108442108409f2108210842084210801f0000007c000001f,0x1fb18c6421084042108410842107c000001f0000007c000001f,0x1fc2108210842084210821084208421f83e000000f8000003e0,0x1fc21082108420842108210be208421083e000000f80000001f,0x1fc210823e8420842108210842084210801f0000007c000001f,0x1fc2108318c63042108410842107c000001f0000007c000001f,0x1ffc000421084108421042108410842104210fc00f8000003e0,0x1ffc00042108410842104210841085f1042108400f80000001f,0x1ffc000421084108421042108410be2104210840007c000001f,0x1ffc000421084108423e421084108421042108400f8000003e0,0x1ffc00042108418c6318210842084210801f0000007c000001f,0x1ffc000421f84108421042108410842104210840007c000001f,0x1ffd0844210840842108210842084210801f0000007c000001f,0x1ffe1082108420842108210842084210801f0000007c000001f,0x3f00000842108210842084210821084208421f83e000000ffc00003e0,0x3f000008421082108420842108210be208421083e000000ffc000001f,0x3f000008421082108420842108210be208421f83e000000f80000001f,0x3f000008421082108420842108210be208421f83e000000f8000003e0,0x3f000008421082108420842108210be208421f84210841f0000007c00,0x3f000008421082108420842108210be210842104210fc1f0000007c00,0x3f000008421082108420842108217c4208421f83e00000007c000001f,0x3f000008421082108420842108217c4208421f83e000000f8000003e0,0x3f000008421082108420842108217c4208421f84210841f00000003e0,0x3f000008421082108420842108217c4210842104210fc1f00000003e0,0x3f000008421082108420842108217c421085f104210841f000000001f,0x3f000008421082108420842108217fe208421083e00000007c000001f,0x3f000008421082108420842108217fe21085f104210841f000000001f,0x3f00000842108210842084213e4210841085f104210841f0000007c00,0x3f00000842108210842084213e42108410be2104210841f00000003e0,0x3f00000842108210847c84210821084208421083e000000ffc00003e0,0x3f00000842108210847c84210821084208421f83e000000f8000003e0,0x3f00000842108210847c842108210be208421083e000000f80000001f,0x3f00000842108210847c842108210be208421083e000000f8000003e0,0x3f00000842108210847c842108210be210842104210841f0000007c00]

def r8p1 : Keys := .leaf [
0x3f00000842108210847c842108217c4208421083e00000007c000001f,0x3f00000842108210847c842108217c4208421083e000000f8000003e0,0x3f00000842108210847c842108217c4210842104210841f00000003e0,0x3f00000842108210847c84213e21084208421083e000000f8000003e0,0x3f0000084210823e842084210821084208421f83e000000f8000003e0,0x3f0000084210823e8420842108210be208421083e000000f80000001f,0x3f0000084210823e8420842108217c4208421083e00000007c000001f,0x3f0000084210823e842084213e21084208421083e000000f8000003e0,0x3f0000084210825294a484210821084208421f83e000000f8000003e0,0x3f0000084210825294a4842108210be208421083e000000f80000001f,0x3f0000084210825294a4842108217c4208421083e00000007c000001f,0x3f0000084210825294a484213e21084208421083e000000f8000003e0,0x3f0000084210825294a4a5294a21084207c000001f0000007c000001f,0x3f0000084210825294fc84210821084208421083e000000f8000003e0,0x3f0000084210825294fc84210821084208421f83e000000f8000003e0,0x3f00000842108318c63042108410842107c000001ff800007c000001f,0x3f00000842108318c63042108410843f07c000001f0000007c000001f,0x3f00000842108318c63042108410843f08421083e000000f8000003e0,0x3f00000842108318c6304217c410842107c000001f0000007c000001f,0x3f00000842108318c6304217c421084208421083e000000f80000001f,0x3f00000842108318c63042f88410842107c000001f0000007c000001f,0x3f00000842108318c63042f88421084208421083e00000007c000001f,0x3f00000842108318c63084210821084208421f83e000000f8000003e0,0x3f00000842108318c630842108210be208421083e000000f80000001f,0x3f00000842108318c630842108217c4208421083e00000007c000001f,0x3f00000842108318c63084213e21084208421083e000000f8000003e0,0x3f00000842108318c67c42108410842107c000001f0000007c000001f,0x3f00000842108318c67c84210821084208421083e000000f8000003e0,0x3f00000842108318c67c84213e21084208421083e000000f8000003e0,0x3f00000842108318c67d8c631821084208421083e000000f8000003e0,0x3f0000084210833ec63042108410842107c000001f0000007c000001f,0x3f0000084210835ad6b442108410842107c000001f0000007c000001f,0x3f00000843f08210842084210821084208421f83e00000007c000001f,0x3f00000843f08210842084210821084208421f83e000000f8000003e0,0x3f00000843f08210842084210821084208421f84210841f00000003e0,0x3f00000843f082108420842108210be208421083e00000007c000001f,0x3f00000843f082108420842108217c4208421083e00000007c000001f,0x3f00000843f08210842084213e42108410842104210841f00000003e0,0x3f00000843f08210847c84210821084208421083e00000007c000001f,0x3f00000843f08210847c84210821084208421083e000000f8000003e0,0x3f00000843f0825294a484210821084208421083e00000007c000001f,0x3f00000843f08318c63042108410842107c000001f0000007c000001f,0x3f00000843f08318c63084210821084208421083e00000007c000001f,0x3f00000843f08421084108421042108410842104210fc1f00000003e0,0x3f00000843f0842108410842104210841085f104210841f000000001f,0x3f00000843f08421084108423e42108410842104210841f00000003e0,0x3f00000843f0842108418c631821084208421083e00000007c000001f,0x3f0000087e108210842084210821084208421f83e000000f8000003e0]

def r8p2 : Keys := .leaf [
0x3f0000087e1082108420842108210be208421083e000000f80000001f,0x3f0000087e1082108420842108217c4208421083e00000007c000001f,0x3f0000087e108318c63042108410842107c000001f0000007c000001f,0x3f210848421082108420842108210be208421083e000000f80000001f,0x3f210848421082108420842108217c4208421083e00000007c000001f,0x3f21084842108210847c84210821084208421083e000000f8000003e0,0x3f21084842108318c63042108410842107c000001f0000007c000001f,0x3f21084843f08210842084210821084208421083e00000007c000001f,0x3f42108842108108421042108410842107c000001ff800007c000001f,0x3f42108842108108421042108410843f08421083e000000f8000003e0,0x3f4210884210810842104217c410842107c000001f0000007c000001f,0x3f4210884210810842104217c421084208421083e000000f80000001f,0x3f42108842108108421042f88410842107c000001f0000007c000001f,0x3f42108842108108421042f88421084208421083e00000007c000001f,0x3f42108842108108427c42108410842107c000001f0000007c000001f,0x3f42108842108108427c84210821084208421083e000000f8000003e0,0x3f4210884210813e421042108410842107c000001f0000007c000001f,0x3f4210884210813e4210842108210842084210801f0000007c000001f,0x3f4210884210814a529442108410842107c000001f0000007c000001f,0x3f42108842108210847c84210821084208421083e000000f8000003e0,0x3f4210884210823e8420842108210842084210801f0000007c000001f,0x3f42108843f08108421042108410842107c000001f0000007c000001f,0x3f4210887e108108421042108410842107c000001f0000007c000001f,0x3f42108f90842421084042108410842107c000001f0000007c000001f,0x3f6318c842108108421042108410842107c000001f0000007c000001f,0x3f6318c842108318c63042108410842107c000001f0000007c000001f,0x3f6318cf90842421084042108410842107c000001f0000007c000001f,0x3f84210421084108421042108410842107c000001ff800007c000001f,0x3f84210421084108421042108410843f07c000001f0000007c000001f,0x3f84210421084108421042108410843f08421083e000000f8000003e0,0x3f8421042108410842104217c410842107c000001f0000007c000001f,0x3f8421042108410842104217c421084208421083e000000f80000001f,0x3f84210421084108421042f88421084208421083e00000007c000001f,0x3f8421042108413e4210842108210842084210801f0000007c000001f,0x3f8421042108f908421042108410842107c000001f0000007c000001f,0x3f8421047d084108421042108410842107c000001f0000007c000001f,0x3f842104a5294908421042108410842107c000001f0000007c000001f,0x3f842106318c6108421042108410842107c000001f0000007c000001f,0x3f84210842108210842084210821084208421f83e000000f8000003e0,0x3f842108421082108420842108210be208421083e000000f80000001f,0x3f84210842108210847c84210821084208421083e000000f8000003e0,0x3f8421084210823e8420842108210842084210801f0000007c000001f,0x3f84210842108318c63042108410842107c000001f0000007c000001f,0x3f84210843f08210842084210821084208421083e00000007c000001f,0x3f8421087e1082108420842108210842084210801f0000007c000001f,0x3f84210fa1084108421042108410842107c000001f0000007c000001f,0x3ff80008421082108420842108210842084210801ff800007c000001f,0x3ff8000842108210842084210821084208421f801f0000007c000001f]

def r8p3 : Keys := .leaf [
0x3ff8000842108210842084210821084208421f83e000000f8000003e0,0x3ff8000842108210842084210821084208421f842108400f8000003e0,0x3ff80008421082108420842108210be2084210801f0000007c000001f,0x3ff80008421082108420842108210be208421083e000000f80000001f,0x3ff80008421082108420842108210be2108421042108400f80000001f,0x3ff80008421082108420842108217c42084210801f0000007c000001f,0x3ff80008421082108420842108217c4208421083e00000007c000001f,0x3ff80008421082108420842108217c4210842104210840007c000001f,0x3ff8000842108210842084213e421084108421042108400f8000003e0,0x3ff8000842108210847c842108210842084210801f0000007c000001f,0x3ff8000842108210847c84210821084208421083e000000f8000003e0,0x3ff800084210823e8420842108210842084210801f0000007c000001f,0x3ff800084210825294a4842108210842084210801f0000007c000001f,0x3ff8000842108318c63042108410842107c000001f0000007c000001f,0x3ff8000842108318c630842108210842084210801f0000007c000001f,0x3ff8000843f082108420842108210842084210801f0000007c000001f,0x3ff8000843f08210842084210821084208421083e00000007c000001f,0x3ff8000843f08421084108421042108410842104210840007c000001f,0x3ff800087e1082108420842108210842084210801f0000007c000001f,0x3ff90848421082108420842108210842084210801f0000007c000001f,0x3ffa108842108108421042108410842107c000001f0000007c000001f,0x3ffa10884210823e8420842108210842084210801f0000007c000001f,0x3ffa108ffc0004210840842108210842084210801f0000007c000001f,0x3ffc210421084108421042108410842107c000001f0000007c000001f,0x3ffc2108421082108420842108210842084210801f0000007c000001f,0x3ffc21087e1082108420842108210842084210801f0000007c000001f,0x3ffc210ffc0002108420842108210842084210801f0000007c000001f]

def r8 : Keys := (.branch 0x3f0000087e1082108420842108210be208421083e000000f80000001f (.branch 0x3f00000842108210847c842108217c4208421083e00000007c000001f r8p0 r8p1) (.branch 0x3ff8000842108210842084210821084208421f83e000000f8000003e0 r8p2 r8p3))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p0 : r8p0.all (checkFast 7 a7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p1 : r8p1.all (checkFast 7 a7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p2 : r8p2.all (checkFast 7 a7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr8p3 : r8p3.all (checkFast 7 a7) = true := by decide +kernel

theorem badR8 : Rejects 8 r8 :=
  verifyFast 7 a7 r8 badA7 (by
    unfold r8
    simp only [allBranch, Bool.and_true, goodr8p0, goodr8p1, goodr8p2, goodr8p3])

def a8p0 : Keys := .leaf [
0x7e0000108421042108410842104217c410843f07c000001f000,0x7e00001084210421084108421042f88410843f07c0000000f80,0x7e00001084210421084108427c4217c410842107c000001f001,0x7e00001084210421084108427c42f88410842107c0000000f81,0x7e0000108421042108413e42104217c4108421003e00000007f,0x7e0000108421042108413e421042f8841084210001f0000007f,0x7e0000108421042108f90842104217c410842107c000001f000,0x7e0000108421042108f908421042f88410842107c0000000f80,0x7e0000108421042108f93e4210421084108421003e000000f83,0x7e0000108421047d08410842104217c4108421003e00000007e,0x7e0000108421047d084108421042f8841084210001f0000007e,0x7e000010842106318c6084210821087e0f8000003e000000f80,0x7e000010842106318c60842f882108420f8000003e00000007c,0x7e000010842106318c6085f1082108420f80000001f0000007c,0x7e000010842106318cf88421082108420f8000003e000000f80,0x7e0000108421067d8c60842108210842007c000001f0000007e,0x7e00001087e10421084108421042108410843f07c0000000f80,0x7e00001087e10421084108427c42108410842107c0000000f81,0x7e00001087e1042108f908421042108410842107c0000000f80,0x7e00001087e106318c608421082108420f80000001f0000007c,0x7e000010fc210421084108421042108410843f003e000000f82,0x7e000010fc21042108410842104217c4108421003e00000007e,0x7e000010fc2106318c60842108210842007c000001f0000007e,0x7e421090842104210840842f882108420f8000003e00000007d,0x7e42109084210421084085f1082108420f80000001f0000007d,0x7e4210908421042108f88421082108420f8000003e000000f81,0x7e842110842102108420842f882108420f8000003e00000007c,0x7e84211084210210842085f1082108420f80000001f0000007c,0x7e8421108421021084f88421082108420f8000003e000000f80,0x7e8421108421027c8420842108210842007c000001f0000007c,0x7e842110fc2102108420842108210842007c000001f0000007e,0x7ec631908421010842104210841f0000007c000001f0000007c,0x7f08420842108210842084210821087e0f8000003e000000f80,0x7f084208421082108420842f882108420f8000003e00000007c,0x7f0842084210827c8420842108210842007c000001f0000007d,0x7f084208fa1082108420842108210842007c000001f0000007c,0x7f08420c6318c10842104210841f0000007c000001f0000007c,0x7ff0001084210421084108421042108410843f003e000000f80,0x7ff000108421042108410842104217c4108421003e00000007c,0x7ff0001084210421084108421042f8841084210001f0000007c,0x7ff0001084210421084108427c421084108421003e000000f81,0x7ff000108421042108f9084210421084108421003e000000f80,0x7ff00010842106318c60842108210842007c000001f0000007c,0x7ff0001087e1042108410842104210841084210001f0000007c,0x7ff21090842104210840842108210842007c000001f0000007d,0x7ff42110842102108420842108210842007c000001f0000007c,0x7ff84208421082108420842108210842007c000001f0000007c,0xfc00002108420842108210842084210821087e0f8000003ff00000f80]

def a8p1 : Keys := .leaf [
0xfc000021084208421082108420842f882108420f8000003ff0000007c,0xfc000021084208421082108420842f8821087e0f8000003e00000007c,0xfc000021084208421082108420842f8821087e0f8000003e000000f80,0xfc000021084208421082108420842f8821087e10842107c000001f000,0xfc000021084208421082108420842f8842108410843f07c000001f000,0xfc00002108420842108210842085f10821087e0f80000001f0000007c,0xfc00002108420842108210842085f10821087e0f8000003e000000f80,0xfc00002108420842108210842085f10821087e10842107c0000000f80,0xfc00002108420842108210842085f10842108410843f07c0000000f80,0xfc00002108420842108210842085f1084217c410842107c000000007c,0xfc00002108420842108210842085ff882108420f80000001f0000007c,0xfc00002108420842108210842085ff884217c410842107c000000007c,0xfc0000210842084210821084f88421082108420f8000003ff00000f81,0xfc0000210842084210821084f884210821087e0f8000003e000000f81,0xfc0000210842084210821084f8842f882108420f8000003e00000007d,0xfc0000210842084210821084f8842f882108420f8000003e000000f81,0xfc0000210842084210821084f8842f8842108410842107c000001f001,0xfc0000210842084210821084f885f1082108420f80000001f0000007d,0xfc0000210842084210821084f885f1082108420f8000003e000000f81,0xfc0000210842084210821084f885f10842108410842107c0000000f81,0xfc0000210842084210821084f90842104217c410842107c000001f000,0xfc0000210842084210821084f908421042f88410842107c0000000f80,0xfc0000210842084210827c8420842108210842007fe00001f0000007f,0xfc0000210842084210827c842084210821087e0f8000003e000000f81,0xfc0000210842084210827c842084210821087e108421003e000000f83,0xfc0000210842084210827c8420842f88210842007c000001f0000007f,0xfc0000210842084210827c8420842f882108420f8000003e00000007d,0xfc0000210842084210827c8420842f88421084108421003e00000007f,0xfc0000210842084210827c842085f108210842007c000001f0000007f,0xfc0000210842084210827c842085f1082108420f80000001f0000007d,0xfc0000210842084210827c842085f1084210841084210001f0000007f,0xfc0000210842084210827c84210842104217c4108421003e00000007e,0xfc0000210842084210827c842108421042f8841084210001f0000007e,0xfc0000210842084210827c842108427c421084108421003e000000f83,0xfc00002108420842108294a52884210821087e0f8000003e000000f81,0xfc00002108420842108294a528842f882108420f8000003e00000007d,0xfc00002108420842108294a52885f1082108420f80000001f0000007d,0xfc00002108420842108294a5f88421082108420f8000003e000000f81,0xfc00002108420842108294a5f884210821087e0f8000003e000000f81,0xfc0000210842084211f21084208421082108420f8000003ff00000f80,0xfc0000210842084211f210842084210821087e0f8000003e000000f80,0xfc0000210842084211f2108420842f882108420f8000003e00000007c,0xfc0000210842084211f2108420842f882108420f8000003e000000f80,0xfc0000210842084211f2108420842f8842108410842107c000001f000,0xfc0000210842084211f210842085f1082108420f80000001f0000007c,0xfc0000210842084211f210842085f1082108420f8000003e000000f80,0xfc0000210842084211f210842085f10842108410842107c0000000f80,0xfc0000210842084211f21084f88421082108420f8000003e000000f80]

def a8p2 : Keys := .leaf [
0xfc0000210842084211f27c8420842108210842007c000001f0000007f,0xfc0000210842084211f27c84208421082108420f8000003e000000f81,0xfc0000210842084211f27c8421084210421084108421003e000000f82,0xfc0000210842084211f294a5288421082108420f8000003e000000f81,0xfc0000210842084211f42108410842104217c410842107c000001f001,0xfc0000210842084211f421084108421042f88410842107c0000000f81,0xfc000021084208fa1082108420842108210842007fe00001f0000007e,0xfc000021084208fa108210842084210821087e0f8000003e000000f80,0xfc000021084208fa108210842084210821087e108421003e000000f82,0xfc000021084208fa1082108420842f88210842007c000001f0000007e,0xfc000021084208fa1082108420842f882108420f8000003e00000007c,0xfc000021084208fa1082108420842f88421084108421003e00000007e,0xfc000021084208fa108210842085f108210842007c000001f0000007e,0xfc000021084208fa108210842085f1082108420f80000001f0000007c,0xfc000021084208fa108210842085f1084210841084210001f0000007e,0xfc000021084208fa10821084f88421082108420f8000003e000000f80,0xfc000021084208fa10821084f9084210421084108421003e000000f82,0xfc000021084208fa10827c8420842108210842007c000001f0000007e,0xfc000021084208fa10842108410842104217c4108421003e00000007f,0xfc000021084208fa108421084108421042f8841084210001f0000007f,0xfc0000210842094a529210842084210821087e0f8000003e000000f80,0xfc0000210842094a5292108420842f882108420f8000003e00000007c,0xfc0000210842094a529210842085f1082108420f80000001f0000007c,0xfc0000210842094a52921084f88421082108420f8000003e000000f80,0xfc0000210842094a52927c8420842108210842007c000001f0000007f,0xfc0000210842094a529294a5288421081f0000007c000001f0000007c,0xfc0000210842094a53f21084208421082108420f8000003e000000f80,0xfc0000210842094a53f210842084210821087e0f8000003e000000f80,0xfc00002108420c6318c10842104210841f0000007fe00001f0000007c,0xfc00002108420c6318c10842104210fc1f0000007c000001f0000007c,0xfc00002108420c6318c10842104210fc2108420f8000003e000000f80,0xfc00002108420c6318c1085f104210841f0000007c000001f0000007c,0xfc00002108420c6318c1085f108421082108420f8000003e00000007c,0xfc00002108420c6318c10be2104210841f0000007c000001f0000007c,0xfc00002108420c6318c10be2108421082108420f80000001f0000007c,0xfc00002108420c6318c210842084210821087e0f8000003e000000f80,0xfc00002108420c6318c2108420842f882108420f8000003e00000007c,0xfc00002108420c6318c210842085f1082108420f80000001f0000007c,0xfc00002108420c6318c21084f88421082108420f8000003e000000f80,0xfc00002108420c6318c27c8420842108210842007c000001f0000007e,0xfc00002108420c6318c421084084210821087e0f8000003e000000f81,0xfc00002108420c6318c4210840842f882108420f8000003e00000007d,0xfc00002108420c6318c421084085f1082108420f80000001f0000007d,0xfc00002108420c6319f10842104210841f0000007c000001f0000007c,0xfc00002108420c6319f21084208421082108420f8000003e000000f80,0xfc00002108420c6319f42108f88421082108420f8000003e000000f81,0xfc00002108420c6319f6318c608421082108420f8000003e000000f80,0xfc00002108420cfb18c10842104210841f0000007c000001f0000007c]

def a8p3 : Keys := .leaf [
0xfc00002108420cfb18c2108420842108210842007c000001f0000007e,0xfc00002108420cfb18c6318c60842108210842007c000001f0000007e,0xfc00002108420d6b5ad10842104210841f0000007c000001f0000007c,0xfc0000210fc20842108210842084210821087e0f80000001f0000007c,0xfc0000210fc20842108210842084210821087e0f8000003e000000f80,0xfc0000210fc20842108210842084210821087e10842107c0000000f80,0xfc0000210fc208421082108420842f882108420f80000001f0000007c,0xfc0000210fc20842108210842085f1082108420f80000001f0000007c,0xfc0000210fc2084210821084f88421082108420f80000001f0000007d,0xfc0000210fc2084210821084f88421082108420f8000003e000000f81,0xfc0000210fc2084210821084f908421042108410842107c0000000f80,0xfc0000210fc2084210827c8420842108210842007c000001f0000007f,0xfc0000210fc2084210827c84210842104210841084210001f0000007e,0xfc0000210fc20842108294a5288421082108420f80000001f0000007d,0xfc0000210fc2084211f21084208421082108420f80000001f0000007c,0xfc0000210fc2084211f21084208421082108420f8000003e000000f80,0xfc0000210fc2084211f421084108421042108410842107c0000000f81,0xfc0000210fc208fa1082108420842108210842007c000001f0000007e,0xfc0000210fc208fa10842108410842104210841084210001f0000007f,0xfc0000210fc2094a52921084208421082108420f80000001f0000007c,0xfc0000210fc20c6318c10842104210841f0000007c000001f0000007c,0xfc0000210fc20c6318c21084208421082108420f80000001f0000007c,0xfc0000210fc20c6318c42108408421082108420f80000001f0000007d,0xfc0000210fc21084210421084108421042108410843f07c0000000f80,0xfc0000210fc2108421042108410842104217c410842107c000000007c,0xfc0000210fc21084210421084108427c42108410842107c0000000f81,0xfc0000210fc2108421042108f908421042108410842107c0000000f80,0xfc0000210fc210842106318c608421082108420f80000001f0000007c,0xfc000021f84208421082108420842108210842007fe00001f0000007e,0xfc000021f8420842108210842084210821087e007c000001f0000007e,0xfc000021f8420842108210842084210821087e0f8000003e000000f80,0xfc000021f8420842108210842084210821087e108421003e000000f82,0xfc000021f84208421082108420842f88210842007c000001f0000007e,0xfc000021f84208421082108420842f882108420f8000003e00000007c,0xfc000021f84208421082108420842f88421084108421003e00000007e,0xfc000021f8420842108210842085f1082108420f80000001f0000007c,0xfc000021f8420842108210842085f1084210841084210001f0000007e,0xfc000021f842084210827c8420842108210842007c000001f0000007f,0xfc000021f842084211f2108420842108210842007c000001f0000007e,0xfc000021f84208fa1082108420842108210842007c000001f0000007e,0xfc000021f842094a5292108420842108210842007c000001f0000007e,0xfc000021f8420c6318c10842104210841f0000007c000001f0000007c,0xfc000021f8420c6318c2108420842108210842007c000001f0000007e,0xfc000021f8421084210421084108421042108410843f003e000000f82,0xfc000021f842108421042108410842104217c4108421003e00000007e,0xfc000021f842108421042108f9084210421084108421003e000000f82,0xfc000021f84210842106318c60842108210842007c000001f0000007e,0xfc000021f8421087e1042108410842104210841084210001f0000007e]

def a8p4 : Keys := .leaf [
0xfc8421210842084210810842104210841f0000007fe00001f0000007d,0xfc8421210842084210810842104210fc2108420f8000003e000000f81,0xfc842121084208421081085f104210841f0000007c000001f0000007d,0xfc842121084208421081085f108421082108420f8000003e00000007d,0xfc8421210842084210810be2104210841f0000007c000001f0000007d,0xfc8421210842084210810be2108421082108420f80000001f0000007d,0xfc842121084208421082108420842f882108420f8000003e00000007c,0xfc84212108420842108210842085f1082108420f80000001f0000007c,0xfc8421210842084210821084f88421082108420f8000003e000000f81,0xfc8421210842084210827c8420842108210842007c000001f0000007d,0xfc8421210842084211f10842104210841f0000007c000001f0000007d,0xfc8421210842084211f21084208421082108420f8000003e000000f80,0xfc842121084208fa10810842104210841f0000007c000001f0000007d,0xfc842121084208fa1082108420842108210842007c000001f0000007e,0xfc8421210842094a52910842104210841f0000007c000001f0000007d,0xfc84212108420c6318c10842104210841f0000007c000001f0000007c,0xfc8421210fc2084210810842104210841f0000007c000001f0000007d,0xfc8421210fc2084210821084208421082108420f80000001f0000007c,0xfc842121f842084210810842104210841f0000007c000001f0000007d,0xfc842121f84208421082108420842108210842007c000001f0000007e,0xfc84213e00001084210421084084210821087e0f8000003e000000f83,0xfc84213e000010842104210840842f882108420f8000003e00000007f,0xfc84213e00001084210421084085f1082108420f80000001f0000007f,0xfc84213e0000108421042108f88421082108420f8000003e000000f83,0xfd0842210842042108410842104210841f0000007fe00001f0000007c,0xfd0842210842042108410842104210fc2108420f8000003e000000f80,0xfd084221084204210841085f104210841f0000007c000001f0000007c,0xfd084221084204210841085f108421082108420f8000003e00000007c,0xfd0842210842042108410be2104210841f0000007c000001f0000007c,0xfd0842210842042108410be2108421082108420f80000001f0000007c,0xfd0842210842042109f10842104210841f0000007c000001f0000007c,0xfd0842210842042109f21084208421082108420f8000003e000000f80,0xfd084221084204f908410842104210841f0000007c000001f0000007c,0xfd084221084204f90842108420842108210842007c000001f0000007c,0xfd084221084205294a510842104210841f0000007c000001f0000007c,0xfd084221084208421082108420842f882108420f8000003e00000007d,0xfd08422108420842108210842085f1082108420f80000001f0000007d,0xfd0842210fc2042108410842104210841f0000007c000001f0000007c,0xfd0842210fc2084210821084208421082108420f80000001f0000007d,0xfd084221f842042108410842104210841f0000007c000001f0000007c,0xfd084221f84210842102108420842108210842007c000001f0000007e,0xfd08423e00001084210210842084210821087e0f8000003e000000f82,0xfd08423e000010842102108420842f882108420f8000003e00000007e,0xfd08423e00001084210210842085f1082108420f80000001f0000007e,0xfd8c63210842042108410842104210841f0000007c000001f0000007c,0xfd8c632108420c6318c10842104210841f0000007c000001f0000007c,0xfd8c633e0000108421010842104210841f0000007c000001f0000007e,0xfd8c633e8421108421010842104210841f0000007c000001f0000007d]

def a8p5 : Keys := .leaf [
0xfe1084108421042108410842104210841f0000007fe00001f0000007c,0xfe1084108421042108410842104210fc1f0000007c000001f0000007c,0xfe1084108421042108410842104210fc2108420f8000003e000000f80,0xfe108410842104210841085f104210841f0000007c000001f0000007c,0xfe108410842104210841085f108421082108420f8000003e00000007c,0xfe1084108421042108410be2108421082108420f80000001f0000007c,0xfe1084108421042109f10842104210841f0000007c000001f0000007d,0xfe108410842104f908410842104210841f0000007c000001f0000007d,0xfe108410842104f90842108420842108210842007c000001f0000007c,0xfe108410842105294a510842104210841f0000007c000001f0000007d,0xfe1084108423e42108410842104210841f0000007c000001f0000007c,0xfe108411f421042108410842104210841f0000007c000001f0000007c,0xfe108411f42108421082108420842108210842007c000001f0000007d,0xfe10841294a5242108410842104210841f0000007c000001f0000007c,0xfe108418c631842108410842104210841f0000007c000001f0000007c,0xfe108418c631884210810842104210841f0000007c000001f0000007d,0xfe10842108420842108210842084210821087e0f8000003e000000f80,0xfe108421084208421082108420842f882108420f8000003e00000007c,0xfe1084210842084210821084f88421082108420f8000003e000000f81,0xfe1084210842084210827c8420842108210842007c000001f0000007d,0xfe1084210842084211f21084208421082108420f8000003e000000f80,0xfe108421084208fa1082108420842108210842007c000001f0000007c,0xfe10842108420c6318c10842104210841f0000007c000001f0000007c,0xfe1084210fc2084210821084208421082108420f80000001f0000007c,0xfe108421f84208421082108420842108210842007c000001f0000007c,0xfe10843e00000842108210842084210821087e0f8000003e000000f82,0xfe10843e000008421082108420842f882108420f8000003e00000007e,0xfe10843e00000842108210842085f1082108420f80000001f0000007e,0xfe10843e00000c6318c10842104210841f0000007c000001f0000007e,0xffe00021084208421082108420842108210842007fe00001f0000007c,0xffe0002108420842108210842084210821087e007c000001f0000007c,0xffe0002108420842108210842084210821087e0f8000003e000000f80,0xffe0002108420842108210842084210821087e108421003e000000f80,0xffe00021084208421082108420842f88210842007c000001f0000007c,0xffe00021084208421082108420842f882108420f8000003e00000007c,0xffe00021084208421082108420842f88421084108421003e00000007c,0xffe0002108420842108210842085f108210842007c000001f0000007c,0xffe0002108420842108210842085f1082108420f80000001f0000007c,0xffe0002108420842108210842085f1084210841084210001f0000007c,0xffe000210842084210821084f8842108210842007c000001f0000007d,0xffe000210842084210821084f88421082108420f8000003e000000f81,0xffe000210842084210821084f9084210421084108421003e000000f80,0xffe000210842084210827c8420842108210842007c000001f0000007d,0xffe0002108420842108294a528842108210842007c000001f0000007d,0xffe000210842084211f2108420842108210842007c000001f0000007c,0xffe000210842084211f21084208421082108420f8000003e000000f80,0xffe000210842084211f4210841084210421084108421003e000000f81,0xffe00021084208fa1082108420842108210842007c000001f0000007c]

def a8p6 : Keys := .leaf [
0xffe000210842094a5292108420842108210842007c000001f0000007c,0xffe0002108420c6318c10842104210841f0000007c000001f0000007c,0xffe0002108420c6318c2108420842108210842007c000001f0000007c,0xffe0002108420c6318c4210840842108210842007c000001f0000007d,0xffe000210fc208421082108420842108210842007c000001f0000007c,0xffe000210fc2084210821084208421082108420f80000001f0000007c,0xffe000210fc2108421042108410842104210841084210001f0000007c,0xffe00021f84208421082108420842108210842007c000001f0000007c,0xffe0003e00001084210421084108421042108410843f003e000000f82,0xffe0003e0000108421042108410842104217c4108421003e00000007e,0xffe0003e00001084210421084108421042f8841084210001f0000007e,0xffe0003e0000108421042108f9084210421084108421003e000000f82,0xffe0003e000010842106318c60842108210842007c000001f0000007e,0xffe0003e00001087e1042108410842104210841084210001f0000007e,0xffe421210842084210810842104210841f0000007c000001f0000007d,0xffe42121084208421082108420842108210842007c000001f0000007c,0xffe4213ff00010842104210840842108210842007c000001f0000007d,0xffe842210842042108410842104210841f0000007c000001f0000007c,0xffe84221084208421082108420842108210842007c000001f0000007d,0xffe8423e842110842102108420842108210842007c000001f0000007e,0xffe8423ff00010842102108420842108210842007c000001f0000007c,0xfff084108421042108410842104210841f0000007c000001f0000007c,0xfff08421084208421082108420842108210842007c000001f0000007c,0xfff0843f084208421082108420842108210842007c000001f0000007e,0xfff0843ff00008421082108420842108210842007c000001f0000007c]

def a8 : Keys := (.branch 0x3f0000084210833ec630842108210842084210801f0000007c000001f (.branch 0x3f000008421082108420842108210be208421083e000000ffc000001f a8p0 (.branch 0x3f00000842108210847c9f2108210842084210801f0000007c000001f a8p1 a8p2)) (.branch 0x3f84210421084108421042108410842107c000001ff800007c000001f (.branch 0x3f21084842108210842042108410842107c000001ff800007c000001f a8p3 a8p4) (.branch 0x3ff800084210825294a4842108210842084210801f0000007c000001f a8p5 a8p6)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p0 : a8p0.all (checkAlias r8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p1 : a8p1.all (checkAlias r8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p2 : a8p2.all (checkAlias r8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p3 : a8p3.all (checkAlias r8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p4 : a8p4.all (checkAlias r8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p5 : a8p5.all (checkAlias r8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda8p6 : a8p6.all (checkAlias r8) = true := by decide +kernel

theorem badA8 : RejectsAlias 8 a8 :=
  verifyAliases 8 r8 a8 badR8 (by
    unfold a8
    simp only [allBranch, Bool.and_true, gooda8p0, gooda8p1, gooda8p2, gooda8p3, gooda8p4, gooda8p5, gooda8p6])

def r9p0 : Keys := .leaf [
0x3f00000842108210842084210821084208421f83e000000f8000003e0,0x3f000008421082108420842108210be208421083e000000f80000001f,0x3f000008421082108420842108217c4208421083e00000007c000001f,0x3f00000842108210847c84210821084208421083e000000f8000003e0,0x3f00000842108318c63042108410842107c000001f0000007c000001f,0x3f00000843f08210842084210821084208421083e00000007c000001f,0x3f42108842108108421042108410842107c000001f0000007c000001f,0x3f84210421084108421042108410842107c000001f0000007c000001f,0x3ff80008421082108420842108210842084210801f0000007c000001f,0x7e00001084210421084108421042108410842107c000001ff800007c000001f,0x7e00001084210421084108421042108410843f07c000001f0000007c000001f,0x7e00001084210421084108421042108410843f08421083e000000f8000003e0,0x7e0000108421042108410842104217c410842107c000001f0000007c000001f,0x7e0000108421042108410842104217c421084208421083e000000f80000001f,0x7e00001084210421084108421042f88410842107c000001f0000007c000001f,0x7e00001084210421084108421042f88421084208421083e00000007c000001f,0x7e00001084210421084108427c84210821084208421083e000000f8000003e0,0x7e0000108421042108f908421042108410842107c000001f0000007c000001f,0x7e0000108421047d084108421042108410842107c000001f0000007c000001f,0x7e000010842104a5294908421042108410842107c000001f0000007c000001f,0x7e000010842106318c6108421042108410842107c000001f0000007c000001f,0x7e00001087e10421084108421042108410842107c000001f0000007c000001f,0x7e00001087e10842108210842084210821084208421083e00000007c000001f,0x7e000010fc210421084108421042108410842107c000001f0000007c000001f,0x7e42109084210421084108421042108410842107c000001f0000007c000001f,0x7f08421084210421084108421042108410842107c000001f0000007c000001f,0x7ff0001084210421084108421042108410842107c000001f0000007c000001f]

def r9 : Keys := r9p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr9p0 : r9p0.all (checkFast 8 a8) = true := by decide +kernel

theorem badR9 : Rejects 9 r9 :=
  verifyFast 8 a8 r9 badA8 (by
    unfold r9
    simp only [allBranch, Bool.and_true, goodr9p0])

def a9p0 : Keys := .leaf [
0xfc00002108420842108210842084210821087e0f8000003e000000f80,0xfc000021084208421082108420842f882108420f8000003e00000007c,0xfc00002108420842108210842085f1082108420f80000001f0000007c,0xfc0000210842084210821084f88421082108420f8000003e000000f81,0xfc0000210842084210827c8420842108210842007c000001f0000007f,0xfc0000210842084211f21084208421082108420f8000003e000000f80,0xfc000021084208fa1082108420842108210842007c000001f0000007e,0xfc00002108420c6318c10842104210841f0000007c000001f0000007c,0xfc0000210fc2084210821084208421082108420f80000001f0000007c,0xfc000021f84208421082108420842108210842007c000001f0000007e,0xfc8421210842084210810842104210841f0000007c000001f0000007d,0xfd0842210842042108410842104210841f0000007c000001f0000007c,0xfe1084108421042108410842104210841f0000007c000001f0000007c,0xffe00021084208421082108420842108210842007c000001f0000007c,0x1f80000421084108421042108410842104210841f0000007fe00001f0000007c,0x1f80000421084108421042108410842104210fc1f0000007c000001f0000007c,0x1f80000421084108421042108410842104210fc2108420f8000003e000000f80,0x1f8000042108410842104210841085f104210841f0000007c000001f0000007c,0x1f8000042108410842104210841085f108421082108420f8000003e00000007c,0x1f80000421084108421042108410be2104210841f0000007c000001f0000007c,0x1f80000421084108421042108410be2108421082108420f80000001f0000007c,0x1f80000421084108421042109f10842104210841f0000007c000001f0000007d,0x1f80000421084108421042109f21084208421082108420f8000003e000000f80,0x1f8000042108410842104f908410842104210841f0000007c000001f0000007d,0x1f8000042108410842104f90842108420842108210842007c000001f0000007e,0x1f8000042108410842105294a510842104210841f0000007c000001f0000007d,0x1f80000421084108423e42108410842104210841f0000007c000001f0000007c,0x1f80000421084108423e84210821084208421082108420f8000003e000000f81,0x1f8000042108411f421042108410842104210841f0000007c000001f0000007c,0x1f8000042108411f42108421082108420842108210842007c000001f0000007f,0x1f800004210841294a5242108410842104210841f0000007c000001f0000007c,0x1f8000042108418c631842108410842104210841f0000007c000001f0000007c,0x1f8000042108418c631884210810842104210841f0000007c000001f0000007d,0x1f80000421f84108421042108410842104210841f0000007c000001f0000007c,0x1f80000421f84210842084210821084208421082108420f80000001f0000007c,0x1f8000043f084108421042108410842104210841f0000007c000001f0000007c,0x1f8000043f08421084208421082108420842108210842007c000001f0000007e,0x1f90842421084108421042108410842104210841f0000007c000001f0000007c,0x1f908427c0000210842084210810842104210841f0000007c000001f0000007f,0x1fa1084421084108421042108410842104210841f0000007c000001f0000007d,0x1fa10847c0000210842042108410842104210841f0000007c000001f0000007e,0x1fc2108421084108421042108410842104210841f0000007c000001f0000007c,0x1fc21087c0000108421042108410842104210841f0000007c000001f0000007e,0x1ffc000421084108421042108410842104210841f0000007c000001f0000007c,0x1ffc0007c000021084208421082108420842108210842007c000001f0000007e]

def a9 : Keys := a9p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gooda9p0 : a9p0.all (checkAlias r9) = true := by decide +kernel

theorem badA9 : RejectsAlias 9 a9 :=
  verifyAliases 9 r9 a9 badR9 (by
    unfold a9
    simp only [allBranch, Bool.and_true, gooda9p0])

def r10p0 : Keys := .leaf [
0x7e00001084210421084108421042108410842107c000001f0000007c000001f]

def r10 : Keys := r10p0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem goodr10p0 : r10p0.all (checkFast 9 a9) = true := by decide +kernel

theorem badR10 : Rejects 10 r10 :=
  verifyFast 9 a9 r10 badA9 (by
    unfold r10
    simp only [allBranch, Bool.and_true, goodr10p0])

theorem lower :
    ¬ RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (3258290 : ℕ).testBit (5*u.val+v.val)) 10 := by
  rintro ⟨C, mono, size, computes⟩
  obtain ⟨k,hk,build⟩ := representsBuild C mono computes
  obtain ⟨W,sub,j,jk,reach⟩ := buildReach build
  rw [allSources W sub (reachSeparates reach)] at reach
  have same : (decodeKey 3561963710422844759837215754900201654275826917327189221308241152903380729887).toFinset = sources.toFinset := by decide +kernel
  rw [← same] at reach
  exact badR10 3561963710422844759837215754900201654275826917327189221308241152903380729887 (by decide +kernel) j (jk.trans (hk.trans size)) reach

end PEqualNP.Outside.L_meta_9312

theorem PEqualNP.Outside.L_meta_9312 :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3258290 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_9312.lower
