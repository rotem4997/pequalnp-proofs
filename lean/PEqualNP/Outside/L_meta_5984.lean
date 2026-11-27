import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5984
abbrev W := BitVec 16

def mix (o : Bool) (a b : W) := if o then a ||| b else a &&& b
inductive Plan (t : W) : ℕ → Finset W → Prop where
  | done : Plan t 0 {t}
  | merge {k : ℕ} (s : Finset W) (a b : W) (o : Bool) :
    mix o a b ∉ s → Plan t k (insert (mix o a b) s) → Plan t (k+1) (insert a (insert b s))

def raw : Finset W := {15,240,3840,61440,4369,8738,17476,34952}

def Sep (t : W) (s : Finset W) : Prop := ∀ p q : Fin 16, t.getLsbD p = true → t.getLsbD q = false → ∃ w ∈ s, w.getLsbD p = true ∧ w.getLsbD q = false

lemma planSep {t k s} (h : Plan t k s) : Sep t s := by
  induction h with
  | done => exact fun p q hp hq => ⟨_,Finset.mem_singleton_self _,hp,hq⟩
  | merge s a b o _ _ ih =>
    intro p q hp hq
    obtain ⟨c,hc,hp',hq'⟩ := ih p q hp hq
    rcases Finset.mem_insert.mp hc with rfl|hc
    · have v : (a.getLsbD p = true ∧ a.getLsbD q = false) ∨ (b.getLsbD p = true ∧ b.getLsbD q = false) := by
        have split : ∀ o ap aq bp bq : Bool, (if o then ap || bp else ap && bp) = true →
            (if o then aq || bq else aq && bq) = false →
            (ap = true ∧ aq = false) ∨ (bp = true ∧ bq = false) := by decide
        apply split o
        · cases o <;> simpa only [mix,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using hp'
        · cases o <;> simpa only [mix,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using hq'
      rcases v with h|h
      · exact ⟨a,by simp,h⟩
      · exact ⟨b,by simp,h⟩
    · exact ⟨c,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),hp',hq'⟩

lemma planCard {t k s} (h : Plan t k s) : s.card ≤ k+1 := by
  induction h with
  | done => simp
  | merge s a b o he _ ih =>
    rw [Finset.card_insert_of_notMem he] at ih
    have h1 := Finset.card_insert_le a (insert b s)
    have h2 := Finset.card_insert_le b s
    omega

def posBits : List ℕ := [0,1,3,6,9,12]
def forbidden (s : Finset W) (p : ℕ) : W :=
  s.fold (fun x y : W => x &&& y) (~~~4683) (fun w => if w.getLsbD p then w else ~~~0)

lemma forbidden_spec (s : Finset W) (p : ℕ) (q : Fin 16) :
    (forbidden s p).getLsbD q = true → (4683 : W).getLsbD q = false ∧
      ∀ w ∈ s, w.getLsbD p = true → w.getLsbD q = true := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [forbidden,Finset.fold_empty,Finset.notMem_empty,false_implies,implies_true,and_true]
    exact (by decide +kernel : ∀ q : Fin 16, (60852 : W).getLsbD q = true → (4683 : W).getLsbD q = false) q
  | insert x s hx ih =>
    simp only [forbidden,Finset.fold_insert hx,BitVec.getLsbD_and,Bool.and_eq_true] at *
    rintro ⟨h,h'⟩
    obtain ⟨hn,rest⟩ := ih h'
    refine ⟨hn,?_⟩
    intro w hw hp
    rcases Finset.mem_insert.mp hw with rfl|hw
    · simpa [hp] using h
    · exact rest _ hw hp

def sepTest (s : Finset W) : Bool := posBits.all fun p => forbidden s p == 0

def dropIf (s : Finset W) (a : W) (d : Bool) : Finset W := if d then s.erase a else s

def possible (k : ℕ) (s : Finset W) : Bool := decide (s.card ≤ k+1) && sepTest s

def step (P : Finset W → Bool) (s : Finset W) : Bool :=
  letI (p : W → Prop) [DecidablePred p] : Decidable (∃ w ∈ s, p w) :=
    Finset.decidableExistsAndFinset
  decide (∃ a ∈ s, ∃ b ∈ s, a ≤ b ∧ ∃ o da db : Bool,
    P (insert (mix o a b) (dropIf (dropIf s a da) b db)) = true)

def search : ℕ → Finset W → Bool
  | 0,s => decide ((4683 : W) ∈ s)
  | k+1,s => possible (k+1) s && step (search k) s

lemma keep (s : Finset W) (a : W) : dropIf (insert a s) a (decide (a ∉ s)) = s := by
  by_cases ha : a ∈ s <;> simp [dropIf,ha]

lemma mix_comm (o : Bool) (a b : W) : mix o a b = mix o b a := by
  cases o <;> simp [mix,BitVec.and_comm,BitVec.or_comm]

lemma sep_ok {s : Finset W} (h : Sep 4683 s) : sepTest s = true := by
  apply List.all_eq_true.mpr
  intro p hp
  have hpos : ∀ p ∈ posBits, p < 16 ∧ (4683 : W).getLsbD p = true := by decide +kernel
  have hp' := hpos p hp
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  by_cases hb : (forbidden s p).getLsbD q = true
  · obtain ⟨hn,hall⟩ := forbidden_spec s p ⟨q,hq⟩ hb
    obtain ⟨w,hw,h1,h2⟩ := h ⟨p,hp'.1⟩ ⟨q,hq⟩ hp'.2 hn
    exact False.elim (Bool.noConfusion ((hall _ hw h1).symm.trans h2))
  · simpa using hb

lemma plan_search {k s} (h : Plan 4683 k s) : search k s = true := by
  induction h with
  | done => simp [search]
  | merge s a b o he hx ih =>
    have hp := Plan.merge s a b o he hx
    have pos : possible _ _ = true := Bool.and_eq_true_iff.mpr ⟨decide_eq_true (planCard hp),sep_ok (planSep hp)⟩
    simp only [search,pos,Bool.true_and,step,decide_eq_true_eq]
    rcases Nat.le_total a.toNat b.toNat with hl|hl
    · refine ⟨a,by simp,b,by simp,hl,o,decide (a ∉ insert b s),decide (b ∉ s),?_⟩
      simpa only [keep] using ih
    · refine ⟨b,by simp,a,by simp,hl,o,decide (b ∉ insert a s),decide (a ∉ s),?_⟩
      rw [Finset.insert_comm a b,keep,keep,mix_comm o b a]; exact ih

lemma mustUse {k s} (h : Plan 4683 k s) (sub : s ⊆ raw) : s = raw := by
  letI (u : Finset W) (p : W → Prop) [DecidablePred p] : Decidable (∀ w ∈ u, p w) :=
    Finset.decidableDforallFinset
  apply Finset.Subset.antisymm sub
  intro w hw
  by_contra hn
  have obstruction : ∀ z ∈ raw, ∃ p q : Fin 16, (4683 : W).getLsbD p = true ∧ (4683 : W).getLsbD q = false ∧
      ∀ x ∈ raw.erase z, ¬ (x.getLsbD p = true ∧ x.getLsbD q = false) := by
    intro z hz
    simp only [raw,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨0,4,by decide⟩
    · exact ⟨6,2,by decide⟩
    · exact ⟨9,5,by decide⟩
    · exact ⟨12,4,by decide⟩
    · exact ⟨0,2,by decide⟩
    · exact ⟨1,2,by decide⟩
    · exact ⟨6,4,by decide⟩
    · exact ⟨3,2,by decide⟩
  obtain ⟨p,q,hp,hq,hno⟩ := obstruction w hw
  obtain ⟨x,hx,hbit⟩ := planSep h p q hp hq
  exact hno x (Finset.mem_erase.mpr ⟨fun e => hn (e ▸ hx),sub hx⟩) hbit

lemma noPlanOf (h7 : search 7 raw = false) (h8 : search 8 raw = false) :
    ∀ k ≤ 8, ∀ s ⊆ raw, ¬ Plan 4683 k s := by
  intro k hk s hsub hp
  have eq := mustUse hp hsub
  subst s
  have h := planCard hp
  have count : raw.card = 8 := by decide
  have se := plan_search hp
  rcases (show k=7 ∨ k=8 by omega) with rfl|rfl
  · exact Bool.noConfusion (h7.symm.trans se)
  · exact Bool.noConfusion (h8.symm.trans se)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def inputMasks : List W :=
  [0x000f, 0x00f0, 0x0f00, 0xf000, 0x1111, 0x2222, 0x4444, 0x8888]

private abbrev ones : W := BitVec.allOnes 16
private def pointBit (q : Fin 16) (v : W) : Bool := v[q.val]

private def wordOp : GateOp → List W → W
  | .and, l => l.foldr (· &&& ·) ones
  | .or, l => l.foldr (· ||| ·) 0
  | _, _ => 0

private def value (env : List W) (g : Gate) : W :=
  wordOp g.op (g.inputs.map fun i => env.getD i 0)

private def generated : List W → List Gate → List W
  | _, [] => []
  | env, g :: gs => let z := value env g; z :: generated (env ++ [z]) gs

private def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private theorem bitWord (q : Fin 16) (op : GateOp) (l : List W)
    (h : op = .and ∨ op = .or) :
    pointBit q (wordOp op l) = op.eval (l.map (pointBit q)) := by
  rcases h with rfl | rfl
  · induction l with
    | nil => exact BitVec.getElem_allOnes _ q.isLt
    | cons x xs ih =>
      simpa [wordOp, pointBit, GateOp.eval, Bool.and_comm] using
        congrArg (fun t => pointBit q x && t) ih
  · induction l with
    | nil => simp [wordOp, pointBit, GateOp.eval]
    | cons x xs ih =>
      simpa [wordOp, pointBit, GateOp.eval, Bool.or_comm] using
        congrArg (fun t => pointBit q x || t) ih

private theorem readBit (q : Fin 16) (env : List W) (a : ℕ) :
    (env.map (pointBit q)).getD a false = pointBit q (env.getD a 0) := by
  simpa [pointBit] using (List.getD_map env (0 : W) (n := a) (pointBit q))

private theorem simulate (q : Fin 16) (env : List W) (gs : List Gate)
    (h : ∀ g ∈ gs, legal g) :
    (env ++ generated env gs).map (pointBit q) =
      gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
        (env.map (pointBit q)) := by
  induction gs generalizing env with
  | nil => simp [generated]
  | cons g gs ih =>
    have hstep : pointBit q (value env g) = g.op.eval (g.inputs.map fun a =>
        (env.map (pointBit q)).getD a false) := by
      rw [value, bitWord q _ _ (h g (by simp)).1]
      simp only [List.map_map, Function.comp_def, readBit]
    simpa [generated, List.append_assoc, hstep] using
      ih (env ++ [value env g]) (fun a ha => h a (by simp [ha]))

private theorem observe (q : Fin 16) (env : List W) (gs : List Gate)
    (h : ∀ g ∈ gs, legal g) (j : ℕ) :
    pointBit q ((env ++ generated env gs).getD j 0) =
      Circuit.eval ⟨gs,j⟩ (env.map (pointBit q)) := by
  rw [← readBit, simulate q env gs h]
  rfl

private def rowAt (q : Fin 16) : Fin 4 := ⟨q.val / 4, by omega⟩
private def colAt (q : Fin 16) : Fin 4 := ⟨q.val % 4, Nat.mod_lt _ (by decide)⟩

private theorem masks_at : ∀ q : Fin 16,
    inputMasks.map (pointBit q) = oneEach (rowAt q) (colAt q) := by decide
private theorem target_at : ∀ q : Fin 16,
    pointBit q 4683 = (4683 : ℕ).testBit (4 * (rowAt q).val + (colAt q).val) := by decide

private def Known (env : List W) (z : W) : Prop := z = 0 ∨ z = ones ∨ z ∈ env
private def Good (env : List W) (z : W) : Prop := z ≠ 0 ∧ z ≠ ones ∧ z ∈ env

private theorem read_known (env : List W) (i : ℕ) : Known env (env.getD i 0) := by
  by_cases hi : i < env.length
  · right; right
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _
  · left
    exact List.getD_eq_default _ _ (by omega)

private theorem mix_origin {env : List W} (o : Bool) (a b : W)
    (ha : Known env a) (hb : Known env b) :
    Known env (mix o a b) ∨ (Good env a ∧ Good env b) := by
  have zero : Known env 0 := Or.inl rfl
  have top : Known env ones := Or.inr (Or.inl rfl)
  by_cases ha0 : a = 0
  · subst a; left; cases o <;> simp [mix] <;> assumption
  by_cases ha1 : a = ones
  · subst a; left; cases o <;> simp only [mix, Bool.false_eq_true, ite_false, ite_true, ones, BitVec.allOnes_and, BitVec.allOnes_or] <;> assumption
  by_cases hb0 : b = 0
  · subst b; left; cases o <;> simp [mix] <;> assumption
  by_cases hb1 : b = ones
  · subst b; left; cases o <;> simp only [mix, Bool.false_eq_true, ite_false, ite_true, ones, BitVec.and_allOnes, BitVec.or_allOnes] <;> assumption
  exact Or.inr ⟨⟨ha0, ha1, (ha.resolve_left ha0).resolve_left ha1⟩,
    ⟨hb0, hb1, (hb.resolve_left hb0).resolve_left hb1⟩⟩

private theorem value_origin (env : List W) (g : Gate) (hg : legal g) :
    Known env (value env g) ∨
      ∃ (o : Bool) (a b : W), Good env a ∧ Good env b ∧ value env g = mix o a b := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hlen
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => exact Or.inl (Or.inr (Or.inl rfl))
    | [i], _ => left; simpa only [value,wordOp,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,ones,BitVec.and_allOnes] using read_known env i
    | [i,j], _ =>
      let a := env.getD i 0
      let b := env.getD j 0
      have he : value env ⟨.and,[i,j]⟩ = mix false a b := by simp only [value,wordOp,mix,ones,a,b,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,BitVec.and_allOnes,Bool.false_eq_true,ite_false]
      rw [he]
      rcases mix_origin false a b (read_known env i) (read_known env j) with h|h
      · exact Or.inl h
      · exact Or.inr ⟨false,a,b,h.1,h.2,rfl⟩
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => exact Or.inl (Or.inl rfl)
    | [i], _ => left; simpa [value,wordOp] using read_known env i
    | [i,j], _ =>
      let a := env.getD i 0
      let b := env.getD j 0
      have he : value env ⟨.or,[i,j]⟩ = mix true a b := by simp [value,wordOp,mix,a,b]
      rw [he]
      rcases mix_origin true a b (read_known env i) (read_known env j) with h|h
      · exact Or.inl h
      · exact Or.inr ⟨true,a,b,h.1,h.2,rfl⟩
    | _ :: _ :: _ :: _, h => simp at h


private theorem pull (t : W) (gs : List Gate) (env : List W)
    (leg : ∀ g ∈ gs, legal g) (k : ℕ) (s : Finset W) (hp : Plan t k s)
    (hs : ∀ x ∈ s, Good (env ++ generated env gs) x) :
    ∃ k' ≤ k + gs.length, ∃ s' : Finset W, (∀ x ∈ s', Good env x) ∧ Plan t k' s' := by
  induction gs generalizing env k s with
  | nil => exact ⟨k, by simp, s, by simpa [generated] using hs, hp⟩
  | cons g gs ih =>
    let z := value env g
    have htail : ∀ x ∈ s, Good ((env ++ [z]) ++ generated (env ++ [z]) gs) x := by
      simpa [generated, z, List.append_assoc] using hs
    obtain ⟨n, hn, f, hf, p⟩ := ih (env := env ++ [z]) (k := k) (s := s)
      (fun g' hg' => leg g' (by simp [hg'])) hp htail
    have drop : ∀ x ∈ f, x ≠ z → Good env x := by
      intro x hx hxz
      obtain ⟨hx0,hx1,hxm⟩ := hf x hx
      exact ⟨hx0,hx1,by simpa [hxz] using hxm⟩
    by_cases hz : z ∈ f
    · rcases value_origin env g (leg g (by simp)) with old | ⟨o,a,b,ha,hb,eq⟩
      · change Known env z at old
        have gz := hf z hz
        have zm := (old.resolve_left gz.1).resolve_left gz.2.1
        refine ⟨n, by simp only [List.length_cons]; omega, f, ?_, p⟩
        intro x hx
        by_cases e : x = z
        · subst x; exact ⟨gz.1,gz.2.1,zm⟩
        · exact drop x hx e
      · change z = mix o a b at eq
        have hrec : insert (mix o a b) (f.erase z) = f := by
          rw [← eq, Finset.insert_erase hz]
        refine ⟨n+1, by simp only [List.length_cons]; omega, insert a (insert b (f.erase z)), ?_,
          Plan.merge (f.erase z) a b o (by rw [← eq]; exact Finset.notMem_erase _ _)
            (by rw [hrec]; exact p)⟩
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_erase] at hx
        rcases hx with rfl | rfl | ⟨e, h⟩
        · exact ha
        · exact hb
        · exact drop x h e
    · exact ⟨n, by simp only [List.length_cons]; omega, f,
        fun x hx => drop x hx (fun e => hz (e ▸ hx)), p⟩


theorem rep_to_plan
    (h : RepSizeAtMost (fun u v : Fin 4 => (4683 : ℕ).testBit (4*u.val + v.val)) 8) :
    ∃ k ≤ 8, ∃ s ⊆ raw, Plan 4683 k s := by
  obtain ⟨⟨gs,j⟩,mono,sz,correct⟩ := h
  have leg : ∀ g ∈ gs, legal g := by
    intro g hg
    obtain ⟨hop,hlen⟩ := mono g hg
    exact ⟨by simpa using hop, hlen⟩
  let env := inputMasks ++ generated inputMasks gs
  have out : env.getD j 0 = (4683 : W) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let q : Fin 16 := ⟨i,hi⟩
    change pointBit q (env.getD j 0) = pointBit q 4683
    calc
      _ = Circuit.eval ⟨gs,j⟩ (inputMasks.map (pointBit q)) := observe q inputMasks gs leg j
      _ = Circuit.eval ⟨gs,j⟩ (oneEach (rowAt q) (colAt q)) := by rw [masks_at q]
      _ = _ := (correct (rowAt q) (colAt q)).trans (target_at q).symm
  have good : Good env 4683 := by
    have known := read_known env j
    rw [out] at known
    have h0 : (4683 : W) ≠ 0 := by decide
    have h1 : (4683 : W) ≠ ones := by decide
    exact ⟨h0,h1,(known.resolve_left h0).resolve_left h1⟩
  obtain ⟨k,hk,s,hs,hp⟩ := pull 4683 gs inputMasks leg 0 {4683} Plan.done
    (by intro x hx; simp only [Finset.mem_singleton] at hx; subst x; exact good)
  have base : inputMasks.toFinset = raw := by decide
  exact ⟨k, by change gs.length ≤ 8 at sz; omega, s, fun x hx => by
    rw [← base]; exact List.mem_toFinset.mpr (hs x hx).2.2, hp⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or,[4,5]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩,
  ⟨.and,[1,6]⟩, ⟨.and,[2,5]⟩, ⟨.and,[3,4]⟩, ⟨.or,[10,11]⟩,
  ⟨.or,[12,13]⟩, ⟨.or,[14,15]⟩],16⟩

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (4683 : ℕ).testBit (4*u.val+v.val)) 9 := by
  refine ⟨witness,?_,by decide,by decide +kernel⟩
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

private def excluded (k : ℕ) (covered : List (Finset W)) (s : Finset W) : Bool :=
  possible k s && !(covered.contains s)

private theorem row {k : ℕ} {s : Finset W} {covered : List (Finset W)}
    (h : step (excluded (k+1) covered) s = false)
    (hc : ∀ u ∈ covered, search (k+1) u = false) : search (k+2) s = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  obtain ⟨_,hs⟩ := Bool.and_eq_true_iff.mp ht
  simp only [step,decide_eq_true_eq] at hs
  simp only [step,decide_eq_false_iff_not] at h
  obtain ⟨a,ha,b,hb,hab,o,da,db,hx⟩ := hs
  let t := insert (mix o a b) (dropIf (dropIf s a da) b db)
  change search (k+1) t = true at hx
  by_cases hm : t ∈ covered
  · rw [hc t hm] at hx; contradiction
  · have hpos := (Bool.and_eq_true_iff.mp hx).1
    have hu : excluded (k+1) covered t = true := by simp [excluded,hpos,hm]
    exact h ⟨a,ha,b,hb,hab,o,da,db,hu⟩

private theorem allNil (k : ℕ) : ∀ u ∈ ([] : List (Finset W)), search k u = false := by simp

private theorem allCons {k : ℕ} {s : Finset W} {l : List (Finset W)}
    (hs : search k s = false) (hl : ∀ u ∈ l, search k u = false) :
    ∀ u ∈ s :: l, search k u = false := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | h
  · exact hs
  · exact hl u h
private def s3_0 : Finset W := {15,578,4369,63624}
private def s3_1 : Finset W := {15,4161,8738,36744}
private def s3_2 : Finset W := {15,72,7953,61986}
private def s3_3 : Finset W := {3840,8738,21583,39417}
private def s3_4 : Finset W := {4593,17999,43690,61440}
private def s3_5 : Finset W := {4369,17999,43770,61440}
private def s3_6 : Finset W := {3840,8946,21583,39321}
private def s3_7 : Finset W := {15,64,7961,61986}
private def s3_8 : Finset W := {15,64,7953,61994}
private def s3_9 : Finset W := {15,4160,8738,40857}
private def s3_10 : Finset W := {527,4593,43690,62532}
private def s3_11 : Finset W := {4175,4593,8738,36744}
private def s3_12 : Finset W := {3840,4175,8738,39417}
private def s3_13 : Finset W := {15,576,4369,64170}
private def s3_14 : Finset W := {4111,8946,20292,39321}
private def s3_15 : Finset W := {591,4369,43770,61440}
private def s3_16 : Finset W := {591,4369,8946,63624}
private def s3_17 : Finset W := {79,7953,35064,61986}
private def s3_18 : Finset W := {79,8017,34952,61986}
private def s3_19 : Finset W := {79,7953,34952,62050}
private def s3_20 : Finset W := {79,7953,35016,61986}
private def s3_21 : Finset W := {15,8017,34952,62050}
private def s3_22 : Finset W := {64,4111,8738,40857}
private def s3_23 : Finset W := {15,64,12834,40857}
private def s3_24 : Finset W := {64,527,4369,64170}
private def s3_25 : Finset W := {15,64,4881,64170}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_0 : search 3 s3_0 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_1 : search 3 s3_1 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_2 : search 3 s3_2 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_3 : search 3 s3_3 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_4 : search 3 s3_4 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_5 : search 3 s3_5 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_6 : search 3 s3_6 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_7 : search 3 s3_7 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_8 : search 3 s3_8 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_9 : search 3 s3_9 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_10 : search 3 s3_10 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_11 : search 3 s3_11 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_12 : search 3 s3_12 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_13 : search 3 s3_13 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_14 : search 3 s3_14 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_15 : search 3 s3_15 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_16 : search 3 s3_16 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_17 : search 3 s3_17 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_18 : search 3 s3_18 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_19 : search 3 s3_19 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_20 : search 3 s3_20 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_21 : search 3 s3_21 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_22 : search 3 s3_22 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_23 : search 3 s3_23 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_24 : search 3 s3_24 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c3_25 : search 3 s3_25 = false := by
  apply row (k := 1) (covered := [])
  · decide +kernel
  · exact allNil 2
private def s4_0 : Finset W := {15,4593,8738,36744,62532}
private def s4_1 : Finset W := {15,4369,8946,20292,63624}
private def s4_2 : Finset W := {15,64,7953,34952,61986}
private def s4_3 : Finset W := {15,7953,17476,35064,61986}
private def s4_4 : Finset W := {514,4593,17487,34952,61440}
private def s4_5 : Finset W := {3855,4593,8738,34952,62543}
private def s4_6 : Finset W := {3855,4369,8946,17487,63624}
private def s4_7 : Finset W := {514,4369,17487,35064,61440}
private def s4_8 : Finset W := {3855,4369,17487,35064,61986}
private def s4_9 : Finset W := {4369,8946,20303,34952,61455}
private def s4_10 : Finset W := {15,514,4593,34952,62532}
private def s4_11 : Finset W := {15,578,4369,34952,61440}
private def s4_12 : Finset W := {15,4369,8946,20303,63624}
private def s4_13 : Finset W := {15,64,514,4369,63624}
private def s4_14 : Finset W := {3840,4601,8738,17487,61440}
private def s4_15 : Finset W := {3840,4369,8954,17487,61440}
private def s4_16 : Finset W := {3840,4377,8946,17487,61440}
private def s4_17 : Finset W := {3840,4593,8746,17487,61440}
private def s4_18 : Finset W := {4593,8738,17487,36744,61455}
private def s4_19 : Finset W := {3840,4097,8946,17487,34952}
private def s4_20 : Finset W := {7953,8738,17487,35064,61455}
private def s4_21 : Finset W := {3840,4097,8738,17487,35064}
private def s4_22 : Finset W := {15,4593,8738,36744,62543}
private def s4_23 : Finset W := {15,3840,4161,8738,34952}
private def s4_24 : Finset W := {15,7953,17487,35064,61986}
private def s4_25 : Finset W := {15,72,7953,8738,61440}
private def s4_26 : Finset W := {15,72,3840,4369,61986}
private def s4_27 : Finset W := {7953,8738,17487,39417,61440}
private def s4_28 : Finset W := {3840,4593,8738,21583,34952}
private def s4_29 : Finset W := {3840,4096,8738,17487,39417}
private def s4_30 : Finset W := {4593,8738,17999,34952,61440}
private def s4_31 : Finset W := {4593,8738,17487,35464,61440}
private def s4_32 : Finset W := {512,4593,17487,43690,61440}
private def s4_33 : Finset W := {4593,8738,20303,34952,62543}
private def s4_34 : Finset W := {3840,4161,8738,17487,34952}
private def s4_35 : Finset W := {4369,8946,17999,34952,61440}
private def s4_36 : Finset W := {512,4369,17487,43770,61440}
private def s4_37 : Finset W := {3840,4369,17487,43770,61986}
private def s4_38 : Finset W := {578,4369,17487,34952,61440}
private def s4_39 : Finset W := {4369,8946,20303,34952,62543}
private def s4_40 : Finset W := {3840,4096,8946,17487,39321}
private def s4_41 : Finset W := {3840,4369,8946,21583,34952}
private def s4_42 : Finset W := {3840,4369,8946,17487,39048}
private def s4_43 : Finset W := {4881,8738,17487,35064,61440}
private def s4_44 : Finset W := {4369,8738,17999,35064,61440}
private def s4_45 : Finset W := {4369,8738,20303,35064,62543}
private def s4_46 : Finset W := {3840,4369,12834,17487,35064}
private def s4_47 : Finset W := {3840,4369,8738,21583,35064}
private def s4_48 : Finset W := {3840,4441,8738,17487,61440}
private def s4_49 : Finset W := {3840,4369,8810,17487,61440}
private def s4_50 : Finset W := {240,4881,17487,43690,61440}
private def s4_51 : Finset W := {240,4369,17999,43690,61440}
private def s4_52 : Finset W := {240,3840,12834,17487,39321}
private def s4_53 : Finset W := {240,3840,8738,21583,39321}
private def s4_54 : Finset W := {15,3840,4601,8738,62532}
private def s4_55 : Finset W := {15,4369,8954,20292,61440}
private def s4_56 : Finset W := {15,248,7953,17476,61986}
private def s4_57 : Finset W := {15,3848,4593,8738,62532}
private def s4_58 : Finset W := {15,64,7961,8738,61440}
private def s4_59 : Finset W := {15,64,3848,4369,61986}
private def s4_60 : Finset W := {15,240,7961,17476,61986}
private def s4_61 : Finset W := {15,4377,8946,20292,61440}
private def s4_62 : Finset W := {15,64,3840,4377,61986}
private def s4_63 : Finset W := {15,3840,4593,8746,62532}
private def s4_64 : Finset W := {15,64,7953,8746,61440}
private def s4_65 : Finset W := {15,64,3840,4369,61994}
private def s4_66 : Finset W := {15,240,7953,17476,61994}
private def s4_67 : Finset W := {15,4369,8946,20292,61448}
private def s4_68 : Finset W := {15,64,7953,8738,61448}
private def s4_69 : Finset W := {8,15,64,7953,61986}
private def s4_70 : Finset W := {15,4097,8946,20292,34952}
private def s4_71 : Finset W := {15,64,4097,8738,36744}
private def s4_72 : Finset W := {79,4593,8738,36744,61440}
private def s4_73 : Finset W := {15,4593,8738,36744,61504}
private def s4_74 : Finset W := {15,7953,17476,39417,61986}
private def s4_75 : Finset W := {15,4593,8738,40857,62532}
private def s4_76 : Finset W := {15,4160,7953,8738,34952}
private def s4_77 : Finset W := {4111,4593,8738,17476,36744}
private def s4_78 : Finset W := {15,4593,8738,21572,36744}
private def s4_79 : Finset W := {15,4160,4369,8738,36744}
private def s4_80 : Finset W := {15,3840,4160,8738,39321}
private def s4_81 : Finset W := {3840,4111,8738,17476,39417}
private def s4_82 : Finset W := {15,3840,8738,21572,39417}
private def s4_83 : Finset W := {527,4593,17476,43690,61440}
private def s4_84 : Finset W := {527,4593,8738,34952,62532}
private def s4_85 : Finset W := {15,4593,17988,43690,61440}
private def s4_86 : Finset W := {15,4593,8738,35464,62532}
private def s4_87 : Finset W := {15,512,4593,43690,62532}
private def s4_88 : Finset W := {15,4160,4593,8738,36744}
private def s4_89 : Finset W := {15,3840,4160,8738,39417}
private def s4_90 : Finset W := {3840,4175,4593,8738,34952}
private def s4_91 : Finset W := {79,3840,4369,8946,63624}
private def s4_92 : Finset W := {15,3904,4369,8946,63624}
private def s4_93 : Finset W := {15,7953,17476,43770,61986}
private def s4_94 : Finset W := {527,4369,17476,43770,61440}
private def s4_95 : Finset W := {527,4369,8946,17476,63624}
private def s4_96 : Finset W := {15,4369,17988,43770,61440}
private def s4_97 : Finset W := {15,4369,8946,17988,63624}
private def s4_98 : Finset W := {15,576,4369,43690,61440}
private def s4_99 : Finset W := {15,4369,8946,20292,64170}
private def s4_100 : Finset W := {15,576,4369,34952,61986}
private def s4_101 : Finset W := {15,576,4369,8738,63624}
private def s4_102 : Finset W := {15,4096,8946,20292,39321}
private def s4_103 : Finset W := {4111,4369,8946,20292,34952}
private def s4_104 : Finset W := {15,4369,8946,20292,39048}
private def s4_105 : Finset W := {591,4369,8946,34952,61440}
private def s4_106 : Finset W := {15,576,4369,43770,61440}
private def s4_107 : Finset W := {15,576,4369,8946,63624}
private def s4_108 : Finset W := {3840,4111,8946,17476,39321}
private def s4_109 : Finset W := {15,3840,8946,21572,39321}
private def s4_110 : Finset W := {79,7953,8738,35064,61440}
private def s4_111 : Finset W := {79,3840,4369,35064,61986}
private def s4_112 : Finset W := {79,240,7953,34952,61986}
private def s4_113 : Finset W := {15,64,7953,35064,61986}
private def s4_114 : Finset W := {15,4433,8738,36744,62532}
private def s4_115 : Finset W := {15,4369,8802,20292,63624}
private def s4_116 : Finset W := {15,7953,17476,35016,61986}
private def s4_117 : Finset W := {79,8017,8738,34952,61440}
private def s4_118 : Finset W := {79,4369,8738,36808,61440}
private def s4_119 : Finset W := {79,3904,4369,34952,61986}
private def s4_120 : Finset W := {79,3904,4369,8738,63624}
private def s4_121 : Finset W := {79,4433,8738,36744,61440}
private def s4_122 : Finset W := {79,3840,4433,34952,61986}
private def s4_123 : Finset W := {79,3840,4433,8738,63624}
private def s4_124 : Finset W := {79,7953,8802,34952,61440}
private def s4_125 : Finset W := {79,4369,8802,36744,61440}
private def s4_126 : Finset W := {79,3840,4369,34952,62050}
private def s4_127 : Finset W := {79,3840,4369,8802,63624}
private def s4_128 : Finset W := {79,7953,8738,35016,61440}
private def s4_129 : Finset W := {79,3840,4369,35016,61986}
private def s4_130 : Finset W := {79,3840,4369,8738,63688}
private def s4_131 : Finset W := {79,7953,8738,34952,61504}
private def s4_132 : Finset W := {79,4369,8738,36744,61504}
private def s4_133 : Finset W := {64,79,7953,34952,61986}
private def s4_134 : Finset W := {15,8017,8802,34952,61440}
private def s4_135 : Finset W := {15,4369,8802,36808,61440}
private def s4_136 : Finset W := {15,3904,4369,34952,62050}
private def s4_137 : Finset W := {15,3904,4369,8802,63624}
private def s4_138 : Finset W := {15,8017,8738,34952,61504}
private def s4_139 : Finset W := {15,64,8017,34952,61986}
private def s4_140 : Finset W := {15,4433,8802,36744,61440}
private def s4_141 : Finset W := {15,3840,4433,34952,62050}
private def s4_142 : Finset W := {15,3840,4433,8802,63624}
private def s4_143 : Finset W := {15,3840,4433,35016,61986}
private def s4_144 : Finset W := {15,3840,4433,8738,63688}
private def s4_145 : Finset W := {15,4433,8738,36744,61504}
private def s4_146 : Finset W := {15,7953,8802,35016,61440}
private def s4_147 : Finset W := {15,64,7953,34952,62050}
private def s4_148 : Finset W := {15,64,7953,35016,61986}
private def s4_149 : Finset W := {15,64,7953,36744,61986}
private def s4_150 : Finset W := {15,64,7953,39321,61986}
private def s4_151 : Finset W := {64,4111,7953,8738,34952}
private def s4_152 : Finset W := {15,64,7953,12834,34952}
private def s4_153 : Finset W := {15,64,4096,8738,40857}
private def s4_154 : Finset W := {15,64,7953,40857,61986}
private def s4_155 : Finset W := {15,64,7953,43690,61986}
private def s4_156 : Finset W := {15,64,7953,61986,63624}
private def s4_157 : Finset W := {15,64,7953,61986,64170}
private def s4_158 : Finset W := {64,527,4369,43690,61440}
private def s4_159 : Finset W := {64,527,4369,34952,61986}
private def s4_160 : Finset W := {64,527,4369,8738,63624}
private def s4_161 : Finset W := {15,64,4881,43690,61440}
private def s4_162 : Finset W := {15,64,4881,34952,61986}
private def s4_163 : Finset W := {15,64,4881,8738,63624}
private def s4_164 : Finset W := {15,64,512,4369,64170}
private def s4_165 : Finset W := {64,4111,4369,8738,36744}
private def s4_166 : Finset W := {15,64,4369,12834,36744}
private def s4_167 : Finset W := {64,3840,4111,8738,39321}
private def s4_168 : Finset W := {15,64,3840,12834,39321}
private def s4_169 : Finset W := {4111,7953,8738,17476,35064}
private def s4_170 : Finset W := {15,7953,12834,17476,35064}
private def s4_171 : Finset W := {527,4369,17476,35064,61986}
private def s4_172 : Finset W := {15,4881,17476,35064,61986}
private def s4_173 : Finset W := {240,4111,8738,17476,40857}
private def s4_174 : Finset W := {15,240,12834,17476,40857}
private def s4_175 : Finset W := {240,527,4369,43690,62532}
private def s4_176 : Finset W := {240,527,4369,17476,64170}
private def s4_177 : Finset W := {15,240,4881,43690,62532}
private def s4_178 : Finset W := {15,240,4881,17476,64170}
private def s4_179 : Finset W := {240,4111,8738,20292,39321}
private def s4_180 : Finset W := {15,240,12834,20292,39321}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_0 : search 4 s4_0 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_1 : search 4 s4_1 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_2 : search 4 s4_2 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_3 : search 4 s4_3 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_4 : search 4 s4_4 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_5 : search 4 s4_5 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_6 : search 4 s4_6 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_7 : search 4 s4_7 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_8 : search 4 s4_8 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_9 : search 4 s4_9 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_10 : search 4 s4_10 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_11 : search 4 s4_11 = false := by
  apply row (k := 2) (covered := [s3_0])
  · decide +kernel
  · exact allCons c3_0 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_12 : search 4 s4_12 = false := by
  apply row (k := 2) (covered := [s3_0])
  · decide +kernel
  · exact allCons c3_0 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_13 : search 4 s4_13 = false := by
  apply row (k := 2) (covered := [s3_0])
  · decide +kernel
  · exact allCons c3_0 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_14 : search 4 s4_14 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_15 : search 4 s4_15 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_16 : search 4 s4_16 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_17 : search 4 s4_17 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_18 : search 4 s4_18 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_19 : search 4 s4_19 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_20 : search 4 s4_20 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_21 : search 4 s4_21 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_22 : search 4 s4_22 = false := by
  apply row (k := 2) (covered := [s3_1])
  · decide +kernel
  · exact allCons c3_1 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_23 : search 4 s4_23 = false := by
  apply row (k := 2) (covered := [s3_1])
  · decide +kernel
  · exact allCons c3_1 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_24 : search 4 s4_24 = false := by
  apply row (k := 2) (covered := [s3_2])
  · decide +kernel
  · exact allCons c3_2 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_25 : search 4 s4_25 = false := by
  apply row (k := 2) (covered := [s3_2])
  · decide +kernel
  · exact allCons c3_2 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_26 : search 4 s4_26 = false := by
  apply row (k := 2) (covered := [s3_2])
  · decide +kernel
  · exact allCons c3_2 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_27 : search 4 s4_27 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_28 : search 4 s4_28 = false := by
  apply row (k := 2) (covered := [s3_3])
  · decide +kernel
  · exact allCons c3_3 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_29 : search 4 s4_29 = false := by
  apply row (k := 2) (covered := [s3_3])
  · decide +kernel
  · exact allCons c3_3 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_30 : search 4 s4_30 = false := by
  apply row (k := 2) (covered := [s3_4])
  · decide +kernel
  · exact allCons c3_4 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_31 : search 4 s4_31 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_32 : search 4 s4_32 = false := by
  apply row (k := 2) (covered := [s3_4])
  · decide +kernel
  · exact allCons c3_4 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_33 : search 4 s4_33 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_34 : search 4 s4_34 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_35 : search 4 s4_35 = false := by
  apply row (k := 2) (covered := [s3_5])
  · decide +kernel
  · exact allCons c3_5 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_36 : search 4 s4_36 = false := by
  apply row (k := 2) (covered := [s3_5])
  · decide +kernel
  · exact allCons c3_5 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_37 : search 4 s4_37 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_38 : search 4 s4_38 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_39 : search 4 s4_39 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_40 : search 4 s4_40 = false := by
  apply row (k := 2) (covered := [s3_6])
  · decide +kernel
  · exact allCons c3_6 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_41 : search 4 s4_41 = false := by
  apply row (k := 2) (covered := [s3_6])
  · decide +kernel
  · exact allCons c3_6 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_42 : search 4 s4_42 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_43 : search 4 s4_43 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_44 : search 4 s4_44 = false := by
  apply row (k := 2) (covered := [s3_5])
  · decide +kernel
  · exact allCons c3_5 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_45 : search 4 s4_45 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_46 : search 4 s4_46 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_47 : search 4 s4_47 = false := by
  apply row (k := 2) (covered := [s3_3])
  · decide +kernel
  · exact allCons c3_3 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_48 : search 4 s4_48 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_49 : search 4 s4_49 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_50 : search 4 s4_50 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_51 : search 4 s4_51 = false := by
  apply row (k := 2) (covered := [s3_4,s3_5])
  · decide +kernel
  · exact allCons c3_4 (allCons c3_5 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_52 : search 4 s4_52 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_53 : search 4 s4_53 = false := by
  apply row (k := 2) (covered := [s3_6,s3_3])
  · decide +kernel
  · exact allCons c3_6 (allCons c3_3 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_54 : search 4 s4_54 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_55 : search 4 s4_55 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_56 : search 4 s4_56 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_57 : search 4 s4_57 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_58 : search 4 s4_58 = false := by
  apply row (k := 2) (covered := [s3_7])
  · decide +kernel
  · exact allCons c3_7 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_59 : search 4 s4_59 = false := by
  apply row (k := 2) (covered := [s3_7])
  · decide +kernel
  · exact allCons c3_7 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_60 : search 4 s4_60 = false := by
  apply row (k := 2) (covered := [s3_7])
  · decide +kernel
  · exact allCons c3_7 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_61 : search 4 s4_61 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_62 : search 4 s4_62 = false := by
  apply row (k := 2) (covered := [s3_7])
  · decide +kernel
  · exact allCons c3_7 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_63 : search 4 s4_63 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_64 : search 4 s4_64 = false := by
  apply row (k := 2) (covered := [s3_8])
  · decide +kernel
  · exact allCons c3_8 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_65 : search 4 s4_65 = false := by
  apply row (k := 2) (covered := [s3_8])
  · decide +kernel
  · exact allCons c3_8 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_66 : search 4 s4_66 = false := by
  apply row (k := 2) (covered := [s3_8])
  · decide +kernel
  · exact allCons c3_8 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_67 : search 4 s4_67 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_68 : search 4 s4_68 = false := by
  apply row (k := 2) (covered := [s3_8])
  · decide +kernel
  · exact allCons c3_8 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_69 : search 4 s4_69 = false := by
  apply row (k := 2) (covered := [s3_2,s3_7,s3_8])
  · decide +kernel
  · exact allCons c3_2 (allCons c3_7 (allCons c3_8 (allNil 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_70 : search 4 s4_70 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_71 : search 4 s4_71 = false := by
  apply row (k := 2) (covered := [s3_1])
  · decide +kernel
  · exact allCons c3_1 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_72 : search 4 s4_72 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_73 : search 4 s4_73 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_74 : search 4 s4_74 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_75 : search 4 s4_75 = false := by
  apply row (k := 2) (covered := [s3_9])
  · decide +kernel
  · exact allCons c3_9 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_76 : search 4 s4_76 = false := by
  apply row (k := 2) (covered := [s3_9])
  · decide +kernel
  · exact allCons c3_9 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_77 : search 4 s4_77 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_78 : search 4 s4_78 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_79 : search 4 s4_79 = false := by
  apply row (k := 2) (covered := [s3_9])
  · decide +kernel
  · exact allCons c3_9 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_80 : search 4 s4_80 = false := by
  apply row (k := 2) (covered := [s3_9])
  · decide +kernel
  · exact allCons c3_9 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_81 : search 4 s4_81 = false := by
  apply row (k := 2) (covered := [s3_3])
  · decide +kernel
  · exact allCons c3_3 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_82 : search 4 s4_82 = false := by
  apply row (k := 2) (covered := [s3_3])
  · decide +kernel
  · exact allCons c3_3 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_83 : search 4 s4_83 = false := by
  apply row (k := 2) (covered := [s3_4,s3_10])
  · decide +kernel
  · exact allCons c3_4 (allCons c3_10 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_84 : search 4 s4_84 = false := by
  apply row (k := 2) (covered := [s3_10])
  · decide +kernel
  · exact allCons c3_10 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_85 : search 4 s4_85 = false := by
  apply row (k := 2) (covered := [s3_4])
  · decide +kernel
  · exact allCons c3_4 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_86 : search 4 s4_86 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_87 : search 4 s4_87 = false := by
  apply row (k := 2) (covered := [s3_10])
  · decide +kernel
  · exact allCons c3_10 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_88 : search 4 s4_88 = false := by
  apply row (k := 2) (covered := [s3_11])
  · decide +kernel
  · exact allCons c3_11 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_89 : search 4 s4_89 = false := by
  apply row (k := 2) (covered := [s3_12])
  · decide +kernel
  · exact allCons c3_12 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_90 : search 4 s4_90 = false := by
  apply row (k := 2) (covered := [s3_11,s3_12])
  · decide +kernel
  · exact allCons c3_11 (allCons c3_12 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_91 : search 4 s4_91 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_92 : search 4 s4_92 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_93 : search 4 s4_93 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_94 : search 4 s4_94 = false := by
  apply row (k := 2) (covered := [s3_5])
  · decide +kernel
  · exact allCons c3_5 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_95 : search 4 s4_95 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_96 : search 4 s4_96 = false := by
  apply row (k := 2) (covered := [s3_5])
  · decide +kernel
  · exact allCons c3_5 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_97 : search 4 s4_97 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_98 : search 4 s4_98 = false := by
  apply row (k := 2) (covered := [s3_13])
  · decide +kernel
  · exact allCons c3_13 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_99 : search 4 s4_99 = false := by
  apply row (k := 2) (covered := [s3_13])
  · decide +kernel
  · exact allCons c3_13 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_100 : search 4 s4_100 = false := by
  apply row (k := 2) (covered := [s3_13])
  · decide +kernel
  · exact allCons c3_13 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_101 : search 4 s4_101 = false := by
  apply row (k := 2) (covered := [s3_13])
  · decide +kernel
  · exact allCons c3_13 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_102 : search 4 s4_102 = false := by
  apply row (k := 2) (covered := [s3_14])
  · decide +kernel
  · exact allCons c3_14 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_103 : search 4 s4_103 = false := by
  apply row (k := 2) (covered := [s3_14])
  · decide +kernel
  · exact allCons c3_14 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_104 : search 4 s4_104 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_105 : search 4 s4_105 = false := by
  apply row (k := 2) (covered := [s3_15,s3_16])
  · decide +kernel
  · exact allCons c3_15 (allCons c3_16 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_106 : search 4 s4_106 = false := by
  apply row (k := 2) (covered := [s3_15])
  · decide +kernel
  · exact allCons c3_15 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_107 : search 4 s4_107 = false := by
  apply row (k := 2) (covered := [s3_16])
  · decide +kernel
  · exact allCons c3_16 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_108 : search 4 s4_108 = false := by
  apply row (k := 2) (covered := [s3_14,s3_6])
  · decide +kernel
  · exact allCons c3_14 (allCons c3_6 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_109 : search 4 s4_109 = false := by
  apply row (k := 2) (covered := [s3_6])
  · decide +kernel
  · exact allCons c3_6 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_110 : search 4 s4_110 = false := by
  apply row (k := 2) (covered := [s3_17])
  · decide +kernel
  · exact allCons c3_17 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_111 : search 4 s4_111 = false := by
  apply row (k := 2) (covered := [s3_17])
  · decide +kernel
  · exact allCons c3_17 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_112 : search 4 s4_112 = false := by
  apply row (k := 2) (covered := [s3_17])
  · decide +kernel
  · exact allCons c3_17 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_113 : search 4 s4_113 = false := by
  apply row (k := 2) (covered := [s3_17])
  · decide +kernel
  · exact allCons c3_17 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_114 : search 4 s4_114 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_115 : search 4 s4_115 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_116 : search 4 s4_116 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_117 : search 4 s4_117 = false := by
  apply row (k := 2) (covered := [s3_18])
  · decide +kernel
  · exact allCons c3_18 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_118 : search 4 s4_118 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_119 : search 4 s4_119 = false := by
  apply row (k := 2) (covered := [s3_18])
  · decide +kernel
  · exact allCons c3_18 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_120 : search 4 s4_120 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_121 : search 4 s4_121 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_122 : search 4 s4_122 = false := by
  apply row (k := 2) (covered := [s3_18])
  · decide +kernel
  · exact allCons c3_18 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_123 : search 4 s4_123 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_124 : search 4 s4_124 = false := by
  apply row (k := 2) (covered := [s3_19])
  · decide +kernel
  · exact allCons c3_19 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_125 : search 4 s4_125 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_126 : search 4 s4_126 = false := by
  apply row (k := 2) (covered := [s3_19])
  · decide +kernel
  · exact allCons c3_19 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_127 : search 4 s4_127 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_128 : search 4 s4_128 = false := by
  apply row (k := 2) (covered := [s3_20])
  · decide +kernel
  · exact allCons c3_20 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_129 : search 4 s4_129 = false := by
  apply row (k := 2) (covered := [s3_20])
  · decide +kernel
  · exact allCons c3_20 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_130 : search 4 s4_130 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_131 : search 4 s4_131 = false := by
  apply row (k := 2) (covered := [s3_19])
  · decide +kernel
  · exact allCons c3_19 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_132 : search 4 s4_132 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_133 : search 4 s4_133 = false := by
  apply row (k := 2) (covered := [s3_18,s3_20,s3_19])
  · decide +kernel
  · exact allCons c3_18 (allCons c3_20 (allCons c3_19 (allNil 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_134 : search 4 s4_134 = false := by
  apply row (k := 2) (covered := [s3_21])
  · decide +kernel
  · exact allCons c3_21 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_135 : search 4 s4_135 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_136 : search 4 s4_136 = false := by
  apply row (k := 2) (covered := [s3_21])
  · decide +kernel
  · exact allCons c3_21 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_137 : search 4 s4_137 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_138 : search 4 s4_138 = false := by
  apply row (k := 2) (covered := [s3_21])
  · decide +kernel
  · exact allCons c3_21 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_139 : search 4 s4_139 = false := by
  apply row (k := 2) (covered := [s3_18,s3_21])
  · decide +kernel
  · exact allCons c3_18 (allCons c3_21 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_140 : search 4 s4_140 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_141 : search 4 s4_141 = false := by
  apply row (k := 2) (covered := [s3_21])
  · decide +kernel
  · exact allCons c3_21 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_142 : search 4 s4_142 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_143 : search 4 s4_143 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_144 : search 4 s4_144 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_145 : search 4 s4_145 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_146 : search 4 s4_146 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_147 : search 4 s4_147 = false := by
  apply row (k := 2) (covered := [s3_19,s3_21])
  · decide +kernel
  · exact allCons c3_19 (allCons c3_21 (allNil 3))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_148 : search 4 s4_148 = false := by
  apply row (k := 2) (covered := [s3_20])
  · decide +kernel
  · exact allCons c3_20 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_149 : search 4 s4_149 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_150 : search 4 s4_150 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_151 : search 4 s4_151 = false := by
  apply row (k := 2) (covered := [s3_22])
  · decide +kernel
  · exact allCons c3_22 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_152 : search 4 s4_152 = false := by
  apply row (k := 2) (covered := [s3_23])
  · decide +kernel
  · exact allCons c3_23 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_153 : search 4 s4_153 = false := by
  apply row (k := 2) (covered := [s3_22,s3_9,s3_23])
  · decide +kernel
  · exact allCons c3_22 (allCons c3_9 (allCons c3_23 (allNil 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_154 : search 4 s4_154 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_155 : search 4 s4_155 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_156 : search 4 s4_156 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_157 : search 4 s4_157 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_158 : search 4 s4_158 = false := by
  apply row (k := 2) (covered := [s3_24])
  · decide +kernel
  · exact allCons c3_24 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_159 : search 4 s4_159 = false := by
  apply row (k := 2) (covered := [s3_24])
  · decide +kernel
  · exact allCons c3_24 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_160 : search 4 s4_160 = false := by
  apply row (k := 2) (covered := [s3_24])
  · decide +kernel
  · exact allCons c3_24 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_161 : search 4 s4_161 = false := by
  apply row (k := 2) (covered := [s3_25])
  · decide +kernel
  · exact allCons c3_25 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_162 : search 4 s4_162 = false := by
  apply row (k := 2) (covered := [s3_25])
  · decide +kernel
  · exact allCons c3_25 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_163 : search 4 s4_163 = false := by
  apply row (k := 2) (covered := [s3_25])
  · decide +kernel
  · exact allCons c3_25 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_164 : search 4 s4_164 = false := by
  apply row (k := 2) (covered := [s3_24,s3_13,s3_25])
  · decide +kernel
  · exact allCons c3_24 (allCons c3_13 (allCons c3_25 (allNil 3)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_165 : search 4 s4_165 = false := by
  apply row (k := 2) (covered := [s3_22])
  · decide +kernel
  · exact allCons c3_22 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_166 : search 4 s4_166 = false := by
  apply row (k := 2) (covered := [s3_23])
  · decide +kernel
  · exact allCons c3_23 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_167 : search 4 s4_167 = false := by
  apply row (k := 2) (covered := [s3_22])
  · decide +kernel
  · exact allCons c3_22 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_168 : search 4 s4_168 = false := by
  apply row (k := 2) (covered := [s3_23])
  · decide +kernel
  · exact allCons c3_23 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_169 : search 4 s4_169 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_170 : search 4 s4_170 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_171 : search 4 s4_171 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_172 : search 4 s4_172 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_173 : search 4 s4_173 = false := by
  apply row (k := 2) (covered := [s3_22])
  · decide +kernel
  · exact allCons c3_22 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_174 : search 4 s4_174 = false := by
  apply row (k := 2) (covered := [s3_23])
  · decide +kernel
  · exact allCons c3_23 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_175 : search 4 s4_175 = false := by
  apply row (k := 2) (covered := [s3_10])
  · decide +kernel
  · exact allCons c3_10 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_176 : search 4 s4_176 = false := by
  apply row (k := 2) (covered := [s3_24])
  · decide +kernel
  · exact allCons c3_24 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_177 : search 4 s4_177 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_178 : search 4 s4_178 = false := by
  apply row (k := 2) (covered := [s3_25])
  · decide +kernel
  · exact allCons c3_25 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_179 : search 4 s4_179 = false := by
  apply row (k := 2) (covered := [s3_14])
  · decide +kernel
  · exact allCons c3_14 (allNil 3)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c4_180 : search 4 s4_180 = false := by
  apply row (k := 2) (covered := [])
  · decide +kernel
  · exact allNil 3
private def s5_0 : Finset W := {3840,4593,8738,17487,34952,61440}
private def s5_1 : Finset W := {3840,4369,8946,17487,34952,61440}
private def s5_2 : Finset W := {3840,4369,8738,17487,35064,61440}
private def s5_3 : Finset W := {15,4593,8738,17476,36744,61440}
private def s5_4 : Finset W := {15,3840,4593,8738,34952,62532}
private def s5_5 : Finset W := {15,4369,8946,20292,34952,61440}
private def s5_6 : Finset W := {15,3840,4369,8946,17476,63624}
private def s5_7 : Finset W := {15,64,7953,8738,34952,61440}
private def s5_8 : Finset W := {15,64,4369,8738,36744,61440}
private def s5_9 : Finset W := {15,64,3840,4369,34952,61986}
private def s5_10 : Finset W := {15,64,3840,4369,8738,63624}
private def s5_11 : Finset W := {15,7953,8738,17476,35064,61440}
private def s5_12 : Finset W := {15,3840,4369,17476,35064,61986}
private def s5_13 : Finset W := {15,240,7953,17476,34952,61986}
private def s5_14 : Finset W := {15,240,4369,8738,20292,63624}
private def s5_15 : Finset W := {15,240,4369,8738,36744,62532}
private def s5_16 : Finset W := {3855,4593,8738,17487,34952,61440}
private def s5_17 : Finset W := {3855,4369,8946,17487,34952,61440}
private def s5_18 : Finset W := {3855,4369,8738,17487,35064,61440}
private def s5_19 : Finset W := {240,514,4369,17487,34952,61440}
private def s5_20 : Finset W := {240,3855,4369,17487,34952,61986}
private def s5_21 : Finset W := {240,3855,4369,8738,34952,62543}
private def s5_22 : Finset W := {240,3855,4369,8738,17487,63624}
private def s5_23 : Finset W := {3855,4593,8738,17476,34952,61455}
private def s5_24 : Finset W := {3855,4369,8946,17476,34952,61455}
private def s5_25 : Finset W := {64,3855,4369,8738,34952,61455}
private def s5_26 : Finset W := {3855,4369,8738,17476,35064,61455}
private def s5_27 : Finset W := {240,4369,8738,20303,34952,61455}
private def s5_28 : Finset W := {15,514,4593,17476,34952,61440}
private def s5_29 : Finset W := {15,3855,4593,8738,34952,62532}
private def s5_30 : Finset W := {15,4369,8946,20303,34952,61440}
private def s5_31 : Finset W := {15,3855,4369,8946,17476,63624}
private def s5_32 : Finset W := {15,64,514,4369,34952,61440}
private def s5_33 : Finset W := {15,64,3855,4369,34952,61986}
private def s5_34 : Finset W := {15,64,3855,4369,8738,63624}
private def s5_35 : Finset W := {15,514,4369,17476,35064,61440}
private def s5_36 : Finset W := {15,3855,4369,17476,35064,61986}
private def s5_37 : Finset W := {15,240,514,4369,34952,62532}
private def s5_38 : Finset W := {15,240,514,4369,17476,63624}
private def s5_39 : Finset W := {15,240,4369,8738,20303,63624}
private def s5_40 : Finset W := {248,3840,4369,8738,17487,61440}
private def s5_41 : Finset W := {240,3840,4377,8738,17487,61440}
private def s5_42 : Finset W := {240,3840,4369,8746,17487,61440}
private def s5_43 : Finset W := {8,3840,4593,8738,17487,61440}
private def s5_44 : Finset W := {8,3840,4369,8946,17487,61440}
private def s5_45 : Finset W := {3840,4593,8738,17487,34952,61455}
private def s5_46 : Finset W := {3840,4369,8946,17487,34952,61455}
private def s5_47 : Finset W := {3840,4369,8738,17487,35064,61455}
private def s5_48 : Finset W := {240,7953,8738,17487,34952,61455}
private def s5_49 : Finset W := {240,4369,8738,17487,36744,61455}
private def s5_50 : Finset W := {240,3840,4097,8738,17487,34952}
private def s5_51 : Finset W := {15,4593,8738,17487,36744,61440}
private def s5_52 : Finset W := {15,3840,4593,8738,34952,62543}
private def s5_53 : Finset W := {15,3840,4369,8946,17487,63624}
private def s5_54 : Finset W := {15,7953,8738,17487,35064,61440}
private def s5_55 : Finset W := {15,3840,4369,17487,35064,61986}
private def s5_56 : Finset W := {15,72,3840,4369,8738,61440}
private def s5_57 : Finset W := {15,240,7953,17487,34952,61986}
private def s5_58 : Finset W := {15,240,4369,8738,36744,62543}
private def s5_59 : Finset W := {4593,8738,17487,20292,34952,61440}
private def s5_60 : Finset W := {3840,4593,8738,17487,34952,62532}
private def s5_61 : Finset W := {4369,8946,17487,20292,34952,61440}
private def s5_62 : Finset W := {3840,4369,8946,17487,34952,62532}
private def s5_63 : Finset W := {3840,4433,8738,17487,34952,61440}
private def s5_64 : Finset W := {3840,4369,8802,17487,34952,61440}
private def s5_65 : Finset W := {3840,4369,8738,17487,35016,61440}
private def s5_66 : Finset W := {4369,8738,17487,20292,35064,61440}
private def s5_67 : Finset W := {3840,4369,8738,17487,35064,62532}
private def s5_68 : Finset W := {3840,4593,8946,17487,34952,61440}
private def s5_69 : Finset W := {3840,4593,8738,17487,35064,61440}
private def s5_70 : Finset W := {4593,7953,8738,17487,34952,61440}
private def s5_71 : Finset W := {3840,4593,8738,17487,39321,61440}
private def s5_72 : Finset W := {3840,4096,4593,8738,17487,34952}
private def s5_73 : Finset W := {3840,4369,8738,17487,39417,61440}
private def s5_74 : Finset W := {512,4593,8738,17487,34952,61440}
private def s5_75 : Finset W := {4593,8738,17487,20303,34952,61440}
private def s5_76 : Finset W := {4593,8738,17487,34952,36744,61440}
private def s5_77 : Finset W := {3840,4593,8738,17487,39417,61440}
private def s5_78 : Finset W := {3840,4593,8738,17487,43690,61440}
private def s5_79 : Finset W := {3840,4593,8738,17487,34952,62543}
private def s5_80 : Finset W := {3840,4369,8946,17487,35064,61440}
private def s5_81 : Finset W := {512,4369,8946,17487,34952,61440}
private def s5_82 : Finset W := {3840,4369,8946,17487,43690,61440}
private def s5_83 : Finset W := {3840,4369,8946,17487,34952,61986}
private def s5_84 : Finset W := {3840,4369,8738,17487,43770,61440}
private def s5_85 : Finset W := {4369,8946,17487,20303,34952,61440}
private def s5_86 : Finset W := {3840,4369,8946,17487,39321,61440}
private def s5_87 : Finset W := {3840,4096,4369,8946,17487,34952}
private def s5_88 : Finset W := {3840,4369,8946,17487,43770,61440}
private def s5_89 : Finset W := {3840,4369,8946,17487,34952,62543}
private def s5_90 : Finset W := {3840,4369,8946,17487,34952,63624}
private def s5_91 : Finset W := {4369,8738,17487,35064,36744,61440}
private def s5_92 : Finset W := {3840,4369,8738,17487,35064,63624}
private def s5_93 : Finset W := {4369,7953,8738,17487,35064,61440}
private def s5_94 : Finset W := {512,4369,8738,17487,35064,61440}
private def s5_95 : Finset W := {4369,8738,17487,20303,35064,61440}
private def s5_96 : Finset W := {3840,4096,4369,8738,17487,35064}
private def s5_97 : Finset W := {3840,4369,8738,17487,35064,61986}
private def s5_98 : Finset W := {72,3840,4369,8738,17487,61440}
private def s5_99 : Finset W := {3840,4369,8738,17487,35064,62543}
private def s5_100 : Finset W := {240,7953,8738,17487,39321,61440}
private def s5_101 : Finset W := {240,4881,8738,17487,34952,61440}
private def s5_102 : Finset W := {240,4369,8738,17999,34952,61440}
private def s5_103 : Finset W := {240,4369,8738,17487,35464,61440}
private def s5_104 : Finset W := {240,512,4369,17487,43690,61440}
private def s5_105 : Finset W := {240,4369,8738,20303,34952,62543}
private def s5_106 : Finset W := {240,4369,8738,17487,36744,63624}
private def s5_107 : Finset W := {240,3840,4096,8738,17487,39321}
private def s5_108 : Finset W := {240,3840,4369,12834,17487,34952}
private def s5_109 : Finset W := {240,3840,4369,8738,21583,34952}
private def s5_110 : Finset W := {240,3840,4369,8738,17487,39048}
private def s5_111 : Finset W := {240,3840,4369,17487,43690,61986}
private def s5_112 : Finset W := {15,3840,4601,8738,17476,61440}
private def s5_113 : Finset W := {15,3840,4369,8954,17476,61440}
private def s5_114 : Finset W := {15,248,7953,8738,17476,61440}
private def s5_115 : Finset W := {15,248,4369,8738,20292,61440}
private def s5_116 : Finset W := {15,248,3840,4369,17476,61986}
private def s5_117 : Finset W := {15,248,3840,4369,8738,62532}
private def s5_118 : Finset W := {15,3848,4593,8738,17476,61440}
private def s5_119 : Finset W := {15,3848,4369,8946,17476,61440}
private def s5_120 : Finset W := {15,64,3848,4369,8738,61440}
private def s5_121 : Finset W := {15,240,7961,8738,17476,61440}
private def s5_122 : Finset W := {15,240,3848,4369,17476,61986}
private def s5_123 : Finset W := {15,240,3848,4369,8738,62532}
private def s5_124 : Finset W := {15,3840,4377,8946,17476,61440}
private def s5_125 : Finset W := {15,64,3840,4377,8738,61440}
private def s5_126 : Finset W := {15,240,4377,8738,20292,61440}
private def s5_127 : Finset W := {15,240,3840,4377,17476,61986}
private def s5_128 : Finset W := {15,240,3840,4377,8738,62532}
private def s5_129 : Finset W := {15,3840,4593,8746,17476,61440}
private def s5_130 : Finset W := {15,64,3840,4369,8746,61440}
private def s5_131 : Finset W := {15,240,7953,8746,17476,61440}
private def s5_132 : Finset W := {15,240,4369,8746,20292,61440}
private def s5_133 : Finset W := {15,240,3840,4369,17476,61994}
private def s5_134 : Finset W := {15,240,3840,4369,8746,62532}
private def s5_135 : Finset W := {15,3840,4593,8738,17476,61448}
private def s5_136 : Finset W := {15,3840,4369,8946,17476,61448}
private def s5_137 : Finset W := {15,64,3840,4369,8738,61448}
private def s5_138 : Finset W := {15,240,7953,8738,17476,61448}
private def s5_139 : Finset W := {15,240,4369,8738,20292,61448}
private def s5_140 : Finset W := {8,15,3840,4593,8738,62532}
private def s5_141 : Finset W := {8,15,4369,8946,20292,61440}
private def s5_142 : Finset W := {8,15,64,7953,8738,61440}
private def s5_143 : Finset W := {8,15,64,3840,4369,61986}
private def s5_144 : Finset W := {8,15,240,7953,17476,61986}
private def s5_145 : Finset W := {15,4593,8738,17476,36744,61455}
private def s5_146 : Finset W := {15,4369,8946,20292,34952,61455}
private def s5_147 : Finset W := {15,3840,4097,8946,17476,34952}
private def s5_148 : Finset W := {15,64,7953,8738,34952,61455}
private def s5_149 : Finset W := {15,64,4369,8738,36744,61455}
private def s5_150 : Finset W := {15,64,3840,4097,8738,34952}
private def s5_151 : Finset W := {15,7953,8738,17476,35064,61455}
private def s5_152 : Finset W := {15,3840,4097,8738,17476,35064}
private def s5_153 : Finset W := {15,240,4097,8738,20292,34952}
private def s5_154 : Finset W := {15,240,4097,8738,17476,36744}
private def s5_155 : Finset W := {15,4593,8946,20292,34952,61440}
private def s5_156 : Finset W := {15,3840,4593,8946,34952,62532}
private def s5_157 : Finset W := {79,3840,4593,8738,34952,61440}
private def s5_158 : Finset W := {15,3840,4593,8738,34952,61504}
private def s5_159 : Finset W := {15,64,4593,8738,36744,61440}
private def s5_160 : Finset W := {15,4593,8738,20292,35064,61440}
private def s5_161 : Finset W := {15,3840,4593,8738,35064,62532}
private def s5_162 : Finset W := {15,240,4593,8738,36744,62532}
private def s5_163 : Finset W := {15,7953,8738,17476,39417,61440}
private def s5_164 : Finset W := {15,4593,8738,17476,40857,61440}
private def s5_165 : Finset W := {15,4593,7953,17476,34952,61986}
private def s5_166 : Finset W := {15,4593,7953,8738,34952,62532}
private def s5_167 : Finset W := {15,4593,7953,8738,17476,63624}
private def s5_168 : Finset W := {15,4096,4593,8738,17476,36744}
private def s5_169 : Finset W := {15,4369,4593,8738,36744,62532}
private def s5_170 : Finset W := {15,3840,4593,17476,39321,61986}
private def s5_171 : Finset W := {15,3840,4593,8738,39321,62532}
private def s5_172 : Finset W := {3840,4111,4593,8738,17476,34952}
private def s5_173 : Finset W := {15,3840,4593,8738,21572,34952}
private def s5_174 : Finset W := {15,3840,4096,8738,17476,39417}
private def s5_175 : Finset W := {15,3840,4369,17476,39417,61986}
private def s5_176 : Finset W := {15,3840,4160,4369,8738,34952}
private def s5_177 : Finset W := {527,4593,8738,17476,34952,61440}
private def s5_178 : Finset W := {15,4593,8738,17988,34952,61440}
private def s5_179 : Finset W := {15,4593,8738,17476,35464,61440}
private def s5_180 : Finset W := {15,512,4593,17476,43690,61440}
private def s5_181 : Finset W := {15,512,4593,8738,34952,62532}
private def s5_182 : Finset W := {15,4593,8738,20292,34952,62532}
private def s5_183 : Finset W := {15,3840,4593,8738,36744,62532}
private def s5_184 : Finset W := {15,4593,8738,34952,36744,62532}
private def s5_185 : Finset W := {15,4593,8738,17476,36744,62532}
private def s5_186 : Finset W := {15,4593,8738,36744,61440,62532}
private def s5_187 : Finset W := {15,4593,8738,36744,62532}
private def s5_188 : Finset W := {15,3840,4593,8738,39417,62532}
private def s5_189 : Finset W := {15,3840,4593,8738,43690,62532}
private def s5_190 : Finset W := {15,3840,4593,34952,61986,62532}
private def s5_191 : Finset W := {15,3840,4593,17476,61986,63624}
private def s5_192 : Finset W := {15,3840,4593,8738,62532,63624}
private def s5_193 : Finset W := {15,3840,4160,4593,8738,34952}
private def s5_194 : Finset W := {79,3840,4369,8946,34952,61440}
private def s5_195 : Finset W := {15,3904,4369,8946,34952,61440}
private def s5_196 : Finset W := {15,64,3840,4369,8946,63624}
private def s5_197 : Finset W := {15,4369,8946,20292,35064,61440}
private def s5_198 : Finset W := {15,3840,4369,8946,35064,62532}
private def s5_199 : Finset W := {15,240,4369,8946,20292,63624}
private def s5_200 : Finset W := {15,7953,8946,17476,43690,61440}
private def s5_201 : Finset W := {15,7953,8946,17476,34952,61986}
private def s5_202 : Finset W := {15,7953,8738,17476,43770,61440}
private def s5_203 : Finset W := {527,4369,8946,17476,34952,61440}
private def s5_204 : Finset W := {15,4369,8946,17988,34952,61440}
private def s5_205 : Finset W := {15,512,4369,17476,43770,61440}
private def s5_206 : Finset W := {15,512,4369,8946,17476,63624}
private def s5_207 : Finset W := {15,4369,8946,20292,43690,61440}
private def s5_208 : Finset W := {15,4369,8946,20292,34952,61986}
private def s5_209 : Finset W := {15,576,4369,8738,34952,61440}
private def s5_210 : Finset W := {15,4369,8738,8946,20292,63624}
private def s5_211 : Finset W := {15,4369,8946,17476,36744,61986}
private def s5_212 : Finset W := {15,3840,4369,8946,17476,64170}
private def s5_213 : Finset W := {15,3840,4369,17476,43770,61986}
private def s5_214 : Finset W := {15,7953,8946,20292,34952,61440}
private def s5_215 : Finset W := {15,7953,8946,17476,36744,61440}
private def s5_216 : Finset W := {15,4369,8946,20292,36744,61440}
private def s5_217 : Finset W := {15,3840,4369,8946,20292,63624}
private def s5_218 : Finset W := {15,4369,8946,20292,34952,62532}
private def s5_219 : Finset W := {15,4369,8946,17476,20292,63624}
private def s5_220 : Finset W := {15,4369,8946,20292,39321,61440}
private def s5_221 : Finset W := {15,4096,4369,8946,20292,34952}
private def s5_222 : Finset W := {15,576,4369,8946,34952,61440}
private def s5_223 : Finset W := {15,4369,8946,20292,43770,61440}
private def s5_224 : Finset W := {15,4369,8946,20292,34952,63624}
private def s5_225 : Finset W := {15,4369,8946,20292,61440,63624}
private def s5_226 : Finset W := {15,4369,8946,20292,63624}
private def s5_227 : Finset W := {15,3840,4096,8946,17476,39321}
private def s5_228 : Finset W := {3840,4111,4369,8946,17476,34952}
private def s5_229 : Finset W := {15,3840,4369,8946,21572,34952}
private def s5_230 : Finset W := {15,3840,4369,8946,17476,39048}
private def s5_231 : Finset W := {79,3840,4369,8738,35064,61440}
private def s5_232 : Finset W := {79,240,7953,8738,34952,61440}
private def s5_233 : Finset W := {79,240,4369,8738,36744,61440}
private def s5_234 : Finset W := {79,240,3840,4369,34952,61986}
private def s5_235 : Finset W := {79,240,3840,4369,8738,63624}
private def s5_236 : Finset W := {15,240,3904,4369,34952,61986}
private def s5_237 : Finset W := {15,240,3904,4369,8738,63624}
private def s5_238 : Finset W := {15,240,7953,8738,34952,61504}
private def s5_239 : Finset W := {15,240,4369,8738,36744,61504}
private def s5_240 : Finset W := {15,64,7953,8738,35064,61440}
private def s5_241 : Finset W := {15,64,3840,4369,35064,61986}
private def s5_242 : Finset W := {15,64,240,7953,34952,61986}
private def s5_243 : Finset W := {15,4433,8738,17476,36744,61440}
private def s5_244 : Finset W := {15,3840,4433,17476,34952,61986}
private def s5_245 : Finset W := {15,3840,4433,8738,34952,62532}
private def s5_246 : Finset W := {15,3840,4433,8738,17476,63624}
private def s5_247 : Finset W := {15,7953,8802,17476,34952,61440}
private def s5_248 : Finset W := {15,4369,8802,20292,34952,61440}
private def s5_249 : Finset W := {15,4369,8802,17476,36744,61440}
private def s5_250 : Finset W := {15,3840,4369,8802,17476,63624}
private def s5_251 : Finset W := {15,7953,8738,17476,35016,61440}
private def s5_252 : Finset W := {15,3840,4369,17476,35016,61986}
private def s5_253 : Finset W := {15,64,7953,17476,34952,61986}
private def s5_254 : Finset W := {15,64,4369,8738,20292,63624}
private def s5_255 : Finset W := {15,64,4369,8738,36744,62532}
private def s5_256 : Finset W := {79,3904,4369,8738,34952,61440}
private def s5_257 : Finset W := {79,3840,4433,8738,34952,61440}
private def s5_258 : Finset W := {79,3840,4369,8802,34952,61440}
private def s5_259 : Finset W := {79,3840,4369,8738,35016,61440}
private def s5_260 : Finset W := {79,3840,4369,8738,34952,61504}
private def s5_261 : Finset W := {64,79,7953,8738,34952,61440}
private def s5_262 : Finset W := {64,79,4369,8738,36744,61440}
private def s5_263 : Finset W := {64,79,3840,4369,34952,61986}
private def s5_264 : Finset W := {64,79,3840,4369,8738,63624}
private def s5_265 : Finset W := {15,3904,4369,8802,34952,61440}
private def s5_266 : Finset W := {15,3904,4369,8738,34952,61504}
private def s5_267 : Finset W := {15,64,8017,8738,34952,61440}
private def s5_268 : Finset W := {15,64,4369,8738,36808,61440}
private def s5_269 : Finset W := {15,64,3904,4369,34952,61986}
private def s5_270 : Finset W := {15,64,3904,4369,8738,63624}
private def s5_271 : Finset W := {15,3840,4433,8802,34952,61440}
private def s5_272 : Finset W := {15,3840,4433,8738,35016,61440}
private def s5_273 : Finset W := {15,3840,4433,8738,34952,61504}
private def s5_274 : Finset W := {15,64,4433,8738,36744,61440}
private def s5_275 : Finset W := {15,64,3840,4433,34952,61986}
private def s5_276 : Finset W := {15,64,3840,4433,8738,63624}
private def s5_277 : Finset W := {15,3840,4369,8802,35016,61440}
private def s5_278 : Finset W := {15,64,7953,8802,34952,61440}
private def s5_279 : Finset W := {15,64,4369,8802,36744,61440}
private def s5_280 : Finset W := {15,64,3840,4369,34952,62050}
private def s5_281 : Finset W := {15,64,3840,4369,8802,63624}
private def s5_282 : Finset W := {15,64,7953,8738,35016,61440}
private def s5_283 : Finset W := {15,64,3840,4369,35016,61986}
private def s5_284 : Finset W := {15,64,3840,4369,8738,63688}
private def s5_285 : Finset W := {15,64,7953,8738,34952,61504}
private def s5_286 : Finset W := {15,64,4369,8738,36744,61504}
private def s5_287 : Finset W := {15,64,7953,8738,36744,61440}
private def s5_288 : Finset W := {15,64,3840,7953,34952,61986}
private def s5_289 : Finset W := {15,64,7953,8738,39321,61440}
private def s5_290 : Finset W := {15,64,4096,7953,8738,34952}
private def s5_291 : Finset W := {15,64,4369,8738,40857,61440}
private def s5_292 : Finset W := {15,64,4369,7953,34952,61986}
private def s5_293 : Finset W := {15,64,4369,7953,8738,63624}
private def s5_294 : Finset W := {15,64,7953,8738,40857,61440}
private def s5_295 : Finset W := {15,64,7953,8738,43690,61440}
private def s5_296 : Finset W := {15,64,7953,8738,34952,61986}
private def s5_297 : Finset W := {15,64,7953,34952,61440,61986}
private def s5_298 : Finset W := {15,64,7953,34952,61986}
private def s5_299 : Finset W := {15,64,7953,8738,61440,63624}
private def s5_300 : Finset W := {64,527,4369,8738,34952,61440}
private def s5_301 : Finset W := {15,64,4881,8738,34952,61440}
private def s5_302 : Finset W := {15,64,4369,8738,35464,61440}
private def s5_303 : Finset W := {15,64,512,4369,43690,61440}
private def s5_304 : Finset W := {15,64,512,4369,34952,61986}
private def s5_305 : Finset W := {15,64,512,4369,8738,63624}
private def s5_306 : Finset W := {15,64,3840,4369,36744,61986}
private def s5_307 : Finset W := {15,64,4369,8738,36744,63624}
private def s5_308 : Finset W := {15,64,4096,4369,8738,36744}
private def s5_309 : Finset W := {15,64,4369,8738,36744,61986}
private def s5_310 : Finset W := {15,64,3840,4096,8738,39321}
private def s5_311 : Finset W := {15,64,3840,4369,39321,61986}
private def s5_312 : Finset W := {64,3840,4111,4369,8738,34952}
private def s5_313 : Finset W := {15,64,3840,4369,12834,34952}
private def s5_314 : Finset W := {15,64,3840,4369,8738,39048}
private def s5_315 : Finset W := {15,64,3840,4369,43690,61986}
private def s5_316 : Finset W := {15,64,3840,4369,8738,64170}
private def s5_317 : Finset W := {15,64,3840,4369,61986,63624}
private def s5_318 : Finset W := {15,64,3840,4369,61986,64170}
private def s5_319 : Finset W := {15,240,7953,17476,35064,61986}
private def s5_320 : Finset W := {15,7953,17476,34952,35064,61986}
private def s5_321 : Finset W := {15,3840,7953,17476,35064,61986}
private def s5_322 : Finset W := {15,4096,7953,8738,17476,35064}
private def s5_323 : Finset W := {15,4369,7953,17476,35064,61986}
private def s5_324 : Finset W := {15,7953,8738,17476,35064,61986}
private def s5_325 : Finset W := {15,7953,17476,35064,61440,61986}
private def s5_326 : Finset W := {15,7953,17476,35064,61986}
private def s5_327 : Finset W := {527,4369,8738,17476,35064,61440}
private def s5_328 : Finset W := {15,4881,8738,17476,35064,61440}
private def s5_329 : Finset W := {15,4369,8738,17988,35064,61440}
private def s5_330 : Finset W := {15,512,4369,17476,35064,61986}
private def s5_331 : Finset W := {15,4369,8738,20292,35064,62532}
private def s5_332 : Finset W := {3840,4111,4369,8738,17476,35064}
private def s5_333 : Finset W := {15,3840,4369,12834,17476,35064}
private def s5_334 : Finset W := {15,3840,4369,8738,21572,35064}
private def s5_335 : Finset W := {15,240,7953,20292,34952,61986}
private def s5_336 : Finset W := {15,240,7953,17476,36744,61986}
private def s5_337 : Finset W := {15,240,7953,17476,39321,61986}
private def s5_338 : Finset W := {15,240,7953,8738,39321,62532}
private def s5_339 : Finset W := {240,4111,7953,8738,17476,34952}
private def s5_340 : Finset W := {15,240,7953,12834,17476,34952}
private def s5_341 : Finset W := {15,240,4096,8738,17476,40857}
private def s5_342 : Finset W := {15,240,4369,8738,40857,62532}
private def s5_343 : Finset W := {15,240,7953,17476,40857,61986}
private def s5_344 : Finset W := {15,240,7953,17476,43690,61986}
private def s5_345 : Finset W := {15,240,7953,34952,61986,62532}
private def s5_346 : Finset W := {15,240,7953,17476,61986,63624}
private def s5_347 : Finset W := {15,240,7953,17476,61986,64170}
private def s5_348 : Finset W := {15,240,7953,8738,62532,63624}
private def s5_349 : Finset W := {240,527,4369,17476,43690,61440}
private def s5_350 : Finset W := {240,527,4369,17476,34952,61986}
private def s5_351 : Finset W := {240,527,4369,8738,34952,62532}
private def s5_352 : Finset W := {240,527,4369,8738,17476,63624}
private def s5_353 : Finset W := {15,240,4881,17476,43690,61440}
private def s5_354 : Finset W := {15,240,4881,17476,34952,61986}
private def s5_355 : Finset W := {15,240,4881,8738,34952,62532}
private def s5_356 : Finset W := {15,240,4881,8738,17476,63624}
private def s5_357 : Finset W := {15,240,4369,17988,43690,61440}
private def s5_358 : Finset W := {15,240,4369,8738,17988,63624}
private def s5_359 : Finset W := {15,240,4369,8738,35464,62532}
private def s5_360 : Finset W := {15,240,512,4369,43690,62532}
private def s5_361 : Finset W := {15,240,512,4369,17476,64170}
private def s5_362 : Finset W := {15,240,4369,20292,36744,61986}
private def s5_363 : Finset W := {15,240,4096,8738,20292,39321}
private def s5_364 : Finset W := {240,4111,4369,8738,20292,34952}
private def s5_365 : Finset W := {15,240,4369,12834,20292,34952}
private def s5_366 : Finset W := {15,240,4369,8738,20292,39048}
private def s5_367 : Finset W := {15,240,4369,20292,43690,61986}
private def s5_368 : Finset W := {15,240,4369,8738,20292,64170}
private def s5_369 : Finset W := {240,4111,4369,8738,17476,36744}
private def s5_370 : Finset W := {15,240,4369,12834,17476,36744}
private def s5_371 : Finset W := {15,240,4369,8738,21572,36744}
private def s5_372 : Finset W := {240,3840,4111,8738,17476,39321}
private def s5_373 : Finset W := {15,240,3840,12834,17476,39321}
private def s5_374 : Finset W := {15,240,3840,8738,21572,39321}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_0 : search 5 s5_0 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_1 : search 5 s5_1 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_2 : search 5 s5_2 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_3 : search 5 s5_3 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_4 : search 5 s5_4 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_5 : search 5 s5_5 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_6 : search 5 s5_6 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_7 : search 5 s5_7 = false := by
  apply row (k := 3) (covered := [s4_2])
  · decide +kernel
  · exact allCons c4_2 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_8 : search 5 s5_8 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_9 : search 5 s5_9 = false := by
  apply row (k := 3) (covered := [s4_2])
  · decide +kernel
  · exact allCons c4_2 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_10 : search 5 s5_10 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_11 : search 5 s5_11 = false := by
  apply row (k := 3) (covered := [s4_3])
  · decide +kernel
  · exact allCons c4_3 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_12 : search 5 s5_12 = false := by
  apply row (k := 3) (covered := [s4_3])
  · decide +kernel
  · exact allCons c4_3 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_13 : search 5 s5_13 = false := by
  apply row (k := 3) (covered := [s4_2,s4_3])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_3 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_14 : search 5 s5_14 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_15 : search 5 s5_15 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_16 : search 5 s5_16 = false := by
  apply row (k := 3) (covered := [s4_4,s4_5])
  · decide +kernel
  · exact allCons c4_4 (allCons c4_5 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_17 : search 5 s5_17 = false := by
  apply row (k := 3) (covered := [s4_6])
  · decide +kernel
  · exact allCons c4_6 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_18 : search 5 s5_18 = false := by
  apply row (k := 3) (covered := [s4_7,s4_8])
  · decide +kernel
  · exact allCons c4_7 (allCons c4_8 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_19 : search 5 s5_19 = false := by
  apply row (k := 3) (covered := [s4_4,s4_7])
  · decide +kernel
  · exact allCons c4_4 (allCons c4_7 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_20 : search 5 s5_20 = false := by
  apply row (k := 3) (covered := [s4_8])
  · decide +kernel
  · exact allCons c4_8 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_21 : search 5 s5_21 = false := by
  apply row (k := 3) (covered := [s4_5])
  · decide +kernel
  · exact allCons c4_5 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_22 : search 5 s5_22 = false := by
  apply row (k := 3) (covered := [s4_6])
  · decide +kernel
  · exact allCons c4_6 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_23 : search 5 s5_23 = false := by
  apply row (k := 3) (covered := [s4_5])
  · decide +kernel
  · exact allCons c4_5 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_24 : search 5 s5_24 = false := by
  apply row (k := 3) (covered := [s4_9])
  · decide +kernel
  · exact allCons c4_9 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_25 : search 5 s5_25 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_26 : search 5 s5_26 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_27 : search 5 s5_27 = false := by
  apply row (k := 3) (covered := [s4_9])
  · decide +kernel
  · exact allCons c4_9 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_28 : search 5 s5_28 = false := by
  apply row (k := 3) (covered := [s4_4,s4_10])
  · decide +kernel
  · exact allCons c4_4 (allCons c4_10 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_29 : search 5 s5_29 = false := by
  apply row (k := 3) (covered := [s4_5,s4_10])
  · decide +kernel
  · exact allCons c4_5 (allCons c4_10 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_30 : search 5 s5_30 = false := by
  apply row (k := 3) (covered := [s4_9,s4_11,s4_12])
  · decide +kernel
  · exact allCons c4_9 (allCons c4_11 (allCons c4_12 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_31 : search 5 s5_31 = false := by
  apply row (k := 3) (covered := [s4_6,s4_12])
  · decide +kernel
  · exact allCons c4_6 (allCons c4_12 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_32 : search 5 s5_32 = false := by
  apply row (k := 3) (covered := [s4_11,s4_13])
  · decide +kernel
  · exact allCons c4_11 (allCons c4_13 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_33 : search 5 s5_33 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_34 : search 5 s5_34 = false := by
  apply row (k := 3) (covered := [s4_13])
  · decide +kernel
  · exact allCons c4_13 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_35 : search 5 s5_35 = false := by
  apply row (k := 3) (covered := [s4_7])
  · decide +kernel
  · exact allCons c4_7 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_36 : search 5 s5_36 = false := by
  apply row (k := 3) (covered := [s4_8])
  · decide +kernel
  · exact allCons c4_8 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_37 : search 5 s5_37 = false := by
  apply row (k := 3) (covered := [s4_10])
  · decide +kernel
  · exact allCons c4_10 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_38 : search 5 s5_38 = false := by
  apply row (k := 3) (covered := [s4_13])
  · decide +kernel
  · exact allCons c4_13 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_39 : search 5 s5_39 = false := by
  apply row (k := 3) (covered := [s4_12])
  · decide +kernel
  · exact allCons c4_12 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_40 : search 5 s5_40 = false := by
  apply row (k := 3) (covered := [s4_14,s4_15])
  · decide +kernel
  · exact allCons c4_14 (allCons c4_15 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_41 : search 5 s5_41 = false := by
  apply row (k := 3) (covered := [s4_14,s4_16])
  · decide +kernel
  · exact allCons c4_14 (allCons c4_16 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_42 : search 5 s5_42 = false := by
  apply row (k := 3) (covered := [s4_17,s4_15])
  · decide +kernel
  · exact allCons c4_17 (allCons c4_15 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_43 : search 5 s5_43 = false := by
  apply row (k := 3) (covered := [s4_14,s4_17])
  · decide +kernel
  · exact allCons c4_14 (allCons c4_17 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_44 : search 5 s5_44 = false := by
  apply row (k := 3) (covered := [s4_16,s4_15])
  · decide +kernel
  · exact allCons c4_16 (allCons c4_15 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_45 : search 5 s5_45 = false := by
  apply row (k := 3) (covered := [s4_18])
  · decide +kernel
  · exact allCons c4_18 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_46 : search 5 s5_46 = false := by
  apply row (k := 3) (covered := [s4_9,s4_19])
  · decide +kernel
  · exact allCons c4_9 (allCons c4_19 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_47 : search 5 s5_47 = false := by
  apply row (k := 3) (covered := [s4_20,s4_21])
  · decide +kernel
  · exact allCons c4_20 (allCons c4_21 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_48 : search 5 s5_48 = false := by
  apply row (k := 3) (covered := [s4_20])
  · decide +kernel
  · exact allCons c4_20 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_49 : search 5 s5_49 = false := by
  apply row (k := 3) (covered := [s4_18])
  · decide +kernel
  · exact allCons c4_18 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_50 : search 5 s5_50 = false := by
  apply row (k := 3) (covered := [s4_19,s4_21])
  · decide +kernel
  · exact allCons c4_19 (allCons c4_21 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_51 : search 5 s5_51 = false := by
  apply row (k := 3) (covered := [s4_18,s4_22])
  · decide +kernel
  · exact allCons c4_18 (allCons c4_22 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_52 : search 5 s5_52 = false := by
  apply row (k := 3) (covered := [s4_5,s4_22,s4_23])
  · decide +kernel
  · exact allCons c4_5 (allCons c4_22 (allCons c4_23 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_53 : search 5 s5_53 = false := by
  apply row (k := 3) (covered := [s4_6,s4_12])
  · decide +kernel
  · exact allCons c4_6 (allCons c4_12 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_54 : search 5 s5_54 = false := by
  apply row (k := 3) (covered := [s4_20,s4_24,s4_25])
  · decide +kernel
  · exact allCons c4_20 (allCons c4_24 (allCons c4_25 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_55 : search 5 s5_55 = false := by
  apply row (k := 3) (covered := [s4_8,s4_24,s4_26])
  · decide +kernel
  · exact allCons c4_8 (allCons c4_24 (allCons c4_26 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_56 : search 5 s5_56 = false := by
  apply row (k := 3) (covered := [s4_25,s4_26])
  · decide +kernel
  · exact allCons c4_25 (allCons c4_26 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_57 : search 5 s5_57 = false := by
  apply row (k := 3) (covered := [s4_2,s4_24])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_24 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_58 : search 5 s5_58 = false := by
  apply row (k := 3) (covered := [s4_22])
  · decide +kernel
  · exact allCons c4_22 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_59 : search 5 s5_59 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_60 : search 5 s5_60 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_61 : search 5 s5_61 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_62 : search 5 s5_62 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_63 : search 5 s5_63 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_64 : search 5 s5_64 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_65 : search 5 s5_65 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_66 : search 5 s5_66 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_67 : search 5 s5_67 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_68 : search 5 s5_68 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_69 : search 5 s5_69 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_70 : search 5 s5_70 = false := by
  apply row (k := 3) (covered := [s4_27])
  · decide +kernel
  · exact allCons c4_27 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_71 : search 5 s5_71 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_72 : search 5 s5_72 = false := by
  apply row (k := 3) (covered := [s4_28,s4_29])
  · decide +kernel
  · exact allCons c4_28 (allCons c4_29 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_73 : search 5 s5_73 = false := by
  apply row (k := 3) (covered := [s4_27,s4_29])
  · decide +kernel
  · exact allCons c4_27 (allCons c4_29 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_74 : search 5 s5_74 = false := by
  apply row (k := 3) (covered := [s4_30,s4_31,s4_32])
  · decide +kernel
  · exact allCons c4_30 (allCons c4_31 (allCons c4_32 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_75 : search 5 s5_75 = false := by
  apply row (k := 3) (covered := [s4_4,s4_33])
  · decide +kernel
  · exact allCons c4_4 (allCons c4_33 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_76 : search 5 s5_76 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_77 : search 5 s5_77 = false := by
  apply row (k := 3) (covered := [s4_29])
  · decide +kernel
  · exact allCons c4_29 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_78 : search 5 s5_78 = false := by
  apply row (k := 3) (covered := [s4_32])
  · decide +kernel
  · exact allCons c4_32 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_79 : search 5 s5_79 = false := by
  apply row (k := 3) (covered := [s4_33,s4_34])
  · decide +kernel
  · exact allCons c4_33 (allCons c4_34 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_80 : search 5 s5_80 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_81 : search 5 s5_81 = false := by
  apply row (k := 3) (covered := [s4_35,s4_36])
  · decide +kernel
  · exact allCons c4_35 (allCons c4_36 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_82 : search 5 s5_82 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_83 : search 5 s5_83 = false := by
  apply row (k := 3) (covered := [s4_37])
  · decide +kernel
  · exact allCons c4_37 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_84 : search 5 s5_84 = false := by
  apply row (k := 3) (covered := [s4_36,s4_37])
  · decide +kernel
  · exact allCons c4_36 (allCons c4_37 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_85 : search 5 s5_85 = false := by
  apply row (k := 3) (covered := [s4_38,s4_39])
  · decide +kernel
  · exact allCons c4_38 (allCons c4_39 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_86 : search 5 s5_86 = false := by
  apply row (k := 3) (covered := [s4_40])
  · decide +kernel
  · exact allCons c4_40 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_87 : search 5 s5_87 = false := by
  apply row (k := 3) (covered := [s4_41,s4_42,s4_40])
  · decide +kernel
  · exact allCons c4_41 (allCons c4_42 (allCons c4_40 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_88 : search 5 s5_88 = false := by
  apply row (k := 3) (covered := [s4_36])
  · decide +kernel
  · exact allCons c4_36 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_89 : search 5 s5_89 = false := by
  apply row (k := 3) (covered := [s4_39,s4_19])
  · decide +kernel
  · exact allCons c4_39 (allCons c4_19 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_90 : search 5 s5_90 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_91 : search 5 s5_91 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_92 : search 5 s5_92 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_93 : search 5 s5_93 = false := by
  apply row (k := 3) (covered := [s4_27])
  · decide +kernel
  · exact allCons c4_27 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_94 : search 5 s5_94 = false := by
  apply row (k := 3) (covered := [s4_43,s4_44,s4_36])
  · decide +kernel
  · exact allCons c4_43 (allCons c4_44 (allCons c4_36 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_95 : search 5 s5_95 = false := by
  apply row (k := 3) (covered := [s4_7,s4_45])
  · decide +kernel
  · exact allCons c4_7 (allCons c4_45 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_96 : search 5 s5_96 = false := by
  apply row (k := 3) (covered := [s4_46,s4_47,s4_29])
  · decide +kernel
  · exact allCons c4_46 (allCons c4_47 (allCons c4_29 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_97 : search 5 s5_97 = false := by
  apply row (k := 3) (covered := [s4_37])
  · decide +kernel
  · exact allCons c4_37 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_98 : search 5 s5_98 = false := by
  apply row (k := 3) (covered := [s4_48,s4_49])
  · decide +kernel
  · exact allCons c4_48 (allCons c4_49 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_99 : search 5 s5_99 = false := by
  apply row (k := 3) (covered := [s4_45,s4_21])
  · decide +kernel
  · exact allCons c4_45 (allCons c4_21 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_100 : search 5 s5_100 = false := by
  apply row (k := 3) (covered := [s4_27])
  · decide +kernel
  · exact allCons c4_27 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_101 : search 5 s5_101 = false := by
  apply row (k := 3) (covered := [s4_43,s4_50])
  · decide +kernel
  · exact allCons c4_43 (allCons c4_50 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_102 : search 5 s5_102 = false := by
  apply row (k := 3) (covered := [s4_30,s4_35,s4_44,s4_51])
  · decide +kernel
  · exact allCons c4_30 (allCons c4_35 (allCons c4_44 (allCons c4_51 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_103 : search 5 s5_103 = false := by
  apply row (k := 3) (covered := [s4_31])
  · decide +kernel
  · exact allCons c4_31 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_104 : search 5 s5_104 = false := by
  apply row (k := 3) (covered := [s4_32,s4_36,s4_50,s4_51])
  · decide +kernel
  · exact allCons c4_32 (allCons c4_36 (allCons c4_50 (allCons c4_51 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_105 : search 5 s5_105 = false := by
  apply row (k := 3) (covered := [s4_33,s4_39,s4_45])
  · decide +kernel
  · exact allCons c4_33 (allCons c4_39 (allCons c4_45 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_106 : search 5 s5_106 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_107 : search 5 s5_107 = false := by
  apply row (k := 3) (covered := [s4_40,s4_29,s4_52,s4_53])
  · decide +kernel
  · exact allCons c4_40 (allCons c4_29 (allCons c4_52 (allCons c4_53 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_108 : search 5 s5_108 = false := by
  apply row (k := 3) (covered := [s4_46,s4_52])
  · decide +kernel
  · exact allCons c4_46 (allCons c4_52 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_109 : search 5 s5_109 = false := by
  apply row (k := 3) (covered := [s4_28,s4_41,s4_47,s4_53])
  · decide +kernel
  · exact allCons c4_28 (allCons c4_41 (allCons c4_47 (allCons c4_53 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_110 : search 5 s5_110 = false := by
  apply row (k := 3) (covered := [s4_42])
  · decide +kernel
  · exact allCons c4_42 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_111 : search 5 s5_111 = false := by
  apply row (k := 3) (covered := [s4_37])
  · decide +kernel
  · exact allCons c4_37 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_112 : search 5 s5_112 = false := by
  apply row (k := 3) (covered := [s4_14,s4_54])
  · decide +kernel
  · exact allCons c4_14 (allCons c4_54 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_113 : search 5 s5_113 = false := by
  apply row (k := 3) (covered := [s4_15,s4_55])
  · decide +kernel
  · exact allCons c4_15 (allCons c4_55 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_114 : search 5 s5_114 = false := by
  apply row (k := 3) (covered := [s4_56])
  · decide +kernel
  · exact allCons c4_56 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_115 : search 5 s5_115 = false := by
  apply row (k := 3) (covered := [s4_55])
  · decide +kernel
  · exact allCons c4_55 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_116 : search 5 s5_116 = false := by
  apply row (k := 3) (covered := [s4_56])
  · decide +kernel
  · exact allCons c4_56 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_117 : search 5 s5_117 = false := by
  apply row (k := 3) (covered := [s4_54])
  · decide +kernel
  · exact allCons c4_54 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_118 : search 5 s5_118 = false := by
  apply row (k := 3) (covered := [s4_57])
  · decide +kernel
  · exact allCons c4_57 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_119 : search 5 s5_119 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_120 : search 5 s5_120 = false := by
  apply row (k := 3) (covered := [s4_58,s4_59])
  · decide +kernel
  · exact allCons c4_58 (allCons c4_59 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_121 : search 5 s5_121 = false := by
  apply row (k := 3) (covered := [s4_58,s4_60])
  · decide +kernel
  · exact allCons c4_58 (allCons c4_60 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_122 : search 5 s5_122 = false := by
  apply row (k := 3) (covered := [s4_59,s4_60])
  · decide +kernel
  · exact allCons c4_59 (allCons c4_60 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_123 : search 5 s5_123 = false := by
  apply row (k := 3) (covered := [s4_57])
  · decide +kernel
  · exact allCons c4_57 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_124 : search 5 s5_124 = false := by
  apply row (k := 3) (covered := [s4_16,s4_61])
  · decide +kernel
  · exact allCons c4_16 (allCons c4_61 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_125 : search 5 s5_125 = false := by
  apply row (k := 3) (covered := [s4_58,s4_62])
  · decide +kernel
  · exact allCons c4_58 (allCons c4_62 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_126 : search 5 s5_126 = false := by
  apply row (k := 3) (covered := [s4_61])
  · decide +kernel
  · exact allCons c4_61 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_127 : search 5 s5_127 = false := by
  apply row (k := 3) (covered := [s4_62,s4_60])
  · decide +kernel
  · exact allCons c4_62 (allCons c4_60 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_128 : search 5 s5_128 = false := by
  apply row (k := 3) (covered := [s4_54])
  · decide +kernel
  · exact allCons c4_54 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_129 : search 5 s5_129 = false := by
  apply row (k := 3) (covered := [s4_17,s4_63])
  · decide +kernel
  · exact allCons c4_17 (allCons c4_63 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_130 : search 5 s5_130 = false := by
  apply row (k := 3) (covered := [s4_64,s4_65])
  · decide +kernel
  · exact allCons c4_64 (allCons c4_65 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_131 : search 5 s5_131 = false := by
  apply row (k := 3) (covered := [s4_64,s4_66])
  · decide +kernel
  · exact allCons c4_64 (allCons c4_66 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_132 : search 5 s5_132 = false := by
  apply row (k := 3) (covered := [s4_55])
  · decide +kernel
  · exact allCons c4_55 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_133 : search 5 s5_133 = false := by
  apply row (k := 3) (covered := [s4_65,s4_66])
  · decide +kernel
  · exact allCons c4_65 (allCons c4_66 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_134 : search 5 s5_134 = false := by
  apply row (k := 3) (covered := [s4_63])
  · decide +kernel
  · exact allCons c4_63 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_135 : search 5 s5_135 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_136 : search 5 s5_136 = false := by
  apply row (k := 3) (covered := [s4_67])
  · decide +kernel
  · exact allCons c4_67 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_137 : search 5 s5_137 = false := by
  apply row (k := 3) (covered := [s4_68,s4_65])
  · decide +kernel
  · exact allCons c4_68 (allCons c4_65 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_138 : search 5 s5_138 = false := by
  apply row (k := 3) (covered := [s4_68,s4_66])
  · decide +kernel
  · exact allCons c4_68 (allCons c4_66 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_139 : search 5 s5_139 = false := by
  apply row (k := 3) (covered := [s4_67])
  · decide +kernel
  · exact allCons c4_67 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_140 : search 5 s5_140 = false := by
  apply row (k := 3) (covered := [s4_57,s4_54,s4_63])
  · decide +kernel
  · exact allCons c4_57 (allCons c4_54 (allCons c4_63 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_141 : search 5 s5_141 = false := by
  apply row (k := 3) (covered := [s4_61,s4_55,s4_67])
  · decide +kernel
  · exact allCons c4_61 (allCons c4_55 (allCons c4_67 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_142 : search 5 s5_142 = false := by
  apply row (k := 3) (covered := [s4_25,s4_58,s4_64,s4_68,s4_69])
  · decide +kernel
  · exact allCons c4_25 (allCons c4_58 (allCons c4_64 (allCons c4_68 (allCons c4_69 (allNil 4)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_143 : search 5 s5_143 = false := by
  apply row (k := 3) (covered := [s4_26,s4_59,s4_62,s4_65,s4_69])
  · decide +kernel
  · exact allCons c4_26 (allCons c4_59 (allCons c4_62 (allCons c4_65 (allCons c4_69 (allNil 4)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_144 : search 5 s5_144 = false := by
  apply row (k := 3) (covered := [s4_56,s4_60,s4_66,s4_69])
  · decide +kernel
  · exact allCons c4_56 (allCons c4_60 (allCons c4_66 (allCons c4_69 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_145 : search 5 s5_145 = false := by
  apply row (k := 3) (covered := [s4_18,s4_22])
  · decide +kernel
  · exact allCons c4_18 (allCons c4_22 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_146 : search 5 s5_146 = false := by
  apply row (k := 3) (covered := [s4_9,s4_70])
  · decide +kernel
  · exact allCons c4_9 (allCons c4_70 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_147 : search 5 s5_147 = false := by
  apply row (k := 3) (covered := [s4_19,s4_70])
  · decide +kernel
  · exact allCons c4_19 (allCons c4_70 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_148 : search 5 s5_148 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_149 : search 5 s5_149 = false := by
  apply row (k := 3) (covered := [s4_71])
  · decide +kernel
  · exact allCons c4_71 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_150 : search 5 s5_150 = false := by
  apply row (k := 3) (covered := [s4_23,s4_71])
  · decide +kernel
  · exact allCons c4_23 (allCons c4_71 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_151 : search 5 s5_151 = false := by
  apply row (k := 3) (covered := [s4_20])
  · decide +kernel
  · exact allCons c4_20 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_152 : search 5 s5_152 = false := by
  apply row (k := 3) (covered := [s4_21])
  · decide +kernel
  · exact allCons c4_21 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_153 : search 5 s5_153 = false := by
  apply row (k := 3) (covered := [s4_70])
  · decide +kernel
  · exact allCons c4_70 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_154 : search 5 s5_154 = false := by
  apply row (k := 3) (covered := [s4_71])
  · decide +kernel
  · exact allCons c4_71 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_155 : search 5 s5_155 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_156 : search 5 s5_156 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_157 : search 5 s5_157 = false := by
  apply row (k := 3) (covered := [s4_72])
  · decide +kernel
  · exact allCons c4_72 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_158 : search 5 s5_158 = false := by
  apply row (k := 3) (covered := [s4_73])
  · decide +kernel
  · exact allCons c4_73 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_159 : search 5 s5_159 = false := by
  apply row (k := 3) (covered := [s4_72,s4_73])
  · decide +kernel
  · exact allCons c4_72 (allCons c4_73 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_160 : search 5 s5_160 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_161 : search 5 s5_161 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_162 : search 5 s5_162 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_163 : search 5 s5_163 = false := by
  apply row (k := 3) (covered := [s4_27,s4_74])
  · decide +kernel
  · exact allCons c4_27 (allCons c4_74 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_164 : search 5 s5_164 = false := by
  apply row (k := 3) (covered := [s4_75])
  · decide +kernel
  · exact allCons c4_75 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_165 : search 5 s5_165 = false := by
  apply row (k := 3) (covered := [s4_2,s4_74])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_74 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_166 : search 5 s5_166 = false := by
  apply row (k := 3) (covered := [s4_76,s4_75])
  · decide +kernel
  · exact allCons c4_76 (allCons c4_75 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_167 : search 5 s5_167 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_168 : search 5 s5_168 = false := by
  apply row (k := 3) (covered := [s4_77,s4_78])
  · decide +kernel
  · exact allCons c4_77 (allCons c4_78 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_169 : search 5 s5_169 = false := by
  apply row (k := 3) (covered := [s4_0,s4_75,s4_79])
  · decide +kernel
  · exact allCons c4_0 (allCons c4_75 (allCons c4_79 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_170 : search 5 s5_170 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_171 : search 5 s5_171 = false := by
  apply row (k := 3) (covered := [s4_75,s4_80])
  · decide +kernel
  · exact allCons c4_75 (allCons c4_80 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_172 : search 5 s5_172 = false := by
  apply row (k := 3) (covered := [s4_77,s4_28,s4_81])
  · decide +kernel
  · exact allCons c4_77 (allCons c4_28 (allCons c4_81 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_173 : search 5 s5_173 = false := by
  apply row (k := 3) (covered := [s4_28,s4_78,s4_82])
  · decide +kernel
  · exact allCons c4_28 (allCons c4_78 (allCons c4_82 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_174 : search 5 s5_174 = false := by
  apply row (k := 3) (covered := [s4_81,s4_29,s4_82])
  · decide +kernel
  · exact allCons c4_81 (allCons c4_29 (allCons c4_82 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_175 : search 5 s5_175 = false := by
  apply row (k := 3) (covered := [s4_74])
  · decide +kernel
  · exact allCons c4_74 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_176 : search 5 s5_176 = false := by
  apply row (k := 3) (covered := [s4_76,s4_79,s4_80])
  · decide +kernel
  · exact allCons c4_76 (allCons c4_79 (allCons c4_80 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_177 : search 5 s5_177 = false := by
  apply row (k := 3) (covered := [s4_30,s4_83,s4_84])
  · decide +kernel
  · exact allCons c4_30 (allCons c4_83 (allCons c4_84 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_178 : search 5 s5_178 = false := by
  apply row (k := 3) (covered := [s4_30,s4_85])
  · decide +kernel
  · exact allCons c4_30 (allCons c4_85 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_179 : search 5 s5_179 = false := by
  apply row (k := 3) (covered := [s4_31,s4_86])
  · decide +kernel
  · exact allCons c4_31 (allCons c4_86 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_180 : search 5 s5_180 = false := by
  apply row (k := 3) (covered := [s4_83,s4_32,s4_85,s4_87])
  · decide +kernel
  · exact allCons c4_83 (allCons c4_32 (allCons c4_85 (allCons c4_87 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_181 : search 5 s5_181 = false := by
  apply row (k := 3) (covered := [s4_84,s4_86,s4_87])
  · decide +kernel
  · exact allCons c4_84 (allCons c4_86 (allCons c4_87 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_182 : search 5 s5_182 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_183 : search 5 s5_183 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_184 : search 5 s5_184 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_185 : search 5 s5_185 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_186 : search 5 s5_186 = false := by
  apply row (k := 3) (covered := [s4_0])
  · decide +kernel
  · exact allCons c4_0 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_187 : search 5 s5_187 = false := by
  apply row (k := 3) (covered := [s4_0,s4_22,s4_88])
  · decide +kernel
  · exact allCons c4_0 (allCons c4_22 (allCons c4_88 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_188 : search 5 s5_188 = false := by
  apply row (k := 3) (covered := [s4_89])
  · decide +kernel
  · exact allCons c4_89 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_189 : search 5 s5_189 = false := by
  apply row (k := 3) (covered := [s4_87])
  · decide +kernel
  · exact allCons c4_87 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_190 : search 5 s5_190 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_191 : search 5 s5_191 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_192 : search 5 s5_192 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_193 : search 5 s5_193 = false := by
  apply row (k := 3) (covered := [s4_90,s4_88,s4_89])
  · decide +kernel
  · exact allCons c4_90 (allCons c4_88 (allCons c4_89 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_194 : search 5 s5_194 = false := by
  apply row (k := 3) (covered := [s4_91])
  · decide +kernel
  · exact allCons c4_91 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_195 : search 5 s5_195 = false := by
  apply row (k := 3) (covered := [s4_92])
  · decide +kernel
  · exact allCons c4_92 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_196 : search 5 s5_196 = false := by
  apply row (k := 3) (covered := [s4_91,s4_92])
  · decide +kernel
  · exact allCons c4_91 (allCons c4_92 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_197 : search 5 s5_197 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_198 : search 5 s5_198 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_199 : search 5 s5_199 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_200 : search 5 s5_200 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_201 : search 5 s5_201 = false := by
  apply row (k := 3) (covered := [s4_2,s4_93])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_93 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_202 : search 5 s5_202 = false := by
  apply row (k := 3) (covered := [s4_93])
  · decide +kernel
  · exact allCons c4_93 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_203 : search 5 s5_203 = false := by
  apply row (k := 3) (covered := [s4_35,s4_94,s4_95])
  · decide +kernel
  · exact allCons c4_35 (allCons c4_94 (allCons c4_95 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_204 : search 5 s5_204 = false := by
  apply row (k := 3) (covered := [s4_35,s4_96,s4_97])
  · decide +kernel
  · exact allCons c4_35 (allCons c4_96 (allCons c4_97 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_205 : search 5 s5_205 = false := by
  apply row (k := 3) (covered := [s4_94,s4_36,s4_96])
  · decide +kernel
  · exact allCons c4_94 (allCons c4_36 (allCons c4_96 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_206 : search 5 s5_206 = false := by
  apply row (k := 3) (covered := [s4_95,s4_97])
  · decide +kernel
  · exact allCons c4_95 (allCons c4_97 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_207 : search 5 s5_207 = false := by
  apply row (k := 3) (covered := [s4_98,s4_99])
  · decide +kernel
  · exact allCons c4_98 (allCons c4_99 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_208 : search 5 s5_208 = false := by
  apply row (k := 3) (covered := [s4_100,s4_99])
  · decide +kernel
  · exact allCons c4_100 (allCons c4_99 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_209 : search 5 s5_209 = false := by
  apply row (k := 3) (covered := [s4_98,s4_100,s4_101])
  · decide +kernel
  · exact allCons c4_98 (allCons c4_100 (allCons c4_101 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_210 : search 5 s5_210 = false := by
  apply row (k := 3) (covered := [s4_1,s4_99,s4_101])
  · decide +kernel
  · exact allCons c4_1 (allCons c4_99 (allCons c4_101 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_211 : search 5 s5_211 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_212 : search 5 s5_212 = false := by
  apply row (k := 3) (covered := [s4_99])
  · decide +kernel
  · exact allCons c4_99 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_213 : search 5 s5_213 = false := by
  apply row (k := 3) (covered := [s4_37,s4_93])
  · decide +kernel
  · exact allCons c4_37 (allCons c4_93 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_214 : search 5 s5_214 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_215 : search 5 s5_215 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_216 : search 5 s5_216 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_217 : search 5 s5_217 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_218 : search 5 s5_218 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_219 : search 5 s5_219 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_220 : search 5 s5_220 = false := by
  apply row (k := 3) (covered := [s4_102])
  · decide +kernel
  · exact allCons c4_102 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_221 : search 5 s5_221 = false := by
  apply row (k := 3) (covered := [s4_103,s4_104,s4_102])
  · decide +kernel
  · exact allCons c4_103 (allCons c4_104 (allCons c4_102 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_222 : search 5 s5_222 = false := by
  apply row (k := 3) (covered := [s4_105,s4_106,s4_107])
  · decide +kernel
  · exact allCons c4_105 (allCons c4_106 (allCons c4_107 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_223 : search 5 s5_223 = false := by
  apply row (k := 3) (covered := [s4_106])
  · decide +kernel
  · exact allCons c4_106 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_224 : search 5 s5_224 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_225 : search 5 s5_225 = false := by
  apply row (k := 3) (covered := [s4_1])
  · decide +kernel
  · exact allCons c4_1 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_226 : search 5 s5_226 = false := by
  apply row (k := 3) (covered := [s4_1,s4_12,s4_107])
  · decide +kernel
  · exact allCons c4_1 (allCons c4_12 (allCons c4_107 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_227 : search 5 s5_227 = false := by
  apply row (k := 3) (covered := [s4_108,s4_40,s4_102,s4_109])
  · decide +kernel
  · exact allCons c4_108 (allCons c4_40 (allCons c4_102 (allCons c4_109 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_228 : search 5 s5_228 = false := by
  apply row (k := 3) (covered := [s4_103,s4_41,s4_108])
  · decide +kernel
  · exact allCons c4_103 (allCons c4_41 (allCons c4_108 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_229 : search 5 s5_229 = false := by
  apply row (k := 3) (covered := [s4_41,s4_109])
  · decide +kernel
  · exact allCons c4_41 (allCons c4_109 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_230 : search 5 s5_230 = false := by
  apply row (k := 3) (covered := [s4_42,s4_104])
  · decide +kernel
  · exact allCons c4_42 (allCons c4_104 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_231 : search 5 s5_231 = false := by
  apply row (k := 3) (covered := [s4_110,s4_111])
  · decide +kernel
  · exact allCons c4_110 (allCons c4_111 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_232 : search 5 s5_232 = false := by
  apply row (k := 3) (covered := [s4_110,s4_112])
  · decide +kernel
  · exact allCons c4_110 (allCons c4_112 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_233 : search 5 s5_233 = false := by
  apply row (k := 3) (covered := [s4_72])
  · decide +kernel
  · exact allCons c4_72 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_234 : search 5 s5_234 = false := by
  apply row (k := 3) (covered := [s4_111,s4_112])
  · decide +kernel
  · exact allCons c4_111 (allCons c4_112 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_235 : search 5 s5_235 = false := by
  apply row (k := 3) (covered := [s4_91])
  · decide +kernel
  · exact allCons c4_91 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_236 : search 5 s5_236 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_237 : search 5 s5_237 = false := by
  apply row (k := 3) (covered := [s4_92])
  · decide +kernel
  · exact allCons c4_92 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_238 : search 5 s5_238 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_239 : search 5 s5_239 = false := by
  apply row (k := 3) (covered := [s4_73])
  · decide +kernel
  · exact allCons c4_73 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_240 : search 5 s5_240 = false := by
  apply row (k := 3) (covered := [s4_110,s4_113])
  · decide +kernel
  · exact allCons c4_110 (allCons c4_113 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_241 : search 5 s5_241 = false := by
  apply row (k := 3) (covered := [s4_111,s4_113])
  · decide +kernel
  · exact allCons c4_111 (allCons c4_113 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_242 : search 5 s5_242 = false := by
  apply row (k := 3) (covered := [s4_112,s4_2,s4_113])
  · decide +kernel
  · exact allCons c4_112 (allCons c4_2 (allCons c4_113 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_243 : search 5 s5_243 = false := by
  apply row (k := 3) (covered := [s4_114])
  · decide +kernel
  · exact allCons c4_114 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_244 : search 5 s5_244 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_245 : search 5 s5_245 = false := by
  apply row (k := 3) (covered := [s4_114])
  · decide +kernel
  · exact allCons c4_114 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_246 : search 5 s5_246 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_247 : search 5 s5_247 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_248 : search 5 s5_248 = false := by
  apply row (k := 3) (covered := [s4_115])
  · decide +kernel
  · exact allCons c4_115 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_249 : search 5 s5_249 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_250 : search 5 s5_250 = false := by
  apply row (k := 3) (covered := [s4_115])
  · decide +kernel
  · exact allCons c4_115 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_251 : search 5 s5_251 = false := by
  apply row (k := 3) (covered := [s4_116])
  · decide +kernel
  · exact allCons c4_116 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_252 : search 5 s5_252 = false := by
  apply row (k := 3) (covered := [s4_116])
  · decide +kernel
  · exact allCons c4_116 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_253 : search 5 s5_253 = false := by
  apply row (k := 3) (covered := [s4_2,s4_116])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_116 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_254 : search 5 s5_254 = false := by
  apply row (k := 3) (covered := [s4_115])
  · decide +kernel
  · exact allCons c4_115 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_255 : search 5 s5_255 = false := by
  apply row (k := 3) (covered := [s4_114])
  · decide +kernel
  · exact allCons c4_114 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_256 : search 5 s5_256 = false := by
  apply row (k := 3) (covered := [s4_117,s4_118,s4_119,s4_120])
  · decide +kernel
  · exact allCons c4_117 (allCons c4_118 (allCons c4_119 (allCons c4_120 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_257 : search 5 s5_257 = false := by
  apply row (k := 3) (covered := [s4_117,s4_121,s4_122,s4_123])
  · decide +kernel
  · exact allCons c4_117 (allCons c4_121 (allCons c4_122 (allCons c4_123 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_258 : search 5 s5_258 = false := by
  apply row (k := 3) (covered := [s4_124,s4_125,s4_126,s4_127])
  · decide +kernel
  · exact allCons c4_124 (allCons c4_125 (allCons c4_126 (allCons c4_127 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_259 : search 5 s5_259 = false := by
  apply row (k := 3) (covered := [s4_128,s4_118,s4_129,s4_130])
  · decide +kernel
  · exact allCons c4_128 (allCons c4_118 (allCons c4_129 (allCons c4_130 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_260 : search 5 s5_260 = false := by
  apply row (k := 3) (covered := [s4_131,s4_132,s4_126,s4_130])
  · decide +kernel
  · exact allCons c4_131 (allCons c4_132 (allCons c4_126 (allCons c4_130 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_261 : search 5 s5_261 = false := by
  apply row (k := 3) (covered := [s4_117,s4_124,s4_128,s4_131,s4_133])
  · decide +kernel
  · exact allCons c4_117 (allCons c4_124 (allCons c4_128 (allCons c4_131 (allCons c4_133 (allNil 4)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_262 : search 5 s5_262 = false := by
  apply row (k := 3) (covered := [s4_121,s4_125,s4_118,s4_132])
  · decide +kernel
  · exact allCons c4_121 (allCons c4_125 (allCons c4_118 (allCons c4_132 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_263 : search 5 s5_263 = false := by
  apply row (k := 3) (covered := [s4_119,s4_122,s4_129,s4_126,s4_133])
  · decide +kernel
  · exact allCons c4_119 (allCons c4_122 (allCons c4_129 (allCons c4_126 (allCons c4_133 (allNil 4)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_264 : search 5 s5_264 = false := by
  apply row (k := 3) (covered := [s4_120,s4_123,s4_127,s4_130])
  · decide +kernel
  · exact allCons c4_120 (allCons c4_123 (allCons c4_127 (allCons c4_130 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_265 : search 5 s5_265 = false := by
  apply row (k := 3) (covered := [s4_134,s4_135,s4_136,s4_137])
  · decide +kernel
  · exact allCons c4_134 (allCons c4_135 (allCons c4_136 (allCons c4_137 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_266 : search 5 s5_266 = false := by
  apply row (k := 3) (covered := [s4_138,s4_136])
  · decide +kernel
  · exact allCons c4_138 (allCons c4_136 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_267 : search 5 s5_267 = false := by
  apply row (k := 3) (covered := [s4_117,s4_134,s4_138,s4_139])
  · decide +kernel
  · exact allCons c4_117 (allCons c4_134 (allCons c4_138 (allCons c4_139 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_268 : search 5 s5_268 = false := by
  apply row (k := 3) (covered := [s4_118,s4_135])
  · decide +kernel
  · exact allCons c4_118 (allCons c4_135 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_269 : search 5 s5_269 = false := by
  apply row (k := 3) (covered := [s4_119,s4_136,s4_139])
  · decide +kernel
  · exact allCons c4_119 (allCons c4_136 (allCons c4_139 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_270 : search 5 s5_270 = false := by
  apply row (k := 3) (covered := [s4_120,s4_137])
  · decide +kernel
  · exact allCons c4_120 (allCons c4_137 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_271 : search 5 s5_271 = false := by
  apply row (k := 3) (covered := [s4_134,s4_140,s4_141,s4_142])
  · decide +kernel
  · exact allCons c4_134 (allCons c4_140 (allCons c4_141 (allCons c4_142 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_272 : search 5 s5_272 = false := by
  apply row (k := 3) (covered := [s4_143,s4_144])
  · decide +kernel
  · exact allCons c4_143 (allCons c4_144 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_273 : search 5 s5_273 = false := by
  apply row (k := 3) (covered := [s4_138,s4_145,s4_141,s4_144])
  · decide +kernel
  · exact allCons c4_138 (allCons c4_145 (allCons c4_141 (allCons c4_144 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_274 : search 5 s5_274 = false := by
  apply row (k := 3) (covered := [s4_121,s4_140,s4_145])
  · decide +kernel
  · exact allCons c4_121 (allCons c4_140 (allCons c4_145 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_275 : search 5 s5_275 = false := by
  apply row (k := 3) (covered := [s4_122,s4_143,s4_141,s4_139])
  · decide +kernel
  · exact allCons c4_122 (allCons c4_143 (allCons c4_141 (allCons c4_139 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_276 : search 5 s5_276 = false := by
  apply row (k := 3) (covered := [s4_123,s4_142,s4_144])
  · decide +kernel
  · exact allCons c4_123 (allCons c4_142 (allCons c4_144 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_277 : search 5 s5_277 = false := by
  apply row (k := 3) (covered := [s4_146,s4_135])
  · decide +kernel
  · exact allCons c4_146 (allCons c4_135 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_278 : search 5 s5_278 = false := by
  apply row (k := 3) (covered := [s4_124,s4_134,s4_146,s4_147])
  · decide +kernel
  · exact allCons c4_124 (allCons c4_134 (allCons c4_146 (allCons c4_147 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_279 : search 5 s5_279 = false := by
  apply row (k := 3) (covered := [s4_125,s4_140,s4_135])
  · decide +kernel
  · exact allCons c4_125 (allCons c4_140 (allCons c4_135 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_280 : search 5 s5_280 = false := by
  apply row (k := 3) (covered := [s4_126,s4_136,s4_141,s4_147])
  · decide +kernel
  · exact allCons c4_126 (allCons c4_136 (allCons c4_141 (allCons c4_147 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_281 : search 5 s5_281 = false := by
  apply row (k := 3) (covered := [s4_127,s4_137,s4_142])
  · decide +kernel
  · exact allCons c4_127 (allCons c4_137 (allCons c4_142 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_282 : search 5 s5_282 = false := by
  apply row (k := 3) (covered := [s4_128,s4_146,s4_148])
  · decide +kernel
  · exact allCons c4_128 (allCons c4_146 (allCons c4_148 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_283 : search 5 s5_283 = false := by
  apply row (k := 3) (covered := [s4_129,s4_143,s4_148])
  · decide +kernel
  · exact allCons c4_129 (allCons c4_143 (allCons c4_148 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_284 : search 5 s5_284 = false := by
  apply row (k := 3) (covered := [s4_130,s4_144])
  · decide +kernel
  · exact allCons c4_130 (allCons c4_144 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_285 : search 5 s5_285 = false := by
  apply row (k := 3) (covered := [s4_131,s4_138,s4_147])
  · decide +kernel
  · exact allCons c4_131 (allCons c4_138 (allCons c4_147 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_286 : search 5 s5_286 = false := by
  apply row (k := 3) (covered := [s4_132,s4_145])
  · decide +kernel
  · exact allCons c4_132 (allCons c4_145 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_287 : search 5 s5_287 = false := by
  apply row (k := 3) (covered := [s4_149])
  · decide +kernel
  · exact allCons c4_149 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_288 : search 5 s5_288 = false := by
  apply row (k := 3) (covered := [s4_2,s4_149])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_149 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_289 : search 5 s5_289 = false := by
  apply row (k := 3) (covered := [s4_150])
  · decide +kernel
  · exact allCons c4_150 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_290 : search 5 s5_290 = false := by
  apply row (k := 3) (covered := [s4_151,s4_76,s4_152,s4_153])
  · decide +kernel
  · exact allCons c4_151 (allCons c4_76 (allCons c4_152 (allCons c4_153 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_291 : search 5 s5_291 = false := by
  apply row (k := 3) (covered := [s4_153])
  · decide +kernel
  · exact allCons c4_153 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_292 : search 5 s5_292 = false := by
  apply row (k := 3) (covered := [s4_2,s4_150])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_150 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_293 : search 5 s5_293 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_294 : search 5 s5_294 = false := by
  apply row (k := 3) (covered := [s4_153,s4_154])
  · decide +kernel
  · exact allCons c4_153 (allCons c4_154 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_295 : search 5 s5_295 = false := by
  apply row (k := 3) (covered := [s4_155])
  · decide +kernel
  · exact allCons c4_155 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_296 : search 5 s5_296 = false := by
  apply row (k := 3) (covered := [s4_155,s4_2])
  · decide +kernel
  · exact allCons c4_155 (allCons c4_2 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_297 : search 5 s5_297 = false := by
  apply row (k := 3) (covered := [s4_156,s4_2])
  · decide +kernel
  · exact allCons c4_156 (allCons c4_2 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_298 : search 5 s5_298 = false := by
  apply row (k := 3) (covered := [s4_2,s4_133,s4_69,s4_139,s4_148,s4_147,s4_154,s4_157])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_133 (allCons c4_69 (allCons c4_139 (allCons c4_148 (allCons c4_147 (allCons c4_154 (allCons c4_157 (allNil 4))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_299 : search 5 s5_299 = false := by
  apply row (k := 3) (covered := [s4_156])
  · decide +kernel
  · exact allCons c4_156 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_300 : search 5 s5_300 = false := by
  apply row (k := 3) (covered := [s4_158,s4_159,s4_160])
  · decide +kernel
  · exact allCons c4_158 (allCons c4_159 (allCons c4_160 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_301 : search 5 s5_301 = false := by
  apply row (k := 3) (covered := [s4_161,s4_162,s4_163])
  · decide +kernel
  · exact allCons c4_161 (allCons c4_162 (allCons c4_163 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_302 : search 5 s5_302 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_303 : search 5 s5_303 = false := by
  apply row (k := 3) (covered := [s4_158,s4_98,s4_161,s4_164])
  · decide +kernel
  · exact allCons c4_158 (allCons c4_98 (allCons c4_161 (allCons c4_164 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_304 : search 5 s5_304 = false := by
  apply row (k := 3) (covered := [s4_159,s4_100,s4_162,s4_164])
  · decide +kernel
  · exact allCons c4_159 (allCons c4_100 (allCons c4_162 (allCons c4_164 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_305 : search 5 s5_305 = false := by
  apply row (k := 3) (covered := [s4_160,s4_101,s4_163,s4_164])
  · decide +kernel
  · exact allCons c4_160 (allCons c4_101 (allCons c4_163 (allCons c4_164 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_306 : search 5 s5_306 = false := by
  apply row (k := 3) (covered := [s4_149])
  · decide +kernel
  · exact allCons c4_149 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_307 : search 5 s5_307 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_308 : search 5 s5_308 = false := by
  apply row (k := 3) (covered := [s4_165,s4_79,s4_166,s4_153])
  · decide +kernel
  · exact allCons c4_165 (allCons c4_79 (allCons c4_166 (allCons c4_153 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_309 : search 5 s5_309 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_310 : search 5 s5_310 = false := by
  apply row (k := 3) (covered := [s4_167,s4_80,s4_153,s4_168])
  · decide +kernel
  · exact allCons c4_167 (allCons c4_80 (allCons c4_153 (allCons c4_168 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_311 : search 5 s5_311 = false := by
  apply row (k := 3) (covered := [s4_150])
  · decide +kernel
  · exact allCons c4_150 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_312 : search 5 s5_312 = false := by
  apply row (k := 3) (covered := [s4_151,s4_165,s4_167])
  · decide +kernel
  · exact allCons c4_151 (allCons c4_165 (allCons c4_167 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_313 : search 5 s5_313 = false := by
  apply row (k := 3) (covered := [s4_152,s4_166,s4_168])
  · decide +kernel
  · exact allCons c4_152 (allCons c4_166 (allCons c4_168 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_314 : search 5 s5_314 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_315 : search 5 s5_315 = false := by
  apply row (k := 3) (covered := [s4_155])
  · decide +kernel
  · exact allCons c4_155 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_316 : search 5 s5_316 = false := by
  apply row (k := 3) (covered := [s4_164])
  · decide +kernel
  · exact allCons c4_164 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_317 : search 5 s5_317 = false := by
  apply row (k := 3) (covered := [s4_156])
  · decide +kernel
  · exact allCons c4_156 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_318 : search 5 s5_318 = false := by
  apply row (k := 3) (covered := [s4_157,s4_164])
  · decide +kernel
  · exact allCons c4_157 (allCons c4_164 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_319 : search 5 s5_319 = false := by
  apply row (k := 3) (covered := [s4_113,s4_3])
  · decide +kernel
  · exact allCons c4_113 (allCons c4_3 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_320 : search 5 s5_320 = false := by
  apply row (k := 3) (covered := [s4_2,s4_3])
  · decide +kernel
  · exact allCons c4_2 (allCons c4_3 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_321 : search 5 s5_321 = false := by
  apply row (k := 3) (covered := [s4_3])
  · decide +kernel
  · exact allCons c4_3 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_322 : search 5 s5_322 = false := by
  apply row (k := 3) (covered := [s4_169,s4_170])
  · decide +kernel
  · exact allCons c4_169 (allCons c4_170 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_323 : search 5 s5_323 = false := by
  apply row (k := 3) (covered := [s4_3,s4_74])
  · decide +kernel
  · exact allCons c4_3 (allCons c4_74 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_324 : search 5 s5_324 = false := by
  apply row (k := 3) (covered := [s4_93,s4_3])
  · decide +kernel
  · exact allCons c4_93 (allCons c4_3 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_325 : search 5 s5_325 = false := by
  apply row (k := 3) (covered := [s4_3])
  · decide +kernel
  · exact allCons c4_3 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_326 : search 5 s5_326 = false := by
  apply row (k := 3) (covered := [s4_3,s4_24,s4_113])
  · decide +kernel
  · exact allCons c4_3 (allCons c4_24 (allCons c4_113 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_327 : search 5 s5_327 = false := by
  apply row (k := 3) (covered := [s4_44,s4_94,s4_171])
  · decide +kernel
  · exact allCons c4_44 (allCons c4_94 (allCons c4_171 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_328 : search 5 s5_328 = false := by
  apply row (k := 3) (covered := [s4_43,s4_172])
  · decide +kernel
  · exact allCons c4_43 (allCons c4_172 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_329 : search 5 s5_329 = false := by
  apply row (k := 3) (covered := [s4_44,s4_96])
  · decide +kernel
  · exact allCons c4_44 (allCons c4_96 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_330 : search 5 s5_330 = false := by
  apply row (k := 3) (covered := [s4_171,s4_172])
  · decide +kernel
  · exact allCons c4_171 (allCons c4_172 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_331 : search 5 s5_331 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_332 : search 5 s5_332 = false := by
  apply row (k := 3) (covered := [s4_169,s4_47,s4_81])
  · decide +kernel
  · exact allCons c4_169 (allCons c4_47 (allCons c4_81 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_333 : search 5 s5_333 = false := by
  apply row (k := 3) (covered := [s4_46,s4_170])
  · decide +kernel
  · exact allCons c4_46 (allCons c4_170 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_334 : search 5 s5_334 = false := by
  apply row (k := 3) (covered := [s4_47,s4_82])
  · decide +kernel
  · exact allCons c4_47 (allCons c4_82 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_335 : search 5 s5_335 = false := by
  apply row (k := 3) (covered := [s4_2])
  · decide +kernel
  · exact allCons c4_2 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_336 : search 5 s5_336 = false := by
  apply row (k := 3) (covered := [s4_149])
  · decide +kernel
  · exact allCons c4_149 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_337 : search 5 s5_337 = false := by
  apply row (k := 3) (covered := [s4_150,s4_74])
  · decide +kernel
  · exact allCons c4_150 (allCons c4_74 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_338 : search 5 s5_338 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_339 : search 5 s5_339 = false := by
  apply row (k := 3) (covered := [s4_151,s4_169,s4_173])
  · decide +kernel
  · exact allCons c4_151 (allCons c4_169 (allCons c4_173 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_340 : search 5 s5_340 = false := by
  apply row (k := 3) (covered := [s4_152,s4_170,s4_174])
  · decide +kernel
  · exact allCons c4_152 (allCons c4_170 (allCons c4_174 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_341 : search 5 s5_341 = false := by
  apply row (k := 3) (covered := [s4_173,s4_153,s4_174])
  · decide +kernel
  · exact allCons c4_173 (allCons c4_153 (allCons c4_174 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_342 : search 5 s5_342 = false := by
  apply row (k := 3) (covered := [s4_75])
  · decide +kernel
  · exact allCons c4_75 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_343 : search 5 s5_343 = false := by
  apply row (k := 3) (covered := [s4_154])
  · decide +kernel
  · exact allCons c4_154 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_344 : search 5 s5_344 = false := by
  apply row (k := 3) (covered := [s4_155,s4_93])
  · decide +kernel
  · exact allCons c4_155 (allCons c4_93 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_345 : search 5 s5_345 = false := by
  apply row (k := 3) (covered := [s4_2])
  · decide +kernel
  · exact allCons c4_2 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_346 : search 5 s5_346 = false := by
  apply row (k := 3) (covered := [s4_156])
  · decide +kernel
  · exact allCons c4_156 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_347 : search 5 s5_347 = false := by
  apply row (k := 3) (covered := [s4_157])
  · decide +kernel
  · exact allCons c4_157 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_348 : search 5 s5_348 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_349 : search 5 s5_349 = false := by
  apply row (k := 3) (covered := [s4_83,s4_158,s4_94,s4_51,s4_175,s4_176])
  · decide +kernel
  · exact allCons c4_83 (allCons c4_158 (allCons c4_94 (allCons c4_51 (allCons c4_175 (allCons c4_176 (allNil 4))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_350 : search 5 s5_350 = false := by
  apply row (k := 3) (covered := [s4_159,s4_171,s4_176])
  · decide +kernel
  · exact allCons c4_159 (allCons c4_171 (allCons c4_176 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_351 : search 5 s5_351 = false := by
  apply row (k := 3) (covered := [s4_84,s4_175])
  · decide +kernel
  · exact allCons c4_84 (allCons c4_175 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_352 : search 5 s5_352 = false := by
  apply row (k := 3) (covered := [s4_95,s4_160,s4_176])
  · decide +kernel
  · exact allCons c4_95 (allCons c4_160 (allCons c4_176 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_353 : search 5 s5_353 = false := by
  apply row (k := 3) (covered := [s4_50,s4_161,s4_177,s4_178])
  · decide +kernel
  · exact allCons c4_50 (allCons c4_161 (allCons c4_177 (allCons c4_178 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_354 : search 5 s5_354 = false := by
  apply row (k := 3) (covered := [s4_162,s4_172,s4_178])
  · decide +kernel
  · exact allCons c4_162 (allCons c4_172 (allCons c4_178 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_355 : search 5 s5_355 = false := by
  apply row (k := 3) (covered := [s4_177])
  · decide +kernel
  · exact allCons c4_177 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_356 : search 5 s5_356 = false := by
  apply row (k := 3) (covered := [s4_163,s4_178])
  · decide +kernel
  · exact allCons c4_163 (allCons c4_178 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_357 : search 5 s5_357 = false := by
  apply row (k := 3) (covered := [s4_51,s4_85,s4_96])
  · decide +kernel
  · exact allCons c4_51 (allCons c4_85 (allCons c4_96 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_358 : search 5 s5_358 = false := by
  apply row (k := 3) (covered := [s4_97])
  · decide +kernel
  · exact allCons c4_97 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_359 : search 5 s5_359 = false := by
  apply row (k := 3) (covered := [s4_86])
  · decide +kernel
  · exact allCons c4_86 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_360 : search 5 s5_360 = false := by
  apply row (k := 3) (covered := [s4_175,s4_87,s4_177])
  · decide +kernel
  · exact allCons c4_175 (allCons c4_87 (allCons c4_177 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_361 : search 5 s5_361 = false := by
  apply row (k := 3) (covered := [s4_176,s4_164,s4_178])
  · decide +kernel
  · exact allCons c4_176 (allCons c4_164 (allCons c4_178 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_362 : search 5 s5_362 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_363 : search 5 s5_363 = false := by
  apply row (k := 3) (covered := [s4_179,s4_102,s4_180])
  · decide +kernel
  · exact allCons c4_179 (allCons c4_102 (allCons c4_180 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_364 : search 5 s5_364 = false := by
  apply row (k := 3) (covered := [s4_103,s4_179])
  · decide +kernel
  · exact allCons c4_103 (allCons c4_179 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_365 : search 5 s5_365 = false := by
  apply row (k := 3) (covered := [s4_180])
  · decide +kernel
  · exact allCons c4_180 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_366 : search 5 s5_366 = false := by
  apply row (k := 3) (covered := [s4_104])
  · decide +kernel
  · exact allCons c4_104 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_367 : search 5 s5_367 = false := by
  apply row (k := 3) (covered := [])
  · decide +kernel
  · exact allNil 4
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_368 : search 5 s5_368 = false := by
  apply row (k := 3) (covered := [s4_99])
  · decide +kernel
  · exact allCons c4_99 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_369 : search 5 s5_369 = false := by
  apply row (k := 3) (covered := [s4_77,s4_165,s4_173])
  · decide +kernel
  · exact allCons c4_77 (allCons c4_165 (allCons c4_173 (allNil 4)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_370 : search 5 s5_370 = false := by
  apply row (k := 3) (covered := [s4_166,s4_174])
  · decide +kernel
  · exact allCons c4_166 (allCons c4_174 (allNil 4))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_371 : search 5 s5_371 = false := by
  apply row (k := 3) (covered := [s4_78])
  · decide +kernel
  · exact allCons c4_78 (allNil 4)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_372 : search 5 s5_372 = false := by
  apply row (k := 3) (covered := [s4_108,s4_167,s4_81,s4_179,s4_173,s4_53])
  · decide +kernel
  · exact allCons c4_108 (allCons c4_167 (allCons c4_81 (allCons c4_179 (allCons c4_173 (allCons c4_53 (allNil 4))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_373 : search 5 s5_373 = false := by
  apply row (k := 3) (covered := [s4_52,s4_168,s4_180,s4_174])
  · decide +kernel
  · exact allCons c4_52 (allCons c4_168 (allCons c4_180 (allCons c4_174 (allNil 4))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c5_374 : search 5 s5_374 = false := by
  apply row (k := 3) (covered := [s4_53,s4_109,s4_82])
  · decide +kernel
  · exact allCons c4_53 (allCons c4_109 (allCons c4_82 (allNil 4)))
private def s6_0 : Finset W := {240,3840,4369,8738,17487,34952,61440}
private def s6_1 : Finset W := {15,3840,4593,8738,17476,34952,61440}
private def s6_2 : Finset W := {15,3840,4369,8946,17476,34952,61440}
private def s6_3 : Finset W := {15,64,3840,4369,8738,34952,61440}
private def s6_4 : Finset W := {15,3840,4369,8738,17476,35064,61440}
private def s6_5 : Finset W := {15,240,7953,8738,17476,34952,61440}
private def s6_6 : Finset W := {15,240,4369,8738,20292,34952,61440}
private def s6_7 : Finset W := {15,240,4369,8738,17476,36744,61440}
private def s6_8 : Finset W := {15,240,3840,4369,17476,34952,61986}
private def s6_9 : Finset W := {15,240,3840,4369,8738,34952,62532}
private def s6_10 : Finset W := {15,240,3840,4369,8738,17476,63624}
private def s6_11 : Finset W := {240,3855,4369,8738,17487,34952,61440}
private def s6_12 : Finset W := {240,3855,4369,8738,17476,34952,61455}
private def s6_13 : Finset W := {15,3855,4593,8738,17476,34952,61440}
private def s6_14 : Finset W := {15,3855,4369,8946,17476,34952,61440}
private def s6_15 : Finset W := {15,64,3855,4369,8738,34952,61440}
private def s6_16 : Finset W := {15,3855,4369,8738,17476,35064,61440}
private def s6_17 : Finset W := {15,240,514,4369,17476,34952,61440}
private def s6_18 : Finset W := {15,240,4369,8738,20303,34952,61440}
private def s6_19 : Finset W := {15,240,3855,4369,17476,34952,61986}
private def s6_20 : Finset W := {15,240,3855,4369,8738,34952,62532}
private def s6_21 : Finset W := {15,240,3855,4369,8738,17476,63624}
private def s6_22 : Finset W := {8,240,3840,4369,8738,17487,61440}
private def s6_23 : Finset W := {240,3840,4369,8738,17487,34952,61455}
private def s6_24 : Finset W := {15,3840,4593,8738,17487,34952,61440}
private def s6_25 : Finset W := {15,3840,4369,8946,17487,34952,61440}
private def s6_26 : Finset W := {15,3840,4369,8738,17487,35064,61440}
private def s6_27 : Finset W := {15,240,7953,8738,17487,34952,61440}
private def s6_28 : Finset W := {15,240,4369,8738,17487,36744,61440}
private def s6_29 : Finset W := {15,240,3840,4369,17487,34952,61986}
private def s6_30 : Finset W := {15,240,3840,4369,8738,34952,62543}
private def s6_31 : Finset W := {15,240,3840,4369,8738,17487,63624}
private def s6_32 : Finset W := {3840,4593,8738,17476,17487,34952,61440}
private def s6_33 : Finset W := {3840,4369,8946,17476,17487,34952,61440}
private def s6_34 : Finset W := {64,3840,4369,8738,17487,34952,61440}
private def s6_35 : Finset W := {3840,4369,8738,17476,17487,35064,61440}
private def s6_36 : Finset W := {240,4369,8738,17487,20292,34952,61440}
private def s6_37 : Finset W := {240,3840,4369,8738,17487,34952,62532}
private def s6_38 : Finset W := {240,3840,4593,8738,17487,34952,61440}
private def s6_39 : Finset W := {3840,4369,4593,8738,17487,34952,61440}
private def s6_40 : Finset W := {3840,4593,8738,17487,34952,61440}
private def s6_41 : Finset W := {240,3840,4369,8946,17487,34952,61440}
private def s6_42 : Finset W := {3840,4369,8738,8946,17487,34952,61440}
private def s6_43 : Finset W := {3840,4369,8946,17487,34952,61440}
private def s6_44 : Finset W := {240,3840,4369,8738,17487,35064,61440}
private def s6_45 : Finset W := {3840,4369,8738,17487,34952,35064,61440}
private def s6_46 : Finset W := {3840,4369,8738,17487,35064,61440}
private def s6_47 : Finset W := {240,4369,7953,8738,17487,34952,61440}
private def s6_48 : Finset W := {240,512,4369,8738,17487,34952,61440}
private def s6_49 : Finset W := {240,4369,8738,17487,20303,34952,61440}
private def s6_50 : Finset W := {240,4369,8738,17487,34952,36744,61440}
private def s6_51 : Finset W := {240,3840,4369,8738,17487,39321,61440}
private def s6_52 : Finset W := {240,3840,4096,4369,8738,17487,34952}
private def s6_53 : Finset W := {240,3840,4369,8738,17487,43690,61440}
private def s6_54 : Finset W := {240,3840,4369,8738,17487,34952,61986}
private def s6_55 : Finset W := {240,3840,4369,8738,17487,34952,62543}
private def s6_56 : Finset W := {240,3840,4369,8738,17487,34952,63624}
private def s6_57 : Finset W := {15,248,3840,4369,8738,17476,61440}
private def s6_58 : Finset W := {15,240,3848,4369,8738,17476,61440}
private def s6_59 : Finset W := {15,240,3840,4377,8738,17476,61440}
private def s6_60 : Finset W := {15,240,3840,4369,8746,17476,61440}
private def s6_61 : Finset W := {15,240,3840,4369,8738,17476,61448}
private def s6_62 : Finset W := {8,15,3840,4593,8738,17476,61440}
private def s6_63 : Finset W := {8,15,3840,4369,8946,17476,61440}
private def s6_64 : Finset W := {8,15,64,3840,4369,8738,61440}
private def s6_65 : Finset W := {8,15,240,7953,8738,17476,61440}
private def s6_66 : Finset W := {8,15,240,4369,8738,20292,61440}
private def s6_67 : Finset W := {8,15,240,3840,4369,17476,61986}
private def s6_68 : Finset W := {8,15,240,3840,4369,8738,62532}
private def s6_69 : Finset W := {15,3840,4593,8738,17476,34952,61455}
private def s6_70 : Finset W := {15,3840,4369,8946,17476,34952,61455}
private def s6_71 : Finset W := {15,64,3840,4369,8738,34952,61455}
private def s6_72 : Finset W := {15,3840,4369,8738,17476,35064,61455}
private def s6_73 : Finset W := {15,240,7953,8738,17476,34952,61455}
private def s6_74 : Finset W := {15,240,4369,8738,20292,34952,61455}
private def s6_75 : Finset W := {15,240,4369,8738,17476,36744,61455}
private def s6_76 : Finset W := {15,240,3840,4097,8738,17476,34952}
private def s6_77 : Finset W := {15,3840,4593,8946,17476,34952,61440}
private def s6_78 : Finset W := {15,64,3840,4593,8738,34952,61440}
private def s6_79 : Finset W := {15,3840,4593,8738,17476,35064,61440}
private def s6_80 : Finset W := {15,240,4593,8738,20292,34952,61440}
private def s6_81 : Finset W := {15,240,4593,8738,17476,36744,61440}
private def s6_82 : Finset W := {15,240,3840,4593,8738,34952,62532}
private def s6_83 : Finset W := {15,4593,7953,8738,17476,34952,61440}
private def s6_84 : Finset W := {15,4369,4593,8738,17476,36744,61440}
private def s6_85 : Finset W := {15,3840,4593,8738,17476,39321,61440}
private def s6_86 : Finset W := {15,3840,4096,4593,8738,17476,34952}
private def s6_87 : Finset W := {15,3840,4369,8738,17476,39417,61440}
private def s6_88 : Finset W := {15,3840,4369,4593,17476,34952,61986}
private def s6_89 : Finset W := {15,3840,4369,4593,8738,34952,62532}
private def s6_90 : Finset W := {15,3840,4369,4593,8738,17476,63624}
private def s6_91 : Finset W := {15,512,4593,8738,17476,34952,61440}
private def s6_92 : Finset W := {15,4593,8738,17476,20292,34952,61440}
private def s6_93 : Finset W := {15,3840,4593,8738,17476,36744,61440}
private def s6_94 : Finset W := {15,4593,8738,17476,34952,36744,61440}
private def s6_95 : Finset W := {15,4593,8738,17476,36744,61440}
private def s6_96 : Finset W := {15,3840,4593,8738,17476,39417,61440}
private def s6_97 : Finset W := {15,3840,4593,8738,17476,43690,61440}
private def s6_98 : Finset W := {15,3840,4593,17476,34952,61440,61986}
private def s6_99 : Finset W := {15,3840,4593,8738,17476,34952,62532}
private def s6_100 : Finset W := {15,3840,4593,8738,34952,61440,62532}
private def s6_101 : Finset W := {15,3840,4593,8738,34952,62532}
private def s6_102 : Finset W := {15,3840,4593,8738,17476,61440,63624}
private def s6_103 : Finset W := {15,64,3840,4369,8946,34952,61440}
private def s6_104 : Finset W := {15,3840,4369,8946,17476,35064,61440}
private def s6_105 : Finset W := {15,240,4369,8946,20292,34952,61440}
private def s6_106 : Finset W := {15,240,3840,4369,8946,34952,62532}
private def s6_107 : Finset W := {15,240,3840,4369,8946,17476,63624}
private def s6_108 : Finset W := {15,7953,8738,8946,17476,34952,61440}
private def s6_109 : Finset W := {15,512,4369,8946,17476,34952,61440}
private def s6_110 : Finset W := {15,4369,8738,8946,20292,34952,61440}
private def s6_111 : Finset W := {15,4369,8738,8946,17476,36744,61440}
private def s6_112 : Finset W := {15,3840,4369,8946,17476,43690,61440}
private def s6_113 : Finset W := {15,3840,4369,8946,17476,34952,61986}
private def s6_114 : Finset W := {15,3840,4369,8738,17476,43770,61440}
private def s6_115 : Finset W := {15,3840,4369,8738,8946,17476,63624}
private def s6_116 : Finset W := {15,3840,7953,8946,17476,34952,61440}
private def s6_117 : Finset W := {15,3840,4369,8946,20292,34952,61440}
private def s6_118 : Finset W := {15,4369,8946,17476,20292,34952,61440}
private def s6_119 : Finset W := {15,4369,8946,20292,34952,61440}
private def s6_120 : Finset W := {15,3840,4369,8946,17476,36744,61440}
private def s6_121 : Finset W := {15,3840,4369,8946,17476,39321,61440}
private def s6_122 : Finset W := {15,3840,4096,4369,8946,17476,34952}
private def s6_123 : Finset W := {15,3840,4369,8946,17476,43770,61440}
private def s6_124 : Finset W := {15,3840,4369,8946,17476,34952,62532}
private def s6_125 : Finset W := {15,3840,4369,8946,17476,34952,63624}
private def s6_126 : Finset W := {15,3840,4369,8946,17476,61440,63624}
private def s6_127 : Finset W := {15,3840,4369,8946,17476,63624}
private def s6_128 : Finset W := {79,240,3840,4369,8738,34952,61440}
private def s6_129 : Finset W := {15,240,3904,4369,8738,34952,61440}
private def s6_130 : Finset W := {15,240,3840,4369,8738,34952,61504}
private def s6_131 : Finset W := {15,64,3840,4369,8738,35064,61440}
private def s6_132 : Finset W := {15,64,240,7953,8738,34952,61440}
private def s6_133 : Finset W := {15,64,240,4369,8738,36744,61440}
private def s6_134 : Finset W := {15,64,240,3840,4369,34952,61986}
private def s6_135 : Finset W := {15,64,240,3840,4369,8738,63624}
private def s6_136 : Finset W := {15,3840,4433,8738,17476,34952,61440}
private def s6_137 : Finset W := {15,3840,4369,8802,17476,34952,61440}
private def s6_138 : Finset W := {15,3840,4369,8738,17476,35016,61440}
private def s6_139 : Finset W := {15,64,7953,8738,17476,34952,61440}
private def s6_140 : Finset W := {15,64,4369,8738,20292,34952,61440}
private def s6_141 : Finset W := {15,64,4369,8738,17476,36744,61440}
private def s6_142 : Finset W := {15,64,3840,4369,17476,34952,61986}
private def s6_143 : Finset W := {15,64,3840,4369,8738,34952,62532}
private def s6_144 : Finset W := {15,64,3840,4369,8738,17476,63624}
private def s6_145 : Finset W := {64,79,3840,4369,8738,34952,61440}
private def s6_146 : Finset W := {15,64,3904,4369,8738,34952,61440}
private def s6_147 : Finset W := {15,64,3840,4433,8738,34952,61440}
private def s6_148 : Finset W := {15,64,3840,4369,8802,34952,61440}
private def s6_149 : Finset W := {15,64,3840,4369,8738,35016,61440}
private def s6_150 : Finset W := {15,64,3840,4369,8738,34952,61504}
private def s6_151 : Finset W := {15,64,3840,7953,8738,34952,61440}
private def s6_152 : Finset W := {15,64,4369,7953,8738,34952,61440}
private def s6_153 : Finset W := {15,64,7953,8738,34952,61440}
private def s6_154 : Finset W := {15,64,512,4369,8738,34952,61440}
private def s6_155 : Finset W := {15,64,3840,4369,8738,36744,61440}
private def s6_156 : Finset W := {15,64,4369,8738,34952,36744,61440}
private def s6_157 : Finset W := {15,64,4369,8738,36744,61440}
private def s6_158 : Finset W := {15,64,3840,4369,8738,39321,61440}
private def s6_159 : Finset W := {15,64,3840,4096,4369,8738,34952}
private def s6_160 : Finset W := {15,64,3840,4369,8738,43690,61440}
private def s6_161 : Finset W := {15,64,3840,4369,8738,34952,61986}
private def s6_162 : Finset W := {15,64,3840,4369,34952,61440,61986}
private def s6_163 : Finset W := {15,64,3840,4369,34952,61986}
private def s6_164 : Finset W := {15,64,3840,4369,8738,34952,63624}
private def s6_165 : Finset W := {15,64,3840,4369,8738,61440,63624}
private def s6_166 : Finset W := {15,64,3840,4369,8738,63624}
private def s6_167 : Finset W := {15,240,7953,8738,17476,35064,61440}
private def s6_168 : Finset W := {15,240,4369,8738,20292,35064,61440}
private def s6_169 : Finset W := {15,240,3840,4369,17476,35064,61986}
private def s6_170 : Finset W := {15,240,3840,4369,8738,35064,62532}
private def s6_171 : Finset W := {15,7953,8738,17476,34952,35064,61440}
private def s6_172 : Finset W := {15,4369,8738,17476,35064,36744,61440}
private def s6_173 : Finset W := {15,3840,4369,17476,34952,35064,61986}
private def s6_174 : Finset W := {15,3840,4369,8738,17476,35064,63624}
private def s6_175 : Finset W := {15,3840,7953,8738,17476,35064,61440}
private def s6_176 : Finset W := {15,4369,7953,8738,17476,35064,61440}
private def s6_177 : Finset W := {15,7953,8738,17476,35064,61440}
private def s6_178 : Finset W := {15,512,4369,8738,17476,35064,61440}
private def s6_179 : Finset W := {15,4369,8738,17476,20292,35064,61440}
private def s6_180 : Finset W := {15,3840,4096,4369,8738,17476,35064}
private def s6_181 : Finset W := {15,3840,4369,8738,17476,35064,61986}
private def s6_182 : Finset W := {15,3840,4369,17476,35064,61440,61986}
private def s6_183 : Finset W := {15,3840,4369,17476,35064,61986}
private def s6_184 : Finset W := {15,3840,4369,8738,17476,35064,62532}
private def s6_185 : Finset W := {15,240,7953,8738,20292,34952,61440}
private def s6_186 : Finset W := {15,240,7953,8738,17476,36744,61440}
private def s6_187 : Finset W := {15,240,3840,7953,17476,34952,61986}
private def s6_188 : Finset W := {15,240,7953,8738,17476,39321,61440}
private def s6_189 : Finset W := {15,240,4096,7953,8738,17476,34952}
private def s6_190 : Finset W := {15,240,4369,8738,17476,40857,61440}
private def s6_191 : Finset W := {15,240,4369,7953,17476,34952,61986}
private def s6_192 : Finset W := {15,240,4369,7953,8738,34952,62532}
private def s6_193 : Finset W := {15,240,4369,7953,8738,17476,63624}
private def s6_194 : Finset W := {15,240,7953,8738,17476,40857,61440}
private def s6_195 : Finset W := {15,240,7953,8738,17476,43690,61440}
private def s6_196 : Finset W := {15,240,7953,8738,17476,34952,61986}
private def s6_197 : Finset W := {15,240,7953,17476,34952,61440,61986}
private def s6_198 : Finset W := {15,240,7953,17476,34952,61986}
private def s6_199 : Finset W := {15,240,7953,8738,34952,61440,62532}
private def s6_200 : Finset W := {15,240,7953,8738,17476,61440,63624}
private def s6_201 : Finset W := {240,527,4369,8738,17476,34952,61440}
private def s6_202 : Finset W := {15,240,4881,8738,17476,34952,61440}
private def s6_203 : Finset W := {15,240,4369,8738,17988,34952,61440}
private def s6_204 : Finset W := {15,240,4369,8738,17476,35464,61440}
private def s6_205 : Finset W := {15,240,512,4369,17476,43690,61440}
private def s6_206 : Finset W := {15,240,512,4369,17476,34952,61986}
private def s6_207 : Finset W := {15,240,512,4369,8738,34952,62532}
private def s6_208 : Finset W := {15,240,512,4369,8738,17476,63624}
private def s6_209 : Finset W := {15,240,4369,8738,20292,36744,61440}
private def s6_210 : Finset W := {15,240,3840,4369,20292,34952,61986}
private def s6_211 : Finset W := {15,240,3840,4369,8738,20292,63624}
private def s6_212 : Finset W := {15,240,4369,8738,20292,34952,62532}
private def s6_213 : Finset W := {15,240,4369,8738,17476,20292,63624}
private def s6_214 : Finset W := {15,240,4369,8738,20292,39321,61440}
private def s6_215 : Finset W := {15,240,4096,4369,8738,20292,34952}
private def s6_216 : Finset W := {15,240,4369,8738,20292,43690,61440}
private def s6_217 : Finset W := {15,240,4369,8738,20292,34952,61986}
private def s6_218 : Finset W := {15,240,4369,8738,20292,34952,63624}
private def s6_219 : Finset W := {15,240,4369,8738,20292,61440,63624}
private def s6_220 : Finset W := {15,240,4369,8738,20292,63624}
private def s6_221 : Finset W := {15,240,3840,4369,17476,36744,61986}
private def s6_222 : Finset W := {15,240,3840,4369,8738,36744,62532}
private def s6_223 : Finset W := {15,240,4369,8738,34952,36744,62532}
private def s6_224 : Finset W := {15,240,4369,8738,17476,36744,63624}
private def s6_225 : Finset W := {15,240,4096,4369,8738,17476,36744}
private def s6_226 : Finset W := {15,240,4369,8738,17476,36744,61986}
private def s6_227 : Finset W := {15,240,4369,8738,17476,36744,62532}
private def s6_228 : Finset W := {15,240,4369,8738,36744,61440,62532}
private def s6_229 : Finset W := {15,240,4369,8738,36744,62532}
private def s6_230 : Finset W := {15,240,3840,4096,8738,17476,39321}
private def s6_231 : Finset W := {15,240,3840,4369,17476,39321,61986}
private def s6_232 : Finset W := {15,240,3840,4369,8738,39321,62532}
private def s6_233 : Finset W := {240,3840,4111,4369,8738,17476,34952}
private def s6_234 : Finset W := {15,240,3840,4369,12834,17476,34952}
private def s6_235 : Finset W := {15,240,3840,4369,8738,21572,34952}
private def s6_236 : Finset W := {15,240,3840,4369,8738,17476,39048}
private def s6_237 : Finset W := {15,240,3840,4369,17476,43690,61986}
private def s6_238 : Finset W := {15,240,3840,4369,8738,43690,62532}
private def s6_239 : Finset W := {15,240,3840,4369,8738,17476,64170}
private def s6_240 : Finset W := {15,240,3840,4369,34952,61986,62532}
private def s6_241 : Finset W := {15,240,3840,4369,17476,61986,63624}
private def s6_242 : Finset W := {15,240,3840,4369,17476,61986,64170}
private def s6_243 : Finset W := {15,240,3840,4369,8738,62532,63624}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_0 : search 6 s6_0 = false := by
  apply row (k := 4) (covered := [s5_0,s5_1,s5_2])
  · decide +kernel
  · exact allCons c5_0 (allCons c5_1 (allCons c5_2 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_1 : search 6 s6_1 = false := by
  apply row (k := 4) (covered := [s5_0,s5_3,s5_4])
  · decide +kernel
  · exact allCons c5_0 (allCons c5_3 (allCons c5_4 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_2 : search 6 s6_2 = false := by
  apply row (k := 4) (covered := [s5_1,s5_5,s5_6])
  · decide +kernel
  · exact allCons c5_1 (allCons c5_5 (allCons c5_6 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_3 : search 6 s6_3 = false := by
  apply row (k := 4) (covered := [s5_7,s5_8,s5_9,s5_10])
  · decide +kernel
  · exact allCons c5_7 (allCons c5_8 (allCons c5_9 (allCons c5_10 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_4 : search 6 s6_4 = false := by
  apply row (k := 4) (covered := [s5_2,s5_11,s5_12])
  · decide +kernel
  · exact allCons c5_2 (allCons c5_11 (allCons c5_12 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_5 : search 6 s6_5 = false := by
  apply row (k := 4) (covered := [s5_7,s5_11,s5_13])
  · decide +kernel
  · exact allCons c5_7 (allCons c5_11 (allCons c5_13 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_6 : search 6 s6_6 = false := by
  apply row (k := 4) (covered := [s5_5,s5_14])
  · decide +kernel
  · exact allCons c5_5 (allCons c5_14 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_7 : search 6 s6_7 = false := by
  apply row (k := 4) (covered := [s5_3,s5_8,s5_15])
  · decide +kernel
  · exact allCons c5_3 (allCons c5_8 (allCons c5_15 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_8 : search 6 s6_8 = false := by
  apply row (k := 4) (covered := [s5_9,s5_12,s5_13])
  · decide +kernel
  · exact allCons c5_9 (allCons c5_12 (allCons c5_13 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_9 : search 6 s6_9 = false := by
  apply row (k := 4) (covered := [s5_4,s5_15])
  · decide +kernel
  · exact allCons c5_4 (allCons c5_15 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_10 : search 6 s6_10 = false := by
  apply row (k := 4) (covered := [s5_6,s5_10,s5_14])
  · decide +kernel
  · exact allCons c5_6 (allCons c5_10 (allCons c5_14 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_11 : search 6 s6_11 = false := by
  apply row (k := 4) (covered := [s5_16,s5_17,s5_18,s5_19,s5_20,s5_21,s5_22])
  · decide +kernel
  · exact allCons c5_16 (allCons c5_17 (allCons c5_18 (allCons c5_19 (allCons c5_20 (allCons c5_21 (allCons c5_22 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_12 : search 6 s6_12 = false := by
  apply row (k := 4) (covered := [s5_23,s5_24,s5_25,s5_26,s5_27,s5_21])
  · decide +kernel
  · exact allCons c5_23 (allCons c5_24 (allCons c5_25 (allCons c5_26 (allCons c5_27 (allCons c5_21 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_13 : search 6 s6_13 = false := by
  apply row (k := 4) (covered := [s5_16,s5_23,s5_28,s5_29])
  · decide +kernel
  · exact allCons c5_16 (allCons c5_23 (allCons c5_28 (allCons c5_29 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_14 : search 6 s6_14 = false := by
  apply row (k := 4) (covered := [s5_17,s5_24,s5_30,s5_31])
  · decide +kernel
  · exact allCons c5_17 (allCons c5_24 (allCons c5_30 (allCons c5_31 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_15 : search 6 s6_15 = false := by
  apply row (k := 4) (covered := [s5_25,s5_32,s5_33,s5_34])
  · decide +kernel
  · exact allCons c5_25 (allCons c5_32 (allCons c5_33 (allCons c5_34 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_16 : search 6 s6_16 = false := by
  apply row (k := 4) (covered := [s5_18,s5_26,s5_35,s5_36])
  · decide +kernel
  · exact allCons c5_18 (allCons c5_26 (allCons c5_35 (allCons c5_36 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_17 : search 6 s6_17 = false := by
  apply row (k := 4) (covered := [s5_19,s5_28,s5_32,s5_35,s5_37,s5_38])
  · decide +kernel
  · exact allCons c5_19 (allCons c5_28 (allCons c5_32 (allCons c5_35 (allCons c5_37 (allCons c5_38 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_18 : search 6 s6_18 = false := by
  apply row (k := 4) (covered := [s5_27,s5_30,s5_39])
  · decide +kernel
  · exact allCons c5_27 (allCons c5_30 (allCons c5_39 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_19 : search 6 s6_19 = false := by
  apply row (k := 4) (covered := [s5_20,s5_33,s5_36])
  · decide +kernel
  · exact allCons c5_20 (allCons c5_33 (allCons c5_36 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_20 : search 6 s6_20 = false := by
  apply row (k := 4) (covered := [s5_21,s5_29,s5_37])
  · decide +kernel
  · exact allCons c5_21 (allCons c5_29 (allCons c5_37 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_21 : search 6 s6_21 = false := by
  apply row (k := 4) (covered := [s5_22,s5_31,s5_34,s5_38,s5_39])
  · decide +kernel
  · exact allCons c5_22 (allCons c5_31 (allCons c5_34 (allCons c5_38 (allCons c5_39 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_22 : search 6 s6_22 = false := by
  apply row (k := 4) (covered := [s5_40,s5_41,s5_42,s5_43,s5_44])
  · decide +kernel
  · exact allCons c5_40 (allCons c5_41 (allCons c5_42 (allCons c5_43 (allCons c5_44 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_23 : search 6 s6_23 = false := by
  apply row (k := 4) (covered := [s5_45,s5_46,s5_47,s5_48,s5_27,s5_49,s5_50])
  · decide +kernel
  · exact allCons c5_45 (allCons c5_46 (allCons c5_47 (allCons c5_48 (allCons c5_27 (allCons c5_49 (allCons c5_50 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_24 : search 6 s6_24 = false := by
  apply row (k := 4) (covered := [s5_16,s5_0,s5_43,s5_45,s5_51,s5_52])
  · decide +kernel
  · exact allCons c5_16 (allCons c5_0 (allCons c5_43 (allCons c5_45 (allCons c5_51 (allCons c5_52 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_25 : search 6 s6_25 = false := by
  apply row (k := 4) (covered := [s5_17,s5_1,s5_44,s5_46,s5_30,s5_53])
  · decide +kernel
  · exact allCons c5_17 (allCons c5_1 (allCons c5_44 (allCons c5_46 (allCons c5_30 (allCons c5_53 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_26 : search 6 s6_26 = false := by
  apply row (k := 4) (covered := [s5_18,s5_2,s5_47,s5_54,s5_55,s5_56])
  · decide +kernel
  · exact allCons c5_18 (allCons c5_2 (allCons c5_47 (allCons c5_54 (allCons c5_55 (allCons c5_56 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_27 : search 6 s6_27 = false := by
  apply row (k := 4) (covered := [s5_48,s5_7,s5_54,s5_57])
  · decide +kernel
  · exact allCons c5_48 (allCons c5_7 (allCons c5_54 (allCons c5_57 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_28 : search 6 s6_28 = false := by
  apply row (k := 4) (covered := [s5_49,s5_51,s5_8,s5_58])
  · decide +kernel
  · exact allCons c5_49 (allCons c5_51 (allCons c5_8 (allCons c5_58 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_29 : search 6 s6_29 = false := by
  apply row (k := 4) (covered := [s5_20,s5_9,s5_55,s5_57])
  · decide +kernel
  · exact allCons c5_20 (allCons c5_9 (allCons c5_55 (allCons c5_57 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_30 : search 6 s6_30 = false := by
  apply row (k := 4) (covered := [s5_21,s5_52,s5_58])
  · decide +kernel
  · exact allCons c5_21 (allCons c5_52 (allCons c5_58 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_31 : search 6 s6_31 = false := by
  apply row (k := 4) (covered := [s5_22,s5_53,s5_10,s5_39])
  · decide +kernel
  · exact allCons c5_22 (allCons c5_53 (allCons c5_10 (allCons c5_39 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_32 : search 6 s6_32 = false := by
  apply row (k := 4) (covered := [s5_59,s5_0,s5_60])
  · decide +kernel
  · exact allCons c5_59 (allCons c5_0 (allCons c5_60 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_33 : search 6 s6_33 = false := by
  apply row (k := 4) (covered := [s5_61,s5_1,s5_62])
  · decide +kernel
  · exact allCons c5_61 (allCons c5_1 (allCons c5_62 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_34 : search 6 s6_34 = false := by
  apply row (k := 4) (covered := [s5_63,s5_64,s5_65])
  · decide +kernel
  · exact allCons c5_63 (allCons c5_64 (allCons c5_65 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_35 : search 6 s6_35 = false := by
  apply row (k := 4) (covered := [s5_66,s5_2,s5_67])
  · decide +kernel
  · exact allCons c5_66 (allCons c5_2 (allCons c5_67 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_36 : search 6 s6_36 = false := by
  apply row (k := 4) (covered := [s5_59,s5_61,s5_66])
  · decide +kernel
  · exact allCons c5_59 (allCons c5_61 (allCons c5_66 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_37 : search 6 s6_37 = false := by
  apply row (k := 4) (covered := [s5_60,s5_62,s5_67])
  · decide +kernel
  · exact allCons c5_60 (allCons c5_62 (allCons c5_67 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_38 : search 6 s6_38 = false := by
  apply row (k := 4) (covered := [s5_0,s5_68,s5_69])
  · decide +kernel
  · exact allCons c5_0 (allCons c5_68 (allCons c5_69 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_39 : search 6 s6_39 = false := by
  apply row (k := 4) (covered := [s5_70,s5_0,s5_71,s5_72,s5_73])
  · decide +kernel
  · exact allCons c5_70 (allCons c5_0 (allCons c5_71 (allCons c5_72 (allCons c5_73 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_40 : search 6 s6_40 = false := by
  apply row (k := 4) (covered := [s5_0,s5_74,s5_75,s5_76,s5_77,s5_72,s5_78,s5_43,s5_79])
  · decide +kernel
  · exact allCons c5_0 (allCons c5_74 (allCons c5_75 (allCons c5_76 (allCons c5_77 (allCons c5_72 (allCons c5_78 (allCons c5_43 (allCons c5_79 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_41 : search 6 s6_41 = false := by
  apply row (k := 4) (covered := [s5_68,s5_1,s5_80])
  · decide +kernel
  · exact allCons c5_68 (allCons c5_1 (allCons c5_80 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_42 : search 6 s6_42 = false := by
  apply row (k := 4) (covered := [s5_81,s5_1,s5_82,s5_83,s5_84])
  · decide +kernel
  · exact allCons c5_81 (allCons c5_1 (allCons c5_82 (allCons c5_83 (allCons c5_84 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_43 : search 6 s6_43 = false := by
  apply row (k := 4) (covered := [s5_1,s5_81,s5_85,s5_86,s5_87,s5_88,s5_44,s5_89,s5_90])
  · decide +kernel
  · exact allCons c5_1 (allCons c5_81 (allCons c5_85 (allCons c5_86 (allCons c5_87 (allCons c5_88 (allCons c5_44 (allCons c5_89 (allCons c5_90 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_44 : search 6 s6_44 = false := by
  apply row (k := 4) (covered := [s5_69,s5_80,s5_2])
  · decide +kernel
  · exact allCons c5_69 (allCons c5_80 (allCons c5_2 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_45 : search 6 s6_45 = false := by
  apply row (k := 4) (covered := [s5_91,s5_2,s5_92])
  · decide +kernel
  · exact allCons c5_91 (allCons c5_2 (allCons c5_92 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_46 : search 6 s6_46 = false := by
  apply row (k := 4) (covered := [s5_2,s5_93,s5_94,s5_95,s5_73,s5_96,s5_84,s5_97,s5_98,s5_99])
  · decide +kernel
  · exact allCons c5_2 (allCons c5_93 (allCons c5_94 (allCons c5_95 (allCons c5_73 (allCons c5_96 (allCons c5_84 (allCons c5_97 (allCons c5_98 (allCons c5_99 (allNil 5))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_47 : search 6 s6_47 = false := by
  apply row (k := 4) (covered := [s5_70,s5_93,s5_100])
  · decide +kernel
  · exact allCons c5_70 (allCons c5_93 (allCons c5_100 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_48 : search 6 s6_48 = false := by
  apply row (k := 4) (covered := [s5_74,s5_81,s5_94,s5_101,s5_102,s5_103,s5_104])
  · decide +kernel
  · exact allCons c5_74 (allCons c5_81 (allCons c5_94 (allCons c5_101 (allCons c5_102 (allCons c5_103 (allCons c5_104 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_49 : search 6 s6_49 = false := by
  apply row (k := 4) (covered := [s5_75,s5_85,s5_95,s5_19,s5_105])
  · decide +kernel
  · exact allCons c5_75 (allCons c5_85 (allCons c5_95 (allCons c5_19 (allCons c5_105 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_50 : search 6 s6_50 = false := by
  apply row (k := 4) (covered := [s5_76,s5_91,s5_106])
  · decide +kernel
  · exact allCons c5_76 (allCons c5_91 (allCons c5_106 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_51 : search 6 s6_51 = false := by
  apply row (k := 4) (covered := [s5_71,s5_86,s5_73,s5_100,s5_107])
  · decide +kernel
  · exact allCons c5_71 (allCons c5_86 (allCons c5_73 (allCons c5_100 (allCons c5_107 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_52 : search 6 s6_52 = false := by
  apply row (k := 4) (covered := [s5_72,s5_87,s5_96,s5_108,s5_109,s5_110,s5_107])
  · decide +kernel
  · exact allCons c5_72 (allCons c5_87 (allCons c5_96 (allCons c5_108 (allCons c5_109 (allCons c5_110 (allCons c5_107 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_53 : search 6 s6_53 = false := by
  apply row (k := 4) (covered := [s5_78,s5_82,s5_84,s5_104,s5_111])
  · decide +kernel
  · exact allCons c5_78 (allCons c5_82 (allCons c5_84 (allCons c5_104 (allCons c5_111 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_54 : search 6 s6_54 = false := by
  apply row (k := 4) (covered := [s5_83,s5_97,s5_111])
  · decide +kernel
  · exact allCons c5_83 (allCons c5_97 (allCons c5_111 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_55 : search 6 s6_55 = false := by
  apply row (k := 4) (covered := [s5_79,s5_89,s5_99,s5_105,s5_50])
  · decide +kernel
  · exact allCons c5_79 (allCons c5_89 (allCons c5_99 (allCons c5_105 (allCons c5_50 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_56 : search 6 s6_56 = false := by
  apply row (k := 4) (covered := [s5_90,s5_92,s5_106])
  · decide +kernel
  · exact allCons c5_90 (allCons c5_92 (allCons c5_106 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_57 : search 6 s6_57 = false := by
  apply row (k := 4) (covered := [s5_40,s5_112,s5_113,s5_114,s5_115,s5_116,s5_117])
  · decide +kernel
  · exact allCons c5_40 (allCons c5_112 (allCons c5_113 (allCons c5_114 (allCons c5_115 (allCons c5_116 (allCons c5_117 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_58 : search 6 s6_58 = false := by
  apply row (k := 4) (covered := [s5_118,s5_119,s5_120,s5_121,s5_122,s5_123])
  · decide +kernel
  · exact allCons c5_118 (allCons c5_119 (allCons c5_120 (allCons c5_121 (allCons c5_122 (allCons c5_123 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_59 : search 6 s6_59 = false := by
  apply row (k := 4) (covered := [s5_41,s5_112,s5_124,s5_125,s5_121,s5_126,s5_127,s5_128])
  · decide +kernel
  · exact allCons c5_41 (allCons c5_112 (allCons c5_124 (allCons c5_125 (allCons c5_121 (allCons c5_126 (allCons c5_127 (allCons c5_128 (allNil 5))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_60 : search 6 s6_60 = false := by
  apply row (k := 4) (covered := [s5_42,s5_129,s5_113,s5_130,s5_131,s5_132,s5_133,s5_134])
  · decide +kernel
  · exact allCons c5_42 (allCons c5_129 (allCons c5_113 (allCons c5_130 (allCons c5_131 (allCons c5_132 (allCons c5_133 (allCons c5_134 (allNil 5))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_61 : search 6 s6_61 = false := by
  apply row (k := 4) (covered := [s5_135,s5_136,s5_137,s5_138,s5_139,s5_133])
  · decide +kernel
  · exact allCons c5_135 (allCons c5_136 (allCons c5_137 (allCons c5_138 (allCons c5_139 (allCons c5_133 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_62 : search 6 s6_62 = false := by
  apply row (k := 4) (covered := [s5_118,s5_112,s5_129,s5_135,s5_43,s5_140])
  · decide +kernel
  · exact allCons c5_118 (allCons c5_112 (allCons c5_129 (allCons c5_135 (allCons c5_43 (allCons c5_140 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_63 : search 6 s6_63 = false := by
  apply row (k := 4) (covered := [s5_119,s5_124,s5_113,s5_136,s5_44,s5_141])
  · decide +kernel
  · exact allCons c5_119 (allCons c5_124 (allCons c5_113 (allCons c5_136 (allCons c5_44 (allCons c5_141 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_64 : search 6 s6_64 = false := by
  apply row (k := 4) (covered := [s5_56,s5_120,s5_125,s5_130,s5_137,s5_142,s5_143])
  · decide +kernel
  · exact allCons c5_56 (allCons c5_120 (allCons c5_125 (allCons c5_130 (allCons c5_137 (allCons c5_142 (allCons c5_143 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_65 : search 6 s6_65 = false := by
  apply row (k := 4) (covered := [s5_114,s5_121,s5_131,s5_138,s5_142,s5_144])
  · decide +kernel
  · exact allCons c5_114 (allCons c5_121 (allCons c5_131 (allCons c5_138 (allCons c5_142 (allCons c5_144 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_66 : search 6 s6_66 = false := by
  apply row (k := 4) (covered := [s5_115,s5_126,s5_132,s5_139,s5_141])
  · decide +kernel
  · exact allCons c5_115 (allCons c5_126 (allCons c5_132 (allCons c5_139 (allCons c5_141 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_67 : search 6 s6_67 = false := by
  apply row (k := 4) (covered := [s5_116,s5_122,s5_127,s5_133,s5_143,s5_144])
  · decide +kernel
  · exact allCons c5_116 (allCons c5_122 (allCons c5_127 (allCons c5_133 (allCons c5_143 (allCons c5_144 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_68 : search 6 s6_68 = false := by
  apply row (k := 4) (covered := [s5_117,s5_123,s5_128,s5_134,s5_140])
  · decide +kernel
  · exact allCons c5_117 (allCons c5_123 (allCons c5_128 (allCons c5_134 (allCons c5_140 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_69 : search 6 s6_69 = false := by
  apply row (k := 4) (covered := [s5_23,s5_45,s5_145,s5_52])
  · decide +kernel
  · exact allCons c5_23 (allCons c5_45 (allCons c5_145 (allCons c5_52 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_70 : search 6 s6_70 = false := by
  apply row (k := 4) (covered := [s5_24,s5_46,s5_146,s5_147])
  · decide +kernel
  · exact allCons c5_24 (allCons c5_46 (allCons c5_146 (allCons c5_147 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_71 : search 6 s6_71 = false := by
  apply row (k := 4) (covered := [s5_25,s5_148,s5_149,s5_150])
  · decide +kernel
  · exact allCons c5_25 (allCons c5_148 (allCons c5_149 (allCons c5_150 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_72 : search 6 s6_72 = false := by
  apply row (k := 4) (covered := [s5_26,s5_47,s5_151,s5_152])
  · decide +kernel
  · exact allCons c5_26 (allCons c5_47 (allCons c5_151 (allCons c5_152 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_73 : search 6 s6_73 = false := by
  apply row (k := 4) (covered := [s5_48,s5_148,s5_151])
  · decide +kernel
  · exact allCons c5_48 (allCons c5_148 (allCons c5_151 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_74 : search 6 s6_74 = false := by
  apply row (k := 4) (covered := [s5_27,s5_146,s5_153])
  · decide +kernel
  · exact allCons c5_27 (allCons c5_146 (allCons c5_153 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_75 : search 6 s6_75 = false := by
  apply row (k := 4) (covered := [s5_49,s5_145,s5_149,s5_154,s5_58])
  · decide +kernel
  · exact allCons c5_49 (allCons c5_145 (allCons c5_149 (allCons c5_154 (allCons c5_58 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_76 : search 6 s6_76 = false := by
  apply row (k := 4) (covered := [s5_50,s5_147,s5_150,s5_152,s5_153,s5_154])
  · decide +kernel
  · exact allCons c5_50 (allCons c5_147 (allCons c5_150 (allCons c5_152 (allCons c5_153 (allCons c5_154 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_77 : search 6 s6_77 = false := by
  apply row (k := 4) (covered := [s5_68,s5_155,s5_156])
  · decide +kernel
  · exact allCons c5_68 (allCons c5_155 (allCons c5_156 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_78 : search 6 s6_78 = false := by
  apply row (k := 4) (covered := [s5_157,s5_158,s5_159])
  · decide +kernel
  · exact allCons c5_157 (allCons c5_158 (allCons c5_159 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_79 : search 6 s6_79 = false := by
  apply row (k := 4) (covered := [s5_69,s5_160,s5_161])
  · decide +kernel
  · exact allCons c5_69 (allCons c5_160 (allCons c5_161 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_80 : search 6 s6_80 = false := by
  apply row (k := 4) (covered := [s5_155,s5_160])
  · decide +kernel
  · exact allCons c5_155 (allCons c5_160 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_81 : search 6 s6_81 = false := by
  apply row (k := 4) (covered := [s5_3,s5_159,s5_162])
  · decide +kernel
  · exact allCons c5_3 (allCons c5_159 (allCons c5_162 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_82 : search 6 s6_82 = false := by
  apply row (k := 4) (covered := [s5_4,s5_156,s5_161,s5_162])
  · decide +kernel
  · exact allCons c5_4 (allCons c5_156 (allCons c5_161 (allCons c5_162 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_83 : search 6 s6_83 = false := by
  apply row (k := 4) (covered := [s5_70,s5_7,s5_163,s5_164,s5_165,s5_166,s5_167])
  · decide +kernel
  · exact allCons c5_70 (allCons c5_7 (allCons c5_163 (allCons c5_164 (allCons c5_165 (allCons c5_166 (allCons c5_167 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_84 : search 6 s6_84 = false := by
  apply row (k := 4) (covered := [s5_3,s5_164,s5_168,s5_8,s5_169])
  · decide +kernel
  · exact allCons c5_3 (allCons c5_164 (allCons c5_168 (allCons c5_8 (allCons c5_169 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_85 : search 6 s6_85 = false := by
  apply row (k := 4) (covered := [s5_71,s5_164,s5_170,s5_171])
  · decide +kernel
  · exact allCons c5_71 (allCons c5_164 (allCons c5_170 (allCons c5_171 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_86 : search 6 s6_86 = false := by
  apply row (k := 4) (covered := [s5_172,s5_72,s5_168,s5_173,s5_174])
  · decide +kernel
  · exact allCons c5_172 (allCons c5_72 (allCons c5_168 (allCons c5_173 (allCons c5_174 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_87 : search 6 s6_87 = false := by
  apply row (k := 4) (covered := [s5_73,s5_163,s5_174,s5_175])
  · decide +kernel
  · exact allCons c5_73 (allCons c5_163 (allCons c5_174 (allCons c5_175 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_88 : search 6 s6_88 = false := by
  apply row (k := 4) (covered := [s5_165,s5_170,s5_9,s5_175])
  · decide +kernel
  · exact allCons c5_165 (allCons c5_170 (allCons c5_9 (allCons c5_175 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_89 : search 6 s6_89 = false := by
  apply row (k := 4) (covered := [s5_166,s5_169,s5_4,s5_171,s5_176])
  · decide +kernel
  · exact allCons c5_166 (allCons c5_169 (allCons c5_4 (allCons c5_171 (allCons c5_176 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_90 : search 6 s6_90 = false := by
  apply row (k := 4) (covered := [s5_167,s5_10])
  · decide +kernel
  · exact allCons c5_167 (allCons c5_10 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_91 : search 6 s6_91 = false := by
  apply row (k := 4) (covered := [s5_177,s5_74,s5_178,s5_179,s5_180,s5_181])
  · decide +kernel
  · exact allCons c5_177 (allCons c5_74 (allCons c5_178 (allCons c5_179 (allCons c5_180 (allCons c5_181 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_92 : search 6 s6_92 = false := by
  apply row (k := 4) (covered := [s5_59,s5_182])
  · decide +kernel
  · exact allCons c5_59 (allCons c5_182 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_93 : search 6 s6_93 = false := by
  apply row (k := 4) (covered := [s5_3,s5_183])
  · decide +kernel
  · exact allCons c5_3 (allCons c5_183 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_94 : search 6 s6_94 = false := by
  apply row (k := 4) (covered := [s5_76,s5_184,s5_3])
  · decide +kernel
  · exact allCons c5_76 (allCons c5_184 (allCons c5_3 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_95 : search 6 s6_95 = false := by
  apply row (k := 4) (covered := [s5_3,s5_51,s5_145,s5_159,s5_168,s5_185,s5_186,s5_187])
  · decide +kernel
  · exact allCons c5_3 (allCons c5_51 (allCons c5_145 (allCons c5_159 (allCons c5_168 (allCons c5_185 (allCons c5_186 (allCons c5_187 (allNil 5))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_96 : search 6 s6_96 = false := by
  apply row (k := 4) (covered := [s5_77,s5_174,s5_188])
  · decide +kernel
  · exact allCons c5_77 (allCons c5_174 (allCons c5_188 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_97 : search 6 s6_97 = false := by
  apply row (k := 4) (covered := [s5_78,s5_180,s5_189])
  · decide +kernel
  · exact allCons c5_78 (allCons c5_180 (allCons c5_189 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_98 : search 6 s6_98 = false := by
  apply row (k := 4) (covered := [s5_190,s5_191])
  · decide +kernel
  · exact allCons c5_190 (allCons c5_191 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_99 : search 6 s6_99 = false := by
  apply row (k := 4) (covered := [s5_60,s5_182,s5_185,s5_4])
  · decide +kernel
  · exact allCons c5_60 (allCons c5_182 (allCons c5_185 (allCons c5_4 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_100 : search 6 s6_100 = false := by
  apply row (k := 4) (covered := [s5_186,s5_190,s5_192,s5_4])
  · decide +kernel
  · exact allCons c5_186 (allCons c5_190 (allCons c5_192 (allCons c5_4 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_101 : search 6 s6_101 = false := by
  apply row (k := 4) (covered := [s5_4,s5_29,s5_140,s5_52,s5_181,s5_183,s5_184,s5_187,s5_188,s5_193,s5_189])
  · decide +kernel
  · exact allCons c5_4 (allCons c5_29 (allCons c5_140 (allCons c5_52 (allCons c5_181 (allCons c5_183 (allCons c5_184 (allCons c5_187 (allCons c5_188 (allCons c5_193 (allCons c5_189 (allNil 5)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_102 : search 6 s6_102 = false := by
  apply row (k := 4) (covered := [s5_191,s5_192])
  · decide +kernel
  · exact allCons c5_191 (allCons c5_192 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_103 : search 6 s6_103 = false := by
  apply row (k := 4) (covered := [s5_194,s5_195,s5_196])
  · decide +kernel
  · exact allCons c5_194 (allCons c5_195 (allCons c5_196 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_104 : search 6 s6_104 = false := by
  apply row (k := 4) (covered := [s5_80,s5_197,s5_198])
  · decide +kernel
  · exact allCons c5_80 (allCons c5_197 (allCons c5_198 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_105 : search 6 s6_105 = false := by
  apply row (k := 4) (covered := [s5_155,s5_5,s5_197,s5_199])
  · decide +kernel
  · exact allCons c5_155 (allCons c5_5 (allCons c5_197 (allCons c5_199 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_106 : search 6 s6_106 = false := by
  apply row (k := 4) (covered := [s5_156,s5_198])
  · decide +kernel
  · exact allCons c5_156 (allCons c5_198 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_107 : search 6 s6_107 = false := by
  apply row (k := 4) (covered := [s5_6,s5_196,s5_199])
  · decide +kernel
  · exact allCons c5_6 (allCons c5_196 (allCons c5_199 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_108 : search 6 s6_108 = false := by
  apply row (k := 4) (covered := [s5_200,s5_201,s5_7,s5_202])
  · decide +kernel
  · exact allCons c5_200 (allCons c5_201 (allCons c5_7 (allCons c5_202 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_109 : search 6 s6_109 = false := by
  apply row (k := 4) (covered := [s5_203,s5_81,s5_204,s5_205,s5_206])
  · decide +kernel
  · exact allCons c5_203 (allCons c5_81 (allCons c5_204 (allCons c5_205 (allCons c5_206 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_110 : search 6 s6_110 = false := by
  apply row (k := 4) (covered := [s5_5,s5_207,s5_208,s5_209,s5_210])
  · decide +kernel
  · exact allCons c5_5 (allCons c5_207 (allCons c5_208 (allCons c5_209 (allCons c5_210 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_111 : search 6 s6_111 = false := by
  apply row (k := 4) (covered := [s5_211,s5_8])
  · decide +kernel
  · exact allCons c5_211 (allCons c5_8 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_112 : search 6 s6_112 = false := by
  apply row (k := 4) (covered := [s5_82,s5_200,s5_207,s5_212])
  · decide +kernel
  · exact allCons c5_82 (allCons c5_200 (allCons c5_207 (allCons c5_212 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_113 : search 6 s6_113 = false := by
  apply row (k := 4) (covered := [s5_83,s5_201,s5_208,s5_211,s5_9,s5_213,s5_212])
  · decide +kernel
  · exact allCons c5_83 (allCons c5_201 (allCons c5_208 (allCons c5_211 (allCons c5_9 (allCons c5_213 (allCons c5_212 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_114 : search 6 s6_114 = false := by
  apply row (k := 4) (covered := [s5_84,s5_202,s5_205,s5_213])
  · decide +kernel
  · exact allCons c5_84 (allCons c5_202 (allCons c5_205 (allCons c5_213 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_115 : search 6 s6_115 = false := by
  apply row (k := 4) (covered := [s5_206,s5_210,s5_6,s5_212,s5_10])
  · decide +kernel
  · exact allCons c5_206 (allCons c5_210 (allCons c5_6 (allCons c5_212 (allCons c5_10 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_116 : search 6 s6_116 = false := by
  apply row (k := 4) (covered := [s5_214,s5_215])
  · decide +kernel
  · exact allCons c5_214 (allCons c5_215 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_117 : search 6 s6_117 = false := by
  apply row (k := 4) (covered := [s5_214,s5_5,s5_216,s5_217])
  · decide +kernel
  · exact allCons c5_214 (allCons c5_5 (allCons c5_216 (allCons c5_217 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_118 : search 6 s6_118 = false := by
  apply row (k := 4) (covered := [s5_61,s5_5,s5_218,s5_219])
  · decide +kernel
  · exact allCons c5_61 (allCons c5_5 (allCons c5_218 (allCons c5_219 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_119 : search 6 s6_119 = false := by
  apply row (k := 4) (covered := [s5_5,s5_30,s5_141,s5_146,s5_220,s5_221,s5_222,s5_223,s5_224,s5_225,s5_226])
  · decide +kernel
  · exact allCons c5_5 (allCons c5_30 (allCons c5_141 (allCons c5_146 (allCons c5_220 (allCons c5_221 (allCons c5_222 (allCons c5_223 (allCons c5_224 (allCons c5_225 (allCons c5_226 (allNil 5)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_120 : search 6 s6_120 = false := by
  apply row (k := 4) (covered := [s5_215,s5_216])
  · decide +kernel
  · exact allCons c5_215 (allCons c5_216 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_121 : search 6 s6_121 = false := by
  apply row (k := 4) (covered := [s5_86,s5_220,s5_227])
  · decide +kernel
  · exact allCons c5_86 (allCons c5_220 (allCons c5_227 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_122 : search 6 s6_122 = false := by
  apply row (k := 4) (covered := [s5_228,s5_87,s5_221,s5_229,s5_230,s5_227])
  · decide +kernel
  · exact allCons c5_228 (allCons c5_87 (allCons c5_221 (allCons c5_229 (allCons c5_230 (allCons c5_227 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_123 : search 6 s6_123 = false := by
  apply row (k := 4) (covered := [s5_88,s5_205,s5_223])
  · decide +kernel
  · exact allCons c5_88 (allCons c5_205 (allCons c5_223 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_124 : search 6 s6_124 = false := by
  apply row (k := 4) (covered := [s5_62,s5_218])
  · decide +kernel
  · exact allCons c5_62 (allCons c5_218 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_125 : search 6 s6_125 = false := by
  apply row (k := 4) (covered := [s5_90,s5_224,s5_6])
  · decide +kernel
  · exact allCons c5_90 (allCons c5_224 (allCons c5_6 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_126 : search 6 s6_126 = false := by
  apply row (k := 4) (covered := [s5_225,s5_6])
  · decide +kernel
  · exact allCons c5_225 (allCons c5_6 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_127 : search 6 s6_127 = false := by
  apply row (k := 4) (covered := [s5_6,s5_31,s5_53,s5_206,s5_217,s5_219,s5_226,s5_196])
  · decide +kernel
  · exact allCons c5_6 (allCons c5_31 (allCons c5_53 (allCons c5_206 (allCons c5_217 (allCons c5_219 (allCons c5_226 (allCons c5_196 (allNil 5))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_128 : search 6 s6_128 = false := by
  apply row (k := 4) (covered := [s5_157,s5_194,s5_231,s5_232,s5_233,s5_234,s5_235])
  · decide +kernel
  · exact allCons c5_157 (allCons c5_194 (allCons c5_231 (allCons c5_232 (allCons c5_233 (allCons c5_234 (allCons c5_235 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_129 : search 6 s6_129 = false := by
  apply row (k := 4) (covered := [s5_195,s5_236,s5_237])
  · decide +kernel
  · exact allCons c5_195 (allCons c5_236 (allCons c5_237 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_130 : search 6 s6_130 = false := by
  apply row (k := 4) (covered := [s5_158,s5_238,s5_239])
  · decide +kernel
  · exact allCons c5_158 (allCons c5_238 (allCons c5_239 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_131 : search 6 s6_131 = false := by
  apply row (k := 4) (covered := [s5_231,s5_240,s5_241])
  · decide +kernel
  · exact allCons c5_231 (allCons c5_240 (allCons c5_241 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_132 : search 6 s6_132 = false := by
  apply row (k := 4) (covered := [s5_232,s5_7,s5_238,s5_240,s5_242])
  · decide +kernel
  · exact allCons c5_232 (allCons c5_7 (allCons c5_238 (allCons c5_240 (allCons c5_242 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_133 : search 6 s6_133 = false := by
  apply row (k := 4) (covered := [s5_233,s5_8,s5_239,s5_159])
  · decide +kernel
  · exact allCons c5_233 (allCons c5_8 (allCons c5_239 (allCons c5_159 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_134 : search 6 s6_134 = false := by
  apply row (k := 4) (covered := [s5_234,s5_9,s5_236,s5_241,s5_242])
  · decide +kernel
  · exact allCons c5_234 (allCons c5_9 (allCons c5_236 (allCons c5_241 (allCons c5_242 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_135 : search 6 s6_135 = false := by
  apply row (k := 4) (covered := [s5_235,s5_10,s5_237,s5_196])
  · decide +kernel
  · exact allCons c5_235 (allCons c5_10 (allCons c5_237 (allCons c5_196 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_136 : search 6 s6_136 = false := by
  apply row (k := 4) (covered := [s5_63,s5_243,s5_244,s5_245,s5_246])
  · decide +kernel
  · exact allCons c5_63 (allCons c5_243 (allCons c5_244 (allCons c5_245 (allCons c5_246 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_137 : search 6 s6_137 = false := by
  apply row (k := 4) (covered := [s5_64,s5_247,s5_248,s5_249,s5_250])
  · decide +kernel
  · exact allCons c5_64 (allCons c5_247 (allCons c5_248 (allCons c5_249 (allCons c5_250 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_138 : search 6 s6_138 = false := by
  apply row (k := 4) (covered := [s5_65,s5_251,s5_252])
  · decide +kernel
  · exact allCons c5_65 (allCons c5_251 (allCons c5_252 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_139 : search 6 s6_139 = false := by
  apply row (k := 4) (covered := [s5_247,s5_7,s5_251,s5_253])
  · decide +kernel
  · exact allCons c5_247 (allCons c5_7 (allCons c5_251 (allCons c5_253 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_140 : search 6 s6_140 = false := by
  apply row (k := 4) (covered := [s5_248,s5_254])
  · decide +kernel
  · exact allCons c5_248 (allCons c5_254 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_141 : search 6 s6_141 = false := by
  apply row (k := 4) (covered := [s5_243,s5_249,s5_8,s5_255])
  · decide +kernel
  · exact allCons c5_243 (allCons c5_249 (allCons c5_8 (allCons c5_255 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_142 : search 6 s6_142 = false := by
  apply row (k := 4) (covered := [s5_244,s5_9,s5_252,s5_253])
  · decide +kernel
  · exact allCons c5_244 (allCons c5_9 (allCons c5_252 (allCons c5_253 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_143 : search 6 s6_143 = false := by
  apply row (k := 4) (covered := [s5_245,s5_255])
  · decide +kernel
  · exact allCons c5_245 (allCons c5_255 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_144 : search 6 s6_144 = false := by
  apply row (k := 4) (covered := [s5_246,s5_250,s5_10,s5_254])
  · decide +kernel
  · exact allCons c5_246 (allCons c5_250 (allCons c5_10 (allCons c5_254 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_145 : search 6 s6_145 = false := by
  apply row (k := 4) (covered := [s5_256,s5_257,s5_258,s5_259,s5_260,s5_261,s5_262,s5_263,s5_264])
  · decide +kernel
  · exact allCons c5_256 (allCons c5_257 (allCons c5_258 (allCons c5_259 (allCons c5_260 (allCons c5_261 (allCons c5_262 (allCons c5_263 (allCons c5_264 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_146 : search 6 s6_146 = false := by
  apply row (k := 4) (covered := [s5_256,s5_265,s5_266,s5_267,s5_268,s5_269,s5_270])
  · decide +kernel
  · exact allCons c5_256 (allCons c5_265 (allCons c5_266 (allCons c5_267 (allCons c5_268 (allCons c5_269 (allCons c5_270 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_147 : search 6 s6_147 = false := by
  apply row (k := 4) (covered := [s5_257,s5_271,s5_272,s5_273,s5_267,s5_274,s5_275,s5_276])
  · decide +kernel
  · exact allCons c5_257 (allCons c5_271 (allCons c5_272 (allCons c5_273 (allCons c5_267 (allCons c5_274 (allCons c5_275 (allCons c5_276 (allNil 5))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_148 : search 6 s6_148 = false := by
  apply row (k := 4) (covered := [s5_258,s5_265,s5_271,s5_277,s5_278,s5_279,s5_280,s5_281])
  · decide +kernel
  · exact allCons c5_258 (allCons c5_265 (allCons c5_271 (allCons c5_277 (allCons c5_278 (allCons c5_279 (allCons c5_280 (allCons c5_281 (allNil 5))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_149 : search 6 s6_149 = false := by
  apply row (k := 4) (covered := [s5_259,s5_272,s5_277,s5_282,s5_268,s5_283,s5_284])
  · decide +kernel
  · exact allCons c5_259 (allCons c5_272 (allCons c5_277 (allCons c5_282 (allCons c5_268 (allCons c5_283 (allCons c5_284 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_150 : search 6 s6_150 = false := by
  apply row (k := 4) (covered := [s5_260,s5_266,s5_273,s5_285,s5_286,s5_280,s5_284])
  · decide +kernel
  · exact allCons c5_260 (allCons c5_266 (allCons c5_273 (allCons c5_285 (allCons c5_286 (allCons c5_280 (allCons c5_284 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_151 : search 6 s6_151 = false := by
  apply row (k := 4) (covered := [s5_7,s5_287,s5_288])
  · decide +kernel
  · exact allCons c5_7 (allCons c5_287 (allCons c5_288 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_152 : search 6 s6_152 = false := by
  apply row (k := 4) (covered := [s5_7,s5_289,s5_290,s5_291,s5_292,s5_293])
  · decide +kernel
  · exact allCons c5_7 (allCons c5_289 (allCons c5_290 (allCons c5_291 (allCons c5_292 (allCons c5_293 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_153 : search 6 s6_153 = false := by
  apply row (k := 4) (covered := [s5_7,s5_261,s5_142,s5_148,s5_267,s5_278,s5_282,s5_285,s5_294,s5_290,s5_295,s5_296,s5_297,s5_298,s5_299])
  · decide +kernel
  · exact allCons c5_7 (allCons c5_261 (allCons c5_142 (allCons c5_148 (allCons c5_267 (allCons c5_278 (allCons c5_282 (allCons c5_285 (allCons c5_294 (allCons c5_290 (allCons c5_295 (allCons c5_296 (allCons c5_297 (allCons c5_298 (allCons c5_299 (allNil 5)))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_154 : search 6 s6_154 = false := by
  apply row (k := 4) (covered := [s5_300,s5_209,s5_301,s5_302,s5_303,s5_304,s5_305])
  · decide +kernel
  · exact allCons c5_300 (allCons c5_209 (allCons c5_301 (allCons c5_302 (allCons c5_303 (allCons c5_304 (allCons c5_305 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_155 : search 6 s6_155 = false := by
  apply row (k := 4) (covered := [s5_287,s5_8,s5_306])
  · decide +kernel
  · exact allCons c5_287 (allCons c5_8 (allCons c5_306 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_156 : search 6 s6_156 = false := by
  apply row (k := 4) (covered := [s5_8,s5_307])
  · decide +kernel
  · exact allCons c5_8 (allCons c5_307 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_157 : search 6 s6_157 = false := by
  apply row (k := 4) (covered := [s5_8,s5_262,s5_149,s5_274,s5_279,s5_268,s5_286,s5_291,s5_308,s5_309])
  · decide +kernel
  · exact allCons c5_8 (allCons c5_262 (allCons c5_149 (allCons c5_274 (allCons c5_279 (allCons c5_268 (allCons c5_286 (allCons c5_291 (allCons c5_308 (allCons c5_309 (allNil 5))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_158 : search 6 s6_158 = false := by
  apply row (k := 4) (covered := [s5_289,s5_291,s5_310,s5_311])
  · decide +kernel
  · exact allCons c5_289 (allCons c5_291 (allCons c5_310 (allCons c5_311 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_159 : search 6 s6_159 = false := by
  apply row (k := 4) (covered := [s5_312,s5_176,s5_290,s5_308,s5_313,s5_314,s5_310])
  · decide +kernel
  · exact allCons c5_312 (allCons c5_176 (allCons c5_290 (allCons c5_308 (allCons c5_313 (allCons c5_314 (allCons c5_310 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_160 : search 6 s6_160 = false := by
  apply row (k := 4) (covered := [s5_295,s5_303,s5_315,s5_316])
  · decide +kernel
  · exact allCons c5_295 (allCons c5_303 (allCons c5_315 (allCons c5_316 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_161 : search 6 s6_161 = false := by
  apply row (k := 4) (covered := [s5_296,s5_304,s5_309,s5_315,s5_9,s5_316])
  · decide +kernel
  · exact allCons c5_296 (allCons c5_304 (allCons c5_309 (allCons c5_315 (allCons c5_9 (allCons c5_316 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_162 : search 6 s6_162 = false := by
  apply row (k := 4) (covered := [s5_297,s5_317,s5_9])
  · decide +kernel
  · exact allCons c5_297 (allCons c5_317 (allCons c5_9 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_163 : search 6 s6_163 = false := by
  apply row (k := 4) (covered := [s5_9,s5_263,s5_33,s5_143,s5_269,s5_275,s5_283,s5_280,s5_288,s5_292,s5_298,s5_306,s5_304,s5_311,s5_318])
  · decide +kernel
  · exact allCons c5_9 (allCons c5_263 (allCons c5_33 (allCons c5_143 (allCons c5_269 (allCons c5_275 (allCons c5_283 (allCons c5_280 (allCons c5_288 (allCons c5_292 (allCons c5_298 (allCons c5_306 (allCons c5_304 (allCons c5_311 (allCons c5_318 (allNil 5)))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_164 : search 6 s6_164 = false := by
  apply row (k := 4) (covered := [s5_307,s5_10])
  · decide +kernel
  · exact allCons c5_307 (allCons c5_10 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_165 : search 6 s6_165 = false := by
  apply row (k := 4) (covered := [s5_299,s5_317,s5_10])
  · decide +kernel
  · exact allCons c5_299 (allCons c5_317 (allCons c5_10 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_166 : search 6 s6_166 = false := by
  apply row (k := 4) (covered := [s5_10,s5_264,s5_34,s5_270,s5_276,s5_281,s5_284,s5_293,s5_305,s5_316])
  · decide +kernel
  · exact allCons c5_10 (allCons c5_264 (allCons c5_34 (allCons c5_270 (allCons c5_276 (allCons c5_281 (allCons c5_284 (allCons c5_293 (allCons c5_305 (allCons c5_316 (allNil 5))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_167 : search 6 s6_167 = false := by
  apply row (k := 4) (covered := [s5_240,s5_11,s5_319])
  · decide +kernel
  · exact allCons c5_240 (allCons c5_11 (allCons c5_319 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_168 : search 6 s6_168 = false := by
  apply row (k := 4) (covered := [s5_160,s5_197])
  · decide +kernel
  · exact allCons c5_160 (allCons c5_197 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_169 : search 6 s6_169 = false := by
  apply row (k := 4) (covered := [s5_241,s5_12,s5_319])
  · decide +kernel
  · exact allCons c5_241 (allCons c5_12 (allCons c5_319 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_170 : search 6 s6_170 = false := by
  apply row (k := 4) (covered := [s5_161,s5_198])
  · decide +kernel
  · exact allCons c5_161 (allCons c5_198 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_171 : search 6 s6_171 = false := by
  apply row (k := 4) (covered := [s5_320,s5_7,s5_11])
  · decide +kernel
  · exact allCons c5_320 (allCons c5_7 (allCons c5_11 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_172 : search 6 s6_172 = false := by
  apply row (k := 4) (covered := [s5_91,s5_8])
  · decide +kernel
  · exact allCons c5_91 (allCons c5_8 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_173 : search 6 s6_173 = false := by
  apply row (k := 4) (covered := [s5_320,s5_9,s5_12])
  · decide +kernel
  · exact allCons c5_320 (allCons c5_9 (allCons c5_12 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_174 : search 6 s6_174 = false := by
  apply row (k := 4) (covered := [s5_92,s5_10])
  · decide +kernel
  · exact allCons c5_92 (allCons c5_10 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_175 : search 6 s6_175 = false := by
  apply row (k := 4) (covered := [s5_11,s5_321])
  · decide +kernel
  · exact allCons c5_11 (allCons c5_321 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_176 : search 6 s6_176 = false := by
  apply row (k := 4) (covered := [s5_93,s5_11,s5_163,s5_322,s5_323])
  · decide +kernel
  · exact allCons c5_93 (allCons c5_11 (allCons c5_163 (allCons c5_322 (allCons c5_323 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_177 : search 6 s6_177 = false := by
  apply row (k := 4) (covered := [s5_11,s5_54,s5_151,s5_322,s5_202,s5_324,s5_325,s5_326,s5_240])
  · decide +kernel
  · exact allCons c5_11 (allCons c5_54 (allCons c5_151 (allCons c5_322 (allCons c5_202 (allCons c5_324 (allCons c5_325 (allCons c5_326 (allCons c5_240 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_178 : search 6 s6_178 = false := by
  apply row (k := 4) (covered := [s5_327,s5_94,s5_328,s5_329,s5_205,s5_330])
  · decide +kernel
  · exact allCons c5_327 (allCons c5_94 (allCons c5_328 (allCons c5_329 (allCons c5_205 (allCons c5_330 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_179 : search 6 s6_179 = false := by
  apply row (k := 4) (covered := [s5_66,s5_331])
  · decide +kernel
  · exact allCons c5_66 (allCons c5_331 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_180 : search 6 s6_180 = false := by
  apply row (k := 4) (covered := [s5_332,s5_96,s5_322,s5_333,s5_334,s5_174])
  · decide +kernel
  · exact allCons c5_332 (allCons c5_96 (allCons c5_322 (allCons c5_333 (allCons c5_334 (allCons c5_174 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_181 : search 6 s6_181 = false := by
  apply row (k := 4) (covered := [s5_97,s5_324,s5_330,s5_213,s5_12])
  · decide +kernel
  · exact allCons c5_97 (allCons c5_324 (allCons c5_330 (allCons c5_213 (allCons c5_12 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_182 : search 6 s6_182 = false := by
  apply row (k := 4) (covered := [s5_325,s5_12])
  · decide +kernel
  · exact allCons c5_325 (allCons c5_12 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_183 : search 6 s6_183 = false := by
  apply row (k := 4) (covered := [s5_12,s5_36,s5_55,s5_321,s5_323,s5_326,s5_330,s5_175,s5_241])
  · decide +kernel
  · exact allCons c5_12 (allCons c5_36 (allCons c5_55 (allCons c5_321 (allCons c5_323 (allCons c5_326 (allCons c5_330 (allCons c5_175 (allCons c5_241 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_184 : search 6 s6_184 = false := by
  apply row (k := 4) (covered := [s5_67,s5_331])
  · decide +kernel
  · exact allCons c5_67 (allCons c5_331 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_185 : search 6 s6_185 = false := by
  apply row (k := 4) (covered := [s5_214,s5_7,s5_335])
  · decide +kernel
  · exact allCons c5_214 (allCons c5_7 (allCons c5_335 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_186 : search 6 s6_186 = false := by
  apply row (k := 4) (covered := [s5_215,s5_287,s5_336])
  · decide +kernel
  · exact allCons c5_215 (allCons c5_287 (allCons c5_336 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_187 : search 6 s6_187 = false := by
  apply row (k := 4) (covered := [s5_288,s5_321,s5_13,s5_335,s5_336])
  · decide +kernel
  · exact allCons c5_288 (allCons c5_321 (allCons c5_13 (allCons c5_335 (allCons c5_336 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_188 : search 6 s6_188 = false := by
  apply row (k := 4) (covered := [s5_100,s5_289,s5_163,s5_337,s5_338])
  · decide +kernel
  · exact allCons c5_100 (allCons c5_289 (allCons c5_163 (allCons c5_337 (allCons c5_338 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_189 : search 6 s6_189 = false := by
  apply row (k := 4) (covered := [s5_339,s5_290,s5_322,s5_340,s5_341])
  · decide +kernel
  · exact allCons c5_339 (allCons c5_290 (allCons c5_322 (allCons c5_340 (allCons c5_341 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_190 : search 6 s6_190 = false := by
  apply row (k := 4) (covered := [s5_164,s5_291,s5_341,s5_342])
  · decide +kernel
  · exact allCons c5_164 (allCons c5_291 (allCons c5_341 (allCons c5_342 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_191 : search 6 s6_191 = false := by
  apply row (k := 4) (covered := [s5_165,s5_292,s5_323,s5_13,s5_337])
  · decide +kernel
  · exact allCons c5_165 (allCons c5_292 (allCons c5_323 (allCons c5_13 (allCons c5_337 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_192 : search 6 s6_192 = false := by
  apply row (k := 4) (covered := [s5_166,s5_338,s5_342])
  · decide +kernel
  · exact allCons c5_166 (allCons c5_338 (allCons c5_342 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_193 : search 6 s6_193 = false := by
  apply row (k := 4) (covered := [s5_167,s5_293])
  · decide +kernel
  · exact allCons c5_167 (allCons c5_293 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_194 : search 6 s6_194 = false := by
  apply row (k := 4) (covered := [s5_294,s5_341,s5_343])
  · decide +kernel
  · exact allCons c5_294 (allCons c5_341 (allCons c5_343 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_195 : search 6 s6_195 = false := by
  apply row (k := 4) (covered := [s5_200,s5_295,s5_202,s5_344])
  · decide +kernel
  · exact allCons c5_200 (allCons c5_295 (allCons c5_202 (allCons c5_344 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_196 : search 6 s6_196 = false := by
  apply row (k := 4) (covered := [s5_201,s5_296,s5_324,s5_344,s5_13])
  · decide +kernel
  · exact allCons c5_201 (allCons c5_296 (allCons c5_324 (allCons c5_344 (allCons c5_13 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_197 : search 6 s6_197 = false := by
  apply row (k := 4) (covered := [s5_297,s5_325,s5_345,s5_346,s5_13])
  · decide +kernel
  · exact allCons c5_297 (allCons c5_325 (allCons c5_345 (allCons c5_346 (allCons c5_13 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_198 : search 6 s6_198 = false := by
  apply row (k := 4) (covered := [s5_13,s5_57,s5_144,s5_242,s5_253,s5_298,s5_319,s5_320,s5_326,s5_343,s5_347])
  · decide +kernel
  · exact allCons c5_13 (allCons c5_57 (allCons c5_144 (allCons c5_242 (allCons c5_253 (allCons c5_298 (allCons c5_319 (allCons c5_320 (allCons c5_326 (allCons c5_343 (allCons c5_347 (allNil 5)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_199 : search 6 s6_199 = false := by
  apply row (k := 4) (covered := [s5_7,s5_345,s5_348])
  · decide +kernel
  · exact allCons c5_7 (allCons c5_345 (allCons c5_348 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_200 : search 6 s6_200 = false := by
  apply row (k := 4) (covered := [s5_299,s5_346,s5_348])
  · decide +kernel
  · exact allCons c5_299 (allCons c5_346 (allCons c5_348 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_201 : search 6 s6_201 = false := by
  apply row (k := 4) (covered := [s5_177,s5_203,s5_300,s5_327,s5_102,s5_349,s5_350,s5_351,s5_352])
  · decide +kernel
  · exact allCons c5_177 (allCons c5_203 (allCons c5_300 (allCons c5_327 (allCons c5_102 (allCons c5_349 (allCons c5_350 (allCons c5_351 (allCons c5_352 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_202 : search 6 s6_202 = false := by
  apply row (k := 4) (covered := [s5_101,s5_301,s5_328,s5_353,s5_354,s5_355,s5_356])
  · decide +kernel
  · exact allCons c5_101 (allCons c5_301 (allCons c5_328 (allCons c5_353 (allCons c5_354 (allCons c5_355 (allCons c5_356 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_203 : search 6 s6_203 = false := by
  apply row (k := 4) (covered := [s5_102,s5_178,s5_204,s5_329,s5_357,s5_358])
  · decide +kernel
  · exact allCons c5_102 (allCons c5_178 (allCons c5_204 (allCons c5_329 (allCons c5_357 (allCons c5_358 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_204 : search 6 s6_204 = false := by
  apply row (k := 4) (covered := [s5_103,s5_179,s5_302,s5_359])
  · decide +kernel
  · exact allCons c5_103 (allCons c5_179 (allCons c5_302 (allCons c5_359 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_205 : search 6 s6_205 = false := by
  apply row (k := 4) (covered := [s5_349,s5_104,s5_180,s5_303,s5_205,s5_353,s5_357,s5_360,s5_361])
  · decide +kernel
  · exact allCons c5_349 (allCons c5_104 (allCons c5_180 (allCons c5_303 (allCons c5_205 (allCons c5_353 (allCons c5_357 (allCons c5_360 (allCons c5_361 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_206 : search 6 s6_206 = false := by
  apply row (k := 4) (covered := [s5_350,s5_304,s5_330,s5_354,s5_361])
  · decide +kernel
  · exact allCons c5_350 (allCons c5_304 (allCons c5_330 (allCons c5_354 (allCons c5_361 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_207 : search 6 s6_207 = false := by
  apply row (k := 4) (covered := [s5_351,s5_181,s5_355,s5_359,s5_360])
  · decide +kernel
  · exact allCons c5_351 (allCons c5_181 (allCons c5_355 (allCons c5_359 (allCons c5_360 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_208 : search 6 s6_208 = false := by
  apply row (k := 4) (covered := [s5_352,s5_206,s5_305,s5_356,s5_358,s5_361])
  · decide +kernel
  · exact allCons c5_352 (allCons c5_206 (allCons c5_305 (allCons c5_356 (allCons c5_358 (allCons c5_361 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_209 : search 6 s6_209 = false := by
  apply row (k := 4) (covered := [s5_216,s5_8,s5_362])
  · decide +kernel
  · exact allCons c5_216 (allCons c5_8 (allCons c5_362 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_210 : search 6 s6_210 = false := by
  apply row (k := 4) (covered := [s5_9,s5_335,s5_362])
  · decide +kernel
  · exact allCons c5_9 (allCons c5_335 (allCons c5_362 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_211 : search 6 s6_211 = false := by
  apply row (k := 4) (covered := [s5_217,s5_10,s5_14])
  · decide +kernel
  · exact allCons c5_217 (allCons c5_10 (allCons c5_14 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_212 : search 6 s6_212 = false := by
  apply row (k := 4) (covered := [s5_182,s5_218,s5_331])
  · decide +kernel
  · exact allCons c5_182 (allCons c5_218 (allCons c5_331 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_213 : search 6 s6_213 = false := by
  apply row (k := 4) (covered := [s5_219,s5_254,s5_14])
  · decide +kernel
  · exact allCons c5_219 (allCons c5_254 (allCons c5_14 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_214 : search 6 s6_214 = false := by
  apply row (k := 4) (covered := [s5_220,s5_363])
  · decide +kernel
  · exact allCons c5_220 (allCons c5_363 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_215 : search 6 s6_215 = false := by
  apply row (k := 4) (covered := [s5_364,s5_221,s5_365,s5_366,s5_363])
  · decide +kernel
  · exact allCons c5_364 (allCons c5_221 (allCons c5_365 (allCons c5_366 (allCons c5_363 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_216 : search 6 s6_216 = false := by
  apply row (k := 4) (covered := [s5_207,s5_367,s5_368])
  · decide +kernel
  · exact allCons c5_207 (allCons c5_367 (allCons c5_368 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_217 : search 6 s6_217 = false := by
  apply row (k := 4) (covered := [s5_208,s5_367,s5_368])
  · decide +kernel
  · exact allCons c5_208 (allCons c5_367 (allCons c5_368 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_218 : search 6 s6_218 = false := by
  apply row (k := 4) (covered := [s5_224,s5_14])
  · decide +kernel
  · exact allCons c5_224 (allCons c5_14 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_219 : search 6 s6_219 = false := by
  apply row (k := 4) (covered := [s5_225,s5_14])
  · decide +kernel
  · exact allCons c5_225 (allCons c5_14 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_220 : search 6 s6_220 = false := by
  apply row (k := 4) (covered := [s5_14,s5_39,s5_199,s5_210,s5_226,s5_254,s5_368])
  · decide +kernel
  · exact allCons c5_14 (allCons c5_39 (allCons c5_199 (allCons c5_210 (allCons c5_226 (allCons c5_254 (allCons c5_368 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_221 : search 6 s6_221 = false := by
  apply row (k := 4) (covered := [s5_306,s5_336,s5_362])
  · decide +kernel
  · exact allCons c5_306 (allCons c5_336 (allCons c5_362 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_222 : search 6 s6_222 = false := by
  apply row (k := 4) (covered := [s5_183,s5_15])
  · decide +kernel
  · exact allCons c5_183 (allCons c5_15 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_223 : search 6 s6_223 = false := by
  apply row (k := 4) (covered := [s5_184,s5_15])
  · decide +kernel
  · exact allCons c5_184 (allCons c5_15 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_224 : search 6 s6_224 = false := by
  apply row (k := 4) (covered := [s5_106,s5_307])
  · decide +kernel
  · exact allCons c5_106 (allCons c5_307 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_225 : search 6 s6_225 = false := by
  apply row (k := 4) (covered := [s5_369,s5_168,s5_308,s5_370,s5_371,s5_341])
  · decide +kernel
  · exact allCons c5_369 (allCons c5_168 (allCons c5_308 (allCons c5_370 (allCons c5_371 (allCons c5_341 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_226 : search 6 s6_226 = false := by
  apply row (k := 4) (covered := [s5_211,s5_309])
  · decide +kernel
  · exact allCons c5_211 (allCons c5_309 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_227 : search 6 s6_227 = false := by
  apply row (k := 4) (covered := [s5_185,s5_255,s5_15])
  · decide +kernel
  · exact allCons c5_185 (allCons c5_255 (allCons c5_15 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_228 : search 6 s6_228 = false := by
  apply row (k := 4) (covered := [s5_186,s5_8,s5_15])
  · decide +kernel
  · exact allCons c5_186 (allCons c5_8 (allCons c5_15 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_229 : search 6 s6_229 = false := by
  apply row (k := 4) (covered := [s5_15,s5_58,s5_162,s5_169,s5_187,s5_255,s5_342])
  · decide +kernel
  · exact allCons c5_15 (allCons c5_58 (allCons c5_162 (allCons c5_169 (allCons c5_187 (allCons c5_255 (allCons c5_342 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_230 : search 6 s6_230 = false := by
  apply row (k := 4) (covered := [s5_372,s5_107,s5_227,s5_310,s5_174,s5_363,s5_341,s5_373,s5_374])
  · decide +kernel
  · exact allCons c5_372 (allCons c5_107 (allCons c5_227 (allCons c5_310 (allCons c5_174 (allCons c5_363 (allCons c5_341 (allCons c5_373 (allCons c5_374 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_231 : search 6 s6_231 = false := by
  apply row (k := 4) (covered := [s5_170,s5_311,s5_175,s5_337])
  · decide +kernel
  · exact allCons c5_170 (allCons c5_311 (allCons c5_175 (allCons c5_337 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_232 : search 6 s6_232 = false := by
  apply row (k := 4) (covered := [s5_171,s5_338,s5_342])
  · decide +kernel
  · exact allCons c5_171 (allCons c5_338 (allCons c5_342 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_233 : search 6 s6_233 = false := by
  apply row (k := 4) (covered := [s5_172,s5_228,s5_312,s5_332,s5_339,s5_364,s5_369,s5_109,s5_372])
  · decide +kernel
  · exact allCons c5_172 (allCons c5_228 (allCons c5_312 (allCons c5_332 (allCons c5_339 (allCons c5_364 (allCons c5_369 (allCons c5_109 (allCons c5_372 (allNil 5)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_234 : search 6 s6_234 = false := by
  apply row (k := 4) (covered := [s5_108,s5_313,s5_333,s5_340,s5_365,s5_370,s5_373])
  · decide +kernel
  · exact allCons c5_108 (allCons c5_313 (allCons c5_333 (allCons c5_340 (allCons c5_365 (allCons c5_370 (allCons c5_373 (allNil 5)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_235 : search 6 s6_235 = false := by
  apply row (k := 4) (covered := [s5_109,s5_173,s5_229,s5_334,s5_371,s5_374])
  · decide +kernel
  · exact allCons c5_109 (allCons c5_173 (allCons c5_229 (allCons c5_334 (allCons c5_371 (allCons c5_374 (allNil 5))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_236 : search 6 s6_236 = false := by
  apply row (k := 4) (covered := [s5_110,s5_230,s5_314,s5_366])
  · decide +kernel
  · exact allCons c5_110 (allCons c5_230 (allCons c5_314 (allCons c5_366 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_237 : search 6 s6_237 = false := by
  apply row (k := 4) (covered := [s5_111,s5_315,s5_213,s5_344,s5_367])
  · decide +kernel
  · exact allCons c5_111 (allCons c5_315 (allCons c5_213 (allCons c5_344 (allCons c5_367 (allNil 5)))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_238 : search 6 s6_238 = false := by
  apply row (k := 4) (covered := [s5_189,s5_360])
  · decide +kernel
  · exact allCons c5_189 (allCons c5_360 (allNil 5))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_239 : search 6 s6_239 = false := by
  apply row (k := 4) (covered := [s5_212,s5_316,s5_361,s5_368])
  · decide +kernel
  · exact allCons c5_212 (allCons c5_316 (allCons c5_361 (allCons c5_368 (allNil 5))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_240 : search 6 s6_240 = false := by
  apply row (k := 4) (covered := [s5_190,s5_9,s5_345])
  · decide +kernel
  · exact allCons c5_190 (allCons c5_9 (allCons c5_345 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_241 : search 6 s6_241 = false := by
  apply row (k := 4) (covered := [s5_191,s5_317,s5_346])
  · decide +kernel
  · exact allCons c5_191 (allCons c5_317 (allCons c5_346 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_242 : search 6 s6_242 = false := by
  apply row (k := 4) (covered := [s5_318,s5_347,s5_361])
  · decide +kernel
  · exact allCons c5_318 (allCons c5_347 (allCons c5_361 (allNil 5)))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c6_243 : search 6 s6_243 = false := by
  apply row (k := 4) (covered := [s5_192,s5_10,s5_348])
  · decide +kernel
  · exact allCons c5_192 (allCons c5_10 (allCons c5_348 (allNil 5)))
private def s7_0 : Finset W := {15,240,3840,4369,8738,17476,34952,61440}
private def s7_1 : Finset W := {15,240,3855,4369,8738,17476,34952,61440}
private def s7_2 : Finset W := {15,240,3840,4369,8738,17487,34952,61440}
private def s7_3 : Finset W := {240,3840,4369,8738,17476,17487,34952,61440}
private def s7_4 : Finset W := {240,3840,4369,8738,17487,34952,61440}
private def s7_5 : Finset W := {8,15,240,3840,4369,8738,17476,61440}
private def s7_6 : Finset W := {15,240,3840,4369,8738,17476,34952,61455}
private def s7_7 : Finset W := {15,240,3840,4593,8738,17476,34952,61440}
private def s7_8 : Finset W := {15,3840,4369,4593,8738,17476,34952,61440}
private def s7_9 : Finset W := {15,3840,4593,8738,17476,34952,61440}
private def s7_10 : Finset W := {15,240,3840,4369,8946,17476,34952,61440}
private def s7_11 : Finset W := {15,3840,4369,8738,8946,17476,34952,61440}
private def s7_12 : Finset W := {15,3840,4369,8946,17476,34952,61440}
private def s7_13 : Finset W := {15,64,240,3840,4369,8738,34952,61440}
private def s7_14 : Finset W := {15,64,3840,4369,8738,17476,34952,61440}
private def s7_15 : Finset W := {15,64,3840,4369,8738,34952,61440}
private def s7_16 : Finset W := {15,240,3840,4369,8738,17476,35064,61440}
private def s7_17 : Finset W := {15,3840,4369,8738,17476,34952,35064,61440}
private def s7_18 : Finset W := {15,3840,4369,8738,17476,35064,61440}
private def s7_19 : Finset W := {15,240,3840,7953,8738,17476,34952,61440}
private def s7_20 : Finset W := {15,240,4369,7953,8738,17476,34952,61440}
private def s7_21 : Finset W := {15,240,7953,8738,17476,34952,61440}
private def s7_22 : Finset W := {15,240,512,4369,8738,17476,34952,61440}
private def s7_23 : Finset W := {15,240,3840,4369,8738,20292,34952,61440}
private def s7_24 : Finset W := {15,240,4369,8738,17476,20292,34952,61440}
private def s7_25 : Finset W := {15,240,4369,8738,20292,34952,61440}
private def s7_26 : Finset W := {15,240,3840,4369,8738,17476,36744,61440}
private def s7_27 : Finset W := {15,240,4369,8738,17476,34952,36744,61440}
private def s7_28 : Finset W := {15,240,4369,8738,17476,36744,61440}
private def s7_29 : Finset W := {15,240,3840,4369,8738,17476,39321,61440}
private def s7_30 : Finset W := {15,240,3840,4096,4369,8738,17476,34952}
private def s7_31 : Finset W := {15,240,3840,4369,8738,17476,43690,61440}
private def s7_32 : Finset W := {15,240,3840,4369,8738,17476,34952,61986}
private def s7_33 : Finset W := {15,240,3840,4369,17476,34952,61440,61986}
private def s7_34 : Finset W := {15,240,3840,4369,17476,34952,61986}
private def s7_35 : Finset W := {15,240,3840,4369,8738,17476,34952,62532}
private def s7_36 : Finset W := {15,240,3840,4369,8738,34952,61440,62532}
private def s7_37 : Finset W := {15,240,3840,4369,8738,34952,62532}
private def s7_38 : Finset W := {15,240,3840,4369,8738,17476,34952,63624}
private def s7_39 : Finset W := {15,240,3840,4369,8738,17476,61440,63624}
private def s7_40 : Finset W := {15,240,3840,4369,8738,17476,63624}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_0 : search 7 s7_0 = false := by
  apply row (k := 5) (covered := [s6_0,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s6_7,s6_8,s6_9,s6_10])
  · decide +kernel
  · exact allCons c6_0 (allCons c6_1 (allCons c6_2 (allCons c6_3 (allCons c6_4 (allCons c6_5 (allCons c6_6 (allCons c6_7 (allCons c6_8 (allCons c6_9 (allCons c6_10 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_1 : search 7 s7_1 = false := by
  apply row (k := 5) (covered := [s6_11,s6_12,s6_13,s6_14,s6_15,s6_16,s6_17,s6_18,s6_19,s6_20,s6_21])
  · decide +kernel
  · exact allCons c6_11 (allCons c6_12 (allCons c6_13 (allCons c6_14 (allCons c6_15 (allCons c6_16 (allCons c6_17 (allCons c6_18 (allCons c6_19 (allCons c6_20 (allCons c6_21 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_2 : search 7 s7_2 = false := by
  apply row (k := 5) (covered := [s6_11,s6_0,s6_22,s6_23,s6_24,s6_25,s6_3,s6_26,s6_27,s6_18,s6_28,s6_29,s6_30,s6_31])
  · decide +kernel
  · exact allCons c6_11 (allCons c6_0 (allCons c6_22 (allCons c6_23 (allCons c6_24 (allCons c6_25 (allCons c6_3 (allCons c6_26 (allCons c6_27 (allCons c6_18 (allCons c6_28 (allCons c6_29 (allCons c6_30 (allCons c6_31 (allNil 6))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_3 : search 7 s7_3 = false := by
  apply row (k := 5) (covered := [s6_32,s6_33,s6_34,s6_35,s6_36,s6_0,s6_37])
  · decide +kernel
  · exact allCons c6_32 (allCons c6_33 (allCons c6_34 (allCons c6_35 (allCons c6_36 (allCons c6_0 (allCons c6_37 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_4 : search 7 s7_4 = false := by
  apply row (k := 5) (covered := [s6_0,s6_38,s6_39,s6_40,s6_41,s6_42,s6_43,s6_34,s6_44,s6_45,s6_46,s6_47,s6_48,s6_49,s6_50,s6_51,s6_52,s6_53,s6_54,s6_22,s6_55,s6_56])
  · decide +kernel
  · exact allCons c6_0 (allCons c6_38 (allCons c6_39 (allCons c6_40 (allCons c6_41 (allCons c6_42 (allCons c6_43 (allCons c6_34 (allCons c6_44 (allCons c6_45 (allCons c6_46 (allCons c6_47 (allCons c6_48 (allCons c6_49 (allCons c6_50 (allCons c6_51 (allCons c6_52 (allCons c6_53 (allCons c6_54 (allCons c6_22 (allCons c6_55 (allCons c6_56 (allNil 6))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_5 : search 7 s7_5 = false := by
  apply row (k := 5) (covered := [s6_57,s6_58,s6_59,s6_60,s6_61,s6_22,s6_62,s6_63,s6_64,s6_65,s6_66,s6_67,s6_68])
  · decide +kernel
  · exact allCons c6_57 (allCons c6_58 (allCons c6_59 (allCons c6_60 (allCons c6_61 (allCons c6_22 (allCons c6_62 (allCons c6_63 (allCons c6_64 (allCons c6_65 (allCons c6_66 (allCons c6_67 (allCons c6_68 (allNil 6)))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_6 : search 7 s7_6 = false := by
  apply row (k := 5) (covered := [s6_12,s6_23,s6_69,s6_70,s6_71,s6_72,s6_73,s6_74,s6_75,s6_76,s6_30])
  · decide +kernel
  · exact allCons c6_12 (allCons c6_23 (allCons c6_69 (allCons c6_70 (allCons c6_71 (allCons c6_72 (allCons c6_73 (allCons c6_74 (allCons c6_75 (allCons c6_76 (allCons c6_30 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_7 : search 7 s7_7 = false := by
  apply row (k := 5) (covered := [s6_38,s6_1,s6_77,s6_78,s6_79,s6_80,s6_81,s6_82])
  · decide +kernel
  · exact allCons c6_38 (allCons c6_1 (allCons c6_77 (allCons c6_78 (allCons c6_79 (allCons c6_80 (allCons c6_81 (allCons c6_82 (allNil 6))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_8 : search 7 s7_8 = false := by
  apply row (k := 5) (covered := [s6_39,s6_83,s6_84,s6_1,s6_85,s6_86,s6_3,s6_87,s6_88,s6_89,s6_90])
  · decide +kernel
  · exact allCons c6_39 (allCons c6_83 (allCons c6_84 (allCons c6_1 (allCons c6_85 (allCons c6_86 (allCons c6_3 (allCons c6_87 (allCons c6_88 (allCons c6_89 (allCons c6_90 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_9 : search 7 s7_9 = false := by
  apply row (k := 5) (covered := [s6_1,s6_13,s6_24,s6_32,s6_40,s6_62,s6_69,s6_91,s6_92,s6_93,s6_94,s6_95,s6_78,s6_96,s6_86,s6_97,s6_98,s6_99,s6_100,s6_101,s6_102])
  · decide +kernel
  · exact allCons c6_1 (allCons c6_13 (allCons c6_24 (allCons c6_32 (allCons c6_40 (allCons c6_62 (allCons c6_69 (allCons c6_91 (allCons c6_92 (allCons c6_93 (allCons c6_94 (allCons c6_95 (allCons c6_78 (allCons c6_96 (allCons c6_86 (allCons c6_97 (allCons c6_98 (allCons c6_99 (allCons c6_100 (allCons c6_101 (allCons c6_102 (allNil 6)))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_10 : search 7 s7_10 = false := by
  apply row (k := 5) (covered := [s6_41,s6_77,s6_2,s6_103,s6_104,s6_105,s6_106,s6_107])
  · decide +kernel
  · exact allCons c6_41 (allCons c6_77 (allCons c6_2 (allCons c6_103 (allCons c6_104 (allCons c6_105 (allCons c6_106 (allCons c6_107 (allNil 6))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_11 : search 7 s7_11 = false := by
  apply row (k := 5) (covered := [s6_42,s6_108,s6_109,s6_110,s6_111,s6_2,s6_112,s6_113,s6_3,s6_114,s6_115])
  · decide +kernel
  · exact allCons c6_42 (allCons c6_108 (allCons c6_109 (allCons c6_110 (allCons c6_111 (allCons c6_2 (allCons c6_112 (allCons c6_113 (allCons c6_3 (allCons c6_114 (allCons c6_115 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_12 : search 7 s7_12 = false := by
  apply row (k := 5) (covered := [s6_2,s6_14,s6_25,s6_33,s6_43,s6_63,s6_70,s6_116,s6_109,s6_117,s6_118,s6_119,s6_120,s6_121,s6_122,s6_103,s6_123,s6_124,s6_125,s6_126,s6_127])
  · decide +kernel
  · exact allCons c6_2 (allCons c6_14 (allCons c6_25 (allCons c6_33 (allCons c6_43 (allCons c6_63 (allCons c6_70 (allCons c6_116 (allCons c6_109 (allCons c6_117 (allCons c6_118 (allCons c6_119 (allCons c6_120 (allCons c6_121 (allCons c6_122 (allCons c6_103 (allCons c6_123 (allCons c6_124 (allCons c6_125 (allCons c6_126 (allCons c6_127 (allNil 6)))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_13 : search 7 s7_13 = false := by
  apply row (k := 5) (covered := [s6_128,s6_3,s6_129,s6_130,s6_78,s6_103,s6_131,s6_132,s6_133,s6_134,s6_135])
  · decide +kernel
  · exact allCons c6_128 (allCons c6_3 (allCons c6_129 (allCons c6_130 (allCons c6_78 (allCons c6_103 (allCons c6_131 (allCons c6_132 (allCons c6_133 (allCons c6_134 (allCons c6_135 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_14 : search 7 s7_14 = false := by
  apply row (k := 5) (covered := [s6_34,s6_136,s6_137,s6_3,s6_138,s6_139,s6_140,s6_141,s6_142,s6_143,s6_144])
  · decide +kernel
  · exact allCons c6_34 (allCons c6_136 (allCons c6_137 (allCons c6_3 (allCons c6_138 (allCons c6_139 (allCons c6_140 (allCons c6_141 (allCons c6_142 (allCons c6_143 (allCons c6_144 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_15 : search 7 s7_15 = false := by
  apply row (k := 5) (covered := [s6_3,s6_145,s6_15,s6_64,s6_71,s6_146,s6_147,s6_148,s6_149,s6_150,s6_151,s6_152,s6_153,s6_154,s6_155,s6_156,s6_157,s6_158,s6_159,s6_160,s6_161,s6_162,s6_163,s6_164,s6_165,s6_166])
  · decide +kernel
  · exact allCons c6_3 (allCons c6_145 (allCons c6_15 (allCons c6_64 (allCons c6_71 (allCons c6_146 (allCons c6_147 (allCons c6_148 (allCons c6_149 (allCons c6_150 (allCons c6_151 (allCons c6_152 (allCons c6_153 (allCons c6_154 (allCons c6_155 (allCons c6_156 (allCons c6_157 (allCons c6_158 (allCons c6_159 (allCons c6_160 (allCons c6_161 (allCons c6_162 (allCons c6_163 (allCons c6_164 (allCons c6_165 (allCons c6_166 (allNil 6))))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_16 : search 7 s7_16 = false := by
  apply row (k := 5) (covered := [s6_44,s6_79,s6_104,s6_131,s6_4,s6_167,s6_168,s6_169,s6_170])
  · decide +kernel
  · exact allCons c6_44 (allCons c6_79 (allCons c6_104 (allCons c6_131 (allCons c6_4 (allCons c6_167 (allCons c6_168 (allCons c6_169 (allCons c6_170 (allNil 6)))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_17 : search 7 s7_17 = false := by
  apply row (k := 5) (covered := [s6_45,s6_171,s6_172,s6_173,s6_3,s6_4,s6_174])
  · decide +kernel
  · exact allCons c6_45 (allCons c6_171 (allCons c6_172 (allCons c6_173 (allCons c6_3 (allCons c6_4 (allCons c6_174 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_18 : search 7 s7_18 = false := by
  apply row (k := 5) (covered := [s6_4,s6_16,s6_26,s6_35,s6_46,s6_72,s6_175,s6_176,s6_177,s6_178,s6_179,s6_87,s6_180,s6_114,s6_181,s6_182,s6_183,s6_131,s6_184])
  · decide +kernel
  · exact allCons c6_4 (allCons c6_16 (allCons c6_26 (allCons c6_35 (allCons c6_46 (allCons c6_72 (allCons c6_175 (allCons c6_176 (allCons c6_177 (allCons c6_178 (allCons c6_179 (allCons c6_87 (allCons c6_180 (allCons c6_114 (allCons c6_181 (allCons c6_182 (allCons c6_183 (allCons c6_131 (allCons c6_184 (allNil 6)))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_19 : search 7 s7_19 = false := by
  apply row (k := 5) (covered := [s6_116,s6_151,s6_175,s6_5,s6_185,s6_186,s6_187])
  · decide +kernel
  · exact allCons c6_116 (allCons c6_151 (allCons c6_175 (allCons c6_5 (allCons c6_185 (allCons c6_186 (allCons c6_187 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_20 : search 7 s7_20 = false := by
  apply row (k := 5) (covered := [s6_47,s6_83,s6_152,s6_176,s6_5,s6_188,s6_189,s6_190,s6_191,s6_192,s6_193])
  · decide +kernel
  · exact allCons c6_47 (allCons c6_83 (allCons c6_152 (allCons c6_176 (allCons c6_5 (allCons c6_188 (allCons c6_189 (allCons c6_190 (allCons c6_191 (allCons c6_192 (allCons c6_193 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_21 : search 7 s7_21 = false := by
  apply row (k := 5) (covered := [s6_5,s6_27,s6_65,s6_73,s6_108,s6_132,s6_139,s6_153,s6_167,s6_171,s6_177,s6_194,s6_189,s6_195,s6_196,s6_197,s6_198,s6_199,s6_200])
  · decide +kernel
  · exact allCons c6_5 (allCons c6_27 (allCons c6_65 (allCons c6_73 (allCons c6_108 (allCons c6_132 (allCons c6_139 (allCons c6_153 (allCons c6_167 (allCons c6_171 (allCons c6_177 (allCons c6_194 (allCons c6_189 (allCons c6_195 (allCons c6_196 (allCons c6_197 (allCons c6_198 (allCons c6_199 (allCons c6_200 (allNil 6)))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_22 : search 7 s7_22 = false := by
  apply row (k := 5) (covered := [s6_201,s6_48,s6_91,s6_109,s6_154,s6_178,s6_202,s6_203,s6_204,s6_205,s6_206,s6_207,s6_208])
  · decide +kernel
  · exact allCons c6_201 (allCons c6_48 (allCons c6_91 (allCons c6_109 (allCons c6_154 (allCons c6_178 (allCons c6_202 (allCons c6_203 (allCons c6_204 (allCons c6_205 (allCons c6_206 (allCons c6_207 (allCons c6_208 (allNil 6)))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_23 : search 7 s7_23 = false := by
  apply row (k := 5) (covered := [s6_117,s6_3,s6_185,s6_6,s6_209,s6_210,s6_211])
  · decide +kernel
  · exact allCons c6_117 (allCons c6_3 (allCons c6_185 (allCons c6_6 (allCons c6_209 (allCons c6_210 (allCons c6_211 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_24 : search 7 s7_24 = false := by
  apply row (k := 5) (covered := [s6_36,s6_92,s6_118,s6_140,s6_179,s6_6,s6_212,s6_213])
  · decide +kernel
  · exact allCons c6_36 (allCons c6_92 (allCons c6_118 (allCons c6_140 (allCons c6_179 (allCons c6_6 (allCons c6_212 (allCons c6_213 (allNil 6))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_25 : search 7 s7_25 = false := by
  apply row (k := 5) (covered := [s6_6,s6_18,s6_66,s6_74,s6_80,s6_105,s6_110,s6_119,s6_140,s6_168,s6_214,s6_215,s6_216,s6_217,s6_218,s6_219,s6_220])
  · decide +kernel
  · exact allCons c6_6 (allCons c6_18 (allCons c6_66 (allCons c6_74 (allCons c6_80 (allCons c6_105 (allCons c6_110 (allCons c6_119 (allCons c6_140 (allCons c6_168 (allCons c6_214 (allCons c6_215 (allCons c6_216 (allCons c6_217 (allCons c6_218 (allCons c6_219 (allCons c6_220 (allNil 6)))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_26 : search 7 s7_26 = false := by
  apply row (k := 5) (covered := [s6_93,s6_120,s6_155,s6_186,s6_209,s6_7,s6_221,s6_222])
  · decide +kernel
  · exact allCons c6_93 (allCons c6_120 (allCons c6_155 (allCons c6_186 (allCons c6_209 (allCons c6_7 (allCons c6_221 (allCons c6_222 (allNil 6))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_27 : search 7 s7_27 = false := by
  apply row (k := 5) (covered := [s6_50,s6_94,s6_156,s6_172,s6_223,s6_7,s6_224])
  · decide +kernel
  · exact allCons c6_50 (allCons c6_94 (allCons c6_156 (allCons c6_172 (allCons c6_223 (allCons c6_7 (allCons c6_224 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_28 : search 7 s7_28 = false := by
  apply row (k := 5) (covered := [s6_7,s6_28,s6_75,s6_81,s6_84,s6_95,s6_111,s6_133,s6_141,s6_157,s6_190,s6_225,s6_226,s6_227,s6_228,s6_229])
  · decide +kernel
  · exact allCons c6_7 (allCons c6_28 (allCons c6_75 (allCons c6_81 (allCons c6_84 (allCons c6_95 (allCons c6_111 (allCons c6_133 (allCons c6_141 (allCons c6_157 (allCons c6_190 (allCons c6_225 (allCons c6_226 (allCons c6_227 (allCons c6_228 (allCons c6_229 (allNil 6))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_29 : search 7 s7_29 = false := by
  apply row (k := 5) (covered := [s6_51,s6_85,s6_121,s6_158,s6_87,s6_188,s6_214,s6_190,s6_230,s6_231,s6_232])
  · decide +kernel
  · exact allCons c6_51 (allCons c6_85 (allCons c6_121 (allCons c6_158 (allCons c6_87 (allCons c6_188 (allCons c6_214 (allCons c6_190 (allCons c6_230 (allCons c6_231 (allCons c6_232 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_30 : search 7 s7_30 = false := by
  apply row (k := 5) (covered := [s6_233,s6_52,s6_86,s6_122,s6_159,s6_180,s6_189,s6_215,s6_225,s6_234,s6_235,s6_236,s6_230])
  · decide +kernel
  · exact allCons c6_233 (allCons c6_52 (allCons c6_86 (allCons c6_122 (allCons c6_159 (allCons c6_180 (allCons c6_189 (allCons c6_215 (allCons c6_225 (allCons c6_234 (allCons c6_235 (allCons c6_236 (allCons c6_230 (allNil 6)))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_31 : search 7 s7_31 = false := by
  apply row (k := 5) (covered := [s6_53,s6_97,s6_112,s6_160,s6_114,s6_195,s6_205,s6_216,s6_237,s6_238,s6_239])
  · decide +kernel
  · exact allCons c6_53 (allCons c6_97 (allCons c6_112 (allCons c6_160 (allCons c6_114 (allCons c6_195 (allCons c6_205 (allCons c6_216 (allCons c6_237 (allCons c6_238 (allCons c6_239 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_32 : search 7 s7_32 = false := by
  apply row (k := 5) (covered := [s6_54,s6_113,s6_161,s6_181,s6_196,s6_206,s6_217,s6_226,s6_237,s6_8,s6_239])
  · decide +kernel
  · exact allCons c6_54 (allCons c6_113 (allCons c6_161 (allCons c6_181 (allCons c6_196 (allCons c6_206 (allCons c6_217 (allCons c6_226 (allCons c6_237 (allCons c6_8 (allCons c6_239 (allNil 6)))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_33 : search 7 s7_33 = false := by
  apply row (k := 5) (covered := [s6_98,s6_162,s6_182,s6_197,s6_240,s6_241,s6_8])
  · decide +kernel
  · exact allCons c6_98 (allCons c6_162 (allCons c6_182 (allCons c6_197 (allCons c6_240 (allCons c6_241 (allCons c6_8 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_34 : search 7 s7_34 = false := by
  apply row (k := 5) (covered := [s6_8,s6_19,s6_29,s6_67,s6_88,s6_134,s6_142,s6_163,s6_169,s6_173,s6_183,s6_187,s6_191,s6_198,s6_210,s6_221,s6_206,s6_231,s6_242])
  · decide +kernel
  · exact allCons c6_8 (allCons c6_19 (allCons c6_29 (allCons c6_67 (allCons c6_88 (allCons c6_134 (allCons c6_142 (allCons c6_163 (allCons c6_169 (allCons c6_173 (allCons c6_183 (allCons c6_187 (allCons c6_191 (allCons c6_198 (allCons c6_210 (allCons c6_221 (allCons c6_206 (allCons c6_231 (allCons c6_242 (allNil 6)))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_35 : search 7 s7_35 = false := by
  apply row (k := 5) (covered := [s6_37,s6_99,s6_124,s6_143,s6_184,s6_212,s6_227,s6_9])
  · decide +kernel
  · exact allCons c6_37 (allCons c6_99 (allCons c6_124 (allCons c6_143 (allCons c6_184 (allCons c6_212 (allCons c6_227 (allCons c6_9 (allNil 6))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_36 : search 7 s7_36 = false := by
  apply row (k := 5) (covered := [s6_100,s6_3,s6_199,s6_228,s6_240,s6_243,s6_9])
  · decide +kernel
  · exact allCons c6_100 (allCons c6_3 (allCons c6_199 (allCons c6_228 (allCons c6_240 (allCons c6_243 (allCons c6_9 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_37 : search 7 s7_37 = false := by
  apply row (k := 5) (covered := [s6_9,s6_20,s6_68,s6_30,s6_82,s6_89,s6_101,s6_106,s6_170,s6_143,s6_192,s6_207,s6_222,s6_223,s6_229,s6_232,s6_238])
  · decide +kernel
  · exact allCons c6_9 (allCons c6_20 (allCons c6_68 (allCons c6_30 (allCons c6_82 (allCons c6_89 (allCons c6_101 (allCons c6_106 (allCons c6_170 (allCons c6_143 (allCons c6_192 (allCons c6_207 (allCons c6_222 (allCons c6_223 (allCons c6_229 (allCons c6_232 (allCons c6_238 (allNil 6)))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_38 : search 7 s7_38 = false := by
  apply row (k := 5) (covered := [s6_56,s6_125,s6_164,s6_174,s6_218,s6_224,s6_10])
  · decide +kernel
  · exact allCons c6_56 (allCons c6_125 (allCons c6_164 (allCons c6_174 (allCons c6_218 (allCons c6_224 (allCons c6_10 (allNil 6)))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_39 : search 7 s7_39 = false := by
  apply row (k := 5) (covered := [s6_102,s6_126,s6_165,s6_200,s6_219,s6_241,s6_243,s6_10])
  · decide +kernel
  · exact allCons c6_102 (allCons c6_126 (allCons c6_165 (allCons c6_200 (allCons c6_219 (allCons c6_241 (allCons c6_243 (allCons c6_10 (allNil 6))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c7_40 : search 7 s7_40 = false := by
  apply row (k := 5) (covered := [s6_10,s6_21,s6_31,s6_90,s6_107,s6_115,s6_127,s6_135,s6_144,s6_166,s6_193,s6_208,s6_211,s6_213,s6_220,s6_239])
  · decide +kernel
  · exact allCons c6_10 (allCons c6_21 (allCons c6_31 (allCons c6_90 (allCons c6_107 (allCons c6_115 (allCons c6_127 (allCons c6_135 (allCons c6_144 (allCons c6_166 (allCons c6_193 (allCons c6_208 (allCons c6_211 (allCons c6_213 (allCons c6_220 (allCons c6_239 (allNil 6))))))))))))))))
private def s8_0 : Finset W := {15,240,3840,4369,8738,17476,34952,61440}
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem c8_0 : search 8 s8_0 = false := by
  apply row (k := 6) (covered := [s7_0,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s7_7,s7_8,s7_9,s7_10,s7_11,s7_12,s7_13,s7_14,s7_15,s7_16,s7_17,s7_18,s7_19,s7_20,s7_21,s7_22,s7_23,s7_24,s7_25,s7_26,s7_27,s7_28,s7_29,s7_30,s7_31,s7_32,s7_33,s7_34,s7_35,s7_36,s7_37,s7_38,s7_39,s7_40])
  · decide +kernel
  · exact allCons c7_0 (allCons c7_1 (allCons c7_2 (allCons c7_3 (allCons c7_4 (allCons c7_5 (allCons c7_6 (allCons c7_7 (allCons c7_8 (allCons c7_9 (allCons c7_10 (allCons c7_11 (allCons c7_12 (allCons c7_13 (allCons c7_14 (allCons c7_15 (allCons c7_16 (allCons c7_17 (allCons c7_18 (allCons c7_19 (allCons c7_20 (allCons c7_21 (allCons c7_22 (allCons c7_23 (allCons c7_24 (allCons c7_25 (allCons c7_26 (allCons c7_27 (allCons c7_28 (allCons c7_29 (allCons c7_30 (allCons c7_31 (allCons c7_32 (allCons c7_33 (allCons c7_34 (allCons c7_35 (allCons c7_36 (allCons c7_37 (allCons c7_38 (allCons c7_39 (allCons c7_40 (allNil 7)))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem raw7 : search 7 raw = false := by
  have he : raw = s7_0 := by decide +kernel
  rw [he]; exact c7_0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem raw8 : search 8 raw = false := by
  have he : raw = s8_0 := by decide +kernel
  rw [he]; exact c8_0
end PEqualNP.Outside.L_meta_5984

open PEqualNP.Outside.L_meta_5984 in
theorem PEqualNP.Outside.L_meta_5984 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4683 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4683 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨upper,?_⟩
  intro hr
  obtain ⟨k,hk,s,hs,hp⟩ := rep_to_plan hr
  exact noPlanOf raw7 raw8 k hk s hs hp
