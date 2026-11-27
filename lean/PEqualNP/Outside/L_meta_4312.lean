import PEqualNP.Defs
import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Fin

-- The finite proof of the base formula is adapted from arvindf232's L-meta-3210 in PR 7578.
-- This file adds the clause-extension argument for the conjunctive output case.
namespace PEqualNP.Outside.L_meta_4312

namespace Decode3210
open PEqualNP.Defs.LratEncoding
def yes : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
def no : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
def rows := yes ++ no
def truth (r : Nat) := yes.contains r
def lit (k j t : Nat) (b : Bool) := 2*(((k*15+j)*1049+t)+1) + if b then 0 else 1
def num (a : Nat → Bool) (k j t : Nat) := a (((k*15+j)*1049+t)+1)

structure Present (f : List (List Nat)) : Prop where
  opcode : ∀ j < 14, (List.range 3).map (fun k => lit 0 j k true) ∈ f
  input : ∀ e ∈ [1,2], ∀ j < 14, (List.range (10+j+1)).map (fun i => lit e j i true) ∈ f
  raw : ∀ e ∈ [1,2], ∀ j < 14, ∀ r ∈ rows, ∀ i < 10, [lit e j i false,lit (e+3) j r (r.testBit i)] ∈ f
  prev : ∀ e ∈ [1,2], ∀ j < 14, ∀ r ∈ rows, ∀ t < j,
    [lit e j (10+t) false,lit (e+3) j r false,lit 3 t r true] ∈ f ∧
    [lit e j (10+t) false,lit (e+3) j r true,lit 3 t r false] ∈ f
  zero : ∀ e ∈ [1,2], ∀ j < 14, ∀ r ∈ rows, [lit e j (10+j) false,lit (e+3) j r false] ∈ f
  gates : ∀ j < 14, ∀ r ∈ rows, ∀ c ∈ [
    [lit 0 j 0 false,lit 3 j r false,lit 4 j r true], [lit 0 j 0 false,lit 3 j r false,lit 5 j r true],
    [lit 0 j 0 false,lit 3 j r true,lit 4 j r false,lit 5 j r false],
    [lit 0 j 1 false,lit 3 j r true,lit 4 j r false], [lit 0 j 1 false,lit 3 j r true,lit 5 j r false],
    [lit 0 j 1 false,lit 3 j r false,lit 4 j r true,lit 5 j r true],
    [lit 0 j 2 false,lit 3 j r true]], c ∈ f
  output : (List.range 25).map (fun i => lit 6 0 i true) ∈ f
  outRaw : ∀ r ∈ rows, ∀ i < 10, r.testBit i ≠ truth r → [lit 6 0 i false] ∈ f
  outPrev : ∀ r ∈ rows, ∀ t < 14, [lit 6 0 (10+t) false,lit 3 t r (truth r)] ∈ f
  outZero : ∀ r ∈ rows, truth r = true → [lit 6 0 24 false] ∈ f
end Decode3210

namespace Decode3210
open PEqualNP.Defs.LratEncoding

private theorem addrPos (k j t : Nat) : P (ix 10 14 k j t) = lit k j t true := by
  simp [P,ix,wd,lit]
  omega

private theorem addrNeg (k j t : Nat) : Q (ix 10 14 k j t) = lit k j t false := by
  simp [Q,ix,wd,lit]
  omega

private theorem addrBit (k j t : Nat) (b : Bool) :
    L (ix 10 14 k j t) b = lit k j t b := by
  cases b
  · exact addrNeg ..
  · exact addrPos ..

private theorem containsBlocks (a b c d e f g h i j k l : List (List Nat)) :
    let z := a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i ++ j ++ k ++ l
    (∀ {x}, x ∈ a → x ∈ z) ∧ (∀ {x}, x ∈ b → x ∈ z) ∧
    (∀ {x}, x ∈ c → x ∈ z) ∧ (∀ {x}, x ∈ d → x ∈ z) ∧
    (∀ {x}, x ∈ e → x ∈ z) ∧ (∀ {x}, x ∈ f → x ∈ z) := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals intro x hx; simp only [List.mem_append]; tauto

theorem present_enc : Present (enc 10 14 truth rows) := by
  let F := enc 10 14 truth rows
  have included :
      (∀ {c}, c ∈ fOp 10 14 → c ∈ F) ∧
      (∀ {c}, c ∈ fSrcAlo 10 14 → c ∈ F) ∧
      (∀ {c}, c ∈ fSrcEq 10 14 rows → c ∈ F) ∧
      (∀ {c}, c ∈ fGate 10 14 rows → c ∈ F) ∧
      (∀ {c}, c ∈ fOutAlo 10 14 → c ∈ F) ∧
      (∀ {c}, c ∈ fOutEq 10 14 truth rows → c ∈ F) := by
    exact containsBlocks _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨opBlock,choiceBlock,srcBlock,gateBlock,outBlock,outEqBlock⟩ := included
  have source {e j r i : Nat} {c : List Nat} (he : e ∈ [1,2]) (hj : j < 14)
      (hr : r ∈ rows) (hi : i < 10+j+1) (hc : c ∈ srcEq 10 14 e j i r) : c ∈ F := by
    apply srcBlock
    unfold fSrcEq
    exact List.mem_flatMap.mpr ⟨e,he,List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,
      List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hc⟩⟩⟩⟩
  have lastSource {r i : Nat} {c : List Nat} (hr : r ∈ rows) (hi : i < 25)
      (hc : c ∈ outEq 10 14 truth i r) : c ∈ F := by
    apply outEqBlock
    unfold fOutEq
    exact List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hc⟩⟩
  constructor
  · intro j hj
    apply opBlock
    unfold fOp
    refine List.mem_map.mpr ⟨j,List.mem_range.mpr hj,?_⟩
    have aligned : [P (ix 10 14 0 j 0),P (ix 10 14 0 j 1),P (ix 10 14 0 j 2)] =
        (List.range 3).map (fun k => lit 0 j k true) := by
      simp only [addrPos]
      rfl
    exact aligned
  · intro e he j hj
    apply choiceBlock
    unfold fSrcAlo
    refine List.mem_flatMap.mpr ⟨e,he,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,?_⟩⟩
    simp only [addrPos]
  · intro e he j hj r hr i hi
    apply source (i := i) he hj hr (by omega)
    simp [srcEq,hi,addrNeg,addrBit]
  · intro e he j hj r hr t ht
    have above : ¬ 10+t < 10 := by omega
    have below : 10+t < 10+j := by omega
    constructor <;> apply source (i := 10+t) he hj hr (by omega) <;>
      simp [srcEq,above,below,addrNeg,addrPos]
  · intro e he j hj r hr
    apply source (i := 10+j) he hj hr (by omega)
    have above : ¬ 10+j < 10 := by omega
    simp [srcEq,above,addrNeg]
  · intro j hj r hr c hc
    apply gateBlock
    unfold fGate
    refine List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_flatMap.mpr ⟨r,hr,?_⟩⟩
    simpa only [gateCl,addrNeg,addrPos] using hc
  · apply outBlock
    simp [fOutAlo,addrPos]
  · intro r hr i hi mismatch
    apply lastSource (i := i) hr (by omega)
    simp [outEq,hi,mismatch,addrNeg]
  · intro r hr t ht
    apply lastSource (i := 10+t) hr (by omega)
    have above : ¬ 10+t < 10 := by omega
    have below : 10+t < 10+14 := by omega
    simp [outEq,above,below,addrNeg,addrBit]
  · intro r hr hit
    apply lastSource (i := 24) hr (by decide)
    simp [outEq,hit,addrNeg]
end Decode3210

namespace Decode3210
open PEqualNP.Defs.LratEncoding

private theorem litEval (a) (k j t) (b : Bool) :
    litVal a (lit k j t b) = if b then num a k j t else !(num a k j t) := by
  let u := ((k*15+j)*1049+t)+1
  unfold litVal
  cases b
  · change _ = !(a u)
    have form : lit k j t false = 2*u+1 := rfl
    have rem : (2*u+1)%2 = 1 := by omega
    have div : (2*u+1)/2 = u := by omega
    rw [form,rem,div]
    cases a u <;> rfl
  · change _ = a u
    have form : lit k j t true = 2*u+0 := rfl
    have rem : (2*u+0)%2 = 0 := by omega
    have div : (2*u+0)/2 = u := by omega
    rw [form,rem,div]
    cases a u <;> rfl

private theorem satCons (a : Nat → Bool) (k j t) (b : Bool) (cs : List Nat) :
    ClauseSat a (lit k j t b :: cs) ↔ num a k j t = b ∨ ClauseSat a cs := by
  unfold ClauseSat
  simp only [List.mem_cons,exists_eq_or_imp,litEval]
  cases b <;> simp

def valIn (a : Nat → Bool) (j i r : Nat) : Bool :=
  if i<10 then r.testBit i else if i < 10+j then num a 3 (i-10) r else false

structure Meaning (a : Nat → Bool) : Prop where
  op : ∀ j<14, ∃ k<3, num a 0 j k = true
  input : ∀ e∈[1,2], ∀ j<14, ∃ i<10+j+1, num a e j i = true
  side : ∀ e∈[1,2], ∀ j<14, ∀ i<10+j+1, num a e j i = true →
    ∀ r∈rows, num a (e+3) j r = valIn a j i r
  eval : ∀ j<14, ∀ k<3, num a 0 j k = true → ∀ r∈rows, num a 3 j r =
    if k=0 then num a 4 j r && num a 5 j r else if k=1 then num a 4 j r || num a 5 j r else true
  out : ∃ i<25, ∀ r∈rows, valIn a 14 i r = truth r

theorem meaning {f} (covers : Present f) {a : Nat → Bool} (sat : ∀ c ∈ f, ClauseSat a c) : Meaning a := by
  have al (k j bound) (mem : (List.range bound).map (fun i => lit k j i true) ∈ f) :
      ∃ i<bound, num a k j i = true := by
    obtain ⟨v,hv,hon⟩ := sat _ mem
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    exact ⟨i,List.mem_range.mp hi,by simpa [litEval] using hon⟩
  have nil : ¬ ClauseSat a [] := by simp [ClauseSat]
  constructor
  · exact fun j hj => al _ _ _ (covers.opcode j hj)
  · exact fun e eh j jh => al _ _ _ (covers.input e eh j jh)
  · intro e eh j jh i ih sel r rh
    by_cases raw : i<10
    · have h := sat _ (covers.raw e eh j jh r rh i raw)
      simpa [satCons,sel,nil,valIn,raw] using h
    · by_cases prev : i < 10+j
      · obtain ⟨u,eu⟩ : ∃ u, i=10+u := ⟨i-10,by omega⟩
        subst i
        obtain ⟨hp,hq⟩ := covers.prev e eh j jh r rh u (by omega)
        have a₁ := sat _ hp; have a₂ := sat _ hq
        simp [satCons,nil,sel] at a₁ a₂
        simp [valIn,raw,prev]
        grind
      · have iis : i=10+j := by omega
        subst i
        have h := sat _ (covers.zero e eh j jh r rh)
        simpa [satCons,nil,sel,valIn,raw,prev] using h
  · intro j jh k kh selected r rh
    have g := covers.gates j jh r rh
    simp only [List.mem_cons,List.mem_nil_iff,or_false,forall_eq_or_imp] at g
    obtain ⟨g0,g1,g2,g3,g4,g5,g6⟩ := g
    have h0 := sat _ g0; have h1 := sat _ g1; have h2 := sat _ g2
    have h3 := sat _ g3; have h4 := sat _ g4; have h5 := sat _ g5; have h6 := sat _ (g6 _ rfl)
    interval_cases k <;> simp [satCons,nil,selected] at * <;> grind
  · obtain ⟨i,ih,sel⟩ := al _ _ _ covers.output
    use i,ih
    intro r rh
    by_cases raw : i<10
    · simp only [valIn,raw,↓reduceIte]
      by_contra diff
      have h := sat _ (covers.outRaw r rh i raw diff)
      simp [satCons,nil,sel] at h
    · by_cases prev : i<24
      · obtain ⟨u,eu⟩ : ∃ u, i=10+u := ⟨i-10,by omega⟩
        subst i
        have h := sat _ (covers.outPrev r rh u (by omega))
        simpa [satCons,nil,sel,valIn,raw,show 10+u<10+14 by omega] using h
      · have iis : i=24 := by omega
        subst i
        cases tr : truth r
        · rfl
        · have h := sat _ (covers.outZero r rh tr)
          simp [satCons,nil,sel] at h
end Decode3210

namespace Weight3210
def combine (b : Bool) (u v : Nat × Nat) : Nat × Nat :=
  (if b then u.1 &&& v.1 else u.1 ||| v.1, u.2 + v.2)

def cols : List Nat := [5521449, 8532035, 3227782, 430612, 11083800, 111904, 903232, 13500800, 15732224, 14053483]
def base := List.ofFn (fun i : Fin 10 => ((cols.getD i.val 0, 1) : Nat × Nat)) ++ [(0,0),(16777215,0)]
def scoreStep (ws : List (Nat × Nat)) (g : Bool × Nat × Nat) :=
  ws ++ [combine g.1 (ws.getD g.2.1 (0,0)) (ws.getD g.2.2 (0,0))]

end Weight3210

namespace Decode3210
open Weight3210 PEqualNP.Defs.LratEncoding

def pack (rs : List Nat) (f : Nat → Bool) : Nat :=
  rs.foldr (fun r v => Nat.bit (f r) v) 0

private theorem pack_ext (rs : List Nat) {f g : Nat → Bool} (same : ∀ r∈rs, f r = g r) :
    pack rs f = pack rs g := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change Nat.bit _ (pack rs _) = Nat.bit _ (pack rs _)
    rw [same r (by simp),ih (fun k h => same k (by simp [h]))]

private theorem pack_combine (rs : List Nat) (op : Bool) (f g : Nat → Bool) :
    pack rs (fun r => if op then f r && g r else f r || g r) =
    if op then pack rs f &&& pack rs g else pack rs f ||| pack rs g := by
  induction rs with
  | nil => cases op <;> simp [pack]
  | cons r rs ih =>
    cases op <;> simp only [pack,List.foldr_cons,Bool.false_eq_true,ite_false,ite_true] at ih ⊢
    · rw [Nat.lor_bit,ih]
    · rw [Nat.land_bit,ih]

private theorem rawNumbers : ∀ i : Fin 10, ∃ w ∈ base, w.1 = pack rows (fun r => r.testBit i.val) := by decide +kernel
private theorem constantNumbers : (0,0) ∈ base ∧ (16777215,0) ∈ base ∧
    pack rows (fun _ => false) = 0 ∧ pack rows (fun _ => true) = 16777215 ∧
    pack rows truth = 4095 := by decide +kernel

abbrev WS := List (Nat × Nat)
abbrev Cmd := Bool × Nat × Nat
def Has (ws : WS) (f : Nat → Bool) := ∃ w ∈ ws, w.1 = pack rows f

private theorem has_ext {f g} {ws} (h : Has ws f) (same : ∀ r ∈ rows, f r = g r) : Has ws g := by
  obtain ⟨w,mem,eq⟩ := h
  exact ⟨w,mem,eq.trans (pack_ext rows same)⟩

private theorem keep (p : List Cmd) (ws : WS) {w} (mem : w ∈ ws) : w ∈ p.foldl scoreStep ws := by
  induction p generalizing ws with
  | nil => exact mem
  | cons g p ih => exact ih (scoreStep ws g) (List.mem_append_left _ mem)

private theorem readIn {a : Nat → Bool} {p : List Cmd} {j : Nat}
    (earlier : ∀ t<j, Has (p.foldl scoreStep base) (num a 3 t)) (i : Nat) :
    Has (p.foldl scoreStep base) (valIn a j i) := by
  by_cases raw : i<10
  · obtain ⟨w,hw,e⟩ := rawNumbers ⟨i,raw⟩
    exact ⟨w,keep p base hw,e.trans (pack_ext rows (fun r _ => by simp [valIn,raw]))⟩
  · by_cases prev : i < 10+j
    · apply has_ext (earlier (i-10) (by omega))
      intro r _
      simp [valIn,raw,prev]
    · exact ⟨(0,0),keep p base constantNumbers.1,constantNumbers.2.2.1.symm.trans (pack_ext rows (fun r _ => by simp [valIn,raw,prev]))⟩

private theorem writeGate {ws : WS} {f g} (op : Bool) (hf : Has ws f) (hg : Has ws g) :
    ∃ c : Cmd, Has (scoreStep ws c) (fun r => if op then f r && g r else f r || g r) := by
  obtain ⟨u,hu,eu⟩ := hf
  obtain ⟨v,hv,ev⟩ := hg
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp hv
  have ui : ws.getD i (0,0)=u := (List.getD_eq_getElem _ _ hi).trans ei
  have vj : ws.getD j (0,0)=v := (List.getD_eq_getElem _ _ hj).trans ej
  use (op,i,j),combine op u v
  constructor
  · apply List.mem_append_right
    change combine op u v ∈ [combine op (ws.getD i (0,0)) (ws.getD j (0,0))]
    rw [ui,vj]; simp
  · simp [combine,eu,ev,pack_combine]

private theorem compile {a} (sem : Meaning a) (j : Nat) (jh : j≤14) :
    ∃ p : List Cmd, p.length = j ∧ ∀ t<j, Has (p.foldl scoreStep base) (num a 3 t) := by
  induction j with
  | zero => exact ⟨[],rfl,by omega⟩
  | succ j ih =>
    obtain ⟨p,length,done⟩ := ih (by omega)
    let ws := p.foldl scoreStep base
    have jlt : j<14 := by omega
    obtain ⟨k,kh,ks⟩ := sem.op j jlt
    obtain ⟨i,ih',is⟩ := sem.input 1 (by simp) j jlt
    obtain ⟨i',ih'',is'⟩ := sem.input 2 (by simp) j jlt
    have l : Has ws (num a 4 j) := has_ext (readIn done i) (fun r h => (sem.side 1 (by simp) j jlt i ih' is r h).symm)
    have r : Has ws (num a 5 j) := has_ext (readIn done i') (fun r h => (sem.side 2 (by simp) j jlt i' ih'' is' r h).symm)
    have gate : ∃ c : Cmd, Has (scoreStep ws c) (num a 3 j) := by
      interval_cases k
      · obtain ⟨c,hc⟩ := writeGate true l r
        exact ⟨c,has_ext hc (fun row hr => by simpa using (sem.eval j jlt 0 (by decide) ks row hr).symm)⟩
      · obtain ⟨c,hc⟩ := writeGate false l r
        exact ⟨c,has_ext hc (fun row hr => by simpa using (sem.eval j jlt 1 (by decide) ks row hr).symm)⟩
      · have one : Has ws (fun _ => true) :=
          ⟨(16777215,0),keep p base constantNumbers.2.1,constantNumbers.2.2.2.1.symm⟩
        obtain ⟨c,hc⟩ := writeGate true one one
        exact ⟨c,has_ext hc (fun row hr => by simpa using (sem.eval j jlt 2 (by decide) ks row hr).symm)⟩
    obtain ⟨c,hc⟩ := gate
    refine ⟨p ++ [c],by simp [length],?_⟩
    intro t tl
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    by_cases eq : t=j
    · simpa [eq] using hc
    · obtain ⟨w,hw,ev⟩ := done t (by omega)
      exact ⟨w,List.mem_append_left _ hw,ev⟩

theorem decode {f : List (List Nat)} (present : Present f) (h : FormulaSat f) :
    ∃ p : List (Bool × Nat × Nat), p.length ≤ 14 ∧ ∃ k, (4095,k) ∈ p.foldl scoreStep base := by
  obtain ⟨a,sat⟩ := h
  have sem := meaning present sat
  obtain ⟨p,plen,prev⟩ := compile sem 14 (by decide)
  obtain ⟨i,_,chosen⟩ := sem.out
  obtain ⟨⟨v,k⟩,hw,correct⟩ := has_ext (readIn prev i) chosen
  change v=pack rows truth at correct
  rw [constantNumbers.2.2.2.2] at correct
  subst v
  exact ⟨p,by omega,k,hw⟩
end Decode3210

theorem VerifiedDecoder3210 : let raw : List Nat := [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
      let base := List.ofFn (fun i : Fin 10 => ((raw.getD i.val 0,1) : Nat × Nat)) ++ [(0,0),(16777215,0)]
      let step := fun (ws : List (Nat × Nat)) (g : Bool × Nat × Nat) =>
        let a := ws.getD g.2.1 (0,0)
        let b := ws.getD g.2.2 (0,0)
        ws ++ [(if g.1 then a.1 &&& b.1 else a.1 ||| b.1, a.2+b.2)]
      (let yes : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
      let no : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
      PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc 10 14 yes.contains (yes++no))) → ∃ (p : List (Bool × Nat × Nat)) (k : Nat), p.length ≤ 14 ∧ (4095,k) ∈ p.foldl step base := by
  dsimp only
  intro h
  obtain ⟨p,hp,k,hk⟩ := Decode3210.decode Decode3210.present_enc h
  exact ⟨p,k,hp,hk⟩

namespace Live3210

abbrev Instruction := Bool × Nat × Nat
def full : Nat := 2^24-1
def combine (op : Bool) (a b : Nat) := if op then a &&& b else a ||| b
def step (ws : List Nat) (g : Instruction) :=
  ws ++ [combine g.1 (ws.getD g.2.1 0) (ws.getD g.2.2 0)]

inductive Move (ban : Finset Nat) (s t : Finset Nat) : Prop where
  | take (op : Bool) (a b w : Nat) (keep : Finset Nat)
      (left : a ∈ s) (right : b ∈ s) (different : a ≠ b)
      (value : w = combine op a b) (nonzero : w ≠ 0) (nonfull : w ≠ full)
      (fresh : w ∉ s) (notBase : w ∉ ban) (retained : keep ⊆ {a,b})
      (next : t = insert w (((s.erase a).erase b) ∪ keep)) : Move ban s t

inductive Trace (ban : Finset Nat) : Nat → Finset Nat → Finset Nat → Prop where
  | done (s) : Trace ban 0 s s
  | more {s t u k} (move : Move ban s t) (tail : Trace ban k t u) : Trace ban (k+1) s u

abbrev Guard := Nat → Finset Nat → Prop
inductive Filtered (ban : Finset Nat) (guard : Guard) : Nat → Finset Nat → Finset Nat → Prop where
  | done (s) : Filtered ban guard 0 s s
  | more {s t u k} (move : Move ban s t) (allowed : ∀ z∈t, z∉s → guard z s)
      (tail : Filtered ban guard k t u) : Filtered ban guard (k+1) s u

theorem Filtered.plain {ban guard k s t} (path : Filtered ban guard k s t) : Trace ban k s t := by
  induction path with
  | done => exact .done _
  | more m _ _ ih => exact .more m ih

def audited (guard : Guard) : List Instruction → List Nat → Prop
  | [], _ => True
  | g::p, ws =>
    (∀ s : Finset Nat, (∀ x ∈ s, x ∈ ws) →
      guard (combine g.1 (ws.getD g.2.1 0) (ws.getD g.2.2 0)) s) ∧ audited guard p (step ws g)

def Fits (ws : List Nat) (s : Finset Nat) :=
  ∀ x ∈ s, x ∈ ws ∧ x ≠ 0 ∧ x ≠ full

private theorem get_bound {ws : List Nat} (h : ∀ w∈ws, w<2^24) (i) : ws.getD i 0 < 2^24 := by
  by_cases hi : i<ws.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; decide

private theorem mem_or_zero (ws : List Nat) (i) : ws.getD i 0 ∈ ws ∨ ws.getD i 0=0 := by
  by_cases hi : i<ws.length
  · left; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · exact Or.inr (List.getD_eq_default _ _ (by omega))

private theorem combine_bound (op : Bool) {a b : Nat} (ha : a<2^24) (hb : b<2^24) :
    combine op a b < 2^24 := by
  cases op
  · exact Nat.or_lt_two_pow ha hb
  · exact Nat.and_lt_two_pow _ hb

private theorem full_or {a : Nat} (ha : a<2^24) : full ||| a = full := by
  have low : full ≤ full ||| a := Nat.left_le_or
  have high := Nat.or_lt_two_pow (by decide : full < 2^24) ha
  change 16777215 ≤ full ||| a at low
  change full ||| a < 16777216 at high
  change full ||| a = 16777215
  omega

private theorem left_nontrivial (op : Bool) {a b : Nat} (hb : b<2^24)
    (nz : combine op a b ≠ 0) (nf : combine op a b ≠ full)
    (newB : combine op a b ≠ b) : a ≠ 0 ∧ a ≠ full := by
  constructor
  · rintro rfl
    cases op <;> simp [combine] at *
  · rintro rfl
    cases op
    · exact nf (full_or hb)
    · exact newB (Nat.and_comm .. |>.trans (Nat.and_two_pow_sub_one_of_lt_two_pow hb))

private theorem combine_comm (op : Bool) (a b : Nat) : combine op a b = combine op b a := by
  cases op <;> simp [combine,Nat.or_comm,Nat.and_comm]

theorem compileWith (guard : Guard) (ban : Finset Nat) (p : List Instruction) (ws : List Nat)
    (bounds : ∀ w∈ws, w<2^24) (keepBase : ∀ z∈ban, z∈ws)
    (d : Finset Nat) (post : Fits (p.foldl step ws) d) (ok : audited guard p ws) :
    ∃ s k, Fits ws s ∧ k ≤ p.length ∧ Filtered ban guard k s d := by
  classical
  induction p generalizing ws with
  | nil => exact ⟨d,0,post,by simp,.done d⟩
  | cons g p ih =>
    let a := ws.getD g.2.1 0
    let b := ws.getD g.2.2 0
    let w := combine g.1 a b
    have aB : a<2^24 := get_bound bounds _
    have bB : b<2^24 := get_bound bounds _
    have nextBound : ∀ z∈step ws g, z<2^24 := by
      intro z hz
      change z ∈ ws++[w] at hz
      rcases List.mem_append.mp hz with h|h
      · exact bounds _ h
      · simp only [List.mem_singleton] at h
        exact h ▸ combine_bound g.1 aB bB
    obtain ⟨t,k,fit,clock,path⟩ := ih (step ws g) nextBound
      (fun z h => List.mem_append_left _ (keepBase z h)) post ok.2
    have others (z) (hz : z∈t) (ne : z≠w) : z∈ws := by
      have inc := (fit z hz).1
      change z∈ws++[w] at inc
      simpa [ne] using inc
    by_cases original : w ∈ ws
    · refine ⟨t,k,?_,by simp; omega,path⟩
      intro z h
      exact ⟨by by_cases e : z=w; exact e ▸ original; exact others z h e,(fit z h).2⟩
    by_cases wanted : w ∈ t
    · have nz := (fit w wanted).2.1
      have nf := (fit w wanted).2.2
      have ma : a∈ws ∨ a=0 := mem_or_zero ws _
      have mb : b∈ws ∨ b=0 := mem_or_zero ws _
      have na : w≠a := fun e => ma.elim (fun h => original (e ▸ h)) (fun z => nz (e.trans z))
      have nb : w≠b := fun e => mb.elim (fun h => original (e ▸ h)) (fun z => nz (e.trans z))
      have av := left_nontrivial g.1 bB nz nf nb
      have bv : b≠0 ∧ b≠full := by
        apply left_nontrivial g.1 aB <;> rw [combine_comm g.1 b a] <;> assumption
      have am := ma.resolve_right av.1
      have bm := mb.resolve_right bv.1
      have ab : a≠b := by
        intro e
        apply na
        simp [w,e,combine]
      let s := insert a (insert b (t.erase w))
      have small : Fits ws s := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl|h
        · exact ⟨am,av⟩
        rcases Finset.mem_insert.mp h with rfl|h
        · exact ⟨bm,bv⟩
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp h
        exact ⟨others z mem ne,(fit z mem).2⟩
      refine ⟨s,k+1,small,by simp; omega,.more (.take g.1 a b w (t ∩ {a,b})
        (by simp [s]) (by simp [s]) ab rfl nz nf (by simp [s,na,nb])
        (fun h => original (keepBase w h)) (Finset.inter_subset_right) ?_) ?_ path⟩
      · ext z
        by_cases h₁ : z=a <;> by_cases h₂ : z=b <;> by_cases h₃ : z=w <;>
          simp_all [s]
      · intro z zt missing
        have eq : z=w := by
          by_contra ne
          exact missing (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ne,zt⟩)))
        exact eq ▸ ok.1 s (fun r hr => (small r hr).1)
    · exact ⟨t,k,fun z h => ⟨others z h (fun e => wanted (e ▸ h)),(fit z h).2⟩,by simp; omega,path⟩

theorem compile (ban : Finset Nat) (p : List Instruction) (ws : List Nat)
    (bounds : ∀ w∈ws, w<2^24) (keepBase : ∀ z∈ban, z∈ws)
    (d : Finset Nat) (post : Fits (p.foldl step ws) d) :
    ∃ s k, Fits ws s ∧ k ≤ p.length ∧ Trace ban k s d := by
  have ok (ps : List Instruction) (w : List Nat) : audited (fun _ _ => True) ps w := by
    induction ps generalizing w with
    | nil => trivial
    | cons g ps ih => exact ⟨fun _ _ => trivial,ih _⟩
  obtain ⟨s,k,fit,b,path⟩ := compileWith _ ban p ws bounds keepBase d post (ok p ws)
  exact ⟨s,k,fit,b,path.plain⟩

end Live3210

namespace Live3210

def covers (w : Nat) (i j : Fin 12) : Prop :=
  w.testBit i.val = true ∧ w.testBit (12+j.val) = false
instance (w : Nat) (i j : Fin 12) : Decidable (covers w i j) := by unfold covers; infer_instance
def separates (s : Finset Nat) : Prop := ∀ i j : Fin 12, ∃ w ∈ s, covers w i j

private theorem descend (op : Bool) (a b : Nat) (i j) (h : covers (combine op a b) i j) :
    covers a i j ∨ covers b i j := by
  unfold covers at *
  cases op <;> simp only [combine,Bool.false_eq_true,↓reduceIte,Nat.testBit_or,Nat.testBit_and] at h <;>
    cases ha : a.testBit i.val <;> cases hb : b.testBit i.val <;>
    cases hc : a.testBit (12+j.val) <;> cases hd : b.testBit (12+j.val) <;> simp_all

theorem Move.back {ban s t} (move : Move ban s t) (h : separates t) : separates s := by
  intro i j
  obtain ⟨w,mem,good⟩ := h i j
  rcases move with ⟨op,a,b,z,keep,ha,hb,_,rfl,_,_,_,_,sub,rfl⟩
  rcases Finset.mem_insert.mp mem with rfl|others
  · rcases descend op a b i j good with l|r
    · exact ⟨a,ha,l⟩
    · exact ⟨b,hb,r⟩
  · refine ⟨w,?_,good⟩
    rcases Finset.mem_union.mp others with old|kept
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp old).2).2
    · have both : w=a ∨ w=b := by simpa only [Finset.mem_insert,Finset.mem_singleton] using sub kept
      exact both.elim (fun e => e ▸ ha) (fun e => e ▸ hb)

theorem Move.card_back {ban s t} (move : Move ban s t) : s.card ≤ t.card+1 := by
  rcases move with ⟨op,a,b,w,keep,ha,hb,neq,_,_,_,fresh,_,_,rfl⟩
  have left := Finset.card_erase_add_one ha
  have right := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨Ne.symm neq,hb⟩ : b ∈ s.erase a)
  let old := (s.erase a).erase b
  have no : w∉old := fun h => fresh (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
  have sub : insert w old ⊆ insert w (old ∪ keep) := Finset.insert_subset_insert _ Finset.subset_union_left
  have c := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem no] at c
  change s.card ≤ (insert w (old ∪ keep)).card+1
  change old.card+1 = (s.erase a).card at right
  omega

theorem Trace.back {ban k s t} (path : Trace ban k s t) (good : separates t) : separates s := by
  induction path with
  | done => exact good
  | more move _ ih => exact move.back (ih good)

theorem Trace.card_bound {ban k s t} (path : Trace ban k s t) : s.card ≤ t.card+k := by
  induction path with
  | done => simp
  | more move _ ih => have := move.card_back; omega

def inputs : List Nat := [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
def required : Finset Nat := (inputs.take 9).toFinset
def optional : Nat := 14053483
def raw : Finset Nat := inputs.toFinset

private theorem keys : ∀ w∈required, ∃ i j : Fin 12, ∀ v∈raw, covers v i j → v=w := by
  decide +kernel
private theorem raw_id : raw = insert optional required := by decide +kernel
theorem start_set {s : Finset Nat} (sub : s⊆raw) (sep : separates s) : s=required ∨ s=raw := by
  have inc : required ⊆ s := by
    intro w hw
    obtain ⟨i,j,only⟩ := keys w hw
    obtain ⟨v,hv,good⟩ := sep i j
    exact only v (sub hv) good ▸ hv
  by_cases opt : optional∈s
  · right; exact Finset.Subset.antisymm sub (by rw [raw_id]; exact Finset.insert_subset opt inc)
  · left; apply Finset.Subset.antisymm _ inc
    intro v hv
    have up := sub hv
    rw [raw_id,Finset.mem_insert] at up
    exact up.resolve_left (fun e => opt (e ▸ hv))

theorem target_sep : separates {4095} := by unfold separates; decide +kernel

def initialScored :=
  List.ofFn (fun i : Fin 10 => ((inputs.getD i.val 0,1) : Nat × Nat)) ++ [(0,0),(16777215,0)]
def scored (ws : List (Nat×Nat)) (g : Instruction) :=
  let a := ws.getD g.2.1 (0,0)
  let b := ws.getD g.2.2 (0,0)
  ws ++ [(combine g.1 a.1 b.1,a.2+b.2)]

private theorem optionFirst (p : Option (Nat×Nat)) :
    (p.map Prod.fst).getD 0 = (p.getD (0,0)).1 := by cases p <;> rfl
theorem forget_score (p : List Instruction) (ws : List (Nat×Nat)) :
    (p.foldl scored ws).map Prod.fst = p.foldl step (ws.map Prod.fst) := by
  induction p generalizing ws with
  | nil => rfl
  | cons g p ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    simp [scored,step,optionFirst]

theorem from_program (p : List Instruction) (cost : Nat) (len : p.length≤14)
    (hit : (4095,cost)∈p.foldl scored initialScored) :
    ∃ s k, (s=required ∨ s=raw) ∧ k≤14 ∧ Trace raw k s {4095} := by
  let ws := initialScored.map Prod.fst
  have hs : ws=inputs++[0,full] := by decide +kernel
  have bounds : ∀ x∈ws, x<2^24 := by decide +kernel
  have retain : ∀ x∈raw, x∈ws := by decide +kernel
  have present : 4095∈p.foldl step ws := by
    rw [←forget_score]
    exact List.mem_map.mpr ⟨(4095,cost),hit,rfl⟩
  have clean : Fits (p.foldl step ws) {4095} := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst x
    exact ⟨present,by decide,by decide⟩
  obtain ⟨s,k,fit,costBound,path⟩ := compile raw p ws bounds retain _ clean
  have sub : s⊆raw := by
    intro v hv
    obtain ⟨hw,nz,nf⟩ := fit v hv
    simpa [hs,raw,nz,nf] using hw
  exact ⟨s,k,start_set sub (path.back target_sep),costBound.trans len,path⟩

end Live3210

namespace Live3210

def Dominated (w v : Nat) : Prop :=
  (∀ i : Fin 12, w.testBit i.val = true → v.testBit i.val = true) ∧
  (∀ j : Fin 12, v.testBit (12+j.val) = true → w.testBit (12+j.val) = true)

def stronger (ban : Finset Nat) (w : Nat) (s : Finset Nat) : Prop :=
  ∀ v ∈ s ∪ ban, ¬Dominated w v

theorem Dominated.refl (w) : Dominated w w := ⟨fun _ h => h, fun _ h => h⟩
theorem Dominated.trans {w a b} (h : Dominated w a) (g : Dominated a b) : Dominated w b :=
  ⟨fun i p => g.1 i (h.1 i p),fun i p => h.2 i (g.2 i p)⟩

private theorem bit_op (op : Bool) (a b : Nat) (i) :
    (combine op a b).testBit i =
      (if op then a.testBit i && b.testBit i else a.testBit i || b.testBit i) := by
  cases op <;> simp [combine]
private theorem bit_mono (op x y u v : Bool) (hx : x=true → u=true) (hy : y=true → v=true) :
    (if op then x && y else x || y) = true → (if op then u && v else u || v) = true := by
  cases op <;> cases x <;> cases y <;> cases u <;> cases v <;> simp_all

theorem Dominated.op {a a' b b'} (ha : Dominated a a') (hb : Dominated b b') (op : Bool) :
    Dominated (combine op a b) (combine op a' b') := by
  constructor <;> intro i
  · rw [bit_op,bit_op]
    exact bit_mono op _ _ _ _ (ha.1 i) (hb.1 i)
  · rw [bit_op,bit_op]
    exact bit_mono op _ _ _ _ (ha.2 i) (hb.2 i)

theorem target_maximal {v : Nat} (bound : v<2^24) (h : Dominated 4095 v) : v=4095 := by
  have pos : ∀ i : Fin 12, (4095 : Nat).testBit i.val = true := by decide +kernel
  have neg : ∀ i : Fin 12, (4095 : Nat).testBit (12+i.val) = false := by decide +kernel
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases lo : i<12
  · exact (h.1 ⟨i,lo⟩ (pos ⟨i,lo⟩)).trans (pos ⟨i,lo⟩).symm
  by_cases hi : i<24
  · let j : Fin 12 := ⟨i-12,by omega⟩
    have ij : i=12+j.val := by dsimp [j]; omega
    rw [ij,neg j]
    cases on : v.testBit (12+j.val) with
    | false => rfl
    | true => simpa [neg j] using h.2 j on
  · have up : 2^24 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (bound.trans_le up),
        Nat.testBit_lt_two_pow ((by decide : 4095<2^24).trans_le up)]

def approximates (ws vs : List Nat) : Prop := ∀ w ∈ ws, ∃ v ∈ vs, Dominated w v

private theorem mem_read (ws : List Nat) (zero : 0 ∈ ws) (i : Nat) : ws.getD i 0 ∈ ws :=
  (mem_or_zero ws i).elim id (fun h => by rw [h]; exact zero)
private theorem find_read {v : Nat} {ws : List Nat} (h : v∈ws) : ∃ i, ws.getD i 0=v := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  exact ⟨i,(List.getD_eq_getElem _ _ hi).trans eq⟩

theorem normalize (ban : Finset Nat) (p : List Instruction) (ws vs : List Nat)
    (zero : 0∈ws) (base : ∀ v∈ban, v∈vs) (sim : approximates ws vs) :
    ∃ q : List Instruction, q.length≤p.length ∧ audited (stronger ban) q vs ∧
      approximates (p.foldl step ws) (q.foldl step vs) := by
  classical
  induction p generalizing ws vs with
  | nil => exact ⟨[],by simp,True.intro,sim⟩
  | cons g p ih =>
    let a := ws.getD g.2.1 0
    let b := ws.getD g.2.2 0
    let w := combine g.1 a b
    obtain ⟨a',am,ad⟩ := sim a (mem_read ws zero _)
    obtain ⟨b',bm,bd⟩ := sim b (mem_read ws zero _)
    let v := combine g.1 a' b'
    have wd : Dominated w v := ad.op bd g.1
    have zs : 0 ∈ step ws g := List.mem_append_left _ zero
    by_cases redundant : ∃ y∈vs, Dominated v y
    · obtain ⟨y,ym,yd⟩ := redundant
      have next : approximates (step ws g) vs := by
        intro t ht
        rcases List.mem_append.mp ht with old|new
        · exact sim t old
        · change t∈[w] at new
          obtain rfl := List.mem_singleton.mp new
          exact ⟨y,ym,wd.trans yd⟩
      obtain ⟨q,len,ok,done⟩ := ih (step ws g) vs zs base next
      exact ⟨q,by simp; omega,ok,done⟩
    · obtain ⟨i,readA⟩ := find_read am
      obtain ⟨j,readB⟩ := find_read bm
      let g' : Instruction := (g.1,i,j)
      have nextEq : step vs g'=vs++[v] := by simp only [step,g',readA,readB,v]
      have keep (t) (ht : t∈vs) : t∈step vs g' := nextEq ▸ List.mem_append_left _ ht
      have next : approximates (step ws g) (step vs g') := by
        intro t ht
        rcases List.mem_append.mp ht with old|new
        · obtain ⟨s,hs,d⟩ := sim t old
          exact ⟨s,keep _ hs,d⟩
        · change t∈[w] at new
          obtain rfl := List.mem_singleton.mp new
          exact ⟨v,by simp [nextEq],wd⟩
      obtain ⟨q,len,ok,done⟩ := ih (step ws g) (step vs g') zs (fun t ht => keep t (base t ht)) next
      refine ⟨g'::q,by simpa using len,⟨?_,ok⟩,done⟩
      intro s sub y hy dom
      have present := (Finset.mem_union.mp hy).elim (sub y) (base y)
      apply redundant
      exact ⟨y,present,by simpa only [g',readA,readB,v] using dom⟩

theorem bounded_run (p : List Instruction) (ws : List Nat) (ok : ∀ x∈ws, x<2^24) :
    ∀ x∈p.foldl step ws, x<2^24 := by
  induction p generalizing ws with
  | nil => exact ok
  | cons g p ih =>
    apply ih
    intro w hw
    rcases List.mem_append.mp hw with h|h
    · exact ok w h
    · rw [List.mem_singleton] at h
      exact h ▸ combine_bound g.1 (get_bound ok _) (get_bound ok _)

def sources : Finset Nat := insert 0 (insert full raw)

theorem dominated_trace (p : List Instruction) (cost : Nat) (len : p.length≤14)
    (hit : (4095,cost)∈p.foldl scored initialScored) :
    ∃ s k, (s=required ∨ s=raw) ∧ k≤14 ∧ Filtered raw (stronger sources) k s {4095} := by
  let ws := initialScored.map Prod.fst
  have hs : ws=inputs++[0,full] := by decide +kernel
  have bounds : ∀ x∈ws, x<2^24 := by decide +kernel
  have retain : ∀ x∈raw, x∈ws := by decide +kernel
  have present : 4095∈p.foldl step ws := by
    rw [←forget_score]
    exact List.mem_map.mpr ⟨(4095,cost),hit,rfl⟩
  have allSources : ∀ x∈sources, x∈ws := by decide +kernel
  obtain ⟨q,le,ok,sim⟩ := normalize sources p ws ws (by decide +kernel) allSources
    (fun w hw => ⟨w,hw,Dominated.refl w⟩)
  obtain ⟨v,vm,dom⟩ := sim 4095 present
  obtain rfl := target_maximal (bounded_run q ws bounds v vm) dom
  have endFit : Fits (q.foldl step ws) {4095} := by
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨vm,by decide,by decide⟩
  obtain ⟨s,k,fit,size,path⟩ := compileWith _ raw q ws bounds retain _ endFit ok
  have sub : s⊆raw := by
    intro v hv
    obtain ⟨hw,nz,nf⟩ := fit v hv
    simpa [hs,raw,nz,nf] using hw
  exact ⟨s,k,start_set sub (path.plain.back target_sep),size.trans (le.trans len),path⟩

end Live3210

namespace Live3210.Ordered

-- A signal is tagged with its value and its depth in the circuit.
abbrev Signal := Nat × Nat
def key (s : Signal) := 16777216*s.2+s.1
structure Gate where
  op : Bool
  left : Signal
  right : Signal
  deriving DecidableEq

def Gate.output (g : Gate) : Signal :=
  (combine g.op g.left.1 g.right.1,1+max g.left.2 g.right.2)
def Gate.inputs (g : Gate) := [g.left,g.right]
def built (pool : List Signal) (gs : List Gate) := pool ++ gs.map Gate.output
def legal (pool : List Signal) : List Gate → Prop
  | [] => True
  | g::gs => (∀ x∈g.inputs, x∈pool) ∧ legal (g.output::pool) gs

private theorem built_cons {w : Signal} {g : Gate} {gs pool} :
    w∈built (g.output::pool) gs ↔ w∈built pool (g::gs) := by
  simp [built,or_left_comm]

def represents (ws : List Nat) (pool : List Signal) :=
  ∀ w∈ws, ∃ v∈pool, v.1=w

theorem tag (p : List Instruction) (ws : List Nat) (pool : List Signal)
    (zero : 0∈ws) (cover : represents ws pool) :
    ∃ gs : List Gate, gs.length=p.length ∧ legal pool gs ∧
      represents (p.foldl step ws) (built pool gs) := by
  induction p generalizing ws pool with
  | nil => exact ⟨[],rfl,True.intro,by simpa [built] using cover⟩
  | cons g p ih =>
    obtain ⟨a,ha,ae⟩ := cover _ (mem_read ws zero g.2.1)
    obtain ⟨b,hb,be⟩ := cover _ (mem_read ws zero g.2.2)
    let node : Gate := ⟨g.1,a,b⟩
    have rep : represents (step ws g) (node.output::pool) := by
      intro x hx
      rcases List.mem_append.mp hx with h|h
      · obtain ⟨v,hv,eq⟩ := cover x h
        exact ⟨v,List.mem_cons_of_mem _ hv,eq⟩
      · refine ⟨node.output,by simp,?_⟩
        rw [List.mem_singleton] at h
        simpa only [Gate.output,node,ae,be] using h.symm
    obtain ⟨gs,length,ok,seen⟩ := ih (step ws g) (node.output::pool) (List.mem_append_left _ zero) rep
    refine ⟨node::gs,by simp [length],⟨?_,ok⟩,?_⟩
    · intro x hx
      simp [node,Gate.inputs] at hx
      exact hx.elim (fun e => e ▸ ha) (fun e => e ▸ hb)
    · intro x hx
      obtain ⟨v,hv,eq⟩ := seen x hx
      exact ⟨v,built_cons.mp hv,eq⟩

def safe (pool : List Signal) := ∀ x∈pool, x.1<2^24
private theorem operand_before {g : Gate} {x : Signal} (hx : x∈g.inputs) (h : x.1<2^24) :
    key x < key g.output := by
  have depth : x.2 < 1+max g.left.2 g.right.2 := by
    simp [Gate.inputs] at hx
    rcases hx with rfl|rfl
    · have := Nat.le_max_left g.left.2 g.right.2; omega
    · have := Nat.le_max_right g.left.2 g.right.2; omega
  change 16777216*x.2+x.1 < 16777216*(1+max g.left.2 g.right.2)+_
  change x.1<16777216 at h
  omega

def Supply (pool : List Signal) (gs : List Gate) : Prop :=
  ∀ g∈gs, ∀ x∈g.inputs, x∈pool ∨ ∃ p∈gs, p.output=x ∧ key p.output<key g.output

theorem supplies {pool gs} (ok : legal pool gs) (bound : safe pool) : Supply pool gs := by
  induction gs generalizing pool with
  | nil => simp [Supply]
  | cons g gs ih =>
    have gv : g.output.1<2^24 := combine_bound g.op (bound _ (ok.1 _ (by simp [Gate.inputs])))
      (bound _ (ok.1 _ (by simp [Gate.inputs])))
    have rest := ih ok.2 (fun x h => (List.mem_cons.mp h).elim (fun e => e ▸ gv) (bound x))
    intro t ht x hx
    rcases List.mem_cons.mp ht with rfl|later
    · exact Or.inl (ok.1 _ hx)
    rcases rest t later x hx with now|⟨p,hp,eq,lt⟩
    · rcases List.mem_cons.mp now with rfl|early
      · exact Or.inr ⟨g,by simp,rfl,operand_before hx gv⟩
      · exact Or.inl early
    · exact Or.inr ⟨p,List.mem_cons_of_mem _ hp,eq,lt⟩

def precedes (g h : Gate) : Prop := key g.output ≤ key h.output
private theorem legal_of_sorted {pool gs} (ord : gs.Pairwise precedes) (supply : Supply pool gs) :
    legal pool gs := by
  induction gs generalizing pool with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ord
    constructor
    · intro x hx
      rcases supply g (by simp) x hx with now|⟨p,hp,_,lt⟩
      · exact now
      · rcases List.mem_cons.mp hp with rfl|later
        · omega
        · exact False.elim ((Nat.not_lt_of_ge (head p later)) lt)
    · apply ih tail
      intro f hf x hx
      rcases supply f (List.mem_cons_of_mem _ hf) x hx with now|⟨p,hp,eq,lt⟩
      · exact Or.inl (List.mem_cons_of_mem _ now)
      · rcases List.mem_cons.mp hp with rfl|old
        · exact Or.inl (eq ▸ List.mem_cons_self)
        · exact Or.inr ⟨p,old,eq,lt⟩

instance (g h : Gate) : Decidable (precedes g h) := inferInstanceAs (Decidable (_ ≤ _))
def sort (gs : List Gate) := gs.mergeSort (fun g h => decide (precedes g h))

theorem sort_perm (gs : List Gate) : (sort gs).Perm gs := List.mergeSort_perm ..
theorem sort_order (gs : List Gate) : (sort gs).Pairwise precedes := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ij
  have sorted : (sort gs).Pairwise (fun g h => decide (precedes g h) = true) :=
    List.pairwise_mergeSort (by intro a b c h₁ h₂; exact decide_eq_true (Nat.le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂)))
      (by intro a b; rcases Nat.le_total (key a.output) (key b.output) with h|h <;> simp [precedes,h]) gs
  exact of_decide_eq_true (List.pairwise_iff_getElem.mp sorted i j hi hj ij)

theorem reorder {pool gs} (ok : legal pool gs) (bounds : safe pool) : legal pool (sort gs) := by
  apply legal_of_sorted (sort_order gs)
  intro g hg x hx
  have perm := sort_perm gs
  rcases supplies ok bounds g (perm.mem_iff.mp hg) x hx with early|⟨p,prior,e,lt⟩
  · exact Or.inl early
  · exact Or.inr ⟨p,perm.mem_iff.mpr prior,e,lt⟩

end Live3210.Ordered

namespace Live3210.Ordered

-- The emitted register instruction reads the values of its two tagged operands.
inductive Reads : List Nat → List Instruction → List Gate → Prop where
  | nil (ws) : Reads ws [] []
  | cons {ws i j p gs} (g : Gate) (left : ws.getD i 0=g.left.1) (right : ws.getD j 0=g.right.1)
      (tail : Reads (ws++[g.output.1]) p gs) : Reads ws ((g.op,i,j)::p) (g::gs)

theorem Reads.length_eq {ws p gs} (read : Reads ws p gs) : p.length=gs.length := by
  induction read <;> simp_all

theorem Reads.value_eq {ws p gs} (read : Reads ws p gs) :
    p.foldl step ws = ws ++ gs.map (fun g => g.output.1) := by
  induction read with
  | nil => simp
  | cons g left right tail ih =>
    simp only [List.foldl_cons,step,left,right]
    simpa [Gate.output] using ih

theorem reify {gs pool} (ok : legal pool gs) (ws : List Nat)
    (concrete : ∀ v∈pool, v.1∈ws) : ∃ p, Reads ws p gs := by
  induction gs generalizing pool ws with
  | nil => exact ⟨[],.nil _⟩
  | cons g gs ih =>
    obtain ⟨i,ha⟩ := find_read (concrete _ (ok.1 g.left (by simp [Gate.inputs])))
    obtain ⟨j,hb⟩ := find_read (concrete _ (ok.1 g.right (by simp [Gate.inputs])))
    obtain ⟨p,rest⟩ := ih ok.2 (ws++[g.output.1]) (by
      intro v hv
      rcases List.mem_cons.mp hv with rfl|h
      · simp
      · exact List.mem_append_left _ (concrete _ h))
    exact ⟨(g.op,i,j)::p,.cons g ha hb rest⟩

def undominated : List Instruction → List Nat → Prop
  | [],_ => True
  | g::p,ws =>
    (∀ v∈ws, ¬Dominated (combine g.1 (ws.getD g.2.1 0) (ws.getD g.2.2 0)) v) ∧
      undominated p (step ws g)

theorem shorten {p : List Instruction} {ws : List Nat}
    (zero : 0∈ws) (bounded : ∀w∈ws, w<2^24)
    (goal : 4095∈p.foldl step ws) (bad : ¬undominated p ws) :
    ∃ q : List Instruction, q.length < p.length ∧ 4095∈q.foldl step ws := by
  classical
  induction p generalizing ws with
  | nil => exact False.elim (bad True.intro)
  | cons g p ih =>
    let w := combine g.1 (ws.getD g.2.1 0) (ws.getD g.2.2 0)
    by_cases useful : ∀v∈ws, ¬Dominated w v
    · have miss : ¬ undominated p (step ws g) := fun h => bad ⟨useful,h⟩
      obtain ⟨q,len,h⟩ := ih (List.mem_append_left _ zero) (bounded_run [g] ws bounded) goal miss
      exact ⟨g::q,by simpa using len,h⟩
    · obtain ⟨v,member,dom⟩ : ∃v∈ws, Dominated w v := by push Not at useful; exact useful
      have ready : approximates (step ws g) ws := by
        intro t ht
        rcases List.mem_append.mp ht with old|new
        · exact ⟨t,old,Dominated.refl t⟩
        · change t∈[w] at new
          exact ⟨v,member,List.mem_singleton.mp new ▸ dom⟩
      obtain ⟨q,len,_,sim⟩ := normalize ∅ p (step ws g) ws (List.mem_append_left _ zero) (by simp) ready
      obtain ⟨v',inQ,better⟩ := sim 4095 goal
      exact ⟨q,by simp; omega,target_maximal (bounded_run q ws bounded v' inQ) better ▸ inQ⟩

def clean : List Gate → List Signal → Prop
  | [],_ => True
  | g::gs,pool => (∀ v∈pool, ¬Dominated g.output.1 v.1) ∧ clean gs (g.output::pool)

theorem Reads.clean {ws p gs} (r : Reads ws p gs) (optimal : undominated p ws)
    (pool : List Signal) (concrete : ∀ v∈pool, v.1∈ws) : clean gs pool := by
  induction r generalizing pool with
  | nil => trivial
  | @cons ws i j p gs g left right tail ih =>
    have eq : step ws (g.op,i,j) = ws++[g.output.1] := by simp only [step,left,right,Gate.output]
    constructor
    · intro v hv
      simpa only [left,right,Gate.output] using optimal.1 v.1 (concrete v hv)
    · apply ih (eq ▸ optimal.2)
      intro v hv
      rcases List.mem_cons.mp hv with rfl|h
      · simp
      · exact List.mem_append_left _ (concrete _ h)

def startWords := initialScored.map Prod.fst
def taggedRaw : List Signal := startWords.map (fun w => (w,0))
def Synthesizes (n : Nat) := ∃ p : List Instruction, p.length=n ∧ 4095∈p.foldl step startWords

theorem sorted_minimum {p : List Instruction} (cost : Nat) (n : p.length≤14)
    (hit : (4095,cost)∈p.foldl scored initialScored) :
    ∃ nodes : List Gate, nodes.length≤14 ∧ nodes.Pairwise precedes ∧
      legal taggedRaw nodes ∧ clean nodes taggedRaw ∧ ∃ y∈built taggedRaw nodes, y.1=4095 := by
  classical
  have possible : ∃ k, Synthesizes k := by
    refine ⟨p.length,p,rfl,?_⟩
    unfold startWords
    rw [←forget_score]
    exact List.mem_map.mpr ⟨(4095,cost),hit,rfl⟩
  obtain ⟨best,len,goal⟩ := Nat.find_spec possible
  have small : Nat.find possible ≤ p.length := Nat.find_min' possible ⟨p,rfl,by
    unfold startWords; rw [←forget_score]; exact List.mem_map.mpr ⟨(4095,cost),hit,rfl⟩⟩
  have zero : 0∈startWords := by decide +kernel
  have bound : safe taggedRaw := by unfold safe; decide +kernel
  have copy : represents startWords taggedRaw := by
    intro w hw
    exact ⟨(w,0),List.mem_map.mpr ⟨w,hw,rfl⟩,rfl⟩
  obtain ⟨tree,size,ok,seen⟩ := tag best startWords taggedRaw zero copy
  obtain ⟨y,hy,value⟩ := seen 4095 goal
  let nodes := sort tree
  have perm : nodes.Perm tree := sort_perm tree
  have yn : y∈built taggedRaw nodes := by
    rcases List.mem_append.mp hy with raw|made
    · exact List.mem_append_left _ raw
    · exact List.mem_append_right _ ((perm.map _).mem_iff.mpr made)
  have legalN := reorder ok bound
  have exactRaw : ∀ v∈taggedRaw, v.1∈startWords := by
    intro v h
    obtain ⟨w,member,rfl⟩ := List.mem_map.mp h
    exact member
  obtain ⟨new,run⟩ := reify legalN startWords exactRaw
  have newLen : new.length = Nat.find possible := by
    rw [run.length_eq,perm.length_eq,size,len]
  have newGoal : 4095∈new.foldl step startWords := by
    rw [run.value_eq]
    rcases List.mem_append.mp yn with h|h
    · exact List.mem_append_left _ (value ▸ exactRaw y h)
    · obtain ⟨g,hg,eq⟩ := List.mem_map.mp h
      exact List.mem_append_right _ (List.mem_map.mpr ⟨g,hg,by simpa [eq] using value⟩)
  have optimal : undominated new startWords := by
    by_contra bad
    obtain ⟨q,ql,qg⟩ := shorten zero (by decide +kernel) newGoal bad
    exact Nat.find_min possible (newLen ▸ ql) ⟨q,rfl,qg⟩
  exact ⟨nodes,by rw [perm.length_eq,size,len]; omega,sort_order tree,legalN,
    run.clean optimal taggedRaw exactRaw,y,yn,value⟩

end Live3210.Ordered

namespace Live3210.Ordered

structure Enables (g : Gate) (s t : Finset Signal) : Prop where
  left : g.left∈s
  right : g.right∈s
  different : g.left.1≠g.right.1
  notZero : g.output.1≠0
  notFull : g.output.1≠full
  novel : ∀ v∈s, ¬Dominated g.output.1 v.1
  notRaw : ∀ v∈sources, ¬Dominated g.output.1 v
  size : s.card≤t.card+1
  update : ∃ keep : Finset Signal, keep⊆{g.left,g.right} ∧
    t=insert g.output (((s.erase g.left).erase g.right) ∪ keep)

inductive Route : List Gate → Finset Signal → Finset Signal → Prop where
  | stop (s) : Route [] s s
  | next {g gs s t u} (ok : Enables g s t) (tail : Route gs t u) : Route (g::gs) s u

def separated (s : Finset Signal) := separates (s.image Prod.fst)

theorem Enables.back {g s t} (m : Enables g s t) (enough : separated t) : separated s := by
  intro i j
  obtain ⟨w,hm,good⟩ := enough i j
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨keep,sub,eq⟩ := m.update
  rw [eq] at hv
  rcases Finset.mem_insert.mp hv with rfl|old
  · rcases descend g.op g.left.1 g.right.1 i j good with l|r
    · exact ⟨_,Finset.mem_image_of_mem _ m.left,l⟩
    · exact ⟨_,Finset.mem_image_of_mem _ m.right,r⟩
  · refine ⟨v.1,Finset.mem_image_of_mem _ ?_,good⟩
    rcases Finset.mem_union.mp old with stay|haveK
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp stay).2).2
    · have e : v=g.left ∨ v=g.right := by simpa using sub haveK
      exact e.elim (fun h => h ▸ m.left) (fun h => h ▸ m.right)

theorem Route.back {gs s t} (path : Route gs s t) (ok : separated t) : separated s := by
  induction path with
  | stop => exact ok
  | next m _ ih => exact m.back (ih ok)
theorem Route.budget {gs s t} (path : Route gs s t) : s.card ≤ t.card+gs.length := by
  induction path with
  | stop => simp
  | next m _ ih => have := m.size; simp only [List.length_cons]; omega

def supported (pool : List Signal) (d : Finset Signal) :=
  ∀ v∈d, v∈pool ∧ v.1≠0 ∧ v.1≠full
def includesBase (pool : List Signal) := ∀ x∈sources, ∃v∈pool, v.1=x

theorem prune {gs pool} (ok : legal pool gs) (optimal : clean gs pool)
    (bounds : safe pool) (rawIn : includesBase pool) (d : Finset Signal)
    (finish : supported (built pool gs) d) :
    ∃ start kept, supported pool start ∧ kept.Sublist gs ∧ Route kept start d := by
  classical
  induction gs generalizing pool with
  | nil =>
    exact ⟨d,[],by simpa [built] using finish,List.Sublist.refl _,.stop _⟩
  | cons g gs ih =>
    have ga := ok.1 g.left (by simp [Gate.inputs])
    have gb := ok.1 g.right (by simp [Gate.inputs])
    have lower := bounds g.left ga
    have upper := bounds g.right gb
    have wB : g.output.1<2^24 := combine_bound g.op lower upper
    have nextB : safe (g.output::pool) := fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ wB) (bounds x)
    have nextRaw : includesBase (g.output::pool) := by
      intro x hx
      obtain ⟨v,hv,eq⟩ := rawIn x hx
      exact ⟨v,List.mem_cons_of_mem _ hv,eq⟩
    have nextF : supported (built (g.output::pool) gs) d := by
      intro x hx
      exact ⟨built_cons.mpr (finish x hx).1,(finish x hx).2⟩
    obtain ⟨t,keep,fit,sub,rest⟩ := ih ok.2 optimal.2 nextB nextRaw nextF
    have other (x) (hx : x∈t) (ne : x≠g.output) : x∈pool := (List.mem_cons.mp (fit x hx).1).resolve_left ne
    by_cases wanted : g.output∈t
    · let s := insert g.left (insert g.right (t.erase g.output))
      have new (v) (hv : v∈pool) : g.output.1≠v.1 := by
        intro e
        exact optimal.1 v hv (e ▸ Dominated.refl v.1)
      have wNZ := (fit g.output wanted).2.1
      have wNF := (fit g.output wanted).2.2
      have leftGood := left_nontrivial g.op upper wNZ wNF (new _ gb)
      have rightGood : g.right.1≠0 ∧ g.right.1≠full := by
        apply left_nontrivial g.op lower <;> rw [combine_comm g.op g.right.1 g.left.1]
        · exact wNZ
        · exact wNF
        · exact new _ ga
      have neq : g.left.1≠g.right.1 := by
        intro e
        apply new _ gb
        simp [Gate.output,combine,e]
      have small : supported pool s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl|h
        · exact ⟨ga,leftGood⟩
        rcases Finset.mem_insert.mp h with rfl|h
        · exact ⟨gb,rightGood⟩
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp h
        exact ⟨other x mem ne,(fit x mem).2⟩
      refine ⟨s,g::keep,small,sub.cons_cons g,.next ?_ rest⟩
      refine ⟨by simp [s],by simp [s],neq,wNZ,wNF,(fun v hv => optimal.1 v (small v hv).1),?_,?_,?_⟩
      · intro w hw
        obtain ⟨v,hv,rfl⟩ := rawIn w hw
        exact optimal.1 v hv
      · have a := Finset.card_insert_le g.left (insert g.right (t.erase g.output))
        have b := Finset.card_insert_le g.right (t.erase g.output)
        have c := Finset.card_erase_add_one wanted
        change (insert g.left (insert g.right (t.erase g.output))).card ≤ t.card+1
        omega
      · refine ⟨t ∩ {g.left,g.right},Finset.inter_subset_right,?_⟩
        ext v
        by_cases h₁ : v=g.left <;> by_cases h₂ : v=g.right <;> by_cases h₃ : v=g.output <;>
          simp_all [s]
    · exact ⟨t,keep,(fun x hx => ⟨other x hx (fun e => wanted (e ▸ hx)),(fit x hx).2⟩),sub.cons g,rest⟩

theorem clean.order_ne {gs pool} (ok : clean gs pool) :
    gs.Pairwise (fun g h => g.output.1≠h.output.1) := by
  have exclude {ns : List Gate} {s} (h : clean ns s) (v) (mem : v∈s) (g) (hg : g∈ns) :
      g.output.1≠v.1 := by
    induction ns generalizing s with
    | nil => simp at hg
    | cons first ns ih =>
      rcases List.mem_cons.mp hg with rfl|later
      · exact fun e => h.1 _ mem (e ▸ Dominated.refl v.1)
      · exact ih h.2 (List.mem_cons_of_mem _ mem) later
  induction gs generalizing pool with
  | nil => exact List.Pairwise.nil
  | cons g gs ih =>
    exact List.pairwise_cons.mpr ⟨fun f hf => Ne.symm (exclude ok.2 _ List.mem_cons_self f hf),ih ok.2⟩

def tagged (s : Finset Nat) : Finset Signal := s.image (fun w => (w,0))
def strict (a b : Gate) := a.output.2 < b.output.2 ∨ (a.output.2=b.output.2 ∧ a.output.1<b.output.1)

theorem route_for_target {p : List Instruction} (c : Nat) (budget : p.length≤14)
    (hit : (4095,c)∈p.foldl scored initialScored) :
    ∃ s kept y, (s=tagged required ∨ s=tagged raw) ∧ kept.length≤14 ∧
      kept.Pairwise strict ∧ y.1=4095 ∧ Route kept s {y} := by
  obtain ⟨gs,size,order,ok,opt,y,hy,val⟩ := sorted_minimum c budget hit
  have bounds : safe taggedRaw := by unfold safe; decide +kernel
  have rawIn : includesBase taggedRaw := by unfold includesBase; decide +kernel
  have endFit : supported (built taggedRaw gs) {y} := by
    intro v hv
    obtain rfl := Finset.mem_singleton.mp hv
    exact ⟨hy,by omega,by rw [val]; decide⟩
  obtain ⟨s,kept,fit,sub,path⟩ := prune ok opt bounds rawIn {y} endFit
  have boundedOutputs {ns pool} (h : legal pool ns) (safeS : safe pool) (g) (mem : g∈ns) :
      g.output.1<16777216 := by
    induction ns generalizing pool with
    | nil => simp at mem
    | cons first ns ih =>
      have b : first.output.1<2^24 := combine_bound first.op
        (safeS _ (h.1 first.left (by simp [Gate.inputs]))) (safeS _ (h.1 first.right (by simp [Gate.inputs])))
      rcases List.mem_cons.mp mem with rfl|later
      · exact b
      · exact ih h.2 (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ b) (safeS x)) later
  have ranks : gs.Pairwise strict := by
    have ne := clean.order_ne opt
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    have a := List.pairwise_iff_getElem.mp order i j hi hj ij
    have b := List.pairwise_iff_getElem.mp ne i j hi hj ij
    have c₁ := boundedOutputs ok bounds _ (List.getElem_mem hi)
    have c₂ := boundedOutputs ok bounds _ (List.getElem_mem hj)
    change 16777216*(gs[i].output.2)+gs[i].output.1 ≤ 16777216*(gs[j].output.2)+gs[j].output.1 at a
    unfold strict
    omega
  have endSep : separated {y} := by simpa only [separated,Finset.image_singleton,val] using target_sep
  have startSep := path.back endSep
  have sourceFacts : ∀ v∈taggedRaw, v.1≠0 → v.1≠full → v.1∈raw ∧ v.2=0 := by decide +kernel
  have small : s.image Prod.fst ⊆ raw := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨pool,nz,nf⟩ := fit x hx
    exact (sourceFacts x pool nz nf).1
  have lift : s = tagged (s.image Prod.fst) := by
    ext x
    constructor
    · intro hx
      obtain ⟨pool,nz,nf⟩ := fit x hx
      exact Finset.mem_image.mpr ⟨x.1,Finset.mem_image_of_mem _ hx,Prod.ext rfl (sourceFacts x pool nz nf).2.symm⟩
    · intro hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨x,xx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨pool,nz,nf⟩ := fit x xx
      have e : (x.1,0)=x := Prod.ext rfl (sourceFacts x pool nz nf).2.symm
      exact e ▸ xx
  rcases start_set small startSep with nine|ten
  · exact ⟨s,kept,y,Or.inl (lift.trans (congrArg tagged nine)),sub.length_le.trans size,ranks.sublist sub,val,path⟩
  · exact ⟨s,kept,y,Or.inr (lift.trans (congrArg tagged ten)),sub.length_le.trans size,ranks.sublist sub,val,path⟩

end Live3210.Ordered

namespace Live3210.Packed

def sign (w : Nat) := w ^^^ 0xfff000
def spread (a : Nat) :=
  let a := (a ||| (a <<< 88)) &&& 0xf0000000000000000000000ff
  let a := (a ||| (a <<< 44)) &&& 0xf00000000000f00000000000f
  let a := (a ||| (a <<< 22)) &&& 0x3000003000003000003000003000003
  (a ||| (a <<< 11)) &&& 0x1001001001001001001001001001001001
def cover (w : Nat) := spread (w &&& 4095) * ((w >>> 12) ^^^ 4095)
def dom (w v : Nat) := w &&& v == w

def spreadRec : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, p => (if p.testBit 0 then 1 else 0) + 4096 * spreadRec k (p/2)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem spreadTable : ∀ p : Fin 4096, spread p.val = spreadRec 12 p.val ∧ spread p.val * 4095 < 2^144 := by
  decide +kernel

private theorem blockBits (s t : Nat) (low : s<4096) (i j : Nat) (hj : j<12) :
    (s+4096*t).testBit (12*i+j) = if i=0 then s.testBit j else t.testBit (12*(i-1)+j) := by
  cases i with
  | zero =>
    have h := Nat.testBit_mod_two_pow (s+4096*t) 12 j
    change ((s+4096*t)%4096).testBit j = _ at h
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt low] at h
    simpa [hj] using h.symm
  | succ i =>
    rw [show 12*(i+1)+j = (12*i+j)+12 by omega, Nat.testBit_add]
    change ((s+4096*t)/4096).testBit _ = _
    rw [Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt low]
    simp

private theorem spreadBits (k p z i j : Nat) (hz : z<4096) (hi : i<k) (hj : j<12) :
    (spreadRec k p*z).testBit (12*i+j) = (p.testBit i && z.testBit j) := by
  induction k generalizing p i with
  | zero => omega
  | succ k ih =>
    let s := if p.testBit 0 then z else 0
    have sl : s<4096 := by dsimp [s]; split <;> omega
    have eqn : spreadRec (k+1) p * z = s + 4096*(spreadRec k (p/2)*z) := by
      simp only [spreadRec,Nat.add_mul,Nat.mul_assoc,s]
      split <;> simp
    rw [eqn,blockBits _ _ sl i j hj]
    cases i with
    | zero => cases b : p.testBit 0 <;> simp [s,b]
    | succ i => simp [ih (p/2) i (by omega),Nat.testBit_div_two]

private theorem maskLo (i : Fin 12) : (4095 : Nat).testBit i.val = true := by
  change (2^12-1 : Nat).testBit i.val = true
  rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true i.isLt

private theorem hiBound {w : Nat} (hw : w<2^24) : (w >>> 12) ^^^ 4095 < 2^12 := by
  apply Nat.xor_lt_two_pow _ (by decide)
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem product_bits (a z : Nat) (hz : z<4096) (i j : Fin 12) :
    (spread (a &&& 4095)*z).testBit (12*i.val+j.val) = (a.testBit i.val && z.testBit j.val) := by
  let p : Fin 4096 := ⟨a &&& 4095,Nat.lt_succ_of_le Nat.and_le_right⟩
  change (spread p.val*z).testBit _ = _
  rw [(spreadTable p).1,spreadBits _ _ _ _ _ hz i.isLt j.isLt]
  simp [p,maskLo]

theorem product_bound (a z : Nat) (hz : z<4096) : spread (a &&& 4095)*z < 2^144 := by
  let p : Fin 4096 := ⟨a &&& 4095,Nat.lt_succ_of_le Nat.and_le_right⟩
  exact (Nat.mul_le_mul_left (spread p.val) (Nat.le_of_lt_succ hz)).trans_lt (spreadTable p).2

theorem cover_bound {w : Nat} (hw : w<2^24) : cover w < 2^144 := by
  let p : Fin 4096 := ⟨w &&& 4095,Nat.lt_succ_of_le Nat.and_le_right⟩
  exact (Nat.mul_le_mul_left (spread p.val) (Nat.le_of_lt_succ (hiBound hw))).trans_lt (spreadTable p).2

theorem cover_bits {w : Nat} (hw : w<2^24) (i j : Fin 12) :
    (cover w).testBit (12*i.val+j.val) = true ↔ covers w i j := by
  let p : Fin 4096 := ⟨w &&& 4095,Nat.lt_succ_of_le Nat.and_le_right⟩
  change (spread p.val * _).testBit _ = true ↔ _
  rw [(spreadTable p).1, spreadBits _ _ _ _ _ (hiBound hw) i.isLt j.isLt]
  simp [p,Nat.testBit_xor,Nat.testBit_and,Nat.testBit_shiftRight,maskLo,covers]

theorem dom_sound {w v : Nat} (h : dom (sign w) (sign v) = true) : Dominated w v := by
  have eq : sign w &&& sign v = sign w := by simpa [dom] using h
  have lo : ∀ k : Fin 12, (0xfff000 : Nat).testBit k.val = false := by decide +kernel
  have hi : ∀ k : Fin 12, (0xfff000 : Nat).testBit (12+k.val) = true := by decide +kernel
  constructor
  · intro i wi
    have := congrArg (fun x : Nat => x.testBit i.val) eq
    simpa [sign,Nat.testBit_and,Nat.testBit_xor,lo,wi] using this
  · intro i vi
    have := congrArg (fun x : Nat => x.testBit (12+i.val)) eq
    simpa [sign,Nat.testBit_and,Nat.testBit_xor,hi,vi] using this

theorem cover_all {ws : List Nat} (bounded : ∀ w∈ws, w<2^24) (sep : separates ws.toFinset) :
    ws.foldl (fun acc w => acc ||| cover w) 0 = 2^144-1 := by
  have foldBit (vs : List Nat) (a n : Nat) :
      (vs.foldl (fun acc w => acc ||| cover w) a).testBit n = true ↔
        a.testBit n = true ∨ ∃ w∈vs, (cover w).testBit n = true := by
    induction vs generalizing a with
    | nil => simp
    | cons v vs ih =>
      simp only [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true,List.mem_cons]
      aesop
  have foldBound (vs : List Nat) (hvs : ∀ v∈vs, v<2^24) (a : Nat) (ha : a<2^144) :
      vs.foldl (fun acc w => acc ||| cover w) a < 2^144 := by
    induction vs generalizing a with
    | nil => exact ha
    | cons v vs ih =>
      exact ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) _ (Nat.or_lt_two_pow ha (cover_bound (hvs v List.mem_cons_self)))
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hn : n<144
  · simp only [hn,decide_true]
    let i : Fin 12 := ⟨n/12,by omega⟩
    let j : Fin 12 := ⟨n % 12,Nat.mod_lt _ (by decide)⟩
    have hn' : 12*i.val+j.val=n := by dsimp [i,j]; omega
    obtain ⟨w,mem,cov⟩ := sep i j
    have hw : w ∈ ws := List.mem_toFinset.mp mem
    exact (foldBit ws 0 n).mpr (Or.inr ⟨w,hw,hn' ▸ (cover_bits (bounded w hw) i j).mpr cov⟩)
  · simp only [hn,decide_false]
    exact Nat.testBit_lt_two_pow ((foldBound ws bounded 0 (by decide)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))

theorem fold_or_append (xs ys : List Nat) (a : Nat) :
    (xs ++ ys).foldl (fun acc w => acc ||| cover w) a =
    (xs.foldl (fun acc w => acc ||| cover w) a) ||| ys.foldl (fun acc w => acc ||| cover w) 0 := by
  have add (ws : List Nat) (u v : Nat) :
      ws.foldl (fun acc w => acc ||| cover w) (u ||| v) =
        u ||| ws.foldl (fun acc w => acc ||| cover w) v := by
    induction ws generalizing v with
    | nil => rfl
    | cons w ws ih => simp only [List.foldl_cons,Nat.or_assoc,ih]
  rw [List.foldl_append]
  simpa using add ys (xs.foldl (fun acc w => acc ||| cover w) a) 0

end Live3210.Packed

namespace Live3210.Search

variable {α : Type}
def scanRight (f : α → α → List α → Nat) (x : α) (pre seen : List α) : List α → Nat
  | [] => 0
  | y::ys => f x y (pre++seen++ys) + scanRight f x pre (y::seen) ys

def scanPairs (f : α → α → List α → Nat) (pre : List α) : List α → Nat
  | [] => 0
  | x::xs => scanRight f x pre [] xs + scanPairs f (x::pre) xs

private theorem scanRight_pos (f : α → α → List α → Nat) (x y : α)
    (pre seen ys : List α) (hy : y∈ys)
    (hit : ∀ rest, (pre++seen++ys).Perm (y::rest) → 0<f x y rest) :
    0<scanRight f x pre seen ys := by
  induction ys generalizing seen with
  | nil => contradiction
  | cons z zs ih =>
    rw [scanRight]
    have rearr : (pre++seen++z::zs).Perm (z::(pre++seen++zs)) := List.perm_middle
    rcases List.mem_cons.mp hy with rfl|later
    · have := hit _ rearr; omega
    · apply Nat.add_pos_right
      apply ih (z::seen) later
      intro rest perm
      apply hit
      have move : (pre++(z::seen)++zs).Perm (z::(pre++seen++zs)) := by
        simp [List.append_assoc]
      exact rearr.trans (move.symm.trans perm)

theorem scanPairs_pos [DecidableEq α] (f : α → α → List α → Nat) (a b : α)
    (pre xs : List α) (ha : a∈xs) (hb : b∈xs) (ne : a≠b)
    (hit : ∀ x y rest, (x=a ∧ y=b ∨ x=b ∧ y=a) →
      (pre++xs).Perm (x::y::rest) → 0<f x y rest) :
    0<scanPairs f pre xs := by
  induction xs generalizing pre with
  | nil => contradiction
  | cons z zs ih =>
    rw [scanPairs]
    have move : (pre++z::zs).Perm (z::(pre++zs)) := List.perm_middle
    by_cases za : z=a
    · subst a
      have later := (List.mem_cons.mp hb).resolve_left ne.symm
      have h := scanRight_pos f z b pre [] zs later (by
        intro rest perm
        exact hit _ _ _ (Or.inl ⟨rfl,rfl⟩) (move.trans (List.Perm.cons z (by simpa using perm))))
      omega
    by_cases zb : z=b
    · subst b
      have later := (List.mem_cons.mp ha).resolve_left ne
      have h := scanRight_pos f z a pre [] zs later (by
        intro rest perm
        exact hit _ _ _ (Or.inr ⟨rfl,rfl⟩) (move.trans (List.Perm.cons z (by simpa using perm))))
      omega
    · apply Nat.add_pos_right
      apply ih (z::pre) ((List.mem_cons.mp ha).resolve_left (Ne.symm za))
        ((List.mem_cons.mp hb).resolve_left (Ne.symm zb))
      intro x y rest order eq
      exact hit x y rest order (move.trans eq)

private theorem scanRight_map {β : Type} (c : α → β) (f : β → β → List β → Nat)
    (x : α) (pre seen ys : List α) :
    scanRight f (c x) (pre.map c) (seen.map c) (ys.map c) =
      scanRight (fun x y rest => f (c x) (c y) (rest.map c)) x pre seen ys := by
  induction ys generalizing seen with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons,scanRight,List.map_append]
    rw [← List.map_cons,ih]

theorem scanPairs_map {β : Type} (c : α → β) (f : β → β → List β → Nat)
    (pre xs : List α) :
    scanPairs f (pre.map c) (xs.map c) =
      scanPairs (fun x y rest => f (c x) (c y) (rest.map c)) pre xs := by
  induction xs generalizing pre with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,scanPairs]
    rw [← List.map_nil (f:=c),scanRight_map,←List.map_cons,ih]

end Live3210.Search
namespace Live3210.Search
open Ordered

structure Wire where
  value : Nat
  cells : Nat
  signed : Nat
  depth : Nat

def pack (v : Signal) : Wire := ⟨v.1,Packed.cover v.1,Packed.sign v.1,v.2⟩
def wordMask (ws : List Wire) := ws.foldl (fun a x => a ||| x.cells) 0
def rawSigned := inputs.map Packed.sign
def blocked (all : List Wire) (w : Nat) : Bool :=
  let sig := Packed.sign w
  w &&& 4095 == 0 || w >>> 12 == 4095 ||
    rawSigned.any (Packed.dom sig) || all.any (fun a => Packed.dom sig a.signed)

inductive Choice where
  | none | left | right | both
  deriving DecidableEq

def Choice.keep {α : Type} (x y : α) : Choice → List α
  | .none => []
  | .left => [x]
  | .right => [y]
  | .both => [x,y]

def Choice.mask (x y : Wire) : Choice → Nat
  | .none => 0
  | .left => x.cells
  | .right => y.cells
  | .both => x.cells ||| y.cells

def Choice.count : Choice → Nat
  | .none => 0
  | .left => 1
  | .right => 1
  | .both => 2

abbrev Callback := List Wire → Nat → Nat → Nat

def branch (f : Callback) (z x y : Wire) (others : List Wire) (cards d combined : Nat) (c : Choice) :=
  if cards+c.count ≤ d && (combined ||| c.mask x y) == 2^144-1 then
    f (z :: (c.keep x y ++ others)) z.depth z.value else 0

def trial (f : Callback) (all others : List Wire) (cards d limit lw : Nat) (x y : Wire)
    (cov w level : Nat) :=
  if (level == limit && w ≤ lw) || blocked all w then 0 else
  let z := pack (w,level)
  let run := branch f z x y others cards d (z.cells ||| cov)
  run .none + run .left + run .right + run .both

def options (f : Callback) (all others : List Wire) (cards d limit lw : Nat) (x y : Wire) :=
  let level := 1 + max x.depth y.depth
  if level < limit then 0 else
  let t := trial f all others cards d limit lw x y (wordMask others)
  t (x.value &&& y.value) level + t (x.value ||| y.value) level

def next (f : Callback) (s : List Wire) (d limit lw : Nat) :=
  scanPairs (fun x y rest => options f s rest (s.length-1) d limit lw x y) [] s

private theorem noPositive {w : Nat} (eq : w &&& 4095 = 0) : Dominated w 0 := by
  constructor
  · intro i on
    have h := congrArg (fun x : Nat => x.testBit i.val) eq
    have mask : (4095 : Nat).testBit i.val = true := by
      change (2^12-1 : Nat).testBit _ = true
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true i.isLt
    simp [mask,on] at h
  · simp

private theorem allNegative {w : Nat} (eq : w >>> 12 = 4095) : Dominated w full := by
  constructor
  · intro i _
    change (2^24-1 : Nat).testBit _ = true
    rw [Nat.testBit_two_pow_sub_one]; apply decide_eq_true; omega
  · intro j _
    have mask : (4095 : Nat).testBit j.val = true := by
      change (2^12-1 : Nat).testBit _ = true
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true j.isLt
    simpa [mask] using congrArg (fun x : Nat => x.testBit j.val) eq

theorem notBlocked {g : Gate} {ws : List Signal} {t} (m : Enables g ws.toFinset t) :
    blocked (ws.map pack) g.output.1 = false := by
  have nz (eq : g.output.1 &&& 4095 = 0) : False :=
    m.notRaw 0 (by simp [sources]) (noPositive eq)
  have nf (eq : g.output.1 >>> 12 = 4095) : False :=
    m.notRaw full (by simp [sources]) (allNegative eq)
  have base : rawSigned.any (Packed.dom (Packed.sign g.output.1)) = false := by
    apply List.any_eq_false.mpr
    intro v hv yes
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact m.notRaw w (by simp [sources,raw,hw]) (Packed.dom_sound yes)
  have seen : (ws.map pack).any (fun a => Packed.dom (Packed.sign g.output.1) a.signed) = false := by
    apply List.any_eq_false.mpr
    intro v hv yes
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact m.novel w (List.mem_toFinset.mpr hw) (Packed.dom_sound yes)
  simpa [blocked,base,seen] using And.intro nz nf

theorem pickKeep {g : Gate} {ws : List Signal} {t} (m : Enables g ws.toFinset t)
    (nd : ws.Nodup) (x y : Signal) (rest : List Signal)
    (order : x=g.left ∧ y=g.right ∨ x=g.right ∧ y=g.left)
    (perm : ws.Perm (x::y::rest)) :
    ∃ c : Choice, (g.output :: (c.keep x y ++ rest)).toFinset = t ∧
      (g.output :: (c.keep x y ++ rest)).Nodup := by
  obtain ⟨retain,sub,update⟩ := m.update
  have was : ws.toFinset = (x::y::rest).toFinset := by
    ext v; simp only [List.mem_toFinset]; exact perm.mem_iff
  have good := perm.nodup nd
  simp only [List.nodup_cons,List.mem_cons,not_or] at good
  obtain ⟨⟨xy,xr⟩,yr,rd⟩ := good
  have retained : retain⊆{x,y} := by rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simpa [Finset.pair_comm] using sub
  have remaining : (ws.toFinset.erase g.left).erase g.right = rest.toFinset := by
    rw [was]; ext v
    simp only [Finset.mem_erase,List.mem_toFinset,List.mem_cons]
    rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> aesop
  have fresh : g.output∉x::y::rest := by
    intro mem
    exact m.novel g.output (List.mem_toFinset.mpr (perm.mem_iff.mpr mem)) (Dominated.refl _)
  simp only [List.mem_cons,not_or] at fresh
  have finish (c : Choice) (hc : (c.keep x y).toFinset=retain)
      (hn : (g.output :: (c.keep x y ++ rest)).Nodup) :
      (g.output :: (c.keep x y ++ rest)).toFinset=t ∧ (g.output :: (c.keep x y ++ rest)).Nodup := by
    refine ⟨?_,hn⟩
    simp [update,remaining,hc,Finset.union_comm]
  have h (v) (hv : v∈retain) : v=x ∨ v=y := by simpa using retained hv
  have hs (v) : v∈retain ↔ (v=x ∧ x∈retain) ∨ (v=y ∧ y∈retain) := by
    constructor
    · intro hv; rcases h v hv with rfl|rfl
      · exact Or.inl ⟨rfl,hv⟩
      · exact Or.inr ⟨rfl,hv⟩
    · rintro (⟨rfl,hv⟩|⟨rfl,hv⟩) <;> exact hv
  by_cases a : x∈retain <;> by_cases b : y∈retain
  · refine ⟨.both,finish _ ?_ ?_⟩
    · apply Finset.ext; intro v; rw [hs]; simp [Choice.keep,a,b]
    · simpa [Choice.keep,List.nodup_cons,xy,xr,yr,rd] using fresh
  · refine ⟨.left,finish _ ?_ ?_⟩
    · apply Finset.ext; intro v; rw [hs]; simp [Choice.keep,a,b]
    · simp [Choice.keep,List.nodup_cons,xr,rd,fresh]
  · refine ⟨.right,finish _ ?_ ?_⟩
    · apply Finset.ext; intro v; rw [hs]; simp [Choice.keep,a,b]
    · simp [Choice.keep,List.nodup_cons,yr,rd,fresh]
  · refine ⟨.none,finish _ ?_ ?_⟩
    · apply Finset.ext; intro v; rw [hs]; simp [Choice.keep,a,b]
    · simp [Choice.keep,List.nodup_cons,rd,fresh]

theorem wordMask_acc (ws : List Wire) (a : Nat) :
    ws.foldl (fun b x => b ||| x.cells) a = a ||| wordMask ws := by
  have add (vs : List Wire) (u v : Nat) :
      vs.foldl (fun b x => b ||| x.cells) (u|||v) = u ||| vs.foldl (fun b x => b ||| x.cells) v := by
    induction vs generalizing v with
    | nil => rfl
    | cons w ws ih => simp only [List.foldl_cons,Nat.or_assoc,ih]
  simpa [wordMask] using add ws a 0

theorem wordMask_cons (w : Wire) (ws : List Wire) :
    wordMask (w::ws) = w.cells ||| wordMask ws := by
  change ws.foldl (fun b x => b ||| x.cells) (0 ||| w.cells) = _
  rw [Nat.zero_or,wordMask_acc]

theorem wordMask_full (ws : List Signal) (ok : safe ws) (sep : separated ws.toFinset) :
    wordMask (ws.map pack) = 2^144-1 := by
  have bound : ∀ w∈ws.map Prod.fst, w<2^24 := by
    intro w hw; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw; exact ok v hv
  have eq : (ws.map Prod.fst).toFinset = ws.toFinset.image Prod.fst := by
    apply Finset.ext; intro v; simp
  have good : separates (ws.map Prod.fst).toFinset := eq ▸ sep
  exact (by simpa [wordMask,List.foldl_map,pack,Function.comp_def] using Packed.cover_all bound good)

def later (v : Signal) (limit lw : Nat) := limit<v.2 ∨ (limit=v.2 ∧ lw<v.1)

private theorem trial_selected (f : Callback) {g : Gate} {ws : List Signal} {t}
    (m : Enables g ws.toFinset t) (nd : ws.Nodup) (x y : Signal) (rest : List Signal)
    (order : x=g.left ∧ y=g.right ∨ x=g.right ∧ y=g.left) (perm : ws.Perm (x::y::rest))
    (d limit lw : Nat) (ordered : later g.output limit lw) (budget : t.card≤d)
    (good : separated t) (bound : ∀ v∈t, v.1<2^24)
    (advance : ∀ vs : List Signal, vs.toFinset=t → vs.Nodup → 0<f (vs.map pack) g.output.2 g.output.1) :
    0<trial f (ws.map pack) (rest.map pack) (ws.length-1) d limit lw (pack x) (pack y)
      (wordMask (rest.map pack)) g.output.1 g.output.2 := by
  obtain ⟨c,represent,distinct⟩ := pickKeep m nd x y rest order perm
  let vs := g.output::(c.keep x y++rest)
  have fullMask := wordMask_full vs (fun v hv => bound v (represent ▸ List.mem_toFinset.mpr hv)) (represent ▸ good)
  have lengths := perm.length_eq
  have keptLen : (c.keep x y).length=c.count := by cases c <;> rfl
  have card := List.toFinset_card_of_nodup distinct
  rw [represent] at card
  simp only [List.length_cons,List.length_append,keptLen] at card lengths
  have small : ws.length-1+c.count≤d := by omega
  have leftComm (a b e : Nat) : a ||| (b ||| e) = b ||| (a ||| e) := by
    rw [←Nat.or_assoc,Nat.or_comm a b,Nat.or_assoc]
  have mask : ((pack g.output).cells ||| wordMask (rest.map pack)) ||| c.mask (pack x) (pack y) = 2^144-1 := by
    cases c <;> simpa [vs,Choice.keep,Choice.mask,wordMask_cons,Nat.or_assoc,Nat.or_comm,leftComm] using fullMask
  have mapped : (c.keep x y).map pack = c.keep (pack x) (pack y) := by cases c <;> rfl
  have keyok : ((g.output.2 == limit) && decide (g.output.1 ≤ lw)) = false := by
    simp only [Bool.and_eq_false_iff,beq_eq_false_iff_ne,decide_eq_false_iff_not]
    unfold later at ordered
    omega
  rw [trial,notBlocked m,keyok]
  simp only [Bool.false_or,Bool.false_eq_true,↓reduceIte]
  have used : 0<branch f (pack g.output) (pack x) (pack y) (rest.map pack) (ws.length-1) d
      ((pack g.output).cells ||| wordMask (rest.map pack)) c := by
    rw [branch,ite_eq_left (by simp [small,mask])]
    simpa [vs,List.map_append,mapped,pack] using advance vs represent distinct
  rw [show (g.output.1,g.output.2)=g.output by rfl]
  cases c <;> omega

theorem next_pos (f : Callback) {g : Gate} {ws : List Signal} {t}
    (m : Enables g ws.toFinset t) (nd : ws.Nodup)
    (d limit lw : Nat) (ordered : later g.output limit lw) (budget : t.card≤d)
    (good : separated t) (bound : ∀ v∈t, v.1<2^24)
    (advance : ∀ vs : List Signal, vs.toFinset=t → vs.Nodup → 0<f (vs.map pack) g.output.2 g.output.1) :
    0<next f (ws.map pack) d limit lw := by
  unfold next
  rw [←List.map_nil (f:=pack),scanPairs_map,List.length_map]
  apply scanPairs_pos _ g.left g.right [] ws (List.mem_toFinset.mp m.left) (List.mem_toFinset.mp m.right)
    (fun eq => m.different (congrArg Prod.fst eq))
  intro x y rest order perm
  simp only [List.nil_append] at perm
  have yes := trial_selected f m nd x y rest order perm d limit lw ordered budget good bound advance
  have lev : 1+max (pack x).depth (pack y).depth = g.output.2 := by
    rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [Gate.output,pack,Nat.max_comm]
  have high : ¬g.output.2<limit := by unfold later at ordered; omega
  unfold options
  rw [lev,ite_eq_right high]
  have word : g.output.1 = combine g.op x.1 y.1 := by
    rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rfl
    · cases op : g.op <;> simp [Gate.output,op,combine,Nat.and_comm,Nat.or_comm]
  cases op : g.op
  · rw [op] at word
    rw [show combine false x.1 y.1=x.1|||y.1 by rfl] at word
    exact Nat.add_pos_right _ (word ▸ yes)
  · rw [op] at word
    rw [show combine true x.1 y.1=x.1&&&y.1 by rfl] at word
    exact Nat.add_pos_left (word ▸ yes) _

def survives : Nat → Nat → List Wire → Nat → Nat → Nat
  | 0,_,_,_,_ => 1
  | h+1,d,ws,limit,lw =>
    if ws.any (fun w => w.value == 4095) then 1
    else next (survives h (d-1)) ws d limit lw

private theorem step_bound {g : Gate} {s t} (m : Enables g s t)
    (bound : ∀ v∈s, v.1<2^24) : ∀ v∈t, v.1<2^24 := by
  have ha := bound _ m.left
  have hb := bound _ m.right
  have out : g.output.1<2^24 := by
    simp only [Gate.output,combine]
    split
    · exact Nat.and_lt_two_pow _ hb
    · exact Nat.or_lt_two_pow ha hb
  obtain ⟨k,sub,rfl⟩ := m.update
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl|hold
  · exact out
  · rcases Finset.mem_union.mp hold with other|kept
    · exact bound _ (Finset.mem_erase.mp (Finset.mem_erase.mp other).2).2
    · rcases (show v=g.left ∨ v=g.right by simpa using sub kept) with rfl|rfl <;> assumption

private theorem empty_route {s t : Finset Signal} (path : Route [] s t) : s=t := by
  cases path; rfl

theorem cannot_prune (h d : Nat) (ws : List Signal) (gs : List Gate) (y : Signal)
    (limit lw : Nat) (val : y.1=4095) (route : Route gs ws.toFinset {y})
    (nd : ws.Nodup) (bound : safe ws) (cost : gs.length≤d)
    (ord : gs.Pairwise strict) (afterKey : ∀ g∈gs, later g.output limit lw) :
    0<survives h d (ws.map pack) limit lw := by
  induction h generalizing d gs ws limit lw with
  | zero => simp [survives]
  | succ h ih =>
    rw [survives]
    split
    · decide
    case isFalse miss =>
      cases gs with
      | nil =>
        have equal := empty_route route
        have mem : y∈ws := List.mem_toFinset.mp (equal ▸ Finset.mem_singleton_self _)
        apply False.elim
        exact miss (List.any_eq_true.mpr ⟨pack y,List.mem_map_of_mem mem,by simp [pack,val]⟩)
      | cons g gs =>
        cases route with
        | next m tail =>
          have last : separated {y} := by simpa only [separated,Finset.image_singleton,val] using target_sep
          have tSep := tail.back last
          have tCard := tail.budget
          simp only [Finset.card_singleton] at tCard
          simp only [List.length_cons] at cost
          have pair := List.pairwise_cons.mp ord
          have newBound := step_bound m (fun v hv => bound v (List.mem_toFinset.mp hv))
          apply next_pos _ m nd d limit lw (afterKey g List.mem_cons_self) (by omega) tSep newBound
          intro vs rep dis
          apply ih (d-1) vs gs g.output.2 g.output.1 (rep ▸ tail) dis
            (fun v hv => newBound v (rep ▸ List.mem_toFinset.mpr hv)) (by omega) pair.2
          intro k hk
          rcases pair.1 k hk with lt|⟨same,lt⟩
          · exact Or.inl lt
          · exact Or.inr ⟨same,lt⟩

def starts (n : Nat) : List Signal := (inputs.take n).map (fun w => (w,0))
def run (h : Nat) :=
  survives h 14 ((starts 9).map pack) 0 0 + survives h 14 ((starts 10).map pack) 0 0

theorem program_survives (h : Nat) (p : List Instruction) (cost : Nat) (len : p.length≤14)
    (hit : (4095,cost)∈p.foldl scored initialScored) : 0<run h := by
  obtain ⟨s,gs,y,init,budget,sorted,val,route⟩ := route_for_target cost len hit
  have startKey : ∀ g∈gs, later g.output 0 0 := by
    intro g _; exact Or.inl (by simp [Gate.output])
  have first (n : Nat) (hs : (starts n).toFinset=s) (nd : (starts n).Nodup) (ok : safe (starts n)) :=
    cannot_prune h 14 (starts n) gs y 0 0 val (hs ▸ route) nd ok budget sorted startKey
  rcases init with eq|eq
  · have u := first 9 (by rw [eq]; decide +kernel) (by decide +kernel) (by unfold safe; decide +kernel)
    exact Nat.add_pos_left u _
  · have u := first 10 (by rw [eq]; decide +kernel) (by decide +kernel) (by unfold safe; decide +kernel)
    exact Nat.add_pos_right _ u

end Live3210.Search
namespace Live3210.Blocks

inductive Tree (α : Type) where
  | atom (a : α)
  | node (op : Bool) (l r : Tree α)

def Tree.leaves : Tree α → List α
  | .atom a => [a]
  | .node _ l r => l.leaves ++ r.leaves

def Tree.val (t : Tree α) (row : α → Bool) : Bool :=
  match t with
  | .atom a => row a
  | .node op l r => if op then l.val row && r.val row else l.val row || r.val row

def Tree.word (t : Tree α) (vars : α → Nat) : Nat :=
  match t with
  | .atom a => vars a
  | .node op l r => if op then l.word vars &&& r.word vars else l.word vars ||| r.word vars

theorem Tree.word_bit (t : Tree α) (vars : α → Nat) (b : Nat) :
    (t.word vars).testBit b = t.val (fun a => (vars a).testBit b) := by
  induction t with
  | atom => rfl
  | node op l r il ir => cases op <;> simp [Tree.word,Tree.val,il,ir]

theorem Tree.val_congr (t : Tree α) {x y : α → Bool}
    (agree : ∀ a∈t.leaves, x a = y a) : t.val x = t.val y := by
  induction t with
  | atom a => exact agree a (by simp [Tree.leaves])
  | node op l r il ir =>
    rw [Tree.val, Tree.val, il (fun a h => agree a (List.mem_append_left _ h)),
      ir (fun a h => agree a (List.mem_append_right _ h))]

theorem Tree.source_rise (t : Tree α) {lo hi : α → Bool}
    (off : t.val lo = false) (on : t.val hi = true) :
    ∃ j ∈ t.leaves, lo j = false ∧ hi j = true := by
  induction t with
  | atom a => exact ⟨a,by simp [Tree.leaves],off,on⟩
  | node op l r il ir =>
    have left (h : l.val lo = false ∧ l.val hi = true) : ∃ j ∈ (Tree.node op l r).leaves, lo j = false ∧ hi j = true := by
      obtain ⟨j,hj,good⟩ := il h.1 h.2
      exact ⟨j,List.mem_append_left _ hj,good⟩
    have right (h : r.val lo = false ∧ r.val hi = true) : ∃ j ∈ (Tree.node op l r).leaves, lo j = false ∧ hi j = true := by
      obtain ⟨j,hj,good⟩ := ir h.1 h.2
      exact ⟨j,List.mem_append_right _ hj,good⟩
    apply Or.elim (a := l.val lo = false ∧ l.val hi = true)
      (b := r.val lo = false ∧ r.val hi = true) _ left right
    cases op <;> cases a : l.val lo <;> cases b : l.val hi <;> cases c : r.val lo <;> cases d : r.val hi <;>
      simp_all [Tree.val]

def Tree.cnt [DecidableEq α] (a : α) : Tree α → Nat
  | .atom i => if i=a then 1 else 0
  | .node _ l r => l.cnt a + r.cnt a

theorem Tree.cnt_eq [DecidableEq α] (t : Tree α) (i : α) : t.cnt i = t.leaves.count i := by
  induction t with
  | atom j => by_cases e : j=i <;> simp_all [Tree.cnt,Tree.leaves]
  | node k l r il ir => simp [Tree.cnt,Tree.leaves,il,ir]

def OnlyRise (a : α) (lo hi : α → Bool) := ∀ j, lo j = false → hi j = true → j = a

theorem rise [DecidableEq α] (t : Tree α) (i : α) {x y}
    (h : OnlyRise i x y) (low : t.val x = false) (high : t.val y = true) : 0 < t.cnt i := by
  obtain ⟨j,mem,hx,hy⟩ := t.source_rise low high
  obtain rfl := h j hx hy
  rw [t.cnt_eq]
  exact List.count_pos_iff.mpr mem

section TreeInduction
variable {α : Type} [DecidableEq α]

/-- A pair of positive occurrences whose least common ancestor has the chosen sign. -/
def Tree.split (isAnd : Bool) (a b : α) : Tree α → Prop
  | .atom _ => False
  | .node k l r => l.split isAnd a b ∨ r.split isAnd a b ∨
      (k=isAnd ∧ ((0<l.cnt a ∧ 0<r.cnt b) ∨ (0<r.cnt a ∧ 0<l.cnt b)))

theorem splitContains (t : Tree α) {op a b} (h : t.split op a b) : 0<t.cnt a ∧ 0<t.cnt b := by
  induction t with
  | atom _ => contradiction
  | node k l r il ir =>
    rcases h with hl|hr|⟨_,⟨_,_⟩|⟨_,_⟩⟩
    · specialize il hl; simp only [Tree.cnt]; omega
    · specialize ir hr; simp only [Tree.cnt]; omega
    all_goals simp only [Tree.cnt]; omega

theorem uniqueSign (t : Tree α) {a b} (c1 : t.cnt a ≤ 1) (c2 : t.cnt b ≤ 1)
    (yes : t.split true a b) (no : t.split false a b) : False := by
  induction t with
  | atom _ => contradiction
  | node k l r il ir =>
    simp only [Tree.cnt] at c1 c2
    have ihL := il (by omega) (by omega)
    have ihR := ir (by omega) (by omega)
    by_cases la : 0 < l.cnt a <;> by_cases lb : 0 < l.cnt b
    · have select (op) (h : (Tree.node k l r).split op a b) : l.split op a b := by
        rcases h with hl|hr|⟨_,⟨ha,hb⟩|⟨ha,hb⟩⟩
        · exact hl
        · obtain ⟨ha,hb⟩ := splitContains r hr; omega
        · omega
        · omega
      exact ihL (select _ yes) (select _ no)
    · have select (op) (h : (Tree.node k l r).split op a b) : k=op := by
        rcases h with hl|hr|⟨hk,_⟩
        · obtain ⟨ha,hb⟩ := splitContains l hl; omega
        · obtain ⟨ha,hb⟩ := splitContains r hr; omega
        · exact hk
      simpa using (select _ yes).symm.trans (select _ no)
    · have select (op) (h : (Tree.node k l r).split op a b) : k=op := by
        rcases h with hl|hr|⟨hk,_⟩
        · obtain ⟨ha,hb⟩ := splitContains l hl; omega
        · obtain ⟨ha,hb⟩ := splitContains r hr; omega
        · exact hk
      simpa using (select _ yes).symm.trans (select _ no)
    · have select (op) (h : (Tree.node k l r).split op a b) : r.split op a b := by
        rcases h with hl|hr|⟨_,⟨ha,hb⟩|⟨ha,hb⟩⟩
        · obtain ⟨ha,hb⟩ := splitContains l hl; omega
        · exact hr
        · omega
        · omega
      exact ihR (select _ yes) (select _ no)

/-- The AND restriction needs a positive instance of each variable in the same
true-proof at (1,1). Their least common ancestor is an AND. -/
theorem meetCorner (t : Tree α) {a b : α} {z x y : α → Bool}
    (fx : OnlyRise a x z) (fy : OnlyRise b y z)
    (on : t.val z = true) (offx : t.val x = false) (offy : t.val y = false)
    (ne : a ≠ b) : t.split true a b := by
  induction t with
  | atom j =>
    have h1 := rise (Tree.atom j) a fx offx on
    have h2 := rise (Tree.atom j) b fy offy on
    by_cases h : j = a <;> by_cases t : j = b <;> simp_all [Tree.cnt]
  | node k l r il ir =>
    cases k
    · simp only [Tree.val,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.or_eq_false_iff] at on offx offy
      rcases on with hl|hr
      · exact Or.inl (il hl offx.1 offy.1)
      · exact Or.inr (Or.inl (ir hr offx.2 offy.2))
    · have lr : l.val z = true ∧ r.val z = true := by simpa [Tree.val] using on
      by_cases hx : l.val x = false <;> by_cases hy : l.val y = false
      · exact Or.inl (il lr.1 hx hy)
      · have rr : r.val y = false := by simpa [Tree.val,Bool.eq_true_of_not_eq_false hy] using offy
        exact Or.inr (Or.inr ⟨rfl,Or.inl ⟨rise l a fx hx lr.1,rise r b fy rr lr.2⟩⟩)
      · have rr : r.val x = false := by simpa [Tree.val,Bool.eq_true_of_not_eq_false hx] using offx
        exact Or.inr (Or.inr ⟨rfl,Or.inr ⟨rise r a fx rr lr.2,rise l b fy hy lr.1⟩⟩)
      · have r1 : r.val x = false := by simpa [Tree.val,Bool.eq_true_of_not_eq_false hx] using offx
        have r2 : r.val y = false := by simpa [Tree.val,Bool.eq_true_of_not_eq_false hy] using offy
        exact Or.inr (Or.inl (ir lr.2 r1 r2))

/-- The OR restriction needs a positive instance of each variable in the same
false-proof at (0,0). Their least common ancestor is an OR. -/
theorem joinCorner (t : Tree α) {a b : α} {z x y : α → Bool}
    (fx : OnlyRise a z x) (fy : OnlyRise b z y)
    (off : t.val z = false) (onx : t.val x = true) (ony : t.val y = true)
    (ne : a ≠ b) : t.split false a b := by
  induction t with
  | atom j =>
    have h1 := rise (Tree.atom j) a fx off onx
    have h2 := rise (Tree.atom j) b fy off ony
    by_cases h : j = a <;> by_cases t : j = b <;> simp_all [Tree.cnt]
  | node k l r il ir =>
    cases k
    · have lr : l.val z = false ∧ r.val z = false := by simpa [Tree.val] using off
      by_cases hx : l.val x = true <;> by_cases hy : l.val y = true
      · exact Or.inl (il lr.1 hx hy)
      · have rr : r.val y = true := by simpa [Tree.val,Bool.eq_false_of_not_eq_true hy] using ony
        exact Or.inr (Or.inr ⟨rfl,Or.inl ⟨rise l a fx lr.1 hx,rise r b fy lr.2 rr⟩⟩)
      · have rr : r.val x = true := by simpa [Tree.val,Bool.eq_false_of_not_eq_true hx] using onx
        exact Or.inr (Or.inr ⟨rfl,Or.inr ⟨rise r a fx lr.2 rr,rise l b fy lr.1 hy⟩⟩)
      · have r1 : r.val x = true := by simpa [Tree.val,Bool.eq_false_of_not_eq_true hx] using onx
        have r2 : r.val y = true := by simpa [Tree.val,Bool.eq_false_of_not_eq_true hy] using ony
        exact Or.inr (Or.inl (ir lr.2 r1 r2))
    · simp only [Tree.val,ite_true,Bool.and_eq_true] at onx ony
      cases h : l.val z
      · exact Or.inl (il h onx.1 ony.1)
      · have hr : r.val z = false := by simpa [Tree.val,h] using off
        exact Or.inr (Or.inl (ir hr onx.2 ony.2))

end TreeInduction

end Live3210.Blocks
namespace Live3210.Blocks
variable {α : Type} [DecidableEq α]

def Cell (w p q : Nat) := w.testBit p = true ∧ w.testBit q = false

def Local (t : Tree α) (vars : α → Nat) (a : α) (p q : Nat) :=
  Cell (t.word vars) p q ∧ ∀ j∈t.leaves, Cell (vars j) p q → j=a

private def clipped (t : Tree α) (vars : α → Nat) (r : Nat) (j : α) : Bool :=
  if j∈t.leaves then (vars j).testBit r else false

private theorem clipVal (t : Tree α) (vars : α → Nat) (r : Nat) :
    t.val (clipped t vars r) = (t.word vars).testBit r := by
  rw [t.word_bit]
  apply t.val_congr
  intro j hj
  simp [clipped,hj]

private theorem clipOnly {t : Tree α} {vars a p q} (h : Local t vars a p q) :
    OnlyRise a (clipped t vars q) (clipped t vars p) := by
  intro j lo hi
  by_cases hj : j∈t.leaves
  · apply h.2 j hj
    simpa [Cell,clipped,hj] using And.intro hi lo
  · simp [clipped,hj] at hi

theorem Tree.no_conflict (t : Tree α) (vars : α → Nat) {a b : α} (different : a ≠ b)
    (ua : t.leaves.count a ≤ 1) (ub : t.leaves.count b ≤ 1)
    {p qa qb q pa pb : Nat}
    (ap : Local t vars a p qa) (bp : Local t vars b p qb)
    (aq : Local t vars a pa q) (bq : Local t vars b pb q) : False := by
  have pos := meetCorner t (clipOnly ap) (clipOnly bp)
    ((clipVal t vars p).trans ap.1.1) ((clipVal t vars qa).trans ap.1.2)
    ((clipVal t vars qb).trans bp.1.2) different
  have neg := joinCorner t (clipOnly aq) (clipOnly bq)
    ((clipVal t vars q).trans aq.1.2) ((clipVal t vars pa).trans aq.1.1)
    ((clipVal t vars pb).trans bq.1.1) different
  exact uniqueSign t (by simpa [Tree.cnt_eq] using ua) (by simpa [Tree.cnt_eq] using ub) pos neg

/-- Following a separating reference backwards must end at the unique owner. -/
theorem earlier_or_owner (good : Nat → Prop) (owner n : Nat)
    (source : ∀ j, j≤n → good j → j=owner ∨ ∃ i<j, good i) :
    ∀ j, j≤n → good j → good owner ∧ owner≤j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro bounded hj
    rcases source j bounded hj with rfl|⟨i,lt,hi⟩
    · exact ⟨hj,le_rfl⟩
    · obtain ⟨inc,order⟩ := ih i lt (by omega) hi
      exact ⟨inc,by omega⟩

end Live3210.Blocks
namespace Live3210.Blocks

abbrev Label (β : Type) := Sum β (Nat × Nat)
def variableWord (raw : β → Nat) : Label β → Nat := Sum.elim raw Prod.snd

/-- Each private cell is also a private cell of the block containing its sole
separating initial wire. No reference available before that block separates it. -/
theorem local_of_private [DecidableEq β] (raw : β → Nat)
    (blocks : Nat → Tree (Label β)) (last owner : Nat) (ownerBound : owner≤last)
    (a : β) (p q : Nat)
    (back : ∀ k≤last, ∀ ref : Nat × Nat, Sum.inr ref ∈ (blocks k).leaves →
      ref.1 < k ∧ ref.2 = (blocks ref.1).word (variableWord raw))
    (privateRaw : ∀ k≤last, ∀ b, Sum.inl b ∈ (blocks k).leaves → Cell (raw b) p q → b=a)
    (uniqueOwner : ∀ k≤last, Sum.inl a ∈ (blocks k).leaves → k=owner)
    (target : Cell ((blocks last).word (variableWord raw)) p q) :
    Local (blocks owner) (variableWord raw) (Sum.inl a) p q := by
  let good (k : Nat) := Cell ((blocks k).word (variableWord raw)) p q
  have follow (k) (bound : k≤last) (g : good k) : k=owner ∨ ∃j<k, good j := by
    have low := g.2
    have high := g.1
    change ((blocks k).word (variableWord raw)).testBit q = false at low
    change ((blocks k).word (variableWord raw)).testBit p = true at high
    rw [Tree.word_bit] at low high
    obtain ⟨lab,mem,zero,one⟩ := (blocks k).source_rise low high
    cases lab with
    | inl b =>
      have eq := privateRaw k bound b mem ⟨one,zero⟩
      exact Or.inl (uniqueOwner k bound (eq ▸ mem))
    | inr ref =>
      obtain ⟨lt,eq⟩ := back k bound ref mem
      refine Or.inr ⟨ref.1,lt,?_⟩
      change Cell ((blocks ref.1).word (variableWord raw)) p q
      rw [←eq]
      exact ⟨one,zero⟩
  have forced := earlier_or_owner good owner last follow
  refine ⟨(forced last le_rfl target).1,?_⟩
  intro label mem g
  cases label with
  | inl b => exact congrArg Sum.inl (privateRaw owner ownerBound b mem g)
  | inr ref =>
    obtain ⟨lt,eq⟩ := back owner ownerBound ref mem
    have earlier : good ref.1 := by
      change Cell ((blocks ref.1).word (variableWord raw)) p q
      rw [←eq]
      exact g
    have order := (forced ref.1 (by omega) earlier).2
    omega

end Live3210.Blocks
namespace Live3210.Blocks
open Ordered Search

abbrev InputLabel := Sum Signal (Nat × Nat)
abbrev Expr := Tree InputLabel
abbrev Entry := Signal × Expr

def value (t : Expr) : Nat := t.word (Sum.elim Prod.fst Prod.snd)
def literal (s : Signal) : Expr := .atom (.inl s)
def reference (i v : Nat) : Expr := .atom (.inr (i,v))

def Admits (defs : List Expr) (t : Expr) : Prop :=
  ∀ (i v : Nat), (.inr (i,v) : InputLabel)∈t.leaves → ∃ e, defs[i]?=some e ∧ value e=v

inductive Chronological : List Expr → Prop where
  | nil : Chronological []
  | snoc {defs t} (valid : Chronological defs) (closed : Admits defs t) : Chronological (defs++[t])

def charge (u : Signal) (t : Expr) := t.leaves.count (.inl u)
def inventory (u : Signal) (ts : List Expr) := (ts.map (charge u)).sum
def frontier (ws : List Entry) := (ws.map Prod.fst).toFinset

structure State (defs : List Expr) (ws : List Entry) : Prop where
  order : Chronological defs
  valid : ∀ e∈ws, Admits defs e.2
  agrees : ∀ e∈ws, value e.2=e.1.1
  unique : (ws.map Prod.fst).Nodup

theorem Admits.append {defs : List Expr} {t : Expr} (ok : Admits defs t) (extra : List Expr) :
    Admits (defs++extra) t := by
  intro i w use
  obtain ⟨e,atI,eq⟩ := ok i w use
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp atI
  exact ⟨e,(List.getElem?_append_left hi).trans atI,eq⟩

private theorem valid_ref (defs : List Expr) (t : Expr) :
    Admits (defs++[t]) (reference defs.length (value t)) := by
  intro i v use
  have eq : (i,v)=(defs.length,value t) := by simpa [reference,Tree.leaves] using use
  cases eq
  exact ⟨t,List.getElem?_concat_length,rfl⟩

private theorem valid_fork {defs : List Expr} (op : Bool) {a b : Expr}
    (ha : Admits defs a) (hb : Admits defs b) : Admits defs (.node op a b) := by
  intro i v use
  rcases (List.mem_append.mp use) with l|r
  · exact ha _ _ l
  · exact hb _ _ r

def decls (a b : Expr) (c : Choice) : List Expr := c.keep a b
def leftTree (n : Nat) (a : Expr) : Choice → Expr
  | .left | .both => reference n (value a)
  | .none | .right => a
def rightTree (n : Nat) (b : Expr) : Choice → Expr
  | .right => reference n (value b)
  | .both => reference (n+1) (value b)
  | .none | .left => b

private theorem step_refs (defs : List Expr) (a b : Expr) (c : Choice)
    (ok : Chronological defs) (ha : Admits defs a) (hb : Admits defs b) :
    Chronological (defs++decls a b c) ∧
    Admits (defs++decls a b c) (leftTree defs.length a c) ∧
    Admits (defs++decls a b c) (rightTree defs.length b c) := by
  cases c with
  | none => simpa [leftTree,rightTree,decls,Choice.keep] using And.intro ok (And.intro ha hb)
  | left => exact ⟨.snoc ok ha,valid_ref _ _,hb.append _⟩
  | right => exact ⟨.snoc ok hb,ha.append _,valid_ref _ _⟩
  | both =>
    have ok₂ := Chronological.snoc (.snoc ok ha) (hb.append [a])
    have l := (valid_ref defs a).append [b]
    have r := valid_ref (defs++[a]) b
    simpa only [decls,Choice.keep,leftTree,rightTree,List.append_assoc,List.cons_append,List.nil_append,
      List.length_append,List.length_singleton] using And.intro ok₂ (And.intro l r)

private theorem left_value (n) (a : Expr) (c) : value (leftTree n a c)=value a := by cases c <;> rfl
private theorem right_value (n) (b : Expr) (c) : value (rightTree n b c)=value b := by cases c <;> rfl

def made (g : Gate) (n : Nat) (a b : Expr) (c : Choice) (rest : List Entry) : List Entry :=
  let l := leftTree n a c
  let r := rightTree n b c
  (g.output,Tree.node g.op l r) :: (c.keep (g.left,l) (g.right,r) ++ rest)

private theorem made_ids (g : Gate) (n : Nat) (a b : Expr) (c) (rest : List Entry) :
    (made g n a b c rest).map Prod.fst = g.output::(c.keep g.left g.right ++ rest.map Prod.fst) := by
  cases c <;> rfl

private theorem charges (u : Signal) (g : Gate) (defs : List Expr) (a b : Expr) (c) (rest : List Entry) :
    inventory u (defs++decls a b c) + inventory u ((made g defs.length a b c rest).map Prod.snd) =
    inventory u defs + inventory u ((a::b::rest.map Prod.snd)) := by
  cases c <;>
    simp [inventory,charge,decls,Choice.keep,leftTree,rightTree,made,Tree.leaves,List.count_append,
      reference,List.sum_append,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]

private theorem mem_keep {α : Type} (c : Choice) (x y z : α) (hz : z∈c.keep x y) : z=x ∨ z=y := by
  cases c <;> simp [Choice.keep] at hz <;> tauto

theorem cutStep {defs : List Expr} {ws : List Entry} {g : Gate} {t : Finset Signal}
    (st : State defs ws) (m : Enables g (frontier ws) t) :
    ∃ ds zs, frontier zs=t ∧ State ds zs ∧ ds.length+ws.length=defs.length+zs.length+1 ∧
      ∀ u, inventory u ds + inventory u (zs.map Prod.snd) =
           inventory u defs + inventory u (ws.map Prod.snd) := by
  classical
  obtain ⟨⟨v,a⟩,ha,tagA⟩ := List.mem_map.mp (List.mem_toFinset.mp m.left)
  obtain ⟨⟨w,b⟩,hb,tagB⟩ := List.mem_map.mp (List.mem_toFinset.mp m.right)
  change v=g.left at tagA
  change w=g.right at tagB
  subst v; subst w
  let ea : Entry := (g.left,a)
  let eb : Entry := (g.right,b)
  have ne : ea≠eb := fun h => m.different (congrArg (fun e : Entry => e.1.1) h)
  have step₁ : ws.Perm (ea::ws.erase ea) := List.perm_cons_erase ha
  have present : eb∈ws.erase ea := (List.mem_cons.mp (step₁.mem_iff.mp hb)).resolve_left ne.symm
  let rest := (ws.erase ea).erase eb
  have perm : ws.Perm (ea::eb::rest) := step₁.trans ((List.perm_cons_erase present).cons ea)
  have permIds : (ws.map Prod.fst).Perm (g.left::g.right::rest.map Prod.fst) := perm.map Prod.fst
  obtain ⟨c,rep,nd⟩ := pickKeep m st.unique g.left g.right (rest.map Prod.fst)
    (Or.inl ⟨rfl,rfl⟩) permIds
  let ds := defs++decls a b c
  let zs := made g defs.length a b c rest
  have ids : zs.map Prod.fst = g.output::(c.keep g.left g.right ++ rest.map Prod.fst) := made_ids ..
  have old (e) (mem : e∈rest) : e∈ws := perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))
  obtain ⟨chron,lOK,rOK⟩ := step_refs defs a b c st.order (st.valid _ ha) (st.valid _ hb)
  have getA := st.agrees _ ha
  have getB := st.agrees _ hb
  change value a = g.left.1 at getA
  change value b = g.right.1 at getB
  have branches (e : Entry) (he : e∈zs) :
      e=(g.output,.node g.op (leftTree defs.length a c) (rightTree defs.length b c)) ∨
      e=(g.left,leftTree defs.length a c) ∨ e=(g.right,rightTree defs.length b c) ∨ e∈rest := by
    rcases List.mem_cons.mp he with rfl|other
    · exact Or.inl rfl
    · rcases List.mem_append.mp other with held|prior
      · rcases mem_keep _ _ _ _ held with l|r
        · exact Or.inr (Or.inl l)
        · exact Or.inr (Or.inr (Or.inl r))
      · exact Or.inr (Or.inr (Or.inr prior))
  refine ⟨ds,zs,(congrArg List.toFinset ids).trans rep,⟨chron,?_,?_,ids ▸ nd⟩,?_,?_⟩
  · intro e he
    rcases branches e he with rfl|rfl|rfl|remain
    · exact valid_fork _ lOK rOK
    · exact lOK
    · exact rOK
    · exact (st.valid e (old e remain)).append _
  · intro e he
    rcases branches e he with rfl|rfl|rfl|remain
    · change combine g.op (value (leftTree _ a c)) (value (rightTree _ b c)) = combine g.op _ _
      rw [left_value,right_value,getA,getB]
    · exact (left_value ..).trans getA
    · exact (right_value ..).trans getB
    · exact st.agrees e (old e remain)
  · have len := perm.length_eq
    cases c <;> simp [ds,zs,decls,Choice.keep,made] at * <;> omega
  · intro u
    have rearr := ((perm.map Prod.snd).map (charge u)).sum_eq
    exact (charges u g defs a b c rest).trans (congrArg (inventory u defs + ·) rearr.symm)

theorem cutRoute {s t : Finset Signal} {gs : List Gate} (route : Route gs s t)
    (defs : List Expr) (ws : List Entry) (start : frontier ws=s) (st : State defs ws) :
    ∃ ds zs, frontier zs=t ∧ State ds zs ∧ ds.length+ws.length=defs.length+zs.length+gs.length ∧
      ∀ u, inventory u ds + inventory u (zs.map Prod.snd) =
           inventory u defs + inventory u (ws.map Prod.snd) := by
  induction route generalizing defs ws with
  | stop =>
    exact ⟨defs,ws,start,st,by simp,fun _ => rfl⟩
  | next m tail ih =>
    obtain ⟨ds,ts,repr,valid,count,amount⟩ := cutStep st (start ▸ m)
    obtain ⟨es,zs,done,ok,len,fin⟩ := ih ds ts repr valid
    exact ⟨es,zs,done,ok,by simp; omega,fun u => (fin u).trans (amount u)⟩

structure Certificate (live : List Signal) (target gates : Nat) where
  blocks : List Expr
  output : Expr
  chronological : Chronological blocks
  closed : Admits blocks output
  correct : value output = target
  excess : blocks.length+live.length=gates+1
  occurrences : ∀ u, inventory u blocks + charge u output = live.count u

private theorem literal_inventory (u : Signal) (ws : List Signal) :
    inventory u (ws.map literal) = ws.count u := by
  induction ws with
  | nil => rfl
  | cons v vs ih =>
    by_cases eq : v=u
    · subst v; simp [inventory,charge,literal,Tree.leaves] at ih ⊢; omega
    · simp [inventory,charge,literal,Tree.leaves,eq] at ih ⊢; omega

theorem compile_blocks {ws : List Signal} {gs : List Gate} {y : Signal}
    (path : Route gs ws.toFinset {y}) (nd : ws.Nodup) :
    Nonempty (Certificate ws y.1 gs.length) := by
  let entries := ws.map (fun v => ((v,literal v) : Entry))
  have ids : entries.map Prod.fst=ws := by simp [entries,List.map_map,Function.comp_def]
  have expr : entries.map Prod.snd=ws.map literal := by simp [entries,List.map_map,Function.comp_def]
  have initial : State [] entries := by
    refine ⟨.nil,?_,?_,ids ▸ nd⟩
    · intro e he i v h
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp he
      simp [literal,Tree.leaves] at h
    · intro e he
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp he
      rfl
  obtain ⟨bs,zs,rep,st,count,total⟩ := cutRoute path [] entries (congrArg List.toFinset ids) initial
  have size := List.toFinset_card_of_nodup st.unique
  change (frontier zs).card = _ at size
  rw [rep,Finset.card_singleton,List.length_map] at size
  obtain ⟨e,rfl⟩ := List.length_eq_one_iff.mp size.symm
  have hm : e.1∈frontier [e] := by simp [frontier]
  rw [rep,Finset.mem_singleton] at hm
  refine ⟨⟨bs,e.2,st.order,st.valid _ List.mem_cons_self,(st.agrees _ List.mem_cons_self).trans (congrArg Prod.fst hm),?_,?_⟩⟩
  · simpa [entries,Nat.add_comm] using count
  · intro u
    simpa [expr,inventory, ←literal_inventory u ws] using total u

end Live3210.Blocks
namespace Live3210.Blocks
open Ordered

theorem Chronological.read {bs : List Expr} (ok : Chronological bs) (k : Nat) (hk : k<bs.length) :
    Admits (bs.take k) bs[k] := by
  induction ok with
  | nil => simp at hk
  | @snoc ds t order closed ih =>
    by_cases earlier : k<ds.length
    · rw [List.getElem_append_left earlier,List.take_append_of_le_length earlier.le]
      exact ih earlier
    · have eq : k=ds.length := by simp only [List.length_append,List.length_singleton] at hk; omega
      subst k
      simpa [List.getElem_append_right] using closed

private theorem list_charge_le (xs : List Expr) (u : Signal) (k : Nat) (hk : k<xs.length) :
    charge u xs[k] ≤ inventory u xs := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons t ts ih =>
    cases k with
    | zero => simp [inventory]
    | succ k =>
      have len : k<ts.length := by simpa using hk
      have tail := ih k len
      change charge u ts[k] ≤ charge u t + inventory u ts
      omega

def owner (ts : List Expr) (u : Signal) := ts.findIdx (fun t => t.leaves.contains (.inl u))
private theorem owner_index (ts : List Expr) (u : Signal) (k : Nat) (hk : k<ts.length)
    (unique : inventory u ts≤1) (used : (.inl u : InputLabel)∈ts[k].leaves) :
    owner ts u=k := by
  induction ts generalizing k with
  | nil => simp at hk
  | cons t ts ih =>
    rw [owner,List.findIdx_cons]
    cases k with
    | zero =>
      change (.inl u : InputLabel)∈t.leaves at used
      simp [used]
    | succ k =>
      have len : k<ts.length := by simpa using hk
      change (.inl u : InputLabel)∈ts[k].leaves at used
      have pos : 0<charge u ts[k] := List.count_pos_iff.mpr used
      have upper := list_charge_le ts u k len
      change charge u t + inventory u ts ≤ 1 at unique
      have no : (.inl u : InputLabel)∉t.leaves := by
        intro mem
        have : 0<charge u t := List.count_pos_iff.mpr mem
        omega
      have tail := ih k len (by omega) used
      simp [no,owner] at tail ⊢
      omega

def Certificate.trees {ws target cost} (c : Certificate ws target cost) := c.blocks++[c.output]
def Certificate.get {ws target cost} (c : Certificate ws target cost) (k : Nat) :=
  c.trees.getD k c.output

theorem Certificate.total {ws target cost} (c : Certificate ws target cost) (u : Signal) :
    inventory u c.trees=ws.count u := by
  simpa [Certificate.trees,inventory] using c.occurrences u
theorem Certificate.atLast {ws target cost} (c : Certificate ws target cost) :
    c.get c.blocks.length=c.output := by
  simp [Certificate.get,Certificate.trees,List.getD_eq_getElem?_getD]

private theorem Certificate.inRange {ws target cost} (c : Certificate ws target cost) (k) (hk : k≤c.blocks.length) :
    k<c.trees.length := by simp [Certificate.trees]; omega

theorem Certificate.references {ws target cost} (c : Certificate ws target cost) (k) (hk : k≤c.blocks.length)
    (r : Nat×Nat) (use : (.inr r : InputLabel)∈(c.get k).leaves) :
    r.1<k ∧ r.2=value (c.get r.1) := by
  have bound := c.inRange k hk
  have atK : c.get k=c.trees[k] := List.getD_eq_getElem _ _ bound
  rw [atK] at use
  have chronological : Chronological c.trees := .snoc c.chronological c.closed
  obtain ⟨e,atRef,eq⟩ := chronological.read k bound r.1 r.2 use
  obtain ⟨within,found⟩ := List.getElem?_eq_some_iff.mp atRef
  have len : r.1<k := within.trans_le (List.length_take_le _ _)
  have lookup : c.trees[r.1]? = some e := by
    simpa [List.getElem?_take,len] using atRef
  refine ⟨len,?_⟩
  rw [Certificate.get,List.getD_eq_getElem?_getD,lookup]
  exact eq.symm

theorem Certificate.owns_raw {ws target cost} (c : Certificate ws target cost) (k) (hk : k≤c.blocks.length)
    (u : Signal) (use : (.inl u : InputLabel)∈(c.get k).leaves) : u∈ws := by
  have bound := c.inRange k hk
  rw [show c.get k=c.trees[k] from List.getD_eq_getElem _ _ bound] at use
  have pos : 0<charge u c.trees[k] := List.count_pos_iff.mpr use
  exact List.count_pos_iff.mp ((pos.trans_le (list_charge_le c.trees u k bound)).trans_eq (c.total u))

theorem Certificate.unique_owner {ws target cost} (c : Certificate ws target cost) (nd : ws.Nodup)
    (k) (hk : k≤c.blocks.length) (u : Signal) (use : (.inl u : InputLabel)∈(c.get k).leaves) :
    k=owner c.trees u := by
  have bound := c.inRange k hk
  rw [show c.get k=c.trees[k] from List.getD_eq_getElem _ _ bound] at use
  exact (owner_index _ u k bound (by rw [c.total]; exact List.nodup_iff_count_le_one.mp nd _) use).symm

theorem Certificate.owner_bound {ws target cost} (c : Certificate ws target cost) {u : Signal} (hu : u∈ws) :
    owner c.trees u≤c.blocks.length := by
  have positive := (c.total u).symm ▸ List.count_pos_iff.mpr hu
  have existsLeaf (ts : List Expr) (pos : 0 < inventory u ts) :
      ∃ x∈ts, x.leaves.contains (.inl u) = true := by
    induction ts with
    | nil => simp [inventory] at pos
    | cons t ts ih =>
      change 0<charge u t + inventory u ts at pos
      by_cases has : (.inl u : InputLabel)∈t.leaves
      · exact ⟨t,List.mem_cons_self,by simpa using has⟩
      · have missing : charge u t=0 := List.count_eq_zero_of_not_mem has
        obtain ⟨x,mem,found⟩ := ih (by omega)
        exact ⟨x,List.mem_cons_of_mem _ mem,found⟩
  have lt := List.findIdx_lt_length_of_exists (existsLeaf c.trees positive)
  change owner c.trees u < c.trees.length at lt
  simpa [Certificate.trees,Nat.lt_succ_iff] using lt

theorem Certificate.occurrence_bound {ws target cost} (c : Certificate ws target cost) (nd : ws.Nodup)
    (k) (hk : k≤c.blocks.length) (u : Signal) : (c.get k).leaves.count (.inl u)≤1 := by
  have bound := c.inRange k hk
  rw [show c.get k=c.trees[k] from List.getD_eq_getElem _ _ bound]
  exact (list_charge_le c.trees u k bound).trans ((c.total u) ▸ List.nodup_iff_count_le_one.mp nd u)

def Private (ws : List Signal) (u : Signal) (p q : Fin 12) :=
  u∈ws ∧ ∀ w∈ws, covers w.1 p q → w=u

theorem Certificate.local_cell {ws cost} (c : Certificate ws 4095 cost) (nd : ws.Nodup)
    {u : Signal} {p q : Fin 12} (cell : Private ws u p q) :
    Local (c.get (owner c.trees u)) (variableWord Prod.fst) (.inl u) p.val (12+q.val) := by
  apply local_of_private Prod.fst c.get c.blocks.length (owner c.trees u) (c.owner_bound cell.1)
    u p.val (12+q.val) c.references
  · intro k hk a ha covers
    exact cell.2 a (c.owns_raw k hk a ha) covers
  · exact fun k hk used => c.unique_owner nd k hk u used
  · change Cell (value (c.get c.blocks.length)) _ _
    rw [c.atLast,c.correct]
    obtain ⟨v,hv,h⟩ := target_sep p q
    rwa [Finset.mem_singleton.mp hv] at h

def Conflict (ws : List Signal) (a b : Signal) :=
  a≠b ∧ ∃ p qa qb q pa pb : Fin 12,
    Private ws a p qa ∧ Private ws b p qb ∧ Private ws a pa q ∧ Private ws b pb q

theorem Certificate.separate_owners {ws cost} (c : Certificate ws 4095 cost) (nd : ws.Nodup)
    {a b : Signal} (conf : Conflict ws a b) : owner c.trees a ≠ owner c.trees b := by
  rintro same
  obtain ⟨ne,p,qa,qb,q,pa,pb,h₁,h₂,h₃,h₄⟩ := conf
  let k := owner c.trees a
  have atA := c.owner_bound h₁.1
  have beqs := lawful_beq_subsingleton (α:=InputLabel) instBEqOfDecidableEq Sum.instBEq
  apply Tree.no_conflict (c.get k) (variableWord Prod.fst) (a:=.inl a) (b:=.inl b)
    (fun eq => ne (Sum.inl.inj eq))
    (by rw [beqs]; exact c.occurrence_bound nd k atA a) (by rw [beqs]; exact c.occurrence_bound nd k atA b)
    (c.local_cell nd h₁) (same ▸ c.local_cell nd h₂) (c.local_cell nd h₃) (same ▸ c.local_cell nd h₄)

theorem Certificate.cell_source {ws target cost} (c : Certificate ws target cost) (nd : ws.Nodup)
    (k) (hk : k≤c.blocks.length) (p q : Fin 12) (yes : covers (value (c.get k)) p q) :
    (∃ u∈ws, owner c.trees u=k ∧ covers u.1 p q) ∨
      ∃ prev<k, covers (value (c.get prev)) p q := by
  let vars : InputLabel → Nat := variableWord Prod.fst
  have on := yes.1
  have off := yes.2
  change ((c.get k).word vars).testBit _ = true at on
  change ((c.get k).word vars).testBit _ = false at off
  rw [Tree.word_bit] at on off
  obtain ⟨label,mem,lo,hi⟩ := (c.get k).source_rise off on
  cases label with
  | inl u => exact Or.inl ⟨u,c.owns_raw _ hk _ mem,(c.unique_owner nd _ hk _ mem).symm,hi,lo⟩
  | inr r =>
    obtain ⟨early,eq⟩ := c.references k hk r mem
    exact Or.inr ⟨r.1,early,eq ▸ (show covers r.2 p q from ⟨hi,lo⟩)⟩

theorem Certificate.word_bound {ws target cost} (c : Certificate ws target cost) (bound : safe ws)
    (k) (hk : k≤c.blocks.length) : value (c.get k)<2^24 := by
  have treeBound (t : Expr) (ok : ∀ j∈t.leaves, variableWord Prod.fst j < 2^24) : value t<2^24 := by
    induction t with
    | atom a => exact ok a (by simp [Tree.leaves])
    | node op a b ia ib =>
      have l := ia (fun j hj => ok j (List.mem_append_left _ hj))
      have r := ib (fun j hj => ok j (List.mem_append_right _ hj))
      cases op
      · exact Nat.or_lt_two_pow l r
      · exact Nat.and_lt_two_pow _ r
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    apply treeBound
    intro j hj
    cases j with
    | inl u => exact bound u (c.owns_raw _ hk _ hj)
    | inr ref =>
      obtain ⟨prior,eq⟩ := c.references k hk ref hj
      change ref.2<2^24
      rw [eq]
      exact ih ref.1 prior (by omega)

structure Coloring (ws : List Signal) (d : Nat) where
  last : Nat
  assign : Signal → Nat
  bitword : Nat → Nat
  fits : last+ws.length ≤ d+1
  assigned : ∀ u∈ws, assign u≤last
  output : bitword last=4095
  bounded : ∀ k≤last, bitword k<2^24
  edges : ∀ a b, Conflict ws a b → assign a≠assign b
  needed : ∀ u p q, Private ws u p q → covers (bitword (assign u)) p q
  support : ∀ k≤last, ∀ p q, covers (bitword k) p q →
    (∃ u∈ws, assign u=k ∧ covers u.1 p q) ∨ ∃ i<k, covers (bitword i) p q

theorem coloring_of_route {ws : List Signal} {d : Nat} {gs : List Gate} {y : Signal}
    (path : Route gs ws.toFinset {y}) (nd : ws.Nodup) (bounded : safe ws)
    (target : y.1=4095) (cost : gs.length≤d) : Nonempty (Coloring ws d) := by
  obtain ⟨initial⟩ := compile_blocks path nd
  let c : Certificate ws 4095 gs.length := target ▸ initial
  refine ⟨⟨c.blocks.length,owner c.trees,(fun k => value (c.get k)),?_,fun _ => c.owner_bound,?_,
    c.word_bound bounded,(fun _ _ => c.separate_owners nd),?_,c.cell_source nd⟩⟩
  · have e := c.excess; omega
  · rw [c.atLast,c.correct]
  · intro u p q cell
    exact (c.local_cell nd cell).1

theorem Coloring.prefix_support {ws : List Signal} {d} (c : Coloring ws d)
    (k) (bound : k≤c.last) (p q : Fin 12) (cover : covers (c.bitword k) p q) :
    ∃ u∈ws, c.assign u≤k ∧ covers u.1 p q := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases c.support k bound p q cover with ⟨u,hu,eq,good⟩|⟨prev,earlier,good⟩
    · exact ⟨u,hu,eq.le,good⟩
    · obtain ⟨u,hu,rank,sep⟩ := ih _ earlier (earlier.le.trans bound) good
      exact ⟨u,hu,rank.trans earlier.le,sep⟩

theorem Coloring.cross {ws : List Signal} {d} (c : Coloring ws d)
    {a b : Signal} {p qa pb q : Fin 12} (left : Private ws a p qa) (right : Private ws b pb q)
    (same : c.assign a=c.assign b) : ∃ u∈ws, c.assign u≤c.assign a ∧ covers u.1 p q := by
  have high := (c.needed _ _ _ left).1
  have low := (c.needed _ _ _ right).2
  rw [←same] at low
  exact c.prefix_support _ (c.assigned a left.1) _ _ ⟨high,low⟩

end Live3210.Blocks
namespace Live3210.SubsetCheck

def strictNat {α : Type} (x : Nat) (f : Nat → α) : α :=
  Nat.casesOn x (f 0) (fun n => f n.succ)

structure Digit where
  word : Nat
  index : Nat
  members : Nat
  cover : Nat
  yes : Nat
  no : Nat

def full (n : Nat) := (1 <<< n)-1

def replicateMasks : Nat → Nat × Nat × List Nat
  | 0 => (1,1,[])
  | n+1 =>
    let (size,u,ms) := replicateMasks n
    (2*size, u ||| (u <<< size), (ms.map fun v => v ||| (v <<< size)) ++ [u <<< size])

def spread (w : Nat) : Nat :=
  let a := w &&& 4095
  let a := (a ||| (a <<< 88)) &&& 0xf0000000000000000000000ff
  let a := (a ||| (a <<< 44)) &&& 0xf00000000000f00000000000f
  let a := (a ||| (a <<< 22)) &&& 0x3000003000003000003000003000003
  let a := (a ||| (a <<< 11)) &&& 0x1001001001001001001001001001001001
  a

def rowCode (p q : Nat) := spread p * q
def sourceCode (v : Nat) := rowCode (v &&& 4095) ((v >>> 12) ^^^ 4095)



def collect (v : Nat) :=
  let a := v &&& 0x1001001001001001001001001001001001
  let a := (a ||| (a >>> 11)) &&& 0x3000003000003000003000003000003
  let a := (a ||| (a >>> 22)) &&& 0xf00000000000f00000000000f
  let a := (a ||| (a >>> 44)) &&& 0xf0000000000000000000000ff
  (a ||| (a >>> 88)) &&& 4095

def fastRows (w : Nat) :=
  let a := w ||| (w >>> 1)
  let b := a ||| (a >>> 2)
  let c := b ||| (b >>> 4)
  collect (c ||| (c >>> 4))

private def stage (s m : Nat) (f : Nat → List Nat) (i : Nat) : List Nat :=
  if m.testBit i then f i ++ f (s+i) else []

private def origin (i : Nat) : List Nat :=
  let a := fun j => if (0x1001001001001001001001001001001001 : Nat).testBit j then [j] else []
  let b := stage 11 0x3000003000003000003000003000003 a
  let c := stage 22 0xf00000000000f00000000000f b
  let d := stage 44 0xf0000000000000000000000ff c
  stage 88 4095 d i

private theorem stage_bit (v s m : Nat) (f : Nat → List Nat) (w : Nat)
    (ok : ∀ i, v.testBit i=true ↔ ∃ j∈f i, w.testBit j=true) (i : Nat) :
    ((v ||| (v >>> s)) &&& m).testBit i=true ↔ ∃ j∈stage s m f i, w.testBit j=true := by
  cases h : m.testBit i <;> simp [stage,h,Nat.testBit_shiftRight,ok,List.mem_append]; aesop

private theorem collect_bit (w : Nat) (i : Fin 12) : (collect w).testBit i.val = w.testBit (12*i.val) := by
  have base (j : Nat) : (w &&& 0x1001001001001001001001001001001001).testBit j=true ↔
    ∃ k∈(if (0x1001001001001001001001001001001001 : Nat).testBit j then [j] else []), w.testBit k=true := by
    cases h : (0x1001001001001001001001001001001001 : Nat).testBit j <;> simp [h]
  have check : ∀ j : Fin 12, origin j.val = [12*j.val] := by decide +kernel
  have h1 := stage_bit _ 11 0x3000003000003000003000003000003 _ _ base
  have h2 := stage_bit _ 22 0xf00000000000f00000000000f _ _ h1
  have h3 := stage_bit _ 44 0xf0000000000000000000000ff _ _ h2
  have eq := stage_bit _ 88 4095 _ w h3 i.val
  change (collect w).testBit i.val=true ↔ ∃ j∈origin i.val, w.testBit j=true at eq
  rw [check] at eq
  simp only [List.mem_singleton,exists_eq_left] at eq
  exact Bool.eq_iff_iff.mpr eq

private def hitAt (w i n : Nat) := ∃ j<n, w.testBit (i+j)=true

private theorem widen {w v n s : Nat} (sub : s≤n) (old : ∀ i, v.testBit i=true ↔ hitAt w i n) (i : Nat) :
    (v ||| (v >>> s)).testBit i=true ↔ hitAt w i (n+s) := by
  simp only [Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true,old,hitAt]
  constructor
  · rintro (⟨j,hj,h⟩|⟨j,hj,h⟩)
    · exact ⟨j,by omega,h⟩
    · exact ⟨s+j,by omega,by convert h using 2; omega⟩
  · rintro ⟨j,hj,h⟩
    by_cases lt : j<n
    · exact Or.inl ⟨j,lt,h⟩
    · exact Or.inr ⟨j-s,by omega,by convert h using 2; omega⟩

theorem fast_spec (w : Nat) (i : Fin 12) : (fastRows w).testBit i.val=true ↔ ∃ j : Fin 12, w.testBit (12*i.val+j.val)=true := by
  have h0 (k : Nat) : w.testBit k=true ↔ hitAt w k 1 := by simp [hitAt]
  have h1 := widen (s:=1) (by decide) h0
  have h2 := widen (s:=2) (by decide) h1
  have h3 := widen (s:=4) (by decide) h2
  have h4 := widen (s:=4) (by decide) h3 (12*i.val)
  rw [fastRows,collect_bit,h4]
  exact ⟨fun ⟨j,hj,h⟩ => ⟨⟨j,hj⟩,h⟩,fun ⟨j,h⟩ => ⟨j.val,j.isLt,h⟩⟩


def rowsOf := fastRows
def colsOf (w : Nat) :=
  let a := w ||| (w >>> 12)
  let a := a ||| (a >>> 24)
  let a := a ||| (a >>> 48)
  (a ||| (a >>> 96)) &&& 4095

def prepare (vs : List Nat) (masks : List Nat) : List Digit :=
  let dup := (vs.foldl (fun (p : Nat×Nat) v =>
    let x := sourceCode v
    (p.1 ||| x,p.2 ||| (p.1 &&& x))) (0,0)).2
  (vs.zip masks).zipIdx.map fun ((v,mem),i) =>
    let c := sourceCode v
    let pr := c &&& ((full 144) ^^^ dup)
    ⟨v,1 <<< i,mem,c,rowsOf pr,colsOf pr⟩

end Live3210.SubsetCheck
namespace Live3210.SubsetCheck
open Ordered Blocks

theorem source_eq (v : Nat) : sourceCode v = Packed.cover v := by
  change Packed.spread ((v &&& 4095) &&& 4095) * _ = Packed.spread (v &&& 4095)*_
  rw [Nat.and_assoc,Nat.and_self]

theorem source_bits (v : Nat) (hv : v<2^24) (i j : Fin 12) :
    (sourceCode v).testBit (12*i.val+j.val) = true ↔ covers v i j := by
  rw [source_eq]; exact Packed.cover_bits hv i j

theorem row_bit {w : Nat} (i : Fin 12) (hit : (rowsOf w).testBit i.val=true) :
    ∃ j : Fin 12, w.testBit (12*i.val+j.val)=true := (fast_spec w i).mp hit

theorem col_bit {w : Nat} (hw : w<2^144) (j : Fin 12) (hit : (colsOf w).testBit j.val=true) :
    ∃ i : Fin 12, w.testBit (12*i.val+j.val)=true := by
  have get (i : Nat) (bit : w.testBit (12*i+j.val)=true) :
      ∃ r : Fin 12, w.testBit (12*r.val+j.val)=true := by
    by_cases hi : i<12
    · exact ⟨⟨i,hi⟩,bit⟩
    · have no := Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right (by decide) (by omega : 144≤12*i+j.val)))
      rw [no] at bit; contradiction
  simp only [colsOf,Nat.testBit_and,Bool.and_eq_true,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true,
    ←Nat.add_assoc] at hit
  have any := hit.1
  clear hit
  rcases any with (((h|h)|(h|h))|((h|h)|(h|h)))|(((h|h)|(h|h))|((h|h)|(h|h))) <;>
    first | exact get 0 (by simpa using h) | exact get 1 h | exact get 2 h | exact get 3 h
          | exact get 4 h | exact get 5 h | exact get 6 h | exact get 7 h
          | exact get 8 h | exact get 9 h | exact get 10 h | exact get 11 h
          | exact get 12 h | exact get 13 h | exact get 14 h | exact get 15 h

def coverStep (p : Nat×Nat) (v : Nat) :=
  let x := sourceCode v
  (p.1 ||| x,p.2 ||| (p.1 &&& x))
def duplicate (vs : List Nat) := (vs.foldl coverStep (0,0)).2

private theorem fold_state (xs : List Nat) (acc : Nat×Nat) (k : Nat) :
    let n := (xs.filter (fun v => (sourceCode v).testBit k)).length
    let out := xs.foldl coverStep acc
    (out.1.testBit k = (acc.1.testBit k || decide (1≤n))) ∧
    (out.2.testBit k = (acc.2.testBit k || (acc.1.testBit k && decide (1≤n)) || decide (2≤n))) := by
  induction xs generalizing acc with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons]
    obtain ⟨left,right⟩ := ih (coverStep acc v)
    rw [left,right]
    simp only [coverStep,Nat.testBit_or,Nat.testBit_and,List.filter_cons]
    cases a : acc.1.testBit k <;> cases b : acc.2.testBit k <;> cases c : (sourceCode v).testBit k <;>
      simp only [Bool.false_eq_true,↓reduceIte,List.length_cons]
    all_goals generalize (vs.filter (fun v => (sourceCode v).testBit k)).length=n
    all_goals rcases n with _|⟨_|n⟩ <;> simp


theorem duplicate_bit (vs : List Nat) (k : Nat) :
    (duplicate vs).testBit k = decide (2≤(vs.filter (fun v => (sourceCode v).testBit k)).length) := by
  simpa [duplicate] using (fold_state vs (0,0) k).2

def privateMask (vs : List Nat) (v : Nat) := sourceCode v &&& (full 144 ^^^ duplicate vs)

private theorem same_of_short {α : Type} {xs : List α} (h : xs.length≤1) {a b : α}
    (ha : a∈xs) (hb : b∈xs) : a=b := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    have empty : xs=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_cons,Nat.succ_le_succ_iff,Nat.le_zero] using h)
    subst xs
    exact (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm

theorem private_cell {ws : List Signal} (ok : safe ws) (s : Signal) (hs : s∈ws) (i j : Fin 12)
    (hit : (privateMask (ws.map Prod.fst) s.1).testBit (12*i.val+j.val)=true) :
    Private ws s i j := by
  let k := 12*i.val+j.val
  have hk : k<144 := by dsimp [k]; omega
  have mask : (full 144).testBit k=true := by
    change ((1 <<< 144)-1 : Nat).testBit _=true
    rw [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
  change (sourceCode s.1 &&& (full 144 ^^^ duplicate (ws.map Prod.fst))).testBit k=true at hit
  rw [Nat.testBit_and,Bool.and_eq_true,Nat.testBit_xor,mask] at hit
  have ownBit := hit.1
  have few : (duplicate (ws.map Prod.fst)).testBit k=false := by simpa using hit.2
  rw [duplicate_bit] at few
  let test := fun x : Signal => (sourceCode x.1).testBit k
  let selected := ws.filter test
  have len : selected.length ≤ 1 := by
    have eq : (ws.map Prod.fst).filter (fun v => (sourceCode v).testBit k) = selected.map Prod.fst := by
      simp [selected,test,List.filter_map,Function.comp_def]
    rw [eq,List.length_map] at few
    have := of_decide_eq_false few
    omega
  refine ⟨hs,?_⟩
  intro w hw sep
  exact same_of_short len (List.mem_filter.mpr ⟨hw,(source_bits w.1 (ok w hw) i j).mpr sep⟩)
    (List.mem_filter.mpr ⟨hs,ownBit⟩)

theorem prepare_fields {ws : List Signal} (masks : List Nat) {d : Digit}
    (hd : d∈prepare (ws.map Prod.fst) masks) :
    d.cover = sourceCode d.word ∧
    d.yes = rowsOf (privateMask (ws.map Prod.fst) d.word) ∧
    d.no = colsOf (privateMask (ws.map Prod.fst) d.word) := by
  obtain ⟨⟨⟨v,mask⟩,i⟩,_,rfl⟩ := List.mem_map.mp hd
  exact ⟨rfl,rfl,rfl⟩

theorem prepare_pos {ws : List Signal} (ok : safe ws) (s : Signal) (hs : s∈ws) (masks : List Nat)
    {d : Digit} (hd : d∈prepare (ws.map Prod.fst) masks) (same : d.word=s.1) {i : Fin 12}
    (hit : d.yes.testBit i.val=true) : ∃ j : Fin 12, Private ws s i j := by
  rw [(prepare_fields masks hd).2.1,same] at hit
  obtain ⟨j,atJ⟩ := row_bit i hit
  exact ⟨j,private_cell ok s hs i j atJ⟩

theorem prepare_neg {ws : List Signal} (ok : safe ws) (s : Signal) (hs : s∈ws) (masks : List Nat)
    {d : Digit} (hd : d∈prepare (ws.map Prod.fst) masks) (same : d.word=s.1) {j : Fin 12}
    (hit : d.no.testBit j.val=true) : ∃ i : Fin 12, Private ws s i j := by
  rw [(prepare_fields masks hd).2.2,same] at hit
  have upper : privateMask (ws.map Prod.fst) s.1 < 2^144 :=
    Nat.and_le_left.trans_lt ((source_eq s.1) ▸ Packed.cover_bound (ok s hs))
  obtain ⟨i,atI⟩ := col_bit upper j hit
  exact ⟨i,private_cell ok s hs i j atI⟩

end Live3210.SubsetCheck
namespace Live3210.SubsetCheck

structure Requirement where
  left : Nat
  right : Nat
  prior : Nat
  deriving Repr

def picked (axes : List Digit) (m : Nat) := axes.zipIdx.foldl
  (fun a z => if m.testBit z.2 then a ||| z.1.index else a) 0

def outsideCode (ws axes : List Digit) (m : Nat) : Nat :=
  let kept := picked axes m
  ws.foldl (fun a z => if z.index &&& kept == 0 then a ||| z.cover else a) 0

def ruleOK (ws axes : List Digit) (r : Requirement) : Bool :=
  match axes[r.left]?, axes[r.right]? with
  | some a, some b =>
    a.index != b.index &&
      ((a.yes &&& b.yes != 0 && a.no &&& b.no != 0) ||
        (let req := rowCode a.yes b.no ||| rowCode b.yes a.no
         req &&& ((2^144-1) ^^^ outsideCode ws axes r.prior) != 0))
  | _,_ => false

def Conforms (ranks : List Nat) (r : Requirement) : Prop :=
  ∀ a b, ranks[r.left]?=some a → ranks[r.right]?=some b →
    a≠b ∨ ∃ i z, r.prior.testBit i=true ∧ ranks[i]?=some z ∧ z≤a

structure Pattern where
  count : Nat
  colors : Nat
  rules : List Requirement

structure Chart where
  size : Nat
  univ : Nat
  axes : List (List Nat)

def rep (v sz cnt : Nat) := (List.range cnt).foldl (fun a k => a ||| (v <<< (sz*k))) 0

def chart (colors : Nat) : Nat → Chart
  | 0 => ⟨1,1,[]⟩
  | k+1 =>
    let old := chart colors k
    let newest := (List.range colors).map (fun r => old.univ <<< (old.size*r))
    ⟨old.size*colors, rep old.univ old.size colors,
      newest :: old.axes.map (fun x => x.map (fun m => rep m old.size colors))⟩

def lor (xs : List Nat) := xs.foldl (fun a w => a ||| w) 0

def prevBits (axes : List (List Nat)) (mask color : Nat) := lor <|
  axes.zipIdx.map (fun (row,i) => if mask.testBit i then lor (row.take (color+1)) else 0)

def allowed (t : Chart) (r : Requirement) : Nat :=
  match t.axes[r.left]?, t.axes[r.right]? with
  | some left,some right => lor <| left.zipIdx.map fun (a,i) =>
      a &&& (lor <| right.zipIdx.map fun (b,j) =>
        if i==j then b &&& prevBits t.axes r.prior i else b)
  | _,_ => t.univ

def impossible (p : Pattern) : Bool :=
  let t := chart p.colors p.count
  p.rules.foldl (fun acc rule => acc &&& allowed t rule) t.univ == 0

end Live3210.SubsetCheck
namespace Live3210.SubsetCheck
open Ordered Blocks

def signalOf (ws : List Signal) (x : Digit) := ws.getD x.index.log2 (0,0)

theorem prepare_length (ws : List Signal) (masks : List Nat) (equal : masks.length=ws.length) :
    (prepare (ws.map Prod.fst) masks).length=ws.length := by simp [prepare,equal]

theorem prepare_at (ws : List Signal) (masks : List Nat) (equal : masks.length=ws.length)
    (k : Nat) (hk : k<ws.length) :
    let ds := prepare (ws.map Prod.fst) masks
    let digit := ds[k]'(by rwa [prepare_length _ _ equal])
    digit.index=2^k ∧ digit.word=ws[k].1 := by
  simp [prepare,List.getElem_zipIdx,List.getElem_zip, Nat.shiftLeft_eq]

theorem digit_at {ws : List Signal} {masks : List Nat} (equal : masks.length=ws.length)
    {x : Digit} (hx : x∈prepare (ws.map Prod.fst) masks) :
    ∃ (k : Nat) (hk : k<ws.length), x.index=2^k ∧ x.word=ws[k].1 ∧ signalOf ws x=ws[k] := by
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hx
  have bound : k<ws.length := by rwa [prepare_length _ _ equal] at hk
  obtain ⟨ix,word⟩ := prepare_at ws masks equal k bound
  subst x
  exact ⟨k,bound,ix,word,by simp [signalOf,ix,List.getElem?_eq_getElem bound]⟩

private theorem digit_of {ws : List Signal} {masks : List Nat} (equal : masks.length=ws.length)
    {v : Signal} (hv : v∈ws) : ∃ x∈prepare (ws.map Prod.fst) masks, signalOf ws x=v := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hv
  let ds := prepare (ws.map Prod.fst) masks
  have h : k<ds.length := by rwa [prepare_length _ _ equal]
  obtain ⟨ix,_⟩ := prepare_at ws masks equal k hk
  exact ⟨ds[k],List.getElem_mem h,by simp [signalOf,show ds[k].index=2^k from ix,List.getElem?_eq_getElem hk]⟩

private theorem exists_bit {v n : Nat} (size : v<2^n) (on : v≠0) : ∃ i : Fin n, v.testBit i.val=true := by
  by_contra no
  apply on
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k<n
  · cases bit : v.testBit k with
    | false => simp
    | true => exact False.elim (no ⟨⟨k,hk⟩,bit⟩)
  · simp [Nat.testBit_lt_two_pow (size.trans_le (Nat.pow_le_pow_right (by decide) (by omega : n≤k)))]

private theorem rows_bound (v : Nat) : rowsOf v<2^12 := Nat.lt_succ_of_le Nat.and_le_right

private theorem cols_bound (v : Nat) : colsOf v<2^12 := Nat.lt_succ_of_le Nat.and_le_right

private theorem and_witness {a b : Nat} (bound : a<2^12) (nz : a &&& b ≠ 0) :
    ∃ i : Fin 12, a.testBit i.val=true ∧ b.testBit i.val=true := by
  obtain ⟨i,h⟩ := exists_bit (Nat.and_le_left.trans_lt bound : a &&& b < 2^12) nz
  exact ⟨i,by simpa using h⟩

def rankOf {ws : List Signal} {d} (c : Coloring ws d) (s : Digit) := c.assign (signalOf ws s)

private theorem conflict_rule {ws : List Signal} {masks : List Nat} (equal : masks.length=ws.length)
    (nd : ws.Nodup) (bound : safe ws) {a b : Digit}
    (ha : a∈prepare (ws.map Prod.fst) masks) (hb : b∈prepare (ws.map Prod.fst) masks)
    (ne : a.index≠b.index) (p : a.yes &&& b.yes≠0) (q : a.no &&& b.no≠0) :
    Conflict ws (signalOf ws a) (signalOf ws b) := by
  obtain ⟨ia,hia,ai,aw,asig⟩ := digit_at equal ha
  obtain ⟨ib,hib,bi,bw,bsig⟩ := digit_at equal hb
  have distinct : signalOf ws a ≠ signalOf ws b := by
    rw [asig,bsig]
    intro eq
    have ij : ia=ib := Fin.val_eq_of_eq ((List.nodup_iff_injective_getElem.mp nd) (a₁:=⟨ia,hia⟩) (a₂:=⟨ib,hib⟩) eq)
    exact ne (ai.trans ((congrArg (fun n : Nat => 2^n) ij).trans bi.symm))
  obtain ⟨_,py,ny⟩ := prepare_fields masks ha
  obtain ⟨i,ap,bp⟩ := and_witness (py ▸ rows_bound _) p
  obtain ⟨j,an,bn⟩ := and_witness (ny ▸ cols_bound _) q
  obtain ⟨qa,ca⟩ := prepare_pos bound ws[ia] (List.getElem_mem hia) masks ha aw ap
  obtain ⟨qb,cb⟩ := prepare_pos bound ws[ib] (List.getElem_mem hib) masks hb bw bp
  obtain ⟨pa,da⟩ := prepare_neg bound ws[ia] (List.getElem_mem hia) masks ha aw an
  obtain ⟨pb,db⟩ := prepare_neg bound ws[ib] (List.getElem_mem hib) masks hb bw bn
  exact ⟨distinct,i,qa,qb,j,pa,pb,asig ▸ ca,bsig ▸ cb,asig ▸ da,bsig ▸ db⟩

theorem rowCode_bit (a b : Nat) (bound : b<4096) (p q : Fin 12) :
    (rowCode a b).testBit (12*p.val+q.val) = (a.testBit p.val && b.testBit q.val) :=
  Packed.product_bits a b bound p q

private theorem fold_masks {α : Type} (ws : List α) (value : α → Nat) (test : α → Bool) (acc bit : Nat) :
    ((ws.foldl (fun a x => if test x then a ||| value x else a) acc).testBit bit=true) ↔
      acc.testBit bit=true ∨ ∃ x∈ws, test x=true ∧ (value x).testBit bit=true := by
  induction ws generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    cases choice : test x <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.testBit_or,
      Bool.or_eq_true,List.mem_cons] <;> grind

private theorem picked_source {axes : List Digit} {m k : Nat} (on : (picked axes m).testBit k=true) :
    ∃ i x, axes[i]?=some x ∧ m.testBit i=true ∧ x.index.testBit k=true := by
  have h := (fold_masks axes.zipIdx (fun z => z.1.index) (fun z => m.testBit z.2) 0 k).mp on
  rcases h with no|⟨⟨x,i⟩,mem,sel,bit⟩
  · simp at no
  · exact ⟨i,x,List.mk_mem_zipIdx_iff_getElem?.mp mem,sel,bit⟩

private theorem missed_point {xs : List Signal} {masks : List Nat} {a b : Digit}
    (ha : a∈prepare (xs.map Prod.fst) masks) (hb : b∈prepare (xs.map Prod.fst) masks) (outside : Nat)
    (absent : (rowCode a.yes b.no ||| rowCode b.yes a.no) &&& ((2^144-1) ^^^ outside) ≠ 0) :
    ∃ p q : Fin 12, ((a.yes.testBit p.val=true ∧ b.no.testBit q.val=true) ∨
        (b.yes.testBit p.val=true ∧ a.no.testBit q.val=true)) ∧
      outside.testBit (12*p.val+q.val)=false := by
  have boundA : a.no<4096 := (prepare_fields masks ha).2.2 ▸ cols_bound _
  have boundB : b.no<4096 := (prepare_fields masks hb).2.2 ▸ cols_bound _
  let u := rowCode a.yes b.no ||| rowCode b.yes a.no
  have upper : u<2^144 := Nat.or_lt_two_pow (Packed.product_bound a.yes b.no boundB) (Packed.product_bound b.yes a.no boundA)
  obtain ⟨idx,hit⟩ := exists_bit (Nat.and_le_left.trans_lt upper : u &&& ((2^144-1) ^^^ outside) < 2^144) absent
  let p : Fin 12 := ⟨idx.val/12,by omega⟩
  let q : Fin 12 := ⟨idx.val % 12,Nat.mod_lt _ (by decide)⟩
  have key : idx.val=12*p.val+q.val := by dsimp [p,q]; omega
  have inside : (2^144-1 : Nat).testBit idx.val=true := by
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true idx.isLt
  rw [Nat.testBit_and,Bool.and_eq_true,Nat.testBit_xor,inside] at hit
  have neg : outside.testBit idx.val=false := by simpa using hit.2
  refine ⟨p,q,?_,key ▸ neg⟩
  have yes := hit.1
  simpa only [u,key,Nat.testBit_or,Bool.or_eq_true,rowCode_bit _ _ boundA,rowCode_bit _ _ boundB,
    Bool.and_eq_true] using yes

private theorem cross_source {ws : List Signal} {masks : List Nat} (equal : masks.length=ws.length)
    (bound : safe ws) {a b : Digit}
    (ha : a∈prepare (ws.map Prod.fst) masks) (hb : b∈prepare (ws.map Prod.fst) masks)
    {d : Nat} (c : Coloring ws d) (same : rankOf c a=rankOf c b) (p q : Fin 12)
    (hp : a.yes.testBit p.val=true) (hq : b.no.testBit q.val=true) :
    ∃ v∈ws, c.assign v≤rankOf c a ∧ covers v.1 p q := by
  obtain ⟨ia,hia,_,aw,ar⟩ := digit_at equal ha
  obtain ⟨ib,hib,_,bw,br⟩ := digit_at equal hb
  obtain ⟨qa,ap⟩ := prepare_pos bound ws[ia] (List.getElem_mem hia) masks ha aw hp
  obtain ⟨pb,bq⟩ := prepare_neg bound ws[ib] (List.getElem_mem hib) masks hb bw hq
  unfold rankOf at same ⊢
  rw [ar,br] at same
  rw [ar]
  exact c.cross ap bq same

private theorem supplied {ws : List Signal} {masks : List Nat} (equal : masks.length=ws.length)
    (bound : safe ws) (axes : List Digit) (sub : axes⊆prepare (ws.map Prod.fst) masks)
    (prior : Nat) (p q : Fin 12) (u : Signal) (hu : u∈ws) (cell : covers u.1 p q)
    (absent : (outsideCode (prepare (ws.map Prod.fst) masks) axes prior).testBit (12*p.val+q.val)=false) :
    ∃ i x, axes[i]?=some x ∧ prior.testBit i=true ∧ signalOf ws x=u := by
  let ds := prepare (ws.map Prod.fst) masks
  let k := 12*p.val+q.val
  obtain ⟨digit,mem,rep⟩ := digit_of equal hu
  obtain ⟨id,valid,ix,word,signal⟩ := digit_at equal mem
  have wordRep : digit.word=u.1 := by rw [←rep,signal,word]
  have good : digit.cover.testBit k=true := by
    rw [(prepare_fields masks mem).1,wordRep]
    exact (source_bits _ (bound u hu) _ _).mpr cell
  have inside : (picked axes prior).testBit id=true := by
    cases test : (picked axes prior).testBit id with
    | true => rfl
    | false =>
      have zero : digit.index &&& picked axes prior=0 := by
        apply Nat.eq_of_testBit_eq; intro j
        rw [ix,Nat.testBit_and,Nat.testBit_two_pow]
        by_cases eq : id=j
        · subst j; simp [test]
        · simp [eq]
      have on := (fold_masks ds Digit.cover (fun d => d.index &&& picked axes prior == 0) 0 k).mpr
        (Or.inr ⟨digit,mem,by simp [zero],good⟩)
      exact False.elim (Bool.noConfusion (absent.symm.trans on))
  obtain ⟨i,x,atI,selected,xbit⟩ := picked_source inside
  have fullMember := sub (List.mem_of_getElem? atI)
  obtain ⟨j,hj,xix,_,xsig⟩ := digit_at equal fullMember
  rw [xix,Nat.testBit_two_pow,decide_eq_true_eq] at xbit
  subst j
  exact ⟨i,x,atI,selected,xsig.trans (signal.symm.trans rep)⟩

theorem rule_conforms {ws : List Signal} {masks : List Nat} (equal : masks.length=ws.length)
    (nd : ws.Nodup) (bound : safe ws) (axes : List Digit)
    (sub : axes⊆prepare (ws.map Prod.fst) masks) {d : Nat} (c : Coloring ws d) (r : Requirement)
    (pass : ruleOK (prepare (ws.map Prod.fst) masks) axes r = true) :
    Conforms (axes.map (rankOf c)) r := by
  intro ra rb readA readB
  cases atA : axes[r.left]? with
  | none => simp [ruleOK,atA] at pass
  | some a =>
    cases atB : axes[r.right]? with
    | none => simp [ruleOK,atA,atB] at pass
    | some b =>
      simp only [List.getElem?_map,atA,atB,Option.map_some,Option.some.injEq] at readA readB
      subst ra; subst rb
      by_cases same : rankOf c a=rankOf c b
      · right
        have ha := sub (List.mem_of_getElem? atA)
        have hb := sub (List.mem_of_getElem? atB)
        simp only [ruleOK,atA,atB,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne] at pass
        obtain ⟨ne,conf|cross⟩ := pass
        · exact False.elim ((c.edges _ _ (conflict_rule equal nd bound ha hb ne conf.1 conf.2)) same)
        · obtain ⟨p,q,hit,missing⟩ := missed_point ha hb _ cross
          have existsSrc : ∃ v∈ws, c.assign v≤rankOf c a ∧ covers v.1 p q := by
            rcases hit with ⟨ap,bq⟩|⟨bp,aq⟩
            · exact cross_source equal bound ha hb c same p q ap bq
            · rw [same]; exact cross_source equal bound hb ha c same.symm p q bp aq
          obtain ⟨u,hu,low,cell⟩ := existsSrc
          obtain ⟨i,x,read,selected,eq⟩ := supplied equal bound axes sub _ p q u hu cell missing
          exact ⟨i,c.assign u,selected,by simp [List.getElem?_map,read,rankOf,eq],low⟩
      · exact Or.inl same

end Live3210.SubsetCheck

namespace Live3210.Search
open Ordered Blocks

abbrev Screen := Nat → List Wire → Bool
def Sound (screen : Screen) := ∀ (d : Nat) (ws : List Signal), ws.Nodup → safe ws →
  Nonempty (Coloring ws d) → screen d (ws.map pack)=true

def screened (screen : Screen) : Nat → Nat → List Wire → Nat → Nat → Nat
  | 0,d,ws,_,_ => if screen d ws then 1 else 0
  | h+1,d,ws,limit,lw =>
    if screen d ws then
      if ws.any (fun w => w.value == 4095) then 1 else next (screened screen h (d-1)) ws d limit lw
    else 0

private theorem screen_bound {g : Gate} {s t} (m : Enables g s t)
    (bound : ∀ v∈s, v.1<2^24) : ∀ v∈t, v.1<2^24 := by
  have ha := bound _ m.left
  have hb := bound _ m.right
  have out : g.output.1<2^24 := by
    simp only [Gate.output,combine]
    split
    · exact Nat.and_lt_two_pow _ hb
    · exact Nat.or_lt_two_pow ha hb
  obtain ⟨k,sub,rfl⟩ := m.update
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl|hold
  · exact out
  · rcases Finset.mem_union.mp hold with other|kept
    · exact bound _ (Finset.mem_erase.mp (Finset.mem_erase.mp other).2).2
    · rcases (show v=g.left ∨ v=g.right by simpa using sub kept) with rfl|rfl <;> assumption

private theorem screen_empty {s t : Finset Signal} (path : Route [] s t) : s=t := by
  cases path; rfl

theorem screened_route (screen : Screen) (sound : Sound screen) (h d : Nat) (ws : List Signal) (gs : List Gate) (y : Signal)
    (limit lw : Nat) (val : y.1=4095) (route : Route gs ws.toFinset {y})
    (nd : ws.Nodup) (bound : safe ws) (cost : gs.length≤d)
    (ord : gs.Pairwise strict) (afterKey : ∀ g∈gs, later g.output limit lw) :
    0<screened screen h d (ws.map pack) limit lw := by
  induction h generalizing d gs ws limit lw with
  | zero => simp [screened,sound d ws nd bound (coloring_of_route route nd bound val cost)]
  | succ h ih =>
    rw [screened,ite_eq_left (sound d ws nd bound (coloring_of_route route nd bound val cost))]
    split
    · decide
    case isFalse miss =>
      cases gs with
      | nil =>
        have equal := screen_empty route
        have mem : y∈ws := List.mem_toFinset.mp (equal ▸ Finset.mem_singleton_self _)
        apply False.elim
        exact miss (List.any_eq_true.mpr ⟨pack y,List.mem_map_of_mem mem,by simp [pack,val]⟩)
      | cons g gs =>
        cases route with
        | next m tail =>
          have last : separated {y} := by simpa only [separated,Finset.image_singleton,val] using target_sep
          have tSep := tail.back last
          have tCard := tail.budget
          simp only [Finset.card_singleton] at tCard
          simp only [List.length_cons] at cost
          have pair := List.pairwise_cons.mp ord
          have newBound := screen_bound m (fun v hv => bound v (List.mem_toFinset.mp hv))
          apply next_pos _ m nd d limit lw (afterKey g List.mem_cons_self) (by omega) tSep newBound
          intro vs rep dis
          apply ih (d-1) vs gs g.output.2 g.output.1 (rep ▸ tail) dis
            (fun v hv => newBound v (rep ▸ List.mem_toFinset.mpr hv)) (by omega) pair.2
          intro k hk
          rcases pair.1 k hk with lt|⟨same,lt⟩
          · exact Or.inl lt
          · exact Or.inr ⟨same,lt⟩

def checkedRun (screen : Screen) (h : Nat) :=
  screened screen h 14 ((starts 9).map pack) 0 0 + screened screen h 14 ((starts 10).map pack) 0 0

theorem program_checked (screen : Screen) (sound : Sound screen) (h : Nat) (p : List Instruction) (cost : Nat) (len : p.length≤14)
    (hit : (4095,cost)∈p.foldl scored initialScored) : 0<checkedRun screen h := by
  obtain ⟨s,gs,y,init,budget,sorted,val,route⟩ := route_for_target cost len hit
  have startKey : ∀ g∈gs, later g.output 0 0 := by
    intro g _; exact Or.inl (by simp [Gate.output])
  have first (n : Nat) (hs : (starts n).toFinset=s) (nd : (starts n).Nodup) (ok : safe (starts n)) :=
    screened_route screen sound h 14 (starts n) gs y 0 0 val (hs ▸ route) nd ok budget sorted startKey
  rcases init with eq|eq
  · have u := first 9 (by rw [eq]; decide +kernel) (by decide +kernel) (by unfold safe; decide +kernel)
    exact Nat.add_pos_left u _
  · have u := first 10 (by rw [eq]; decide +kernel) (by decide +kernel) (by unfold safe; decide +kernel)
    exact Nat.add_pos_right _ u

end Live3210.Search

namespace Live3210.SubsetCheck

private theorem orFold {α} (xs : List α) (f : α → Nat) (pos init : Nat)
    (yes : init.testBit pos = true ∨ ∃ x∈xs, (f x).testBit pos = true) :
    (xs.foldl (fun a x => a ||| f x) init).testBit pos = true := by
  induction xs generalizing init with
  | nil => simpa using yes
  | cons y ys ih =>
    apply ih
    rcases yes with hy|⟨x,hx,hxv⟩
    · exact Or.inl (by simp [hy])
    · rcases List.mem_cons.mp hx with rfl|h
      · exact Or.inl (by simp [hxv])
      · exact Or.inr ⟨x,h,hxv⟩

private theorem lor_mem {xs : List Nat} {w i} (hm : w∈xs) (on : Nat.testBit w i=true) :
    (lor xs).testBit i=true := orFold xs id i 0 (Or.inr ⟨w,hm,on⟩)

private theorem shift_hit {v i j : Nat} (on : v.testBit i=true) :
    (v <<< j).testBit (i+j)=true := by simp [Nat.testBit_shiftLeft,on]

private theorem rep_hit {v sz colors d i} (hd : d<colors) (h : Nat.testBit v i=true) :
    (rep v sz colors).testBit (i+sz*d)=true :=
  orFold _ _ _ _ (Or.inr ⟨d,List.mem_range.mpr hd,shift_hit h⟩)

def Shows (t : Chart) (ranks : List Nat) (i : Nat) :=
  t.univ.testBit i=true ∧ ∀ (j r : Nat), ranks[j]?=some r →
    ∃ (row : List Nat) (w : Nat), t.axes[j]?=some row ∧ row[r]?=some w ∧ w.testBit i=true

private theorem chart_shows (colors : Nat) (ranks : List Nat) (fit : ∀ r∈ranks, r<colors) :
    ∃ i, Shows (chart colors ranks.length) ranks i := by
  induction ranks with
  | nil =>
    refine ⟨0,by simp [chart],?_⟩
    intro j r h
    simp at h
  | cons d ranks ih =>
    have hd := fit d List.mem_cons_self
    obtain ⟨i,huniv,hrows⟩ := ih (fun r hr => fit r (List.mem_cons_of_mem _ hr))
    let t := chart colors ranks.length
    refine ⟨i+t.size*d,rep_hit hd huniv,?_⟩
    intro j r atR
    cases j with
    | zero =>
      have eq : d=r := by simpa using atR
      subst r
      refine ⟨_,_,rfl,?_,shift_hit huniv⟩
      simp [hd,t]
    | succ j =>
      obtain ⟨row,w,ar,wr,bit⟩ := hrows j r (by simpa using atR)
      refine ⟨row.map (fun v => rep v t.size colors),rep w t.size colors,?_,?_,rep_hit hd bit⟩
      · simpa [chart,t,List.getElem?_map] using congrArg
          (fun o : Option (List Nat) => o.map (fun rs => rs.map (fun v => rep v t.size colors))) ar
      · simp [List.getElem?_map,wr]

private theorem prev_hit {t : Chart} {ranks : List Nat} {i slot c color prior}
    (seen : Shows t ranks i) (yes : Nat.testBit prior slot=true) (ar : ranks[slot]?=some c)
    (le : c≤color) : (prevBits t.axes prior color).testBit i=true := by
  obtain ⟨row,w,atRow,atW,on⟩ := seen.2 slot c ar
  apply lor_mem (List.mem_map.mpr ⟨(row,slot),List.mk_mem_zipIdx_iff_getElem?.mpr atRow,rfl⟩)
  simp only [yes,↓reduceIte]
  apply lor_mem _ on
  apply List.mem_of_getElem? (i:=c)
  rw [List.getElem?_take]
  simpa [show c < color+1 by omega] using atW

private theorem chart_length (colors n) : (chart colors n).axes.length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chart,ih]

private theorem allowed_hit {i t ranks} (seen : Shows t ranks i)
    (sameSize : t.axes.length=ranks.length) (r : Requirement) (ok : Conforms ranks r) :
    (allowed t r).testBit i=true := by
  by_cases hl : r.left<ranks.length
  · by_cases hr : r.right<ranks.length
    · let a := ranks[r.left]
      let b := ranks[r.right]
      have ha : ranks[r.left]?=some a := List.getElem?_eq_getElem hl
      have hb : ranks[r.right]?=some b := List.getElem?_eq_getElem hr
      obtain ⟨left,wa,leftAt,hasA,onA⟩ := seen.2 _ _ ha
      obtain ⟨right,wb,rightAt,hasB,onB⟩ := seen.2 _ _ hb
      simp only [allowed,leftAt,rightAt]
      apply lor_mem (List.mem_map.mpr ⟨(wa,a),List.mk_mem_zipIdx_iff_getElem?.mpr hasA,rfl⟩)
      rw [Nat.testBit_and,onA,Bool.true_and]
      apply lor_mem (List.mem_map.mpr ⟨(wb,b),List.mk_mem_zipIdx_iff_getElem?.mpr hasB,rfl⟩)
      by_cases eq : a=b
      · obtain ⟨slot,c,chosen,atC,le⟩ := (ok a b ha hb).resolve_left (fun ne => ne eq)
        simp [eq,onB,prev_hit seen chosen atC (show c≤b from eq ▸ le)]
      · simp [eq,onB]
    · have miss := List.getElem?_eq_none (show t.axes.length≤r.right by omega)
      cases h : t.axes[r.left]? <;> simpa [allowed,h,miss] using seen.1
  · have miss := List.getElem?_eq_none (show t.axes.length≤r.left by omega)
    simpa [allowed,miss] using seen.1

theorem impossible_sound (p : Pattern) (bad : impossible p=true)
    (ranks : List Nat) (count : ranks.length=p.count) (fits : ∀ r∈ranks, r<p.colors)
    (ok : ∀ r∈p.rules, Conforms ranks r) : False := by
  obtain ⟨i,seen⟩ := chart_shows p.colors ranks fits
  rw [count] at seen
  let t := chart p.colors p.count
  have sz : t.axes.length=ranks.length := (chart_length ..).trans count.symm
  have keep (rs : List Requirement) (init : Nat) (start : init.testBit i=true)
      (guard : ∀ r∈rs, Conforms ranks r) :
      (rs.foldl (fun a r => a &&& allowed t r) init).testBit i=true := by
    induction rs generalizing init with
    | nil => exact start
    | cons r rs ih =>
      have okr : (allowed t r).testBit i=true := allowed_hit seen sz r (guard r List.mem_cons_self)
      exact ih _ (by rw [Nat.testBit_and,start,okr]; rfl)
        (fun x hx => guard x (List.mem_cons_of_mem _ hx))
  have final := keep p.rules t.univ seen.1 ok
  have eq : p.rules.foldl (fun a r => a &&& allowed t r) t.univ = 0 := of_decide_eq_true bad
  simp [eq] at final

end Live3210.SubsetCheck

namespace Live3210.SubsetCheck

def decodeReq (v : Nat) : Requirement := ⟨v % 8,(v/8)%8,v/64⟩
structure Prohibited where
  pattern : Pattern
  checked : impossible pattern = true
def ob0_0 : Pattern := ⟨2,1,[8].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob0_0_bad : impossible ob0_0=true := by decide +kernel
def ob1_0 : Pattern := ⟨4,2,[16,152,529,25,26].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_0_bad : impossible ob1_0=true := by decide +kernel
def ob1_1 : Pattern := ⟨4,2,[16,280,529,25,26].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_1_bad : impossible ob1_1=true := by decide +kernel
def ob1_2 : Pattern := ⟨4,2,[16,152,81,25,26].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_2_bad : impossible ob1_2=true := by decide +kernel
def ob1_3 : Pattern := ⟨4,2,[8,528,280,529,281,26].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_3_bad : impossible ob1_3=true := by decide +kernel
def ob1_4 : Pattern := ⟨4,2,[520,528,24,17,281,154].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_4_bad : impossible ob1_4=true := by decide +kernel
def ob1_5 : Pattern := ⟨4,2,[8,528,152,529,281,26].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_5_bad : impossible ob1_5=true := by decide +kernel
def ob1_6 : Pattern := ⟨3,2,[8,16,17].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_6_bad : impossible ob1_6=true := by decide +kernel
def ob1_7 : Pattern := ⟨4,2,[8,144,280,529,89,26].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob1_7_bad : impossible ob1_7=true := by decide +kernel
def ob2_0 : Pattern := ⟨5,3,[520,1040,24,32,17,25,289,154,34,163,291].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_0_bad : impossible ob2_0=true := by decide +kernel
def ob2_1 : Pattern := ⟨6,3,[16,152,32,1064,2065,25,2081,41,26,546,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_1_bad : impossible ob2_1=true := by decide +kernel
def ob2_2 : Pattern := ⟨5,3,[520,1040,24,32,17,25,97,545,90,1050,34,99].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_2_bad : impossible ob2_2=true := by decide +kernel
def ob2_3 : Pattern := ⟨6,3,[16,1048,32,168,2065,25,2081,41,26,546,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_3_bad : impossible ob2_3=true := by decide +kernel
def ob2_4 : Pattern := ⟨6,3,[16,24,544,168,2065,2073,33,41,1050,2082,42,35,1067,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_4_bad : impossible ob2_4=true := by decide +kernel
def ob2_5 : Pattern := ⟨6,3,[24,544,552,2065,2073,2081,41,1050,34,42,35,171,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_5_bad : impossible ob2_5=true := by decide +kernel
def ob2_6 : Pattern := ⟨6,3,[520,1040,24,288,168,2065,2073,2081,41,1050,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_6_bad : impossible ob2_6=true := by decide +kernel
def ob2_7 : Pattern := ⟨6,3,[1040,24,288,168,1041,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_7_bad : impossible ob2_7=true := by decide +kernel
def ob2_8 : Pattern := ⟨6,3,[2072,288,40,1041,25,289,553,1050,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_8_bad : impossible ob2_8=true := by decide +kernel
def ob2_9 : Pattern := ⟨6,3,[1040,24,288,168,2065,2073,289,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_9_bad : impossible ob2_9=true := by decide +kernel
def ob2_10 : Pattern := ⟨5,3,[8,16,152,288,81,25,545,1050,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_10_bad : impossible ob2_10=true := by decide +kernel
def ob2_11 : Pattern := ⟨6,3,[280,2080,40,1041,1049,33,1065,26,546,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_11_bad : impossible ob2_11=true := by decide +kernel
def ob2_12 : Pattern := ⟨6,3,[2072,2080,40,529,25,289,553,1050,34,1066,163,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_12_bad : impossible ob2_12=true := by decide +kernel
def ob2_13 : Pattern := ⟨6,3,[528,280,32,1064,529,2073,2081,41,26,98,170,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_13_bad : impossible ob2_13=true := by decide +kernel
def ob2_14 : Pattern := ⟨6,3,[16,1048,2080,168,2065,281,2081,41,26,546,170,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_14_bad : impossible ob2_14=true := by decide +kernel
def ob2_15 : Pattern := ⟨6,3,[16,152,2080,40,1041,25,33,553,2074,34,1066,2083,43,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_15_bad : impossible ob2_15=true := by decide +kernel
def ob2_16 : Pattern := ⟨6,3,[2072,2080,40,529,1049,33,1065,26,162,106,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_16_bad : impossible ob2_16=true := by decide +kernel
def ob2_17 : Pattern := ⟨6,3,[16,24,160,552,2065,2073,33,41,1050,34,1066,2083,43,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_17_bad : impossible ob2_17=true := by decide +kernel
def ob2_18 : Pattern := ⟨6,3,[1032,152,32,296,2065,25,2081,1065,26,98,42,163,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_18_bad : impossible ob2_18=true := by decide +kernel
def ob2_19 : Pattern := ⟨6,3,[152,2080,40,529,25,289,553,1050,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_19_bad : impossible ob2_19=true := by decide +kernel
def ob2_20 : Pattern := ⟨6,3,[2056,1040,24,288,168,2065,2073,289,41,90,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_20_bad : impossible ob2_20=true := by decide +kernel
def ob2_21 : Pattern := ⟨6,3,[1040,24,288,552,2065,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_21_bad : impossible ob2_21=true := by decide +kernel
def ob2_22 : Pattern := ⟨6,3,[1040,280,32,1064,529,281,2081,41,26,546,170,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_22_bad : impossible ob2_22=true := by decide +kernel
def ob2_23 : Pattern := ⟨6,3,[1040,2072,2080,40,1041,25,289,553,154,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_23_bad : impossible ob2_23=true := by decide +kernel
def ob2_24 : Pattern := ⟨6,3,[2056,24,288,296,2065,2073,2081,41,1050,34,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_24_bad : impossible ob2_24=true := by decide +kernel
def ob2_25 : Pattern := ⟨6,3,[2056,2072,2080,40,1041,2073,33,1065,26,34,554,163,43,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_25_bad : impossible ob2_25=true := by decide +kernel
def ob2_26 : Pattern := ⟨6,3,[1040,24,288,168,2065,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_26_bad : impossible ob2_26=true := by decide +kernel
def ob2_27 : Pattern := ⟨6,3,[16,24,544,296,2065,1049,33,41,2074,2082,42,35,1067,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_27_bad : impossible ob2_27=true := by decide +kernel
def ob2_28 : Pattern := ⟨6,3,[1040,1048,32,168,529,2073,2081,41,26,546,170,1066,99,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_28_bad : impossible ob2_28=true := by decide +kernel
def ob2_29 : Pattern := ⟨6,3,[2064,1048,32,296,17,2073,545,553,2074,162,42,35,43,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_29_bad : impossible ob2_29=true := by decide +kernel
def ob2_30 : Pattern := ⟨6,3,[16,24,544,552,2065,2073,33,41,1050,34,554,2083,43,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_30_bad : impossible ob2_30=true := by decide +kernel
def ob2_31 : Pattern := ⟨6,3,[24,288,296,2065,2073,2081,41,1050,34,42,35,171,172,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_31_bad : impossible ob2_31=true := by decide +kernel
def ob2_32 : Pattern := ⟨6,3,[16,152,2080,40,529,25,33,553,26,2082,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_32_bad : impossible ob2_32=true := by decide +kernel
def ob2_33 : Pattern := ⟨6,3,[16,24,544,552,2065,2073,33,41,1050,34,1066,2083,43,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_33_bad : impossible ob2_33=true := by decide +kernel
def ob2_34 : Pattern := ⟨6,3,[1032,152,32,296,2065,25,545,1065,26,2082,42,163,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_34_bad : impossible ob2_34=true := by decide +kernel
def ob2_35 : Pattern := ⟨5,3,[520,528,24,544,17,89,33,90,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_35_bad : impossible ob2_35=true := by decide +kernel
def ob2_36 : Pattern := ⟨6,3,[1032,280,32,296,2065,25,545,1065,26,2082,42,163,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_36_bad : impossible ob2_36=true := by decide +kernel
def ob2_37 : Pattern := ⟨6,3,[2056,24,544,168,2065,2073,2081,41,1050,34,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_37_bad : impossible ob2_37=true := by decide +kernel
def ob2_38 : Pattern := ⟨6,3,[1040,152,2080,40,1041,25,289,105,154,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_38_bad : impossible ob2_38=true := by decide +kernel
def ob2_39 : Pattern := ⟨6,3,[16,152,32,1064,2065,25,545,41,26,2082,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_39_bad : impossible ob2_39=true := by decide +kernel
def ob2_40 : Pattern := ⟨6,3,[1032,24,160,296,2065,1049,33,553,2074,34,42,163,43,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_40_bad : impossible ob2_40=true := by decide +kernel
def ob2_41 : Pattern := ⟨5,3,[1040,1048,32,17,25,97,26,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_41_bad : impossible ob2_41=true := by decide +kernel
def ob2_42 : Pattern := ⟨6,3,[16,280,32,1064,2065,25,2081,41,26,546,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_42_bad : impossible ob2_42=true := by decide +kernel
def ob2_43 : Pattern := ⟨6,3,[1040,24,288,168,2065,89,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_43_bad : impossible ob2_43=true := by decide +kernel
def ob2_44 : Pattern := ⟨6,3,[264,144,2072,32,552,17,281,289,553,154,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_44_bad : impossible ob2_44=true := by decide +kernel
def ob2_45 : Pattern := ⟨5,3,[520,144,24,544,17,89,33,154,1050,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_45_bad : impossible ob2_45=true := by decide +kernel
def ob2_46 : Pattern := ⟨6,3,[264,144,2072,32,552,17,281,289,553,154,98,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_46_bad : impossible ob2_46=true := by decide +kernel
def ob2_47 : Pattern := ⟨6,3,[16,152,2080,40,529,25,33,1065,26,2082,554,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_47_bad : impossible ob2_47=true := by decide +kernel
def ob2_48 : Pattern := ⟨6,3,[2072,288,40,1041,25,289,553,154,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_48_bad : impossible ob2_48=true := by decide +kernel
def ob2_49 : Pattern := ⟨6,3,[16,24,544,296,1041,2073,33,41,2074,2082,42,35,1067,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_49_bad : impossible ob2_49=true := by decide +kernel
def ob2_50 : Pattern := ⟨6,3,[1040,24,288,168,1041,2073,2081,41,90,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_50_bad : impossible ob2_50=true := by decide +kernel
def ob2_51 : Pattern := ⟨6,3,[1032,2064,24,160,296,2065,1049,33,297,2074,2082,42,163,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_51_bad : impossible ob2_51=true := by decide +kernel
def ob2_52 : Pattern := ⟨6,3,[520,152,32,296,2065,25,2081,1065,26,98,42,163,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_52_bad : impossible ob2_52=true := by decide +kernel
def ob2_53 : Pattern := ⟨6,3,[16,280,2080,40,529,25,33,1065,26,2082,554,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_53_bad : impossible ob2_53=true := by decide +kernel
def ob2_54 : Pattern := ⟨5,3,[264,528,24,544,17,89,33,90,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_54_bad : impossible ob2_54=true := by decide +kernel
def ob2_55 : Pattern := ⟨6,3,[520,528,24,160,552,1041,89,33,297,90,2082,42,163,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_55_bad : impossible ob2_55=true := by decide +kernel
def ob2_56 : Pattern := ⟨6,3,[2056,1048,32,1064,2065,2073,2081,41,26,546,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_56_bad : impossible ob2_56=true := by decide +kernel
def ob2_57 : Pattern := ⟨6,3,[520,1040,24,288,168,2065,89,2081,41,90,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_57_bad : impossible ob2_57=true := by decide +kernel
def ob2_58 : Pattern := ⟨6,3,[16,1048,2080,168,2065,281,2081,41,26,546,106,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_58_bad : impossible ob2_58=true := by decide +kernel
def ob2_59 : Pattern := ⟨6,3,[1040,24,288,168,1041,2073,289,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_59_bad : impossible ob2_59=true := by decide +kernel
def ob2_60 : Pattern := ⟨6,3,[280,2080,40,1041,281,33,1065,26,546,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_60_bad : impossible ob2_60=true := by decide +kernel
def ob2_61 : Pattern := ⟨6,3,[152,288,40,1041,25,289,553,1050,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_61_bad : impossible ob2_61=true := by decide +kernel
def ob2_62 : Pattern := ⟨6,3,[16,24,544,552,81,1049,33,41,2074,2082,42,35,1067,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_62_bad : impossible ob2_62=true := by decide +kernel
def ob2_63 : Pattern := ⟨6,3,[528,2072,32,168,1041,2073,2081,41,26,34,554,291,43,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_63_bad : impossible ob2_63=true := by decide +kernel
def ob2_64 : Pattern := ⟨6,3,[264,1040,2072,32,552,17,281,289,553,154,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_64_bad : impossible ob2_64=true := by decide +kernel
def ob2_65 : Pattern := ⟨6,3,[16,1048,2080,296,2065,25,545,1065,154,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_65_bad : impossible ob2_65=true := by decide +kernel
def ob2_66 : Pattern := ⟨6,3,[520,1040,24,544,168,1041,2073,289,41,1050,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_66_bad : impossible ob2_66=true := by decide +kernel
def ob2_67 : Pattern := ⟨6,3,[24,160,552,1041,2073,33,553,2074,34,42,163,43,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_67_bad : impossible ob2_67=true := by decide +kernel
def ob2_68 : Pattern := ⟨6,3,[16,2072,160,40,1041,25,33,1065,26,2082,554,2083,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_68_bad : impossible ob2_68=true := by decide +kernel
def ob2_69 : Pattern := ⟨6,3,[24,544,296,1041,2073,33,553,2074,34,42,163,43,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_69_bad : impossible ob2_69=true := by decide +kernel
def ob2_70 : Pattern := ⟨6,3,[8,528,280,2080,1064,529,281,2081,1065,26,2082,554,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_70_bad : impossible ob2_70=true := by decide +kernel
def ob2_71 : Pattern := ⟨6,3,[2072,160,40,1041,281,33,1065,26,162,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_71_bad : impossible ob2_71=true := by decide +kernel
def ob2_72 : Pattern := ⟨6,3,[2072,160,40,1041,2073,33,553,26,34,106,1066,163,2083,43,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_72_bad : impossible ob2_72=true := by decide +kernel
def ob2_73 : Pattern := ⟨6,3,[16,24,544,168,2065,1049,33,41,2074,2082,42,35,1067,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_73_bad : impossible ob2_73=true := by decide +kernel
def ob2_74 : Pattern := ⟨6,3,[16,280,544,1064,529,25,2081,297,154,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_74_bad : impossible ob2_74=true := by decide +kernel
def ob2_75 : Pattern := ⟨6,3,[528,2072,2080,40,1041,281,33,1065,26,162,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_75_bad : impossible ob2_75=true := by decide +kernel
def ob2_76 : Pattern := ⟨6,3,[16,152,2080,40,1041,25,33,553,2074,34,1066,2083,43,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_76_bad : impossible ob2_76=true := by decide +kernel
def ob2_77 : Pattern := ⟨6,3,[528,2072,2080,40,1041,1049,33,105,26,162,106,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_77_bad : impossible ob2_77=true := by decide +kernel
def ob2_78 : Pattern := ⟨6,3,[1040,24,288,168,2065,2073,289,41,90,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_78_bad : impossible ob2_78=true := by decide +kernel
def ob2_79 : Pattern := ⟨5,3,[264,1040,24,32,17,25,289,154,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_79_bad : impossible ob2_79=true := by decide +kernel
def ob2_80 : Pattern := ⟨6,3,[152,288,40,1041,25,289,553,1050,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_80_bad : impossible ob2_80=true := by decide +kernel
def ob2_81 : Pattern := ⟨6,3,[2072,288,40,1041,25,545,553,1050,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_81_bad : impossible ob2_81=true := by decide +kernel
def ob2_82 : Pattern := ⟨6,3,[16,280,2080,1064,1041,2073,33,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_82_bad : impossible ob2_82=true := by decide +kernel
def ob2_83 : Pattern := ⟨6,3,[8,1040,2072,288,552,1041,2073,289,553,2074,34,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_83_bad : impossible ob2_83=true := by decide +kernel
def ob2_84 : Pattern := ⟨5,3,[16,152,160,81,25,33,26,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_84_bad : impossible ob2_84=true := by decide +kernel
def ob2_85 : Pattern := ⟨6,3,[520,528,24,544,552,2065,1049,33,297,2074,162,42,163,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_85_bad : impossible ob2_85=true := by decide +kernel
def ob2_86 : Pattern := ⟨6,3,[8,144,2072,288,552,1041,2073,289,553,2074,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_86_bad : impossible ob2_86=true := by decide +kernel
def ob2_87 : Pattern := ⟨6,3,[2064,2072,2080,40,1041,25,289,553,154,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_87_bad : impossible ob2_87=true := by decide +kernel
def ob2_88 : Pattern := ⟨6,3,[8,2064,1048,544,296,2065,1049,545,297,2074,2082,42,35,1067,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_88_bad : impossible ob2_88=true := by decide +kernel
def ob2_89 : Pattern := ⟨6,3,[528,280,32,1064,2065,2073,2081,41,26,98,170,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_89_bad : impossible ob2_89=true := by decide +kernel
def ob2_90 : Pattern := ⟨6,3,[280,160,40,1041,281,33,1065,26,162,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_90_bad : impossible ob2_90=true := by decide +kernel
def ob2_91 : Pattern := ⟨6,3,[280,2080,40,1041,1049,33,1065,26,162,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_91_bad : impossible ob2_91=true := by decide +kernel
def ob2_92 : Pattern := ⟨6,3,[8,1040,152,288,552,1041,89,289,553,2074,34,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_92_bad : impossible ob2_92=true := by decide +kernel
def ob2_93 : Pattern := ⟨6,3,[2056,1048,32,168,2065,1049,2081,41,26,546,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_93_bad : impossible ob2_93=true := by decide +kernel
def ob2_94 : Pattern := ⟨6,3,[8,144,2072,288,552,81,2073,289,553,1050,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_94_bad : impossible ob2_94=true := by decide +kernel
def ob2_95 : Pattern := ⟨6,3,[24,544,552,2065,2073,545,41,1050,34,42,35,171,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_95_bad : impossible ob2_95=true := by decide +kernel
def ob2_96 : Pattern := ⟨6,3,[16,24,544,168,2065,2073,33,41,1050,34,1066,2083,43,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_96_bad : impossible ob2_96=true := by decide +kernel
def ob2_97 : Pattern := ⟨6,3,[16,280,2080,1064,81,2073,33,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_97_bad : impossible ob2_97=true := by decide +kernel
def ob2_98 : Pattern := ⟨6,3,[1040,2072,32,1064,17,281,2081,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_98_bad : impossible ob2_98=true := by decide +kernel
def ob2_99 : Pattern := ⟨6,3,[2072,2080,40,1041,1049,33,1065,26,546,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_99_bad : impossible ob2_99=true := by decide +kernel
def ob2_100 : Pattern := ⟨6,3,[16,24,544,552,2065,1049,33,41,2074,34,1066,2083,43,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_100_bad : impossible ob2_100=true := by decide +kernel
def ob2_101 : Pattern := ⟨6,3,[8,1040,2072,288,552,1041,2073,289,553,2074,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_101_bad : impossible ob2_101=true := by decide +kernel
def ob2_102 : Pattern := ⟨6,3,[528,1048,2080,40,2065,281,33,1065,26,546,42,35,299,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_102_bad : impossible ob2_102=true := by decide +kernel
def ob2_103 : Pattern := ⟨6,3,[1040,24,288,168,2065,2073,2081,41,90,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_103_bad : impossible ob2_103=true := by decide +kernel
def ob2_104 : Pattern := ⟨6,3,[16,24,544,552,81,2073,33,41,1050,34,554,2083,43,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_104_bad : impossible ob2_104=true := by decide +kernel
def ob2_105 : Pattern := ⟨6,3,[1040,24,288,168,1041,2073,289,41,1050,34,1066,99,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_105_bad : impossible ob2_105=true := by decide +kernel
def ob2_106 : Pattern := ⟨6,3,[2056,24,288,168,1041,2073,545,41,90,34,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_106_bad : impossible ob2_106=true := by decide +kernel
def ob2_107 : Pattern := ⟨6,3,[1032,1040,32,552,2073,2081,41,26,34,170,99,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_107_bad : impossible ob2_107=true := by decide +kernel
def ob2_108 : Pattern := ⟨6,3,[520,528,24,160,552,2065,1049,33,297,2074,2082,42,163,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_108_bad : impossible ob2_108=true := by decide +kernel
def ob2_109 : Pattern := ⟨5,3,[16,280,32,529,25,33,26,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_109_bad : impossible ob2_109=true := by decide +kernel
def ob2_110 : Pattern := ⟨6,3,[16,152,288,552,529,25,2081,1065,154,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_110_bad : impossible ob2_110=true := by decide +kernel
def ob2_111 : Pattern := ⟨6,3,[16,152,32,1064,2065,25,97,41,26,2082,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_111_bad : impossible ob2_111=true := by decide +kernel
def ob2_112 : Pattern := ⟨6,3,[2056,528,32,552,281,2081,41,26,34,170,99,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_112_bad : impossible ob2_112=true := by decide +kernel
def ob2_113 : Pattern := ⟨6,3,[1032,16,280,288,552,1041,2073,33,553,90,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_113_bad : impossible ob2_113=true := by decide +kernel
def ob2_114 : Pattern := ⟨6,3,[2072,2080,40,529,1049,33,1065,26,546,106,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_114_bad : impossible ob2_114=true := by decide +kernel
def ob2_115 : Pattern := ⟨6,3,[1040,1048,32,1064,529,2073,2081,41,26,546,170,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_115_bad : impossible ob2_115=true := by decide +kernel
def ob2_116 : Pattern := ⟨6,3,[1040,24,288,552,1041,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_116_bad : impossible ob2_116=true := by decide +kernel
def ob2_117 : Pattern := ⟨6,3,[1040,2072,288,40,1041,25,289,105,154,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_117_bad : impossible ob2_117=true := by decide +kernel
def ob2_118 : Pattern := ⟨6,3,[24,544,168,2065,2073,2081,41,1050,34,42,35,107,1067,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_118_bad : impossible ob2_118=true := by decide +kernel
def ob2_119 : Pattern := ⟨6,3,[16,152,32,168,81,25,2081,41,26,2082,1066,2083,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_119_bad : impossible ob2_119=true := by decide +kernel
def ob2_120 : Pattern := ⟨6,3,[2064,24,544,552,17,281,2081,1065,154,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_120_bad : impossible ob2_120=true := by decide +kernel
def ob2_121 : Pattern := ⟨6,3,[8,1040,2072,160,552,1041,2073,289,553,2074,34,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_121_bad : impossible ob2_121=true := by decide +kernel
def ob2_122 : Pattern := ⟨6,3,[528,24,288,168,2065,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_122_bad : impossible ob2_122=true := by decide +kernel
def ob2_123 : Pattern := ⟨6,3,[8,144,152,288,552,1041,2073,289,553,1050,34,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_123_bad : impossible ob2_123=true := by decide +kernel
def ob2_124 : Pattern := ⟨6,3,[2072,2080,40,529,1049,33,1065,26,162,106,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_124_bad : impossible ob2_124=true := by decide +kernel
def ob2_125 : Pattern := ⟨6,3,[1040,24,544,168,1041,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_125_bad : impossible ob2_125=true := by decide +kernel
def ob2_126 : Pattern := ⟨5,3,[520,528,24,544,17,89,33,154,1050,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_126_bad : impossible ob2_126=true := by decide +kernel
def ob2_127 : Pattern := ⟨6,3,[280,2080,40,1041,1049,33,1065,26,546,554,163,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_127_bad : impossible ob2_127=true := by decide +kernel
def ob2_128 : Pattern := ⟨6,3,[152,2080,40,1041,25,289,553,1050,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_128_bad : impossible ob2_128=true := by decide +kernel
def ob2_129 : Pattern := ⟨6,3,[2072,288,40,1041,25,289,553,1050,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_129_bad : impossible ob2_129=true := by decide +kernel
def ob2_130 : Pattern := ⟨6,3,[8,144,1048,544,296,2065,1049,545,297,2074,546,42,35,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_130_bad : impossible ob2_130=true := by decide +kernel
def ob2_131 : Pattern := ⟨6,3,[2064,152,2080,40,1041,25,289,105,154,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_131_bad : impossible ob2_131=true := by decide +kernel
def ob2_132 : Pattern := ⟨6,3,[280,32,1064,529,2073,2081,41,26,546,42,35,299,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_132_bad : impossible ob2_132=true := by decide +kernel
def ob2_133 : Pattern := ⟨6,3,[528,24,288,168,1041,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_133_bad : impossible ob2_133=true := by decide +kernel
def ob2_134 : Pattern := ⟨6,3,[152,288,40,1041,25,289,553,154,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_134_bad : impossible ob2_134=true := by decide +kernel
def ob2_135 : Pattern := ⟨6,3,[520,1040,24,288,168,2065,2073,2081,41,90,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_135_bad : impossible ob2_135=true := by decide +kernel
def ob2_136 : Pattern := ⟨6,3,[24,288,296,1041,2073,33,1065,2074,34,42,163,43,172,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_136_bad : impossible ob2_136=true := by decide +kernel
def ob2_137 : Pattern := ⟨6,3,[2072,160,40,1041,2073,33,553,26,34,170,1066,163,2083,43,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_137_bad : impossible ob2_137=true := by decide +kernel
def ob2_138 : Pattern := ⟨6,3,[2072,2080,40,529,281,33,1065,26,162,106,1066,163,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_138_bad : impossible ob2_138=true := by decide +kernel
def ob2_139 : Pattern := ⟨6,3,[2072,160,40,1041,1049,33,1065,26,162,106,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_139_bad : impossible ob2_139=true := by decide +kernel
def ob2_140 : Pattern := ⟨6,3,[24,544,296,2065,2073,2081,41,1050,34,42,35,171,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_140_bad : impossible ob2_140=true := by decide +kernel
def ob2_141 : Pattern := ⟨6,3,[1040,152,2080,40,1041,25,289,553,154,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_141_bad : impossible ob2_141=true := by decide +kernel
def ob2_142 : Pattern := ⟨6,3,[528,24,288,168,1041,2073,289,41,1050,34,170,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_142_bad : impossible ob2_142=true := by decide +kernel
def ob2_143 : Pattern := ⟨6,3,[8,144,2072,160,552,81,2073,289,553,1050,34,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_143_bad : impossible ob2_143=true := by decide +kernel
def ob2_144 : Pattern := ⟨6,3,[8,144,1048,544,296,2065,1049,545,105,2074,546,42,35,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_144_bad : impossible ob2_144=true := by decide +kernel
def ob2_145 : Pattern := ⟨6,3,[8,144,152,288,552,81,2073,289,553,2074,34,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_145_bad : impossible ob2_145=true := by decide +kernel
def ob2_146 : Pattern := ⟨6,3,[1040,280,32,1064,2065,281,2081,41,26,546,170,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_146_bad : impossible ob2_146=true := by decide +kernel
def ob2_147 : Pattern := ⟨6,3,[520,24,288,552,1041,2073,545,41,90,34,42,35,171,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_147_bad : impossible ob2_147=true := by decide +kernel
def ob2_148 : Pattern := ⟨6,3,[8,16,1048,2080,296,2065,25,545,1065,2074,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_148_bad : impossible ob2_148=true := by decide +kernel
def ob2_149 : Pattern := ⟨6,3,[16,152,32,1064,529,25,2081,41,26,2082,1066,2083,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_149_bad : impossible ob2_149=true := by decide +kernel
def ob2_150 : Pattern := ⟨6,3,[1040,24,288,552,1041,2073,289,41,1050,34,170,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_150_bad : impossible ob2_150=true := by decide +kernel
def ob2_151 : Pattern := ⟨6,3,[2064,2072,288,40,1041,25,289,105,154,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_151_bad : impossible ob2_151=true := by decide +kernel
def ob2_152 : Pattern := ⟨6,3,[2056,280,32,168,2065,2073,2081,41,26,546,42,35,171,108,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_152_bad : impossible ob2_152=true := by decide +kernel
def ob2_153 : Pattern := ⟨6,3,[1032,528,280,2080,40,529,281,33,105,26,162,554,163,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_153_bad : impossible ob2_153=true := by decide +kernel
def ob2_154 : Pattern := ⟨6,3,[8,144,152,288,552,81,2073,289,553,2074,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_154_bad : impossible ob2_154=true := by decide +kernel
def ob2_155 : Pattern := ⟨6,3,[520,1040,1048,32,296,2065,25,545,297,2074,2082,42,163,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_155_bad : impossible ob2_155=true := by decide +kernel
def ob2_156 : Pattern := ⟨6,3,[16,1048,2080,168,81,281,2081,41,26,546,170,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_156_bad : impossible ob2_156=true := by decide +kernel
def ob2_157 : Pattern := ⟨6,3,[8,1040,2072,288,552,1041,2073,289,553,1050,34,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_157_bad : impossible ob2_157=true := by decide +kernel
def ob2_158 : Pattern := ⟨6,3,[24,288,168,2065,2073,2081,41,1050,34,42,35,107,1067,172,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_158_bad : impossible ob2_158=true := by decide +kernel
def ob2_159 : Pattern := ⟨6,3,[1040,24,288,552,1041,2073,2081,41,1050,34,170,554,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_159_bad : impossible ob2_159=true := by decide +kernel
def ob2_160 : Pattern := ⟨6,3,[16,24,544,552,2065,2073,33,41,1050,2082,42,35,1067,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_160_bad : impossible ob2_160=true := by decide +kernel
def ob2_161 : Pattern := ⟨6,3,[520,1040,24,288,168,2065,2073,289,41,90,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_161_bad : impossible ob2_161=true := by decide +kernel
def ob2_162 : Pattern := ⟨6,3,[2056,1040,24,288,168,1041,2073,289,41,90,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_162_bad : impossible ob2_162=true := by decide +kernel
def ob2_163 : Pattern := ⟨6,3,[2056,2072,2080,40,529,25,2081,1065,26,34,1066,163,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_163_bad : impossible ob2_163=true := by decide +kernel
def ob2_164 : Pattern := ⟨6,3,[2072,2080,40,529,25,289,553,1050,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_164_bad : impossible ob2_164=true := by decide +kernel
def ob2_165 : Pattern := ⟨6,3,[8,144,152,288,552,81,89,289,553,1050,34,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_165_bad : impossible ob2_165=true := by decide +kernel
def ob2_166 : Pattern := ⟨6,3,[520,528,24,160,552,1041,89,33,297,2074,2082,42,163,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_166_bad : impossible ob2_166=true := by decide +kernel
def ob2_167 : Pattern := ⟨6,3,[16,24,160,552,2065,2073,33,41,1050,2082,42,35,1067,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_167_bad : impossible ob2_167=true := by decide +kernel
def ob2_168 : Pattern := ⟨6,3,[16,152,2080,1064,529,25,289,553,154,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_168_bad : impossible ob2_168=true := by decide +kernel
def ob2_169 : Pattern := ⟨6,3,[144,1048,2080,40,17,2073,545,553,1050,34,170,35,43,108,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_169_bad : impossible ob2_169=true := by decide +kernel
def ob2_170 : Pattern := ⟨5,3,[264,16,280,32,529,25,33,26,162,546,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_170_bad : impossible ob2_170=true := by decide +kernel
def ob2_171 : Pattern := ⟨6,3,[2056,1040,24,288,168,2065,2073,289,41,1050,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_171_bad : impossible ob2_171=true := by decide +kernel
def ob2_172 : Pattern := ⟨6,3,[8,144,152,288,552,1041,2073,97,553,2074,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_172_bad : impossible ob2_172=true := by decide +kernel
def ob2_173 : Pattern := ⟨6,3,[16,280,160,1064,81,2073,33,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_173_bad : impossible ob2_173=true := by decide +kernel
def ob2_174 : Pattern := ⟨6,3,[16,152,2080,40,1041,25,33,1065,26,2082,554,2083,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_174_bad : impossible ob2_174=true := by decide +kernel
def ob2_175 : Pattern := ⟨6,3,[16,280,2080,1064,529,2073,33,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_175_bad : impossible ob2_175=true := by decide +kernel
def ob2_176 : Pattern := ⟨6,3,[144,280,32,1064,17,2073,97,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_176_bad : impossible ob2_176=true := by decide +kernel
def ob2_177 : Pattern := ⟨6,3,[24,544,296,2065,2073,545,41,1050,34,42,35,171,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_177_bad : impossible ob2_177=true := by decide +kernel
def ob2_178 : Pattern := ⟨6,3,[528,24,288,168,1041,2073,289,41,90,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_178_bad : impossible ob2_178=true := by decide +kernel
def ob2_179 : Pattern := ⟨6,3,[2064,2072,2080,40,1041,2073,33,1065,26,34,554,291,43,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_179_bad : impossible ob2_179=true := by decide +kernel
def ob2_180 : Pattern := ⟨6,3,[1040,152,2080,40,529,25,289,105,154,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_180_bad : impossible ob2_180=true := by decide +kernel
def ob2_181 : Pattern := ⟨6,3,[24,544,552,1041,2073,33,1065,2074,34,42,163,43,172,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_181_bad : impossible ob2_181=true := by decide +kernel
def ob2_182 : Pattern := ⟨6,3,[2056,16,280,544,296,2065,1049,2081,41,90,546,170,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_182_bad : impossible ob2_182=true := by decide +kernel
def ob2_183 : Pattern := ⟨6,3,[2064,2072,2080,40,1041,25,289,105,154,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_183_bad : impossible ob2_183=true := by decide +kernel
def ob2_184 : Pattern := ⟨6,3,[16,1048,32,168,2065,25,545,41,2074,2082,42,35,1067,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_184_bad : impossible ob2_184=true := by decide +kernel
def ob2_185 : Pattern := ⟨6,3,[24,288,552,2065,2073,545,41,1050,34,42,35,171,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_185_bad : impossible ob2_185=true := by decide +kernel
def ob2_186 : Pattern := ⟨6,3,[1040,1048,32,168,2065,2073,2081,41,26,546,170,1066,99,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_186_bad : impossible ob2_186=true := by decide +kernel
def ob2_187 : Pattern := ⟨6,3,[8,2064,1048,544,168,2065,1049,545,297,2074,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_187_bad : impossible ob2_187=true := by decide +kernel
def ob2_188 : Pattern := ⟨6,3,[2064,2072,2080,40,17,1049,2081,297,26,546,170,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_188_bad : impossible ob2_188=true := by decide +kernel
def ob2_189 : Pattern := ⟨6,3,[24,544,296,1041,2073,33,553,2074,34,42,163,43,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_189_bad : impossible ob2_189=true := by decide +kernel
def ob2_190 : Pattern := ⟨6,3,[24,288,296,2065,2073,545,41,1050,34,42,35,171,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_190_bad : impossible ob2_190=true := by decide +kernel
def ob2_191 : Pattern := ⟨6,3,[1040,32,552,2073,289,41,26,34,170,1066,99,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_191_bad : impossible ob2_191=true := by decide +kernel
def ob2_192 : Pattern := ⟨6,3,[16,1048,32,1064,2065,25,2081,41,26,546,1066,2083,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_192_bad : impossible ob2_192=true := by decide +kernel
def ob2_193 : Pattern := ⟨6,3,[1032,24,288,296,2065,1049,33,553,2074,34,42,163,43,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_193_bad : impossible ob2_193=true := by decide +kernel
def ob2_194 : Pattern := ⟨6,3,[2072,2080,40,1041,25,545,553,1050,34,1066,163,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_194_bad : impossible ob2_194=true := by decide +kernel
def ob2_195 : Pattern := ⟨6,3,[1032,1040,280,32,168,2065,281,2081,41,26,546,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_195_bad : impossible ob2_195=true := by decide +kernel
def ob2_196 : Pattern := ⟨6,3,[1040,24,288,168,2065,2073,2081,41,1050,34,1066,99,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_196_bad : impossible ob2_196=true := by decide +kernel
def ob2_197 : Pattern := ⟨6,3,[2056,24,288,296,2065,1049,2081,41,1050,34,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_197_bad : impossible ob2_197=true := by decide +kernel
def ob2_198 : Pattern := ⟨6,3,[280,2080,40,1041,281,33,1065,26,162,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_198_bad : impossible ob2_198=true := by decide +kernel
def ob2_199 : Pattern := ⟨6,3,[2056,24,544,296,2065,2073,2081,41,1050,34,42,35,171,172].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_199_bad : impossible ob2_199=true := by decide +kernel
def ob2_200 : Pattern := ⟨6,3,[528,24,288,168,2065,2073,289,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_200_bad : impossible ob2_200=true := by decide +kernel
def ob2_201 : Pattern := ⟨6,3,[528,2072,32,1064,17,281,2081,1065,26,162,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_201_bad : impossible ob2_201=true := by decide +kernel
def ob2_202 : Pattern := ⟨6,3,[16,152,544,1064,2065,25,545,297,154,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_202_bad : impossible ob2_202=true := by decide +kernel
def ob2_203 : Pattern := ⟨6,3,[2056,1040,280,32,168,2065,281,2081,41,26,98,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_203_bad : impossible ob2_203=true := by decide +kernel
def ob2_204 : Pattern := ⟨6,3,[528,24,288,552,1041,2073,289,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_204_bad : impossible ob2_204=true := by decide +kernel
def ob2_205 : Pattern := ⟨6,3,[280,2080,40,529,1049,33,1065,26,162,554,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_205_bad : impossible ob2_205=true := by decide +kernel
def ob2_206 : Pattern := ⟨6,3,[2056,1040,280,32,1064,2065,281,2081,41,26,98,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_206_bad : impossible ob2_206=true := by decide +kernel
def ob2_207 : Pattern := ⟨6,3,[528,24,544,168,17,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_207_bad : impossible ob2_207=true := by decide +kernel
def ob2_208 : Pattern := ⟨6,3,[144,24,32,552,17,89,2081,41,154,34,1066,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_208_bad : impossible ob2_208=true := by decide +kernel
def ob2_209 : Pattern := ⟨6,3,[8,2064,152,544,296,2065,1049,545,297,2074,546,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_209_bad : impossible ob2_209=true := by decide +kernel
def ob2_210 : Pattern := ⟨6,3,[528,24,544,552,1041,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_210_bad : impossible ob2_210=true := by decide +kernel
def ob2_211 : Pattern := ⟨6,3,[520,528,24,160,552,2065,89,33,297,90,2082,42,163,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_211_bad : impossible ob2_211=true := by decide +kernel
def ob2_212 : Pattern := ⟨6,3,[24,288,296,1041,2073,33,553,2074,34,42,163,43,172,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_212_bad : impossible ob2_212=true := by decide +kernel
def ob2_213 : Pattern := ⟨6,3,[24,160,296,1041,1049,33,41,2074,34,42,291,43,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_213_bad : impossible ob2_213=true := by decide +kernel
def ob2_214 : Pattern := ⟨6,3,[16,1048,544,168,2065,25,2081,41,1050,546,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_214_bad : impossible ob2_214=true := by decide +kernel
def ob2_215 : Pattern := ⟨5,3,[520,1040,24,32,17,25,289,154,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_215_bad : impossible ob2_215=true := by decide +kernel
def ob2_216 : Pattern := ⟨6,3,[16,152,32,1064,529,25,545,41,2074,2082,42,35,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_216_bad : impossible ob2_216=true := by decide +kernel
def ob2_217 : Pattern := ⟨6,3,[152,2080,40,1041,25,289,553,1050,34,1066,163,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_217_bad : impossible ob2_217=true := by decide +kernel
def ob2_218 : Pattern := ⟨6,3,[520,1040,24,288,168,1041,2073,289,41,1050,34,170,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_218_bad : impossible ob2_218=true := by decide +kernel
def ob2_219 : Pattern := ⟨6,3,[2064,2072,160,40,1041,281,33,105,26,162,106,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_219_bad : impossible ob2_219=true := by decide +kernel
def ob2_220 : Pattern := ⟨6,3,[520,528,24,544,168,2065,2073,289,41,90,34,1066,291,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_220_bad : impossible ob2_220=true := by decide +kernel
def ob2_221 : Pattern := ⟨6,3,[528,24,544,168,1041,2073,2081,41,1050,34,1066,291,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_221_bad : impossible ob2_221=true := by decide +kernel
def ob2_222 : Pattern := ⟨6,3,[1040,280,32,168,2065,281,2081,41,26,546,554,291,171,1067,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_222_bad : impossible ob2_222=true := by decide +kernel
def ob2_223 : Pattern := ⟨6,3,[24,288,296,2065,2073,545,41,1050,34,42,35,171,172,300].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_223_bad : impossible ob2_223=true := by decide +kernel
def ob2_224 : Pattern := ⟨6,3,[264,16,280,160,552,1041,2073,33,1065,2074,98,554,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_224_bad : impossible ob2_224=true := by decide +kernel
def ob2_225 : Pattern := ⟨6,3,[264,144,1048,32,552,17,2073,289,553,2074,162,554,99,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_225_bad : impossible ob2_225=true := by decide +kernel
def ob2_226 : Pattern := ⟨6,3,[528,280,32,168,529,281,2081,41,26,546,554,291,299,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_226_bad : impossible ob2_226=true := by decide +kernel
def ob2_227 : Pattern := ⟨5,3,[8,144,152,160,81,89,289,545,26,34,35].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_227_bad : impossible ob2_227=true := by decide +kernel
def ob2_228 : Pattern := ⟨6,3,[144,24,32,552,17,2073,289,41,1050,34,1066,2083,43,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_228_bad : impossible ob2_228=true := by decide +kernel
def ob2_229 : Pattern := ⟨6,3,[152,2080,40,1041,25,545,553,1050,34,1066,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_229_bad : impossible ob2_229=true := by decide +kernel
def ob2_230 : Pattern := ⟨6,3,[2056,152,288,40,1041,25,2081,553,26,34,106,163,171,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_230_bad : impossible ob2_230=true := by decide +kernel
def ob2_231 : Pattern := ⟨6,3,[16,280,544,552,2065,2073,33,41,1050,546,42,35,43,300,556].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_231_bad : impossible ob2_231=true := by decide +kernel
def ob2_232 : Pattern := ⟨6,3,[2064,152,2080,40,529,25,545,105,1050,34,1066,163,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob2_232_bad : impossible ob2_232=true := by decide +kernel
def ob3_0 : Pattern := ⟨7,4,[4104,1040,2072,288,40,48,1041,25,545,4129,553,49,154,2074,34,42,114,178,163,4131,43,179,108,556,52,181,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_0_bad : impossible ob3_0=true := by decide +kernel
def ob3_1 : Pattern := ⟨7,4,[4104,1040,2072,288,40,48,1041,25,545,4129,553,49,154,2074,34,42,114,178,163,4131,43,179,108,556,52,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_1_bad : impossible ob3_1=true := by decide +kernel
def ob3_2 : Pattern := ⟨7,4,[1032,2064,1048,32,40,1072,2065,25,97,41,561,4122,2082,4130,42,50,163,4131,171,51,108,52,181,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_2_bad : impossible ob3_2=true := by decide +kernel
def ob3_3 : Pattern := ⟨7,4,[264,1040,2072,32,40,1072,17,4121,289,297,49,154,162,42,178,99,4131,43,51,108,52,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_3_bad : impossible ob3_3=true := by decide +kernel
def ob3_4 : Pattern := ⟨7,4,[1032,4112,24,160,552,48,4113,1049,33,1065,49,2074,2082,4130,42,50,99,2083,43,179,307,44,180,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_4_bad : impossible ob3_4=true := by decide +kernel
def ob3_5 : Pattern := ⟨7,4,[4104,528,280,32,1064,48,529,281,2081,41,49,26,546,42,562,291,299,51,44,180,2100,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_5_bad : impossible ob3_5=true := by decide +kernel
def ob3_6 : Pattern := ⟨7,4,[520,2064,152,32,40,1072,2065,25,545,41,305,1073,2074,4122,4130,42,50,99,4131,171,51,172,300,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_6_bad : impossible ob3_6=true := by decide +kernel
def ob3_7 : Pattern := ⟨7,4,[520,2064,2072,2080,40,2096,529,25,4129,105,49,26,34,106,1074,291,107,307,1075,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_7_bad : impossible ob3_7=true := by decide +kernel
def ob3_8 : Pattern := ⟨7,4,[1032,2064,152,32,168,296,1072,2065,25,97,41,561,4122,2082,4130,42,50,163,4131,299,4139,51,108,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_8_bad : impossible ob3_8=true := by decide +kernel
def ob3_9 : Pattern := ⟨7,4,[1032,528,1048,32,1064,1072,529,25,97,41,2097,26,98,4138,50,99,299,4139,307,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_9_bad : impossible ob3_9=true := by decide +kernel
def ob3_10 : Pattern := ⟨7,4,[1032,2064,4120,160,40,48,1041,1049,33,41,113,561,26,546,4130,42,562,291,4131,299,51,108,300,52,309,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_10_bad : impossible ob3_10=true := by decide +kernel
def ob3_11 : Pattern := ⟨7,4,[4104,528,4120,2080,40,48,529,281,33,1065,49,26,162,2082,42,114,178,163,4131,107,1067,51,44,180,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_11_bad : impossible ob3_11=true := by decide +kernel
def ob3_12 : Pattern := ⟨7,4,[4104,528,280,32,1064,48,4113,281,4121,2081,41,49,26,546,170,1066,50,291,2083,43,307,44,180,308,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_12_bad : impossible ob3_12=true := by decide +kernel
def ob3_13 : Pattern := ⟨7,4,[4104,4112,2072,288,40,48,1041,25,289,553,49,1050,34,1066,50,163,291,43,179,44,308,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_13_bad : impossible ob3_13=true := by decide +kernel
def ob3_14 : Pattern := ⟨7,4,[4104,528,280,2080,40,48,529,1049,4121,33,1065,49,26,162,2082,42,114,178,163,4131,299,51,44,180,181,1077].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_14_bad : impossible ob3_14=true := by decide +kernel
def ob3_15 : Pattern := ⟨7,4,[2056,528,280,4128,40,48,529,281,33,41,1073,26,162,2082,42,114,1074,163,4131,107,171,51,172,52,181,1077].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_15_bad : impossible ob3_15=true := by decide +kernel
def ob3_16 : Pattern := ⟨7,4,[1032,1040,2064,24,160,552,176,2096,1041,89,33,297,4137,49,1050,2074,34,42,2098,163,291,299,4139,51,172,4140,180,564,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_16_bad : impossible ob3_16=true := by decide +kernel
def ob3_17 : Pattern := ⟨7,4,[520,2064,2072,2080,40,2096,529,25,4129,105,49,26,34,106,1074,291,107,179,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_17_bad : impossible ob3_17=true := by decide +kernel
def ob3_18 : Pattern := ⟨7,4,[1032,2064,24,160,40,304,1072,2065,1049,33,41,305,561,4122,2082,4130,42,50,99,4131,171,299,51,172,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_18_bad : impossible ob3_18=true := by decide +kernel
def ob3_19 : Pattern := ⟨7,4,[2056,4112,1048,544,40,48,17,281,2073,545,41,305,1050,162,4130,170,50,35,43,115,307,108,172,52,181,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_19_bad : impossible ob3_19=true := by decide +kernel
def ob3_20 : Pattern := ⟨7,4,[2056,528,280,32,40,1072,2065,2073,4121,4129,41,49,26,98,4130,42,562,99,4131,299,51,108,52,117,1077].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_20_bad : impossible ob3_20=true := by decide +kernel
def ob3_21 : Pattern := ⟨7,4,[2056,528,2072,4128,40,48,529,281,33,41,1073,26,162,4130,106,170,50,163,4131,43,115,1075,172,52,181,1077].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_21_bad : impossible ob3_21=true := by decide +kernel
def ob3_22 : Pattern := ⟨7,4,[2056,528,2072,2080,40,304,1072,529,25,33,105,1073,26,4130,106,50,163,107,307,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_22_bad : impossible ob3_22=true := by decide +kernel
def ob3_23 : Pattern := ⟨7,4,[8,144,4120,160,168,48,1041,89,289,41,113,2074,34,42,1074,291,4131,43,51,300,52,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_23_bad : impossible ob3_23=true := by decide +kernel
def ob3_24 : Pattern := ⟨7,4,[520,2064,152,32,40,1072,2065,25,97,41,305,1073,2074,4122,4130,42,50,99,4131,171,51,172,300,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_24_bad : impossible ob3_24=true := by decide +kernel
def ob3_25 : Pattern := ⟨7,4,[4104,1040,2072,288,40,48,1041,25,289,553,49,1050,34,42,1074,163,4131,43,179,300,52,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_25_bad : impossible ob3_25=true := by decide +kernel
def ob3_26 : Pattern := ⟨7,4,[2056,1040,4120,288,40,48,1041,25,289,41,561,1050,34,42,114,562,163,4131,171,51,108,172,52,181,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_26_bad : impossible ob3_26=true := by decide +kernel
def ob3_27 : Pattern := ⟨7,4,[2056,1040,24,288,40,176,1072,2065,4121,289,2081,41,49,1050,34,42,178,562,291,4131,171,299,51,300,52,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_27_bad : impossible ob3_27=true := by decide +kernel
def ob3_28 : Pattern := ⟨7,4,[520,1040,1048,32,1064,176,2096,529,25,97,4137,49,26,98,42,2098,99,299,307,2099,300,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_28_bad : impossible ob3_28=true := by decide +kernel
def ob3_29 : Pattern := ⟨7,4,[2056,4112,1048,544,40,48,17,281,2073,289,4129,41,305,154,4122,162,4130,170,50,35,43,115,307,108,172,52,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_29_bad : impossible ob3_29=true := by decide +kernel
def ob3_30 : Pattern := ⟨7,4,[2056,2064,4120,288,40,48,1041,25,289,41,561,1050,34,42,1074,291,4131,171,51,300,52,181,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_30_bad : impossible ob3_30=true := by decide +kernel
def ob3_31 : Pattern := ⟨7,4,[2056,144,1048,4128,40,48,17,281,289,545,41,305,1050,4122,546,170,50,35,43,1075,556,52,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_31_bad : impossible ob3_31=true := by decide +kernel
def ob3_32 : Pattern := ⟨7,4,[1032,1040,1048,32,1064,48,17,2073,97,41,305,4122,162,4130,170,50,2083,4131,43,51,44,308,564,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_32_bad : impossible ob3_32=true := by decide +kernel
def ob3_33 : Pattern := ⟨7,4,[8,2064,1048,544,40,176,4113,1049,545,105,49,1050,546,42,50,35,1067,51,44,180,308,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_33_bad : impossible ob3_33=true := by decide +kernel
def ob3_34 : Pattern := ⟨7,4,[520,4112,24,160,552,48,4113,1049,33,1065,49,90,2074,162,4130,42,50,163,2083,43,115,44,180,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_34_bad : impossible ob3_34=true := by decide +kernel
def ob3_35 : Pattern := ⟨7,4,[8,1040,4120,288,168,48,1041,2073,97,41,561,1073,1050,4122,34,42,114,1074,2083,4131,43,51,172,556,52,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_35_bad : impossible ob3_35=true := by decide +kernel
def ob3_36 : Pattern := ⟨7,4,[4104,4112,2072,160,40,48,1041,1049,33,1065,49,26,162,554,50,163,291,43,307,44,116,308,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_36_bad : impossible ob3_36=true := by decide +kernel
def ob3_37 : Pattern := ⟨7,4,[264,144,2072,4128,40,48,17,1049,2073,545,4129,41,305,1050,4122,546,4130,170,50,35,43,1075,556,52,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_37_bad : impossible ob3_37=true := by decide +kernel
def ob3_38 : Pattern := ⟨7,4,[2056,1040,4120,2080,40,48,529,25,545,2081,41,561,154,4122,34,106,170,50,163,4131,171,51,44,116,564,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_38_bad : impossible ob3_38=true := by decide +kernel
def ob3_39 : Pattern := ⟨7,4,[4104,528,4120,2080,40,48,529,281,33,1065,49,26,162,2082,42,114,178,163,4131,107,1067,51,44,180,181,1077].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_39_bad : impossible ob3_39=true := by decide +kernel
def ob3_40 : Pattern := ⟨7,4,[2056,4112,1048,544,40,48,17,281,2073,545,41,305,1050,162,4130,170,50,35,43,115,307,108,172,52,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_40_bad : impossible ob3_40=true := by decide +kernel
def ob3_41 : Pattern := ⟨7,4,[1032,2064,24,544,40,560,2065,89,33,41,1073,4122,162,4130,42,50,163,4131,107,51,172,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_41_bad : impossible ob3_41=true := by decide +kernel
def ob3_42 : Pattern := ⟨7,4,[2056,1040,4120,2080,40,48,1041,25,289,41,561,1050,4122,34,1066,50,291,171,51,44,116,564,181,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_42_bad : impossible ob3_42=true := by decide +kernel
def ob3_43 : Pattern := ⟨7,4,[1032,4112,24,160,552,48,1041,1049,33,1065,49,2074,162,42,50,163,43,307,2099,44,116,308,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_43_bad : impossible ob3_43=true := by decide +kernel
def ob3_44 : Pattern := ⟨7,4,[520,528,1040,2072,2080,40,176,1072,529,25,4129,105,49,26,34,554,1066,1074,163,4131,171,299,179,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_44_bad : impossible ob3_44=true := by decide +kernel
def ob3_45 : Pattern := ⟨7,4,[1032,2064,24,544,40,304,1072,2065,1049,33,41,305,561,4122,162,2082,42,50,163,4131,171,299,51,172,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_45_bad : impossible ob3_45=true := by decide +kernel
def ob3_46 : Pattern := ⟨7,4,[2056,1040,1048,32,168,296,1072,2065,4121,97,41,49,26,98,42,562,291,4131,299,51,108,52,309,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_46_bad : impossible ob3_46=true := by decide +kernel
def ob3_47 : Pattern := ⟨7,4,[4104,528,1048,32,1064,48,4113,281,2081,41,49,26,546,554,50,291,2083,43,307,44,180,2100,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_47_bad : impossible ob3_47=true := by decide +kernel
def ob3_48 : Pattern := ⟨7,4,[1032,16,1048,2072,160,544,296,176,2096,81,1049,33,4137,49,90,98,106,4138,50,35,43,2099,172,4140,180,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_48_bad : impossible ob3_48=true := by decide +kernel
def ob3_49 : Pattern := ⟨7,4,[4104,4112,280,2080,40,48,529,281,33,1065,49,26,162,4130,554,50,163,2083,43,115,179,44,180,181,1077].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_49_bad : impossible ob3_49=true := by decide +kernel
def ob3_50 : Pattern := ⟨7,4,[4104,528,280,32,1064,48,4113,281,2081,41,49,26,546,554,50,291,2083,43,307,44,180,2100,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_50_bad : impossible ob3_50=true := by decide +kernel
def ob3_51 : Pattern := ⟨7,4,[1032,4112,2072,160,40,48,1041,1049,33,1065,49,26,162,554,50,291,2083,43,307,44,116,308,309,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_51_bad : impossible ob3_51=true := by decide +kernel
def ob3_52 : Pattern := ⟨7,4,[2056,2064,152,2080,40,176,560,17,25,289,105,561,154,1050,34,106,1074,4131,107,51,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_52_bad : impossible ob3_52=true := by decide +kernel
def ob3_53 : Pattern := ⟨7,4,[520,4112,152,32,1064,48,4113,25,545,553,49,154,2074,98,4130,42,50,163,2083,43,179,44,180,308,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_53_bad : impossible ob3_53=true := by decide +kernel
def ob3_54 : Pattern := ⟨7,4,[520,1040,152,2072,32,296,552,1072,4113,25,97,553,49,2074,2082,4130,42,50,99,43,179,300,556,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_54_bad : impossible ob3_54=true := by decide +kernel
def ob3_55 : Pattern := ⟨7,4,[1032,2064,152,32,168,296,1072,2065,25,97,41,561,4122,98,2082,42,50,99,163,299,4139,51,108,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_55_bad : impossible ob3_55=true := by decide +kernel
def ob3_56 : Pattern := ⟨7,4,[2056,1040,152,2080,40,304,560,1041,25,33,553,1065,561,4122,34,1066,4138,50,291,4131,171,4139,51,172,300,308,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_56_bad : impossible ob3_56=true := by decide +kernel
def ob3_57 : Pattern := ⟨7,4,[2056,16,1048,544,40,304,4113,2073,545,41,49,1050,98,4130,106,50,35,43,179,307,108,172,52,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_57_bad : impossible ob3_57=true := by decide +kernel
def ob3_58 : Pattern := ⟨7,4,[2056,144,1048,2080,40,2096,17,1049,33,105,305,4122,162,106,170,50,35,107,1067,51,172,556,564,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_58_bad : impossible ob3_58=true := by decide +kernel
def ob3_59 : Pattern := ⟨7,4,[264,1040,4120,32,1064,48,17,2073,289,41,305,154,162,170,50,99,4131,43,51,44,116,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_59_bad : impossible ob3_59=true := by decide +kernel
def ob3_60 : Pattern := ⟨7,4,[1032,2064,4120,160,40,48,529,4113,281,4121,33,1065,49,26,546,2082,42,562,291,2083,299,51,44,116,564,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_60_bad : impossible ob3_60=true := by decide +kernel
def ob3_61 : Pattern := ⟨7,4,[264,144,24,288,2080,552,560,17,89,289,1065,4137,49,90,34,170,4138,178,291,2083,1067,4139,51,44,2100,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_61_bad : impossible ob3_61=true := by decide +kernel
def ob3_62 : Pattern := ⟨7,4,[4104,1040,1048,32,1064,48,4113,2073,97,41,49,26,98,554,50,291,2083,43,307,44,180,308,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_62_bad : impossible ob3_62=true := by decide +kernel
def ob3_63 : Pattern := ⟨7,4,[4104,4112,2072,288,40,48,1041,25,289,553,49,154,4122,34,1066,50,163,2083,43,179,44,116,180,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_63_bad : impossible ob3_63=true := by decide +kernel
def ob3_64 : Pattern := ⟨7,4,[1032,2064,4120,160,40,48,1041,281,4121,33,1065,49,26,546,2082,42,562,291,2083,299,51,44,116,564,309,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_64_bad : impossible ob3_64=true := by decide +kernel
def ob3_65 : Pattern := ⟨7,4,[520,2064,1048,32,40,1072,2065,25,97,41,305,1073,154,4122,4130,42,50,99,4131,171,51,172,300,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_65_bad : impossible ob3_65=true := by decide +kernel
def ob3_66 : Pattern := ⟨7,4,[264,144,280,2072,32,1064,1072,17,281,97,553,4137,49,26,98,170,4138,178,291,2083,43,2099,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_66_bad : impossible ob3_66=true := by decide +kernel
def ob3_67 : Pattern := ⟨7,4,[1032,528,1048,32,1064,1072,17,281,97,41,2097,26,98,170,178,2098,99,171,4139,51,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_67_bad : impossible ob3_67=true := by decide +kernel
def ob3_68 : Pattern := ⟨7,4,[2056,2064,152,2080,40,176,1072,529,25,545,4129,105,49,26,34,554,1066,1074,291,171,299,307,1075,300,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_68_bad : impossible ob3_68=true := by decide +kernel
def ob3_69 : Pattern := ⟨7,4,[2056,16,1048,2072,288,168,552,304,81,2073,4129,41,49,1050,2074,546,4130,106,50,35,43,1075,172,4140,52,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_69_bad : impossible ob3_69=true := by decide +kernel
def ob3_70 : Pattern := ⟨7,4,[264,1040,1048,32,1064,304,2096,17,25,97,553,561,2097,154,98,554,4138,50,163,2083,43,2099,108,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_70_bad : impossible ob3_70=true := by decide +kernel
def ob3_71 : Pattern := ⟨7,4,[4104,2064,4120,2080,40,48,529,1049,4121,33,1065,49,26,162,2082,42,562,291,299,51,44,116,564,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_71_bad : impossible ob3_71=true := by decide +kernel
def ob3_72 : Pattern := ⟨7,4,[2056,2064,152,2080,40,176,1072,529,25,289,4129,105,49,26,34,554,1066,1074,291,171,299,307,1075,300,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_72_bad : impossible ob3_72=true := by decide +kernel
def ob3_73 : Pattern := ⟨7,4,[264,144,1048,32,1064,1072,17,281,97,553,4137,49,26,98,554,562,2098,291,2083,43,2099,556,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_73_bad : impossible ob3_73=true := by decide +kernel
def ob3_74 : Pattern := ⟨7,4,[1040,1048,32,1064,176,529,4113,281,2081,41,49,26,546,170,1066,50,35,171,1067,51,44,180,2100,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_74_bad : impossible ob3_74=true := by decide +kernel
def ob3_75 : Pattern := ⟨7,4,[1040,32,40,1072,17,281,289,297,49,26,162,554,1066,178,562,291,4131,43,51,44,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_75_bad : impossible ob3_75=true := by decide +kernel
def ob3_76 : Pattern := ⟨7,4,[1032,4112,4120,160,4136,48,1041,1049,33,1065,113,26,162,42,114,163,43,115,172,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_76_bad : impossible ob3_76=true := by decide +kernel
def ob3_77 : Pattern := ⟨7,4,[1048,32,168,176,529,4113,281,4121,2081,41,49,26,98,2082,170,1066,50,35,299,1067,51,44,180,2100,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_77_bad : impossible ob3_77=true := by decide +kernel
def ob3_78 : Pattern := ⟨6,4,[8,144,528,152,1048,32,296,552,81,529,89,1049,33,297,553,26,546,2082,42,291,2083,43,44].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_78_bad : impossible ob3_78=true := by decide +kernel
def ob3_79 : Pattern := ⟨7,4,[8,144,152,2080,1064,48,4113,25,97,105,305,4122,34,4138,50,35,43,307,44,308,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_79_bad : impossible ob3_79=true := by decide +kernel
def ob3_80 : Pattern := ⟨7,4,[1040,4120,288,168,48,529,2065,25,545,4129,41,561,90,2074,34,42,114,562,163,4131,171,299,51,44,52,117,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_80_bad : impossible ob3_80=true := by decide +kernel
def ob3_81 : Pattern := ⟨7,4,[2056,1040,24,288,40,560,2065,4121,289,41,49,1050,34,42,1074,291,4131,107,51,300,52,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_81_bad : impossible ob3_81=true := by decide +kernel
def ob3_82 : Pattern := ⟨7,4,[4104,4112,2072,160,40,48,1041,1049,33,1065,49,26,162,554,50,291,2083,43,307,44,116,308,309,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_82_bad : impossible ob3_82=true := by decide +kernel
def ob3_83 : Pattern := ⟨7,4,[264,16,152,288,40,304,2096,81,25,33,553,4137,561,26,162,1066,4138,1074,2098,2083,4131,4139,51,44,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_83_bad : impossible ob3_83=true := by decide +kernel
def ob3_84 : Pattern := ⟨7,4,[8,2064,1048,544,40,176,4113,1049,545,105,49,1050,546,42,50,35,43,1075,556,52,309].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_84_bad : impossible ob3_84=true := by decide +kernel
def ob3_85 : Pattern := ⟨7,4,[528,280,160,40,2096,1041,4113,2073,4121,33,1065,4137,49,26,34,554,562,1074,291,43,307,2099,300,556,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_85_bad : impossible ob3_85=true := by decide +kernel
def ob3_86 : Pattern := ⟨7,4,[8,1040,4120,160,168,48,1041,2073,289,41,561,2097,1050,4122,34,1066,50,291,43,51,44,116,564,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_86_bad : impossible ob3_86=true := by decide +kernel
def ob3_87 : Pattern := ⟨7,4,[4104,1040,24,288,552,48,4113,2073,289,41,49,1050,34,1066,50,291,2083,43,115,44,116,180,181].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_87_bad : impossible ob3_87=true := by decide +kernel
def ob3_88 : Pattern := ⟨7,4,[1032,16,4120,160,296,48,1041,4121,33,1065,49,2074,98,162,42,114,2083,4131,43,51,44,180,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_88_bad : impossible ob3_88=true := by decide +kernel
def ob3_89 : Pattern := ⟨7,4,[528,280,4128,4136,48,1041,1049,33,1065,113,2097,26,162,546,42,114,1074,163,291,43,115,1075,172,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_89_bad : impossible ob3_89=true := by decide +kernel
def ob3_90 : Pattern := ⟨7,4,[4112,4120,160,4136,48,1041,1049,33,1065,113,26,162,4130,42,562,2098,163,4131,43,307,2099,172,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_90_bad : impossible ob3_90=true := by decide +kernel
def ob3_91 : Pattern := ⟨7,4,[1032,528,4120,2080,40,48,529,2065,281,33,1065,49,26,162,42,562,291,4131,299,51,44,116,2100,117].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_91_bad : impossible ob3_91=true := by decide +kernel
def ob3_92 : Pattern := ⟨7,4,[520,1040,24,160,288,552,304,2096,1041,89,33,41,2097,90,34,4138,50,99,171,4139,51,172,308,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_92_bad : impossible ob3_92=true := by decide +kernel
def ob3_93 : Pattern := ⟨7,4,[1032,16,2072,160,40,304,81,2073,33,41,1073,4122,98,4130,106,50,163,4131,43,51,172,52,565].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_93_bad : impossible ob3_93=true := by decide +kernel
def ob3_94 : Pattern := ⟨7,4,[144,24,288,40,176,17,89,289,105,49,154,34,1066,1074,291,43,51,44,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_94_bad : impossible ob3_94=true := by decide +kernel
def ob3_95 : Pattern := ⟨7,4,[4104,528,280,4128,4136,48,1041,1049,33,1065,1073,26,162,42,114,163,43,115,172,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_95_bad : impossible ob3_95=true := by decide +kernel
def ob3_96 : Pattern := ⟨7,4,[2056,144,2072,2080,40,176,304,17,25,545,105,305,154,1050,4130,106,50,35,107,1075,556,4140,52,53].map decodeReq⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ob3_96_bad : impossible ob3_96=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def obRow0 : Array Prohibited := #[
  ⟨ob0_0,ob0_0_bad⟩
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def obRow1 : Array Prohibited := #[
  ⟨ob1_0,ob1_0_bad⟩,
  ⟨ob1_1,ob1_1_bad⟩,
  ⟨ob1_2,ob1_2_bad⟩,
  ⟨ob1_3,ob1_3_bad⟩,
  ⟨ob1_4,ob1_4_bad⟩,
  ⟨ob1_5,ob1_5_bad⟩,
  ⟨ob1_6,ob1_6_bad⟩,
  ⟨ob1_7,ob1_7_bad⟩
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def obRow2 : Array Prohibited := #[
  ⟨ob2_0,ob2_0_bad⟩,
  ⟨ob2_1,ob2_1_bad⟩,
  ⟨ob2_2,ob2_2_bad⟩,
  ⟨ob2_3,ob2_3_bad⟩,
  ⟨ob2_4,ob2_4_bad⟩,
  ⟨ob2_5,ob2_5_bad⟩,
  ⟨ob2_6,ob2_6_bad⟩,
  ⟨ob2_7,ob2_7_bad⟩,
  ⟨ob2_8,ob2_8_bad⟩,
  ⟨ob2_9,ob2_9_bad⟩,
  ⟨ob2_10,ob2_10_bad⟩,
  ⟨ob2_11,ob2_11_bad⟩,
  ⟨ob2_12,ob2_12_bad⟩,
  ⟨ob2_13,ob2_13_bad⟩,
  ⟨ob2_14,ob2_14_bad⟩,
  ⟨ob2_15,ob2_15_bad⟩,
  ⟨ob2_16,ob2_16_bad⟩,
  ⟨ob2_17,ob2_17_bad⟩,
  ⟨ob2_18,ob2_18_bad⟩,
  ⟨ob2_19,ob2_19_bad⟩,
  ⟨ob2_20,ob2_20_bad⟩,
  ⟨ob2_21,ob2_21_bad⟩,
  ⟨ob2_22,ob2_22_bad⟩,
  ⟨ob2_23,ob2_23_bad⟩,
  ⟨ob2_24,ob2_24_bad⟩,
  ⟨ob2_25,ob2_25_bad⟩,
  ⟨ob2_26,ob2_26_bad⟩,
  ⟨ob2_27,ob2_27_bad⟩,
  ⟨ob2_28,ob2_28_bad⟩,
  ⟨ob2_29,ob2_29_bad⟩,
  ⟨ob2_30,ob2_30_bad⟩,
  ⟨ob2_31,ob2_31_bad⟩,
  ⟨ob2_32,ob2_32_bad⟩,
  ⟨ob2_33,ob2_33_bad⟩,
  ⟨ob2_34,ob2_34_bad⟩,
  ⟨ob2_35,ob2_35_bad⟩,
  ⟨ob2_36,ob2_36_bad⟩,
  ⟨ob2_37,ob2_37_bad⟩,
  ⟨ob2_38,ob2_38_bad⟩,
  ⟨ob2_39,ob2_39_bad⟩,
  ⟨ob2_40,ob2_40_bad⟩,
  ⟨ob2_41,ob2_41_bad⟩,
  ⟨ob2_42,ob2_42_bad⟩,
  ⟨ob2_43,ob2_43_bad⟩,
  ⟨ob2_44,ob2_44_bad⟩,
  ⟨ob2_45,ob2_45_bad⟩,
  ⟨ob2_46,ob2_46_bad⟩,
  ⟨ob2_47,ob2_47_bad⟩,
  ⟨ob2_48,ob2_48_bad⟩,
  ⟨ob2_49,ob2_49_bad⟩,
  ⟨ob2_50,ob2_50_bad⟩,
  ⟨ob2_51,ob2_51_bad⟩,
  ⟨ob2_52,ob2_52_bad⟩,
  ⟨ob2_53,ob2_53_bad⟩,
  ⟨ob2_54,ob2_54_bad⟩,
  ⟨ob2_55,ob2_55_bad⟩,
  ⟨ob2_56,ob2_56_bad⟩,
  ⟨ob2_57,ob2_57_bad⟩,
  ⟨ob2_58,ob2_58_bad⟩,
  ⟨ob2_59,ob2_59_bad⟩,
  ⟨ob2_60,ob2_60_bad⟩,
  ⟨ob2_61,ob2_61_bad⟩,
  ⟨ob2_62,ob2_62_bad⟩,
  ⟨ob2_63,ob2_63_bad⟩,
  ⟨ob2_64,ob2_64_bad⟩,
  ⟨ob2_65,ob2_65_bad⟩,
  ⟨ob2_66,ob2_66_bad⟩,
  ⟨ob2_67,ob2_67_bad⟩,
  ⟨ob2_68,ob2_68_bad⟩,
  ⟨ob2_69,ob2_69_bad⟩,
  ⟨ob2_70,ob2_70_bad⟩,
  ⟨ob2_71,ob2_71_bad⟩,
  ⟨ob2_72,ob2_72_bad⟩,
  ⟨ob2_73,ob2_73_bad⟩,
  ⟨ob2_74,ob2_74_bad⟩,
  ⟨ob2_75,ob2_75_bad⟩,
  ⟨ob2_76,ob2_76_bad⟩,
  ⟨ob2_77,ob2_77_bad⟩,
  ⟨ob2_78,ob2_78_bad⟩,
  ⟨ob2_79,ob2_79_bad⟩,
  ⟨ob2_80,ob2_80_bad⟩,
  ⟨ob2_81,ob2_81_bad⟩,
  ⟨ob2_82,ob2_82_bad⟩,
  ⟨ob2_83,ob2_83_bad⟩,
  ⟨ob2_84,ob2_84_bad⟩,
  ⟨ob2_85,ob2_85_bad⟩,
  ⟨ob2_86,ob2_86_bad⟩,
  ⟨ob2_87,ob2_87_bad⟩,
  ⟨ob2_88,ob2_88_bad⟩,
  ⟨ob2_89,ob2_89_bad⟩,
  ⟨ob2_90,ob2_90_bad⟩,
  ⟨ob2_91,ob2_91_bad⟩,
  ⟨ob2_92,ob2_92_bad⟩,
  ⟨ob2_93,ob2_93_bad⟩,
  ⟨ob2_94,ob2_94_bad⟩,
  ⟨ob2_95,ob2_95_bad⟩,
  ⟨ob2_96,ob2_96_bad⟩,
  ⟨ob2_97,ob2_97_bad⟩,
  ⟨ob2_98,ob2_98_bad⟩,
  ⟨ob2_99,ob2_99_bad⟩,
  ⟨ob2_100,ob2_100_bad⟩,
  ⟨ob2_101,ob2_101_bad⟩,
  ⟨ob2_102,ob2_102_bad⟩,
  ⟨ob2_103,ob2_103_bad⟩,
  ⟨ob2_104,ob2_104_bad⟩,
  ⟨ob2_105,ob2_105_bad⟩,
  ⟨ob2_106,ob2_106_bad⟩,
  ⟨ob2_107,ob2_107_bad⟩,
  ⟨ob2_108,ob2_108_bad⟩,
  ⟨ob2_109,ob2_109_bad⟩,
  ⟨ob2_110,ob2_110_bad⟩,
  ⟨ob2_111,ob2_111_bad⟩,
  ⟨ob2_112,ob2_112_bad⟩,
  ⟨ob2_113,ob2_113_bad⟩,
  ⟨ob2_114,ob2_114_bad⟩,
  ⟨ob2_115,ob2_115_bad⟩,
  ⟨ob2_116,ob2_116_bad⟩,
  ⟨ob2_117,ob2_117_bad⟩,
  ⟨ob2_118,ob2_118_bad⟩,
  ⟨ob2_119,ob2_119_bad⟩,
  ⟨ob2_120,ob2_120_bad⟩,
  ⟨ob2_121,ob2_121_bad⟩,
  ⟨ob2_122,ob2_122_bad⟩,
  ⟨ob2_123,ob2_123_bad⟩,
  ⟨ob2_124,ob2_124_bad⟩,
  ⟨ob2_125,ob2_125_bad⟩,
  ⟨ob2_126,ob2_126_bad⟩,
  ⟨ob2_127,ob2_127_bad⟩,
  ⟨ob2_128,ob2_128_bad⟩,
  ⟨ob2_129,ob2_129_bad⟩,
  ⟨ob2_130,ob2_130_bad⟩,
  ⟨ob2_131,ob2_131_bad⟩,
  ⟨ob2_132,ob2_132_bad⟩,
  ⟨ob2_133,ob2_133_bad⟩,
  ⟨ob2_134,ob2_134_bad⟩,
  ⟨ob2_135,ob2_135_bad⟩,
  ⟨ob2_136,ob2_136_bad⟩,
  ⟨ob2_137,ob2_137_bad⟩,
  ⟨ob2_138,ob2_138_bad⟩,
  ⟨ob2_139,ob2_139_bad⟩,
  ⟨ob2_140,ob2_140_bad⟩,
  ⟨ob2_141,ob2_141_bad⟩,
  ⟨ob2_142,ob2_142_bad⟩,
  ⟨ob2_143,ob2_143_bad⟩,
  ⟨ob2_144,ob2_144_bad⟩,
  ⟨ob2_145,ob2_145_bad⟩,
  ⟨ob2_146,ob2_146_bad⟩,
  ⟨ob2_147,ob2_147_bad⟩,
  ⟨ob2_148,ob2_148_bad⟩,
  ⟨ob2_149,ob2_149_bad⟩,
  ⟨ob2_150,ob2_150_bad⟩,
  ⟨ob2_151,ob2_151_bad⟩,
  ⟨ob2_152,ob2_152_bad⟩,
  ⟨ob2_153,ob2_153_bad⟩,
  ⟨ob2_154,ob2_154_bad⟩,
  ⟨ob2_155,ob2_155_bad⟩,
  ⟨ob2_156,ob2_156_bad⟩,
  ⟨ob2_157,ob2_157_bad⟩,
  ⟨ob2_158,ob2_158_bad⟩,
  ⟨ob2_159,ob2_159_bad⟩,
  ⟨ob2_160,ob2_160_bad⟩,
  ⟨ob2_161,ob2_161_bad⟩,
  ⟨ob2_162,ob2_162_bad⟩,
  ⟨ob2_163,ob2_163_bad⟩,
  ⟨ob2_164,ob2_164_bad⟩,
  ⟨ob2_165,ob2_165_bad⟩,
  ⟨ob2_166,ob2_166_bad⟩,
  ⟨ob2_167,ob2_167_bad⟩,
  ⟨ob2_168,ob2_168_bad⟩,
  ⟨ob2_169,ob2_169_bad⟩,
  ⟨ob2_170,ob2_170_bad⟩,
  ⟨ob2_171,ob2_171_bad⟩,
  ⟨ob2_172,ob2_172_bad⟩,
  ⟨ob2_173,ob2_173_bad⟩,
  ⟨ob2_174,ob2_174_bad⟩,
  ⟨ob2_175,ob2_175_bad⟩,
  ⟨ob2_176,ob2_176_bad⟩,
  ⟨ob2_177,ob2_177_bad⟩,
  ⟨ob2_178,ob2_178_bad⟩,
  ⟨ob2_179,ob2_179_bad⟩,
  ⟨ob2_180,ob2_180_bad⟩,
  ⟨ob2_181,ob2_181_bad⟩,
  ⟨ob2_182,ob2_182_bad⟩,
  ⟨ob2_183,ob2_183_bad⟩,
  ⟨ob2_184,ob2_184_bad⟩,
  ⟨ob2_185,ob2_185_bad⟩,
  ⟨ob2_186,ob2_186_bad⟩,
  ⟨ob2_187,ob2_187_bad⟩,
  ⟨ob2_188,ob2_188_bad⟩,
  ⟨ob2_189,ob2_189_bad⟩,
  ⟨ob2_190,ob2_190_bad⟩,
  ⟨ob2_191,ob2_191_bad⟩,
  ⟨ob2_192,ob2_192_bad⟩,
  ⟨ob2_193,ob2_193_bad⟩,
  ⟨ob2_194,ob2_194_bad⟩,
  ⟨ob2_195,ob2_195_bad⟩,
  ⟨ob2_196,ob2_196_bad⟩,
  ⟨ob2_197,ob2_197_bad⟩,
  ⟨ob2_198,ob2_198_bad⟩,
  ⟨ob2_199,ob2_199_bad⟩,
  ⟨ob2_200,ob2_200_bad⟩,
  ⟨ob2_201,ob2_201_bad⟩,
  ⟨ob2_202,ob2_202_bad⟩,
  ⟨ob2_203,ob2_203_bad⟩,
  ⟨ob2_204,ob2_204_bad⟩,
  ⟨ob2_205,ob2_205_bad⟩,
  ⟨ob2_206,ob2_206_bad⟩,
  ⟨ob2_207,ob2_207_bad⟩,
  ⟨ob2_208,ob2_208_bad⟩,
  ⟨ob2_209,ob2_209_bad⟩,
  ⟨ob2_210,ob2_210_bad⟩,
  ⟨ob2_211,ob2_211_bad⟩,
  ⟨ob2_212,ob2_212_bad⟩,
  ⟨ob2_213,ob2_213_bad⟩,
  ⟨ob2_214,ob2_214_bad⟩,
  ⟨ob2_215,ob2_215_bad⟩,
  ⟨ob2_216,ob2_216_bad⟩,
  ⟨ob2_217,ob2_217_bad⟩,
  ⟨ob2_218,ob2_218_bad⟩,
  ⟨ob2_219,ob2_219_bad⟩,
  ⟨ob2_220,ob2_220_bad⟩,
  ⟨ob2_221,ob2_221_bad⟩,
  ⟨ob2_222,ob2_222_bad⟩,
  ⟨ob2_223,ob2_223_bad⟩,
  ⟨ob2_224,ob2_224_bad⟩,
  ⟨ob2_225,ob2_225_bad⟩,
  ⟨ob2_226,ob2_226_bad⟩,
  ⟨ob2_227,ob2_227_bad⟩,
  ⟨ob2_228,ob2_228_bad⟩,
  ⟨ob2_229,ob2_229_bad⟩,
  ⟨ob2_230,ob2_230_bad⟩,
  ⟨ob2_231,ob2_231_bad⟩,
  ⟨ob2_232,ob2_232_bad⟩
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def obRow3 : Array Prohibited := #[
  ⟨ob3_0,ob3_0_bad⟩,
  ⟨ob3_1,ob3_1_bad⟩,
  ⟨ob3_2,ob3_2_bad⟩,
  ⟨ob3_3,ob3_3_bad⟩,
  ⟨ob3_4,ob3_4_bad⟩,
  ⟨ob3_5,ob3_5_bad⟩,
  ⟨ob3_6,ob3_6_bad⟩,
  ⟨ob3_7,ob3_7_bad⟩,
  ⟨ob3_8,ob3_8_bad⟩,
  ⟨ob3_9,ob3_9_bad⟩,
  ⟨ob3_10,ob3_10_bad⟩,
  ⟨ob3_11,ob3_11_bad⟩,
  ⟨ob3_12,ob3_12_bad⟩,
  ⟨ob3_13,ob3_13_bad⟩,
  ⟨ob3_14,ob3_14_bad⟩,
  ⟨ob3_15,ob3_15_bad⟩,
  ⟨ob3_16,ob3_16_bad⟩,
  ⟨ob3_17,ob3_17_bad⟩,
  ⟨ob3_18,ob3_18_bad⟩,
  ⟨ob3_19,ob3_19_bad⟩,
  ⟨ob3_20,ob3_20_bad⟩,
  ⟨ob3_21,ob3_21_bad⟩,
  ⟨ob3_22,ob3_22_bad⟩,
  ⟨ob3_23,ob3_23_bad⟩,
  ⟨ob3_24,ob3_24_bad⟩,
  ⟨ob3_25,ob3_25_bad⟩,
  ⟨ob3_26,ob3_26_bad⟩,
  ⟨ob3_27,ob3_27_bad⟩,
  ⟨ob3_28,ob3_28_bad⟩,
  ⟨ob3_29,ob3_29_bad⟩,
  ⟨ob3_30,ob3_30_bad⟩,
  ⟨ob3_31,ob3_31_bad⟩,
  ⟨ob3_32,ob3_32_bad⟩,
  ⟨ob3_33,ob3_33_bad⟩,
  ⟨ob3_34,ob3_34_bad⟩,
  ⟨ob3_35,ob3_35_bad⟩,
  ⟨ob3_36,ob3_36_bad⟩,
  ⟨ob3_37,ob3_37_bad⟩,
  ⟨ob3_38,ob3_38_bad⟩,
  ⟨ob3_39,ob3_39_bad⟩,
  ⟨ob3_40,ob3_40_bad⟩,
  ⟨ob3_41,ob3_41_bad⟩,
  ⟨ob3_42,ob3_42_bad⟩,
  ⟨ob3_43,ob3_43_bad⟩,
  ⟨ob3_44,ob3_44_bad⟩,
  ⟨ob3_45,ob3_45_bad⟩,
  ⟨ob3_46,ob3_46_bad⟩,
  ⟨ob3_47,ob3_47_bad⟩,
  ⟨ob3_48,ob3_48_bad⟩,
  ⟨ob3_49,ob3_49_bad⟩,
  ⟨ob3_50,ob3_50_bad⟩,
  ⟨ob3_51,ob3_51_bad⟩,
  ⟨ob3_52,ob3_52_bad⟩,
  ⟨ob3_53,ob3_53_bad⟩,
  ⟨ob3_54,ob3_54_bad⟩,
  ⟨ob3_55,ob3_55_bad⟩,
  ⟨ob3_56,ob3_56_bad⟩,
  ⟨ob3_57,ob3_57_bad⟩,
  ⟨ob3_58,ob3_58_bad⟩,
  ⟨ob3_59,ob3_59_bad⟩,
  ⟨ob3_60,ob3_60_bad⟩,
  ⟨ob3_61,ob3_61_bad⟩,
  ⟨ob3_62,ob3_62_bad⟩,
  ⟨ob3_63,ob3_63_bad⟩,
  ⟨ob3_64,ob3_64_bad⟩,
  ⟨ob3_65,ob3_65_bad⟩,
  ⟨ob3_66,ob3_66_bad⟩,
  ⟨ob3_67,ob3_67_bad⟩,
  ⟨ob3_68,ob3_68_bad⟩,
  ⟨ob3_69,ob3_69_bad⟩,
  ⟨ob3_70,ob3_70_bad⟩,
  ⟨ob3_71,ob3_71_bad⟩,
  ⟨ob3_72,ob3_72_bad⟩,
  ⟨ob3_73,ob3_73_bad⟩,
  ⟨ob3_74,ob3_74_bad⟩,
  ⟨ob3_75,ob3_75_bad⟩,
  ⟨ob3_76,ob3_76_bad⟩,
  ⟨ob3_77,ob3_77_bad⟩,
  ⟨ob3_78,ob3_78_bad⟩,
  ⟨ob3_79,ob3_79_bad⟩,
  ⟨ob3_80,ob3_80_bad⟩,
  ⟨ob3_81,ob3_81_bad⟩,
  ⟨ob3_82,ob3_82_bad⟩,
  ⟨ob3_83,ob3_83_bad⟩,
  ⟨ob3_84,ob3_84_bad⟩,
  ⟨ob3_85,ob3_85_bad⟩,
  ⟨ob3_86,ob3_86_bad⟩,
  ⟨ob3_87,ob3_87_bad⟩,
  ⟨ob3_88,ob3_88_bad⟩,
  ⟨ob3_89,ob3_89_bad⟩,
  ⟨ob3_90,ob3_90_bad⟩,
  ⟨ob3_91,ob3_91_bad⟩,
  ⟨ob3_92,ob3_92_bad⟩,
  ⟨ob3_93,ob3_93_bad⟩,
  ⟨ob3_94,ob3_94_bad⟩,
  ⟨ob3_95,ob3_95_bad⟩,
  ⟨ob3_96,ob3_96_bad⟩
]
def prohibited (e i : Nat) : Prohibited :=
  let row := match e with
    | 0 => obRow0
    | 1 => obRow1
    | 2 => obRow2
    | 3 => obRow3
    | _ => #[]
  (row[i]?).getD ⟨ob0_0,ob0_0_bad⟩
def idBits : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 8
  | 3 => 7
  | _ => 0
end Live3210.SubsetCheck

namespace Live3210.SubsetCheck
namespace HA
def f {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) (i : Nat) : α := (if i.testBit 3 then (if i.testBit 2 then (if i.testBit 1 then (if i.testBit 0 then x15 else x14) else (if i.testBit 0 then x13 else x12)) else (if i.testBit 1 then (if i.testBit 0 then x11 else x10) else (if i.testBit 0 then x9 else x8))) else (if i.testBit 2 then (if i.testBit 1 then (if i.testBit 0 then x7 else x6) else (if i.testBit 0 then x5 else x4)) else (if i.testBit 1 then (if i.testBit 0 then x3 else x2) else (if i.testBit 0 then x1 else x0))))
def p (k : Nat) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat → Nat) (i : Nat) : Nat := (f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (i >>> k)) i
def a0 := f 21397609749984262 32684082647279617 14691675445141504 15765903673135105 2251828806811652 6606736588802 65308835709984777 5635003534808064 10135346515819540 12887003184 4516867868730387 5637214374472772 12413488426123264 5639398368477186 4504705588792337 7712689622049
def a1 := f 51865062994871297 1188633330581586 3379898802595840 18034189718781973 15505937165332 139670966387130405 1134717479951407 2300206342215696 3479958631484465 3378804608205824 4510199918370819 7709466298370 33784697008994312 14335530237954 1133598676725760 2255102647763982
def a2 := f 5647093885585416 9898891948041 42784228672274438 15762623479946259 19141417259501570 4517900796830728 2251799826294795 3300685551734 121608190424001538 20317880739430401 7758866819075 3344714172426 32667591066568704 42788598801500166 58546796254734338 36032197560373248
def a3 := f 16889620668088337 12408029521642496 3387606105659392 7886809797239817 6631452573721 129612690971696137 3377699727896613 4514605483165702 2277092876147715 61928902626441336 1139108005028916 23669301710946306 5630661334442000 4503607159292030 19194188475156598 9010506379622401
def a4 := f 86712988831103002 2207637342377 45036001863672833 30409193089423376 13520797567025153 9953595102233 9008300929634338 90074193718181888 34905097211228170 2351924122790918 68685401545506817 23089903588353 28147509482225668 12101073515543 1121052530716 47291124698644510
def a5 := f 64178514114387976 1140329923271748 70982271684839452 58547913996915758 25896799579676740 4516873226951719 1135798734841931 6838965548089430 37159096132081671 6759813598990341 1080156234 2251812723770368 6845604507544577 8798298197015 20444088373 15032462364
def a6 := f 37241558371741700 24820385155386411 11270012441508866 46166308200427535 4541931163661 75435308821255199 32651097490329604 3388702353014927 29305295305998337 101367277648105651 19156814720450564 139628115483944960 31551646887587853 57436294868900917 233127614092294 10150757995205632
def a7 := f 15770364004014139 7903500075801603 13516408334843908 1167718930728035 5736169348269103 14649892928495616 20315703227723819 6776599401726992 41688074661402626 81065892832627726 34956775346145283 28147505247097985 245481372653736963 4509097196002377 25907804331054087 1323822746702858
def a8 := f 50703985159440385 18015515208324115 6769709365068801 21393201003825187 24809440498685981 4505880501420034 111492733916416071 3515169856606225 49539796752664578 67573785628272646 7881321987776523 40820015104 45050292081903658 34951277771234322 106978084410922073 1270195895154814
def a9 := f 1147892322744322 13542686928669708 28279440144338958 64176294914425903 64183995696414730 4544422218838016 40557831451049990 19232800235333655 104464342102016 9007219675771934 7887906203040853 19331620865 284927457207788545 6769701708510208 109458614879544393 25895716143498270
def a10 := f 13540492243408061 6886242398554154 70931773669935150 86883971557408 1151189780616206 13568251985400845 11125061106771 75444099616918735 41674799007689735 201552619179618381 4602658754397198 6841161368993793 6765312225629353 22593875180786689 22575172871578827 57467082253586462
def a11 := f 20341005916047369 16896199610079240 138508780456395779 7899995352092672 33988104570298598 176783894825162772 24894050280670281 101357786843064332 11277698323194976 12433286089472015 40544508455379968 2272989053750345 130605500594131061 9030292485510161 29277796881749092 30420241948373081
def a12 := f 10150964093784142 18017712082007042 3377765309001732 50665627144614912 76563399132101632 160265928342276102 52921771144321025 31560398954056742 15001769943913476 14721365642844238 665438730795987029 1140673520702468 4515763055505412 1164384985419908 7887956552451075 25907831196614750
def a13 := f 9085266749816846 6786225511888002 266369586167838 10146314823315466 13513001129738267 23665941971749974 9011602676254917 27028587825930275 1100806620195 73211023702672384 44016859643909179 43914494431199237 1125917201007616 194827040560566279 130606772977139712 90156704403030090
def a14 := f 4564087834937362 389675733251848243 3415088506610735 65309920201868289 56430250480896038 31527405004865715 18218912073178112 239833192174015503 9079804603217920 28435574054457538 55170204610667526 56295107044846592 152224542201856 106967208578582654 288236976469248006 4505805148656750
def a15 := f 83346379782561806 4593881095132168 10134255582576640 187029205291109452 23973764417989075 42794172617338887 182396991869815905 24035368209747971 6796081372750854 88991178006078470 27498529172480 318878819288200 79967506547081289 63080087118946415 307455472368369724 76562312506392576
def a16 := f 4408789476405 49593480583863342 59747461869144065 82240217437701121 6833516427870209 44108352512 5940669917079699 108858173297665 28150885328617631 48522549801372673 521338015766832131 180201224132384825 202672087156360361 15948475326983172 2248422757424 4624552348892198
def a17 := f 14340977665028 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
def a18 := p 4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
def a19 := p 4 a16 a17 a16 a16 a16 a16 a16 a16 a16 a16 a16 a16 a16 a16 a16 a16
def a20 := p 8 a18 a19 a18 a18 a18 a18 a18 a18 a18 a18 a18 a18 a18 a18 a18 a18
def dis0 (i : Nat) := (a20 (i/6) >>> (10*(i % 6))) &&& 1023
def a21 := f 2738193467680490358 8540905530627355684 7207033975409476918 7278943402755167092 375316395837596421 9747202973213422709 321639275131306084 3995819071961895815 8536121555499038052 7283289496789214564 6062976578688062309 3896587857870217747 8446349877306541844 1374504057137698388 1393868918775637361 7283169420770625094
def a22 := f 3825074510613591556 289657779883676435 10809765506077373972 3855455116399477844 9742785883377329509 1500094711292676 6080898970404808020 10679724133366191188 9657254719748728064 3847558439970821255 36950187763377429 10592466832370124661 9688461079453131829 6072617013864662308 15221729242972244 8536188283472127270
def a23 := f 2600358211613910292 7314711544384066900 7305970014887367735 23665224788948499 9319221986468324726 15503617100354374 32762148046574437 8535539575131476992 8396810203339961653 18881934997 6081287991602722054 6072564465828959572 3857058285168629332 316401119886922836 9752263880565887744 8513492576787234816
def a24 := f 2617828636145112101 393650882988053268 8513405644956906752 5059361057608656212 5067786966864933139 11688248770869536310 5049525844512634484 7283206823251871094 1369115680027604023 5348026246889573 360346327895532884 23702254654914614 7279020963063170388 5116131258787968309 8502796115639664640 7221298802810311798
def a25 := f 1369205771187078470 2775765500097291525 5152176681960887350 433492853138941184 3820327262067490837 7305964581745132563 3819144843340502117 8180225792324665430 2630213233976345875 10481657976144069632 8215713019168253221 8432275619700801555 7207243745397637125 5067675916474646528 360327927451391236 8539480565105164358
def a26 := f 3914774867153785600 6274486546722158080 7205759766804899589 298666349712932965 5085126950816998757 7283323714526445652 12792304398855636308 7301588456404370963 8502937952356512053 7305124485865432374 1469128978035179524 28540522956404516 1513230727989462661 5971879126897939 2753106764389154820 1388803601547134262
def a27 := f 6058278713626612736 3995948662170948662 7306392206939816804 316436449477228116 7279002570158662740 2635542927593858323 1384089861551900197 6085899618783565157 303310337649960310 6081272388555011332 6052915300737749844 7277856942439368192 8476921310814245249 7306285571757069366 8504203704469456164 393615285212825143
def a28 := f 10669932434459747638 8504049622500795493 9477640716438164484 9743104888293097590 7306357450970777349 9761066715049186067 7206977821917541941 1563686215389434981 9583665518099129701 8548506674898765140 2595259986130326582 1536964857378923908 321587936615499269 1388874584488756837 20113384299385972 384008834936864787
def a29 := f 9612147761529386500 33214048429766021 7301466966357901348 7305987063213888275 3820747261851559267 8531353248731234304 6052930258165269093 388809665296105846 5049457910751712278 1514428169172895076 6306838439144980564 6076541261962573382 6022531999204422 19832992695713846 7306089502219437396 1379234280990048260
def a30 := f 9598618271451874560 289356509630977125 2770087605676762368 9689061752893248788 15200012024968803 33343808767983733 393220543377375350 8391332441167529829 6058596342300939109 5144613278664053765 5408499391534340 396879798841251188 2622367350909056357 1447206975316557844 8358722021806571620 1405707423292063780
def a31 := f 7278011613070099475 33325098856752133 9589008055049453701 19781545948767269 7315330568052569605 5931357569043 6252183903364453 1623266671728071494 312004108461801476 8358792467867514245 1541659419853484307 388738336393811075 1375416564571251973 6076574663079957381 6081394918018205189 1546534933819131781
def a32 := f 6072633942291793683 8531283344133346308 1402137911349150756 7297806694752875636 8454945858654765110 433492934748570275 7283804419086775830 7315927252290863956 1401806095333458998 7314132288030602629 9598689666971997078 3829615575503819829 2599795673447610196 1469411002016937235 1392883411391100785 8536102864898389588
def a33 := f 316770416741233238 10810105309919979109 9765585635092206726 6063382454152139608 6067760554012075269 2672401018101437524 2771530671190275701 8383174197771519588 9729012779049039397 1397634947109684837 9612148851860571253 7311196547947181572 6058860158245942660 8374010999953687556 316787254338336084 8472192724510119172
def a34 := f 1402473356909295205 388775235549495556 3819145276845749381 8359806831936501011 3996228978328469622 3820289516288562277 7099173176200935013 8358757875622896694 9621117302508692853 6063048325006116115 9661721442844234836 7229530179549560933 23755530520786550 7283165041517854838 3927568807004315909 3919665577824048228
def a35 := f 33219007945637972 6356326633403868244 6058278769465074580 9671309111165543699 1370312981384492036 6076611777778721063 7229496421377119572 2622681600794865924 6081267302489347109 8360181149961880916 8503718814690670150 6086163643253548307 7315927172343141176 366009912779957332 1532918459163477014 1369205421232252261
def a36 := f 1518561920815482423 2708510990785607332 6068185310209332357 8454475193576228149 1388800990482073172 2631039401781118564 8445734015999501652 1388520691486446724 1384140159367533587 338635648801137941 8531336480900281349 1384018389230519076 8152943608334595668 1518687741136950356 2599513851917980741 3834362445330474386
def a37 := f 7292811537311618695 1528132065489597750 1406551372522092148 8552747272203732055 320993032900269056 3859977767974097029 7301553690629195125 8395913005283751508 9756315313828623653 6072952800396407878 8358828334846837830 1374446938938896758 288340836106961974 5149308266841608774 6068130269631960692 6085650707998049301
def a38 := f 7293016875907417348 9583664767282996484 393508633391269140 28429479527671044 9539829638749296228 8504070513760761141 6072846147768317541 3842807931012908309 9612199013868844341 330529688308168532 288323040161568261 361525231988274835 7297597574486164886 7283307986348758661 19703755243271956 288357942388134757
def a39 := f 6085863059253253120 361418703632822645 447356527883715702 4072754230866626119 6077437777308304896 3891132640140674900 3856617320320616037 6085917468652802934 3927441240768282996 2594184798232081526 1411145544955724631 7315534645902398548 7277894513725884037 20916816118884 23648721618482787 7305986794972284215
def a40 := f 7283749165124157541 3991394336292303891 6058770125278946900 2594112991776683621 2631637123780969525 8539499402622957174 1428267298997760 6068097283524686611 7278966349668570196 433530855268644357 6090280003853112438 361435321149515124 2604790958259524679 7283257404523041909 1374591175163748692 3924452171496883255
def a41 := f 7292758282899719172 8436196840635131057 2761944030951847444 9684295370842080516 6052985317294605686 1469601827426178661 7306393392922330368 6076503059583947830 1397672056195122260 326326336954066260 6090366865803408900 326339532763010052 12926305181159027765 3906721588711864164 1392761783512757796 1370225916454008326
def a42 := f 6306468389583070464 7301591000198173750 5144522548805194757 7206996376219250963 370795210201187640 289661276735739189 3969139619939058774 8526551128207676529 7277821625731736950 7314711196471866755 5076792649994106439 7229514353688782086 3919368989409957716 2681141602347742868 9612181641549280768 3892383334910985221
def a43 := f 1451284979920163893 6080764830794781973 6054356758889182582 1370313054395585589 3842754744306590720 15558451193415460 244713039331755540 9743051965710361619 3901303059634152564 9656992298074191221 6302336206122263557 8459188726584935796 3839130071113041492 8526444622186435747 1392849235447190407 6081306456753438789
def a44 := f 9680487482909946916 59736099680512 2617723213223134533 7297349824164353125 7310841929086075909 32780858797855828 1411336786142103044 384043425715156551 6058278645718521189 7311158889082664532 1397527657483302404 3928551976319928148 6000593935086740853 11850680379072839842 7283276306685362280 397520068423361620
def a45 := f 1374588852968424549 9441063825246130980 8358688003690222676 7283728127861294710 12854701602776581892 7315120700952761349 9444985363320162102 7311031045166798181 6081413109083567123 7315856137600177270 8446312492028920950 6077403206316724997 3910813352193163382 1514465201364436021 9759674243984196608 8531002967842882900
def a46 := f 6063276117211886901 7287973621719708998 293578555420464133 1375147119707706480 7306044086429976375 9517128859180667923 9661124055555966292 7311196055399584902 33306708856274966 9517077981802030983 5121723435051152787 3824421490901071491 6058578683026035782 1533024272061367413 6081266872722915364 8430866046961063168
def a47 := f 7238978430092776192 8538824984331834486 7301609892588369268 9598971136284374272 6053987118702859269 7306267369701311605 8378384384477390080 365975761070325760 36894423897048832 6090122699586417973 3986870278682932342 3914881820412609666 5933473244410643 6085489616940663653 3968818144021538067 2689885949923456340
def a48 := f 7301481803867816788 7297930726784390292 9607327430041019988 293743563768202533 1411356575936177413 6090468914249406024 294586655849072468 3968802903629833601 1514621609393288310 1397527740428588341 8467179010793682276 3892523385946022243 6063013961816892773 388794614726010503 8359954373205656868 289505012997256709
def a49 := f 7306268396486019190 5144280132024100180 3851869149956618085 5090023356882027539 6054304128328815767 3851832245979739207 5076969121861949255 8531317936607270484 3852062039363314516 5067805392253420662 8508274290587796740 5008361724732274324 1384596809950057491 3852096125550133764 311984308139349126 33073672792442373
def a50 := f 1402369380037170055 8373621704097207173 4973139489301345955 365778193704301940 7297825242113840712 288307359464555797 7243498449612964933 4982130539228329525 6064208251846014548 239816766066673509 8531317791048148358 384024726842209876 1590708023673054500 8531373503551911525 8502892187780068692 8508219988229109284
def a51 := f 6072915481978995717 28609292638897958 8504614774948242485 3936768064312603648 7220789136739026579 3924453959835924325 9738338702485397861 5045161904322117670 5149448447627121668 8531264670422881411 1469657975533614340 3820571413781566468 1474405598297915493 23773663301162085 1456392646400873349 8387255042420466531
def a52 := f 1469585612238820100 8147915525378495572 393348317745407060 447603922861127286 6076609642926204244 5014287594189780534 6309635935750717574 77268709843574 4971974010716095542 36878055767045651 8359968664476542005 8517843421324457317 9395993743542400596 1370241378315154772 6086091616225067909 6076593281769211172
def a53 := f 8364138291758724486 6067848732582700307 8535524392932803733 3852377672472626055 7277943443082712134 7277817020195079556 328924780377306694 7311036559821993477 5067675502184183414 1518966673456239360 6052930260129153094 11786857584903201876 8436649839421503232 8509135210573468928 8536010162325259621 7301520704706774272
def a54 := f 2699352104851760388 10832394490165486867 7293298548739040645 28207099543827717 8395615033890993236 3847643168174716517 388775725739545445 7277945104172922196 6086052372549075062 7306375731732702582 311933052810196598 6054104538545459968 3919278548941431892 3919631642512360452 1392849318226232342 6085654556008710228
def a55 := f 3919666613209818228 8504296192522323045 383952992300643746 5000424360487646821 3919560638617395813 396598673667260421 2595609426287560037 8518300329368176212 6058809845968282708 7279228790178673920 288358149349717781 7301482294293051156 294233791327986999 6351612673460163702 8503943043137885302 6086144861950711060
def a56 := f 7311192830183372104 7297631730768503861 9656936296274462295 397730144125650004 3847541265494599013 1536982099258925968 6058278714457023828 1384686689922151764 3969190133049394486 1397615846046765925 7283165105156822629 5117574012217873412 288230956313355520 9540142453513982720 311933056527373696 3919539411825791765
def a57 := f 5144518583745078645 7292845553156712549 6052965803319754822 2614150843604415799 9670694622432748901 7297560189396608020 8142600914835174436 8504052384162649348 3834081158703179092 2667403622057522437 1473895420340364598 7279035690578638485 6058190752696308518 3919261996936291763 33273726146737205 384043000519725925
def a58 := f 7277875359527548420 3896606967874191493 465668692978726518 8504350141362545811 9679366525933651334 1528132348439233557 36419554812233349 8540092648505243237 6094905236950119428 6076611969173300224 9683924774709170963 8386976320788430868 6052930281337680640 6300910147853509888 9607396763455455363 6063662823174788099
def a59 := f 375530999013193220 1406253464713253989 7158492582018183941 8526463322689917952 7311160121828476437 8358703333838714469 7302100813060723782 8504224869529191956 3906049715997062675 6076593075857359876 1374569877009036358 10594302736516539749 3914846358533641061 5049419696791884548 6058262908418479108 8450571868250833014
def a60 := f 8214643048097141878 7293425748203046198 3842717274758079798 5049942992659808326 2632183920641446661 5352856403443716 8502796727842326117 38021689593853223 5440384943539732 1401745891999612928 9607432565447500116 42541973308517 8359916759789315075 6086073270951678821 19764084234146816 23702401772971425
def a61 := f 7288096976352470326 33341951998694144 388793910067270501 10630332986047100244 1236285180433555 7277909358267081846 15029224777942276 330495001829463140 6076482232989812593 7211389264743039126 1375005498363163909 6081270399989322597 8430831360531326053 321272990958720005 28506373664019271 311985324878620004
def a62 := f 3856511979286127877 1514713079345071637 2743685463519028342 7287971543995745381 7277823002516133253 1441331461938771092 6090914006200226564 6004570671365248054 6086072854664803924 293583915520983409 1397369898980999252 8502907507932664709 316665354346923268 1402436033121096549 9585459044294202880 8531285977755649846
def a63 := f 9608278579197793284 6076574590904434688 1392815586641511525 2671760914138563429 1590743817946162516 1392883403313140836 7277875290323576064 1441298117214615296 3820552524231278708 2739407202050921556 6058560249507812197 1393675591449187072 307933927373607797 7323281285630485877 3824404569829623300 10376404046683923591
def a64 := f 6081396989854285845 2689816962509722678 1374553593970197830 1392834277466768389 6058895344972096902 8517735523719067446 8518105779935868487 1414540298617862 28557916241159542 7310842291276903424 6072599650202051956 1442336415560189780 8436198082172006912 5144329116421818230 7292827891688301587 1393306649776984390
def a65 := f 8508255533381482085 8522626369913562500 12976336537641055525 12773989908661756982 1392830978464350309 7279073144316724598 11629831374493713668 3987785756314007158 8440893674343310389 8431993407683180133 2634979637540967428 7301572103136105590 7323276328446395957 6068149291022856454 8364722000357713286 7315049096600114277
def a66 := f 5072466626611672595 293725215650039350 3910923295116305478 1464796208617755732 32651531090151285 8504295848927319140 2766622379627451206 299300621699544660 8502936915571703943 7311036625922818164 1469586578916901989 2766165875600942341 7221368491768767763 7277909379976808007 1392761848450056214 9544816483151205397
def a67 := f 23664810239751764 380278192789083136 37827616419697765 316664048669496117 1369094593643021568 1523435574864905526 380051775285367812 8229595378875565444 393523342574904660 7306159740738892804 8378671211232916837 8463149241896027732 7306357250487309316 7297894442882826243 288322895726575637 1402401200396449028
def a68 := f 28429064252859156 1412133797844131 15591307968071238 8535821046609437696 971989821191798 2594185013552838023 8526440017403314181 7315030331637511540 6054375180810454691 6081397049980773685 5045550169112969317 8396810470096582228 6364717900519216501 8536010371680666997 1536895517022225814 1370241159862256485
def a69 := f 6067936901081420819 1389138402066302053 7310753968219780116 1369115600049476453 7311161479568643840 146596151387510 9747589928030865299 15504213471683956 7305968893553955958 7205759782354228086 23664788832003446 434039238230820405 432475736168203539 3838867088908502533 23736257020647424 1370225686709810451
def a70 := f 3847630325432018180 1397528839945715829 7225521429712745747 6081272387985634838 9535251144872703316 452088757207971382 1442688667374322724 5059008539044156292 3824530334221895010 8503980508690253174 1608910966883628564 7309630894335277189 361592353728103542 6063079871480079635 8436282602256893333 28557615827288916
def a71 := f 7247418264471877268 5406729871627126 7277978645485074277 7306269421610480932 9611918918133572864 8391354562970543415 865545269552134 7301520498548434277 7310755430712743557 3919559942306223222 5044072771716644965 5059061237499036997 3896479226150532709 1407097894504633172 7247247775673775621 7283309286669055606
def a72 := f 3829310189659772005 1536912218278757652 433774070418671461 9612089341645235782 8526440424341259782 380119067173217590 8526604938534880823 289642451142251397 8508149700287168643 11751077137083561333 289730131811120484 7238973812162696071 8502888816833738341 3964352346280064531 3861013228762334598 3820199851086579045
def a73 := f 7302083727192384852 40818700350485302 7310474165617976595 3820465371031479668 6067852229593077045 375227469398283109 10244585899239013 6067903009254539270 3901670889216238966 7309716390020493587 8536102803427624212 5996601269329089607 8504016860790129719 9440816427607413779 6054388790491247700 8535312389590287444
def a74 := f 37442241345946677 36334690300675924 18592773716 7283165041841799286 6302283004870292551 6081397048064877894 7297239133986239780 10814641339992658948 8504351168106100228 6085075060421325908 388512661401392181 7205764901706757238 3924328884479599687 5121529582347883283 1388927712149967635 6085881956011086645
def a75 := f 31547270117733429 5165950264407266917 20270615255646292 9589571480090670592 9589289742889255012 5050035350025888852 7319215218919494660 8382436218239325524 9319676422173111829 289415732706759798 23702172168844544 316752068553487872 8431956778501039360 2617757965344855040 1125902389870597 7288008800610811909
def a76 := f 5144646123116364800 1464937615878018069 5067696601017115958 37177786988756992 6052930341713477750 28453189373408884 393349204658119990 6090274071430628709 289484120373884499 6052916327268513280 32933081061008484 7310489069152466533 7238819519423346004 10448500005582446592 7288795098361757797 1401745817903367699
def a77 := f 15222220215383296 54 0 0 0 0 0 0 0 0 0 0 0 0 0 0
def a78 := p 4 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36
def a79 := p 4 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52
def a80 := p 4 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 a65 a66 a67 a68
def a81 := p 4 a69 a70 a71 a72 a73 a74 a75 a76 a77 a69 a69 a69 a69 a69 a69 a69
def a82 := p 8 a78 a79 a80 a81 a78 a78 a78 a78 a78 a78 a78 a78 a78 a78 a78 a78
def slots0 (i : Nat) := (a82 (i/8) >>> (8*(i % 8))) &&& 255
def a83 := f 171832270849 17609403662341 163238117377 52793738004507 52776570763315 105596082724931 527765589766144 176007764156447 300647714961440 299685709395988 123214147618831 88776982495233 176265457881091 299075853416448 1231461613045770 334294539046917
def a84 := f 25769814197 17635337043968 87969549600768 211406943162370 35287468134422 985318287212563 17746913925121 283467845643 17746918117404 249494671196194 281801398433793 55138806982656 77426913311 281483566645260 193514067503110 439839015147541
def a85 := f 404620283234313 53258022346848 1583331116320791 18056248055840 17660905523203 18992441888840 949978050619392 105570359144448 211192400318478 123600606601222 246290969620480 140780513568768 879626494748674 158561602635776 158338453098501 3729663729899520
def a86 := f 70489003276288 439804651280386 281681168719908 281509357420544 158751235508225 257698093093 299127321657345 70386003830785 439804772745249 105578890266630 474997801885697 6177 932420325064706 562975723243531 17738340818945 206187792386
def a87 := f 1037947646844929 395136993304 88553644097539 791751665147909 87995357128722 52776562366478 25774080005 176093789163525 2463335568336896 263994808211559 492667209254952 1407658364008460 35340106614790 232121171999 457568682043394 2216615831763056
def a88 := f 88253118163022 581203564435464 158372636661764 1637018291404878 88235816527872 17789771352066 140737488455698 17617964281884 17592186302466 188978561080 616138891411516 85924511756 17686750894080 422427230208023 70394514151424 1372276607952936
def a89 := f 1197668856496128 510199190329348 105733580394498 52785148069901 41943078 2656420109492224 35313271439360 493621002381336 88064017833984 1600923294001170 935546956300291 17721035063304 334466291597327 283124281950208 17626625560590 17643885043726
def a90 := f 678604941334 985179606757378 193643101057024 775293195370498 88381899950096 1460666883964931 123309412921348 25782509570 3307477084936244 703859592792081 105561924360193 228698485708815 257765177394 8992608257 1706777053761539 422212649705487
def a91 := f 1354598354819075 3132173880193034 105561844621312 53102996619293 35253091567665 193600033982471 263908606636035 2674149721905152 105630471821327 17635215458307 140737501040660 510465499240449 2550867001608195 175921864923152 1196741097527324 141450536818690
def a92 := f 105604849326171 105553716093030 70987223689240 33566721 88244427466765 476140078628864 35270292721664 2920449210060843 316702524993558 17781189896226 35192962035727 264140488794112 175921894273047 1284762320807942 326614857748 2216993641996297
def a93 := f 967656140230661 439847676280840 404620291608618 721288242929664 68744691712 53687107977217 2445313931487234 141115453898766 17807010017335 87969528545280 70428882112545 140737496754186 545830683807889 8589957124 405195804940321 528023375898739
def a94 := f 545453179416581 52974130870276 405840330778648 35184472758298 809249202507820 86016927772 228947531042820 88450560688131 4063812185505795 1618481204205707 35639651321880 686095255734272 264209216598017 292309465140 1057034405427282 601312206849
def a95 := f 158329770909702 52948465893393 1267513635663876 51539691556 17592555143168 651452141916269 2111844542064643 158390349209602 1620671566262282 71143927054348 422221155663874 1231495972784203 1090835802245191 669190549667913 211415516315668 9173014535
def a96 := f 176704219779165 176334676496386 598134791141378 123291398387862 141785464580100 387157562783749 1126604311091237 1202595172410 317286418219218 193703025463296 2410138082215936 35837307811851 123196900638814 193514327537677 1337014825793571 8356348563888160
def a97 := f 1301821767675961 140995220021338 231893911994393 5488873740173329 369856826310687 17617972664528 1600923390482464 70832684558338 35734178269186 175921957287954 934464641404934 17903034302499 105570296295426 492624188389390 34397511845 87960993167634
def a98 := f 427819063 1126423892867073 422642129575958 140763262355465 107631913992194 52828164968455 70386041528328 492615963252737 17781185669123 950003900102681 1178925615063051 88871501041692 826832773496832 1653734627121310 985188200917030 176600507353091
def a99 := f 35433480368136 2023702690576405 1125900045373472 228767234539541 282024975796326 5453681046851734 1125925924288524 2550927294758922 35442086903810 105587476004893 862480997838881 932549090181299 1759279006627878 140737664563239 317003072012329 35236104779808
def a100 := f 581246744858716 545392194226199 494944258 17687031840771 17600776063673 1462247578677308 70523409408038 52819545565190 1125917481046019 9118674944 70368765167616 141132633743362 4891006017226769 35296418770963 193514046488581 34405881874
def a101 := f 263960406380600 475985506254925 175957172334600 2005552162937119 703756173858886 34389108809 17192491101 34359758866 70386024718338 18159155556358 721494523359274 334252004608000 1196268760158208 176042119833624 738898070235141 299101522528432
def a102 := f 741491743916034 3958319538610176 1566022410821632 4030010780401722 17652471136267 1213861370626145 2375314499979271 879858410422300 4468459056422990 17635353837575 2269546799124549 475074947711164 475143662993408 35328831489 915394978213908 1284401409316868
def a103 := f 3940659241220116 17592475461646 52853930512408 158338293719139 1038102210873389 19559281252554 1460271713392727 475049161156611 3201821124448259 105819572037633 87961832046596 439806194681875 247055151218783 317088854009856 88794153877504 211286621278222
def a104 := f 318205537192130 439822627907672 70463262969857 678957166649 2480498286856221 17188900872 212368957112320 35528305029120 103159465999 4204755823972503 1400163608599 652844081303 6404019585064968 3518660547328029 105587564277762 17858557913275
def a105 := f 35487205093377 2023247646296163 1671378600237067 246290604670976 177047360211304 510835105579041 90142958291018 211699122626668 369462259861539 2392640767133734 841814171730 2515914561984788 423689996771328 17738269458452 545358145079431 1284246807257104
def a106 := f 448835641 3607154053390453 35433744590856 334346259007557 85991657476 18219289028635 7564768948797496 176437281746992 9448481391378439 38603224795144 213944320 616903399723047 932789738274821 438212499462 1266663315998723 35339674611822
def a107 := f 264046029529131 3078676048549900 53094389934080 1354599734796388 230605484767233 2199195054268416 18734697678885 1637937527679246 299290522060800 1056073062666349 914889598066701 140834167076892 52776558278767 123738507370498 879626620594176 5911077598570525
def a108 := f 916468871589942 816471959554 351843725445131 862446965229571 528041235191844 475006941554688 3555470673535083 757383164975132 6316187503820840 5506422968274946 17696011974707 600789065095299 13124030669230777 25202690 475007163568176 2322538252234753
def a109 := f 88384345368692 264656052674561 1970410736382088 1213998498316296 1741626469609572 1636237173592087 3379078220513324 35193008205872 369436553095175 5205500432427 404655213686831 2269984743129214 4503608854841344 1179174853167144 35201930068150 2973088111144963
def a110 := f 1284229589631013 106102964359211 1020561597669439 163997333525 422282329735172 476037200842755 791683063185414 2445314506113302 35192974614854 105562410901562 4667478781618347 1284770801653774 77468799005 35433501169670 211132032174080 54048627636335
def a111 := f 2957292320329734 1249191238111266 633490513088583 88055583301632 76081201678345 2762445655375875 7459164192245769 722681385263313 739481792364549 1759914523389952 2991376811866122 106223131164673 17609756178460 5806735654754306 1374390621186173 90383883886608
def a112 := f 1143664201961501 10080322624425996 246411048274154 266326867999 1231462208637004 709262804332552 4382189525401644 3483991969628160 1514637434578952 3343056514792447 36687636086784 10961787436566570 2429096244365316 2270104964304924 510181993644108 71184792252450
def a113 := f 429560758374 17592266229766 3379615284584464 140904832722976 53867500879894 211106597615871 691610107052067 351852508145666 598890256549889 2937912257679430 844433662755977 2621983275640842 651056926638208 703928024322077 791648443457763 1530520501233788
def a114 := f 950674347081728 299471325958161 1304355860905984 9007199355730048 1291886701 0 0 0 0 0 0 0 0 0 0 0
def a115 := p 4 a83 a84 a85 a86 a87 a88 a89 a90 a91 a92 a93 a94 a95 a96 a97 a98
def a116 := p 4 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108 a109 a110 a111 a112 a113 a114
def a117 := p 8 a115 a116 a115 a115 a115 a115 a115 a115 a115 a115 a115 a115 a115 a115 a115 a115
def dis1 (i : Nat) := (a117 (i/5) >>> (11*(i % 5))) &&& 2047
def a118 := f 1972002223360298 13062840253094480 14742323216777216 14852278569901317 15485581156997504 56475489288913058 53102805160 49547292482639941 56475469957243536 56405279970689442 56475421688463360 14918231832657920 14183746508968976 22670355664032648 40180855922020736 24354355584117129
def a119 := f 81792777708997456 72209983907318410 46867803542862889 36153403054955088 14284924228120724 11103253912146816 47358547427824336 14742327071998672 14883017512237474 49701588247941704 14746703132099114 45266965094498472 45832070743888336 36670224858143616 47393360553777338 45267000357835914
def a120 := f 24349922187020752 46181000414286592 14746702942575270 5315682384827288 5211754212737152 41167959745477248 72171972439904426 15446112375783552 83146031584303616 66787429155220249 36698452709182128 14918281517382050 13625767844118946 90120950284033353 47358613883523122 39972075298011145
def a121 := f 36262031142363793 56475373777095760 49189977175308585 48457997780830976 49136525192184092 46867808617290112 30153859632519936 46289594395709824 81709669017623048 46867938494493955 14883016439177473 36299330059704920 40605070017958918 31138600231016768 81111562954324608 46322513195645482
def a122 := f 39061588661125888 81109498698273849 81109430124712106 46797716898124496 15481214115325187 82239715293584400 31314987100408528 72818484203166216 22670307542225296 14887507917445640 14179371116167336 31560472092885897 56475374640693712 38850446047187768 82390941974049697 48458043696556365
def a123 := f 27773965640608339 1981668932553649 2580131417305113 90716944466182562 40567736867338880 14179473839729795 46867904284733449 75266864676131600 39584661919379480 72209933845280777 91847196237009360 90116610181966617 81227596786602154 24347693228833322 46285196349198720 27844352718146256
def a124 := f 23224010323052928 27773732519584001 90126995182202889 100253856252465676 90641988488335418 30685556069980680 14847913671316480 90719162858733994 37387853923177216 14746709343130496 32146786668452432 36297149155168640 81217136185423145 29880972550423082 56473143270791688 81111630280302848
def a125 := f 5915546597196330 47607616751325584 82239696633766145 13625806429931904 14918226536956624 63175810487601552 36294968092447120 39483483378884865 10922703439698185 66082973891515272 48422856224935043 14742376904198578 28380717926985737 30997493080918608 39409030032335026 39409016207868066
def a126 := f 5211714308219008 45705753764504264 73910082731126793 24459763798561152 23890217102618633 39409077247410896 58276716216371984 56966049828154128 46868085642314640 46289528922659336 56405358998096405 54717254517627472 46867875000759707 14746761105525642 37451866996574928 27817770225905673
def a127 := f 27844354051801936 48979226527382144 15309721544393296 22131023089451928 23892496388628785 27881760731803810 41343973890019864 72172521323115144 27773818421678114 14183774099845547 14782137597186440 72172587666428800 58276683602203344 39409078358901584 56475469951938569 1444347346329857
def a128 := f 15410800353196160 48422778311975169 24347606311295360 46306009920181048 81109431232004258 55875068079199128 40605017400452282 13062794538853000 14179439609924496 36224538408884824 66755081123507089 39061614360146568 65517769236185642 56330208915014050 36698420176015744 90712527163524048
def a129 := f 23890212488794896 27780415491441194 24455431345408720 14742280225214864 81179802870745816 40743546119132112 23116240180693292 38848291009703061 27773690762661057 72783298958635169 11065914602685112 91211756827890048 48669178135253704 36330091332028816 48669152368038404 45269214382144264
def a130 := f 48422812343540360 48458125309880584 13062777094701896 48423113142223012 49189996841777792 14883063495045281 31292678801069113 72172538373144738 45337305771313540 48455810901905458 30087388508336137 22107383602157754 13062841720998577 91246899354980736 47358526953148816 27811201847765905
def a131 := f 64970169339926928 72772932962947258 57212881967845434 14742263184804224 81194562911158989 39061697999229832 37381225513779800 14742425877753864 31701276043561744 86340046898 295074 14183806609173832 14883018594329747 72627750208293905 38850511246099272 30760516662237704
def a132 := f 64902043797697161 81109382905084357 23927664939715080 37387819362135056 66785229993509388 39409063469629568 14742263251993288 46180875179803400 56475469953106474 72185208820637953 39409144617452109 36226709112019328 72220348803734672 31560410150786048 31138197417237158 37451868062061008
def a133 := f 36224681972419080 107509045904 27782580380106752 81634917116684313 91249109138286617 11103280906252936 23786879933534592 13100134865945344 57144704334889122 66750131327908616 39726255063730768 23228353008605776 64970187383970504 49190054521846400 23927632240479048 64374234968807808
def a134 := f 5950677408094394 49136376072110634 5352467973970440 56475733620107657 39730120457603336 18200244093391304 14179345192029105 23784705837181313 49296501982141315 4228021011723523 55927775921605584 27811185916293153 81780053725264512 54888534716391681 91847228171771024 59788212947648512
def a135 := f 65535302143516800 10918826258792618 39694932021285456 81705352642724176 14918298693141192 14742376059353728 66082985530798241 6513662731762082 49016562635561344 55930032799922594 15481278421931201 83356473590166152 82237560126151504 14289312505975832 27919180808466730 65500199518787968
def a136 := f 72101619000611528 14179362417582345 56330225285419912 36259833284002504 24490598770430012 36698444978749904 14746677197984512 37385620428065872 47358511143422979 14742297275338930 48985854668003864 14847833148489728 48422836058073113 180388 15305230120161450 57215101089953050
def a137 := f 91847182189068288 38850590693108496 107718265173 27811203905608352 5915510215588394 56965999357905552 59123010224 72209969890081565 75501685642 4651059880726706 1444208523083776 46797748976081936 93491560448 33500027989055888 31701119252365482 45900240733247753
def a138 := f 81790530090042064 40322115047522304 31138324140886704 23178772480 55364808505238160 56473227379605504 27093715592 90118748836462592 91812039695122560 90717029137383424 81109376504609557 46867782645696725 36224536149019392 37381196321300737 41167988468813874 56998957661991073
def a139 := f 14179355009923856 28118630818 63175739108891268 39726273236972683 64374300609696280 31138169298848336 27916875107255040 2007200642891776 134201 46324653093865872 55897047634542592 72209876398518281 72209451641260944 86710785501561250 13100237963204922 155000590856
def a140 := f 46867835821737994 46867807632427442 23791260720599632 6372880011547024 46270871584809995 56938090773814165 82239778326723329 137658215441 24349843900071936 6511952413917346 37489268708397568 46797746166300672 90717031167478144 58795330153593472 55930405379539904 23890301401956770
def a141 := f 58061999921381393 21181869617840128 45269183092591665 116780 36224510088878345 37381370356432896 56966031435890688 15450461180170301 39442936630516280 48669057569927177 39408970640872578 49190040827384192 40604987266433024 11065867408941361 23892447868387772 136144
def a142 := f 27811122288593616 18766517437274298 72783318155839872 72172630661341888 5209660069197993 109129110344 23927600372131865 14179362148450304 49192219104009232 30154472073806378 37381253639026816 123858131122 39409015939269456 48454439194996745 14958377373839778 15305342524326440
def a143 := f 81181911861170594 30122495432726537 56475342562394112 49016503244491050 27782459810939216 72210049427286409 28328624682 27778138147334713 14742309359524552 14284894064378069 29469416016 11065805269869264 88317498168 46712130384 36299431808715093 48669214425219072
def a144 := f 54311476365988018 4862590173895040 32455978289117968 91209448605876224 24349895259923083 47393376248528896 38850539299066256 41167925583089834 48503118925247619 55894947149119488 31138264277158736 104727717913 170504 81109412906896433 30122650136215552 27773684293391240
def a145 := f 50110242436067361 63760679294818816 69088870613 18763342098202624 27782528895662208 46867782645752193 56330318537380360 14707067533265284 101433 23890188648338448 48422845486727168 39761423240443936 127319814153 156859763769 86339747840 82239674453590016
def a146 := f 10209561264 27811086104788992 55804888034345745 14179371250144402 81179785281872853 56966000440037888 47607604029161936 91213942050915280 47358596569160448 57179999212546073 91211636349814938 64904224378555313 14887387440087040 39584696073474440 37381271487774720 14179456659750912
def a147 := f 36220112042196992 27780417772979152 46178709102828040 2370085392535936 81182029010586069 4055548639051776 72102281118506128 38850511562936498 46324623901690883 81709830839114248 64515219149462024 30118754885304784 81217128639928888 30997525301875072 14183699998310400 45264782982399130
def a148 := f 54346689938755746 37387897850036224 27782634928220185 59828901215613976 27044872192 47358511088140288 27773775463125178 55910441150523785 14746676996931762 57177734942163640 47371727675588608 37381284674230792 14742251905550361 27773938595528704 39150682112 71505229857
def a149 := f 15305294687709475 156074377928 55296638784162560 15410862958926344 14777505508658256 14784060392182608 48457979455996624 2343490949395361 13627983285922835 22107383518200136 5774722478547200 46287397298736337 36926367211716608 24455396747902976 20635930285775113 73368240016939528
def a150 := f 14742261845822152 46322453206705291 47358164831806288 46867809758186185 5880188185346048 5915442989039778 15485615588278872 24915548210 5352529214832640 14179344118272520 46867810831880448 27881743709211344 5917599699474952 2343354602356736 46287336270468289 13663108295928849
def a151 := f 36294971661797760 49054026835923664 14179360001174675 5352512958256138 46496483863867553 23896906196402730 22107401922595216 36888901269323776 48422795083829632 5315588964483072 40015928313944584 14883047981301888 23228557526509859 20526258887801001 14847929957352280 30997588598688961
def a152 := f 56965999358149026 45679610414860977 55929986749562880 50212574393959368 36220187217231872 45902411436600595 45339565946506192 39408970640654336 30997539528391074 14918200810648835 55419051811416089 37263548577288242 63164790704540368 91246841795588744 67669002029772809 55910236269185412
def a153 := f 24349829874455609 29880964092116227 81194623074190080 38848219710512144 65622551216259072 81229788838672802 81825764397123609 72783298757186432 5809991327940608 27780386830630929 58795344980607394 27815599997567104 14289342533075656 14918212762814984 12508187691122850 67884168142436770
def a154 := f 46306007705567360 46797716025770402 5774695601416217 30997524834208144 65535417367888290 38850283820058649 48669131670694681 63895721794964176 14852324939567274 46707940545 36703160878041386 31560408808722888 64374315462498490 27844432237690880 81109328348746509 45306584189577784
def a155 := f 46883185947137153 14179427718299818 46867939433959808 65515527979995330 6513533928057096 37423041457949392 15305339519980056 46496486497798664 14847892573475840 23786862942411136 27780347265657987 23927647545623120 46867907644359352 36294969228579200 14742345325531520 13062758908246057
def a156 := f 40332989992928080 46322549814083840 27811168756192392 31560490417816400 23925529808787856 57179984113172898 66083002714831624 72209904517040512 22107400983678145 67884294660445194 27881801888913928 10989196342287240 154707951616 23791291725025338 48669057569783808 49192150226718984
def a157 := f 31138214664208384 15340446696022417 36220123056525848 14742262919462912 32100330258825216 14179313231446144 90116550887049936 75501798224 46867958815784960 51584 45306529112542088 29875957003452834 81109323513742088 45369991569 36261997075106180 65535353678780800
def a158 := f 89259639624 72183266232381449 23784681975602314 39584645809015729 5950602307941659 27773837690178640 24490550115867144 29857022765748992 90719228173365257 30997880727672001 81111059957754240 39327367168 72735489408422912 59122965656 81792697043812514 37381224448244352
def a159 := f 81109478217402624 20671340945 45269092738847104 45339547961184920 137678211984 72185226780002688 91847295809684673 46867804825583616 12499885345481898 66082934188317192 14746659892318744 81194658718091562 91249048937352064 30087140910710912 24349829878756032 49016675132150276
def a160 := f 30997521203462144 37387793391094931 38850465185769632 27773753140480600 48669102067331232 91844958977819292 23786941128583737 36824922070889377 134088 49192173480987144 27773663717702184 78450281096 90116575755155601 63213260233560448 39061635710695552 14746787538534400
def a161 := f 108716503688 36698399600411336 38850479266202064 82239680858524881 81157306973260488 55894783251660945 46988755969710680 40605017404604416 36261969323163946 81109410931277824 39584645742100642 46645186618 46324635251823120 14179425809772577 63813476678767440 46178668661756672
def a162 := f 58586483178800080 47502015370273152 14746787502653653 48420705599174697 52991413120 91246975424692386 78473464196 37381270418227200 81117569850974592 72172539647965738 14742358478425145 31736381336332312 120569462784 27815514248264745 46867782645579776 24495093072318848
def a163 := f 131019622656 176115823240 55437376272728520 64904171387730048 112151663116 47373972057620480 38850493900568593 14883042439236312 46881050886446273 59115247458374032 32148923489538584 64374232592884368 91207291277237272 36226882140675241 84557403325203024 5950919359385984
def a164 := f 31138243400079880 37489251457303640 31618989278464688 47358508806650913 27879600267497650 31560507798491660 23791232601817088 156851240960 0 9155661711802786 28185985480 69089099776 81634690368975009 46305959248712344 66752350740777552 91844960983423568
def a165 := f 60465208352 24490567375307442 81780052651463056 111153830784 27881415857143808 52974059520 93826580480 41224264338257929 173028758400 14852290620133840 55367007528309256 14742359623335936 72209397941711009 44304473363 14883115461913369 58276635543347378
def a166 := f 57179827324760225 173968297041 0 46443693128 37381325180895650 39584687619977865 47371724182436624 23786892612917632 40579783364533256 27780264548870450 6513597212295586 46867782645750280 0 69097297978 27773772671142052 57001246960789529
def a167 := f 56475435818681296 27782519404071504 30716791815667712 13062747893809570 46712295602 30087417662799872 27773691836530850 49016578411137322 30716781467484288 63970497616020168 13100251858621456 36698573643972608 173976879522 15410844234416128 14284931438119752 4547138054900357
def a168 := f 40567609338450440 45267048644872580 90717012972646475 72210013922433544 53259932472 21031453648 14742280032223232 74101293056 66754953863303346 56365458884607016 56966098008462336 24354337259014672 27811116201682969 36294965248185232 46868150943949448 49192208686954912
def a169 := f 39528846600610049 107718291609 64409402505040268 82237496545036672 41167914367523122 64899800386091648 57995142249840640 4020393727965332 49021057273875344 72147765274253832 46322518700733064 40605033502591120 137523989168 31714863147499648 39408981987377706 46324652368464464
def a170 := f 47358611593312297 63773933631046336 10837686412327977 5949062365986944 56928359611105440 58274462461612296 36259784790086795 47572469905620992 40579753089957888 72185137386883460 14707113976716176 39584726368995865 82237548486773504 56944119758631073 11279585944 58030406215139328
def a171 := f 2579806959643145 72101574503090944 63213210857352459 13062836578736912 67568425811221001 2535001457596984 46993126971193762 22107486598437712 31114619192052304 56998760496142857 55364835550081953 14746755551931332 15305214282375824 48979148177199360 46881101783760896 91244680821519265
def a172 := f 23786862950922273 45829930143097137 27773772318290081 57179880298942634 90156229822387000 30645883639634185 38883473309733328 23329509025630549 65497984305760856 27817666434181913 49788209453945368 27053402137 45900287579783168 72209385765470208 331954 31560410083861192
def a173 := f 46180890875037977 63165449731572168 39408970640763921 14289281300380202 5878048553510081 81709678040256682 5139144661678856 2547071933058097 31736395983366169 72102217083620048 23890363765751808 46306009651609600 14883100077588480 56963801416817176 23329592556296760 47358439709737424
def a174 := f 46867787436579728 14179409669970320 122650134826 23791358511385160 47358517157475233 72783362066776226 32181954812684363 5211713234373296 81192396838289672 38850527795722880 360618 23786921033597648 57107286825482368 55927852281080592 46304907263213568 45341660506456482
def a175 := f 55296794791247872 81179766359176065 14707223540380289 39971996095885321 49192178613895944 39726334449025024 73749316602220928 56405326074216448 72101660918456705 107718202248 5949064454934586 27780306165619072 90716942528362665 82237422443905928 13100219579349120 21177899194
def a176 := f 47515516637563401 56330268170659865 65535319189050248 58799728401498701 39413368687342497 49190021200257408 90126995106648960 28387381306 10993192132512464 54766781927129800 14777496474104456 14852297866140832 47341986466468512 47501925976899584 45369918152 11283372297
def a177 := f 50110242436096257 31738502647401104 45474 66222210951650128 107718378026 14887456533156018 99123798263726498 36226883080274048 48669057569802896 31138277952754188 11646921018018480 1936882560804889 27844335458455948 72102281051474865 91809816045110160 29880415410107296
def a178 := f 19847698094012970 14883078789110480 31560402865882048 23791301403836872 57179917678936912 90118815821123968 14847909484998817 31560453197605384 110612874192 55894801228234752 33394412730057416 45264747746234824 14883034759256600 47371663318364320 15305325746013080 262608
def a179 := f 48457996971545739 36224812154093568 58030304497832122 14144159791272832 14887458739161777 91244692129821955 73194559421073792 36226802934356262 23786834555305984 46178835616551312 47358547187073992 92828916752 77376553500 23791260720484864 63694848776 48457951337250816
def a180 := f 52990860432 93420465291 27844352973789568 58276615159855522 69097019776 36297232575924824 56914320253196880 48985716918715088 38850445980205474 23927660400958088 39726270099686344 14284930234825344 36222403491791816 15309726218325185 72102152377567920 36220183547549754
def a181 := f 12499820124748552 40253401176616969 39659459915647688 40743595305253009 46324648816718242 81709181610604672 2858352360164296 13100190680652296 48422857294329984 1875262451106561 47371739315077674 81780101311154944 59192302308073777 5317266350703552 23791261861551251 37390020532935632
def a182 := f 63164754134411409 36818332475409296 38883479584480080 4647240602800512 37385665801476768 49796188209350957 63952296240983451 5210081486610817 14742312437528704 39972075302239273 90116549813338944 15450394386932097 81111630255018368 56405232397265337 84451976544426504 23786960276504704
def a183 := f 46867903124079010 5915401749922768 11048777934754176 37451839943392008 14289361098678529 24915346384 46180970474383385 69088907336 39584662120704025 86344204450 5350881990118096 13062770145398962 14742342234358322 36222386777561165 23925378472065664 56473158392328353
def a184 := f 54311535757593264 5317412275823248 45902536367982976 45269120857605072 91844982092247969 46443700481 90116598489332496 14179408525001416 64970298068360208 90719080055767488 49190025304902616 31560471156998784 36138030226245930 37451850957620304 55296746502327369 45832106395322888
def a185 := f 14965882347412488 49190041532205610 6513533936468522 46867810772582400 55894912000008577 57014440218008272 15305240854838032 55894773109799688 46867910024109113 39584772327002496 27844415993323905 38850487830844352 37381223567338518 93459097239816580 173972411536 12499971984272523
def a186 := f 46868116646508672 11065785888934276 28127056256 46867873382531072 174039630800 30752515595275088 171887842450 63895673606593048 55930232359616512 39408970640671632 52991019392 40661342650105856 64372007759985705 31736350067949904 47572294721077248 64902032092873122
def a187 := f 38850488958976000 39584774474486930 81157205327553169 21715928245916544 37381286650183680 31138256850784312 56475361701116544 45902411436628010 37451868062006037 90116582496850816 14847805021540736 110751265416 20618935762157568 77376662297 46305968010766729 27844307339917481
def a188 := f 70360082594 64409481484288129 56367563109730724 56388728708531160 91213841973253177 27881798453371536 58743911002144768 14742425877754776 48422766965275264 56473116225885072 12499797940484736 90716932422062616 91213924791335040 72183076093110792 15410844368245817 81111596638437930
def a189 := f 37451909939855360 331962 6337739730452480 90120920814866960 178952 46322470315360976 81780199646202653 156788326400 20392927046025984 81217103771729920 54853320111639048 36698409536815522 38850487893954746 45302107279988041 15305201858910218 49192255965364642
def a190 := f 27778090151349328 82204061390250241 72209904726813955 81709794386299264 14289345943645459 12499312080912546 47358548321552640 66012781031432912 30997552308533888 49790439390353728 36138029116572168 39488517940269952 57212812673679786 36224555458548096 54769010885054848 14320159938581328
def a191 := f 40324408646173377 45264802679564681 56475649249902592 69227164577 74101555618 91211745411518848 28328473224 81790625670871168 41224339839867400 72783382866088336 23791301690444160 73503187156599336 30575522409349120 15305374744977585 56488600125774544 72209934850719744
def a192 := f 56965972313184856 15309757053140992 14883082222606856 1769724161666051 63213201025996986 47572341160467344 63165431272346124 36226737377519641 81109413846956672 56928681746572617 66573659624495504 46289527815416601 81792745156989464 48454384675361360 81192381138971405 36261914155333777
def a193 := f 23221730948415488 39408991751199240 13663187682263200 91211726678919760 14746825136607266 91249110098640896 27773836746346880 66080756413927821 31736391945925312 63165293748495040 24495076836346883 72185214834905130 82237510765335048 15450390367712523 126309141034 63774218672161109
def a194 := f 56475679549554688 30685532803736380 136249 2939083737792512 38848376570413656 81109495397220352 91246849050217731 14847876320665857 2007285547275457 14742406767428352 45300001915678729 40743657582860880 72147861454716928 20445171959201792 14742251905356857 72209901317990793
def a195 := f 14852242428166570 72783317279345744 58276593030157328 23892475993270297 81192396032887168 91246866288821136 30122495432637192 40094058743992716 45869512431501312 46289577140489424 75501965490 28118614016 27782614518651920 5317307033827456 36332333540000664 31736324199987345
def a196 := f 30997431810425680 47607548190242053 55331996185075909 40567650249660800 72172493003084160 58276745082568704 81192396235020602 72185184098954056 81709107106810576 46324683024699586 37423023132982313 31138277016785280 48985840713683236 29460812680 57014145035511936 15305228903660168
def a197 := f 49701498988265472 56475391551951384 56475390750884560 14742297543653417 46867782645711552 15446014513815755 91213888347046608 46867908958916658 15481123719086080 72783359121723916 27852857755652608 107584590288 56948929882750976 81792759383982080 58276590173466785 32942795866594200
def a198 := f 156859681152 15450444004655304 24385107708254728 5352422604013568 56488530562014346 27773716960727576 46867793928435873 154704000275 14746757669996716 23786862883778569 45369786368 0 23784809500246016 81792669990400648 27881783563964800 5915462911799944
def a199 := f 31173628548612096 11351038664 82204497627054080 14742321132208128 31701119252037632 53905 60196651008 50735935985947448 39409079765575705 23927659287544226 56192 36224584190001152 14777530099782168 13062747893997969 14742278950227001 28118614016
def a200 := f 45829896714375552 24349922166917888 65900632120342656 32123462732534656 39126473600261136 47658 77716315152 47358164831567872 39584617623362057 63811256829619378 27914850047971864 59391511624 14742264328917516 45302731152 27879561010222273 38850507993494811
def a201 := f 54344488759380352 13100184276418688 36698489897037067 37381282795147664 27782505390477498 47358548771639488 49190271451284224 46797764280975360 81705258815959185 12499797940395152 15340464704266896 86343993728 14742360621914426 14746743376348240 5209515293329436 14183777446312720
def a202 := f 6515727016710528 56473419222583850 77447924657 5350860750082576 27780351116654761 36224681980838528 77802766336 14179413101454665 14179389365584290 82239794495707672 14746758605871369 31701225925952077 1444301352274202 58276635543439658 56475326192168969 37381272623906816
def a203 := f 23892496329783714 5807746139161373 46881016077877248 265603 89259507712 40182804939590016 86552 57514164384 39659684206042008 90719147969352504 65535428720398528 47393469680989209 28185722880 52982612816 56652086729911065 178952
def a204 := f 52991007240 52974059520 72220380881918472 105604240128 89758802177 3492754739974672 14742341299114440 14777436277487625 91847207179387984 46287250712070992 72185137386806160 27773787642527744 56968343295658674 45830000528677400 66782991141044224 47393730688188416
def a205 := f 5315588964483072 55894861462929570 14184062293901312 36208172276711713 81634643589372424 69093066810 42166616482 53632 33392196254466210 14742251905356857 5948447165973456 45933548141679673 73414511863901315 14284900446374276 14179477132447914 56341735865865360
def a206 := f 47341506337083916 14852231186689186 30997477176093843 81192424055184073 24494979637021971 40780914392994256 27782581682045640 90116613096981120 65949310235181056 2499830014948249 27919143196527568 91312963323236530 65412318792698020 30153958838819200 22670388006223872 48455762523032497
def a207 := f 39408981654950272 28127134408 58586404619389632 23786941996776200 15309754680267520 27782529037679010 55875024873062400 15305229985943602 27811047113143329 72172493003229776 82237482976527104 27817688680315945 72185312571425480 39972028308228688 23294914255853765 27852852396470288
def a208 := f 27780354609917961 30122573148849232 36224568407130576 10837686738917952 15340397510308258 66498796444134547 56473209946184400 30760608668432512 15305201858940978 11030650694455937 24349795858600472 30649270123760004 31138169298729600 36224618707049616 81179761059791432 36224537133601296
def a209 := f 14284883186733968 30727546001981912 36226754481891345 37387821576761353 27778149007807360 14887447592784776 56475385474450128 72818531251196428 15305229977370668 23791308313891213 48457990736220202 14742326476570786 39584625358637745 11063587921597264 81109434667515147 37387918318291329
def a210 := f 72185164431766152 38850494235709618 27879648567460258 14179394378177032 47358467895405707 72172519861342744 31138229831381410 36889033545783816 39584645888660352 82204514811136944 47406621055517128 37907932387584162 40791230930586424 46306040804485561 91209465713447824 81146716849607240
def a211 := f 81109348433115776 46867809690624305 5880247308356272 46867887104899856 23329549861489232 57212837588837008 47358492956803840 46797797908523792 57179852240093610 58065529511922064 14781909825622992 46867810764241314 48458010728731449 36259849164601896 55927880010599240 22131056387869440
def a212 := f 56473127240204940 48458026655425850 82239685161762944 57179898825615744 82204593954601088 91246828457053466 23791253427786192 15305274162389840 57177783210836552 72172556899297585 72783324770783616 36604126683080729 56473144344586266 46867893262502538 30725411740158484 27844482457254016
def a213 := f 23786972213582344 30122635762860032 11103232452018730 123786707848 58276727851496717 14284915264883664 12710949551180849 32831492977187472 14742342234417177 5077015881030480 64955905880998016 24349813701230796 30997520132116658 14179458740145162 55892645386007821 14179456885281288
def a214 := f 14179391345143833 48979291807994256 12499859832624016 29536500777 31560409882439978 21106393784 23892456764953480 45302183553564829 46867812253171712 27782547362601344 81179692258014491 38848100768415744 46867891257779227 13064975111891235 31701143093658069 58276683999972016
def a215 := f 38850463038479763 36292707928449736 27817644182732800 55892602627162936 99724065379500416 90116569220392985 63175859587076616 30118724518369800 31138228689982352 23786927384428960 39413477217575217 66080709026125197 30118752607647872 56475490366573328 48979165487214624 37263686255129224
def a216 := f 31560394184165893 72973318952606858 45832103157416064 63211096366993928 49136505860446976 36226754490749448 49195770091733154 27817697362917930 39584695339501952 36072107716782105 1745227958360584 31537320415048835 66622038290250282 55913589536174609 38850446852653656 66617
def a217 := f 48979177370168089 30997543962018264 56475470229803832 47358486161725754 37451929336562432 65502317063084297 170249 49016609917981208 48979294966419920 91244674756411932 15305201858907395 58276698919666376 64899773341340683 36226814716357771 14777540732551328 108051139272
def a218 := f 5915379157705898 13625771948038672 30122599891740697 55892650994868481 48979257531216800 82237492668968114 48979224308535808 45869601138180258 48666858546583952 28127111330 56490845935819792 36220189490020352 5350773336651019 45902549038418440 30575547197364816 5915466379870762
def a219 := f 22672569849610240 10918725268154384 86339836440 14284966222081181 38850465387098257 5915383588622800 39691006723054472 14179376053262856 46867791410203569 91847211584621136 14746743778855440 39694901686512009 76374252040 27916935303790592 31315024447082546 38850481034136152
def a220 := f 178250785416 39584773606381833 36297103916663338 90754286165774873 75829802142575801 66189775358448016 36261903689842688 14746720311820928 36220190492459008 23446644423448976 11346809288 48979244780528001 52990953685 15410847803900616 65500261398120744 54166340831090994
def a221 := f 64742053619383337 55927880097726928 5354917331206306 24349789029281924 82202313843390592 56998982581364761 11067985967993872 5915411889291432 10837700496588800 49267238540280776 56475374640642217 14918196017072816 14847880188298176 30997524165312684 36220187216818338 36698468764615210
def a222 := f 73416763438826026 22107356533047440 82239795510725512 5812157421927465 63164743992682889 64917503185310096 91211725742967888 91209562325079040 69160043336 45705755714703872 14320050786937733 39163849544389128 6513678766769224 5350928039300154 4514073106621579 36138017374840067
def a223 := f 39584724058546481 56979235549565448 32449432750443538 39694902786838912 23223962049970594 86708742318545416 91250990535192994 39061577949427873 82839964752314786 48734100714965512 27773772300396706 5915510244024577 31138244465347336 54344488759408768 39408998759469776 47393687772205700
def a224 := f 32100270091643907 33394378438431752 27773753110954696 23223942116021072 27782567395393706 66080757549945216 15305313012678959 14742327739920461 14883028544465153 38850508156422493 30118807155554722 81709684981060120 56966062071790149 39584755238511240 56488538648291721 57177698732629136
def a225 := f 27782564502343730 11028381429960754 46993231430421561 14742276819466794 82239632749738112 37381224439919521 65622516751895064 45867237940265680 36698521247823881 156788658226 81254547733676194 20526370505382928 14360176535624200 5878567045073429 47607507211864584 6513582058001552
def a226 := f 27780285702775089 56475421895672448 13065040337305600 81217144880435378 64374209568624896 14742296197370034 13100176659012104 32301609460577419 29854809729415177 27773716969083264 91211712054296973 93491702553 81790540064131912 27780399589530883 5950646322930320 23791339248399491
def a227 := f 81227675720618824 31560472118037561 20445173033157325 45299889273975432 72255517480765824 56473190729889920 23223993281075584 15450416022574090 47371661967766795 28127056656 23857277400954889 14742323212582912 27844415958158529 57000988485192369 81109417233887241 14742280300706210
def a228 := f 72785539966786072 45339553909348421 91211792198482474 55930028780830976 123790887496 14882989393623458 14150807008751649 24455448774625664 24986724920 55296667104150585 14746678079066312 23784704616563408 23784757175255040 73760187793716129 5317364612071424 28127056784
def a229 := f 55913540548135640 104459376650 49547345662628496 0 30997443898266128 46324711145345744 49547465511438634 46868057523618768 12499952778400144 14746678070395570 14742315809636352 45299879064503232 14958380041452074 14883100138048592 36783236035117056 23784756010586290
def a230 := f 15485548810799130 81109334793142792 82239710889657096 27780546945063504 11065783741429888 15340560270283648 39726251044292992 37489362161839371 39761470795393923 39584642538425634 38850476187931136 13064958268148266 69096983568 47393402312511872 49192238548453912 4547119730039305
def a231 := f 69231238032 38850252913562112 37423065247952929 31138246746677960 33398834302432409 10208989952 48453580384471760 81109449556955322 63773931501432865 39409064467536516 5948907662135808 36224535008295696 40745822380531867 81709215640101121 49296373678604706 27881759827860801
def a232 := f 65949284234920354 39198963919950416 47330423273509504 29880905879499273 27881690735182536 27844360385331792 23925426267855568 36137969127522304 23896855714929224 90120989979085632 47358465702888016 33398818314330369 46797774832419080 50353291499049356 81157241529078352 46867828015596112
def a233 := f 5810181495914656 45079307954076424 81780078581233792 40745713185008907 66755014635958920 33500027989051776 75231731208798336 46993139059186048 90716925210077704 11048770443729808 46883203927034256 75823255547281744 48669162029621505 24354274977423665 5774721408936003 48422921669118613
def a234 := f 30575553346214153 64882181155389602 31138244465525200 27773716969113728 90116596865565384 91776907197565584 36111562313880216 81780025606802691 76575578632 15340415624514224 36226798505378509 45900373650712601 27881524548377793 38850831270084770 31738657350226744 47393635364350019
def a235 := f 47360812772281088 14746708614887842 36294890112588296 46797734283516496 37451951097166600 58030425357005955 27844366731223237 11103143295275544 55367066919632896 39413368687306777 5317346843480832 27044973392 82204475301560874 15305241186341050 47343667601642064 48455633276740232
def a236 := f 14179301952011305 36224596504009472 14883059390454025 22693941174915456 14918267257276800 49701607734190737 24459807176694280 40180983652417992 63896142514 66080661249737141 27937765828210697 29192442368 38850418734039202 66785298634252621 13627991374664144 66080648829391632
def a237 := f 38850487897817088 23294323646904960 39488583455837105 72185190373687896 64902000491529296 14742276891826696 46867809690622217 30997477377347653 36698427794527032 81109480369111594 65498001158265368 75762132199723392 22670280497470657 55437404391168520 39726248842285440 38850527862807064
def a238 := f 91208956655012552 58028100545413120 39163807666453264 56475423831958160 92359098368 8880555080 94504062145 156800099152 65996320434901896 5950610038412296 69996695936 58586405839831040 81192405518778368 56475343443436240 4646863990947840 15309635716289036
def a239 := f 27780417647069568 56475342642657698 65655034835162000 23786836987008146 55322031142701845 81634935437345458 39972062333504344 31138197417397056 90116594068038280 45745484471799978 14179361074797448 81179762558706064 14179392756124240 5812173172381001 27782516758337936 23927744002886320
def a240 := f 91252945483518336 15305255101803289 54874454437759696 66783069599796433 58795458827427001 3145198309937616 37387968508464321 39408998759471824 70300783762 55930016873261449 39061534906831232 39409058188657194 56475342495613090 81254534753127088 31738611247975088 23927581984369024
def a241 := f 37423005881766285 63760679294744994 18763165928049024 55188114997691272 46287262690456715 2579735155704912 56475360883413178 0 24349940563050496 39694843663989290 1460521117731200 15305201858695568 11666267221054616 65502394398313385 29192497945 14887387440087040
def a242 := f 48979172835512720 39584691724747472 65935788172399632 14183753107374498 14746758672911312 15340476559993400 27844307339879435 49192254685839360 54311565758971147 50110319879733965 46797779133661896 27774094602965170 63895768272186136 56928342359837520 31738530774493345 23791260997387088
def a243 := f 56979195791671296 5812093035647568 54348859761021824 27773672526797448 14883048516725520 28454328852 81227589815576969 22106857028602120 47341957173883528 46305960322519712 40604993673410577 40743571806724872 4754316397285840 71299121416 24385077601471152 5948907662138112
def a244 := f 39061550959447322 60491401733 23786863747924424 55804888034181832 37381225513661345 100254019976728746 58276711812355072 39584646010321024 14746674867000208 15450509277305352 81227611342687104 37451839943299968 55296810672032432 57179935925371434 18349062580545929 22001555523972243
def a245 := f 22707663892808512 38848034225834384 91213943091183760 27881737379990408 90716909360321232 91246881992196224 71505024134 39413421938714649 49333757920030729 6513646831275065 14883081752971992 63895667601443204 14742298348917328 45145215631758136 46988728924836816 58276745035428258
def a246 := f 27782566250121936 14179372378990754 11068079421428176 39409108298938513 40605071024798761 104799576329 72172614713608776 65535465101459456 81109348428808192 81790609790239696 45902549166002896 23786957339443754 30752070504321074 5211742569894736 46867843110752792 14883017722204210
def a247 := f 81192444359646537 37451915445015352 82204479261376669 27053376128 47572340091032136 40605121206344592 36224555458595528 48422842140332856 55929985600464921 15445968740792960 40604992532579280 4055654109132928 32831475793232290 38850526452058696 54769148080861345 36224521099086130
def a248 := f 55894802377527680 38850172243182168 54344635749847960 30685556539826481 73979696211087760 11103151968012544 66080820713065160 39726251044295168 86478337173 4547133990797730 65535412701018530 48422812335080128 57144669997453824 54272 14847832074953105 144008
def a249 := f 12119419971044040 14847882469364096 58743941738182665 46867051838439424 39409039737794708 15450365512323536 27811218996673066 48457951337394824 73381406037912589 20636020853253313 37451862123395081 15445968539428123 24349813701282376 48981388868759970 52974160953 82202312172950400
def a250 := f 91211644040420138 45829981351332012 38850529406925584 31138256716562888 14918247867071104 36698426653783307 56475390750926091 10837656606919424 40604970268262562 90154010828636322 91244621698695722 90716392843696528 24455428046331209 14887444954057392 5315726646706176 107513316304
def a251 := f 5361265140799530 72735471410724992 86920 38850522324765384 48669180353927688 13062777086291977 14284884268942032 64742080599031808 46303760368121984 30087364034636939 23791341251768353 37451839943269376 11048872403341482 46322454070612352 32272908538713137 46303733180530688
def a252 := f 48458106041244248 14179313234477056 30445844273300010 75501720320 72147823218696506 64372035878387712 5702078652066705 87176563089 14179475991662770 27773721231544704 55188090129481728 72818466290375496 28127138752 23228371908115497 81192491416756936 37381256939831296
def a253 := f 27844427818113592 54016 91847229237156752 55913557827202067 46324650891858816 10956194768456264 40604989329152960 47358528031167545 49790310549576842 55927832957794432 27780348205404594 36926326430503942 46289595536673608 12499387142144793 14883031560128805 82756143051645329
def a254 := f 14883081815677824 60196817316 59150436975823232 81109478221545472 65502365104714433 139964037760 14179301951914317 66080674889810832 46645117392 15305248310558720 9155661652961305 11948726859857920 75501836553 125114536976 46322580885547449 47572449559153713
def a255 := f 27916970943053986 5913751408661504 14179313298528904 137682265545 20526306919797256 31701274090310184 46867827944108450 30997520368974600 37423132600958976 54874454437827152 38850558697720192 14852329111200523 55910194391155664 36078643959150720 72172521390166536 23791285576171682
def a256 := f 14179330079007424 23791232602022145 55897064961758224 14742304888273450 82239680858407253 91246865219146632 33394476153811371 5913816114831555 47393360486478472 39584705944834560 36299303924269056 58065512471700104 31173674115674121 64899784623915728 48702072111139656 13616506931949601
def a257 := f 14746661306277057 64460821450955344 59157116528710152 38850511562291497 39694870708867592 88286017664 23784723822262912 56475389350585024 5950834664362520 31560455860433825 90328697220 2544819662574472 46496482746041016 31560442296011833 46451996724 49192209618280713
def a258 := f 69092911129 66752244483695809 48669102948221482 5209555252546090 14958396294596634 46867861118960000 73416699063566754 90329078288 5702136394471824 58274498893370128 11101033690634554 90153981481058858 56341800088119321 91249077191758208 14183744361605145 31701140334329984
def a259 := f 45299967386075392 27916885114757453 32831525859502096 39584686550977360 12499308649820321 90296844842 56400672383439824 21181904948857522 49193662298685858 90116643266679712 37381221236578896 31736332011379208 90116594068065489 81194553127879432 72452580363 57179887860973568
def a260 := f 31701141285294480 39408980576960512 72147800443346064 31560409962319930 58743960063246514 31138197425750736 23892415999976707 45832168934097160 24494930048201352 75231637348080512 23786862674004480 31701243913568256 13100159408020296 23786861679979537 12499952849649664 5247188792017360
def a261 := f 37387871103167627 14254157199085746 5317411264877056 27784686952717008 46868151345926528 46883301035223065 57179915681962249 47393713474966216 14742327677031224 56473204583338034 15522905161015947 65533182393058000 14183856790962872 64303975717083736 30087423211914128 72745917710598144
def a262 := f 32146700100489600 46867792787426321 27095568040010384 30997525632748240 91312802769666048 5915450005347352 5352594487720354 46867811041231768 24459909644189994 39408970640826632 90716885456427528 46289467656522205 27881778291289229 55804965750571562 72185275069141576 58276635543247424
def a263 := f 46867828023886528 23223929032152070 14742344331449482 47341976235934392 24490561404471624 63175785820883776 55913489726833352 37387966419571905 30118690158684953 14320085078430592 14289329520137232 46797815022262537 56652187786463496 55364897764585890 46289613573116304 31138277948431681
def a264 := f 31736330669108369 39584739266691626 46287299093866641 63165346802153600 56473497677138202 23784663919109434 39413414057155280 5950602299363712 23787009672781121 18311648167636146 23329498209538944 14854413441732669 12508072396434248 27811201975159472 14746708270029065 72783378116155960
def a265 := f 23892398686015944 72102250302082000 15309644398386048 56948956936061260 36264120894413200 45740812419518720 57179853389169092 5317267701276928 24354271948493200 5915494267988760 15305227918989848 37387949445360409 66783055708291792 48422794010212361 38850490167636001 15309675406932096
def a266 := f 56475392625715362 27773726338632064 45827702092595597 45339536801215786 39584663261582529 90121010233540770 31138258692552857 48669103149330850 27881719935851672 72210031102188160 12499403890436481 46289486174245904 72182961546109963 40182873591945731 72209919638604464 14918201884410688
def a267 := f 36698427987593808 30997491201870416 48422813408826184 91209548077665232 14742304879459088 31138197425675008 55890531851735218 36926418023109770 14179360022145545 74666480923857424 47393699583283584 65375062157656520 24354356599015944 72818593762548288 46867876137193856 39413445262674993
def a268 := f 15410812564359704 23896892328954624 36224584190233603 14742280032265537 90719100518663112 55894844417036672 72172571952562432 13581203343123280 14183807716636713 75501834704 46180915730389704 81109351632340048 36226846636030736 63175845782573592 175184749835 45902475127063360
def a269 := f 56473289254588936 4055620072937992 14183759743169160 91252943537602722 30087355490959560 40324385382510753 36698399600368136 27095265043456265 22107330543966728 1885770159751168 63164743992707490 46867875071990360 33398810583498752 81108801876435890 15305243204690177 91211689323802633
def a270 := f 14883077715132416 15309622949707776 58276665675219400 55875301082679952 55892574086660560 81227642636962504 23822078050353706 23791309510351440 45902472666939392 55910515251815048 45299967386169737 71433886217 21638692913582258 91211636349894818 27923577777011328 81817455445496320
def a271 := f 105604186112 81643567222790665 48669082489248256 56475590127104009 15450442121084928 137522983560 89156827688 72172545989774385 24354261412347904 37385721237516706 81792669990256640 39061553093380785 74100998562 36224596499759104 90116522768356368 56473391103761546
def a272 := f 15305275959462272 74503627408 39061534902729352 53058558856 55984179745217032 90642113167884288 46306018539516065 111153917961 27881690735282730 36224584190118101 137658125322 81194535664767504 30153936178598408 14847960727829643 23927632240365952 95835800329
def a273 := f 11435853276691209 46867828078367232 81192407940582272 48979258671975168 31583799561886400 123790832264 63164819704381440 66750005725436090 54766749346468010 72783409370600144 55294714638851096 38850487826745928 46324694261576328 72102210737146937 38850423207637001 155848945962
def a274 := f 48455530422778410 107719774729 14852359927798280 24495009436881800 14746652706517025 49054041501801096 65513647018922368 2370087642766665 91249192631063576 29854872069264272 14958443618146637 14742340226947337 54753567457976634 14847864144566792 81111080499350480 48418544032034840
def a275 := f 47344173111750817 12499972990904483 72772855812719432 66012891664351232 39584656388521984 56475344508730129 23892475988942145 63213161500446890 81792824899668356 27782553633200648 13311070107343696 36698423441805696 81192365095694754 47358449915377792 48454449223581824 9940587016
def a276 := f 45829903865610240 27045013529 24919544656 23841526144 6512029499274251 38848327219583508 75550348572369237 2060868384718848 37385647355134258 28261260481 36332348635321168 5809879637867810 90116615127574553 14742329621819450 5772523597957712 14742280292383753
def a277 := f 15309624891802296 81792669990310272 27923609906319902 23791285575876608 49547447185195434 63175876795500978 27782548167965697 63210923480896384 27844463188527752 14742280032430601 31738530766208041 65517703253492176 15485695809342224 46303743184708875 27782470019668488 30997540464249744
def a278 := f 23786945709080576 14852214350883987 14742280024004873 10837722911121563 64361040963608960 55913619515292202 120478290320 47393713840371721 15305339588166400 27780329880361680 15340414282382595 63809078916952712 31616758779740616 37452011827046841 5702124815616945 37381222310199424
def a279 := f 81179717173317818 30997623025523336 48979162015375617 27780270723811456 5077102494308888 91317218658275840 3145228178040857 14179409536266658 81157242598510976 33497832405776393 37451885510281685 14254194781495552 45337384331155533 11053220248171811 91246992609783195 23786863089289604
def a280 := f 14742357371110144 81709750684832280 72220380882043442 37381220162748588 5315658048950792 36224602447950472 48979194352837915 30997539528671394 31288292000053257 46881084503404704 39762021587423282 36259771908639376 14742297476469132 72185190373448592 23892542509660800 9155662517015745
def a281 := f 47607554488607368 36224584190333106 39584705976341440 14742373548430529 65502401362180514 48457736656227016 64566518327857552 45829931955159458 14742291190292785 12499887333624192 64972461673813313 31138240732536960 23786887815220538 55930049840890410 56944119741766664 39584725337410128
def a282 := f 56966047479714312 14746822984767753 47358513811069114 36224622236181643 56999010636010296 36224587536552976 81217103771907105 45304451150547920 13100160481624760 14883066841731234 47358546387579041 14746660966552576 65502427352191360 56999045983457816 56649923185136384 6513678775013760
def a283 := f 47642771179323656 6478497695453952 72772931016559296 72210031331883648 82243514183795242 23329490763600408 58276679432899505 46797811728628352 5350866164964224 14742309420282504 90116580282370880 81780151649735180 32980172873532104 72172080933806337 40745713253009808 55294594690157232
def a284 := f 38850446860888857 81709119530126208 37451863804849419 14179355009846224 72818509067002512 47360746450932232 27780306358589976 14887457437057224 46797766156069128 56475419913800064 93454795919174673 39584646882986282 72172521390211928 40579765039583616 27844107963579008 45300033973699201
def a285 := f 13099670926637184 64374280884466312 40058560108993033 58030471452467457 23749544116884537 54344557487280648 56965972313004560 23784809508766672 81157162277618218 54689039580795961 27782485729559440 47572347783269248 72172630681271337 14742320998193804 72102195764052901 49016556230939448
def a286 := f 46797762880658320 36138034232238736 37451915445020697 21181862269534848 14746703203304528 72783427715337168 46867876472524986 56475358489420424 58276618300525827 55804917226611089 57179952323283328 91252946888699913 57014079775099776 6513559869827864 63164803383962393 46883222528864905
def a287 := f 27780415491166472 11666272640188680 23892478000736418 5772611230665394 41341726597635224 14887415768746282 56966025493356554 24455492420061720 2581957641044130 81780099707853840 15415307930716688 46305943483497232 27811116205965730 40183054945554610 15305275959612104 14883077711174480
def a288 := f 22107341827129985 81109417005321296 56475504312637824 23784688506374736 46305991595372993 39061568206549640 48454485667877945 14883115436720256 56998775143059840 21720409129091544 27782565280744400 5915425544218649 14847833140157184 90116631835705762 38883524560990241 81179719302886675
def a289 := f 14883052014580130 46885467190530234 15309643145423642 46883268637335564 40791143159506315 58276590173585872 90116631351179409 2546839572362144 45705770738781241 36888959986637392 48669184952519133 14256325279820169 72183046077592481 11065788018790578 39726290899093904 36259740032045904
def a290 := f 39584707045902813 65500280666632353 48669145891508740 56475343376108040 81792841882405688 49016549687927560 72172564302140609 63165417367591296 91249174611562530 6478416337608961 39409028707699456 72818484412729728 37381267628663947 5948978961144328 81109497485983744 14742304789889360
def a291 := f 46289527882496768 65480470188724876 39199041296417032 14746677063883017 32299300021158442 37418688370586248 48669169717320528 37423052929639602 81109381831830285 137658127505 72185181813920128 40605070986859656 63776181040428307 14742344734198109 55930018863877169 48422820145600840
def a292 := f 36297140468946954 72172563434639538 54349016616639312 15485591762441101 49192239620719010 41107761475619370 23786958345994240 38850540357167897 13625823886068624 23786990538415128 137658346248 27919120842658520 52986847633 14742389634742912 49018711129980928 47343607585476786
def a293 := f 232451 58061931353786768 56475325185628425 0 22107389890242722 46178775884365824 14179458807472848 14746678070489736 27780260787474968 75166646272 65482607332735402 1383460505649152 55804974508218633 28118850384 66785172187714248 36210511760327210
def a294 := f 54766744539640456 90719098380747170 31560489481929424 14183808652333952 14742346001809408 30997431810405517 6513647079260872 72783380366341379 31736389968085905 48668792897721216 58276727902699520 46885435363840656 24495031193346305 5807648545120384 15309690642280609 48422921803137024
def a295 := f 14742345396828578 92421603968 86339983960 23927625017862937 14887479866537235 36294971652974617 27778336642175800 36226836049040184 23786858416710970 55897061528174592 14742327684235264 13625725160786512 31138290937827405 75166816521 49192161506331336 40567581018555336
def a296 := f 46443528192 23786879052883083 2549217708998656 54768985222676480 30122516459793677 40745822396139905 27881718853870224 36857839800681416 14179731533711402 109128974336 24354182555382408 63165402398165832 23927572043960506 27852839767298432 46867810764358464 81709749221752992
def a297 := f 81709668950365336 46867808706044560 45832095738236097 91847211524698760 91809877285928960 48979172906875008 63165322949177353 47330430281748876 24349784508750992 72210033546512861 18311652680764473 37263548577071445 72818629117379408 72009961872 65624184067364033 55894862503064859
def a298 := f 37381223366132552 91246847766710749 90716933833593386 15481218682378640 82202313246292113 121871440848 30997610069277226 37894805929444096 24490610682302498 23896844178555434 14742426079140560 40745748547150129 46867957696235816 45378290432 57107259557251896 64531190186838314
def a299 := f 23228375007625936 72102212549062019 56966093936349696 32299325011284874 47358508806554290 58276590173587754 24915360907 65535291062061776 27313484705 31138248151769488 31138275002071185 65914161170916363 66621650716646416 39971927194515601 81217247541199266 14887415903783760
def a300 := f 82204506259102216 39759218202954112 6513532876175914 136008 81217149816946816 14746702925961736 57212937276314136 238296 15305356653712264 106573273165 90121058472106705 45339540340080640 55894784459461008 33394425746686416 66082935935797840 63895817366941705
def a301 := f 40180982783934464 81108802144997453 74321047785570304 66080648829337600 24349784508894032 72102231977024144 56475394106374152 38850446860915204 15305308536625536 54894600124694834 14742339318819971 5425569663731876 64902036055163042 14179459952290874 39726207058707152 27811107309617152
def a302 := f 72185166579311249 31138240597637538 24354210673906064 11030652975819536 81709734239084945 37331838775120272 90153980260551256 173028876416 56928400446642560 48457978390745680 23791318613013409 154980757537 28380594136154112 14742305081131008 58030388828176384 47358239530664064
def a303 := f 89393255184 14742304880009872 45269201392904217 154862426426 37451839943213056 45832112689035273 72101627489737088 30118742843279872 5915441650373124 23791358644964224 45902516902300036 15305291252013576 48458008852222336 46867905461234693 47393730759790768 91207266690343569
def a304 := f 31138230904607104 37451995997668024 107714159240 77716310400 5211745648582913 57144814840369536 90719066221855496 36698488993593984 37385619282973712 45829938244307480 72772885743196544 30434551021244458 36332315219118480 37451866988220812 14179407421808073 36299305006604545
def a305 := f 107718345781 48420707947915289 46867851729960960 55364837705824672 46305960545026210 81109392669516624 56614707548705168 55296662625788305 5915463294718010 39699266625751304 2431748397 56979253870222480 14742312101946651 9940740402 23927592715950724 55348368884517085
def a306 := f 5953083821657032 23223973995229832 6511934258153860 63213133787021980 71307569545 46867872038988217 31138244473829393 14847865218222616 14883144096432392 14179423590809600 46868231495876608 48985888802296328 23784814881639248 69996812808 22107436041109504 31138180645358416
def a307 := f 56913831913437312 46881150757522442 30997539319513250 91246909347497040 15481183915737088 40743525059134032 56475389349855232 30051147654990905 5211756414638982 27815532403309609 37381270422568203 127382624771 72101602621823496 5425597574224584 14183759121891584 72185184098713600
def a308 := f 46797747902354640 39584725207793828 36224510088760192 56966042309767816 22670368818991944 5915442554242128 66787485971323480 24349860010502161 14777544930754560 49584699719388081 29607591936 60491354496 52991135794 55930029760221708 24349872830283776 90116600216271488
def a309 := f 38850539231957392 36224617597656208 12499875316978184 0 100256264369478849 36226778272468161 27780435972135632 47358529102887060 6478351703389089 90642262359478828 56966043818101681 27044872192 14179576829968848 24354182555406860 2581997406964480 31560381763706000
def a310 := f 14320060466889808 106610870656 39483808810212048 14742281374501568 46797764281140160 14742276819563425 5713121809314210 72187443994427392 56938046511850129 37381370293697683 56405310776562698 47572432470577616 39409041072134728 39584791591682216 81219274676458376 14746758672986317
def a311 := f 36297155572400128 48422856224841985 104664863440 27817718686761514 55928142398231881 29607760396 48979212275266241 37381288740573584 30997505911731105 15309689298583970 81117674515464192 33504423584578341 48458059084827705 69222964176 31560486428488843 36294878833097122
def a312 := f 24354253934035664 23786845569878297 38848018933987968 46320278963831424 15305254832964176 12152422262940300 30752058668362521 82239650659598800 30118675336728618 12499355625980616 6511857615618176 46867890127295506 22107383724310696 15445967465611264 39408784084476732 48457995641946530
def a313 := f 30122564529627792 39584962498072746 4647114013409280 27881690735050752 49192325277137229 45827644645755536 1497966570424704 30443467080056909 63175750123017354 91208956801763712 54311547440409739 55910297296196488 5774728560771784 27844335659703168 71074750849 39409045891852312
def a314 := f 84447493995680640 11065788027023521 47341523322374832 91811990274255289 60308324352 5702173642752464 72185211488043008 90329108864 56966000767195520 36698474767012376 2857024272 14179331421157385 38850592907506082 66224409974669312 22107330544177194 56330562306349242
def a315 := f 63165293748345216 123790834440 55910273714459857 15305272159536088 36224637408650184 92828881545 27778061764132864 23927678658763272 14746743443292160 55897064492023074 66082847852705027 39584617623245200 38850508127089803 55910452500341137 22670373326307592 27773818421706930
def a316 := f 31560404014989312 63164830336549576 24349794449398280 31738680906647850 31738571744434696 0 63175749045059584 23841735074 110684012544 13625721688797312 6513680855674898 92426504882 5950903119199273 54311476365623296 36137928473360393 47341425397959376
def a317 := f 82239728140681216 22707663892886811 108716566969 46324623901512080 63165322135571024 55367007528550872 295466 55296711303797256 38850439768835008 171887993089 48983528909570048 54348949179499328 91246976570545040 54768873203040720 1444208523254280 14179301951944713
def a318 := f 36224537133745096 46289493711559176 120565479721 27773732949006984 28395438080 56490752909268024 78521620864 72855928872901286 57177718697492480 91249191633060176 15305308536646938 11103218796855296 39413524871131145 55927783373911307 31283588986247760 45269092739056208
def a319 := f 22670435406719001 28328415768 39584961429045426 23329466910739024 14852377103532448 56490736538964480 45900320131519899 39971925586487321 55875007960907954 49192160432731419 72783377182458274 56930533638721920 40778698601354248 56652151136554041 14179330070628500 190086381568
def a320 := f 45829871795981329 91249174532231748 31183552339151364 50212572784958032 47358596502167857 38850488730594579 2857107874 52986825104 14742425940820568 14742345732100146 5352724526816394 63164755002855474 39409041939834003 37381316890827336 23890263818804417 47371661967763473
def a321 := f 14883042384513728 10787629968831393 48422938853004298 82243522748568456 48669144983605298 54344617721612808 48669121466171554 72209904525523592 24915350585 70026169296 14742359489810888 56902861548260032 14777545306810393 5950831807543936 47393406657858248 46305958192920781
def a322 := f 23791278181370256 56473177608073249 57215119414991440 47059372546960144 28466877241 2584402081299497 27774110499406024 36297077856403874 207417 81146295955433993 14746649951939729 47059510229146312 56966146356730880 46271068079390720 5915372557434880 81179717173097731
def a323 := f 14746660157653952 31701239730407812 45679640363467050 72172585899051904 90116548757379592 99123809436565504 23446588815454856 45267048419410048 154703757312 23890259008391880 36226738371658146 91847182189200464 14742327223624400 91774657816529592 81262980263718921 47371722170618240
def a324 := f 36698554509730177 92425886296 48421001826456320 81792824698208256 53632 72147782110120777 46322579716348169 46867782645666824 31138243400114824 55927848787712712 45902585480174616 58276661607249179 36698475372066944 46867835691120785 90652883666240320 81709668077945173
def a325 := f 81194535664913216 14746710416949953 36888919597680938 72171943247512016 46322449797881866 46867824589144064 72783292822864136 58799820488366480 23223992315805696 31776023701131442 83919428475005841 92829155490 0 45832102038571720 14746670527459746 72209897504768157
def a326 := f 37418668401688754 30997437876450209 73760226944322248 24490582149808172 27782487065332424 55927768394861761 14742425944719360 27811380309295530 30434485685489706 48669104281880964 63165402360447696 56944051008191627 31138258930892800 47607537748087436 14179312966182937 23822127989260288
def a327 := f 48422921760289416 72209972166971792 54945129333051792 72172630661313441 57122974050095266 6511945163509810 40555836770192048 45269247600974344 56341812908071504 40745857905119632 120478236672 36226737499218568 56488666374250761 14179409665925776 81111582733669569 36224587805229610
def a328 := f 56351345313110416 91213910638271184 82237491540868137 81179720376437778 27815523609852032 36889046845397512 10787636432243792 39971989678660228 0 46289527985754888 46322454486059600 37418648809259426 14847910625694224 27780339309055033 23786941229054261 36224600484959128
def a329 := f 14179439701332688 46376666697095552 30997522139316224 36226846794359041 23786858396943176 15450408692533632 57179827324583936 15305227869749944 57000974256540368 7735579787 55894819821697152 82204481592284032 14742281298903040 175180405136 327842 40182751948701696
def a330 := f 137658368464 46993186094234384 7674003456 39726224049815680 121710458889 47642722655543474 77716258816 107509103376 54344532015185920 58624088830264072 29527947818 58797513276129280 81780070976588368 14742305934446770 14742281097717784 199632
def a331 := f 81643792838599819 14746679144258056 57179999208356301 49796100543011856 36818354085876224 36224650842311729 36224510088728840 1460426319829576 39584694198599680 95385956085923840 124998756514 92426383394 14284855068065792 37387838756574216 155849097378 234507
def a332 := f 115328 60308324352 59391400448 14320151587564547 23890188648316928 141337 81790594887926672 30118706264873560 31138239295429176 49192178757456256 72783271712592058 6511945972889745 28118668176 82204593954661515 49016609854994733 24349829878684624
def a333 := f 81217135849855512 56475368235991458 91213904465768729 72183319047119552 24459844253909410 31138229043534472 137658157952 31560470121060872 23329490692346680 4055660786408192 36224584190102224 38850446852565385 91207375964340224 49192150226877201 45369786368 63165402402429448
def a334 := f 49333757718738197 5774778553801416 31701126987530504 89418366976 55365083382979777 81634643312512057 91249080277369416 47607524672752136 14742304891999032 27780332221157632 46496500041287973 39460647687291576 40182841208345400 58799710084846592 91847260711240242 13100188676297168
def a335 := f 47358596569188872 49192203402785697 27782587193282960 27773733714353032 23786860544498504 27773663717756089 14742328208209961 31560440351556048 41343861143175330 47358469245934088 14883016439120648 23791560466388104 90118781183197648 3460531390876360 90716934638717313 27780381264783693
def a336 := f 10956087474589754 41341690191133312 72183113548202816 14742406613313561 63776245486485674 36888999047516544 90754266565705728 23786895937372160 108654150092 38850527795815056 54853354140766386 27780329951668481 58797542929912192 39413506369442176 77716788553 23784677698732504
def a337 := f 47358492696138768 40743556004055428 49190106069895684 56928588917686656 46306089063592097 14742297275061120 72218260465113744 3182643013237154 57001160513720498 73760208820633600 31138212537751936 14179326954188809 47358439709611193 23228389326340632 69231479338 14746770429068040
def a338 := f 27773753993410844 14179354938495376 30752058198628872 48979146893983904 14742409053208576 23786862875380793 39584726772201600 82239710860296968 45579708809 73503245752598690 5774789935454728 5915400684579717 172337 56965972313153793 5774663254802432 30716790276414352
def a339 := f 56966060998110475 45902569374005802 39584710049439041 49016610991748227 90116581438837120 54766703787257865 77447936128 56928695595860432 13616379244632448 45827679360065664 40182861010618752 46867891299792147 37331729580851362 31138257616157843 92829001752 55894773109674368
def a340 := f 91246958379909248 11065850229070344 47358547427731481 58080756688 15305229977426440 14777591119656993 36262004235381899 36889027806405643 28118790305 49333740400366472 74312248369287624 13616410526390792 27780313896331280 71433715712 63895730687027992 58276659270337281
def a341 := f 91317216519228080 2007186595287496 72185161228363801 66545543081624008 207241 123920890632 46287369646838216 6513506883177475 40743595305208889 154702921872 63765654141927424 27246532914 91249130898831488 94029625557 56475489233183104 36138061277429760
def a342 := f 63966015346180096 154909448457 31736356669489152 55892582948929536 30087414647331408 27773791096031752 82204447304491163 29876204828066384 36332352623973433 39096882371288216 90719125170598306 14742280023966664 124998818312 12499336541963344 11283011898 55313160659403856
def a343 := f 46868084778095632 15305229985847896 36698469597251882 56475373709875712 5915481211540432 82239117081028675 15305272218782084 91213892316511273 47607600732230416 2343391149965848 91847199440376656 46867871003050440 56475440247878280 27844319763288448 58743987078630488 56488584563674122
def a344 := f 55786333859262882 36222437108720400 27773709083345592 5915476211597474 65337454673611272 45745577790624392 56475360619135696 45902414289156224 24354193905635848 39061629425750074 82239727205351424 40602874044744144 66082987812493832 49790439418629177 82204496486472520 46306009580450440
def a345 := f 20618920640168354 27879566886881680 5352819487640136 66082925564863112 14777525671273296 21117523387271424 39584725341485201 91213864980779208 22531221477278472 14746804789808185 65480315480715273 46867920395078736 155840413696 28118782476 0 0
def a346 := p 4 a118 a119 a120 a121 a122 a123 a124 a125 a126 a127 a128 a129 a130 a131 a132 a133
def a347 := p 4 a134 a135 a136 a137 a138 a139 a140 a141 a142 a143 a144 a145 a146 a147 a148 a149
def a348 := p 4 a150 a151 a152 a153 a154 a155 a156 a157 a158 a159 a160 a161 a162 a163 a164 a165
def a349 := p 4 a166 a167 a168 a169 a170 a171 a172 a173 a174 a175 a176 a177 a178 a179 a180 a181
def a350 := p 4 a182 a183 a184 a185 a186 a187 a188 a189 a190 a191 a192 a193 a194 a195 a196 a197
def a351 := p 4 a198 a199 a200 a201 a202 a203 a204 a205 a206 a207 a208 a209 a210 a211 a212 a213
def a352 := p 4 a214 a215 a216 a217 a218 a219 a220 a221 a222 a223 a224 a225 a226 a227 a228 a229
def a353 := p 4 a230 a231 a232 a233 a234 a235 a236 a237 a238 a239 a240 a241 a242 a243 a244 a245
def a354 := p 4 a246 a247 a248 a249 a250 a251 a252 a253 a254 a255 a256 a257 a258 a259 a260 a261
def a355 := p 4 a262 a263 a264 a265 a266 a267 a268 a269 a270 a271 a272 a273 a274 a275 a276 a277
def a356 := p 4 a278 a279 a280 a281 a282 a283 a284 a285 a286 a287 a288 a289 a290 a291 a292 a293
def a357 := p 4 a294 a295 a296 a297 a298 a299 a300 a301 a302 a303 a304 a305 a306 a307 a308 a309
def a358 := p 4 a310 a311 a312 a313 a314 a315 a316 a317 a318 a319 a320 a321 a322 a323 a324 a325
def a359 := p 4 a326 a327 a328 a329 a330 a331 a332 a333 a334 a335 a336 a337 a338 a339 a340 a341
def a360 := p 4 a342 a343 a344 a345 a342 a342 a342 a342 a342 a342 a342 a342 a342 a342 a342 a342
def a361 := p 8 a346 a347 a348 a349 a350 a351 a352 a353 a354 a355 a356 a357 a358 a359 a360 a346
def slots1 (i : Nat) := (a361 (i/3) >>> (19*(i % 3))) &&& 524287
def a362 := f 3396396790064128 65302195675859971 14652094099229712 1125899908945920 3389797574902809 6764199831153669 29282229134819342 15782397426532358 21393208484317222 1149008986773504 15401798039552 153947740520449 2328873103523866 1180890535298059 36210216438599688 1127005860922371
def a363 := f 22517999219001347 2257379003466764 4505804037174310 32652196811118592 14722503646675968 5664684980051982 57430806980734000 2255106985779211 2324367581220900 1176523613667328 20896133679107 13511957466330120 14638898894343168 20266203691876377 40543407887670273 12406892465750133
def a364 := f 10288133572660224 17592195486720 36349384117263 6771900707505165 29273407247880213 11285399163902977 32986467686414 88946107678226438 1212255575049 92341397435219066 52994432181470299 7918682911083520 2371695109226501 2318879698192500 1077942272 3377744817700914
def a365 := f 1125902106756151 16888498667651099 18016607238389766 34934787246410816 42790807565066241 22523523613339700 23731877240114188 15762709292256303 1157807218888704 21392102535534606 10143007736082432 30412556048858112 3517404381454420 33801327122330625 32678636628741140 46161909070693464
def a366 := f 3390963696282656 30095179805 9076484601828363 84498572631867401 63057060588461089 49605750208610345 14296872477701 48463174020635680 64921656174642 85570596283368448 30454299939045473 97859812730880 65314300104825908 93450821864262661 1127017678626877 18036388797615104
def a367 := f 20300283253885952 34948038295326780 103587190559217669 6772991652289557 97955322266727 9007199256839170 95714696958592069 148681482466023453 38299303565854720 17008346443838464 8797181479936 15798885812311041 22518433045316608 3396400014427144 32657801754969091 60799698776096782
def a368 := f 41662718229348558 256711787687251968 64872298633249 13215614373925 2252069356437520 46248793165791245 10136646821367852 6770805528606720 5658094390533133 146489033727455302 2264115778159616 7890147447163996 26144239040631808 2259572661165060 11810953949625346 153138885375832071
def a369 := f 41667269829330982 410138243501064 140738565251074 121598295906762863 3383201606139954 5632808807565348 42908682876355676 57986252800 19142520026989568 51188868713679901 64185227188118611 2284924749189157 88963710598512696 63050398004412519 3378803527130140 19199673198734341
def a370 := f 1194153379652709 22600466882889133 30431217681718272 11322812639740962 448109284983577600 168886148888881213 234187190308994048 27039313430620173 161010283764016131 90286399564045368 70971288360857605 16888510472551430 5647110212004966 68679897642530826 461621160901101570 66489686595556352
def a371 := f 231951085357653066 57421042351606786 5671286344792091 127254199821938688 4503683391855636 22523495772644353 81143990353847300 25319996220709 51791396825400321 3483265808772103 4547646665634823 1135797661116419 54069720205233214 6768649415172096 78825244893118867 80195144020818949
def a372 := f 94594628967851 13513063405940770 12399631807837236 11370078743305222 36029038651781139 265830025859786754 16940196094310400 16924832028486961 36301478054476800 2253058330380351 16888617809159169 114922057002666110 693557675756135463 533719855557259264 5672385979182153 31888022493184
def a373 := f 3307131189302 4398063288321 1247952169337201 15995878770801814 149744722091442260 85569554791544834 33803400526298159 12097854386327 96835092923551746 171276600988402691 117110084069346482 72634838720900122 235313157892999185 141869988632868023 16897365582559258 2290478264353808
def a374 := f 19792284151833 37166795894866945 60801995535026197 23675783957551373 9150135843974152 25913292208792598 22524684656443394 1400877719104512 34905096144882256 2368481559321601 7833018004497 24786542961799615 104456057291777 0 0 0
def a375 := p 4 a362 a363 a364 a365 a366 a367 a368 a369 a370 a371 a372 a373 a374 a362 a362 a362
def dis2 (i : Nat) := (a375 (i/6) >>> (10*(i % 6))) &&& 1023
def a376 := f 671372796969898258 7459423539723125504 479668546097917953 5145380653484290049 675631204252599049 5879273526226595841 4999312294385627137 752437589741470279 1410871297 6819172558469163 1952979401 83396857456769536 5143165921876580098 167872335818733824 8375105112569499648 5080396899640805506
def a377 := f 92611873036592896 7284924245409488896 83679432117670656 167872337228214273 5857265640851210753 5066954597382313734 92612972665389568 6289313301101883904 6819171271782912 167872335974585088 600210203464972800 8458123807781642755 7283334626680141328 5046585000863159808 748234156626089743 167872337010135809
def a378 := f 92893347993635072 59123980 5927150544582422529 600210204923095046 1176007425 676176561360610048 101902746916307209 675912678942978569 91010975520854794 6059927554456813568 1521920 622413828290208006 20396091020687616 6059927554458401280 7158832617983979535 21562882
def a379 := f 5999078459283035648 6536596650674432 747970272585318400 4972650372953291264 694471421251053312 21562882 5129689058389267457 23726082 6536596649436928 169473233337188352 599315200998375424 752737755040668160 1774496426958882593 4979118628388505360 167872336146859784 6059646081177370625
def a380 := f 595425128881612544 7296415541958818304 92611872999094528 6818071625467394 1450324235 694472032291672325 3850614035130112283 7296415284398801664 167872335839823618 676176561459908608 3821728701087834629 4979118629152909060 455207710427007352 10459054937187959552 6059927556424624412 160464927679006983
def a381 := f 6197930583201945090 6059927554630955520 167872335990235392 139747584 91010975479052544 39393282 9876437023640854564 671372796481925891 653077153554315532 144917012 6060209029526061647 523352143069523969 1672128577623031808 7228861324229563904 167872337750806802 523349944046202881
def a382 := f 1371722198231298049 47590207153117206 222193751626973697 6059646079550752000 167872335874193408 600211303402184750 244733697567830017 173977932498798338 92612972510656768 4979118628198756864 95814741779283968 672267797639942144 91010977143783955 3564041859253076588 6819172279459851 326293321378062336
def a383 := f 95814741798701568 91029669630010386 1405257284683313673 39393026 4721848314718352389 6059646080705913605 753037921835102720 523349944096154454 10459054937050008064 92612972520219658 6296737462404454159 672268898376626193 665142075 11688837802134360832 37295360 5924003912830111744
def a384 := f 25090855433408596 92611873171718912 6059927554631025408 7427431029156091137 676176562514133761 6059646079869425685 1096364047 6204115318948045097 9229056612420246241 289751194025871872 617910227567863808 7000083513539298165 5059530437158252591 169191759770167592 3564124141810352128 5999078928824217601
def a385 := f 747670105950328578 92330398096767500 5080396898990581504 1363685393 7284924409592754191 83679431967246338 671372795036303360 6208901493083674941 1560559978254061617 621836338757843200 7429393486108504065 8523161281049682176 1371703505161840384 657899379568953600 523349942635331584 91029667313836032
def a386 := f 91010975517734912 91010975512615168 599928728503920896 671372795036303360 7228861324209961216 676176561338056704 7293378416003610624 6060209030597517323 3555071918435755776 7118238422090260 92612972666442240 6818071644043264 675612511912466178 4784854785812862521 1600067685050220544 6818073049831828
def a387 := f 671372795866140678 258818256030750226 694471421387227904 1174492934 167872336913641487 22611714 6059646080311058438 671372796382877981 4697367678226544896 5856984165142119168 83397958665995016 1631619332 7228861325619310593 671108912245637120 4978782366500869632 6066632678374387729
def a388 := f 7289428944448939776 752737755125207040 6535497115500544 169191758535681024 677070466275891719 167872336661408029 6060209029472983042 7080090740942057809 172676102925612577 675876394668548362 6060209029433524224 97398047270650624 169191758482329600 91010975477530624 39085824 97399146763472896
def a389 := f 599615368078862708 83396857594720768 3564124141810352128 6819171271721472 671372795651163912 7100646092177408 6059646081381859422 91010975583515648 1703541574405153030 169191758360477696 677071563842152192 4999577113464996371 91029667555062377 6059646079480102912 5283007278152698368 167872335903299330
def a390 := f 11611976444092179474 6059927554495899392 407330575341470464 7228861325302064900 83679433622892545 19417600 6818071623256576 97398047252963584 681658137 9958135134702667264 743166506306176770 6060209030340116993 7284924246698635265 672267798914167304 92930722779627520 167872335856670466
def a391 := f 167872335856297728 29858339208393219 5856984164969560576 11539937579133719330 246035528212943632 7289427844915003392 752491466383186439 743430389131454210 6818073000608275 747970272758411776 167872335817211904 667184755246104576 91010975485100579 6422524516400968192 1775599167348540930 671372795057493504
def a392 := f 83679431982606336 5265382420290469888 289257328758513920 95814741779283968 5927150544349499424 6059646079653134848 7289709319891714048 92611873004393472 1466256721199515417 83379266365501455 167872336991704838 95533266802573312 5051212498570586382 258695878943573506 675876394785525760 57288706
def a393 := f 595365175568187904 91010975617278208 3563860452294736128 8523161282003625732 671108912574236424 6059646079501293056 743166506407309824 523349944046202881 91010976602675483 752473873431277860 6060209029457073152 97147349893645826 600211305393362710 3563860452333721602 748234157811173133 1816647454127370752
def a394 := f 752737755004942592 6197931090008893184 6202716840550107396 331078395853612042 244733696158480896 6819171155792896 1414841736065582856 523349943809824518 1847693092650631936 675612513526894872 7438402882998241026 6059646243819387421 4999312292996318722 21190144 6060209030558078601 6066368523663527981
def a395 := f 1591808 91010976888467457 92611875415856918 5131869507448866573 7212849059063660544 671372795193668096 752208889932023298 5856984166364684314 523351042168149504 6059927554613068288 173199469655308544 6536596703099148 7151736390355064578 167872337228214273 1632186385 3855772235122934561
def a396 := f 743166506439819776 96338110759727875 0 523349942757183744 600210203463385088 7284924421503143936 675631205191074309 330196799464694789 6197648163295738368 303734589690951948 4793907006877488138 7284926500147050752 326292222874034187 600210203484948226 157643264 1699038271394379780
def a397 := f 92611874408443905 6289313300945567744 7284926501275990557 95533266941138432 6818071761146368 3850614034715317028 6537697820235804 160183451179504640 2636319955021793026 5927150543786416136 6819172559649050 1410936833 676176561349137162 378980969292113408 2981669449114339840 92611873153823232
def a398 := f 6059927554479425282 20394993172677139 5264816837524802048 6060209029472917250 1096429583 92893348147249664 672268897034130944 662698748997702401 5059530436000627200 747951581216011792 169191758399563520 672797763282047745 10458839475740239616 747670107085427286 326292221716927488 7936000
def a399 := f 4617745556982229275 182684958232478653 6059927555553177615 92893349418791427 747687698103931904 6819171255214336 6059927717704656640 5856984165859791004 167872335893182732 6061952185031352576 523349942657640192 6059927554880832036 1699037975072485377 8446582495367476657 600210205161507079 748234155432966144
def a400 := f 743166507726698778 91010976652023558 5044408741070521088 6536596784501504 671108912285030146 167872335839520512 600211303098823936 672286489355301376 5055417030980688155 6289313301118599680 675912678586476288 748234155399533568 180218120920904201 5192834538578511618 95533266924425216 6059646079505608749
def a401 := f 164669458447087872 10459054937204736768 6361795469703870505 5936149231211917313 747970272586840576 3966142954884851456 5857265639966930944 160463827365798160 596508535756489235 7438402883131818496 6059927555620806667 10889780396784115968 671108912252523520 5051212498801799169 675912678705033472 167872335894231564
def a402 := f 6059927554494108928 167872335973466624 91012074990746112 4709129202248458512 21628418 4793907008167817217 7285205721675214849 6276471980111910400 5850307876495197052 600210203464976896 747687700783896854 83396859152384001 5152770157316812801 1703541788210442752 167872335842968576 246053118700158976
def a403 := f 600210203463385088 3564124141984502528 156524544 5051493973542131462 6059927554614120960 4708903052535732246 7007751670464006656 2349299464044291112 29576862842365440 600211302982947840 11603403658260787201 6208620018105006348 5927150543173073408 2636319954999181312 156524800 91029668072788993
def a404 := f 4697386369924151296 244733697336615095 6818071681896448 1371704604634382336 3555071918569763328 752437588328972288 6059927554863094362 83396857492542720 101650949656826368 91010975479122432 747970272606946818 600211304656558364 5051493972369225984 246035527925116929 92893348924641801 3465649786244567608
def a405 := f 167873435367925504 671108912266827264 169473233358378496 747933989877748481 523349944333453831 6208901493007268096 92611874678986780 2640102310820877313 7293378417459734558 8523161281585588501 6059927554478441986 6819171136656896 671108912401891840 32795365251496448 292898912287676166 6369340288407189760
def a406 := f 675912678703706624 3821429632562374912 6204115318911600130 1697202177 244733696158415104 11612259016183473449 5233799748872327941 91010976579068703 54920448 6059927555620806747 73826708403335680 244733696771594256 7293379516639027211 153179136 92611873036900098 169191759805969155
def a407 := f 6836764712448001 1699037973681031680 1410319444411940864 92611872997507072 5264799245510136320 91010976888467457 92612972683285248 599051318230017792 95814741953495808 91010976846135320 10459054937186841088 747687698098567680 3931665569915351568 169473233337188352 157304832 752208891405755397
def a408 := f 97398047113216000 1477314878346843904 6059927554456813568 91010975874167305 743166506304755200 7100646103257866 167872335839454976 97398047287296512 3490722811588146186 889745921 5059515042974879744 6059646242711471874 91010975499093506 1681479708 70328446 92893348028764707
def a409 := f 6819171288498688 5217139922016823566 1076450841 6059646244418325018 92893347995407872 70342959 91010976374071568 169191758360477696 3855103276782478085 671372797739993101 1825263327567628807 7100648510657858 7284924246984835073 5927150543171485696 3568909216536285184 5927150544330711555
def a410 := f 4999312294704480771 4697367678244375040 6059646080930427147 6059927554596561152 6059927554456813568 5857265640117649920 7208312529961117440 677072664478687243 6059927554632073984 599051319889188892 3484222679216563510 97116572138027264 1163993099 4697386371086622731 6060209030844395521 7151999964008440064
def a411 := f 156524544 5857265642361860631 4769706747244405002 7080090739615753984 671372796447305729 6536596784493056 10381978117092311811 8514762373578358784 743430390690359581 91010976988554358 6941218130217150720 675631205224566808 169191758366254080 3893786295056019457 7103390576281139712 8523161281085071872
def a412 := f 32709414371333120 1414840636369224212 6059646080309940230 747687698119657218 73826708304001024 6204396793877828362 83679431999383296 6059646080891039745 1556075086795198464 97398047795135241 523356541115969537 747933989826750747 6204115318890037248 4697367678269395722 121851904 47308731739439684
def a413 := f 91010975633846784 11534636025881456795 6064431154084184064 1521920 29858338593722374 169474332870379266 671372795057493504 3822010174756958720 5999078459283035648 29576862944539136 3893786293645082624 11603104591132586755 748234155415070464 97116572294148352 1698122247 6059927554478003712
def a414 := f 595407536793867274 4040379965613539328 3568926808600477696 6818071605360896 0 676176562167894022 22677250 9237256748499338270 1631484194138960384 6536598072619779 5122169691922591845 1703541573310174720 6536597723492367 167872335968540707 83679432116613632 97116572457986082
def a415 := f 91010975501079552 747970272604736000 169174167872555271 3564124143508474119 4697386371016321028 6059646080891039745 675631205339988287 747687699260973067 5927150543193048834 91010976888401921 6536598038065153 91010977156902913 4708005733303226881 100618509492039681 5937742246058674688 6059646080375669282
def a416 := f 6228795369817769736 5051212497413539586 829958419 6059646079501665794 19417600 321507147145045760 6536598038065153 6818071642924800 336156212 8539768337304324185 6059927554613129728 169473233494491648 97116574122021896 2610514528803514112 6818071605360896 6059927554458466816
def a417 := f 6818071603838976 92611873137254400 9944327411997884928 671372795209335296 97116574117941774 676176561727379477 7422645953810678272 523349944334099208 11340363051851776 5075873488050860033 595407536830566912 3821429632444399616 7100646248432128 7212849059459248649 92612973920071681 91010976571221764
def a418 := f 1774496425972342819 1521920 1699185416 618210394221051904 4979063841595929088 2829783763257936384 3464542576295085826 6269688006671888960 675912678703645184 6800479439422978 169474332889323522 675876394731148802 7289428944752183560 6059927554478003712 6819172526469121 29858339127068932
def a419 := f 5131869505053882368 1672146171504181518 29295389260787979 4793905907369133312 91010975479118080 236744645853381487 685464973697247622 156254720 6494582111726762266 3564124142760435748 6422524517755675653 6060209029472610048 7429393486192927749 5856984521450192896 330469214983832064 326292221866295808
def a420 := f 2601486370108368640 11688837801977053184 169473234430883844 1672128579033968641 5878112412169224449 671108914949261069 7433898183838218752 6836763474604544 6537696158173696 595408636206515714 11611976443048243201 455207709525476866 677071563960431104 3564124141985682432 97116572293939968 246035526533532160
def a421 := f 527001420752763392 4979400103057118720 182980725133874946 730010893782694008 11751626002044834826 92330398022384128 6818072779916033 376087003094530304 6060209029571041024 671372796194089003 6059927554458401280 671372796212380417 169191758534619648 748234155413280000 752491464398733312 1614451215
def a422 := f 671372795131074877 122700544 95814743190220801 6059927554630963968 6059927554613129728 6280976679387021824 1632318731925922826 585841828462868736 156254720 752737755042440960 675876394821047040 7289709321302585345 11340363050733568 169191759072867669 22677250 603536226138995200
def a423 := f 7297945792121164877 92611873119358976 747970272623285760 676176562748993537 11621839316529153 6819171271782912 7221900354920722944 1125148955 2454807570 6819171117054208 10458772363953188865 38600894089402624 6060209029589840384 8381782828854547970 83397957088661504 6059927554596352512
def a424 := f 91010976159188761 595407538370461697 6059927554478003712 6800480828665895 5854811476878366733 6536596628781568 6060209031130726657 6204115318927398144 6271287001083300352 91010975634895360 748234155415070464 3850614035415838721 169191758534619648 7289428944426631168 528154808602489908 0
def a425 := f 92611874408509441 523349942635331584 167872337213988967 3821728699781239296 364957604818993664 1410936833 10449532333499652117 7289428944447821312 92612972548527874 2927699405893345326 5269323573886529537 21563138 6819171115466752 1632667908 167872335818799360 1699037973685340162
def a426 := f 29576865493693970 1672146169982108160 675876396043700484 748234156820558339 6059927554458335488 605013969786328576 167872337267536139 1817893167653142552 92893349167072001 88548864 6819171118106880 1697202177 11540499619070298375 92930722935943680 6536598396436799 169473233338776064
def a427 := f 523349944015353860 1416423963055314432 6280995362376541952 91010975499159298 5051511565964619777 1410936833 3824832831542080000 91010975866915408 676176561339709952 599315202986813761 167872335893182732 8723551801967640576 95815842654091524 169473234748125185 3855103275576084992 2630517857909211136
def a428 := f 7212849059103119106 83679431962937856 4999312294385692673 169456742073774081 83397958161703494 96344706423330562 7153784578771071488 7571765074987345664 6059927555866633018 748234155537678868 6818071660820480 5051511566233137732 91010975635952384 4769725440699161285 748234155497836544 34363037075976704
def a429 := f 1905643668900480514 675912678866769426 6059927554629906944 752491464400320768 599051318259442698 523349945339021325 677071563804658176 7433898183994000128 5866574755289182225 6836763742119735 7107895275457376547 4062815375850743050 2636319956443689475 6274191605965599744 19417344 747687698130892323
def a430 := f 4709129201373545986 97398047180559874 11539937579362693121 169191760057679873 672268898463265035 7289427846325940225 139538944 95814741818369792 7095512769415719284 6422524516265842176 671108912401891840 6819171237318656 169191760795665771 600211304419586563 6422524517470458782 21562882
def a431 := f 4694306762428843522 91029667215710210 3464542576294712832 5292598242180305217 6060209029433524224 0 6197931684372496385 747933988796436480 91010976888401921 1415780161 97399146626365696 4203936718291730432 11534899619969907200 7212849059120642048 8510205768151472406 6536596627128320
def a432 := f 0 167872337228148737 523352141816021760 1444573699 1486899329797220096 474059695376782848 371062093343962368 10526724826914568460 97116573043098113 1410936833 675876394663673856 4832460944054706176 8403828539638506240 1699022091701397523 5084604665526484992 11340363086254848
def a433 := f 671372795036303360 7221900354747629568 0 167872335854573056 4999329885160734720 167873435351270144 7293379516087499278 671108913174024236 653643213010331392 95814742954152801 523349945321009687 6066788923651785728 6198212141398642968 671108913422506546 6517292772677400400 0
def a434 := f 39085824 6059646080843788305 6060209031131646215 8309221894676630016 3564124141967716864 167872337312572447 169191758975174416 7438399631840595968 293481653104748563 167872335817211904 3555152775467761664 91010977912653325 1559979664263378948 23667712 7221900354766981120 5123569158591610880
def a435 := f 743166506423312640 747688797781701120 167872337330402847 2707054909564926464 67343874 2703573783 2636319955174441728 0 4832460975631772189 671108912285030146 3564124143221354497 172676103295042305 182980726276379426 6819172006111047 173977932515272448 681658137
def a436 := f 6208901493163110912 6361795469682166016 10459054938727727105 3922987290978699520 752774040298074113 6059646242690451968 6819172206459176 3559858092685684736 95814741786170368 167872335973528064 5850307876040500364 10543318232315105793 1699037973783465984 676176561512198656 11321672327639055 6818071960891465
def a437 := f 95814742653106499 7284924246698569729 92893348804055046 164671657488173568 7293378416235346148 6422524516332146772 6059927554476300800 114371244166038030 11611132175949563400 685164450592928256 5850307874702569984 83679432874737704 455207709660168704 244733696195979008 6801580608794625 7423210660253206018
def a438 := f 4139377669176443648 83397958462104607 4041505874724132616 8539768334774714880 6059927554495899648 6359189349394379267 4709129202715602961 6800480863286019 5051212497392449792 92893347975805440 671108913656573953 6536596666214144 3893786293682443776 595480462619131905 83397958144827445 167872337228083201
def a439 := f 303453114794586624 7284926501841617422 173199471351054593 600210203464907264 7284924409876412420 7213130534059788544 97116572231411976 11611976441658934786 5059530436038125312 83397956968397056 6819171154859778 5051511565669851398 6536596782538752 1096364047 11674760171104900872 747933989080412777
def a440 := f 92612972665451008 335281812762861579 6060209029473662976 6059927554458401280 6059646079501293056 6059927555550504708 1672147269342201346 671108912247159296 303453114813600768 7107895275575078912 747970272606815746 1681359368 6059646080939812870 7084594339482454540 246053118721721858 1194348805
def a441 := f 671372795432940041 1483376238184658948 677070466726627085 3894067769814717185 92611872999164416 4999312293388173833 11539938677603131392 164386885653316110 7156933408119601408 6059646242688860160 3464523897460752384 5051212498852217857 236762236877145602 303453115754438918 92330399384547345 97116572310717184
def a442 := f 6060209029573271552 6819171115466752 42856997853808903 167872335973466624 622714244402148099 8383567446285698834 91010976571221764 3464542576273522688 167872335928889344 169191758363183616 671372795037895168 6537696159946240 1703541788175913216 5123569160323433475 95814742461203209 4697367678226614784
def a443 := f 167872336212800009 101902746391961856 665142075 1699038025241547776 5927150543192675840 6536599330818061 91010975600231168 91012075127787520 7289427846295021316 5152770155905810432 0 156316160 5856984167654824214 4623321157846695936 6055425110215849984 671108914949261069
def a444 := f 21190144 752491466129572611 97116572136505344 752491466097918728 8728352272171422482 6819171187843454 0 9485151466111133440 752492564083393024 91010975528424020 3562458686658512386 7289710419404929280 83396858866118657 599051318209362432 671372796447240193 6819171117054464
def a445 := f 6059927554461688074 6060209029472983042 167872335941092608 110627362430204160 11340362928881664 1699037976080029718 5927169236280094721 6060209029589778944 169191759770366222 21562882 83679431980881408 4697367679388950539 6537696163538176 6059927555071678216 97116572157695488 91029668658180415
def a446 := f 3894085363243026189 70718720 167872338272019474 747933989860893187 160182351649911296 747970275020506893 671372796498450994 6440715261837903362 8332896503145771009 10458839477112090625 599315201035671552 617910834362864415 671108912267945728 6204115319218570760 4972933973994207232 169174166296285184
def a447 := f 5044409651468764930 167872337549099278 6059927554629906944 743430389075753472 92330398022384128 743430390454257924 91048359554467609 11688820210101998550 95814742391749134 6536596666455554 11340363258299920 6055425112630453266 4618871457233126160 671372795112198144 6059646079636357632 3564124141817304064
def a448 := f 5139557424903256346 6059927554494174464 19417600 6059646079519495938 6202715740053718809 6536598037999617 653077153478344704 4979118628080846338 0 5927169235025686784 677070464413290496 743166507197931890 671108913941790721 671372795036303360 6276491762711673344 5922646944955117569
def a449 := f 83397958142886657 667465130730605056 97116573314519072 743430389963977217 7293379516920656643 6536596648318464 747970272741573120 11679948357862975232 1521920 6059927554613068288 600211302994430208 7289427845829496839 1163993099 6536596795978762 889815553 6059646080924676611
def a450 := f 4784937607665627648 5911136367672918529 3893786293645082624 675612511894198016 6819171138828288 0 3866102819945709568 1410936833 6059927554613129728 5045459712519312227 1683100435 5878112410472022016 1405257285732233731 3469292356280939011 218027666819776512 91010975477530624
def a451 := f 7109056389762252800 7280421801904054544 671108912245637120 10387016073502348032 6819173302421883 1587712 83397957124174336 83679431964710400 0 91029667789018888 6819171154552576 5044409840561119273 7293378416002492160 2630517858083422976 675912678569633536 402808285808974108
def a452 := f 6537696177841920 747933988858126592 753037923088674817 83097790414278656 11340363068628992 3850600165557156096 6819171931873560 95814741779283968 6059927554458401280 6819171720058386 39085824 7291689566103142400 5051212498466858756 1587456 671372795055720960 6059927554478003712
def a453 := f 7212849061488272281 4697386371333566465 403135990808707388 3922989490051821613 150933259719083778 671108912283604480 326292221885231616 169191758360477696 1744204863358631936 5927150543174191616 6060209029454714368 1411040689836278272 92612974004495365 671372795193668096 7213130534077666560 747970273681682447
def a454 := f 91010977159010332 6059927556154081281 380314474977951744 167872335817211904 91010975849092099 6059927554456813568 6836763913910798 676176562782630403 6059927554478441986 5927150543192675840 5941207936810641152 6229640674641471232 167872335874500610 747970272593319168 1775599167348102656 139747584
def a455 := f 8305025028748609282 167872336767295524 4694306762564583936 6059927556188701699 5856984165038626304 5044409840597746176 164386884058360320 671108913656573953 1410871335 91010976391106577 671108912266827264 160463827930081286 6489797035852640768 6059646079519495938 3564124141949891072 167872335939063808
def a456 := f 588110302514086657 9313535366199314178 11539938677534102784 169191758516732416 7284924246480234881 3569673249557655553 675630104197685248 4708847726548300288 92611873323043153 3898289894195892737 523349942775078912 3059459146812510232 9597278237389058819 6208620018186408704 3541085091282366976 167891028479706383
def a457 := f 244733696196286210 83396857476371968 7293378417644886044 91010977175652615 91010976824105245 167872337261720067 676421133994104578 8724996504487934476 5992400064310629888 1846537527254193152 2901905111945073152 7284906653103241728 6059646079842404876 6059646079885923971 5911611828237515264 7284924246236667940
def a458 := f 293481652449989120 74354473985716736 6060209029822847180 6836764459668322 169473234430879492 5055661628264240640 671987423129925636 173977934130073624 6819171155671040 4769725438938790144 600211302996575746 3564124142616999457 752737755022772736 11539654574139785728 11688837802017556482 6059646080924611075
def a459 := f 169473233358816770 6059646255747973888 523349942656521728 518006359075535104 167872335856670466 7031051507266500864 7289709320721489971 667465130732377600 10381978115483324416 1703541574452977675 4697367680257185317 21194496 39085824 6819171797124889 6819171154552576 694471421369332224
def a460 := f 1371704604655945218 8315221887484725022 523349944112988312 6535497117022720 6422524517151244801 169191758398817792 6059927554479122176 600211303014098688 622364096076252680 6819171237318656 6059706857581726208 752191297881723648 677070465187979536 6280995363748458497 677071563822549504 6060209030883778571
def a461 := f 7280422900639944704 675876394669450240 173977933306023942 6060209029472917250 6059927555286650886 19417344 6818072499405346 5856984165107654912 11603386064663740416 7433898183838152960 5084604665526484992 6059646079558094848 173977933887123457 7100646186953021 3855103452816499647 10472179988526560801
def a462 := f 11603386064752289280 4697367679921106945 6818071605492224 83679432117732096 523349942635331584 6060209029608784640 752737755024918018 671108913409630219 91010975516616448 167872336492865813 10458839477112090625 167872337514479617 83679431945112064 95814742685876737 83679431965148930 92930722785408000
def a463 := f 6059927555286650886 2641487656765698090 7157515307624509952 6289699152256591616 6204115319495677458 6059927554478003712 316694709422670592 7284926500202444800 4769725439551084296 743166506302982656 7289428944448939776 29576863177615381 11679948357962518528 6059927554456813568 4697367679388950539 3969114031223222807
def a464 := f 97116572158813952 4697367679635894273 6059927554478310914 748234156786921473 6059927554496206594 6819171138085888 97116572147520266 680680161139577600 7084594340514246657 6059927554456813568 75971084 4708847726375206912 6229095157921218560 6060209030048388872 1453089424530210816 11603386064663740416
def a465 := f 169191758482329600 6059927731961409537 97398049531565846 4190344731649643520 7156933409613374469 4697367678227527936 91010977793992997 217339703254792704 6536598122488837 672268898423877633 676176561432897800 6417739441780318208 6818072415011345 236180595204423680 3821728699646613250 2630517858067636992
def a466 := f 6197930664907792640 92894449266610525 5937788597345733120 7118240999741453 7109056389835683113 7289427846325940225 752774038887071744 303735689133495296 1699037975358882049 5922646943701479936 97116572258357248 7156933409015603472 29576862931042836 1405257285983879694 7458577856331993088 97116572292760064
def a467 := f 465037343477794306 6060209029472610048 6059927556110700824 8519267313380512590 160185651203437313 5999078459433973891 752437589774529283 10470979163519528961 752491465809670145 95814741919031552 6060209030879081219 95814741780806144 6059927554613129728 0 10687326955551341056 5283007279830544385
def a468 := f 752191297745540608 22619136 95814741819488256 29595556214112344 167872336422917650 5928585826825041408 599315202208837934 523349942656521728 671372796447240193 5044408742609240590 29858337763885056 1697267969 167872335955841024 7423209848482824192 594586244436983808 743166507663587332
def a469 := f 6836764999633159 22677250 680133703860572928 10387016073346562304 1410936833 22308608 523349942656960002 5051212497412556290 97399146798994176 145689697373747200 83396859151401486 752437588368058112 675912678686929408 402535868463670277 34081561948481280 1326650633922543616
def a470 := f 6059927554456813568 0 92893348013303552 21190144 40507394 7293460885010479108 91010975477530624 1587712 600210203485693696 523349942674786306 0 5264816839219363841 6059927555581958427 11340364025311247 7284924245287632896 753037922907783969
def a471 := f 1398166821584635394 5856984164989470210 83397957024098306 6818073014775809 5856984164989097472 91010976092227344 92612973920071681 748234155695359250 8523161281084146432 6229095159552297348 1533528763265590784 83679433388028419 747970272604736000 675912679722484481 913391656 7100646267437824
def a472 := f 3846428271174680849 97398047252693504 6055143635198935040 92893348130742272 19417600 600210203464907008 8387279480855748608 2601204895487899161 0 675876396074610689 2636319956698010495 523349942656521728 600210205159470138 4686375989425938432 523349943042550037 4978837154779709735
def a473 := f 173960341701013505 34380629094704128 91029667297054720 4708847727738957841 97116574574749751 6055143635338473984 6819171154552576 169191758399870722 5123569160290440007 6060209029456201474 6060209029435111936 44372746 22430464 167872335973736704 83396858866053121 155410432
def a474 := f 167872335986066698 672268897014462720 92611873153823232 21628418 6059927556136185857 6819172526469121 83679432083267584 743166507694501889 156316160 169473234227003905 599315200998375424 42523655293657088 7228861324208373760 0 2927699406643434241 7459423539927724553
def a475 := f 3821728701018091521 11611760980308000768 92611875432695565 139747328 752737755141984256 676788989314727936 91029667332715008 1462408193 1697267969 4697386370062376960 1410871297 649947862187419925 91010975477530624 11539938679161571847 167872337800612359 6059927556773275941
def a476 := f 167872336750518308 91010975633785344 7310512354791924992 6422524516264069632 671372796152471558 6536597717870609 42805130132207872 1703541573288984576 747933990381039765 4999312292976282112 6059646080890974209 11603685574228412713 748234156786921473 6819173801144855 167872335838775042 92893349473813534
def a477 := f 29858338927878155 6422524629580257838 19483136 139747584 5873608812289159683 6819171115466752 10526045438459933222 6198213239342643245 157307392 3859868735219258112 3630315941478299652 83397959385290050 92611873154810368 239929930012717056 5927150543173073408 600211305156384720
def a478 := f 743166506285218304 653080452014815744 1363685393 675876395642479148 39393026 7429393484803552256 123880704 7289427844916595200 91010975479187968 6060209029522073088 5220517621490203148 5051475290710155275 523349942654814720 92611873036592896 91010975633846784 160183451148042772
def a479 := f 97116572311642624 6536598007150596 150386802400690176 91010977156902913 671108912403010304 600211302997690114 173977933569877764 6296613701829357568 97398047170504706 4697368777775671040 7100646168148236 92893349417220139 7103391676887543823 19483136 523349942678655754 671108912252589056
def a480 := f 7222182929311938828 7438402884386435073 91010975629771299 83114284377780225 395588105 378418548746375970 671108912385384448 303470706946166784 600210203464972544 91010975479118336 8523161282145300772 6536596627128320 6059646079502780162 595407536818246420 319374610 169473233476935936
def a481 := f 3470418255902433795 2640102309434440204 83679433307205649 92611873036900098 244733696963540513 6059927555146281937 167872336429677070 743430389113317120 676176563036178951 6229095157942413312 6064431154085771776 92893347995407872 95533269528954642 6059927556154935559 83397957060663040 523349942791856128
def a482 := f 4972684372069134848 600210204874387457 5856984165347766889 8724996504433526274 139474688 169473233376274176 1082366528 6059927554464814080 523349942656521728 6059927555556204550 747933988843377664 3051014116876813837 167873435485155840 7433898186556085030 1521920 7289429107635388416
def a483 := f 157373184 963773967 675611413711168261 95814741901135872 172676103065961743 92611874458707041 11688837801998243328 167872336707092993 169191759476646150 6818071748825620 6202716840294625281 5051511565235341081 3902175792066492420 167872337486042181 169191758379895040 5051212499826116365
def a484 := f 5927150543210571520 11040196394246144 167872335974576640 3821711108102768409 600210203464976896 5856984165008233472 167872337513296954 167872335962198804 6055425110215034626 5857265640020588812 675876394683091456 331078395845233152 6059646081915291405 91010975514825984 236444478438651357 163068569655206144
def a485 := f 10535069864830518039 649945663682269387 675912680964633111 671108913437512449 246053119029741064 164670559319259140 600211303337314828 6818071625029120 667484921922074880 331078397051556613 671108912407331348 167872337496584193 4999312293013776128 748234156205821958 403153583460593665 595407537899066117
def a486 := f 83679431945042176 743166508969243159 2852257445940778496 743430391122254117 6836763303033344 6059927554614178304 92611873019815680 5999078459261845504 95814741953425920 6059646080891039745 600210203463385088 7652045811081239054 92893348113965056 1736655371 10459054937053202178 29858337921258240
def a487 := f 6536596637029130 83679432083059200 6289294609423155968 8527728656528180738 600210204122261525 0 600211303001567277 5854811475253276687 523349942954640658 139477504 747687698130946306 29576864198176769 6059927554596560896 1415544290990502170 10665985894591382272 29858339174821889
def a488 := f 4793907006896627968 326292221710041088 4972650372973946624 6059646080094967560 6422243154151809324 42805130286875136 6818071605426432 2640102309378806794 6059927554495899392 6536598037999617 1679437825 1225810693 9611651662439610894 1698121991 6059927730572101122 6536596766667264
def a489 := f 5927150544582356993 6059646079636419072 6818072779916033 11340365361853003 675630104059052032 4062815375824257024 1816647453992436480 5856984165125280512 8805194938400187648 169191759771414529 157364736 672268898457448963 7213130535404056593 671108912283915778 169191758379895296 10387016073671109134
def a490 := f 6489797035717584640 3855117633632337920 600210205631862290 76943360 4134381093064873472 4852091061897139456 244733697836265473 173031936 83679432116613632 6060209030047340296 600210203852706387 86198317 6886400 752492564306997819 380314476340082692 239929929876329984
def a491 := f 92893348148368128 1443068423 6204115318912280576 6836763476780032 7438402882977151488 4708847727786078209 4999312293132063488 4978837153238761984 0 101652049011146752 753037921817485568 519224666613100545 92611873821980193 6059927554525009410 6204115318911227392 7296415306623914497
def a492 := f 2956702783126123067 671372795036303360 748234155533292032 143868436 5850307875238541447 6269406531395281152 10459054937069917954 9900810 169191758362065152 675631203627661312 91010975633785344 671372795075389184 671108912245637120 11679909969444537858 527276298751986188 6818072728983835
def a493 := f 167872335824840745 6059927555833112373 442363304884979968 6818072044447910 600210204908942083 167872337433340189 5192742039256117249 4979118628198965248 600210203465955584 6059646079876739593 169473233337188352 6422524903467362581 4143880169273180672 39085824 895566370 6202433240601855757
def a494 := f 92894447848147468 6059927555620806667 92611873086055936 371062093394363136 743166506283565056 6819171152762624 167872335838840322 218585471575409152 83679431965763328 671108913745232926 97398047114803712 4686619144631158274 1522176 8796976170602665730 0 6287876932188123403
def a495 := f 326292221729458432 600210204874321921 4708621292815396865 523349943299425033 6060209031112896513 710369580 747933989795292932 321542434 0 155406336 748234155443525378 5051212497390927872 7228620767385092096 169473234260627969 671372795057800706 40326144
def a496 := f 56981504 155406336 4999312292974690304 5856984165007365890 5050112099141833490 6836763457765888 3564124141810352128 6059927555620806667 6535497117022464 6060209029554131978 97398047132699136 21190144 600210203620692480 167872335956959488 92893347974217728 6819171272774144
def a497 := f 8451683221389263374 3855103276171364112 11679248490322084097 91010976927784971 600211303148106240 160463826508711682 6417739442719721903 6489797035852644864 1410936833 6059927554495899392 675912679958261761 6059646079501293056 88614435 83397958126022703 157373184 6418544663520227329
def a498 := f 910250008 95814741779283968 92611873171718912 3822027768149932036 152188170 236163003018379264 7100646265209344 97398047235067904 241230653555294255 752737757051377957 6494582110302063104 3821429634861901263 91010976641523723 6999589806671411456 1232279055 3563860452293214208
def a499 := f 523349944301684996 11674764569143301650 6059646079481624832 7158271281916754188 6059927557161560342 675611412363033088 7289427844972292098 6819171115466752 88548864 600211304385884161 1511023621 362301964 671108912266827264 600210203463385088 37974125 175268864
def a500 := f 1453107018161877763 0 7293378415985649408 6059927554456813568 0 403153583460724737 6229095157942846978 7438402884487701509 6289294699442208768 326293322632605697 330196880968986625 7100646265209344 3893786293684475650 92611874093871119 747970272625522688 676176561377515522
def a501 := f 156254720 6204396793944745992 169191760795666189 156254720 6208620018029035520 675630104059052032 0 27728734087047168 39454466 4697367678226544896 7293378416121049344 671372796447240193 2610532122176279301 172676102141208320 95814741953434368 7086765932023202053
def a502 := f 6197930664770685440 5051212498801864705 6204029965080934668 11612259016125710336 157434624 6494599702507710208 6059646079480102912 1703015466961797651 326292221732652802 671372795057493504 22619136 7222182930646904833 7293379515476621824 0 21562882 167872335836629504
def a503 := f 6819171221452800 91010975477530624 6234287438374633472 3966142956541997636 91010975518033922 6537696297239296 216621391487309826 6059646080891039745 319374866 600211302997321472 7433616708900059136 169191758360477696 6417739441640570880 92611873170539008 6422524516401959424 91010975477530624
def a504 := f 97398048810418177 3850614034065266432 369742679881516816 172676102275219968 5287812328705062912 244733697507672369 92611874174505013 6536597309047561 1411040861500278530 743430389964042753 91010975499839232 169473233359496960 7648327527229837824 675876395562308650 5123569159004763929 1696153601
def a505 := f 1699037975357780548 675630104740644633 6059909962295490048 7293379515526706750 675912678909692428 595407538084196353 5336876742273619456 6422524516283737856 6818071605492224 91029667350533120 6536596646545664 6063597157508731392 6422524516244652032 671986323700418866 0 121851904
def a506 := f 523349942759212288 743166506457776896 600217901408464913 11540220685344704264 83397958377680897 7084594339124938242 29858340471453458 6818071643297538 528152609425457152 6274191605861136640 175137536 106438223283171840 169473233337188352 676176561338056704 7100647271899155 6060209029504243200
def a507 := f 6202715739391609344 3564124141849745154 1521664 675876396393464323 1522176 748234155398596354 83397957006202626 21190144 97116572157695488 675876396394513155 371838166180955917 600210203482868224 6800479557541888 5046374788101263360 677071563977150976 92330400258683459
def a508 := f 531764506738829597 4978837153101924608 671372796447174657 109546735773628672 671108912385384448 455207709543368450 167872337180962833 6819171237318656 675912681266840358 4972933286865428736 752178104995753985 653868720321935628 7280422900557178880 6819172561023747 39085824 6090678712842321920
def a509 := f 7293378415984969218 172676102118965248 169191758360477696 7221620143985550341 747670106054803988 303453114659899138 23427072 6536596627128320 91010976923022337 6060209029435046144 6819171252396852 167872335991362304 523349944146478023 389322773 8086936674058704642 4004016884685509640
def a510 := f 1380022276 5715968 455202211945775104 3464542576295085570 6197931077915403597 676176562244649473 8800957283124117504 2435188493 7433898183836565504 7433898183844500480 3850614034026530306 523349943024658453 671372797456655671 11340363818549794 595407536675899904 671372795058915074
def a511 := f 97116573917082885 7289427845021053952 1729790467 402855236441473024 6198212139768365609 3821728699782353664 7284924246967005185 7278530861729908179 671372795057493504 7285207975143736834 83397958146658502 599051318209296896 37361152 6059927554458466816 7288101547572164871 1775880642478760448
def a512 := f 3850614034401604105 11539938677835994901 6818071605360896 6208620020750555149 8163117900931348908 173977934628099895 594867719575392939 743430389230486016 6208901493027309058 167872337283285340 128008843 6059927554496272130 528153708959393536 40507394 677071566506690317 523349942635331584
def a513 := f 5992398964777811968 600211303114694656 6202715740261941761 614696818 6059646079501293056 178233033924830976 1125144859 747687698136065792 7031051508465611280 0 3893786293818176000 173031936 675876396027359249 6536596649436928 6059927554533898764 10450165493067170304
def a514 := f 677072663336257026 5129689057888317961 241266944605640192 6819171118172672 675912678686019584 7228894341116224517 92611873019135490 244733697503467805 92611873004393472 10387016074755911681 169473233358378496 138629120 7284906654512525313 7284906653123151362 7212849059063660544 1163993099
def a515 := f 6819171116988672 33834348077732608 11611976443001057297 10387297738711117825 91029667212563968 2640384 672285390249873414 680379994312238848 6059927554456813568 6818071761146368 671372795211506432 39393026 5046023214846248450 5080396899091243008 7296415782496589568 95814741800474112
def a516 := f 0 0 73825608735391744 169473233949587982 6354903558998982656 164668358974076928 174141952 10387016073518068224 748234155413345792 6489797615620935680 6536598533596472 675630105274548510 167872335817211904 5261666927366516737 594586246090871064 5865729904925547037
def a517 := f 622713996552046349 600211304671232526 1699037974776789267 6422524629324738561 10459054937033165312 600210203575066880 167872335973528064 6208620019193028619 4834937950711355413 6208620018710693657 5264816837522096128 91029667175202816 0 173977933887123457 6422524516244652032 7433898183836565504
def a518 := f 743430389074231296 1495360517 157643264 5051212497412490754 156254720 160463827376577074 5883777124482180864 2640384 167872335895203840 1411922068666413056 675912679740314369 83397957006268418 3563860453989299258 1443068167 5927150543210878722 169473233356671488
def a519 := f 167872338503997462 91010977429086531 1411040691043207428 5194374603569967105 4708902768348915996 675876394684864000 7102534761101865984 8446582495888429062 11612259343157921552 11612259342619195660 6060209031417574750 671108912271142957 3632163119633006592 6059927554478441986 92611874408443905 92892248464177664
def a520 := f 244733697854095361 8163396257349843200 676176561496408576 5854811474315198720 4999312293148840704 2960561866697947648 157434624 2999758099087496448 169455641190602498 6536596649740034 10387016073400837888 92894448677115910 4978837153084029184 600212402608492544 8163448432785175040 7566408173806563343
def a521 := f 92611874161500171 22430464 167872337197238532 6537696138756096 6819171259335188 4067318975453280768 680132604213884928 160182352902369550 671986322564806656 3927712195775197322 2703623949 326292223406260750 600211302975012864 169191760056631297 6060209030039229970 0
def a522 := f 4067318975472817664 11764852728519921696 92611873141375508 7289427845760682269 1587456 164668359109075712 160182351494134016 10381978116525465611 164670566615394306 6537696278503424 4004016882721555970 91010976857887078 7280422902248932099 95814741918761728 6819173533882390 91010975505392650
def a523 := f 167872335839823618 91010975635956736 1699038270171722240 7284926501591020291 0 752737755159609856 174141952 675876394991158792 4709129202762854401 1672128577797112320 7289427844954089216 6536596634014720 11674880000078643200 7567193305638307330 83397958649910035 5044408742009516047
def a524 := f 676176563033089082 167872335939063808 1699037973737584908 6059927554495899392 6229640676585317726 6271845574620762624 3548949894915436545 747970273996255233 83397956968401408 167872337262768899 7228861324263564800 6204396793868339712 330777113870872577 7012255270245052928 97116572465038856 7228861324347002880
def a525 := f 743166507474838426 4999312636573661696 2960563219650078464 6059927554613068288 5051212497447098114 6818074289517079 7213130534041893120 600211302996203008 92611873019069954 1414860427590910464 2636319955173265920 105074688 10458772362549072896 3990209642344484896 675612511994859520 167872335818865152
def a526 := f 29576862909026304 725207126462579456 7289427845053632512 6536598072685315 92330398040279552 748234156786921473 748234156003233888 83397958696075352 1163993099 1699037975054729591 167872335818799360 1699037973783465984 671372795075761922 523367534860769026 6059927556136185857 6536596648318464
def a527 := f 303453114660579072 3927175227708044067 4832460373860455169 5927150543293337600 7289427845020078080 6204396793921873152 6276367865810061058 675876395760103439 246053118739244800 675630104197692038 6059927554495899392 92611873171718912 676176562734826003 7100646093764864 3488462395908101120 244733696176376320
def a528 := f 6060209029472982786 6204115318911227392 600210204145304329 6059927554458401024 1744486340064676139 10387016074441338895 160182351532750848 95814742609059891 2927699406878224385 11616798939786863621 465037344362889729 6536596628716032 5123569160037167875 6204115319047401984 10459054937186779648 7293378418414350423
def a529 := f 1699037973669614848 676176563036178695 6063596650685879040 92611874492867615 101902746291300096 599315202224186117 672297218066683650 671108912403985920 7103113638299329541 675630104082479104 1775599168690092036 2640823556121912351 303457512842216192 1672006961405049100 6276471981501657089 370565282879123457
def a530 := f 675631203592308226 3966142955165140242 92893348937991695 169473234849326198 303453114677356288 95814741818369792 303453115762824841 452703340017500672 2888067423102190336 600211304371782163 4793905907267561216 5926869069017531878 167872335818869248 173977932480995594 5264799245493694976 97116572751369992
def a531 := f 523349944046268417 595425130371441669 313006771311559168 6536596648691458 743166506322650880 523349944097739777 4215942162645938691 747670107321872385 92330399431733290 1600069884073476096 169191759771414529 1672128577645709058 748234155375984640 600211303871553808 671108912265054720 389851638994715392
def a532 := f 7284906654511342394 1847693093399790081 671372795036303360 4979118630509113743 160182351514859520 675630104060573952 173204967231408640 220823725063422720 169174166332782080 5927151642683113472 6536598091468832 671372795193946368 6819171117058560 121851904 523349945336693286 676790088845838848
def a533 := f 19417600 6059927554631951104 747670107321872385 3553453841197380096 6059927555164690652 330469215735071250 6819171115466752 96343606911637250 5084849579128150300 95814741800474112 6060209029455954688 4059566628580635145 599315201005327360 167872336431908624 523349944330363962 10459054938443022947
def a534 := f 6059927555867750401 39085824 748234156870231045 97116573504061464 8523161281078785034 21628674 6059646079480102912 4972933975436821534 6053161937446913536 677071563822483712 97116572964254311 0 7293378417329271392 7284924246698569729 671108913656508417 169473234245718069
def a535 := f 47590204856553472 6202100017330729472 3564124141983445504 5857265640626537225 1775635499285106694 4697367678399042048 1816647454294173966 1522176 1698136624 4832477966264512513 4972933974332813833 169455641237357609 4832460372669053184 676176562502049803 748234156821541635 677071563891615232
def a536 := f 7422928375941302029 5215754736054335770 3819410950744851200 4979118628080408064 3855117633654646528 7221900354747629568 1513171048 167872335973736448 5051212498801799169 671108912247224832 6059646079480102912 1591808 667502515756042500 3464523897484051510 91010975477530624 4697367678226479360
def a537 := f 95814741779283968 160463827375849985 6422262945557393409 653149532343187724 5938629491831297536 7151999963868692480 106438223128443392 167872335956755200 6059646080698621988 91010976961462558 743430389113624322 671108913404928515 172676102138382848 6284791009622112512 1495360517 2927699406563651599
def a538 := f 10616112686969415424 6217399309277814784 6208620018068494338 403153582187239168 11688837802372641289 3893786293684168448 676176561511088640 650333683127115776 6801580340424705 55191040 1591808 6204115318891690496 743430390753603585 6059927554478003712 6819171137029890 7293379517173156103
def a539 := f 174025306579277576 95814743239431085 671108913075474438 4139377671319742245 4789640957802334801 4064234970285355529 523349942808424960 5783493958820182528 7213130536741995046 167872335824106752 677071563824256512 4978782367155333397 92611874099130904 1983400455 1679437825 6818071603838976
def a540 := f 675630104388634120 671108912419779072 747970273815364456 4709129202762854401 515754834178742274 3850614034027644674 95579321760249856 95814743222356487 7136677835683684352 6059927554593157417 600211303950653826 6422524628052430848 95814743190286337 167872336910903044 7222182929397662228 95814742693650704
def a541 := f 7285207975123765760 5838716977589474816 5283007278325256960 747970272591094784 101902747702532462 6059927554456813568 1183908719 6818071757017088 747687699174369388 523356539705098240 1461330770 676476729423310849 677071565482438657 2928820838629332480 671108912267265538 6536598038130689
def a542 := f 6836763474604544 4979400103037450752 0 7103391677173668125 289753393068795648 95814741936591360 5051193815494926918 11603386066074677249 6064396721352562176 671372796481860355 7293378416001373696 91010976888467457 6536598325250311 6059927554497139712 6059927555867684865 622713993867839744
def a543 := f 3821429632617492992 4999312294138683403 1411040689720530946 671372795055720960 95814742875713551 91010975479052800 680980327778443264 672267797896901129 671108912927556361 172676102240817152 6819171255214336 6059927554456813568 167872335939063808 7284924245338069071 226876529507450881 7157496617213981187
def a544 := f 3927703269572573447 4697367678318823948 6537696260608000 91012075146801664 5080396900362432513 6202143161482049540 6059927554456813568 672268897035552514 743166506285218304 6417739828309479424 671372796719403795 4832529642863855631 6204115321593688202 97116572136505344 6059646242863072000 1632905501
def a545 := p 4 a376 a377 a378 a379 a380 a381 a382 a383 a384 a385 a386 a387 a388 a389 a390 a391
def a546 := p 4 a392 a393 a394 a395 a396 a397 a398 a399 a400 a401 a402 a403 a404 a405 a406 a407
def a547 := p 4 a408 a409 a410 a411 a412 a413 a414 a415 a416 a417 a418 a419 a420 a421 a422 a423
def a548 := p 4 a424 a425 a426 a427 a428 a429 a430 a431 a432 a433 a434 a435 a436 a437 a438 a439
def a549 := p 4 a440 a441 a442 a443 a444 a445 a446 a447 a448 a449 a450 a451 a452 a453 a454 a455
def a550 := p 4 a456 a457 a458 a459 a460 a461 a462 a463 a464 a465 a466 a467 a468 a469 a470 a471
def a551 := p 4 a472 a473 a474 a475 a476 a477 a478 a479 a480 a481 a482 a483 a484 a485 a486 a487
def a552 := p 4 a488 a489 a490 a491 a492 a493 a494 a495 a496 a497 a498 a499 a500 a501 a502 a503
def a553 := p 4 a504 a505 a506 a507 a508 a509 a510 a511 a512 a513 a514 a515 a516 a517 a518 a519
def a554 := p 4 a520 a521 a522 a523 a524 a525 a526 a527 a528 a529 a530 a531 a532 a533 a534 a535
def a555 := p 4 a536 a537 a538 a539 a540 a541 a542 a543 a544 a536 a536 a536 a536 a536 a536 a536
def a556 := p 8 a545 a546 a547 a548 a549 a550 a551 a552 a553 a554 a555 a545 a545 a545 a545 a545
def slots2 (i : Nat) := (a556 (i/2) >>> (32*(i % 2))) &&& 4294967295
def a557 := f 253292781075434606 184585187437867520 126276986310768138 703893744651294 885133593444364322 378690221701596163 54676514629238039 289462861061181955 2380257957121688072 36031890891776581 1856504090931774491 109290566743756808 37014031112358403 828662333315483153 4184236512922602078 684559583118908929
def a558 := f 703583197555598341 183522234715078667 1873567884865699864 217307691409474604 3084794983159971331 40533848872 0 0 0 0 0 0 0 0 0 0
def a559 := p 4 a557 a558 a557 a557 a557 a557 a557 a557 a557 a557 a557 a557 a557 a557 a557 a557
def dis3 (i : Nat) := (a559 (i/7) >>> (9*(i % 7))) &&& 511
def a560 := f 20060344708 3022109313 2754091776 2897224576 5043892360 7315966022 11753687600 2762480384 14129135746 0 0 5539334921 20060309764 2762480384 2762480384 2754091776
def a561 := f 0 748241409 2176988035 3030499969 7039134491 11972706434 5144093580 11559648400 11275090689 0 0 2754091776 8993354369 9986705816 5044708224 10797335698
def a562 := f 14120190082 883016321 9329226651 8993354369 8993354369 0 2754091776 9852453126 9289564349 19872819479 19917210686 20060309764 11836981535 2762480384 2897222528 2726572428
def a563 := f 9269523472 874068481 11292916481 19489034887 8993354369 7561838854 2177514499 4458689411 2619540118 20049530951 2224143056 5178505729 11559648400 11174416457 413318149 2762480384
def a564 := f 2754091776 2730498855 4467637251 19873864707 2754091776 7434969144 5044708224 5178505729 5178505729 3030499969 2762480384 7651168982 2762480512 2754091776 2177514499 2897224576
def a565 := f 3125396107 2453324977 11972706434 0 2754091776 10767012377 3382936329 20060344708 3380820303 7704969478 2762480384 5043892360 11606231559 20060379327 11821744426 11606231559
def a566 := f 2762480384 7696580870 11284003585 5572790274 5044708224 0 9463038384 5144099364 2751572755 2754091776 186361011 413320325 2754091776 17878288388 3022109313 883016321
def a567 := f 3029445216 5044708224 11972706434 5573869753 2762480384 5178505729 3030499969 2763004800 5178505729 413320325 4901575424 2730498855 8727042842 5312758529 2762480384 9315582343
def a568 := f 11838488706 3380848981 11838488706 5044740992 5043892360 11606231559 2762480384 3382936329 4467637251 2762480384 3030499969 8993354369 11971824434 9001218699 20060344708 0
def a569 := f 11606196743 5044708224 883016321 186361042 7696580870 2686108476 2762480384 605600391 2753243144 11275090689 2185935875 5144060812 883016321 11552471569 5043892360 9807938347
def a570 := f 7704969537 8769355811 4499163698 5170117121 19597411094 0 0 20016990766 4468161539 0 20060344708 0 7709659927 8993354369 2726413069 2762480384
def a571 := f 7704969478 0 4467637251 8770821013 2761622410 3030499969 2897318957 9852488070 11275090689 2177512323 5043892232 11606231559 11972706434 5043892360 0 2762480384
def a572 := f 7460766337 11559648400 2762480384 11284003585 2687179829 2751572755 8766364431 2897222528 11606196743 748241409 11972706434 11972706434 0 2762480384 413318149 13330785476
def a573 := f 2177514499 19917179140 2185935875 2762480384 8993354369 11606231559 0 2887856513 5043892232 20060309764 2761622410 9010131595 11559648400 0 11972706434 9852488070
def a574 := f 2754091776 4467731351 9001219214 2762480384 5539334921 7696580870 11606196743 2726413069 2754091776 2177514499 2216905135 7704969478 11838488706 14120190082 7561838854 8993354369
def a575 := f 7696580870 2762480384 11972706434 11972706434 2178036611 11606229511 11838488706 5043892360 8993354369 2895884296 14118682911 2185998808 413318149 2897224576 13046563730 2762480384
def a576 := f 8767685413 5178505729 11972706434 747870760 11284003585 5044708224 8766364431 8993354369 5043892360 883016321 413320325 413320325 9717746054 20060309764 7839187224 2751572765
def a577 := f 13057104537 20060309764 883016321 5539334921 883016321 2896245121 13046565906 11838488706 5178505729 1152950673 5044740992 0 20060309764 5320585908 2754091776 2754091776
def a578 := f 2762480384 0 9013232296 11291867915 20060309764 3383460617 8793981760 11838488706 14120190082 11140872961 6652406090 2895840138 17726341550 2454371387 3383460617 700529166
def a579 := f 11284003585 11972673822 3030989313 413320325 11846324244 17912861060 5043892407 8993389313 8995911981 9002267265 882459137 11559648400 739850753 0 9852488070 5178505729
def a580 := f 11972706434 13984465183 11972706434 11606229511 2754091776 8752480928 748241409 5044936886 14129102978 5044708224 20060309764 11972706434 5539332873 3248685705 9852488070 4333943811
def a581 := f 5147048459 2169125891 11972706434 7704969478 2897222528 14129137922 13054428306 11838488706 413318149 5044740992 5170117121 9868220546 2762480384 0 20060344708 3517121161
def a582 := f 8993354369 5539313836 8753525388 2897224576 5539334921 7704969478 4467637251 21638058780 8993387137 9043455045 4468161539 20060344708 2754091776 10766455321 11284003585 0
def a583 := f 0 2762480384 11972706434 0 8753525388 7696056600 5178505729 748241409 20025772066 2896245121 11838488706 883016321 11838488706 2763004800 19918786956 2726413069
def a584 := f 5179548315 883016321 2754091776 0 11284003585 11972706434 11284003585 0 11602788546 11838488706 2897224576 2763004800 8993354369 2762480384 5016537997 0
def a585 := f 2897224576 0 0 19917179140 11846324244 2897224576 2763004800 11838488706 11972706434 3382936329 2897224576 0 11838488706 11300765891 548095109 2853379159
def a586 := f 0 2177514499 0 9002267265 20060309764 0 0 0 2730498855 19917179140 4893868254 0 0 2896364426 2895323560 11838488706
def a587 := f 9002267265 883016321 20060344708 11284003585 0 5539313836 20015985047 11606229511 13333701832 2177514499 11294936097 413320325 5178505729 2686200614 5312197300 11275614977
def a588 := f 0 2726572428 11838488706 5043892360 5144066596 2897224576 5146524171 4459248643 2754091776 2178038787 0 2754091776 2730498830 0 0 9004300562
def a589 := f 9012677537 4467637251 0 0 413320325 0 7839187224 455845087 2754091776 2897224576 5178505729 17769695492 11291867918 5313241745 5178505729 9852488070
def a590 := f 5044708224 2853482916 11606229511 3030499969 8766364431 11972706434 7704969478 4467637251 0 11838488706 11972706434 0 9001218699 9850947586 0 2762480384
def a591 := f 2991178379 11972706434 2185935875 7852425565 2762480384 11010620237 7651508907 20060344708 20052511116 13057661593 19345940684 3022109313 5178505729 11838488706 2754091776 202512462
def a592 := f 3022109313 3166706193 0 5178505729 2177514499 3030499969 2762480512 2897224576 4333419523 2991178382 11606229511 8766207057 17878288388 2762480384 2762480384 883016321
def a593 := f 3391849225 2762480384 2762480384 5289656843 0 4910189334 2897224576 5147048462 2762480384 2754091776 11821744426 2726413069 9010131595 0 2754091776 2177514499
def a594 := f 9852486022 2169093123 4467637251 11972706434 11972706434 2754091776 19907218209 20134824404 4910005009 413318149 11606231559 2596279123 5178505729 2754091776 5539332873 11286561042
def a595 := f 11560172688 8753525388 11972706434 2896408584 2763004800 5539332873 17458954652 2897222528 2896245121 14129102978 19480651865 5043892360 2895884296 2754091776 17769695492 11606231559
def a596 := f 2754091776 1103802938 9269523472 5044708224 4873896717 5044708224 2762480384 2754091776 5178505729 17886087437 12007282946 11846353065 0 2897224576 0 9852488070
def a597 := f 14129137922 0 20060344708 2990652043 19915348235 0 8993389185 739850753 11284003585 4467637251 2897224576 11275090689 9815360559 2726413069 0 0
def a598 := f 9852488070 5539334921 11838488706 2177514499 413318149 8770821013 14120190082 5178505729 5043892360 0 413320325 0 5044708224 413320325 5044708224 0
def a599 := f 0 2762480384 19347966748 20060309764 162252123 11972706434 2754091776 13054426130 2753200906 0 9986705816 5171159707 14129135746 11972706434 0 2754091776
def a600 := f 456737483 0 4459215875 2762480384 0 11275614977 9852486022 2887856513 2754091776 21493352967 2856399246 0 0 0 5170117121 548095109
def a601 := f 2759961363 0 5178505729 21643670236 5170117121 883016321 0 882983553 163202225 0 2762480384 11284003585 1260953946 3030499969 9852488070 5044740992
def a602 := f 5178505729 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
def a603 := p 4 a560 a561 a562 a563 a564 a565 a566 a567 a568 a569 a570 a571 a572 a573 a574 a575
def a604 := p 4 a576 a577 a578 a579 a580 a581 a582 a583 a584 a585 a586 a587 a588 a589 a590 a591
def a605 := p 4 a592 a593 a594 a595 a596 a597 a598 a599 a600 a601 a602 a592 a592 a592 a592 a592
def a606 := p 8 a603 a604 a605 a603 a603 a603 a603 a603 a603 a603 a603 a603 a603 a603 a603 a603
def slots3 (i : Nat) := (a606 (i/1) >>> (35*(i % 1))) &&& 34359738367
end HA
open HA
def wordHash (ws : List Nat) (scale : Nat) := ws.foldl (fun h w => (h*scale+w)%2147483647) 17
def hintNumber (ws : List Nat) : Nat → Nat
  | 0 => slots0 ((wordHash ws 7923+dis0 (wordHash ws 1000003 % 1637)) % 7177)
  | 1 => slots1 ((wordHash ws 7925+dis1 (wordHash ws 1000003 % 2503)) % 10937)
  | 2 => slots2 ((wordHash ws 7919+dis2 (wordHash ws 1000003 % 1229)) % 5407)
  | 3 => slots3 ((wordHash ws 7927+dis3 (wordHash ws 1000003 % 151)) % 673)
  | _ => 0

end Live3210.SubsetCheck

namespace Live3210.SubsetCheck

def insDigit (x : Digit) : List Digit → List Digit
  | [] => [x]
  | y::ys => if x.word ≤ y.word then x::y::ys else y::insDigit x ys

def sortedDigits (xs : List Digit) := xs.foldr insDigit []

def axesFor (sorted : List Digit) (n code : Nat) :=
  (List.range n).filterMap (fun i => sorted[(code >>> (4*i)) &&& 15]?)

def permitsDigits (ds : List Digit) (surplus : Nat) : Bool :=
  if 3 < surplus then true else
  let sorted := sortedDigits ds
  let num := hintNumber (sorted.map Digit.word) surplus
  if num==0 then true else
  let bits := idBits surplus
  let ban := (prohibited surplus (num &&& (2^bits-1))).pattern
  let axes := axesFor sorted ban.count (num >>> bits)
  !(ban.colors==surplus+1 && axes.length==ban.count && ban.rules.all (ruleOK ds axes))

def guard (vs : List Nat) (gates : Nat) :=
  permitsDigits (prepare vs (List.replicate vs.length 0)) (gates+1-vs.length)

end Live3210.SubsetCheck


namespace Live3210.SubsetCheck
open Search Ordered Blocks

private theorem ins_subset (x : Digit) (s : List Digit) : insDigit x s ⊆ x::s := by
  induction s with
  | nil => exact List.Subset.refl _
  | cons y s ih =>
    rw [insDigit]; split
    · exact List.Subset.refl _
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|old
      · simp
      · rcases List.mem_cons.mp (ih old) with rfl|mem <;> simp [*]

private theorem sort_subset (ds : List Digit) : sortedDigits ds ⊆ ds := by
  induction ds with
  | nil => exact List.Subset.refl _
  | cons x ds ih =>
    intro v hv
    rcases List.mem_cons.mp (ins_subset x (sortedDigits ds) hv) with rfl|old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih old)

private theorem axis_subset (ds : List Digit) (n code : Nat) : axesFor (sortedDigits ds) n code ⊆ ds := by
  intro x hx
  obtain ⟨k,_,hk⟩ := List.mem_filterMap.mp hx
  exact sort_subset ds (List.mem_of_getElem? hk)

private theorem hint_ok {ws : List Signal} {masks : List Nat} (mix : masks.length=ws.length)
    (nd : ws.Nodup) (bound : safe ws) {d : Nat} (c : Coloring ws d) (p : Prohibited)
    (axes : List Digit) (inside : axes⊆prepare (ws.map Prod.fst) masks) :
    (!(p.pattern.colors==d+1-ws.length+1 && axes.length==p.pattern.count &&
      p.pattern.rules.all (ruleOK (prepare (ws.map Prod.fst) masks) axes))) = true := by
  generalize yes : (p.pattern.colors==d+1-ws.length+1 && axes.length==p.pattern.count &&
    p.pattern.rules.all (ruleOK (prepare (ws.map Prod.fst) masks) axes)) = b
  cases b with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at yes
    obtain ⟨⟨colors,length⟩,all⟩ := yes
    apply impossible_sound p.pattern p.checked (axes.map (rankOf c)) (by simpa using length)
    · intro v hv
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      obtain ⟨k,hk,_,_,atK⟩ := digit_at mix (inside hx)
      have upto := c.assigned _ (List.getElem_mem hk)
      have limit := c.fits
      rw [rankOf,atK,colors]
      omega
    · intro r hr
      exact rule_conforms mix nd bound axes inside c r (all r hr)

def gateScreen (d : Nat) (ws : List Wire) := guard (ws.map Wire.value) d

theorem screen_sound : Sound gateScreen := by
  intro d ws nd bound possible
  obtain ⟨c⟩ := possible
  change guard ((ws.map pack).map Wire.value) d = true
  have codes : (ws.map pack).map Wire.value=ws.map Prod.fst := by simp [List.map_map,Function.comp_def,pack]
  rw [codes]; unfold guard permitsDigits
  simp only [List.length_map]
  split
  · rfl
  · split
    · rfl
    · exact hint_ok (by simp) nd bound c _ _ (axis_subset ..)

end Live3210.SubsetCheck

namespace Live3210.SubsetCheck

def dupCode (ds : List Digit) := (ds.foldl (fun (p : Nat×Nat) z =>
  (p.1 ||| z.cover,p.2 ||| (p.1 &&& z.cover))) (0,0)).2

def quickRule (dup : Nat) (axes : List Digit) (r : Requirement) : Bool :=
  match axes[r.left]?, axes[r.right]? with
  | some a, some b =>
    a.index != b.index && ((a.yes &&& b.yes != 0 && a.no &&& b.no != 0) ||
      (r.prior != 0 && (1 <<< r.prior.log2) == r.prior &&
        (match axes[r.prior.log2]? with
         | some z =>
           let req := rowCode a.yes b.no ||| rowCode b.yes a.no
           req &&& z.cover &&& ((2^144-1) ^^^ dup) != 0
         | none => false)))
  | _,_ => false

def permitsQuick (ds : List Digit) (surplus : Nat) : Bool :=
  if 3 < surplus then true else
  let sorted := sortedDigits ds
  let num := hintNumber (sorted.map Digit.word) surplus
  if num==0 then true else
  let bits := idBits surplus
  let ban := (prohibited surplus (num &&& (2^bits-1))).pattern
  let axes := axesFor sorted ban.count (num >>> bits)
  !(ban.colors==surplus+1 && axes.length==ban.count && ban.rules.all (quickRule (dupCode ds) axes))

def quickGuard (vs : List Nat) (gates : Nat) :=
  permitsQuick (prepare vs (List.replicate vs.length 0)) (gates+1-vs.length)

end Live3210.SubsetCheck

namespace Live3210.SubsetCheck

private theorem selectedBits {α : Type} (xs : List α) (get : α → Nat) (select : α → Bool) (a i : Nat) :
    ((xs.foldl (fun v x => if select x then v ||| get x else v) a).testBit i=true) ↔
      a.testBit i=true ∨ ∃ x∈xs, select x=true ∧ (get x).testBit i=true := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    cases h : select x <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.testBit_or,
      Bool.or_eq_true,List.mem_cons] <;> grind

private theorem dupState (ds : List Digit) (acc : Nat×Nat) (i : Nat) :
    let cnt := (ds.filter (fun x => x.cover.testBit i)).length
    let out := ds.foldl (fun (p : Nat×Nat) z => (p.1 ||| z.cover,p.2 ||| (p.1 &&& z.cover))) acc
    (out.1.testBit i = (acc.1.testBit i || decide (1≤cnt))) ∧
    (out.2.testBit i = (acc.2.testBit i || (acc.1.testBit i && decide (1≤cnt)) || decide (2≤cnt))) := by
  induction ds generalizing acc with
  | nil => simp
  | cons z tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨one,two⟩ := ih (acc.1 ||| z.cover,acc.2 ||| (acc.1 &&& z.cover))
    rw [one,two]
    cases a : acc.1.testBit i <;> cases b : acc.2.testBit i <;> cases c : z.cover.testBit i <;>
      simp only [Nat.testBit_or,Nat.testBit_and,a,b,c,List.filter_cons,Bool.false_eq_true,
        ↓reduceIte,List.length_cons]
    all_goals generalize (tail.filter (fun x => x.cover.testBit i)).length=n
    all_goals rcases n with _|⟨_|n⟩ <;> simp

private theorem oneCover {ds : List Digit} {i} (off : (dupCode ds).testBit i=false)
    {x y : Digit} (hx : x∈ds) (hy : y∈ds) (cx : x.cover.testBit i=true)
    (cy : y.cover.testBit i=true) : x=y := by
  have d := (dupState ds (0,0) i).2
  change (dupCode ds).testBit i = _ at d
  rw [off] at d
  have ln : (ds.filter (fun v => v.cover.testBit i)).length ≤ 1 := by
    have e : decide (2 ≤ (ds.filter (fun v => v.cover.testBit i)).length)=false := by simpa using d.symm
    exact Nat.le_of_lt_succ (Nat.lt_of_not_ge (of_decide_eq_false e))
  have xm : x ∈ ds.filter (fun d => d.cover.testBit i) := List.mem_filter.mpr ⟨hx,cx⟩
  have ym : y ∈ ds.filter (fun d => d.cover.testBit i) := List.mem_filter.mpr ⟨hy,cy⟩
  generalize (ds.filter (fun v => v.cover.testBit i))=ys at ln xm ym
  cases ys with
  | nil => contradiction
  | cons z zs =>
    have eq : zs=[] := List.length_eq_zero_iff.mp (by simpa using ln)
    subst zs
    exact (List.mem_singleton.mp xm).trans (List.mem_singleton.mp ym).symm

private theorem outside_clear {ds axes : List Digit} {i k m} {z : Digit}
    (sub : axes ⊆ ds) (atz : axes[k]?=some z) (nonzero : z.index≠0)
    (sel : m.testBit k=true) (cz : z.cover.testBit i=true) (off : (dupCode ds).testBit i=false) :
    (outsideCode ds axes m).testBit i=false := by
  have existsBit := Nat.testBit_log2 nonzero
  have pickedBit : (picked axes m).testBit z.index.log2=true :=
    (selectedBits axes.zipIdx (fun q => q.1.index) (fun q => m.testBit q.2) 0 _).mpr
      (Or.inr ⟨(z,k),List.mk_mem_zipIdx_iff_getElem?.mpr atz,sel,existsBit⟩)
  cases state : (outsideCode ds axes m).testBit i with
  | false => rfl
  | true =>
    rcases (selectedBits ds Digit.cover (fun x => x.index &&& picked axes m == 0) 0 i).mp state with hz|⟨y,hy,none,cy⟩
    · simp at hz
    · have eq := oneCover off hy (sub (List.mem_of_getElem? atz)) cy cz
      subst y
      have zero : z.index &&& picked axes m=0 := of_decide_eq_true none
      have h := congrArg (fun x : Nat => x.testBit z.index.log2) zero
      simp [existsBit,pickedBit] at h

theorem quickRule_implies {ds axes : List Digit} (sub : axes ⊆ ds)
    (ids : ∀ x∈ds, x.index≠0) (upper : ∀ x∈ds, x.cover<2^144) (r : Requirement)
    (ok : quickRule (dupCode ds) axes r=true) : ruleOK ds axes r=true := by
  cases ar : axes[r.left]? with
  | none => simp [quickRule,ar] at ok
  | some a =>
    cases br : axes[r.right]? with
    | none => simp [quickRule,ar,br] at ok
    | some b =>
      simp only [quickRule,ar,br,Bool.and_eq_true,Bool.or_eq_true] at ok
      simp only [ruleOK,ar,br,Bool.and_eq_true,Bool.or_eq_true]
      refine ⟨ok.1,?_⟩
      rcases ok.2 with edge|⟨⟨nz,_⟩,good⟩
      · exact Or.inl edge
      · right
        cases zr : axes[r.prior.log2]? with
        | none => simp [zr] at good
        | some z =>
          simp only [zr,bne_iff_ne] at good ⊢
          let req := rowCode a.yes b.no ||| rowCode b.yes a.no
          let v := req &&& z.cover &&& ((2^144-1) ^^^ dupCode ds)
          have hit := Nat.testBit_log2 (show v≠0 from good)
          let i := v.log2
          have tiny : v<2^144 := Nat.and_le_left.trans_lt
            (Nat.and_le_right.trans_lt (upper z (sub (List.mem_of_getElem? zr))))
          have lt : i<144 := (Nat.log2_lt (by omega : v≠0)).mpr tiny
          have mask : (2^144-1 : Nat).testBit i=true := by
            rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true lt
          change (req &&& z.cover &&& ((2^144-1) ^^^ dupCode ds)).testBit i=true at hit
          simp only [Nat.testBit_and,Nat.testBit_xor,mask,Bool.and_eq_true] at hit
          have clean : (dupCode ds).testBit i=false := by simpa using hit.2
          have nonzero : r.prior≠0 := by simpa using nz
          have out := outside_clear sub zr (ids z (sub (List.mem_of_getElem? zr)))
            (Nat.testBit_log2 nonzero) hit.1.2 clean
          intro impossible
          have e := congrArg (fun x : Nat => x.testBit i) impossible
          change (req &&& ((2^144-1) ^^^ outsideCode ds axes r.prior)).testBit i=(0 : Nat).testBit i at e
          rw [Nat.testBit_and,Nat.testBit_xor,hit.1.1,mask,out] at e
          simp at e

end Live3210.SubsetCheck

namespace Live3210.SubsetCheck

private theorem allowed_quick (ds axes : List Digit) (sub : axes ⊆ ds)
    (ids : ∀ x∈ds, x.index≠0) (upper : ∀ x∈ds, x.cover<2^144)
    (rs : List Requirement) (flags : Bool)
    (ok : (!(flags && rs.all (ruleOK ds axes)))=true) :
    (!(flags && rs.all (quickRule (dupCode ds) axes)))=true := by
  cases ff : flags with
  | false => rfl
  | true =>
    cases yes : rs.all (quickRule (dupCode ds) axes) with
    | false => rfl
    | true =>
      have good := List.all_eq_true.mpr (fun r hr => quickRule_implies sub ids upper r (List.all_eq_true.mp yes r hr))
      change rs.all (ruleOK ds axes)=true at good
      simp [ff,good] at ok

theorem permitsQuick_of_slow (ds : List Digit) (surplus : Nat)
    (sub : ∀ n x, axesFor (sortedDigits ds) n x ⊆ ds)
    (ids : ∀ x∈ds, x.index≠0) (upper : ∀ x∈ds, x.cover<2^144)
    (good : permitsDigits ds surplus=true) : permitsQuick ds surplus=true := by
  let num := hintNumber ((sortedDigits ds).map Digit.word) surplus
  by_cases large : 3<surplus
  · exact Eq.trans (ite_eq_left large) rfl
  by_cases zero : (num==0)=true
  · change (if 3<surplus then true else if num==0 then true else _) = true
    rw [ite_eq_right large,ite_eq_left zero]
  · have simpGood := good
    rw [permitsDigits,ite_eq_right large,ite_eq_right zero] at simpGood
    rw [permitsQuick,ite_eq_right large,ite_eq_right zero]
    exact allowed_quick ds _ (sub _ _) ids upper _ _ simpGood

end Live3210.SubsetCheck

namespace Live3210.SubsetCheck
open Search Ordered Blocks
private theorem quick_ins_subset (x : Digit) (s : List Digit) : insDigit x s ⊆ x::s := by
  induction s with
  | nil => exact List.Subset.refl _
  | cons y s ih =>
    rw [insDigit]; split
    · exact List.Subset.refl _
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|old
      · simp
      · rcases List.mem_cons.mp (ih old) with rfl|mem <;> simp [*]

private theorem quick_sort_subset (ds : List Digit) : sortedDigits ds ⊆ ds := by
  induction ds with
  | nil => exact List.Subset.refl _
  | cons x ds ih =>
    intro v hv
    rcases List.mem_cons.mp (quick_ins_subset x (sortedDigits ds) hv) with rfl|old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih old)

private theorem quick_axis_subset (ds : List Digit) (n code : Nat) : axesFor (sortedDigits ds) n code ⊆ ds := by
  intro x hx
  obtain ⟨k,_,hk⟩ := List.mem_filterMap.mp hx
  exact quick_sort_subset ds (List.mem_of_getElem? hk)


def quickScreen (d : Nat) (ws : List Wire) := quickGuard (ws.map Wire.value) d

theorem quick_sound : Sound quickScreen := by
  intro d ws nd bound possible
  have slow := screen_sound d ws nd bound possible
  have codes : (ws.map pack).map Wire.value=ws.map Prod.fst := by simp [List.map_map,Function.comp_def,pack]
  unfold quickScreen quickGuard
  unfold gateScreen guard at slow
  rw [codes] at slow ⊢
  simp only [List.length_map] at slow ⊢
  apply permitsQuick_of_slow _ _ (quick_axis_subset _) _ _ slow
  · intro z hz
    obtain ⟨k,_,ix,_,_⟩ := digit_at (by simp) hz
    simp [ix]
  · intro z hz
    obtain ⟨k,hk,_,w,_⟩ := digit_at (by simp) hz
    rw [(prepare_fields _ hz).1, source_eq,w]
    exact Packed.cover_bound (bound _ (List.getElem_mem hk))

end Live3210.SubsetCheck
namespace Live3210.SubsetCheck
open Search Ordered Blocks

def cellsDup (ws : List Wire) :=
  (ws.foldl (fun (p : Nat×Nat) z => (p.1 ||| z.cells, p.2 ||| (p.1 &&& z.cells))) (0,0)).2

def projectWire (dup : Nat) (z : Wire × Nat) : Digit :=
  let p := z.1.cells &&& ((full 144) ^^^ dup)
  ⟨z.1.value,1 <<< z.2,0,z.1.cells,rowsOf p,colsOf p⟩

def wireDigits (ws : List Wire) := ws.zipIdx.map (projectWire (cellsDup ws))

private theorem dup_packs (ws : List Signal) : cellsDup (ws.map pack) = duplicate (ws.map Prod.fst) := by
  simp only [cellsDup,duplicate,List.foldl_map,pack,coverStep,source_eq]

private theorem digits_packs (ws : List Signal) : wireDigits (ws.map pack) =
    prepare (ws.map Prod.fst) (List.replicate ws.length 0) := by
  unfold wireDigits
  rw [dup_packs]
  change _ = (((ws.map Prod.fst).zip (List.replicate ws.length 0)).zipIdx.map _)
  generalize constant : duplicate (ws.map Prod.fst)=v
  have aux (xs : List Signal) (i : Nat) :
    ((xs.map pack).zipIdx i).map (projectWire v) =
      ((((xs.map Prod.fst).zip (List.replicate xs.length 0)).zipIdx i).map fun ((word,mem),k) =>
        let c := sourceCode word
        let pr := c &&& ((full 144) ^^^ v)
        (⟨word,1 <<< k,mem,c,rowsOf pr,colsOf pr⟩ : Digit)) := by
    induction xs generalizing i with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons,List.length_cons,List.replicate_succ,List.zip_cons_cons,List.zipIdx_cons]
      rw [ih]
      simp [projectWire,pack,source_eq]
  subst v
  exact aux ws 0

def wireScreen (d : Nat) (ws : List Wire) := permitsQuick (wireDigits ws) (d+1-ws.length)

theorem wire_sound : Sound wireScreen := by
  intro d ws nd bound possible
  have ok := quick_sound d ws nd bound possible
  unfold wireScreen
  rw [digits_packs]
  unfold quickScreen quickGuard at ok
  simpa only [List.length_map,List.map_map,Function.comp_def,pack] using ok

end Live3210.SubsetCheck
namespace Live3210.Search
open Ordered

def firstPair (screen : Screen) (n i j : Nat) : Nat :=
  let ws := (starts n).map pack
  let x := ws.getD i (pack (0,0))
  let y := ws.getD j (pack (0,0))
  let prior := (ws.take i).reverse
  let middle := ((ws.drop (i+1)).take (j-(i+1))).reverse
  let others := prior ++ middle ++ ws.drop (j+1)
  options (screened screen 4 13) ws others (ws.length-1) 14 0 0 x y

theorem split9 (screen : Screen) (beginning : screen 14 ((starts 9).map pack)=true) :
    screened screen 5 14 ((starts 9).map pack) 0 0 = ((firstPair screen 9 0 1 + (firstPair screen 9 0 2 + (firstPair screen 9 0 3 + (firstPair screen 9 0 4 + (firstPair screen 9 0 5 + (firstPair screen 9 0 6 + (firstPair screen 9 0 7 + (firstPair screen 9 0 8 + 0)))))))) + ((firstPair screen 9 1 2 + (firstPair screen 9 1 3 + (firstPair screen 9 1 4 + (firstPair screen 9 1 5 + (firstPair screen 9 1 6 + (firstPair screen 9 1 7 + (firstPair screen 9 1 8 + 0))))))) + ((firstPair screen 9 2 3 + (firstPair screen 9 2 4 + (firstPair screen 9 2 5 + (firstPair screen 9 2 6 + (firstPair screen 9 2 7 + (firstPair screen 9 2 8 + 0)))))) + ((firstPair screen 9 3 4 + (firstPair screen 9 3 5 + (firstPair screen 9 3 6 + (firstPair screen 9 3 7 + (firstPair screen 9 3 8 + 0))))) + ((firstPair screen 9 4 5 + (firstPair screen 9 4 6 + (firstPair screen 9 4 7 + (firstPair screen 9 4 8 + 0)))) + ((firstPair screen 9 5 6 + (firstPair screen 9 5 7 + (firstPair screen 9 5 8 + 0))) + ((firstPair screen 9 6 7 + (firstPair screen 9 6 8 + 0)) + ((firstPair screen 9 7 8 + 0) + (0 + 0))))))))) := by
  rw [screened,ite_eq_left beginning]
  have absent : (((starts 9).map pack).any (fun w => w.value == 4095)) ≠ true := by decide +kernel
  rw [ite_eq_right absent]
  rfl

theorem split10 (screen : Screen) (beginning : screen 14 ((starts 10).map pack)=true) :
    screened screen 5 14 ((starts 10).map pack) 0 0 = ((firstPair screen 10 0 1 + (firstPair screen 10 0 2 + (firstPair screen 10 0 3 + (firstPair screen 10 0 4 + (firstPair screen 10 0 5 + (firstPair screen 10 0 6 + (firstPair screen 10 0 7 + (firstPair screen 10 0 8 + (firstPair screen 10 0 9 + 0))))))))) + ((firstPair screen 10 1 2 + (firstPair screen 10 1 3 + (firstPair screen 10 1 4 + (firstPair screen 10 1 5 + (firstPair screen 10 1 6 + (firstPair screen 10 1 7 + (firstPair screen 10 1 8 + (firstPair screen 10 1 9 + 0)))))))) + ((firstPair screen 10 2 3 + (firstPair screen 10 2 4 + (firstPair screen 10 2 5 + (firstPair screen 10 2 6 + (firstPair screen 10 2 7 + (firstPair screen 10 2 8 + (firstPair screen 10 2 9 + 0))))))) + ((firstPair screen 10 3 4 + (firstPair screen 10 3 5 + (firstPair screen 10 3 6 + (firstPair screen 10 3 7 + (firstPair screen 10 3 8 + (firstPair screen 10 3 9 + 0)))))) + ((firstPair screen 10 4 5 + (firstPair screen 10 4 6 + (firstPair screen 10 4 7 + (firstPair screen 10 4 8 + (firstPair screen 10 4 9 + 0))))) + ((firstPair screen 10 5 6 + (firstPair screen 10 5 7 + (firstPair screen 10 5 8 + (firstPair screen 10 5 9 + 0)))) + ((firstPair screen 10 6 7 + (firstPair screen 10 6 8 + (firstPair screen 10 6 9 + 0))) + ((firstPair screen 10 7 8 + (firstPair screen 10 7 9 + 0)) + ((firstPair screen 10 8 9 + 0) + (0 + 0)))))))))) := by
  rw [screened,ite_eq_left beginning]
  have absent : (((starts 10).map pack).any (fun w => w.value == 4095)) ≠ true := by decide +kernel
  rw [ite_eq_right absent]
  rfl

end Live3210.Search
namespace Live3210.Search

def firstWith (f : Callback) (n i j : Nat) : Nat :=
  let ws := (starts n).map pack
  let x := ws.getD i (pack (0,0))
  let y := ws.getD j (pack (0,0))
  let rest := (ws.take i).reverse ++ ((ws.drop (i+1)).take (j-(i+1))).reverse ++ ws.drop (j+1)
  options f ws rest (ws.length-1) 14 0 0 x y

def bucket (x y : Wire) : Nat := ((x.value*12347+y.value*1777)%65521)%16

def bandNext (f : Callback) (ws : List Wire) (d l w lo hi : Nat) : Nat :=
  scanPairs (fun x y rest => if lo≤bucket x y ∧ bucket x y<hi then
    options f ws rest (ws.length-1) d l w x y else 0) [] ws

def bandState (screen : Screen) (h lo hi : Nat) : Callback := fun ws l w =>
  if screen 13 ws then
    if ws.any (fun z => z.value==4095) then (if lo=0 ∧ 0<hi then 1 else 0)
    else bandNext (screened screen h 12) ws 13 l w lo hi
  else 0

def bandPair (screen : Screen) (h n i j lo hi : Nat) :=
  firstWith (bandState screen h lo hi) n i j

private theorem branch_linear (f g : Callback) (z x y : Wire) (ws : List Wire) (k d u : Nat) (c : Choice) :
    branch (fun vs l w => f vs l w+g vs l w) z x y ws k d u c =
      branch f z x y ws k d u c + branch g z x y ws k d u c := by
  unfold branch; split <;> rfl

private theorem trial_linear (f g : Callback) (ws rest : List Wire) (k d lim lw : Nat) (x y : Wire)
    (u w rank : Nat) :
    trial (fun vs l w => f vs l w+g vs l w) ws rest k d lim lw x y u w rank =
      trial f ws rest k d lim lw x y u w rank + trial g ws rest k d lim lw x y u w rank := by
  unfold trial; split
  · rfl
  · simp only [branch_linear]; omega

private theorem options_linear (f g : Callback) (ws rest : List Wire) (k d lim w : Nat) (x y : Wire) :
    options (fun vs l w => f vs l w+g vs l w) ws rest k d lim w x y =
      options f ws rest k d lim w x y + options g ws rest k d lim w x y := by
  simp only [options]; split
  · rfl
  · simp only [trial_linear]; omega

private theorem right_linear {α : Type} (f g : α → α → List α → Nat) (x : α) (pre seen ys : List α) :
    scanRight (fun x y r => f x y r + g x y r) x pre seen ys =
      scanRight f x pre seen ys + scanRight g x pre seen ys := by
  induction ys generalizing seen with
  | nil => rfl
  | cons y ys ih => simp only [scanRight,ih]; omega

private theorem pairs_linear {α : Type} (f g : α → α → List α → Nat) (pre ys : List α) :
    scanPairs (fun x y r => f x y r + g x y r) pre ys =
      scanPairs f pre ys + scanPairs g pre ys := by
  induction ys generalizing pre with
  | nil => rfl
  | cons y ys ih => simp only [scanPairs,right_linear,ih]; omega

private theorem split_interval (k lo mid hi v : Nat) (hm : lo≤mid) (hn : mid≤hi) :
    (if lo≤k ∧ k<hi then v else 0) =
      (if lo≤k ∧ k<mid then v else 0) + (if mid≤k ∧ k<hi then v else 0) := by
  split_ifs <;> omega

private theorem bandNext_split (f : Callback) (ws : List Wire) (d l w lo mid hi : Nat)
    (hm : lo≤mid) (hn : mid≤hi) :
    bandNext f ws d l w lo hi = bandNext f ws d l w lo mid + bandNext f ws d l w mid hi := by
  unfold bandNext
  rw [← pairs_linear]
  apply congrArg (fun g => scanPairs g [] ws)
  funext x y r
  exact split_interval _ _ _ _ _ hm hn

private theorem bandState_split (screen : Screen) (h lo mid hi : Nat) (hm : lo≤mid) (hn : mid≤hi) :
    bandState screen h lo hi = fun vs l w => bandState screen h lo mid vs l w + bandState screen h mid hi vs l w := by
  funext vs l w
  simp only [bandState]
  split
  · split
    · split_ifs <;> omega
    · exact bandNext_split _ _ _ _ _ _ _ _ hm hn
  · rfl

theorem bandPair_split (screen : Screen) (h n i j lo mid hi : Nat) (hm : lo≤mid) (hn : mid≤hi) :
    bandPair screen h n i j lo hi = bandPair screen h n i j lo mid + bandPair screen h n i j mid hi := by
  unfold bandPair
  rw [bandState_split _ _ _ mid _ hm hn]
  unfold firstWith
  exact options_linear ..

private theorem bandState_all (screen : Screen) (h : Nat) :
    bandState screen h 0 16 = screened screen (h+1) 13 := by
  funext vs l w
  simp only [bandState,screened,true_and, Nat.reduceLT, ite_true]
  by_cases yes : screen 13 vs=true
  · rw [ite_eq_left yes,ite_eq_left yes]
    by_cases term : vs.any (fun z => z.value == 4095)=true
    · simp [term]
    · rw [ite_eq_right term,ite_eq_right term]
      unfold bandNext next
      congr 1
      funext x y r
      have b : bucket x y<16 := Nat.mod_lt _ (by decide)
      simp [b]
  · rw [ite_eq_right yes,ite_eq_right yes]

theorem firstPair_all (screen : Screen) (n i j : Nat) : firstPair screen n i j=bandPair screen 3 n i j 0 16 := by
  unfold bandPair
  rw [bandState_all]
  rfl

end Live3210.Search
namespace Live3210.Search
private abbrev cg := SubsetCheck.wireScreen

private theorem glueBand {n i j lo mid hi : Nat}
    (left : bandPair cg 3 n i j lo mid=0) (right : bandPair cg 3 n i j mid hi=0)
    (a : lo≤mid) (b : mid≤hi) : bandPair cg 3 n i j lo hi=0 := by
  rw [bandPair_split _ _ _ _ _ _ mid _ a b,left,right]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_1 : firstPair cg 9 0 1=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_2x0 : bandPair cg 3 9 0 2 0 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_2x1 : bandPair cg 3 9 0 2 9 16=0 := by decide +kernel
private theorem p9_0_2 : firstPair cg 9 0 2=0 := by
  rw [firstPair_all]
  exact (glueBand p9_0_2x0 p9_0_2x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_3x0 : bandPair cg 3 9 0 3 0 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_3x1 : bandPair cg 3 9 0 3 9 16=0 := by decide +kernel
private theorem p9_0_3 : firstPair cg 9 0 3=0 := by
  rw [firstPair_all]
  exact (glueBand p9_0_3x0 p9_0_3x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_4x0 : bandPair cg 3 9 0 4 0 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_4x1 : bandPair cg 3 9 0 4 9 16=0 := by decide +kernel
private theorem p9_0_4 : firstPair cg 9 0 4=0 := by
  rw [firstPair_all]
  exact (glueBand p9_0_4x0 p9_0_4x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_5 : firstPair cg 9 0 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_6 : firstPair cg 9 0 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_7 : firstPair cg 9 0 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_0_8 : firstPair cg 9 0 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_2x0 : bandPair cg 3 9 1 2 0 11=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_2x1 : bandPair cg 3 9 1 2 11 16=0 := by decide +kernel
private theorem p9_1_2 : firstPair cg 9 1 2=0 := by
  rw [firstPair_all]
  exact (glueBand p9_1_2x0 p9_1_2x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_3x0 : bandPair cg 3 9 1 3 0 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_3x1 : bandPair cg 3 9 1 3 7 16=0 := by decide +kernel
private theorem p9_1_3 : firstPair cg 9 1 3=0 := by
  rw [firstPair_all]
  exact (glueBand p9_1_3x0 p9_1_3x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_4 : firstPair cg 9 1 4=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_5x0 : bandPair cg 3 9 1 5 0 12=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_5x1 : bandPair cg 3 9 1 5 12 16=0 := by decide +kernel
private theorem p9_1_5 : firstPair cg 9 1 5=0 := by
  rw [firstPair_all]
  exact (glueBand p9_1_5x0 p9_1_5x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_6x0 : bandPair cg 3 9 1 6 0 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_6x1 : bandPair cg 3 9 1 6 6 16=0 := by decide +kernel
private theorem p9_1_6 : firstPair cg 9 1 6=0 := by
  rw [firstPair_all]
  exact (glueBand p9_1_6x0 p9_1_6x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_7 : firstPair cg 9 1 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_1_8 : firstPair cg 9 1 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_3 : firstPair cg 9 2 3=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_4 : firstPair cg 9 2 4=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_5x0 : bandPair cg 3 9 2 5 0 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_5x1 : bandPair cg 3 9 2 5 9 16=0 := by decide +kernel
private theorem p9_2_5 : firstPair cg 9 2 5=0 := by
  rw [firstPair_all]
  exact (glueBand p9_2_5x0 p9_2_5x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_6 : firstPair cg 9 2 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_7x0 : bandPair cg 3 9 2 7 0 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_7x1 : bandPair cg 3 9 2 7 9 16=0 := by decide +kernel
private theorem p9_2_7 : firstPair cg 9 2 7=0 := by
  rw [firstPair_all]
  exact (glueBand p9_2_7x0 p9_2_7x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_2_8 : firstPair cg 9 2 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_4x0 : bandPair cg 3 9 3 4 0 11=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_4x1 : bandPair cg 3 9 3 4 11 16=0 := by decide +kernel
private theorem p9_3_4 : firstPair cg 9 3 4=0 := by
  rw [firstPair_all]
  exact (glueBand p9_3_4x0 p9_3_4x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_5x0 : bandPair cg 3 9 3 5 0 2=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_5x1 : bandPair cg 3 9 3 5 2 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_5x2 : bandPair cg 3 9 3 5 8 16=0 := by decide +kernel
private theorem p9_3_5 : firstPair cg 9 3 5=0 := by
  rw [firstPair_all]
  exact (glueBand p9_3_5x0 (glueBand p9_3_5x1 p9_3_5x2 (by decide) (by decide)) (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_6 : firstPair cg 9 3 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_7 : firstPair cg 9 3 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_3_8 : firstPair cg 9 3 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_4_5 : firstPair cg 9 4 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_4_6 : firstPair cg 9 4 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_4_7 : firstPair cg 9 4 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_4_8 : firstPair cg 9 4 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_5_6 : firstPair cg 9 5 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_5_7x0 : bandPair cg 3 9 5 7 0 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_5_7x1 : bandPair cg 3 9 5 7 6 16=0 := by decide +kernel
private theorem p9_5_7 : firstPair cg 9 5 7=0 := by
  rw [firstPair_all]
  exact (glueBand p9_5_7x0 p9_5_7x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_5_8 : firstPair cg 9 5 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_6_7 : firstPair cg 9 6 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_6_8x0 : bandPair cg 3 9 6 8 0 10=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_6_8x1 : bandPair cg 3 9 6 8 10 16=0 := by decide +kernel
private theorem p9_6_8 : firstPair cg 9 6 8=0 := by
  rw [firstPair_all]
  exact (glueBand p9_6_8x0 p9_6_8x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p9_7_8 : firstPair cg 9 7 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_1 : firstPair cg 10 0 1=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_2 : firstPair cg 10 0 2=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_3 : firstPair cg 10 0 3=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_4 : firstPair cg 10 0 4=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_5 : firstPair cg 10 0 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_6x0 : bandPair cg 3 10 0 6 0 14=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_6x1 : bandPair cg 3 10 0 6 14 16=0 := by decide +kernel
private theorem p10_0_6 : firstPair cg 10 0 6=0 := by
  rw [firstPair_all]
  exact (glueBand p10_0_6x0 p10_0_6x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_7 : firstPair cg 10 0 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_8 : firstPair cg 10 0 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_0_9 : firstPair cg 10 0 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_2 : firstPair cg 10 1 2=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_3 : firstPair cg 10 1 3=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_4 : firstPair cg 10 1 4=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_5 : firstPair cg 10 1 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_6 : firstPair cg 10 1 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_7 : firstPair cg 10 1 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_8 : firstPair cg 10 1 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_1_9 : firstPair cg 10 1 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_3 : firstPair cg 10 2 3=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_4 : firstPair cg 10 2 4=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_5 : firstPair cg 10 2 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_6 : firstPair cg 10 2 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_7 : firstPair cg 10 2 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_8 : firstPair cg 10 2 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_2_9 : firstPair cg 10 2 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_4 : firstPair cg 10 3 4=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_5 : firstPair cg 10 3 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_6x0 : bandPair cg 3 10 3 6 0 15=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_6x1 : bandPair cg 3 10 3 6 15 16=0 := by decide +kernel
private theorem p10_3_6 : firstPair cg 10 3 6=0 := by
  rw [firstPair_all]
  exact (glueBand p10_3_6x0 p10_3_6x1 (by decide) (by decide))
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_7 : firstPair cg 10 3 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_8 : firstPair cg 10 3 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_3_9 : firstPair cg 10 3 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_4_5 : firstPair cg 10 4 5=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_4_6 : firstPair cg 10 4 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_4_7 : firstPair cg 10 4 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_4_8 : firstPair cg 10 4 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_4_9 : firstPair cg 10 4 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_5_6 : firstPair cg 10 5 6=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_5_7 : firstPair cg 10 5 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_5_8 : firstPair cg 10 5 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_5_9 : firstPair cg 10 5 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_6_7 : firstPair cg 10 6 7=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_6_8 : firstPair cg 10 6 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_6_9 : firstPair cg 10 6 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_7_8 : firstPair cg 10 7 8=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_7_9 : firstPair cg 10 7 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem p10_8_9 : firstPair cg 10 8 9=0 := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem splitClosure : checkedRun cg 5=0 := by
  rw [checkedRun,split9 _ (by decide +kernel),split10 _ (by decide +kernel)]
  simp only [p9_0_1, p9_0_2, p9_0_3, p9_0_4, p9_0_5, p9_0_6, p9_0_7, p9_0_8, p9_1_2, p9_1_3, p9_1_4, p9_1_5, p9_1_6, p9_1_7, p9_1_8, p9_2_3, p9_2_4, p9_2_5, p9_2_6, p9_2_7, p9_2_8, p9_3_4, p9_3_5, p9_3_6, p9_3_7, p9_3_8, p9_4_5, p9_4_6, p9_4_7, p9_4_8, p9_5_6, p9_5_7, p9_5_8, p9_6_7, p9_6_8, p9_7_8, p10_0_1, p10_0_2, p10_0_3, p10_0_4, p10_0_5, p10_0_6, p10_0_7, p10_0_8, p10_0_9, p10_1_2, p10_1_3, p10_1_4, p10_1_5, p10_1_6, p10_1_7, p10_1_8, p10_1_9, p10_2_3, p10_2_4, p10_2_5, p10_2_6, p10_2_7, p10_2_8, p10_2_9, p10_3_4, p10_3_5, p10_3_6, p10_3_7, p10_3_8, p10_3_9, p10_4_5, p10_4_6, p10_4_7, p10_4_8, p10_4_9, p10_5_6, p10_5_7, p10_5_8, p10_5_9, p10_6_7, p10_6_8, p10_6_9, p10_7_8, p10_7_9, p10_8_9, Nat.zero_add]
end Live3210.Search
end PEqualNP.Outside.L_meta_4312

namespace PEqualNP.Outside.L_meta_4312

private theorem base_unsat : have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) := by
  dsimp only
  intro sat
  obtain ⟨p,k,len,hit⟩ := PEqualNP.Outside.L_meta_4312.VerifiedDecoder3210 sat
  have pos := PEqualNP.Outside.L_meta_4312.Live3210.Search.program_checked
    PEqualNP.Outside.L_meta_4312.Live3210.SubsetCheck.wireScreen PEqualNP.Outside.L_meta_4312.Live3210.SubsetCheck.wire_sound 5 p k len hit
  rw [PEqualNP.Outside.L_meta_4312.Live3210.Search.splitClosure] at pos
  exact (Nat.lt_irrefl 0) pos

end PEqualNP.Outside.L_meta_4312

theorem PEqualNP.Outside.L_meta_4312 : have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2) ++ [[PEqualNP.Defs.LratEncoding.P (PEqualNP.Defs.LratEncoding.ix (10 : ℕ) (14 : ℕ) (0 : ℕ) (13 : ℕ) (0 : ℕ))], [PEqualNP.Defs.LratEncoding.P (PEqualNP.Defs.LratEncoding.ix (10 : ℕ) (14 : ℕ) (2 : ℕ) (13 : ℕ) (22 : ℕ))], List.map (fun (x3 : ℕ) => PEqualNP.Defs.LratEncoding.P (PEqualNP.Defs.LratEncoding.ix (10 : ℕ) (14 : ℕ) (1 : ℕ) (13 : ℕ) ((10 : ℕ) + x3))) (List.range (12 : ℕ))]) := by
  dsimp only
  rintro ⟨assignment, satisfies⟩
  apply PEqualNP.Outside.L_meta_4312.base_unsat
  exact ⟨assignment, fun clause hClause => satisfies clause (List.mem_append_left _ hClause)⟩
