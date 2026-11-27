import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2732_3
 (canon :
  let F := fun x : Fin 14 → Bool => decide (∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true)
  let score := fun a b c d : ℕ => (15*min a b+max a b)*225+15*min c d+max c d
  let ext := fun (p : Equiv.Perm (Fin 14)) (i : Fin 15) => if i.val < 14 then (p (Fin.ofNat 14 i.val)).val else 14
  ∀ k : Fin 65,
    let t := (([[226,227,228,232,233,234,236,239,258,259,260,262,263],[264,266,267,269,277,278,281,284,338,341,344,354,355],[356,359,402,404,1576,1577,1582,1583,1584,1589,1592,1593,1598],[1599,1601,1604,1609,1611,1614,1617,1619,2026,2027,2032,2034,2036],[2039,2042,2043,2045,2047,2048,2051,2053,2054,2058,2066,2067,2069]] : List (List ℕ)).getD (k.val/13) []).getD (k.val % 13) 0
    let b := Fin.ofNat 14 (t/225)
    let c := Fin.ofNat 15 ((t % 225)/15)
    let d := Fin.ofNat 15 (t % 15)
    0<b ∧ c<d ∧ ∀ p : Equiv.Perm (Fin 14), (∀ x,F (x ∘ p)=F x) →
      score 0 b.val c.val d.val ≤ score (p 0).val (p b).val (ext p c) (ext p d))
 (decode :
  let w := ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ)
  let step := fun (w : List ℕ) (t : ℕ) => w++[if t<4096 then w.getD (t % 64) 0 &&& w.getD ((t/64) % 64) 0 else w.getD (t % 64) 0 ||| w.getD ((t/64) % 64) 0]
  let gate := fun t : ℕ => (⟨if t<4096 then GateOp.and else GateOp.or,[t % 64,(t/64) % 64]⟩ : Gate)
  let F := fun x : Fin 14 → Bool => decide (∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true)
  ∀ P : List ℕ, (P.foldl step w).getD (13+P.length) 0=2097151 →
    ∀ x : Fin 14 → Bool, (Circuit.mk (P.map gate) (13+P.length)).eval (List.ofFn x)=F x)
 (search :
  let w := ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ)
  let step := fun (w : List ℕ) (t : ℕ) => w++[if t<4096 then w.getD (t % 64) 0 &&& w.getD ((t/64) % 64) 0 else w.getD (t % 64) 0 ||| w.getD ((t/64) % 64) 0]
  let pack := fun (a b : ℕ) (o : Bool) => a+64*b+(if o then 4096 else 0)
  ∃ k : Fin 65, ∃ u v : Bool, ∃ p : List (Fin 8192), p.length≤24 ∧
    let t := (([[226,227,228,232,233,234,236,239,258,259,260,262,263],[264,266,267,269,277,278,281,284,338,341,344,354,355],[356,359,402,404,1576,1577,1582,1583,1584,1589,1592,1593,1598],[1599,1601,1604,1609,1611,1614,1617,1619,2026,2027,2032,2034,2036],[2039,2042,2043,2045,2047,2048,2051,2053,2054,2058,2066,2067,2069]] : List (List ℕ)).getD (k.val/13) []).getD (k.val % 13) 0
    let P := pack 0 (Fin.ofNat 14 (t/225)).val u :: pack (Fin.ofNat 15 ((t % 225)/15)).val (Fin.ofNat 15 (t % 15)).val v :: p.map Fin.val
    (P.foldl step w).getD (13+P.length) 0=2097151) :
have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); have x3 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x3 x4 x5 x6 : ℕ) => ((15 : ℕ) * Min.min x3 x4 + Max.max x3 x4) * (225 : ℕ) + ((15 : ℕ) * Min.min x5 x6 + Max.max x5 x6); have x4 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x4 : Equiv.Perm (Fin (14 : ℕ))) (x5 : Fin (15 : ℕ)) => if ↑x5 < (14 : ℕ) then ↑(x4 (Fin.ofNat (14 : ℕ) ↑x5)) else (14 : ℕ); ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)) (x7 : Fin (15 : ℕ)) (x8 : Fin (15 : ℕ)) (x9 : PEqualNP.CircuitLowerBounds.GateOp) (x10 : PEqualNP.CircuitLowerBounds.GateOp) (x11 : PEqualNP.CircuitLowerBounds.Circuit),   x5 < x6 ∧     x7 < x8 ∧       (x9 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x9 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧         (x10 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧           (∀ (x12 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x13 : Fin (14 : ℕ) → Bool), x2 (x13 ∘ ⇑x12) = x2 x13) → x3 ↑x5 ↑x6 ↑x7 ↑x8 ≤ x3 (↑(x12 x5)) (↑(x12 x6)) (x4 x12 x7) (x4 x12 x8)) ∧             PEqualNP.MetaComplexity.Monotone2 x11 ∧               x11.size ≤ (24 : ℕ) ∧                 ∀ (x12 : Fin (14 : ℕ) → Bool),                   have x13 : List Bool := List.ofFn x12 ++ [x9.eval [x12 x5, x12 x6]];                   x11.eval (x13 ++ [x10.eval [x13.getD (↑x7) Bool.false, x13.getD (↑x8) Bool.false]]) = x2 x12 := by
  dsimp only
  let F := fun x : Fin 14 → Bool => decide (∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true)
  let edges : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let G := fun x : Fin 14 → Bool => decide (∃ a b : Fin 14, (a.val,b.val)∈edges ∧ x a=true ∧ x b=true)
  have ef : ∀ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val=true ↔ (a.val,b.val)∈edges := by decide +kernel
  have agree (x : Fin 14 → Bool) : F x=G x := by simp only [F,G,ef]
  obtain ⟨k,u,v,p,hp,check⟩ := search
  let t := (([[226,227,228,232,233,234,236,239,258,259,260,262,263],[264,266,267,269,277,278,281,284,338,341,344,354,355],[356,359,402,404,1576,1577,1582,1583,1584,1589,1592,1593,1598],[1599,1601,1604,1609,1611,1614,1617,1619,2026,2027,2032,2034,2036],[2039,2042,2043,2045,2047,2048,2051,2053,2054,2058,2066,2067,2069]] : List (List ℕ)).getD (k.val/13) []).getD (k.val % 13) 0
  let b := Fin.ofNat 14 (t/225)
  let c := Fin.ofNat 15 ((t % 225)/15)
  let d := Fin.ofNat 15 (t % 15)
  let pack := fun (a b : ℕ) (o : Bool) => a+64*b+(if o then 4096 else 0)
  let gate := fun t : ℕ => (⟨if t<4096 then GateOp.and else GateOp.or,[t % 64,(t/64) % 64]⟩ : Gate)
  let tail := p.map Fin.val
  let P := pack 0 b.val u :: pack c.val d.val v :: tail
  let op := fun x : Bool => if x then GateOp.or else GateOp.and
  let out := Circuit.mk (tail.map gate) (15+tail.length)
  have enc (a b : ℕ) (o : Bool) (ha : a<64) (hb : b<64) : gate (pack a b o)=⟨op o,[a,b]⟩ := by
    cases o
    · have h : a+64*b<4096 := by omega
      have h1 : (a+64*b) % 64=a := by omega
      have h2 : (a+64*b)/64 % 64=b := by omega
      simp [gate,pack,op,h,h1,h2]
    · have h : ¬ a+64*b+4096<4096 := by omega
      have h1 : (a+64*b+4096) % 64=a := by omega
      have h2 : (a+64*b+4096)/64 % 64=b := by omega
      simp [gate,pack,op,h,h1,h2]
  have opOK (f : Bool) : op f=GateOp.and ∨ op f=GateOp.or := by cases f <;> simp [op]
  obtain ⟨hb,hcd,hcan⟩ := canon k
  refine ⟨0,b,c,d,op u,op v,out,hb,hcd,opOK _,opOK _,?_,?_,?_,?_⟩
  · intro σ hf
    have hf' : ∀ x,F (x ∘ σ)=F x := by
      intro x
      rw [agree,agree]
      exact hf x
    let score := fun a b c d : ℕ => (15*min a b+max a b)*225+15*min c d+max c d
    let ext := fun (p : Equiv.Perm (Fin 14)) (i : Fin 15) => if i.val < 14 then (p (Fin.ofNat 14 i.val)).val else 14
    have hc : score 0 b.val c.val d.val ≤ score (σ 0).val (σ b).val (ext σ c) (ext σ d) := hcan σ hf'
    change (15*min 0 b.val+max 0 b.val)*225+(15*min c.val d.val+max c.val d.val) ≤
      (15*min (σ 0).val (σ b).val+max (σ 0).val (σ b).val)*225+
        (15*min (ext σ c) (ext σ d)+max (ext σ c) (ext σ d))
    simpa only [score,Nat.add_assoc] using hc
  · intro g hg
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hg
    by_cases h : z<4096 <;> simp [gate,h]
  · change (tail.map gate).length≤24
    simpa [tail] using hp
  · intro x
    have ev := decode P check x
    change (Circuit.mk (P.map gate) (13+P.length)).eval (List.ofFn x)=F x at ev
    have el : 13+P.length=15+tail.length := by simp [P];omega
    rw [el] at ev
    change (Circuit.mk (gate (pack 0 b.val u) :: gate (pack c.val d.val v) :: tail.map gate) (15+tail.length)).eval (List.ofFn x)=F x at ev
    rw [enc 0 b.val u (by decide) (by have:=b.isLt;omega),enc c.val d.val v (by have:=c.isLt;omega) (by have:=d.isLt;omega)] at ev
    let w := List.ofFn x
    let pref := w++[(op u).eval [w.getD 0 false,w.getD b.val false]]
    change out.eval (pref++[(op v).eval [pref.getD c.val false,pref.getD d.val false]])=F x at ev
    have get (i : Fin 14) : w.getD i.val false=x i := by
      rw [List.getD_eq_getElem _ _ (by simp [w]),List.getElem_ofFn]
    have eq : pref=w++[(op u).eval [x 0,x b]] := by rw [←get 0,←get b];rfl
    rw [eq,agree] at ev
    exact ev
