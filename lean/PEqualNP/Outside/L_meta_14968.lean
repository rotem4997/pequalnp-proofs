import PEqualNP.Defs

-- Projection and clique certificate adapted from L-meta-11761.

namespace PEqualNP.Outside.L_meta_14968.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7]
def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [4,5]⟩,
  ⟨.or, [0,1]⟩,
  ⟨.and, [8,9]⟩,
  ⟨.or, [2,4]⟩,
  ⟨.or, [9,11]⟩,
  ⟨.and, [6,12]⟩,
  ⟨.or, [3,5]⟩,
  ⟨.or, [2,14]⟩,
  ⟨.or, [0,15]⟩,
  ⟨.and, [7,16]⟩,
  ⟨.or, [10,13]⟩,
  ⟨.or, [18,17]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,19⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 12 ≤ gs.length) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 19, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_14968.Frame

namespace PEqualNP.Outside.L_meta_14968.Reduce
variable {m : Nat}
def canon (w : BitVec (m+1)) := if w.getLsbD 0 then ~~~w else w
def signed (d : Bool) (w : BitVec (m+1)) := if d then ~~~w else w
def gate (s t : Bool) (a b : BitVec (m+1)) := canon (signed s a &&& signed t b)
def Path (goal : BitVec (m+1)) (k : Nat) (S : Finset (BitVec (m+1))) : Prop :=
  ∀ P : Nat → Finset (BitVec (m+1)) → Prop, P 0 {goal} →
    (∀ {k a b U} (s t : Bool), a ≠ b → gate s t a b ∉ insert a (insert b U) →
      gate s t a b ≠ 0 → P k (insert (gate s t a b) U) → P (k+1) (insert a (insert b U))) →
    P k S
theorem Path.done {g : BitVec (m+1)} : Path g 0 {g} := fun _ d _ => d
theorem Path.binary {g : BitVec (m+1)} {k a b U} (s t : Bool) (ne : a ≠ b)
    (fresh : gate s t a b ∉ insert a (insert b U)) (proper : gate s t a b ≠ 0)
    (tail : Path g k (insert (gate s t a b) U)) : Path g (k+1) (insert a (insert b U)) :=
  fun P d f => f s t ne fresh proper (tail P d f)
theorem canon_not (x : BitVec (m+1)) : canon (~~~x) = canon x := by
  unfold canon
  simp only [BitVec.getLsbD_not, Nat.zero_lt_succ,decide_true, Bool.true_and]
  cases x.getLsbD 0 <;> simp

theorem canon_canon (x : BitVec (m+1)) : canon (canon x) = canon x := by
  by_cases h : x.getLsbD 0 = true
  · rw [show canon x = ~~~x from if_pos h,canon_not,show canon x = ~~~x from if_pos h]
  · rw [show canon x = x from if_neg h]
    exact if_neg h

theorem sign_back (x : BitVec (m+1)) : signed (x.getLsbD 0) (canon x) = x := by
  unfold signed canon
  cases x.getLsbD 0 <;> simp

theorem canon_zero : canon (0 : BitVec (m+1)) = 0 := by simp [canon]
theorem gate_left_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t 0 x = 0 ∨ gate s t 0 x = canon x := by
  cases s with
  | false => exact Or.inl ((congrArg canon (BitVec.zero_and (x := signed t x))).trans canon_zero)
  | true =>
    cases t with
    | false => right; simp [gate,signed]
    | true => right; simp [gate,signed,canon_not]

theorem gate_right_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t x 0 = 0 ∨ gate s t x 0 = canon x := by
  rw [show gate s t x 0 = gate t s 0 x from congrArg canon (BitVec.and_comm ..)]
  exact gate_left_zero _ _ _

theorem gate_same (s t : Bool) (x : BitVec (m+1)) : gate s t x x = 0 ∨ gate s t x x = canon x := by
  cases s <;> cases t
  · exact Or.inr (congrArg canon (BitVec.and_self (x := x)))
  · exact Or.inl ((congrArg canon (BitVec.and_not_self x)).trans canon_zero)
  · exact Or.inl ((congrArg canon (BitVec.not_and_self x)).trans canon_zero)
  · exact Or.inr ((congrArg canon (BitVec.and_self (x := ~~~x))).trans (canon_not x))

variable {A : Type} [DecidableEq A] (pin : A → BitVec (m+1))
def avail (S : Finset A) := (S.image pin).erase 0
def lost (S : Finset A) := (S.filter fun x => pin x = 0).card
theorem avail_mem {S : Finset A} {x : BitVec (m+1)} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono {S T : Finset A} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases {S : Finset A} {c : A} {x : BitVec (m+1)} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (c : A) (S : Finset A) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,if_neg (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [if_pos ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,if_pos h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [if_neg (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,if_neg h]

theorem cost_skip (a b c : A) (U : Finset A) (fresh : c ∉ U)
    (both : pin a = 0 → pin b = 0 → pin c = 0) :
    lost pin (insert a (insert b U)) ≤ lost pin (insert c U) + 1 := by
  simp only [lost_insert]
  split_ifs <;> grind

def Proj (goal : BitVec (m+1)) (limit extra : Nat) (S : Finset A) : Prop :=
  ∃ k, k + lost pin S + extra ≤ limit ∧ ∃ T ⊆ avail pin S, Path goal k T

theorem proj_done (x : A) (nz : pin x ≠ 0) : Proj pin (pin x) 0 0 {x} := by
  refine ⟨0,?_,{pin x},?_,Path.done⟩ <;> simp [lost,avail] <;> exact nz
theorem proj_inv {g : BitVec (m+1)} {limit extra : Nat} (a c : A) (U : Finset A)
    (newc : c ∉ U) (eq : pin c = pin a) (tail : Proj pin g limit extra (insert c U)) :
    Proj pin g limit extra (insert a U) := by
  obtain ⟨k,hle,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,eq] at hle ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq'|old
    · exact (avail_mem pin).mpr ⟨((avail_mem pin).mp (sub hx)).1,a,by simp,(eq'.trans eq).symm⟩
    · exact avail_mono pin (Finset.subset_insert _ _) old

theorem proj_strong {g : BitVec (m+1)} {limit : Nat} (a b c : A) (U : Finset A)
    (newc : c ∉ U) (hc : pin c = 0) (one : pin a ≠ 0 ∨ pin b ≠ 0)
    (tail : Proj pin g limit 0 (insert c U)) : Proj pin g (limit+1) 1 (insert a (insert b U)) := by
  obtain ⟨k,le,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,hc] at le ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq|old
    · exact (((avail_mem pin).mp (sub hx)).1 (eq.trans hc)).elim
    · exact avail_mono pin (by intro _ mem; simp [mem]) old

theorem proj_bin {g : BitVec (m+1)} {b extra : Nat} (a x c : A) (U : Finset A)
    (can : ∀ v, canon (pin v) = pin v) (cnew : c ∉ U) (s t : Bool)
    (repr : pin c = gate s t (pin a) (pin x))
    (tail : Proj pin g b extra (insert c U)) : Proj pin g (b+1) extra (insert a (insert x U)) := by
  let prev := insert a (insert x U)
  obtain ⟨k,hle,T,sub,path⟩ := tail
  change k + lost pin (insert c U) + extra ≤ b at hle
  change T ⊆ avail pin (insert c U) at sub
  have both (ha : pin a = 0) (hx : pin x = 0) : pin c = 0 := by
    rw [repr,ha,hx]
    exact (gate_same s t 0).elim id (fun q => q.trans canon_zero)
  have skipcost := cost_skip pin a x c U cnew both
  have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
  by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
  · have nz := ((avail_mem pin).mp (sub useful.1)).1
    have df (v : A) (hv : v ∈ prev) : pin c ≠ pin v := by
      intro e
      exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
    have da := df a (by simp [prev])
    have dx := df x (by simp [prev])
    have ha : pin a ≠ 0 := by
      intro h
      have drop := gate_left_zero s t (pin x)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have hx : pin x ≠ 0 := by
      intro h
      have drop := gate_right_zero s t (pin a)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz da
    have distinct : pin a ≠ pin x := by
      intro e
      have drop := gate_same s t (pin x)
      rw [e] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have vcost : lost pin prev ≤ lost pin (insert c U) := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    let V := T.erase (pin c)
    have old (v : BitVec (m+1)) (hv : v ∈ V) : v ∈ avail pin U :=
      (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
    refine ⟨k+1,by change k+1+lost pin prev + extra ≤ b+1; omega,insert (pin a) (insert (pin x) V),?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨ha,a,by simp [prev],rfl⟩
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨hx,x,by simp [prev],rfl⟩
      exact liftU (old _ hv)
    · apply Path.binary s t distinct
      · rw [←repr]
        simp [V,da,dx]
      · rwa [←repr]
      · rwa [←repr,show insert (pin c) V = T from Finset.insert_erase useful.1]
  · refine ⟨k,by change k+lost pin (insert a (insert x U)) + extra ≤ b+1; omega,T,?_,path⟩
    intro v hv
    rcases avail_cases pin (sub hv) with rfl|old
    · by_contra miss
      exact useful ⟨hv,miss⟩
    · exact liftU old
end PEqualNP.Outside.L_meta_14968.Reduce

namespace PEqualNP.Outside.L_meta_14968

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 128
def ones : Word := BitVec.allOnes 128
def goal : Word := 0xaaaafeeefcc8
def roots : List Word := [0xf002cccccccc,0x800000000,0x2000000000,0x8000000000,0x20faaaaaaaa,0x800f0f0f0f0,0x2330ffff0000,0x8cc0ff00ff00]
def join (d : Bool) (a b : Word) : Word := if d then a ||| b else a &&& b

def Live (b n : Nat) (S : Finset Word) : Prop :=
  ∀ (P : Nat → Nat → Finset Word → Prop),
    P 0 0 {goal} →
    (∀ {i j : Nat} {a x : Word} {U : Finset Word} (d : Bool), a ≠ x →
      join d a x ∉ insert a (insert x U) → (join d a x ≠ 0 ∧ join d a x ≠ ones) →
      P i j (insert (join d a x) U) → P (i+1) j (insert a (insert x U))) →
    (∀ {i j : Nat} {a : Word} {U : Finset Word},
      ~~~a ∉ insert a U → (~~~a ≠ 0 ∧ ~~~a ≠ ones) →
      P i j (insert (~~~a) U) → P i (j+1) (insert a U)) →
    P b n S

theorem Live.done : Live 0 0 {goal} :=
  fun _ done _ _ => done

theorem Live.binary {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
    (fresh : join d a x ∉ insert a (insert x U))
    (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
    (tail : Live b n (insert (join d a x) U)) :
    Live (b+1) n (insert a (insert x U)) :=
  fun P done binary inversion => binary d ne fresh proper (tail P done binary inversion)

theorem Live.inversion {b n : Nat} {a : Word} {U : Finset Word}
    (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
    (tail : Live b n (insert (~~~a) U)) : Live b (n+1) (insert a U) :=
  fun P done binary inversion => inversion fresh proper (tail P done binary inversion)

theorem Live.recPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)),
      motive tail → motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)),
      motive tail → motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  let P (b n : Nat) (S : Finset Word) : Prop := ∃ p : Live b n S, motive p
  have result : P b n S := by
    apply h P
    · exact ⟨Live.done,done⟩
    · intro i j a x U d ne fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.binary d ne fresh proper p,binary d ne fresh proper p ih⟩
    · intro i j a U fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.inversion fresh proper p,inversion fresh proper p ih⟩
  obtain ⟨_,proof⟩ := result
  exact proof

theorem Live.casesPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)), motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)), motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  apply Live.recPlain (motive := @motive) done _ _ h
  · intro i j a x U d ne fresh proper tail _
    exact binary d ne fresh proper tail
  · intro i j a U fresh proper tail _
    exact inversion fresh proper tail

theorem goal_proper : goal ≠ 0 ∧ goal ≠ ones := by decide +kernel

def assignment (r : Fin 128) : Fin 8 → Bool := fun i =>
  if r.val < 32 then r.val.testBit (([1, 5, 5, 5, 0, 2, 4, 3] : List Nat).get i)
  else (([16, 17, 16, 18, 64, 68, 128, 136, 64, 80, 128, 160, 1, 65, 1, 129] : List Nat).getD (r.val-32) 0).testBit i.val
def readBit (r : Fin 128) (v : Word) := v.getLsbD r

@[local simp] theorem read_ones (r : Fin 128) : readBit r ones = true := by
  exact (BitVec.getLsbD_allOnes).trans (decide_eq_true r.isLt)

@[local simp] theorem read_zero (r : Fin 128) : readBit r 0 = false := by simp [readBit]

@[local simp] theorem ones_and (a : Word) : ones &&& a = a := BitVec.allOnes_and
@[local simp] theorem and_ones (a : Word) : a &&& ones = a := BitVec.and_allOnes
@[local simp] theorem ones_or (a : Word) : ones ||| a = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (a : Word) : a ||| ones = ones := BitVec.or_allOnes

theorem roots_bits : ∀ r : Fin 128, roots.map (readBit r) = List.ofFn (assignment r) :=
  by decide +kernel

abbrev graph := Frame.target

theorem row_flags : ∀ r : Fin 128, graph (assignment r) = readBit r goal := by decide +kernel

theorem getD_map {α β} (f : α → β) (s : List α) (i : Nat) (a : α) :
    (s.map f).getD i (f a) = f (s.getD i a) := by
  induction s generalizing i with
  | nil => simp
  | cons x s ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_mem_or (w : List Word) (i : Nat) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  by_cases h : i < w.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

def binaryWord (w : List Word) (g : Gate) : Word :=
  let d := match g.op with | .or => true | _ => false
  match g.inputs with
  | [] => if d then 0 else ones
  | [a] => w.getD a 0
  | a::b::_ => join d (w.getD a 0) (w.getD b 0)

def gateWord (w : List Word) (g : Gate) : Word :=
  match g.op with
  | .not => match g.inputs with | [] => ones | a::_ => ~~~(w.getD a 0)
  | _ => binaryWord w g

def binCost (g : Gate) : Nat :=
  match g.op, g.inputs with | .and, _::_::_ | .or, _::_::_ => 1 | _, _ => 0
def invCost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

def binaryCount : List Gate → Nat
  | [] => 0 | g::gs => binaryCount gs + binCost g
def inversionCount : List Gate → Nat
  | [] => 0 | g::gs => inversionCount gs + invCost g

def stepWord (w : List Word) (g : Gate) := w ++ [gateWord w g]
def stepBit (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem step_correct (r : Fin 128) (w : List Word) (g : Gate) (h : allowed g) :
    (stepWord w g).map (readBit r) = stepBit (w.map (readBit r)) g := by
  have get (j : Nat) : (w[j]?.map (readBit r)).getD false = readBit r (w[j]?.getD 0) := by
    cases w[j]? <;> simp [readBit]
  rcases g with ⟨op,ins⟩
  rcases h with ⟨hOp, hlen⟩
  change op = .and ∨ op = .or ∨ op = .not at hOp
  change ins.length ≤ 2 at hlen
  rcases hOp with rfl|rfl|rfl <;> cases ins with
  | nil => simp [stepWord,stepBit,gateWord,binaryWord,GateOp.eval] <;> exact read_zero r
  | cons a rest =>
    cases rest with
    | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,readBit]
    | cons b tail =>
      cases tail with
      | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,join,readBit]
      | cons c rest => simp at hlen

theorem fold_correct (r : Fin 128) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, allowed g) :
    (gs.foldl stepWord w).map (readBit r) = gs.foldl stepBit (w.map (readBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by grind), step_correct r w g (h _ (by simp))]

theorem sampled_circuit (C : Circuit) (hp : ∀ g ∈ C.gates, allowed g)
    (accept : ∀ r : Fin 128, C.eval (List.ofFn (assignment r)) = readBit r goal) :
    (C.gates.foldl stepWord roots).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 128 := ⟨i,hi⟩
  change readBit r ((C.gates.foldl stepWord roots).getD C.output 0) = readBit r goal
  rw [← getD_map (readBit r) (C.gates.foldl stepWord roots) C.output 0]
  rw [fold_correct r C.gates roots hp, roots_bits]
  rw [read_zero]
  exact accept r

theorem nontrivial_join (d : Bool) (a b : Word)
    (haa : join d a b ≠ a) (hbb : join d a b ≠ b)
    (h0 : join d a b ≠ 0) (h1 : join d a b ≠ ones) :
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rintro rfl <;> cases d <;> simp_all [join]

theorem not_ones : ~~~ones = (0 : Word) := by decide +kernel
theorem not_zero : ~~~(0 : Word) = ones := by decide +kernel

def Parents (w : List Word) (g : Gate) (c : Word) : Prop :=
  (∃ d a b, c = join d a b ∧ binCost g = 1 ∧ a ∈ w ∧ b ∈ w ∧
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b) ∨
  (∃ a, c = ~~~a ∧ invCost g = 1 ∧ a ∈ w ∧ a ≠ 0 ∧ a ≠ ones)

theorem binary_parents (w : List Word) (op : GateOp) (opok : op = .and ∨ op = .or)
    (ins : List Nat) (missing : binaryWord w ⟨op,ins⟩ ∉ w)
    (p0 : binaryWord w ⟨op,ins⟩ ≠ 0) (p1 : binaryWord w ⟨op,ins⟩ ≠ ones) :
    Parents w ⟨op,ins⟩ (binaryWord w ⟨op,ins⟩) := by
  let d := match op with | .or => true | _ => false
  cases ins with
  | nil =>
    change (if d then 0 else ones) ≠ 0 at p0
    change (if d then 0 else ones) ≠ ones at p1
    cases d <;> simp_all
  | cons i rest =>
    cases rest with
    | nil =>
      change w.getD i 0 ∉ w at missing
      change w.getD i 0 ≠ 0 at p0
      exact (getD_mem_or w i).elim (fun h => (missing h).elim) (fun h => (p0 h).elim)
    | cons j tail =>
      let a := w.getD i 0
      let b := w.getD j 0
      change join d a b ∉ w at missing
      change join d a b ≠ 0 at p0
      change join d a b ≠ ones at p1
      have absent (u : Word) (mem : u ∈ w ∨ u = 0) : join d a b ≠ u := by
        intro e
        exact mem.elim (fun m => missing (e ▸ m)) (fun z => p0 (e.trans z))
      have parts := nontrivial_join d a b (absent _ (getD_mem_or w i))
        (absent _ (getD_mem_or w j)) p0 p1

      have cost : binCost ⟨op,i::j::tail⟩ = 1 := by rcases opok with rfl|rfl <;> rfl
      exact Or.inl ⟨d,a,b,rfl,cost,(getD_mem_or w i).resolve_right parts.1,
        (getD_mem_or w j).resolve_right parts.2.1,parts⟩

theorem gate_parents (w : List Word) (g : Gate) (okay : allowed g)
    (missing : gateWord w g ∉ w) (p0 : gateWord w g ≠ 0) (p1 : gateWord w g ≠ ones) :
    Parents w g (gateWord w g) := by
  rcases g with ⟨op,ins⟩
  have ops : op = .and ∨ op = .or ∨ op = .not := okay.1
  rcases ops with h|h|h
  · subst op
    exact binary_parents w _ (.inl rfl) ins missing p0 p1
  · subst op
    exact binary_parents w _ (.inr rfl) ins missing p0 p1
  · subst op
    cases ins with
    | nil => exact (p1 rfl).elim
    | cons i rest =>
      let a := w.getD i 0
      change ~~~a ≠ 0 at p0
      change ~~~a ≠ ones at p1
      have a0 : a ≠ 0 := fun e => p1 (e ▸ not_zero)
      have a1 : a ≠ ones := fun e => p0 (e ▸ not_ones)
      exact Or.inr ⟨a,rfl,rfl,(getD_mem_or w i).resolve_right a0,a0,a1⟩

def Trace (b n : Nat) (w : List Word) : Prop :=
  ∃ (k j : Nat) (S : Finset Word), k ≤ b ∧ j ≤ n ∧
    (∀ x ∈ S, x ∈ w ∧ x ≠ 0 ∧ x ≠ ones) ∧ Live k j S

theorem unwind (b n : Nat) (w : List Word) (g : Gate) (okay : allowed g)
    (t : Trace b n (stepWord w g)) : Trace (b + binCost g) (n + invCost g) w := by
  obtain ⟨k,j,S,hk,hj,valid,live⟩ := t
  let c := gateWord w g
  have prev (x : Word) (hx : x ∈ S) : (x ∈ w ∨ x = c) ∧ x ≠ 0 ∧ x ≠ ones := by
    simpa [c,stepWord] using valid x hx
  by_cases used : c ∈ S
  · by_cases old : c ∈ w
    · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩
    · let U := S.erase c
      have uc : c ∉ U := Finset.notMem_erase _ _
      have sub (x : Word) (hx : x ∈ U) : x ∈ w ∧ x ≠ 0 ∧ x ≠ ones := by
        have hx' := Finset.mem_erase.mp hx
        have h := prev x hx'.2
        exact ⟨h.1.resolve_right hx'.1,h.2⟩
      have back : insert c U = S := Finset.insert_erase used
      rcases gate_parents w g okay old (valid c used).2.1 (valid c used).2.2 with binary|inv
      · obtain ⟨d,a,x,eqc,cost,ha,hx,a0,x0,a1,x1,ne⟩ := binary
        change c = join d a x at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        have cx : c ≠ x := fun e => old (e ▸ hx)
        refine ⟨k+1,j,insert a (insert x U),by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨hx,x0,x1⟩
          exact sub _ hy
        · apply Live.binary d ne
          · simpa [← eqc,ca,cx] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [← eqc,back]
      · obtain ⟨a,eqc,cost,ha,a0,a1⟩ := inv
        change c = ~~~a at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        refine ⟨k,j+1,insert a U,by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          exact sub _ hy
        · apply Live.inversion
          · simpa [←eqc,ca] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [←eqc,back]
  · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩

theorem trace_aux (gs : List Gate) (w : List Word) (out : Nat) (hp : ∀ g ∈ gs, allowed g)
    (success : (gs.foldl stepWord w).getD out 0 = goal) :
    Trace (binaryCount gs) (inversionCount gs) w := by
  induction gs generalizing w with
  | nil =>
    change w.getD out 0 = goal at success
    have h := (getD_mem_or w out).resolve_right (success ▸ goal_proper.1)
    rw [success] at h
    refine ⟨0,0,{goal},by simp [binaryCount],by simp [inversionCount],?_,Live.done⟩
    simpa using And.intro h goal_proper
  | cons g gs ih => exact unwind _ _ w g (hp _ (by simp)) (ih _ (by grind) success)

theorem circuit_live (C : Circuit) (legal : ∀ g ∈ C.gates, allowed g)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    ∃ b ≤ binaryCount C.gates, ∃ n ≤ inversionCount C.gates, ∃ S ⊆ roots.toFinset, Live b n S := by
  have accept (r : Fin 128) : C.eval (List.ofFn (assignment r)) = readBit r goal :=
    (correct _).trans (row_flags r)
  obtain ⟨b,n,S,hb,hn,incl,live⟩ := trace_aux _ _ _ legal (sampled_circuit C legal accept)
  exact ⟨b,hb,n,hn,S,fun x hx => List.mem_toFinset.mpr (incl x hx).1,live⟩

theorem agree_join (p q : Fin 128) (d : Bool) (a x : Word)
    (ha : readBit p a = readBit q a) (hx : readBit p x = readBit q x) :
    readBit p (join d a x) = readBit q (join d a x) := by
  cases d <;> simp_all [join,readBit]

theorem agree_not (p q : Fin 128) (a : Word) (ha : readBit p a = readBit q a) :
    readBit p (~~~a) = readBit q (~~~a) := by simp_all [readBit]

theorem live_agrees {b n S} (live : Live b n S) (p q : Fin 128)
    (same : ∀ x ∈ S, readBit p x = readBit q x) : readBit p goal = readBit q goal := by
  induction live using Live.recPlain with
  | done => exact same goal (by simp)
  | @binary b n a x U d _ _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_join p q d a x (same _ (by simp)) (same _ (by simp))
    · exact same _ (by simp [hy])
  | @inversion b n a U _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_not p q a (same _ (by simp))
    · exact same _ (by simp [hy])

def witnesses (i : Fin 8) : Fin 128 × Fin 128 :=
  ([(32,33),(34,35),(36,37),(38,39),(40,41),(42,43),(44,45),(46,47)]
    : List (Fin 128 × Fin 128)).get i

theorem witness_correct : ∀ i : Fin 8,
    readBit (witnesses i).1 goal ≠ readBit (witnesses i).2 goal ∧
    ∀ j : Fin 8, readBit (witnesses i).1 (roots.get j) =
      readBit (witnesses i).2 (roots.get j) ∨ j = i := by decide +kernel

theorem roots_full {b n S} (live : Live b n S) (sub : S ⊆ roots.toFinset) :
    S = roots.toFinset := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := witness_correct i
  by_contra missing
  apply distinct (live_agrees live _ _ ?_)
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)

theorem cost_bound (gs : List Gate) : binaryCount gs + inversionCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [binaryCount,inversionCount]
  | cons g gs ih =>
    have hg : binCost g + invCost g ≤ 1 := by
      rcases g with ⟨op,ins⟩
      cases op <;> cases ins with
      | nil => simp [binCost,invCost]
      | cons i tail => cases tail <;> simp [binCost,invCost]
    simp only [binaryCount,inversionCount,List.length_cons]
    omega

theorem zero_inversions (gs : List Gate) (none : ∀ g ∈ gs, g.op ≠ .not) :
    inversionCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ng := none g (by simp)
    have cost : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
    rw [inversionCount,cost,ih (by grind),Nat.add_zero]

theorem unique_inversion (gs : List Gate)
    (uniq : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j) :
    inversionCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases head : g.op = .not
    · have none (x : Gate) (hx : x ∈ gs) : x.op ≠ .not := by
        obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hx
        intro nj
        have eq := uniq ⟨0,by simp⟩ j.succ head nj
        have e := congrArg Fin.val eq
        simp at e
      have one : invCost g = 1 := by simp [invCost,head]
      rw [inversionCount,zero_inversions gs none,one]
    · have zero : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
      rw [inversionCount,zero,Nat.add_zero]
      apply ih
      intro i j ni nj
      exact Fin.succ_injective _ (uniq i.succ j.succ ni nj)

theorem full_chain (gates : List Gate) (out : Nat)
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x) :
    ∃ b n, b+n ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb hn).trans (cost_bound gates),hn.trans (unique_inversion gates uniq),live⟩

theorem has_inversion_cost (gates : List Gate) (hasNot : ∃ g ∈ gates, g.op = .not) :
    1 ≤ inversionCount gates := by
  induction gates with
  | nil => simp at hasNot
  | cons g gs ih =>
    by_cases top : g.op = .not
    · simp [inversionCount, invCost, top]
    · obtain ⟨f,hf,inv⟩ := hasNot
      have hin : f ∈ gs := (List.mem_cons.mp hf).resolve_left (fun eq => top (eq ▸ inv))
      have tail := ih ⟨f,hin,inv⟩
      rw [inversionCount]
      omega

theorem signed_chain {gates : List Gate} {out : Nat}
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x)
    (hasNot : ∃ g ∈ gates, g.op = .not) :
    ∃ b n, b+1 ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gates hasNot)).trans (cost_bound gates),
    hn.trans (unique_inversion gates uniq),live⟩

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true

theorem binaryCount_le_countP (gs : List Gate) :
    binaryCount gs ≤ gs.countP counted := by
  induction gs with
  | nil => simp [binaryCount]
  | cons g gs ih =>
    have cap : binCost g ≤ (counted g).toNat := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> cases inputs with
      | nil => simp [binCost, counted]
      | cons a rest => cases rest <;> simp [binCost, counted]
    rw [binaryCount, List.countP_cons]
    cases h : counted g <;> simp [h] at cap ⊢ <;> omega

theorem circuit_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x) :
    ∃ b n, b ≤ gs.countP counted ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,hb.trans (binaryCount_le_countP gs),live⟩

theorem freely_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x)
    (hasNot : ∃ g ∈ gs, g.op = .not) :
    ∃ b n, b+1 ≤ gs.length ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gs hasNot)).trans (cost_bound gs),live⟩

end PEqualNP.Outside.L_meta_14968

namespace PEqualNP.Outside.L_meta_14968.Reduce
open PEqualNP.Outside.L_meta_14968
def low (a : Word) : BitVec 32 := a.setWidth 32
def pin (a : Word) := canon (low a)
def cliqueGoal : BitVec 32 := 0xfeeefcc8
def cliqueRaw : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
theorem pin_neg (a : Word) : pin (~~~a) = pin a := by
  unfold pin low
  rw [BitVec.setWidth_not (by decide),canon_not]
theorem gate_repr (d : Bool) (a b : Word) :
    ∃ s t, pin (join d a b) = gate s t (pin a) (pin b) := by
  cases d with
  | false =>
    exact ⟨(low a).getLsbD 0,(low b).getLsbD 0,by
      simp only [pin,gate,sign_back]
      exact congrArg canon BitVec.setWidth_and⟩
  | true =>
    refine ⟨(~~~(low a)).getLsbD 0,(~~~(low b)).getLsbD 0,?_⟩
    unfold gate pin
    rw [←canon_not (low a),←canon_not (low b),sign_back,sign_back,←BitVec.not_or,canon_not]
    exact congrArg canon BitVec.setWidth_or
theorem ordinary {b n S} (h : Live b n S) : Proj pin (pin goal) b 0 S := by
  induction h using Live.recPlain with
  | done => exact proj_done _ _ (by decide +kernel)
  | @inversion b n a U fresh proper tail ih =>
    exact proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (pin_neg a) ih
  | @binary b n a x U d ne fresh proper tail ih =>
    obtain ⟨s,t,rep⟩ := gate_repr d a x
    exact proj_bin _ _ _ _ _ (fun v => canon_canon _) (fun h => fresh (by simp [h])) s t rep ih
theorem to_four {b n} (h : Live b n roots.toFinset) :
    ∃ k, k+3 ≤ b ∧ ∃ T ⊆ cliqueRaw.toFinset, Path cliqueGoal k T := by
  obtain ⟨k,hk,T,sub,hp⟩ := ordinary h
  have av : avail pin roots.toFinset = cliqueRaw.toFinset := by decide +kernel
  have cost : lost pin roots.toFinset = 3 := by decide +kernel
  have g : pin goal = cliqueGoal := by decide +kernel
  rw [av] at sub
  rw [g] at hp
  exact ⟨k,by omega,T,sub,hp⟩
end PEqualNP.Outside.L_meta_14968.Reduce

namespace PEqualNP.Outside.L_meta_14968.ArchivedClique

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega

def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

def half (m q r a : ℕ) := (a &&& q &&& full m) |||
    (if a.testBit r then ((full m ^^^ q) &&& full m) else 0)
def slice (m q r a : ℕ) := half m q r a ||| ((half m q r (a >>> m)) <<< m)
lemma half_bit (m q r a i : ℕ) : (half m q r a).testBit i =
    (decide (i<m) && (if q.testBit i then a.testBit i else a.testBit r)) := by
  cases e : a.testBit r <;> cases f : q.testBit i <;> by_cases l : i<m <;>
    simp [half,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,full_bit,e,f,l]
lemma slice_lo {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit i =
    a.testBit (if q.testBit i then i else r) := by
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,hi,e,(show ¬ (m ≤ i) from by omega)]
lemma slice_hi {m i : ℕ} (q r a : ℕ) (hi : i<m) : (slice m q r a).testBit (m+i) =
    a.testBit (m+(if q.testBit i then i else r)) := by
  have n : ¬ (m + i < m) := by omega
  cases e : q.testBit i <;> simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,half_bit,hi,e,n]
lemma slice_above {m i : ℕ} (q r a : ℕ) (hi : 2 * m ≤ i) : (slice m q r a).testBit i=false := by
  simp [slice,Nat.testBit_or,Nat.testBit_shiftLeft,half_bit,(show ¬ (i < m) from by omega),(show ¬ (i - m < m) from by omega)]
lemma slice_hom (m q r d a b : ℕ) (hd : d<4) : slice m q r (combine d a b)=combine d (slice m q r a) (slice m q r b) := by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases lo : i<m
  · rw [slice_lo _ _ _ lo]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_lo _ _ _ lo]
  by_cases upper : i<2*m
  · let j := i-m
    have h : j<m := by dsimp [j];omega
    have e : i=m+j := by dsimp [j];omega
    rw [e,slice_hi _ _ _ h]
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,slice_hi _ _ _ h]
  · have large := slice_above (m:=m) (i:=i) (hi := (show 2 * m ≤ i from by omega))
    interval_cases d <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,large]
def projection (m q r : ℕ) (hr : r < m) : Projection m m := by
  refine ⟨slice m q r, ?_, slice_hom m q r, ?_, by omega⟩
  · simp [slice, half]
  · intro a ga i hi
    rw [slice_lo _ _ _ hi, slice_hi _ _ _ hi]
    cases q.testBit i
    · exact ga r hr
    · exact ga i hi

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def cutSearch (m q fuel : ℕ) (v : List ℕ) : Bool :=
  let r := min (Nat.log2 q) (m-1)
  let xs := v.map (slice m q r)
  let gone := xs.count 0
  gone≤fuel && start m (fuel-gone) xs

theorem cut_complete {m k S} (hm : 0<m) (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup)
    (q fuel : ℕ) (lim : k≤fuel) : cutSearch m q fuel v=true := by
  let r := min (Nat.log2 q) (m-1)
  let p := projection m q r (show r<m by dsimp [r];omega)
  obtain ⟨l,T,cost,live,sub⟩ := projectLive p h
  let xs := v.map (slice m q r)
  have fixed : dead p.toFun S=xs.count 0 := by
    rw [←rep];dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [xs,List.count_eq_countP,List.countP_map,p,projection,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at cost
  have has (x : ℕ) (hx : x∈T) : x∈xs := by simpa [xs, p, projection, Projection.toFun, ←rep] using sub x hx
  have test := start_complete live xs has (fuel-xs.count 0) (by omega)
  change (decide (xs.count 0≤fuel) && start m (fuel-xs.count 0) xs)=true
  simp [test,show xs.count 0≤fuel by omega]

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)

theorem viaDirect {m f v} (nd : v.Nodup) (test : search m f v = false) : Ban m f v := by
  intro k le run
  have yes := complete m f run le v rfl nd
  simp_all

def graph (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def posBits : ℕ := 0x14d1a3468d1a3468d1a3468d1870e1c3870e1c3870e1c387060c183060c183060c183058b162c58b162c58b162c58a3468d1a3468d1a3468d1a342850a142850a142850a14254a952a54a952a54a952a548912244891224489122448870e1c3870e1c3870e1c3870a142850a142850a142850a0c183060c183060c183060b870e1c3870e1c3870e1c3862c58b162c58b162c58b162c183060c183060c183060c152a54a952a54a952a54a952952a54a952a54a952a54a9468d1a3468d1a3468d1a34689122448912244891224488d1a3468d1a3468d1a3468d193264c993264c993264c99264c993264c993264c993264891224489122448912244858b162c58b162c58b162c589122448912244891224489
def negBits : ℕ := 0x1080a10a0304480a100c10101014214060890142018202020284280c112028403040404050850182240508060808080a10a0304480a100c10101014214060890142018202020284280c112028403040404050850182240508060808080a10a0304480a100c10101014214060890142018202020284280c112028403040404050850182240508060808080a10a0304480a100c10101014214060890142018202020284280c112028403040404050850182240508060808080a10a0304480a100c10101014214060890142018202020284280c112028403040404050850182240508060808080a10a0304480a100c10101014214060890142018202020284280c1120284030404040508501822405080608080
def sample (bank : ℕ) (i : Fin 313) (j : Fin 7) := bank.testBit (7*i.val+j.val)
def inputs : List ℕ := [0x48a245122891448a245122891448a245122891448a245122891448a245122891448a24512289140007ffc000000fff8000000000fff8003ffe000fff8000001ffffff8000001ffffff8003ffffff,0x2c01600b005802c01600b005802c01600b005802c01600b005802c01600b005802c01600b005800000000000000000003ffe000ffffffc0000000000003ffe000fffffffffe000fffffffffe000,0x1000000000000000000000000000000000000000000000000000000000000000000000000000000,0x93049824c126093049824c126093049824c126093049824c126093049824c126093049824c1260fff8000001fff0000003ffffff0000000001fff0000003ffffff0000003ffffff0000003ffffff,0x21c00e007003801c00e007003801c00e007003801c00e007003801c00e007003801c00e007003810000000001fffffffffc0000000000000001fffffffffc0000000000003ffffffffffffc000000,0xe007003801c00e007003801c00e007003801c00e007003801c00e007003801c00e007003801c00fffffffffe00000000000000000000000001ffffffffffffffffffffffc0000000000000000000,0x1000800400200100080040020010008004002001000800400200100080040020010008004002000fffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000]
def seeds : List Wire := inputs.map (fun a => (false,a))
theorem listed : ∀ i : Fin 313, seeds.map (read i.val)=List.ofFn (sample posBits i) ∧
    seeds.map (read (313+i.val))=List.ofFn (sample negBits i) := by decide +kernel
theorem labels : ∀ i : Fin 313, graph (sample posBits i)=true ∧ graph (sample negBits i)=false := by decide +kernel
theorem essential : ∀ a∈inputs, ∃ i : Fin 313, ∀ b∈inputs, b.testBit i.val≠b.testBit (313+i.val) → b=a := by decide +kernel
theorem initial {k S} (live : Live 313 k S) (sub : ∀ a∈S,a∈inputs) : S=inputs.toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  obtain ⟨i,h⟩ := essential a (List.mem_toFinset.mp ha)
  obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
  exact h b (sub b hb) sep ▸ hb
theorem trace (C : Circuit) (fan : FanInTwo C) (eq : circuitFun 7 C=graph) :
    ∃ k≤C.gates.countP counted, Live 313 k inputs.toFinset := by
  let final := execute C.gates seeds
  let out := final.getD C.output zero
  have ev (i : ℕ) : read i out = C.eval (seeds.map (read i)) := by
    rw [show read i out = (final.map (read i)).getD C.output false from (read_get i final C.output).symm]
    rw [show final=execute C.gates seeds from rfl,execute_read i _ _ fan];rfl
  have result (x : Fin 7 → Bool) : C.eval (List.ofFn x)=graph x := congrFun eq x
  have good : Good 313 out.2 := by
    intro i hi same
    let j : Fin 313 := ⟨i,hi⟩
    have diff : read i out=read (313+i) out := by simp [read,same]
    have p := ev i;have n := ev (313+i)
    rw [(listed j).1,result,(labels j).1] at p
    rw [(listed j).2,result,(labels j).2] at n
    rw [p,n] at diff;contradiction
  have nz : out.2≠0 := by
    intro z;have bad := good 0 (by decide);simp [z] at bad
  have found : out.2∈ reps final := (get_simple final C.output).resolve_left nz
  obtain ⟨k,S,limit,live,sub⟩ := extract good nz C.gates seeds found
  have stays : ∀ a∈S, a∈inputs := by simpa [reps,seeds,List.map_map,Function.comp_def] using sub
  exact ⟨k,limit,initial live stays ▸ live⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj0 : Projection 50 50 := pick [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj1 : Projection 50 50 := pick [0,1,4,5,2,3,6,9,10,7,8,14,15,16,11,12,13,17,19,18,21,20,22,25,26,23,24,27,28,31,32,29,30,33,44,45,46,42,43,47,48,49,37,38,34,35,36,39,40,41] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj2 : Projection 50 50 := pick [1,0,3,2,5,4,6,8,7,10,9,11,13,12,14,16,15,17,20,21,18,19,28,30,29,32,31,33,22,24,23,26,25,27,34,36,35,38,37,39,41,40,43,42,44,46,45,47,49,48] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj3 : Projection 50 50 := pick [1,0,5,4,3,2,6,10,9,8,7,14,16,15,11,13,12,17,21,20,19,18,28,32,31,30,29,33,22,26,25,24,23,27,44,46,45,43,42,47,49,48,38,37,34,36,35,39,41,40] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj4 : Projection 50 50 := pick [11,14,12,15,13,16,17,18,19,20,21,0,2,4,1,3,5,6,7,8,9,10,34,35,37,36,38,39,44,42,45,43,46,47,22,23,25,24,26,27,40,48,29,31,28,30,32,33,41,49] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj5 : Projection 50 50 := pick [11,14,13,16,12,15,17,20,21,18,19,1,3,5,0,2,4,6,8,7,10,9,34,36,38,35,37,39,44,43,46,42,45,47,28,30,32,29,31,33,41,49,24,26,22,23,25,27,40,48] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj6 : Projection 50 50 := pick [14,11,15,12,16,13,17,19,18,21,20,0,4,2,1,5,3,6,9,10,7,8,44,45,42,46,43,47,34,37,35,38,36,39,22,25,23,26,24,27,48,40,31,29,28,32,30,33,49,41] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
def proj7 : Projection 50 50 := pick [14,11,16,13,15,12,17,21,20,19,18,1,5,3,0,4,2,6,10,9,8,7,44,46,43,45,42,47,34,38,36,37,35,39,28,32,30,31,29,33,49,41,26,24,22,25,23,27,48,40] rfl (by decide +kernel) (by decide)
def valeur0 : ℕ := 0x3c718650e633fffc003ff980
def valeur1 : ℕ := 0x2020820080103ffffffc00000
def valeur2 : ℕ := 0x494a28b324a5501000fcc07ff
def valeur3 : ℕ := 0x9294554c494aa0203f03007ff
def valeur4 : ℕ := 0xdc18618a718c3fc00003ffe00
def etat0 : List ℕ := [valeur0,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne8 : Ban 50 5 etat0 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur5 : ℕ := 0x3fc0000000000
def etat1 : List ℕ := [valeur5,valeur0,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne9 : Ban 50 5 etat1 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur6 : ℕ := 0x3c718650e63003fc003ff980
def etat2 : List ℕ := [valeur6,valeur0,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne10 : Ban 50 5 etat2 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur7 : ℕ := 0x202082008010003ffffc00000
def etat3 : List ℕ := [valeur5,valeur6,valeur7,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne11 : Ban 50 5 etat3 := viaDirect (by decide +kernel) (by decide +kernel)
def etat4 : List ℕ := [valeur6,valeur7,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne12 : Ban 50 5 etat4 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur8 : ℕ := 0x1000000000000
def etat5 : List ℕ := [valeur8,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne13 : Ban 50 5 etat5 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur9 : ℕ := 0x494a28b324a57fd000fcc07ff
def etat6 : List ℕ := [valeur6,valeur1,valeur9,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne14 : Ban 50 5 etat6 := viaDirect (by decide +kernel) (by decide +kernel)
def etat7 : List ℕ := [valeur5,valeur6,valeur1,valeur9,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne15 : Ban 50 5 etat7 := viaDirect (by decide +kernel) (by decide +kernel)
def etat8 : List ℕ := [valeur6,valeur1,valeur2,valeur9,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne16 : Ban 50 5 etat8 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur10 : ℕ := 0x2fc0000000000
def etat9 : List ℕ := [valeur10,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne17 : Ban 50 5 etat9 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur11 : ℕ := 0x494a28b324a5401000fcc07ff
def etat10 : List ℕ := [valeur6,valeur1,valeur11,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne18 : Ban 50 5 etat10 := viaDirect (by decide +kernel) (by decide +kernel)
def etat11 : List ℕ := [valeur5,valeur6,valeur1,valeur11,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne19 : Ban 50 5 etat11 := viaDirect (by decide +kernel) (by decide +kernel)
def etat12 : List ℕ := [valeur6,valeur1,valeur11,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne20 : Ban 50 5 etat12 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur12 : ℕ := 0x2000000000000
def etat13 : List ℕ := [valeur12,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne21 : Ban 50 5 etat13 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur13 : ℕ := 0x9294554c494abfe03f03007ff
def etat14 : List ℕ := [valeur6,valeur1,valeur2,valeur13,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne22 : Ban 50 5 etat14 := viaDirect (by decide +kernel) (by decide +kernel)
def etat15 : List ℕ := [valeur5,valeur6,valeur1,valeur2,valeur13,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne23 : Ban 50 5 etat15 := viaDirect (by decide +kernel) (by decide +kernel)
def etat16 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur13,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne24 : Ban 50 5 etat16 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur14 : ℕ := 0x1fc0000000000
def etat17 : List ℕ := [valeur14,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne25 : Ban 50 5 etat17 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur15 : ℕ := 0x9294554c494a80203f03007ff
def etat18 : List ℕ := [valeur6,valeur1,valeur2,valeur15,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne26 : Ban 50 5 etat18 := viaDirect (by decide +kernel) (by decide +kernel)
def etat19 : List ℕ := [valeur5,valeur6,valeur1,valeur2,valeur15,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne27 : Ban 50 5 etat19 := viaDirect (by decide +kernel) (by decide +kernel)
def etat20 : List ℕ := [valeur6,valeur1,valeur2,valeur15,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne28 : Ban 50 5 etat20 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur16 : ℕ := 0xdc18618a718c00000003ffe00
def etat21 : List ℕ := [valeur5,valeur6,valeur1,valeur2,valeur3,valeur16]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne29 : Ban 50 5 etat21 := viaDirect (by decide +kernel) (by decide +kernel)
def etat22 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur16,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne30 : Ban 50 5 etat22 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur17 : ℕ := 0x101000fc007ff
def etat23 : List ℕ := [valeur17,valeur6,valeur1,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne31 : Ban 50 4 etat23 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur18 : ℕ := 0x101000fc00000
def valeur19 : ℕ := 0x2020820080103ffffffc007ff
def etat24 : List ℕ := [valeur18,valeur6,valeur19,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne32 : Ban 50 4 etat24 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur20 : ℕ := 0x7ff
def valeur21 : ℕ := 0x3c718650e63103fc0ffff980
def etat25 : List ℕ := [valeur20,valeur21,valeur1,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne33 : Ban 50 4 etat25 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur22 : ℕ := 0x9294554c494ab0303fff007ff
def etat26 : List ℕ := [valeur20,valeur6,valeur1,valeur22,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne34 : Ban 50 4 etat26 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur23 : ℕ := 0xdc18618a718c3fd000ffffe00
def etat27 : List ℕ := [valeur20,valeur6,valeur1,valeur3,valeur23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne35 : Ban 50 4 etat27 := viaDirect (by decide +kernel) (by decide +kernel)
def etat28 : List ℕ := [valeur20,valeur18,valeur6,valeur1,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne36 : Ban 50 5 etat28 := viaBranch (ws := [etat23,etat24,etat25,etat26,etat27]) (consBan borne31 (consBan borne32 (consBan borne33 (consBan borne34 (consBan borne35 (nilBan 50 4)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur24 : ℕ := 0x3ff800
def etat29 : List ℕ := [valeur24,valeur5,valeur6,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne37 : Ban 50 5 etat29 := viaPerm proj6 proj5 borne36 (by decide +kernel) (by decide +kernel)
def valeur25 : ℕ := 0x3c718650e63003fc00000180
def etat30 : List ℕ := [valeur5,valeur25,valeur6,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne38 : Ban 50 5 etat30 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur26 : ℕ := 0xfc38e38af19c3fffffffffe00
def etat31 : List ℕ := [valeur0,valeur1,valeur2,valeur3,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne39 : Ban 50 4 etat31 := viaDirect (by decide +kernel) (by decide +kernel)
def etat32 : List ℕ := [valeur6,valeur1,valeur9,valeur3,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne40 : Ban 50 4 etat32 := viaDirect (by decide +kernel) (by decide +kernel)
def etat33 : List ℕ := [valeur6,valeur1,valeur2,valeur13,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne41 : Ban 50 4 etat33 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur27 : ℕ := 0xfc38e38af19c003fffffffe00
def etat34 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur27]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne42 : Ban 50 4 etat34 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur28 : ℕ := 0x3fc003ff800
def etat35 : List ℕ := [valeur28,valeur5,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne43 : Ban 50 4 etat35 := viaDirect (by decide +kernel) (by decide +kernel)
def etat36 : List ℕ := [valeur5,valeur6,valeur1,valeur2,valeur3,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne44 : Ban 50 5 etat36 := viaBranch (ws := [etat31,etat32,etat33,etat34,etat35]) (consBan borne39 (consBan borne40 (consBan borne41 (consBan borne42 (consBan borne43 (nilBan 50 4)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat37 : List ℕ := [valeur5,valeur6,valeur2,valeur3,valeur4,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne45 : Ban 50 5 etat37 := viaDirect (by decide +kernel) (by decide +kernel)
def etat38 : List ℕ := [valeur5,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne46 : Ban 50 6 etat38 := viaBranch (ws := [etat0,etat1,etat2,etat3,etat4,etat5,etat6,etat7,etat8,etat9,etat10,etat11,etat12,etat13,etat14,etat15,etat16,etat17,etat18,etat19,etat20,etat21,etat22,etat29,etat30,etat36,etat37]) (consBan borne8 (consBan borne9 (consBan borne10 (consBan borne11 (consBan borne12 (consBan borne13 (consBan borne14 (consBan borne15 (consBan borne16 (consBan borne17 (consBan borne18 (consBan borne19 (consBan borne20 (consBan borne21 (consBan borne22 (consBan borne23 (consBan borne24 (consBan borne25 (consBan borne26 (consBan borne27 (consBan borne28 (consBan borne29 (consBan borne30 (consBan borne37 (consBan borne38 (consBan borne44 (consBan borne45 (nilBan 50 5)))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur29 : ℕ := 0x3fc00000000
def etat39 : List ℕ := [valeur29,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne47 : Ban 50 6 etat39 := viaPerm proj1 proj1 borne46 (by decide +kernel) (by decide +kernel)
def valeur30 : ℕ := 0x23e79a658e733fffffffff980
def etat40 : List ℕ := [valeur29,valeur6,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne48 : Ban 50 5 etat40 := viaDirect (by decide +kernel) (by decide +kernel)
def etat41 : List ℕ := [valeur29,valeur1,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne49 : Ban 50 5 etat41 := viaPerm proj1 proj1 borne44 (by decide +kernel) (by decide +kernel)
def valeur31 : ℕ := 0x3c718650e6300000003ff980
def etat42 : List ℕ := [valeur31,valeur6,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne50 : Ban 50 5 etat42 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur32 : ℕ := 0x2020820080103fc03ffc00000
def etat43 : List ℕ := [valeur32,valeur1,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne51 : Ban 50 5 etat43 := viaDirect (by decide +kernel) (by decide +kernel)
def etat44 : List ℕ := [valeur6,valeur32,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne52 : Ban 50 5 etat44 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur33 : ℕ := 0x4bcf38f72ee7503fc0fffffff
def etat45 : List ℕ := [valeur1,valeur30,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne53 : Ban 50 5 etat45 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur34 : ℕ := 0x28510440a42002fc0033f800
def etat46 : List ℕ := [valeur34,valeur1,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne54 : Ban 50 5 etat46 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur35 : ℕ := 0x93d75d6d4f6ba03fff03fffff
def etat47 : List ℕ := [valeur1,valeur30,valeur2,valeur3,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne55 : Ban 50 5 etat47 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur36 : ℕ := 0x14308210621001fc000ff800
def etat48 : List ℕ := [valeur36,valeur1,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne56 : Ban 50 5 etat48 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur37 : ℕ := 0xdfdf79ef7fef3fffc003fff80
def etat49 : List ℕ := [valeur1,valeur30,valeur2,valeur3,valeur4,valeur37]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne57 : Ban 50 5 etat49 := viaDirect (by decide +kernel) (by decide +kernel)
def etat50 : List ℕ := [valeur25,valeur1,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne58 : Ban 50 5 etat50 := viaDirect (by decide +kernel) (by decide +kernel)
def etat51 : List ℕ := [valeur31,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne59 : Ban 50 5 etat51 := viaDirect (by decide +kernel) (by decide +kernel)
def etat52 : List ℕ := [valeur6,valeur30,valeur2,valeur3,valeur4,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne60 : Ban 50 5 etat52 := viaDirect (by decide +kernel) (by decide +kernel)
def etat53 : List ℕ := [valeur6,valeur7,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne61 : Ban 50 5 etat53 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur38 : ℕ := 0x14208210421101000fcc0180
def etat54 : List ℕ := [valeur38,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne62 : Ban 50 5 etat54 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur39 : ℕ := 0x6befbaf7aef77ffffffffffff
def etat55 : List ℕ := [valeur6,valeur1,valeur2,valeur39,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne63 : Ban 50 5 etat55 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur40 : ℕ := 0x22a592448a522fefff033f800
def etat56 : List ℕ := [valeur6,valeur1,valeur40,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne64 : Ban 50 5 etat56 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur41 : ℕ := 0x480820922084400000000067f
def etat57 : List ℕ := [valeur6,valeur1,valeur41,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne65 : Ban 50 5 etat57 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur42 : ℕ := 0x2841044084220203f0300180
def etat58 : List ℕ := [valeur42,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne66 : Ban 50 5 etat58 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur43 : ℕ := 0xb3f7df6dcf7bbffffffffffff
def etat59 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur43,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne67 : Ban 50 5 etat59 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur44 : ℕ := 0x21638a2186311fdfc0fcff800
def etat60 : List ℕ := [valeur6,valeur1,valeur44,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne68 : Ban 50 5 etat60 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur45 : ℕ := 0x901045084108800000000067f
def etat61 : List ℕ := [valeur6,valeur1,valeur2,valeur45,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne69 : Ban 50 5 etat61 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur46 : ℕ := 0x3fc00003ff800
def etat62 : List ℕ := [valeur46,valeur0,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne70 : Ban 50 4 etat62 := viaDirect (by decide +kernel) (by decide +kernel)
def etat63 : List ℕ := [valeur46,valeur25,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne71 : Ban 50 4 etat63 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur47 : ℕ := 0x2020820080103fffffffff800
def etat64 : List ℕ := [valeur46,valeur6,valeur47,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne72 : Ban 50 4 etat64 := viaDirect (by decide +kernel) (by decide +kernel)
def etat65 : List ℕ := [valeur46,valeur6,valeur7,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne73 : Ban 50 4 etat65 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur48 : ℕ := 0x494a28b324a57fd000fffffff
def etat66 : List ℕ := [valeur46,valeur6,valeur1,valeur48,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne74 : Ban 50 4 etat66 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur49 : ℕ := 0x494a28b324a5401000fc007ff
def etat67 : List ℕ := [valeur46,valeur6,valeur1,valeur49,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne75 : Ban 50 4 etat67 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur50 : ℕ := 0x9294554c494abfe03f03fffff
def etat68 : List ℕ := [valeur46,valeur6,valeur1,valeur2,valeur50]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne76 : Ban 50 4 etat68 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur51 : ℕ := 0x9294554c494a80203f00007ff
def etat69 : List ℕ := [valeur46,valeur6,valeur1,valeur2,valeur51]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne77 : Ban 50 4 etat69 := viaDirect (by decide +kernel) (by decide +kernel)
def etat70 : List ℕ := [valeur29,valeur46,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne78 : Ban 50 4 etat70 := viaDirect (by decide +kernel) (by decide +kernel)
def etat71 : List ℕ := [valeur46,valeur32,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne79 : Ban 50 4 etat71 := viaDirect (by decide +kernel) (by decide +kernel)
def etat72 : List ℕ := [valeur46,valeur1,valeur2,valeur33,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne80 : Ban 50 4 etat72 := viaDirect (by decide +kernel) (by decide +kernel)
def etat73 : List ℕ := [valeur46,valeur34,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne81 : Ban 50 4 etat73 := viaDirect (by decide +kernel) (by decide +kernel)
def etat74 : List ℕ := [valeur46,valeur1,valeur2,valeur3,valeur35]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne82 : Ban 50 4 etat74 := viaDirect (by decide +kernel) (by decide +kernel)
def etat75 : List ℕ := [valeur46,valeur36,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne83 : Ban 50 4 etat75 := viaDirect (by decide +kernel) (by decide +kernel)
def etat76 : List ℕ := [valeur46,valeur6,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne84 : Ban 50 5 etat76 := viaBranch (ws := [etat62,etat63,etat64,etat65,etat66,etat67,etat68,etat69,etat70,etat71,etat72,etat73,etat74,etat75]) (consBan borne70 (consBan borne71 (consBan borne72 (consBan borne73 (consBan borne74 (consBan borne75 (consBan borne76 (consBan borne77 (consBan borne78 (consBan borne79 (consBan borne80 (consBan borne81 (consBan borne82 (consBan borne83 (nilBan 50 4))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat77 : List ℕ := [valeur46,valeur6,valeur1,valeur30,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne85 : Ban 50 5 etat77 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne86 : Ban 50 4 etat0 := viaDirect (by decide +kernel) (by decide +kernel)
def etat78 : List ℕ := [valeur6,valeur47,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne87 : Ban 50 4 etat78 := viaDirect (by decide +kernel) (by decide +kernel)
def etat79 : List ℕ := [valeur6,valeur1,valeur48,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne88 : Ban 50 4 etat79 := viaDirect (by decide +kernel) (by decide +kernel)
def etat80 : List ℕ := [valeur6,valeur1,valeur49,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne89 : Ban 50 4 etat80 := viaDirect (by decide +kernel) (by decide +kernel)
def etat81 : List ℕ := [valeur6,valeur1,valeur2,valeur50,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne90 : Ban 50 4 etat81 := viaDirect (by decide +kernel) (by decide +kernel)
def etat82 : List ℕ := [valeur6,valeur1,valeur2,valeur51,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne91 : Ban 50 4 etat82 := viaDirect (by decide +kernel) (by decide +kernel)
def etat83 : List ℕ := [valeur46,valeur1,valeur2,valeur3,valeur37]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne92 : Ban 50 4 etat83 := viaDirect (by decide +kernel) (by decide +kernel)
def etat84 : List ℕ := [valeur46,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne93 : Ban 50 5 etat84 := viaBranch (ws := [etat0,etat78,etat79,etat80,etat81,etat82,etat83,etat63,etat65]) (consBan borne86 (consBan borne87 (consBan borne88 (consBan borne89 (consBan borne90 (consBan borne91 (consBan borne92 (consBan borne71 (consBan borne73 (nilBan 50 4)))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur52 : ℕ := 0xfffffbefffff3ffffffffff80
def etat85 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur52]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne94 : Ban 50 5 etat85 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur53 : ℕ := 0x23e79a658e73003ffffc00180
def etat86 : List ℕ := [valeur6,valeur1,valeur53,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne95 : Ban 50 5 etat86 := viaDirect (by decide +kernel) (by decide +kernel)
def etat87 : List ℕ := [valeur6,valeur1,valeur53,valeur30,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne96 : Ban 50 5 etat87 := viaDirect (by decide +kernel) (by decide +kernel)
def etat88 : List ℕ := [valeur6,valeur1,valeur53,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne97 : Ban 50 5 etat88 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur54 : ℕ := 0xdc18618a718c0000000000600
def etat89 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur54,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne98 : Ban 50 5 etat89 := viaDirect (by decide +kernel) (by decide +kernel)
def etat90 : List ℕ := [valeur6,valeur1,valeur30,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne99 : Ban 50 6 etat90 := viaBranch (ws := [etat40,etat41,etat42,etat43,etat44,etat45,etat46,etat47,etat48,etat49,etat50,etat51,etat52,etat53,etat54,etat55,etat56,etat57,etat58,etat59,etat60,etat61,etat76,etat77,etat84,etat85,etat86,etat87,etat88,etat89]) (consBan borne48 (consBan borne49 (consBan borne50 (consBan borne51 (consBan borne52 (consBan borne53 (consBan borne54 (consBan borne55 (consBan borne56 (consBan borne57 (consBan borne58 (consBan borne59 (consBan borne60 (consBan borne61 (consBan borne62 (consBan borne63 (consBan borne64 (consBan borne65 (consBan borne66 (consBan borne67 (consBan borne68 (consBan borne69 (consBan borne84 (consBan borne85 (consBan borne93 (consBan borne94 (consBan borne95 (consBan borne96 (consBan borne97 (consBan borne98 (nilBan 50 5))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat91 : List ℕ := [valeur29,valeur31,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne100 : Ban 50 5 etat91 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne101 : Ban 50 5 etat39 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne102 : Ban 50 5 etat90 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur55 : ℕ := 0x1420821042100000000c0180
def etat92 : List ℕ := [valeur55,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne103 : Ban 50 5 etat92 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur56 : ℕ := 0x4bcf38f72ee7501000fffffff
def etat93 : List ℕ := [valeur6,valeur1,valeur2,valeur56,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne104 : Ban 50 5 etat93 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur57 : ℕ := 0x28510440a42000000033f800
def etat94 : List ℕ := [valeur57,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne105 : Ban 50 5 etat94 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur58 : ℕ := 0x480820922084501000fc0067f
def etat95 : List ℕ := [valeur6,valeur1,valeur58,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne106 : Ban 50 5 etat95 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur59 : ℕ := 0x284104408420000000300180
def etat96 : List ℕ := [valeur59,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne107 : Ban 50 5 etat96 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur60 : ℕ := 0x93d75d6d4f6ba0203f03fffff
def etat97 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur60,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne108 : Ban 50 5 etat97 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur61 : ℕ := 0x1430821062100000000ff800
def etat98 : List ℕ := [valeur61,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne109 : Ban 50 5 etat98 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur62 : ℕ := 0x901045084108a0203f000067f
def etat99 : List ℕ := [valeur6,valeur1,valeur2,valeur62,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne110 : Ban 50 5 etat99 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur63 : ℕ := 0x3c718650e63003fc003fffff
def etat100 : List ℕ := [valeur63,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne111 : Ban 50 4 etat100 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur64 : ℕ := 0x3c718650e63003fc003ff800
def etat101 : List ℕ := [valeur64,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne112 : Ban 50 4 etat101 := viaDirect (by decide +kernel) (by decide +kernel)
def etat102 : List ℕ := [valeur6,valeur19,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne113 : Ban 50 4 etat102 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur65 : ℕ := 0xdc18618a718c3fc00003fffff
def etat103 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne114 : Ban 50 4 etat103 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur66 : ℕ := 0xdc18618a718c3fc00003ff800
def etat104 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur66]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne115 : Ban 50 4 etat104 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur67 : ℕ := 0xdbde7dff6deff0303fffc07ff
def etat105 : List ℕ := [valeur20,valeur6,valeur1,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne116 : Ban 50 4 etat105 := viaDirect (by decide +kernel) (by decide +kernel)
def etat106 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne117 : Ban 50 5 etat106 := viaBranch (ws := [etat100,etat101,etat102,etat103,etat104,etat105]) (consBan borne111 (consBan borne112 (consBan borne113 (consBan borne114 (consBan borne115 (consBan borne116 (nilBan 50 4))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat107 : List ℕ := [valeur24,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne118 : Ban 50 5 etat107 := viaPerm proj4 proj4 borne117 (by decide +kernel) (by decide +kernel)
def valeur68 : ℕ := 0xdfdf79ef7fef3fc00003fff80
def etat108 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur68]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne119 : Ban 50 5 etat108 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur69 : ℕ := 0x3c718650e630000000000180
def etat109 : List ℕ := [valeur69,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne120 : Ban 50 5 etat109 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur70 : ℕ := 0xdc18618a718c3fc0000000600
def etat110 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur70,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne121 : Ban 50 5 etat110 := viaDirect (by decide +kernel) (by decide +kernel)
def etat111 : List ℕ := [valeur31,valeur32,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne122 : Ban 50 5 etat111 := viaDirect (by decide +kernel) (by decide +kernel)
def etat112 : List ℕ := [valeur31,valeur6,valeur32,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne123 : Ban 50 5 etat112 := viaDirect (by decide +kernel) (by decide +kernel)
def etat113 : List ℕ := [valeur31,valeur32,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne124 : Ban 50 5 etat113 := viaDirect (by decide +kernel) (by decide +kernel)
def etat114 : List ℕ := [valeur31,valeur1,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne125 : Ban 50 5 etat114 := viaDirect (by decide +kernel) (by decide +kernel)
def etat115 : List ℕ := [valeur34,valeur31,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne126 : Ban 50 5 etat115 := viaDirect (by decide +kernel) (by decide +kernel)
def etat116 : List ℕ := [valeur31,valeur1,valeur2,valeur3,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne127 : Ban 50 5 etat116 := viaDirect (by decide +kernel) (by decide +kernel)
def etat117 : List ℕ := [valeur36,valeur31,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne128 : Ban 50 5 etat117 := viaDirect (by decide +kernel) (by decide +kernel)
def etat118 : List ℕ := [valeur31,valeur1,valeur2,valeur3,valeur4,valeur37]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne129 : Ban 50 5 etat118 := viaDirect (by decide +kernel) (by decide +kernel)
def etat119 : List ℕ := [valeur31,valeur25,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne130 : Ban 50 5 etat119 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne131 : Ban 50 6 etat51 := viaBranch (ws := [etat91,etat39,etat42,etat90,etat92,etat93,etat94,etat95,etat96,etat97,etat98,etat99,etat107,etat108,etat109,etat110,etat111,etat112,etat113,etat114,etat115,etat116,etat117,etat118,etat119]) (consBan borne100 (consBan borne101 (consBan borne50 (consBan borne102 (consBan borne103 (consBan borne104 (consBan borne105 (consBan borne106 (consBan borne107 (consBan borne108 (consBan borne109 (consBan borne110 (consBan borne118 (consBan borne119 (consBan borne120 (consBan borne121 (consBan borne122 (consBan borne123 (consBan borne124 (consBan borne125 (consBan borne126 (consBan borne127 (consBan borne128 (consBan borne129 (consBan borne130 (nilBan 50 5)))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur71 : ℕ := 0x23e79a658e73003fffffff980
def etat120 : List ℕ := [valeur6,valeur1,valeur71,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne132 : Ban 50 5 etat120 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur72 : ℕ := 0x20208200801000003ffc00000
def etat121 : List ℕ := [valeur6,valeur72,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne133 : Ban 50 5 etat121 := viaDirect (by decide +kernel) (by decide +kernel)
def etat122 : List ℕ := [valeur6,valeur7,valeur32,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne134 : Ban 50 5 etat122 := viaDirect (by decide +kernel) (by decide +kernel)
def etat123 : List ℕ := [valeur24,valeur6,valeur7,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne135 : Ban 50 5 etat123 := viaDirect (by decide +kernel) (by decide +kernel)
def etat124 : List ℕ := [valeur25,valeur6,valeur7,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne136 : Ban 50 5 etat124 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne137 : Ban 50 5 etat38 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur73 : ℕ := 0x1000fc00000
def etat125 : List ℕ := [valeur73,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne138 : Ban 50 5 etat125 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur74 : ℕ := 0x696aaab3a4b5503ffffcc07ff
def etat126 : List ℕ := [valeur6,valeur1,valeur2,valeur74,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne139 : Ban 50 5 etat126 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur75 : ℕ := 0x202082008010002fff0000000
def etat127 : List ℕ := [valeur6,valeur75,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne140 : Ban 50 5 etat127 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur76 : ℕ := 0x494a28b324a550000000c07ff
def etat128 : List ℕ := [valeur6,valeur1,valeur76,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne141 : Ban 50 5 etat128 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur77 : ℕ := 0x203f0000000
def etat129 : List ℕ := [valeur77,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne142 : Ban 50 5 etat129 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur78 : ℕ := 0xb2b4d74cc95aa03fffff007ff
def etat130 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur78,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne143 : Ban 50 5 etat130 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur79 : ℕ := 0x202082008010001fc0fc00000
def etat131 : List ℕ := [valeur6,valeur79,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne144 : Ban 50 5 etat131 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur80 : ℕ := 0x9294554c494aa0000003007ff
def etat132 : List ℕ := [valeur6,valeur1,valeur2,valeur80,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne145 : Ban 50 5 etat132 := viaDirect (by decide +kernel) (by decide +kernel)
def etat133 : List ℕ := [valeur6,valeur7,valeur1,valeur2,valeur3,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne146 : Ban 50 5 etat133 := viaDirect (by decide +kernel) (by decide +kernel)
def etat134 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur26]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne147 : Ban 50 5 etat134 := viaDirect (by decide +kernel) (by decide +kernel)
def etat135 : List ℕ := [valeur6,valeur7,valeur2,valeur3,valeur16]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne148 : Ban 50 5 etat135 := viaDirect (by decide +kernel) (by decide +kernel)
def etat136 : List ℕ := [valeur6,valeur7,valeur1,valeur2,valeur3,valeur16]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne149 : Ban 50 5 etat136 := viaDirect (by decide +kernel) (by decide +kernel)
def etat137 : List ℕ := [valeur6,valeur7,valeur2,valeur3,valeur16,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne150 : Ban 50 5 etat137 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne151 : Ban 50 6 etat4 := viaBranch (ws := [etat39,etat120,etat51,etat121,etat53,etat122,etat123,etat124,etat3,etat38,etat125,etat126,etat127,etat128,etat129,etat130,etat131,etat132,etat133,etat134,etat135,etat136,etat137]) (consBan borne101 (consBan borne132 (consBan borne59 (consBan borne133 (consBan borne61 (consBan borne134 (consBan borne135 (consBan borne136 (consBan borne11 (consBan borne137 (consBan borne138 (consBan borne139 (consBan borne140 (consBan borne141 (consBan borne142 (consBan borne143 (consBan borne144 (consBan borne145 (consBan borne146 (consBan borne147 (consBan borne148 (consBan borne149 (consBan borne150 (nilBan 50 5)))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne152 : Ban 50 6 etat44 := viaPerm proj1 proj1 borne151 (by decide +kernel) (by decide +kernel)
def valeur81 : ℕ := 0x284104408420020000300180
def etat138 : List ℕ := [valeur36,valeur81,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne153 : Ban 50 5 etat138 := viaDirect (by decide +kernel) (by decide +kernel)
def etat139 : List ℕ := [valeur36,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne154 : Ban 50 5 etat139 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur82 : ℕ := 0x20000000000
def etat140 : List ℕ := [valeur82,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne155 : Ban 50 5 etat140 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur83 : ℕ := 0x22a4924488523fffffff00180
def etat141 : List ℕ := [valeur6,valeur1,valeur83,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne156 : Ban 50 5 etat141 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur84 : ℕ := 0x2020820080103fdffffc00000
def etat142 : List ℕ := [valeur6,valeur84,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne157 : Ban 50 5 etat142 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur85 : ℕ := 0x180
def etat143 : List ℕ := [valeur85,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne158 : Ban 50 5 etat143 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur86 : ℕ := 0x4bce38f72ce7503000ffc07ff
def etat144 : List ℕ := [valeur6,valeur1,valeur2,valeur86,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne159 : Ban 50 5 etat144 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur87 : ℕ := 0x284104408420020000300000
def etat145 : List ℕ := [valeur87,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne160 : Ban 50 5 etat145 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur88 : ℕ := 0x494a28b324a5501000fcc067f
def etat146 : List ℕ := [valeur6,valeur1,valeur88,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne161 : Ban 50 5 etat146 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur89 : ℕ := 0x901045084108a0003f000067f
def etat147 : List ℕ := [valeur81,valeur6,valeur1,valeur2,valeur89,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne162 : Ban 50 5 etat147 := viaDirect (by decide +kernel) (by decide +kernel)
def etat148 : List ℕ := [valeur6,valeur1,valeur2,valeur89,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne163 : Ban 50 5 etat148 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur90 : ℕ := 0x300000
def etat149 : List ℕ := [valeur90,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne164 : Ban 50 5 etat149 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur91 : ℕ := 0xde9c71ce79ce3fe00003fff80
def etat150 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur91]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne165 : Ban 50 5 etat150 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur92 : ℕ := 0x284104408420020000000180
def etat151 : List ℕ := [valeur92,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne166 : Ban 50 5 etat151 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur93 : ℕ := 0xdc18618a718c3fc00000ffe00
def etat152 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur93,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne167 : Ban 50 5 etat152 := viaDirect (by decide +kernel) (by decide +kernel)
def etat153 : List ℕ := [valeur81,valeur6,valeur1,valeur2,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne168 : Ban 50 5 etat153 := viaDirect (by decide +kernel) (by decide +kernel)
def etat154 : List ℕ := [valeur81,valeur1,valeur2,valeur3,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne169 : Ban 50 5 etat154 := viaDirect (by decide +kernel) (by decide +kernel)
def etat155 : List ℕ := [valeur81,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne170 : Ban 50 6 etat155 := viaBranch (ws := [etat138,etat139,etat140,etat141,etat96,etat142,etat143,etat144,etat145,etat146,etat147,etat148,etat149,etat150,etat151,etat152,etat153,etat154]) (consBan borne153 (consBan borne154 (consBan borne155 (consBan borne156 (consBan borne107 (consBan borne157 (consBan borne158 (consBan borne159 (consBan borne160 (consBan borne161 (consBan borne162 (consBan borne163 (consBan borne164 (consBan borne165 (consBan borne166 (consBan borne167 (consBan borne168 (consBan borne169 (nilBan 50 5))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur94 : ℕ := 0x1420821042100100000c0180
def etat156 : List ℕ := [valeur94,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne171 : Ban 50 6 etat156 := viaPerm proj2 proj2 borne170 (by decide +kernel) (by decide +kernel)
def etat157 : List ℕ := [valeur94,valeur6,valeur1,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne172 : Ban 50 5 etat157 := viaDirect (by decide +kernel) (by decide +kernel)
def etat158 : List ℕ := [valeur94,valeur1,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne173 : Ban 50 5 etat158 := viaDirect (by decide +kernel) (by decide +kernel)
def etat159 : List ℕ := [valeur34,valeur6,valeur1,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne174 : Ban 50 5 etat159 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur95 : ℕ := 0x480820922084500000fc0067f
def etat160 : List ℕ := [valeur1,valeur95,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne175 : Ban 50 5 etat160 := viaDirect (by decide +kernel) (by decide +kernel)
def etat161 : List ℕ := [valeur6,valeur1,valeur95,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne176 : Ban 50 5 etat161 := viaDirect (by decide +kernel) (by decide +kernel)
def etat162 : List ℕ := [valeur1,valeur2,valeur33,valeur3,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne177 : Ban 50 5 etat162 := viaDirect (by decide +kernel) (by decide +kernel)
def etat163 : List ℕ := [valeur36,valeur1,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne178 : Ban 50 5 etat163 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur96 : ℕ := 0xde9c75ce79cebfe03f03fffff
def etat164 : List ℕ := [valeur63,valeur1,valeur2,valeur4,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne179 : Ban 50 4 etat164 := viaDirect (by decide +kernel) (by decide +kernel)
def etat165 : List ℕ := [valeur6,valeur19,valeur2,valeur4,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne180 : Ban 50 4 etat165 := viaDirect (by decide +kernel) (by decide +kernel)
def etat166 : List ℕ := [valeur6,valeur1,valeur2,valeur66,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne181 : Ban 50 4 etat166 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur97 : ℕ := 0xdd5a69bb75ad7fd000fffffff
def etat167 : List ℕ := [valeur20,valeur6,valeur1,valeur97,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne182 : Ban 50 4 etat167 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur98 : ℕ := 0xdfde7dff7deffff03ffffffff
def etat168 : List ℕ := [valeur20,valeur6,valeur1,valeur4,valeur98]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne183 : Ban 50 4 etat168 := viaDirect (by decide +kernel) (by decide +kernel)
def etat169 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur4,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne184 : Ban 50 5 etat169 := viaBranch (ws := [etat164,etat165,etat166,etat167,etat168]) (consBan borne179 (consBan borne180 (consBan borne181 (consBan borne182 (consBan borne183 (nilBan 50 4)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat170 : List ℕ := [valeur24,valeur1,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne185 : Ban 50 5 etat170 := viaPerm proj7 proj7 borne184 (by decide +kernel) (by decide +kernel)
def etat171 : List ℕ := [valeur1,valeur2,valeur33,valeur3,valeur70,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne186 : Ban 50 5 etat171 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur99 : ℕ := 0x696aaab3a4b57ffffffcc07ff
def etat172 : List ℕ := [valeur6,valeur1,valeur33,valeur99,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne187 : Ban 50 5 etat172 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur100 : ℕ := 0x494a28b324a540000000c07ff
def etat173 : List ℕ := [valeur6,valeur1,valeur100,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne188 : Ban 50 5 etat173 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur101 : ℕ := 0x103fc0fc00000
def etat174 : List ℕ := [valeur101,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne189 : Ban 50 5 etat174 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur102 : ℕ := 0x2020820080102fc03f0000000
def etat175 : List ℕ := [valeur6,valeur102,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne190 : Ban 50 5 etat175 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur103 : ℕ := 0x4bcf38f72ee740000003fffff
def etat176 : List ℕ := [valeur6,valeur1,valeur2,valeur103,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne191 : Ban 50 5 etat176 := viaDirect (by decide +kernel) (by decide +kernel)
def etat177 : List ℕ := [valeur34,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne192 : Ban 50 5 etat177 := viaDirect (by decide +kernel) (by decide +kernel)
def etat178 : List ℕ := [valeur20,valeur6,valeur1,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne193 : Ban 50 5 etat178 := viaPerm proj3 proj3 borne184 (by decide +kernel) (by decide +kernel)
def valeur104 : ℕ := 0x9294554c494aa0203f0300000
def etat179 : List ℕ := [valeur6,valeur1,valeur33,valeur104,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne194 : Ban 50 5 etat179 := viaDirect (by decide +kernel) (by decide +kernel)
def etat180 : List ℕ := [valeur6,valeur1,valeur33,valeur3,valeur4,valeur97]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne195 : Ban 50 5 etat180 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur105 : ℕ := 0x14208310421401000fc001ff
def etat181 : List ℕ := [valeur105,valeur6,valeur1,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne196 : Ban 50 5 etat181 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur106 : ℕ := 0x2841044084200200003007ff
def etat182 : List ℕ := [valeur106,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne197 : Ban 50 5 etat182 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur107 : ℕ := 0xdbdf7dff6feff03ffffffffff
def etat183 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur107,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne198 : Ban 50 5 etat183 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur108 : ℕ := 0x494b28b326a5501fc0fcff800
def etat184 : List ℕ := [valeur6,valeur1,valeur2,valeur108,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne199 : Ban 50 5 etat184 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur109 : ℕ := 0x901045084108a0003f0000000
def etat185 : List ℕ := [valeur6,valeur1,valeur2,valeur109,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne200 : Ban 50 5 etat185 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur110 : ℕ := 0x48082082208410000003ffe00
def etat186 : List ℕ := [valeur6,valeur1,valeur110,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne201 : Ban 50 5 etat186 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur111 : ℕ := 0xdfdf79ff7fef7fffc0fffffff
def etat187 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur111]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne202 : Ban 50 5 etat187 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur112 : ℕ := 0x3c718750e63403fc0fc001ff
def etat188 : List ℕ := [valeur6,valeur112,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne203 : Ban 50 5 etat188 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur113 : ℕ := 0x9410410851082fc0000000000
def etat189 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur113,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne204 : Ban 50 5 etat189 := viaDirect (by decide +kernel) (by decide +kernel)
def etat190 : List ℕ := [valeur6,valeur1,valeur2,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne205 : Ban 50 6 etat190 := viaBranch (ws := [etat45,etat114,etat157,etat158,etat159,etat160,etat161,etat162,etat163,etat170,etat171,etat172,etat173,etat174,etat55,etat175,etat176,etat177,etat178,etat179,etat180,etat181,etat182,etat183,etat184,etat185,etat186,etat187,etat188,etat189]) (consBan borne53 (consBan borne125 (consBan borne172 (consBan borne173 (consBan borne174 (consBan borne175 (consBan borne176 (consBan borne177 (consBan borne178 (consBan borne185 (consBan borne186 (consBan borne187 (consBan borne188 (consBan borne189 (consBan borne63 (consBan borne190 (consBan borne191 (consBan borne192 (consBan borne193 (consBan borne194 (consBan borne195 (consBan borne196 (consBan borne197 (consBan borne198 (consBan borne199 (consBan borne200 (consBan borne201 (consBan borne202 (consBan borne203 (consBan borne204 (nilBan 50 5))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur114 : ℕ := 0x3c71c650e63803fff03ff9ff
def etat191 : List ℕ := [valeur114,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne206 : Ban 50 5 etat191 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur115 : ℕ := 0x2841444084280203f00001ff
def etat192 : List ℕ := [valeur115,valeur114,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne207 : Ban 50 5 etat192 := viaDirect (by decide +kernel) (by decide +kernel)
def etat193 : List ℕ := [valeur6,valeur114,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne208 : Ban 50 5 etat193 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur116 : ℕ := 0x400000080003f000007f
def etat194 : List ℕ := [valeur116,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne209 : Ban 50 5 etat194 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur117 : ℕ := 0x14308210621001fc003ff800
def etat195 : List ℕ := [valeur117,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne210 : Ban 50 5 etat195 := viaDirect (by decide +kernel) (by decide +kernel)
def etat196 : List ℕ := [valeur117,valeur115,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne211 : Ban 50 5 etat196 := viaDirect (by decide +kernel) (by decide +kernel)
def etat197 : List ℕ := [valeur117,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne212 : Ban 50 5 etat197 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur118 : ℕ := 0x22a496448852bffffffc001ff
def etat198 : List ℕ := [valeur6,valeur1,valeur118,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne213 : Ban 50 5 etat198 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur119 : ℕ := 0x2841444084280000000001ff
def etat199 : List ℕ := [valeur119,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne214 : Ban 50 5 etat199 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur120 : ℕ := 0x2020820080103fdfc0fc00000
def etat200 : List ℕ := [valeur6,valeur120,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne215 : Ban 50 5 etat200 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur121 : ℕ := 0x1ff
def etat201 : List ℕ := [valeur121,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne216 : Ban 50 5 etat201 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur122 : ℕ := 0x4bce3cf72ce7d0303ffcc07ff
def etat202 : List ℕ := [valeur6,valeur1,valeur2,valeur122,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne217 : Ban 50 5 etat202 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur123 : ℕ := 0x2841444084280203f0000000
def etat203 : List ℕ := [valeur123,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne218 : Ban 50 5 etat203 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur124 : ℕ := 0x494a28b324a5501000fcc0600
def etat204 : List ℕ := [valeur6,valeur1,valeur124,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne219 : Ban 50 5 etat204 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur125 : ℕ := 0x9010410841082000000300600
def etat205 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur125,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne220 : Ban 50 5 etat205 := viaDirect (by decide +kernel) (by decide +kernel)
def etat206 : List ℕ := [valeur6,valeur1,valeur2,valeur125,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne221 : Ban 50 5 etat206 := viaDirect (by decide +kernel) (by decide +kernel)
def etat207 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur3,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne222 : Ban 50 5 etat207 := viaDirect (by decide +kernel) (by decide +kernel)
def etat208 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne223 : Ban 50 5 etat208 := viaDirect (by decide +kernel) (by decide +kernel)
def etat209 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne224 : Ban 50 5 etat209 := viaDirect (by decide +kernel) (by decide +kernel)
def etat210 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur89,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne225 : Ban 50 5 etat210 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur126 : ℕ := 0xb2b4d74cc95abfffffff007ff
def etat211 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur126,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne226 : Ban 50 5 etat211 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur127 : ℕ := 0x9294554c494a80000003007ff
def etat212 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur127,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne227 : Ban 50 5 etat212 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur128 : ℕ := 0x2841444084280203f00007ff
def etat213 : List ℕ := [valeur128,valeur6,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne228 : Ban 50 4 etat213 := viaDirect (by decide +kernel) (by decide +kernel)
def etat214 : List ℕ := [valeur115,valeur63,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne229 : Ban 50 4 etat214 := viaDirect (by decide +kernel) (by decide +kernel)
def etat215 : List ℕ := [valeur115,valeur6,valeur19,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne230 : Ban 50 4 etat215 := viaDirect (by decide +kernel) (by decide +kernel)
def etat216 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur66]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne231 : Ban 50 4 etat216 := viaDirect (by decide +kernel) (by decide +kernel)
def etat217 : List ℕ := [valeur20,valeur114,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne232 : Ban 50 4 etat217 := viaDirect (by decide +kernel) (by decide +kernel)
def etat218 : List ℕ := [valeur20,valeur6,valeur1,valeur122,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne233 : Ban 50 4 etat218 := viaDirect (by decide +kernel) (by decide +kernel)
def etat219 : List ℕ := [valeur20,valeur115,valeur6,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne234 : Ban 50 5 etat219 := viaBranch (ws := [etat213,etat214,etat215,etat216,etat217,etat218]) (consBan borne228 (consBan borne229 (consBan borne230 (consBan borne231 (consBan borne232 (consBan borne233 (nilBan 50 4))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur129 : ℕ := 0x494a28b324a5501000fcc0000
def etat220 : List ℕ := [valeur115,valeur6,valeur1,valeur129,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne235 : Ban 50 5 etat220 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur130 : ℕ := 0x4c08208230841fc00000ff800
def etat221 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur130]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne236 : Ban 50 5 etat221 := viaDirect (by decide +kernel) (by decide +kernel)
def etat222 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur130,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne237 : Ban 50 5 etat222 := viaDirect (by decide +kernel) (by decide +kernel)
def etat223 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur130,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne238 : Ban 50 5 etat223 := viaDirect (by decide +kernel) (by decide +kernel)
def etat224 : List ℕ := [valeur115,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne239 : Ban 50 6 etat224 := viaBranch (ws := [etat151,etat191,etat192,etat193,etat194,etat195,etat196,etat197,etat129,etat198,etat199,etat200,etat201,etat202,etat203,etat204,etat205,etat206,etat207,etat208,etat209,etat210,etat211,etat212,etat219,etat220,etat221,etat222,etat223]) (consBan borne166 (consBan borne206 (consBan borne207 (consBan borne208 (consBan borne209 (consBan borne210 (consBan borne211 (consBan borne212 (consBan borne142 (consBan borne213 (consBan borne214 (consBan borne215 (consBan borne216 (consBan borne217 (consBan borne218 (consBan borne219 (consBan borne220 (consBan borne221 (consBan borne222 (consBan borne223 (consBan borne224 (consBan borne225 (consBan borne226 (consBan borne227 (consBan borne234 (consBan borne235 (consBan borne236 (consBan borne237 (consBan borne238 (nilBan 50 5)))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne240 : Ban 50 6 etat177 := viaPerm proj7 proj7 borne239 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne241 : Ban 50 6 etat161 := viaPerm proj3 proj3 borne239 (by decide +kernel) (by decide +kernel)
def etat225 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne242 : Ban 50 6 etat225 := viaPerm proj2 proj2 borne205 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne243 : Ban 50 6 etat139 := viaPerm proj6 proj5 borne239 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne244 : Ban 50 6 etat148 := viaPerm proj1 proj1 borne239 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne245 : Ban 50 5 etat100 := viaDirect (by decide +kernel) (by decide +kernel)
def etat226 : List ℕ := [valeur63,valeur1,valeur2,valeur3,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne246 : Ban 50 4 etat226 := viaDirect (by decide +kernel) (by decide +kernel)
def etat227 : List ℕ := [valeur64,valeur1,valeur2,valeur3,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne247 : Ban 50 4 etat227 := viaDirect (by decide +kernel) (by decide +kernel)
def etat228 : List ℕ := [valeur6,valeur19,valeur2,valeur3,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne248 : Ban 50 4 etat228 := viaDirect (by decide +kernel) (by decide +kernel)
def etat229 : List ℕ := [valeur20,valeur6,valeur1,valeur67,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne249 : Ban 50 4 etat229 := viaDirect (by decide +kernel) (by decide +kernel)
def etat230 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur3,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne250 : Ban 50 5 etat230 := viaBranch (ws := [etat226,etat227,etat228,etat104,etat229]) (consBan borne246 (consBan borne247 (consBan borne248 (consBan borne115 (consBan borne249 (nilBan 50 4)))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat231 : List ℕ := [valeur20,valeur63,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne251 : Ban 50 5 etat231 := viaPerm proj1 proj1 borne250 (by decide +kernel) (by decide +kernel)
def etat232 : List ℕ := [valeur6,valeur63,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne252 : Ban 50 5 etat232 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur131 : ℕ := 0x67f
def etat233 : List ℕ := [valeur131,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne253 : Ban 50 5 etat233 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne254 : Ban 50 5 etat101 := viaDirect (by decide +kernel) (by decide +kernel)
def etat234 : List ℕ := [valeur20,valeur64,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne255 : Ban 50 5 etat234 := viaDirect (by decide +kernel) (by decide +kernel)
def etat235 : List ℕ := [valeur64,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne256 : Ban 50 5 etat235 := viaDirect (by decide +kernel) (by decide +kernel)
def etat236 : List ℕ := [valeur6,valeur19,valeur33,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne257 : Ban 50 4 etat236 := viaDirect (by decide +kernel) (by decide +kernel)
def etat237 : List ℕ := [valeur6,valeur19,valeur95,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne258 : Ban 50 4 etat237 := viaDirect (by decide +kernel) (by decide +kernel)
def etat238 : List ℕ := [valeur6,valeur19,valeur2,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne259 : Ban 50 4 etat238 := viaDirect (by decide +kernel) (by decide +kernel)
def etat239 : List ℕ := [valeur6,valeur19,valeur2,valeur89,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne260 : Ban 50 4 etat239 := viaDirect (by decide +kernel) (by decide +kernel)
def etat240 : List ℕ := [valeur17,valeur6,valeur19,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne261 : Ban 50 4 etat240 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur132 : ℕ := 0x2020820080102fefff0000000
def etat241 : List ℕ := [valeur6,valeur132,valeur19,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne262 : Ban 50 4 etat241 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur133 : ℕ := 0x20203f00007ff
def etat242 : List ℕ := [valeur133,valeur6,valeur19,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne263 : Ban 50 4 etat242 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur134 : ℕ := 0x2020820080101fdfc0fc00000
def etat243 : List ℕ := [valeur6,valeur134,valeur19,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne264 : Ban 50 4 etat243 := viaDirect (by decide +kernel) (by decide +kernel)
def etat244 : List ℕ := [valeur6,valeur19,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne265 : Ban 50 4 etat244 := viaDirect (by decide +kernel) (by decide +kernel)
def etat245 : List ℕ := [valeur6,valeur19,valeur2,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne266 : Ban 50 4 etat245 := viaDirect (by decide +kernel) (by decide +kernel)
def etat246 : List ℕ := [valeur6,valeur19,valeur3,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne267 : Ban 50 4 etat246 := viaDirect (by decide +kernel) (by decide +kernel)
def etat247 : List ℕ := [valeur6,valeur19,valeur129,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne268 : Ban 50 4 etat247 := viaDirect (by decide +kernel) (by decide +kernel)
def etat248 : List ℕ := [valeur6,valeur19,valeur2,valeur104,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne269 : Ban 50 4 etat248 := viaDirect (by decide +kernel) (by decide +kernel)
def etat249 : List ℕ := [valeur6,valeur19,valeur3,valeur4,valeur97]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne270 : Ban 50 4 etat249 := viaDirect (by decide +kernel) (by decide +kernel)
def etat250 : List ℕ := [valeur105,valeur6,valeur19,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne271 : Ban 50 4 etat250 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne272 : Ban 50 5 etat102 := viaBranch (ws := [etat236,etat237,etat238,etat239,etat240,etat241,etat242,etat243,etat244,etat245,etat246,etat247,etat248,etat249,etat250,etat165,etat215]) (consBan borne257 (consBan borne258 (consBan borne259 (consBan borne260 (consBan borne261 (consBan borne262 (consBan borne263 (consBan borne264 (consBan borne265 (consBan borne266 (consBan borne267 (consBan borne268 (consBan borne269 (consBan borne270 (consBan borne271 (consBan borne180 (consBan borne230 (nilBan 50 4)))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat251 : List ℕ := [valeur63,valeur19,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne273 : Ban 50 4 etat251 := viaDirect (by decide +kernel) (by decide +kernel)
def etat252 : List ℕ := [valeur64,valeur19,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne274 : Ban 50 4 etat252 := viaDirect (by decide +kernel) (by decide +kernel)
def etat253 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne275 : Ban 50 4 etat253 := viaDirect (by decide +kernel) (by decide +kernel)
def etat254 : List ℕ := [valeur6,valeur19,valeur2,valeur3,valeur66]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne276 : Ban 50 4 etat254 := viaDirect (by decide +kernel) (by decide +kernel)
def etat255 : List ℕ := [valeur20,valeur6,valeur19,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne277 : Ban 50 4 etat255 := viaDirect (by decide +kernel) (by decide +kernel)
def etat256 : List ℕ := [valeur20,valeur6,valeur19,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne278 : Ban 50 5 etat256 := viaBranch (ws := [etat251,etat252,etat253,etat247,etat248,etat228,etat254,etat255]) (consBan borne273 (consBan borne274 (consBan borne275 (consBan borne268 (consBan borne269 (consBan borne248 (consBan borne276 (consBan borne277 (nilBan 50 4))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def valeur135 : ℕ := 0x20203f0000000
def etat257 : List ℕ := [valeur135,valeur6,valeur19,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne279 : Ban 50 4 etat257 := viaDirect (by decide +kernel) (by decide +kernel)
def etat258 : List ℕ := [valeur133,valeur6,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne280 : Ban 50 4 etat258 := viaDirect (by decide +kernel) (by decide +kernel)
def etat259 : List ℕ := [valeur6,valeur1,valeur19,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne281 : Ban 50 4 etat259 := viaDirect (by decide +kernel) (by decide +kernel)
def etat260 : List ℕ := [valeur6,valeur1,valeur19,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne282 : Ban 50 5 etat260 := viaBranch (ws := [etat24,etat241,etat257,etat243,etat23,etat258,etat259]) (consBan borne32 (consBan borne262 (consBan borne279 (consBan borne264 (consBan borne31 (consBan borne280 (consBan borne281 (nilBan 50 4)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat261 : List ℕ := [valeur20,valeur6,valeur1,valeur129,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne283 : Ban 50 5 etat261 := viaDirect (by decide +kernel) (by decide +kernel)
def etat262 : List ℕ := [valeur6,valeur1,valeur129,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne284 : Ban 50 5 etat262 := viaDirect (by decide +kernel) (by decide +kernel)
def etat263 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur104,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne285 : Ban 50 5 etat263 := viaDirect (by decide +kernel) (by decide +kernel)
def etat264 : List ℕ := [valeur6,valeur1,valeur2,valeur104,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne286 : Ban 50 5 etat264 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur136 : ℕ := 0x600
def etat265 : List ℕ := [valeur136,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne287 : Ban 50 5 etat265 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne288 : Ban 50 5 etat103 := viaDirect (by decide +kernel) (by decide +kernel)
def etat266 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur65]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne289 : Ban 50 5 etat266 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne290 : Ban 50 5 etat104 := viaDirect (by decide +kernel) (by decide +kernel)
def etat267 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur3,valeur66]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne291 : Ban 50 5 etat267 := viaDirect (by decide +kernel) (by decide +kernel)
def etat268 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur66,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne292 : Ban 50 5 etat268 := viaDirect (by decide +kernel) (by decide +kernel)
def etat269 : List ℕ := [valeur20,valeur6,valeur1,valeur95,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne293 : Ban 50 5 etat269 := viaPerm proj3 proj3 borne234 (by decide +kernel) (by decide +kernel)
def etat270 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur35,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne294 : Ban 50 5 etat270 := viaPerm proj1 proj1 borne184 (by decide +kernel) (by decide +kernel)
def etat271 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur89,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne295 : Ban 50 5 etat271 := viaPerm proj1 proj1 borne234 (by decide +kernel) (by decide +kernel)
def etat272 : List ℕ := [valeur20,valeur6,valeur132,valeur1,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne296 : Ban 50 5 etat272 := viaDirect (by decide +kernel) (by decide +kernel)
def etat273 : List ℕ := [valeur20,valeur135,valeur6,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne297 : Ban 50 5 etat273 := viaPerm proj2 proj2 borne36 (by decide +kernel) (by decide +kernel)
def etat274 : List ℕ := [valeur20,valeur6,valeur134,valeur1,valeur2,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne298 : Ban 50 5 etat274 := viaDirect (by decide +kernel) (by decide +kernel)
def etat275 : List ℕ := [valeur20,valeur63,valeur1,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne299 : Ban 50 4 etat275 := viaDirect (by decide +kernel) (by decide +kernel)
def etat276 : List ℕ := [valeur20,valeur64,valeur1,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne300 : Ban 50 4 etat276 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur137 : ℕ := 0xdbde7dff6deff0303fffc0000
def etat277 : List ℕ := [valeur6,valeur1,valeur137,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne301 : Ban 50 4 etat277 := viaDirect (by decide +kernel) (by decide +kernel)
def etat278 : List ℕ := [valeur20,valeur6,valeur1,valeur137,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne302 : Ban 50 4 etat278 := viaDirect (by decide +kernel) (by decide +kernel)
def etat279 : List ℕ := [valeur6,valeur1,valeur137,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne303 : Ban 50 4 etat279 := viaDirect (by decide +kernel) (by decide +kernel)
def etat280 : List ℕ := [valeur20,valeur6,valeur1,valeur67,valeur66]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne304 : Ban 50 4 etat280 := viaDirect (by decide +kernel) (by decide +kernel)
def etat281 : List ℕ := [valeur20,valeur6,valeur1,valeur107,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne305 : Ban 50 4 etat281 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur138 : ℕ := 0xd818659a618cf0003ffc0067f
def etat282 : List ℕ := [valeur20,valeur6,valeur1,valeur138,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne306 : Ban 50 4 etat282 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur139 : ℕ := 0x30303ffc00000
def etat283 : List ℕ := [valeur20,valeur139,valeur6,valeur1,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne307 : Ban 50 4 etat283 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur140 : ℕ := 0x2020820080100fcfc00000000
def etat284 : List ℕ := [valeur20,valeur6,valeur140,valeur1,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne308 : Ban 50 4 etat284 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur141 : ℕ := 0x3c61c750c63c0303ffc001ff
def etat285 : List ℕ := [valeur20,valeur141,valeur6,valeur1,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne309 : Ban 50 4 etat285 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne310 : Ban 50 5 etat105 := viaBranch (ws := [etat275,etat276,etat244,etat255,etat259,etat277,etat278,etat279,etat229,etat280,etat281,etat282,etat283,etat284,etat168,etat285]) (consBan borne299 (consBan borne300 (consBan borne265 (consBan borne277 (consBan borne281 (consBan borne301 (consBan borne302 (consBan borne303 (consBan borne249 (consBan borne304 (consBan borne305 (consBan borne306 (consBan borne307 (consBan borne308 (consBan borne183 (consBan borne309 (nilBan 50 4))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat286 : List ℕ := [valeur20,valeur6,valeur1,valeur2,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne311 : Ban 50 5 etat286 := viaDirect (by decide +kernel) (by decide +kernel)
def etat287 : List ℕ := [valeur20,valeur6,valeur1,valeur3,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne312 : Ban 50 5 etat287 := viaDirect (by decide +kernel) (by decide +kernel)
def etat288 : List ℕ := [valeur20,valeur6,valeur1,valeur3,valeur4,valeur97]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne313 : Ban 50 5 etat288 := viaPerm proj2 proj2 borne184 (by decide +kernel) (by decide +kernel)
def etat289 : List ℕ := [valeur20,valeur105,valeur6,valeur1,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne314 : Ban 50 5 etat289 := viaPerm proj2 proj2 borne234 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne315 : Ban 50 6 etat106 := viaBranch (ws := [etat143,etat100,etat231,etat232,etat233,etat101,etat234,etat235,etat102,etat256,etat260,etat261,etat262,etat263,etat264,etat265,etat103,etat230,etat266,etat201,etat104,etat267,etat268,etat178,etat269,etat270,etat271,etat28,etat272,etat273,etat274,etat105,etat286,etat287,etat288,etat289,etat169,etat219]) (consBan borne158 (consBan borne245 (consBan borne251 (consBan borne252 (consBan borne253 (consBan borne254 (consBan borne255 (consBan borne256 (consBan borne272 (consBan borne278 (consBan borne282 (consBan borne283 (consBan borne284 (consBan borne285 (consBan borne286 (consBan borne287 (consBan borne288 (consBan borne250 (consBan borne289 (consBan borne216 (consBan borne290 (consBan borne291 (consBan borne292 (consBan borne193 (consBan borne293 (consBan borne294 (consBan borne295 (consBan borne36 (consBan borne296 (consBan borne297 (consBan borne298 (consBan borne310 (consBan borne311 (consBan borne312 (consBan borne313 (consBan borne314 (consBan borne184 (consBan borne234 (nilBan 50 5))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne316 : Ban 50 6 etat107 := viaPerm proj4 proj4 borne315 (by decide +kernel) (by decide +kernel)
def valeur142 : ℕ := 0x3c618650c6300300003c0180
def etat290 : List ℕ := [valeur142,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne317 : Ban 50 5 etat290 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur143 : ℕ := 0x100000200000fc0003f800
def etat291 : List ℕ := [valeur143,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne318 : Ban 50 5 etat291 := viaDirect (by decide +kernel) (by decide +kernel)
def etat292 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur138,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne319 : Ban 50 5 etat292 := viaDirect (by decide +kernel) (by decide +kernel)
def etat293 : List ℕ := [valeur6,valeur1,valeur99,valeur3,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne320 : Ban 50 5 etat293 := viaDirect (by decide +kernel) (by decide +kernel)
def etat294 : List ℕ := [valeur6,valeur1,valeur100,valeur3,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne321 : Ban 50 5 etat294 := viaDirect (by decide +kernel) (by decide +kernel)
def etat295 : List ℕ := [valeur6,valeur1,valeur2,valeur126,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne322 : Ban 50 5 etat295 := viaDirect (by decide +kernel) (by decide +kernel)
def etat296 : List ℕ := [valeur6,valeur1,valeur2,valeur127,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne323 : Ban 50 5 etat296 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur144 : ℕ := 0x494a28b324a57fffc0fcc07ff
def etat297 : List ℕ := [valeur6,valeur1,valeur144,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne324 : Ban 50 4 etat297 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur145 : ℕ := 0x494a28b324a5400000fcc07ff
def etat298 : List ℕ := [valeur6,valeur1,valeur145,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne325 : Ban 50 4 etat298 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur146 : ℕ := 0x9294554c494abfffff03007ff
def etat299 : List ℕ := [valeur6,valeur1,valeur2,valeur146,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne326 : Ban 50 4 etat299 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur147 : ℕ := 0x9294554c494a80003f03007ff
def etat300 : List ℕ := [valeur6,valeur1,valeur2,valeur147,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne327 : Ban 50 4 etat300 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur148 : ℕ := 0xdc18618a718c3fffc003ffe00
def etat301 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur148]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne328 : Ban 50 4 etat301 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur149 : ℕ := 0x3fffc00000000
def etat302 : List ℕ := [valeur24,valeur149,valeur1,valeur2,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne329 : Ban 50 4 etat302 := viaDirect (by decide +kernel) (by decide +kernel)
def etat303 : List ℕ := [valeur149,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne330 : Ban 50 5 etat303 := viaBranch (ws := [etat0,etat297,etat298,etat299,etat300,etat301,etat302]) (consBan borne86 (consBan borne324 (consBan borne325 (consBan borne326 (consBan borne327 (consBan borne328 (consBan borne329 (nilBan 50 4)))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat304 : List ℕ := [valeur139,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne331 : Ban 50 5 etat304 := viaPerm proj4 proj4 borne330 (by decide +kernel) (by decide +kernel)
def valeur150 : ℕ := 0xfbfeffffedffffffffffc07ff
def etat305 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur150]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne332 : Ban 50 5 etat305 := viaDirect (by decide +kernel) (by decide +kernel)
def etat306 : List ℕ := [valeur6,valeur140,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne333 : Ban 50 5 etat306 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur151 : ℕ := 0xdbde7dff6defc0000003c07ff
def etat307 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur151,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne334 : Ban 50 5 etat307 := viaDirect (by decide +kernel) (by decide +kernel)
def etat308 : List ℕ := [valeur6,valeur1,valeur129,valeur2,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne335 : Ban 50 5 etat308 := viaDirect (by decide +kernel) (by decide +kernel)
def etat309 : List ℕ := [valeur6,valeur1,valeur104,valeur3,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne336 : Ban 50 5 etat309 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur152 : ℕ := 0xd818618a618c30000003c0600
def etat310 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur152,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne337 : Ban 50 5 etat310 := viaDirect (by decide +kernel) (by decide +kernel)
def etat311 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur98]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne338 : Ban 50 5 etat311 := viaDirect (by decide +kernel) (by decide +kernel)
def etat312 : List ℕ := [valeur141,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne339 : Ban 50 5 etat312 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur153 : ℕ := 0x400000010000fc000003f800
def etat313 : List ℕ := [valeur6,valeur153,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne340 : Ban 50 5 etat313 := viaDirect (by decide +kernel) (by decide +kernel)
def etat314 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur67,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne341 : Ban 50 6 etat314 := viaBranch (ws := [etat290,etat183,etat291,etat292,etat293,etat294,etat295,etat296,etat304,etat305,etat306,etat307,etat105,etat286,etat287,etat308,etat309,etat264,etat262,etat310,etat311,etat312,etat313]) (consBan borne317 (consBan borne198 (consBan borne318 (consBan borne319 (consBan borne320 (consBan borne321 (consBan borne322 (consBan borne323 (consBan borne331 (consBan borne332 (consBan borne333 (consBan borne334 (consBan borne310 (consBan borne311 (consBan borne312 (consBan borne335 (consBan borne336 (consBan borne286 (consBan borne284 (consBan borne337 (consBan borne338 (consBan borne339 (consBan borne340 (nilBan 50 5)))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def etat315 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur37]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne342 : Ban 50 6 etat315 := viaPerm proj4 proj4 borne341 (by decide +kernel) (by decide +kernel)
def etat316 : List ℕ := [valeur24,valeur25,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne343 : Ban 50 5 etat316 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur154 : ℕ := 0x23e79a658e733ffffffc00180
def etat317 : List ℕ := [valeur6,valeur1,valeur154,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne344 : Ban 50 5 etat317 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur155 : ℕ := 0x142082104210010000000180
def etat318 : List ℕ := [valeur155,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne345 : Ban 50 5 etat318 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur156 : ℕ := 0x4bcf38f72ee7503fc0fcc07ff
def etat319 : List ℕ := [valeur6,valeur1,valeur2,valeur156,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne346 : Ban 50 5 etat319 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur157 : ℕ := 0x28510440a42002fc00000000
def etat320 : List ℕ := [valeur157,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne347 : Ban 50 5 etat320 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur158 : ℕ := 0x480820922084500000fcc067f
def etat321 : List ℕ := [valeur6,valeur1,valeur158,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne348 : Ban 50 5 etat321 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur159 : ℕ := 0x93d75d6d4f6ba03fff03007ff
def etat322 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur159,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne349 : Ban 50 5 etat322 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur160 : ℕ := 0x14308210621001fc00000000
def etat323 : List ℕ := [valeur160,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne350 : Ban 50 5 etat323 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur161 : ℕ := 0x901045084108a0003f030067f
def etat324 : List ℕ := [valeur6,valeur1,valeur2,valeur161,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne351 : Ban 50 5 etat324 := viaDirect (by decide +kernel) (by decide +kernel)
def etat325 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur3,valeur37]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne352 : Ban 50 5 etat325 := viaDirect (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne353 : Ban 50 5 etat315 := viaDirect (by decide +kernel) (by decide +kernel)
def etat326 : List ℕ := [valeur25,valeur1,valeur2,valeur3,valeur70]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne354 : Ban 50 5 etat326 := viaDirect (by decide +kernel) (by decide +kernel)
def etat327 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur3,valeur70]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne355 : Ban 50 5 etat327 := viaDirect (by decide +kernel) (by decide +kernel)
def etat328 : List ℕ := [valeur25,valeur1,valeur2,valeur3,valeur70,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne356 : Ban 50 5 etat328 := viaDirect (by decide +kernel) (by decide +kernel)
def etat329 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur3,valeur97]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne357 : Ban 50 5 etat329 := viaDirect (by decide +kernel) (by decide +kernel)
def valeur162 : ℕ := 0x9410410851082fc000033f800
def etat330 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur3,valeur162]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne358 : Ban 50 5 etat330 := viaDirect (by decide +kernel) (by decide +kernel)
def etat331 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur3,valeur96]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne359 : Ban 50 5 etat331 := viaDirect (by decide +kernel) (by decide +kernel)
def etat332 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur130,valeur3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne360 : Ban 50 5 etat332 := viaDirect (by decide +kernel) (by decide +kernel)
def etat333 : List ℕ := [valeur25,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne361 : Ban 50 6 etat333 := viaBranch (ws := [etat316,etat107,etat39,etat317,etat109,etat44,etat318,etat319,etat320,etat321,etat151,etat322,etat323,etat324,etat325,etat315,etat50,etat119,etat326,etat327,etat328,etat30,etat124,etat329,etat330,etat331,etat332]) (consBan borne343 (consBan borne118 (consBan borne101 (consBan borne344 (consBan borne120 (consBan borne52 (consBan borne345 (consBan borne346 (consBan borne347 (consBan borne348 (consBan borne166 (consBan borne349 (consBan borne350 (consBan borne351 (consBan borne352 (consBan borne353 (consBan borne58 (consBan borne130 (consBan borne354 (consBan borne355 (consBan borne356 (consBan borne38 (consBan borne136 (consBan borne357 (consBan borne358 (consBan borne359 (consBan borne360 (nilBan 50 5)))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne362 : Ban 50 6 etat110 := viaPerm proj1 proj1 borne361 (by decide +kernel) (by decide +kernel)
def etat334 : List ℕ := [valeur18,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne363 : Ban 50 6 etat334 := viaPerm proj5 proj6 borne46 (by decide +kernel) (by decide +kernel)
def etat335 : List ℕ := [valeur6,valeur1,valeur2,valeur99,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne364 : Ban 50 6 etat335 := viaPerm proj4 proj4 borne99 (by decide +kernel) (by decide +kernel)
def etat336 : List ℕ := [valeur6,valeur132,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne365 : Ban 50 6 etat336 := viaPerm proj5 proj6 borne151 (by decide +kernel) (by decide +kernel)
def etat337 : List ℕ := [valeur6,valeur1,valeur100,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne366 : Ban 50 6 etat337 := viaPerm proj4 proj4 borne131 (by decide +kernel) (by decide +kernel)
def etat338 : List ℕ := [valeur135,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne367 : Ban 50 6 etat338 := viaPerm proj4 proj4 borne46 (by decide +kernel) (by decide +kernel)
def etat339 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur126,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne368 : Ban 50 6 etat339 := viaPerm proj5 proj6 borne99 (by decide +kernel) (by decide +kernel)
def etat340 : List ℕ := [valeur6,valeur134,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne369 : Ban 50 6 etat340 := viaPerm proj4 proj4 borne151 (by decide +kernel) (by decide +kernel)
def etat341 : List ℕ := [valeur6,valeur1,valeur2,valeur127,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne370 : Ban 50 6 etat341 := viaPerm proj5 proj6 borne131 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne371 : Ban 50 6 etat134 := viaPerm proj1 proj1 borne99 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne372 : Ban 50 6 etat22 := viaPerm proj1 proj1 borne131 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne373 : Ban 50 6 etat262 := viaPerm proj4 proj4 borne361 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne374 : Ban 50 6 etat264 := viaPerm proj5 proj6 borne361 (by decide +kernel) (by decide +kernel)
def valeur163 : ℕ := 0x48082082208410000000c0600
def etat342 : List ℕ := [valeur6,valeur1,valeur163,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne375 : Ban 50 6 etat342 := viaPerm proj3 proj3 borne170 (by decide +kernel) (by decide +kernel)
def etat343 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur4,valeur97]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne376 : Ban 50 6 etat343 := viaPerm proj1 proj1 borne205 (by decide +kernel) (by decide +kernel)
def etat344 : List ℕ := [valeur105,valeur6,valeur1,valeur2,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne377 : Ban 50 6 etat344 := viaPerm proj2 proj2 borne239 (by decide +kernel) (by decide +kernel)
def etat345 : List ℕ := [valeur6,valeur1,valeur2,valeur3,valeur162,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne378 : Ban 50 6 etat345 := viaPerm proj5 proj6 borne239 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne379 : Ban 50 6 etat206 := viaPerm proj1 proj1 borne170 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne380 : Ban 50 6 etat208 := viaPerm proj3 proj3 borne205 (by decide +kernel) (by decide +kernel)
def etat346 : List ℕ := [valeur6,valeur1,valeur2,valeur130,valeur3,valeur4]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne381 : Ban 50 6 etat346 := viaPerm proj4 proj4 borne239 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne382 : Ban 50 7 etat253 := viaBranch (ws := [etat39,etat90,etat51,etat44,etat156,etat190,etat177,etat161,etat155,etat225,etat139,etat148,etat107,etat315,etat333,etat110,etat334,etat335,etat336,etat337,etat338,etat339,etat340,etat341,etat38,etat134,etat4,etat22,etat106,etat314,etat262,etat264,etat342,etat343,etat344,etat345,etat206,etat208,etat224,etat346]) (consBan borne47 (consBan borne99 (consBan borne131 (consBan borne152 (consBan borne171 (consBan borne205 (consBan borne240 (consBan borne241 (consBan borne170 (consBan borne242 (consBan borne243 (consBan borne244 (consBan borne316 (consBan borne342 (consBan borne361 (consBan borne362 (consBan borne363 (consBan borne364 (consBan borne365 (consBan borne366 (consBan borne367 (consBan borne368 (consBan borne369 (consBan borne370 (consBan borne46 (consBan borne371 (consBan borne151 (consBan borne372 (consBan borne315 (consBan borne341 (consBan borne373 (consBan borne374 (consBan borne375 (consBan borne376 (consBan borne377 (consBan borne378 (consBan borne379 (consBan borne380 (consBan borne239 (consBan borne381 (nilBan 50 6))))))))))))))))))))))))))))))))))))))))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem borne383 : Wide 50 7 etat253 := widen (by decide +kernel) borne382
end PEqualNP.Outside.L_meta_14968.ArchivedClique

namespace PEqualNP.Outside.L_meta_14968.Reduce
namespace CliqueCertificate
open PEqualNP.Outside.L_meta_14968.ArchivedClique

def rows : List Nat := [12,12,12,12,12,12,12,13,13,28,28,17,17,17,17,17,17,17,21,21,25,25,6,6,6,6,6,6,10,10,10,10,10,10,3,3,3,3,3,3,7,11,18,18,18,18,18,18,22,26,4,8,5,9,20,24,2,5,9,20,24,1,5,9,16,20,24,2,5,20,9,24,4,5,9,20,24,2,8,5,9,20,24,2,1,5,9,20,24,2,5,9,5,9,16,20,24,2,20,24]
def pack (w : BitVec 32) := actL rows (canon w).toNat

private def mix (s t : Bool) (a b : BitVec 32) : BitVec 32 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b

private theorem mix_correct (x y : BitVec 32) :
    canon (x &&& y) = mix (x.getLsbD 0) (y.getLsbD 0) (canon x) (canon y) := by
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [canon, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl

private theorem pack_mix (s t : Bool) (a b : BitVec 32) :
    actL rows (mix s t a b).toNat =
      combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and,
    BitVec.toNat_or, actL_and, actL_or, actL_xor]

private theorem canon_signed (s : Bool) (x : BitVec 32) : canon (signed s x) = canon x := by
  cases s
  · rfl
  · exact canon_not x

private theorem pack_gate (s t : Bool) (a b : BitVec 32) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a
  let y := signed t b
  refine ⟨opIndex (x.getLsbD 0) (y.getLsbD 0), op_lt _ _, ?_⟩
  change actL rows (canon (canon (x &&& y))).toNat = _
  rw [canon_canon, mix_correct, pack_mix]
  simp [x, y, pack, canon_signed]

private theorem word_sep : Good 50 (pack cliqueGoal) := by
  intro i hi
  have h : ∀ j : Fin 50, (pack cliqueGoal).testBit j.val ≠ (pack cliqueGoal).testBit (50+j.val) := by decide +kernel
  exact h ⟨i,hi⟩

theorem possible {k S} (h : Path cliqueGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible 50 k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible 50 n av) ?_ ?_ av carry
  · intro v yes
    refine ⟨0,{pack cliqueGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_14968.ArchivedClique.Live.done word_sep (by decide +kernel)
    · simpa using yes cliqueGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible 50 k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩
    cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega

theorem lower (k : Nat) (T : Finset (BitVec 32)) (raw : T ⊆ cliqueRaw.toFinset)
    (path : Path cliqueGoal k T) : 8 ≤ k := by
  by_contra! short
  have tick : ∀ w∈cliqueRaw, pack w ∈ etat253 := by
    simp [cliqueRaw]
    decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact borne383 ⟨n,S,by omega,live,inc⟩

end CliqueCertificate
end PEqualNP.Outside.L_meta_14968.Reduce

theorem PEqualNP.Outside.L_meta_14968 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  apply PEqualNP.Outside.L_meta_14968.Frame.finish
  intro gs o legal computes hn
  obtain ⟨b,n,hlen,live⟩ := PEqualNP.Outside.L_meta_14968.freely_chain gs o legal computes hn
  obtain ⟨k,hk,T,sub,path⟩ := PEqualNP.Outside.L_meta_14968.Reduce.to_four live
  have low := PEqualNP.Outside.L_meta_14968.Reduce.CliqueCertificate.lower k T sub path
  omega
