import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_6746
open PEqualNP.CircuitLowerBounds
def d0 (ws : List Nat) : Nat :=
  ws.foldl (fun a b => (a <<< 72) + b) 0
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def n3 (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def d5 (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def m14 (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem h5 {u d} (h : d5 u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem q22 {u d} (h : d5 u d) (a b : Sig) : bin d a b = bin (m14 d) b a := by
  rcases h5 h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,m14,BitVec.and_comm,BitVec.or_comm]
theorem m39 {u d} (h : d5 u d) : d5 u (m14 d) ∧ m14 (m14 d)=d := by
  rcases h5 h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [m14,d5]
def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ n3 target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), d5 u d ∧ S=insert a (insert b U) ∧
      n3 a ∧ n3 b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : n3 target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : d5 u d)
    (ha : n3 a) (hb : n3 b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : n3 target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : d5 u d)
      (ha : n3 a) (hb : n3 b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)
private lemma v18 {u target k S} (h : Live u target k S) : ∀ a ∈ S, n3 a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma w17 {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma d6 (i) : bit i zero = false := by simp [bit,zero]
private lemma g8 (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma y11 (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma z11 (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem d7 {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩
def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem t38 (a : Sig) : nrm false a = a := rfl
theorem y45 (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,y11]
theorem b42 {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem z45' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem z35 (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,y11,z45']
theorem f33 {a : Sig} (h : n3 (neg a)) : n3 a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem d33 {u} {a : Sig} (h : n3 (nrm u a)) : n3 a := by
  unfold nrm at h
  split at h
  · exact f33 h
  · exact h
def t11 (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem y10 (i) (d : Bool) (a b : Sig) : bit i (t11 d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [t11,bit]
theorem s38 (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (t11 d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply d7
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,y10,ha,hb,z11,y11,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,y11,y10]
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (t11 false) one
  | .or => xs.foldr (t11 true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def f15 (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def j5 (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬n3 v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := j5 w (nrm u v)
private lemma t30 (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply d7 <;> intro i <;>
    simp [z11,d6,g8]
private lemma c42 : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma q15 {w : List Sig} {a : Sig} (h : j5 w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ n3 a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def q14 (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, d5 u d ∧ a ∈ w ∧ b ∈ w ∧ n3 a ∧ n3 b ∧ a ≠ b ∧ z = bin d a b
private lemma k36 {u w a b} (d : Nat) (hd : d5 u d) (ha : j5 w a) (hb : j5 w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    j5 w (bin d a b) ∨ q14 u w (bin d a b) := by
  have rz : j5 w zero := Or.inr (fun h => h.1 rfl)
  have ro : j5 w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := t30 a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := t30 b
  by_cases he : a=b
  · subst b
    left
    rcases h5 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases q15 ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases h5 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases h5 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases q15 hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases h5 hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases h5 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem q18 (a : Sig) : nrm true a ≠ one := by
  intro h
  have := y45 a
  rw [h,g8] at this
  exact Bool.noConfusion this
theorem k23 {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (t11 d a b) ∨ q14 u w (nrm u (t11 d a b)) := by
  cases u
  · have e : t11 d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := k36 (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [t38] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := s38 d a b
    unfold Repr
    rw [eq]
    exact k36 e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨q18 a,q18 b⟩)
theorem f11 {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := d33 hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma g17 {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact f11 (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem s41 {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [z35]
def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma k43 (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ q14 u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (t11 d) (if d then zero else one)) ∨
      q14 u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (t11 d) (if d then zero else one))) := by
    have unit (v : Sig) : t11 d v (if d then zero else one) = v := by
      apply d7
      intro i
      cases d <;> simp [y10,d6,g8]
    cases l with
    | nil => exact Or.inl (f11 (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (g17 w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact k23 d (g17 w i) (g17 w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact f11 (Or.inr (by simp [gv,c42]))
    | cons i l => exact s41 (g17 w i)
private lemma j23 {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : j5 w z ∨ (c=1 ∧ q14 u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := v18 h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma b47 {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : n3 target) (hout : target ∈ (f15 gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [f15] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := k43 u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : j5 (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ q14 u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := j23 ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega
private lemma w43 (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (d6 _).symm
  | some a => rfl
private lemma v45 (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [w43]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact g8 _
    | cons a l ih =>
      change bit i (t11 false _ _) = (_ && _)
      rw [y10]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact d6 _
    | cons a l ih =>
      change bit i (t11 true _ _) = (_ || _)
      rw [y10]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [y11,d6]
    | cons a l => exact y11 _ _
private lemma d26 (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (f15 gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (f15 gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,v45 i g w (hg g (by simp))]
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def g5 {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then g5 false a b else if d=1 then g5 true a b else
    if d=2 then g5 false a (inv b) else g5 false (inv a) b
def s3 {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if s3 a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def s1 {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ s3 v ∨ (u=true ∧ inv v ∈ pool)
def y15 {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, s1 u pool a
def p4 {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), p4 u roots p bank ∧ s1 u bank a ∧
      s1 u bank b ∧ c=g5 op a b :: bank
theorem p4.start {R u} {roots : List (Wire R)} : p4 u roots 0 roots := rfl
theorem p4.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : p4 u roots p bank)
    (ha : s1 u bank a) (hb : s1 u bank b) : p4 u roots (p+1) (g5 op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem p4.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, p4 u roots p bank → Prop}
    (start : motive 0 roots p4.start)
    (two : ∀ {p bank a b} (op : Bool) (h : p4 u roots p bank) (ha : s1 u bank a)
      (hb : s1 u bank b), motive p bank h →
      motive (p+1) (g5 op a b :: bank) (p4.two op h ha hb))
    {p bank} (h : p4 u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), d5 u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : d5 u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : d5 u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem v10 {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem q23 {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,v10]
theorem j13 {R} {a : Wire R} (h : s3 a) : s3 (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem g36' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem b30 {R} (a : Wire R) : cost (inv a)=cost a := by
  have : s3 (inv a) ↔ s3 a := ⟨fun h => g36' a ▸ j13 h,j13⟩
  by_cases h : s3 a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem j18 {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : s1 u bank a) : s1 u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(g36' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (j13 h))
  · exact Or.inl h
theorem d23 {R} {a b : Wire R} (op) (h : s3 a) (g : s3 b) :
    s3 (g5 op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem y22 {R u} (op) {a b : Wire R} {bank}
    (h : s3 a ∨ s3 b) (ha : s1 u bank a) (hb : s1 u bank b) :
    s1 u bank (g5 op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [g5]⟩)
    · simpa [g5] using hb
    · simpa [g5] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [g5]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [g5]⟩)
    · simpa [g5] using ha
    · simpa [g5] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [g5]⟩)
theorem p14 {R u} {bank v} (w : Wire R) (h : s1 u bank v) :
    s1 u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem n34 {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : p4 u roots p bank)
    (ha : s1 u bank a) (hb : s1 u bank b) :
    ∃ q next, p4 u roots q next ∧ s1 u next (g5 op a b) ∧
        (∀ v, s1 u bank v → s1 u next v) ∧
        q+cost a+cost b ≤ p+1+cost (g5 op a b) := by
  classical
  by_cases c : s3 a ∨ s3 b
  · refine ⟨p,bank,hp,y22 op c ha hb,fun _ h => h,?_⟩
    by_cases ca : s3 a <;> by_cases cb : s3 b
    · simp [cost,ca,cb,d23 op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬s3 a := fun h => c (Or.inl h)
    have cb : ¬s3 b := fun h => c (Or.inr h)
    exact ⟨p+1,_,p4.two op hp ha hb,Or.inl (by simp),fun _ h => p14 _ h,
      by simp [cost,ca,cb]⟩
theorem n22 {R u} {bank : List (Wire R)} {d a b} (hd : d5 u d) (ha : s1 u bank a) (hb : s1 u bank b) :
    ∃ op x y, comb d a b=g5 op x y ∧ s1 u bank x ∧ s1 u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases h5 hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,j18 hu hb,rfl,b30 b⟩
  · exact ⟨false,inv a,b,rfl,j18 hu ha,hb,b30 a,rfl⟩
theorem t29 {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : d5 u d) (hp : p4 u roots p bank)
    (ha : s1 u bank a) (hb : s1 u bank b) :
    ∃ q next, p4 u roots q next ∧ s1 u next (comb d a b) ∧
        (∀ v, s1 u bank v → s1 u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := n22 hd ha hb
  rw [e,←cx,←cy]
  exact n34 roots op hp hx hy
theorem p28 {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem n30 {R u} {goal : Wire R} (nc : ¬s3 goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : p4 u roots p bank) (hs : y15 u bank ws) :
    ∃ q next, p4 u roots q next ∧ s1 u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : y15 u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := t29 roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : y15 u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases p28 hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (p28 hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := q23 a (kept kb b rest) ka
    have hlen' := q23 b rest kb
    rw [v10] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [v10,v10]
    omega
def y0 {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem w22 {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (y0 rows) =
    kept k (y0 rows a) (ws.map (y0 rows)) := by
  cases k <;> simp [kept]
theorem l15 {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    y0 rows (comb d a b) = comb d (y0 rows a) (y0 rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem m25 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (y0 rows goal) s (ws.map (y0 rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,w22,l15] at ih ⊢
    exact Run.two op hd ka kb ih
theorem k10 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬s3 (y0 rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : p4 u roots p bank) (hs : y15 u bank (ws.map (y0 rows)))
    (hl : ∀ q bs, p4 u roots q bs → s1 u bs (y0 rows goal) → L ≤ q) :
    L + mass (ws.map (y0 rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := n30 nc (m25 rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 512
def q1 (a : Sig) : Wire Row := fun r => bit r a
def m10 (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem s8 (f : Wire Row) (r : Row) : bit r (m10 f) = f r := by
  simp only [bit,m10,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem c12 (v : Sig) : m10 (q1 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact s8 (q1 v) ⟨j,hj⟩
theorem x22 (f : Wire Row) : q1 (m10 f) = f := by
  funext r
  exact s8 f r
theorem x35 (a : Sig) : q1 (neg a) = inv (q1 a) := by
  funext r
  exact y11 _ _
theorem y35 (d : Nat) (a b : Sig) :
    q1 (bin d a b) = comb d (q1 a) (q1 b) := by
  funext r
  simp only [q1,z11,comb]
  split_ifs <;> rfl
theorem s28 {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem q19 {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem f17 (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem x20 {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (q1 T) k (v.map q1) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := q19 kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := q19 ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [f17,f17,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map q1) at progress
    rw [List.map_cons,s28,s28,y35] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem k38 (f : Wire Row) : m10 (inv f) = neg (m10 f) := by
  rw [←c12 (neg (m10 f)),x35,x22]
theorem r27 (d : Bool) (f g : Wire Row) :
    m10 (g5 d f g) = t11 d (m10 f) (m10 g) := by
  apply d7
  intro r
  rw [s8,y10,s8,s8]
  cases d <;> rfl
theorem h12 {u} {bank : List (Wire Row)} {a} (h : s1 u bank a) :
    Repr u ((bank.map m10).map (nrm u)) (m10 a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply f11
    cases b
    · exact Or.inl (d7 fun i => (s8 _ i).trans (d6 i).symm)
    · exact Or.inr (d7 fun i => (s8 _ i).trans (g8 i).symm)
  · have := k38 a
    refine Or.inl ?_
    rw [←z35,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem l20 {u} {roots : List (Wire Row)} {p bank}
    (h : p4 u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map m10).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map m10).map (nrm u) := by
  induction h using p4.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,r27] at sub
    have rep := k23 d (h12 ha) (h12 hb)
    obtain ⟨k',S',hk,run',sub'⟩ := j23 (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩
def d4 (a : Sig) : Bool := !(bit 0 a)
theorem b36 {u} {w : List Sig} (h : w.all d4=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact b42 (by simpa [d4] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem d13 {u} {roots : List Sig} {p bank T} (hp : n3 T) (nT : d4 T=true) (nR : roots.all d4=true)
    (h : p4 u (roots.map q1) p bank) (hit : s1 u bank (q1 T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := h12 hit
  rw [c12] at hm
  unfold Repr at hm
  rw [b42 (by simpa [d4] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := l20 h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map q1).map m10 = roots := by simp [List.map_map,Function.comp_def,c12]
  rw [e,b36 nR] at hs
  exact hs
theorem p10 {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [z11,z11,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem v8 {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := p10 h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig:=[(d0 [170,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa]),(d0 [204,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc]),(d0 [240,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0]),(d0 [255,0xff00ff00ff00ff00,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00]),(d0 [255,0xff0000ffff0000ffff,0xffff0000ffff00,0xffff0000ffff0000,0xffff0000ffff0000ff,0xff0000ffff0000ffff,0xffff0000ffff00,0xffff0000ffff0000]),(d0 [255,0xffffff00000000ffff,0xffff00000000ffffff,0xff00000000ffffffff,0xffffffff00,0xffffffff0000,0xffffffff000000,0xffffffff00000000]),(d0 [255,0xffffffffffffff0000,16777215,0xffffffffff00000000,0xffffffffff,0xffffff000000000000,0xffffffffffffff,0xff0000000000000000]),(d0 [255,0xffffffffffffffffff,0xffffffffffff000000,0,0xffffffffff,0xffffffffffffffffff,0xffff00000000000000,0]),(d0 [255,0xffffffffffffffffff,0xffffffffffffffffff,0xffffffffffffffffff,0xffffffff0000000000,0,0,0])]
def q13 : Sig:=(d0 [255,0xffffffffffffffffff,0xfffffffafff8ffffff,0xffffffffffffffffff,0xffeaffc8ffffffffff,0xfefcfcfffffffffffa,0xf8f8ffeefeeeffeefc,0xccffeafaeaffeaf8c8])
theorem d22 : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def g6 (f : Row → Row) (a : Sig) := m10 fun r => bit (f r) a
theorem w7 (f : Row → Row) (a : Sig) (r : Row) :
    bit r (g6 f a) = bit (f r) a := s8 _ _
theorem s7 (f : Row → Row) (a : Sig) :
    q1 (g6 f a) = y0 f (q1 a) := by funext r; exact w7 f a r
theorem k20 (f : Row → Row) (d : Nat) (a b : Sig) :
    g6 f (bin d a b) = bin d (g6 f a) (g6 f b) := by
  apply d7
  intro r
  simp only [w7,z11]
theorem c33 (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (g6 f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [w7,w7,hr] at he
  exact he
theorem l12 (f : Row → Row) : g6 f zero = zero ∧ g6 f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (w7 f zero ⟨j,hj⟩).trans ((d6 _).trans (d6 ⟨j,hj⟩).symm)
  · exact (w7 f one ⟨j,hj⟩).trans ((g8 _).trans (g8 ⟨j,hj⟩).symm)
theorem v28 {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (g6 f T) k (S.image (g6 f)) := by
  have inj := c33 f onto
  obtain ⟨fz,fo⟩ := l12 f
  have pp (v) (p : n3 v) : n3 (g6 f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : g6 f (bin d a b) ∉ (insert a (insert b U)).image (g6 f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,k20] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem n10 {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [z11] at hp hn
      subst none
      rcases h5 hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def f6 (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, p4 u (roots.map q1) p bank → s1 u bank (q1 T) → L ≤ p
theorem t41 {R u} {roots : List (Wire R)} {p bank} (h : p4 false roots p bank) : p4 u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : s1 false bank a) : s1 u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using p4.ind with
  | start => exact p4.start
  | two op h ha hb ih => exact p4.two op ih (up ha) (up hb)
theorem s33 {u roots T L} (h : f6 true roots T L) : f6 u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (t41 hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h
def v0 (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S
def j15 (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem v17 {u roots T L} (hp : n3 T) (nT : d4 T=true) (nR : roots.all d4=true)
    (essential : ∀ a ∈ roots, j15 T roots a)
    (noRun : v0 u T L roots.toFinset) : f6 u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := d13 hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact v8 run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)
theorem j11 {v : Sig} (hv : n3 v) : ¬s3 (q1 v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply f11
    cases b
    · exact Or.inl (d7 fun i => (congrFun h i).trans (d6 i).symm)
    · exact Or.inr (d7 fun i => (congrFun h i).trans (g8 i).symm)
  have hr' : j5 [] v := hr
  exact (hr'.resolve_left (by simp)) hv
theorem q28 {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem v20 {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, s3 x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [v10,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem t18 {u} {roots other : List Sig} {T G : Sig} (pT : n3 T) (nT : d4 T=true) (nR : roots.all d4=true) (pG : n3 G)
    (r : Row → Row) (eq : g6 r T = G)
    (covered : ∀ a ∈ roots, s1 u (other.map q1) (q1 (g6 r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, j15 T roots a)
    (constant : ∀ a ∈ singles, s3 (q1 (g6 r a)))
    (L : Nat) (prior : f6 u other G L) : f6 u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := d13 pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact v8 run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := x20 run front nd fe
  have gc : y0 r (q1 T) = q1 G := (s7 _ _).symm.trans (congrArg q1 eq)
  have supp : y15 u (other.map q1) ((front.map q1).map (y0 r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←s7]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := k10 r run' (gc ▸ j11 pG) p4.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map q1).map (y0 r)) := by
    simp only [front,List.map_append,q28]
    let xs := (singles.toList.map q1).map (y0 r)
    have only : ∀ v ∈ xs, s3 v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←s7]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := v20 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega
def v7 (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem w24 {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem p39 {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, d5 u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      n3 (bin d a b) → (v7 ws a b d ka kb).length ≤ cap →
      v0 u T (cap-1) (v7 ws a b d ka kb).toFinset) :
    v0 u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := v18 tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,w24 (hn.erase _) b,
        w24 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [f17,f17,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := q19 kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (v7 ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,q19 ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (v7 ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := w17 tail
    have len : (v7 ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem x29 {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem y29 {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (x29 (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := p10 h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := n10 h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem m22 {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply y29 h rfl correct
  simp
def f19 (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, s1 u (roots.map q1) (y0 f (q1 a))) ∧
    ¬s3 (y0 f (q1 T)) ∧
    ∀ p bank, p4 u (roots.map q1) p bank → s1 u bank (y0 f (q1 T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def y2 (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))
theorem r23 {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    y0 f (q1 a) = y0 f (q1 b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h
theorem s18 {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : y0 f (q1 a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [d6] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
theorem w20 {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : y0 f (q1 a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he
def j8 (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, s1 u bank (y0 f (q1 a))
theorem s5 {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : j8 u f bank pool)
    (check : y2 u d pool a = true) : s1 u bank (y0 f (q1 a)) := by
  simp only [y2,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,s18 dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,w20 dom ho⟩)
  · exact r23 dom he ▸ supplyB v hv
  · have h := j18 hu (r23 dom he ▸ supplyB v hv)
    rw [x35] at h
    have e : inv (y0 f (inv (q1 a))) = y0 f (q1 a) := by
      funext r
      simp [inv,y0]
    rwa [e] at h
abbrev t9 := Nat × Sig × Sig
def t3 (c : t9) := bin c.1 c.2.1 c.2.2
def t12 (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem w30 {u d} (h : t12 u d=true) : d5 u d := by
  simpa [t12,d5] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : t9) :=
  t12 u c.1 && (y2 u d pool c.2.1 && y2 u d pool c.2.2)
theorem p20 {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : p4 u roots q bank) (hs : j8 u f bank pool)
    (c : t9) (valid : choiceOK u d pool c = true) :
    ∃ next, p4 u roots (q+1) next ∧ j8 u f next (t3 c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := n22 (w30 valid.1) (s5 dom hs valid.2.1)
    (s5 dom hs valid.2.2)
  refine ⟨_,p4.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [t3,y35,l15,e]
    exact Or.inl (by simp)
  · exact p14 _ (hs _ hm)
def k11 (u : Bool) (d : Sig) (pool : List Sig) : List t9 → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then k11 u d (t3 c::pool) cs else none
theorem j14 {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : p4 u roots q bank) (hs : j8 u f bank pool)
    (cs : List t9) {result} (ok : k11 u d pool cs = some result) :
    ∃ next, p4 u roots (q+cs.length) next ∧ j8 u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [k11] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := p20 dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def d1 (d a : Sig) := masked d a == zero || masked d a == d
theorem r13 {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (d1 d) ≤ mass ((ws.map q1).map (y0 f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,v10]
    cases h : d1 d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : s3 (y0 f (q1 a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [d1,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,s18 dom hz⟩
        · exact ⟨true,w20 dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def r16 (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (d1 d)) && ws.all (y2 u d pool)
theorem m15 {u raw T d L} (slice : f19 u raw T d L) (cs : List t9)
    {pool ws cap} (built : k11 u d raw cs = some pool)
    (nd : ws.Nodup) (cut : r16 u d L cap cs.length pool ws = true) :
    v0 u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := j14 dom (p4.start (roots:=roots.map q1)) base cs built
  simp only [r16,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : y15 u bank ((ws.map q1).map (y0 f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact s5 dom hs (List.all_eq_true.mp all a ha)
  have b := k10 f (x20 h ws nd rfl) nc hr coveredS lo
  have massLo := r13 dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move := Sig × Sig × Row
def m19 (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def b25 (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def k25 (m : Move) (r : Row) : Row :=
  if bit r m.1 then m19 m.2.2 r else if bit r m.2.1 then m19 (b25 m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def s13 (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (b25 m.2.2).val) a)
theorem t39 (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (m19 d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [m19,h,r.isLt]
theorem t43 (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp
theorem g47 (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact t43 _ _ _
theorem v43 (r : Row) (m : Move) (a : Sig) : bit r (s13 m a) = bit (k25 m r) a := by
  simp only [s13,g47,t39,k25]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def v5 (ms : List Move) (r : Row) := ms.foldl (fun j m => k25 m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr s13 a
theorem r12 (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (v5 ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (v43 r m _).trans (ih _)
theorem n5 (ms : List Move) (a : Sig) : movedWord ms a = g6 (v5 ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (r12 ms a ⟨j,hj⟩).trans (w7 _ _ ⟨j,hj⟩).symm
def g22 (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem q29 {u roots w} (ok : g22 roots w = true) :
    s1 u (roots.map q1) (q1 w) := by
  simp only [g22,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext d6⟩)
  · exact Or.inr (Or.inl ⟨true,funext g8⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def f10 (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => g22 base (movedWord ms a))
theorem g14 {u ms raw T base G} (ok : f10 ms raw T base G = true) :
    g6 (v5 ms) T = G ∧
    ∀ a ∈ raw, s1 u (base.map q1) (q1 (g6 (v5 ms) a)) := by
  simp only [f10,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,n5] at ok
  exact ⟨ok.1,fun a ha => q29 (ok.2 a ha)⟩
theorem b39 {u ms raw T base G L} (ok : f10 ms raw T base G = true)
    (pT : n3 T) (nT : d4 T=true) (nR : raw.all d4=true) (pG : n3 G)
    (hL : f6 u base G L) : f6 u raw T L := by
  obtain ⟨eq,supp⟩ := g14 ok
  simpa using t18 pT nT nR pG (v5 ms) eq supp ∅ (by simp) (by simp) L hL
theorem v22 {u ms raw T base G L d} (ok : f10 ms raw T base G = true)
    (all : movedWord ms d = one) (properG : n3 G) (hL : f6 u base G L) :
    f19 u raw T d L := by
  obtain ⟨eq,supp⟩ := g14 ok
  have obs : y0 (v5 ms) (q1 T) = q1 G :=
    (s7 _ _).symm.trans (congrArg q1 eq)
  refine ⟨v5 ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←r12,all,g8]
  · intro a ha
    rw [←s7]
    exact supp a ha
  · rw [obs]
    exact j11 properG
  · rw [obs]
    exact hL
def w19 (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem v19 {T roots a rs} (ok : w19 T roots a rs = true) : j15 T roots a := by
  simp only [w19,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def v4 (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  d4 T && raw.all d4 && xs.all (fun a => w19 T raw a.1 a.2)
theorem s10 {T raw xs} (ok : v4 T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, j15 T raw a := by
  simp only [v4,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact v19 (List.all_eq_true.mp ok.2 _ hm)
theorem z4 {T raw xs} (ok : v4 T raw xs = true) :
    d4 T=true ∧ raw.all d4=true := by
  simp only [v4,Bool.and_eq_true] at ok
  exact ok.1
theorem t28 {u raw T} (properT : n3 T) (xs : List (Sig × Row × Row))
    (ok : v4 T raw xs = true) :
    f6 u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := d13 properT (z4 ok).1 (z4 ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := s10 ok a ha
    exact v8 run raw a sub r s hd iso
  have bound := w17 run
  omega
def g18 (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  f10 ms raw T base G && v4 T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)
theorem d46 {u ms T raw base G xs L} (ok : g18 ms T raw base G xs = true)
    (properT : n3 T) (properG : n3 G) (low : f6 u base G L) :
    f6 u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [g18,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := g14 ok.1.1
  apply t18 properT (z4 ok.1.2).1 (z4 ok.1.2).2 properG _ eq supp _ (s10 ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,n5] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext d6⟩
  · rw [h]
    exact ⟨true,funext g8⟩
def y7 (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (y7 m).map Prod.snd
def k16 (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def m4 (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [k16 (m/512-1)]
def y19 (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def q0 (m : Nat) : Sig :=
  let x := y19 m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def f55 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def d55 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def c55 : Nat → Nat
  | 0 => (d0 [65536,16777216,4294967296,1099511627776,281474976710656,72057594037927936,0x10000000000000001])
  | 1 => (d0 [16777216,0,1099511627776,0,72057594037927936,1])
  | 2 => (d0 [4294967296,1099511627776,0,0,0x10000000000000001])
  | 3 => (d0 [1099511627776,0,0,1])
  | 4 => (d0 [281474976710656,72057594037927936,0x10000000000000001])
  | 5 => (d0 [72057594037927936,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def r11 (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((f55 (fixed &&& 7)*d55 ((fixed >>> 3) &&& 7)*c55 ((fixed >>> 6) &&& 7)) <<< o)
def x25 (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def h7 (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def m16 (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (y7 mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def z33 (m hints : Nat) : List (Sig × Row × Row) :=
  (y7 m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def v6 (T : Sig) := T != zero && T != one
theorem x7 (T : Sig) (h : v6 T = true) : n3 T := by
  simpa only [v6,n3,Bool.and_eq_true,bne_iff_ne] using h
def m1 (x off width : Nat) := (x >>> off) % 2^width
def q7 {α : Type} (width : Nat) (read : Nat → α) : Nat → Nat → List α
  | 0, _ => []
  | k+1, x => read x :: q7 width read k (x >>> width)
abbrev z2 := Nat × Nat × Nat × Nat × Nat
def f26 (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def r8 (m : Nat) : Sig := q0 m
def s11 (m : Nat) (c : z2) : Nat := m % 512+512*(c.1/512)
def p11 (m : Nat) (c : z2) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := x25 z o
  let raw := s11 m c
  let free := f26 raw (z % 512) o
  let G := movedWord ms (r8 m)
  let xs := m16 (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  v6 G && f10 ms (m4 raw) (r8 m) (m4 free) G &&
    (movedWord ms (r11 z o)==one) &&
    (if q=0 then v4 G (m4 free) xs && decide (L ≤ count-1)
     else v6 (q0 q) &&
       g18 (x25 (f26 free q 0) 0) G (m4 free) (m4 q) (q0 q) xs &&
       decide (L ≤ prior q+count))
theorem q12 {u} {m : Nat} (c : z2) (prior : Nat → Nat)
    (valid : ∀ q, f6 u (m4 q) (q0 q) (prior q))
    (ok : p11 m c prior = true) : f19 u (m4 (s11 m c)) (r8 m) (r11 c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := x25 z o
  let raw := s11 m (z,o,q,s,L)
  let free := f26 raw (z % 512) o
  let G := movedWord ms (r8 m)
  let xs := m16 (z/512+80) s
  change (((v6 G && f10 ms (m4 raw) (r8 m) (m4 free) G) &&
    (movedWord ms (r11 z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply v22 ok.1.1.2 ok.1.2 (x7 _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [p11,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (t28 (x7 _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [p11,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (d46 hh.1.2 (x7 _ ok.1.1.1) (x7 _ hh.1.1) (valid q) p bank hr ha)
def r19 (old rep : Nat) (swaps : List Nat) :=
  (v6 (q0 old) && d4 (q0 old) && (m4 old).all d4) && v6 (q0 rep) &&
    f10 (swaps.map h7) (m4 old) (q0 old) (m4 rep) (q0 rep)
theorem q30 {u old rep L swaps} (ok : r19 old rep swaps = true)
    (h : f6 u (m4 rep) (q0 rep) L) : f6 u (m4 old) (q0 old) L := by
  simp only [r19,Bool.and_eq_true] at ok
  exact b39 ok.2 (x7 _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (x7 _ ok.1.2) h
def j1 (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem n0 {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, f6 u (m4 e.1) (q0 e.1) e.2) (q : Nat) :
    f6 u (m4 q) (q0 q) (j1 entries q) := by
  unfold j1
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev f4 := Sig × Nat × Nat × List Sig
def f4.domain (c : f4) : Sig := c.1
def f4.bound (c : f4) : Nat := c.2.1
def f4.paid (c : f4) : Nat := c.2.2.1
def f4.wires (c : f4) : List Sig := c.2.2.2
def t8 (u : Bool) (raw : List Sig) (T : Sig) (c : f4) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬s3 (y0 f (q1 T)) ∧
    (∀ q ws, p4 u (roots.map q1) q ws → s1 u ws (y0 f (q1 T)) → c.bound ≤ q) ∧
    p4 u (roots.map q1) c.paid bank ∧ j8 u f bank c.wires ∧ True
theorem r30 {u raw T d lb} (h : f19 u raw T d lb) (cs : List t9) {ws}
    (build : k11 u d raw cs = some ws) : t8 u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := j14 dom (p4.start (roots:=roots.map q1)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [f4.paid] using hr,hs,trivial⟩
theorem r22 {u raw T c} (valid : t8 u raw T c) (k : Nat) (rest : List Sig)
    (choice : t9) (paid : Bool)
    (known : ∀ a ∈ rest, y2 u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else y2 u c.domain c.wires (t3 choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(t3 choice :: rest).countP (d1 c.domain))
    (nd : (t3 choice :: rest).Nodup) :
    v0 u T k (t3 choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := t3 choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : p4 u (roots.map q1) n out)
      (zs : j8 u f out (t3 choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : y15 u out ((ws.map q1).map (y0 f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := k10 f (x20 run ws nd rfl) nc reach covered lo
    have cm := r13 dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (d1 c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact s5 dom hs buy
    · exact s5 dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := p20 dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, s1 u out (y0 f (q1 v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact s5 dom point (known _ hm)
def p5 (u : Bool) (c : f4) (k : Nat) (rest : List Sig) (op : t9) :=
  let z := t3 op
  let extra := !(y2 u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (d1 c.domain)) &&
    rest.all (y2 u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)
theorem k15 {u raw T c} (valid : t8 u raw T c) {k rest op}
    (nd : (t3 op::rest).Nodup) (cut : p5 u c k rest op = true) :
    v0 u T k (t3 op::rest).toFinset := by
  let extra := !(y2 u c.domain c.wires (t3 op))
  apply r22 valid k rest op extra _ _ _ nd
  · simp only [p5,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [p5,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : y2 u c.domain c.wires (t3 op) <;> simp_all [extra]
  · simp only [p5,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def f14 (u : Bool) (raw : List Sig) (cs : List t9) (d : Sig) (lb : Nat) : Option f4 :=
  (k11 u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem v16 {u raw T d L cs c} (slice : f19 u raw T d L)
    (h : f14 u raw cs d L = some c) : t8 u raw T c := by
  unfold f14 at h
  cases he : k11 u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact r30 slice cs he
abbrev Bits := BitVec 152
abbrev s19 := Bits × Bits
abbrev y1 := Sig × s19
def h11 {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem w6 {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (h11 r v).getLsbD i.val = bit (r i) v := by
  simp only [h11,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def v9 (r s : Fin 152 → Row) (a : Sig) : s19 := (h11 r a,h11 s a)
def y9 (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem y41 {T r s} (h : y9 T r s) : Sep T 152 r s (v9 r s) := by
  exact ⟨h,fun a i => ⟨w6 _ _ _,w6 _ _ _⟩⟩
def k6 (r s : Fin 152 → Row) (x : y1) := x.2 = v9 r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : y1) : y1 := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem k33 {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    h11 r (bin d a b) = bv d (h11 r a) (h11 r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := w6 r (bin d a b) ⟨j,hj⟩
  rw [z11,←w6 r a ⟨j,hj⟩,←w6 r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem k17 {r s x y} (d) (hx : k6 r s x) (hy : k6 r s y) :
    k6 r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [k6,dbin,v9,k33,hx,hy]
def p3 : y1 := (zero,0,0)
theorem b18 (r s) : k6 r s p3 := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (h11 r zero).getLsbD j
    rw [show (h11 r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from w6 _ _ ⟨j,hj⟩,d6]
    simp
  · change (0 : Bits).getLsbD j = (h11 s zero).getLsbD j
    rw [show (h11 s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from w6 _ _ ⟨j,hj⟩,d6]
    simp
theorem j17 {r s ws} (all : ∀ v ∈ ws, k6 r s v) (i : Nat) :
    k6 r s (List.getD ws i p3) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact b18 _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def l11 (n : Nat) (bits : Nat) (ws : List y1) : List y1 :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) p3
    let b := ws.getD ((bits >>> 4) &&& 15) p3
    l11 k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem k19 (n bits) (ws) (r s) (base : ∀ v ∈ ws, k6 r s v) :
    ∀ v ∈ l11 n bits ws, k6 r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact k17 _ (j17 base _) (j17 base _)
def s12 (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem m30 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem l30 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem k30 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem j30 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem h30 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem g30 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem f30 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem d30 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem c30 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem k13 : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact m30 r
  · exact l30 r
  · exact k30 r
  · exact j30 r
  · exact h30 r
  · exact g30 r
  · exact f30 r
  · exact d30 r
  · exact c30 r
theorem l18 (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (s12 cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [k13]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def q16 (m : Nat) (p q : Nat → Bits) : List y1 :=
  (y7 m).map (fun (j,a) => (a,p j,q j))
theorem v13 {m j a} (h : (j,a) ∈ y7 m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem n25 (m) (p q : Nat → Bits) :
    ∀ a ∈ q16 m p q, k6 (s12 p) (s12 q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := v13 hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (l18 p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (w6 _ _ ⟨i,hi⟩).symm
  · exact (l18 q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (w6 _ _ ⟨i,hi⟩).symm
def y20 (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem s34 (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (s12 v i) (y19 m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [y19,hh] using l18 v i j
  · simp [y19,hh,d6]
theorem g26 (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (s12 v i) (q0 m) = (y20 m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (y19 m j).getLsbD (s12 v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := s34 m v i ⟨j,hj⟩
  simp only [bit,q0,y20,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits
def s9 (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def j4 (d : Bool) (v : List y1) : Cov :=
  v.foldr (fun a c => s9 (column d a.2) c) (0,0,0)
def r10 (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def r14 (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem f47 (c : Cov) (a : Bits) : r10 (s9 a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [r10,s9,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem d47 (c : Cov) (a b : Bits) : r14 (s9 a (s9 b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [r14,s9,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : s9 a (s9 b c)=s9 b (s9 a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [s9,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [s9,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem z29 (d : Bool) {l r : List y1} (h : l.Perm r) : j4 d l=j4 d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (s9 (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem r43 (d : Bool) (v : List y1) {r s} (good : ∀ a ∈ v, k6 r s a) :
    (j4 d v).1 = covered d (v9 r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (j4 d v).1) = column d (v9 r s a.1) ||| _
    rw [show a.2=v9 r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def l10 (ws : List y1) (a : y1) (keep : Bool) :=
  if keep then ws else ws.erase a
def z5 (ws : List y1) (a b : y1) (ka kb : Bool) :=
  l10 (l10 ws a ka) b kb
theorem n14 {ws : List y1} (a : y1) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem x24 {ws : List y1} (d : Bool) (a : y1) (ha : a ∈ ws) (keep : Bool) :
    (j4 d (l10 ws a keep)).1 =
      (if keep then (j4 d ws).1 else r10 (j4 d ws) (column d a.2)) := by
  cases keep
  · change (j4 d (ws.erase a)).1 = r10 (j4 d ws) _
    rw [z29 d (n14 a ha)]
    exact (f47 _ _).symm
  · rfl
theorem w29 {ws : List y1} (a b : y1) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (n14 a ha).trans (List.Perm.cons _ (n14 b hm))
theorem r39 {ws : List y1} (d : Bool) (a b : y1) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (j4 d (z5 ws a b ka kb)).1 =
      (if ka then (if kb then (j4 d ws).1 else r10 (j4 d ws) (column d b.2))
       else if kb then r10 (j4 d ws) (column d a.2)
       else r14 (j4 d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (j4 d ((ws.erase a).erase b)).1 = r14 (j4 d ws) _ _
    rw [z29 d (w29 a b ha hb ne)]
    exact (d47 _ _ _).symm
  · exact x24 d a ha false
  · exact x24 d b hb false
  · rfl
def t10 (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem g10 {xs ys} (h : t10 xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [t10,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def z8 (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def b22 (xs : List Sig) := xs.foldl (fun v x => v+z8 x) 0
def r9 (u : Bool) (pools : List f4) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : t9) :=
  let ws := t3 op::rest
  (links (b22 ws)).any (t10 ws) || pools.any (fun p => p5 u p k rest op)
theorem f18 {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, t8 u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → v0 u T k (List.toFinset xs))
    (nd : (t3 op :: rest).Nodup)
    (h : r9 u pools links k rest op = true) :
    v0 u T k (t3 op :: rest).toFinset := by
  simp only [r9,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [g10 ok]
    exact lValid _ _ hx
  · exact k15 (pValid _ hp) nd ok
abbrev l36 := Cov × Bool
def m20 (u : Bool) (ws : List y1) : l36 := (j4 (!u) ws,u)
def c13 (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else r10 v b) else if kb then r10 v a else r14 v a b
theorem d16 (ws : List y1) (a : y1) (k : Bool) : (l10 ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem v42 (ws : List y1) (a b : y1) (ka kb : Bool) :
    (z5 ws a b ka kb).Sublist ws := (d16 _ _ _).trans (d16 _ _ _)
theorem h42 (ws : List y1) (a b : y1) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (z5 ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [z5,l10,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def w4 (op : Nat) (a b : y1) : t9 := (op,a.1,b.1)
abbrev g3 := Nat × Nat × List y1 × l36 × List f4 × (Nat → List (List Sig))
def d10 (c : g3) (op : Nat) (a b z : y1) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := c13 cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !v6 z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (z5 ws a b ka kb).map Prod.fst
      r9 cov.2 pools links (cap-1) rest (w4 op a b)
def t17 (ws : List y1) (op : Nat) (a b : y1) (ka kb : Bool) :=
  (dbin op a b).1 :: (z5 ws a b ka kb).map Prod.fst
theorem k22 {u raw T r s ws pools links cap a b op ka kb}
    (pairs : y9 T r s) (faith : ∀ w ∈ ws, k6 r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, t8 u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → v0 u T (cap-1) (List.toFinset xs))
    (pro : n3 (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : d10 (cap,ws.length,ws,m20 u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    v0 u T (cap-1) (t17 ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := z5 ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := v42 _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : v6 z.1 = true := by simpa [v6,n3] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,h42 _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := w17 h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold d10 at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := m22 h (y41 pairs)
  let d := !u
  have g : (j4 d rest).1 = covered d (v9 r s) (rest.map Prod.fst) :=
    r43 _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (j4 d rest).1 = c13 (j4 d ws) (column d a.2) (column d b.2) ka kb :=
    r39 d a b ha hb ne ka kb
  have hf := k17 op (faith _ ha) (faith _ hb)
  change column d (v9 r s z.1) ||| covered d (v9 r s) (rest.map Prod.fst) = _ at sep
  change z.2 = v9 r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((c13 (j4 (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (c13 (j4 (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !v6 z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact f18 (op:=w4 op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def c11 (ctx : g3) (a b : y1) (op : Nat) :=
  let z := dbin op a b
  let attempt := d10 ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def r20 (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem n23 {u d} (h : d5 u d) : d ∈ r20 u := by
  rcases h5 h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [r20]
  · cases u <;> simp [r20]
  · simp [r20]
  · simp [r20]
def f25 (ctx : g3) (a : y1) (bs : List y1) :=
    bs.all (fun b => (r20 ctx.2.2.2.1.2).all (c11 ctx a b))
def q10 (ctx : g3) : List y1 → Bool
  | [] => true
  | a::bs => f25 ctx a bs && q10 ctx bs
theorem y34 {ctx ws} (h : q10 ctx ws=true) {a b : y1} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, d5 ctx.2.2.2.1.2 d → c11 ctx a b d=true) ∨
      (∀ d, d5 ctx.2.2.2.1.2 d → c11 ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [q10,Bool.and_eq_true,f25,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (n23 hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (n23 hd)
      · exact ih h.2 haTail hbTail
theorem q27 {ctx a b d} (h : c11 ctx a b d = true) (ka kb : Bool) :
    d10 ctx d a b (dbin d a b) ka kb = true := by
  simp only [c11,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem b29 {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem t20 {v : List y1} (nd : v.Nodup) (a w : y1) (k : Bool) :
    w ∈ l10 v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [l10,nd.mem_erase_iff,and_comm]
theorem j16 {ws : List y1} (nd : (ws.map Prod.fst).Nodup) {a b : y1}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem c22 {ws : List y1} (nd : (ws.map Prod.fst).Nodup) {a b : y1}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (z5 ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (d16 ws a ka)
  simp only [z5,List.mem_map,t20 wn,t20 dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (j16 nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (j16 nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem h26 {ws : List y1} (nd : (ws.map Prod.fst).Nodup) {a b : y1}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (t17 ws d a b ka kb).toFinset =
      (v7 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [t17,v7,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    c22 nd ha hb,b29,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem c23 {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : d5 u d) (ka kb : Bool) :
    (v7 v a b d ka kb).toFinset = (v7 v b a (m14 d) kb ka).toFinset := by
  ext x
  simp only [v7,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    b29,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,q22 hd a b]
  tauto
theorem l33 {u raw T r s ws pools links cap}
    (pairs : y9 T r s) (faith : ∀ w ∈ ws, k6 r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, t8 u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → v0 u T (cap-1) (List.toFinset xs))
    (checks : q10 (cap,ws.length,ws,m20 u ws,pools,links) ws = true) :
    v0 u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply p39 nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : y1) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : n3 (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : c11 (cap,ws.length,ws,m20 u ws,pools,links) a b d = true) :
      v0 u T (cap-1) (v7 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←h26 nd aa bb ne']
    exact k22 pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (q27 test ka kb)
  rcases y34 checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [c23 _ nd _ _ d hd]
    exact one b a (m14 d) hbW haW (Ne.symm ne) kb ka (q22 hd a.1 b.1 ▸ pro)
      (q22 hd a.1 b.1 ▸ fresh) (hh _ (m39 hd).1)
theorem l26 (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← d22]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (k13 i r).symm.trans ((h _ hm).trans (k13 i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def f16 (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem b19 {p q} (h : f16 p q = true) (r : Row) :
    v5 q (v5 p r) = r := by
  apply l26
  intro a ha
  rw [←r12,←r12]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def k18 (T : Sig) (p : List Move) :=
  (movedWord p T == T) && f16 p p.reverse && f16 p.reverse p
theorem g19 {u T n} {ws : List Sig} (hi : v0 u T n ws.toFinset)
    (p : List Move) (ok : k18 T p = true) : v0 u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [k18,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (v5 p) := fun r => ⟨v5 p.reverse r,b19 ok.2 r⟩
  intro k hk h
  have run := v28 h (v5 p) onto
  have goal : g6 (v5 p) T = T := (n5 p T).symm.trans ok.1.1
  have inv (x : Sig) : g6 (v5 p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [w7,r12,b19 ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (g6 (v5 p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run
abbrev w0 := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def j3 : w0 := (0,0,0,0,0,0,0,fun _ => 0)
def z3 (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def t1 (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := z3 data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := z3 data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def y4 (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := z3 data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := z3 data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
abbrev w1 := Nat × Nat × (Nat → Bits × Bits) × List z2 × List (List Nat) ×
  (Nat → w0) × (Nat → Nat → Option (Nat × Nat))
def w1.mask (g : w1) : Nat := g.1
def w1.mode (g : w1) : Bool := !(g.1.testBit 10)
def w1.cap (g : w1) : Nat := g.2.1
def w1.samples (g : w1) : Nat → Bits × Bits := g.2.2.1
def w1.cols (g : w1) : List z2 := g.2.2.2.1
def w1.autos (g : w1) : List (List Nat) := g.2.2.2.2.1
def w1.levels (g : w1) : Nat → w0 := g.2.2.2.2.2.1
def w1.index (g : w1) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2
def q11 (g : w1) :=
  let ws := q16 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem x19 (g : w1) : ∀ a ∈ q11 g,
    k6 (s12 fun j => (g.samples j).1) (s12 fun j => (g.samples j).2) a := by
  exact n25 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def m3 (g : w1) := r8 g.mask
def z6 (m : Nat) (v : Nat → Bits) :=
  y20 m v
theorem s39 (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (s12 v i) (r8 m) = (z6 m v).getLsbD i.val := by
  exact g26 m v i
theorem w11 {m : Nat} {p q : Nat → Bits}
    (hp : z6 m p = BitVec.allOnes 152) (hq : z6 m q = 0) :
    y9 (r8 m) (s12 p) (s12 q) := by
  intro i
  simp only [s39,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def m6 {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::m6 (bits >>> 1) ws else m6 (bits >>> 1) ws
theorem f20 {α : Type} (bits : Nat) (ws : List α) : (m6 bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold m6
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def z9 (d : Nat) := 10*(d-1)
def t15 (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def v15 (d raw dict : Nat) :=
  (dict % 65536)*z9 d + (dict/65536)*(raw+d)
def h17 (tab : w0) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then z3 word (i*width) width else
    let off := v15 d raw dict+i*t15 d flags
    let pre := z3 word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := z3 word (off+flags % 16) lastBits
    let mask := z3 word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*z9 d
    z3 word (pre*z9 d) (z9 d) |||
      (last <<< z9 d) ||| (z3 word (base+mask*(raw+d)) (raw+d) <<< (10*d))
def p18 (_g : w1) (depth : Nat) := depth
def p16 (g : w1) (k i : Nat) : Nat × List y1 × List y1 :=
  let raw := q11 g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*p18 g depth
  let width := len+raw.length+depth
  let recp := h17 (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := l11 depth ops raw
  (ops,bank,m6 (recp >>> len) bank)
def s24 (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def c19 (bank : List y1) (ops paid : Nat) : Nat → List t9
  | 0 => []
  | n+1 =>
    let more := c19 bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (s24 ops 8 2,(bank.getD (ops &&& 15) p3).1,
        (bank.getD (s24 ops 4 4) p3).1) :: more
def h15 (g : w1) (ops d : Nat) (bank : List y1) (idx paid : Nat) : Option f4 :=
  (g.cols[idx]?).bind fun ci =>
    f14 g.mode (m4 (s11 g.mask ci)) (c19 bank ops paid d) (r11 ci.1 ci.2.1) ci.2.2.2.2
theorem l19 (g : w1)
    (cols : ∀ ci ∈ g.cols, f19 g.mode (m4 (s11 g.mask ci)) (m3 g) (r11 ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : h15 g ops depth bank i paid = some c) :
    t8 g.mode (vars g.mask) (m3 g) c := by
  unfold h15 at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply v16 _ h
    exact cols ci (List.mem_of_getElem? e)
def c29 (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := z3 data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: c29 data w v n (pos+w+v)
def q9 {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)
def j10 (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    q9 st fun pos => q9 first fun base =>
    q9 (z3 data pos 32) fun head =>
    q9 (Nat.log2 (head ^^^ (head+1))) fun ones =>
    q9 (base+(ones <<< gapBits)+z3 data (pos+ones+1) gapBits) fun key =>
    q9 (z3 data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        j10 data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def p25 {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []
def y18 (tab : w0) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+z3 data (start+i*ow) ow
    c29 data cw d (z3 data pos 5) (pos+5+marker)
  else
    let off := v15 d raw dict + num*t15 d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+z3 data (off+i*ow) ow
    let n := z3 data pos 5
    let gap := z3 data (pos+5) 3
    if !priority || decide (n≤1) then j10 data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := z3 data (pos+8) width
      let b := if n=2 then 1-a else z3 data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := j10 data pairs cw d gap n (pos+8+extra) 0
      p25 a b xs
def s4 (g : w1) (k i : Nat) := (p16 g k i).2.2.map Prod.fst
def l9 (g : w1) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (s4 g k pair.1).map (movedWord (perm.map h7).reverse)
theorem j19 (g : w1) (k : Nat)
    (names : ∀ x ∈ g.autos, k18 (m3 g) (x.map h7) = true)
    (earlier : ∀ i < (g.levels k).1, v0 g.mode (m3 g) k (s4 g k i).toFinset)
    {pair out} (h : l9 g k pair = some out) :
    v0 g.mode (m3 g) k out.toFinset := by
  unfold l9 at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact g19 (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def j6 (g : w1) (k i : Nat) :=
  let raw := q11 g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := p16 g k i
  let values := ws.map Prod.fst
  let rules := (y18 (g.levels k) raw.length i).filterMap (fun (a,b) => h15 g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (l9 g (k-1))).toList
  decide values.Nodup && !(values.contains (m3 g)) &&
    (if k=0 then true else q10 (k,ws.length,ws,m20 g.mode ws,rules,ls) ws)
theorem x6 (g : w1) (k i : Nat)
    (samples : y9 (m3 g) (s12 fun j => (g.samples j).1) (s12 fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, f19 g.mode (m4 (s11 g.mask ci)) (m3 g) (r11 ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, k18 (m3 g) (x.map h7) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, v0 g.mode (m3 g) (k-1) (s4 g (k-1) j).toFinset)
    (checked : j6 g k i = true) : v0 g.mode (m3 g) k (s4 g k i).toFinset := by
  simp only [j6,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : m3 g ∉ s4 g k i := by simpa [s4] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (s4 g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply l33 (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply k19 _ _ _ _ _ (x19 g) v
    exact (f20 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact l19 g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (l9 g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact j19 g _ names (prior (by omega)) h
def z1 (g : w1) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => j6 g k (start+n) && z1 g k start n
theorem p22 {g k start n} (h : z1 g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    j6 g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [z1,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem j2 {g k start a b} (h : z1 g k start a=true)
    (h' : z1 g k (start+a) b=true) : z1 g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [z1,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,z1,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def l4 (g : w1) (top : Nat) :=
  ∀ k ≤ top, z1 g k 0 (g.levels k).1 = true
def q2 (g : w1) (prior : Nat → Nat) :=
  (z6 g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (z6 g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => p11 g.mask c prior) &&
  g.autos.all (fun p => k18 (m3 g) (p.map h7))
theorem m34 (g : w1) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, f6 g.mode (m4 q) (q0 q) (prior q))
    (geometry : q2 g prior = true) (rows : l4 g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, v0 g.mode (m3 g) k (s4 g k i).toFinset := by
  simp only [q2,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply x6 g 0 i (w11 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => q12 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact p22 (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply x6 g _ i (w11 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => q12 _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact p22 (rows _ hk) i (by omega) (by omega)
def q8 (g : w1) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && t10 (s4 g k i) ws
theorem j20 {g top prior k i ws} (low : ∀ q, f6 g.mode (m4 q) (q0 q) (prior q))
    (geom : q2 g prior = true) (blocks : l4 g top) (le : k ≤ top)
    (idx : q8 g k i ws = true) : v0 g.mode (m3 g) k ws.toFinset := by
  simp only [q8,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←g10 idx.2]
  exact m34 g top prior low geom blocks _ le i idx.1
def t2 (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, f6 u (m4 e.1) (q0 e.1) e.2
def z18 (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem s0 {u old L m carries} (previous : t2 u old)
    (main : f6 u (m4 m) (q0 m) L)
    (ok : carries.all (fun v => r19 v.1 m v.2) = true) :
    t2 u (z18 old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact q30 (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem z24 : t2 true [] := by simp [t2]
theorem w33 {u es} (h : t2 true es) : t2 u es := fun e he => s33 (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def b20 : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (b20 n)
theorem x17 (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem p38 (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (x17 _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem v41 (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (x17 _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem n38 (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (x17 _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem m12 {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,p38,ih]
theorem z20 {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,v41,ih]
theorem c15 {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,n38,ih]
def d15 (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem c41 (n i : Nat) (hi : i<n) : (b20 n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [b20,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem z42 (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem c46 {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (d15 (b20 xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [d15,Nat.testBit_and,Nat.testBit_shiftRight,c41 _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,b20,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using z42 (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev v12 := Nat × Nat
abbrev m18 := Nat × Nat × Nat
def p6 {α} (s : α → s19) (xs : List α) : v12 :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def x14 {α} (c : α → Cov) (xs : List α) : m18 :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : v12) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem g16 (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem g12 {α} (s : α → s19) (xs : List α) (d : Bool) :
    packedColumn d (p6 s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,p6,column,Bool.false_eq_true,ite_false,ite_true,m12,c15,g16]
def g11 (op : Nat) (a b : v12) : v12 :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem r38 {α} (a b : α → y1) (xs : List α) (op : Nat) :
    g11 op (p6 (fun x => (a x).2) xs) (p6 (fun x => (b x).2) xs) =
    p6 (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [g11,h0,ite_true,p6,m12,dbin,bv]
  by_cases h1 : op=1
  · simp [g11,h1,p6,z20,dbin,bv]
  by_cases h2 : op=2
  · simp [g11,h2,p6,m12,c15,g16,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [g11,h0,h1,h2,ite_false,p6,m12,c15,g16,dbin,bv,e]
def z12 (c : m18) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem s22 {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    z12 (x14 c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => c13 (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [z12,x14,m12,z20,c15,g16,c13,r10,r14,
      Bool.false_eq_true,ite_false,ite_true]
def t0 (c : g3) (i : Nat) := c.2.2.1.getD i p3
def l13 (c : g3) (i j op : Nat) (ka kb : Bool) :=
  let a := t0 c i
  let b := t0 c j
  d10 c op a b (dbin op a b) ka kb
def d18 (c : g3) (d ka kb : Bool) (op i j : Nat) :=
  let a := t0 c i
  let b := t0 c j
  c13 c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def t16 {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && t16 f (mask >>> 153) xs
theorem y38 {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : t16 f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [t16,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev c25 := Nat × Nat × Nat × List v12 × m18
def j7 (k n : Nat) (xs : List g3) : c25 :=
  (k,n,b20 xs.length,(List.range n).map (fun i => p6 (fun c => (t0 c i).2) xs),
    x14 (fun c => c.2.2.2.1.1) xs)
def n12 (b : c25) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem w18 (k n) (xs) {i : Nat} (h : i<n) :
    n12 (j7 k n xs) i = p6 (fun c => (t0 c i).2) xs := by
  simp [n12,j7,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem r28 (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply d7
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def v3 (p : y1 → Bool) (a : y1) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem s23 (p : y1 → Bool) (ws : List y1) (a : y1) (keep : Bool) :
    ws.countP p ≤ (l10 ws a keep).countP p + v3 p a keep := by
  cases keep
  · simp only [l10,Bool.false_eq_true,ite_false,v3,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [l10,v3]
theorem c39 (p : y1 → Bool) (ws : List y1) (a b : y1) (ka kb : Bool) :
    ws.countP p - v3 p a ka - v3 p b kb ≤
    (z5 ws a b ka kb).countP p := by
  have h1 := s23 p ws a ka
  have h2 := s23 p (l10 ws a ka) b kb
  simp only [z5]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem d9 {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem l14 {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [d9,ih]
    rfl
def g4 (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def c14 (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (c14 d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem z13 (d a : Sig) : g4 d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem h18 (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem y14 (d a : Sig) : c14 d.toNat (g4 d.toNat a) = d1 d a := by
  rw [z13]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←h18,z0]
  rw [c14,e,h18]
  rfl
theorem v30 (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (g4 d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (g4 d.toNat a)) (anyEq x.toNat (l.map (g4 d.toNat))) = _
    rw [ih,z13,h18,List.map_cons,List.any_cons,Bool.beq_comm]
theorem z14 (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (g4 d.toNat)) (g4 d.toNat a) = y2 u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [r28]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,y14,z13,x,v30,v30]
  simp only [y2,d1]
def unav (u : Bool) (p : f4) (w : y1) : Nat := cond (y2 u p.domain p.wires w.1) 0 1
def n16 (u : Bool) (p : f4) (ws : List y1) (k : Nat) (a b : y1) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : y1 => d1 p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - v3 const a ka - v3 const b kb + (d1 p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!y2 u p.domain p.wires z).toNat < p.bound+cm)) &&
    (y2 u p.domain p.wires z || (y2 u p.domain p.wires a.1 && y2 u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem h47 (op : Nat) (d a b : Sig) : zN op (g4 d.toNat a) (g4 d.toNat b) = g4 d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [z13]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply d7
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply d7
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply d7
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply d7
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def r15 (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (c14 d x) 1 0)
theorem l28 (d : Sig) (a : y1) (keep : Bool) :
    r15 d.toNat (g4 d.toNat a.1) keep = v3 (fun w : y1 => d1 d w.1) a keep := by
  rw [r15,y14,v3]
  cases keep
  · cases d1 d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List y1) (p : f4) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : y1 => g4 d w.1)
  (d,ms.countP (c14 d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (g4 d)) m) 0 1).sum,ms,p.wires.map (g4 d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List y1) (p : f4) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (g4 d) p.wires fun pm => forceMap (fun w : y1 => g4 d w.1) ws fun ms =>
  force (ms.countP (c14 d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem w25 {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,d9,l14,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List y1) (ps : List f4) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem z22 {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [w25,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := g3 × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : g3) : Lane :=
  let ws := c.2.2.1.map (fun w : y1 => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List g3) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : y1 => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem s15 {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : y1 => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [d9,d9,l14,d9,z22,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (r15 s.1 x ka)) (r15 s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (c14 s.1 (zN op x y)) false))
theorem g41 {d : Nat} (ws : List y1) (i : Nat) (hd : g4 d zero=0) :
    (ws.map (fun w : y1 => g4 d w.1)).getD i 0 = g4 d (ws.getD i p3).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem n39 {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    n16 u p ws k (ws.getD i p3) (ws.getD j p3) op ka kb=true := by
  have z0 : g4 p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [g4,this]
  have su : (((ws.map (fun w : y1 => g4 p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat)) (g4 p.domain.toNat w.1)) 0 1 = _
    rw [z14]
    rfl
  simp only [fastCost,quickSpec,d9,g41 _ _ z0,su,List.countP_map,Function.comp_def,y14] at h
  generalize ws.getD i p3=a at h ⊢
  generalize ws.getD j p3=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat))) (g4 p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat))) (g4 p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : y1 => d1 p.domain w.1)) (r15 p.domain.toNat (g4 p.domain.toNat a.1) ka)) (r15 p.domain.toNat (g4 p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat))) (zN op (g4 p.domain.toNat a.1) (g4 p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : y1 => d1 p.domain w.1)) (r15 p.domain.toNat (g4 p.domain.toNat a.1) ka)) (r15 p.domain.toNat (g4 p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat))) (g4 p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (g4 p.domain.toNat))) (g4 p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : y1 => d1 p.domain w.1)) (r15 p.domain.toNat (g4 p.domain.toNat a.1) ka)) (r15 p.domain.toNat (g4 p.domain.toNat b.1) kb)))) (c14 p.domain.toNat (zN op (g4 p.domain.toNat a.1) (g4 p.domain.toNat b.1))) false)) = true := h
  rw [h47,y14,z14,z14,z14,l28,l28] at h
  have ca : d1 p.domain (bin op a.1 b.1)=true → y2 u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [y2,d1,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [n16,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => d1 p.domain w.1) - v3 (fun w : y1 => d1 p.domain w.1) a ka -
      v3 (fun w : y1 => d1 p.domain w.1) b kb = c at h ⊢
    generalize d1 p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize y2 u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]
theorem v39 (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem y33 (xs : List Sig) : b22 xs = (xs.map z8).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+z8 x) a = a+(xs.map z8).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem l22 (f : y1 → Nat) {ws : List y1} {a b : y1} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((z5 ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List y1} {x : y1} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [z5,l10,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem b23 {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : t12 u op=true)
    (h : n16 u p ws k a b op ka kb=true) :
    p5 u p k ((z5 ws a b ka kb).map Prod.fst) (w4 op a b)=true := by
  let const := fun w : y1 => d1 p.domain w.1
  let z := bin op a.1 b.1
  let rest := z5 ws a b ka kb
  have ck := c39 const ws a b ka kb
  change ws.countP const - v3 const a ka - v3 const b kb ≤ rest.countP const at ck
  simp only [n16,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := l22 (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((z5 ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (y2 u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : y2 u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!y2 u p.domain p.wires z) || choiceOK u p.domain p.wires (w4 op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,w4,x,y,al]
  change k+p.paid+(!y2 u p.domain p.wires z).toNat < p.bound+(ws.countP const - v3 const a ka -
        v3 const b kb+(d1 p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : t3 (w4 op a b)=z := rfl
  simp only [p5,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!y2 u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if d1 p.domain z then 1 else 0)
  cases hc' : d1 p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem z34 (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : g4 one.toNat v = v.toNat := by
    rw [z13]
    congr 1
    exact BitVec.and_allOnes
  have := h47 op one a b
  rwa [e,e,e] at this
theorem getW (ws : List y1) (i : Nat) :
    (ws.map (fun w : y1 => w.1.toNat)).getD i 0 = (ws.getD i p3).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem d35 {c : g3} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (t0 c i).1 ≠ (t0 c j).1 := by
  have gi : t0 c i = c.2.2.1[i] := by simp [t0,List.getD_eq_getElem?_getD,hi]
  have gj : t0 c j = c.2.2.1[j] := by simp [t0,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem t33 {c : g3} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (b22 (t3 (w4 op (t0 c i) (t0 c j)) ::
      (z5 c.2.2.1 (t0 c i) (t0 c j) ka kb).map Prod.fst))).any (t10
      (t3 (w4 op (t0 c i) (t0 c j)) ::
      (z5 c.2.2.1 (t0 c i) (t0 c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : t0 c t ∈ c.2.2.1 := by
    simp [t0,List.getD_eq_getElem?_getD,ht]
  have hne := d35 nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : t0 c i ≠ t0 c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := c22 nd ha hb ka kb v
  have sum := l22 (fun w : y1 => z8 w.1) ha hb hab ka kb
  have wi : t0 c i = c.2.2.1.getD i p3 := rfl
  have wj : t0 c j = c.2.2.1.getD j p3 := rfl
  simp only [linkAt,laneOf,d9,getW,←wi,←wj,z34] at h
  generalize t0 c i=a at *
  generalize t0 c j=b at *
  change Option.rec false _ (fl (z8 (bin op a.1 b.1)+(((c.2.2.1.map (fun w : y1 => w.1.toNat)).map kwN).sum -
    (cond ka 0 (z8 a.1)) - (cond kb 0 (z8 b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : y1 => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : y1 => z8 w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : b22 (t3 (w4 op a b) :: (z5 c.2.2.1 a b ka kb).map Prod.fst) =
      z8 (bin op a.1 b.1)+((z5 c.2.2.1 a b ka kb).map (fun w : y1 => z8 w.1)).sum := by
    rw [y33,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize b22 (t3 (w4 op a b) :: (z5 c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [l14,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,v39,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [t10,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (l13 l.1 i j op ka kb)
theorem h22 {c : g3} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    l13 c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : t12 c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [t12] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : t0 c t ∈ c.2.2.1 := by
      simp [t0,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := d35 nd hi hj (fun e => by simp [e] at hn)
    have closed := b23 (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (n39 ok)
    have cut : c.2.2.2.2.1.any (fun p => p5 c.2.2.2.1.2 p (c.1-1)
        ((z5 c.2.2.1 (t0 c i) (t0 c j) ka kb).map Prod.fst)
        (w4 op (t0 c i) (t0 c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [l13,d10,r9,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := t33 nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [l13,d10,r9,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def l16 (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def j9 (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem v32 : ∀ v : Fin 144, j9 v.val=true → ∀ t : Fin 9, l16 v.val t.val<9 ∧
    s13 (h7 v.val) (inputs.getD t.val zero) = inputs.getD (l16 v.val t.val) zero := by decide +kernel
theorem w32 {v t : Nat} (hv : j9 v=true) (ht : t<9) : l16 v t<9 ∧
    s13 (h7 v) (inputs.getD t zero) = inputs.getD (l16 v t) zero := by
  have lt : v<144 := by
    simp only [j9,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact v32 ⟨v,lt⟩ hv ⟨t,ht⟩
def x42 (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => l16 v t) t
theorem w42 {perm : List Nat} (ok : perm.all j9=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map h7).reverse (inputs.getD t zero) = inputs.getD (x42 perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := w32 ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem p34 (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List y1) :
    (l11 n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List y1) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i p3).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,d9,l11,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem g20 {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (m6 bits ws).map f = m6 bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,m6,m6]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : w1) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (y7 g.mask).map fun e => (inputs.getD (x42 perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (h17 (g.levels k) (y7 g.mask).length i) fun rec =>
  m6 (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem y25 (g : w1) (k i : Nat) {perm : List Nat} (ok : perm.all j9=true) :
    fastState g k i perm = ((s4 g k i).map (movedWord (perm.map h7).reverse)).map BitVec.toNat := by
  let ms := (perm.map h7).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [n5,(l12 _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [z34,n5,k20,n5,n5]
  have raw : (q11 g).map (fun w => F w.1) = (y7 g.mask).map fun e => (inputs.getD (x42 perm e.1) zero).toNat := by
    simp only [q11,q16,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := v13 hm
    exact congrArg BitVec.toNat (w42 ok hj)
  have len : (q11 g).length = (y7 g.mask).length := by simp [q11,q16]
  unfold fastState s4 p16
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [d9,p18,len]
  rw [List.map_map,List.map_map,g20,←raw,←p34 F F0 Fb]
  rfl
noncomputable def linkedFast (g : w1) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all j9) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : w1) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : c25) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := n12 b i
    let b' := n12 b j
    let z := g11 op a b'
    let mask := d15 r (z12 cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    t16 (fun c => fallbackAt fl c i j op ka kb) mask xs
theorem k26 {fl u} (k n) (xs : List g3) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (j7 k n xs) (xs.map laneOf) i j op ka kb=true) :
    l13 xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : l13 xs[q] i j op ka kb =
      if len>k then true else if d18 xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !v6 (dbin op (t0 xs[q] i) (t0 xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (t0 xs[q] i) (t0 xs[q] j)).1)
      then true else r9 u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((z5 xs[q].2.2.1 (t0 xs[q] i) (t0 xs[q] j) ka kb).map Prod.fst)
        (w4 op (t0 xs[q] i) (t0 xs[q] j)) := by
    simp only [l13,d10,budget,arity,mode,len,d18] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := b20 xs.length
    let a := n12 (j7 k n xs) i
    let b := n12 (j7 k n xs) j
    let cov := x14 (fun c : g3 => c.2.2.2.1.1) xs
    change (if len>k then true else t16 _ (d15 r
       (z12 cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (g11 op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := w18 k n xs hi
    have cb : b = _ := w18 k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,r38,g12,g12,g12,s22,z20] at pass
    by_cases hit : d18 xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply h22 nd hfl
      have m := y38 _ _ _ q (by simpa using hq) (by
        rw [c46 _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : c25) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : c25) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (r20 u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : c25) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
theorem j26 {fl u} (k n) (xs : List g3) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (j7 k n xs) (xs.map laneOf) js=true) :
    q10 xs[q] (js.map (t0 xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,q10,f25,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @k26 fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [c11,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List g3) :=
    batchRows fl u (j7 k n xs) (xs.map laneOf) (List.range n)
theorem x27 {fl u k n} {xs : List g3} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : q10 xs[q] xs[q].2.2.1=true := by
  have all := j26 k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (t0 xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [t0,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def w10 (g : w1) (k i : Nat) : g3 :=
  let raw := q11 g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := p16 g k i
  let rules := (y18 (g.levels k) raw.length i).filterMap (fun (a,b) => h15 g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (l9 g (k-1))).toList
  (k,ws.length,ws,m20 g.mode ws,rules,ls)
theorem z46 (g : w1) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (w10 g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (l9 g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,l9]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all j9 with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(s4 g (k-1) pair.1).map (movedWord (perm.map h7).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (y25 g _ _ hv)
def g33 (T : Sig) (c : g3) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem v25 (g : w1) (k i : Nat) :
    j6 g k i = (g33 (m3 g) (w10 g k i) &&
      (if k=0 then true else q10 (w10 g k i) (w10 g k i).2.2.1)) := rfl
theorem z38 {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → j6 g k i = true) :
    z1 g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [z1,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def m11 (g : w1) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (w10 g k)
def y42 (g : w1) (k start n ar : Nat) :=
  (m11 g k start n).all (fun c => c.2.1==ar && g33 (m3 g) c)
noncomputable def rowCut (g : w1) (k start n ar lo len : Nat) :=
  let xs := m11 g k start n
  let b := j7 k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem q17 {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (j7 k ar (m11 g k start n)) ((m11 g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,s15] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem l25 {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,s15]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact q17 h (lo+j) (by omega) (by omega)
  · exact q17 t (lo+j) (by omega) (by omega)
theorem c47 {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (m11 g k start n)=true := by
  let xs := m11 g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (j7 k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := q17 h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem q39 {g k start n ar} (hd : y42 g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : z1 g k start n=true := by
  apply z38
  intro i lo hi
  let xs := m11 g k start n
  have hm : w10 g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [g33,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => z46 g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [v25,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ x27 hq hb ha hm nd hfl hn (c47 h)
def s30 (g : w1) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => s30 g k start n ar lo (num/2) d ∧ s30 g k start n ar (lo+num/2) (num-num/2) d
theorem s43 {g k start n ar lo num d} (h : s30 g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := l25 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def s2 (g : w1) (k start n ar rows : Nat) : Nat → Prop
  | 0 => y42 g k start n ar=true ∧ s30 g k start n ar 0 ar rows
  | d+1 => s2 g k start (n/2) ar rows d ∧ s2 g k (start+n/2) (n-n/2) ar rows d
theorem q34 {g k start n ar rows d} (h : s2 g k start n ar rows d) :
    z1 g k start n=true := by
  induction d generalizing start n with
  | zero => exact q39 h.1 (s43 h.2)
  | succ d ih =>
    have v := j2 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def w5 {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => w5 f (xs.take (xs.length/2)) d ∧ w5 f (xs.drop (xs.length/2)) d
theorem r7 {α f xs d} (h : @w5 α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem x32 {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : n3 T) (h : f6 u raw T L) :
    f19 u raw T one L := by
  refine ⟨id,raw,fun r => g8 r,fun a ha => ?_,j11 pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)
theorem f13 {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, f6 u (m4 q) (q0 q) (prior q))
    (e : (q0 q == q0 m && (m4 q == vars m) && (prior q == cap+1) && v6 (q0 m) &&
      decide (vars m).Nodup && r16 u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    v0 u (q0 m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact m15 (x32 (x7 _ e4) h) [] rfl e5 e6
theorem q43 {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, f6 u (m4 q) (q0 q) (prior q)) (ci : z2)
    (ok : p11 m ci prior = true)
    (cut : (decide ws.Nodup && r16 u (r11 ci.1 ci.2.1) ci.2.2.2.2 cap 0 (m4 (s11 m ci)) ws)=true) :
    v0 u (q0 m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact m15 (q12 ci prior low ok) [] rfl cut.1 cut.2
theorem n8 {u} {g : w1} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, f6 u (m4 q) (q0 q) (prior q))
    (geom : q2 g prior = true) (blocks : l4 g cap)
    (idx : q8 g cap i ws = true) : v0 u (q0 m) cap ws.toFinset := by
  subst hm
  subst hu
  exact j20 low geom blocks (Nat.le_refl _) idx
def r47 (m hints : Nat) : Bool :=
  let xs := z33 m hints
  v6 (q0 m) && v4 (q0 m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem q5 {u} {m hints cap : Nat} (ok : r47 m hints = true)
    (a : v0 u (q0 m) cap (vars m).toFinset) : f6 u (vars m) (q0 m) (cap+1) := by
  simp only [r47,Bool.and_eq_true,beq_iff_eq] at ok
  apply v17 (x7 _ ok.1.1) (z4 ok.1.2).1 (z4 ok.1.2).2 _ a
  intro v hv
  apply s10 ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv
def z40 (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((y7 m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def f22 (m : Nat) (rs : List Nat) : Bool :=
  let xs := z40 m rs
  v4 (q0 m) (m4 m) xs && (xs.map Prod.fst == vars m) &&
    v6 (q0 m) && decide (m4 m = vars m ++ [k16 (m/512-1)])
theorem l34 {u} {m : Nat} {rs : List Nat} (ok : f22 m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (q0 m) k S) (sub : ∀ v ∈ S, v ∈ m4 m) :
    S=(vars m).toFinset ∨ S=(m4 m).toFinset := by
  simp only [f22,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := s10 ess v (List.mem_toFinset.mpr hv)
    exact v8 h (m4 m) v sub r s hd hi
  have mem : ∀ v, v ∈ m4 m ↔ v ∈ vars m ∨ v=k16 (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : k16 (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem s27 {u} {m q cap : Nat} {rs : List Nat} (ok : f22 m rs = true)
    (e : q0 m = q0 q) (ev : vars m = vars q)
    (a : v0 u (q0 q) cap (vars q).toFinset)
    (b : v0 u (q0 q) cap (m4 m).toFinset) :
    f6 u (m4 m) (q0 m) (cap+1) := by
  have ok' := ok
  simp only [f22,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := d13 (x7 _ ok'.1.2) (z4 ok'.1.1.1).1 (z4 ok'.1.1.1).2 hr ha
  by_contra! small
  rcases l34 ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
def v33 (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩
def k42 {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem s25 {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
theorem t25 {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨v33 T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := s25 tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨k42 d01 ha hb fresh H⟩
def w3 (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
theorem x18 {S T v p n} (H : KWRooms S T) (one : w3 S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw
theorem f46 {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : w3 S T a p na) (B : w3 S T b p nb)
    (C : w3 S T a pa n) (D : w3 S T b pb n) : v0 false T k S := by
  intro j hj run
  have lb := s25 run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := t25 run tight
  exact different (H.unique (H.rect (x18 H A) (x18 H C)) (H.rect (x18 H B) (x18 H D)))
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot
def p43 {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def r29 {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩
def z25 {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }
def s29 {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem n18 {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def c26 {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := n18 F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,k42 hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := n18 ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      s29 hd ha hb (by simp [z]) old⟩
def j22 {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ r29 (p43 H a)
  have H1 := s29 hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,v33 a,r29 H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem z41 {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨z25 (v33 T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := s25 tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := t25 tail (by change (insert z U).card=k+1; omega)
        exact ⟨j22 hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := t25 tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := j22 hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨c26 hd01 fa fb zU F⟩
theorem b26 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem f9 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : w3 S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw
theorem s17 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : w3 S T a p na) (B : w3 S T b p nb)
    (C : w3 S T a pa n) (D : w3 S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (f9 F aout A) (f9 F aout C))
    (F.outside.rect (f9 F bout B) (f9 F bout D)))
theorem y17 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : w3 F.inner F.pivot a p na) (B : w3 F.inner F.pivot b p nb)
    (C : w3 F.inner F.pivot a pa n) (D : w3 F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (x18 F.inside A) (x18 F.inside C))
    (F.inside.rect (x18 F.inside B) (x18 F.inside D)))
theorem p8 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : w3 S T v p n) : w3 F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply b26 F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem y3 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : w3 S T a p na) (br : w3 S T b pa n) (cr : w3 S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := p8 F ia ar
  have bh := p8 F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem k4 {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : w3 S T a p na) (h2 : w3 S T b p nb)
    (h3 : w3 S T a pa n) (h4 : w3 S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact y17 F ne (p8 F ia h1) (p8 F ib h2)
      (p8 F ia h3) (p8 F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact s17 F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def g13 (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem z7 {ws T v p n} (h : g13 ws T v p n=true) :
    w3 ws.toFinset T v p n := by
  simp only [g13,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
def v11 (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def b21 (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := v11 pos (field 2)
  let n := v11 neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    g13 ws T a p (v11 neg (field 4)) && g13 ws T b p (v11 neg (field 5)) &&
    g13 ws T a (v11 pos (field 6)) n && g13 ws T b (v11 pos (field 7)) n
theorem y16 {pos neg T ws k v} (h : b21 pos neg T ws k v=true) : v0 false T k ws.toFinset := by
  simp only [b21,Bool.and_eq_true,decide_eq_true_eq] at h
  exact f46 h.1.1.1.1.1 h.1.1.1.1.2 (z7 h.1.1.1.2)
    (z7 h.1.1.2) (z7 h.1.2) (z7 h.2)
def d3 (g : w1) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → j6 g k j=true ∨ v0 g.mode (m3 g) k (s4 g k j).toFinset
theorem p0 (g : w1) (k a : Nat) : d3 g k a 0 := by
  intro j lo hi
  omega
theorem g1 {g k a n} (h : z1 g k a n=true) : d3 g k a n :=
  fun j lo hi => Or.inl (p22 h j lo hi)
theorem m0 {g k a x y} (first : d3 g k a x) (last : d3 g k (a+x) y) :
    d3 g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def j42 (pos neg : Nat) (g : w1) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => b21 pos neg (m3 g) (s4 g k (a+j)) k (z3 data (32*j) 32))
theorem c10 {pos neg g k a n data} (mode : g.mode=false) (h : j42 pos neg g k a n data=true) :
    d3 g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change b21 pos neg _ (s4 g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact y16 hh
def t4 (g : w1) (top : Nat) := ∀ k ≤ top, d3 g k 0 (g.levels k).1
theorem n28 (g : w1) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, f6 g.mode (m4 q) (q0 q) (prior q))
    (geometry : q2 g prior=true) (rows : t4 g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, v0 g.mode (m3 g) k (s4 g k i).toFinset := by
  simp only [q2,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact x6 g 0 i (w11 geometry.1.1.1 geometry.1.1.2)
        (fun x hx => q12 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact x6 g _ i (w11 geometry.1.1.1 geometry.1.1.2)
        (fun x hx => q12 _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem p23 {g top prior k i ws} (lower : ∀ q, f6 g.mode (m4 q) (q0 q) (prior q))
    (geom : q2 g prior=true) (blocks : t4 g top) (le : k≤top)
    (idx : q8 g k i ws=true) : v0 g.mode (m3 g) k ws.toFinset := by
  simp only [q8,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←g10 idx.2]
  exact n28 g top prior lower geom blocks _ le i idx.1
abbrev h9 := Nat × Nat × Nat
def q6 (arity : Nat) (tags : List h9) : Prop :=
  ∀ {S T}, (F : SingleFactor S T) → (w : Nat → Sig) → (p n : Nat → Row) →
    (∀ i<arity, w i∈S) → (∀ i<arity, ∀ j<arity, i≠j → w i≠w j) →
    (∀ t∈tags, w3 S T (w t.1) (p t.2.1) (n t.2.2)) → False
structure PanelProof where
  arity : Nat
  tags : List h9
  closed : q6 arity tags
def w35 : List h9 := [(0,0,2),(1,1,2),(2,2,3),(3,3,3),(0,4,1),(1,4,3),(2,5,0),(3,5,1),(3,5,2)]
theorem k28 (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A2 → A1) → (A0 → A3 → A1) → (A2 → A1 → A3) → False := by tauto
theorem s50 : q6 4 w35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,2) (by decide)
  have c1 := s2 (1,1,2) (by decide)
  have c2 := s2 (2,2,3) (by decide)
  have c3 := s2 (3,3,3) (by decide)
  have c4 := s2 (0,4,1) (by decide)
  have c5 := s2 (1,4,3) (by decide)
  have c6 := s2 (2,5,0) (by decide)
  have c7 := s2 (3,5,1) (by decide)
  have c8 := s2 (3,5,2) (by decide)
  have r0 := k4 F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := k4 F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := y3 F c5 c7 c4
  have r3 := y3 F c4 c2 c5
  have r4 := y3 F c4 c3 c5
  have r5 := y3 F c6 c1 c8
  exact k28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def v35 : List h9 := [(0,0,1),(1,1,3),(2,2,0),(1,2,2),(3,3,1),(2,3,3),(3,4,2),(0,4,3)]
theorem j28 (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A3 → A1) → (A2 → A0 → A3) → (A3 → A1 → A2) → (A0 → A1 → A3) → False := by tauto
theorem r50 : q6 4 v35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,1) (by decide)
  have c1 := s2 (1,1,3) (by decide)
  have c2 := s2 (2,2,0) (by decide)
  have c3 := s2 (1,2,2) (by decide)
  have c4 := s2 (3,3,1) (by decide)
  have c5 := s2 (2,3,3) (by decide)
  have c6 := s2 (3,4,2) (by decide)
  have c7 := s2 (0,4,3) (by decide)
  have r0 := k4 F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := k4 F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c7 c6 c0 c4
  have r2 := y3 F c2 c6 c3
  have r3 := y3 F c5 c0 c4
  have r4 := y3 F c4 c1 c5
  have r5 := y3 F c7 c3 c6
  exact j28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def t35 : List h9 := [(0,0,2),(1,1,1),(2,2,0),(1,2,2),(3,3,0),(0,3,1),(2,4,1),(3,4,2)]
theorem h28 (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A2) → (A2 → A0 → A1) → False := by tauto
theorem q50 : q6 4 t35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,2) (by decide)
  have c1 := s2 (1,1,1) (by decide)
  have c2 := s2 (2,2,0) (by decide)
  have c3 := s2 (1,2,2) (by decide)
  have c4 := s2 (3,3,0) (by decide)
  have c5 := s2 (0,3,1) (by decide)
  have c6 := s2 (2,4,1) (by decide)
  have c7 := s2 (3,4,2) (by decide)
  have r0 := k4 F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c6
  have r1 := k4 F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c5 c4 c0 c7
  have r2 := k4 F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c7 c2 c4
  have r3 := y3 F c3 c4 c2
  have r4 := y3 F c2 c0 c3
  exact h28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def s35 : List h9 := [(0,0,0),(1,1,0),(2,2,3),(3,3,3),(2,4,1),(3,4,2),(1,5,1),(1,5,2),(0,5,3)]
theorem g28 (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (A3 → A1 → A2) → (A2 → A1 → A3) → (A0 → A2 → A1) → (A0 → A3 → A1) → False := by tauto
theorem p50 : q6 4 s35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,0) (by decide)
  have c1 := s2 (1,1,0) (by decide)
  have c2 := s2 (2,2,3) (by decide)
  have c3 := s2 (3,3,3) (by decide)
  have c4 := s2 (2,4,1) (by decide)
  have c5 := s2 (3,4,2) (by decide)
  have c6 := s2 (1,5,1) (by decide)
  have c7 := s2 (1,5,2) (by decide)
  have c8 := s2 (0,5,3) (by decide)
  have r0 := k4 F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c4 c5 c2 c3
  have r1 := k4 F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c8 c7 c0 c1
  have r2 := y3 F c5 c6 c4
  have r3 := y3 F c4 c7 c5
  have r4 := y3 F c8 c4 c6
  have r5 := y3 F c8 c5 c7
  exact g28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def r35 : List h9 := [(0,0,3),(1,1,3),(2,2,3),(3,3,3),(0,4,1),(1,4,2),(2,5,0),(3,5,1),(3,5,2)]
theorem f28 (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A3 → A1) → (A2 → A0 → A3) → (A2 → A1 → A3) → False := by tauto
theorem n50 : q6 4 r35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,3) (by decide)
  have c1 := s2 (1,1,3) (by decide)
  have c2 := s2 (2,2,3) (by decide)
  have c3 := s2 (3,3,3) (by decide)
  have c4 := s2 (0,4,1) (by decide)
  have c5 := s2 (1,4,2) (by decide)
  have c6 := s2 (2,5,0) (by decide)
  have c7 := s2 (3,5,1) (by decide)
  have c8 := s2 (3,5,2) (by decide)
  have r0 := k4 F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := k4 F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := y3 F c5 c7 c4
  have r3 := y3 F c4 c8 c5
  have r4 := y3 F c6 c4 c7
  have r5 := y3 F c6 c5 c8
  exact f28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def q35 : List h9 := [(0,0,2),(1,1,3),(2,2,0),(1,2,4),(3,3,1),(2,3,3),(0,3,4),(3,4,2),(4,4,3),(4,4,4)]
theorem d28 (A0 A1 A2 A3 A4 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A0 → A1) → (A3 → A1 → A2) → (A0 → A1 → A2) → (A2 → A4 → A1) → (A3 → A2 → A4) → False := by tauto
theorem m50 : q6 5 q35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,2) (by decide)
  have c1 := s2 (1,1,3) (by decide)
  have c2 := s2 (2,2,0) (by decide)
  have c3 := s2 (1,2,4) (by decide)
  have c4 := s2 (3,3,1) (by decide)
  have c5 := s2 (2,3,3) (by decide)
  have c6 := s2 (0,3,4) (by decide)
  have c7 := s2 (3,4,2) (by decide)
  have c8 := s2 (4,4,3) (by decide)
  have c9 := s2 (4,4,4) (by decide)
  have r0 := k4 F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := k4 F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c6 c4 c0 c7
  have r2 := y3 F c2 c6 c3
  have r3 := y3 F c4 c1 c5
  have r4 := y3 F c6 c1 c5
  have r5 := y3 F c2 c9 c3
  have r6 := y3 F c7 c5 c8
  exact d28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) (w 4∈F.inner) r0 r1 r2 r3 r4 r5 r6
def p35 : List h9 := [(0,0,0),(1,1,0),(2,2,3),(2,3,1),(3,3,2),(1,4,2),(0,4,3),(1,5,1),(3,5,3)]
theorem c28 (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A1 ∧ A3) ∨ (¬A1 ∧ ¬A3)) → False) → (A2 → A1 → A3) → (A0 → A3 → A1) → False := by tauto
theorem l50 : q6 4 p35 := by
  intro S T F w p n mem diff s2
  have c0 := s2 (0,0,0) (by decide)
  have c1 := s2 (1,1,0) (by decide)
  have c2 := s2 (2,2,3) (by decide)
  have c3 := s2 (2,3,1) (by decide)
  have c4 := s2 (3,3,2) (by decide)
  have c5 := s2 (1,4,2) (by decide)
  have c6 := s2 (0,4,3) (by decide)
  have c7 := s2 (1,5,1) (by decide)
  have c8 := s2 (3,5,3) (by decide)
  have r0 := k4 F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c3 c4 c2 c8
  have r1 := k4 F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c6 c5 c0 c1
  have r2 := k4 F (mem 1 (by decide)) (mem 3 (by decide)) (diff 1 (by decide) 3 (by decide) (by decide)) c7 c8 c5 c4
  have r3 := y3 F c3 c5 c4
  have r4 := y3 F c6 c4 c5
  exact c28 (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def x45 : Nat → PanelProof
  | 0 => ⟨4,w35,s50⟩
  | 1 => ⟨4,v35,r50⟩
  | 2 => ⟨4,t35,q50⟩
  | 3 => ⟨4,s35,p50⟩
  | 4 => ⟨4,r35,n50⟩
  | 5 => ⟨5,q35,m50⟩
  | _ => ⟨4,p35,l50⟩
def j33 (arity : Nat) (ws : List Sig) (w : Nat→Sig) :=
  (List.range arity).all (fun i => decide (w i∈ws) &&
    (List.range arity).all (fun j => (i==j) || decide (w i≠w j)))
def q20 (pc : PanelProof) (ws : List Sig) (T : Sig) (w : Nat→Sig) (p n : Nat→Row) :=
  j33 pc.arity ws w &&
    pc.tags.all (fun t => g13 ws T (w t.1) (p t.2.1) (n t.2.2))
theorem s16 {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h
theorem c16 {pc ws T w p n} (F : SingleFactor (List.toFinset ws) T)
    (h : q20 pc ws T w p n=true) : False := by
  have ij := (s16 h).1
  have hrow (i : Nat) (hi : i<pc.arity) := s16
    (List.all_eq_true.mp ij i (List.mem_range.mpr hi))
  apply pc.closed F w p n
  · intro i hi
    exact List.mem_toFinset.mpr (of_decide_eq_true (hrow i hi).1)
  · intro i hi j hj ne
    have one := List.all_eq_true.mp (hrow i hi).2 j (List.mem_range.mpr hj)
    have diff : (i==j)=false := beq_eq_false_iff_ne.mpr ne
    simpa only [diff,Bool.false_or,decide_eq_true_eq] using one
  · intro t ht
    exact z7 (List.all_eq_true.mp (s16 h).2 t ht)
def w14 (pos neg : Nat) (ws : List Sig) (T : Sig) (k rec : Nat) :=
  let field := fun i => (rec >>> (4*i)) &&& 15
  decide (k≤ws.toFinset.card) && q20 (x45 (field 0)) ws T
    (fun i => ws.getD (field (1+i)) zero)
    (fun i => v11 pos (field (6+i))) (fun i => v11 neg (field (12+i)))
theorem n13 {pos neg ws T k rec} (ok : w14 pos neg ws T k rec=true) :
    v0 false T k ws.toFinset := by
  obtain ⟨bound,check⟩ := s16 ok
  intro j hj live
  obtain ⟨F⟩ := z41 live (hj.trans (of_decide_eq_true bound))
  exact c16 F check
def p47 : Nat:=(d0 [38738673928,0x4210842110c0300c03])
def q47 : Nat:=(d0 [54056593669,0x68325147434114642a])
def p13 (pos neg : Nat) (g : w1) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun i => w14 pos neg (s4 g k (start+i)) (m3 g) k (data i))
theorem h19 {pos neg g k start n data} (mode : g.mode=false)
    (ok : p13 pos neg g k start n data=true) : d3 g k start n := by
  intro j lo hi
  right
  rw [mode]
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  change w14 pos neg (s4 g k (start+(j-start))) (m3 g) k _=true at h
  rw [e] at h
  exact n13 h
def f12 (pos neg : Nat) (g : w1) (k i : Nat) (kw panels : Nat→Nat) (tag : Nat) :=
  if tag=0 then j6 g k i else if tag<128 then
    b21 pos neg (m3 g) (s4 g k i) k (z3 kw (32*(tag-1)) 32)
  else w14 pos neg (s4 g k i) (m3 g) k (z3 panels (68*(tag-128)) 68)
def z15 (pos neg : Nat) (g : w1) (k start n : Nat) (kw panels : Nat→Nat) (data : Nat) :=
  (List.range n).all fun j => f12 pos neg g k (start+j) kw panels ((data >>> (8*j)) &&& 255)
theorem j0 {pos neg g k start n kw panels data} (mode : g.mode=false)
    (h : z15 pos neg g k start n kw panels data=true) : d3 g k start n := by
  intro j lo hi
  have one := List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
  have eq : start+(j-start)=j := by omega
  change f12 pos neg g k (start+(j-start)) kw panels _=true at one
  rw [eq] at one
  unfold f12 at one
  split at one
  · exact Or.inl one
  · right
    rw [mode]
    split at one
    · exact y16 one
    · exact n13 one
theorem m2 {u} {g : w1} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, f6 u (m4 q) (q0 q) (prior q))
    (geom : q2 g prior=true) (blocks : t4 g cap)
    (idx : q8 g cap i ws=true) : v0 u (q0 m) cap ws.toFinset := by
  subst hm
  subst hu
  exact p23 low geom blocks (Nat.le_refl _) idx
theorem l0 {g k start n} (arity rows depth : Nat)
    (proof : s2 g k start n arity rows depth := by
      simp only [s2, s30, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel) : z1 g k start n = true := q34 proof
theorem w2 {g : w1} {prior : Nat → Nat} (columns autos : Nat)
    (pos : (z6 g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) = true := by decide +kernel)
    (neg : (z6 g.mask (fun j => (g.samples j).2) == 0) = true := by decide +kernel)
    (col : w5 (fun c => p11 g.mask c prior) g.cols columns := by
      simp only [w5]
      repeat' apply And.intro
      all_goals decide +kernel)
    (aut : w5 (fun p => k18 (m3 g) (p.map h7)) g.autos autos := by
      simp only [w5]
      repeat' apply And.intro
      all_goals decide +kernel) : q2 g prior = true := by
  simp only [q2, Bool.and_eq_true]
  exact ⟨⟨⟨pos, neg⟩, r7 col⟩, r7 aut⟩
theorem k0 {u m q cap} (rows : List Nat)
    (plain : v0 u (q0 q) cap (vars q).toFinset)
    (mixed : v0 u (q0 q) cap (m4 m).toFinset)
    (essential : f22 m rows = true := by decide +kernel)
    (target : q0 m = q0 q := by decide +kernel)
    (sources : vars m = vars q := by decide +kernel) :
    f6 u (m4 m) (q0 m) (cap+1) := s27 essential target sources plain mixed
theorem g2 {u m cap} {ws : List Sig} {es} (known : t2 u es) (ci : z2)
    (valid : p11 m ci (j1 es) = true := by decide +kernel)
    (cut : (decide ws.Nodup && r16 u (r11 ci.1 ci.2.1) ci.2.2.2.2 cap 0 (m4 (s11 m ci)) ws) = true := by decide +kernel) :
    v0 u (q0 m) cap ws.toFinset := q43 (n0 es known) ci valid cut
def q25 : Array Nat := #[
  0x2015947530075400,0x801264a130061400,0x6012142630021400,0x248a38642086430,0x6014142630021400,0x8214635a0030510,0x2016947530075400,
  0x250885a290083500,0x801264a130051300,0x801264a130050380,0x268a98675086750,0x2018b4a530085400,0x250885a290072480,0x6894b35842058430,
  0x8214635a0040610,0x32800865a2007610,0xa9462587b4032500,0xa502257890023500,0x2015947530064300,0x801264a130051400,0x850265a1900504a0,
  0x2018b4a530063280,0x1328a4b653086040,0x2045947530075400,0x801264a130041300,0x2018b4a130047160,0x2018b4a530074300,0x201a947530075400,
  0x32800865a2005480,0x65b2142630021400,0x6502152690021400,0x60b2142630021400,0x18202631a0028510,0x801264a130050390,0x892a36842068430,
  0xb624519420050210,0x9a5093b784057340,0xa230690a57016570,0x5890b39842058430,0x8257691a0068510,0x2015947530065400,0xb8262631a0032610,
  0x850265a190050490,0x862008a602042081,0x851264a130061400,0x6012142630021300,0x862008a602064011,0x2016947530064380,0x248a38642064210,
  0x801264a130049280,0xa230690a57005460,0x8257691a0072610,0x268a98675075640,0x80359a7b68064570,0x850265a190050480,0x250885a290069370,
  0x32800865a2007690,0x248a38642075320,0x250885a2900724a0,0x1628a1b620086210,0x85b264a130050380,0x6502152690021500,0x8214635a1040610,
  0x6012142630071300,0x201a947530069400,0x6014142630019300,0xba84519470050210,0x6308b08965063070,0x748a28674064170,0x35a27a2986016750,
  0x6308b08965074080,0x7b8106ab90046301,0x6502152690010390,0x2108b2a531074320,0x8214635a1040910,0x801364a130061400,0xa81413570040210,
  0x9102524b31005320,0x862008a6020640a1,0x2015947530064390,0x20169475300643a0,0x801264a130040280,0x205887a29107a620,0x248a38642079430,
  0x9a5093b784059340,0x5890b39842059430,0x628b1807a2001720,0x32800865a2008720,0x268a98675064530,0xa6020a827606a141,0x6894b35842047320,
  0x80359a7b68075680,0x206887a291083720,0x8244639a0038500,0x248a3b642086430,0x25b4945730057400,0x9230631a24016340,0x5a80b19870058210,
  0x43b60092163274655,0xba84519370025080,0xb64002b51056202,0x32800865a2004370,0x9a5093b784047230,0x7b44819a3067510,0x801264a130031200,
  0x6012142630071200,0x8214635a1080310,0x2051374291082570,0x621413520030710,0x851264a130041300,0x6512142630071300,0x8214635a0030410,
  0x8257691a0067510,0x6012142630081300,0x6012142630091200,0x201a947530058300,0x6b02152690021400,0x2015947530068400,0x6014142630019200,
  0x801264ab32027160,0x801264a130027160,0x32844b36a0015470,0x601bb48230048160,0x801264a130039170,0x801264a130020160,0x60b2142630021300,
  0x2016947530059400,0x2016947530065400,0x2016947530089400,0x628b1807a2001680,0x801264a130040270,0x80359a7b68042350,0x801264a130040870,
  0x253885a290059360,0xb624519420047100,0x801264a130080370,0x250885a290059260,0x2015947530053270,0x6a84b25670028070,0x63b40035069176825,
  0x630bb08965063090,0x64b0218a0017602,0x35a27a2986015640,0x35a27a2986015690,0x945759214050970,0x832008a602042081,0x628b1805a2017580,
  0x430b81a362057160,0x638006a82002451,0x32800865a2006580,0xba84519470047100,0xba84519370036100,0xba84519470049100,0x6a84b25a78036190,
  0x6012142630010380,0x268a98675068540,0x2814835a2040730,0x8351374892043620,0x9a5093b784056340,0x268a98675065840,0x2570945730048300,
  0x25b0945730058400,0x2570945730058400,0xb680519420050210,0xb684519420050210,0x628a18620068210,0x638006a85004681,0x95b264a190040870,
  0x85709ab768046570,0x2015947530085400,0xb426203741029010,0xb624519420040210,0x230881a562068120,0x2844865a2080630,0x810368a13b051370,
  0x8045947b35065400,0x8214635a1030410,0x2051374291032690,0x2018b4a53007a400,0x2051374291043720,0x8214635a1090510,0x2b40352490039400,
  0x2b10352490039400,0x6014142630021300,0x601414263001a300,0xa81413570030210,0x6014142630018300,0x6018b48530085400,0x9102524b31004210,
  0x8015947530064300,0x2015947530095400,0x8015947530095400,0x436b84a263061720,0x8200a6b50046a12,0x18202631a002a510,0x4986852a4b016730,
  0x801264a130040380,0x82b4631a0028400,0x80b264a130050390,0x2016947530064390,0x68b4b35842047320,0x25043542900324a0,0x250885a290079400,
  0x862008a602064191,0xa50225789001a390,0xa502257890012490,0x892a36b48057320,0x9a5093b784046230,0x8b40358490034500,0x892a36b48068430,
  0x896a36842068430,0x892a36b48057430,0x648b1807a2012830,0x9230631a24019340,0x892a36b48067430,0x9a6093b784059340,0x892a368420573a0,
  0x6018b48930074380,0x86a0027958016421,0x80359a7b68053460,0xa6020a8276069a41,0x26a0027950015391,0x6a84b25a78047290,0xa6020a827607a251,
  0x630bb08965063070,0x268a98675064590,0x205887a290061570,0x2308b0a562063070,0x832008a602064011,0x2308b1a56206a170,0x832008a6020641a1,
  0x628b1807a2019720,0x832008a602064091,0x628a18620075210,0x832008a602064191,0x638006a85004671,0x26a00279580153a1,0x26a0027958016421,
  0x6a84b25a78049120,0x8306907b650640a0,0xb8245693a0038400,0x32800865a20076a0,0x2015947530064380,0x80b264a130050380,0x892a36842057320,
  0x801a947b35075400,0x1368a4b653086040,0x8015947b35075400,0xb681519420050210,0x1328a4b653075830,0x250885a290068370,0x601bb48530074380,
  0x801364a130050380,0xb6040a8276083261,0x64b0218a0023812,0x2015947530064a00,0x2106927531064320,0x6890b35842047830,0xb9262637a1032610,
  0xb9452637a1032610,0x6012142630021900,0x6012142630021a00,0x90359a4b68084560,0xa9462587b4021380,0x95036ba198050470,0x5278006a84004671,
  0xa9462587b4019380,0x85b364a130050380,0x7b8006ab90046901,0xa9462587b4021480,0xa644639a0038500,0x7b8106ab90056401,0x6891b35842047320,
  0x2048b4a530085400,0x5628a18620076210,0x6512142630021400,0x8257692a0072610,0x8244635a0040610,0x8015947b30075400,0xb621519420050210,
  0x804a947530075400,0x5628a18620086210,0x4b8609b837058371,0x2054374291043720,0x80b264a130061400,0x2308b1a562079120,0x20b71ba576085213,
  0x7412079541054021,0x26ba98675078650,0x5a80b19870056210,0x62ba18620078210,0x2048b3a542065434,0xba635694a0050610,0x1a80813b70038210,
  0x2108b2a531085320,0x8b2a36842068430,0x862008a602086131,0x850265a190061500,0x18202631a0032610,0x9a6093b784057340,0x832008a602086131,
  0x26a0027958027531,0x90379a7b68075680,0x95046ba198061580,0x7b8006a830068311,0x7b8106ab90068511,0x85026ba098061580,0x86406b0a58016580,
  0x9260631a24016340,0x5896a36842068430,0x628a18620086210,0x59471b9867058123,0x76835894a3050834,0x4687b58294083506,0xa437528749032053,
  0x634ab48935085400]
def b28 (codes i : Nat) : Nat :=
  q25[(codes >>> (9*i)) &&& 511]?.getD 0
theorem d2 {g k start n} (codes : Nat)
    (mode : g.mode = false := by rfl)
    (proof : p13 p47 q47 g k start n (b28 codes) = true := by decide +kernel) :
    d3 g k start n := h19 mode proof
theorem y6 {g k start n} (data : Nat)
    (mode : g.mode = false := by rfl)
    (proof : j42 p47 q47 g k start n (fun _ => data) = true := by decide +kernel) :
    d3 g k start n := c10 mode proof
def b55 (i : Nat) : Nat:=0xf
def z54 : w0 := (1,0,1,0,0,0,0,b55)
def h34 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffffffffff3]),0x62),((d0 [255,0xffffffffffffffffff,0xffffffffffffffffbf]),(d0 [255,0xffffffffffffffffff,0xffffffffffffffff99])),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def j34 : List z2 := []
def n43 : List (List Nat) := [[],[48,33]]
def j39 : Nat → w0
  | 3 => z54
  | _ => j3
def m43 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : w1 := ⟨15,3,fun j => h34[j]?.getD (0,0),j34,n43,j39,m43⟩
set_option maxHeartbeats 0 in
theorem k46 : q2 g15 (j1 []) = true := w2 0 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem d44 : z1 g15 3 0 1=true :=
  (by decide +kernel)
theorem j38 : l4 g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 g15 0 0 0 = true)
  · exact (rfl : z1 g15 1 0 0 = true)
  · exact (rfl : z1 g15 2 0 0 = true)
  · exact d44
def z16 : Array (List Nat) := #[
  [],[101,66,16],[135,50,65],[133,117,101,33,48],[82,129,48],
  [50,65],[115,83,82,130,99,66,16],[130,50,81,115,98,65],[116,83,32],[113,97,82,32,65,48],
  [115,84,99],[128,64,116,81,96,49,32],[83,133,115,67,32,96],[128,16,64,100,80,113,33,48],[117,67,32],
  [135,101,50,33,16,64],[129,98,82,16,66,49,112],[133,117,16,64,49,32],[114,81,98,50,65],[83,114,99,33,16,64],
  [130,50,98,82,115,33,65],[128,100,49,112],[99,132,84,48,33,112],[129,82,97,48],[118,133,33,48],
  [116,100,83,32],[132,65,48,80,113,32],[67,80,100,131,112,32,16],[129,82,113,48],[130,114,98,81],
  [66,114,132,49,32,81,96],[50,117,131,49,32,65,96],[50,33,16,64],[114,33,97,82,50,65],[130,33,113,99,82,65],
  [130,33,50,113,99,82,16,64],[115,67,100,83],[131,115,65,50,98,81],[131,115,100,50,33,16,80],[117,101,67,32],
  [80,84,132,49,113,96],[117,80,66,96,16],[114,83,48,33,97,64],[129,33,97,81,16,114,49,64],[134,81,114,50,65],
  [64,132,49,96],[115,82,98,131,66,16],[98,118,81,130,50,65],[128,80,84,66,16,114,97,48],[132,116,84,48,33,96],
  [132,116,65,48,80,97,32],[66,114,50,132,99,32,80,16],[82,48],[84,115],[80,132,99,112,32,16],
  [131,67,99,116,50,33,16,80],[132,67,100,84,48,33,112],[130,50,97,115,82,16,64],[128,97,65,49,33,112],[129,80,48,50,114,97,64],
  [114,67,84,48,33,97,128],[66,16],[99,83,64,32,16],[115,50,98,83,66,16],[114,98,83,33,16,64],
  [130,114,98,49,32,81,64],[131,50,66,116,99,82],[130,50,116,49,32,97,80],[101,50,33,16,64],[83,82,114,99,66,16],
  [128,81,67,112,97,32],[83,80,132,115,96,32,16],[115,83,67],[101,117,50,33,16,64],[82,98,115,66,16],
  [128,80,117,32,16,98,65,48],[82,50,133,98,49,32,113,64],[49,50,83,48,130,113,64],[113,129,97,82,32,65,48],[99,81,115,130,65],
  [128,64,116,49,96],[131,84,115,98],[130,114,98,33,81],[82,133,99,49,32,65,112],[128,84,66,16,98,113,48],
  [131,65,50,114,81],[130,33,113,98,66,16,80],[128,80,81,67,96,113,32],[84,117,80,132,96,48,32,16],[118,130,81],
  [80,48,50,114,129,64],[100,131,82,16],[100,131,116,50,33,16,80],[33,80,112,97,130,49,64],[117,80,66,130,96,16],
  [84,131,98],[64,48,32,16],[80,64,48,32,16],[32,82,64,16],[96,80,64],
  [48,96,83,64,32,16],[115,99,83,67],[112,96,48,50,33,81,64],[114,50,99,48,33,81,64],[115,99,82,64,16],
  [115,96,83,64],[131,115,99,50,82,65],[131,115,50,98,83,66,16],[131,115,99,82,64,16],[130,114,49,98,81,64],
  [131,115,98,83,66],[131,115,98,83,32,64],[130,114,97,82,16,64],[130,50,115,98,49,32,81,64],[130,50,115,49,98,81,64],
  [48,128,115,96,50,33,81,64],[129,33,115,48,98,81,64],[32,50,128,115,98,81,64],[82,98,66,16],[131,67,116,99,82,16],
  [131,115,99,67,82,16],[128,112,96,49,64],[131,115,83,67,98],[129,113,82,65,48],[80,81,129,114,50,65,96],
  [81,33,80,128,97,114,49,64],[98,99,81,131,114,65],[48,84,100,49,129,112],[33,32,65,48],[16,64,49,32],
  [113,16,96,81,49,64],[129,113,33,98,81,48],[130,114,99,49,32,65,80],[129,113,98,16,66,49,80],[129,50,114,48,66,97,80],
  [129,116,50,97,80],[115,50,32,83,66,96,16],[112,48,50,33,97,64],[99,115,83,48,33,64],[83,80,96,115,64,32,16],
  [81,80,48,50,130,113,64],[117,101,33,32,65,48],[129,113,82,97,48],[129,33,114,82,16,66,49,96],[132,67,84,48,33,113,96],
  [128,16,113,65,49,33,96],[82,50,133,115,49,32,65,96],[81,80,128,113,98,49,64],[82,48,66,112],[83,114,64],
  [117,130,99,32,64,16],[116,100,49,81,32],[115,83,133,99,50,66,16],[84,100,49,128,113,32],[131,100,115,82,16],
  [134,117,33,32,65,48],[84,133,80,66,114,96,16],[82,48,66,129,112],[67,132,99,82,16],[117,99,49,32,65,128],
  [100,49,128],[118,101,133,50,33,16,64],[98,82,16,66,49,128],[84,66,16,98,129,48],[80,81,114,66,50,129,96],
  [116,50,129,80],[116,100,49,32,81,128]]
def f0 (old : List (Nat × Nat)) (bound : Nat) (entries : List (Nat × Nat)) :=
  z18 old bound (entries.map fun p => (p.1, z16[p.2]?.getD []))
def p19 := f0 [] 4 [(15,0),(23,96),(27,61),(29,5),(30,32),(39,97),(57,98),(78,99),(83,62),(99,100),(135,101),(156,102),(163,63),(165,33),(166,64),(172,103),(177,104),(198,105),(281,106),(291,107),(300,65),(305,108),(312,109),(323,110),(326,111),(330,112),(332,113),(344,114),(353,34),(354,35),(396,115),(424,116),(480,117)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem k35 : t2 true p19 := s0 (m:=15) z24
    (q5 (hints:=8449) (by decide +kernel) (n8 (g:=g15) (i:=0) rfl rfl (n0 [] z24) k46 j38 (by decide +kernel))) (by decide +kernel)
def w54 (i : Nat) : Nat:=0x11a20bf
def q54 : w0 := (1,0,3,0,0,0,0,w54)
def t54 (i : Nat) : Nat:=(d0 [48,0xbe6702080000650000,0x16357504004755c084])
def x54 (i : Nat) : Nat:=0x40828fd20fd10
def r54 : w0 := (2,1,3,0,0,3,0,x54)
def v54 (i : Nat) : Nat:=0x300
def y54 (i : Nat) : Nat:=0x5dd4520
def s54 : w0 := (1,2,3,0,0,0,0,y54)
def c34 : Array (Bits × Bits):=#[(0x2e44,0x2c52),(0x5a8a,0x5208),((d0 [255,0xffffffffffffffffff,0xffffffffffffffb4f7]),(d0 [255,0xffffffffffffffffff,0xffffffffffffffa0c7])),((d0 [255,0xffffffffffffffffff,0xffffffffffffffcf79]),0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def d34 : List z2 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def h29 : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def f39 : Nat → w0
  | 6 => q54
  | 5 => r54
  | 4 => s54
  | _ => j3
def l43 : Nat → Nat → Option (Nat × Nat)
  | 6 => t1 5 15 3 9 1 4 t54
  | 5 => t1 1 3 1 9 1 4 v54
  | _ => fun _ => none
def g31 : w1 := ⟨31,6,fun j => c34[j]?.getD (0,0),d34,h29,f39,l43⟩
set_option maxHeartbeats 0 in
theorem j46 : q2 g31 (j1 p19) = true := w2 0 1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem z43 : z1 g31 6 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b44 : z1 g31 5 0 2=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c44 : z1 g31 4 0 1=true :=
  (by decide +kernel)
theorem h38 : l4 g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 g31 0 0 0 = true)
  · exact (rfl : z1 g31 1 0 0 = true)
  · exact (rfl : z1 g31 2 0 0 = true)
  · exact (rfl : z1 g31 3 0 0 = true)
  · exact c44
  · exact b44
  · exact z43
def f36 := f0 p19 7 [(31,0),(167,36),(313,37),(334,38),(355,66),(428,67)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j35 : t2 true f36 := s0 (m:=31) k35
    (q5 (hints:=8449) (by decide +kernel) (n8 (g:=g31) (i:=0) rfl rfl (n0 p19 k35) j46 h38 (by decide +kernel))) (by decide +kernel)
def d36 := f0 f36 5 [(61,5),(91,1),(94,68),(181,18),(227,69),(230,19)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem h35 : t2 true d36 := s0 (m:=47) j35
    (q5 (hints:=8449) (by decide +kernel) (g2 j35 (8,0,39,0,4))) (by decide +kernel)
def c36 := f0 d36 5 [(55,0),(59,5),(103,118)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem g35 : t2 true c36 := s0 (m:=55) h35
    (q5 (hints:=257) (by decide +kernel) (g2 h35 (16,0,39,0,4))) (by decide +kernel)
def n19 := f0 c36 8 [(63,0),(95,1),(159,39),(359,119),(377,70),(462,12),(483,71),(492,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f35 : t2 true n19 := s0 (m:=63) g35
    (q5 (hints:=8449) (by decide +kernel) (g2 g35 (32,0,31,0,7))) (by decide +kernel)
def g52 (i : Nat) : Nat:=0x7213f
def c52 : w0 := (1,0,2,0,0,0,0,g52)
def f52 (i : Nat) : Nat:=0x8000
def h52 (i : Nat) : Nat:=0x17e51
def d52 : w0 := (1,1,2,0,0,0,0,h52)
def n29 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xffffffffffffffed93]),0x2d12),((d0 [255,0xffffffffffffffffff,0xffffffffffffff9467]),(d0 [255,0xffffffffffffffffff,0xffffffffffffff9025])),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def p29 : List z2 := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def l39 : List (List Nat) := [[],[32,83]]
def k34 : Nat → w0
  | 6 => c52
  | 5 => d52
  | _ => j3
def k39 : Nat → Nat → Option (Nat × Nat)
  | 6 => t1 1 3 1 6 1 1 f52
  | _ => fun _ => none
def g111 : w1 := ⟨111,6,fun j => n29[j]?.getD (0,0),p29,l39,k34,k39⟩
set_option maxHeartbeats 0 in
theorem j43 : q2 g111 (j1 n19) = true := w2 0 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem j40 : z1 g111 6 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem k40 : z1 g111 5 0 1=true :=
  (by decide +kernel)
theorem t32 : l4 g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 g111 0 0 0 = true)
  · exact (rfl : z1 g111 1 0 0 = true)
  · exact (rfl : z1 g111 2 0 0 = true)
  · exact (rfl : z1 g111 3 0 0 = true)
  · exact (rfl : z1 g111 4 0 0 = true)
  · exact k40
  · exact j40
def d17 := f0 n19 7 [(111,0),(123,1),(187,41),(190,42),(215,72),(222,73),(238,19),(243,74),(311,120),(318,121),(343,122),(349,75),(365,123),(378,43),(437,44),(455,12),(476,76),(485,124),(490,125),(497,126),(504,77)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem n27 : t2 true d17 := s0 (m:=111) f35
    (q5 (hints:=16785665) (by decide +kernel) (n8 (g:=g111) (i:=0) rfl rfl (n0 n19 f35) j43 t32 (by decide +kernel))) (by decide +kernel)
def y51 (i : Nat) : Nat:=0x163441bf
def s51 : w0 := (1,0,3,0,0,0,0,y51)
def w51 (i : Nat) : Nat:=(d0 [0x42f9f28c08140000,9279884095127760])
def z51 (i : Nat) : Nat:=0x420a3fa41fd10
def t51 : w0 := (2,1,3,0,0,3,0,z51)
def x51 (i : Nat) : Nat:=0x18000
def b52 (i : Nat) : Nat:=0xb7d8d20
def v51 : w0 := (1,2,3,0,0,0,0,b52)
def l29 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffffff55417]),(d0 [255,0xffffffffffffffffff,0xfffffffffffff46453])),(0x0,0x0),((d0 [255,0xffffffffffffffffff,0xfffffffffffffc60f7]),0x44076),((d0 [255,0xffffffffffffffffff,0xfffffffffffff0bbcb]),(d0 [255,0xffffffffffffffffff,0xfffffffffffff03a89])),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def m29 : List z2 := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def v24 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def g34 : Nat → w0
  | 7 => s51
  | 6 => t51
  | 5 => v51
  | _ => j3
def h39 : Nat → Nat → Option (Nat × Nat)
  | 7 => t1 9 13 2 9 1 4 w51
  | 6 => t1 1 3 1 9 1 4 x51
  | _ => fun _ => none
def g189 : w1 := ⟨189,7,fun j => l29[j]?.getD (0,0),m29,v24,g34,h39⟩
set_option maxHeartbeats 0 in
theorem h43 : q2 g189 (j1 d17) = true := w2 1 2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f40 : z1 g189 7 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g40 : z1 g189 6 0 2=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h40 : z1 g189 5 0 1=true :=
  (by decide +kernel)
theorem s32 : l4 g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 g189 0 0 0 = true)
  · exact (rfl : z1 g189 1 0 0 = true)
  · exact (rfl : z1 g189 2 0 0 = true)
  · exact (rfl : z1 g189 3 0 0 = true)
  · exact (rfl : z1 g189 4 0 0 = true)
  · exact h40
  · exact g40
  · exact f40
def z28 := f0 d17 8 [(189,0),(303,2),(347,20),(486,6)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem l27 : t2 true z28 := s0 (m:=189) n27
    (q5 (hints:=536879876) (by decide +kernel) (n8 (g:=g189) (i:=0) rfl rfl (n0 d17 n27) h43 s32 (by decide +kernel))) (by decide +kernel)
def c17 := f0 z28 9 [(127,0),(382,21),(478,22),(508,127)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem m27 : t2 true c17 := s0 (m:=127) l27
    (q5 (hints:=16785665) (by decide +kernel) (g2 l27 (32,0,95,0,8))) (by decide +kernel)
def y46 (i : Nat) : Nat:=0x8201ff
def w46 : w0 := (1,0,5,0,0,0,0,y46)
def x46 (i : Nat) : Nat:=(d0 [0x99090000b500,458852568751104,0xe4006080015749fa6,0x141c73802b0a68137,0x976081bca199eaaa3d,0x961388c0f3a0002328,0xc00084a05000089c2a])
def n51 (i : Nat) : Nat:=(d0 [2,0x88616180c48a1166c0,0x8c818588a2e004e68,0xc2c214019ce18588b2,0x410102944c300431c5,0x89360181384080512,0x18b0c0328614b0a030,0x139610c0803944862a,0x8614888704038c2842,0x4018278d600745a25b,0x53e43cce27c5e0bc00,0xff483fe30ff4c3fd10,0xff54ffe10ff903fe20,0xff4c7fc20ff58ffd40])
def f51 : w0 := (12,1,5,0,0,10,0,n51)
def k51 (i : Nat) : Nat:=(d0 [351843720888320,0x198cb0000a04e08a,0x520001a51c20000531,0xe80b64388d00078963,0xd80a7524800343b41a,0x670800007a7cc632d7,0x5239502d6072864000,0x60840000002a,0x100028a67e35dbbd50,0x1a6c315cd7a0d113,0xac2700012180005256,0x8158594ec000682af9,0xf6880000010b6f,0xab800321ac31374a97,0xc0018068243a2b09f0,0x6ef8c8000c984c7fad,0x8000732e29d36fd3c9,0xba4660000003c50a43,0xa2e72f0000037c5c48,0x4413000060966343d5,0x67081fd24000161fd8,0xfb857db1616c2d70bc,0x1da504981c000a8,0xcb68709baa54393350,0x153817e93b2ee08a0b,0x35c971e4812648c40c,0xf0c890074a5b901b85,0xc19b060f0f30f9c6d4,0x6f822909e468ae58b6,73289049124639786,0x8dc0d2c800031c6000,0x5ad28d4a6000000000,0x4610000000000,98371931427008,0x7fc419a5a33000612d,0xc38451b04000033fe5,0x70000002d76000244c,0x429f180a5d34b0ba13,0x60001a731afd48a565,0xb2f860060014b1d811,0x1aaaac600056d80000,681893276580045,0x5b803ae00010d91906,0xc6000000173ec82c42,0x58c80000000001b,0x509c9847ce37e90001,0xc466a9e954000000c9,0x9484d7ca82a800f934,0x47182024f80000c48d,0xc000596030083ad05a,0x1c75006c1081741081,0x4060062c3582005184,0x1c00801071c96460c2,576628352389259,0xc0000080000041016])
def p51 (j : Nat) : Nat:=(d0 [528495944,0x99e077b024a9159a24,0xb911ac077e0465c892,0x708574212ef090d670,0x221e053c214e043b82,0x35cc808a67d091c046,0xf022c0a32623f70495,0x22d15433a6477b08ce,0x33e84719314e04222,0xc097484381b79046f2,0x83ea431f521b80ae4,0x46e02b90c91ffb0022,0xff500273ff780227d0,0x9160ad1a2b008a388,0x648213e1129ec12370,0x1bbc02b6031f108e81,0x2788527a1372fef00a,0x370177821af58220f9,0x8488d80ed11b79e031,0x29f81224fe00116e0,0x8ea457911b01380878,0x4866ffa009e7c49103,0xfc0098ee0495c8319f,0x848269f5444bf2292d,0xf046e02b7ba00a2fc6,0xc027b211cfe48667a0,0x4ad80ec912592247ef,0xae68147aaa443fce,0x6009d00860143e0495,0x227c608ef0062ec24c,0x9e99123806bc624482,0x87a25ec8251c78110a,0x11258898fc21534520,0x9610e8c37008430004,0x14019102020c60a121,0xc5c5ec5844fc4543ec,0x3542cc25c1bc12409b,0xfebf43e8be1bd8bcf3,0xc73b9bae3a7b9eb983,0x8f383b7d373369b603,0x5934fb46b3ab3432bb,0x24b1b311b072fcaf62,0xedae72dc2ce2bf2b02,0xa2294a8da83a7ca70a,0x66a5ea54a4d24423c2,0x33a2aa192102069fa9,0xed9e61de9d29cd1c09,0xb21aa1a399a99498e1,0x8397416815a14f9449,0x3712b11e91590f1000,0xf10e88dd8d18ca0c08,0xb70ab8a209508407d8,0x7606b86505b8510420,0x3883182501880d0004,0x2a470a82c2e250b1c4,0x28051315c2a4b0980c,0x2c730b01c220f0b994,0x2c37098142e4308834,0x28431b894240f098cc,0x2a090881424370b12c,0x240d090ac4e43090cc,0x6e650994426530b0d4,0x4651090d4242f0b98c,0x2a490b0242c570b154,0x2c490b02c2408c3891,0xae246b94ba4107b92b,0x6e24e8849aeb66b881,0xee82a983aa6486b951,0xae707b831ae0c6bad3,0x64307b893a2047b923,0x24287b8ba6e867bb19,0xae0e6bb51ee2a7b909,0xae2c6ba49aed66b9c9,0xae607b8b1ee088a159,0xae50e9811ee4ea9821,0xeea8c98c2a60c6b921,0xae086b8b9ee467bb29,0xee62e9849ae346b8d9,0xee647baa9ee0e6b993,0xa4146b8caa64e6ba41,0xeea67b89b2a286b959,0xae4e7bb216e242b9c8,0x6e87ffff7f7efefbfd,0xf6ef6f902308821058,0xd53501314c12044020])
def g51 : w0 := (113,2,5,589836,68,12,1057,p51)
def l51 (i : Nat) : Nat:=(d0 [62487568815043,0x679268754bc6188000,0x1bef920589c626a6,0x500070140c8d5de5f1,0xd7a21d0344d98ee800,0x183ee4880000011197,0x1a189f7ac18d073c4,0x1c5a460f2f6dbb0d3e,0x90a06b82f5bcc02928,0xe3aa852e880000109c,0x34616429775d57a008,0x41de8968c753cd4f77,0x79436ba625de899899,0x71c11166c07285d41,0x58b1c40cba3819701f,0xf1ed4e0000001d75e3,0x86545f25c03c4e3ccf,0xe7905e221777000000,0xa100005011f899118,0x6d800000144100008f,0x313025a433c0cd88da,0xe660be94000121c000,0x2c88000000655b0,0xaf52342fd8c3fbe11d,0x39049a5a1e7325180,0x4d4e9a308f4f4000,0xef1802b07e014ce,0xa170acb800000009b4,0xc4008e61bc79a059a0,0xf70fccb137f85b2554,0xdc0000000f21e93d12,0x600012580034900000,707721288482816,0xb1c00000000031850,0x23a5319608aa000191,0x347800000000000000,0x4662140000000000,0x5b0dc8e00000042,0x6e6c726f99d415a6c3,0x45000127023e070c8,0xd80b889403631ef964,0xfdd2196b35879ca860,0xc0656093c9b66e604e,0x1a08c20003c8494d72,0x28964094caf59a8139,0xa149ac000c15105044,0x2c0100242082111,0x47148207881095147,0x80042047000002000,0x1001c02830c5040001,0x40080040540040204,0xc00080070800c1,0xd0040151000c0,0x40141188000004000])
def q51 (i : Nat) : Nat:=(d0 [616011088138240,0x2c2161020800838410,97068458967072,0x808400418108150880,0x8200a81105842c3401,0x8081882c400010401,0x610060400004128800,0x6508824200028421,0x410000c01624108000,0x7085060424a100000,0x220d0042c200002c20,0x410018408210b0d084,0x384082c4121090,0x80006109020848e842,0x5084082000000006,0x1881c2121000008bf,0x14a22c388670ba10c1,0x480f009fabe87c6f79,0xecbd479ef09d6ba873,0x6e39c4b7c6ded69a6b,0x48666c998cb0c5febe,0x972ae05b6b3964abc5,0x6eaa952aa0536a1940,0xa7c4ee9892aa504969,0x191ca2c44e8890ea08,0x3f67d8f89ec3be748e,0x29b83666b8d49a432e,0x628be9782e65b8b095,0x429e5089e930246458,0x8890c20e3e8728d819,0x6318608bc15e248428,0x800f61b83085c0ae14,0x8268480860b8108140,0x1e02802800df4815ca,0x209fd879c9109fd82d,0xc163df5215c620aff8,0x654931ff38148230fe,0x92054930df7715c520,0x9fd82dd530b7f85581,0x40bf7815c520bbf844,0xc1209ff815c163df77,0x1501209ff815c1539f,0xd81dc163fe92048630,0xdf920dc530ff210dc5,0x209fd825c640f75515,0x4131bf78148131df78,0x15ca10df7815ca40dd,0xf714c163bf7815cd20,0x9fd8798a409ff815ca,0x20fd5514c131df9724,0x4220bf9809c910dbf7,0x4549309ff805c5639f,0xd81dd930ded20dc963,0xcfd764c620df4815ca,0x40bf9808ca10b7f855,0x81319fd82dc530df92,0x5c630ff210481319f,0xd80dc5539fd81dd530,0xbbd849c910bf58158e,0x109ff805c963aff865,0x4940ddf714c963df77,0x15cd209fd80dd9319f,0xd82dc563df551dc131,0xddd215ce20df7714c1,0x20fe92050910df5315,0xca10df783dc5209fd8,0x25c630ded52dc931db,0xd425d640df610dd931,0x9ff815cd20bf781481,0x63df5515c1319fd82d,0xc540ddf764c1319fd8,0x78ca109fd81dcd209f,0xd80dc5639ff815ca40,0xdbd54dc940ff110dc5,0x20dbf7458130ded215,0xca30df5615d210bbf8,0x44c110ff081482309f,0xd82dd1109fd82dd540,0xdf471dcd20df771441,0x20bbf845cd20dbd425,0xc640bf7814ca10ff37,0x14c120bdf8350910bf,0x78148153df7215d210,0xbf78158131fe520485,0x31bf78154131ded724,0x8640cfd764ca209ff8,0x15c963bbf845cd10df,0x583dc520edd6358130,0xdf4715cd20df771dcd,0x20ddf714c153ff0714,0xc120fd5314ca109f78,0x15c5209f7815cd209b,0xf845c1539ef825c563,0x9bf845c1639bf845ce,0x10fe120c861097f855,0xda408fd86dd5319bf8,0x45cd209bf845c1319f,0x7815ca409f581dc163])
def h51 : w0 := (116,3,5,0,0,11,0,q51)
def m51 (i : Nat) : Nat:=(d0 [0x30450ac641c006,0x2400b2c00a0c810000,0x1c50000042a883a])
def r51 (i : Nat) : Nat:=(d0 [59906623710,0x6543ca1408fb4c102b,0x944193f85dd1604c23,0xef22c16eaa062fe1b7,0x454930cdbc26e29824,0x11f79161e6290336f0,0x838ae69056de5183dc,0x5208fb4c0e2b9a419b,0x784dc5734823ef22c1,0x6ea9847de4582dd110])
def j51 : w0 := (12,4,5,0,0,6,0,r51)
def j29 : Array (Bits × Bits):=#[((d0 [255,0xfffffffffffffda8e8,0x1df4649a4aea03f353]),(d0 [108576,0x9cc44085084a802052])),((d0 [255,0xfffffffffffffe5506,0x27bdd1589ea381610f]),(d0 [255,0xfffffffffffffe550c,0x23b884896b1415109])),((d0 [47222,0xf0435535c500a8ea8c]),(d0 [10354,0x300045166108a00a84])),((d0 [157341,0xfd182653b341a80c0]),(d0 [148108,0xbdd82211a84129140])),((d0 [87361,0x72223bd2f53d4f48e0]),(d0 [5441,0x6022395ae5314d4aa0])),((d0 [152506,0x8288d622045549630]),(d0 [151710,0x22805626105509220])),(0x0,0x0),((d0 [233217,0xc59fba0814d3746c20]),(d0 [100097,0xc597ba0892d2056500])),(0x0,0x0)]
def k29 : List z2:=q7 32 (fun x => (m1 x 0 8,m1 x 8 8,m1 x 16 8,m1 x 24 4,m1 x 28 4)) 21 (d0 [4200192,0xa840a6001940270098,0x401d00a24039008640,0xa5001a40870038409c,0x2340b1000e40a308,0x1440a61009401e2081,0x50370088401b802470,0xbe000170bb000469a6,0x100040ac001380bd00,0x270a70018701f00a0])
def z17 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def f34 : Nat → w0
  | 10 => w46
  | 9 => f51
  | 8 => g51
  | 7 => h51
  | 6 => j51
  | _ => j3
def g39 : Nat → Nat → Option (Nat × Nat)
  | 10 => t1 16 41 5 10 4 2 x46
  | 9 => t1 67 277 6 13 7 2 k51
  | 8 => t1 100 251 6 13 7 2 l51
  | 7 => t1 4 19 2 10 4 2 m51
  | _ => fun _ => none
def g191 : w1 := ⟨191,10,fun j => j29[j]?.getD (0,0),k29,z17,f34,g39⟩
set_option maxHeartbeats 0 in
theorem g43 : q2 g191 (j1 c17) = true := w2 3 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x34 : z1 g191 10 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem z39 : z1 g191 9 0 12=true :=
  (l0 8 0 2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b40 : z1 g191 8 0 113=true :=
  (@j2 g191 8 0 106 7 (@j2 g191 8 0 70 36 (@j2 g191 8 0 39 31 (@j2 g191 8 0 3 36
  (by decide +kernel)
  (l0 8 0 3))
  (l0 8 0 3))
  (l0 9 0 3))
  (l0 9 0 1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c40 : z1 g191 7 0 116=true :=
  (@j2 g191 7 0 85 31 (@j2 g191 7 0 49 36 (@j2 g191 7 0 13 36
  (l0 7 0 2)
  (l0 8 0 3))
  (l0 8 0 3))
  (l0 8 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem d40 : z1 g191 6 0 12=true :=
  (l0 7 0 2)
theorem r32 : l4 g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 g191 0 0 0 = true)
  · exact (rfl : z1 g191 1 0 0 = true)
  · exact (rfl : z1 g191 2 0 0 = true)
  · exact (rfl : z1 g191 3 0 0 = true)
  · exact (rfl : z1 g191 4 0 0 = true)
  · exact (rfl : z1 g191 5 0 0 = true)
  · exact d40
  · exact c40
  · exact b40
  · exact z39
  · exact x34
def y28 := f0 c17 11 [(191,0),(319,2),(351,3),(367,13),(379,7),(431,78),(445,23),(487,6),(494,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem k27 : t2 true y28 := s0 (m:=191) m27
    (q5 (hints:=536879361) (by decide +kernel) (n8 (g:=g191) (i:=0) rfl rfl (n0 c17 m27) g43 r32 (by decide +kernel))) (by decide +kernel)
def x28 := f0 y28 8 [(251,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j27 : t2 true x28 := s0 (m:=251) k27
    (q5 (hints:=1358970881) (by decide +kernel) (g2 k27 (128,0,123,0,7))) (by decide +kernel)
def b17 := f0 x28 12 [(255,0),(479,24),(503,46),(507,79),(509,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem h27 : t2 true b17 := s0 (m:=255) j27
    (q5 (hints:=553656577) (by decide +kernel) (g2 j27 (64,0,191,0,11))) (by decide +kernel)
def s46 (i : Nat) : Nat:=0x1840804ff
def l46 : w0 := (1,0,6,0,0,0,0,s46)
def p46 (i : Nat) : Nat:=(d0 [3167806819908,0x28954b00129713b90,0x21c5c400a24a286e0,0x30000000000d800006,0x790000005048cec0c5,0x84c000029410000109])
def t46 (i : Nat) : Nat:=(d0 [494230678538304,0xa80c160880850c1604,0x287044044070d0e042,0x82102a03050f061043,0x70d0a085086803613,0x65e17803fe087fc30f,0xfa61ff443ff187fe10])
def m46 : w0 := (6,1,6,0,0,9,0,t46)
def q46 (i : Nat) : Nat:=(d0 [0x605ec8c000000111,0x7d3d8e632bfc434126,0xa560a0c97cd1c2e000,0x6879dce01300020298,0x32241d31f89848e708,6943248552,0x1d83401050198b41ca,0x520a2f40adbada2902,0x70002212000f024055,0x5b3c62d0c010b44640,0xb0000000000a020000,0x274e000193000140,0xac0e19590854ad6249,0xde02102d21d615614,0x2944000d8a4082dc48,0x550007f79444000141,90670475577393152,0x58000991281875380f,0x661504984eda4b2e78,0x7cc39625232a002653,0xd245061c2fea200000,0x680400000024e94b1,0x850b1ad21701010060,0xb00017050301c0500,0x70e260404451400410])
def v46 (j : Nat) : Nat:=(d0 [767,0x45022545810b0ebed2,0xa0a0caa9a4a6461701,0x18bba1216fab28127d,0x3e208a4fd302575680,0x8373fd0139d909a4f7,0x7fc6205153e0263c3e,0x95f7f520157b044d7,0x7c804c7e9c8080acf7,0x959fa41af7f15139,0xe7a243e4b049e3e725,0x49ef82c4149a9b213c,0xd771046be348414dff,0x820a1d72484df8820,0x50f8046fdd00eb5019,0xeb3818801d311052ae,0x460a7bcd01029a0290,0xf738439afc1100200,0xb730408c90182a2e28,0x830c2c20863024850e,0x8b0a261b081c11808f,0x861e128c0d84221782,0xe140a0933257c918e,0x31461a4187eaf6de1b,0xa2708d81a3b2d618bd,0x16c2b1532a053124b4,0x5a834f71d2366648b8,0x95627049c860f91c23,0x445d09f1081b43084b,0x6209c0e800eb8beb9,0xaeb83eb98e398eb9cf,0x41aeb8df389e982e39,0xce41af982fc0bf40bf,0x38de98ce98df39cf18,0xdec0beb89e389fc1af,0x98cec1ae40bfb8dbc2,0x3cb858c1a8c0d8c188,0xc1d8c0c8c098c3dcb8,0x39c0b8c1c9c1a54180,0xc316c156c104c183c2,0x3ffffefbeffbeef7bb,0xebf8c2104c1100c010])
def n46 : w0 := (47,2,6,524294,51,11,1060,v46)
def r46 (i : Nat) : Nat:=(d0 [7,0x1198115833604b01a0,0x606e88fc000242d,0x7c1fb0faad28000000,0x90720000000000000,310474596682078,0x7a03c800000002072,0xb0000f0374218000,0x83d74340000000000,0x10fe000191d800038,0xc8000000000050001a,0x19c0000000f0d80002,0x417105f0001002bc08,0xec1b0001e12c000000,0xf0e7e92d81a680100,0x81e2997c07b60460,0x2f86e047b093591c,0xb42863642440b4814,0xa40900000001016701,0xf80992cbb0308000c1,0xb416439d943b147aa,0xe00000001400000000,0x51cc437e4b4604d433,0x68120000516302b9f1,0x4067d0c804300,0x61b56b100000c580,0x783f104c0003,0xfbb80009070d07382c,0x4f54000000014a4104,0x60001715080ea87408,0x33a5880002404721a4,0x1d7010e870e0a60000,0x41e7802d68a0000000,1537694969235,0x36823a9a000d7e20d8,0x6d416e10a400828f54,0x40c813b83e60a220d8,0xfa1581020e4099e819,0x7842301210c9aa8083,0x57404e01fd304041e1,0x23c6482e6b2cf063e,0x21e71a6056370a0032,0x1825400056b139c29,0x3c35f0f8311d903113,0x2ca772115827b06218,0xa0203561cf86910f5a,0x5f4b8b233b382b58ee,0x49dec3300d7802d8c0,0x502fd10109b0c0a907,0xee0a0fc274022d3a10,0xd5060b108505d001d3,0xc31732301838cca179,0x204071480aad97c1b,0x8000509cd0a402a948,0x2901e3171c30000064,0xac78e80004854e040d,0xdec841106f32a0420d,0x715820cb2810092535,0x383b24a5005e832182,0x80109ecf40006a47e0,0x540003c1d6c17800c8,0x4f7001b077b0900001,0xc268000e088000143b,0x221e2f0000390d0004,0xc17340800211f0400,0xc3852005c082b0403,0x102880201024c3d0e,0x17000f051141010057,0x3e0400120007050001,0x6400040b010407000d,72624946333089802,0x10e07000000003720])
def b51 (j : Nat) : Nat:=(if j<1 then (d0 [0x90c4083f321d6c,0xc55f504646019c4420,0x4dfc10cf28937f0432,0x53910ce223b024009,0x80bbc34c65818045e5,0xf095406f016f31822b,0xf789912c221f5c01,0x14f24249ce0e08c5fc,0x120656c06b2083990d,0x70859f222641714118,0x12e90b633045ad9356,0x4ac98ac1927756b1df,0x4473c74045ae40c7bc,0x4213fdaa08c1dec4c9,0x7b82425ed04f3d690c,0x2f0864391ec72208d3,0x90a7d7c922807c0191,0x10fa1911e02bfb824,0xe4c43990d011c06bd,0x692267e463b811dee0,0x91ec041cc873e3c904,0x6de215e623de216f10,0x97a08640ab2623f980,0x4abea9226f20245bf6,0x30932fde02207c2399,0x86b88877f60496e23,0x9ac50c021f5491180a,0x7108bc843247a20643,0xec231f50022efe0c11,0x4fda0958225a38918c,0x18c308840c70fd088c,0x683056b01e8ec1e8c,0xc2c288d0b416286c21,0xc0109148e1a8287387,0x84a282029c20384833,0x40b05c2684e081412,0xe020441e0b05549d4,0x1d33d27d1c513d084f,0xe4f74f14e5cdecd84d,0x14ca4c34bccb4cab49,0xf497c8747fc77c70c6,0x6c60c57c51442437c2,0xfc26c1ec1440dc02bf,0x9beb3e4bddbd73cc3c,0x23b73b1ba83a139739,0x238c37fb78b73b6635,0xfb58b4ab4433833132,0x2317307af72efae7ad,0xe2d5ac72bcab6aae2a,0x129328a280a74a6ba5,0xd251a49237a29a1f21,0x1a061fb9f29e39dc1c,0xc9be1b89ac1a519918,0xf98618097996c96115,0x894e14513b92b12291,0x91109080fd8f80ef0e,0x18d48c70b88aa8a109,0x788d88187906e06905,0xc05604e04083302901,0xa80c00049718e4c0b3,0x6e11290e6d2997424c,0xb9261cf970e52b973,0x15cb95261d8532e4ab,0x97614cb9ca65cf532e,0x6a997744cc1735c271,0x330008982c5cc02266,0x41130937948c5c8c8,0x266017b0528b970cfc,0x91846550c2628b9836,0x12c82e3e58513308c2,0x711a9cabe265d58302,0xaba833c4cc325e5138,0x2e23159451dc19c266,0x176322389989d3c83c,0x2e5cc7ce6137946d3c,0x830e65c3372688b976,0xda48ace60cf232a425,0x9095ec14c266267306,0xa5900054c162a6121,0x72f0bd97886cb3afa4,0x62c1268bd9189c4b86,0xf5cc2173103d8201fb,0x9848644e7b05036915,0x9bc8acde1134322bd7,0x8445bc222c61857b27,0x1159411bc2251e61f1,0xf2d03d829e140aac61,0x88772e19f924dcc192,0x26608830280998704c,0xb8c2e6194b213c5837,0xe0c0bc2e5c62f28537,0x84553c8182661d7306,0xeb784512c83aca4477,0xf2460998808ca9a465,0x4e3f24c3a970dec13d,0x8cc513f24f0b9815f4,0xbc574c555b0f009973,0xddc194de1106b22b09,0x98943c9180e51b0729,0x1ff6febfbff77deefd,0xbff7f6fddf7bdf77eb,0xfcff7feff5fdbf77de,0xf7ddfb7f3fe7dcefdc,0x6309c6308c63061e30,0x60e3060a30606305c6,0x305c2304c630cc6109,0xce1060e10606105ce1,0x4c6101ce10e1130e0,0x530a0530605305c530,0x5c13020530e0d10cc1,0x10a0d1060d105cd104,0xc11020d109c4306183,0x604305c4301c43060,0xc10608105cc101cc10]) else (d0 [0x23fc480cb7845bfa2,0x8a1e04c73d8113708,0x5d8158ef1090e22602,0xdc5c887112c08e2238,0x88e2258134029f023b,0xd8325d2859f446065d,0x28576447019d812002,0x35c08603afc001907c,0x8877046f6022e212f4]))
def v50 : w0 := (136,3,6,1638440,86,12,1083,b51)
def y50 (i : Nat) : Nat:=(d0 [169275476,0x972c28000915083d00,0x9e0b000184b4aa0007,0xdf9a0000000103800,4434919150068,0x30452c83b410000000,0x66c401a93140358900,0x181590e60c4006e97,0x739878c268f4319a8,0xa1e8a227410f80515a,0x677800202f02991,0x5b907440e6c7f8b08b,0x68a9c416408c84be1,0xfb32f0400014320000,29,0xaa0990d58b4800e1d9,0x17e016405818117209,0x91cb65f653999ed024,0xcf0c80400004d08a6,0x610820084081054000,0x400010000a42100804])
def c51 (i : Nat) : Nat:=(d0 [0xa10200000e0858,0x408185082e10440a10,0xc840000161001e1,0x30a10000000000504,5385494032,0x108102819120810282,0x2820c8400001e102,0x83e0edf5ba3ccdeebb,0x539ac5dcadb68acd52,0x9f4a9dcda4f2289c3a,0x13047fbe9eaf070b71,0xaed266b2186be57aa9,0x3696439b8be50258f0,0x5a28118781e00dafe5,0xb845c530cefe1f944c,0x110aef69c91e1130af,0xb68f7360810cefe119,0x720530cef5c79460e3,0xcfb61f924c610adfe,0x9587e0d10cef5c7946,0xe10cdb655821cc10f,0x745c5315c1308fdea5,0x81205308efe91985c1,0x308fb689981cc10caf,0x619941c4308fbe8998,0x5cd108bf69a985c530,0xafa6829760a30cafe5,0xb845c530ccfe119520,0x530cdb655829c630cf,0xa609901cc10cebe539,0x260d10aebe8991e113,0xaf66809760c10cbbe,0x59825c6308fb68b916,0x1e308efe91989ce108,0xbfe999760430af3688,0x9760c10ceb651828c6,0x308efe91985ce108fb,0x6a582dc6308bfe9b98,0x5c4308bfe99985c630,0xc9f655869c430cebe1,0x39260530ad76949760,0xc108bf6a3965c430ac,0xf69491e11308f7ea58,0x320d10cfa609908c63,0xaf9a869760a30add6,0x967160430aeb692976,0xa30af96869760a308,0xef6a784a0530ceb651,0x821cc108dfe9597e05,0x30aebe919360a30ccf,0xe57845c130cee61190,0x1cc108fb6a3924c630])
def w50 : w0 := (53,4,6,0,0,9,0,c51)
def z50 (i : Nat) : Nat:=0x834601a000
def d51 (i : Nat) : Nat:=(d0 [0xa295fdb2e3ca307,0x852bfb65c79460e30])
def x50 : w0 := (2,5,6,0,0,3,0,d51)
def f29 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffd8fd63,0xdda8e8aa61c90014d]),(d0 [255,0xffffffffffffd8d423,0x4082801a102900145])),((d0 [2581215,0xc636db2d3474067090]),(d0 [2171096,0x2a34960818c4045090])),((d0 [4112640,0x918c681557416c0816]),(d0 [2015488,0x818829154701680800])),((d0 [105710,0x55353e34c9ba0a86e6]),(d0 [3818,0x5424062a80ba0284c6])),((d0 [3613076,0xb48c0c06e80091ef8]),(d0 [2564372,0xb40c0c04e00091a38])),((d0 [200344,0xf28487160298718700]),(d0 [199320,0xf08487160298418600])),((d0 [255,0xffffffffffffcace0a,0x51892172a62383f801]),(d0 [708098,0xd1892132a62281a800])),(0x0,0x0),((d0 [255,0xfffffffffffffc3135,0x226350618b47fd9801]),(d0 [255,0xfffffffffffff43105,0x24250c159053c1001]))]
def g29 : List z2:=q7 27 (fun x => (m1 x 0 9,([0,8,2,1,256,32,64,4,16] : List Nat).getD (m1 x 9 4) 0,m1 x 13 9,([0,48] : List Nat).getD (m1 x 22 1) 0,m1 x 23 4)) 38 (d0 [66160,0xac42b602445300668b,0xb869146814a09cb11,0x75b4024a1b8521d370,0x24203ad2284bc0a082,0x704c5131725383e160,0x40e5a0c80f2d05d7a0,0x2a2c401d414c2588a,0xc009d0174343a7c041,0x4530c648a300e5b4c3,0x138f610444e088a83,0x18c5112c029bac601c,0x859c03123f8401d390,0x233a9c031b5bc0216b,0xd8012d3f0205abe020])
def t24 : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def b34 : Nat → w0
  | 12 => l46
  | 11 => m46
  | 10 => n46
  | 9 => v50
  | 8 => w50
  | 7 => x50
  | _ => j3
def d39 : Nat → Nat → Option (Nat × Nat)
  | 12 => t1 8 37 4 10 3 3 p46
  | 11 => t1 48 123 4 13 6 3 q46
  | 10 => t1 79 299 8 15 8 3 r46
  | 9 => t1 39 99 5 13 6 3 y50
  | 8 => t1 1 5 1 8 1 3 z50
  | _ => fun _ => none
def g383 : w1 := ⟨383,12,fun j => f29[j]?.getD (0,0),g29,t24,b34,d39⟩
set_option maxHeartbeats 0 in
theorem f43 : q2 g383 (j1 b17) = true := w2 3 1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t34 : z1 g383 12 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem v34 : z1 g383 11 0 6=true :=
  (l0 9 0 1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem w34 : z1 g383 10 0 47=true :=
  (@j2 g383 10 0 19 28 (@j2 g383 10 0 6 13
  (l0 8 0 1)
  (l0 9 0 2))
  (l0 10 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem w39 : z1 g383 9 0 136=true :=
  (@j2 g383 9 0 119 17 (@j2 g383 9 0 111 8 (@j2 g383 9 0 75 36 (@j2 g383 9 0 39 36 (@j2 g383 9 0 3 36
  (by decide +kernel)
  (l0 9 0 3))
  (l0 9 0 3))
  (l0 9 0 3))
  (l0 9 0 1))
  (l0 10 0 2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem x39 : z1 g383 8 0 53=true :=
  (@j2 g383 8 0 44 9 (@j2 g383 8 0 36 8
  (l0 8 0 3)
  (l0 8 0 1))
  (l0 9 0 1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem y39 : z1 g383 7 0 2=true :=
  (by decide +kernel)
theorem q32 : l4 g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 g383 0 0 0 = true)
  · exact (rfl : z1 g383 1 0 0 = true)
  · exact (rfl : z1 g383 2 0 0 = true)
  · exact (rfl : z1 g383 3 0 0 = true)
  · exact (rfl : z1 g383 4 0 0 = true)
  · exact (rfl : z1 g383 5 0 0 = true)
  · exact (rfl : z1 g383 6 0 0 = true)
  · exact y39
  · exact x39
  · exact w39
  · exact w34
  · exact v34
  · exact t34
def y8 := f0 b17 13 [(383,0),(447,47),(495,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem g27 : t2 true y8 := s0 (m:=383) h27
    (q5 (hints:=12901687553) (by decide +kernel) (n8 (g:=g383) (i:=0) rfl rfl (n0 b17 h27) f43 q32 (by decide +kernel))) (by decide +kernel)
theorem d25 : t2 false y8 := w33 g27
def d53 (i : Nat) : Nat:=0x1a230180fd10fc20
def z52 : w0 := (2,1,2,0,0,4,0,d53)
def c53 (i : Nat) : Nat:=(d0 [73259428977057794,0x2082101c0c0071400])
def f53 (i : Nat) : Nat:=(d0 [0x613110000e3d4,0x507e48110bea9a217d,0x53082faa4885f54420])
def b53 : w0 := (5,2,2,0,0,5,0,f53)
def b31 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffffffffc47]),0xa86),((d0 [255,0xffffffffffffffffff,0xfffffffffffffff09b]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffff531])),(0x29c,0x8cc),((d0 [255,0xffffffffffffffffff,0xfffffffffffffff327]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffff303])),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def c31 : List z2 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def x40 : List (List Nat) := h29
def s36 : Nat → w0
  | 6 => z52
  | 5 => b53
  | _ => j3
def w40 : Nat → Nat → Option (Nat × Nat)
  | 6 => t1 8 11 1 11 3 4 c53
  | _ => fun _ => none
def x31 : w1 := ⟨1055,6,fun j => b31[j]?.getD (0,0),c31,x40,s36,w40⟩
set_option maxHeartbeats 0 in
theorem j36 : q2 x31 (j1 y8) = true := w2 0 1
def x31P : Nat:=0x110c0300c03
def x31N : Nat:=0x14090281205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g46 : d3 x31 6 0 2 :=
  (g1 (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h46 : d3 x31 5 0 5 :=
  (c10 (pos:=x31P) (neg:=x31N) (data:=fun _ => (d0 [16932,0x33220301121141340,0x101413401031423232])) rfl (by decide +kernel))
theorem h23 : t4 x31 6 := by
  intro k hk
  interval_cases k
  · exact p0 x31 0 0
  · exact p0 x31 1 0
  · exact p0 x31 2 0
  · exact p0 x31 3 0
  · exact p0 x31 4 0
  · exact h46
  · exact g46
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl31 : v0 false (q0 1055) 6 (vars 1055).toFinset := f13 (q:=31) (prior:=j1 y8) (n0 y8 d25) (by decide +kernel)
def m24 := f0 y8 7 [(1567,0),(2079,5),(6687,32),(7199,61),(1703,36),(4263,33),(7847,63),(12455,9),(2361,37),(6990,38),(4963,34),(9571,35)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem b38 : t2 false m24 := s0 (m:=1567) d25
    (k0 (q:=1055) [2, 1, 2, 4, 1] pl31
      (m2 (g:=x31) (i:=0) rfl rfl (n0 y8 d25) j36 h23 (by decide +kernel))) (by decide +kernel)
def m8 := f0 m24 7 [(42527,0),(44063,5),(47647,32),(52767,128),(57887,129),(42663,36),(44711,33),(47783,64),(54951,9),(68775,130),(44345,37),(60217,131),(53070,132),(60238,133),(42851,66),(44899,34),(50019,35),(53164,67),(60332,134),(69548,135)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y12 : t2 false m8 := s0 (m:=42527) b38
    (k0 (q:=1055) [2, 1, 2, 4, 1] pl31
      (m2 (g:=x31) (i:=1) rfl rfl (n0 y8 d25) j36 h23 (by decide +kernel))) (by decide +kernel)
def j50 (i : Nat) : Nat:=0x1040a3fa21fd51
def f50 : w0 := (2,1,1,0,0,3,0,j50)
def h50 (i : Nat) : Nat:=0x40000
def k50 (i : Nat) : Nat:=0x102de54110
def g50 : w0 := (1,2,1,0,0,0,0,k50)
def d27 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffffffff9b5]),0xe94),((d0 [255,0xffffffffffffffffff,0xfffffffffffffff0db]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffff10b])),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def f27 : List z2 := [(96,0,15,0,4),(1,32,78,0,4)]
def h37 : List (List Nat) := [[],[32,83]]
def l31 : Nat → w0
  | 6 => f50
  | 5 => g50
  | _ => j3
def g37 : Nat → Nat → Option (Nat × Nat)
  | 6 => t1 1 3 1 6 1 1 h50
  | _ => fun _ => none
def x111 : w1 := ⟨1135,6,fun j => d27[j]?.getD (0,0),f27,h37,l31,g37⟩
set_option maxHeartbeats 0 in
theorem d29 : q2 x111 (j1 m8) = true := w2 0 0
def l47 : Nat:=0x42108300c03
def m47 : Nat:=0x68321248a2a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s42 : d3 x111 6 0 2 :=
  (c10 (pos:=l47) (neg:=m47) (data:=fun _ => 0x2401212143203010) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t42 : d3 x111 5 0 1 :=
  (c10 (pos:=l47) (neg:=m47) (data:=fun _ => 0x24012110) rfl (by decide +kernel))
theorem c20 : t4 x111 6 := by
  intro k hk
  interval_cases k
  · exact p0 x111 0 0
  · exact p0 x111 1 0
  · exact p0 x111 2 0
  · exact p0 x111 3 0
  · exact p0 x111 4 0
  · exact t42
  · exact s42
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem n47 : v0 false (q0 1135) 6 (vars 1135).toFinset := f13 (q:=111) (prior:=j1 m8) (n0 m8 y12) (by decide +kernel)
def k21 := f0 m8 7 [(42683,41),(47806,42),(69498,43),(69557,44)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem t31 : t2 false k21 := s0 (m:=49775) y12
    (k0 (q:=1135) [2, 64, 2, 4, 1, 2] n47
      (m2 (g:=x111) (i:=0) rfl rfl (n0 m8 y12) d29 c20 (by decide +kernel))) (by decide +kernel)
def l8 := f0 k21 7 [(44155,62),(44219,136),(44731,41),(52926,42),(54974,137),(42711,72),(47838,73),(52958,138),(42739,74),(44787,139),(53054,65),(60253,75),(60282,43),(44981,44),(48071,12),(53212,76),(60408,77),(69624,140)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem t6 : t2 false l8 := s0 (m:=42607) t31
    (k0 (q:=1135) [2, 1, 2, 4, 1, 2] n47
      (m2 (g:=x111) (i:=1) rfl rfl (n0 m8 y12) d29 c20 (by decide +kernel))) (by decide +kernel)
def v52 (i : Nat) : Nat:=0x344640ac3f865fc10
def m52 : w0 := (2,1,2,0,0,4,0,v52)
def r52 (i : Nat) : Nat:=(d0 [371636974411078,0xb7171000680020c000,0xf391436008009b010])
def w52 (i : Nat) : Nat:=(d0 [18727267467392,0x4c8462023211880840,0x401f7cb4e4b74a0b44,0x658480fb48032fd4c4,0x10bf58032bf58c10bf,0x590109f59432be5803,0x29f59410bd58432bb5,0x8810af59010b758c10])
def n52 : w0 := (12,2,2,0,0,7,0,w52)
def s52 (i : Nat) : Nat:=(d0 [2,0x4f9400060ba8030352])
def x52 (i : Nat) : Nat:=(d0 [4433514884,0x210872a1e50a03e498,0x240196e52058432cea,0x62b2821b54c1610cb5,0xa98ac8086e53158810])
def p52 : w0 := (6,3,2,0,0,6,0,x52)
def t52 (i : Nat) : Nat:=0x20034000
def y52 (i : Nat) : Nat:=0x3b04813058432
def q52 : w0 := (1,4,2,0,0,0,0,y52)
def x30 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xffffffffffffff209f]),0xd8096),((d0 [255,0xffffffffffffffffff,0xfffffffffffff19c61]),(d0 [255,0xffffffffffffffffff,0xfffffffffffff03861])),(0x97be,0x2c69c),((d0 [255,0xffffffffffffffffff,0xfffffffffffff04b47]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffd3903])),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def y30 : List z2 := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def v40 : List (List Nat) := [[],[65,50]]
def p36 : Nat → w0
  | 7 => m52
  | 6 => n52
  | 5 => p52
  | 4 => q52
  | _ => j3
def t40 : Nat → Nat → Option (Nat × Nat)
  | 7 => t1 7 21 2 9 4 1 r52
  | 6 => t1 2 9 1 8 3 1 s52
  | 5 => t1 1 5 1 6 1 1 t52
  | _ => fun _ => none
def x63 : w1 := ⟨1087,7,fun j => x30[j]?.getD (0,0),y30,v40,p36,t40⟩
set_option maxHeartbeats 0 in
theorem h36 : q2 x63 (j1 l8) = true := w2 0 0
def c35 (j : Nat) : Nat:=(d0 [227971182645,0x142420351320403142,0x355431423232203411,0x211512401013243543])
def h16 (j : Nat) : Nat:=(d0 [210990543376,0x43201024300234510,0x350210243002345103,0x402102430023451023,0x51024300234010340,0x210210341352003510,0x2103413520030210])
def x63P : Nat:=0x42110c0300c03
def x63N : Nat:=0x34190a81205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem w47 : d3 x63 4 0 1 :=
  (j0 (pos:=x63P) (neg:=x63N) (kw:=c35) (panels:=h16) (data:=0x1) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem v47 : d3 x63 5 0 6 :=
  (j0 (pos:=x63P) (neg:=x63N) (kw:=c35) (panels:=h16) (data:=0x50008000607) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t47 : d3 x63 6 0 12 :=
  (j0 (pos:=x63P) (neg:=x63N) (kw:=c35) (panels:=h16) (data:=(d0 [2051,0x20482818600838580])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s47 : d3 x63 7 0 2 :=
  (j0 (pos:=x63P) (neg:=x63N) (kw:=c35) (panels:=h16) (data:=0x84) rfl (by decide +kernel))
theorem g23 : t4 x63 7 := by
  intro k hk
  interval_cases k
  · exact p0 x63 0 0
  · exact p0 x63 1 0
  · exact p0 x63 2 0
  · exact p0 x63 3 0
  · exact w47
  · exact v47
  · exact t47
  · exact s47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl63 : v0 false (q0 1087) 7 (vars 1087).toFinset := f13 (q:=63) (prior:=j1 l8) (n0 l8 t6) (by decide +kernel)
def w23 := f0 l8 8 [(2143,1),(2425,48)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem l37 : t2 false w23 := s0 (m:=6719) t6
    (k0 (q:=1087) [2, 1, 2, 4, 1, 1] pl63
      (g2 t6 (6688,0,6687,0,7))) (by decide +kernel)
def r24 := f0 w23 8 [(1087,0),(2623,5),(1119,1),(6303,39),(11423,141),(6319,25),(13487,9),(1207,10),(3255,18),(1255,69),(18749,142),(11614,49),(18782,143),(18798,80),(1395,81),(18809,48),(11708,144),(3555,71)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem g38 : t2 false r24 := s0 (m:=1087) l37
    (k0 (q:=1087) [16, 4, 2, 4, 1, 1] pl63
      (m2 (g:=x63) (i:=0) rfl rfl (n0 l8 t6) h36 g23 (by decide +kernel))) (by decide +kernel)
def z21 := f0 r24 8 [(2719,39),(13495,10),(3389,50),(8542,49)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem l32 : t2 false z21 := s0 (m:=11327) g38
    (k0 (q:=1087) [2, 1, 2, 16, 1, 1] pl63
      (m2 (g:=x63) (i:=1) rfl rfl (n0 l8 t6) h36 g23 (by decide +kernel))) (by decide +kernel)
def l24 := f0 z21 8 [(1599,0),(12463,9),(1719,10),(2365,50),(9582,145),(4979,7)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z37 : t2 false l24 := s0 (m:=1599) l32
    (k0 (q:=1087) [2, 1, 2, 4, 1, 1] pl63
      (g2 t6 (1568,0,1567,0,7))) (by decide +kernel)
def l21 := f0 l24 8 [(47679,0),(44127,1),(52831,68),(42671,25),(68783,9),(47799,10),(68791,18),(44349,50),(60366,146)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v31 : t2 false l21 := s0 (m:=47679) z37
    (k0 (q:=1087) [2, 4, 2, 4, 1, 1] pl63
      (g2 t6 (47648,0,47647,0,7))) (by decide +kernel)
def v21 := f0 l21 8 [(42559,0),(42591,1),(47791,25),(54959,9),(42679,10),(44727,18),(60270,80),(60281,48),(69497,70),(48078,12),(69603,147)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem g32 : t2 false v21 := s0 (m:=42559) v31
    (k0 (q:=1087) [2, 1, 2, 4, 1, 1] pl63
      (g2 t6 (42528,0,42527,0,7))) (by decide +kernel)
def n6 := f0 v21 8 [(44719,25),(54967,10),(60239,38),(50014,49)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem h8 : t2 false n6 := s0 (m:=52799) g32
    (k0 (q:=1087) [2, 1, 8, 4, 1, 1] pl63
      (g2 t6 (52768,0,52767,0,7))) (by decide +kernel)
def v49 (i : Nat) : Nat:=(d0 [0x8151108090c8,0x8420380cd31101fd3,0xfe887f0c3f821fc20])
def p49 : w0 := (5,1,3,0,0,7,0,v49)
def s49 (i : Nat) : Nat:=(d0 [0x74308515c76e7700,0x818435800000a7,0x1f02000000828c06fa,0x800102590967003857,0x9507803705e0482024,0x814000001004000000])
def w49 (i : Nat) : Nat:=(d0 [0x1084200042100004,0x820b764a0f19283c2,0x80fe48130bf58910bf,0x58430fe54030fe4811,0xbf58930bf594209f5,0x9420bb58830bd58430])
def q49 : w0 := (10,2,3,0,0,7,0,w49)
def t49 (i : Nat) : Nat := (d0 [481036928000,952685821954])
def x49 (i : Nat) : Nat:=(d0 [16,0x4208141ba541620c36,0x698ac4186f15058430])
def r49 : w0 := (3,3,3,0,0,5,0,x49)
def y26 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffffff1880f]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffe600d])),(0x0,0x0),((d0 [255,0xffffffffffffffffff,0xfffffffffffff2619f]),0x2a10e),((d0 [255,0xffffffffffffffffff,0xfffffffffffff60271]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffc5851])),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def z26 : List z2 := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def c37 : List (List Nat) := v24
def j31 : Nat → w0
  | 7 => p49
  | 6 => q49
  | 5 => r49
  | _ => j3
def b37 : Nat → Nat → Option (Nat × Nat)
  | 7 => t1 23 29 4 12 4 4 s49
  | 6 => t1 2 11 1 10 2 4 t49
  | _ => fun _ => none
def x189 : w1 := ⟨1213,7,fun j => y26[j]?.getD (0,0),z26,c37,j31,b37⟩
set_option maxHeartbeats 0 in
theorem k14 : q2 x189 (j1 n6) = true := w2 1 2
def j47 : Nat:=0x1408410844300c
def k47 : Nat:=0x90448d05005
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem m42 : d3 x189 7 0 5 :=
  (g1 (l0 7 0 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem n42 : d3 x189 6 0 10 :=
  (@m0 x189 6 0 3 7
  (g1 (by decide +kernel))
  (c10 (pos:=j47) (neg:=k47) (data:=fun _ => (d0 [37,0x234363203201322034,0x13214234010432405,0x431423402114234021])) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p42 : d3 x189 5 0 3 :=
  (c10 (pos:=j47) (neg:=k47) (data:=fun _ => (d0 [2368320,0x404324053241324040])) rfl (by decide +kernel))
theorem d11 : t4 x189 7 := by
  intro k hk
  interval_cases k
  · exact p0 x189 0 0
  · exact p0 x189 1 0
  · exact p0 x189 2 0
  · exact p0 x189 3 0
  · exact p0 x189 4 0
  · exact p42
  · exact n42
  · exact m42
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y27 : v0 false (q0 1213) 7 (vars 1213).toFinset := f13 (q:=189) (prior:=j1 n6) (n0 n6 h8) (by decide +kernel)
def f24 := f0 n6 8 [(2237,0),(18109,148),(2395,82),(12774,51)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem t37 : t2 false f24 := s0 (m:=2237) h8
    (k0 (q:=1213) [16, 8, 4, 1, 1, 4] y27
      (m2 (g:=x189) (i:=0) rfl rfl (n0 n6 h8) k14 d11 (by decide +kernel))) (by decide +kernel)
def k24 := f0 f24 8 [(1725,0),(17085,52)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y37 : t2 false k24 := s0 (m:=1725) t37
    (k0 (q:=1213) [16, 8, 4, 1, 1, 4] y27
      (m2 (g:=x189) (i:=1) rfl rfl (n0 n6 h8) k14 d11 (by decide +kernel))) (by decide +kernel)
def z23 := f0 k24 8 [(2749,0),(11453,14),(1371,20),(6630,6),(13798,51)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem p37 : t2 false z23 := s0 (m:=2749) y37
    (k0 (q:=1213) [32, 8, 4, 8, 1, 4] y27
      (m2 (g:=x189) (i:=2) rfl rfl (n0 n6 h8) k14 d11 (by decide +kernel))) (by decide +kernel)
def s21 := f0 z23 8 [(43197,0),(58557,52),(64189,149),(43823,2),(46427,20),(48475,15),(49638,6),(55782,150)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem d32 : t2 false s21 := s0 (m:=43197) p37
    (k0 (q:=1213) [20, 9, 4, 1, 1, 4] y27
      (m2 (g:=x189) (i:=3) rfl rfl (n0 n6 h8) k14 d11 (by decide +kernel))) (by decide +kernel)
def p9 := f0 s21 8 [(44221,0),(44733,53),(52925,14),(54973,8),(58045,52),(60207,26),(42843,20),(44379,82),(58203,3),(48102,6),(55270,51),(69606,54)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem x15 : t2 false p9 := s0 (m:=44221) d32
    (k0 (q:=1213) [16, 8, 4, 1, 1, 4] y27
      (m2 (g:=x189) (i:=4) rfl rfl (n0 n6 h8) k14 d11 (by decide +kernel))) (by decide +kernel)
def w48 (i : Nat) : Nat:=0x60bfd31
def v48 : w0 := (1,1,1,0,0,0,0,w48)
def t26 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffffffffc91]),(d0 [255,0xffffffffffffffffff,0xfffffffffffffffc01])),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),((d0 [255,0xffffffffffffffffff,0xffffffffffffffff8d]),0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def v26 : List z2 := [(88,0,163,0,4),(8,0,243,0,7)]
def x36 : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def f31 : Nat → w0
  | 7 => v48
  | _ => j3
def w36 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : w1 := ⟨1275,7,fun j => t26[j]?.getD (0,0),v26,x36,f31,w36⟩
set_option maxHeartbeats 0 in
theorem c43 : q2 x251 (j1 p9) = true := w2 0 1
def g53 : Nat:=0x14042108443003
def h53 : Nat:=0x68325248a381a0642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem l42 : d3 x251 7 0 1 :=
  (c10 (pos:=g53) (neg:=h53) (data:=fun _ => 0x50634340) rfl (by decide +kernel))
theorem n32 : t4 x251 7 := by
  intro k hk
  interval_cases k
  · exact p0 x251 0 0
  · exact p0 x251 1 0
  · exact p0 x251 2 0
  · exact p0 x251 3 0
  · exact p0 x251 4 0
  · exact p0 x251 5 0
  · exact p0 x251 6 0
  · exact l42
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y53 : v0 false (q0 1275) 7 (vars 1275).toFinset := f13 (q:=251) (prior:=j1 p9) (n0 p9 x15) (by decide +kernel)
def m9 := f0 p9 8 [(59646,151),(43479,152),(55773,22),(46581,27),(58874,153)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem n7 : t2 false m9 := s0 (m:=48891) x15
    (k0 (q:=1275) [2, 80, 16, 10, 1, 2, 32] y53
      (m2 (g:=x251) (i:=0) rfl rfl (n0 p9 x15) c43 n32 (by decide +kernel))) (by decide +kernel)
def c50 (i : Nat) : Nat:=0x1948817fd30
def y49 : w0 := (1,1,3,0,0,0,0,c50)
def b50 (i : Nat) : Nat:=0x8e80
def d50 (i : Nat) : Nat:=(d0 [616720676,0x3a037eb0261df54530])
def z49 : w0 := (2,2,3,0,0,5,0,d50)
def b27 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xffffffffffffff22a7]),(d0 [255,0xffffffffffffffffff,0xffffffffffffffa027])),((d0 [255,0xffffffffffffffffff,0xffffffffffffff4759]),0x4258),(0x942e,0x8424),((d0 [255,0xffffffffffffffffff,0xffffffffffffff99d3]),(d0 [255,0xffffffffffffffffff,0xffffffffffffff3bd3])),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def c27 : List z2 := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def f37 : List (List Nat) := [[],[16,66,101]]
def k31 : Nat → w0
  | 8 => y49
  | 7 => z49
  | _ => j3
def d37 : Nat → Nat → Option (Nat × Nat)
  | 8 => t1 1 3 1 6 1 1 b50
  | _ => fun _ => none
def x127 : w1 := ⟨1151,8,fun j => b27[j]?.getD (0,0),c27,f37,k31,d37⟩
set_option maxHeartbeats 0 in
theorem d43 : q2 x127 (j1 m9) = true := w2 1 0
def j53 : Nat:=0x10842110c0300c03
def k53 : Nat:=0xe86824914642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q42 : d3 x127 8 0 1 :=
  (g1 (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem r42 : d3 x127 7 0 2 :=
  (c10 (pos:=j53) (neg:=k53) (data:=fun _ => 0x2615312126154121) rfl (by decide +kernel))
theorem p32 : t4 x127 8 := by
  intro k hk
  interval_cases k
  · exact p0 x127 0 0
  · exact p0 x127 1 0
  · exact p0 x127 2 0
  · exact p0 x127 3 0
  · exact p0 x127 4 0
  · exact p0 x127 5 0
  · exact p0 x127 6 0
  · exact r42
  · exact q42
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem m23 : v0 false (q0 1151) 8 (vars 1151).toFinset := f13 (q:=127) (prior:=j1 m9) (n0 m9 n7) (by decide +kernel)
def g24 := f0 m9 9 [(2429,28),(7038,16),(9598,21)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v37 : t2 false g24 := s0 (m:=2175) n7
    (k0 (q:=1151) [2, 1, 2, 4, 1, 1, 2] m23
      (g2 n7 (2080,0,2143,0,8))) (by decide +kernel)
def q24 := f0 g24 9 [(18814,16),(11742,83)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f38 : t2 false q24 := s0 (m:=1151) v37
    (k0 (q:=1151) [16, 4, 2, 4, 1, 1, 2] m23
      (g2 n7 (1056,0,1119,0,8))) (by decide +kernel)
def j21 := f0 q24 9 [(44925,28),(50046,16)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s31 : t2 false j21 := s0 (m:=52863) f38
    (k0 (q:=1151) [2, 1, 8, 4, 1, 1, 2] m23
      (g2 n7 (52768,0,52831,0,8))) (by decide +kernel)
def p21 := f0 j21 9 [(44159,0),(47743,1),(69501,84),(74110,21),(48094,83)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z31 : t2 false p21 := s0 (m:=44159) s31
    (k0 (q:=1151) [16, 1, 2, 4, 1, 1, 2] m23
      (g2 n7 (44064,0,44127,0,8))) (by decide +kernel)
def r21 := f0 p21 9 [(43647,0),(46455,81),(51063,154),(43901,28),(46461,84),(48510,16),(51070,21),(43423,155),(58811,156),(59900,157)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem c32 : t2 false r21 := s0 (m:=43647) z31
    (k0 (q:=1151) [10, 1, 2, 5, 1, 1, 2] m23
      (m2 (g:=x127) (i:=0) rfl rfl (n0 m9 n7) d43 p32 (by decide +kernel))) (by decide +kernel)
def q4 := f0 r21 9 [(42623,0),(60285,28),(60286,16)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem m5 : t2 false q4 := s0 (m:=42623) c32
    (k0 (q:=1151) [2, 1, 2, 4, 1, 1, 2] m23
      (g2 n7 (42528,0,42591,0,8))) (by decide +kernel)
def q45 (i : Nat) : Nat:=(d0 [0x28270019312920,0xf8e91910020841c006,0x2403e3031e1d18e0d,0x8d0c8c0b8b0a888028,0x504c483c3844400101,0xe1c1a180e0060b0a09,0x80700303028201810,0x801fbb98bdd7a82ec,0x539c87a00ff503fd43,0xff54ffd10ff083fc40,0xff0c3fc53ff18ffc31])
def n45 : w0 := (10,1,7,0,0,9,0,q45)
def p45 (i : Nat) : Nat:=(d0 [10,0x49b3289cfee0003c11,0xe62e10c1e400023500,0x513996000090c91cf,0xa000013a78dac3f26,0xc00039c5cb80000000,0x204a000000452c00,0x1633e0e551fc80b152,0xf0f95a89a255e23881,0xa8be81b938018248c6,0x65c070000000000b3b,0xc9a800000031700028,0xc3072b06ecfafc9837,0x5010470c01e16716e0,0x74d6b0bf948ee3ac96,0x36e0054814054a5,0xd5892c4d40b354401d,0x8907a8d08616748686,0x6b2610135be1dd1165,0x170cee09f0f01bcb5,0x800000010d202243f3,0x18eef1419c646e0a9a,0x79430db52928c52c,0x5193c564cb39a69000,0x28ec00122803750628,0x65214c24898f806a2a,0x5df5d43e1d42ba11a4,0xfe586827629805dd99,0x2be81c8003761a6d0e,0xc800000000072b8000,0xc8986beae000000185,0x81727cae660c120006,0x8bc0011c561f014800,0xb8c0000001cb4c5e7,0x11000138985d121316,0xf8741ed00000000000,0x907402000000,0x4d29b7e000c0d67181,0x8d8a3e1049165c75b6,0x93b0000000c7511c31,0x3d41fc131606bb107a,0xd0436070133001020,0x700000300000004610,0x6da15030000002,0x500000000021061070,0x3013010000000a0,0x20130090060020020,0x100100240030000015,72075186761310209,0x10001104000000010,0x400000000001011])
def j49 (j : Nat) : Nat:=(if j<1 then (d0 [0x4670b12533d10c,0x75e8c8b58478714c78,0x518d7ffe317a00012a,0x9ac91478d191b210c3,0x2553e54c93f8948122,0x4ccae8c8db6fde2547,0x91fe4e848fbc887bfd,0x7bf91489036fde2547,0xdcf8012e849566e24b,0x9fb14c8811a0e059e3,0x52b5153447cbd4232d,0x7f49221033d2726414,0x7a231b409789c248c,0x37effc18880013340f,0x91678851c118ebe79,0xab9993d531d8dc499a,0x5bd0c116be4b20866,0xcfc8181973f508195b,0xdbb50994f7c60a504f,0xc8428b9e9121c0ac4,0xfc46a1120e04a60f44,0x53fb885004944e5f86,0x55bc6ff42c412779,0x9d428024a1e7ce7ac1,0x704adc7e20451ffc42,0x44651f5f0228486f4f,0xa1954c1e8977ea4a0,0x53be12443c9c3c6580,0x589afe03afe94c9448,0x9efffa830090fdb8d0,0x417f449000ce5f928a,0x32dffc2d0614d27f80,0x7b0a67cf1f4d91f647,0xd4208fbfe370010109,0x6bf0781268499f1f02,0x903ffe01040482f,0xca44652ffe289a4fc1,0x22aff8d4941804bdf2,0x3604101297c7e21401,0x24af7ee811a7f86101,0x1d78f7002c80953e38,0x1127d8e0211e7f2991,0x42fbf18650920df8cb,0x8019cf270f30e05479,0x38798702a5ebf90311,0x20250f9f5818890128,0xf270f30e05400fe351,0xd6404a258208d1b924,0x507a3c1d8e86f1d841,0x349848218d86b12821,0x2494478f110820c0a8,0xe62006815047c23094,0x8a42161f9088a0318c,0x9c0a1707c9404221c0,0xc881288b0503b15130,0xa240108fc04381b1a0,0x844030838cc0801088,0xb84e07148944900150,0xb4582b1787c010b284,0x6416a08101e7fcbfa1,0xf92fab7c5bddde64f0,0xb778bb55d82e9e73db,0x929c58e0c6f43739b5,0xad886b9b591a7ed1d6,0x8533b5996cb263d319,0x988cc2b606af8d78ab,0xa05bcad9566ab10570,0xab25534a8d52fa8ed4,0x1e9ef4eba72935296e,0x4a92505254906477a3,0x591928ae444219908c,0x8224009f80f6c78e3c,0x9da0e727113711ad0,0xd0066031e1840bdc5d,0x52d89660ad254f2941,0x3e49b64b1247919c87,0xc4161f88ef47203651,0x9c0c605f42df15609f,0x849e22e105076437c1,0x9a0bf054424c0f9066,0x25c0c403500052411,0x4a83d264f4b885240f,0x4b93d2a234983d2a4f,0x4bb3d2e6f4b24d2813,0x498352c034b1852c6d,0x4902d242d4b9352409,0x4884d284d4aa3d2633,0x4a0bd2a614b0bd2c13,0x498852eaf490352c73,0x4b1bd2a274b13d0e4f,0x4b01d24134a13d2403,0x499352e334b09d2407,0x498b522014a8c52e2f,0x4b08d2c114a84d2613,0x4ba4d2e8d4aa352833,0x4b9b52e61498052c05,0x4384d0e4d4a0352a43,0x4a9152a474b84d282d,0x4a8bd2c0f498bd2401,0x4a002ae4cab8c32846,0xeb1caae10ab883282e,0xab84aae22a393ca40c,0xabb0c282cab91aae4a,0xa3932ae0aab8caae2a,0xab982aea4abb128e13,0x2983aaea6ab913a610,0xab8a3a612aba32ae6c,0xabb1aae26abac2ae4e,0xab822ae42caa3aaea2,0xababaae048b8a1ae46,0x2ba9a2e260bb192e66,0xbb0ffffdfdfbfbeff,0x7dbdddebf3f54d4350,0x11018c53100310c020]) else (d0 [744459458756178,0x268663fe3f325000b1,0x3ca8643f53090a16b2,0xb1c08e6b231fc5008b,0x7c382938e31a32317b,0x310ffc6068f4091041,0x3efe1f6c01485ee44d,0x9b654c87a249bf13a0,0x91bbf9e4f32ae0e4e3,0xd3a92ab09fe26af3c9,0xe651e04e8247ae7089,0xa62f4408edf4ca4466,0x3e5120b04991818324]))
def x48 : w0 := (122,2,7,720906,68,13,1115,j49)
def d49 (i : Nat) : Nat:=(if i<1 then (d0 [0x8d2114ec42d555,0x274bd2a00000161bc6,0x98a2be56e421c83e4e,0xb400028745174e28a0,677789873,0x403000000000000000,0x29000001258a89ff00,0x992fe0002b3da039c6,0x1254b5a7f81c0000a,0x2dd89140da00006de2,0xa4c59326092843a174,0x50c9f98641eb8a6b0f,0x32194d57899800010,0xe20001c2208b800000,0x2805000000000000,0x585b4e2b828d9a9,0xb073f668000000008c,0xd0000ca8dc8ad2baca,0x4800000006ec300006,0xefc281810153c0000,0x217ef0d083fe87f,1794088372097,0xec09a000246b324e00,0xa18c000390100014,0x15c9baeb4c41fa9478,75091250574426123,0x516940168a70089713,0xc725c00019a69eb0a0,0xe0430e88f585868e06,0x60223a8000a20e09dc,0x8435154e1a3a209844,0x215f52428c1cc67013,0x432ca00034b5802270,0xffe195659f02531b06,0x4907608000e55761ca,0x5e994bc50c000024e,0x80003a02817f18688f,0x76221a3d7d8af0df90,0xeba87909b1876f302c,0x105aa7800000000000,0x60c0e190431ed5c,0x5ec7000063d08b7742,0x86a09c1800006874a1,0xac3148761ac934514,0x90187128de904f0308,0x4bb0000a1760000000,0x300806afc2d7193f6f,0xb0001841047b129960,0x5400e8ea3fab29decc,0x4b4cb3f14996518be8,0x37c8c662106570000,0x523a41e200014bda0c,0xb8046d9e082a6aa400,0x259c4890f3613a2,0x27b440214710bd222c,0xc55f95a52ee000384b,0x99090001f43ac0db05,0xdc2c380b606a4018e2,0xc7c29000020e0b2c1c,0x36d592581d405720e2,0x70800051e58148179,0xe57ec06e29fd94ff15,0x96e576499887e93d52,0x40000000000000000,0x795500018280,0x403f0001612c000,0xd1780598000000,0x115f98a2c6b800031,0x1dd8c356120d5b0c30,0x3bf0199866f08fe41a,0x48e86705255e23385c,0x8000b199fa7000050b,0xf517da340801104c12,0xde04508900000b134e,0x67c961c1421cdc609,0x488c1179277c579c8b,0x767531636558089d34,0x7628365a2ca9e67f39,0xdc94eff59cd5e90d48,0x1580b63f30a091557c,0x1e97ce0ab2092d9b,0x9923c13184648424ae,0x92a2000251800e365,0xb6ec4f892fb1b00c5d,0xc12c482812e2f0e3ac,0xdd56a4e1cbc,0xe14af06045e8559b82,0x2a28aa3599f78a280,0x94d6254a491b0a46e,0x5c4126684e456a0000,0xc079b020000034f4b9,0x50b30000428604a800,5105464176577024,331488,0x255e0000d1f60003,0x4aeaabb506cd2c0000,0x502a8681003000e00,0x140330401a0204c8b1,0xa00001810408004561,0x400304416020230110,0x24280ba0254000865c,0x1840010380140418f1,0xc0150e04008001d0,0x71a10080281008102,0x181030000081320400,0x4060008e000c00e000,0xc78710080080004291,0x40029d2a44b060000,0x6020a0048206000030,0x2c0042e002800c180,0x8804104021e0c18108,0x40800004400060008,0x818243810040104020,0x81091e001882208203]) else (d0 [6986,0x50500001d9fb975a15,0xd240d09f665ca19400,0x10148000d11204700,0x302ea103812ad928,0x41b8000000718e4,0x169580000000ec7,0xa54fe07d532f9ea600,441991382612288,0x5ceede82b68ac1,0x14331d200000002c30,0x9023e0d6a8e255930f,0x60000c3e4692000000,845286578585624,0xb2000032dae49dca32,0x8dd0000a33c802b87e,2207689202831,0x5b1242c8cbf3068ec,0xc87758a5e2ae00033,0xb16092dd50a395c365,0x6b110702c1017c118,0xae2964af86cfc21792,0x48c7f843873f929c84,0x3749a8d53e0a64b791,0x7a78aa300f619f11a0,0xa6c8001a2da47e4e38,0xc952035c3c914c125,0xe79dcb032d7fa52532,0xf204a38c452e64523c,0x2d6831f0269d1e3b60,0x46b502a1432594f,0x8042e11bfb57140000,0xa50987ce83cb1f000,0x31980004d6a00010,0x94d53200010bf80001,0x6ed000074c40006015,2316732203008,0xa15c1ea832e2e163,0x9ec13384f000000004,0x985c7752fb3484c946,0x32b82150298cb54f67,8661277,0xa000200d009f000000,0x10a20000000144eac,0x4c90ba0127cce6836c,0xb09b02f9c9c5737045,0x411fc4dc83c5131302,0x9e144400d939d939a2,0x6f84e6069a63962ca0,0x54f61f393ca2d000fd]))
def k49 (j : Nat) : Nat:=(if j<1 then (d0 [0x6525d9a24904d8,0x9415292e2f4660a546,0xa02949804e92e60125,0x80e3841401982aa92a,0x4d525c84a4901d4960,0x28e285512442340a12,0x9793064f2c6e9261e3,0xaea93e49204ef2a521,0x754a9a4b94249760e9,0x2407125d43a4bb2b51,0x60ad12a2b066119c4a,0x8b94954511aa4e1c50,0x8d249035714182e282,0xf524812a4b9398d206,0x8910f412482ca4b09d,0x49727c92a44de58dc4,0x4409749204d1ac0e12,0x5825c4b0d4714236e2,0xa8d866008a4c28e793,0x17092e42925d820cc2,0xb55d52a91ac2e1e4c2,0xa24ba8349730292e8c,0xd25d4224a8b6496366,0x330539261d244a8ad8,0xd845292e6cd248118c,0xc2b4198224a2c03125,0xca7c6900b49406692e,0x4f622063a4b9544982,0x44330ce125465bc982,0xc4971871a60a52614a,0x24a0598d2071110341,0xe4c27a4b0351983511,0x102dc6619a3cb1d449,0x76583306a525c8424b,0x88279537092407dc55,0x1724b0cb19855e92e4,0x2dc502a46c1a98d203,0x4f2615d2614e82c122,0x487860b0e18161e18,0x2c33629523e090efd5,0x551e8243be05821e0b,0x6a0e5cc30243d7595,0x2a27ac274e480f36aa,0x380580b20b0ec98212,0x890b09039730a23075,0x4e20e282c14d058366,0x82c270d50a6b4a0c20,0x581408a4094160a314,0xa94d05870a43024085,0x85002c22821602c0b0,0xad8e4c260ac0b10580,0x2ceaa6e1048119ec01,0xd05823e53047ca5487,0x8243b94572707b0a74,0x858081c985904879e7,0xac0741604f9ca89e3d,0x72328ae6a5b505c02c,0x3ba40818a52c27ce54,0x8f02c14e21524042c0,0x801605b20a0a861429,0x52a538121e81aa120,0x5849c130d38121d91,0xaa11c4d63aaaaa5001,0x6013bea12935423eea,0xc6e1654ab34a0ae215,0x14082a2d0a480fba98,0x504171307ae429a505,0xc9cb1d805859882c07,0x1606702c3835954ac,0x52a23c848081cb09e0,0x5818c6ae500e580f20,0xb8830487a6824070e4,0xc268243ad41863882a,0x471358ebb4a12f5554,0xa70a82a41604810c0a,0x5822a0b0ef0d5c9d,0xb2a117418538090ec0,0x854483a90480487845,0x2a27c360600243b121,0x204042a441d4c5c20b,0x88929813e72e60ca58,0xf9ea89d29522a8a40,0x881604796a11e1d424,0x30d389508f98a11c,0xffbfdff3fbfebf7fdb,0xeffbbedfafe7f7fd7f,0x3fbfedf7fdfb7ddef7,0x7dbf6dd9f5fd3f3fcb,0xeffbf6f7bbebf9fe3f,0x5c5535c1535915358d,0x535815350553501534,0xc5534c153481534415,0x31c1535d5435c5435c,0x14358143545434c143,0x481435d5405c94058d,0x405894058540581405,0x514054940545405414,0x50940505404c9404c,0x5404c140481401c940,0x5d1105cd105c91058d,0x105511050910505105,0x1104c9104c5104c11,0x48510481101c9105c,0x8635c4635c06348063,0x5c4535c053480535d8,0x405d4405cc405c8405,0xc44058440580405484,0x54440480405d8315d,0x4315c8315c03158031,0x548315d8305d4305c8,0x305c43058430580305,0x483054430480305cc2,0x58c2054c20500204c,0x4204c0204802044020]) else (if j<2 then (d0 [0x91681d011002a0,0xfd070f4380c4270111,0xf8940107c110cc0787,0xd000a6000b8000b02b,0xbc2deb07517a69d25,0xe8cf4179efcdae64f2,0xcf94fc90e4271bb8b3,0xc3fe1870a3833c0bdf,0xe6fc77c5bd4ddceeb7,0x743b8ddc2ede76c1b4,0xbd966c7761faf6d6ce,0xb0f569a9fd4aea174f,0x7a6ad2de93b47ba2fd,0x10e8273fb9e3ce566b,0x3333987cbc65b32bb9,0x4cc9c64b72258fac6f,0xe34f1898b1c4f625b1,0x1868c27e10b06d81f,0xc065fdefc77d5be45e,0xcaf3178dbbcddaeebb,0x73eb925c2edf36ecb7,0xdb42d836b3b53da62,0xcff673b2ed93ac8962,0xfb0ad80ebe75dbae75,0x6d2b41595abed5d6ad,0xb553a9dd482a0b4eea,0x6552be94f491a3cd19,0xa883430a12503e8013,0xf39f44f627953ac9ca,0xce1a6f135a99fccce6,0x3b30d97a4b9a5a52c2,0x9554a7650f27d934c9,0x7a49923a912c862405,0x1e38e3c6ba34518e8c,0x2c5b22b514289d4482,0x20b0f486b43261830a,0xe84b421e0e506282b4,0x10e06701d807400dff,0x6fee7f03f55f8efb77,0xd5be7df2af827b83d8,0x9e9af367943c55e14e,0xfc7773b51d8ceb9751,0x3a4dcfce7272f3941c,0x8ae39711b855c12df2,0x6f5377dba2dc56dd36,0x89b18d776b5b579aa4,0xd4769a34a1a2cd0a67,0x933999a4cb6655b271,0x90ec6c62f312186cc1,0x86052ffd7cebd25e12,0xec5740b8d5b62d3566,0xab28586ac0d5e8ae45,0x6a2af5556a9a53ca98,0xd480a26503a7cd3cc9,0xda4e026c534c98c4bf,0x25b92b894749ea4892,0x68ee46a231d1688a7,0x44821d90cc85341c20,0x910207f43ef1f1cf5e,0x79b3bd1d80e8c73839,0x1c34df46db3659ad0,0xd3869033f19acc9463,0x7311981cbe85d42dc1,0x6b8b445922be1574aa,0x654229a9450a024ee2,0x6992dc94e494242117,0xc87c42e2098fe07c43,0xcf1d20e507043611a3,0x8ce864e31c1830bb05,0xa42bd1508a0c4e425e,0x12788fc45621210107,0x9c3a21b20d206342f8,0x1680aa84d424a10b07,0x9839016c08e03080cc,0x33031d25c9fc4b0,0xbb71429292e21a3481,0x924c3a1198262a2c11,0x1261e824b88549208c,0x92ead525c6ba4904c7,0x1425e92403d2618e38,0xa1188d20aa93049634,0x81aa490228d2062f26,0x142254578cc3361980,0x86910518660670cc32,0xc71422ef2415925c8c,0xcc10c492096f24121,0x248104440a45161831,0xa413d2486324bb038d,0x4253110284660d9a4b,0x881498366330269c54,0x9dc4a8d249765a92e2,0x2925cd48cc22971418,0x712a2ac6605224b09f,0x493066baa501e4c24a,0x4b94171423292c0746,0x6050a4b013893154e2,0x84c62204438a0c4495,0x29692e4dd25d5a0cc2,0xb689525ee240edc551,0xca4bb2e1980191a412,0x9754a4a4ba8289515d,0x1a41046608da4b88b4,0x920b092e22125ca224,0xa9b35d529f12a20e25,0x59bc9932198074930,0xc4de4c5d46a8b84970,0x9e3305246601946902,0xd49765e92e4312548a,0x28b09a796090330125,0x25cd50cc2ba89516a9,0x2e46521ca324c30d49,0x202092c13125d81389,0x4081207e330311254,0x9a44408189516892e2]) else (d0 [0x340a25a5322c508,0xf112816314116c3de5,0x4064dca108c686c049,0xec18d808de0829e121,0xcf18c88708802c913c,0x53686908722a6065d,0x5041b011814e221803,0x127c898cde1045fae,0x190e111e05df2863e,0xf912326700c7468777,0x88680cc210053a42a3,0x435615f2106c359147,0xa03199093c85065f40,0x630ff70992f091d6cc,0x53108c84e116c50b54,0x50d0144be0640f4a63,0xc9700c86421c8b2da1,0xd9923005f190e3e018,0xddc2106b41602dfc08,0x67848d7a886ba88759,0x1588b5e282f71020d8,0xad4a19e0559147cba,0x6417d1a0f6f8489bc,0x215585808f90aad09a,0x45a83b90a7f0488c04,0x6f0415a234057a887d,0xfd531a78c4bc06dec8,0xc6e021b3e9127810e9,0x87b431800047f00c7,0xde40c60f0020f47e82,0x20fd0436fdb422651f,0x810880159731d7a031,0xd65625ffab00233cc0,0xd8084f486748b68240,0x9780cb036fe60190bc,0x319c22c6073a78064,0x8790506c05730922f2,0x153c2a0cb619e04319,0x42af60636810f58860,0x12d7219028958b7842,0x1d6a1d5867f443cfe0,0xc8bfd44885f4a633,0x2cf06200c7ca18cf2,0x238fe26300e70020d7,0xd79221ec0f3a780645,0x81005af232f2863a70,0x3ba14336236020e0c4,0xc7433e221eb8140400,0xd02388980dc4506846,0x4c040147262de108b,0x61677416403630d86e,0xb91d21ac8ab222fc89,0x8de02581278463a343,0x3d243d41da143b88a9,0x981133c492c0a8147,0x286300a43ec0a81521,0xcf6663e2e18d7c486a,0x5b415026026708d80,0xbb262602ef80636021,0x3a43af362642048e06,0xe1848ef10a0ee22a4c,0x495ba625fd08115503,0x40590e2c735843be22,0x3b11e6989f6022fe81,0x118edf1613b79231b,0xefcc312a023810f8,0x88f88a78e219c84766,0x235fd020232f848796,0xc3d05967c0844edb49,0x8cb6e848c034039f02,0x1107021024fc218de0,0x29a42be08e62a86016,0xd509453b7c584f3584,0x3ce68191c057109120,0x798c18cbf80639a424,0xecc590e8190cb090cb,0x923c10193b3263ce4,0x8c75e24c72c904bfa0,0x4046ce68192fc40267,0x8083e018ee2121fa23,0xfe404c97845b65511,0xbc218cc0b78424ecc4,0x9dbe08655bc09b5086,0x3c8508bd0d8b035c91,0x977fa0910023023e03,0xada98cedf16138047e,0x370147d309195f602,0x1f023c8740c85fa44c,0x97c44fb010b8133ca8,0x100ccbfa0404698428,0xf448c990e81917c243,0x4ecc45fb1482819e69,0xad5245fd020236734,0xc96223e446808af92,0x49f021127c08449ac2,0x1d72923227ca48c8bc,0x4232c24ac467c0679c,0x46be80443e039f5a08,0x9b2b221f790c26780b,0x3a1319b810cb092f91,0x187e1d0321f01b7ec0,0xc7b59288708829e5ff,0x3e22a9c6fd08248df7,0xfcca0824053cbfe7c4,0x54be30c6f1a092a210,0x88340e91013c280584,0x1913414844b4961d80,0x42140842076168d112,0x8a0020412308300422,0x41c581bc54308404e0,0x71228552789d4186d1,0x54a02409604480450c])))
def y48 : w0 := (387,3,7,2359386,103,13,1105,k49)
def f49 (i : Nat) : Nat:=(d0 [0x4048000b050c19000,0x427c0b6c0ae0f8000,73446353935101989,0x4c0002c1800020759,0x179d2161bfc05f1f9c,0x566d19c76b1d2c3080,0xd1a07c04df1a000000,0x3098000c08207790b,0xc000d109d3bd0a6807,0x18000312ec6ee1e6,0x3900c583a64be4353,0x18e5361509868521b4,0x80d14000061f544fe9,0xa2085606fc21202242,0x2905f08741ac000000,0x3c0b40dd01e10ec840,0x11cbc52b0e0f51a123,0x465808c85a1c044466,0xf4c1561b5c0ce4440,0x812a82800f105b00,0x286710ca054a1b085,0x800014600000000307,0xc483404304d4074c33,0xc1ff0841038,0x484ec36f1c287a8,0x1ef449f20986a315ec,0x62200000070b948101,0xa6f5f2222844000041,0xc0000000500a40d000,0x2025706b864214c000,0x2043000145c203f,0x51d0003c61000342b2,0x11600150a800000000,0x11e000081cc00059,0xff03f0001b45b17c01,0x611c5424e00c00014d,0xc05d0000b5a6c44441,0x44b2c2c0147c7cb044,0x7013866515700a4,0x4048b3520eb08aa56,0x95d0a7551014001041,0x10500d38b50100a080])
def l49 (j : Nat) : Nat:=(if j<1 then (d0 [0xcf10e13bf579ae,0xc5c2b756a2cd588b01,0x5e2b6560ab1536a0d3,0x9a634a690d19a21422,0x804f49c9362684c397,0x72ce52c8d8f91d2364,0x5c8a911e1d42e84d06,0x608c057f4fc9f53da7,0xa4f1ddfbb775ee8dca,0xb8d6f6dadb1b4f684c,0xdd9331961ac05792e6,0x5acb0d5baaf538a293,0xf2744d09812aa46476,0x8bd13a0d40a7d4ef1c,0xf38e6fcd91a933863c,0xc39772de570aa14226,0x84908e10b1f43c86f8,0xd71922d85309b12421,0x83e8710d0170268420,0x660940d00f00013309,0x42649c6ca0b0c54187,0x4ac3246645536a9478,0x5422c1330a026430ea,0x90069c914e9a40da95,0x64209034752033292,0x241b508ce49842a963,0x7a7930252481b8cc8a,0x5119128790335f5089,0x6c899c930be52a544,0xf206b8ccc250991c3b,0xa413cf245206c91ad9,0x417cfa844e250869e4,0xa6d94158510f54e21,0xec0ccba19d60121131,0x8dc244b7098566d423,0x52a54195806b2b08b,0x85421213235e250829,0xe48a91995011284334,0x50821443dd6d4238c9,0x2274264a284c9533c9,0x84a1324d21480f4e48,0xa38d510312e219f508,0x8c4a0b128878cb2847,0x5b508dbea114516132,0x7ae22275457b6ba871,0x5911d324039c545ccc,0x903919921b12c31365,0x5704c95c6d422e2b2,0x43cf545598a11b7d73,0xfaa40d46644588c91,0x5454195192245b508b,0x70984189710e2b303d,0x9244164a0bfe52066b,0xac251858471e40a230,0x876ab2847cf206cc89,0x857b154787b0eea250,0x8518aa408942123930,0xb784c26489014b952a,0x942c983348192aa11d,0xbd209c01300c126129,0xa952b520b60130809,0x21f134a116348396f2,0x84470505d9643daad3,0xbd028427fc7f4fe5f,0xb3f57e9fd1f9bf2fe4,0xfc5f6be97cef8dedbd,0x6f87ef9debbcf76eeb,0xdb7b5f69ecfd8faf75,0xde9fd2f9ef3be6fcbf,0x95f1fdf9beb76e7ecf,0xb9df3ae6fccf97f1be,0x1fbf95f6bdd77abf1f,0xe3ec3f4817154d6359,0x15321d6454d5458d53,0x5014154d5450153549,0x4054c8750153549305,0x4c844c15361d2054d3,0x4815321d2054c8148,0x1535491054d2044153,0x21d1054d861c153610,0x7054d811c153549305,0xd424c14361d2050c8,0x148143205725018158,0xd40505625016158140,0x5c954501525454021d,0x5150172505404c5325,0x1544c540545315008,0x74c54058d30501614c,0x14058130501524c140,0x4c5305008148140549,0x734408758d10609544,0x418155110509544408,0x755110549414414250,0x5105d9404418448110,0x5cd204414248110505,0x20441404811060c724,0x41541c9106017218d2,0x5c4634817018d8748,0x634817114d825c053,0x4817014d8748053205,0x2014d525d840545761,0x1425d840481761018,0x25d44060575101615d,0x44058175101525d440,0x54575101205d440585,0x73101605cc40549731,0x1515cc40481731018,0x5c84058572101605c,0x84061971101855c440,0x58171101525c440481,0x711018258440509611,0x142580405c5511008,0x148040549760c1205d,0x8305cd31081714c420]) else (d0 [2782270,0x6105ac2095c0d7b8c6,0xc040101078c50c0aaf,0x41113c18a9815e610c,0x3b2626c097a420000,0xb21321002046420000,1099516879842,0x2502001a0800026c21,0x860c6f60300003e220,0x701380b5040168201,0x6424080000f8880180,0x8000004a0c3020152b,0x14d210007831458481,0x2e909c056432837488,0xc866108be314a08007,0x3625f90ac8501b2100,0x205748980990802c7a,0x4880134853f090ee91,0x548802e0270100,0x4e210003762005e909,0x3613e2200dd2168d08,0x34c218058442710ce,0xc0e90804c8402c0401,0x6023244c04c9126074,0x8690992206610100a2,0x784ed04271200030d0,0x19507a0004620e00c8,0x30008f90124ec020b0,0x4a828120fd1662d45,0x48002c43e0b8000290,0x5e0ad0002dd73ac74e,0x689ced99f28e46c7d8]))
def z48 : w0 := (137,4,7,3801188,103,11,1064,l49)
def g49 (i : Nat) : Nat:=(d0 [0x247800a1c000850,0xa0de22d610c00000,0x272000f1bc2ec1b907,0x25c1d40191e0508b44,0xd01001a1400000c080,1115951632])
def m49 (i : Nat) : Nat:=(d0 [48413249110244,0x10815871042002c080,0x3504205c102f02,0xd800181687ab67230e,0xfab6722e19d5c1ad99,0x85712ce84403d49524,0xc087481538fc2a5206,0x5544430dd63640875,0x9153de850898505204,0x43f40a1481524c153f,0x6848171509601039a9,0x2021d4255110f4a481,0x4258175103d2542245,0x205d4409dc69498505,0x20443d8542245205cc,0x40fe0509302052050f,0x9a542261205c440f29,0x50891481761039d130,0x2048748153f6250920,0x58173103d615148152,0x5cd10b0729d6455163,0x54e07ca9549861c153])
def b49 : w0 := (19,5,7,0,0,8,0,m49)
def h49 (i : Nat) : Nat:=0x81900
def n49 (i : Nat) : Nat:=(d0 [163,0x390a134a4c28290221,0xe50549302048748153])
def c49 : w0 := (2,6,7,0,0,3,0,n49)
def w26 : Array (Bits × Bits):=#[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),((d0 [255,0xffffffffffffffffff,0xffffffff4ca8886101]),(d0 [255,0xffffffffffffffffff,0xffffffff8c0d9a00c9])),(0xdc001a04a,0x12b065ab12),((d0 [255,0xffffffffffffffffff,0xffffffff815101844f]),(d0 [255,0xffffffffffffffffff,0xffffffffe94a0254e5])),(0x2200761284,0xca4842b0f4),(0x0,0x0),((d0 [255,0xffffffffffffffffff,0xffffffff2220844287]),0x31b2254f02),(0x0,0x0)]
def x26 : List z2:=q7 39 (fun x => (m1 x 0 17,([0,16,32,128,8] : List Nat).getD (m1 x 17 3) 0,m1 x 20 17,0,([7,8,4] : List Nat).getD (m1 x 37 2) 0)) 80 (d0 [8389472,0x14900074002890c4f,0x80c10204b700408800,0x4e001302baec2b8105,0xd0f85d50218af01810,0x4087e009000429c040,0x62000b8005420cb700,0xc084695e068203387c,0x33a81054f805104003,0x9000861ad7c1ac02b3,0xaf43380a00528000d2,0x2c9f02c202194e2183,0xc29c0c0600f5380f,0xc40087000385f57a1,0xf404c32dc430211a5b,0x81a040acbb0ac04801,0x620001d00298000645,0xd5f05d008a6bb0a604,0x80147000290006d800,0x92000f20040c00ac00,0x138014c40012002ec,81070153413012171,0xd0ac021583e1594035,0xa9c358605d5385d0c0,0xaea70ae185c57a1c40,0x43887c38a81725e872,0x10a61f0a6a014d4e1,0x4c300187c01a800353,0x8030c30caf10c105ad,0x5e1ac20aeabc2e8415,0x757857082a6af0a610,0x4615e0602082af4028,0x9051f805402d6b70d,0x60855d6e15c10822f4,0x2008005f000008081,0xf008a05756e17410a9,0xadc29821035b803042,0x42bd042025747e1750,0xa98fc29a01031f803,0x40246bd046020003e0,0x140b5af435809575e,0x857012a8bd0a80240d,0x7a00c040687c06a810,0x5e80001000a700018])
def z36 : List (List Nat) := z17
def h31 : Nat → w0
  | 10 => n45
  | 9 => x48
  | 8 => y48
  | 7 => z48
  | 6 => b49
  | 5 => c49
  | _ => j3
def y36 : Nat → Nat → Option (Nat × Nat)
  | 10 => t1 177 223 4 13 7 2 p45
  | 9 => t1 185 697 7 15 9 2 d49
  | 8 => t1 39 199 6 14 8 2 f49
  | 7 => t1 11 35 3 11 5 2 g49
  | 6 => t1 1 3 1 7 1 2 h49
  | _ => fun _ => none
def x191 : w1 := ⟨1215,10,fun j => w26[j]?.getD (0,0),x26,z36,h31,y36⟩
set_option maxHeartbeats 0 in
theorem d8 : q2 x191 (j1 q4) = true := w2 4 0
def k5 (j : Nat) : Nat:=(d0 [0x764260437506145074,0x436550744365407443,0x653074436254734362,0x657236165272361651,0x723616317236163071,0x362652713626427136,0x264170435540704355,0x307042554070415550,0x704155407003547070,0x35450672465416714,0x653065360765653607,0x546536074360634121,0x606341106060416160,0x604121605341216050,0x412160134121566307,0x635663075453641483,0x531322715313227053,0x132261531022715310,0x225051643070516430,0x505135227147145542,0x463462604606417142,0x560343425603324256,0x32142530343425303,0x324246037342460371,0x424603434246033242,0x430376374316743743,0x167337431663374316,0x623743164337401475,0x374014633734657337,0x346572363562323635,0x622136356210363462,0x323634622135461480,0x354614403546143035,0x461420313522823135,0x225231352232313522,0x213134223231342221,0x313122723131223231,0x312221310522323101,0x223231012221304656,0x652434038317632675,0x154630701546306015,0x463050154630101545,0x307015453010154230,0x101541307015063460,0x150630601506301014,0x463010135322521313,0x228213132275072455,0x740724555207145574,0x71455640606418106,0x64161060541810605,0x417103645676036456,0x650364566403645483])
def l3 (j : Nat) : Nat:=(d0 [0x6453043210043201,0x64500432100432010,0x641306357005416106,0x410043210043201064,0x25174200502100640,0x251742004610006402,0x517420040210064025,0x174200401700640251,0x732003610006401517,0x420050210064015174,0x200301500640103457,0x203042106324067501,0x54021063200675010,0x540210630120364103,0x201006042537420030,0x270052345207130072,0x600523452071300523,0x5234520713004270,0x52344207130052400,0x523052071300623005,0x230520713005230052,0x305207130042600523,0x52071300412005046,0x10432010421040351,0x306420124300403113,0x64201632004031130,0x642012430040311306,0x420123500315406417,0x200162003120021053,0x21061031200210530,0x210310312002105301,0x602103120021043021,0x31030420315240103,0x600304203152401034,0x3041031524010340,0x30410315240102300,0x254064170302604002,0x460057610056201024,0x600576100341010241,0x4321004320102036,0x1674012501020340,0x16740126010203400,0x167400146101450057,0x630012561014500576,0x200451010145005761,0x5620101450057610,0x45201014500576100,0x342010145005761003,0x415101450057610012,0x31014064135200402,0x100140641352003021,0x1402413520040210,0x14024135200302100,0x140241352003017001,0x324023401034021013,0x200234010630210132,0x2340103402101304,0x607241072010013046,0x72410620100062435,0x247003640000624352,0x470034500006243524,0x700273000062007561,0x5620200620075610,0x34102005123542700,0x435000051235427003,0x240000461735642056,0x434004517156020561,0x200045171460207412,0x412314602037120,0x3247065140651000,0x32470641202506000,0x264362471037520002,0x643624710365200026,0x436247103462000214,0x726531065320002147,0x264310473200014236,0x427104362000142364,0x271043520001423642,0x710325600014236427,0x103251000134746530,0x65400001257465300,0x654000012474653006,0x540000124746530054,0x360001247465300543,5144848246007107,0x400124736542054324])
def f7 : Nat:=0x5021042110c0300c03
def g7 : Nat:=0x24914891a0c85405
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s44 : d3 x191 5 0 2 :=
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=0x7570) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem r44 : d3 x191 6 0 19 :=
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [111,0x311660000238033954,0x395f3a36481e4dbfb1])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q44 : d3 x191 7 0 137 :=
  (@m0 x191 7 0 64 73 (@m0 x191 7 0 32 32
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [65589113922,0x354b2f19185c5c3400,0x4fc7ad00d8a4cf9f00,0xa4be00d000a7a99000])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [450974194500,0x6259441f4e1a250b18,0x6118056a663a071871,0x5c536b661845495029])) rfl (by decide +kernel))) (@m0 x191 7 64 32 41
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [391999664211,0x182327273c181317,0x12683b18185d111845,0x1800442b005c472337])) rfl (by decide +kernel)) (@m0 x191 7 96 32 9
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [94560845863,0x44006c5a5d511a,0x583269584a182f1a18,0xd1418491866454010])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=0x1818403d3232183c18) rfl (by decide +kernel)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p44 : d3 x191 8 0 387 :=
  (@m0 x191 8 0 192 195 (@m0 x191 8 0 96 96 (@m0 x191 8 0 32 64
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [631370139013,0xd69c0000848a00a400,0x8f0000b6a887008200,0x88b6808a0000000000])) rfl (by decide +kernel)) (@m0 x191 8 32 32 32
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [759447997399,0xa2000000b5b2a3bd00,0x8a84ca8981c4848e00,0x829d00aa84c3bac898])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [917877271204,0xc00000b583a884d3c6,0xbc84bbd984ac009fb4,0xcc9e84cd92b8c100])) rfl (by decide +kernel)))) (@m0 x191 8 96 32 64
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [569161389987,0xa5d48484c3ce9ac580,0x84a18497c5d1bfa4aa,0xa6a88080b6b9b6d1])) rfl (by decide +kernel)) (@m0 x191 8 128 32 32
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [194720982107,0x582828462842005b,0x188684a4d6a4b9848b,0x8a8484a3bf009600ae])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [103486457406,0x584658182856451815,0x5d28555b2863180a18,0x185d00585b563e582a])) rfl (by decide +kernel))))) (@m0 x191 8 192 96 99 (@m0 x191 8 192 32 64
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [172474397509,0x4626235b5d465a,0x5b27671815186e1818,0x5823092a2d5e181828])) rfl (by decide +kernel)) (@m0 x191 8 224 32 32
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [95968303128,0x1846464667581c5818,0x462346241826185e18,0x585b2c586d334c0046])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [378248118824,0x4618285b1821180818,0x1828465b5b410e7320,0x45082358005d15183e])) rfl (by decide +kernel)))) (@m0 x191 8 288 64 35 (@m0 x191 8 288 32 32
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [190761497112,0x3f581822416e585801,0x235b083e1828434618,0x18232c0856575b1d6d])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [302208009512,0x52112d0c4558461858,0x232c56234658330818,0x285b182a5b1846185b])) rfl (by decide +kernel))) (@m0 x191 8 352 32 3
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [198328862243,0x5b43283f18185e6546,0x286a01574546000027,0x181818282d5d004618])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=0x181827) rfl (by decide +kernel))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem n44 : d3 x191 9 0 122 :=
  (@m0 x191 9 0 64 58 (@m0 x191 9 0 32 32
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=0x0) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [569431268740,0xd6b6b6bba48c8dbfb3,0x81d600000000000000,0])) rfl (by decide +kernel))) (@m0 x191 9 64 32 26
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [706987853014,0x81a4d600d6d6000091,0x8184bdc5008484b4d6,0x97daa4ab9d8400c984])) rfl (by decide +kernel))
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=(d0 [0x8cbf8495d68a94,0xb7d6d6c9af94bfa4a4,0x81848481a499ccb48c])) rfl (by decide +kernel))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem r40 : d3 x191 10 0 10 :=
  (j0 (pos:=f7) (neg:=g7) (kw:=k5) (panels:=l3) (data:=0x0) rfl (by decide +kernel))
theorem l6 : t4 x191 10 := by
  intro k hk
  interval_cases k
  · exact p0 x191 0 0
  · exact p0 x191 1 0
  · exact p0 x191 2 0
  · exact p0 x191 3 0
  · exact p0 x191 4 0
  · exact s44
  · exact r44
  · exact q44
  · exact p44
  · exact n44
  · exact r40
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem p15 : v0 false (q0 1215) 10 (vars 1215).toFinset := f13 (q:=191) (prior:=j1 q4) (n0 q4 m5) (by decide +kernel)
def v23 := f0 q4 11 [(6847,0),(1887,3),(14175,55),(8059,11),(17275,29),(17390,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem k37 : t2 false v23 := s0 (m:=6847) m5
    (k0 (q:=1215) [2, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=0) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def w21 := f0 v23 11 [(14143,2)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem h32 : t2 false w21 := s0 (m:=18111) k37
    (k0 (q:=1215) [2, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=1) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def y21 := f0 w21 11 [(17087,0),(9535,17),(4959,3),(2415,13)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem k32 : t2 false y21 := s0 (m:=17087) h32
    (k0 (q:=1215) [2, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=2) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def d24 := f0 y21 11 [(2239,0),(4927,85),(6975,17),(2399,3),(9567,55),(4975,13),(7023,86),(2427,29),(9595,11),(9703,158),(12782,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s37 : t2 false d24 := s0 (m:=2239) k32
    (k0 (q:=1215) [2, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=3) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def y23 := f0 d24 11 [(2751,0),(1343,2),(18751,26),(1375,15),(18783,56),(1391,57),(18799,58),(1403,7),(18811,87),(28135,54),(6638,31),(28142,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem n37 : t2 false y23 := s0 (m:=2751) s37
    (k0 (q:=1215) [2, 1, 2, 4, 8, 1, 4] p15
      (m2 (g:=x191) (i:=4) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def j24 := f0 y23 11 [(1727,0),(2367,2),(7007,15),(9583,57),(4987,7),(17341,23),(14318,31)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem x37 : t2 false j24 := s0 (m:=1727) n37
    (k0 (q:=1215) [2, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=5) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def t21 := f0 j24 11 [(42687,0),(44351,2),(47967,15),(53087,3),(44923,7),(69499,11),(60349,23),(69565,59),(42983,6),(45031,88),(53230,31),(60398,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f32 : t2 false t21 := s0 (m:=42687) x37
    (k0 (q:=1215) [2, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=6) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def d21 := f0 t21 11 [(58559,0),(64191,14),(51007,17),(54079,2),(46431,3),(43887,13),(54127,58),(48507,11),(43951,78),(43453,23),(64445,59),(49646,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem n31 : t2 false d21 := s0 (m:=58559) f32
    (k0 (q:=1215) [2, 1, 2, 36, 1, 9, 4] p15
      (m2 (g:=x191) (i:=7) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def g21 := f0 d21 11 [(58047,0),(47935,17),(69439,26),(44383,3),(74079,56),(50043,11),(58235,29),(69102,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q31 : t2 false g21 := s0 (m:=58047) n31
    (k0 (q:=1215) [2, 1, 2, 16, 8, 1, 4] p15
      (m2 (g:=x191) (i:=8) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def n9 := f0 g21 11 [(44223,0),(44735,53),(52927,14),(54975,8),(42815,2),(44863,85),(53055,17),(60223,26),(42847,15),(50015,55),(58207,3),(60255,56),(42863,57),(47983,86),(60271,58),(69487,13),(42875,7),(44411,29),(60283,87),(74107,11),(44989,59),(69095,88),(69607,54),(48110,31),(55278,30),(69614,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem l5 : t2 false n9 := s0 (m:=44223) q31
    (k0 (q:=1215) [16, 1, 2, 4, 1, 1, 4] p15
      (m2 (g:=x191) (i:=9) rfl rfl (n0 q4 m5) d8 l6 (by decide +kernel))) (by decide +kernel)
def l45 (i : Nat) : Nat:=(d0 [313487,0x1a284060808057fc10])
def g45 : w0 := (1,1,6,0,0,0,0,l45)
def j45 (i : Nat) : Nat:=(d0 [137887971,0xc4814a28004c828,0xa8000000128807217,0x108490827828b80af])
def m45 (i : Nat) : Nat:=(d0 [76841487043713,0x8140206a2410640600,0x40e1d00022e2050212,0x800011103640685c1c,0x10c04820d80802c260,0xc58342c08544800504,0xd78c021e1c04000874,0x80d0b4609048382010,0x50c640685848241c1,0x80283c30342c2718,0xa0c10040161a18161,0x413918d06080200bbe,0xabda425b7f9a15910f,0x2e85d003ff5cc10ffd,0x30043ff55010ffd420,0x42ff60810bfd83042f,0xf61010afd86042fb60,0x810bbd84042f760c10])
def h45 : w0 := (11,2,6,0,0,10,0,m45)
def k45 (i : Nat) : Nat:=(d0 [9042383627059296,0x6397c47943e4890180,0x297152608243b403c,0x8700800082947f1180,0x1c3285b90ec419200,0x2c8c93c003182c,0x4b157140c721300030,0x50003410000003d1e5,0x37c6746e01704d4450,0x5c06907602c0011095,0x282796c1628578340,0x1c1c40e9129862001,0x8200000514a043340,0x4082000000144000])
def s48 (j : Nat) : Nat:=(d0 [0x5e531855aca28df,0x80d3485b10aff144a3,0x3b08ac2279015e405,0x3fc243f74904e6f88,0xcfe84131fd4095e405,0xa6492532492f60487f,0x42099e4055ba01ef50,0x25bee9209cfec0916e,0x8073ee9209c7a80887,0x9e449669080ff091d4,0x57d0116e807bd8120,0x8116988c51b8c1680a,0x3e0241874390b410,0x783414020482f09088,0x6c0001070642100bd2,0xd8b0ab2a8e8a9f66f9,0x864f8f625819f3761b,0xf6b59860d6e54d414a,0xd153dcdf324ab24877,0x19c4f0f42b054002c9,0x2cc12c983ca94cb84c,0xc11eb80cca3ca134aa,0x60cad8a94ab9b89846,0xb856a15aaa38cbc0cb,0xc4a168b846cad4986a,0xa134b9e6c95a9836b9,0xd0c958b9c8a146a956,0xaa58aa46985aca3ffd,0xbff7def7ddfafeffcf,0xf618106101060c1060,0x8105cc10550104c010])
def p48 : w0 := (36,3,6,524295,51,10,1055,s48)
def r48 (i : Nat) : Nat:=(d0 [0x4200118060050,0x390014553e041769a0])
def t48 (i : Nat) : Nat:=(d0 [439822067446272,0x81c306401038600041,0x8002029b9673502d1e,0x1900abf6897361810a,0xfb6a57360810ebe5c1,0x3061810efa5c130608,0x10eee5c13061010cfb,0x649825cc10aef68973,0x610108f72a54260c10])
def q48 : w0 := (8,4,6,0,0,8,0,t48)
def p26 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xffffffffffa8c12191]),0x7c002100),(0x100d1cae,0x38d1cac),((d0 [255,0xffffffffffffffffff,0xffffffffffc4146207]),(d0 [255,0xffffffffffffffffff,0xffffffffffec000203])),(0x5308cf8,0x139088f0),((d0 [255,0xffffffffffffffffff,0xffffffffffa160574f]),(d0 [255,0xffffffffffffffffff,0xffffffffff806f560f])),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def q26 : List z2:=q7 40 (fun x => (m1 x 0 16,([64,0,32,16,8,128] : List Nat).getD (m1 x 16 3) 0,m1 x 19 16,([0,36] : List Nat).getD (m1 x 35 1) 0,m1 x 36 4)) 33 (d0 [7865053,0x76b5f1d6414005,0x1c0054400529005a40,0xf200c1400589004e,0x7675f1ce418747f1e8,0x186b5e8d602400271,0xb1700799000c8002,0xf900a040031c009480,0x25b904484006330029,0x4000e800a240053300,0x4987d5e8fa02400272,0x918725e8e4028715,0xe8e2028675e8ce0281,0x65e82c028545e8a802,0xb7d5f9fa40b725f9e4,0x40b6b5f9d640b675f9,0xce4070077100118022,0xf904a0802739041870,0x6f100218005e80002])
def v36 : List (List Nat) := z17
def d31 : Nat → w0
  | 11 => g45
  | 10 => h45
  | 9 => p48
  | 8 => q48
  | _ => j3
def t36 : Nat → Nat → Option (Nat × Nat)
  | 11 => t1 5 23 3 10 4 2 j45
  | 10 => t1 27 69 6 12 6 2 k45
  | 9 => t1 2 13 4 9 3 2 r48
  | _ => fun _ => none
def x255 : w1 := ⟨1279,11,fun j => p26[j]?.getD (0,0),q26,v36,d31,t36⟩
set_option maxHeartbeats 0 in
theorem b43 : q2 x255 (j1 n9) = true := w2 3 0
def t19 (j : Nat) : Nat:=(d0 [0x847465507548287565,0x753010647580103578,0x44026643171266431,0x212664311026523060])
def j12 (j : Nat) : Nat:=(d0 [0x760215268407,0x140007602152684021,0x500076021526800214,0x756214263002130,0x7502157680021400,0x75021526800214000,0x724013674201273007,0x12142630021400070,0x121426300213000641,0x207854107502106412,0x78541065021064120,0x785410640710641207,0x854106402106412078,0x501064021041620746,0x810017200405707468,0x100162002305817562,0x75120023058175620,0x651200230581756206,0x417002305817562064,0x120007214135200402,0x100041202345103702,0x100412023401073021])
def r26 : Nat:=(d0 [160,0x4210842110c0300c03])
def s26 : Nat:=(d0 [208,0x64a49147434114642a])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem m44 : d3 x255 8 0 8 :=
  (j0 (pos:=r26) (neg:=s26) (kw:=t19) (panels:=j12) (data:=0x304020102040392) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem l44 : d3 x255 9 0 36 :=
  (@m0 x255 9 0 32 4
  (j0 (pos:=r26) (neg:=s26) (kw:=t19) (panels:=j12) (data:=(d0 [25769937161,0x8096919089008e,0x8f8c9300858b828984,0x94888e8a810087838b])) rfl (by decide +kernel))
  (j0 (pos:=r26) (neg:=s26) (kw:=t19) (panels:=j12) (data:=0x3050807) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q40 : d3 x255 10 0 11 :=
  (j0 (pos:=r26) (neg:=s26) (kw:=t19) (panels:=j12) (data:=(d0 [38278,0x8d00000000000000])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p40 : d3 x255 11 0 1 :=
  (j0 (pos:=r26) (neg:=s26) (kw:=t19) (panels:=j12) (data:=0x0) rfl (by decide +kernel))
theorem m32 : t4 x255 11 := by
  intro k hk
  interval_cases k
  · exact p0 x255 0 0
  · exact p0 x255 1 0
  · exact p0 x255 2 0
  · exact p0 x255 3 0
  · exact p0 x255 4 0
  · exact p0 x255 5 0
  · exact p0 x255 6 0
  · exact p0 x255 7 0
  · exact m44
  · exact l44
  · exact q40
  · exact p40
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem n15 : v0 false (q0 1279) 11 (vars 1279).toFinset := f13 (q:=255) (prior:=j1 n9) (n0 n9 l5) (by decide +kernel)
def c24 := f0 n9 12 [(27127,27)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem r37 : t2 false c24 := s0 (m:=2303) l5
    (k0 (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] n15
      (g2 l5 (2112,0,2239,0,11))) (by decide +kernel)
def x21 := f0 c24 12 [(17151,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j32 : t2 false x21 := s0 (m:=17151) r37
    (k0 (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] n15
      (g2 l5 (16960,0,17087,0,11))) (by decide +kernel)
def x23 := f0 x21 12 [(18911,22),(28151,27)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem m37 : t2 false x23 := s0 (m:=2815) j32
    (k0 (q:=1279) [2, 1, 2, 4, 8, 1, 2, 4] n15
      (g2 l5 (2624,0,2751,0,11))) (by decide +kernel)
def t23 := f0 x23 12 [(17403,89)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j37 : t2 false t23 := s0 (m:=6911) m37
    (k0 (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] n15
      (g2 l5 (6720,0,6847,0,11))) (by decide +kernel)
def h24 := f0 t23 12 [(17405,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem w37 : t2 false h24 := s0 (m:=1791) j37
    (k0 (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] n15
      (g2 l5 (1600,0,1727,0,11))) (by decide +kernel)
def p24 := f0 h24 12 [(3579,79),(18941,4),(11774,159),(18942,160)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem d38 : t2 false p24 := s0 (m:=1279) w37
    (k0 (q:=1279) [16, 4, 2, 4, 1, 1, 2, 4] n15
      (m2 (g:=x255) (i:=0) rfl rfl (n0 n9 l5) b43 m32 (by decide +kernel))) (by decide +kernel)
def c21 := f0 p24 12 [(58623,0),(46559,24),(43517,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem m31 : t2 false c21 := s0 (m:=58623) d38
    (k0 (q:=1279) [2, 1, 2, 36, 1, 9, 2, 4] n15
      (g2 l5 (58432,0,58559,0,11))) (by decide +kernel)
def f21 := f0 c21 12 [(68863,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem p31 : t2 false f21 := s0 (m:=58111) m31
    (k0 (q:=1279) [2, 1, 2, 16, 8, 1, 2, 4] n15
      (g2 l5 (57920,0,58047,0,11))) (by decide +kernel)
def n21 := f0 f21 12 [(44799,53),(42975,161),(58335,24),(60383,22),(48119,46),(69623,27),(45053,90),(58365,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y31 : t2 false n21 := s0 (m:=44287) p31
    (k0 (q:=1279) [16, 1, 2, 4, 1, 1, 2, 4] n15
      (g2 l5 (44096,0,44223,0,11))) (by decide +kernel)
def y5 := f0 n21 12 [(42751,0),(47871,14),(42999,46),(60413,4),(69629,90)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem p7 : t2 false y5 := s0 (m:=42751) y31
    (k0 (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] n15
      (g2 l5 (42560,0,42687,0,11))) (by decide +kernel)
def c45 (i : Nat) : Nat:=(d0 [0x5a2c1286c92b8,0x843c484150a4502713,0xc12251208c442103,0x34401f0f074381b0d0,0x6430170b05402080a0,0x4c24110803c1c0d065,0xc160a048200e063014,0x80301004006f6f129,0x4761d803fe887fd30f,0xfa81ff54bfe087fc30])
def v44 : w0 := (6,1,8,0,0,9,0,c45)
def y44 (i : Nat) : Nat:=(d0 [1335552,0x4baed31538440,0xc1ffdeb0f6183e0600,0xa8c0b07e49b14e320,0x2839810909504c00,0x50a76d4868c100006,0x8bfa4c000000000083,0x709a00000028a80019,0xdc14911063a64efd1,2062370134,0xed2b90b0000000c28,0x9281131c40021b7200,34283569,0x241808c49c03280750,0x2389b83e000b92e08c,0x9128422147ccdc2,0x4b299c6cd4889ec33b,0x15a259e00915b38a81,0x356660ac43d82820ca,0x83712145fe1b30b939,0xf002000f12fa0743b0,0x39c1d0b445d640f03,0x5b1000194c00000010,0x45e02d07502ddb960a,0x713a47c0008c3e89f8,0x1470c2045041347100,0x1400820430050b11c3,0x5410032cc082000283])
def d45 (j : Nat) : Nat:=(d0 [0x6ffff64904012,0xa7fcc020224b7f64e1,0x30f024d2bfafe40a03,0x2481e0294604de32d2,0x2ffc68564541281bff,0x144081a63d8b81940,0x9fff785350254fffe0,0x2f017139c880000015,0x47ebf703c5804a327e,0x1f3e4c0082f1cf1be8,0x9c1b0004ec70629097,0x78125ffe0ca5ec0085,0xe09fb70ef058a20000,0xdc5fff81aae0670005,0xffd7000400fcfea200,0x2aaffec8001025157a,0xa85702d1ae1e9c8400,0x3ff3fc7f89904,0x14d7fe7f00184005c1,0x5620000af597d0ca8a,0x688f6fe300022685f5,0x54114bff14d63033df,0xf85f00ccb9c800caef,0x24afe865044340378,0x275f91338fb400f3f4,0x4a0073c6fbb087000,0x4c004ff0178007139c,0x9224a93c6a8dbca094,0xdffea8819f3f0e00,0x85a338ff5f0360058d,0x98227afe40ec8c0000,0x4fe7ff61784cbbc090,8725724279312382,0x14e3f504e40cc18553,0x8033003cfc0464a868,0x19c66172268a04d84e,0x148820c84045511124,0x69184211b10d424450,0xf4fc3981c641855454,0xd52428511404f1394b,0xa82900c2809c09094,0x1f0c00486a170520e0,0x86017c5e16e064904,0x64743a41c6518c6289,0xd565552c42c2487612,0x872188442d0320f834,0xb1303c1762a169585,0x5d3d4084844d304b51,0xc082018260882e2d96,0x540436024cd324c514,0x88e038120a0bd2b11e,0x2c86d204404a88a210,0xda2550438caf100d43,0xb0f8371270f0b83489,7888547798290776,0xe38c58a386e83a81a7,0xe378274c7106d06b16,0x9b6616155e45835535,0x255044aa44941c3e83,0xca39b3563403132e32,0xb02a526c2151e51b61,0x8713f11d0dc0c60720,0x4902300090414ae2e5,0x7352b8391cd48e6253,0x32c3c90c14ae12560,0x729829619cae324835,0x2c189609ca63257032,0x9859605cae2647132a,0x8b9589cb06a48172c0,0x994c04a40d98306c1a,0x32059b060c8126c3c3,0x6199b0251862641a84,0x81c2e0d5418ec10748,0x2830c498202c18ffff,0xefeff7fbfbfbfefbbd,0xebf549404c1100c010])
def w44 : w0 := (48,2,8,655366,67,12,1166,d45)
def z44 (i : Nat) : Nat:=(if i<1 then (d0 [0x46d2ef6d0e6207,0xb000048f9000000005,0x4c6c4bb48ca6097d01,0xf00000000000000000,197,0xec8a4109c785902e50,0xe5a00a0101c8f8501,0x720d3781340b4e400a,0xec00008421a0f450b,0x500000000000000fe0,0xe073000050bcc29,0x8100850520000700e0,0x20f098d17828141,0x90000208e000062400,0xd60b0000b032189,0x8c03bd8fe000072fc2,0x33a028302eb0e1687,0x968e540e720fca88a0,0x6d5d26d8087ea25b00,0x7a092e05b200900000,0xd5000008cb789a508,0xad0a1146feefc00788,0x2b700cd901988f070b,0x8b0b9e0e320cb00d9e,0x2a02cd80f50000903,0x9d00b0000000000003,0x18c0eac65e48cd886,0x55081d242041520ed9,0x82788a5fc223a4bc70,0x2a3026cd5d06d3084b,0xa4205624eb3ec6220,0xb200110e47053b0d4d,0xef8e90501120aec07,0x56088e429327e20294,0x67fa66306cc042f0f,0x26098e03754c58ced6,0x68122500437409000,0x90bed0c8609500a97,0x1428e870bf207fa08,0xb00007072c0c790c36,0x6a22c5a2e2d825a09,0xd0e8da83f0699884f,0x7a0000a0890000e04,0x7000000000000904d0,252124677,0x700000000361a00004,0x8375015302d3020102,0x5d010f410b8d800624,0xfab0ac00000000310,0x20000b03e000014ca2,0x80300008079a8bec06,0x5d016e013104a00008,0x4180000dec50000385,0xa000020abc8c670505,0xe0d87c282e5658a03,0x8d0a030dbe866b816e,0xc277c0eb026303500e,0x92005bed2d02356216,0x76e0042d00b08f922,0x26427686228b3e03a7,0x307609e226a02f80d,0x40aaca6c00baeac50,0x64d065c528fe25c205,0xde0b00000e0120849a,0x27e09a204ba836c05,0x89830486896dbb0550,7190580559873,0xd0000602c000000000,252434785,0x8b04e5021b083208d1,0x700000f6960000000,0x60cf0000206e00000,0xf0c4589e969,0x2e0b6f05aa0c0c8b1c,0x886d2d792212a9b041,0x5c004021000008902a,0x400000000c20c000a,0x1b00000c013000180,0xc40000c3300280,0x420000000001c0140,0x5000000000040000,0x8000000b00130e180,0x6006082001502,0x1c0080200000281004,17179942912,0xc1000000000000,0xc0307000001000000,0x2400000002800800c7,0x681000044052040,0x1810000000020001c0,0x30000800020c0001,0x83004042000180000,0x2040c1001080080044,0x802800000c1001,0x490c9000000040000,0x40001000000000000,0xb00000000d000007,0x108410000000d140,281612415684672,0xc00030000c0080000,853224244420736,2147483649,0xcd000000000001,0xc002000008080,0x3040000000000001,8796093038594,0x7100001002000000,0x3140000084000000,24576,0x200080000000000,290279659667456,0x40002000000000,0x1c0000000003041000,0x10000c0000000000]) else (d0 [798016,0xe85f900d000010d,0x80000a0d684eec100e,0x44c70cef0de2002102,0x2603fd439000000008,0x9908f200000000000,15050279416,0x2992cda18eb909bb49,0xb00a764c760c6304f0,0xc29400000000d47,0xa00008875220e56228,0x2ba8a0ec6c489f80b,0xb08350000f0a5a60fc,0x1a40df507d26e70a2,0x1b0c9e03d820c882df,0xf8000000000000000,0xe09e2091c2acc,0x60c6f87031929ca07,0x4f422e0630cd022391,0xe9be01ef05ffe6fe49,0xbc9280820a90e8900,0x40b84d760d7e041f8f,0x3383da210100fe252d,0xe2c9049a8316096d0f,0xb70f644fc28531502d,0xa98a6da24e7f8b4a0f,0x3540190cc407e5048b,0x5e50d242909034740,0x5206f0000000000000,0x80fd0000804c229,0xb70cabeeb80c5dcf8c,0x5c40dc1287b84b286,0x626600001894a8974,0x7c9c2168da2000000,0x10240000e0f1e8faa,0xf9d0ff0059fae5605,0x4b09314e2c0a3f0e24,0xafc08f12b00e0ddb0c,0x140a64061e09d00006,0xc886fd08508d6509,0x4d8c1e0ebd82140f7f,0x682e06b1040682ca86,0x9c0af64205876442c2,0x3c60662086b080382,0x90000d0b2cc83701b8,0x8c30ad00a2841e000,0x78330000000020442,0xb1c077f8d50000000,33858366672,0xe8f49006b892000,0xb8580000000000000,0x80ee401c2036000,0xa8f70000e885e,0x46285120c280b3b04,0x5205120da806400000,8112774649220,0x8000020b7f0a810031]))
def f45 (j : Nat) : Nat:=(if j<1 then (d0 [0x53d58f2b3c28eb,0x83a90e78393ce29376,0x8dc436c0d91359cd22,0x33fccd432b8c9b31e8,0xc563090c122ff0be22,0xe5cb622d3cb392c18a,0xda2a50a812994a3427,0xf09d626f4992261496,0x24dc8fa233c89b218,0xc82b20607d21e94775,0x1d3c7121bb86c21a94,0x67a198461f17d85bc1,0x62455014a050a13844,0xce128c480117842b0f,0xd83d40e4037d0d102f,0x70b4c29309a022507f,0x1d106b417a053c118,0x39c0da031c0b40284,0x66016404600cc0200,0x3400095304255c629,0x5717a5661894973e52,0x5d195317a566109531,0x3e55c9595714e56462,0x9597725641695724a5,0x61d695654e55c4f948,0x75a52618959072564d,0xf95718254c5595987e,0x554d394918a55c5c95,0x935255cd195515a55c,0x9495315e565d495987,0x256056953182558979,0x5985a5641f95716a56,0x62295656a55c0e9487,0x565641894874652610,0x949772558d394937da,0x61d9688739a5cd1699,0x70da26102d9034b662,0x2716559f4c5d698305,0xa4c602d98364589769,0x8724b65d12d974a45c,0xf69516e45c012d917,0x9a6055698744b26169,0x1604cb64cb68970cb6,0x41c91874e154d56897,0x2634c21716356164d4,0x90985da24e06887463,0x64e17d9775a6616698,0x14da261f2d977235c9,0x391206da649b699181,0xa65d169811a154da91,0x935da609490815da5c,0x112d976a4605791725,0xcb65cc7d7174b65939,0x1706da6608912060b6,0x55291315e45c1a6987,0x50b2614689744b65ce,0x68816da65c969875a4,0x5c132d926da21d9853,0x13db5c5e6898623249,0x92d9649a605a7d4179,0xa615369534a465d32d,0x9169a61da698159a26,0x2269916da481b68816,0x9a6622689871a61556,0x99381a4c112d987244,0x857697180b64606887,0x4a154d3698121a6047,0x69706e421d3698569a,0x24602d9189f64dd698,0x16da21da8d71864659,0x3698704b644f69826e,0x35c962d916cb64927d,0x4181a6095698559a24,0x5b69874e35c9a90814,0xe365e191514da66182,0xd9131a61c769985245,0x953716555a61c39181,0x4c465d111980042610,0x35870c4660421932d7,0x65c21098604660d259,0x784465c519954a04c5,0x71197384660f3d861c,0xf604a81534c464d23d,0x8618464e0159631960,0x53618120f644a59900,0xd665c3119548a640d8,0x9724ca640051877595,0xc1b5d8205625c32592,0x35760805d820c42614,0x119039764c23d8621d,0x54611d9411e4c5d498,0x50c465d28930854610,0x17553844649b119820,0xf244a59700d2614111,0x9180466223d8604964,0x8b019715061434d840,0x8c61c3059548165454,0x58508264d239860956,0x830d9217ffffeff7f,0xebfbff6fdffb7edfbf,0xeffbff7f6fddf7bdf7,0x9eefdd7b7f6ded7d7f,0xaef3fe77bff7fafddf,0x7bdf77edfcff9f73de,0x6fc7f4c1524815261d,0x405c5405c140505404,0xc54061930609306053,0x5c5305c1305893058,0x130545304813020530,0x60d105cd104c11020d,0x101cd100c110041106,0x1830604305c4305c03,0x4c030204301c43060,0xc10608104c0101cc10]) else (if j<2 then (d0 [726470055827474,0x5a4c0d94ff1102129f,0xfd080042d275fc88cc,0x7d08e32d5a4ca1d3e2,0x40ca037fc0042243d7,0x8c55d1318fe00895ff,0xf0e105d3009081b01d,0x1fd4e20010e7b410dc,0x82500e01ff0000d08c,0x5060b310c019f4978f,0xfef011359ed040b978,0xa3df8cc28180257304,0x85f341944407c3d214,0x551e90632fde35400c,0xe503bbfd64a14479eb,0xd08198bf837d44a804,0x4d40dfc218819dbe3f,0xb489689a11fd4cfa84,0x10a203b8c33a15081a,0x8f482827f7a6d123c1,0x44da94fef4220672f,0xf8fda88267aebe1881,0x981af92c4649019120,0x6189cd483f27d44849,0x174c4a3c749363910,0xd1e90630ef8780361f,0xf911abdb383b610b5f,0x13eba1b0203547ec9e,0x824206907fb855000c,0x14449c5d78852e1c8a,0xd47cc58b8f0853da08,0x8ff1343221a0f76445,0x2011fdd10858604791,0x431a4bbe9cd63940d2,0x2e1078c2057cbebd8a,0xa49a3359ed0427c0af,0x2080034400017c0bbe,0x142f9501b60af51a91,0xd3e015c308f48d5aaf,0x7fb0e401527fcb0c8f,0x4880466b0029f743c2,0x871a470e26782bd46a,0x479fea3fe0240932f2,0x82e30219bffe705d07,0x1346fc66140c0128a0,0x67b410f6821ed040ef,0xce05fa1e10d25033da,0x87b410f6821ed0428,0x1c0e41a23c2e3080f2,0x1c82d0944b4cc4ab92,0xce2024c969130ec472,0x814036174444546487,0xc211c18800fa1ed3c6,0x140189d9240742621c,0x3786b6b0562abd2aa,0x658220144644024448,0x13026719d05a6686b1,0x984442810b1861861d,0xc22c9108c470042084,0xa0a125175b8d0fa84,0x91844c10c39881a022,0x281e0f2a006d41e965,0x24896817824458500c,0xa4084731d22819a8e8,0x8710c1161542081887,0x40800f0dc18d0622c4,0x3623134400c041dc3a,0xb410e64af12e2d12b4,0xc795a0211a4c890171,0x84ac703384681383b0,0xe220c8188a0d08a49,0xd1a151cc378b28a70,0xf0bc1ea0a42d09180e,0x385108e88686e0fc0,0x813f0686165689024b,0x11a661a31087840148,0x19060ac461ff058434,0x7c17695a070700e436,0x4a0d216e0307c8499,0x649f2066215043f30f,0x6e0d2881070d40f81,0xd83606a0bc2683ac48,0x1c0004c00c0ba6cd9,0xa72682994e633984a5,0xe997565c3964256995,0xa523942e4f4936a4c,0x925246e917643e908,0xe4048f223ad8e4e378,0x8d5a32f8c462db8aca,0x27f895e23f88aa2048,0x74a1ba866e175854e1,0x3484520f9833a0b682,0xba09281f205780ae00,0xf7fc9fd57ecdf9e7e2,0x1f357c11ef47b11ea8,0x7959e2c7871dfa7741,0xda57601d607501d0e7,0x3d1ccf728dc83718dc,0x4870b9c0b6f8db9f6d,0xfdb596ccdb046b9dac,0x76aa1a8a69c1a32676,0x99c266959796529913,0x63e18c862598786119,0x81b5fd17d85eb57775,0xd2d7275c216be5a856,0x7e598962858455e256,0xa558f559d51e53ad4d,0x2529d49851f1456510,0x541650013d74ead37c,0x4d3d3384c4d2ee4b05,0x2a149c5249489120c4,0x7b91ce46bd18e45511,0x2744210ea430108b41,0x3901e402cfe43efcf8]) else (d0 [49292039,0xbc14abdfc307b7cc69,0xf38145081a23fe8819,0x1ef881084fe013a08,0x547682bc08c9d1ec34,0x420438ffa252847172,0xf00810a97f7d114b96,0x18fbd23190f884c4f4,0x813469ff92003369f8,0x4009499a625fde088b,0xd9571903cb803233ff,0xc88b00020444389183,0x5f70913be00324f1dc,0x2c8dded86c01980f50,0xa327ffc4d185021e1,0xeaea8810aefea20a20,0x21c3a7c2c01997181,0x10f88498f25040429b,0xfca5410010e5d2cc70,0xe2c3a137e3d9104747,0xe100211bfe003255f9,0x8051aff1044a87d892,0x18cffb7184019ca08c,0x87321269f5983a927e,0x8501b41251f09a0f6b,0x1888a174c4a3578cfd,0x210bcc0c3ed2197fff,0xc5a3080e0854206d53,0xf4482041535911d8fe,0x7e60441647c503243e,0x1da8c958204200811a,0x1fe7da913334029feb,0x118511ff95848330f7,0x3e7400488bfa10023c,0xf83f022cfaa8023037,0x9971f140d0bd62a22f,0xfcc0411b7fe140a092,0x34f15091b7a4be1159,0xfe903cc780896fed48,0xa13dfa9b0021400d7b,0xdd44fa02228de1002,0x133aacb806633f2003,0xa90193ffd31033c7db,0x499213760a107c5632,0x2af8e408a3437a247f,0xe881e00c000d411ff8,0x7d00ad07f708804df7,0xf90499f420643be040,0x300a502e0cffc28cfd,0xb7f8547a889a4efe01,0x2ede01555805373f06,0x1200010e3fa8822a3a,0x7aa090010e1ff85000,0x1986fd2c68238d7c22,0x2ebfff2a428517fc9b,0xa8410a1f71f44c0412,0x57e97c411b32a94329,0x7ffffd6190000804d7,0x5e700646fe1268cb5f,0xf104ccfcff92080004,0x45cd025064fff4c40c,0xe5fc1be9a60a06959f,0x41125d9df21a1483f1,0xfded08000440da5ff8,0x4202501a17fb00de7c,0x2061295c0253e9041,0x97a409b4cc798240ff,0xe02840cc6e4128bfc8,0x2002175fe9da0021ad,0xfcfcc2a1437bfa2401,0x219fec02de721f20a,0xb1e1050cc027924e7,0x86cfd42065dbea0a2,0x100a657b3a1c08577d,0xe82042d61ab1a8fe00,0x8b97fa808bb9e8091a,0x5dd54108077c7d86cc,0x24403fc56420a194f,0xc88518f58c28b9e184,0xa8033f3ff4214410a1,0xe9ff6e9016358512bd,0x7c54440093b110c3e3,0x680033698595029012,0xff94541840888b876c,0x6054c5fe564c819b9,0xf40090801ff67a5861,0x1f58220371f4120e0a,0xf50952483fd0610217,0xde28040850fffc0150,0xdba624048da7c412d9,0xa924df302a3bbec500])))
def x44 : w0 := (259,3,8,2490403,102,14,1251,f45)
def b45 (i : Nat) : Nat:=(if i<1 then (d0 [0xa087405c06c402,0xf82ba83696c9af3800,0x20581025c55122e28,0x1908bb4a800000001,0x279141156dc2ea0bb,0xe97b882043dd877c92,0x7e075027bc12c0b200,0xc016c9d214d30d80,0x707200000000,0x814000000000000000,0xd18472f34d40000000,0x141af8c80100a06ee0,0x7884c906413302cbad,0x3f3a040001ae400004,0x2d0000804382d35bc,0x90b842700000000000,447209371760,0x980000000bb4342200,2732581424,0x820e832a09a03edc80,0xb16922440004012219,0x4e0c0000287fd0fc00,52340721250,0x46c696615920d28070,0x80e051ead519854,0xe2638088000000,0x413941e80006b6800,0x2444e038214461a9a,0x16103679540003456d,0x853a85c0003c8b402b,0x30923252c21f87c50c,0xc00030140000615e41,0xdb244ea87203400008,0x3a461b0000000361c8,25389635043328,0x713ba28f13bb09e000,0x16c989b88095c8fb40,0x600003132000000000,0x4c17112c62370304,0xc35b963604cc50a20c,0xf77192b6d10e82a50f,0x631740ab295000100,0x6d63651b4110921c40,0xf29800000000,74100774405169229,0x10a3d0b69457501415,0x540fb0317108901300,0xf1ca26ba6b88be0286,0x581671518f8301a3a0,0xf1eec2f0000,0x804902c4e42645e514,0x8000044038c3e0620e,0xec85cb8165902a0d5e,0x1c12bbd05e0184c438,0xcb87943ad3ec2048a8,0x28787ab3655c428194,0x1faef8ada8b3748400,0x2503606e46fd88010,0x4d7081c13778dcc264,0x8bd60afae8f62d08a9,0x85080001451718,0x9001e8024846210400,0x7c65112471b40,839,0xbc2107f6240000782c,0x299202d9807d850c16,0xac016aa2590a10aa00,0,2693547160,0x53210ebbae1437c852,0x78ed02f9847369f101,0x9400433e11227d0d60,0xa563100bab4d2307d4,0x428041e866819fd861,0x848f089b0acc252897,0xc044e037053e073a08,0xb90a64000079818df3,0xe02fa09fe0b0531d0,0x591863ad48015abd14,0x24360e4221b80e38a5,0xb0ca72a4841bc7520f,0x4801bc1df04718c741,0x2d064b8c8000142fc4,0x4550ab000000035183,0x83346af14c70608008,0xd96be4c4639a02e000,0x304080000000100181,0x20000001450c6153,0x201000280026102080,0xc000824d000203000,0xc00430c0202006,17321984,0x383000040001000000,0x810000000e040,0x4100010d0801800c2,0x40040000004143,0x1000000140000000,0x1009000002000000,0x10400020c0000000,755981361152,0x1000000000000040,17799418220544,4604204941377,0x6000100003087000,8796093022208,0x400c6080080000040,0x2040005082000080,0x1000200000000042,0x40040005080080080,0x1000000040000000,0x41000000040000001,0x80006000001000001,0,0x1000000000000000]) else (d0 [12087997691,0xa781186efec4a18424,0x90a80c8847a92012c1]))
def j48 (j : Nat) : Nat:=(if j<1 then (d0 [0x5a2c6b4e344b82,0x353242352c282e4709,0xb5145eb04a292e47c9,0xb4afc2152e1f2e2a66,0xaa76942a4e8cb49462,0x2e2e0cb491c9950529,0x240a0c34b454330e5e,0xae4cc9b511e6aa4717,0xae4989b4ed1a346149,0xb4f20f341467a633e3,0x2a2c54130ed41512c2,0x34ebe2ae0e9632a5c9,0xb4748215244f344d8f,0x34cd8f152ddeae490e,0x342ca7a831e12e485e,0xae50cab46ad634460f,0x34e654130a02352b89,0xb517142604941317e1,0x2e300e344409b43754,0x32ea54b2e5cf150dd6,0x2ca9cf34a69a302c4f,0x34c68234c9dc30f354,0x130d669536692e474f,0x34268e344a89b4751b,0x2a2d1c30f30234e9d4,0x1517d41312c9b42fde,0xb4e0e5aa7709b4af57,0xb245cf150e423525e3,0xac079eae48dda63569,0x2e48272a27c13524c1,0x3449c1344e811503c1,0x35255ba63384b4d544,0xb4e341353110b46626,0x26160e942981352d01,0x3475d394318894318d,0x34665332e1c19526c1,0x34380db44686349516,0xa83293344086348304,0x9522d594060bb4a644,0xb4e390b2b112350290,0xb2a588344547b47097,0x2616d0aa69c8344f48,0x34021ca630982e01a1,0xae2e0834424bb4ad90,0xaa38252a271e241764,0xaa4701350989151155,0x2a69c5b4b04b34761b,0xa8320134c9d534661d,0x263145b4a259ae0159,0x2e238db4464a34ed81,0x352cc135314134e9cd,0x342705b4af90aca9da,0xae0105b4b0a0ae289e,0x2a48de2e48c9341541,0x15359032a0202e2e00,0x1522c0b4408fb0c292,0xb040642a4707340243,0x34a346b44243b48345,0x34a244344342b4e351,0x328011b0807ff3febf,0xdbfcffb7f7bf6ff6bf,0x5ff5bf4ff4befbe7fd,0xfbdf7df3defdebdd3b,0xfbbf7befbebbdfbdbb,0xd7bbfbb7b7fb7baffa,0xfbaf79ff9fb7ef7eb7,0xb777f77b75f5ff3ff3,0xf73ef3eb3bf3bb3af3,0x7f36f2beffaff2feef,0xeafdafbef7ef7af6ee,0xfedfabfebfabf6beeb,0xdebdabcebbeb7eb5ea,0xfeaeeabea7e8fe7fe7,0xfa3fe3ee2fd984c152,0x64530549714c152261,0x30548914c15265d205,0x49714815254d205495,0x148152645875013161,0xd4024d875009161d40,0x64d71500985c54024d,0x71501715c140505705,0x187505405c5415013,0x15054065d31501904c,0x5405c531500984c540,0x25d3150192619305c1,0x864c15161930481864,0xc09161930205864c17,0x26093021d824c08160,0x93021d814c1985c530,0x641714c0985c530589,0x704c1315c130485704,0xc0815c13061d624c18,0x558930605624c17258,0x930595624c15158930,0x261624c08758930615,0x604c18258130595604,0xc08758130609514c17,0x254530261514c19648,0x13061d204c18548130,0x605204c172481305c5,0x204c17048130595204,0xc16348130581204c15,0x348130545204c08748,0x130205204c19520530,0x5c8814c1532053021c,0x814c17360d105c1834,0x40985cd105c5304409,0x74c11065c834419161,0x830245860c09760430,0x619710c1941c43025d,0x83041976081064d820,0x41874c010619300418,0x54c01060930041981c,0xc1064073041821cc10]) else (d0 [3549275,0xf610c3eb16a0f78313,0x259a16018b360a9f10,0x20ef08ac84e1493586,0x87710ef811806dc08,0xf490f0c6a2601ae509,0x1c1046648f7d2431b8,0x43c342afe64645d213,0x4087bd144b9847522e,0xe8c4dc189c047018f3,0x90d40b2e8594b1081e,0xdd0b3e0241dec472b4,0x246af906806788830d,0x68cb760514584df01,0x20f2e850c1058f0f02,0x12ae845fa09e01cca1,0x5e22d910c023488b22,0xf7a20b6b88720e6891,0x61514304a0dbca8c60,0xe8e20d8076910fd811,0x7a90d807384217041,0x53cc4838e04c75c018,0xcfa233c22ea4d14722,0x9c443187434d85e01b,0xbdd050c0a029f98a72,0x13bd9053f810ce1120,0x1bc030704135d0af09,0xef113809617a19e11,0x20378896350dbae58d,0x7e021a7f9341653844,0x7e035025020fac5622,0xcfe9244cb3f121cd55,0xc7b8864c89013b01d,0x795318f350dd01ba03,0x7a03b66826fc047792,0xb7f311117f8218f42,0x1cb2d5070ea9419d91,0x57940032cf021d52c5,0xbc1436811322179850,0x6e80d0127f446265d6,0x8920dec0680a3e0631,0xc422051e818c991172,0xc18eb8031da118bc40,0x835e821bf00c4f086c,0xe0733429aa12fec110,0xfc119028f818f73426,0x200e30411f80c9b23,0x4047fc04859147c0c6,0x3a843c721a0e384719,0x239fc10ce05bef9220,0x3ffe3641203e90c66,0x50ff58992bf5c4c93f,0x1c110003813ff024e7,0xf081932f1432f4d18f,0x39aa643fe2240373ed,0x140dcfb45df7c91013,0xc18dcad880270dc441,0xc26b480c20266c4589,0x9250d2e0e8874ac26,0x92b88420217891a0d,0x54742281b6482c81d0,0x747281a198119450c3,0xdc381a4a5e26c27825,0x823e0d20001d023017,0x46741d4c4443144021,0x780780c17119a25e17,0x55c6c3c25749010c0d,0x501824c2079640e40f,0x813e19f0901b344081,0x825016c00350601813,0x40e81fc01801f8901f,0x81f01a81300bc0bbe2,0xfdd3d87d57ce7cabc7,0x7c23bb3b73b43af3aa,0x3a53a079e39a79538f,0xb8c788382f7e378b73,0xb6fb68b6476135ab55,0xf52b4df49345f4273d,0x33a335f3172e72a723,0x71ef1ab13f10f0d304,0xeff6fc2f52f0eebee4,0x2e02db2d76d36cfacb,0x2c8ac52c1abc2b6eb0,0xeab6a529ee98294e91,0x68b286282e7ea79672,0xa6ce67262a5ea59655,0xa50a4ba4824463ee3b,0x638e3423062ae25221,0x61e61aa1561160c208,0x6051ff5fb5f8df51f0,0x1ea1e45db9d7dd39d0,0x9cd9c8dc59bcdb75b2,0x1acda91a65a259c597,0x19358f98b98698197c,0x17516f56a563d5d559,0x55154c547d4293f53b,0x934d3112e52591f11a,0xd1811290e90bd06102,0x4fc0f64f24eb8e64e2,0xdccd8cd48d04ca0c5,0x4c28bd0b88b58b34ae,0x4aa0a58a2c9cc99493,0xc8e888083c7f87a076,0xc7046505c85504dc47,0x3b43402e82802181b,0x81400c806000023537,0x97ae57d433049fb027,0xd634c6141314d634e6,0x9b4cf68ae2729ae26,0xdeae4b142e3814130f,0x1eae4d18ae0ea22634,0x28952709b4efa92417,0x8c34b714152d49b4cf,0xdeae4949b4355b14ad]))
def x47 : w0 := (203,4,8,5505121,119,12,1118,j48)
def d48 (i : Nat) : Nat:=(d0 [592579168,0x10e441400000002b21,0xa46000182e001301e1,0xc617a1e0013ac00000,0x208000000001c3062,0xc000c03a1862803620,0xc233810023c068ec35,0x400191ca2600020efa,0x5404820000a1200000,0x224001208c05149e1])
def k48 (i : Nat) : Nat:=(d0 [6020,0x5e10350405c07c100,0x1805c203f01a840000,0x4004c083a83e24100,0xbc3d2400300b8604c0,0x35080fc02f1013005c,0x200233ae2400300b88,0x4d00300bc7d240260,0xb87e2401708002f01,0x70a33be2400300b880,0x6017080981adaa4a4,0xa73952358c21e86607,0x809e3745a561967521,0x434f905364ad238891,0xa83104800bcdb6c54a,0xa6902a5fd24c0a954d,0x2054bfa4a9a40b92a2,0x985779b72819520530,0xcebaa6d3930a8a61e7,0x95c971609514c2bbc5,0xcaa2b2a40986bb5a75,0x4984c540cfe152b8a,0xa290261f78545715c9,0x204c2f6cdb152a9a40,0x987dd1315c0985c530,0xafd172902e4a8a61ad,0x754da12613054bfa49,0x82a6b8a40a96adda64,0xc49361d40fec2e2982,0xa2902a58eb691a2660,0x730431b6cab4443902,0x985739b42819520530,0xaeb172a8aa690261ed,0x254d202613054a3bc5,0xcb4a40ae098636da56,0x89981cc108f736854a,0xa29026155e6dca0654,0x814c2bb4d9140ca902,0x986f49526855348130])
def y47 : w0 := (28,5,8,0,0,10,0,k48)
def f48 (i : Nat) : Nat:=(d0 [0x2022120a00481835b,0xb4200000707b100030])
def l48 (i : Nat) : Nat:=(d0 [14600,0x5c1eb5c2b99303f50,0x54d515c57248130e5e,0x1722a571545204c379,0x2549b62a5534813097,0x39c42e551595204c35,0xd254cb948172545308,0x3b8c86d0a9545204c3,0x1c654db42a55148130])
def z47 : w0 := (7,6,8,0,0,6,0,l48)
def g48 (i : Nat) : Nat:=0x78001b2d178400008
def m48 (i : Nat) : Nat:=(d0 [0x3507340795054d722,0xa571545204c22671b0,0xe2172a8aca90261474,0x8da54cb94817254530])
def b48 : w0 := (3,7,8,0,0,5,0,m48)
def h48 (i : Nat) : Nat:=0x1e0
def n48 (i : Nat) : Nat:=(d0 [56938811484,0x4da54cb94817254530])
def c48 : w0 := (1,8,8,0,0,0,0,n48)
def m26 : Array (Bits × Bits):=#[(0x840a108bec0006,0xd3584ac0e0a004),((d0 [255,0xffffffffffffffffff,0xffff24640550c50029]),(d0 [255,0xffffffffffffffffff,0xffff2c85b1021f1821])),((d0 [255,0xffffffffffffffffff,0xffff61200154008957]),0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),((d0 [255,0xffffffffffffffffff,0xffff000b70212005e1]),(d0 [255,0xffffffffffffffffff,0xffff28a2b4371545e1])),((d0 [255,0xffffffffffffffffff,0xffff8880028a0a427f]),(d0 [255,0xffffffffffffffffff,0xffff04a7252e0a5a3b])),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def n26 : List z2:=q7 41 (fun x => (m1 x 0 17,([0,1,16,2,8,256,32,4,64] : List Nat).getD (m1 x 17 4) 0,m1 x 21 17,0,([7,11,9,8,4,5] : List Nat).getD (m1 x 38 3) 0)) 159 (d0 [274907791441,0x9834f401885000c600,0x11c6495e02410c0091,0x80017200074002c500,0x2620004e6043f002a0,0x400138005620014c00,0x259002320006600157,90731418249333168,0xd7818442186c60c21c,0xa003b000a20759c83a,0x9183ad381d462000f6,0x104a00670008c009,0xb18048718b57805842,0xc26e60120c6eb79075,0x3324bc81201a00518,0x80052974fe0bb002bb,0x6f05d08310af008084,0x24e40108cc025e000,0x50801617000d4000ec,0x489824f401085000,0x9cc01110017a000028,0x67a70338c600530000,0x6615a720ac468004e0,0x988560f82b580001,0xbc0022100294000356,0xab2f055284009c0001,0x1c925ec09008d5a7a0,0xac420cf3e06720857b,0x182b870005b4000250,0x73001060eb7a0750,0x2c0098b8012a000798,0x28214c3e0a7606493,0xd024213022f8014812,0xf5f817802a1efa10e0,0x24eb7d0750125abe82,0xd00806d3803462c4ad,0xc024116eb6e07508b2,0x4b7012045815cc0081,0x80027c000418012c00,0x29a563f82b400805b,0xc0002061e7e10e402e,0xb3f075201579f82b90,0x924fc0908044a7e02,0x44021b3f00d201099f,0x804901485f82400298,0x6fc0c2010013700024,0x20dbf0068060005d40,0xd1000c6801142257b,0x120225abb82d0212a,0x9fc1560098eee0c608,0x4097d004010040f802,0x5800958c04838642be,0x120200015d00011161,0xaf830880b1cfc18c80,0x5767e0ba402373f01b,0x200000f800580b3cfc,0x19c8094cfe0a7000a7,0x630530e4009c180116,0x5180007284afc024,0x14c77e06300a75bf0,0x3a805125f809002956,0xfa0aa023217b090021,0x75bd83a810b0dec184,0x8426f601204801622,0x6c00a60800c8a9d,0xec14c0854e7e0a6402,0x13f00020175b783a8,0x40925bc0902044ade0,0x241021b6f00d08109b,0x7804840a9dbc14c205,0x56de0aa102ad5f0561,0x156bd82b010ab4fc1,0x588057af60bc042437,0xb0210210fbd807810b,0xad7c1d44056abe0b42,0x2a75f05310124af81,0x20808dd7c06c4044ab,0xe0242021b5f00d1010,0x9af80488081d7c00c4,0x61ef610e042af7b05,0x702167af833880aed7,0xc17440402f60000420,0x15f00010169b783484,0xb4cfc1a480c02b600,0x242057b002021029f,0x801100815bc0082040,0xabe004200013900023,0xa70000c5005f800,0x2412f6008042096f,0x4081049f80210082,0x57c01040002c60001c])
def r36 : List (List Nat) := t24
def z30 : Nat → w0
  | 12 => v44
  | 11 => w44
  | 10 => x44
  | 9 => x47
  | 8 => y47
  | 7 => z47
  | 6 => b48
  | 5 => c48
  | _ => j3
def q36 : Nat → Nat → Option (Nat × Nat)
  | 12 => t1 35 135 6 13 6 3 y44
  | 11 => t1 470 589 6 16 9 3 z44
  | 10 => t1 338 423 6 15 8 3 b45
  | 9 => t1 9 55 5 12 5 3 d48
  | 8 => t1 3 13 3 10 3 3 f48
  | 7 => t1 4 7 1 9 2 3 g48
  | 6 => t1 1 3 1 8 1 3 h48
  | _ => fun _ => none
def x383 : w1 := ⟨1407,12,fun j => m26[j]?.getD (0,0),n26,r36,z30,q36⟩
set_option maxHeartbeats 0 in
theorem p12 : q2 x383 (j1 y5) = true := w2 4 1
def t5 (j : Nat) : Nat:=(d0 [0x965808769465,0x755094657540946575,0x309461755092462752,0x855829948558298485,0x582975855829648558,0x295485582153824627,0x738246275382462752,0x823627738206276281,0x756661817566518175,0x664181756640817566,0x206567401065614010,0x656040106557417565,0x574153655141856537,0x501065374070653740,0x106530401056854187,0x568541655685314356,0x784170567640705675,0x419056754180567541,0x705675316056752150,0x560640805606407056,0x64060560640405603,0x408049568574495685,0x734847668442482343,0x424823324247233242,0x452343424523324176,0x809041768070318412,0x323154128526783191,0x267831212678311026,0x763191267631212675,0x412126184171261841,0x612618412126083191,0x260541812453237314,0x678090146780101461,0x801014608070146080,0x501460801013451272])
def q3 (j : Nat) : Nat:=(d0 [533254,0x318240152300810252,0x493100532008015021,0x683021531076255694,0x810653000762326318,0x2751007620569180,0x38400076202691800,0x762000750208924604,0x653107361519420050,0x210070352810670142,0x300703228196702845,0x6783004321004311,0x67136584900463000,0x670365849004830006,0x350690857005460063,0x406918570054600634,0x69185700485006340,0x691857004350063200,0x786120761310632007,0x861206502106320078,0x612057021063200786,0x120541810632007861,0x205402106320078612,0x43021063200786020,0x850210632007860207,0x502106320078602065,0x191063200786020650,0x210630531470204312,0x6012648130040260,0x54077183620671200,0x540771836205217005,0x267091485008530042,0x654735820407300426,0x7658201073004260,0x76582010630042600,0x765820096200426007,0x658200862004260076,0x582007510041730756,0x930017300370208612,0x4017103407907562,0x37050031569275130,0x642300307214263002,0x140003016947530075,0x400030121426300214,0x301214263001830,0x2765068950056411,0x27600689500564010,0x276006895004530102,0x713352490039400027,0x133524900384000271,0x335249003450002710,0x352490034500025800,0x543290032410240691,0x856207512002406918,0x562065120024069185,0x620641800240671856,0x204716002106928531,0x75320021069285310,0x642800210692853105,0x726002106928531053,0x260020569485300754,0x205694853006840,0x2056948530064380,0x20569485300643000,0x205694853005320002,0x36012780029611020,0x360127800236110201,0x694853007540002016,0x948530068400020169,0x485300674000201694,0x853006540002016948,0x530064800020169485,0x300643000201694853,0x5730002016948530,0x53260016720598600,0x576010167205986004,0x650101620263180032,0x610015360168920045,0x110132681962007621,0x1326819620068210,0x13268196200651000,0x123683962005428000,0x765826713056230007,0x628269170451200067,0x283674206743000621,0x463581040610006214,0x635800305100054601,0x687200346100346006,0x875004571003284135,0x200402100032681962,0x7621000326817620,0x76210003268176200,0x659100032681762006,0x521000321413520040,0x210002674730820407,0x300025683764207643,0x256837642065320])
def l7 : Nat:=(d0 [147776,0x8410842110c0300c03])
def m7 : Nat:=(d0 [276,0x89414e86824914642a])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem k44 : d3 x383 5 0 1 :=
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x43) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem j44 : d3 x383 6 0 3 :=
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x2c1125) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem h44 : d3 x383 7 0 7 :=
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x342d2111268edc) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g44 : d3 x383 8 0 28 :=
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [12,0x392711360349312e35,0x22002836140833a799,0xcededfcfa894bde2bc])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f44 : d3 x383 9 0 203 :=
  (@m0 x383 9 0 96 107 (@m0 x383 9 0 32 64
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [789196939174,0xb889a5b8cfa50098c8,0x918700000000000000,0])) rfl (by decide +kernel)) (@m0 x383 9 32 32 32
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [892642041220,0xb89aa3c5b89ae1a2cc,0x9acf9e00e0aba6a4,0xdba5c6d89fd0009ed1])) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [233070808122,0x409f9f9f9f9fd99283,0x9fb88a009f9fa3a3d4,0x8b009fb4b290a99bb0])) rfl (by decide +kernel)))) (@m0 x383 9 96 64 43 (@m0 x383 9 96 32 32
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [232837892112,0x36363624122438242f,0x15383b2b1f1332194c,0x3638301c3c0b383624])) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [26713017613,0x45381230171d410238,0x36003c060f24201618,0x3e4b4718120b241c36])) rfl (by decide +kernel))) (@m0 x383 9 160 32 11
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [22384416007,0x3a361e0b38361b1538,0x123606363b06092336,0x1204013606004c3829])) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [14392,0x382a1238123800000a])) rfl (by decide +kernel)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem n40 : d3 x383 10 0 259 :=
  (@m0 x383 10 0 128 131 (@m0 x383 10 0 64 64 (@m0 x383 10 0 32 32
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x0) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x0) rfl (by decide +kernel))) (@m0 x383 10 64 32 32
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [715900584095,0xa60086c3b3c49fa68d,0xb6d6e500b09f9581c0,0xa08cc0000000000000])) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [579342547159,0x86889fc3a681a686be,0xaa93868600b1869fcb,0xb000c9b5a6b19fbb86])) rfl (by decide +kernel)))) (@m0 x383 10 128 64 67 (@m0 x383 10 128 32 32
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [570333188757,0x86ca00b8b200cab000,0xd300ca82d39fb8a6b9,0xc3ca869f00dae485ae])) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [869761451690,0x9f86009f9f86c0a19f,0xacadc7ca939f808fa6,0x8db0ddb6c1a6939f00])) rfl (by decide +kernel))) (@m0 x383 10 192 32 35
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [233224222214,0x36360f12000f0f4d,0x4606ba9fb8b8b8879f,0xc29686979f00b09f00])) rfl (by decide +kernel)) (@m0 x383 10 224 32 3
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=(d0 [252641295,0x4e4600364d423d3642,0x36004a060646063d,0xb4d0e0f4200000e4d])) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0xf0006) rfl (by decide +kernel))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem m40 : d3 x383 11 0 48 :=
  (@m0 x383 11 0 32 16
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x0) rfl (by decide +kernel))
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x0) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem l40 : d3 x383 12 0 6 :=
  (j0 (pos:=l7) (neg:=m7) (kw:=t5) (panels:=q3) (data:=0x0) rfl (by decide +kernel))
theorem k9 : t4 x383 12 := by
  intro k hk
  interval_cases k
  · exact p0 x383 0 0
  · exact p0 x383 1 0
  · exact p0 x383 2 0
  · exact p0 x383 3 0
  · exact p0 x383 4 0
  · exact k44
  · exact j44
  · exact h44
  · exact g44
  · exact f44
  · exact n40
  · exact m40
  · exact l40
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem l23 : v0 false (q0 1407) 12 (vars 1407).toFinset := f13 (q:=383) (prior:=j1 y5) (n0 y5 p7) (by decide +kernel)
def b24 := f0 y5 13 [(9599,91),(17343,60),(9711,92)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q37 : t2 false b24 := s0 (m:=2431) p7
    (k0 (q:=1407) [2, 1, 2, 4, 1, 1, 2, 8] l23
      (m2 (g:=x383) (i:=0) rfl rfl (n0 y5 p7) p12 k9 (by decide +kernel))) (by decide +kernel)
def n24 := f0 b24 13 [(28143,93)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem c38 : t2 false n24 := s0 (m:=1407) q37
    (k0 (q:=1407) [16, 4, 2, 4, 1, 1, 2, 8] l23
      (m2 (g:=x383) (i:=1) rfl rfl (n0 y5 p7) p12 k9 (by decide +kernel))) (by decide +kernel)
def h21 := f0 n24 13 [(54143,0),(64447,94),(44015,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem r31 : t2 false h21 := s0 (m:=54143) c38
    (k0 (q:=1407) [2, 1, 34, 4, 1, 5, 2, 8] l23
      (m2 (g:=x383) (i:=2) rfl rfl (n0 y5 p7) p12 k9 (by decide +kernel))) (by decide +kernel)
def m21 := f0 h21 13 [(44927,95),(47999,1),(53119,162),(58239,4),(69503,163),(58303,24),(60351,60),(69567,94),(42991,19),(60399,164),(69103,165)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem w31 : t2 false m21 := s0 (m:=44415) r31
    (k0 (q:=1407) [16, 1, 2, 4, 1, 1, 2, 8] l23
      (m2 (g:=x383) (i:=3) rfl rfl (n0 y5 p7) p12 k9 (by decide +kernel))) (by decide +kernel)
def q21 := f0 m21 13 [(43903,0),(46463,95),(48511,1),(51071,91),(43455,47),(43967,89),(54207,166),(58815,60),(49647,19),(51183,92),(54255,8),(55791,12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem b32 : t2 false q21 := s0 (m:=43903) w31
    (k0 (q:=1407) [10, 1, 2, 5, 1, 1, 2, 8] l23
      (m2 (g:=x383) (i:=4) rfl rfl (n0 y5 p7) p12 k9 (by decide +kernel))) (by decide +kernel)
def h13 := f0 q21 13 [(42879,0),(60287,4),(44991,47),(69615,93)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z19 : t2 false h13 := s0 (m:=42879) b32
    (k0 (q:=1407) [2, 1, 2, 4, 1, 1, 2, 8] l23
      (m2 (g:=x383) (i:=5) rfl rfl (n0 y5 p7) p12 k9 (by decide +kernel))) (by decide +kernel)
def l52 (i : Nat) : Nat:=(d0 [0x16ad2728c1ee6b1,0x6a4a0e629062082fff])
def k52 : w0 := (1,0,5,0,0,0,0,l52)
def m36 : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffffffff,0xfffffffffff8278ca9]),(d0 [255,0xffffffffffffffffff,0xfffffffffffe078829])),(0x8c5796,0x1884792),((d0 [255,0xffffffffffffffffff,0xfffffffffff819b865]),0x31b824),((d0 [255,0xffffffffffffffffff,0xfffffffffffe1200db]),(d0 [255,0xffffffffffffffffff,0xfffffffffffec400d9])),(0x4205b12,0x1385302),(0x140617c,0xf06154),(0x808260,0x6740060),(0x430380,0x70e0280),(0x303fc00,0x10b9c00)]
def n36 : List z2:=q7 38 (fun x => (m1 x 0 17,0,m1 x 17 17,0,m1 x 34 4)) 23 (d0 [860,0xb7ee440d54dfaa1035,0xb3ded810d60f7b0043,0x61eff0e80d75bfbaa0,0x35a6fed280d67bfb3a,0x358efec680d5ebfaf,0x203576feba80d5abfa,0xd20355efeae80d55bf,0xaaa0354efea680c00f,0xd80012c03dc0011c00,0x7f80403003fa0002c0,0xef800834037e0040d,0xf780043402fe0080])
def b35 : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def s40 : Nat → w0
  | 14 => k52
  | _ => j3
def t44 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : w1 := ⟨1535,14,fun j => m36[j]?.getD (0,0),n36,b35,s40,t44⟩
set_option maxHeartbeats 0 in
theorem t50 : q2 xd (j1 h13) = true := w2 3 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem f41 : z1 xd 14 0 1=true := by decide +kernel
theorem y43 : z1 xd 14 0 1=true := f41
theorem d41 : l4 xd 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 xd 0 0 0 = true)
  · exact (rfl : z1 xd 1 0 0 = true)
  · exact (rfl : z1 xd 2 0 0 = true)
  · exact (rfl : z1 xd 3 0 0 = true)
  · exact (rfl : z1 xd 4 0 0 = true)
  · exact (rfl : z1 xd 5 0 0 = true)
  · exact (rfl : z1 xd 6 0 0 = true)
  · exact (rfl : z1 xd 7 0 0 = true)
  · exact (rfl : z1 xd 8 0 0 = true)
  · exact (rfl : z1 xd 9 0 0 = true)
  · exact (rfl : z1 xd 10 0 0 = true)
  · exact (rfl : z1 xd 11 0 0 = true)
  · exact (rfl : z1 xd 12 0 0 = true)
  · exact (rfl : z1 xd 13 0 0 = true)
  · exact y43
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j52 : v0 false (q0 511) 14 (vars 511).toFinset := by
  have h : v0 false (q0 1535) 14 (vars 1535).toFinset :=
    n8 (g:=xd) (i:=0) rfl rfl (n0 h13 z19) t50 d41 (by decide +kernel)
  have e1 : q0 1535=q0 511 := by decide +kernel
  have e2 : vars 1535=vars 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
def w28 := f0 h13 15 [(511,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem b41 : t2 false w28 := s0 (m:=511) z19
    (q5 (hints:=13438558465) (by decide +kernel) j52) (by decide +kernel)
def r18 (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def m13 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< r18 i)
def d12 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< r18 i))
set_option maxHeartbeats 1000000 in
theorem y13 :
    (∀ i : Fin 9, bit (m13 i) q13 ≠ bit (d12 i) q13) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (m13 i) (inputs.getD j.val zero) =
      bit (d12 i) (inputs.getD j.val zero)) := by decide +kernel
abbrev g9 := Nat × Nat × Nat × List Nat
def d14 (rows : List g9) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base
def t13 (base : List (Nat × Nat)) (e : g9) :=
  (j1 base e.2.2.1 == e.2.1) && r19 e.1 e.2.2.1 e.2.2.2
theorem s20 {u base rows} (h : t2 u base)
    (cert : rows.all (t13 base) = true) : t2 u (d14 rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [t13,Bool.and_eq_true,beq_iff_eq] at hh
    exact q30 hh.2 (hh.1 ▸ n0 base h r.2.2.1)
  · exact h e hb
def p27 : List g9:=q7 30 (fun x => (m1 x 0 17,([5,9,8,12,13,11,7] : List Nat).getD (m1 x 17 3) 0,([94,91,478,127,251,95,255,3579,28143,18911,17405,4927,17343,17403,17151,9599,2239,1375,1343,11742,1725,6847,1119,1727,2751,2237,18814,2079,2367,2429,27127,7038,11453,48094,42679,42591,44927,42683,44799,46455,58335,58239,68863,42711,42751,42623,42879,58623,43479,58047,54143,43647,44925,44223,44733,64447,44221,64191,44155] : List Nat).getD (m1 x 20 6) 0,([[48,33,133,118],[81,130,118],[32,49,128,81,116,100],[80,16,33,50,116,131,100],[32,83,116],[16,82,131,100],[128,49,100],[48,129,82],[16,32,48,128,100,80,116],[128,81,32,49,100,116],[80,129,50,116]] : List (List Nat)).getD (m1 x 26 4) [])) 187 (d0 [0x228721fe8a6487bdb,0x5b21ee9eb487a9b852,0x1e62e6c7fb979b1fe7,0x699c3ff86130ffc9b1,0xc3fede130ff39af43f,0xc6a250fb96a9c37f92,0x870df73e143798a990,0xdbfad6c36f4778f97f,0x6b1baffa666ebfb284,0xbafe5a24ebeca84baf,0x79abcebdc0d93ad6c2,0x72e5be9a9b8fedf5ae,0x3bd4a9b8bfd6f6d9f7,0x99cb67b6a86d7fe5a9,0xb5fdea98d7ef3a635e,0xfce86d6ffaccb4fb4b,0x32d3be2b1b3ff9e66c,0xffd884b3ff1248cfef,0x4d0b3fb42c6cfdf289,0x33f38ae8cfbf08933d,0x7a332c7cf1ca31efca,0xa6c3fe9a1b0fde698c,0x3ef6c6b0fb9a86c3df,0x6a630dfcaf6c1fea9c,0xb07ad704c0fb1bdaf7,0xeca66bbfe8ba2efbe2,0xc6bbdf8b4aef3ca48b,0xbbf1b1abfecec6aff7,0x1af2bfc6a48afef189,0x2bdce612aef7aa9ab7,0xf5e86adfb8a9ab77c2,0x98adbf7a62b5fc286a,0xcff19caa6dc666a7fb,0x484a9fcd65ca7c7192,0x29efd634a77358929b,0x9ce12a6df079a47f99,0x8a7fee8259b7f8c766,0xdfd61d9b7ed6046de6,0xa4a9b6bcd8a6be714c,0x927f149649fb422125,0xfc604495b97991ff50,0xd643fe17c90ef94a63,0x7fe3358dff54c837ef,0x2510df994d637dfa56,0x8def64ba376f2628d7,0xb9de633fe83e0c7bd1,0xd231ed13e0c6fe90a3,0x1bd4728c6bc9bc31ac,0x1258b7f54882dbf168,0x8b6f990a25ee565097,0x9958a21e723987ff88,0xa61ff723207fbd57a1,0xfe793586ff995a1bee,0x13206dfe89619fe122,0x67be16419ce84a865,0xbc0d613fd82984fee0,0xd613f775684ef60c81,0x37f15104d6d1320df3,0x822036fc52a0d3f346,0x832fc8f809bf742826,0xf54f8097f73981ff68,0xd607f773581f7dcc80,0x7bf22e81ebdca606ff,0x725817ee07605f7625,0x8177c888057f11d813,0xfc86601fe611007e94,0x2201f9311007d50220,0x1f3a0c807b643201eb,0xa040079241001e2011,0x77544401d780c807,0x3e00001cc804007188,0x3201be215006f04000,0x1b870c805f54320177,0x515005cd4000171615,0x579810015a504005,0x4d04400fe008803dd0,0x3200ef3088037c8100,0xbc104002e40000097])
def pri := d14 p27 w28
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vpri : t2 false pri := by
  apply s20 b41
  apply r7 (d:=6)
  simp only [w5]
  repeat' apply And.intro
  all_goals decide +kernel
def l17 : List g9:=q7 26 (fun x => (m1 x 0 9,m1 x 9 4,m1 x 13 9,([[48,33,133,118],[32,83,116],[81,130,118],[32,49,128,81,116,100],[16,82,131,100],[128,49,100],[16,32,48,128,100,80,116],[128,81,32,49,100,116],[80,129,50,116]] : List (List Nat)).getD (m1 x 22 4) [])) 14 (d0 [8,0x2daf91cb6be262f2f3,0x18b6bc622f2ee0c7ab,0xa642f2dc54b6b5a42d,0xad4c3bd2f732daaf08,0xb6ab911eaab40bca97])
def spri := d14 l17 y8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem l53 : t2 true spri := by
  apply s20 g27
  apply r7 (d:=6)
  simp only [w5]
  repeat' apply And.intro
  all_goals decide +kernel
def moY : Array (Bits × Bits):=#[((d0 [255,0xffffffffffffff0247,0x102040c820c0830811]),(d0 [63,0x3f81ff800001f8000])),((d0 [255,0xffffffffffffff04c1,0x40881096109041223]),(d0 [255,0xffffffffffffffffc0,8658654101503])),((d0 [2184,0x245902104218288206]),0xfff800001ff81f8000),((d0 [4368,0x8902432803260844c]),(d0 [255,0xffffffffffffff0000,9007061947908607])),((d0 [770,0x182060608060410c08]),(d0 [65472,0xfc07e0001ff8007e00])),((d0 [40964,0x820208841484826190]),(d0 [255,0xffffffffffffff0000,137436889087])),((d0 [17440,0x410491010901141020]),0x7fff81fffff8000),((d0 [10248,0x20430a040604082080]),(d0 [65535,0x7ffffe000000000])),((d0 [53296,0xc38414021802104140]),(d0 [65535,0xfff800000000000000]))]
def moC : List z2:=q7 47 (fun x => (m1 x 0 17,([0,1,16,128,256,8,4,2,64,32] : List Nat).getD (m1 x 17 4) 0,m1 x 21 17,([0,50,16,64,18,128,138,276,32,69,258,136,8,384,130,36,256,4,1,68,272,9,2,104,20,48,96,385,129] : List Nat).getD (m1 x 38 5) 0,m1 x 43 4)) 387 (d0 [8796186083395,0x94a001e900a0a80016,0xb0010a50005c580114,0xa3009c3802154001cc,0x10019280038c400295,0x1806a1c002ad80031a,0x80601b8004e9008834,0x401c6a01106b007304,0x60cb00b0b00049c0,0xf30008638002ae00,0xa8700c6b0060a6e00,0xda800129c0bbc705d,0x1c38243d4120157000,0x7a80002ae057f882b8,0x39c001f10000740175,0x6e0bb488029b9c14e3,0x100715ec38c0a00ceb,0xd8678140002bc000a1,0x802bdcc15d190053b9,0x829a32001373009464,0x2e60008c80005e4,0x10d0000de00010e0,0xe35b371124015ab66,0xac24801256cc904900,0x9ad98489200015b00,0x124021bcc50c09803,0x67981b013005df302e,0x8260001e600004c814,0xdbe0a72090003bc002,0x2136725ec394024001,0x7d0004148002fc0008,0x1902a6dc150912072d,0xf03910640d3be06920,0xc80877c04241900b6f,0x8058832063e78318c2,0x40ebde07510c8003d6,92609011275989586,0x69f683484a4031ed0,0x18094821fe610e0c90,0x37cc018192000fc80,0x1a4049fc02401cc1,0x5d7b0ae02a533af619,0xc01606b5f835d02c00,0xcbf006a05800d7e007,0x40b02bcfc15d816024,0x9f812302c00d3f0066,0x5819ebe0cea0b02ed,0x7c175416024af81228,0x2c0a76f0534858026d,0xe01290b01b6bc0d8a1,0x6018d780c142c0e3bd,0x71215806f7a03642b,0x4ef4024856053f38,0x29862c025e70120c58,0x43ce02018b0437b82,0x18236061f703084701,0xcff0868060093be04,0x820c00df7c06c41803,0x4fb81a0230049fb024,0x260093fa04802c011,0xff408c058061ff0308,0x70091fe04800e0067,0xfc03201d033dfc19d0,0x1a090f784804100016,0x220046ad802c2c0098,0x50007888001ac400a6,0x802819c01616000c3,0x819dbc0cf21702bbcc,0x15e18fc002f480401c,0xaf630574e3814f8e0,0xa638700077000046e0,0x87f8843839c0ebf807,0x503c0181f60c104802,0xbaf615e0500215ec10,0xc0a0000bd000814021,0xf7210e468035f989ac,0x131b002f4800024000,0xdf000904818efc0c68,0x190006f8000832000e,0x78000c2402dde01610,0xcc57ab66bc209033fb,0x419c252053f9829832,0x40cffc06701cb177cc,0x4ba01a52baf615c016,0x71af838a82c0056f0,0x2485800af600484b0,0x1ebc00ca16000d780,0x142c11fe708f0c582,0x1bce10c18b007f9c03,0xc31600df700684700a,0xcff05680601d7be0ea,0x20c02b77c158418009,0xfb80482300e3fb0710,0x2600dbf606c04c004f,0xec024098056fe82b00,0xb0043fd021016005bf,0xa02c02d02bdfc15d01,0xa056bf82b2034001bf,0x206815fde0ae10d,0x67bc03021e000ff8,4503692019504053,0x802e2c008864007304,0x24fa004ba00021f2,0x1cc1000140001f600,0x10480392f61ca05000,0x7f00040600cf5e067,0x50c01d6b66ea248000,0x7d4000153260f31300,0x2240ebf9075034c1c9,0x7b0e402a5392f61c80,0x1607d5f83ed02c0a73,0xf05360580267e012c0,0xb03ad7c1d5416000b7,0x800242c06be70350c5,0x804bdc02411c010bfc,0x8601805def82e8830,0x10ffb087026021bfc1,0xc01d030dfc18500d9,0xa6080209f000e350,0x803821ff010e07800,0x156cc08490075f603a,0x84e00b5f505a05400d,0xbcc46c099043ff021c,0x7607dde83e90ac10f,0xe70870c5806bdc0341,0x1c0437dc218118056f,0xd82b01300ebfd07501,0x6804afe02480d010ef,0xc08481a018df80c103,0x40c3ef061086803fde,0x1e108043f98a1c130,0x1bf310d8262e00974,0x4d8017b0010090,0x778000432000f680,0x4a4001f300006554,0x3cc40000b0022fc01,0x28160049f802302c03,0x1bd0182158033dc018,0x11c038bfc1c601805a,0xef82d08300aff70570,0x46019ffa0ce02c01b7,0xf40d8058090ff04800,0x7410dbf086206805b7,0xe02c407a0038d40008,0xf300dc380006c0053f,0x2605821b7a10c42b,0x26f401085805d7f8,0x2ec0300e3df0711060,0x15ff60ae04c0037ec0,0x18098057fe82b80b40,0xf97f07c40681f77e0f,0xa40700035c00251005,0xead9af09200bbe625d,0x4cc803cc40008c01b,0x7dc0d8118087fe8438,0xb0037fd01b01601af,0xfc0d601d0097bc0482,0x8000f010003e0019e,0x620c04c8001ee00108,0x988056cc004130005e,0xc0000ac000bf000a05,0x8243dc12011c02efdc,0x17411800fff0078074,0x10f7f0874068036fe0,0x1a80d004dfc02501a0,0x63df8319034037ef01,0xb084016ab66b424940,0x56cc00092c00f3100,0x69e015b30000581a,0xfdc0d611b01ffb80fc,0x23a069bf834a0340eb,0xbf07520681af7e0d64,0xd0036fc01881a067f,0x78338418a005e90080,0xbb802e2c0008802a75,0xc150510000eb8000a2,0xa75b3531240012b6,0x60824c043fdc21c11a,0x5ddf82e901da005e9,0xc00017b0010296,0x367989b0036009bd80,0x4a12c11fee08f08e82,0x1f7e10e40d02efbc17,0x420eb00b8b0000a000,0x1fa00002d28017b000,0xd00c7bc060216056,0xbd82b213001bfe00d0,0xe8012fe00880d038e,0xfc1c481a056df82b10,0x24001fc00001d814ef,0x60a684d033efc19c81,0x900dc38000250b55b,0x35a0258012be008a0d,0x2befc15c81a06bf78,0x3584200c1e626004c0,0x63cc4300980397e81,0xc80b070071a800020c,0x1716000060087fc04,0x201d038dfc1c501005,0x45ec2a40b00d9f706c,0x468176fe0ba80d012,0x5fc091016057bd82ba,0x12c0cfee06708e000d,0xfe00700d0026fc0108,0x1a036f781b0418601b,0x870002e00dbfc06c01,0xc0067f803003a075bf,0x83aa0340b57f05a403,0x1402e2c000a7200730,0x400418003ef8018830,0x7f70030460093fc0,0x4801c001ff400c04c2,0x71a80412c0015f00,0x505806fdc03611c00,0xdff806c03a072df839,0x101860097400144000,0x2b66002470007e0000,0xfa086f7843042c0bb,0xee05d08b0803982002,0x2d03afbc1d42180727,0xf83940340abbf05520,0x58063dc03011c0013f,0xc00a01a06cf7836043,0x40c1ef0600840003cc,0x40009c00b7f8058030,0x6cf313602740c77f0,0x63406017bf60bc04c0,0x2eff817403a087f784,0x3842c001e70000c404,0x39820000b0025ec01,0x1096000bd800213400,0x7bf0032068002fe000,0x80d034efc1a4818002,0xfd8010130001fe0000,0xe000bee00408d0007,0xbc000218000fb80002,0x340bd7f05e4060003f,0x600004c00177c00841,0x8067ff033806c001bd,0x216818fde0c610d,0x15fc00901a069f78,0x34842c001ee00008e0,0x14fbe0a620c00077c0,0x418060ff03000700,0xa7fb053026021ffc10,0xe01d02afbc15421805,0x37f829c030001fd000,0x16014fee0a608c000,0x3fc00201a055bf82aa,0x300ebfe07500e814f,0x7e0a640d029dfc14d0,0x1a053f782984300a9f,0xd05401681537e0a840])
def moA : List (List Nat) := b35
def moD9 (j : Nat) : Nat:=(d0 [0x30a206102004e8a0,0xe8c6c0b2eb28da986d,0x9ada8efa1d3d389edf,0xd2bf251de8cb5cd425,0xc1206ddb62a531480c,0x954d524c120661814c,0x53048152605314c120])
def p54 (j : Nat) : Nat:=(if j<1 then (d0 [0xad8b0aad8b06ad,0x8aa6adc30aaacb30a6,0xcb2aa6cb0aa6c96aa6,0xc94aa5d302a1ab0299,0xc3029603028ebb926e,0xbb906ebb306eb9946e,0xb9926ed306683b8534,0x438b3212cb300b8b29,0x1b012502a524d34f20,0xd34320bb4f1cbb4b1d,0x4aa51cb35114bb4b10,0x1b83051309050aa705,0x7260fcbb52f8bb40f9,0x4260f80b90f4e302f4,0xb90f0ea60f00b90e8,0xb350e4b340e53b02e5,0x3260e4bb70e0bb6ae0,0xbb40e14260e00b90dc,0xc30adceb62d87b82d5,0xe994d26186d26b30ca,0xa2a6c92b02c48b8cc2,0xa392bea382bc9382be,0xa360bea342be8330be,0xa322bea300bea220be,0xa192bea174bea152bc,0x2196b98172b02390ad,0x538cad6b88ad7386ad,0x72a6ad7330a97192a9,0xbb6aa69330a6c2a4a5,0x2342a1b262a0fb429d,0x53309d92629d134299,0xa262983382951b4295,0x733095db0291f2a28c,0xbb708a0aa2880b8a84,0xb8a800b8080daa480,0xc2a67c0b8a78d2a678,0xb90740b8472a3066d,0xcb666ab34a6ab39266,0xb38666b36666b34666,0xb32666b30666b17464,0xbb6a600b8a5c5b8a58,0xe35054a36a500b8a4e,0x4b02480b8244a30244,0xc39640c3663c738639,0x636638cb70340b9032,0x23502c4b96284b9026,0x430424539020db461c,0x53861a2aa619e34616,0x52a615fb461272a612,0x1b460c73860a2b460a,0x3346067aa606439402,0x838a00299700ab6ee2,0x5b30a4119498038247,0xff8ffd3ff0ff6bfd8f,0xf4ffd2fbf3ef4f7f3d,0xd3f72fd5bf3ebcf6f3,0xd3cdbe7d79f3e7bf9e,0xbe76f9d7e6ef9afe67,0xf97fe5ef95fe3fb8fb,0xe1ff7fadfe37f6dfd3,0x7f2dfbb7e6defb7b6d,0x7fb5fcd7df5f6d7bb5,0xdbd6ff5bed6ef5b7d5,0xf7577d3fb3facfdb3e,0xecf7b3d7cefb1ffc7f,0xb1fdc7ef1f7c7bf1df,0xc6ff17fc4ff0ffbfda,0xfd3bedadfdb7daddba,0xffa9ffa7f69fba7de9,0xefa6fe7f69dea5fe8f,0xfa3ee87fe1fd2a5635,0x5602a542505606c8a,0x9505606c8a9605306c,0xda5245302cda466120,0x6d8a3661206e99564d,0x206dc93645206d8936,0x45206c553605206cca,0x9605202e9545c1205c,0xd425c1202e5a154d20,0x6d8a954d206c4a954d,0x202e5a54c5202e1a54,0xc5202e9944c5206dca,0x94c5206d8a94c5206d,0x4a94c5202e9984c120,0x2cd984c120661814c1,0x2054d814c120549814,0xc1206e5804c1202e55,0x34c12054d524c12066,0x1514c120609514c120,0x605514c1202e5514c1,0x206d5314c120605314,0xc1206c8a54c1206d89,0x54c1206d0954c1206c,0xc954c120661a724d20,0x69d9524d206999524d,0x206c8a960d102e9936,0x9106d4a9609106cca,0x9609106e9954c9106e,0x5a54c11054d5248110,0x6c9514811054951481,0x10659a2604306e9926,0x43068991604306c55,0x364420661a3604206e,0x9936042064da154c20,0x2e99854c20655a3608,0x106e995608106c9956,0x810651a3548106e99,0x3548106d593548106a,0x1935481068d9354810,0x68d92548106e582548,0x106a58254810661825,0x481065d82548106598,0x254810655825481065,0x1825481064d8254810]) else (d0 [0x3be919000000000,0,0,0,0,0,0,0,0,0x1c2305002fffec0,0x40580000000000000,2147266564,0xa52000000000000000,201359808,0,0,0,0,0,0,0,4294318356,0x8001ffc827bf200584,0xe0ffbc0c200ffc8060,0xf84dbc8c807710e10,0x2c029d632d006e3250,0x6181d0177035c0f361,0x415300380572c00037,0xf091a14989ae8940cc,0x114815b81a749f0d38,0x15ae10b841d133c21d,0x8b411015c03900d3c,0x101e40490113a0be8,0x1bc00d8dafb5b696d1,0xda1b3f676cdd99b2f6,0x56c9d91b1f636c5d89,0xb0f616c1d81aff5f6b,0xdd79aef5d6b9d71adf,0x5b6b5d69acf596b1d6,0x1abf576add59aaf556,0xa9d51a9f536a5d49a8,0xf516a1d41a7f4f69dd,0x39a6f4d699d31a5f4b,0x695d29a4f49691d21a,0x3f4768dd19a2f45689,0xd11a1f43685d09a083,0xd97a2f25e0bb9762ea,0x5d0b99722e25c0b516,0x92d059cb31652c858c,0xb11612c057caf15d2b,0x49652c2574ac9552a2,0x534a49452824f49c93,0x52624b494925242474,0x8c9152224348490520,0x23f47c8f51e23b4748,0xe51c23746c8d51a233,0x4648c51822f45c8b51,0x622b4548a51422744c,0x895122234448851021,0xf43c8750e21b434865,0xc217422c3204103c0,0x23b0f30f30f2cf303,0x1881930cf2a508f350,0xfd7b06fd5b22f99a20,0xf86392ec6b80ecf172,0xecf306ddc364cdd366,0xc9d172c89b82c2ab02,0xbd8972b6d364b29b04,0xb2d2a4b28972b18b90]))
def h54 (j : Nat) : Nat:=(d0 [0x6000005c00000,134217732,0x100000000000042800,0,598065675239424,0x2c0000080000000,0x7a03000000001])
def n54 (j : Nat) : Nat:=(if j<3 then (if j<1 then (d0 [342253605966720,0x4dc9bb864ca24aa651,0x51b2272ecb91186588,0x813743e71a21f3ad28,0xf1d6887813743829b1,0x1c2ccc0d026e860db2,0x62a09ba142cd40a022,0xe85043702425b31112,0xdc081c6a040b3301c5,0xd970e30cb071965438,0xd3281c65ba0a62d905,0x1b6e8201374106da30,0x838d1839765c14c32c,0xa69940536dd01026e,0x809836a046da80236d,0x1811c6a004e3460225,0xb90038d48029660016,0x32e00b9960062ca803,0x365001ab2600fd7480,0x2db3d016d9b22aa6c,0x1215227025d10002e8,0x13ffdffdffe7fefff5,0xff8ffbffdbfebff4ff,0x9ffbffddfeafef7f6f,0xfb5fd8febff4ffa5fb,0xffd7fdffefdf7afb57,0xcffdfddffeff77f7bf,0x7dfaefbf7dbbe7defe,0xf5f77fbb7dd7edff6e,0xfaffd7be7ff3fb9f7b,0xffdff6ff77f7bf7def,0xeeff6ffaffcffe7fb3,0xfb9fbcfbe7bf3bf9bf,0xcbfe3fefff7febfddf,0xeafef7f6bf75efef7d,0x5ffaff57f6bf75f7ad,0xfd5fe7ff3fe9fbc7fe,0x37f17f69573581655c,0x56058d71581715c160,0x58d70581655096058d,0x4158142505602a5415,0x819864530655914c19,0x2645306a5814c15260,0x5302a5814c1a824530,0x694914c1a224530660,0x914c19524530648914,0xc1a46612068598480a,0x366120661944819864,0xd2065d934819564d20,0x26193481986452064d,0x914815364520261914,0x8093645206a5844819,0x5611206a5814819860,0x52054d81480a960520,0x6898048131601206a1,0x74481985d12065d734,0x81935cd2061d734819,0x85c12064d70481845c,0x1205cd70481715c120,0x55170481535c120545,0x70481425c120505704,0x81a954d2068553481a,0x54d2065153480a954,0xd20695434819550d20,0x61143481a750520661,0x414819550520651414,0x81845052054d41481a,0x94c52069531481a04c,0x52065131480a94c520,0x6a130481a54c120689,0x30481a14c120661304,0x81954c120645304818,0x24c12060530481804c,0x12054d30481524c120,0x54530481314c1202a5,0x30480a84c120295304,0x80984c12025530481a,0x32612068498481a824,0xd2069c93481a624d20,0x69493481a124d20660,0x934819524d20254934,0x81a564d10689934419,0x864d1068d924419864,0x910655924419364910,0x6a583440a960d106a5,0x82441956091064d824,0x40a96091064d804413,0x1601106a5524419354,0x91060952440a954910,0x6a532441a54c910655,0x32440a94c910695304,0x41984c110601304415,0x34c1104c530441a848,0x11069520441a348110,0x66120441954811064d,0x20441854811060d204,0x41804811054d204415,0x248110545204415048,0x1104c120441a864430,0x6a5810c1a26043065d,0x810c19660430649810,0xc19160430685980815,0x3644206a581081a360,0x420661810819360420,0x6a553081a854c20685,0x530819854c2064d530,0x81a564c106a192041a,0x5648106a582041a360,0x810661820419760810,0x659820419560810651,0x820419360810649820,0x41a95481068d520419,0x754810651520419354,0x810649520418254810]) else (if j<2 then (d0 [0xaa4bd48b95e6e5,0xcaf522d57a914abd48,0x955e28dc2e946d570a,0x364b851b15c28dc2d9,0x46c96ca362b651b55a,0x28d9ad146c5693b42b,0x451b85928d9ac946c5,0x653b42b2ed98594898,0xac056cd5d3262ae818,0x15642cc2aa1655550b,0x2aa85515544cc2a22,0x6555112a2a87d98534,0x6a8a9856e1482b6aa4,0x7d98523ecaa9266054,0x932a2a47da85118dc2,0x81f6a140fb4aa07da8,0x4e3ed4269f69534fb5,0x967da54b18dc241f6,0xc91cfaa48c7db3453e,0xd2a29f68d14fb408a7,0xd95453ec9a29f6e910,0x6374887dba4318dd21,0x8c6d50cf9748631b54,0x23ed2a11f68508fb40,0x847d534218d9209f68,0xcfcfb407e7d933f3ed,0xd1f0c6e8f863707c7c,0xba3e72dc9eb96a4f5c,0xb267b29533d725c9e9,0xf6d4ecfb50767da53b,0x3edc9d056e4e8fb307,0x47cb93a3edd1c8c6e8,0xe46370727da8393edc,0x9b856e0dc2b626e7cb,0x93718da9b0c6c8d9eb,0x26b495335a4989ab7,0x6e4d1bb30691d52346,0xe5c9a116d4cdbb3066,0x15b3320adc18a76a0c,0x4fb30629da83018da9,0x7bb660b9db705a31b8,0x2d76da96bb6a0b4fb5,0x5aeda52d3ed296bb6,0x60b5db2a5aed852d28,0xdd16146e4b0a374565,0x1b92b76c99555548a8,0xa3745215ba2928dc94,0x8c6e4a4a370532d852,0x9a4c194d56e4a1cb72,0x5155b828aad994556a,0xa12b505155a328aac,0xc1439660a2ab2650e5,0x9328aac1944a54ca2b,0xb744f5db327aed193d,0x764c9ebb064f5cba27,0x4ed4133b66099db264,0xc51b5254ed412bb660,0x9692a64b55522518d9,0x121f6c88cfb44467db,0x9220ada912d6e8856b,0x4442bd52203edd0f8c,0x6e87c636a3e7da51f7,0x2d10fba69479d3443c,0xe9521e18d98e9f6e87,0x63743831b81c74d88,0xe1f6cc6cfb46367d53,0x1b3edc8d056d4695b4,0x632ad53193edd0c0c6,0xe860636a307da5186e,0xa98c1f6e05cfb622e7,0xda8173ed08b9f6e458,0xfb722a7d98154cc08a,0x9f6e850637428ada81,0x46ed409b76844dbb70,0x24ddb21272da88b96c,0xc45cb7020e5b31072d,0x4081f6a040fb6a1e7d,0xb30f3ed2879f68c3cf,0xb721c7d950e56d286a,0xb68c356b4a18b5a30c,0x5aa9862f6942d7b461,0x6c9ba0a3edd050c6e8,0x29936614e5b20a64d2,0x853268c29917414d1a,0x50968d184b454c25bb,0x741031ba086eda840c,0x6d421bb4a10dda3086,0xea984396d41dcb4a0e,0xe5a30772a9839f6cc1,0x8fb460c7db9050adc0,0x2b46a00da34606ddba,0x23edd010c6e809936,0xa04dda8023ed401376,0x8c09cb7002e5a80172,0xd180b96e401cb52009,0x5a30072c9804a54c00,0xc1536268a9b004d9d7,0x826cabc13755809b2a,0x906d9d3882ce883b6d,0x4009ba9c0cdbcb076d,0xa5813672008b98d085,0xd41c05ce026284fe61,0xb67a0edb3d026c5e81,0x172f208b976045cb78,0x22e9b4336ed861b66c,0xedb36026d5b0f174c,0xed8b36754cc318b6e5,0x8a32a6c02cb95f20da,0xaf50605789364b635b,0x6591eda2c906cd64bb,0x30aa6198542ed3a818,0x6994013749e61a64f0,0x4d923022e910117486,0x9b54204d9a1026ccf]) else (d0 [0xc34db2612ad93,0xd36c5869b04c34d81,0x61acdc30566cd82b36,0x2c1598160aca9b0564,0xc582b170c165b85fb2,0xd9afd96c97ecb04bf6,0x4985f50caac2854561,0x4362aca1985650caab,0x286055942a2aca1985,0x350c0a9bc60541e2a4,0x98f1534a78c1a4bc61,0x521e2a48ea1534578a,0x822bc4c115e37488f1,0xb34478d1a23c2e911e,0x34a86f1a14378d021b,0xc54905434480f1833f,0x50c19fbc4c0fde3747,0xcf1b83e78d41f3c684,0xf9e3407d59b93dacd9,0x9ed66c4f6b3607b59a,0x93dacd19ed6684f6b3,0x407b59933dac989ed6,0x4c0f6b1727af1853b5,0xdc9d286e0e9433074,0xf1ba3978dc1cbc6a0e,0x543046ea1813778a91,0xb59548d69b70694db2,0x34a6d89a53608d29b0,0x2694d8233a6a919d96,0x14c2cb0a5b65ba2cb2,0xdc96596ccb2cb74576,0x5b92bb2da95d9694ae,0xcb2a5765532ab2dd14,0xa86e8a6cb7252f1b92,0x9b2dc14956e0a6cb60,0x5365a82950d414d966,0xa5e3305364ba29b25,0xc94d66e0a2b36650f1,0x522378da8fbc6e871e,0x37038f1a81c78da8c3,0xc69461e3022ef1ba0a,0x78d9853c68c282b616,0xe7d98b77cb2da3e58e,0xd0736366f973b31cd8,0xd943596c0fae75e7da,0x2ab3e51559f2a6a923,0x674e7d98a746a95385,0x6d698fb314c7d95a63,0xed4529f6a290fb4b48,0x7da8a33ed2d19f68a8,0xcfb4f447da4a13ed1d,0x9f28e846363407da7,0xa018d8cf8c6e274fb5,0x13a7da19d18dacd8c6,0xc66cfb4b3631b99818,0xd9cb8c6e258636b2c7,0xd87953edd4a0c6c650,0xf975287da3933ec9c9,0x9f24e4d5b2724ac939,0x2185cc8856ce40fb27,0x207d30900ad9c7856c,0x63c29751c30b98e18d,0x8c62d64e2c637114b5,0x878a18d9c4146c6206,0x3631051b88728d8c3b,0xb6621e0aeb0e51b986,0x82c9c2c1612160b270,0x90584849ac241946e6,0x8a361052d548228dc,0x40d566202aaa70051b,0x37f9ac23fc15cdfda1,0x68fc7da97d185cbe9f,0x2a5f46372f87da97c3,0xe54be1f6a5ec736cf4,0x31b17a3ed4bd1f6e9e,0x6370f031b17868cab,0xb8c6ddd4f974ea7dba,0x7418dc3a1f2e9d1a32,0xae6d1957218dcb89f6,0xa1c1a168e07ca8703e,0x52b81f6e5bc2b72de7,0xda96f3ecc379f2e5bc,0x6172de7ca96f4ed437,0x27695ba9326dc9ca96,0xe4e543727295b8fb50,0xda31b86c3edab60c6d,0x5b0fb50d87da06c3ec,0x2b61f541b0f90ad8ec,0xb96b4e54b5a76a1a9d,0x972d4ed98694ed4342,0x7695a1db30d1495368,0xaaa9343b2e5a13950d,0x9ca56876d9b3bb6c5,0x9d3974ceecb567a459,0xb3bb661993974cced9,0x865a4a9b2d5549953b,0x42c8ed986428dd3194,0x6e58deb30c6f58263a,0x4a9b1d55498ca172c6,0x51b2627ac0b1524c58,0xa9372c231b961a4d93,0xd26c5869360c31d52,0x61a45cb0b72e586915,0x2c355ba604add30556,0xcd809b62c155b060aa,0xd4305566181cb30c13,0xd536094a9b0552e982,0xa952c154a860aa4c30,0x146e97ca372bf49b35,0xfaad92fbb6617e5b2a,0xbf5d815fa4a9afbb2e,0x57ca172bf49b95ea4d,0xaaf116d57a934abcdd,0x985ea4caaf516057a7]))) else (if j<5 then (if j<4 then (d0 [0xd65ad969659d96,0x5658d961657d95d656,0xd959655d955654d951,0x653d94d652d949651d,0x945650d94164fd93d6,0x4ed93964dd93564cd9,0x3164bd92d64ad92964,0x9d925648d921647d91,0xd646d919645d915644,0xd911643d90d642d909,0x641d905640d90163fd,0x8fd63ed8f963dd8f56,0x3cd8f163bd8ed63ad8,0xe9639d8e5638d8e163,0x7d8dd636d8d9635d8d,0x5634d8d1633d8cd632,0xd8c9631d8c5630d8c1,0x62fd8bd62ed8b962dd,0x8b562cd8b162bd8ad6,0x2ad8a9629d8a5628d8,0xa1627d89d626d89962,0x5d895624d891623d88,0xd622d889621d885620,0xd88161fd87d61ed879,0x61dd87561cd87161bd,0x86d61ad869619d8656,0x18d861617d85d616d8,0x59615d855614d85161,0x3d84d612d849611d84,0x5610d84160fd83d60e,0xd83960dd83560cd831,0x60bd82d60ad829609d,0x825608d821607d81d6,0x6d819605d815604d8,0x11603d80d602d80960,0x1d805600d8015ffd7f,0xd5fed7f95fdd7f55fc,0xd7f15fbd7ed5fad7e9,0x5f9d7e55f8d7e15f7d,0x7dd5f6d7d95f5d7d55,0xf4d7d15f3d7cd5f2d7,0xc95f1d7c55f0d7c15e,0xfd7bd5eed7b95edd7b,0x55ecd7b15ebd7ad5ea,0xd7a95e9d7a55e8d7a1,0x5e7d79d5e6d7995e5d,0x7955e4d7915e3d78d5,0xe2d7895e1d7855e0d7,0x815dfd77d5ded7795d,0xdd7755dcd7715dbd76,0xd5dad7695d9d7655d8,0xd7615d7d75d5d6d759,0x5d5d7555d4d7515d3d,0x74d5d2d7495d1d7455,0xd0d7415cfd73d5ced7,0x395cdd7355ccd7315c,0x7f7081bbe6d49afa6a,0xa1a5567819a2658993,0x764318ba61d98165f1,0x97625cc16f25abd664,0x58cd5e956755695499,0x4e3525544c503d3c44,0xde932c4b792a149792,0x2047791a5455d12643,0xbd0b141b90404034fc,0x43e1cf453c28ecd3a5,0x8e50384cdcc35e4d3d,0x33d4cab31d4c342fa4,0xbaa2d90b252ba8aa32,0x964a1f278c9ac25dc9,0x3d24188d4226486720,0xf87ff1f007871d1c6f,0xb1b08690195c612177,0x5a615c452d13e44b3,0x11b443f10103b00dec,0x3380bb02b60a102340,0x7f81b7055c118037c0,0xb201cc03e000143056,0xf1142b688aa5ac450a,0xd622e7653987b078c0,0xd73c54ab9e2435cf18,0x1ad7890d6bc616b1e3,0x358f150ab78d4d528,0x54aa143654ea152a75,0xdad32854a99e2a54a,0xf152a478c3cf3c6167,0x9e3073cf1819e78c1c,0xe3c60671e15138f151,0x9b78c1cd3c61665e30,0x732a1ba9878dccc3c6,0x6261e32730f0b99850,0xc3cabc4c651430726f,0x15093789849bc6e646,0xc36322a1a99178dcc7,0x156e238ab6b1d65b08,0xe78a8c54264e261309,0x13094189b2cc43596e,0x60acb6105659382b2c,0x2415954dfe7168fca1,0xa97d785cbe956c9f14,0x34ef8a1a27c50d0be3,0xc6a5ecab62f5399577,0x78c3babc2e1d2732ae,0x539877278dcb8bc655,0xc5e30ae0f1507078cc,0x37a864dbd4170dea0a,0x86fb2c2b73c6059ec9,0x70cd64a866b24c3359,0x6e98ecb72c765b563b,0x2d9b1d96c98ecb50c7,0x65a563b2d131d96618,0xecb2ac7658263b254b,0x1d92958ec92ac76582,0x62b2c0b1594c58a9b7]) else (d0 [6755957049481315,0x4b5a67040841c19b03,0x581e04120b211506f0,0x4200e00c957b18c985,0x45203482640b149f3,0x69029d0a4a2504c704,0xc2024a4f302014cc,0x5ca0d5197044c18e21,0x70ff085841a1151301,0x90e076060439839454,0xa2450bc23403c3137b,0xa81b610305c38cb8c8,0x77d1b70c780c03806,0x603700b3428307839a,0x44a05204260ac137c1,0xdc056022847a09d03e,0xff453c4cc02d05d85,0xe0e060770228a3440b,0xa01e7830078c11801,0xf8b9c4ba20d03a8220,0x6805cb0ad82360782c,0x1d686002ac06d0400,0xed815037c1d3051091,0x80700dc0bd415a0e01,0xc685740502bd004092,0x43022511d82b801d0,0xcf02b843811e0bf0be,0x813e2001f685345cc0,0x503500e4068c090160,0x15a819817e0e786f80,0x4055e02700f803a0bc,0xf687f425a06e09f00,0x35f9d7c75e9d7875d9,0xd7475c9d7075b9d6c7,0x5a9d687599d647589d,0x607579d5c7569d5875,0x59d547549d507539d4,0xc7529d487519d44750,0x9d4074f9d3c74e9d38,0x74d9d3474c9d3074b9,0xd2c74a9d287475d1b7,0x465d177423d06f413d,0x2f403cfef3f3cfaf3,0xe3cf6f3d3cf2f3c3ce,0xef3b3ceaf3a3ce6f39,0x3ce2f383cdef373cda,0xf363cd6f353cd2f343,0xccef333ccaf2f6cbbb,0x2e6cb7b2d6cb3b2c6c,0xafb2b6cabb2a6ca7b2,0x96ca3b286c9fb276c9,0xbb266c97b256c93b24,0x6c8fb236c8bb226c87,0xb216c83b206c7fb1f6,0xc7bb1e6c77b1d6c73b,0x1c6c6fb192c62b182c,0x5eb172c5ab162c56b1,0x52c52b142c4eb132c4,0xab122c46b112c42b10,0x2c3eb0f2c3ab0e2c36,0xb0d2c32b0c2c2eb0b2,0xc2ab0a2c26b092c22b,0x82c1eb072c1ab062c,0x16b052c12b042c0eb0,0x32c0ab022c06b012c0,0x2b002bfeaff2bfaafe,0x2bf6afd2bf2afc2bee,0xafb2beaafa2be6af92,0xbe2af82bdeaf72bdaa,0xf62bd6af52bd2af42b,0xceaf32bcaaf22bc6af,0x12bc2af02bbeaef2bb,0xaaee2bb6aed2bb2aec,0x2baeaeb2baaaea2ba6,0xae92ba2ae82b9eae72,0xb9aae62b96ae52b92a,0xdd0b722dc0b6e2db0b,0x6a2da0b662d90b622d,0x80b5e2d70b5a2d60b5,0x62d50b522d40b4e2d3,0xb4a2d20b462d10b42,0x2d00b3e2cf0b3a2ce0,0xb362cd0b322cc0b2e2,0xcb0b2a2ca0b262c90b,0x222c80b1e2c70b1a2c,0x60b162c50b122c40b0,0xe2c30b0a2c20b062c1,0xb022c00afe2bf0afa,0x2be0af62bd0af22bc0,0xaee2bb0aea2ba0ae62,0xb90ae22b80ade2b70a,0xda2b60ad62b50ad22b,0x40ace2adbab4eacbab,0xeabbaacea79a9c6a6,0x9a986a59a946a49a90,0x6a39a8c6a29a886a19,0xa846a09a8069f9a7c6,0x9e9a7869d9a7469c9a,0x7069b9a6c69a9a6869,0x99a646989a606979a5,0xc6969a586959a54694,0x9a506939a4c6929a48,0x6919a446909a4068f9,0xa3c68e9a3868d9a346,0x8c9a3068b9a2c68a9a,0x286899a246889a2068,0x79a1c6869a186859a0,0xaa7d99dfe7779dbe76,0x79d7e7579d3e7479cf,0xe7379cbe6f49bb26e4,0x9b726d49b326c49af2,0x6b49ab26a49a726949,0xa3268499f267499b26,0x649972654985a60e96])) else (if j<6 then (d0 [0x99f821d9fa046c,0x68900008fcdf90b0,0x602589153f02bb02c8,0x617f96ae0f011c7b10,0x4702ad1020a18d6a29,0xffb4c883c046c0478a,0xfe1c136f683104a35,0x43c2067c18404e219f,0xfc9901060c2041c4a3,0xf060df84b40800913e,0xffa61909c80c200bc5,0x16ffdf823830806f,0x1415fc2b5162053691,0x7e6fcfa24c20271000,0x5fae490101653835f3,0x39ffa623d10027a64,0xe8100587f7c0001bf9,0x7a610096280803ffe0,0x46cd27801594688e98,0xbc12344c025a7003,0x5f00baa097bb115e62,0x7be14b30baac6501e0,0x86f7c9c0c978000809,0xc48bf87db188105a1c,0xd7fe3d4204158827,0x9c33ac4082f1001737,0xd02041688020fe160,0x8094c01ff690ee320,0x813563fc9c2888105,0xa1c1cfffb963040812,0x44821f37c501048881,0x958beffe685190045,0x6837fdd60387081003,0x89000000005f053fcc,0xa241eff66f38548608,0xf82619e61e9b34d3f4,0x68e00a16d14428ae78,0x3ca0cd2d09d11cf073,0x140cb30f3444fbf988,0x157c0e7088e78382af,0x81cd10fcf06300a616,0xc8462279f8c02ab443,0x21e128a073f1b3ef01,0xaa1c801bf837e43a9a,0x6b885fad43c181,0xc54bbeae9adfc18bba,0xe09a8742ffec130946,0xce11fb0d0251b387c2,0xbf61a049c6813d6aab,0xf2d1200dbb91b3491f,0xd32d517589d5a71fe4,0xcac2f185e4457f2cb5,0xdd6299a113fe809979,0x8819a400f921e6244e,0xb08162b7f8bac85e4c,0xe9257f7733b3414eff,0x17590bc99d279f8f26,0x94e4404ad12cfeaf2d,0xc2c36f1cae8d240c,0x933f75d86220849aff,0xf812050022106a3ee5,0xf330a102ab7fc5a071,0x8020822275f8f17150,0x420889b87e3c2820,0xa73e1882501103b481,0x7ffff0ae06c501103b,0x66ffec2284941273d3,0xfb3025011483513fd3,0x808604002144c503ff,0xba2003190d3f1c485a,0x4324025eae9c044400,0x213ac58dff1301c4b0,0x922ff7602184e20962,0x24000000003fc3bfb7,0x970009bc00f100de0e,0xf0b440057f0e847175,0xa21f80c20150a6fcda,0x28881042200017fa6,0xdb970c2fcdf310000c,0x3c448c81c409a69484,0xf414b8aac4a603a432,0xc6c61d31c986324511,0xe929346509a8162060,0x870607c0d606116c88,0x191348da45d25a9094,0x92816c1520a8053c2d,0x401ae1d689b46614b0,0xa5052791a0e8007aa5,0x8c30af0e0582ec28c0,0xa2084c80652a14d94b,0x58dacb562db35da16c,0x2461a0671b0e89d84d,0x36a9bf42260b500b04,0x481c7a9396b589609b,0x633d278c282c205d01,0x1da4c6020b0d22ea1c,0xc6c84ed1ee80c2e015,0x6d57ca874a760fb135,0x92a9840df0b9051014,0x82ab5720b09961590,0x8f886817472b37c024,0x8e58e0f41185794e66,0xed074e3042ea114e04,0x846f0200ca06380630,0xcb00d83a917884690c,0x951120d8778a366ab2,0x282d943be11b08f019,0x442623d06287ec220a,0xff079880c6d08e12df,0x5e0dd07090b022d01,0xed07c32d8ca8b740b9,0xa806a0c4522a80d50,0xe614316a8f409c1430,0x4740061670a30a8855]) else (d0 [2271,0x904283c4000000abf9,0x39119a662980000000,0,0,0,0xcffd08b59234a0000,0,0,0,0,0x1dbcb1665b8800000,0,0,0,0,0,0,0,0,0,0,0,0,0xffe4d7eff2524,0x880000000000000000,0,0,0,0,0,0,0,0,46179355041344,0x694eb0116300000000,0x1e0f0a08946a870,0,0,0,0,0,0,0,23620534788,0x70a01d7e3fc3344962,0x26c0031ffabfc400,0x746100822c00000000,62455588,0xeac40ab40000000000,0,3931848,0x60c202710000013ff,0xfebe900c1840028b00,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6021161,0x164d068632a0000000,0x13ff57fb60290460,0xf7fc0005393f006,0xc531a00000000010f,0xf829f9e6940c91e000,0xaffd3830a8b668d1,0x60013ffa603601cfa2,0xb4500000055f900829,0x6054aa000000001eff,0xfc852172c4b0093c8a,0x5fdcf09c154574e009,0xe17c019806b4f6396b,0xc03710571953066200,0x23ffd96277022b1,0x4071f281c064006750,79096584189739,0x10f1a000bf829f1b7,0x930049140000000025,0xff07be19040c31cf7d,0x48d568e52cbff6a6a2,0x3bc650e0033db84bab,0x22240067e0fd7882,0xc022c4c7edc0c302d9]))))
def g54 (j : Nat) : Nat:=(if j<1 then (d0 [8068216350920704,0,139125455,0x80b68a000000000006,0xaccd2000100f80000,36,0x1400060be000609e00,0,0,0x214a00044940000000,0x607603580000000,0x641200040660,26134708224,291,0xd000041b8001021000,101736448,0,0,0x168057800000000008,0x3f0000000000120260,0x500000000000000000,0,618530,0xa4a602d000000040b8,0x44800000021400002,0xe4000000184100000,1586304,0x168000000000000,4536584976203776,0x18068001b2ea15a000,73570522074316800,0,0x817800000020040,1240901103398,0xa20000000000000083,0x880000000000000000,0x520001a398000150,0x813800000a800040f6,0,0,872576,0x34000000000000010c,0x1800000000010250eb,0x8000000000062cc000,5033701670912,0,9,0x4fc122000009000000,0x1a3be03c000000000,0x20298330000000000,0x100940018230000000,16738,0,2151153668,0xad8000000000000000,0x60f2000000180,0x892b40000000000204,0xa00020d80000000000,0x407400280000000000,4152,0x848000025581660,0x2143009a0a000000,0x3ac8000000000000,0,0x32b80000000000,140050640,0xc0800c00da0000,0xcd68001846c01c8,0x1c8002000000000000,0,0x4f5c0000000000000,0,0,20021688,0x103eeebc82380000,25952256000,59904,0xb7019000000048b,0x600000000000000000,0,0,0x614400041460,0,2129408,414195908608,0,272826368,6,0xbb829331aa5680000,0,3183616,0,0x1843800023c0000000,0,4,0xaa000000000000000,25840587008,19516335591424,0x95e00000f8000000,2058,0x800000000000000000,0x85860a200000000004,0x2e000000000000000,1055232,0x8058000baa60ee00,0,0x82200000000000000,28991054434,0,0x2c8000a46a0628,0x4f8000849800000000,4673329430721,0x2288180091c125021a,0x8803120000b00a200]) else (d0 [0x401f853000084,0xd8000000604c000000,983040,405177396,555661787136,0x1840000000000000,8678014976,0,581,0x200060400000056811,0x800131200000050000,0x94e00000000000,0x104b603600000000,19584,0x4f49847c10800,0,0x800000000000000000,864237077397504,542638080,71476845740032,0x84b800000000,0xc6e030c15600,60429,0xe00028a800000018b0,0x80000538001bd40000,0,0,0,2176000,0x40e60000000000000,2117,0x800091600000000000,0,0xfe000000000000000,0xe0000000000000000,0,0,0x224000080c8000000,72831650223882240,1628438528,0x1998800000000012,0x520000398800000000,129,0xe800010e8432000000,34340864,0x22f800000000000000,0,0,8753512448,2153472,305114485338112,1171049676800,0,8884139851782,0xc6000000000000015,0xad000000000ce00060,0x7c0000000000205c00,0,0,0x24d84a01540000000,70914,0xe800041520000001a,0x30206a000000000040,0x980000000000401800,370538774004749,0x400000000000000000,0x2f5a832a11584f0020,0x144e2c890dce95042a,0x800b2e124020a69f0,0x4ec04000000000000,0x185ae092000000000,4506898172471296,0x64380000f4a000,136937472,0x854000104ee0e00000,0x22200f400000000,0,562036736,413944537088]))
def m54 (j : Nat) : Nat:=(if j<3 then (if j<1 then (d0 [0xd308fe9547f4cc,0x3da54ded352ee9a177,0x4d03ba651dd2e8ee8a,0x9774cc39a655cd330d,0xe9956f4c3b7a5cdbd2,0xa6de9a96b4d2b5a681,0xad32ad69946b4aa35a,0x2a5ad14ad68956b4d2,0xb3a6859d330ce99567,0x4c133a6059d2a6ce95,0x267498b3a6617d32ab,0xe9a85b4d2ada6896d3,0x30b69a8574d2aba68d,0x5d330ae995574c9aba,0x60d5d352a69a94f4d2,0xa7a68d3d3429e9a04f,0x4caa7a64d3d2a69e8a,0x94f4d125a64d2d2a69,0x69524b498a5a6a51d3,0x468e9a0474c9a3a60d,0x1d34486993434c121a,0x6a4fd34a7e9953f4c2,0x9fa694ed330769823b,0x4c09da548ed3506e9a,0x5374cc1ba64cdd2a66,0xe9a22b4a915a68c6d2,0xa6369a8174d08ba694,0x1d3460e953074d1803,0x69706b317c187be4b2,0xdf258ef82e374963ba,0x4b2d9258eb9a855b59,0x8a9acad4d64aa6b534,0x8da8a06d2d0368a86b,0x3143595a1ac950d692,0x76b433b4a39dacc4cd,0x66256b2f2b59595a4c,0x4ad66246b272349891,0xa49c836a636b2b1b5a,0x9886d4c4e662219531,0xda2846d440d66201b,0x52fc1977dac9bf061d,0xf82e8fe59879acc3d9,0x64decb08f41737a0b8,0xbd9551ecaa6f65517b,0x2a0bcd6a5d6952e8da,0x571acc38d655c9b08e,0xda76dacc36d655b9b,0x28dcd846dad4b43695,0xacb40d359469a54b59,0x6a19cb4ace5a2672d0,0xb3966196b30ce59567,0x2c8b396099cb02ce58,0x66aa9b375499caa2c,0xd53167254b392a19c9,0x4ace4986724ab2368d,0x81b42c0da85c6d2ae3,0x68576b30bb5955da4a,0xaed6a166b4ab35a259,0xacc2cd6a156b46ab59,0x855acaaad64d56b52a,0x35a94c6d4a6d65536b,0x269b4a94dac9a4d6a5,0x11b528b59346ec122d,0x6a4f1b4a7b5953c6d2,0x9cd660ecb00755533a,0xa989d96a0d1b506e5a,0x5346d29b968cdcb306,0xb598372ca9b964cd6b,0x266e585372c19b9600,0xdcaa66dd52372a81b9,0x4c0d6b505b5a9286d1,0x14d648a6b424b5a521,0xad40ed54c76b5230da,0x319ac98cd6a451b502,0x8da115acc0ad69436b,0x50135a509ad482368c,0x16b2a0b59305ad4803,0x68c06b2605d82000d4,0xe0565ef8b09681a9b2,0x2b25602a6b0153481a,0x98c054c406a610352f,0x95977debabcf5d1e7a,0xe6f3d717aca13c02a5,0xd4328d80a9698cc334,0x54d9b2a4cd131642d3,0xae269970352a00a950,0xd4a602a530152881a,0x93c0549ec64cdb2a46,0xe15134cd11806a4a2b,0x2e51996296c89406a4,0x62330301a9152c98a5,0x68c44b4a1a9a8094d2,0x8406a4123300959704,0xccb027654143280a59,0x3054c90206a402b2e0,0x2194012c980a6480ff,0xfffeffcffbffaff7ff,0x6feffbffaff7ff7eef,0xfdffdfedfddfbdf7de,0xfddfdbfd7fcffbffbb,0xfb7f9ff5cd605c5605,0xc16059160509605056,0x64530605302453066,0x1206512064d2064520,0x6112060520601205d1,0x205cd205c12054d205,0xd20505204c5204c12,0x2612024d2064d1064,0x91060d106091060110,0x54910541104c9104c1,0x104811065830644306,0x4306602064c206442,0x6042054c2065c1064,0xc10648106081054810]) else (if j<2 then (d0 [8165190436797532,0xc4281508341160905e,0xa25246a45614632208,0xc4b43008f817409c09,0xa2d21924f069c18a1f,0x49044a2605882b80a,0xa07a09a2ec0b83b21a,0x59c31c2f039c06c0d,0xc1703e40a05d808415,0x41604340842802c401,0x80c034e2003881e40e,0x37c1d410c2182780e,0xe1bc1ca2980581640c,0xa12a19811a14c08a0b,0x60f405c13c0a60702a,0xc10a0680d024801c02,0xc01c03c04c00ad375a,0x4eb45d683acf759ceb,0x35d663acb7594eb25d,0x643ac7758ceb15d623,0xac37584eadf55b6ab5,0xd569aacf5596ab1d56,0x1aabf5576aadd559aa,0xaf5556aa9d551aa9f5,0x536aa5d549aa8f5516,0xaa1d5316a5ed4b5a95,0xb5296a4ed495a91b50,0xeea19d42ba847506e9,0xc65384a6f94dd29b65,0x364a6b94bbe941522a,0xa35d44ca862508da10,0xb41f683ad06da0cb41,0x767e5cfc39f013de27,0xb84f689ec13d627a84,0xf489e813ce27984f28,0x9e413c62750ce999d2,0x33a26740ce799ce339,0xa6730ce599ca339267,0x20ce399c6338a6710c,0xe199c233826700cdf9,0x9be337a66f0cdd99ba,0x337266e0cdb99a7734,0xce695cd239a37344e6,0x85cd0399f733ce675c,0xce399b7334e665ccc3,0x997732ce655cca3993,0x7324e60ecc15981b30,0x165fecbf597db2f965,0xeecbd5979b2cfe5684,0xa2d93692472433c7b0,0x8e011aa230cc5bd8ac,0x313c624c444e87f50e,0xc21b3c3148571090e0,0xf0c18a82670322026b,0xffa7f6afda9f91bee6,0x7d50f8c9ee4bd7f7a7,0x8f40de62bc627814ef,0x15dab3af57516e89dc,0xee397c7258e309c15b,0x7af6ea6db1db2db5e9,0x6a96d37da47b432679,0x4cda198332a86478c7,0x158b7b10f6172c1b98,0x132fb35eb8bc2d762a,0xe6f5c56b7616bc2d2d,0x59beb1e560f2baf56b,0xaabe1557aa6253eaa6,0xdd4b6291c518ca17d4,0xe27b24e909be13632,0x6764c7897f92dea572,0x4a6893fd266249948d,0xa90ed1f8a3a746d28c,0x5115f22744468879d0,0xcea14041f482a50269,0xfeb3f387ce4f641e63,0x3bd076d4ebf9d533a0,0xe7354e511c63386e70,0x14dde1b65361c6a88d,0x389a1f3370659cc8c9,0x8d1311460c8bee9796,0x2e965bb0b5696582be,0xe56d0ab8952f29ae52,0x24a2513fe27904de89,0x8d92e3252e49248f51,0x1942288442084e1048,0x20183e4c7a20ed71d0,0x438dc6ec8d8e1a5433,0x446378c1316fa2c405,0x670a84148a28004df8,0x99b1266239444d0863,0x10641fec3e1077a0e7,0xa1c4036786a80cd418,0x882e4059a0aa4143c2,0x660491089c106c1e90,0x38e06a60c741738293,0x4ba08240e7019b029,0x804400678094007800,0x34d4e1a6970d3097e,0x942bf4c3d9a5cebd35,0x1569a5ab4d155a662a,0xd32b56992ab45455a2,0x96ad145569a9a74d05,0x3a64a9d2a54e8a9a74,0x4953a6927d3473e9a1,0x9f451cfa6626d3512e,0x9a7974d2cba6865d33,0x12e997974cacba61e5,0xd1512e8a59744c4ba6,0xa24d34726998934c9c,0x9a54e4d3311e9878f4,0xd4c5a68e2d34116998,0x8b4c9c5a54e2d12716,0x9a2874d0c3a60a1d26,0x30e998834cc3fa64df]) else (d0 [0x27f317c0c4100a,0x442dfdd0d2280dffe2,0xd584088135eea40164,0x70197f03001883e0a6,0xf524fffd90cf102008,0xa279f64531004b43e,0xff3ea88241239fce44,0x1004b4381fef488002,0x1698dffbb420882008,0xa249ffab1104012d0,0xf3fc4820a24817ffd2,0x1801004fc45f999882,0x27038005ed9d96b29c,0x1eab0e002db6650e28,0x7be0e717b2cf593,0x518b440cf5932e141e,0xab0e000e36650e2b3f,0x9dbe68466caa3567f3,0xb7cd08cd9456a260d1,0x536fcd30e0d1053ee,0xce77212279e0b5bbac,0x5431bff5a3f7006569,0x86241ffe1c220195a3,0xa22bf1f1c81aab8b42,0xc42c7b42eac92b10b1,0xed0bab2493f07bff76,0x804a16e3a452c42c7b,0x42eac926ff1fffc04a,0x67034ad159f0050b7,0x5619a442f4744983a,0x4bdff48802418e01a4,0x5a9133ef1a3217404a,0x3aff302b8639553b4,0x332d85a150869b7fff,0xc0ce6940c301a3a8b1,0x33ae7a3217044a8702,0x7043823842cc0f16d1,0x7c16fc20a201768b04,0xf04ac14517433cacfc,0x8606810b33a181c7c1,0x554b348c5420d845b0,0xa42ef2872644a446c4,0xa948647242147d4a81,0x3eaef0b28c488c49c4,0x7b1370ffa8513686da,0xeb90b22e25a28508c0,0x6d07fc7b218c1a0ada,0xb1a96aab65a66b6850,0xb917717f68964667e6,0x2963d61946011c6d36,0x7369715717941a11fa,0xd621b1671662c344d1,0x6533820330a6bc160a,0x4f17e33b0cb3016933,0x3917a1784201718f52,0xb2af17d8828fa3320,0xdf3314c217b0de1801,0x1616e2514526ae03b6,0xa26f86d210d20a2d32,0x900a000da731144611,0x1b8751069059068650,0x4808a0085288545585,0x6bc48c5114844284c1,0x82c2b4b715dc05c0e9,0x3485b80087b82126b8,0x42eba9d08d69dc8d1,0x6911311272d27e62e0,0x4e1091470200111642,0xd51532fd4d045c10c8,0xb316344843b4404658,0xcb6202fc8a4c7247c4,0x624310c644bc6c2452,0x228aa41f8944686180,0xc8a9511e46e8801202,0xda61b0e81212812c03,0x20e111911811daaf2,0xa1aa1abc2360b041b0,0xcd64a2fb0c9a1b81a8,0x2c4f44f30e941d8091,0x174f18400400650542,0xa283f11143f0e244c0,0xdd110c15c47c63c62c,0x7d22d0b8a7aa6b0e3a,0xae01b10f4806c31000,0x800c40918c10ca8514,0x948a3c1e42f82f46d0,0xb70a7a88c5f45f4634,0x3ac5b2962ab2012952,0xb181d84d0ce60243c4,0x352882d78660b4a930,0xe703040760b8184d14,0x9f86e83c49e0278480,0xe502b0b5441c220790,0xe405506a267a670b6a,0x4a06606e25324a4660,0x188ac0c7075081841a,0x22c1f0a5400209a890,0x9aa7e2c50822ad4a00,0xba22540da188610a6c,0x3a0bb23d060a8709b2,0x2600700f01a0908108,0x7f08e427c2342241c2,0x661a84ea3244ec070,0x1600c00500e830c110,0x760560712020992328,0x2262663604d6250740,0x98a1a297061423c64c,0x41842417077a0f0848,0x60a0206f40f0788472,0x12a33a5a62d03c0352,0x73052070451c4cc3fa,0x5083541805720f0922,0x7a36a46229250a536,0x33612a3da030098280]))) else (if j<4 then (d0 [0x7219fe1f007f08,0xbb477f7fde5f08284,0x286acbd5dce06080e,0x38068a9006ff8ec55d,0x8e204021aa81efe4f0,0x3bea90c0cd1e4049c6,0x85f80139fd76148a7a,0x7fff240b56da0601f7,0x52017238dfd5ff86e9,0x594189335c80bc8e43,0xfc1ab202c9804071a9,0xead39ed40d59e2f47c,0x49415555401cea5193,0xf01ac183187dff14f3,0xf1208092b7be9789ea,0x9044e96efe1f0d2104,0x20080a2b7fc53cfc48,0x2024abff7ef0111015,0x5f9fe6022022adff50,0x104a0937e660444a5,0x27fff30111294abfe3,0xf6b788100405129fff,0xf56bcf410103356fef,0xf3ea090440954f87bf,0xfa935220802108b47f,0xdffd328c88820089e2,0xc001ee87f43080085a,0x8dec79627c482a24c1,0x64fee37c4384010b45,0x7ffeff3100440442d,0x4f71bcaf3069881020,0x22aabf51fd20f3020,0x822248fd6dbea0840,0x40045153efff37fbfe,0x7510410054317afe9e,0x847ffc10941040115c,0x617ffefc7483a22020,0x26bc7ffffe410a0468,0x82100405180f7ecf37,0x8048fba41431080224,0x8ff7fff1f1ee43848b,0x384011446821f829e0,0x87ae9fb02404122008,0x4991dff50010446927,0xfe7ef01111955f9981,0x1099497ffa36440001,0x109b61fffcc044465,0x3bfea00208152771f1,0x5d4004110265f99811,0x12949fffcc0444a535,0xffb2742000202526b4,0xbffbc1349040040044,0x75487ff292b8208008,0x8e6a814f07800057,0xfc42000020088e3ef8,0xff9c4446525fffff42,0x364601010bb6025e2f,0x5fe4a0000080237,0x8e00affff3a1000101,0x11b673a3c13cd4c370,0x633115deb0f5805b76,0xe686d4025fc8b72f56,0xe49aa1deafeb30e014,0x65b66522309ffb4353,0x3e404641b2117e7f0a,0x449742b0caa15f97b,0x435738a06b3c4c3f97,0xa3f550879f0520d608,0xccfe7e6f346264ad27,0x7382cafdd484832427,0xaa77eef02bfc9dc641,0xc6e2dc67054414dbb,0x9dc83893391e890556,0x7e695087245d4d45df,0x99d401de8fa8749bb5,0x9cee42c613fa93ad1f,0x209128b11404dff010,0x629a369dde8f93f888,0x6568622660858f617,0x754963e4d64b5d27aa,0x68dea5dff2d5fc7f01,0x2819c0d43460f10b1f,0x449b02483fe0671172,0x180d20454bff35e257,0xdd3b41314affff1f0,0x3058d2b4c0685a3002,0xffe7eff12ada1da688,0xa01116fcdf9099c6d4,0x58a5bd8f7d6292e9a6,937884796,0xd93cb508e37bb46268,0x30e7f08d678b33e17a,0x1ce6948a637e4f050d,0xc70030c1aa759011a2,0x6c8d27afcbd020113e,0x9266b6ffaf00f6c32f,0x66afd20ca005b80000,0x9d0dee164e4c901ea8,0x9fe6fa7a84184001c4,0x811fe36d9e51b89009,0x16b1baffe546200af,0x20212240aff5f013a6,0x36d2e32024a37dfc0,0xe8093652d81900e518,0x15ebfe014b403b43d,0xa001b7eb8018fe14c4,0x2e342901946857ff84,0x7ff0f000cc00b0000e,0x877f6c20026ee0023f,0xfc44007bcc5e835520,0x328f0be078358f2008,0xa9f9f003f4e3671001,0x889b7ece8009040071,0xff2cce0620802489]) else (if j<5 then (d0 [0xe20022f3725ec4,0x4a491013ff8000020d,0xf1000ae2013e6d025e,0xc44e59500006ffe000,0x5aa749ad2c1e1495c,0xe0858006db409c4e00,385859584,0x1be28725d2f07a5c0a,0xeb42519c000000000c,0xffe9c10821e9a6a002,0xad9cae43c426539bdb,0xe77b330a506c67aa42,0xaa0000000008fffeea,0xd9ed349b2733350107,0x29cffa33ca2e6212ca,0x7cc519cffa73c1c86,0x212ca46cc7198ffffc,0x5f0fb218842098c9ac,0xf51d27ff8189810c10,0x140136aa00000b7d5f,0xb29d102264fe000000,0x17e62950c2a4000025,0xf77eca744089dbf4f4,0x99e7314a9e54025f66,0x9c3fa8c4a74248a034,0xfcbf36fb94308a5484,0xab000024fe47c2a90e,0x9951060805157d9e24,0x1f0a5a3594760e0013,0x5937f97b380a534304,0x24aab1fca4dccb242,0x21840594628df013fc,0xb2e529015338808c8f,1511601823591,0xe836971013120afabd,0xb420d64ce2026a2dcf,0xa0ccafbd880274fd84,0x9b39ff1daa01d5ac93,0x6efc563b5404bb59ad,0xb6578a0000718024fb,0x44580019c687e9fa45,0x2105b8c804de270807,0x964414fffe53766eec,0xef60e100711ba7fe90,0x9d46191012d4161fc5,0x53d9180046a6fc2bc7,0x230173449ff0675d99,0x2274d0f9199be9e008,0x340c4202523a5ffba9,0x1488c9c9a29a8a2d0f,0x14fe8e7183334e0ff,0xfe68fc550aded01201,0x20316381fcf1db2085,0x2d2d81901a51c00000,0xc7fad825319100804,0xc56957ce7f00a5a01d,0xa1ef2002380006ffcd,0xb100c80328906bf0f1,0x64b89ef744280a88d0,0xfd3a7ff00122440596,0xb57f8b92782b95f842,0xce2027a3d9ff0ffc4,0x10000c800280000781,0xef641000acb33fd5fc,0x7c35654b0354b31462,0x401248e3ff7370e551,0xc6c189009c68008ffc,0x6bedeb103120009013,0xee090008ca2be0b600,0x1bd802837712a40044,0x78000b7fff80350530,0x55f8d500b71e003bff,0x1e4c78f02013200120,0x5196cdb3812acc001,0x6fe087bf2eec13f1e6,0x403cc771e4f38d02c6,0x47c02bd483dfc1e006,0x40d5c582015e331fc8,0xfffa45b3b59058202,0x5e340017c1cdea8b67,0x707080658d03ae376c,0x62ba11115c4019eb3a,0xdfd376c934e0bb7d80,0xb36ed7f07dd77d00ab,0x36bea2100d28e05bff,0xc001228ecddd9c0e49,0x201d1214f039a59318,0x9f3680414602da3a7a,0x59333e6954800a4683,0xde0fa1936dcfe20009,0x179fa53a36be41600d,0x9adeffd6f22e9c2007,0xaa0000029fc1af03be,0x4f30b2cd05d4780065,0xd085f690cc98007aa9,0x7ffcc2ceca818e01a4,0x50bf0b3b2a82380691,0x31ffffccefcd583270,0x22b6774c74dd832702,0x3b5cbff91aa80c0120,0x80378b87ff77f11201,0x81812080038d2ffbf8,0xcadd709c068d55fdff,0xead81832703cb5e3fd,0xbc12ffdf6e95424100,0x6d1b9763e34be80b80,0x30e00eaac02ff87901,0xe00001ff7088401247,0x175cb8e0a0c19d0806,0xedce07fff571047180,0xc720809d8e67ffa044,0xaa08e0324487e5f286,0x40018f82a5ac14f03b,0x13dfd43c954241000]) else (d0 [6734424715413,0x44aa40000000000000,0,3908221,0xcbf2c2100ecd400000,30064221551,0x98b308010458000000,0xdfffc9278bff824,0x8110248018d0500699,0x300000000000047f18,0x6f655b6d759388e0,0x7d483aef17f42580a3,0xc86041d200823c1e0e,0x2a76ec09254829233,0xdffffb7aaca4b0328e,0xd39c42001e411ffff,0xc50979cea0c08e1ccc,0x4202d643de2843078e,0xa644021196406f909,0x3b6c96570590e00000,100655157,0x5a7e307eab1f1a1004,0x200134a001bffedab1,0x6a006880000000000,239,0xfff3e39c0fcee13780,0x89150112e400000000,0,0,35,0xfff8386267fe8f1012,0x4a0105c8000000000,0,447,0xfb75fe32842460c000,0x40109122000000000,0,0x1dffc5efed5880efd,0xe6f800a5c98000147f,0xcc0c2040c696a2e8a3,0xae013ff814007a582d,0x35a583c217b36001c6,0x9040d30000010f880c]))))
def f54 (j : Nat) : Nat:=(if j<2 then (if j<1 then (d0 [0x4cc2da88830172,0x831e002d02b281d382,0x2485b0ad35c11a443b,0xc1bfc2fa80de2ec2c2,0xc98298826ceabb815c,0x24ccc4e88e80d2582,0xb9083602635225c116,0x851d01b41c4d0577c0,0x5ec2a199d0014381e9,0x5c4fddfa8176a60883,0x1c82f8057841ff805a,0x122429d08f00160c2,0xc0400bc4e390f742ef,0x8016c1860729c19dc0,0x1ac0ce801800a0c266,0x810c8333914e99fac0,0x3e42b61da642e1c86a,0x992e402ec11fd1af41,0x3ec2c6c86f00f4031f,0x412f42930000000082,0x1d001c826f0000d9e8,0x81ac10ee8d94c934a9,0x30000000000008076,0x42c39e690000c0,0x9842614180d1ff0000,0x49940000ae81df,0x601e6000042320000,0x81a9c2010950821300,0xae424e919741bc1170,0x81ad902bc274c3,0x142f409f00000c147,0x20e2532813a000001,0xe91a48316000059dd,0x403b81a1c1dd40f018,0x4d1f0ae9592160d93,0xc107018a81c8009dc0,0x3100004abb0090504e,0xc50b4008c59b9db981,0x2e0b25086c1a1a0005,0x1a5d5048000000ebc1,0x7321e8850140ed9f2b,0x8525c0d1c899904a4d,0x981a6806841460000,0xc26742f240d4000080,0x860515117108419153,831707165440,0x325000000110000,0xc2dfea0caaea66c142,0xf642530000000042ee,0x84fc893b00b3408ec1,0x330000c89642880152,0x8ebbd0ea000000006e,0x1300005172cd372226,0x401400001038494825,0xf800000000492504e1,0x42e00000000045,0x38461b0300c0f71918,0x31500b601de02cd52,0xe4414e5f0f00c34105,0x4132c1b2d0605cd784,0xd3c280d93002308038,0x1c91e4a0000000001,0x5400c8000002dba305,0x921f017f0a00405282,0xd5d0500000ae8c9100,0xc11182e2000002fd00,0x37c2fe480dc1350000,0xd808fd130b0000c8,0x1ecde3c007d02d8268,0x8089804f000046,0x37427d00a7c318c167,0x81af000000000000c0,0xe0019a863a42dec0bb,0xc144c24f405b000049,0x7526d52c3823c2e06,0x9002302010a881c05,0x4a2502014110031026,0x12e0b453e27770403,0x3e0011803e07000209,0x10004f1c273a16170f,0x6b0100090104001d1b,0xb0c12230513002001,0x2e1b0812000a100103,0x5c4d0d070e0013043b,0x32e1e200739100200,0x800051a3147000e,0xb2501000101020105,0x803112300100a02,0x52202100217241a0f,0x909180001020046,6764300392033845,0x3a250c152207430003,0x1403141219020028,0x5101708000f0802,0x20001e43090a1e0e1a,0x90a0f1006013f0601,0xb10390e3f00091e,0x61901020613030023,0x7000507002a0f0900,0xb03010a1d0b0d6009,0x4090520300e1e17,0xc670409030b141707,0x30b01261c000d2a06,0x110331050702050410,0x1a0d0f040300380b01,0xd0206131813010304,0x505050e1805030017,0xa00190806130d0829,0x41a4e01010009063e,0x219220038001e0b03,0x2d01051502200101,0x50001040024030211,0x500010c000702021d,0x13000a051503021606]) else (d0 [0x2cc12600000214,0x4071016c400ec00681,0x484271102c125f828a,0x82e68e054206c01580,0xe3a250c312c27a8211,0x88c00000000d83ac1,0x91dd0292ca4187e6c6,0x9985c32cc292972599,0x389ef19c5c61e20000,0x80f8c2a9846642eb00,0xa8fb023610f4486e,0x827fc222000081f7d1,0xbc1e7f8681ca020000,0xc2c1427840b881c699,0x80818b85ac41b3c1fb,0xf311e494219010d91,0x914083810411b18294,0xd04200000000183982,0x2100f5032640652d3c,0x55041f26404a0de492,0x23d98742ca000000c6,628680737280,0xa9441da76e4d0000,0x9986126c88975e6d00,0x80e8000081ee0000,10419394,0x814209480c41190000,0x6437426bef30000000,0xc2d482570000,4773882456178724,0xec1e7b42cba1e581cf,0xc171c1f16e9400,0xc192c25c8225c18d,834991049728,0x54830b000001490000,0x830449b0c2834d2840,0x72405602d96d45e1d9,0x2d4d002741258323d5,0x50073418f01c3c311,0xc1fe80e202628168e1,0xba662000082e55a81,0x40ee0000c03dca0102,0x318d3bc1b8dd8dd2c2,0xe982169ecb923901,0xd622c28151000042aa,0x4075294c02f0c60a00,0xc19f01f90725c2d6,0x82aec0db9f0e82b8c2,0x5b01c7813dd30f41e5,0xc1ed91a9c02a00,0x91395b08123c609,0x4a9f00000000000000,0x10000010cdc1cc0000,0x8cfc000005ae113b59,0x28c0ecc1415ac28153,0x90f626f300da48fc91,0x9d0000000080cc0189,0x7050000016f10c0ed,0x339e7dc20a00000000,0x920901c0000000,0x9270000429bca26,0x401385c081ca50c700,2193031168,0x40410000000000,0x51eb00002ac282ac,0x303000082720000c0,0x340000c23400008ae3,0xc04702730242000000,0xd38917011852c8acf3,0x9ec6dec98170523a51,0xb4030640fc83070000,0xc1b041900000000042,0xd7c85f0000429c9988,8433730,0x4b0000024dda7a0000,0x809fc0ddc30800,0x4a9c4202031452c4,0x81f0028b80b7e2a000,0xc0794208006cd16e,0x9b05c1360000809201,0xd5000029455e62e6c2,0x6d2f41b6531712,0x810000dd7b0000df12,8356563819430029,0x1c1ec8c10f1f08419c,0x80e400008059000000,0x9a4033000000000000,0x5ef60000814fdd7a81,0x3f82ea832702f30a85,0x5ef00000954bc30dc4,0xe2407e828541a351a8,0x82e48036c061000000,3215876161536,0xe669c17b9da10000c0,0x9b021fc91bc032c188,0x8243083c030c02a300,0x8195416ad2c5c1fc,0xd6a0a665032e491000,0x401f6dfa099201da,0x2f2e4109000000,0xc2569d1a422d82b1,0xc12d41210000021b00,0x4181c30e00004094,0x491a0137c1abc082d2,0x2251a00a4a0254c0b4,0x27b021744d640f6c9,0x1ce85000b24d92dda9,0x8028c060c302d0bec2,0x8caebbc11d624a82a0,0x2d34008b0000032002,0x9e81650159c15f42a8,0x1b27c2b4c1d7844b41,0x124062eaa5c2478317,0x5c35018c28ed6affc1])) else (if j<3 then (d0 [71270725682593,0xe2a148ea0000810100,0x23000041d8000001ce,0x10000000000c32100,0xa6810000431d0000,0x82be020f5063a47000,0x51991e08c26e0a6a,0x40f342a681e340b500,0x5f0265dcff41a7454b,0x41e4c25f0228807088,0x1002ed4296c8148e48,0x10643316d9bc14b43,0x32889080fa80660134,0x411c0244c8ecc27c44,0xe002e7de7e80f282b3,0xda7958cec83bc00a4c,0xf7c0b152bb415bdacc,826912898944,0x3a11ae000000000000,0x59e2000066f0c2,0xdd000011f9000002d8,0x45000000fd80dfc0,0x1d80e700009ec2dc31,0x5d22d4fbe9b5c1b700,0x80cb99e50000014a,0x88542904919d9,0xdc02ff40bf02370226,0x80968003ddc681db01,0xa400000124403f0000,0x402540bc0329400900,1664303300608,0xc0c180fb0000000000,0x10c80000c17e0000,0x644fc0c081e8992fc0,0x6d00008019c1ef0000,0x81a201970000c0cd48,0x12d50681df81bd513c,0x829a817901b5401b48,0x6d00001d1800009d1c,0x8115008000000000c8,0x3700000dfa822e82c7,0xd19bd1a501c2000053,0x15000086e581f2819e,0x49b5e951000043,0x9000c00005eca0000,0xc5c780cae94d11,0x760000812a80a5820b,0x832b8002c2230000c0,0x26c92919d81e6300e6,0x1d7cc1f8c879211700,0x8101ecc88942339114,0xed2d01a80461c21e42,0x3e8064c20500001dcc,0x8313402f000042c512,0xf089440088800d0000,0xa902022bc21cdae582,0x1000004284000099a1,0x21582990000000000,966367641600,0x81aa00000000000040,0xf9cd3c00000030c2f5,0xcd8bc039416b00002e,0x911afe009e190b5de3,0x914e81017c82c242,0xcf00008c3b02480097,0xc451521d431a827082,0x4116bc16411be8220,0x422c804349909ef952,0x36c1eb828704e44259,0x80c545ca0000422ac0,0xf1e6500000000c255,0xddf8451f84679d88ca,0x81464f807a02cc8537,0x2dc5681c32ac2f11d,0xc300ea0000402b0000,281857228895,0x700001231423d91b3,0xe1dd80c4420c000082,0x290000e138c1829196,0xc2ce4663c2bc000001,0xc400006e8dd319d226,0x5036c218030f8aa681,0x8c1408156d3098142,0xa66dd2bf01e2c0a882,0xb58166c1174150c1ae,0x1d51c139051b1dfe42,0x4a457902951d1b0000,0x413180d980d749,0xe400f1828fc5c2c10a,0x4103893cc94a815e40,0x85521e01d98d29806f,0x4816432d80c745,0xccc8844069c264c102,0x2bb41d0104dc23800,0x2fb1ec1c90848e9,874122172763264,0x8a425a614500004638,0xc68300460000c17500,0x19900008162e186,0x4004487c000042,0x910000000040530c02,0xc1f6e6cb40a90d8f11,0xb90000c80ac5099f11,0x472a817dc07712c602,0x60c02980b940930057,0xc80f4a4bc11e01fa59,0x89c5864938e663c80b,0x4130c15a422f00cfc0,0x8c0000c03cc196518c,0xc04c827e40abc02442,0x768a5596c2c2770000,0x29f1aa046c240bdc1,0x2700000000420351c0,0x2a240fe8811c08f89]) else (d0 [4962098924894720,0x82ab9a1be29f0169,0x621b4145428602d200,0x821200a4d856,0xc0ba12630000000000,0xbe426ac32f00009174,0x81f401cb42af806a00,1123811328,0xe03901dc22e212e902,0xad40dc561b105f86e0,0xee930000c114000088,0x1d025d41e181fd01bb,0x81f3000040ad59d782,0x9740c2d2f110ec46cd,0x8ec205f30000c52800,34060801557129,0x1130000020d516c91,0xba5e0700004310d1f8,0xd8540809523880d000,0xc15d00000000e666,0xee909cd240a6004800,0x59834178006302a4,0x8058c04dc2c8d18311,0x925224000048399325,0xddc94319c1579da3de,0x814044018ed30ac049,0x23b407dde7c000099,0x2742d0c30a0000c06b,0xd2bd417a92c0000042,0x5e00000000408d8185,0x823f00005cd482,0x40e990c07fc1b9c0ac,0x81e0df1005fa000040,0xd541c541bed97e0000,0x8817c2ba891d040600,0x9c8818e1e681984050,0x4055880e80a3819ba2,0x814227016d0000aa26,0x11fa00004279aa4a41,0x6e0000000024ff0000,0x80e5c252000090f38d,0xb045ad624906cc41d2,0x158000002c4419300,0x8095000010370000,0x1ec20029b685c8d1,0x9e823542bfa1845262,0x493a00000000c12bed,0x4cdef28250c2821d25,0x404b5ef348f7025841,0x775ec7051742a7451e,0x813b813802468239c1,0x1b1233e04c10f082a5,0x92b866ee51a6e8f10,0x495cdbc1b1d22dc021,0xd98450f225a1419482,0x75c2f982e900748110,0xc12990c30000c06702,0xe381554120c0990000,0x49490084c91f421a41,0xe7c12cdde940c94d8d,0x82e84078d84d402083,0x229e66024151c54174,0x1e2ec0ff82d1d9d500,0x6e00002a8100128184,0x83300000926aed2ec5,0x2095ad014de6fcd2fc,0x4c610f25807c00a292,0x30000081c182b00a63,0x40d681cd40a141f541,0xba0000d1ab0000c207,5124749739050240,0x2d30000ae880000,0x8328d86082f71eef00,3229286400,0xc28d000042bdc1,0xd1864800005da80000,0x80aac02c9cdcdee480,0x101d4c10bc1ea0000,0x4947805c000086,0xa012f7000081612dbe,0x83248042887300ef80,0x400000428e904f192c,0x4e005dc163425100,0x8702c0515c34,0x413c455a8305001700])))
def l54 (j : Nat) : Nat:=(if j<1 then (d0 [0x99ff8fe7880a0e,0x18eec0cbbe66039,0x45800007e0761dd418,0x851602fac46c0a44f,0x8e2d41b00a483df013,0xc0af006010662c3e1f,0x5a5adc83308350ff9f,0xb1f8d1000804bea0c,0xe0e7e965500318662b,0x3feffe92f848000400,0x4badc007bff2b49001,0x8c51165e1ffe78810,0x54a5d7ff1cdf102095,0xcb80000392ada6fa91,0xbc82e3a85d04e2,0x400f00b0c2007190c4,0x805fa49a2332060512,0x73c12905ef828ac5,0x6787c001b824009295,0xd200ea1b9000000000,0xbfc00001bfcf3d7b,0xc035b9ffffe0000000,0x5e1557d71a0060baa,0x96800000000005fe00,0xdfe79ebde01ad80,131857279,0xc09be1bbc06a330188,0x7aff5a413aa8018218,0x1f5bc0004e06d602c2,0xe6fc00d5377af1541e,0x980d4400beb11b0291,0x3e38b506c02933e38b,0x11b1a91045f04f5b40,0xb10536d91f0ca7cc0a,0xa980a51b1be194f981,0x553014a36027f3506f,0x64d602936cefff8f48,0x562012a358f5fe00,0xe16604a8960001f002,0xf846b5b40b104d5388,0x17c33f00fde620122b,0x6463d241140243691f,0xf98016604a894bfc01,0xc2cc09512a54cbf97d,0x2a0a094017036840b2,0x314912c998a52d0588,0x978ff26a4b8b987052,0xc80555a9503aac4150,0x5255cb5841a874c884,0xd01aaf5423d549abc1,0x6101c86a0a5a6a8939,0xa8b410a5c608ca0ea2,0x785a8ac20b17211c51,0x86110a20c288181081,0x7c1685e05d0f93f1fc,0x981982e0241e81680,0xb9f33de610f29dc3e8,0x78180384c09312425,0x449c92acf9391ec634,0x8d05886104c1a580a2,0x1190610202cc6c06c1,0x522703e01f0be21839,0xbe0fa1885f8a80962,0x345a01a14613020c4c,0x7e144550d41a02523,0xe08e8c696a05c06101,0x3c1b890015016070d,0x98fb21a392bd50a99d,0x4e85b0620e83180000,0x81ec10a894fc940370,0x230c10621f82203c11,0xe3241c105026360b24,0xf49ae312460cc13814,0x7f83d05e2fa2282a2,0x303442282294d0d408,0xca22a2da3640507c1,0xe22949f86e0ec0d011,0x8436a2e40e1341aa4,0x540c82c0683b05704e,0x18a0fc409291e80187,0x4866080300901500a8,0x1142489919a2d81410,0x13a1444b00e0100e0,0x2d00602005019002b9,0xf587a75d14a7713279,0x44c7ee36f15b888438,0x61230628143f19eecf,0x1974f3891b34d6167d,0x31dd858bf65d2ad4d6,0x4aaf155029654069b8,0x4ada42d19688c425a0,0x10f7a7773969b04c84,0x5bc29e937094444c1f,0x90ed470e3531918b5c,0x5182410fb06a42ce10,0x105881d80760009663,0xcb2fe584f2b9f95c7c,0xae1e542f2a0f9646cb,0x36491b2cc496524b2,0x7259192c2496064b01,0x257492b9c95c24aa72,0x54392a0c94c64a6124,0x989249c964dcb24e58,0x372c139601caa4e550,0x7299394c1ca40e5815,0x2c09954ccb0425520a,0xcbf6597b2c9d963eea,0xe56622b2921709098,0x4564dab24e1206ac8a,0x5660ab2655912ac985,0x6480b2c819704ca036,0x4c23243ffffefdfefe,0xffdfbbef7bedfd7f58,0x1404c1204403008010]) else (d0 [155618,0x67259934a6b1ccffb,0x7406a1e14a4f13bfff,0xff9ff85c09f851030b,0x2684d0060b0726ba3,0x7ffffc2fbf9c6df106,0x850640b0b901f81125,0xd004fffffa81fe04c2,0xcc7da27100b9c86f8d,0x6574003ff64f4a8002,0x70048252a141005d05,0xe4f43ffffc4ffc2e04,0xfe0a2068989a134018,0x2c13f2f8077fc0be9f,0x48400a0926e00060,0x822cf2003b043cd20,0x7231120f800066015b,0xd520722f1a0000000,0x1bf819fcca2425f35f,0xe1423eef5313544018,0xe0b7a8c5e16bfc034,0x72f5cb20b170cda37f,0xcfc21a1242880301c0,0xf54b7cbb71810137a,0x401a8b4ffffff60cd0,0x40010000436a7fff1f,0x6d01241398a0001821,0x8014750ffff8000064,0x1a50028151b60039d,0x2bfc33e70094ab0,0x48205212602008d79c,0x7c02c541810438037f,0xfffe4411300060860c,0x27000efff6f4e04120,0x4c02680006008018ee,0xeff1c8da185c800822]))
def d54 (j : Nat) : Nat:=(if j<2 then (if j<1 then (d0 [0x8ae000001c400,0x5168000000000,13,0x8ea0001041a14ad94b,0xa2f9110b467000184a,0xc0000000d05054a506,0xa80fa000180fc00020,0x4c49b7085c00042fcc,0x1fe00030ae80000000,5835696509719,0xf16b00000001833e0a,0x8000012a000000000,487752,0x8e4000000020740000,3129415,0x800070e60000013800,103691583488,42464,0x11186b3380000000,0,775,0xe80000001525c00000,0,0x184b400000008150,640902554162,13979942,0x300000000000000000,14032044032,0x857d039c2b444c4,6658273055515,0xc05680000000028000,0x8163817000000,4359192896,0x1022400061240000,18243584,0,461440,0x81fc232757300000,11774,91725658035585024,0x6099c0cda2c874,0xb80000001335400000,0,0x95730720000,6987,0xf1868000e9f59a5201,0x48000401c040400000,424437275426821,0x11c000000000000000,0x810000000000000000,72057707418353664,1349824,0x46d26600000006f700,4252,0x242d4f40c804000,0x30a00000ca36000000,0x985f051c00000,0,0x104c800000000001,0x3300000000c1105be,0x8000692a0000000000,0x82ac000000040,0x8a0000000000000000,1229848576,0,0,70044876800,0x82d400000000,0x10600000606c0000,0x20218148000005f,11699200,0,78643200,0xa19c00060d20000,0xb00000000015f,832116359168,0,425545360081808,386564538718,115400704,309533368945668,0xd00000001005400000,0,16529,0x844c45680000001056,0xc0000000000002c120,0xd914b01900419a3d00,0x8006025f21f4f714,0xd68000005480000000,0x328880000000000,0x26310000bcdc00,50390368260,0x9124f8b0a00900000,2732689719297,0x9c0d0550000000012c,0x713a8959000034c745,0xd80000000000000000,62844325855232,18116716726490,0x908400040900460000,0x303b00000000bd1000,0xd1a112a800000,0x2d2880f4000600d3,0x400412246035106000,0x22733020201321274,0x4513207000000507,0x2a301113130020210b,0x81043010000000c000,0x16100010064028024,0x520010120056011014,0x402310003150401010,0x300103010012031250,0x1300100100201006,0x220001001100210]) else (d0 [9007408298852433,0x6a5be3699000000008,0xa3c000000000000000,0x2a000000000002022,0xc2e30000048400060a,0x1000024a007c000091,0x74000000000009d480,0,0,0x89900000000000000,0xb9744310000c2,0xc2000000000004d480,0x233766b200009414,0x840000d9d18966468,0x80f600000003414800,0x5eb00002479800000,856030163501056,0x6c80000001807b,0x419600c000083012a9,0xe09b00000000000000,0xad300000000000000,2963275778,0x56c000000000000000,0x60cd00000000000,520,0x542d000016b80000c8,0xdc000000000d600011,0x2c000217b00008293,0x9a00000000084dc000,773027004416,2109314,0x2a29d70b5000000000,0x23498000022c0003,0x65e40056ae20d2c000,37957632,64212822917120,0x84da22d800002ed0,0x4c0000000c2960000,0xea00000000000,4622388423557120,0xe1e40000000411400,0xa260000014600000,0x601726820000,12303,0xc07d00000000000217,0xac8de0020000093940,0x7c0000000605000018,0x21d03cc11f000184cc,180388626432,0x9382ac000000,81822482520,0x64000000e000000012,0xb805fe92300000001,0xb15c14d00ac0000000,0x4254000000016e,0xc0001b1b8000289700,21798846464,0x102ee6f8c9e60000,0x609800000000000,0x493a00012ce4000626,0x7000000030aba1281c,0xa80000007800000000,2,0x495800000000000000,0,0,28012707840,0,0x415381f72254000,1901462554293,0x600010178000000000,0x829c0000000c2920,80304,498618370,0x42c6000000040a,0x200000001193000000,0x1cd10000245dd2ae0,0x207be03000012b08,0x759800000000000171,1289362604032,0xc25e840a0988e7b81,0x580515a8c000059448,0x3c800020e0000110fc,0x616742460000000,0xbd00000000000000,0x594680a8000000000,727711744,33156,19327357095,0x8000000184b8000000,0xd26f88b4000000000,298052,0xbaa086e03400000000,0x62000000000001235,40464384,0,265792,44800803944874,0x304790221a51055e,0x407501fc000208,0x4821c00000000000a8,0xf0a885185000000000,7599824414703616,2199,0xe13000010412048cf4,0x20000d1b0000610782,0x2e45fa02b800000018,0x298000610f00000000,8577,0x80000000011c06e2d3,0x500000000465800000,0x1142eb39767100000,2854823328,13390])) else (if j<3 then (d0 [17666408449,0x84b66e000000000000,0,0x829c839e169800042d,0xa000201ac0b6000182,0x380000000c61732da4,0x693498000000000000,0x7c81ae00000000000,0xddda00000000000000,9210059150065664,0,2,0xc7000000000000000,0x92c684600000000c1d,0xc02c900500000000a0,0x440000000000000032,0x3c0000000000000000,19568,0x1ad2c0004152416,0xe80880000000add200,0x20380000c05c00000,0xccca00000000,0xdb000000000000000,43433984,4555826429689856,0x1221e0ce000181a81,0x1944fe00018129a89a,0x64de30000041d0000,413696,9047552,34579939382,0x390000000000000948,26585847562240,2199023255552,0x180760ba0000000000,752135071866756,0x3f8000000000000002,0x86881f800000006082,98304,4567921057595392,0x1068e0bba1ca05700,0xae2a00000000,8952,34709504,524346,0x800000000000000000,0x60d381dea5240000,0,2247140537000,0xe0000000703c000000,58314987568,0x49b2b3000000010528,0x88bc000229c8000,88886732166006292,0xa00012364924000102,0x2c00000005d200327a,0xbf8000028400000004,0xcfe20ea00030bbe894,107429888,0x2779804180b600,579567856131594,0x94095d5277c1df09a8,0xb3000000000000000,0x83980000000000,202056976896,0x201d8000000000037,0x6be22ed10c00000198,26417541316608,43276316,0x70278000000044d800,0x32318000894800000,7828212384,0x51c0b000000000000,0x98a9cbcc0000000000,0x3634f6b9000081,0x4c0006962000183b22,0x400000000000244de,0xeaf00010059089530f,0x860400000000000000,54839086265344,734003200,47141561040896,4037818753167,73574920184967168,8472064,0x60eb82d680ad0,0xb60000d55200000006,0x6b000000010aaa0d0,3317325365248,0,74766790688826,0x5ce493013a13d485ac,0x67000000000000000,0x94ce00000000000000,0,25,0x72a746000002e6b190,0xa3da0008000,0x20a00010430000000,6207843913054212,0x880220000000000037,0x4aa26eddf200000000,0x444e00024b58000,2225195712512,0x5cc494c16e000000,0x24b4f45d000000026,0x49202540a424f00000,0x29f81b050a59708000,0x4f04e24188000000,0,727086652194816,0x2960c0b200022852,0x8330000db7c0000000,0x42c800000000000827]) else (d0 [22626672790,0x7a00d0000000000004,0x8b4049aa4dc81b266f,0x832a755e4975a6891a,0x603de0f30000000205,0xd0000007800000006b,0x984ca937c08d8000c,0x23a000172dc12082c4,0x85110bc0000d135004,0x146a00009caa0ad712,0xe422f0218000000000,0xb4000000060200,0x904000000000000,0x18bf80000000000,0x1b8900000000000270,0xc80000000000000000,0x806400000000,53015490789530,0x202100000001842,0xc00010e40000c96c00,0x32c11a000109d25,0x60000000000000000,0xb1f42724ae0,0x20848000000083d,0x449700000a5013ec1a,0x6f63a0000000000000,0x80000103b40000000c,0x27a000000000000000,0x9029a3b80000000000,0x309a00000000000000,24868028416,5876,0x552844400000000000,0x33830000000005c,0x800000000000000342,0x68000c94c0001777ad,0x7c0000000109606728,0x15c5bac00000009a96,2250831301127,0xa443d02e0001a50101,0x8895100004a5477000,0x42fa000307800004,0x138000000000000001,0x85c00000000418a000,0x413f0000000000,40656777018496,0x119b23c7274a8a98,0x528000000000000000,0x67c402880dc00b,0x40000000c85785e400,0x166f82cb849400000,0x1dc48cb400000000,17911155261441,0xc38f200a56d48e2809,0x811e00000000a2e400,14,0xe4000085680004f6d0,0x1325000000000000,67756032,0,35029779328,0x41c5a33c00000000,0,6155,184046059520,64,0x94ae391f800036770,0x1a0c00000000c1ca,0x206582230000000,17146880,80341893128,0xf70000000000000004,0x1a92d3400005180000,73799220523646976,121,0x400000001838769c00,0,35869096083456,75338536745435136,901406262073,0x300000000253f49e81,0x3c286000144680000,0x837800000000000,201465856,0x105e0d80000184ec00])))
def k54 (j : Nat) : Nat:=(d0 [0x7ffffe000017e0,0x10944e400000002fff,0x97991d6494e800fff0,0xbf2a0c06404fe00,0xb950499fc055100a3,0x8000fe26242400007f,0xf2f09a1617fe00190c,0x5617fe06002054911,0x7a2510a3384a4e9fc3,0x61524e0fa3e03e2f90,0xc3917e5f1502d8f646,0xc410d9f27b984791dc,0xc0120300205020040,0x1a01860138764508e2,0x88c86a0501f82c0f02,0x61d0c613066170243d,0x28168d6760620381e,0xd03a0209607042110,0xa200a831016000040,0x60900a823d1bacb1ee,0xca4d18860005916050,0x130481100c020043ff])
def c54 (j : Nat) : Nat:=(d0 [0xd078000000000,0x10b16ef035b8d00060,0xd400000041c0000000,1051136,0,9793122970,0xf1074e2801b30d8928,0x173a92a812c0b102,0x511f000a24021bab10,0x120000650000000000,0x101600000000220180,0x88e6a840008155ca,0x8d000081c24b80024,0x100000000002054000,0x447800000000000000,0,0xc3d456800107600000,0x60f40000000000002,0x4200048c228720400,0x289800010be8a0,0,977105059840,845258992648192,0xc0280000000,0x60d2023820000,20447232,4947802324992,2713766806,0x88000000c19c474108,0x8018000a3000040,0x200000000020000248,0xa2900060fc00000,0x1f00000000000004,0x1c000000e990cac65,0xc00081180880000004,0xc8000001905490800,0x3750000000000145c0,576144092954624,0x536000516e8a80,0x98003078000,0xc8d000203a00000000,0x2456000000000063b,0x836000000000000000,4184,0x914000000000,0,53095855104,0xbb900000000000000,0x20c5114000000000,0,0x4830000000000000,163208757248,0x5080ce4000000,0x69160ca1363b701700,0x102f0390006453460,5770238655307877,402490243678209,0x50000000206c00001,0x44076040b30037c07c,0x2262000000000000,0x1bab88000af05a0000,0x2cdc000000000000,5101735070864864,0x105800208308e000,263680,35600581263360,0x4c380000006c860,0xbc24800008d8003534,17819883343040,0xb000000000091a8000,0,6,0x2e000088d000244800,0x181f00c60088050800,0x11400010051002008,0x1c0084222500080020])
def j54 (j : Nat) : Nat:=0x403103b437ff
def b54 (j : Nat) : Nat:=(d0 [48,0x400222000000000000,0x42000000000000067,0x107c080000000000,8673820672,0x8cc00000000000,0x951970000095f0600,0x231000000000000000,0x5c40000000000000d0,5200,35634806784,0x61c000000000,0,1267015352320,4630511616,57868288,85487029059721,0x400000000000000000,0,0x9000000000000,0x11000000000000000,0,803840,154618822656,0xedc00000008,0x5c0000000000000000,0x293000000000054,0,0xd1c000000000318000,0x5dc0000000000000,0,0,0,0,0,20938025344,0,0,0x3a70000000000000,0,7171,148992,0,0xc0c000000000000000,0,23,0x400000000000012100,0x253000000000000000,0x1860000000000000,0x35100000000000,51606716416,208305913856,0,0,0,0x9800000000000,0,870,1024])
def g42 : Nat → w0
  | 9 => (7,6,9,393221,51,6,4096,moD9)
  | 10 => (182,5,9,5963854,119,11,4144,p54)
  | 11 => (820,4,9,5898424,120,14,4465,n54)
  | 12 => (386,3,9,1769521,86,15,4664,m54)
  | 13 => (66,2,9,655368,67,13,4360,l54)
  | 14 => (9,1,9,65537,0,9,4180,k54)
  | 15 => (1,0,9,65537,0,0,4099,j54)
  | _ => j3
def b46 : Nat → Nat → Option (Nat × Nat)
  | 10 => y4 3 61 1 8 3 3 h54
  | 11 => y4 65 977 3 14 8 4 g54
  | 12 => y4 353 1741 8 16 10 4 f54
  | 13 => y4 199 1993 4 15 9 4 d54
  | 14 => y4 40 409 5 13 7 4 c54
  | 15 => y4 12 431 1 10 4 4 b54
  | _ => fun _ => none
def mo : w1 := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,g42,b46⟩
def sgY : Array (Bits × Bits):=#[((d0 [244,0xe2669a6837f027081c,0xf22055df808222736]),(d0 [4,0x209409843f007000c,0x720001df800000733])),((d0 [96,0x1c324b069010597803,0xf9010a2609fbe0181f]),(d0 [32,0x80a02e269000187801,0xf800000000fbe0180c])),((d0 [37,0xf0dd0188027ef8024,0x25e13c1fd105e4930]),(d0 [2,0x2808d1092003e78000,0xe03c1fd001e4031])),((d0 [201,0xc0d906874040901240,0xffc4fc1e1027e41fc0]),(d0 [192,0xc0010ec00000000000,0x7fc0fc1e0003e01fc0])),((d0 [16,0x28d4b1279c83fa01f1,0x902f20e021fc806260]),(d0 [16,0x28d4b1279c03f801f1,0x800f00e001fc006000])),((d0 [134,0x910025492109002481,0x248fff0841ffff8000]),(d0 [0x9100a343a000000000,0xfff0001ffff8000])),((d0 [0x81412a020041fe,0xffffffe01001009]),(d0 [0x814120000001fe,0xffffffe00000001])),((d0 [0x28004905ffc0481ff,0xfff04000804208c000]),(d0 [0x28004905ffc0001ff,0xfff000000000000000])),((d0 [58,0x518020b05fffffff08,0x400880910680110480]),(d0 [2,0xaa0103c5ffffffe00,0]))]
def sgC : List z2:=q7 35 (fun x => (m1 x 0 9,([0,1,2,16,32,4,8,256,64,128] : List Nat).getD (m1 x 9 4) 0,m1 x 13 9,m1 x 22 9,m1 x 31 4)) 106 (d0 [68742021434,0x800b732450038da28a,0x56c449400ad08928,0x1cc1095002e620ca0,0xd301258025e4c0301,0x1c6d106015c5510c09,0xf01819e04ad8083892,0xa7208704f88c08e097,0x31c01c654c1404002c,0xe098800738063000f6,0x4d400b5885280370,0x44550054c058a00e31,0x8a59005e480b0212ee,0x6061025dc90e284bb9,0x1c0bb82203801ae12,0x878238d821220adc81,0x2600bd8012801cc709,0x5002f2206a00ad4896,0x4095b910300b982306,0x8038d828c24ac480de,0x25e44048097b10040,0x56244ee09f21809c0,0xde090c0013e160904,0x798c02a00a9c8b2400,0xf70843801dc111900f,0x98c10a00f100360017,0x90432803c800b90077,0x8042a00f11835cc097,0x7043801e610c719630,0x4810005e8409d11715,0x14002b6024400780c,0x1ea00f2182d8809771,0x43e00bc80172425dc4,0xe00e380e28495b900,0x390770404740979200,0xe00ee008e000fb0824,0x2b72248007980135,0x25ec001820e368250,0x27cc60080078c038c1,0xe6088a000bd881320,0x2e2a0a73421dc20c40,0xdc1015d05715043803,0xe200e70a38da00e30e,0x6080a228e36003c41c,0x6c047455854211812f,0x2002001e6304b91750,0x410709730441200fe0,0xf401ef0083803f00,0x7b007b8023800fe80,0xb001f70046003f600,0x4c0077c0418007f840,0x34017f04068037e040])
def sgA := moA
def sgD8 (j : Nat) : Nat:=(d0 [4295004413,0x30b281002edebeda17,0x59cedd17588f587f42,0xef25c4befc9513fe9b,0x94549814c153549814,0xc120f055354930483a,0x454d524c1203255354,0x93048198edda54c910])
def sgD9 (j : Nat) : Nat:=(d0 [868787,0x420474103910526840,0x3991050687dc080000,0x35a0a59104010c882e,0xf4310000067a320057,0xa16400608180138100,0xee00cc600000e065,0x4339883a8461d1230,0x9020000d6071810,0x4e6200037d944cd8,0x6b6100008d84000000,0x1b6100007a21b04,0xcbc70497c248c0000,611465904117257,0x174194188a0ae1220,0xa46f606496407a0b20,0x804d9158ddc05c2588,0x1835e27c1360287f60,0xf012425a06a0fa0547,0x940142720dc000300b,0xc023e00267e0487c04,0x8166021c94099e0147,0x75e040680a3a0005,0x8063b2e8f8dddf68d8,0x34bcf32dc971dc22f3,0xbaed6b06b9a667a9ca,0x619664a90a3a87e178,0x3e007d1e072db66b9a,0x5669926297c5b96654,0x94a4b9204490a408f4,0x3b0e4370d4330be2d8,0x9d2307317054130440,0xf03409c1f05c0089cb,0xc22727089a9c0af06e,0x8ba6b91e9ac6f94ae2,0xe9aa8ba6a4771681fc,0x89d1e9a42bc4899e9a,0x22bc4848f2205ba67d,0x16a5e45a9744f2dc10,0xcb6d8e61a77b665eed,0x987fb65e854d72dc65,0x8b71959bb7524e6143,0x1c64e8f052a0c949c2,0xe5183b542a54903db8,0x214ea0787a71d7e9c7,0x57a71daed063fb814f,0x6e4427c40cf6602a18,0x306960c009cbc46f1a,0xf0bcbb46f1ad19c6a0,0x5f1e705cb981f2e50d,0xcb8cdf0529fa44a366,0x101bc63c6f18e4ba53,0x53e94c43b62c072ca0,0x3cb24ee9c797c703ff,0xff63fd2ff0bf6afd6,0x3deaf3d39afe5bf7f4,0xdeeb7b6debb5fcd7b7,0x5ebd6f757ed5bf3afc,0xdbf1efc77b1ddc6ff1,0xafc5ff16fbf4afbabe,0xdadedb7aecfda7be9a,0xfa5be1ff87f61ef86f,0xe17fea79460530e9b9,0x4605306eb94605306c,0xb94605306a79460530,0x6d79260530ec592605,0x30e519260530e51526,0x530e63a464d20657a,0x464d20aa7a6605206a,0x7a6605206d79360520,0xea791605206cf91605,0x2064f916052054f916,0x520ed193605206dba,0x154d206d8a954d206a,0x4a954d20661a54c520,0xedd954c120e91814c1,0x2054d814c120549814,0xc120ec5534c1202e55,0x34c120e91524c120e6,0x1524c12054d524c120,0x605514c120605314c1,0x206a3a464d10663a46,0x4d10ec5a564d10ec1a,0x564d10ed1a960d10aa,0x7a7549106a7a754910,0xe9f9354910ed193549,0x10ec99354910e9d935,0x4910e9d835491064d8,0x254910edda54c91054,0xd52481105495148110])
def sgH9 (j : Nat) : Nat:=(d0 [47872,0,0x800000000000c3,0,0,0,0,0,1099511627776,50432,1140981760,0,0])
def x53 (j : Nat) : Nat:=(if j<2 then (if j<1 then (d0 [0x9c72fd9472fd94,0x62fd9454fd24567d9c,0x42dd9c42fd94459cc4,0x421dbc32dd9c325db4,0x258cc422dd8c183d24,0x185d24069cc4089c9c,0x1bdcbf1a5cbf2ddab,0xe83d23e2cdabe8ac0b,0xe01dabd01d93d3fdb3,0xc01dabc01d9bc01dc3,0xb01dabb00dd3a00dab,0x900d93900dc3800d93,0x841d43741d2b740d43,0x740d2b740cc3741d23,0x600dc3600dab663d23,0x54fd23511db3419d8b,0x41bd83419d8b31bd83,0x319d8b241d23215d9b,0x100d9b000dc2f00daa,0xf06daae42d42e42cc2,0xe11db2d19d8ad13da2,0xc19d8ac11db2b17d92,0xb13da2a17d92a00dd2,0x914d9a941da2815d9a,0x801d92845d82800daa,0x706d8a708d82700dca,0x600dca500dd2400dd2,0x300dd220cdc2216d92,0x23fdb2101d9a117d92,0x143d8a107d8a145d82,0x109d82101dd1e13da1,0xe08d81c3b5c9b3b549,0xb3adc9b3ad49b00dc9,0xa3bd39900dd1916d91,0x803db9709d81701dd1,0x513da1517d9153bd39,0x500dc9200dd1100dd1,0x14d99016d91001da8,0xf41da0f17d90f43d88,0xf01dc8e03db8e00dd0,0xd32da8b8ea90b2fd90,0x933d88921db8833d88,0x829da0733d88725db0,0x62fd90633d88663da0,0x529da0569d9052fd90,0x571db8169c98168c98,0x17ca9818ed9003dd37,0x778a9c07aa900ffe7f,0xebff1ff6ffa7fcbfdd,0xfeaff37f7bfb7fdafe,0xc7f4bf7dfaffbdfdeb,0xbfddfdefdf7ebbedde,0xfef776ffb7ddbdebff,0x3fb9fbbfddfdefeb7d,0xdbbfdd7edff3ff9fec,0xfee7bf37f9afcbfe3f,0xeffd7fdbfe5feeff57,0xf6bf7dfbaf7f7bebbf,0xddfadfd5ffaff57f6b,0xf75f7af7d6feaff4ff,0x9ffcffa7fb3bf9bfc7,0xfda1e51306a3914c1a,0x5e453068b914c3a264,0x530e81914c39464530,0xe51814c39260530aa5,0x814c1a960530649814,0xc1526053068f98481a,0x8e4d206979348198e4,0xd206a391481a3e4520,0x64f9148153e4520e85,0x98483a066120685984,0x83a864d20e91934839,0x864d20661934819564,0xd2064d91483a960520,0xe9981483a360520e4d,0x814839160520aa5814,0x81a960520661814819,0x36052054d81483a154,0xd20aa553481a954d20,0x68553480a954d20e95,0x31483954c520aa5314,0x81a94c52069531480a,0x94c520e9130483a14c,0x120e6130483934c120,0x6a130481a54c120685,0x30481984c120655304,0x81814c12054d304815,0x24c12054530481314c,0x1206a393441a8e4910,0x68f9244183e4910ea1,0x93443a564d10e91934,0x43a264d10e8193441a,0x864d1069593441a264,0xd1066193443a864910,0xe8d92443a1649106a1,0x92441a364910661924,0x419364910aa583441a,0x960d10ea582443a560,0x910e8d824439560910,0xe4d82442a9609106a5,0x82441a560910655824,0x41936091054d82443a,0x954910e9d52443a354,0x910e4d52442a954910,0x6a552441a35491064d,0x524418354910609524,0x43a54c910e5532442a,0x94c9106a532441a54c,0x91065532441854c910,0xe852044393481106a1,0x20441a54811068d204,0x41984811064d204418,0x54811060d204415348,0x110549204415148110]) else (d0 [0x732dcb87285c74,0x710dc116f71bb66df5,0xb536ca1b036b45ab66,0xa01a5968f5a0d67ed9,0xdf66e99a3661595664,0x798f4633d8ae620985,0x8608d8025f457a65e2,0x17765d657325c316f6,0x5b0969a599962a5835,0x5f057415ae562156b5,0x53151d53f54e152f94,0xa751d945250713f74f,0x713bf4e613744d4932,0x94bf52e54b212ad4a3,0x125648b51fe47251a0,0x45e914744610e242e5,0x83417104740c8fff3,0xf08f8a3db4f3f3c20e,0xf03b40eaa3a44e7539,0x74e423880deb3740da,0x73604d4e34b0d0d33b,0xccdc3338cbb32b0c99,0x3200c6d3178c1e2ff4,0xbd12eb8b7f2da4b342,0xc30ae42ab0a7d2940a,0x2a27c89d526e099325,0x9894024948f423748b,0x4223885e20d48061f5,0x47be1e307621c906f1,0x1b406af1a106511864,0x5ea16a457d15205111,0x3dc4de12e848d11ac4,0x4e109c3ef0ee439d0d,0xf835c0cf03170b7c2b,0xa0a50275096422d07e,0xc1d706d41990584142,0x46c0fb033c08c011c,0x75d37764dd7764d,0x97764d4f761d37647d,0x2f61cdaf635d8f34dd,0x37365ca7365ca720bd,0xaf01ddaee1ddc6a0ad,0xae61cdae447d4620ad,0xade47d2dd1cdadd6cd,0x9dc34d9dc6cc9dc6ca,0x9dc2bda584dd3584dd,0x3571d5cd61cdcd60ad,0xc5626db5646d4d647d,0x4d51cd8d51dd8d41dd,0xcd31c5cd326db5246d,0x4d20adc511cdc500bd,0xc4d46cc4d36dac937d,0xc436fcc4377db4237d,0xac287d24293c8c28ca,0x9c290a9428dd8c18c5,0xcc191cc406fcc3f92c,0xbf1ddaba46d2ba0ad,0xab954c1ae1dd9ab2ad,0xa270ad9a734d8a70ad,0x9a647caa50adaa546c,0xaa51cdaa30bd9a135d,0x8a123dba06fd81f37d,0x81f1dda9e2bda1e0b5,0xd1d0a5d1d0ad99c48d,0x99b0adc1a1cdc1931d,0x91649d3961ddc1565d,0xa152bda156bd91531d,0x91547d4155bd39549d,0x39549d3941cdc947fd,0xa9373d39353d1936bc,0x9936ac9937ea9930ad,0xc121cdc111cda900bd,0xc0e49db8e23db8e53d,0x90e31d90e47cc0e46c,0xc0e1ddc0d6fd80d37d,0x80d47d40d46d40d46d,0x48c92c28b92c18b92a,0x98b6ec28a37d9866ec,0x28537d98437da8337d,0xc0236dc0280c2828cc,0x18290c18192c18013d,0xc7e13dafe13d97e40d,0x47e40d17e01dafd01d,0x97d01dc7c01d97c01d,0xc7b01dafb41ca7a63c,0xa7908dc7941d47841d,0x2f841d4f74bd377415,0xd7740dd7740d4f73fd,0x37600dd7618d8f513d,0xa7419d8f401daf101d,0x8f13ed37101daf001d,0x8f001dc6f3bdbef0fd,0xbef01d8ef01d9ed01d,0xc6c01daec41da6c13d,0xa6c13da6b00dd6a00d,0x9e951d16859cc6808d,0x8e811db6741cc6541c,0xae540cc6540cae510d,0xb6439d46313da6108d,0x8603f5cdf3f54df3ed,0xcdf3ed4df00dcde3fd,0x35d00dd5d0cdc5d43d,0x4dc5dd35c56dc5c18d,0x9dc56cc5c0cdc5b00d,0x9db18d8db05db5a19d,0x8da09d85a1fd85900d,0xcd604db5600dc5514d,0x9d515d9d400dcd108d,0x85100dd5014d9d000d,0xc4f00dacf14d9cf18d,0x8cf19d8ce01dccd00d,0xacc63cc4b62cc4b50a,0x94a5edb4924db4983d,0x2482cdac866cc482dd])) else (if j<3 then (d0 [0xe4f6b20c781444,0x1e1d451138b15a449c,0x588f812716293ca512,0x71623e05bff5e71e80,0x4a953c8a9a459fe2,0x6100b479e6c1468ddf,0xe98200ad9b491435fc,0x749640392497af8846,0x32975f8851b2afaf29,0xa0039a51fd71c0084,0x2adff313009a3afbd6,0x10a12bf3ea10000289,0x54ab2c268c98892a9c,0xf0851b7fad640688f,0x4f8ea51944788225cf,0xf6e4d44ab3473423df,0xe8544ea32fad612a15,0x19571c001acf5f6200,0xd6605b93ea1350bdc,0x7f08e8ac6680ed451f,0xf856c045b31974f00c,0x6525f0db9a2b510b34,0xdff2e9900732a9f140,0x522a7f109d90bafb88,0x4e335ff2e9900232ac,0xebae2880030691fea3,0xac8568fd970d6e7a10,0x2216adfa19c03247bf,0xfe3b1a012155ffe6d8,0x900252b6bc70151f28,0xb4f7b0644e3f5c110,0x354753c24268c71846,0x88b5dfa10c26dcde45,0x1942361eeffc763402,0x42bd9a58445fa11a89,0xdefd632456194b267,0x895c699402c5f94242,0x721d9f8398d0833e0f,0x4ca2f61ce66484fa46,0x3668a5188b850fff40,0x6a0a99b9dd8706123e,0xc50d6484fa463001dd,0x5c92462875fa106881,0xd3cc04d95de4e660f9,0xd02d806a1403c230fe,0x348813b497c71e746e,0x180115a803d3f84143,0xb0039b52ae0b416c33,0x64237280929015051,0x3122a37602c2510180,0x81260a1089e1382084,0x285c1b0a061841b600,0x87104c0430a60c3018,0x430c17827189064264,0x6040760887c1585787,0x6a103085f137c0a19a,0xac14c964251ca0e48,0x3c178550746e42c82b,0x12478800810a72041d,0x3c09747c8fe890a01,0x3c5704da07218528ac,0xa04c180699c06aa7bc,0x205114160702483113,0x4264c806060a0306d0,0x4052a15c230a828109,0xc0f8341a0f94c84408,0x6e19c4a0805c0841b0,0x1b8144702083805842,0x48550d07a09ac001fb,0x809e06804d02015c2,0xd0a05e0d00e81460e0,0x730302205a0c5c1025,0x500934000ae0b6180,0xd01e030059c060702a,0x8f41b83b0404e0400,0x2b0b60c01812d0ba18,0xb80bd05c134201002,0x203fc4f06010030077,0x7f01e07383cd6b329,0xcbe72d9caef29dc9fb,0x258c8a3200c7971ccc,0x6cb19ec5f7157c50f1,0x2fc3e70d6c313097c1,0xd7056c0a300fbfd2fe,0xbf42fbabe12f70bd6,0x6f42bc8eef1bb6eeab,0xba6ee7eb9bae52b8ee,0xe1bb7eedd8b722da6b,0x626d6bb556d37b466c,0xffb3aacd5b302ca4b2,0x46c80b17ac48b0cec1,0xdb022becaf1abaaae2,0xeb76ad82b47acdeb27,0xac22af1ab72aa2aa36,0xa66a946a33a8729f4a,0x75a9aea63296ba53a9,0x2aa40a8d5a2f6886a1,0xfa866a17a84ea0ba82,0x6a0467fa9f9a7d19ec,0x27979e1e7779d46729,0x9c4a7029bca6dd9b06,0x6919a2668199ca66a9,0x97664c98f662e987e6,0x1097e25e097625d096,0xbe59095b2542946a4e,0x492a2472910e40b8f5,0x63b88e8a3828db6358,0x8cae2f28b3629e899e,0x22d87fa1d786ca1888,0x52e11c83a20ab81c20,0x338021ff57ee9f867d,0x81f3b7c35ef37b65ea,0x779c5e427859df1772,0x1d8b75d5d4a747dce6]) else (if j<4 then (d0 [5079856263475950,0xa18f40f0481e622cf3,0x147d30b1c7162e5e0c,0x5daa6d462e8c16b960,0xaddc822f8b105b2931,0xf31e2d03091f4c2c66,0xf41a20f5cb056ee415,0xcc87088e848e84de83,0x441a3d1822f8b10000,0xd7fe0b4030fae582bb,0x91eba5485f162b2b9a,0x20f6a5d13d539230d2,0x581e050698af46a2cb,0xe065e6c2607cba5919,0x287107cc3265908a71,0xb8211496d9b0356085,0xe1d8c205392c0e8317,0xe00319d4401338329,0xbe1106005f16207c90,0x4196c45f16202ee925,0x1c8c930a570657040c,0xf9f2d8462055d24a40,0x7c904474247434cc82,0x8fa616306347f51998,0x50000170201341a9e0,0xfb81f703ee07dc0f2d,0xe6170de61000049d5f,0x1a8c58d5cc1909f507,0x42057e27916ca00067,0xae3483f35e880031a4,0xd7e5a7400002a348f8,0xfda2000c4927fa87b0,0x18ca77e4f06c002512,0xb7e751b00023499720,0x3419bd3054d87ccc96,0xc38257cc163f340008,0xa17a195aff4882ed00,0x3e078400ff468018,0xcd4fc40240002a1c13,0xf84e5a4415683f924e,0x485231d0e24518df,0xa104f0879fc7c4d13c,0x7ff83800001cda4feb,0x2e002a152bf5dd1200,0x64377f863800001cda,0x63f947000004234d7f,0xd238000009da6bf82e,0x45b2d76625fff8a9a,0x8010693bfe68a00108,0x92b76f84104d7dbc0b,0x89dbe96a401c6611e9,0x90c47a64355fb65800,0x9926f9ff61b00842ae,0xf9f4d0046cc4fc0c00,0x270a6eed00d8415385,0x91a239bfaa01878003,0xa23df9821f88b204a8,0xe3f40e40111d9d3e61,0x1a801d0e1d3dc9321b,0x12de90404b67b00d42,0xc317c8d8052180efcd,0x2101c864ffdefc4411,0x33adbde1081209ffa4,0xbab00c683fafc208ca,0x33e18a04eb33be4401,0xa123ff2c38919663f0,0xdc499e1fb34a041b3c,0x9d86a41a4b789425df,0xf314003c483580f5e4,0x60e9f2f1044eb7a41,0x39c034833cce3d8106,0x534ff0922420630fba,0xd6b019238cdad08d1a,0x6d68468bbf43320648,0xfbe30a811a3afd6124,0x801cd2adb793a4dbf3,0x4500028495d2eb004a,0x8f49c4a931ac065c3e,0x66358fdf0a6127cb78,0xb13dd37444ff08082,0xc270c17c808034845b,0x7c03c02ace14b7eb8a,0x50042d2ce1c6839e52,0xe227759543227b7930,0xc95db3930b2c3750a0,0xe67ac4a2772f5b1421,0x66d3a76245d3cdd448,0xcf961ac87ac88d1f90,0x808c450d0d1b12d089,0xfd25511813b40738a2,0x8d9503f331d3c6e20f,0xae91206d2039f50342,0x4f284428a985de3836,0x6eb4305c4a66dd8dc2,0xa78dc41a07e9634c3d,0x17326fe31a8000e693,0x71f10085298f63d648,0x14cebfcea40007349b,0xbc4804294afeb60501,0x37fcba6401cca8fbbc,0x48032950ffd1a8000e,0x69371f10085295ff83,0x500009d256bf5c3a04,0xdb0e095f3053dc7fd8,0x402d239f062d190001,0x711afc8c93000150f2,0xe406835fefec00511e,0x7fc50e00041a491d4d,0x123e41341d9fb6c164,0xf3ec1439e096445ec1,0x435c12c891f5813322,0x631e5e80071a27da12,0x25de240214a57f5b02,0x809bfe5d3200e6559f]) else (d0 [0x35dc301da928e0,0x45843494f16eb6ec18,0x5024fe49088a527183,0x4836ff1a18d5bbe283,0x8d254cc8afa7e71420,0x5ee1ae601d2ed91b4e,0x9d275ba9632bc6d10d,0x6a886186c4e59c62a3,0x82b6c7d210d508db29,0x8808feae8ea0386ef8,0xe342c91a3133e3416a,0x2e172f7304a3ec1072,0xc8427d312ac42d0d73,0x93d3331d32c11b117,0xa0f0400031fe5d4543,0x734c133e58267cb050,0x5e2b99012fa2514228,0x6a75208df895ef7061,0x4d88a93ca2c66c4440,0x1e8c6c7a68a281a0a8,0xfca33668daf580cd1c,0xee0b43ea26c98f0a48,0x3b480ca0f51782068d]))))
def r53 (j : Nat) : Nat:=(d0 [786529,0xb72b8135154829442,0x3880e207a351422c1,0x6800008701a0004eaa,0x5fa2f400a0d000123,0x7c1e000361303240f8,86274365631014663,0xe017956201f74b02a9,0x9f60b903701281ee06,0x1047806088800275c0,18010811148316,0xcc88717bb381380b00,0x8934101d0010050000,0x81def0004400000048,0x9c03ba2d4058000151,0x40c198025a80bbd40,0x8a4b3060008802a03b,0x4d19900060af06a00,0xcc1b40350218034a1e,0x8e8001889ca0606606,0xe59780a800000083e0,0x2094028024807ec5,0xf04100a8c060580010,0x3100000009828e7428,0xa14542800e000810e6,0x819a12007908005916])
def w53 (j : Nat) : Nat:=(if j<1 then (d0 [0xbe0f07e2408e03,0x81a80a9c2a5fe94ca4,0x6e8dba2ba88ca17e81,0x89fa27c09e6a7589cd,0xa7169baa6b89a1a65c,0x98e660f97ae5bd9606,0x54c949250193424af9,0x23646390f24158f8e3,0xb48dd23388c3e2df8a,0xda28889a223388221d,0x4869e17f850211583a,0x20b5822a0358019fd9,0x7ea1f7a7d41f287c1d,0xedd7ac5e73791de257,0x805dd576c5d86753dd,0x127359c9f71c1c3970,0x11bd86e69b646c79ae,0x6ab1a91699da2b67f,0xd9bf668d980652d90f,0x634d8ab61c18506055,0x7ee5e997895d857435,0xc8d6f65b316a159e96,0x5358915ed570559555,0xbd542549d503535149,0x2518541a4f4938a4d5,0x532c4bd12bb49a1234,0x481d1d0467115f44c9,0xfa433908140f900b3,0xf60fae3e10f3f3bd4e,0xca3a64e7038b8e0b37,0x8cda43594d26337cca,0x3180c262fccbb02db,0x8b2a2bb0aac2a1ca47,0x28149ec26e097b2520,0x91c23e08b521e08341,0xff07cf1e747841cfc7,0xb1b646a019e464418,0x345cb165455914b851,0x513784b51208442101,0xc3d20e743660d08313,0xb982c70a8827d08d4,0x206073018e053c12a0,0x42c0e0028c06c00e00,0xd3533d3253d2a53d,0x2a70d2a6dd326cd2a6,0xcd742bd552bd352bd3,0x42bd152bd3065d3524,0xd7523d74a3d7463d35,0x23d34a3d3463d32a3d,0x3263d2a63d3462d326,0x2d3062d34a1d32a1d3,0xa147514474b447454,0xcf41473314732b4732,0x549f29377253755337,0x353373472434727351,0x143511734b1434b173,0x311735104351073470,0x43470733107327072a,0x704746f7742f4742fc,0xf40f7342f4750e474a,0xe9f48e4742e7730e77,0x2ae7330e732ae7330d,0x7326d4752c8f4cc474,0x6c7726cc722c7552c7,0x352c4352c7b30c4742,0xb7552b7352b474aa77,0x2aa7552a7352a434aa,0xcb40acf309cf2a9cf2,0x29cb509cb4a9cb429c,0xb309cb2a9cb229cb02,0x9caa29730677750647,0x506774a6474a69f486,0x7744647446cf406735,0x6734a673446733067,0x35057346573305732a,0x573265755247352447,0x523474a347463772a3,0x772637552373523435,0x23732a373263475228,0x74e247462772627552,0x2735224352273262b3,0x42474a1772a175521,0x73521434a1732a1cb5,0xcb4a0cb460cb300c,0xb2a0cb260cb0a0cb06,0xcaa605b4361351513,0x4b5134553f4145f294,0x5f293534d2234d2134,0x721343213511134b11,0x343113510134701742,0xf3f40f4f30f2f48e27,0x4cc6722c1552c1552b,0x1152b1552a1152a974,0x893f4296f309a72696,0xb309a2a69aaa49a262,0x913508134a81344813,0x507134a71346717506,0x174a65f4862f486174,0x466f4063f406175051,0x746567425374251352,0x417523135231f4e213,0x521bf4206f2606b260,0xaaa40baa20034d20f4,0x86fffffeffdffcffbf,0xfaff6feffeefbff7fe,0xffdffdfedfddefdbfc,0xffbffbfebfdbefbbfb,0x7f9ff9ef9bfe5130e4,0x5306453060530e6120,0xe4d20e45206612064d,0x20645206052054d204,0xc5204c120e4d10e491,0x64d106491060d1060,0x910549104c91048110]) else (if j<2 then (d0 [0x8542afd71e6b00,0x1ba52f32a1711238e,0xbf7ff5900019256fc8,0x4a20ef8022451fe210,0xc4033a489fdf9a32a0,0x1aa54ff9d546c4023a,0x546f1303b14a434fce,0x22a254693f9219251f,0xbcaa48401349667f57,0xb89f3fe98dc219880,0x15dac77dd6892bf5c0,0x388c3f133a27438613,0x2019fe5cc0e147f0fb,0x81c46c3c7ae0468c7d,0x61fab89efc9a20b945,0xf7db09027299ff02a4,0x8006894bfea2802c8f,0x3f1be002a8f332078e,0xa32ff5c000511f31a0,0xb1ccefe85a2d7961c8,0x2b662e4de5e459002,0x15ab33f9a10046cf3f,0x5cf8161c2400c93b7e,0x7ff8030db40189377f,0xffed4918b201a5317f,0xcd41f4058903e67a02,0x346effdd5880035684,0xd3f9680000a344ebcf,0xfc1a9230090027505f,0xe3cdf4015486fe2d56,0x48b317a7c7e7088e67,0xa4e4bc4488f684f0a1,0xf860910bb4d70cb400,0x95997f1baf9001e124,0xb0f3eb22d957d7a4fb,0x3604da00e4a1bff381,0x38f3400992e312f6b4,0x634373e862800568,0xc0fc300699718c9f10,0xa85d5deeeeb0c48001,0x272fbb11e3d8c1a008,0x49c7eff1005ca03a05,0xd3c32ccf9e768b0466,0x4ff587950000099a7b,0xba7b4b248f21b23238,0xfe78c0c0200744b1fc,0xf181804008e963f9e3,0x3008011d2c03ff113,0xdcd30024b5c7c21267,0xd400396acf8d1467d4,0x396a9848fac44014,0x92e381f10c01e3467f,0xe3c48a0600786a4f3d,0xb1cfb1801e1a80bff7,0xc70808185a833c3f1,0xc202021698fcf40c02,0x536a3f3c00d13af,0xfff8a5820029a52f5f,0xebf0288010696741a0,0x795af234006349def9,0xa522a0049a61ff5b0e,0x10922aec71c001c669,0xfc002245ef98f9680c,0xc00ced41dff8c0c060,0x1769affd2450c04008,0x26a5e56be300052495,0xcfea000d23bbeb8000,0x550c741a070ed79f8,0x310000093597c32d02,0x12b3cf88830004c92,0x3f903a5200784abfa7,0x6451bf1534b40874,0x99fc385c000d095b5f,0xbe3dc202053a5df9f4,0x9c004e591fad02c44,0x10cd23bf0a80751ce,0x8340ebcac7cba01512,0x47d99402c8fbf106d2,0x159247ff1fca10401,0x892a7caff002802125,0x47e4fed141d8ae7f43,0xfc6c01c91b1d781040,0x24929b3fb454233f51,0xc01a33cae7f000891,0xdf7a0d039fce00289c,0xfe700144ebfea7fef0,0x202002499313ffd005,0x51d7958f1e400634a0,0xfcfe7b0990a05a47df,0xc294020039a61fce00,0x689df7a0d0387c5d40,0x892a1f8e2740600492,0x5cf63660c00324b8ff,0xb4301831671de3fc09,0x801849c2604080631a,0x2204f21b47e02200ae,0x11603224341a6060f8,0x671591c138c0820861,0x304246e198d455064b,0xc0e2891284041452a6,0x49e150060104911c46,0xc0e81204844240e120,0x31e183648017096800,0xa0b9214370e9330fc3,0x34103b20d03c09020b,0x82f08d0726d800782d,0x702c6041b8350d0cb,0x5044266103000c020,0x901f2082782805e118,0x603e83280220ac9906,0x290582a0698942810,0x7607e14210301502a,0x8604813a11850500dc,0x128260b82a170660c0]) else (d0 [1657,0x3eb688648959a83db8,0x4618641099a63c740e,0x409a479934f3f32142,0x90c86effccaac81b30,0x7b7ad10a01a00b4fa2,0xe200b4216d680b684c,0xe5ebac8ab347f659b6,0xea4ab9476bced6888f,0x666748473d1c6577aa,0x891a102bc9cbc82839,0x626a2f0aef5902b0fa,0x5903fcca8341971d13,0xa6892886c51cd17aea,0xa181e5210518597053,0xa3085c82bba533230d,0x968c235503e7852cdd,0xe12e1054384cd36f5e,0xb152d5087ad577bd96,0x597053a3080979abed,0x48861dedce22cd7131,0x88a3e3bdc0e231cdb9,0x82328bd93305e50bff,0xd5a740f240ff5b6202,0x548eed6ff3ec600186,0x98388e3e6cc0174a8b,0xdfe00ea3484bdfe00f,0x242e7f00051187dfe6,0x16476edd4664dfcf,0xa9e00112433962690c,0x854a571ef6d0d675fe,0x78800aa3edfa000b23,0xd7fdb183000027699f,0xce2e13a8dd40871d0b,0x66dffb7e8002c913f9,0xe1c2751a7ffff8deb8,0x9168800e69c7ee4384,0xa0a674f18005c900e,0xac208342861fe3c000,0xd51f7ef000354795fa,0xe01c46087df3b2574e,0xb8c98cac0186ad82cd,0x9fc363b400013b4b39,0x3d9885c2bead62e10f,0x8ad85013bfde0002a8,0xf34efe348b35f78103,0x11c08e9b3a901543f6,0x5f0da0488095a64ff2,0x3f0c000592b3ffa384,0x40073457cb1ac01d66,0xaf973090005ed03ffd,0x2f00016486e9100d0b,0x669f32a37d4001152d,0x3fccc050014686f84b,0xf5c048000d5abbf949,0xbe800056699ff97e88,0x2e480f2ccc78c64f8])))
def q53 (j : Nat) : Nat:=(if j<1 then (d0 [0x931828049fe42b,0xc283841e02d972182e,0x205d00b1c0aa0a6ea5,0x80092e0644ad55c4d2,0x84a03880fc040b33d8,0x10027941c054eef7,0x4e2c00016b94095ca3,0x29413025e03495f800,0x2ab801520a3400000,0x2022117f04980000,0x1c8a00000068429,0x1a8000160d000001b,0x7817007c6f40000100,0x3c03420dd023d02890,0x3294fe8079a28da44e,0x527413c0003b160029,0xd8ee000346776bd00e,0x3912003ea0464207ad,0x400060e5416684f00,0x6894c0f5dcc42336,0x13e02400001b206136,0xc1c182f488ce07302a,0xe84a8449c0e81eab21,0xf70a1e00c406c85a91,0xbe431803e824b68c8,0x96f913938c80cf,0x8213c08c0004943412,0x68052054609952d400,0x1b86406c1a0e52540,0x2f4121438564241a,0x148e880911406ce16e,0x1c2214031e01c9d4,0xc224a004a0495e9715,0x160310e5f028881b40,0xa2cc23003785603a08,0x28c42a685a462f0037,0x81758258077e0d0c04,0xa80ec000212c403100,0xce81ad720489282984,0x1aa14ac05f01f1080e,0x67c2c80002b116525,0xc81a0001028211d42b,0x4903204fa0400001dc,0x8d30040ec829b5c900,0x57a0ff415a1c1209de,0x111d2cb821609be13f,0x418d02db210887f081,0xd82de203a16101e984,0x41048813d89ef5c2b2,0x904c7fc9b95c266813,0x70b41c801fd0b780bc,0xc9bb8168000012182c,0xa22a3202000089c2a0,0x110914172402dbd604,0x516008000b831caa30,0x62d0a0a256e76d2d6d,0x883470ad8000000,0x4813064c2869025a2,0x7d47ee900c0c200030,0x20c0b2e5eea2040000,0x14e01e6911d097cf72,0xca5795040005077000,0x15c654578803000103,0xe407380000100015b3,0x172af9000000027a8e,0xb48a0600020666b00,0x2e2a857cb0c6052d94,0x1d370058c039c13a01,0x200869530e0bcbd777,0x6c6100025c03c04104,0x146c1c4a51945ac8c5,0x19704c922c972c81f,0x601e7074800040993d,0x1001fc0f251aa043c7,0x79494c5cf1113409a2,0x27c143316d062e8ac,0x230825e20bae8e009,0x50156034c076ee1004,0x571a0ee8dd2801cf67,0x7c68a7e621dc3d779c,0x112021da1ef0b32942,0x80bc820c000085841e,0x3985c441e08d95f502,0x9c01ee00641b9008d2,0x70495f02d181830ab0,0x948c2e0043105cf56c,0x1fca0170420124480,0x621e388d416d087e53,0xcf047c0d6805c91184,0xae4f3e96c82286822,0x130ae662bdb02e806e,0x156002db938000517,0x6000aa22a139807c98,0x8e08b8135822635b96,0x2e0240113090002813,0x2a04800181b0341038,0x78101800004502617,0x8408a48070000404,0x484c1607191205e73,0x1200418002280d404b,0x409016b9100841608,0x70800008040082a20,0x68497e8d02c84020e,0xb0dc0208010f4441c,0xa8186687148001608,0x28a04411148088e3c,0x500c0a12050147420,0x301c1c1604804642b,0x10193a00018081201,0x1500c0e0b148183a0a,0x1c024604800120e,0x80241c2f00884fa73,0x60a400040f0000000,0xf80407010100048]) else (d0 [4,0x3d05cc06901278235,0x42c000484dc112014,0x6043a0d5414a141a40,0x9c08280cd01614b420,0x434a1d02534a4c0e10,0x23f047000040c0c176,0xb1e000d251881cd031,0x3008642381fa836b7b,0x5805942d981bd14101,0x62c1ee221e0ae81385,0xe82c308de5460293,0x83d404e60fa002f83b,0x409980004159853f57,0xfaca104fe80c8b0cc1,0x480a7011c23e609b4,0xe4023a09d2057c20c,0x837d061a4fb82ce097,0x502fe128405a204400,0x2b806b810b03bc0,0xeb01a700c6027c12be,0xe283a9407b457082a0,0x81ab44f015e0000325,0xc066801941bd95b3b8,0x892fa6c82002a07741,0x84059a213082a1192,0x29b15c4026e52a52bd,0x38c4a38f57828e520,0xe01360ce029782fda7,0xc467c4022a31d28a68,0x3900013a05022402ac,0x28494020432114c0d6,0x82b80004003404982e,0x345f609a510c000229,0x20c9442800003094d3,0x2692c880740ae216b4,0x24258a05f481402c1,0xb36c0a88000c18484c,0x60756081800e8116b1,0x1971a5ad6022c0270c,0x6200009a6203c612dc,0x22d31e800064b841b1,0x829207e0000c0e8d2f,0x706ba070ae0500a30a,0xa60750194bd5a0aaa0,0xc100600221091a0a38,0x84f00840a6407b8040,0xc5a40b6945c494805,0x506414f6eac6015000,0x4098d83a82d604640,0x3a412000030850000c]))
def v53 (j : Nat) : Nat:=(d0 [33553795,0x40260acff0e695c049,0x961e62b073fe4c0161,0x41fe7000114a5dffad,0x88930b3f9cc984002f,0xb5f5c41d0287ff9b1,0x146197fcf308402655,0x7f2fd08004a1607ffb,0x22804a15b7b883a051,0x7e79a0c051961fdc26,0x50006565f397220392,0xbbf61c200251597fd3,0x800c50edf80c0eff6c,0x42184bff980a812ec0,0x2a04ada80c20de782b,0x849387810f730d4217,0xa60040a67f00a40b4f,0xe2128147eb4e000c52,0xb0ec3464260a09054,0x395c884403f158243e,0x1c0206832990b06214,0x830d81a0a350383509,0x6c32190589c24110a,0xac28220f82c1e0701,0x2b63b45b865015ebb9,0xd6f2d318c2e255ca29,0x2b2243e6708cc1782a,0x44b0870f119c2d04a8,0x7309e0b00046468c0d,0x3986726ce458cc3193,0x6322c6058a9b131632,0x646488c1918222a444,0xc85ca47918f309e4d3,0xc8a5985a609e4c3c90,0x5930b2434801ca5fff,0xff7efbff7bd3048110])
def p53 (j : Nat) : Nat:=(d0 [265,0x4021e25e00490cc0ac,0xe241c14ea5b890b0ce,0x4298000832c095c012,0x604024e007811fbc09,0x10205b0dd801f0a440,0xd42547e000140302,0x12032800b034c2060d,0x69b5a0978268000589,0x140600032b10000000,0x8b2fab200000d44af1,0x255010873a14ad051c,0x28000026d08c41050,0x5f9d0109981104a682,0xc000503b250000000,0x11fe0bcc294000ed6,0xf05e09290c28180030,0x322b4242b4a41aa,0x2b0c2ea7d4022f478c,0x4e5a20593801e40530,0x9f8093a598e09050c0,0x8508880140cf9295bc,0x51242010000306f000,0x20d39f3f5a09200109,0x40d604c428a0699e1e,0x4afdecb10bd28f0bdc,0x27b098d509009404f1,0x3fa501027022801703,0x4b02d9ddf0b980f506,0xd5a1002f59430be000,0x3422c1f4000c18a016,0x412b4aec95213a40de,0xd7c914476ed246bd0,0x1b4ee82a4970a300,0xbb402d77dc32595644,0x7b07e14b50c4011743,0x2ce01510d9356c96,0x41b30000275003b59d,0x524c05490b97a20b00,0xc1d6076c1ba0828,0x60a802d30396b1e0,0x860c2200d989b48581,0xd07942c164b8acb05,0x943010c6c1fea5f9d0,0x44770c0804d45f1096,90648696867061761,0x8c170000aa40908d,0x8fc028000107880fb0,0x4800e30d1d09800000,0x30cd8248000000302,0x58184000413c00040f,0xdb5fdc93bc8919f64d,0x3057cb84be2bf0002,0x8eeb12a58806831e0,0x204641f107429dc0,0x19ab2c19d5285bbd40,0x60349029e24d01b106,0x580e97d05e2327701c,0x109d40f0bc719240bf,0x15eb5841c97635123,0xae11e868503428830,0x3a7581ae789415b4,0x79000002c40ec1499a,0xf201ca1432490214b5,0xc226728d01c05a000,0x249e00d903102acb60,0xa0c08f02ac23c,0x447c2db0b2a1610290,0x124498d847b4f83290,0x73c16263a000104e62,0x1b7d6534a0550002bc,0x4107c080000205d493,0xc0001d8848f49da077,0x800c00000000001e08,0x82b1071c4910228,0xb0c000cd437cddcfd0,0x8d000277548e624000,0x30b1c4b4000012eb5,0x501a00000001040c2a,0x42440293000c284000,0xd4852f0b58000c14a,0xc3418f0aa80470664,0x1ee0af00030a341930,0xc700016b2896a15000,0xad82e301bc0aead,0x600cc09c5928000032,0x2067c80c0004098006,0x59300b7290607aca0a,0x1a0d2a400f96464968,0x33020ac2868603570,0x2e02d568382479c15f,0x4d68149990c5010400,0x2921771400253a01a1,0x39b3e122e323b18a5,0x10342351a2a031100,0x632026137025206,0x3112a0e1a181d0665,0x130005003b161e3d02,0x160e02040c03200f01,0x9006d0c0e0801,0xc0201130201070600,0x11f08024b0509070c,0x1c03010b1c0102002c])
def t53 (j : Nat) : Nat:=(d0 [15204865,0x2c8100820040243414,0x10281a1a16120a0e06,0x1f36804c120443ff])
def n53 (j : Nat) : Nat:=(d0 [88629975108428364,0x42410606e07dc,0xc000000001c6854000,0x90200000000c2e00,0x103000000000000000,0x130d6300090c00000,8,0x8c000000083f400000,325318215337728,0x89a002370009ba,0,72304486945147124,545259520,51970396172,0xb0000000000000114,0x80009a001074000000,0x34480000000000,427710023204864,1539309568,0x8348ac2280000084c0,0x2050008640b008001,0x25c0061bc05038a780,0x41200205000000c0c,0,0x397000d961100c4,0x4362122d0052001005])
def s53 (j : Nat) : Nat:=(d0 [4105,0xe08185081808013ff])
def m53 (j : Nat) : Nat:=(d0 [828939035840,0x284000045004a5c,0xc900550000000000,0,0,0x8d0000000000d40000,0x8c00000000009200])
def j41 : Nat → w0
  | 8 => (6,6,7,327686,51,6,4097,sgD8)
  | 9 => (69,5,7,2818098,102,10,4151,sgD9)
  | 10 => (373,4,7,4849791,119,14,4299,x53)
  | 11 => (216,3,7,1769495,85,14,4244,w53)
  | 12 => (30,2,7,327683,50,11,4144,v53)
  | 13 => (3,1,7,65537,0,6,4109,t53)
  | 14 => (1,0,7,65537,0,0,4105,s53)
  | _ => j3
def r45 : Nat → Nat → Option (Nat × Nat)
  | 9 => y4 1 113 0 8 3 3 sgH9
  | 10 => y4 26 127 7 13 7 4 r53
  | 11 => y4 159 691 9 15 9 4 q53
  | 12 => y4 102 467 8 14 8 4 p53
  | 13 => y4 16 163 4 11 5 4 n53
  | 14 => y4 3 59 0 8 2 4 m53
  | _ => fun _ => none
def sg : w1 := ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,j41,r45⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem r25 : q2 mo (j1 pri) = true := by
  simp only [q2, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,r7 (d:=6) ?_⟩,r7 (d:=3) ?_⟩
  all_goals simp only [w5]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem d20 : q2 sg (j1 spri) = true := by
  simp only [q2, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,r7 (d:=6) ?_⟩,r7 (d:=3) ?_⟩
  all_goals simp only [w5]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb9 : d3 mo 9 0 7 :=
  (@m0 mo 9 0 6 1
  (d2 0xce6632990c662)
  (y6 0x31401265))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb10 : d3 mo 10 0 182 :=
  (@m0 mo 10 0 87 95 (@m0 mo 10 0 72 15 (@m0 mo 10 0 5 67
  (g1 (l0 9 0 0))
  (d2 (d0 [35983495,0x43215088321a090242,0x401fcfc000d8a43440,0x1f400003e1ec3219,0xc9e8f2193c1dc5000,0x910408003b0000075,0x200fc3074001cc2412,0x3909c4e710c1c0de6e,0x369b0303f359a8d268]))) (@m0 mo 10 72 1 14
  (g1 (by decide +kernel)) (@m0 mo 10 73 13 1
  (d2 (d0 [1943625080874,0x47a38884446a31168a]))
  (g1 (by decide +kernel))))) (@m0 mo 10 87 52 43 (@m0 mo 10 87 11 41
  (d2 (d0 [39397916,0x4a24c381c490ac562b])) (@m0 mo 10 98 2 39
  (g1 (by decide +kernel))
  (d2 (d0 [0x2bd5cad0012158ab,0xf07404aa548a15047,0x53a9804285281082a4,0x2328d44a15027d3c9d,0x4e26c08044d2653097])))) (@m0 mo 10 139 39 4
  (y6 (d0 [6661424,0x108746a23284b68383,0x65ab401003ba047365,0x6b4010a36b48723746,0x723265613010093655,0x73565a30707868a291,0x9065573314312767b,0x4b8964654b3196891b,0x5ba3654131968786a2,0x108786a2218786a221,0x8786a221929b076156,0x5630708786a2806560,0x309665653096656530,0x96656530967868a291,0x8786a2218786a29114,0xa19010533412715334,0x12715334127113ba04,0x725334127126b43076])) (@m0 mo 10 178 1 3
  (g1 (by decide +kernel))
  (y6 (d0 [7780721,0x21426b234314a59010]))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb11 : d3 mo 11 0 820 :=
  (@m0 mo 11 0 504 316 (@m0 mo 11 0 399 105 (@m0 mo 11 0 112 287 (@m0 mo 11 0 7 105
  (g1 (l0 9 0 0)) (@m0 mo 11 7 96 9
  (g1 (l0 10 0 4))
  (g1 (l0 10 0 0)))) (@m0 mo 11 112 192 95 (@m0 mo 11 112 96 96
  (d2 (d0 [0x92f00402002ed7400,0x40004001300000,0x12d7200000080802,0x20117002010085ab7,0x168b40a05028140a0e,0x70381c0e0007c1c0e,0x160b0584a2504c0201,0x9820261309ad96ab4,0x40041001040201005,0x28140a0b058016649,0x24868000b59068361a,0x28140a05042c410b0]))
  (d2 (d0 [3591,0x66921981e0f32c3c52,0x6507c0c50033240609,0x488812c8148bc0c09,0x48258e216308464c5,0x27800420310b10a215,0x100542ac3610c02a20,0xa880a2c118b006031,0x188c0a02f1793c280c,0x270b800000000000bf,0x5f13402000312c24bd]))) (@m0 mo 11 304 94 1
  (d2 (d0 [0xb2451a8ddc0df,0x1bb78b0dd6e1606837,0x21b6c64571b0306c0c,0x1a95c6c0c04b688c35,0x6c959b0221a154a8d7,0x2a359aa5329b51a6d2,0x68b400ccf6708c0c02,0x10000000000000000,0x58003600118000000,0x8000201008043600,0x11804660003000000b,0x58001008040601000]))
  (g1 (by decide +kernel))))) (@m0 mo 11 399 23 82 (@m0 mo 11 399 2 21 (@m0 mo 11 399 1 1
  (d2 225)
  (g1 (by decide +kernel))) (@m0 mo 11 401 20 1
  (d2 (d0 [31333555744,0x789c1e0f1739dcce5,0x7b91c60f06030b2e2]))
  (g1 (by decide +kernel)))) (@m0 mo 11 422 13 69 (@m0 mo 11 422 10 3
  (d2 (d0 [26674,0x76bb070071c3ac70ea]))
  (g1 (by decide +kernel))) (@m0 mo 11 435 68 1
  (d2 (d0 [537398274,0x1412070203170b901,0x8004400ff000000803,0x23f9fa5b0b3f1f6fa,0x7c82412f87b8582cf6,0xb3d42c0a1d3d0183a,0xa3cde4147883c7409,0x48a8545a2b3c1de39,0xa1385c090a03018ee]))
  (g1 (by decide +kernel)))))) (@m0 mo 11 504 195 121 (@m0 mo 11 504 89 106 (@m0 mo 11 504 5 84
  (d2 275146343483) (@m0 mo 11 509 1 83
  (g1 (by decide +kernel))
  (d2 (d0 [76432673,0x9047e3c000002ca41f,0x8e81e38000f8000417,0x8d85c463b0b80a341d,0x1dc64be5f8c05c0000,0x80517030f40200,0xb800aa428b08a2b14,0x180cbc2489c4a223d,0xe8f03a3c1e168bb10,0x2ec3e1d0d238e4730c,0x85c2a130883c1a0a04])))) (@m0 mo 11 593 3 103 (@m0 mo 11 593 1 2
  (g1 (by decide +kernel))
  (d2 150308)) (@m0 mo 11 596 96 7
  (y6 (d0 [0x8796a2328746,0xa2328746a23214a190,0x103183123214ab9010,0x65ab401076b8612165,0xab301076b8612165a1,0x401070b9a12165ab30,0x1065ab301065ab3010,0x65ab301065ab301070,0xb8a12170b8a1212618,0x3121754b297565ab30,0x1076b8612165a53010,0x65ab301065ab301065,0xab3010658b301065a1,0x301070b8a19170b8a1,0x9170b8a19170b8a191,0x70b8a191133912a213,0x3912a2133912a270b8,0xa19135ab043070b8a1,0x9170b8a19165ab3010,0x765861217658612176,0x58612165ab301065ab,0x301065ab301070b8a1,0x2170b8a121a1b68661,0xa1b6865076b8612176,0x5861213146129270b8,0xa12170b8a12190a055,0x403bb618978796a221,0x8786a2218796a22187,0x96a2218796a2218796,0xa2218796a2218796a2,0x218796a2218796a221,0xa1b68650531a049376,0x58612153ba0493a1b6,0x866153ba04938796a2,0x32531a0493a1b68650,0x76b8612153ba0493a1,0xb6866103ba049353ba,0x49313391292133912,0x9214ab901014ab9010,0x314612323146123231,0x46123214ab901014ab,0x901014ab9010426b23,0x4335ab0440426b2343]))
  (y6 (d0 [135,0x86a2218796a2328796,0xa2328796a2328796a2,0x328796a2328796a232]))))) (@m0 mo 11 699 72 49 (@m0 mo 11 699 40 32 (@m0 mo 11 699 1 39
  (g1 (by decide +kernel))
  (y6 (d0 [11959050,0x8656b6308070b9a121,0x560a3080560a308056,0xa30808786a2218786,0xa2218786a2218786a2,0x21093a55848786a221,0x8786a2218786a22187,0x86a2218786a221093a,0x55848786a2218786a2,0x218786a221a1b78650,0x8786a221754b296487,0x86a2a2a1b78651a1b7,0x8661b67b0a75a1b786,0x518786a2a226193181,0x261931812619318178,0x68a2a226193181b67b,0xa75261931818786a2,0x21b67b0a75a26a2872]))) (@m0 mo 11 739 1 31
  (g1 (by decide +kernel))
  (y6 (d0 [0x754b2964265431,0x21b4a49550b4a49550,0xb4a495508796a221a1,0xb78650a1b78650a1b7,0x865046ba7080a1b796,0x50a1b78651b67b0a86,0xb67b0a86a1b7866187,0x46a23242642343b67b,0xa8665a14010b67b0a,0x86b4a495408796a232,0x319612328796a23287,0x96a232314612323146,0x1232656b3010656130,0x10b464b550b67b0a86])))) (@m0 mo 11 771 4 45 (@m0 mo 11 771 1 3
  (g1 (by decide +kernel))
  (y6 (d0 [10598022,0x61929b07728796a232]))) (@m0 mo 11 775 1 44
  (g1 (by decide +kernel))
  (y6 (d0 [484150682004,0x6475503746723294a4,0x755076b9712176b971,0x2170b8a12165ab3010,0x8785b23270b8a12131,0x85123265a530107058,0xa12170b9a12114ab90,0x1065a5301026593121,0x261931216585301065,0x853010261931212619,0x31218796a2328796a2,0x328796a2328796a232,0x65a0301014a0901065,0xa030102654312165ab,0x401065a5401065a540,0x10a1b6866165a54010,0x65ab401065a5401065,0xab40108796a2326561,0x30108796a23270b9a1,0x2170b9a12114a59010])))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb12 : d3 mo 12 0 386 :=
  (@m0 mo 12 0 311 75 (@m0 mo 12 0 265 46 (@m0 mo 12 0 233 32 (@m0 mo 12 0 62 171
  (g1 (l0 10 0 3)) (@m0 mo 12 62 96 75
  (g1 (l0 11 0 4))
  (g1 (l0 11 0 4)))) (@m0 mo 12 233 10 22
  (d2 (d0 [77,0x13004041f0f87d26])) (@m0 mo 12 243 1 21
  (g1 (by decide +kernel))
  (d2 (d0 [757393528321,0x30180c00000000207,0x3ca423280680c4527]))))) (@m0 mo 12 265 31 15 (@m0 mo 12 265 1 30
  (g1 (by decide +kernel)) (@m0 mo 12 266 29 1
  (d2 (d0 [20617194788352,0,68853957156,0x8040201148cc672a]))
  (g1 (by decide +kernel)))) (@m0 mo 12 296 13 2
  (d2 (d0 [688539720714,0x516c140a128284b2d])) (@m0 mo 12 309 1 1
  (g1 (by decide +kernel))
  (d2 10))))) (@m0 mo 12 311 25 50 (@m0 mo 12 311 14 11 (@m0 mo 12 311 1 13
  (g1 (by decide +kernel)) (@m0 mo 12 312 6 7
  (d2 0x4a0a08040212f)
  (g1 (l0 12 0 0)))) (@m0 mo 12 325 6 5
  (d2 584087983513613) (@m0 mo 12 331 1 4
  (g1 (by decide +kernel))
  (d2 4857161824)))) (@m0 mo 12 336 9 41 (@m0 mo 12 336 1 8
  (g1 (by decide +kernel)) (@m0 mo 12 337 7 1
  (d2 0x402026130982026)
  (g1 (by decide +kernel)))) (@m0 mo 12 345 22 19
  (d2 (d0 [604801862998565,0x680c0603018340603,0x9a97806030180c1a03])) (@m0 mo 12 367 1 18
  (g1 (by decide +kernel))
  (d2 (d0 [49979,0x9d4e671370381c0e07,0x381c7b36038442211])))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb13 : d3 mo 13 0 66 :=
  (@m0 mo 13 0 5 61
  (g1 (l0 9 0 0)) (@m0 mo 13 5 18 43
  (g1 (l0 10 0 1))
  (g1 (l0 11 0 3))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb14 : d3 mo 14 0 9 :=
  (g1 (l0 10 0 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hb15 : d3 mo 15 0 1 :=
  (g1 (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem f42 : t4 mo 15 := by
  intro k hk
  interval_cases k
  · exact p0 mo 0 0
  · exact p0 mo 1 0
  · exact p0 mo 2 0
  · exact p0 mo 3 0
  · exact p0 mo 4 0
  · exact p0 mo 5 0
  · exact p0 mo 6 0
  · exact p0 mo 7 0
  · exact p0 mo 8 0
  · exact hb9
  · exact hb10
  · exact hb11
  · exact hb12
  · exact hb13
  · exact hb14
  · exact hb15
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem t45 : z1 sg 8 0 6 = true :=
  (l0 9 0 0)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s45 : z1 sg 9 0 69 = true :=
  (@j2 sg 9 0 21 48
  (l0 9 0 2)
  (l0 10 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem p41 : z1 sg 10 0 373 = true :=
  (@j2 sg 10 0 131 242 (@j2 sg 10 0 3 128
  (l0 9 0 0)
  (l0 10 0 4)) (@j2 sg 10 131 111 131
  (l0 10 0 4) (@j2 sg 10 242 128 3
  (l0 11 0 4)
  (l0 11 0 0))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem n41 : z1 sg 11 0 216 = true :=
  (@j2 sg 11 0 64 152 (@j2 sg 11 0 2 62
  (l0 9 0 0)
  (l0 10 0 3)) (@j2 sg 11 64 123 29
  (l0 11 0 4)
  (l0 12 0 2)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem m41 : z1 sg 12 0 30 = true :=
  (@j2 sg 12 0 1 29
  (l0 9 0 0) (@j2 sg 12 1 12 17
  (l0 10 0 1)
  (l0 11 0 1)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem l41 : z1 sg 13 0 3 = true :=
  (l0 10 0 0)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem k41 : z1 sg 14 0 1 = true :=
  (l0 9 0 0)
set_option maxHeartbeats 0 in
theorem h41 : l4 sg 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : z1 sg 0 0 0 = true)
  · exact (rfl : z1 sg 1 0 0 = true)
  · exact (rfl : z1 sg 2 0 0 = true)
  · exact (rfl : z1 sg 3 0 0 = true)
  · exact (rfl : z1 sg 4 0 0 = true)
  · exact (rfl : z1 sg 5 0 0 = true)
  · exact (rfl : z1 sg 6 0 0 = true)
  · exact (rfl : z1 sg 7 0 0 = true)
  · exact t45
  · exact s45
  · exact p41
  · exact n41
  · exact m41
  · exact l41
  · exact k41
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem d42 : v0 false q13 15 inputs.toFinset := by
  rw [show q13 = m3 mo by decide +kernel]
  exact p23 (g:=mo) (top:=15) (i:=0) (n0 pri vpri) r25 f42 (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem y32 : v0 true q13 14 inputs.toFinset := by
  rw [show q13 = m3 sg by decide +kernel]
  exact j20 (g:=sg) (top:=14) (i:=0) (n0 spri l53) d20 h41 (by decide) (by decide +kernel)
def s6 : List Sig := inputs ++ [zero]
def h20 (r : Row) (i : Fin 10) := bit r (s6.getD i.val zero)
def fullEdge (x1 : Fin 10 → Bool) := x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem w13 : ∀ r : Row, List.ofFn (h20 r) = s6.map (bit r) ∧
    h20 r 9 = false ∧ fullEdge (h20 r) = bit r q13 := by decide +kernel
theorem w16 {u T k S} (run : Live u T k S) : ∀ a ∈ S, n3 a := by
  induction run using Live.ind with
  | stop hp => simpa using hp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    intro v h
    rcases Finset.mem_insert.mp h with rfl|h
    · exact ha
    rcases Finset.mem_insert.mp h with rfl|h
    · exact hb
    exact ih _ (Finset.mem_insert_of_mem h)
theorem sliceCore (C : Circuit) (j : Nat) (sign u : Bool)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : u = false → ∀ g ∈ C.gates, isNot g = false)
    (count : C.gates.countP (fun g => !isNot g) ≤ if u then 14 else 15)
    (computes : ∀ x : Fin 10 → Bool, x 9 = false →
      (if sign then !(C.wires (List.ofFn x)).getD j false else (C.wires (List.ofFn x)).getD j false) = fullEdge x) : False := by
  let T := if sign then neg q13 else q13
  have goalEq : (f15 C.gates s6).getD j zero = T := by
    apply d7
    intro r
    rw [← w43, d26 _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (s6.map (bit r))).getD j false = bit r T
    rw [← (w13 r).1]
    have h := (computes _ (w13 r).2.1).trans (w13 r).2.2
    cases sign
    · exact h
    · change _ = bit r (neg q13)
      rw [y11]
      simpa using congrArg Bool.not h
  let Z := nrm u T
  have casesZ : Z = q13 ∨ (u = false ∧ Z = neg q13) := by
    cases u <;> cases sign <;> decide +kernel
  have hp : n3 Z := by
    rcases casesZ with h | ⟨_, h⟩ <;> rw [h] <;> unfold n3 <;> decide +kernel
  have out := g17 (u := u) (f15 C.gates s6) j
  rw [goalEq] at out
  change j5 _ Z at out
  obtain ⟨k, S, hk, run, hsub⟩ := b47 C.gates s6 legal mono hp (out.resolve_right (fun h => h hp))
  have initialPlain : s6.all d4 = true := by decide +kernel
  rw [b36 initialPlain] at hsub
  have sub : ∀ a ∈ S, a ∈ inputs := by
    intro a h
    have mem := hsub a h
    simp only [s6, List.mem_append, List.mem_singleton] at mem
    exact mem.resolve_right (w16 run a h).1
  rcases casesZ with hz | ⟨hu, hz⟩
  case inr =>
    rw [hz] at run
    obtain ⟨a, ha, hi, _⟩ := n10 run hu (r := 0) (s := 511) (by decide +kernel) (by decide +kernel)
    have p : inputs.all d4 = true := by decide +kernel
    have h := List.all_eq_true.mp p a (sub a ha)
    simp [d4, hi] at h
  rw [hz] at run
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [← d22] at ha
    exact List.mem_ofFn.mp ha
  have eqS : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i, rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply v8 run inputs (inputs.getD i.val zero) sub (m13 i) (d12 i)
        (y13.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := idx v hv
      apply y13.2 i j
      rintro rfl
      exact hn rfl
  rw [eqS] at run
  cases u
  · exact d42 k (hk.trans count) run
  · exact y32 k (hk.trans count) run
lemma t7 {α : Type*} (l r : List α) (d : α) {i : Nat} (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := List.getD_append l r d i h
lemma f8 {α : Type*} (l r : List α) (d : α) {i : Nat} (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := List.getD_append_right l r d i h
lemma gDef {α : Type*} (l : List α) (d : α) {i : Nat} (h : l.length ≤ i) :
    l.getD i d = d := List.getD_eq_default l d h
lemma k7 (x : Fin 10 → Bool) (i : Nat) :
    (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; split_ifs <;> simp
lemma d19 (b fl v t : Bool) (h : (if b = true then !(xor v fl) else xor v fl) = t) :
    (if xor b fl = true then !v else v) = t := by cases b <;> cases fl <;> cases v <;> simpa using h
structure SGate where
  op : Bool
  i1 : Nat
  n1 : Bool
  i2 : Nat
  n2 : Bool
def sEv (g : SGate) (f : Nat → Bool) : Bool :=
  let a := xor (f g.i1) g.n1
  let b := xor (f g.i2) g.n2
  if g.op then a || b else a && b
def h6 (w : List Bool) (g : SGate) : List Bool := w ++ [sEv g (fun i => w.getD i false)]
def sRun (gs : List SGate) (l : List Bool) : List Bool := gs.foldl h6 l
lemma f5 (g : SGate) (gs : List SGate) (l : List Bool) : sRun (g :: gs) l = sRun gs (h6 l g) := rfl
lemma k12 (gs hs : List SGate) (l : List Bool) : sRun (gs ++ hs) l = sRun hs (sRun gs l) := by
  simp [sRun, List.foldl_append]
lemma x13 (gs : List SGate) : ∀ l : List Bool, (sRun gs l).length = l.length + gs.length := by
  induction gs with
  | nil => intro l; simp [sRun]
  | cons g gs ih => intro l; rw [f5, ih]; simp [h6]; omega
lemma t14 (gs : List SGate) : ∀ (l : List Bool) (i : Nat), i < l.length → (sRun gs l).getD i false = l.getD i false := by
  induction gs with
  | nil => intro l i _; rfl
  | cons g gs ih =>
    intro l i h; rw [f5, ih _ _ (by simp [h6]; omega)]; exact t7 l _ false h
lemma m35 (gs : List SGate) (l : List Bool) (p : Nat) (hp : p ≤ gs.length) (i : Nat) :
    (sRun (gs.take p) l).getD i false = if i < l.length + p then (sRun gs l).getD i false else false := by
  have hs : sRun gs l = sRun (gs.drop p) (sRun (gs.take p) l) := by rw [← k12, List.take_append_drop]
  have hl : (sRun (gs.take p) l).length = l.length + p := by rw [x13]; simp; omega
  split_ifs with h
  · rw [hs, t14 (gs.drop p) _ _ (by omega)]
  · exact gDef _ false (by omega)
lemma h25 (gs : List SGate) (l : List Bool) (p : Nat) (hp : p < gs.length) :
    (sRun gs l).getD (l.length + p) false = sEv gs[p] (fun i => (sRun (gs.take p) l).getD i false) := by
  have hs : sRun gs l = sRun (gs.drop (p + 1)) (h6 (sRun (gs.take p) l) gs[p]) := by
    conv_lhs => rw [← List.take_append_drop p gs, List.drop_eq_getElem_cons hp]
    rw [k12, f5]
  have hl : (sRun (gs.take p) l).length = l.length + p := by rw [x13]; simp; omega
  rw [hs, t14 _ _ _ (by simp [h6]; omega)]
  unfold h6; rw [f8 _ _ false (by omega)]
  have : l.length + p - (sRun (gs.take p) l).length = 0 := by omega
  rw [this]; rfl
def sPos (gs : List SGate) : Prop := ∀ g ∈ gs, g.n1 = false ∧ g.n2 = false
def sRd (gs : List SGate) (p w : Nat) : Prop := ∃ hp : p < gs.length, (gs[p].i1 = w ∨ gs[p].i2 = w) ∧ w < 10 + p
def rIdx (k r i : Nat) : Nat := if i = k then r else if k < i then i - 1 else i
def rNeg (k : Nat) (fl : Bool) (i : Nat) (n : Bool) : Bool := if i = k then xor n fl else n
def sMap (k r : Nat) (fl : Bool) (g : SGate) : SGate := ⟨g.op, rIdx k r g.i1, rNeg k fl g.i1 g.n1, rIdx k r g.i2, rNeg k fl g.i2 g.n2⟩
def sEr (gs : List SGate) (m r : Nat) (fl : Bool) : List SGate := gs.take m ++ (gs.drop (m + 1)).map (sMap (10 + m) r fl)
def w9 (gs : List SGate) (u : Nat) (b : Bool) (S : (Fin 10 → Bool) → Prop) : Prop :=
  ∀ x, S x → (if b = true then !((sRun gs (List.ofFn x)).getD u false) else (sRun gs (List.ofFn x)).getD u false) = fullEdge x
def sRem (gs : List SGate) (u : Nat) (S : (Fin 10 → Bool) → Prop) (m r : Nat) (fl : Bool) : Prop :=
  m < gs.length ∧ r < 10 + m ∧
    ((∀ x, S x → xor ((sRun gs (List.ofFn x)).getD r false) fl = (sRun gs (List.ofFn x)).getD (10 + m) false) ∨
      ((∀ p, ¬ sRd gs p (10 + m)) ∧ u ≠ 10 + m ∧ fl = false))
lemma r41 (B : Nat → Prop) (gs : List SGate) :
    ∀ (l l' : List Bool), l.length = l'.length →
      (∀ i, ¬ B i → l.getD i false = l'.getD i false) →
      (∀ p (hp : p < gs.length), ¬ B (l.length + p) →
        (gs[p].i1 < l.length + p → ¬ B gs[p].i1) ∧ (gs[p].i2 < l.length + p → ¬ B gs[p].i2)) →
      ∀ i, ¬ B i → (sRun gs l).getD i false = (sRun gs l').getD i false := by
  induction gs with
  | nil => intro l l' _ h0 _ i hi; exact h0 i hi
  | cons g gs ih =>
    intro l l' hlen h0 hg
    rw [f5, f5]
    apply ih
    · simp [h6, hlen]
    · intro i hi
      unfold h6
      by_cases hil : i < l.length
      · rw [t7 _ _ false hil, t7 _ _ false (by omega)]; exact h0 i hi
      · by_cases hie : i = l.length
        · subst hie
          rw [f8 _ _ false le_rfl, f8 _ _ false (by omega)]
          simp only [Nat.sub_self, hlen, List.getD_cons_zero]
          have h00 := hg 0 (by simp) (by simpa using hi)
          simp only [List.getElem_cons_zero, Nat.add_zero] at h00
          have h1 : l.getD g.i1 false = l'.getD g.i1 false := by
            by_cases hlt : g.i1 < l.length
            · exact h0 g.i1 (h00.1 hlt)
            · rw [gDef _ false (by omega), gDef _ false (by omega)]
          have h2 : l.getD g.i2 false = l'.getD g.i2 false := by
            by_cases hlt : g.i2 < l.length
            · exact h0 g.i2 (h00.2 hlt)
            · rw [gDef _ false (by omega), gDef _ false (by omega)]
          simp only [sEv, h1, h2]
        · rw [gDef _ false (by simp; omega), gDef _ false (by simp; omega)]
    · intro p hp hB
      have hlen1 : (h6 l g).length = l.length + 1 := by simp [h6]
      have hB' : ¬ B (l.length + (p + 1)) := by
        rw [hlen1] at hB; exact (show l.length + (p + 1) = l.length + 1 + p by omega) ▸ hB
      have t := hg (p + 1) (by simp; omega) hB'
      simp only [List.getElem_cons_succ] at t
      exact ⟨fun h => t.1 (by rw [hlen1] at h; omega), fun h => t.2 (by rw [hlen1] at h; omega)⟩
lemma b33 (k r : Nat) (fl : Bool) (A : List Bool) (hA : A.length = k) (val : Bool) :
    ∀ (post : List SGate) (T : List Bool),
      (∀ g ∈ post, (g.i1 = k ∨ g.i2 = k) → r < k ∧ xor (A.getD r false) fl = val) →
      sRun (post.map (sMap k r fl)) (A ++ T) = (sRun post (A ++ val :: T)).eraseIdx k := by
  intro post
  induction post with
  | nil => intro T _; simp [sRun, hA, List.eraseIdx_append_of_length_le]
  | cons g post ih =>
    intro T hpost
    have hlit : ∀ (i : Nat) (n : Bool),
        (i = k → r < k ∧ xor (A.getD r false) fl = val) →
        xor ((A ++ val :: T).getD i false) n = xor ((A ++ T).getD (rIdx k r i) false) (rNeg k fl i n) := by
      intro i n hc
      unfold rIdx rNeg
      by_cases hik : i = k
      · simp only [hik, ↓reduceIte]
        obtain ⟨hrk, hrv⟩ := hc hik
        have hL : (A ++ val :: T).getD k false = val := by
          rw [f8 _ _ false (by omega)]; simp [hA]
        rw [hL, t7 _ _ false (by omega), ← hrv]
        cases A.getD r false <;> cases fl <;> cases n <;> rfl
      · by_cases hlt : k < i
        · simp only [hik, hlt, ↓reduceIte]
          rw [f8 _ _ false (by omega), f8 _ _ false (by omega)]
          obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + j := ⟨i - k - 1, by omega⟩
          have e1 : k + 1 + j - A.length = j + 1 := by omega
          have e2 : k + 1 + j - 1 - A.length = j := by omega
          rw [e1, e2]; rfl
        · simp only [hik, hlt, ↓reduceIte]
          rw [t7 _ _ false (by omega), t7 _ _ false (by omega)]
    have hv : sEv g (fun i => (A ++ val :: T).getD i false) = sEv (sMap k r fl g) (fun i => (A ++ T).getD i false) := by
      simp only [sEv, sMap]
      rw [hlit g.i1 g.n1 (fun h => hpost g List.mem_cons_self (Or.inl h)),
          hlit g.i2 g.n2 (fun h => hpost g List.mem_cons_self (Or.inr h))]; rfl
    have hr := ih (T ++ [sEv g (fun i => (A ++ val :: T).getD i false)]) (fun g' hg' hk' => hpost g' (List.mem_cons_of_mem _ hg') hk')
    rw [List.map_cons, f5, f5]; unfold h6 at hr ⊢; rw [← hv]
    simpa [List.append_assoc] using hr
lemma v27 (gs : List SGate) (m r : Nat) (fl : Bool) (hm : m < gs.length) (hr : r < 10 + m)
    (l : List Bool) (hl : l.length = 10)
    (hc : xor ((sRun gs l).getD r false) fl = (sRun gs l).getD (10 + m) false ∨ ∀ p, ¬ sRd gs p (10 + m)) :
    sRun (sEr gs m r fl) l = (sRun gs l).eraseIdx (10 + m) := by
  have hA : (sRun (gs.take m) l).length = 10 + m := by rw [x13]; simp; omega
  have hs : sRun gs l = sRun (gs.drop (m + 1)) (sRun (gs.take m) l ++ [sEv gs[m] (fun i => (sRun (gs.take m) l).getD i false)]) := by
    conv_lhs => rw [← List.take_append_drop m gs, List.drop_eq_getElem_cons hm]
    rw [k12, f5]; rfl
  have hnew : sRun (sEr gs m r fl) l = sRun ((gs.drop (m + 1)).map (sMap (10 + m) r fl)) (sRun (gs.take m) l) := by
    simp only [sEr]; rw [k12]
  have key := b33 (10 + m) r fl (sRun (gs.take m) l) hA (sEv gs[m] (fun i => (sRun (gs.take m) l).getD i false)) (gs.drop (m + 1)) [] (by
    intro g hg hk
    rcases hc with hc | hd
    · refine ⟨hr, ?_⟩
      rw [m35 gs l m hm.le r, if_pos (by omega), hc]
      have := h25 gs l m hm; rw [hl] at this; exact this
    · exfalso; obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg; rw [List.getElem_drop] at hk
      exact hd (m + 1 + j) ⟨by simp at hj; omega, hk, by omega⟩)
  rw [hnew, hs]; simpa using key
lemma v29 (L : List Bool) (k j : Nat) :
    (L.eraseIdx k).getD j false = L.getD (if j < k then j else j + 1) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]; split_ifs <;> rfl
lemma p17 (gs : List SGate) (u : Nat) (b : Bool) (S : (Fin 10 → Bool) → Prop)
    (m r : Nat) (fl : Bool) (hC : w9 gs u b S) (hR : sRem gs u S m r fl) :
    (sEr gs m r fl).length + 1 = gs.length ∧
    w9 (sEr gs m r fl) (rIdx (10 + m) r u) (if u = 10 + m then xor b fl else b) S ∧
    (sPos gs → fl = false → sPos (sEr gs m r fl)) ∧
    (∀ p w, p ≠ m → w < 10 + m → sRd gs p w → sRd (sEr gs m r fl) (if p < m then p else p - 1) w) := by
  obtain ⟨hm, hr, hcase⟩ := hR
  refine ⟨by simp [sEr]; omega, ?_, ?_, ?_⟩
  · intro x hx
    have hmain := v27 gs m r fl hm hr (List.ofFn x) (by simp) (by
      rcases hcase with hc | ⟨hd, _, _⟩; exact Or.inl (hc x hx); exact Or.inr hd)
    rw [hmain, v29]
    by_cases hu : u = 10 + m
    · simp only [hu, ↓reduceIte, rIdx, hr]
      rcases hcase with hc | ⟨_, hne, _⟩
      · have hxC := hC x hx; rw [hu, ← hc x hx] at hxC
        exact d19 b fl _ _ hxC
      · exact absurd hu hne
    · simp only [hu, ↓reduceIte]
      have hval : (sRun gs (List.ofFn x)).getD (if rIdx (10 + m) r u < 10 + m then rIdx (10 + m) r u
          else rIdx (10 + m) r u + 1) false = (sRun gs (List.ofFn x)).getD u false := by
        by_cases hlt : 10 + m < u
        · have : rIdx (10 + m) r u = u - 1 := by simp [rIdx, hu, hlt]
          rw [this, if_neg (by omega)]; congr 1; omega
        · have : rIdx (10 + m) r u = u := by simp [rIdx, hu, hlt]
          rw [this, if_pos (by omega)]
      rw [hval]; exact hC x hx
  · intro hpos hfl g hg
    simp only [sEr, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hpos g (List.mem_of_mem_take hg)
    · obtain ⟨h1, h2⟩ := hpos g0 (List.mem_of_mem_drop hg0); simp [sMap, rNeg, h1, h2, hfl]
  · intro p w hpm hw hrd
    obtain ⟨hp, hwe, hwl⟩ := hrd
    by_cases hlt : p < m
    · simp only [hlt, ↓reduceIte]
      refine ⟨by simp [sEr]; omega, ?_, hwl⟩
      have : (sEr gs m r fl)[p]'(by simp [sEr]; omega) = gs[p] := by
        simp only [sEr]; rw [List.getElem_append_left (by simp; omega)]; simp
      rw [this]; exact hwe
    · simp only [hlt, ↓reduceIte]
      have hpm' : m < p := by omega
      refine ⟨by simp [sEr]; omega, ?_, by omega⟩
      have : (sEr gs m r fl)[p - 1]'(by simp [sEr]; omega) = sMap (10 + m) r fl gs[p] := by
        simp only [sEr]; rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_drop]; congr 2; simp; omega
      rw [this]; simp only [sMap]
      have hw' : rIdx (10 + m) r w = w := by simp [rIdx, Nat.ne_of_lt hw, Nat.not_lt.mpr hw.le]
      rcases hwe with h | h
      · exact Or.inl (by rw [h, hw'])
      · exact Or.inr (by rw [h, hw'])
lemma s14 (gs : List SGate) (S : (Fin 10 → Bool) → Prop) (w : Nat) (c : Bool)
    (hw : ∀ x, S x → (sRun gs (List.ofFn x)).getD w false = c) (p : Nat) (hp : sRd gs p w) :
    (∃ c', ∀ x, S x → (sRun gs (List.ofFn x)).getD (10 + p) false = c') ∨
    (∃ (hp' : p < gs.length) (y : Nat) (fl : Bool), y < 10 + p ∧ y ≠ w ∧ (sPos gs → fl = false) ∧
      ((gs[p].i1 = w ∧ gs[p].i2 = y ∧ gs[p].op = !(xor c gs[p].n1) ∧ fl = gs[p].n2) ∨
       (gs[p].i1 = y ∧ gs[p].i2 = w ∧ gs[p].op = !(xor c gs[p].n2) ∧ fl = gs[p].n1)) ∧
      ∀ x, S x → xor ((sRun gs (List.ofFn x)).getD y false) fl = (sRun gs (List.ofFn x)).getD (10 + p) false) := by
  obtain ⟨hp', hwe, hwl⟩ := hp
  have hval : ∀ x : Fin 10 → Bool, (sRun gs (List.ofFn x)).getD (10 + p) false =
      sEv gs[p] (fun i => if i < 10 + p then (sRun gs (List.ofFn x)).getD i false else false) := by
    intro x
    have h1 := h25 gs (List.ofFn x) p hp'; simp only [List.length_ofFn] at h1
    rw [h1]; simp only [sEv, m35 gs (List.ofFn x) p hp'.le, List.length_ofFn]
  have aux : ∀ (op a b : Bool), op = !a → (if op then a || b else a && b) = b := by decide
  have auxC : ∀ (op a b : Bool), op ≠ !a → (if op then a || b else a && b) = op := by decide
  rcases hwe with h1 | h2
  · by_cases heq : gs[p].i2 = w
    · left; refine ⟨if gs[p].op then xor c gs[p].n1 || xor c gs[p].n2 else xor c gs[p].n1 && xor c gs[p].n2, fun x hx => ?_⟩
      rw [hval x]; simp only [sEv, h1, heq, hwl, ↓reduceIte, hw x hx]
    · by_cases hpass : gs[p].op = !(xor c gs[p].n1)
      · by_cases hy : gs[p].i2 < 10 + p
        · right; refine ⟨hp', gs[p].i2, gs[p].n2, hy, heq, fun hpos => (hpos gs[p] (List.getElem_mem hp')).2,
            Or.inl ⟨h1, rfl, hpass, rfl⟩, fun x hx => ?_⟩
          rw [hval x]; simp only [sEv, h1, hwl, hy, ↓reduceIte, hw x hx]
          exact (aux _ _ _ hpass).symm
        · left; refine ⟨xor false gs[p].n2, fun x hx => ?_⟩
          rw [hval x]; simp only [sEv, h1, hwl, hy, ↓reduceIte, hw x hx]
          exact aux _ _ _ hpass
      · left; refine ⟨gs[p].op, fun x hx => ?_⟩
        rw [hval x]; simp only [sEv, h1, hwl, ↓reduceIte, hw x hx]
        exact auxC _ _ _ hpass
  · by_cases heq : gs[p].i1 = w
    · left; refine ⟨if gs[p].op then xor c gs[p].n1 || xor c gs[p].n2 else xor c gs[p].n1 && xor c gs[p].n2, fun x hx => ?_⟩
      rw [hval x]; simp only [sEv, h2, heq, hwl, ↓reduceIte, hw x hx]
    · by_cases hpass : gs[p].op = !(xor c gs[p].n2)
      · by_cases hy : gs[p].i1 < 10 + p
        · right; refine ⟨hp', gs[p].i1, gs[p].n1, hy, heq, fun hpos => (hpos gs[p] (List.getElem_mem hp')).1,
            Or.inr ⟨rfl, h2, hpass, rfl⟩, fun x hx => ?_⟩
          rw [hval x]; simp only [sEv, h2, hwl, hy, ↓reduceIte, hw x hx]
          have aux2 : ∀ (op a b : Bool), op = !b → (if op then a || b else a && b) = a := by decide
          exact (aux2 _ _ _ hpass).symm
        · left; refine ⟨xor false gs[p].n1, fun x hx => ?_⟩
          rw [hval x]; simp only [sEv, h2, hwl, hy, ↓reduceIte, hw x hx]
          have aux2 : ∀ (op a b : Bool), op = !b → (if op then a || b else a && b) = a := by decide
          exact aux2 _ _ _ hpass
      · left; refine ⟨gs[p].op, fun x hx => ?_⟩
        rw [hval x]; simp only [sEv, h2, hwl, ↓reduceIte, hw x hx]
        have auxC2 : ∀ (op a b : Bool), op ≠ !b → (if op then a || b else a && b) = op := by decide
        exact auxC2 _ _ _ hpass
lemma j25 (gs : List SGate) (u : Nat) (S : (Fin 10 → Bool) → Prop)
    (hnc : ∃ x x', S x ∧ S x' ∧ (sRun gs (List.ofFn x)).getD u false ≠ (sRun gs (List.ofFn x')).getD u false) :
    ∀ k q c, gs.length - q = k → q < gs.length →
      (∀ x, S x → (sRun gs (List.ofFn x)).getD (10 + q) false = c) →
      ∃ m r fl, sRem gs u S m r fl ∧ (sPos gs → fl = false) ∧ q ≤ m ∧
        (m = q → (∀ p, ¬ sRd gs p (10 + q)) ∧ u ≠ 10 + q) := by
  intro k; induction k using Nat.strong_induction_on with | _ k ih =>
  intro q c hk hq hc
  have hu : u ≠ 10 + q := by rintro rfl; obtain ⟨x, x', hx, hx', hne⟩ := hnc; exact hne (by rw [hc x hx, hc x' hx'])
  by_cases hrd : ∃ p, sRd gs p (10 + q)
  · obtain ⟨p, hp⟩ := hrd
    have hpq : q < p := by obtain ⟨_, _, h⟩ := hp; omega
    rcases s14 gs S (10 + q) c hc p hp with ⟨c', hc'⟩ | ⟨hp', y, fl, hy, _, hpf, _, hcopy⟩
    · obtain ⟨m, r, fl, hR, hpf, hpm, _⟩ := ih (gs.length - p) (by omega) p c' rfl hp.1 hc'
      exact ⟨m, r, fl, hR, hpf, by omega, fun h => by omega⟩
    · exact ⟨p, y, fl, ⟨hp', hy, Or.inl hcopy⟩, hpf, by omega, fun h => by omega⟩
  · push Not at hrd; exact ⟨q, 0, false, ⟨hq, by omega, Or.inr ⟨hrd, hu, rfl⟩⟩, fun _ => rfl, le_rfl, fun _ => ⟨hrd, hu⟩⟩
lemma w27 (gs : List SGate) (B : Nat → Prop) (x x' : Fin 10 → Bool)
    (hx : ∀ i : Fin 10, ¬ B i → x i = x' i)
    (hg : ∀ p i, ¬ B (10 + p) → sRd gs p i → ¬ B i) (u : Nat) (hu : ¬ B u) :
    (sRun gs (List.ofFn x)).getD u false = (sRun gs (List.ofFn x')).getD u false := by
  apply r41 B gs (List.ofFn x) (List.ofFn x') (by simp)
  · intro i hi; rw [k7, k7]; split_ifs with h; exact hx ⟨i, h⟩ hi; rfl
  · intro p hp hB; simp only [List.length_ofFn] at hB ⊢
    exact ⟨fun h => hg p gs[p].i1 hB ⟨hp, Or.inl rfl, h⟩, fun h => hg p gs[p].i2 hB ⟨hp, Or.inr rfl, h⟩⟩
  · exact hu
lemma w45 : ∀ v : Fin 10, ∃ a b : Fin 10, a ≠ v ∧ b ≠ v ∧ fullEdge (fun i => decide (i = a) || decide (i = b)) = true := by decide
lemma v14 : fullEdge (fun _ => false) = false := by decide
lemma n20 : fullEdge (fun _ => true) = true := by decide
lemma q38 : ∀ i : Fin 10, fullEdge (fun j => decide (j = i)) = false := by decide
lemma w41' : ∀ v : Fin 10, ∃ a : Fin 10, a ≠ v ∧ fullEdge (fun i => decide (i = v) || decide (i = a)) ≠ fullEdge (fun i => decide (i = a)) := by decide
lemma z53' : ∀ v w : Fin 10, v ≠ w → ∃ a : Fin 10, fullEdge (fun i => decide (i = v) || decide (i = a)) ≠ fullEdge (fun i => decide (i = w) || decide (i = a)) := by decide
lemma r17 (v : Fin 10) : ∃ x x' : Fin 10 → Bool, x v = false ∧ x' v = false ∧ fullEdge x ≠ fullEdge x' := by
  obtain ⟨a, b, ha, hb, h⟩ := w45 v
  refine ⟨fun _ => false, fun i => decide (i = a) || decide (i = b), rfl, ?_, ?_⟩
  · simp [Ne.symm ha, Ne.symm hb]
  · rw [h, v14]; decide
lemma n17 (gs : List SGate) (u : Nat) (b : Bool) (S : (Fin 10 → Bool) → Prop)
    (hC : w9 gs u b S) (h : ∃ x x', S x ∧ S x' ∧ fullEdge x ≠ fullEdge x') :
    ∃ x x', S x ∧ S x' ∧ (sRun gs (List.ofFn x)).getD u false ≠ (sRun gs (List.ofFn x')).getD u false := by
  obtain ⟨x, x', hx, hx', hne⟩ := h
  exact ⟨x, x', hx, hx', fun heq => hne (by rw [← hC x hx, ← hC x' hx', heq])⟩
lemma g25 (gs : List SGate) (u : Nat) (b : Bool) (hC : w9 gs u b (fun _ => True)) : 10 ≤ u := by
  by_contra h; push Not at h
  have hv : ∀ x : Fin 10 → Bool, (sRun gs (List.ofFn x)).getD u false = x ⟨u, h⟩ := by
    intro x; rw [t14 _ _ _ (by simpa using h), k7]; simp [h]
  cases b
  · have := hC (fun j => decide (j = ⟨u, h⟩)) trivial; rw [hv, q38] at this; simp at this
  · have := hC (fun _ => false) trivial; rw [hv, v14] at this; simp at this
lemma n35 (gs : List SGate) (u : Nat) (b : Bool) (hC : w9 gs u b (fun _ => True)) (v : Fin 10) :
    ∃ p, sRd gs p v := by
  by_contra h; push Not at h; have hu := g25 gs u b hC
  obtain ⟨a, _, hne⟩ := w41' v; apply hne
  rw [← hC _ trivial, ← hC _ trivial]
  have hEq := w27 gs (fun i => i = (v : Nat)) (fun i => decide (i = v) || decide (i = a)) (fun i => decide (i = a))
    (fun i hi => by have : i ≠ v := fun he => hi (by rw [he]); simp [this])
    (fun p i _ hr hi => by rw [hi] at hr; exact h p hr) u (by omega)
  rw [hEq]
lemma l35 (gs : List SGate) (u : Nat) (b : Bool) (v : Fin 10)
    (hC : w9 gs u b (fun x => x v = false)) (p : Nat) (hp : sRd gs p v) :
    ∃ gs' u' b', gs'.length + 1 = gs.length ∧ w9 gs' u' b' (fun x => x v = false) ∧ (sPos gs → sPos gs') := by
  have hnc := n17 gs u b _ hC (r17 v)
  have hwv : ∀ x : Fin 10 → Bool, x v = false → (sRun gs (List.ofFn x)).getD v false = false := by
    intro x hx; rw [t14 _ _ _ (by simp), k7]; simp [v.isLt, hx]
  obtain ⟨m, r, fl, hR, hpf⟩ : ∃ m r fl, sRem gs u (fun x => x v = false) m r fl ∧ (sPos gs → fl = false) := by
    rcases s14 gs _ v false hwv p hp with ⟨c', hc'⟩ | ⟨hp', y, fl, hy, _, hpf, _, hcopy⟩
    · obtain ⟨m, r, fl, hR, hpf, _⟩ := j25 gs u _ hnc _ p c' rfl hp.1 hc'; exact ⟨m, r, fl, hR, hpf⟩
    · exact ⟨p, y, fl, ⟨hp', hy, Or.inl hcopy⟩, hpf⟩
  obtain ⟨h1, h2, h3, _⟩ := p17 gs u b _ m r fl hC hR
  exact ⟨_, _, _, h1, h2, fun hp0 => h3 hp0 (hpf hp0)⟩
def sBad (gs : List SGate) (v : Nat) : Prop :=
  ∃ r, (∀ p, sRd gs p v → p = r) ∧ ∃ hr : r < gs.length, ∃ y, y < 10 + r ∧ y ≠ v ∧
    ((gs[r].i1 = v ∧ gs[r].i2 = y ∧ gs[r].op = !gs[r].n1) ∨ (gs[r].i1 = y ∧ gs[r].i2 = v ∧ gs[r].op = !gs[r].n2))
lemma m38 (gs : List SGate) (u : Nat) (b : Bool) (hC : w9 gs u b (fun _ => True))
    (v : Fin 10) (hgood : ¬ sBad gs v) :
    ∃ gs'' u'' b'', gs''.length + 2 = gs.length ∧ w9 gs'' u'' b'' (fun x => x v = false) ∧ (sPos gs → sPos gs'') := by
  have hu10 := g25 gs u b hC
  have hCS : w9 gs u b (fun x => x v = false) := fun x _ => hC x trivial
  have hnc := n17 gs u b _ hCS (r17 v)
  have hwv : ∀ x : Fin 10 → Bool, x v = false → (sRun gs (List.ofFn x)).getD v false = false := by
    intro x hx; rw [t14 _ _ _ (by simp), k7]; simp [v.isLt, hx]
  suffices H : ∃ m r fl p, sRem gs u (fun x => x v = false) m r fl ∧ (sPos gs → fl = false) ∧ p ≠ m ∧ sRd gs p v by
    obtain ⟨m, r, fl, p, hR, hpf, hpm, hp⟩ := H
    obtain ⟨h1, h2, h3, h4⟩ := p17 gs u b _ m r fl hCS hR
    obtain ⟨gs'', u'', b'', k1, k2, k3⟩ := l35 _ _ _ v h2 _ (h4 p v hpm (by omega) hp)
    exact ⟨gs'', u'', b'', by omega, k2, fun hp0 => k3 (h3 hp0 (hpf hp0))⟩
  by_cases h2 : ∃ p1 p2, p1 ≠ p2 ∧ sRd gs p1 v ∧ sRd gs p2 v
  · obtain ⟨p1, p2, hne, hp1, hp2⟩ := h2
    obtain ⟨m, r, fl, hR, hpf⟩ : ∃ m r fl, sRem gs u (fun x => x v = false) m r fl ∧ (sPos gs → fl = false) := by
      rcases s14 gs _ v false hwv p1 hp1 with ⟨c', hc'⟩ | ⟨hp', y, fl, hy, _, hpf, _, hcopy⟩
      · obtain ⟨m, r, fl, hR, hpf, _⟩ := j25 gs u _ hnc _ p1 c' rfl hp1.1 hc'; exact ⟨m, r, fl, hR, hpf⟩
      · exact ⟨p1, y, fl, ⟨hp', hy, Or.inl hcopy⟩, hpf⟩
    by_cases hm : p1 = m
    · exact ⟨m, r, fl, p2, hR, hpf, by rw [← hm]; exact Ne.symm hne, hp2⟩
    · exact ⟨m, r, fl, p1, hR, hpf, hm, hp1⟩
  · obtain ⟨q, hq⟩ := n35 gs u b hC v
    have huniq : ∀ p, sRd gs p v → p = q := fun p hp => by by_contra hne; exact h2 ⟨p, q, hne, hp, hq⟩
    rcases s14 gs _ v false hwv q hq with ⟨c', hc'⟩ | ⟨hq', y, _, hy, hyv, _, hshape, _⟩
    · obtain ⟨m, r, fl, hR, hpf, hqm, hdead⟩ := j25 gs u _ hnc _ q c' rfl hq.1 hc'
      by_cases hmq : m = q
      · exfalso; obtain ⟨hnr, hune⟩ := hdead hmq; obtain ⟨a, _, hne⟩ := w41' v; apply hne
        rw [← hC _ trivial, ← hC _ trivial]
        have hEq := w27 gs (fun i => i = (v : Nat) ∨ i = 10 + q) (fun i => decide (i = v) || decide (i = a)) (fun i => decide (i = a))
          (fun i hi => by have : i ≠ v := fun he => hi (Or.inl (by rw [he])); simp [this])
          (fun p i hB hr hi => by
            rcases hi with hi | hi
            · rw [hi] at hr; exact hB (Or.inr (by rw [huniq p hr]))
            · rw [hi] at hr; exact hnr p hr)
          u (by rintro (h | h); omega; exact hune h)
        rw [hEq]
      · exact ⟨m, r, fl, q, hR, hpf, Ne.symm hmq, hq⟩
    · exfalso; apply hgood; refine ⟨q, huniq, hq', y, hy, hyv, ?_⟩
      rcases hshape with ⟨ha, hb, hc, _⟩ | ⟨ha, hb, hc, _⟩
      · exact Or.inl ⟨ha, hb, by simpa using hc⟩
      · exact Or.inr ⟨ha, hb, by simpa using hc⟩
lemma t27 (gs : List SGate) (u : Nat) (b : Bool) (hC : w9 gs u b (fun _ => True))
    (hne : 0 < gs.length) (hbad : ∀ v : Fin 10, sBad gs v) :
    ∃ c, ∀ x : Fin 10 → Bool, True → (sRun gs (List.ofFn x)).getD 10 false = c := by
  have hu10 := g25 gs u b hC
  by_cases hrd : ∃ v : Fin 10, sRd gs 0 v
  · exfalso
    obtain ⟨v, hv⟩ := hrd
    obtain ⟨r, huniq, hr, y, hy, hyv, hsh⟩ := hbad v
    have hr0 : r = 0 := (huniq 0 hv).symm; subst hr0
    have hy10 : y < 10 := by omega
    have hyr : sRd gs 0 y := ⟨hr, by rcases hsh with ⟨_, h2, _⟩ | ⟨h1, _, _⟩; exact Or.inr h2; exact Or.inl h1, by omega⟩
    obtain ⟨r', huniq', _, _, _, _, hsh'⟩ := hbad ⟨y, hy10⟩
    have hr'0 : r' = 0 := (huniq' 0 hyr).symm; subst hr'0
    have hsym : gs[0].n1 = gs[0].n2 ∧ gs[0].op = !gs[0].n1 ∧ (gs[0].i1 = v ∧ gs[0].i2 = y ∨ gs[0].i1 = y ∧ gs[0].i2 = v) := by
      rcases hsh with ⟨h1, h2, hop1⟩ | ⟨h1, h2, hop2⟩
      · rcases hsh' with ⟨k1, _, _⟩ | ⟨_, _, kop2⟩
        · exact absurd (h1.symm.trans k1) hyv.symm
        · have hn : gs[0].n1 = gs[0].n2 := by cases hn1 : gs[0].n1 <;> cases hn2 : gs[0].n2 <;> simp_all
          exact ⟨hn, hop1, Or.inl ⟨h1, h2⟩⟩
      · rcases hsh' with ⟨_, _, kop1⟩ | ⟨_, k2, _⟩
        · have hn : gs[0].n1 = gs[0].n2 := by cases hn1 : gs[0].n1 <;> cases hn2 : gs[0].n2 <;> simp_all
          exact ⟨hn, kop1, Or.inr ⟨h1, h2⟩⟩
        · exact absurd (h2.symm.trans k2) hyv.symm
    obtain ⟨a, ha⟩ := z53' v ⟨y, hy10⟩ (fun h => hyv (by subst h; rfl))
    set x : Fin 10 → Bool := fun i => decide (i = v) || decide (i = a) with hxdef
    set x' : Fin 10 → Bool := fun i => decide (i = (⟨y, hy10⟩ : Fin 10)) || decide (i = a) with hx'def
    have key : (sRun gs (List.ofFn x)).getD u false = (sRun gs (List.ofFn x')).getD u false := by
      obtain ⟨g0, rest, hgs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
      subst hgs; simp only [List.getElem_cons_zero] at hsym
      rw [f5, f5]
      apply r41 (fun i => i = (v : Nat) ∨ i = y) rest _ _ (by simp [h6])
      · intro i hi; unfold h6
        by_cases hil : i < 10
        · rw [t7 _ _ false (by simpa using hil), t7 _ _ false (by simpa using hil),
              k7, k7, dif_pos hil, dif_pos hil]
          have h1 : (⟨i, hil⟩ : Fin 10) ≠ v := fun h => hi (Or.inl (by rw [← h]))
          have h2 : (⟨i, hil⟩ : Fin 10) ≠ ⟨y, hy10⟩ := fun h => hi (Or.inr (by have := congrArg Fin.val h; simpa using this))
          simp [hxdef, hx'def, h1, h2]
        · by_cases hi10 : i = 10
          · subst hi10
            rw [f8 _ _ false (by simp), f8 _ _ false (by simp)]
            simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero, sEv]
            have ev1 : (List.ofFn x).getD v false = true := by rw [k7, dif_pos v.isLt]; simp [hxdef]
            have ev2 : (List.ofFn x').getD y false = true := by rw [k7, dif_pos hy10]; simp [hx'def]
            obtain ⟨hn, hop, hpair⟩ := hsym
            have hconst1 : ∀ (op n1 b1 b2 : Bool), op = !n1 →
                (if op then xor true n1 || xor b1 n1 else xor true n1 && xor b1 n1) =
                (if op then xor b2 n1 || xor true n1 else xor b2 n1 && xor true n1) := by decide
            have hconst2 : ∀ (op n1 b1 b2 : Bool), op = !n1 →
                (if op then xor b1 n1 || xor true n1 else xor b1 n1 && xor true n1) =
                (if op then xor true n1 || xor b2 n1 else xor true n1 && xor b2 n1) := by decide
            rcases hpair with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
            · rw [hi1, hi2, ev1, ev2, ← hn]; exact hconst1 _ _ _ _ hop
            · rw [hi1, hi2, ev1, ev2, ← hn]; exact hconst2 _ _ _ _ hop
          · rw [gDef _ false (by simp; omega), gDef _ false (by simp; omega)]
      · intro p hp _
        have hlen1 : (h6 (List.ofFn x) g0).length = 11 := by simp [h6]
        refine ⟨fun hlt => ?_, fun hlt => ?_⟩
        · rw [hlen1] at hlt; rintro (h | h)
          · have := huniq (p + 1) ⟨by simp; omega, Or.inl (by simpa using h), by omega⟩; omega
          · have := huniq' (p + 1) ⟨by simp; omega, Or.inl (by simpa using h), by omega⟩; omega
        · rw [hlen1] at hlt; rintro (h | h)
          · have := huniq (p + 1) ⟨by simp; omega, Or.inr (by simpa using h), by omega⟩; omega
          · have := huniq' (p + 1) ⟨by simp; omega, Or.inr (by simpa using h), by omega⟩; omega
      · rintro (h | h) <;> omega
    apply ha; rw [← hC x trivial, ← hC x' trivial, key]
  · push Not at hrd
    obtain ⟨g0, rest, hgs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
    refine ⟨sEv g0 (fun _ => false), fun x _ => ?_⟩
    have hv := h25 gs (List.ofFn x) 0 hne; simp only [List.length_ofFn, List.take_zero] at hv; rw [hv]
    have hg0 : gs[0] = g0 := by subst hgs; rfl
    rw [hg0]
    have hi1 : ¬ g0.i1 < 10 := fun h => hrd ⟨g0.i1, h⟩ ⟨hne, Or.inl (by rw [hg0]), by simpa using h⟩
    have hi2 : ¬ g0.i2 < 10 := fun h => hrd ⟨g0.i2, h⟩ ⟨hne, Or.inr (by rw [hg0]), by simpa using h⟩
    simp only [sEv, sRun, List.foldl_nil]
    rw [gDef _ false (by simp; omega), gDef _ false (by simp; omega)]
def k8 : Fin 10 → Fin 10 → Fin 10 :=
  ![![9, 6, 8, 5, 7, 4, 1, 3, 0, 2], ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
    ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3], ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
    ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4], ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
lemma x41 : ∀ v : Fin 10, k8 v v = 9 := by decide
lemma z27 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool, ∀ v : Fin 10,
    fullEdge (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] ∘ k8 v) =
    fullEdge ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by decide +kernel
lemma h33 (v : Fin 10) (x : Fin 10 → Bool) : fullEdge (x ∘ k8 v) = fullEdge x := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by funext i; fin_cases i <;> rfl
  rw [hx]; exact z27 _ _ _ _ _ _ _ _ _ _ v
def rlbl (π : Fin 10 → Fin 10) (i : Nat) : Nat := if h : i < 10 then (π ⟨i, h⟩ : Nat) else i
def m17 (π : Fin 10 → Fin 10) (g : SGate) : SGate := ⟨g.op, rlbl π g.i1, g.n1, rlbl π g.i2, g.n2⟩
lemma l38 (π : Fin 10 → Fin 10) (gs : List SGate) :
    ∀ (L L' : List Bool), L.length = L'.length → 10 ≤ L.length →
      (∀ k, L.getD (rlbl π k) false = L'.getD k false) →
      ∀ k, (sRun (gs.map (m17 π)) L).getD (rlbl π k) false = (sRun gs L').getD k false := by
  induction gs with
  | nil => intro L L' _ _ h k; exact h k
  | cons g gs ih =>
    intro L L' hlen h10 h; rw [List.map_cons, f5, f5]
    apply ih
    · simp [h6, hlen]
    · simp [h6]; omega
    intro k; unfold h6
    have hv : sEv (m17 π g) (fun i => L.getD i false) = sEv g (fun i => L'.getD i false) := by
      simp only [sEv, m17, h g.i1, h g.i2]
    rw [hv]
    by_cases hk : k < 10
    · have hr : rlbl π k = π ⟨k, hk⟩ := by simp [rlbl, hk]
      rw [hr, t7 _ _ false (by have := (π ⟨k, hk⟩).isLt; omega), t7 _ _ false (by omega), ← hr]; exact h k
    · have hr : rlbl π k = k := by simp [rlbl, hk]
      rw [hr]
      by_cases hkl : k < L.length
      · rw [t7 _ _ false hkl, t7 _ _ false (by omega)]; have := h k; rwa [hr] at this
      · by_cases hke : k = L.length
        · subst hke; rw [f8 _ _ false le_rfl, f8 _ _ false (by omega)]; simp [hlen]
        · rw [gDef _ false (by simp; omega), gDef _ false (by simp; omega)]
lemma z32 (gs : List SGate) (u : Nat) (b : Bool) (v : Fin 10)
    (hC : w9 gs u b (fun x => x v = false)) :
    (gs.map (m17 (k8 v))).length = gs.length ∧
    w9 (gs.map (m17 (k8 v))) (rlbl (k8 v) u) b (fun x => x 9 = false) ∧
    (sPos gs → sPos (gs.map (m17 (k8 v)))) := by
  refine ⟨by simp, ?_, fun hp g hg => by obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg; exact hp g0 hg0⟩
  intro x hx
  have hrun := l38 (k8 v) gs (List.ofFn x) (List.ofFn (x ∘ k8 v)) (by simp) (by simp) (by
    intro k; by_cases hk : k < 10
    · have hr : rlbl (k8 v) k = k8 v ⟨k, hk⟩ := by simp [rlbl, hk]
      rw [hr, k7, k7, dif_pos (k8 v ⟨k, hk⟩).isLt, dif_pos hk]; rfl
    · have hr : rlbl (k8 v) k = k := by simp [rlbl, hk]
      rw [hr, k7, k7, dif_neg hk, dif_neg hk]) u
  rw [hrun]
  have hxv : (x ∘ k8 v) v = false := by simp [Function.comp, x41, hx]
  rw [hC (x ∘ k8 v) hxv, h33]
lemma q41 (gs : List SGate) (u : Nat) (b : Bool) (hC : w9 gs u b (fun _ => True)) :
    ∃ gs' u' b', (2 ≤ gs.length → gs'.length + 2 = gs.length) ∧ gs'.length ≤ gs.length ∧
      w9 gs' u' b' (fun x => x 9 = false) ∧ (sPos gs → sPos gs') := by
  by_cases hlt : gs.length < 2
  · exact ⟨gs, u, b, fun h => by omega, le_rfl, fun x _ => hC x trivial, id⟩
  · by_cases hgood : ∃ v : Fin 10, ¬ sBad gs v
    · obtain ⟨v, hv⟩ := hgood
      obtain ⟨gs'', u'', b'', k1, k2, k3⟩ := m38 gs u b hC v hv
      obtain ⟨r1, r2, r3⟩ := z32 gs'' u'' b'' v k2
      exact ⟨_, _, _, fun _ => by omega, by omega, r2, fun hp => r3 (k3 hp)⟩
    · push Not at hgood
      obtain ⟨c, hc⟩ := t27 gs u b hC (by omega) hgood
      have hnc := n17 gs u b (fun _ => True) hC (by obtain ⟨x, x', _, _, h⟩ := r17 0; exact ⟨x, x', trivial, trivial, h⟩)
      obtain ⟨m, r, fl, hR, hpf, -⟩ := j25 gs u _ hnc _ 0 c rfl (by omega) hc
      obtain ⟨e1, e2, e3, -⟩ := p17 gs u b _ m r fl hC hR
      obtain ⟨p, hp⟩ := n35 _ _ _ e2 9
      obtain ⟨gs', u', b', f1, f2, f3⟩ := l35 _ _ _ 9 (fun x _ => e2 x trivial) p hp
      exact ⟨gs', u', b', fun _ => by omega, by omega, f2, fun h0 => f3 (e3 h0 (hpf h0))⟩
def h14 (gs : List SGate) : List Gate := gs.map fun g => ⟨if g.op then GateOp.or else GateOp.and, [g.i1, g.i2]⟩
lemma n33 (gs : List SGate) (hpos : sPos gs) :
    ∀ l : List Bool, (Circuit.mk (h14 gs) 0).wires l = sRun gs l := by
  induction gs with
  | nil => intro l; rfl
  | cons g gs ih =>
    intro l; obtain ⟨hn1, hn2⟩ := hpos g List.mem_cons_self
    have hstep : (Circuit.mk (h14 (g :: gs)) 0).wires l = (Circuit.mk (h14 gs) 0).wires (h6 l g) := by
      simp only [h14, List.map_cons, Circuit.wires, List.foldl_cons]; congr 1
      simp only [h6, sEv, hn1, hn2]; cases g.op <;> simp [GateOp.eval]
    rw [hstep, ih (fun g' hg' => hpos g' (List.mem_cons_of_mem _ hg')), f5]
lemma v38 (gs : List SGate) (u : Nat) (b : Bool) (hpos : sPos gs) (hlen : gs.length ≤ 17)
    (hC : w9 gs u b (fun _ => True)) : False := by
  obtain ⟨gs', u', b', h2, hle, hC', hpos'⟩ := q41 gs u b hC
  have hlen' : gs'.length ≤ 15 := by by_cases h : 2 ≤ gs.length; have := h2 h; omega; omega
  have hp' := hpos' hpos
  let C : Circuit := ⟨h14 gs', u'⟩
  have hFT : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg; obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg; cases g0.op <;> simp
  have hmono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg; obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg; cases g0.op <;> simp [isNot]
  have hcnt : C.gates.countP (fun g => !isNot g) ≤ 15 := by
    have := List.countP_le_length (p := fun g => !isNot g) (l := C.gates)
    simp only [C, h14, List.length_map] at this ⊢; omega
  apply sliceCore C u' b' false hFT (fun _ => hmono) (by simpa using hcnt)
  intro x hx; have hw := n33 gs' hp' (List.ofFn x)
  change (if b' = true then !((Circuit.mk (h14 gs') 0).wires (List.ofFn x)).getD u' false
    else ((Circuit.mk (h14 gs') 0).wires (List.ofFn x)).getD u' false) = fullEdge x
  rw [hw]; exact hC' x hx
def mIdx (w : Nat) : Nat := if w < 10 then w else 10 + 3 * (w - 10) + 2
def c18 (k : Nat) (g : SGate) : List Gate :=
  [⟨GateOp.not, [mIdx g.i1]⟩, ⟨GateOp.not, [mIdx g.i2]⟩,
   ⟨if g.op then GateOp.or else GateOp.and, [if g.n1 then 10 + 3 * k else mIdx g.i1, if g.n2 then 10 + 3 * k + 1 else mIdx g.i2]⟩]
def w8 (k : Nat) : List SGate → List Gate
  | [] => []
  | g :: gs => c18 k g ++ w8 (k + 1) gs
lemma q33 (k : Nat) (gs : List SGate) :
    ∀ g ∈ w8 k gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing k with
  | nil => intro g hg; simp [w8] at hg
  | cons g0 gs ih =>
    intro g hg; simp only [w8, List.mem_append, c18, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl | rfl) | hg
    · simp
    · simp
    · cases g0.op <;> simp
    · exact ih (k + 1) g hg
lemma r33 (k : Nat) (gs : List SGate) : (w8 k gs).countP (fun g => !isNot g) = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g0 gs ih =>
    simp only [w8, List.countP_append, c18, List.countP_cons, List.countP_nil, ih]
    cases g0.op <;> simp [isNot] <;> omega
lemma p33 (gs : List SGate) :
    ∀ (k : Nat) (L M : List Bool), L.length = 10 + k → M.length = 10 + 3 * k →
      (∀ w, M.getD (mIdx w) false = L.getD w false) →
      ∀ w, ((Circuit.mk (w8 k gs) 0).wires M).getD (mIdx w) false = (sRun gs L).getD w false := by
  induction gs with
  | nil => intro k L M _ _ h w; exact h w
  | cons g gs ih =>
    intro k L M hL hM h
    have hfold : (Circuit.mk (w8 k (g :: gs)) 0).wires M =
        (Circuit.mk (w8 (k + 1) gs) 0).wires ((Circuit.mk (c18 k g) 0).wires M) := by
      simp [w8, Circuit.wires, List.foldl_append]
    rw [hfold, f5]
    let v1 := !(M.getD (mIdx g.i1) false)
    let v2 := !(M.getD (mIdx g.i2) false)
    let M1 := M ++ [v1]
    let M2 := M1 ++ [v2]
    have hM1L : M1.length = 10 + 3 * k + 1 := by simp [M1, hM]
    have hM2L : M2.length = 10 + 3 * k + 2 := by simp [M2, hM1L]
    have hM1g : ∀ i, i < 10 + 3 * k → M1.getD i false = M.getD i false := fun i hi => t7 M [v1] false (by omega)
    have hM2g : ∀ i, i < 10 + 3 * k → M2.getD i false = M.getD i false := fun i hi => by
      rw [t7 M1 [v2] false (by omega)]; exact hM1g i hi
    have hM2n1 : M2.getD (10 + 3 * k) false = v1 := by
      rw [t7 M1 [v2] false (by omega), f8 M [v1] false (by omega)]; simp [hM]
    have hM2n2 : M2.getD (10 + 3 * k + 1) false = v2 := by
      rw [f8 M1 [v2] false (by omega)]; simp [hM1L]
    have hM2m : ∀ u, M2.getD (mIdx u) false = L.getD u false := by
      intro u; by_cases hlt : mIdx u < 10 + 3 * k
      · rw [hM2g _ hlt, h u]
      · have hge : 10 + 3 * k + 2 ≤ mIdx u := by unfold mIdx at hlt ⊢; split_ifs at hlt ⊢ <;> omega
        rw [gDef M2 false (by omega), ← h u, gDef M false (by omega)]
    have hM1m : M1.getD (mIdx g.i2) false = M.getD (mIdx g.i2) false := by
      by_cases hlt : mIdx g.i2 < 10 + 3 * k
      · exact hM1g _ hlt
      · have hge : 10 + 3 * k + 1 ≤ mIdx g.i2 := by unfold mIdx at hlt ⊢; split_ifs at hlt ⊢ <;> omega
        rw [gDef M1 false (by omega), gDef M false (by omega)]
    have ha : M2.getD (if g.n1 then 10 + 3 * k else mIdx g.i1) false = xor (L.getD g.i1 false) g.n1 := by
      cases hn1 : g.n1
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]; exact hM2m g.i1
      · simp only [↓reduceIte, Bool.xor_true, hM2n1, v1, h]
    have hb : M2.getD (if g.n2 then 10 + 3 * k + 1 else mIdx g.i2) false = xor (L.getD g.i2 false) g.n2 := by
      cases hn2 : g.n2
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]; exact hM2m g.i2
      · simp only [↓reduceIte, Bool.xor_true, hM2n2, v2, h]
    have hstep : (Circuit.mk (c18 k g) 0).wires M = M2 ++ [sEv g (fun i => L.getD i false)] := by
      have hnot : ∀ (w : List Bool) (i : Nat), GateOp.not.eval ([i].map fun j => w.getD j false) = !(w.getD i false) := fun _ _ => rfl
      simp only [Circuit.wires, c18, List.foldl_cons, List.foldl_nil, hnot]
      change (M1 ++ [!(M1.getD (mIdx g.i2) false)]) ++ [(if g.op then GateOp.or else GateOp.and).eval
        ([(if g.n1 then 10 + 3 * k else mIdx g.i1), (if g.n2 then 10 + 3 * k + 1 else mIdx g.i2)].map
          fun j => (M1 ++ [!(M1.getD (mIdx g.i2) false)]).getD j false)] = M2 ++ _
      rw [hM1m]; change M2 ++ [(if g.op then GateOp.or else GateOp.and).eval
        [M2.getD (if g.n1 then 10 + 3 * k else mIdx g.i1) false,
         M2.getD (if g.n2 then 10 + 3 * k + 1 else mIdx g.i2) false]] = M2 ++ _
      congr 1; simp only [ha, hb, sEv]; cases g.op <;> simp [GateOp.eval]
    rw [hstep]
    apply ih (k + 1) (h6 L g) (M2 ++ [sEv g (fun i => L.getD i false)]) (by simp [h6, hL]; omega) (by simp [hM2L]; omega)
    intro w; by_cases hw : w < 10 + k
    · have hmw : mIdx w < 10 + 3 * k := by unfold mIdx; split_ifs <;> omega
      rw [t7 M2 _ false (by omega), hM2g _ hmw, h w]; unfold h6; rw [t7 L _ false (by omega)]
    · by_cases hwe : w = 10 + k
      · subst hwe; have hmw : mIdx (10 + k) = 10 + 3 * k + 2 := by unfold mIdx; simp
        rw [hmw, f8 M2 _ false (by omega)]; simp only [hM2L, Nat.sub_self, List.getD_cons_zero]
        unfold h6; rw [f8 L _ false (by omega)]; simp only [hL, Nat.sub_self, List.getD_cons_zero]
      · have hmw : 10 + 3 * k + 3 ≤ mIdx w := by unfold mIdx; split_ifs <;> omega
        rw [gDef _ false (by simp [hM2L]; omega)]; unfold h6; rw [gDef _ false (by simp [hL]; omega)]
lemma w38 (gs : List SGate) (u : Nat) (b : Bool) (hlen : gs.length ≤ 16) (hC : w9 gs u b (fun _ => True)) : False := by
  obtain ⟨gs', u', b', h2, hle, hC', _⟩ := q41 gs u b hC
  have hlen' : gs'.length ≤ 14 := by by_cases h : 2 ≤ gs.length; have := h2 h; omega; omega
  let C : Circuit := ⟨w8 0 gs', mIdx u'⟩
  have hcnt : C.gates.countP (fun g => !isNot g) ≤ 14 := by
    change (w8 0 gs').countP (fun g => !isNot g) ≤ 14; rw [r33]; exact hlen'
  apply sliceCore C (mIdx u') b' true (q33 0 gs') (by simp) (by simpa using hcnt)
  intro x hx
  have hw := p33 gs' 0 (List.ofFn x) (List.ofFn x) (by simp) (by simp) (by
    intro w; by_cases hlt : w < 10
    · simp [mIdx, hlt]
    · have : 10 ≤ mIdx w := by unfold mIdx; split_ifs <;> omega
      rw [gDef _ false (by simp; omega), gDef _ false (by simp; omega)]) u'
  change (if b' = true then !((Circuit.mk (w8 0 gs') 0).wires (List.ofFn x)).getD (mIdx u') false
    else ((Circuit.mk (w8 0 gs') 0).wires (List.ofFn x)).getD (mIdx u') false) = fullEdge x
  rw [hw]; exact hC' x hx
inductive WRef | const (c : Bool) | wire (idx : Nat) (fl : Bool)
def evWR (w : List Bool) : WRef → Bool
  | WRef.const c => c
  | WRef.wire idx fl => xor (w.getD idx false) fl
def m28 : WRef → WRef
  | WRef.const c => WRef.const (!c)
  | WRef.wire idx fl => WRef.wire idx (!fl)
def z10 : WRef → Prop | WRef.const _ => True | WRef.wire _ fl => fl = false
def wrBd (k : Nat) : WRef → Prop | WRef.const _ => True | WRef.wire idx _ => idx < 10 + k
lemma y40 (k : Nat) (r : WRef) (h : wrBd k r) : wrBd k (m28 r) := by cases r <;> exact h
def n11 (op : Bool) (n : Nat) (r1 r2 : WRef) : WRef × List SGate :=
  match r1, r2 with
  | WRef.const c, r => if c == op then (WRef.const op, []) else (r, [])
  | r, WRef.const c => if c == op then (WRef.const op, []) else (r, [])
  | WRef.wire i1 n1, WRef.wire i2 n2 => (WRef.wire (10 + n) false, [⟨op, i1, n1, i2, n2⟩])
def n4 (env : List WRef) (sc : List SGate) (g : Gate) : List WRef × List SGate :=
  let getR (i : Nat) := env.getD i (WRef.const false)
  match g.op with
  | GateOp.not => (env ++ [match g.inputs with | [] => WRef.const true | a :: _ => m28 (getR a)], sc)
  | GateOp.and => match g.inputs with
    | [] => (env ++ [WRef.const true], sc)
    | [a] => (env ++ [getR a], sc)
    | a :: b :: _ => let (r, ad) := n11 false sc.length (getR a) (getR b); (env ++ [r], sc ++ ad)
  | GateOp.or => match g.inputs with
    | [] => (env ++ [WRef.const false], sc)
    | [a] => (env ++ [getR a], sc)
    | a :: b :: _ => let (r, ad) := n11 true sc.length (getR a) (getR b); (env ++ [r], sc ++ ad)
  | _ => (env ++ [WRef.const false], sc)
def cAux (env : List WRef) (sc : List SGate) : List Gate → List WRef × List SGate
  | [] => (env, sc)
  | g :: gs => let p := n4 env sc g; cAux p.1 p.2 gs
lemma p30 (op : Bool) (sc : List SGate) (r1 r2 : WRef) (h1 : wrBd sc.length r1) (h2 : wrBd sc.length r2) :
    let (r, ad) := n11 op sc.length r1 r2
    ad.length ≤ 1 ∧ wrBd (sc ++ ad).length r ∧ (z10 r1 → z10 r2 → z10 r ∧ sPos ad) ∧
    ∀ l : List Bool, l.length = 10 →
      evWR (sRun (sc ++ ad) l) r = (if op then evWR (sRun sc l) r1 || evWR (sRun sc l) r2 else evWR (sRun sc l) r1 && evWR (sRun sc l) r2) := by
  rcases r1 with c1 | ⟨i1, n1⟩ <;> rcases r2 with c2 | ⟨i2, n2⟩
  · cases op <;> cases c1 <;> cases c2 <;> simp [n11, evWR, z10, wrBd, sPos]
  · cases op <;> cases c1 <;> simp [n11, evWR, z10, wrBd, sPos] at h2 ⊢ <;> try exact h2
  · cases op <;> cases c2 <;> simp [n11, evWR, z10, wrBd, sPos] at h1 ⊢ <;> try exact h1
  · simp only [n11, List.length_singleton, le_refl, true_and, List.length_append, wrBd]
    refine ⟨by omega, fun hp1 hp2 => ⟨rfl, fun g hg => by simp at hg; rw [hg]; exact ⟨hp1, hp2⟩⟩, fun l hl => ?_⟩
    simp only [evWR, k12, f5, Bool.xor_false]
    have hnil : sRun [] (h6 (sRun sc l) ⟨op, i1, n1, i2, n2⟩) = h6 (sRun sc l) ⟨op, i1, n1, i2, n2⟩ := rfl
    rw [hnil]; unfold h6
    have hlen : (sRun sc l).length = 10 + sc.length := by rw [x13, hl]
    rw [f8 _ _ false (by omega)]; simp [hlen, sEv]
lemma r34 (env : List WRef) (sc : List SGate) (g : Gate)
    (hFT : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hbd : ∀ r ∈ env, wrBd sc.length r) :
    let p := n4 env sc g
    p.2.length ≤ sc.length + (if !isNot g then 1 else 0) ∧
    (∀ r ∈ p.1, wrBd p.2.length r) ∧ p.1.length = env.length + 1 ∧
    (isNot g = false → (∀ r ∈ env, z10 r) → sPos sc → sPos p.2 ∧ ∀ r ∈ p.1, z10 r) ∧
    (∀ (x : Fin 10 → Bool) (W : List Bool), W.length = env.length →
      (∀ i, evWR (sRun sc (List.ofFn x)) (env.getD i (WRef.const false)) = W.getD i false) →
      ∀ i, evWR (sRun p.2 (List.ofFn x)) (p.1.getD i (WRef.const false)) =
        (W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)]).getD i false) := by
  have hgb : ∀ i, wrBd sc.length (env.getD i (WRef.const false)) := fun i => by
    rw [List.getD_eq_getElem?_getD]; cases h : env[i]? with | none => trivial | some r => exact hbd r (List.mem_of_getElem? h)
  have hgp : (∀ r ∈ env, z10 r) → ∀ i, z10 (env.getD i (WRef.const false)) := fun hp i => by
    rw [List.getD_eq_getElem?_getD]; cases h : env[i]? with | none => trivial | some r => exact hp r (List.mem_of_getElem? h)
  have hApp : ∀ (r : WRef) (ad : List SGate) (x : Fin 10 → Bool) (W : List Bool), W.length = env.length →
      (∀ i, evWR (sRun sc (List.ofFn x)) (env.getD i (WRef.const false)) = W.getD i false) →
      evWR (sRun (sc ++ ad) (List.ofFn x)) r = g.op.eval (g.inputs.map fun j => W.getD j false) →
      ∀ i, evWR (sRun (sc ++ ad) (List.ofFn x)) ((env ++ [r]).getD i (WRef.const false)) =
        (W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)]).getD i false := by
    intro r ad x W hWL hW hr i
    by_cases hi : i < env.length
    · rw [t7 _ _ _ hi, t7 _ _ false (by omega)]
      have hpr : evWR (sRun (sc ++ ad) (List.ofFn x)) (env.getD i (WRef.const false)) =
          evWR (sRun sc (List.ofFn x)) (env.getD i (WRef.const false)) := by
        have hbi := hgb i; cases hri : env.getD i (WRef.const false) with
        | const _ => rfl
        | wire idx fl => rw [hri] at hbi; simp only [evWR, k12]; rw [t14 ad _ _ (by rw [x13]; simp; exact hbi)]
      rw [hpr, hW i]
    · by_cases hie : i = env.length
      · subst hie; rw [f8 _ _ _ le_rfl, f8 _ _ false (by omega)]; simp only [hWL, Nat.sub_self, List.getD_cons_zero, hr]
      · rw [gDef _ _ (by simp; omega), gDef _ false (by simp; omega)]; rfl
  have hBin : ∀ (op : Bool) (a b : Nat),
      let (r, ad) := n11 op sc.length (env.getD a (WRef.const false)) (env.getD b (WRef.const false))
      (sc ++ ad).length ≤ sc.length + 1 ∧ (∀ r' ∈ env ++ [r], wrBd (sc ++ ad).length r') ∧
      (env ++ [r]).length = env.length + 1 ∧
      ((∀ r' ∈ env, z10 r') → sPos sc → sPos (sc ++ ad) ∧ ∀ r' ∈ env ++ [r], z10 r') ∧
      ∀ (x : Fin 10 → Bool) (W : List Bool),
        (∀ i, evWR (sRun sc (List.ofFn x)) (env.getD i (WRef.const false)) = W.getD i false) →
        evWR (sRun (sc ++ ad) (List.ofFn x)) r = (if op then W.getD a false || W.getD b false else W.getD a false && W.getD b false) := by
    intro op a b
    have hcs := p30 op sc (env.getD a (WRef.const false)) (env.getD b (WRef.const false)) (hgb a) (hgb b)
    rcases hc : n11 op sc.length (env.getD a (WRef.const false)) (env.getD b (WRef.const false)) with ⟨r, ad⟩
    rw [hc] at hcs
    refine ⟨by simp; exact hcs.1, fun r' hr' => ?_, by simp, fun hp hs => ?_, fun x W hW => ?_⟩
    · simp only [List.mem_append, List.mem_singleton] at hr'
      rcases hr' with hr' | rfl
      · have := hbd r' hr'; cases r' with | const _ => trivial | wire idx _ => simp [wrBd] at this ⊢; omega
      · exact hcs.2.1
    · obtain ⟨hrp, hadp⟩ := hcs.2.2.1 (hgp hp a) (hgp hp b)
      exact ⟨fun g' hg' => (List.mem_append.mp hg').elim (hs g') (hadp g'),
             fun r' hr' => (List.mem_append.mp hr').elim (hp r') (fun h => by simp at h; rw [h]; exact hrp)⟩
    · rw [hcs.2.2.2 (List.ofFn x) (by simp), hW a, hW b]
  rcases g with ⟨op, ins⟩; rcases hFT with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨by simp [n4], fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hbd r hr; trivial,
        by simp [n4], fun _ hp hs => ⟨hs, fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hp r hr; trivial⟩,
        fun x W hWL hW i => by simpa [n4] using hApp (WRef.const true) [] x W hWL hW (by simp [evWR, GateOp.eval]) i⟩
    · refine ⟨by simp [n4], fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hbd r hr; exact hgb a,
        by simp [n4], fun _ hp hs => ⟨hs, fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hp r hr; exact hgp hp a⟩,
        fun x W hWL hW i => by simpa [n4] using hApp (env.getD a (WRef.const false)) [] x W hWL hW (by simp only [List.append_nil]; rw [hW a]; simp [GateOp.eval]) i⟩
    · have hb := hBin false a b
      rcases hc : n11 false sc.length (env.getD a (WRef.const false)) (env.getD b (WRef.const false)) with ⟨r, ad⟩
      rw [hc] at hb
      refine ⟨by simp only [n4, hc, isNot, Bool.not_false, ↓reduceIte]; exact hb.1, by simp only [n4, hc]; exact hb.2.1, by simp [n4, hc],
        fun _ hp hs => by simp only [n4, hc]; exact hb.2.2.2.1 hp hs,
        fun x W hWL hW i => by
          have hv : evWR (sRun (sc ++ ad) (List.ofFn x)) r = GateOp.and.eval ([a, b].map fun j => W.getD j false) := by
            simpa [GateOp.eval] using hb.2.2.2.2 x W hW
          simp only [n4, hc]; exact hApp r ad x W hWL hW hv i⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨by simp [n4], fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hbd r hr; trivial,
        by simp [n4], fun _ hp hs => ⟨hs, fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hp r hr; trivial⟩,
        fun x W hWL hW i => by simpa [n4] using hApp (WRef.const false) [] x W hWL hW (by simp [evWR, GateOp.eval]) i⟩
    · refine ⟨by simp [n4], fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hbd r hr; exact hgb a,
        by simp [n4], fun _ hp hs => ⟨hs, fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hp r hr; exact hgp hp a⟩,
        fun x W hWL hW i => by simpa [n4] using hApp (env.getD a (WRef.const false)) [] x W hWL hW (by simp only [List.append_nil]; rw [hW a]; simp [GateOp.eval]) i⟩
    · have hb := hBin true a b
      rcases hc : n11 true sc.length (env.getD a (WRef.const false)) (env.getD b (WRef.const false)) with ⟨r, ad⟩
      rw [hc] at hb
      refine ⟨by simp only [n4, hc, isNot, Bool.not_false, ↓reduceIte]; exact hb.1, by simp only [n4, hc]; exact hb.2.1, by simp [n4, hc],
        fun _ hp hs => by simp only [n4, hc]; exact hb.2.2.2.1 hp hs,
        fun x W hWL hW i => by
          have hv : evWR (sRun (sc ++ ad) (List.ofFn x)) r = GateOp.or.eval ([a, b].map fun j => W.getD j false) := by
            simpa [GateOp.eval] using hb.2.2.2.2 x W hW
          simp only [n4, hc]; exact hApp r ad x W hWL hW hv i⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, rest⟩
    · refine ⟨by simp [n4, isNot], fun r hr => by simp [n4] at hr; rcases hr with hr | rfl; exact hbd r hr; trivial,
        by simp [n4], fun hn => by simp [isNot] at hn,
        fun x W hWL hW i => by simpa [n4] using hApp (WRef.const true) [] x W hWL hW (by simp [evWR, GateOp.eval]) i⟩
    · refine ⟨by simp [n4, isNot], fun r hr => by
          simp [n4] at hr; rcases hr with hr | rfl; exact hbd r hr
          exact y40 _ _ (hgb a),
        by simp [n4], fun hn => by simp [isNot] at hn,
        fun x W hWL hW i => by
          have hneg : evWR (sRun sc (List.ofFn x)) (m28 (env.getD a (WRef.const false))) = !(W.getD a false) := by
            rw [← hW a]; cases env.getD a (WRef.const false) with
            | const _ => rfl
            | wire idx fl => simp only [m28, evWR]; cases (sRun sc (List.ofFn x)).getD idx false <;> cases fl <;> rfl
          simpa [n4] using hApp (m28 (env.getD a (WRef.const false))) [] x W hWL hW (by simpa [GateOp.eval] using hneg) i⟩
lemma y24 (gs : List Gate)
    (hFT : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (env : List WRef) (sc : List SGate), (∀ r ∈ env, wrBd sc.length r) →
      let (env', sc') := cAux env sc gs
      sc'.length ≤ sc.length + gs.countP (fun g => !isNot g) ∧
      ((∀ g ∈ gs, isNot g = false) → (∀ r ∈ env, z10 r) → sPos sc → sPos sc' ∧ ∀ r ∈ env', z10 r) ∧
      (∀ (x : Fin 10 → Bool) (W : List Bool), W.length = env.length →
        (∀ i, evWR (sRun sc (List.ofFn x)) (env.getD i (WRef.const false)) = W.getD i false) →
        ∀ i, evWR (sRun sc' (List.ofFn x)) (env'.getD i (WRef.const false)) = ((Circuit.mk gs 0).wires W).getD i false) := by
  induction gs with
  | nil => intro env sc _; exact ⟨by simp [cAux], fun _ hp hs => ⟨hs, hp⟩, fun _ _ _ hW i => hW i⟩
  | cons g gs ih =>
    intro env sc hbd
    have hs := r34 env sc g (hFT g List.mem_cons_self) hbd
    have hr := ih (fun g' hg' => hFT g' (List.mem_cons_of_mem _ hg')) (n4 env sc g).1 (n4 env sc g).2 hs.2.1
    simp only [cAux]; refine ⟨?_, ?_, ?_⟩
    · have h1 := hr.1; have h2 := hs.1; simp only [List.countP_cons]; cases hg : isNot g <;> simp only [hg, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at h2 ⊢ <;> omega
    · intro hno hp hs0; obtain ⟨hs1, hp1⟩ := hs.2.2.2.1 (hno g List.mem_cons_self) hp hs0
      exact hr.2.1 (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) hp1 hs1
    · intro x W hWL hW i
      exact hr.2.2 x _ (by simp [hs.2.2.1, hWL]) (hs.2.2.2.2 x W hWL hW) i
lemma x38 (gs : List Gate) (u : Nat) (b : Bool)
    (hFT : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hbin : gs.countP (fun g => !isNot g) ≤ 16)
    (hC : ∀ x : Fin 10 → Bool, (if b then !((Circuit.mk gs 0).wires (List.ofFn x)).getD u false
      else ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false) = fullEdge x) : False := by
  let env0 : List WRef := List.ofFn (fun i : Fin 10 => WRef.wire i.val false)
  have hsp := y24 gs hFT env0 [] (fun r hr => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr; exact i.isLt)
  rcases hc : cAux env0 [] gs with ⟨env', sc'⟩; rw [hc] at hsp
  have hlen' : sc'.length ≤ 16 := by have := hsp.1; simp at this; omega
  have hev : ∀ x, evWR (sRun sc' (List.ofFn x)) (env'.getD u (WRef.const false)) = ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false :=
    fun x => hsp.2.2 x (List.ofFn x) (by simp [env0]) (fun i => by
      by_cases hi : i < 10
      · have h1 : env0.getD i (WRef.const false) = WRef.wire i false := by
          simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi, Option.getD_some]
        rw [h1]; simp only [evWR, sRun, List.foldl_nil, Bool.xor_false]
      · have h1 : env0.getD i (WRef.const false) = WRef.const false := by
          simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hi, Option.getD_none]
        rw [h1, k7, dif_neg hi]; rfl) u
  cases hr : env'.getD u (WRef.const false) with
  | const c =>
    have h0 := hC (fun _ => false); have h1 := hC (fun _ => true)
    rw [← hev, hr, v14] at h0; rw [← hev, hr, n20] at h1
    cases b <;> cases c <;> simp [evWR] at h0 h1
  | wire idx fl =>
    apply w38 sc' idx (xor b fl) hlen'
    intro x _; have h := hC x; rw [← hev x, hr] at h; simp only [evWR] at h
    exact d19 b fl _ _ h
lemma m33 (gs : List Gate) (u : Nat)
    (hFT : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hno : ∀ g ∈ gs, isNot g = false) (hlen : gs.length ≤ 17)
    (hC : ∀ x : Fin 10 → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false = fullEdge x) : False := by
  let env0 : List WRef := List.ofFn (fun i : Fin 10 => WRef.wire i.val false)
  have hsp := y24 gs hFT env0 [] (fun r hr => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr; exact i.isLt)
  rcases hc : cAux env0 [] gs with ⟨env', sc'⟩; rw [hc] at hsp
  have hlen' : sc'.length ≤ 17 := by
    have := hsp.1; have := List.countP_le_length (p := fun g => !isNot g) (l := gs); simp at *; omega
  obtain ⟨hscpos, henvpos⟩ := hsp.2.1 hno (fun r hr => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr; rfl) (fun _ h => by simp at h)
  have hev : ∀ x, evWR (sRun sc' (List.ofFn x)) (env'.getD u (WRef.const false)) = ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false :=
    fun x => hsp.2.2 x (List.ofFn x) (by simp [env0]) (fun i => by
      by_cases hi : i < 10
      · have h1 : env0.getD i (WRef.const false) = WRef.wire i false := by
          simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi, Option.getD_some]
        rw [h1]; simp only [evWR, sRun, List.foldl_nil, Bool.xor_false]
      · have h1 : env0.getD i (WRef.const false) = WRef.const false := by
          simp only [env0, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg hi, Option.getD_none]
        rw [h1, k7, dif_neg hi]; rfl) u
  have hrupos : z10 (env'.getD u (WRef.const false)) := by
    rw [List.getD_eq_getElem?_getD]; cases h : env'[u]? with | none => trivial | some r => exact henvpos r (List.mem_of_getElem? h)
  cases hr : env'.getD u (WRef.const false) with
  | const c =>
    have h0 := hC (fun _ => false); have h1 := hC (fun _ => true)
    rw [← hev, hr, v14] at h0; rw [← hev, hr, n20] at h1; cases c <;> simp [evWR] at h0 h1
  | wire idx fl =>
    rw [hr] at hrupos; have hfl : fl = false := hrupos; subst hfl
    apply v38 sc' idx false hscpos hlen'
    intro x _; have h := hC x; rw [← hev x, hr] at h; simpa [evWR] using h
lemma w15 (g : Gate) (gs : List Gate) (l : List Bool) :
    (Circuit.mk (g :: gs) 0).wires l = (Circuit.mk gs 0).wires (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) := rfl
lemma w12 (gs : List Gate)
    (hFT : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hno : ∀ g ∈ gs, isNot g = false) :
    ∀ (l1 l2 : List Bool), l1.length = l2.length →
      (∀ i, l1.getD i false = true → l2.getD i false = true) →
      ∀ i, ((Circuit.mk gs 0).wires l1).getD i false = true → ((Circuit.mk gs 0).wires l2).getD i false = true := by
  induction gs with
  | nil => intro l1 l2 _ h i hi; exact h i hi
  | cons g gs ih =>
    intro l1 l2 hlen h
    have hgFT := (hFT g List.mem_cons_self).1; have hgno := hno g List.mem_cons_self
    rw [w15, w15]
    apply ih (fun g' hg' => hFT g' (List.mem_cons_of_mem _ hg')) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
    intro i hi
    by_cases hil : i < l1.length
    · rw [t7 _ _ false hil] at hi; rw [t7 _ _ false (by omega)]; exact h i hi
    · by_cases hie : i = l1.length
      · subst hie; rw [f8 _ _ false le_rfl] at hi; rw [f8 _ _ false (by omega)]
        simp only [Nat.sub_self, hlen, List.getD_cons_zero] at hi ⊢
        rcases g with ⟨op, ins⟩; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgFT
        rcases hgFT with rfl | rfl | rfl
        · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hi ⊢
          intro j hj; exact h j (hi j hj)
        · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
          obtain ⟨_, ⟨j, hj, rfl⟩, hb⟩ := hi; exact ⟨_, ⟨j, hj, rfl⟩, h j hb⟩
        · simp [isNot] at hgno
      · rw [gDef _ false (by simp; omega)] at hi; simp at hi
lemma t22 (gs : List Gate) (h1 : gs.countP isNot = 1) :
    ∃ (pre post : List Gate) (ng : Gate),
      gs = pre ++ ng :: post ∧ isNot ng = true ∧ (∀ g ∈ pre, isNot g = false) ∧ (∀ g ∈ post, isNot g = false) := by
  induction gs with
  | nil => simp at h1
  | cons g gs ih =>
    simp only [List.countP_cons] at h1
    cases hng : isNot g with
    | true =>
      simp only [hng, ↓reduceIte] at h1
      have hpost : ∀ g' ∈ gs, isNot g' = false := fun g' hg' => by
        cases h : isNot g' with
        | false => rfl
        | true => have : 0 < gs.countP isNot := List.countP_pos_iff.mpr ⟨g', hg', h⟩; omega
      exact ⟨[], gs, g, rfl, hng, fun _ h => by simp at h, hpost⟩
    | false =>
      simp only [hng, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1
      obtain ⟨pre, post, ng, rfl, hng', hpre, hpost⟩ := ih h1
      exact ⟨g :: pre, post, ng, rfl, hng', fun g' hg' => (List.mem_cons.mp hg').elim (fun h => h ▸ hng) (hpre g'), hpost⟩
lemma f23 (l : List Gate) : ∀ w : List Bool, ((Circuit.mk l 0).wires w).length = w.length + l.length := by
  induction l with
  | nil => intro w; simp [Circuit.wires]
  | cons a t ih => intro w; rw [w15, ih]; simp; omega
lemma main_proof :
    ∀ (x1 : Gate) (x2 : Circuit) (x3 : Nat) (x4 : Bool),
      PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := 0 : Circuit } →
      PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ 17 →
      (∀ (x8 : Fin 10) (x9 : Finset Nat), (∀ x10 ∈ x9, ∃ (x12 : Gate), (x1 :: x2.gates)[x10]? = Option.some x12 ∧ ↑x8 ∈ x12.inputs ∧ (x12.op = GateOp.not → x12.inputs.head? = Option.some ↑x8)) → x9.card ≤ if x4 = true then 3 else 2) →
      x4 = true →
      have x10 : (Fin 10 → Bool) → Bool := fullEdge;
      have x11 : (Fin 10 → Bool) → Nat → Bool := fun x11 x12 => (x2.wires ({ gates := [x1], output := 0 : Circuit }.wires (List.ofFn x11))).getD x12 false;
      ∃ (x12 : Fin 10 → Bool), (if x4 = true then !x11 x12 x3 else x11 x12 x3) ≠ x10 x12 := by
  intro g D u b hg hD hs _ hb; subst hb; dsimp only; by_contra hcon; push Not at hcon
  let gs := g :: D.gates
  have hFT : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => (List.mem_cons.mp hg').elim (fun h => h ▸ hg g (List.mem_singleton_self g)) (hD g')
  have hlen : gs.length ≤ 18 := by change D.gates.length ≤ 17 at hs; simp only [gs, List.length_cons]; omega
  have hW : ∀ x : Fin 10 → Bool, (!(((Circuit.mk gs 0).wires (List.ofFn x)).getD u false)) = fullEdge x := by
    intro x; have hx := hcon x; simp only [↓reduceIte] at hx; exact hx
  have hsum : gs.countP isNot + gs.countP (fun g' => !isNot g') = gs.length := by
    clear hFT hlen hW hcon
    induction gs with
    | nil => simp
    | cons a l ih => simp only [List.countP_cons, List.length_cons]; cases isNot a <;> simp <;> omega
  by_cases h2 : 2 ≤ gs.countP isNot
  · exact x38 gs u true hFT (by omega) (fun x => by simp only [↓reduceIte]; exact hW x)
  · by_cases h0 : gs.countP isNot = 0
    · have hno : ∀ g' ∈ gs, isNot g' = false := fun g' hg' => by
        cases h : isNot g' with
        | false => rfl
        | true => have : 0 < gs.countP isNot := List.countP_pos_iff.mpr ⟨g', hg', h⟩; omega
      have h0v : ((Circuit.mk gs 0).wires (List.ofFn (fun _ : Fin 10 => false))).getD u false = true := by
        have := hW (fun _ => false); rw [v14] at this
        cases hv : ((Circuit.mk gs 0).wires (List.ofFn (fun _ : Fin 10 => false))).getD u false <;> rw [hv] at this <;> simp at this ⊢
      have h1v : ((Circuit.mk gs 0).wires (List.ofFn (fun _ : Fin 10 => true))).getD u false = false := by
        have := hW (fun _ => true); rw [n20] at this
        cases hv : ((Circuit.mk gs 0).wires (List.ofFn (fun _ : Fin 10 => true))).getD u false <;> rw [hv] at this <;> simp at this ⊢
      have hm := w12 gs hFT hno (List.ofFn (fun _ : Fin 10 => false)) (List.ofFn (fun _ : Fin 10 => true))
        (by simp) (fun i hi => by rw [k7] at hi; split_ifs at hi <;> simp at hi) u h0v
      rw [h1v] at hm; simp at hm
    · have h1 : gs.countP isNot = 1 := by omega
      obtain ⟨pre, post, ng, hgs, hng, hpre_no, hpost_no⟩ := t22 gs h1
      have hpre_FT : ∀ g' ∈ pre, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hFT g' (by rw [hgs]; simp [hg'])
      have hpost_FT : ∀ g' ∈ post, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hFT g' (by rw [hgs]; simp [hg'])
      have hng_op : ng.op = GateOp.not := by cases hop : ng.op <;> simp [isNot, hop] at hng; rfl
      have hpre_len : pre.length ≤ 17 := by have : gs.length = pre.length + 1 + post.length := by { rw [hgs]; simp; omega }; omega
      let hfun (x : Fin 10 → Bool) : Bool := match ng.inputs with | [] => false | a :: _ => ((Circuit.mk pre 0).wires (List.ofFn x)).getD a false
      let Gfun (x : Fin 10 → Bool) (bit : Bool) : Bool := ((Circuit.mk post 0).wires ((Circuit.mk pre 0).wires (List.ofFn x) ++ [bit])).getD u false
      have hdecomp : ∀ x : Fin 10 → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD u false = Gfun x (!hfun x) := by
        intro x; simp only [Gfun, hfun, hgs, Circuit.wires, List.foldl_append, List.foldl_cons]
        cases hins : ng.inputs with
        | nil => simp [hng_op, GateOp.eval]
        | cons a rest => simp [hng_op, GateOp.eval]
      have hG_mono : ∀ (x y : Fin 10 → Bool) (b1 b2 : Bool), (∀ i, x i = true → y i = true) → (b1 = true → b2 = true) →
          Gfun x b1 = true → Gfun y b2 = true := by
        intro x y b1 b2 hxy hb12
        have hlx : ((Circuit.mk pre 0).wires (List.ofFn x)).length = 10 + pre.length := by rw [f23]; simp
        have hly : ((Circuit.mk pre 0).wires (List.ofFn y)).length = 10 + pre.length := by rw [f23]; simp
        apply w12 post hpost_FT hpost_no _ _ (by simp only [List.length_append, List.length_singleton, hlx, hly])
        intro i hi
        by_cases hil : i < 10 + pre.length
        · rw [t7 _ _ false (by omega)] at hi; rw [t7 _ _ false (by omega)]
          exact w12 pre hpre_FT hpre_no (List.ofFn x) (List.ofFn y) (by simp)
            (fun j hj => by rw [k7] at hj ⊢; split_ifs at hj ⊢ with hj10; exact hxy ⟨j, hj10⟩ hj) i hi
        · by_cases hie : i = 10 + pre.length
          · subst hie; rw [f8 _ _ false (by omega)] at hi; rw [f8 _ _ false (by omega)]
            simp only [hlx, hly, Nat.sub_self, List.getD_cons_zero] at hi ⊢; exact hb12 hi
          · rw [gDef _ false (by simp only [List.length_append, List.length_singleton, hlx]; omega)] at hi; simp at hi
      have hW0 : Gfun (fun _ => false) (!hfun (fun _ => false)) = true := by
        have := hW (fun _ => false); rw [hdecomp, v14] at this
        cases hv : Gfun (fun _ => false) (!hfun (fun _ => false)) <;> rw [hv] at this <;> simp at this ⊢
      have hW1 : Gfun (fun _ => true) (!hfun (fun _ => true)) = false := by
        have := hW (fun _ => true); rw [hdecomp, n20] at this
        cases hv : Gfun (fun _ => true) (!hfun (fun _ => true)) <;> rw [hv] at this <;> simp at this ⊢
      have hh_mono : ∀ (x y : Fin 10 → Bool), (∀ i, x i = true → y i = true) → hfun x = true → hfun y = true := by
        intro x y hxy; dsimp only [hfun]; cases ng.inputs with
        | nil => intro h; exact h
        | cons a _ =>
          exact w12 pre hpre_FT hpre_no (List.ofFn x) (List.ofFn y) (by simp)
            (fun j hj => by rw [k7] at hj ⊢; split_ifs at hj ⊢ with hj10; exact hxy ⟨j, hj10⟩ hj) a
      have hh0 : hfun (fun _ => false) = false := by
        cases h : hfun (fun _ => false) with
        | false => rfl
        | true =>
          have hh1 := hh_mono _ _ (fun _ _ => rfl) h
          rw [h] at hW0; rw [hh1] at hW1; simp only [Bool.not_true] at hW0 hW1
          have := hG_mono (fun _ => false) (fun _ => true) false false (fun _ _ => rfl) id hW0
          rw [hW1] at this; simp at this
      have hh1 : hfun (fun _ => true) = true := by
        cases h : hfun (fun _ => true) with
        | true => rfl
        | false =>
          rw [hh0] at hW0; rw [h] at hW1; simp only [Bool.not_false] at hW0 hW1
          have := hG_mono (fun _ => false) (fun _ => true) true true (fun _ _ => rfl) id hW0
          rw [hW1] at this; simp at this
      rw [hh0] at hW0; rw [hh1] at hW1; simp only [Bool.not_false, Bool.not_true] at hW0 hW1
      have hh_eq : ∀ x : Fin 10 → Bool, hfun x = fullEdge x := by
        intro x; cases hf : fullEdge x with
        | true =>
          have hWx : Gfun x (!hfun x) = false := by
            have := hW x; rw [hdecomp, hf] at this
            cases hv : Gfun x (!hfun x) <;> rw [hv] at this <;> simp at this ⊢
          cases hhx : hfun x with
          | true => rfl
          | false =>
            rw [hhx] at hWx; simp only [Bool.not_false] at hWx
            have := hG_mono (fun _ => false) x true true (fun _ h => by simp at h) id hW0
            rw [hWx] at this; simp at this
        | false =>
          have hWx : Gfun x (!hfun x) = true := by
            have := hW x; rw [hdecomp, hf] at this
            cases hv : Gfun x (!hfun x) <;> rw [hv] at this <;> simp at this ⊢
          cases hhx : hfun x with
          | false => rfl
          | true =>
            rw [hhx] at hWx; simp only [Bool.not_true] at hWx
            have := hG_mono x (fun _ => true) false false (fun _ _ => rfl) id hWx
            rw [hW1] at this; simp at this
      cases hins : ng.inputs with
      | nil => have := hh_eq (fun _ => true); simp [hfun, hins, n20] at this
      | cons a _ => exact m33 pre a hpre_FT hpre_no hpre_len (fun x => by have := hh_eq x; simpa [hfun, hins] using this)
end PEqualNP.Outside.L_meta_6746
theorem PEqualNP.Outside.L_meta_6746 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         (∀ (x8 : Fin (10 : ℕ)) (x9 : Finset ℕ), (∀ x10 ∈ x9, ∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), (x1 :: x2.gates)[x10]? = Option.some x12 ∧ ↑x8 ∈ x12.inputs ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.not → x12.inputs.head? = Option.some ↑x8)) → x9.card ≤ if x4 = Bool.true then (3 : ℕ) else (2 : ℕ)) →           x4 = Bool.true →             have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));             have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;             ∃ (x12 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x11 x12 x3 else x11 x12 x3) ≠ x10 x12) := by
  exact PEqualNP.Outside.L_meta_6746.main_proof
