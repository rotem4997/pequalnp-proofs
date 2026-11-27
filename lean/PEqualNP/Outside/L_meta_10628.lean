import PEqualNP.Defs

-- The signed circuit and cofactor framework follows L_meta_10802, L_meta_1674, L_meta_670,
-- and the checker in L_meta_1667 (Apache-2.0).
-- The verified restriction bounds and monotone witness below concern this graph.

namespace PEqualNP.Outside.L_meta_10628
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
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

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
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
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
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
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffaffffffeefefeaa00fffffffffffffffaffffffeefefeaa00fffffffffffffffaffffffeefefeaa00fffffffffffffffaffffffeefefeaa00
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
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
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
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

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv



def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,5]⟩,⟨.or,[7,2]⟩,⟨.or,[6,4]⟩,⟨.and,[8,9]⟩,⟨.or,[4,3]⟩,⟨.or,[7,6]⟩,⟨.and,[11,12]⟩,⟨.or,[5,4]⟩,⟨.or,[1,0]⟩,⟨.and,[14,15]⟩,⟨.or,[10,13]⟩,⟨.or,[17,16]⟩], 18⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([3,4,4,0,0,0,0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3,4,4,0,0,0,0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 10 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim


def badPair (m r s : Nat) (ws : List Sig) : Bool :=
  let p := Fin.ofNat 512 r
  let q := Fin.ofNat 512 s
  (bit p (graphGoal m) != bit q (graphGoal m)) &&
    ws.all (fun w => bit p w == bit q w)

theorem badPair_sound {m r s cap : Nat} {ws : List Sig}
    (ok : badPair m r s ws = true) :
    Impossible true (graphGoal m) cap ws.toFinset := by
  simp only [badPair, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, beq_iff_eq] at ok
  intro k _ run
  obtain ⟨w, hw, hd⟩ := live_row_difference run ok.1
  exact hd (ok.2 w (List.mem_toFinset.mp hw))

def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior

def paidSliceCut (m cap s l : Nat) (hist : List Choice) (ws : List Sig) : Bool :=
  let d := subcube (m - s) 0
  let raw := vars m
  let paid := paidSliceChoices d raw hist
  match makePool true d raw paid with
  | none => false
  | some pool => poolCut true d l cap paid.length pool ws

theorem paidSliceCut_sound {m cap s l : Nat} {hist : List Choice} {ws : List Sig} (slice : Slice true (vars m)
    (graphGoal m) (subcube (m - s) 0) l) (nd : ws.Nodup)
    (ok : paidSliceCut m cap s l hist ws = true) :
    Impossible true (graphGoal m) cap ws.toFinset := by
  dsimp only [paidSliceCut] at ok
  split at ok
  next h => contradiction
  next pool h => exact poolCut_sound slice _ h nd ok

def sliceCuts (m cap : Nat) (smaller : List (Nat × Nat))
    (hist : List Choice) (ws : List Sig) : Bool :=
  smaller.any fun e =>
    let s := e.1
    let l := e.2
    (s != m && (s &&& m) == s) &&
    ((decide (cap < l + ws.countP (isMaskedConstant (subcube (m - s) 0)))) &&
      (paidSliceCut m cap s l hist ws && zeroSliceOK m s))

theorem sliceCuts_sound {m cap : Nat} {smaller : List (Nat × Nat)}
    {hist : List Choice} {ws : List Sig}
    (prior : ∀ e ∈ smaller, Lower true (vars e.1) (graphGoal e.1) e.2)
    (nd : ws.Nodup) (ok : sliceCuts m cap smaller hist ws = true) :
    Impossible true (graphGoal m) cap ws.toFinset := by
  obtain ⟨e, hmem, hit⟩ := List.any_eq_true.mp ok
  simp only [Bool.and_eq_true] at hit
  exact paidSliceCut_sound (zeroSlice_sound hit.2.2.2 (prior e hmem)) nd hit.2.2.1

theorem enumKeptMem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by
  cases k <;> simp [kept]

theorem enumChildSwap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat)
    (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    enumKeptMem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_flip hd a b]
  tauto

theorem enumIndexed {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (check : ∀ i j : Fin ws.length, j.val < i.val → ∀ d, d < 4 → ∀ ka kb,
      bin d (ws.get i) (ws.get j) ∉ ws → proper (bin d (ws.get i) (ws.get j)) →
      (childTwo ws (ws.get i) (ws.get j) d ka kb).length ≤ cap →
      Impossible true T (cap - 1) (childTwo ws (ws.get i) (ws.get j) d ka kb).toFinset) :
    Impossible true T cap ws.toFinset := by
  apply enum_step hn out
  intro a ha b hb d hd ka kb hab fresh hp hlen
  obtain ⟨i, hi⟩ := List.get_of_mem ha
  obtain ⟨j, hj⟩ := List.get_of_mem hb
  subst a
  subst b
  have diff : i.val ≠ j.val := fun e => hab (congrArg ws.get (Fin.ext e))
  have four {v : Nat} (h : allowed true v) : v < 4 := by
    rcases h with h | ⟨_, h⟩ <;> omega
  by_cases order : j.val < i.val
  · exact check i j order d (four hd) ka kb fresh hp hlen
  · have lower : i.val < j.val := by omega
    have flip := bin_flip hd (ws.get i) (ws.get j)
    have swapLen : (childTwo ws (ws.get i) (ws.get j) d ka kb).length =
        (childTwo ws (ws.get j) (ws.get i) (flipOp d) kb ka).length := by
      cases ka <;> cases kb <;>
        simp only [childTwo, kept, Bool.false_eq_true, if_false, if_true, List.length_cons,
          List.erase_comm (ws.get i) (ws.get j)]
    rw [enumChildSwap _ hn _ _ d hd]
    exact check j i lower _ (four (flip_flip hd).1) kb ka (flip ▸ fresh) (flip ▸ hp) (swapLen ▸ hlen)

def chosenSlice (m cap s : Nat) (prior : List (Nat × Nat)) (hist : List Choice) (ws : List Sig) : Bool :=
  decide ws.Nodup && prior.any (fun e => e.1 == s && paidSliceCut m cap s e.2 hist ws)

def prepared (m : Nat) (prior : List (Nat × Nat)) : Prop :=
  ∀ e ∈ prior, Slice true (vars m) (graphGoal m) (subcube (m - e.1) 0) e.2

theorem chosenSlice_sound {m cap s prior hist ws} (valid : prepared m prior)
    (ok : chosenSlice m cap s prior hist ws = true) :
    Impossible true (graphGoal m) cap ws.toFinset := by
  simp only [chosenSlice, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨nd,any⟩ := ok
  obtain ⟨e,mem,hit⟩ := List.any_eq_true.mp any
  simp only [Bool.and_eq_true, beq_iff_eq] at hit
  obtain ⟨eq,cut⟩ := hit
  have es : e.1 = s := eq
  subst s
  exact paidSliceCut_sound (valid e mem) nd cut

def attempt (m cap code : Nat) (prior : List (Nat × Nat))
    (next : Nat → List Choice → List Sig → Bool) (hist : List Choice)
    (c : Choice) (ws : List Sig) : Bool :=
  if code < 16384 then badPair m (code / 128) (code % 128) ws
  else if code < 32768 then chosenSlice m cap (code - 16384) prior (hist ++ [c]) ws
  else next (code - 32768) (hist ++ [c]) ws

theorem attempt_sound {m cap code prior next hist c ws}
    (valid : prepared m prior)
    (ih : ∀ n h w, next n h w = true → Impossible true (graphGoal m) cap w.toFinset)
    (ok : attempt m cap code prior next hist c ws = true) :
    Impossible true (graphGoal m) cap ws.toFinset := by
  unfold attempt at ok
  split at ok
  · exact badPair_sound ok
  · split at ok
    · exact chosenSlice_sound valid ok
    · exact ih _ _ _ ok

def eachMove (ws : List Sig) (cap : Nat) (visit : Nat → Choice → List Sig → Bool) : Bool :=
  (List.range ws.length).all fun i =>
    (List.range i).all fun j =>
      let a := ws.getD i zero
      let b := ws.getD j zero
      (List.range 4).all fun d =>
        [false,true].all fun ka =>
          [false,true].all fun kb =>
            let z := bin d a b
            let next := childTwo ws a b d ka kb
            if ws.contains z || !properB z || decide (cap < next.length) then true
            else visit (((i*(i-1)/2+j)*4+d)*4+ka.toNat*2+kb.toNat) (d,a,b) next

theorem eachMove_sound {ws cap visit T}
    (nd : ws.Nodup) (out : T ∉ ws)
    (good : ∀ i c w, visit i c w = true → Impossible true T (cap-1) w.toFinset)
    (ok : eachMove ws cap visit = true) : Impossible true T cap ws.toFinset := by
  apply enumIndexed nd out
  intro i j ji d hd ka kb fresh prop len
  have p := List.all_eq_true.mp ok i.val (List.mem_range.mpr i.isLt)
  have q := List.all_eq_true.mp p j.val (List.mem_range.mpr ji)
  have t := List.all_eq_true.mp q d (List.mem_range.mpr hd)
  have u := List.all_eq_true.mp t ka (by cases ka <;> simp)
  have v := List.all_eq_true.mp u kb (by cases kb <;> simp)
  have ia : ws.getD i.val zero = ws.get i := by simp [List.getD]
  have ib : ws.getD j.val zero = ws.get j := by simp [List.getD]
  have hp : properB (bin d (ws.get i) (ws.get j)) = true := by
    simpa only [properB, proper, Bool.and_eq_true, bne_iff_ne] using prop
  have memfalse : ws.contains (bin d (ws.get i) (ws.get j)) = false := by
    simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using fresh
  simp only [ia,ib,memfalse,hp,Bool.not_true,Bool.false_or,
    decide_eq_false (Nat.not_lt.mpr len),Bool.false_eq_true,ite_false] at v
  exact good _ _ _ v

def checkPlan (m : Nat) (prior : List (Nat × Nat)) (program : Nat → Nat → Nat) :
    Nat → Nat → List Choice → List Sig → Bool
  | 0, _, _, ws => !(ws.contains (graphGoal m))
  | k+1, node, hist, ws =>
    decide ws.Nodup && (!(ws.contains (graphGoal m)) &&
      eachMove ws (k+1) (fun slot c newWires =>
        attempt m k (program node slot) prior (checkPlan m prior program k) hist c newWires))

theorem checkPlan_sound {m prior program} (valid : prepared m prior) :
    ∀ cap node hist ws, checkPlan m prior program cap node hist ws = true →
      Impossible true (graphGoal m) cap ws.toFinset := by
  intro cap
  induction cap with
  | zero =>
    intro node hist ws h k hk run
    have out : graphGoal m ∉ ws := by simpa [checkPlan] using h
    obtain rfl : k = 0 := by omega
    have he := run.1
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | succ k ih =>
    intro node hist ws ok
    simp only [checkPlan, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨nd,no,steps⟩ := ok
    apply eachMove_sound nd (by simpa using no) _ steps
    intro i c w h
    exact attempt_sound valid ih h

def orbitOnto (p q : List Move) : Bool :=
  (List.finRange 512).all fun r => movedRow p (movedRow q r) == r

theorem orbit_onto {p q : List Move} (ok : orbitOnto p q = true) :
    Function.Surjective (movedRow p) := by
  intro r
  refine ⟨movedRow q r, beq_iff_eq.mp ((List.all_eq_true.mp ok) r ?_)⟩
  simp

theorem orbit_transfer {T : Sig} {k : Nat} {p q : List Move} {ws rs : List Sig}
    (onto : orbitOnto p q = true) (tg : movedWord p T = T)
    (state : (ws.map (movedWord p)).toFinset = rs.toFinset)
    (hi : Impossible true T k rs.toFinset) : Impossible true T k ws.toFinset := by
  intro n hn live
  have h := live_rename live (movedRow p) (orbit_onto onto)
  have t : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans tg
  have eq : ws.toFinset.image (rename (movedRow p)) = rs.toFinset := by
    rw [←state]
    ext x
    simp only [List.mem_toFinset, Finset.mem_image, List.mem_map, moved_eq_rename]
  rw [t, eq] at h
  exact hi n hn h

def orbitState (m i j d : Nat) (ka kb : Bool) : List Sig :=
  let ws := vars m
  childTwo ws (ws.getD i zero) (ws.getD j zero) d ka kb

def orbitChoice (m i j d : Nat) : Choice :=
  (d, (vars m).getD i zero, (vars m).getD j zero)

def visitOrbit (m cap code : Nat) (prior : List (Nat × Nat)) (cache : List (List Sig))
    (c : Choice) (ws : List Sig) : Bool :=
  if code < 32768 then attempt m cap code prior (fun _ _ _ => false) [] c ws
  else cache.any fun rep => decide (ws.toFinset = rep.toFinset)

theorem visitOrbit_sound {m cap code prior cache c ws}
    (valid : prepared m prior)
    (saved : ∀ w ∈ cache, Impossible true (graphGoal m) cap w.toFinset)
    (hit : visitOrbit m cap code prior cache c ws = true) :
    Impossible true (graphGoal m) cap ws.toFinset := by
  unfold visitOrbit at hit
  split at hit
  · exact attempt_sound valid (by intros; contradiction) hit
  · obtain ⟨w, hm, he⟩ := List.any_eq_true.mp hit
    rw [of_decide_eq_true he]
    exact saved w hm

def orbitRoot (m cap : Nat) (prior : List (Nat × Nat)) (program : Nat → Nat → Nat)
    (cache : List (List Sig)) : Bool :=
  let ws := vars m
  decide ws.Nodup && (!(ws.contains (graphGoal m)) &&
    eachMove ws (cap + 1) (fun i c w => visitOrbit m cap (program 0 i) prior cache c w))

theorem orbitRoot_sound {m cap prior program cache} (valid : prepared m prior)
    (saved : ∀ w ∈ cache, Impossible true (graphGoal m) cap w.toFinset)
    (ok : orbitRoot m cap prior program cache = true) :
    Impossible true (graphGoal m) (cap+1) (vars m).toFinset := by
  simp only [orbitRoot, Bool.and_eq_true, decide_eq_true_eq] at ok
  apply eachMove_sound ok.1 (by simpa using ok.2.1) _ ok.2.2
  intro i c w h
  exact visitOrbit_sound valid saved h

def certCode41 (node slot : Nat) : Nat :=
  (0x14201408108110a004880481 >>> (16 * ((0x15b0201640180a205909b0610690800400aa >>> (3 * slot)) &&& 7))) &&& 65535



def prior41 : List (Nat × Nat) := []

theorem prepared41 : prepared 41 prior41 := by

  intro e h

  simp [prior41] at h

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded41 : Impossible true (graphGoal 41) 3 (vars 41).toFinset :=
  checkPlan_sound (program := certCode41) prepared41 3 0 [] (vars 41) (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound41 : Lower true (vars 41) (graphGoal 41) 4 :=
  plain_low (hints:=3) (by decide +kernel) excluded41

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound50 : Lower true (vars 50) (graphGoal 50) 4 :=
  carry_of (old := 50) (rep := 41) (swaps := [16, 67]) (by decide +kernel) bound41

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound49 : Lower true (vars 49) (graphGoal 49) 4 :=
  carry_of (old := 49) (rep := 41) (swaps := [67]) (by decide +kernel) bound41

def certCode59 (node slot : Nat) : Nat :=
  (0x18200d181810140810a00d0a0583058a1120142011024032090208904031108109100881048804814029 >>> (16 * ((0x50a500e430525200ca332ca53062132e31304a1030a5011440314a010a44c150488a24c0a54894200063005e1001ef004610106303108011080306301d070086201c630090204c21011c404dce010213096231c213082131d6703484008020352d00882 >>> (5 * slot)) &&& 31))) &&& 65535



def prior59 : List (Nat × Nat) := [(41, 4), (50, 4), (49, 4)]

theorem prepared59 : prepared 59 prior59 := by

  intro e h

  simp only [prior59,List.mem_cons,List.not_mem_nil,or_false] at h

  rcases h with rfl | rfl | rfl

  · exact zeroSlice_sound (by decide +kernel) bound41

  · exact zeroSlice_sound (by decide +kernel) bound50

  · exact zeroSlice_sound (by decide +kernel) bound49

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded59 : Impossible true (graphGoal 59) 6 (vars 59).toFinset :=
  checkPlan_sound (program := certCode59) prepared59 6 0 [] (vars 59) (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound59 : Lower true (vars 59) (graphGoal 59) 7 :=
  plain_low (hints:=67) (by decide +kernel) excluded59

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 7 :=
  carry_of (old := 118) (rep := 59) (swaps := [50, 84, 96, 48]) (by decide +kernel) bound59

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound122 : Lower true (vars 122) (graphGoal 122) 7 :=
  carry_of (old := 122) (rep := 59) (swaps := [96]) (by decide +kernel) bound59

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound97 : Lower true (vars 97) (graphGoal 97) 4 :=
  carry_of (old := 97) (rep := 41) (swaps := [99]) (by decide +kernel) bound41

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound104 : Lower true (vars 104) (graphGoal 104) 4 :=
  carry_of (old := 104) (rep := 41) (swaps := [96]) (by decide +kernel) bound41

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  carry_of (old := 73) (rep := 41) (swaps := [101]) (by decide +kernel) bound41

def certCode105 (node slot : Nat) : Nat :=
  let data : Nat × Nat × Nat := match node with
    | 1 => (5, 0x8010800e800d800a800880068005800210a01420402940494068240814083040302040610481048820811081, 0x1821000a0018a500020025080082205421009020102100d030510800c2304ca502c210482102ca5024e70080204400008e20100000ce3040e700c0303cc60280003800028c600c830244200000010840108d0000000000000000112c000000000000000)
    | 2 => (4, 0x30208004800320c0140824403040240810a01081208104880481, 0x5000100020001000200000005000000020003000c0003000b00020002000a000000010000000400010004000300010009000000000000000000030008000000070000000000000006000000000000)
    | 3 => (4, 0x20c014082408302010a02081108104880481, 0x10000000400010004000200010001000800030001000000020007000000000003000600000002000300050002)
    | 4 => (4, 0x20c014082408302010a02081108104880481, 0x10000000400010004000200010003000100010008000000020007000000060000000000030005000200020003)
    | 5 => (3, 0x108124083020142010a0208104880481, 0x6001002001002000006000002005005002005002002005000001000003001003003001003001001003000004004000004000000004000000007000)
    | 6 => (4, 0x10a080074068108130202408404920811420048814080481, 0x6000200040002000700030004000300040001000700010004000000060000000b00000000000000020001000a00020000000200000009000100030001000500000003000000050008000000000000)
    | 7 => (3, 0x3020406124084049208110a004880481, 0x7002003002003000005000005001003001000002000004001002001004001000000006)
    | 8 => (4, 0x1420800940611408302024084049208110a0108104880481, 0x4000000060000000700030004000300040002000700020006000100040001000b00000000000000000002000a00000001000000000009000200030002000500010003000100050008000000000000)
    | 9 => (3, 0x3020406124084049208110a004880481, 0x7002003002005001003001003000005000001002001004000002000004000001000006)
    | 10 => (4, 0x3040800c800b10a0240814203020140820c02081048810810481, 0x5000200010002000100000005000000010003000c0001000b00010001000a000000020000000400020004000300020009000000000000000000030008000000070000000000000006000000000000)
    | 11 => (4, 0x10a024081408304020c02081108104880481, 0x10000000400010004000300010001000800020001000000030007000000000002000600000003000200050002)
    | 12 => (4, 0x20c024081408302010a02081108104880481, 0x10000000400010008000300010002000100010004000000030007000000060000000000020005000200030002)
    | 13 => (4, 0x302010a01420208114083040244020c0108104880481, 0x6000100020001000200000006000000020005000a00020005000200020005000000010000000300010003000300010009000100010003000000040004000000080000000000040000000000070000)
    | 14 => (4, 0x10a0800f40681420208130401408244040292408048810810481, 0x6000200010002000700010001000500010003000700010001000000060000000c00000000000000020003000b0002000000020000000a000300050003000400000009000000040008000000000000)
    | 15 => (4, 0x304020c0142010a0406114084029108104880481, 0x900020002000800020000000400000004000100020001000000070000000300010006000100030001000000000005)
    | 16 => (4, 0x14208011406110a024083040140820c040292081048810810481, 0x1000000060000000700010001000500010003000700010006000200010002000c00000000000000000003000b0000000200000000000a000300050003000400020009000200040008000000000000)
    | 17 => (4, 0x304020c010a01420406114084029108104880481, 0x900020002000800040001000200010002000000040000000100070001000300000006000000030000000100000005)
    | 18 => (5, 0x8021801f801e801b801980178016801304881408402940613020406814202440108110a04049240820810481, 0x18210004001842000200204201024054210104400c2101525051290142504c4202c210482102c42020e70100004400010e400c00014e5040e70140003cc60280003800028c601465020840000000c6300c6d00000000000000000d0c000000000000000)
    | 19 => (4, 0x30208015801420c0140830402440240810a01081208104880481, 0x500010002000100020003000c00030002000000050000000b00020002000a000100040003000100000001000000040009000000000000000300000008000000070000000000000006000000000000)
    | 20 => (4, 0x20c014083020240810a02081108104880481, 0x100040002000100000001000000040001000800030001000200000007000000020003000600020000000300050000)
    | 21 => (4, 0x20c014083020240810a02081108104880481, 0x100040002000100000001000000040003000100010008000200000007000000060002000200030005000000000003)
    | 22 => (3, 0x302004811408240810a0208110810488, 0x4000002000002001007001002004004002004002002004000003001000003000000003000003003000001005005001005001001005000000006000)
    | 23 => (4, 0x488801840680481406120812408142010a014081081, 0x4000200050002000400010005000100050003000400030005000000040000000a00000000000000020003000900020000000200000008000300010001000600000001000000060007000000000000)
    | 24 => (3, 0x3020406124084049208110a004880481, 0x5001003001003000005000007002003002000001000006002001001004002000000004)
    | 25 => (4, 0x1408801a40611420240830204049208110a0108104880481, 0x4000200060002000700010004000100040000000700000006000300040003000b00000000000000020000000a00000003000200020005000000010000000900030001000100050008000000000000)
    | 26 => (3, 0x3020406124084049208110a004880481, 0x5001003001007002003002003000005000002001001004000001000006000002000004)
    | 27 => (4, 0x2440801d801c0488302014082408142020c0208110a010810481, 0x5000000000002000000010005000000000003000c0000000b00000000000a000100020001000400020004000300020009000000000000000100030008000100070000000000000006000000000000)
    | 28 => (4, 0x48830201420244020c0208110a010810481, 0x100020001000400020004000300020000000800000002000100030007000100010000000600000003000000050000)
    | 29 => (4, 0x20c030201408240810a02081108104880481, 0x100040002000100010008000300010000000400000001000200030007000200060000000200000005000000030000)
    | 30 => (4, 0x140820811420048824083040244020c010a010810481, 0x80000000000020000000100080000000000040006000000040000000000040001000200010003000200030003000200070007000200030001000600050001000a0001000100050000000000090000)
    | 31 => (4, 0x48880204068304014082081142040293020244010a010810481, 0x6000000000002000300000000000300000003000300000000000100060000000c00000000000000020004000b0002000100020001000a000400090004000500010008000100050007000000000000)
    | 32 => (4, 0x244020c01408404914200488402910a010810481, 0x900000000000800000001000500000005000000000002000100070001000300040004000200030002000100010006)
    | 33 => (4, 0x14088022404924082440142020c00488402910a0208110810481, 0x100070000000800000000000600000002000800000007000000000003000c00000000000000010002000b0001000300010001000a000200060002000400050005000300040009000000000000)
    | 34 => (4, 0x244020c01408404914200488402910a010810481, 0x900000000000800050000000000020000000100050000000400040002000300010007000100030001000200010006)
    | 35 => (5, 0x80328030802f802c802a80288027802404811081402940683020406120c010a0140814202408404920810488, 0x1c670002001c2100060020210106405463010240082101525051290142504c2102c630486302c21020c60100004400010c600800014c6040c60140003ce70280003800028e7014450208400000008420084d0000000000000000090c000000000000000)
    | 36 => (4, 0x30208026802514082440304020c0240810a01081208104880481, 0x200000005000000020003000c00030005000100020001000b00020002000a000000030009000000010000000000040008000000000000000400010003000100070000000000000006000000000000)
    | 37 => (4, 0x14082408302020c010a02081108104880481, 0x20008000000010000000000040000000300070000000400010002000100020003000600020001000500030001)
    | 38 => (4, 0x14082408302020c010a02081108104880481, 0x20008000000010000000000040007000000000003000400010002000100060002000200030003000100010005)
    | 39 => (4, 0x302020c00488240814201408208110810481, 0x2000000050000000200010008000100070002000200050002000500050002000000010003000000040000000000040000000400040000000300010001000300010003000300010000000000060000)
    | 40 => (4, 0x481802940680488406124082081142010a014081081, 0x4000300050003000400000005000000050002000400020005000100040001000a00000000000000030002000900020001000300010006000200000000000800010000000000060007000000000000)
    | 41 => (3, 0x3020406124084049208110a004880481, 0x3000005000005001003001007002003002001000000006002000000004002001001004)
    | 42 => (4, 0x1081802b406810a024083020404920811420140804880481, 0x4000200060002000400000007000000070001000400010006000300040003000b00000000000000020001000a00010003000200020005000100000000000900030000000000050008000000000000)
    | 43 => (3, 0x3020406124084049208110a004880481, 0x3000005000007002003002005001003001002000000004001000000006001002001004)
    | 44 => (4, 0x802e802d048130201081208120c024402408142010a014080488, 0x200000000000200000002000200000000000600060000000c00000000000b00010003000100050003000500040003000a000000000000000100040009000100080000000000000007000000000000)
    | 45 => (4, 0x30201081208120c024400481240810a0142014080488, 0x10002000100060002000600040002000500050000000300010004000a000100090000000300000008000000070000)
    | 46 => (4, 0x14082408302020c010a02081108104880481, 0x20008000000000003000700000000000400010000000200030006000200020001000400010003000100050001)
    | 47 => (4, 0x240804811081304020c02440208110a0142014080488, 0x30000000000030000000300030000000000060004000000060000000000060001000200010005000200040005000200090009000200050001000400070001000800080001000700000000000a0000)
    | 48 => (4, 0x48180314061304020811081402914203020140820c010a00488, 0x1000000000001000200000000000200000002000200000000000100010000000c00000000000000050004000b0005000300050003000a000400090004000600070007000300060008000000000000)
    | 49 => (4, 0x404920c01081048140291420140810a00488, 0x700000000000700000001000100000001000000000001000600060002000400050005000300040003000200020008)
    | 50 => (4, 0x10818033404924402081048114204029240820c010a014080488, 0x200020000000300000000000300000003000300000002000000000002000c00000000000000010004000b0001000600010001000a000400090004000500070007000600050008000000000000)
    | 51 => (4, 0x404920c00481108140291420140810a00488, 0x700000000000700010000000000010000000100010000000600060003000400050005000200040002000300020008)
    | 52 => (5, 0x804380418040803d803b803980388035048824084049406130402440406820c0208140291420140810810481, 0xc210004000c420002001c420182105421018420102101525051290142104c4202c210482102c4201c630180004400018630100001505041080140003c630280003800028630148501cc600000010840108d000000000000000010ec000000000000000)
    | 53 => (4, 0x30408037803610a0240830201420140820c02081048810810481, 0x500020001000200010003000c00010001000000050000000b00010001000a000200040003000200000002000000040009000000000000000300000008000000070000000000000006000000000000)
    | 54 => (4, 0x10a024083040140820c02081108104880481, 0x100040003000100000001000000040001000800020001000300000007000000030002000600020000000200050000)
    | 55 => (4, 0x20c024083020140810a02081108104880481, 0x100080003000100000001000000040002000100010004000300000007000000060002000300020005000000000002)
    | 56 => (4, 0x304010a0048120c0142024081408208110810488, 0x3000000010000000100020009000100010003000300010003000100010003000000060002000000060000000000050000000800060000000200050004000500040002000200040000000000070000)
    | 57 => (4, 0x488803a406804812440406120c02408208114081081, 0x1000000000001000100000000000100000001000100000000000100010000000a00000000000000040006000900040002000400020008000600030003000500020003000200050007000000000000)
    | 58 => (4, 0x304020c0406110a0142014084029108104880481, 0x400010002000100020000000400000009000200020008000000010000000700060001000100030005000000000003)
    | 59 => (4, 0x2408803c406110a014201408304020c040292081048810810481, 0x1000300060001000700020001000200010000000700000006000100010005000c00000000000000030000000b00000005000300030004000000020000000a00090002000200040008000000000000)
    | 60 => (4, 0x304020c010a04061142014084029108104880481, 0x400010002000100090002000200080002000000040000000700010001000300000001000000060000000500000003)
    | 61 => (4, 0x2440803f803e0488302024081408142020c0208110a010810481, 0x500000000000200000003000c00000000000100050000000b00000000000a000200040003000200010002000100040009000000000000000300010008000100070000000000000006000000000000)
    | 62 => (4, 0x48830202440142020c0208110a010810481, 0x200040003000200010002000100040000000800000002000300010007000100030000000600000001000000050000)
    | 63 => (4, 0x20c030202408140810a02081108104880481, 0x100080003000100010004000200010000000400000001000300020007000200060000000300000005000000020000)
    | 64 => (4, 0x2440240810810488302020c014201408208110a00481, 0x400000000000100000002000a000000000004000300000004000000000004000100050002000100050001000100030007000700050001000200030006000300090002000200060000000000080000)
    | 65 => (4, 0x488804240682408108130403020404920c0208114200481, 0x1000000000001000100000000000100000001000100000000000100010000000b00000000000000030006000a00030002000300020009000600050005000400020008000200040007000000000000)
    | 66 => (4, 0x244020c04049140814200488402910a010810481, 0x500000000000200000001000500000009000000000008000100020001000700040004000200030006000100010003)
    | 67 => (4, 0x24088044404914081420244020c00488402910a0208110810481, 0x200070000000800000000000300000001000800000007000000000006000c00000000000000020001000b00010006000200020004000100030001000a00050005000300040009000000000000)
    | 68 => (4, 0x244020c04049140814200488402910a010810481, 0x500000000000200090000000000080000000100050000000400040002000300010002000100070001000600010003)
    | 69 => (5, 0x805480528051804e804c804a804980460481208140494068304020c04061244024084029140810a010810488, 0x86200020008210006001c210186305463018210102101525051290142104c2102c630486302c2101c420180004400018420100001508041080140003c420280003800028420148501cc600000010840108d000000000000000010ec000000000000000)
    | 70 => (4, 0x30408048804724081420302010a0140820c02081048810810481, 0x100000005000000010003000c00010005000200010002000b00010001000a000000030009000000020000000000040008000000000000000400020003000200070000000000000006000000000000)
    | 71 => (4, 0x24081408304010a020c02081108104880481, 0x30008000000010000000000040000000200070000000400010003000100030002000600020001000500020001)
    | 72 => (4, 0x2408140820c0302010a02081108104880481, 0x30008000000010000000000040007000000000002000600010003000100050002000300020002000100010004)
    | 73 => (4, 0x3040142004882440140810a02408208110810481, 0x1000000050000000100020009000100040001000100050001000500050001000000020003000000060000000000040000000800060000000300040002000400020003000300020000000000070000)
    | 74 => (4, 0x481804b406804882440406120c02408208110811408, 0x1000000000001000100000000000100000001000100000000000100010000000a00000000000000060004000900040003000600030005000400020002000800030002000200050007000000000000)
    | 75 => (4, 0x304020c04061142010a014084029108104880481, 0x200000004000000040001000200010009000200020008000100000000000700060000000000030005000100010003)
    | 76 => (4, 0x2081804d4068142010a014083040244040292408048810810481, 0x1000300060001000100000007000000070002000100020006000100010005000c00000000000000030002000b00020005000300030004000200000000000a00090000000000040008000000000000)
    | 77 => (4, 0x304020c01420406110a014084029108104880481, 0x200000004000000090002000200080004000100020001000700000000000300010000000000060001000500010003)
    | 78 => (4, 0x8050804f048130202081108120c024402408142010a014080488, 0x200000000000200000006000600000000000200020000000c00000000000b00030005000400030001000300010005000a000000000000000400010009000100080000000000000007000000000000)
    | 79 => (4, 0x3020208120c0108124400481240810a0142014080488, 0x20006000400020001000200010006000500050000000300040001000a000100090000000800000007000000030000)
    | 80 => (4, 0x24081408302020c010a02081108104880481, 0x30008000000000002000700000000000400010000000300020006000200030001000500010002000100040001)
    | 81 => (4, 0x140820c004812081302024402408142010a010810488, 0x20000000000020000000900090000000000020001000000020000000000020003000500040003000500010003000100080008000500030004000100060001000700070004000600000000000a0000)
    | 82 => (4, 0x48180534061108130403020208140492440240810a00488, 0x1000000000001000100000000000100000001000100000000000100010000000b00000000000000030007000a00030002000300020009000700060006000400050005000200040008000000000000)
    | 83 => (4, 0x404920c00481142010814029140810a00488, 0x100000000000100000001000100000007000000000007000200050002000800060006000500030004000400020003)
    | 84 => (4, 0x20818055244040491081048114204029240810a020c014080488, 0x200020000000300000000000300000003000300000002000000000002000c00000000000000040001000b0001000a000400040005000100060001000900070007000600050008000000000000)
    | 85 => (4, 0x404920c00481142010814029140810a00488, 0x100000000000100070000000000070000000100010000000600060005000300020005000200080004000400020003)
    | 86 => (5, 0x806580638062805f805d805b805a80571081208140614068244020c04049302030404029142010a004880481, 0x46100800004000086201c000146305463014000100001929051290180004c0002c630486302c0001c210144204442014210102101908041080182103c210284203842028210188601ca500000010840108d000000000000000010ec000000000000000)
    | 87 => (4, 0x2440805980583020140824080488142020c0208110a010810481, 0x10005000000000003000c00000005000000000002000b00000000000a000100030009000100020001000100040008000000000000000400020003000200070000000000000006000000000000)
    | 88 => (4, 0x302014202440048820c0208110a010810481, 0x100030008000100020001000100040001000000070000000400020003000200030000000600000000000500000002)
    | 89 => (4, 0x3020140820c0240810a02081108104880481, 0x200030008000200040001000200010007000000020000000600010003000100050000000300000000000400000001)
    | 90 => (4, 0x24401408240810a03040302014200488208110810481, 0x10004000000000002000a000000030000000000040000000400040000000100020005000100060003000100030001000900060001000500030002000300020008000500020000000000070000)
    | 91 => (4, 0x1081805c40682408048830403020404920c0208104811420, 0x1000000000001000100000000000100000001000100000000000100010000000b00000000000000060003000a00030005000600050004000300020002000900080002000200040007000000000000)
    | 92 => (4, 0x244020c04049140814200488402910a010810481, 0x10005000000050000000000020009000000000008000200010001000700060001000100030004000400020003)
    | 93 => (4, 0x2081805e3040406814080488142040293020244010a010810481, 0x300030000000000010006000000060000000000020003000000000003000c00000000000000040002000b0002000a000400040005000200010001000900080001000100050007000000000000)
    | 94 => (4, 0x244020c01408404914200488402910a010810481, 0x10005000000090000000000080005000000000002000700010001000300020001000100060004000400020003)
    | 95 => (4, 0x80618060302010812081048120c024402408142010a014080488, 0x20002000000000006000600000002000000000002000c00000000000b00010004000a000100030001000100050009000000000000000500030004000300080000000000000007000000000000)
    | 96 => (4, 0x30201081208120c024402408048110a0142014080488, 0x10005000a000100020001000100060009000000030000000600020005000200080000000700000004000400000003)
    | 97 => (4, 0x30201408240820c010a02081108104880481, 0x200030008000200020000000700000002000100040001000300000006000000030001000500010000000400010000)
    | 98 => (4, 0x142020c010813040208130202408140810a004810488, 0x2000200000000000900090000000100000001000200000002000200000003000400050003000700010003000100080008000700030005000100040001000600060005000400000000000a0000)
    | 99 => (4, 0x1081806440610481304030202081404924402408048810a0, 0x1000000000001000100000000000100000001000100000000000100010000000b00000000000000070003000a00030006000700060004000300020002000900050005000200040008000000000000)
    | 100 => (4, 0x404920c01081048114204029140810a00488, 0x10001000000010000000000010007000000000007000400020002000800060006000200030005000500040003)
    | 101 => (4, 0x208180663040406104811081402930201420140810a020c00488, 0x100010000000000020002000000020000000000020001000000000001000c00000000000000050004000b0004000a000500050006000400030003000900070007000300060008000000000000)
    | 102 => (4, 0x404920c01081048114204029140810a00488, 0x10001000000070000000000070001000000000001000600060002000300040002000200080005000500040003)
    | _ => (5, 0x80568045803480238012800130402440302020c0406840611420240840491408402910a02081108104880481, 0x3bc63289a2abdad288625386328100a3908280605b10c284619b0632850152442380c0924c638040590c43844189042384c158521510008040051124)
  (data.2.1 >>> (16 * ((data.2.2 >>> (data.1 * slot)) &&& ((1 <<< data.1) - 1)))) &&& 65535



def prior105 : List (Nat × Nat) := [(97, 4), (104, 4), (73, 4), (41, 4)]

theorem prepared105 : prepared 105 prior105 := by

  intro e h

  simp only [prior105,List.mem_cons,List.not_mem_nil,or_false] at h

  rcases h with rfl | rfl | rfl | rfl

  · exact zeroSlice_sound (by decide +kernel) bound97

  · exact zeroSlice_sound (by decide +kernel) bound104

  · exact zeroSlice_sound (by decide +kernel) bound73

  · exact zeroSlice_sound (by decide +kernel) bound41

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105slot7 : Impossible true (graphGoal 105) 5 (orbitState 105 1 0 1 true true).toFinset :=
  checkPlan_sound (program := certCode105) prepared105 5 1 [orbitChoice 105 1 0 1] (orbitState 105 1 0 1 true true) (by decide +kernel)

def orbit105map0 := ([83] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map0Onto : orbitOnto orbit105map0 orbit105map0.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map0Goal : movedWord orbit105map0 (graphGoal 105) = graphGoal 105 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105slot23 : Impossible true (graphGoal 105) 5 (orbitState 105 2 0 1 true true).toFinset :=
  orbit_transfer orbit105map0Onto orbit105map0Goal (by decide +kernel) orbit105slot7

def orbit105map1 := ([80] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map1Onto : orbitOnto orbit105map1 orbit105map1.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map1Goal : movedWord orbit105map1 (graphGoal 105) = graphGoal 105 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105slot39 : Impossible true (graphGoal 105) 5 (orbitState 105 2 1 1 true true).toFinset :=
  orbit_transfer orbit105map1Onto orbit105map1Goal (by decide +kernel) orbit105slot7

def orbit105map2 := ([99] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map2Onto : orbitOnto orbit105map2 orbit105map2.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map2Goal : movedWord orbit105map2 (graphGoal 105) = graphGoal 105 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105slot55 : Impossible true (graphGoal 105) 5 (orbitState 105 3 0 1 true true).toFinset :=
  orbit_transfer orbit105map2Onto orbit105map2Goal (by decide +kernel) orbit105slot7

def orbit105map3 := ([96] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map3Onto : orbitOnto orbit105map3 orbit105map3.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map3Goal : movedWord orbit105map3 (graphGoal 105) = graphGoal 105 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105slot71 : Impossible true (graphGoal 105) 5 (orbitState 105 3 1 1 true true).toFinset :=
  orbit_transfer orbit105map3Onto orbit105map3Goal (by decide +kernel) orbit105slot7

def orbit105map4 := ([80, 99] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map4Onto : orbitOnto orbit105map4 orbit105map4.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105map4Goal : movedWord orbit105map4 (graphGoal 105) = graphGoal 105 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit105slot87 : Impossible true (graphGoal 105) 5 (orbitState 105 3 2 1 true true).toFinset :=
  orbit_transfer orbit105map4Onto orbit105map4Goal (by decide +kernel) orbit105slot7

def saved105 : List (List Sig) := [orbitState 105 1 0 1 true true, orbitState 105 2 0 1 true true, orbitState 105 2 1 1 true true, orbitState 105 3 0 1 true true, orbitState 105 3 1 1 true true, orbitState 105 3 2 1 true true]

theorem saved105_sound : ∀ w ∈ saved105, Impossible true (graphGoal 105) 5 w.toFinset := by

  intro w hw

  simp only [saved105, List.mem_cons, List.not_mem_nil, or_false] at hw

  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl

  · exact orbit105slot7

  · exact orbit105slot23

  · exact orbit105slot39

  · exact orbit105slot55

  · exact orbit105slot71

  · exact orbit105slot87

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded105 : Impossible true (graphGoal 105) 6 (vars 105).toFinset :=
  orbitRoot_sound (program := certCode105) prepared105 saved105_sound (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 7 :=
  plain_low (hints:=3) (by decide +kernel) excluded105

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound112 : Lower true (vars 112) (graphGoal 112) 4 :=
  carry_of (old := 112) (rep := 41) (swaps := [64, 99]) (by decide +kernel) bound41

def certCode27 (node slot : Nat) : Nat :=
  (0xd0a0583058a090208900910088104880481 >>> (16 * ((0x200000008000000020005000500020004000100020001000000030007000000010000000000040003000100060001 >>> (4 * slot)) &&& 15))) &&& 65535



def prior27 : List (Nat × Nat) := []

theorem prepared27 : prepared 27 prior27 := by

  intro e h

  simp [prior27] at h

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded27 : Impossible true (graphGoal 27) 3 (vars 27).toFinset :=
  checkPlan_sound (program := certCode27) prepared27 3 0 [] (vars 27) (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound27 : Lower true (vars 27) (graphGoal 27) 4 :=
  plain_low (hints:=67) (by decide +kernel) excluded27

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound29 : Lower true (vars 29) (graphGoal 29) 4 :=
  carry_of (old := 29) (rep := 27) (swaps := [33]) (by decide +kernel) bound27

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound60 : Lower true (vars 60) (graphGoal 60) 4 :=
  carry_of (old := 60) (rep := 27) (swaps := [33, 80, 16]) (by decide +kernel) bound27

def certCode61 (node slot : Nat) : Nat :=
  let data : Nat × Nat × Nat := match node with
    | 0 => (5, 0x8007403c800480011820401d0e181810128510a00e0c0685068c142014080a040890403110810a100881048804814029, 0x4ca500e0304e1000ca3328a53052132929304a1000a5011e405def010a4b392e908a2ab8a59092200063005a1001ad004610106300108011080006301d070086201c630090204421011840458c010213094231c213082131d4702c840080202e8b00882)
    | 1 => (5, 0x8003800204880e1818100e0c0a0412a41820068c4029142014080a10108108810481, 0x2042005810218c00441014420008001484000400248401c420244201c840408400c4303c4200c8301821001600196b000200194a01c210182101d4a00d030182100c210190801ca50240001c00024a5034a500c000340000ca3018ce000000000000000)
    | 3 => (4, 0xe0c1810182010810a040488068c142010a014080a1008810481, 0x10000000c0000000800010001000800010003000b0001000200010001000a000500000000000400000005000300000005000000000002000600040004000300070007000600020000000000090000)
    | 4 => (5, 0xe0c182006858006403112a4128540298005401d04881408142010a010810a040a1008810481, 0x1000000001200000000010000300003000010000300001000010000300001000040001100001000030000100001000030000000002000100000000006000000000000005000000000400006000000000f00000000000000e00002000050000d0000200002000040000c00002000020000b0000a00002000040000500000000090000800000000000000000007000000000000000)
    | 6 => (4, 0x1820068c1285068510a0089014080a040a101081088104880481, 0x2000500050002000500010002000100020003000c0002000500000002000000040001000b000100040003000a00040004000000090000000100080003000100000007000000010006000000030000)
    | 7 => (5, 0x8009800810810e180e0c1820160c0a040890128510a00a1040291420088104880481, 0x1042001800118c00040021280044102042005210104201d6b0116b01c4201442011290152901042004610200000400020680280001c630286301c000340001465034630140001c21028c601cc60282104021014c503cc6014210108e000000000000000)
    | 8 => (4, 0xe0c182040290e18068c140804880a0414200a1010a0108108810481, 0x10000000d000000010002000c00010006000100010006000400010001000b00000002000500000005000000000003000a000000000004000300020002000900080000000000000007000000000000)
    | 9 => (4, 0xe0c182010a00a0408901420160c0a101081048808810481, 0x10000000b000000010003000a000100070002000100020001000800080001000000030006000000020000000000070000000400060000000500020003000200030004000500040000000000090000)
    | _ => (4, 0xe0c182040290e18068c048814080a0414200a1010a0108108810481, 0x10000000d0000000600010001000600010002000c0001000400010001000b00050000000000030000000200050000000a000000000004000200030002000900080000000000000007000000000000)
  (data.2.1 >>> (16 * ((data.2.2 >>> (data.1 * slot)) &&& ((1 <<< data.1) - 1)))) &&& 65535



def prior61 : List (Nat × Nat) := [(41, 4), (49, 4), (29, 4), (60, 4)]

theorem prepared61 : prepared 61 prior61 := by

  intro e h

  simp only [prior61,List.mem_cons,List.not_mem_nil,or_false] at h

  rcases h with rfl | rfl | rfl | rfl

  · exact zeroSlice_sound (by decide +kernel) bound41

  · exact zeroSlice_sound (by decide +kernel) bound49

  · exact zeroSlice_sound (by decide +kernel) bound29

  · exact zeroSlice_sound (by decide +kernel) bound60

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit61slot5 : Impossible true (graphGoal 61) 5 (orbitState 61 1 0 1 false true).toFinset :=
  checkPlan_sound (program := certCode61) prepared61 5 1 [orbitChoice 61 1 0 1] (orbitState 61 1 0 1 false true) (by decide +kernel)

def orbit61map0 := ([80] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit61map0Onto : orbitOnto orbit61map0 orbit61map0.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit61map0Goal : movedWord orbit61map0 (graphGoal 61) = graphGoal 61 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit61slot118 : Impossible true (graphGoal 61) 5 (orbitState 61 4 1 1 true false).toFinset :=
  orbit_transfer orbit61map0Onto orbit61map0Goal (by decide +kernel) orbit61slot5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit61slot103 : Impossible true (graphGoal 61) 5 (orbitState 61 4 0 1 true true).toFinset :=
  checkPlan_sound (program := certCode61) prepared61 5 4 [orbitChoice 61 4 0 1] (orbitState 61 4 0 1 true true) (by decide +kernel)

def saved61 : List (List Sig) := [orbitState 61 1 0 1 false true, orbitState 61 4 1 1 true false, orbitState 61 4 0 1 true true]

theorem saved61_sound : ∀ w ∈ saved61, Impossible true (graphGoal 61) 5 w.toFinset := by

  intro w hw

  simp only [saved61, List.mem_cons, List.not_mem_nil, or_false] at hw

  rcases hw with rfl | rfl | rfl

  · exact orbit61slot5

  · exact orbit61slot118

  · exact orbit61slot103

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded61 : Impossible true (graphGoal 61) 6 (vars 61).toFinset :=
  orbitRoot_sound (program := certCode61) prepared61 saved61_sound (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound61 : Lower true (vars 61) (graphGoal 61) 7 :=
  plain_low (hints:=1027) (by decide +kernel) excluded61

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 7 :=
  carry_of (old := 91) (rep := 61) (swaps := [33, 101]) (by decide +kernel) bound61

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 7 :=
  carry_of (old := 113) (rep := 105) (swaps := [67]) (by decide +kernel) bound105

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound90 : Lower true (vars 90) (graphGoal 90) 4 :=
  carry_of (old := 90) (rep := 27) (swaps := [96]) (by decide +kernel) bound27

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound81 : Lower true (vars 81) (graphGoal 81) 4 :=
  carry_of (old := 81) (rep := 41) (swaps := [67, 101]) (by decide +kernel) bound41

def certCode123 (node slot : Nat) : Nat :=
  let data : Nat × Nat × Nat := match node with
    | 0 => (6, 0x80df809a807b8046800130402840244018200d1830202810218320c01810140810a00d0a0583058a1120142024081102090240710890405b403b407a2081108109100881048804814069, 0x25f18620568591f69a20518501e18620364301e6592031832dd1862013812dd38e2011810001862046040236182041841d73972021828971861c238201c14524358301c5962431432cf1452415412cf55524114101014524434401034d2441441d43542421428541451c23420000c30014c10004d30010c10040c301030c00430c0100c31ca30a0020c200a0c31c230201b04100448401b4920040411c23c22ca0412c20411ca3ca1d11040020020118111c2102)
    | 1 => (6, 0x80378035802780184071800b8002407004883040284024400d183020281018100d0a1102405b0902182021c21408407a11204069058a142024080910406820811081088104814032, 0x45a1040035838da5960031031591040025422995550021020181040011c10181c700110100e1c700910400e1040091c71621c70061068601040061c614f0c344250228f5141420c20080c34413417c834d0010c100c4923090c331e0c300949214b34b4460c674b0c314634600a0821414c128a4d300108100c41014908214a0820094101463c614b08214608214b3cb00920800e04100904100e20815720800604171704100620614c29b000000000000000000)
    | 2 => (5, 0x80098007800310a0405b140a091014083142150a281030200d0a4070090221c240321102182028402440058a142040491120240810814068208108810481, 0x2c420068102e940044102842000a0028a50004003ca50244203c42024a500ca50184607842018a6058420126405a7301044074a50384207042038a500c210024000e520002000e100242100c210261000d8c0182100c210198600c210118400d8c0102100d6b01c2100c2101d6b0250803c000240003d0800d08018000440001906054000110405508010000454a03800044000394a01cfb000000000000000011240346d013440352d01ce7000000000000000010e400cc60000000cf901cf800000000000000000c77000000000000000)
    | 3 => (5, 0xd0a28408006406824408005403210a0800430400910140824080902182011021420302011202081108108810481, 0x1000000001600000000090000100001000090000800001000010000400001000020000800001000010000300015000010001400001000010001300006000000000000006000060000000000000040000000002000060000000000000030001200000000110000000000000100000f00000000000000000002000070000200007000030000500003000050000e0000000000000000000200004000020000d000040000500003000040000c000000000000000000020000300005000020000b0000000000000000000a000000000000000)
    | 4 => (5, 0xd0a1820284024401120091010a024080902089011021420302020811081088104880481, 0x2000000001100000000080000100002000010000200003000100000200002000040000f0000200002000090000900002000010000000000000080000000003000060000000000000040000e0000000000000060000600000000010000d000030000100001000050000400001000010000c0000b000010000300004000050000300003000070000700003000040000a0000500004)
    | 5 => (4, 0x28400d0a04880910302009021820110214081420112024082081108108810481, 0xa00010001000a0009000100010005000100020009000100010003000f0001000e000000010000000d000000000000000200080002000800030004000300040000000600000006000200050002000700050004000300050000000c0000000600020003000b000200070000000200000004000000030000)
    | 6 => (4, 0x24400d0a08903020140824081102090211202810142009102081108108810481, 0x50000000000050005000000000004000000020005000000000003000f0000000e000000000001000d00000000000000020009000200090003000600030006000100080001000800040007000200040004000600030004000100070001000400020003000c0002000b000100020001000a000100030001)
    | 7 => (5, 0xd0a281010a08008403214082081090218202840110209102440058a21c23040142011202408108108810481, 0x10000000015000000000e00001000010000e0000d00001000010000400001000020000d00001000010000300014000010000c00001000010000c000050000000000000050000500000000000000400000000020000500000000000000900003000000000900000000000000900013000000000000000000020000b000020000b000080000300007000030000700008000080000700002000040000200006000040000300012000040000a0000a0000400011000020000300006000020001000002000020000600000000000000f00000)
    | 8 => (5, 0xd0a28402440058a20c010a0140809021820110209102408142011202081108108810481, 0x10000000011000000000a00001000010000a00001000020000900001000100000100001000030000900001000010000400005000000000000005000000000200005000000000f0000000000000030000500000000000000400002000080000200008000030000e000030000d0000c0000000000000000000b0000200002000030000400002000020000600007000070000400006)
    | 9 => (5, 0xd0a20c021c2058a10a014083142140a800a240a40322408090218201102091028402440142011202081108108810481, 0x10000000017000000000b00001000010000b00001000020000a0000100007000010000100007000010000300007000010000a000010000100004000050000000000000050000000002000050000000006000000000000006000000000300006000000000500000000000000400002000090000200009000160000000000000000000300015000030001400013000000000000000000120000000000000000000200003000110000200004000020000200010000030000f000030000e0000800008000040000d0000c000000000000000)
    | 10 => (5, 0xd0a2840244010a0058a20c0140809021820110209102408142011202081108108810481, 0x10000000011000000000a00001000010000a0000100002000090000100009000010000100004000100000100001000030000500000000000000500000000020000500000000050000000000000040000f000000000000003000020000800002000080000e000000000000000000030000d000030000c000040000200002000060000b00002000020000300007000070000400006)
    | 11 => (6, 0x801780148011800e800c40704051110228400d1840710488281030200d0a405a090221c2182014202440405b4069058a10a0406824081081208140490910088104814032, 0x1191450025422d955500214200d1450011c100d1c70011412211c700314381f1450031c310c14500650631e5140061464901c700a14575014500a1c700b0821014c12cb4d30010812033c31090822030821093c910c0821063c610b3cf10608248b45110a0822cb08210a45121838e00304171804100338310c0410063866d738e00604148a34d0100415ca04101034d1060c32082493062461080c310a0d610425630a2492080c300001a000000000000000000)
    | 12 => (5, 0xd0a18202840800d304021c2058a2408142030202440403209021081208110a0091008810481, 0x100000000120000000002000010000100003000010000500011000010000600001000010000600001000040001000001000060000100001000060000a00000000000000200000000050000a0000000008000000000000008000000000400008000000000f000000000000007000020000300005000020000200003000030000200002000090000400002000020000300003000020000e0000000000000000000500004000090000500007000000000000000000040000d00000000070000c0000000000000000000b000000000000000)
    | 13 => (4, 0x1820284014083020142004882440090210a0240810812081091008810481, 0x200010001000600010004000e0001000700010001000700010003000d000100070000000100000002000600040002000900090006000200020005000300020000000600000002000c00000000000000040003000b0004000a000000040000000300050003000500000008000000080005000000030000)
    | 14 => (5, 0x8010800f405a1102404920810d18048840680d0a09022840182040691420244010a0058a3020304010814032091008810481, 0xc21001e002def000200098202021008210218802dce0142102c21015ce00c21019ad02dad0182102c210118402d8c010210494a00800048000094201d290140001c000152900c000192900d290180000c000114400d4a0100001c510151101d080144200c4201866060770184201042041080110404042018e6058a5018a600ce7010e400cb5010a400ce700e93000000000000000)
    | 16 | 83 | 101 => (5, 0xd0a1102405b240a240809100902244020c0058a30403020406818201420108108810481, 0x10000000011000000000b00001000010000b0000100002000040000100004000010000100004000040000100001000040000a00000000000000a00000000020000300000000030000000000000030000300000000000000300002000100000200008000090000900008000070000600007000060000f0000500002000020000e0000d0000200002000050000c000000000000000)
    | 17 => (5, 0x1102801380124029406824080d1804880d0a28400902250a405b40691820058a2440142010a020c0403210812081091008810481, 0x142100220032310002003421011640316b01021031ef0182103021019ef0142100e030321000c210096201c210082101d6701400011040150801000029290180002800019260380000d230392900c0004d080080004c0000902014b90000000000000000148400ca3034b800c8401ee70088201c84009a200d43038c600cc30394a01ed2008d201cc7009a2016b4000000000000000)
    | 18 | 73 | 106 | 119 => (5, 0xd0a284018102440110230204068091009021820142020c010a014082081108108810481, 0x1000000001100000000090000100001000090000100003000100000100008000010000100005000080000100001000020000400000000000000f00000000030000e00000000070000000000000050000700000000000000200004000060000300004000050000600005000040000200006000020000d0000c0000000000000000000b000020000300002000000000a0000000000)
    | 19 | 74 | 107 | 120 | 153 | 217 => (5, 0x40324029110240680d180488405b0d0a24400902250a40691820058a142020c010a01081091008810481, 0x5021001a0025ad000200256b01421024210156b009020102100821011040242100d030250800c2101d8c0140001c0001585040c60080004000008c20280000cc3028c600c000126f008af010a4009c200ce3028b200ca3028e700c420448400c8303842)
    | 20 => (5, 0xd0a284011028016801521c24029240a09102408090220c0405b2440058a4068182014202081108108810481, 0x1000000001500000000010000200005000010000b00001000010000b0000500001000010000500001000030001400001000050000100001000050000000002000040000000008000000000000008000040000000000000040000000003000080000000004000000000000004000130000000000000000000600002000020000600002000030001200002000110000200002000090000a0000a0000700006000030001000003000070000f0000700007000090000300006000000000e0000d0000000000000000000c000000000000000)
    | 21 | 76 => (5, 0xd0a28401810244020c021c2058a11023020240809021820142009101408208110a0108108810481, 0x10000000013000000000900001000010000900008000010000100003000010000400012000010000800001000010000200005000000000000011000070000000000000030000000004000100000000007000000000000002000030000f0000300005000050000e0000400005000020000d000020000c000030000b0000400003000060000600002000030000a000020000400002)
    | 22 | 77 => (5, 0xd0a405b11020910240a24080902244020c030403020058a406818201420108108810481, 0x10000000011000000000b00001000010000b0000400001000010000400004000010000100004000010000200004000010000a00000000000000a0000300000000000000300003000000000000003000000000200003000000000900009000060000800007000080000700010000020000f00002000060000e0000000000000000000200005000020000d000020000c0000200005)
    | 23 | 78 => (5, 0x1102208128400d1804880d0a090218202810244014203020058a4032406810a020c024081081091008810481, 0x20210020001e100002001c2100dc301dce00c2101def0142101c21015ef03421012640366d01021009c20182100821019c60200000d630216b00c000258c014000240001585010000358c01184034000496b0080004800009620211500000000000000002863011040290a01063018e60086201863008e20292a010a5028a501124018b10093101926008a20000000000020f400000)
    | 24 => (5, 0x80248021801e80190488406824080d1818103040405b0d0a28402440110209021820250a1408058a406911204031142020c00910208110810881048140294032, 0xbc84a8ee35bef708c834a084009a2021ad488820023101c8407c8401e3108084016c507ad609484ea9aaa9886e2884a99a64806308a8202e94088620021009c6302c6309e1008063096650ae7309463599e60a863598630a9ea0310849c420304249d080b842496454ba52094420610849842060424990609585038e7014e50b98c0843b00000000000000000359000000000000000)
    | 25 => (5, 0xd0a2840801d40692440801c403220c0058a10a0801b30203040801a140a09101408090218201102112014202081108108810481, 0x1000000001900000000080000100001000080000100003000180000100007000010000100005000010000200007000010001700001000010001600004000000000000004000000000300015000000000400000000000000500000000020000400000000140000000000000130000300012000030001100010000000000000000000020000600002000060000f0000000000000000000e00000000000000000003000020000d000020000c0000000000000000000200005000000000b0000a00000000000000000009000000000000000)
    | 26 | 49 | 126 | 158 => (5, 0xd0a2840244010a0058a20c0140809021820110209102408142011202081108108810481, 0x10000000011000000000a00001000010000a0000900001000010000400001000020000900001000100000100001000030000500000000000000500005000000000000004000000000200005000000000f0000000000000030000e00000000000000000002000080000200008000030000d000030000c00002000040000200006000070000700004000060000b000020000200003)
    | 27 | 127 | 157 | 180 => (5, 0xd0a28401820244030203040058a20c01120091010a0090208901102142020810488108108810481, 0x100000000130000000001000040001200001000070000300001000030000100002000110000100001000080000800001000000000400010000000000300000000000000700000000020000500000000000000500005000000000f00000000000000000004000020000e00002000040000d0000c00004000030000b0000200003000030000a000090000300002000060000600002)
    | 28 | 128 => (5, 0x28400d0a20c0058a048824083040244009100902182011021120140814202081108108810481, 0x9000010000100009000010000300012000010000800001000010000600001000020000800001000110000000001000000000300010000030000f0000e00000000000000000002000070000200007000000000400000000040000d00000000000000000003000020000c000020000b00000000030000000002000060000200005000000000a000000000400005000000000200000)
    | 29 | 129 => (5, 0x24400d0a20c0058a08902810304028401408110209021120142009102081108108810481, 0x500000000000000500000000030001100000000050000000000000040000000002000050000000010000000000000001000030000f000030000e0000d00000000000000000002000080000200008000010000700001000070000c00000000000000000003000020000b000020000a000010000300001000040000600002000040000100006000010000400009000010000200001)
    | 30 => (5, 0xd0a284018102440058a10a0802040293020801f4068110009101081090240321820112020c014202081140808810481, 0x100000000170000000009000010000100009000010000300016000010000700001000010000600001000020001500001000070000100001000070000400000000000000400000000030001400000000040000000000000060000000004000020000000004000000000000004000030000500003000130001200000000000000000005000020001100002000100000500005000080000f00000000000000000003000020000e000020000d0000300003000080000c000000000600002000000000b000000000000000000000000a00000)
    | 31 | 131 | 163 => (4, 0xd0a181010a0402930400910090220c010811820112020811420140808810481, 0x10000000f000000090001000100090006000100010005000600010001000600010002000e00010003000000000003000300000000000500030000000000030000000300020000000d000000000000000c00080008000b00040002000400020000000a0000000000040005000500020004000200070007)
    | 32 | 132 | 162 => (5, 0xd0a284024401810302040680910110218200902142020c0208110a01408108108810481, 0x10000000011000000000100005000100000100009000010000100004000090000100001000020000800001000010000800000000050000f0000000007000000000000004000070000000000000020000300000000000000e0000d0000000000000000000c00002000050000200006000030000500003000000000b0000000000000060000400004000030000600002000020000a)
    | 33 => (5, 0x48880238022406810810d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e1000020025ef0142102c21015ef00ce30102100c21010e403421020e702ce70202102c21018e702ce701821028420140002800014420444200c000440000c43024000204202442020000380001842038420180003196000000000000000024a502128025b5020a501946038a5018a60394a020630508402084034630186304c84018840346303192000000000000000)
    | 34 | 63 | 134 | 146 | 168 => (4, 0xd0a181010a0402930400910090220c010811820112020811420140808810481, 0x10000000f0000000900010001000900010002000e00010006000100010005000600010001000600030000000000030000000300020000000300000000000500030000000000030004000200040002000d000000000000000c00080008000b000500040005000200020004000700070000000a00000000)
    | 35 | 135 | 169 => (5, 0x40324068402911020d180488405b0d0a24400902250a18204069058a142010a020c00910108108810481, 0x5021001a0021ad0002000d230142100c2101525020210092202129008210216b01021020210116b040c600c000400000cc302800008c2028c60080001d8c0100001c00011840086304ca5008a2038630106f048af010a5038630115101c420104201d47)
    | 36 => (5, 0x4068240880268025402911020d1804880d0a28400902250a405b18204069058a1420244010a020c0403220811081091008810481, 0x14210022002e3100020014210120402e10010210098201c210082101d870342100d8302d8c00c2102def0182102c21019ef0380001104039080100004d290080004c00009220140000d230152900c0002908018000280001906017380000000000000000148400ca3015b700c83019c60288401884029ca00c42058e700ce30344201852054f2018e703442014b4000000000000000)
    | 37 | 137 | 152 | 165 | 216 => (5, 0xd0a284024401810302040681102091009021820142020c0208110a01408108108810481, 0x10000000011000000000100005000100000100009000010000100009000080000100001000040000800001000010000200000000050000f000000000300000000000000e0000700000000000000400007000000000000002000060000300005000030000d0000000000000000000c000020000500002000040000600004000030000200006000020000b000000000a0000000000)
    | 38 | 138 | 166 => (5, 0x40324029406811020d180488405b0d0a24400902250a40691820058a142010a020c00910108108810481, 0x5021001a0025ad0002000d030142100c21015050256b01021024210116b02421009020250800821040c600c000400000cc301d8c0100001c000118402800008c2028c6008000106f04caf010a50386300863048a5008a203863008e20289100882028e7)
    | 39 => (5, 0x80328030802e802c802820c0240a0910240818103040405b0d0a28402440110209024031250a21c2058a1820140840324068402914202081108108810481, 0x2442006a1026b5004410104200100011080004001def0284207842029ef0190804c42074420190801c4200e830729400c4206d0804c420684204d0801c210024001a520002001dce0282101821029ce0192901421018210152901c2100e2301a3100c21019290142101821015290288402c000280002c8401c840340001c00034840300000e030321000c0001c840340001c0003484014b900000000000000000d430316b00d630314a014a500000000000000000ca3018e60000001cb8014b700000000000000001cd6000000000000000)
    | 40 => (5, 0xd0a2840802b40682440802a403210a0802930400910240814080902182011021420302011202081108108810481, 0x1000000001600000000090000100001000090000800001000010000400001000030001500001000010000200008000010001400001000010001300006000000000000006000060000000000000040000000003000120000000000000020000600000000110000000000000100000f00000000000000000003000050000300005000020000700002000070000e000000000000000000040000500003000040000200004000020000d0000c000000000000000000030000200005000020000b0000000000000000000a000000000000000)
    | 41 => (5, 0xd0a2840182024401120091010a024080902089011021420302020811081088104880481, 0x2000000001100000000080000100002000010000200004000100000200002000030000f00002000020000900009000020000100000000000000800000000040000e00000000000000300006000000000000006000060000000001000050000400001000010000d0000300001000010000c0000b0000100004000030000500003000040000a000050000400003000070000700003)
    | 42 => (4, 0x28400d0a04880910302009021820110214081420112024082081108108810481, 0xa00010001000a000900010001000500010003000f00010001000200090001000e000000010000000d000000000000000300040003000400020008000200080000000600000006000500040003000500020005000200070000000c0000000600030002000b000200040000000300000007000000020000)
    | 43 => (4, 0x24400d0a08903020240814081102090211202810142009102081108108810481, 0x5000000000005000500000000000400000003000f00000000000200050000000e000000000001000d00000000000000030006000300060002000900020009000100080001000800040006000300040004000700020004000100070001000400030002000c0002000b000100030001000a000100020001)
    | 44 => (5, 0xd0a28401810244010a0802d40291100240810810902091040321820058a3020142011201408208108810481, 0x10000000015000000000b00001000010000b0000800001000010000400001000020001400001000010000300013000010000800001000010000800005000000000000005000050000000000000040000000002000120000000000000050000300000000050000000000000050001100000000000000000002000060000200006000070000300010000030000f000070000700009000040000600002000040000e0000400004000030000a0000a0000900004000020000300006000030000d00002000020000600000000000000c00000)
    | 45 => (5, 0xd0a284024401810302020c0240821c2058a110218200902142009101408208110a0108108810481, 0x10000000013000000000900001000010000300001000040001200001000090000100001000020000800001000010000800007000000000000003000000000400011000000000700000000000000200005000000000000010000030000f0000400003000060000600002000030000e0000300003000050000d0000200004000020000c0000500004000050000b00002000020000a)
    | 46 => (5, 0xd0a20c04029802f21c20910240a405b240810810902058a314230204068304020811820142008810481, 0x10000000014000000000a00001000010000a000030000100001000030000300001000010000300001000030000300001000010000300003000010000200000000000000200002000000000000002000020000000000000020000000002000020000000000000020000200000000130000000000000000001200000000000000000009000050001100005000040001000004000090000f000000000000000000080000500008000050000400006000040000e0000500007000070000d000040000c00004000060000b000000000000000)
    | 47 => (5, 0xd0a0910240a2408405b11020902244020c0406830403020058a18201420108108810481, 0x10000000011000000000400001000010000400004000010000100004000010000200004000010000b00001000010000b0000300000000000000300003000000000000003000000000200003000000000a00000000000000a000100000000000000000000200008000020000f00009000090000500007000020000e00002000080000700006000060000d0000c000020000200005)
    | 48 => (5, 0xd0a21c2058a10a020c0240831428031240a140a40321408090218201102091028402440142011202081108108810481, 0x10000000017000000000b00001000010000b000010000300007000010000a00001000010000400001000020000a000010000700001000010000700005000000000000005000000000300006000000000500000000000000400000000020000500000000060000000000000060000300016000030001500014000000000000000000020000900002000090001300000000000000000012000000000000000000030000200011000020001000003000030000f0000200004000020000e0000800008000040000d0000c000000000000000)
    | 50 => (5, 0xd0a2840240a09102408803421c2803340291102090220c0405b24404068058a182014202081108108810481, 0x1000000001500000000050000100001000050000100003000140000100005000010000100005000010000200005000010000b00001000010000b00004000000000000004000000000300008000000000400000000000000400000000020000400000000080000000000000080000300007000000001300012000000000000000000020000700002000070000a0000a000060000700011000000000000000000030000200010000020000f000030000300006000020000e0000200009000060000d00006000090000c000000000000000)
    | 51 => (5, 0xd0a284024401810302020c021c22408058a110209021820142009101408208110a0108108810481, 0x10000000013000000000800001000010000300001000040001200001000090000100001000090000800001000010000200007000000000000003000000000400011000000000500000000000001000007000000000000002000030000f00004000030000e000030000300005000060000600002000030000d0000500004000050000c000020000400002000020000b000020000a)
    | 52 => (5, 0xd0a0910240a405b240811020902244020c0304030204068058a18201420108108810481, 0x100000000110000000004000010000100004000040000100001000040000b00001000010000b0000100002000040000100003000000000000003000030000000000000030000a00000000000000a0000000002000030000000010000000000000000000090000900005000080000200006000020000f0000800007000070000e000020000d0000200006000020000c0000200005)
    | 53 => (5, 0x80362081304028400d180488181030200d0a2440110209021820140828101120058a403114204068240820c0091010810881048140294032, 0xbc8440ea343eb508c8352484009c2025ce50882002310188406c8401a310d08401f270533409c84431cc4148543084415c55006308a62022730886200210098630206309a100b46309f070b70d09c63415e50b063414630b1ec02d295184202c425192909c425365251e470b44205d295144205c42515250816b01cc6000c609d67084d6095760016b014c500000000000011a00000)
    | 54 => (5, 0x2081110228400d1804880d0a090218202810142024403020058a4068403210a020c024081081091008810481, 0x1c2100200022100002003421012640366d01021009c20182100821019c60202100dc3021ce00c21021ef0142102021015ef010000356b01164034000498c00800048000098201c0000d8301d8c00c000256b014000240001565000000000001d150000001c8400d4301d4a00c83014850254a015450248400c42020c600cc30204202451014d1024c60144201cf4000000000000000)
    | 55 => (5, 0x48880438041803e803c80381142108120810d184031405b3142406840490d0a0902284024404069402921c21820112030403020058a14200910088140320481, 0x442002000321000040005ef0144203042015ef00d230204200c42021280504201d290312901c4200442019ce031ce018420304202d290312902c42014840280001400028840588400c000580000c830040001c840048401c0000400019ad005ad018000040005484004840540002d7f000000000000000004a501c270069e01ca7004a5019460054a018a6004a50054a0054a004a504c6301d0804d0801c6300463018260743c0186306c6304908069080486301966044e7000000057902d7800000000000000000637000000000000000)
    | 56 => (5, 0xd0a2840803b40682440803a403210a0803930401408240809100902182011021420302011202081108108810481, 0x10000000016000000000900001000010000900001000020000800001000010000300015000010000800001000010000400014000010000100013000060000000000000060000000002000060000000000000030001200000000060000000000000040001100000000000001000002000070000200007000030000500003000050000f0000000000000000000e000000000000000000020000300005000020000400002000020000d0000c000000000000000000050000400003000040000b0000000000000000000a000000000000000)
    | 57 | 263 => (5, 0xd0a18202840244011202408091010a00902089011021420302020811081088104880481, 0x20000000011000000000200003000100000200002000040000f0000200008000010000200001000020000900009000020000000003000060000000000000040000e000000000100000000000000800000000060000600000000030000400005000030000d0000100003000010000300007000070000300005000010000400001000040000c0000500004000010000b0000a00001)
    | 58 => (4, 0x28400d0a04883020091009021820110214081420112024082081108108810481, 0xa00010001000a000100020009000100010003000f00010009000100010005000e00000001000000020008000200080003000400030004000d000000000000000000060000000600020003000c000200050002000200070007000000020000000400050003000500040000000300000000000b00000006)
    | 59 => (4, 0x24400d0a08903020140824081102090211202810142020810910108108810481, 0x5000000000005000000020005000000000004000f00000005000000000003000e00000000000100020009000200090004000600040006000d000000000000000100080001000800020004000c00020007000300020003000b0001000200010006000300040003000a0001000400010001000700010003)
    | 60 => (5, 0xd0a284024400488803d14082408112009021102304018203020142009102081108108810481, 0x10000000012000000000a00001000010000a00001000020000700001000010000300011000010000400001000010000700001000070000700001000050000000000000050000000002000050000000000000030001000000000050000000000000040000000005000050000000002000090000200009000030000600003000060000f00000000000000000000000000000e000000000200003000060000200008000040000200004000020000d000080000200006000040000300004000030000c000060000300000000000000b00000)
    | 61 | 267 => (5, 0xd0a18202840244021c2302020c02408090214201102058a048810a020811081091008810481, 0x10000000012000000000100003000110000100001000040001000001000020000100001000050000a00001000010000a0000000003000090000000000000040000f00000000090000000000000020000700000000000000e00003000040000d0000300005000020000300002000080000300003000080000c0000200004000020000b00004000040000700006000060000500002)
    | 62 => (5, 0x804004881081803f40680d180d0a0902250a4029405b4069058a403230401820208120c011200910142008810481, 0x24210020002e1000020025ef0142102c21015ef03021020e702ce70202102c21018e702ce70182100ce30102100c21010e40284201400028000144202400020420244202000038000184203842018000444200c000440000c43024a50212802596020a501946038a5018a60394a035b5000000000000000035b40000000000000000126400d030110400d830124400cc3010c400d83)
    | 64 | 147 | 203 | 238 | 251 | 270 => (5, 0x40324068110240290d180488405b0d0a24400902250a18204069058a142020c010a01081091008810481, 0x5021001a0021ad000200202100d230212900c21009220102100821011240216b01421020210156b0280000cc3028c600c00040c60080004000008c201d8c0140001c0001585012640086201063009c20155201c630146301d470144f0448f0148403842)
    | 65 => (5, 0xd0a804221c220c040291081405b240a240809100902058a314230204068304020811820142008810481, 0x10000000014000000000a00001000010000a000010000300003000010000100003000030000100003000010000100003000030000100001000030000200000000000000200000000020000200000000000000200002000000000200000000000000200002000000000000002000090000500013000050000400012000040000900011000000000000000000100000000000000000000f000000000000000000050000800008000050000700005000070000e0000600004000040000d0000c0000400004000060000b000000000000000)
    | 66 | 272 => (5, 0xd0a240a240811020910405b09022440406820c0058a3040302018201420108108810481, 0x10000000011000000000100002000040000100004000010000100004000040000100001000040000b00001000010000b0000000002000030000000003000000000000003000030000000000000030000a00000000000000a000090000200002000100000f0000200002000090000e0000200002000070000d000000000000000000080000800007000060000600005000050000c)
    | 67 => (5, 0x8045804440492081405a11020d18406804880d0a28400902182040691420244010a0058a3020304010814032091008810481, 0xc21001e002def000200098202021008210218800c21019ce02dce0182102c210118402d8c0102102dad0142102c21015ad0494a00800048000094200c000192900d290180000c000114400d4a0100001d290140001c000152900c420186606077018420104204508011040444201c500151001d080144200ed50000000000000000168501cc6014c601c670147301c840148401c67)
    | 68 | 144 | 199 | 235 | 241 | 243 | 246 | 259 | 274 => (5, 0x40321102406840290d180488405b0d0a24400902250a40691820058a142020c010a01081091008810481, 0x5021001a0025ad000200242100d030250800c210256b01421024210156b009020102100821011040280000cc3028c600c0001d8c0140001c0001585040c60080004000008c20155301c630146301d47012440086201063009c20122f008af010a4009c2)
    | 69 | 244 | 275 => (5, 0xd0a1102240a2408405b091009022440406820c0058a3040302018201420108108810481, 0x1000000001100000000010000200004000010000b00001000010000b0000400001000010000400004000010000100004000000000200003000000000a00000000000000a0000300000000000000300003000000000000003000100000200002000070000900002000020000f0000e000020000200009000080000800007000060000500006000050000d0000c000000000000000)
    | 70 => (6, 0x806c8066805d805c80578054804711030488110228400d184051406811832810218330200d0a18200583405b405a407114202440407a11202408090210a040691081208109100881048140494032, 0x5c1450035c31dc5d700314300d14500228200d28a0021420471450045841e659600414400c28a00814802514500828805114500654646455500614642328a0001458a114500028a0070c30425021c75140020c20440c304b24904424904b0c300c2490480c36470c30082490510c30464c60474d30460c34072490410c31c70c304124905b08200448469b49200408200c38e00808200f08200838805108200638668f38e00608240f34d0000823cf08200034d00c1040483086473200081040581040462c60582cb0461044071040412cb1c72cb04110404604600020800000000005f04105e00000000000000000000001d000000000000000000)
    | 71 => (6, 0x8051804f804e804b8048405140701102284040710d180488281030200d0a405a090221c2182024401420405b4069058a10a0406824081081208140490910088104814032, 0x1191450025422d955500214200e1450011c100e1c700114110c1450065063215140061464901c700a14581014500a1c721f1c700314379d1450031c300b0821014c12cb4d300108110c0821063c610b3cf10608248b45110a0822cb08210a4512033c31090822030821093c910c04100634671834d00604148a38e01004160a04101038e21734d0030416d704100334300001a000000000000000000209209103183309186103203109116103296309289203203)
    | 72 => (5, 0x1102804a80494029406824080d1804880d0a28400902250a405b40691820058a2440142010a020c0403210812081091008810481, 0x142100220032310002003421011640316b01021031ef0182103021019ef0142100e030321000c210096201c210082101d6701400011040150801000029290180002800019260380000d230392900c0004d080080004c0000902014b90000000000000000148400ca3034b800c8401ee70088201c84009a200d43038c600cc30394a01ed2008d201cc7009a2016b4000000000000000)
    | 75 => (5, 0xd0a28401102804d804c21c24029240a09102408090220c0405b2440058a4068182014202081108108810481, 0x1000000001500000000010000200005000010000b00001000010000b0000500001000010000500001000030001400001000050000100001000050000000002000040000000008000000000000008000040000000000000040000000003000080000000004000000000000004000130000000000000000000600002000020000600002000030001200002000110000200002000090000a0000a0000700006000030001000003000070000f0000700007000090000300006000000000e0000d0000000000000000000c000000000000000)
    | 79 => (5, 0xd0a182028408050304021c2058a2408142030202440403209021081208110a0091008810481, 0x1000000001200000000010000500011000010000200001000010000300006000010000100006000010000400010000010000600001000010000600000000050000a000000000a00000000000000200008000000000000008000000000400008000000000f000000000000007000030000200005000020000e0000000000000000000500004000090000500007000000000000000000020000300003000020000200009000040000200002000030000300002000040000d00000000070000c0000000000000000000b000000000000000)
    | 80 => (4, 0x1820284014083020142004882440090210a0240810812081091008810481, 0x10004000e00010002000100010006000700010001000700010003000d000100070000000100000006000200040002000c00000000000000040003000b0004000a000000040000000900090006000200020005000300020000000600000002000300050003000500000008000000080005000000030000)
    | 81 => (5, 0x405a110280538052404920810d18048840680d0a09022840182040691420244010a0058a3040302010814032091008810481, 0xc21001e002def0002002dce0182102c21019ce0098202021008210218800c21015ad02dad0142102c210118402d8c0102101d290180001c00019290494a00800048000094200c000152900d290140000c000114400d4a01000020d1008f1020e8008c2014e5060c6014c500ce7010e400cd7010c400ce700c420146505875014420104204108011040404200e93000000000000000)
    | 84 => (6, 0x405b80568055401b04881102405a24080d18403111830d0a182028400583244021c22183402930403020142020c040691120090210a0208110810910403208810481, 0x20410005400095550000400030410081c70031c70080410021c70060410090410061c70200410045040095140040410020410054c50094d30050410091c700e04100904100e1c70180000034830184920030000022cb0060000020000062c60020000042c40022cb0040000020000054450024510050000027de0170000020000170820100c30060860100900060c30160c30042040162080040c300f0c300508500f08f0050c30090c300e20800920800e0c300428400d18600418400d28a00518600c28a00528500c18600275c00000000000000000000c10400534500c34c00510400209b000000000000000000002699000000000000000000)
    | 85 => (5, 0x89011020c981c182c184069118305833040244018202840058a218320c0302040321420140810a0240811200902208109101081088104880481, 0x104201cc6010c601c42068c60044106842004c10644200e430665200c420604201625062310144205cc60004005c42000c0040840058104190004810588400ce3058e700c8403c840158503d8f0148405484000e0054e70008000c210292900d230282101421021ce015c5020210002002d3c0012002c2103463016850368d0146302d5b0006002c630014004d08000a004ca500100)
    | 86 => (5, 0x1820284021c2218304883020140824082440403120c01420112010a0208109021081091004810881, 0x400004000000000400000000000000400000000030001300000000000000500012000000000400000000000000400004000010000000001000020000600011000020000200003000070000200002000050001000002000020000700007000020000200001000070000100003000060000300009000060000900005000060000f0000000000000000000100006000010000800003000050000e000030000d000000000000000000080000100003000010000c0000000000000000000b000010000500001000000000a0000000000)
    | 87 => (5, 0xd0a182028400583805a80582183110320c0401b3040405a402924081420302024404032112010a0108120810902091008810481, 0x1000000001900000000010000300003000010000300001000010000300001000050001800001000030000100001000030000100004000170000100003000010000100003000000000200016000000000b00000000000000600000000050000b0000000009000000000000009000000000400009000000001500000000000000800002000060001400002000020000500007000020000200007000070000200002000040001300002000020000700007000020000500006000000001200011000000000000000000060000a0000400006000100000000000000000000f00000000000000000005000040000a0000500008000000000000000000040000e00000000080000d0000000000000000000c000000000000000)
    | 88 => (5, 0xd0a182028408059304021c2058a2408142030202440403209021081208110a0091008810481, 0x1000000001200000000010000500011000010000600001000010000600001000040001000001000060000100001000060000200001000010000300000000050000a0000000008000000000000008000000000400008000000000f0000000000000070000a0000000000000020000e000000000000000000050000400009000050000700000000000000000003000020000500002000040000d00000000070000c000000000000000000030000200003000020000b0000000000000000000900002000040000200003000020000300002)
    | 89 => (4, 0x18202840140830201420048824400902240810a010812081091008810481, 0x10004000e0001000700010001000700010003000d000100020001000100050007000000010000000c00000000000000040003000b00040005000200040002000a000000040000000300060003000600090009000500020000000800000008000600020003000200060000000300000000000500000002)
    | 90 => (5, 0x18202840805b21831103048814083020142024401120240810a0108109022081091008810481, 0x1000040000400001000040000100001000040000100005000120000100004000010000100004000010000300011000010000400000000010000000002000060001000002000020000500008000020000200008000080000200002000030000f00002000020000000008000000000500006000000000e0000d000000000000000000060000700003000060000000006000000000a0000c00000000000000000005000030000b000050000a000000000500000000030000700003000070000000009000000000900007000000000300000)
    | 91 => (4, 0x18202840140830201420244004880902240810a010812081091008810481, 0x10004000e0001000700010001000700010003000d000100070000000100000002000100010005000c00000000000000040003000b0004000a0000000400000005000200040002000300060003000600000009000000090008000800050002000600000003000000060002000300020005000000000002)
    | 92 => (5, 0x1102208128400d184031118304880d0a1820058321c2250a28104069405a1420402924403040112020c00902240810a009101081403208810481, 0x821002a003eb50002001021024e7010e702421008e70142103c21014e70382100e8303e9400c210402101b460435001821038e70302103c21030e706400012640667301000009ad0140000800015a50080000da3009ad00c00018000416b01966040000096b06000008000616b0488401445048520148405c8400d2305d2900c8404484018460445101884038840312903d290308400d03028a500ca302908008a50190800908018a500916030b6008a50090800863019460394a018630095c03063008630094a0000000000009db00000)
    | 93 => (5, 0x806380600488805e401b1103405a1142110220810d183142118340490d0a1820058340292840142024404069112030400902302010a010810910088104814032, 0x420062102a310044100c42024e700ce702442000e70144202842014e7028e70204202842020e700042019ad029ad01842028420120402a10010420542100de3055ef00c210018c0142100021015850016b02021000210216b000210196b0016b0182100021011840018c0102100063014050281f014630506302129051290206300063018060281e0186304c630112404d29010630025d000000000000000000a5018060001c018a501364000a5010a40001a019c60650801906001d8011c400117011040000000256000000000000000)
    | 94 => (5, 0x805f1102114211030d1821c211834029048840490d0a18200583244014204069112020c0090210a009101081088104814032, 0x42005c1025ce0044101042020c6010c602042024c601c420244201cc60244200da3025ad00c42000c60144202442014c605021011840518c010210016b01c210002101d670002100d430014a00c210014a01421000210154504c8401d0804d0801c840488400d030490800c840008401405024180148400e23000f700ce3000000163003cf0014e5000160140503c630146300015)
    | 96 => (5, 0x40490488401b8062806111020d1811830d0a18204029406914202440250a3040112010a0090240321081091008810481, 0x1021001e0031ef00020010a50182103021018a5030a50202103021020a50302100dc3031ce00c210082101ca5008a501c210116b0180001000019660114a02000010000214a0240000d630256b00c0004400009420454a00800012f600000000000000000ea3024c600cc302489010c60088201293008c200da30251200d030248901da70090201d07009a201c6300a0201e0700862)
    | 98 | 117 | 222 => (5, 0xd0a1102058a048a20811183405b09101820142004884029244020c0090210a0108108810481, 0x10000000012000000000400001000010000400001000020000a00001000010000400004000010000a00001000010000300006000000000000005000000000200009000000000000006000060000000009000000000000003000020001100002000100000700005000050000f00008000080000300007000020000e0000d000020000300002000020000c0000b000000000000000)
    | 99 => (5, 0x405a110240492081806580640d18048840680d0a09022840182040691420244010a0058a3040302040321081091008810481, 0x1021001e002def0002002dce0182102c21019ce01021015ad02dad0142102c2100d8302d8c00c210098202021008210218801d290180001c0001929010000152901129014000100000d430114a00c000494a008000480000942014e5060c6014c5010e700ce3010d700cc3010e7020d1008f1020e8008c2012d5000000000000000010a50088201293008a202208008620206300a02)
    | 102 => (5, 0x8069110280671103405a24080d18118321c2405b404904880d0a182028400583218340292440142040691120090220c010a0208110810910088104814032, 0x420064102a520044100c420250800d0802442054420122402a31010420290801c420284201d08000420160502a1001442001080184202842019080602100de3061ef00c2100021011640016b010210018c01c210002101d8700021015850018c014210016b01821000210196605c630112405d29010630586301d290592901c6303863014050380e0146300063018060281e018630001d00000000000000000084014050541c014840180605084018840001b015a5068e7014e5001a0019b3050f3018e60000000019000000000000000)
    | 103 => (5, 0x80681142110211030d1821c211830488402940490d0a18200583244014204069112020c0090210a009101081088104814032, 0x42005c1025ce0044101042020c6010c602042024c601c420244201cc6000c60144202442014c60244200da3025ad00c4205021011840518c010210016b01c210002101d670014a0142100021015450002100d430014a00c2104c8401d0804d0801c84000840140502418014840488400d030490800c840161103cf1014e50001700e03000f600ce30000000de3000a500ca300015)
    | 105 => (5, 0x1102806b806a4029406824080d1804880d0a28400902250a405b40691820058a2440142010a020c0403210812081091008810481, 0x142100220032310002003421011640316b01021031ef0182103021019ef0142100e030321000c210096201c210082101d6701400011040150801000029290180002800019260380000d230392900c0004d080080004c0000902014b90000000000000000148400ca3034b800c8401ee70088201c84009a200d43038c600cc30394a01ed2008d201cc7009a2016b4000000000000000)
    | 108 => (5, 0x1103048880798076110280738071806d208140310d18405b11830d0a182040492840406914204029250a11202440090210a0218310810910088104814032, 0x42006210363100441000e70184203442018e704c42012040361001042034e702c420344202ce700042015ce035ce0144200c42024e700ce7024420018c01821000210198600021011840018c0102100108054210002105508028210150802908014210502100d030510800c21011e4000c6000000001e001fd000000000000000014c60280a01405028c6000c600c030039b00cc30001a000000000000000000840140504c19014840248400e430264900c83015650280a014050296a0256900f03026e900d63001f6000000000000000)
    | 109 => (5, 0xd0a182080704029806f4031048814082081806e09102840142011203040244020c01102090210a0108108810481, 0x10000000016000000000400001000010000400001000020001500001000010000b0000b0000100001000040000400001000140000100001000130000a00000000000000300000000020000a000000000000007000070000000000000090000700000000120000000000000110000200003000020000500003000060000600003000030000900006000030001000000000000000000002000080000800002000020000500005000020000f0000000000000000000e0000000000000000000d0000000000000000000c000000000000000)
    | 110 | 210 => (5, 0xd0a18202408140830402081284014202440048820c0091011021120090210a0108108810481, 0x10000000012000000000400001000010000400001000020001100001000010000400004000010000c00001000010000c0000b00000000000000300000000020000b00000000000000500010000000000a00000000000000a000020000300002000060000300005000080000300009000090000300008000020000600006000020000f00002000020000e0000700007000050000d)
    | 111 => (5, 0x18200d0a10a0089014082081091028403040110224401120090220c01081088104880481, 0x500001000020000100002000030001100002000020000a0000a000020000200005000050000200010000000000200000000010000f00003000010000100004000040000100001000060000400001000000000e000000000100003000090000900003000030000800008000030000d0000000003000000000c000000000000000000070000000007000000000b000000000600000)
    | 112 => (5, 0xd0a10a011021408208114200488304028400902244020c009101081089008810481, 0xb00000000000000200000000030000b00000000000000600006000000000000004000060000000010000000000000001000020000f000030000200002000050000500002000020000400005000020000a0000a00001000020000300009000090000300003000040000e000040000d0000100003000010000c0000000000000000000800001000080000100007000010000700001)
    | 113 => (5, 0xd0a1820240880721120284014200488304020c0110224400910090210a0108108810481, 0x10000000011000000000400001000010000400001000020001000001000010000c0000c0000100001000040000400001000040000100001000040000b00000000000000300000000020000b000000000000006000060000000000000050000600000000060000000000000060000200003000020000700003000080000800003000030000500008000050000a0000a00003000080000200009000090000200002000050000700005000070000200002000070000f00000000000000000000000000000e0000000000000000000d00000)
    | 114 | 214 => (4, 0xd0a18202440058a1120142005830488208110a0110209021081091008810481, 0x10000000f0000000400010001000400010003000e000100010004000400010004000100010004000a00000000000600000003000a000000000002000d0000000900000000000900030006000300050006000200070002000800080006000c0003000200050002000500030003000500020007000b0002)
    | 115 => (5, 0x4049048880758074401b11020d1811830d0a182040294069142024403040250a112010a0090240321081091008810481, 0x1021001e0031ef00020010a50182103021018a5030a50242103021024a50082101ca5008a501c210302100dc3031ce00c210116b0180001000019660114a02400010000254a04400009420454a008000200000d630216b00c00012f6000000000000000010c600882012b4008c200e63020c600cc30208801da70092201d27009a200da30213200d23020880404200ce3040e700c42)
    | 118 => (5, 0x1102807880774029406824080d1804880d0a28400902250a405b40691820058a2440142010a020c0403210812081091008810481, 0x142100220032310002003421011640316b01021031ef0182103021019ef0142100e030321000c210096201c210082101d6701400011040150801000029290180002800019260380000d230392900c0004d080080004c0000902014b90000000000000000148400ca3034b800c8401ee70088201c84009a200d43038c600cc30394a01ed2008d201cc7009a2016b4000000000000000)
    | 121 => (5, 0xd0a11022183807a405b048a2081406809102840182014201183058a04884029090210a0244020c0108108810481, 0x100000000160000000001000020000c0000100006000010000100006000010000d0000d00001000010000600006000010000c00001000010000500000000020000b000000000400000000000000300000000040000400000000000000400004000000000b0000000000000050001500000000000000000002000140001300002000020000a0000a0000200005000020000200012000090000300003000090000700003000030001100008000080000500007000100000000000000000000f0000000000000000000e000000000000000)
    | 122 | 219 => (5, 0xd0a048a1102058a091020811183405b1820142004884029244020c0090210a0108108810481, 0x100000000120000000004000010000100004000010000400004000010000a00001000010000300001000020000a000010000600000000000000500000000060000600000000090000000000000030000000002000090000000007000050000500011000080000800003000070000200010000020000f0000e0000000000000000000d000020000c000020000200003000020000b)
    | 123 => (6, 0x8094808e808b807c407a0488240818200d18181014083040405b0d0a28400583244021c22183112040691420110220c0090240312081108109100881048140294032, 0x591455035c33195d70431431cb14500258200b5961c214204d14550428430d28a04414400028a00914502014500928a04014500654601f55504614500028a01414501e14500028a1c00c30424c200c4d30420c20440c304d20804420804d0c30002080490c300c0c30492080400c304648604c4920460c30002080410c300c0c30412080580821c44441d84510440820002cb1c90820000821c92cb0400821c64061c04100460820002cb1c70820000821c72cb00f10404900900f00f04910404e10404600604e00e04610400010404100c00c01d04110404604600024900000004005c04105b00000000000000000000001a000000000000000000)
    | 124 => (5, 0x808880858082807d0488406824080d1818103040405b0d0a28402440110209021820250a1408058a406911204031142020c00910208110810881048140294032, 0xbc84a8ee35bef708c834a084009a2021ad488820023101c8407c8401e3108084016c507ad609484ea9aaa9886e2884a99a64806308a8202e94088620021009c6302c6309e1008063096650ae7309463599e60a863598630a9ea0310849c420304249d080b842496454ba52094420610849842060424990609585038e7014e50b98c0843b00000000000000000359000000000000000)
    | 125 => (5, 0xd0a28408081406924408080403220c0058a10a0807f30203040807e140a09101408090218201102112014202081108108810481, 0x1000000001900000000080000100001000080000100003000180000100007000010000100005000010000200007000010001700001000010001600004000000000000004000000000300015000000000400000000000000500000000020000400000000140000000000000130000300012000030001100010000000000000000000020000600002000060000f0000000000000000000e00000000000000000003000020000d000020000c0000000000000000000200005000000000b0000a00000000000000000009000000000000000)
    | 130 => (5, 0xd0a284018102440058a10a080844029302080834068110009101081090240321820112020c014202081140808810481, 0x100000000170000000009000010000100009000010000300016000010000700001000010000600001000020001500001000070000100001000070000400000000000000400000000030001400000000040000000000000060000000004000020000000004000000000000004000030000500003000130001200000000000000000005000020001100002000100000500005000080000f00000000000000000003000020000e000020000d0000300003000080000c000000000600002000000000b000000000000000000000000a00000)
    | 133 => (5, 0x48880878086406810810d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e1000020025ef0142102c21015ef00ce30102100c21010e403421020e702ce70202102c21018e702ce701821028420140002800014420444200c000440000c43024000204202442020000380001842038420180003196000000000000000024a502128025b5020a501946038a5018a60394a020630508402084034630186304c84018840346303192000000000000000)
    | 136 => (5, 0x40682408808a8089402911020d1804880d0a28400902250a405b18204069058a1420244010a020c0403220811081091008810481, 0x14210022002e3100020014210120402e10010210098201c210082101d870342100d8302d8c00c2102def0182102c21019ef0380001104039080100004d290080004c00009220140000d230152900c0002908018000280001906017380000000000000000148400ca3015b700c83019c60288401884029ca00c42058e700ce30344201852054f2018e703442014b4000000000000000)
    | 139 => (6, 0x405b808d808c401b0488405a240811020d18403111830d0a284018200583244021c22183402930403020142020c040691120090210a0208110810910403208810481, 0x20410005400095550000400030410081c70031c70080410021c70060410090410061c70020410055050095140050410200410044c40094d30040410091c700e04100904100e1c70180000034830184920030000022cb0060000020000062c60020000054450024510050000020000042c40022cb0040000027de0170000020000170820100c30060860100900060c300f0c300508500f08f0050c30160c30042040162080040c30090c300e20800920800e0c300518600c28a00528500c18600428400d18600418400d28a00275c00000000000000000000d14500430400d30c0041440026da000000000000000000002099000000000000000000)
    | 140 => (5, 0x89011020c982c181c184069118305833040244028401820058a218320c0302040321420140810a0240811200902208109101081088104880481, 0x104201cc6010c601c42068c60044106842004c1064420164506652014420604200e230623100c4205cc60004005c42000c00408400581041900048103c840158503d8f014840588400ce3058e700c8405484000e0054e70008001421021ce015c50202100c210292900d23028210002002d3c0012002c21050a500da3051ad00ca304d08000a004ca50010002d5b0006002c6300140)
    | 141 => (5, 0x2840182021c2218304883020240824401408403120c01420112010a0208109021081091004810881, 0x400004000000000400000000000000400000000050001300000000000000300012000000000400000000000000400004000010000000001000020000600011000020000200005000100000200002000030000700002000020000700007000020000200001000070000100006000090000500006000030000600003000090000f0000000000000000000100006000010000800005000030000e000030000d0000000000000000000c0000100005000010000b00000000000000000008000010000300001000000000a0000000000)
    | 142 => (5, 0x80910488808f401b1142240810810d1831422183405b40490d0a058321c2402940691820112009023040302020c0208114200910088104814032, 0x4200601032100044100c420292900d2902842001290184203042019290012901c420304201d29048420216b0316b02042030420156b0316b014420542100de3055ef00c21000840182100021018840008401c210002101c84000210208400084020210002101484000840142103863018060380e018630006301c070301c01c63050630214a0514a0206304c630154a04d4a01463035bb000000000000000000c6020080025a020c601725000c6014c50000002228000e7020e70001801625000f7014e500000035b6000000000000000)
    | 143 => (5, 0x80901103114211020d18118321c24049048840290d0a18200583244014204069112020c0090210a009101081088104814032, 0x42005c1025ce0044101042020c6010c602042000c60144202442014c60244200da3025ad00c42024c601c420244201cc605021011840518c010210014a0142100021015450002100d430014a00c210016b01c210002101d670008401405024180148404c8400d0304d0800c840488401d080490801c8400e23000a500ca30001701e3003cb001ca50001601c1503c6301c6300000)
    | 145 => (5, 0x809304881081809240680d180d0a0902250a4029405b4069058a403230401820208120c011200910142008810481, 0x24210020002e1000020025ef0142102c21015ef03021020e702ce70202102c21018e702ce70182100ce30102100c21010e40284201400028000144202400020420244202000038000184203842018000444200c000440000c43024a50212802596020a501946038a5018a60394a035b5000000000000000035b40000000000000000126400d030110400d830124400cc3010c400d83)
    | 148 => (5, 0x809724088095405a110311020d18118321c2405b404904880d0a284018200583218340291420244040691120090220c010a0208110810910088104814032, 0x420064102a520044100c420250800d0802442000420162502a310144200108018420284201908054420120402a10010420290801c420284201d080602100de3061ef00c2100021015650016b014210018c01821000210198600021011840018c010210016b01c210002101d6703863014050380e0146300063018060281e0186305c630112405d29010630586301d290592901c630001d000000000000000000a501004002bc010a401f67034a501ca50340001284000c6010c40001a01e93034d301cc60000000019000000000000000)
    | 149 => (5, 0x80961142110311020d1821c211830488404940290d0a18200583244014204069112020c0090210a009101081088104814032, 0x42005c1025ce0044101042020c6010c602042000c60144202442014c6024c601c420244201cc60244200da3025ad00c4205021011840518c010210014a0142100021015450016b01c210002101d670002100d430014a00c210008401405024180148404c8401d0804d0801c840488400d030490800c8401e1103cb101ca50001700e03000a500ca30001600de3000f500ce300000)
    | 151 => (5, 0x8099406824081102809840290d1804880d0a28400902250a405b40691820058a2440142010a0403220c020811081091008810481, 0x1821002200323100020018210120403210010210342100d630316b00c21031ef0142103021015ef0096201c210082101d67038000112403929010000180000d030190800c000292901400028000152504d080080004c00009020188400cc3019b900c83015c50288401484029ca01b17000000000000000018d600000000000000001ea70086201c63009a201e92008b201ca7009a2)
    | 154 => (6, 0x407180d080c380ba80b880aa809b208118200d181810140810a00d0a3040405b284011201420250a1102403b09020890244020c04069218340324031091010810881048804814029, 0x1b10450364325b6590031031911045016018d16181811011d73d75021028971041c23c200e1043885553a15550081040121045053c58123cf0051051890c30015812495960010c11cc34c0020c224c0c300234200e0c30084d30094d30080c30050c301234d00534d0120c31c244218c0411c204118c44c0100411882cb1902cb00804101a0411852c519a2cb0050410080821d028a1c828a01008201f0821c528579d28a00508200e25c000000000000000000)
    | 155 => (5, 0x80a780a480a1809c4068240804880d1818103040405b0d0a28402440110209021820250a1408058a406911204031142020c00910208110810881048140294032, 0xbc84a8ee35bef708c834a084009a2021ad4888208084016c507ed6094840023101c840788401e31ea9aaa9886e2884a99a64806308a8202e940886208063096650ae73094630021009c6302c6309e10599e60a863598630a9ea0b842496454ba52094420310849c420304249d080610849842060424990601dc70b0a501ca50b1cc0037a00000000000000008439000000000000000)
    | 156 => (5, 0xd0a284080a040692440809f403220c0058a30203040809e10a0809d140a09101408090218201102112014202081108108810481, 0x100000000190000000001000030001800001000080000100001000080000700001000010000500001000020000700001000170000100001000160000000003000150000000004000000000000004000040000000000000050000000002000040000000014000000000000013000120000300003000110001000000000000000000003000020000f000020000e0000000000000000000d000000000000000000020000600002000060000c0000000000000000000200005000000000b0000a00000000000000000009000000000000000)
    | 159 => (5, 0x28400d0a20c0058a240830402440048809100902182011021120140814202081108108810481, 0x1000030001200001000090000100001000090000800001000010000600001000020000800001000110000000001000000001000003000030000f0000e00000000000000000003000020000d000020000c0000000003000000000b000000000000000000020000700002000070000000004000000000400002000060000200005000000000a000000000400005000000000200000)
    | 160 => (5, 0x24400d0a20c0058a28103040284008901408110209021120142009102081108108810481, 0x30001100000000050000000000000050000500000000000000400000000020000500000000100000000000000010000f00003000030000e0000d00000000000000000003000020000c000020000b0000100003000010000a0000000000000000000200008000020000800001000070000100007000040000600002000040000100006000010000400009000010000200001)
    | 161 => (5, 0xd0a284018102440058a302080a3406810a080a24029110009101081090240321820112020c014202081140808810481, 0x100000000170000000001000030001600001000090000100001000090000700001000010000600001000020001500001000070000100001000070000000003000140000000004000000000000004000040000000000000060000000004000020000000004000000000000004000050000300003000130001200000000000000000003000020001100002000100000300003000080000f00000000000000000005000020000e000020000d0000500005000080000c000000000600002000000000b000000000000000000000000a00000)
    | 164 => (5, 0x4068240880a680a5402911020d1804880d0a28400902250a405b18204069058a1420244010a020c0403220811081091008810481, 0x14210022002e3100020014210120402e10010210098201c210082101d870342100d8302d8c00c2102def0182102c21019ef0380001104039080100004d290080004c00009220140000d230152900c0002908018000280001906017380000000000000000148400ca3015b700c83019c60288401884029ca00c42058e700ce30344201852054f2018e703442014b4000000000000000)
    | 167 => (5, 0x48880a980a8406810810d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e1000020025ef0142102c21015ef00ce30102100c21010e403421020e702ce70202102c21018e702ce701821028420140002800014420444200c000440000c43024000204202442020000380001842038420180003196000000000000000024a502128025b5020a501946038a5018a60394a020630508402084034630186304c84018840346303192000000000000000)
    | 170 => (5, 0x80b580b380b180af80ab2081048a0910048840681810405b0d0a403230402840250a18204031058a14081102090224402183142020c01081088104814029, 0x346300a82036940086201463005410154a004610006301a1007a10018630006304d2907529000630452901063070630112906d4a04c630686304d4a0004200641002520044100042019ef001ef018420004200108001080004200108010420004201108001ad0004200042001ad03821018e7038e70182100021030e7030e70002102ca50102102c21010a5030a50302103021030a500019000000000000000011c402ccb010c402dcb002b5000000000000000012240000000000000180023700000000000000000016000000000000000)
    | 171 => (5, 0xd0a182080ae402980ad4031208180ac0910048814082840142030401120244020c01102090210a0108108810481, 0x1000000001600000000010000b0000b000010000100004000040000100004000010000100004000010000200015000010001400001000010001300000000070000700000000000000800007000000000a00000000000000300000000020000a00000000120000000000000110001000000000000000000006000030000600003000090000200009000020000f00000000000000000008000030000600003000050000200005000020000e000000000000000000020000300002000050000d0000000000000000000c000000000000000)
    | 172 => (5, 0xd0a182024082081140830402840142024400910048820c011201102090210a0108108810481, 0x10000000012000000000100004000040000100004000010000100004000010000200011000010000c00001000010000c000000000600010000000000b00000000000000300000000020000b000000000a00000000000000a00006000030000700003000050000200005000020000900009000060000f00002000030000200005000080000800003000070000e00002000020000d)
    | 173 => (5, 0x18200d0a2081091010a00890140828403040244011021120090220c01081088104880481, 0x20000a0000a00002000020000500005000020000500001000020000100002000030001100002000100000000002000000000f00000000000000000004000010000400001000090000300009000030000800000000080000000006000010000400001000070000300007000030000e000000000600000000010000d0000300001000000000c00000000010000b000000000300000)
    | 174 => (5, 0xd0a2081110210a0140814203040284009020488244020c009101081089008810481, 0x60000600000000000000400006000000000b00000000000000200000000030000b00000000100000000000000010000f000000000000000000050000200005000020000a000030000a00003000090000100009000010000400002000050000200004000030000e0000400008000010000800001000020000d0000300002000070000700001000020000c000010000300001)
    | 175 => (5, 0xd0a1810208180b04068402911004032108128401820091004882440218309021420112020c0140810a008810481, 0x1000000001600000000010000d0000d000010000100007000070000100007000010000100007000010000300015000010000c00001000010000c00000000090000900000000000000500009000000000600000000000000200000000060000300000000060000000000000060001400000000000000000004000020000400002000080000300013000030001200008000080001100005000020000400002000100000500005000030000b0000b0000f00005000040000200002000030000a0000a000040000200000000000000e00000)
    | 176 => (5, 0xd0a1810244030402081058a218318200910048820c01081090214201120140810a008810481, 0x100000000120000000001000060000600001000060000100001000060000b00001000010000b0000100003000110000100000000040001000000000050000000000000020000500000000000000500000000050000300000000040000200008000020000a0000a0000f000040000e000040000400003000090000900008000020000d0000200002000030000c000030000700007)
    | 177 => (5, 0xd0a20814068218380b20910048a405b1102284018201420058a118304884029090210a0244020c0108108810481, 0x1000000001600000000010000d0000d00001000010000600006000010000c00001000010000500001000020000c000010000600001000010000600000000040000400000000000000400004000000000b00000000000000500000000020000b0000000004000000000000003000150000000000000000001400000000000000000013000020001200002000030000a000030000a0001100000000000000000009000020000900002000030000700003000100000200005000020000f000080000800005000070000e000000000000000)
    | 178 => (5, 0xd0a0910048a20811183405b1102058a1820142004884029244020c0090210a0108108810481, 0x1000000001200000000010000400004000010000a0000100001000030000400001000010000400001000020000a000010000000006000060000000009000000000000003000060000000000000050000000002000090000000011000000000000000000050000700005000100000f000020000e00002000080000800003000070000200003000020000d000020000c000020000b)
    | 179 => (5, 0xd0a302020810488118380b4048a140a40321081284018202440058a304009100902112020c01420110208810481, 0x1000000001600000000010000c0000c00001000060000100001000060000b00001000010000500001000020000b0000100001000060000600001000000000a0000a0000000003000000000000003000030000000000000050000000002000030000000000000030000300000000040000900004000090001500000000000000000008000020000800002000140000000000000000001300000000000000000004000020001200002000110000400004000100000200005000020000f0000700007000050000e0000d000000000000000)
    | 181 => (5, 0xd0a048a0910048880b780b64068108124402081058a405b21830902402920c030401820142008810481, 0x10000000014000000000100007000070000100007000010000100007000030000100001000030000100003000030000100001000030000300001000000000c0000c00000000020000000000000020000200000000000000200000000020000200000000000000200002000000000500006000000001300012000000000000000000040000600004000060000b0000b000080000600011000000000000000000050000400010000050000a00005000050000a000040000f0000400009000080000e00008000090000d000000000000000)
    | 182 => (5, 0xd0a1810244020813040058a218318200910048820c01081090214201120140810a008810481, 0x10000000012000000000100006000060000100006000010000100006000010000300011000010000b00001000010000b00000000040001000000000050000000000000020000000005000030000000005000000000000005000040000200008000020000f0000400004000030000a0000a0000e000040000d00002000020000300009000090000800002000030000c0000700007)
    | 183 => (5, 0xd0a091020811183048a405b1102058a1820142004884029244020c0090210a0108108810481, 0x1000000001200000000010000400004000010000a00001000010000300001000020000a0000100004000010000100004000000000600006000000000900000000000000300000000020000900000000060000000000000050001100000000000000000010000020000f000020000500007000050000e0000200003000020000d000080000800003000070000c00002000020000b)
    | 184 => (5, 0x80b920c018200d1818101408304010a00d0a284011201420110240320902089024404031250a0910048820811081088104814029, 0x5c6300aa205eb500862438634068143a944046100063012640667301063649b26146564863615a503c63019a603dad0186600042006210023100441000420120400210010420296a0144502842015650184203d6b0196b03c4201c210112401d2901021415c54282141421429ca05821019260592901821000e70148500084014e500084018e6000e70188600000000000301800000)
    | 185 => (5, 0x20c010810d1840310d0a2440403209020890250a182010a0304020811420112040290910048808810481, 0x1021002000121000020031ac0082203021009a200c21015ad00dad01421010210214a0114a020210102101d4a0114a01c21008c20300000800030cc0480000de3049ef00c0004400020c6044c60200002c0001cc602cc601c00000000000003894000000384202129039290204201c4202d2901d2902c4202063010a5020a50106302c6301ca502ca501c6301093000000000000000)
    | 186 => (5, 0x80c180bf80bb3020405b108309101081150a118340320d0a18202840250a3040404940310890244020c010a0218314200902112011020881048804814029, 0x63006610027300461030cc0086203063008c20006302231002310206300063014c6000c6014630006301244002520106300063000c6000c600063008e20302100821030ec040210216b0416b0202100021015650356b0142105821010e4058e70102103421034e7034e703421020420414a0214a0404200042015450794a0144205442011290552901042074420512907129050420001b00000000000000003d0f0100403f4f01104001ce000000000000000011c4000a50000000019001d800000000000000000017000000000000000)
    | 187 => (5, 0xd0a182080be402980bd4031208180bc0910140804882840142030401120244020c01102090210a0108108810481, 0x1000000001600000000010000b0000b0000100001000040000400001000010000200015000010000400001000010000400014000010000100013000000000700007000000000000008000070000000000000020000a000000000a000000000000003000120000000000000110001000000000000000000009000020000900002000060000300006000030000f00000000000000000005000020000500002000080000300006000030000e000000000000000000030000200002000050000d0000000000000000000c000000000000000)
    | 188 => (5, 0xd0a182024082081140830402840142024400910048820c011201102090210a0108108810481, 0x10000000012000000000100004000040000100001000020001100001000040000100001000040000c00001000010000c0000000006000100000000000000020000b000000000b0000000000000030000a00000000000000a00005000020000500002000060000300007000030000900009000060000f000030000200002000050000e00002000020000d00008000080000300007)
    | 189 => (5, 0x18200d0a2081091010a01408089028403040244011021120090220c01081088104880481, 0x20000a0000a00002000020000500005000020000200003000110000200005000010000200001000100000000002000000000f00000000000000000009000030000900003000040000100004000010000800000000080000000007000030000700003000060000100004000010000e0000000006000000000d0000100003000010000c000000000300000000000000b0000000001)
    | 190 => (5, 0xd0a2081110210a0140814203040284009020488244020c009101081088108900481, 0x600006000000000000004000060000000000000030000b000000000b000000000000001000100000000000000020000f0000000000000000000a000030000a00003000050000100005000010000900002000090000200004000030000e0000400004000010000500001000080000200008000020000d0000100003000010000c00002000030000200007000070000200001)
    | 191 => (5, 0xd0a1820208180c0402910a0284008903040091024401420250a21831120090211020488108108810481, 0x1000000001400000000010000e0000e0000100001000050000500001000010000200013000010000d00003000010000300001000050000500001000000000a0000a0000000000000060000a00000000000000200009000000000300000000000000d00000000090000900000000120000000000000000000c000020000c00002000080000300007000030000700008000080000700004000020000400002000060000300011000030000b0000b0000600010000040000300002000030000200004000040000200000000000000f00000)
    | 192 => (5, 0xd0a2840182024403040058a20c030201120091010a0090208901102142020811081048808810481, 0x1000000001300000000010000400012000010000100003000110000100001000080000800001000070000200001000020000000004000100000000000000030000500000000000000500005000000000200000000000000700004000030000f00003000040000e0000d000040000c000000000000000000030000600006000030000b0000200003000020000a000020000900002)
    | 193 => (5, 0xd0a2081302010811183140a80c2048a403204882840182024403040058a09100902112020c01420110208810481, 0x1000000001600000000010000c0000c0000100001000020000b0000100001000060000600001000060000100001000060000b000010000100005000000000a0000a0000000000000020000300000000000000300003000000000300000000000000300003000000000000005000090000200009000020001500000000000000000004000080000400008000140000000000000000001300000000000000000002000040001200002000050000200002000110000400010000040000f0000700007000050000e0000d000000000000000)
    | 194 => (5, 0xd0a28401820244030403020058a20c01120091010a0090208901102142020811081048808810481, 0x1000000001300000000010000400012000010000100003000110000100007000020000100002000010000800008000010000000004000100000000000000030000500000000020000000000000070000000005000050000000004000030000f000030000e000000000000000000040000d0000c000040000b00002000030000200003000060000600003000020000a0000900002)
    | 195 => (5, 0x405180cf80cc80c980c680c410810d1840710d0a244020c0401b250a090208904049405b4069182010a040323040218340311420112009100881048804814029, 0x3b463006c16b6d60046154230008626c06300a22010630163101231014637b8630258c7b58c024639b4630218c6b58c02063508c23c021508213c0d006021392a43e2b5010217b8213a4c6fdcc63a4219c8213a0c6bc8c63a0210784251284ef294010427b8425256b76d6b524429a0425496bd216b548427a484000a5724a5000847a084000a5720a50008400019000000000000000)
    | 196 => (5, 0xd0a244080c510812183250a048820c040321820142010a009021120091008810481, 0x1000000001000000000010000400004000010000100007000070000100001000070000700001000040000100001000040000400001000010000400000000020000f000000000000006000060000000000000060000600000000060000000000000050000e000000000000008000020000300003000020000200003000030000200002000050000900002000020000300003000020000d0000000000000000000500009000050000900008000000000000000000050000c00000000080000b0000000000000000000a000000000000000)
    | 197 => (4, 0x20c0108108901820090210a0142011200910088104880481, 0x200070007000200020008000800020002000800080002000700010002000100070000000200000003000400040003000300040004000300030001000b00010003000000040000000a00000000000000060001000600010005000000050000000600010006000100050000000500000000000900000001)
    | 198 => (5, 0x80c880c7401b1102404904880d1811830d0a182040294069142024403040250a112010a0090240320910108108810481, 0x1021001e0031ef0002000c2101ca500ca501c2103021009c2031ce00821010a50182103021018a5030a50242103021024a50440000d430454a00c0002000009620216b008000116b0180001000019660114a02400010000254a04063008e2040e700863010630188605c960186302463034e7024e703463019060544201842011080251403442024420110801272000000000000000)
    | 200 | 247 | 260 => (5, 0xd0a1102058a20811183405b048a09101820142004884029244020c0090210a0108108810481, 0x100000000120000000001000020000a0000100004000010000100004000010000400004000010000a0000100001000030000000002000090000000006000000000000005000000000600006000000000900000000000000300011000020000200010000020000f0000e000020000300002000020000d0000700005000050000c000080000800003000070000b000000000000000)
    | 201 => (5, 0x108180cb80ca406804880d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e100002003421020e702ce70202102c21018e702ce701821025ef0142102c21015ef00ce30102100c21010e40240002042024420200003800018420384201800028420140002800014420444200c000440000c4303196000000000000000025080152503535015050128400d030110400da3015c5028c6014c6029ca0126400cc3010c400da303192000000000000000)
    | 202 | 237 | 250 | 269 => (4, 0xd0a181010a04029304009100902108120c01820112020811420140808810481, 0x10000000f000000010002000e00010009000100010009000600010001000500060001000100060000000300020000000300000000000300030000000000050003000000000003000200040004000200050004000500020002000400080008000d000000000000000c00070007000b0000000a00000000)
    | 204 => (5, 0xd0a108180ce80cd4068048a0910048824402081058a405b218309024029304020c01820142008810481, 0x100000000140000000001000030000300001000010000300003000010000100007000070000100007000010000100007000030000100001000030000000002000020000000000000020000200000000000000c0000c000000000200000000000000200002000000000000002000130000000000000000000600005000050000600005000040001200004000110000500005000090000b0000b0000800006000040000a000040000a000100000800008000090000400006000000000f0000e0000000000000000000d000000000000000)
    | 205 | 253 => (5, 0xd0a181024402081058a21833040182010810910048820c0090214201408112010a008810481, 0x10000000012000000000100004000110000100001000060000600001000060000100001000060000b00001000010000b00000000050000400000000000000300010000000000500000000000000200005000000000000005000030000f0000300004000020000e0000200004000040000d0000a0000a0000300002000070000200009000090000c0000300008000080000700002)
    | 206 | 254 => (5, 0xd0a20811183405b1102058a0910048a1820142004884029244020c0090210a0108108810481, 0x100000000120000000001000020000a00001000010000400004000010000a0000100001000030000400001000010000400000000020000900000000000000600006000000000900000000000000300006000000000000005000020001100010000020000300002000020000f0000e00002000020000d0000c0000000000000000000500007000050000b00008000080000300007)
    | 207 | 255 => (5, 0x108120c040310d180d0a2440403209020890250a1820304010a020811420112040290910048808810481, 0x1021002000121000020010210254a0114a024210102101d4a0114a01c21031ac0082203021009a200c21015ad00dad0142104800024c6048c60240002c0001cc602cc601c00008c20300000800030cc0440000de3045ef00c000109400000000000000002128009c2021c8009220148500d230152500c8302168008e2020e800962014e500d630156500ce300000000000389300000)
    | 208 => (5, 0x208180dc80da80d780d580d11103048811020d184031405b11830d0a182040492840406914204029250a112024400902218310a010810910088104814032, 0x4200621036310044100042019ce035ce0184200c42024e700ce702442000e70144203442014e704c42012040361001042034e702c420344202ce7028210190802908018210542100d030550800c210018c01421000210158500021011840018c0102100108050210002105108001fe0000000000000000014a014c5000c601545000c6010040027d010c40014a02cc6000c602d4a00063014050701b01463048630112404929010630686302d290652902c63011e4000a50000000018001f700000000000000000016000000000000000)
    | 209 => (5, 0xd0a182080d4402980d34031208180d20488140809102840142030401120244020c01102090210a0108108810481, 0x1000000001600000000010000b0000b0000100004000010000100004000010000200015000010000100004000040000100014000010000100013000000000700007000000000a00000000000000300000000020000a0000000000000080000700000000120000000000000110000600003000060000300009000020000900002000100000000000000000000f00000000000000000002000030000200005000030000800006000030000e000000000000000000020000500005000020000d0000000000000000000c000000000000000)
    | 211 => (5, 0x18200d0a208110a008901408091028403040244011021120090220c01081088104880481, 0x20000a0000a000020000500001000020000100002000030001100002000020000500005000020001000000000020000000004000010000400001000090000300009000030000f00000000000000000008000000000800000000010000e000030000100001000060000400001000000000d0000000001000030000700007000030000c0000000003000000000b000000000600000)
    | 212 => (5, 0xd0a208110a01102140814203040284004880902244020c009101081089008810481, 0x600006000000000b00000000000000200000000030000b000000000000004000060000000010000000000000001000050000200005000020000a000030000a000030000f00000000000000000009000010000900001000020000e0000300002000020000400005000020000800008000010000200003000040000d000040000c00001000030000100007000010000700001)
    | 213 => (5, 0xd0a1820240880d61120284014203040048820c0110224400910090210a0108108810481, 0x1000000001100000000010000c0000c0000100004000010000100004000010000200010000010000100004000040000100004000010000100004000000000600006000000000b00000000000000300000000020000b000000000000005000060000000006000000000000006000080000300008000030000a000020000a000020000f00000000000000000000000000000e00000000020000300002000070000300005000080000500009000090000300008000020000500007000050000700002000020000700000000000000d00000)
    | 215 => (5, 0x80d940682408110280d840290d1804880d0a28400902250a405b40691820058a2440142010a0403220c020811081091008810481, 0x1821002200323100020018210120403210010210342100d630316b00c21031ef0142103021015ef0096201c210082101d67038000112403929010000180000d030190800c000292901400028000152504d080080004c00009020188400cc3019b900c83015c50288401484029ca01b17000000000000000018d600000000000000001ea70086201c63009a201e92008b201ca7009a2)
    | 218 => (5, 0xd0a218380db208140681102405b048a0910284018201420058a118304884029090210a0244020c0108108810481, 0x1000000001600000000010000d0000d0000100001000020000c0000100006000010000100006000010000600006000010000c0000100001000050000000004000040000000000000020000b0000000004000000000000003000000000400004000000000b00000000000000500015000020001400002000030000a000030000a00013000000000000000000120000000000000000001100000000000000000002000090000900002000050000200002000100000700003000030000f000080000800005000070000e000000000000000)
    | 220 => (5, 0x80de80dd40490488401b11020d1811830d0a182040294069142024403040250a112010a0090240320910108108810481, 0x1021001e0031ef0002000c2101ca500ca501c21010a50182103021018a5030a50242103021024a503021009c2031ce008210440000d430454a00c000116b0180001000019660114a02400010000254a02000009620216b00800010630188605c960186302463034e7024e70346304063008e2040e700863012b400000000000000000a62020c6008c202088009a2021320092202088)
    | 223 => (6, 0x4051810580f880ef80e980e880e380e01142108120810d1831420d0a0583058a28402440405b20c0401b407109020890403b182010a01420112030403020403240494031406909100881048804814029, 0x1850c300168114569a0010c10040c300b45100445100b0c32104500020c21500c30024421d50c300a38e1c538e00a0c300f0c30095d70055d70090c34c50c300038e14538e0000c301c04118464419c6590040412023021900412020411903101d504118a30c9d230c18a04100f0411895961925960090414d204118630c49230c1860412181040021421589980021021db10400a2cb1db2cb00a10400f1040093c90053e50091044c51040002cb1452cb0001041d508220a34d56434d20a08200f0822095142235140090824e208220834d86034d2080820090091c728a00000000701f00001e0000000000000000001c71dd000000000000000000)
    | 224 => (6, 0x405b80e280e11102405a2408401b04880d18403111830d0a1820284005832440218321c2402930403020142020c0406911200902208110a010810910403208810481, 0x20410005400095550000400030410081c70031c70080410200410045040095140040410020410064c60094d30060410021c70050410090410051c70091c700e04100904100e1c70180000034830184920030000020000042c40022cb0040000020000064460024510060000022cb0050000020000052c50027de0170000020000170820160c30042040162080040c30100c30060860100900060c300f0c300508500f08f0050c30090c300e20800920800e0c300c10400634600c34c00610400534500a10400510400a34a00209d00000000000000000000a30a00518500a18600530500271b000000000000000000002699000000000000000000)
    | 225 => (5, 0x110208901c182c180c9840691183058330402440182028402183058a302020c0403214081420240810a011200902208109101081088104880481, 0x104201cc6010c601c420684200e4306a5200c4206442016250663101442060c60044106042004c105cc60004005c42000c00588400ce3058e700c840408401585041900148403c840058103d8f0048105484000e0054e700080038630168503a8e01463021680046102063005610297c0006002863001600352d004a1034a50052104d29000a004ca500120000200291b0010002821)
    | 226 => (5, 0x18202840218321c230201408240824400488403120c014201120208110a009021081091004810881, 0x400004000000000000003000130000000000000060001200000000040000000000000040000400000000000000400004000010000000001000020000300007000020000200006000110000200002000050001000002000020000700007000020000200001000070000100003000060000f00003000050000300003000090000e00000000000000000008000010000300001000090000500006000050000d0000000000000000000c0000100006000010000b00000000000000000001000050000100008000000000a0000000000)
    | 227 => (5, 0xd0a058380e680e421c23040114210812081405a401b0488284024403020182020c0403214200902112010a0091008810481, 0x10000000018000000000100005000050000100001000090000900001000010000c0000c000010000100009000090000100005000010000100005000050000100001000050000000002000170000000000000060000600000000000000b0000b0000000000000060000600000000060000000000000030001600000000000000700002000040000400002000020000a00015000020000200004000040000200002000030001400002000020000400004000020000a00013000000001200011000000000000000000030000800003000080000700000000000000000010000000000000000000080000300008000030000f000000000000000000030000e0000000007000070000000000000000000d000000000000000)
    | 228 => (5, 0xd0a80e5244010812183250a0488403220c01820142010a009021120091008810481, 0x100000000100000000001000070000700001000010000700007000010000400001000010000400004000010000100004000010000400004000010000000006000060000000000000060000600000000060000000000000050000f00000000000000900000000020000e000000000d000000000000000000050000800005000080000900000000000000000003000020000300002000050000c00000000090000b000000000000000000030000200003000020000a0000000000000000000500002000080000200003000020000300002)
    | 229 => (4, 0x108120c008901820090210a0142011200910088104880481, 0x20008000800020002000800080002000700010002000100020007000700020007000000020000000b00000000000000060001000600010004000300040003000500000005000000060001000600010004000300040003000500000005000000010003000a000100000009000000010003000000040000)
    | 230 => (5, 0x80e7058a304011421081208108902840302020c024401820090210a0142011200910088104880481, 0x200007000070000200002000080000800002000020000c0000c0000200002000080000800002000070000100002000010000700000000020000000003000040000400003000030000b00013000030000300004000040000300003000010001200001000030000000004000000000b0001100000000100000f00000000000000000006000010000600001000050000000005000000000e0000000000000000000a000010000a00001000090000000009000000000600001000060000100005000000000500000000000000d0000000001)
    | 231 => (4, 0x1081089020c01820090210a0142011200910088104880481, 0x20008000800020002000800080002000700010002000100070000000200000002000700070002000b0000000000000006000100060001000500000005000000040003000400030006000100060001000500000005000000040003000400030000000a0000000100010003000900010000000300040000)
    | 232 => (5, 0x1102240810a00d18403111830d0a2840058324402183058a4069401b090208901820402930401420112030200488208109101081403208810481, 0x821002c0042d60002001021021ce011ce0202103c2100d830418c00c2100821016a5042b501421035cd0182603421019c603c2102d8c0418c02c21064000128406694010000080000d230092900c00008000166500a73014000192603400018000352d0080006129009290600005c8400d0305d0800c84048840144504852014840448401846044510188603c8402d080410802c8401c630154501d47014630094a0186603c630194602c630095c0094a00863008e7018a6008a5018e6008a502cfb008e702ca50000000000009fa00000)
    | 233 => (5, 0x80ec108180ea1142401b240804880d1831422183405b40490d0a058321c2402940691820112009023040302020c0208114200910088104814032, 0x4200601032100044100c420292900d2902842048420216b0316b02042030420156b0316b01442001290184203042019290012901c420304201d290542100de3055ef00c210002102084000840202100021014840008401421000840182100021018840008401c210002101c84050630214a0514a0206304c630154a04d4a0146303863018060380e018630006301c070301c01c63035bb00000000000000000108018060481a0190601c070450801d070001901806060a5018a50000001c17044a501ca500000035b6000000000000000)
    | 234 => (5, 0x80eb1103110211420d18118321c24049402904880d0a18200583244014204069112020c0090210a009101081088104814032, 0x42005c1025ce0044101042020c6010c6020420244200da3025ad00c42000c60144202442014c6024c601c420244201cc605021011840518c010210002100d430014a00c210014a0142100021015450016b01c210002101d6704c8400d0304d0800c84000840140502418014840488401d080490801c840140504463014630001701c160406301c630000001e2f040af01ca500015)
    | 236 => (5, 0x108180ee80ed406804880d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e100002003421020e702ce70202102c21018e702ce701821025ef0142102c21015ef00ce30102100c21010e40240002042024420200003800018420384201800028420140002800014420444200c000440000c4303196000000000000000025080152503535015050128400d030110400da3015c5028c6014c6029ca0126400cc3010c400da303192000000000000000)
    | 239 => (5, 0x80f580f2208180f0405a1142401b1103110204880d181183314240490d0a1820058340292840142024404069112030400902302010a010810910088104814032, 0x420062102a310044100c42024e700ce70244200042019ad029ad01842028420120402a1001042000e70144202842014e7028e70204202842020e70542100de3055ef00c21000210196b0016b0182100021011840018c010210018c0142100021015850016b02021000210216b00063018060281f018630506301124051290106300063014050281e0146304c630212904d29020630025d000000000000000000c6014050001c014c502368038c6020c60381a014050648401484000180201703884020840000000256000000000000000)
    | 240 => (5, 0x80f11102110311420d18118321c24029404904880d0a18200583244014204069112020c0090210a009101081088104814032, 0x42005c1025ce0044101042020c6010c6020420244200da3025ad00c42024c601c420244201cc6000c60144202442014c605021011840518c010210002100d430014a00c210016b01c210002101d670014a01421000210154504c8400d0304d0800c840488401d080490801c840008401405024180148401c170446301c6300000014050406301463000160162f040ef014e500015)
    | 242 => (5, 0x40492081405a80f480f311020d18406804880d0a28400902182040691420244010a0058a3020304040321081091008810481, 0x1021001e002def0002001021019ce02dce0182102c2100d8302d8c00c2102dad0142102c21015ad00982020210082102188010000192901129018000100000d430114a00c0001d290140001c00015290494a00800048000094201317000000000000000016c501cc6014c601c87010c600882012b4008c20149301c630146301c8702228008620206300a22020b0008f0020e8008a2)
    | 245 => (5, 0x401b11024049048880f780f60d1811830d0a18204029406914202440250a3040112010a0090240321081091008810481, 0x1021001e0031ef000200302100dc3031ce00c21010a50182103021018a5030a50202103021020a50082101ca5008a501c210240000d630256b00c000116b0180001000019660114a02000010000214a04400009420454a008000192605c6301863011290213603463020630112901c6300a0201e0700862012b4000000000000000010c60088201272008c201da70090201d07009a2)
    | 248 => (5, 0x40518102810080ff80fc80f9108140710d180d0a2440401b20c0250a090208904049405b4069182010a040323040218340311420112009100881048804814029, 0x3b463006c16b6d60046154230008626c06300a227b8630258c7b58c02463a34630218c6b58c0206301063016310123101463508c23c021508213c0d07b8213a4c6fe0c63a421a48213a0c6c48c63a02105c21392a43deb5010217b8425256b7796b52442a20425496bea16b548420704251264dea7301042000190000000000000000140579124715250100401405791047150501004)
    | 249 => (5, 0x108180fb80fa406804880d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e100002003421020e702ce70202102c21018e702ce701821025ef0142102c21015ef00ce30102100c21010e40240002042024420200003800018420384201800028420140002800014420444200c000440000c4303196000000000000000025080152503535015050128400d030110400da3015c5028c6014c6029ca0126400cc3010c400da303192000000000000000)
    | 252 => (5, 0xd0a108180fe80fd4068048a0910048824402081058a405b218309024029304020c01820142008810481, 0x100000000140000000001000030000300001000010000300003000010000100007000070000100007000010000100007000030000100001000030000000002000020000000000000020000200000000000000c0000c000000000200000000000000200002000000000000002000130000000000000000000600005000050000600005000040001200004000110000500005000090000b0000b0000800006000040000a000040000a000100000800008000090000400006000000000f0000e0000000000000000000d000000000000000)
    | 256 => (5, 0xd0a2440810110812183250a048820c040321820142010a009021120091008810481, 0x100000000100000000001000070000700001000010000400004000010000100007000070000100004000010000100004000040000100001000040000000006000060000000000000020000f0000000000000060000600000000060000000000000050000e000000000000008000030000200003000020000d0000000000000000000500009000050000900008000000000000000000020000300003000020000200005000090000200002000030000300002000050000c00000000080000b0000000000000000000a000000000000000)
    | 257 => (4, 0x108120c008901820090210a0142011200910088104880481, 0x200080008000200020007000700020002000800080002000700010002000100070000000200000004000300040003000b00000000000000060001000600010005000000050000000300040004000300030001000a00010003000000040000000600010006000100050000000500000000000900000001)
    | 258 => (5, 0x401b110281048103404904880d1811830d0a18204029406914202440250a3040112010a0090240321081091008810481, 0x1021001e0031ef000200302100dc3031ce00c210082101ca5008a501c21010a50182103021018a5030a50202103021020a50240000d630256b00c0004400009420454a008000116b0180001000019660114a02000010000214a01c6300a0201e07008620192605c630186301129021360346302063011290104201886054940184202042034e7020e70344201272000000000000000)
    | 261 => (5, 0x1142108181112081810f810c810a8106048840310d18405b3142404940680d0a2840090224404069402921c21820112030403020058a14200910088140320481, 0x4420020003210000400504201d290312901c4200442019ef031ef018420304202d290312902c42005ce0144203042015ce00d230204200c42021280040001c840048401c0000400019ad005ad0180000400058840048405800014840280001400028840548400c000540000c8301966048e7000000057f02d7e000000000000000004e7014250503d014e7020e800e630226800ce30065c000000000000000028c6014250282a014c6004c600c230077a00cc30282a014250282a014250222800f230230800e2302d77000000000000000)
    | 262 => (5, 0xd0a28408109406824408108403230401408240810a0810709100902182011021420302011202081108108810481, 0x10000000016000000000100002000080000100001000030001500001000090000100001000090000800001000010000400014000010000100013000000000200006000000000000003000120000000006000000000000006000060000000000000040001100000000000001000002000030000500002000070000200002000070000400002000020000f0000e00000000000000000005000030000300005000050000400003000040000d0000000000000000000c0000000000000000000b0000000000000000000a000000000000000)
    | 264 => (4, 0x28400d0a30200488091009021820110214081420112024082081108108810481, 0x100020009000100010003000f0001000a00010001000a0009000100010005000e00000001000000020003000d0002000800020002000800050002000200070007000000020000000400030003000400040005000300050004000000030000000c00000000000000000006000000060000000b00000006)
    | 265 => (4, 0x24400d0a30201408240808901102090211202810142020810910108108810481, 0x20005000000000004000f000000050000000000050005000000000003000e00000000000100020004000d000200090002000200090007000300020003000c00010002000100060004000400060006000300040003000b000100040001000a00000000000000010008000100080001000700010003)
    | 266 => (5, 0xd0a28402440140824080488810b112009021102304018203020142009102081108108810481, 0x100000000120000000001000020000700001000010000300011000010000a00001000010000a00004000010000100007000010000700007000010000000002000050000000000000030001000000000050000000000000050000500000000000000400000000050000500000000020000300006000020000900002000020000900008000040000200004000020000f00008000020000600003000030000600006000040000300004000030000e00006000030000d00000000000000000000000000000c0000000000000000000b00000)
    | 268 => (5, 0x1081810e810d406804880d180d0a0902250a405b40294069058a403230401820208120c011200910142008810481, 0x24210020002e100002003421020e702ce70202102c21018e702ce701821025ef0142102c21015ef00ce30102100c21010e40240002042024420200003800018420384201800028420140002800014420444200c000440000c4303196000000000000000025080152503535015050128400d030110400da3015c5028c6014c6029ca0126400cc3010c400da303192000000000000000)
    | 271 => (5, 0xd0a10818110405b21c2240a240820c040290910090231423020058a4068304020811820142008810481, 0x100000000140000000001000030000300001000010000300003000010000a00001000010000a0000300001000010000300003000010000100003000000000200002000000000000002000020000000002000000000000002000020000000000000020000200000000000000200013000000000000000000050000700012000050000500009000090000500008000050000800011000100000400004000070000600004000040000f0000e0000400004000060000d0000000000000000000c0000000000000000000b000000000000000)
    | 273 => (5, 0x4049208181138112405a11020d18406804880d0a28400902182040691420244010a0058a3020304010814032091008810481, 0xc21001e002def0002000c21019ce02dce0182102c210118402d8c010210098202021008210218802dad0142102c21015ad00c000192900d290180000c000114400d4a010000494a00800048000094201d290140001c000152900f1700000000000000000cc60086200ed5008c20168501cc6014c601c6702228008820208400a220147301c840148401c6701c500151001d0801442)
    | _ => (5, 0x40321102402940680d180488405b0d0a24400902250a40691820058a142020c010a01081091008810481, 0x5021001a0025ad000200256b01421024210156b0242100d030250800c210090201021008210110401d8c0140001c00015850280000cc3028c600c00040c60080004000008c200ce3028b300ca3028e70124f008af010a4009c2012240086201063009c2)
  (data.2.1 >>> (16 * ((data.2.2 >>> (data.1 * slot)) &&& ((1 <<< data.1) - 1)))) &&& 65535



def prior123 : List (Nat × Nat) := [(122, 7), (105, 7), (104, 4), (50, 4), (112, 4), (73, 4), (91, 7), (113, 7), (90, 4), (81, 4), (41, 4), (49, 4), (27, 4), (59, 7)]

theorem prepared123 : prepared 123 prior123 := by

  intro e h

  simp only [prior123,List.mem_cons,List.not_mem_nil,or_false] at h

  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact zeroSlice_sound (by decide +kernel) bound122

  · exact zeroSlice_sound (by decide +kernel) bound105

  · exact zeroSlice_sound (by decide +kernel) bound104

  · exact zeroSlice_sound (by decide +kernel) bound50

  · exact zeroSlice_sound (by decide +kernel) bound112

  · exact zeroSlice_sound (by decide +kernel) bound73

  · exact zeroSlice_sound (by decide +kernel) bound91

  · exact zeroSlice_sound (by decide +kernel) bound113

  · exact zeroSlice_sound (by decide +kernel) bound90

  · exact zeroSlice_sound (by decide +kernel) bound81

  · exact zeroSlice_sound (by decide +kernel) bound41

  · exact zeroSlice_sound (by decide +kernel) bound49

  · exact zeroSlice_sound (by decide +kernel) bound27

  · exact zeroSlice_sound (by decide +kernel) bound59

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123slot5 : Impossible true (graphGoal 123) 8 (orbitState 123 1 0 1 false true).toFinset :=
  checkPlan_sound (program := certCode123) prepared123 8 1 [orbitChoice 123 1 0 1] (orbitState 123 1 0 1 false true) (by decide +kernel)

def orbit123map0 := ([96] : List Nat).map swapRows

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123map0Onto : orbitOnto orbit123map0 orbit123map0.reverse = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123map0Goal : movedWord orbit123map0 (graphGoal 123) = graphGoal 123 := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123slot182 : Impossible true (graphGoal 123) 8 (orbitState 123 5 1 1 true false).toFinset :=
  orbit_transfer orbit123map0Onto orbit123map0Goal (by decide +kernel) orbit123slot5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123slot103 : Impossible true (graphGoal 123) 8 (orbitState 123 4 0 1 true true).toFinset :=
  checkPlan_sound (program := certCode123) prepared123 8 70 [orbitChoice 123 4 0 1] (orbitState 123 4 0 1 true true) (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123slot231 : Impossible true (graphGoal 123) 8 (orbitState 123 5 4 1 true true).toFinset :=
  orbit_transfer orbit123map0Onto orbit123map0Goal (by decide +kernel) orbit123slot103

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem orbit123slot167 : Impossible true (graphGoal 123) 8 (orbitState 123 5 0 1 true true).toFinset :=
  checkPlan_sound (program := certCode123) prepared123 8 123 [orbitChoice 123 5 0 1] (orbitState 123 5 0 1 true true) (by decide +kernel)

def saved123 : List (List Sig) := [orbitState 123 1 0 1 false true, orbitState 123 5 1 1 true false, orbitState 123 4 0 1 true true, orbitState 123 5 4 1 true true, orbitState 123 5 0 1 true true]

theorem saved123_sound : ∀ w ∈ saved123, Impossible true (graphGoal 123) 8 w.toFinset := by

  intro w hw

  simp only [saved123, List.mem_cons, List.not_mem_nil, or_false] at hw

  rcases hw with rfl | rfl | rfl | rfl | rfl

  · exact orbit123slot5

  · exact orbit123slot182

  · exact orbit123slot103

  · exact orbit123slot231

  · exact orbit123slot167

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded123 : Impossible true (graphGoal 123) 9 (vars 123).toFinset :=
  orbitRoot_sound (program := certCode123) prepared123 saved123_sound (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound123 : Lower true (vars 123) (graphGoal 123) 10 :=
  plain_low (hints:=67) (by decide +kernel) excluded123

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound124 : Lower true (vars 124) (graphGoal 124) 7 :=
  carry_of (old := 124) (rep := 59) (swaps := [33, 80, 96, 16]) (by decide +kernel) bound59

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound93 : Lower true (vars 93) (graphGoal 93) 7 :=
  carry_of (old := 93) (rep := 59) (swaps := [33, 101]) (by decide +kernel) bound59

def certCode127 (node slot : Nat) : Nat :=
  (0x403d405b304028402440182040710e180d182342302028102408218320c018101408128510a00d0a068505831324068c058a0a042240112014202204110209020890407b405d403b407c407a208110810a10091040690881048804814076 >>> (16 * ((0x32c2082c790736c9242c720712b2082c38c312b8e32c320302a2082c1881a2a8a20012012542082c64462d44512462062842082c5845b8d8612852050204602c22023602080024421291c73037c31297df3031c30121c7301781a1279e0011c12441c7306746b4d75d2461c62931c73054053134102851c501c41c3021c235c1c70024020040c31016c11046db0010c12460c31145551065552540c32850c31133cf1053cf2930c300e3ce1020c210e0c30023c226704100668612769a0060412a604100564512665900504100248200e04100204100e48e298186245945118958245185017186242102257357002182016145282102296356002142 >>> (6 * slot)) &&& 63))) &&& 65535


def prior127 : List (Nat × Nat) := [(118, 7), (123, 10), (124, 7), (105, 7), (122, 7), (93, 7), (91, 7), (113, 7), (59, 7), (61, 7)]

theorem prepared127 : prepared 127 prior127 := by

  intro e h

  simp only [prior127,List.mem_cons,List.not_mem_nil,or_false] at h

  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact zeroSlice_sound (by decide +kernel) bound118

  · exact zeroSlice_sound (by decide +kernel) bound123

  · exact zeroSlice_sound (by decide +kernel) bound124

  · exact zeroSlice_sound (by decide +kernel) bound105

  · exact zeroSlice_sound (by decide +kernel) bound122

  · exact zeroSlice_sound (by decide +kernel) bound93

  · exact zeroSlice_sound (by decide +kernel) bound91

  · exact zeroSlice_sound (by decide +kernel) bound113

  · exact zeroSlice_sound (by decide +kernel) bound59

  · exact zeroSlice_sound (by decide +kernel) bound61

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem excluded127 : Impossible true (graphGoal 127) 10 (vars 127).toFinset :=
  checkPlan_sound (program := certCode127) prepared127 10 0 [] (vars 127) (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem bound127 : Lower true (vars 127) (graphGoal 127) 11 :=
  plain_low (hints:=1091) (by decide +kernel) excluded127

end PEqualNP.Outside.L_meta_10628

open PEqualNP.Outside.L_meta_10628 in
theorem PEqualNP.Outside.L_meta_10628 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _oneNot correct
  exact replaceShort (by simpa only [sevenInputs, show graph = graphGoal 127 by decide +kernel] using excluded127) gates o fit correct
