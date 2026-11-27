import PEqualNP.Defs

namespace PEqualNP.Outside.V_meta_9980__k13
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 128
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

def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) := by
      cases ho : opOK u c.1
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ ho hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 10000 then (match t.cuts[i]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif Nat.blt i 20000 then (match t.seps[i-10000]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif Nat.blt i 30000 then (match t.kws[i-20000]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[i-30000]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) st.2
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : Nat.blt i 10000
      · rw [h1,cond_false] at hi
        cases h2 : Nat.blt i 20000
        · rw [h2,cond_false] at hi
          cases h3 : Nat.blt i 30000
          · rw [h3,cond_false] at hi
            cases hg : t.perms[i-30000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[i-20000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[i-10000]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def sw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def sw1 : Nat := 0xcccccccccccccccccccccccccccccccc
def sw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def sw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def sw4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def sw5 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def sw6 : Nat := 0xffccffccffccffccffccffccffccffcc
def sw7 : Nat := 0xfefefefefefefefefefefefefefefefe
def sw8 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def sw9 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def sw10 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def sw11 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def sw12 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def sw13 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def sw14 : Nat := 0xffffccccffffccccffffccccffffcccc
def sw15 : Nat := 0xeeee0000eeee0000eeee0000eeee
def sw16 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def sw17 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def sw18 : Nat := 0xfffffafafffffafafffffafafffffafa
def sw19 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfc
def sw20 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def sw21 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeee
def sw22 : Nat := 0xfffefffefffefffefffefffefffefffe
def sw23 : Nat := 0xfefe0000fefe0000fefe0000fefe
def sw24 : Nat := 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8
def sw25 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def sw26 : Nat := 0xa0000000a0000000a0000000a
def sw27 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def sw28 : Nat := 0x88888888888888888888888888888888
def sw29 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def sw30 : Nat := 0xaaaafefeaaaafefeaaaafefeaaaafefe
def sw31 : Nat := 0xf000f000f000f000f000f000f000f000
def sw32 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def sw33 : Nat := 0xee000000ee000000ee000000ee
def sw34 : Nat := 0xfffafffafffafffafffafffafffafffa
def sw35 : Nat := 0xffffffaaffffffaaffffffaaffffffaa
def sw36 : Nat := 0xfafafafafafafafafafafafafafafafa
def sw37 : Nat := 0xfffffffcfffffffcfffffffcfffffffc
def sw38 : Nat := 0xffffffccffffffccffffffccffffffcc
def sw39 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def sw40 : Nat := 0xfffe0000fffe0000fffe0000fffe
def sw41 : Nat := 0xfffffe00fffffe00fffffe00fffffe00
def sw42 : Nat := 0x2aaaa0002aaaa0002aaaa0002aaaa
def sw43 : Nat := 0xfffffefefffffefefffffefefffffefe
def sw44 : Nat := 0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8
def sw45 : Nat := 0xfffffffefffffffefffffffefffffffe
def sw46 : Nat := 0xaaaafffeaaaafffeaaaafffeaaaafffe
def sw47 : Nat := 0xfe000000fe000000fe000000fe
def sw48 : Nat := 0xfffc0000fffc0000fffc0000fffc
def sw49 : Nat := 0xffff000affff000affff000affff000a
def sw50 : Nat := 0x55555550555555505555555055555550
def sw51 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def sw52 : Nat := 0xfffefefefffefefefffefefefffefefe
def sw53 : Nat := 0xfefefe00fefefe00fefefe00fefefe
def sw54 : Nat := 0xff000000ff000000ff000000ff000000
def sw55 : Nat := 0xffff00aaffff00aaffff00aaffff00aa
def sw56 : Nat := 0xfefefffefefefffefefefffefefefffe
def sw57 : Nat := 0xaaa8fffcaaa8fffcaaa8fffcaaa8fffc
def sw58 : Nat := 0xffff00eeffff00eeffff00eeffff00ee
def sw59 : Nat := 0xaafeaafeaafeaafeaafeaafeaafeaafe
def sw60 : Nat := 0xeeeefffeeeeefffeeeeefffeeeeefffe
def sw61 : Nat := 0xaafe0000aafe0000aafe0000aafe
def sw62 : Nat := 0x8888fff88888fff88888fff88888fff8
def sw63 : Nat := 0xfcccfcccfcccfcccfcccfcccfcccfccc
def sw64 : Nat := 0xfffff000fffff000fffff000fffff000
def sw65 : Nat := 0xfff00000fff00000fff00000fff0
def sw66 : Nat := 0xaafcfe00aafcfe00aafcfe00aafcfe
def sw67 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def sw68 : Nat := 0xffffffeeffffffeeffffffeeffffffee
def sw69 : Nat := 0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2
def sw70 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def sw71 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafa
def sw72 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def sw73 : Nat := 0xfffffffafffffffafffffffafffffffa
def sw74 : Nat := 0xffffee00ffffee00ffffee00ffffee
def sw75 : Nat := 0xffa00000ffa00000ffa00000ffa
def sw76 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def sw77 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def sw78 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def sw79 : Nat := 0x3fffc0003fffc0003fffc0003fffc
def sw80 : Nat := 0xfffeff00fffeff00fffeff00fffeff00
def sw81 : Nat := 0xff00fe00ff00fe00ff00fe00ff00fe00
def sw82 : Nat := 0xaaaafffcaaaafffcaaaafffcaaaafffc
def sw83 : Nat := 0x99989998999899989998999899989998
def sw84 : Nat := 0xffccccccffccccccffccccccffcccccc
def sw85 : Nat := 0xffe00000ffe00000ffe00000ffe
def sw86 : Nat := 0xffffffff00000000ffffffff00000000
def s1_T : Nat := 0x88888888888888888888888888888888
def s1_R : List Nat := [0, 1]
def s1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem s1_B : baseOK s1_T s1_R s1_E = true := by decide +kernel
theorem s1_L : LowN true s1_R s1_T 1 := lowCount s1_B (by decide +kernel)
def s2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def s2_R : List Nat := [0, 1]
def s2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem s2_B : baseOK s2_T s2_R s2_E = true := by decide +kernel
theorem s2_L : LowN true s2_R s2_T 1 := lowCount s2_B (by decide +kernel)
def s3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def s3_R : List Nat := [0, 1, 2]
def s3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem s3_B : baseOK s3_T s3_R s3_E = true := by decide +kernel
theorem s3_S0 : SliceN true s3_R s3_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S1 : SliceN true s3_R s3_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S2 : SliceN true s3_R s3_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S3 : SliceN true s3_R s3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S4 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S5 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) s3_B s2_B s2_L (by decide +kernel)
def s3_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem s3_Y : ∀ s ∈ s3_Z, SliceN true s3_R s3_T s := by
  unfold s3_Z
  simp only [List.forall_mem_cons]
  exact ⟨s3_S0,s3_S1,s3_S2,s3_S3,s3_S4,s3_S5,by simp⟩
def s3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def s3_t : Tabs := (s3_C.map (mkCut true s3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem s3_W : TabsP true s3_R s3_T s3_t := ⟨cutsGood s3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s3_D3 : List StD := [
([sw0,sw1,sw2],[[0,1,10000,2,3,10001,10002],[4,1,10003,10000,3],[10001,0,5,2,10004,10005]])]
def s3_D2 : List StD := []
theorem s3_I2 : LevelN true s3_T 2 s3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s3_C3x0 : levelOK true s3_T s3_t 2 (s3_D2.map Prod.fst) ((s3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s3_I3 : LevelN true s3_T 3 s3_D3 := levelStep s3_B s3_W s3_I2 (chunks 16 s3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s3_C3x0
  ))
theorem s3_L : LowN true s3_R s3_T 4 := lowSearch s3_B s3_I3 (by decide +kernel)
def s4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def s4_R : List Nat := [0, 1, 2]
def s4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem s4_B : baseOK s4_T s4_R s4_E = true := by decide +kernel
theorem s4_L : LowN true s4_R s4_T 2 := lowCount s4_B (by decide +kernel)
def s5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def s5_R : List Nat := [0, 1, 2, 3]
def s5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem s5_B : baseOK s5_T s5_R s5_E = true := by decide +kernel
theorem s5_S0 : SliceN true s5_R s5_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S1 : SliceN true s5_R s5_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S2 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S3 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S4 : SliceN true s5_R s5_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) s5_B s1_B s1_L (by decide +kernel)
theorem s5_S5 : SliceN true s5_R s5_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S6 : SliceN true s5_R s5_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S7 : SliceN true s5_R s5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S8 : SliceN true s5_R s5_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S9 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S10 : SliceN true s5_R s5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S11 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S12 : SliceN true s5_R s5_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S13 : SliceN true s5_R s5_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) s5_B s2_B s2_L (by decide +kernel)
def s5_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x11111111111111111111111111111111,1,[2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0x50505050505050505050505050505050,1,[1, 3])]
theorem s5_Y : ∀ s ∈ s5_Z, SliceN true s5_R s5_T s := by
  unfold s5_Z
  simp only [List.forall_mem_cons]
  exact ⟨s5_S0,s5_S1,s5_S2,s5_S3,s5_S4,s5_S5,s5_S6,s5_S7,s5_S8,s5_S9,s5_S10,s5_S11,s5_S12,s5_S13,by simp⟩
def s5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[]),(1,[(3,0,2)]),(6,[]),(0,[(3,0,2)]),(2,[(1,1,2)]),(2,[(1,0,2)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(1,[(3,0,1)]),(7,[]),(0,[(3,0,1)]),(8,[]),(0,[(2,0,1)]),(9,[]),(10,[]),(0,[(2,0,2)]),(11,[]),(12,[]),(0,[(1,0,2),(1,1,2)]),(8,[(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(1,0,3)]),(3,[(3,1,2)]),(0,[(0,0,2)]),(0,[(2,1,2)]),(0,[(0,1,2)]),(13,[])]
def s5_t : Tabs := (s5_C.map (mkCut true s5_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem s5_W : TabsP true s5_R s5_T s5_t := ⟨cutsGood s5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s5_D6 : List StD := [
([sw0,sw1,sw2,sw3],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[1,10002,30003,10006,10007,2],[1,10002,30004,10008,10009,3],[2,10003,30005,10010,10011,3]])]
noncomputable def s5_D5 : List StD := [
([sw0,sw1,sw4,sw2,sw3],[[0,1],[1],[0,30006,10003,4],[0,30007,10005,5],[0],[1,30008,10007,4],[1,30009,10009,5],[4,6,2,30000,10003,30010,10010],[5,6,3,30010,10005,30000,10011],[10003,4,10010,10011]])]
noncomputable def s5_D4 : List StD := [
([sw0,sw1,sw2,sw5,sw6],[[7,30011,8],[7,9],[10],[7,8,9],[8,11],[8,7,11],[12],[13,9,10007],[14,11,10003],[7,8]]),
([sw0,sw1,sw2,sw7,sw3],[[15,4,16],[15,16,4],[17],[15,18],[4,15,16],[19],[16,20],[21],[4,22],[3,18,30000]]),
([sw8,sw0,sw1,sw2,sw3],[[0,1],[1,0],[2,23,6],[7],[24,23],[6,23],[6,25,5],[6,26],[23,25],[23,25]])]
noncomputable def s5_D3 : List StD := [
([sw0,sw9,sw6,sw10],[[27,28,10012],[29,28,10000],[30,10000,10001],[3,31,32],[3,28,1],[1,28]]),
([sw11,sw0,sw1,sw2],[[0,18],[24,20,33],[34,6,35],[36,18],[11,18],[9,20]])]
def s5_D2 : List StD := []
theorem s5_I2 : LevelN true s5_T 2 s5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C3x0 : levelOK true s5_T s5_t 2 (s5_D2.map Prod.fst) ((s5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I3 : LevelN true s5_T 3 s5_D3 := levelStep s5_B s5_W s5_I2 (chunks 16 s5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C4x0 : levelOK true s5_T s5_t 3 (s5_D3.map Prod.fst) ((s5_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I4 : LevelN true s5_T 4 s5_D4 := levelStep s5_B s5_W s5_I3 (chunks 16 s5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C5x0 : levelOK true s5_T s5_t 4 (s5_D4.map Prod.fst) ((s5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I5 : LevelN true s5_T 5 s5_D5 := levelStep s5_B s5_W s5_I4 (chunks 16 s5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C6x0 : levelOK true s5_T s5_t 5 (s5_D5.map Prod.fst) ((s5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I6 : LevelN true s5_T 6 s5_D6 := levelStep s5_B s5_W s5_I5 (chunks 16 s5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C6x0
  ))
theorem s5_L : LowN true s5_R s5_T 7 := lowSearch s5_B s5_I6 (by decide +kernel)
def s6_T : Nat := 0xfffefffefffefffefffefffefffefffe
def s6_R : List Nat := [0, 1, 2, 3]
def s6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem s6_B : baseOK s6_T s6_R s6_E = true := by decide +kernel
theorem s6_L : LowN true s6_R s6_T 3 := lowCount s6_B (by decide +kernel)
def s7_T : Nat := 0xfffefee8fffefee8fffefee8fffefee8
def s7_R : List Nat := [0, 1, 2, 3, 4]
def s7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem s7_B : baseOK s7_T s7_R s7_E = true := by decide +kernel
theorem s7_S0 : SliceN true s7_R s7_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S1 : SliceN true s7_R s7_T (0x33333333333333333333333333333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S2 : SliceN true s7_R s7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S3 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S4 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S5 : SliceN true s7_R s7_T (0x11111111111111111111111111111111,4,[2, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S6 : SliceN true s7_R s7_T (0x3333000033330000333300003333,4,[0, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S7 : SliceN true s7_R s7_T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S8 : SliceN true s7_R s7_T (0x3030303030303030303030303030303,4,[0, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S9 : SliceN true s7_R s7_T (0x5050505050505050505050505050505,4,[1, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S10 : SliceN true s7_R s7_T (0x1010101010101010101010101010101,1,[3, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S11 : SliceN true s7_R s7_T (0xf000f000f000f000f000f000f000f,4,[0, 1, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S12 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S13 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff,4,[0, 1, 2]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S14 : SliceN true s7_R s7_T (0x550055005500550055005500550055,4,[1, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S15 : SliceN true s7_R s7_T (0x33003300330033003300330033003300,2,[0, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S16 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]) := mkSlice (w:=16) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S17 : SliceN true s7_R s7_T (0x11110000111100001111000011110000,1,[2, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S18 : SliceN true s7_R s7_T (0x10101010101010101010101010101010,1,[3, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S19 : SliceN true s7_R s7_T (0x11001100110011001100110011001100,1,[2, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S20 : SliceN true s7_R s7_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S21 : SliceN true s7_R s7_T (0x2222000022220000222200002222,1,[2, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S22 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff0000,2,[0, 1, 2]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S23 : SliceN true s7_R s7_T (0x2020202020202020202020202020202,1,[3, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S24 : SliceN true s7_R s7_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S25 : SliceN true s7_R s7_T (0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]) := mkSlice (w:=2) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S26 : SliceN true s7_R s7_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S27 : SliceN true s7_R s7_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S28 : SliceN true s7_R s7_T (0xa0a00000a0a00000a0a00000a0a,1,[1, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S29 : SliceN true s7_R s7_T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S30 : SliceN true s7_R s7_T (0x330033003300330033003300330033,4,[0, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S31 : SliceN true s7_R s7_T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S32 : SliceN true s7_R s7_T (0x44444444444444444444444444444444,2,[2, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S33 : SliceN true s7_R s7_T (0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S34 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S35 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]) := mkSlice (w:=8) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S36 : SliceN true s7_R s7_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S37 : SliceN true s7_R s7_T (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S38 : SliceN true s7_R s7_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S39 : SliceN true s7_R s7_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S40 : SliceN true s7_R s7_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S41 : SliceN true s7_R s7_T (0xaa000000aa000000aa000000aa,1,[1, 2]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S42 : SliceN true s7_R s7_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S43 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S44 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S45 : SliceN true s7_R s7_T (0x440044004400440044004400440044,1,[2, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S46 : SliceN true s7_R s7_T (0x3030000030300000303000003030000,1,[0, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S47 : SliceN true s7_R s7_T (0x500050005000500050005000500050,1,[1, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S48 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S49 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S50 : SliceN true s7_R s7_T (0x300030003000300030003000300030,1,[0, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S51 : SliceN true s7_R s7_T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S52 : SliceN true s7_R s7_T (0x5000500050005000500050005000500,1,[1, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S53 : SliceN true s7_R s7_T (0x4040404040404040404040404040404,1,[3, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S54 : SliceN true s7_R s7_T (0xa000a000a000a000a000a000a000a,1,[1, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S55 : SliceN true s7_R s7_T (0x3300000033000000330000003300,1,[0, 2]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S56 : SliceN true s7_R s7_T (0x550000005500000055000000550000,1,[1, 2]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S57 : SliceN true s7_R s7_T (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S58 : SliceN true s7_R s7_T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S59 : SliceN true s7_R s7_T (0x5050000050500000505000005050000,1,[1, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S60 : SliceN true s7_R s7_T (0x50005000500050005000500050005,1,[1, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S61 : SliceN true s7_R s7_T (0x110011001100110011001100110011,1,[2, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S62 : SliceN true s7_R s7_T (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S63 : SliceN true s7_R s7_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
def s7_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,7,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]),(0x11111111111111111111111111111111,4,[2, 3, 4]),(0x3333000033330000333300003333,4,[0, 2, 3]),(0x5555000055550000555500005555,4,[1, 2, 3]),(0x3030303030303030303030303030303,4,[0, 3, 4]),(0x5050505050505050505050505050505,4,[1, 3, 4]),(0x1010101010101010101010101010101,1,[3, 4]),(0xf000f000f000f000f000f000f000f,4,[0, 1, 4]),(0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]),(0xff000000ff000000ff000000ff,4,[0, 1, 2]),(0x550055005500550055005500550055,4,[1, 2, 4]),(0x33003300330033003300330033003300,2,[0, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]),(0x11110000111100001111000011110000,1,[2, 3]),(0x10101010101010101010101010101010,1,[3, 4]),(0x11001100110011001100110011001100,1,[2, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x2222000022220000222200002222,1,[2, 3]),(0xff000000ff000000ff000000ff0000,2,[0, 1, 2]),(0x2020202020202020202020202020202,1,[3, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0xa0a00000a0a00000a0a00000a0a,1,[1, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0x330033003300330033003300330033,4,[0, 2, 4]),(0x30003000300030003000300030003,1,[0, 4]),(0x44444444444444444444444444444444,2,[2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]),(0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0xaa000000aa000000aa000000aa,1,[1, 2]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]),(0xf0000000f0000000f0000000f0000,1,[0, 1]),(0x440044004400440044004400440044,1,[2, 4]),(0x3030000030300000303000003030000,1,[0, 3]),(0x500050005000500050005000500050,1,[1, 4]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0x300030003000300030003000300030,1,[0, 4]),(0x220022002200220022002200220022,1,[2, 4]),(0x5000500050005000500050005000500,1,[1, 4]),(0x4040404040404040404040404040404,1,[3, 4]),(0xa000a000a000a000a000a000a000a,1,[1, 4]),(0x3300000033000000330000003300,1,[0, 2]),(0x550000005500000055000000550000,1,[1, 2]),(0x5050000050500000505000005050,1,[1, 3]),(0x3030000030300000303000003030,1,[0, 3]),(0x5050000050500000505000005050000,1,[1, 3]),(0x50005000500050005000500050005,1,[1, 4]),(0x110011001100110011001100110011,1,[2, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(0xc000c000c000c000c000c000c000c,1,[0, 4])]
theorem s7_Y : ∀ s ∈ s7_Z, SliceN true s7_R s7_T s := by
  unfold s7_Z
  simp only [List.forall_mem_cons]
  exact ⟨s7_S0,s7_S1,s7_S2,s7_S3,s7_S4,s7_S5,s7_S6,s7_S7,s7_S8,s7_S9,s7_S10,s7_S11,s7_S12,s7_S13,s7_S14,s7_S15,s7_S16,s7_S17,s7_S18,s7_S19,s7_S20,s7_S21,s7_S22,s7_S23,s7_S24,s7_S25,s7_S26,s7_S27,s7_S28,s7_S29,s7_S30,s7_S31,s7_S32,s7_S33,s7_S34,s7_S35,s7_S36,s7_S37,s7_S38,s7_S39,s7_S40,s7_S41,s7_S42,s7_S43,s7_S44,s7_S45,s7_S46,s7_S47,s7_S48,s7_S49,s7_S50,s7_S51,s7_S52,s7_S53,s7_S54,s7_S55,s7_S56,s7_S57,s7_S58,s7_S59,s7_S60,s7_S61,s7_S62,s7_S63,by simp⟩
def s7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[]),(0,[(1,0,3)]),(1,[(1,0,3)]),(2,[(1,0,3),(1,1,3)]),(3,[(1,0,3),(1,1,3)]),(6,[]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(8,[]),(3,[(1,0,1),(1,2,4)]),(4,[(1,0,1),(1,2,4)]),(9,[]),(10,[]),(0,[(2,0,3)]),(4,[(3,0,1)]),(1,[(2,0,3)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(11,[(1,0,1)]),(5,[(1,0,1)]),(11,[]),(4,[(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(12,[]),(13,[]),(0,[(1,0,3),(1,2,3)]),(1,[(1,0,2),(1,2,3)]),(2,[(1,0,2),(1,1,3),(1,2,3)]),(3,[(1,1,3)]),(6,[(1,0,2)]),(14,[(1,0,2)]),(15,[]),(14,[]),(1,[(1,2,3),(1,0,4)]),(16,[]),(0,[(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(3,[(1,0,1),(1,2,3)]),(17,[]),(5,[(1,1,2)]),(5,[(1,0,2)]),(0,[(1,2,3),(3,1,3)]),(18,[]),(19,[]),(0,[(1,1,3),(3,2,3)]),(0,[(1,0,3),(1,1,3)]),(1,[(1,0,3),(1,1,4)]),(4,[(1,0,2)]),(20,[]),(4,[(3,0,2)]),(0,[(1,0,3),(1,1,4)]),(0,[(1,1,3),(1,0,4)]),(21,[]),(1,[(1,0,3),(1,1,3)]),(9,[(1,0,2)]),(22,[]),(23,[]),(4,[(1,1,2)]),(11,[(1,1,2)]),(0,[(1,0,1),(2,0,3)]),(4,[(1,1,2),(1,0,4)]),(2,[(0,1,3)]),(0,[(1,0,1),(1,0,3)]),(12,[(1,0,1)]),(8,[(2,0,2)]),(4,[(1,0,1),(1,1,2)]),(24,[]),(0,[(1,0,1),(1,0,2)]),(2,[(1,0,1),(1,2,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,2),(3,0,1)]),(1,[(1,0,1),(3,0,2)]),(0,[(1,0,2),(3,0,1)]),(0,[(1,0,1),(3,0,2)]),(25,[]),(0,[(1,0,2),(2,0,1)]),(0,[(1,0,1),(2,0,2)]),(2,[(1,0,1),(1,3,4)]),(26,[]),(1,[(1,1,3),(3,0,3)]),(27,[]),(0,[(1,1,3),(3,0,3)]),(0,[(1,0,3),(3,1,3)]),(3,[(1,0,1),(1,3,4)]),(28,[]),(8,[(1,0,1)]),(1,[(1,0,1),(1,2,4)]),(9,[(1,0,1)]),(3,[(1,0,1),(3,2,4)]),(5,[(2,0,1)]),(5,[(2,0,2)]),(1,[(1,0,1),(3,3,4)]),(2,[(1,0,1),(3,3,4)]),(9,[(2,0,2)]),(29,[]),(2,[(1,1,2),(2,0,4)]),(2,[(1,1,2),(0,0,1)]),(2,[(1,1,2),(3,0,1)]),(30,[]),(1,[(1,1,2),(0,0,4)]),(2,[(1,1,2),(0,0,4)]),(3,[(1,1,2),(0,0,4)]),(31,[]),(9,[(3,0,1)]),(32,[]),(5,[(3,0,1)]),(9,[(2,0,1)]),(0,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(3,2,4)]),(33,[]),(3,[(1,0,2),(1,1,4)]),(2,[(1,0,2),(1,1,4)]),(0,[(1,0,2),(1,1,4)]),(0,[(1,1,2),(1,0,4)]),(0,[(1,0,1),(1,3,4)]),(0,[(1,0,1),(3,3,4)]),(4,[(1,0,2),(1,1,4)]),(34,[]),(4,[(1,2,3),(0,0,4)]),(9,[(1,1,2)]),(2,[(1,2,3),(2,0,4)]),(3,[(1,2,3),(2,0,4)]),(35,[]),(4,[(1,2,3),(2,0,4)]),(13,[(2,0,2)]),(9,[(3,1,2)]),(9,[(2,1,2)]),(4,[(1,2,3),(2,0,1)]),(4,[(1,2,3),(3,0,1)]),(2,[(1,2,3)]),(3,[(1,2,3)]),(2,[(0,0,1),(1,2,3)]),(36,[]),(3,[(0,0,1),(1,2,3)]),(37,[]),(4,[(0,0,1),(1,2,3)]),(38,[]),(39,[]),(40,[]),(3,[(0,0,1),(3,2,3)]),(4,[(0,0,1),(2,2,3)]),(3,[(0,0,1),(2,2,3)]),(3,[(1,0,1),(3,2,3)]),(2,[(1,0,1),(3,2,3)]),(3,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(0,0,3)]),(3,[(1,1,2),(1,0,3)]),(1,[(2,0,3),(1,1,2)]),(2,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(3,1,2)]),(3,[(2,0,3),(2,1,2)]),(2,[(2,0,3),(2,1,2)]),(0,[(0,1,2)]),(4,[(0,2,3),(1,0,1)]),(4,[(0,2,3),(3,0,1)]),(5,[(0,0,1)]),(0,[(0,1,2),(1,0,3)]),(0,[(2,0,3),(0,1,2)]),(41,[]),(42,[]),(0,[(2,0,3),(2,1,2)]),(0,[(2,0,3),(3,1,2)]),(43,[]),(4,[(1,2,3),(1,0,1)]),(0,[(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,1,2)]),(44,[]),(45,[]),(46,[]),(47,[]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(1,2,3),(2,0,4)]),(1,[(1,2,3),(2,0,4)]),(5,[(3,1,2)]),(5,[(2,1,2)]),(5,[(1,0,2),(1,1,2)]),(5,[(1,0,1),(1,1,2)]),(5,[(1,0,1),(1,0,2)]),(0,[(1,2,3),(1,1,4)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,1,2),(1,3,4)]),(3,[(1,0,2),(1,3,4)]),(48,[]),(49,[]),(0,[(1,1,2),(1,2,3),(1,1,5)]),(0,[(1,1,2),(1,2,3),(2,3,4)]),(0,[(1,1,2),(1,1,3),(1,2,5)]),(0,[(1,1,2),(1,1,3),(2,3,4)]),(15,[(1,1,2)]),(4,[(1,0,3),(1,2,4)]),(11,[(1,0,2)]),(16,[(1,2,3)]),(3,[(1,0,3),(1,2,4)]),(12,[(1,0,2)]),(39,[(1,1,2)]),(0,[(1,1,3),(1,1,2),(1,2,4)]),(0,[(1,1,3),(1,1,2),(2,3,5)]),(0,[(1,1,2),(1,1,3),(2,2,5)]),(4,[(1,1,3),(1,0,3),(1,0,4)]),(3,[(0,0,3)]),(3,[(0,1,3)]),(0,[(1,0,2),(1,0,3)]),(14,[(2,0,2)]),(4,[(1,0,1),(1,0,3),(1,1,3)]),(8,[(1,1,2)]),(0,[(1,0,2),(1,1,3),(1,2,3)]),(30,[(1,1,2)]),(0,[(1,0,1),(1,1,3),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,1,3)]),(4,[(1,1,3),(1,2,4)]),(4,[(1,1,2),(1,3,4)]),(4,[(1,1,3),(2,2,4)]),(4,[(1,1,2),(2,3,4)]),(4,[(1,1,3),(1,1,2)]),(1,[(1,1,3),(1,2,4)]),(16,[(1,1,2)]),(3,[(1,1,2),(1,2,3)]),(1,[(1,0,1),(1,1,3),(1,2,3)]),(3,[(1,2,3),(3,0,2)]),(50,[]),(51,[]),(52,[]),(0,[(1,1,3),(1,2,3),(3,0,2)]),(53,[]),(2,[(1,0,3),(1,2,4)]),(1,[(1,0,1),(1,3,4),(1,2,3)]),(54,[]),(1,[(1,0,1),(1,1,2),(1,2,3)]),(3,[(1,0,2)]),(1,[(1,0,2),(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3),(3,0,2)]),(0,[(1,2,3),(1,0,1),(1,3,5)]),(2,[(1,0,2),(1,2,3),(3,1,3)]),(1,[(1,0,2),(1,2,3),(3,1,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,2),(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,0,2),(3,1,2)]),(4,[(1,0,1),(1,1,3),(1,2,3)]),(2,[(1,1,3),(1,2,3),(3,0,2)]),(55,[]),(56,[]),(4,[(1,0,3),(3,2,3)]),(14,[(1,1,2)]),(2,[(1,1,2)]),(4,[(1,0,2),(1,1,3),(1,1,4)]),(2,[(1,1,2),(0,0,3)]),(4,[(1,0,2),(1,1,3),(1,0,5)]),(3,[(1,0,2),(0,1,3)]),(30,[(2,0,2)]),(3,[(1,0,3),(1,1,2),(1,3,5)]),(0,[(1,1,3)]),(3,[(1,0,2),(1,2,3)]),(1,[(1,0,2),(1,0,3),(1,2,3)]),(20,[(1,1,2)]),(4,[(1,1,3),(3,0,3)]),(4,[(1,0,3),(1,1,3)]),(4,[(1,0,3),(3,1,3)]),(7,[(1,0,2)]),(3,[(1,1,2),(3,0,1)]),(3,[(1,1,2),(2,0,4)]),(0,[(1,0,1),(1,1,3)]),(4,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(3,2,3)]),(4,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(2,0,3)]),(3,[(2,2,3)]),(3,[(0,2,3)]),(4,[(1,2,3),(1,0,1),(1,2,5)]),(57,[]),(58,[]),(4,[(1,0,2),(1,1,2),(1,0,5)]),(8,[(0,0,2)]),(0,[(2,0,3),(1,0,1)]),(0,[(2,0,3),(2,0,1)]),(8,[(1,0,2)]),(0,[(2,1,2),(0,0,3)]),(0,[(2,1,2),(1,0,3)]),(59,[]),(0,[(1,0,2),(1,0,3),(1,2,3)]),(30,[(1,0,2)]),(0,[(1,0,3),(1,2,3),(3,0,2)]),(0,[(1,0,2),(1,2,3),(3,0,3)]),(0,[(1,0,2),(1,0,3),(1,2,5)]),(0,[(1,0,3),(2,1,4)]),(4,[(1,0,1),(3,2,4)]),(0,[(1,0,3),(1,0,1),(3,3,5)]),(8,[(3,0,1)]),(3,[(0,0,1),(1,0,1),(3,2,5)]),(8,[(2,0,1)]),(3,[(0,0,1),(1,0,1),(1,2,5)]),(4,[(0,0,1),(1,0,1)]),(3,[(1,0,3)]),(0,[(0,0,3)]),(0,[(2,2,3)]),(30,[(1,0,1)]),(30,[(2,0,1)]),(14,[(2,0,1)]),(0,[(1,0,1),(0,0,3)]),(0,[(1,0,1),(2,1,3)]),(9,[(0,0,2)]),(0,[(1,0,1),(2,2,3)]),(14,[(1,0,1)]),(0,[(2,1,3)]),(60,[]),(61,[]),(14,[(0,0,2)]),(14,[(3,0,1)]),(14,[(3,1,2)]),(14,[(2,1,2)]),(0,[(0,2,3)]),(0,[(0,2,3),(2,0,3)]),(9,[(0,1,2)]),(0,[(0,2,3),(0,0,3)]),(7,[(1,0,1)]),(9,[(3,0,2)]),(0,[(1,1,3),(0,2,3)]),(0,[(0,1,3)]),(0,[(0,1,2),(1,1,2)]),(0,[(0,1,2),(1,1,2),(2,0,3)]),(0,[(0,1,2),(1,1,2),(0,0,3)]),(0,[(0,1,2),(1,1,2),(1,0,3)]),(7,[(1,1,2)]),(0,[(2,0,3),(0,1,3)]),(0,[(2,0,3),(1,1,2),(3,3,5)]),(62,[]),(0,[(1,2,3),(0,2,3)]),(0,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(2,0,5)]),(0,[(0,2,3),(1,2,3),(0,0,5)]),(5,[(0,1,2),(1,1,2)]),(63,[]),(0,[(1,1,2),(1,1,3)]),(5,[(1,1,2),(1,0,3)]),(40,[(1,1,2)]),(32,[(1,0,1)]),(40,[(1,0,2)]),(0,[(2,1,2),(2,0,3)]),(0,[(2,1,2),(1,0,1)]),(0,[(2,1,2),(1,0,1),(1,0,3)]),(0,[(2,0,3),(1,0,1),(1,1,2)]),(0,[(1,1,2),(1,0,2)]),(0,[(1,0,2),(1,1,3),(1,2,5)]),(0,[(1,1,3),(1,2,3),(0,0,1)]),(0,[(1,1,3),(1,2,3),(2,0,1)]),(9,[(2,1,2),(1,0,1)]),(9,[(2,1,2),(2,0,2)]),(5,[(0,1,2)]),(0,[(1,0,1),(1,0,2),(1,0,3)]),(9,[(1,0,1),(1,1,2)]),(30,[(2,1,2)]),(0,[(2,0,3),(1,0,1),(2,1,2)]),(11,[(3,0,2)]),(30,[(3,0,2)]),(14,[(3,0,2)]),(11,[(0,0,1),(1,0,1)]),(11,[(2,0,2)]),(11,[(2,1,2)]),(0,[(0,0,1),(1,0,1)]),(11,[(0,1,2)]),(0,[(0,0,1),(1,0,1),(1,3,5)]),(14,[(0,0,1)]),(11,[(3,1,2)]),(30,[(3,1,2)]),(12,[(3,0,1)]),(12,[(2,0,1)]),(7,[(2,0,1)]),(11,[(2,0,1)]),(11,[(3,0,1)]),(11,[(0,0,1)]),(7,[(3,1,2)]),(7,[(2,1,2)]),(0,[(1,1,2),(2,0,3)]),(11,[(0,0,2)]),(7,[(2,0,2)]),(11,[(1,0,2),(1,1,2)]),(9,[(1,0,1),(3,2,3)]),(0,[(2,0,3),(1,0,2),(2,1,3)]),(30,[(2,0,2),(1,0,1)]),(0,[(2,0,3),(1,0,2),(0,1,3)])]
def s7_t : Tabs := (s7_C.map (mkCut true s7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(17,16),(17,1),(6,4),(6,2),(10,8),(10,2),(18,16),(18,2),(12,8),(12,4),(20,16),(20,4),(24,16),(24,8),(10,16),(18,4),(24,0),(17,0),(19,2),(5,8),(19,8),(22,8),(17,4),(9,2),(20,8),(20,0),(7,4),(18,0),(19,1),(21,1),(25,1),(3,0),(12,0),(21,4),(22,4),(14,16),(7,1),(14,8)],[],[[],[1],[2,1],[3,2,1],[0,1],[0,2,1],[0,3,2,1],[1,0,2,1],[1,0,3,2,1],[2,1,0,3,2,1],[0,1,2,3],[0,1,2,1,3],[0,1,2,3,2,1],[1,2,3],[1,2,1,3],[1,2,3,2,1],[2,3],[2],[3],[3,2],[0,1,0,2],[0,1,2,1,0],[1,0,2],[1,2,1,0],[0],[2,3,2,1],[0,2,3,2,1],[0,2],[2,3,2],[0,1,2,1,0,3],[0,1,2,3,2,1,0],[1,2,1,0,3],[1,2,3,2,1,0],[2,1,0,3],[2,3,2,1,0],[2,1,0],[3,2,1,0],[2,1,0,3,2,1,0],[1,0],[1,0,3],[0,2,1,3,2],[0,1,3,2],[0,1,0,2,1,3],[2,1,3,2],[1,3,2],[1,0,2,1,3],[1,0,2,1,3,2],[0,1,0,2,3,2,1],[0,1,2,1,0,3,2,1],[0,3,2],[0,3],[1,0,2,3,2,1],[0,2,3],[1,2,1,0,3,2,1],[0,1,0,3],[0,1,2,3,2],[0,1,2],[2,1,3],[0,2,1,3],[0,1,3],[0,1,2,1],[1,3],[1,2,1],[1,2],[1,2,3,2],[0,1,0,2,1,3,2],[1,2,1,3,2],[1,3,2,1],[0,1,0,3,2,1],[0,1,3,2,1],[1,0,2,1,0,3,2,1],[1,0,2,1,3,2,1],[1,0,2,1,0]])
theorem s7_W : TabsP true s7_R s7_T s7_t := ⟨cutsGood s7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s7_D9 : List StD := [
([sw0,sw1,sw2,sw3,sw12],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[0,10000,30003,10006,10007,4],[1,10002,30004,10008,10009,2],[1,10002,30005,10010,10011,3],[1,10002,30006,10012,10013,4],[2,10003,30007,10014,10015,3],[2,10003,30008,10016,10017,4],[3,10005,30009,10018,10019,4]])]
noncomputable def s7_D8 : List StD := [
([sw0,sw1,sw4,sw2,sw3,sw12],[[0,1],[0,1],[0,30010,10003,5],[0,30011,10005,6],[0,30012,10007,7],[0],[1,30013,10009,5],[1,30014,10011,6],[1,30015,10013,7],[5,8,2,30000,10003,30016,10014],[6,8,3,30017,10005,30018,10015],[7,8,4,30019,10007,30000,10017],[5,10003,30000,10014,10015,6],[5,10003,30018,10016,10017,7],[6,10005,30016,10018,10019,7]])]
noncomputable def s7_D7 : List StD := [
([sw0,sw1,sw2,sw3,sw13,sw14],[[9,10,30007],[9,30020,10003,11],[9,30021,10005,12],[9,4],[9,10,13,10007],[10,30022,10009,11],[10,30023,10011,12],[10,9,14,10013],[10,4],[11,10003,30007,10014,10015,12],[11,10009,30000,10003,30024,14,30025],[11,10003,30024,10009,30000,13,30026],[12,10011,30017,10005,30027,14,30003],[12,10005,30027,10011,30017,13,30006],[9,10]]),
([sw0,sw1,sw4,sw2,sw7,sw3,sw12],[[15,16],[16],[15,16,5],[17],[15,30011,10005,18],[15,30012,10007,19],[15],[16,15,5],[20],[16,30014,10011,18],[16,30015,10013,19],[5,8],[5],[18,8,30000,10005],[19,8,30018,10007],[8],[5,30016,10015,18],[5,30028,10017,19],[18,21,6,30000,10005,30018,10018],[19,21,7,30018,10007,30000,10019],[10005,18,10018,10019]]),
([sw0,sw1,sw2,sw7,sw3,sw12],[[15,5,16],[15,5,16],[15,17],[15,30029,10005,10001],[15,30030,10007,10001],[5,15,16],[16,20],[16,30031,10011,10002],[16,30032,10013,10002],[5,8],[5,30033,10015,10003],[5,30034,10017,10003],[30035,3,10018,30000,10005,30018,30009],[30036,4,10019,30018,10007,30000,30037],[30009,10005,10007,10018,10019,30035,30036]]),
([sw15,sw0,sw1,sw2,sw3,sw12],[[22,7,8,23],[22,7],[8,30038,10003,2],[8,30035,10005,3],[7,8,9],[22,7,8,24],[22,30024,10003,10001],[22,30027,10005,10001],[22,7,10006],[8,30000,10009,10002],[8,30017,10011,10002],[7,8,10012],[30000,10003,10005,10014,10015,30039,30033],[7,10017,10019],[7,10019,10017]]),
([sw0,sw1,sw4,sw2,sw3,sw10,sw12],[[25,26],[26],[25,5,30040],[25,6,30041],[25,30042,30010,27,10001],[25,30042,10007,10001],[25],[26,5,30043],[26,6,30044],[26,30045,30013,27,10002],[26,30045,10013,10002],[5,30016,30033,28,10014],[6,30018,30039,28,10015],[27,28,8,30007,30000,30019,30046,29],[30,28,30007,10007,30000,10017],[5,6],[6],[5,30016,10017,10014],[5],[6,30018,10019,10015],[7,27,30000,10017,30007,10007]])]
noncomputable def s7_D6 : List StD := [
([sw0,sw1,sw10,sw16,sw17],[[31,32,10000,30000,10001,10002],[31,10001,30000,10000,30019,29,30042],[31,10001,30018,10000,30017,33,30047],[31,10000,30016,10004,30000,34,30048],[32,10002,30024,10008,30049,29,30045],[32,10002,30050,10008,30027,33,30051],[32,10002,30052,10010,30024,34,30053],[29,33,4,30,34],[29,34,4,30,33],[33,34,3,30,29]]),
([sw0,sw1,sw2,sw5,sw14,sw17],[[35,36,30038],[35,30054,10003,37],[38],[35,30055,30056,39,10004],[35,10004,34,10005],[36,30038,10009,37],[36,30013,30044,40,10020],[34],[36,38,34,10013],[10009,37,10003,30050,30057],[10003,37,10009,30000,30026],[10003,37,41,30000,10014,30009],[39,40,42,43,41,44,13],[35,39],[36,38]]),
([sw0,sw1,sw4,sw2,sw3,sw16,sw17],[[45,46],[46],[45,30058,47],[45,30059,48],[45,30060,10001],[45,30056,10001],[45],[46,30057,47],[46,30061,48],[46,30062,10002],[46,30063,10002],[47,30033,49],[48,30039,49],[50,30035,33],[51,30038,34],[47,30000,48],[52],[47,48,53],[48,47,54],[55],[47,48]]),
([sw0,sw1,sw2,sw3,sw13,sw14,sw18],[[56,30045,57],[56,58,11],[56,59],[58],[56,57,59],[60],[57,30043,11],[57,10011],[57,56,14],[58],[57,61,30064],[11,10015],[11,14],[11,62,63],[14],[10011,59],[10015,10011],[10011,59],[56,57],[11],[57,20]]),
([sw0,sw1,sw2,sw3,sw13,sw19],[[64,30063,30007,65,10008],[11,30017,30005,51,10009],[66,65,10011,30021,67,10005,30018],[68],[30018,65,0,66,67,57,30055,10007],[64,10008,65,11],[64,30023,10011,10008],[64,66,61,10008],[33],[11,30035,10015,10009],[11,66,62,10009],[13],[10011,69,67,30004,10005,30003],[10005,10007,10011,30000,30041],[61,17,67]]),
([sw15,sw0,sw2,sw9,sw3,sw12],[[15,70,24],[2,8,71],[70,72,8],[8,30035,10005,29],[73,8],[70,30000,30017,74,10001],[70,10001,75,10002],[70,30024,10005,10001],[70,76,10006],[24],[77,10005,30017,53,10015,30039],[76,53,10021,75,10019],[10002,10005,30000,53,10015,30024],[74,75,10002,76,53,10012],[10005,76,10019,10017]]),
([sw0,sw1,sw2,sw7,sw3,sw20,sw12],[[78,79,80],[78,80,79],[81],[78,80,18],[82],[78,59],[79,78,80],[83],[80,78,18],[84],[80,85],[86],[79,30019,18],[79,18,30016],[79,10017],[18,79,30018],[79,18],[10019,59],[87],[18,10019],[10017,59]]),
([sw0,sw1,sw4,sw2,sw3,sw21,sw16],[[56,64],[64],[56,30005,88],[56,89],[90],[56,89],[56],[64,30002,88],[64,91],[92],[64,91],[88,30017,51],[51,89],[90],[51,88,89],[88,53],[88,51,53],[93],[48,89,10015],[94,53,95],[88,51]]),
([sw0,sw1,sw4,sw2,sw3,sw22,sw12],[[30000,85,89],[96],[79,97,28],[28,89],[30010],[28,89],[98],[89,85,97],[97,85],[30013],[97,85],[79,85,28],[28,85],[29],[28,85],[89,28,18],[99],[89,53],[100],[18,54],[7,85,30000]]),
([sw23,sw0,sw1,sw4,sw2,sw3,sw12],[[0,19,17],[19,20],[19,17],[19,8],[6,95,21],[51],[30000,77,95],[75],[101,102,103],[21,95],[19,30004,21],[104],[95,77,101],[21,105],[19,30001,21],[101,19,77],[21,95],[19,30000,21],[95,10015],[19,49],[19,49]]),
([sw24,sw0,sw1,sw2,sw3,sw25,sw12],[[106],[107,29,108],[106,109],[29,17],[30010],[28,30056,30030],[98,30063,110],[28,30017,111],[28,30000,112],[30000,28,113],[28,10007],[28,112,98],[28,98,112],[114],[28,115],[98,28,112],[116],[98,53],[117],[112,54],[113,115]]),
([sw0,sw1,sw2,sw7,sw3,sw22,sw12],[[118,79,97],[118,97,79],[96],[118,89],[30010],[118,89],[79,118,97],[98],[97,85],[30013],[97,85],[28],[79,53],[30016],[79,53],[30035,30018,89],[3],[10019,89],[119],[95,10019,120],[30036,89,30000]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[96,98,10000,18,85,10001,89],[96,28,10001,10000,121,59],[10000,98,18,89,122,10004],[30010,10006],[10000,98,30030,89,10007,30000,10013],[98,28,122,85,118,10003],[18,85,123,96,10005],[30013,10012],[95,96,10007,30032,85,10013,30024],[18,122,124],[30016,122,10016],[122,30034,10017,10003],[30018,18,10018],[18,30036,10019,10005],[4,30036,30000,85,10007]]),
([sw23,sw0,sw1,sw2,sw7,sw3,sw12],[[15,17],[17,95,20],[17,8],[4],[21,95],[125],[126,95],[126,127,103],[75],[21,95],[21,30004,127],[95,126,102],[104],[21,105],[95,30001,21],[101],[95,128],[21,30000,127],[21,95],[21,30000,127],[95,10019,10022]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,44,17,105],[17,44,20,95],[17,44,8,105],[3,44,30035,105,10005,30000,10018],[30018,30000,10007],[75,104,10000,105,95,19,10001],[75,101,10001,10000,127,63],[10000,10018,30004,95,10005,30018],[105,104,10000,44,30000,10006,19],[95,101,10002,126,128,10003,105],[10002,10005,30001,105,10011,30050],[95,75,19,30024,10012],[10003,95,30000,128,10015,30039,10005],[105,75,19,30038,10016],[105,19,10019,30035,10018]]),
([sw26,sw0,sw1,sw2,sw3,sw12,sw27],[[129],[130,10002],[30016],[30018],[30000],[30013],[130,10002],[131,128],[130,41,132],[130,44,128],[130,128,30000],[130,128],[10002,133],[10002,44],[10002,128],[130,128],[130,132,134],[135],[128,130,132],[136],[137]]),
([sw28,sw0,sw1,sw2,sw3,sw12,sw27],[[138],[139],[140,30016,41],[130,30018,141],[138,30000,41],[130,30046],[30000,130,41],[142,143],[130,41,144],[130,145,146],[130,41,30065],[41,147,130],[143,148,144],[41,149,146],[8,147,30046],[130,41,143],[130,143],[150],[144,41],[151],[152]]),
([sw0,sw1,sw4,sw2,sw3,sw12,sw27],[[30000,10001,10002],[139],[10001,30040,54],[10001,30041,53],[10001,30056,54],[10001,30010,0],[138],[10002,30043,54],[10002,30044,53],[10002,30063,54],[10002,30013,8],[54,30016,140],[53,30018,141],[139,30000,54],[8,30000,30046],[48,54],[47,53],[153],[48,54],[154],[155]]),
([sw29,sw0,sw1,sw2,sw3,sw25,sw12],[[156],[98,30013,17],[17,30016,28],[156,30018,98],[98,30056,30030],[157],[98,30063,158],[28,30017,159],[98,30000,160],[98,30000,10006],[98,10006,10023],[98,160,28],[28,98,160],[161],[28,115],[98,28,160],[162],[98,53],[163],[160,54],[4,115,30000]]),
([sw0,sw30,sw1,sw2,sw3,sw12],[[17],[17,19,104,10001],[17,127,101,10000],[10001,104,30010,95,10005,30018,10011],[19,89,10007,104,10024],[17,19,104],[17,19,101],[3,21,30002,95,10005,30018,10018],[19,89,10007,21,10019],[17,10002,126,10003],[17,30001,10011,10002],[17,19,10012],[17,30000,10015,10003],[17,19,10016],[19,10019,10007]]),
([sw15,sw0,sw1,sw31,sw2,sw3,sw12],[[164,165,166],[165,164],[3,30007,8],[167,77],[3,95,167],[168],[169,165,95],[8,30024,77],[167,170],[167,95],[165,66],[8,30000,95],[167,77],[167,171],[165,66],[172],[173],[165,30000,104],[30000,95,77],[165,66],[165,174]]),
([sw15,sw0,sw1,sw2,sw3,sw10,sw12],[[25,175,139],[175,25],[28,30016,20],[28,30018,3],[28,30007,29],[176],[177,175,158],[28,30027,178],[28,30024,178],[28,30024,178],[175,178],[28,30017,178],[28,30000,178],[28,30000,178],[175,178],[30000,54,53],[173],[175,53,10019],[172],[175,54,10017],[175,54,30000]]),
([sw29,sw32,sw0,sw1,sw2,sw3,sw12],[[0,30018,17],[156],[17,30054,117],[17,30059,100],[156,10005,117],[157],[0,30000,75],[117,100],[117,100],[28],[75,179],[117,30001,75],[100,30000,75],[117,10005],[117,180,10023],[117,179,100],[100,148,160],[100,179],[117,148,179],[117,181],[10005,180]]),
([sw33,sw0,sw1,sw2,sw3,sw12,sw17],[[182,183],[183,182],[50,77],[30018],[30000],[30016],[184,77,185],[50,170],[50,41,77],[50,44,77],[50,41,77],[50,77],[50,148,170],[50,44,170],[50,44,170],[77,41],[77,44],[77,41],[30000,44,41],[186],[187]])]
noncomputable def s7_D5 : List StD := [
([sw0,sw1,sw4,sw10,sw16,sw17],[[31,32],[32],[31,30049,10001],[31,30027,10001],[31,30024,10001],[31],[32,30019,10002],[32,30017,10002],[32,30000,10002],[188,30019,29],[189,30017,33],[190,30000,34],[6,191,153],[17,192,7],[6,193,17]]),
([sw0,sw1,sw10,sw34,sw16,sw17],[[31,10002],[31,29],[29],[31,194,195],[31,195,196],[10002,195],[32,10002,10012],[10002,196],[10002,195],[31],[29,197,198],[29,199,200],[30,194,42],[30,199,20],[29]]),
([sw0,sw1,sw10,sw16,sw35],[[31,30024,10002,201],[31,201,202,203,10005],[31,204,205,206,10025],[34],[10002,10005,207,30050,10008,30045],[10002,201,204,30024,10008,30051],[10008,17,10002,30000,30066],[202,203,204,201,191,205],[14,203,202,208,10005,209],[42,206,201,208,203,210]]),
([sw15,sw2,sw5,sw6,sw12],[[96,8,30038,10003],[8,211,212],[8,211,213],[214,8],[215,75,171,10003,30024,30017,10009],[10003,104,10009,30000,30027],[10003,216,10017,10026],[8],[171,215,216,10026,10017],[216,10026,10017]]),
([sw0,sw9,sw6,sw16,sw17],[[217,218,77,30043,10001,30010,10004],[219,220,77,30044,10001,30011,10000],[10001,221,10000,30017,30047],[77,222,10004,30000,30048,10001],[219,217,141,223,224,225,226],[223,217,227,219],[34,217,223,228,207,17,53],[33,219,224,77,229,109],[224,219,227,217],[77,17,230,217]]),
([sw0,sw1,sw36,sw6,sw16,sw17],[[218,30000,231],[232],[218,30041,233],[218,233,234],[218,30060,10000],[231,30043,235],[236],[231,30063,10010],[231,235,237],[130,30019,219],[218,234],[237,233],[234,235],[231,237],[234,233,235]]),
([sw0,sw1,sw36,sw10,sw18,sw17],[[31,170],[33],[31,170],[33],[31,238,89],[130,170],[239,128,240],[241,170,10010],[170,10010],[31,170],[33],[130,238,89],[242,170,148],[170,130],[130,89]]),
([sw0,sw1,sw2,sw5,sw19,sw17],[[243,30022,149],[149,30027,37],[244],[182,30056,10004],[65,10004,67],[243,245,37],[243,30013,181],[246],[243,149,115],[37,30016,179],[247],[37,149,181],[42,149,148],[65,149,67],[67,181]]),
([sw15,sw0,sw2,sw6,sw10,sw12],[[248,26],[98,30067,28],[28,248,213],[28,148,29],[249],[28,30000,171],[28,171,95],[28,30024,178],[28,178,171],[95,28,53],[250],[251,53,10027],[28,171],[95,178],[171,53,30000]]),
([sw0,sw1,sw2,sw5,sw14,sw27],[[149,30038,41],[149,30006,37],[252],[130,30004,253],[9,41,67],[41,30002,37],[217,30061,254],[246],[67,149,115],[37,41,254],[37,149,253],[255],[256,149,41],[9,149,67],[67,41,115]]),
([sw15,sw2,sw36,sw3,sw6,sw12],[[257,258,8],[8,258,259],[8,260,242],[8,260,261],[214],[8],[171,30000,170],[104,30017,10003],[170,10028,10019],[262,30024,10029],[104,171,170],[171,178],[8],[171,10019,10017],[170,10019,178]]),
([sw0,sw1,sw2,sw3,sw13,sw37],[[148,30007,145],[148,30005,178],[178,30004,53],[171],[0,145,67],[145,263,178],[145,148,178],[53,178,115],[10002],[263,148],[217,145,53],[10003],[263,148],[10005],[0,148,67]]),
([sw23,sw0,sw1,sw36,sw3,sw16],[[264,17],[17,20],[20,17],[265,95,149],[17,65,104],[149,95],[75],[149,95],[104,127,170],[104,95],[170,10011,53],[95,149],[104,95],[104,149,127],[95,149]]),
([sw0,sw1,sw2,sw5,sw13,sw38],[[148,30038,266],[148,267],[268],[269],[0,267],[266,115],[266,148,115],[266,115],[270],[40,148],[271,267],[20,148,10003],[268,148],[0,267],[0,148,267]]),
([sw29,sw1,sw2,sw5,sw25,sw12],[[98,30068,96],[96,30069,148],[156],[98,95],[157],[98,118],[118],[118],[118],[98,148,118],[118],[98,118],[98,95],[118],[95,148,118]]),
([sw24,sw1,sw2,sw5,sw25,sw12],[[98,29,272],[29,109],[273],[95],[98,30056,253],[98,118],[118],[118],[118],[98,253,118],[118],[98,118],[98,118],[118],[118]]),
([sw23,sw0,sw1,sw7,sw3,sw16],[[274,17],[17,20],[4],[181,95,21],[17,181],[181,95],[75],[21,95],[21,127,171],[104],[181,171,21],[95,181],[21,95],[21,127],[95,53]]),
([sw0,sw1,sw2,sw3,sw21,sw27],[[149,275,145],[149,30005,178],[149,30004,178],[139],[9,145,67],[145,30002,178],[145,30001,178],[138],[67,149,115],[66,275,54],[130,149,53],[276],[141,149,54],[277],[29,67,54]]),
([sw15,sw0,sw2,sw3,sw25,sw12],[[278,17,156],[17,181],[278,171,53],[22,181,95],[115],[171,30017,54],[53,30000,178],[22,171,95],[171,178],[171,53],[262],[77,53,10019],[75],[171,54,10017],[95,53,178]]),
([sw23,sw0,sw1,sw3,sw10,sw12],[[25,17],[17,20],[3,54],[279,54,280],[53],[254,281,170],[178,30024,282],[254,170],[281,178],[254,30000,283],[178,282],[281,254],[75],[281,10030,30035],[281,254]]),
([sw0,sw30,sw1,sw3,sw10,sw12],[[17],[17,281,77],[77,30006,282],[149,170],[281,234,10024],[17,281,20],[3,282,54],[149,77],[281,234,10019],[17,30000,170],[17,77],[17,254,281],[17],[281,10019,234],[281,149]]),
([sw15,sw2,sw36,sw9,sw3,sw12],[[17,284,181],[75,285],[17,284,181],[181,95,53],[73],[286],[287],[75,53],[75,53],[75,95,286],[104,95],[104,53],[75,53],[75,53],[95,174]]),
([sw29,sw32,sw1,sw36,sw3,sw12],[[0,170],[17,30059,117],[285],[117,10005],[288],[170,117],[117,170],[98],[170,181,75],[117,181],[10005,148,181],[75,179],[117,10005],[117,181],[10005,148,181]]),
([sw15,sw39,sw1,sw2,sw3,sw12],[[20,77,178],[178,20,289],[20,170,54],[242,253],[290],[75,77],[77,170,54],[177],[77,178],[178,30000,54],[178,10029,21],[170,178],[170,54],[170,10028,21],[10011,54,291]]),
([sw0,sw1,sw2,sw20,sw21,sw17],[[292,170],[292,170],[293],[253],[292,95],[95,77,54],[294],[295],[170,296,67],[174,170,10016],[235,170,10014],[170,54],[7,54,293],[7,95,174],[6,95,54]]),
([sw23,sw0,sw1,sw2,sw3,sw21],[[9,19,288],[19,297],[19,298],[174,95],[19,288],[149,19,95],[174,170,149],[149,95],[283],[174,299,234],[170,115,67],[282],[174,10015],[75,19,10031],[10015,174]]),
([sw28,sw4,sw2,sw3,sw22,sw12],[[10032],[95,30070,54],[96,30071,170],[30046],[95,30046,54],[54,170],[53,95],[300],[54,67],[95,54,170],[301],[96,53],[302],[95,54,303],[304,54,30000]]),
([sw23,sw0,sw1,sw2,sw3,sw13],[[0,288],[288,170,20],[288,170,54],[305,95,174],[0,288],[104,170],[174,170,149],[104,95],[77],[95,126],[170,126],[126],[170,126],[104,170,126],[126]]),
([sw40,sw0,sw1,sw4,sw2,sw3],[[0,77,67],[67,170,115],[22,67,306],[67,77,53],[307,95,54],[30000,77,170],[253],[115,170],[77,67,115],[149],[95,77,54],[67,115],[54,77],[53,67],[77,53,67]]),
([sw23,sw28,sw4,sw2,sw3,sw12],[[0,170,30007],[22,20,306],[20,170,149],[149,95],[65],[10032],[149,30038,95],[170,30038,149],[170,30038,104],[104,170,282],[254,95,21],[282,149],[170,282,95],[170,149],[95,149]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,77,17],[17,20],[17,77,149],[149,95],[65],[149,77,95],[149,170],[77,95,149],[77,174],[95,77,282],[170,171,75],[95,149],[77,282,95],[77,149],[95,149]]),
([sw0,sw1,sw2,sw7,sw3,sw41],[[181,18],[18],[18],[18],[181,18],[18],[18],[181,18],[18],[18],[18],[18],[18],[18],[181,18]]),
([sw42,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,308,309],[98,96,77],[98,77,113],[98,157,77],[98,77,282],[181,98,53],[114],[113,115],[98,282],[310],[98,181],[117],[113,54],[113,181]]),
([sw24,sw1,sw2,sw3,sw22,sw12],[[98,77,96],[96,308],[98,96,77],[30030],[98,30010,77],[98,77,282],[181,98,53],[114],[282,115,53],[98,282],[310],[98,181],[117],[282,54,181],[14,181,10023]]),
([sw23,sw0,sw1,sw2,sw3,sw43],[[65,288],[288,65],[65,181],[181,282,149],[65],[181,77,170],[149,170],[282,95],[10023],[95,181],[181,115,53],[10033],[77,282,95],[10031],[30000,282,10022]]),
([sw44,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,283],[98,253,77],[98,77,300],[98,113,77],[98,77,253],[283,98,181],[114],[282,115,53],[98,283],[310],[98,181],[117],[283,54,181],[14,181,30056]]),
([sw40,sw0,sw1,sw2,sw7,sw3],[[15,77,113],[70,115,311],[312,77,53],[104,115,313],[314,282,21],[282,77,170],[115,170],[180],[77,95,115],[95,77,282],[235],[53,115],[54],[77,53,95],[10022,115]]),
([sw29,sw1,sw2,sw3,sw22,sw12],[[282,77,170],[115,170],[282,95],[30030],[67],[95,282],[170,115,53],[114],[282,115,53],[77,282,95],[310],[77,53,98],[117],[282,54,315],[14,115,174]]),
([sw44,sw1,sw2,sw3,sw12,sw37],[[282,77,217],[217,283],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,174],[30046],[77,282,253],[77,53,235],[30040],[282,174],[30041],[30056]]),
([sw0,sw1,sw2,sw3,sw12,sw45],[[282,77,253],[115,283,174],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,115,174],[30013],[77,282,253],[77,53,235],[30016],[282,174],[30018],[30000]]),
([sw40,sw0,sw1,sw2,sw3,sw12],[[0,77,174],[174,282],[316,77,149],[174,282],[53],[282,77,283],[174,283],[77,253],[77,174],[174,77,282],[283,171],[282,174],[77,282,174],[77,149],[282,174]]),
([sw40,sw0,sw1,sw2,sw3,sw22],[[53,77,113],[53,282,115],[235,53],[315,282,235],[14],[282,77,253],[115,283,171],[53,253,77],[10023],[235,77,282],[53,115],[10033],[77,53,253],[10031],[10022]]),
([sw40,sw0,sw1,sw2,sw3],[[0,174,67,77,10001,113],[67,174,22,115,282,10002,317],[67,149,316,53,77,10003,318],[113,174,307,235,282,10005,21],[253,282,10000,77,10002,10001],[174,115,10001,10000,10003],[77,115,10001,253,67,10005,10004],[174,10003,282,77,10009],[10002,67,235,115,10011,10005],[77,174,10003,253,282,10015,10005]]),
([sw0,sw46,sw1,sw2,sw3,sw12],[[174],[282,77,253],[149,283,171],[282,253,77],[77,67,10024],[149,282],[149,77],[149,282],[0,67,30000],[253,282,77],[283,171],[282,149],[77,282,253],[77,149],[282,149]]),
([sw47,sw0,sw1,sw2,sw3,sw12],[[0,77,253],[149,20,319],[253,77],[282],[181],[253,77],[149,170],[77,253],[77,174],[253,77],[170,235],[170,149],[77,253],[77,149],[30000,149,235]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[253,77],[315,283,171],[77,253],[113],[253,67,315],[253,77],[315,171,283],[320],[67,115],[77,253],[310],[253,181,67],[117],[315,235],[14,67,30000]]),
([sw29,sw11,sw1,sw2,sw3,sw12],[[0,77,253],[253,77],[315,170],[77,253],[234],[315,320],[253,77],[283],[235,181],[253,77],[315,235],[170,179,21],[77,253],[77,181,235],[315,235]]),
([sw29,sw48,sw0,sw1,sw2,sw3],[[0,30000,67],[283],[235,10034,113],[113,10035,115],[113,10036,115],[0,10024,174],[174,115,306],[235,181],[174,235,181],[235,30063,180],[115,30017,174],[115,30000,178],[235,115,181],[181,235],[174,282]]),
([sw0,sw1,sw2,sw3,sw49,sw27],[[235,240],[256,283,174],[282,253,178],[235,174,283],[256,240],[235,282],[240,235],[282,240],[8,235,10002],[256,283,174],[235,256,253],[321],[256,235],[136],[256,240]]),
([sw26,sw50,sw1,sw2,sw3,sw12],[[30010],[235,10002],[170],[95],[240],[10002,235],[0,256,321],[0,282,253],[0,235,322],[235,282],[10002,235],[10002,178],[256,282,253],[235,256,253],[256,235]]),
([sw0,sw1,sw2,sw3,sw51,sw27],[[235,30046,253],[256,283,178],[178,253],[235,178,253],[256,253,30065],[235,282],[256,235],[282,178],[8,235,30046],[256,253],[235,256,253],[321],[256,235],[136],[256,322]]),
([sw0,sw1,sw2,sw3,sw52,sw12],[[315,170],[315,170],[282,67],[113],[315,67],[240,315,282],[315,115,67],[320],[170,115,67],[315,282,67],[310],[170,181,67],[315,282,117],[315,30000,282],[14,67,104]]),
([sw53,sw0,sw1,sw2,sw3,sw12],[[0,283,113],[42,315,320],[42,315,310],[42,283,117],[14,65,104],[283,170,315],[315,283,170],[282,95],[283,240,315],[95,315,282],[283,171],[170,179,21],[315,283,95],[170,181,240],[283,10019,315]]),
([sw28,sw4,sw2,sw3,sw12,sw27],[[10037],[256,30070,27],[27,30071,130],[256,30046,275],[256,30046,10002],[130,282],[256,253],[282,180],[8,282,30046],[256,282,130],[130,256,253],[321],[256,130,282],[136],[137]]),
([sw23,sw0,sw1,sw2,sw54,sw3],[[323,240],[324,325,326],[240,170,181],[30035],[240,282,30000],[181,240],[178,170,327],[178,30004,104],[282,95],[240,181],[240,30001,101],[240,171,283],[170,30000,104],[170,282,95],[180]]),
([sw0,sw1,sw2,sw3,sw55,sw19],[[65,30046,180],[180,30040,327],[65,10004,178],[65,180,10004],[65,180,10004],[65,327,282],[180,115],[327,65,178],[328],[65,282],[65,62],[62],[327,180],[62],[65,62]]),
([sw0,sw1,sw2,sw56,sw3,sw12],[[282,170],[115,170],[180],[282,95],[115,240],[95,282],[320],[170,115,283],[282,115,67],[310],[170,282,95],[170,181,240],[320,282,117],[313,115,30000],[282,10018]]),
([sw57,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[22,282,178],[316,253,234],[307,283,180],[0,181,113],[283,171],[113,283],[282,253,113],[283,10007,10023],[253,282,77],[283,171],[282,149],[171,283],[253,149],[283,149]]),
([sw0,sw1,sw2,sw3,sw58,sw16],[[180,240,149],[180,30040,149],[149,195,178],[195,180],[195,180],[240,30043,51],[180,195,240],[195,240],[195,149],[180,53],[20,149,53],[170],[329,180,10015],[240,180,10036],[51,240]]),
([sw29,sw59,sw1,sw2,sw3,sw12],[[253],[117,170],[100,170],[117,95],[240],[117,170],[117,170,100],[117,95],[14,180],[117,119],[170,119],[170,119],[117,119],[117,119],[95,180]]),
([sw0,sw1,sw60,sw2,sw3,sw12],[[282,170],[180],[171,170,283],[282,95],[171,240,115],[149],[95,282],[170,171,283],[282,115,67],[20,170,310],[310,282,117],[306,240,30000],[170,282,171],[170,49],[282,49]]),
([sw61,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[149,170],[149,77],[0,282,180],[240],[180,77],[180,170,149],[77,95,149],[77,180],[95,77,49],[180,235,170],[170,149],[77,54],[77,149],[95,180]]),
([sw62,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[149,282],[149,42,330],[180,283],[0,256,322],[283,30000,149],[180,283],[149,253,113],[283,180],[253,282,137],[283,195,322],[282,149],[180,283],[253,149],[283,180]]),
([sw15,sw0,sw2,sw63,sw3,sw12],[[180,77],[20,77,167],[167,20,313],[180,95],[65],[180,170,167],[180,77],[77,95,167],[77,180],[167,77],[180,30000,77],[77,254],[180,167,170],[95,254],[95,180]]),
([sw15,sw0,sw1,sw2,sw3,sw64],[[180,77],[104,313],[104,77,149],[180,95],[104,65],[180,77],[180,170,149],[77,95,104],[77,180],[104,77,49],[180,171],[95,149],[180,30000,77],[77,149],[95,180]]),
([sw15,sw0,sw1,sw31,sw10,sw12],[[331,77,180],[332,333],[20,30007,28],[180,77],[334],[180,77],[77,30024,332],[332,170],[77,180],[28,30000,170],[180,77],[170,178],[10038],[104,30000,335],[77,180]]),
([sw15,sw65,sw0,sw1,sw2,sw3],[[8,30000,240],[137,240],[178,137,282],[240,10035,149],[240,10036,149],[8,10039,178],[8,10040,240],[149,215,336],[149,104,215],[149,240],[178,30027,149],[178,30024,149],[240,30017,49],[240,30000,49],[180,337,254]]),
([sw66,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[22,20,306],[20,77,8],[180,282,49],[0,51,101],[282,77,170],[49,170],[77,338],[77,240,101],[49,77],[49,171],[282,149],[77,282,171],[77,49],[282,49]]),
([sw15,sw0,sw67,sw2,sw3,sw12],[[180,171],[22,20,313],[20,77,100],[180,171],[65],[180,171],[180,30024,100],[77,95,100],[171,180],[100,77],[180,171],[95,149],[180,54,77],[77,10021,104],[171,180]]),
([sw0,sw1,sw2,sw3,sw58,sw17],[[180,77],[180,170,50],[77,253],[50,180,253],[77,180],[50,77],[180,195,170],[50,170,195],[170,195],[180,253,77],[253,77],[77,253],[339,180,54],[186],[50,307]]),
([sw33,sw0,sw1,sw2,sw54,sw17],[[340,77,180],[341,342],[343,77],[30009],[171],[180,77],[180,170,341],[77,30024,341],[77,180],[343,77],[180,30000,170],[343,149,170],[77,30000,180],[77,149],[10022]])]
noncomputable def s7_D4 : List StD := [
([sw0,sw4,sw10,sw16,sw38],[[180],[188,30018,344],[189,30000,171],[345,344,95],[188,171],[189,344],[345,95],[344,346,171],[95,171,282],[95,344,282]]),
([sw0,sw1,sw10,sw16,sw68],[[180,171],[188,95],[171,180],[10000],[180,171],[95,347],[10008],[171,180],[20,180,282],[20,282]]),
([sw0,sw1,sw10,sw18,sw38],[[347,30000,180],[347,283,178],[171],[345,180,240],[180,235,178],[189,347,348],[170],[40,347,235],[240,347,283],[20,283]]),
([sw15,sw2,sw5,sw25,sw12],[[28,282,98],[28,171],[28,282,170],[240],[171,28,282],[116],[77,53,10026],[28,170],[282,10026,180],[170,53,149]]),
([sw23,sw0,sw6,sw10,sw12],[[248,171,178],[178,170],[349,171],[240],[347,171,170],[178,170,349],[171,178],[178,171,101],[170,178],[171,349]]),
([sw0,sw30,sw6,sw10,sw12],[[178],[347,170],[349,170],[171,240,10024],[347,170],[349,170],[248,240,10027],[240,171,101],[170,347],[170,349]]),
([sw15,sw39,sw9,sw3,sw12],[[8,171],[350,351,170],[100,253,315],[352],[350,8,170],[353],[171,178],[170,253],[170,178],[10011,54,291]]),
([sw0,sw9,sw6,sw16,sw35],[[218,30011,180],[220,95],[221,180,195],[77],[180,195,178],[195,349],[17,195,171],[95,180],[17,180,171],[17,54,315]]),
([sw15,sw36,sw6,sw10,sw12],[[178,171],[178,354,170],[8,171],[249],[104,171,170],[178,170,8],[171,178],[178,171,8],[170,178],[171,54,30000]]),
([sw4,sw36,sw6,sw16,sw17],[[195,171,180],[45,195,236],[195,170,50],[51,195,171],[130,171,170],[171,170,50],[98,355,77],[95,54,149],[170,171,51],[171,355,170]]),
([sw0,sw1,sw69,sw16,sw17],[[256,171,253],[256,253,171],[256,283,171],[256,253,67],[356,95,357,10041],[253,282,10042],[283,171],[256,253],[171,256,283],[256,171]]),
([sw15,sw65,sw0,sw2,sw6],[[8,171],[358,171,253],[358,10035,54],[359,358,95],[8,10026,178],[171,215],[359,171,360],[171,30000,54],[359,171,95],[359,54,282]]),
([sw0,sw9,sw6,sw14,sw27],[[54,171,180],[282,171,219],[54,171,253],[361,180,10001],[180,54,282],[253,219,362],[219,171],[282,54,180],[219,171],[219,171]]),
([sw0,sw1,sw70,sw18,sw17],[[282,170],[45,170],[171],[282,180,67],[180,282,178],[54,282,10043],[170,178],[42,170,54],[170,282,180],[42,282,54]]),
([sw0,sw1,sw7,sw10,sw41],[[282,170],[180],[315,170],[282,67],[320],[308,282,77],[170,65,67],[315,310],[54,282],[170,282,67]]),
([sw29,sw48,sw1,sw2,sw5],[[0,67],[282,10034,363],[54,10035,195],[77],[67,282,178],[67,262],[178,67,282],[54,282,195],[180,195,171],[178,282]]),
([sw15,sw71,sw9,sw3,sw12],[[262,308,171],[350,351,313],[308,171,180],[352],[262,171],[262,353,364],[171,180],[180,171],[170,178],[171,180]]),
([sw0,sw1,sw72,sw17,sw73],[[180,170,282],[191,170],[282,180,95],[365],[180,282,95],[170,178],[109,170,30013],[170,180],[321],[322]]),
([sw74,sw0,sw1,sw2,sw17],[[182,293,366],[293,40,367],[180,170,30016],[293,180],[293,170,40],[40,170],[40,293,95],[293,77],[293,40,170],[170,54]]),
([sw0,sw1,sw72,sw17,sw68],[[40,170],[40,170],[40,180,95],[366],[180,77],[170,40,293],[367],[170,180],[29,170,30016],[215]]),
([sw40,sw28,sw4,sw2,sw3],[[0,95,30007],[22,368,306],[368,77,149],[368,95,149],[10032],[95,30072,149],[77,30007,149],[180,77,54],[53,95],[95,54,77]]),
([sw75,sw0,sw1,sw10,sw12],[[25,29],[54,95,347],[29,25],[203],[347,95],[347,95],[322,180,195],[180,195,369],[95,347],[95,347]]),
([sw23,sw76,sw9,sw3,sw12],[[369,77,180],[370,371,372],[369,95,180],[373],[180,77],[77,95,104],[77,180],[180,282],[95,178],[95,180]]),
([sw23,sw0,sw9,sw77,sw12],[[369,77,180],[370,95,374],[369,77,180],[65],[180,77],[126,95],[77,180],[180,77],[95,178],[77,180]]),
([sw23,sw0,sw9,sw3,sw78],[[369,77,178],[178,95],[369,95,180],[369,77,104],[180,77],[77,95,104],[104,178,171],[178,171,180],[95,77,178],[77,180,95]]),
([sw79,sw0,sw1,sw2,sw3],[[0,77,67],[67,69,375],[67,77,376],[69,180,54],[282,77,253],[54,283,171],[77,253],[54,77],[283,171],[77,54]]),
([sw0,sw1,sw2,sw80,sw43],[[282,95],[171,283],[282,95],[377],[95,282],[283,171],[378],[95,282],[379],[34,282,54]]),
([sw23,sw0,sw1,sw2,sw81],[[180,171],[370,95,178],[370,77,149],[180,171],[180,171],[180,283],[178,95,149],[95,77,282],[180,171],[180,283]]),
([sw0,sw82,sw1,sw2,sw3],[[0,171,180],[282,171,283],[171,283],[282,253,77],[22,282,149],[149,253],[149,171],[253,282,77],[283,171],[171,282]]),
([sw40,sw0,sw1,sw2,sw3],[[0,171,180],[22,95,149],[149,77],[180,171],[180,171],[171,283],[149,95],[95,77,282],[180,171],[171,283]]),
([sw47,sw0,sw1,sw2,sw54],[[323,95],[283,171],[95,283],[10036],[283,95,171],[171,283],[283,30004,149],[95,282],[95,30001,180],[180,30000,77]]),
([sw0,sw1,sw7,sw72,sw17],[[282,171,283],[180],[171,283],[282,95],[380],[95,282],[283,171],[380,77,54],[34,282,30000],[171,282]]),
([sw23,sw0,sw1,sw3,sw72],[[369,171,178],[178,95],[369,171,30000],[369,77,54],[283,171],[178,95,282],[171,283],[178,171,283],[178,77,282],[171,283]]),
([sw0,sw1,sw2,sw52,sw17],[[282,171,283],[171,283],[381],[282,95],[95,282],[380],[283,171],[379],[171,282],[34,282,54]]),
([sw62,sw4,sw2,sw3,sw12],[[382,171,283],[171,335,383],[171,283,384],[171,54,137],[382,283],[382,253],[283,180],[137,283],[335,149],[283,180]]),
([sw15,sw0,sw63,sw10,sw12],[[369,171,283],[385,20,372],[369,171,180],[65],[385,171,180],[104,95],[171,180],[180,171],[95,347],[171,180]]),
([sw15,sw0,sw1,sw10,sw64],[[20,171,283],[104,313],[29,171,149],[20,65,104],[104,171,180],[104,95],[171,180],[180,171],[95,347],[171,149]]),
([sw83,sw4,sw2,sw3,sw12],[[0,98,114],[98,54,109],[114,109],[95,54,67],[114,77,54],[382,95,53],[54,67],[114,54,77],[114,53],[95,54,368]]),
([sw33,sw0,sw2,sw84,sw17],[[369,77,180],[369,77,349],[180,14,372],[271],[180,170,349],[349,77,170],[77,180],[180,77,262],[77,349],[170,180]]),
([sw33,sw0,sw1,sw72,sw17],[[369,109,386],[109,14],[369,77,149],[271],[387,77,262],[149,170],[77,180],[262,77],[262,347,170],[77,149]])]
noncomputable def s7_D3 : List StD := [
([sw4,sw10,sw18,sw38],[[388,170,283],[109,283,77],[345,170],[109,170,271],[20,283],[109,170,77]]),
([sw15,sw65,sw36,sw6],[[29,389,283],[358,283],[359,358,372],[390,391,392],[359,283],[359,283]]),
([sw40,sw0,sw63,sw10],[[20,283,180],[104,283,347],[180,77],[180,77],[178,283],[180,283,77]]),
([sw85,sw0,sw1,sw10],[[25,77,180],[104,170,347],[180,77],[180,77],[347,170],[180,77]]),
([sw47,sw0,sw1,sw72],[[325,77,180],[347,325,372],[325,77,180],[180,77],[347,170],[180,77]])]
def s7_D2 : List StD := []
theorem s7_I2 : LevelN true s7_T 2 s7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C3x0 : levelOK true s7_T s7_t 2 (s7_D2.map Prod.fst) ((s7_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I3 : LevelN true s7_T 3 s7_D3 := levelStep s7_B s7_W s7_I2 (chunks 16 s7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x0 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x1 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x2 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (2*16)).take 16) = true := by decide +kernel
theorem s7_I4 : LevelN true s7_T 4 s7_D4 := levelStep s7_B s7_W s7_I3 (chunks 16 s7_D4 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C4x0
  · exact s7_C4x1
  · exact s7_C4x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x0 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x1 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x2 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x3 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x4 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (4*16)).take 16) = true := by decide +kernel
theorem s7_I5 : LevelN true s7_T 5 s7_D5 := levelStep s7_B s7_W s7_I4 (chunks 16 s7_D5 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C5x0
  · exact s7_C5x1
  · exact s7_C5x2
  · exact s7_C5x3
  · exact s7_C5x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x0 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x1 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (1*16)).take 16) = true := by decide +kernel
theorem s7_I6 : LevelN true s7_T 6 s7_D6 := levelStep s7_B s7_W s7_I5 (chunks 16 s7_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C6x0
  · exact s7_C6x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C7x0 : levelOK true s7_T s7_t 6 (s7_D6.map Prod.fst) ((s7_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I7 : LevelN true s7_T 7 s7_D7 := levelStep s7_B s7_W s7_I6 (chunks 16 s7_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C8x0 : levelOK true s7_T s7_t 7 (s7_D7.map Prod.fst) ((s7_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I8 : LevelN true s7_T 8 s7_D8 := levelStep s7_B s7_W s7_I7 (chunks 16 s7_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C9x0 : levelOK true s7_T s7_t 8 (s7_D8.map Prod.fst) ((s7_D9.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I9 : LevelN true s7_T 9 s7_D9 := levelStep s7_B s7_W s7_I8 (chunks 16 s7_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C9x0
  ))
theorem s7_L : LowN true s7_R s7_T 10 := lowSearch s7_B s7_I9 (by decide +kernel)
def stopT : Nat := 0xfffffffefffefee8fffffffefffefee8
def stopR : List Nat := [0, 1, 2, 3, 4, 5]
def stopE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33)]
theorem stopB : baseOK stopT stopR stopE = true := by decide +kernel
theorem stopS0 : SliceN true stopR stopT (0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem stopS1 : SliceN true stopR stopT (0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem stopS2 : SliceN true stopR stopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem stopS3 : SliceN true stopR stopT (0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem stopS4 : SliceN true stopR stopT (0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem stopS5 : SliceN true stopR stopT (0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
def stopZ : List SliceD := [(0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]),(0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]),(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]),(0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]),(0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4])]
theorem stopY : ∀ s ∈ stopZ, SliceN true stopR stopT s := by
  unfold stopZ
  simp only [List.forall_mem_cons]
  exact ⟨stopS0,stopS1,stopS2,stopS3,stopS4,stopS5,by simp⟩
def stopC : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def stopt : Tabs := (stopC.map (mkCut true stopZ),[(3,1),(5,1),(9,1),(17,1),(33,1),(6,2),(10,2),(18,2),(34,2),(12,4),(20,4),(36,4),(24,8),(40,8),(48,16)],[],[])
theorem stopW : TabsP true stopR stopT stopt := ⟨cutsGood stopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def stopD11 : List StD := [
([sw0,sw1,sw2,sw3,sw12,sw86],[[0,1,10000],[0,2,10001],[0,3,10002],[0,4,10003],[0,5,10004],[1,2,10005],[1,3,10006],[1,4,10007],[1,5,10008],[2,3,10009],[2,4,10010],[2,5,10011],[3,4,10012],[3,5,10013],[4,5,10014]])]
def stopD10 : List StD := []
theorem stopI10 : LevelN true stopT 10 stopD10 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem stopC11x0 : levelOK true stopT stopt 10 (stopD10.map Prod.fst) ((stopD11.drop (0*16)).take 16) = true := by decide +kernel
theorem stopI11 : LevelN true stopT 11 stopD11 := levelStep stopB stopW stopI10 (chunks 16 stopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact stopC11x0
  ))
theorem stopL : LowN true stopR stopT 12 := lowSearch stopB stopI11 (by decide +kernel)
def mw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def mw1 : Nat := 0xcccccccccccccccccccccccccccccccc
def mw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def mw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def mw4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def mw5 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def mw6 : Nat := 0xffccffccffccffccffccffccffccffcc
def mw7 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def mw8 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def mw9 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def mw10 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def mw11 : Nat := 0xffffccccffffccccffffccccffffcccc
def mw12 : Nat := 0xfefefefefefefefefefefefefefefefe
def mw13 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def mw14 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def mw15 : Nat := 0xfffffafafffffafafffffafafffffafa
def mw16 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfc
def mw17 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def mw18 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeee
def mw19 : Nat := 0xfffefffefffefffefffefffefffefffe
def mw20 : Nat := 0xfffafffafffafffafffafffafffafffa
def mw21 : Nat := 0xffffffaaffffffaaffffffaaffffffaa
def mw22 : Nat := 0xfafafafafafafafafafafafafafafafa
def mw23 : Nat := 0xffffffff00000000ffffffff00000000
def mw24 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def mw25 : Nat := 0xffffffffccccccccffffffffcccccccc
def mw26 : Nat := 0xffffffffff00ff00ffffffffff00ff00
def mw27 : Nat := 0xffffffffffff0000ffffffffffff0000
def mw28 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0
def mw29 : Nat := 0xfffffffffafafafafffffffffafafafa
def mw30 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfc
def mw31 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeee
def mw32 : Nat := 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8
def mw33 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def mw34 : Nat := 0x88888888888888888888888888888888
def mw35 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def mw36 : Nat := 0xffffffffffffaaaaffffffffffffaaaa
def mw37 : Nat := 0xffffffffffaaffaaffffffffffaaffaa
def mw38 : Nat := 0xfffffffffffff0f0fffffffffffff0f0
def mw39 : Nat := 0xffffffffffffeeeeffffffffffffeeee
def mw40 : Nat := 0xfffffffffefefefefffffffffefefefe
def mw41 : Nat := 0xfffffffffffafffafffffffffffafffa
def mw42 : Nat := 0xffffffffffeeffeeffffffffffeeffee
def mw43 : Nat := 0xfffffffffffcfffcfffffffffffcfffc
def mw44 : Nat := 0xffffffffffffff00ffffffffffffff00
def mw45 : Nat := 0xffffffffffccffccffffffffffccffcc
def mw46 : Nat := 0xfffffffffff0fff0fffffffffff0fff0
def mw47 : Nat := 0xffffffffffffccccffffffffffffcccc
def mw48 : Nat := 0xfffffefefffffefefffffefefffffefe
def mw49 : Nat := 0xffffffeeffffffeeffffffeeffffffee
def mw50 : Nat := 0xfffffffefffffffefffffffefffffffe
def mw51 : Nat := 0xeeeeeeeaeeeeeeeaeeeeeeeaeeeeeeea
def mw52 : Nat := 0xfffffffffe00fe00fffffffffe00fe00
def mw53 : Nat := 0xfffffffcfffffffcfffffffcfffffffc
def mw54 : Nat := 0xfffffffafffffffafffffffafffffffa
def mw55 : Nat := 0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8
def mw56 : Nat := 0xfffffffffffffff0fffffffffffffff0
def mw57 : Nat := 0xffffffff88888888ffffffff88888888
def mw58 : Nat := 0xfffefefefffefefefffefefefffefefe
def mw59 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def mw60 : Nat := 0xffffffffff000000ffffffffff000000
def mw61 : Nat := 0xffffffffffffffaaffffffffffffffaa
def mw62 : Nat := 0xffffffccffffffccffffffccffffffcc
def mw63 : Nat := 0xfffffffffffffefefffffffffffffefe
def mw64 : Nat := 0xfffffffffffffcfcfffffffffffffcfc
def mw65 : Nat := 0xfffffffffffffffcfffffffffffffffc
def mw66 : Nat := 0xffffffffaaa8aaa8ffffffffaaa8aaa8
def mw67 : Nat := 0xffffaaaafefeaaaaffffaaaafefeaaaa
def mw68 : Nat := 0xffffffffffee0000ffffffffffee0000
def mw69 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def mw70 : Nat := 0xffffffffeaeaeaeaffffffffeaeaeaea
def mw71 : Nat := 0xfffffffffffcfcfcfffffffffffcfcfc
def mw72 : Nat := 0xffffaaaaffffa8a8ffffaaaaffffa8a8
def mw73 : Nat := 0xffffffeeffeeffeeffffffeeffeeffee
def mw74 : Nat := 0xffffff00ff00ff00ffffff00ff00ff00
def mw75 : Nat := 0xffffaaaaaaaaaaaaffffaaaaaaaaaaaa
def mw76 : Nat := 0xfffeaaaafffeaaaafffeaaaafffeaaaa
def mw77 : Nat := 0xffffffffffffa8a8ffffffffffffa8a8
def mw78 : Nat := 0xfffffefeffff0000fffffefeffff0000
def mw79 : Nat := 0xfffffffffefe0000fffffffffefe0000
def mw80 : Nat := 0xfffffffffffe0000fffffffffffe0000
def mw81 : Nat := 0xaaaaaaaaaaaaaaa8aaaaaaaaaaaaaaa8
def mw82 : Nat := 0xfffffffffffffffefffffffffffffffe
def mw83 : Nat := 0xfffffffefffefffefffffffefffefffe
def mw84 : Nat := 0xfffffefefefefefefffffefefefefefe
def mw85 : Nat := 0xfffffffffffffafafffffffffffffafa
def mw86 : Nat := 0xffffff00ffeeff00ffffff00ffeeff00
def mw87 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def mw88 : Nat := 0xffffffffff88ff88ffffffffff88ff88
def mw89 : Nat := 0xffffffffffffeaeaffffffffffffeaea
def mw90 : Nat := 0xfafafaf8fafafaf8fafafaf8fafafaf8
def mw91 : Nat := 0xfffffffffffffffafffffffffffffffa
def mw92 : Nat := 0xfff0fff0fff0faf0fff0fff0fff0faf0
def mw93 : Nat := 0xfffffffffffc0000fffffffffffc0000
def mw94 : Nat := 0xffffffffffffffccffffffffffffffcc
def mw95 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def mw96 : Nat := 0xffffffffffaaaaaaffffffffffaaaaaa
def mw97 : Nat := 0xfffffff0fff0fff0fffffff0fff0fff0
def mw98 : Nat := 0xfffffffcfffcfffcfffffffcfffcfffc
def mw99 : Nat := 0xfffffffcffff0000fffffffcffff0000
def mw100 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def mw101 : Nat := 0xfffffffffeeefeeefffffffffeeefeee
def mw102 : Nat := 0xfffffffffffff000fffffffffffff000
def mw103 : Nat := 0xffffffffffeeeeeeffffffffffeeeeee
def mw104 : Nat := 0xffffffffffffffeeffffffffffffffee
def mw105 : Nat := 0xfffffffffff0faf0fffffffffff0faf0
def mw106 : Nat := 0xffffffffffeeff00ffffffffffeeff00
def mw107 : Nat := 0xfffffffeffff0000fffffffeffff0000
def mw108 : Nat := 0xfffffffffffefffefffffffffffefffe
def mw109 : Nat := 0xffffffffffc0ffc0ffffffffffc0ffc0
def mw110 : Nat := 0xfffffffafffafffafffffffafffafffa
def mw111 : Nat := 0xfcfcfcecfcfcfcecfcfcfcecfcfcfcec
def mw112 : Nat := 0xfcccfcccfcccfcccfcccfcccfcccfccc
def mw113 : Nat := 0xfffffffffffffaaafffffffffffffaaa
def mw114 : Nat := 0xffffffccffffffc0ffffffccffffffc0
def mw115 : Nat := 0xffffffffffccffc0ffffffffffccffc0
def mw116 : Nat := 0xfffffff0fffafff0fffffff0fffafff0
def mw117 : Nat := 0xfffffffffffaf0f0fffffffffffaf0f0
def mw118 : Nat := 0xffffffffffffc0c0ffffffffffffc0c0
def m1_T : Nat := 0x88888888888888888888888888888888
def m1_R : List Nat := [0, 1]
def m1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem m1_B : baseOK m1_T m1_R m1_E = true := by decide +kernel
theorem m1_L : LowN false m1_R m1_T 1 := lowCount m1_B (by decide +kernel)
def m2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def m2_R : List Nat := [0, 1]
def m2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem m2_B : baseOK m2_T m2_R m2_E = true := by decide +kernel
theorem m2_L : LowN false m2_R m2_T 1 := lowCount m2_B (by decide +kernel)
def m3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def m3_R : List Nat := [0, 1, 2]
def m3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem m3_B : baseOK m3_T m3_R m3_E = true := by decide +kernel
theorem m3_S0 : SliceN false m3_R m3_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) m3_B m1_B m1_L (by decide +kernel)
theorem m3_S1 : SliceN false m3_R m3_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) m3_B m1_B m1_L (by decide +kernel)
theorem m3_S2 : SliceN false m3_R m3_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) m3_B m2_B m2_L (by decide +kernel)
theorem m3_S3 : SliceN false m3_R m3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) m3_B m2_B m2_L (by decide +kernel)
theorem m3_S4 : SliceN false m3_R m3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) m3_B m1_B m1_L (by decide +kernel)
theorem m3_S5 : SliceN false m3_R m3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) m3_B m2_B m2_L (by decide +kernel)
def m3_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem m3_Y : ∀ s ∈ m3_Z, SliceN false m3_R m3_T s := by
  unfold m3_Z
  simp only [List.forall_mem_cons]
  exact ⟨m3_S0,m3_S1,m3_S2,m3_S3,m3_S4,m3_S5,by simp⟩
def m3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def m3_t : Tabs := (m3_C.map (mkCut false m3_Z),[(5,4),(3,1),(3,2),(6,2)],[],[])
theorem m3_W : TabsP false m3_R m3_T m3_t := ⟨cutsGood m3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def m3_D3 : List StD := [
([mw0,mw1,mw2],[[0,1,10000,2,3,10001],[4,1,10002,10000,3],[10001,0,5,2,10003]])]
def m3_D2 : List StD := []
theorem m3_I2 : LevelN false m3_T 2 m3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m3_C3x0 : levelOK false m3_T m3_t 2 (m3_D2.map Prod.fst) ((m3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem m3_I3 : LevelN false m3_T 3 m3_D3 := levelStep m3_B m3_W m3_I2 (chunks 16 m3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m3_C3x0
  ))
theorem m3_L : LowN false m3_R m3_T 4 := lowSearch m3_B m3_I3 (by decide +kernel)
def m4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def m4_R : List Nat := [0, 1, 2]
def m4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem m4_B : baseOK m4_T m4_R m4_E = true := by decide +kernel
theorem m4_L : LowN false m4_R m4_T 2 := lowCount m4_B (by decide +kernel)
def m5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def m5_R : List Nat := [0, 1, 2, 3]
def m5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem m5_B : baseOK m5_T m5_R m5_E = true := by decide +kernel
theorem m5_S0 : SliceN false m5_R m5_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) m5_B m3_B m3_L (by decide +kernel)
theorem m5_S1 : SliceN false m5_R m5_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) m5_B m3_B m3_L (by decide +kernel)
theorem m5_S2 : SliceN false m5_R m5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) m5_B m3_B m3_L (by decide +kernel)
theorem m5_S3 : SliceN false m5_R m5_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) m5_B m1_B m1_L (by decide +kernel)
theorem m5_S4 : SliceN false m5_R m5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) m5_B m3_B m3_L (by decide +kernel)
theorem m5_S5 : SliceN false m5_R m5_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) m5_B m2_B m2_L (by decide +kernel)
theorem m5_S6 : SliceN false m5_R m5_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) m5_B m2_B m2_L (by decide +kernel)
theorem m5_S7 : SliceN false m5_R m5_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) m5_B m4_B m4_L (by decide +kernel)
theorem m5_S8 : SliceN false m5_R m5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) m5_B m4_B m4_L (by decide +kernel)
def m5_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0x11111111111111111111111111111111,1,[2, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3])]
theorem m5_Y : ∀ s ∈ m5_Z, SliceN false m5_R m5_T s := by
  unfold m5_Z
  simp only [List.forall_mem_cons]
  exact ⟨m5_S0,m5_S1,m5_S2,m5_S3,m5_S4,m5_S5,m5_S6,m5_S7,m5_S8,by simp⟩
def m5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(0,[(1,0,2)]),(5,[]),(6,[]),(2,[(1,1,2)]),(2,[(1,0,2)]),(0,[(1,0,2),(1,1,2)]),(7,[(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)]),(8,[(1,1,2)])]
def m5_t : Tabs := (m5_C.map (mkCut false m5_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4)],[(3,4,2,5,1,6),(3,8,2,9,1,10)],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[1,0]])
theorem m5_W : TabsP false m5_R m5_T m5_t := ⟨cutsGood m5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def m5_D6 : List StD := [
([mw0,mw1,mw2,mw3],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003],[0,10000,30002,10004,10005],[1,10002,30003,10006,10007],[1,10002,30004,10008,10009],[2,10003,30005,10010,10011]])]
noncomputable def m5_D5 : List StD := [
([mw0,mw1,mw4,mw2,mw3],[[0],[],[0,30006,10003],[0,30007,10005],[],[1,30008,10007],[1,30009,10009],[2,3,20000,10003],[20000,3,4,20001,10005],[10003,10005,10010,10011]])]
noncomputable def m5_D4 : List StD := [
([mw0,mw1,mw2,mw5,mw6],[[5,30010],[5,6],[],[5,6],[6,7],[1,5],[],[8,6],[9,7],[5]])]
noncomputable def m5_D3 : List StD := [
([mw0,mw7,mw6,mw8],[[10,11],[12,11],[13,14],[2,14],[4,11],[2,11]])]
def m5_D2 : List StD := []
theorem m5_I2 : LevelN false m5_T 2 m5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m5_C3x0 : levelOK false m5_T m5_t 2 (m5_D2.map Prod.fst) ((m5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem m5_I3 : LevelN false m5_T 3 m5_D3 := levelStep m5_B m5_W m5_I2 (chunks 16 m5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m5_C4x0 : levelOK false m5_T m5_t 3 (m5_D3.map Prod.fst) ((m5_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem m5_I4 : LevelN false m5_T 4 m5_D4 := levelStep m5_B m5_W m5_I3 (chunks 16 m5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m5_C5x0 : levelOK false m5_T m5_t 4 (m5_D4.map Prod.fst) ((m5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem m5_I5 : LevelN false m5_T 5 m5_D5 := levelStep m5_B m5_W m5_I4 (chunks 16 m5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m5_C6x0 : levelOK false m5_T m5_t 5 (m5_D5.map Prod.fst) ((m5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem m5_I6 : LevelN false m5_T 6 m5_D6 := levelStep m5_B m5_W m5_I5 (chunks 16 m5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m5_C6x0
  ))
theorem m5_L : LowN false m5_R m5_T 7 := lowSearch m5_B m5_I6 (by decide +kernel)
def m6_T : Nat := 0xfffefffefffefffefffefffefffefffe
def m6_R : List Nat := [0, 1, 2, 3]
def m6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem m6_B : baseOK m6_T m6_R m6_E = true := by decide +kernel
theorem m6_L : LowN false m6_R m6_T 3 := lowCount m6_B (by decide +kernel)
def m7_T : Nat := 0xfffefee8fffefee8fffefee8fffefee8
def m7_R : List Nat := [0, 1, 2, 3, 4]
def m7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem m7_B : baseOK m7_T m7_R m7_E = true := by decide +kernel
theorem m7_S0 : SliceN false m7_R m7_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) m7_B m5_B m5_L (by decide +kernel)
theorem m7_S1 : SliceN false m7_R m7_T (0x33333333333333333333333333333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) m7_B m5_B m5_L (by decide +kernel)
theorem m7_S2 : SliceN false m7_R m7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) m7_B m5_B m5_L (by decide +kernel)
theorem m7_S3 : SliceN false m7_R m7_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) m7_B m5_B m5_L (by decide +kernel)
theorem m7_S4 : SliceN false m7_R m7_T (0x11111111111111111111111111111111,4,[2, 3, 4]) := mkSlice (w:=0) m7_B m3_B m3_L (by decide +kernel)
theorem m7_S5 : SliceN false m7_R m7_T (0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) m7_B m5_B m5_L (by decide +kernel)
theorem m7_S6 : SliceN false m7_R m7_T (0x1010101010101010101010101010101,1,[3, 4]) := mkSlice (w:=0) m7_B m1_B m1_L (by decide +kernel)
theorem m7_S7 : SliceN false m7_R m7_T (0xf000f000f000f000f000f000f000f,4,[0, 1, 4]) := mkSlice (w:=0) m7_B m3_B m3_L (by decide +kernel)
theorem m7_S8 : SliceN false m7_R m7_T (0x33003300330033003300330033003300,2,[0, 2, 4]) := mkSlice (w:=8) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S9 : SliceN false m7_R m7_T (0x550055005500550055005500550055,4,[1, 2, 4]) := mkSlice (w:=0) m7_B m3_B m3_L (by decide +kernel)
theorem m7_S10 : SliceN false m7_R m7_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S11 : SliceN false m7_R m7_T (0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]) := mkSlice (w:=2) m7_B m6_B m6_L (by decide +kernel)
theorem m7_S12 : SliceN false m7_R m7_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S13 : SliceN false m7_R m7_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S14 : SliceN false m7_R m7_T (0x10101010101010101010101010101010,1,[3, 4]) := mkSlice (w:=4) m7_B m2_B m2_L (by decide +kernel)
theorem m7_S15 : SliceN false m7_R m7_T (0x3030303030303030303030303030303,4,[0, 3, 4]) := mkSlice (w:=0) m7_B m3_B m3_L (by decide +kernel)
theorem m7_S16 : SliceN false m7_R m7_T (0xaaaa0000aaaa0000aaaa0000aaaa,2,[1, 2, 3]) := mkSlice (w:=1) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S17 : SliceN false m7_R m7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,3,[0, 1, 3, 4]) := mkSlice (w:=4) m7_B m6_B m6_L (by decide +kernel)
theorem m7_S18 : SliceN false m7_R m7_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]) := mkSlice (w:=8) m7_B m6_B m6_L (by decide +kernel)
theorem m7_S19 : SliceN false m7_R m7_T (0xf000f000f000f000f000f000f000f0,2,[0, 1, 4]) := mkSlice (w:=4) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S20 : SliceN false m7_R m7_T (0x330033003300330033003300330033,4,[0, 2, 4]) := mkSlice (w:=0) m7_B m3_B m3_L (by decide +kernel)
theorem m7_S21 : SliceN false m7_R m7_T (0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]) := mkSlice (w:=8) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S22 : SliceN false m7_R m7_T (0x5050505050505050505050505050505,4,[1, 3, 4]) := mkSlice (w:=0) m7_B m3_B m3_L (by decide +kernel)
theorem m7_S23 : SliceN false m7_R m7_T (0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]) := mkSlice (w:=16) m7_B m4_B m4_L (by decide +kernel)
theorem m7_S24 : SliceN false m7_R m7_T (0x11001100110011001100110011001100,1,[2, 4]) := mkSlice (w:=8) m7_B m2_B m2_L (by decide +kernel)
def m7_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,7,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]),(0x11111111111111111111111111111111,4,[2, 3, 4]),(0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]),(0x1010101010101010101010101010101,1,[3, 4]),(0xf000f000f000f000f000f000f000f,4,[0, 1, 4]),(0x33003300330033003300330033003300,2,[0, 2, 4]),(0x550055005500550055005500550055,4,[1, 2, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0x10101010101010101010101010101010,1,[3, 4]),(0x3030303030303030303030303030303,4,[0, 3, 4]),(0xaaaa0000aaaa0000aaaa0000aaaa,2,[1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,3,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]),(0xf000f000f000f000f000f000f000f0,2,[0, 1, 4]),(0x330033003300330033003300330033,4,[0, 2, 4]),(0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]),(0x5050505050505050505050505050505,4,[1, 3, 4]),(0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]),(0x11001100110011001100110011001100,1,[2, 4])]
theorem m7_Y : ∀ s ∈ m7_Z, SliceN false m7_R m7_T s := by
  unfold m7_Z
  simp only [List.forall_mem_cons]
  exact ⟨m7_S0,m7_S1,m7_S2,m7_S3,m7_S4,m7_S5,m7_S6,m7_S7,m7_S8,m7_S9,m7_S10,m7_S11,m7_S12,m7_S13,m7_S14,m7_S15,m7_S16,m7_S17,m7_S18,m7_S19,m7_S20,m7_S21,m7_S22,m7_S23,m7_S24,by simp⟩
def m7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(4,[]),(5,[]),(3,[(1,0,1)]),(0,[(1,0,3)]),(1,[(1,0,3)]),(3,[(1,0,3),(1,1,3)]),(2,[(1,1,3),(1,0,3)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(6,[]),(5,[(1,0,1)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(7,[]),(4,[(1,0,1)]),(5,[(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(3,[(1,2,3)]),(0,[(1,0,3),(1,2,3)]),(1,[(1,0,2),(1,2,3)]),(5,[(1,0,3)]),(3,[(1,1,3)]),(2,[(1,0,2),(1,1,3)]),(8,[]),(9,[]),(0,[(1,2,3),(1,0,4)]),(0,[(1,1,3),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(3,[(1,0,1),(1,2,3)]),(1,[(1,2,3)]),(1,[(1,1,3)]),(0,[(1,0,3),(1,1,3)]),(5,[(1,0,2)]),(10,[]),(0,[(1,1,3),(1,0,4)]),(1,[(1,0,3),(1,1,3)]),(2,[(1,0,3),(1,1,3)]),(1,[(1,0,3),(1,1,4)]),(0,[(1,0,1),(1,3,4)]),(0,[(1,0,3),(1,1,4)]),(0,[(1,0,1),(1,0,2)]),(2,[(1,0,1),(1,2,4)]),(1,[(1,0,1),(1,0,2)]),(11,[]),(12,[]),(13,[]),(4,[(1,0,2)]),(14,[]),(3,[(1,0,1),(1,3,4)]),(15,[(1,0,1)]),(9,[(1,0,1)]),(3,[(1,0,1),(1,2,4)]),(3,[(1,0,2),(1,1,4)]),(2,[(1,0,2),(1,1,4)]),(0,[(1,0,1),(1,2,4)]),(0,[(1,0,2),(1,1,4)]),(16,[]),(0,[(1,1,2),(1,0,4)]),(1,[(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,2,3)]),(1,[(1,1,2),(1,1,3)]),(4,[(1,0,2),(1,1,2)]),(4,[(1,0,1),(1,1,2)]),(4,[(1,0,1),(1,0,2)]),(0,[(1,2,3),(1,1,4)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,1,2),(1,3,4)]),(3,[(1,0,2),(1,3,4)]),(2,[(1,0,2),(1,3,4)]),(17,[(1,2,3)]),(18,[(1,2,3)]),(2,[(1,0,3),(1,2,4)]),(5,[(1,0,3),(1,2,3)]),(15,[(1,1,2)]),(0,[(1,0,2),(1,1,3),(1,2,3)]),(19,[]),(20,[(1,1,2)]),(0,[(1,0,1),(1,1,3),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,1,3)]),(21,[]),(2,[(1,2,3)]),(2,[(1,2,3),(1,1,2)]),(1,[(1,2,3),(1,1,3)]),(15,[]),(0,[(1,0,2),(1,1,3),(1,4,5)]),(20,[]),(0,[(1,0,1),(1,2,3),(1,4,5)]),(1,[(1,0,1),(1,2,3),(1,3,4)]),(1,[(1,0,1),(1,1,3)]),(0,[(1,0,2),(1,1,3),(1,3,4)]),(22,[(1,0,1)]),(20,[(1,0,1)]),(1,[(1,0,1),(1,2,3),(1,1,5)]),(0,[(1,0,2),(1,0,3),(1,2,3)]),(5,[(1,0,1),(1,3,4)]),(10,[(1,1,2)]),(11,[(1,2,3)]),(23,[]),(24,[])]
def m7_t : Tabs := (m7_C.map (mkCut false m7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(17,16),(17,1),(6,4),(6,2),(10,8),(10,2),(18,16),(18,2),(12,8),(12,4),(20,16),(20,4),(24,16),(24,8)],[(12,1,8,5,4,9),(20,1,16,5,4,17),(3,4,2,5,1,6),(3,16,2,17,1,18),(12,16,8,20,4,24),(9,2,16,3,1,18),(18,1,8,3,2,9),(5,8,4,9,1,12),(6,16,4,18,2,20),(5,16,4,17,1,20),(9,16,8,17,1,24),(10,16,8,18,2,24),(3,8,2,9,1,10),(6,1,16,5,4,17),(20,2,16,3,1,18),(20,1,16,3,2,17),(3,4,1,6,2,5),(5,8,4,9,1,24),(5,16,4,17,1,24),(6,8,4,10,2,24),(6,16,4,18,2,24),(6,1,4,9,2,17),(3,16,2,20,1,24),(3,8,1,10,2,9),(5,8,16,9,1,24),(6,16,2,20,4,24)],[[],[1],[2,1],[3,2,1],[0,1],[0,2,1],[0,3,2,1],[1,0,2,1],[1,0,3,2,1],[2,1,0,3,2,1],[0,1,2,3],[0,1,2,1,3],[0,1,2,3,2,1],[1,2,3],[1,2,1,3],[1,2,3,2,1],[2],[3,2],[3],[2,3],[0,1,0,2],[0,1,2,1,0],[1,0,2],[1,2,1,0],[0],[0,2],[2,3,2],[0,1,2,1,0,3],[0,1,2,3,2,1,0],[1,2,1,0,3],[1,2,3,2,1,0],[2,1,0,3],[2,3,2,1,0],[0,2,1,3,2],[0,1,3,2],[0,1,0,2,1,3],[2,1,3,2],[1,3,2],[1,0,2,1,3],[1,0,3],[0,3,2],[0,3],[0,2,3],[1,0],[0,1,0,3],[0,1,2],[0,2,1,3],[0,1,3],[2,1,3],[1,3]])
theorem m7_W : TabsP false m7_R m7_T m7_t := ⟨cutsGood m7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def m7_D9 : List StD := [
([mw0,mw1,mw2,mw3,mw9],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003],[0,10000,30002,10004,10005],[0,10000,30003,10006,10007],[1,10002,30004,10008,10009],[1,10002,30005,10010,10011],[1,10002,30006,10012,10013],[2,10003,30007,10014,10015],[2,10003,30008,10016,10017],[3,10005,30009,10018,10019]])]
noncomputable def m7_D8 : List StD := [
([mw0,mw1,mw4,mw2,mw3,mw9],[[0],[],[0,30010,10003],[0,30011,10005],[0,30012,10007],[],[1,30013,10009],[1,30014,10011],[1,30015,10013],[4,5,2,30000,10003],[5,3,30016,10005],[5,6,30017,10007],[4,10003,30000,10014,10015],[4,10003,30018,10016,10017],[7,10005,30019,10018,10019]])]
noncomputable def m7_D7 : List StD := [
([mw0,mw1,mw2,mw3,mw10,mw11],[[8,9,30007],[8,30020,10003],[8,30021,10005],[],[8,9],[9,30022,10009],[9,30023,10011],[9,8],[],[10,10005,30007,10014,10015],[11,10009,30000,10003,30024],[11,10003,30024,10009,30000],[10,10011,30016,10005,30025],[10,10005,30025,10011,30016],[8]]),
([mw0,mw1,mw4,mw2,mw12,mw3,mw9],[[12],[],[12,4,13],[],[12,30011,10005],[12,30012,10007],[],[4,12],[],[13,30014,10011],[13,30015,10013],[4],[],[5,30000,10005],[5,30018,10007],[],[4,30019,10015],[4,30026,10017],[7,14,20000,10005],[20000,14,15,20001,10007],[10005,10007,10018,10019]]),
([mw0,mw1,mw2,mw12,mw3,mw9],[[12,13,4],[12,13],[],[12,30027,10005],[12,30028,10007],[13,12],[],[13,30029,10011],[13,30030,10013],[],[4,30031,10015],[4,30032,10017],[20002,3,10018,30000,10005],[20002,6,10019,30018,10007],[20002,10005,10007,10018,10019]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw9],[[16],[],[16,4,30033],[16,7,30034],[16,30035,30010],[16,30035,10007],[],[4,17,30036],[7,17,30037],[17,30038,30013],[17,30038,10013],[4,30019,30031],[7,30018,30039],[18,5,20002,20000,30000],[20002,19,20,20003,10007],[4],[],[4,30019,10017],[],[7,30018,10019],[20000,10007,20004,10017]])]
noncomputable def m7_D6 : List StD := [
([mw0,mw1,mw8,mw13,mw14],[[21,22,10000,30000,10001,10002],[21,10001,30000,10000,30017],[21,10001,30018,10000,30016],[21,10000,30019,10004,30000],[22,10002,30024,10008,30040],[22,10002,30041,10008,30025],[22,10002,30042,10010,30024],[20],[20],[23]]),
([mw0,mw1,mw2,mw5,mw11,mw14],[[24,25,30043],[24,30044,10003],[],[24,20005,30045],[24,26],[25,30043,10009],[25,20006,30037],[],[25,27],[10009,20005,10003,20007],[10003,20006,10009,20008],[10003,28,29,20004,10014],[20007,20008,30,20005,20006,31],[24],[25]]),
([mw0,mw1,mw4,mw2,mw3,mw13,mw14],[[32],[],[32,30046],[32,30047],[32,20009],[32,20010],[],[33,30048],[34,30049],[35,20008],[36,20011],[33,20002],[34,20012],[20012,20009],[20002,20010],[33,30000],[],[33,34],[34,33],[],[33]]),
([mw0,mw1,mw2,mw3,mw10,mw11,mw15],[[37,30038],[37,38],[37,39],[],[37,39],[],[39,20013],[39,10011],[20013,37],[],[9,20013],[10011,10015],[11],[11,40],[],[10011,39],[10015,10011],[10011,39],[37],[],[9,39]]),
([mw0,mw1,mw2,mw3,mw10,mw16],[[41,20008,30007],[20008,42,30005],[20008,10011,10005],[],[20008,0,43],[41,42,44],[41,20008,10011],[41,45],[],[42,20008,10015],[42,40],[],[20008,10011,10005],[20008,10005,10011],[20008,0,43]]),
([mw0,mw1,mw2,mw12,mw3,mw17,mw9],[[46,47],[46,48],[],[46,48],[],[46,39],[47,46],[],[48,46],[],[48,49],[],[47,30017],[47,39],[47,10017],[7,47],[47],[10019,39],[],[10017,10019],[10017,39]]),
([mw0,mw1,mw4,mw2,mw3,mw18,mw13],[[37],[],[37,20014],[37,50],[],[37,50],[],[50,20015],[41,51],[],[41,51],[52,30016],[52,50],[],[52,50],[50,53],[4,52],[],[34,50],[54,53],[52]]),
([mw0,mw1,mw2,mw3,mw19,mw9],[[55,56,10000,57],[55,56,10001,10000,58],[10000,57,59],[],[10000,56,20016,39,10007],[59,60],[56,55,57,61],[],[62,55,10007,20016,49,10013],[56,55,57,59,63],[],[59,20016,10017],[],[57,20016,10019],[20016,6,10007]])]
noncomputable def m7_D5 : List StD := [
([mw0,mw1,mw4,mw8,mw13,mw14],[[21],[],[21,20017],[21,20018],[21,20010],[],[64,20019],[65,20020],[66,20011],[67,20017],[68,20018],[69,20010],[7,70],[4,71],[7,72]]),
([mw0,mw1,mw8,mw20,mw13,mw14],[[21,10002],[21],[],[21,73],[21,74],[10002,75],[22,10002],[10002,75],[10002,76],[],[73,76],[74,75],[20,73],[20,74],[73,75]]),
([mw0,mw1,mw8,mw13,mw21],[[21,20010,10002],[21,74],[21,77],[],[20010,67,10002,76,10008],[20010,10002,10008],[20010,10008,10002],[26,78],[20010,74],[20010,74]]),
([mw0,mw7,mw6,mw13,mw14],[[79,80,81,20002,10001],[82,83,10001,20012],[10001,84,81,20009,10000],[10001,85,86,20021,10004],[82,79,87,86,81,88],[20002,79,35,89],[20002,79,90,86,81,91],[20012,82,92,81,86,93],[20012,82,89],[20009,88]]),
([mw0,mw1,mw22,mw6,mw13,mw14],[[80,20022],[],[80,20023],[80,94],[80,20024],[20024,20002],[],[94,20025],[95,96],[82,20023],[80],[97,20024],[98,99],[95,96],[97,99]]),
([mw0,mw1,mw2,mw17,mw18,mw14],[[100,101],[100,102],[],[],[100,102],[102,103],[],[],[102,103],[104,102],[86,102],[51,105],[101],[101],[92,101]])]
def m7_D4 : List StD := []
theorem m7_I4 : LevelN false m7_T 4 m7_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m7_C5x0 : levelOK false m7_T m7_t 4 (m7_D4.map Prod.fst) ((m7_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem m7_I5 : LevelN false m7_T 5 m7_D5 := levelStep m7_B m7_W m7_I4 (chunks 16 m7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m7_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m7_C6x0 : levelOK false m7_T m7_t 5 (m7_D5.map Prod.fst) ((m7_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem m7_I6 : LevelN false m7_T 6 m7_D6 := levelStep m7_B m7_W m7_I5 (chunks 16 m7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m7_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m7_C7x0 : levelOK false m7_T m7_t 6 (m7_D6.map Prod.fst) ((m7_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem m7_I7 : LevelN false m7_T 7 m7_D7 := levelStep m7_B m7_W m7_I6 (chunks 16 m7_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m7_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m7_C8x0 : levelOK false m7_T m7_t 7 (m7_D7.map Prod.fst) ((m7_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem m7_I8 : LevelN false m7_T 8 m7_D8 := levelStep m7_B m7_W m7_I7 (chunks 16 m7_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m7_C8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem m7_C9x0 : levelOK false m7_T m7_t 8 (m7_D8.map Prod.fst) ((m7_D9.drop (0*16)).take 16) = true := by decide +kernel
theorem m7_I9 : LevelN false m7_T 9 m7_D9 := levelStep m7_B m7_W m7_I8 (chunks 16 m7_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact m7_C9x0
  ))
theorem m7_L : LowN false m7_R m7_T 10 := lowSearch m7_B m7_I9 (by decide +kernel)
def m8_T : Nat := 0xfffffffefffffffefffffffefffffffe
def m8_R : List Nat := [0, 1, 2, 3, 4]
def m8_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8),(4,0,16)]
theorem m8_B : baseOK m8_T m8_R m8_E = true := by decide +kernel
theorem m8_L : LowN false m8_R m8_T 4 := lowCount m8_B (by decide +kernel)
def mtopT : Nat := 0xfffffffefffefee8fffffffefffefee8
def mtopR : List Nat := [0, 1, 2, 3, 4, 5]
def mtopE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33)]
theorem mtopB : baseOK mtopT mtopR mtopE = true := by decide +kernel
theorem mtopS0 : SliceN false mtopR mtopT (0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]) := mkSlice (w:=0) mtopB m7_B m7_L (by decide +kernel)
theorem mtopS1 : SliceN false mtopR mtopT (0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]) := mkSlice (w:=0) mtopB m7_B m7_L (by decide +kernel)
theorem mtopS2 : SliceN false mtopR mtopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]) := mkSlice (w:=0) mtopB m7_B m7_L (by decide +kernel)
theorem mtopS3 : SliceN false mtopR mtopT (0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]) := mkSlice (w:=0) mtopB m7_B m7_L (by decide +kernel)
theorem mtopS4 : SliceN false mtopR mtopT (0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]) := mkSlice (w:=0) mtopB m7_B m7_L (by decide +kernel)
theorem mtopS5 : SliceN false mtopR mtopT (0x11111111111111111111111111111111,7,[2, 3, 4, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS6 : SliceN false mtopR mtopT (0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]) := mkSlice (w:=0) mtopB m7_B m7_L (by decide +kernel)
theorem mtopS7 : SliceN false mtopR mtopT (0x1010101010101010101010101010101,4,[3, 4, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS8 : SliceN false mtopR mtopT (0xf000f000f000f000f000f000f000f,7,[0, 1, 4, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS9 : SliceN false mtopR mtopT (0x5555000055550000555500005555,7,[1, 2, 3, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS10 : SliceN false mtopR mtopT (0x333333330000000033333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS11 : SliceN false mtopR mtopT (0xf0f0f0f000000000f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS12 : SliceN false mtopR mtopT (0xff00ff0000000000ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS13 : SliceN false mtopR mtopT (0x555555550000000055555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS14 : SliceN false mtopR mtopT (0x3333000033330000333300003333,7,[0, 2, 3, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS15 : SliceN false mtopR mtopT (0x110011001100110011001100110011,4,[2, 4, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS16 : SliceN false mtopR mtopT (0x10001000100010001000100010001,1,[4, 5]) := mkSlice (w:=0) mtopB m1_B m1_L (by decide +kernel)
theorem mtopS17 : SliceN false mtopR mtopT (0xff000000ff000000ff000000ff,7,[0, 1, 2, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS18 : SliceN false mtopR mtopT (0x330033003300330033003300330033,7,[0, 2, 4, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS19 : SliceN false mtopR mtopT (0x3030303030303030303030303030303,7,[0, 3, 4, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS20 : SliceN false mtopR mtopT (0x30003000300030003000300030003,4,[0, 4, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS21 : SliceN false mtopR mtopT (0x5050505050505050505050505050505,7,[1, 3, 4, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS22 : SliceN false mtopR mtopT (0xf0000000f0000000f0000000f,4,[0, 1, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS23 : SliceN false mtopR mtopT (0xffff000000000000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS24 : SliceN false mtopR mtopT (0xf0f00000f0f00000f0f00000f0f,7,[0, 1, 3, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS25 : SliceN false mtopR mtopT (0x550055005500550055005500550055,7,[1, 2, 4, 5]) := mkSlice (w:=0) mtopB m5_B m5_L (by decide +kernel)
theorem mtopS26 : SliceN false mtopR mtopT (0xf0f00000f0f00000f0f00000f0f0000,3,[0, 1, 3, 5]) := mkSlice (w:=16) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS27 : SliceN false mtopR mtopT (0x30303030000000003030303,4,[0, 3, 4]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS28 : SliceN false mtopR mtopT (0x33330000333300003333000033330000,3,[0, 2, 3, 5]) := mkSlice (w:=16) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS29 : SliceN false mtopR mtopT (0x55555555000000005555555500000000,3,[1, 2, 3, 4]) := mkSlice (w:=32) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS30 : SliceN false mtopR mtopT (0x11111111000000001111111100000000,2,[2, 3, 4]) := mkSlice (w:=32) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS31 : SliceN false mtopR mtopT (0xa000a00000000000a000a,1,[1, 4]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS32 : SliceN false mtopR mtopT (0xc000c00000000000c000c,1,[0, 4]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS33 : SliceN false mtopR mtopT (0x100010001000100010001000100010,1,[4, 5]) := mkSlice (w:=4) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS34 : SliceN false mtopR mtopT (0xffff000000000000ffff00000000,3,[0, 1, 2, 3]) := mkSlice (w:=32) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS35 : SliceN false mtopR mtopT (0x3300330000000000330033,4,[0, 2, 4]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS36 : SliceN false mtopR mtopT (0x2200220000000000220022,1,[2, 4]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS37 : SliceN false mtopR mtopT (0x40404040000000004040404,1,[3, 4]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS38 : SliceN false mtopR mtopT (0x22222222222222222222222222222222,3,[2, 3, 4, 5]) := mkSlice (w:=1) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS39 : SliceN false mtopR mtopT (0x101010100000000010101010,1,[3, 4]) := mkSlice (w:=4) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS40 : SliceN false mtopR mtopT (0x1111000011110000111100001111,4,[2, 3, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS41 : SliceN false mtopR mtopT (0x111111110000000011111111,4,[2, 3, 4]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS42 : SliceN false mtopR mtopT (0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3, 4, 5]) := mkSlice (w:=2) mtopB m8_B m8_L (by decide +kernel)
theorem mtopS43 : SliceN false mtopR mtopT (0xaaaaaaaa00000000aaaaaaaa,3,[1, 2, 3, 4]) := mkSlice (w:=1) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS44 : SliceN false mtopR mtopT (0x1010000010100000101000001010000,1,[3, 5]) := mkSlice (w:=16) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS45 : SliceN false mtopR mtopT (0x30303030303030303030303030303030,3,[0, 3, 4, 5]) := mkSlice (w:=4) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS46 : SliceN false mtopR mtopT (0x33003300330033003300330033003300,3,[0, 2, 4, 5]) := mkSlice (w:=8) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS47 : SliceN false mtopR mtopT (0x50505050505050505050505050505050,3,[1, 3, 4, 5]) := mkSlice (w:=4) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS48 : SliceN false mtopR mtopT (0x55005500550055005500550055005500,3,[1, 2, 4, 5]) := mkSlice (w:=8) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS49 : SliceN false mtopR mtopT (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3,[1, 3, 4, 5]) := mkSlice (w:=1) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS50 : SliceN false mtopR mtopT (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,3,[0, 3, 4, 5]) := mkSlice (w:=2) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS51 : SliceN false mtopR mtopT (0x1000100010001000100010001000100,1,[4, 5]) := mkSlice (w:=8) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS52 : SliceN false mtopR mtopT (0xa0000000a0000000a0000000a,1,[1, 5]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS53 : SliceN false mtopR mtopT (0xc0000000c0000000c0000000c,1,[0, 5]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS54 : SliceN false mtopR mtopT (0xaa00000000000000aa,1,[1, 2]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS55 : SliceN false mtopR mtopT (0x55550000555500005555000055550000,3,[1, 2, 3, 5]) := mkSlice (w:=16) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS56 : SliceN false mtopR mtopT (0xcc00000000000000cc,1,[0, 2]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS57 : SliceN false mtopR mtopT (0x11001100110011001100110011001100,2,[2, 4, 5]) := mkSlice (w:=8) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS58 : SliceN false mtopR mtopT (0x11110000111100001111000011110000,2,[2, 3, 5]) := mkSlice (w:=16) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS59 : SliceN false mtopR mtopT (0x3300000000000000330000,1,[0, 2]) := mkSlice (w:=16) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS60 : SliceN false mtopR mtopT (0x30003000000000003000300000000,1,[0, 4]) := mkSlice (w:=32) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS61 : SliceN false mtopR mtopT (0xf0f0f0f000000000f0f0f0f0,3,[0, 1, 3, 4]) := mkSlice (w:=4) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS62 : SliceN false mtopR mtopT (0xff000000ff000000ff000000ff00,3,[0, 1, 2, 5]) := mkSlice (w:=8) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS63 : SliceN false mtopR mtopT (0x50005000500050005000500050005,4,[1, 4, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS64 : SliceN false mtopR mtopT (0x50000000500000005000000050000,1,[1, 5]) := mkSlice (w:=16) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS65 : SliceN false mtopR mtopT (0x55550000000000005555,4,[1, 2, 3]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS66 : SliceN false mtopR mtopT (0x22220000000000002222,1,[2, 3]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS67 : SliceN false mtopR mtopT (0x4400440000000000440044,1,[2, 4]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS68 : SliceN false mtopR mtopT (0x3300000033000000330000003300,2,[0, 2, 5]) := mkSlice (w:=8) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS69 : SliceN false mtopR mtopT (0x550000005500000055000000550000,2,[1, 2, 5]) := mkSlice (w:=16) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS70 : SliceN false mtopR mtopT (0x550055000000000055005500000000,2,[1, 2, 4]) := mkSlice (w:=32) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS71 : SliceN false mtopR mtopT (0x22000000220000002200000022,1,[2, 5]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS72 : SliceN false mtopR mtopT (0x44444444444444444444444444444444,3,[2, 3, 4, 5]) := mkSlice (w:=2) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS73 : SliceN false mtopR mtopT (0x20202020000000002020202,1,[3, 4]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS74 : SliceN false mtopR mtopT (0x4444000044440000444400004444,2,[2, 3, 5]) := mkSlice (w:=2) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS75 : SliceN false mtopR mtopT (0x404000004040000040400000404,1,[3, 5]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS76 : SliceN false mtopR mtopT (0xf000f000f000f000f000f000f000f00,3,[0, 1, 4, 5]) := mkSlice (w:=8) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS77 : SliceN false mtopR mtopT (0x33000000330000003300000033,4,[0, 2, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS78 : SliceN false mtopR mtopT (0x110000001100000011000000110000,1,[2, 5]) := mkSlice (w:=16) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS79 : SliceN false mtopR mtopT (0x44000000440000004400000044,1,[2, 5]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS80 : SliceN false mtopR mtopT (0x5050000050500000505000005050,2,[1, 3, 5]) := mkSlice (w:=4) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS81 : SliceN false mtopR mtopT (0x33333333000000003333333300000000,3,[0, 2, 3, 4]) := mkSlice (w:=32) mtopB m6_B m6_L (by decide +kernel)
theorem mtopS82 : SliceN false mtopR mtopT (0x202000002020000020200000202,1,[3, 5]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS83 : SliceN false mtopR mtopT (0xf0000000f0000000f0000000f0000,2,[0, 1, 5]) := mkSlice (w:=16) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS84 : SliceN false mtopR mtopT (0x30000000300000003000000030,1,[0, 5]) := mkSlice (w:=4) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS85 : SliceN false mtopR mtopT (0x50000000500000005000000050,1,[1, 5]) := mkSlice (w:=4) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS86 : SliceN false mtopR mtopT (0x3030000030300000303000003030000,2,[0, 3, 5]) := mkSlice (w:=16) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS87 : SliceN false mtopR mtopT (0x30003000000000003000300,1,[0, 4]) := mkSlice (w:=8) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS88 : SliceN false mtopR mtopT (0xa0a0000000000000a0a,1,[1, 3]) := mkSlice (w:=1) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS89 : SliceN false mtopR mtopT (0xc0c0000000000000c0c,1,[0, 3]) := mkSlice (w:=2) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS90 : SliceN false mtopR mtopT (0x1010000010100000101000001010,1,[3, 5]) := mkSlice (w:=4) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS91 : SliceN false mtopR mtopT (0x110011000000000011001100000000,1,[2, 4]) := mkSlice (w:=32) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS92 : SliceN false mtopR mtopT (0x300000003000000030000000300,1,[0, 5]) := mkSlice (w:=8) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS93 : SliceN false mtopR mtopT (0x5000500050005000500050005000500,2,[1, 4, 5]) := mkSlice (w:=8) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS94 : SliceN false mtopR mtopT (0x33000000000000003300000000,1,[0, 2]) := mkSlice (w:=32) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS95 : SliceN false mtopR mtopT (0x33330000000000003333,4,[0, 2, 3]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS96 : SliceN false mtopR mtopT (0x5500000055000000550000005500,2,[1, 2, 5]) := mkSlice (w:=8) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS97 : SliceN false mtopR mtopT (0xf000f00000000000f000f0,2,[0, 1, 4]) := mkSlice (w:=4) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS98 : SliceN false mtopR mtopT (0xf0000000f0000000f0000000f00,2,[0, 1, 5]) := mkSlice (w:=8) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS99 : SliceN false mtopR mtopT (0x505050500000000050505050,2,[1, 3, 4]) := mkSlice (w:=4) mtopB m4_B m4_L (by decide +kernel)
theorem mtopS100 : SliceN false mtopR mtopT (0xf000f00000000000f000f,4,[0, 1, 4]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS101 : SliceN false mtopR mtopT (0xf0f0000000000000f0f,4,[0, 1, 3]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS102 : SliceN false mtopR mtopT (0x505000005050000050500000505,4,[1, 3, 5]) := mkSlice (w:=0) mtopB m3_B m3_L (by decide +kernel)
theorem mtopS103 : SliceN false mtopR mtopT (0xf000000000000000f00,1,[0, 1]) := mkSlice (w:=8) mtopB m2_B m2_L (by decide +kernel)
theorem mtopS104 : SliceN false mtopR mtopT (0x500000005000000050000000500,1,[1, 5]) := mkSlice (w:=8) mtopB m2_B m2_L (by decide +kernel)
def mtopZ : List SliceD := [(0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]),(0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]),(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]),(0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]),(0x11111111111111111111111111111111,7,[2, 3, 4, 5]),(0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]),(0x1010101010101010101010101010101,4,[3, 4, 5]),(0xf000f000f000f000f000f000f000f,7,[0, 1, 4, 5]),(0x5555000055550000555500005555,7,[1, 2, 3, 5]),(0x333333330000000033333333,7,[0, 2, 3, 4]),(0xf0f0f0f000000000f0f0f0f,7,[0, 1, 3, 4]),(0xff00ff0000000000ff00ff,7,[0, 1, 2, 4]),(0x555555550000000055555555,7,[1, 2, 3, 4]),(0x3333000033330000333300003333,7,[0, 2, 3, 5]),(0x110011001100110011001100110011,4,[2, 4, 5]),(0x10001000100010001000100010001,1,[4, 5]),(0xff000000ff000000ff000000ff,7,[0, 1, 2, 5]),(0x330033003300330033003300330033,7,[0, 2, 4, 5]),(0x3030303030303030303030303030303,7,[0, 3, 4, 5]),(0x30003000300030003000300030003,4,[0, 4, 5]),(0x5050505050505050505050505050505,7,[1, 3, 4, 5]),(0xf0000000f0000000f0000000f,4,[0, 1, 5]),(0xffff000000000000ffff,7,[0, 1, 2, 3]),(0xf0f00000f0f00000f0f00000f0f,7,[0, 1, 3, 5]),(0x550055005500550055005500550055,7,[1, 2, 4, 5]),(0xf0f00000f0f00000f0f00000f0f0000,3,[0, 1, 3, 5]),(0x30303030000000003030303,4,[0, 3, 4]),(0x33330000333300003333000033330000,3,[0, 2, 3, 5]),(0x55555555000000005555555500000000,3,[1, 2, 3, 4]),(0x11111111000000001111111100000000,2,[2, 3, 4]),(0xa000a00000000000a000a,1,[1, 4]),(0xc000c00000000000c000c,1,[0, 4]),(0x100010001000100010001000100010,1,[4, 5]),(0xffff000000000000ffff00000000,3,[0, 1, 2, 3]),(0x3300330000000000330033,4,[0, 2, 4]),(0x2200220000000000220022,1,[2, 4]),(0x40404040000000004040404,1,[3, 4]),(0x22222222222222222222222222222222,3,[2, 3, 4, 5]),(0x101010100000000010101010,1,[3, 4]),(0x1111000011110000111100001111,4,[2, 3, 5]),(0x111111110000000011111111,4,[2, 3, 4]),(0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3, 4, 5]),(0xaaaaaaaa00000000aaaaaaaa,3,[1, 2, 3, 4]),(0x1010000010100000101000001010000,1,[3, 5]),(0x30303030303030303030303030303030,3,[0, 3, 4, 5]),(0x33003300330033003300330033003300,3,[0, 2, 4, 5]),(0x50505050505050505050505050505050,3,[1, 3, 4, 5]),(0x55005500550055005500550055005500,3,[1, 2, 4, 5]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3,[1, 3, 4, 5]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,3,[0, 3, 4, 5]),(0x1000100010001000100010001000100,1,[4, 5]),(0xa0000000a0000000a0000000a,1,[1, 5]),(0xc0000000c0000000c0000000c,1,[0, 5]),(0xaa00000000000000aa,1,[1, 2]),(0x55550000555500005555000055550000,3,[1, 2, 3, 5]),(0xcc00000000000000cc,1,[0, 2]),(0x11001100110011001100110011001100,2,[2, 4, 5]),(0x11110000111100001111000011110000,2,[2, 3, 5]),(0x3300000000000000330000,1,[0, 2]),(0x30003000000000003000300000000,1,[0, 4]),(0xf0f0f0f000000000f0f0f0f0,3,[0, 1, 3, 4]),(0xff000000ff000000ff000000ff00,3,[0, 1, 2, 5]),(0x50005000500050005000500050005,4,[1, 4, 5]),(0x50000000500000005000000050000,1,[1, 5]),(0x55550000000000005555,4,[1, 2, 3]),(0x22220000000000002222,1,[2, 3]),(0x4400440000000000440044,1,[2, 4]),(0x3300000033000000330000003300,2,[0, 2, 5]),(0x550000005500000055000000550000,2,[1, 2, 5]),(0x550055000000000055005500000000,2,[1, 2, 4]),(0x22000000220000002200000022,1,[2, 5]),(0x44444444444444444444444444444444,3,[2, 3, 4, 5]),(0x20202020000000002020202,1,[3, 4]),(0x4444000044440000444400004444,2,[2, 3, 5]),(0x404000004040000040400000404,1,[3, 5]),(0xf000f000f000f000f000f000f000f00,3,[0, 1, 4, 5]),(0x33000000330000003300000033,4,[0, 2, 5]),(0x110000001100000011000000110000,1,[2, 5]),(0x44000000440000004400000044,1,[2, 5]),(0x5050000050500000505000005050,2,[1, 3, 5]),(0x33333333000000003333333300000000,3,[0, 2, 3, 4]),(0x202000002020000020200000202,1,[3, 5]),(0xf0000000f0000000f0000000f0000,2,[0, 1, 5]),(0x30000000300000003000000030,1,[0, 5]),(0x50000000500000005000000050,1,[1, 5]),(0x3030000030300000303000003030000,2,[0, 3, 5]),(0x30003000000000003000300,1,[0, 4]),(0xa0a0000000000000a0a,1,[1, 3]),(0xc0c0000000000000c0c,1,[0, 3]),(0x1010000010100000101000001010,1,[3, 5]),(0x110011000000000011001100000000,1,[2, 4]),(0x300000003000000030000000300,1,[0, 5]),(0x5000500050005000500050005000500,2,[1, 4, 5]),(0x33000000000000003300000000,1,[0, 2]),(0x33330000000000003333,4,[0, 2, 3]),(0x5500000055000000550000005500,2,[1, 2, 5]),(0xf000f00000000000f000f0,2,[0, 1, 4]),(0xf0000000f0000000f0000000f00,2,[0, 1, 5]),(0x505050500000000050505050,2,[1, 3, 4]),(0xf000f00000000000f000f,4,[0, 1, 4]),(0xf0f0000000000000f0f,4,[0, 1, 3]),(0x505000005050000050500000505,4,[1, 3, 5]),(0xf000000000000000f00,1,[0, 1]),(0x500000005000000050000000500,1,[1, 5])]
theorem mtopY : ∀ s ∈ mtopZ, SliceN false mtopR mtopT s := by
  unfold mtopZ
  simp only [List.forall_mem_cons]
  exact ⟨mtopS0,mtopS1,mtopS2,mtopS3,mtopS4,mtopS5,mtopS6,mtopS7,mtopS8,mtopS9,mtopS10,mtopS11,mtopS12,mtopS13,mtopS14,mtopS15,mtopS16,mtopS17,mtopS18,mtopS19,mtopS20,mtopS21,mtopS22,mtopS23,mtopS24,mtopS25,mtopS26,mtopS27,mtopS28,mtopS29,mtopS30,mtopS31,mtopS32,mtopS33,mtopS34,mtopS35,mtopS36,mtopS37,mtopS38,mtopS39,mtopS40,mtopS41,mtopS42,mtopS43,mtopS44,mtopS45,mtopS46,mtopS47,mtopS48,mtopS49,mtopS50,mtopS51,mtopS52,mtopS53,mtopS54,mtopS55,mtopS56,mtopS57,mtopS58,mtopS59,mtopS60,mtopS61,mtopS62,mtopS63,mtopS64,mtopS65,mtopS66,mtopS67,mtopS68,mtopS69,mtopS70,mtopS71,mtopS72,mtopS73,mtopS74,mtopS75,mtopS76,mtopS77,mtopS78,mtopS79,mtopS80,mtopS81,mtopS82,mtopS83,mtopS84,mtopS85,mtopS86,mtopS87,mtopS88,mtopS89,mtopS90,mtopS91,mtopS92,mtopS93,mtopS94,mtopS95,mtopS96,mtopS97,mtopS98,mtopS99,mtopS100,mtopS101,mtopS102,mtopS103,mtopS104,by simp⟩
def mtopC : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[(1,0,1)]),(5,[]),(6,[]),(4,[(1,0,1)]),(6,[(1,0,1)]),(0,[(1,0,4)]),(1,[(1,0,4)]),(3,[(1,0,4),(1,1,4)]),(4,[(1,0,4),(1,1,4)]),(2,[(1,1,4),(1,0,4)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(3,[(1,0,1),(1,2,5)]),(7,[]),(3,[(1,0,1)]),(6,[(1,0,1),(1,2,5)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(5,[(1,0,1)]),(8,[]),(4,[(1,2,3)]),(6,[(1,2,3)]),(4,[(1,0,1),(1,2,3)]),(6,[(1,0,1),(1,2,3)]),(0,[(1,2,3),(1,2,4),(1,3,4)]),(1,[(1,2,3),(1,2,4),(1,3,4)]),(2,[(1,2,4),(1,3,4),(1,2,3)]),(4,[(1,3,4)]),(6,[(1,3,4)]),(0,[(1,0,4),(1,3,4)]),(1,[(1,0,3),(1,3,4)]),(6,[(1,0,4)]),(4,[(1,1,4)]),(2,[(1,0,3),(1,1,4),(1,3,4)]),(3,[(1,1,4),(1,3,4),(1,0,3)]),(9,[(1,0,3)]),(10,[]),(1,[(1,3,4),(1,0,5)]),(0,[(1,3,4),(1,0,5)]),(0,[(1,1,4),(1,2,4)]),(2,[(1,0,1),(1,2,4)]),(3,[(1,0,1),(1,2,4)]),(1,[(1,1,4),(1,2,4)]),(4,[(1,2,4),(1,3,4),(1,0,1)]),(5,[(1,0,3),(1,1,3)]),(4,[(1,2,4),(1,3,4)]),(11,[]),(12,[]),(0,[(1,0,4),(1,1,4)]),(1,[(1,0,4),(1,1,5)]),(2,[(1,0,4),(1,1,4)]),(6,[(1,0,2)]),(4,[(1,0,4),(1,1,4),(1,2,5)]),(3,[(1,1,4),(1,0,4),(1,2,6)]),(13,[]),(1,[(1,0,4),(1,1,4)]),(5,[(1,0,3)]),(2,[(1,0,4),(1,1,5)]),(0,[(1,0,1),(1,4,5)]),(0,[(1,0,4),(1,1,5)]),(0,[(1,1,4),(1,0,5)]),(13,[(1,0,1)]),(8,[(1,1,3)]),(8,[(1,0,3)]),(14,[(1,1,3)]),(4,[(1,0,4)]),(0,[(1,0,1),(1,0,2)]),(2,[(1,0,1),(1,2,5)]),(1,[(1,0,1),(1,0,2)]),(14,[(1,0,2)]),(13,[(1,0,2)]),(15,[]),(14,[(1,0,1)]),(2,[(1,0,1),(1,4,5)]),(3,[(1,0,1),(1,4,5),(1,2,4)]),(4,[(1,0,1),(1,2,4),(1,4,5)]),(0,[(1,0,1),(1,2,5)]),(1,[(1,0,1),(1,2,5)]),(4,[(1,0,1),(1,2,5)]),(16,[]),(1,[(1,0,2),(1,1,5)]),(0,[(1,0,2),(1,1,5)]),(0,[(1,0,1),(1,2,3)]),(1,[(1,0,1),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(5,[(1,1,2)]),(17,[(1,0,1)]),(6,[(1,0,1),(1,3,4)]),(7,[(1,0,1)]),(2,[(1,1,2),(0,0,1)]),(2,[(1,1,2),(0,0,5)]),(18,[]),(3,[(1,1,2),(0,0,5)]),(19,[]),(1,[(1,1,2),(0,0,5)]),(20,[]),(8,[(1,0,1)]),(19,[(1,0,1)]),(21,[(1,0,1)]),(2,[(1,0,2),(1,1,5)]),(0,[(1,1,2),(1,0,5)]),(14,[]),(2,[(1,2,3),(0,0,1)]),(14,[(1,1,2)]),(3,[(1,2,3),(0,0,1)]),(19,[(1,1,2)]),(21,[(1,1,2)]),(3,[(1,0,1),(1,2,3)]),(22,[]),(11,[(1,2,3)]),(13,[(1,1,2)]),(0,[(1,1,2),(1,3,4)]),(2,[(1,0,1),(1,3,4)]),(3,[(1,0,1),(1,3,4)]),(1,[(1,1,2),(1,3,4)]),(8,[(1,2,3)]),(5,[(1,2,3)]),(2,[(1,0,1),(1,2,3),(1,2,4),(1,3,4)]),(5,[(1,1,2),(1,1,3),(1,2,3)]),(2,[(1,2,3),(1,2,4),(1,3,4)]),(17,[]),(23,[]),(4,[(1,0,1),(1,3,4)]),(2,[(1,2,3),(1,0,5),(1,2,4),(1,3,4)]),(1,[(1,2,4),(1,3,4),(1,2,3),(1,0,7)]),(4,[(1,0,3),(1,3,4)]),(6,[(1,3,4),(1,0,5)]),(3,[(1,0,3),(1,4,5)]),(3,[(1,0,4),(1,3,5)]),(17,[(1,0,3)]),(5,[(1,1,3),(1,2,3)]),(12,[(1,0,3)]),(5,[(1,1,2),(1,2,3)]),(5,[(1,1,2),(1,1,3)]),(21,[(1,1,3),(1,2,3)]),(21,[(1,1,2),(1,2,3)]),(21,[(1,1,2),(1,1,3)]),(4,[(1,0,4),(1,3,4)]),(0,[(1,1,2),(1,1,3),(1,2,4),(1,3,4)]),(1,[(1,1,2),(1,1,3),(1,2,4),(1,3,4)]),(4,[(1,3,4),(1,2,3)]),(12,[(1,2,3)]),(6,[(1,2,4),(1,2,3)]),(4,[(1,3,4),(1,2,5)]),(3,[(1,2,3),(1,4,5)]),(24,[]),(3,[(1,3,4),(1,2,5)]),(4,[(1,2,3),(1,4,5)]),(0,[(1,0,3),(1,2,4),(1,3,4)]),(1,[(1,0,2),(1,2,4),(1,3,4)]),(6,[(1,0,3),(1,1,4)]),(2,[(1,1,3),(1,2,4),(1,3,4),(1,0,2)]),(14,[(1,2,3),(1,0,2)]),(25,[(1,2,3)]),(23,[(1,0,3)]),(25,[(1,0,2)]),(4,[(1,3,4),(1,0,5)]),(0,[(1,0,3),(1,2,4),(1,3,6)]),(3,[(1,3,4),(1,1,5)]),(1,[(1,0,2),(1,3,4),(1,2,6)]),(4,[(1,0,3),(1,4,5)]),(1,[(1,0,2),(1,2,3),(1,4,5),(1,3,4)]),(0,[(1,1,3),(1,2,4),(1,3,4)]),(2,[(1,0,1),(1,2,4),(1,3,4)]),(3,[(1,0,1),(1,2,3),(1,3,4)]),(1,[(1,1,3),(1,2,4),(1,3,4)]),(24,[(1,2,3)]),(5,[(1,0,2),(1,2,3)]),(5,[(1,0,2),(1,1,3)]),(6,[(1,0,1),(1,2,4)]),(24,[(1,0,1)]),(3,[(1,0,1),(1,3,4),(1,2,6)]),(0,[(1,0,3),(1,1,4),(1,3,4)]),(4,[(1,0,1),(1,2,4)]),(2,[(1,0,3),(1,1,5),(1,3,4)]),(6,[(1,0,4),(1,1,5)]),(1,[(1,0,3),(1,1,4),(1,3,4)]),(26,[]),(0,[(1,0,3),(1,1,4),(1,4,5)]),(9,[(1,1,3)]),(3,[(1,0,3),(1,2,4),(1,3,4)]),(3,[(1,0,3),(1,1,5),(1,2,4)]),(0,[(1,0,3),(1,3,4),(1,1,6)]),(11,[(1,0,3)]),(5,[(1,0,3),(1,2,3)]),(23,[(1,1,2)]),(1,[(1,0,3),(1,1,4),(1,4,5)]),(0,[(1,3,4),(1,0,1),(1,4,6)]),(4,[(1,1,4),(1,2,5)]),(4,[(1,2,4),(1,1,5)]),(12,[(1,1,2)]),(3,[(1,0,3),(1,3,4)]),(8,[(1,0,2),(1,1,3)]),(27,[]),(9,[]),(0,[(1,0,4),(1,3,4),(1,1,6)]),(1,[(1,0,3),(1,3,4),(1,1,6)]),(6,[(1,0,4),(1,2,4)]),(28,[]),(6,[(1,0,4),(1,2,5)]),(4,[(1,1,4),(1,2,4)]),(29,[]),(6,[(1,2,4),(1,0,5)]),(3,[(1,1,4),(1,3,4),(1,2,6)]),(3,[(1,0,3),(1,3,4),(1,2,6)]),(3,[(1,0,3),(1,1,4),(1,3,4)]),(0,[(1,3,4),(1,1,5),(1,0,5)]),(9,[(1,0,3),(1,1,3)]),(2,[(1,0,3),(1,1,4),(1,4,5)]),(2,[(1,0,3),(1,1,4),(1,3,6)]),(0,[(1,0,4),(1,1,3),(1,4,6)]),(1,[(1,0,3),(1,1,4),(1,3,6)]),(8,[(1,0,2),(1,2,3)]),(3,[(1,0,3),(1,1,4)]),(0,[(1,0,4),(1,3,4),(1,0,6)]),(4,[(1,1,4),(1,0,5)]),(1,[(1,0,3),(1,4,5),(1,3,4)]),(21,[(1,2,3),(1,0,4)]),(2,[(1,0,3),(1,1,4),(1,5,6)]),(25,[(1,2,3),(1,0,4)]),(3,[(1,0,3),(1,1,4),(1,5,6)]),(0,[(1,0,3),(1,1,4),(1,2,4)]),(1,[(1,0,3),(1,1,4),(1,2,4)]),(2,[(1,0,3),(1,1,3),(1,2,4)]),(3,[(1,0,3),(1,1,3),(1,2,4)]),(9,[(1,2,3)]),(2,[(1,0,3),(1,1,3),(1,4,5)]),(4,[(1,0,4),(1,2,5)]),(3,[(1,0,3),(1,2,4),(1,4,5)]),(3,[(1,0,3),(1,1,3),(1,4,5)]),(2,[(1,0,1),(1,3,5),(1,3,4)]),(3,[(1,0,1),(1,2,4),(1,3,4)]),(3,[(1,0,1),(1,3,5),(1,2,4)]),(30,[]),(11,[(1,0,1)]),(2,[(1,0,1),(1,3,4),(1,5,6)]),(0,[(1,0,1),(1,2,4),(1,3,4)]),(1,[(1,0,1),(1,2,4),(1,3,4)]),(12,[(1,0,1)]),(23,[(1,0,1)]),(3,[(1,0,1),(1,2,5),(1,3,4)]),(0,[(1,0,1),(1,2,4),(1,3,6)]),(3,[(1,3,4),(1,0,2),(1,1,6)]),(9,[(1,0,1)]),(0,[(1,1,4),(1,0,5),(1,2,4)]),(31,[]),(1,[(1,1,4),(1,0,5),(1,2,4)]),(32,[]),(2,[(1,0,1),(1,4,5),(1,2,4)]),(33,[]),(2,[(1,0,1),(1,2,4),(1,5,6)]),(2,[(1,0,4),(1,1,4),(1,2,5)]),(6,[(1,0,2),(1,3,5)]),(6,[(1,0,3),(1,2,5)]),(2,[(1,0,4),(1,2,5),(1,1,5)]),(3,[(1,0,4),(1,1,4),(1,2,5)]),(1,[(1,1,4),(1,0,2),(1,4,6)]),(0,[(1,1,4),(1,0,2),(1,4,6)]),(3,[(1,0,1),(1,2,4),(1,4,5)]),(3,[(1,0,1),(1,2,4),(1,5,6)]),(19,[(1,0,3),(1,1,3)]),(11,[(1,1,2)]),(18,[(1,0,3),(1,1,3)]),(1,[(1,0,4),(1,1,2),(1,4,6)]),(0,[(1,1,4),(1,2,4),(1,3,5)]),(1,[(1,1,4),(1,2,4),(1,3,5)]),(3,[(1,0,1),(1,2,4),(1,3,6)]),(2,[(1,0,1),(1,3,4),(1,2,6)]),(18,[(1,1,3),(1,2,3)]),(9,[(1,1,3),(1,2,3)]),(11,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(1,2,4),(1,3,4)]),(0,[(1,1,4),(1,2,3),(1,4,6)]),(2,[(1,0,1),(1,2,4),(1,3,6)]),(1,[(1,0,4),(1,1,4),(1,2,4)]),(2,[(1,0,4),(1,1,4),(1,2,6)]),(3,[(1,0,4),(1,1,4),(1,2,6)]),(34,[]),(5,[(1,1,3)]),(1,[(1,0,4),(1,2,4),(1,1,5)]),(35,[]),(1,[(1,0,4),(1,1,4),(1,2,5)]),(6,[(1,1,2),(1,1,3)]),(0,[(1,0,4),(1,1,5),(1,2,5)]),(1,[(1,1,4),(1,2,4),(1,0,5)]),(1,[(1,1,4),(1,2,4),(1,0,6)]),(14,[(1,1,3),(1,2,3)]),(14,[(1,0,3),(1,2,3)]),(14,[(1,0,3),(1,1,3)]),(0,[(1,0,4),(1,1,4),(1,2,5)]),(6,[(1,0,2),(1,1,3)]),(36,[]),(1,[(1,0,4),(1,1,5),(1,2,4)]),(1,[(1,0,4),(1,1,5),(1,2,5)]),(37,[]),(0,[(1,0,4),(1,2,5),(1,1,5)]),(2,[(1,1,4),(1,0,4),(1,2,5)]),(3,[(1,0,4),(1,2,5),(1,1,4)]),(18,[(1,0,3)]),(2,[(1,0,4),(1,1,5),(1,2,4)]),(3,[(1,0,4),(1,1,5),(1,2,4)]),(2,[(1,0,4),(1,1,5),(1,2,5)]),(0,[(1,0,4),(1,1,4),(1,2,6)]),(0,[(1,0,4),(1,2,4),(1,1,6)]),(38,[]),(39,[]),(0,[(1,1,4),(1,2,5),(1,0,5)]),(21,[(1,1,3)]),(13,[(1,0,3)]),(0,[(1,0,4),(1,3,5)]),(2,[(1,0,1),(1,0,4),(1,2,4)]),(3,[(1,0,1),(1,0,4),(1,2,4)]),(2,[(1,0,1),(1,0,4),(1,2,6)]),(2,[(1,0,1),(1,2,4),(1,4,5)]),(0,[(1,1,4),(1,2,5)]),(2,[(1,0,2),(1,1,2),(0,0,1)]),(2,[(1,0,2),(1,1,2),(0,0,6)]),(2,[(1,0,4),(1,1,4),(1,0,6)]),(13,[(1,2,3)]),(2,[(0,0,1)]),(18,[(1,1,3),(1,2,4)]),(2,[(0,0,1),(1,2,4),(1,3,6)]),(2,[(0,0,1),(1,3,4),(1,2,6)]),(2,[(1,2,4),(1,0,1),(1,4,6)]),(25,[(1,0,3),(1,1,3)]),(0,[(1,0,4),(1,1,2),(1,4,6)]),(2,[(1,1,2),(1,2,3),(0,0,1)]),(5,[(1,0,1),(1,1,2)]),(2,[(1,1,2),(1,2,3),(0,0,5)]),(25,[(1,0,1)]),(9,[(1,0,2),(1,1,4)]),(9,[(1,1,2),(1,0,4)]),(5,[(1,1,2),(1,0,4)]),(13,[(1,0,1),(1,2,4)]),(1,[(1,0,4),(1,1,4),(1,2,6)]),(0,[(1,0,1),(1,4,5),(1,2,6)]),(0,[(1,0,4),(1,1,5),(1,2,6)]),(0,[(1,1,4),(1,0,5),(1,2,6)]),(0,[(1,0,3),(1,0,4),(1,3,4)]),(6,[(1,0,1),(1,4,5)]),(1,[(1,0,3),(1,0,4),(1,3,6)]),(0,[(1,0,3),(1,0,4),(1,3,6)]),(40,[]),(19,[(1,0,3),(1,2,3)]),(41,[]),(19,[(1,0,2),(1,2,3)]),(19,[(1,0,2),(1,0,3)]),(18,[(1,0,3),(1,2,3)]),(18,[(1,0,2),(1,2,3)]),(18,[(1,0,2),(1,0,3)]),(0,[(1,0,1),(1,0,4),(1,2,4)]),(1,[(1,0,1),(1,0,4),(1,2,4)]),(1,[(1,0,1),(1,0,4),(1,2,6)]),(0,[(1,0,1),(1,0,4),(1,2,6)]),(7,[(1,0,2)]),(9,[(1,0,3),(1,2,3)]),(2,[(1,0,1),(1,4,5),(1,2,6)]),(18,[(1,0,1)]),(9,[(1,0,1),(1,2,3)]),(9,[(1,0,1),(1,0,3)]),(0,[(1,0,1),(1,0,2),(1,3,5)]),(2,[(1,0,1),(1,2,5),(1,3,5)]),(1,[(1,0,1),(1,0,2),(1,3,5)]),(42,[]),(5,[(1,0,2)]),(18,[(1,0,1),(1,0,2)]),(3,[(1,0,1),(1,2,5),(1,3,5)]),(1,[(1,0,1),(1,0,2),(1,3,6)]),(1,[(1,0,1),(1,0,3),(1,2,6)]),(0,[(1,0,1),(1,0,2),(1,3,6)]),(0,[(1,0,1),(1,0,3),(1,2,6)]),(2,[(1,0,1),(1,2,5),(1,3,6)]),(9,[(1,0,2)]),(2,[(1,0,1),(1,3,5),(1,2,6)]),(43,[]),(44,[]),(18,[(1,1,2),(1,1,3)]),(9,[(1,1,2),(1,3,4)]),(45,[]),(46,[]),(13,[(1,1,2),(1,3,4)]),(47,[]),(48,[]),(2,[(1,0,1),(1,2,3),(1,2,4)]),(3,[(1,0,1),(1,2,3),(1,2,4)]),(4,[(1,0,1),(1,2,3),(1,4,6)]),(6,[(1,0,1),(1,2,3),(1,4,6)]),(9,[(1,1,2)]),(18,[(1,1,3)]),(18,[(1,1,2)]),(10,[(1,0,3)]),(18,[(1,0,2),(1,3,4)]),(0,[(1,1,2),(1,0,4),(1,3,4)]),(1,[(1,1,2),(1,0,4),(1,3,6)]),(1,[(1,1,2),(1,0,4),(1,3,4)]),(0,[(1,1,2),(1,0,4),(1,3,6)]),(5,[(1,0,1),(1,2,3)]),(2,[(1,0,1),(1,4,5),(1,3,4)]),(3,[(1,0,1),(1,4,5),(1,3,4)]),(49,[]),(50,[]),(5,[(1,1,3),(1,0,4)]),(5,[(1,0,3),(1,1,4)]),(5,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,2,5),(1,3,5)]),(0,[(1,0,1),(1,2,5),(1,3,5)]),(3,[(1,0,1),(1,2,5),(1,3,6)]),(0,[(1,0,1),(1,4,5),(1,2,4)]),(1,[(1,0,1),(1,4,5),(1,2,4)]),(51,[]),(4,[(1,0,1),(1,2,5),(1,3,4)]),(2,[(1,0,1),(1,2,5),(0,0,1)]),(3,[(1,0,1),(1,2,5),(0,0,1)]),(4,[(0,0,1),(1,0,1)]),(8,[(1,0,1),(1,2,4)]),(40,[(1,0,1)]),(5,[(1,0,1),(1,2,4)]),(52,[]),(53,[]),(3,[(1,0,1),(1,2,5),(1,2,3)]),(4,[(1,0,1),(1,2,3),(1,5,6)]),(2,[(1,0,1),(1,2,5),(1,2,3)]),(0,[(1,1,2),(1,0,4),(1,4,5)]),(1,[(1,1,2),(1,0,4),(1,5,6)]),(5,[(1,0,1),(1,3,4)]),(0,[(1,1,2),(1,0,4),(1,5,6)]),(1,[(1,1,2),(1,0,3),(1,5,6)]),(0,[(1,1,2),(1,0,3),(1,5,6)]),(2,[(1,0,1),(1,2,3),(1,5,6)]),(17,[(1,0,2)]),(24,[(1,0,2)]),(8,[(1,0,2)]),(0,[(1,1,2),(1,3,5),(0,0,6)]),(19,[(1,0,3)]),(3,[(1,1,2),(1,0,5)]),(8,[(1,1,2)]),(3,[(1,1,2),(0,0,5),(1,3,5)]),(5,[(1,0,2),(1,1,4)]),(19,[(1,0,1),(1,0,2)]),(9,[(1,0,1),(1,2,4)]),(3,[(1,0,2),(1,1,5),(1,3,6)]),(3,[(1,0,1),(1,2,5),(1,4,6)]),(3,[(1,0,2),(1,1,5),(1,4,6)]),(8,[(1,0,1),(1,3,4)]),(0,[(1,0,1),(1,2,4),(1,5,6)]),(18,[(1,0,1),(1,2,4)]),(3,[(1,1,2),(1,0,5),(1,3,6)]),(3,[(1,0,1),(1,0,2),(1,3,6)]),(2,[(1,0,1),(1,0,2),(1,3,6)]),(25,[(1,1,2)]),(3,[(1,0,1),(1,0,3),(1,2,6)]),(0,[(1,2,3),(1,1,5)]),(24,[(1,1,2)]),(8,[(1,1,2),(0,0,4)]),(2,[(1,0,2),(1,1,5),(1,3,6)]),(0,[(1,0,1),(1,2,5),(1,3,6)]),(0,[(1,0,2),(1,1,5),(1,3,6)]),(0,[(1,1,2),(1,0,5),(1,3,6)]),(23,[(1,2,3)]),(17,[(0,0,1),(1,2,3)]),(24,[(0,0,1),(1,2,3)]),(8,[(0,0,1),(1,2,3)]),(3,[(0,0,1),(1,2,3),(1,4,6)]),(3,[(0,0,1),(1,2,4),(1,3,6)]),(13,[(1,2,3),(1,1,4)]),(3,[(0,0,1),(1,3,4),(1,2,6)]),(17,[(1,0,1),(1,2,3)]),(24,[(1,0,1),(1,2,3)]),(3,[(1,0,1),(1,2,3),(1,4,6)]),(2,[(1,0,1),(1,2,3),(1,4,6)]),(2,[(1,2,4),(0,0,1),(1,4,6)]),(2,[(1,2,4),(1,0,4)]),(2,[(1,2,4),(1,1,4)]),(0,[(1,2,4),(1,1,5)]),(18,[(1,2,3)]),(54,[]),(10,[(1,2,3)]),(0,[(0,0,1)]),(2,[(1,0,1),(1,2,3),(0,0,1)]),(4,[(1,0,1),(1,2,3),(0,0,1)]),(22,[(0,0,1)]),(18,[(1,0,1),(1,2,3)]),(13,[(1,0,1),(1,2,3)]),(3,[(1,3,4),(1,0,1),(1,2,6)]),(3,[(1,3,4),(1,1,2),(1,0,6)]),(0,[(1,0,1),(1,2,3),(1,4,6)]),(0,[(1,0,1),(1,2,3),(1,2,4),(1,3,4)]),(1,[(1,0,1),(1,2,3),(1,2,4),(1,3,4)]),(17,[(1,1,2)]),(7,[(1,0,2),(1,1,2)]),(7,[(1,0,1),(1,1,2)]),(7,[(1,0,1),(1,0,2)]),(12,[(1,0,2)]),(23,[(1,0,2)]),(17,[(1,0,2),(1,1,2)]),(0,[(1,0,1),(1,3,4),(1,2,4),(1,2,6)]),(0,[(1,0,1),(1,3,4),(1,2,3),(1,2,6)]),(0,[(1,0,1),(1,2,4),(1,2,3),(1,3,6)]),(23,[(1,0,2),(1,1,2)]),(3,[(1,0,2),(1,1,2)]),(0,[(1,2,3),(1,1,5),(1,2,4),(1,3,4)]),(21,[(1,1,2),(1,1,3),(1,2,3)]),(18,[(1,1,2),(1,2,3)]),(1,[(1,2,3),(1,1,5),(1,2,4),(1,3,4)]),(1,[(1,0,1),(1,2,3),(1,1,6),(1,3,4)]),(18,[(1,0,1),(1,1,2)]),(55,[(1,2,3)]),(48,[(1,2,3)]),(3,[(1,0,2),(1,2,3),(1,3,4)]),(3,[(1,0,2),(1,3,4),(1,2,6)]),(13,[(1,2,3),(1,1,3)]),(0,[(1,2,3),(1,2,4)]),(4,[(1,0,2),(1,3,4),(1,4,5)]),(10,[(1,2,3),(1,1,3)]),(10,[(1,0,1),(1,1,3)]),(19,[(1,1,2),(1,2,3)]),(17,[(1,2,3)]),(17,[(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,3,4),(1,2,6)]),(0,[(1,2,3),(1,0,5),(1,2,4),(1,3,4)]),(1,[(1,2,3),(1,0,5),(1,2,4),(1,3,4)]),(56,[]),(57,[(1,1,2)]),(58,[(1,1,2)]),(3,[(1,3,4),(1,0,3),(1,1,6)]),(46,[(1,2,3)]),(55,[]),(5,[(1,2,3),(1,1,3),(1,1,4)]),(5,[(1,2,3),(1,1,2),(1,1,4)]),(10,[(1,2,3),(1,0,3)]),(13,[(1,2,3),(1,0,3)]),(4,[(1,3,4),(1,0,1),(1,4,6)]),(2,[(1,2,3),(1,2,4)]),(5,[(1,1,2),(1,0,4),(1,2,3)]),(5,[(1,1,2),(1,0,4),(1,1,3)]),(2,[(1,0,1),(1,2,3),(1,3,4),(1,2,7)]),(2,[(1,0,1),(1,2,3),(1,2,4),(1,3,7)]),(13,[(1,1,3)]),(10,[(1,1,3)]),(0,[(1,2,3),(1,2,4),(1,3,4),(1,0,7)]),(1,[(1,2,3),(1,2,4),(1,3,4),(1,0,7)]),(26,[(1,2,3)]),(6,[(1,0,4),(1,1,4),(1,3,5)]),(4,[(1,0,4),(1,1,4),(1,3,5)]),(6,[(1,0,4),(1,1,4),(1,3,6)]),(4,[(1,0,4),(1,1,4),(1,3,6)]),(21,[(1,1,3),(1,2,3),(1,0,5)]),(19,[(1,1,2),(1,1,3),(1,2,3)]),(0,[(1,3,4),(1,0,5),(1,2,5)]),(17,[(1,1,3)]),(4,[(1,3,4),(1,1,4),(1,0,5)]),(4,[(1,3,4),(1,0,4),(1,1,5)]),(4,[(1,0,3),(1,1,5),(1,4,5)]),(3,[(1,0,3),(1,1,5),(1,4,5)]),(0,[(1,2,3),(1,2,4),(1,0,6),(1,3,4)]),(3,[(1,0,3),(1,1,4),(1,4,5)]),(59,[]),(3,[(1,0,3),(1,3,4),(1,1,6)]),(3,[(1,1,4),(1,3,4),(1,0,6)]),(4,[(1,0,3),(1,1,4),(1,4,5)]),(3,[(1,0,3),(1,1,3),(1,4,6)]),(19,[(1,1,2),(1,0,4),(1,2,3)]),(4,[(1,1,4),(1,3,4),(1,0,6)]),(10,[(1,2,3),(1,0,2)]),(9,[(1,2,3),(1,0,3)]),(17,[(1,0,3),(1,1,3)]),(4,[(1,1,4),(1,0,3),(1,4,6)]),(3,[(1,0,4),(1,1,3),(1,4,6)]),(11,[(1,0,2),(1,1,3)]),(25,[]),(10,[(1,1,2)]),(5,[(1,0,1),(1,0,3),(1,1,3)]),(19,[(1,1,3)]),(25,[(1,0,1),(1,1,3)]),(60,[]),(13,[(1,0,2),(1,1,4)]),(17,[(1,1,2),(0,0,4)]),(3,[(1,0,3),(1,4,5),(1,1,6)]),(3,[(1,0,4),(1,3,5),(1,1,6)]),(17,[(1,0,3),(1,1,4)]),(0,[(1,3,4),(1,0,5),(1,2,4),(1,2,5)]),(1,[(1,1,3),(1,2,4),(1,3,4),(1,1,2)]),(5,[(1,0,2),(1,1,3),(1,2,3)]),(5,[(1,0,1),(1,1,3),(1,2,3)]),(5,[(1,0,1),(1,0,2),(1,2,3)]),(5,[(1,0,1),(1,0,2),(1,1,3)]),(3,[(1,0,1),(1,3,4),(1,2,3)]),(8,[(1,0,1),(1,2,3)]),(0,[(1,1,3),(1,3,4),(1,2,4),(1,1,7)]),(0,[(1,1,3),(1,3,4),(1,1,2),(1,4,7)]),(0,[(1,1,3),(1,2,4),(1,3,4),(1,5,6)]),(0,[(1,1,3),(1,2,4),(1,1,2),(1,5,6)]),(0,[(1,1,2),(1,3,4),(1,2,4),(1,5,6)]),(0,[(1,1,2),(1,3,4),(1,1,3),(1,5,6)]),(0,[(1,1,2),(1,2,4),(1,3,4),(1,1,7)]),(0,[(1,1,2),(1,2,4),(1,1,3),(1,4,7)]),(61,[]),(3,[(1,0,2),(1,3,4),(1,3,5)]),(62,[]),(2,[(1,0,2),(1,3,4),(1,4,5)]),(63,[(1,1,2)]),(10,[(1,1,2),(1,1,3)]),(10,[(1,1,2),(1,0,4)]),(64,[]),(3,[(1,0,2),(1,3,4),(1,2,3)]),(2,[(1,0,2),(1,3,4),(1,2,4)]),(0,[(1,1,2),(1,1,3),(1,2,4),(1,6,7)]),(3,[(1,3,4),(1,2,3),(1,0,6)]),(21,[(1,2,3)]),(2,[(1,3,4),(1,2,4),(1,0,6)]),(2,[(1,2,4),(1,0,3),(1,4,6)]),(3,[(1,2,3),(1,0,4),(1,3,6)]),(10,[(1,1,3),(1,0,3)]),(10,[(1,1,2),(1,0,3)]),(65,[]),(24,[(1,0,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,4),(1,3,4),(1,5,8)]),(0,[(1,1,2),(1,1,3),(1,2,4),(1,3,4),(1,5,8)]),(0,[(1,0,2),(1,1,3),(1,2,4),(1,3,4),(1,0,1)]),(19,[(1,1,3),(1,2,3)]),(0,[(1,0,2),(1,1,3),(1,2,4),(1,3,4)]),(0,[(1,0,1),(1,1,3),(1,2,4),(1,3,4)]),(3,[(1,2,3),(1,3,4)]),(3,[(1,2,3),(1,3,4),(1,1,2)]),(24,[(1,1,2),(1,2,3)]),(1,[(1,2,4),(1,3,4),(1,1,3)]),(6,[(1,1,3),(1,2,4),(1,2,5)]),(2,[(1,1,2),(1,3,4),(1,4,5)]),(23,[(1,1,3)]),(6,[(1,1,3),(1,2,4),(1,1,6)]),(1,[(1,1,3),(1,2,4),(1,4,5)]),(4,[(1,1,2),(1,3,4),(1,3,5)]),(3,[(1,1,2),(1,3,4),(1,3,5)]),(4,[(1,1,2),(1,3,4),(1,1,6)]),(1,[(1,1,3),(1,2,4),(1,3,6)]),(3,[(1,1,2),(1,3,4),(1,2,6)]),(2,[(1,1,2),(1,3,4),(1,2,6)]),(1,[(1,0,1),(1,1,3),(1,2,4),(1,3,4)]),(4,[(1,0,2),(1,1,3),(1,3,4)]),(6,[(1,0,2),(1,1,3),(1,2,4)]),(21,[(1,0,1),(1,2,3)]),(21,[(1,0,1),(1,1,3)]),(0,[(1,0,2),(1,1,3),(1,2,4),(1,4,6)]),(1,[(1,0,1),(1,1,3),(1,2,4),(1,3,7)]),(3,[(1,0,2),(1,3,5),(1,3,4)]),(2,[(1,0,3),(1,2,4),(1,4,5)]),(1,[(1,0,1),(1,3,5),(1,2,4),(1,3,4)]),(1,[(1,0,1),(1,1,2),(1,2,4),(1,3,4)]),(1,[(1,0,1),(1,1,2),(1,3,5),(1,2,4)]),(0,[(1,1,2),(1,1,3),(1,3,4),(1,4,5)]),(0,[(1,1,2),(1,3,4),(1,5,6)]),(0,[(1,1,2),(1,2,3),(1,4,5),(1,3,4)]),(3,[(1,0,2),(1,2,4),(1,3,4)]),(3,[(1,0,2),(1,3,4),(1,4,5)]),(1,[(1,1,2),(1,2,3),(1,4,5),(1,3,4)]),(1,[(1,0,1),(1,1,2),(1,4,6),(1,3,4)]),(1,[(1,0,1),(1,1,2),(1,2,3),(1,4,6)]),(0,[(1,1,2),(1,4,5),(1,3,4),(1,3,5)]),(47,[(1,1,2)]),(23,[(1,0,2),(1,2,3)]),(0,[(1,1,2),(1,3,4),(1,4,5),(1,3,7)]),(1,[(1,0,2),(1,1,3),(1,3,4),(1,4,5)]),(1,[(1,0,2),(1,1,3),(1,2,4),(1,3,4)]),(0,[(1,0,2),(1,1,3),(1,3,4),(1,4,5)]),(25,[(1,1,2),(1,2,3)]),(24,[(1,0,2),(1,2,3)]),(24,[(1,0,2),(1,1,4)]),(2,[(1,0,2),(1,1,3),(1,2,4),(1,3,4)]),(0,[(1,2,4),(1,3,4)]),(21,[(1,0,2),(1,2,3)]),(21,[(1,0,2),(1,1,3)]),(0,[(1,2,4),(1,3,4),(1,0,1),(1,3,7)]),(6,[(1,0,3),(1,1,4),(1,2,6)]),(6,[(1,0,3),(1,2,4),(1,1,6)]),(4,[(1,1,2),(1,3,4),(1,0,6)]),(4,[(1,0,3),(1,1,2)]),(0,[(1,0,3),(1,2,4),(1,1,6),(1,3,4)]),(6,[(1,0,3),(1,1,4),(1,2,3)]),(1,[(1,0,2),(1,2,4),(1,1,6),(1,3,4)]),(2,[(1,1,3),(1,2,4),(1,3,4)]),(6,[(1,1,4),(1,2,3),(1,0,6)]),(3,[(1,1,3),(1,2,4),(1,3,6)]),(25,[(1,1,3),(1,2,3)]),(25,[(1,0,2),(1,1,3)]),(0,[(1,0,3),(1,2,4),(1,1,6),(1,3,6)]),(14,[(1,0,2),(1,2,3)]),(14,[(1,0,2),(1,2,3),(1,1,3)]),(21,[(1,0,2),(1,1,3),(1,2,3)]),(14,[(1,2,3),(1,1,3)]),(14,[(1,0,2),(1,1,3)]),(1,[(1,0,2),(1,2,4),(1,1,3),(1,4,7)]),(6,[(1,1,4),(1,2,4),(1,0,3)]),(0,[(1,0,3),(1,2,5),(1,2,4),(1,3,4)]),(66,[]),(67,[]),(68,[]),(69,[]),(14,[(1,0,2),(1,3,4)]),(25,[(1,0,3),(1,2,3)]),(3,[(1,3,4),(1,0,1),(1,4,6)]),(1,[(1,0,2),(1,4,5),(1,3,4),(1,3,5)]),(4,[(1,0,3),(1,1,4),(1,5,6)]),(2,[(1,0,2),(1,2,3),(1,3,4)]),(70,[]),(0,[(1,0,3),(1,2,4),(1,3,4),(1,2,7)]),(0,[(1,0,3),(1,2,4),(1,3,6),(1,4,5)]),(25,[(1,0,2),(1,2,3)]),(6,[(1,0,3),(1,4,5)]),(1,[(1,1,2),(1,1,3),(1,2,4),(1,4,6),(1,3,7)]),(0,[(1,1,2),(1,1,3),(1,2,4),(1,4,6),(1,3,7)]),(6,[(1,2,4),(1,3,4),(1,2,3)]),(0,[(1,0,2),(1,2,3),(1,2,4),(1,3,4)]),(3,[(1,0,1),(1,0,4),(1,3,4)]),(3,[(1,0,1),(1,0,4),(1,3,6)]),(0,[(1,0,2),(1,2,4),(1,3,4),(1,3,5)]),(0,[(1,0,2),(1,2,3),(1,3,4),(1,4,5)]),(21,[(1,0,1),(1,1,3),(1,2,3)]),(21,[(1,0,1),(1,1,2),(1,1,3)]),(71,[]),(4,[(1,0,3),(1,1,3),(1,4,5)]),(4,[(1,0,3),(1,4,5),(1,1,5)]),(25,[(1,0,2),(1,3,4)]),(1,[(1,0,2),(1,3,5),(1,2,4),(1,3,4)]),(1,[(1,0,2),(1,3,5),(1,3,4),(1,4,5)]),(0,[(1,2,3),(1,3,4),(1,0,2),(1,4,7)]),(4,[(1,0,3),(1,1,4),(1,3,6)]),(10,[(1,0,2)]),(1,[(1,0,2),(1,3,4),(1,5,6)]),(6,[(1,0,3),(1,1,4),(1,3,6)]),(1,[(1,0,2),(1,2,3),(1,3,4)]),(4,[(1,0,3),(1,4,5),(1,1,4)]),(25,[(1,0,3),(1,2,4)]),(19,[(1,0,1),(1,3,4),(1,2,3)]),(0,[(1,0,3),(1,2,3),(1,1,4),(1,2,4)]),(4,[(1,0,3),(1,2,4),(1,4,5)]),(3,[(1,1,3),(1,0,4),(1,2,6)]),(1,[(1,0,2),(1,2,3),(1,1,4),(1,4,5)]),(0,[(1,0,3),(1,1,4),(1,2,4),(1,2,5)]),(21,[(1,0,2),(1,1,2)]),(0,[(1,0,3),(1,2,3),(1,1,4),(1,4,6)]),(4,[(1,0,3),(1,2,4),(1,3,4)]),(1,[(1,0,2),(1,2,3),(1,1,4),(1,4,6)]),(3,[(1,1,3),(1,2,4),(1,3,4)]),(3,[(1,1,3),(1,2,4),(1,4,5)]),(19,[(1,1,2),(1,3,4)]),(21,[(1,1,2),(1,3,4)]),(0,[(1,2,3),(1,1,4),(1,4,5),(1,0,5)]),(3,[(1,1,3),(1,3,4),(1,2,6)]),(14,[(1,0,2),(1,1,3),(1,2,3)]),(25,[(1,0,2),(1,1,3),(1,2,3)]),(0,[(1,0,3),(1,1,4)]),(21,[(1,0,2)]),(1,[(1,0,2),(1,1,3),(1,2,4)]),(19,[(1,0,2),(1,1,3),(1,2,3)]),(0,[(1,3,4)]),(8,[(1,0,2),(1,1,3),(1,2,3)]),(1,[(1,0,3),(1,3,4),(1,1,2),(1,4,7)]),(17,[(1,1,3),(1,2,3)]),(24,[(1,1,3),(1,2,3)]),(0,[(1,0,3),(1,2,3),(1,2,4),(1,4,5)]),(3,[(1,1,3),(1,0,4),(1,5,6)]),(2,[(1,0,2),(1,1,3),(1,4,5),(1,4,6)]),(1,[(1,0,3),(1,1,4),(1,2,4),(1,3,4)]),(21,[(1,0,3),(1,2,3)]),(25,[(1,0,3),(1,1,4)]),(1,[(1,0,3),(1,1,4),(1,2,4),(1,4,5)]),(6,[(1,0,4),(1,1,2),(1,1,3)]),(3,[(1,0,3),(1,1,4),(1,2,6),(1,3,4)]),(21,[(1,0,3),(1,1,4)]),(14,[(1,2,3)]),(72,[]),(1,[(1,0,3),(1,1,4),(1,3,4),(1,0,7)]),(73,[]),(21,[(1,0,3),(1,2,4)]),(0,[(1,3,4),(1,0,5),(1,0,1),(1,4,7)]),(74,[]),(1,[(1,0,3),(1,3,4),(1,0,1),(1,6,7)]),(1,[(1,0,3),(1,4,5),(1,1,6)]),(0,[(1,0,4),(1,3,4),(1,0,1),(1,6,7)]),(2,[(1,0,3),(1,1,4),(1,3,4),(1,5,6)]),(1,[(1,0,2),(1,0,3),(1,2,4),(1,3,4)]),(1,[(1,0,2),(1,0,3),(1,3,4),(1,4,5)]),(1,[(1,0,2),(1,0,3),(1,2,4),(1,4,6)]),(0,[(1,2,4),(1,0,3),(1,4,6)]),(0,[(1,0,2),(1,2,3),(1,4,5),(1,3,4)]),(4,[(1,0,3),(1,1,5),(1,4,6)]),(4,[(1,1,3),(1,0,5),(1,4,6)]),(2,[(1,0,3),(1,3,4),(1,0,1),(1,4,7)]),(1,[(1,0,3),(1,3,4),(1,0,1),(1,4,7)]),(3,[(1,2,4),(1,3,4),(1,0,1),(1,3,7)]),(6,[(1,2,3),(1,1,4),(1,0,6)]),(4,[(1,0,1),(1,2,4),(1,3,6)]),(4,[(1,0,1),(1,3,4),(1,2,6)]),(21,[(1,0,3)]),(8,[(1,1,3),(1,2,3)]),(6,[(1,1,2),(1,3,4),(1,0,6)]),(19,[(1,0,2)]),(2,[(1,0,3),(1,1,4),(1,3,4),(1,2,7)]),(6,[(1,2,4),(1,3,4),(1,0,5)]),(6,[(1,2,4),(1,3,4),(1,0,6)]),(6,[(1,0,3),(1,0,4),(1,3,6)]),(9,[(1,0,3),(1,2,4)]),(0,[(1,0,4),(1,2,3),(1,4,6)]),(6,[(1,0,4),(1,0,1),(1,2,4)]),(6,[(1,0,4),(1,0,1),(1,2,5)]),(6,[(1,0,1),(1,2,4),(1,4,5)]),(14,[(1,0,3)]),(9,[(1,0,3),(1,1,4)]),(14,[(1,0,1),(1,1,2)]),(21,[(1,0,1),(1,1,2)]),(1,[(1,0,1),(1,1,2),(1,2,3),(0,0,6)]),(0,[(1,2,3),(1,0,1),(1,2,6)]),(2,[(1,0,3),(1,1,4),(1,5,6),(1,3,4)]),(75,[]),(0,[(1,0,4),(1,3,5),(1,1,3),(1,4,7)]),(1,[(1,0,3),(1,4,5),(1,1,4),(1,3,7)]),(0,[(1,2,3),(1,2,4),(1,3,4),(1,2,7)]),(1,[(1,0,2),(1,1,3),(1,4,5),(1,3,4)]),(15,[(1,0,1)]),(24,[(1,0,2),(1,1,2)]),(0,[(1,0,3),(1,2,4),(1,4,5),(1,3,6)]),(1,[(1,0,2),(1,3,4),(1,2,6),(1,4,5)]),(1,[(1,0,2),(1,2,4),(1,3,4),(1,5,7)]),(1,[(1,2,4),(1,3,4),(1,2,6)]),(2,[(1,0,2),(1,1,3),(1,2,4),(1,4,6)]),(25,[(1,0,2),(1,0,3),(1,2,3)]),(1,[(1,0,2),(1,2,3),(1,2,4),(1,3,4)]),(76,[(1,2,3)]),(77,[]),(1,[(1,0,2),(1,2,4),(1,3,4),(1,3,5)]),(1,[(1,0,2),(1,2,3),(1,3,4),(1,4,5)]),(23,[(1,0,3),(1,1,3)]),(25,[(1,0,2),(1,0,3)]),(0,[(1,3,4),(1,0,2),(1,3,6),(1,4,6)]),(3,[(1,1,3),(1,1,4),(1,3,6)]),(24,[(1,1,2),(1,3,4)]),(19,[(1,0,1),(1,1,3),(1,2,3)]),(78,[]),(1,[(1,0,2),(1,3,4),(1,2,4),(1,2,6)]),(6,[(1,0,3),(1,1,3)]),(79,[]),(0,[(1,0,2),(1,4,5),(1,3,4),(1,3,5)]),(2,[(1,0,2),(1,1,2),(1,3,5),(1,4,6)]),(1,[(1,0,3),(1,1,3),(1,2,4),(1,3,4)]),(2,[(1,0,3),(1,1,3),(1,2,4),(1,4,6)]),(1,[(1,0,3),(1,1,3),(1,2,4),(1,4,5)]),(4,[(1,1,2),(1,3,4),(1,1,4)]),(0,[(1,2,4),(1,0,3),(1,1,6),(1,4,6)]),(4,[(1,1,2),(1,1,4),(1,3,6)]),(1,[(1,1,3),(1,2,4),(1,3,4),(1,0,5)]),(1,[(1,0,3),(1,1,3),(1,2,4),(1,4,6)]),(1,[(1,0,3),(1,1,3),(1,2,4),(1,3,7)]),(12,[(1,0,3),(1,1,3)]),(2,[(1,0,3),(1,1,4),(1,4,5),(1,3,6)]),(0,[(1,0,4),(1,3,4),(1,1,3),(1,5,7)]),(0,[(1,0,2),(1,0,3),(1,2,4),(1,3,4)]),(3,[(1,0,1),(1,3,5),(1,3,4)]),(0,[(1,0,2),(1,0,3),(1,3,4),(1,4,5)]),(0,[(1,0,2),(1,0,3),(1,2,4),(1,4,6)]),(15,[(1,1,2)]),(40,[(1,1,2)]),(24,[(1,0,1),(1,2,4)]),(21,[(1,0,1),(1,0,2),(1,1,3)]),(0,[(1,0,3),(1,3,4),(1,2,4),(1,0,7)]),(0,[(1,0,3),(1,2,4),(1,3,4),(1,5,6)]),(0,[(1,0,3),(1,2,4),(1,0,2),(1,5,6)]),(0,[(1,0,2),(1,3,4),(1,2,4),(1,5,6)]),(0,[(1,0,2),(1,3,4),(1,0,3),(1,5,6)]),(0,[(1,0,2),(1,2,4),(1,3,4),(1,0,7)]),(0,[(1,0,1),(1,0,3),(1,2,4),(1,3,4)]),(3,[(1,3,4),(1,0,1),(1,2,6),(1,3,6)]),(1,[(1,0,1),(1,0,3),(1,2,4),(1,3,4)]),(1,[(1,0,1),(1,0,3),(1,2,4),(1,4,6)]),(0,[(1,0,1),(1,0,3),(1,2,4),(1,4,6)]),(0,[(1,0,1),(1,2,4),(1,3,4),(1,3,5)]),(7,[(1,1,2)]),(0,[(1,0,1),(1,0,3),(1,2,4),(1,3,7)]),(1,[(1,0,3),(1,1,5),(1,1,4),(1,3,4)]),(2,[(1,0,3),(1,1,5),(1,1,4),(1,3,4)]),(9,[(1,0,1),(1,3,4)]),(80,[]),(19,[(1,0,2),(1,0,3),(1,2,3)]),(21,[(1,0,2),(1,0,3),(1,2,3)]),(2,[(1,3,4),(1,0,1),(1,3,6),(1,4,6)]),(0,[(1,0,3),(1,3,4),(1,0,1),(1,4,7)]),(4,[(1,0,1),(1,2,4),(1,5,6)]),(15,[(1,0,2)]),(81,[]),(3,[(1,0,1),(1,2,4),(1,4,5),(0,0,1)]),(24,[(1,0,3),(1,1,3)]),(40,[(1,0,2)]),(21,[(1,0,2),(1,3,4)]),(5,[(1,0,2),(1,3,4)]),(5,[(1,0,3),(1,2,4)]),(24,[(1,1,3)]),(19,[(1,0,2),(1,1,2)]),(24,[(1,1,2),(0,0,4)]),(3,[(1,0,3),(1,1,2),(1,3,6),(0,0,7)]),(21,[(1,0,2),(1,1,4)]),(6,[(1,0,1),(1,3,4),(1,2,6)]),(19,[(1,1,3),(0,0,4)]),(19,[(1,1,3),(1,0,3)]),(6,[(1,1,2),(1,3,5),(0,0,6)]),(3,[(1,0,1),(1,2,4),(1,3,4),(0,0,1)]),(4,[(1,0,1),(1,2,4),(1,3,4),(0,0,1)]),(0,[(1,1,4)]),(2,[(0,0,1),(1,0,1)]),(3,[(0,0,1),(1,0,1),(1,2,4),(1,3,7)]),(6,[(1,0,4),(1,2,4),(1,1,5)]),(6,[(1,0,4),(1,1,4),(1,2,5)]),(5,[(1,2,3),(1,0,4)]),(6,[(1,1,4),(1,2,4),(1,0,5)]),(6,[(1,1,4),(1,2,4),(1,0,6)]),(82,[]),(1,[(1,0,3),(1,0,4),(1,3,4),(1,1,5)]),(4,[(1,1,2),(1,0,4),(1,1,4)]),(9,[(1,1,2),(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,1,4)]),(14,[(1,1,2),(1,2,3)]),(5,[(1,0,1),(1,0,2),(1,0,3)]),(6,[(1,3,4),(1,2,5)]),(4,[(1,0,3),(1,3,4),(1,1,4)]),(6,[(1,0,3),(1,3,4),(1,1,4)]),(3,[(1,1,3),(1,4,5)]),(5,[(1,0,3),(0,2,4),(1,2,3)]),(5,[(1,0,3),(0,2,4)]),(0,[(1,3,4),(1,0,1),(1,4,6),(0,3,7)]),(10,[(1,0,1)]),(4,[(1,0,1),(1,3,5)]),(6,[(1,2,3),(0,0,1),(1,4,6)]),(83,[]),(6,[(1,2,3),(1,0,4)]),(6,[(1,2,3),(1,1,4)]),(9,[(1,1,3),(1,2,4)]),(9,[(1,2,3),(1,1,4)]),(21,[(1,2,3),(1,1,4)]),(84,[]),(6,[(1,3,4),(1,0,4)]),(85,[]),(6,[(1,3,4),(1,1,4)]),(21,[]),(8,[(1,0,3),(1,2,3)]),(14,[(1,0,3),(1,2,4)]),(21,[(1,1,3),(1,2,4)]),(8,[(1,0,3),(1,1,3)]),(14,[(1,0,3),(1,1,4)]),(9,[(1,1,3),(1,0,4)]),(14,[(1,1,3),(0,0,4)]),(86,[]),(21,[(1,0,3),(1,1,3)]),(87,[]),(0,[(1,2,4),(1,0,1),(1,4,6)]),(19,[(1,0,1),(1,1,2)]),(14,[(1,0,2),(1,1,2)]),(21,[(1,1,2),(1,0,4)]),(5,[(1,1,2),(1,2,3),(1,1,5)]),(5,[(1,1,2),(1,1,3),(1,2,5)]),(21,[(1,1,2),(1,2,3),(1,1,5)]),(21,[(1,1,2),(1,1,3),(1,2,5)]),(45,[(1,2,3)]),(47,[(1,2,3)]),(8,[(0,0,1)]),(19,[(1,1,2),(1,1,3)]),(3,[(1,0,1),(1,2,3),(1,2,4),(1,3,4)]),(0,[(1,3,4),(1,1,2),(1,3,6),(1,4,6)]),(3,[(1,0,1),(1,2,3),(1,2,4),(1,3,7)]),(0,[(1,0,3),(1,1,5),(1,0,4),(1,3,4)]),(6,[(1,0,1),(1,4,5),(1,2,6)]),(38,[(1,2,3)]),(0,[(1,0,3),(1,0,4),(1,3,4),(1,1,7)]),(6,[(1,0,1),(1,4,5),(1,2,4)]),(88,[]),(89,[]),(6,[(1,0,1),(1,2,4),(1,5,6)]),(41,[(1,0,2)]),(12,[(1,0,1),(1,2,3)]),(21,[(1,0,2),(1,0,3)]),(5,[(1,0,2),(1,0,3)]),(0,[(1,0,1),(1,3,5),(1,4,5)]),(19,[(1,0,2),(1,1,3)]),(1,[(1,0,3),(1,1,3),(1,1,4),(1,2,4)]),(0,[(1,2,4),(1,0,1),(1,3,6),(1,4,6)]),(2,[(1,1,3),(1,1,4),(1,2,4),(1,0,5)]),(1,[(1,1,3),(1,1,4),(1,2,4),(1,0,5)]),(1,[(1,0,3),(1,1,3),(1,1,4),(1,2,7)]),(8,[(1,1,2),(1,1,3)]),(8,[(1,0,2),(1,1,2)]),(12,[(1,0,3),(1,1,2)]),(4,[(1,1,2),(1,0,4),(1,5,6)]),(1,[(1,0,3),(1,1,3),(1,1,4),(1,4,5)]),(19,[(1,0,1),(1,0,3)]),(2,[(1,0,4),(1,1,4),(1,0,1),(1,2,7)]),(1,[(1,0,4),(1,1,4),(1,0,1),(1,2,7)]),(5,[(1,0,1),(1,0,3)]),(0,[(1,0,1),(1,2,5),(1,4,5)]),(0,[(1,0,1),(1,0,3),(1,4,5),(1,3,4)]),(4,[(1,0,1),(1,2,5),(1,4,6)]),(1,[(1,0,1),(1,0,3),(1,4,5),(1,3,4)]),(90,[]),(25,[(1,0,1),(1,0,2)]),(9,[(1,0,1),(1,0,2)]),(19,[(1,0,1),(1,2,4)]),(19,[(1,0,2),(1,1,4)]),(35,[(1,0,2)]),(4,[(1,2,4),(1,3,5),(1,1,4)]),(25,[(1,1,3)]),(14,[(1,0,1),(1,0,3)]),(0,[(1,0,1),(1,0,4),(1,3,4)]),(4,[(1,0,1),(1,2,5),(1,3,5)]),(8,[(0,0,1),(1,0,1)]),(12,[(0,0,1),(1,0,1)]),(19,[(1,0,3),(1,1,4)]),(5,[(1,0,2),(1,0,3),(1,2,3)]),(1,[(1,3,4),(1,0,1),(1,3,6),(1,4,6)]),(0,[(1,3,4),(1,0,1),(1,3,6),(1,4,6)]),(91,[]),(25,[(0,2,3),(1,2,3)]),(5,[(0,2,3),(1,2,3),(1,0,5)]),(0,[(0,3,4),(1,3,4)]),(4,[(1,0,1),(1,4,5)]),(4,[(0,0,1),(1,0,1),(1,2,3),(1,6,7)]),(6,[(0,0,1),(1,0,1)]),(25,[(1,0,1),(1,1,2)]),(4,[(0,0,1),(1,0,1),(1,2,3)]),(57,[]),(8,[(1,1,2),(1,0,1)]),(18,[(1,1,2),(1,0,1)]),(19,[(1,1,2),(1,0,1)]),(19,[(1,2,3),(1,0,2)]),(24,[(1,1,2),(1,0,4)]),(21,[(1,0,1),(1,0,3)]),(4,[(1,0,2),(1,1,5),(1,4,6)]),(24,[(1,0,1),(1,3,4)]),(14,[(1,0,1),(1,2,4)]),(8,[(1,1,2),(1,0,4)]),(24,[(1,1,2),(0,0,1)]),(24,[(1,2,3),(1,0,3)]),(24,[(1,2,3),(1,1,3)]),(27,[(1,1,2)]),(23,[(1,0,1),(1,2,3)]),(24,[(0,0,1),(1,0,1),(1,2,3)]),(8,[(0,2,3),(1,2,3)]),(7,[(0,1,2)]),(12,[(1,0,2),(1,1,2)]),(17,[(1,0,1),(1,1,2)]),(12,[(1,0,1),(1,1,2)]),(23,[(1,0,1),(1,1,2)]),(17,[(1,0,1),(1,0,2)]),(12,[(1,0,1),(1,0,2)]),(23,[(1,0,1),(1,0,2)]),(12,[(1,0,1),(1,0,2),(1,1,2)]),(23,[(1,0,1),(1,0,2),(1,1,2)]),(17,[(1,0,1),(1,0,2),(1,1,2)]),(17,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(1,2,3),(1,1,6),(1,3,4)]),(48,[(1,0,1)]),(9,[(1,2,3),(1,1,3)]),(17,[(1,0,1),(1,1,2),(1,2,3)]),(9,[(1,0,1),(1,2,3),(1,1,3)]),(9,[(1,0,1),(1,1,3)]),(0,[(1,0,1),(1,2,3),(1,2,4)]),(17,[(1,1,2),(1,2,3)]),(12,[(1,1,2),(1,2,3)]),(47,[(1,1,3)]),(29,[(1,2,3)]),(29,[(1,0,1)]),(14,[(1,0,1),(1,2,3),(1,1,3)]),(14,[(1,0,1),(1,1,3)]),(9,[(1,0,2),(1,1,2),(1,3,5)]),(18,[(1,1,2),(1,1,3),(1,2,3)]),(9,[(1,0,1),(1,1,2),(1,3,5)]),(9,[(1,0,1),(1,0,2),(1,1,2)]),(47,[(1,0,1)]),(2,[(1,1,2),(1,2,4),(1,3,4),(1,3,5)]),(2,[(1,1,2),(1,2,3),(1,3,4),(1,4,5)]),(23,[(1,1,2),(1,2,3)]),(2,[(1,1,2),(1,3,4),(1,2,3),(1,2,6)]),(23,[(1,1,2),(1,1,3),(1,2,3)]),(92,[]),(0,[(1,0,1),(1,0,2),(1,1,2),(1,3,5),(1,3,4)]),(0,[(1,0,1),(1,0,2),(1,1,2),(1,3,5),(1,4,6)]),(2,[(1,1,3),(1,3,4),(1,1,2),(1,4,7)]),(1,[(1,1,2),(1,2,4),(1,3,4),(1,3,5)]),(2,[(1,1,3),(1,2,4),(1,3,4),(1,1,2)]),(2,[(1,1,2),(1,1,3),(1,3,4),(1,4,5)]),(2,[(1,2,4),(1,3,4),(1,1,2),(1,3,7)]),(2,[(1,1,3),(1,2,4),(1,3,4),(1,5,6)]),(2,[(1,1,3),(1,2,4),(1,1,2),(1,5,6)]),(2,[(1,1,2),(1,3,4),(1,5,6)]),(23,[(1,1,2),(1,1,3)]),(18,[(1,2,3),(1,1,4)]),(12,[(1,0,2),(1,2,3)]),(12,[(1,0,2),(1,3,4)]),(93,[(1,1,2)]),(4,[(1,0,2),(1,2,4),(1,0,3),(1,4,7)]),(38,[(1,1,2)]),(6,[(1,0,3),(1,2,4),(1,5,6)]),(18,[(1,0,1),(1,0,3)]),(6,[(1,1,3),(1,2,4),(1,3,4),(1,5,6)]),(6,[(1,1,3),(1,2,4),(1,1,2),(1,5,6)]),(6,[(1,3,4),(1,2,4),(1,1,2),(1,3,7)]),(6,[(1,3,4),(1,1,3),(1,1,2),(1,4,7)]),(6,[(1,1,2),(1,2,4),(1,3,4),(1,1,7)]),(19,[(1,1,3),(1,2,4)]),(6,[(1,1,2),(1,3,4),(1,2,4),(1,5,6)]),(24,[(1,0,1),(1,1,2),(1,2,3)]),(24,[(1,1,2),(0,0,4),(1,2,3)]),(25,[(1,0,1),(1,3,4)]),(48,[(1,1,3)]),(21,[(1,0,1),(1,3,4)]),(14,[(1,1,2),(0,0,4),(1,2,3)]),(6,[(1,3,4),(1,2,4),(1,0,1),(1,2,7)]),(17,[(1,0,2),(1,1,3),(1,2,3)]),(6,[(1,0,2),(1,1,3),(1,2,4),(1,4,6)]),(6,[(1,0,2),(1,3,4),(1,2,4)]),(86,[(1,1,2)]),(38,[(1,1,3)]),(14,[(1,2,3),(1,0,3)]),(18,[(1,0,3),(1,2,4)]),(18,[(1,0,3),(0,2,4),(1,2,3)]),(17,[(1,0,1),(1,3,4)]),(23,[(1,0,3),(1,1,4)]),(23,[(1,1,3),(1,0,4)]),(17,[(1,1,3),(1,0,4)]),(18,[(1,1,2),(1,3,4)]),(17,[(1,2,3),(1,0,2)]),(17,[(1,2,3),(1,1,2)]),(94,[]),(9,[(1,0,2),(1,3,4)]),(12,[(1,1,3)]),(18,[(1,0,1),(1,1,3)]),(19,[(1,0,1),(1,1,3)]),(74,[(1,1,2)]),(0,[(1,1,2),(1,0,5),(1,2,4),(1,3,4)]),(0,[(1,1,2),(1,0,5),(1,1,3),(1,3,4)]),(0,[(1,1,2),(1,0,5),(1,1,3),(1,2,4)]),(2,[(1,1,2),(1,2,4),(1,3,4),(1,0,5)]),(2,[(1,0,1),(1,1,2),(1,3,4),(1,2,4)]),(48,[(1,1,2)]),(19,[(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,4)]),(6,[(1,0,1),(1,2,3),(1,2,4),(1,4,5)]),(6,[(1,0,1),(1,1,4),(1,2,4),(1,3,7)]),(6,[(1,0,1),(1,1,4),(1,2,3),(1,4,7)]),(6,[(1,0,1),(1,2,4),(1,1,4),(1,2,3)]),(5,[(1,0,2),(1,1,3),(1,4,5)]),(6,[(1,0,1),(1,2,3),(1,2,4),(1,1,7)]),(14,[(1,1,2),(1,2,3),(1,0,3)]),(6,[(1,2,3),(1,2,4),(1,0,1),(1,4,7)]),(0,[(1,0,1),(1,1,3),(1,2,3),(1,4,5),(1,4,7)]),(0,[(1,0,1),(1,0,2),(1,1,3),(1,2,3),(1,4,8)]),(0,[(1,0,1),(1,0,2),(1,1,3),(1,2,3),(1,4,5)]),(6,[(1,2,4),(1,3,4),(1,1,2),(1,3,7)]),(6,[(1,1,3),(1,3,4),(1,1,2),(1,4,7)]),(9,[(1,0,1),(1,3,4),(1,2,3)]),(25,[(1,0,1),(1,3,4),(1,2,3)]),(3,[(1,2,3),(1,3,4),(1,1,2),(1,4,7)]),(24,[(1,1,2),(1,1,3),(1,2,3)]),(4,[(1,1,3),(1,3,4),(1,1,2),(1,4,7)]),(6,[(1,1,2),(1,3,4),(1,1,3),(1,5,6)]),(6,[(1,1,2),(1,2,4),(1,1,3),(1,4,7)]),(6,[(1,1,2),(1,1,3),(1,3,4),(1,2,7)]),(6,[(1,1,2),(1,1,3),(1,2,4),(1,3,7)]),(0,[(1,1,2),(1,1,3),(1,2,4),(1,3,4),(1,0,8)]),(6,[(1,2,3),(1,0,4),(1,1,4),(1,2,6)]),(4,[(1,2,3),(1,0,4),(1,1,4),(1,3,6)]),(6,[(1,2,3),(1,2,4),(1,0,4),(1,1,7)]),(18,[(1,2,3),(1,0,4)]),(6,[(1,2,3),(1,0,4),(1,1,4),(1,2,7)]),(14,[(1,1,2),(1,0,3)]),(4,[(1,2,3),(1,0,4),(1,1,4),(1,3,7)]),(4,[(1,3,4),(1,0,4),(1,1,4),(1,2,3)]),(6,[(1,2,4),(1,0,4),(1,1,4)]),(6,[(1,2,4),(1,0,4),(1,1,4),(1,2,3)]),(95,[]),(0,[(1,1,2),(1,3,4),(1,0,6),(1,5,6)]),(6,[(1,2,3),(1,0,4),(1,4,5),(1,2,6)]),(4,[(1,2,3),(1,0,4),(1,4,5),(1,3,6)]),(6,[(1,2,3),(1,2,4),(1,0,4),(1,5,7)]),(96,[]),(4,[(1,3,4),(1,0,4),(1,2,5)]),(2,[(1,2,4),(1,3,4),(1,0,2),(1,6,7)]),(4,[(1,2,3),(1,3,4),(1,0,2),(1,6,7)]),(6,[(1,2,3),(1,2,4),(1,0,3),(1,6,7)]),(4,[(1,2,3),(1,3,4),(1,0,4),(1,5,7)]),(14,[(1,1,2),(1,0,1),(1,2,3)]),(25,[(1,1,2),(1,0,3),(1,2,3)]),(6,[(1,2,3),(1,1,3),(1,0,4),(1,2,7)]),(2,[(1,0,3),(1,3,4),(1,1,2),(1,4,7)]),(4,[(1,2,3),(1,0,2),(1,1,4),(1,3,7)]),(29,[(1,1,3)]),(5,[(1,0,1),(1,2,3),(1,4,5)]),(18,[(1,1,2),(1,0,3),(1,2,3)]),(6,[(1,2,3),(1,0,3),(1,1,4),(1,2,7)]),(6,[(1,0,3),(1,1,4),(1,2,3),(1,4,7)]),(6,[(1,2,4),(1,1,4),(1,0,3),(1,2,7)]),(6,[(1,1,2),(1,1,3),(1,0,4),(1,2,7)]),(4,[(1,1,2),(1,1,3),(1,0,4),(1,3,7)]),(0,[(1,1,3),(1,2,4),(1,3,4),(1,0,2),(1,1,8)]),(0,[(1,1,3),(1,2,4),(1,3,4),(1,0,1),(1,2,8)]),(4,[(1,1,3),(1,3,4),(1,0,4)]),(0,[(1,0,2),(1,2,4),(1,3,4),(1,1,3),(1,0,8)]),(0,[(1,0,2),(1,2,4),(1,3,4),(1,0,1),(1,3,8)]),(12,[(1,2,3),(1,0,3)]),(6,[(1,1,3),(1,2,4),(1,0,4),(1,2,5)]),(4,[(1,1,2),(1,3,4),(1,0,4),(1,3,5)]),(6,[(1,1,2),(1,2,4),(1,0,4)]),(6,[(1,1,2),(1,2,4),(1,0,4),(1,1,3)]),(12,[(1,1,2),(1,0,3)]),(24,[(1,1,2),(1,0,3)]),(4,[(1,1,3),(1,3,4),(1,0,2),(1,1,7)]),(4,[(1,1,3),(1,3,4),(1,0,1),(1,2,7)]),(0,[(1,1,3),(1,2,4),(1,3,4),(1,0,2)]),(6,[(1,0,2),(1,1,3),(1,2,4),(1,0,6)]),(23,[(1,0,2),(1,1,3)]),(3,[(1,0,1),(1,2,3),(1,3,4),(1,2,5)]),(23,[(1,0,1),(1,1,3)]),(6,[(1,0,1),(1,1,3),(1,2,4),(1,0,7)]),(6,[(1,0,1),(1,0,2),(1,2,4),(1,1,3)]),(4,[(1,0,1),(1,0,2),(1,3,4),(1,1,7)]),(93,[]),(24,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(1,0,2),(1,3,4),(1,2,7)]),(2,[(1,0,1),(1,1,2),(1,3,4),(1,2,7)]),(0,[(1,0,2),(1,1,3),(1,2,4),(1,4,6),(1,3,7)]),(97,[]),(0,[(1,0,1),(1,1,3),(1,2,4),(1,4,6),(1,3,7)]),(0,[(1,0,1),(1,0,2),(1,1,3),(1,2,4),(1,3,8)]),(0,[(1,0,1),(1,0,2),(1,1,3),(1,2,4),(1,4,7)]),(4,[(1,1,3),(1,3,4),(1,2,4),(1,1,2)]),(4,[(1,1,3),(1,2,4),(1,3,4),(1,5,6)]),(12,[(1,2,3),(1,1,4)]),(4,[(1,1,2),(1,2,4),(1,3,4),(1,1,7)]),(0,[(1,0,1),(1,0,2),(1,1,3),(1,3,6),(1,2,4)]),(0,[(1,0,1),(1,0,2),(1,1,3),(1,3,6),(1,4,5)]),(3,[(1,2,3),(1,1,3),(1,1,2),(1,4,7)]),(4,[(1,1,2),(1,1,3),(1,3,4),(1,4,5)]),(2,[(1,2,4),(1,3,4),(1,0,3),(1,5,7)]),(3,[(1,2,3),(1,4,5),(1,0,4),(1,3,7)]),(98,[]),(0,[(1,1,2),(1,1,3),(1,4,5),(1,3,4),(1,2,8)]),(3,[(1,2,4),(1,3,4),(1,0,2),(1,3,7)]),(4,[(1,2,3),(1,0,2),(1,3,4),(1,6,7)]),(2,[(1,0,3),(1,2,4),(1,3,6),(1,4,5)]),(2,[(1,0,3),(1,2,4),(1,3,4),(1,5,6)]),(2,[(1,3,4),(1,2,5),(1,0,2),(1,4,7)]),(3,[(1,2,3),(1,0,4),(1,3,4),(1,5,6)]),(3,[(1,2,3),(1,0,4),(1,4,5),(1,3,6)]),(19,[(1,2,3),(1,1,4)]),(3,[(1,0,4),(1,3,4),(1,2,6)]),(3,[(1,0,4),(1,3,4),(1,2,6),(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3),(1,2,4),(1,4,6)]),(2,[(1,3,4),(1,0,2),(1,3,6),(1,4,6)]),(24,[(1,0,2),(1,3,4)]),(3,[(1,0,3),(1,0,4),(1,2,3),(1,4,7)]),(8,[(1,0,2),(1,0,3),(1,2,3)]),(25,[(1,1,2),(1,1,3),(1,2,3)]),(3,[(1,3,4),(1,0,2),(1,3,6),(1,4,6)]),(38,[(1,0,1)]),(14,[(1,0,1),(1,3,4),(1,2,3)]),(4,[(1,0,2),(1,4,5),(1,3,4),(1,2,7)]),(25,[(1,2,3),(1,1,4)]),(2,[(1,3,4),(1,1,2),(1,3,6),(1,4,6)]),(3,[(1,0,2),(1,1,3),(1,1,4),(1,3,7)]),(3,[(1,0,2),(1,2,4),(1,3,4),(1,3,5)]),(3,[(1,0,2),(1,2,3),(1,3,4),(1,4,5)]),(18,[(1,0,1),(1,1,3),(1,2,3)]),(18,[(1,0,1),(1,1,2),(1,2,3)]),(18,[(1,0,1),(1,1,2),(1,1,3)]),(23,[(1,1,3),(1,2,3)]),(25,[(1,0,1),(1,1,3),(1,2,3)]),(25,[(1,0,1),(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,0,3),(1,1,4)]),(3,[(1,1,3),(1,2,4),(1,3,4),(1,1,2)]),(3,[(1,2,4),(1,3,4),(1,1,3),(1,2,7)]),(3,[(1,2,4),(1,3,4),(1,1,2),(1,3,7)]),(3,[(1,1,3),(1,2,4),(1,3,4),(1,5,6)]),(3,[(1,1,2),(1,3,4),(1,2,4),(1,5,6)]),(24,[(1,0,3),(1,2,4)]),(2,[(1,0,4),(1,2,3),(1,4,6)]),(2,[(1,2,4),(1,0,3),(1,4,6),(0,2,7)]),(95,[(1,1,2)]),(25,[(1,0,1),(1,2,3)]),(2,[(1,1,2),(1,1,3),(1,2,4),(1,4,6)]),(3,[(1,0,2),(1,1,2),(1,3,6),(1,3,4)]),(0,[(1,1,2),(1,1,3),(1,2,4),(1,1,7),(1,3,4)]),(2,[(1,2,4),(1,0,5),(1,0,3),(1,4,7)]),(99,[]),(19,[(1,1,3),(1,0,4)]),(21,[(1,1,3),(1,2,3),(1,1,5)]),(17,[(1,2,3),(1,0,4)]),(3,[(1,0,4),(1,3,4),(1,0,1),(1,6,7)]),(0,[(1,1,2),(1,1,3),(1,2,3),(1,4,5),(1,3,4)]),(9,[(1,2,3),(1,0,4)]),(14,[(1,2,3),(1,0,4)]),(14,[(1,0,1),(1,3,4)]),(14,[(1,1,3),(1,0,4)]),(86,[(1,0,2)]),(95,[(1,0,1)]),(3,[(1,2,4),(1,0,3),(1,4,6)]),(23,[(1,2,3),(1,0,2)]),(9,[(1,1,2),(1,1,3),(1,2,3)]),(8,[(1,0,2),(1,3,4)]),(100,[(1,0,2)]),(14,[(1,0,2),(1,1,4)]),(14,[(1,1,2),(1,0,4)]),(9,[(1,0,1),(1,1,2)]),(17,[(1,0,2),(1,1,4)]),(17,[(1,1,2),(1,0,4)]),(25,[(1,0,1),(0,2,3)]),(9,[(1,0,2),(1,1,2)]),(0,[(1,1,2),(1,1,3),(1,2,3),(1,1,4),(1,4,7)]),(0,[(1,2,3),(1,1,4),(1,4,5),(1,1,5)]),(100,[]),(0,[(1,1,2),(1,1,3),(1,2,3),(1,1,4),(1,2,4)]),(8,[(1,0,2),(1,0,3)]),(4,[(1,2,3),(1,0,3),(1,4,6),(1,2,4)]),(10,[(1,0,3),(1,0,2)]),(13,[(1,0,3),(1,0,2)]),(10,[(1,0,2),(1,1,2)]),(11,[(1,0,2),(1,1,2)]),(10,[(1,0,2),(1,1,4)]),(8,[(1,1,3),(1,1,2)]),(13,[(1,1,2),(1,0,4)]),(25,[(1,0,1),(1,0,3)]),(9,[(1,1,3),(1,2,4),(1,2,3)]),(9,[(1,1,2),(1,3,4),(1,2,3)]),(14,[(1,1,3),(1,2,4),(1,2,3)]),(14,[(1,1,2),(1,3,4),(1,2,3)]),(4,[(1,0,3),(1,1,4),(1,3,4),(1,5,6)]),(10,[(1,0,2),(1,2,3)]),(14,[(1,1,2),(1,3,4)]),(72,[(1,2,3)]),(50,[(1,2,3)]),(10,[(1,1,3),(1,0,4)]),(0,[(1,2,3),(1,0,5),(1,2,4)]),(3,[(1,0,3),(1,1,3),(1,0,4),(1,6,7)]),(4,[(1,0,3),(1,1,3),(1,1,4),(1,5,7)]),(10,[(1,0,3),(1,2,3)]),(10,[(1,2,3),(1,0,4)]),(10,[(1,0,3),(1,1,3)]),(11,[(1,0,3),(1,1,3)]),(10,[(1,0,3),(1,1,4)]),(10,[(1,0,1),(1,0,2)]),(17,[(1,0,2),(1,3,4)]),(17,[(1,0,3),(1,2,4)]),(10,[(1,2,3),(1,0,1)]),(8,[(1,2,3),(1,0,4)]),(10,[(1,0,1),(1,3,4)]),(30,[(1,1,2)]),(10,[(1,0,3),(1,2,4)]),(23,[(1,0,1),(1,0,3)]),(23,[(1,0,1),(1,3,4)]),(11,[(1,0,1),(1,3,4)]),(10,[(1,0,2),(1,0,3)]),(9,[(1,0,2),(1,0,3)]),(10,[(1,0,1),(1,0,3)]),(23,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(1,3,4),(1,0,6)]),(25,[(1,0,1),(1,0,3),(1,1,3)]),(48,[(1,0,3)]),(8,[(1,0,3),(1,2,4)]),(17,[(1,2,3),(1,0,3)]),(9,[(1,1,3),(1,1,2)]),(11,[(1,0,1),(1,2,4)]),(10,[(1,0,1),(1,2,4)]),(11,[(1,1,2),(1,0,4)]),(11,[(1,0,2),(1,1,4)]),(10,[(1,0,1),(1,1,2)]),(11,[(1,2,3),(1,1,3)]),(23,[(1,1,2),(1,0,4)]),(100,[(1,1,2)]),(72,[(1,1,2)]),(23,[(1,0,2),(1,1,4)]),(0,[(1,2,4),(1,3,4),(1,0,1),(1,2,7),(1,3,7)]),(23,[(1,0,2),(1,1,2),(1,3,5)]),(72,[(1,1,3)]),(23,[(1,0,1),(1,1,2),(1,3,5)]),(11,[(1,2,3),(1,1,2)]),(101,[(1,1,2)]),(17,[(1,0,2),(1,1,3),(1,4,5)]),(35,[(1,1,2)]),(13,[(1,2,3),(1,0,2),(1,1,3)]),(13,[(1,0,1),(1,0,2),(1,1,3)]),(13,[(1,0,1),(1,2,3),(1,1,3)]),(13,[(1,0,2),(1,1,3),(1,4,5)]),(17,[(1,1,2),(1,1,3)]),(102,[]),(17,[(1,1,3),(1,2,3),(1,1,5)]),(17,[(1,1,2),(1,1,3),(1,2,5)]),(17,[(1,1,2),(1,1,3),(1,2,3)]),(103,[]),(13,[(1,0,1),(1,2,3),(1,0,2)]),(17,[(1,2,3),(1,1,4)]),(10,[(1,2,3),(1,1,4)]),(11,[(1,2,3),(1,0,1)]),(17,[(1,1,2),(1,0,2)]),(18,[(1,2,3),(1,1,2)]),(10,[(1,1,2),(1,3,4)]),(10,[(1,1,3),(1,2,4)]),(17,[(1,1,2),(1,3,4)]),(10,[(1,1,3),(1,2,3)]),(0,[(1,2,3),(1,2,4),(1,3,4),(1,0,1),(0,0,1)]),(17,[(1,1,2),(1,0,3)]),(13,[(1,0,2),(1,1,2),(1,0,1)]),(11,[(1,0,2),(1,3,4)]),(11,[(1,0,3),(1,2,4)]),(9,[(1,1,2),(1,2,3),(1,0,5)]),(11,[(1,1,2),(1,2,3)]),(8,[(1,2,3),(1,0,1)]),(23,[(1,0,1),(1,1,3),(1,2,3)]),(11,[(1,0,1),(1,1,2)]),(23,[(1,0,2),(1,1,3),(1,4,5)]),(104,[]),(0,[(1,1,2),(1,1,3),(1,3,4)]),(23,[(1,2,3),(1,0,2),(1,1,3)]),(8,[(1,0,2),(1,1,3),(1,4,5)]),(30,[(1,0,1)]),(23,[(1,1,3),(1,2,4)]),(19,[(1,1,2),(1,1,3),(1,2,5)]),(23,[(1,0,3),(1,2,3)]),(30,[(0,0,1)]),(23,[(1,2,3),(1,1,4)]),(17,[(1,1,3),(1,2,4)]),(25,[(1,1,3),(1,2,3),(1,1,2)]),(35,[(1,0,1)]),(11,[(1,0,2),(1,2,3)]),(13,[(1,1,2),(1,1,3),(1,2,3)]),(11,[(1,0,3),(1,2,3)]),(8,[(1,0,2),(1,0,3),(1,2,5)]),(11,[(1,0,2)]),(0,[(1,1,2),(1,3,5),(1,4,5),(1,3,4)]),(13,[(1,0,2),(1,0,3),(1,2,3)]),(10,[(1,0,2),(1,0,3),(1,2,5)]),(10,[(1,0,2),(1,0,3),(1,2,3)]),(10,[(1,0,1),(1,0,3),(1,1,3)]),(13,[(1,0,1),(1,0,3)]),(23,[(1,0,3),(1,2,4)]),(11,[(1,2,3),(1,0,4)]),(35,[(1,0,2),(1,1,2)]),(35,[(1,0,1),(1,1,2)]),(35,[(1,0,1),(1,0,2)]),(98,[(1,0,1)])]
def mtopt : Tabs := (mtopC.map (mkCut false mtopZ),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(17,16),(17,1),(33,32),(33,1),(6,4),(6,2),(10,8),(10,2),(18,16),(18,2),(34,32),(34,2),(12,8),(12,4),(20,16),(20,4),(36,32),(36,4),(24,16),(24,8),(40,32),(40,8),(48,32),(48,16),(33,2),(33,4),(33,8),(33,16),(6,32),(17,2),(17,4),(17,8),(3,4)],[(24,1,16,9,8,17),(40,1,32,9,8,33),(12,1,8,5,4,9),(36,1,32,5,4,33),(24,32,16,40,8,48),(6,8,4,10,2,12),(3,4,2,5,1,6),(12,16,8,20,4,24),(3,16,2,17,1,18),(48,1,32,17,16,33),(48,4,32,20,16,36),(48,1,32,9,8,33),(20,1,16,5,4,17),(3,8,2,9,1,10),(20,8,32,12,4,40),(40,4,16,12,8,20),(36,1,16,5,4,17),(10,1,8,3,2,9),(12,32,8,36,4,40),(40,16,32,24,8,48),(6,32,4,34,2,36),(9,16,8,17,1,24),(10,32,8,34,2,40),(20,32,16,36,4,48),(36,16,32,20,4,48),(17,4,16,5,1,20),(17,8,16,9,1,24),(18,4,16,6,2,20),(36,2,32,6,4,34),(18,8,16,10,2,24),(40,2,32,10,8,34),(10,16,8,18,2,24),(48,2,32,18,16,34),(3,4,1,6,2,5),(5,32,4,33,1,36),(3,32,2,33,1,34),(12,2,8,6,4,10),(10,4,8,6,2,12),(9,32,8,33,1,40),(24,4,32,20,16,36),(17,32,16,33,1,48),(20,2,16,6,4,18),(24,2,16,10,8,18),(6,1,32,5,4,33),(10,1,32,9,8,33),(33,4,32,5,1,36),(34,4,32,6,2,36),(48,2,32,3,1,34),(48,1,32,3,2,33),(36,2,32,3,1,34),(36,1,32,3,2,33),(12,1,32,9,8,33),(40,2,32,3,1,34),(40,1,32,3,2,33),(40,1,32,5,4,33),(5,8,4,10,2,12),(5,8,4,9,2,12),(5,8,4,9,1,12),(17,4,16,6,2,20),(20,1,16,9,8,17),(6,1,4,3,2,5),(9,2,8,3,1,10),(24,4,16,12,8,20),(20,8,16,12,4,24),(5,2,4,3,1,6),(24,1,32,9,8,33),(5,16,4,17,1,20),(24,1,32,17,16,33),(24,2,32,10,8,34),(6,16,4,18,2,20),(24,2,32,18,16,34),(34,8,32,10,2,48),(34,16,32,18,2,48),(12,16,8,20,4,48),(12,32,8,36,4,48),(9,16,8,17,1,48),(3,8,1,10,2,9),(18,1,16,3,2,17),(34,1,32,3,2,33),(17,2,16,3,1,18),(33,2,32,3,1,34),(33,8,32,9,1,48),(33,16,32,17,1,48),(18,32,16,34,2,48),(9,32,8,33,1,48),(6,8,4,10,2,40),(20,1,16,9,4,33),(12,1,8,17,4,33),(34,8,32,10,2,40),(12,2,8,18,4,34),(6,32,4,40,2,48),(10,16,8,20,2,48),(20,8,16,10,4,40),(20,8,16,9,4,40),(5,32,16,33,1,48),(40,4,32,6,8,20),(10,16,32,18,2,48),(40,1,32,5,8,17),(48,4,32,12,8,36),(12,32,8,33,4,48),(9,16,8,20,1,48),(48,1,32,17,16,40),(6,16,2,20,4,18),(48,1,32,5,16,9),(3,32,2,40,1,48),(5,32,8,36,4,40),(3,16,1,18,2,17),(17,32,16,40,1,48),(18,8,16,12,2,40),(18,8,32,10,2,40),(9,16,8,18,1,48),(9,16,32,17,1,48),(48,1,32,3,16,9),(9,32,8,34,1,48),(36,8,32,9,1,40),(18,1,16,3,2,24),(6,8,4,24,2,40),(18,1,8,3,2,9),(6,32,2,36,4,34),(20,8,4,24,16,40),(5,16,4,24,1,48),(3,16,1,18,2,24),(5,32,1,36,4,33),(3,8,2,9,1,24),(5,8,4,9,1,40),(6,16,4,18,2,48),(9,2,16,3,1,18),(36,1,8,5,4,9),(36,2,16,6,4,18),(40,2,1,10,8,3),(48,2,32,6,16,10),(40,1,2,9,8,3),(12,32,4,40,8,48),(17,2,16,6,1,34),(17,2,16,10,1,34),(5,2,1,6,4,3),(9,2,1,10,8,3),(17,2,16,3,1,48),(3,32,1,34,2,48),(3,16,2,17,1,48),(5,16,4,17,1,36),(5,32,16,36,4,48),(9,32,16,40,8,48),(6,16,32,20,4,48),(10,16,32,24,8,48),(20,1,16,5,4,48),(20,1,32,5,4,33),(20,2,16,6,4,48),(36,2,32,6,4,48),(5,2,16,6,4,18),(9,2,8,18,1,34),(9,32,1,40,8,33),(40,16,32,18,2,48),(12,32,4,40,8,36),(12,2,8,6,4,40),(40,2,32,3,8,18),(40,1,32,9,8,48),(40,1,32,3,8,17),(40,2,32,10,8,48),(17,4,16,6,1,36),(36,1,32,5,4,48),(9,32,8,34,2,40),(3,32,1,34,2,33),(17,4,16,5,1,48),(33,4,32,5,1,48),(18,4,16,6,2,48),(34,4,32,6,2,48),(17,2,16,6,4,18),(33,2,32,18,1,34),(40,4,32,6,2,36),(40,2,32,6,4,34),(24,2,8,18,16,40),(9,16,8,18,2,24),(3,4,32,6,2,36),(3,8,4,10,2,12),(3,4,8,6,2,12),(3,4,16,6,2,20),(6,16,4,34,2,36),(9,4,8,6,2,12),(3,8,4,9,1,12),(3,16,4,17,1,20),(3,16,4,18,2,20),(3,16,1,20,2,48),(3,8,1,12,2,48),(3,8,2,9,1,12),(3,16,2,17,1,20),(6,8,4,9,2,48),(5,8,16,9,1,48),(3,4,2,5,1,12),(40,4,32,12,8,48),(5,16,32,20,4,48),(3,16,1,18,2,20),(24,2,32,10,8,36),(6,8,32,10,2,48),(10,32,8,36,2,48),(6,1,4,3,2,20),(6,1,4,3,2,36),(5,2,4,3,1,20),(5,2,4,3,1,36),(20,2,16,3,4,10),(10,32,8,34,2,48),(17,32,16,34,2,48),(33,16,32,18,2,48),(9,4,2,20,1,36),(10,4,2,20,1,36),(10,16,8,18,2,48),(3,4,16,5,1,20),(3,8,32,9,1,40),(12,1,8,20,4,40),(5,8,1,12,4,9),(6,8,2,12,4,10),(5,8,16,33,1,48),(5,16,8,33,1,40),(3,16,2,20,1,18),(20,2,16,3,1,18),(3,32,8,33,1,40),(10,4,8,5,1,12),(24,1,16,5,4,48),(17,8,32,24,16,40),(5,2,8,3,1,10),(5,2,1,10,4,48),(5,2,4,3,1,12),(3,8,1,10,2,12),(17,8,16,12,4,48),(18,4,16,12,8,48),(9,2,8,3,1,24),(17,2,16,3,1,24),(9,2,8,6,4,10),(5,32,2,36,4,48),(9,32,16,33,1,48),(12,16,8,36,4,48),(10,32,16,34,2,48),(12,16,32,24,8,48),(12,1,32,9,8,48),(3,32,16,34,2,48),(3,16,32,18,2,48),(3,4,32,6,2,48),(17,4,32,20,16,36),(3,16,1,34,2,33),(10,16,8,34,2,48),(3,8,2,12,4,40),(3,4,2,12,8,36),(6,1,4,9,2,17),(12,1,8,3,4,33),(18,32,16,36,4,48),(10,16,8,20,4,48),(10,32,8,36,4,48),(3,8,1,12,2,9),(6,32,8,34,2,48),(5,32,8,33,1,48),(9,16,8,33,1,48),(12,1,32,17,16,33)],[[],[1],[2,1],[3,2,1],[4,3,2,1],[0,1],[0,2,1],[0,3,2,1],[0,4,3,2,1],[1,0,2,1],[1,0,3,2,1],[1,0,4,3,2,1],[2,1,0,3,2,1],[2,1,0,4,3,2,1],[3,2,1,0,4,3,2,1],[0,1,2,3,4],[0,1,2,1,3,4],[0,1,2,3,2,1,4],[0,1,2,3,4,3,2,1],[1,2,3,4],[1,2,1,3,4],[1,2,3,2,1,4],[1,2,3,4,3,2,1],[2],[3,2],[4,3,2],[3],[4,3],[2,3],[2,4,3],[3,2,4,3],[1,0,2,1,3,2],[0,1,0,2,3],[0,1,2,1,0,3],[0,1,2,3,2,1,0],[1,0,2,3],[1,2,1,0,3],[1,2,3,2,1,0],[0],[0,2],[0,3,2],[2,3,4],[2,3,2,4],[2,3,4,3,2],[4],[3,4],[0,1,2,1,0,3,4],[0,1,2,3,2,1,0,4],[0,1,2,3,4,3,2,1,0],[1,2,1,0,3,4],[1,2,3,2,1,0,4],[1,2,3,4,3,2,1,0],[2,1,0,3,4],[2,3,2,1,0,4],[2,3,4,3,2,1,0],[2,1,0],[3,2,1,0],[4,3,2,1,0],[0,2,1,3,2,4,3],[0,1,3,2,4,3],[0,1,0,2,1,3,4],[0,1,0,2,1,3,4,3],[2,1,3,2,4,3],[1,3,2,4,3],[1,0,2,1,3,4],[1,0,2,1,3,4,3],[1,0,3,4],[1,0,2,1,4],[2,3,4,3],[3,4,3],[1,0,2,1,4,3,2],[0,4,3],[0,4],[0,3],[0,3,4],[1,0],[1,0,4,3],[1,0,4],[1,0,3],[0,1,0,2,4],[0,1,2,1,0,4],[0,1,2,3,4,3],[0,1,2,3],[1,0,2],[1,2,1,0],[1,2,4,3],[0,1,4],[0,2,4],[0,2,1,4],[0,2,1,3,2,4],[0,1,3,2,4],[0,1,2,3,2,1],[0,1,2,1,3],[0,1,0,2,1,0,3,4],[2,1,3,2,4],[1,3,2,4],[1,2,3,2,1],[1,2,1,3],[1,0,2,1,0,3,4],[1,2,3],[1,0,2,1,0],[2,3,2],[1,0,2,1,3,2,4],[1,2,3,2,4],[1,3],[0,2,1,3,2],[2,1,0,3],[2,3,2,1,0],[0,1,2,1,0,4,3],[0,1,3],[0,1,3,2,1,0,4,3],[2,4],[2,1,3,2],[3,2,4],[3,4,3,2],[0,1,2,4,3],[0,1,2,1,0,3,2,1,4],[0,1,2,1,0,3,2,1,4,3],[1,2,1,0,3,2,1,4],[1,2,1,0,3,2,1,4,3],[0,1,2,4],[0,1,2],[1,2],[1,2,4],[3,2,1,0,4],[3,4,3,2,1,0],[0,1,0,2,1,3,2,4],[0,2,3,4],[0,2,1,3,2,1,0,4,3,2,1],[0,1,3,2,1,0,4,3,2,1],[0,1,0,2,1,3,2,4,3],[0,1,2,3,2,1,0,4,3,2,1],[0,1,0,2,1,4,3],[0,1,0,2,1,3],[0,1,0,2,1,3,2,1,0,4,3,2,1],[2,1,3,2,1,0,4,3,2,1],[1,3,2,1,0,4,3,2,1],[1,0,2,1,3,2,4,3],[1,2,3,2,1,0,4,3,2,1],[1,0,2,1,4,3],[1,0,2,1,3],[1,0,2,1,3,2,1,0,4,3,2,1],[2,3,2,4,3],[2,1,0,3,2,1,0,4,3,2,1],[1,0,3,2,1,0,4,3,2,1],[2,3,2,1,0,4,3,2,1],[0,1,4,3],[0,1,3,4],[1,4,3],[1,4],[1,3,4],[0,1,0],[0,3,2,4,3],[1,0,3,2,4,3],[0,2,4,3],[0,1,0,3],[0,1,2,3,2,4,3],[0,1,2,3,2],[1,2,3,4,3],[0,2,1,4,3],[0,1,0,2,1,0,3,4,3],[2,1,4,3],[1,2,1,0,4,3],[1,0,2,1,0,3,4,3],[2,1,0,4,3],[2,1,0,4],[0,2,1,3],[0,1,0,2,1,0,4],[0,1,0,2,3,4,3],[2,1,3],[0,2,1,3,2,4,3,2],[0,1,2,1,4,3],[0,1,0,2,3,4],[1,0,2,3,4,3],[0,2,1,4,3,2],[0,1,3,2,4,3,2],[0,2,1,0,3,4,3],[2,1,0,3,4,3],[0,1,0,3,4,3],[1,0,3,4,3],[1,0,2,1,3,4,3,2],[0,1,2,1,0],[0,2,3],[0,1,2,1,4],[0,1,0,2,4,3],[1,2,1,4],[1,0,2,4,3],[1,3,2,1,0,4,3],[3,2,1,0,4,3],[1,0,2,3,4],[0,1,3,2],[0,2,1,0,3,2,4,3],[0,1,0,3,2,1,4,3],[0,1,0,2,1,0,3,2,4],[2,1,0,3,2,4,3],[1,0,3,2,1,4,3],[1,0,2,1,0,3,2,4],[0,1,2,1,3,2],[1,2,1,3,2],[0,1,0,2],[0,1,2,4,3,2],[0,1,3,2,4,3,2,1,0],[0,1,0,2,1,0,3],[0,1,0,2,1,3,2,1,0],[1,0,2,1,0,3],[1,3,2],[1,0,2,1,3,2,1,0],[1,0,2,1,3,2,4,3,2],[0,1,0,2,1,3,4,3,2],[1,0,2,1,0,3,2,1,4,3,2],[1,0,2,1,3,2,1,4,3,2],[1,0,2,1,3,2,1,0,4,3],[1,0,2,1,3,2,4,3,2,1,0],[0,1,2,4,3,2,1,0],[2,1,0,3,2,1,4,3,2],[0,2,1,3,2,4,3,2,1],[0,1,2,1,3,2,4,3],[0,1,2,1,3,2,1,4,3],[0,1,2,3,2,4],[2,1,3,2,4,3,2,1],[1,3,2,1,4,3],[0,1,3,2,1,4,3],[0,1,2,1,4,3,2],[1,2,3,2],[1,2,3,4,3,2],[0,2,3,2,1],[2,1,4,3,2],[0,2,3,2,4],[1,0,2,4,3,2,1],[0,2,3,2],[1,0,2,1,3,2,4,3,2,1],[0,1,0,4,3,2],[1,0,3,4,3,2],[0,3,2,4],[0,1,4,3,2],[0,2,3,2,1,4,3,2,1],[0,1,2,1,3,2,1,0],[0,2,1,3,4,3,2],[1,0,2,3,2,1,4,3,2],[1,0,2,1,0,4,3,2],[0,1,2,3,4,3,2],[0,1,2,3,2,4,3,2],[1,2,3,2,4,3,2],[1,0,2,1,0,3,2,1],[0,1,0,2,1,4,3,2],[1,0,2,1,0,3,2,1,4,3],[0,2,1,3,4],[2,1,0,3,2,1,4,3],[0,1,0,2,1,0,4,3,2],[0,1,2,1,0,4,3,2],[0,1,2,1,0,3,4,3],[1,0,2,1,3,2,1],[0,1,3,4,3,2],[1,2,1,0,3,2,1,4,3,2,1,0],[2,1,3,2,1,4,3,2],[1,3,2,1,4,3,2],[0,1,2,1,0,3,2,1,4,3,2],[1,0,2,1,3,2,1,4,3],[1,2,3,2,1,4,3],[1,2,1,3,4,3],[0,1,2,1,0,3,4,3,2],[0,1,0,2,3,2,4],[1,0,2,3,2],[0,1,2,1],[0,1,2,1,0,3,2,1,0,4,3,2,1,0],[0,3,2,1,4,3,2],[0,1,2,1,3,2,4],[0,1,0,2,3,2,1,4,3,2],[0,1,2,3,2,1,4,3,2],[0,4,3,2],[3,2,1,4,3,2]])
theorem mtopW : TabsP false mtopR mtopT mtopt := ⟨cutsGood mtopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def mtopD12 : List StD := [
([mw0,mw1,mw2,mw3,mw9,mw23],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003],[0,10000,30002,10004,10005],[0,10000,30003,10006,10007],[0,10000,30004,10008,10009],[1,10002,30005,10010,10011],[1,10002,30006,10012,10013],[1,10002,30007,10014,10015],[1,10002,30008,10016,10017],[2,10003,30009,10018,10019],[2,10003,30010,10020,10021],[2,10003,30011,10022,10023],[3,10005,30012,10024,10025],[3,10005,30013,10026,10027],[4,10007,30014,10028,10029]])]
noncomputable def mtopD11 : List StD := [
([mw0,mw1,mw4,mw2,mw3,mw9,mw23],[[0],[],[0,30015,10003],[0,30016,10005],[0,30017,10007],[0,30018,10009],[],[1,30019,10011],[1,30020,10013],[1,30021,10015],[1,30022,10017],[5,6,2,30000,10003],[6,3,30023,10005],[6,4,30024,10007],[6,7,30025,10009],[5,10003,30000,10018,10019],[5,10003,30026,10020,10021],[5,10003,30027,10022,10023],[8,10007,30028,10024,10025],[9,10009,30029,10026,10027],[8,10007,30030,10028,10029]])]
noncomputable def mtopD10 : List StD := [
([mw0,mw1,mw2,mw3,mw9,mw24,mw25],[[10,11,30031],[10,30032,10003],[10,30033,10005],[10,30034,10007],[],[10,11],[11,30035,10011],[11,30036,10013],[11,30037,10015],[11,10],[],[12,10005,30009,10018,10019],[13,10007,30010,10020,10021],[14,10011,30000,10003,30038],[14,10003,30038,10011,30000],[12,10005,30012,10024,10025],[12,10013,30023,10005,30039],[12,10005,30039,10013,30023],[13,10015,30024,10007,30040],[13,10007,30040,10015,30024],[10]]),
([mw0,mw1,mw4,mw2,mw12,mw3,mw9,mw23],[[15],[],[15,5,16],[],[15,30016,10005],[15,30017,10007],[15,30018,10009],[],[5,15],[],[16,30020,10013],[16,30021,10015],[16,30022,10017],[5],[],[17,6,30000,10005],[6,30026,10007],[6,30027,10009],[],[5,30041,10019],[5,30042,10021],[5,30043,10023],[17,18,19,30000,10005],[18,8,30026,10007],[18,9,30027,10009],[17,10005,30000,10024,10025],[17,10005,30044,10026,10027],[20,10009,30045,10028,10029]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw23],[[15,16,5],[15,16],[],[15,30046,10005],[15,30047,10007],[15,30048,10009],[16,15],[],[16,30049,10013],[16,30050,10015],[16,30051,10017],[],[5,30052,10019],[5,30053,10021],[5,30054,10023],[30055,3,10024,30000,10005],[30056,4,10025,30026,10007],[30057,7,10027,30027,10009],[30012,10005,10007,10024,10025],[30013,10005,10009,10026,10027],[30014,10007,10009,10028,10029]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw9,mw23],[[21],[],[21,5,30058],[21,19,30059],[21,30060,30015],[21,30060,10007],[21,30061,10009],[],[5,22,30062],[19,22,30063],[22,30064,30019],[22,30064,10015],[22,30065,10017],[5,30041,30052],[19,30045,30066],[23,24,30000,30009],[23,25,30024,30009,10007],[23,26,30025,30067,10009],[5],[],[5,30041,10021],[5,30068,10023],[],[19,30045,10025],[19,30069,10027],[27,10007,30031,30000,10021],[28,10009,30070,30044,10023],[27,10007,30000,10028,10029]])]
noncomputable def mtopD9 : List StD := [
([mw0,mw1,mw2,mw14,mw26,mw27],[[29,30,10000,30000,10001,10002],[29,10001,30001,10000,10003],[29,10000,30000,10004,30027],[29,10000,30044,10004,30026],[29,10000,30045,10006,30000],[30,10002,30005,10010,10011],[30,10002,30038,10012,30071],[30,10002,30072,10012,30073],[30,10002,30074,10014,30038],[31,10003,30075,10018,30076],[31,10003,30077,10018,30078],[31,10003,30066,10020,30075],[32],[33],[32]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw27],[[34,35,30009],[34,30079,10003],[34,30080,10005],[],[34,30081,30082],[34,36],[35,30083,10011],[35,30084,10013],[35,30019,30085],[],[35,37],[38,10003,30009,10018,10019],[38,10011,30001,10003,30072],[38,10003,30086,10011,30000],[38,10003,30000,10020],[39,10013,30002,10005,30087],[39,10005,30088,10013,30023],[39,10005,30023,10024],[40,41,30000,42,43],[34],[35]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw28,mw26],[[44],[],[44,45,30089],[44,46,30090],[44,30091,10007],[44,30060,30092],[44,30093,30082],[],[45,47,30094],[46,47,30095],[47,30096,10015],[47,30064,30097],[47,30098,30099],[45,30028,30052],[46,30026,30066],[48,49,50,30024,10007],[49,51,30000,30009,30023,30055],[49,52,30023,30100,30000,30075],[45,46,30024],[45,30101,10021],[],[45,46],[46,30024,10025],[46,45],[],[48,10007,30000,10021,30023],[48,10007,30023,10025,30000],[45]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw25,mw29],[[53,54,30102],[53,55,56],[53,30033,10005],[53,30034,10007],[],[53,54],[],[54,55,30062],[54,30019,10013],[54,30103,10015],[54,53],[],[54,10016],[55,30041,10019],[55,30042,10021],[55],[55,10022],[],[57,10007,30012,10024,10025],[58,10013,59,30038,10005],[58,10005,30000,10013,30001],[58,10013,30000,10005],[57,10015,59,30073,10007],[57,10007,30026,10015,30104],[57,10015,30026,10007],[53],[],[54]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw30],[[60,30099,30031],[55,30028,30105],[61,10008,30002,30033,10005],[61,10008,30003,30034,10007],[],[61,30027,0,30000,10008,62],[60,55,63],[60,30036,10013],[60,30037,10015],[60,64],[],[55,30106,10019],[55,30107,10021],[55,65],[],[30012,10005,10007,10024,10025],[66,67,10013,30002,10005,30005],[30108,10005,68,30000,10013],[66,69,10015,30003,10007,30109],[30110,10007,70,30026,10015],[63]]),
([mw0,mw1,mw2,mw12,mw3,mw17,mw9,mw23],[[71,72],[71,72,73],[],[71,73],[],[71,30047,10007],[71,30048,10009],[72,71],[],[73,71],[],[73,30050,10015],[73,30051,10017],[],[72,17,30030],[72,17],[72,30041,10021],[72,30068,10023],[17,72],[72],[18,74,10025,30000,30023,10007],[18,75,10027,30044,30111,10009],[],[17,30045,10025],[17,30069,10027],[76,77,10021,30023,30000,10007],[76,66,10023,30111,30044,10009],[30014,10007,10009,10028,10029]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw31,mw28],[[53],[],[53,78,30105],[53,30092,10005],[53,30091,10007],[],[53,30082,54],[],[78,60,30112],[60,30097,10013],[60,30096,10015],[],[60,30099,64],[78,61,30028],[61,30023,10005],[61,30024,10007],[],[61,78],[78,30041,10019],[78,30042,10021],[78,61],[],[79,10005,30028,10024,10025],[79,10019,30000,10005],[79,10005,30000,10019],[80,10021,30026,10007],[80,10007,30026,10021],[78]]),
([mw0,mw1,mw4,mw2,mw12,mw3,mw19,mw9,mw23],[[81],[],[81,82],[],[81,17,10005],[],[81,30017,10007],[81,30018,10009],[],[82,81],[],[82,17,10013],[],[82,30021,10015],[82,30022,10017],[72],[],[17,10005],[],[23,30026,10007],[23,30027,10009],[],[17,72,23],[],[72,30042,10021],[72,30043,10023],[17],[],[18,30000,10007],[18,30044,10009],[],[17,30045,10025],[17,30069,10027],[83,84,20000,10007],[20000,84,20,20001,10009],[10007,10009,10028,10029]]),
([mw0,mw1,mw4,mw2,mw3,mw19,mw9,mw23],[[23,30000],[],[23,72,82],[23,85],[],[23,30017,10007],[23,30018,10009],[],[23,72,81],[23,86],[],[23,30021,10015],[23,30022,10017],[23,72,82],[23,72],[],[23,30024,10007],[23,30025,10009],[72,23],[],[72,30042,10021],[72,30043,10023],[],[17,30113,10025],[17,30114,10027],[20002,8,10028,30000,10007],[20002,9,10029,30044,10009],[20002,10007,10009,10028,10029]]),
([mw0,mw1,mw4,mw2,mw12,mw3,mw9,mw14,mw23],[[87],[],[87,88],[],[87,17,30059],[87,83,30115],[87,30116,30015],[87,30117,10009],[],[88,87],[],[88,17,30063],[88,83,30085],[88,30118,30019],[88,30119,10017],[89],[],[17,90,30045],[83,90,30044],[90,30012,30000],[90,30012,10009],[],[17,89,30030],[83,89,30029],[89,30041],[89,30041,10023],[17,30045,30113],[83,30044,30111],[91,18,30028,20000,30000],[92,93,20003,10009],[17],[],[17,30045,10027],[],[83,30044,10029],[20000,10009,20004,10027]]),
([mw32,mw0,mw1,mw2,mw3,mw33,mw9,mw23],[[],[18,94,23,24],[18,94,23,95,96],[18,23,97,98],[],[18,23,30056,30120],[18,23,30057,30121],[18,23,99,30122],[18,23,95,30023],[18,23,97,30000],[23,100,30000],[18,23,10006],[18,23,10008],[18,23,95,97],[18,23,95],[],[18,23,30122,10015],[18,23,30123,10017],[18,95,23],[],[18,95,30023,10021],[18,95,30111,10023],[],[97,30000,10025],[97,30044,10027],[100,30000,10015],[100,30044,10017],[20005,10015,10017,10028,10029]]),
([mw0,mw1,mw2,mw12,mw3,mw19,mw9,mw23],[[81,72],[81,72,82],[],[81,30046,10005],[],[81,30047,10007],[81,30048,10009],[72,81],[],[82,30049,10013],[],[82,30050,10015],[82,30051,10017],[],[72,30052,10019],[],[72,30053,10021],[72,30054,10023],[18,101,30055],[],[18,30056,10025,20006,30000,10007],[18,30057,10027,20006,30044,10009],[],[101,10005,20006,30045,10025],[101,10005,20006,30069,10027],[20006,77,10028,30000,10007],[20006,66,10029,30044,10009],[20006,10007,10009,10028,10029]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw23],[[23,102,103,10000,72],[23,102,72,82],[23,10000,104],[],[23,10000,30003,30047,10007],[23,10000,30004,30048,10009],[23,103,72,82,81],[23,82,86],[],[23,82,30050,10015],[23,82,30051,10017],[102,72,105],[],[102,72,30053,10021],[102,72,30054,10023],[],[101,10005,30012,30124,10025],[101,10005,30013,30125,10027],[30056,106,10028,30000,10007],[30057,59,10029,30044,10009],[30014,10007,10009,10028,10029]]),
([mw34,mw0,mw1,mw2,mw3,mw9,mw35,mw23],[[],[],[107,108,30041],[108,109,30045],[108,110,30044],[108,30031],[108,30057,30031],[108,111,30000],[107,111,10000],[109,111,10004],[108,111,10006],[111,10000],[111,10008],[107,108,10010],[108,109,10012],[108,110,10014],[108,10010],[108,10016],[107,108],[107,108,109],[],[107,30043,10023],[108,107],[],[109,30114,10027],[],[108,30025,10029],[20007,59,10009,30000,10023]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw35,mw23],[[108,111,30000],[],[111,89,30041,30058],[111,101,112,30045,30059],[108,111,27,30044,30115],[111,10001,20007,30126,30000,30015],[111,10001,20007,30126,10009],[],[108,111,89,30127,30062],[108,101,112,30074,30063],[108,27,30072,30085],[108,10002,20007,30102,30038,30019],[108,10002,20007,30102,10017],[111,89,30041],[101,112,30045],[108,27,30044],[20007,113,6,30031,30000],[20007,114,10023,30025,10009],[111,89,112,27],[108,111,89,112],[],[111,89,30043,10023],[108,101,112,89],[],[101,112,30114,10027],[],[108,27,30025,10029],[20007,59,10009,30000,10023]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw19,mw9,mw23],[[105],[],[105,72,30058],[105,101,30059],[105,101,30015],[],[105,30060,10007],[105,30061,10009],[],[72,23,30062],[101,23,30063],[101,105],[],[23,30064,10015],[23,30065,10017],[72,23,30052],[101,72],[101],[],[23,30009,10007],[23,30067,10009],[72],[],[],[72,30041,10021],[72,30068,10023],[],[],[101,30045,10025],[101,30069,10027],[],[101,30000,10021],[101,30044,10023],[108,84,27,30000,10007],[115,84,28,30044,10009],[10007,10009,10028,10029]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw9,mw23,mw27],[[116],[],[116,117,30128],[116,118,30129],[116,30130,30131],[116,27,30132],[116,28,30133],[116,30134,30060],[],[117,119,30135],[118,119,30136],[119,30137,30138],[27,119,30139],[28,119,30140],[119,30141,30064],[117,30142,30143],[118,30030,30144],[120,121,20006,20002,30014],[27,30044,30070],[28,30000,30031],[20006,23,20008,20009,30009],[117],[],[117,27,30029],[117,28,30028],[117,30145,30041],[],[118,27,30027],[118,28,30026],[118,30014,30045],[27,30067,30025],[28,30009,30024],[20002,20009,101,20007,20010,30000],[27],[],[]])]
noncomputable def mtopD8 : List StD := [
([mw0,mw1,mw4,mw2,mw14,mw26,mw27],[[29],[],[29,30005,10003],[29,30005,30146],[29,30086,30109],[29,30147,30005],[],[122,10003,30,30001,10011],[30,30001,30148],[30,30149,30104],[30,30150,30001],[122,123,124,30000,10003],[123,125,30000,30027],[123,52,30044,30026],[123,126,30045,30000],[122,10003,30000,10018,30027],[122,10003,30044,10018,30026],[122,10003,30045,10020,30000],[127],[92],[127]]),
([mw0,mw1,mw2,mw14,mw21,mw26,mw27],[[29,30005,10002],[29,30151,10003],[29],[],[29,10004],[29,10006],[128,10003,30005,10010,10011],[129,10002,125,30027,10012],[129,10010,30000,10002],[129,10002,30000,10012,30026],[129,10002,30026,10014,30000],[128,10003,125,30148,10018],[128,10011,30001,10003],[128,10003,30001,10018,30104],[128,10003,30104,10020,30001],[],[125,130],[125,130],[131],[131],[125]]),
([mw0,mw1,mw2,mw14,mw26,mw36],[[29,30005,10002],[29,30151,10003],[29,132],[29,133],[],[30005,10002,10003,10010,10011],[134,135,10002,30038,10012,30072],[136,137,10002,30072,10012,30038],[30152,10010,138,30000,10002],[134,139,10003,30075,10018,30077],[136,140,10003,30077,10018,30075],[30153,10011,141,30001,10003],[134,136,70,142],[132],[132]]),
([mw0,mw1,mw8,mw13,mw26,mw27],[[143,144,10000,30000,10001,10002],[143,10001,30000,10000,30030],[143,10001,30026,10000,30029],[143,10000,30029,10004,30026],[143,10000,30030,10006,30000],[144,10002,30038,10010,30152],[144,10002,30073,10010,30154],[144,10002,30154,10012,30073],[144,10002,30152,10014,30038],[145],[146,147],[120,126,30000,148,149],[146,150,30000,151,152],[147],[145]]),
([mw0,mw1,mw2,mw5,mw11,mw26,mw27],[[153,154,30075],[153,30155,10003],[],[153,30059,30115],[153,155],[153,30156,30157],[154,30075,10011],[154,30085,30063],[],[154,30158,30099],[154,155],[156,10011,30001,10003,30073],[156,10003,30109,10011,30000],[156,10003,30000,10018,30073],[156,10003,30073,10020,30000],[157,158,30000,30074,30044,30027],[153],[159,160,30000,161,162],[157,52,30073,163,164],[154],[159,160,130]]),
([mw0,mw1,mw2,mw5,mw14,mw37,mw27],[[29,30005,10002],[29,30151,10003],[],[29,165],[],[29,30082,133],[166,10002,20011,10010,10011],[166,10010,20011,10002,30000],[166,10002,30000,10012,30044],[166,10010,20011,10002,30000],[166,10002,30000,10014],[20011,10011,158,30001,10003],[20011,10003,139,30001,10018,30149],[20011,10011,140,10003,30001],[20011,10003,141,30001,10020],[29],[],[158,165],[165],[158],[165]]),
([mw0,mw1,mw4,mw2,mw3,mw13,mw26,mw27],[[167],[],[167,168,30159],[167,169,30109],[167,30060,30108],[167,30160,30032],[167,30060,30121],[],[168,170,30161],[169,170,30104],[170,30064,30162],[170,30163,30035],[170,30064,30122],[168,30111,30164],[169,30000,30078],[171,135,20006,20012,30165],[20006,172,20013,20001,30075],[20006,173,20008,20009,30009],[168,169,30000],[],[168,20014,30028],[168,174],[169,20015,30027],[],[169,127],[20012,20001,175,20014,20015,176],[168],[169]]),
([mw0,mw1,mw2,mw3,mw10,mw18,mw28,mw27],[[177,178],[177,179,30166],[177,30167,10005],[],[],[177,30168,30082],[177,180],[179,181,30062],[181,30019,10013],[181],[],[181,30019],[181,182,183],[179,30028,10019],[179,184,30041],[179,20016,30041],[],[179,178],[10013,184,30077,10005],[10019,185,10005,20017],[10005,20016,10019,20018],[10005,186,182,20019,10024],[],[184,30077,187],[177],[20017,20018,188,30001,182,10029],[180],[178]]),
([mw0,mw1,mw2,mw3,mw10,mw30,mw27],[[189,181,30099,30140],[189,38,30028,30166],[189,10006,20020,30080,10005],[],[189,10006,20020,30081,30000,30082],[189,190,61,20020,10006,191],[189,181,38,192],[189,181,30097,10013],[189,181,30019],[],[189,181,193],[38,30169,10019],[38,30041],[],[38,194],[20020,10013,195,10005,30002],[20020,10005,196,10013,30000],[20020,10005,197,10024,30000],[20020,198,199,10028,10029],[20020,190,61,192],[20020,190,193]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw27,mw38],[[200,201,30137],[200,38,30170],[200,30171,10005],[],[200,30081,30172],[200,126,202],[200,203,204],[201,38,30062],[201,30097,10013],[201,30019,30173],[],[201,126,205],[201,206,193],[38,30041,10019],[38,203,207],[38,206,194],[38],[],[10013,208,10005,20021],[10005,209,10013,20022],[10005,126,30000,10024],[10005,210,203,20007,10019],[20021,20022,184,206,203,211],[200],[200],[201],[201],[]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw38],[[212,69,10006,20023,30120,30122,30009],[212,10006,38,30023,30174],[212,10006,20023,30080,10005],[],[212,10006,20023,30115,30000,30121],[212,30063,10,20023,10006,213],[69,38,30087,30112],[69,10016,20023,30084,10013],[212,69,10016,20024,30099,30072,30123],[],[69,30175,6,20023,10016,214],[20023,38,30055,10019],[212,38,215],[38,216],[],[212,146,10013,20024,10005,30087],[20023,10005,217,10013,30023],[20023,10005,218,10019,30000],[212,198,184,30000,10028,10029],[212,215],[20023,216]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw27,mw39],[[219,121,30009],[219,30115,10003],[219,30171,10005],[],[219,220],[219,221],[],[121,30099,10011],[121,30097,10013],[121,40,30085],[],[121,219],[],[10003,10005,10018,10019],[10011,40,30072,10003],[10003,222,10011,30000],[10003,223,203,30000,10020],[10018,38,10003,30000],[10013,40,30087,10005],[10005,224,10013,30023],[10005,225,203,30023,10024],[10019,210,10005,30023],[40],[219],[],[121],[],[]]),
([mw0,mw1,mw2,mw3,mw10,mw11,mw28,mw26],[[226,227,30070],[226,228,30058],[226,229,30059],[],[226,227],[226,30061,30016],[226,30160,30015],[227,228,30062],[227,229,30063],[227,226],[],[227,30065,30020],[227,30163,30019],[228,229,30024],[228,30041,30176],[228,30127,30177],[],[228,229],[229,30045,30178],[229,30074,30179],[229,228],[],[226],[198,230,20025,20003,30006],[20025,184,20026,20001,30005],[188,20003,20027,20028,30002],[20027,20001,136,20029,20030,30001],[228]]),
([mw0,mw1,mw2,mw3,mw10,mw11,mw28,mw36],[[177,191,30180],[177,231,30105],[177,30181,10005],[],[177,191],[177,30015,232],[],[191,231,30094],[191,30097,10013],[191,177],[],[191,30019,30099],[191,182,183],[231,30028,10019],[231,184,30182],[231,30182,30041],[],[231,184],[10013,184,30039,10005],[10005,233,10013,20031],[10005,234,10019,20018],[10013,229,10005,20001],[177],[184,231],[],[20031,20018,188,30001,182,10029],[191],[231]]),
([mw0,mw1,mw4,mw2,mw3,mw18,mw28,mw27],[[177],[],[177,235,30006],[177,30183,10005],[],[177,30184,30121],[177,30184,191],[],[235,181,30002],[181,30185,10013],[],[181,30186,30122],[181,30186,183],[235,189,30023],[189,30023,10005],[],[189,30077,30000],[189,20008,191],[235,30028,10019],[235,20016,30029],[],[235,178],[10019,236,10005,20000],[10005,20016,10019,20018],[10005,237,238,20004,10024],[20000,20018,239,238,20016,240],[189],[235]]),
([mw0,mw1,mw4,mw2,mw12,mw3,mw9,mw26,mw27],[[241],[],[241,242],[],[241,30090],[241,30120],[241,20001],[241,20009],[],[242,241],[],[242,30095],[242,30123],[242,20030],[242,20032],[168],[],[135,30026],[135,30000],[135,20001],[135,20009],[],[168,30113],[168,30111],[20001,20018],[20009,20023],[118,20002],[127,20012],[243,20001],[244,20009],[245,30000],[],[20009,246],[20001,245],[],[20001,245]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw26,mw27],[[241,168],[241,168,247],[],[241,247,30110],[241,20033,30108],[241,20033,30047],[241,20033,30046],[168,241],[],[247,242,30187],[242,20033,30162],[242,20033,30050],[242,20033,30049],[],[168,247,30188],[168,20033,30164],[168,20033,30053],[168,20033,30052],[247,20033,30124],[20033,32,30165],[20033,52,30056],[20033,126,30055],[247,20033,30000],[],[247,20033,246],[20033,248,247],[],[247]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw28,mw40,mw26],[[249],[],[249,30089],[249,30090],[249,250],[249,20034],[],[249,30082],[],[250,30094],[250,30095],[251,252],[250,249],[],[250,30099],[49,20006],[49,30066],[49,250],[49],[],[49,20035],[253,30113],[250,254],[],[],[253,254],[250,10025],[239,253],[243,255],[],[250,254],[10025,250],[250,10025],[],[253],[243,254]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw25,mw41],[[115,20002,30102],[115,256,257],[115,258],[115,20002,10007],[],[115,20002,259],[],[20002,256,30062],[20002,260,30063],[20002,10007,10015],[115,20002,10016],[],[20002,11,10016],[256,115],[256,20002,10021],[115,256,257],[256,20002,10022],[],[260,20002,10025],[115,256],[260,20002,10026],[],[115,20002,10007],[20002,10007,10015],[20002,10015,10007],[115,20002,259],[],[20002,11,10009]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw28,mw42],[[49,30000],[],[49,20001,30105],[49,261],[49,20001,10007],[49,30172,10009],[],[],[49,20001,30112],[49,262],[49,20001,10015],[49,30189,10017],[],[49,20001,30028],[49,261],[49,20001,10007],[49,20035,10009],[],[20001,263,30024],[20001,10007,10021],[],[20001,5,264],[263,20001,10025],[263,255],[],[20001,10009,10021],[20001,10021,10007],[20001,5,10009]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw43],[[265,10010,20036,30082,30099,30031],[265,10011,20037,30032,30028,30105],[20036,195,10013,20005,30033,30026,30190],[20036,10008,10015,30034,10007],[],[20036,30044,0,10008,10009],[265,266,267,10012,10010,10011],[265,10010,267,10012,10013],[265,10010,20036,30037,10015],[265,10010,20036,10016,10017],[],[265,10011,268],[265,10011,20037,30107,10021],[265,10011,20037,10022,10023],[],[20036,10013,195,20005,30056,10025],[20036,10013,195,20005,10026,10027],[],[20036,10015,10017,10007,30003],[20036,10007,10009,10015,30000],[20036,30000,0,10017,10009]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw28,mw26,mw38],[[269],[],[269,30191],[269,30192],[269,30132],[269,30193],[269,20038],[269,20025],[],[270,30194],[270,30195],[270,30139],[270,30196],[270,20022],[270,20027],[51,20006],[20006,20013],[20006,20008],[51,20006],[20006,20038],[20013,20025],[271,30113],[239,174],[],[239,271],[],[271,20039],[271,168],[],[271,20039],[239],[184,272],[],[271],[],[271]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw28,mw44],[[273,274,30000],[],[275,274,10001,20004,30089],[273,274,10001,236,20004,30090],[10001,276,20004,30120],[275,274,10001,20004,30197],[10001,274,20004,30082],[],[275,273,10002,20004,30094],[20004,236,30095],[274,273,276,20004,30123],[275,273,10002,20004,30198],[20004,10002,30099],[275,20004,114,30028],[273,236,20004,30066],[274,276,20004,30077],[275,20004,114,30012],[20004,61,30075],[273,275,236,20004,30024],[274,275,276,20004,30023],[],[20004,239,271],[274,273,236,276,277],[275,273,236,278],[],[275,274,276,272],[],[20004,239,271]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw30,mw45],[[267,279,30099,30031],[280,30041,30058],[267,281,30045,30059],[282,49,10015,30034,10007],[],[198,49,283,282,284],[285,49,61,282,286],[279,280,287],[279,281,287],[279,30037,10015],[279,282,288],[],[],[267,280,281,30030],[280,30041,10021],[280,282,289],[],[280,281],[281,30045,10025],[281,282,290],[281,280],[],[10015,291,10007,20040],[10007,292,10015,20041],[10007,293,10015,20042],[198,283,288],[285,61,288],[280]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw25,mw29,mw45],[[294,30137],[294,295],[294,30059],[294,296],[],[294,297],[],[294,298],[296,30062],[297,295],[296,299],[297,294],[],[297,300],[],[296,30030],[299,10021],[301],[296,206],[],[296,206],[296,10025],[299,206],[302],[299,206],[],[299,296],[296,299],[299,296],[296,299],[294],[],[294],[297],[],[303,20002]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw31,mw46],[[267,115,28],[115,304,30089],[267,115,305,30090],[115,20018,10007],[],[],[115,20018,306],[304,20018,30062],[305,20018,30063],[20018,10007,10015],[115],[],[20018,303,10016],[267,304,115],[304,20018,10021],[115,304,307],[304,206,10022],[],[305,20018,10025],[115,305,308],[305,206,10026],[],[115,20018,10007],[20018,10021,10007],[20018,10007,10021],[],[115,20018,306],[20018,6,10009]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw25,mw29,mw41],[[307,30102],[307,257],[307,309],[307,309],[],[307,309],[],[],[309,20043],[309,20044],[309,10015],[20043,307],[],[20044,20043],[61,20043],[256,115],[10015,310],[256],[256,311],[],[],[10015,10025],[115,309],[310,206],[260],[],[10015,309],[310,10015],[10015,309],[10015,309],[307],[],[],[312,309],[61,309],[]]),
([mw0,mw1,mw2,mw3,mw10,mw24,mw47],[[121,313,30009],[121,30199,10003],[121,30181,10005],[],[],[121,30121,180],[121,30019,10011],[121,30020,10013],[121,313],[121,313,314],[],[314],[314],[313,314],[314],[314],[313,314],[314],[313,121],[121],[121]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw24,mw46],[[115],[],[115,315,30105],[115,316,30190],[115,20018,10007],[],[115,20018,317],[],[315,20018,30094],[316,20018,30095],[20018,10007,10015],[115,20018,318],[20018,6,30099],[315,20018,30041],[316,20018,30045],[20018,10021,10007],[115,20018,318],[20018,6,10009],[315,115],[315,20018,10021],[115,315,319],[],[316,20018,319],[115,316,319],[],[115,20018,10007],[20018,10007,10021],[115,20018,317]]),
([mw32,mw1,mw2,mw5,mw33,mw9,mw23],[[23,320,24],[23,321,96],[],[],[23,30110,30200],[23,30201,30157],[23,321,81],[23,81],[],[23,81],[23,81],[321,23],[],[321,81],[321,81],[23],[81],[81],[81],[81],[81]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw30,mw40],[[61,66,30031],[61,322,30105],[61,20020,10005],[61,20020,10007],[],[61],[],[61,66],[61,20020,10013],[61,20020,10015],[61,66,322],[],[],[322,20020,10019],[322,20020,10021],[66,61],[],[],[20020,10005,10025],[66,20020,10005],[20020,10005,10013],[20020,10024,10005],[66,20020,10007],[20020,10007,10015],[20020,10025,10007],[61],[],[]]),
([mw34,mw0,mw1,mw2,mw3,mw9,mw28,mw44],[[],[],[323,20004,30028],[323,273,30026],[323,291,30000],[323,20004,30075],[323,20004,30031],[20004,30000],[323,20004,10000],[323,273,10004],[323,291,10006],[323,20004,10000],[323,20004,10004],[20004,273,10010],[20004,273,291,10012],[20004,273,291,10014],[20004,273,10010],[20004,273,10012],[20004,273,30024],[20004,291,30023],[],[20004,324,325],[273,323],[273,326],[],[291,327],[],[20004,324,325]]),
([mw0,mw1,mw2,mw3,mw9,mw31,mw46],[[267,115,10008,328],[115,10008,328,30028,30105],[267,115,10008,329,30202,30026,30190],[115,10008,20018,30203,10007],[],[115,10001,20018,10008,10009],[267,328,30182,30112],[267,329,265,10002,30204,30073,30205],[267,10002,20018,30206,10015],[],[267,10002,20018,10016,10017],[267,328,330],[328,30107,10021],[328,10022],[],[267,10019,20035,30056,10025],[267,10019,20035,10026,10027],[],[20018,10021,10027,10007,30009],[20018,10007,10009,10021,30000],[20018,24,6,10027,10009]]),
([mw32,mw0,mw1,mw2,mw33,mw9,mw14,mw23],[[],[331,332,24],[331,332,333,96],[],[332,20005,30069],[332,20005,110],[332,20005,30045],[332,334,30001],[332,333,30000],[20005,30000],[332,20005,10006],[332,20005,10006],[332,20005,10009],[332,333,334],[],[332,20005,30149],[332,335],[332,20005,10017],[],[333,20005,30044],[333,336],[333,20005,10023],[20005,335,337],[20005,335],[20005,10009,10017],[],[20005,10009,10029],[20005,10009,10029]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw30,mw43],[[267,338,339,20020,30031],[20020,338,280,30105],[267,338,10013,20020,30059],[20020,10015,10007],[],[20020,30027,10008],[20020,61,10008],[339,280,340],[339,20020,10013],[339,20020,10015],[338,267,339,341],[],[],[267,20020,280,10019],[280,20020,10021],[338,280,342],[],[],[20020,10013,10025],[338,267,10013,20020,10026],[20020,30108],[],[338,20020,10015,10007],[20020,10007,10015],[20020,10007,10015],[20020,340],[20020,61,340],[]]),
([mw0,mw1,mw2,mw3,mw18,mw31,mw27],[[343,121,344],[343,30199,10003],[343,30181,10005],[],[],[343,30015,345],[121,30083,10011],[121,30084,10013],[],[],[121,30019,346],[30009,10003,10005,10018,10019],[347,348,10018,30000,10003,30044],[349,350,10018,30044,10003,30000],[244,351,10003,30000,10020],[347,352,10019,30023,10005,30111],[349,353,10019,30111,10005,30023],[244,354,10005,30023,10024],[344],[121],[121]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw31,mw26],[[355,283,253],[355,253,356],[],[355,30033,30190],[355,30034,10007],[],[355,30046,357],[283,355],[],[283,30036,30205],[283,30037,10015],[],[283,30049,358],[],[253,30106,30113],[253,30052,10021],[253,20],[253,30052,30028],[303,359,30055,30045],[360,359,10025,20012,10007],[253],[20012,359,18,20035,361],[10026,10007,30045,10025],[349,362,283],[],[10021,363,10007,20009],[10007,364,10025,20004],[283]]),
([mw0,mw1,mw2,mw12,mw3,mw17,mw9,mw48,mw23],[[365,366],[365,367],[],[365,367],[],[365,309],[],[365,309],[366,365],[],[367,365],[],[367,368],[],[367,368],[],[366,30030],[366,309],[366,369],[],[366,254],[18,366],[366],[18],[],[18,309],[],[254,30027],[362,309],[254,10027],[254,309],[362,20006],[254,309],[],[10027,10029],[10027,309]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw49,mw23],[[370,90,30000,371],[90,20000,10003],[],[370,90,371,372],[90,373],[],[90,20000,10009],[90,20000,10011],[],[90,371,374],[90,375],[],[90,20000,10017],[],[370,371,20000,30030],[20000,93,10003,30053,30029],[20000,18,10003],[20000,10003,10023],[370,371,376],[377,93,20008,378],[20000,18,376],[20000,10027,10009],[371,90],[],[371,20000,10027],[],[379,20000,10009,380,10029],[20000,10023,10009]]),
([mw34,mw0,mw1,mw2,mw3,mw9,mw35,mw23,mw46],[[],[],[381,30041],[382,30045],[381,30070],[381,30207],[381,30031],[381,30137],[30000],[382,383],[381,384],[385,10006],[382,383],[382,10008],[382,383],[381,386],[383,387],[381,10014],[381,386],[381,10016],[381,386],[381,382],[382,381],[],[385,381],[],[381,384],[],[381,384],[],[],[382,30000],[382,383],[385,382],[382],[]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw35,mw23,mw46],[[30000],[],[388,30058],[389,30059],[390,30208],[115,20025],[391,30126],[392,20045],[],[388,30062],[389,30063],[390,30180],[393,20027],[391,30102],[394,20046],[388,20006],[389,20013],[390,20008],[113,20025],[391,20035],[20008,20045],[388,390],[388,389],[],[388,389],[],[389,388],[],[389,388],[],[],[390,30000],[390,391],[115,390],[390],[]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw36,mw47],[[219,221,30009],[219,30079,10003],[219,30080,10005],[],[219,395,30121],[],[219,221],[221,30083,10011],[221,30084,10013],[221,40,30123],[],[221,219],[],[10003,10005,10018,10019],[10011,40,30072,10003],[10003,395,30000,10011],[10011,214,10003,30072],[10003,213,10011,30000],[10013,40,30087,10005],[10005,395,30023,10013],[10013,353,10005,30087],[10005,396,10013,30023],[395,219],[],[219],[221],[],[219]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw9,mw31,mw27],[[397],[],[397,30105],[397,30190],[397,20002],[397,20047],[],[397,398],[],[399,30112],[399,30205],[20002,20036],[399,20048],[],[398,400],[401,30106],[401,30078],[401,20002],[401,30009],[],[401,398],[402],[],[402,30029],[402,20003],[402,20023],[],[403,30027],[403,20001],[403,20004],[20002,20007],[20007,20002],[20002,20023],[392,401],[],[401]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw31,mw28,mw42],[[294],[],[294,20049],[294,404],[294,404],[],[294,404],[],[],[404,20050],[286,405],[286,405],[],[286,405],[],[49,30041],[49,404],[49,404],[],[49,404],[],[404,20051],[404,10021],[20051,49],[],[78,20051],[10021,10025],[263],[263,406],[],[10021,404],[10025,10021],[10021,404],[49],[],[78,404]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw31,mw28,mw46],[[307],[],[307,30105],[307,30090],[307,250],[],[307,30082],[307,30082],[],[250,30112],[250,30095],[407,252],[],[250,30099],[250,30099],[407,30028],[407,30066],[407,250],[],[407,20035],[407,20035],[253,28],[250,254],[253,407],[],[],[250,10025],[254,255],[79],[],[10025,250],[250,254],[250,254],[407],[407],[]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw31,mw46],[[267,115,30000],[],[253,20018,30105],[267,115,79,20018,30190],[20018,10001,10007],[],[20018,10001,10009],[],[253,20018,30112],[20018,79,30205],[20018,10007,10015],[],[20018,10009,10017],[253,20018,30028],[267,79,20018,30026],[20018,10021,10007],[],[20018,6,10009],[267,253,79,330],[253,20018,10021],[253,407],[],[79,20018,10025],[79,406],[],[20018,10021,10007],[20018,10007,10021],[20018,6,10009]]),
([mw0,mw1,mw4,mw2,mw3,mw19,mw9,mw48,mw23],[[30000],[],[408,409],[408,309],[],[408,309],[],[408,309],[],[408,410],[408,368],[],[408,368],[],[408,368],[408,409],[408,309],[],[408,309],[],[408,309],[411,408],[],[366,408],[],[366,254],[],[411,30027],[411,309],[411,10027],[248,309],[411],[10029,309],[],[10027,10029],[10027,309]]),
([mw0,mw1,mw4,mw2,mw12,mw3,mw9,mw40,mw26],[[412],[],[412,413],[],[412,20052],[412,250],[],[412,309],[],[413,412],[],[413,20053],[413,252],[],[413,368],[253],[],[49,30026],[49,250],[],[49,309],[],[253,20054],[250,254],[],[253,254],[359,30026],[359,250],[],[359,309],[250,414],[17,359],[],[415,250],[250,414],[359]]),
([mw34,mw4,mw2,mw3,mw19,mw9,mw23],[[],[416,23,30209],[23,417,30210],[],[23,30211,30207],[23,30212,30137],[416,23,417],[23,416],[],[23,30024,10007],[23,30025,10009],[416,23],[],[416,30042,10021],[416,30043,10023],[],[417,30113,10025],[417,30114,10027],[20055,418,10028,30000,10007],[20055,59,10029,30044,10009],[20055,10007,10009,10028,10029]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw50,mw23],[[20056,20005,30000],[],[419,420,10001,20000,10003],[419,420,10001,20012,10005],[20056,93,10001,20002,10007],[],[20056,420,10001,20000,10009],[],[419,420,10003,20000,10011],[419,420,10005,20012,10013],[20005,93,10007,20002,10015],[],[20005,420,10009,20000,10017],[419,420,10018,20000,10003],[419,420,10019,20012,10005],[20005,93,10021,20002,10007],[],[20005,420,10023,20000,10009],[20000,20012,10003,10018],[420,419,10003,20002,20000,10021],[],[20000,10003,10023],[420,419,10005,20002,20012,337],[],[20012,10005,10027],[],[20002,10007,10029],[20000,59,10009]]),
([mw0,mw1,mw4,mw2,mw3,mw19,mw9,mw35,mw23],[[30000],[],[421,30058],[421,30059],[],[421,30115],[421,20057],[421,422],[],[421,30062],[421,30063],[],[421,30085],[421,20005],[421,423],[421,20006],[421,20013],[],[421,30044],[421,20057],[421,422],[424,421],[],[425,424],[],[422,254],[],[424,426],[],[422,414],[425,421],[421],[10029,422],[],[422,10029],[422,254]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw9,mw31,mw46],[[427],[],[427,30105],[427,30190],[427,30082],[427,250],[],[427,428],[],[250,30112],[250,30205],[250,30099],[429,252],[],[250,430],[429,30106],[429,30078],[429,30000],[429,250],[],[429,428],[253],[],[250,254],[253,254],[],[],[250,414],[254,414],[],[250,254],[101,429],[],[390,250],[250,254],[429]]),
([mw0,mw1,mw4,mw2,mw3,mw8,mw9,mw50,mw23],[[20058],[],[421,30058],[421,30059],[421,20057],[421,431],[],[421,422],[],[421,30062],[421,30063],[421,20005],[421,432],[],[421,423],[421,20006],[421,20013],[421,20057],[421,431],[],[421,422],[20059],[],[425,254],[],[422,254],[],[425,433],[],[422,414],[425,421],[],[422,254],[],[422,10029],[115,422]]),
([mw0,mw1,mw51,mw2,mw3,mw9,mw35,mw23],[[394,422,10002],[],[110,20007,30058],[394,20007,30059],[20007,113,30115],[20007,113,30015],[20007,10017,10009],[394,422,10002],[394,110,30062],[394,10002,30063],[394,20007,30085],[394,20007,30099],[394,20007,10017],[110,20007,434],[394,20007,435],[20007,113,436],[20007,113,434],[20007,10017,10009],[394,110,437],[110,394],[],[110,20007,10023],[394,110],[],[394,20007,10027],[],[20007,113,10029],[20007,113,10023]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw52],[[362,101],[101,362],[],[362,18,30190],[18,30046,10007],[18,30046,438],[362,101,439],[],[362,101,439],[362,439],[362,439],[],[362,101,439],[101,439],[101,439],[362,18,439],[18,439],[18,439],[362,439],[362,439],[439]]),
([mw32,mw1,mw2,mw3,mw19,mw9,mw23],[[23,362,101],[23,362],[23,102],[],[23,30034,30081],[23,30213,30015],[23,81],[23,81],[],[23,81],[23,81],[81],[],[81],[81],[],[81],[81],[81],[81],[81]]),
([mw32,mw0,mw1,mw2,mw3,mw9,mw53,mw23],[[],[394,386,440,100],[440,100,394],[394,386,100,110],[100,20005,30044],[],[100,20005,30082],[100,20005,30122],[100,20005,30023],[100,20005,30000],[20005,10015,10006],[20005,0,10006],[20005,10006,10009],[100,10012,441],[100,441,10012],[100,20005,10015],[],[100,20005,10017],[100,441,421],[100,20005,442],[],[100,20005,10023],[100,20005,337],[],[100,20005,10027],[],[20005,10015,10029],[20005,10009,10017]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw48,mw23],[[443,444,10000,411],[443,444,10001,10000,445],[10000,444,411,309,10005],[],[10000,408,20033,309,10007],[],[10000,444,20033,309,10009],[419,309,10002,410],[411,368,10013],[],[444,443,10007,20033,368,10015],[],[10002,443,20033,368,10017],[411,20033,10019],[],[444,443,10007,20033,10021],[],[20033,10009,10023],[],[444,411,20033,30027],[411,309,10005],[411,20033,10027],[444,20033,248,411],[411],[20033,10029,10009],[],[20033,10007,10029],[20033,10027,10009]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw40,mw26],[[412,446],[412,447],[],[412,446,30190],[412,20033,10007],[],[412,20033,10009],[448,49,253,412],[],[446,413,30205],[413,20033,10015],[],[413,20033,10017],[],[446,20033,30024],[20033,10007,10021],[],[20033,10009,10023],[446,20033,30026],[20033,10025,10007],[],[20033,18,446],[446,20033,10025],[446,20033,449],[],[20033,10025,10007],[20033,10007,10025],[446]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw50,mw23],[[450,444,10000,411],[419,444,10001,10000,445],[],[450,444,10000,411,309,10005],[10000,93,20033,309,10007],[],[10000,444,20033,309,10009],[419,450,10002,451],[],[411,368,10013],[444,450,10007,20033,368,10015],[],[10002,450,20033,368,10017],[],[450,411,20033,10019],[444,419,10007,20033,10021],[],[20033,10009,10023],[450,411,309,10005],[444,93,10025,411],[],[20033,10027,10009],[444,450,411,20033,10025],[],[411,20033,10027],[],[20033,10007,10029],[20033,66,10009]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw54,mw23],[[392],[],[392,452],[392,452,453],[392,454,455],[],[392,20002,10009],[],[453,20002,30062],[452,20002,30063],[392,20002,30085],[20002,6,10002],[20002,10009,10017],[453,309,10003],[452,309,10005],[392,20002,10007],[20002,6,30000],[20002,10023,10009],[452,392],[392,453,454],[],[453,20002,10023],[392,452,456],[],[452,20002,456],[],[392,20002,456],[20002,10017,10009]]),
([mw55,mw0,mw1,mw2,mw3,mw9,mw53,mw23],[[],[394,386,20036,30019],[20036,420,440,20037,30041],[394,386,20005,30045],[20036,457,30044],[],[20036,10009,30082],[20036,10010,30099],[20036,420,10011,20037,30028],[20036,386,10013,20005,30026],[20036,10015,30000],[20036,30000],[20036,10017,10009],[458,420,10012,386,10011],[10010,420,10012,10013],[20036,10010,10015],[],[20036,10009,10017],[10011,10013,421],[420,20036,10011,386,442],[],[20037,10009,10023],[420,20036,10013,20005,337],[],[20005,10009,10027],[],[20036,10009,10029],[20036,10009,10017]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw50,mw23],[[450,386,10000,411],[419,421,10001,10000,445],[450,386,10000,411,309,459],[],[10000,386,20033,309,10007],[],[10000,386,20033,309,10009],[419,450,459,460],[411,461],[],[422,450,10007,20033,368,10015],[],[250,450,10009,20033,368,10017],[450,411,386,462],[],[459,20033,10021],[],[459,20033,10023],[],[411,20033,10025],[],[411,20033,10027],[20033,30056],[],[20033,10029,10009],[],[20033,10007,10029],[20033,30057,10009]]),
([mw0,mw1,mw2,mw3,mw9,mw50,mw23],[[20057,10000,10010,20002,10001,10002],[20013,10001,10011,20017,10000,10003],[20006,10000,10013,20060,10004,10005],[20057,10000,10015,20002,10006,10007],[],[20057,10000,10017,20002,30048,10009],[20057,10002,10003,20061,10010,10011],[20057,10010,10005,10012,10013],[20057,10010,10007,10014,10015],[],[20057,10010,10009,30051,10017],[20013,10011,10013,10018,10019],[20057,10011,10015,20013,10020,10021],[],[20057,10011,10017,20013,30054,10023],[20057,10013,10015,10024,10025],[],[20057,10013,10017,30125,10027],[],[20057,10015,10017,30057,10029],[20057,59,30057,30000,10017]]),
([mw34,mw0,mw1,mw2,mw3,mw9,mw23,mw56],[[],[],[120,206,20062,30041],[120,206,20063,30045],[20062,206,171,20007,30044],[20062,463,30000],[20062,0,30137],[20062,30000],[20062,10004,10000],[20062,206,10000,20063,10004],[20062,206,10004,20007,10006],[20062,10004,10008],[20062,0,10004],[20062,10012,10010],[20062,20063,10010,10012],[20062,20007,10012,10014],[20062,10012,10016],[20062,6,10012],[464,465,10020,385],[464,466,10018,10020,467],[20062,10020,468],[],[465,466,467,469],[20063,385,326],[],[20007,385,470],[],[]]),
([mw0,mw1,mw4,mw2,mw3,mw9,mw23,mw56],[[20007,30000],[],[20007,238,10001,20062,30058],[20007,238,10001,20063,30059],[20007,10001,30115],[20007,10001,30082],[20007,10001,30015],[],[20007,238,10002,20062,30062],[20007,238,10002,20063,30063],[20007,10002,30085],[20007,10002,30099],[20007,10002,30019],[20007,238,120,20062,30041],[20007,238,120,20063,30045],[20007,171,30044],[20007,463,30000],[20007,6,30000],[471,472,10020,390],[471,390,473],[20062,10020,271],[],[472,390,473,474],[20063,473,278],[],[20007,390,272],[],[]]),
([mw0,mw1,mw2,mw3,mw9,mw57,mw46],[[475,115,393,30137],[475,115,10000],[115,393,10004],[115,10006],[115,10000,476],[115,10000],[475,393,10010],[393,10010,10012],[393,10014],[115,393,477],[393,10010],[475,115],[475,30042,10021],[475,115,393],[],[393,30113,10025],[115,393,478],[],[115,478],[478],[115,393]]),
([mw0,mw1,mw2,mw12,mw3,mw58,mw9,mw23],[[362,17],[17],[],[362,17],[],[17],[17],[362,17],[],[362,17],[],[362,17],[362,17],[],[362,17],[],[17],[17],[362,17],[],[17],[17],[362,17],[362,17],[362,17],[17],[17],[17]]),
([mw0,mw1,mw2,mw3,mw58,mw9,mw23],[[362,17],[17],[362,17],[],[17],[17],[362,17],[362,17],[],[362,17],[362,17],[362,17],[],[17],[17],[362,17],[362,17],[362,17],[17],[17],[17]]),
([mw0,mw1,mw59,mw2,mw3,mw9,mw23,mw44],[[479,480,10002],[],[171,480,10003],[479,20004,30059],[171,20004,30115],[20004,481,30082],[20004,482,30015],[479,480,10002],[479,171,30214],[479,10002,10012],[479,171,10014],[479,20004,10016],[479,20004,10012],[171,480,10003],[479,20004,30045],[171,20004,30044],[20004,481,30000],[20004,6,30062],[479,171,10018],[480,171,10003,10020],[480,171,20004,10022],[480,171,20004,10018],[479,171,481],[479,171],[],[171,479],[],[]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw60],[[362,17],[17],[],[362,17],[17],[17],[362,17],[],[362,17],[362,17],[362,17],[],[362,17],[17],[17],[362,17],[17],[17],[362,17],[362,17],[17]]),
([mw34,mw4,mw2,mw3,mw9,mw35,mw23],[[],[394,483,30209],[394,112,30210],[394,484,30207],[394,30137],[394,30137],[483,30041,10000],[394,30045,10004],[484,30044,10006],[20007,485,6,10000,30000],[20007,10000,10023,10008,10009],[394,483,484],[483,394],[],[483,30043,10023],[394,483],[],[394,30114,10027],[],[484,30025,10029],[20007,59,10009,30000,10023]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw23,mw44],[[486,487,10000,488],[472,487,10001,10000,247],[],[486,487,10000,488,20060,30059],[10000,487,20060,30115],[10000,20060,30082],[10000,487,20060,30015],[472,486,10002,489],[],[488,20064,30063],[472,486,10002,20060,20064,30085],[487,486,10002,20060,20064,30099],[10002,486,20060,20064,30019],[],[486,488,20006,30030],[20006,10003,30029],[487,472,10003,20060,20006,30028],[20006,10003,30041],[486,488,20060,30014],[472,20060,171,30013],[487,20060,323,30012],[20060,18,30000],[488,20060,490],[487,486,488,20060,246],[],[487,472,10025,488],[],[]])]
noncomputable def mtopD7 : List StD := [
([mw0,mw1,mw22,mw7,mw14,mw26,mw27],[[491,492,30000],[],[491,492],[491,30005,30146],[491,30086,30109],[491,30147,30005],[492,491],[],[492,30001,30148],[492,30149,30104],[492,30150,30001],[491],[493,494,20057,20000,30071],[195,495,20057,20065,30073],[20057,496,190,20066,20067,30038],[434,494,20005,20042,30027],[497,495,20005,20068,30026],[20005,496,498,20069,20070,30000],[66,499,500,501],[66,499,500,502],[503,504,501,502]]),
([mw0,mw1,mw22,mw14,mw35,mw26,mw27],[[505,30038,10002],[],[505,434,30215],[505,434],[505,30216,30217],[505,30217,30216],[506,507,508,10002,20006],[10002,434,30027,10012],[10002,486,10012,20005],[10002,509,10012,20071],[10002,510,511,20072,10014],[434,505],[505],[20006,506,146,512,30026,10018],[20006,506,10018,511,30000,10020],[],[434,513],[434,513],[20005,20071,323,514,511],[20005,20072,323,514,512],[434]]),
([mw0,mw1,mw22,mw14,mw26,mw38],[[515,10000,20023,30038,10002],[],[515,10000,20024,30058,30044,30072],[515,10000,20023,30170,30000,30038],[515,30063,516,20023,10000,517],[20023,506,518,10012,20039,10002,30000],[20023,10002,519,20024,10012,30044],[20023,10002,520,10012,30000],[20023,10002,362,10010,30000],[506,521,30000,10020,10021],[506,10020,30044,10022,10023],[506,126,20023,10020,517],[522,10021,514],[20024,514],[20023,514]]),
([mw0,mw1,mw4,mw2,mw12,mw14,mw26,mw27],[[491],[],[491,492],[],[491,20000],[491,20065],[491,20067],[],[492,491],[],[492,20042],[492,20068],[492,20070],[123],[],[123,20000],[123,20065],[123,20067],[],[20000,20073],[20065,20074],[20067,20023],[91,20000],[243,20065],[244,20067],[20000,523],[20000,246],[20065,490]]),
([mw0,mw1,mw2,mw12,mw14,mw26,mw27],[[491,488],[491,247],[],[491,20033,30146],[491,20033,30109],[491,20033,30005],[492,491],[],[492,20033,30148],[492,20033,30104],[492,20033,30001],[],[20033,139,30027],[20033,140,30026],[20033,141,30000],[20033,125,30027],[20033,52,30026],[20033,126,30000],[20033,66,488],[488],[488]]),
([mw0,mw1,mw4,mw2,mw14,mw49,mw26,mw27],[[524],[],[524,480],[524,20075],[],[524,30109],[524,30005],[],[525,526],[480,524],[],[480,30104],[480,30001],[123,480],[123],[],[123,20013],[123,20008],[480,527],[122,480],[480,527],[480,528],[],[91,528],[91,527],[244,528],[244,527],[91]]),
([mw0,mw1,mw2,mw14,mw49,mw26,mw27],[[524,91],[524,20076,10003],[524,91,529],[],[524,530,10004],[524,20076,10006],[525,20076,10011],[91,524],[],[525,512,10012],[525,20076,10014],[91,20076,10018],[20076,124,10003],[20076,10003,10018],[20076,10003,10020],[],[91,20076,529],[91,20076,529],[20076,126,531],[20076,126,387],[91]]),
([mw0,mw1,mw4,mw2,mw14,mw26,mw39],[[123,30000],[],[123,20067,10003],[123,30005,10007],[123,30086,10009],[],[],[123,20067,10011],[123,30001,10015],[123,30149,10017],[],[123,20067,10003],[123,20008,10007],[123,20035,10009],[],[20067,10007,527,10018],[20067,10009,527,10018],[20067,10018,10003],[10007,10009,532,533],[20067,91,10007],[20067,91,10009]]),
([mw0,mw1,mw2,mw14,mw26,mw39],[[123,534,535,10006,536],[123,10006,20077,30151,10003],[123,10001,20078,10006,10007],[123,10006,20077,10008,10009],[],[123,10002,20079,30075,10011],[123,10002,20080,10014,10015],[123,10002,20079,10016,10017],[],[20077,10003,10007,20078,10018,30077],[20077,10003,10009,10018,30075],[20077,10018,537,10003,30000],[536],[20078,30026,125,10007,387],[20077,30027,125,10009,387]]),
([mw0,mw1,mw4,mw2,mw14,mw35,mw26,mw27],[[505],[],[505,30038],[505,30146],[505,20057],[505,20081],[505,20082],[],[122,30000],[91,30148],[123,20005],[538,20071],[539,20072],[122,20006],[91,20013],[123,20057],[538,20081],[539,20082],[122],[],[122,390],[122,473],[],[91,540],[91,541],[244,390],[244,473],[91]]),
([mw0,mw1,mw4,mw2,mw14,mw26,mw38],[[518,515,30000],[],[122,20023,30038],[20023,515,542,20024,30146],[20023,140,30109],[20023,516,30005],[],[122,20023,30000],[20023,518,543,20024,30148],[20023,520,30104],[20023,481,30001],[122,20023,30000],[20023,20024,521,30076],[20023,146,30078],[20023,138,30000],[122,473],[122,271],[],[542,471,176],[20023,20024,473],[20023,473]]),
([mw0,mw1,mw2,mw14,mw26,mw36,mw47],[[544,545,30137],[544,30151,10003],[544,546,547],[544,282,548],[],[544,545],[545,30075,10011],[545,546,549],[545,282,550],[545,544],[],[10003,551,511,20073,10018],[10003,546,282,20074,10018],[10011,552,10003,20066],[10003,506,282,20069,10011],[547,548,282,546,553],[20073,20066,554,547,555],[20073,20069,134,282,556],[20074,20066,554,546,555],[20074,20069,134,546,556],[544]]),
([mw0,mw1,mw2,mw14,mw21,mw49,mw26,mw27],[[524,91],[524,480],[524],[],[],[524,557],[524,558],[525,10011],[91,524],[525],[],[480,512],[480,511],[91,512],[10011,480],[128,480],[480,512],[480,511],[],[],[91,511],[91,512],[],[377,557],[160,558],[323,511],[323,512],[91]]),
([mw0,mw1,mw2,mw14,mw21,mw26,mw45,mw27],[[559,30137],[559,10003],[559],[],[559,530],[559,530],[559,560],[10003,10011],[554,512],[30,512],[525],[],[530,554],[10003,530],[10011,10003],[10003,530],[10003,530],[10003,561],[],[554,210],[554,562],[560,530],[481,563],[481,20013],[481,530],[],[560,530],[554]]),
([mw0,mw1,mw2,mw14,mw21,mw26,mw47],[[525,20072,30137],[20072,10011,10003],[20072,554],[],[20072,535,531,530,564],[20072,516,10006],[525,20072,10011],[525,554,565],[525,511,10014],[525,554],[],[20072,10011,10018],[20072,10011,10003],[20072,566,10011,530,10018],[20072,10003,10011],[],[554,562],[20072,554,565],[481,40,567,531],[20072,481,384],[20072,554]]),
([mw34,mw0,mw1,mw2,mw14,mw26,mw38],[[],[],[518,552,30000],[518,20024,30044],[518,20023,30000],[518,20024,30075],[518,20024,30000],[552,20024,10000],[20024,10000,10004],[20024,20023,10000,10004],[20024,10004,10000],[518,552,10010],[518,20024,10012],[518,20023,10012],[518,20024,10010],[552,467],[552,468],[],[518],[20024,467],[20024,20023,467]]),
([mw0,mw1,mw2,mw14,mw37,mw47],[[568,569,10004,123,30109,30001,30075],[569,10004,20083,30155,10003],[569,570,135,571],[],[569,10004,20083,10008,10009],[568,10014,20084,30075,10011],[568,570,135,572],[568,10014,20084,10016,10017],[],[20083,10003,573,20081,10018,30075],[20083,10011,10017,10003,30073],[20083,10003,10009,10011,30000],[570,571],[570,572],[20083,106,574,10017,10009]]),
([mw32,mw0,mw1,mw33,mw9,mw28,mw26],[[],[575,576,24],[],[576,20085,30024],[576,393],[576,20085,577],[576,578,30000],[20085,30000],[576,20085,10007],[576,579,10008],[576,20085,10008],[],[576,20085,10015],[576,338],[576,580],[20085,10007,10015],[338],[20085,338],[20085,581,10007,579,10021],[20085,10007,10025],[578]]),
([mw0,mw1,mw2,mw14,mw26,mw36,mw39],[[544,20040,10002],[544,20040,10003],[544,582],[544,583],[],[],[20040,10002,10011],[20040,395,511,10014],[20040,10002,10016],[20040,30152],[],[20040,551,10003,511,10018],[20040,10003,10018],[20040,10011,10003],[20040,10018,10003],[395,584,585,511],[20040,582],[20040,582],[20040,582],[20040,582],[]]),
([mw0,mw1,mw4,mw8,mw13,mw26,mw27],[[143],[],[143,30038,30152],[143,30073,30154],[143,30154,30073],[143,30152,30038],[],[586,30000,30030],[586,30026,30029],[586,30029,30026],[586,30030,30000],[120,587,20006,20002,30030],[171,588,20006,20012,30029],[20006,589,20013,20086,30026],[20006,590,20008,20087,30000],[591],[543,592,593,594],[20002,20087,101,595,596],[20012,20086,175,597,598],[575,101,599,600],[591]]),
([mw0,mw1,mw8,mw20,mw13,mw26,mw27],[[143,30038,10002],[143],[],[143,601,602],[143,603,604],[143,30015],[10002,120,30030,10010],[605,606,144,10002,20006],[10002,607,601,20027,10010],[10002,589,603,20088,10012],[10002,590,608,20089,10014],[],[120,609],[120,610],[120,30030,611],[20006,605,125,612,602],[20006,605,613,614,601],[20006,605,463,30000,601,611],[20027,20088,435,603,601,120],[120],[120]]),
([mw0,mw1,mw8,mw13,mw26,mw36],[[143,30038,10002],[143,30015,30218],[143,615],[143,616],[],[20087,10002,617,10010,30073],[20087,10002,618,20082,10010,30087],[20087,10002,589,20040,10012,30038],[20087,10010,606,10002,30000],[616],[615],[20087,619,24,595,596],[620,136,30000,597,598],[615],[616]]),
([mw0,mw1,mw8,mw13,mw26,mw27,mw56],[[621,622,10000,10001,10002],[10001,622,10000,30030],[10001,622,10000,30029],[10000,622,146,30026,10004],[10000,622,463,30000,10006],[10001,622,10000,30000],[10002,621,120,30152,10010],[10002,621,10010,30154],[10002,621,146,30073,10012],[10002,621,463,30038,10014],[10002,621,10010,30038],[146],[146,463],[463],[],[146],[146],[],[146,463,120],[],[]]),
([mw0,mw7,mw6,mw13,mw26,mw27],[[623,624,625,20090,10001,30219],[623,507,626,20091,10001,30220],[623,10001,20091,10000,30161],[623,10001,20090,10004,30104],[623,10001,20090,10006,30000],[624,507,627,628],[624,629,41,630],[624,146,20090,631,632],[624,633,20090,634,635],[507,629,171,20091,636,637],[507,630],[507,190,20091,638,639],[629,195,20092,640,641],[20091,41,629,640,635],[20090,628]]),
([mw0,mw1,mw22,mw6,mw13,mw26,mw27],[[625,642,30000],[],[625,20093,30221],[625,643],[625,20093,30092],[625,20094,30222],[642,20095,30219],[],[642,20095,30085],[642,644],[642,20096,30223],[20094,20096,507,20064,20017,30030],[625],[20064,645,20057,20001,30182],[20064,646,20094,647],[20017,486,20037,20041,30027],[642],[20017,510,20096,648],[20041,20001,457,514,641],[644],[643]]),
([mw0,mw1,mw22,mw8,mw15,mw26,mw27],[[143,20097,10002],[],[143,649],[],[143,20097,30005],[143,30171,650],[20097,139,10002],[20097,651,601,10010],[20097,652,10002],[20097,10002,10012],[20097,653,608,10014],[143],[],[20097,139,654],[139,20066,650],[649],[139],[498,436,595,601],[20097,497,655],[139],[649]]),
([mw0,mw1,mw22,mw8,mw14,mw46,mw27],[[656,20098,10002],[],[656,20098,657],[656,30092,30120],[656,20098,658],[656,20099,30121],[20098,659,10002],[20098,10002,10010],[20098,660,512,10012],[20098,10002,10010],[20098,661,608,10014],[656],[521,139,512,662],[656],[463,141,30028,663,10023],[31],[],[664,24,20098,512,10023],[20098,150,665],[657],[664,20098,24,512,10023]]),
([mw0,mw1,mw2,mw5,mw17,mw13,mw26,mw27],[[625,169],[625,20100],[],[],[625,20012],[625,666],[625,20101],[667,20092],[667],[],[20012,20102],[666,668],[20101,20083],[669,20103],[670,20103],[],[671,20014],[20101,647],[],[669,20012],[625],[669,20101],[670,20012],[159,666],[159,20101],[20012,20014],[20012,647],[169]]),
([mw0,mw1,mw2,mw5,mw16,mw26,mw27],[[667,20069,30139],[20069,672,30159],[],[20069,673,30115],[20069,674,666],[20069,675,30157],[667,672,676],[667,20069,30224],[],[667,20069,30019],[667,677],[672,20069,30043],[],[672,20069,30041],[672,678],[20069,158,30027],[20069,674,666],[20069,190,679],[20069,52,10029],[20069,677],[20069,680,10029]]),
([mw0,mw1,mw2,mw5,mw11,mw26,mw46,mw27],[[681,20104],[681,20105],[],[681,20106],[681,682],[681,20105],[681,20107],[683,20108],[683,20013],[],[683,20109],[683,20109],[683,682],[684,685],[20109,20069],[672],[],[672,686],[687,20106],[681],[681],[688,689],[52,20109],[690,20109],[682],[],[686,689],[690,686]]),
([mw0,mw1,mw2,mw5,mw11,mw26,mw38],[[691,692,10004,20023,30075],[10004,672,20023,30225],[],[691,692,10004,20024,30120],[20023,674,10004],[10004,692,20023,30157],[692,691,672,20023,30226],[20023,693,30104],[],[20023,694,30099],[20023,690,677],[672,20023,30227],[691,692,672,695],[672,686],[],[691,20024,693,30076],[20023,674,696],[20023,160,10027],[146,691,206,531,10029],[20023,691,690,20024,677],[20023,686]]),
([mw0,mw1,mw2,mw5,mw11,mw49,mw26,mw27],[[697,20110],[697,698],[],[697,20106],[],[697,698],[697,30157],[698,699],[690,20013],[],[],[698,30099],[690,699],[699,698],[698,699],[672,698],[699,700],[698,701],[690],[],[697],[699,700],[],[698,701],[690,699],[155,698],[155,699],[698,690]]),
([mw0,mw1,mw2,mw5,mw14,mw42,mw27],[[702,703,166,704],[703,20078,10003],[],[703,20078,705],[],[703,30218,10009],[166,20078,10011],[703,166,704],[166,20078,10012],[],[166,706],[703,20078,10003],[20078,10003,10018],[20078,707,10003],[20078,10009,708,10020],[703,20078,705],[],[703,20084,10009],[20078,706],[703],[706]]),
([mw0,mw1,mw2,mw5,mw11,mw26,mw27,mw61],[[709,20110],[709,698],[],[709,30115],[709,698],[709,20111],[],[698,10011],[20111,20112],[],[698,30019],[20112,710],[154,20112],[20111,698],[698,10011],[10011,238],[698,238],[10011,698],[158,20075],[709],[711],[],[698,238],[712,710],[154,238],[698,709],[],[]]),
([mw0,mw1,mw8,mw13,mw26,mw38,mw44],[[713,714,10000,10001,10002],[10001,714,10000,30026],[10001,714,10000,30111],[10000,714,146,30000,10004],[10001,714,10000,30111],[10000,714,10004,30000],[10002,713,120,30073,10010],[10002,713,10010,30087],[10002,713,146,30038,10012],[10002,713,10010,30087],[10002,713,10012,30038],[146],[146,120,715],[146],[120,146],[146,120],[],[146],[146,120],[],[146]]),
([mw0,mw1,mw2,mw17,mw14,mw37,mw27],[[716,166,717],[716,20011,10003],[],[716,557],[],[716,30218,718],[166,20011,10011],[],[166,512,719],[166,20011,720],[166,30103,30099],[20011,10020,10003],[20011,721,10003,512,10020],[20011,10011,10003],[20011,722,10003,10020],[557],[166],[159,76,20011,512,387],[20011,557],[717],[557]]),
([mw0,mw1,mw2,mw5,mw14,mw62,mw37,mw27],[[524,30140],[524,723],[],[524,724],[524,725],[],[524,723],[723,10011],[711,512],[166],[],[166,512],[723,726],[10011,723],[723,512],[723,10011],[10011,723],[10011,701],[524],[524],[],[711,723],[],[724],[723,711],[74,701],[723,512],[724]]),
([mw0,mw1,mw2,mw5,mw21,mw45,mw27],[[727,703,30083],[703,20071,10003],[],[],[703,20071,728],[703,30120,560],[727,20071,10011],[727,703,729],[727,512,10012],[],[727,730],[703,20071,10003],[20071,10011,10003],[20071,10003,10011],[20071,197,10003,708,10020],[],[703,20071,728],[703,20075,560],[20071,731,732],[703],[730]]),
([mw0,mw1,mw2,mw5,mw14,mw37,mw27,mw47],[[544,20113],[544,698],[],[544,698],[],[544,30082],[544,30082],[698,10011],[224,30103],[698,733],[734,706],[166],[],[10011,698],[10011,701],[10011,698],[698,701],[698,10011],[544],[],[224,20084],[224,20084],[706,698],[698,224],[698,224],[224],[224],[]]),
([mw0,mw1,mw2,mw5,mw14,mw37,mw47],[[166,20083,30083],[20083,10011,10003],[],[20083,206,135,735],[],[20083,516,10009],[166,20083,10011],[166,20083,30099],[166,726],[166,736],[],[20083,10011,10003],[20083,737,10011,701,10018],[20083,10011,10003],[20083,10003,10011],[20083,135,735],[],[20083,726,10009],[735],[20083,10009,206,726],[20083,726]]),
([mw0,mw1,mw2,mw5,mw11,mw14,mw28,mw37],[[738,30228],[738,20114],[],[738,20115],[738,739],[738,740],[],[741,20116],[741,20117],[],[741,742],[741,20118],[741,20117],[688,30229],[20115,20069],[675,20119],[],[743,688],[688,20115],[738],[688,740],[],[20115,741],[20115,20118],[694,20115],[134,384],[739],[688]]),
([mw0,mw1,mw2,mw5,mw11,mw14,mw28,mw44],[[744,30230],[744,20120],[],[744,20121],[744,745],[744,20122],[744,739],[746,20116],[746,20123],[],[746,747],[746,20118],[746,748],[749,20124],[750,20125],[521,30028],[],[743,521],[687,751],[744],[711,20122],[744],[746],[690,20118],[746],[521,752],[],[521]]),
([mw0,mw1,mw2,mw5,mw11,mw28,mw44],[[753,754,10004,20004,30011],[10004,754,20004,30007],[],[753,754,10004,20126,20004,30231],[10004,754,20004,30190],[20004,755,10004],[20004,10014,30002],[754,753,10014,20117,20004,30232],[],[20004,10014,30122],[20004,694,10014],[754,20126,171,20127,20004,30233],[753,20117,120,20128,20004,30111],[],[20004,756,686],[753,754,291,20126,20117,10025],[20126,754,711,238,20127,10027],[20004,754,755,238,10005],[20117,753,10025,238,20128,10029],[20004,753,694,10025],[20004,756,686]]),
([mw0,mw1,mw4,mw2,mw17,mw13,mw26,mw27],[[625],[],[625,20103],[],[625,20012],[625,666],[625,20129],[],[20103,20130],[],[20012,20041],[666,668],[757,20131],[587,20103],[],[587,20012],[587,666],[587,20101],[139,20103],[],[645,20132],[20103,647],[472,20012],[587],[244,20101],[20012,176],[20012,647],[20101,169]]),
([mw0,mw1,mw2,mw3,mw10,mw43,mw27],[[758,206,10010,20036,30140],[758,206,10011,20037,30166],[20036,206,10013,20005,30109],[],[20036,759,30082],[20036,10017,10007],[760,238,10012,10010,10011],[10010,758,10012,10013],[10010,758,20036,30019],[],[10010,758,206,20036,10017],[10011,758,761],[10011,758,20036,20037,30041],[],[10011,758,206,20037,10023],[10013,20036,20005,30045],[],[10013,20036,20005,10027],[20036,199,10029],[20036,10017,10007],[20036,10007,10017]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw56],[[203,206,10006,20007,30009],[10006,206,20062,30174],[10006,206,20063,30234],[],[10006,20007,30121],[20007,10,10006],[20007,203,10018,20062,30112],[20007,203,10019,20063,30205],[20007,10021,30123],[],[20007,106,10017],[762,763,10020,10018,10019],[10018,763,203,10021],[20062,10018,10023],[],[10019,10021,203,384,10025],[20063,10019,10027],[],[20007,10021,10029],[20007,10,10021],[20007,106,10017]]),
([mw0,mw1,mw2,mw5,mw11,mw14,mw37,mw47],[[764,30083],[764,698],[],[764,30082],[764,698],[],[764,765],[698,699],[726,30223],[],[698,699],[74,706],[],[699,698],[698,699],[766,701],[699,698],[698,699],[726,30000],[764],[],[726,765],[698,699],[74,726],[],[699,698],[698,699],[726]]),
([mw0,mw1,mw2,mw3,mw10,mw30,mw45,mw27],[[767,30140],[206,20133],[206,20134],[],[703,20135],[768,20136],[769,770],[767,771],[767,771],[767,20137],[],[],[767,206],[772,30030],[20137,20066],[],[768,206],[773,206],[20137,20021],[703,206],[],[769,206],[198,206],[285,206],[769,206],[703,772],[774,775],[69,775]]),
([mw0,mw1,mw2,mw3,mw10,mw30,mw27,mw39],[[776,30140],[206,20133],[206,777],[],[43,20138],[778,776],[],[776,779],[776,780],[776,20139],[],[776,206],[],[777,10019],[780,30041],[],[777,206],[768,206],[780,777],[777,206],[10019,206],[10019,206],[40,206],[778,776],[],[777,778],[768,222],[]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw27,mw63],[[206,30009],[206,781],[206,698],[],[222,20138],[778,782],[],[781,783],[781,780],[781,20139],[],[781,206],[],[784,10019],[780,698],[698,206],[698,206],[],[780,698],[698,206],[698,206],[210,206],[20140,206],[778,206],[],[781],[],[]]),
([mw0,mw1,mw2,mw5,mw10,mw26,mw47],[[785,569,30083],[569,20083,10003],[],[],[569,20083,786],[569,20083,787],[785,20083,10011],[785,20083,30103],[785,569,788],[785,788],[],[20083,10011,10003],[569,20083,10003],[20083,10003,788],[20083,10003,10011],[569,20083,788],[569],[20083,788],[569,788],[569,788],[20083,788]]),
([mw0,mw1,mw2,mw17,mw14,mw42,mw27],[[789,166,403],[789,20076,10003],[],[789,790],[],[789,20076,10009],[166,20076,10011],[],[166,791],[],[166,20076,10017],[20076,10020,10003],[20076,10003,10020],[20076,10020,10003],[20076,10003,10020],[20076,790],[],[20076,76,790],[20076,790],[403],[20076,790]]),
([mw0,mw1,mw2,mw3,mw10,mw40,mw27],[[768,792],[768,792,793],[768,20060,10005],[],[],[768,20060,309],[768,793,192],[793,20060,192],[793,192],[],[793,20060,192],[768,20060,192],[768,192],[],[768,20060,192],[20060,192],[20060,192],[20060,10005,192],[20060,192],[768],[20060,192]]),
([mw0,mw1,mw2,mw3,mw18,mw46,mw27],[[758,692,10006,794],[758,754,10006,20106,20018,30006],[10006,692,794,20018,30005],[],[10006,692,20106,20018,30015],[20018,675,10006],[692,20106,10002,20018,30002],[794,20018,30001],[],[20018,10002,30019],[20018,10002,795],[794,20106,795],[20106,139,30177],[],[20106,675,796],[794,20106,30179],[],[794,20106,797],[20106,347,10029],[20106,795],[20106,796]]),
([mw0,mw1,mw2,mw3,mw10,mw30,mw44],[[291,206,10010,20004,30009],[20004,10011,30006],[20004,206,10006,20020,30234],[],[20004,10006,30033],[20004,798,10006],[20004,10016,10010],[10010,291,20020,20004,30205],[10010,291,20020,20004,30122],[],[10010,291,206,20004,10016],[20004,20020,10011,30024],[20004,20020,10011,30023],[],[20004,10011,10023],[20020,799,800],[20020,196,10027],[],[20020,10027,10029],[20004,20020,798,800],[20004,801,10023]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw38,mw44],[[206,30009],[206,20141],[206,20142],[],[20141,20138],[20142,20141],[20141,20142],[802,20143],[20143,20144],[20143,20139],[],[20144,206],[20143,206],[802,30030],[802,803],[802,206],[],[802,206],[208,804],[209,206],[210,206],[],[274,206],[360,206],[212,206],[774,701],[69,701],[802]]),
([mw0,mw1,mw2,mw5,mw10,mw25,mw44],[[360,20004,30075],[360,20004,10003],[],[],[360,20004,30005],[360,20004,805],[20004,10003,10011],[20004,774,703,30095],[360,20004,30123],[],[20004,74,806],[20004,703,10003],[360,20004,10003],[20004,10003,10011],[20004,10003,10018],[360,703,807],[703,807],[360],[360,807],[360,703],[20004,74,806]]),
([mw0,mw1,mw2,mw3,mw10,mw31,mw38],[[212,808],[212,768,30006],[212,20023,10005],[],[],[212,20023,809],[768,20023,30112],[20023,10005,10013],[212,20023,810],[],[20023,811,812],[768,20023,10019],[212,768,215],[768,215],[],[212,20023,10005],[20023,10019,10005],[20023,10005,10019],[212,810],[212,768],[20023,215]]),
([mw32,mw1,mw22,mw33,mw9,mw14,mw23],[[813,814,815,24],[],[],[813,814,20005,30235],[814,20005,110],[814,20005,30236],[814,815,816],[],[815,20005,816],[815,816],[815,20005,816],[814,816],[814,20005,816],[814,816],[814,20005,816],[20005,816],[20005,816],[20005,816],[],[20005,816],[20005,816]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw39,mw38],[[212,30009],[212,30237],[212,777],[],[212,20138],[],[212,777],[817,30094],[777,818],[212,20139],[],[],[777,818],[777,10019],[212,819],[817,820],[817,206],[],[212,777],[777,818],[10019,777],[225,10019],[212],[],[212,777],[],[777,818],[817]]),
([mw0,mw1,mw2,mw14,mw26,mw36,mw61],[[821,20040,10002],[821,20040,10003],[821,132],[821,132],[],[],[20040,10002,132],[20040,132],[20040,10002,132],[20040,132],[20040,132],[20040,132],[20040,10003,132],[20040,132],[20040,132],[132],[20040,132],[],[20040,132],[],[]]),
([mw0,mw1,mw2,mw5,mw6,mw13,mw37,mw27],[[625,30238],[625,20093],[],[625,822],[625,20145],[],[625,616],[822,20092],[822,625],[],[822,20102],[822,668],[822,20083],[669,30087],[139,20005],[],[645,20146],[646,647],[625],[669,20145],[],[669,616],[20145,20102],[822],[823,20083],[824,20145],[20145,647],[669]]),
([mw0,mw1,mw2,mw5,mw11,mw26,mw47,mw44],[[825,30075],[825,10003],[],[825,30115],[825,826],[825,30218],[825,827],[10003,699],[828,30104],[],[826,30122],[],[827,699],[699,10003],[10003,699],[10003,238],[10003,699],[10003,238],[774,30071],[825],[711,238],[825],[690,826],[],[827,699],[711,826],[],[827,699]]),
([mw0,mw1,mw2,mw5,mw11,mw21,mw26,mw47],[[764,20110],[764,698],[],[764,30120],[],[764,698],[764,30157],[698,699],[690,30104],[],[690,699],[698,730],[],[699,698],[698,699],[829,698],[699,700],[698,699],[690,20075],[],[764],[160,700],[690,699],[698,730],[],[699,698],[160,699],[698,690]]),
([mw0,mw1,mw2,mw5,mw62,mw45,mw27],[[690,830,831,30001,30075],[832,830,10011,30151,10003],[],[833,830,703,832,834],[285,830,711,832,835],[836,830,837,30156,20009,30121],[831,30075,10011],[830,690,831,832,838],[],[],[831,30019,839],[830,840,10011,10003,20057],[10003,841,10011,20147],[10003,824,10011,20148],[10011,832,842,20023,10020],[833,830,703,838],[285,830,711,838],[836,830,837,30074,832,384],[285,833,74,843,842],[836,833,844,843,832],[836,285,74,842,832,839]]),
([mw0,mw1,mw2,mw5,mw6,mw21,mw45,mw27],[[789,30009],[789,296],[],[789,727],[],[789,728],[789,296],[296,845],[727,789],[],[727,846],[],[296,845],[845,296],[296,845],[845,296],[296,845],[847,842],[789],[],[789],[845,296],[727],[],[296,845],[377,842],[845,296],[296,845]]),
([mw0,mw1,mw2,mw3,mw10,mw16,mw26,mw47],[[848,30239],[849,20149],[20149,20150],[],[569,20149],[20149,20151],[20149,850],[848,851],[848,20152],[848,852],[],[848,853],[],[849,30113],[849,854],[],[849,20153],[849,855],[699,20075],[554,20154],[],[493,856],[569,852],[699,20151],[852],[857,20153],[849],[493,853]]),
([mw0,mw1,mw2,mw3,mw10,mw25,mw36,mw64],[[812,30009],[812,30237],[812,777],[],[812,30121],[],[812,777],[858,783],[777,780],[812,30123],[],[69,812],[],[777,10019],[812,859],[858,812],[858,206],[],[812,777],[777,780],[10019,777],[560,780],[812,206],[],[812,777],[812],[],[812]]),
([mw0,mw1,mw2,mw17,mw18,mw26,mw27],[[860,785,861],[860,30151,10003],[],[],[860,30240,786],[860,30241,787],[785,30075,10011],[],[],[785,30224,862],[785,30242,863],[864,472,10020,10003,20002],[865,721,10018,10003,20012],[10003,866,10018,20018],[10003,867,10020,20023],[861],[244,864,868,786],[20002,864,244,869,870],[20012,865,347,871,872],[243,865,873,787],[861]]),
([mw0,mw1,mw2,mw12,mw3,mw18,mw26,mw27],[[874,875],[874,876],[],[874,20155],[],[874,20156],[874,877],[876,874],[],[875,20157],[],[876,20158],[876,878],[],[875,20097],[139,879],[20156,20018],[675,20023],[875,20002],[139,879],[880,20156],[244,20023],[875,20000],[],[875,881],[347,20156],[76,877],[875]]),
([mw0,mw1,mw2,mw3,mw10,mw48,mw30,mw27],[[882,20159],[883,20133],[884,777],[],[],[884,20033],[884,777],[882,884],[882,780],[882,883],[],[],[882,780],[883,885],[883,882],[],[],[883,885],[884,777],[10026,777],[777,780],[254,10026],[],[884,20033],[884,777],[884],[190,884],[884]]),
([mw0,mw1,mw2,mw3,mw18,mw40,mw27],[[886,887,30000,888],[886,888,793],[189,20160,10005],[],[],[189,30015,309],[887,888,793,889],[793,20160,10013],[],[],[793,30019,775],[888,20160,10019],[888,780,10003],[],[888,890],[20160,10019,10005],[20160,91,10005],[20160,891,10005,238,10024],[20160,890],[189],[890]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw65],[[892,206,10010,20036,30031],[20036,206,10011,20037,30105],[20036,206,10013,20005,30190],[20036,10015,30121],[],[20036,0,10009],[608,892,10012,10010,10011],[10010,892,10012,10013],[10010,892,20036,10015],[10010,20036,10017],[],[10011,10013,387,386,10019],[10011,20036,20037,10021],[10011,20036,20037,10023],[],[10013,20036,20005,10025],[10013,20036,20005,10027],[],[20036,10015,10029],[],[20036,0,10009]]),
([mw34,mw4,mw2,mw3,mw9,mw28,mw42],[[],[49,20161,30243],[49,893,30210],[49,20161,30207],[49,20161,30031],[],[49,20161,30028],[49,893,262],[49,20161,262],[49,262],[],[20161,893,262],[20161,262],[],[20161,262],[893,20161,262],[893,262],[],[20161,262],[20161,262],[20161,262]]),
([mw0,mw1,mw2,mw3,mw10,mw24,mw64],[[886,206,10010,20041,30009],[886,206,10011,20027,30006],[20041,10013,10005],[],[],[20041,0,309],[894,895,10014,10010,10011],[10010,886,20041,10013],[10010,886,10014,896],[10010,886,206,20041,778],[],[10011,886,20041,20027,10019],[10011,886,897],[10011,886,206,20027,898],[],[20041,699,10013,10005],[20041,10013,10005],[20041,10005,10013],[699,20041,899,222],[20041,0,206,309],[20041,0,309]]),
([mw55,mw1,mw2,mw3,mw10,mw53,mw23],[[900,387,20036,30244],[900,387,20037,30222],[20036,780,493,20005,30200],[],[],[20036,10006,30082],[901,420,10012,902],[902,780,10012],[20036,10012,903],[],[20036,10012,10017],[902,903,421],[20037,903,442],[],[20037,903,10023],[780,20036,902,337],[],[20005,902,10027],[20036,903],[20036,10017,10009],[20036,10009,10017]]),
([mw0,mw1,mw2,mw3,mw9,mw31,mw56],[[892,206,10008,423,422,10002],[10008,206,20162,20007,30105],[10008,206,20162,20007,30190],[10008,206,20162,20007,30121],[],[20007,10,10008],[422,892,10002,20162,20007,30112],[422,892,10002,20162,20007,30205],[422,892,10002,20162,20007,30122],[],[10002,20007,10017],[20162,10020,391],[20162,10018,10020],[20162,10020,10023],[],[20162,10019,904],[20162,10023,10027],[],[20162,10023,10029],[],[20162,6,10017]]),
([mw0,mw1,mw2,mw3,mw9,mw66,mw43],[[892,206,100,20005,30137],[100,20005,30058],[100,20005,30059],[20005,10015,10007],[20005,905,906],[20005,0,10008],[100,10012,907],[100,10010,10012],[100,20005,10015],[100,206,773],[],[100,773,429],[100,20005,10021],[100,892,407],[],[100,20005,10025],[100,892,905],[],[20005,10015,10028],[20005,10007,10015],[]]),
([mw34,mw4,mw2,mw3,mw9,mw28,mw44],[[],[472,206,20004,30209],[20004,206,236,908,30210],[472,206,909,20004,30207],[20004,230,30245],[20004,910,30137],[20004,465,10000],[20004,908,10004],[20004,909,10006],[20004,10004,10000],[20004,10000,10004],[20004,908,30024],[20004,909,30023],[],[20004,911,912],[908,909,277],[908,206,277],[],[909,206,277],[],[20004,911,912]]),
([mw0,mw1,mw2,mw3,mw10,mw24,mw47,mw38],[[206,30064],[206,30246],[206,10005],[],[],[613,913],[121,914],[915,30062],[10005,10013],[915,916],[915,206],[],[121,206],[10005,10019],[222,917],[222,206],[613,206],[],[10013,10005],[10013,206],[10005,206],[10005,206],[916,206],[613,206],[121,206],[613,913],[121,914],[613,915]]),
([mw0,mw1,mw2,mw3,mw10,mw16,mw24,mw47],[[896,30009],[172,30166],[896,918],[],[896,919],[],[896,918],[896,920],[172,780],[172,896],[],[172,780],[],[896,10019],[896,172],[],[896,20003],[896,780],[780,918],[918,780],[10019,918],[10019,780],[896],[920],[896],[313,896],[896],[896]]),
([mw0,mw1,mw8,mw13,mw28,mw44],[[20004,10000,10010,10001,10002],[20004,10001,274,120,30045,10000],[20004,10001,171,30044,10000],[20004,10001,921,10000,30000],[20004,10000,922,10004,30000],[20004,10002,120,30074,10010],[20004,10002,171,30072,10010],[20004,10002,923,10010,30038],[20004,10010,924,10012,30038],[120,171,925],[120,171],[120,171],[171,120],[120],[20004,120]]),
([mw0,mw1,mw2,mw5,mw14,mw26,mw47],[[831,20083,30064],[20083,10011,10003],[],[20083,135,926],[20083,137,927],[20083,516,30121],[831,20083,10011],[831,20083,30019],[831,928],[831,928],[],[20083,10011,10003],[20083,928],[20083,10011,928],[20083,10003,10011],[20083,135,926],[20083,137,927],[20083,928],[926],[20083,928],[20083,928]]),
([mw0,mw1,mw2,mw3,mw67,mw30,mw27],[[69,20020,30140],[20020,929,899,30166],[20020,10013,10005],[],[20020,199,30121],[20020,930,10007],[69,899,931],[69,20020,10013],[69,20020,239],[],[69,899],[899,20020,10019],[899,20020,932],[],[899,69],[20020,10013,10005],[20020,10005,10013],[20020,10013,10025],[20020,199,931],[20020,930,10007],[69]]),
([mw0,mw1,mw2,mw17,mw14,mw68],[[377,933],[377,933],[],[377,933],[377,933],[933],[],[933],[933],[933],[933],[933],[377],[933],[933]]),
([mw0,mw1,mw2,mw3,mw69,mw46,mw27],[[934,624,139,30207],[624,139,10000],[139,687,10004],[139,935,936],[139,10000],[139,935,10006],[624,139,10010],[624,687,10012],[624,935,937],[624,10010],[624,935,10014],[624,934],[624,20153,30041],[],[624,938],[687,20153,30045],[],[687,939],[20153,938,940],[934],[20153,938]]),
([mw0,mw1,mw2,mw3,mw69,mw28,mw44],[[274,291,30207],[274,941,10000],[274,687,10004],[274,291,942],[274,941,10000],[274,10004],[291,943,10010],[291,687,10012],[274,291,944],[291,943,10010],[291,10012],[687,20004,30024],[274,20004,30111],[],[20004,945,938],[274,687,277],[687,277],[],[274,277],[274,687],[20004,945,938]]),
([mw0,mw1,mw2,mw3,mw9,mw70,mw44],[[292,422,10002],[620,480,10003],[946,20004,30190],[292,20004,30121],[],[20004,945,947],[292,620,30247],[292,946,10012],[292,10002,10014],[292,422,10002],[292,20004,10012],[620,946,10018],[292,620,10020],[620,480,10003],[620,20004,10018],[292,946,750],[946,948],[],[292,940],[],[20004,945,947]]),
([mw0,mw1,mw2,mw3,mw9,mw24,mw71],[[293,20020,30031],[20020,894,30105],[20020,949,10005],[293,20020,10007],[],[20020,0,950],[293,894,884],[293,20020,10013],[293,894,10015],[293,812],[],[894,20020,10019],[293,894,10021],[894,951],[],[293,20020,30027],[20020,949,10005],[20020,949,10013],[293,20020,10007],[293,20020,10015],[20020,0,950]]),
([mw0,mw1,mw2,mw3,mw72,mw30,mw27],[[952,768,189,30102],[768,189,30089],[768,10004],[768,953,69],[768,198,30082],[768,953,10006],[768,189,192],[189,192],[189,192],[],[189,192],[768,192],[768,192],[],[768,192],[192],[198,192],[192],[198,953,69],[768],[198,953,192]]),
([mw0,mw1,mw2,mw3,mw72,mw30,mw26],[[954,49,30248],[954,49,30249],[954,955,10004],[954,10006],[954,198,30250],[954,955,10004],[954,49,956],[49,956],[49,956],[],[49,956],[954,956],[954,956],[],[954,956],[956],[198,956],[],[955,198,956],[956],[198,956]]),
([mw32,mw1,mw2,mw19,mw9,mw14,mw23],[[332,814,101],[332,814,362],[],[332,20005,30175],[332,20005,957],[332,20005,30047],[332,814,816],[],[332,20005,816],[332,816],[332,20005,816],[],[814,20005,816],[814,816],[814,20005,816],[20005,816],[20005,816],[20005,816],[],[20005,816],[20005,816]]),
([mw32,mw1,mw2,mw5,mw9,mw53,mw23],[[958,387,440,100],[440,387,100,394],[],[958,387,20005,30175],[],[100,20005,30157],[100,10012,444],[100,387,10012],[100,20005,903],[],[100,20005,10017],[100,387,336],[100,20005,442],[],[100,20005,10023],[20005,444,959],[20005,444],[20005,10017,10009],[],[20005,444,10029],[20005,10009,10017]]),
([mw0,mw1,mw2,mw14,mw37,mw36,mw44],[[821,30005,10002],[821,30151,10003],[821,134,30005],[],[],[821,134],[10002,10003,10010,10011],[10002,134,30027,10012],[10010,960,10002,30026],[10010,961,10002,30000],[10002,123,10012,30000],[10003,134,30148,10018],[10011,962,10003,30104],[10011,963,10003,30001],[10003,506,10018,30001],[134,821],[134,821],[],[134],[821],[821]]),
([mw34,mw0,mw1,mw2,mw3,mw35,mw46,mw27],[[],[],[382,30023],[382,30000],[382,30067],[382,30009],[382,30009],[30000],[382,964],[382,530],[382,964],[382,964],[382,579],[530,965],[964,512],[579,965],[108,965],[964,608],[506,382],[],[],[506,964],[],[],[966,530],[382],[966,382],[382]]),
([mw0,mw1,mw4,mw2,mw3,mw35,mw46,mw27],[[30000],[],[592,30006],[592,30005],[139,20163],[140,20164],[141,20040],[],[592,30002],[592,30001],[624,20165],[520,20166],[967,20083],[592,20006],[592,20013],[238,20163],[842,20164],[20006,20040],[968,969],[],[],[592,970],[],[],[592,387],[392,592],[592],[592]]),
([mw0,mw1,mw2,mw3,mw18,mw48,mw31,mw27],[[971,972],[971,973],[971,973],[],[],[],[971,973],[973,780],[973,780],[],[],[],[973,780],[842,10019],[347],[],[350,973],[351,842],[10019,973],[10026,973],[842,973],[10019,10026],[],[972],[972],[972],[972],[347]]),
([mw0,mw1,mw2,mw3,mw18,mw31,mw27,mw38],[[974,975],[974,30058],[974,976],[],[],[974,30121],[974,30015],[976,30062],[915,977],[],[],[976,30122],[976,30019],[976,10019],[348,978],[350,890],[244],[],[10019,976],[10019,976],[976,238],[976,10019],[975],[975],[915],[915],[915],[]]),
([mw0,mw1,mw2,mw3,mw18,mw31,mw38],[[886,887,30000,975],[886,212,10001,20010,30006],[10001,887,20010,10005],[],[],[10001,887,20010,309],[887,20010,10002,30002],[20010,10005,10013],[],[],[20010,309,775],[20010,10005,10019],[895,886,768,897],[979,886,674,898],[],[20010,980,10019,10005],[20010,842,10019,10005],[20010,10005,10019],[975],[20010,895,897],[20010,897]]),
([mw0,mw1,mw2,mw3,mw10,mw30,mw36,mw47],[[812,30009],[812,30166],[812,777],[],[812,30082],[],[812,777],[189,779],[777,780],[812,30099],[],[189,812],[],[777,10019],[812,30041],[],[778,238],[777,812],[812,777],[777,780],[10019,777],[10019,780],[812,238],[],[812,777],[812],[812],[812]]),
([mw0,mw1,mw2,mw3,mw10,mw16,mw24,mw30],[[981,30009],[982,30006],[981,777],[],[981,777],[],[981,351],[981,983],[982,983],[982,981],[],[982,981],[],[981,983],[981,982],[],[981,982],[],[983],[983],[983],[777,983],[981],[983],[983],[983],[777,983],[981]]),
([mw0,mw1,mw2,mw3,mw10,mw16,mw30,mw26],[[984,20058],[984,20167],[10006,20150],[],[49,984],[10006,20168],[10006,20151],[985,986],[984,20169],[984,987],[],[],[984,780],[984,20170],[984,988],[],[],[984,989],[990,20021],[197,20171],[991,984],[],[984],[363,699],[780,20151],[363,20069],[992,780],[984]]),
([mw0,mw1,mw2,mw3,mw10,mw16,mw30,mw36],[[884,30009],[884,30006],[884,777],[],[884,777],[884,993],[],[994,884],[777,780],[884,30083],[],[],[994,780],[777,885],[884,30039],[],[],[801,885],[884,777],[918,780],[777,780],[254,777],[884,777],[884,993],[],[884],[801,884],[884]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw24,mw30],[[995,996],[995,997],[998,995],[],[998,777],[],[998,995],[996,999],[995,999],[],[995,999],[995,999],[],[995,998],[],[995,999],[995,998],[],[],[999],[999],[777,999],[999],[999],[999],[999],[777,999],[995]]),
([mw0,mw1,mw2,mw12,mw3,mw18,mw40,mw27],[[1000,1001],[1000,1002],[],[1000,777],[],[],[1000,777],[1002,1000],[],[1002,780],[],[],[1002,780],[],[777,1003],[348,1001],[],[777,1003],[880,777],[1001],[],[880,1001],[1003,777],[10024,777],[699,10024],[1001],[1003,777],[1001]]),
([mw34,mw2,mw12,mw3,mw9,mw49,mw23],[[90,20172,30209],[],[90,1004,30210],[90,20172,30207],[],[90,20172,30137],[],[20172,1004,30030],[20172,1005,30029],[20172,98,444],[20172,10003,10023],[1004,1006],[1005,1007],[20172,98,1006],[1008,20172,10004,10023],[1004,90],[],[1004,20172,10027],[],[20172,1005,10029],[20172,10023,10027]]),
([mw0,mw1,mw2,mw3,mw9,mw57,mw46,mw38],[[624,20173],[624,383],[20173,10004],[20173,10006],[10004,20173],[20173,383],[20173,383],[139,386],[624,10012],[624,10014],[624,1009],[624,386],[624,386],[624,383],[624,383],[624,383],[],[],[938,30027],[120,624],[],[1010,383],[1009,624],[938,383],[],[624],[624],[938]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw31,mw60],[[364,448],[364,1011],[],[364,698],[1011,250],[],[364,1011],[448,364],[],[448,780],[364,699],[],[1011,364],[],[699,10019],[364,10021],[448,698],[448,30028],[448,698],[364,250],[448],[243,448],[364,20067],[448,698],[448,20067],[364,250],[364,1012],[364]]),
([mw0,mw1,mw2,mw12,mw3,mw9,mw73,mw23],[[1005,1013],[1005,1013],[],[1005,1013],[1013],[],[1005,1013],[1013],[],[1013],[1005,1013],[],[1013],[],[1013],[1005,1013],[1013],[1013],[1013],[1005,1013],[1013],[1013],[1005,1013],[],[1013],[1005,1013],[1005,1013],[1013]]),
([mw34,mw4,mw2,mw3,mw9,mw35,mw23,mw46],[[],[382,20174],[382,20175],[390,20176],[382,30207],[382,20173],[382,30137],[966,386],[966,387],[382,10006],[485,386],[10006,10008],[10006,386],[967,382],[382,386],[],[967,386],[],[382,387],[],[1014,387],[],[],[382,30000],[382,386],[1015,382],[382],[]]),
([mw34,mw4,mw2,mw3,mw9,mw31,mw46],[[],[448,265,30243],[448,265,329,30251],[265,20018,30207],[],[265,20018,30031],[265,20018,30028],[329,20018,30026],[20018,10021,10007],[],[20018,6,1016],[265,329,330],[265,20018,10021],[265,330],[],[329,20018,330],[329,330],[],[20018,10021,10007],[20018,10007,10021],[20018,6,1016]]),
([mw34,mw4,mw2,mw3,mw19,mw9,mw48,mw23],[[],[419,30209],[419,30210],[],[443,30207],[],[443,30137],[443,410],[410],[],[410],[],[410],[443,410],[],[443,410],[],[443,410],[],[410],[410],[410],[410],[410],[410],[],[410],[410]]),
([mw0,mw1,mw4,mw2,mw3,mw48,mw40,mw27],[[30000],[],[1017,1018],[1017,777],[],[],[1017,777],[],[1017,1019],[1017,780],[],[],[1017,780],[1017,1018],[1017,777],[],[],[1017,777],[777,1003],[],[],[777,1003],[1020,777],[842,777],[699,380],[83,1020],[20,777],[83,777]]),
([mw0,mw1,mw2,mw74,mw27,mw61],[[1021,230,30005,10002],[1021,230,30151,10003],[1021,230,165],[1021,230,165],[],[165],[165],[165],[165],[165],[165],[165],[165],[],[]]),
([mw0,mw1,mw2,mw3,mw75,mw27,mw64],[[69,20177,30064],[20177,1022,899,30246],[20177,10013,10005],[],[20177,190,30121],[20177,1023,30121],[69,899,190],[69,20177,10013],[69,20177,30019],[69,899],[],[899,20177,10019],[899,20177,30041],[899,69],[],[20177,10013,10005],[20177,10013,10024],[20177,10005,10013],[20177,190,915],[20177,1023,915],[]]),
([mw0,mw1,mw2,mw74,mw27,mw39],[[40,1024],[40,1024],[40,1024],[40,1024],[],[1024],[1024],[1024],[],[1024],[1024],[1024],[1024],[1024],[]]),
([mw34,mw4,mw2,mw3,mw9,mw50,mw23],[[],[419,780,20178,30209],[419,780,20055,30210],[20178,866,30207],[],[20178,10002,30137],[608,842,10004,444],[608,420,10000,10004,780],[10004,20178,1007],[],[10004,20178,780,10009],[842,1007,1025],[780,20178,444,442],[],[20178,1007,10023],[780,20178,444,20055,337],[],[20055,10009,10027],[],[20178,444,10029],[20178,1026,10009]]),
([mw34,mw4,mw2,mw3,mw19,mw9,mw35,mw23],[[],[421,20174],[421,20175],[],[421,30207],[421,30137],[421,30137],[421,1027],[421,957],[],[421,30044],[421,1006],[421,422],[1027,421],[],[957,1027],[],[957,386],[],[1027,957],[],[1027,387],[1028,421],[421],[10029,422],[],[422,10029],[422,386]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw31,mw46],[[30000,448],[448,30105],[448,30190],[],[429,250],[],[429,422],[448,30112],[448,30205],[],[429,252],[],[429,780],[30009,429],[],[448,254],[448,254],[],[],[448,1029],[448,1029],[],[10028,250],[448],[429],[885,250],[250,254],[448]]),
([mw0,mw1,mw2,mw3,mw76,mw53,mw23],[[108,20005,30180],[20005,780,457,30237],[20005,493,30252],[],[20005,199,10007],[20005,10017,10009],[108,457,493],[108,457],[108,20005,1030],[],[108,20005,10017],[457,108],[780,20005,457,1031],[],[457,20005,10023],[20005,493,1032],[],[20005,493,10027],[20005,199,10007],[20005,10017,10009],[20005,10007,10017]]),
([mw0,mw1,mw2,mw3,mw72,mw30,mw77],[[189,768,30031],[189,768,30105],[189,10004],[189,953,1033],[189,198,30082],[189,953,10006],[189,768,192],[189,192],[189,192],[],[189,192],[768,192],[768,192],[],[768,192],[192],[198,192],[192],[198,953,1033],[],[198,953,192]]),
([mw0,mw1,mw2,mw3,mw78,mw40],[[198,18,932,20],[198,18,20],[18,20],[18,20],[],[198,18,932,20],[198,18,20],[198,18,20],[],[198,18,20],[198,18,20],[],[20],[20],[20]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw79],[[18,10000,866],[18,866,10000],[18,671],[],[18,866,30121],[18,20033,995],[18,866,444],[18,20033,1034],[],[18,866,30122],[18,20033,1035],[18,20033,336],[],[18,866,30023],[18,20033,998],[],[866,20033,10025],[20033,101,10027],[866,20033,10025],[20033,126,10027],[866,20033,401]]),
([mw0,mw1,mw2,mw3,mw48,mw40,mw27],[[886,884,10000,1001],[886,884,10001,10000,1036],[10000,884,20033,777,10005],[],[],[10000,884,20033,777,309],[1037,1017,10002,1019],[10002,886,20033,780,10013],[],[],[10002,886,20033,780,775],[20033,10005,10019],[],[],[20033,351,386],[20033,10026,10005],[20033,10024,10005],[20033,10005,10026],[1001],[20033,18,1001],[1001]]),
([mw0,mw1,mw2,mw3,mw9,mw50,mw23],[[383,386,10000,866],[866,1038],[10000,386,671],[10000,386,866,1007],[],[10000,386,20033,309,10009],[866,1038,444],[1038,20033,1034],[866,1038,1039],[],[1038,20033,10017],[866,20033,421],[866,1038,442],[],[866,20033,10023],[866,20033,337],[],[20033,10009,10027],[],[866,20033,10029],[20033,7,10009]]),
([mw0,mw1,mw2,mw3,mw19,mw9,mw80],[[700,885,10000,866],[866,1038],[10000,885,700,671],[],[700,866,20060,30121],[10000,885,20060,10009],[866,1038,444],[1038,20060,1034],[],[885,866,1038,30122],[1038,20060,10017],[866,700,336],[],[700,866,1038,30023],[866,20060,10023],[],[885,866,20060,30000],[20060,10009,10027],[866,20060,30044],[20060,126,10009],[866,20060,401]]),
([mw55,mw1,mw2,mw3,mw9,mw50,mw23],[[383,386,10000,252,20005,10001],[252,780,10001,383,20005,10000],[10000,386,20005,10004],[10000,386,20005,10006],[],[10000,386,20005,30015],[608,842,10012,386,780,444],[608,383,10010,10012,780],[10012,383,20005,252,903],[],[10012,383,20005,780,10030],[842,903,421],[780,252,444,383,442],[],[903,20005,10031],[20005,444,337],[],[20005,10030,10032],[],[252,20005,444,10033],[20005,349,10030]]),
([mw81,mw1,mw2,mw3,mw9,mw53,mw23],[[1040,386,252,20005,10001],[1040,780,383,20005,10000],[252,386,10001,20005,10004],[1040,386,20005,10006],[20005,0,10001],[252,386,10001,20005,10008],[608,842,10012,386,780,444],[608,383,10010,10012,780],[10012,20005,252,903],[],[10012,20005,780,10017],[842,903,336],[780,252,444,386,442],[],[903,20005,10023],[20005,444,337],[],[20005,10017,10027],[],[252,20005,444,10029],[20005,349,10017]]),
([mw81,mw1,mw2,mw3,mw9,mw23,mw65],[[383,386,10000,252,20005,10001],[252,780,10001,383,20005,10000],[10000,386,20005,10004],[10000,386,20005,10006],[10000,386,20005,10008],[],[608,842,10012,386,780,10011],[608,383,10010,10012,780],[10012,383,20005,252,10015],[10012,383,20005,780,10017],[],[842,953,10011,387,383,10019],[780,252,10011,20005,383,10021],[10011,20005,383,10023],[],[20005,10015,10025],[20005,10017,10027],[],[252,20005,10015,10029],[],[]]),
([mw0,mw1,mw2,mw3,mw9,mw23,mw82],[[383,386,10000,252,422,10002],[252,780,10001,383,309,10000],[10000,386,700,309,10005],[10000,386,953,309,10007],[10000,386,892,422,10009],[],[422,309,10002,386,780,10011],[422,383,10002,387,780,10013],[422,383,10002,608,252,10015],[10002,383,206,780,10017],[],[10011,10005,700,383,10019],[780,252,10007,842,383,10021],[10011,422,892,383,10023],[],[780,252,10005,953,387,10025],[10005,422,892,700,10027],[],[252,422,10007,892,953,10029],[],[]]),
([mw0,mw1,mw2,mw3,mw9,mw57,mw56],[[383,386,10000,20007,30137],[20007,842,10004,383,10000],[10000,386,10004,20007],[10000,386,20007,10006],[10000,386,20007,1041],[20007,0,10000],[20007,842,10012,386,10010],[20007,383,10010,10012],[20007,10012,10014],[20007,10012,1042],[20007,6,10012],[842,953,10020,387,383,382],[382,383,10020],[10020,20007,383,938],[],[382,387,750],[1043,20007,120,387,939],[],[20007,1041,940],[],[20007,0,382]]),
([mw0,mw1,mw2,mw3,mw9,mw83,mw23],[[383,386,10000,866],[866,309,10000],[10000,386,671],[10000,386,866,309,10007],[],[10000,386,20033,309,10009],[866,444],[422,383,10002,20033,335],[866,252,10015],[],[10002,383,20033,780,10017],[866,20033,336],[866,10007,10021],[],[866,20033,10023],[866,20033,10025],[],[20033,10009,10027],[866,383,10007],[866,20033,30000],[20033,198,10009]]),
([mw34,mw4,mw2,mw3,mw9,mw23,mw56],[[],[472,842,20062,30209],[20062,386,592,20063,30210],[472,386,20007,30207],[20062,1044,30137],[20062,0,30137],[20062,465,10000],[20062,20063,10000,10004],[20062,20007,465,10006],[20062,10000,10008],[20062,6,10000],[842,1045,10020,382],[382,386,10020],[20062,10020,938],[],[1045,382,750],[20063,10019,948],[],[20007,382,940],[],[]]),
([mw0,mw1,mw2,mw17,mw74,mw27],[[377,74,933],[377,933],[],[377,74],[377,933],[74,933],[],[74,377],[74,933],[933],[933],[933],[377],[933],[933]]),
([mw0,mw1,mw2,mw12,mw3,mw74,mw27],[[248,175],[248,175,77],[],[248,20033,30005],[248,20033,30121],[248,20033,10007],[175,248],[],[77,20033,30001],[77,20033,30122],[77,20033,10015],[],[175,20033,30000],[175,20033,30023],[175,20033,10021],[20033,1046,30000],[20033,880,30000],[20033,126,10007],[],[20033,10007,414],[20033,10007,414]]),
([mw0,mw1,mw2,mw12,mw3,mw84,mw27],[[248,175],[248,175,77],[],[248,20033,10005],[],[248,20033,309],[175,248],[],[77,20033,10013],[],[77,20033,775],[],[175,20033,10019],[],[175,20033,386],[20033,10024,10005],[],[20033,1047,309],[20033,10024,10005],[20033,10005,10024],[20033,1047,309]]),
([mw0,mw1,mw2,mw3,mw84,mw27],[[248,77,175],[248,77],[248,30181,10005],[],[248,30015,10007],[77,248],[77,30084,10013],[],[77,30019,10015],[175,30055,10019],[],[175,30041,10021],[20006,10024,120,10005,30000],[20006,10005,10007,10024,10025],[20006,126,10025,222,10007]]),
([mw0,mw1,mw2,mw12,mw74,mw27],[[248,175],[248,175,77],[],[248,30005,10005],[248,30005,10007],[175,248],[],[77,30001,10013],[77,30001,10015],[],[175,30000,10019],[175,30000,10021],[20006,125,880,30000,10005],[20006,126,414,30000,10007],[20006,10005,10007,523,414]])]
noncomputable def mtopD6 : List StD := [
([mw4,mw22,mw7,mw14,mw26,mw27],[[171,774,491],[171,491],[499,494,20013,20000,30076],[1048,495,20013,20065,30078],[20013,496,503,20008,20067,30075],[774,491],[1049,494,20179,20000,30071],[1050,495,20179,20065,30073],[20179,496,1051,20180,20067,30038],[1052,494,20174,20042,30027],[1053,495,20174,20068,30026],[20174,496,1054,20181,20070,30000],[1055,175,500,501],[1056,1057,101,500,502],[175,1055,501,502]]),
([mw0,mw4,mw7,mw14,mw35,mw26,mw27],[[],[505,1058],[1049,30253],[491,20179],[1059,20182],[20179,20183],[505,1058],[1049,20184],[123,20179],[538,20184],[20179,20185],[1058,842],[1058,1049],[980,512],[1044,842],[],[1049,842],[1049,1060],[175,842],[1051,1060],[1049]]),
([mw0,mw4,mw7,mw14,mw26,mw38],[[],[552,842,1061,122],[1062,1063,139,20186,20023,30072],[20023,1064,30038],[20186,1063,1065,20023,30038],[552,842,1061,122],[1062,494,1066,20013,20023,30148],[20023,1067,30104],[20023,138,10011],[1062,552,471,842,1068,10021],[980,552,1069,663,10023],[20023,552,138,842,10011],[10021,1062,1070,842,940],[20023,1062,10011,1068,10021],[20023,10011,10023]]),
([mw0,mw1,mw22,mw14,mw26,mw64],[[1071,1069,10000,20041,30000],[],[10000,1069,20187,20041,30072],[10000,20041,30038],[20041,516,10000],[608,1071,693,943,699,10011],[943,1071,624,608,699,10015],[20041,1072,10017],[],[10011,10015,20187,1068,10021],[699,20041,10011,943,10023],[20041,516,1069,10011],[699,20041,10015,608,206],[20041,497,1069,10015],[20041,497,10017]]),
([mw0,mw7,mw6,mw35,mw46,mw27],[[552,1073,512,964,20188,10001],[1074,1075,965,10001,20184],[10001,721,964,20163,10000],[10001,1076,964,20164,10000],[10001,1077,579,20040,10006],[1074,552,146,512,964],[20188,552,624,512,1078],[20188,552,146,512,1079],[20188,552,967,30254,964,1077],[20184,1074,624,964,1078],[20184,1074,520,964,1079],[20184,1074,1080,30255,1060],[20163,20164,195,579,1081],[195,24,579,964,1077],[1082,20040,24,1081,964]]),
([mw0,mw7,mw6,mw8,mw16,mw45,mw27],[[624,252],[507,252],[252,1083],[1083,252],[1084,252],[1085,579],[624,1086],[624,507],[],[624,1086],[624,252],[624],[507,1087],[],[507,252],[507],[624],[252,1083],[195,579],[624],[507]]),
([mw0,mw7,mw6,mw16,mw46,mw27],[[624,20189,10001],[20189,965,10001],[20189,10004,10001],[20189,10001,10004],[20189,1077,579,10006],[624,1088],[],[624,20189,1089],[624,20125,1077],[171,579,965,1090],[624],[1080,381,1091,1092],[20189,195,1093],[624],[1094,20189,1077]]),
([mw0,mw1,mw22,mw14,mw26,mw47,mw38],[[1069,30256],[],[1069,20141],[212,20190],[1061,20191],[569,498],[1095,20006],[624,608],[520,1069],[],[486,1069],[551,842],[608,1069],[506,1069],[569,1069],[212,1069],[1096,1069],[486,1069],[1096,608],[486,608],[486,20069]]),
([mw0,mw1,mw22,mw14,mw35,mw26,mw85],[[506,422],[],[506,30072],[506,1097],[506,422],[],[506,422],[422,608],[422,608],[842,1098],[510,422],[506,842],[506,1097],[506,422],[],[],[422,608],[510,1098],[422,608],[510,1097],[510,422]]),
([mw0,mw1,mw22,mw14,mw37,mw38],[[506,20023,10002],[],[506,1099],[],[506,20023,1100],[506,20023,10002],[20023,494,10002,608,10012],[20023,520,10002],[20023,10002,10010],[506,842,1101],[506,1069,938],[506,842,1100],[1099],[20023,1102,1069,948],[20023,150,1100]]),
([mw0,mw7,mw14,mw45,mw38],[[552,1069,10034,20192,10001,30112],[20192,10001,1070,20193,10004,30000],[20192,10000,140,10001,30104],[20192,10001,1060,20143,10000,30000],[552,10034,30000,1103,1104],[552,146,20192,1069,1105],[552,633,20143,1069,1106],[20193,543,190,1070,1107],[20143,266,195,1070,1060,1108],[20194,150,96,1109,1060]]),
([mw32,mw4,mw33,mw9,mw28,mw26],[[],[],[1110,646,20085,30056],[646,393],[646,20085,577],[646],[1111,20085,576,10007],[576,1068,1112],[576,1113,1114],[20085,10007,10035],[349,20085,1112],[20085,349,1114],[20085,1115,10007,1068,10021],[20085,10007,10025],[646]]),
([mw0,mw1,mw12,mw14,mw26,mw38],[[552,506,10000,1116],[],[10000,506,20033,20195,30174],[10000,506,20033,20196,30105],[10001,506,10000,480],[],[480,552,624,20033,20197,30226],[480,552,520,20033,20198,30112],[10002,552,943,699,10011],[20033,521,10021],[20033,146,10023],[20033,126,10011],[1116],[20033,10011,10021],[20033,10011,10023]]),
([mw0,mw1,mw22,mw14,mw45,mw38],[[552,1069,10000,20199,20200,30000],[],[10000,1069,20187,20200,30072],[10000,20200,30109],[20199,20200,387,10000],[1098,552,693,20200,20198,30112],[1117,552,624,1098,1118],[],[10012,552,1069,780,10017],[20200,494,762,20187,10021],[20200,140,10023],[20200,387,10003],[20200,1117,10021,1069,1118],[266,1117,1069,387],[20200,10003,387]]),
([mw0,mw1,mw22,mw14,mw54,mw26,mw38],[[506,480],[],[506,20187],[],[506,30038],[506,480],[506,480],[480,608],[10016,480],[480,10016],[450,608],[506],[],[506,663],[506,480],[],[522,608],[480,963],[1119,608],[1119,480],[480,608]]),
([mw0,mw1,mw2,mw14,mw26,mw63],[[579,608,10000,252,480,10002],[579,1069,10001,10000,480],[10000,1069,1120,1121,10007],[10000,608,579,1100,10009],[],[608,842,10002,943,699,10011],[480,579,10002,608,252,10015],[480,1120,10002,1069,780,10017],[],[480,579,10007,842,1068,10021],[480,608,10009,1069,943,10023],[],[252,10009,579,608,206],[20006,125,10007],[20006,125,10009]]),
([mw34,mw4,mw2,mw14,mw26,mw39],[[],[1122,20201,30075],[1122,20202,30077],[1122,20201,30075],[],[608,20201,123,10003],[123,608,396],[123,1069,1123],[],[20201,20202,10003,10018],[20201,10003,10018],[20201,10018,10003],[1122],[20201,20202,396],[20201,396]]),
([mw0,mw1,mw2,mw14,mw37,mw64],[[579,1069,10010,20084,20069,30075],[579,1069,10011,20084,20069,30038],[20069,206,10005],[],[20069,516,10009],[20084,10014,10010],[10010,579,10014,20084],[10010,20084,10017],[],[20084,579,10011,842,10021],[20084,10011,10023],[],[20084,20069,10017,206],[20069,10005,206],[20084,574,10009]]),
([mw0,mw1,mw2,mw86,mw42,mw27],[[1124,1069,10004,1125],[10004,1069,20076,480,10003],[1125,1126],[],[10004,20076,584],[349,20076,10011],[1125,349,1127],[],[480,1124,1126,349,1128],[1125,20076,10018],[20076,150,10003],[20076,10003,10021],[],[1125,1069,206],[1125]]),
([mw34,mw4,mw2,mw14,mw26,mw38],[[],[506,693,30075],[506,20024,30230],[506,20023,30257],[506,20024,30137],[506,20024,10000],[20024,10000,10004],[20024,20023,10000,10004],[20024,10004,10000],[506,1129],[506,1069,325],[],[693],[20024,1129],[20024,20023,1129]]),
([mw0,mw1,mw87,mw14,mw26,mw38],[[506,693,30075],[506,552,1130],[506,1120,10004],[506,10004],[506,1120,10000],[506,693,1131],[693,608,10012],[693,10012],[693,608,10010],[506,1129],[506,325],[506,693],[693],[1129],[1129]]),
([mw0,mw1,mw2,mw14,mw88,mw38],[[506,693,30257],[506,552,10000],[506,1120,10004],[506,10004],[506,10000],[506,693,10010],[693,608,10012],[693,10012],[693,10010],[506,1129],[506,325],[],[693],[1129],[1129]]),
([mw0,mw1,mw2,mw14,mw26,mw89],[[506,1122,10002],[506,1041,10003],[506,396],[506,1123],[],[506,1122,30062],[1122,608,10012],[1122,10012],[1122,10002],[506,842,10018],[506,10018],[506,10003],[1122],[396],[396]]),
([mw0,mw1,mw2,mw21,mw45,mw38],[[691,1069,10004,20203,20204,30066],[10004,1069,20075,20200,30072],[],[20200,140,10004],[10004,20200,10007],[20204,691,10012,20075,30000],[20075,693,10012],[],[20204,691,10007,1069,20075,10017],[20075,624,10021],[20075,20200,140,10023],[],[20200,20075,10021,206],[20075,10017,10007],[20200,10007,10017]]),
([mw0,mw1,mw90,mw62,mw26,mw27],[[123,711,30075],[123,10000],[123,833,30005],[123,1132,10008],[123,1132,10008],[123,20205,493],[],[123,512,1133],[123,608,726],[833,20205,493],[20205,608,1134,1132,10018],[20205,10018,10020],[833,20205,1133],[833,20205,726],[711]]),
([mw32,mw1,mw19,mw9,mw28,mw26],[[646,576,101],[],[646,20085,30007],[646,1135],[646,20085,1136],[],[576,20085,10035],[576,1068,1112],[576,1113,1114],[20085,274,10035],[349,20085,1112],[20085,349,1114],[20085,1137,10035,1068,10036],[20085,10035,10037],[646]]),
([mw0,mw4,mw8,mw33,mw13,mw26,mw27],[[],[592,30141],[143,592],[1138,20174],[1139,20175],[1140,20087],[592,1141],[592],[588,601],[589,603],[590,20087],[],[592,512],[592,1142],[592,1143],[921,512],[1144,965],[20087,1143],[1050,592],[592],[592]]),
([mw0,mw4,mw8,mw13,mw26,mw47],[[],[252,587,20089,30026],[20089,588,20206,30239],[252,589,20207,20089,30031],[20089,1145,1146],[20089,587,30258],[20207,588,20206,252,10015],[20206,589,20207,423,10017],[20089,1145,1146],[774,252,1147,1148],[1147,423,1149],[20089,101,1150],[252,423,10015,1148,608],[575,101,252,1151],[108,101,423,1143,10017]]),
([mw0,mw1,mw8,mw13,mw26,mw39],[[1152,608,10006,1153],[10006,587,20106,20208,30218],[423,588,10006,250],[10006,608,20106,422,10009],[],[608,1152,587,20106,20087,30103],[422,1152,588,608,20087,10015],[250,1152,10009,20106,423,10017],[],[20106,10015,10018],[1153],[20106,24,1150],[20106,10009,10018],[20106,10018,10015],[20106,24,10009]]),
([mw0,mw7,mw6,mw13,mw14,mw30,mw44],[[749,423],[1154,423],[423,953],[423,953],[1155,423],[1156,953],[749,1157],[749,1158],[749,30023],[],[749,423],[273,749],[749],[120,1157],[749],[749],[774,953],[749],[493,749],[],[749]]),
([mw0,mw7,mw6,mw13,mw30,mw44],[[953,20090,10004,10001],[20090,1159,10000,10004],[20090,1160,10004,953,10000],[20090,10004,10001],[20090,10001,10004],[1074,953,763,1161],[1162,273,1163],[],[20090,98,1104],[763,1074,953,1164],[20090,1074,1161],[190,1074,953,1165],[20090,1162,1163],[195,1162,1166,1167],[20090,98,1104]]),
([mw0,mw1,mw8,mw13,mw26,mw36,mw47],[[1168,30137],[1168,20209],[1168,1169],[1168,1170],[],[1168,1171],[1122,20210],[1172,1173],[1174,1175],[923,1168],[],[1122,1176],[1177,1178],[619,20209],[1179,20210],[894,1180],[1042,1169],[1041,1173],[507,1170],[1174,1175],[1168]]),
([mw0,mw1,mw8,mw13,mw26,mw36,mw56],[[622,10002],[622,30218],[622,1181],[622,1182],[],[622,1183],[10002,1184],[10002,608],[10002,1184],[1129,10002],[10002,1184],[1185,1181],[608,1182],[120,622],[],[620],[120,1181],[],[1129,1182],[],[622]]),
([mw0,mw1,mw8,mw13,mw26,mw27,mw91],[[622,10002],[622,1186],[622,1187],[622,1188],[622,1189],[],[10002,601],[10002,601],[10002,603],[10002,608],[507,10002],[1187],[1186],[20211,622],[],[20212,622],[1186],[],[1187],[],[]]),
([mw0,mw1,mw8,mw15,mw45,mw27],[[1190,1191,10000,20066,20022,30000],[20022,1191,587,10000],[],[10000,1191,20066,20022,30015],[10000,1191,20022,1192],[20066,1190,587,1193],[20066,479,30259],[],[20066,590,1194],[20066,20022,479,10003],[20022,20066,1193],[10003,197,1195,1143,1150],[20066,285,1196],[20066,1192],[20066,1194]]),
([mw0,mw1,mw8,mw13,mw37,mw47],[[1197,608,10004,20038,20089,30031],[20089,587,10004],[10004,20038,20089,30015],[],[10004,20089,10009],[608,1197,587,20089,30103],[20038,588,1198],[20038,589,10017],[],[569,20038,1199],[20038,608,10017,1200],[20089,10009,1150],[20038,10017,1196],[20038,10009,1198],[20038,108,10009]]),
([mw0,mw7,mw6,mw13,mw26,mw36],[[623,20090,30260],[623,20091,30261],[623,20091,1201],[623,20090,1202],[],[669,1041,1203,1204],[1205,135,1206,1207],[20090,1208,1209],[20090,577,10021],[20091,1041,1210],[1211,1212],[20091,10021,10027],[1213,1214,579,953,10029],[20091,577,1201],[20090,10021,1202]]),
([mw4,mw22,mw6,mw13,mw26,mw27],[[629,587,1215,1216],[1217],[629,587,1215,480],[1096,587,1218,668],[1219,587,20213,20214,30262],[507,139,1220,480],[1216,1217],[980,645,20215,20216,30182],[1221,646,1222,647],[472,486,20181,20055,30027],[480,1223],[480,510,1224,1225],[480,1226,1227,1228],[480,646,1223],[20216,20214,510,1228,1225]]),
([mw0,mw7,mw6,mw13,mw26,mw38,mw44],[[1229,1230],[1231,1083],[1083,1230],[1230,1083],[1232,1230],[1233,1083],[171,1230],[1095,1234],[146,1235],[1083,1236],[624,1230],[171,1230],[1230,1237],[507,1230],[624,1237],[1067,1095],[],[624,1230],[507,1083],[],[624,1230]]),
([mw0,mw7,mw6,mw13,mw62,mw30,mw26],[[967,423],[381,423],[423,941],[941,423],[1238,423],[1239,1083],[967,1240],[967,381],[967,381],[],[967,423],[381,967],[],[381,967],[967],[967],[1083,1241],[423,941],[493,1083],[941,423],[967]]),
([mw0,mw1,mw8,mw13,mw26,mw38,mw61],[[714,10002],[714,1186],[714,1242],[714,1243],[714,579],[],[10002,1244],[10002,608],[10002,1244],[10002,608],[1129,10002],[1243],[1186],[1243],[1186],[1208,1243],[],[1186],[1243],[],[1186]]),
([mw0,mw1,mw8,mw15,mw46,mw27,mw44],[[1245,10002],[1245,1246],[],[1245,1247],[1245,1248],[1245,1249],[10002,1184],[273,10002],[10002,1184],[10002,608],[10002,1184],[1246],[],[664,1248],[1249,664],[52,1247],[664,1248],[52,1249],[1247,1248],[1247,608],[]]),
([mw0,mw1,mw8,mw13,mw37,mw38,mw44],[[714,10002],[714,1250],[714,30015],[],[714,1251],[714,1252],[10002,1244],[10002,608],[1253,10002],[10002,608],[10002,1244],[1254,1255],[1250],[1251,1250],[1250],[171,608],[],[1250],[171,1251],[714],[1250]]),
([mw0,mw1,mw8,mw13,mw21,mw37,mw38],[[1256,422],[1256,1257],[1256,30263],[],[],[1256,422],[422,1244],[422,608],[943,422],[953,422],[1083,608],[1258,1259],[1257],[1257],[422,1244],[1257],[1258,608],[],[943,608],[454,422],[1258]]),
([mw0,mw1,mw8,mw15,mw29,mw44],[[941,608,10000,20217,10002],[1260,1261,274,941,1262],[],[],[10000,1261,20218,422,1263],[608,1264,10002,943,20217,10010],[20217,10012,10002],[20217,10012,10002],[20217,941,10002,608,10012],[20217,1260,274,1262],[1262],[498,1260,1265,941],[20217,171,1266],[497,20217,941,1263],[434,945,608,941,1263]]),
([mw0,mw1,mw22,mw8,mw62,mw45,mw27],[[486,30001],[],[1133,486],[703,20219],[711,20219],[20219,20220],[486,20221],[486,1267],[],[],[486,1268],[486],[833,20219],[608,20219],[20219,20066],[1267],[1267],[1219,387],[457,486],[486],[486]]),
([mw0,mw1,mw22,mw6,mw35,mw46,mw27],[[512,30000],[],[382,20222],[687,1269],[669,1270],[512,20223],[1074,20188],[],[1271,512],[1272,512],[1273,20224],[1074,512],[687,512],[669,512],[1274,941],[1271,601],[1272,601],[1273,512],[457,514],[497,512],[457,512]]),
([mw0,mw1,mw2,mw14,mw49,mw37,mw47],[[726,30075],[726,698],[726,698],[],[],[726,422],[698,699],[698,726],[],[353,423],[],[777,842],[10022,698],[699,698],[698,699],[],[699,698],[726],[159,726],[726],[726]]),
([mw0,mw7,mw6,mw11,mw28,mw44],[[953,754,10004,941,20064,10001],[941,273,20225,10004],[10004,1275,953,20226,10001],[10004,1276,941,20034,10000],[10001,1277,953,20021,10004],[20064,953,273,1278],[20064,20226,633,1279,1280],[273],[20064,20021,98,1281,941],[273,953,1278],[273,1108],[273,953,1108],[20226,20034,774,1282,953],[273],[20034,20021,98,953,941,1108]]),
([mw0,mw1,mw8,mw13,mw29,mw44],[[941,1261,10000,20004,10002],[20004,1261,274,941,10000],[20004,1261,687,941,10000],[],[10000,1261,20004,1283],[20004,946,10010],[20004,620,10010],[20004,507,10002],[20004,10002,10012],[274,687,620,946,1284],[946,1284],[20004,1283,620],[620,1284],[20004,1283,946],[20004,1284]]),
([mw0,mw1,mw92,mw13,mw26,mw36],[[669,20040,10002],[669,20040,498],[669,1285],[669,616],[],[20040,10002,616],[20040,616],[20040,10002,616],[20040,616],[669],[20040,1285],[20040,1285],[616],[20040,1285],[669]]),
([mw0,mw1,mw22,mw33,mw14,mw93],[[941,813,20005,30264],[],[20005,199,1038],[941,20005,499,10007],[20005,334,10009],[813,444],[],[813,499,335],[813,20005,67],[20005,199,444],[499,10007],[1286,20005,814,941,10009],[813],[20005,10009,67],[20005,499,1287]]),
([mw0,mw1,mw22,mw33,mw16,mw26,mw27],[[624,30000],[],[363,601],[1287,601],[444,20227],[20227,20167],[624,601],[],[],[624,1089],[624,1288],[363,699],[1287,699],[699,601],[867,601],[363,20005],[624],[503,601],[1048,601],[624],[444,1289]]),
([mw0,mw1,mw8,mw13,mw37,mw46,mw36],[[1290,422],[1290,30157],[1290,1291],[],[1290,422],[],[422,1184],[422,1292],[1003,422],[250,1184],[1293,422],[250,1184],[1291],[],[68,1184],[1041,1184],[422,1184],[1291],[1290],[1003,1184],[68,422]]),
([mw0,mw1,mw22,mw14,mw46,mw38,mw44],[[941,10002],[],[941,30146],[274,941],[939,941],[938,30197],[608,10002],[10002,608],[10002,943],[10002,608],[941,608],[1294,30025],[274,1295],[939,1295],[506,941],[274,608],[657,939],[],[274,939],[274,941],[506,941]]),
([mw0,mw1,mw2,mw14,mw37,mw39,mw44],[[569,1296],[569,480],[569,30121],[],[],[569,583],[608,10011],[480,608],[292,480],[],[480,608],[480,842],[608,480],[963,480],[480,842],[569],[1296],[],[1296],[569],[1296]]),
([mw0,mw1,mw8,mw15,mw21,mw46,mw27],[[1297,250],[1297,30265],[],[],[1297,30015],[1297,250],[250,943],[700,250],[943,250],[250,943],[1003,608],[185,700],[139,1003],[],[250,943],[185,700],[392,700],[141,250],[392,1003],[943,250],[250,943]]),
([mw0,mw1,mw22,mw5,mw35,mw46,mw27],[[506,10002],[],[],[506,1269],[506,1270],[506,20009],[506,10002],[608,10002],[10002,608],[10002,943],[10002,608],[506,969],[506,1269],[506,1270],[506,20009],[506],[506],[943,20009],[969],[20009,943],[20009,608]]),
([mw0,mw1,mw2,mw14,mw37,mw36,mw94],[[608,30031],[1298,723],[1298,30005],[],[],[1298,723],[608,10011],[570,608],[292,1298],[1299,608],[],[723,842],[608,723],[10011,723],[506,10011],[1298],[570,1298],[],[1298],[1298],[1298]]),
([mw34,mw2,mw3,mw18,mw40,mw27],[[887,1037,30100],[887,20228,30009],[],[],[887,20228,30137],[887,20228,10019],[887,1300],[],[887,1301],[20228,943,10019,1302,10005],[20228,608,10019],[20228,10019,10024],[20228,1300],[1303,1003,61,950],[20228,1300]]),
([mw0,mw1,mw95,mw14,mw28,mw61],[[274,20229,10002],[274,20229,30266],[274,1304],[274,1304],[],[20229,10002,1304],[20229,1304],[20229,10002,1304],[20229,1304],[20229,1304],[274],[20229,1304],[1304],[],[20229,1304]]),
([mw0,mw1,mw22,mw74,mw27,mw56],[[941,608,10000,20230,10002],[],[941,608,10000,522,20230,30265],[10000,20230,30058],[20230,199,10000],[608,842,10012,10002,20230],[20230,522,10012],[20230,10002,10014],[20230,10002,10012],[522,382],[1286,1305,941,938],[20230,199,842,382],[522,608,939],[],[]]),
([mw0,mw1,mw22,mw74,mw27,mw64],[[1072,20177,30214],[],[20177,222,10005],[20177,503,30058],[20177,199,1300],[1072,884],[1072,20177,10013],[1072,503,812],[],[699,20177,222,10005],[503,951],[20177,199,884],[20177,10005,1253],[20177,10005,10013],[]]),
([mw0,mw1,mw2,mw14,mw96,mw94],[[292,20231,30031],[20231,10011,10003],[20231,570,30146],[],[20231,199,947],[292,20231,10011],[292,570,1133],[292,806],[],[20231,570,10018],[20231,10011,10003],[20231,10003,10011],[570,1298],[],[20231,199,947]]),
([mw0,mw1,mw8,mw13,mw28,mw61],[[953,1306,10010,20021,250,10002],[579,1306,274,1258],[1258,250,1307],[1308,1306,921,20021,1283],[],[20021,953,10002,10010],[20021,10002,10010],[20021,10002,10010],[10010,20021,10002],[274,250,953,1307,750],[1307,20021,939],[20021,1258],[20021,1258,940],[20021,1258,1307],[20021,1258]]),
([mw0,mw1,mw2,mw19,mw14,mw80],[[941,943,10000,866],[866,1038],[],[941,1003,10000,1309],[10000,943,20033,422,10009],[866,1038,444],[],[943,1038,20033,335],[1038,20033,10017],[],[866,20033,1310],[866,20033,10023],[866],[20033,126,10009],[20033,10009,592]]),
([mw0,mw1,mw12,mw8,mw74,mw27],[[813,1311,175],[],[1311,1312],[1311,1312,30121],[1311,20033,10007],[],[813,1313],[813,1312,30122],[813,20033,10015],[1312],[1312,20033,1310],[20033,463,10007],[813],[20033,10007,414],[1312,20033,414]]),
([mw0,mw1,mw22,mw33,mw74,mw27],[[813,20005,30214],[],[20005,199,1038],[20005,499,30005],[20005,1314,10007],[813,444],[],[813,499,335],[813,20005,10015],[20005,199,444],[499,336],[1286,20005,10015,10007],[813],[20005,10007,10015],[20005,499,120]]),
([mw0,mw1,mw2,mw17,mw97,mw27],[[1315,91],[1315,20076,30038],[],[1315,671],[1315,20076,10007],[671,958,30000],[],[958,1034],[958,20076,10015],[20076,671,336],[],[20076,671,254],[20076,671],[20076,254,10007],[20076,10007,254]]),
([mw0,mw1,mw2,mw5,mw98,mw27],[[958,20005,30075],[20005,824,30038],[],[20005,759,671],[20005,414,10007],[958,824,444],[958,335],[],[958,20005,775],[824,336],[],[824,20005,254],[20005,759,671],[20005,254,414],[20005,10007,414]]),
([mw0,mw1,mw8,mw13,mw21,mw28,mw44],[[1316,10002],[1316,670],[1316,217],[],[1316,20045],[1316,1307],[10002,943],[10002,943],[943,10002],[10002,943],[10002,608],[670,1317],[670],[217,670],[670],[670,217],[670,217],[670,217],[1318,20045],[1316],[670]]),
([mw0,mw1,mw8,mw13,mw21,mw28,mw37],[[1319,422],[1319,1258],[1319,1320],[],[1319,422],[],[422,943],[422,943],[943,422],[414,943],[1003,422],[1258,414],[1258],[422,414],[1258],[1258,1320],[422,1321],[1258,943],[1318,422],[1258],[1258]]),
([mw0,mw1,mw2,mw86,mw26,mw39],[[569,1122,1125],[569,20162,10003],[569,1125,1322],[569,584],[],[1122,20162,10011],[1122,1125,1323],[1122,1128],[],[1125,20162,10018],[20162,10003,10018],[20162,10018,10003],[569],[1125,20162,1298],[1125]]),
([mw0,mw1,mw2,mw5,mw99,mw43],[[1324,20005,30267],[20005,699,1325,30268],[],[20005,414,10007],[20005,59,1326],[1324,1325,338],[1324,580],[1324,20005,1327],[],[699,1325,1328],[1325,20005,254],[],[20005,254,414],[20005,59,1326],[20005,10007,414]]),
([mw0,mw1,mw2,mw19,mw14,mw68],[[941,943,10000,1058],[423,512,76,941,10000],[],[941,1058,76,1309],[10000,943,20033,76,1102],[76,943,444],[],[943,1058,76,335],[76,20033,1329],[],[1058,20033,336],[20033,101,10023],[1058,1309],[20033,126,10023],[1058,20033,592]]),
([mw0,mw1,mw35,mw46,mw38,mw44],[[941,943,10000,10001,10002],[10001,1330,941,30025,10000],[10001,1306,941,30024,10000],[10001,1331,941,30023,10000],[10000,943,1120,30000,10004],[10002,1332,943,30269,10010],[10002,1120,943,30040,10010],[10002,1333,943,30039,10010],[10002,941,608,30038,10012],[521],[521],[120],[521],[521],[521]]),
([mw0,mw1,mw2,mw21,mw37,mw47,mw44],[[569,30075],[569,698],[],[],[569,30121],[569,698],[698,10011],[1299,608],[690,1334],[],[698,608],[10011,698],[10011,698],[698,10011],[10011,842],[569],[1335,1299],[569],[690,608],[569],[698,1298]]),
([mw0,mw1,mw2,mw100,mw35,mw46,mw27],[[382,20175],[382,941],[382,20175],[382,941],[382,941],[382,579],[1336,943],[1336,120],[579,943],[1336,943],[941,608],[120,382],[],[],[966,941],[382],[382],[941,414],[382],[966,382],[382]]),
([mw0,mw1,mw2,mw3,mw18,mw101,mw27],[[830,1125],[830,698],[1125,698],[],[],[830,422],[698,699],[830,1337],[],[],[354,699],[830,20232],[20232,698],[608,698],[698,842],[830,698],[830,698],[830,238],[1125],[239,1125],[1125]]),
([mw0,mw1,mw2,mw3,mw18,mw31,mw102],[[830,1125],[830,480],[1125,777],[],[],[830,777],[842,699],[830,1338],[],[],[480,699],[830,20233],[20233,480],[20233,480],[480,842],[830,777],[830,777],[830,360],[1125],[239,1125],[1125]]),
([mw34,mw4,mw2,mw3,mw35,mw46,mw27],[[],[382,20174],[382,20175],[382,20234],[382,20235],[382,20236],[608,943],[608,512],[238,608],[842,943],[414,608],[1261,382],[],[],[414,943],[],[],[943,512],[382],[1014,382],[382]]),
([mw34,mw2,mw3,mw18,mw31,mw38],[[212,887,30100],[212,20237,30009],[],[],[212,20237,30009],[887,20237,10019],[887,842,1339],[887,238,951],[],[20237,579,777,10005],[20237,842,10019,238,10005],[20237,10005,10019],[212],[20237,6,1339],[20237,6,842,951]]),
([mw0,mw1,mw2,mw21,mw62,mw37,mw47],[[608,30075],[842,698],[],[569,698],[],[1340,1341],[608,699],[568,608],[],[842,1342],[],[845,842],[777,842],[608,698],[698,842],[569,698],[699,608],[568,1341],[74,608],[698,1298],[74,608]]),
([mw0,mw1,mw2,mw74,mw39,mw44],[[360,1343,1125],[360,20238,10003],[360,1125,30121],[],[360,584],[1343,20238,10011],[1343,1125,30122],[],[1343,1128],[1125,20238,10018],[20238,10018,10003],[20238,10003,10018],[1125,20238,1344],[],[1125]]),
([mw0,mw1,mw2,mw74,mw36,mw94],[[1343,20239,30137],[20239,10011,10003],[20239,842,570,30005],[],[20239,199,584],[1343,20239,10011],[1343,570,1133],[1343,806],[],[20239,570,10018],[20239,10011,10003],[20239,10003,10011],[570,842,1298],[],[20239,199,584]]),
([mw0,mw1,mw2,mw74,mw36,mw64],[[1345,20177,30137],[20177,842,1346,30058],[20177,238,10005],[],[20177,199,1347],[1345,1346,884],[1345,20177,10013],[1345,812],[],[1346,20177,10019],[1346,842,1339],[],[20177,10013,238],[20177,10005,238],[20177,199,1347]]),
([mw0,mw1,mw2,mw12,mw3,mw73,mw27],[[1348,1058],[1005,1348],[],[1058,1348],[],[1005,777],[1348,1005],[],[1348,1005],[],[1348,699],[],[1058,20098],[592,1058],[777,10021],[1058,777],[1058],[414,777],[],[1058,414],[10021,777]]),
([mw0,mw1,mw95,mw14,mw29,mw44],[[274,20034,10002],[274,1349],[274,20034,30082],[],[274,1350],[20034,1351,946,10010],[20034,10002,10012],[20034,10012,10002],[20034,10002,10012],[1349,946,114],[274],[946,114],[20034,1349,1352],[],[20034,1349]]),
([mw0,mw1,mw12,mw74,mw27,mw38],[[519,1064,239],[],[1064,20033,10005],[1064,20033,30058],[1064,941,1353],[],[519,20033,10013],[519,20033,30062],[519,943,884],[20033,521,10005],[20033,126,951],[20033,126,1353],[20033,10005,238],[20033,10005,238],[]]),
([mw0,mw1,mw2,mw14,mw103,mw44],[[360,1125],[360,20162,10003],[360,1125,30082],[],[360,584],[292,20162,10011],[1125,292,30099],[],[292,1128],[1125,20162,10018],[20162,10018,10003],[20162,10003,10018],[1125,20162,1298],[],[1125]]),
([mw0,mw1,mw2,mw74,mw27,mw61,mw94],[[1298,30137],[1298,10003],[1298,836],[1298,570],[],[1298,584],[10003,10011],[570,836],[836,570],[481,1298],[],[10003,512],[10003,1354],[10011,10003],[10003,10011],[836,1298],[],[],[],[],[1298]]),
([mw0,mw1,mw2,mw74,mw27,mw39,mw61],[[1355,1356],[360,698],[360,1356],[1356,1355],[],[],[1355,10011],[1355,30063],[1355,360],[],[1355,806],[10011,10018],[1356,1354],[10018,698],[10011,698],[1356,360],[134,1355],[],[],[],[1355]]),
([mw0,mw1,mw2,mw74,mw27,mw39,mw85],[[1347,1054],[1354,1054],[1354,698],[1054,1347],[],[],[1347,30062],[1347,10013],[1347,212],[],[1347,812],[10013,10019],[1054,1354],[188,1347],[],[1054,1354],[10019,1354],[10013,1354],[],[],[1347]]),
([mw34,mw4,mw2,mw3,mw48,mw40,mw27],[[],[884,30100],[884,30009],[],[],[884,30009],[1017,884],[1017,698],[],[],[1017,699],[699,1003],[],[],[698,1003],[579,698],[842,698],[698,380],[884],[932,884],[884]]),
([mw0,mw1,mw2,mw74,mw27,mw104],[[579,512,10004,1357],[579,512,10004,20076,698,10003],[423,238,10004,698],[10004,512,579,1355],[],[1355,20076,10011],[1355,512,1133],[1357,423,806],[],[20076,10003,10018],[1357,20076,10020],[20076,51,10003],[1357,512,238],[],[]]),
([mw0,mw1,mw2,mw74,mw27,mw63],[[579,943,10000,1358],[579,1358,1353],[10000,238,20033,698,10005],[10000,943,579,1347],[],[1358,1353,884],[943,579,1353,20033,10013],[1353,20033,812],[],[1358,20033,10019],[1358,20033,1339],[],[20033,10005,238],[20033,125,238],[]]),
([mw0,mw1,mw2,mw17,mw74,mw27,mw39],[[1359,1125],[1360,698],[],[1125,1359],[1360,1359],[],[1359,699],[],[1359,1360],[1359,1360],[],[842,698],[1125,10018],[698,842],[10018,698],[1359],[244,1125],[1125],[1125,842],[1125,698],[]]),
([mw0,mw1,mw2,mw3,mw84,mw27,mw39],[[1361,1362],[364,1361],[364,698],[],[1362,1361],[],[1361,364],[1361,1337],[],[1361,364],[],[699,10019],[],[1362,30023],[239,1362],[842,698],[1362,380],[10019,698],[1362,1337],[1362],[]]),
([mw0,mw1,mw2,mw12,mw74,mw27,mw39],[[1361,1358],[1358,1361],[],[1363,698],[699,1361],[],[1361,699],[],[1361,1337],[1361,699],[],[],[1358,10019],[1358,30000],[1358,698],[380,698],[244,1358],[1358],[698,380],[10019,698],[]]),
([mw34,mw2,mw3,mw19,mw9,mw31,mw46],[[607,20240],[607,20241],[],[607,30207],[],[607,30137],[1364,607],[],[579,254],[1014,254],[],[],[1364,1365],[1364,1365],[],[1132,254],[607],[607],[943,579],[423,579],[1014,607]]),
([mw0,mw1,mw92,mw14,mw105,mw36],[[579,943,687,20040,10002],[579,687,20040,30197],[687,1307],[687,579,1366],[],[20040,10002,10010],[943,579,10002,1367,20040,10013],[20040,10002,10010],[20040,10010,10002],[20040,579,1307,1367,1368],[],[20040,1307,1368],[1367,579,1352],[687],[20040,1307]]),
([mw0,mw1,mw2,mw86,mw106,mw39],[[579,569,244],[579,569,20162,10003],[569,20162,30121],[569,579,584],[],[1122,20162,10011],[584,1122,30122],[1122,1128],[],[20162,10003,10018],[20162,10003,10018],[20162,10018,10003],[],[20162,584,1298],[20162,584]]),
([mw0,mw1,mw2,mw3,mw107,mw108],[[941,943,10000,1369],[1369,1370],[941,1337,10000,1326],[10000,943,20033,777,309],[],[1369,1370,338],[943,1370,20033,1371],[1370,20033,775],[],[1369,20033,607],[1369,20033,254],[],[20033,254,387],[],[20033,126,309]]),
([mw0,mw1,mw2,mw19,mw74,mw27],[[941,943,10000,1369],[1369,1370],[],[941,1337,10000,1326],[10000,943,20033,777,10007],[1369,1370,444],[],[943,1370,20033,1371],[1370,20033,10015],[],[1369,20033,607],[1369,20033,10021],[1369],[20033,126,10007],[20033,10007,592]]),
([mw0,mw1,mw2,mw3,mw83,mw27],[[941,943,10000,1369],[1369,1370],[941,1337,10000,1372],[],[10000,943,20033,777,309],[1369,1370,444],[943,1370,20033,1371],[],[1370,20033,775],[1369,20033,607],[],[1369,20033,254],[],[20033,254,387],[20033,126,309]]),
([mw0,mw1,mw12,mw74,mw97,mw27],[[1373,239],[],[1311,20033,30265],[1311,941,1370],[1311,20033,10007],[],[1373,20033,30270],[1373,943,444],[1373,20033,10015],[20033,125,336],[20033,125,1370],[20033,463,10007],[],[20033,10007,414],[20033,10007,414]]),
([mw0,mw1,mw2,mw74,mw83,mw27],[[941,943,10000,1369],[1369,1370],[941,1337,10000,1326],[],[10000,943,20033,777,10007],[1369,1370,444],[943,1370,20033,335],[],[1370,20033,10015],[1369,20033,607],[],[1369,20033,10021],[],[20033,10007,387],[20033,126,10007]])]
noncomputable def mtopD5 : List StD := [
([mw4,mw22,mw14,mw26,mw64],[[1374,518,943,699,1375],[943,254,238,608,699,10015],[1376,254,380,1069,1377,10017],[20181,516,943,1378],[423,10015,842,254,10021],[699,608,380,1069,943,10023],[20181,516,699,1362],[699,943,10015,238,608],[20181,1052,238],[20181,1052,380]]),
([mw4,mw22,mw33,mw16,mw26,mw27],[[606,1379],[1379],[1379],[380,1337],[1380,1381],[1379],[1379],[380,1003],[1382,254],[1056,20174],[380,1337],[1056,1381],[1055,380],[20174,1381],[1003,380]]),
([mw4,mw22,mw14,mw45,mw38],[[1383,518,941,423,10001],[941,254,1117,1244,1338,10013],[1096,254,1244,422,10002],[1384,414,941,423,1385],[423,10013,842,254,10021],[1386,380,423,941,10001],[10001,414,842,480,10003],[10021,941,1338,842,10013],[10013,423,254,414],[10002,10003,941,423,414]]),
([mw0,mw7,mw14,mw45,mw85],[[579,842,1387,941,480,10003],[941,254,1388,1120,777,10007],[561,842,1389,579,422,10009],[],[480,579,10003,842,254,1390],[10003,1120,1354,941,943],[10012,481,842,1377],[10007,941,579,842,238],[10013,1391,579,414],[1392,285,842,1377]]),
([mw0,mw7,mw14,mw45,mw46,mw64],[[1354,941],[1354,1083],[254,1083],[1377,941],[414,941],[1393,254],[1374,1354],[518,1354],[],[941,1354],[1394,1354],[1395,1354],[1374,941],[1395,941],[1395,1083]]),
([mw0,mw7,mw21,mw45,mw38],[[1120,1354,1387,20242,30000],[],[561,254,1389,1083,777,10005],[1396,1397,1120,777,10007],[20242,624,1390],[561,1120,10005,1354,254,1398],[1396,1083,10007,1354,1377],[543,943,1354,1120,10005],[266,1329,1354,1083,10007],[10005,10007,1120,1083,1377]]),
([mw0,mw7,mw14,mw53,mw45,mw38],[[842,941],[941,1120],[10008,941],[842,10008],[1377,941],[1395],[],[1120,941],[1399,842],[],[941,842],[1395,1399],[518,842],[518,1377],[394,842]]),
([mw51,mw7,mw35,mw26,mw27],[[1120,842,552,480,1400],[113,20179,1401],[1386,842,380,1083,20084,10004],[10004,20179,20243,10006],[552,842,1402],[552,1403],[552,842,1404],[113,20179,380],[113,20179,1403],[113]]),
([mw59,mw7,mw14,mw26,mw64],[[1120,842,552,20244,1375],[20244,254,1405,1120,10004],[20244,380,10004],[20244,10004,1375],[552,842,1404],[552,325],[],[1404,1406],[20244,325],[20244,325]]),
([mw0,mw7,mw14,mw109,mw64],[[1120,842,552,20143,10001],[20143,10001,10004],[20143,842,10001,10004],[20143,10004,10001],[552,842,1404],[552,325],[],[1404,1406],[20143,325],[20143,325]]),
([mw59,mw7,mw14,mw26,mw36],[[1407],[1408,238,1120,1355],[1008,842,380,1123],[1123],[480,777,842,20245,10012],[1008,1120,380,10012,20246],[10012,967,842,20180,480],[1355,1343],[1123],[1123]]),
([mw0,mw7,mw17,mw97,mw27],[[1409,1369],[],[1409,1372],[1409,20247,10007],[1369],[1324],[480,20247,10007,254],[1369],[20247,254,10007],[20247,10007,254]]),
([mw0,mw7,mw6,mw110,mw27],[[1409,1370],[1409,1326],[],[1409,20209,309],[1325],[1370],[480,20209,414,254],[1370],[20209,254,414],[20209,1094,309]]),
([mw0,mw111,mw54,mw26,mw27],[[1120,842,669,20075,480],[],[1308,842,380,1410],[506,1120,1411],[20075,624,480],[20075,1120,480,1412],[20075,480,701],[1308,20075,1410],[20075,1410],[217]]),
([mw4,mw22,mw6,mw35,mw46,mw27],[[1413,1414],[1414],[238,941],[842,941],[254,20008],[1074,1414],[238,512],[842,512],[1415,941],[238,1003],[842,1003],[941,512],[1416,1414],[1414],[1414]]),
([mw4,mw8,mw15,mw45,mw27],[[760,842,1244,480,1417],[1418,624,561,423,10001],[561,842,1419,1244,480,10002],[1420,254,561,423,1421],[818,423,10001,842,512,10003],[561,10002,818,1003,10013],[480,423,10003,842,1418,1150],[285,1392,423,842,10001],[10001,1418,1422,254,10007],[480,10007,842,1418,10017]]),
([mw0,mw7,mw62,mw35,mw45,mw38],[[842,941],[941,1120],[423,941],[842,423],[1060,941],[1383,842],[552,842],[1120,941],[552,842],[1383,552],[941,842],[1383,423],[518,842],[423,1060],[394,842]]),
([mw0,mw7,mw62,mw45,mw38,mw44],[[842,977],[238,977],[842,977],[977,1120],[818,1120],[1413,842],[1120,1423],[1423,842],[552,842],[1413,842],[1413,238],[1413,977],[479,842],[552,842],[977,1424]]),
([mw0,mw1,mw35,mw46,mw38,mw61],[[1120,10002],[238,1120],[842,1244],[387,1120],[],[10002,1244],[1120,1244],[10002,943],[552,10002],[1425],[1425],[552,238],[1425],[552,1120],[552,1244]]),
([mw0,mw112,mw35,mw43,mw27],[[552,20248,10001],[20248,1426,10001,1120,10000],[20248,842,10001],[20248,10001,10006],[552,1427],[],[552,1428],[20248,1428],[266,1413],[20248,1428]]),
([mw0,mw112,mw35,mw41,mw27],[[941,512,20249,480,10002],[1429,941,1410],[],[1429,1350],[20249,1430,10002,512],[20249,520,512],[20249,10002,10014],[20249,1350],[480,1431],[20249,1350]]),
([mw0,mw1,mw97,mw38,mw61],[[1120,943,1432,20250,10002],[1432,1410],[1432,1120,1411],[],[20250,1120,10002,943,10010],[20250,10002,10010],[20250,10010,10002],[159,1425],[20250,1410],[20250,1410]]),
([mw0,mw112,mw35,mw46,mw47],[[552,20083,10001],[20083,1426,10001,1120,10000],[20083,10001,10000],[20083,10000,10001],[552,1427],[552,1427],[552,1374],[1374],[20083,24,1426,1108],[20083,24,749]]),
([mw0,mw112,mw35,mw46,mw36],[[1120,512,20040,1261,10002],[1261,1120,1411],[1261,1366],[],[20040,1008,10002,512],[20040,10002,512],[20040,967,10002],[1411,1433],[20040,1366],[20040,1366]]),
([mw0,mw1,mw35,mw46,mw113],[[1120,1261,20251,10002],[1261,1120,1411],[1261,1366],[],[20251,1008,10002,943,10010],[20251,1120,10002,943,10010],[20251,10010,10002],[1411,1433],[20251,1366],[20251,1366]]),
([mw0,mw112,mw8,mw53,mw43,mw27],[[552,423],[423,941],[708,423],[842,423],[943,579],[552,943],[],[],[552,423],[],[],[423,941],[266,708],[266,423],[493,423]]),
([mw0,mw1,mw8,mw54,mw41,mw102],[[943,480],[1260,480],[],[],[943,1434],[1260,943],[1422,943],[953,943],[480,608],[],[],[480,943],[1435,1422],[1435,943],[434,943]]),
([mw0,mw112,mw8,mw54,mw41,mw27],[[1436,480],[1260,480],[],[],[943,1434],[1260,943],[579,480],[953,480],[480,608],[],[],[480,943],[1435,579],[1435,943],[434,943]]),
([mw0,mw1,mw2,mw73,mw39,mw44],[[1437,1125],[1437,480],[],[],[1437,1438],[1439,699],[],[],[480,699],[953,480],[1244,480],[480,1354],[1125],[244,1125],[1125]]),
([mw0,mw1,mw12,mw74,mw39,mw38],[[1440,480],[],[238,777],[],[1441,480],[],[1440,818],[],[1440,818],[380,777],[239,1354],[244,480],[943,238],[480,238],[239,480]]),
([mw0,mw7,mw114,mw115,mw38],[[1120,1354,552,10002],[941,1354,238,1120,20075,10004],[1386,943,380,10004,20084],[10004,1060,1120,20180,10038],[552,1244,1404],[552,1354,1383],[552,1354,518],[1386,941,1404,1354,1120,238],[20075,20180,285,238],[20084,1386,285,1120,1060]]),
([mw0,mw1,mw116,mw117,mw61],[[579,943,1306,20084,10002],[1306,1244,1442],[1306,579,1350],[],[20084,579,10002,943,10010],[20084,10002,10010],[20084,10010,10002],[1442,1350,579,1244,238],[20084,1392,579,1442],[20084,1392,1350]]),
([mw0,mw7,mw21,mw109,mw118],[[1120,1354,123,20075,10002],[],[123,1410],[123,1120,1411],[20075,624,10002],[20075,1120,10002,1354,708],[20075,10002,708],[1410],[20075,1410],[1392,1008,1120,1443]])]
noncomputable def mtopD4 : List StD := [
([mw12,mw21,mw45,mw38],[[762,624,1120,941,1244],[1444,1392,1244,941],[836,138,1120,480,1421],[1445,1392,238,1120],[1416,1329,941,480,238],[1392,1446,1120,1447,953]])]
def mtopD3 : List StD := []
theorem mtopI3 : LevelN false mtopT 3 mtopD3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC4x0 : levelOK false mtopT mtopt 3 (mtopD3.map Prod.fst) ((mtopD4.drop (0*16)).take 16) = true := by decide +kernel
theorem mtopI4 : LevelN false mtopT 4 mtopD4 := levelStep mtopB mtopW mtopI3 (chunks 16 mtopD4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC5x0 : levelOK false mtopT mtopt 4 (mtopD4.map Prod.fst) ((mtopD5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC5x1 : levelOK false mtopT mtopt 4 (mtopD4.map Prod.fst) ((mtopD5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC5x2 : levelOK false mtopT mtopt 4 (mtopD4.map Prod.fst) ((mtopD5.drop (2*16)).take 16) = true := by decide +kernel
theorem mtopI5 : LevelN false mtopT 5 mtopD5 := levelStep mtopB mtopW mtopI4 (chunks 16 mtopD5 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC5x0
  · exact mtopC5x1
  · exact mtopC5x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x0 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x1 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x2 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x3 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x4 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x5 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC6x6 : levelOK false mtopT mtopt 5 (mtopD5.map Prod.fst) ((mtopD6.drop (6*16)).take 16) = true := by decide +kernel
theorem mtopI6 : LevelN false mtopT 6 mtopD6 := levelStep mtopB mtopW mtopI5 (chunks 16 mtopD6 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC6x0
  · exact mtopC6x1
  · exact mtopC6x2
  · exact mtopC6x3
  · exact mtopC6x4
  · exact mtopC6x5
  · exact mtopC6x6
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x0 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x1 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x2 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x3 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x4 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x5 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x6 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x7 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC7x8 : levelOK false mtopT mtopt 6 (mtopD6.map Prod.fst) ((mtopD7.drop (8*16)).take 16) = true := by decide +kernel
theorem mtopI7 : LevelN false mtopT 7 mtopD7 := levelStep mtopB mtopW mtopI6 (chunks 16 mtopD7 9 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC7x0
  · exact mtopC7x1
  · exact mtopC7x2
  · exact mtopC7x3
  · exact mtopC7x4
  · exact mtopC7x5
  · exact mtopC7x6
  · exact mtopC7x7
  · exact mtopC7x8
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC8x0 : levelOK false mtopT mtopt 7 (mtopD7.map Prod.fst) ((mtopD8.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC8x1 : levelOK false mtopT mtopt 7 (mtopD7.map Prod.fst) ((mtopD8.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC8x2 : levelOK false mtopT mtopt 7 (mtopD7.map Prod.fst) ((mtopD8.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC8x3 : levelOK false mtopT mtopt 7 (mtopD7.map Prod.fst) ((mtopD8.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC8x4 : levelOK false mtopT mtopt 7 (mtopD7.map Prod.fst) ((mtopD8.drop (4*16)).take 16) = true := by decide +kernel
theorem mtopI8 : LevelN false mtopT 8 mtopD8 := levelStep mtopB mtopW mtopI7 (chunks 16 mtopD8 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC8x0
  · exact mtopC8x1
  · exact mtopC8x2
  · exact mtopC8x3
  · exact mtopC8x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC9x0 : levelOK false mtopT mtopt 8 (mtopD8.map Prod.fst) ((mtopD9.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC9x1 : levelOK false mtopT mtopt 8 (mtopD8.map Prod.fst) ((mtopD9.drop (1*16)).take 16) = true := by decide +kernel
theorem mtopI9 : LevelN false mtopT 9 mtopD9 := levelStep mtopB mtopW mtopI8 (chunks 16 mtopD9 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC9x0
  · exact mtopC9x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC10x0 : levelOK false mtopT mtopt 9 (mtopD9.map Prod.fst) ((mtopD10.drop (0*16)).take 16) = true := by decide +kernel
theorem mtopI10 : LevelN false mtopT 10 mtopD10 := levelStep mtopB mtopW mtopI9 (chunks 16 mtopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC10x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC11x0 : levelOK false mtopT mtopt 10 (mtopD10.map Prod.fst) ((mtopD11.drop (0*16)).take 16) = true := by decide +kernel
theorem mtopI11 : LevelN false mtopT 11 mtopD11 := levelStep mtopB mtopW mtopI10 (chunks 16 mtopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC11x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem mtopC12x0 : levelOK false mtopT mtopt 11 (mtopD11.map Prod.fst) ((mtopD12.drop (0*16)).take 16) = true := by decide +kernel
theorem mtopI12 : LevelN false mtopT 12 mtopD12 := levelStep mtopB mtopW mtopI11 (chunks 16 mtopD12 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact mtopC12x0
  ))
theorem mtopL : LowN false mtopR mtopT 13 := lowSearch mtopB mtopI12 (by decide +kernel)

def target : (Fin 6 → Bool) → Bool := (fun x : Fin 6 → Bool => decide (2 ≤ ((List.ofFn x).count true)))
def theInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W stopT
theorem sameT : mtopT = stopT := rfl
theorem graph_proper : proper graph := (baseOK_ok stopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 6 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by unfold target; decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physical (u : Bool) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : u=false → ∀ g ∈ C.gates, isNot g=false)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u graph k theInputs.toFinset := by
  have b := baseOK_ok stopB
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=u) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W stopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=u) C.gates theInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes {u : Bool} {L : Nat} (low : LowN u [0,1,2,3,4,5] stopT L) : ∀ k, k < L → ¬Live u graph k theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := low q bank built hit
  omega
theorem tooSmall (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target 12) : False := by
  classical
  obtain ⟨C,legal,hs,correct⟩ := h
  have hs' : C.gates.length ≤ 12 := hs
  by_cases mono : ∀ g ∈ C.gates, isNot g = false
  · obtain ⟨k,hk,run⟩ := physical false C legal (fun _ => mono) correct
    have le := List.countP_le_length (p := fun g => !isNot g) (l := C.gates)
    exact excludes (u:=false) (L:=13) mtopL k (by omega) run
  · push Not at mono
    obtain ⟨g,hg,hop⟩ := mono
    have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
      rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
        simp [hop] at eq
    obtain ⟨k,hk,run⟩ := physical true C legal (by simp) correct
    exact excludes (u:=true) (L:=12) stopL k (by omega) run

open PEqualNP.MetaComplexity

def tableFunction (x : Fin 6 → Bool) : Bool :=
  (18446744069414518504 : ℕ).testBit (tableIndex x)

def tableWitness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩,
    ⟨.and, [6, 2]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [7, 8]⟩,
    ⟨.or, [3, 4]⟩, ⟨.and, [3, 4]⟩,
    ⟨.and, [11, 5]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [12, 13]⟩,
    ⟨.and, [9, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

set_option maxHeartbeats 0 in
theorem tableAgreement : ∀ x : Fin 6 → Bool, tableFunction x = target x := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem upper : HasCircuitSize 6 tableFunction 13 := by
  refine ⟨tableWitness, by simp [FanInTwo, tableWitness], by decide, ?_⟩
  decide +kernel

theorem lower (t : ℕ) (h : HasCircuitSize 6 tableFunction t) : 13 ≤ t := by
  by_contra! small
  obtain ⟨C, legal, size, eval⟩ := h
  apply tooSmall
  refine ⟨C, legal, by omega, ?_⟩
  intro x
  exact (eval x).trans (tableAgreement x)

end PEqualNP.Outside.V_meta_9980__k13

theorem PEqualNP.Outside.V_meta_9980__k13 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446744069414518504 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 13 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446744069414518504 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 13 ≤ t) :=
  ⟨PEqualNP.Outside.V_meta_9980__k13.upper, PEqualNP.Outside.V_meta_9980__k13.lower⟩
