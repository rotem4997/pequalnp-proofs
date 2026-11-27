import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9825
namespace Engine
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
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
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
theorem extract {u target} (gs : List Gate) (w : List Sig)
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
abbrev Row := Fin 1024
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
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0c0fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff0c0fffffffffffffffffffffffffffaf0f0ffffffffffffffffffffffffffeaf0c0fffffffffffefcfcfffffffffffaf0f0ffeefeeeffeefcccffeafaeaffeaf0c0
def sample (r : Row) (j : Fin 10) := bit r (inputs.getD j.val zero)
def edge (x : Fin 10 → Bool) : Bool :=
  (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 10 => inputs.getD j.val zero) = inputs := rfl
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
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 1024-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(1024-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 1024 (1024-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 1024-d.val <;> simp [shifted,h,r.isLt]
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
  (List.range 10).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def varsX (m : Nat) := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 7 &&& x 9) ||| (x 6 &&& x 9) ||| (x 6 &&& x 8) ||| (x 5 &&& x 8)
def subcube (z o : Nat) : Sig :=
  if z &&& o != 0 then zero else
    (List.range 10).foldl (fun w i => if z.testBit i then w &&& ~~~(inputs.getD i zero)
      else if o.testBit i then w &&& inputs.getD i zero else w) one
def fixRows (z o : Nat) : List Move :=
  (List.range 10).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 1024 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 1024 d)
def supportPairs (_t mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 1024 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 1024 r,Fin.ofNat 1024 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 1024+1024*(c.1/1024)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 1024) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/1024+80) s
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
  let free := colFree raw (z % 1024) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/1024+80) s
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
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2
def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True
theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩
theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)
theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he
abbrev Bits := BitVec 320
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 320 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 320 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 320 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 320 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 320) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 10 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem coordinate9 : ∀ r : Row, bit r (inputs.getD 9 zero) = r.val.testBit 9 := by decide +kernel
theorem input_coords : ∀ (j : Fin 10) (r : Row), bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j
  fin_cases j
  · exact coordinate0
  · exact coordinate1
  · exact coordinate2
  · exact coordinate3
  · exact coordinate4
  · exact coordinate5
  · exact coordinate6
  · exact coordinate7
  · exact coordinate8
  · exact coordinate9
theorem asRow_bit (cols : Nat → Bits) (i : Fin 320) (j : Fin 10) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 10 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<10 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 7 &&& x 9) ||| (x 6 &&& x 9) ||| (x 6 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 320) (j : Fin 10) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<10) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide),pos 9 (by decide)]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0
def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)
theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 320 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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
theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto
theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<10
  · let i : Fin 10 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 1024 ≤ 2^j := by
      change 2^10 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 12)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 320) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def forestRecord (tab : Packing) (_raw i : Nat) :=
  let (_,_,_,_,_,_,_,words) := tab
  words (2*i)
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 12*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 2,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)
def decodeHints (cw d : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,x => (x % (1 <<< cw),(x >>> cw) % (1 <<< d)) ::
      decodeHints cw d n (x >>> (cw+d))
def forestHints (tab : Packing) (_raw i : Nat) :=
  let (_,depth,cw,_,_,_,_,words) := tab
  let data := words (2*i+1)
  decodeHints cw depth (data % 256) (data >>> 8)
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 320) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^321*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^321 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 320) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (321*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^321)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 321*(i+1)-321=321*i := by omega
      have ge : ¬321*(i+1)<321 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 320 = (a==BitVec.allOnes 320) := by
  by_cases h : a=BitVec.allOnes 320
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^320-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^320 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (321*i) =
      (f xs[i]==BitVec.allOnes 320) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^321*u+x+(2^321*v+1)=2^321*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^321 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬321*(i+1)+320<321 := by omega
      have di : 321*(i+1)+320-321=321*i+320 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]
def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 321) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (321*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
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
      apply ih (mask:=mask >>> 321) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
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
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
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
theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
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
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega
theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 10)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem swap_table : ∀ v : Fin 160, validSwap v.val=true → ∀ t : Fin 10, swapIdx v.val t.val<10 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<10) : swapIdx v t<10 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<160 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<10) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 10) &&& 3) (ws.getD (bits &&& 31) 0) (ws.getD ((bits >>> 5) &&& 31) 0))
      fun z => decodeN n (bits >>> 12) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 12*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs
theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 320 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 320
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js
theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)
theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩
def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
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
theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
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
    exact ⟨kwFork d01 ha hb fresh H⟩
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw
theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
def kwWord (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let a := ws.getD (value % 16) zero
  let b := ws.getD ((value >>> 4) % 16) zero
  let row := fun i : Nat => Fin.ofNat 1024 ((value >>> (8+10*i)) % 1024)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a (row 0) (row 2) && kwWireB ws T b (row 0) (row 3) &&
    kwWireB ws T a (row 4) (row 1) && kwWireB ws T b (row 5) (row 1)
theorem kwWord_sound {T ws k v} (h : kwWord T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all fun j => kwWord (targetOf g) (stateSet g k (a+j)) k (data j)
theorem mixedCut {g k a n data} (mode : g.mode=false) (h : kwTest g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh
def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1
theorem mixedLower {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
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
def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
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
def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
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
def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
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
theorem supportSide {A B U : Finset Sig} {a b z : Sig}
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
def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩
def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
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
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
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
theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))
theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def colorPoint (v : Fin 10 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn v)).toFin.cast (by simp [List.length_ofFn])
theorem color_bit (v : Fin 10 → Bool) (i : Fin 10) :
    bit (colorPoint v) (inputs.getD i.val zero) = v i := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def colorField (d j : Nat) : Fin 10 := Fin.ofNat 10 ((d >>> (1+4*j)) % 16)
def colorRow (d j : Nat) : Row := Fin.ofNat 1024 ((d >>> (13+10*j)) % 1024)
def colorWire (ws : List Sig) (names : Nat) (j : Fin 10) : Sig :=
  ws.getD ((names >>> (4*j.val)) % 16) zero
def colorRule (ws : List Sig) (T : Sig) (names d : Nat) : Bool :=
  let a := colorWire ws names (colorField d 0)
  let b := colorWire ws names (colorField d 1)
  let c := colorWire ws names (colorField d 2)
  let r := colorRow d
  if d.testBit 0 then
    (decide (a ∈ ws) && decide (b ∈ ws) && decide (a ≠ b)) &&
    (kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 0) (r 3) &&
      kwWireB ws T a (r 4) (r 1) && kwWireB ws T b (r 5) (r 1))
  else kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 3) (r 1) &&
    kwWireB ws T c (r 0) (r 1)
def constraintWord (d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  if d.testBit 0 then x 0 ^^^ x 1 else ~~~(x 0 &&& x 1) ||| x 2
def colorTruth {ws : List Sig} {T : Sig} (F : SingleFactor ws.toFinset T)
    (names : Nat) (i : Fin 10) := decide (colorWire ws names i ∈ F.inner)
theorem parity_bit {A B : Prop} [Decidable A] [Decidable B]
    (h : ¬ ((A ∧ B) ∨ (¬A ∧ ¬B))) : (decide A ^^ decide B) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem horn_bit {A B C : Prop} [Decidable A] [Decidable B] [Decidable C]
    (h : A → B → C) : (!(decide A && decide B) || decide C) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem bit_xor (r : Row) (a b : Sig) : bit r (a ^^^ b) = (bit r a ^^ bit r b) :=
  BitVec.getLsbD_xor
theorem rule_valid {ws T names d} (F : SingleFactor ws.toFinset T)
    (h : colorRule ws T names d = true) :
    bit (colorPoint (colorTruth F names)) (constraintWord d) = true := by
  have bits (i) := color_bit (colorTruth F names) (colorField d i)
  by_cases flag : d.testBit 0 = true
  · simp only [colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h
    have rule := parityRule F (List.mem_toFinset.mpr h.1.1.1) (List.mem_toFinset.mpr h.1.1.2) h.1.2
      (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2) (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
    simp only [constraintWord,flag,ite_true]
    rw [bit_xor,bits,bits]
    exact parity_bit rule
  · simp only [colorRule,if_neg flag,Bool.and_eq_true] at h
    have rule := hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
    simp only [constraintWord,if_neg flag]
    change bit _ (prime true (neg (prime false _ _)) _) = true
    rw [bit_prime,bit_neg,bit_prime]
    change (!(bit _ _ && bit _ _) || bit _ _) = true
    rw [bits,bits,bits]
    exact horn_bit rule
def colorSet : List Nat → Sig
  | [] => one
  | d::ds => constraintWord d &&& colorSet ds
theorem color_set {ws T names} (F : SingleFactor ws.toFinset T) (ds : List Nat)
    (h : ds.all (colorRule ws T names) = true) :
    bit (colorPoint (colorTruth F names)) (colorSet ds) = true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    change bit _ (prime false _ _) = true
    rw [bit_prime,rule_valid F h.1,ih h.2]
    rfl
def colorCheck (ws : List Sig) (T : Sig) (k names : Nat) (ds : List Nat) :=
  decide (k ≤ ws.toFinset.card) && ds.all (colorRule ws T names) && (colorSet ds == zero)
theorem color_sound {ws T k names ds} (h : colorCheck ws T k names ds=true) :
    Impossible false T k ws.toFinset := by
  simp only [colorCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  intro n le run
  obtain ⟨F⟩ := oneShare run (le.trans h.1.1)
  have ok := color_set F ds h.1.2
  rw [h.2,bit_zero] at ok
  contradiction
def colorRange (g : Forest) (k a n : Nat) (ds : Nat → Nat × List Nat) :=
  (List.range n).all fun i =>
    colorCheck (stateSet g k (a+i)) (targetOf g) k (ds i).1 (ds i).2
theorem colorCut {g k a n ds} (mode : g.mode=false)
    (h : colorRange g k a n ds=true) : CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change colorCheck (stateSet g k (a+(j-a))) _ _ _ _=true at hh
  rw [eq] at hh
  exact color_sound hh
def neighbor670 (i : Fin 10) : Nat := [4, 2, 1, 2, 0, 0, 1, 2, 5, 4].getD i.val 0
def absentRow670 (i : Fin 10) : Row := Fin.ofNat 1024 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< i.val) ||| (1 <<< neighbor670 i))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem requiredInputs :
    (∀ i : Fin 10, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 10, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel
theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (small : C.size ≤ 16) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 15 else 16) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 16 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 15 else 16) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩
theorem directSplit
    (m : ∀ k, k ≤ 16 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 15 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 16 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def orderLaw (S : Finset Sig) (T : Sig) (f : Sig → Nat) :=
  (∀ {a b p n na nb pa pb}, a ≠ b →
    onlyWire S T a p na → onlyWire S T b p nb →
    onlyWire S T a pa n → onlyWire S T b pb n → f a ≠ f b) ∧
  (∀ {a b c p n na pb}, onlyWire S T a p na → onlyWire S T b pb n →
    onlyWire S T c p n → f a = f b → f c ≤ f a)
theorem only_value {k S T v p n} (run : Live false T k S) (h : onlyWire S T v p n) :
    v∈S ∧ bit p v=true ∧ bit n v=false := by
  obtain ⟨w,hw,hp,hn⟩ := mono_row_difference run rfl h.1 h.2.1
  exact h.2.2 w hw hp hn ▸ ⟨hw,hp,hn⟩
def gateList (a b : Sig) (U : Finset Sig) := [a,b].filter fun t => decide (t∈U)
def gateMap (a b z v : Sig) := if v=a ∨ v=b then z else v
def gateColor (a b z : Sig) (U : Finset Sig) (f : Sig → Nat) (v : Sig) :=
  let kept := gateList a b U
  if v∈kept then kept.idxOf v else kept.length+f (gateMap a b z v)
theorem gate_kept {a b v U} :
    v∈gateList a b U ↔ (v=a ∨ v=b) ∧ v∈U := by simp [gateList]
theorem gate_mem {a b z v : Sig} {U : Finset Sig} (h : v∈insert a (insert b U)) :
    gateMap a b z v ∈ insert z U := by
  by_cases eq : v=a ∨ v=b
  · simp [gateMap,eq]
  · simp_all [gateMap]
theorem mono_bin_bit {d} (hd : allowed false d) (a b : Sig) (r : Row) :
    bit r (bin d a b) = if d=0 then bit r a && bit r b else bit r a || bit r b := by
  rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
  · simp [bit,bin]
  · simp [bit,bin]
  · contradiction
  · contradiction
theorem gate_only {a b d U T v p n} (hd : allowed false d)
    (unused : v∉gateList a b U) (h : onlyWire (insert a (insert b U)) T v p n) :
    onlyWire (insert (bin d a b) U) T (gateMap a b (bin d a b) v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro w hw hp hn
  rcases Finset.mem_insert.mp hw with rfl | hw
  · rw [mono_bin_bit hd] at hp hn
    have sep : (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
      by_cases op : d=0 <;> cases u : bit p a <;> cases v : bit n a <;> cases x : bit p b <;>
        cases y : bit n b <;> simp_all
    have eq : v=a ∨ v=b := by
      rcases sep with ⟨x,y⟩ | ⟨x,y⟩
      · exact Or.inl (h.2.2 a (by simp) x y).symm
      · exact Or.inr (h.2.2 b (by simp) x y).symm
    simp [gateMap,eq]
  · obtain rfl := h.2.2 w (by simp [hw]) hp hn
    have ne : ¬(w=a ∨ w=b) := fun eq => unused (gate_kept.mpr ⟨eq,hw⟩)
    simp [gateMap,ne]
theorem gate_share_eq {a b z U f v w} (hv : v∈gateList a b U)
    (eq : gateColor a b z U f v = gateColor a b z U f w) : v=w := by
  have bound := List.idxOf_lt_length_of_mem hv
  by_cases hw : w∈gateList a b U
  · simp only [gateColor,if_pos hv,if_pos hw] at eq
    exact (List.idxOf_inj hv).mp eq
  · simp only [gateColor,if_pos hv,if_neg hw] at eq
    omega
theorem gate_cross {a b d U T k p n na nb pa pb} (hd : allowed false d) (hab : a≠b)
    (run : Live false T k (insert (bin d a b) U)) (prev : Live false T (k+1) (insert a (insert b U)))
    (ua : a∉gateList a b U)
    (A : onlyWire (insert a (insert b U)) T a p na) (B : onlyWire (insert a (insert b U)) T b p nb)
    (C : onlyWire (insert a (insert b U)) T a pa n) (D : onlyWire (insert a (insert b U)) T b pb n) : False := by
  have Zp := (only_value run (gate_only hd ua C)).2.1
  have Zn := (only_value run (gate_only hd ua A)).2.2
  simp only [gateMap,true_or,ite_true,mono_bin_bit hd] at Zp Zn
  by_cases op : d=0
  · simp [op] at Zp
    exact hab (C.2.2 b (by simp) Zp.2 (only_value prev D).2.2).symm
  · simp [op] at Zn
    exact hab (A.2.2 b (by simp) (only_value prev B).2.1 Zn.2).symm
theorem order_live {k S T} (h : Live false T k S) :
    ∃ (count : Nat) (f : Sig → Nat), count+S.card ≤ k+2 ∧ (∀ v∈S, f v<count) ∧ orderLaw S T f := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,properT⟩ := h
    refine ⟨1,fun _ => 0,by simp,by simp,?_,by simp⟩
    intro a b p n na nb pa pb ne A B C D
    have e := (only_value (Live.stop (u:=false) properT) A).1
    have j := (only_value (Live.stop (u:=false) properT) B).1
    simp only [Finset.mem_singleton] at e j
    exact (ne (e.trans j.symm)).elim
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,fresh,tail⟩ := h
    let z := bin d a b
    let kept := gateList a b U
    have prev := Live.binary hd ha hb hab fresh tail
    obtain ⟨count,f,mass,bound,law⟩ := ih tail
    have hzu : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem hzu] at mass
    have size : kept.length + (insert a (insert b U)).card = U.card+2 := by
      by_cases x : a∈U <;> by_cases y : b∈U <;>
        simp [kept,gateList,x,y,hab,Finset.card_insert_of_notMem] <;> omega
    refine ⟨kept.length+count,gateColor a b z U f,by omega,?_,?_,?_⟩
    · intro v hv
      by_cases u : v∈kept
      · have m := List.idxOf_lt_length_of_mem u
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_pos u]
        omega
      · have m := bound _ (gate_mem (z:=z) hv)
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_neg u]
        exact Nat.add_lt_add_left m _
    · intro v w p n na nb pa pb vw A B C D eq
      have uv : v∉kept := fun u => vw (gate_share_eq u eq)
      have uw : w∉kept := fun u => vw (gate_share_eq u eq.symm).symm
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      by_cases ne : gateMap a b z v ≠ gateMap a b z w
      · exact law.1 ne (gate_only hd uv A) (gate_only hd uw B)
          (gate_only hd uv C) (gate_only hd uw D) same
      · have vS := (only_value prev A).1
        have wS := (only_value prev B).1
        have vz : v≠z := fun e => fresh (show z∈_ from e ▸ vS)
        have wz : w≠z := fun e => fresh (show z∈_ from e ▸ wS)
        have pair : (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
          by_cases va : v=a ∨ v=b <;> by_cases wa : w=a ∨ w=b <;> simp_all [gateMap] <;> grind
        rcases pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact gate_cross hd hab tail prev uv A B C D
        · exact gate_cross hd hab tail prev uw B A D C
    · intro v w t p n na pb A B C eq
      have ident (e : v=w) : t=v := by
        subst w
        exact (C.2.2 v (only_value prev A).1 (only_value prev A).2.1 (only_value prev B).2.2).symm
      by_cases uv : v∈kept
      · rw [ident (gate_share_eq uv eq)]
      by_cases uw : w∈kept
      · rw [ident (gate_share_eq uw eq.symm).symm]
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      change (if t∈kept then kept.idxOf t else kept.length+_) ≤ (if v∈kept then _ else kept.length+_)
      rw [if_neg uv]
      by_cases ut : t∈kept
      · rw [if_pos ut]
        have lim := List.idxOf_lt_length_of_mem ut
        omega
      · rw [if_neg ut]
        exact Nat.add_le_add_left (law.2 (gate_only hd uv A) (gate_only hd uw B) (gate_only hd ut C) same) _
def rankRule (d : Nat) (f : Fin 10 → Nat) : Prop :=
  let v := fun j => f (colorField d j)
  if d.testBit 0 then v 0 ≠ v 1 else v 0=v 1 → v 2≤v 0
theorem rank_rule {ws T names d f} (h : colorRule ws T names d=true)
    (law : orderLaw ws.toFinset T f) :
    rankRule d (fun i => f (colorWire ws names i)) := by
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    exact law.1 h.1.2 (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2)
      (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
  · simp only [rankRule,colorRule,if_neg flag,Bool.and_eq_true] at h ⊢
    exact law.2 (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def layerCovers (lo : Nat) (f : Fin 10 → Nat) (t : Nat) :=
  ∀ i, f i<t → lo.testBit i.val=true
def layerBits (lo : Nat) (f : Fin 10 → Nat) (t : Nat) (i : Fin 10) :=
  !lo.testBit i.val && decide (f i=t)
def layerRule (lo d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  let pair := neg (prime false (x 0) (x 1))
  if d.testBit 0 then pair else
    if lo.testBit (colorField d 2).val then one else prime true pair (x 2)
theorem layer_rule {lo d f t} (h : rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerRule lo d)=true := by
  have eval (j) := color_bit (layerBits lo f t) (colorField d j)
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,flag,ite_true] at h
    simp only [layerRule,flag,ite_true,bit_neg,bit_prime,Bool.false_eq_true,ite_false,eval]
    cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
    simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
    exact h (x.2.trans y.2.symm)
  · simp only [rankRule,if_neg flag] at h
    simp only [layerRule,if_neg flag]
    by_cases old : lo.testBit (colorField d 2).val=true
    · rw [if_pos old,bit_one]
    · rw [if_neg old]
      simp only [bit_prime,ite_true,bit_neg,Bool.false_eq_true,ite_false,eval]
      cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
      simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
      have le := h (x.2.trans y.2.symm)
      have ge : ¬ f (colorField d 2)<t := by
        intro lt
        have hit := cov _ lt
        simp [old] at hit
      simp [layerBits,old,show f (colorField d 2)=t by omega]
def layerWords (lo : Nat) : List Nat → Sig
  | [] => one
  | d::ds => prime false (layerRule lo d) (layerWords lo ds)
theorem layer_words {lo f t} (ds : List Nat) (h : ∀d∈ds, rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerWords lo ds)=true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    rw [layerWords,bit_prime,layer_rule (h d (by simp)) cov,ih (fun e he => h e (by simp [he]))]
    rfl
def cubeParts (mask : Nat) : List (Fin 10) → Sig
  | [] => one
  | i::is => if mask.testBit i.val then cubeParts mask is else
      prime false (neg (inputs.getD i.val zero)) (cubeParts mask is)
theorem cube_parts {x : Fin 10 → Bool} (mask : Nat) (is : List (Fin 10))
    (h : bit (colorPoint x) (cubeParts mask is)=true) :
    ∀ i∈is, x i=true → mask.testBit i.val=true := by
  induction is with
  | nil => simp
  | cons j js ih =>
    by_cases hm : mask.testBit j.val=true
    · rw [cubeParts,if_pos hm] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hm
      · exact ih h i hi hx
    · rw [cubeParts,if_neg hm,bit_prime,bit_neg,color_bit] at h
      simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.not_eq_true'] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · simp_all
      · exact ih h.2 i hi hx
def cubeWord (mask : Nat) := cubeParts mask (List.finRange 10)
def layerUpper (lo : Nat) : List Nat → Sig
  | [] => zero
  | a::as => if lo &&& a = lo then prime true (cubeWord a) (layerUpper lo as) else layerUpper lo as
theorem upper_choice {lo f t} (as : List Nat) (cov : layerCovers lo f t)
    (ok : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) :
    ∃ a∈as, layerCovers a f (t+1) := by
  induction as with
  | nil => rw [layerUpper,bit_zero] at ok; contradiction
  | cons a as ih =>
    have follow (h : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) : ∃ v∈a::as, layerCovers v f (t+1) := by
      obtain ⟨v,hv,cv⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem _ hv,cv⟩
    by_cases sub : lo &&& a=lo
    · rw [layerUpper,if_pos sub,bit_prime] at ok
      rcases Bool.or_eq_true_iff.mp ok with hit | tail
      · refine ⟨a,by simp,?_⟩
        intro i hi
        by_cases old : lo.testBit i.val=true
        · have z := congrArg (fun v : Nat => v.testBit i.val) sub
          simpa only [Nat.testBit_and,old,Bool.true_and] using z
        · have ge : ¬ f i<t := fun lt => old (cov i lt)
          have yes : layerBits lo f t i=true := by simp [layerBits,old,show f i=t by omega]
          exact cube_parts a (List.finRange 10) hit i (by simp) yes
      · exact follow tail
    · rw [layerUpper,if_neg sub] at ok
      exact follow ok
def layerStep (ds : List Nat) (lo : Nat) (hi : List Nat) :=
  (prime false (layerWords lo ds) (neg (layerUpper lo hi)) == zero)
theorem layer_step {ds lo hi f t} (laws : ∀d∈ds,rankRule d f) (cov : layerCovers lo f t)
    (ok : layerStep ds lo hi=true) : ∃ a∈hi, layerCovers a f (t+1) := by
  have eq := beq_iff_eq.mp ok
  have chk := congrArg (bit (colorPoint (layerBits lo f t))) eq
  rw [bit_prime,bit_neg,bit_zero,layer_words ds laws cov] at chk
  apply upper_choice hi cov
  simpa using chk
def finalPair (lo d : Nat) := d.testBit 0 && !lo.testBit (colorField d 0).val && !lo.testBit (colorField d 1).val
def layerScan (ds lo : List Nat) : List (List Nat) → Bool
  | [] => lo.all fun a => ds.any (finalPair a)
  | hi::tail => (lo.all fun a => layerStep ds a hi) && layerScan ds hi tail
theorem layer_scan {ds f} (laws : ∀d∈ds,rankRule d f) (ls : List (List Nat))
    {lo t} (covered : ∃a∈lo,layerCovers a f t) (bound : ∀i, f i<t+ls.length+1)
    (ok : layerScan ds lo ls=true) : False := by
  induction ls generalizing lo t with
  | nil =>
    obtain ⟨a,ha,ca⟩ := covered
    obtain ⟨d,hd,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok a ha)
    simp only [finalPair,Bool.and_eq_true,Bool.not_eq_true'] at yes
    have top (i : Fin 10) (no : a.testBit i.val=false) : f i=t := by
      have small : f i<t+1 := by simpa using bound i
      have big : ¬ f i<t := by intro lt; have hh := ca i lt; simp [no] at hh
      omega
    have diff := laws d hd
    simp only [rankRule,yes.1.1,ite_true] at diff
    exact diff ((top _ yes.1.2).trans (top _ yes.2).symm)
  | cons l ls ih =>
    obtain ⟨a,ha,ca⟩ := covered
    have both := Bool.and_eq_true_iff.mp ok
    apply ih (t:=t+1) (layer_step laws ca (List.all_eq_true.mp both.1 a ha)) _ both.2
    intro i
    have z := bound i
    simp only [List.length_cons] at z
    omega
abbrev OrderPage := Nat × List Nat × Nat × List (List Nat)
def orderCheck (ws : List Sig) (T : Sig) (k : Nat) (book : OrderPage) :=
  let (names,ds,start,ls) := book
  decide (k+2 ≤ ws.toFinset.card+ls.length+1) &&
    (List.finRange 10).all (fun i => decide (colorWire ws names i ∈ ws)) &&
    ds.all (colorRule ws T names) && layerScan ds [start] ls
theorem order_sound {ws T k page} (ok : orderCheck ws T k page=true) : Impossible false T k ws.toFinset := by
  rcases page with ⟨names,ds,start,ls⟩
  simp only [orderCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  intro n le run
  obtain ⟨count,f,mass,bound,law⟩ := order_live run
  apply layer_scan (f:=fun i => f (colorWire ws names i)) (fun d hd => rank_rule (ok.1.2 d hd) law)
    ls (t:=0) (lo:=[start]) ⟨start,by simp,by simp [layerCovers]⟩ _ ok.2
  intro i
  have use := (ok.1.1.2 _ (List.mem_finRange i))
  have less := bound _ (List.mem_toFinset.mpr use)
  have size := ok.1.1.1
  omega
def orderRange (g : Forest) (k a n : Nat) (pages : Nat → OrderPage) :=
  (List.range n).all fun i => orderCheck (stateSet g k (a+i)) (targetOf g) k (pages i)
theorem orderCut {g k a n pages} (mode : g.mode=false) (ok : orderRange g k a n pages=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp ok (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change orderCheck (stateSet g k (a+(j-a))) _ _ _=true at hh
  rw [eq] at hh
  exact order_sound hh
def padColumn (n v : Nat) : Bits :=
  BitVec.ofNat 320 (v + if v % 2=1 then (1 <<< 320)-(1 <<< n) else 0)
theorem lowerHint {u raw T a b} (h : Lower u raw T a) (le : b ≤ a) : Lower u raw T b :=
  fun p bank hr hit => le.trans (h p bank hr hit)
def treeData (p n v : Nat) :=
  let row := fun base i => (base >>> (10*((v >>> (8+5*i)) % 32))) % 1024
  v % 256 + (row p 0 <<< 8) + (row n 1 <<< 18) + (row n 2 <<< 28) +
    (row n 3 <<< 38) + (row p 4 <<< 48) + (row p 5 <<< 58)
def ruleData (p n v : Nat) :=
  let row := fun base i => (base >>> (10*((v >>> (13+5*i)) % 32))) % 1024
  v % 8192 + (row p 0 <<< 13) + (row n 1 <<< 23) + (row n 2 <<< 33) +
    (row (if v.testBit 0 then n else p) 3 <<< 43) + (row p 4 <<< 53) + (row p 5 <<< 63)
theorem countFace {u m L} (hints : Nat)
    (hp : properB (graphGoal m)=true)
    (ess : checkEssential (graphGoal m) (varsX m) (graphPairs m hints)=true)
    (enough : L ≤ (List.map Prod.fst (graphPairs m hints)).toFinset.card - 1) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lower_count (proper_of _ hp) (graphPairs m hints) ess) enough
theorem dropFace {u m q a L} (fixed hints : Nat) (prior : Lower u (varsX q) (graphGoal q) a)
    (mapped : checkLift (fixRows fixed 0) (graphGoal m) (varsX m) (varsX q) (graphGoal q) (graphPairs fixed hints)=true)
    (hm : properB (graphGoal m)=true) (hq : properB (graphGoal q)=true)
    (enough : L ≤ a + (List.map Prod.fst (graphPairs fixed hints)).toFinset.card) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lift_ok mapped (proper_of _ hm) (proper_of _ hq) prior) enough
abbrev Face (u : Bool) (m L : Nat) := Lower u (varsX m) (graphGoal m) L
def tableWord (xs : Array Nat) (i : Nat) := xs.getD (i%8) 0
def tablePair (xs : Array (Nat × Nat)) (i : Nat) := xs.getD (i%8) (0,0)
def tableBits (xs : Array (Bits × Bits)) (i : Nat) := xs.getD (i%8) (0,0)
def readRules (pos neg width : Nat) (rules : Nat → Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,v => ruleData pos neg (rules (v % (1 <<< width))) :: readRules pos neg width rules n (v >>> width)
def readPanel (pos neg rw pw : Nat) (rules programs : Nat → Nat) (rec : Nat) :=
  let program := programs (rec % (1 <<< pw))
  (rec >>> pw,readRules pos neg rw rules (program % 16) (program >>> 4))
theorem consFace {u m L es} (h : Face u m L) (tail : Known u es) : Known u ((m,L)::es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | h'
  · exact h
  · exact tail e h'
def smallSlot (h buckets slots iw pw : Nat) (disp slotsAt : Nat → Nat) : Option (Nat × Nat) :=
  let slot := (h/buckets+disp (h%buckets))%slots
  let val := slotsAt slot
  if val=0 || (val >>> (iw+pw)) != (h/(buckets*slots))%8 then none
  else some (val % (1 <<< iw)-1,(val >>> iw)%(1 <<< pw))
def variableSlot (blocks : Nat → Nat × Nat) (i : Nat) :=
  let b := blocks (i/16)
  let offsets := b.1 >>> (12*(i%16))
  let start := offsets % 4096
  (b.2 >>> start) % (1 <<< ((offsets >>> 12)%4096 - start))
def bookData (d fw mw : Nat) (fronts masks codes costs : Nat → Nat) (j : Nat) :=
  let i := j/2
  if j%2=1 then costs i else
    let code := codes i
    fronts (code % (1 <<< fw)) + ((code >>> (fw+mw)) <<< (12*(d-1))) +
      (masks ((code >>> fw)%(1 <<< mw)) <<< (12*d))
noncomputable def bandTest (g : Forest) (k a n ar : Nat) :=
  header g k a n ar && rowCut g k a n ar 0 ar
theorem bandTest_sound {g k a n ar} (ok : bandTest g k a n ar=true) :
    block g k a n=true :=
  cutsBlock (Bool.and_eq_true_iff.mp ok).1 (Bool.and_eq_true_iff.mp ok).2
noncomputable def bandCells (g : Forest) (k a n ar : Nat) (splitBand : Bool) :=
  if splitBand then bandTest g k a (n/2) ar && bandTest g k (a+n/2) (n-n/2) ar
  else bandTest g k a n ar
theorem bandCut {g k a n} (ar : Nat) (splitBand : Bool) (ok : bandCells g k a n ar splitBand=true) :
    CutRow g k a n := by
  apply checkedRow
  cases splitBand
  · exact bandTest_sound ok
  · have both := Bool.and_eq_true_iff.mp ok
    have all := block_merge (bandTest_sound both.1) (bandTest_sound both.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using all
def readGroup (n pad : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | s+1,x => (pad+x % (1 <<< n)) :: readGroup n pad s (x >>> n)
def readGroups (n pad : Nat) : Nat → Nat → List (List Nat)
  | 0,_ => []
  | s+1,x =>
    let len := x % 64
    readGroup n pad len (x >>> 6) :: readGroups n pad s (x >>> (6+n*len))
def orderPage (pos neg w : Nat) (bank : Nat → Nat) (n q names clauses groups : Nat) : OrderPage :=
  let pad := 1024-(1 <<< n)
  (names,readRules pos neg w bank (clauses % 128) (clauses >>> 7),pad,readGroups n pad (q-1) groups)

theorem h6_1 : Face true 6 1 := countFace 288 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h12_1 : Face true 12 1 := carry_of (swaps:=[33,49]) (by decide +kernel) h6_1
theorem h14_2 : Face true 14 2 := countFace 8480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h17_1 : Face true 17 1 := carry_of (swaps:=[66,50,16]) (by decide +kernel) h6_1
theorem h24_1 : Face true 24 1 := carry_of (swaps:=[66,49]) (by decide +kernel) h6_1
theorem h28_2 : Face true 28 2 := carry_of (swaps:=[50,33,65]) (by decide +kernel) h14_2

namespace B29_4
def entries : List (Nat × Nat) := []
theorem prior : Known true entries := (known_down baseKnown)
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 20 0xe0ef0,padColumn 20 0xabad0),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x7dc3,padColumn 20 0x75d81),(padColumn 20 0x1f3cf,padColumn 20 0x8a246),(padColumn 20 0xf8f3c,padColumn 20 0x54528),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0)] i else tableBits #[(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0)] i))
def cols : List ColumnInfo := []
def data3 : Nat → Nat := (fun i => tableWord #[0xf,0x0] i)
def levels : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,data3)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨29,3,samples,cols,[[],[32,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row3_0 : CutRow book 3 0 1 := bandCut 4 false (by decide +kernel)
theorem band3 : CutRow book 3 0 1 := row3_0
theorem checked : mixedTables book 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band3
end B29_4
theorem h29_4 : Face true 29 4 :=
  mixedLower (g:=B29_4.book) (i:=0) (hints:=8964)
    (before_sound B29_4.entries B29_4.prior) B29_4.geometry B29_4.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h30_4 : Face true 30 4 := carry_of (swaps:=[66,16]) (by decide +kernel) h29_4
theorem h33_1 : Face true 33 1 := carry_of (swaps:=[82,66,50,16]) (by decide +kernel) h6_1
theorem h49_2 : Face true 49 2 := carry_of (swaps:=[83,65,16,32]) (by decide +kernel) h14_2
theorem h57_4 : Face true 57 4 := carry_of (swaps:=[82,48]) (by decide +kernel) h29_4

namespace B63_7
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h57_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 82 0x93fffe00003ff8460fc0,padColumn 82 0x1caaa0860ea50460d40),(padColumn 82 0x17fc000001fc31981fc03,padColumn 82 0x7fc186308b4319815801),(padColumn 82 0x3a4400007ffcc603ffc0f,padColumn 82 0x380061843348c602ca406),(padColumn 82 0x24fc001ffe03007fe103c,padColumn 82 0xfd8209cc13005521018),(padColumn 82 0x3f8807ff80000ffc860f0,padColumn 82 0x3f02055610600aa8860a0),(padColumn 82 0x3ff3f8000003f86318300,padColumn 82 0x3fe354186181586318200),(padColumn 82 0x0,padColumn 82 0x0),(padColumn 82 0x0,padColumn 82 0x0)] i else tableBits #[(padColumn 82 0x0,padColumn 82 0x0),(padColumn 82 0x0,padColumn 82 0x0)] i))
def cols : List ColumnInfo := [(1,32,30,0,4),(4,2,57,0,4),(34,0,29,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x603] i)
def levels : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨63,6,samples,cols,[[],[32,81,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
end B63_7
theorem h63_7 : Face true 63 7 :=
  mixedLower (g:=B63_7.book) (i:=0) (hints:=8484)
    (before_sound B63_7.entries B63_7.prior) B63_7.geometry B63_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h66_1 : Face true 66 1 := carry_of (swaps:=[98,82,66,50]) (by decide +kernel) h6_1
theorem h70_2 : Face true 70 2 := carry_of (swaps:=[99,83,67,33]) (by decide +kernel) h14_2
theorem h78_4 : Face true 78 4 := carry_of (swaps:=[98,82,66,48,16]) (by decide +kernel) h29_4
theorem h95_7 : Face true 95 7 := carry_of (swaps:=[101,66,16]) (by decide +kernel) h63_7
theorem h132_1 : Face true 132 1 := carry_of (swaps:=[114,98,82,66,33,49]) (by decide +kernel) h6_1
theorem h164_2 : Face true 164 2 := carry_of (swaps:=[114,98,83,33,65]) (by decide +kernel) h14_2
theorem h165_4 : Face true 165 4 := carry_of (swaps:=[115,67,100,83]) (by decide +kernel) h29_4
theorem h166_4 : Face true 166 4 := carry_of (swaps:=[115,50,98,83,66,16]) (by decide +kernel) h29_4
theorem h156_4 : Face true 156 4 := carry_of (swaps:=[114,98,32,66,50,80,16]) (by decide +kernel) h29_4
theorem h172_4 : Face true 172 4 := carry_of (swaps:=[115,50,98,48,66,80,16]) (by decide +kernel) h29_4
theorem h177_4 : Face true 177 4 := carry_of (swaps:=[114,50,99,82,64]) (by decide +kernel) h29_4

namespace B189_8
def entries : List (Nat × Nat) := [(29,4),(57,4),(156,4),(165,4),(172,4),(177,4)]
theorem prior : Known true entries := (consFace h29_4 (consFace h57_4 (consFace h156_4 (consFace h165_4 (consFace h172_4 (consFace h177_4 (known_down baseKnown)))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 84 0xe4003ffc00007ff8430f0,padColumn 84 0xe010e55410c07a9043050),(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0x3c0fc0000fc3e3183f303,padColumn 84 0x1c2a430c2343431816101),(padColumn 84 0xe8000003ffcc0c07ff00f,padColumn 84 0xe0c10c115c8c0c0569006),(padColumn 84 0x5c0000fff03180ffc403c,padColumn 84 0x1f0610aaa131806a84028),(padColumn 84 0x9ff03f00003e1f2198cc0,padColumn 84 0x1d681a20c62a052198480),(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0xf3ffc000003ff0c620f00,padColumn 84 0xe295a0c30814b0c620a00)] i else tableBits #[(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0x0,padColumn 84 0x0)] i))
def cols : List ColumnInfo := [(12,0,177,0,4),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def data7 : Nat → Nat := (fun i => tableWord #[0x3f,0x171506] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x7f420,0x0,0x7f440,0x201] i)
def data5 : Nat → Nat := (fun i => tableWord #[0xb7cc3440,0x0] i)
def levels : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,data5)
  | 6 => (2,1,3,0,0,0,0,data6)
  | 7 => (1,0,3,0,0,0,0,data7)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=7502621870530246385 then some (0,0) else none)
  | 7 => fun h => smallSlot h 4 14 2 4 (fun i => ((fun i => tableWord #[0x2000] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0xa200000010346416663cd6000009cca] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨189,7,samples,cols,[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66],[112,66,48,82]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 6 false (by decide +kernel)
theorem band7 : CutRow book 7 0 1 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 2 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 2 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
  · exact band7
end B189_8
theorem h189_8 : Face true 189 8 :=
  mixedLower (g:=B189_8.book) (i:=0) (hints:=536879876)
    (before_sound B189_8.entries B189_8.prior) B189_8.geometry B189_8.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h198_4 : Face true 198 4 := carry_of (swaps:=[114,96,82,50,64,16]) (by decide +kernel) h29_4
theorem h231_7 : Face true 231 7 := carry_of (swaps:=[83,82,114,99,66,16]) (by decide +kernel) h63_7
theorem h183_7 : Face true 183 7 := carry_of (swaps:=[115,84,99]) (by decide +kernel) h63_7

namespace B190_7
def entries : List (Nat × Nat) := [(30,4),(156,4),(166,4)]
theorem prior : Known true entries := (consFace h30_4 (consFace h156_4 (consFace h166_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xfcfe000001f86030fc03,padColumn 80 0xfc7e0c20c3586030d401),(padColumn 80 0x279203e03ff81c0ffccf,padColumn 80 0x38012810ca018052846),(padColumn 80 0x5d2e001ffe0183ff043c,padColumn 80 0x1c0e604a720982aa0418),(padColumn 80 0xebf4001fc0060ff11830,padColumn 80 0xe3f1819584360d511820),(padColumn 80 0x93fffc000007f0c66300,padColumn 80 0x3feb60618c550c66100),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xfe49ffe00007ff0883c0,padColumn 80 0xfc0149782102a7088280)] i else tableBits #[(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0x0,padColumn 80 0x0)] i))
def cols : List ColumnInfo := [(8,16,166,0,4),(24,0,166,0,4),(34,0,156,0,4),(128,32,30,0,4),(160,0,30,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x4cc05] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x7ec20,0x0] i)
def levels : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,data5)
  | 6 => (1,0,3,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=7689521405595769300 then some (0,0) else none)
  | _ => fun _ => none
def book : Forest := ⟨190,6,samples,cols,[[],[115,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
end B190_7
theorem h190_7 : Face true 190 7 :=
  mixedLower (g:=B190_7.book) (i:=0) (hints:=544416032)
    (before_sound B190_7.entries B190_7.prior) B190_7.geometry B190_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h222_7 : Face true 222 7 := carry_of (swaps:=[101,113]) (by decide +kernel) h190_7
theorem h238_7 : Face true 238 7 := carry_of (swaps:=[84,100,49,113]) (by decide +kernel) h190_7

namespace B255_11
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(166,4),(177,4),(183,7),(189,8),(190,7),(198,4),(222,7),(231,7),(238,7)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h189_8 (consFace h190_7 (consFace h198_4 (consFace h222_7 (consFace h231_7 (consFace h238_7 (known_down baseKnown))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 248 0xf8787c3f888447fe210f80000001ffffe0000000000c03ffffc02060303c0,padColumn 248 0x78783c3f800003fe0007802030074aaaa0080c06000c03d55280206030140),(padColumn 248 0x1088fffc7910888425fff80000ffe0000000003fe0603ff0180c0c01ff0c03,padColumn 248 0x7ffc7800000001fff80c0455201806030125a0602aa0180c0c01560401),(padColumn 248 0x211108448f813fcbfe210801ff00000000007fffe01fc000603001ffff300f,padColumn 248 0x7803fc3fe000010d10080601804165a40168000603000aca91006),(padColumn 248 0x47f813ff8227d13c484ff8000000000001ffffc0018000c18003fffe04003c,padColumn 248 0x7f803ff8007c03c000ff8600803018020a9e980818000c18002ab52040018),(padColumn 248 0xfa227c8917fa03d09ff2100000000007ffff80000603030007fffe081800f0,padColumn 248 0xf8007c0007f803c01ff00180300c0205555602030603030002d554081800a0),(padColumn 248 0x8444211227fffc211fffa7fe00001ff8000000001fe40c0ff840303060c300,padColumn 248 0x7fffc001fff82b440300b5040180c0c15440c02a8403030604200),(padColumn 248 0xffffc22047ffffffe084400000ffe0000000000018183ff60180c0c0800c00,padColumn 248 0xffff800007ffffffe000060180aacc0180603010181815560180c0c0800800),(padColumn 248 0xfffffffffc442202110807ffff000000000000001ffff0080603010100f000,padColumn 248 0xfffffffff80000000000054b2ec01006018040200aa970080603010100a000)] i else tableBits #[(padColumn 248 0x0,padColumn 248 0x0),(padColumn 248 0x0,padColumn 248 0x0)] i))
def cols : List ColumnInfo := [(2,64,189,0,8),(66,0,189,0,8),(17,0,238,0,7),(24,0,231,0,7),(33,0,222,0,7),(65,0,190,0,7),(72,0,183,0,7),(160,0,95,0,7),(192,0,63,0,7),(41,16,198,0,4),(56,1,198,0,4),(57,0,198,0,4),(73,16,166,0,4),(78,0,177,0,4),(89,0,166,0,4),(176,1,78,0,4),(177,0,78,0,4),(193,32,30,0,4),(198,0,57,0,4),(225,0,30,0,4),(226,0,29,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x220ce106] i)
def data9 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x1ff440,0x2a014f04,0x1ff460,0xe038f04,0x1ff462,0xf44c40d05,0x1ff482,0x115200cc05] i else tableWord #[0x1ff4a3,0x202d103,0x1ff4e3,0xa48c80f18707,0x1ff4a4,0x53202d105,0x1ff862,0x83d14930cd08] i) else tableWord #[0x1ff882,0x321224d06,0x1ffc40,0x31c529206] i))
def data8 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x2efd04460,0x306102,0x2f7d03482,0x306102,0x2fed004a4,0x306102,0x2ef504c40,0x1201] i else tableWord #[0x3f7862460,0x18e02,0x3f74e3462,0x1401,0x2ff507462,0x0,0x2ffd07482,0x0] i) else tableWord #[0x2ffd024e3,0x6001] i))
def levels : Nat → Packing
  | 8 => (9,2,5,0,0,0,0,data8)
  | 9 => (10,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => smallSlot h 5 17 4 1 (fun i => ((fun i => tableWord #[0x380c4] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xe502d4612369a708e6e4760000000000,0x0] i) (i/16) >>> (8*(i%16))) % 256)
  | 10 => fun h => smallSlot h 8 25 4 1 (fun i => ((fun i => tableWord #[0x10400180c1] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xd800000000e15265440043e92600a2,0x338a008708191594] i) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨255,10,samples,cols,[[],[115,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 10 := bandCut 9 true (by decide +kernel)
theorem band9 : CutRow book 9 0 10 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 5 := bandCut 9 false (by decide +kernel)
theorem combine8_0_9 : CutRow book 8 0 9 := @joinRow book 8 0 4 5 row8_0 row8_4
theorem band8 : CutRow book 8 0 9 := combine8_0_9
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B255_11
theorem h255_11 : Face true 255 11 :=
  mixedLower (g:=B255_11.book) (i:=0) (hints:=553656612)
    (before_sound B255_11.entries B255_11.prior) B255_11.geometry B255_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h305_4 : Face true 305 4 := carry_of (swaps:=[130,114,50,99,82,64]) (by decide +kernel) h29_4
theorem h326_4 : Face true 326 4 := carry_of (swaps:=[130,50,115,98,83,32,64,16]) (by decide +kernel) h29_4
theorem h352_2 : Face true 352 2 := carry_of (swaps:=[130,33,113,99,82,65]) (by decide +kernel) h14_2
theorem h353_4 : Face true 353 4 := carry_of (swaps:=[131,50,66,116,99,82]) (by decide +kernel) h29_4
theorem h354_4 : Face true 354 4 := carry_of (swaps:=[131,67,116,99,82,16]) (by decide +kernel) h29_4
theorem h359_7 : Face true 359 7 := carry_of (swaps:=[131,67,116,99,82,16]) (by decide +kernel) h63_7
theorem h366_7 : Face true 366 7 := carry_of (swaps:=[128,64,116,49,96]) (by decide +kernel) h63_7
theorem h371_7 : Face true 371 7 := carry_of (swaps:=[131,84,115,98]) (by decide +kernel) h63_7
theorem h377_7 : Face true 377 7 := carry_of (swaps:=[128,80,84,66,16,114,97,48]) (by decide +kernel) h63_7
theorem h317_7 : Face true 317 7 := carry_of (swaps:=[133,117,80,48,50,33,97,64]) (by decide +kernel) h63_7
theorem h350_7 : Face true 350 7 := carry_of (swaps:=[133,117,50,65,96]) (by decide +kernel) h63_7

namespace B383_11
def entries : List (Nat × Nat) := [(57,4),(63,7),(78,4),(95,7),(317,7),(326,4),(350,7),(353,4),(354,4),(359,7),(366,7),(371,7),(377,7)]
theorem prior : Known true entries := (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h317_7 (consFace h326_4 (consFace h350_7 (consFace h353_4 (consFace h354_4 (consFace h359_7 (consFace h366_7 (consFace h371_7 (consFace h377_7 (known_down baseKnown))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 248 0x87c3ffe22111ffc421f00000003ffffc0000000000180fffff0080c0303c0,padColumn 248 0x3c3ffe00000ffc000f0040300e955540100c03000180f554a0080c030140),(padColumn 248 0x17ffc03e44222084bfff00000ffc0000000003ff03007fc060303003ff0c03,padColumn 248 0x7ffc01e000000003fff01804aa40300c060112d03006a8060303002560401),(padColumn 248 0xf88447e3e04ff17fc421000000000000000fffff0c06000180c007ffff000f,padColumn 248 0xf80003e1e00ff07fc000060180100c03008566d20c06000180c00559a90006),(padColumn 248 0x213ffc4089f44f8909ff0000000000003ffffc0030180306000ffffc04003c,padColumn 248 0x3ffc0001f00f8001ff180600603004153a980430180306000aaaa4040018),(padColumn 248 0xffc88885fe80f213fe420000000000fffff00000c0600c001ffff8101800f0,padColumn 248 0xffc00001fe00f003fe006018018040aaaac02018c0600c000b5550101800a0),(padColumn 248 0x42111109ffff0423fff4ffc00003ff0000000000ff80303fe100c06060c300,padColumn 248 0x1ffff0003fff0aaa006016a080300c060aa80300aa100c060604200),(padColumn 248 0x84222211fffffffc1088003ffffc00000000000000ffffd806030180803c00,padColumn 248 0x1fffffffc0000802a955980300c03008000d5155806030180801800),(padColumn 248 0x0,padColumn 248 0x0)] i else tableBits #[(padColumn 248 0xffffffff110888422100fffff000000000000000ffffc020180c060300f000,padColumn 248 0xfffffffe0000000000005555680200c0300c0300552ac020180c060300a000),(padColumn 248 0x0,padColumn 248 0x0)] i))
def cols : List ColumnInfo := [(6,0,377,0,7),(12,0,371,0,7),(17,0,366,0,7),(24,0,359,0,7),(33,0,350,0,7),(66,0,317,0,7),(288,0,95,0,7),(320,0,63,0,7),(22,8,353,0,4),(29,0,354,0,4),(56,1,326,0,4),(57,0,326,0,4),(304,1,78,0,4),(324,2,57,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x1256034708] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x1ff420,0x14d02,0x1ff440,0x12a02,0x1ff460,0x1b10b04] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x2efd04460,0x0] i)
def levels : Nat → Packing
  | 8 => (1,2,4,0,0,0,0,data8)
  | 9 => (3,1,4,0,0,0,0,data9)
  | 10 => (1,0,4,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=9836245588253958792 then some (0,0) else none)
  | 10 => fun h => smallSlot h 13 44 2 4 (fun i => ((fun i => tableWord #[0xc0000000001000] i) (i/16) >>> (6*(i%16))) % 64) (fun i => ((fun i => tableWord #[0x23003de000051c9400000000061,0x96c760d27c1eb801320000000019e,0x23c00662d0039600f38018511] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨383,10,samples,cols,[[],[98,131,84],[16,66,101],[16,82,131,100],[32,81,67,134],[32,81,128,99,65,67,64],[48,129,98,16,66,84],[48,129,82],[64,97,33,50,48,80,133],[64,97,130,83],[80,33,49,65,16,129,97],[80,33,99,132],[96,65,50,133],[96,65,32,83,129,49,50],[128,49,100],[128,49,66,16,82,98]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 3 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 1 := bandCut 8 false (by decide +kernel)
theorem band8 : CutRow book 8 0 1 := row8_0
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B383_11
theorem h383_11 : Face true 383 11 :=
  mixedLower (g:=B383_11.book) (i:=0) (hints:=21491622180)
    (before_sound B383_11.entries B383_11.prior) B383_11.geometry B383_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h486_8 : Face true 486 8 := carry_of (swaps:=[115,83,82,130,99,66,16]) (by decide +kernel) h189_8
theorem h503_11 : Face true 503 11 := carry_of (swaps:=[115,82,98,131,66,16]) (by decide +kernel) h255_11
theorem h480_4 : Face true 480 4 := carry_of (swaps:=[32,48,132,115,98,80,16]) (by decide +kernel) h29_4
theorem h497_7 : Face true 497 7 := carry_of (swaps:=[113,82,129,98,16,48]) (by decide +kernel) h190_7
theorem h509_11 : Face true 509 11 := carry_of (swaps:=[82,48,66,129,112]) (by decide +kernel) h255_11
theorem h510_11 : Face true 510 11 := carry_of (swaps:=[84,100,49,113,128]) (by decide +kernel) h255_11

namespace B511_13
def entries : List (Nat × Nat) := [(29,4),(30,4),(63,7),(78,4),(95,7),(177,4),(189,8),(222,7),(231,7),(255,11),(305,4),(353,4),(371,7),(377,7),(383,11),(480,4),(486,8),(497,7),(503,11),(509,11),(510,11)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h177_4 (consFace h189_8 (consFace h222_7 (consFace h231_7 (consFace h255_11 (consFace h305_4 (consFace h353_4 (consFace h371_7 (consFace h377_7 (consFace h383_11 (consFace h480_4 (consFace h486_8 (consFace h497_7 (consFace h503_11 (consFace h509_11 (consFace h510_11 (known_down baseKnown))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0x3e1f0fe108210fff0820f800000000000003fffff8000000000000c0003007fffff00201803003c0,padColumn 320 0x3e0f0fe0000007ff0000780100300200c00f4aaaa8008030060000c0003007d554a0020180300140),(padColumn 320 0x43fff1e21042104117fff800000000003ffc00000000000ffe060000600ffe0180300c007ff00c03,padColumn 320 0x1fff1e00000000007fff80600400c012aa40180180300465a060000600d540180300c0055600401),(padColumn 320 0x8421123f009ff8bff8410800000001ffc000000000007ffffe1803001ff0000600c001fffff0300f,padColumn 320 0x1f001ff83ff8000018018010b44010060060042599a418030015a0000600c0012b2a901006),(padColumn 320 0xc04ffe0427e427c2209ff800000000000000000007fffff000600c0180001818000fffff8040003c,padColumn 320 0xc00ffe0007e007c0001ff860060060020060180082a9da6008600c0180001818000aaad480400018),(padColumn 320 0x9f2245ff900f904ffe21000000000000000007fffff80000180300600c060007ffffe02018000f0,padColumn 320 0x1f0001ff800f800ffe001801801800c01802055555600803180300600c060002b555402018000a0),(padColumn 320 0x1084489fffff0208ffffa7ff000ffe000003ff800000000001fe403fe10181ff8100300c060cc300,padColumn 320 0x1fffff0000ffff82aa2002b4100600b50100180300c15440154101802a8100300c06044200),(padColumn 320 0xff08811fffffffff01044000fff000003ffc0000000000000001ffd8060ffe600600c03008030c00,padColumn 320 0xfe00001fffffffff000002006a9600601558c00600600c0100016a980602aa600600c03008010800),(padColumn 320 0xffffffe84208401042080000000fffffc0000000000000000001803ffff60080180300401000f000,padColumn 320 0xffffffe00000000000000400c00d4b4b98010018018010020001802aaa560080180300401000a000)] i else tableBits #[(padColumn 320 0x2000001084108420841007fffff00000000000000000000001ffffe018080100600c0180600f0000,padColumn 320 0x55595680180200200600600600c00aa956018080100600c0180600a0000),(padColumn 320 0x0,padColumn 320 0x0)] i))
def cols : List ColumnInfo := [(1,0,510,0,11),(2,0,509,0,11),(8,0,503,0,11),(128,0,383,0,11),(256,0,255,0,11),(9,16,486,0,8),(25,0,486,0,8),(258,64,189,0,8),(322,0,189,0,8),(14,0,497,0,7),(134,0,377,0,7),(140,0,371,0,7),(280,0,231,0,7),(289,0,222,0,7),(416,0,95,0,7),(448,0,63,0,7),(31,0,480,0,4),(154,4,353,0,4),(202,4,305,0,4),(334,0,177,0,4),(401,32,78,0,4),(418,64,29,0,4),(449,32,30,0,4)]
def data12 : Nat → Nat := (fun i => tableWord #[0x1ff,0x1142438cc809] i)
def data11 : Nat → Nat := (fun i => tableWord #[0x3ff0a2,0x72051a7a0d24e09,0x3ff4a2,0x730f8248a18ce2a54560d,0x3ff8a2,0x528c3e090d9d058b0b] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x57fd274a2,0x32601d9c89606,0x7dbca28a2,0xb2a4c80e05,0x77fd274a2,0x3c91403,0x5ff5258a2,0x3c91403] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x97fd475258a2,0x0] i)
def levels : Nat → Packing
  | 9 => (1,3,5,0,0,0,0,data9)
  | 10 => (4,2,5,0,0,0,0,data10)
  | 11 => (3,1,5,0,0,0,0,data11)
  | 12 => (1,0,5,0,0,0,0,data12)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=11369311757800862412 then some (0,0) else none)
  | 11 => fun v => (if v=11369311757800862412 then some (0,0) else (if v=11458423956265286981 then some (1,0) else (if v=12322638194242191766 then some (3,0) else (if v=12698024304231822181 then some (2,0) else none))))
  | 12 => fun v => (if v=11787858522310454322 then some (2,1) else (if v=12115950459901266192 then some (2,0) else (if v=12322638194242191766 then some (1,0) else (if v=13136768276869170638 then some (0,0) else none))))
  | _ => fun _ => none
def book : Forest := ⟨511,12,samples,cols,[[],[48,129,82],[16,82,131,100],[128,49,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 9 false (by decide +kernel)
theorem band12 : CutRow book 12 0 1 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 3 := bandCut 10 false (by decide +kernel)
theorem band11 : CutRow book 11 0 3 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 2 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_2 : CutRow book 10 2 2 := bandCut 10 false (by decide +kernel)
theorem combine10_0_4 : CutRow book 10 0 4 := @joinRow book 10 0 2 2 row10_0 row10_2
theorem band10 : CutRow book 10 0 4 := combine10_0_4
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
theorem checked : mixedTables book 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
end B511_13
theorem h511_13 : Face true 511 13 :=
  mixedLower (g:=B511_13.book) (i:=0) (hints:=22028493092)
    (before_sound B511_13.entries B511_13.prior) B511_13.geometry B511_13.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h528_1 : Face true 528 1 := carry_of (swaps:=[146,130,114,98,33,81,66,49]) (by decide +kernel) h6_1
theorem h576_1 : Face true 576 1 := carry_of (swaps:=[146,130,33,113,98,81,66,49]) (by decide +kernel) h6_1
theorem h593_4 : Face true 593 4 := carry_of (swaps:=[147,131,50,114,99,82]) (by decide +kernel) h29_4
theorem h599_7 : Face true 599 7 := carry_of (swaps:=[147,131,67,116,66,99,82,16]) (by decide +kernel) h63_7
theorem h606_8 : Face true 606 8 := carry_of (swaps:=[151,135,101,66,16]) (by decide +kernel) h189_8
theorem h657_4 : Face true 657 4 := carry_of (swaps:=[147,131,114,99,82]) (by decide +kernel) h29_4
theorem h540_4 : Face true 540 4 := carry_of (swaps:=[146,130,114,98,67,32,80,16]) (by decide +kernel) h29_4
theorem h652_4 : Face true 652 4 := carry_of (swaps:=[146,130,115,98,48,66,80,16]) (by decide +kernel) h29_4
theorem h660_4 : Face true 660 4 := carry_of (swaps:=[147,131,116,66,99,32,80,16]) (by decide +kernel) h29_4
theorem h664_4 : Face true 664 4 := carry_of (swaps:=[147,50,130,115,48,98,80,16]) (by decide +kernel) h29_4

namespace B668_7
def entries : List (Nat × Nat) := [(156,4),(540,4),(652,4),(660,4),(664,4)]
theorem prior : Known true entries := (consFace h156_4 (consFace h540_4 (consFace h652_4 (consFace h660_4 (consFace h664_4 (known_down baseKnown))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1e1e3e3c33,padColumn 45 0x2742a3c2411),(padColumn 45 0x1ff81fc0f,padColumn 45 0xc8355819806),(padColumn 45 0x1e1e077c4cc,padColumn 45 0x112ca2664448),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1e1e01cecb30,padColumn 45 0x150ac542c920)] i else tableBits #[(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1fe001f933c0,padColumn 45 0xad118993280)] i))
def cols : List ColumnInfo := [(4,0,664,0,4),(8,0,660,0,4),(16,0,652,0,4),(128,0,540,0,4),(512,0,156,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x1f,0x29c05] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x3f420,0x0,0x3f440,0x101] i)
def data4 : Nat → Nat := (fun i => tableWord #[0x5dca1440,0x0] i)
def levels : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,data4)
  | 5 => (2,1,3,0,0,0,0,data5)
  | 6 => (1,0,3,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun v => (if v=5239425270783651293 then some (0,0) else none)
  | 6 => fun h => smallSlot h 5 16 2 4 (fun i => ((fun i => tableWord #[0x50050] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x2085400000025800000051505ca6e9199d0d] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨668,6,samples,cols,[[],[115,148],[50,116],[50,66,146,114],[66,151],[66,147,114,50],[114,50,67,148],[114,147],[146,67],[146,115,66,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 5 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 2 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 2 := row5_0
set_option maxRecDepth 16000 in
theorem row4_0 : CutRow book 4 0 1 := bandCut 5 false (by decide +kernel)
theorem band4 : CutRow book 4 0 1 := row4_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band4
  · exact band5
  · exact band6
end B668_7
theorem h668_7 : Face true 668 7 :=
  mixedLower (g:=B668_7.book) (i:=0) (hints:=275414983424)
    (before_sound B668_7.entries B668_7.prior) B668_7.geometry B668_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h679_7 : Face true 679 7 := carry_of (swaps:=[145,129,49,99,48,114,81,64]) (by decide +kernel) h190_7
theorem h685_7 : Face true 685 7 := carry_of (swaps:=[145,129,97,83,114,16,64]) (by decide +kernel) h190_7
theorem h689_7 : Face true 689 7 := carry_of (swaps:=[116,83,16,32]) (by decide +kernel) h668_7
theorem h561_4 : Face true 561 4 := carry_of (swaps:=[146,130,114,32,48,99,82,64]) (by decide +kernel) h29_4
theorem h646_4 : Face true 646 4 := carry_of (swaps:=[146,130,115,98,83,66,16]) (by decide +kernel) h29_4
theorem h663_7 : Face true 663 7 := carry_of (swaps:=[147,131,116,66,99,32,80,16]) (by decide +kernel) h63_7
theorem h694_7 : Face true 694 7 := carry_of (swaps:=[151,114,130,81,98,50,65]) (by decide +kernel) h190_7

namespace B695_10
def entries : List (Nat × Nat) := [(165,4),(166,4),(183,7),(561,4),(646,4),(660,4),(663,7),(679,7),(689,7),(694,7)]
theorem prior : Known true entries := (consFace h165_4 (consFace h166_4 (consFace h183_7 (consFace h561_4 (consFace h646_4 (consFace h660_4 (consFace h663_7 (consFace h679_7 (consFace h689_7 (consFace h694_7 (known_down baseKnown)))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 146 0x47fc7c440000001fffe0030000ffff80c03c,padColumn 146 0x3fc3c001810106cb4a0330000ed6500c014),(padColumn 146 0xbc7ffcbc00000000001ffc18300181ffc003,padColumn 146 0x3c3ffc3c60606080606d5c18300181da8001),(padColumn 146 0x3cbc487c800000fe0001ff000cfc6067fc0c3,padColumn 146 0x3c3c003c080818d218192a000ce8606254042),(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x1108bcbfc000ff0001fe00067f3007f83030c,padColumn 146 0x3c3fd030aa3020b40c066a3001a830108),(padColumn 146 0x3fd1113fc07f0001fe00000fb043f880c0c30,padColumn 146 0x3fc0003fe05a60413420300d30412880c0420),(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x22223fd13fff00fe000000ffc0fc830103cc0,padColumn 146 0x3fc012a5802c40c040a2c014830101880)] i else tableBits #[(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x3fffe2223f80ff00000000f87f83040603300,padColumn 146 0x3fffc0002d405581810180581583040602200)] i))
def cols : List ColumnInfo := [(1,0,694,0,7),(16,0,679,0,7),(32,0,663,0,7),(512,0,183,0,7),(4,2,689,0,7),(6,0,689,0,7),(35,0,660,0,4),(48,1,646,0,4),(134,0,561,0,4),(513,16,166,0,4),(529,0,166,0,4),(530,0,165,0,4)]
def data9 : Nat → Nat := (fun i => tableWord #[0x7f,0x40123506] i)
def data8 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xff460,0xa552a04,0xff480,0x50e603,0xff4a0,0x282582a706,0xff4c0,0x140d4ea05] i else tableWord #[0xff4a4,0x282424f506,0xff4c4,0x5043454e907,0xffca0,0x242ace807,0xffca4,0x810a93a84808] i))
def data7 : Nat → Nat := bookData 2 3 3 (fun i => ((fun i => tableWord #[0xca44c44a4ca04c04a0] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x1efdfdfeef6f] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => tableWord #[0x139954e64b3954ce64d39934c48e3159ce64138cace3273900] i) (i/16) >>> (18*(i%16))) % 262144) (fun i => (if i<8 then tableWord #[0xd3502,0xd3502,0x801,0x0,0x84a02,0xb01,0x0,0x0] i else tableWord #[0x3401,0x0,0x0] i))
def levels : Nat → Packing
  | 7 => (11,2,4,0,0,0,0,data7)
  | 8 => (8,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun h => smallSlot h 6 20 4 1 (fun i => ((fun i => tableWord #[0x18100] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x2529a38400817588000007008a000016,0x2286008b] i) (i/16) >>> (8*(i%16))) % 256)
  | 9 => fun h => smallSlot h 7 22 4 1 (fun i => ((fun i => tableWord #[0x86020403] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xc16288c35300000038d4a5b207a655d7,0x400000000] i) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨695,9,samples,cols,[[],[64,149]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 7 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 8 := bandCut 8 true (by decide +kernel)
theorem band8 : CutRow book 8 0 8 := row8_0
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 3 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_3 : CutRow book 7 3 8 := bandCut 8 true (by decide +kernel)
theorem combine7_0_11 : CutRow book 7 0 11 := @joinRow book 7 0 3 8 row7_0 row7_3
theorem band7 : CutRow book 7 0 11 := combine7_0_11
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
end B695_10
theorem h695_10 : Face true 695 10 :=
  mixedLower (g:=B695_10.book) (i:=0) (hints:=275414778148)
    (before_sound B695_10.entries B695_10.prior) B695_10.geometry B695_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h573_7 : Face true 573 7 := carry_of (swaps:=[145,129,66,16,112]) (by decide +kernel) h190_7
theorem h673_4 : Face true 673 4 := carry_of (swaps:=[146,50,131,66,116,99,82]) (by decide +kernel) h29_4
theorem h688_4 : Face true 688 4 := carry_of (swaps:=[148,132,66,64,115,98,80,16]) (by decide +kernel) h29_4

namespace B701_11
def entries : List (Nat × Nat) := [(29,4),(57,4),(156,4),(165,4),(172,4),(177,4),(189,8),(540,4),(561,4),(573,7),(652,4),(657,4),(660,4),(664,4),(668,7),(673,4),(685,7),(688,4),(689,7)]
theorem prior : Known true entries := (consFace h29_4 (consFace h57_4 (consFace h156_4 (consFace h165_4 (consFace h172_4 (consFace h177_4 (consFace h189_8 (consFace h540_4 (consFace h561_4 (consFace h573_7 (consFace h652_4 (consFace h657_4 (consFace h660_4 (consFace h664_4 (consFace h668_7 (consFace h673_4 (consFace h685_7 (consFace h688_4 (consFace h689_7 (known_down baseKnown))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 145 0x23ffe20000001fffc00018001fffc10300f0,padColumn 145 0x1ffe00c08106cb5408198001dac81030050),(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x5e3e3e00000fe000007f8007f830c0ff0303,padColumn 145 0x1e1e1e10106d2060c1268007d030c0960101),(padColumn 145 0x1e5e3e400000000003fffe0c000c03fff000f,padColumn 145 0x1e1e1e060608081812ad960c000c035690006),(padColumn 145 0x88445e0007f0001fff80033e600fff040c3c,padColumn 145 0x1e818523020a9502033460034a040428),(padColumn 145 0x1fe889e03f8001fe0000007d887f1061830c0,padColumn 145 0x1fe001f02b3041342060c0698825106181080),(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x11111e9fff80fe00000007fe1f9061820f300,padColumn 145 0x1e0a54c02c40c18105160290618206200)] i else tableBits #[(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x1ffff11fc07f0000000007c3f060820c0cc00,padColumn 145 0x1fffe015a02d8181020602c0b060820c08800)] i))
def cols : List ColumnInfo := [(512,0,189,0,8),(16,0,685,0,7),(128,0,573,0,7),(12,0,689,0,7),(33,0,668,0,7),(13,0,688,0,4),(20,8,673,0,4),(28,0,673,0,4),(37,0,664,0,4),(41,0,660,0,4),(44,0,657,0,4),(48,1,652,0,4),(49,0,652,0,4),(129,32,540,0,4),(136,4,561,0,4),(140,0,561,0,4),(161,0,540,0,4),(524,0,177,0,4),(529,0,172,0,4),(536,0,165,0,4),(545,0,156,0,4),(644,0,57,0,4),(672,0,29,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0x7f,0x6403] i)
def data9 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0xff0a3,0x49604310e18c4c20b,0xff420,0x20108b80e0c408,0xff440,0x108980b0c407,0xff460,0x422e348407] i else tableWord #[0xff4a0,0x10a040b8c407,0xff4c0,0x108b02348407,0xff4a3,0x200428e406,0xff4c3,0x10928c091307] i) else tableWord #[0xff8a3,0x31062c24e39010a,0xff8c3,0x218b8e400107,0xffc60,0x864e304407,0xffca0,0x138b56310208] i))
def data8 : Nat → Nat := bookData 2 4 4 (fun i => ((fun i => tableWord #[0xca0c608c34c34c04604404200a38a34a34a0] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x7ffefbff7f7ffd7febdf67f6f] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => tableWord #[0x4e6454e5454e3454a05546055ce644ce3444e6444e3444a0544e6434e043ca3324e122ce611ce400,0xca360ce240ce1404e6404a3604c050ce646ce546ce246ce1464e6464e5464c056ce645ce545ce345,0xce641ce0418c3914e6414c3910e681ce547ce347ce247ce1478c5874c3874c187ce640ce470ce340,0x4e24a4e14a4a05a8c5894e5494e1494e0494e6424e5424c3924e1424e042ce548ce148ce048ce681,0x4a1a6461a6ca3a58c5a54c5a54c3a54a3a54c3a44a3a44e64b4e34b4a36b4e24b4e14b4e64a4e54a,0x4c3a04a3a04c2a04a2a04c1a0461a0ca3a6ca2a6ca1a68c5a64c5a64a3a64c2a64a2a6462a64c1a6,0xca1aa8c5aa4c5aa4c1aa4c5a28e5a84e5a84e1a8ce6a1ce0a14e6a14c3a14e0a1ca3a74a3a74c5a0,0x4c3ab4c2ab] i) (i/16) >>> (20*(i%16))) % 1048576) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc18c59004,0x830b1e404,0x8b0c3071306,0x2654581043439608,0x59202,0x245499604,0xc70b03,0x65858e04] i else tableWord #[0x2058e03,0x58802,0x1870803,0x1a18b03,0x2c1218b04,0x18a8b03,0x4125a18b05,0x10e2012c8030b07] i) else (if i<24 then tableWord #[0x18048b03,0x3830904,0xa3830904,0x459203,0x30e251088b07,0x90b02,0x3071203,0x231a5890605] i else tableWord #[0x30b1c4461206,0x61c3079205,0xe084100b05,0xc4220b04,0x401030e284480b08,0x464c80e04,0x5831003,0x1059003] i)) else (if i<48 then (if i<40 then tableWord #[0x859003,0x1080b03,0x10061c4459006,0x39028551c406,0x84059204,0x42d04a1005,0x64871404,0x5831403] i else tableWord #[0x18c59203,0x81858e204839408,0x142a4cb2005,0x11a4c72005,0x401858d1c5890a08,0x843470616580a008,0x64838a8b05,0x20c2c79030e16345200a] i) else (if i<56 then tableWord #[0x20c7920c205,0xe263c59205,0xd2c4871305,0xd1c4841305,0x59202,0x38e02,0x1a4871304,0x41000c3458e07] i else tableWord #[0x68e2a5891306,0x59202,0xc38e03,0x110d1c185c006,0x20a202,0x41070b04,0xc38e03,0x11031303] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x3834404,0xe2b1099205,0x71502,0x30f02,0xc4870b04,0x20c5470b05,0x6122ca9605,0x402c40e04] i else tableWord #[0x2071303,0x20021848b05,0x48b02,0x2459603,0xc8058904,0x1848b03,0x8c70703,0x71502] i) else (if i<88 then tableWord #[0x71502,0x31302,0x8c78603,0x98602,0x459203,0x2c91603,0x2c91603,0x462c91604] i else tableWord #[0x462c91604,0x8c59203,0x23171038e05,0x885459004,0x471079004,0x882c81304,0x411059004,0x11080b03] i)) else (if i<112 then (if i<104 then tableWord #[0x2c81603,0xa0b02,0x4640a0b04,0x20164092405,0x4004b1304,0x8099603,0x120b02,0x4cb2003] i else tableWord #[0x5439303,0x99602,0x10491303,0x4ca9603,0x881c71504,0x11099603,0x41164091605,0x38b1c4091506] i) else tableWord #[0x11031303,0xb1202] i))))
def data7 : Nat → Nat := bookData 3 7 5 (fun i => ((fun i => tableWord #[0x4a04204e5c604e1c604a0c608c58c34e18c38c34a30e64a3ce14c08c54c04e64a04e5460ce54404e64404e54404e3420,0xca3460ce24608c54604a34604a24604c14604614604c0460ce64408c54404e34404a34404a0440460440ce64204a3420,0xca34c0ce24c04a34c04c14c0ce64a0ce44a0ce24a0ce14a04c34a04a34a04c24a04a24a04c14a04614a04c04a0ce6460,0xca1c608c5c604c5c604e08c34e58a34c58a34c38a34e18a3ce04c38e54c34e14c3ce64a3ce04a34e64a34c34a34e04a3,0x4c3ca04a3ca0] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xcff77feafe9febfdfaf6adf97c7e6f8fe779f67b,0xdf6f7bbfb7d7f9fb7f6ff5efdbefbe] i) (i/16) >>> (10*(i%16))) % 1024) (fun i => ((fun i => tableWord #[0xd0618ed0200dd0340c50338bd0200a8c5309907188502007ce5286d04205d06184d04204506183d03102d01081d02000,0x5035834e6796d05582d06581d06595d05595d06514ce3714ce64934a2693ce6492d05612503591d06580d06510ce648f,0xd026214c18215055a050289f50559ece679dd06584d0651cd0191bce679ad028998c58184c1818505597503597506583,0x5035a8ce4a27d06b26d06526ce6ba6ce4a264c39a6106b26ce67a5ce4a25d01924d05aa3ce4a234e67a3d028a24a39a2,0xd04cb00e67b09075085028af8c57ae5055ae503506501506d0652d8c5b2d4c3c2dd0352c5035ab4c5a2a5065a95065a8,0x5055b7503d36500636d028b5d007b45037b45007b4ce67b35065b30e67b3ce6c09d067b2ce6c31ce67b1d06530ce67b0,0x5075be4e5bbed0678ed0658e10678e5075bd4e5bbd4e648c4e248c8c57bcd065bb1067bb5075ba4e67ba4e57394c5db8,0x5075c14e3741d06b404e6bc04c39c0106b405075bf] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101402] i else tableWord #[0xe01,0x0,0x131602,0x0,0x1601,0xb01,0xe01,0x0] i) else (if i<24 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x43841603,0x901] i else tableWord #[0xa01602,0x0,0x0,0x0,0x0,0x901,0x410902,0x1601] i)) else (if i<48 then (if i<40 then tableWord #[0x0,0x0,0x0,0x1501,0x1601,0x0,0x1501,0x0] i else tableWord #[0x0,0x0,0xb01,0x1601,0x0,0xb01,0x841002,0x1401] i) else (if i<56 then tableWord #[0xe01,0xc401,0x1501,0x0,0xc401,0xc401,0x0,0x1301] i else tableWord #[0x1401,0xb01,0xa001,0xb01,0xc401,0x8101,0x0,0x1601] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x0,0x0,0x0,0xb01,0x0,0xb1402,0x1401,0x1401] i else tableWord #[0x0,0x0,0x1601,0x0,0x0,0x1601,0x1601,0x0] i) else (if i<88 then tableWord #[0xa41402,0x2001,0x1301,0x8201,0x131602,0x421602,0x0,0x0] i else tableWord #[0x0,0x6401,0x4201,0x0,0x0,0x0,0x4101,0x1601] i)) else (if i<112 then (if i<104 then tableWord #[0x0,0x1601,0x1601,0x0,0x0,0x0,0x0,0x8401] i else tableWord #[0x8401,0x1601,0x0,0x0,0x0,0x1601,0x1601,0x4101] i) else tableWord #[0x1601,0x0,0x0,0x0,0x0,0x1601,0x0] i))))
def data6 : Nat → Nat := bookData 4 4 3 (fun i => ((fun i => tableWord #[0x507ca1c605074c5c605074c58a3500ce64a3d044e04a30e64e04a3503ce14a0ce44a34a0d014a24a0d024614a0505ce2460ce68c54604e68c5440] i) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => ((fun i => tableWord #[0x297e2fcdb9ae1fd1f] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => tableWord #[0x3498e6931bd2635a496739a4073489282fa4c5b41a2e7234ce447a4c494940e9280] i) (i/16) >>> (19*(i%16))) % 524288) (fun i => (if i<8 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0] i else tableWord #[0x0,0x0,0x0,0x0,0x0,0x0] i))
def levels : Nat → Packing
  | 6 => (14,4,5,0,0,0,0,data6)
  | 7 => (119,3,5,0,0,0,0,data7)
  | 8 => (114,2,5,0,0,0,0,data8)
  | 9 => (12,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 7 => fun h => smallSlot h 7 22 4 2 (fun i => ((fun i => tableWord #[0x100210000] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x29704000038709e40000000e08021985,0x1c4de10280ec6] i) (i/16) >>> (9*(i%16))) % 512)
  | 8 => fun h => smallSlot h 98 313 7 2 (fun i => ((fun i => tableWord #[0x180000000000e00008000001000180600,0x80404000000c0802000000000000000000,0x100000010080004000000c02000280c0600,0x81c0000018000000050000801000000009,0x1000040c09000000002028000401,0x18000402000080205008040000000000201,0x0] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x443e32c04d5e5cfa3bfd185bc62000000000f0281e000000,0x2db000e72000d3e9366c88d4294339ac9a47a21000452460,0x812c69006a4c875e496d921801b8298a6c56cd7,0xe6885c026c310d6000814a7664dd61cb2000e2a,0x26a00063f0006dc000a5a0000000000001ad000ab3000000,0xc1fc36c0d663c74e0146c63a348227416ec7e0c4ca,0xa655c8000bdae25000a1a00000000000002c000000000728,0xf670000000006be01dc35264845ed3a6fcb9a4644e000000] i else tableWord #[0x2d83c2a9359a8d00067140b957000000000e6e33da6ba13,0xa5e3d96bdf4fa670009d705400000025000afdce66e28,0xbf5d5ae051f200000020fdc70003cace7000441000951000,0x531be00062e4392e21187b9238b732402d10000006338cf,0x45d000000000a150001290000a40000000000003a9cb5e3e,0xa42c020000da0000590000004afe5f65700007722ba44000,0xa51e7304fa2f00080733aa340030001bd000000000d5c000,0xc48000000000f160000000000000005e78c5a19000000] i) else tableWord #[0xa10000c30655000e9a000cf50002f2f4600e000,0xc24ee397200044b00000000000000000047000000000086d,0xd12000e08a1c1cd00000000043d000a1763740937504a891,0xa20a22e11000c58a61000a23] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 9 => fun h => smallSlot h 122 422 7 2 (fun i => ((fun i => tableWord #[0x40000000000000000000001000000000,0x18000602018040000008000000,0x40200000000200000040001,0x2000000201000000000000000001,0x80002000040000018000001000080000,0x8000400010000200000001400,0x8000600000040200010000600008000001,0x603000080201038000602] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x26245b4050000000003d7d36000000000559000000d15b2f,0xa1c000903000221a55000000000849000c3b0004cf016,0xe4e000000b0d0007e3000762000000e3113a636,0x266def8270e2000835ee481b41000000064d000560000,0x22439d73325d0023df0000000004dae08,0x954d14dc63a0007c50006ac87008784a000e71,0xc50000c4f62c2c942d226,0xe0dccc372000000000000b16e1d4c5000000000000] i else tableWord #[0xa2b000014000000000000a6e00000000000049d000c465a0,0xa53000c4100080f00000000000000043835e000000000,0x8ae000000f48ee7000e12cee7e2000023260011818,0xc174d54df1d600000000020921a00000000000030ce06000,0x2220af000c6dbe400000000043faceb05c47000613a19,0x1714a664800000000086460b00000060c000b53,0xd950007850006d7000000859000000042000000000204c6f,0xa152456a035f000c0300043dc61bee] i) else (if i<24 then tableWord #[0xe3c000000000000a67000aed000169a33fda59cc07000000,0x26a45eb54000000232000000000843258000000335000,0xc2f0000008ece2a43e3e1252000000000000c6cb32000,0xe3400000000000000000000006b00084be5c000000,0xd8000000000000000ba6456000839c1e000aca269,0x62ea6820e000000b1c000265,0x20a00000000000000000000005f000000000ee3000000425,0xb55000e1f000a72c300009250000007e7c5469cb3b000ccd] i else tableWord #[0xa28000663000437285651f4924c00000096448a767000fd5,0x4d64014e1945cefe5a9af044e88000000000840a29000000,0x657ce5e20] i))) (i/16) >>> (12*(i%16))) % 4096)
  | 10 => fun h => smallSlot h 20 69 4 2 (fun i => ((fun i => tableWord #[0xa0c001001828004000000200000,0x14001] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xe3a5a2a488dbb0344ca52ec0034,0x19800000021000002a0000000208027800,0x20c4a35a164f30b6000000000000000000,0xe5f714800000000a00000000000559640049,0x4600002c400] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨701,10,samples,cols,[[],[32,83,116],[48,82],[80,50,116]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 7 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 12 := bandCut 8 true (by decide +kernel)
theorem band9 : CutRow book 9 0 12 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_16 : CutRow book 8 16 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_28 : CutRow book 8 28 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_40 : CutRow book 8 40 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_52 : CutRow book 8 52 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_64 : CutRow book 8 64 7 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_71 : CutRow book 8 71 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_83 : CutRow book 8 83 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_95 : CutRow book 8 95 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_107 : CutRow book 8 107 7 := bandCut 9 false (by decide +kernel)
theorem combine8_0_16 : CutRow book 8 0 16 := @joinRow book 8 0 4 12 row8_0 row8_4
theorem combine8_16_24 : CutRow book 8 16 24 := @joinRow book 8 16 12 12 row8_16 row8_28
theorem combine8_40_24 : CutRow book 8 40 24 := @joinRow book 8 40 12 12 row8_40 row8_52
theorem combine8_64_19 : CutRow book 8 64 19 := @joinRow book 8 64 7 12 row8_64 row8_71
theorem combine8_83_24 : CutRow book 8 83 24 := @joinRow book 8 83 12 12 row8_83 row8_95
theorem combine8_0_40 : CutRow book 8 0 40 := @joinRow book 8 0 16 24 combine8_0_16 combine8_16_24
theorem combine8_40_43 : CutRow book 8 40 43 := @joinRow book 8 40 24 19 combine8_40_24 combine8_64_19
theorem combine8_83_31 : CutRow book 8 83 31 := @joinRow book 8 83 24 7 combine8_83_24 row8_107
theorem combine8_0_83 : CutRow book 8 0 83 := @joinRow book 8 0 40 43 combine8_0_40 combine8_40_43
theorem combine8_0_114 : CutRow book 8 0 114 := @joinRow book 8 0 83 31 combine8_0_83 combine8_83_31
theorem band8 : CutRow book 8 0 114 := combine8_0_114
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 12 := bandCut 7 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_12 : CutRow book 7 12 4 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_16 : CutRow book 7 16 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_28 : CutRow book 7 28 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_40 : CutRow book 7 40 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_52 : CutRow book 7 52 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_64 : CutRow book 7 64 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_76 : CutRow book 7 76 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_88 : CutRow book 7 88 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_100 : CutRow book 7 100 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_112 : CutRow book 7 112 7 := bandCut 8 false (by decide +kernel)
theorem combine7_0_16 : CutRow book 7 0 16 := @joinRow book 7 0 12 4 row7_0 row7_12
theorem combine7_16_24 : CutRow book 7 16 24 := @joinRow book 7 16 12 12 row7_16 row7_28
theorem combine7_40_24 : CutRow book 7 40 24 := @joinRow book 7 40 12 12 row7_40 row7_52
theorem combine7_64_24 : CutRow book 7 64 24 := @joinRow book 7 64 12 12 row7_64 row7_76
theorem combine7_88_24 : CutRow book 7 88 24 := @joinRow book 7 88 12 12 row7_88 row7_100
theorem combine7_0_40 : CutRow book 7 0 40 := @joinRow book 7 0 16 24 combine7_0_16 combine7_16_24
theorem combine7_40_48 : CutRow book 7 40 48 := @joinRow book 7 40 24 24 combine7_40_24 combine7_64_24
theorem combine7_88_31 : CutRow book 7 88 31 := @joinRow book 7 88 24 7 combine7_88_24 row7_112
theorem combine7_0_88 : CutRow book 7 0 88 := @joinRow book 7 0 40 48 combine7_0_40 combine7_40_48
theorem combine7_0_119 : CutRow book 7 0 119 := @joinRow book 7 0 88 31 combine7_0_88 combine7_88_31
theorem band7 : CutRow book 7 0 119 := combine7_0_119
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 12 := bandCut 7 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row6_12 : CutRow book 6 12 2 := bandCut 7 false (by decide +kernel)
theorem combine6_0_14 : CutRow book 6 0 14 := @joinRow book 6 0 12 2 row6_0 row6_12
theorem band6 : CutRow book 6 0 14 := combine6_0_14
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
  · exact band7
  · exact band8
  · exact band9
  · exact band10
end B701_11
theorem h701_11 : Face true 701 11 :=
  mixedLower (g:=B701_11.book) (i:=0) (hints:=275414786820)
    (before_sound B701_11.entries B701_11.prior) B701_11.geometry B701_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h710_7 : Face true 710 7 := carry_of (swaps:=[116,100,84,49,33]) (by decide +kernel) h668_7
theorem h723_7 : Face true 723 7 := carry_of (swaps:=[146,33,114,129,50,99,32,81,64]) (by decide +kernel) h190_7
theorem h727_10 : Face true 727 10 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h695_10
theorem h730_7 : Face true 730 7 := carry_of (swaps:=[146,50,131,113,83,98,65]) (by decide +kernel) h190_7
theorem h734_11 : Face true 734 11 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h701_11
theorem h743_10 : Face true 743 10 := carry_of (swaps:=[100,82,16]) (by decide +kernel) h695_10
theorem h582_4 : Face true 582 4 := carry_of (swaps:=[146,130,50,115,98,83,32,64,16]) (by decide +kernel) h29_4
theorem h627_7 : Face true 627 7 := carry_of (swaps:=[147,131,115,98]) (by decide +kernel) h63_7
theorem h633_7 : Face true 633 7 := carry_of (swaps:=[151,135,84,66,98,16,48]) (by decide +kernel) h190_7
theorem h639_11 : Face true 639 11 := carry_of (swaps:=[151,135,101,66,16]) (by decide +kernel) h255_11
theorem h706_4 : Face true 706 4 := carry_of (swaps:=[147,50,67,130,116,99,82,16]) (by decide +kernel) h29_4
theorem h739_7 : Face true 739 7 := carry_of (swaps:=[148,32,132,115,98,80,16]) (by decide +kernel) h63_7
theorem h755_10 : Face true 755 10 := carry_of (swaps:=[151,84,98,50]) (by decide +kernel) h695_10
theorem h594_4 : Face true 594 4 := carry_of (swaps:=[147,131,67,116,66,99,82,16]) (by decide +kernel) h29_4

namespace B759_12
def entries : List (Nat × Nat) := [(165,4),(166,4),(177,4),(183,7),(198,4),(231,7),(582,4),(593,4),(594,4),(599,7),(627,7),(689,7),(695,10),(710,7),(727,10),(743,10),(755,10)]
theorem prior : Known true entries := (consFace h165_4 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h198_4 (consFace h231_7 (consFace h582_4 (consFace h593_4 (consFace h594_4 (consFace h599_7 (consFace h627_7 (consFace h689_7 (consFace h695_10 (consFace h710_7 (consFace h727_10 (consFace h743_10 (consFace h755_10 (known_down baseKnown))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 244 0x87ff0fc3f1111f8840000000000000fffff0003180000301fffff00c003c,padColumn 244 0x3ff07c1f0000f8000606010080c03696a500c3180000301dab4a00c0014),(padColumn 244 0x17c3f107ff2222097c00000000003ff00000ffc06030300ff80c03ffc00c3,padColumn 244 0x7c1f003ff0000007c08180603012a900c0365406030300d500c03aa80041),(padColumn 244 0xf8be120841f0ffff88000000007fc0000000ffcc0000cff000300cffc0303,padColumn 244 0xf83e000000f0ffff803020080c5a4040300c9a8c0000cda000300c5540102),(padColumn 244 0x0,padColumn 244 0x0),(padColumn 244 0x21042f93e2ff0f17fc000000ff80000003ff000000cff0c06003ff0300c0c,padColumn 244 0xf83e0ff0f07fc404030d5060180415a030000cea0c06000b50300408),(padColumn 244 0xffc8442084fff027fc0001ff0000000ffc00003007f3010187fc100c03030,padColumn 244 0xffc0000000fff007fd80815a3008060968100c3006a301018254100c01020),(padColumn 244 0x42108ffd08fffff813fe000000003ff00000003f8304060ff8c06010300c0,padColumn 244 0xffc00fffff802d300c0403015618060102a83040602a8c0601010080),(padColumn 244 0x84210fffff4444422001ffff007fc00000000000fff80ff6010180200f300,padColumn 244 0xfffff00000002014aa58025980201802000d15802560101802006200)] i else tableBits #[(padColumn 244 0x0,padColumn 244 0x0),(padColumn 244 0xfffff8421088888443fffe00ff8000000000003ffc0ff808060200c03cc00,padColumn 244 0xfffff00000000000012cb5002ac0200c0200c0152c015808060200c028800)] i))
def cols : List ColumnInfo := [(4,0,755,0,10),(16,0,743,0,10),(32,0,727,0,10),(64,0,695,0,10),(132,0,627,0,7),(160,0,599,0,7),(528,0,231,0,7),(576,0,183,0,7),(48,1,710,0,7),(49,0,710,0,7),(68,2,689,0,7),(70,0,689,0,7),(145,32,582,0,4),(162,4,593,0,4),(165,0,594,0,4),(177,0,582,0,4),(560,1,198,0,4),(577,16,166,0,4),(580,2,177,0,4),(594,0,165,0,4)]
def data11 : Nat → Nat := (fun i => tableWord #[0xff,0x89001a92b08] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x1ff0e6,0x518a22a2d32443c70b,0x1ff4e6,0xaa38288a1147a6b0a,0x1ff8e6,0x263a84a0e1e1ac50a] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x2fb5020e6,0x11241471305,0x33fce68e6,0x8920a1c71306,0x2ff5078e6,0x811243068706] i)
def levels : Nat → Packing
  | 9 => (3,2,5,0,0,0,0,data9)
  | 10 => (3,1,5,0,0,0,0,data10)
  | 11 => (1,0,5,0,0,0,0,data11)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun h => smallSlot h 3 11 2 2 (fun i => ((fun i => tableWord #[0x0] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x546ae9e6f4000] i) (i/16) >>> (7*(i%16))) % 128)
  | 11 => fun v => (if v=8846553226619420952 then some (2,0) else (if v=9083563835880407257 then some (1,0) else (if v=9967659315218139993 then some (2,1) else (if v=10268309250932263832 then some (0,0) else none))))
  | _ => fun _ => none
def book : Forest := ⟨759,11,samples,cols,[[],[98,84,151],[16,66,101,151],[16,82,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 8 false (by decide +kernel)
theorem band11 : CutRow book 11 0 1 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 3 := bandCut 9 false (by decide +kernel)
theorem band10 : CutRow book 10 0 3 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_2 : CutRow book 9 2 1 := bandCut 9 false (by decide +kernel)
theorem combine9_0_3 : CutRow book 9 0 3 := @joinRow book 9 0 2 1 row9_0 row9_2
theorem band9 : CutRow book 9 0 3 := combine9_0_3
theorem checked : mixedTables book 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
end B759_12
theorem h759_12 : Face true 759 12 :=
  mixedLower (g:=B759_12.book) (i:=0) (hints:=275431555364)
    (before_sound B759_12.entries B759_12.prior) B759_12.geometry B759_12.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

namespace B767_14
def entries : List (Nat × Nat) := [(6,1),(14,2),(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(166,4),(177,4),(183,7),(189,8),(198,4),(231,7),(255,11),(561,4),(582,4),(593,4),(599,7),(606,8),(627,7),(633,7),(639,11),(668,7),(673,4),(689,7),(701,11),(706,4),(710,7),(734,11),(739,7),(743,10),(755,10),(759,12)]
theorem prior : Known true entries := (consFace h6_1 (consFace h14_2 (consFace h29_4 (consFace h30_4 (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h189_8 (consFace h198_4 (consFace h231_7 (consFace h255_11 (consFace h561_4 (consFace h582_4 (consFace h593_4 (consFace h599_7 (consFace h606_8 (consFace h627_7 (consFace h633_7 (consFace h639_11 (consFace h668_7 (consFace h673_4 (consFace h689_7 (consFace h701_11 (consFace h706_4 (consFace h710_7 (consFace h734_11 (consFace h739_7 (consFace h743_10 (consFace h755_10 (consFace h759_12 (known_down baseKnown)))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0xf07fc210421ffe1043e0000000000000001fffffc00000000060c00000600fffffe0080600c003c0,padColumn 320 0xf07fc000000ffe0001e00c0300200806006d2b55400803006060c00000600ed56940080600c00140),(padColumn 320 0xff87c4208420822fffe0000000000001ffe00000000000ffe0030060601ffc0180603001ffc00c03,padColumn 320 0xff87c0000000000fffe0100c00c0300955200600c0300465a0030060601aa8018060300155800401),(padColumn 320 0x10887e013ff17ff084200000000007fe000000000007ffffe18000019fe00006018007ffffc0300f,padColumn 320 0x3e003ff07ff0000060100100c5a2008018030042599a418000019b400006018004acaa401006),(padColumn 320 0xfff8084fc84f84413fe0000000000000000000003fffff00060c018000003018001ffffe0100003c,padColumn 320 0xfff8000fc00f80003fe1806006010010030060042a9da600860c018000003018001aab5201000018),(padColumn 320 0x2110bff201f209ffc8400000001ff800000001fffff800000000061fe180c0007ffff8080600c0f0,padColumn 320 0x3ff001f001ffc0020080181a50600c0080aa956008030000061d4180c00016a55008060040a0),(padColumn 320 0x42213ffffe0411fffe800000ffe00000001ffe000000000018003fe6020303ff8200c03018030300,padColumn 320 0x3ffffe0001fffe0c0100ab4600803012d4080180300c180035460203012a8200c03018010200),(padColumn 320 0x84023ffffffffe02111ffc0000000001ffe00000000000001ff018080c1ffc600c0300c020300c00,padColumn 320 0x3ffffffffe000016a60060080300aac300300600c010155018080c0554600c0300c020100800),(padColumn 320 0xffffd08410802084200003ffffe007fe0000000000000000001ffff01fec0080300c0100400f3000,padColumn 320 0xffffc00000000000001002a554b0025cc00400c018010020001a8ab004ac0080300c010040062000)] i else tableBits #[(padColumn 320 0x0,padColumn 320 0x0),(padColumn 320 0x844210821084108001fffff001ff80000000000000000001fffe01ff010030040100601803cc000,padColumn 320 0x9595a8005ac0100180100200600c00aa56002b01003004010060180288000)] i))
def cols : List ColumnInfo := [(8,0,759,0,12),(128,0,639,0,11),(512,0,255,0,11),(33,0,734,0,11),(66,0,701,0,11),(12,0,755,0,10),(24,0,743,0,10),(129,32,606,0,8),(514,64,189,0,8),(578,0,189,0,8),(20,8,739,0,7),(28,0,739,0,7),(134,0,633,0,7),(140,0,627,0,7),(168,0,599,0,7),(536,0,231,0,7),(584,0,183,0,7),(672,0,95,0,7),(704,0,63,0,7),(57,0,710,0,7),(76,2,689,0,7),(78,0,689,0,7),(99,0,668,0,7),(52,9,706,0,4),(60,1,706,0,4),(92,2,673,0,4),(94,0,673,0,4),(170,4,593,0,4),(185,0,582,0,4),(202,4,561,0,4),(553,16,198,0,4),(585,16,166,0,4),(590,0,177,0,4),(646,64,57,0,4),(657,32,78,0,4),(689,0,78,0,4),(705,32,30,0,4),(708,2,57,0,4),(710,0,57,0,4),(738,0,29,0,4),(216,544,6,1,2),(240,513,14,0,2)]
def data13 : Nat → Nat := (fun i => tableWord #[0x1ff,0x421460c407] i)
def data12 : Nat → Nat := (fun i => tableWord #[0x3ff482,0x2e0c20b0e20607,0x3ff4e2,0x85180c40a3219408,0x3ff502,0xa0c60a2219407,0x3ff507,0x25022818c0a1c408] i)
def data11 : Nat → Nat := bookData 2 2 3 (fun i => ((fun i => tableWord #[0x5075024e2482] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x3ffefffef7fffddf7] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => tableWord #[0x504aa93d141e9a44bd2756922941e5a509d244a9425408ba4e8d236293a14089a460,0x522be93db492ca4f6524b272594a2aa495] i) (i/16) >>> (17*(i%16))) % 131072) (fun i => (if i<16 then (if i<8 then tableWord #[0x506c1c20bc3c407,0xb15c442c3861e1d08,0x410d120bc485c31b1f09,0x15c1c2c3c40b06,0x1241c4c30b05,0xd2605c48142c31d08,0x4212810dc685c425c31d0a,0x4612c3c41f0d06] i else tableWord #[0x1342c4c30d05,0xc609122641c485c31d09,0x828512c4c3462607,0x1d82c685c441c32008,0x13c445c31b1206,0x410b121d0d42c3c48609,0x860a0d0b1b1f06,0x1d1f81420d0f1285c4c3460b] i) else tableWord #[0x21c30b260d1b06,0xd12261b04,0x23261d1f418246c4c3850a,0xf0b46c31d05,0x410d12261d05,0x12c3462604,0xc3121541261b06,0xd12c645c32606] i))
def data10 : Nat → Nat := bookData 3 5 5 (fun i => ((fun i => tableWord #[0x522507d27502d245025075025245024e4502d284e2d244e25284e25244e25024e2d27482d23482507482502482527482,0xd22507] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xbffff7dffe7fd7fb7fbf7f7bdf7bfb9ffff3dfbefbfeb9f7,0xeff] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x54829151ce352738d41ce3d4828350ce0d42183508c054928b49c61d4408748c8152718541c414e408750c00,0x5442b951cadd2763350d2b9492a941d8a1492a9510a95482a351d67d4751f510a7d4349b508c6d4741749065,0x5246bd5120cd4879941dc3949689525a25442c351d4f] i) (i/16) >>> (22*(i%16))) % 4194304) (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xa0f0f880a04,0x361f02,0x1d1487c421b05,0x483e1b03,0x4c3e1b03,0x4c1b02,0x161b02,0x5054361f04] i else tableWord #[0x2c3e1b03,0x34161e03,0x543a1e03,0x2839412064361f06,0xc8e1864361f05,0x38361f03,0x2c361f03,0x120603c1d04] i) else (if i<24 then tableWord #[0x3c2602,0x4c1b02,0x8c1a1b03,0x1a1b02,0x3c2602,0x1a1b02,0x90981a1b04,0x3c2602] i else tableWord #[0x7c181e03,0xe080b048382606,0x440743fc3a3614422208,0x3c2602,0x70c141d03,0x3a2602,0x1205c3c2604,0x5054361f04] i)) else tableWord #[0xe187c222604,0x461f02,0x201a02,0x3a1f02,0x8074341f04,0x4c1d02,0x3c4c2303,0x3a2602] i))
def data9 : Nat → Nat := (fun i => tableWord #[0x1e6b5074e4502482,0x280981f03,0x15f7d63549507482,0x0,0x157fd67549507482,0x2701] i)
def levels : Nat → Packing
  | 9 => (3,4,6,0,0,0,0,data9)
  | 10 => (40,3,6,0,0,0,0,data10)
  | 11 => (24,2,6,0,0,0,0,data11)
  | 12 => (4,1,6,0,0,0,0,data12)
  | 13 => (1,0,6,0,0,0,0,data13)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=9173731893560143937 then some (1,0) else (if v=9817994258469878493 then some (0,0) else (if v=11282382653361050149 then some (2,0) else (if v=13146079884629819533 then some (2,1) else none))))
  | 11 => fun h => smallSlot h 24 76 6 1 (fun i => ((fun i => tableWord #[0x40400a000000006040010000000,0x22c0010604004] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xf0021e0a08400000b7094001026542068d88,0xc2dc564299002180740042903000229280004800,0x634000000019f96000a443887003819109c09ba7,0x30cd3e9a0000085d8900000000008141100000,0x84ea1219a5d3b1f00000003c30039b] i) (i/16) >>> (10*(i%16))) % 1024)
  | 12 => fun h => smallSlot h 25 92 5 1 (fun i => ((fun i => tableWord #[0x8000000000000000800400000,0x2000000000000] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xac0000003aa004528d0200,0xa403d4a00088028400005180000,0xda380050f981469000000026b600000,0x7122c00004981c0190000000000000025400,0x4125e00002140000000031d67000000009,0x157] i) (i/16) >>> (9*(i%16))) % 512)
  | 13 => fun h => smallSlot h 3 11 3 1 (fun i => ((fun i => tableWord #[0x0] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x480310002da30128064] i) (i/16) >>> (7*(i%16))) % 128)
  | _ => fun _ => none
def book : Forest := ⟨767,13,samples,cols,[[],[16,66,101,151]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 1 := bandCut 9 false (by decide +kernel)
theorem band13 : CutRow book 13 0 1 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 4 := bandCut 10 false (by decide +kernel)
theorem band12 : CutRow book 12 0 4 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_13 : CutRow book 11 13 11 := bandCut 11 true (by decide +kernel)
theorem combine11_0_13 : CutRow book 11 0 13 := @joinRow book 11 0 1 12 row11_0 row11_1
theorem combine11_0_24 : CutRow book 11 0 24 := @joinRow book 11 0 13 11 combine11_0_13 row11_13
theorem band11 : CutRow book 11 0 24 := combine11_0_24
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_1 : CutRow book 10 1 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_13 : CutRow book 10 13 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_25 : CutRow book 10 25 9 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_34 : CutRow book 10 34 6 := bandCut 11 false (by decide +kernel)
theorem combine10_0_13 : CutRow book 10 0 13 := @joinRow book 10 0 1 12 row10_0 row10_1
theorem combine10_13_21 : CutRow book 10 13 21 := @joinRow book 10 13 12 9 row10_13 row10_25
theorem combine10_0_34 : CutRow book 10 0 34 := @joinRow book 10 0 13 21 combine10_0_13 combine10_13_21
theorem combine10_0_40 : CutRow book 10 0 40 := @joinRow book 10 0 34 6 combine10_0_34 row10_34
theorem band10 : CutRow book 10 0 40 := combine10_0_40
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_1 : CutRow book 9 1 2 := bandCut 10 false (by decide +kernel)
theorem combine9_0_3 : CutRow book 9 0 3 := @joinRow book 9 0 1 2 row9_0 row9_1
theorem band9 : CutRow book 9 0 3 := combine9_0_3
theorem checked : mixedTables book 13 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
  · exact band13
end B767_14
theorem h767_14 : Face true 767 14 :=
  mixedLower (g:=B767_14.book) (i:=0) (hints:=275431563556)
    (before_sound B767_14.entries B767_14.prior) B767_14.geometry B767_14.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h881_8 : Face true 881 8 := carry_of (swaps:=[151,84,131,98]) (by decide +kernel) h189_8
theorem h895_13 : Face true 895 13 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h511_13
theorem h934_7 : Face true 934 7 := carry_of (swaps:=[81,82,146,117,129,98,50,65]) (by decide +kernel) h190_7
theorem h956_10 : Face true 956 10 := carry_of (swaps:=[129,82,97,48]) (by decide +kernel) h695_10
theorem h960_4 : Face true 960 4 := carry_of (swaps:=[66,32,50,144,132,115,98,80,16]) (by decide +kernel) h29_4
theorem h977_7 : Face true 977 7 := carry_of (swaps:=[82,33,114,149,49,131,98,16,64]) (by decide +kernel) h190_7
theorem h984_7 : Face true 984 7 := carry_of (swaps:=[82,113,149,67,130,97]) (by decide +kernel) h190_7
theorem h992_7 : Face true 992 7 := carry_of (swaps:=[67,132,99,82]) (by decide +kernel) h668_7
theorem h998_11 : Face true 998 11 := carry_of (swaps:=[67,132,99,82,16]) (by decide +kernel) h701_11
theorem h1009_11 : Face true 1009 11 := carry_of (swaps:=[151,84,131,98]) (by decide +kernel) h701_11
theorem h1015_14 : Face true 1015 14 := carry_of (swaps:=[100,131,82,16]) (by decide +kernel) h767_14
theorem h1021_14 : Face true 1021 14 := carry_of (swaps:=[82,129,48]) (by decide +kernel) h767_14
theorem h1022_14 : Face true 1022 14 := carry_of (swaps:=[151,98,82,16,66,49,128]) (by decide +kernel) h767_14

namespace B1023_16
def entries : List (Nat × Nat) := [(6,1),(12,1),(14,2),(17,1),(24,1),(28,2),(29,4),(30,4),(33,1),(49,2),(57,4),(63,7),(66,1),(70,2),(78,4),(95,7),(132,1),(164,2),(165,4),(166,4),(189,8),(198,4),(231,7),(255,11),(305,4),(326,4),(352,2),(353,4),(354,4),(359,7),(366,7),(371,7),(377,7),(383,11),(486,8),(503,11),(511,13),(528,1),(576,1),(593,4),(599,7),(606,8),(657,4),(668,7),(679,7),(685,7),(689,7),(695,10),(701,11),(710,7),(723,7),(727,10),(730,7),(734,11),(743,10),(767,14),(881,8),(895,13),(934,7),(956,10),(960,4),(977,7),(984,7),(992,7),(998,11),(1009,11),(1015,14),(1021,14),(1022,14)]
theorem prior : Known true entries := (consFace h6_1 (consFace h12_1 (consFace h14_2 (consFace h17_1 (consFace h24_1 (consFace h28_2 (consFace h29_4 (consFace h30_4 (consFace h33_1 (consFace h49_2 (consFace h57_4 (consFace h63_7 (consFace h66_1 (consFace h70_2 (consFace h78_4 (consFace h95_7 (consFace h132_1 (consFace h164_2 (consFace h165_4 (consFace h166_4 (consFace h189_8 (consFace h198_4 (consFace h231_7 (consFace h255_11 (consFace h305_4 (consFace h326_4 (consFace h352_2 (consFace h353_4 (consFace h354_4 (consFace h359_7 (consFace h366_7 (consFace h371_7 (consFace h377_7 (consFace h383_11 (consFace h486_8 (consFace h503_11 (consFace h511_13 (consFace h528_1 (consFace h576_1 (consFace h593_4 (consFace h599_7 (consFace h606_8 (consFace h657_4 (consFace h668_7 (consFace h679_7 (consFace h685_7 (consFace h689_7 (consFace h695_10 (consFace h701_11 (consFace h710_7 (consFace h723_7 (consFace h727_10 (consFace h730_7 (consFace h734_11 (consFace h743_10 (consFace h767_14 (consFace h881_8 (consFace h895_13 (consFace h934_7 (consFace h956_10 (consFace h960_4 (consFace h977_7 (consFace h984_7 (consFace h992_7 (consFace h998_11 (consFace h1009_11 (consFace h1015_14 (consFace h1021_14 (consFace h1022_14 (known_down baseKnown))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0x1ffffff80000000000000180c060000001801ffffff800801800c0003c0,padColumn 320 0x800c00c00c00400400c006e95aaa80040060030000180c060000001801dd56a5000801800c000140),(padColumn 320 0x3ffe0000000000001fff00c000001801806007ff8018018030007ffc000c03,padColumn 320 0x100100300180180135520030018018008b2d00c000001801806007550018018030005558000401),(padColumn 320 0x3ffc0000000000003ffffff030060300000019ff8000060060007fffffc00300f,padColumn 320 0x60060040020062b4400800c00600214b34d2030060300000019ad00000600600052b2aa4001006),(padColumn 320 0x7fffffe0000c0180c06006000000060180007fffff801000003c,padColumn 320 0x1801801800c0080020030030008554eb4c0040c0180c06006000000060180006aaad48010000018),(padColumn 320 0x3ffc000000000ffffffc0000003006000000187fe060180007fffff802006000c0f0,padColumn 320 0x600200200301d280c00c00405552ab00100183006000000185d40601800015a95500200600040a0),(padColumn 320 0x8000000003ffc000000001fff0000000000000ffc8030001ff860080607ff80800c00c0183030300,padColumn 320 0x800c0040256830010030116a01000c0060060aa88030001550600806022a80800c00c0181010200),(padColumn 320 0x7fffffc000000000003ffe0000000000000000003ffffc8060080307ff8600300300300200f00c00,padColumn 320 0x1aa56a4800c00400600aac1800600300180080002d52a88060080300aa8600300300300200500800),(padColumn 320 0x3fffffc003ffc000000000000000000000300003ffff901ff9800800c00c004004000f3000,padColumn 320 0x3001001a95a948014b8c002001800c0020010000300002d4aa900529800800c00c00400400062000)] i else tableBits #[(padColumn 320 0xfffc0000000000000000000000000000000000fffffc030080600c02001003003001801803c00000,padColumn 320 0xe55a0030010030018010004006003000c006005552ac030080600c02001003003001801802800000),(padColumn 320 0x3fffffc003ffc0000000000000000000000c00007ffff007ff0040060040040060060003cc000,padColumn 320 0x400295a56a0022d60020018008004003001800c00005552b0022b004006004004006006000288000)] i))
def cols : List ColumnInfo := [(1,0,1022,0,14),(2,0,1021,0,14),(8,0,1015,0,14),(256,0,767,0,14),(128,0,895,0,13),(512,0,511,0,13),(520,0,503,0,11),(640,0,383,0,11),(768,0,255,0,11),(14,0,1009,0,11),(25,0,998,0,11),(289,0,734,0,11),(322,0,701,0,11),(67,0,956,0,10),(280,0,743,0,10),(296,0,727,0,10),(328,0,695,0,10),(138,4,881,0,8),(142,0,881,0,8),(385,32,606,0,8),(521,16,486,0,8),(537,0,486,0,8),(770,64,189,0,8),(39,0,984,0,7),(46,0,977,0,7),(89,0,934,0,7),(293,0,730,0,7),(300,0,723,0,7),(338,0,685,0,7),(344,0,679,0,7),(424,0,599,0,7),(646,0,377,0,7),(652,0,371,0,7),(657,0,366,0,7),(664,0,359,0,7),(792,0,231,0,7),(928,0,95,0,7),(960,0,63,0,7),(23,8,992,0,7),(31,0,992,0,7),(99,256,668,0,7),(312,1,710,0,7),(313,0,710,0,7),(332,2,689,0,7),(334,0,689,0,7),(355,0,668,0,7),(63,0,960,0,4),(366,0,657,0,4),(426,4,593,0,4),(430,0,593,0,4),(653,16,354,0,4),(666,4,353,0,4),(669,0,354,0,4),(670,0,353,0,4),(681,16,326,0,4),(714,4,305,0,4),(794,64,165,0,4),(809,16,198,0,4),(841,16,166,0,4),(858,0,165,0,4),(902,64,57,0,4),(913,32,78,0,4),(930,64,29,0,4),(961,32,30,0,4),(966,0,57,0,4),(994,0,29,0,4),(266,116,0,641,2),(299,80,132,512,2),(344,546,0,133,2),(403,36,576,8,2),(410,36,576,1,2),(450,52,0,521,2),(456,52,0,515,2),(458,36,528,1,2),(465,544,14,0,2),(472,516,33,2,2),(472,544,6,1,2),(496,513,14,0,2),(553,84,0,386,2),(651,20,352,0,2),(779,80,164,0,2),(780,208,0,35,2),(801,208,0,14,2),(803,80,132,8,2),(808,84,0,131,2),(808,208,0,7,2),(810,80,132,1,2),(812,192,17,2,2),(816,69,0,138,2),(833,50,0,140,2),(899,96,28,0,2),(902,96,24,1,2),(905,48,70,0,2),(906,68,49,0,2),(908,48,66,1,2),(913,96,12,2,2),(914,96,12,1,2),(920,68,33,2,2),(960,50,0,13,2),(961,48,6,8,2),(968,48,6,1,2)]
def data15 : Nat → Nat := (fun i => tableWord #[0x3ff,0x2020c205122c50c0a] i)
def data14 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x7ff482,0x827848b8c1483090a09,0x7ff4a2,0x7858a8c13090b07,0x7ff4e2,0x4111280838a8c078b090a,0x7ff522,0x5118a8c8083078b0909] i else tableWord #[0x7ff527,0x80828183898b8a8c0709] i))
def data13 : Nat → Nat := bookData 2 2 3 (fun i => ((fun i => tableWord #[0x5224e24a2482] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0xfffdffff7bffffbbf7] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0xd494ea3a75112a9295474a9115388ba8e8d4546a1b151d0a8a85222261112889a860,0x4e4aa625549e8a4b44e5a262d351d7a8abd445a93cd4967a92ad4556a2295254a446,0x1a8b7d44ba725d496ca496d49aea25549eaa495] i) (i/16) >>> (17*(i%16))) % 131072) (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc1824158b08e30282708,0x18c8a429161105,0x18b4b429181105,0x62c2d8c8560c221407,0x8522c221606c24261408,0x1090985b178c8560c221409,0x218bc6044282706,0x16c6050262705] i else tableWord #[0x3178c0a60c222706,0x3158c09a1e161106,0x6282816c6216161107,0x109858502d8ac621c221309,0xe140b62a130bc621422130a,0x2d8c09c26161406,0x109858502d8ac6614221309,0x26140b06d0b8ac621e130b0a] i) else (if i<24 then tableWord #[0x26140b603078ac601f16110a,0x42426140b603078ac601f16110b,0x4c2c28c5e30281207,0x502d8ac641c261207,0x26140b603078ac601f16120a,0x23158c88a4e128b07,0x13c060f1509c601f161109,0x985b178c08e0e121408] i else tableWord #[0x502d8ac6416121307,0x42426140b603078ac601f16110b,0x12c11098b6128b0a05a4ead88a4e148c0e,0x2122413a4c298c1b42916110a,0x5848398509c238c49a2e12140b,0x4c2c2784e2e158cc1a1c22140b,0x221483a20261b0e85a169684c4d148c0e,0x3850443d44426178c4525022130c] i)) else (if i<40 then tableWord #[0x22140a85836224a63026854542e123d0e,0x140b62a130bc621c221309,0x30b8c45044261b06,0x3158c42844261b06,0x2616100ca22140ae0f178c03c2514350e,0x8848281645883158c8881e12130c,0x130b425158bc660c221409,0x8f0b0a8798cc1844282009] i else tableWord #[0xa0584e3cc6045162008] i)))
def data12 : Nat → Nat := bookData 3 5 5 (fun i => ((fun i => tableWord #[0xd494a2d444a25474a25274a24e44a24c44a24e24a2d45482d434825224824c24825494a25224a25474825454824a2482,0x5244e25244a25254824e54824c5482d445225255224e4522d454e25254e25224e2] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xffdf5ff3ffb7f9ffefdfbf77fbdfdff6ffd737feedcfde7fdfcb,0xffffdfffdfff7effdffffbfbff] i) (i/16) >>> (13*(i%16))) % 8192) (fun i => ((fun i => tableWord #[0x52549b524e5d45395290a5d69403524e0d66403518e0525301314c04c428359c8452518f58c42d6008529000,0x96a5b351d8b16a5ac5a96ad6440f5a509d493a7591095695a149d4752551d395474c551f59906d6541b514e6,0x547859315e6525795499e05675d751db4d624d149dd316a5cd5a5725496c7514f05254c159d6f5675bb5a56d,0x547829311e35247a5311e94c5a1f59e58d4786359a585279e35a657d4985f59a57d4685d5a6575258df51e16,0x56693b59e59d4786759a595478675a64bd4982f59a4bd4682d5a64b527b2d39acb524aaf59e4ad4782959e4a,0xd67ba949eea16aba939af8526bdd49ef656595549675d6594d49673d649475161a56783d5920f56493d5a64e,0xd46be549aeb] i) (i/16) >>> (22*(i%16))) % 4194304) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x21124d1403,0xc24140442904,0x38be30110502605,0xe281405b8c8451306,0x38ae32850441305,0xa2e116311404,0xc298c8449304,0x30a458964509318e1107] i else tableWord #[0xa2c114582704,0x24c11c289604,0x25a8b045141902706,0x30a458960468b1891407,0x62e8c8451404,0x2d0445a44c2705,0x28c450112582705,0x30a058241241462e1107] i) else (if i<24 then tableWord #[0x11050160904c09d1307,0xc2a162581124e1406,0x30a24c1125a1405,0x1ad65a1162e278518c07,0x1930578c8283662c1107,0x19304b8c0d98b8241407,0xe0f8be31870441406,0x50160b43f04c2706] i else tableWord #[0x30b258122521305,0x9425b0b0f4130fc1107,0x9425811c2c121121307,0x85896c2c111889406,0x44c270b49605c1d06,0x160b0110682205,0xe3309c2d16a5087a283d044130a,0x87050160ac1c0cc3704c1b09] i)) else (if i<48 then (if i<40 then tableWord #[0x140581d0f43f0441307,0x3d05b8c044130c41407,0x8706c140581d0f43f0441309,0x501662c4844e1106,0x501607c201111306,0xa2c4884d1104,0x50160a83ce301f04c2008,0x4c160f0400a3830442108] i else tableWord #[0xe2c1305b8cc268ae0c07044140a,0x5016090484449306,0xa2c484449304,0x13058280f011e2f8c0502009,0x9309e8b259141646407,0x270b02d450961485607,0x62e118509604,0x2dc268c24d1405] i) else (if i<56 then tableWord #[0xa2c37a311124d2706,0x3e10455c28938443607,0x9c3e10455c2a1124c3608,0x44130502449c3e06,0x2110781409c960d83007,0x960e8110528b49c3607,0x2112583e1578cc28274503009,0x503e10455c28934443608] i else tableWord #[0x1109e140db092583907,0x4449349c3604,0x9c3e10456c28934443908,0x2a8458c8522705,0x6284c2503dc2d8c84e1108,0xfc6084c94c2c3306,0x220942584a04,0x4b1301d0fc16a2a8c4451309] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x1072201b2511144c9607,0xa281b12c4c0743da528c445130a,0xa304cc2c3b0f81ba2896445130a,0x1160883a15060184948443d09,0x851160b41104c5406,0x458130e8541806121c940443d0a,0x1160883a15060186112503d09,0x881404413a291606] i else tableWord #[0x8a1306c968443d06,0x1160e85418061088112503d09,0x1160885418061e30948443d09,0x50230e38c4443d06,0x441306c96c243d06,0x38e301b4443d05,0x9604c220e05718061e301b4443d0b,0x84e110603d04] i) else (if i<88 then tableWord #[0x2f844940603d05,0x9e110603f04,0x18a0603f03,0x6c110fc3104,0x50230d4380ed130c83408,0x200f03ee301104f090903209,0x24c2a0504704,0x200f05b0b0938443407] i else tableWord #[0x27844141144805,0x102110f02062c3306,0x83a104449349cad0dc41450960a,0x1102583089d270dd1407,0x4404224c410dc9606,0x6444c9603,0x3e0b4371305744c9607,0x1843b15c362591306] i)) else tableWord #[0x4583a18454180220f49408,0x3b444310fc9605] i)))
def data11 : Nat → Nat := bookData 4 5 5 (fun i => ((fun i => tableWord #[0x5674c44a216a4c44a24c45224a2525d434824e5d43482d475254825474c5482d455224824c5522482d454c24825254a24824c54a24824c5d434824a44c24824c44a24824a44a2482,0x5264e44a2d674c44a25474c44a25274c44a24c44e24a24e6525482d474c5482d475244a2d664e44a25274e44a24e64e44a25244e44a2d474c44a2] i) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => ((fun i => tableWord #[0xe7dfbd7ebdf37fafdeefbf76f3fbafeefdbdf6fbdbabdff8bdf2fbcb,0x3b7f9ffebffefeeffbffafef7efdfd7fcffeb7fedbe5ff8ffedfb] i) (i/16) >>> (14*(i%16))) % 16384) (fun i => ((fun i => tableWord #[0x58758f59d8ad835a759908d8851d49527d69419624e6d863175a4a4d49213620634c510931441d6608351800,0x16a64b51e715676436264f5878bb6260d5254b761d6cd865b149decd895af6196b5895ad495cbd8868f61d63,0x569aea62b9916aae762758d49de162758524ce139aec526baf62303527b8d49ed7d69adb59d95d4765262a93,0xd47f73526bb589eef5a6b0d89e6b5a6ba] i) (i/16) >>> (22*(i%16))) % 4194304) (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x5a01,0x5001,0x5d01,0x5001,0x30a18bc2265b139ad06,0x3105c02,0x2e05d02,0x3185d02] i else tableWord #[0x2d04302,0x2d05f02,0x10a04902,0x3278444b61404,0x3005302,0x229a2c9349304,0x149c8883603,0xb178290899604] i) else (if i<24 then tableWord #[0x8c178c99ad04,0x5864ccb1ad04,0x64e0883603,0x124c983603,0x6581803603,0x32c0e81b03004,0x64d0883603,0x32c0db0483904] i else tableWord #[0x844c983603,0x2504b04c03,0x1344b04c03,0x1040c83103,0xa222504b51304,0x8707e44489a9605,0xad2510883d04,0x96c604e03] i)) else (if i<48 then (if i<40 then tableWord #[0x552501703d04,0x12581983d03,0x29602615c0883d05,0xa20fc2085d04,0x40c15849a1404,0x327038d699604,0x1ad0c80b30a19605,0xcb03a02] i else tableWord #[0x1b99602,0xa1c2d05d03,0x1f19602,0xca19602,0x7c1330999604,0xec2784103,0x12501dc9603,0x1883f02] i) else tableWord #[0x961301d83e04,0xc42f03f03,0x3b09815e89a9605,0xec3083e03,0xb60ec1f05d04,0xe01ec9403] i)))
def data10 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x4af7da85874c5d43482,0x5801,0x6af7d885274c5d43482,0x0,0x79775274e6525d43482,0x19601,0x537f5a716a5274c44a2,0x4101] i else tableWord #[0x43ff5ac16a5274c44a2,0x0,0x61ffd89d695474c44a2,0x5e03f02] i))
def levels : Nat → Packing
  | 10 => (6,5,7,0,0,0,0,data10)
  | 11 => (54,4,7,0,0,0,0,data11)
  | 12 => (98,3,7,0,0,0,0,data12)
  | 13 => (41,2,7,0,0,0,0,data13)
  | 14 => (5,1,7,0,0,0,0,data14)
  | 15 => (1,0,7,0,0,0,0,data15)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun h => smallSlot h 4 13 3 3 (fun i => ((fun i => tableWord #[0x55] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x70d0200ecf158d8c410018800] i) (i/16) >>> (9*(i%16))) % 512)
  | 12 => fun h => smallSlot h 64 246 6 3 (fun i => ((fun i => tableWord #[0x1000100000000010000000000000000,0x200000000000000,0x10000000000000001020000000000,0x20200000001000200] i) (i/16) >>> (8*(i%16))) % 256) (fun i => ((fun i => (if i<8 then tableWord #[0x540600000000040f01e000a9100062663600000083201c,0xe1a000000e204148adc2306500000000000080764c000000,0xa09000000000e31000000a3402a897000e0d00005b,0x811000000000000e182280000000000c6000a12890c81001,0x65d00000000000000000041b000000000000000000000,0xa74000000000000000e5c000d8a00062e82106b,0x852000000000000000000000408000c0a000000000,0xe17000000000ae100000000041600061900026f000000] i else tableWord #[0x82f60ea0b0000006718d1000e1349b000000000000cab224,0xa03000000000000e2b000ccc000000227000,0x494000ed062966c000000000000235a10000c25000000,0x802815d410000000008330004e0000000000e66000,0x5a000000000000000000cf6a0c02d000000000,0xa6d0000002ac00000000000000000000000000061f000,0x32a81d804000c86000000000e2c000000000000,0xe22000000a300c8000] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 13 => fun h => smallSlot h 105 337 7 3 (fun i => ((fun i => tableWord #[0x201008000000000000000008040001,0x200000040000000040400000000000,0x180000050000000008000001,0x10040001038040002000000200000040403,0x402010200a00018040007058000001,0x100808060001c0004000040205000000000,0x1000080001000000400] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x9a016a887d16000375c00000001d800000000004300038c4000,0x2eadc2e000000000000000028a427b94c0000000001de2,0x10d5067c24818a6400000000030d67e18048a21230d0c0000,0xc23000162403d0000002a93dd20000010000c3420c000304a000,0x470c2500005cc00051300019aa8e3aa09d7781ee2e40e9626000,0x3054420f4600000000000288003d1adbfc61318661fad6,0x2806836e22002a03e000000000000005ec07b116802136,0xa118000000000ea6952c00044a457f0fee1d2be297cacc000000] i else tableWord #[0x608a11c00093ee04800000005b0000722805933,0x95bd6afb1400096cb0b400183200000000000008dca81938c2b8,0xe628001d640004a3c1380014b040e000203a1b00000001bc399a,0x80a867f016c4d4d6903000000026e02f00001ce98804c6510000,0xddbcfab9480789c000307085800003770a745ded370f8000000,0x8d780000000000006107e3240e000000129e5308dac048001946,0xf8e106a20280894830f04b00008c632c4a8840dc278000ab0819,0x16cc0000000000000000cc0000000000000000044250a8000] i) else tableWord #[0x2853422c2bc55f21f5d340a2d550ac02fcec80030aa027,0xb4303800000bda1656e0000c49202800000182b0d88000001440,0x184270a2dba166aaa000c142059a5a0002098000000e0d,0x225c6f4860037c4382fe0721b2a280003a7fc1b660b690000000,0xe290000000000c2fccb4001810000000322a4172c4709800110b,0x0] i)) (i/16) >>> (13*(i%16))) % 8192)
  | 14 => fun h => smallSlot h 42 136 6 3 (fun i => ((fun i => tableWord #[0x1000202000003050002000000,0x302020000000005000301030000,0x4010007000004010300] i) (i/16) >>> (8*(i%16))) % 256) (fun i => ((fun i => (if i<8 then tableWord #[0xe02a222e02e161d484028206e0fcd7000,0xd5d4cef42a89793e1bae3410000204727a242c5000000,0xc174a0ecb000000000452000000000e8300000000000001f,0x2d2186821000000c88000682da840bc0c000f1e203398,0x525000a1681c4dd000000000706c12685405e136c2,0x486000407000d5e008000b5c000000000000215000582000,0xe9d20aa26a1a4620000000002a1223000a0980d697984000,0x611829692000000000a57c20ee6e1900000061ee9c0cac0e] i else tableWord #[0x45e027a142dca25418001] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 15 => fun h => smallSlot h 7 24 3 3 (fun i => ((fun i => tableWord #[0x8000] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x24f171903650012754f4e2c0004f0800015c,0xb0200ed8000000] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨1023,15,samples,cols,[[],[98,131,84,151],[16,66,101,151],[16,82,131,100],[48,129,98,16,66,84,151],[48,129,82],[128,49,100],[128,49,66,16,82,98,151]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row15_0 : CutRow book 15 0 1 := bandCut 10 false (by decide +kernel)
theorem band15 : CutRow book 15 0 1 := row15_0
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 5 := bandCut 11 false (by decide +kernel)
theorem band14 : CutRow book 14 0 5 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_1 : CutRow book 13 1 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_13 : CutRow book 13 13 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_25 : CutRow book 13 25 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_26 : CutRow book 13 26 12 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_38 : CutRow book 13 38 3 := bandCut 12 false (by decide +kernel)
theorem combine13_0_13 : CutRow book 13 0 13 := @joinRow book 13 0 1 12 row13_0 row13_1
theorem combine13_13_13 : CutRow book 13 13 13 := @joinRow book 13 13 12 1 row13_13 row13_25
theorem combine13_26_15 : CutRow book 13 26 15 := @joinRow book 13 26 12 3 row13_26 row13_38
theorem combine13_0_26 : CutRow book 13 0 26 := @joinRow book 13 0 13 13 combine13_0_13 combine13_13_13
theorem combine13_0_41 : CutRow book 13 0 41 := @joinRow book 13 0 26 15 combine13_0_26 combine13_26_15
theorem band13 : CutRow book 13 0 41 := combine13_0_41
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 5 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_5 : CutRow book 12 5 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_17 : CutRow book 12 17 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_29 : CutRow book 12 29 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_41 : CutRow book 12 41 3 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_44 : CutRow book 12 44 12 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_56 : CutRow book 12 56 12 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_68 : CutRow book 12 68 12 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_80 : CutRow book 12 80 10 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_90 : CutRow book 12 90 8 := bandCut 13 true (by decide +kernel)
theorem combine12_0_17 : CutRow book 12 0 17 := @joinRow book 12 0 5 12 row12_0 row12_5
theorem combine12_17_24 : CutRow book 12 17 24 := @joinRow book 12 17 12 12 row12_17 row12_29
theorem combine12_41_15 : CutRow book 12 41 15 := @joinRow book 12 41 3 12 row12_41 row12_44
theorem combine12_56_24 : CutRow book 12 56 24 := @joinRow book 12 56 12 12 row12_56 row12_68
theorem combine12_80_18 : CutRow book 12 80 18 := @joinRow book 12 80 10 8 row12_80 row12_90
theorem combine12_0_41 : CutRow book 12 0 41 := @joinRow book 12 0 17 24 combine12_0_17 combine12_17_24
theorem combine12_41_39 : CutRow book 12 41 39 := @joinRow book 12 41 15 24 combine12_41_15 combine12_56_24
theorem combine12_0_80 : CutRow book 12 0 80 := @joinRow book 12 0 41 39 combine12_0_41 combine12_41_39
theorem combine12_0_98 : CutRow book 12 0 98 := @joinRow book 12 0 80 18 combine12_0_80 combine12_80_18
theorem band12 : CutRow book 12 0 98 := combine12_0_98
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 5 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_5 : CutRow book 11 5 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_17 : CutRow book 11 17 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_29 : CutRow book 11 29 6 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_35 : CutRow book 11 35 12 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_47 : CutRow book 11 47 7 := bandCut 12 false (by decide +kernel)
theorem combine11_0_17 : CutRow book 11 0 17 := @joinRow book 11 0 5 12 row11_0 row11_5
theorem combine11_17_18 : CutRow book 11 17 18 := @joinRow book 11 17 12 6 row11_17 row11_29
theorem combine11_35_19 : CutRow book 11 35 19 := @joinRow book 11 35 12 7 row11_35 row11_47
theorem combine11_0_35 : CutRow book 11 0 35 := @joinRow book 11 0 17 18 combine11_0_17 combine11_17_18
theorem combine11_0_54 : CutRow book 11 0 54 := @joinRow book 11 0 35 19 combine11_0_35 combine11_35_19
theorem band11 : CutRow book 11 0 54 := combine11_0_54
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_1 : CutRow book 10 1 5 := bandCut 11 false (by decide +kernel)
theorem combine10_0_6 : CutRow book 10 0 6 := @joinRow book 10 0 1 5 row10_0 row10_1
theorem band10 : CutRow book 10 0 6 := combine10_0_6
theorem checked : mixedTables book 15 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
  · exact band15
end B1023_16
theorem h1023_16 : Face true 1023 16 :=
  mixedLower (g:=B1023_16.book) (i:=0) (hints:=296906400036)
    (before_sound B1023_16.entries B1023_16.prior) B1023_16.geometry B1023_16.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m29_4 : Face false 29 4 := lowerHint (lower_down h29_4) (by decide)
theorem m78_4 : Face false 78 4 := lowerHint (lower_down h78_4) (by decide)
theorem m95_7 : Face false 95 7 := lowerHint (lower_down h95_7) (by decide)
theorem m189_8 : Face false 189 8 := lowerHint (lower_down h189_8) (by decide)
theorem m255_11 : Face false 255 11 := lowerHint (lower_down h255_11) (by decide)
theorem m353_4 : Face false 353 4 := lowerHint (lower_down h353_4) (by decide)
theorem m359_7 : Face false 359 7 := lowerHint (lower_down h359_7) (by decide)
theorem m371_7 : Face false 371 7 := lowerHint (lower_down h371_7) (by decide)
theorem m377_7 : Face false 377 7 := lowerHint (lower_down h377_7) (by decide)
theorem m383_11 : Face false 383 11 := lowerHint (lower_down h383_11) (by decide)
theorem m486_8 : Face false 486 8 := lowerHint (lower_down h486_8) (by decide)
theorem m510_11 : Face false 510 11 := lowerHint (lower_down h510_11) (by decide)
theorem m511_13 : Face false 511 13 := lowerHint (lower_down h511_13) (by decide)
theorem m606_8 : Face false 606 8 := lowerHint (lower_down h606_8) (by decide)
theorem m639_11 : Face false 639 11 := lowerHint (lower_down h639_11) (by decide)
theorem m668_7 : Face false 668 7 := lowerHint (lower_down h668_7) (by decide)
theorem m689_7 : Face false 689 7 := lowerHint (lower_down h689_7) (by decide)
theorem m695_10 : Face false 695 10 := lowerHint (lower_down h695_10) (by decide)
theorem m701_11 : Face false 701 11 := lowerHint (lower_down h701_11) (by decide)
theorem m710_7 : Face false 710 7 := lowerHint (lower_down h710_7) (by decide)
theorem m727_10 : Face false 727 10 := lowerHint (lower_down h727_10) (by decide)
theorem m734_11 : Face false 734 11 := lowerHint (lower_down h734_11) (by decide)
theorem m743_10 : Face false 743 10 := lowerHint (lower_down h743_10) (by decide)
theorem m30_4 : Face false 30 4 := lowerHint (lower_down h30_4) (by decide)
theorem m57_4 : Face false 57 4 := lowerHint (lower_down h57_4) (by decide)
theorem m63_7 : Face false 63 7 := lowerHint (lower_down h63_7) (by decide)
theorem m165_4 : Face false 165 4 := lowerHint (lower_down h165_4) (by decide)
theorem m166_4 : Face false 166 4 := lowerHint (lower_down h166_4) (by decide)
theorem m172_4 : Face false 172 4 := lowerHint (lower_down h172_4) (by decide)
theorem m177_4 : Face false 177 4 := lowerHint (lower_down h177_4) (by decide)
theorem m183_7 : Face false 183 7 := lowerHint (lower_down h183_7) (by decide)
theorem m190_7 : Face false 190 7 := lowerHint (lower_down h190_7) (by decide)
theorem m198_4 : Face false 198 4 := lowerHint (lower_down h198_4) (by decide)
theorem m222_7 : Face false 222 7 := lowerHint (lower_down h222_7) (by decide)
theorem m540_4 : Face false 540 4 := lowerHint (lower_down h540_4) (by decide)
theorem m561_4 : Face false 561 4 := lowerHint (lower_down h561_4) (by decide)
theorem m573_7 : Face false 573 7 := lowerHint (lower_down h573_7) (by decide)
theorem m582_4 : Face false 582 4 := lowerHint (lower_down h582_4) (by decide)
theorem m593_4 : Face false 593 4 := lowerHint (lower_down h593_4) (by decide)
theorem m594_4 : Face false 594 4 := lowerHint (lower_down h594_4) (by decide)
theorem m599_7 : Face false 599 7 := lowerHint (lower_down h599_7) (by decide)
theorem m627_7 : Face false 627 7 := lowerHint (lower_down h627_7) (by decide)
theorem m633_7 : Face false 633 7 := lowerHint (lower_down h633_7) (by decide)
theorem m652_4 : Face false 652 4 := lowerHint (lower_down h652_4) (by decide)
theorem m657_4 : Face false 657 4 := lowerHint (lower_down h657_4) (by decide)
theorem m664_4 : Face false 664 4 := lowerHint (lower_down h664_4) (by decide)
theorem m673_4 : Face false 673 4 := lowerHint (lower_down h673_4) (by decide)
theorem m688_4 : Face false 688 4 := lowerHint (lower_down h688_4) (by decide)
theorem m706_4 : Face false 706 4 := lowerHint (lower_down h706_4) (by decide)
theorem m723_7 : Face false 723 7 := lowerHint (lower_down h723_7) (by decide)
theorem m739_7 : Face false 739 7 := lowerHint (lower_down h739_7) (by decide)
theorem m755_10 : Face false 755 10 := lowerHint (lower_down h755_10) (by decide)
theorem m759_12 : Face false 759 12 := lowerHint (lower_down h759_12) (by decide)
theorem h760_7 : Face true 760 7 := carry_of (swaps:=[146,67,130,97]) (by decide +kernel) h190_7
theorem m760_7 : Face false 760 7 := lowerHint (lower_down h760_7) (by decide)

namespace M767_15
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(165,4),(166,4),(172,4),(177,4),(183,7),(189,8),(190,7),(198,4),(222,7),(255,11),(540,4),(561,4),(573,7),(582,4),(593,4),(594,4),(599,7),(606,8),(627,7),(633,7),(639,11),(652,4),(657,4),(664,4),(668,7),(673,4),(688,4),(689,7),(695,10),(701,11),(706,4),(710,7),(723,7),(727,10),(734,11),(739,7),(743,10),(755,10),(759,12),(760,7)]
theorem prior : Known false entries := (consFace m29_4 (consFace m30_4 (consFace m57_4 (consFace m63_7 (consFace m78_4 (consFace m95_7 (consFace m165_4 (consFace m166_4 (consFace m172_4 (consFace m177_4 (consFace m183_7 (consFace m189_8 (consFace m190_7 (consFace m198_4 (consFace m222_7 (consFace m255_11 (consFace m540_4 (consFace m561_4 (consFace m573_7 (consFace m582_4 (consFace m593_4 (consFace m594_4 (consFace m599_7 (consFace m606_8 (consFace m627_7 (consFace m633_7 (consFace m639_11 (consFace m652_4 (consFace m657_4 (consFace m664_4 (consFace m668_7 (consFace m673_4 (consFace m688_4 (consFace m689_7 (consFace m695_10 (consFace m701_11 (consFace m706_4 (consFace m710_7 (consFace m723_7 (consFace m727_10 (consFace m734_11 (consFace m739_7 (consFace m743_10 (consFace m755_10 (consFace m759_12 (consFace m760_7 (known_down baseKnown)))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 132 0xffffff000000000,padColumn 132 0x352352352352352352352352352352352),(padColumn 132 0xfff000000000000fff,padColumn 132 0xa31a31a31a31a31a31a31a31a31a31a31),(padColumn 132 0xfff000000000000ffffff,padColumn 132 0x50a50a50a50a50a50a50a50a50a50a50a),(padColumn 132 0xffffff000,padColumn 132 0xa54a54a54a54a54a54a54a54a54a54a54),(padColumn 132 0xfff000000000ffffff000000,padColumn 132 0xa90a90a90a90a90a90a90a90a90a90a9),(padColumn 132 0xfff000000000fff000000000000,padColumn 132 0xc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0d),(padColumn 132 0xfff000000000000fff000000000000000,padColumn 132 0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce),(padColumn 132 0xffffff000fff000000000000000000,padColumn 132 0xf00f00f00f00f00f00f00f00f00f00f0)] i else tableBits #[(padColumn 132 0x0,padColumn 132 0x0),(padColumn 132 0xffffff000fff000000000000000000000,padColumn 132 0xf00f00f00f00f00f00f00f00f00f00f00)] i))
def cols : List ColumnInfo := [(8,0,759,0,12),(128,0,639,0,11),(512,0,255,0,11),(33,0,734,0,11),(66,0,701,0,11),(12,0,755,0,10),(24,0,743,0,10),(40,0,727,0,10),(72,0,695,0,10),(129,32,606,0,8),(161,0,606,0,8),(514,64,189,0,8),(578,0,189,0,8),(7,0,760,0,7),(20,8,739,0,7),(28,0,739,0,7),(44,0,723,0,7),(134,0,633,0,7),(140,0,627,0,7),(168,0,599,0,7),(194,0,573,0,7),(545,0,222,0,7),(577,0,190,0,7),(584,0,183,0,7),(672,0,95,0,7),(704,0,63,0,7),(56,1,710,0,7),(57,0,710,0,7),(76,2,689,0,7),(78,0,689,0,7),(99,0,668,0,7),(52,9,706,0,4),(60,1,706,0,4),(79,0,688,0,4),(84,10,673,0,4),(86,8,673,0,4),(92,2,673,0,4),(101,2,664,0,4),(103,0,664,0,4),(110,0,657,0,4),(114,1,652,0,4),(153,32,582,0,4),(170,4,593,0,4),(173,0,594,0,4),(202,4,561,0,4),(227,0,540,0,4),(531,64,172,0,4),(538,64,165,0,4),(553,16,198,0,4),(569,0,198,0,4),(585,16,166,0,4),(590,0,177,0,4),(601,0,166,0,4),(646,64,57,0,4),(657,32,78,0,4),(674,64,29,0,4),(688,1,78,0,4),(689,0,78,0,4),(708,2,57,0,4),(710,0,57,0,4),(737,0,30,0,4),(738,0,29,0,4)]
def plus : Nat := 0x240a00a084084108210441803006
def minus : Nat := 0x8aa2482e05340c92488b1d06811432
def orderBank : Nat → Nat := (fun i => ((fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x441208047411004819468004a4041988020500432080110c102a1810138184000040404200050808064000a111004800240421200002808423000000048420014c802810e9280260020d4000505031a0610148041,0x4148050000082029900c1480220428801224c08310022004086a00028281842500440010800a0084068000c3090490240c252020c8700942040800a0046068000c0090490001c804118800420073200008414e620,0x1102010c1020004222021800404a3032000208080260012020c900000c430882000080243100445408e085388412841063088011010d03080a403088810086041000c009410c000401281180050100031000048c4408,0x10128c1500000202012800180201420005088802a0000118c050001402120980010400231000400848060008110480c000c43098100018060102000000468201844008810e200440081942500440021a06101480a1,0x10100054000102400a00000086220300020800240310040a0152308801101950009006051800508060a8000a020d140a000282828c001a425145000a02002a40000100c0900028081a280002244510528090a0a0a3,0x1102010c0c200100411a100010480130000848044a60010928890c00240911a90002012234200030200062000414804c030a4081019400408022530008114448600100108d4800100611a10002002004100030040062,0x600910c00004012210000000833102860404e0a7184800880ca0020251821800404411520004090228400082084904000c410918800481033500004008460400081104408000c43090092401108054a0610148081,0x14208454000204308a000050901130000410422404942822814e920088402144008801010800809c60860012340cd40818447202044408c43030800708080a800141104548000820201200000404014000a00488a0] i else tableWord #[0x20cc8000000119880001840020100084146086000624048c400100b11810e440143030800902088a000120220950001404411a0002050a325000520108640012120414400202208208002848103100040902042,0x81200480000041220800000c23310000a00402a400001010090000c01009900038400251000008c8028000412008c400280119a800040060152000400402840000100c08c002020012880020480241000008c6026,0x410154c4001404222800008024430000000488200000800c08c00010318098000012332000000206620000441214d000040619900004006004100040040042001212005400014064102000404001400004090a640,0x812150c00008202a1012401108053a003280c0a35000141410200108128a280020481243000a12026a4000211100900014442228000210451050001104886050081414146001420202a0001040403400050888028,0x101008c002020012080028444013000a00486a000120410d00741100482a52401108043a003280c085001415101500028082228000400450540004004a068001404001040010410918800200200310005019060a,0xa120450800040128120002804230224a141140a900064094514000c4109a100028c83450000018468201102310c102000c01281a00050020051000a1202482000e100054000140611810e50a00a054800708080a6,0x1190054000c0122a0000080245300c240044087000a800c150000100181200002063014000402c48060000040d04030a4081021ce440143040800708060a60010100c10c00180300a10001a0a9504000909022a4,0x31403380042001801282a0004852115200032042462001010151400000202a0804009001021800800c00a231004420152002027182a00008444025206111c80a10010828c150000c0800a1100098060518002080806a] i) else (if i<24 then tableWord #[0x4042411814612902200084002012723500020110648000e0180144001081321880002407512000718002a000103000500000083420180020c80130000048cea04000432004806200814021d2202487052a001200c083,0x600800840014824201800404a0130000040cea0450c0809c14a8004a03020cc5004e0010800610c44a600103108d4800106411a100021020041000320400620002408008400242900a8000284411020c221844065,0x310040a014ea000282820ce408d430208004090aa82000412154c422040b1818400180251350001004a24a0000218884c0008202a90800280833500004008a20a0008041c8d40021003aa1000214264310003284c842,0x41214c407285005029cc401028042a860404e0a3000c0094550001001289a000304630520003004a248000e151008c001406418a80020485431000008c6024000c308c940000c03288200020c2323000001846420,0x10128c084002801212800050023150000600462801102010c0420000831109800280c2312000300ca20a000c041c514001008389280020025023000201104280006009404c0008824209000001071050008080a680,0x801144100000012188000000232101c810286041000a3108c4800200b38a280020127125000720060a2000a400c0c400088b42090002016710500060048480000a020c4c022100b1808400384040520005400ea62,0x8310900c000c830081000205602010c22184408709481100086001480182100011048523000020c6024000c0090d400014041920000280c321008840086041000a100c1080020202a2880030023250000a0206480,0x2110801280260010cc5004c0021a001200c0a5000a032105400180119a8000194665022001280c0a53140138008672040a18184001902014200011884846000240804c8000824012080028c4241300050882426] i else tableWord #[0xa101010c00280800a1000004640130003094c40a000a0210d0000000421900003046305300070a8806800084080508000c81009900048520251000618466a00008308cd009004893029425204c00219c811a86061,0xa801d50c00288100a9000511001420007080a8a20000041cc5400286119a800010485541000501848260000020d08022040b1820400190265322021208c0a5000640990840010240098000104801201d0448120a9,0x100c048002801192800030023240000501064600000020c840000401289a8000102131200040ac240600064184c082004800819400010622030007094c2a8000a801d4c8000009390a800001072050002090a640,0xc0394490000080181180038c00251000518004820000418c04c00100b3982800280833400003180a802000630008046280670010c44201630308005090c2680010100c10800142018190000052a315000a220c862,0x384404080ca2304450810c4420c43030800520060a80004400c0d000008018120000106301400050186820100620040ca221002182040050103340000808060a6000a100c10c001c80182980029003043000700c02a4,0xa83a500c00140740818000206a4020004190a420020a101814e7411004821ce50a00a042988020500633140338014200188318298001044403400010888028000e44194c4001c48091880048d2335000001906620,0x394280280ca6280270020d40005050219c811a860a100040114514001c4809a100038100142000519868203844040810e221062182040038060045000601ca0a4000a022048c0010a1318a8002050a2140007180a480,0x64098c4024002520294c401028032a860404e083400240180c2000c0100aa0002a0073250003004a2a400140400490000023180a80038400431000300c02080008152880c000c03288100000c235100d48004e0a7] i)) else (if i<48 then (if i<40 then tableWord #[0xc308c900001102528180028c83230000320cc8020000320c8408084823020c4408c430208009010428a0004129814c0010083892000180242150002090c0260010829d0840000042102800001271040004204c640,0x90640a014ea181013821400090484130000400ea2400042220c9000288100288000248951400001110628000840800c4000c81001080048520140290448920a9490444a010e129026000840030463042000a18464a0,0x90040a014a8004400828c00108884350000111084a490444a0152001008391a00010c88325000120400a2001440801040010810a98800020a74120005098220a00121200500000083428180002067402054820520a9,0xa22208d0000502528980009048412248222500850000402104c9200894021d4202447052a003200c08300141104514001424089a8000802505300014094826000820854840014064102800384001401ca14014087,0x43298490000c48092880018100051000048c440a0004148054030a408102940038ca61340003004a0a4000a3298490000c01002880039466431000641d462400140400084001c20291810019406041a8000a0a041,0x4912944c00240418a814822049054a4a249140a7000c341c4d40010c13192000304e3041000201104260010100c0c400088241890004808314000060048460000c008c4c01418223021d431a0270518005480446a,0x1404004d4000020202900040ca6524000808080840008009448c00202029a080019466405000300c020a00063299410000c054102000200451030105180c0a93140138014600104951928001910941500080806082,0xe101490000202000980e82a0090439ca34014085400240180c60008072892800288e22130002094aa42000204110803088a810194002a88834500090a4a8a2000aa320c5400180819280c4511080539c810286081] i else tableWord #[0x5208912410e9208894019400384040420008400e8620014008c50072040a1808400284a6123000a284c68200121214900a311014821d250a08a042a001280c063000a121848c001801281900000d2a214000700c0082,0x211480000080201280029044015206401480a140c203901420021403a19000500422410008088206200146098d00001c4a0890142028470429c220284043404261180c223044708084001248941300090248460,0x600944d00000242a1080000c83320000808c60a60010418054800188100a9000284c6215000902466a0000840805480008250118800184a020108012142065001454195080000a1328900000405421000409004a2,0x3910350c0c2001426088112009126051988320500a9000e11901480021003aa08003854401200040a9460a0014308c54000246918a000028c8313000041846240490044a010a72046a18084001a06a5032401224c083,0x310640a010e0008243092000180250230007080a6a000001014c400018083922800110484230002511086a3114442015290208930294c411028054800640c60a6000644004c800186819a800020d0334000001a06620,0x488a821c14a9020893020c0020d0723500001a0e40a518c80a4152a18d0138294004888835418822050087000c341c514002801282980020d0712500000a1460a00043220c900018810020800284c610428c440520a9,0xc138c04c00040619881010984605188c111c2043000211900d4000c8311820000802343000000048a201848308810e00002018098003150724500042a0e46a0004a220c90001c8a421180001527215188a2210087,0x220914c0001081289a00021426532000400402640006139881400144421a000021045104000010486205008141410681844720184000082451000030208a80184c008810e2304470819400190023040004304ca82] i) else (if i<56 then tableWord #[0x10024284086000824309a8005110004100011884624000a3108c080024292a28000420e305400031208a800002340d0c00000681a08000304e30230005119082a000640944d400048128928002804231200011048840,0x50121414102001520112180002462203000710044a6000483254d000280211a9000120a95240003204a06800143108d48000522528a0000904501400004854a08000a1200500928524502a4005110124100020940240,0x600940900020451099000400422510001004a028000802088c40008242a10000104054100002195084a000c408014400142630828004852104100004912a08000002208109020893028c001a4250340001484a048,0x2111008c0024240128800008623140002008a068000e25048c400082b00980e110d420328009090c2a8000840990849299045029c0048888254000522d0864000022208500014464102000408e2243000810042a4,0x490044a01520018a100a90002142014200000946046000a1398854000ca300810c5284e00218006004a286000e1014d440000054212800404a02410001208804a00064400508000829012080020d624030c291a04087,0xa158090400180800a90002a0e6215000602066a000085519408001407420a8c4014280548003194c40a4006501814a6200c1402a503080e40408000115084a00120491140001c8a201a0000100852400032010a08,0x660848c4000c2730828001986120108c131c2043000c008050800180119a00001890a43500014094a480012121514400104a52028004808335024a241140a9000415808c400102a52028001a42a5340001208a248,0x118243840ca000461229810308ca40509c811a8608100048398494000d0730828001100402400012088028000602a1014808cc23028d03200a4040800641c6026000203110400008273092800204c114200043042482] i else tableWord #[0x918884c00280819a8061480220328008008a2a80012048c9409208894029c00200c5134000808060a40004411008c0010041918124011280538000094604800084084d4800288800a90002102134200050982426,0x1108010c0c2001427180980049523350000011088400000520cc800000a11988103088a4040888128860610008310480c70880a1021c001a4251350001484a24a000a4010150001482200a000280c441028000a8a0a3,0x82504c0800100a008100001423410206151480a13902550c10200016442128002acc8415248b22500a90002412149000100a39828e51200a054a840408e0a7000040100900024042228000410a304300050186620,0x140108d88000009398b000508212610003204ca62000e10151807411004832ce50a00a064a860404e0c7000a510904c0010a21201800220412030c222a04087101022840ca00002b201280000544015000509c6028,0x120410d4000100839a3000384040640002011086a001411045880020430928800010085140000400ec260014009118000000422080002848624500000a5484c00140080588001c202a30800500233600005400ec86,0x1440801840004813290800104854301d0448120cb0008409950800108132a0800218265420003304ca64000e1000984001482428a00002067613000600488a04002601814a001465312280038404063000a00486c0,0x6519901800286819180082840606498a009c00c3000482258d4a311014832c0050c232560006184648c0006019418c000064190b000511000310000184640c21c6150c18a00142430a280028802243000a20424c2,0x1a00129018a000d01531a0004848546124a141140c950c6809c18e00288100b100021149506000a18466c0000a320cd000028a1322b000501001360005094cc680000801d588000ca132130001802512300054192a28] i))) else (if i<80 then (if i<72 then tableWord #[0x24094090a01028282040019109536000820044a600120208d88000029520b000500200610009090a8c000140090958001801212300028084236000720108a4000880a948c000004210b000004046120000004840c,0x121200984a411224832c00201072360008400eca40000819d848002801193014302027062800748044c60002041cc98001c430930800380600610003220ca62000414950c07415004832ce51a00a0648006204a0a8,0x922549800004442130002a4c95160005119082c001204911808524824832d24111280648002098c26a00021190090000cc1329880020c423020008400eca600085099508000ca132990001248963500004912c4a,0x394280281d6001420203280018025146000a08824e6000a020918c000502539300050100162000708004e2001400915c00014041a30000200451061ca140140ed50c0809c1d2a000282830c002010734500024912a6c,0x1001145940020201832000120a9736000808824c6000a020914c00284109b90005002017200004112e4c000c2184d880005025392800384055710000020e82e001010009840028011a38000481034601d0440120ed,0x14040d1800004081a1800019066702188020500eb400240181ca00100128ab00040042473000401048a6001001805c800104109a900020020152000808004e2000812159440008202b1880030103470188022100eb,0x64084d080020202b3880030023470000300ca20c000e4521d14000905311b8002a0c62170003414c40e311444201d600180128bb00042003074000540060c8001011049cc000401289b0001200303400050190a2e,0xa320d180001082288300000c834202021208c0e550081414186000824312380001062314000511c46280006039441800204011ba000284030640002090ac82000c00915c0000c2531038001104874500090a424e6] i else tableWord #[0xe1000580a101223831440188010718001184686000003091440620c81403ad2009126072800a2290eca000c118c1d0000c8128a3000100a8537000a22002c4000c138c0900024292b3880048520271000618468e0,0x240944d8001064122980050c41167000818822ae000802088dc001009391b00010c411270002011064a000a2009d080008022812000001272160004204ca6200002009c480001203b0900028042207000208002e0,0x442585c001406428b00050c2347000061048ac0310040a01968004803031400204812530002094ac62000c508d1c00014a41a30000008845200c222844087100222840ca81844520284440944304080050ac80ca,0x8008d14000042a201a8000a824530000029068400000a091440622881403ac00505440650004204a2ac310440a01d6002822203a80038463074000810046c800102288d50002802123980040042463000a204cce4,0x100c1c80019033b290001a02a62400072290a460000341c85800148242898001806010700040a9480c00061015004041420303ad431a02706298a009c00e300064099d0800048133990004040307400032010e0a,0x61299c140110250839425204c00718002094c46e00041580904000ca333810c401428075a001280c0e5000c1429158001868392b000501001470004004026e000010101cc001028521b000290085430003004024e,0x14440051c0015044b2280019021237000009460e6000244254980004285213000104a672500024152c4a000280a989000140411a1000080251240000020e62c000a1319c54000825039080010405421000001066e0,0x310060a01d68004c03039400128a9736000600c02c40006a2a5c18741140483b40030025165000a18824e6000a358494c000403289a80038861372000600402c400142504d480018011a3000051021267000620402ae] i) else tableWord #[0xc008cd80620c8140324001a4251460001484a26c00149400588000d2100a100022445106000348c0204404261181caa024282830c2548440021800a12026c4000a131885c0008c243a2800200c245300010186840,0x49448228192a18d013839400511001570004204248e0008408051c00100128a2800190201370002191086c000c218898c001823183180010ca84260005098ce2c00081201d04000c83090380019060107000600488c0,0x50c0809c1ce001828522b80030d07257000a004a2e8000814290dc00288242b18002090a43600031054e4c00064425498000028520b80010485421000a00486e00014008c9c000240421b000048083260290440920cb,0xa222115800100939a38003900407400024912e6c000422210d800142018298001104403400004912e4c000241218900001003b918004852026100040a94a0e0014008cdc000240919b000020083340290448920ed,0x494482281d6002062093980008065136000402002a40008020d1403088081021c00290040650002190c48e000440100d40000804392800481245700003194c40e490044a01d6800c8030394005014016228000a8a0c3,0x218c00a01da818407203840042041273000201ca26c0008520914c000c4809a100008104530188222100eb405041181ca00104852a38001112963700024094e6a000441218d00000894b1380048480271000901066e0,0xa411005c000c054383000184055012003200c0c540c802901c2001420202b800404e30740002090c48c0006009451400140b122980000404027000a02802a4000a612185c0020202ab0800300247600003094c40c,0x140622880002900405700022090c8e0010128c1d00010041239800110040370000200804e] i))) (i/16) >>> (43*(i%16))) % 8796093022208)
def orderClauses : Nat → Nat := (fun i => (if i<256 then (if i<128 then (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x240400700c01402003004004000a,0x2804c0901102003c0700d01802c050b,0x3005c0901102003c07016018054050b,0x460881082003e0780e81c0360680c8b,0x5c0b41602b0540a41402704c094120b,0x1f83e07a0f01d83a0720e01b83606a0d0198320620c01791,0x114220430760e81c8420820e01b83606a0d0198320800c41792,0x4808810c1d83a07211c1c03606a0d01983208c0c41790] i else tableWord #[0xaa150298520a21402784e09a1302584a09206c0c8f,0xb816c2d0590a21602784e0ae1302585609206c0c8f,0xaa1502985e0a21402784e0ba1302584a09206c0c8f,0x1a8348680ce198328640c61883084a0361802f8e,0xe81a8398720e21983806f0dc1b43106c0d606c300f,0x1e0298680ce1983b8640c61883084a0361d83a8e,0x10e21842884106208408800fe1f83e87c0f61e83c8f,0xa81a8348680ce198440640c61883084a0361802f8f] i) else (if i<24 then tableWord #[0x230348680ce22c3288a0c618830856036180448e,0x6a12a250498921222403288f06a238468610621802f90,0x3a06a13826c4d09913025c4b06f11e0d44708d0d80c43011,0xf02544a09a1242444807706a2784e8610621d83a8f,0x8710c214420a5042290518a21422804f87b0f40680c90,0xa712a25049892122240440a606a238468610621802f90,0x8c12a250558921222a8328a906a2a0468610621804490,0x1642c42209b1602bc570ad06c0d45603208c0c4300f] i else tableWord #[0x5d0b91702dc5803916c2d45a03706c0d44f0321660c43b11,0x18a310348c31843046004f17e2f85e8bc0362ec0c8f,0x1642c42209b1302bc570ad06c0d45603208c0c4300f,0x18e2c45c09b1600e4630ad06c0d4560320800c4300f,0x3404e0cf19c334660cb06a234650c91900c4128e,0x1ac1cc6a8d40a034c2e8d20983443606b0362ec0c8f,0x36c220da07a0ec1d0391b22d41b83606a360198321660c46b92,0xd61c037c6f0d41861985184d1ba1306e04a0362ec0c90] i)) else (if i<48 then (if i<40 then tableWord #[0x1c838c4e0e21262646709012c3845308e1940c42f8f,0x1d6110750e915e1087403606a39c7303208c0c4728f,0x7e3c01f03d1de0e4770ed06c0d41a0ec0640c4180f,0xaa1502985e0a21402784e0ba1302584a1e206c0c8f,0xf307c3c81e0e90723a01b83606a39c730320620c07290,0x7b0f507a0f01d83a0720e01b83606a360198320623d06b91,0xaa1502985e1f01442804f09c174260f709406c0c8f,0xfe1ac3f46f0c31f81407d84d0ba2f87d04a0923e45d90] i else tableWord #[0x10d21842c8510921041c8310520840c651022024007f90,0x23029c8b91622a4508991209c1748884b22043c870f,0x1232443549092023e34c5091e23a470651022364688c90,0x591290d44a058127120498929240dc2b04704a08c1802f91,0xb22521a89412c256498571250dc2b04704a08c1809510,0x2764e89c93826e4d89a9342664c89893025e4b8968f,0x28e08ca314528850ca11412802809f93e27a4f00d0f,0xb22521a894072130528a49252901bc370ac0d61183010] i) else (if i<56 then tableWord #[0x591290d44a04c127120498929480dc2b04704a08c1802f91,0x14728c5440415028453ca714d2980149f13d278000a590,0x15a10c564a88842b0510ab9562aa550a993e27a000a910,0x591290d44a05812712056c929240dc2b04711008c1802f91,0x13b27458c1696226a4d0b09602be578ae92f25c094ae10,0x13b2745a8b496226a5a0b39662be578b292f25c094b210,0x7e3d4ba9742e60f0b91712e05bc1b8362dc0d0b696c2d60c01793,0x350941265ec490b01205e8bc83511c234259782ee180bb11] i else tableWord #[0x350941265ec490b01205e84783511c2342597c0621802f91,0x350941265ec490b01205e84783511c2342597c2fa1802f91,0xd42504989212225cbd17f11e2342597c2fc180950f,0x312620c398630a260481843065b84e84b304604c00f,0x18f31c33c9b09231a59cc618b3145789797c25c0c41290,0x9190c1aa428c991f1a62848f192238644c81022364000c91,0xd461cca97b30a2c04817a2dc5b4259942d61802f8f,0x4808810ccc9723300e4238e832e2341983208c5f8cb10] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x33e678ce98633866c4819a2642746886c25c604c00f,0x1a43466881099323e684699403406449f11b2000680c90,0xd60d2378618660a03ecd285d1a4130358490362ec0c90,0x906a8220430760e4d484735069c1a03334c118178f,0x3486d0d99b23626c0d79ae35a6b0d593e236400120f,0x1c2382700df9be37a6f0dd9ba37223cdc1b71a26d8da90,0x38870cce99530c5884817a37223c4719425c5ac2f8f,0x38870cc70932c4240bd1c52f20d44717825c5dcbb0f] i else tableWord #[0x1cc396110e51c90740e42383806c0d4e41c708c0c4e310,0x3ac754349d43a6748e88643a0188259cf21e738e68f,0x3ca790f19e23c2780ef9de3ba770ed9da3b2760eb8f,0x7ac221ea3d27241d0391b24901b83606a7a0f383208c0c4f312,0x3f47e4fc1f73ec7d4fa1f33e47c4f81ef3dc7b4f60f,0x41081d0320540880d012014007fced1fe3fa7f0fd8f,0x1b442268cd899342083d0720d41882c6513e2368290490,0x24686d0d21943085d0b0a342a648c8a1442646d090f] i) else (if i<88 then tableWord #[0x48d0d8d54328610ea1c23e34d0a91e324470c8a1442646c0c92,0x8a914a2844e8990ba2542c89111a22324884c8a2043e8790912,0x45a7551618730c614488903a260cb716d4565ac3a8f,0x23746c8d4a2a340428cd1904f4622811822f45c0680c90,0x10d2183551d9091a62848f192208644c823a4728e00c90,0x23f10a3550ca3e0428f4520a342a2810a07b4780680c90,0x9252424748c91522243142908f81ef4829008c8e,0x1fc310348c31843046004f17e2f8978490362ec0c8f] i else tableWord #[0x25049e0892724d0429312594003c131252380360680c90,0x25b4b49652c2574ac53ca72554a894d291fd4a2000a590,0x10c98930a604be508a7a5e2980152ea5c27a000a58f,0x9bd3726d4d89ad350074d29a133a6600a994022644c60040012,0x591290d44a05814a120498929240dc2b04706b08c180bb11,0x1f83e07a0f01d9980723a0d41a706a0d0761a62fc0c13811,0x13a93a2c60b53a27326a4d1391602be578aea7125c094ae11,0x591290d49e8582791209e0929244ee2b04727608c1802f91] i)) else (if i<112 then (if i<104 then tableWord #[0x283504a05402434fe9f93ea7c4f69000c8c,0x512a094424350e9f9432855089008c8b,0x40ca354614f516950ed1fd3f8001450b,0x40ca354894f516a4147a8e3f8000a58b,0xa694ca9852ea58ed295528a4d490a,0x7b03e07a0f01d83a0720e01b83606a0d019832062a6c1791,0x1fa9e07aa741d83a0720e01b83606a0d019832062a701791,0x3f07c0f5501720723a0d429f32e234198322fc0c0cb10] i else tableWord #[0x9d93a546638679361244d5512a131862c4692f2f04b81291,0x7ea9cbaaa02e4a9876a9f32ea9419aa43020c0cb0f,0xd48b04a09330a2444baa82fe23c46a2b2fc180950f,0x3126215518730caa44889030860cb709d096604c00f,0x5586215598730c614488900ee60cb709d0c2604c00f,0x2766255799d32a588482ae3084c95689d3044b8c00f,0x1b442268cd899342083d58a0d41882c6513e236ac09690,0x43146576ae8a2150572ae15bab656aad0c813e5664f15911] i) else (if i<120 then tableWord #[0x3126215518730caa44889030860cb709d578604c00f,0x45a6211618730c614488903a260cb709d456604c00f,0xaa1502985222a4508991209c1355f04b094af5090f,0x588620c3ac330a260552c25825b96004b3046055f8f,0x3126215518730caa44889030860cb709d58a604c00f,0x590620c398630a260482c23065b84eac758c604c00f,0x59448c862c91aa3048f8d3142648c89022364000c8f,0x8d672cd344085660a1322b2c6513e2364000d0e] i else tableWord #[0x48d69a1a5a44290b99342c28d68906324470c8ad059e46d0912,0x5aeb5811ad528a510a19425a85005013f27a9440d0f,0x5b248d0dac91aa3048f8d35a2648c8ad82368280c8f,0x2dd2183548519323eb705091e3244716d9025b44000c90,0x5cab9171ae25c23048f8a342a648c8ae05beb780c8f,0xb23542c42209b1300e4d48ae15a69c1a8ac34c1183010,0x6a0d21c8388665cc5e83786e0da1882586b09206c3010,0x7ebad539752e63bcb91705d4ba4b72e85ce5ac180f] i)))) else (if i<192 then (if i<160 then (if i<144 then (if i<136 then tableWord #[0xc798e19e4d84918d2ce630c597906a5789797825c5dc1291,0x6a0d21c9780675de5e83786e5dc1882586b5dabb03010,0x7e3c1539751de0ed532f15d25b9528ec548604180f,0x7ebac1f03d1de5c0770ed06c0d41a2e75e40c4180f,0x7e3c01f03d1de0e4770ed06c0d41a2f30640c4180f,0x1e63c01f0f21de0e57a0ed06c0d4738e60640c4180f,0x1ec3d4ba9742e60f0b91712e05bc1b8362dcbd46c16c2d63d06b93,0xbf8c72fd5f84d8490cd5f6be97c97906abe0979785ee5dd7b12] i else tableWord #[0x1eca9cba83c0760e9532ff2dc36019aa43023d06b8f,0xba6061e1810b024e241808b56002784e84a1661d83a90,0x3c22c128c1582185122240e8aad06a2784ea2b0621d83a91,0x78128c14bd892160240c22ad06a2782597c0621d83a90,0x3095d63d47903c072c218383706c0d5830e60640c47a10,0xd61fa378618660a0c282685d1ba130252bd0362ec0c90,0x30e1ac3f46f30d0ccc318504d0bac2c8891057a2ec8710,0x1ac3810d31122828c2e8dd6203443604a61e2ed090f] i) else (if i<152 then tableWord #[0x18c3171aac598a8501a6c518985d6164458906c220bb00c91,0x638c6d8d3191aa14069a1509a1316804a56006c0c8f,0x31e1fa3786188b0b0c298e85717c1302b2bd0362ec0c90,0x3211fac80618660a0c282685d1ba130252bd036c7c0c90,0xd61fa378618660a0c282685d1ba130253220362ec0c90,0xaa1502985e1f01442804f09c1742606109406c0c8f,0x8710c2144208364a2044007f648c8c3e87c0f6acc3c90,0x2301519405e64e4548a32609c175882bc094c3d090f] i else tableWord #[0x1fc3119832f65ccb59632b1802fd9532925e0985d8f,0x230cc48b9160a21402784e0ba44425910092bb00c8f,0x66a8fc42b34666084520a36642804f87b4780680c8f,0x33836808ca29b0042cdc518a21422819b13d2000680c90,0x2301502985e0a21419304e0ba1316284a21e06c0c8f,0x5901502d05e0a21408904e0ba1316384a64406c0c8f,0x1186781a46f30d676c307d84d674c2c88b3921e2ec8710,0x3f1ea5d4ba173078cf41d9712e05bc1b8362dc0d0b696c2d60c01794] i)) else (if i<176 then (if i<168 then tableWord #[0x340c799d67ecf8668cc316628af0d125c5ac128e,0x798f56865cc1e3422e0d041b8362dc39cb6b402d60c07291,0x1ec3d4ba9742e60f0b91712e05bc1b8362dc0d0b696c2d6a6c1793,0x7ed10ba9742e6a74b91712e05bc1b8362dc0d0b696c2d6a701793,0x6a68c2504d0932f6249a28900ca0d4468612ee180bb10,0x350941265ec490981205e8bc83511c234259782ee180bb11,0xd20d99b268e4d0d71ad4ca5746513e236004ae0e,0x6a69cd35a634b68a240bd17969423952abc692180bb10] i else tableWord #[0x388d49a8893124240bd3502f20d44734f2f05dcbb0f,0x3535412826c4d093608d14580906a60d446a2b2ee180bb11,0x3c0941265ec490b01205e8bc83511c235ab1782eed54bb11,0x38870cc70932c4241ac1c52f20d44735725c5dcbb0f,0x35094126d68490b01205e8bc83511c235ac9782ee180bb11,0x6a6bc25049b5d68a241ae35b06a23846ac72ee180bb10,0xd21089b268e4d0d71ad4ca5756813e236004120e,0x6c2271b0093132d7c480965f20d446b120d80c42f8f] i) else (if i<184 then tableWord #[0xe198e134265b18906c4258af83511c2346886c25c0c42f91,0x1b49c36d0269b3b63120d99b29b906a23846b6425c0c42f91,0x1c838c4e36b1262646709012cda81a88d1940c42f8f,0x6a0d21c8ea0665de5e8320635dc188252ed5d81802f90,0xd4dc9b8b706dedb8370645dcdb55e04a6d81802f8f,0x1181a4391d4116dd1ae08a0c6dcc2b2ed5d8180448f,0x6a0d2de5bc0665deddc320635dc188253765d8dd42f90,0xd4dedb88670ccde8320635dc1896384a5d81802f8f] i else tableWord #[0x7ea9cba83c0760e9530ed2dca9419aa43020c0178f,0x7ea9cba8ef0760e95337e2dca9419aa4302df5be0f,0x7ea9cba8ef076661530ed2dca9419aa43020c0178f,0x1c333a6199f0906c4258dc88f2dc2386886c25c6042f90,0x7ea9cba83c0765c5c00ed2dca94b637f3020c0178f,0x1a8cf18730ccf8580970e05b95286c3021802f8e,0x6a55461da62a9122240bd08f2dc23952abc3021802f90,0x7ea9cba83c0765c5530ed2dca94b62a43020c0178f] i))) else (if i<224 then (if i<208 then (if i<200 then tableWord #[0xb2162e09c09871602bc570ad34e5b8562a408c6043010,0x3cdc1b430783a5530ed2dca94732a43020c0728e,0x7ea9cba83c076661530ed2dca94762a43020c1380f,0x1eca9cba83c0760e9530ed2dca9419aa4302a6c178f,0x48704e101d83a54c11c1c1a72dc0d019aa408c6041790,0x276e25c416370e4d89a9342c2599c315d70a4b8120f,0x38c27458c16a7426a4d1c59662be578aeb8a25c0941210,0x13b27458c1696226a4d0b09662be578ae92f25c0941210] i else tableWord #[0x591290d44a05838f120499c71240dc2b04738d08c180bb11,0xb22521e0940b024e240931240dc2b04704a720d542f90,0x1c99290d44a1c9127120498929240c8e444704a08cdd42f91,0x63b950d4e5058127120c05c70410dc2b04704a0801802f91,0x114220430760e81c8420820e1cb83606a0d1cb1c70800c41792,0x4808810c1d83a07211c1c03606a0d1cb1c708c0c41790,0x3522c12824d821851222415408f06a23846a2b0621802f91,0x3522c128d3182185122e79ceb9c736e6952a2b062e65cc11] i) else (if i<216 then tableWord #[0x3522c30ed31821851222415408f2dc23952a2b2d61802f91,0x1d0a2c1286f9821851226ed5408f06ae8046a2b062181cf91,0x7813826c4d09916025c3808f06a2384686c062d542f90,0x6a138e8c4d09972425dd108f06a2384686c062dd42f90,0x1c331c2684c8906cce98dc88f06a239d2ba425c0c42f90,0x3522c74ee8c499851222415408f06a23846a2b062dd42f91,0x6a13826c4d09916025c3808f06a2384686c0621802f90,0x353aa12824dd49851222415408f06a23846ba80621802f91] i else tableWord #[0x1fbb207aec5d803a0723a0d43af75ceb419832062eb1d591,0x1fbb22ea0f01d83a54c0e0d41a72dc0d019aa43020c01791,0x1f83e07a0f01dbb754ced9dabaf06a0d1da3b30620c01791,0x1fc155e00d677e1a46f8de77cef461bbc0cceec7d84d0ba374263ba772ee0250490362ec0c9b,0x78a4ece21c3788f0cc7093784248483c12f46e44788e774ee5dc17c25c0c42f97,0x1e73cd798710353cb0d2178393bd794f2433bc80ccf1de08880dc18de3062774185dc04a0361802f9d,0x7a4e31e898f788f0cc70cf78424866bd079e62cc515e774ee45eb5725c0c41297,0x79cf35e61c40d4f0dec89b7b0269eb8927ac245ea897782f501a88d77412ddc3d30621802f9b] i)) else (if i<240 then (if i<232 then tableWord #[0x3cd0aac38353cb0d2178393bd7b419dde066782f50bd0640c61b4313ba096ee0250490361802f9c,0x79cf35e61c40d4f0ded89b32a269eb8927ac245ea897782f501a88d77412ddc17c0621802f9b,0x79cf35e61c40d4f0ded89b32a269eb8927ac245ea897782f501a88d7b812ddc17c0621802f9b,0x3e21fc155f0bbf0a637c6f3be7c0f7d868fc7bc44ddd9127ba174692be774ee5dc04a57a2ed091c,0x3e97d0f9cda023244b38d1acd7cc6c4d121a7ca64d0b3e4598854d01911944f9f191b560069091c,0x3e21fcfad873e177e1686f3be7c0f7d868fc7bc44ddd91209a1746eabe7d4ee5dc04a57a2ed091c,0x1fb3f57e8d21f9bf242268df8b477e09a89a3ef42083df71307da3289f11b7d80049699,0xf149d989780abde23fa33a654c33c230a241fcbf8308fdd5689d774ee5dc19425c5ac3a9a] i else tableWord #[0xf149d9897fcabde23fa33a654c33fd30a241fcbf8308fdd5689d7d4ff1fd98225c604c01a,0x101e0340536808e02085806516011b11aa08600c005982845009f1944f9ff93d2000680c9a,0x3e21fd036060d6816168348df1bd029dec0918619a040fb09e6946904c7d4ff0358490362ec0c9c,0x3e28210342ab1881614c348df81f029dec0918619a0430a09e1346e84c7d4ff0250490370380c9c,0x3e21fd035f58d68161687e8df1bd029dec0918619a0430a2241346e84c7d4ff0252bd0362ec0c9c,0x1f10fe8301718f4170b437c6f3be82d05461c14116eec7d84f82615c5f04c8250442b0490362ec0c9d,0x13b83af449d41c2700b5e116226b06c9a41a2ce57caf15d774ee497c1925c094ae18,0x79cf361086a7f50811618730d07cc289112ef05a996e2db07915bb82d61802f97] i) else (if i<248 then tableWord #[0x79cf361206a78708c4dc22134f5c493d668af54483c7782f501a88d77412ddc1782ee180bb1b,0x3cd2310a0353cb0d245a13bbd5e019e13066782f50bd4250c6bb8313ba096ee0882ed5d81802f9c,0x4310e90c03542f85c678c398685b0b19f09112f0ac4b16e54b0aa1486c3021802f98,0x43e87a0fe1e43b1e10ea1c83e1b40f421c38078cf41d83a0730de1b4351da0dccb83606aba046c348660cc194320620c017a4,0x89f1382443c89b13225c4a89312223c4617010e22c4487110c1d8af07510a2084706e0d81a44087f0cc1983208c0c417a3,0x45a87a0fe2cc581e115e1cc568aa36821c548a6a819e83b8a40e628c350700dccb83606aba01a08d8a00cc194320620c017a4,0x119a2d4658c83ce31c628c30e62b0ea8c1152298e98a51462fc5e8ba0d81a8e78b916c194320620c0729e,0x87d0f63583f8d518a2c0f08731541f0da8d314d5033d2e40e81cc6886a0e01b99706cba01a08d8ce0cc194320620c017a3] i else tableWord #[0x43e87b1c41fc708c51607843907d1bc1e8438dd15077b3d2e46601cc6d86d1b07699734e0d57445c06716cd34322fc0c13824,0x45a8ed1d41fc638c51621cc5507c36821c6e0791d0b94520731ce36c7286c0e01ba9f32eba046c5c06716c194320620c017a4,0x8b51da3a83f8e118a2c4398aa0f86d4608a914e3c1727606601cc6d8e51dc7429f32eba046c5c06716c194322fc0c0cb23,0x8b51ea1e83f8e118a2c43907d1bc21c6e1df1e4b903b8a40e636c7286d1b07699734eba046c5c1d916cd34322fc0c13823,0x122243c861ed2161dc848ac3d4bac8390520629aa02e40ecb84808ff1f97fc7d2dcbd46c45c0671f17947b2d63d06ba2,0x116a3d43d07f1c231458908e0d5397570920a2983b8a4a9a404728ff1b24647d2dd22c6c48a06722552432302df5be22,0x49d9383fa4dc9a1892664c49792d02a4ac0918725060c93925246483bb91e300278bf324ca8c8bba7724be4748d0922ec0ca4,0x43e87b1c41fc638c51607843907c3681e8438dd1501e33d2e40e81cc6d86d0d47699706c0d57445c06716c194320620c017a4] i))))) else (if i<288 then (if i<272 then (if i<264 then tableWord #[0x4a090d1c47b46393f27975c391ea3681ec839051501e33d2e45c4b84808ff1f97fc7d06c0d57ac5c2d916d7947b0623d06ba4,0x45a87a0fe31c629530e47a8da7092081e4782e4ec2542a694f29a1abb606f2957abad9491f251c3206328a50a0,0x8b51ea1e83f8e118a2c43907c36821c6e1df1e4b903b8a40e636c7286d1b0770ed32e0d97408d8b83b22d8328640c41823,0x43e87b1ac1fc638c51607843907c3681e8438dd15077c792e46601cc6d86d1b07699706c0d57445c1d916c194320620c13824,0x12da5acb49672ca58aeb9611546d4af95d10c1e33d0752b65603894a0d57ac409560ce550320623d06b9e,0x12e24303f8c727e2c2eb8723d46d03d7092081e33d2e40e81cc808ff1f97fc7d06c0d57acb70671f01947b0632886ba2,0x4b990d1c47b46393f16175c391ea3681ec839051501e33d2e40e81cc808ff1f97fc7d06c0d57ac5c06716c1947b0623d06ba4,0x4b987b1ac1fc708c51625f4397643681eb84905205d8b3d2e40e81cca794d1de5ecbc75eeba5dcba06722419432062eb1d5a4] i else tableWord #[0x46687d3063ac718c718a2c4398aa0f81e8438dd1515003c2e40ee2946d86b3025f83832e0d41a08d8b80ce2d8328640c417a4,0x4b990d1c41fc6393f27975c841ea368bac839052041e33d2e45c4b846d86d1f87699706c5b97445c2d91f17947b2d60c017a4,0x43e87b1c41fc638c527975c841ea368bab849052041e33d2e45c55346d86d0d47699706c5b9744b72d91f251c322d60c017a4,0x43e8f50f41fc638c527a420f59865d6611738dc0f19e9722e25c239c6d86d0d47699706c5b97416d8b85b23e4322d60c017a4,0x26bcd69aa4ee6a4d39a5346684cf99ce22669389980b66596226d3289ac1b2693266441a2ce5826395d98c4be62cc425c094ae25,0x87d0f65983f8c71887843907c3681e8438dd1501e33d9b60e81cc6d8bf0d476cda06c0d5744d9067360194320620c017a3,0x8b51ea1e83f9b918a2c43907d1bc21c6e0791e4b903b8a40e636c7286d0d47699734eba046c5c1d916cd34322fc0c13823,0x9e33c277cee9db3b08c1897c270e75cea9d33a273ce69caf0a724e312138a70ce07f33226f97a372190473ea772ee26f04a9ba4b82fa7] i) else (if i<280 then tableWord #[0x9f3138244f89ef3da7acf49e611021c4588910c1d8398853c82383806c0d41a44087f0cdcb1c708c0c4179f,0x227c4e0910f27ec4c89712a24cfc17011021c458890e22183b07310a7d84706e0d81a4fa87f0cc1983208c0c417a1,0x87d0f6810f68c718a808f08720f86d03d0871b81e33d9b60e81cc6d8bf0d476d0006c0d5744ff0673f819432062a6c17a3,0x4b990d1c41fc6393f160785049083d46d17570940c1e33d2e40e95346d86d1f87699706c5b9744b70671f251c7b2d60c017a4,0x4b9a1b1c41fc63a191607850b1ea36a854839052041e33d6840e8b846d8bf42476d0006d4217445c06741d79506a0a0c017a4,0x28ed1ca3746a8cceca3145e8b1290d54549405e0e54528992c25649c93301a254468850f2481905608ea1d378254dd08c1802fa5,0x43e87b1ac1fc708c5160784847651bcbab849052041e33d2e40e95346d86d0d47699734e5b97448a067225524323020c017a4,0xa5d4b69613ba574aa9493aa5149e4c3882700b6933fd2c44d692d24a4748a909672c257caf15da4147c97d1e25c0941223] i else tableWord #[0x53fa7d4f69e53ba754e624d3888c1129bba3a6c26a1c5352584ac48534a674c8925312fe23c4708da610fe14d2f08c0c42fa4,0x43e87b1c47b4638c51607854107c3681e8438dd1501e33d2e40e81cc6d86d0d47699706c0d57445c06716c19540062a6c17a4,0xa931daa44c187a0fe42c58a8f0e6a329e07a10e374548a60ee29039a8b5121b03832e0d41a54372d508e3c32062a7017a3,0x466a933063ac71a9d5362c439a98a781e8438dd1515029d2e40ee2946d86b302a583832e0d41a08d8a152a2d9c78640c417a4,0xa7f55aaad3caa84a69d5530d554a9c4460894dc4a09b1275469a92c1215429912524823c4708da6153e148460621802fa3,0x43e87b1c41fd5dab956e5f43907d5681e8439052041e4782e4edd5345186d0d6ac99775e0d57455876955dd9c320620c017a4,0x15aab4cb4ad159e58c4cacc6aab2d641b410eb1d6267a5c81d8af073586795602480e01b99706a0d046d5f0672a81939006357817a6,0x43e87b1c41fc638c51607854107c3681e8438dd1501e33d2e40e81cc6d86d0d47699706c0d57445c06716c195400620c017a4] i)) else tableWord #[0xaeb5d2b9d67ae55c6261aaae01106d043adf5899e9720762bc1cd6e08e4901c03732e0dab68340675b0190460635ac17a3,0x54987b1c41fc638c5162a3c3953c3681e8438dd1514eb3d2e40e81cc5186d0d6ac99706c0d6bb45006750819432062a7017a4] i)))
def orderGroups : Nat → Nat := (fun i => (if i<128 then (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x62b26a8e341041045,0x33673462c1041045,0x66926acc341041045,0xe33b2aa65587a10102045,0x38cacaa99954c8a10102045,0x39b2a9954c6a10102045,0xc2c8dc4cd2c7220408102046,0x30b237132c71e0408102046] i else tableWord #[0xe36ba98d91c7a22404045,0x33aa6655386890204045,0x34b237132c71e0408102046,0xe36c6ea631c7a22404045,0xe2caa999958d2c9a10102045,0x31a666554ce1e0408102046,0xe2ea5958b1c7a10102045,0x34cacaa68dc4cb1ca890204045] i) else (if i<24 then tableWord #[0xe31b2aa6658d2c9a10102045,0xe32b2aa5c553389a10102045,0x34c6c99d593388814302045,0x39b2a553386a10102045,0x32ae7656346890204045,0xd289a37195952c9814202045,0xe32b2aa66513349a10102045,0x38caea63654348a22404045] i else tableWord #[0x31a6665634b1e0408102046,0x33a65696386812204045,0x38cecaa9956388a10102045,0xc2c9a371a4ce349810302045,0x38b237132c71e0408102046,0xd2c96371a4ce349810302045,0xd31aa67195954c9814202045,0xdb1a9c6550c7814202045] i)) else (if i<48 then (if i<40 then tableWord #[0xcaa95a593347220408102046,0xca89a365634b220408102046,0x31aa66554ce1e0408102046,0x3a921719593348818484045,0xca892371654b220408102046,0x34c6a99c65655338a814202045,0xd32b2695a54d1c9910202045,0xd32b299a56951c9910202045] i else tableWord #[0x38c6caa9963588a10102045,0xe2caa96d6347a10102045,0xe2ea5958d1c7a10102045,0x30a666d63871e0408102046,0x38d32c5958d2c8c08102045,0x30b2371a4ce348810302045,0xe2caa96d61c7a10102045,0xe6caa65521c7a10102045] i) else (if i<56 then tableWord #[0x38a669573c6810205085,0xf3685a6552c7818502045,0x39d32b2a9954c8c28102045,0xc6a99855338d220408102046,0x32aa56953471e0408102046,0x30a6665634b1e0408102046,0x39d3258d2c6c08102045,0xe7499d593287814448085] i else tableWord #[0x31aa69585ce248810206045,0xe3292371a657349818102045,0x32a6695859334b260408102046,0xc2caa569654e2c9810284045,0x30b237133c6810302045,0xc2c8dc4ce347810302045,0x38d2999958e2c7260408102046,0x36a2171a553348814488045] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0xcac8dc4ce347810302045,0xeb4ce9956347c21204085,0x3ccb169958d2c8c18102045,0x3ccb1aa6953248c24202045,0x32b2a8dc4ce348810302045,0x38aa571a64e1c8818102045,0xe34b2695a54d1c9910202045,0x62b262ce341041045] i else tableWord #[0x35562ce2c1041045,0x3549b4e2c1041045,0x399b2ce2c1041045,0xe31ba99561c7a10102045,0x32a2569954d1c8810205085,0x38c6ea561c6a10102045,0x38d2ea5958d1c8a10102045,0xc2999958e2c7220408102046] i) else (if i<88 then tableWord #[0xcaca5a59334b220408102046,0xc2caa17133c7810302045,0x38a666d63871e0408102046,0x30a666573c6810206045,0x32a6665634b1e0408102046,0xc2d8dc693387810302045,0xd2c9a37132c7220408102046,0xc699a3656387220408102046] i else tableWord #[0xe6caa65522c7a10102045,0x33a666563871e0408102046,0xe34cb195a58c2c9c08102045,0x38cecaa99961c8a10102045,0x36aa3719553388814202045,0xe34b2aa5958d2c9a10102045,0x38d32c6a99955338ac08102045,0x34b237195952c8814202045] i)) else (if i<112 then (if i<104 then tableWord #[0xe34b234cd2c7220408102046,0x3ccb1aa99954c8c28102045,0x36b2a8dc54b1c8890204045,0x36b2a963611348922408045,0x38d32c6c99955338ac08102045,0x34b666562c6910202045,0xe31b2aa658d6389a10102045,0xe34b2aa5958b1c9a10102045] i else tableWord #[0x32aa56d7346812204045,0x34cb1a666d6348812204045,0x38d32c6caa964b1caa10102045,0xe74ca558d2c7c08102045,0xe2999734b1a0408102046,0xd2c9a5657387910202045,0xe34cac9a564e1c9910202045,0xc2999958d2c7220408102046] i) else (if i<120 then tableWord #[0xe36ba98d9147a22404045,0xe74cecaa6547c28102045,0x34b2695958e2c8910202045,0xe36c594ce1c7c08102045,0xe6caa6513147a10102045,0x38cecaa958e1c8a10102045,0x34c6a9a37195954ca814202045,0x34c6a99c65655334a814202045] i else tableWord #[0xe34cb1999553389c08102045,0x38d2caa999958d2caa10102045,0x38eeb966ad39af1cb75e6ccc14664262b1318284c5090a6c0404040404047,0x3969cd6eb4d72d979f2b05293118294c64b0d165c0404040404047,0xe3a3359ad3a3b96eb8e9b33050911a0b15098c942430505067c0404040404047,0xe3a7359ad3dcb75c7cac1424c662a1319284860a0e6c0404040404047,0x1c7769bb5a9cf72d939b2f05193198284c84c942430505067c0404040404047,0x1c7663bb4e73c6ebcf95828cc84c1623384c7090a640404040404047] i)))) else (if i<160 then (if i<144 then (if i<136 then tableWord #[0xe9b735cb75e7b96ccd59792a498d15829446098c16640404040404047,0xe3b3563bb4e73c6ebcf97828cc84c1623385498e12640404040404047,0x1e3af2d56acd79ee979d2f8519511525305490d0e5c0404040404047,0x1cb4e6b75a6b96cbcf958294889058294c64b0d16640404040404047,0x1d36e6b95e7bc72cd59b2f254991a2b05288c13165c0404040404047,0xf1c766ad3769ce78e59ae5a7ced14664260b1121325098e1a6c0404040404047,0x79d9aaed39cd19ae5a7cbd1466426091121325098e1a6c0404040404047,0xe3b315da739e335cb4f1b2e6e0a332130588909c26284860a740404040404047] i else tableWord #[0x76d9a72daaf35dad3e564a5222b25268b131a540404040404047,0x3c74e3bb4d9ad3dcb73e5e8a1263314c64b0e0e540404040404047,0xf1c7769b35a5c772dcf97a284682c5319284860a0e640404040404047,0xf1d3971dda6cd772d979f3345189098294c64b0e0e5c0404040404047,0x3e3cb9b97735ad6b6aa9e79e5cd68ecfe0c4b0a8a5a2948c866158523129230a42821100402008047,0x38b473ae6b2764de5cda9997cf4ecec0a0918c826251484638312415130d0a4201008040201008048,0x3e7cb9b736b5b4f3b1ed275cdb9756cd50e0d8d2c6c1b0949168624c4a494331240547024120801008047,0x3ab4f3ae6ba75edb95cf4ac2a8918c6a5146392c15132e0100a0401008047] i) else (if i<152 then tableWord #[0x3cbc7a39b977b4f271ef2e6d675a9a59d2d1e0d2c8c6c1b0a49c9185614a4328220943024210802008047,0x3cfa7976b5b3ae6d6b679ad9cce0d2c8c4c1b09894918c614a4629252343024080201008047,0x3e3c7938f6b675b4f3b16b27235e9e5cdad9d54f54e0d0c8c4c2c1988c62514a46383124231412090553008040201008047,0x3e3cbc7ab9b8f736b673b16b275e9e5cd9d796d54f55e2d0c8c4c1988c514a46433831241c1912054b008040201008047,0x3e3c7a7978f5b3af2d6b5e9cdad9cf4fe0d0c8c4c2c1948c62524a46383129252347008040201008047,0x3e7bb534f1655e9795cf0ecd4b43cee8d0c4c2c19158524638312c2a29140e05034b00a0401008046,0x3e3cfab9b675b3b16f275edb95cd4ee2d0c8c4c1948c524a4638312419130543008040201008047,0x3c38b735b4f3af2cebe7dc5b16534f4ed0d0c2b0a29c92918e604c41312c19130d424100803008046] i else tableWord #[0x3cfbb9f6b5b26f2e6d6b675acf4de2d2c8c4c1b1aca598944a4623093b028240201008047,0x3c79b978f736b66ee75e59cf8f4dc4c2a1996158382926231c1a053601008040201008048,0x3cfa7976b5b3ae6d6b679ad9cce0d2c8c4c1b09894918c624a463129252347024080201008047,0x3cbc74f3af2e675e5ad9d6d5ce8dc2b0918c61514a4643382422191412054201008040201008048,0x3e3c7a7978f5b3af2e6d6b679e9cdad9d0e0d0c8c4c2c1948c61524a46383129252347008040201008047,0x3e3cba7976b5f32ce2df1e9e5d9d57538b4ad2e0d2c8c4c1837855463229240c0a3b014080201008047,0x3d3cb9b36ae6e59e1c56ce4b4743cec4a292897048424128242119140d0b064201008040201008048,0x3b38b773acde5cdb97cd4acca091826862594e3124151332012080401008047] i)) else (if i<168 then tableWord #[0x3c78b574f3b36e6b275e5cdb97cf4ecfc1a0918c826251484638312415130e0d4201008040201008048,0x3cfa7976b5b3ae6d6b69e79acce0d2c8c4c1b09894918c86614a29252343024080201008047,0x3cbab9b8f675336daae9de5d9b9b574ecbd1e2d0c8c4c17068646154322a2623190d43018040201008047,0x3eb93875b4f36da7a6cccb47cce0d2c8c4c19a3228242116130d37008040201008047,0x3e3d367331b16e6da9e39e5d99d753cf4ed1c4b0888681704946393432230c0a053e0100c0201008047,0x3e7cfb3ab9b975339edb9755cd4de8e2d0c4c16a6159524c46312414130543012080401008047,0x3e3d33b36e6da3de5d93cf4eccc8c4b08986704946383432310d0b3a0100c0201008047,0x3e3cbc7bba7978f72eaceae9e75d0dcfe8e2a198918c8a898570646132262314422180401008046] i else tableWord #[0x3cfaba79b97675736ae9de9d9b974ee1d1c8c4c2858372686458544c2a260943018140201008047] i))))
def ordered (v : Nat) : OrderPage := orderPage plus minus 11 orderBank (v % 16) ((v >>> 4)%8) ((v >>> 7)%1099511627776) (orderClauses ((v >>> 47)%512)) (orderGroups (v >>> 56))
def ruleBank : Nat → Nat := (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0xe10004c012802200084005102003100032040042001212004c000082400901430202703284a40980021001212180c8000c813108122020870318002090c0240000049c40ca31101481954302027031a401224c041,0x40c2029008200280800188400a401021a8000a0a061314013800420028080009800404051200105180c065314013800c2a0002828084001802003100020800240184400880ca2004400810c005002003100030040042,0x100c08c0000231809800180601020003080040209401100086220402181840008444032000208080240006218440c00040121080e2104a103180050808064000a111004800100228818000002421028000a0a063,0x2009404c0000431081000280422011c220284043000640804c8000c8300810002056020104a408800431102010c082001420181900000463012000000464203902050c08200002018098002056110208012002043,0x308c84072046a1810400404a3032000402c440218440088086818405201844408163020800008060640006018040c9280260018c001a420132000348c02040952110008630a40110194e4081430308002008a046,0x10128c08400180118980c401028032888100860210004101004c000c801081000080232100c240044043000c00940c80010012809000280c81030004090a420310040a00c6a00028281040018025123000300ca206,0x418c04c000c6001008c500ce0021888402c60610010100c0c80000201809000184a610300000106420400240180c6001480181900001063012000501864201108010c082002085181080030024230088402c6021,0x3902350c0c2000401199006120022032800608c6062000e1510048001861189800020c231201c811a860210004121808c00242908188001902112000000104402480244980c222100218184c5004e002180002006046] i else tableWord #[0x118263840860020401018800408a202100080084260000803084800009044989000500421300c220044021000c118c0c8000c81319080030c2323000001906420480244980c6000025180980008c2332008012142043,0x494c82280ca000c8100188000902002100020900260000a13044080028880010800384052301ca34014065000600944c8000c0328811400050502184a909800430000308cc401290260010cc411028032800609c6026,0x50c0809c0c2001c25301910009006020a408224c0635012141408200280128190001802501200001a0e20600041214840a18d013818c005010002100090a4026000001014840000c88009900028cc33101c841a86061,0x490044a008600250430190001208601200002a4e206000644188409115043818d204112602080061a0e0460008341c04c0008044081000110482011880205004350c6809c0c2001008380980010c8810218832050043,0xa022004800102850818002900821024a14114063490044a00823088a11019440088a10218881288606100081104408002409381180012c88102000222d0402491644a00860010093809942024470309d044812065,0x660988400010010010800404001302001280c06311822384086a411224819542024470318002098c024001460988c08084c2301040010888102248222500434880821c0c29101243818ce82200903280090110064,0x8320048062806700084002888812300090a4a460490444a00c600004441098002048012024822250065000890800848084c23018c254844001080042040042000a131840c8084823018c25204400108009098c064,0x1002200404200144010108c45110803280062040062310640a00ca62008840195001900603184a00980021400650180c60001644109924591280329ca14014065001001140c800144640818000904831200091a40260] i) else (if i<24 then tableWord #[0x94083000427204aa1818400104040230000080802600020090c80000c43090080050441031080121420210006208448091010438194400900101080090902062000a120408400284108980005090112024a14114065,0xa1104408308861101946110c22021800310420260002341c408a18d013810cc2104e103080090982062000413980480018410890046088e1010800040ce6020002009408c00008109008001810003100024000240,0x184450880868184452018444094430208001184642040c232900c20010021100800180250230003484006200080588c08000825009000020821231000209cc0260014110408400184108980005082112019482052065,0x1444000c4001c030018800080c501200071800260000a300048012806600084000092a2130001208a024000a120048092892450194611150203288081142043494482280ca81854520184e40954302080042884402,0x14008c4c072040a18084000100831200081800260490044a00ca000c4808900614810202180080882062404261180c200100a0081000284e3013000029066400000128c08c000c25010086120102032a8090a0a061,0xb0848042005600810c001ac20132000358c02040956110008600142518190002104510328040a0a0633a08a0240ca001c20181880030023120000810040425080a11c0c670880a10084003046302100080806042,0x818c04c72200a18184e4201430308005080604600080114408000c2029008e11014203280070280062385605080ca00242429180003814002100020ac02405080a11c0ca0018012810800384051301ca14014063,0x2010880400084441098002004230220640148061185200880866108270818c0038941013000800842400a0c11180ca001062110080040403031000220880240008020c48000240918980442004301080004006046] i else tableWord #[0x10800c0c80019071809000198663011c8802860410010400c0c80018871809000304e3023000609c60240006139840c0004061908000310e30130004188220411862384086002040109900040c4103100071282240,0x4400c08c00042220118003840402100090248260429241240ca00042320118000844401300080946026001400904803520013819503080a401080000808046000a111004c0011020881046408e10218c220204065,0x6829840c8184072018400410a30320c2402040433908050c0823088a81010c00404e3032206111c80611102310c08200154440918002a8c8103188a22100630940130008600002b2011800320e301308880086061,0xd000100825020c00218002410c246] i))) (i/16) >>> (43*(i%16))) % 8796093022208)
def programs : Nat → Nat := (fun i => (if i<128 then (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x40180802005,0xe04018180a006,0x1a0c0582812086,0x221007828120e6,0x150a04c240e5,0x1a0c8602e165,0x1e0a074381b5,0x482311084401f6] i else tableWord #[0x5228138984a1f6,0x5e2e168b0562a6,0x321884c602a5,0x6c35110d040336,0x6c35110d040376,0x762e1d0e4702a6,0x803f1f0f4781c6,0x32189083a415] i) else (if i<24 then tableWord #[0x8a2e220e4862a6,0x9035238d08c336,0x4d2612c94495,0xa2352813c404e6,0xae562a950a6526,0x9a5b2d164b04a6,0x5f2f1743e5c5,0x62309743e605] i else tableWord #[0xcc651119040636,0xd66a349a0ce376,0xe06f169b8da6c6,0x5e2e168b0e2416,0xe06f168b056726,0xee763a9d096736,0xf87b3d1e4ba786,0x323f1f460415] i)) else (if i<48 then (if i<40 then tableWord #[0x824084d007f5,0x10e8642a11064e6,0x8a4480802885,0x11c8d4622cba886,0x903f1f51e415,0xf87b3d1e522786,0x904084d1e7f5,0x762e1d24d247f6] i else tableWord #[0x8a2e2224d287f6,0x1e0a048380e5,0x12e2e4b24d2a7f6,0x9a4ca60a4085,0x13c9d4e26c26086,0x9a05a7ca4085,0x1446f1d28524a06,0xaea55228d06526] i) else (if i<56 then tableWord #[0x154a95429d4c526,0xa55220d560e5,0xa5522b0a40e5,0x15c040181802ad6,0xb25880960af5,0x170b75b2d568b36,0x17cbd5e2ed74b96,0xb25b3017eaf5] i else tableWord #[0xc25b3017ec15,0x18cb262b1186af6,0x326384c242a5,0x8263b2992c85,0x1a0cf6733598cb6,0x401b440aad5,0x401b45a4ad5,0x18cb26aad5a8d36] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0xd86bb4402d65,0xd86bb45b2d65,0xb26ab69a8af5,0x906384db62a5,0xde6e975b80e5,0x1c0d86bb7c02d66,0x9063b29b6c85,0xe471a45c4e15] i else tableWord #[0xe752175cce55,0x1d4de523a5d00e6,0x1da5676151d6526,0x1d4f1783bdd0ee6,0x1e65679151d6526,0xa507bd0a40e5,0x1ecde523a5ea0e6,0xde6e974ce0e5] i) else (if i<88 then tableWord #[0xa56ebdca41b5,0xde6e974cef85,0xa56ebe4a40e5,0xa505a7ca40e5,0xde6ebe9f20e5,0xaea56ea8cce526,0x1f8e471ba5f6086,0xde71a45c40e5] i else tableWord #[0xde523f5580e5,0xfe44bd002885,0x209038140600ff6,0x1043a82497055,0x10483c1896ff5,0x1043a82497085,0x150a04c60f85,0x2130381405e8ff6] i)) else (if i<112 then (if i<104 then tableWord #[0x21b0c85c28244a6,0x821884c250e5,0x1118804c250f5,0x2261e0a448601c6,0x154a9544514c526,0xa507bd0a41b5,0x150a1f460f85,0x150a1083a1b5] i else tableWord #[0x231178145805156,0x11c8dc6a32885,0x109838263b155,0x9e8fc79b6e15,0x213178145805156,0x249239148641156,0x21b2585c29b64a6,0x1098382497155] i) else (if i<120 then tableWord #[0x9e9304d92e15,0x909384db70e5,0x1288f84db6e55,0x2523f1f0f4961c6,0x4d9512c94375,0x4d9612e564e5,0x4d984be5d2d5,0x13c9d4e47e3ce16] i else tableWord #[0x9e9304d00085,0x4d2612e65315,0x4d2612e564e5,0x1a0c0582812e16,0x9e9347992e15,0xa505ccca40e5,0x1593479920e5,0x15934d6680e5] i)))) else (if i<192 then (if i<160 then (if i<144 then (if i<136 then tableWord #[0x2733805cde6c0e6,0x158fc79b60e5,0x27d3d9e4ede93a6,0x13f9320038085,0x1e0a0c038f85,0x1e0a04a800e5,0x1110a504240e5,0x2862e1d509247f6] i else tableWord #[0x28745a250856c86,0x150a1f4240e5,0x28745a3508570e6,0x148839628f155,0x148a55268f155,0x90939f5b6415,0x14da652df33a5,0x150a7b44034e5] i) else (if i<152 then tableWord #[0x151a7808025c5,0x15444b46a7525,0x2ad50a7d55a25c6,0x150a7d5c025c5,0x2b435ac8d2b0376,0x2ba2eae0e6b62a6,0x321890abc415,0x2261e0a57ebc1c6] i else tableWord #[0x162b0b46c0165,0x236507d92c60e6,0xa5b34cca40e5,0x1680a59c240e5,0x1680a5a4240e5,0x2d82eb5da92a416,0xe06f168b0576d6,0x321884c3a2a5] i)) else (if i<176 then (if i<168 then tableWord #[0x2e16f168b0576e6,0x5f2f1743f4e5,0x62b91743f715,0x2eb742f5ce965c6,0x5fb93a03e5c5,0x4dbb47494375,0x179bc5de33525,0x52281389af41f6] i else tableWord #[0x4d265ec94335,0x4d9512ef8375,0x90be84d1e2a5,0x2fd74b95cdd05c6,0x30581c05fc79476,0x185c25a706725,0x10f88c3e19cc376,0x2862e1d508702a6] i) else (if i<184 then tableWord #[0x90c25a7062a5,0x3122e220e4862a6,0xd788c3e19cc376,0x3178ac3e19cc636,0x31f8ec3e35cd8c6,0x185c264306725,0x90c94d7222a5,0x32993168b0564a6] i else tableWord #[0x198cbe5883955,0x3359963c29b64a6,0x19dce66dd7955,0x33d931d0e4704a6,0x33f85c242b06726,0x21b9963c29b64a6,0x18563da5b6725,0x33d931d508704a6] i))) else (if i<208 then (if i<200 then tableWord #[0x33d93220e4864a6,0x18563d05b76d5,0x148c00f28f155,0x1a163e41b7a05,0x5f2f2443f4e5,0x5fa78043e5c5,0x2862e1d509242a6,0x4d2c96094335] i else tableWord #[0x345931d509244a6,0x32993168b3464a6,0x762e1d0e5247f6,0x5f2f2443e5c5,0x34c56d295348526,0x1a99512f51a75,0x4d986a894375,0x1ad266b095ab5] i) else tableWord #[0x1a99512f5c375,0x3606ad79a158376,0x5f45a36cb622a6] i))))
def panel := readPanel plus minus 9 8 ruleBank programs
def data14 : Nat → Nat := (fun i => tableWord #[0x1ff,0xc403] i)
def data13 : Nat → Nat := (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x3ff082,0xd853868e8606,0x3ff0e2,0xe81127050506,0x3ff102,0x10b390c60506,0x3ff107,0x100601122c50207] i else tableWord #[0x3ff420,0x1041431e341019c09,0x3ff440,0x41060a0e21a07,0x3ff460,0x1041829a011019b09,0x3ff480,0x4105351019b07] i) else (if i<24 then tableWord #[0x3ff4c0,0x1041430b3c0c21a09,0x3ff4e0,0x8286071049a07,0x3ff500,0x42820d1019a07,0x3ff462,0x6390ce8505] i else tableWord #[0x3ff482,0x820a1a1c407,0x3ff4a2,0x41060a2620307,0x3ff4c2,0x4106170c21d07,0x3ff4e2,0x10602161c406] i)) else (if i<40 then tableWord #[0x3ff502,0x8604161c406,0x3ff4a3,0x289371018706,0x3ff4e3,0x41050c021c407,0x3ff4c5,0x820a18488080c59e0a] i else tableWord #[0x3ff4e5,0x41430a0e2620308,0x3ff505,0x2143020e2620308,0x3ff507,0x1430105021c407] i)))
def data12 : Nat → Nat := bookData 2 5 5 (fun i => ((fun i => tableWord #[0x4201024e34824a35004405055024c24a24e04601070e2082,0x5074e54c54e24624c0480] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0xdffefffdfdfefffdfff5ffbf73fedfdefbef7f6ff5df,0x7ff] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x46150d381235254094890252500948c6252238948022528305498a1525005490815231854844152008549400,0x4c280d406034e180d392094c28254060948182541de850779d399c65026994a1054a46153916452840d38d43,0x4e481540a054c28153920a4c282939a044e481140e044e381140a044c281120a04501811386044e480d31203,0x4c283120a0a50480d39a084e682d39a0752581d416074e481d30e075058193920650381928e0650281939a05,0x48283c41e0f4e58393920e0e483941a0150480441201507801416004e5801316001078014860d4a481938e06,0x50382538e094c382540a094e282520a094e1825186094418244a20912782441e0950783d38e0f50283d38a0f,0x10784040a100e284141e0350680d39a0350280d38a0348280d1060310780d41e0950682539a0950482531209,0x50684139a10504841392104c484140e104e384130e1050284138a104c284120a10462841406104e184110610] i else tableWord #[0x4c481130e044e281118a0410281141e115048453921150384538e1150284538a1148284518a110e284541e10,0x4e68294120a4c482940e0a4e382930e0a50282938a0a4628293860a12782848a0a0e282941e0450681141204,0x52083049e0c10783141e1250684939a12505849396124c5849412124e4849312124a484841e1250782941a0a,0x4e28144a2051248144120552783141e0c5258314160c4e58313160c52383138e0c4a383140a0c4e283128a0c,0x52184d4821312884c492135078193960650481938a060e481941e05506815412054c481540e054e381530e05,0x52684d41a134e684d4961350584d396134c584d4921350484d3921352384d40e134e384d30e134a384d40a13,0x50781d49a0750681d396074c581d4920752381d40e074e381d28e0752181d4820712781c4920752884d41e13,0x52883541e0d52683541a0d4e68354960d5058353960d4c58354920d5228354820d12883541e0b50682d49e07] i) else tableWord #[0x521405481015254014810052585948e165228594821612285941e0812482048a0850785541a154e685541e14,0x5004c12012352842548d094826a5381294604a51012f523409481025264394950e5214394810e52640549101,0x52743d48d0f52243d49d0e5244394a10152540549d004e35cd30dc612353138d524826c9411ea50049140131,0x525449491125284114a111527445311d152844149d1052644149d0352640d4910348350d49d0952642549109,0x50379d4a1135026cd4a10652741949d05526415395854a3615389a55274314950c5026b14a11252744949912,0x528455415955274514159452843540d4d52842d49d0b52642d38d4b] i)) (i/16) >>> (22*(i%16))) % 4194304) (fun i => if i<61 then (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x51c06091a1d06,0x1c0509011a1d06,0xa011c05091d06,0xa011c05091d06,0xa011c05091d06,0xa011c05091d06,0xa011c0b05091d07,0xa011c05091d06] i else tableWord #[0xc0201090b1a06,0xc00a020b01090c07,0xa020b01090c06,0xc00a020b01090c07,0xc01c0a11010c1a02090b120b,0xc0213090b0a06,0x85070ac41a05,0x5061d830e1b4407] i) else (if i<24 then tableWord #[0x5060a1bc40e8307,0x42060a85c41a06,0x83c41a03,0x30685c41b0906,0x4283011b85c40907,0x841dc30b04,0x410405c31d0b06,0x1091c410585c3c408] i else tableWord #[0x870118c40905,0x81420a0c1a1c06,0x81864c0a440c0d9a831c0a,0x814486264b2c831d08,0x82420a1c38c41a07,0x42860c1b0a22839b1c09,0x81864c080a0c22839b1c0a,0x814486211a4b0e831d09] i)) else (if i<48 then (if i<40 then tableWord #[0x42060a341b1d4b441a09,0x42061c381bc4321a08,0x4283452d9a445c0a08,0x45861c0a449a4b835c09,0x82428a830f0a20c41a09,0x42865d1a1d834b89449a0a,0x861c0a0b1a4583c4899a0a,0x4245071fc40a121a08] i else tableWord #[0x70a45178a1fc41a08,0x42834539c40a1a07,0x4283453c4b9a440a08,0x81860a1d16445d839a0b0a,0x85450a0b39c4321a08,0x814486274b2c831d08,0x8142860a1b1e100b051c832c0c,0x82428501291c1bc436090a] i) else (if i<56 then tableWord #[0x428601191b2c444b1d090a,0x4184463bc32a0b1d08,0x840b232a43471d07,0x418446083323c30b1d09,0x821a1d090b46c3848b9d0a,0x4146181b1d37844985430b0b,0x81351a2cc30b1d07,0x410b1a1c09828546c3c40a] i else tableWord #[0x41461b1c02490c18850b430b,0x418246090b1cc485432c0a,0x86463b091dc32c0b08,0x429b44874b1d0907,0x45861b1d48090b07] i)))) i else 0)
def data11 : Nat → Nat := bookData 3 6 6 (fun i => ((fun i => tableWord #[0x4c24e04c24405014405024c24c24a24e44e05024e05014e04c24605014604e65054e65025255024e45024614604e0460,0x4e64a24e44a25024a24e45004c25004e64e05034e04e34e04824e04e14e04e44604c44604e14604e44404814404a34c2,0x5201075075055075024e64c25284a24a44a25284604e34605251075221074e64a35055024c35025054c24e44c25034c2,0x5231075280e25260e25250e25240e25230e25210e25200e2525082] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xffdff7fefbfffffffbf7fefffbfdffffe9ffb7fe7fbf7ff6,0xbfbef7eeff77febdfbcffdbfdefdf7dfdddfefbf6fdfefdf,0xaff] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x4e624a4e42495022085281874c41c75281864c21404e11405070851491055070841470c35070825470414e3000461000,0x5072cd5042cd5072d11072d14e42d04e42cb5032cf4822c84e42c74e42ce4e42cd54528c52818b4e61cb50228b54624a,0x5042c64e42c65072d35042d34e42d35462d25062d24e62d25422d25022d24e22d25412d24e12d24412d25072ce5042ce,0x5022c84e22c85042d65032d65022d64822d64e62d55022d54e22d54412d55072d45022d44e22d45072c75042c75072c6,0x4e32cf5022cf4e22cf5482d75472d75072d75462d75062d74e62d75022d74e22d74c22d75412d74412d75072c84e32c8,0x5062c94e62c95442c95042c94e42c94c42c95432c95032c94e32c94c32c94e22c95412c94412c95072cf5042cf4e42cf,0x4622da5462ca5062ca5422ca5412ca4412ca5072d95062d94e62d94e22d94412d95062d84412d85472c95072c95462c9,0x5042dd4e42dd4c42dd1442dd5072cb5042cb4e62dc5022dc4e22dc4e12dc4412dc4e42db4e32db4e22db4822db5042da] i else tableWord #[0x4a42cc4802cc5042df5032df4832df5462de5062de5032de4c32de5422de4822de5412de4812de4412de5072dd5062dd,0x4e52e15042e15432e14e32e15422e14e22e14822e15402e14802e14e52e04e42e04a42e04802e05072d05042d04e42cc,0x5202c24c02c24802c24202c21492c24e52e34e42e34802e34e32e24832e24e22e24822e25482e15072e15452e15052e1,0x4412e41242e45492c25272c25072c25452c25252c25052c24e52c24c52c25232c24e32c25422c24e22c24822c25402c2,0x4602c45072c35062c35042c35032c34832c31442c31242c35272e45242e45232e44e32e44832e44e22e44822e45212e4,0x4811a64611a65401a64801a64601a64401a64201a64822c54622c50822c55042e54822e54e52c44a32c44832c44802c4,0x4e014e52818d52718d52418d48228d4e014d4831a74821a74621a74811a74611a74411a70821a75441a64831a64821a6,0x50725254631250435254231248235214919254830e52818e54730e52718e4e61ce54430e52418e4c41ce50228e48228e] i) else (if i<24 then tableWord #[0x5241934e33934833934801535073815023814e23811073815071405061404e61405021404e2140501140441140548312,0x5473075271874e61c75443075241874e33874833875022874801475271865241864e3386483386480146528193527193,0x5483145473145061d45043545073a85063a84e63a85043a84e43a84c43a85023a84e23a84813a84413a81483a8548307,0x5013d64413d65001564401565071a95061a94e61a95021a94e21a94411a9548315507255504355543395542315482355,0x4c31cf50228f50014f5483175473175463174e43575022975423085483165281965241964e42565423165221964e2256,0x5032095221894e228954014950014944014914918914724954830f52818f54730f4e61cf52418f4e424f4c41cf54330f,0x5463194c33995483185463184e62585033985423184e2258462398549189528189547309507209524189543309523189,0x52219a50015a44015a54824a54830a50724a54630a50624a50434a54224a4e224a54124a44124a14824a14224a10224a] i else tableWord #[0x54831c50725c50435c54231c48235c54131c14919c52419b50421b48015b54831a52819a50725a5061da52419a52319a,0x4e541d54431d52419d4a441d4e229d48229d54830b54730b52718b4e540b54430b52418b4c41cb4a440b4e228b48228b,0x54631e50435e54331e4e325e54231e48235e14919e50642a50442a50342a4c342a48242a44142a54731d52719d50721d,0x14728c14428c0e428c5061ab5041ab5031ab4c31ab4831ab4821ab4411ab54831f50725f5061df54331f54831e50725e,0x54728c54730c50720c4e528c54428c54430c4e428c4a428c54328c4e328c4a328c48328c4e228c48228c54028c48028c,0x4823611491a15473205443205042204e33a04833a05483105281905473105271904e61d05443105241904a44104e3390,0x5443224a44225491a15483215281a15271a15072615461e14e61e15453215043615433215231a14e32614c31e1542321,0x4822821491825271a35072235241a34e22a34822a34e51ec4e31ec4831ec4e21ec4821ec4801ec5473225072224e5422] i)) else (if i<40 then tableWord #[0x5072244e54245241a45433245231a45032244e22a44822a45491825271825072425231824e32425422825423024e2282,0x5473035271835072035261834e54035241835433035231835032034e22834822835211831472431241835473245271a4,0x48022d46022d44022d42022d14922d14422d12422d5271845072045241845231845032044e2284482284520184149304,0x52422d54322d52322d4e322d4a322d48322d54222d4e222d48222d54122d52122d4a122d44122d54022d52022d4c022d,0x48222e46222e54122e48122e46122e44122e08222e5483255072655061e554622d52622d54522d4e522d4c522d54422d,0x1045725064715044714c44715075305065304e65305074cc50448a44000146146f54622e54422e54322e48322e54222e,0x5005f44c05f41485f45065b35045b34c45b35005b34c05b34805b31045b35065725045724c45725005724c0572480572,0x4806771446775046365006364806365065355045354c45355005354c05354805351045355485f45465f45065f45405f4] i else tableWord #[0x5406a64806a64606a64406a64206a61446a60826a648246f46246f48146f44146f5466775446774c46775406774c0677,0x4805b84405b84205b81425b80825b85446a65441265436a65431264836a64826a64626a65416a64816a64616a64416a6,0x4826d11491114835274825274625274815274615274415274805274605274405274205270825275425b84825b85405b8,0x14911f14911e50475c14911c4e44975285a85440684e47285225a84e27284800284400285225814800014826d2149112,0x54382d4e24ed4824ed1491045491025427c24826c21491025037a35034cc] i))) (i/16) >>> (24*(i%16))) % 16777216) (fun i => if i<28 then (fun i => (if i<16 then (if i<8 then tableWord #[0x21614070fb113a1a07,0x2140e1fe2028561a07,0x8a02e0c1c1c05,0x101024160ec2d1b87c409,0x4c6a141d106862c07,0x81219e18b0760b07,0x241c2c058c4281507,0x18a4064120b05] i else tableWord #[0x1071c029391a05,0x6241d3b1a04,0x10d081e931342206,0x88864d26c962306,0x5110c3b0e92d342307,0x483b16513065c06,0x281ce0c649a05,0xba201c829891a06] i) else (if i<24 then tableWord #[0x11a10313063005,0x4b0f0bf062c05,0x102441792d122c06,0x511024b17a263a2c07,0x10b150bb082c05,0x14486131342505,0x4b4d09a882c05,0x5110c4b108c8469a07] i else tableWord #[0xc1d121820122683c5c08,0x288871987cba9a06,0x1024ba209d122c06,0x3088b15124602306] i))) i else 0)
def data10 : Nat → Nat := bookData 4 5 5 (fun i => ((fun i => tableWord #[0x5074e65021475255025074e45025024c24a24e64e44e04e45024e05034c24e04825014e05474614604e34e04604c24e04604e45014405025014e05455024c25464e44e04614e0460,0x1494e65055074e6505] i) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => ((fun i => tableWord #[0xdbffdefedf77fe7ffbef7ef7fefdf7febfedfebf3fddeecff7f6,0x3cd71ffdafe9ff6f797ff3dedbfed737ffbb7fd3fb7f3f] i) (i/16) >>> (13*(i%16))) % 8192) (fun i => ((fun i => tableWord #[0x502299404a64412995a105567415398e54e3295408c5507281408a04e2281208844e418c59c4216808559c00,0x56262d30a0b4826ad519ea5446a9411aa4c2729209aa16a6294094952458d3894316718d4094850749d418a6,0x5201b53006d4801b51806d4401b50806d1691b45246d4a48892922c4c2804509e156862d521eb50682d411ab,0x4837b95246d5651b55146d5251b53146d5631b548c6d4a31b55886d5421b53086d4a21b52086d5601b55006d,0x5631c1588704821c1188700821c15946f5641bd2906f5631bd28c6f4831bd5806f4801bd1806f5047b940dee,0x4a4db948f0e503d3920b2e521c384930e542bb530aed482bb5512ca482aa85aa8a4e699938a6650190110640,0x120bad562e4520aef526c394930e] i) (i/16) >>> (22*(i%16))) % 4194304) (fun i => if i<4 then (fun i => tableWord #[0x8581d0a2701f05,0x160c83803,0x190dc2c03,0x942802] i) i else 0)
def data9 : Nat → Nat := (fun i => tableWord #[0x267f18b4e45025014e0,0x0,0x3e6b4824e45025014e0,0x0,0x363f4c21685464e44e0,0x0,0x375b4a41675455024c2,0x0] i)
def levels : Nat → Packing
  | 9 => (4,5,6,0,0,0,0,data9)
  | 10 => (101,4,6,0,0,0,0,data10)
  | 11 => (714,3,6,0,0,0,0,data11)
  | 12 => (346,2,6,0,0,0,0,data12)
  | 13 => (23,1,6,0,0,0,0,data13)
  | 14 => (1,0,6,0,0,0,0,data14)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=11331360871622741984 then some (3,0) else (if v=11630591039243279332 then some (2,0) else (if v=12330299553121185554 then some (1,0) else (if v=12789442486860014305 then some (0,0) else none))))
  | 11 => fun h => smallSlot h 64 204 7 1 (fun i => ((fun i => tableWord #[0x10000001110102010200000800000000,0x10200000002020000010400000500,0x50000040400020100050401000d0300,0x70210010100000100010100070200] i) (i/16) >>> (8*(i%16))) % 256) (fun i => ((fun i => (if i<8 then tableWord #[0x22888817c000004c80000000061a00000000,0x644eb02952fb7d9345eb2e0016080001e0bc00000000,0x69f15ba3d06c9d916d6ce4fb510a9921775ec6404113,0x1ca95be38c3e00000000d6c459a515b62400000000,0xc1c0015e71820a0000000000018800000e4e0008d000,0xc0f2e0000000002591f8000000000000000053049d60,0xc8000024846a12d2330bb0003c4595a0b0420831dc02,0xf3fda8d9838c111d51086d56b1631b] i else tableWord #[0x1a5c290000011e40c0aa82b8a00000000357000,0xc92ec0001646c40000000010c0023e000d4400000,0x8662e40a80000198f9c9818ba94f32a0fc3a0000072d,0xc62001ac923a4c0011afb4a4a33400350ab155e9ea03,0xa9ea8000002b80039a5308824dc00000] i)) (i/16) >>> (11*(i%16))) % 2048)
  | 12 => fun h => smallSlot h 712 2899 10 1 (fun i => ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x2000000000000000000000000000000000000,0x1000000000000000000000000000000000000,0x0,0x1000000000000000000000000000000000000000,0x0,0x1000000000000000000,0x1001000000,0x1000000000000000000] i else tableWord #[0x1000000000000000000000000000001000,0x1001000000000000000000000000000000,0x1000000000000000001000000000000000,0x1000000000000001000,0x2000002000000000001000000000,0x1000000000000000000000000000000000,0x1000000001000000000000000000000000000001,0x1000000000000000000001000000000000001000] i) else (if i<24 then tableWord #[0x1000000000000000000000000000000000,0x1000000000000001000000000000000000000000001,0x1000000000001001000000000000000000000000000000,0x0,0x1000000001000001000000000000000000000001000,0x1001000001000000001001000001,0x1000000000000000001000000000000002000000001,0x5002000001000000000000000001000000000000] i else tableWord #[0x1000000000000000001000000000000000000000000,0x1000000000000000000000002000000000000000001000,0x1000000000002000000000000000000001000000000000,0x1000000000000000000000000000,0x2000000000000000001000000000000001000000000000,0x1000000000000000000000000000000002000000003000,0x1001000000000000001000000001000000000001000,0x1000000000001000000000001000000000000000000000] i)) else (if i<40 then tableWord #[0x2000000000000000001000000,0x1000000000000000000000000001000,0x1000001001001000000000000000000003001001001000,0x2000002000000000000000000000000000000000,0x1000000,0x2000,0x1000000000001001000000001000000000000000001,0x1000002000000000001001000000000000000000000000] i else tableWord #[0x1000,0x1000000000000000000000002000000000000001001,0x1000001000000,0x1000000000000000001000000,0x0] i))) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => (if i<128 then (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0xe800000000000000000000000000000000000,0x43e0000a0442540000000000000000000000000000c1a8000,0x4706ac200000000000a0c00005820000000c0280000000000,0xc84000000000006a90000000187700036480003a1d00000000000000,0x8aed9a4ca8000000000000000000000223100009a500000000000000,0xde426000000000000000000a3ae037b03000000000000000000,0x38e40000000aa5c00000028500001ced000000064d00bd,0x434c00000000000000000000000000000000000000] i else tableWord #[0xe2500000000000000000000000000002a8b017d99900000000000000,0x1251000000000000000000000000002e00000000000000ab02607,0x862000008700000002de80000000000000000001ec00000000001038,0x182500011c80000000042c000000000000000000000000,0x3c8b000000000000000000000000000046fb967c598000000283c,0xc36c0000000000000000000000000000000408b8a900000000000000,0x1a8901700000000000000000000028d48005cf352a8000a230000,0x3a56c7d4a80a4aca2e04cea860000000000000000000004a60000] i) else (if i<24 then tableWord #[0x1249e4eeab4c7f8000000000000000000000000454c0004af0000,0xa16400022d0000000000006181ad00030d9000000000000000000000,0x208500000000000000,0x47f000187c00000000000000a0abc3f000000000000000000000,0xa2e32090000000000000000000000000000000000000000000000000,0x698c00000000000000000000000000008b50000000c7da9a20000000,0x7159e300010d0000000017a8000676c00000000004685277,0xc57c17c56d400000000000000000000000000000000000a6a0000000] i else tableWord #[0x2a870000000ca7400000000000000000000000000000000000000,0x308a00002a80000000000310600000000000000c84b0f30000000,0xcae8080e838000000000000000000002169000320a00000000000000,0x4a580000000000000000000000000000000a73800000000000000000,0xca491de000099d9acc0088a440000002deb000000026980000000000,0x4772ac80000000412400024fc9bb6025039e808000,0x0,0x87660720003994000000e1500000e9bc0002b280000000000] i)) else (if i<48 then (if i<40 then tableWord #[0x286d8a519230000000000000000000004594000,0x830a4dc00000000000000000000011400028f0,0x10b10000000000000009140000000000,0x1cc000000000000000000000000000000000001018a7a0002ac9,0x43f80000000000a908000000000067c400000018230000000,0x8a4c00000000000000000000000061680004154925213646f0242073,0x64e000009c51360002657,0x18a868d5a5d00000000001010000112c00000000000000000119b] i else tableWord #[0x82600000000000000000213c00000000000172045c000000396d,0x19240000000000000000000000000000000000000000000000000,0x20830000000000000000000000000000a369086,0x65308b008b40000000000000000000019afc7ac000e5100000003435,0x199f0001aa100000000000000000119c00029c300039bfb170000,0x58f2ae13b800071e80000000000000000000000000000000,0x7a80000000000000000000000892c7880432a880000000000,0x289a00000000003852] i) else (if i<56 then tableWord #[0x82bf1e643aba19c856d9400000000000000c2e400047480000000000,0x28bb000000000029c4000000000000000000226a2b00008aca18b,0x304600000000002a28000000000000000001844c72e21e0000000,0x95100000000003a6100000000000000,0xa26c0000002a68000000028680000002084,0x1060000327e0000000000000077240000000000000384b0000000,0xc28c00029d000000039978754000000158f00000000000000,0x817d63000000000000000000000000115500010cd] i else tableWord #[0x77a400000000000000000000297e249bd477a7c0000000000,0x652c0000000000000000064e400000029d312eae060000000,0x310000000000000000000000000000000000000000a4c80000000000,0xa6e4000000000000000000000000a95c0000000000a009278000014e,0x4680000000000000000077fc4a100034b6000000044f4827,0x85e67e32b80000000e32800020c8000e7e400077b0000,0xa63800000000000000000000000000000000003076d105cb3,0x180c92e0000000] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0xd04000000000000000000000001f0000000000000000000000000000,0x422000000000000000000084400000000000000000c6f40000000000,0xe62a07800000005674000000107f000000000000008b040000000000,0x11faaa7a600000000a88c000000000000000006ab40008858491,0x2406a67000000000000000000000e9c00000000000eaa8000e3b8000,0x8d600038a484780000000000a3751b60000000,0x2394230030400000000540000000000387100038e900000000003047,0xa246e004a16605000000000018e60000107231942f] i else tableWord #[0xa86c000554800000000000000000885c0000000000000291d81bc000,0x80f8000000000000000000003227f428000000182f00000000002a24,0x2740000000000000000000000000000181da802273,0x39f2000000046cb056000386500000000003113,0x10ecc99800000000000000000a49c0000000000,0xc0a3a7d89b4874e1891750002a9b00000000002aab0000000,0x4bb0678000000000000000000002abd0000000,0xd808000000000008f8000e8d8000a804000000000000000000000000] i) else (if i<88 then tableWord #[0x67b80000000000a7b40000000000000000000008e700000000000416,0x45a8000c97800000039d70a38000000000046e325a884c00000028b7,0x6718000000000096e923f0000000d4bf1ef05fc00000038c400021b7,0x39570000000868c000253c0000000000000117a00000000000000,0x388772bc0000000000,0x607000000000000000000000008f00000000000000000000085e4000,0x214494ad1f96a100000000000000a4fa079,0x184cc40a90e00000000001ab90000000000000000000000000000] i else tableWord #[0xe73c0000000000e01c0000000000c9d8000000302d02b40000000000,0x3520000000301a9a8f1cda62509c00000000000000638800083f4000,0x323b000000006a00000000000000000000000000000000471c000,0xa5811d4000000000009b3000000000024ff00000000000181000324f,0x319848230a000021040000000000000000000210002864,0xa8180000001916000000000022370000000000000000000004274000,0x8640000a446908000000082e80000000000000000000000000003057,0x38f7625c00000029ac01c11730000000c9bb8c70002cb9] i)) else (if i<112 then (if i<104 then tableWord #[0xe7cc0000000000000000070040000000000000000000000000000000,0x1919085000000008cc84bc00000000000000000a9281400000000,0x51e487b00000000000000000000000000000000000,0x3bc0000000000,0x1818078593100000000001063464d11563d800000031f000018ab,0x1174945584a0001a48802c0000000283000000000000000000000,0x311829600000000000261000000000000000000,0x47a72400000000a504000830800000030bf0000000000000000020f5] i else tableWord #[0xc9d4000000115800014b5000043a0000a90cad50f187630c040582c6,0x820692d000000046e800000000000000000,0x2013000017600020ed00000002b1d89900000000000000,0x24c000000000000000000000398557bda7c0000000,0x20c3034497b000000000000000000000000101e00000000000000,0x80d0000a658000000000000000000000000,0x214600019910001c5b0384000000000000000005a740000000000,0xa0db21f0002105837c0000000000c5c000000024110000000] i) else (if i<120 then tableWord #[0xa8d0000000000000000004708000ea3400068e3a290002a2a0000000,0x250c0000002a7b0000000000342900000000003d3500011d1342f068,0x22b300000000000000000105b00000008ac38190000000,0x1858000000000000000000000000000002b80000000000000398d,0x183d26a8000000120300000000001992e015003,0x1a39000095400000000000000a0ac0000000000,0x3a0797b8000000000000000fb00001290002c0f0000000,0xe0fc000000000000000008487980] i else tableWord #[0xaa700000004380000000000000000000000000e284000,0x22380005ad000001091ddc28907d000191c000000000000000000000,0x8508000000000000000000002d0000000000000000,0xc22c00000000000000000000117dc91c000000193549c8000,0x16f000129900000000000000000000060e80b6860fcb1,0xc9675b0003c0000000000682c000000000000000000000000,0x96c0f9000000000000006a20000657695900000000000000,0x3abf00b000000002c500000000000000000000000000000000000] i)))) else (if i<160 then (if i<144 then (if i<136 then tableWord #[0xc360000c3490f280d4000000000063fe8cb00000000002a46000111b,0xcac590d00000000000000000200d220b9680000000,0xca7c000000000000000008a040000000000b0f0000,0x405c00043f00000000000000000000000000002253,0xb2c0000879c0000000000000000000000000000a040000000000389e,0x320000000209f00030ce000000000039a7000000000000000002a2c,0x21b0000000000000000002a4100000000000000000000000020f4,0x40c4000000000000009c90000000000000000000006048000a35c000] i else tableWord #[0x2abe00000000000000000000000001da00019fd00000000000000,0x558000e8cc0000000000000000000000004758000c990000,0xc90e1000000000000000181b89af1e466ad1ae,0x4a540000000000000000009480000000000,0x2608150f2e328ca5b00000000000000000000000000003282,0x39e8c93b845c25400000000002424000000140348340000000000,0xaa30003a3a0000000656c0000000000000000000000000000000,0x297700031e0a79400000000000000000] i) else (if i<152 then tableWord #[0x167b1450000000000000000000000000000,0x283c0002a2800000000000000000000000000000000000000,0x296b0000000048800000000000000000000341c,0x21b000000000000000000000000000000000000000e138000,0x1093000000000034b4044000000000000000ab7,0x75e98fa00000000000000832400000008c5014c0000000000000229a,0x28f00000000000e9100000000000a970000000099545882222521a20,0xa980000000000e590cec0000000000000044a800000000000000000] i else tableWord #[0x84e8000000000000011200000000,0x44019b5029c000ca1000000000000000000000216e67e80000000000,0xd17000000000000000000000,0x290300022af47d000061b800000000000000000e43d029,0x62cbdb10000000a17619a0000000b40c9120000000,0x1128f0e6243a1d698ce9fc0000002cae633c00000000000000000,0x2a9e0000000e0919fb01a400000000000000000000023d9804000,0x8104000000000090aeab600001870000000000000000021fcf3bc000] i)) else (if i<176 then (if i<168 then tableWord #[0x2a5000035a6497d9b10000000000000000018e3,0x87fc00000000000000a4c0000000a0180000003a4b85490be0000000,0x372800068ac000000000000000000000000000015a000000062cc000,0xa700000000000000000040cc0000000000000281500000000000000,0x234000000000000008d582f0000c370000a683147,0x28bc000000000000031ea00000000000000000000073af8480000000,0x2082c270000000000000000000000000000e13c00081f9262,0xa01000026f328f000000000000000000000000000000002690000000] i else tableWord #[0x80ec000e52715c0000000000000000000000000000,0xc0e00000000000000000000086a4000e5c40000000000,0x67000000003a4d0000000000000000031ca00032c40000000,0x286000000000000000000000000002249df0000000,0x1780000000000000000000000000608000086b48940000000000,0xe57800000000000000000000390a000000000012c341840000000000,0xa21000000005340000000000a9e40000000000,0x10cc6d01f7902c000c030000c19a8a500000000000000] i) else tableWord #[0x3a550001896000000000000000003ec5,0x18140000000c58400000004d80000000,0x2cbd0001aac581000000000000000000000000000000000000000,0xa63faa5000000000000000000000000000000000000000a650000000,0x62a8232a29800000000000003a6c0000000819c000,0x287a] i)))) (i/16) >>> (14*(i%16))) % 16384)
  | 13 => fun h => smallSlot h 315 1092 9 1 (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x200c00000000000008000000000000000000000001,0x400000804000000000000060000080000000000000,0x800008000008010000000000000200000000,0x400c00800000000008000000000000000200000000,0x200400001002004000000020000000000000002000,0x200400000000000000020020040000000000800800,0x8000030000000000200800000000,0xc00004002004008000000100000000400400003] i else tableWord #[0x200000000002000000000000040000400a01000000,0x200000001002000000020000000000000000001800,0x2000000000000000000000000c0080500200801000,0x400c00002000000000000020080000000000000004,0x40000000000000c0000200200c0000000000000001,0x800000000000008000000000180100000403800,0x200000c00003000000008010000000100a,0x401400000000000008040060000080000200c00000] i) else tableWord #[0x200400000000008020000000040000000a00003800,0x402800000014000030000040000400000400800,0x600001807002000000000000040000000000400800,0x100001001800] i)) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x331227000000000048ec91f6c744ac9b40000960000000000136,0x10989d08c80000000000000000251da0f825647496c4e611e,0xd4a00000000030e0e09e6c84e28cc8bc,0x10899ea720000000001a54000441506a5a60520001380a84000,0x55341e444108df0a800000000000031e8cd4c5a9c9c8f827b,0x6055140001d2e000214695e00000044cf1c982fc498000219265,0xc608000000000000717c0010be00000000000000000000000000,0x301962f587637ba544792553659f00000000000000000c88] i else tableWord #[0x6c344b182ef2c98ab200000c7f8000418803,0xb6f000000080fa2a00000000000000000001d19325e05f4a4000,0x6895d22000000285c000000000000000000039f0000000000,0x43d0000000cc70000000000702c7c000000000000040c0000000,0x74a0001526000000000040d39cda6c0000005320000000000,0x48e28e090f194a880000000000002d69827c1b0000000000094,0x6a4c00188ce2613a800000000043340000000007450000000,0x1a21eae000a04000094a00087cc2480002baa960000000f1c] i) else (if i<24 then tableWord #[0xb54000000000000093b9320000003954f500000000000000,0x5567580000000000074800000800000041169ba000,0x27bd3ef54000044333962430fd994a1cfca241f0000000000000,0xb5aa35580243b0000000000000000000000000000000000008a0,0x142610b235e420000068000000531511a00000064d0001127,0x70700000016c10000000000000000000000000040a000108c000,0x108d8860000006180001ab966f74341de51d94900000004c6,0xc0581ba08400000000000320003840000001aca32000000018d6] i else tableWord #[0x882cce3916000e31b53b2880000000000000000044e53d48d6ff,0xd3a0000000001d5f266000000099e0000001058000000,0xb9873d40000000003cea9c6000d83800000125e0000000000aa6,0x2680000004031834001d4523d9b3325b6f80000000000000,0x4d0e82b66b953e8c52ae1530000003ab0000,0x68880010fe000f8b91ae23809bd4f74d40000000006129548000,0xd3e80b2274000d09800000084be1bd0fd1330e692a84c4001e72,0x1c326a0000000000000000000004d1859bbf4000000] i)) else (if i<48 then (if i<40 then tableWord #[0xb31934e5690bf000543c921ead5a78000001a120ac887c000000,0x28bb82dc0162ca204e7524509f88ac0000000000001f4c,0xa27a8640000000000002870000a0752889927098200000000000,0x7aa3aa50580002d18000000e9fe440d8745e878000027b057,0xd9021ba0e24df278000667000000085b0006a3f8b9cfa,0x143525de3840000000002c31d02000e6baace5e6000,0x318807800058878d50ec000000322d0cce9d8000000000,0x320eaa000048c5ab0000c1d00000000000000000002088920] i else tableWord #[0x25bf1c4001867000000000000003c800217a0001302196682828,0x48413c6a2650ba23f08041520143ba2ad5e0000a3ae3688d3068,0xaaa800000014900078ae949d5400023b76480000000000000076,0x67120175ae0000000000000f350005986e76000f44800393e000,0x86de1f797134da116468d0045300014555d80000948000000af2,0xaa50003e7a8cb34523ba508000a40b2860da501,0xc6524c000000041200001a1cc20000361d6400000000eba48000,0x7ae21be0000000003079ebd0000000000000e5d0000000f3c] i) else (if i<56 then tableWord #[0xe824188000000000000000000000000000002ee0000003214000,0x51fd0c28a400128b24c401fab40000000000001449,0xe8b8000000000000000000084d0001519dc206400000000000b0,0x7c135f800090a000000000000000000000006a60000000744,0x3c5a0000000000a0c00000000000000000000000012097,0xe3f0000000000c1f0001db40000000000000000f4800029d6000,0x28de00000000000000000000000001c3d,0x42991f800396cabc00032010d869ff870000000000] i else tableWord #[0x1290000a568000000000873ac280000004086298000000,0x3d460fea2d00008306df00000000000000000000000000,0xda512d00000000002049cf2000000000389d00ce978001056000,0x190f033000000254400000000031a5503,0x8e82ab129d2a0000000,0x53d8000000000000000009e00074ac001e1e00035040008fc,0x3913cc000000e0f39c000000000078c146f8c3000688ac68000,0x32a40000000000000000000fa2800000000000050e7a244ae] i))) else tableWord #[0x70c65626c573458f365c23e00000000000006873cda023723,0xb31e6e550d0abd4b45cf29e24600009f49fc000000,0x326b2b0001a1d000091c0000005508000001e4af2d000286c000,0x1e680000000000000000000248a8c2f5482c809c000000,0x0] i)) (i/16) >>> (13*(i%16))) % 8192)
  | 14 => fun h => smallSlot h 25 86 5 1 (fun i => ((fun i => tableWord #[0xa00100,0x60000080020c000] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0x5cc000200002a6a200002de000000087d0,0x3cd7c10075108a96378e9c4bf39580000,0xd7002a001913b0011ac5000026ab2,0x4a80001ac000000000000000000,0xc4000000000000e147000000000462a94d12,0x25c49a500001b1] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨4863,14,samples,cols,[[],[16,66,101,151]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 9 false (by decide +kernel)
theorem band14 : CutRow book 14 0 1 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_12 : CutRow book 13 12 11 := bandCut 10 true (by decide +kernel)
theorem combine13_0_23 : CutRow book 13 0 23 := @joinRow book 13 0 12 11 row13_0 row13_12
theorem band13 : CutRow book 13 0 23 := combine13_0_23
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_12 : CutRow book 12 12 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_24 : CutRow book 12 24 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_25 : CutRow book 12 25 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_37 : CutRow book 12 37 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_49 : CutRow book 12 49 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_61 : CutRow book 12 61 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x473008888c3b10b5,0x483088888c3b10b5,0x49310000043aa035,0x49318000043aa035,0x4a321111143a1935,0x49318000043aa035,0x30280002a190836,0x33280002a190836] i else tableWord #[0x33300002a190836,0x503800032190836,0x30280002a190836,0x30280002a190836,0x1a1200002a190836,0x30280002a190836,0x30280002a190836,0x50b800032990836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_77 : CutRow book 12 77 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x33300002a190836,0x4b3380002a190836,0x4c3400003b290836,0x4d3480002a190836,0x1f16000032a18836,0x4e3500003aa10836,0x4b3380002a190836,0x4f3580003aa10836] i else tableWord #[0x4f3600003aa10836,0x2b1d80003aa10836,0x503680003b210836,0x3b37000043b21036,0x5137800043b2a036,0x201680003b2a0836,0x4f3800003aa10836,0x201680003b2a0836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_93 : CutRow book 12 93 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x2b1d80003aa10836,0x3e3880003aa10836,0x2b1d80003aa10836,0x6390888baa190b6,0x2b3980003aa10836,0x4f3a00003aa10836,0x2b1d80003aa10836,0x523a80003aa10836] i else tableWord #[0xa3b0888c3aa10b6,0x533b8888c3b210b6,0x1d150888c3aa10b6,0x3d3c0888c3aa10b6,0x543c8888c3b2a0b6,0x1c3d0888c3aa10b6,0x553d8888c3aa10b6,0x563e0888c3aa10b6] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_109 : CutRow book 12 109 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x191100002a190836,0x191100002a190836,0x191100002a190836,0x223e800032990836,0x906000042a19036,0x53f00003aa19036,0x573f80002a190836,0x2c4000003b290836] i else tableWord #[0x584080003aa19036,0x594100002a190836,0x2217800032a18836,0x194180002a190836,0xd09000042a10836,0x2c1e00003b290836,0x194200002a190836,0x50d000032990836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_125 : CutRow book 12 125 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x194280002a190836,0x191100002a190836,0x191100002a190836,0x191100002a190836,0x31280002a190836,0x284300002a190836,0x5a4380003b290836,0x5b4400002a190836] i else tableWord #[0x5c44800032a18836,0x5d4500003aa10836,0x294580003aa10836,0x110c000032990836,0x194600002a190836,0x31280002a190836,0x32468888bb2190b6,0x5e470888bb2190b6] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_141 : CutRow book 12 141 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x15478888c32190b6,0x5f480888c32190b6,0x60488888c3a190b6,0x61490888bb2190b6,0x32498888bb2190b6,0x324a0888bb2190b6,0x74a8888baa190b6,0x7050888baa190b6] i else tableWord #[0x7050888baa190b6,0xa4b111143b29936,0x1c148888baa190b6,0xa4b8888baa190b6,0xd4c0888bb2a18b6,0x74c8888baa190b6,0x624d0888c3b290b6,0x634d8888c3b290b6] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_157 : CutRow book 12 157 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x6040888baa190b6,0x7048888baa190b6,0x74e0888baa190b6,0x7050888baa190b6,0x1c4e8888baa190b6,0x281b00002a190836,0x644f0888bb2190b6,0x284f80002a190836] i else tableWord #[0x6550000043290836,0x665080002a190836,0x285100002a190836,0x285180002a190836,0x362300003b210836,0x281b00002a190836,0x281b00002a190836,0x281b00002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_173 : CutRow book 12 173 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x291b80003aa10836,0x675200003aa10836,0x295280003aa10836,0x6853000043b20836,0xc5380003aa10836,0x261a00003b2a0836,0x695400003aa10836,0x6a5480003aa10836] i else tableWord #[0x291b80003aa10836,0x295500003aa10836,0x6b5580003b210836,0x362380003b210836,0x295600003aa10836,0xc5680003aa10836,0x291b80003aa10836,0x503800032190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_189 : CutRow book 12 189 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x503800032190836,0x503800032190836,0x6857000043b20836,0x6c57800043210836,0x6d58000043210836,0x6e58800043210836,0x6f59000043a10836,0x510800032190836] i else tableWord #[0x403000032190836,0x503800032190836,0x325980003aa19036,0x705a00003aa19036,0x715a80003aa19036,0x325b00003aa19036,0x705b80003aa19036,0x5b5c00002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_205 : CutRow book 12 205 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x5b5c00002a190836,0x5b5c80002a190836,0x5b5d00002a190836,0x1e15800032a18836,0x725d800043210836,0x5b5e00002a190836,0x735e800042a10836,0xc5f00003aa10836] i else tableWord #[0x5b5f80002a190836,0x7460000032990836,0x756080002a190836,0x5b6100002a190836,0x5b6180002a190836,0x562000032190836,0x562000032190836,0x5b5c00002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_221 : CutRow book 12 221 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x5b5c00002a190836,0x5b5c00002a190836,0x5b5c00002a190836,0x5b5c00002a190836,0x5b5c00002a190836,0x1e15800032a18836,0x1e15800032a18836,0x201680003b2a0836] i else tableWord #[0x1e18000032a18836,0x346280003b2a0836,0x266300003b2a0836,0x266380003b2a0836,0x2519800032a18836,0x1e64000032a18836,0x7664800032a18836,0x7765000032a18836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_237 : CutRow book 12 237 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x2565800032a18836,0x2565800032a18836,0x1e15800032a18836,0x1e15800032a18836,0x466000032190836,0x566800032190836,0x5d6700003aa10836,0x5d6780003aa10836] i else tableWord #[0x5d6800003aa10836,0x5d6880003aa10836,0x7869000042a10836,0x7869800042a10836,0x726a000043210836,0x796a80003aa10836,0x786b000042a10836,0x5d6700003aa10836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_253 : CutRow book 12 253 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x5d6700003aa10836,0x5d6b80003aa10836,0x5d6700003aa10836,0x33280002a190836,0x33300002a190836,0x33300002a190836,0x33300002a190836,0x503800032190836] i else tableWord #[0x503800032190836,0x503800032190836,0x30280002a190836,0x36c00002a190836,0x36c80002a190836,0x36d00002a190836,0x33300002a190836,0x7a6d888c3b2190c7] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_269 : CutRow book 12 269 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x7b6e00043b210847,0x7a6d888c3b2190c7,0x7c6e80043aa19047,0x7b6f00043b290847,0x7d6f80043aa10847,0x7a6d888c3b2190c7,0x7e7000043aa19047,0x7b6e00043b210847] i else tableWord #[0x7d7080043aa10847,0x7a6d888c3b2190c7,0x7d7100043aa10847,0x7f718003b2990847,0x80720004bb298847,0x81728003b2990847,0x827300043b298847,0x837380043b210847] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_285 : CutRow book 12 285 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x837400043b210847,0x847480043b2a0847,0x85750003b2990847,0x85758003b2990847,0x86760003b2990847,0x8776888c3b2190c7,0x88770003b2a18847,0x89778003b2190847] i else tableWord #[0x8a780003b2190847,0x7e788003b2a19047,0x8b7900043aa10847,0x8c7980432a190848,0x8d7a0043b2190848,0x8e7a803b2a190848,0x8f7b003b2a190848,0x907b803b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_301 : CutRow book 12 301 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x917c003b2a190848,0x927c803b2a190848,0x937d003b2a190848,0x947d803b2a190848,0x957e003b2a190848,0x967e803b2a190848,0x977f08c3b2a190c8,0x917f803b2a190848] i else tableWord #[0x9180003b2a190848,0x9880803b2a190848,0x917f803b2a190848,0x9481003b2a190848,0x9181803b2a190848,0x9982003b2a190848,0x9a82803b2a190848,0x9183003b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_317 : CutRow book 12 317 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x9183803b2a190848,0x917f803b2a190848,0x9b84003b2a190848,0x9184803b2a190848,0x9185003b2a190848,0x9c85803b2a190848,0x9d86004bb2a18848,0x9186803b2a190848] i else tableWord #[0x9487003b2a190848,0x9e878043b2990848,0x9f88003b2a190848,0xa088803b2a190848,0x9189003b2a190848,0x917f803b2a190848,0xa189803b2a190848,0x918a003b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_333 : CutRow book 12 333 13 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0xa28a804b2a190848,0x918b003b2a190848,0xa38b804c3b2a0848,0xa48c003b2a190848,0x918c803b2a190848,0xa58d003b2a190848,0x9b8d803b2a190848,0xa68e003b2a190848] i else tableWord #[0x918e803b2a190848,0xa78f004b2a190848,0x918f803b2a190848,0xa890004b2a190848,0x9190803b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
theorem combine12_0_24 : CutRow book 12 0 24 := @joinRow book 12 0 12 12 row12_0 row12_12
theorem combine12_24_13 : CutRow book 12 24 13 := @joinRow book 12 24 1 12 row12_24 row12_25
theorem combine12_37_24 : CutRow book 12 37 24 := @joinRow book 12 37 12 12 row12_37 row12_49
theorem combine12_61_32 : CutRow book 12 61 32 := @joinRow book 12 61 16 16 row12_61 row12_77
theorem combine12_93_32 : CutRow book 12 93 32 := @joinRow book 12 93 16 16 row12_93 row12_109
theorem combine12_125_32 : CutRow book 12 125 32 := @joinRow book 12 125 16 16 row12_125 row12_141
theorem combine12_157_32 : CutRow book 12 157 32 := @joinRow book 12 157 16 16 row12_157 row12_173
theorem combine12_189_32 : CutRow book 12 189 32 := @joinRow book 12 189 16 16 row12_189 row12_205
theorem combine12_221_32 : CutRow book 12 221 32 := @joinRow book 12 221 16 16 row12_221 row12_237
theorem combine12_253_32 : CutRow book 12 253 32 := @joinRow book 12 253 16 16 row12_253 row12_269
theorem combine12_285_32 : CutRow book 12 285 32 := @joinRow book 12 285 16 16 row12_285 row12_301
theorem combine12_317_29 : CutRow book 12 317 29 := @joinRow book 12 317 16 13 row12_317 row12_333
theorem combine12_0_37 : CutRow book 12 0 37 := @joinRow book 12 0 24 13 combine12_0_24 combine12_24_13
theorem combine12_37_56 : CutRow book 12 37 56 := @joinRow book 12 37 24 32 combine12_37_24 combine12_61_32
theorem combine12_93_64 : CutRow book 12 93 64 := @joinRow book 12 93 32 32 combine12_93_32 combine12_125_32
theorem combine12_157_64 : CutRow book 12 157 64 := @joinRow book 12 157 32 32 combine12_157_32 combine12_189_32
theorem combine12_221_64 : CutRow book 12 221 64 := @joinRow book 12 221 32 32 combine12_221_32 combine12_253_32
theorem combine12_285_61 : CutRow book 12 285 61 := @joinRow book 12 285 32 29 combine12_285_32 combine12_317_29
theorem combine12_0_93 : CutRow book 12 0 93 := @joinRow book 12 0 37 56 combine12_0_37 combine12_37_56
theorem combine12_93_128 : CutRow book 12 93 128 := @joinRow book 12 93 64 64 combine12_93_64 combine12_157_64
theorem combine12_221_125 : CutRow book 12 221 125 := @joinRow book 12 221 64 61 combine12_221_64 combine12_285_61
theorem combine12_0_221 : CutRow book 12 0 221 := @joinRow book 12 0 93 128 combine12_0_93 combine12_93_128
theorem combine12_0_346 : CutRow book 12 0 346 := @joinRow book 12 0 221 125 combine12_0_221 combine12_221_125
theorem band12 : CutRow book 12 0 346 := combine12_0_346
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 8 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_8 : CutRow book 11 8 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_20 : CutRow book 11 20 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_21 : CutRow book 11 21 7 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_28 : CutRow book 11 28 48 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc40102875,0x1204112672,0xe440d4340,0xe408d4340,0xe440d4340,0xe408d4340,0x1400050561,0xe50a00a86] i else tableWord #[0x2520cc021,0x25204c021,0x1400050561,0x25204c021,0x25204c021,0x25204c021,0x25204c021,0xe50a00a86] i) else (if i<24 then tableWord #[0x1240112875,0x1222a08784,0x1001900672,0x1000900672,0x1204112672,0x1010984672,0x1222a08784,0x25204c021] i else tableWord #[0xc40102875,0x250044021,0x1400050561,0x25204c021,0x1400050561,0x250044021,0x1430202784,0x611002243] i)) else (if i<40 then tableWord #[0x1251208a86,0x400880132,0x40090a132,0x611002243,0x1220208784,0x400880132,0x1400050561,0xc5004e021] i else tableWord #[0x1430202784,0xc5284e021,0x1400050561,0xc5004e021,0xc5004e021,0xc5004e021,0xc5004e021,0xc5004e021] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_76 : CutRow book 11 76 48 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc5004e021,0x46098e132,0x611002243,0x1430202784,0x46088e132,0x46088e132,0x46088e132,0x1400050561] i else tableWord #[0x1400050561,0x1400050561,0x6110c2243,0x1400050561,0x1400050561,0x1400050561,0x611002243,0x1400050561] i) else (if i<24 then tableWord #[0x1400050561,0x1400050561,0x611002243,0x1404850561,0x1404850561,0x1400050561,0x1400050561,0x1400050561] i else tableWord #[0x250044021,0x1400050561,0x25204c021,0x250044021,0x250044021,0x250044021,0x1400050561,0x2500cc021] i)) else (if i<40 then tableWord #[0x25004c021,0x250044021,0x250044021,0x252044021,0x250044021,0xc40102875,0x46098e132,0x1241112875] i else tableWord #[0x46088e132,0x1400050561,0x400880132,0x25204c021,0x1400050561,0x250044021,0xe44014340,0x440804340] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_124 : CutRow book 11 124 48 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x440804340,0x440804340,0x1400050561,0xe44014340,0x440804340,0x440804340,0x1400050561,0x400880132] i else tableWord #[0x400880132,0x1400050561,0x1400050561,0x250044021,0x250044021,0x250044021,0x250044021,0x442004340] i) else (if i<24 then tableWord #[0x440804340,0xe44014340,0x103080a450,0xe11014243,0x103080a450,0xe44014340,0x440804340,0x103080a450] i else tableWord #[0x1010984672,0x103080a450,0x440804340,0x103080a450,0x103080a450,0x103080a450,0x103080a450,0x103080a450] i)) else (if i<40 then tableWord #[0x103080a450,0x103080a450,0x103080a450,0x103200a450,0x46088e132,0x103200a450,0x103080a450,0x103080a450] i else tableWord #[0xe40814340,0x440804340,0x442004340,0x440804340,0x103080a450,0x103080a450,0x440804340,0x103080a450] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_172 : CutRow book 11 172 45 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x103080a450,0x103080a450,0x103088e450,0x1400050561,0x103080a450,0x103080a450,0x103080a450,0x103080a450] i else tableWord #[0x103080a450,0x103080a450,0x103080e450,0x103200a450,0x1400050561,0x1400050561,0x103200a450,0x103080a450] i) else (if i<24 then tableWord #[0x103080a450,0x103080a450,0x440804340,0x440804340,0x440804340,0xe40814340,0x440804340,0x442004340] i else tableWord #[0x440804340,0x440804340,0xe40814340,0x440804340,0x440804340,0x440804340,0x442004340,0x440804340] i)) else (if i<40 then tableWord #[0xe44014340,0x440804340,0x440804340,0x1431a02784,0x103080a450,0x442004340,0x440804340,0x440804340] i else tableWord #[0xe40814340,0xe44014340,0x440804340,0x440804340,0xe40814340] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_217 : CutRow book 11 217 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x543012,0x641013,0x111111765114,0x543015,0x641013,0x754016,0x754017,0x64100b] i else tableWord #[0x641018,0x64100b,0x421009,0x43200a,0x742019,0x42101a,0x42100d,0x42101b] i) else (if i<24 then tableWord #[0x42101c,0x11111163211d,0x64301e,0x43201f,0x432020,0x742021,0x222222763222,0x64301e] i else tableWord #[0x64301e,0x333333654323,0x432024,0x641013,0x654025,0x432026,0x421027,0x75401e] i)) else (if i<40 then tableWord #[0x421028,0x111111632129,0x95102a,0x421027,0x11111175212b,0x11111143212c,0x11111176212d,0x42102e] i else tableWord #[0x65102f,0x111111763101,0x731002,0x753030,0x731003,0x651031,0x651032,0x222222763233] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_265 : CutRow book 11 265 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x333333764334,0x333333764335,0x222222763236,0x333333764337,0x333333764338,0x333333764339,0x43203a,0x43203b] i else tableWord #[0x55555587653c,0x11111176313d,0x22222276323e,0x33333376433f,0x43203a,0x43203b,0x111111763140,0x333333764335] i) else (if i<24 then tableWord #[0x222222763241,0x333333764342,0x432043,0x111111752144,0x222222764245,0x432046,0x111111752147,0x111111752148] i else tableWord #[0x111111642149,0x11111165414a,0x11111164214b,0x111111732102,0x11111165414c,0x111111642149,0x11111175214d,0x111111642149] i)) else (if i<40 then tableWord #[0x111111732103,0x111111642149,0x11111164214e,0x11111164214f,0x11111165214f,0x11111175214f,0x11111175214f,0x111111652150] i else tableWord #[0x111111752151,0x111111652152,0x111111652152,0x111111762153,0x111111752154,0x111111762155,0x111111752156,0x111111765114] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_313 : CutRow book 11 313 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x111111752157,0x11111175214f,0x111111752158,0x222222753259,0x11111175215a,0x11111173215b,0x11111173215c,0x22222274325d] i else tableWord #[0x432020,0x11111143215e,0x22222276325f,0x532060,0x432061,0x111111432162,0x111111632163,0x111111753164] i) else (if i<24 then tableWord #[0x111111752165,0x111111432104,0x111111432166,0x111111432167,0x111111762168,0x222222a73269,0x22222274326a,0x11111143216b] i else tableWord #[0x22222276326c,0x222222a7326d,0x53206e,0x22222274326f,0x111111432170,0x432071,0x111111432172,0x111111643173] i)) else (if i<40 then tableWord #[0x543074,0x532073,0x532073,0x532073,0x111111532173,0x543075,0x111111a64130,0x543076] i else tableWord #[0x111111432177,0x543015,0x111111643173,0x111111432178,0x543079,0x54307a,0x11111173217b,0x111111742102] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_361 : CutRow book 11 361 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x11111143217c,0x11111175217d,0x111111742103,0x11111143217e,0x11111143217f,0x111111752180,0x111111432181,0x111111632129] i else tableWord #[0x111111632129,0x111111632129,0x111111632163,0x111111762182,0x111111632183,0x111111632184,0x111111532129,0x111111632185] i) else (if i<24 then tableWord #[0x111111432104,0x111111632129,0x111111432186,0x111111632129,0x32102c,0x321004,0x421087,0x421088] i else tableWord #[0x111111432189,0x111111432104,0x111111432104,0x42108a,0x111111432104,0x11111163218b,0x22222274328c,0x43208d] i)) else (if i<40 then tableWord #[0x111111632129,0x11111175218e,0x111111652150,0x111111432166,0x111111532129,0x111111632129,0x111111432186,0x76308f] i else tableWord #[0x763090,0x333333764391,0x764092,0x432043,0x421009,0x764093,0x432043,0x641094] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_409 : CutRow book 11 409 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x421095,0x53100b,0x53100c,0x11111154310e,0x543074,0x432096,0x54100c,0x64100c] i else tableWord #[0x543074,0x64100c,0x111111532197,0x111111765198,0x111111742199,0x11111175219a,0x11111143219b,0x11111143219c] i) else (if i<24 then tableWord #[0x111111632129,0x95109d,0x64100b,0x11111176214d,0x42101c,0x111111532129,0x421009,0x111111632129] i else tableWord #[0x42109e,0x421009,0x421009,0x421009,0x421009,0x43209f,0x64100b,0x42101c] i)) else (if i<40 then tableWord #[0x421009,0x421009,0x4210a0,0x421009,0x432074,0x432074,0x432074,0x432015] i else tableWord #[0x64301e,0x6430a1,0x432074,0x6430a2,0x6430a3,0x6430a4,0x4320a5,0x2222229632a6] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_457 : CutRow book 11 457 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x9420a7,0x5430a8,0x4320a8,0x4320a9,0x543074,0x4320aa,0x432074,0x6430ab] i else tableWord #[0x2222226432ac,0x421009,0x4320ad,0x6420ae,0x4210af,0x4320b0,0x4210b1,0x7420b2] i) else (if i<24 then tableWord #[0x6320b3,0x6430a4,0x7420b4,0x4320b5,0x4320b6,0x5210b7,0x9740b8,0x432024] i else tableWord #[0x5320b9,0x9750ba,0x5210bb,0x4320bc,0x4320bd,0x4320be,0x5320bd,0x5320bd] i)) else (if i<40 then tableWord #[0x5320bd,0x5210bf,0x5210c0,0x4320c1,0x5210b7,0x2222226432c2,0x4320c3,0x432043] i else tableWord #[0x432043,0x432043,0x53206e,0x6540c4,0x4320aa,0x4320bc,0x7540c5,0x432043] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_505 : CutRow book 11 505 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x6430a1,0x4320a5,0x42101b,0x5430a5,0x4210c6,0x5210b7,0x541007,0x541007] i else tableWord #[0x5430c7,0x541007,0x651007,0x5210bb,0x651007,0x5210c8,0x5210c9,0x53100b] i) else (if i<24 then tableWord #[0x53100c,0x64100c,0x42100d,0x64100c,0x42101b,0x54100c,0x64100c,0x4210c6] i else tableWord #[0x5430a9,0x421009,0x64100c,0x43209f,0x53100b,0x53100c,0x64100c,0x421010] i)) else (if i<40 then tableWord #[0x64100c,0x43200f,0x54100c,0x421010,0x64100c,0x64100c,0x543074,0x543074] i else tableWord #[0x4210ca,0x6430c4,0x432074,0x7540cb,0x42100d,0x42101b,0x543074,0x4210c6] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_553 : CutRow book 11 553 44 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x543074,0x543074,0x543074,0x543012,0x641013,0x1111117651cc,0x543015,0x5430cd] i else tableWord #[0x641013,0x543079,0x543074,0x5430a9,0x543074,0x543074,0x64100b,0x543074] i) else (if i<24 then tableWord #[0x543074,0x641018,0x64100c,0x64100c,0x5430a5,0x5430ce,0x5430a8,0x5430cf] i else tableWord #[0x5430d0,0x5430a9,0x5430a9,0x543074,0x543074,0x421009,0x421009,0x421009] i)) else (if i<40 then tableWord #[0x421009,0x43200a,0x7420d1,0x42101a,0x4210d2,0x42100d,0x42101b,0x4210c6] i else tableWord #[0x42101c,0x421009,0x42109e,0x421009] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_597 : CutRow book 11 597 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x10099999c3b21b5,0x101111113b29935,0x20188888c2990b5,0x202000004219035,0x302800042190836,0x40300002a190836,0x50380002a190836,0x604000032190836] i else tableWord #[0x704800032190836,0x705000032190836,0x805800032190836,0x90600003a190836,0x806800032190836,0xa070888bb2a10b6,0xb07800032190836,0x808000032190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_613 : CutRow book 11 613 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x805800032190836,0xc08800032190836,0xd0900003a190836,0xe09800032190836,0xf0a0888bb2a10b6,0x100a800032190836,0xc0b000032190836,0xc08800032190836] i else tableWord #[0x50b80002a190836,0x110c00002a190836,0x120c8888b2a190b6,0x50d00002a190836,0x130d80002a190836,0x140e00003b210836,0x50b80002a190836,0x50380002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_629 : CutRow book 11 629 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x150e8888baa190b6,0x160f00002a190836,0x170f8888baa190b6,0x181000003b210836,0x51080002a190836,0x40300002a190836,0x191100002a190836,0x7118888b2a190b6] i else tableWord #[0x1a1200002a190836,0x30280002a190836,0x191100002a190836,0x31280002a190836,0x7130888baa190b6,0x30280002a190836,0x1a1200002a190836,0x30280002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_645 : CutRow book 11 645 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x513800032990836,0x1b1400003b218836,0x1c14800032190836,0x1d1500003b218836,0x1e1580002a190836,0x1e1580002a190836,0x1f1600002a190836,0x2016800032a18836] i else tableWord #[0x21170888bb2a18b6,0x221780002a190836,0x2016800032a18836,0x1e1800002a190836,0x231880003b2a1836,0x241900003b2a1836,0x1e1800002a190836,0x251980002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_661 : CutRow book 11 661 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x261a000032a18836,0x271a800032a18836,0x281b00002a190836,0x251980002a190836,0x291b80003aa10836,0x261a000032a18836,0x291c000032190836,0x291c800032190836] i else tableWord #[0x2a1d000032190836,0x2b1d800032190836,0x2c1e000032a10836,0x2d1e8888bb2190b6,0x291b800032190836,0x2e1f000032190836,0x50380002a190836,0x2f1f80002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_677 : CutRow book 11 677 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x302000003aa10836,0x31208888bb2a10b6,0x32210888b2a190b6,0x332180002a190836,0x342200003b2a1036,0x352280003aa10836,0x3623000032a10836,0x3623800032a10836] i else tableWord #[0x52400002a190836,0x372480003aa19036,0x38250888bb2a18b6,0x1625800032190836,0x3926000043b20836,0x3a268888bb2990b6,0x3b2700003b299036,0x3c27800032990836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_693 : CutRow book 11 693 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x2d28000032990836,0x3d288888c32190b6,0x3e29000032190836,0x3f298888c32a10b6,0x1b2a0888bb2190b6,0x402a8888bb2a10b6,0x412b0888cbb290b6,0x122b8888bb2990b6] i else tableWord #[0x422c0888c32990b6,0x503800032190836,0x503800032190836,0x432c80004c321836,0x442d00003b2a1836,0x30280002a190836,0x452d80003aa18836,0x1e2e00002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_709 : CutRow book 11 709 5 := orderCut (pages:=fun j => ordered ((fun i => tableWord #[0x32e80002a190836,0x30280002a190836,0x462f000032a18836,0x1e1580002a190836,0x1e2f800032a18836] i) j)) (by decide +kernel) (by decide +kernel)
theorem combine11_0_20 : CutRow book 11 0 20 := @joinRow book 11 0 8 12 row11_0 row11_8
theorem combine11_20_8 : CutRow book 11 20 8 := @joinRow book 11 20 1 7 row11_20 row11_21
theorem combine11_28_96 : CutRow book 11 28 96 := @joinRow book 11 28 48 48 row11_28 row11_76
theorem combine11_124_93 : CutRow book 11 124 93 := @joinRow book 11 124 48 45 row11_124 row11_172
theorem combine11_217_96 : CutRow book 11 217 96 := @joinRow book 11 217 48 48 row11_217 row11_265
theorem combine11_313_96 : CutRow book 11 313 96 := @joinRow book 11 313 48 48 row11_313 row11_361
theorem combine11_409_96 : CutRow book 11 409 96 := @joinRow book 11 409 48 48 row11_409 row11_457
theorem combine11_505_92 : CutRow book 11 505 92 := @joinRow book 11 505 48 44 row11_505 row11_553
theorem combine11_597_32 : CutRow book 11 597 32 := @joinRow book 11 597 16 16 row11_597 row11_613
theorem combine11_629_32 : CutRow book 11 629 32 := @joinRow book 11 629 16 16 row11_629 row11_645
theorem combine11_661_32 : CutRow book 11 661 32 := @joinRow book 11 661 16 16 row11_661 row11_677
theorem combine11_693_21 : CutRow book 11 693 21 := @joinRow book 11 693 16 5 row11_693 row11_709
theorem combine11_0_28 : CutRow book 11 0 28 := @joinRow book 11 0 20 8 combine11_0_20 combine11_20_8
theorem combine11_28_189 : CutRow book 11 28 189 := @joinRow book 11 28 96 93 combine11_28_96 combine11_124_93
theorem combine11_217_192 : CutRow book 11 217 192 := @joinRow book 11 217 96 96 combine11_217_96 combine11_313_96
theorem combine11_409_188 : CutRow book 11 409 188 := @joinRow book 11 409 96 92 combine11_409_96 combine11_505_92
theorem combine11_597_64 : CutRow book 11 597 64 := @joinRow book 11 597 32 32 combine11_597_32 combine11_629_32
theorem combine11_661_53 : CutRow book 11 661 53 := @joinRow book 11 661 32 21 combine11_661_32 combine11_693_21
theorem combine11_0_217 : CutRow book 11 0 217 := @joinRow book 11 0 28 189 combine11_0_28 combine11_28_189
theorem combine11_217_380 : CutRow book 11 217 380 := @joinRow book 11 217 192 188 combine11_217_192 combine11_409_188
theorem combine11_597_117 : CutRow book 11 597 117 := @joinRow book 11 597 64 53 combine11_597_64 combine11_661_53
theorem combine11_0_597 : CutRow book 11 0 597 := @joinRow book 11 0 217 380 combine11_0_217 combine11_217_380
theorem combine11_0_714 : CutRow book 11 0 714 := @joinRow book 11 0 597 117 combine11_0_597 combine11_597_117
theorem band11 : CutRow book 11 0 714 := combine11_0_714
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 3 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_3 : CutRow book 10 3 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_4 : CutRow book 10 4 48 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xe408d4390,0x1430202762,0x1431a02762,0x1204112651,0x1431a02762,0x1430202762,0x1430202763,0x252044010] i else tableWord #[0x254844010,0x1400050540,0x1220208762,0x1400050540,0x250044010,0x1222a08773,0x1431a02783,0x611002243] i) else (if i<24 then tableWord #[0x611002232,0x103080a450,0x1431a02793,0x1400050561,0x1400050551,0xc2104e182,0x1400050551,0x1400050551] i else tableWord #[0x254844021,0xc5004e021,0x46088e132,0x252044021,0x250044021,0x250044021,0x250044021,0x250044021] i)) else (if i<40 then tableWord #[0x250044021,0x46088e132,0xe11014232,0xe11014232,0x103080a450,0x103080a450,0x103080a450,0x1400050561] i else tableWord #[0x1400050561,0x103080a450,0x103088e450,0x1400050561,0x103080a450,0x1030a8a450,0x103080a450,0x1400050561] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_52 : CutRow book 10 52 28 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<16 then (if i<8 then tableWord #[0x103080a450,0x103080a450,0x103080a450,0x1400050561,0x103080a450,0x103080a450,0x103080e450,0x1400050561] i else tableWord #[0x103200a450,0x103200a450,0x103080a450,0x442004340,0x440804340,0xe44014340,0x1222a08774,0x103080a450] i) else (if i<24 then tableWord #[0xe40954340,0x442004340,0x440804340,0x440804340,0xe11014243,0xe42014340,0x440804340,0x440804340] i else tableWord #[0x440804340,0xe40814340,0x440804340,0x440804340] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_80 : CutRow book 10 80 20 := colorCut (ds:=fun j => panel ((fun i => (if i<16 then (if i<8 then tableWord #[0x541000,0x541001,0x521002,0x521003,0x111111432104,0x111111764105,0x111111532106,0x541007] i else tableWord #[0x642008,0x541007,0x421009,0x43200a,0x53100b,0x64100c,0x42100d,0x11111154310e] i) else tableWord #[0x43200f,0x421010,0x631011,0x64100c] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_100 : CutRow book 10 100 1 := orderCut (pages:=fun j => ordered ((fun i => tableWord #[0x2a18835] i) j)) (by decide +kernel) (by decide +kernel)
theorem combine10_0_4 : CutRow book 10 0 4 := @joinRow book 10 0 3 1 row10_0 row10_3
theorem combine10_4_76 : CutRow book 10 4 76 := @joinRow book 10 4 48 28 row10_4 row10_52
theorem combine10_80_21 : CutRow book 10 80 21 := @joinRow book 10 80 20 1 row10_80 row10_100
theorem combine10_0_80 : CutRow book 10 0 80 := @joinRow book 10 0 4 76 combine10_0_4 combine10_4_76
theorem combine10_0_101 : CutRow book 10 0 101 := @joinRow book 10 0 80 21 combine10_0_80 combine10_80_21
theorem band10 : CutRow book 10 0 101 := combine10_0_101
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 4 := mixedCut (data:=fun j => treeData plus minus ((fun i => tableWord #[0x400880132,0x828c0675,0x46088e132,0xe11014232] i) j)) (by decide +kernel) (by decide +kernel)
theorem band9 : CutRow book 9 0 4 := row9_0
theorem checked : mixedTables book 14 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
end M767_15
theorem m767_15 : Face false 767 15 :=
  mixedLower (g:=M767_15.book) (i:=0) (hints:=275431563556)
    (before_sound M767_15.entries M767_15.prior) M767_15.geometry M767_15.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m881_8 : Face false 881 8 := lowerHint (lower_down h881_8) (by decide)
theorem h894_11 : Face true 894 11 := carry_of (swaps:=[151,98,82,16,66,49,128]) (by decide +kernel) h255_11
theorem m894_11 : Face false 894 11 := lowerHint (lower_down h894_11) (by decide)
theorem m895_13 : Face false 895 13 := lowerHint (lower_down h895_13) (by decide)
theorem m992_7 : Face false 992 7 := lowerHint (lower_down h992_7) (by decide)
theorem m998_11 : Face false 998 11 := lowerHint (lower_down h998_11) (by decide)
theorem m1009_11 : Face false 1009 11 := lowerHint (lower_down h1009_11) (by decide)
theorem m1015_15 : Face false 1015 15 := carry_of (swaps:=[100,131,82,16]) (by decide +kernel) m767_15
theorem m1021_15 : Face false 1021 15 := carry_of (swaps:=[82,129,48]) (by decide +kernel) m767_15
theorem m1022_15 : Face false 1022 15 := carry_of (swaps:=[151,98,82,16,66,49,128]) (by decide +kernel) m767_15

namespace M1023_17
def entries : List (Nat × Nat) := [(29,4),(78,4),(95,7),(189,8),(255,11),(353,4),(359,7),(371,7),(377,7),(383,11),(486,8),(510,11),(511,13),(606,8),(639,11),(668,7),(689,7),(695,10),(701,11),(710,7),(727,10),(734,11),(743,10),(767,15),(881,8),(894,11),(895,13),(992,7),(998,11),(1009,11),(1015,15),(1021,15),(1022,15)]
theorem prior : Known false entries := (consFace m29_4 (consFace m78_4 (consFace m95_7 (consFace m189_8 (consFace m255_11 (consFace m353_4 (consFace m359_7 (consFace m371_7 (consFace m377_7 (consFace m383_11 (consFace m486_8 (consFace m510_11 (consFace m511_13 (consFace m606_8 (consFace m639_11 (consFace m668_7 (consFace m689_7 (consFace m695_10 (consFace m701_11 (consFace m710_7 (consFace m727_10 (consFace m734_11 (consFace m743_10 (consFace m767_15 (consFace m881_8 (consFace m894_11 (consFace m895_13 (consFace m992_7 (consFace m998_11 (consFace m1009_11 (consFace m1015_15 (consFace m1021_15 (consFace m1022_15 (known_down baseKnown))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 169 0x1ffffff8000000000,padColumn 169 0x1892c49624b125892c49624b125892c49624b125892),(padColumn 169 0x3ffe0000000000001fff,padColumn 169 0x1581ac0d606b03581ac0d606b03581ac0d606b03581),(padColumn 169 0x7ffc0000000000003ffffff,padColumn 169 0xa4a5252929494a4a5252929494a4a5252929494a4a),(padColumn 169 0x7fffffe000,padColumn 169 0x1494a4a5252929494a4a5252929494a4a5252929494),(padColumn 169 0xfff8000000000ffffffc000000,padColumn 169 0x1690b485a42d21690b485a42d21690b485a42d2169),(padColumn 169 0x1fff0000000001fff0000000001fff0000000000000,padColumn 169 0x60d3069834c1a60d3069834c1a60d3069834c1a60d),(padColumn 169 0xffffffc0000000000003ffe0000000000000000,padColumn 169 0x3e01f00f807c03e01f00f807c03e01f00f807c03e),(padColumn 169 0x3ffffff0007ffc0000000000000000000,padColumn 169 0x1b00d806c03601b00d806c03601b00d806c03601b0)] i else tableBits #[(padColumn 169 0x1ffffff800000000000000000000000000000000000,padColumn 169 0x19c0ce067033819c0ce067033819c0ce067033819c0),(padColumn 169 0x7fffffe000fff80000000000000000000000,padColumn 169 0x1e00f007803c01e00f007803c01e00f007803c01e00)] i))
def cols : List ColumnInfo := [(1,0,1022,0,15),(2,0,1021,0,15),(8,0,1015,0,15),(256,0,767,0,15),(128,0,895,0,13),(512,0,511,0,13),(129,0,894,0,11),(384,0,639,0,11),(513,0,510,0,11),(640,0,383,0,11),(768,0,255,0,11),(14,0,1009,0,11),(25,0,998,0,11),(289,0,734,0,11),(322,0,701,0,11),(280,0,743,0,10),(296,0,727,0,10),(328,0,695,0,10),(138,4,881,0,8),(142,0,881,0,8),(385,32,606,0,8),(417,0,606,0,8),(521,16,486,0,8),(537,0,486,0,8),(770,64,189,0,8),(834,0,189,0,8),(646,0,377,0,7),(652,0,371,0,7),(664,0,359,0,7),(928,0,95,0,7),(31,0,992,0,7),(312,1,710,0,7),(313,0,710,0,7),(332,2,689,0,7),(334,0,689,0,7),(355,0,668,0,7),(666,4,353,0,4),(913,32,78,0,4),(930,64,29,0,4)]
def plus : Nat := 0x12050240a00a084084108210441803006
def minus : Nat := 0x30bc162a8919262d14340c91d06811432
def orderBank : Nat → Nat := (fun i => ((fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x100220040ca1280220010d83080c405088810086081000a93a08d0001560181a00020025123000549104280000b18c0500010272990800200451030003080a602191245a010ab000262818cc458123040a0610148041,0x9401100042002025182a103080a4050800c09860a800001010094000c0100a100028444015000008c6028000a010904c0008200118800200424030004088240600062184c08000c030081000000234100c220044087,0x40c202901022204021818400408022530008114448600100108d4800100411a100020020041000300400620010100054000102700a0000104e013000020800240310040a015230880110195000900605188011002043,0xa11100500008202a98800280e44500001004886000000091040b000262828c00404a3043000808822a400081204508001041092080018821231000903066a000080108c08001022088100018861201248023100a9,0x260ad04c000820200900008084250000b0048480001405908c0000401210818a0992b043ac80305808530841284146001420182a00000403024000501c68a0000a1010150000820201a000580c015200000808048,0x10140108400108951820001806010400034954806000610010040291205021c6449028052a4a009000833102048c14200280b2228183080c4040800b104228a001623044d400042220290005052403200010996628,0x4010094001482200a903200a4050800a02402a400080114414000c200100940005250518009491048a0000100c114001527411a80028403035000422d46480008008049000112452118002a488215000008c602a,0x3854048810e722c09182040050524054000a12426a40010428c150001c0900a100001063014000501048260008050900c0014041a080e1201220439c8402460810006a09451400280b1a2800022845105280a0a4a0a3] i else tableWord #[0x18200894c002c0211a90001180c524000b00400a200180300104001c0900188006040015000080a00280000415004c0b400c5602a4e110122032800558060a80000b00c090000401229800042ca3054000002c6820,0x4b00c0d000040b1a1800050524043000b00402a40014048050800002020118006040025100005856a28000a111004c002c0121a8000501643400001010864000000090c40c50569582a5640182c053a0610148061,0x4502144c0020202a280004050543000020a8a840000410150406600a64029ce110122021ac00098a081000600944d4000401289280000862213000008c60260004101548400140719a80000802442000000046620,0x118c0480018011928000501632400004008a2080000008c8406200814029d60004c50419c81024604100101415504001801282a000400a5034000810042a4000401140900020451099000400422510001004a028,0xa411004c002c0119280002808431030a130160a95900723014e81900520184001802512400052090a2650001494106002c0b1920000300251540004004a268000a100c108002025181900040405451000409ca862,0xa129945000148242098c411028043800b018026a0000100c1480020201821000284030320008080a68200065199014000c03008280030023240000a02c6460020a10181526280250028c0020085134000c080a8a2,0x4006501814a6280250010ce408123030800549d068a000a9220c5400180b19280c4491680538006504a2a80008a0944d0000d4128920004054545100040b0a8620008a114410a028292820c00300201450004004026a,0x9401200086720409182040060403053000b00466a000080080508001404420a80040400251000600466a04002501814a002020182980028403043000b01802840000100c08c000c65310280050163340000328cca04] i) else (if i<24 then tableWord #[0x3088128414a129c240028d83080c4030800c09860860006a184c0830a8011021c400a801032800402c0284000a411005000180b19a80c401168054a06401480810002008d0c0000c8309810612002204388012002065,0x18430c150001540112980062cc3043000208080480000a18884c00280b19a80e1501220329c8b024606100167300514001081091a800284040430001004a2480004101008c0008202a108001906120500010048640,0x6140080400002a201200059cc01520004204268400087080508000ce30081046090a103284a70900043000c128c14c000ce30082800280e3340000520080a8000a02110400021651821800280e4340000c59860a8,0x80508c0800042220128001a820142000508824260006a18040823044508194255044002180000a8804a0008150480c0010eb00a900019c20142000102c8a60000c128c0900010e100a900039d2014200020a00462,0x8912981000040419900e8224090659ca148140c950c0909c18e8004803029400081644200002010a26a0010428c10c00008311098000106301300050106620384804880ca72100918184003852403400035004406,0xa13989140028222031800484e5461000a00486c0000c0090d40a311214832d250a4ea064800519cc48a00100114550000d254b029001900605280064854ca80000152909800280100b100038405461000a00466c0,0xe101018c00240b21a80cc010c80538005480ec86000600940d000280211b1000285411420001004a0480000051cc580028410930800501200410003204ca62000e101518000004311018002804230228000a4a081,0x1603000c40030a63210800600c0021000708002c000181014d4000202000a00004050532000080a002403a0890241927285205031d850980b053ad0031580a53300532010a800ca03020d60004c503080051a0c48a] i else tableWord #[0x602a0c1400006a52130003806016200042a52a0c000834a90187415204832ce51a40a064800701984ca001602a0950001468309a00040045043000728108c4001062ad48c0028010030800004eb3150000021842a,0xe1014d800000066102800204e53201d0458120c9590060b014a62008140215000940604198a00940021000401140d000142708a1000580c00410007224ca62000e24848c4a101223831c004244a654000808080a6,0x840990c00010410898000188211201880205008750c0909c18a3088011010d010904604088c1114202100160220950001428309a00030025043000720108c4000815a8c980010c15a918000050b31500003018a24,0x160220d50001cc062b1800100ec32500081004284000412180900008c2629180009169416000a08820c200020330c54002022082080011008413000409020620014409918000284108b000059026450000b10422a0,0x88a921c18e61102508314253848006180062a4e4ac0008559c8d80000202031800511285430007225484c0006008049800008942898002a4a7612000901086c00008549c818029120503252500480061800c024e4ac,0xab110054000043118a000104e0241000600468e0000a038d180001002288300008083420000002c8a20400240181cab000262830d83580c40508004204248c0002020cd80000c83090300019c6010600a449d40cb,0xa101019400088243a2800200824530002080806a00000091440620081403ac0042c04075000558080ca000600945180020220939800080251360002580806a001603005880001602012800188213420008080ace2,0x6142602c1dab200c1603ac0020085156000810046e80004321891c002020183a000100a85370002200806a001803005480020200138800204e02510002080ac62000602a141c000c6531038cc010c8075a003200c0e5] i)) else (if i<48 then (if i<40 then tableWord #[0xe44a1d1400202a09398004054567100080a804e2000c058d1c0660c86403ad0019146072800510046c800046131d14002c22093980058821372000b00402e4000800805480030202b3880060400271000b00468e0,0x200944d400284109b9000384055710008080aac2000813809040028012238000300244601d0448120ed310040a01928004803031400200251560002010a28c000432988dc001c4909a100001003024000020c4628,0x401245181ca620c8b403ac002a802364000851446a80008060914c00102409298000286231400020a804820006129881c00140722b000000183420000a004a2ea000c0094594001c20203a00020025145000808824c6,0x20094094000007620b800580c00510004204cc82000640998c40000066203800604001700008080aac0000813955000008272a980001040552030a130160eb590060b01d28004803030d60004c5050988922d00eb,0xa0508d480008c06392000114086240000021882e001623049440000a0430a000280a84062d0031580e9001612185d80010012822800608022730002090c26c000660adcd4001440112980058042372000808822c4,0xa0208c08309001101940062802273000850044c60010a28890c00300a11b90002018234200020a8aa600000a18880c000c01281a8000984b715000808002c0001014155000020c55ba280040802263000800846c4,0x81615500c50569583ad405052505080023898e68000005b101cb200e1603a40029008654000c20044e60010400898c0014801129800410a2243000b01046e400120608d88002c01003880028088406000020c4406,0x12059118000240b19b000008083310248022d00c9000c70941940010e1282280019c25035000b08822e40002709409400280b0028940385650508004504a08a0006a0940d400054128128005012005100080a8aac0] i else tableWord #[0x5a0062b014ea1012238314a10804007088011002021001602211d8003020183980010088436000508060a60002033109c00080542130000982b725000b10424e200020221058000080430a00000404014000b00466e0,0x4100005c000429520b0005804225100050284482000a13841040008c062898000054a406000009d680a00000430c1400052253020000984b504000b11822800000603140c001c090390000389211200161018a0e9,0x60cc40001408422b00040403063000810c24c20000100c04c0010c25b8280038400067000c080a8ae001014000dc002125531a0000086217200020a8004e0018901d94800304010a90001184b52400051004284,0x1424849440001203b0980000023370000a00488c000080115c140011225302800080844100141024a0eb394290281965084020038c0062c03073000858060c6000ab00c14c0001601809800184cb507000b00488e0,0xa6131c106600a64032500194060618008008a2ca33004320192800ca030314005112865400035856e6a0002b0adc940005625b8a80038400167000708080c8000890a991400082000938005044116200050a822a4,0x400650181ca00294128ba80042845165000a08880e80002a0944d400104109a10000052a51700080a8aac2520891241da002c6530bb000400a50450002008a06a00046131cd00030a63320800608c124100072a4cc62,0x10100c1900028220939800124a9736000501c48a6001400805c80005244b930003086136200014894e4a00162304d480000093a0b80038400271000808004c20014008d1c000240b1a300e50a40a075a860484e0e9,0x1411045c8002c2208b100028142342000a10424e2001400801c4002c4109308003086125100013096c28000e10151c0001c2000b800060405460000c08002c03a0890241d6728520503a5850980b064a840488e0e7] i) else (if i<56 then tableWord #[0xeb00c1d0002160183200008d2a537000509c24a6000e2184dc80010093a038e82a4090769ca348140eb000e100c1d0000c0128a28003006016200034952e0c0018049cd9c0020c25b2a00060802263000a00846e4,0x461318d0000429529380058042362000509c22a40004603189000000a398b800580200610000024e60e00000331018c284c05832d68018ac064800800848e6001001805c800104109a9000204e5651188022d00eb,0xa03a1158002165182380010ca62360000580604e0000b18c05c0010272aa0800180a84060003194c40c00061015404800c8030314e45812307080020110a8e000a100c1900020282b288003016457000023096c6a,0x2612d8540001203b89800604055602c8030580c950c0909c1ce0014802032800280845100002008a28c00102288d5000280b1a3000019066702198029900eb3844048810e81ac05202844458043040800558060ae,0x184319904001c89331880048581162000b39800a2000840849040010e1002080019c200310001204cc42000270800840030202ab8000284811022401230c0c3094e1200042000cc15b1a800608c2243000501c46a4,0x20a10181d6b200c16031cc5004a0071800b01802ae000010101d0000c01009b8000040307300022090c68000440218900008272a9880010400721000300c020e000c008cd80041020303b4021040107284a008800e3,0x160091180002c0119b0000304cb456000b01106ca0016030051c001001009b800290085430003004024e0000100c1c8000c2b5a130001816c326000c08060c40010100c14800302003b080058024360000b00464c0,0x1803000dc0014a042a180038921127000c10042c40016010898400302003b0000280a830500052890a0600002188408001402110080820406075ad0031580c7008410041c612802200384002984c61400050084624] i else tableWord #[0x108050c18200304611aa0005804247300023018e6a000a6131c5400280b22b0000584a6276000b298cca4000a02210580020280120800184a6206000328ccc044002501818a002c0541b2800580c004700063056ca8,0x8a080498002085181300028404032000c0a80ca200000330854001422200900020140607000b0106ca000160090940000c0541020002184b50300040a80c0200000090840041460303a4cc010c804288aa09000c3,0x2020cdc000040119900022040107284a009000e3000620848dc000c25338300020441702000020060ec000ca18051800182659a2800318ab573000b018026e000a400c0d800180328a180020020127000008080e4,0x81615504000080203b00029004046000609460c6000a200890c00302003a8800580846500003080a8020ace023019661900520304001902134200022890e8a310050a01d6000d4109a1100094060728002094ce4c,0xe64b1448002025181080050023160000b00462a0000c009090000280b18980eb0a4ca063b14132560a750c0909c186720409180840029008765000600c02e400167300588620c81403ad000914607280040b004a2,0x650994c8000c0100990003840026100052090a280000919d84c00180122280006052a35600063056a860008059c498001c20203100051128432000302d842a0018100c1440021203b208001982b513000b0986062,0x181000984003028012080002467713000902c68e0490045a01d6000080439280028088517000a02402c450001494186001823203a8004854127300090a8ace2480245181ca001c8042b2000424076530004284ca84,0x660ad8900030261819000011295170000024e42e00181015184000006618b0002a489715000048cee240014008c9c0a181213839400300a8426000800c02c4000c62adc9400302018318003992c634000b00402c4] i))) else tableWord #[0xc32a1098002d0600a90002202014200060946046001810155c4000006620b80028c884160005094c42c00068180408620c8140324c5404a0021800c024e4ce0008059c8dc001c2020398004180c6530008480eea4,0x145499948001524420b0002a4a6216000602c66c00008549980862248b4032400280a8416188028500c9001632989d80010c45ba28000050b52700003818e4800004021890b200e4603a40030463063000b40402e4,0x4121891c000825311b800210213520005090c42e000ab00c19000314611aa0002854126300030996c0e001600915c000182320320003086226300012252c4e000a9225c58a31121483b4005a4a62760006495084c,0x1212049cc00288109b900031c60162000b21826a4000a3218858731123483b40032862374000658c60e8000e4484d0800196518120001054564100010108a40000003b149c002c8109b900059c2017200000198a2e,0x2494c46e000a921885c000d25310380030065165000608c60c8] i)) (i/16) >>> (43*(i%16))) % 8796093022208)
def orderClauses : Nat → Nat := (fun i => (if i<128 then (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0xb0140240400700c01402003004004000c,0xe01b0340640c01702c0540a0130240440800f01c0340611,0xf01b0340640c01702c0540a0130240440800f01c0740611,0x5a0b01582a0520a01382604a090118220420800f8f,0xe41c03706c0d41a0330640c4180220400bc170e,0x861082084007e0f81e83c0260481d80f074038178f,0x460821140c01702c1100a8130240440800f0740380610,0xa814c290510a013c2704d09812c2504909011c000f] i else tableWord #[0x861082084007e0f82b03c0260481d80f0740382a8f,0x680ce198328640c6188048610c017c0305e0ba1700285b0081682c85800415c0018,0x460d81140c01702c1ac0a8140241a80800f0d20380610,0xf06f0341b80c01702c0540a0130240440800f01c1b40611,0x1cc3604503005c0b0720e20540a0130240440800f0e00380612,0x3d81b0f40643c87802c1dc0a0130241d83a80f01c0743a11,0xfa1083e04007e0582b03c0260481d80f0e0038178f,0x810361e80c80702c1dc0a0130242003f80f01c0743f10] i) else (if i<24 then tableWord #[0x7b0361e80c8790f0058410130241d83a80f01c0743a10,0x861083604007e0f83583c0260481d80f0d2038178f,0x460821140c01702c1ac0a8140241a80800f0740380610,0x1081044180707c1c83b8130242003f80f0740383f0f,0x11e0b04708d11822c4508911021c1208610a0800f8f,0x13a2704d89a1322604b89612a25049892122038480f,0x10827c2088300e0f83909e0260484000f0740383f0f,0x10827c3608300e0f83589e0260484000f0d20383f0f] i else tableWord #[0x218a70722981f8a514828c5106b1420ec500220740bc1711,0x16c2d45a0b31642c4580af15c2b4560ab1542a4540f,0x218a70722985b83f14a2905186b1420ec500220740bc1711,0xc518830c610c11802fc5f0bd17824c5d8ba1722405c10,0xc518830c610c11802fc5f0c617824c5d8ba1722405c10,0xc5188324610c119025c5f8be17824c5d8ba18e2405c10,0x1a230c610d019e2fc670bd178334660cb1723285c0f,0x1b836c6d0d91b02fc6b8d61aa3505d8d31a40085c0f] i)) else (if i<48 then (if i<40 then tableWord #[0x708e01b63086f8de12e2fc6b8d61aa24c5d8dd1a42405c11,0x1d039c730c21ca3905f8be1c624c5d8ba1c42405c0f,0x760c4186308728eb1802fc750bd17824c5d8e91722405c11,0x1ec3d47a0f3182290790f11e0048500ef1723b8768f,0x460821140c01702c1c80a8130240440800f0740380610,0x1c8fb1e63e87c83f1483e0780121401a8118f71dc0bc7691,0x3f47a8f41e6264520fc1e2048500cc1723b8768e,0x460821140c07802c11081902024044809000743fc7f10] i else tableWord #[0x1c9081e63e87c907148418780121401a8828ef1dc4107691,0x8c1042281807c1c83b90b024044851090743b87f0f,0x1c0360680c8180f005841102024044809001fe0347f10,0x1e0360680c8180f005841102024044809001fe0747f10,0x1e0de068370180f005881902024044809001fe1b47f10,0x218a72182981f8a514828c5106b1420ec500220741541711,0x4314e4305303f14a2905186b1420ec500220741541710,0x22e4588a91422625c8911112a4404990f21c2e4868f] i) else (if i<56 then tableWord #[0x4323c4745311c07e46c5191a0d62841d9190741548c10,0x861082084007e0f81e83c0260481d80f0740382a8f,0x8f81b0f40643c87802c1dc0a0130241d83a80f01c0343a11,0x1200361e80c80702c1dc0a0130242003f80f01c0343f10,0x22e4588a91422625c891112424404990f21c2e4480f,0x4323c4885311c07e46c5191a0d62841d9190740bc8c10,0x920a7072298838a514828c5106b06648c500220744101711,0x22e49c7a8a4224444931250662808782221c2e4170f] i else tableWord #[0x430844b49612b07e0f81e83c2044a81d9290744a01790,0x861089692e07e0f81e83c2044a81d9290744a0178f,0xf64c8988190f21e0980822544bc3a9292500743a0f,0x4625a4cc0c0172601100a902254044081290744a00610,0x3c4d89a86e03005c981342544bc081292501b4060f,0xf13826a0640c0172600549b902254044081292500740611,0xe13826a0640c0172600549b902254044081292500340611,0xf13e27a0640c0172780540a0132760440813a2720740611] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x86478a08a62380fc8d8a307a5009f83b2320e8178f,0x1e0360680c81802c1dc9b90b024044851091dc0747f10,0x2194828e2981f94628a28c5106b1420eca21430740bca111,0x920a7072298838a514828c5106b29248c500220744101711,0x2a83d87a9532a426c799511f2290a80f829e2f0a70a029a530a594a18e0381717,0x1582ae3d87a9532a43d0799511f2290a81561e4494a70a029a530a59551720381718,0x2be314af1152a65487a09a2ba3e44b95c2b64844a0932b45645d14a1720384817,0x16c0b4b616b2d40e0b49682ce598b296406a58c5716204a5841214d29852c110210405800f9b] i else tableWord #[0x2e055cb79152a65487a09a2a23e44b95c2dc4844a09329a530b68ef1720384817,0x620c398630a610c1982302600bf97e2fa5f0bd8892f45e4bc1772ec5d4ba1732e45c40f9a,0x1702ae5bc8a98e31a3d04d1511f225cc618b2dc4844a093314624b68ef1720384818,0x3225bcc81152a65484d89a2a23e44b95c31e53c5e094126534a60ef18e0384817,0x16c0b4b61972d40e0cb1682ce598ca99432658c5716210e5841214d298648428210402a00f9b,0x620d39a634a690d19a2304684c017f34067ccf0892f4674bc19c2ec5d4cd99a3325c4cc1a,0x3806fcdf1bd3786ecdd1b93706dcdb1b53686ccd91b13606bcd71ad338244d61ab3546a4d41b,0xe60ec396728e491539071c648c31843ace309738a2fce21c31d44845e893176708749c11722405c1d] i) else (if i<88 then tableWord #[0x750218a70722988e03f14a290519d33a47445106b1420ec501d039e738111cd0740bc171a,0xf49e83ce070f31e53c878cf11e1034114f01df3bc7740b8163b876ced1343b204c091d802075c079d601c7540621,0x7bcf39ee03c798f29ed3d878c0d9e1034114f00193bc7740b8163b8768411d9026048f59ea02075c079d601c0740622,0x3fa7f0fd9fa3ce078fc9ed3f078cfb86f3c2114f01f63ea1b8ef0183e8058f99f23b40540a1d9024044351f10207c0079d601c1b40627,0x3de820f3a0740c7b4f620540878d0181b3c2115012013ea064ef0183e8059001da02a050ec8130247ac351ff3fc040079d601c0740627,0x1ef3ce83c0f20e3ca7b4f61e30367840d04541a8300c9de3ba05c0b20b3b6768411d9026048f5a0a020824079d601c0740624,0x42a8510787b426794f61e30368483d2113c0065081dd0f0058f99f23b6768411d9026048f59f10ea7c0079d601c0743a23,0x89111a224428810f84243c1042021d43886c1f83e4348643583c0260481d86a43085d0b00f074038179e] i else tableWord #[0x3de79cf701e3cc794f69ec3c606cf081a08a780fb0193bc0600b8163b8768411d9026048f59ea02075c079d601c0740623,0x1ef45a8b0f31e54568a8f181b4241e8419e00328a5140073e805905a2744c209128130247ac351ea0fe75c079d601c0743f24,0x1ef3ce83c0f20e3ca7b4f61e30367840d04541a8300c9de3ba05c0b20b3b6768411d9026048f5a2e020824079d601c0740624,0x1ef3ce83c0f20e3ca7b4f61e30367840d04541a8300c9de3ba05c0b20b3b6768411d9026048f5a300208bc079d601c0740624,0x91d2324548890d2102c4829011f82a47c8f51e0294760a11d2394708dc1323604a8d41223446685c112320408c40fa2,0x91d292454a2908162414a093d2724d49892d1ea4a11664d1d239492220b116146892042a320408c40f9e,0x91d232454a2911212560589052023f0548f92aa3d4780a51d8284748e52a25304c588b0a3446685c112320408c40fa2,0x24748c9752e11e4b69692023f4b28f91ea3c05264d1d2394708dc132584ae8d41223446685c8ca320408c40fa0] i)) else (if i<112 then (if i<104 then tableWord #[0x91d34a684ce91121a664ca99131a4047e0a93124b47a8f0148354729852a23704c9812fa3446685d2f2320408c40fa2,0x91d2324548890d2126c4829011f82a47c8f51e0294760a135a394708dc1323604a8d4122344d485c112320408c40fa2,0x123a7448a9113982c4829013902a47c9c51e0294760a11d2394e09bc1316204a5841226e46685c112320409b40fa1,0x48e9ed3d2514889e4162784a09013b82a4ec8f0148354729852a2372c4094b082446685c112320409d40f9f,0x145a69514a2521a88072a1d20a7850ca1415037238a1141a55496a09408355009fd3f03d1440cd3e8314688cd3e0220400bc1725,0x552aa0e02a754ca95522a3544a85500b253ea78dc1b753aa714da9a5326c94c297360a594aa94526a4948a9029833147a8e152a354627,0x145aae4d2a2928aad5100b01ca874829e1202850540dd422ac4960d955a804feaa8190314688cd3e0220400bc1721,0x5169a55aa5c5684795992250e9693c28650a9641b91c508a0d2aa4b504a04c9ab2562ac13fa7e07a468192af4688cd3e1190400bc8c27] i else tableWord #[0x2c5588b0d21288072b08b52c1580470b32bf502af81aabd5785415daba1420c95cab856e52c112b60400bc1720,0x28b592a2944ac8072a1d20a7850cb1c15037238a1141ac657ea09408355009fd3f0562340cd3e8314dc8cd3e0220400bc1724,0x891662224428810f84243c1042021d43886c1f83e4349fc3583c0260481d86a430b2d6500f074038179e,0x16b2d548ab516982c4829e12023f49c9311ead25a222d6808a4748e167a534b08d412234490b3842acd0408c40fa1,0xb796eadc0fa8816d84243c1f0362da080b656c03f02c8693f85602804c0903b5aeb2d6500f0e0038179e,0x1ef45a8b0f31e54568a8f181b4241e8419e00328a5140073e8059059f244c209128130247ac351f10feb7c079d601c0743f24,0x598bbc232ee5da8817621e5d6ba974ae85ce1150eae65cab900c03e02eb8d7104402804c08a185c2b800800f0740380623,0x303604c0416997600bfd7f0385fa5a17e2fb5f4be57c1953262297baf65eabd0570272c421c122f35e4bc5780850402a00fa4] i) else (if i<120 then tableWord #[0x224598c1d77b065dcbb50fa1e5d2c142084543a870ef01802e05971b040d6054ec8110d48600800f0740380620,0x598c3d8708461ac310fb0b60ab9c2088343ab997200702cc29710720ee04c09080612c203f80f0740383f1f,0x2153ce0798a1ed3d8c4cf1b12406784229f66227d4ef0183e8059059da02a050ec8130247ac0886a620040079d601c0740624,0x3035aac059024263e0b18f2ff63ac711fb1b634be98ca3d5a264c453185ecc5d7a2532c421c122e162cc55780850408c40fa4,0x10ab246467b80f1e63ca7b4f63133c6c490181a08a7d9911f53bc0600b816642768410140260480886a620040079d601c0740625,0x855168813cc795159ec3c680c0da123ecc44faa294507d00b20b3b41dc0a0130247ac4006a6201fc079d601c0743f22,0x660cbd9722165ac302132c082b682032b438b919503e02cca59406b07804d9386a596c980783a01cc94179f,0x1ef42883c3da133ca7b4f61e30368483d2113c07d80ca103ba1e00b20b3b6768411d9026048f59f10ea7c0079d601c0743a24] i else tableWord #[0x3d0ce19b8813cc794f21e33c48483d0833c07d8ef9de45005c0b20b66c7689a335026048ec33466675c079d601ccc998a3,0x1ef3ce7b80f1e63ca7b4f61e30367840d0453c07d80c9de03005c0b1dc66c768411d9026048f59ea02075c079d601c0740624,0x33a3ce7b80f1e63ca7b4fc1e30de7840d0453c07d8371de3ba05c0b20b3b67689a1d90260499cb100207c0079d601c1b40624,0x60691980b424acc7da0b1e5febf9a02c0636c697d33f47a0a59f028630bd99e96210e8d4122e162ccf19d8220408c40fa3,0x24748c915222434840b120b4d47e0a91f34c478d2da523b692d21a3b464748e167a3746c0951ab454688cd0b8226888c5a1a4,0x123ad548ab516982c4829e12023f49c9311eb4f5a222da708a4748e167a534b08d412234490b3842a320408c40fa1,0x1ae35b442d69aca5114ed601ca5014cd5d0e32a6ac291aa8a36a8d4c358a10660ec5035242ed44113500740bc1721,0x1b6b6c6d6315b53696d0d9db33656c8d8c618c26c4304640c017ed51b0b6017c2f45db5f5e2d785d35d1722405c21] i)))) else (if i<160 then (if i<144 then (if i<136 then tableWord #[0x1ae35b086d69808a7510c7c8631d14cc6db137107ed5851b706a8dbdb706b0660ec50316678d44113500741541721,0x382702e005b37f6fcdf5be0b45402c9bd8b15382bdbd3796f0dddbb3755e2dd055373152dc8541c,0xd71ada216b4d65448a76b00e5280a66ae8705b8a5148d5451b54432d4c3583364e0ec5035242ed44113500740bc1722,0x1c4a2155aa201ca047103ec200f3402e1d7238607e2914035370a0f435b840242803523446685dc183a1dc0bc76a1,0x3de820f3b8e038e35c61ec40a810f1a030367840d202402e2c0c9de45005c0b2007140540a0130247ac351ff3fc040079d601c0340627,0x750e9dd33a5748e8dd13a1740e7dcf00973ae71cd8d800ce69ccb9872ee59ca805728e4dc9175336e45aeb90004e3c0023,0xd71ada21756a25210a7058a19280a60548705b8a5148d55b835475486435ba9066c9c5035242ed44113500740bc1722,0x1ae35b442d69aca8914e995d80a623887195356148d5451baf6a8d4c358a175cc9c5035242eeb52f3ac0740bc76a1] i else tableWord #[0x1ef3ce83c0f20e3ca8acf61e3036ec80d0453c07d80ca294507d00b1dc66c76841225216048f59ea214ec4849d61dc0747f24,0x1ef3ce7b80f1e63ca7b4f61e30367840d0453c07d80c9de3ba05c0b1dc3b6768411d9026048f59ea02075c079d601c0740624,0x1ef3ceed00f1e63ca8acf61e30367840d0453c07d80c9de45005c0b1dc66c76841225026048f5bb3020ec4079d601c0740624,0x1ef3ce7b80f1e63ca7b4f61e30367840d0453c07d80c9de45005c0b1dc66c768411d9026048f59ea02075c079d601c0740624,0x1ef3ce83c0f20e3ca7b4f61e3036ed40d0453c07d80ca103ba1e00b1dc3b6768411d9204048f59ea20275c801d61fe0747f24,0x3be6d6ef5ad3bc11eeec47114774294521126e0d51dc8fc24a2f019bb8140edc6635139c089a81cd172ed81720,0x1ae35b086d69808a7510c7c8631d14cc6db13bf07ed5851b706a8dbdb706b0660ec50316678d44113500741541721,0x3de820f3a0740c8acf620540878d0181b3c211501201780064ef0183e8059001da02a051128130247ac351ff3fc040079d601c0340627] i) else (if i<152 then tableWord #[0x3de820f3a0740c7b4f620540878d0181b3c2115012013ea064ef0183e8059001da02a050ec8130247ac351ff3fc040079d601c0340627,0x1ef3ce83c0f20e3ca7b4f63c3270ed49a93341a8300c9de3ba05c981dc3b6768411d92044a8f5bc2020f04949d62500740624,0x1e29fa3cecdc0f1e63ca7b4f63c43c6c49019e10347d9889de3ba05c0b1f33b42080a0130247ac0886a3e2040079d601c0740625,0x3d934ef61ebbd67aa145ea3d37a4f45e83cf79cf35cbbcc79612de5177792f20cd99a78e001e31c,0x7c4f841c9527c03edefbde7ba3e5ee03f7b62915e1507b43e00906a29a08ca58f71dc0bc769b,0x1f31ef3ce071f29e53d878c0d9e1034115f20193bc7740b8163b876ced0823b204c091eb020f8c079d601c0340621,0x7bcf39ee03c798f29ed3d8fa00d9e1034114f00193bc7740b8163b8768411d9026048f59ea02075c07be701c0740622,0x6747f0fd1e766e078fc9e545478df506f3c2fa5889de3ba0600b8163e47680a9d9026ce40886a0207c0079d601c1b40623] i else tableWord #[0x855168813cc795159ec3c680c0da123ecc44faa294507d00b3ec3b41dc0a0130247ac4006a7d61fc079d601c0743f22,0x1818437e4a21f890c5d6fc0208fb7bcb95f7bee7da2910d36e234048352e162ccf19d83a1dc154769d,0xa2d34a8a55aa201ca047eafd1f98411f63cd00b875c8e18522804fc4680906a4688cd3e03a1dc0bc769e,0x20238080700a008c46ccd92003637fe325ff3fd7f8fedfd3f912efe05fbf76c2d80ad8be12a2f049af35e4bc5af3f61724345c25,0x712b25454115100e60840f71103a06c0c81702a04c0870c29140353234e12038a04688ce0303a80a0bc769f,0x82f059452ad5100e60aa047e61060a4131e702d00ae470c29140329234e10090a04690496503a1dc410769f,0x1c4a2155aa201ca047103ec200f34030657238607e2914035370a15835b8402428035234467061c183a1dc0bc76a1,0x42159210d452880728121041f0823ec79a0183d075c30a4560a020e11a8360485006a4688ce0d03a1dc0bc76a0] i)) else (if i<168 then tableWord #[0x44688a1304384a29c8642414c4710ec2307e295b821a4321585083b844b859d822074154171b,0x3de79d91b8e038e35c61ec40a810f1a030367840d202402e2c0c9de03005c0b2003b40540a0130247ac351ff3fc040079d601c0340627,0x3de8b615c2a40d0a4f2b8c3d878d0181b4248040ca2900e7d00b42884ee283b814026048f59ff3fc1fc079d601c0343f23,0x854f7c2f3ce07a171e53da7b1e1c2d264ed6163113ea778ee81726089ced0153b2408f5811784040949d62500740622,0x1ef41079dc701c71a7b4f64338650c5e1c2d264ed499a02860c44fa9de0307d0982003b42080a9022547ac089ff3fc040949d62500340628,0x42a7be1cc3845b0ac40c2e3ca8acf63c385a4ca1bc36858c461a9f426089ced0820ef0d0f592f7841fc949d62500743f23,0x854f7c2f3ce07a171e53da7b1e1c2d264ed6163113ea840ee87826089ced1033b2408f5811784404949d62500747f22,0x11062004687ecb58643e87b0f099a1d876060982e3608ca0220152044a808c3a5c2b80081290744a0061e] i else tableWord #[0x42a7bcf381e888794f69ec7870b4993b5886c44fa9de3ba05c984423b42080a9d92047ac0892f460040949d62500740623,0x1ef3ce83c0f20e3ca7b4f63c3270ed49a93341a8300c9de3ba05c9820b3b6768411d92044a8f5a300208bc949d62500740624] i))))
def orderGroups : Nat → Nat := (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc525172ca3c1041045,0xe33b2aa65587a10102045,0x30b237132c71e0408102046,0xe36ba98d91c7a22404045,0x39b2a9954c6a10102045,0x32aa56953471e0408102046,0xe35cadaa779b230a248a161449130a2461433e0408102046,0x38c6caa99d54c8a10102045] i else tableWord #[0x38cacaa99954c8a10102045,0x39b2a553386a10102045,0x38cecaa9956388a10102045,0xe6caa68d54c7a10102045,0x34b237132c71e0408102046,0x32a6665634b1e0408102046,0xd31aa67195954c9814202045,0x31aa66554ce1e0408102046] i) else (if i<24 then tableWord #[0xd31aa68dc656549814202045,0xd32b2695a54d1c9910202045,0xdac95a4cd1c7910202045,0x34cac9a56953c8910202045,0x38aa575a1c6818102045,0xd32aa571654d1c9814202045,0xe34b2695a54d1c9910202045,0xe74ca558d2c7c08102045] i else tableWord #[0xe2caa96d6347a10102045,0xd2d99958b1c7910202045,0x38cecaa9959588a10102045,0x34c6a9a37195954ca814202045,0x32b2565634b1e0408102046,0x31b266554ce1e0408102046,0x34c6a99c65655334a814202045,0x34ca97562c6814202045] i)) else (if i<48 then (if i<40 then tableWord #[0xe6caa6513147a10102045,0x38cecaa99961c8a10102045,0xc6c99955338d220408102046,0x79e9cb35bad35b2f3e570a5262294c64b0d16540404040404047,0x1cb4e6cb6eb4d72d979f2f05293118294c64b0d165c0404040404047,0x3969cd6eb4d72d979f2b05293118294c64b0d165c0404040404047,0x38eeb966ad39af1cb75e6ccc14664262b1318284c5090a6c0404040404047,0x3a6ccd971dcb75de366acd72d563d0c95244368b1121304c5860a6c0404040404047] i else tableWord #[0x1cb8e9cd6eb4d72d979f2f05293118294c64b0d165c0404040404047,0x1d36e6c772dc778dd7959284986d1626426098b0a640404040404047,0x78e9b3569cf4de3b5e5cbd19284282e162a42509890e6c0404040404047,0x78edb75518ef5d2f2e564a12214170d162a4c949111a0cf809080804046,0xedc755cb3569bb6eb8f9782a4885058aa4c64a9318640404040404047,0x3cfa7976b5b3ae6d6b679ad9cce1d2c8c4b198948c4a4629252337024080201008047,0x3cfa7976b5b3ae6d6b679ad9cce0d2c8c4c1b09894918c614a464329252347024080201008047,0x3e7b3ab534b3b170e95cd9d756d5cd4fe8d0c4c2c16258524c4a4946433124140547012080401008047] i) else (if i<56 then tableWord #[0x3e7736b5b4f3af2ca75b1a99d756ced8b09492918c68614c4a494643242205424120801008046,0x3cfa7976b5b3ae6d6b679ad9cce0d2c8c4c1b09894918c614a4629252343024080201008047,0x3cfa7976b5b3ae6d6b679ad9cce0d2c8c4c1b09894918c624a4629252343024080201008047,0x3ab6732eebe75cdb974dcac8aa998c62514c322623152e210080401008047,0x3cfa7976b5b3ae6d6b679ad9cecde0d2c8c4c1b09894918c614a464329252347024080201008047,0x3e7978f736b5b3af2d6ceb5e9ad9cee0d8c4c2c1b09492918c614a463829252347024080201008047,0x3cbb38f6b5b3aceb679f1cdad9d78f4fe0c2928c8170686462614a463125231c0946018040201008047,0x3f3cbc77b4e35cdb9b57cbcbf0d28c816c62615c530e0d2e018140201008047] i else tableWord #[0x3cbb3875b4f3aceb679f1cdb5ad9d793cf51e0c2928c817068646261464331251c0d0a46018040201008047,0x3cbb38f5b3aceb679f1cdb9b59d78f4bd0e0c2928c81706c6261463125231c0e0942018040201008047,0x3cbb38f4f3abe71f1cdb9b4f478de0c2908c837068646261251c12110e0d42018040201008047,0x3e3cbb38f6b5b3aceb67a65f1cdad9d78f51e0c298928c8170686462614a463125231c094a018040201008047,0x3cbb38f6b5b3aceb679f1cdad9d793cf50e0c2928c8170686462614a46312925231c46018040201008047,0x3c7a7938f734f3af6cebe79cd94de0c8c2b1a9a4a39c928e615044253a822209004010047,0x3d3a79b675abab63de5cdb9b579756cfe0d0a489867068646261585452190e0d0346018040201008047,0x3e3a793674f372eeae6d2ae3df1b9b568f85d2c9b084836864584c4a2a291412110e0542012080401008047] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x3d3c79b675adab6ae9e3de5d96d5d3cbc7d1d0a4a1898670514846292618160c0b074201008040201008048,0x3d3c7a79b675ab63de5cdbd756d5c7cfe0d0a4898670686462615452190c0b0742018040201008047,0x3e3cbc7a79b8f675b4f3ae6deba766dd9cd5cf53d0c8c2b0a89994938c8a8670514626211546422100801008047,0x3e3d3a79b675abab63de5cdb9b579756d0e0d0a8a489867068646261585452190e0d034a018040201008047,0x3e7d3cbb38f736b5b3ad6ceb5b5ad9cfe0c8c29492918c70696462584c4a463125234a018120401008047,0x3ab6732eebe75cdb974f47cbc8aa998c62514c312414130e0d36210080401008047,0x38b473ae6b2764de5cda9997cf4ecec0a0918c826251484638312415130d0a4201008040201008048,0x3e3b39b87673a524e1df1e5ddbc7cee0c890848281706c66611914120a073e018040201008047] i else tableWord #[0x3ab8f675736ceba75cdb8ecdc7cdc8c1a2918c625144322a262319153a01008040201008048,0x3b3ab773ae6cde5cdb97cd4bcca891826862594e3124151332012080401008047,0x3e7cb9b736b5b4f3b1ed275cdb9756cd50e0d8d2c6c1b0949168624c4a494331240547024120801008047,0x3c3a37b4f26e2d2ceaa9e665e3df1c58d7ce4dcad4d0c8b0989492918a60544c42413128242316090752410080201008047,0x3cbc7a39b8f635b3b271ee2d2b679e5b9695d3c6d4e0d0c8c6c1b0a18c62514a43282418141209054f008040201008047,0x3e3cbc79b7b674f1ef2e6d675cda99d3d0e0d8c6c1b0a49c929185624a4331280943024210802008047,0x3e7cbbb8f7336eebe75f174f8ce0d0ccc2c1a8a1998d8a8370322c26231447022080401008047,0x3cfa7976b5b3ae6d6b679ad9cecde0d2c8c4c1b09894918c614a4629252343024080201008047] i) else (if i<88 then tableWord #[0x3c7a373675b3ae2d2caba6e55e5d5cdb19d7d2d0c8b0989492918a6154514c463128242219151352410080442010087,0x3cbc7b38f6b5b3aceb679f1ad9d78f4fe0c2928c8170686462614a463125231c0946018040201008047,0x3dbcfa36732ae9e55f1edd5b974de0a3918884747268614c492a2618053e018040201008047,0x3e3cb9757372b1eeade3cf4be0d0c8c4c2c1928a83383225150d073f008040201008047,0x3d3c7bb8f73675b574f36cebe766974f4ecd92e0d4c8c2c1a3918a4c312a2618120d3f008040201008047,0x3e3c7bba75b1ee65e3cf8bcbe0d0c8c6c1918968382a2926160e073f008040201008047,0x3dbcfa36732ae9e75f1e9e5d5b9b574bd0e0a391888474726861584c2a260d3a018040201008047,0x3e3b3aba79b5b36eada72663de5d1c9b5ad9cec7d4e8c4988c8a8986706964623219140d0b422180401008046] i else tableWord #[0x3e77ad2ce75b1a99d3c9d8b094929168614c4a4946242205033e4120801008046,0x3d7cbaf4f1eeab299e9e5b19d756d593cf0785d3e1b0a8a4a2706864625249381a150c060346818040201008047,0x3cfb366baae9e75f1e9d9ad94f83cee0a3918c7268646158261c0a09053a018040201008047,0x3cbc7a39b736756ceadf1e9d9d5cdad74f8dd2e0c4a291887268646158492a26231c1542018040201008047,0x3c7a7938f4f372efab67db57558de0c1b0a8a4a2a1928a83514944422c1c160d4a810040201008047,0x3cbc7b3ab9b8f635b4f3b271ee6b67a55b9793cd14e2d0c8c6c1a1918c524a43302824181409054b008040201008047,0x3d74d9a71d6ab4e5c778e5bab3a3d0d14a24370d11212a305090c6c0404040404047,0x78edc7769b32e3b9669cf99c34468299099284860a0e640404040404047] i)) else (if i<104 then tableWord #[0x3e7cbbb978f731ef2b675796cce2e1d0c8c4b0ac85524a46431c193b028040201008047,0x3c3a7675b3ae6da7a6e5de5993cdcbcfd0c8b09896916049463129260e073a410080201008047,0x3c3a79b675a3de5d9bc7cae0d089867069646219160d0b0736018040201008047,0x3d3b39b9736ea9e563de9d9c5b5ad5478746d2e0c4a290888570686462611a14110d0b0646018040201008047,0x3d3cba79b5b36663de5d9b5ad9d747cfe0c4908986706964625419160d0b3a018040201008047,0x3e7d3cb9b5b362dd9b5ad9d7ccf0c4898269646259560d0b2e018140201008047,0x3c3a79b675b3b363de5d9bd79747cee0c8c49089867069646258544c4a19160d0b4a018120401008047,0x3ab9b574f3ace65ddb97cecbc4c2a2918866554e312a191332011080402008047] i else tableWord #[0x3e77b4ed2ce75b1a99d6d3cbd8b094929168614c4a4946432422053e4120801008046,0x3c797735b3af2e6ceb69e7a75e59cec3d0d0c4b0a49c9291868561484638230a0942421100802008047,0x3c7a39b7b671ef2d675cdb96ce4de0d0c8c6c1a49c85524a43312822193f021080402008047,0x3e7ab8f736b5b4ed2ce55b995756d3cfd8b094929168614c4a4946432422053e4120801008046,0x3cfab9f6b675b3ad6b675b92ce4de2d2c8c6c1a5948c4a43312818093b021080402008047,0x39b473b36ceba75cdb97cf4bc0a2918c62514e312c1915133201008040201008048,0x3cbc7a39b7b4f271ef2e6d675cdb92cfe0d2c8c6c1b0a49c91854a433128220943024210802008047] i))))
def ordered (v : Nat) : OrderPage := orderPage plus minus 11 orderBank (v % 16) ((v >>> 4)%8) ((v >>> 7)%1099511627776) (orderClauses ((v >>> 47)%256)) (orderGroups (v >>> 55))
def ruleBank : Nat → Nat := (fun i => ((fun i => tableWord #[0x4100048030880110194400880102184a008800210000400c08c00008318098e42012303080000808046000a111004c818405201840000403023000008c602600060180408000c2001008250044002188810086061,0x118c0480010022881800000232102c00098a0631102010c0820030201818800584c3021000b00462600014058c480c504c9581944408043010800b0180062580013140c200002018098002044110200030040062,0xa01088040030261819183580c403080080946064000801088043088011010d03200a4030800338c020400061400804129c240010c00304a3023000350c02040008150080412a8220010d400052503180050806064,0x1601084c00008c06181168018ac0329c2202440210006709408c0004e1280994038565030a8000a4a061000041884080014041100861200220218002008a04638440488086000c01281180008025013000010c4204,0xa40100c80014822009000280842102064014804160c203100c20028292010800580241302c80305806340c20290042c18406201040028404032000508880240000009084081840520104006080203100081144042,0x10b28c0c80031661819000201422011c2a02440433916048c082000d0300810c5404a00219c8102460210006a09448c6280250010ce4081230309c8102460410002111008c002829201900022845103280a0a4a063,0x30e6009900029044013000b3980062000414004802304850810c253848001080043840264] i) (i/16) >>> (43*(i%16))) % 8796093022208)
def programs : Nat → Nat := (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x28406080806,0x40706080866,0x58a06080896,0x101e3868c5,0x1222386805,0x141e3498c5,0xd19305cb156,0x101f3c74e1b6] i else tableWord #[0x101f3c7509b6,0x1284488d1006,0x1284509d3006,0x2c56a949b5,0x2e56a969b5,0x2c56a831b5,0x193160bd5136,0x1a3160bd9936] i) else (if i<24 then tableWord #[0x19316ed9a936,0x193160bd5386,0x1dba60bd5396,0x20c07ef9ebc6,0x22c43d0ce426,0x22c43d0d0c26,0x22c43d0ce466,0x4a925a4475] i else tableWord #[0x40706080cb6,0x27ce3d34e4c6,0x2944a30e8426,0x2987488d1066,0x101f3c74e546,0x284060ab556,0x2e56aa59b5,0x101f3c750d46] i)) else (if i<40 then tableWord #[0x2b9fa2768546,0xd19305cb586,0x1284b49ecd56,0x5ebb725db5,0x5fbb7035b5,0x3007509d34b6,0x3007509d3066,0x64c7889e15] i else tableWord #[0x3365509d3296,0x1284509d3556] i)))
def panel := readPanel plus minus 7 6 ruleBank programs
def data16 : Nat → Nat := (fun i => tableWord #[0x3ff,0x108304] i)
def data15 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x7ff082,0x10c58c03,0x7ff0a2,0x58d02,0x7ff0e2,0x4130218b05,0x7ff122,0x5130218b05] i else tableWord #[0x7ff127,0x240830a18506,0x7ff482,0x2051a385c0850e08c0a,0x7ff4a2,0x205183a0c2810c58d0a,0x7ff4e2,0x28c1a38241850218b0a] i) else tableWord #[0x7ff522,0x20c1a382c1850218b0a,0x7ff527,0xb1834740830a18909] i))
def data14 : Nat → Nat := bookData 2 4 4 (fun i => ((fun i => tableWord #[0x5275224e24a24821220a20821270e2] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0xfffdffffbbffbfb9ffbdfbefbfdbfe] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x54464549605456054460549635476354463547625456254251540015494054530544205411054000,0x4e494525904e4935259252788549675227754966547664e276547655456552275542615476454564,0x54798527985459852598544984e498147981459814498525974e497522974e496522965259552295,0x52793524934c49312793124930e4930c493527924e5924c59212792125920e5920c5924c5954c295,0x1279614496124960e4965479552795545954e5954e2954a295147951279514595125950e59552490,0x4e59754497524971499714597125971449754996547965279654496524964c4964e2961499614796,0x54299549975279754597] i) (i/16) >>> (20*(i%16))) % 1048576) (fun i => if i<48 then (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x406c3090b05,0x4c0c3090b05,0x4c0c3090b05,0x4c0c3090b05,0x4c0c3090b05,0x5040809c1c2c307,0x40509c0c1c2c307,0x110920c3140b0c07] i else tableWord #[0xa101113c30b0c07,0x110920160b0d06,0xa0f11150b0d06,0x90f11450b0d06,0x1011091ec304c007160b0a,0xf110414c0c309150b09,0xc0c30b0904,0x101105c00916c3170b09] i) else (if i<24 then tableWord #[0x90f11c0c34d05140b09,0xc0c3090b04,0xf101112c1c204c0c305130b,0x50c8cc0c1c2c3161209,0x8c114d09c18bc3c0c21214160c,0xa10118b8cc0c1c2c312160b,0x40dc0c38dc1c2121409,0xa0f118dc1c28bc0c312140b] i else tableWord #[0xf1145048dc1c28bc0c312140c,0x40509c1c2c0c31208,0xf101109c1c28bc0c3120a,0xb8bc1c209c0c31208,0x1322141720c38b8c08,0x45231516208b8d07,0x1e22098b1405,0x4d2209c38b1606] i)) else (if i<40 then tableWord #[0x8d4d8e4ec0050b8cc316120b,0x8e4e0a1e12148b8c4dc0c2c1c3160e,0x8c4c8e4e0dc0c3458d120a,0x458e4e04168b8dc0c2c1c34c12140e,0x8c4c8d4d8e4e050b09c0c3120c,0x8d4d8e4e4c04160c09c1c213c3c0120f,0x8c4c8e4e13124d09c1c2c0c38b140e,0x50b2012c1c31a4c08] i else tableWord #[0xb152023c2c11b124d09,0x50b1509c0c31207,0x8d4d8e4e098b4cc2c0c1c312160d,0x4d4e0bc04cc3161208,0x8c4c8e4e0b050d1214c1c209c0c38b4d10,0x4c4e85c0c34d1207,0x8c8d8e1bc1c2c0c312090a,0x4c4d4e1bc0c31207] i))) i else 0)
def data13 : Nat → Nat := bookData 3 6 5 (fun i => ((fun i => tableWord #[0x5254825224825255221445225455224e45221475224e41225490e25450e25250e25440e25410e25400e24e40a2525082,0x5454825421275471225451225441225490a25470a25440a25470825450825445225254e24e44e25224e24e44a25224a2,0x5401275275221455225494e25494a25474a24e24a2547482] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xfbfdfff7ff77febfdf7efdf7fdbff6dfe7ff9ffdfeeffb7dfbdf,0x1fdbff5efefbf7ffbff7ff7ffffdff] i) (i/16) >>> (13*(i%16))) % 8192) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x527594acaa2559124ab0a09560392a8e62159483ab480656a28aa9241551402a92844525186a4a20951020aa2800,0x4c58802cf10059a20073440525894a4f03549de52b2b89564712acce31595c62a2b48525688a8cd05519a00b3b0b,0x569882a4f10559a20a934414e6882a49105312208b4c4116688224d10559e20293c40566880a4d10139a20272c40,0x52689e9cd13d39627ab144f4e289e98513d28a278b544f16789e28f13c59a278a344f0e689ea4d13949627262c4e,0x5668a2a4d14539a28a9245116a8a22d3144526288b34511468a224d145496282924504c48a0acf13d49e27ab344f,0x5498a8a891505aa2a0b24541448a8ad314d59a29a934535658a6a4b14c59a298b2c535258a4a491495a628a93c51,0x1266aca92d0159dc02a3b40527800acce0139640262c8054789aac51345aa26a92c5516a8942cb12851625292c4c,0x547682a4ef05599c0a924c15696aea4ed5d599aba933575656ae9cad5d315ab8933571256ae18ad5d49dab293356] i else tableWord #[0x1676b42c8d68391ad06235a5696b2a4ed65591aca923594c46b2248d64311aca93b585266b01ccd615a5c0aa4b41,0x546690988d1d291a38623470a468ea48d19311a306234652668898ad10315a22b3b5a5276b4ac8d69491ad26235a,0x165a1c28b439311af25235e0c46bc148d79311aea5235d0c46ba148d75311ae0b235c0c46b89cad6d315ad862b5b,0x54969eacee3d51da7a93c0f56671ea8cd3d396478b534f527a1ca4d43939a87292d0e4e5a1c98b43859a870a350e,0x4e4a429894845a6908a4d21164a42289484492908625215276c0a4cd81395b00b33601656c0a4ed7d499af8b335f,0x4c46c42d2d88591b10923620c46c4ad2e45525a8aa3b515277a2acce45492688b535116a72228ef4549e90a92521,0x569726a92d4d49de9a92d124e5a24a49449392890b2d12145a242c944851289293b635246c62c8d8d49db1292362,0x5476caa4f095591d2ab3b8c547698a4f031519a62a2b4c14769828cd30595b20b23645496a8acee5149e0a0b5354] i) else tableWord #[0x524088948110598220b28440c5088188110290222628821240b09ca0593140b2b2c2656484c28ad545a9a52b3ba5,0x4c40b0ad45055a4aba939975672acacc5595a8a0293d52527a9c98429d20853a7281c4a4038ad211159422262844,0xa4186ad220959841293082565104ac8209490412620824a410418a20831041052082527234ad25655a4ac2b3158,0x16400c188018290032b4944566088acc511498222b29444c4088a4c30d31461a920c34c418694830c314618620c3,0x5672b8acc56d594ada6205b56a290a8812159083a921074c420e94841c3108385210756400ca4801931003252006,0x4a2b3c905678596cf0b259e0c4b3c14967828acf04159e56414e94829d58853a510a70a414e18429c288538410a7,0x4e5c42ad258159cafab315f56a29e2d453d5a8a72a3d8e546b1c9c9739596cf2b295e564b3cac8579312cf25259e,0xb514a16a2a8ad454949c918b39a35692c42d45455a8a82a4da1] i)) (i/16) >>> (23*(i%16))) % 8388608) (fun i => if i<28 then (fun i => (if i<16 then (if i<8 then tableWord #[0x4605d161404,0xaa2d1a1604,0x220f826161405,0x1e11026161405,0x121e1105a161406,0x1e11025161405,0x1e11025161405,0x2011825161405] i else tableWord #[0x1e11026161405,0x1e11026161405,0xe1825161604,0x1f23027861205,0x2bc304f00421206,0x2a09e070c2c1206,0x1504f03861205,0x1c0c5f07854c04f0c241609] i) else (if i<24 then tableWord #[0x1c0e18269a1205,0x4c441d1322d181807,0x181008c2c1c51a61168d09,0x44230f42c2c1406,0x911122c281605,0x50302011448c1c1e1950344c0b,0x14014208906c981807,0xa0151170c2c1206] i else tableWord #[0x58301e11054a9c0e1824aa120b,0xc6e3849c104f0c341608,0x632998ea743429c1e106f81c30e82524540f,0xc73391a191205383c3048683a160c] i))) i else 0)
def data12 : Nat → Nat := bookData 4 5 6 (fun i => ((fun i => tableWord #[0x5495250e25455250e25255440e25255410e25255400e25444e40a25465250825455250825275255225274e45225651475225641475225661445225651445225464e40a25254e4522,0x5454e41221675455225611475225601475225474e41225655490e25695450e256a5250e2] i) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => ((fun i => tableWord #[0xdfefbfdeffabffedffbbfefbf3ffe7ffbdff7fff7fffef7ffefffd7f,0xf5ef3dfcfbf3fdcffa3fff5bf77ff7eff7bdfbf7fddffa7ffd7ff7df,0x3d6bcdff97f] i) (i/16) >>> (14*(i%16))) % 16384) (fun i => ((fun i => tableWord #[0xc414e98a218314432a30204c20c098811431022a628440c50889ca10d49821273042569042a4e08549010a93800,0xc43989886ad624c0ab4901587302a4e585598a0a921214c428224c505398952b39095271d29ca325498642620a7,0x14620498a5cc314b9a620f20c41e498834431068a621100c42209883bc31077a620ce0c419c2cc4b431096a621cc,0xa44e8a8e40d49d11aa29034e23c628e40d625212c3a42547204a4e88951881292a024e540498a809388f12611e2,0x18554818aa90311520522a44c552a988a552914a8522955864e8b0a9d13153a2c22744c44e89489d03153a062274,0x4c258c2d4018594030a28060c500c2d440161102a622054a440a308814510828622050a440a98aa90619520a3104,0x144748288e54519ba0c534318b6aea48c993118b2523160c462ca8839d20973aa316652600cb0a019514b3262806,0x48288c2890d9516032613e614478a314e90629a20a33a4] i) (i/16) >>> (23*(i%16))) % 8388608) (fun i => if i<1 then (fun i => tableWord #[0xe3ace02425f07c3a2c12074160a] i) i else 0)
def data11 : Nat → Nat := (fun i => tableWord #[0x7d7b4c25275254e4522,0x0,0x797f5465275254e4522,0x0] i)
def levels : Nat → Packing
  | 11 => (2,5,6,0,0,0,0,data11)
  | 12 => (120,4,6,0,0,0,0,data12)
  | 13 => (377,3,6,0,0,0,0,data13)
  | 14 => (100,2,6,0,0,0,0,data14)
  | 15 => (10,1,6,0,0,0,0,data15)
  | 16 => (1,0,6,0,0,0,0,data16)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 12 => fun v => (if v=13074004645524305889 then some (1,5) else (if v=13386348004015190124 then some (1,0) else (if v=13598799148232044752 then some (0,0) else (if v=14671010711520235349 then some (0,5) else none))))
  | 13 => fun h => smallSlot h 87 302 7 3 (fun i => ((fun i => tableWord #[0x8040000018000000010040200008000000,0x18000000020000000000040000,0x100c00000000c0000000000002,0x8080003010100001000000000000000003,0x8040000000040000010000200,0x58040002] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x30f4000000615c1c0001c166398000001de7e231d5a016000,0x1b8000c440000000001835a219d68000c08412000386e000,0x41560360000070000868875daa309c0ad403a00ab9c000000,0x30a2d1a000e2bf0e400085a00011b185905e00c8000001818,0x4da40000000000000000c5000000000010520000000000000,0xccb719d838000a10800000000000000000000006358000001811,0x18edc3a7b30002eee06a000407983ec06434800384442e,0x1575418000000000000040e000156300000018bb83e] i else tableWord #[0x7138001581a04e0ca0ee44f00000000000000000000000000,0xd6104a000000215000000040780010620000000000000000,0x61736ce0000005014000000c28b0280000000003120818000,0x185a0000004108ee9059eaf0000000000c2c20ab076423,0x18c0866b6d800000000041330a40000000000001082000,0xe093010001c4500030fd02807400030bd02f436a2f800000181a,0x201404c0989e6436d0f10920000000000000000000000000100d,0x62995d8001c78a26d18c0000000000002820000e3900018b6000] i) else tableWord #[0x38d00000006194000000825800282a000c25701c5cd020,0xcae800000000000000020e200000010cc00000000000020c4000,0x81c1d00000000de86402380000000000308a336ae000] i)) (i/16) >>> (13*(i%16))) % 8192)
  | 14 => fun h => smallSlot h 319 1020 9 3 (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x101006008040000200400000020000201405,0x200404004070080000002000000040000c00,0x4050000a0000001c0100000008000000e00400,0x40100401010000000000001000000000000000,0x40c004000000000001000010040000400,0x60040d0000c0100000003000000000101801,0x300003000020040000000010030040000c06,0x8000000400803000000000000001] i else tableWord #[0x80200003000010000200400004060000000004,0x100012004010000402c020000800401,0x100300002004010080a00407000000000400002,0x403004050000000808000040000100405,0x403000050140000c0000000000000000300001,0x60080000401008110000201c000000000401,0x101000040000080500000018000100000003,0xc010080000c070180300003004000000000801] i) else tableWord #[0x1000000030000500009000010000101c0400000,0x80000800010000000200013000000000401800,0x2401034020000000400004030000300800,0x40080101c070080600008] i)) (i/16) >>> (10*(i%16))) % 1024) (fun i => ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x6d151c8b3790000a0a60002eaea0b5c1a912d8b5a80b2c14d434f8859082,0xc172000000000000001b3f8b2180000d27c93e68200008076a8c90088000,0x435c00000000000000306c21046d1d41e00000000,0xe1c02c000403c000129960710000c2480002099f0d90001c1166a2c0b4,0x21bc0001231e14d4012c3ef0959632000090b90b6610542ec05610b364c0,0x62c6000000000000000c0bc00001380000a5bc84f8000e1f0000180e0000,0xd8b4e03a0000c4d80000000000000038510000000000000003143,0x5a5742a00000000000082f201b6a771117418a425ea140000] i else tableWord #[0x2ad80000000000000000000000000074d404bc00010ab00017527668a0ca,0x32700000000000040600006013000000000001034903482b2866447d,0x209614a817ac26f871f259cc41420504a2450d44dc43103baa38,0x100001cb1e87820b6c0b8451186a8075e860436831b60e5,0xc17a84016b3411780dc000608461b800000000000000000000000000,0x544979cc58e000010f31c6680a2a643155,0x113580002d64ced980e0ea51a61a2e0459f86dad390000146b0a75abf,0x997c801c8ad112a202f0180098207ce459c0cc09d61153d6c000167aa0ae] i) else (if i<24 then tableWord #[0xa2a2000031200000001c900000113100b0000000000000000d0700000000,0xc1de000000066ecc2a6000002100a96046444e35f80000001d1480001631,0xe9b4000109664bb347cc1ae00d0000000011bd870000000000001b71d175,0x7995c55d62ea85a211a00010061caba202d9ab6a70000000000000000000,0x84f088e80004055301293f000000001dba837724e000000000000051,0x210c18fa0250000aad103db3133a3a40be0000000000000000003e548000,0x58562269f2c350f8000000000000001858,0x4578c12103548be0001d0a50050000000063200000000c62d40140004032] i else tableWord #[0x8dbc000088c263a41fb415800000009abf33af8a08000219000000000000,0xc5b40000000000042440001abd61cc00000000000e1d2c5260688000,0x79a00001833601e00000002050f85b00014b5de0a1a6e820c0000000615e,0xe1d1305786e8000da8200000007049bcb2920b04b0000000000000000132,0x35e8000000000000000000000000000001088c1eadb87833a021,0x4875a483ea0dff1df8194e5aa41a98ae000000000000001d12c0000000,0xc1676887b601227a01b42a381754ef0000000000040a7405acaec0b7e160,0x226f8442ea00000c8574048014b613a1700001013561e000000000003072] i)) else (if i<48 then (if i<40 then tableWord #[0x55e131c5ccb7a51723a896908876d44562a800000000ce7,0x40640000000330f80000000936c000000078780d600004352,0x61d80000eac800082d400002154068000080080005128000000000ac8000,0xcdda0000000723f00011908000000000000000000614ce88800000001692,0x45e00001123a154c4f822d7c05248e008b88d685519640002b720000,0x958d088f226da6c8213421cb37413f2d13c5968b2216178c3bb1f09ed095,0x10d5486180e7000191fc000307be207c5c608960c4e469c470052c076,0x58ca44500006004e1401b740002177a1180001a2b0000000000000002661] i else tableWord #[0xae80000000000000000443ac3c4ec0006654e07b0050000200f,0x222c000204cd05900000000000000058c46ad2275a0eb000000026539d3d,0x140c1652d07a61e4a3c00005621209800023b8f04040b5028f813c665,0x1518b935b351ccd1050b8a3f0bca8b673a868a5100e106000207f7d4c,0x21c2000382786b4c9b0317cd12911f0000055900c908fc1ad70618309cf9,0x282590c0000015a921780000000000005d8cfa000180d485fc050,0x244000036cda5d000000036a38000000044940000000000000000000000,0xc1e20000000000081348498868611b8126302fcb1e0d20056a303629d08a] i) else (if i<56 then tableWord #[0x1c4d4063bd03c174000230e00000000000000000000001007500abd3e,0x3881706c40af856f0906687000000038a7d66c419a82bf8160000,0xd5a0000208f206f421e000387a00005940311560690f9e2b9b3f184f2008,0xe124000101b007f80d2914403180000000000000000000000d9a40001ccb,0x621d450301f00000000c390000000000000001e19608500000000000307e,0x66ac0000000005b00620000888901f2296b27800016f39a8684a4e018000,0x87ff089381c00000b5c0410000000068c0000c243a3bb8ba6681,0xb9805895038800000015a3c000314570c6000182a18100a0528f400026da] i else tableWord #[0xe16142f960650c9e2c481d2023b025cd01051a05beac08444403b021c020,0x10876823110d224e00000000000957c046705220522273326f865e0fc,0x4211057f116800068a700580000000000041cd09700006c7a00000000000,0x15a60568eb7a1ee13c355d108e0001c319858f001a2d0000002e8000,0xb0af32e0803316e89d46ad76ad8000612000000002641000000000000000,0x603600000001a4359f6018a8268000000000018608000807e00026667cb6,0xad7400000004148425bf3bf08500ce81f59c7f84e50cf4073b3e28a91107,0x185013b27270ea40f20002e2e5c1a013ac3b9e568000] i)))) (i/16) >>> (15*(i%16))) % 32768)
  | 15 => fun h => smallSlot h 116 372 7 3 (fun i => ((fun i => tableWord #[0x400000000004008040001010000000,0x80c0000000000000010000002008040008,0x20140000000080000000040000008040000,0x10040300008020002000040001808080a,0x1000000605000080600,0x30100000110080406000200c0000,0x408000180804030080c1c00010000800,0x80000] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x1a740000000005525a84000000000000145b0000000000000,0xa97dae4000000813501f87419f95c0001377c4f00010afa82000,0x4a63b0c00000000033151c99cfe300000a7794a291000234e000,0x9868c09888d260000000000000000207e0a909b22c078b06a000,0x6de000139313c000758a068000000664de07da2c2f4914000000,0xec000321000000116dac20000000000ccb60400e00015bf,0xf1b7091314000c17c92c00000000000000014257a42138a8e000,0x4e996e186ed14a03118906d99d7901678000405] i else tableWord #[0x4180000001028c01e04688780b5a0b0b9172000,0x828421d88441918a619224349322accb3c72c01a318001054000,0x3ad2859a9bcbd80610b789319521f703403785ca0d00010735c7,0x56bfb0e023da3a0ce0be6c5d83409fa8c09c,0x20c98a393f0002c4088a00082b8001a3dc16ca4314f440000,0x22cd074d9741580f65388b5301cb20b24000000e1e00039816a2,0x140e6cb81223ac000c100000001421d5a846d86300a,0x520800000000025b904b40c62600000000000002eda4d520c44b] i) else tableWord #[0x808711887a6b40000000001120a7160ffb46000229551182f25e,0xa0e00028ac3268e6e0b2386000000141c000000b158003852000,0x34d0000000a9c04540001080004174000d1c88492fa8284af,0x311c812000000244d883022e010790880ec7268445881f04c,0x549000101300000000000006daa128a8651d0007709336000,0x30084d70000000001f5f098f7542ab461ae70000000000,0x6d200000000008ce00000012b6000000162c84d00c0002e50000,0xcda0000000000] i)) (i/16) >>> (13*(i%16))) % 8192)
  | 16 => fun h => smallSlot h 15 48 4 3 (fun i => ((fun i => tableWord #[0x10402c2003041000184] i) (i/16) >>> (6*(i%16))) % 64) (fun i => ((fun i => tableWord #[0x4a4006140000000010004480000381001b900000,0xe4c00c0f96a6406c600000011003b80000000288,0x70ccc6f46a4809d68a00ae5241e5eb4c2723] i) (i/16) >>> (10*(i%16))) % 1024)
  | _ => fun _ => none
def book : Forest := ⟨5119,16,samples,cols,[[],[98,131,84,151],[16,66,101,151],[16,82,131,100],[48,129,98,16,66,84,151],[48,129,82],[128,49,100],[128,49,66,16,82,98,151]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row16_0 : CutRow book 16 0 1 := bandCut 10 false (by decide +kernel)
theorem band16 : CutRow book 16 0 1 := row16_0
set_option maxRecDepth 16000 in
theorem row15_0 : CutRow book 15 0 10 := bandCut 11 true (by decide +kernel)
theorem band15 : CutRow book 15 0 10 := row15_0
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 7 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_7 : CutRow book 14 7 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_19 : CutRow book 14 19 9 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_28 : CutRow book 14 28 12 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_40 : CutRow book 14 40 8 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_48 : CutRow book 14 48 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x2f498004c3b2a047,0x2fca0004baa10847,0x18c4803b2a190848,0x16ca803b2a190848,0x18c4803b2a190848,0x18c4803b2a190848,0x174b003b2a190848,0x304b803b2a190848] i else tableWord #[0x18ad803b2a190848,0x18c4803b2a190848,0x18c4803b2a190848,0x18c4803b2a190848,0x18c4803b2a190848,0x1a2c003b2a190848,0x1aac803b2a190848,0x18ad803b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_64 : CutRow book 14 64 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x26cc003b2a190848,0x30cc804c32a10848,0x2bc18043b2a10848,0x2bc18043b2a10848,0x2bc18043b2a10848,0x314d0043b2a10848,0x31cd804c3b2a0848,0x324e0043b2a10848] i else tableWord #[0x32ce8043b2a10848,0x2bcf0043b2a10848,0x334f8043b2a10848,0x2bc18043b2a10848,0x2c4200432a190848,0x2c4200432a190848,0x2c4200432a190848,0x2c4200432a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_80 : CutRow book 14 80 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x2c4200432a190848,0x2c4200432a190848,0x33d0004bb2a18848,0x345080432a190848,0x34d100432a190848,0x2c4200432a190848,0x2c4200432a190848,0x2c4200432a190848] i else tableWord #[0x2c4200432a190848,0x3551803b2a190848,0x3551803b2a190848,0x35d200432a190848,0x3551803b2a190848,0x3652803b2a190848,0x3553003b2a190848,0x36d3804bb2190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_96 : CutRow book 14 96 4 := orderCut (pages:=fun j => ordered ((fun i => tableWord #[0x3551803b2a190848,0x3754003b2a190848,0x3551803b2a190848,0x18d4803b2a190848] i) j)) (by decide +kernel) (by decide +kernel)
theorem combine14_0_19 : CutRow book 14 0 19 := @joinRow book 14 0 7 12 row14_0 row14_7
theorem combine14_19_21 : CutRow book 14 19 21 := @joinRow book 14 19 9 12 row14_19 row14_28
theorem combine14_40_24 : CutRow book 14 40 24 := @joinRow book 14 40 8 16 row14_40 row14_48
theorem combine14_64_32 : CutRow book 14 64 32 := @joinRow book 14 64 16 16 row14_64 row14_80
theorem combine14_0_40 : CutRow book 14 0 40 := @joinRow book 14 0 19 21 combine14_0_19 combine14_19_21
theorem combine14_40_56 : CutRow book 14 40 56 := @joinRow book 14 40 24 32 combine14_40_24 combine14_64_32
theorem combine14_0_96 : CutRow book 14 0 96 := @joinRow book 14 0 40 56 combine14_0_40 combine14_40_56
theorem combine14_0_100 : CutRow book 14 0 100 := @joinRow book 14 0 96 4 combine14_0_96 row14_96
theorem band14 : CutRow book 14 0 100 := combine14_0_100
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 12 := bandCut 11 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_12 : CutRow book 13 12 5 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_17 : CutRow book 13 17 10 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_27 : CutRow book 13 27 1 := bandCut 13 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_28 : CutRow book 13 28 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x108400,0x108400,0x108400,0x108400,0x108400,0x108400,0x108400,0x108400] i else tableWord #[0x108400,0x108400,0x148401,0x148401,0x148401,0x148401,0x148401,0x148401] i) else (if i<24 then tableWord #[0x148401,0x148401,0x148401,0x148401,0x19041f,0x19041c,0x190420,0x10841d] i else tableWord #[0x10841d,0x10841d,0x10841d,0x10841d,0x10841d,0x19041c,0x219021,0x108422] i)) else (if i<40 then tableWord #[0x19041c,0x10841d,0x10841d,0x10841d,0x10841d,0x10841d,0x10841d,0x150c1e] i else tableWord #[0x150c23,0x190407,0x148418,0x148418,0x148418,0x148418,0x148418,0x148418] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_76 : CutRow book 13 76 28 := colorCut (ds:=fun j => panel ((fun i => (if i<16 then (if i<8 then tableWord #[0x148418,0x148418,0x148418,0x148418,0x148418,0x148418,0x150c24,0x190407] i else tableWord #[0x148425,0x148426,0x4444458c867,0x148428,0x148426,0x148426,0x148426,0x10840a] i) else (if i<24 then tableWord #[0x10840a,0x10840a,0x108429,0x10840a,0x190407,0x194414,0x194416,0x194414] i else tableWord #[0x19041c,0x190407,0x190407,0x190407] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_104 : CutRow book 13 104 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x38500002a190836,0x20300002a190836,0x8100002a190836,0x203000032190836,0x203000032190836,0x8580002a190836,0x203000032190836,0x203000032190836] i else tableWord #[0x406000032190836,0x203000032190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8580002a190836,0x8580002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_120 : CutRow book 13 120 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x20280002a190836,0x8100002a190836,0x202800032990836,0x202800032990836] i else tableWord #[0x202800032990836,0x8680002a190836,0x202800032990836,0x487000032990836,0x202800032990836,0x8100002a190836,0x8100002a190836,0x8100002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_136 : CutRow book 13 136 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x50780002a190836,0x8800002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836] i else tableWord #[0x8100002a190836,0x50780002a190836,0x50780002a190836,0x8100002a190836,0x8100002a190836,0x202800032990836,0x588800032990836,0x487000032990836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_152 : CutRow book 13 152 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x203000032190836,0x389000032190836,0x209800032190836,0x8100002a190836,0x8100002a190836,0x60a0888c2a190b6,0x8100002a190836,0x68a800043290836] i else tableWord #[0x20b000032190836,0x58b800032190836,0x20b000032190836,0x203000032190836,0x203000032190836,0x389000032190836,0x8100002a190836,0x8100002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_168 : CutRow book 13 168 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x60a0888c2a190b6,0x8100002a190836,0x70c000032a18836,0x70c000032a18836,0x78c8888bb2a18b6,0x80d000032a18836,0x88d800032a18836,0x88d800032a18836] i else tableWord #[0x88d800032a18836,0x88e000032a18836,0x90e800032a18836,0x98f00003aa18836,0xa0f800053298836,0xa90000053218836,0x910800032a18836,0xb11000032a18836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_184 : CutRow book 13 184 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x203000032190836,0xb91800032a10836,0x212000032190836,0xc1280003aa10836,0xc93000043210836,0x213800032190836,0xc1400003aa10836,0x214800032190836] i else tableWord #[0x8100002a190836,0x8100002a190836,0x8100002a190836,0x9500002a190836,0x9580002a190836,0xd1600002a190836,0x9580002a190836,0x9580002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_200 : CutRow book 13 200 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x71680002a190836,0x71680002a190836,0x71680002a190836,0x71680002a190836,0x71680002a190836,0x71680002a190836,0xd9700002a190836,0xe1780004aa10836] i else tableWord #[0xe9800002a190836,0x71680002a190836,0x204000032990836,0x8080002a190836,0x218800032990836,0x20400002a190836,0x8080002a190836,0x204000032990836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_216 : CutRow book 13 216 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x202800032990836,0x204000032990836,0x9900002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836,0x8100002a190836] i else tableWord #[0x50780002a190836,0x8100002a190836,0x8080002a190836,0x51980002a190836,0x8080002a190836,0x70c00002a190836,0x70c00002a190836,0x71680002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_232 : CutRow book 13 232 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x70c00002a190836,0xe1a000052a10836,0xe9a80002a190836,0xf1b00002a190836,0xf9b800052990836,0x101c000032990836,0x21c800032990836,0x109d00002a190836] i else tableWord #[0x203000032190836,0x21d800032190836,0x109e00002a190836,0x21d800032190836,0x9e80002a190836,0x9f00002a190836,0x8100002a190836,0x8100002a190836] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_248 : CutRow book 13 248 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x8080002a190836,0x9f80002a190836,0x70c000032a18836,0x9e80002a190836,0x70c000032a18836,0x1120000032a18836,0x70c000032a18836,0x9e80002a190836] i else tableWord #[0x70c000032a18836,0x202800032990836,0x52080002a190836,0x721000032a18836,0x721800032a18836,0x11a2000432a10847,0x1222800432a10847,0x12a3000432a10847] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_264 : CutRow book 13 264 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x1323800432990847,0x12a4000432a10847,0x12a4000432a10847,0x12a4000432a10847,0x12a4000432a10847,0x12a4000432a10847,0x13a4888c3b2a10c7,0x1425000432a10847] i else tableWord #[0x11a5800432a10847,0x13a4888c3b2a10c7,0x1425000432a10847,0x1326088c32a190c7,0x1222800432a10847,0x14a680043b2a0847,0x1527088c3b2190c7,0x15a78004b2a18847] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_280 : CutRow book 13 280 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x16280004aa190847,0x16a8803b2a190848,0x1729003b2a190848,0x17a9803b2a190848,0x182a003b2a190848,0x18aa803b2a190848,0x192b003b2a190848,0x19ab80432a190848] i else tableWord #[0x1a2c003b2a190848,0x1aac803b2a190848,0x18ad003b2a190848,0x18ad803b2a190848,0x1b2e003b2a190848,0x1b2e003b2a190848,0x1b2e003b2a190848,0x1bae803b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_296 : CutRow book 13 296 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x1c2f003b2a190848,0x1caf803b2a190848,0x1d30003b2a190848,0x1db0803b2a190848,0x1e31003b2a190848,0x1eb1803b2a190848,0x1b2e003b2a190848,0x1f32003b2a190848] i else tableWord #[0x1f32003b2a190848,0x1f32003b2a190848,0x1fb288cc3aa190c8,0x2033003b2a190848,0x20b3803b2a190848,0x2134004c2a190848,0x21b4803b2a190848,0x19b500432a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_312 : CutRow book 13 312 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x223588c3b2a190c8,0x22b600432a190848,0x1a2c003b2a190848,0x19b500432a190848,0x1ab6803b2a190848,0x233700432a190848,0x233700432a190848,0x233700432a190848] i else tableWord #[0x23b788c3b2a190c8,0x243800432a190848,0x24b880432a190848,0x23b788c3b2a190c8,0x2539003b2a190848,0x2539003b2a190848,0x25b988cc32a190c8,0x263a003b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_328 : CutRow book 13 328 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x26ba803b2a190848,0x26ba803b2a190848,0x273b004b2a190848,0x18bb803b2a190848,0x19ab80432a190848,0x18bc003b2a190848,0x27bc803b2a190848,0x18bd003b2a190848] i else tableWord #[0x1b2e003b2a190848,0x1b2e003b2a190848,0x1b2e003b2a190848,0x1b2e003b2a190848,0x283d8043aa190848,0x28be003b2a190848,0x223e803b2a190848,0x1d30003b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_344 : CutRow book 13 344 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x293f004b2a190848,0x293f004b2a190848,0x293f004b2a190848,0x293f004b2a190848,0x293f004b2a190848,0x293f004b2a190848,0x29bf804bb2a18848,0x2a40004baa190848] i else tableWord #[0x2ac088cbb2a190c8,0x2b41004b2a190848,0x2bc18043b2a10848,0x29bf804bb2a18848,0x2c4200432a190848,0x2a40004baa190848,0x2cc2804c32a18848,0x2d43004b2a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_360 : CutRow book 13 360 16 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x2dc3804b2a190848,0x18c4003b2a190848,0x18c4803b2a190848,0x18c5003b2a190848,0x18c5803b2a190848,0x18c4803b2a190848,0x18c6003b2a190848,0x2e46804c32190848] i else tableWord #[0x2a47004baa190848,0x184780432a190848,0x184800432a190848,0x18c4803b2a190848,0x1847803b2a190848,0x184780432a190848,0x18c8803b2a190848,0x184800432a190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_376 : CutRow book 13 376 1 := orderCut (pages:=fun j => ordered ((fun i => tableWord #[0x2ec9003b2a190848] i) j)) (by decide +kernel) (by decide +kernel)
theorem combine13_0_17 : CutRow book 13 0 17 := @joinRow book 13 0 12 5 row13_0 row13_12
theorem combine13_17_11 : CutRow book 13 17 11 := @joinRow book 13 17 10 1 row13_17 row13_27
theorem combine13_28_76 : CutRow book 13 28 76 := @joinRow book 13 28 48 28 row13_28 row13_76
theorem combine13_104_32 : CutRow book 13 104 32 := @joinRow book 13 104 16 16 row13_104 row13_120
theorem combine13_136_32 : CutRow book 13 136 32 := @joinRow book 13 136 16 16 row13_136 row13_152
theorem combine13_168_32 : CutRow book 13 168 32 := @joinRow book 13 168 16 16 row13_168 row13_184
theorem combine13_200_32 : CutRow book 13 200 32 := @joinRow book 13 200 16 16 row13_200 row13_216
theorem combine13_232_32 : CutRow book 13 232 32 := @joinRow book 13 232 16 16 row13_232 row13_248
theorem combine13_264_32 : CutRow book 13 264 32 := @joinRow book 13 264 16 16 row13_264 row13_280
theorem combine13_296_32 : CutRow book 13 296 32 := @joinRow book 13 296 16 16 row13_296 row13_312
theorem combine13_328_32 : CutRow book 13 328 32 := @joinRow book 13 328 16 16 row13_328 row13_344
theorem combine13_360_17 : CutRow book 13 360 17 := @joinRow book 13 360 16 1 row13_360 row13_376
theorem combine13_0_28 : CutRow book 13 0 28 := @joinRow book 13 0 17 11 combine13_0_17 combine13_17_11
theorem combine13_28_108 : CutRow book 13 28 108 := @joinRow book 13 28 76 32 combine13_28_76 combine13_104_32
theorem combine13_136_64 : CutRow book 13 136 64 := @joinRow book 13 136 32 32 combine13_136_32 combine13_168_32
theorem combine13_200_64 : CutRow book 13 200 64 := @joinRow book 13 200 32 32 combine13_200_32 combine13_232_32
theorem combine13_264_64 : CutRow book 13 264 64 := @joinRow book 13 264 32 32 combine13_264_32 combine13_296_32
theorem combine13_328_49 : CutRow book 13 328 49 := @joinRow book 13 328 32 17 combine13_328_32 combine13_360_17
theorem combine13_0_136 : CutRow book 13 0 136 := @joinRow book 13 0 28 108 combine13_0_28 combine13_28_108
theorem combine13_136_128 : CutRow book 13 136 128 := @joinRow book 13 136 64 64 combine13_136_64 combine13_200_64
theorem combine13_264_113 : CutRow book 13 264 113 := @joinRow book 13 264 64 49 combine13_264_64 combine13_328_49
theorem combine13_0_264 : CutRow book 13 0 264 := @joinRow book 13 0 136 128 combine13_0_136 combine13_136_128
theorem combine13_0_377 : CutRow book 13 0 377 := @joinRow book 13 0 264 113 combine13_0_264 combine13_264_113
theorem band13 : CutRow book 13 0 377 := combine13_0_377
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_1 : CutRow book 12 1 16 := mixedCut (data:=fun j => treeData plus minus ((fun i => (if i<8 then tableWord #[0x103080a450,0x103080a450,0x103080a450,0x440804340,0x440804340,0x440804340,0x103080a450,0x103080a450] i else tableWord #[0x440804340,0x440804340,0xc2104a192,0x255044021,0x103080a450,0x103080a450,0x440804340,0x440804340] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_17 : CutRow book 12 17 48 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x108400,0x108400,0x108400,0x108400,0x108401,0x148401,0x148401,0x108401] i else tableWord #[0x148401,0x148401,0x148401,0x108402,0x148401,0xc8403,0xc8404,0xc8404] i) else (if i<24 then tableWord #[0x4444454c845,0x4444454c845,0x108400,0x108400,0x108400,0x108400,0x108400,0x108400] i else tableWord #[0x108400,0x108400,0x108400,0x108400,0x148401,0x148401,0x108400,0x1d4c06] i)) else (if i<40 then tableWord #[0x14c407,0x150408,0x150407,0x150407,0x108409,0x190407,0x10840a,0x150c0b] i else tableWord #[0x150c0c,0x108400,0x10c80d,0x108400,0x150c0d,0x10840a,0x14c80e,0x14c80e] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_65 : CutRow book 12 65 41 := colorCut (ds:=fun j => panel ((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x14c80e,0x14c80f,0x14c80e,0x14c810,0x14c811,0x14c80e,0x14c812,0x10c80d] i else tableWord #[0x888889d0c93,0x10c80d,0x10c80d,0x150414,0x150414,0x150414,0x150414,0x148401] i) else (if i<24 then tableWord #[0x150414,0x150415,0x150407,0x150407,0x108400,0x150407,0x44444550c4f,0x150407] i else tableWord #[0x44444550c4f,0x108400,0x194414,0x194414,0x194416,0x194414,0x195017,0x194415] i)) else (if i<40 then tableWord #[0x148418,0x194419,0x19441a,0x14841b,0x14c41c,0x10841d,0x150c1e,0x44444590c4f] i else tableWord #[0x150c1e] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_106 : CutRow book 12 106 14 := orderCut (pages:=fun j => ordered ((fun i => (if i<8 then tableWord #[0x42a0835,0x8080002a190836,0x8100002a190836,0x101800032190836,0x182000032190836,0x20280002a190836,0x20280002a190836,0x8100002a190836] i else tableWord #[0x20280002a190836,0x20300002a190836,0x28380003b2a1036,0x204000032990836,0x8080002a190836,0x30480003b218846] i)) j)) (by decide +kernel) (by decide +kernel)
theorem combine12_0_17 : CutRow book 12 0 17 := @joinRow book 12 0 1 16 row12_0 row12_1
theorem combine12_17_89 : CutRow book 12 17 89 := @joinRow book 12 17 48 41 row12_17 row12_65
theorem combine12_0_106 : CutRow book 12 0 106 := @joinRow book 12 0 17 89 combine12_0_17 combine12_17_89
theorem combine12_0_120 : CutRow book 12 0 120 := @joinRow book 12 0 106 14 combine12_0_106 row12_106
theorem band12 : CutRow book 12 0 120 := combine12_0_120
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 2 := mixedCut (data:=fun j => treeData plus minus ((fun i => tableWord #[0xc2104a172,0x255044021] i) j)) (by decide +kernel) (by decide +kernel)
theorem band11 : CutRow book 11 0 2 := row11_0
theorem checked : mixedTables book 16 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band11
  · exact band12
  · exact band13
  · exact band14
  · exact band15
  · exact band16
end M1023_17
theorem m1023_17 : Face false 1023 17 :=
  mixedLower (g:=M1023_17.book) (i:=0) (hints:=296906400036)
    (before_sound M1023_17.entries M1023_17.prior) M1023_17.geometry M1023_17.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem signedRoot : Impossible true graph 15 inputs.toFinset := by
  rw [show graph = targetOf B1023_16.book by decide +kernel]
  exact mixedRoot (g:=B1023_16.book) (top:=15) (i:=0) (before_sound B1023_16.entries B1023_16.prior)
    B1023_16.geometry B1023_16.checked (by decide) (by decide +kernel)
theorem monoRoot : Impossible false graph 16 inputs.toFinset := by
  rw [show graph = targetOf M1023_17.book by decide +kernel]
  exact mixedRoot (g:=M1023_17.book) (top:=16) (i:=0) (before_sound M1023_17.entries M1023_17.prior)
    M1023_17.geometry M1023_17.checked (by decide) (by decide +kernel)
end Engine
end PEqualNP.Outside.L_meta_9825

theorem PEqualNP.Outside.L_meta_9825 : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)) 16) :=
  PEqualNP.Outside.L_meta_9825.Engine.directSplit
    PEqualNP.Outside.L_meta_9825.Engine.monoRoot PEqualNP.Outside.L_meta_9825.Engine.signedRoot
