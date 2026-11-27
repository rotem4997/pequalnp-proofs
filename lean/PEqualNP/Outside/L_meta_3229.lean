import PEqualNP.Defs
-- The verified induced-subgraph bounds, their forest certificates, and parts of the live-wire
-- argument are adapted from the project's L_meta_1669.lean (Apache License 2.0).
-- The monotone frontier, cofactor menus and data for the prescribed OR input are new.
namespace PEqualNP.Outside.L_meta_3229
namespace B
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))
private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v
def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a
inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩
theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
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
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]
theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
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
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih
theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
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
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]
theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 3) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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
theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel
theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed
theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
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
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv
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
theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
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
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
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
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
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
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
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
theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
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
theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)
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
def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))
theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)
theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)
def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
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
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)
theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
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
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)
theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)
theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def apart (m j : Nat) : Bool := m.testBit 9 && (j==0 || j==3)
def word (m j : Nat) : Sig := if apart m j then inputs.getD j zero &&& ~~~seed else inputs.getD j zero
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,word m i) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then word m j else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) :=
  let f := m ^^^ (m &&& (z ||| o))
  if f.testBit 9 && ((z ||| o) &&& 9) != 0 then f ^^^ 512 else f
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
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
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True
theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
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
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)
theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he
abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
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
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
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
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
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
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def wordCol (m : Nat) (v : Nat → Bits) (j : Nat) : Bits :=
  if apart m j then v j &&& ~~~(v 0 &&& v 3) else v j
theorem seed_word : seed = inputs.getD 0 zero &&& inputs.getD 3 zero := by decide +kernel
theorem word_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (word m j.val) = (wordCol m v j.val).getLsbD i.val := by
  by_cases h : apart m j.val = true
  · have e := asRow_bit v i j
    have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (3 : Fin 9)
    change (inputs.getD j.val zero).getLsbD (asRow v i).val = _ at e
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 3 zero).getLsbD (asRow v i).val = (v 3).getLsbD i.val at w
    rw [word,wordCol,if_pos h,if_pos h,seed_word]
    simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,e,u,w]
  · rw [word,wordCol,if_neg h,if_neg h]
    exact asRow_bit v i j
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,wordCol m p j,wordCol m q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=word m j := by
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
  · exact (word_bit m p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (word_bit m q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then wordCol m v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then wordCol m v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using word_bit m v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then wordCol m v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs
theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
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
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
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
  exact hi k t hk run
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)
structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask _ _
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
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
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
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
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl
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
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js
theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
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
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
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
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
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
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def zeroPrior (q : Nat) := if q=111 then 7 else boundsBefore known383 q
theorem zeroPrior_sound (q : Nat) : Lower (vars q) (graphGoal q) (zeroPrior q) := by
  by_cases h : q=111
  · subst q; exact low111
  · simpa only [zeroPrior,if_neg h] using before_sound known383 valid383 q
end B
namespace B
def Compatible {R S : Type} (anchor : S → R) (label : S → Bool)
    (a : Wire R) (b : Wire S) : Prop :=
  ∀ s, a (anchor s) = label s → b s = label s
theorem compatible_bin {R S anchor label a a' b b'} {op : Bool}
    (h : @Compatible R S anchor label a a')
    (j : Compatible anchor label b b') :
    Compatible anchor label (combine op a b) (combine op a' b') := by
  intro s
  have A := h s
  have B := j s
  cases op <;> cases z : label s <;> cases p : a (anchor s) <;> cases q : b (anchor s) <;>
    simp_all [combine]
inductive MRun {R : Type} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : MRun goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → MRun goal s xs → MRun goal s zs
  | two {s a b rest} (op ka kb : Bool) :
      MRun goal s (combine op a b :: kept ka a (kept kb b rest)) →
      MRun goal (s+1) (a::b::rest)
theorem kept_forall₂ {A B} {r : A → B → Prop} (k : Bool) {a b xs ys}
    (h : r a b) (t : xs.Forall₂ r ys) :
    (kept k a xs).Forall₂ r (kept k b ys) := by
  cases k <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true]
  · exact t
  · exact .cons h t
theorem transfer {R S T k xs} (anchor : S → R) (G : Wire S)
    (covered : ∀ s, T (anchor s) = G s) (run : MRun T k xs)
    {ys : List (Wire S)} (rel : xs.Forall₂ (Compatible anchor G) ys) :
    Run G k ys := by
  induction run generalizing ys with
  | stop =>
    cases rel with
    | cons h tt =>
      cases tt
      have e : _ = G := funext fun s => h s (covered s)
      rw [e]
      exact .stop
  | perm p _ ih =>
    obtain ⟨mid,hm,hp⟩ := List.perm_comp_forall₂ p rel
    exact .perm hp (ih hm)
  | two op ka kb _ ih =>
    cases rel with
    | cons h ht =>
      cases ht with
      | cons j jt =>
        exact .two op ka kb (ih (.cons (compatible_bin h j)
          (kept_forall₂ ka h (kept_forall₂ kb j jt))))
theorem directional_leaf {R S T k xs} {anchor : S → R} {G : Wire S}
    (covered : ∀ s, T (anchor s) = G s) (run : MRun T k xs)
    {ys : List (Wire S)} (rel : xs.Forall₂ (Compatible anchor G) ys)
    {roots : List (Wire S)} {p bank L c}
    (hp : Reach roots p bank) (hs : supply bank ys) (hnc : ¬Constant G)
    (hl : ∀ q bs, Reach roots q bs → Available bs G → L ≤ q)
    (constants : c ≤ mass ys) : L+c ≤ p+k := by
  obtain ⟨q,bs,hq,hg,hle⟩ := contraction hnc (transfer anchor G covered run rel) roots hp hs
  have := hl q bs hq hg
  omega
inductive Menu where
  | lit (v : Bool)
  | var (i : Nat)
  | gate (d : Bool) (a b : Menu)
  deriving Repr, DecidableEq
def Menu.value {S : Type} (raw : Nat → Wire S) : Menu → Wire S
  | .lit v => fun _ => v
  | .var i => raw i
  | .gate d a b => combine d (a.value raw) (b.value raw)
def Menu.size : Menu → Nat
  | .lit _ | .var _ => 0
  | .gate _ a b => a.size + b.size + 1
def Menu.literal : Menu → Bool
  | .lit _ => true
  | _ => false
theorem Menu.realize {S roots p bank} {raw : Nat → Wire S}
    (hvars : ∀ i, Available bank (raw i)) (hp : Reach roots p bank) (e : Menu) :
    ∃ next, Reach roots (p+e.size) next ∧ Available next (e.value raw) ∧
      ∀ v, Available bank v → Available next v := by
  induction e generalizing p bank with
  | lit v => exact ⟨_,hp,Or.inr ⟨v,rfl⟩,fun _ h => h⟩
  | var i => exact ⟨_,hp,hvars i,fun _ h => h⟩
  | gate d a b ia ib =>
    obtain ⟨b1,h1,va,inc1⟩ := ia hvars hp
    obtain ⟨b2,h2,vb,inc2⟩ := ib (fun i => inc1 _ (hvars i)) h1
    have pr := Reach.two d h2 (inc2 _ va) vb
    refine ⟨_,by simpa [Menu.size,Nat.add_assoc] using pr,?_,?_⟩
    · exact Or.inl (by simp [Menu.value])
    · exact fun v hv => available_cons _ (inc2 _ (inc1 _ hv))
theorem menuList_realize {S roots p bank} {raw : Nat → Wire S}
    (hvars : ∀ i, Available bank (raw i)) (hp : Reach roots p bank) (es : List Menu) :
    ∃ next, Reach roots (p+(es.map Menu.size).sum) next ∧
      supply next (es.map (Menu.value raw)) ∧ ∀ v, Available bank v → Available next v := by
  induction es generalizing p bank with
  | nil => exact ⟨_,hp,by simp [supply],fun _ h => h⟩
  | cons e es ih =>
    obtain ⟨b1,h1,ve,inc1⟩ := e.realize hvars hp
    obtain ⟨b2,h2,su,inc2⟩ := ih (fun i => inc1 _ (hvars i)) h1
    refine ⟨b2,by simpa [Nat.add_assoc] using h2,?_,fun v => (inc2 v) ∘ (inc1 v)⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | h
    · exact inc2 _ ve
    · exact su _ h
theorem menu_literals {S} (raw : Nat → Wire S) (es : List Menu) :
    es.countP Menu.literal ≤ mass (es.map (Menu.value raw)) := by
  induction es with
  | nil => simp [mass]
  | cons e es ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases e with
    | lit v =>
      have hc : Constant ((Menu.lit v).value raw) := ⟨v,rfl⟩
      simp [Menu.literal,cost,hc]; omega
    | var i => simpa [Menu.literal] using (Nat.le_add_left _ _ |> ih.trans)
    | gate d a b => simpa [Menu.literal] using (Nat.le_add_left _ _ |> ih.trans)
theorem menu_leaf {R S T k xs} {anchor : S → R} {G : Wire S}
    (covered : ∀ s, T (anchor s) = G s) (run : MRun T k xs)
    {raw : Nat → Wire S} (es : List Menu)
    (rel : xs.Forall₂ (Compatible anchor G) (es.map (Menu.value raw)))
    {roots : List (Wire S)} {L} (vars : ∀ i, Available roots (raw i)) (hnc : ¬Constant G)
    (hl : ∀ q bs, Reach roots q bs → Available bs G → L ≤ q) :
    L+es.countP Menu.literal ≤ (es.map Menu.size).sum+k := by
  obtain ⟨b,hr,sup,_⟩ := menuList_realize vars Reach.start es
  exact directional_leaf covered run rel (by simpa using hr) sup hnc hl (menu_literals raw es)
namespace Zero3229
abbrev BRow := Fin 24
abbrev BWord := BitVec 24
def bt (a : BWord) (r : BRow) : Bool := a.getLsbD r.val
def target : BWord := 4095
def raw (i : Fin 9) : BWord := #[0x544031,0x823043,0x314086,0x6910c,0xa92018,0x1ba20,0xdc440,0xce0280,0xf00d00][i.val]!
def cone (j : BRow) : Sig := #[0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000,0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000,0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000,0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000,0xffffffff00000000ffffffff0000000000000000000000000000000000000000ffffffff00000000ffffffff0000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000,0x50500000505,0x5000500050005,0x330000000000000033,0x101000001010000010100000101,0x110011001100110011001100110011,0x50500000000000000000000000000000505,0x303000000000000030300000000000003030000000000000303,0x10001000000000001000100000000000100010000000000010001,0x330000000000000000000000000000000000000000000000000000000000000033,0x1100110000000000000000000000000000000000000000000000000000000000110011,0x3000000000000000000000000000000030000000000000000000000000000000300000000000000000000000000000003,0x50005000000000000000000000000000500050000000000000000000000000005000500000000000000000000000000050005][j.val]!
def wordLabel (a : Sig) (b : Bool) : Sig := if b then a else ~~~a
def coversB (a b : Sig) := (a &&& b) == a
theorem coversB_sound {a b : Sig} (h : coversB a b = true) {r : Row} (hr : bit r a = true) :
    bit r b = true := by
  have e := congrArg (bit r) (beq_iff_eq.mp h)
  simpa only [bit,BitVec.getLsbD_and,show a.getLsbD r.val = true from hr,Bool.true_and] using e
theorem bit_wordLabel (r : Row) (a : Sig) (b : Bool)
    (h : bit r (wordLabel a b) = true) : bit r a = b := by
  cases b
  · simpa only [wordLabel,Bool.false_eq_true,if_false,bit,BitVec.getLsbD_not,r.isLt,decide_true,
      Bool.true_and,Bool.not_eq_true'] using h
  · exact h
set_option maxHeartbeats 1000000 in
theorem cone_labels : ∀ j : BRow, coversB (cone j) (wordLabel graph (bt target j)) = true := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem cone_inputs : ∀ (j : BRow) (i : Fin 9),
    bt (raw i) j = bt target j →
    coversB (cone j) (wordLabel (inputs.getD i.val zero) (bt target j)) = true := by decide +kernel
theorem cone_label {r : Row} {j : BRow} (h : bit r (cone j) = true) :
    bt target j = bit r graph :=
  (bit_wordLabel _ _ _ (coversB_sound (cone_labels j) h)).symm
theorem cone_raw {r : Row} {j : BRow} (h : bit r (cone j) = true) (i : Fin 9)
    (hp : bt (raw i) j = bt target j) : sample r i = bit r graph :=
  (bit_wordLabel _ _ _ (coversB_sound (cone_inputs j i hp) h)).trans (cone_label h)
def foldCones (a : BWord) : List BRow → Sig
  | [] => zero
  | j::js => if bt a j then cone j ||| foldCones a js else foldCones a js
def coverWord (a : BWord) : Sig := foldCones a (List.finRange 24)
theorem findCones (a : BWord) (r : Row) (js) (h : bit r (foldCones a js) = true) :
    ∃ j, js.find? (fun j => bt a j && bit r (cone j)) = some j ∧
      bt a j = true ∧ bit r (cone j) = true := by
  induction js with
  | nil => simp [foldCones,bit,zero] at h
  | cons j js ih =>
    cases ha : bt a j
    · simp only [foldCones,ha,Bool.false_eq_true,if_false] at h
      simpa [List.find?_cons,ha] using ih h
    · cases hc : bit r (cone j)
      · have hv : bit r (foldCones a js) = true := by
          simpa only [foldCones,ha,if_true,bit,BitVec.getLsbD_or,
            show (cone j).getLsbD r.val = false from hc,Bool.false_or] using h
        simpa [List.find?_cons,ha,hc] using ih hv
      · exact ⟨j,by simp [List.find?_cons,ha,hc],ha,hc⟩
def anchor (a : BWord) (r : Row) : BRow :=
  ((List.finRange 24).find? (fun j => bt a j && bit r (cone j))).getD 0
theorem anchor_good (a : BWord) (r : Row) (h : bit r (coverWord a) = true) :
    bt a (anchor a r) = true ∧ bit r (cone (anchor a r)) = true := by
  obtain ⟨j,ej,ha,hc⟩ := findCones a r _ h
  simpa [anchor,ej] using And.intro ha hc
structure Chart where
  z : Nat
  o : Nat
  q : Nat
  sing : Nat
  L : Nat
  active : BWord
def Chart.moves (c : Chart) := fixRows c.z c.o
def Chart.A (c : Chart) (r : Row) : BRow := anchor c.active (movedRow c.moves r)
def Chart.free (c : Chart) := colFree 511 c.z c.o
def Chart.gsig (c : Chart) := movedWord c.moves graph
def Chart.G (c : Chart) : Wire Row := observe c.gsig
def Chart.X (c : Chart) (i : Fin 9) : Wire Row := restrictRows (movedRow c.moves) (fun r => sample r i)
def Chart.roots (c : Chart) := (vars c.free).map observe
def checkChart (c : Chart) := properB c.gsig &&
  checkMap c.moves inputs graph (vars c.free) c.gsig &&
  (movedWord c.moves (coverWord c.active) == one)
structure Valid (c : Chart) : Prop where
  covered : ∀ s, bt target (c.A s) = c.G s
  active : ∀ s, bt c.active (c.A s) = true
  input (i : Fin 9) : Compatible c.A c.G (bt (raw i)) (c.X i)
  supplied (i : Fin 9) : Available c.roots (c.X i)
  nonconstant : ¬Constant c.G
theorem checkChart_sound {c} (ok : checkChart c = true) : Valid c := by
  simp only [checkChart,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨properC,mapC⟩,active⟩ := ok
  obtain ⟨g,supp⟩ := map_correct mapC
  have goalId (s : Row) : c.G s = bit (movedRow c.moves s) graph := by
    change bit s c.gsig = _
    rw [←g,bit_rename]
  have covers (s : Row) : bit (movedRow c.moves s) (coverWord c.active) = true := by
    have e := congrArg (bit s) active
    rw [bit_moved] at e
    exact e.trans (by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp [s.isLt])
  have good (s : Row) := anchor_good c.active _ (covers s)
  refine ⟨?_,?_,?_,?_,observe_proper (proper_of _ properC)⟩
  · intro s
    exact (cone_label (good s).2).trans (goalId _).symm
  · intro s
    exact (good s).1
  · intro i s hs
    rw [goalId] at hs ⊢
    exact cone_raw (good s).2 i ((cone_label (good s).2).trans hs.symm).symm
  · intro i
    have mem : inputs.getD i.val zero ∈ inputs := by
      have mem' := List.mem_ofFn.mpr (show ∃ j : Fin 9, inputs.getD j.val zero = inputs.getD i.val zero from ⟨i,rfl⟩)
      rw [input_list] at mem'
      exact mem'
    have h := supp _ mem
    rw [observe_rename] at h
    exact h
def safeB (c : Chart) (w src : BWord) : Bool :=
  (((~~~(w ^^^ target)) &&& (src ^^^ target)) &&& c.active) == 0
theorem safeB_sound {c : Chart} (cv : Valid c) {w src : BWord} {f : Wire Row}
    (h : Compatible c.A c.G (bt src) f) (ok : safeB c w src = true) :
    Compatible c.A c.G (bt w) f := by
  intro r hr
  apply h
  have eq := beq_iff_eq.mp ok
  have e := congrArg (fun v : BWord => bt v (c.A r)) eq
  have pr := cv.covered r
  have ac := cv.active r
  change w.getLsbD (c.A r).val = c.G r at hr
  change target.getLsbD (c.A r).val = c.G r at pr
  change c.active.getLsbD (c.A r).val = true at ac
  simp only [bt,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,
    BitVec.getLsbD_zero,(c.A r).isLt,decide_true,Bool.true_and,ac,Bool.and_true,hr,pr] at e
  change src.getLsbD (c.A r).val = c.G r
  cases hs : src.getLsbD (c.A r).val <;> cases hg : c.G r <;> simp_all
def checkLB (c : Chart) (prior : Nat → Nat) : Bool :=
  let xs := supportPairs c.sing
  properB c.gsig && properB (graphGoal c.q) &&
    checkLift (fixRows (colFree c.free c.q 0) 0) c.gsig (vars c.free) (vars c.q) (graphGoal c.q) xs &&
    decide (c.L ≤ prior c.q + (xs.map Prod.fst).toFinset.card)
theorem checkLB_sound {c : Chart} {prior : Nat → Nat}
    (h : ∀ q, Lower (vars q) (graphGoal q) (prior q)) (ok : checkLB c prior = true) :
    ∀ p bs, Reach c.roots p bs → Available bs c.G → c.L ≤ p := by
  simp only [checkLB,Bool.and_eq_true,decide_eq_true_eq] at ok
  intro p bs hr hit
  exact ok.2.trans (lift_ok ok.1.2 (proper_of _ ok.1.1.1) (proper_of _ ok.1.1.2)
    (h c.q) p bs hr hit)
end Zero3229
namespace Zero3229
def X (c : Chart) (i : Nat) : Wire Row := if h : i<9 then c.X ⟨i,h⟩ else fun _ => false
def word : Menu → BWord
  | .lit v => if v then BitVec.allOnes 24 else 0
  | .var i => if h : i<9 then raw ⟨i,h⟩ else 0
  | .gate d a b => if d then word a ||| word b else word a &&& word b
theorem bt_lit (v : Bool) (j : BRow) :
    bt (if v then BitVec.allOnes 24 else 0) j = v := by
  have h : ∀ (v : Bool) (j : BRow), bt (if v then BitVec.allOnes 24 else 0) j = v := by decide +kernel
  exact h v j
theorem bt_gate (d : Bool) (a b : BWord) :
    bt (if d then a ||| b else a &&& b) = combine d (bt a) (bt b) := by
  funext r
  cases d <;> simp [bt,combine,BitVec.getLsbD_and,BitVec.getLsbD_or]
theorem word_sound {c : Chart} (cv : Valid c) (e : Menu) :
    Compatible c.A c.G (bt (word e)) (e.value (X c)) := by
  induction e with
  | lit v =>
    intro r h
    exact (bt_lit v (c.A r)).symm.trans h
  | var i =>
    by_cases h : i<9
    · simpa [word,X,h,Menu.value] using cv.input ⟨i,h⟩
    · intro r hr; simpa [word,X,h,bt,Menu.value] using hr
  | gate d a b ia ib =>
    have H := compatible_bin (op:=d) ia ib
    simpa only [word,bt_gate,Menu.value] using H
def menuListOK (c : Chart) : List BWord → List Menu → Bool
  | [], [] => true
  | w::ws, e::es => safeB c w (word e) && menuListOK c ws es
  | _,_ => false
theorem menuList_sound {c : Chart} (cv : Valid c) {ws es} (ok : menuListOK c ws es = true) :
    (ws.map bt).Forall₂ (Compatible c.A c.G) (es.map (Menu.value (X c))) := by
  induction ws generalizing es with
  | nil => cases es <;> simp_all [menuListOK]
  | cons w ws ih =>
    cases es with
    | nil => simp [menuListOK] at ok
    | cons e es =>
      simp only [menuListOK,Bool.and_eq_true] at ok
      exact .cons (safeB_sound cv (word_sound cv e) ok.1) (ih ok.2)
theorem denied {c ws k} (cv : Valid c)
    (lb : ∀ p bs, Reach c.roots p bs → Available bs c.G → c.L ≤ p)
    (es : List Menu) (ok : menuListOK c ws es = true)
    (small : (es.map Menu.size).sum + k < c.L + es.countP Menu.literal) :
    ¬MRun (bt target) k (ws.map bt) := by
  intro hr
  have hvars (i : Nat) : Available c.roots (X c i) := by
    by_cases h : i<9
    · simpa [X,h] using cv.supplied ⟨i,h⟩
    · exact Or.inr ⟨false, by simp [X,h]⟩
  have hh := menu_leaf cv.covered hr es (menuList_sound cv ok) hvars cv.nonconstant lb
  omega
end Zero3229
end B
namespace B
namespace Zero3229
def chart0 : Chart := ⟨64,0,447,0,13,0xf73bbf⟩
def chart1 : Chart := ⟨128,0,383,0,13,0xb5fd7f⟩
def chart2 : Chart := ⟨16,0,495,0,13,0xd7dfe7⟩
def chart3 : Chart := ⟨1,0,510,0,12,0xafbfce⟩
def chart4 : Chart := ⟨8,0,503,0,12,0xfd6ef3⟩
def chart5 : Chart := ⟨24,0,487,0,11,0xd56ee3⟩
def chart6 : Chart := ⟨24,0,487,0,11,0xd55ee3⟩
def chart7 : Chart := ⟨17,0,494,0,11,0x979fc6⟩
def chart8 : Chart := ⟨17,0,494,0,11,0xa79fc6⟩
def chart9 : Chart := ⟨2,0,509,0,12,0xfdcfbc⟩
def chart10 : Chart := ⟨32,0,479,0,12,0xff45df⟩
def chart11 : Chart := ⟨256,0,255,0,12,0x8ff2ff⟩
def chart12 : Chart := ⟨4,0,507,0,12,0xcfbf79⟩
def chart13 : Chart := ⟨132,0,379,0,11,0x95bd79⟩
def chart14 : Chart := ⟨160,0,351,0,11,0xb7455f⟩
def chart15 : Chart := ⟨80,0,431,0,11,0xd71ba7⟩
def chart16 : Chart := ⟨144,0,367,0,11,0x95dd67⟩
def chart17 : Chart := ⟨132,0,379,0,11,0xc5bd79⟩
def chart18 : Chart := ⟨66,0,445,0,11,0xf58bbc⟩
def chart19 : Chart := ⟨320,0,191,0,11,0x9732bf⟩
def chart20 : Chart := ⟨320,0,191,0,11,0x8772bf⟩
def chart21 : Chart := ⟨192,0,319,0,11,0xb5393f⟩
def chart22 : Chart := ⟨66,0,445,0,11,0xf51bbc⟩
def chart23 : Chart := ⟨25,0,486,0,8,0x992ec2⟩
def chart24 : Chart := ⟨9,16,486,0,8,0xa92ec2⟩
def chart25 : Chart := ⟨136,0,375,0,9,0xb16c73⟩
def chart26 : Chart := ⟨3,0,508,0,9,0xad8f8c⟩
def chart27 : Chart := ⟨33,0,478,0,9,0xaf05ce⟩
def chart28 : Chart := ⟨129,0,382,0,9,0xa1bd4e⟩
def chart29 : Chart := ⟨12,0,499,0,9,0xcd2e71⟩
def chart30 : Chart := ⟨264,0,247,0,9,0x8d62f3⟩
def chart31 : Chart := ⟨65,0,446,0,9,0xa33b8e⟩
def chart32 : Chart := ⟨67,0,444,0,8,0xa51b8c⟩
def chart33 : Chart := ⟨81,0,430,0,8,0x931b86⟩
def chart34 : Chart := ⟨67,0,444,0,8,0xa58b8c⟩
def chart35 : Chart := ⟨67,0,444,0,8,0xa31b8c⟩
def chart36 : Chart := ⟨280,0,231,0,8,0x8552e3⟩
def chart37 : Chart := ⟨161,0,350,0,8,0xa1954e⟩
def chart38 : Chart := ⟨280,0,231,0,8,0x762e3⟩
def chart39 : Chart := ⟨328,0,183,0,8,0x9522b3⟩
def chart40 : Chart := ⟨328,0,183,0,8,0xd122b3⟩
def chart41 : Chart := ⟨280,0,231,0,8,0x752e3⟩
def chart42 : Chart := ⟨140,0,371,0,8,0x952c71⟩
def chart43 : Chart := ⟨152,0,359,0,8,0x916c63⟩
def chart44 : Chart := ⟨152,0,359,0,8,0x915c63⟩
def chart45 : Chart := ⟨145,0,366,0,8,0xa19d46⟩
def chart46 : Chart := ⟨140,0,371,0,8,0xc16c71⟩
def chart47 : Chart := ⟨140,0,371,0,8,0x916c71⟩
def chart48 : Chart := ⟨140,0,371,0,8,0xc52c71⟩
def chart49 : Chart := ⟨19,0,492,0,8,0x658f84⟩
def chart50 : Chart := ⟨19,0,492,0,8,0x558f84⟩
def chart51 : Chart := ⟨49,0,462,0,8,0x9705c6⟩
def chart52 : Chart := ⟨49,0,462,0,8,0xa645c6⟩
def chart53 : Chart := ⟨49,0,462,0,8,0x9645c6⟩
def chart54 : Chart := ⟨344,0,167,0,7,0xd112a3⟩
def chart55 : Chart := ⟨156,0,355,0,7,0x949c61⟩
def chart56 : Chart := ⟨83,0,428,0,7,0x951b84⟩
def chart57 : Chart := ⟨83,0,428,0,7,0x538b84⟩
def chart58 : Chart := ⟨83,0,428,0,7,0x551b84⟩
def chart59 : Chart := ⟨83,0,428,0,7,0xa31b84⟩
def chart60 : Chart := ⟨344,0,167,0,7,0x1722a3⟩
def chart61 : Chart := ⟨83,0,428,0,7,0x531b84⟩
def chart62 : Chart := ⟨83,0,428,0,7,0x658b84⟩
def chart63 : Chart := ⟨156,0,355,0,7,0x916c61⟩
def chart64 : Chart := ⟨156,0,355,0,7,0x90ec61⟩
def chart65 : Chart := ⟨156,0,355,0,7,0xc0ec61⟩
def chart66 : Chart := ⟨156,0,355,0,7,0xc0dc61⟩
def chart67 : Chart := ⟨156,0,355,0,7,0xc52c61⟩
def chart68 : Chart := ⟨156,0,355,0,7,0x90dc61⟩
def chart69 : Chart := ⟨156,0,355,0,7,0xc49c61⟩
def chart70 : Chart := ⟨344,0,167,0,7,0x1712a3⟩
def chart71 : Chart := ⟨177,0,334,0,7,0xa70546⟩
def chart72 : Chart := ⟨177,0,334,0,7,0x964546⟩
def chart73 : Chart := ⟨177,0,334,0,7,0x92c546⟩
def chart74 : Chart := ⟨83,0,428,0,7,0x558b84⟩
def chart75 : Chart := ⟨177,0,334,0,7,0xa19546⟩
def chart76 : Chart := ⟨0,128,347,36,10,0xce07d9⟩
def chart77 : Chart := ⟨0,64,189,258,10,0xdc6fc⟩
def chart78 : Chart := ⟨4,128,347,32,9,0xce0759⟩
def chart79 : Chart := ⟨288,0,223,0,9,0x8f40df⟩
def chart80 : Chart := ⟨130,0,381,0,9,0x35cd3c⟩
def chart81 : Chart := ⟨32,128,347,4,9,0xce05d9⟩
def chart82 : Chart := ⟨256,64,189,2,9,0xdc2fc⟩
def chart83 : Chart := ⟨384,0,127,0,9,0x5f07f⟩
def chart84 : Chart := ⟨2,64,189,256,9,0xdc6bc⟩
def chart85 : Chart := ⟨6,0,505,0,9,0xcd8f38⟩
def chart86 : Chart := ⟨96,0,415,0,9,0xf6019f⟩
def chart87 : Chart := ⟨322,0,189,0,8,0xdc2bc⟩
def chart88 : Chart := ⟨194,0,317,0,8,0x35193c⟩
def chart89 : Chart := ⟨164,0,347,0,8,0xcc1559⟩
def chart90 : Chart := ⟨416,0,95,0,8,0x7605f⟩
def chart91 : Chart := ⟨416,0,95,0,8,0x5705f⟩
def chart92 : Chart := ⟨448,0,63,0,8,0x15303f⟩
def chart93 : Chart := ⟨164,0,347,0,8,0xce0559⟩
def chart94 : Chart := ⟨352,0,159,0,8,0xb6009f⟩
def chart95 : Chart := ⟨0,1,460,50,8,0x5445b5⟩
def chart96 : Chart := ⟨5,0,506,0,8,0x8fbf48⟩
def chart97 : Chart := ⟨0,8,227,276,8,0x6936d⟩
def chart98 : Chart := ⟨134,0,377,0,8,0x358d38⟩
def chart99 : Chart := ⟨40,0,471,0,8,0xfd44d3⟩
def chart100 : Chart := ⟨70,0,441,0,8,0xc43b38⟩
def chart101 : Chart := ⟨10,0,501,0,8,0xfd4eb0⟩
def chart102 : Chart := ⟨257,0,254,0,8,0x8fb2ce⟩
def chart103 : Chart := ⟨480,0,31,0,7,0x17201f⟩
def chart104 : Chart := ⟨480,0,31,0,7,0xa4501f⟩
def chart105 : Chart := ⟨198,0,313,0,7,0x651938⟩
def chart106 : Chart := ⟨193,0,318,0,7,0xa1390e⟩
def chart107 : Chart := ⟨256,8,227,20,7,0x6926d⟩
def chart108 : Chart := ⟨198,0,313,0,7,0x358938⟩
def chart109 : Chart := ⟨56,0,455,0,7,0xd444c3⟩
def chart110 : Chart := ⟨321,0,190,0,7,0x83328e⟩
def chart111 : Chart := ⟨273,0,238,0,7,0x792c6⟩
def chart112 : Chart := ⟨268,0,243,0,7,0x8d2271⟩
def chart113 : Chart := ⟨35,0,476,0,7,0xad058c⟩
def chart114 : Chart := ⟨74,0,437,0,7,0xf10ab0⟩
def chart115 : Chart := ⟨7,0,504,0,7,0x8d8f08⟩
def chart116 : Chart := ⟨296,0,215,0,7,0x8d40d3⟩
def chart117 : Chart := ⟨14,0,497,0,7,0xcd0e30⟩
def chart118 : Chart := ⟨289,0,222,0,7,0x8f00ce⟩
def chart119 : Chart := ⟨198,0,313,0,7,0x94a938⟩
def chart120 : Chart := ⟨64,1,396,50,7,0x5401b5⟩
def chart121 : Chart := ⟨32,1,460,18,7,0x544595⟩
def chart122 : Chart := ⟨16,1,460,34,7,0x5445a5⟩
def chart123 : Chart := ⟨2,1,460,48,7,0x5445b4⟩
def chart124 : Chart := ⟨133,0,378,0,7,0x81bd48⟩
def chart125 : Chart := ⟨21,0,490,0,7,0x869f40⟩
def chart126 : Chart := ⟨4,8,227,272,7,0x69369⟩
def chart127 : Chart := ⟨128,1,332,50,7,0x144535⟩
def chart128 : Chart := ⟨64,8,163,276,7,0x6132d⟩
def chart129 : Chart := ⟨128,8,99,276,7,0x4916d⟩
def chart130 : Chart := ⟨130,1,332,48,6,0x144534⟩
def chart131 : Chart := ⟨48,1,460,2,6,0x544585⟩
def chart132 : Chart := ⟨144,1,332,34,6,0x144525⟩
def chart133 : Chart := ⟨160,1,332,18,6,0x144515⟩
def chart134 : Chart := ⟨96,1,396,18,6,0x540195⟩
def chart135 : Chart := ⟨66,1,396,48,6,0x5401b4⟩
def chart136 : Chart := ⟨132,8,99,272,6,0x49169⟩
def chart137 : Chart := ⟨68,8,163,272,6,0x61329⟩
def chart138 : Chart := ⟨20,8,227,256,6,0x69361⟩
def chart139 : Chart := ⟨260,8,227,16,6,0x69269⟩
def chart140 : Chart := ⟨272,8,227,4,6,0x69265⟩
def chart141 : Chart := ⟨320,8,163,20,6,0x6122d⟩
def chart142 : Chart := ⟨18,1,460,32,6,0x5445a4⟩
def chart143 : Chart := ⟨34,1,460,16,6,0x544594⟩
def chart144 : Chart := ⟨384,8,99,20,6,0x4906d⟩
def chart145 : Chart := ⟨80,1,396,34,6,0x5401a5⟩
def chart146 : Chart := ⟨27,0,484,0,5,0x550e80⟩
def chart147 : Chart := ⟨29,0,482,0,5,0x892e40⟩
def chart148 : Chart := ⟨176,1,332,2,5,0x144505⟩
def chart149 : Chart := ⟨84,8,163,256,5,0x61321⟩
def chart150 : Chart := ⟨148,8,99,256,5,0x49161⟩
def chart151 : Chart := ⟨89,0,422,0,5,0xa11a82⟩
def chart152 : Chart := ⟨276,8,227,0,5,0x69261⟩
def chart153 : Chart := ⟨324,8,163,16,5,0x61229⟩
def chart154 : Chart := ⟨388,8,99,16,5,0x49069⟩
def chart155 : Chart := ⟨27,0,484,0,5,0x650e80⟩
def chart156 : Chart := ⟨50,1,460,0,5,0x544584⟩
def chart157 : Chart := ⟨162,1,332,16,5,0x144514⟩
def chart158 : Chart := ⟨146,1,332,32,5,0x144524⟩
def chart159 : Chart := ⟨112,1,396,2,5,0x540185⟩
def chart160 : Chart := ⟨98,1,396,16,5,0x540194⟩
def chart161 : Chart := ⟨82,1,396,32,5,0x5401a4⟩
def chart162 : Chart := ⟨345,0,166,0,4,0x31282⟩
def chart163 : Chart := ⟨345,0,166,0,4,0x811282⟩
def chart164 : Chart := ⟨141,16,354,0,4,0x812c40⟩
def chart165 : Chart := ⟨345,0,166,0,4,0x32282⟩
def chart166 : Chart := ⟨169,16,326,0,4,0xa10442⟩
def chart167 : Chart := ⟨345,0,166,0,4,0x812282⟩
def chart168 : Chart := ⟨297,16,198,0,4,0x8900c2⟩
def chart169 : Chart := ⟨15,16,480,0,4,0x890e00⟩
def chart170 : Chart := ⟨404,8,99,0,4,0x49061⟩
def chart171 : Chart := ⟨313,0,198,0,4,0x640c2⟩
def chart172 : Chart := ⟨313,0,198,0,4,0x8440c2⟩
def chart173 : Chart := ⟨313,0,198,0,4,0x700c2⟩
def chart174 : Chart := ⟨340,8,163,0,4,0x61221⟩
def chart175 : Chart := ⟨114,1,396,0,4,0x540184⟩
def chart176 : Chart := ⟨178,1,332,0,4,0x144504⟩
def chart177 : Chart := ⟨31,0,480,0,4,0x848e00⟩
def chart178 : Chart := ⟨31,0,480,0,4,0x490e00⟩
def chart179 : Chart := ⟨31,0,480,0,4,0x450e00⟩
def chart180 : Chart := ⟨157,0,354,0,4,0x80ac40⟩
def chart181 : Chart := ⟨157,0,354,0,4,0x809c40⟩
def chart182 : Chart := ⟨31,0,480,0,4,0x448e00⟩
def chart183 : Chart := ⟨185,0,326,0,4,0x904442⟩
def chart184 : Chart := ⟨1,32,94,384,7,0x1ba4e⟩
def chart185 : Chart := ⟨400,0,111,0,7,0x5d067⟩
def chart186 : Chart := ⟨8,256,151,96,7,0xf00c93⟩
def chart187 : Chart := ⟨98,0,413,0,7,0xf4019c⟩
def chart188 : Chart := ⟨8,4,369,130,7,0x314cb2⟩
def chart189 : Chart := ⟨162,0,349,0,7,0x35451c⟩
def chart190 : Chart := ⟨1,2,440,68,7,0x823b4a⟩
def chart191 : Chart := ⟨97,0,414,0,6,0xa2018e⟩
def chart192 : Chart := ⟨24,256,135,96,6,0xd00c83⟩
def chart193 : Chart := ⟨136,4,369,2,6,0x314c32⟩
def chart194 : Chart := ⟨40,256,151,64,6,0xf00493⟩
def chart195 : Chart := ⟨392,0,119,0,6,0x16073⟩
def chart196 : Chart := ⟨72,4,305,130,6,0x3108b2⟩
def chart197 : Chart := ⟨24,4,353,130,6,0x114ca2⟩
def chart198 : Chart := ⟨10,4,369,128,6,0x314cb0⟩
def chart199 : Chart := ⟨129,2,312,68,6,0x80394a⟩
def chart200 : Chart := ⟨17,2,424,68,6,0x821b42⟩
def chart201 : Chart := ⟨5,2,440,64,6,0x823b48⟩
def chart202 : Chart := ⟨65,32,30,384,6,0x13a0e⟩
def chart203 : Chart := ⟨24,64,165,258,6,0x546e0⟩
def chart204 : Chart := ⟨17,32,78,384,6,0x19a46⟩
def chart205 : Chart := ⟨257,32,94,128,6,0x1b24e⟩
def chart206 : Chart := ⟨273,32,78,128,5,0x19246⟩
def chart207 : Chart := ⟨147,0,364,0,5,0x118d04⟩
def chart208 : Chart := ⟨26,64,165,256,5,0x546a0⟩
def chart209 : Chart := ⟨200,4,305,2,5,0x310832⟩
def chart210 : Chart := ⟨113,0,398,0,5,0x920186⟩
def chart211 : Chart := ⟨71,0,440,0,5,0x823b08⟩
def chart212 : Chart := ⟨193,32,30,256,5,0x1380e⟩
def chart213 : Chart := ⟨21,2,424,64,5,0x821b40⟩
def chart214 : Chart := ⟨133,2,312,64,5,0x803948⟩
def chart215 : Chart := ⟨26,4,353,128,5,0x114ca0⟩
def chart216 : Chart := ⟨74,4,305,128,5,0x3108b0⟩
def chart217 : Chart := ⟨280,64,165,2,5,0x542e0⟩
def chart218 : Chart := ⟨152,4,353,2,5,0x114c22⟩
def chart219 : Chart := ⟨273,64,172,2,5,0x582c4⟩
def chart220 : Chart := ⟨200,256,23,32,5,0xb00813⟩
def chart221 : Chart := ⟨408,0,103,0,5,0x15063⟩
def chart222 : Chart := ⟨282,64,165,0,4,0x542a0⟩
def chart223 : Chart := ⟨339,0,172,0,4,0x38284⟩
def chart224 : Chart := ⟨202,4,305,0,4,0x310830⟩
def chart225 : Chart := ⟨115,0,396,0,4,0x520184⟩
def chart226 : Chart := ⟨181,0,330,0,4,0x828540⟩
def chart227 : Chart := ⟨339,0,172,0,4,0x31284⟩
def chart228 : Chart := ⟨179,0,332,0,4,0x20c504⟩
def chart229 : Chart := ⟨179,0,332,0,4,0x10c504⟩
def chart230 : Chart := ⟨181,0,330,0,4,0x860540⟩
def chart231 : Chart := ⟨87,0,424,0,4,0x441b00⟩
def chart232 : Chart := ⟨87,0,424,0,4,0x821b00⟩
def chart233 : Chart := ⟨87,0,424,0,4,0x421b00⟩
def chart234 : Chart := ⟨376,0,135,0,4,0x424083⟩
def chart235 : Chart := ⟨488,0,23,0,4,0xb00013⟩
def chart236 : Chart := ⟨433,0,78,0,4,0x2c046⟩
def chart237 : Chart := ⟨412,0,99,0,4,0xd061⟩
def chart238 : Chart := ⟨433,0,78,0,4,0xd046⟩
def chart239 : Chart := ⟨158,0,353,0,4,0x448c20⟩
def chart240 : Chart := ⟨348,0,163,0,4,0x421221⟩
def chart241 : Chart := ⟨346,0,165,0,4,0x5102a0⟩
def chart242 : Chart := ⟨158,0,353,0,4,0x10cc20⟩
def chartTable : List Chart := [chart0,chart1,chart2,chart3,chart4,chart5,chart6,chart7,chart8,chart9,chart10,chart11,chart12,chart13,chart14,chart15,chart16,chart17,chart18,chart19,chart20,chart21,chart22,chart23,chart24,chart25,chart26,chart27,chart28,chart29,chart30,chart31,chart32,chart33,chart34,chart35,chart36,chart37,chart38,chart39,chart40,chart41,chart42,chart43,chart44,chart45,chart46,chart47,chart48,chart49,chart50,chart51,chart52,chart53,chart54,chart55,chart56,chart57,chart58,chart59,chart60,chart61,chart62,chart63,chart64,chart65,chart66,chart67,chart68,chart69,chart70,chart71,chart72,chart73,chart74,chart75,chart76,chart77,chart78,chart79,chart80,chart81,chart82,chart83,chart84,chart85,chart86,chart87,chart88,chart89,chart90,chart91,chart92,chart93,chart94,chart95,chart96,chart97,chart98,chart99,chart100,chart101,chart102,chart103,chart104,chart105,chart106,chart107,chart108,chart109,chart110,chart111,chart112,chart113,chart114,chart115,chart116,chart117,chart118,chart119,chart120,chart121,chart122,chart123,chart124,chart125,chart126,chart127,chart128,chart129,chart130,chart131,chart132,chart133,chart134,chart135,chart136,chart137,chart138,chart139,chart140,chart141,chart142,chart143,chart144,chart145,chart146,chart147,chart148,chart149,chart150,chart151,chart152,chart153,chart154,chart155,chart156,chart157,chart158,chart159,chart160,chart161,chart162,chart163,chart164,chart165,chart166,chart167,chart168,chart169,chart170,chart171,chart172,chart173,chart174,chart175,chart176,chart177,chart178,chart179,chart180,chart181,chart182,chart183,chart184,chart185,chart186,chart187,chart188,chart189,chart190,chart191,chart192,chart193,chart194,chart195,chart196,chart197,chart198,chart199,chart200,chart201,chart202,chart203,chart204,chart205,chart206,chart207,chart208,chart209,chart210,chart211,chart212,chart213,chart214,chart215,chart216,chart217,chart218,chart219,chart220,chart221,chart222,chart223,chart224,chart225,chart226,chart227,chart228,chart229,chart230,chart231,chart232,chart233,chart234,chart235,chart236,chart237,chart238,chart239,chart240,chart241,chart242]
def chart (i : Nat) : Chart := chartTable.getD i chart0
def chartValidated (c : Chart) := checkChart c && checkLB c zeroPrior
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chart_verified (i : Nat) : chartValidated (chart i) = true := by
  have checked : chartTable.all chartValidated = true := by decide +kernel
  have default_ok : chartValidated chart0 = true := by decide +kernel
  simp only [chart, List.getD_eq_getElem?_getD]
  cases e : chartTable[i]? with
  | none => exact default_ok
  | some c => exact List.all_eq_true.mp checked c (List.mem_of_getElem? e)
theorem chart_valid (i : Nat) : Valid (chart i) :=
  checkChart_sound ((Bool.and_eq_true _ _).mp (chart_verified i)).1
theorem chart_low (i p bs) (h : Reach (chart i).roots p bs) (v : Available bs (chart i).G) :
    (chart i).L ≤ p :=
  checkLB_sound zeroPrior_sound ((Bool.and_eq_true _ _).mp (chart_verified i)).2 p bs h v
end Zero3229
end B
namespace Pnp3229Certificate
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 24
def zero : Sig := 0
def one : Sig := BitVec.allOnes 24
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
inductive Live (target : Sig) : Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 {target}
  | binary {k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k (insert (bin d a b) U)) :
      Live target (k+1) (insert a (insert b U))
private lemma live_proper {k S} (h : Live target k S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {k S} (h : Live target k S) : S.card ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @binary k U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩
private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
private lemma pull_gate {w : List Sig} {z : Sig} {k S} (h : Live target k S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩
def bit (i : Fin 24) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
abbrev Row := Fin 24
theorem mono_row_difference {T k S} (h : Live T k S) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live T k S
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d ha hb hab hf tail =>
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
    exact twoStep a am b bm d ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
abbrev Bank := List Sig
def both (p : Bool → Bool) := p false && p true
theorem both_spec {p : Bool → Bool} (h : both p = true) (b : Bool) : p b = true := by
  simp only [both,Bool.and_eq_true] at h
  cases b <;> first | exact h.1 | exact h.2
def pairs (p : Sig → Sig → Bool) : Bank → Bool
  | [] => true
  | a :: xs => xs.all (p a) && pairs p xs
theorem pairs_spec {p : Sig → Sig → Bool} {xs : Bank} (h : pairs p xs = true)
    {a b : Sig} (ha : a ∈ xs) (hb : b ∈ xs) (ne : a ≠ b) : p a b = true ∨ p b a = true := by
  induction xs with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [pairs,Bool.and_eq_true,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · exact Or.inl (h.1 _ ((List.mem_cons.mp hb).resolve_left ne.symm))
    rcases List.mem_cons.mp hb with rfl | hbTail
    · exact Or.inr (h.1 _ haTail)
    exact ih h.2 haTail hbTail
def testPair (cap : Nat) (ws : Bank) (close : Bank → Bool) (a b : Sig) : Bool :=
  both fun d =>
    let z := bin d a b
    ws.contains z || z == zero || z == one || both fun ka => both fun kb =>
      let kid := childTwo ws a b d ka kb
      decide (cap < kid.length) || close kid
def testNode (T : Sig) (cap : Nat) (ws : Bank) (close : Bank → Bool) : Bool :=
  !ws.contains T && decide ws.Nodup && (cap == 0 || pairs (testPair cap ws close) ws)
theorem pair_sound {cap ws close a b} (ht : testPair cap ws close a b = true)
    {d ka kb} (hf : bin d a b ∉ ws) (hp : proper (bin d a b))
    (hl : (childTwo ws a b d ka kb).length ≤ cap) : close (childTwo ws a b d ka kb) = true := by
  have H := both_spec ht d
  simp only [List.contains_eq_mem,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at H
  rcases H with ((h|h)|h)|h
  · contradiction
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)
  have K := both_spec (both_spec h ka) kb
  simpa [Nat.not_lt_of_ge hl] using K
theorem node_sound {T cap ws close} (h : testNode T cap ws close = true)
    (hc : ∀ w, close w = true → Impossible T (cap-1) w.toFinset) :
    Impossible T cap ws.toFinset := by
  simp only [testNode,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
    decide_eq_false_iff_not,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at h
  obtain ⟨⟨hm, nd⟩, z|ht⟩ := h
  · subst cap
    intro k hk hl
    have hz : k=0 := by omega
    subst k
    generalize he : ws.toFinset = S at hl
    cases hl
    exact hm (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  · apply enum_step nd hm
    intro a ha b hb d ka kb ne fresh pro len
    rcases pairs_spec ht ha hb ne with g | g
    · exact hc _ (pair_sound g fresh pro len)
    · have len' : (childTwo ws b a d kb ka).length ≤ cap := by
        have e : (childTwo ws a b d ka kb).length = (childTwo ws b a d kb ka).length := by
          simp only [childTwo,List.length_cons,kept]
          have kla : a ∈ ws.erase b := nd.mem_erase_iff.mpr ⟨ne,ha⟩
          have klb : b ∈ ws.erase a := nd.mem_erase_iff.mpr ⟨ne.symm,hb⟩
          cases ka <;> cases kb <;> simp [List.length_erase_of_mem,ha,hb,kla,klb]
        omega
      rw [childTwo_swap _ nd]
      exact hc _ (pair_sound g (bin_comm d b a ▸ fresh) (bin_comm d b a ▸ pro) len')
structure Auto (T : Sig) (act : Sig → Sig) : Prop where
  inject : Function.Injective act
  zero_eq : act zero = zero
  one_eq : act one = one
  goal_eq : act T = T
  comm (d a b) : act (bin d a b) = bin d (act a) (act b)
theorem transport {T k S f} (ok : Auto T f) (h : Live T k S) :
    Live T k (S.image f) := by
  have pr (a) (p : proper a) : proper (f a) :=
    ⟨fun h => p.1 (ok.inject (h.trans ok.zero_eq.symm)),
     fun h => p.2 (ok.inject (h.trans ok.one_eq.symm))⟩
  induction h with
  | stop hp => simpa [ok.goal_eq] using Live.stop (pr _ hp)
  | @binary k U a b d ha hb hab hf _ ih =>
    have fresh : f (bin d a b) ∉ (insert a (insert b U)).image f := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (ok.inject eq ▸ hv)
    simp only [Finset.image_insert,ok.comm] at fresh ih ⊢
    exact Live.binary (pr _ ha) (pr _ hb) (fun hh => hab (ok.inject hh)) fresh ih
structure Frontiers where
  count : Nat → Nat
  state : Nat → Nat → Bank
  locate : Nat → Bank → Nat × Nat
  act : Nat → Sig → Sig
def checkLink (F : Frontiers) (s : Nat) (ws : Bank) :=
  let (j,g) := F.locate s ws
  decide (j < F.count s) && sameWords (ws.map (F.act g)) (F.state s j)
def checkAt (F : Frontiers) (prune : Nat → Bank → Bool) (T : Sig) (s i : Nat) :=
  let ws := F.state s i
  prune s ws || testNode T s ws (fun kid => prune (s-1) kid || checkLink F (s-1) kid)
theorem certificate_sound {F prune T cap}
    (actions : ∀ g, Auto T (F.act g))
    (cuts : ∀ k w, prune k w = true → Impossible T k w.toFinset)
    (checked : ∀ s ≤ cap, ∀ i < F.count s, checkAt F prune T s i = true) :
    ∀ s ≤ cap, ∀ i < F.count s, Impossible T s (F.state s i).toFinset := by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi
    have h := checked s hs i hi
    rw [checkAt,Bool.or_eq_true] at h
    obtain h | h := h
    · exact cuts _ _ h
    by_cases he : s=0
    · subst s
      simp only [testNode,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
        decide_eq_false_iff_not,Nat.reduceBEq,Bool.true_or,and_true,decide_eq_true_eq] at h
      intro k hk hl
      have hz : k=0 := by omega
      subst k
      generalize eq : (F.state 0 i).toFinset = S at hl
      cases hl
      exact h.1 (List.mem_toFinset.mp (eq.symm ▸ Finset.mem_singleton_self _))
    apply node_sound h
    intro w hw
    simp only [Bool.or_eq_true] at hw
    obtain hcut | hlink := hw
    · exact cuts _ _ hcut
    simp only [checkLink,Bool.and_eq_true,decide_eq_true_eq] at hlink
    obtain ⟨jBound, eq⟩ := hlink
    let g := (F.locate (s-1) w).2
    have no := ih (s-1) (by omega) (by omega) _ jBound
    intro k hk run
    apply no k hk
    rw [←sameWords_sound eq]
    have mapset : (w.map (F.act g)).toFinset = w.toFinset.image (F.act g) := by
      ext a
      simp
    rw [mapset]
    exact transport (actions g) run
def pos : List Nat := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
def negs : List Nat := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
def roots9 : Bank := [0x544031,0x823043,0x314086,0x6910c,0xa92018,0x1ba20,0xdc440,0xce0280,0xf00d00]
def aux : Sig := 0x56d13d
def roots : Bank := roots9 ++ [aux]
def goal : Sig := 4095
def maskAt (r : Row) : Nat := (pos++negs).getD r.val 0
def inputAt (m : Nat) : List Bool :=
  (List.ofFn fun i : Fin 9 => m.testBit i.val) ++ [m.testBit 0 || m.testBit 3]
theorem sample_ok : ∀ r : Row, roots.map (bit r) = inputAt (maskAt r) := by decide +kernel
theorem goal_case : ∀ r : Row,
    ((bit r goal = true ∧ maskAt r ∈ pos) ∨ (bit r goal = false ∧ maskAt r ∈ negs)) := by decide +kernel
theorem goal_proper : proper goal := by unfold proper; decide +kernel
def essentialWitness : Sig → Row × Row
  | 0x544031 => (0,12)
  | 0x823043 => (0,14)
  | 0x314086 => (1,12)
  | 0x6910c => (2,14)
  | 0xa92018 => (3,12)
  | 0x01ba20 => (5,14)
  | 0x0dc440 => (6,12)
  | 0xce0280 => (7,14)
  | _ => (8,12)
def essentialCheck (a : Sig) :=
  let (p,n) := essentialWitness a
  bit p goal && !bit n goal &&
    roots.all (fun b => !bit p b || bit n b || b == a)
theorem roots_forced : ∀ a ∈ roots9, ∃ p n : Row,
    bit p goal = true ∧ bit n goal = false ∧
    ∀ b ∈ roots, bit p b = true → bit n b = false → b = a := by
  have chk : roots9.all essentialCheck = true := by decide +kernel
  intro a ha
  let p := (essentialWitness a).1
  let n := (essentialWitness a).2
  have chk := List.all_eq_true.mp chk a ha
  simp only [essentialCheck,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at chk
  refine ⟨p,n,chk.1.1,chk.1.2,?_⟩
  intro b hb hp hn
  have eq := chk.2 b hb
  change bit (essentialWitness a).1 b = true at hp
  change bit (essentialWitness a).2 b = false at hn
  simpa [hp,hn] using eq
theorem exactly_roots {k S} (h : Live goal k S) (hs : ∀ a ∈ S, a ∈ roots) :
    S = roots.toFinset ∨ S = roots9.toFinset := by
  have raw : ∀ a ∈ roots9, a ∈ S := by
    intro a ha
    obtain ⟨p,n,hp,hn,hh⟩ := roots_forced a ha
    obtain ⟨v,hv,yes,no⟩ := mono_row_difference h hp hn
    exact (hh v (hs v hv) yes no) ▸ hv
  by_cases mem : aux ∈ S
  · left
    ext v
    simp only [List.mem_toFinset]
    refine ⟨hs v,?_⟩
    intro h
    rcases List.mem_append.mp h with hv | hv
    · exact raw v hv
    · simp only [List.mem_singleton] at hv
      exact hv ▸ mem
  · right
    ext v
    simp only [List.mem_toFinset]
    refine ⟨?_,raw v⟩
    intro hv
    rcases List.mem_append.mp (hs v hv) with h | h
    · exact h
    · simp only [List.mem_singleton] at h
      exact False.elim (mem (h ▸ hv))
theorem reduce_exact (c : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 c)
    (yes : ∀ p ∈ pos, c.eval (inputAt p) = true)
    (no : ∀ n ∈ negs, c.eval (inputAt n) = false) :
    ∃ k ≤ c.gates.length, Live goal k roots.toFinset ∨ Live goal k roots9.toFinset := by
  let w := (execute c.gates roots).getD c.output zero
  have heq : w = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r w = bit r goal
    have e : bit r w = c.eval (inputAt (maskAt r)) := by
      change bit r ((execute c.gates roots).getD c.output zero) =
        (c.wires (inputAt (maskAt r))).getD c.output false
      rw [←b_read,execute_bits _ _ _ (fun g hg => (mono g hg).1)]
      rw [←sample_ok r]
      rfl
    rw [e]
    rcases goal_case r with ⟨hp,hm⟩ | ⟨hn,hm⟩
    · rw [hp,yes _ hm]
    · rw [hn,no _ hm]
  have hw := get_rep (execute c.gates roots) c.output
  change represented _ w at hw
  rw [heq] at hw
  obtain ⟨k,S,hk,run,sub⟩ := extract c.gates roots mono goal_proper
    (hw.resolve_right (fun h => h goal_proper))
  refine ⟨k,hk,?_⟩
  obtain eq|eq := exactly_roots run sub
  · exact Or.inl (eq ▸ run)
  · exact Or.inr (eq ▸ run)
def shifted (d r : Row) : Row :=
  if h : r.val < 24-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(24-d.val),by omega⟩
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 24-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
abbrev Plan := List (Sig × Row)
def actWord (p : Plan) (a : Sig) : Sig :=
  match p with
  | [] => a
  | (m,d)::t => mux m (a.rotateRight d.val) (actWord t a)
def actRow (p : Plan) (r : Row) : Row :=
  match p with
  | [] => r
  | (m,d)::t => if bit r m then shifted d r else actRow t r
theorem action_bit (p : Plan) (a : Sig) (r : Row) :
    bit r (actWord p a) = bit (actRow p r) a := by
  induction p with
  | nil => rfl
  | cons hd p ih =>
    rcases hd with ⟨m,d⟩
    rw [actWord,bit_mux,bit_shift,ih,actRow]
    split <;> rfl
theorem auto_of (p : Plan) (T : Sig) (onto : Function.Surjective (actRow p))
    (fixed : actWord p T = T) : Auto T (actWord p) := by
  constructor
  · intro x y eq
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
    have h := congrArg (bit r) eq
    rw [action_bit,action_bit,hr] at h
    exact h
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    exact (action_bit p zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    exact (action_bit p one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
  · exact fixed
  · intro d x y
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [action_bit,bit_bin,bit_bin,action_bit,action_bit]
def plan : Nat → Plan
  | 0 => []
  | 1 => [(0x8000,2),(0xc0,3),(0x1,5),(0x4,6),(0x10000,7),(0x4000,8),(0x2,10),(0x800,14),(0x400000,16),(0x800000,17),(0x100,18),(0x20,19),(0x600,21),(0x20000,22)]
  | 2 => [(0x2000,1),(0x90,2),(0x2,4),(0x60000,5),(0x8000,6),(0x8,7),(0x1000,8),(0x4,9),(0x800,15),(0x100000,16),(0x400,17),(0x200000,18),(0xc00000,19),(0x20,20),(0x240,22),(0x4000,23)]
  | 3 => [(0x200,1),(0x8,4),(0x11,5),(0x8020,6),(0x10000,7),(0x1000,8),(0x2000,9),(0x100000,16),(0x400400,17),(0x100,18),(0x800000,19),(0x200000,20),(0x20800,21),(0x40040,22),(0x4086,23)]
  | 4 => [(0x200001,1),(0x10000,2),(0x114,3),(0x2000,4),(0x8,6),(0x200,18),(0x20000,20),(0x8a0,21),(0x40000,22),(0x400002,23)]
  | 5 => [(0x1a000,2),(0x68,3),(0x2,4),(0x40000,5),(0x10,6),(0x4000,8),(0x1,11),(0x800,15),(0xa00100,17),(0x200,18),(0x20000,20),(0x480,21),(0x4,22),(0x400000,23)]
  | 6 => [(0x248,1),(0x1,2),(0x4020,3),(0x18000,7),(0x3000,8),(0x300000,16),(0xc00000,17),(0x20100,21),(0x4,22),(0x490,23)]
  | 7 => [(0x4008,1),(0x80,2),(0x4,3),(0x40,4),(0x20000,5),(0x3001,8),(0x2,10),(0x800,14),(0x300100,16),(0x400000,19),(0x400,20),(0x20,21),(0x200,22),(0x8010,23)]
  | 8 => [(0x2043,1),(0x10010,2),(0x4100,3),(0x20000,4),(0x40000,5),(0x4,6),(0x8008,7),(0x1000,8),(0x400000,15),(0x100000,16),(0x800000,17),(0x200800,18),(0x220,19),(0x80,20),(0x400,23)]
  | 9 => [(0x4000,1),(0x10000,2),(0x20048,4),(0x10,5),(0x2,7),(0x1000,8),(0x2000,9),(0x1,11),(0x800,13),(0x400000,15),(0x100000,16),(0x100,17),(0x200,19),(0x200480,20),(0x40000,22),(0x8000,23)]
  | 10 => [(0x2,1),(0x2000,2),(0x8,3),(0x40000,5),(0x30,6),(0x4000,7),(0x1,8),(0x100,16),(0x200000,17),(0xc00,18),(0x800000,19),(0x40,21),(0x8000,22),(0x4,23)]
  | 11 => [(0x200000,1),(0x1,2),(0x90,3),(0x2000,4),(0x8,6),(0x14002,7),(0x4,9),(0x800,13),(0x400000,16),(0x400,18),(0x800000,19),(0x20,20),(0x340,21),(0x68000,22)]
  | _ => []
def action (g : Nat) := actWord (plan (g % 12))
theorem actions_verified : ∀ g : Nat, Auto goal (action g) := by
  have onto : ∀ g : Fin 12, ∀ r : Row, ∃ s : Row, actRow (plan g.val) s = r := by decide +kernel
  have fixed : ∀ g : Fin 12, actWord (plan g.val) goal = goal := by decide +kernel
  intro g
  exact auto_of _ _ (onto ⟨g % 12,Nat.mod_lt _ (by decide)⟩)
    (fixed ⟨g % 12,Nat.mod_lt _ (by decide)⟩)
abbrev Bits := BitVec 144
def nibble (x : BitVec 4) : BitVec 48 :=
  match x.toNat with
  | 0 => 0x0
  | 1 => 0xfff
  | 2 => 0xfff000
  | 3 => 0xffffff
  | 4 => 0xfff000000
  | 5 => 0xfff000fff
  | 6 => 0xffffff000
  | 7 => 0xfffffffff
  | 8 => 0xfff000000000
  | 9 => 0xfff000000fff
  | 10 => 0xfff000fff000
  | 11 => 0xfff000ffffff
  | 12 => 0xffffff000000
  | 13 => 0xffffff000fff
  | 14 => 0xfffffffff000
  | _ => 0xffffffffffff
theorem nibble_spec : ∀ x : BitVec 4, ∀ j : Fin 48,
    (nibble x).getLsbD j.val = x.getLsbD (j.val / 12) := by decide +kernel
def widePos (w : Sig) : Bits :=
  (nibble (w.extractLsb' 8 4) ++ nibble (w.extractLsb' 4 4)) ++ nibble (w.extractLsb' 0 4)
def column (w : Sig) : Bits := widePos w &&& (~~~(w.extractLsb' 12 12)).replicate 12
theorem wide_spec (w : Sig) (i : Nat) (hi : i < 144) :
    (widePos w).getLsbD i = w.getLsbD (i/12) := by
  simp only [widePos,BitVec.getLsbD_append]
  by_cases h1 : i < 48
  · simp only [h1,ite_true]
    rw [nibble_spec _ ⟨i,h1⟩,BitVec.getLsbD_extractLsb']
    simp [show i / 12 < 4 by omega]
  · simp only [h1,ite_false]
    by_cases h2 : i-48 < 48
    · simp only [h2,ite_true]
      rw [nibble_spec _ ⟨i-48,h2⟩,BitVec.getLsbD_extractLsb']
      simp [show (i-48)/12 < 4 by omega,show 4+(i-48)/12 = i/12 by omega]
    · simp only [h2,ite_false]
      rw [nibble_spec _ ⟨i-48-48,by omega⟩,BitVec.getLsbD_extractLsb']
      simp [show (i-48-48)/12 < 4 by omega,show 8+(i-48-48)/12 = i/12 by omega]
def posR (i : Fin 144) : Row := ⟨i.val/12,by omega⟩
def negR (i : Fin 144) : Row := ⟨12+i.val % 12,by omega⟩
theorem col_spec (w : Sig) (i : Fin 144) :
    (column w).getLsbD i.val = (bit (posR i) w && !bit (negR i) w) := by
  simp only [column,BitVec.getLsbD_and,wide_spec _ _ i.isLt,BitVec.getLsbD_replicate,BitVec.getLsbD_not,BitVec.getLsbD_extractLsb',decide_true,Bool.true_and,
    posR,negR,bit,i.isLt,show i.val < 12*12 by omega,show i.val % 12<12 by omega]
abbrev Cov := Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (v : Bank) : Cov := v.foldr (fun a c => addCov (column a) c) (0,0,0)
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
private theorem cov_perm {l r : Bank} (h : l.Perm r) : coverage l=coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem coverage_bit (ws : Bank) (i : Fin 144) :
    (coverage ws).1.getLsbD i.val = true ↔ ∃ a ∈ ws, bit (posR i) a = true ∧ bit (negR i) a = false := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change ((column a) ||| (coverage ws).1).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or,Bool.or_eq_true,col_spec,ih]
    simp [Bool.and_eq_true,List.mem_cons]
theorem goalRows : ∀ i : Fin 144,
    bit (posR i) goal = true ∧ bit (negR i) goal = false := by decide +kernel
theorem must_cover {k ws} (h : Live goal k (List.toFinset ws)) :
    (coverage ws).1 = BitVec.allOnes 144 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 144 := ⟨j,hj⟩
  rw [BitVec.getLsbD_allOnes,show decide (j<144)=true by simp [hj]]
  apply (coverage_bit ws i).mpr
  obtain ⟨v,hv,yes,no⟩ := mono_row_difference h (goalRows i).1 (goalRows i).2
  exact ⟨v,List.mem_toFinset.mp hv,yes,no⟩
def remCov (c : Cov) (ca cb : Bits) (ka kb : Bool) : Bits :=
  if ka then (if kb then c.1 else takeOne c cb) else if kb then takeOne c ca else takeTwo c ca cb
theorem get_child_cover (ws : Bank) {a b : Sig} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b)
    (d ka kb : Bool) :
    (coverage (childTwo ws a b d ka kb)).1 =
      column (bin d a b) ||| remCov (coverage ws) (column a) (column b) ka kb := by
  have hbb : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  have perm : ws.Perm (a :: b :: (ws.erase a).erase b) :=
    (List.perm_cons_erase ha).trans (List.Perm.cons a (List.perm_cons_erase hbb))
  have eq := cov_perm perm
  rw [eq]
  let rest := (ws.erase a).erase b
  change
    column (bin d a b) ||| (coverage (kept ka a (kept kb b rest))).1 =
      column (bin d a b) ||| remCov (addCov (column a) (addCov (column b) (coverage rest))) _ _ ka kb
  congr 1
  cases ka <;> cases kb
  · exact (cov_two _ _ _).symm
  · exact (cov_one _ _).symm
  · rw [add_swap]
    exact (cov_one _ _).symm
  · rfl
def goodNeg (a : Sig) : Bits := (~~~(a.extractLsb' 12 12)).replicate 12
def allows (sole : Bits) (a b : Sig) (d : Bool) : Bool :=
  let need := sole &&& column a
  let can := if d then goodNeg b else widePos b
  (need &&& ~~~can) == 0
theorem goodNeg_bit (a : Sig) (i : Fin 144) :
    (goodNeg a).getLsbD i.val = !bit (negR i) a := by
  simp only [goodNeg,BitVec.getLsbD_replicate,BitVec.getLsbD_not,BitVec.getLsbD_extractLsb',
    decide_true,Bool.true_and,negR,bit,show i.val < 12*12 by omega,show i.val % 12<12 by omega]
theorem drop_required {ws : Bank} {a b : Sig} (aa : a ∈ ws) (bb : b ∈ ws) (ne : a ≠ b)
    {d kb : Bool} {k : Nat} (run : Live goal k (childTwo ws a b d false kb).toFinset) :
    allows (coverage ws).2.1 a b d = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 144 := ⟨j,hj⟩
  have full := congrArg (fun x : Bits => x.getLsbD i.val) (must_cover run)
  rw [get_child_cover ws aa bb ne,BitVec.getLsbD_or,BitVec.getLsbD_allOnes] at full
  simp only [i.isLt,decide_true] at full
  change ((coverage ws).2.1 &&& column a &&&
      ~~~(if d then goodNeg b else widePos b)).getLsbD i.val = (0 : Bits).getLsbD i.val
  have zz : (0 : Bits).getLsbD i.val = false := by simp
  rw [zz]
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
  by_cases hs : (coverage ws).2.1.getLsbD i.val = true
  · rw [hs,Bool.true_and]
    by_cases ha : (column a).getLsbD i.val = true
    · rw [ha,Bool.true_and]
      have hh : (remCov (coverage ws) (column a) (column b) false kb).getLsbD i.val = false := by
        cases kb <;>
          simp only [remCov,takeOne,takeTwo,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
            i.isLt,hs,ha,Bool.false_eq_true,ite_false,ite_true,decide_true,Bool.true_and,Bool.true_or,Bool.not_true,Bool.and_false]
      rw [hh,Bool.or_false,col_spec,bit_bin,bit_bin] at full
      cases d
      · change (!(widePos b).getLsbD i.val) = false
        rw [wide_spec b i.val i.isLt]
        change (!bit (posR i) b) = false
        cases hb : bit (posR i) b <;> simp_all
      · change (!(goodNeg b).getLsbD i.val) = false
        rw [goodNeg_bit]
        cases hb : bit (negR i) b <;> simp_all
    · rw [Bool.eq_false_iff.mpr ha]
      rfl
  · rw [Bool.eq_false_iff.mpr hs]
    rfl
abbrev Hook := Sig → Sig → Bool → Bool → Bool → Bool
def HookSound (cap : Nat) (ws : Bank) (close : Hook) : Prop :=
  ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
    (childTwo ws a b d ka kb).Nodup →
    close a b d ka kb = true → Impossible goal (cap-1) (childTwo ws a b d ka kb).toFinset
def pairExclusive (cap n : Nat) (ws : Bank) (sole : Bits) (close : Hook) (a b : Sig) : Bool :=
  both fun d =>
    let z := bin d a b
    ws.contains z || z == zero || z == one ||
      (let da := allows sole a b d
       let db := allows sole b a d
       both fun ka => both fun kb =>
          decide (cap+1 < n+ka.toNat+kb.toNat) || (!ka && !da) || (!kb && !db) ||
            close a b d ka kb)
def nodeFast (cap : Nat) (ws : Bank) (close : Hook) :=
  !ws.contains goal && decide ws.Nodup &&
    (cap == 0 || pairs (pairExclusive cap ws.length ws (coverage ws).2.1 close) ws)
theorem child_nodup {ws : Bank} {a b : Sig} (nd : ws.Nodup)
    (aa : a ∈ ws) (bb : b ∈ ws) (ne : a ≠ b) {d : Bool} (fresh : bin d a b ∉ ws)
    (ka kb : Bool) : (childTwo ws a b d ka kb).Nodup := by
  let rest := (ws.erase a).erase b
  have rn : rest.Nodup := (nd.erase _).erase _
  have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
  have br : b ∉ rest := (nd.erase a).not_mem_erase
  have kbnd := kept_nd kb b rest rn br
  have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,ne]
  refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ kbnd ax⟩
  intro h
  apply fresh
  rw [keep_mem,keep_mem] at h
  rcases h with ⟨e,_⟩ | ⟨e,_⟩ | hr
  · rw [e]; exact aa
  · rw [e]; exact bb
  · exact List.mem_of_mem_erase (List.mem_of_mem_erase hr)
theorem pairFast_sound {cap ws close a b} (ht : pairExclusive cap ws.length ws (coverage ws).2.1 close a b = true)
    (nd : ws.Nodup) (aa : a ∈ ws) (bb : b ∈ ws) (ne : a ≠ b) {d ka kb} (hf : bin d a b ∉ ws)
    (hp : proper (bin d a b)) (hl : (childTwo ws a b d ka kb).length ≤ cap)
    (hc : HookSound cap ws close) :
    Impossible goal (cap-1) (childTwo ws a b d ka kb).toFinset := by
  simp only [pairExclusive] at ht
  have H := both_spec ht d
  simp only [List.contains_eq_mem,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at H
  rcases H with ((h|h)|h)|h
  · contradiction
  · exact False.elim (hp.1 h)
  · exact False.elim (hp.2 h)
  have K := both_spec (both_spec h ka) kb
  simp only [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at K
  rcases K with ((h|⟨hka,hd⟩)|⟨hkb,hd⟩)|h
  · have bb' : b ∈ ws.erase a := nd.mem_erase_iff.mpr ⟨ne.symm,bb⟩
    have indexL : 2 ≤ ws.length := by
      have := List.length_pos_of_mem bb'
      rw [List.length_erase_of_mem aa] at this
      omega
    cases ka <;> cases kb <;> simp [childTwo,kept,List.length_erase_of_mem,aa,bb',Bool.toNat] at hl h <;> omega
  · subst ka; intro k hk run
    rw [drop_required aa bb ne run] at hd
    contradiction
  · subst kb; intro k hk run
    rw [childTwo_swap _ nd] at run
    rw [drop_required bb aa ne.symm run] at hd
    contradiction
  · exact hc a aa b bb d ka kb ne hf (child_nodup nd aa bb ne hf ka kb) h
theorem nodeFast_sound {cap ws close} (h : nodeFast cap ws close = true)
    (hc : HookSound cap ws close) :
    Impossible goal cap ws.toFinset := by
  simp only [nodeFast,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
    decide_eq_false_iff_not,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at h
  obtain ⟨⟨hm, nd⟩, z|ht⟩ := h
  · subst cap
    intro k hk hl
    have hz : k=0 := by omega
    subst k
    generalize he : ws.toFinset = S at hl
    cases hl
    exact hm (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  · apply enum_step nd hm
    intro a ha b hb d ka kb ne fresh pro len
    rcases pairs_spec ht ha hb ne with g | g
    · exact pairFast_sound g nd ha hb ne fresh pro len hc
    · have len' : (childTwo ws b a d kb ka).length ≤ cap := by
        have e : (childTwo ws a b d ka kb).length = (childTwo ws b a d kb ka).length := by
          simp only [childTwo,List.length_cons,kept]
          have kla : a ∈ ws.erase b := nd.mem_erase_iff.mpr ⟨ne,ha⟩
          have klb : b ∈ ws.erase a := nd.mem_erase_iff.mpr ⟨ne.symm,hb⟩
          cases ka <;> cases kb <;> simp [List.length_erase_of_mem,ha,hb,kla,klb]
        omega
      rw [childTwo_swap _ nd]
      exact pairFast_sound g nd hb ha ne.symm (bin_comm d b a ▸ fresh) (bin_comm d b a ▸ pro) len' hc
def moveCheckAt (F : Frontiers) (cut : Nat → Nat → Bank → Hook) (s i : Nat) :=
  let ws := F.state s i
  let attempt := cut s i ws
  nodeFast s ws fun a b d ka kb =>
    attempt a b d ka kb || checkLink F (s-1) (childTwo ws a b d ka kb)
theorem moveCertificate_sound {F cut cap}
    (actions : ∀ g, Auto goal (F.act g))
    (cuts : ∀ s i w, HookSound s w (cut s i w))
    (checked : ∀ s ≤ cap, ∀ i < F.count s, moveCheckAt F cut s i = true) :
    ∀ s ≤ cap, ∀ i < F.count s, Impossible goal s (F.state s i).toFinset := by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi
    have h := checked s hs i hi
    unfold moveCheckAt at h
    by_cases he : s=0
    · subst s
      simp only [nodeFast,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
        decide_eq_false_iff_not,Nat.reduceBEq,Bool.true_or,and_true,decide_eq_true_eq] at h
      intro k hk hl
      have hz : k=0 := by omega
      subst k
      generalize eq : (F.state 0 i).toFinset = S at hl
      cases hl
      exact h.1 (List.mem_toFinset.mp (eq.symm ▸ Finset.mem_singleton_self _))
    apply nodeFast_sound h
    intro a aa b bb d ka kb ne fresh nd hw
    simp only [Bool.or_eq_true] at hw
    obtain hcut | hlink := hw
    · exact cuts s i _ a aa b bb d ka kb ne fresh nd hcut
    let w := childTwo (F.state s i) a b d ka kb
    change checkLink F (s-1) w = true at hlink
    simp only [checkLink,Bool.and_eq_true,decide_eq_true_eq] at hlink
    obtain ⟨jBound, eq⟩ := hlink
    let g := (F.locate (s-1) w).2
    have no := ih (s-1) (by omega) (by omega) _ jBound
    intro k hk run
    apply no k hk
    rw [←sameWords_sound eq]
    have mapset : (w.map (F.act g)).toFinset = w.toFinset.image (F.act g) := by
      ext a
      simp
    rw [mapset]
    exact transport (actions g) run
abbrev Move3229 := Sig × Sig × Bool × Bool × Bool
def bools : List Bool := [false,true]
theorem mem_bools (b : Bool) : b ∈ bools := by cases b <;> decide
def pairMoves (s n : Nat) (ws : Bank) (sole : Bits) (a b : Sig) : List Move3229 :=
  bools.flatMap fun d =>
    let z := bin d a b
    if ws.contains z || z == zero || z == one then [] else
    let da := allows sole a b d
    let db := allows sole b a d
    bools.flatMap fun ka =>
      if !ka && !da then [] else
      bools.filterMap fun kb =>
        if (!kb && !db) || decide (s+1 < n+ka.toNat+kb.toNat) then none else some (a,b,d,ka,kb)
def enumerateWith (pair : Sig → Sig → List Move3229) : Bank → List Move3229
  | [] => []
  | a::xs => xs.flatMap (pair a) ++ enumerateWith pair xs
def legalMoves (s : Nat) (ws : Bank) :=
  enumerateWith (pairMoves s ws.length ws (coverage ws).2.1) ws
theorem pair_visit (pair : Sig → Sig → List Move3229) {ws : Bank}
    {a b : Sig} (aa : a ∈ ws) (bb : b ∈ ws) (ne : a ≠ b) :
    (∀ m ∈ pair a b, m ∈ enumerateWith pair ws) ∨ (∀ m ∈ pair b a, m ∈ enumerateWith pair ws) := by
  induction ws with
  | nil => simp at aa
  | cons w ws ih =>
    rcases List.mem_cons.mp aa with rfl | atail
    · left; intro m hm
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨b,(List.mem_cons.mp bb).resolve_left ne.symm,hm⟩
    rcases List.mem_cons.mp bb with rfl | btail
    · right; intro m hm
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨a,atail,hm⟩
    rcases ih atail btail with xy | yx
    · exact Or.inl (fun m h => List.mem_append_right _ (xy m h))
    · exact Or.inr (fun m h => List.mem_append_right _ (yx m h))
theorem emit_legal {s : Nat} {ws : Bank} {a b : Sig} {d ka kb : Bool}
    (nd : ws.Nodup) (aa : a ∈ ws) (bb : b ∈ ws) (ne : a ≠ b)
    (fresh : bin d a b ∉ ws) (properZ : proper (bin d a b)) {k : Nat} (hk : k ≤ s-1)
    (len : (childTwo ws a b d ka kb).length ≤ s)
    (run : Live goal k (childTwo ws a b d ka kb).toFinset) :
    (a,b,d,ka,kb) ∈ pairMoves s ws.length ws (coverage ws).2.1 a b := by
  have da : (!ka && !allows (coverage ws).2.1 a b d) = false := by
    cases ka
    · rw [drop_required aa bb ne run]; rfl
    · rfl
  have db : (!kb && !allows (coverage ws).2.1 b a d) = false := by
    cases kb
    · rw [childTwo_swap _ nd] at run
      rw [drop_required bb aa ne.symm run]; rfl
    · rfl
  have bb' : b ∈ ws.erase a := nd.mem_erase_iff.mpr ⟨ne.symm,bb⟩
  have l2 : 2 ≤ ws.length := by
    have h := List.length_pos_of_mem bb'
    rw [List.length_erase_of_mem aa] at h; omega
  have ll : ¬s+1 < ws.length+ka.toNat+kb.toNat := by
    cases ka <;> cases kb <;> simp [childTwo,kept,List.length_erase_of_mem,aa,bb',Bool.toNat] at len ⊢ <;> omega
  unfold pairMoves
  apply List.mem_flatMap.mpr
  refine ⟨d,mem_bools d,?_⟩
  simp only [List.contains_eq_mem,fresh,decide_false,beq_eq_false_iff_ne.mpr properZ.1,
    beq_eq_false_iff_ne.mpr properZ.2,Bool.false_or,Bool.false_eq_true,ite_false]
  apply List.mem_flatMap.mpr
  refine ⟨ka,mem_bools ka,?_⟩
  simp only [da,Bool.false_eq_true,ite_false]
  apply List.mem_filterMap.mpr
  exact ⟨kb,mem_bools kb,by simp [db,ll]⟩
def readTape (width : Nat) (probe : Move3229 → Nat → Bool) : Nat → List Move3229 → Bool
  | _, [] => true
  | v, m::xs => probe m (v &&& ((1 <<< width)-1)) && readTape width probe (v >>> width) xs
theorem readTape_spec {width probe v ms} (ht : readTape width probe v ms = true) {m : Move3229}
    (mem : m ∈ ms) : ∃ sel, probe m sel = true := by
  induction ms generalizing v with
  | nil => simp at mem
  | cons a xs ih =>
    simp only [readTape,Bool.and_eq_true] at ht
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_,ht.1⟩
    · exact ih ht.2 mem
abbrev TapeChart := Nat → Nat → Bank → Sig → Sig → Bool → Bool → Bool → Nat → Bool
def probeMove (F : Frontiers) (checkOne : TapeChart) (s i : Nat) (ws : Bank)
    (m : Move3229) (sel : Nat) :=
  let (a,b,d,ka,kb) := m
  if sel=0 then checkLink F (s-1) (childTwo ws a b d ka kb)
  else checkOne s i ws a b d ka kb (sel-1)
def tapeCheckAt (F : Frontiers) (checkOne : TapeChart) (width data : Nat → Nat → Nat) (s i : Nat) :=
  let ws := F.state s i
  !ws.contains goal && decide ws.Nodup &&
   (s == 0 || readTape (width s i) (probeMove F checkOne s i ws) (data s i) (legalMoves s ws))
theorem tapeCertificate_sound {F checkOne width data cap}
    (actions : ∀ g, Auto goal (F.act g))
    (cut : ∀ s ≤ cap, ∀ i < F.count s, ∀ j, HookSound s (F.state s i) (fun a b d ka kb => checkOne s i (F.state s i) a b d ka kb j))
    (checked : ∀ s ≤ cap, ∀ i < F.count s, tapeCheckAt F checkOne width data s i = true) :
    ∀ s ≤ cap, ∀ i < F.count s, Impossible goal s (F.state s i).toFinset := by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi
    let ws := F.state s i
    have node := checked s hs i hi
    simp only [tapeCheckAt,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at node
    rcases node with ⟨⟨out,nd⟩,zero|tape⟩
    · subst s
      intro k hk hl
      have eq : k=0 := by omega
      subst k
      generalize he : (F.state 0 i).toFinset = S at hl
      cases hl
      exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    change Impossible goal s ws.toFinset
    apply enum_step (ws:=ws) (cap:=s) nd out
    intro a aa b bb d ka kb ne fresh pro len
    intro k hk run
    have hpos : s > 0 := by
      have nz : 0 < (childTwo ws a b d ka kb).length := by simp [childTwo]
      exact lt_of_lt_of_le nz len
    have excluded (a b : Sig) (ka kb : Bool)
        (aa : a ∈ ws) (bb : b ∈ ws) (ne : a ≠ b) (fresh : bin d a b ∉ ws)
        (run : Live goal k (childTwo ws a b d ka kb).toFinset)
        (m : (a,b,d,ka,kb) ∈ legalMoves s ws) : False := by
      obtain ⟨sel, test⟩ := readTape_spec tape m
      by_cases hh : sel=0
      · simp only [probeMove,hh,ite_true,checkLink,Bool.and_eq_true,decide_eq_true_eq] at test
        let kid := childTwo ws a b d ka kb
        let g := (F.locate (s-1) kid).2
        have no := ih (s-1) (by omega) (by omega) _ test.1
        apply no k hk
        rw [←sameWords_sound test.2]
        have form : (kid.map (F.act g)).toFinset = kid.toFinset.image (F.act g) := by ext v; simp
        rw [form]
        exact transport (actions g) run
      · simp only [probeMove,hh,ite_false] at test
        exact cut s hs i hi (sel-1) a aa b bb d ka kb ne fresh
          (child_nodup nd aa bb ne fresh ka kb) test k hk run
    rcases pair_visit (pairMoves s ws.length ws (coverage ws).2.1) aa bb ne with visit | visit
    · exact excluded a b ka kb aa bb ne fresh run (visit _ (emit_legal nd aa bb ne fresh pro hk len run))
    · rw [childTwo_swap _ nd] at run
      have len2 : (childTwo ws b a d kb ka).length ≤ s := by
        have kla : a ∈ ws.erase b := nd.mem_erase_iff.mpr ⟨ne,aa⟩
        have klb : b ∈ ws.erase a := nd.mem_erase_iff.mpr ⟨ne.symm,bb⟩
        cases ka <;> cases kb <;> simp [childTwo,kept,List.length_erase_of_mem,aa,bb,kla,klb] at len ⊢ <;> omega
      have f := bin_comm d b a ▸ fresh
      exact excluded b a kb ka bb aa ne.symm f run (visit _ (emit_legal nd bb aa ne.symm f
        (bin_comm d b a ▸ pro) hk len2 run))
end Pnp3229Certificate
namespace Pnp3229Certificate
namespace PackedFront
def bitsAt (v sh wd : Nat) : Nat := (v >>> sh) &&& ((1 <<< wd) - 1)
def field (f : Nat → Nat) (wd per i : Nat) : Nat := bitsAt (f (i / per)) ((i % per)*wd) wd
def dwordsD (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x21001813504512500510f02610d2a410d0240fff6c0fd54c0dfe600dcd640dcc400dc4c00dc4640dc4630dc4470dc4430dc4420c00c209001807bb2f07bb2e07bb2c07912f06990c06950c06918c06914c06910f06910e06910d05092405002705002404c04004010404000701be2001bb2401baa001ba6001ba2301ba22012018010023000d43000d0000081800080200080000044000040000029800028000010400008000005b00004300004000002100001b00001a000018000003000002 else 0xa92039a9201ba9201a9250858ffe638ff44387bb6f86b94f86b14f85092784010783ba638238438234438231478230c38230478108238108028020187fd5ff7dfef77dc4f777fbbf77d1bf75fab77548b77540b75fff7d5fd57d5ed1ff5dfe715dc4755dc4715c40f357fb3d56d93f56d93d56d53d56d1bd56d17d56d13f55fa3555fa315448335448315444315441355440b15440715440355440334402803fd5ce3dfee63dc4c637d18e31faa731faa63148863144863140c63140a7314087) else 0xff42b7ff4286fe4fb1fe3fc3fe0f80fdcd40fd6039f92d18f6dd3df69d0cf67d73f54db7f44d35f44d33f44d31f3bf63f23d43f1bf22f1bf20f14da7f14d86f00d80f00d40f00d21f00d03f00d02ef2298dfc6f1ded3bdde72f3de42b1d6f17fd67077d67073cfc6c0cfbaa0ce938cce32c3ce0a80ce0680ce02c0ce0283ce0282bde4deb9609eb3fae7b378c7b370c7ade458abba7bab305ba9ba3aa9ba38a92818a9211ca9203b)
def dwords (i : Nat) : Nat := field dwordsD 24 64 i
def rawBank : List Sig := [0x1ba20,0x6910c,0xdc440,0x314086,0x544031,0x56d13d,0x823043,0xa92018,0xce0280,0xf00d00]
def selectRaw : Nat → List Sig → List Sig
  | _, [] => []
  | bits, x::xs => let tail := selectRaw (bits >>> 1) xs; if bits % 2 = 1 then x::tail else tail
def decodeExtra : Nat → Nat → List Sig
  | 0, _ => []
  | d+1, v => let t := v &&& 511; if t = 0 then [] else BitVec.ofNat 24 (dwords (t-1)) :: decodeExtra d (v >>> 9)
def count : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 5
  | 8 => 14
  | 9 => 59
  | 10 => 258
  | 11 => 560
  | 12 => 281
  | 13 => 21
  | 14 => 2
  | _ => 0
def r5D (i : Nat) : Nat := 0x4610051a0
def r5 (i : Nat) : Nat := field r5D 37 41 i
def r6D (i : Nat) : Nat := 0x10051a93291856146808c2009821a0
def r6 (i : Nat) : Nat := field r6D 46 33 i
def r7D (i : Nat) : Nat := 0x6515851a90000040130435265230ac260868000461d08011d000000a83b919a4
def r7 (i : Nat) : Nat := field r7D 55 27 i
def r8D (i : Nat) : Nat := 0x12c93401d471152592675210e2a20019456130435200000e84008ea40065230dc57f0000ca461b88be00011856200474865230e85608e80006a230e841f00008c3115883e0001948c2b06cc8a832918622be800000001dc8df20015aa83d119a4
def r8 (i : Nat) : Nat := field r8D 55 27 i
def r9D (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x351185620f90d465230e857f00000065230b7e400280ca4615fc800501948c2b7900065230c457f0000fe65230af64001185620017c80000194782bf90ca461d8ac07a21948c2b0600e64541948c2b07fc0a8329185602e915065230ac07b2220ca4615832e400000ca3215fd200000008c21f9c000000000eff68015aa83c00d2d000015a7a237c8a83c1948c0ca9400ad541e08cd2aa0f0652300f250000112783374a00449e0ca5be1400893c1946dd080112833c19725 else 0x49a00ea38cb800933a90871d325926751c01aaa4b24cea3801c7400000b44218fb000003291c5bf20000000328272f00001147932f4a00541945a18eb000a83291c31d3000ca3915823a900000ca3715fd200001946e22fa400001588011d6800ca3a15823a900000d43a107d200000c45620fa400a8328c457d4801506515863ac00000ca4606cce00541948c31e8c00a8329184bd2800ca461a0afe4001948c3415fc000329185622f9000003291845f2000ca4615823a4) else 0x15065230afe4002a0f0652374a0050a58ea387a80096401d471b50012c75210e3e2)
def r9 (i : Nat) : Nat := field r9D 55 27 i
def r10D (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x1709344996a75a24d1265a9d2c9344996a749a24ca38e9d1265208afe5449945603d954c89328afe449a24ca2be951284328afe4449e0ca2bf9526893c197a5449e0ea65e951278328e7a5449e0ca2be95127838197a5449e0ca23e95127834197a556a24f065e9570893c197a5449e0d465e95127833997a5449e0ca63e95127832977a5449e0ca03c954c893c197a5449e0ca10e952c893c197a5449e0ca38e9512843c197a54b9d4be38ea954a84b9e1ad4b9948c2bf912e753291ba6 else 0xf065230afe53c1948c2bf9000003b197ed56aa0f0656b40000569ebed002b4f003db400003c19bed001e0ca5bf340078328dbe90020cf065db400783a197ad3c1948c0cb94007a3291be5001e8ca46f9000ad3c11be53c1948c03d9550783291be5541e0ca46e94f0753291be4002b50c78eb50c783291ba5002b51278eb40089328dbeb00224ca29fb400893a197af00000fa65f9c00004499be700224ca5bf1c009244996e700224ca36f8c0089419976700224ca29f9400893a197a7) else (if i < 3 then 0xf665230afe400000ca33fac0000328abed000010275dbc0000001bfef000015015ebd50753280f2f499d4ca38eb8000015857ef000005615fb55075328afad3a9948c2bfb11865230afe5461948c2bf90008c32823a700281186579c008f46196e700230ca31f8c008c32863e600230ca25f9400004619be700230ca5bf1c009246196e700230ca36f8c008c328a7e500230e865e9d508c328afe5431948c2bf900000328cbeb000000021fbc006515877ed001e8ca46f9d50783291ba7 else 0xad23032e7001948c08e9c00a03291be700280ca4679c0065230c7e3001fcca46d9c006523097e500000ca3cf9cca461d80f4732918180399d50652303fe3002b5504679d50652300ba7541948c03d9d106523032e7329185603d955065230afe532918702bf90ca4615883e4349948c2bf90ca461d8afe4341948c2bf90ca4e230afe4569948c2bf90d465230afe4329185602f913865230afe43298c8c2bf90ca461580f644c9948c2bf915065230afe44f1948c2bf911065230afe4)) else (if i < 6 then (if i < 5 then 0xa8328c7ab002a0ca18ebc00a832863ae002a0ca25eb400651c023ab001947208eac00003288bef001945608ebc00a0328adef0023cca2bbbc0065188afeb001945618fb8d4651c8afe900194682bfb400651a0afe9001945622fb400003288bed001945608eb4006a15883ed35194742bfa40000328b7ed00280ca2bfb400a0328aded0023cca2bbb40065188afe9001945618fb0007f328af6d000ac4002fb550651583fe9541945602eb550651580f6d4b1945603db4ca461580f6d else 0x6a328a3e9001ccd465eac006516863ee001945a18fb0006523863e600001404efbc000050139ef000009c31fac000027063ee000009c25fb4009c328238f001941003cbc0000328176f00280ca035bc008f3280e6f001946203dac00650c00f6e001944a03db400793a197ad00228e865ebc008a3a197a700000ca12dbc00003300f6f00194b603d3c00923280e6f001946c03dac00651480f6d001948a03d9c00743280f2f00290ca1bfb400a43286fec002910465db400a439197ad) else (if i < 7 then 0x803a8e36e001d48438fb80075210e3e64b1d47006fa92c751c00f7a499d47006eb926751c00f3e4b24cea38ae92c9344926b30029c2e03d780000538b3fc000010a2cff0002c0b80f7c00000005cf7c00002d85fde000008a17fd800003a05fbe00000fc5bd7c00003f1d33f000000054fbc00002d937cf00001064ddbc0000268a7ed000009a45f9c00003a137af00290ca1bff000a4411977d00290e465ef4000015877fd4d24d1265a9d127832957a5000009c08ebc006a32873ea else 0xa8328afed002a0ca46f9c0065230afe4002a0ea65ebc00783291be54b9948c2bf192e753291b865a25892039ec00000018bdf00000005efbd34942f8e6e9000008c0d9fc00a53a90be7001d48e42f980000509f1ef00001007cdbc00003e10be700001007adbc00003d10be700001007adb400003d10be5002910075dbc00a43a90be754290ea556f80096401d76f00258ea42f9c00a13a8e1ee)))
def r10 (i : Nat) : Nat := field r10D 46 33 i
def r11D (i : Nat) : Nat := (if i < 7 then (if i < 4 then (if i < 2 then (if i < 1 then 0xb444997e753224cbf3a24ca10f9d628932fce9644997e749a24cbf3a4d1265e9d12651c7ce89328e7e744a10cbf3a24ca2bf9d126515fca893a997e7449e0cbf3a24f065f95127832f4e893c197a5002b8bff7801365ffbd2e5f1c7d6972f8e7eb5325c57fe25cbe2bfb52e4615ff8973a8e3be4b9d4bfd7a5cea46ef800973d7fa00571e3fd0026cf1feaa12e78ef554973c7da973c1d7bd002b8cbf78013665fbd4c9732fde97328afed4b9948df7a5cca46f9d2e7532f5e973c197ed else 0x7835197ed3c19ccbf69e0ca63fb4f0652efda783280f6d3c1a0cbf6a98f065fb4f065087da963c197ed3c19471f6a20f065fb4f06524fda843c197ed3c1948df69e0ca46f94f07532fda863c197ed431e0cbd68015a89fbd1265087dea444997e74499471f7a24ca49f9d126515fda893c197ed4499483f3a24ca3ef9c008b32fce893293be756a24cbf3ae11265f9d126a32fce8933997e7449a0cbf3ac11265f9d388932fce9c44997c744994c7f3a24ca5df9d126501ece9944997e7) else (if i < 3 then 0x963a997ef499d4cbd79d4ca38fb8ea651cfde75328afef3a99457f69d4ca46fbc00ad467dea446197e74619493f3a30ca2bfb51865237cead46197e75c230cbf3a30d465f9d186732fce8c3280be75a230cbf3acd1865f9d4c8c32fce8c32843e754230cbf3a591865f9d268c32fce8c328e3e7461eccbf3a30ca2bf95187532fce0056a1bef4319457f6a18ca46f9c00650efde003d197ef541e0cbd79e0ca39fb4f06515fda783291be73c19447f6ab4f065fb400ad3c7dab83c197ed else 0x652491be7421948df79948c2bfbcca4615fdc65230afed349948df39948c3bf9cca4e237cead3291be7002b48df39a8ca46f9cd065237ce652300be7581948df3a70ca46f9cca63237ce652e91be73291807b3a64ca46f9d6665237ceb13291be7541948df3a78ca46f9d1065237ce65230e7e73d9948df3a10ca46f9cca4615fce65230afe53291857f2000ca15fbc00750afde0000057ef002a4cbf7a2cea65f9c00ad3afde7533997ee3a99407b7a90ea65fbd507532fdea83a997af)) else (if i < 6 then (if i < 5 then 0x7b32927eb52210cbf7aa10865fbc00652efde00328ebef5699457f79a8ca2bfbcca2b017dea6328afef5319457f72a0ca2bfbd2c6515fde94328afed328e457f69a4ca2bfb4ca2b107da65270afed5699457f69a8ca2bfb4ce6515fda651580bed4e19457f6994c62bfb4ca2b01eda68328afed4c99457f6aa0ca2bfb52c6515fda9e328afed4999457f6a20ca2bfb4ca4915fda7b328afed0019ccbf7800d265fbc0065257de005691bef3291807b7a90ca46f9d5065237de883291bef else 0xa83280baf54270cbe7aa0ca03dbd68a832fdea852195ef002b52df7a58ca03dbd689632ddea84f197ef002b529f7ae12865bbd689432dde005a997ef5c24ccb77a4cca03dbd689332dde9649996ef001accbf7800ca64fbc00ad1c7de6a328e3eb328e007b7accca38fad4c651c7dea6328e3ee4b19471f5a4cca38fbc00ad447de003298fef3519473f5accca39fad28651cfda0035197ef001b0cbf78015a49fbcca4901edea432927e73292471f59949239facf66a32fd67b3280f6f) else 0x5680f6f5c19407b79a8ca03dbcce6501ede650180b6f3298c07b7994ba03dbcd065206de00569a3ef3419407b7a64ca63f3d32652ef9ead4c997cf4c99ccbe7ad0ca03dbd669c32f9eb33280f6f5319407b7a993265f3d68a632fdeb453195ef00198cbf78000066fbc00652dfde003296fcf00248cb77800ca36fac008332ede00328a7ef0019453f6800ca45fbc006522fce003a197ef001d0cbd79942003dbc00ad32fde00002b7ef5219417f6a90ca03dbd506507fd6ad54195ef)) else (if i < 11 then (if i < 9 then (if i < 8 then 0x3295bef00260cbf7ab4ca51f3d5a650f7da005693bef002b4a3f78015a51f3c00ad0f7da6a32823af0019411d7800d44efbc00ad357de005c1abef351941df599cca4cbbc0067277de005699fef00194aff78014065fbc00a032bde0047996ef0019463f5800ca18fbc00650c7dc003f9976f001944bf7800ca25fb4004e017dead4e197cf4e1a8cbe7994c62edbcca632779e005698fef58194c7e7a70ca63f3cca5d0b6de652e93bcf002b4bbf7ac0ca5df3d38652ef9ead3280f6f else 0x9a3298fcf4d194bbe7aa13465fbd349432dde9a49996ef001a871fda98ca38ff92c651c7f600350e7fb5519473f7a68ca39fbd486524fee65248e7fb00274cbf7800ca61fbc00ad2ffdeb03297fcf4e194bfe7994be38facca5f1cfd67b3297feb3c194bff6800d42bffd346515fde652f8afef002b48dffaa8ca46fbcea652afdc0000077ff3c19473fe9e0ca2bff5548932fdeb044997d74e224cbebaa91265f9d268932f6e9a44997e744994abf3a24f065edc00ac32fde0032983ef) else (if i < 10 then 0x47212ff0021061fd8010817ff80084127fa0042137ef002b4a3ef8015a1eff400ad2afde0032823bf00280cbff80140657fc008f32dfe00328c7fb0019431ff000ca25ff400b0357be004e1abdf002b4c7ef8015a5df7c006832fde00531abff00000cdff800ca5bf7c009232dfe00328dbfb0019453ff800ca29ff4006522ffe0032917f7001d0cbdf800ca53fbd486505ffa00521abff5219491fbaa8ca63f3d549932f9eaa52197ef55258cbf7ad12865bfc00b632fde004d1abef else 0xb044927d74e22493ebad11249fdd2c8924fe69344927b74492471f9a249239fcc0057187f6002b85ffe001f8afbf8014e17ffc002c0bffe001605ffd0029c2fff0010a17ff8002c0bffc001605ffc00000afff801564dfbc005726fde00000137f0015c07bf800ae03d7c003001ef6000b80f7f0005c07bf0009a03dbc00a62bfbe00530c3fb002982fff8014c17ff800a63f6fe0053137ef0000023ff800ae10f7c0017087fc003f0437f0013421f78010857f7c009f427fe004fa11ff)) else (if i < 13 then (if i < 12 then 0x682300f5f000007bff801503bf7d504601efe8823032ff4418c8ded9f0ea03d7d64873aede7a3a80f5f591e8ebf68010075dbc0075217de003a90be7001f00df7800f406fbc007a037da7a3a80f7d00000ddffa90ea06fbd487501efea43a957fe4b1d40df7a58ea03dfcea38037dc9c3a8e3de3a8e007bf258ea38fe926751c77c9c3a8e7df4a1d473fea4cea39efd487524fee75248e3fa3a92473fd9d4be38fe948863c7faa443127f7000007fffa591238fed488924fee89248e3fb else 0x4c873fe0026451fe8013244fdc009939f7e004c94bef00264b1ef80144997fc0099485fe004c867fe002644dfe8013243fdc009927fdeb74418fdb00270d9efad09203dfd2c4901ef6b44b126fb5227893fb800002fffd2c9324df6491c00f7b3d92407bd8013863f7d285f1c7f69a2f8e3eb4e17c73eda64be39f6d485f1cff69a2f8e7eb4d1ecbff5800d23bf7c00001e7fe004e1a7df0018c197f98c8c2ed7cd24601ebe461d80f5f23030073f8009403dfcc64601ebe0034032ff) else 0x15046ffcd4651cfb6a8328afdf002a0cbf7800ca2bfb40065237ce003a997ef001e0cbf6a5c8c2bf794c9732f9eaf4b997cf4b99457e7a5cca46f1d2e7532f1e9c318bb5f0018cb3ef80146637fc00631aff6003186bfe0018c4ffe800e263efc0063287deb7318bb5f4e18c07afadcc603d7c00992d7be004ca46ff)))
def r11 (i : Nat) : Nat := field r11D 37 41 i
def r12D (i : Nat) : Nat := (if i < 3 then (if i < 2 then (if i < 1 then 0x59997ef53197ef32843ef58997ef52197ef54197ef4b197ef4f197ef4a197ef49997ef328e3ef44197ef328e7ef32927ef3d997ef42197ef328afef328afed3291bef3291be73a997ef46197ef46197e743197ef3c197ef3c197ed44997ef44997e700267df002bbff0026fff00267ff5a25fff5325fff57a5fff5225fff5425fff5525fef4ba5bff4ba53ff4ba4fff4b8e3ff4b8e7ff4b927ff4b97fef4b8afff4b8affd4b91bff4b9d7ff4b9d7bf4b923ff4b9e3ff4b9e3fd4b997ef else 0x1abff33997ff3280bff58197ff58197df4e197ff4e197df3298fff3298fdf32977ff32977df34197ff34197df4c997ff4c997df5a197ff59997ff53197ff32843ff52197ff54197ff55197ef4b197ff4a197ff49997ff4d197ef328e3ff328e7ff32927ff3d997ff3297fef328afff3291bff3a997ff3c197ff44997ff44997f73293bef56997ef002b7ef5c197ef35197ef33997ef3280bef58197ef4e197ef4e197cf3298fef32977ef3280f6f34197ef4c997ef4c997cf5a197ef) else 0x3a8e3fe441d7ff3a8e7ff3a927ff3a97fff5821bdf4e21bdf4ca1bdf4ca1b9f5a21bff5221bff5421bff4b21bff4aa1bff5ba1bff49a1bff430e3ff43127ff4311bff431d7ff448fbff000fbdf0022fff4498fff4498fdf44977ff44977df4480f7f4ca27ff53227ff4b227ff448e3ff448e7ff44927ff44927f744a13ff449d7ff2b807ff0015fff0015fdf000c3fb0005fff0005ffe001fb7f00137ff00137ef018077f53007ff08007ff42007ff56997ff002b7ff5c197ff35197ff) else (if i < 5 then (if i < 4 then 0x4c9efff4a9efff4f1efff5b9efff3d927fb00277ff0018fff5817fff5817fdf4e17fff4e17fdf4c97fff4c97fdf5a17fff4a97fff4a17fff5b97fff4997fff4d17fef2f8e3fb2f8e7fb3d97ffb3491bff3491bdf001a7df230efff000efdf4e11bff3191bff3191bdf2300f7f3411bff4c91bff5411bff4f11bff4411bff3d91bff2f91bff3e1d7ff439d7ff3d1d7ff3d1d7fd459d7ff3a81bef3a98fff3a98fdf3a80f7f3a9a3ff3a9a3df4c9d7ff4c9d7df521d7ff4b1d7ff3a8e3ff else 0x4b923df4b997cf318bb7f4e18fff4e18fdf3182bff318bb5f3180f7f3180f5f4c87fff4c9b77f4c98fff4c98fdf4c977ff4c977df4c80f7f4c80f5f4c9a3ff4c9a3df4c83bff4c81fff4c9b75f4b18fff4b00f7f4ca5bff4e223df4418fdb4ca23df36127ff001b3ff001b3df25127ff46927ff25927ff35127ff58127ff58127df4e127ff4e127df31927ff2e927ff2e927df2480f7f34127ff4c927ff5a127ff4b127fb4f127ff49927ff248e3fb581efff4e1efff4e1efdf3d80f7f) else 0x11bff56997df002b7df35197df54197df328afdf3c197df00197ef57a5fdf4b8afdf4b91bdf))
def r12 (i : Nat) : Nat := field r12D 28 54 i
def r13D (i : Nat) : Nat := 0x3ff32fbe97f7cc7ff98fdf01efe99ffd33efa5bff447fe49ffcf7ff97fff237fe75ffd0dffa27ff00ffe65ffccbf7a5fff
def r13 (i : Nat) : Nat := field r13D 19 80 i
def r14D (i : Nat) : Nat := 0xf7fff
def r14 (i : Nat) : Nat := field r14D 10 153 i
def recData : Nat → Nat → Nat
  | 5 => r5
  | 6 => r6
  | 7 => r7
  | 8 => r8
  | 9 => r9
  | 10 => r10
  | 11 => r11
  | 12 => r12
  | 13 => r13
  | 14 => r14
  | _ => fun _ => 0
def extraNum : Nat → Nat
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 5
  | 9 => 5
  | 10 => 4
  | 11 => 3
  | 12 => 2
  | 13 => 1
  | 14 => 0
  | _ => 0
def state (s i : Nat) : List Sig := let v := recData s i; selectRaw v rawBank ++ decodeExtra (extraNum s) (v >>> 10)
def wordH (w : Sig) : Nat := let n := w.toNat; ((n*0x9e3779b1) ^^^ (n*n*0x85ebca6b)) % 0xffffffffffffffc5
def listH (ws : List Sig) := ws.foldl (fun h w => h+wordH w) 0
def hsh5D (i : Nat) : Nat := 0x0
def hsh5 (i : Nat) : Nat := field hsh5D 1 1536 i
def lut5D (i : Nat) : Nat := 0x0
def lut5 (i : Nat) : Nat := field lut5D 1 1536 i
def hsh6D (i : Nat) : Nat := 0x0
def hsh6 (i : Nat) : Nat := field hsh6D 1 1536 i
def lut6D (i : Nat) : Nat := 0x400000000020000
def lut6 (i : Nat) : Nat := field lut6D 6 256 i
def hsh7D (i : Nat) : Nat := 0x0
def hsh7 (i : Nat) : Nat := field hsh7D 1 1536 i
def lut7D (i : Nat) : Nat := 0x20320000020018000000040000000000000000000000000000000000000000000
def lut7 (i : Nat) : Nat := field lut7D 7 219 i
def hsh8D (i : Nat) : Nat := 0x412
def hsh8 (i : Nat) : Nat := field hsh8D 2 768 i
def lut8D (i : Nat) : Nat := 0xa000a73000000000c00000002000c100000000000040100000d000118000000000000050699000006000b000007000
def lut8 (i : Nat) : Nat := field lut8D 8 192 i
def hsh9D (i : Nat) : Nat := 0x3a3088c81c000104401110300d5c9040041040002102080
def hsh9 (i : Nat) : Nat := field hsh9D 6 256 i
def lut9D (i : Nat) : Nat := 0x30000060b867700130dc06332643d81a97c3a0d4340b816039f7134170240003c25040050ac381b0b26041441446419a40a8000466601c0400013789da0080c0b021000000a0220058009c0d9b4af0600004439314de080310c83906400022c0070380382d0a407181000002420003000120201502c0a0000000000074232d0730500546c230
def lut9 (i : Nat) : Nat := field lut9D 10 153 i
def hsh10D (i : Nat) : Nat := 0x20a30509648c49f5814a15010000c002468c32946a81a04103000950300330121c003041e281050600181022c19f0a007a8042000506000001c003810e9000342000090a24023040858602144842c00901060000b0a101844c043080410301202050000082890418201121c1040c042800400488000008500000820028010080c387
def hsh10 (i : Nat) : Nat := field hsh10D 7 219 i
def lut10D (i : Nat) : Nat := (if i < 3 then (if i < 2 then (if i < 1 then 0x13600008c5f700004180119e604507101b64d720005602209f207404381a65a004770d00301560c900282cc400026700033ddc6230300000000e100925b80982c00007f80000000fd40000000f60bb03db8000ece43968880000004877e4b501aa25005638001c42cf02a023c1ce09e00eb0940c210102d80000d203404082241a82b016503c8134036600010240006d43100001d800006600002002de0758ac1c380ab75180001860a504e0244000000039390414ccd37138290cea8000 else 0x1080a7780030002e02270b3078192c0801d039c4ee02d609038197c02d000009840003341480e0094edf73f22e01fa0b303922b84600396364959c62c0000000ec0aa03601581c81c4ea7041a8880360d8752b00005007302400c516426a72901641a604f00101b900004905f80dc00010196683080000fc413011009808602b20240e6e8501781b4194c71031c8f40d123e0588a480ac04a04b02080ecc2c068bbac1d00b1000000018e05578043519fc0348728064030ef316c80c990e6883) else 0x11606305b8318000094070816c45f04045c834803000003f00000cc86c0470225ce680003c90d9084048a0001d40ca07c73ab97c00200000a83d00000ef11881e6dc0001974080016002113403e80b0e2307c03a41ea04790001e41d405a03c00001e42d2125819815400001bb1c000005740001d9144400015016015e098008026419607b405800014845d000019000601970003040ae0e300022d8154e0a02381564c000002300000ccedc0088160800015600024c0dc00005300341420ef0) else (if i < 4 then 0x280d2726b93406a843033480018a0fd61982f4056e7a7000280036e3507680cd80c0f100e800000005104803600dae1f03f800000ac87720035409c00006e80f01b40a911000798080d106700001000f705098001680a202e108400004c75d0091d1401f64681d1c0009f00003ec0cf2ad05e03e195200006f814c14ce7a03739ba454ec803781781f80a3246004c0828390730b10066224020bad412a00004400382016db00000d58aeed707800fc0ec06a000003c0f8000024b8b500002e0 else 0x62943927412e0ed18011f4000001419ab581360000148ab44b8047411bb9006ae1467b0398050c7615401f50000000493b604d600001a4908cce0ce12122a1c6400081288000000a407702b9d5c0b20))
def lut10 (i : Nat) : Nat := field lut10D 13 118 i
def hsh11D (i : Nat) : Nat := (if i < 1 then 0x9c182160028828008810008394421868526441000e0410a0200a0e1c5800c560409000393140c0c48a06202821e20482124c6831060002101410000501000200a0c0004000020051922a8100022023902640030414684381c0822e10001000c085180421c0a0010f0094002062018a1600a000c2c18f0444181161c1051e1c080142c08c0004002020002000008ae340448500000010a04c8314001010010002261c000301c086022c1004620303380c0130a0010e0a0410002040060000128 else 0x3c6285a6c07811a418f06001022ab432a00404851e00084260c2812000f8100b46881000829140c98c1c2c1022c1078d8c2c11e2e080820e0de89182820f14341000000200342008b1604012000412902040050811480005410b2614e060850088)
def hsh11 (i : Nat) : Nat := field hsh11D 7 219 i
def lut11D (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 2 then (if i < 1 then 0x22100001bb011c15114180ed36f80dc74681a0104640724ac00004a800247dc046600001c0295c0006c01a503901f306e980005c8121000020e07700b10000179000020563bc45b00900a8485804c03e1974000020c00501e8353d8000079cc2b55c084000012560ac1cf750020a05c05e4042c50d7305c1203d0d2f0058000083c22b91680a2106c0000098182032c0640800204000000004dc02a6000000016409148a484868b2deb02b1c620011ca146998000709989000000006581e10 else 0x4381560099daa67a022a04f80f736b407205b005365f5c0702281a1015800002384c2a26804340140a5100007c008980003c419b634810715c007a12d40ed054000006fd88702d00f90360000082c227000005936fc1fa08242257000066089888b41ec0faa2580e9b7344b8061402303d1990067d973615910614404c1075c1fd04145270309dc6072c1506051c740758000064808007adce2730dc0106e00e61674400088c11902c8ca541f09067249cdb64e807805740e701948000) else 0x1de189013c02ac1c3748022493f005667480f000001df00cc2250444100700012174400f4133dc8d924018475b417602f80da123c152666992200f59d801d10c87000000000022440bd981700019d651012c05dc00002969d1159c49900000444000000032800000001cc13780180000157121400001e45a200f410d102d92013b48a5600008b70bc05765dc47e100004e034007d70000eb063c00605140000739ca648641ee41698ce008822118b408303e587100081c302040ef081402e6) else (if i < 5 then (if i < 4 then 0x8220a19e005b58236705975048c00002d80000735d1e00001bd06f5dd316a40256731cdc05bc51b050800f0000222489ca1a08a51f7184c091073194b00000d66660058627100003a4040081c1e010381e912bddd400d410a05ac02c042850900d800006bc1ac06e8000026114e100019e160849b0741800079809543ded8d032c5fb07485f047d04a856898fa076800e85e813b028c011753c0650815d8371bc00b03200a945c41d170000a2457c063003004767a81ec009c15271540fab else 0x65622509345780e070001b306d800008342180285dca72dc173029603a04341a563d48c23175d4700441e20148070742c10002a40e666a1817125118070f000000f9e2c43a4d9b0021853044c14806901c0052804802cdd02775043a755921b018584405a8108147c19a033013003cc00004cc000010188770740000344000037c11c03800b8774dd4d62c8000037dc4b00000a657a0890962c03201f462528181f205b81037891db402d1d66034c0f0761811e67f800002b4226912401a6) else 0x610053115dcda00000a403cd836422019301dc0cd00000a472b00b2260c125770056473885ab60000b300001bc74c816875b8c760341c8c7308800022c10f00000807251c8912a009c000020760681b70558400025000003ec000065415976a80a5b2b5e2b08701e30025842672dd8a0274199024908871d4000000000001a000a00000000308229088c8a5309da2e060c46675addf0000019e0384000000016802981d907ad80002541d103c8e1203b000002bc000060400000000310)) else (if i < 9 then (if i < 8 then (if i < 7 then 0x55006f43dc1f900c00000049daf62a8115000007d077c565033c000021819703581b107c5000000006e00641d272e9c00018994e01d9c0004f400000001c0605c0e802b806368a00271030c7d65240a4400006b08500c5067c4e5627e425040c000073c14100000f871401e703d00fe034dc0006000d312781fc000003e00101c2013c0bf75f01d5040c5f1000000d010d984173821d06b8000031821f047412601700a52031800065021703f40a9958c22c06f0000028401726740080 else 0x139027c000019c00007d240004a00000035d2900000dd728005f60001d974600a505a40000001943002983807d005e000016100ec19f74d980003881f818bc20514d8075723a03e107c0b9076c10206c81c900001f6029c000064419c004de2c667c10470000ca1238869600022a9171207721d1ee069c01962310150405cfd15a5dd305ec40005b440005f417e704015100000a8145c08c03d417f7169d08736416f056000005c44e600dc0000311c290000071629552113b84dd059c17c1) else 0x15c0359c8d04480ea015016610000000000201023d079000013f0854107723acc9025906f60a005f03e5dca0108082109dca774d40ff000002a000012e0755a07138c1ed04b409a13f1c1d773c578069199c60000fc13a98ed63e0000023a40002ec093089e400043dc00074000006ac14c60781a60840000000d108024802e01b400003d815b00289e74260114000016000584d404e010504c41c5740411600000b003cc5e758b04607379c9701b016e1310061039417e08a600000000000) else (if i < 10 then 0x82027a555029658702fc1c705680000734225a3bd924018002460000d172aa55901a40ed177414d054c05707bc0da71601c402880937255cdb75480b971e80ca2238104073002d6494546008006772f415a779400000b41ff00d0000053002105ec21106ed844671597f02864a3411583f06300000000009000005d062004a000000007a407485c85c503c810c02f0064670400d672013400000ba07e1c726599e2340000ff7659826163807e0000202010c003043045106a5907080c0000 else 0xf531181a30259cfe16801fa73b80390494013000016201cc20803540db0301da8000016401040000000000000000007d41fd67a49761000007139da2002eddfc13bdc00000019961fc1de00000f2b1a804d06e40d70878000089807006d400003000c701140f72888226b5b059d77e008f730c0bc78b0d2670001e69275c890)))
def lut11 (i : Nat) : Nat := field lut11D 14 109 i
def hsh12D (i : Nat) : Nat := 0x102a0000163120010000003c5c2050ca84803c003823400083002c1815e005a1440c0980614280000851130158800804ead0004a000a00100223820c22bc2020018d0912042ae0634e8402045001018000080c1160e24188040048006641830a0c0810e20082001c283180c281020c0050c0c50302202010a04005003c1039a18084041448400001040204000001c0010010312044c00000080070e00002001000b000030300000840e08008
def hsh12 (i : Nat) : Nat := field hsh12D 7 219 i
def lut12D (i : Nat) : Nat := (if i < 3 then (if i < 2 then (if i < 1 then 0x4c2e000018841e20008880541060b842484395b029007388ac09404f03e0209e0206505d83f41ca201071b2841b6e7d64a800000008710101d191410300702cc0942068578448dca08b70282001ea023934800000002378501f821e0b277403580000560000170570c00050385991c05513ab0000760fe00a000019a02617c03a196c0d260002e1c1a09815603501c4c8e14d046000000000001f44880ed048bb99d17210112ba0c45ac60051823d1600b891858d5d2822702703d59d40000 else 0xa40cc0153a5dd362df75b815c1540fe70002c81a4112053033995a2cf77b806818e089717b824068000040b8cdc4807311a3af41e823160bb2588c0c0006182e4434c4501e8260102000042834462608f00003015cc03701883344f0c0000b82c407cc0001f0a3dc0010c400046062a0a0100041002c2957000000046800000b0000bec6772980191b2cbf04588f8064e5007600000302000043a9440001b64480000aecab054b2ca61004b00001d4114f0702c8a584ce09f700004c156e5a1) else 0xf2c8768302f00720fb07ab80004221923f837c00004760200a42000ba05d200004606208614349bc06600349845fcc3c05a8bd804200f0181000000048002880015c105121032c16487202b9be40000000548000118000074bad01e80bf1000111d400ea76ab27000000006782de40000001a080000000000f81e800ced511d0b6004a0630538a3e48601d00c5af061f2b805bba6c1e004004b58000f210506c89f980603615a296dce425f00c9a29800114055096017282292c81b80000e90) else (if i < 5 then (if i < 4 then 0x1c40fd700037858805104e39d01768cd6738000074019085802c03c0fa077029c00000003e820818ecf2700015401cc0000003c402220001b045c00000001cb1f858c0e313880e98000c911e8800144e6b058886091a09514b1bfc030ceb0798445a1c8c2000000022225f4163060d5a0000440945dde06406e80bc566e586458341d920a17063b7c59c0f715202e40200e41553bf454ec9660e02a1830000036800011007601708cc00003177a8b64000086003b8000bc11001831e01500d86 else 0x1dee0001c00000e003c74a034c0820da65f00f580004c02d001805e03314b027861a03f040b00000003b177b14d8a4200051b8000d40b447e018ddc6e12788a445c5ec0003bb0001b80687430a641b60a6107bb9d8de0ca0000161c2827706c3b5c21203004880c04aaf0c045a000024c8f8000121850054615026d9a20d0087b8b0188e1916333c192405717f0bc1c00035033300001ecda10fb32840000008a121021c02b771806c22949360003c801ac5d00eb3010fec151100165c2210f2) else 0x15ecb803f705b934052ea503080b40e0d0874e880022c00007203f58b605a719001c12e055625b8c0cd80de62a02a04d0000081021c0dcc0004f0000112cbc93982ac4000196173000204e65162815c800011b7409ec104c460510865e0c20006a8221916c9f00003040180701323b800082c000b391c04c0e1080ba7c5b400006fb25d96a09300b8a498240a20050051ccac9d00b000016e8661040081844000042b00014228066708000a0e3a70003200000956))
def lut12 (i : Nat) : Nat := field lut12D 13 118 i
def hsh13D (i : Nat) : Nat := 0x2930210af082230002013001198c8
def hsh13 (i : Nat) : Nat := field hsh13D 5 307 i
def lut13D (i : Nat) : Nat := 0x4440c2773a4180671310000f028ca800203800160d0004c90d446b285a2809821c00312085c220158a8000e18000000079008620819b8c1c0a62bd026ce630000a1294895a8b2b38a59ae109d0000097004c650160029e0321
def lut13 (i : Nat) : Nat := field lut13D 9 170 i
def hsh14D (i : Nat) : Nat := 0x0
def hsh14 (i : Nat) : Nat := field hsh14D 1 1536 i
def lut14D (i : Nat) : Nat := 0x1000000
def lut14 (i : Nat) : Nat := field lut14D 5 307 i
def nb : Nat → Nat
  | 5 => 7
  | 6 => 7
  | 7 => 7
  | 8 => 7
  | 9 => 31
  | 10 => 149
  | 11 => 331
  | 12 => 197
  | 13 => 23
  | 14 => 7
  | _ => 0
def ns : Nat → Nat
  | 5 => 47
  | 6 => 47
  | 7 => 47
  | 8 => 47
  | 9 => 107
  | 10 => 521
  | 11 => 1163
  | 12 => 701
  | 13 => 79
  | 14 => 47
  | _ => 0
def hshift : Nat → Nat → Nat
  | 5 => hsh5
  | 6 => hsh6
  | 7 => hsh7
  | 8 => hsh8
  | 9 => hsh9
  | 10 => hsh10
  | 11 => hsh11
  | 12 => hsh12
  | 13 => hsh13
  | 14 => hsh14
  | _ => fun _ => 0
def hdata : Nat → Nat → Nat
  | 5 => lut5
  | 6 => lut6
  | 7 => lut7
  | 8 => lut8
  | 9 => lut9
  | 10 => lut10
  | 11 => lut11
  | 12 => lut12
  | 13 => lut13
  | 14 => lut14
  | _ => fun _ => 0
def locate (s : Nat) (ws : List Sig) : Nat × Nat :=
  let h := listH ws; let b := nb s; let n := ns s; let a := hshift s (h % b); let v := hdata s ((h / b + a*((h / 1031) % (n-1) + 1)) % n); (v / 16, v % 16)
def frontier : Frontiers := ⟨count, state, locate, action⟩
end PackedFront
end Pnp3229Certificate
namespace Pnp3229Certificate.PackedFront
def hintJ5D (i : Nat) : Nat := 0x0
def hintJ5 (i : Nat) : Nat := field hintJ5D 1 1536 i
def hintJ6D (i : Nat) : Nat := 0x0
def hintJ6 (i : Nat) : Nat := field hintJ6D 1 1536 i
def hintJ7D (i : Nat) : Nat := 0xaa8
def hintJ7 (i : Nat) : Nat := field hintJ7D 2 768 i
def hintJ8D (i : Nat) : Nat := 0xa99999999997642
def hintJ8 (i : Nat) : Nat := field hintJ8D 4 384 i
def hintJ9D (i : Nat) : Nat := 0xb15aa53a54a8d09f3e74c932234383060c183060c07ef5db972d5a3362c582f5cad4a74a911a13e74d9b3464b96284880e1a3058a
def hintJ9 (i : Nat) : Nat := field hintJ9D 7 219 i
def hintJ10D (i : Nat) : Nat := (if i < 1 then 0x1c8721c470dc16fdbf6f9bc6e9b76d5b36c1ad6a9a8699a3689a167d9c66d98655936458f6358b6298861985615826017e5e1745c56e5ad685956056d5853d4a50d404f93c4e5374cd304b92a4a5284952247d1d46917455134410d4290841904409003f8fc3e4f53ccf03bced3ace8398e4388df374db364d7350d133cca31cc530cbf2f0ba2dcb52ccb12bcae2b0aa2a0a6290a127c9d26c9926097250922408e2348b22487214832047f1f47b1e0761cc701b06a19864188611785d16c58 else 0xb4ad0b3ec8b12c2b02bdaf2baadeb4ac2acaa2a6a92a2a7e9da6695a468ea368ba2686a0e819fa7d9f67c9f2769d2729c26e9b26a9a26598a6097a5b966579565293e4e9324b91a4390a408f63a8de358ce308ba2b8a22588e208761a8621684e108360b82a0881a0480a007f9fc7e9f87d9f37c1ed7a9e7791e0775d9755d2741ce731ca)
def hintJ10 (i : Nat) : Nat := field hintJ10D 10 153 i
def hintJ11D (i : Nat) : Nat := (if i < 3 then (if i < 2 then (if i < 1 then 0x4c54c04bc4b84ae4a94a64a34a049d49849549148d48a48648247f47c47847446f46c46946646245c45845345044d44644043c43843442e42b42742442141d41941641040d40a4074034003f93f53f23ef3ed3ea3e53e23df3da3d23ce3ca3c53c23bd3ba3b73b43ad3aa3a63a339e39939539238e38a38738337f37a37737436e36a36836636336035d35835435234f34c34933f33a33432e32a32532131e31a31631331030e30a3053002fe2fb2f92f62f32f02ed2ea2e62e22dd2d92d52d2 else 0x6c56bf6b66b36b16ad6aa6a56a169c69869468f68c68868568267f67a67767467066d66a66666366065c65865565164e64b64864564264063d63b63763363062c62962662361f61c61961561260e60b6076056005fc5f75f35f05ed5ea5e85e45e05dc5d65d15cd5ca5c75c25bc5b95af5ac5a759a59258e58c58958758558358057c57857556f56c56a56756556356055755355054d54854353f53c53853352f52c52952251d51b51850d50a5075055035004f74f04e94e34de4d84d34cf4c9) else 0x89c89a89789489188f88b88a88788488187e87b87687186e86b86585f85b85685285084a84684284083e83c83a83783483182d82982682281e81b81781480f80b8048007fc7f87f57f27ee7ea7e77e47e17de7dc7da7d87d67d47d27d07cc7c87c57bf7bc7b77b37af7ad7aa7a67a379d79778f78978377d77777476d76876676376175f75c75975575375174e74b74774574073e73b73873273072e72c72a72872472071d71b71971671470f70c7097067046fc6fa6f36ed6e46de6db6d36d0) else (if i < 4 then 0xa85a83a80a7ca79a76a73a70a6ca69a66a63a60a5da59a56a52a4ea4ba48a45a42a3ea39a36a33a30a2ca28a26a1ea17a0fa0da0aa06a029fe9f99f49f29f09ee9eb9e79e39dd9d59d39d09ce9ca9c69c29be9bb9b89b59af9ab9a79a399f99b99899498f98c98998698398197f97c97897296f96696396095d95995795495094a94694193e93993693092c92792191d91891490f90b9069008fa8f48ed8e78e28e08de8dc8d88d58d28cf8cb8c78c38bf8bb8b88b58b38ad8aa8a78a48a189f else 0xb2ab26b22b1db19b11b0bb08b03affafcafaaf7af3aefaedae9ae6ae3adfadbad7ad3ad0aceacbac9ac7ac5ac3ac1abeabbab8ab5ab2aafaacaa9aa5aa3a9fa9ca9aa94a92a8da8aa87))
def hintJ11 (i : Nat) : Nat := field hintJ11D 12 128 i
def hintJ12D (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x1ceee71736b9a1cc2e5b72ab929c8ce4271e38e5c64e2f7143891c38e187083831c06e006fe37e1be2deb6f3b77dbb4dce6e236e5b68dae6d3b67db32d8a6c2b601ae6d666aeb559a9ed486a0b4e9a60d2b691b469a20d0667eb3d19dece566db359996cc265f32d995cca264cb24190ac78637b1a58c2c586263115878c326153089832c13605300d7ecbed5f4af7d7a4bcd5e22ef5772bb35d6ae99742b9b5cbae41716b835bfadf56f2b735b7adad6c8b625aead5d69eb475a1acfd672b2a else 0x22fb1788b945b22cb1628af456a2a114d8a344e625f12a892c45a22711088544122050ff87dc3de1dd0e9871c3761af0d3866c32a18d0c085e42e616b0ae851c26211f08884241fa0f507883941ba0d3059827c12a08902b813407e02f011806c02600b0017fe3fd1fdcfe67ee3f5dfa2fcb7e2bec9f44f967c53e19efef767b83dadeccf627aebd59e9cf487a13cf5e70f31793bc85e30f127873c21e06eff77c3bd1dd8ee57703b5dda2ec5760baf5d6eeb17563aa1d40e9a7493a25d04e7c) else 0x24e5269932c97e4b525192248f246d22e914c88a43b218909c84240d2018fec7e23e91f08f547963bf1db8eb474239b1c98e2c6fe3771b88da46ba3551a58d0c6763331928c7462a30d182)
def hintJ12 (i : Nat) : Nat := field hintJ12D 13 118 i
def hintJ13D (i : Nat) : Nat := 0x26173059804bee5e72ed974cb865b52ce9644af656b2ad9524a6e52928a941c9f24f1272
def hintJ13 (i : Nat) : Nat := field hintJ13D 13 118 i
def hintJ14D (i : Nat) : Nat := 0x4c5e62130b
def hintJ14 (i : Nat) : Nat := field hintJ14D 13 118 i
def hintValD (i : Nat) : Nat := (if i < 15 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0xfcb03f2c008b03f1f5607d580bd602b2e884ba5d5e25c0eb002290baa601290dc2373029d0196f2895417741f9623f599b9660a5982540b317aa816025b1ec56a24b8ad407d3525cfa820ca542ade053794c02002715e03580106ab036a64dc6d048e476001c9bd1ece490155e7d391bce46f01af02ea0392748872091c8de7c369642e0b4eaf15e17551b58c63583196003581bcc62b222688872371bd406d4cb18de714c2bce49a4e9f0e49d379b5147d4505c729a22280ca9a4ea64f899 else 0x2e3502b5d54350139418aa64b08b2170036132aa2210c30ae47aa9b2094e23d307c01385687501b84e4e1379b40e022e80dca036db34da6f00b9418010c061303f018615e035800d60d901ac1b2035826006b001ac006b001ac006b001ac006b057061601857b658c0d4918130c606024dec6459bc147c632a9b29c3eabd1e98458fd388f4c23d308f4c23d301947a60f8b45823d9cc9441f55c7c611c9607d5828192cd61361acc93eac0da183e86160a6571f8087d021f4089c3f2c0fcb0) else (if i < 3 then 0x49c01270049c023b40a047001408e002811c012393a4e46f04824e4e93d9c818ae04b655ecb0231162cb5e00808cb5e1958c63630118c650200d7817531f0b21705af138c45785d1e983e1b4c6d84e36138d84e070069c02361386f3185ce46e37a80da024c8086e6d5802588b06131812b0630256018581f9608f20388889d221c9c0af39049408625ac140cd503b912863e1b4b2170480802aa3685dca0903aa80a17581b588b00ba19ca6f0600d40e506008fc35770240caa449f4da07 else 0xdeb43b1f4e6a8009f544b45100d407c3780d407c379c40e04371c42e6e6b9b8720937274dc3b4e9b876004e8013ae11c8ec12040115dbe5d10ab824a437aa83aaa0126000980026004034c00806980026006980101138004e011386b1a808089c0101138b34901566f2050240a03068856e8e02abc24005784800af090015ec632b613803632c006c00481538e902a71d2054e1f5303704abd240557b640a9c02a700a9c6c81538d902a7116054e23d30c93f2c0049c00270009c01270049c)) else (if i < 6 then (if i < 5 then 0x144196f00c76a601add44e3501b8b2250bb5006b051190326e50291bca21b86446b1639b8fa875b0ed2e7d6f0fc2e0915884fa57010015e80012bc0457002bd0000192acda1c570d400ae72ab80085242bdcaa2010015eb73e1b46ae51aab80034570d55c8d003a11a234e1b406e81a8015e0200ac13209018d412034ca71127c011e41a89020d5607c038115e9911a70da99501f0da012c815c0aa371b406003eac12ae06727cf802002b8ea02578096cab5c8addae5391c42e6e3900cf8e5 else 0x1bca03e825167d58359b0b43ea8154e26f28110de57884307d6f274fade6b270300a00b18faf21185db07d01abdaee63e08d1ee80fa7030e854a915e183e810e4a65b1f85e0c5e2987ee0440013a0058381941701a99489d1f8258ce83e80c7ee03e9a56e190188db0493e814069d5b298062f5800c5eb049024c4af4400412b0018fd607d030dd5e7d478ad6cc82c86540440125d6002512c12e37018ed403f3e8ed3ab60cabd4ce00ca8960031da99a8196f21c32374eba4d4644e8fd40de) else (if i < 7 then 0xde57b60fc1237864086f3e0384aaf3e3941a03013194c035305dc0034a38128190c2a806010c3800605580088ea90180430af018042eb00600db2175800c30af01815604b6c290260302ac14e03003a430f10180550a91a86006ae5800d54af01a61527d1a80950ae578614e7d018615ea401808e4a66ba9138181a80c30b063220127c0637808b1551c9bc0457001b0ae3e801547d1bbc9c0c604a2d62de6c2c18c6d0200d54726b029660969abc029a580240a8b4e23c0eaa5a2087603 else 0xa17581b41404622c1840c43380da0c01b1160bc03ac018036c2c0680a013b56059010dd600276ac004ed581b4860724bb80ab02c8300437582f160037738184642c88c2e0b0003006c4500d430b0060615eee703b55e185792d886d0bb308086768380a9f369644ace072c0b2170500c0011029f818097480d607c3900dc2b4729c940035a8e44a00018d9c025019b968c24e81116d857b781809581f4043b522bc088b631c8dca011b25d2e16122c14046f3554ea0681f1c05d090bcbab0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x2e7902318087e0c31000044b811540b61265a2420c8381aaa662882eae010051eaa44a194c7c2c85cf80c0285d606d0031160c42cabc029a581bdb01101abd1e02050306a9847819307d3692c7e171a8153a07550091e981a8311e07573c5c6c9611645c250005c080347a65a8d1562a5507c0017456480c2a93aae0c2bd5c9d57281300c580040ab04d00400b000810dae076911e46d0500408ed7000418d84a8fc00947011c308506af008aa65310f86d00a204a852c80802ed581b42ee5 else 0xe41374a48e409062bd1612393a4005900ba0680f01379d29a43804e4d706381582a6f035b2b1120455eaa4d8dc001800b81540a1bb8032112eaa8000d5791422b01a8ad32b0228355e0059974180900abc080205a7000866f03006d95780934af1304d5ec44d00134006f004bade00174009f6f01138bc022d9bcbc021d55c0c68aa92409002bc1205580010ade01265609a00265c08506b79782f57364126057891407d4e824c4ae4c02030d65782030044e3b41600682b978173c81996bc) else (if i < 11 then 0x14054e02c040d4e01560c05985d326d1ba716405578400ab01b81406d9522bc0a9c02a7008b002ac008b00604c049c0602c049c020315e0d580dd5e3700a700a9c4b81496365a831b0b44d1c81aa406abc18b01a83006b3012601cde0227006b6058106e0e6f00cda3506039bc5f1a8301603022601cde1a8bc16de07061a00a4c1f46a0c098141cb055028fce05e17c6a190602c06054c039bc7d07065bc645797c6a0c0580c0898073780488578156029009c8da0402b818a8b010dde299 else 0xc445788406b70201d6eaf4387c7eb0008fd6088002c16e215b0040aaf022bc089c02a700ab0622c00aaf02abcf00c391b4089a391b52462579cce4d14f849660102abce400598115e65490115eb6090015e0c4e0040ab00501002b03c8dd6c7d39024068778abce4d83e8496693019c818b52e84966af39360fa1259b18fc09019f15eaf39360fa1259a1cfa720938030c6062618c7d391f1541259ba40a0c022bc1aaf1b8315e054e011600b02a7000054e03016024e0153804580084c9c)) else (if i < 14 then (if i < 13 then 0x1605f1480816b005314040b5800816b00102d6092028240492000140400580300aaf0201c160219000044e089381435002c01202778055eb600ac0ba01583581203010050ee736830045d5b0088a11580240452002bd0c526c8000048779bc1205292d8a40b048a5dee7000dc04004901400af002bce400578dc00af1b8015e03003655e6f6d05dbc0305abc12d311abcde4d048c4145d2432d8a6f020100e853c828040306b780803583c9d2023483012b64907cc84a5100cfc073e9ec063f else 0x6eaf5217c7237521b46a391b801d4b51300816125a9e400cc5c1bc0432092d40625142d4046d190496a32050081203550306a09550c8180204aa8180901aa86e09010315e03558156a044620c30020c0100683192d4da18020c88eb50c0100683192d4de180200d06325a8600883378c96a030c20c64b502abc0aaf02271240704abc0e093d81c12b00382560e90382560e90382560e9038256037048015e37048015e02002bc16055781160db3c94812001900816b002009600205ac0040b) else 0x2e0203a48dc39568853a6e1d8240200742893a3657920040e68388ae3902008025450275d0610000d020f0100006022b9b804122bac006023f0493a02512bd9205390115c021098944d044174040006a6452721fa20049d090dc00687403000d279264aed20015c56b04e808d4ae4400824575803de4a2358c56c6b18ad8d6025b1e598036600d70af5c0c824b50e8600683192d46e32552e0a2370e824060d572bcd6025b0c418af358c56ca42f8e46e6b5b2ac7237520907237521bc6405))) else (if i < 22 then (if i < 19 then (if i < 17 then (if i < 16 then 0x1600914a6482b00200c00102b9746e0201004009d570093aae0027554385701d30ec7501c14ea25abc00b65580156b65b1c8520255bbc04ab00abc0205729b5ca441891d541000aa8202972ae40226722986ee55c8addae54100472aa080a5ca1000aa86e29721b5ca4420000e8e81a0401e0570b14723708119ca0b1c388063b3e2880e0219ba0dca437001cae103ad096a25a1f0e4197280d486e00395c2075a12d44763e804faa201a80f86f3701c66e80182404aa391c42e07371b4328b else 0x64a2242140807572d0fa075731c46993eb9874e9399b4460c430dc6a0419058c89903ac068157081412c1003781609611bc00720204dd27c36808140d0c2c1546d203b41c055808cf8af5a1c934123e828060d570006ae0062bc00bd57219b0355ead400353e01d3061008a56c1035ad82001571fc2001551fc2001551fc200155040d6015b0a404d703a6052026b8e15c38570e15c38570e15c6b1cb9c1e004e1ac04b6320c5d40f00270f20f5b1ac1eb6320c5d480078015e336f0251602) else (if i < 18 then 0x6963eb1030e71f80c00450c291421f0000dae376f2c030de5a1c88a2f01a68287d1bb800aae0680c24053eba548370b80c00c4738fcc8170480c182b1d8006a121bba4da3200264906d74804649924384fa6d010d494375ba34024857b1c6a09368b5d4861b81d5ce9368dc04055bab81234780f5c2ab11b00640902264da00398e1d448570011a48738c9d485001215ea2000e15c004c92960ea729e000354c9286aae36b8c1299242dd123136921cae570ad10004119215eb7429b8da03 else 0x26054c039bcde521c8063705aa9c0180481134720580c5cf106915c0641700c00f11b85c1a0b09015d2de68aa4062e04909bc11598b456960c2c08ae952064187d443808ae97000c003022ac022ae76990b218000355e140200d54de10bc46e0074abc309a390000614701140cde622246e03000a824b006b79b07c02258247d05b79526d520dc10af58060da2f0582932450b81554590600010050735c6e17050bc06ed06b80b21700030060e02ad0f8642c8bc309d0200c281150291d2a4)) else (if i < 21 then (if i < 20 then 0x18041900d0ea61dba4f8053ea801a176f1c8140906021c0af02acc060c021c8da09019c86ede0683966de3200c240c700155eb32c82408de0500da20d582a8fa1102b18187201a1c24a474ad4fa6d050000ca01bba5487d368281807500dcfa0c001646ec50582406f14e819341859bc51e0b01805e4054d061bc3f0781c8a056f0301203620154018570dd66e95a1f4da000601d40371a830c83701800540a1babc22aa5e1cc08ae09a5012de391645c03002d408e00b835e2a42f8d41803 else 0xfa0d018086801578092409580a400f15300c0a4b5a84c060205ac1d2a64d0102499391f58a2e0681dbc340502404001881406e9050dc5209411b42607088615e780112022b373a98180a1bad8e602438288a11581b414095a0dc0eaf0882d0a32038015eee449fcde1f0139d24883902c00421d05c6203010016060018f816af789903e0c05011d2096d001400759a250c7f0582548314401d4c453785cfabd3f9f06ac5728340ea00e01062073e2c16837390c40e7d5b298621f3e80c7eb3) else 0x2445058100602068c824450e00c0405418dc240d250100602068c824451b8c8001206860f8351b834740301034644509290be391b8700432092d4180b0502404a0550600605418e56abd0581c1806582f5580a04a990c7202a740e6d4901c1ab0490c818af72824f00c77928640d583a524380600c12b0028dd5ed5368086e133e920040c1bac1aa6d01004f0373e920163202ac1e20a001e0de056d0e8163202ac0de2605828045a08b68740702ac00ef10c2f418021bac0da0c010dc6a77)) else (if i < 26 then (if i < 24 then (if i < 23 then 0x84a81caa408003e9154403470fc6aa9508606e05580edd2a81b0d40800580981018578dc08031c86160d7530d44c040082030e5370d40aa41da88fa2131288e429038182e690080c462f2485dce3b5128812112b885ba3d1e81ddea21282c04c5511687e3d4b8dc6405510fc767d1b814c8b7391b832c753290046a51b71a800068856ceb65220d41704b49446c000e87600090fd446210801e46a1ca8800f21da8c64351f8ed4c6e3229076a2358e10ab6023840699770e46eb60200c1a32 else 0x64a20f828de050095d9c392189096e57081472485101cde02520c9446f149880abd1cb84fa3503a816a7d11ad40e353badd6aa232188bc5a2c95c3002370bc08a04d290e40756a89409d240e832040180830127102c1c3970a8d021f01809449d1c83800af2b1506404010054e6e1cabc24a21ca9034a23782c06000104944e5448c406020f85024b03702dcaa2192bd7e370906090c81b84830480c0d46e3b0483c6a181ba9806010292030af74b5c2e08029186ea61a061c2051dba40803) else (if i < 25 then 0xeaf510081609779bddc570bb94fa033782d6a4a01005dae572af420c52d1b04c002d0e5dae50080088732c85c04e51bbb82e29013b5ca621407c2e0c05004b4d7672e400ed2b819caed218404c3f03bb890e50285c520276b94620c013b490f2321886e31170a04c230602c140901808bc5a1280400341c85cb2570289830ed7291002a6520e41e440c1804c0200bb8240776804620779001ca03501b96a031d9f144b4019f144034e1f0dc03008ecf8a237001cae112ad00ea2729bc049d else 0x47f09a648c274d04412370aaa4b8040180960422b8456c371480086b0208c4049d57394c8592b14ca00401808ae0b0480160aa079f556023eaacc21200004287d769f4de88120e470ae09044de7d380ed5a00011a556e53f010044a09051607d5b9b556481cb94de02428a472290b81c0006578a412005b05090075b0195ed23e82400b62424864af1b8d4ee4a760080234002bcdc00242d804155b009240a57bbd0e3504b9c72b072b85d4351902812157781d5e9d2b87c16091a8c808ee)) else (if i < 28 then (if i < 27 then 0xda35250dc6400358156c0c7704c049a1c9f80a32559b4188b240e5c27d368d494371f0d46e31358156c09558e46e861a8601e90738606277751906a37012c872ab082a5560f251141eab242d9a435000606e6f080a472350c0dc94120111960e5378242085148e40062148e41e0d292c10a02293c81e002a2b8240f291b1603707a648cb005800fe121b9a0180242a646ef2741f41259002746e02232c00485233c800671c8f1ca36780841e371f01560460111960851b8240a991cbc8f003 else 0x640809060c80c04808c4170b0fc1a3b018080a0d1911424170502400050881c00030881446090292890072d09814032200022e502815e2075eaece46d098340e095b0307cbd5e87062640581c1af10b1f0da2605824000c0201d7a6f07060e437788c40205091f4000a1b8481a05730dc16012404940064c940901636b98086212828c848320015605360117a0d03991ca6f428a472b6032ac180b0502430e5553a40cab148602099581bc20291cb94de85148e4de10148e4be001aad9c27d) else 0x2812040180802000100400030282812010000c0a0b048001a070200490160382c12040186052062500400292b81894100781c0a0c0200c00350c01c8a77060246a6403914ee682e1603002020441c03030544236008e41e183205c260c01140060d090140029018080205090e8281f098240204001280e02009642e000600c1c050c030160301014240e0387c0801))))
def hintVal (i : Nat) : Nat := field hintValD 9 170 i
def hintJ : Nat → Nat → Nat
  | 5 => hintJ5
  | 6 => hintJ6
  | 7 => hintJ7
  | 8 => hintJ8
  | 9 => hintJ9
  | 10 => hintJ10
  | 11 => hintJ11
  | 12 => hintJ12
  | 13 => hintJ13
  | 14 => hintJ14
  | _ => fun _ => 0
def hintRange (start : Nat) : Nat → List Nat
  | 0 => []
  | d+1 => hintVal start :: hintRange (start+1) d
def hints (s i : Nat) : List Nat := let start:=hintJ s i; hintRange start (hintJ s (i+1)-start)
end Pnp3229Certificate.PackedFront
namespace B.Zero3229.CoOracle
def slot (a : Nat → Nat) (bits i : Nat) : Nat := ((a (i/32)) >>> (bits*(i % 32))) % (2^bits)
def buckets (k : Nat) : Nat := (if k<16 then (if k<8 then (if k<4 then (if k<2 then (if k<1 then 0x4600b401000000808300460080000140208000 else 0x100000882200024000010000000420080011802a) else (if k<3 then 0x800008080004200000000002000050a0c000c21 else 0x1000000002000000080000401000040000000822)) else (if k<6 then (if k<5 then 0x60000000610040100004208001000000400 else 0x121800140008820008c00000011c6301c05) else (if k<7 then 0x1040100021024001000200023005611042000001 else 0x1000018406000310000248001000210140400042))) else (if k<12 then (if k<10 then (if k<9 then 0x5210a000000400000098c00008651840000860 else 0x1000108804000201802008041100204842012840) else (if k<11 then 0x8000806200c03280c0004000100028c40100e0 else 0x680220848068402020010802000c000800000004)) else (if k<14 then (if k<13 then 0x10c00004011800100c260808101c20080a0 else 0x884100020000a50000508801090030080001801) else (if k<15 then 0x61080400000b01c0218402284005040000000 else 0x2840000420008a00a8000004000022080e1)))) else (if k<24 then (if k<20 then (if k<18 then (if k<17 then 0x18820000000044001420000200000000ca000020 else 0x480200840000004008400840010c07108c000000) else (if k<19 then 0x6001000080000006020041000210000008000 else 0x1040014000a4031000000000085a00002310421)) else (if k<22 then (if k<21 then 0x2000000108810180108000100432040010400 else 0x800000800200000800008800008640000121861) else (if k<23 then 0x100020080020044208400008210000700c41 else 0x8000000000042002c0100003704000000003800))) else (if k<28 then (if k<26 then (if k<25 then 0x100000000100801104010080010c200040018020 else 0x520180a210c00100000a0040a4001200100406) else (if k<27 then 0x380000180000002080000000308460000c000c00 else 0x2000002001400800208021000611800100400)) else (if k<30 then (if k<29 then 0x4022008000861018a000400004020802100482 else 0x800010062114a00000048c06100011040000000) else (if k<31 then 0x8821080801800130021000c10140010c6200400 else 0xa120000004020002210400080600040000002)))))
def formIds (k : Nat) : Nat := (if k<64 then (if k<32 then (if k<16 then (if k<8 then (if k<4 then (if k<2 then (if k<1 then 0x230000000000cc0000000068850e169f2b0000e500258a000ba100710000 else 0xb3001f0000d00072fa00a10c0000f30000be00770b0e92e06c92c728a7cd0cc9) else (if k<3 then 0xf98cdd23000c56161700000000246600d500aeda002b1600b10d0000a12168 else 0xb4a800a24c000c2b692b8e1ee000000000880b00001600000000000000006c5c)) else (if k<6 then (if k<5 then 0xd00000000000000007fa2d1000000000b90b610a10000000000000000a20000 else 0x35c1f4cb2500000000f800000000000000000000000e006c000000395900) else (if k<7 then 0x6d0b000049000049a100003f00fb10a100000000b40d1da100 else 0xbfd00000000000088cd00281421cde86800120c0c586da1407e6c0c99680e00))) else (if k<12 then (if k<10 then (if k<9 then 0xa40c5e00007e786d0000145f680000e30fc6ec330000d31662c00b8ca20b0b5e else 0x7d000b1400003f000000ab2be11d680000000033160d0000250084a26700c000) else (if k<11 then 0xbf8e2b10a4231d000000000000000000008e4900190c0d000000000089000b00 else 0xb00f400e500430000220c0c0000000c0060b0004400a256a168a13f4da40c68)) else (if k<14 then (if k<13 then 0xb19b00000000c100006d0037916800da234a0068f3000000000014001b0000 else 0xe80b6c58001d00000000000000c7ce000000b023000000001900001468000000) else (if k<15 then 0xcb000000c0006800000000540000000c6971006800c617001000000000250d00 else 0x4110000000000c0000e5167e0074e00000000000c02b00d197)))) else (if k<24 then (if k<20 then (if k<18 then (if k<17 then 0x8c001ac000000000004bcd160066002100000000002a2b2bef000000c0000000 else 0x2e000000dd21006e212eaf9100a28ca1b58167160cb60016260e00007e678cd7) else (if k<19 then 0xba00008858210021000000cd0000000000f5242c400000003a84c900000b0000 else 0x6ce95b216c40eecd00b10c2b0000be000000000000a100000000000000006800)) else (if k<22 then (if k<21 then 0x68b2cc2b000cc00000000060fafbb0c0af4bc17bc00b10000000b1c600000000 else 0x2b2b191600000e001700a23900000000000e000000e7000000cb7e000c35c700) else (if k<23 then 0x160058140000008ccf180cc000350000007e0000b2402f00a1e300000000 else 0xb60bc1e41681000000e54b000000a5000000002100827200000000a100560c62))) else (if k<28 then (if k<26 then (if k<25 then 0x68686c0000230000230000b13fc0001000c7a42ba02bd38f14afaa0000f2de00 else 0x49e8009b005c0000ee0000a800002b002bcdc81800b400000000a2a100000000) else (if k<27 then 0x7b8da22fa1002bbe18b10e686811168c2b0c0000c10000363aa4c7ed49 else 0xbf3022a130dde3b0d356d68c0c2b1d2ba500000000b40000b0000b0000000000)) else (if k<30 then (if k<29 then 0x7ee37e68d2f3000000d30000a247000000ac000c8c21a600106100e000d90b0c else 0xb30d00162b2500940000002b001a0000a50000f38f00f3000000924d0000dd00) else (if k<31 then 0x25000000a200000000008c0c8ff6c400dd1d006860004928009c000000000000 else 0xdd0d0000da6ca200a44600ed007e00002c0000000000160b00d24900dd004d00))))) else (if k<48 then (if k<40 then (if k<36 then (if k<34 then (if k<33 then 0x8172be7ea1000000000000007b000000e510008f00000000000000e800dd5600 else 0xa019ee000000a1000000ee00b0b257007e00ae108f2800007e003cb29b000000) else (if k<35 then 0xe07f005700728c000c0063c97e00688d008fab0e189f1db400880000000000a0 else 0xba0000002bfab86c005d000000a40000000e7e0e000fb0a1d922cbbef30000)) else (if k<38 then (if k<37 then 0xe000000002b0000002b0000002e0c000000321f36004781000000 else 0x124600b43e001600991e000000000000e8008f0fc158005700000000dd57210b) else (if k<39 then 0x2b0018009500160058e3dab300000049140000000000a1c60000ab00160c007e else 0x7e0000ed000000008800d40000004914b212000000000000b558007b0e000000))) else (if k<44 then (if k<42 then (if k<41 then 0x3e1d00b36cb86cdd71422312bc001000003c68126b2100002b00a10000000000 else 0x478c7e000cf2000c007e6c00000000000000000000cd0e00000c0e7eb6c063a1) else (if k<43 then 0x56002300006c1d0c0c000058007e0c00000e000000d4160e00000000c0000000 else 0x127f0c7eb66c3e2138e89c1d23920ec1df2b0c00490e00ed581a006700008800)) else (if k<46 then (if k<45 then 0x211200cb5c00dd0068d300001df30000c1e04a00000e001b00c600367df9128c else 0x536200000000160000dd007ec61d00000000000c8700006100002b00da7e7c0d) else (if k<47 then 0xdd0cdd00e300000000000000000079000000008cdb00cb0c783b0028c700e000 else 0x2fdd4e6c000db60000bcc06c0000c400b247004d0e2f8c00000c000000da0000)))) else (if k<56 then (if k<52 then (if k<50 then (if k<49 then 0x7c00000000a16c8c1800c023bf7bc41200004000af0000a1001d6cc9da0d7e else 0xf00b1f31696dd00a10088421212f300000000002b2300a1280000001d22) else (if k<51 then 0xeedbda5c880000001700df000000183594000000000e351d00b60000000000 else 0x1247ad920014180000000000002bcbc917dad8dd0e0f00001d000b362e2b0f)) else (if k<54 then (if k<53 then 0xdd000078000e88008aa12b85e000000000002ea10000000021c000bb else 0x9500bca2740000001416000000000000b2009400004800000000fa12db00bb00) else (if k<55 then 0x720c0e2b00bff200a00000e000007000aac5210000da8c683800000000000000 else 0xa058000057e5001600d900000bee000000000000000c00000c0000d40cd1dd7b))) else (if k<60 then (if k<58 then (if k<57 then 0xe0bd8dc77002077a6db8cd2ba73607d8a72b761644400000000007200 else 0x8e7600c7001600000be5000000007d8c000000172b0e002bb4f33c) else (if k<59 then 0x21000000630b7e33280c000025d1db0094008c580e2b2f000000b5002bd40000 else 0x280000210000000000000cdb0c2b61f12b0c2b187eac58b04ccb000c930013df)) else (if k<62 then (if k<61 then 0x21f321008c00668fe510000000000000000000e50000000000000000000000 else 0x88000000cb2b003885f3000000e000008b0000000057e0000000230b) else (if k<63 then 0x490c5772dd005fe30d00006c00000000000000f3000000001f0012210066ed00 else 0xa26ce0722b0075c1e000f3e48ced1747910c8ca2140c12db0c7414000000)))))) else (if k<96 then (if k<80 then (if k<72 then (if k<68 then (if k<66 then (if k<65 then 0x19b61671c43c7f6700c10b77920000007e000c004e00570060b514a1008c else 0x99250044000000b10000000dcb23f3000edd2100ab000000000000a700) else (if k<67 then 0x36a7001600000000000d0018000b0000db6900000000002b001d008f49000000 else 0xfb7d00db000000491400f500000000860047400cb90018ccdb40c165000000)) else (if k<70 then (if k<69 then 0x8cb40000000071000000916c0000002b002b179b00002b000000a2cc00b400 else 0xe4ed002300528e710015741d00162f0000009200001a0e3100690000fa7b0000) else (if k<71 then 0xa98500b4dd3d0000007400006c1d000000000049000000b9002b0000c9000000 else 0x3340477e160c00002800b70ba76c0c5a00e400000089b400000000))) else (if k<76 then (if k<74 then (if k<73 then 0xb2b02d000000a6000000a200000000df00c0006900b6000000000b000000c6 else 0xf00e0084000000000067cd0000000b002e0000b2002300162100000e00000000) else (if k<75 then 0x210000000b7e001600000000e5f50c0000db0000003f000000000000a00d0024 else 0xc057b60000dea1e3427e140000000000b3e01800e0a22218248a8e0c1d000e)) else (if k<78 then (if k<77 then 0xbdd7dda400033009b5f0000000e9d00005000161d6900b6a200000000 else 0xdbf371740000430000b44e7f00000eb1009db7da7a00bf160034c1af00000000) else (if k<79 then 0xd7f5b200dd107e0000da0d0000000000000027000c0000008c00b621000d else 0xa1f4004928009b1016f2cf0000c600e5000b0000004c00600c84000000000000)))) else (if k<88 then (if k<84 then (if k<82 then (if k<81 then 0xc6fa00b100000000006700001b0000580088c00010dc006956000000000000 else 0x8c0085c00019000000000000d71200730023c09800000000b2002b0ee300) else (if k<83 then 0x1900000d21fb0000000000008f0d0000007e580000884f0e00c00000000000 else 0x990000000000a200160b001400004c0000212368008d3f4900008457382b0000)) else (if k<86 then (if k<85 then 0xdb0000005900662300000000000b001000002bd82b0000178cda000000884600 else 0xdb0000000000a2a10c850c00002b5c00585700a00ddfa2db00000ea20000ef00) else (if k<87 then 0x57000000fb007eb1000e0ca2c90c1600c40c160000001f00a26c001dc7c0a500 else 0xc47ee400cd00000051000c002b99000ca4cb0b67c0350088007e0049000000))) else (if k<92 then (if k<90 then (if k<89 then 0x3bd12b00000049a000910000a06c0e006c6cc700590000000000004de5e00b21 else 0x2b2b2b00d4000000da330000eae3000bf300346828411a10000016000055) else (if k<91 then 0x8d00000000004962006747ddc0496ca500880000d100000000b1000000002f else 0xc147b492a200490000da0000000000882e002f8ce823a16c0ed2000c0c9d0c)) else (if k<94 then (if k<93 then 0xa400147a100000004900000000c700000c856c6e8d33392bcb00b3000e7c0000 else 0x10000e007e0000000000c70000b1e0bf0000c77e357e0c9b0e1c) else (if k<95 then 0xdb00000000720c4a22490000000016009b0000000000c9bf00b2b435000014 else 0x710000000000001600003572006c1d00000e16976888284c0000000c71140000))))) else (if k<112 then (if k<104 then (if k<100 then (if k<98 then (if k<97 then 0x21000e0000a600000000c1d800000000000000000000887e00000000004ec600 else 0x570000a122b50000007e99dddd00000000a10000426e1200ea00ba00007e3500) else (if k<99 then 0x16a2880e58160000215700e2000b570000a20000da0000ca00a8557b else 0x57dd00993000000e00000000cb000080000c7a00a121000cc30037000000dd)) else (if k<102 then (if k<101 then 0x947b18a200000000b400da120b0000bf000000000049f3b44900000e00 else 0x1721e8462312a100007221002200cd0e180058d0002ba42c0e00) else (if k<103 then 0xbb0000000085000c0000000000005700000000160000dd000000000000 else 0x1068465757001d00b43537003c00e300005888b000bc49350080a08c000f0000))) else (if k<108 then (if k<106 then (if k<105 then 0xe3dd21b400000e1668000c60da1d920000dae192c91600001600000042210000 else 0xa40000160000101ed4b41d0f00000000001d00330071000c0000000000000017) else (if k<107 then 0x3b002ba0a50000581a00d300bf210c1400e3000b00e500000000cbe1000c00 else 0xe000000057daaf0ee0cb299fc70000490000f20000a5000000002b0ca1a18cdd)) else (if k<110 then (if k<109 then 0xe4d0c5800000b008a0010dd126800c0000000000b000000008c007e0000dd17 else 0xe0000000c00000da4e800000040009e63a23f1b68c9a58cd3000cc068b500f5) else (if k<111 then 0x49001800000000008c0d6868220022496d16e0bdf239000c000000c0000000 else 0x129f7100000000000000186c1d1b000000c900005236dba2f200003557788c)))) else (if k<120 then (if k<116 then (if k<114 then (if k<113 then 0x12e3920e6bddf3742b0000b6285ff312dd166700000000e09b008c0000147800 else 0xb000a2e4a1000e221988000c001d97670000e85700000000002316d90cba1dcf) else (if k<115 then 0xcfa00b1000f000c71a100ba0000004900001649007b100000001200ba7f else 0xc10c6dcb0ea41d39b60072ea0000002300004700004168007bcb350000352b8c)) else (if k<118 then (if k<117 then 0x2c0000570000000b00000000a1000000004e0b00cc00000c0000008ca15d4d else 0xc900d900007d680b0000001221000b12e28800ed0000680e1dd800000000) else (if k<119 then 0x2b250000000035000ca1128e00000000000000490000000000000000c6ddedc9 else 0xa48c00de00000016000000850078006c00560000006800dddb0022000000))) else (if k<124 then (if k<122 then (if k<121 then 0xdd57c73f0e00000000c10f00c67339910000000b00a1ba0000c7c0 else 0xd1000000000000004c7200000076250e0000a100e01600350068000c68000000) else (if k<123 then 0x21a16056a82b0ee02100000c68889a5857970000ad6772491225000000000016 else 0xe2d32b490c008e0068000063f300bb009f880000e70000698c37438c2b)) else (if k<126 then (if k<125 then 0x77b000f800006900000000000068688ab1008aa70c6814d3925716dac60049 else 0xc72c00000e25000e7d00b500a48300910021004d0b000000000000680062d300) else (if k<127 then 0xe17d00000dd7e0c6935003f0b7200e4b14967dd0055161df500000000b6e3 else 0x2ab30021000012000000000000000000000000004d0000dd0000d6000000)))))))
def dictionary (q : Nat) : Nat :=
  let hn := ((q*2654435761) % 4294967296) >>> 22
  let hh := (((q ^^^ (q >>> 11))*2246822519) % 4294967296) >>> 20
  slot formIds 8 ((hh+slot buckets 5 hn) % 4096)
def facts (k : Nat) : Nat := (if k<4 then (if k<2 then (if k<1 then 0x6000108c000209000040500004a8000086c000109800020a0000406000042800008280000d3000018800002480000420000052000008600000c8000011800001a00000240000027c03400e7014010dc44020374406a480608348861314086304608655100c47fffff8000000 else 0x60d221b010001e01a822301be208037648c06ec8180dd50301ba606037449006e88d80dd11301ba2180200470024a1200481c3000c006001200c00208200040840008024001000c0014018002202000400a0005214000a2180014030002204000400c0004110000804000086) else (if k<3 then 0x824a00b443c09a886952410d024820e0450410a8187ffb620fd54c41bfcc0c37310186e26050dc46381b88c2c37118206e22c40dc44661b8889037110d86e22130dc441818018501eecb903dd96506990e60d3218c1a54320348c7306918c60d2298c1a44b2034887b06910e else 0x8ada27e95b44f52afd18d5448336a89062d5110c5aa2118c5441356a8826315102d62a2059b5440b16a880e2d5100d5aa2019c50912087fffdccff57399eff7323dc4c666ff75d0df66391be8c7231faa6662910ccc5121998a0c343140c7662818d0c5029d98a0533314087)) else (if k<6 then (if k<5 then 0x7046886e08c90e4118a3b8231437046186e08c18dc11823c8202219021005200041abfffffc7fd5ff8fbfdeedf713de3bfddfd77d9bf6efa37edd7eade3aa45ba7540b78bffefad7f55f5aeff38a5dc471ab881e755fecfdabfd9ec56d93d8adaa7b55b46fe2b68dec56d17d else 0x79c1500f381a01e701c03ce02c099c0506f380a09def26f3bb70df773f57cae58279d9fd73ab370c755bc8b0eaee9ed55982daa9ba3875250312a48471d4908c5a9203b9524072ea480e254900dba9201a7524032e3ff98d47fa21b87bb6f90d729ea1ac53d41dd31b823843) else (if k<7 then 0x7e77ec6fcdf71d791ea1bf1ffa65e37e40bc53619f806c03f00d409e01a42fc03481f806824f00d037e01a04fc0340577914c3dfc6f19bde7ff77b4efdef69debde72f35bc856375be5fdeb78bfcd670775ace0e6b3f1b01e7dd71acfbaa079d679f33a4e396749c62ce32c3 else 0x27fe9dfbffd38e7fe856ebfd0a1aff7fffcfedfbd9fd7f9effa7e31ff27d8bfe3fc35fc1f00bf735027eb6dfbfd60bf5fac072fe5b6797c968c4f7ddbf7efbb1d3dbf5fefb6e9fbf6dd3d7ed7a9f3da74397b4e863f67d737ea9b6f3d134d67a2699af44d31)))
def recipes (k : Nat) : Nat := (if k<4 then (if k<2 then (if k<1 then 0x73c2b000071c2b00000072b62c1b43bc0062c0c1b000062c1b000060c1b00000061b000051c0b00000050b30c4b21bc000030c4b0021b40bc00000040b0043b21bc00000043b000031c2b00000032b000020c1b00000021b00000010b00000000800000000700000000600000000500000000400000000300000000200000000100000000000000000a000000009 else 0x10b3c0031c20cb0063c21cb000086b5c0082c3b5c000083b5c000072b5c000061b5c000032b5c0020c1b5c000021b5c000010b5c0051c20cb0073c52cb0054c30cb000065c8b000053c8b000080c5b0085b40bc0085b21bc00000085b000063c8b000081c6b00000086b52c7b40bc52c7b43bc000052c7b000070c5b00000075b000082c3b00000083b0073c1c2b) else (if k<3 then 0x21c30cb31c0c52cb73c0c52cb0052c30cb0052c10cb0052c70cb000065c3c00000063c00000065c000085b6c000072b6c51c20cb6c0051c0b6c000050b6c0030c4b6c0031c2b6c000032b6c0020c1b6c000021b6c000010b6c0062c71cb0021b5c3c00000053c85b21bc3c000085b3c000086b3c0071c2b3c000072b3c000061b3c000050b3c0020c1b3c000021b3c else 0x21b3c0c00000030c00000050c85b21bc0c000085b0c000086b0c000075b0c0082c3b0c000083b0c0073c2b0c0071c2b0c000072b0c000061b0c000032b0c000021b0c0085c30cb0065c3c2c000063c2c000065c2c00000062c000053c2c0085b3c2c00000032c00000052c000085b2c000086b2c000083b2c0060c1b2c000061b2c0051c0b2c000050b2c000010b2c)) else (if k<6 then (if k<5 then 0x86b1c000075b1c0082c3b1c000083b1c000072b1c000050b1c000032b1c0051c70cb0082c51cb0082c31cb65c3c2c0c0063c2c0c0065c2c0c000062c0c0053c2c0c85b3c2c0c000032c0c000052c0c0085b2c0c00000020c0065c3c0c000063c0c000065c0c00000060c62c71cb0c21b5c3c0c000053c0c0085b3c0c0086b3c0c71c2b3c0c0072b3c0c0061b3c0c else 0x85b7c000086b7c000083b7c000061b7c0020c1b7c000021b7c000064c2c000042c1c000054c2c00000042c000052c1c00000021c00000064c000054c1c00000041c00000054c000085b4c0082c3b4c000083b4c51c20cb4c0051c0b4c000050b4c0020c1b4c000021b4c000010b4c000065c1c00000061c000053c1c0085b3c1c00000031c00000051c000085b1c) else (if k<7 then 0x85c1c000082c1c00000081c000085c2c00000085c00000082c000072b8c000061b8c0051c0b8c000050b8c000032b8c0020c1b8c000021b8c000010b8c00000074c000076c0c0073c1c0c21b7c3c0c000073c0c000071c0c00000070c85b3c1c0c000031c0c0032b1c0c00000010c00000076c000075c1c00000075c000073c1c0021b7c3c00000073c00000071c else 0x73c2c0c000073c2c000072c0c00000072c87c3c1c0c0087c3c0c0087c3c1c000087c3c000087c0c000087c1c00000087c00000086c0084c2c0c000042c0c00000040c000084c2c00000084c0083c2c0c000083c2c0083c1c0c21b8c3c0c000083c0c000083c1c0021b8c3c00000083c000081c0c000082c0c0032b8c0c0021b8c0c00000080c)))
def numForms : Nat := 254
end B.Zero3229.CoOracle
namespace B.Zero3229.CoOracle
def parse : Nat → Nat → Menu × Nat
  | 0, n => (.lit false,n)
  | fuel+1, n =>
    let d := n % 16
    let rem := n / 16
    if d < 9 then (.var d, rem)
    else if d < 11 then (.lit (d == 10), rem)
    else
      let (a,k) := parse fuel rem
      let (b,r) := parse fuel k
      (.gate (d == 12) a b,r)
def recipe (i : Nat) : Menu := (parse 6 (slot recipes 36 i)).1
def fact (i : Nat) : Nat := slot facts 27 i
def factWord (i : Nat) : BWord := BitVec.ofNat 24 (fact i)
def factPrice (i : Nat) : Nat := (fact i) >>> 24
def coherent (i : Nat) : Bool :=
  factWord i == word (recipe i) &&
    factPrice i + (if (recipe i).literal then 1 else 0) == (recipe i).size + 1
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem facts_checked : (List.range numForms).all coherent = true := by decide +kernel
def needCode (c : Chart) (w : BWord) : Nat :=
  ((w ^^^ 0xfff000) &&& c.active).toNat
def chooseRaw (c : Chart) (w : BWord) (fallback : Nat) : Nat :=
  if safeB c w 0x544031 then 2 else if safeB c w 0x823043 then 3 else
  if safeB c w 0x314086 then 4 else if safeB c w 0x06910c then 5 else
  if safeB c w 0xa92018 then 6 else if safeB c w 0x01ba20 then 7 else
  if safeB c w 0x0dc440 then 8 else if safeB c w 0xce0280 then 9 else
  if safeB c w 0xf00d00 then 10 else fallback
def choose (c : Chart) (w : BWord) : Nat :=
  let q := needCode c w
  if q % 4096 == 0 then 0 else if q < 4096 then 1
  else chooseRaw c w (dictionary q)
def price (c : Chart) (w : BWord) : Option Nat :=
  let i := choose c w
  if i < numForms ∧ safeB c w (factWord i) = true then some (factPrice i) else none
def weight (c : Chart) (w : BWord) : Int :=
  match price c w with | none => 63 | some n => (n : Int) - 1
def total (c : Chart) : List BWord → Option Nat
  | [] => some 0
  | w::ws => do
    let a ← price c w
    let b ← total c ws
    return a+b
theorem total_sound {c : Chart} {ws : List BWord} {n : Nat} (ok : total c ws = some n) :
    ∃ es : List Menu, menuListOK c ws es = true ∧
      n + es.countP Menu.literal = (es.map Menu.size).sum + ws.length := by
  induction ws generalizing n with
  | nil => exact ⟨[],rfl,by simpa [total] using ok.symm⟩
  | cons w ws ih =>
    cases pv : price c w with
    | none => simp [total,pv] at ok
    | some a =>
      cases tv : total c ws with
      | none => simp [total,pv,tv] at ok
      | some b =>
        have hn : a+b=n := by simpa [total,pv,tv] using ok
        unfold price at pv
        dsimp only at pv
        split at pv
        next valid =>
          have factOK := List.all_eq_true.mp facts_checked _ (List.mem_range.mpr valid.1)
          simp only [coherent,Bool.and_eq_true,beq_iff_eq] at factOK
          have pe := Option.some.inj pv
          obtain ⟨es,he,sz⟩ := ih tv
          refine ⟨recipe (choose c w)::es,?_,?_⟩
          · simp only [menuListOK,Bool.and_eq_true]
            exact ⟨factOK.1 ▸ valid.2,he⟩
          · simp only [List.countP_cons,List.map_cons,List.sum_cons,List.length_cons]
            have hh := factOK.2
            split <;> split at hh <;> first | contradiction | omega
        next => contradiction
def chartCut (c : Chart) (ws : List BWord) (cap : Nat) : Bool :=
  match total c ws with
  | none => false
  | some n => decide (n + cap < c.L + ws.length)
theorem chartCut_sound {c ws cap} (cv : Valid c)
    (lb : ∀ p bs, Reach c.roots p bs → Available bs c.G → c.L ≤ p)
    (ok : chartCut c ws cap = true) {k} (hk : k ≤ cap) : ¬MRun (bt target) k (ws.map bt) := by
  unfold chartCut at ok
  cases h : total c ws with
  | none => simp [h] at ok
  | some n =>
    simp only [h,decide_eq_true_eq] at ok
    obtain ⟨es,valid,sz⟩ := total_sound h
    exact denied cv lb es valid (by omega)
end B.Zero3229.CoOracle
namespace B.Zero3229.CoOracle.Lite
def chartInfoChunk (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0x9a33b8e098d62f309cd2e7109a1bd4e09af05ce09ad8f8c09b16c7308a92ec208992ec20bf51bbc0bb5393f0b8772bf0b9732bf0bf58bbc0bc5bd790b95dd670bd71ba70bb7455f0b95bd790ccfbf790c8ff2ff0cff45df0cfdcfbc0ba79fc60b979fc60bd55ee30bd56ee30cfd6ef30cafbfce0dd7dfe70db5fd7f0df73bbf else 0x7916c6107658b8407531b84071722a307a31b8407551b8407538b8407951b8407949c6107d112a3089645c608a645c6089705c608558f8408658f8408c52c7108916c7108c16c7108a19d4608915c6308916c6308952c71080752e308d122b3089522b3080762e308a1954e088552e308a31b8c08a58b8c08931b8608a51b8c) else (if j<3 then 0x85445b508b6009f08ce05590815303f0805705f0807605f08cc15590835193c080dc2bc09f6019f09cd8f38090dc6bc0905f07f090dc2fc09ce05d90935cd3c098f40df09ce07590a0dc6fc0ace07d907a1954607558b840792c5460796454607a70546071712a307c49c610790dc6107c52c6107c0dc6107c0ec610790ec61 else 0x71445350706936907869f400781bd48075445b4075445a507544595075401b50794a938078f00ce07cd0e30078d40d3078d8f0807f10ab007ad058c078d2271070792c60783328e07d444c3073589380706926d07a1390e0765193807a4501f0717201f088fb2ce08fd4eb008c43b3808fd44d308358d380806936d088fbf48)) else (if j<6 then (if j<5 then 0x554018505144524051445140554458405650e8005049069050612290506926105a11a8205049161050613210514450505892e4005550e80065401a50604906d06544594065445a40606122d0606926506069269060693610606132906049169065401b406540195061445150614452506544585061445340704916d0706132d else 0x6a2018e07823b4a0735451c07314cb207f4019c07f00c930705d0670701ba4e0490444204448e0004809c400480ac4004450e0004490e0004848e00041445040454018404061221040700c2048440c2040640c20404906104890e00048900c20481228204a104420403228204812c400481128204031282055401a405540194) else (if j<7 then 0x4038284040542a00501506305b00813050582c405114c22050542e0053108b005114ca00580394805821b400501380e05823b080592018605310832050546a005118d04050192460601b24e06019a46060546e006013a0e06823b4806821b420680394a06314cb006114ca2063108b20601607306f0049306314c3206d00c83 else 0x410cc20045102a00442122104448c200400d0460400d0610402c04604b000130442408304421b0004821b0004441b00048605400410c5040420c50404031284048285400452018404310830)))
def chartInfo (i : Nat) : Nat := ((chartInfoChunk (i/32)) >>> ((i % 32)*32)) &&& 0xffffffff
def isRaw (q : Nat) : Bool := (q &&& 0x544fce == 0) || (q &&& 0x823fbc == 0) || (q &&& 0x314f79 == 0) || (q &&& 0x69ef3 == 0) || (q &&& 0xa92fe7 == 0) || (q &&& 0x1b5df == 0) || (q &&& 0xdcbbf == 0) || (q &&& 0xce0d7f == 0) || (q &&& 0xf002ff == 0)
def feeQ (q : Nat) : Nat :=
 if (q &&& 4095 == 0 || q &&& 0xfff000 == 0) then 0
 else if isRaw q then 1
 else
   let j := dictionary q
   let d := fact j
   if j < numForms && (q &&& ((d &&& 0xffffff) ^^^ 4095)) == 0 then d >>> 24 else 64
def numFee (active w : Nat) : Nat := feeQ ((w ^^^ 0xfff000) &&& active)
def numSum (ac : Nat) : List BWord → Nat
 | [] => 0
 | w :: ws => numFee ac w.toNat + numSum ac ws
def fits (q : Nat) (v : BWord) : Bool := (q &&& (v ^^^ target).toNat) == 0
theorem fits_iff (c : Chart) (w v : BWord) : fits (needCode c w) v = safeB c w v := by
  have ht : ~~~target = (0xfff000 : BWord) := by decide
  have eq : ((~~~(w ^^^ target)) &&& (v ^^^ target)) &&& c.active =
      ((w ^^^ (0xfff000 : BWord)) &&& c.active) &&& (v ^^^ target) := by
    rw [BitVec.not_xor_right,ht]
    rw [BitVec.and_assoc,BitVec.and_comm (v ^^^ target) c.active,←BitVec.and_assoc]
  simp only [safeB,eq,needCode,fits,← BitVec.toNat_and]
  rfl
theorem raw_hit (q : Nat) (h : isRaw q = true) :
    ∃ i : Nat, fits q (word (.var i)) = true := by
  simp only [isRaw,Bool.or_eq_true] at h
  rcases h with h|h
  · rcases h with h|h
    · rcases h with h|h
      · rcases h with h|h
        · rcases h with h|h
          · rcases h with h|h
            · rcases h with h|h
              · rcases h with h|h
                · exact ⟨0,h⟩
                · exact ⟨1,h⟩
              · exact ⟨2,h⟩
            · exact ⟨3,h⟩
          · exact ⟨4,h⟩
        · exact ⟨5,h⟩
      · exact ⟨6,h⟩
    · exact ⟨7,h⟩
  · exact ⟨8,h⟩
set_option maxRecDepth 4096 in
theorem usable {q j : Nat} (hb : j < numForms)
    (hc : (q &&& ((fact j &&& 0xffffff) ^^^ 4095) == 0) = true) :
    ∃ e : Menu, fits q (word e) = true ∧
      factPrice j + (if e.literal then 1 else 0) = e.size+1 := by
  have f := List.all_eq_true.mp facts_checked j (List.mem_range.mpr hb)
  simp only [coherent,Bool.and_eq_true,beq_iff_eq] at f
  refine ⟨recipe j,?_,f.2⟩
  rw [←f.1]
  change (q &&& ((factWord j) ^^^ target).toNat == 0) = true
  rw [BitVec.toNat_xor]
  change (q &&& ((factWord j).toNat ^^^ 4095) == 0) = true
  have cert : (fact j &&& 0xffffff) = (factWord j).toNat :=
    Nat.and_two_pow_sub_one_eq_mod (fact j) 24
  rwa [←cert]
set_option maxRecDepth 4096 in
theorem feeQ_sound {q : Nat} (low : feeQ q < 64) :
    ∃ e : Menu, fits q (word e) = true ∧
      feeQ q + (if e.literal then 1 else 0) = e.size+1 := by
  have lit (v : Bool) (h : fits q (word (.lit v)) = true) (t : feeQ q = 0) :
      ∃ e : Menu, fits q (word e) = true ∧ feeQ q + (if e.literal then 1 else 0) = e.size+1 :=
    ⟨.lit v,h,by rw [t]; rfl⟩
  by_cases hp : (q &&& 4095 == 0 || q &&& 0xfff000 == 0) = true
  · have t : feeQ q = 0 := by simp only [feeQ,hp,ite_true]
    rcases (Bool.or_eq_true _ _).mp hp with h|h
    · exact lit false h t
    · exact lit true h t
  by_cases hr : isRaw q = true
  · have t : feeQ q = 1 := by simp only [feeQ,if_neg hp,hr,ite_true]
    obtain ⟨i,hi⟩ := raw_hit q hr
    exact ⟨.var i,hi,by rw [t];rfl⟩
  let j := dictionary q
  by_cases h : (decide (j < numForms) && (q &&& ((fact j &&& 0xffffff) ^^^ 4095) == 0)) = true
  · have eq : feeQ q = factPrice j := by simp only [feeQ,if_neg hp,if_neg hr]; exact if_pos h
    have H := (Bool.and_eq_true _ _).mp h
    rw [eq]
    exact usable (of_decide_eq_true H.1) H.2
  · have eq : feeQ q = 64 := by simp only [feeQ,if_neg hp,if_neg hr]; exact if_neg h
    omega
theorem rawEq (c : Chart) (w : BWord) : numFee c.active.toNat w.toNat = feeQ (needCode c w) := by
  simp only [numFee,needCode,BitVec.toNat_and,BitVec.toNat_xor]; rfl
theorem sum_good {c : Chart} {ws} (h : numSum c.active.toNat ws < 64) :
    ∃ es : List Menu, menuListOK c ws es = true ∧
      numSum c.active.toNat ws + es.countP Menu.literal = (es.map Menu.size).sum + ws.length := by
  induction ws with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons w ws ih =>
    change numFee _ _ + numSum c.active.toNat ws < 64 at h
    have small : numFee c.active.toNat w.toNat < 64 := by omega
    obtain ⟨e,ok,e0⟩ := feeQ_sound (rawEq c w ▸ small)
    obtain ⟨es,oks,hs⟩ := ih (by omega)
    refine ⟨e::es,?_,?_⟩
    · exact (Bool.and_eq_true _ _).mpr ⟨fits_iff c w _ ▸ ok,oks⟩
    · change (numFee c.active.toNat w.toNat + numSum c.active.toNat ws) + (e::es).countP Menu.literal = _
      simp only [List.countP_cons,List.map_cons,List.sum_cons,List.length_cons,rawEq]
      clear h small ok oks
      cases hl : e.literal <;> simp only [hl,ite_true,ite_false,Bool.false_eq_true] at e0 ⊢ <;> omega
def ciOK (i : Nat) :=
 let inf := chartInfo i
 (inf &&& 0xffffff) == (chart i).active.toNat && (inf >>> 24) == (chart i).L
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem allCI : (List.range 243).all ciOK = true := by decide +kernel
def quickCut (i : Nat) (ws : List BWord) (cap : Nat) :=
 let info := chartInfo i
 let n := numSum (info &&& 0xffffff) ws
 decide (i<243 ∧ n<64 ∧ n+cap < (info >>> 24)+ws.length)
theorem quickCut_sound (i : Nat) {ws : List BWord} {cap : Nat}
    (h : quickCut i ws cap = true) {k : Nat} (hk : k ≤ cap) :
    ¬MRun (bt target) k (ws.map bt) := by
  simp only [quickCut,decide_eq_true_eq] at h
  have H := List.all_eq_true.mp allCI _ (List.mem_range.mpr h.1)
  simp only [ciOK,Bool.and_eq_true,beq_iff_eq] at H
  have norm : numSum (chart i).active.toNat ws < 64 := H.1 ▸ h.2.1
  obtain ⟨es,valid,sz⟩ := sum_good norm
  have small := h.2.2
  rw [H.1,H.2] at small
  exact denied (chart_valid i) (chart_low i) es valid (by omega)
end B.Zero3229.CoOracle.Lite
namespace Pnp3229Certificate
namespace Project
open PEqualNP.Outside.L_meta_3229.B (MRun Wire combine)
def observe (a : Sig) : Wire (Fin 24) := fun r => bit r a
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = PEqualNP.Outside.L_meta_3229.B.kept d (f a) (l.map f) := by cases d <;> rfl
theorem list_mrun {T : Sig} {k S} (h : Live T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : MRun (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact MRun.perm (eq.map _) MRun.stop
  | @binary k U a b d ha hb hab fresh _ ih =>
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
    change MRun _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact MRun.perm (perm.map _) (MRun.two d ka kb progress)
end Project
end Pnp3229Certificate
namespace Pnp3229Certificate.Project
open PEqualNP.Outside.L_meta_3229.B.Zero3229 (Chart Valid)
open PEqualNP.Outside.L_meta_3229.B.Zero3229.CoOracle (chartCut chartCut_sound)
theorem chart_impossible {c : Chart} {ws : List Sig} {cap : Nat}
    (cv : Valid c)
    (lb : ∀ p bs, PEqualNP.Outside.L_meta_3229.B.Reach c.roots p bs →
        PEqualNP.Outside.L_meta_3229.B.Available bs c.G → c.L ≤ p)
    (cut : chartCut c ws cap = true) (nd : ws.Nodup) : Impossible goal cap ws.toFinset := by
  intro k hk run
  exact chartCut_sound cv lb cut hk (list_mrun run ws nd rfl)
end Pnp3229Certificate.Project
namespace Pnp3229Certificate.PackedFront
def t5wD (i : Nat) : Nat := 0x1
def t5A (i : Nat) : Array Nat := #[0x0]
def t5D (i : Nat) : Nat := (t5A (i / 16))[i % 16]?.getD 0
def t6wD (i : Nat) : Nat := 0x49
def t6A (i : Nat) : Array Nat := #[0x0,0x0,0x0]
def t6D (i : Nat) : Nat := (t6A (i / 16))[i % 16]?.getD 0
def t7wD (i : Nat) : Nat := 0x124a
def t7A (i : Nat) : Array Nat := #[0x25,0x0,0x0,0x0,0x0]
def t7D (i : Nat) : Nat := (t7A (i / 16))[i % 16]?.getD 0
def t8wD (i : Nat) : Nat := 0x9249249452
def t8A (i : Nat) : Array Nat := #[0x625,0x191,0x3,0x5565655555,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3]
def t8D (i : Nat) : Nat := (t8A (i / 16))[i % 16]?.getD 0
def t9wD (i : Nat) : Nat := 0x9124924a4524492492922c944929244a491251492249
def t9A (i : Nat) : Array Nat := (if i<2 then (if i<1 then #[0x3,0x3,0x3,0x3,0x6,0x55961,0x9,0x6191,0xfff,0x19164,0x1,0x1,0x0,0x95,0x94,0x9] else #[0x55554956555555,0xffff,0xff,0x24,0x6555,0x2155515,0x1e5555,0x3,0xff,0x8,0x0,0x8555955545,0x1fe,0x2,0x1a311,0x0]) else (if i<3 then #[0x9,0x164,0x1595555556664,0x1,0x6,0x0,0x0,0x0,0x0,0x0,0x0,0x6,0x1e,0x9,0x3,0x55565557555] else #[0x56559,0x1,0x0,0x12,0x2,0xe,0x0,0x5,0x2,0x6,0x25]))
def t9D (i : Nat) : Nat := (t9A (i / 16))[i % 16]?.getD 0
def t10wD (i : Nat) : Nat := (if i<2 then (if i<1 then 0x4926932524924924924924d229249249249349349249149249248949229249249249a691452 else 0x49249249249249245249249249249a6d24922ca44a49249248948a49248a44a49b4924da8da) else 0x116d24524db4924db45249224969249249249248a2d1)
def t10A (i : Nat) : Array Nat := (if i<9 then (if i<5 then (if i<3 then (if i<2 then (if i<1 then #[0x1555556755655,0x1555555555955,0xfffffff,0x15555555955d65,0x1fffff,0x55556559555,0x655555559,0x52261619049048248,0x555695555,0x24924924925924925124925124924b24a24925265164924988a451,0x15555956755,0x1555d5565555,0x6555595555,0x15d56555555656,0x5555555559,0x5555555659] else #[0x155555595955,0x15555555599,0x565555655555,0x255655555555,0x55556555565555,0x5556655555,0x6555555596555,0xf,0x595555,0x1595655,0x6555,0x5555569557,0x1,0x3,0x155a55,0x1959655]) else #[0x19555955,0x15555995,0x15795555,0x1555645,0x1555645,0x1555645,0x1555645,0x1555645,0xfff,0x16,0x9,0x6,0x15556,0x565566d,0x2555556,0x1a555d55]) else (if i<4 then #[0x8b402202841,0x265,0x1555545695,0x55715585,0x4924924825124924924925124926824b24928a4494d1249852251291,0x655595565555,0x9565551555b5,0x555556d6,0x5555586,0x5555586,0x5555586,0x5555586,0x1555c59655,0x6164564,0x95665555555,0x59565555] else #[0x655d9555555556,0x59,0xa5,0x3,0x193,0x5559551,0x9261291249258,0x166659d595555,0x1a5,0x55555995,0x569555555,0x55556655,0x55556655,0x55556655,0x55556655,0x15a5755555])) else (if i<7 then (if i<6 then #[0x155755599,0x557556655,0x55556655,0x55556655,0x555655567955,0x55555655595b555,0x1655,0x979,0x15b,0x5565966577,0x3,0x3,0xa660,0x559555,0x259595d,0x9289449649251261252] else #[0x15555566,0x555d655555,0x65555555556,0x265559155955,0x5555d6975995,0xa449c8024230720aa090d1,0x51459249249261249249a59,0x121513231231312712111132111011131122211812301911331501161411411422111113321011211,0x1995555597555,0x34920b24924c249651251249289249,0x20964d081049209241049849441,0x1571a55555455549,0x19911d5555555555565,0x999555555655d5,0x655555657555,0x66d54555545]) else (if i<8 then #[0x24925124b261249,0x458a91248989440041,0x155555555695596,0x995,0x1555556695559555d,0x0,0x38,0x6500,0x16555646518,0x8,0x55525555555559664,0x15555555555a4,0x555555664,0x5555155585,0x1995555558,0xd9555165555c] else #[0x7655565555c,0x1e,0x9d5555575596558,0x5555555558,0x1f,0x6,0x35a4,0x940,0x24,0xe50,0x5d5555598,0x55d5515665,0x1554555658,0x15555658,0x755555958,0x168]))) else (if i<13 then (if i<11 then (if i<10 then #[0x155555964,0x10,0x0,0x15555555455961,0x555555458,0x4,0x10964a263290,0x0,0x52,0x19,0x16,0x6,0x16,0x172,0x988b,0x25228924b249249249850] else #[0x555555d559565,0x319291249248,0x6695d4551,0x760,0x5e66575550,0x156555556d5559,0x15655555795559,0x1659555556d555,0x255,0x5555955555,0x55555655555,0x55556555555,0x5555955555,0x5555955555,0x5955555555,0x5556555555]) else (if i<12 then #[0x55565555555,0x1555915,0x3,0x5555616,0x1555d6555555,0x155575955555,0x5555d6555555,0x5555955555,0x55556555555,0x555d655555555,0x551555655555d555,0x16555555755,0x15556555665556,0x1575655655955,0x15756556559555,0x1575565595555] else #[0x1595,0x9d55515645,0x595515645,0x16,0x17555595555,0x155d5595555,0x15575595555,0x155556556565559555,0x7ffff,0x5555575559a5555,0x30949d,0xf,0x159,0xf,0x5556655759555,0x55599955d5555])) else (if i<15 then (if i<14 then #[0x969555655556655,0x5565665559555,0x5665559565555,0x5566557559555,0x56655555559,0x56556555559,0x66555755555,0x56555765555,0x65556655555,0x55566555559,0x5555655555,0x55555995,0x1555915,0x1555555556955,0x5565556559,0xe64924a28b442843a49252] else #[0x0,0x64,0x0,0x22,0x5e516855,0x25,0x55615761d9,0x5561791e5,0x184,0x918,0x3,0x1c9,0x60688,0x124924a44924924948928924c2894492c928928925929124a251259,0x124924924924928924984a2c924929245124928964a24925224a459,0x195955555656565]) else (if i<16 then #[0x155d595955665565,0x655555959,0x159a5555556,0x1956555556,0x25c24824a289,0xb08c,0x4924924c259251249451488249251249250,0x1555a55d6955,0x15595955755,0x555666559559,0x6,0x55555595565555559555d5655da59955db56d,0x155599,0x155455a5,0xa660,0xa30b58a24a24d24945324924a489e414592cc2493092ca449251459289] else #[0x18,0x94]))))
def t10D (i : Nat) : Nat := (t10A (i / 16))[i % 16]?.getD 0
def t11wD (i : Nat) : Nat := (if i<3 then (if i<2 then (if i<1 then 0x6936db69a4da69269b4926938db4d24d34db4da6da4da4926d24a36db69b4936d249249b6da else 0x6da4936db6936a272349249b4d24928d26da6da4da5124946db6db6db8d249a6d36936d24db) else 0x49249a4934d24d249369249a4944dc6a28e24d36db69a49a4d269369a49249369a49a4d34d3) else (if i<5 then (if i<4 then 0x49b6da49a4924924994924da4db6d36d24924da6d34db6da4da49249249b4d36d269b8db69b else 0x49a6d249b4936a38936db4926dc4936da49b6db4da49249b5124d26db4d36db6db6db6da49a) else 0x6db8d36926d349b6d249249249249a6934d2493492692))
def t11A (i : Nat) : Array Nat := (if i<18 then (if i<9 then (if i<5 then (if i<3 then (if i<2 then (if i<1 then #[0x15595555d569556655555,0x4b249249249251449259251249249809,0x4924924924924a251251649251249249249241260,0x25124a2d1465,0x12612492492492494c9249249251250,0x965124c,0x56555596566557555655555555,0x56555565d5d5556565555,0x565555997555555,0x56555555c5555655555,0x15955555557155555555,0x555555655555566,0x5555556555557566,0x1555555595555569,0x2512492496492512cd254209249,0x128924924924945124964a24924c24d241] else #[0x924924930924a24965124a2490c9,0x65555955555556615,0x9955555595555977,0x1955595555675555,0x11689249249251249249251251261449249,0x94492492492512494492612494c92c9049,0x5955659595555d55,0x251249251251449259249449249309249,0x844944b05124105524920b24900964920a2818814414490402c1041,0x4924a2514492492492492492496d12592492494914892512492092c92492492092594e22494d1209,0x4930a25264945a64924924924924824824924924a4922493092492492492492493294734c9209449,0x124924924938b249289249849249249249252289a41,0x984925124964924954a259250252,0x10311111121111222129115121131112112181a1201111111113112711102111211111411111111612140112201111141,0x3555655656655559541555,0x59d555555565655956154]) else #[0x5555555959555565497,0x555595516955555496,0x492896494492090492492494d124944924968945320928924924924924a2494a2249290241,0x124924d24924924964924b24924930825248a,0x195555561595551a7,0x1575555555995566155,0x16d4515145515924645,0x15555555965565164,0x1959555855555a64555,0x24924924965124924924b24924984a44a,0x98492494492492492896492492552494d128929129224924924925824925227225149a241,0x1656555d55555915,0x1656555d55556455,0x4925a249651249249249249249252a4924925229124a44924924924924929444928a261,0x124124924a24944924924a24924930b44b,0xb249249649289251249461249]) else (if i<4 then #[0x16d65556555556455,0x94892492c9249249449249461049,0x4a64924a249249651251289249461109249,0x676d5555159555699155,0xa2cc64924924928924944a289841249,0x25928a24925124924930924924935124a,0x130c25124924924924949924924a24a24924924a29124a4c9295449253289249249249249,0x295555555955b55,0x9249249249249251449449249251309648,0x5559555555565559955e5555559,0x3492612492c9c5928c249251291259e41,0x157555555567565559455a,0x5957,0x159555555556555659477,0x4a615204,0x1555595d55a556155] else #[0x24924a44920a2492c924928944924924944924948924924944928925ba4a28928924c659289059,0x128924b24925224924928924944944c24924924b,0x4c2496522892492512492c9241249441,0x11111141220121111111011141111716111112810011120112421211211110111221212311311221105011161151113012131,0x24a669261249209249259249241249251449,0x5556995555d555555e166,0x55559555595591565d,0x924924924924b24a249461255,0x5555955559956455597,0x555555555596645a9,0x5d85455245551516246,0x5595555d5555619a,0x12a164924944964925124a209249,0x4924924904924925124960e24c24964924924924d04924925264a44924924f452289051,0x15969555566555557157,0x12a12592892492c9311249649251441249])) else (if i<7 then (if i<6 then #[0x6555d55595559155,0x19565555d9555925555,0x5555555d5555455a6,0x124924944925925124900924126125144a04924948905124924924924924825254929e049,0x6465555555715556465555,0x4924a24924924944964b24924924128928c,0x924b2492892122c9289249309289241049041,0x45d675555555555555554195544,0x2575555555555b55555865556,0x5265c249489249249249249249209,0x64555555b55599555555445,0x928a24925148a2c9249241261249770,0x25144a24924a24924988a459251049250,0x5124928924925124a24928928a24b2a0,0x924925144b249289449309250249,0x964925124b249c49249451349311252] else #[0x134944945325369124924924924949f20b24924924927124924a2ca509291249251813449251251,0x55595559565557556,0x6556559555556667595,0x124944a26124926924945228b249249,0x4924a4492492492c924984a252,0x12492c92512512c924c2492692094b0,0x25224120928924124824c21108b249,0x55555555556655e5b4,0x155555555555a76555,0x19595655555556a75555,0x2522c82412512c926924b20a211849209,0x4a44924964928924924a24924a461249,0x948924b24a28924124944924948c289249,0x15d55755555d955559666,0x199a556555559556599dd555,0x92512892494492592492492894512492492a124a208]) else (if i<8 then #[0x1144924924928a25124924924964946145128a041,0x15755555555559555b556a,0x24a24924924924924944924944950945b,0x964924925224b249251249889249,0x95674,0x92298512c92490c9249451249309201,0x15b4,0x65db,0x15d961755955995,0x1765655967595581,0x225171d,0x146a9081012235302020417303400040,0x4d3254648,0x1324151a,0x125928928921125930928b249251a49249409,0x2512498492c9249249] else #[0x12422c924e1498494492c8249409,0x259251249289249251289254,0x125924925a28a24924984a24d,0x166124b24924904924928a24924b2cd29124944924924924925244924948924a891249389201,0x542492422492492ca24d249252,0x128924928924b24d24928a2492c825e209249849,0x8a854504812463082090100410410000011c92040410430410c1,0xa46967165b24948a24b85c2c924b85820924926948b28920924964b47964920a40a28a20a20a20a40a,0x23731843222111501132215314161412111016132922211013231111,0x15555959d55565955565a9c,0x59559956555655658,0x55555595596565666564,0x595591955555959758,0x55655a5555d66655558,0x11213b101102170812490a110516123000214000000,0x555555559995556d6664]))) else (if i<14 then (if i<12 then (if i<11 then (if i<10 then #[0x155555555555965558,0x24c34944924964924a28924a249249249250,0xda5168f2ca44920a64970940924a2c188c26124948b05924a2922922814492993890498ca081,0x5596555d555555558,0x5596555d555555558,0x24c20944925924924a289251249249249250,0x494492492c924924d251249309250,0x1165324104920924104c26124a20a209241250,0x19975556555555555c,0x145a2ca24924924904926130928944a249250,0x92892506492492494a8289249449249251289489293249249249241249249849209249241,0x51851a492492492492492c9349251251651249849250,0x266555555559955d555955558,0x9b551556545595558,0x94492c9261249249249250,0x212163111156313317121110210111019121212141811101014111541] else #[0x695556955555d5d5555555165,0x559995,0x166558,0x155755555559d59556555a4,0x1556,0x679540,0x9c4934924984924924945944924964a251208,0x65dd56556959575555555555644,0x24a24c249259652249249249249289249288,0x124a24b24924a249309251249,0x655d5955955555,0x55595555965555955,0x655555555555a5564,0x2555955555556599592,0x95575556555566564,0x655655555555585599a4]) else #[0x22492494492492c924a8892514c8,0x11111261114312311111101148111751101,0x1211a2001151430b101543908100c11062171d00000,0xb30928924925124924a249a496492512c8,0x575555d5955595964,0x16221121391111231111211331a122013113444112221511511521112111170111311122310113113112228011131120000111,0x5a56555565d555575974,0x165926124934925125224a249251449671249251849488,0x1a0820b2092410492c928a249209244260,0x19557555555555958,0x18559555455555155d71,0x20830924924924924924924964924a250,0x5144924924924924929124b44924924d260,0x105449243c4928a26000828b290,0x12492c9309289249449288,0x128928924924924924924924b049249308]) else (if i<13 then #[0x4925124b24924924944a4492494498492492c8,0x556,0x16d954,0x1a556955d55555555,0x259d,0x2802d1084,0x8b04d444,0x4264928c,0x5124c2c92494c9249252249249269,0x56595565595595555,0x2594496a0,0x55655b,0x25a249252249289261,0x556955d55555955555a,0x964924c24a249289249,0x3595555a5565555d] else #[0x5655559a55555f,0x492c9249249459449249289262,0x155655557555965659555,0x5565559d5555555566,0x65559575955555,0x492892492c9251289249251309249,0x57565555555d5a5956,0x8964928a449251249261,0x964924920928b449249449460,0x56595565595595555,0x155555675555555a,0x19524,0x575559a55555a,0x1a75db555555,0x15e,0x1595559557595])) else (if i<16 then (if i<15 then #[0x55559555d5d59556695655,0x259249249049261249449449,0x5565559d95555555a,0x125128a24925924c249289249,0x925144924964944c249251249,0x17569569986955,0x2655565699175555,0x124a2492893092c924928b44a449249249,0x16555565645d555,0x15555655a5575d555,0x968924929124964c249249291,0x1655559a55595d7,0x15655566d555555559,0x261655,0x995559696d555,0x155a5955575555555d48] else #[0x15555566559555b7,0x29130928a2c9249249648208,0x59b,0x24944124924d24b24924924c249451051040,0x24925124924924924930928945b,0x114512496492492c9061048200,0x32c9289249849289249249251a41249,0x24a2c924924924944924924944c20a200,0x12c924945124928a2894492492892492ac,0x1655555645515a5555711,0x4b24924925228924c2c9249252259294249489292289249249251249249249249249249,0x15555555595955656665555,0x5151645457515915464555,0x1111161211221111411121381194743132111000131123011111111111111111101111121151111121122122211222111221,0x4b2512492cd2492892892518612082492ce259049249,0x122216131121221141341112111b811121111a474113132111039111111111111111111111211511011112221212221211211221]) else (if i<17 then #[0x5d655567565555555565596,0x11251112111112411411111221815121211246413131113111017211111110100111211121315112112112131311121211233111,0x555555796555d5555555565,0x2492e12524494d9449249249289c4930a54324965b45b25924924924124925949244948a251,0x1116111121121141111121111111211119474113132111038111311230100111111111211511011112112122212112221221,0x29134a26925124926225b6e124484a6582c124924924924944924e24124948a45144a489291,0x3a366964a68a2612412892d9251249a4a60e04924924924924944f24124928a452451489291,0x565955655665545656555555,0x1411221141112111112111154743132111038131123015011111111111111111111121161101111112212221211222111221,0x15555555559595555665555,0x995595a57555c,0x167,0x555d5555559969,0x124a24924924c25124934a24924b4c8,0x5555555565555659555,0x555955555556d55] else #[0x1555555656559a555995555,0x565955595555565,0x159665555555d55,0x9849449449649249449289249,0x9849649449649249289251249249,0x595555655555555,0x15995565565555555,0x595559555555,0x56565555655955555,0x56565555655955555,0x92096412882c9a4e24928c249209441249049,0x55555d55565955559555,0x15557554556595555975555,0x155555556595555665555,0x24924934924d051259649259289512249254292289249249241249249249249249249,0x15555555556565559566655555])))) else (if i<27 then (if i<23 then (if i<21 then (if i<20 then (if i<19 then #[0x4a24a24a24c24924b249251249249,0x59759555955555,0x15995575565565555,0x596565555565559555955,0x565655595595555,0x13092892892c924944924a249249,0x59759555955555,0x159d5565565565555,0x1659595555595565559555,0x565655595595555,0x159655955545556d55,0x1596655555556555,0x4a24105964954944b28924c24a28944824a209248249,0x126964965934985924928a0512491114532f124144964920944925128945125125831970a24f051,0x6555565a59555d5555555575,0x924a84951624a4ca249249249a4b2494524d124a2922912892492492c92492895aa64940b241] else #[0x4a34cc6933134e30924a28144924344b2d924146030924128924a25128a24a24805964b251251,0x24b289449248261249659249a4124945124924e049201,0x24d251a49c4d28c24928a40a24921a2596c920a28c24904a24928b2c964a24929198cc51260201,0x1131161111618121112111331115324111012111511011211111111221211121311141171121112113114341211130121001,0xd389a613492892892c921a6c920a30924128925124a28928b24b25928928cc4a33144980a201,0x4b24d28944924924a20c47124924924924924b240,0x56d55565565556555555555f,0x4984924a249249649449249251249,0x555d555659955956556555,0x555555965555955,0x492492c9209289249308249209,0x25124926125128924b259249,0x126124b24924d24a24a2492492512c9249,0x15755545659955955955965555,0xa26948d2932692a124919145960920a30924124948948944944929984e24a04949465b24c050201,0x1556555565955565d555]) else #[0x124925924924924949144926124924a2512c949924925224a48a249249249249249,0x4925930924924924945245126144b25224a44a449491249249249249249249249249249249,0x199555555995595995559a655555,0x5655555565995595995559a55555,0x1955955555555596555,0x565555555556566555,0x1595555596566556565655595555,0x56555555656556556555,0x15955555565655655596555,0x596557555555656565955566655555,0x55555555655dd5555555556955d,0x555555555655557455,0x155b55555516599595595555991555,0xa30928928924a2492490492c9251249249,0x4925324924928930925924928a209249,0x5659955d55555555f55555]) else (if i<22 then #[0x756955d565556555,0x2492892cc,0x2094ca251460,0x8944a2492cc,0x365924e251289249349259109249451249449311278,0x24a249261259249249249,0x929224ba60,0x19b695d78,0x4b24c453,0x1595556c,0x128a249654,0x2492892492492498c924924a299249249,0x5d5556595556555,0x24944924924a28964924964945c,0x4926124924924b249249449449,0x165656555555555555d55] else #[0x16596555555555d55,0x15955555565655555557555,0x1595555559595555555,0x1595555565955955555,0x1559,0x556,0x4924a263,0x92496492a1,0x8b2893092492492592b124924924a24d,0x595,0x4951a,0x944926924928924c24924928b259249,0x25124a2492492494592612494414492c9249249,0x299255249249249449259249849249249c89252,0x928d3124ce,0x1656565655565556555755])) else (if i<25 then (if i<24 then #[0x165656565559556557555,0x128924924d24a2512612892592c9249,0x125124924924a259259249251255249309249,0x6579,0x95967,0x9555b,0x159597555655555559555,0x1596565555575555556555,0x3f,0x4c44968a,0x5064,0x59655555555596596655755565556555555,0x5555559665575555565555655555,0x199555556599955d555555555955555,0x265555,0x195555565969955d555555595555555] else #[0x156655,0x5555559656557555555565955555,0x5555559665755555565555955555,0x16595955559555555955557555555,0x15555659955d55555595555955555,0x12c9289aa6,0x65559559555555,0x165dd955595555955955,0x59666555755556559555,0x944a289289289249259251449249509249,0x128944925125124924b24a249449509249,0xa24924926128944a451249649249249249449249249249,0x124924930944a24a2492c924924924925124924a249,0x924924930944a24a2492c9249249249289449249249,0x5555559665755555565555955555,0x5555659655755555565555955555]) else (if i<26 then #[0x155a9b55,0x249251249289449449259249249251249249289309249249,0x15955555595955555555,0x6955555955555565555,0x66555555555595555995555,0x496c926424928944944924944924924a24d24928a2c8,0x4b26124e24925128928924928926134924925165a289,0x5145938924a25148924925124964d24924944984be49,0x4964e24928948924925124b26924924c2494512c8,0x4946924928944925124e26124924b24a249459288,0x593892492894492512c926924924a24c2494512c8,0x8a69124b25bb24,0x4a25164924925324924b25124924a24c2494512c8,0x905144904824a241449259251051309a41249,0x944c64125120924a28824824b2c9248251,0x984844144824924b2a904920928a249209] else #[0x904924c24b24148864124920928a241251,0x25126929144904924985620925124b2c924128a251,0x26184924924a25925124926924924a449259408,0x24924928984944924924a04924a4492594c8,0x28a2492492896c9249261249009249292249d49,0x255755,0x28924924a25a249249849258249249255208,0x5d7555555d555855569559a4,0x24a84924925225124924924924925224924924924a24a44a49124924924928924a44d64a29124a241,0x131924924a24a24a449249249292449409291249249249249449489492251248249249289249,0xb25124925928a24924944944924a349271449261289449281,0x129124924a44a24a44924924929224940929124924924924924924925124a24c64a291291241,0x55555555a5955615a5555555695696a5555565556957d669651,0x555555559555555556,0x124924944924924924924948928125224924924924925225248944924924944924931928a44a44a241,0x175565565556555555557]))) else (if i<31 then (if i<29 then (if i<28 then #[0x15555555596596655755565556555555,0x5556555565d55555557,0x1290121211124110121312511151211112484111721311101111111011116111223312112213112131211111311111111121,0x5555559665557665555555555555,0x5934924a25148924925124964e24924944984b049,0x2492492896c9249241249009249292249809,0x265555b555565599555595,0x65555,0x55655,0x5655556555755555557,0x555565555565d555575,0x555565555565d555557,0x9d559555655e55565855,0xb652249649251249849251a42249,0x224925124924968a24940924a2a1,0x5ed515959559566455] else #[0x311458,0x24c24964a24b24924a249292,0x2492512492c924925944c292,0x124b454,0x929129944c,0x4612f5,0x155565d659579555595556155,0x55ba,0x169ed5,0x24a24a84924944925924924904a249,0x144a2e2,0x25224968924925124984924944b249,0x825c452,0x56,0x9a55d,0x25656]) else (if i<30 then #[0x3233331111411411101630203723810222450412211,0x84924930129124a242a4905e25a691,0x4a25126024928924924b251248249649,0x4945228a24944924924924c649,0x5564551855c458795,0x91558,0x24048,0x2165,0x8c124d498,0x650020c8,0x4924c2c928924928b45124925924944a259,0x4944a2494512492cc249249249,0x4924124924924824924925124984a2496492882522522892494492c944924944a24a459,0x15475545559a45559595565,0x1a4655465555455556,0x12341212011022325112123111211350160111141211113111431101761110111111110801211113112130111601211221111501101] else #[0x125154924824924c25024924925324e279259040,0x1212111212211022511150160111424141211313131123401321311111017110111116112110801211313011111212112111601501101,0x1565955995555596,0x492ca251449249449849249249249249,0x984924a28964b251449251689,0x15d5555d56565556555556,0x6d5555d5955a5656,0x5594c,0x9951400600,0x2612912492492492492492c924a449489,0x1555555555565d556655966,0x165d65555d55559955565556,0x5555965557655555555659,0x165965555d55559995565556,0x92492c944944b24928a249249249249851,0x4904924924c25928924944a291049249449249250])) else (if i<33 then (if i<32 then #[0x1555565555556764555995558,0x128924964984924925144924928924a,0x165959555d556665559556,0x555659555d95555555659,0x165955595d59675555559,0x55555555555565d55626559664,0x655755955565565,0x928924964944930928b649249,0x5995555b55d55545696,0x25567,0x5759d5955d55a55555566,0x556d555d55956a655,0x92492492492892512516c9262249,0x55b,0x59655556565995555599,0x5955555555a55955559] else #[0x6d5556555556956555599,0x25555557655855699,0x28b24924904b24924d29104a249249309249049292291,0x159,0x2622c924945221b456282249a89249,0x1a594555595551665555,0xd5684,0x4a25145924944944924c259249249,0x1556555555555a,0x289249449251449259289449249849249,0x7555655555ad55565555,0x555655595559d5555575,0x55556555559d555575,0x56565595d5665555555,0x55565555a575d5565555,0x555556565d55555557]) else (if i<34 then #[0x5665559559955d65955555,0x56655655955b5555555557,0x5555655555a5555599,0x1595559556555695555656596,0x195559655569555565655,0x1555955569555555599,0x1659555559599555555599,0x596559555555d55555565,0x5965555665555555665,0x596556555575555559,0x24a29924944924a24924c24924924924b,0x5124924a2892492cc24924924a251,0x494492492894492892492ca30924924a24a,0x51249249451449249651849249249,0x565555965555765555599,0x655755557595555556] else #[0x4a25144924925925124a24924924924c,0x596565555995555599,0x94492512492492492892494492492492512892cb64a24a2493212512c924928924a20a651,0x492492892c924924925129144924924925144924b2512522497192912c9249249249209241,0x275655955565555a4,0x155655555a555555,0x656d55565555595,0xc24a449251249249458249249,0x24930924b24924924928144924a24964924924924924a04924949124a64924935964a2c9051,0x579655255959d55995585,0xb67184925b24c45124994824924a30a2c928d24926328c24945248a4502892c96492092ca681,0x13271112111112311311111221810121211231131114111612111111131401112111214131121121125011123121124540111,0x128c249249251249249251251641400,0x124a6ec440,0x128924928924c24b24924928b,0x93851200600])))))
def t11D (i : Nat) : Nat := (t11A (i / 16))[i % 16]?.getD 0
def t12wD (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8e26db71c91b71c6e48db6e392491c8e47249248e48e49238e47238db6db6dc69b6da6e46dc else 0x6e48db69b76375b8db6dc7236ddb2371b6db8db6e38db6db8dc71b6db8e46db6db71b69a6e3) else 0x46dc91c6db6a36db6db6d36da6db6db6db6db69b89c8dc49b49b8db6da6da)
def t12A (i : Nat) : Array Nat := (if i<9 then (if i<5 then (if i<3 then (if i<2 then (if i<1 then #[0x151b5510121d1101211a11212121211111f11112119441222161744183718121212221412151531112214c11634121516113e12131161211191213333122130113311212110111111011612001a1301,0x164904a84128a2492492492092492c924928a24924920924924929429126925104924924924924924924940e491241249449,0x25128924924924925928944a24924a28a24924924924924b25124924924944c289,0x944b2492492492492c944a251249251449249249249249249289851,0x1141411121111111111111111111111111112511111111111111511111111238111112311101112222111123111017111261221111112221111111111111111101101111,0x11211311311121111171211111211211211214111112112112111211111313112111111111111510116101111111811,0x944c44924928924924a2513094592494492ca389408249249259249241268,0x924925224924924924924a061249249249249449249249a4924924b49124989120925a29124a489051249209249249249049,0x165955595555965965556665555555559655555559665,0x124c20924824d2492492492492492492492494c94c924924924c24945a24925424924924924924924a48924929104924f499241249c48281,0x25128928924924924c25128945124944928924b25925124924a259249249,0x944a2492492492492c944a25124925144924924924b249250249249289851,0x944b24925124924928944e25164925124924c25124b28924884d249349049,0x128984924b24924a2512894592494492c924924924924924924925244a,0x1659555555559659655566565555555555559a99,0x4a25124924924944984a25128924928a24928b259249649251249249] else #[0x111113111111111161111111111111116012111111313111313111111114111111421121172251111111412811122251211111111111111101111111111111111111111111111111,0x26128924924924c2513494512494492582492cb6494492492892c8249249,0x12c9a4a24a2494792612c9a4b24924c291c4924924924924964924a252291,0x964a24924924924944a25928924928a24924924924924924924a851,0x128944a24a24944928964d25124925148a2ca261209249249271249248,0x944a24924924925128944a2c924a24924a26a28924924944c249249249,0x24924924924c249e49249249249249293a4924a44924924924924924a489252489449249249c492492536492ca44a44b259,0x12492492493492492492492a12492492492712492492622493526490492d224949324828924a449250252449249249249249249249,0x4924924924e24924925964aa49249249249a4924924968924e4a124124b2d224949424828925a449250252449249249249249249249,0x24924924924c24944924b24929124924924924929224949124924924924924a6c92516c9449,0x4424128204e288289208049200610049039241a4124904a082449200041208203408208201,0x11151111301111111111111111111112911111111161111121111111272101111111111111011111421321111222110111111111111111110011111111111223011118122101101101,0x24a00920826128820a201040244051449209241a482000412c16c104b041208201a08208041,0x123014123b11a1231711212221112113d0111221144418122221114111214314141131121390011116163111311111111110121512151212121210121012101235311321c115301711012,0x11161111201111122911111111111223121111111111111141111114411111145122111115821111172123311113211211116111111111111110011111111121a22211211150131101,0x984824840924924925804124924924a249289208609219249249249848249241012248248241]) else #[0x1111111111401111111111111111111111129111131111111111211111112521011111111111113111111214211112221101111111111111117115111111111112246111318122101161101,0x131000102420113131121181316111111100170111131511633211a11102b119001301111011011114242122011112217110c013112111151d01110120112111112100001201001,0x601092280248c410480202082040011c9200608228208a08208209640208412881008408001,0x10141011536111212222115315121121111512011191122221037313211303811012121210121012101211101211110111311012111012311134110110121114132210100134123100001,0x1609a41493681048008208202018431280610248040a10208808220208201240208200041,0x103309114176114141122112121111201012015121122221013111411121431012111112180111011012510121151151101210121012121210121012101213001112210113000011112,0x111111142711115223111111111111111122012111111114111111115111115111111101221111160211111121238111321121111411111111111110111112162221211110013110101,0x12141212121121213211212161115111121411112141363231331110331121421133014411110111111111110112121111311311311111121213213571411380111501,0x1012101141412122221151151211211112141121111222210123132111038120112201201111111612111101111111012112117110111101131012a122313113201101901,0x10121811215131312911211212112111151511411112222101231331112331101241132214011110110111121117111011121012011211011121161012413321011640111201,0x492498812494d124924924c49964924924924934924d24938a6497d128a5094892c924924924920924924947268944900a241,0x101310114151215272114119131121111515110111164741023212a11102b1101321122010011110110110111118111011110131121131101111113001226160113c011201,0x152210123012012011512351112113911311444121222211121110143121211221101220011112163111201111111111412111111171101111112223381122313011320101101,0x11111111201101101111111111111111122811111111111111111111111111211111511111111161111111212211112231111111111111411111011111242311111713110131101,0x164964a0492492492c94812492492492492492492892492492c9a492c945424989124924924924920924924a59125945120c241,0x151215221011120116121613111121511312011114121122241421110141121221111011011111131313111221141211312117110111311222119312810111201301001]) else (if i<4 then #[0x131410001201312011713131110111012111281712363212011102d12c14901122012011113140a111411111151111118131111211b11000111112015129126010011200111001,0x108012181131211331151215211211512114011141121213333212211202211113101101111b1711111141114110112120a112211126110110111154716142101014610191901,0x111111271111122311111111111122912111111111111111115111115111112122111202111114212221111221121111111111111116110111111114212332111811120131101,0x12001511222202114114201121111020112111194743020313211103812020311230100111111520111111111111111020112116110111111222221211222111221,0x13142c113131100114131611111101311215111131411633711b11107011a13211110110111132821225111122151131411211119120111212121111112150100100001,0x12121411212134112121611131121211121211112141367231301110321121241135012211111111111111111214111151171121111011214134133312113801101501,0x3512301212116123611111301233012013114141222211121110143121212111210120111351731312013113112114141111101181101111112151300112131311320111101,0x12cb24124924924924949124924924924a24a29124a44924924924924882124a241449,0x1114141111261111111111111131111111229111111111111111111111111112311111111111101111111152122111122201111111111111171111111132282111121201110121101,0x1212101121211511212061413111121911b1311114a62122111012131111411011101211131131311131121211811011131101411731241511170151301,0x1920124224120904104929148a4c9052a1020922022020824924920924864809021b008241,0x1012221011418131436311211212041121111412115111122043013011103011012311322150111111012111111111111111131171101111112a13322191250111301,0x10122210114391114123112112120421111114186151111120430130111010110123111121101111113112213115111313117110111311110126313215111a0131301,0x4c30904924924924924ba092492492492412410c926b24924924924925248925128a251,0x111414111126111111111131111111111132291111111111111111111111111231111141111111101111111112122111122201111111111111171111111152282111121201110121101,0x1113132611111111111111311111111111322911111111111111111111121111111111110111111421221111222011111111111117111111115228211112120110121101] else #[0x3512020151192031151182011111201211111062102612311a11103211424127111101121113122202221111223121111020311114122111213122020131111113170121001,0x1316201131303261111315281111113292271212110133312033111a11101021111101401111013212141711211211013111111151101111124111212011240111101,0x162610116151012113131314111131600131914111101353110552120111018141111011011111201121201114110131121411711011140110171174212212111401201001,0x12121611211215161411112181164120111121333113335152111015131111011011112121011411414111311213114120117110111411222121221221211122121221,0x602594412802082430c924905226021025140829020920104d281051251849041008241,0x12181219163112121212411112171219a014111151202101066313011101014111101101111732101213113131114115120210123141151101114112381015431331311140131001,0x60920949228944924924925d60827944925230928924934c24945224a08a25824825b4496c8251249249249261249609209cd225920940b241,0x986128929324924924924824924babb0b204924924924924124124924924924924924924924969a4492410492492ca49124aa49049281,0x128968924924924a2512c944a85124a24944b051249e4924938944a449249a49249309289249208,0x96482692692492412512c984a24924a249c4b07924924920928924924c251249249448289249201,0x12c968924924924824a2513094692496492c964924920a38925144924945128924c249209439,0x311111016522122211115361322222748121542111115114011101211101012211022382221113171414131327219132312641411000,0x277111413a4333111149811221111251113131111531160111010111d1b11421101012101122111c10111011152121618121610001,0x1012221011634191101231121121221111411216717111118a41012223013011121c1101251111211b111111341122130111411110123151121101114011121012d313213111501301001,0x2512c92512c924944a25128945124964928984924928925125924906a251249249249,0x25128928924924924944a26928a2492c9241289249241251251249251849049249249])) else (if i<7 then (if i<6 then #[0x22211161256331111122521221111221113131111a31170111010111e1d11b21148018142141010111199101121012171fc,0x26128924ac4924924944a26128a2492c92412c924926924a248241249069409249049249,0x111111201128111111232323231131202322601101212411111121111124442111112333242311111111113110121112011201221121222011112411212410133250111011127202521112121202110121001,0x130954924c34924925928944a2c924e24904a249049249251051449e492c9449249249249,0x4a25134a2c824924924a251289449249449289409409249261249249249249249c51289240,0x964a28926924924925928944a65124c24904a051249249249249249249251249200,0x106012221612101216331112121212221211012151800171111a1255191233121011144410110120113221001121815101211011111101711a22192212012410017201131b101200131111110100111001,0x113112010111811111111711911211411313111116111101121001011111111111111115111111111211101011241011a100,0x161111612222211113136c11133372222253211111511401110121117121b2218801414101309725151031a1414100,0x4824924124c24904a25120a2492c9241249248209289348249281049249249,0x11211251111111111113111211411811311111112111131141001111101111511117016161111111121212120210,0x128944924924924925128944a28924c24944a249249249289249259449649249249,0x4b25125144924924964a25128a24930924128924924ac8928924924934a049249249249,0x24a24e24c3c924928944924d24924928945124904944924944924924924a24925144a48925144926126124926124a2492592d944a259259459,0x25130a2492492c924928945124944924924a24a249249251249249249,0x928924924924924a3092912492492492498492512592522492492492592892c925344a4494094c9249249249249249249] else #[0x195555955566557555555955559555555,0x111111332011111726111113411111111115111111111111111111101101111111113212211111111111111111111111111111238221111110122111111443211111112011191,0x25928930924924a24925928a2492c9249249289289249249449249249,0x1111113320111116271111115111111111131111111111111111111011011111111132122111111111111111111111111112352211111110122111111111184421111112011141,0x25928930924924a24925928a2492c9249249289289249251249249249,0x11111215111327111111111111161111111111111112281111110111111111111111112152111111202111111201144111124101121232223111121131122311111111111111111111111111111,0x944b28924930924924a25144928924924928b24a249249251249249249,0x24928d58924924924924d24924924924a5c92492492492492912492822496812d924a64145449324944c294249249249249249249249,0x59755657555565a55655555656555559555555,0x4820924124b3c944a26128a249349261289249259649289348249256209249209249,0x5556555555d65d675575555556555559955555,0x124925c249249249269249249259681281249249249048249248291249253209249249249249249692249249488249222449249249c48201,0x492514492490492c944b251649259249249249449249251449849249249,0x492492492492c944a25184925924924924944924924a2a1249249249,0x1934611212212114320013121121234041111111111121211221111111111111122511321733b112011185415a12153301120113112140461711215011131511412513111313011201100161101,0x24924924924944a2712cd24930924924924b251249251451249249249]) else (if i<8 then #[0x985820924133124944a2412492512492193092492510893492092c84512c8,0x120904f2692090882412092492ca44220924125188e249048251051,0x4d0412482492092512c9049249849248201249252211249048219408,0x24824820924824944920824924925224944204948924924924924a21225248944924924124944924924111928a44a44a241,0x30c2ea05124924904925249224941544990c29224b6892492492c92482922b224a44b6024092db309201,0x412512892492492492492414d92d124924924904944924924944a2912492914492492492492492492412da249249291249362449249249289201,0x492892ca249261c4944964924824924a29245125125b45b2c92512492496492492024c9a4928b241,0x130820928a28a2db44924924906929360185f29430924a2d932145245149a251440249271489251,0x9562222215611012133113121111111111144444211111017431111115012116111221121222121112222133111121111111111121000011442148133112231005022225011331111111111111122113311000011,0x22214121011122212121321111111111111015112221001413712221411111213311441211111161221111210811012133323341001,0x24924984924504925245144030bc526c984925190b44a48a292289249a5220928b6d004828b70a201,0x12121212411212064121121371511112121212121020121340141181111312512111111312101131213113131131211511111161101111411313441241711313114141501,0x4c20944125920924924b24908924925904920925104a,0x128944925944925928984c2512c92515092494492896412492492692502492c9,0x4a25124924924924944c2512a1249291249c4b24b2c828945124a249409269248,0x12cb24a24a409249249249049249553413409249249249249049249249248249249249252891249041241251d22249549248301] else #[0x4a25325124924924944c2612892492c944904124924c25160928924924924124924a240,0x4a26124944924928944b25928944929924924925104964924940930a258249249,0x11111111251354111111011181422211163611111111111c14123010111370111110013511a10119121b,0x25130a45104924960944a2512c9249289249c492490892882492482d1245,0x11711311121221111112112118112119112111136111111101114141011111111111116011511510,0x12c964924924964924a251249261249291441452289255249249,0x24924924a251249289249863c9244924924924824924a29149228824924924924924924928929225104a4492493da44ba49289281,0x1111112611111117112311123111111111121111111111101111111101111111111251221111111111111111111111111112311422111101112211281133321111111511141,0x2592c924a28924b2512c984a24988924924a209249249281249,0x12492f12492612a924a24924925924924924124924c24924925c35124924924924924924a64a4892410494894c92498aa249251279,0x25120924b24924a25928984b24948924924b20924924a049249,0x924924d24924925924924926184a44924924924924984124924a24929244944124b6c925b6c925124a48924a64a489249249249249249,0xb24924929124924924928944948924924924924924924924924a252252251249309d49449489251,0x924a44928a25128925a24924924a20924924924a849249,0x944a24924a24964a25130944b24945524925126128a64b2492492893892502492c9,0x1121122111111114112111131131161121211111311711111011512181212910211121121311211210111111120]))) else (if i<14 then (if i<12 then (if i<11 then (if i<10 then #[0x2512d12c92494512592c964b251449259389249269442251459449461289442249249,0x11211221112141112111131131141121211111311811111111712151212111161a111115213121112101191111,0x944a24927938934944a25184925134924b24c24924924924924925144984168b64b,0x2512c924924924944b2512914492894492612c9249249261249a49248289452,0x25128924924924944c2512c944928a44924926928a44a24924924b2496c9251,0x130945124b24924944a25129984928984925938924924925124934924828945b,0x4a25124924d24e2512894592494482492402592492492492892492522892c831184c,0x116112111111111611128112112112115211111141221110111011411213171313131011141151111100111111111,0x25129144944925928964b28924c25924924c25a3ea28924924948e289441249249,0x9461289249249289292249449249249249252b0928a24924924924924945b249489649,0x924925248925224925124924c24904944924924924924925224945228924944924924924924924924929224928925225224925b4892c9251251,0x4924924949124924924945124924d2492492492492493124e124a3198492524db24a2d930a44a44925224a489249249249249249249,0x4924929124924924924944a449249a4924924924924925249c2494632492d24db24a2d930a44a44925224a489249249249249249249,0x25129925924924970944a25128a24928924a24921924b24d249259c4925928924c241,0x11311241121111111111120111311211711213111115111116111114101121213121111810112110110111191201,0x27128924c24924920964a2512890492d124d24925124824a2492413c9051249209] else #[0x2512892512c924964944c26128964931124928928944b2498492482514492c9,0x1222214121131331113111611120120111141214121c15301212104832121103a11013119120112b0101376112141230111212120111112121210120115111110115122111111,0x11211241113131111111c31141121141121211111711111811111915112111121311115a1016111b131111114112110111601,0x18c6210821088427182608c202880108421084210842418821004e408421081004b0225042200c210b5e181001210420856011402,0x6239480110a3210030a8231800000421188c1084210b84c084014c025100210802014ce2788052904b080230188800648044656840000000,0x4925964972a449249249251691289241249449491252289249249249249249249249249249249989909489449249292251292249251,0x964b24a24924b27124b25924926124b449249249452449a49251252,0x124924929125a49125224924925924924904a24924924924950985224924924924924924924ac4d689249253249252489249509251,0x25128924b2c924c28b25128964929124a24944b249249a4a2492c9,0x212423112a33116111601701111111112325331133111111111111011111128411101332424251012924112201222411117125001111122515011222111822312411111701601201,0x1111111111231113264411113111111111151111111113110111111113111111112811111431721111111111111111111111126113201111111125111111222411111120111121,0x25128924b24924c24b25128964929124a2494492c9249a4a249389,0x1414102010342251121212201121221501601111212113111222311432202001332113111017121101111111611080121211311213011111221311321111601501101,0x4925185124944a25128944a2496c92692592512882492492512c9289,0x24924924a24924924a24948924c30924944b0c924924824924124924944a4894914492492492492492492912c9252249,0x4925144925128964a25128924424964904928a25124924a251261249249449]) else #[0x924a28928944b2512894492d924c24b2482514894492492892892c9289,0x145124924a24a251289449249049261242249249291249251259253,0x26928a24924e249249251289a4c28924c24928124904a641289249289649249258,0x112113111111111511111111121121171181111111612121211111111140111141111113111312410,0x24924b44928724969125128c84945124b4492412768410cb20924920936c208,0x924964a249249449249252a4924924924a4516892c924a10a289249291292288,0x12528c40a08610a00820481908cb310402a8a418161184200b322312c400001a8c0003f0100001380e20ba020dc330b400024710000a18000,0x944824a24928930924938944924944a64935924a049249249449488,0x2612ca24924824b24924984d289248249451291049249449249250,0x2126211111230811412621110121270721012311231123232521111401212211a0133262201150501201111240142201121212111111111110111111114229220120232214110101,0xa46308842088650bc23088220882602881088220082d08881084220942e08c6108421098253802108421086021100122c240a02800423088231846008c210842130844110220a0010842218429088e10b021084010842309c01,0x2612ca24924824b24924984d28924824944a44a441249449249250,0x251209249289309249448251249289249289291049249459259250,0x30929124924c24144924924924928945225224e25d4496c9449249249249249289492251251449,0x155515555465545559696915559955558,0x24a24a2d12492c9249249249249249452249249249249249252449249909492249251251]) else (if i<13 then #[0x494912492612492492618c128924924924924929224b6494492492692492492492492492494896c9c4925224a249489281,0x5124964904984924920a24920925144a441249251249250,0x124d2492492c924924924b2492492492992b12492492492592092492492594892494c82592524492492916494d224924924f321,0x1111126222721213111111111111262722151111211121110111011111118101111101101111101201210153115214111011110110111110111112120132331191141111131141,0x112221711181613111111212121117181a1b1111512151216341612121222161211210110112110110131011321911544101113011301221001134113013111101151211231001,0x11222101151111112112121221101115a130111112221122218311112221811631010113421311731111431121101114111111330122130133401116101913011111171b1101901,0x944a64a251c4924984d251289451249449209241249259651489259249e49249249,0x128944924924924925128944a28924c24944924928924924b2592c9249249,0x5d65651555559659655575518555555955555865950,0x944a28b26124924928944b25124925124970a049249249649249249249252,0x4b25124924924925928944a28924d24904924a244289251249251209c49249249,0x124924a44924a44924a24924924924924924924825124924948925148924a24924924924924924c88924929104924925b489249289659,0x596655556555659955955757555555d5555,0x492492496a36492492496492492492495312492092492492d024124948824929b2492ea2ca04a449289293049249249249249249249,0x944a2892492892492482514493092492c9289249249259249249,0x24928a49224924924924c24924924924ba8924944924924926304a2492d904928a49124949145e2522496496d0249249249249249249249] else #[0x2512c924924a24924938948924c24924a24a249649249269249249,0x24a24944924c2492492492522582492492492892492492916c924948824924924924949124924a44924a4d92492493892a9,0x124a24924924924924924924948948924924924c24924924aa5224925220924924924924924b68924925b24929248924924944a291,0x1343413323131213111213121123312121111125111133111111101611111125123121171211133121114412511101131211311111111121131213212212125112191801,0x964c24924924a28944a2592892492c924924a25124944924a249249,0x128944924924925128964a24c84929124924945325924964924a249249,0x59655555555555555955d555599a556557559,0x165955555955659555a65555556555959,0x124924944928925124924925225d2492492492512492892516c925220924924924924128924a48924a4494492936492493892a1,0x494494494494492892498492492492522c924924924924924924924924924949125124924925124924928925924a45934924a381,0x175d5555d555659556555665955959555,0x175d5555d555659556555565955959555,0x133332411152411511121111111124152612121161316131c131d131310771e232011220121291221110111110011a132011110111111811011111100111212011b2312f1101,0x25920925184924924d25930964924965148944924a04926925024924924a452291,0x128948964924924a25130945134925124924924225145924a252251249249,0x1222212213112011131a121121313120111131213121413121212104614131111501211811111201211110112121211413111111711011111223010312515119121121001])) else (if i<16 then (if i<15 then #[0x3331113111116161811382222115772112211102b23a1d19641490104241111111051122528c051a51047450,0x1289a4944924984924944c24924e24b24b2492592492492892bb,0x165d99555d5556599559556595955965555,0x2324111324252301112423812111111111251125112524241123120121223380122772111120113116601401111121111111311131301111131201123912221112422a1601301,0x92492492492492d26c924930924924928948944948924a24a4492496c94922492492c925124924924924924925b2496c928a4c9649,0x12894514492498492492894492494492892892494492492492db,0x165999555d5556599559555a59955965555,0x124924924aad924924925924924924b255e4925025124948924b20924904924929b2492f24492492492492492492d426224945225c261,0x4a251259249a492492412892494492c92732492592492493092a3,0x2492cb24924924924928d48928924964b64928c04924a51925124945048924964924927124a49124a48a291449249249249249249249,0x4a251449249849249251291249a492494c944a31924944b249249,0x51449249249a4928944a25164926124925928a24928a259249249,0x4924a24924924a25128944924985128925124a2492492512d1,0x5144924924928964a25124925924928a249449249249249314,0x145125924924924a259289451249849249289651249659289249,0x125125a24926124924984924924924a2d924924924924929224924948924949b249259251] else #[0x494498892498492492692492912c124924924944924928b64924a44124924924924949124924a44924a4d92492493c92b1,0x28a24924b24930925144925124928945124944a249249,0x2492494892494892894492492c924924924964924924924948a25148924a24924924924925129224924a4512492c9912249251251,0x24964924928924a2492492492492892492492886492492922492494892528c9249051,0x24924924949324924924a2892492924e924a29128924a4492492492492492496c92da44924924924924924925a44c84930a44b261,0x944c24b25926124924a25124925125924924924924924a252,0x1b4926cbc0929260e0492492492492494922533018524892c1269489a0a69149225160924964926824964925b909052492058301,0x944a24924924985148944a24924a24924b24964b24a249249,0x55555555755656955555555df5f955555555565a59a595,0x24904a2092c9849049249699049488251249241449241249,0x26944a2092c984824828924b2484492412492c924a20927104a,0x24928c24924924924924924a24924924949124928124929124924924924925244a44929224924924a24924925244b64928a44a241,0x25120924924928928924924985924924924924924b,0x5555555515565695555555575f5f95555555555969669659,0x4924924924938924924929125c24a44924924924924924a252252489449249249a492492512d92ca44a44b259,0x24925448924d48924a4492492492892492492492692492495092994892482492492492492492da24924b64924a491249251251]) else (if i<17 then #[0x2512c92492492892c9249249449309261449251249,0x24924440924c4092494492492492c92492492492412492492b125a29124904924924924924a48924924a44924924d491249349281,0x2513092c9249289289249249a5924924924924924b,0x24924924924938924924924924a449709291249249249249249452252489449249249a492492512d92ca44a44b259,0x9249249649248251249251261249249649249251252,0x24a24924944924924924944924928944324924924924924a4892494892492528c9241251,0x494492492892492492912c124924928924925128b64929104924924924924a48924a4492492936492493492a1,0x125124925124924924944924928944324924924924924a4892494892492528c9241251,0x9a5220944964c24904828924b24904928a288251049248249,0x12221222101212191212411212021212021146110121237313131101111111123a101241133133301121251113611331311131114011111111218101211311151115141101,0x596555565655d55455755d55d555,0x24a24924a24924924924948960924924944924928945b24948824924924924924a48924a4492492936492493492a1,0x12cb26124b2c929228924925124924a24924924924924926115948924926210b448241241,0x924925d24928924924949224a44924924928924b24a44924824944924924924924924924968948929125124a4e124b64a2416c9251,0x2492cb24990924924924924924924949244924924924924929024925228824949129124a45144926d4be249449491249249249281249241,0x24b24a2492892492c964924924924a25144925924924a24a309a4b25260925144948929245124920964924b249249241249249248249] else #[0x2474111126112511251121111111111111123113131111241121211121111112360124113220111231123223111222313121111111111111113123241125624211201228121101,0xa48924924b05124124c31124c8d14892820416d125b05104924924124914548904540e241,0x11121112111318111111141141111111111111131120121111111711111411112111111111111112011111212112221111211111315111311111131011112211111151166141121111012131,0x334b11114c11353a222222222111111111111122493d11012111351131221115013411712211170414811381143211134514133116012211161165013131421120222111212122701211,0x11111111259011631123333124112424213111111111111641144133122111231123123341111111111121111111111111111126252723223122101401321128252744223341101243011101,0x125124924924924944948924926924924928924a24b24a4492492912892512492c92e425225025a049249249249249249249,0x11248c24924b74b0512492492514894898db6d125b2512626d126920a4ca50b691389281661,0x24924924924a24a44924924924924a2492892c929124924c2492c944944924c24c6c94894096c9249249249249249249,0x25211123333121111111252101211128982131251123111111112524262160121111223013321132231133601241124311142241121212111111111110111111722321120127232214117101]))))
def t12D (i : Nat) : Nat := (t12A (i / 16))[i % 16]?.getD 0
def t13wD (i : Nat) : Nat := 0x36e371c72491c6db
def t13A (i : Nat) : Array Nat := (if i<1 then #[0x204a0482492492082494102494a448924925224824924a8e829139b72104975b0496db24820a04880924024404924248900b649208201,0x84092410480410402882012400c148020204110104404104104b2010410c0481043008201,0x919204924925b141049000ed201b0092492402482482492482414892020122402440491002482410120c1248049081009012241009209008201,0x820c22134805124924021249224941644920800c2ea2614912da3212482492496492492084915d124a44904009024b6cb709201,0x101214220115120131010011112120560003300111110170a111414001011311101223110622000011214810111110011110011222033111100001132011012009201010011010101001,0x492492092490412494496412412492592012492412493892492811493d1849049292049291849209259249249248049249248029209849208241,0x220822010911010100100101111111110044001111101500111111010010114100100330122010300440010733330101330011010100001104014610011040102220110011001001001001,0x221122080106110101004401010100000670001107111110190033002200101111030012220104001100001001105010105001101010011010113100110101022420100100220210100001,0x262320110111111111112601011120231111004300111111110011101101111101201101051182224310122331111202221113120110401111001104301201107051101221111101301001,0x1111111111111111011113121111113110111001111202603211113111012422211131105013222430011111111211110110111111101472331184111111110501312222220111001,0x33113344010a110101443301010100602211002100111120270b3100110010122203001440100306210011111011110101111110022020125200110210100110984010100510501101001,0x24a24904924925020924928928824824924a209249209249249241109ccb24829225228824928924924924824924924da2120964920a241,0x14111011811011115110110101222211110b2201111120270c33101100111662031411011101050922001111111101111110110110211232001102111511041101010a330301101001,0x20a20a04a28204905900830a2d14702492c804a76be416c1649249041241292109841881041,0x101210120112120231110101331111111111110102200141271421218011111010011001120500013100001101011111161001111011222041131010022420101001,0x124824820804804809125028a448220001281243043009441249249049249200808092408241] else #[0x14e945025141420946b20920104924848118104125920924b31028804189920a0c6041241641,0x123812120112120231411217010111002200111110100011001011611110220100410111220011101141111111013201251001132311012030041011111110101001,0xc12e130924924a28924924929240b64a44125249125228a2c122c24a248a892486d9281241441,0x4a4922492492dc80a24925124828a4494110c96d125b25101215124120a4c8048a91209281641,0x10924830920122124924809205124a40c848a012816d925b0c9459249249049248d2120809240b241])
def t13D (i : Nat) : Nat := (t13A (i / 16))[i % 16]?.getD 0
def t14wD (i : Nat) : Nat := 0x1b
def t14A (i : Nat) : Array Nat := #[0x82082082012012490680900412484088080012010c1043009041041288048208020208090408201,0x4594414590516c405264604924924924545b0411491d2641101241]
def t14D (i : Nat) : Nat := (t14A (i / 16))[i % 16]?.getD 0
def tapeData : Nat → Nat → Nat
  | 5 => t5D
  | 6 => t6D
  | 7 => t7D
  | 8 => t8D
  | 9 => t9D
  | 10 => t10D
  | 11 => t11D
  | 12 => t12D
  | 13 => t13D
  | 14 => t14D
  | _ => fun _ => 0
def tapeWidth : Nat → Nat → Nat
  | 5 => field t5wD 3 100
  | 6 => field t6wD 3 100
  | 7 => field t7wD 3 100
  | 8 => field t8wD 3 100
  | 9 => field t9wD 3 100
  | 10 => field t10wD 3 100
  | 11 => field t11wD 3 100
  | 12 => field t12wD 3 100
  | 13 => field t13wD 3 100
  | 14 => field t14wD 3 100
  | _ => fun _ => 0
end Pnp3229Certificate.PackedFront
namespace Pnp3229Certificate.PackedFront
open PEqualNP.Outside.L_meta_3229.B.Zero3229
open PEqualNP.Outside.L_meta_3229.B.Zero3229.CoOracle
open PEqualNP.Outside.L_meta_3229.B.Zero3229.CoOracle.Lite
def parentD (i : Nat) : Nat := (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x182860b243058e142060a183060818387081c2060f1a3060c1a3040e2038808102081c247091c144041010404101060410242090820208102040910185841a104041a1240808342090810209081c207082020c0838284121260f081c4840a1c2860e1630690145841a1020e1a1420c0834404141850a1c2040f10203050a30207902240a1c2050690143c81920508102044c0a1c20b0828348081820c091c5080e143c8911c30a0c1c4870a103850d2038590283070c244050e184050a14385 else 0x14305183428c0c1638a13224470c287061c2038418182460c3020618104041010307081c287901024818183070818385081c388102044c2040208101078c082c404101820a0c1238d1a1420e1e1c4041e3020610205081028284103c20e091a30a1438306081c388081c20518143050e3c2040e34208092050c1c24684181438a8e3c28d1e244050e344041a106840a342051a1028d083420d083420d083420d0814484101028616144050e347090e1e40d90182050a1c2060a184050c14305) else (if i<3 then 0x11c5080c2040e10183870c1c38f0e38304102068d1c2028810105840e1050496164051c1470d0a386851c146051c3428e0a3028710386851c342858a30285943460d1620206161060d08306841834207901828d0c10707182c284161420b0a1c287181028c081460518146050a30285181430c0a1828710106851e147851a146851a146851a14685163020b181058c082e384902868c8e104471a106050818686081c44b1a1c4480f2038e0f2070e102828810226080a1c20b0c1448a9018286 else (if i<4 then 0x142090810248081068708184840e24405081c4050c142041210687083420408163098e2428c081048a0e142040a2048808184070c103050e10308161c38610386840e3820e10342071a20208121040d081020d0e1c20408386840a1c408082020e10104040c38206101440c08207041c342061c3448d1814287123c40c0e344040e2c6840a2028a0c184081820504082050d1c1c20508142861d202071c107040922384091a38a111c607081c2070e1c20f0e10204161430616143068e30708 else 0x1c2471a202041a343840c1428812344040c1c6871810604091c20c08342841038208101020618182040a1030718302060a3020e0a1078508386060a18604081838c081430e0c1c2050a1230508102050c10209101c2050e1028510347060e104890a1c6040a123090c105051010204081c30d0e122088e363840e1038e0e342040e286850a1838c0c1040c0e1040708206070a1840b1a142041a2420d101028e101038f96106870820607082030808183880a18785083c2040a1c6060a18407))) else (if i<8 then (if i<6 then 0x12070f0e103841a10246142850a1a3868d8c1848808344040810204101038710243880e1458b0a204080a28208102c58c142a38d1a106040e2068408103851610308963438410383840e146c60c1020d961238d101020e8c1e3890c283850b1a30d1a143050c18405123048808342040d1c648183638816242080a3068d0c1068410106850818508083470808346041c1c20d1e2020d1e2020d1a144041a2020d1610385082c68b081468e082020d1a1020a10342041a1020d0a104081810204 else (if i<7 then 0x3438814207071d1c5071e3430c083a3060c2050b161038512108100c103870a2040810305880820787081c5041e142470d286840c3c70e101430c0a204070e2040a0a2820f0c1440e0c302050b1a30a912070a1a343860c182850a24688121c4040a1040408142050a3020f181028e1a1070d0e10207092068e1a1020f1a183081a14208122060718103871224707121c41020102081010588082070e0c1030c0c1030d1a18207181068d0a1040e1e102081e1c20f0810784082038a0e10504 else 0x2858a0810607081c408903058c1614504122e4841210408182c60c0a2820d0c106041030306182c2060c343840d1c5840b1870d09185c7083840d082860d08103071d1828c0810484181420a1610286103c48d08106070828588092c584102c20a1214208161068410365cb08365cb0a343041a342841a1424816103861c146841a2020e1234284181438d081038c0e10685081470d092c6041a1820d0a1030d0a1030b081c4040a3840410143851a2020618243051824605092c6850820508)) else (if i<9 then 0x10c60d083428f161070e1e10387082238c1a1c2048c1438a0814646161040a08123050e282078e3068808123050e282060f185040e186850c1e30708282041630604161038d082c28c092c6051c3028e983c28b0a3020f101470c0b3078c0a3020608202860e1420c092860410306850810585161468418106841c347851d307851c3420c081c2071a145850c2c38708342840d20604161068410306041a145041a14604163038a08304081628208103058c18145041020584141c28c0a2040c else (if i<10 then 0x3e28e18386841a3020e183478b1c3c50c132c44b08387041a1028d08206840c3868f1c1c2081a384041c205841c3848d081c5861c384041038589082c70f121830e103c745183420d081c6840e342071a1060d0a10405101060c0834288082650f13304880e1c48d1c303881c3c68c08346040810707183020616284061a20609103440c0e1040c0834584081c48708343840e38204101078b083020c0a2c28c081820b082c207181830b0a1830510103c60a145041e2c2461c107048e14704 else 0x282040e38208181038808104060c1c2040c182080c18289102c384082030608204060c38204123860b0820787102470916106081010709122c247183860d083040c091c60e181060c181230c1c3020d082c20e0e1c48e103468610104081a20384103468610104881a343080820686122020d101840416105841a1428b181060d102c60416302041630204163020416302071c342071c3420e1a1250c0830207102878e12386041a3820e181070c082448e18106871c3020e181070c091460f)))) else (if i<17 then (if i<14 then (if i<12 then 0x103881c1c20a1a34605102840c0e1060708383870830689081c2071c1020a081c2040f1c585181038e08105040e103871e1c20b0a18307182420d18382098e28608912e30a1c3228810145060e1c68d1a10206101040e1618288103470d141830590387471a3c70e1e2440e162020e1f1c6051c1020718207051c204040e1c48f1c3030b102038f0c3038d0e1068d0a103890c384080814707081c70b1010604081c4040e202072010407201c787082048b082844b0c2020712103890e2458e else (if i<13 then 0x20747182c208103058a10102080e1050a0824384091828a0c3060b0834404181068708182870c106070c2c2881a2020c0e1060d081c60d081c60d081c60d083038d0820685161440d0a1c207081c207081c2070e1060d0a1c784102020c1a1438c081c60410202071834208092c30f08405060e1068d1a30408103870d1a1420e0a10705081c20b0a1830c96103841a1020d081028812382041c106842030208081c4080830684182020820202050e12447081030f101060808306840e20208 else 0x30585081020c0a1c307081858c0c1820512346050e10207081230710302ca0e1c20a082858a14182040e2460d0c10308102c58b0e18586121420710342860e106080a182070e343870c1438d0e103881a204040c205840b1c48e181020c1410384082030818302861a1c3840e107060e104840e343840a343841a14384081038c1014308081c20c0a18287122038408102c71a20384081838716202060c305840a205840c1c287081820710206061020608162028a0828685183830d08346c6)) else (if i<15 then 0x3070c0c2c288081c204081c40e1a2c2860e2c305183440d0e105040e1c60414145848c2638c1a10604122c204102060c142c28a0810246181c604081c68c0b1860c1010507082638c1a10409163058b08102841820687082820810143840c10209181c3040c1020c1a203841410209122460b082c60c08104040e302040e1630c182c20714103060e3060816105040a1c605141c58408202071410207102068c0a1c40a082058c14285050e246081810504102060b16285040e24489121460c else (if i<16 then 0x1c2081c1c708161044b1a1038a082a607142c6840a1e38814382860f1c70d102040a1838684103038c081048918346041a1460514103878e38705141c58510204088f1c4090e1458b0a2c689161c204111c48b0e10289122060708306081618206081c5070a283848c3870c161020c082c58b0c1870c8c1c20a141020918306041810209963420d1814584081e48c0c3230c0c28204081c40e1c2c28608103881c345850c1858c0c1434b1c302051614404081a58c1c10585101030a1218484 else 0x2838b1630487121830718244860e2038a0c2c6090e1848410183481c24584183060c1c142081a2c307091870b1a3424608346840c1c585141c28b16102881a1020d0e3020610302040a1c68c1810607081440d0c2c3061e383840a2068c0e18306982060408346070e2c28698206040e2250c1a205850c2c60414104061c3c38410306860e1830b183850d083828c08287050a30607082c60e18102850c365868e20389162c28a1c3470e12306041a2048d0c2058a16202081c20584081468e))) else (if i<20 then (if i<18 then 0x1c3860c2c5060c1428d1a2c4080814309162c4080828404161c20d1a2020708347080e106860e2020610205840e102881234685902c40410346871010305122868e1620207122c207082040808183898e1828d181c386121038408305870e1430718102479434304101c3050e205040c184071820208112038408383840c1868b10102870e2050d0c1440d101c68b0e104081a10387083020608244870e10389081c2070e1820c08302840e1c20b16243890c2c58b18243890c2c60d161838a else (if i<19 then 0x2a448142868d1a3468e912240e1c2848a142860a10102071c1428816204091238704163020e142c20d08382870838387081070708342860c387870e1038e081040414102471e14404903230b1a1c28610243840828387082a38f0820246101c5860c12388181424610105870c14285142a448142850e10286c58a1440c0a14306102058d1a3850b0a3858808163c91a38286102c684142448c1a342070e105040e104848e3868d1c2c2048c2868e92305840e382041010306161c3060c2c386 else 0x2258d181024a0e10787082050c18283040e1c3070c1c20b161c4070e1068e0e10207183438a14103840e10306081c6860e1850816386041234604141858418102871a302060a202070e183051c3450d081c68708385841c14604081c50d081c204081040896345041410288132c688103020a081068d1a10384101c207161c5840c40804081038d0c1c306181828408306060c1830f081c209123c2048f1c50918306c70a1440c0820584081c5890e2820708284891e1020a1c3c2070828509)) else (if i<21 then 0x283051034404081c3870e1840f0e3020e08307050c1c608081c7060c182070e1c3860c182880e3020d08183061224606082440708183051e10384141020a0e1c6840e10287181c30614182870e1830d201c2040f286860e185860c1460c121030e121060d121060c121c2079414404183038b0c1870f0c14384081c687181430f0e107860e106060c1820708205070e282071e1c2060e38605101040d1c20586102430b1c20584123060d081c40a081c50d0e1040a1c14204122450a143060d else (if i<22 then 0x2858a121c30c0c24308102858c122c50a142c38b18305090c2440a183058b0c2460c102060b1628508183058c142850a102c6071228308162c608102830a0c2c60a121c3090e3060c142848b14244871628306131c48b161c60a082860414183060c244891a105860c1c508102c50a0828408123060c162c5070e284460e1040c142830b1618509121038b181c5051414506141820c10205870c1c604141858612243040e18386083020e9638708081020b082448c0a1030a0c142070c1c306 else 0x81020408102050a142440a1428509102850a102050a0a2044a1a2c5870e2830b14183090a24488103458b1a1c38a0c1458a0c184850f14408103058a)))))
def parentV (i : Nat) := field parentD 7 219 i
def fnat {α : Type} (n : Nat) (k : Nat → α) : α :=
 match n with
 | 0 => k 0
 | n+1 => k (n+1)
def fbank {α : Type} : Bank → (Bank → α) → α
 | [],k => k []
 | w::ws,k => fnat w.toNat fun n => fbank ws fun xs => k (BitVec.ofNat 24 n :: xs)
theorem fnat_eq {α : Type} (x : Nat) (k : Nat → α) : fnat x k = k x := by cases x <;> rfl
theorem fbank_eq {α : Type} (ws : Bank) (k : Bank → α) : fbank ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => simp only [fbank,fnat_eq,ih,BitVec.ofNat_toNat,BitVec.setWidth_eq]
def checkParent (s i : Nat) : Bool :=
  fbank (state s i) fun ws => fnat (hintJ s i) fun b =>
  (List.range (hintJ s (i+1)-b)).all fun j =>
    let v := b+j
    fnat (chartInfo (hintVal v) &&& 0xffffff) fun ac =>
    numSum ac ws == parentV v
theorem checkedEntry {s i j} (parent : checkParent s i = true)
    (hj : j < hintJ s (i+1) - hintJ s i) :
    numSum (chartInfo (hintVal (hintJ s i+j)) &&& 0xffffff) (state s i) =
      parentV (hintJ s i+j) :=
by
  simp only [checkParent,fbank_eq,fnat_eq] at parent
  exact beq_iff_eq.mp (List.all_eq_true.mp parent j (List.mem_range.mpr hj))
theorem as_sum (ac : Nat) (ws : List Sig) :
    numSum ac ws = (ws.map (fun w => numFee ac w.toNat)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws h => simp only [numSum,List.map_cons,List.sum_cons,h]
def tickUp (old pa pb pz : Nat) (ka kb : Bool) :=
  old + pz - (if ka then 0 else pa) - (if kb then 0 else pb)
def lenUp (n : Nat) (ka kb : Bool) := n-1+ka.toNat+kb.toNat
theorem cheap_perm {xs ys : List Nat} (h : xs.Perm ys) : xs.sum=ys.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons,ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ h j => exact h.trans j
theorem cost_step (ac : Nat) {ws : Bank} {a b : Sig}
    (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) (d ka kb : Bool) :
    numSum ac (childTwo ws a b d ka kb) =
      tickUp (numSum ac ws) (numFee ac a.toNat) (numFee ac b.toNat)
        (numFee ac (bin d a b).toNat) ka kb ∧
    (childTwo ws a b d ka kb).length = lenUp ws.length ka kb := by
  have hb' : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
  have eq := (List.perm_cons_erase ha).trans (List.Perm.cons a (List.perm_cons_erase hb'))
  have se := cheap_perm (eq.map (fun w => numFee ac w.toNat))
  have le := eq.length_eq
  cases ka <;> cases kb <;>
    simp only [List.map_cons,List.sum_cons,List.length_cons] at se le <;>
    simp only [as_sum,tickUp,lenUp,childTwo,kept,List.map_cons,List.sum_cons,List.length_cons,
      ite_true,ite_false,Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Nat.sub_zero,Nat.add_zero] <;> constructor <;> omega
def oneChart (s i : Nat) (ws : Bank) (a b : Sig) (d ka kb : Bool) (j : Nat) :=
 fnat (hintJ s i) fun b0 => fnat (b0+j) fun v =>
 fnat (hintVal v) fun c => fnat (chartInfo c) fun info => fnat (info &&& 0xffffff) fun ac =>
 let n:=parentV v + numFee ac (bin d a b).toNat - (if ka then 0 else numFee ac a.toNat) - (if kb then 0 else numFee ac b.toNat)
 fnat n fun m => decide (j<hintJ s (i+1)-b0 ∧ c<243 ∧ m<64 ∧ m+(s-1)<(info >>> 24)+(ws.length-1+ka.toNat+kb.toNat))
def strictNode (ck : TapeChart) (s i : Nat) := fbank (state s i) fun ws =>
 !ws.contains goal && decide ws.Nodup &&
 (s==0 || fnat (tapeWidth s i) fun w => fnat (tapeData s i) fun v =>
 fnat (coverage ws).2.1.toNat fun solo => fnat ws.length fun n =>
 readTape w (probeMove frontier ck s i ws) v (enumerateWith (pairMoves s n ws (BitVec.ofNat 144 solo)) ws))
theorem strictNode_eq (ck : TapeChart) (s i : Nat) :
  strictNode ck s i = tapeCheckAt frontier ck tapeWidth tapeData s i := by
  simp only [strictNode,fbank_eq,fnat_eq,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rfl
theorem one_good {s i : Nat} (j : Nat) {a b : Sig} {d ka kb : Bool}
    (parent : checkParent s i = true) (ha : a ∈ state s i) (hb : b ∈ state s i) (hne : a ≠ b)
    (ok : oneChart s i (state s i) a b d ka kb j = true) :
    quickCut (hintVal (hintJ s i+j)) (childTwo (state s i) a b d ka kb) (s-1) = true := by
  simp only [oneChart,fnat_eq,decide_eq_true_eq] at ok
  have p := checkedEntry parent ok.1
  let c := hintVal (hintJ s i + j)
  let ac := chartInfo c &&& 0xffffff
  have ⟨cs,ls⟩ := cost_step ac ha hb hne d ka kb
  have pol : numSum ac (state s i) = parentV (hintJ s i+j) := p
  rw [pol] at cs
  simp only [quickCut,decide_eq_true_eq]
  change c<243 ∧ numSum ac _ <64 ∧ numSum ac _ + (s-1) < (chartInfo c >>> 24)+_
  rw [cs,ls]
  exact ⟨ok.2.1,ok.2.2.1,ok.2.2.2⟩
theorem per_cut (s i : Nat) (parent : checkParent s i = true) (j : Nat) :
    HookSound s (state s i) (fun a b d ka kb => oneChart s i (state s i) a b d ka kb j) := by
  intro a ha b hb d ka kb ne fresh nd ok
  intro k hk run
  exact quickCut_sound _ (one_good j parent ha hb ne ok) hk (Project.list_mrun run _ nd rfl)
def tapeRow (s i : Nat) := checkParent s i && strictNode oneChart s i
def tapeRows (s : Nat) (i : Nat) : Nat → Bool
  | 0 => true
  | n+1 => tapeRow s (i+n) && tapeRows s i n
theorem tapeRows_at {s i n j} (h : tapeRows s i n = true) (lo : i ≤ j) (hi : j < i+n) : tapeRow s j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [tapeRows,Bool.and_eq_true] at h
    by_cases e : j=i+n
    · simpa [e] using h.1
    · exact ih h.2 (by omega)
theorem tapeRows_join {s i a b} (h : tapeRows s i a = true) (t : tapeRows s (i+a) b = true) :
    tapeRows s i (a+b) = true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [tapeRows,Bool.and_eq_true] at t
    change tapeRow s (i+(a+b)) && tapeRows s i (a+b) = true
    rw [Bool.and_eq_true]
    exact ⟨by simpa only [Nat.add_assoc] using t.1, ih t.2⟩
end Pnp3229Certificate.PackedFront
namespace Pnp3229Certificate.PackedFront
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b5_0 : tapeRows 5 0 1 = true := by decide +kernel
theorem all5 : tapeRows 5 0 (count 5) = true :=
  b5_0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b6_0 : tapeRows 6 0 3 = true := by decide +kernel
theorem all6 : tapeRows 6 0 (count 6) = true :=
  b6_0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b7_0 : tapeRows 7 0 5 = true := by decide +kernel
theorem all7 : tapeRows 7 0 (count 7) = true :=
  b7_0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b8_0 : tapeRows 8 0 14 = true := by decide +kernel
theorem all8 : tapeRows 8 0 (count 8) = true :=
  b8_0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b9_0 : tapeRows 9 0 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b9_20 : tapeRows 9 20 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b9_40 : tapeRows 9 40 19 = true := by decide +kernel
theorem all9 : tapeRows 9 0 (count 9) = true :=
  (@tapeRows_join 9 0 40 19 (@tapeRows_join 9 0 20 20 b9_0 b9_20) b9_40)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_0 : tapeRows 10 0 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_20 : tapeRows 10 20 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_40 : tapeRows 10 40 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_60 : tapeRows 10 60 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_80 : tapeRows 10 80 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_100 : tapeRows 10 100 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_120 : tapeRows 10 120 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_140 : tapeRows 10 140 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_160 : tapeRows 10 160 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_180 : tapeRows 10 180 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_200 : tapeRows 10 200 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_220 : tapeRows 10 220 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b10_240 : tapeRows 10 240 18 = true := by decide +kernel
theorem all10 : tapeRows 10 0 (count 10) = true :=
  (@tapeRows_join 10 0 160 98 (@tapeRows_join 10 0 80 80 (@tapeRows_join 10 0 40 40 (@tapeRows_join 10 0 20 20 b10_0 b10_20) (@tapeRows_join 10 40 20 20 b10_40 b10_60)) (@tapeRows_join 10 80 40 40 (@tapeRows_join 10 80 20 20 b10_80 b10_100) (@tapeRows_join 10 120 20 20 b10_120 b10_140))) (@tapeRows_join 10 160 80 18 (@tapeRows_join 10 160 40 40 (@tapeRows_join 10 160 20 20 b10_160 b10_180) (@tapeRows_join 10 200 20 20 b10_200 b10_220)) b10_240))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_0 : tapeRows 11 0 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_20 : tapeRows 11 20 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_40 : tapeRows 11 40 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_60 : tapeRows 11 60 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_80 : tapeRows 11 80 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_100 : tapeRows 11 100 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_120 : tapeRows 11 120 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_140 : tapeRows 11 140 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_160 : tapeRows 11 160 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_180 : tapeRows 11 180 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_200 : tapeRows 11 200 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_220 : tapeRows 11 220 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_240 : tapeRows 11 240 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_260 : tapeRows 11 260 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_280 : tapeRows 11 280 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_300 : tapeRows 11 300 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_320 : tapeRows 11 320 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_340 : tapeRows 11 340 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_360 : tapeRows 11 360 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_380 : tapeRows 11 380 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_400 : tapeRows 11 400 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_420 : tapeRows 11 420 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_440 : tapeRows 11 440 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_460 : tapeRows 11 460 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_480 : tapeRows 11 480 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_500 : tapeRows 11 500 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_520 : tapeRows 11 520 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b11_540 : tapeRows 11 540 20 = true := by decide +kernel
theorem all11 : tapeRows 11 0 (count 11) = true :=
  (@tapeRows_join 11 0 320 240 (@tapeRows_join 11 0 160 160 (@tapeRows_join 11 0 80 80 (@tapeRows_join 11 0 40 40 (@tapeRows_join 11 0 20 20 b11_0 b11_20) (@tapeRows_join 11 40 20 20 b11_40 b11_60)) (@tapeRows_join 11 80 40 40 (@tapeRows_join 11 80 20 20 b11_80 b11_100) (@tapeRows_join 11 120 20 20 b11_120 b11_140))) (@tapeRows_join 11 160 80 80 (@tapeRows_join 11 160 40 40 (@tapeRows_join 11 160 20 20 b11_160 b11_180) (@tapeRows_join 11 200 20 20 b11_200 b11_220)) (@tapeRows_join 11 240 40 40 (@tapeRows_join 11 240 20 20 b11_240 b11_260) (@tapeRows_join 11 280 20 20 b11_280 b11_300)))) (@tapeRows_join 11 320 160 80 (@tapeRows_join 11 320 80 80 (@tapeRows_join 11 320 40 40 (@tapeRows_join 11 320 20 20 b11_320 b11_340) (@tapeRows_join 11 360 20 20 b11_360 b11_380)) (@tapeRows_join 11 400 40 40 (@tapeRows_join 11 400 20 20 b11_400 b11_420) (@tapeRows_join 11 440 20 20 b11_440 b11_460))) (@tapeRows_join 11 480 40 40 (@tapeRows_join 11 480 20 20 b11_480 b11_500) (@tapeRows_join 11 520 20 20 b11_520 b11_540))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_0 : tapeRows 12 0 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_20 : tapeRows 12 20 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_40 : tapeRows 12 40 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_60 : tapeRows 12 60 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_80 : tapeRows 12 80 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_100 : tapeRows 12 100 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_120 : tapeRows 12 120 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_140 : tapeRows 12 140 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_160 : tapeRows 12 160 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_180 : tapeRows 12 180 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_200 : tapeRows 12 200 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_220 : tapeRows 12 220 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_240 : tapeRows 12 240 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_260 : tapeRows 12 260 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b12_280 : tapeRows 12 280 1 = true := by decide +kernel
theorem all12 : tapeRows 12 0 (count 12) = true :=
  (@tapeRows_join 12 0 160 121 (@tapeRows_join 12 0 80 80 (@tapeRows_join 12 0 40 40 (@tapeRows_join 12 0 20 20 b12_0 b12_20) (@tapeRows_join 12 40 20 20 b12_40 b12_60)) (@tapeRows_join 12 80 40 40 (@tapeRows_join 12 80 20 20 b12_80 b12_100) (@tapeRows_join 12 120 20 20 b12_120 b12_140))) (@tapeRows_join 12 160 80 41 (@tapeRows_join 12 160 40 40 (@tapeRows_join 12 160 20 20 b12_160 b12_180) (@tapeRows_join 12 200 20 20 b12_200 b12_220)) (@tapeRows_join 12 240 40 1 (@tapeRows_join 12 240 20 20 b12_240 b12_260) b12_280)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b13_0 : tapeRows 13 0 20 = true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b13_20 : tapeRows 13 20 1 = true := by decide +kernel
theorem all13 : tapeRows 13 0 (count 13) = true :=
  (@tapeRows_join 13 0 20 1 b13_0 b13_20)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem b14_0 : tapeRows 14 0 2 = true := by decide +kernel
theorem all14 : tapeRows 14 0 (count 14) = true :=
  b14_0
theorem checked : ∀ s ≤ 14, ∀ i < frontier.count s, tapeRow s i = true := by
  intro s hs i hi
  have t : tapeRows s 0 (count s) = true := by
    interval_cases s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact all5
    · exact all6
    · exact all7
    · exact all8
    · exact all9
    · exact all10
    · exact all11
    · exact all12
    · exact all13
    · exact all14
  change i < count s at hi
  exact tapeRows_at (j:=i) t (by omega) (by simpa only [Nat.zero_add] using hi)
theorem resolved (s : Nat) (hs : s≤14) (i : Nat) (hi : i<count s) :
    Impossible goal s (state s i).toFinset := by
  apply tapeCertificate_sound (F:=frontier) (checkOne:=oneChart) (width:=tapeWidth) (data:=tapeData)
    (cap:=14) actions_verified _ _ s hs i hi
  · intro t ht j hj v
    have h := ((Bool.and_eq_true _ _).mp (checked t ht j hj)).1
    exact per_cut t j h v
  · intro t ht j hj
    have h := ((Bool.and_eq_true _ _).mp (checked t ht j hj)).2
    exact (strictNode_eq oneChart t j) ▸ h
theorem nine : Impossible goal 14 roots9.toFinset := by
  have h := resolved 14 (by omega) 1 (by decide +kernel)
  have e : (frontier.state 14 1).toFinset = roots9.toFinset := sameWords_sound (by decide +kernel)
  exact e ▸ h
theorem ten : Impossible goal 14 roots.toFinset := by
  have h := resolved 14 (by omega) 0 (by decide +kernel)
  have e : (frontier.state 14 0).toFinset = roots.toFinset := sameWords_sound (by decide +kernel)
  exact e ▸ h
end Pnp3229Certificate.PackedFront

end PEqualNP.Outside.L_meta_3229

theorem PEqualNP.Outside.L_meta_3229 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x2 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.false]) = Bool.false) ∧ ∃ x2 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.true]) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [x3.testBit (0 : ℕ) || x3.testBit (3 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → x1 x3 → (∀ x8 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x2 x3 x8 = Bool.true) → ¬∀ x9 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x2 x3 x9 = Bool.false := by
  dsimp only
  intro c len hm _ _ yes no
  obtain ⟨k,hk,h | h⟩ := PEqualNP.Outside.L_meta_3229.Pnp3229Certificate.reduce_exact c hm yes no
  · exact PEqualNP.Outside.L_meta_3229.Pnp3229Certificate.PackedFront.ten k (by omega) h
  · exact PEqualNP.Outside.L_meta_3229.Pnp3229Certificate.PackedFront.nine k (by omega) h
