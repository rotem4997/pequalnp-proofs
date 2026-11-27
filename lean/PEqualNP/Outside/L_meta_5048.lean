import PEqualNP.Defs
-- The parametric switch bound below is from Great-Leader-of-ISLAND in accepted PR 6762.

namespace PEqualNP.Outside.L_meta_5048_aux

namespace CoThetaFreeCore

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def base (join a b : Bool) : Bool := if join then a || b else a && b

inductive Kind where
  | conj | disj | leftOnly | rightOnly

def applyKind : Kind → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .leftOnly, a, b => a && !b
  | .rightOnly, a, b => !a && b

def normalizedKind : Bool → Bool → Bool → Kind
  | false, false, false => .conj
  | false, false, true  => .leftOnly
  | false, true, false  => .rightOnly
  | false, true, true   => .disj
  | true, false, false  => .disj
  | true, false, true   => .rightOnly
  | true, true, false   => .leftOnly
  | true, true, true    => .conj

theorem normalization_table : ∀ join a0 b0 a b : Bool,
    phase (base join a0 b0) (base join a b) =
    applyKind (normalizedKind join a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem inversion_table : ∀ a0 a : Bool, phase (!a0) (!a) = phase a0 a := by decide

variable {ρ : Type}

def norm (empty : ρ) (a : ρ → Bool) : ρ → Bool := fun i => phase (a empty) (a i)

theorem normalize_binary (empty : ρ) (join : Bool) (a b : ρ → Bool) :
    norm empty (fun i => base join (a i) (b i)) =
    fun i => applyKind (normalizedKind join (a empty) (b empty)) (norm empty a i) (norm empty b i) := by
  funext i
  exact normalization_table join (a empty) (b empty) (a i) (b i)

theorem normalize_unary (empty : ρ) (a : ρ → Bool) :
    norm empty (fun i => !(a i)) = norm empty a := by
  funext i
  exact inversion_table (a empty) (a i)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

/-- A straight-line program with an explicit count of its binary steps.
    Newly computed wires are prepended, and existing wires may be shared. -/
inductive Ordinary (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Ordinary raw 0 raw
  | inv {n ws a} (pre : Ordinary raw n ws) (ha : a ∈ ws) :
      Ordinary raw n ((fun i => !(a i)) :: ws)
  | binary {n ws a b} (pre : Ordinary raw n ws) (join : Bool) (ha : a ∈ ws) (hb : b ∈ ws) :
      Ordinary raw (n+1) ((fun i => base join (a i) (b i)) :: ws)

inductive Free (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Free raw 0 raw
  | binary {n ws a b} (pre : Free raw n ws) (kind : Kind) (ha : a ∈ ws) (hb : b ∈ ws) :
      Free raw (n+1) ((fun i => applyKind kind (a i) (b i)) :: ws)

theorem simulate_all_wires (empty : ρ) {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Ordinary raw n ws) :
    ∃ ys, Free (raw.map (norm empty)) n ys ∧
          ∀ a ∈ ws, norm empty a ∈ ys := by
  induction run with
  | start =>
    exact ⟨_, Free.start, fun a ha => List.mem_map_of_mem ha⟩
  | @inv n ws a pre ha ih =>
    obtain ⟨ys,hy,old⟩ := ih
    refine ⟨ys,hy,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_unary]
      exact old a ha
    · exact old w was
  | @binary n ws a b pre join ha hb ih =>
    obtain ⟨ys,hy,old⟩ := ih
    let kk := normalizedKind join (a empty) (b empty)
    have fresh := Free.binary hy kk (old a ha) (old b hb)
    refine ⟨_,fresh,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_binary]
      simp [kk]
    · exact List.mem_cons_of_mem _ (old w was)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

def absentBit : ρ → Bool := fun _ => false
def ins {α : Type} (a : α) (U : α → Prop) : α → Prop := fun v => v = a ∨ U v

/-- Work backwards through a DAG, preserving only the distinct signals still
    needed. U may contain either of the two inputs, representing reuse. -/
inductive Live (goal : ρ → Bool) : Nat → ((ρ → Bool) → Prop) → Prop
  | stop : Live goal 0 (fun v => v=goal)
  | step {k U a b} (kind : Kind) (ab : a≠b)
      (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Live goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Live goal (k+1) (ins a (ins b U))

private theorem same_result (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) (a i)) = a ∨
    (fun i => applyKind kind (a i) (a i)) = absentBit := by
  cases kind with
  | conj => left; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => right; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem zero_left (kind : Kind) (b : ρ → Bool) :
    (fun i => applyKind kind false (b i)) = b ∨
    (fun i => applyKind kind false (b i)) = absentBit := by
  cases kind with
  | conj => right; rfl
  | disj => left; funext i; cases b i <;> rfl
  | leftOnly => right; rfl
  | rightOnly => left; funext i; cases b i <;> rfl

private theorem zero_right (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) false) = a ∨
    (fun i => applyKind kind (a i) false) = absentBit := by
  cases kind with
  | conj => right; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => left; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem free_keeps_raw {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Free raw n ws) {v} (h : v∈raw) : v∈ws := by
  induction run with
  | start => exact h
  | binary _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem rewind {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Live goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Live goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Live goal (k+1) (ins a (ins b U)) :=
          Live.step kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

theorem Live.separates {goal : ρ → Bool} {S k} (h : Live goal k S)
    (pos neg : ρ) (different : goal pos≠goal neg) :
    ∃ w, S w ∧ w pos≠w neg := by
  induction h with
  | stop => exact ⟨goal,rfl,different⟩
  | @step n U a b kind hab ha hb hf tail ih =>
    obtain ⟨w,hw,diff⟩ := ih
    rcases hw with eq | inU
    · subst w
      by_cases ea : a pos=a neg
      · refine ⟨b,Or.inr (Or.inl rfl),?_⟩
        intro eb
        apply diff
        change applyKind kind (a pos) (b pos) = applyKind kind (a neg) (b neg)
        rw [ea,eb]
      · exact ⟨a,Or.inl rfl,ea⟩
    · exact ⟨w,Or.inr (Or.inr inU),diff⟩

private def eraseOnce {α : Type} [DecidableEq α] (v : α) : List α → List α
  | [] => []
  | x::xs => if x=v then xs else x::eraseOnce v xs

private theorem erase_len {α : Type} [DecidableEq α] (v : α) (xs : List α) (h : v∈xs) :
    (eraseOnce v xs).length+1=xs.length := by
  induction xs with
  | nil => simp at h
  | cons a l ih =>
    by_cases e : a=v
    · simp [eraseOnce,e]
    · have hit : v∈l := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      have hlen := ih hit
      simp [eraseOnce,e]
      omega

private theorem erase_preserves {α : Type} [DecidableEq α] {v w : α} (hw : w≠v)
    (xs : List α) (hin : w∈xs) : w∈eraseOnce v xs := by
  induction xs with
  | nil => simp at hin
  | cons a l ih =>
    by_cases e : a=v
    · subst a
      simpa [eraseOnce] using (List.mem_cons.mp hin).resolve_left hw
    · simp only [eraseOnce,if_neg e,List.mem_cons]
      rcases List.mem_cons.mp hin with eq | old
      · exact Or.inl eq
      · exact Or.inr (ih old)

theorem Live.width_cover {goal : ρ → Bool} {S k} (h : Live goal k S) :
    ∃ xs : List (ρ→Bool), xs.length≤k+1 ∧ ∀ w, S w → w∈xs := by
  classical
  induction h with
  | stop =>
    refine ⟨[goal],by simp,?_⟩
    intro w eq
    change w=goal at eq
    subst w
    simp
  | @step n U a b kind hab ha hb fresh tail ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    obtain ⟨xs,len,sub⟩ := ih
    have inside : z∈xs := sub z (Or.inl rfl)
    have reduced := erase_len z xs inside
    refine ⟨a::b::eraseOnce z xs,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · intro w hw
      rcases hw with eq | eq | hu
      · simp [eq]
      · simp [eq]
      · have ne : w≠z := by
          intro eq
          apply fresh
          exact Or.inr (Or.inr ((congrArg U eq).mp hu))
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (erase_preserves ne xs (sub w (Or.inr hu))))

end CoThetaFreeCore

namespace CoThetaFreeCore

def primary {ι : Type} (j : ι) (x : ι → Bool) := x j

theorem necessary_primary {ι : Type} {goal : (ι → Bool) → Bool} {S k}
    (run : Live goal k S) (j : ι)
    (inputs : ∀ w, S w → w=absentBit ∨ ∃ i, w=primary i)
    (sens : ∃ p n, goal p≠goal n ∧ ∀ i, i≠j → p i=n i) :
    S (primary j) := by
  obtain ⟨p,n,diff,rest⟩ := sens
  obtain ⟨wire,hw,dis⟩ := run.separates p n diff
  rcases inputs wire hw with c | ⟨i,c⟩
  · subst wire
    exact (dis rfl).elim
  · subst wire
    by_cases eq : i=j
    · exact eq ▸ hw
    · exact (dis (rest i eq)).elim

def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def neigh (i : Fin 7) : Fin 7 := match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | _ => 1

def single (j : Fin 7) (i : Fin 7) : Bool := i == neigh j
def edgeRow (j : Fin 7) (i : Fin 7) : Bool := single j i || i==j

theorem theta_rows : ∀ j : Fin 7, theta (single j) = false ∧ theta (edgeRow j) = true := by decide

theorem theta_needs_every_input {S k} (run : Live theta k S)
    (inputs : ∀ w, S w → w=absentBit ∨ ∃ i, w=primary i) : ∀ j, S (primary j) := by
  intro j
  apply necessary_primary run j inputs
  refine ⟨single j,edgeRow j,?_,?_⟩
  · rw [(theta_rows j).1,(theta_rows j).2]
    decide
  · intro i h
    simp [edgeRow,h]

end CoThetaFreeCore

namespace CoThetaFreeCore

structure TraceGate (ρ : Type) where
  kind : Kind
  left : ρ → Bool
  right : ρ → Bool

def TraceGate.value {ρ} (g : TraceGate ρ) : ρ → Bool :=
  fun r => applyKind g.kind (g.left r) (g.right r)

def registered {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → Prop
  | [] => True
  | g::gs => g.left∈raw ∧ g.right∈raw ∧ registered (g.value::raw) gs

def traceWires {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → List (ρ→Bool)
  | [] => raw
  | g::gs => traceWires (g.value::raw) gs

def restrict {ρ σ} (lift : σ→ρ) (wire : ρ→Bool) : σ→Bool := fun i => wire (lift i)

def disappears {ρ σ} (lift : σ→ρ) (g : TraceGate ρ) : Prop :=
  restrict lift g.left=absentBit ∨ restrict lift g.right=absentBit

noncomputable def remaining {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 0 else 1) + remaining lift gs

noncomputable def saved {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 1 else 0) + saved lift gs

theorem accounted {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    remaining lift gs + saved lift gs = gs.length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [remaining,saved,h] <;> omega

private theorem trace_step {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    {init pool : List (σ→Bool)} {n} (live : Free init n pool)
    (ha : restrict lift g.left∈pool) (hb : restrict lift g.right∈pool)
    (hz : absentBit∈pool) :
    ∃ k ys, (disappears lift g → k=0) ∧ (¬disappears lift g → k=1) ∧
      Free init (n+k) ys ∧ (∀ a∈pool,a∈ys) ∧ restrict lift g.value∈ys := by
  classical
  by_cases drop : disappears lift g
  · refine ⟨0,pool,fun _ => rfl,fun n => (n drop).elim,live,fun _ h => h,?_⟩
    change (fun r => applyKind g.kind (restrict lift g.left r) (restrict lift g.right r))∈pool
    rcases drop with lo|lo
    · rw [lo]
      rcases zero_left g.kind (restrict lift g.right) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr hb
      · exact (congrArg (fun v => v∈pool) e).mpr hz
    · rw [lo]
      rcases zero_right g.kind (restrict lift g.left) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr ha
      · exact (congrArg (fun v => v∈pool) e).mpr hz
  · exact ⟨1,_,fun h => (drop h).elim,fun _ => rfl,Free.binary live g.kind ha hb,
      fun _ h => List.mem_cons_of_mem _ h,List.mem_cons_self⟩

theorem restrict_trace {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ))
    {start : List (ρ→Bool)} {init pool : List (σ→Bool)} {n}
    (good : registered start gs) (pre : Free init n pool) (hz : absentBit∈pool)
    (known : ∀ w∈start,restrict lift w∈pool) :
    ∃ ys, Free init (n+remaining lift gs) ys ∧ ∀ w∈traceWires start gs,restrict lift w∈ys := by
  classical
  induction gs generalizing start pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons g gs ih =>
    rcases good with ⟨left,right,rest⟩
    obtain ⟨k,mid,zeroCost,oneCost,step,old,output⟩ :=
      trace_step lift g pre (known _ left) (known _ right) hz
    have fresh (w) (h : w∈g.value::start) : restrict lift w∈mid := by
      rcases List.mem_cons.mp h with e|h
      · exact (congrArg (fun v => restrict lift v∈mid) e).mpr output
      · exact old _ (known _ h)
    obtain ⟨ys,tail,available⟩ := ih rest step (old _ hz) fresh
    refine ⟨ys,?_,available⟩
    by_cases d : disappears lift g
    · have eq := zeroCost d
      simpa [remaining,d,eq] using tail
    · have eq := oneCost d
      simpa [remaining,d,eq,Nat.add_assoc] using tail

end CoThetaFreeCore

namespace CoThetaFreeCore

theorem trace_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    traceWires raw (a++b)=traceWires (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => rfl
  | cons x xs ih => exact ih (x.value::raw)

theorem registered_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    registered raw (a++b) ↔ registered raw a ∧ registered (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => simp [registered,traceWires]
  | cons x xs ih =>
    simp only [List.cons_append,registered,traceWires,ih]
    simp [and_assoc]

theorem trace_of_free {ρ} {raw ws : List (ρ→Bool)} {n} (p : Free raw n ws) :
    ∃ gs : List (TraceGate ρ), gs.length=n ∧ registered raw gs ∧ traceWires raw gs=ws := by
  induction p with
  | start => exact ⟨[],rfl,True.intro,rfl⟩
  | @binary n ws a b pre kind ha hb ih =>
    obtain ⟨s,len,reg,eq⟩ := ih
    let g : TraceGate ρ := ⟨kind,a,b⟩
    refine ⟨s++[g],by simp [len],(registered_append _ _ _).2 ⟨reg,?_⟩,?_⟩
    · simpa [eq,registered,g] using And.intro ha hb
    · rw [trace_append,eq]
      rfl

def reads {ρ} (g : TraceGate ρ) (wire : ρ→Bool) : Prop := g.left=wire ∨ g.right=wire

theorem reading_zero_disappears {ρ σ} (lift : σ→ρ) {g : TraceGate ρ} {wire}
    (drop : restrict lift wire=absentBit) (h : reads g wire) : disappears lift g := by
  rcases h with e|e
  · exact Or.inl ((congrArg (restrict lift) e).trans drop)
  · exact Or.inr ((congrArg (restrict lift) e).trans drop)

theorem two_zero_propagate {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    (l : restrict lift g.left=absentBit) (r : restrict lift g.right=absentBit) :
    restrict lift g.value=absentBit := by
  funext i
  change applyKind g.kind (restrict lift g.left i) (restrict lift g.right i) = false
  rw [l,r]
  cases g.kind <;> rfl

end CoThetaFreeCore
namespace CoThetaFreeCore

def agreeOutside {ρ : Type} (E : (ρ → Bool) → Prop) (r s : ρ)
    (ws : List (ρ → Bool)) : Prop := ∀ w∈ws, ¬ E w → w r = w s

theorem trace_barrier {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    (gs : List (TraceGate ρ)) {raw} (well : registered raw gs)
    (sources : agreeOutside E r s raw)
    (blocked : ∀ g∈gs, (E g.left ∨ E g.right) → g.value r=g.value s) :
    agreeOutside E r s (traceWires raw gs) := by
  classical
  induction gs generalizing raw with
  | nil => exact sources
  | cons g gs ih =>
    rcases well with ⟨hl,hr,rest⟩
    have same : g.value r=g.value s := by
      by_cases h : E g.left ∨ E g.right
      · exact blocked g (by simp) h
      · have le := sources g.left hl (fun x => h (Or.inl x))
        have re := sources g.right hr (fun x => h (Or.inr x))
        simp only [TraceGate.value,le,re]
    apply ih rest _ (fun t ht => blocked t (List.mem_cons_of_mem _ ht))
    intro w hw n
    rcases List.mem_cons.mp hw with e|h
    · exact e ▸ same
    · exact sources w h n

theorem reader_witness {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (well : registered raw gs)
    (sources : agreeOutside E r s raw) (hOut : out∈traceWires raw gs)
    (clear : ¬ E out) (diff : out r ≠ out s) :
    ∃ g∈gs, (E g.left ∨ E g.right) ∧ g.value r≠g.value s := by
  classical
  apply Classical.byContradiction
  intro bad
  apply diff
  apply trace_barrier E r s gs well sources _ out hOut clear
  intro g hg he
  apply Classical.byContradiction
  intro ne
  exact bad ⟨g,hg,he,ne⟩

theorem second_reader {ρ : Type} (x : ρ→Bool) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (gate : TraceGate ρ)
    (well : registered raw gs) (source : agreeOutside (·=x) r s raw)
    (hOut : out∈traceWires raw gs) (distinct : out≠x) (diff : out r ≠ out s)
    (masked : gate.value r=gate.value s) :
    ∃ g∈gs, reads g x ∧ g≠gate := by
  obtain ⟨g,hg,reader,ne⟩ := reader_witness (·=x) r s well source hOut distinct diff
  exact ⟨g,hg,reader,fun e => ne (e ▸ masked)⟩

end CoThetaFreeCore
namespace CoThetaFreeCore

def sufficient {ρ : Type} (raw : List (ρ→Bool)) (out : ρ→Bool)
    (gs : List (TraceGate ρ)) : Prop := registered raw gs ∧ out∈traceWires raw gs

def freshTrace {ρ : Type} (raw : List (ρ→Bool)) : List (TraceGate ρ)→Prop
  | [] => True
  | g::gs => g.value∉raw ∧ freshTrace (g.value::raw) gs

theorem trace_subset {ρ : Type} (gs : List (TraceGate ρ)) {as bs}
    (sub : ∀ w∈as,w∈bs) :
    (registered as gs → registered bs gs) ∧
      ∀ w∈traceWires as gs,w∈traceWires bs gs := by
  induction gs generalizing as bs with
  | nil => exact ⟨fun _ => True.intro,sub⟩
  | cons g tail ih =>
    have next : ∀ w∈g.value::as,w∈g.value::bs := by
      intro w hw
      rcases List.mem_cons.mp hw with e|h
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons_of_mem _ (sub _ h)
    have h := ih next
    exact ⟨fun ok => ⟨sub _ ok.1,sub _ ok.2.1,h.1 ok.2.2⟩,h.2⟩

theorem simplify_trace {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    (gs : List (TraceGate ρ)) (solves : sufficient raw out gs) :
    ∃ ts : List (TraceGate ρ), sufficient raw out ts ∧ freshTrace raw ts ∧
      (ts.length≤gs.length ∧ (¬freshTrace raw gs → ts.length<gs.length)) := by
  classical
  induction gs generalizing raw with
  | nil => exact ⟨[],solves,True.intro,Nat.le_refl _,fun bad => (bad True.intro).elim⟩
  | cons g gs ih =>
    obtain ⟨reg,output⟩ := solves
    rcases reg with ⟨left,right,rest⟩
    by_cases seen : g.value∈raw
    · have cover : ∀ w∈g.value::raw,w∈raw := by
        intro w h
        rcases List.mem_cons.mp h with e|h
        · exact e ▸ seen
        · exact h
      have reduce := trace_subset gs cover
      obtain ⟨ts,ok,fresh,le,_⟩ := ih ⟨reduce.1 rest,reduce.2 out output⟩
      refine ⟨ts,ok,fresh,?_,?_⟩ <;> simp only [List.length_cons] <;> omega
    · obtain ⟨ts,ok,fresh,le,lt⟩ := ih ⟨rest,output⟩
      refine ⟨g::ts,⟨⟨left,right,ok.1⟩,ok.2⟩,⟨seen,fresh⟩,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro bad
        have h := lt (fun f => bad (And.intro seen f))
        simp only [List.length_cons]
        omega

theorem trace_minimal_fresh {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    {gs : List (TraceGate ρ)} (solves : sufficient raw out gs)
    (minimal : ∀ ts, sufficient raw out ts → gs.length≤ts.length) : freshTrace raw gs := by
  classical
  apply Classical.byContradiction
  intro bad
  obtain ⟨ts,h,_,_,lt⟩ := simplify_trace gs solves
  have small := lt bad
  have big := minimal ts h
  omega

theorem fresh_outputs {ρ : Type} {raw : List (ρ→Bool)} {gs : List (TraceGate ρ)}
    (fresh : freshTrace raw gs) (g : TraceGate ρ) (hg : g∈gs) : g.value∉raw := by
  induction gs generalizing raw with
  | nil => simp at hg
  | cons t ts ih =>
    rcases fresh with ⟨ft,fs⟩
    rcases List.mem_cons.mp hg with e|h
    · exact e ▸ ft
    · exact fun hRaw => ih fs h (List.mem_cons_of_mem _ hRaw)

end CoThetaFreeCore
namespace CoThetaFreeCore

def pairCode (op : Kind) (sw : Bool) (u v : Bool) : Bool :=
  if sw then applyKind op v u else applyKind op u v

theorem pair_collision (A B : Kind) : ∀ (sa sb : Bool),
    ∃ a b c d : Bool, (a,b)≠(c,d) ∧
      pairCode A sa a b=pairCode A sa c d ∧ pairCode B sb a b=pairCode B sb c d := by
  cases A <;> cases B <;> decide

theorem joint_reader_code {ρ : Type} (x y : ρ→Bool) (different : x≠y) (g : TraceGate ρ)
    (rx : reads g x) (ry : reads g y) :
    ∃ sw : Bool, ∀ i, g.value i=pairCode g.kind sw (x i) (y i) := by
  rcases rx with xl|xr <;> rcases ry with yl|yr
  · exact (different (xl.symm.trans yl)).elim
  · exact ⟨false,by simp [TraceGate.value,pairCode,xl,yr]⟩
  · exact ⟨true,by simp [TraceGate.value,pairCode,xr,yl]⟩
  · exact (different (xr.symm.trans yr)).elim

theorem two_joint_readers_impossible {ρ τ : Type} (x y out : ρ→Bool)
    (raw : List (ρ→Bool)) (gs : List (TraceGate ρ)) (A B : TraceGate ρ)
    (rxA : reads A x) (ryA : reads A y) (rxB : reads B x) (ryB : reads B y)
    (different : x≠y) (notPrimary : out≠x ∧ out≠y)
    (well : registered raw gs) (available : out∈traceWires raw gs)
    (point : Bool→Bool→τ→ρ)
    (px : ∀ a b j, x (point a b j)=a)
    (py : ∀ a b j, y (point a b j)=b)
    (fixed : ∀ a b c d j, agreeOutside (fun f => f=x ∨ f=y) (point a b j) (point c d j) raw)
    (separate : ∀ a b c d : Bool, (a,b)≠(c,d) → ∃ j : τ, out (point a b j)≠out (point c d j)) :
    ∃ g∈gs, (reads g x ∨ reads g y) ∧ g≠A ∧ g≠B := by
  classical
  obtain ⟨sa,saCode⟩ := joint_reader_code x y different A rxA ryA
  obtain ⟨sb,sbCode⟩ := joint_reader_code x y different B rxB ryB
  obtain ⟨a,b,c,d,ne,ca,cb⟩ := pair_collision A.kind B.kind sa sb
  obtain ⟨j,away⟩ := separate a b c d ne
  have eA : A.value (point a b j)=A.value (point c d j) := by
    simpa only [saCode,px,py] using ca
  have eB : B.value (point a b j)=B.value (point c d j) := by
    simpa only [sbCode,px,py] using cb
  have badOut : ¬(out=x ∨ out=y) := fun e => e.elim notPrimary.1 notPrimary.2
  obtain ⟨g,hg,read,diff⟩ := reader_witness (fun f => f=x ∨ f=y) _ _ well
    (fixed a b c d j) available badOut away
  refine ⟨g,hg,?_,fun eq => diff (eq ▸ eA),fun eq => diff (eq ▸ eB)⟩
  rcases read with (h|h)|(h|h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

end CoThetaFreeCore


namespace CoPetersenThetaGeometry

def nine (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def theta (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def embedding (j : Fin 6) : List Nat := match j.val with
  | 0 => [2, 8, 3, 1, 6, 7, 5]
  | 1 => [3, 5, 8, 2, 7, 4, 0]
  | 2 => [8, 0, 5, 3, 4, 6, 1]
  | 3 => [5, 1, 0, 8, 6, 7, 2]
  | 4 => [0, 2, 1, 5, 7, 4, 3]
  | _ => [1, 3, 2, 0, 4, 6, 8]

def cycleEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | _ => 5

def subEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 4
  | 1 => 6
  | 2 => 7
  | 3 => 4
  | 4 => 6
  | _ => 7

def outerNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 8
  | 4 => 5
  | _ => 0

def shortNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 3
  | 1 => 8
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | _ => 2

def sensitive : List Nat := [2, 0, 16, 2, 2, 20, 2, 10, 2, 16, 2, 32, 2, 80, 2, 130, 2, 258, 4, 1, 1, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 2, 9, 8, 2, 2, 0, 2, 8, 2, 18, 2, 34, 2, 72, 2, 128, 2, 258, 4, 5, 4, 18, 16, 4, 4, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 8, 1, 1, 10, 1, 5, 1, 8, 1, 0, 1, 40, 1, 65, 1, 129, 1, 257, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 1, 0, 1, 65, 1, 128, 1, 256, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 2, 0, 2, 130, 2, 256, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 4, 0, 4, 260, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 8, 0]

def plant (j : Fin 6) (m : Nat) : Nat :=
  (List.range 7).foldl (fun val i => if m.testBit i then
    val ||| (1 <<< ((embedding j).getD i 0)) else val) 0

theorem theta_slice : ∀ (j : Fin 6) (r : Fin 128),
    nine (plant j r.val) = theta r.val ∧
    (plant j r.val).testBit (cycleEnd j)=false ∧
    (plant j r.val).testBit (subEnd j)=false := by decide +kernel

theorem every_input_has_slice : ∀ v : Fin 9, ∃ j : Fin 6,
    cycleEnd j=v.val ∨ subEnd j=v.val := by decide

def sensRow (p q : Fin 9) (v : Bool) : Nat :=
  sensitive.getD (2*(9*p.val+q.val)+v.toNat) 0

theorem sensitive_at_both : ∀ (p q : Fin 9), p≠q → ∀ v : Bool,
    let r := sensRow p q v
    r.testBit p.val=false ∧ r.testBit q.val=v ∧
    nine r=false ∧ nine (r ||| (1 <<< p.val))=true := by decide +kernel

def panel (p q : Bool) : Bool × Bool × Bool := (p&&q,(p&&q)||p,(p&&q)||q)

theorem slice_panels : ∀ (j : Fin 6) (p q : Bool),
    let r := (if p then 1 <<< cycleEnd j else 0) ||| (if q then 1 <<< subEnd j else 0)
    (nine r, nine (r ||| (1 <<< outerNeighbor j)), nine (r ||| (1 <<< shortNeighbor j))) = panel p q := by
  decide +kernel

inductive Kind where | conj | disj | leftOnly | rightOnly
def binary : Kind → Bool → Bool → Bool
  | .conj,a,b => a&&b
  | .disj,a,b => a||b
  | .leftOnly,a,b => a && !b
  | .rightOnly,a,b => !a && b

theorem unbalanced_code (kind : Kind) : ∀ (a b c d : Bool),
    ¬[(binary kind false false,a),(binary kind false true,b),
      (binary kind true false,c),(binary kind true true,d)].Nodup := by
  cases kind <;> decide

end CoPetersenThetaGeometry
namespace CoThetaNine
open CoThetaFreeCore
open CoPetersenThetaGeometry (nine sensRow cycleEnd subEnd outerNeighbor shortNeighbor)

abbrev Input := Fin 512
def vtx (i : Fin 9) (r : Input) : Bool := r.val.testBit i.val
def ans (r : Input) : Bool := nine r.val
def vertices : List (Input→Bool) := absentBit::List.ofFn vtx

def row (n : Nat) : Input := ⟨n % 512,Nat.mod_lt _ (by decide)⟩
def index (n : Nat) : Fin 9 := ⟨n % 9,Nat.mod_lt _ (by decide)⟩
def ep (j : Fin 6) := index (cycleEnd j)
def eqp (j : Fin 6) := index (subEnd j)
def low (p q : Fin 9) (v : Bool) : Input := row (sensRow p q v)
def high (p q : Fin 9) (v : Bool) : Input := row ((low p q v).val ||| (1 <<< p.val))

theorem sens_data : ∀ (p q : Fin 9), p≠q → ∀ b : Bool,
    vtx p (low p q b)=false ∧ vtx p (high p q b)=true ∧
    vtx q (low p q b)=b ∧ vtx q (high p q b)=b ∧
    ans (low p q b)≠ans (high p q b) ∧
    ∀ t : Fin 9, t≠p → vtx t (low p q b)=vtx t (high p q b) := by decide +kernel

theorem distinct_raw : ∀ i j : Fin 9, i≠j → ∃ r : Input, vtx i r≠vtx j r := by
  decide +kernel

theorem not_raw : ∀ i : Fin 9, ∃ r : Input, ans r≠vtx i r := by decide +kernel

theorem distinct_inputs {i j : Fin 9} (ne : i≠j) : vtx i≠vtx j := by
  obtain ⟨r,d⟩ := distinct_raw i j ne
  exact fun h => d (congrFun h r)

theorem not_input (i : Fin 9) : ans≠vtx i := by
  obtain ⟨r,d⟩ := not_raw i
  exact fun h => d (congrFun h r)

theorem agree_on_vertices (E : (Input→Bool)→Prop) (r s : Input)
    (ok : ∀ i : Fin 9, ¬E (vtx i) → vtx i r=vtx i s) :
    agreeOutside E r s vertices := by
  intro w hw h
  rcases List.mem_cons.mp hw with z|h2
  · subst w
    rfl
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h2
    subst w
    exact ok i h

def point (j : Fin 6) (a b : Bool) (t : Fin 3) : Input :=
  let u := (if a then 1 <<< cycleEnd j else 0) ||| (if b then 1 <<< subEnd j else 0)
  row (match t.val with
    | 0 => u
    | 1 => u ||| (1 <<< outerNeighbor j)
    | _ => u ||| (1 <<< shortNeighbor j))

theorem panel_data : ∀ (j : Fin 6), ep j≠eqp j ∧
    (∀ a b t, vtx (ep j) (point j a b t)=a ∧ vtx (eqp j) (point j a b t)=b) ∧
    (∀ a b c d t, ∀ i : Fin 9, i≠ep j → i≠eqp j →
      vtx i (point j a b t)=vtx i (point j c d t)) ∧
    (∀ a b c d : Bool, (a,b)≠(c,d) → ∃ t : Fin 3, ans (point j a b t)≠ans (point j c d t)) := by
  decide +kernel

theorem third_joint_reader (j : Fin 6) (gs : List (TraceGate Input)) (A B : TraceGate Input)
    (rxA : reads A (vtx (ep j))) (ryA : reads A (vtx (eqp j)))
    (rxB : reads B (vtx (ep j))) (ryB : reads B (vtx (eqp j)))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, (reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) ∧ g≠A ∧ g≠B := by
  obtain ⟨distinct,axis,other,apart⟩ := panel_data j
  apply two_joint_readers_impossible (vtx (ep j)) (vtx (eqp j)) ans vertices gs A B
    rxA ryA rxB ryB (distinct_inputs distinct) ⟨not_input _,not_input _⟩ well out
    (point j) (fun a b t => (axis a b t).1) (fun a b t => (axis a b t).2) _ apart
  intro a b c d t
  apply agree_on_vertices
  intro i ni
  exact other a b c d t i (fun e => ni (Or.inl (congrArg vtx e)))
    (fun e => ni (Or.inr (congrArg vtx e)))

theorem masks_some_value (op : CoThetaFreeCore.Kind) : ∀ sw : Bool, ∃ v : Bool,
    ∀ a b : Bool, pairCode op sw a v=pairCode op sw b v := by
  cases op <;> decide

theorem another_raw_reader {p q : Fin 9} (ne : p≠q) (gs : List (TraceGate Input))
    (gate : TraceGate Input) (rx : reads gate (vtx p)) (ry : reads gate (vtx q))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) ∧ g≠gate := by
  obtain ⟨sw,code⟩ := joint_reader_code _ _ (distinct_inputs ne) gate rx ry
  obtain ⟨b,masked⟩ := masks_some_value gate.kind sw
  obtain ⟨pl,ph,ql,qh,diff,fixed⟩ := sens_data p q ne b
  have source : agreeOutside (fun w => w=vtx p) (low p q b) (high p q b) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fixed i (fun e => ni (congrArg vtx e))
  have mask : gate.value (low p q b)=gate.value (high p q b) := by
    simpa only [code,pl,ph,ql,qh] using masked false true
  exact second_reader (vtx p) (low p q b) (high p q b) gate well source out (not_input p) diff mask

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def neighborIndex (p : Fin 9) := index (p.val+1)
theorem neighbor_diff : ∀ p : Fin 9, p≠neighborIndex p := by decide

theorem a_raw_reader (p : Fin 9) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) := by
  let q := neighborIndex p
  have ne : p≠q := neighbor_diff p
  obtain ⟨_,_,_,_,diff,fix⟩ := sens_data p q ne false
  have source : agreeOutside (fun w => w=vtx p) (low p q false) (high p q false) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fix i (fun e => ni (congrArg vtx e))
  obtain ⟨g,hg,h,_⟩ := reader_witness (·=vtx p) _ _ well source out (not_input p) diff
  exact ⟨g,hg,h⟩

def ThreeReaders {ρ : Type} (P : TraceGate ρ→Prop) (gs : List (TraceGate ρ)) : Prop :=
  ∃ A∈gs, ∃ B∈gs, ∃ C∈gs, P A ∧ P B ∧ P C ∧ A≠B ∧ A≠C ∧ B≠C

theorem three_for_pair (j : Fin 6) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs)
    (known : (∃ A∈gs, ∃ B∈gs, reads A (vtx (ep j)) ∧ reads B (vtx (ep j)) ∧ A≠B) ∨
             (∃ A∈gs, ∃ B∈gs, reads A (vtx (eqp j)) ∧ reads B (vtx (eqp j)) ∧ A≠B)) :
    ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs := by
  classical
  have ne := (panel_data j).1
  by_cases shared : ∃ J∈gs, reads J (vtx (ep j)) ∧ reads J (vtx (eqp j))
  · obtain ⟨J,hJ,Jp,Jq⟩ := shared
    obtain ⟨A,hA,Ap,AJ⟩ := another_raw_reader ne gs J Jp Jq well out
    obtain ⟨B,hB,Bq,BJ⟩ := another_raw_reader ne.symm gs J Jq Jp well out
    by_cases e : A=B
    · subst B
      obtain ⟨C,hC,read,CJ,CA⟩ := third_joint_reader j gs J A Jp Jq Ap Bq well out
      exact ⟨J,hJ,A,hA,C,hC,Or.inl Jp,Or.inl Ap,read,AJ.symm,CJ.symm,CA.symm⟩
    · exact ⟨J,hJ,A,hA,B,hB,Or.inl Jp,Or.inl Ap,Or.inr Bq,AJ.symm,BJ.symm,e⟩
  · rcases known with ⟨A,hA,B,hB,Ap,Bp,AB⟩|⟨A,hA,B,hB,Aq,Bq,AB⟩
    · obtain ⟨C,hC,Cq⟩ := a_raw_reader (eqp j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inl Ap,Or.inl Bp,Or.inr Cq,AB,
        fun e => shared ⟨A,hA,Ap,e ▸ Cq⟩,fun e => shared ⟨B,hB,Bp,e ▸ Cq⟩⟩
    · obtain ⟨C,hC,Cp⟩ := a_raw_reader (ep j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inr Aq,Or.inr Bq,Or.inl Cp,AB,
        fun e => shared ⟨A,hA,e ▸ Cp,Aq⟩,fun e => shared ⟨B,hB,e ▸ Cp,Bq⟩⟩

end CoThetaNine
namespace CoThetaFreeCore

theorem fresh_ports {ρ : Type} {ws : List (ρ→Bool)} (g : TraceGate ρ)
    (hl : g.left∈ws) (hr : g.right∈ws) (hz : absentBit∈ws) (fresh : g.value∉ws) :
    g.left≠absentBit ∧ g.right≠absentBit ∧ g.left≠g.right := by
  refine ⟨?_,?_,?_⟩
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_left g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_right g.kind g.left with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hl
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases same_result g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz

noncomputable def vanishing {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :=
  gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))

theorem saved_eq_length {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    saved lift gs = (vanishing lift gs).length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [saved,vanishing,h] at * <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

theorem endpoint_in_slice : ∀ p : Fin 9, ∃ j : Fin 6, p=ep j ∨ p=eqp j := by decide

theorem ans_not_zero : ans≠absentBit := by
  intro e
  have bad := congrFun e (row 3)
  have test : ans (row 3)=true := by decide
  exact Bool.noConfusion (test.symm.trans bad)

theorem fresh_slice_head {g : TraceGate Input} {tail : List (TraceGate Input)}
    (h : sufficient vertices ans (g::tail)) (fresh : freshTrace vertices (g::tail)) :
    ∃ j : Fin 6, ThreeReaders (fun t => reads t (vtx (ep j)) ∨ reads t (vtx (eqp j))) (g::tail) := by
  obtain ⟨nonL,nonR,different⟩ := fresh_ports g h.1.1 h.1.2.1 (List.mem_cons_self) fresh.1
  have rawL := (List.mem_cons.mp h.1.1).resolve_left nonL
  have rawR := (List.mem_cons.mp h.1.2.1).resolve_left nonR
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp rawL
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp rawR
  have xy : x≠y := fun eq => different (ex.symm.trans ((congrArg vtx eq).trans ey))
  have rx : reads g (vtx x) := Or.inl ex.symm
  have ry : reads g (vtx y) := Or.inr ey.symm
  obtain ⟨s,hs,sx,other⟩ := another_raw_reader xy _ g rx ry h.1 h.2
  obtain ⟨j,side⟩ := endpoint_in_slice x
  refine ⟨j,three_for_pair j h.1 h.2 ?_⟩
  rcases side with eq|eq
  · exact Or.inl ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩
  · exact Or.inr ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩

theorem nonempty_solution {gs : List (TraceGate Input)} (h : sufficient vertices ans gs) : gs≠[] := by
  intro e
  subst gs
  have m : ans∈vertices := h.2
  rcases List.mem_cons.mp m with z|r
  · exact ans_not_zero z
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp r
    exact not_input i eq.symm

end CoThetaNine
namespace CoThetaBits
open CoThetaFreeCore

abbrev Width := 440
abbrev Bits := BitVec Width
abbrev Wire := Bits × Bits
abbrev Row := Bool × Fin Width
def zero : Wire := (0,0)
def full : Bits := BitVec.allOnes Width
def target : Wire := (full,0)

def den (wire : Wire) (r : Row) : Bool :=
  (if r.1 then wire.1 else wire.2).getLsbD r.2.val

def gate : Kind → Wire → Wire → Wire
  | .conj,a,b => (a.1 &&& b.1,a.2 &&& b.2)
  | .disj,a,b => (a.1 ||| b.1,a.2 ||| b.2)
  | .leftOnly,a,b => (a.1 &&& ~~~b.1,a.2 &&& ~~~b.2)
  | .rightOnly,a,b => (~~~a.1 &&& b.1,~~~a.2 &&& b.2)

theorem den_injective {a b : Wire} (h : den a=den b) : a=b := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (true,⟨i,hi⟩)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (false,⟨i,hi⟩)

theorem den_gate (kind : Kind) (a b : Wire) :
    den (gate kind a b) = fun i => applyKind kind (den a i) (den b i) := by
  funext r
  obtain ⟨side,i⟩ := r
  cases kind <;> cases side <;>
    simp [den,gate,applyKind,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,i.isLt]

theorem den_zero : den zero = absentBit := by
  funext r
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,zero,absentBit]

theorem den_target (r : Row) : den target r = r.1 := by
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,target,full,BitVec.getLsbD_allOnes,i.isLt]

def sep (w : Wire) : Bits := w.1 ^^^ w.2

def coverage : List Wire → Bits
  | [] => 0
  | w::ws => sep w ||| coverage ws

theorem bit_covered {l : List Wire} {w : Wire} (hw : w∈l) (i : Fin Width)
    (h : den w (true,i) ≠ den w (false,i)) : (coverage l).getLsbD i.val=true := by
  induction l with
  | nil => simp at hw
  | cons a xs ih =>
    rw [coverage,BitVec.getLsbD_or]
    rcases List.mem_cons.mp hw with e|mem
    · subst a
      have hd : w.1.getLsbD i.val ≠ w.2.getLsbD i.val := h
      simp only [sep,BitVec.getLsbD_xor]
      cases hp : w.1.getLsbD i.val <;> cases hn : w.2.getLsbD i.val <;> simp_all
    · simp [ih mem]

theorem live_coverage {k} {S : (Row → Bool) → Prop} (l : List Wire)
    (h : Live (den target) k S) (sub : ∀ w, S w → ∃ v∈l, den v=w) :
    coverage l = full := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin Width := ⟨i,hi⟩
  have ne : den target (true,j) ≠ den target (false,j) := by simp [den_target]
  obtain ⟨w,hw,hd⟩ := h.separates (true,j) (false,j) ne
  obtain ⟨v,hv,eq⟩ := sub w hw
  have h1 := bit_covered hv j (eq.symm ▸ hd)
  simpa [full,BitVec.getLsbD_allOnes,hi,j] using h1

end CoThetaBits

namespace CoThetaFreeCore

theorem length_of_cover {α : Type} (xs ys : List α) (nd : xs.Nodup)
    (sub : ∀ a∈xs, a∈ys) : xs.length≤ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have parts := List.nodup_cons.mp nd
    have has : a∈ys := sub a (by simp)
    have hl := erase_len a ys has
    have nextOK : xs.length≤(eraseOnce a ys).length := ih (eraseOnce a ys) parts.2 (by
      intro x hx
      have ne : x≠a := fun eq => parts.1 (eq ▸ hx)
      exact erase_preserves ne ys (sub x (List.mem_cons_of_mem _ hx)))
    simp only [List.length_cons]
    omega

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

def Rep (ws : List Wire) (S : (Row→Bool)→Prop) : Prop :=
  ∀ f, S f ↔ ∃ w∈ws, den w=f

private theorem mem_rep {S ws} (rep : Rep ws S) (w : Wire) : w∈ws ↔ S (den w) := by
  constructor
  · intro h
    exact (rep _).2 ⟨w,h,rfl⟩
  · intro h
    obtain ⟨v,hv,e⟩ := (rep _).1 h
    exact den_injective e ▸ hv

private theorem den_nodup {ws : List Wire} (nd : ws.Nodup) : (ws.map den).Nodup := by
  induction ws with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.mp nd with ⟨hne,ht⟩
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih ht⟩
    intro hm
    obtain ⟨v,hv,e⟩ := List.mem_map.mp hm
    exact hne (den_injective e ▸ hv)

theorem state_width {k S ws} (h : Live (den target) k S) (nd : ws.Nodup) (rep : Rep ws S) :
    ws.length≤k+1 := by
  obtain ⟨xs,hsize,hsub⟩ := h.width_cover
  have le := length_of_cover (ws.map den) xs (den_nodup nd) (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hf
    exact hsub f ((rep _).2 ⟨w,hw,eq⟩))
  simpa using Nat.le_trans le hsize

def trim (a b : Wire) (ws : List Wire) : List Wire :=
  ws.filter (fun w => w != a && w != b)

theorem mem_trim {w a b : Wire} {ws : List Wire} :
    w∈trim a b ws ↔ w∈ws ∧ w≠a ∧ w≠b := by simp [trim]

def allKinds : List Kind := [.conj,.disj,.leftOnly,.rightOnly]
def options (a b : Wire) : List (List Wire) := [[],[a],[b],[a,b]]

def testStep (k : Nat) (ws : List Wire) (nextOK : List Wire → Bool) : Bool :=
  ws.any fun a => ws.any fun b => a != b &&
    (allKinds.any fun kind =>
      let z := gate kind a b
      z != zero && !(ws.contains z) &&
        (options a b).any fun keep =>
          let out := z::(keep++trim a b ws)
          out.length≤k+1 && coverage out==full && nextOK out)

def certifiedSearch : Nat → List Wire → Bool
  | 0, ws => ws.contains target
  | k+1, ws => ws.contains target || (ws.length≤k+2 && testStep k ws (certifiedSearch k))

theorem step_hit {k ws nextOK a b keep kind} (ha : a∈ws) (hb : b∈ws)
    (ab : a≠b) (hk : keep∈options a b)
    (non : gate kind a b ≠zero) (fresh : gate kind a b∉ws)
    (len : (gate kind a b::(keep++trim a b ws)).length≤k+1)
    (cov : coverage (gate kind a b::(keep++trim a b ws))=full)
    (valid : nextOK (gate kind a b::(keep++trim a b ws))=true) : testStep k ws nextOK=true := by
  have hkind : kind∈allKinds := by cases kind <;> simp [allKinds]
  unfold testStep
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
  simp only [Bool.and_eq_true,bne_iff_ne,ab,true_and,List.any_eq_true,Bool.not_eq_true']
  refine ⟨ab,kind,hkind,?_⟩
  simp [non,fresh]
  have ct : keep.length + (trim a b ws).length ≤ k := by
    simp only [List.length_cons,List.length_append] at len
    omega
  exact ⟨keep,hk,by simp [ct,cov,valid]⟩

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

noncomputable def kept (a b : Wire) (U : (Row→Bool)→Prop) : List Wire := by
  classical
  exact (if U (den a) then [a] else []) ++ (if U (den b) then [b] else [])

theorem is_option (a b : Wire) (U : (Row→Bool)→Prop) : kept a b U∈options a b := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,options,p,q]

theorem mem_kept {v a b : Wire} {U : (Row→Bool)→Prop} :
    v∈kept a b U ↔ (v=a ∧ U (den a)) ∨ (v=b ∧ U (den b)) := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,p,q]

theorem edit_member {a b v : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    v∈(kept a b U ++ trim a b ws) ↔ U (den v) := by
  classical
  constructor
  · intro hm
    rcases List.mem_append.mp hm with inK | inR
    · rcases mem_kept.mp inK with ⟨e,yes⟩ | ⟨e,yes⟩ <;> subst v <;> exact yes
    · obtain ⟨inside,na,nb⟩ := mem_trim.mp inR
      rcases (mem_rep rep v).1 inside with e | e | hu
      · exact (na (den_injective e)).elim
      · exact (nb (den_injective e)).elim
      · exact hu
  · intro hu
    by_cases ea : v=a
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inl ⟨ea,ea ▸ hu⟩)))
    by_cases eb : v=b
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inr ⟨eb,eb ▸ hu⟩)))
    apply List.mem_append.mpr
    right
    exact mem_trim.mpr ⟨(mem_rep rep v).2 (Or.inr (Or.inr hu)),ea,eb⟩

theorem edit_distinct {a b : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (ab : a≠b) (nd : ws.Nodup) : (kept a b U ++ trim a b ws).Nodup := by
  classical
  have ndr : (trim a b ws).Nodup := nd.filter _
  have ha : a∉trim a b ws := fun h => (mem_trim.mp h).2.1 rfl
  have hb : b∉trim a b ws := fun h => (mem_trim.mp h).2.2 rfl
  by_cases p : U (den a) <;> by_cases q : U (den b) <;>
    simp [kept,p,q,List.nodup_cons,ha,hb,ab,ndr]

theorem edit_rep {a b z : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    Rep (z::(kept a b U ++ trim a b ws)) (ins (den z) U) := by
  intro f
  constructor
  · intro hf
    rcases hf with e | hu
    · exact ⟨z,by simp,e.symm⟩
    · obtain ⟨v,hv,e⟩ := (rep f).1 (Or.inr (Or.inr hu))
      refine ⟨v,List.mem_cons_of_mem _ ((edit_member rep).2 ?_),e⟩
      exact e.symm ▸ hu
  · intro h
    obtain ⟨v,hv,e⟩ := h
    rcases List.mem_cons.mp hv with vz | tail
    · subst v
      exact Or.inl e.symm
    · exact Or.inr (e ▸ (edit_member rep).1 tail)

end CoThetaBits

namespace CoThetaFreeCore
variable {ρ : Type}

theorem Live.excludes_zero {goal : ρ→Bool} {k S} (h : Live goal k S)
    (ng : goal≠absentBit) : ¬S absentBit := by
  induction h with
  | stop => exact fun eq => ng eq.symm
  | step _ _ ha hb _ _ ih =>
    intro bad
    rcases bad with eq | eq | u
    · exact ha eq.symm
    · exact hb eq.symm
    · exact ih (Or.inr u)

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

private theorem target_nonzero : den target≠absentBit := by
  intro eq
  have q := congrFun eq (true,0)
  simp [den_target,absentBit] at q

theorem certified_complete {m S} (run : Live (den target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → certifiedSearch fuel ws=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have ht : target∈ws := (mem_rep rep target).2 rfl
    cases fuel <;> simp [certifiedSearch,ht]
  | @step m U a b kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      let out := z::(kept x y U ++ trim x y ws)
      have dg : den z=(fun i => applyKind kind (den x i) (den y i)) := den_gate _ _ _
      have zab : x≠y := fun e => ab (congrArg den e)
      have nz : z≠zero := by
        intro e
        have dz : (fun i => applyKind kind (den x i) (den y i))=absentBit :=
          dg.symm.trans ((congrArg den e).trans den_zero)
        exact tail.excludes_zero target_nonzero (Or.inl dz.symm)
      have nf : z∉ws := by
        intro hz
        have st := (mem_rep rep z).1 hz
        exact fresh (dg ▸ st)
      have nextRep : Rep out (ins (fun i => applyKind kind (den x i) (den y i)) U) := by
        have e := edit_rep (z:=z) rep
        rw [dg] at e
        exact e
      have nextNd : out.Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,edit_distinct zab nd⟩
        intro hz
        have inU := (edit_member rep).1 hz
        exact fresh (Or.inr (Or.inr (dg ▸ inU)))
      have width := state_width tail nextNd nextRep
      have cover := live_coverage out tail (fun f hf => (nextRep f).1 hf)
      have verdict := ih k (by omega) out nextNd nextRep
      have stepOk : testStep k ws (certifiedSearch k)=true :=
        step_hit hx hy zab (is_option x y U) nz nf (Nat.le_trans width (by omega)) cover verdict
      have current := Live.step kind ab ha hb fresh tail
      have max := state_width current nd rep
      have size : ws.length≤k+2 := by omega
      simp [certifiedSearch,size,stepOk]

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

def raw : List Wire := [(0xaa1404600a0270047003878002808c017f84fc07ff0fffe0050138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff,0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a),
(0xcc1807800c0380078003f8000300f00181ff3ff807f00ffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000,0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c),
(0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00007fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff,0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0),
(0xffe000000ffffff80000000003fffffe0007fffff800000007fffffc000003fff000000007ffffffffff000000003ffffffffc00000000,0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220),
(0xfffffffff00000000000000003fffffffff800000000000007fffffffffffc000000000007ffffffffffffffffffc00000000000000000,0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0),
(0xfffffffffffffffffffffffffc000000000000000000000007fffffffffffffffffffffff8000000000000000000000000000000000000,0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300),
(0xfffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000,0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00)]

def col (j : Fin 7) : Wire := raw[j.val]?.getD zero
def sample (r : Row) (j : Fin 7) : Bool := den (col j) r
def empty : Row := (false,0)
def start : List (Row→Bool) := (fun _ => false)::(fun _ => true)::raw.map den

def edgeWord : Wire := (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .conj (col 0) (col 2)) (gate .conj (col 1) (col 2))) (gate .conj (col 0) (col 3))) (gate .conj (col 3) (col 4))) (gate .conj (col 1) (col 4))) (gate .conj (col 0) (col 5))) (gate .conj (col 5) (col 6))) (gate .conj (col 1) (col 6)))

theorem edge_exact : edgeWord=target := by decide +kernel
theorem sample_correct (r : Row) : CoThetaFreeCore.theta (sample r)=den target r := by
  have h := congrFun (congrArg den edge_exact) r
  simp only [edgeWord,den_gate,applyKind] at h
  exact h

theorem raw_is_ofFn : List.ofFn col=raw := rfl
theorem raw_nodup : raw.Nodup := by decide +kernel
theorem low_raw : ∀ j : Fin 7, den (col j) empty=false := by decide +kernel

def privateIndex (j : Fin 7) : Fin Width := match j.val with
  | 0 => 4
  | 1 => 17
  | 2 => 1
  | 3 => 35
  | 4 => 71
  | 5 => 148
  | _ => 244

theorem private_row : ∀ j k : Fin 7,
    den (col k) (true,privateIndex j) ≠ den (col k) (false,privateIndex j) → k=j := by decide +kernel

private theorem indexed {v : Wire} (h : v∈raw) : ∃ j, col j=v := by
  rw [←raw_is_ofFn] at h
  exact List.mem_ofFn.mp h

theorem root_rep {k S} (h : Live (den target) k S)
    (inputs : ∀ f, S f → f=absentBit ∨ ∃ j, den (col j)=f) : Rep raw S := by
  have allcol (j : Fin 7) : S (den (col j)) := by
    let i := privateIndex j
    have diff : den target (true,i) ≠ den target (false,i) := by simp [den_target]
    obtain ⟨v,hv,hd⟩ := h.separates (true,i) (false,i) diff
    rcases inputs v hv with z | ⟨l,e⟩
    · subst v
      exact (hd rfl).elim
    · subst v
      obtain rfl := private_row j l hd
      exact hv
  intro f
  constructor
  · intro hf
    rcases inputs f hf with z | ⟨j,eq⟩
    · exact (h.excludes_zero target_nonzero (z ▸ hf)).elim
    · refine ⟨col j,?_,eq⟩
      rw [←raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · rintro ⟨v,hv,eq⟩
    obtain ⟨j,rfl⟩ := indexed hv
    exact eq ▸ allcol j

theorem root_input {f : Row→Bool} (hm : f∈start.map (norm empty)) :
    f=absentBit ∨ ∃ j, den (col j)=f := by
  obtain ⟨v,hin,rfl⟩ := List.mem_map.mp hm
  rcases List.mem_cons.mp hin with e | tail
  · subst v
    exact Or.inl rfl
  rcases List.mem_cons.mp tail with e | t
  · subst v
    exact Or.inl rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp t
  obtain ⟨j,rfl⟩ := indexed hw
  right
  refine ⟨j,?_⟩
  funext r
  simp [CoThetaFreeCore.norm,low_raw j,phase]

theorem no_small_ordinary (certificate : certifiedSearch 10 raw=false)
    {n ws} (program : Ordinary start n ws) (cost : n≤10) (out : den target∈ws) : False := by
  obtain ⟨ys,fre,contains⟩ := simulate_all_wires empty program
  have self : norm empty (den target)=den target := by
    funext r
    simp [CoThetaFreeCore.norm,den_target,empty,phase]
  have hin : den target∈ys := self ▸ contains _ out
  have rn : absentBit∈start.map (norm empty) := by
    change absentBit∈(absentBit::_)
    simp
  obtain ⟨m,S,le,live,sub⟩ :=
    rewind fre rn (Live.stop (goal:=den target)) (fun w eq => eq.symm ▸ hin)
  have rep := root_rep live (fun f hf => root_input (sub f hf))
  have yes := certified_complete live 10 (by omega) raw raw_nodup rep
  exact Bool.false_ne_true (certificate.symm.trans yes)

end CoThetaBits
namespace CoThetaFreeCore

theorem Free.map_rows {ρ σ : Type} (lift : σ→ρ)
    {init ws n} (run : @Free ρ init n ws) :
    Free (init.map (restrict lift)) n (ws.map (restrict lift)) := by
  induction run with
  | start => exact Free.start
  | @binary n ws a b pre kind ha hb ih =>
    have h1 := List.mem_map_of_mem (f:=restrict lift) ha
    have h2 := List.mem_map_of_mem (f:=restrict lift) hb
    exact Free.binary ih kind h1 h2

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

abbrev SmallInput := Fin 128
def raw7 (i : Fin 7) (r : SmallInput) : Bool := r.val.testBit i.val
def ans7 (r : SmallInput) : Bool := CoPetersenThetaGeometry.theta r.val
def vertices7 : List (SmallInput→Bool) := absentBit::List.ofFn raw7
def sliceLift (j : Fin 6) (r : SmallInput) : Input := row (CoPetersenThetaGeometry.plant j r.val)

def coord7 (j : Fin 6) (v : Fin 9) : Option (Fin 7) :=
  match j.val,v.val with
  | 0,2 => some 0
  | 0,8 => some 1
  | 0,3 => some 2
  | 0,1 => some 3
  | 0,6 => some 4
  | 0,7 => some 5
  | 0,5 => some 6
  | 1,3 => some 0
  | 1,5 => some 1
  | 1,8 => some 2
  | 1,2 => some 3
  | 1,7 => some 4
  | 1,4 => some 5
  | 1,0 => some 6
  | 2,8 => some 0
  | 2,0 => some 1
  | 2,5 => some 2
  | 2,3 => some 3
  | 2,4 => some 4
  | 2,6 => some 5
  | 2,1 => some 6
  | 3,5 => some 0
  | 3,1 => some 1
  | 3,0 => some 2
  | 3,8 => some 3
  | 3,6 => some 4
  | 3,7 => some 5
  | 3,2 => some 6
  | 4,0 => some 0
  | 4,2 => some 1
  | 4,1 => some 2
  | 4,5 => some 3
  | 4,7 => some 4
  | 4,4 => some 5
  | 4,3 => some 6
  | 5,1 => some 0
  | 5,3 => some 1
  | 5,2 => some 2
  | 5,0 => some 3
  | 5,4 => some 4
  | 5,6 => some 5
  | 5,8 => some 6
  | _,_ => none

theorem slice7_values : ∀(j : Fin 6) (r : SmallInput),
    ans (sliceLift j r)=ans7 r ∧ vtx (ep j) (sliceLift j r)=false ∧
    vtx (eqp j) (sliceLift j r)=false ∧
    ∀ i : Fin 9, vtx i (sliceLift j r)=
      match coord7 j i with | none => false | some k => raw7 k r := by decide +kernel

theorem slice_known (j : Fin 6) : ∀ w∈vertices, restrict (sliceLift j) w∈vertices7 := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
    subst w
    cases h : coord7 j i with
    | none =>
      have eq : restrict (sliceLift j) (vtx i)=absentBit := by
        funext r
        simpa [restrict,h,absentBit] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_self
    | some k =>
      have eq : restrict (sliceLift j) (vtx i)=raw7 k := by
        funext r
        simpa [restrict,h] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨k,rfl⟩)

def packBits (a b c d e f g : Bool) : SmallInput :=
  ⟨(a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat+64*g.toNat) % 128,
    Nat.mod_lt _ (by decide)⟩

def pack (x : Fin 7 → Bool) : SmallInput := packBits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

theorem pack_exact : ∀ a b c d e f g : Bool,
    let t := packBits a b c d e f g
    (raw7 0 t,raw7 1 t,raw7 2 t,raw7 3 t,raw7 4 t,raw7 5 t,raw7 6 t)=(a,b,c,d,e,f,g) := by
  intro a b c d e f g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem unpack (x : Fin 7→Bool) (j : Fin 7) : raw7 j (pack x)=x j := by
  have h := pack_exact (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  change (_,_,_,_,_,_,_) = (_,_,_,_,_,_,_) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := h
  have total : ∀ t : Fin 7, t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by decide
  rcases total j with e|e|e|e|e|e|e <;> subst j <;> assumption

theorem numeric_goal (r : SmallInput) : ans7 r=CoThetaFreeCore.theta (fun j => raw7 j r) := by
  rfl

def toRows (r : CoThetaBits.Row) := pack (CoThetaBits.sample r)

theorem numeric_target : restrict toRows ans7=CoThetaBits.den CoThetaBits.target := by
  funext r
  change ans7 (toRows r)=_
  rw [numeric_goal]
  have eq : (fun j => raw7 j (toRows r))=CoThetaBits.sample r :=
    funext (unpack (CoThetaBits.sample r))
  rw [eq]
  exact CoThetaBits.sample_correct r

theorem numeric_lower (cert : CoThetaBits.certifiedSearch 10 CoThetaBits.raw=false)
    {n ws} (run : Free vertices7 n ws) (goal : ans7∈ws) : 11≤n := by
  classical
  obtain ⟨m,S,le,live,sub⟩ := rewind (run.map_rows toRows) List.mem_cons_self
    (Live.stop (goal:=CoThetaBits.den CoThetaBits.target)) (by
      intro w e
      have h := List.mem_map_of_mem (f:=restrict toRows) goal
      rw [numeric_target] at h
      exact e ▸ h)
  have rep := CoThetaBits.root_rep live (by
    intro f h
    have w := sub f h
    obtain ⟨g,hg,eq⟩ := List.mem_map.mp w
    subst f
    rcases List.mem_cons.mp hg with z|other
    · subst g
      exact Or.inl rfl
    · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
      subst g
      exact Or.inr ⟨j,funext (fun r => (unpack (CoThetaBits.sample r) j).symm)⟩)
  apply Classical.byContradiction
  intro bad
  have pass := CoThetaBits.certified_complete live 10 (by omega) _ CoThetaBits.raw_nodup rep
  exact Bool.false_ne_true (cert.symm.trans pass)

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def SignedLower : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

theorem three_saved (j : Fin 6) {gs : List (TraceGate Input)}
    (three : ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs) :
    3≤saved (sliceLift j) gs := by
  classical
  obtain ⟨A,hA,B,hB,C,hC,rA,rB,rC,AB,AC,BC⟩ := three
  have zp : restrict (sliceLift j) (vtx (ep j))=absentBit :=
    funext (fun r => (slice7_values j r).2.1)
  have zq : restrict (sliceLift j) (vtx (eqp j))=absentBit :=
    funext (fun r => (slice7_values j r).2.2.1)
  have retain (g : TraceGate Input) (hg : g∈gs) (r : reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) :
      g∈vanishing (sliceLift j) gs := by
    have d : disappears (sliceLift j) g := r.elim (reading_zero_disappears _ zp) (reading_zero_disappears _ zq)
    simp [vanishing,hg,d]
  have nd : [A,B,C].Nodup := by simp [AB,AC,BC]
  have sub : ∀ t∈[A,B,C],t∈vanishing (sliceLift j) gs := by
    intro t h
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain A hA rA
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain B hB rB
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain C hC rC
    · simp at h
  rw [saved_eq_length]
  exact length_of_cover [A,B,C] _ nd sub

theorem residual_at_least_eleven (cert : SignedLower)
    (j : Fin 6) {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) :
    11≤remaining (sliceLift j) gs := by
  obtain ⟨ws,run,sub⟩ := restrict_trace (sliceLift j) gs ok.1
    (Free.start (raw:=vertices7)) List.mem_cons_self (slice_known j)
  have read := sub ans ok.2
  have ax : restrict (sliceLift j) ans=ans7 := funext (fun r => (slice7_values j r).1)
  rw [ax] at read
  simpa only [Nat.zero_add] using cert run read

theorem any_nine_lower (cert : SignedLower)
    {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) : 14≤gs.length := by
  classical
  obtain ⟨ts,solves,fresh,le,_⟩ := simplify_trace gs ok
  cases ts with
  | nil => exact (nonempty_solution solves rfl).elim
  | cons g tail =>
    obtain ⟨j,readers⟩ := fresh_slice_head solves fresh
    have gain := three_saved j readers
    have cost := residual_at_least_eleven cert j solves
    have eq := accounted (sliceLift j) (g::tail)
    omega

end CoThetaNine
namespace CoNatBench
abbrev Word := Nat × Nat
def project (w : CoThetaBits.Wire) : Word := (w.1.toNat,w.2.toNat)
def target := project CoThetaBits.target
def all := target.1
def sep (w : Word) := w.1 ^^^ w.2
def meet (a b : Word) : Word := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : Word) : Word := (a.1 ||| b.1,a.2 ||| b.2)
def skip (a b : Word) : Word := (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
def cover (ws : List Word) := ws.foldl (fun c w => c ||| sep w) 0
def pairs {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => false
  | x::xs => xs.any (f x) || pairs f xs
def successors (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  pairs (fun a b =>
    let rest := ws.filter (fun w => w != a && w != b)
    let base := cover rest
    let ca := base ||| sep a
    let cb := base ||| sep b
    let stay := n+1≤k+1
    let half := n≤k+1
    ([meet a b,join a b,skip a b,skip b a] : List Word).any fun z =>
      z != (0,0) && !(ws.contains z) &&
        (let cut := sep z
         ((base ||| cut)==all && next (z::rest)) ||
         (half && (ca ||| cut)==all && next (z::a::rest)) ||
         (half && (cb ||| cut)==all && next (z::b::rest)) ||
         (stay && next (z::a::b::rest)))) ws

-- Each visited state already separates every indexed positive/negative pair.
def search : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || successors k (search k) ws
end CoNatBench
namespace CoNatBench

def multiplicities : List Word → Nat×Nat
  | [] => (0,0)
  | w::ws =>
    let s := sep w
    let m := multiplicities ws
    (s ||| m.1, (s &&& m.1) ||| m.2)

def guarded (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  let bucket := multiplicities ws
  let once := bucket.1 ^^^ bucket.2
  let cols := ws.map fun w => (w,sep w &&& once)
  let half := n≤k+1
  let stay := n≤k
  pairs (fun a b =>
    let a0 := (a.2 &&& b.1.1)==0
    let a1 := (a.2 &&& b.1.1)==a.2
    let b0 := (b.2 &&& a.1.1)==0
    let b1 := (b.2 &&& a.1.1)==b.2
    let rest := ws.filter (fun w => w != a.1 && w != b.1)
    let base := cover rest
    let attempt (oka okb : Bool) (value : Unit → Word) :=
      (stay || (half && (oka || okb)) || (oka && okb)) &&
        (let z := value ()
         z != (0,0) && !(ws.contains z) &&
          ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
           (half && okb && next (z::a.1::rest)) ||
           (half && oka && next (z::b.1::rest)) ||
           (stay && next (z::a.1::b.1::rest))))
    attempt a1 b1 (fun _ => meet a.1 b.1) ||
      attempt a0 b0 (fun _ => join a.1 b.1) ||
      attempt a0 b1 (fun _ => skip a.1 b.1) ||
      attempt a1 b0 (fun _ => skip b.1 a.1)) cols

def guardedSearch : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || guarded k (guardedSearch k) ws

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

private theorem foldBits (ws : List Word) (i : Nat) (seed : Nat) :
    (ws.foldl (fun c w => c ||| sep w) seed).testBit i =
    (seed.testBit i || ws.any (fun w => (sep w).testBit i)) := by
  induction ws generalizing seed with
  | nil => simp
  | cons a xs ih =>
    simp [List.foldl_cons,ih,Nat.testBit_or,Bool.or_assoc]

theorem covered_iff (ws : List Word) (i : Nat) :
    (cover ws).testBit i=true ↔ ∃ w∈ws,(sep w).testBit i=true := by
  simp [cover,foldBits,List.any_eq_true]

private theorem firstMask (ws : List Word) (i : Nat) (w : Word)
    (h : w∈ws) (bit : (sep w).testBit i=true) : (multiplicities ws).1.testBit i=true := by
  induction ws with
  | nil => simp at h
  | cons a xs ih =>
    change (sep a ||| (multiplicities xs).1).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp h with e|h
    · exact Or.inl (e ▸ bit)
    · exact Or.inr (ih h)

private theorem secondMask (ws : List Word) (i : Nat) {a b : Word} (ab : a≠b)
    (ha : a∈ws) (hb : b∈ws) (da : (sep a).testBit i=true) (db : (sep b).testBit i=true) :
    (multiplicities ws).2.testBit i=true := by
  induction ws with
  | nil => simp at ha
  | cons h xs ih =>
    change ((sep h &&& (multiplicities xs).1) ||| (multiplicities xs).2).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    by_cases x : a=h
    · subst h
      have bt := (List.mem_cons.mp hb).resolve_left ab.symm
      exact Or.inl (by simp [Nat.testBit_and,da,firstMask xs i b bt db])
    · have atail := (List.mem_cons.mp ha).resolve_left x
      by_cases y : b=h
      · subst h
        exact Or.inl (by simp [Nat.testBit_and,db,firstMask xs i a atail da])
      · exact Or.inr (ih atail ((List.mem_cons.mp hb).resolve_left y))

def privateMask (ws : List Word) (a : Word) :=
  sep a &&& ((multiplicities ws).1 ^^^ (multiplicities ws).2)

theorem private_only {ws : List Word} {a : Word} (ha : a∈ws) {i : Nat}
    (h : (privateMask ws a).testBit i=true) :
    (sep a).testBit i=true ∧ ∀ b∈ws, b≠a → (sep b).testBit i=false := by
  simp only [privateMask,Nat.testBit_and,Nat.testBit_xor,Bool.and_eq_true] at h
  obtain ⟨bit,one⟩ := h
  have first := firstMask ws i a ha bit
  have no : (multiplicities ws).2.testBit i=false := by
    cases m : (multiplicities ws).2.testBit i <;> simp_all
  refine ⟨bit,?_⟩
  intro b hb diff
  cases d : (sep b).testBit i with
  | false => rfl
  | true => exact Bool.noConfusion (no.symm.trans (secondMask ws i diff hb ha d bit))

def wordGate : Kind→Word→Word→Word
  | .conj => meet
  | .disj => join
  | .leftOnly => skip
  | .rightOnly => fun a b => skip b a

def leftNeeds : Kind→Bool
  | .conj | .rightOnly => true
  | .disj | .leftOnly => false

theorem bit_rule (op : Kind) (a b : Word) (i : Nat) :
    (wordGate op a b).1.testBit i = applyKind op (a.1.testBit i) (b.1.testBit i) ∧
    (wordGate op a b).2.testBit i = applyKind op (a.2.testBit i) (b.2.testBit i) := by
  cases op <;> simp only [wordGate,meet,join,skip,applyKind,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]
  all_goals
    cases a.1.testBit i <;> cases b.1.testBit i <;> cases a.2.testBit i <;> cases b.2.testBit i <;> decide

theorem masked_l (op : Kind) (a b u : Bool) (miss : u≠leftNeeds op) :
    applyKind op a u = applyKind op b u := by
  cases op <;> cases u <;> simp_all [leftNeeds,applyKind]

theorem needed_bit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a)
    {i : Nat} (p : (privateMask ws a).testBit i=true) :
    b.1.testBit i = leftNeeds op := by
  obtain ⟨da,only⟩ := private_only ha p
  have db := only b hb ab.symm
  have beq : b.1.testBit i=b.2.testBit i := by
    simp only [sep,Nat.testBit_xor] at db
    cases hl : b.1.testBit i <;> cases hr : b.2.testBit i <;> simp_all
  have on := (covered_iff ws i).2 ⟨a,ha,da⟩
  rw [←same] at on
  obtain ⟨w,hw,good⟩ := (covered_iff out i).1 on
  rcases others w hw with e|⟨belongs,no⟩
  · subst w
    apply Classical.byContradiction
    intro neg
    obtain ⟨lo,hi⟩ := bit_rule op a b i
    have flat := masked_l op (a.1.testBit i) (a.2.testBit i) (b.1.testBit i) neg
    rw [←beq] at hi
    simp [sep,Nat.testBit_xor,lo,hi,flat] at good
  · exact Bool.noConfusion ((only w belongs no).symm.trans good)

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def maskOK (word mask : Nat) (want : Bool) : Bool :=
  if want then (mask &&& word)==mask else (mask &&& word)==0

theorem mask_hit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  have key := fun i => @needed_bit ws out a b ha hb ab op same others i
  cases d : leftNeeds op with
  | false =>
    simp only [maskOK,Bool.false_eq_true,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]
  | true =>
    simp only [maskOK,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]

def reflectOp : Kind→Kind
  | .conj => .conj
  | .disj => .disj
  | .leftOnly => .rightOnly
  | .rightOnly => .leftOnly

theorem gate_swap (op : Kind) (a b : Word) : wordGate (reflectOp op) b a=wordGate op a b := by
  cases op <;> simp [reflectOp,wordGate,meet,join,skip,Nat.and_comm,Nat.or_comm]

def restOf (ws : List Word) (a b : Word) := ws.filter (fun w => w != a && w != b)
def keepList (ka kb : Bool) (a b : Word) := (if ka then [a] else [])++(if kb then [b] else [])
def extension (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) :=
  wordGate op a b::(keepList ka kb a b ++ restOf ws a b)

theorem rest_mem {ws : List Word} {a b w} : w∈restOf ws a b ↔ w∈ws ∧ w≠a ∧ w≠b := by
  simp [restOf]

theorem kept_mask_left {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (kb : Bool)
    (full : cover (extension ws a b op false kb)=cover ws) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  apply mask_hit ha hb ab op full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl eq
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases kb <;> simp [keepList] at hk
      exact hk ▸ And.intro hb ab.symm
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.1⟩

theorem kept_mask_right {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (ka : Bool)
    (full : cover (extension ws a b op ka false)=cover ws) :
    maskOK a.1 (privateMask ws b) (leftNeeds (reflectOp op))=true := by
  apply mask_hit hb ha ab.symm (reflectOp op) full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl (eq.trans (gate_swap op a b).symm)
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases ka <;> simp [keepList] at hk
      exact hk ▸ And.intro ha ab
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.2⟩

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def tryField (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind) : Bool :=
  let n := ws.length
  let half := n≤k+1
  let stay := n≤k
  let rest := restOf ws a.1 b.1
  let base := cover rest
  let oka := maskOK b.1.1 a.2 (leftNeeds op)
  let okb := maskOK a.1.1 b.2 (leftNeeds (reflectOp op))
  (stay || (half && (oka || okb)) || (oka && okb)) &&
    (let z := wordGate op a.1 b.1
     z != (0,0) && !(ws.contains z) &&
      ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
       (half && okb && next (z::a.1::rest)) ||
       (half && oka && next (z::b.1::rest)) ||
       (stay && next (z::a.1::b.1::rest))))

def pairTry (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) : Bool :=
  tryField k next ws a b .conj || tryField k next ws a b .disj ||
    tryField k next ws a b .leftOnly || tryField k next ws a b .rightOnly

theorem guarded_eq (k : Nat) (next : List Word→Bool) (ws : List Word) :
    guarded k next ws =
      if ws.length>k+2 then false else
        pairs (pairTry k next ws) (ws.map fun a => (a,privateMask ws a)) := rfl

theorem cover_cons (w : Word) (ws : List Word) : cover (w::ws)=sep w ||| cover ws := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [cover,foldBits,Nat.testBit_or]

theorem drop_len (ws : List Word) (d : Word) (nd : ws.Nodup) (hd : d∈ws) :
    (ws.filter (fun w => w != d)).length+1=ws.length := by
  induction ws with
  | nil => simp at hd
  | cons x xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    by_cases e : x=d
    · subst x
      have self : xs.filter (fun w => w != d)=xs := List.filter_eq_self.mpr (by
        intro v hv
        have neq : v≠d := fun eq => fresh (eq ▸ hv)
        simp [neq])
      simp [self]
    · have hit := (List.mem_cons.mp hd).resolve_left (Ne.symm e)
      have n := ih rest hit
      simp [e,n]

theorem rest_len (ws : List Word) (a b : Word) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b) :
    (restOf ws a b).length+2=ws.length := by
  let after := ws.filter (fun w => w != a)
  have inside : b∈after := by simp [after,hb,ab.symm]
  have n1 := drop_len ws a nd ha
  have n2 := drop_len after b (nd.filter _) inside
  have order : (after.filter (fun w => w != b))=restOf ws a b := by
    simp [after,restOf,List.filter_filter,Bool.and_comm]
  rw [order] at n2
  dsimp [after] at n2
  omega

theorem tryField_hit {k : Nat} {ws : List Word} {a b : Word} (op : Kind) (ka kb : Bool)
    (next : List Word→Bool) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (non : wordGate op a b≠(0,0)) (fresh : wordGate op a b∉ws)
    (wide : (extension ws a b op ka kb).length≤k+1) (old : cover ws=all)
    (new : cover (extension ws a b op ka kb)=all) (pass : next (extension ws a b op ka kb)=true) :
    tryField k next ws (a,privateMask ws a) (b,privateMask ws b) op=true := by
  have remaining := rest_len ws a b nd ha hb ab
  have same := new.trans old.symm
  cases ka <;> cases kb
  · have l := kept_mask_left op ha hb ab false same
    have r := kept_mask_right op ha hb ab false same
    have cc : cover (restOf ws a b) ||| sep (wordGate op a b)=all := by
      simpa [extension,keepList,cover_cons,Nat.or_comm] using new
    simp [extension,keepList] at pass
    simp [tryField,l,r,non,fresh,cc,pass]
  · have l := kept_mask_left op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,l,width,non,fresh,pass]
  · have r := kept_mask_right op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,r,width,non,fresh,pass]
  · have width : ws.length≤k := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,width,non,fresh,pass]

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem project_inj {a b : CoThetaBits.Wire} (h : project a=project b) : a=b := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

@[simp] theorem project_eq {a b : CoThetaBits.Wire} : project a=project b ↔ a=b :=
  ⟨project_inj,congrArg project⟩

private theorem mask_sub {n} (a b : BitVec n) :
    (a &&& ~~~b)=a ^^^ (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem mask_rev {n} (a b : BitVec n) :
    (~~~a &&& b)=b ^^^ (b &&& a) := by rw [BitVec.and_comm,mask_sub]

theorem project_gate (op : Kind) (a b : CoThetaBits.Wire) :
    project (CoThetaBits.gate op a b)=wordGate op (project a) (project b) := by
  cases op <;> simp only [project,CoThetaBits.gate,wordGate,meet,join,skip,mask_sub,mask_rev,
    BitVec.toNat_and,BitVec.toNat_or,BitVec.toNat_xor]

theorem project_cover (ws : List CoThetaBits.Wire) :
    cover (ws.map project)=(CoThetaBits.coverage ws).toNat := by
  induction ws with
  | nil => change 0=(0:CoThetaBits.Bits).toNat; simp
  | cons w ws ih => simp [cover_cons,project,sep,CoThetaBits.coverage,CoThetaBits.sep,ih]

theorem project_trim (xs : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) :
    (CoThetaBits.trim a b xs).map project=restOf (xs.map project) (project a) (project b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x=a <;> by_cases h : x=b <;>
      simp [CoThetaBits.trim,restOf,e,h,project_eq] at * <;> exact ih

theorem project_edit (ws : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) (op : Kind)
    (U : (CoThetaBits.Row→Bool)→Prop) :
    (CoThetaBits.gate op a b::(CoThetaBits.kept a b U++CoThetaBits.trim a b ws)).map project=
      extension (ws.map project) (project a) (project b) op
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den a))))
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den b)))) := by
  classical
  by_cases p : U (CoThetaBits.den a) <;> by_cases q : U (CoThetaBits.den b) <;>
    simp [CoThetaBits.kept,extension,keepList,p,q,project_gate,project_trim]

theorem pair_hit (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind)
    (h : tryField k next ws a b op=true) : pairTry k next ws a b=true := by
  cases op <;> simp [pairTry,h]

theorem pairs_hit {α} (test : α→α→Bool) {a b : α} {ws : List α}
    (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (go : test a b=true) (back : test b a=true) :
    pairs test ws=true := by
  classical
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    rw [pairs,Bool.or_eq_true]
    by_cases eq : a=w
    · subst w
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left ne.symm,go⟩)
    · by_cases e : b=w
      · subst w
        exact Or.inl (List.any_eq_true.mpr ⟨a,(List.mem_cons.mp ha).resolve_left ne,back⟩)
      · exact Or.inr (ih ((List.mem_cons.mp ha).resolve_left eq) ((List.mem_cons.mp hb).resolve_left e))

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

private theorem project_nodup {xs : List Wire} (h : xs.Nodup) : (xs.map project).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨no,rest⟩ := List.nodup_cons.mp h
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih rest⟩
    intro h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    exact no (project_inj eq ▸ hb)

private theorem seen_iff {S ws} (rep : Rep ws S) (a : Wire) : a∈ws ↔ S (den a) := by
  constructor
  · exact fun ha => (rep _).2 ⟨a,ha,rfl⟩
  · intro h
    obtain ⟨b,hb,eq⟩ := (rep _).1 h
    exact CoThetaBits.den_injective eq ▸ hb

private theorem direction_hit {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      guardedSearch k (zs.map project)=true) :
    pairTry k (guardedSearch k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem guarded_complete {m S} (run : Live (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → guardedSearch fuel (ws.map project)=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    cases fuel <;> simp [guardedSearch,target,hit]
  | @step m U a b kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → guardedSearch k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := direction_hit kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (guardedSearch k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply direction_hit (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (guardedSearch k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [guardedSearch,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench
namespace CoThetaSix
open CoThetaBits
open CoNatBench
def cycle : List CoThetaBits.Wire := [(0x401f80fff40701fff,0x400f006ba486086a6),
(0x81e3f3070807ffe00,0x80a1a10608232d414),
(0x3067c0c180ff801fff,0x3027004100a3001958),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07800fe00ffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc05000ac005c4d0020),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000ffff00000000,0x590000f94410060040),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa675a4000820080180)]
theorem cycle_small : CoNatBench.guardedSearch 7 (cycle.map CoNatBench.project)=false := by decide +kernel
def cyclePrivate : List Nat := [3, 16, 1, 14, 33, 49]
def pendant : List CoThetaBits.Wire := [(0x118fc1cffbf0601ff,0x108780c5d1e420896),
(0x2071fe33847fffe00,0x2020d213003924c04),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc19e003c07807ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc118002806005b168),
(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01e007c007ff80000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05c00580074602030),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fff80000000,0x56400073a20080c040),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa99dd2000400010180)]
theorem pendant_small : CoNatBench.guardedSearch 7 (pendant.map CoNatBench.project)=false := by decide +kernel
def pendantPrivate : List Nat := [3, 12, 1, 20, 32, 48]
end CoThetaSix
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)

def essentialBasis (roots : List Wire) : Prop :=
  ∀ w∈roots, ∃ i : Fin CoThetaBits.Width, ∀ v∈roots,
    den v (true,i)≠den v (false,i) → v=w

theorem generic_rep {m S} {roots : List Wire} (live : Live (den CoThetaBits.target) m S)
    (onlyRaw : ∀ f, S f → f=absentBit ∨ ∃ w∈roots, den w=f)
    (required : essentialBasis roots) : Rep roots S := by
  have ng : den CoThetaBits.target≠absentBit := by
    intro e
    have no := congrFun e (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  intro f
  constructor
  · intro hf
    rcases onlyRaw f hf with z|h
    · exact (live.excludes_zero ng (z ▸ hf)).elim
    · exact h
  · rintro ⟨w,hw,eq⟩
    obtain ⟨i,key⟩ := required w hw
    have d : den CoThetaBits.target (true,i)≠den CoThetaBits.target (false,i) := by simp [CoThetaBits.den_target]
    obtain ⟨v,hv,diff⟩ := live.separates (true,i) (false,i) d
    rcases onlyRaw v hv with z|⟨u,hu,e⟩
    · subst v
      exact (diff rfl).elim
    · subst v
      obtain rfl := key u hu diff
      exact eq ▸ hv

theorem table_bound {roots : List Wire} (required : essentialBasis roots)
    (nd : roots.Nodup) {n ws} (run : Free (absentBit::roots.map den) n ws)
    (goal : den CoThetaBits.target∈ws) {cap : Nat} (cert : guardedSearch cap (roots.map project)=false) : cap<n := by
  obtain ⟨k,S,le,live,sub⟩ := rewind run List.mem_cons_self
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  apply Classical.byContradiction
  intro bad
  apply Bool.false_ne_true
  rw [←cert]
  apply guarded_complete live cap (by omega) roots nd
  apply generic_rep live _ required
  intro f h
  rcases List.mem_cons.mp (sub f h) with z|raw
  · exact Or.inl z
  · exact Or.inr (List.mem_map.mp raw)

end CoNatBench

namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den)

def basisAt (ws : List Wire) (ids : List Nat) : Bool :=
  (List.range ws.length).all fun a =>
    let i := (ids.getD a 0) % CoThetaBits.Width
    ws.all fun v =>
      let want := ws.getD a CoThetaBits.zero
      (den v (true,⟨i,Nat.mod_lt _ (by decide)⟩) == den v (false,⟨i,Nat.mod_lt _ (by decide)⟩)) || v==want

theorem basisAt_sound (ws : List Wire) (ids : List Nat) (cert : basisAt ws ids=true) :
    CoNatBench.essentialBasis ws := by
  intro w hw
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hw
  let i := (ids.getD k 0) % CoThetaBits.Width
  refine ⟨⟨i,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro v hv ne
  have each := List.all_eq_true.mp cert k (List.mem_range.mpr hk)
  have hit := List.all_eq_true.mp each v hv
  simp only [Bool.or_eq_true,beq_iff_eq] at hit
  have vwant := hit.resolve_left ne
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,eq] using vwant

theorem cycle_basis : CoNatBench.essentialBasis cycle := basisAt_sound cycle cyclePrivate (by decide +kernel)
theorem pendant_basis : CoNatBench.essentialBasis pendant := basisAt_sound pendant pendantPrivate (by decide +kernel)
theorem cycle_nd : cycle.Nodup := by decide +kernel
theorem pendant_nd : pendant.Nodup := by decide +kernel

end CoThetaSix
namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)

def rootsFor (gone : Fin 7) := if gone=2 then cycle else pendant

def indexAt (gone vertex : Fin 7) : Option Nat :=
  match gone.val,vertex.val with
  | 2,0 => some 0
  | 2,1 => some 1
  | 2,3 => some 2
  | 2,4 => some 3
  | 2,5 => some 4
  | 2,6 => some 5
  | 3,0 => some 0
  | 3,1 => some 1
  | 3,2 => some 2
  | 3,4 => some 3
  | 3,5 => some 4
  | 3,6 => some 5
  | 4,1 => some 0
  | 4,0 => some 1
  | 4,2 => some 2
  | 4,3 => some 3
  | 4,6 => some 4
  | 4,5 => some 5
  | 5,0 => some 0
  | 5,1 => some 1
  | 5,2 => some 2
  | 5,6 => some 3
  | 5,3 => some 4
  | 5,4 => some 5
  | 6,1 => some 0
  | 6,0 => some 1
  | 6,2 => some 2
  | 6,5 => some 3
  | 6,4 => some 4
  | 6,3 => some 5
  | _,_ => none

def minorCol (gone vertex : Fin 7) : Wire :=
  match indexAt gone vertex with
  | none => CoThetaBits.zero
  | some n => (rootsFor gone).getD n CoThetaBits.zero

def minorLift (g : Fin 7) (r : Row) : SmallInput := pack (fun j => den (minorCol g j) r)
def minorGraph (g : Fin 7) : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (minorCol g 0) (minorCol g 2)) (gate .conj (minorCol g 1) (minorCol g 2)))
    (gate .conj (minorCol g 0) (minorCol g 3))) (gate .conj (minorCol g 3) (minorCol g 4)))
    (gate .conj (minorCol g 1) (minorCol g 4))) (gate .conj (minorCol g 0) (minorCol g 5)))
    (gate .conj (minorCol g 5) (minorCol g 6))) (gate .conj (minorCol g 1) (minorCol g 6))

theorem minor_table : ∀ g : Fin 7, 2≤g.val → minorGraph g=CoThetaBits.target ∧
    minorCol g g=CoThetaBits.zero := by decide +kernel

theorem minor_input (g j : Fin 7) :
    restrict (minorLift g) (raw7 j)=den (minorCol g j) :=
  funext (fun r => unpack (fun v => den (minorCol g v) r) j)

theorem minor_goal {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) ans7=den CoThetaBits.target := by
  have graph := congrArg den (minor_table g small).1
  funext r
  change ans7 (minorLift g r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (minorLift g r))=(fun j => den (minorCol g j) r) :=
    funext (fun j => congrFun (minor_input g j) r)
  rw [values]
  have equality := congrFun graph r
  simp only [minorGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem minor_off {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) (raw7 g)=absentBit :=
  (minor_input g g).trans ((congrArg den (minor_table g small).2).trans CoThetaBits.den_zero)

theorem minor_known (g : Fin 7) : ∀ w∈vertices7,
    restrict (minorLift g) w∈absentBit::(rootsFor g).map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [minor_input]
    cases h : indexAt g j with
    | none => simp [minorCol,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : (rootsFor g)[n]? with
      | none => simp [minorCol,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [minorCol,h,List.getD_eq_getElem?_getD,hn,inList]

theorem minor_lower {g : Fin 7} (small : 2≤g.val) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : 8≤remaining (minorLift g) gs := by
  let roots := rootsFor g
  obtain ⟨ws,run,all⟩ := restrict_trace (minorLift g) gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self (minor_known g)
  have h := all ans7 ok.2
  rw [minor_goal small] at h
  have yes : 7<0+remaining (minorLift g) gs := by
    by_cases e : g=2
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using cycle_basis)
        (by simpa [roots,rootsFor,e] using cycle_nd) run h (by simpa [roots,rootsFor,e] using cycle_small)
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using pendant_basis)
        (by simpa [roots,rootsFor,e] using pendant_nd) run h (by simpa [roots,rootsFor,e] using pendant_small)
  omega

end CoThetaSix
namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

noncomputable def readerSet {ρ : Type} (gs : List (TraceGate ρ)) (p : ρ → Bool) :
    Finset (TraceGate ρ) := by classical exact gs.toFinset.filter (fun g => reads g p)

theorem mem_readerSet {ρ : Type} {gs : List (TraceGate ρ)} {p : ρ → Bool}
    {g : TraceGate ρ} : g ∈ readerSet gs p ↔ g ∈ gs ∧ reads g p := by
  classical
  simp [readerSet]

/-- For the nonedge head, p has two readers including a head that does not read q.
Any gate reading both raw inputs masks q on one slice, forcing its second reader. -/
theorem three_readers_separate_head {α : Type} [DecidableEq α] (P Q : Finset α)
    (twoP : 2 ≤ P.card) (someQ : Q.Nonempty) (head : ∃ g ∈ P, g ∉ Q)
    (shared : ∀ g ∈ P, g ∈ Q → 2 ≤ Q.card) : 3 ≤ (P ∪ Q).card := by
  classical
  by_cases both : ∃ g ∈ P, g ∈ Q
  · obtain ⟨g,hg,hq⟩ := both
    obtain ⟨h,hp,hn⟩ := head
    have sub : insert h Q ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_left _ hp
      · exact Finset.mem_union_right _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hn] at hc
    have low := shared g hg hq
    omega
  · obtain ⟨q,hq⟩ := someQ
    have out : q ∉ P := fun hp => both ⟨q,hp,hq⟩
    have sub : insert q P ⊆ P ∪ Q := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right _ hq
      · exact Finset.mem_union_left _ hv
    have hc := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem out] at hc
    omega

/-- Path in the given semantic trace, through reads of actual gate operands. -/
inductive UsePath {ρ : Type} (gs : List (TraceGate ρ)) :
    (ρ → Bool) → (ρ → Bool) → Prop
  | stop {w} : UsePath gs w w
  | through {w out} (g : TraceGate ρ) (mem : g ∈ gs) (input : reads g w)
      (rest : UsePath gs g.value out) : UsePath gs w out

private theorem two_reads_zero {ρ σ : Type} (lift : σ → ρ)
    {g : TraceGate ρ} {w p : ρ → Bool} (ne : w ≠ p) (hw : reads g w) (hp : reads g p)
    (zw : restrict lift w = absentBit) (zp : restrict lift p = absentBit) :
    restrict lift g.value = absentBit := by
  apply two_zero_propagate
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h).trans zw
    · exact (congrArg (restrict lift) h').trans zp
    · exact (ne (h.symm.trans h')).elim
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h').trans zp
    · exact (congrArg (restrict lift) h).trans zw
    · exact (ne (h.symm.trans h')).elim

/-- A path starting at a projected-zero signal and ending at a nonzero target
must lose another gate outside the two raw-reader sets. Freshness is only needed
for exact raw-function aliases along the path, because a semantic reader records
values rather than pin indices. -/
theorem extra_loss_on_path {ρ σ : Type} (lift : σ → ρ) {gs : List (TraceGate ρ)}
    {p q z out : ρ → Bool} (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (aliasFree : ∀ g ∈ gs, g.value ≠ p ∧ g.value ≠ q)
    (path : UsePath gs z out) (zz : restrict lift z = absentBit)
    (distinct : z ≠ p ∧ z ≠ q) (ends : restrict lift out ≠ absentBit) :
    ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g := by
  induction path with
  | stop => exact (ends zz).elim
  | @through w out g hg hw more ih =>
    by_cases hp : reads g p
    · exact ih (two_reads_zero lift distinct.1 hw hp zz zp) (aliasFree g hg) ends
    by_cases hq : reads g q
    · exact ih (two_reads_zero lift distinct.2 hw hq zz zq) (aliasFree g hg) ends
    exact ⟨g,hg,hp,hq,reading_zero_disappears lift zz hw⟩

private noncomputable def lostList {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    List (TraceGate ρ) := by classical exact gs.filter (fun g => decide (disappears lift g))

private theorem lost_length {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    (lostList lift gs).length = saved lift gs := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [lostList,saved,h,lostList] at ih ⊢ <;> omega

theorem four_saved_raw_head {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ))
    (p q : ρ → Bool) (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (three : 3 ≤ (readerSet gs p ∪ readerSet gs q).card)
    (extra : ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g) :
    4 ≤ saved lift gs := by
  classical
  obtain ⟨g,hg,hp,hq,hd⟩ := extra
  let A := readerSet gs p ∪ readerSet gs q
  have hout : g ∉ A := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact hp (mem_readerSet.mp h).2
    · exact hq (mem_readerSet.mp h).2
  have sub : insert g A ⊆ (lostList lift gs).toFinset := by
    intro v hv
    have hv' : v∈gs ∧ disappears lift v := by
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨hg,hd⟩
      · rcases Finset.mem_union.mp hv with h|h
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zp hr⟩
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zq hr⟩
    simpa [lostList] using hv'
  have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
  rw [Finset.card_insert_of_notMem hout,lost_length] at bound
  change 3 ≤ A.card at three
  omega

end CoThetaFreeCore
namespace CoThetaFreeCore

theorem UsePath.trans {ρ : Type} {chain : List (TraceGate ρ)} {a b c : ρ → Bool}
    (first : UsePath chain a b) (last : UsePath chain b c) : UsePath chain a c := by
  induction first with
  | stop => exact last
  | through g hg hr _ ih => exact .through g hg hr (ih last)

/-- Recompute every wire not reachable from z, completely omitting the source z
itself. The returned signed binary program has at most the old suffix cost. -/
theorem omit_path_scan {ρ : Type} (chain : List (TraceGate ρ)) (z : ρ → Bool)
    (gs : List (TraceGate ρ)) (sub : ∀ g∈gs, g∈chain)
    {raw start pool : List (ρ → Bool)} {b : Nat}
    (reg : registered start gs) (pre : Free raw b pool)
    (known : ∀ w∈start, ¬UsePath chain z w → w∈pool) :
    ∃ j ys, j ≤ b+gs.length ∧ Free raw j ys ∧
      ∀ w∈traceWires start gs, ¬UsePath chain z w → w∈ys := by
  induction gs generalizing start pool b with
  | nil => exact ⟨b,pool,by simp,pre,known⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,rest⟩ := reg
    have hg := sub g List.mem_cons_self
    have tail (v) (hv : v∈gs) := sub v (List.mem_cons_of_mem _ hv)
    by_cases path : UsePath chain z g.value
    · have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact (hn path).elim
        · exact known _ hw hn
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest pre carry
      exact ⟨j,ys,by simp; omega,run,avail⟩
    · have pl : ¬UsePath chain z g.left := fun p =>
        path (p.trans (.through g hg (Or.inl rfl) .stop))
      have pr : ¬UsePath chain z g.right := fun p =>
        path (p.trans (.through g hg (Or.inr rfl) .stop))
      have next : Free raw (b+1) (g.value::pool) :=
        .binary pre g.kind (known _ hl pl) (known _ hr pr)
      have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈g.value::pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (known _ hw hn)
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest next carry
      exact ⟨j,ys,by simp; omega,run,avail⟩

theorem omit_dead_head {ρ : Type} (raw : List (ρ → Bool))
    (gs : List (TraceGate ρ)) (z target : ρ → Bool)
    (reg : registered (z::raw) gs) (out : target∈traceWires (z::raw) gs)
    (dead : ¬UsePath gs z target) :
    ∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ target∈ys := by
  have known (w) (hw : w∈z::raw) (hn : ¬UsePath gs z w) : w∈raw := by
    rcases List.mem_cons.mp hw with rfl|hw
    · exact (hn .stop).elim
    · exact hw
  obtain ⟨j,ys,hj,run,avail⟩ := omit_path_scan gs z gs (fun _ h => h) reg (Free.start (raw:=raw)) known
  exact ⟨j,ys,by simpa using hj,run,avail _ out dead⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

private theorem masked_setting {ρ : Type} (g : TraceGate ρ) (p : ρ → Bool) (hp : reads g p) :
    ∃ b : Bool, ∀ r s, p r=b → p s=b → g.value r = g.value s := by
  obtain ⟨k,l,r⟩ := g
  rcases hp with h|h
  · change l=p at h
    subst l
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k b a = applyKind k b c := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩
  · change r=p at h
    subst r
    have valid : ∀ k : Kind, ∃ b : Bool, ∀ a c : Bool, applyKind k a b = applyKind k c b := by
      intro j
      cases j <;> decide
    obtain ⟨b,f⟩ := valid k
    exact ⟨b,fun x y hx hy => by simp only [TraceGate.value,hx,hy]; exact f _ _⟩

/-- Instantiate this for p=0, q=4, head=(0 AND 3). The geometric data use just
one masked row pair at the head and two row pairs for q, one per setting of p. -/
theorem nonedge_head_dichotomy {ρ σ : Type} (lift : σ → ρ)
    (raw : List (ρ → Bool)) (head : TraceGate ρ) (gs : List (TraceGate ρ))
    (p q out : ρ → Bool)
    (reg : registered raw (head::gs)) (solves : out∈traceWires raw (head::gs))
    (hrp : reads head p) (hrq : ¬reads head q)
    (outp : out≠p) (outq : out≠q)
    (pTest : ∃ r s, agreeOutside (·=p) r s raw ∧ out r≠out s ∧ head.value r=head.value s)
    (qTest : ∀ b : Bool, ∃ r s, agreeOutside (·=q) r s raw ∧ out r≠out s ∧ p r=b ∧ p s=b)
    (zp : restrict lift p=absentBit) (zq : restrict lift q=absentBit)
    (zh : restrict lift head.value=absentBit) (endNZ : restrict lift out≠absentBit)
    (headNew : head.value≠p ∧ head.value≠q)
    (fresh : ∀ g∈gs, g.value≠p ∧ g.value≠q) :
    (∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ out∈ys) ∨ 4 ≤ saved lift (head::gs) := by
  classical
  by_cases alive : UsePath gs head.value out
  case neg =>
    exact Or.inl (omit_dead_head raw gs head.value out reg.2.2 solves alive)
  case pos =>
    right
    apply four_saved_raw_head lift (head::gs) p q zp zq
    · apply three_readers_separate_head
      · obtain ⟨r,s,hs,hd,hm⟩ := pTest
        obtain ⟨g,hg,hp,ne⟩ := second_reader p r s head reg hs solves outp hd hm
        apply Finset.one_lt_card.mpr
        exact ⟨g,mem_readerSet.mpr ⟨hg,hp⟩,head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,ne⟩
      · obtain ⟨r,s,hs,hd,_,_⟩ := qTest false
        obtain ⟨g,hg,read,_⟩ := reader_witness (·=q) r s reg hs solves outq hd
        exact ⟨g,mem_readerSet.mpr ⟨hg,read⟩⟩
      · exact ⟨head,mem_readerSet.mpr ⟨List.mem_cons_self,hrp⟩,fun h => hrq (mem_readerSet.mp h).2⟩
      · intro g hgP hgQ
        obtain ⟨b,hm⟩ := masked_setting g p (mem_readerSet.mp hgP).2
        obtain ⟨r,s,hs,hd,hpR,hpS⟩ := qTest b
        obtain ⟨other,hOther,readsQ,ne⟩ := second_reader q r s g reg hs solves outq hd (hm r s hpR hpS)
        apply Finset.one_lt_card.mpr
        exact ⟨other,mem_readerSet.mpr ⟨hOther,readsQ⟩,g,hgQ,ne⟩
    · obtain ⟨g,hg,hp,hq,hd⟩ := extra_loss_on_path lift zp zq fresh alive zh headNew endNZ
      exact ⟨g,List.mem_cons_of_mem _ hg,hp,hq,hd⟩

end CoThetaFreeCore
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off minor_goal minor_lower)

def smallRow (n : Nat) : SmallInput := ⟨n % 128,Nat.mod_lt _ (by decide)⟩
def sensSeeds : List Nat :=
  [0, 0, 4, 10, 8, 4, 4, 8, 4, 20, 4, 32, 4, 68, 4, 17, 0, 0, 16, 4, 4, 12, 4, 16, 4, 36, 4, 64, 2, 1, 1, 2, 0, 0, 1, 10, 1, 17, 1, 34, 1, 65, 16, 1, 1, 3, 1, 20, 0, 0, 1, 16, 1, 48, 1, 65, 2, 3, 8, 2, 2, 12, 2, 8, 0, 0, 2, 34, 2, 72, 64, 1, 1, 3, 1, 68, 1, 72, 1, 17, 0, 0, 1, 64, 2, 3, 32, 2, 2, 36, 2, 10, 2, 48, 2, 32, 0, 0]

def loRow (x y : Fin 7) (b : Bool) := smallRow (sensSeeds.getD (2*(7*x.val+y.val)+b.toNat) 0)
def hiRow (x y : Fin 7) (b : Bool) := smallRow ((loRow x y b).val ||| (1 <<< x.val))
theorem seven_sensitivity : ∀ (x y : Fin 7), x≠y → ∀ b : Bool,
    raw7 x (loRow x y b)=false ∧ raw7 x (hiRow x y b)=true ∧
    raw7 y (loRow x y b)=b ∧ raw7 y (hiRow x y b)=b ∧
    ans7 (loRow x y b)≠ans7 (hiRow x y b) ∧
    ∀ z : Fin 7, z≠x → raw7 z (loRow x y b)=raw7 z (hiRow x y b) := by decide +kernel

theorem seven_diff : ∀ (x y : Fin 7), x≠y → ∃ r : SmallInput, raw7 x r≠raw7 y r := by
  have table : ∀ p q : Fin 7, p≠q → raw7 p (smallRow (1 <<< p.val))≠raw7 q (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p q pq => ⟨_,table p q pq⟩
theorem seven_not_raw : ∀ x : Fin 7, ∃ r : SmallInput, ans7 r≠raw7 x r := by
  have table : ∀ p : Fin 7, ans7 (smallRow (1 <<< p.val))≠raw7 p (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p => ⟨_,table p⟩

theorem raw_mem (x : Fin 7) : raw7 x∈vertices7 := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨x,rfl⟩)

theorem read_twice (x y : Fin 7) (xy : x≠y) (g : TraceGate SmallInput)
    (gx : reads g (raw7 x)) (gy : reads g (raw7 y)) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : ∃ t∈gs, reads t (raw7 x) ∧ t≠g := by
  obtain ⟨r,ne⟩ := seven_diff x y xy
  have diff : raw7 x≠raw7 y := fun h => ne (congrFun h r)
  obtain ⟨sw,code⟩ := joint_reader_code _ _ diff g gx gy
  obtain ⟨b,mask⟩ := CoThetaNine.masks_some_value g.kind sw
  obtain ⟨lx,hx,ly,hy,out,fixed⟩ := seven_sensitivity x y xy b
  obtain ⟨r,notSame⟩ := seven_not_raw x
  apply second_reader (raw7 x) (loRow x y b) (hiRow x y b) g ok.1 _ ok.2
    (fun eq => notSame (congrFun eq r)) out
  · simpa only [code,lx,hx,ly,hy] using mask false true
  · intro w hw no
    rcases List.mem_cons.mp hw with e|h
    · subst w
      rfl
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp h
      subst w
      exact fixed i (fun e => no (congrArg raw7 e))

theorem three_losses {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) {a b c : TraceGate ρ}
    (ha : a∈gs) (hb : b∈gs) (hc : c∈gs) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (da : disappears lift a) (db : disappears lift b) (dc : disappears lift c) :
    3≤saved lift gs := by
  classical
  have nd : [a,b,c].Nodup := by simp [ab,ac,bc]
  rw [saved_eq_length]
  apply length_of_cover [a,b,c] _ nd
  intro w h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e <;> subst w <;> simp [vanishing,ha,hb,hc,da,db,dc]

theorem absorbing_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (budget : (g::gs).length≤10) {x y : Fin 7} (xy : x≠y)
    (rx : reads g (raw7 x)) (ry : reads g (raw7 y)) (nonhub : 2≤x.val)
    (zero : restrict (minorLift x) g.value=absentBit) :
    ∃ n ws, n≤gs.length ∧ Free vertices7 n ws ∧ ans7∈ws := by
  classical
  by_cases path : UsePath gs g.value ans7
  · exfalso
    have off := minor_off nonhub
    have fin : restrict (minorLift x) ans7≠absentBit := by
      rw [minor_goal nonhub]
      intro e
      have no := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at no
    have distinct {t : TraceGate SmallInput} (ht : t∈g::gs) : t.value≠raw7 x :=
      fun e => fresh_outputs fresh _ ht (e ▸ raw_mem x)
    have headNe := distinct (List.mem_cons_self (a:=g) (l:=gs))
    obtain ⟨b,hb,rb,bg⟩ := read_twice x y xy g rx ry ok
    obtain ⟨c,hc,nr,_,gone⟩ := extra_loss_on_path (minorLift x) off off
      (fun t ht => ⟨distinct (List.mem_cons_of_mem _ ht),distinct (List.mem_cons_of_mem _ ht)⟩)
      path zero ⟨headNe,headNe⟩ fin
    have gain := three_losses (minorLift x) (g::gs) List.mem_cons_self hb
      (List.mem_cons_of_mem _ hc) (Ne.symm bg) (fun e => nr (e ▸ rx)) (fun e => nr (e ▸ rb))
      (reading_zero_disappears _ off rx) (reading_zero_disappears _ off rb) gone
    have lo := minor_lower nonhub ok
    have tot := accounted (minorLift x) (g::gs)
    omega
  · exact omit_dead_head vertices7 gs g.value ans7 ok.1.2.2 ok.2 path

end CoThetaSeven
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off)
def opIndex : Kind→Nat
  | .conj => 0 | .disj => 1 | .leftOnly => 2 | .rightOnly => 3
def opAt (n : Nat) : Kind := match n with
  | 0 => .conj | 1 => .disj | 2 => .leftOnly | _ => .rightOnly
def allPerms : List (List (Fin 7)) := [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 5, 6, 3, 4], [1, 0, 2, 4, 3, 6, 5], [1, 0, 2, 6, 5, 4, 3]]
def casesA : List (Fin 7) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3]
def casesB : List (Fin 7) := [1, 1, 1, 2, 2, 3, 3, 4, 4, 3, 4, 5, 6]
def casesOp : List Nat := [0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1]
def tags : List Nat := [0, 0, 0, 0, 2, 6, 10, 12, 1, 14, 18, 1, 1, 22, 26, 1, 1, 30, 34, 1, 1, 23, 27, 1, 1, 31, 35, 1, 2, 6, 12, 10, 0, 0, 0, 0, 1, 16, 20, 1, 1, 32, 36, 1, 1, 24, 28, 1, 1, 33, 37, 1, 1, 25, 29, 1, 0, 14, 0, 18, 0, 16, 0, 20, 0, 0, 0, 0, 0, 38, 0, 1, 0, 40, 0, 1, 0, 39, 0, 1, 0, 41, 0, 1, 0, 22, 0, 26, 0, 32, 0, 36, 0, 38, 0, 1, 0, 0, 0, 0, 0, 42, 0, 1, 0, 46, 0, 1, 0, 50, 0, 1, 0, 30, 0, 34, 0, 24, 0, 28, 0, 40, 0, 1, 0, 42, 0, 1, 0, 0, 0, 0, 0, 51, 0, 1, 0, 48, 0, 1, 0, 23, 0, 27, 0, 33, 0, 37, 0, 39, 0, 1, 0, 46, 0, 1, 0, 51, 0, 1, 0, 0, 0, 0, 0, 43, 0, 1, 0, 31, 0, 35, 0, 25, 0, 29, 0, 41, 0, 1, 0, 50, 0, 1, 0, 48, 0, 1, 0, 43, 0, 1, 0, 0, 0, 0]
def numbered (i : Fin 13) : TraceGate SmallInput :=
  ⟨opAt (casesOp.getD i.val 0),raw7 (casesA.getD i.val 0),raw7 (casesB.getD i.val 0)⟩
def position (s : Fin 4) (j : Fin 7) := (allPerms.getD s.val []).getD j.val 0
def rowPerm (s : Fin 4) (r : SmallInput) := pack (fun j => raw7 (position s j) r)
def tag (x y : Fin 7) (op : Kind) := tags.getD (4*(7*x.val+y.val)+opIndex op) 0
def picked (n : Nat) : Fin 13 := ⟨((n-2)/4) % 13,Nat.mod_lt _ (by decide)⟩
def rotation (n : Nat) : Fin 4 := ⟨(n-2) % 4,Nat.mod_lt _ (by decide)⟩

theorem perm_graph : ∀ (s : Fin 4) (r : SmallInput), ans7 (rowPerm s r)=ans7 r := by decide +kernel

theorem raw_permute (s : Fin 4) (j : Fin 7) :
    restrict (rowPerm s) (raw7 j)=raw7 (position s j) :=
  funext (fun r => unpack (fun k => raw7 (position s k) r) j)

theorem dispatch_rules (op : Kind) : ∀ x y : Fin 7, x≠y →
    let n := tag x y op
    if n=0 then 2≤x.val ∧ ∀ b : Bool, applyKind op false b=false else
    if n=1 then 2≤y.val ∧ ∀ a : Bool, applyKind op a false=false else
    ∀r : SmallInput, applyKind op (raw7 x (rowPerm (rotation n) r)) (raw7 y (rowPerm (rotation n) r)) =
      (numbered (picked n)).value r := by
  cases op <;> decide +kernel

def Selected : Prop := (∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws) ∨
  ∃ i : Fin 13, ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem dispatch_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (size : (g::gs).length≤10) : Selected := by
  classical
  obtain ⟨nL,nR,separate⟩ := fresh_ports g ok.1.1 ok.1.2.1 List.mem_cons_self fresh.1
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.1).resolve_left nL)
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.2.1).resolve_left nR)
  have xy : x≠y := fun e => separate (ex.symm.trans ((congrArg raw7 e).trans ey))
  have rx : reads g (raw7 x) := Or.inl ex.symm
  have ry : reads g (raw7 y) := Or.inr ey.symm
  let t := tag x y g.kind
  have rule := dispatch_rules g.kind x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  have n : gs.length≤9 := by simp only [List.length_cons] at size; omega
  by_cases a : t=0
  · rw [if_pos a] at rule
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind g.kind (g.left (minorLift x r)) (g.right (minorLift x r))=false
      rw [←ex,←ey]
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size xy rx ry rule.1 drop
    exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind g.kind (g.left (minorLift y r)) (g.right (minorLift y r))=false
        rw [←ex,←ey]
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size (Ne.symm xy) ry rx rule.1 drop
      exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
    · rw [if_neg b] at rule
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := by
        funext r
        change applyKind g.kind (g.left (rowPerm s r)) (g.right (rowPerm s r))=_
        rw [←ex,←ey]
        exact rule r
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨ws,run,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact Or.inr ⟨i,_,ws,by omega,run,goal⟩

theorem select_program {n ws} (run : Free vertices7 n ws) (small : n≤10) (hit : ans7∈ws) :
    Selected := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,solves,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  cases clean with
  | nil =>
    have h : ans7∈vertices7 := solves.2
    rcases List.mem_cons.mp h with z|r
    · have test : ans7 (smallRow 5)=true := by decide
      exact Bool.noConfusion (test.symm.trans (congrFun z (smallRow 5)))
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
      obtain ⟨s,d⟩ := seven_not_raw i
      exact (d (congrFun e.symm s)).elim
  | cons g gs => exact dispatch_head solves fresh (by omega)

end CoThetaSeven
namespace CoNatBench

def firstPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]
def secondPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

def rootWords : List Word := CoThetaBits.raw.map project
def nth (ws : List Word) (i : Nat) := ws.getD i (0,0)
def kinds (i : Nat) (x y : Word) : Word :=
  match i with | 0 => meet x y | 1 => join x y | 2 => skip x y | _ => skip y x

-- A successful first gate keeps each of its two raw operands, as the simple
-- finite root computation will separately certify.
def firstWords (index : Nat) : List Word :=
  let pair := firstPairs[index/4]?.getD (0,1)
  let a := nth rootWords pair.1
  let b := nth rootWords pair.2
  let z := kinds (index % 4) a b
  z::a::b::(rootWords.filter (fun w => w != a && w != b))

def prefixCase (i j : Nat) : Bool :=
  let ws := firstWords i
  let p := secondPairs[j/16]?.getD (0,1)
  let a := nth ws p.1
  let b := nth ws p.2
  let z := kinds ((j/4) % 4) a b
  let rest := ws.filter (fun w => w != a && w != b)
  let next := match j % 4 with
    | 0 => z::rest
    | 1 => z::a::rest
    | 2 => z::b::rest
    | _ => z::a::b::rest
  if z == (0,0) || ws.contains z || next.length>9 || cover next != all then true
  else !(guardedSearch 8 next)

def casesBlock (i first count : Nat) : Bool :=
  (List.range count).all (fun d => prefixCase i (first+d))

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack toRows numeric_target)
open CoThetaBits (Row Wire den col Rep)

def numbers : List Nat := [0,1,2,5,6,9,10,13,14,45,61,65,69]
def numberedWord (i : Fin 13) :=
  CoThetaBits.gate (numbered i).kind (col (casesA.getD i.val 0)) (col (casesB.getD i.val 0))

def postPool (i : Fin 13) :=
  let a := col (casesA.getD i.val 0)
  let b := col (casesB.getD i.val 0)
  numberedWord i::a::b::CoThetaBits.trim a b CoThetaBits.raw

theorem post_data : ∀ i : Fin 13,
    (postPool i).Nodup ∧ ((postPool i).map CoNatBench.project)=CoNatBench.firstWords (numbers.getD i.val 0) ∧
    ((postPool i).Perm (numberedWord i::CoThetaBits.raw)) ∧
    ∀ j : Fin 7, CoThetaBits.coverage ((postPool i).filter fun v => v != col j)≠CoThetaBits.full := by
  decide +kernel

theorem proj_raw (j : Fin 7) : restrict toRows (raw7 j)=den (col j) :=
  funext (fun r => unpack (CoThetaBits.sample r) j)

theorem proj_head (i : Fin 13) : restrict toRows (numbered i).value=den (numberedWord i) := by
  rw [numberedWord,CoThetaBits.den_gate]
  funext r
  change applyKind (numbered i).kind (raw7 (casesA.getD i.val 0) (toRows r))
    (raw7 (casesB.getD i.val 0) (toRows r))=_
  change applyKind _ (raw7 _ (pack (CoThetaBits.sample r))) (raw7 _ (pack (CoThetaBits.sample r)))=_
  rw [unpack,unpack]
  rfl

theorem collect_init (i : Fin 13) {f : Row→Bool}
    (hf : f∈((numbered i).value::vertices7).map (restrict toRows)) :
    f=absentBit ∨ ∃ w∈postPool i, den w=f := by
  obtain ⟨v,hv,eq⟩ := List.mem_map.mp hf
  subst f
  have perm := (post_data i).2.2.1
  rcases List.mem_cons.mp hv with h|rest
  · subst v
    exact Or.inr ⟨_,perm.mem_iff.mpr List.mem_cons_self,(proj_head i).symm⟩
  rcases List.mem_cons.mp rest with h|final
  · subst v
    exact Or.inl rfl
  · obtain ⟨j,h⟩ := List.mem_ofFn.mp final
    subst v
    have mem : col j∈CoThetaBits.raw := by
      rw [←CoThetaBits.raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    exact Or.inr ⟨_,perm.mem_iff.mpr (List.mem_cons_of_mem _ mem),(proj_raw j).symm⟩

theorem classify_pool (i : Fin 13) {k S} (live : Live (den CoThetaBits.target) k S)
    (sub : ∀ f, S f → f=absentBit ∨ ∃w∈postPool i,den w=f) :
    Rep CoThetaBits.raw S ∨ Rep (postPool i) S := by
  classical
  have ng : den CoThetaBits.target≠absentBit := by
    intro bad
    have no := congrFun bad (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  have present (f) (h : S f) : ∃w∈postPool i,den w=f := by
    rcases sub f h with z|p
    · exact (live.excludes_zero ng (z ▸ h)).elim
    · exact p
  have core (j : Fin 7) : S (den (col j)) := by
    apply Classical.byContradiction
    intro missing
    apply (post_data i).2.2.2 j
    apply CoThetaBits.live_coverage _ live
    intro f hf
    obtain ⟨w,hw,eq⟩ := present f hf
    have ne : w≠col j := by
      intro same
      exact missing (same ▸ (eq ▸ hf))
    exact ⟨w,List.mem_filter.mpr ⟨hw,by simp [ne]⟩,eq⟩
  have raw_has {w : Wire} (hw : w∈CoThetaBits.raw) : S (den w) := by
    obtain ⟨j,e⟩ := CoThetaBits.indexed hw
    exact e ▸ core j
  have perm := (post_data i).2.2.1
  by_cases hit : S (den (numberedWord i))
  · right
    intro f
    refine ⟨present f,?_⟩
    rintro ⟨w,hw,eq⟩
    rcases List.mem_cons.mp (perm.mem_iff.mp hw) with z|r
    · subst w
      exact eq ▸ hit
    · exact eq ▸ raw_has r
  · left
    intro f
    constructor
    · intro hf
      obtain ⟨w,m,eq⟩ := present f hf
      rcases List.mem_cons.mp (perm.mem_iff.mp m) with e|r
      · subst w
        exact (hit (eq ▸ hf)).elim
      · exact ⟨w,r,eq⟩
    · rintro ⟨w,hw,eq⟩
      exact eq ▸ raw_has hw

def RawNine : Prop := ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep CoThetaBits.raw S → False
def AfterNine : Prop := ∀ i : Fin 13, ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep (postPool i) S → False

theorem impossible_after (r9 : RawNine) (p9 : AfterNine) (i : Fin 13)
    {n ws} (run : Free ((numbered i).value::vertices7) n ws) (n9 : n≤9) (out : ans7∈ws) : False := by
  let basis := ((numbered i).value::vertices7).map (restrict toRows)
  have zero : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
  have goal := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at goal
  obtain ⟨k,S,le,live,sub⟩ := rewind (run.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  rcases classify_pool i live (fun f hf => collect_init i (sub f hf)) with raw|extra
  · exact r9 live (by omega) raw
  · exact p9 i live (by omega) extra

theorem seven_bound (r9 : RawNine) (p9 : AfterNine) {n ws} (run : Free vertices7 n ws)
    (out : ans7∈ws) : 11≤n := by
  apply Classical.byContradiction
  intro ne
  rcases select_program run (by omega) out with ⟨h,ys,cost,reduced,goal⟩ | ⟨i,h,ys,cost,reduced,goal⟩
  · let raw0 := (vertices7.map (restrict toRows))
    have zero : absentBit∈raw0 := List.mem_cons_self
    have endw := List.mem_map_of_mem (f:=restrict toRows) goal
    rw [numeric_target] at endw
    obtain ⟨m,S,le,live,sub⟩ := rewind (reduced.map_rows toRows) zero
      (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
    have rep := CoThetaBits.root_rep live (by
      intro f hf
      obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
      subst f
      rcases List.mem_cons.mp hw with z|l
      · subst w
        exact Or.inl rfl
      · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
        subst w
        exact Or.inr ⟨j,(proj_raw j).symm⟩)
    exact r9 live (by omega) rep
  · exact impossible_after r9 p9 i reduced cost goal

end CoThetaSeven
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def Supported (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ guardedSearch k out=true

private theorem support_from {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, Supported k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact guarded_complete tail k enough out d ro

theorem supported_step {m k S} {ws : List Wire} (run : Live (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      Supported k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact support_from op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply support_from (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaBits (Wire Row Rep den)

def keepIndex (a b : Bool) : Nat := a.toNat+2*b.toNat

theorem pair7_index : ∀ a b : Fin 7, a.val<b.val →
    ∃ q : Fin 21, firstPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem pair8_index : ∀ a b : Fin 8, a.val<b.val →
    ∃ q : Fin 28, secondPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem first_keep (op : Kind) : ∀ a b : Fin 7, a.val<b.val → ∀ ka kb : Bool,
    cover (extension rootWords (nth rootWords a.val) (nth rootWords b.val) op ka kb)=all → ka=true ∧ kb=true := by
  cases op <;> decide +kernel

theorem first_repr (op : Kind) (q : Fin 21) :
    let pair := firstPairs[q.val]?.getD (0,1)
    extension rootWords (nth rootWords pair.1) (nth rootWords pair.2) op true true =
    firstWords (4*q.val+opIndex op) := by
  revert q
  cases op <;> decide +kernel

theorem class_data : ∀ i : Fin 13, (postPool i).length=8 ∧ CoThetaBits.target∉postPool i := by decide +kernel
theorem target_out : CoThetaBits.target∉CoThetaBits.raw := by decide +kernel

theorem root_from_cases (checks : ∀ i : Fin 84, guardedSearch 8 (firstWords i.val)=false) : RawNine := by
  intro m S live cost rep
  obtain ⟨a,b,ab,limit,op,ka,kb,hit⟩ := supported_step live CoThetaBits.raw_nodup rep cost target_out
  change b<7 at limit
  let u : Fin 7 := ⟨a,by omega⟩
  let v : Fin 7 := ⟨b,limit⟩
  obtain ⟨q,eq⟩ := pair7_index u v ab
  obtain ⟨_,_,_,cov,more⟩ := hit
  obtain ⟨k1,k2⟩ := first_keep op u v ab ka kb cov
  subst ka
  subst kb
  have link := first_repr op q
  change firstPairs[q.val]?.getD (0,1)=(a,b) at eq
  rw [eq] at link
  change guardedSearch 8 (extension rootWords (nth rootWords a) (nth rootWords b) op true true)=true at more
  rw [link] at more
  have bound : 4*q.val+opIndex op<84 := by
    have h := q.isLt
    cases op <;> simp [opIndex] <;> omega
  exact Bool.false_ne_true ((checks ⟨_,bound⟩).symm.trans more)

theorem digits (q : Nat) (op : Kind) (ka kb : Bool) :
    let n := 16*q+4*opIndex op+keepIndex ka kb
    n/16=q ∧ (n/4) % 4=opIndex op ∧ n % 4=keepIndex ka kb := by
  cases op <;> cases ka <;> cases kb <;> simp [opIndex,keepIndex] <;> omega

theorem bits_op (op : Kind) (a b : Word) : kinds (opIndex op) a b=wordGate op a b := by cases op <;> rfl

theorem prefix_conflict (label q : Nat) (qBound : q<28) {a b : Nat}
    (pair : secondPairs[q]?.getD (0,1)=(a,b)) (op : Kind) (ka kb : Bool)
    (hit : Supported 8 (firstWords label) (nth (firstWords label) a) (nth (firstWords label) b) op ka kb) :
    ∃ j : Fin 448, prefixCase label j.val=false := by
  let j := 16*q+4*opIndex op+keepIndex ka kb
  have cap : j<448 := by cases op <;> cases ka <;> cases kb <;> simp [j,opIndex,keepIndex] <;> omega
  refine ⟨⟨j,cap⟩,?_⟩
  obtain ⟨hq,ho,hk⟩ := digits q op ka kb
  change j/16=q at hq
  change (j/4) % 4=opIndex op at ho
  change j % 4=keepIndex ka kb at hk
  obtain ⟨non,fresh,width,cov,yes⟩ := hit
  simp only [prefixCase,hq,ho,hk,pair,bits_op,Prod.fst,Prod.snd]
  cases ka <;> cases kb <;>
    simp [extension,keepList,restOf] at width cov yes <;>
    simp [keepIndex,restOf,non,fresh,Nat.not_lt_of_ge width,cov,yes]

theorem after_from_cases (checks : ∀ i : Fin 13, ∀ j : Fin 448, prefixCase (numbers.getD i.val 0) j.val=true) :
    AfterNine := by
  intro i m S live bound rep
  obtain ⟨n,stop⟩ := class_data i
  obtain ⟨a,b,ab,lb,op,ka,kb,hit⟩ := supported_step live (post_data i).1 rep bound stop
  rw [n] at lb
  obtain ⟨q,eq⟩ := pair8_index ⟨a,by omega⟩ ⟨b,lb⟩ ab
  rw [(post_data i).2.1] at hit
  obtain ⟨j,fault⟩ := prefix_conflict (numbers.getD i.val 0) q.val q.isLt eq op ka kb hit
  exact Bool.false_ne_true (fault.symm.trans (checks i j))

theorem combine_blocks (tests : ∀ i : Fin 13, ∀ b : Fin 38,
    casesBlock (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true) :
    ∀ i : Fin 13, ∀ j : Fin 448, prefixCase (numbers.getD i.val 0) j.val=true := by
  intro i j
  let b : Fin 38 := ⟨j.val/12,by have h := j.isLt; omega⟩
  have all := tests i b
  have d : j.val % 12 < min 12 (448-12*b.val) := by
    have h := j.isLt
    dsimp [b]
    omega
  have yes := List.all_eq_true.mp all (j.val % 12) (List.mem_range.mpr d)
  have eq : 12*b.val+j.val % 12=j.val := by dsimp [b]; omega
  exact eq ▸ yes

end CoThetaSeven

namespace CoNatBench
def rankSignal (z : Word) : Nat :=
  if z.1<0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 || (z.1==0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 && z.2<0x800000000000008004000100008020000000020000010200008020000080000020020801080800801010010008) then (if z.1<0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 || (z.1==0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 && z.2<0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0) then (if z.1<0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 || (z.1==0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 && z.2<0x1030a5c100000000800004000624b84e7500004000c080000040808240d1800000000004268c26311c0d1b8e1380002080300821010c0) then (if z.1<0x7fffffffffffffffffffffff8000000000000000000000000000000000000 || (z.1==0x7fffffffffffffffffffffff8000000000000000000000000000000000000 && z.2<0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300) then (if z.1<0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff || (z.1==0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2<0x5800802c008110e8000080030000040000002020200000ae02814108815409a4a0020353a8408120946400202291440481e0da03b0) then (if z.1<0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0x50138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2==0x80800800000002800400090010a02000080026001401120010a070200282208260134a11080a28a2181401404a then 6 else 20) else (if z.1==0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 8 else 20)) else (if z.1<0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 || (z.1==0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2<0x200000003490e800400001000110020001087030000000403250e40040019ea0c0040001913118c2380800100633e19704e0408c0220) then (if z.1==0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2==0x5800802c008110e8000080030000040000002020200000ae02814108815409a4a0020353a8408120946400202291440481e0da03b0 then 0 else 20) else (if z.1<0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 || (z.1==0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2<0x406920d0000100008000020002000c061000000000000000c4ab09758cd800010000044262c26305c0d07860b80002080300801000c0) then (if z.1==0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2==0x200000003490e800400001000110020001087030000000403250e40040019ea0c0040001913118c2380800100633e19704e0408c0220 then 0 else 20) else (if z.1==0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2==0x406920d0000100008000020002000c061000000000000000c4ab09758cd800010000044262c26305c0d07860b80002080300801000c0 then 0 else 20)))) else (if z.1<0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x88001000100000890c28011000c07000000002020009020200c02080019400142a021c05984c02c0501805800c) then (if z.1<0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff || (z.1==0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1==0x7fffffffffffffffffffffff8000000000000000000000000000000000000 && z.2==0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300 then 0 else 20) else (if z.1==0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 8 else 20)) else (if z.1<0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff || (z.1==0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff && z.2<0x28810014408024e08001000570240d402820224ab2008000600000008001000042000035ca8408120952401202491440082e31a18b0) then (if z.1==0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x88001000100000890c28011000c07000000002020009020200c02080019400142a021c05984c02c0501805800c then 6 else 20) else (if z.1<0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 || (z.1==0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 && z.2<0x80000201854c0804000020001934620003ab333002001040020404000000182000000001943118c8380800100634e18710e0400c0020) then (if z.1==0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff && z.2==0x28810014408024e08001000570240d402820224ab2008000600000008001000042000035ca8408120952401202491440082e31a18b0 then 0 else 20) else (if z.1==0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 && z.2==0x80000201854c0804000020001934620003ab333002001040020404000000182000000001943118c8380800100634e18710e0400c0020 then 0 else 20))))) else (if z.1<0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 || (z.1==0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 && z.2<0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220) then (if z.1<0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff || (z.1==0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff && z.2<0x20002002848808000000088054008b0094a42000000002000401120118b030000080200220030a01080820a8181401440a) then (if z.1<0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00) then (if z.1==0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 && z.2==0x1030a5c100000000800004000624b84e7500004000c080000040808240d1800000000004268c26311c0d1b8e1380002080300821010c0 then 0 else 20) else (if z.1==0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00 then 0 else 20)) else (if z.1<0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 || (z.1==0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff && z.2==0x20002002848808000000088054008b0094a42000000002000401120118b030000080200220030a01080820a8181401440a then 6 else 20) else (if z.1<0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff || (z.1==0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff && z.2<0x9000016c088356680010801500401002820224a32008002a00800000015408a4a00201152800802004040000269144048361ca0b30) then (if z.1==0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 8 else 20) else (if z.1==0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff && z.2==0x9000016c088356680010801500401002820224a32008002a00800000015408a4a00201152800802004040000269144048361ca0b30 then 0 else 20)))) else (if z.1<0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff || (z.1==0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1<0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 || (z.1==0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 && z.2<0x201080203890f190713101e00000000000004000400101803850f0887021e6ccf8c70380010000020000000040030010040100e00300) then (if z.1==0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 && z.2==0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220 then 0 else 20) else (if z.1<0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x80800301c16e026702463c001c24701822f383c683c61e00000400000000000001081800040000080000000000040000180201000c00) then (if z.1==0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 && z.2==0x201080203890f190713101e00000000000004000400101803850f0887021e6ccf8c70380010000020000000040030010040100e00300 then 0 else 20) else (if z.1==0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x80800301c16e026702463c001c24701822f383c683c61e00000400000000000001081800040000080000000000040000180201000c00 then 0 else 20))) else (if z.1<0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 || (z.1==0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 && z.2<0x80000000008001a8005000000000880408015001c1300000008a220021061202c120000084000422020c41880c00c0101821800c) then (if z.1==0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 8 else 20) else (if z.1<0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff || (z.1==0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff && z.2<0x2d810804800035aa8001080460200d400000004a92008008c0201410880400924a002024a88400100956401200010400003a3521990) then (if z.1==0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 && z.2==0x80000000008001a8005000000000880408015001c1300000008a220021061202c120000084000422020c41880c00c0101821800c then 6 else 20) else (if z.1==0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff && z.2==0x2d810804800035aa8001080460200d400000004a92008008c0201410880400924a002024a88400100956401200010400003a3521990 then 0 else 20)))))) else (if z.1<0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff || (z.1==0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff && z.2<0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0) then (if z.1<0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 || (z.1==0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 && z.2<0xa000020091d46800000021000834220001297110000010401054640040008aa0400400008011184a1808001006116093106000040000) then (if z.1<0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x103825d004022026b02465c00644b90f9605084c68dce0e00000000000100000001081800080000100001808100000000080203001c00) then (if z.1<0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 || (z.1==0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 && z.2<0x4071a0e008011190b13102e0000008000000000040010180c8a311d9b0e0604d38c307800200000400004000c0000000000100600100) then (if z.1==0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 && z.2==0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0 then 0 else 20) else (if z.1==0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 && z.2==0x4071a0e008011190b13102e0000008000000000040010180c8a311d9b0e0604d38c307800200000400004000c0000000000100600100 then 0 else 20)) else (if z.1<0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 || (z.1==0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1==0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x103825d004022026b02465c00644b90f9605084c68dce0e00000000000100000001081800080000100001808100000000080203001c00 then 0 else 20) else (if z.1<0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 || (z.1==0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 7 else 20) else (if z.1==0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 7 else 20)))) else (if z.1<0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 || (z.1==0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 && z.2<0x6021a060109170801131036000000800000040004001018050f17098f060a2c4584705800000000600000000c0010010000000200000) then (if z.1<0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 || (z.1==0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 && z.2<0x141236c50000100000000420020498c23500004000408000040a90834855800000000044020422314c04098e098000208030000000040) then (if z.1==0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 && z.2==0xa000020091d46800000021000834220001297110000010401054640040008aa0400400008011184a1808001006116093106000040000 then 0 else 20) else (if z.1==0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 && z.2==0x141236c50000100000000420020498c23500004000408000040a90834855800000000044020422314c04098e098000208030000000040 then 0 else 20)) else (if z.1<0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x181024f008166002102466c00286db029607185c204ce1600000400000100000001081800000000180000808000000000180000000400) then (if z.1==0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 && z.2==0x6021a060109170801131036000000800000040004001018050f17098f060a2c4584705800000000600000000c0010010000000200000 then 0 else 20) else (if z.1<0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff || (z.1==0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff && z.2<0x480000200020020488080009002b0050048a049c240000080024011400100118305020020220824091c2100002282a0804004442) then (if z.1==0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x181024f008166002102466c00286db029607185c204ce1600000400000100000001081800000000180000808000000000180000000400 then 0 else 20) else (if z.1==0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff && z.2==0x480000200020020488080009002b0050048a049c240000080024011400100118305020020220824091c2100002282a0804004442 then 11 else 20))))) else (if z.1<0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 || (z.1==0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 && z.2<0x80000080408001280050001000000908680050014150004040886200aa045206410080011400140a001444914412404008248004) then (if z.1<0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 || (z.1==0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 && z.2<0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0) then (if z.1<0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 || (z.1==0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 && z.2<0xa0000201b55ca804400021001924620002a31330020010003214a400000114a080000001153008ca280000000226a18514a040880220) then (if z.1==0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff && z.2==0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0 then 0 else 20) else (if z.1==0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 && z.2==0xa0000201b55ca804400021001924620002a31330020010003214a400000114a080000001153008ca280000000226a18514a040880220 then 0 else 20)) else (if z.1<0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 || (z.1==0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 && z.2<0x607120e03811b110f01103a0000008000000000000000080f8b3b15190e144c9a8c10680030000060000400080020000040100c00300) then (if z.1==0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 && z.2==0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0 then 0 else 20) else (if z.1<0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 || (z.1==0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 && z.2<0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00) then (if z.1==0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 && z.2==0x607120e03811b110f01103a0000008000000000000000080f8b3b15190e144c9a8c10680030000060000400080020000040100c00300 then 0 else 20) else (if z.1==0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 && z.2==0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00 then 0 else 20)))) else (if z.1<0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 || (z.1==0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 && z.2<0x1436b34d0000100088000420062428cc45000000008000000c4a309518cc80001000004024ac0611540916821a8000000010082101080) then (if z.1<0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 || (z.1==0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 && z.2<0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0) then (if z.1==0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 && z.2==0x80000080408001280050001000000908680050014150004040886200aa045206410080011400140a001444914412404008248004 then 11 else 20) else (if z.1<0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 || (z.1==0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 && z.2<0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220) then (if z.1==0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 && z.2==0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0 then 0 else 20) else (if z.1==0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 && z.2==0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220 then 0 else 20))) else (if z.1<0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 || (z.1==0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 && z.2<0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300) then (if z.1==0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 && z.2==0x1436b34d0000100088000420062428cc45000000008000000c4a309518cc80001000004024ac0611540916821a8000000010082101080 then 0 else 20) else (if z.1<0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x183821701c14e024f004274007c66f0d062a383448b421a000004000000000000000008000c0000180001000100040000100203001800) then (if z.1==0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 && z.2==0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300 then 0 else 20) else (if z.1==0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x183821701c14e024f004274007c66f0d062a383448b421a000004000000000000000008000c0000180001000100040000100203001800 then 0 else 20))))))) else (if z.1<0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff || (z.1==0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff && z.2<0xa0004a01b5fce8244284a908193d622b83ff77bb069cb460325ce42641159fb2c11cb071b5339aeaba6893da173febbfbef8548d466a) then (if z.1<0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x0) then (if z.1<0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 && z.2<0x480000200020020408000009002900500482048c0400000000000100000001081000000000000000808000000000080000000400) then (if z.1<0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 || (z.1==0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 && z.2<0x0) then (if z.1<0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff || (z.1==0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff && z.2<0x0) then (if z.1==0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 && z.2==0x800000000000008004000100008020000000020000010200008020000080000020020801080800801010010008 then 5 else 20) else (if z.1==0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff && z.2==0x0 then 0 else 20)) else (if z.1<0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 || (z.1==0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 && z.2<0x4800000000000000000000090023000004000408000000080024011000000000004020020200804090c010000208020000000040) then (if z.1==0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 && z.2==0x0 then 0 else 20) else (if z.1<0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 || (z.1==0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 && z.2<0x0) then (if z.1==0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 && z.2==0x4800000000000000000000090023000004000408000000080024011000000000004020020200804090c010000208020000000040 then 0 else 20) else (if z.1==0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 && z.2==0x0 then 0 else 20)))) else (if z.1<0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 || (z.1==0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 && z.2<0x804000000000000010000001086000000000400040400040008a0040040000800110001008001004114012004000040000) then (if z.1<0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 || (z.1==0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 && z.2<0x0) then (if z.1==0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 && z.2==0x480000200020020408000009002900500482048c0400000000000100000001081000000000000000808000000000080000000400 then 0 else 20) else (if z.1==0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 && z.2==0x0 then 0 else 20)) else (if z.1<0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 || (z.1==0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 && z.2<0x0) then (if z.1==0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 && z.2==0x804000000000000010000001086000000000400040400040008a0040040000800110001008001004114012004000040000 then 0 else 20) else (if z.1<0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 || (z.1==0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 && z.2<0x80000080408001200040000000000000400040010100004040886000a20450060100000000000000000040010010000000200000) then (if z.1==0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 && z.2==0x0 then 0 else 20) else (if z.1==0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 && z.2==0x80000080408001200040000000000000400040010100004040886000a20450060100000000000000000040010010000000200000 then 0 else 20))))) else (if z.1<0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 && z.2<0x28010014008024e00001000540240d0028202048b0008000000000000000000000000000c0000000001000100040000000203001800) then (if z.1<0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 || (z.1==0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 && z.2<0x12408800440000000110040000282022002000000220080000001140080000001152000802000000000268104048040880220) then (if z.1<0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff || (z.1==0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff && z.2<0xc80000a040a003ac88580019002b895c6c8b549de570004840ae6314ab16531ef170a0039620966a93de55994e3aea581c25c44e) then (if z.1==0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x0 then 0 else 20) else (if z.1==0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff && z.2==0xc80000a040a003ac88580019002b895c6c8b549de570004840ae6314ab16531ef170a0039620966a93de55994e3aea581c25c44e then 12 else 20)) else (if z.1<0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 || (z.1==0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 && z.2<0x24810800000000880000000420200c400000000080000008402014108800001000000024a8040010091600120000000000082101080) then (if z.1==0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 && z.2==0x12408800440000000110040000282022002000000220080000001140080000001152000802000000000268104048040880220 then 0 else 20) else (if z.1<0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 || (z.1==0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 && z.2<0x50008028008110e0000080000000000000000000000000a802814100814409a0800200030000000000400000020000040100c00300) then (if z.1==0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 && z.2==0x24810800000000880000000420200c400000000080000008402014108800001000000024a8040010091600120000000000082101080 then 0 else 20) else (if z.1==0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 && z.2==0x50008028008110e0000080000000000000000000000000a802814100814409a0800200030000000000400000020000040100c00300 then 0 else 20)))) else (if z.1<0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 || (z.1==0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 && z.2<0x0) then (if z.1<0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff || (z.1==0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff && z.2<0x2d858816c28837eea849888570b40ff82d606afafbcac20ae0a81670995551ba5b8b2737faac2a1a2f5f7cb312e9b6cae9bf7db5ffa) then (if z.1==0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 && z.2==0x28010014008024e00001000540240d0028202048b0008000000000000000000000000000c0000000001000100040000000203001800 then 0 else 20) else (if z.1<0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff || (z.1==0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff && z.2<0x2d890816c88c3dee9a810d0571240d48b8e6a25fb21c970ae42c1cb6a81ff0ff6a6c323dfa9d48134bf661d65bfdd56c4d3fbff9bbc) then (if z.1==0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff && z.2==0x2d858816c28837eea849888570b40ff82d606afafbcac20ae0a81670995551ba5b8b2737faac2a1a2f5f7cb312e9b6cae9bf7db5ffa then 1 else 20) else (if z.1==0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff && z.2==0x2d890816c88c3dee9a810d0571240d48b8e6a25fb21c970ae42c1cb6a81ff0ff6a6c323dfa9d48134bf661d65bfdd56c4d3fbff9bbc then 1 else 20))) else (if z.1<0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 || (z.1==0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 && z.2<0x200000003090e000400001000000000000004000000000003050e00040018680c0040000010000020000000000030010040000800200) then (if z.1==0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 && z.2==0x0 then 0 else 20) else (if z.1<0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x80000201814c0004000020001824600002a3030002001000000400000000000000000000040000080000000000040000100000000000) then (if z.1==0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 && z.2==0x200000003090e000400001000000000000004000000000003050e00040018680c0040000010000020000000000030010040000800200 then 0 else 20) else (if z.1==0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x80000201814c0004000020001824600002a3030002001000000400000000000000000000040000080000000000040000100000000000 then 0 else 20)))))) else (if z.1<0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff || (z.1==0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff && z.2<0x6071e8e038b1f1b0f3b58be80009082b8054448b449da5a0f8fbf1fff1f5e7dff9dfb7f0230282268260d3cad10b0a38ae1914e1474a) then (if z.1<0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff || (z.1==0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff && z.2<0x1436b7cd0002100288284ca08624b8cefd054048b0c9ca420c4ab09778ddc01130118b4726ac2e335c2f1fbebb9080a28ab18961154ca) then (if z.1<0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff || (z.1==0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff && z.2<0xa2d81281fddceb5ee80031805f3662d403ab7334ab201840be56e5414881dea9e4a40203dfb958cb389d64112637f1d714e3e3de1bb0) then (if z.1<0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 || (z.1==0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 && z.2<0xa0008201b5dce88441a82150193462008baf7b315201d1703254e48a6201bfa6d206c12195319cca3c2a021c47bfed97d4f058ad822c) then (if z.1==0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff && z.2==0xa0004a01b5fce8244284a908193d622b83ff77bb069cb460325ce42641159fb2c11cb071b5339aeaba6893da173febbfbef8548d466a then 4 else 20) else (if z.1==0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 && z.2==0xa0008201b5dce88441a82150193462008baf7b315201d1703254e48a6201bfa6d206c12195319cca3c2a021c47bfed97d4f058ad822c then 13 else 20)) else (if z.1<0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 || (z.1==0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 && z.2<0x406120c00001000080000200000008000000000000000000c0a3015180c0000100000400020000040000400080000000000000000000) then (if z.1==0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff && z.2==0xa2d81281fddceb5ee80031805f3662d403ab7334ab201840be56e5414881dea9e4a40203dfb958cb389d64112637f1d714e3e3de1bb0 then 10 else 20) else (if z.1<0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x103025c000000000800004000604b80e1400004000c080000000000000100000000000000080000100001808100000000000002001000) then (if z.1==0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 && z.2==0x406120c00001000080000200000008000000000000000000c0a3015180c0000100000400020000040000400080000000000000000000 then 0 else 20) else (if z.1==0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x103025c000000000800004000604b80e1400004000c080000000000000100000000000000080000100001808100000000000002001000 then 0 else 20)))) else (if z.1<0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff || (z.1==0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff && z.2<0x143fb7cd16c09835ee8005280774bccf752820624af280800eeab89758dd95409a4a006437fea6395e0d5fce1b826934c0783e3da1bf0) then (if z.1<0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 || (z.1==0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 && z.2<0x1436bfcd00081408881a84250625b8ce7d90c6c015c09c170c4eb49ffefd8ab075206c562eac3f715d4fbfafdfd994e1ac3509a3590cc) then (if z.1==0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff && z.2==0x1436b7cd0002100288284ca08624b8cefd054048b0c9ca420c4ab09778ddc01130118b4726ac2e335c2f1fbebb9080a28ab18961154ca then 13 else 20) else (if z.1==0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 && z.2==0x1436bfcd00081408881a84250625b8ce7d90c6c015c09c170c4eb49ffefd8ab075206c562eac3f715d4fbfafdfd994e1ac3509a3590cc then 4 else 20)) else (if z.1<0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 || (z.1==0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 && z.2<0x1e36b7ed1b5dde80cc00063007b7feee753ab77300e081040f6ffed75cdd99ea1c0040443fff37bdff8d9f8f1be37e39f17e0c29c12e0) then (if z.1==0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff && z.2==0x143fb7cd16c09835ee8005280774bccf752820624af280800eeab89758dd95409a4a006437fea6395e0d5fce1b826934c0783e3da1bf0 then 10 else 20) else (if z.1<0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x0) then (if z.1==0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 && z.2==0x1e36b7ed1b5dde80cc00063007b7feee753ab77300e081040f6ffed75cdd99ea1c0040443fff37bdff8d9f8f1be37e39f17e0c29c12e0 then 2 else 20) else (if z.1==0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x0 then 0 else 20))))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2<0x183825f01c16e026f02c6fc087c6ff0fbe2f787cf8fdebe20000c0026011401120118b8702c028238826193cb110c0a28ba1a17015c4a) then (if z.1<0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff || (z.1==0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff && z.2<0x62f9b0e17c99f3def93113e0570248d402824224eb210980fef3f1d9f8e1f6cdfce707835fa8408720956401e02791540483e3fa1bb0) then (if z.1<0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x6071a0e03891f190f1b903f000100800890c68015001c1f0f8f3f1dbf2e1efcffac7c7a083019406142a421cc59b4c12c45118e5830c) then (if z.1==0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff && z.2==0x6071e8e038b1f1b0f3b58be80009082b8054448b449da5a0f8fbf1fff1f5e7dff9dfb7f0230282268260d3cad10b0a38ae1914e1474a then 4 else 20) else (if z.1==0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x6071a0e03891f190f1b903f000100800890c68015001c1f0f8f3f1dbf2e1efcffac7c7a083019406142a421cc59b4c12c45118e5830c then 13 else 20)) else (if z.1<0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 || (z.1==0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 && z.2<0xe071a2e1bdddf994f13123e019346a0003ab7330420111c0faf7f5d9f0e1feedf8c70781973118ce38084010c637e19714e140ec0320) then (if z.1==0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff && z.2==0x62f9b0e17c99f3def93113e0570248d402824224eb210980fef3f1d9f8e1f6cdfce707835fa8408720956401e02791540483e3fa1bb0 then 10 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 && z.2<0x1637bfcf03891f198f13143e0624b8ce7500044004c090180fcfbf9fdfdf9e6cdf8c707c26bc26317c0d1f8e1f8030218070182f013c0) then (if z.1==0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 && z.2==0xe071a2e1bdddf994f13123e019346a0003ab7330420111c0faf7f5d9f0e1feedf8c70781973118ce38084010c637e19714e140ec0320 then 9 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 && z.2==0x1637bfcf03891f198f13143e0624b8ce7500044004c090180fcfbf9fdfdf9e6cdf8c707c26bc26317c0d1f8e1f8030218070182f013c0 then 3 else 20)))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2<0x1a3825f01f5feea6f42467d007d7ff2f963fbf7f68fce1e403254e40041019ea0c10c18019d3118da380980910637e1971ce2438c1e20) then (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x18382df01c1ee42ef03ee7c507c7ff0f9ebffefc7dfcfdf700044408a6300ab06530ed9208c019418142b829d459d4c12d8521b259c0c) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2==0x183825f01c16e026f02c6fc087c6ff0fbe2f787cf8fdebe20000c0026011401120118b8702c028238826193cb110c0a28ba1a17015c4a then 13 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2<0x183da5f81ed6e837fea467c807f6ff0fd62f387e6afee1e00ae06814109815409a5a81a035fa840992095e481202691441c83e3da1fb0) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x18382df01c1ee42ef03ee7c507c7ff0f9ebffefc7dfcfdf700044408a6300ab06530ed9208c019418142b829d459d4c12d8521b259c0c then 4 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2==0x183da5f81ed6e837fea467c807f6ff0fd62f387e6afee1e00ae06814109815409a5a81a035fa840992095e481202691441c83e3da1fb0 then 10 else 20))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2<0x1c3eb7fd1c16f026f82467e007e6ffcff72f387c68fce1e00c4af09758dd8000101081c426ec2631dc0d1f8e1b80402081b0283101cc0) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2==0x1a3825f01f5feea6f42467d007d7ff2f963fbf7f68fce1e403254e40041019ea0c10c18019d3118da380980910637e1971ce2438c1e20 then 3 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 && z.2<0x1e3f3ffe1f9fff3fff3777fe07c6ff8f962f3c7c6cfcf1f80f8f7f1d9f1e1e6cdf9cf1f800f00001e0001c081c00700101c0303e01f00) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2==0x1c3eb7fd1c16f026f82467e007e6ffcff72f387c68fce1e00c4af09758dd8000101081c426ec2631dc0d1f8e1b80402081b0283101cc0 then 9 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 && z.2==0x1e3f3ffe1f9fff3fff3777fe07c6ff8f962f3c7c6cfcf1f80f8f7f1d9f1e1e6cdf9cf1f800f00001e0001c081c00700101c0303e01f00 then 2 else 20)))))))
def headOK (bound : Nat) : List Word → Bool
  | [] => true
  | x::_ => decide (bound≤rankSignal x)

def permittedSearch (bound : Nat) : Nat → List Word → Bool
  | 0,ws => headOK bound ws && ws.contains target
  | k+1,ws => headOK bound ws && (ws.contains target || guarded k (permittedSearch bound k) ws)

end CoNatBench

namespace CoNatBench
def permitPrefix (bound i j : Nat) : Bool :=
  let ws := firstWords i
  let p := secondPairs[j/16]?.getD (0,1)
  let a := nth ws p.1
  let b := nth ws p.2
  let z := kinds ((j/4) % 4) a b
  let rest := ws.filter (fun w => w != a && w != b)
  let next := match j % 4 with
    | 0 => z::rest
    | 1 => z::a::rest
    | 2 => z::b::rest
    | _ => z::a::b::rest
  if rankSignal z < bound || z == (0,0) || ws.contains z || next.length>9 || cover next != all then true
  else !(permittedSearch bound 8 next)

def permitBlock (bound i first count : Nat) : Bool :=
  (List.range count).all (fun d => permitPrefix bound i (first+d))


end CoNatBench

namespace CoThetaFreeCore

variable {ρ : Type}

theorem free_enlarge {raw ws : List (ρ→Bool)} {k} (run : Free raw k ws)
    (base : List (ρ→Bool)) (inc : ∀ f∈raw, f∈base) :
    ∃ xs, Free base k xs ∧ ∀ f∈ws, f∈xs := by
  induction run with
  | start => exact ⟨_,Free.start,inc⟩
  | @binary n us a b pre op ha hb ih =>
    obtain ⟨ys,prev,sub⟩ := ih
    refine ⟨_,Free.binary prev op (sub a ha) (sub b hb),?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with e|old
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub f old)

theorem free_move {raw ws : List (ρ→Bool)} {k} (run : Free raw k ws)
    {w : ρ→Bool} (atEnd : w∈ws) (notRaw : w∉raw) :
    ∃ m xs, m<k ∧ Free (w::raw) m xs ∧ ∀ f∈ws, f∈xs := by
  induction run with
  | start => exact (notRaw atEnd).elim
  | @binary n us a b pre op ha hb ih =>
    by_cases found : w∈us
    · obtain ⟨m,ys,cap,prev,sub⟩ := ih found
      refine ⟨m+1,_,by omega,Free.binary prev op (sub a ha) (sub b hb),?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with e|old
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sub f old)
    · have eq := (List.mem_cons.mp atEnd).resolve_right found
      obtain ⟨ys,prev,sub⟩ := free_enlarge pre (w::raw) (fun _ h => List.mem_cons_of_mem _ h)
      refine ⟨n,ys,by omega,prev,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with e|old
      · exact (e.trans eq.symm).symm ▸ free_keeps_raw prev List.mem_cons_self
      · exact sub f old

end CoThetaFreeCore

namespace CoThetaFreeCore
variable {ρ : Type}
inductive Marked (p : (ρ→Bool)→Prop) (goal : ρ→Bool) : Nat→((ρ→Bool)→Prop)→Prop
  | stop (allowed : p goal) : Marked p goal 0 (fun v => v=goal)
  | step {k U a b} (allowed : ∀ w, ins a (ins b U) w → p w)
      (kind : Kind) (ab : a≠b) (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Marked p goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Marked p goal (k+1) (ins a (ins b U))

theorem Marked.live {p : (ρ→Bool)→Prop} {goal k S} (r : Marked p goal k S) : Live goal k S := by
  induction r with
  | stop => exact .stop
  | step _ op ab ha hb fresh _ ih => exact .step op ab ha hb fresh ih

theorem Marked.allowed {p : (ρ→Bool)→Prop} {goal k S} (r : Marked p goal k S) : ∀ w, S w → p w := by
  cases r with
  | stop good => exact fun w h => h.symm ▸ good
  | step allow _ _ _ _ _ _ => exact allow

theorem rewindMarked {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {p : (ρ→Bool)→Prop} (hs : ∀ w∈ws, p w) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Marked p goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Marked p goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Marked p goal (k+1) (ins a (ins b U)) :=
          Marked.step (fun w h => hs w (List.mem_cons_of_mem _ (memAll w h))) kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

def allowedWire (bnd : Nat) (f : Row→Bool) : Prop := ∀ v : Wire, den v=f → bnd≤rankSignal (project v)

theorem head_allowed {bnd ws S} (rep : Rep ws S) (h : ∀ f, S f → allowedWire bnd f) :
    headOK bnd (ws.map project)=true := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    change decide (bnd≤rankSignal (project w))=true
    exact decide_eq_true_eq.mpr (h (den w) ((rep _).2 ⟨w,List.mem_cons_self,rfl⟩) w rfl)

private theorem marked_direction (bnd : Nat) {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      permittedSearch bnd k (zs.map project)=true) :
    pairTry k (permittedSearch bnd k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem marked_complete (bnd : Nat) {m S} (run : Marked (allowedWire bnd) (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → permittedSearch bnd fuel (ws.map project)=true := by
  classical
  induction run with
  | stop permitted =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    have good := head_allowed rep (fun _ eq => eq.symm ▸ permitted)
    cases fuel <;> simp [permittedSearch,good,target,hit]
  | @step m U a b admissible kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail.live
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail.live
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → permittedSearch bnd k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := marked_direction bnd kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (permittedSearch bnd k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply marked_direction bnd (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (permittedSearch bnd k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [permittedSearch,head_allowed rep admissible,Bool.true_and,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench

namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def MarkSupport (bnd : Nat) (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ permittedSearch bnd k out=true

private theorem marked_support_from (bnd : Nat) {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Marked (allowedWire bnd) (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, MarkSupport bnd k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail.live d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail.live (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact marked_complete bnd tail k enough out d ro

theorem marked_step (bnd : Nat) {m k S} {ws : List Wire} (run : Marked (allowedWire bnd) (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      MarkSupport bnd k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b admissible op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Marked (allowedWire bnd) (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.live.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact marked_support_from bnd op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply marked_support_from bnd (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem allowed_head {bnd k w ws} (yes : permittedSearch bnd k (w::ws)=true) : bnd≤rankSignal w := by
  cases k <;> simp only [permittedSearch,headOK,Bool.and_eq_true,decide_eq_true_eq] at yes <;> exact yes.1

end CoNatBench
namespace CoThetaSeven
open CoNatBench CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)
theorem marked_conflict (bnd label q : Nat) (qBound : q<28) {a b : Nat}
    (pair : secondPairs[q]?.getD (0,1)=(a,b)) (op : Kind) (ka kb : Bool)
    (hit : MarkSupport bnd 8 (firstWords label) (nth (firstWords label) a) (nth (firstWords label) b) op ka kb) :
    ∃ j : Fin 448, permitPrefix bnd label j.val=false := by
  let j := 16*q+4*opIndex op+keepIndex ka kb
  have cap : j<448 := by cases op <;> cases ka <;> cases kb <;> simp [j,opIndex,keepIndex] <;> omega
  refine ⟨⟨j,cap⟩,?_⟩
  obtain ⟨hq,ho,hk⟩ := digits q op ka kb
  change j/16=q at hq
  change (j/4) % 4=opIndex op at ho
  change j % 4=keepIndex ka kb at hk
  obtain ⟨non,fresh,width,cov,yes⟩ := hit
  have certified : bnd≤rankSignal (wordGate op (nth (firstWords label) a) (nth (firstWords label) b)) := allowed_head yes
  simp only [permitPrefix,hq,ho,hk,pair,bits_op,Prod.fst,Prod.snd]
  cases ka <;> cases kb <;>
    simp [extension,keepList,restOf] at width cov yes <;>
    simp [keepIndex,restOf,non,fresh,Nat.not_lt_of_ge width,Nat.not_lt_of_ge certified,cov,yes]

theorem marked_after (bnd : Nat) (i : Fin 13) (checks : ∀ j : Fin 448, permitPrefix bnd (numbers.getD i.val 0) j.val=true) :
    ∀ {m S}, Marked (allowedWire bnd) (den CoThetaBits.target) m S → m≤9 → Rep (postPool i) S → False := by
  intro m S live bound rep
  obtain ⟨n,stop⟩ := class_data i
  obtain ⟨a,b,ab,lb,op,ka,kb,hit⟩ := marked_step bnd live (post_data i).1 rep bound stop
  rw [n] at lb
  obtain ⟨q,eq⟩ := pair8_index ⟨a,by omega⟩ ⟨b,lb⟩ ab
  rw [(post_data i).2.1] at hit
  obtain ⟨j,fault⟩ := marked_conflict bnd (numbers.getD i.val 0) q.val q.isLt eq op ka kb hit
  exact Bool.false_ne_true (fault.symm.trans (checks j))

theorem marked_blocks (bnd : Nat) (i : Fin 13) (tests : ∀ b : Fin 38,
    permitBlock bnd (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true) :
    ∀ j : Fin 448, permitPrefix bnd (numbers.getD i.val 0) j.val=true := by
  intro j
  let b : Fin 38 := ⟨j.val/12,by have h := j.isLt; omega⟩
  have all := tests b
  have d : j.val % 12 < min 12 (448-12*b.val) := by
    have h := j.isLt
    dsimp [b]
    omega
  have yes := List.all_eq_true.mp all (j.val % 12) (List.mem_range.mpr d)
  have eq : 12*b.val+j.val % 12=j.val := by dsimp [b]; omega
  exact eq ▸ yes


open CoThetaNine (SmallInput vertices7 ans7 toRows numeric_target)
theorem safe_after (r9 : RawNine) (bnd : Nat) (i : Fin 13)
    (tests : ∀ j : Fin 448, CoNatBench.permitPrefix bnd (numbers.getD i.val 0) j.val=true)
    {n ws} (run : Free ((numbered i).value::vertices7) n ws) (n9 : n≤9) (out : ans7∈ws) (ok : ∀ w∈ws, CoNatBench.allowedWire bnd (restrict toRows w)) : False := by
  let basis := ((numbered i).value::vertices7).map (restrict toRows)
  have zero : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
  have goal := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at goal
  have permit : ∀ w∈ws.map (restrict toRows), CoNatBench.allowedWire bnd w := by
    intro w hw
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp hw
    exact eq ▸ ok a ha
  obtain ⟨k,S,le,live,sub⟩ := rewindMarked (run.map_rows toRows) zero permit
    (Marked.stop (permit _ goal)) (fun w e => e.symm ▸ goal)
  rcases classify_pool i live.live (fun f hf => collect_init i (sub f hf)) with raw|extra
  · exact r9 live.live (by omega) raw
  · exact marked_after bnd i tests live (by omega) extra

end CoThetaSeven

namespace CoThetaFixedOrbit
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7)
open CoThetaSix (minorLift minor_off)
open CoThetaSeven (tag picked rotation numbered raw_mem rowPerm)

def rawGate (x y : Fin 7) (k : Kind) : TraceGate SmallInput := ⟨k,raw7 x,raw7 y⟩

def singleRow (x : Fin 7) : SmallInput := CoThetaSeven.smallRow (1 <<< x.val)
def pairRow (x y : Fin 7) : SmallInput := CoThetaSeven.smallRow ((1 <<< x.val) ||| (1 <<< y.val))
def positiveRow (k : Kind) (x y : Fin 7) : SmallInput := match k with
  | .conj => pairRow x y
  | .rightOnly => singleRow y
  | _ => singleRow x
def differentRow (k : Kind) (x y j : Fin 7) : SmallInput := match k with
  | .conj => singleRow j
  | .disj => if j=x then singleRow y else singleRow x
  | .leftOnly => if j=x then pairRow x y else singleRow x
  | .rightOnly => if j=y then pairRow x y else singleRow y

theorem fresh_data (k : Kind) : ∀ (x y : Fin 7), x≠y →
    (∃ r : SmallInput, (rawGate x y k).value r ≠ false) ∧
    ∀ j : Fin 7, ∃ r : SmallInput, (rawGate x y k).value r ≠ raw7 j r := by
  have data : ∀ (x y : Fin 7), x≠y →
      (rawGate x y k).value (positiveRow k x y) ≠ false ∧
      ∀ j : Fin 7, (rawGate x y k).value (differentRow k x y j) ≠
        raw7 j (differentRow k x y j) := by
    cases k <;> decide +kernel
  intro x y xy
  exact ⟨⟨_,(data x y xy).1⟩,fun j => ⟨_,(data x y xy).2 j⟩⟩

theorem head_fresh (x y : Fin 7) (k : Kind) (xy : x≠y) :
    (rawGate x y k).value∉vertices7 := by
  intro h
  rcases List.mem_cons.mp h with z|other
  · obtain ⟨r,off⟩ := (fresh_data k x y xy).1
    exact off (congrFun z r)
  · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
    obtain ⟨r,ne⟩ := (fresh_data k x y xy).2 j
    exact ne (congrFun eq.symm r)

def RawNine : Prop := ∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws
def PostNine (i : Fin 13) : Prop := ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem named_trace {x y : Fin 7} {k : Kind} (xy : x≠y)
    {n ws} (run : Free ((rawGate x y k).value::vertices7) n ws) (hit : ans7∈ws) :
    ∃ clean, sufficient vertices7 ans7 (rawGate x y k::clean) ∧
      freshTrace vertices7 (rawGate x y k::clean) ∧ clean.length≤n := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,ok,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  exact ⟨clean,⟨⟨raw_mem x,raw_mem y,ok.1⟩,ok.2⟩,⟨head_fresh x y k xy,fresh⟩,by omega⟩

theorem dispatch (x y : Fin 7) (k : Kind) (xy : x≠y) {n ws}
    (run : Free ((rawGate x y k).value::vertices7) n ws) (small : n≤9) (hit : ans7∈ws) :
    if tag x y k < 2 then RawNine else PostNine (picked (tag x y k)) := by
  classical
  let g := rawGate x y k
  obtain ⟨gs,ok,fresh,le⟩ := named_trace xy run hit
  change sufficient vertices7 ans7 (g::gs) at ok
  change freshTrace vertices7 (g::gs) at fresh
  have size : (g::gs).length≤10 := by simp only [List.length_cons]; omega
  have rx : reads g (raw7 x) := Or.inl rfl
  have ry : reads g (raw7 y) := Or.inr rfl
  let t := tag x y k
  change (if t<2 then _ else _)
  have rule := CoThetaSeven.dispatch_rules k x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  by_cases a : t=0
  · rw [if_pos a] at rule
    rw [if_pos (by omega : t<2)]
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind k (raw7 x (minorLift x r)) (raw7 y (minorLift x r))=false
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy rx ry rule.1 drop
    exact ⟨m,vs,by omega,rest,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      rw [if_pos (by omega : t<2)]
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind k (raw7 x (minorLift y r)) (raw7 y (minorLift y r))=false
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy.symm ry rx rule.1 drop
      exact ⟨m,vs,by omega,rest,out⟩
    · rw [if_neg b] at rule
      rw [if_neg (by omega : ¬t<2)]
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := funext rule
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [CoThetaSeven.raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨vs,newRun,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (CoThetaSeven.perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact ⟨_,vs,by omega,newRun,goal⟩

end CoThetaFixedOrbit
namespace CoThetaCycleFive
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)
open CoThetaSeven (read_twice raw_mem)

def roots : List Wire := [
(0xffffffff800ffe003ff800fffffc007ff001ffffffffffe003fffff001ffc007ff001ffc007ff001fffff800ffe003ffffffffffc007ff,0xfffffffd20a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a),
(0xfffffffffff000003fffff001ffffffffffe003ff800fffffc007ffffe000007ffffe000007ffffe003ffffffffffc007ff001fffff800,0xfffffffe04c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c),
(0x3fffffffe000007fffffffc00000fffffffffffffffffff800000000007fffffffc00000ffffffff800001ffffffff,0x490921242484909212424849092124248490921242484909212424849092124248490921242484909212424849092124248490),
(0xffffffffffffffffc00000000000007fffffffffffff000000007fffffffffffffffffffff80000000000000fffffffffffffe00000000,0xe01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),
(0xffffffffffffffffffffffffffffff80000000000000000000007fffffffffffffffffffffffffffffffffff0000000000000000000000,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700)]
def basis : CoNatBench.essentialBasis roots := CoThetaSix.basisAt_sound roots [4, 15, 1, 34, 90] (by decide +kernel)
theorem nd : roots.Nodup := by decide +kernel
theorem small : CoNatBench.guardedSearch 6 (roots.map CoNatBench.project)=false := by decide +kernel

def indexAt (v : Fin 7) : Option Nat := match v.val with
  | 0 => some 0 | 1 => some 1 | 2 => some 2 | 5 => some 3 | 6 => some 4 | _ => none

def column (vertex : Fin 7) : Wire := match indexAt vertex with
  | none => CoThetaBits.zero
  | some n => roots.getD n CoThetaBits.zero
def liftRows (r : Row) : SmallInput := pack (fun j => den (column j) r)

def cycleGraph : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (column 0) (column 2)) (gate .conj (column 1) (column 2)))
    (gate .conj (column 0) (column 3))) (gate .conj (column 3) (column 4)))
    (gate .conj (column 1) (column 4))) (gate .conj (column 0) (column 5)))
    (gate .conj (column 5) (column 6))) (gate .conj (column 1) (column 6))


theorem table : cycleGraph=CoThetaBits.target := by decide +kernel

theorem input (j : Fin 7) : restrict liftRows (raw7 j)=den (column j) :=
  funext (fun r => unpack (fun v => den (column v) r) j)

theorem goal : restrict liftRows ans7=den CoThetaBits.target := by
  funext r
  change ans7 (liftRows r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (liftRows r))=(fun j => den (column j) r) :=
    funext (fun j => congrFun (input j) r)
  rw [values]
  have equality := congrFun (congrArg den table) r
  simp only [cycleGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem known : ∀ w∈vertices7, restrict liftRows w∈absentBit::roots.map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [input]
    cases h : indexAt j with
    | none => simp [column,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : roots[n]? with
      | none => simp [column,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [column,h,List.getD_eq_getElem?_getD,hn,inList]

theorem residual {gs : List (TraceGate SmallInput)} (ok : sufficient vertices7 ans7 gs) :
    7≤remaining liftRows gs := by
  obtain ⟨ws,run,all⟩ := restrict_trace liftRows gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self known
  have h := all ans7 ok.2
  rw [goal] at h
  have yes := CoNatBench.table_bound basis nd run h small
  omega

def joint (a b : Bool) (j : Fin 32) : SmallInput :=
  pack (fun i => if i=3 then a else if i=4 then b else j.val.testBit ((indexAt i).getD 0))

theorem separation : ∀ a b c d : Bool, (a,b)≠(c,d) →
    ∃ j : Fin 32, ans7 (joint a b j)≠ans7 (joint c d j) := by decide +kernel

theorem panel_fixed (a b c d : Bool) (j : Fin 32) :
    agreeOutside (fun f => f=raw7 3 ∨ f=raw7 4) (joint a b j) (joint c d j) vertices7 := by
  intro f hf outside
  rcases List.mem_cons.mp hf with z|other
  · subst f
    rfl
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp other
    subst f
    have i3 : i≠3 := fun e => outside (Or.inl (congrArg raw7 e))
    have i4 : i≠4 := fun e => outside (Or.inr (congrArg raw7 e))
    simp [joint,unpack,i3,i4]

def head : TraceGate SmallInput := ⟨.disj,raw7 3,raw7 4⟩

theorem no_live_ten {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (head::gs)) (fresh : freshTrace vertices7 (head::gs))
    (budget : (head::gs).length≤10) :
    ∃ k ws, k≤gs.length ∧ Free vertices7 k ws ∧ ans7∈ws := by
  classical
  have h3 : reads head (raw7 3) := Or.inl rfl
  have h4 : reads head (raw7 4) := Or.inr rfl
  by_cases path : UsePath gs head.value ans7
  · exfalso
    have gone3 := (input 3).trans (show den (column 3)=absentBit from CoThetaBits.den_zero)
    have gone4 := (input 4).trans (show den (column 4)=absentBit from CoThetaBits.den_zero)
    have newp (g : TraceGate SmallInput) (hg : g∈head::gs) :
        g.value≠raw7 3 ∧ g.value≠raw7 4 :=
      ⟨fun e => fresh_outputs fresh g hg (e ▸ raw_mem 3),
       fun e => fresh_outputs fresh g hg (e ▸ raw_mem 4)⟩
    have head0 : restrict liftRows head.value=absentBit := by
      funext r
      change (raw7 3 (liftRows r) || raw7 4 (liftRows r))=false
      have a := congrFun gone3 r
      have b := congrFun gone4 r
      change raw7 3 (liftRows r)=false at a
      change raw7 4 (liftRows r)=false at b
      simp only [a,b,Bool.false_or]
    have nz : restrict liftRows ans7 ≠ absentBit := by
      rw [goal]
      intro e
      have bad := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    obtain ⟨other,hm,n3,n4,drop⟩ := extra_loss_on_path liftRows gone3 gone4
      (fun g hg => newp g (List.mem_cons_of_mem _ hg)) path head0
      (newp head List.mem_cons_self) nz
    let all := head::gs
    let R := readerSet all (raw7 3) ∪ readerSet all (raw7 4)
    have card3 {a b c : TraceGate SmallInput} (ha : a∈R) (hb : b∈R) (hc : c∈R)
        (ab : a≠b) (ac : a≠c) (bc : b≠c) : 3≤R.card := by
      have sub : ({a,b,c}:Finset _) ⊆ R := by
        intro g hg
        simp only [Finset.mem_insert,Finset.mem_singleton] at hg
        rcases hg with rfl|rfl|rfl
        · exact ha
        · exact hb
        · exact hc
      have ct := Finset.card_le_card sub
      simpa [ab,ac,bc] using ct
    have from3 {g} (h : g∈all) (p : reads g (raw7 3)) : g∈R :=
      Finset.mem_union_left _ (mem_readerSet.mpr ⟨h,p⟩)
    have from4 {g} (h : g∈all) (p : reads g (raw7 4)) : g∈R :=
      Finset.mem_union_right _ (mem_readerSet.mpr ⟨h,p⟩)
    obtain ⟨A,ha,r3,ah⟩ := read_twice 3 4 (by decide) head h3 h4 ok
    obtain ⟨B,hb,r4,bh⟩ := read_twice 4 3 (by decide) head h4 h3 ok
    have three : 3≤R.card := by
      by_cases same : A=B
      · subst B
        have nraw (j : Fin 7) : ans7≠raw7 j := by
          obtain ⟨r,h⟩ := CoThetaSeven.seven_not_raw j
          exact fun e => h (congrFun e r)
        obtain ⟨row,ne⟩ := CoThetaSeven.seven_diff 3 4 (by decide)
        obtain ⟨C,hc,read,ch,ca⟩ := two_joint_readers_impossible (raw7 3) (raw7 4) ans7
          vertices7 all head A h3 h4 r3 r4 (fun e => ne (congrFun e row))
          ⟨nraw 3,nraw 4⟩ ok.1 ok.2 joint
          (fun a b j => by simp [joint,unpack])
          (fun a b j => by simp [joint,unpack]) panel_fixed separation
        exact card3 (from3 List.mem_cons_self h3) (from3 ha r3)
          (read.elim (from3 hc) (from4 hc)) ah.symm ch.symm ca.symm
      · exact card3 (from3 List.mem_cons_self h3) (from3 ha r3) (from4 hb r4)
          ah.symm bh.symm same
    have saved4 := four_saved_raw_head liftRows all (raw7 3) (raw7 4) gone3 gone4 three
      ⟨other,List.mem_cons_of_mem _ hm,n3,n4,drop⟩
    have cost := residual ok
    have eq := accounted liftRows (head::gs)
    change 4 ≤ saved liftRows (head::gs) at saved4
    omega
  · exact omit_dead_head vertices7 gs head.value ans7 ok.1.2.2 ok.2 path

end CoThetaCycleFive
namespace CoThetaCycleFive
open CoThetaNine (vertices7 ans7)
open CoThetaFreeCore
theorem no_post {n ws} (run : Free (head.value::vertices7) n ws)
    (bound : n≤9) (hit : ans7∈ws) : CoThetaFixedOrbit.RawNine := by
  obtain ⟨gs,ok,fresh,le⟩ := CoThetaFixedOrbit.named_trace (x:=3) (y:=4) (k:=.disj) (by decide) run hit
  have size : (head::gs).length≤10 := by simp only [List.length_cons]; omega
  obtain ⟨j,vs,small,prog,out⟩ := no_live_ten ok fresh size
  exact ⟨j,vs,by omega,prog,out⟩
end CoThetaCycleFive

namespace CoThetaSeven
open CoNatBench CoThetaBits CoThetaFreeCore

def orbitPriority (i : Fin 13) : Nat := ([5,12,11,1,7,4,8,13,6,10,2,9,3] : List Nat).getD i.val 20

def priority (x y : Fin 7) (op : Kind) : Nat :=
  let t := tag x y op
  if t<2 then 0 else orbitPriority (picked t)

private theorem rankLeaf {z : Word} {n p r bound : Nat} (x y : Fin 7) (op : Kind)
    (hit : (z.1==n && z.2==p)=true) (less : r<bound)
    (cert : x≠y ∧ project (gate op (col x) (col y))=(n,p) ∧ priority x y op=r) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  have eq : z=(n,p) := Prod.ext (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).1) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).2)
  exact ⟨x,y,op,cert.1,cert.2.1.trans eq.symm,lt_of_eq_of_lt cert.2.2 less⟩

private theorem rankFork {c : Prop} [Decidable c] {a b bound : Nat} {P : Prop}
    (v : (if c then a else b)<bound) (left : a<bound → P) (right : b<bound → P) : P := by
  by_cases h : c
  · rw [if_pos h] at v
    exact left v
  · rw [if_neg h] at v
    exact right v

private theorem rankMatch {c : Bool} {r bound : Nat} {P : Prop}
    (v : (if c then r else 20)<bound) (cap : bound≤13) (take : c=true → r<bound → P) : P := by
  cases c with
  | false => change 20<bound at v; omega
  | true => exact take rfl v

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rankSignal_sound (bound : Nat) (cap : bound≤13) (z : Word) (bad : rankSignal z<bound) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  unfold rankSignal at bad
  exact (rankFork bad
    (fun bad => (rankFork bad
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .leftOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .leftOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .leftOnly hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .rightOnly hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .leftOnly hit smaller (by decide +kernel))))))))))))))
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .leftOnly hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .rightOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .rightOnly hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .rightOnly hit smaller (by decide +kernel))))))))))))))))
    (fun bad => (rankFork bad
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .conj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .conj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .conj hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .disj hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .conj hit smaller (by decide +kernel))))))))))))))
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .conj hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .disj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .disj hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .disj hit smaller (by decide +kernel)))))))))))))))))
end CoThetaSeven

namespace CoThetaFreeCore
variable {ρ : Type}

theorem free_compose {raw us ws : List (ρ→Bool)} {m n} (pre : Free raw m us) (post : Free us n ws) : Free raw (m+n) ws := by
  induction post with
  | start => simpa using pre
  | binary _ op ha hb ih => exact .binary ih op ha hb

end CoThetaFreeCore

namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaNine (SmallInput raw7 vertices7 ans7 toRows numeric_target)
open CoThetaBits (den col gate)

def sampleCodes : List Nat := [0, 1, 2, 3, 4, 440, 453, 466, 37, 474, 18, 485, 5, 493, 498, 507, 40, 6, 510, 521, 7, 528, 537, 541, 544, 557, 562, 567, 570, 580, 583, 586, 151, 587, 21, 597, 8, 604, 609, 617, 113, 620, 52, 624, 9, 626, 627, 633, 79, 634, 641, 649, 94, 653, 655, 657, 658, 667, 670, 672, 673, 680, 681, 682, 155, 10, 683, 693, 11, 700, 708, 712, 44, 715, 723, 730, 66, 734, 736, 738, 116, 87, 739, 743, 12, 745, 751, 752, 753, 762, 764, 767, 768, 775, 776, 777, 778, 791, 795, 799, 802, 812, 815, 818, 819, 828, 831, 833, 834, 841, 842, 843, 844, 853, 855, 858, 859, 866, 867, 868, 869, 873, 874, 875, 876, 877, 878, 879]
def inverseRow (r : SmallInput) : CoThetaBits.Row :=
  let q := sampleCodes.getD r.val 0
  (decide (440≤q),⟨q  %  440,Nat.mod_lt _ (by decide)⟩)

theorem sample_surjective : ∀ r : SmallInput, toRows (inverseRow r)=r := by decide +kernel

theorem reflect_rows {f g : SmallInput→Bool} (h : restrict toRows f=restrict toRows g) : f=g := by
  funext r
  have e := congrFun h (inverseRow r)
  change f (toRows (inverseRow r))=g (toRows (inverseRow r)) at e
  simpa only [sample_surjective] using e

theorem raw_gate_sample (x y : Fin 7) (op : Kind) :
    restrict toRows (CoThetaFixedOrbit.rawGate x y op).value=den (gate op (col x) (col y)) := by
  rw [CoThetaBits.den_gate]
  funext r
  change applyKind op (raw7 x (toRows r)) (raw7 y (toRows r))=_
  rw [show raw7 x (toRows r)=den (col x) r from congrFun (proj_raw x) r,
    show raw7 y (toRows r)=den (col y) r from congrFun (proj_raw y) r]

theorem raw_gate_fresh (op : Kind) : ∀ x y : Fin 7, x≠y → (CoThetaFixedOrbit.rawGate x y op).value∉vertices7 := by
  exact fun x y xy => CoThetaFixedOrbit.head_fresh x y op xy

theorem reject_raw (r9 : RawNine) : ¬ CoThetaFixedOrbit.RawNine := by
  rintro ⟨h,ys,cost,reduced,goal⟩
  let raw0 := vertices7.map (restrict toRows)
  have zero : absentBit∈raw0 := List.mem_cons_self
  have endw := List.mem_map_of_mem (f:=restrict toRows) goal
  rw [numeric_target] at endw
  obtain ⟨m,S,le,live,sub⟩ := rewind (reduced.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
  have rep := CoThetaBits.root_rep live (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
    subst f
    rcases List.mem_cons.mp hw with z|l
    · subst w
      exact Or.inl rfl
    · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
      subst w
      exact Or.inr ⟨j,(proj_raw j).symm⟩)
  exact r9 live (by omega) rep

theorem numbered_start (i : Fin 13) : Free vertices7 1 ((numbered i).value::vertices7) :=
  .binary .start _ (raw_mem (casesA.getD i.val 0)) (raw_mem (casesB.getD i.val 0))

theorem orbit_cap : ∀ i : Fin 13, orbitPriority i≤13 := by decide +kernel

theorem prove_post (r9 : RawNine) (checks : ∀ i : Fin 13, i≠10 → ∀ j : Fin 448,
    permitPrefix (orbitPriority i) (numbers.getD i.val 0) j.val=true) : ∀ i, ¬CoThetaFixedOrbit.PostNine i := by
  have byrank : ∀ t : Nat, ∀ i : Fin 13, orbitPriority i=t → ¬CoThetaFixedOrbit.PostNine i := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro i key post
      obtain ⟨n,ws,small,run,out⟩ := post
      by_cases five : i=10
      · subst i
        exact reject_raw r9 (CoThetaCycleFive.no_post run small out)
      apply safe_after r9 (orbitPriority i) i (checks i five) run small out
      intro f hf v eq
      by_contra no
      have low : rankSignal (project v)<orbitPriority i := by omega
      obtain ⟨x,y,k,xy,word,earlier⟩ := rankSignal_sound _ (orbit_cap i) _ low
      have same : (CoThetaFixedOrbit.rawGate x y k).value=f := by
        apply reflect_rows
        rw [raw_gate_sample,project_inj word,eq]
      have whole := free_compose (numbered_start i) run
      obtain ⟨m,ys,cap,moved,sub⟩ := free_move whole hf (same ▸ raw_gate_fresh k x y xy)
      rw [←same] at moved
      have alt := CoThetaFixedOrbit.dispatch x y k xy moved (by omega) (sub _ out)
      by_cases bad : tag x y k<2
      · rw [if_pos bad] at alt
        exact reject_raw r9 alt
      · rw [if_neg bad] at alt
        have lt : orbitPriority (picked (tag x y k))<t := by simpa [priority,bad,key] using earlier
        exact ih _ lt _ rfl alt
  intro i
  exact byrank _ i rfl

theorem lower_from_ranked (r9 : RawNine) (checks : ∀ i : Fin 13, i≠10 → ∀ b : Fin 38,
    permitBlock (orbitPriority i) (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true)
    {n ws} (run : Free vertices7 n ws) (out : ans7∈ws) : 11≤n := by
  by_contra bad
  rcases select_program run (by omega) out with raw|⟨i,post⟩
  · exact reject_raw r9 raw
  · exact prove_post r9 (fun i ne => marked_blocks _ i (checks i ne)) i post

end CoThetaSeven

namespace CoThetaNine
open CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

def slice04 (r : Fin 128) : Input := row (CoPetersenThetaGeometry.plant 0 r.val)
def or04 : TraceGate Input := ⟨.disj,vtx 0,vtx 4⟩
def and03 : TraceGate Input := ⟨.conj,vtx 0,vtx 3⟩

def fixedHeadResult (gate : TraceGate Input) (gs : List (TraceGate Input)) : Prop :=
  (∃ n ys, n ≤ gs.length ∧ Free vertices n ys ∧ ans∈ys) ∨
  ∃ ts, ts.length≤gs.length ∧ sufficient vertices ans (gate::ts) ∧ 4 ≤ saved slice04 (gate::ts)

private theorem threeSet {gs : List (TraceGate Input)} {p q : Input→Bool}
    (h : ThreeReaders (fun g => reads g p ∨ reads g q) gs) :
    3 ≤ (readerSet gs p ∪ readerSet gs q).card := by
  classical
  obtain ⟨a,ha,b,hb,c,hc,ra,rb,rc,ab,ac,bc⟩ := h
  let S := readerSet gs p ∪ readerSet gs q
  have ins (g : TraceGate Input) (hg : g∈gs) (hr : reads g p ∨ reads g q) : g∈S := by
    rcases hr with r|r
    · exact Finset.mem_union_left _ (mem_readerSet.mpr ⟨hg,r⟩)
    · exact Finset.mem_union_right _ (mem_readerSet.mpr ⟨hg,r⟩)
  have sub : ({a,b,c} : Finset (TraceGate Input)) ⊆ S := by
    intro g hg
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl|rfl|rfl
    · exact ins _ ha ra
    · exact ins _ hb rb
    · exact ins _ hc rc
  have bound := Finset.card_le_card sub
  simpa [Finset.card_insert_of_notMem,ab,ac,bc,S] using bound

private theorem fixedHead04 {gate : TraceGate Input} (gs : List (TraceGate Input))
    {j : Fin 9} (different : (0 : Fin 9) ≠ j) (hp : reads gate (vtx 0))
    (hj : reads gate (vtx j)) (headZero : restrict slice04 gate.value = absentBit)
    (headDistinct : gate.value ≠ vtx 0 ∧ gate.value ≠ vtx 4)
    (correct : sufficient vertices ans (gate::gs)) : fixedHeadResult gate gs := by
  classical
  have init : sufficient (gate.value::vertices) ans gs := ⟨correct.1.2.2,correct.2⟩
  obtain ⟨ts,⟨reg,out⟩,fresh,le,_⟩ := simplify_trace gs init
  have well : registered vertices (gate::ts) := ⟨correct.1.1,correct.1.2.1,reg⟩
  have result : ans∈traceWires vertices (gate::ts) := out
  by_cases live : UsePath ts gate.value ans
  · have rz (i : Fin 9) : vtx i∈vertices :=
      List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have pz : restrict slice04 (vtx 0)=absentBit := by
      funext y
      exact (by decide +kernel : ∀ y : Fin 128, vtx 0 (slice04 y)=false) y
    have qz : restrict slice04 (vtx 4)=absentBit := by
      funext y
      exact (by decide +kernel : ∀ y : Fin 128, vtx 4 (slice04 y)=false) y
    have nz : restrict slice04 ans ≠ absentBit := by
      intro e
      exact (by decide : ans (slice04 5) ≠ false) (congrFun e (5 : Fin 128))
    have aliases (g : TraceGate Input) (hg : g∈ts) : g.value≠vtx 0 ∧ g.value≠vtx 4 := by
      have h := fresh_outputs fresh g hg
      exact ⟨fun e => h (List.mem_cons_of_mem _ (e ▸ rz 0)),
             fun e => h (List.mem_cons_of_mem _ (e ▸ rz 4))⟩
    obtain ⟨x,hx,rx,neq⟩ := another_raw_reader different (gate::ts) gate hp hj well result
    have three := three_for_pair 0 well result
      (Or.inl ⟨gate,List.mem_cons_self,x,hx,hp,rx,neq.symm⟩)
    obtain ⟨g,mem,hp',hq',van⟩ := extra_loss_on_path slice04 pz qz aliases live headZero headDistinct nz
    exact Or.inr ⟨ts,le,⟨well,result⟩,four_saved_raw_head slice04 _ _ _ pz qz (threeSet three)
       ⟨g,List.mem_cons_of_mem _ mem,hp',hq',van⟩⟩
  · obtain ⟨n,ws,hn,run,mem⟩ := omit_dead_head vertices ts gate.value ans reg out live
    exact Or.inl ⟨n,ws,hn.trans le,run,mem⟩

theorem fixed_or04 (gs : List (TraceGate Input)) (h : sufficient vertices ans (or04::gs)) :
    fixedHeadResult or04 gs := by
  apply fixedHead04 gs (j:=4) (by decide) (Or.inl rfl) (Or.inr rfl) _ _ h
  · funext y
    exact (by decide +kernel : ∀ y : Fin 128, or04.value (slice04 y)=false) y
  · exact ⟨fun e => (by decide : or04.value (row 16) ≠ vtx 0 (row 16)) (congrFun e (row 16)),
           fun e => (by decide : or04.value (row 1) ≠ vtx 4 (row 1)) (congrFun e (row 1))⟩

theorem fixed_and03 (gs : List (TraceGate Input)) (h : sufficient vertices ans (and03::gs)) :
    fixedHeadResult and03 gs := by
  apply fixedHead04 gs (j:=3) (by decide) (Or.inl rfl) (Or.inr rfl) _ _ h
  · funext y
    exact (by decide +kernel : ∀ y : Fin 128, and03.value (slice04 y)=false) y
  · exact ⟨fun e => (by decide : and03.value (row 1) ≠ vtx 0 (row 1)) (congrFun e (row 1)),
           fun e => (by decide : and03.value (row 16) ≠ vtx 4 (row 16)) (congrFun e (row 16))⟩

end CoThetaNine

namespace CoThetaNine
open CoThetaFreeCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fixed_head_lower (cert : SignedLower)
    {head : TraceGate Input} {gs : List (TraceGate Input)} (h : fixedHeadResult head gs) :
    14≤gs.length := by
  rcases h with ⟨n,zs,le,run,out⟩|⟨ts,le,solves,saves⟩
  · obtain ⟨s,len,reg,eq⟩ := trace_of_free run
    have h := any_nine_lower cert (gs:=s) ⟨reg,eq ▸ out⟩
    omega
  · have lower := residual_at_least_eleven cert 0 solves
    have total := accounted (sliceLift 0) (head::ts)
    change 4≤saved (sliceLift 0) (head::ts) at saves
    simp only [List.length_cons] at total
    omega

end CoThetaNine


namespace CoThetaFreeCore

variable {ρ : Type}

inductive PinForm where
  | constant (v : Bool)
  | copy (i : Nat)
  | inv (i : Nat)
  | binary (join : Bool) (i j : Nat)

def PinForm.value : PinForm → List (ρ→Bool) → (ρ→Bool)
  | .constant v, _ => fun _ => v
  | .copy i, w => w.getD i absentBit
  | .inv i, w => fun r => !(w.getD i absentBit r)
  | .binary join i j, w => fun r => base join (w.getD i absentBit r) (w.getD j absentBit r)

def PinForm.binaryCost : PinForm → Nat
  | .binary _ _ _ => 1
  | _ => 0

def cost : List PinForm → Nat
  | [] => 0
  | f::fs => f.binaryCost + cost fs

def execute : List PinForm → List (ρ→Bool) → List (ρ→Bool)
  | [], w => w
  | f::fs, w => execute fs (w ++ [f.value w])

private theorem read_registered (w pool : List (ρ→Bool)) (i : Nat) (hz : absentBit∈pool)
    (known : ∀ v∈w, v∈pool) : w.getD i absentBit∈pool := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact hz
  | some a => exact known a (List.mem_of_getElem? h)

private theorem pin_step (f : PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+f.binaryCost) ys ∧
      (∀ v∈pool, v∈ys) ∧ f.value w∈ys := by
  have reg := read_registered w pool
  have hz : absentBit∈pool := consts false
  cases f with
  | constant v => exact ⟨pool,pre,fun _ h => h,consts _⟩
  | copy i => exact ⟨pool,pre,fun _ h => h,reg i hz known⟩
  | inv i =>
    exact ⟨_, Ordinary.inv pre (reg i hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩
  | binary join i j =>
    exact ⟨_, Ordinary.binary pre join (reg i hz known) (reg j hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩

theorem pins_to_program (fs : List PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+cost fs) ys ∧ ∀ v∈execute fs w, v∈ys := by
  induction fs generalizing w pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons f fs ih =>
    obtain ⟨mid,hmid,old,hw⟩ := pin_step f w pool raw n pre consts known
    have available (v) (h : v∈w++[f.value w]) : v∈mid := by
      rcases List.mem_append.mp h with original | fresh
      · exact old _ (known _ original)
      · exact (congrArg (fun u => u∈mid) (List.mem_singleton.mp fresh)).mpr hw
    obtain ⟨ys,hy,sub⟩ := ih (w++[f.value w]) mid (n+f.binaryCost) hmid
      (fun b => old _ (consts b)) available
    exact ⟨ys,by simpa [cost,Nat.add_assoc] using hy,sub⟩

end CoThetaFreeCore

namespace CoThetaPhysical
open CoThetaFreeCore PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateForm (g : Gate) : PinForm :=
  match g.op, g.inputs with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .not, [] => .constant true
  | .and, [i] | .or, [i] => .copy i
  | .not, i::_ => .inv i
  | .and, i::j::_ => .binary false i j
  | .or, i::j::_ => .binary true i j
  | _, _ => .constant false

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem read_word {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    ((w.map (fun f => f r)).getD i false) = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem read_option {ρ : Type} (o : Option (ρ→Bool)) (r : ρ) :
    (o.map (fun f => f r)).getD false = o.getD absentBit r := by cases o <;> rfl

theorem form_agrees {ρ : Type} (g : Gate) (hg : legal g) (w : List (ρ→Bool)) (r : ρ) :
    (gateForm g).value w r =
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f r)).getD i false) := by
  obtain ⟨op,pins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not at hop
  change pins.length≤2 at hlen
  rcases hop with rfl | rfl | rfl <;>
    cases pins with
    | nil => rfl
    | cons i xs =>
      cases xs with
      | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
      | cons j t =>
        cases t with
        | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
        | cons h t => simp at hlen

theorem map_execute {ρ : Type} (gs : List Gate) (w : List (ρ→Bool)) (r : ρ)
    (hg : ∀ g∈gs, legal g) :
    (execute (gs.map gateForm) w).map (fun f => f r) =
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,execute,List.foldl_cons]
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp [form_agrees g (hg _ (by simp)) w r]

theorem circuit_rows {ρ : Type} (C : Circuit) (hf : FanInTwo C) (w : List (ρ→Bool)) (r : ρ) :
    (execute (C.gates.map gateForm) w).map (fun f => f r) = C.wires (w.map (fun f => f r)) :=
  map_execute C.gates w r hf

def boolCost (g : Gate) : Nat :=
  match g.op with
  | .and | .or => 1
  | _ => 0

theorem form_cost_le (g : Gate) : (gateForm g).binaryCost ≤ boolCost g := by
  obtain ⟨op,pins⟩ := g
  cases op <;> cases pins with
    | nil => simp [gateForm,boolCost,PinForm.binaryCost]
    | cons i t => cases t <;> simp [gateForm,boolCost,PinForm.binaryCost]

theorem cost_le_binary (gs : List Gate) :
    cost (gs.map gateForm) ≤ (gs.map boolCost).sum := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih =>
    simp only [List.map_cons,cost,List.sum_cons]
    exact Nat.add_le_add (form_cost_le g) ih

end CoThetaPhysical

namespace CoThetaFreeCore

theorem run_append {ρ : Type} (a b : List PinForm) (start : List (ρ→Bool)) :
    execute (a++b) start = execute b (execute a start) := by
  induction a generalizing start with
  | nil => rfl
  | cons f fs ih => exact ih _

theorem cost_append (a b : List PinForm) : cost (a++b)=cost a+cost b := by
  induction a with
  | nil => simp [cost]
  | cons x xs ih => simp [cost,ih,Nat.add_assoc]

theorem pin_cost_length (fs : List PinForm) : cost fs≤fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp only [cost,PinForm.binaryCost,List.length_cons] <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fan_of_mono (C : Circuit) (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,arity⟩ := h g hg
  refine ⟨?_,arity⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  exact op.elim Or.inl (fun e => Or.inr (Or.inl e))

def rawOrHead : TraceGate Input := ⟨.disj,vtx 0,vtx 4⟩
def prefixInputs : List (Input→Bool) := List.ofFn vtx ++ [rawOrHead.value]
def seed : List (Input→Bool) := absentBit::(fun _ => true)::prefixInputs

private theorem read_row_eq {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    (w.map (fun f => f r)).getD i false = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

theorem root_contains_norm : ∀ f∈seed.map (norm (row 0)), f∈rawOrHead.value::vertices := by
  intro f hf
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp hf
  subst f
  have hz : absentBit∈rawOrHead.value::vertices := List.mem_cons_of_mem _ List.mem_cons_self
  rcases List.mem_cons.mp ht with t0|ht
  · subst t
    exact hz
  rcases List.mem_cons.mp ht with t1|ht
  · subst t
    exact hz
  rcases List.mem_append.mp ht with hin|head
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp hin
    subst t
    have lo : ∀ j : Fin 9, vtx j (row 0)=false := by decide
    have eq : norm (row 0) (vtx i)=vtx i := by
      funext r
      simp [CoThetaFreeCore.norm,lo,phase]
    rw [eq]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · obtain rfl := List.mem_singleton.mp head
    have lo : rawOrHead.value (row 0)=false := by decide
    have eq : norm (row 0) rawOrHead.value=rawOrHead.value := by
      funext r
      simp [CoThetaFreeCore.norm,lo,phase]
    exact eq ▸ List.mem_cons_self

theorem segments_to_trace (P Q : Circuit) (pFan : FanInTwo P) (qFan : FanInTwo Q)
    (correct : ∀r : Input,
      let w := P.wires (List.ofFn (fun i => vtx i r) ++ [vtx 0 r || vtx 4 r])
      Q.eval (w++[!w.getD P.output false])=ans r) :
    ∃ gs, gs.length≤P.size+Q.size ∧ sufficient vertices ans (rawOrHead::gs) := by
  let p := P.gates.map gateForm
  let q := Q.gates.map gateForm
  let fs := p ++ (PinForm.inv P.output)::q
  let t := execute p prefixInputs
  let mid := t ++ [(PinForm.inv P.output).value t]
  have stages : execute fs prefixInputs=execute q mid := run_append p _ _
  have evalPrefix (r : Input) : prefixInputs.map (fun f => f r)=
      List.ofFn (fun i => vtx i r) ++ [vtx 0 r || vtx 4 r] := by
    simp [prefixInputs,List.map_ofFn,rawOrHead,TraceGate.value,applyKind]
  have evalMid (r : Input) :
      mid.map (fun f => f r)=
        let w := P.wires (List.ofFn (fun i => vtx i r) ++ [vtx 0 r || vtx 4 r])
        w++[!w.getD P.output false] := by
    have h := circuit_rows P pFan prefixInputs r
    have read := congrArg (fun ws : List Bool => ws.getD P.output false) h
    change (t.map (fun f => f r)).getD P.output false=_ at read
    rw [read_row_eq,evalPrefix] at read
    change t.map (fun f => f r)=_ at h
    rw [evalPrefix] at h
    simp only [mid,List.map_append,List.map_cons,List.map_nil,PinForm.value,h,read]
  let result := (execute fs prefixInputs).getD Q.output absentBit
  have correctWord : result=ans := by
    funext r
    have h := circuit_rows Q qFan mid r
    have read := congrArg (fun ws : List Bool => ws.getD Q.output false) h
    change ((execute q mid).map (fun f => f r)).getD Q.output false=_ at read
    rw [read_row_eq,evalMid] at read
    change (execute fs prefixInputs).getD Q.output absentBit r=_
    rw [stages]
    exact read.trans (correct r)
  have present : result∈execute fs prefixInputs := by
    cases e : (execute fs prefixInputs)[Q.output]? with
    | none =>
      have no : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (correctWord.symm.trans no)).elim
    | some w =>
      have eq : result=w := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v∈execute fs prefixInputs) eq).mpr (List.mem_of_getElem? e)
  have cs (b : Bool) : (fun _ : Input => b)∈seed := by
    cases b with
    | false => exact List.mem_cons_self
    | true => exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ys,program,cover⟩ := pins_to_program fs prefixInputs seed seed 0 Ordinary.start cs
    (fun w h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  obtain ⟨zs,free,sub⟩ := simulate_all_wires (row 0) program
  have hnorm : norm (row 0) ans=ans := by
    have lo : ans (row 0)=false := by decide
    funext r
    simp [CoThetaFreeCore.norm,lo,phase]
  have goalIn := sub result (cover _ present)
  rw [correctWord,hnorm] at goalIn
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have switch := trace_subset gs root_contains_norm
  have here : ans∈traceWires (rawOrHead.value::vertices) gs := switch.2 ans (eq ▸ goalIn)
  refine ⟨gs,?_,⟨⟨?_,?_,switch.1 reg⟩,here⟩⟩
  · have cp := pin_cost_length p
    have cq := pin_cost_length q
    simp only [fs,cost_append,cost,PinForm.binaryCost,Nat.zero_add] at len
    simp only [p,q,List.length_map,Circuit.size] at *
    omega
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨0,rfl⟩)
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨4,rfl⟩)

end CoThetaNine

namespace CoThetaFreeCore
variable {ρ σ : Type}

theorem realize_live (lift : σ→ρ) {goal : ρ→Bool} {k S} (live : Live goal k S)
    {raw pool : List (σ→Bool)} {n} (pre : Free raw n pool)
    (sub : ∀ w, S w → restrict lift w∈pool) :
    ∃ ys, Free raw (n+k) ys ∧ restrict lift goal∈ys := by
  induction live generalizing n pool with
  | stop => exact ⟨_,by simpa using pre,sub _ rfl⟩
  | @step k U a b op ab ha hb fresh tail ih =>
    let z : ρ→Bool := fun r => applyKind op (a r) (b r)
    have gate : Free raw (n+1) (restrict lift z::pool) :=
      Free.binary pre op (sub a (Or.inl rfl)) (sub b (Or.inr (Or.inl rfl)))
    obtain ⟨ys,run,read⟩ := ih gate (fun v hv => by
      rcases hv with e|mem
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sub v (Or.inr (Or.inr mem))))
    exact ⟨ys,(show n+1+k=n+(k+1) by omega) ▸ run,read⟩

end CoThetaFreeCore
namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaNine (SmallInput raw7 vertices7 ans7 pack unpack toRows numeric_target)
open CoThetaSix (minorLift minor_off)
open CoThetaBits (den Rep Wire col)
def SelectedEight : Prop := (∃ n ws, n≤8 ∧ Free vertices7 n ws ∧ ans7∈ws) ∨
  ∃ i : Fin 13, ∃ n ws, n≤8 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem dispatch_eight {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (size : (g::gs).length≤9) : SelectedEight := by
  classical
  obtain ⟨nL,nR,separate⟩ := fresh_ports g ok.1.1 ok.1.2.1 List.mem_cons_self fresh.1
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.1).resolve_left nL)
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.2.1).resolve_left nR)
  have xy : x≠y := fun e => separate (ex.symm.trans ((congrArg raw7 e).trans ey))
  have rx : reads g (raw7 x) := Or.inl ex.symm
  have ry : reads g (raw7 y) := Or.inr ey.symm
  let t := tag x y g.kind
  have rule := dispatch_rules g.kind x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  have n : gs.length≤8 := by simp only [List.length_cons] at size; omega
  by_cases a : t=0
  · rw [if_pos a] at rule
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind g.kind (g.left (minorLift x r)) (g.right (minorLift x r))=false
      rw [←ex,←ey]
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh (by omega) xy rx ry rule.1 drop
    exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind g.kind (g.left (minorLift y r)) (g.right (minorLift y r))=false
        rw [←ex,←ey]
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh (by omega) (Ne.symm xy) ry rx rule.1 drop
      exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
    · rw [if_neg b] at rule
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := by
        funext r
        change applyKind g.kind (g.left (rowPerm s r)) (g.right (rowPerm s r))=_
        rw [←ex,←ey]
        exact rule r
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨ws,run,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact Or.inr ⟨i,_,ws,by omega,run,goal⟩

theorem select_eight {n ws} (run : Free vertices7 n ws) (small : n≤9) (hit : ans7∈ws) :
    SelectedEight := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,solves,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  cases clean with
  | nil =>
    have h : ans7∈vertices7 := solves.2
    rcases List.mem_cons.mp h with z|r
    · have test : ans7 (smallRow 5)=true := by decide
      exact Bool.noConfusion (test.symm.trans (congrFun z (smallRow 5)))
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
      obtain ⟨s,d⟩ := seven_not_raw i
      exact (d (congrFun e.symm s)).elim
  | cons g gs => exact dispatch_eight solves fresh (by omega)


theorem raw_all_eight (checked : guardedSearch 8 rootWords=false) {n S}
    (live : Live (den CoThetaBits.target) n S) (cap : n≤8) (rep : Rep CoThetaBits.raw S) : False :=
  Bool.false_ne_true (checked.symm.trans (guarded_complete live 8 cap _ CoThetaBits.raw_nodup rep))

theorem raw_prog_eight (checked : guardedSearch 8 rootWords=false) {n ys}
    (cost : n≤8) (run : Free vertices7 n ys) (out : ans7∈ys) : False := by
  let raw0 := vertices7.map (restrict toRows)
  have zero : absentBit∈raw0 := List.mem_cons_self
  have endw := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at endw
  obtain ⟨m,S,le,live,sub⟩ := rewind (run.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
  have rep := CoThetaBits.root_rep live (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
    subst f
    rcases List.mem_cons.mp hw with z|l
    · subst w
      exact Or.inl rfl
    · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
      subst w
      exact Or.inr ⟨j,(proj_raw j).symm⟩)
  exact raw_all_eight checked live (by omega) rep

theorem raw_nine_short (zero : guardedSearch 8 rootWords=false)
    (numbers8 : ∀ i : Fin 13, guardedSearch 8 (firstWords (numbers.getD i.val 0))=false) : RawNine := by
  intro n S live le rep
  have undo (f : SmallInput→Bool) : restrict inverseRow (restrict toRows f)=f := by
    funext r
    exact congrArg f (sample_surjective r)
  obtain ⟨ys,run,out⟩ := realize_live inverseRow live (Free.start (raw:=vertices7)) (fun f hf => by
    obtain ⟨w,hw,eq⟩ := (rep f).1 hf
    obtain ⟨j,e⟩ := CoThetaBits.indexed hw
    subst w
    rw [←eq,←proj_raw,undo]
    exact raw_mem j)
  rw [←numeric_target,undo] at out
  rcases select_eight run (by omega) out with ⟨m,us,cap,p,hit⟩|⟨i,m,us,cap,p,hit⟩
  · exact raw_prog_eight zero cap p hit
  · let basis := ((numbered i).value::vertices7).map (restrict toRows)
    have base0 : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
    have goal := List.mem_map_of_mem (f:=restrict toRows) hit
    rw [numeric_target] at goal
    obtain ⟨k,T,cost,L,sub⟩ := rewind (p.map_rows toRows) base0 (Live.stop (goal:=den CoThetaBits.target))
      (fun w e => e.symm ▸ goal)
    rcases classify_pool i L (fun f hf => collect_init i (sub f hf)) with raw|extra
    · exact raw_all_eight zero L (by omega) raw
    · have no := guarded_complete L 8 (by omega) (postPool i) (post_data i).1 extra
      rw [(post_data i).2.1] at no
      exact Bool.false_ne_true ((numbers8 i).symm.trans no)

end CoThetaSeven

namespace CoThetaProofData
open CoNatBench CoThetaSeven
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8 : guardedSearch 8 rootWords=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_0 : guardedSearch 8 (firstWords 0)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_1 : guardedSearch 8 (firstWords 1)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_2 : guardedSearch 8 (firstWords 2)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_5 : guardedSearch 8 (firstWords 5)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_6 : guardedSearch 8 (firstWords 6)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_9 : guardedSearch 8 (firstWords 9)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_10 : guardedSearch 8 (firstWords 10)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_13 : guardedSearch 8 (firstWords 13)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_14 : guardedSearch 8 (firstWords 14)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_45 : guardedSearch 8 (firstWords 45)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_61 : guardedSearch 8 (firstWords 61)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_65 : guardedSearch 8 (firstWords 65)=false := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem r8_69 : guardedSearch 8 (firstWords 69)=false := by decide +kernel
theorem raw_shapes (i : Fin 13) : guardedSearch 8 (firstWords (numbers.getD i.val 0))=false := by
  fin_cases i
  · exact r8_0
  · exact r8_1
  · exact r8_2
  · exact r8_5
  · exact r8_6
  · exact r8_9
  · exact r8_10
  · exact r8_13
  · exact r8_14
  · exact r8_45
  · exact r8_61
  · exact r8_65
  · exact r8_69
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_0 : permitBlock 5 0 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_12 : permitBlock 5 0 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_24 : permitBlock 5 0 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_36 : permitBlock 5 0 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_48 : permitBlock 5 0 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_60 : permitBlock 5 0 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_72 : permitBlock 5 0 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_84 : permitBlock 5 0 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_96 : permitBlock 5 0 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_108 : permitBlock 5 0 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_120 : permitBlock 5 0 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_132 : permitBlock 5 0 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_144 : permitBlock 5 0 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_156 : permitBlock 5 0 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_168 : permitBlock 5 0 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_180 : permitBlock 5 0 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_192 : permitBlock 5 0 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_204 : permitBlock 5 0 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_216 : permitBlock 5 0 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_228 : permitBlock 5 0 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_240 : permitBlock 5 0 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_252 : permitBlock 5 0 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_264 : permitBlock 5 0 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_276 : permitBlock 5 0 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_288 : permitBlock 5 0 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_300 : permitBlock 5 0 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_312 : permitBlock 5 0 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_324 : permitBlock 5 0 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_336 : permitBlock 5 0 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_348 : permitBlock 5 0 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_360 : permitBlock 5 0 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_372 : permitBlock 5 0 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_384 : permitBlock 5 0 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_396 : permitBlock 5 0 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_408 : permitBlock 5 0 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_420 : permitBlock 5 0 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_432 : permitBlock 5 0 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b0_444 : permitBlock 5 0 444 4=true := by decide +kernel
theorem block0 (b : Fin 38) : permitBlock 5 0 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b0_0
  · exact b0_12
  · exact b0_24
  · exact b0_36
  · exact b0_48
  · exact b0_60
  · exact b0_72
  · exact b0_84
  · exact b0_96
  · exact b0_108
  · exact b0_120
  · exact b0_132
  · exact b0_144
  · exact b0_156
  · exact b0_168
  · exact b0_180
  · exact b0_192
  · exact b0_204
  · exact b0_216
  · exact b0_228
  · exact b0_240
  · exact b0_252
  · exact b0_264
  · exact b0_276
  · exact b0_288
  · exact b0_300
  · exact b0_312
  · exact b0_324
  · exact b0_336
  · exact b0_348
  · exact b0_360
  · exact b0_372
  · exact b0_384
  · exact b0_396
  · exact b0_408
  · exact b0_420
  · exact b0_432
  · exact b0_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_0 : permitBlock 12 1 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_12 : permitBlock 12 1 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_24 : permitBlock 12 1 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_36 : permitBlock 12 1 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_48 : permitBlock 12 1 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_60 : permitBlock 12 1 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_72 : permitBlock 12 1 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_84 : permitBlock 12 1 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_96 : permitBlock 12 1 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_108 : permitBlock 12 1 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_120 : permitBlock 12 1 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_132 : permitBlock 12 1 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_144 : permitBlock 12 1 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_156 : permitBlock 12 1 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_168 : permitBlock 12 1 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_180 : permitBlock 12 1 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_192 : permitBlock 12 1 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_204 : permitBlock 12 1 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_216 : permitBlock 12 1 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_228 : permitBlock 12 1 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_240 : permitBlock 12 1 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_252 : permitBlock 12 1 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_264 : permitBlock 12 1 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_276 : permitBlock 12 1 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_288 : permitBlock 12 1 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_300 : permitBlock 12 1 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_312 : permitBlock 12 1 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_324 : permitBlock 12 1 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_336 : permitBlock 12 1 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_348 : permitBlock 12 1 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_360 : permitBlock 12 1 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_372 : permitBlock 12 1 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_384 : permitBlock 12 1 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_396 : permitBlock 12 1 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_408 : permitBlock 12 1 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_420 : permitBlock 12 1 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_432 : permitBlock 12 1 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b1_444 : permitBlock 12 1 444 4=true := by decide +kernel
theorem block1 (b : Fin 38) : permitBlock 12 1 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b1_0
  · exact b1_12
  · exact b1_24
  · exact b1_36
  · exact b1_48
  · exact b1_60
  · exact b1_72
  · exact b1_84
  · exact b1_96
  · exact b1_108
  · exact b1_120
  · exact b1_132
  · exact b1_144
  · exact b1_156
  · exact b1_168
  · exact b1_180
  · exact b1_192
  · exact b1_204
  · exact b1_216
  · exact b1_228
  · exact b1_240
  · exact b1_252
  · exact b1_264
  · exact b1_276
  · exact b1_288
  · exact b1_300
  · exact b1_312
  · exact b1_324
  · exact b1_336
  · exact b1_348
  · exact b1_360
  · exact b1_372
  · exact b1_384
  · exact b1_396
  · exact b1_408
  · exact b1_420
  · exact b1_432
  · exact b1_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_0 : permitBlock 11 2 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_12 : permitBlock 11 2 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_24 : permitBlock 11 2 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_36 : permitBlock 11 2 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_48 : permitBlock 11 2 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_60 : permitBlock 11 2 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_72 : permitBlock 11 2 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_84 : permitBlock 11 2 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_96 : permitBlock 11 2 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_108 : permitBlock 11 2 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_120 : permitBlock 11 2 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_132 : permitBlock 11 2 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_144 : permitBlock 11 2 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_156 : permitBlock 11 2 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_168 : permitBlock 11 2 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_180 : permitBlock 11 2 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_192 : permitBlock 11 2 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_204 : permitBlock 11 2 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_216 : permitBlock 11 2 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_228 : permitBlock 11 2 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_240 : permitBlock 11 2 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_252 : permitBlock 11 2 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_264 : permitBlock 11 2 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_276 : permitBlock 11 2 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_288 : permitBlock 11 2 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_300 : permitBlock 11 2 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_312 : permitBlock 11 2 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_324 : permitBlock 11 2 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_336 : permitBlock 11 2 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_348 : permitBlock 11 2 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_360 : permitBlock 11 2 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_372 : permitBlock 11 2 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_384 : permitBlock 11 2 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_396 : permitBlock 11 2 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_408 : permitBlock 11 2 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_420 : permitBlock 11 2 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_432 : permitBlock 11 2 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b2_444 : permitBlock 11 2 444 4=true := by decide +kernel
theorem block2 (b : Fin 38) : permitBlock 11 2 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b2_0
  · exact b2_12
  · exact b2_24
  · exact b2_36
  · exact b2_48
  · exact b2_60
  · exact b2_72
  · exact b2_84
  · exact b2_96
  · exact b2_108
  · exact b2_120
  · exact b2_132
  · exact b2_144
  · exact b2_156
  · exact b2_168
  · exact b2_180
  · exact b2_192
  · exact b2_204
  · exact b2_216
  · exact b2_228
  · exact b2_240
  · exact b2_252
  · exact b2_264
  · exact b2_276
  · exact b2_288
  · exact b2_300
  · exact b2_312
  · exact b2_324
  · exact b2_336
  · exact b2_348
  · exact b2_360
  · exact b2_372
  · exact b2_384
  · exact b2_396
  · exact b2_408
  · exact b2_420
  · exact b2_432
  · exact b2_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_0 : permitBlock 1 5 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_12 : permitBlock 1 5 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_24 : permitBlock 1 5 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_36 : permitBlock 1 5 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_48 : permitBlock 1 5 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_60 : permitBlock 1 5 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_72 : permitBlock 1 5 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_84 : permitBlock 1 5 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_96 : permitBlock 1 5 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_108 : permitBlock 1 5 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_120 : permitBlock 1 5 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_132 : permitBlock 1 5 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_144 : permitBlock 1 5 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_156 : permitBlock 1 5 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_168 : permitBlock 1 5 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_180 : permitBlock 1 5 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_192 : permitBlock 1 5 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_204 : permitBlock 1 5 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_216 : permitBlock 1 5 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_228 : permitBlock 1 5 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_240 : permitBlock 1 5 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_252 : permitBlock 1 5 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_264 : permitBlock 1 5 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_276 : permitBlock 1 5 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_288 : permitBlock 1 5 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_300 : permitBlock 1 5 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_312 : permitBlock 1 5 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_324 : permitBlock 1 5 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_336 : permitBlock 1 5 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_348 : permitBlock 1 5 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_360 : permitBlock 1 5 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_372 : permitBlock 1 5 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_384 : permitBlock 1 5 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_396 : permitBlock 1 5 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_408 : permitBlock 1 5 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_420 : permitBlock 1 5 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_432 : permitBlock 1 5 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b5_444 : permitBlock 1 5 444 4=true := by decide +kernel
theorem block5 (b : Fin 38) : permitBlock 1 5 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b5_0
  · exact b5_12
  · exact b5_24
  · exact b5_36
  · exact b5_48
  · exact b5_60
  · exact b5_72
  · exact b5_84
  · exact b5_96
  · exact b5_108
  · exact b5_120
  · exact b5_132
  · exact b5_144
  · exact b5_156
  · exact b5_168
  · exact b5_180
  · exact b5_192
  · exact b5_204
  · exact b5_216
  · exact b5_228
  · exact b5_240
  · exact b5_252
  · exact b5_264
  · exact b5_276
  · exact b5_288
  · exact b5_300
  · exact b5_312
  · exact b5_324
  · exact b5_336
  · exact b5_348
  · exact b5_360
  · exact b5_372
  · exact b5_384
  · exact b5_396
  · exact b5_408
  · exact b5_420
  · exact b5_432
  · exact b5_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_0 : permitBlock 7 6 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_12 : permitBlock 7 6 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_24 : permitBlock 7 6 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_36 : permitBlock 7 6 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_48 : permitBlock 7 6 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_60 : permitBlock 7 6 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_72 : permitBlock 7 6 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_84 : permitBlock 7 6 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_96 : permitBlock 7 6 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_108 : permitBlock 7 6 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_120 : permitBlock 7 6 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_132 : permitBlock 7 6 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_144 : permitBlock 7 6 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_156 : permitBlock 7 6 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_168 : permitBlock 7 6 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_180 : permitBlock 7 6 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_192 : permitBlock 7 6 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_204 : permitBlock 7 6 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_216 : permitBlock 7 6 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_228 : permitBlock 7 6 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_240 : permitBlock 7 6 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_252 : permitBlock 7 6 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_264 : permitBlock 7 6 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_276 : permitBlock 7 6 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_288 : permitBlock 7 6 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_300 : permitBlock 7 6 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_312 : permitBlock 7 6 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_324 : permitBlock 7 6 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_336 : permitBlock 7 6 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_348 : permitBlock 7 6 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_360 : permitBlock 7 6 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_372 : permitBlock 7 6 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_384 : permitBlock 7 6 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_396 : permitBlock 7 6 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_408 : permitBlock 7 6 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_420 : permitBlock 7 6 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_432 : permitBlock 7 6 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b6_444 : permitBlock 7 6 444 4=true := by decide +kernel
theorem block6 (b : Fin 38) : permitBlock 7 6 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b6_0
  · exact b6_12
  · exact b6_24
  · exact b6_36
  · exact b6_48
  · exact b6_60
  · exact b6_72
  · exact b6_84
  · exact b6_96
  · exact b6_108
  · exact b6_120
  · exact b6_132
  · exact b6_144
  · exact b6_156
  · exact b6_168
  · exact b6_180
  · exact b6_192
  · exact b6_204
  · exact b6_216
  · exact b6_228
  · exact b6_240
  · exact b6_252
  · exact b6_264
  · exact b6_276
  · exact b6_288
  · exact b6_300
  · exact b6_312
  · exact b6_324
  · exact b6_336
  · exact b6_348
  · exact b6_360
  · exact b6_372
  · exact b6_384
  · exact b6_396
  · exact b6_408
  · exact b6_420
  · exact b6_432
  · exact b6_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_0 : permitBlock 4 9 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_12 : permitBlock 4 9 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_24 : permitBlock 4 9 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_36 : permitBlock 4 9 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_48 : permitBlock 4 9 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_60 : permitBlock 4 9 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_72 : permitBlock 4 9 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_84 : permitBlock 4 9 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_96 : permitBlock 4 9 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_108 : permitBlock 4 9 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_120 : permitBlock 4 9 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_132 : permitBlock 4 9 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_144 : permitBlock 4 9 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_156 : permitBlock 4 9 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_168 : permitBlock 4 9 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_180 : permitBlock 4 9 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_192 : permitBlock 4 9 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_204 : permitBlock 4 9 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_216 : permitBlock 4 9 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_228 : permitBlock 4 9 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_240 : permitBlock 4 9 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_252 : permitBlock 4 9 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_264 : permitBlock 4 9 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_276 : permitBlock 4 9 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_288 : permitBlock 4 9 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_300 : permitBlock 4 9 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_312 : permitBlock 4 9 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_324 : permitBlock 4 9 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_336 : permitBlock 4 9 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_348 : permitBlock 4 9 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_360 : permitBlock 4 9 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_372 : permitBlock 4 9 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_384 : permitBlock 4 9 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_396 : permitBlock 4 9 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_408 : permitBlock 4 9 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_420 : permitBlock 4 9 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_432 : permitBlock 4 9 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b9_444 : permitBlock 4 9 444 4=true := by decide +kernel
theorem block9 (b : Fin 38) : permitBlock 4 9 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b9_0
  · exact b9_12
  · exact b9_24
  · exact b9_36
  · exact b9_48
  · exact b9_60
  · exact b9_72
  · exact b9_84
  · exact b9_96
  · exact b9_108
  · exact b9_120
  · exact b9_132
  · exact b9_144
  · exact b9_156
  · exact b9_168
  · exact b9_180
  · exact b9_192
  · exact b9_204
  · exact b9_216
  · exact b9_228
  · exact b9_240
  · exact b9_252
  · exact b9_264
  · exact b9_276
  · exact b9_288
  · exact b9_300
  · exact b9_312
  · exact b9_324
  · exact b9_336
  · exact b9_348
  · exact b9_360
  · exact b9_372
  · exact b9_384
  · exact b9_396
  · exact b9_408
  · exact b9_420
  · exact b9_432
  · exact b9_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_0 : permitBlock 8 10 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_12 : permitBlock 8 10 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_24 : permitBlock 8 10 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_36 : permitBlock 8 10 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_48 : permitBlock 8 10 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_60 : permitBlock 8 10 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_72 : permitBlock 8 10 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_84 : permitBlock 8 10 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_96 : permitBlock 8 10 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_108 : permitBlock 8 10 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_120 : permitBlock 8 10 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_132 : permitBlock 8 10 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_144 : permitBlock 8 10 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_156 : permitBlock 8 10 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_168 : permitBlock 8 10 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_180 : permitBlock 8 10 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_192 : permitBlock 8 10 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_204 : permitBlock 8 10 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_216 : permitBlock 8 10 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_228 : permitBlock 8 10 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_240 : permitBlock 8 10 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_252 : permitBlock 8 10 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_264 : permitBlock 8 10 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_276 : permitBlock 8 10 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_288 : permitBlock 8 10 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_300 : permitBlock 8 10 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_312 : permitBlock 8 10 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_324 : permitBlock 8 10 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_336 : permitBlock 8 10 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_348 : permitBlock 8 10 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_360 : permitBlock 8 10 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_372 : permitBlock 8 10 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_384 : permitBlock 8 10 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_396 : permitBlock 8 10 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_408 : permitBlock 8 10 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_420 : permitBlock 8 10 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_432 : permitBlock 8 10 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b10_444 : permitBlock 8 10 444 4=true := by decide +kernel
theorem block10 (b : Fin 38) : permitBlock 8 10 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b10_0
  · exact b10_12
  · exact b10_24
  · exact b10_36
  · exact b10_48
  · exact b10_60
  · exact b10_72
  · exact b10_84
  · exact b10_96
  · exact b10_108
  · exact b10_120
  · exact b10_132
  · exact b10_144
  · exact b10_156
  · exact b10_168
  · exact b10_180
  · exact b10_192
  · exact b10_204
  · exact b10_216
  · exact b10_228
  · exact b10_240
  · exact b10_252
  · exact b10_264
  · exact b10_276
  · exact b10_288
  · exact b10_300
  · exact b10_312
  · exact b10_324
  · exact b10_336
  · exact b10_348
  · exact b10_360
  · exact b10_372
  · exact b10_384
  · exact b10_396
  · exact b10_408
  · exact b10_420
  · exact b10_432
  · exact b10_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_0 : permitBlock 13 13 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_12 : permitBlock 13 13 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_24 : permitBlock 13 13 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_36 : permitBlock 13 13 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_48 : permitBlock 13 13 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_60 : permitBlock 13 13 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_72 : permitBlock 13 13 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_84 : permitBlock 13 13 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_96 : permitBlock 13 13 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_108 : permitBlock 13 13 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_120 : permitBlock 13 13 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_132 : permitBlock 13 13 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_144 : permitBlock 13 13 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_156 : permitBlock 13 13 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_168 : permitBlock 13 13 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_180 : permitBlock 13 13 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_192 : permitBlock 13 13 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_204 : permitBlock 13 13 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_216 : permitBlock 13 13 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_228 : permitBlock 13 13 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_240 : permitBlock 13 13 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_252 : permitBlock 13 13 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_264 : permitBlock 13 13 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_276 : permitBlock 13 13 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_288 : permitBlock 13 13 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_300 : permitBlock 13 13 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_312 : permitBlock 13 13 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_324 : permitBlock 13 13 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_336 : permitBlock 13 13 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_348 : permitBlock 13 13 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_360 : permitBlock 13 13 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_372 : permitBlock 13 13 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_384 : permitBlock 13 13 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_396 : permitBlock 13 13 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_408 : permitBlock 13 13 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_420 : permitBlock 13 13 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_432 : permitBlock 13 13 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b13_444 : permitBlock 13 13 444 4=true := by decide +kernel
theorem block13 (b : Fin 38) : permitBlock 13 13 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b13_0
  · exact b13_12
  · exact b13_24
  · exact b13_36
  · exact b13_48
  · exact b13_60
  · exact b13_72
  · exact b13_84
  · exact b13_96
  · exact b13_108
  · exact b13_120
  · exact b13_132
  · exact b13_144
  · exact b13_156
  · exact b13_168
  · exact b13_180
  · exact b13_192
  · exact b13_204
  · exact b13_216
  · exact b13_228
  · exact b13_240
  · exact b13_252
  · exact b13_264
  · exact b13_276
  · exact b13_288
  · exact b13_300
  · exact b13_312
  · exact b13_324
  · exact b13_336
  · exact b13_348
  · exact b13_360
  · exact b13_372
  · exact b13_384
  · exact b13_396
  · exact b13_408
  · exact b13_420
  · exact b13_432
  · exact b13_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_0 : permitBlock 6 14 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_12 : permitBlock 6 14 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_24 : permitBlock 6 14 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_36 : permitBlock 6 14 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_48 : permitBlock 6 14 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_60 : permitBlock 6 14 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_72 : permitBlock 6 14 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_84 : permitBlock 6 14 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_96 : permitBlock 6 14 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_108 : permitBlock 6 14 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_120 : permitBlock 6 14 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_132 : permitBlock 6 14 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_144 : permitBlock 6 14 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_156 : permitBlock 6 14 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_168 : permitBlock 6 14 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_180 : permitBlock 6 14 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_192 : permitBlock 6 14 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_204 : permitBlock 6 14 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_216 : permitBlock 6 14 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_228 : permitBlock 6 14 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_240 : permitBlock 6 14 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_252 : permitBlock 6 14 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_264 : permitBlock 6 14 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_276 : permitBlock 6 14 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_288 : permitBlock 6 14 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_300 : permitBlock 6 14 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_312 : permitBlock 6 14 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_324 : permitBlock 6 14 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_336 : permitBlock 6 14 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_348 : permitBlock 6 14 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_360 : permitBlock 6 14 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_372 : permitBlock 6 14 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_384 : permitBlock 6 14 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_396 : permitBlock 6 14 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_408 : permitBlock 6 14 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_420 : permitBlock 6 14 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_432 : permitBlock 6 14 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b14_444 : permitBlock 6 14 444 4=true := by decide +kernel
theorem block14 (b : Fin 38) : permitBlock 6 14 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b14_0
  · exact b14_12
  · exact b14_24
  · exact b14_36
  · exact b14_48
  · exact b14_60
  · exact b14_72
  · exact b14_84
  · exact b14_96
  · exact b14_108
  · exact b14_120
  · exact b14_132
  · exact b14_144
  · exact b14_156
  · exact b14_168
  · exact b14_180
  · exact b14_192
  · exact b14_204
  · exact b14_216
  · exact b14_228
  · exact b14_240
  · exact b14_252
  · exact b14_264
  · exact b14_276
  · exact b14_288
  · exact b14_300
  · exact b14_312
  · exact b14_324
  · exact b14_336
  · exact b14_348
  · exact b14_360
  · exact b14_372
  · exact b14_384
  · exact b14_396
  · exact b14_408
  · exact b14_420
  · exact b14_432
  · exact b14_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_0 : permitBlock 10 45 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_12 : permitBlock 10 45 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_24 : permitBlock 10 45 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_36 : permitBlock 10 45 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_48 : permitBlock 10 45 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_60 : permitBlock 10 45 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_72 : permitBlock 10 45 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_84 : permitBlock 10 45 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_96 : permitBlock 10 45 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_108 : permitBlock 10 45 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_120 : permitBlock 10 45 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_132 : permitBlock 10 45 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_144 : permitBlock 10 45 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_156 : permitBlock 10 45 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_168 : permitBlock 10 45 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_180 : permitBlock 10 45 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_192 : permitBlock 10 45 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_204 : permitBlock 10 45 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_216 : permitBlock 10 45 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_228 : permitBlock 10 45 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_240 : permitBlock 10 45 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_252 : permitBlock 10 45 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_264 : permitBlock 10 45 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_276 : permitBlock 10 45 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_288 : permitBlock 10 45 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_300 : permitBlock 10 45 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_312 : permitBlock 10 45 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_324 : permitBlock 10 45 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_336 : permitBlock 10 45 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_348 : permitBlock 10 45 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_360 : permitBlock 10 45 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_372 : permitBlock 10 45 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_384 : permitBlock 10 45 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_396 : permitBlock 10 45 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_408 : permitBlock 10 45 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_420 : permitBlock 10 45 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_432 : permitBlock 10 45 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b45_444 : permitBlock 10 45 444 4=true := by decide +kernel
theorem block45 (b : Fin 38) : permitBlock 10 45 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b45_0
  · exact b45_12
  · exact b45_24
  · exact b45_36
  · exact b45_48
  · exact b45_60
  · exact b45_72
  · exact b45_84
  · exact b45_96
  · exact b45_108
  · exact b45_120
  · exact b45_132
  · exact b45_144
  · exact b45_156
  · exact b45_168
  · exact b45_180
  · exact b45_192
  · exact b45_204
  · exact b45_216
  · exact b45_228
  · exact b45_240
  · exact b45_252
  · exact b45_264
  · exact b45_276
  · exact b45_288
  · exact b45_300
  · exact b45_312
  · exact b45_324
  · exact b45_336
  · exact b45_348
  · exact b45_360
  · exact b45_372
  · exact b45_384
  · exact b45_396
  · exact b45_408
  · exact b45_420
  · exact b45_432
  · exact b45_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_0 : permitBlock 9 65 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_12 : permitBlock 9 65 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_24 : permitBlock 9 65 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_36 : permitBlock 9 65 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_48 : permitBlock 9 65 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_60 : permitBlock 9 65 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_72 : permitBlock 9 65 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_84 : permitBlock 9 65 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_96 : permitBlock 9 65 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_108 : permitBlock 9 65 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_120 : permitBlock 9 65 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_132 : permitBlock 9 65 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_144 : permitBlock 9 65 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_156 : permitBlock 9 65 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_168 : permitBlock 9 65 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_180 : permitBlock 9 65 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_192 : permitBlock 9 65 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_204 : permitBlock 9 65 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_216 : permitBlock 9 65 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_228 : permitBlock 9 65 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_240 : permitBlock 9 65 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_252 : permitBlock 9 65 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_264 : permitBlock 9 65 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_276 : permitBlock 9 65 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_288 : permitBlock 9 65 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_300 : permitBlock 9 65 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_312 : permitBlock 9 65 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_324 : permitBlock 9 65 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_336 : permitBlock 9 65 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_348 : permitBlock 9 65 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_360 : permitBlock 9 65 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_372 : permitBlock 9 65 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_384 : permitBlock 9 65 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_396 : permitBlock 9 65 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_408 : permitBlock 9 65 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_420 : permitBlock 9 65 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_432 : permitBlock 9 65 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b65_444 : permitBlock 9 65 444 4=true := by decide +kernel
theorem block65 (b : Fin 38) : permitBlock 9 65 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b65_0
  · exact b65_12
  · exact b65_24
  · exact b65_36
  · exact b65_48
  · exact b65_60
  · exact b65_72
  · exact b65_84
  · exact b65_96
  · exact b65_108
  · exact b65_120
  · exact b65_132
  · exact b65_144
  · exact b65_156
  · exact b65_168
  · exact b65_180
  · exact b65_192
  · exact b65_204
  · exact b65_216
  · exact b65_228
  · exact b65_240
  · exact b65_252
  · exact b65_264
  · exact b65_276
  · exact b65_288
  · exact b65_300
  · exact b65_312
  · exact b65_324
  · exact b65_336
  · exact b65_348
  · exact b65_360
  · exact b65_372
  · exact b65_384
  · exact b65_396
  · exact b65_408
  · exact b65_420
  · exact b65_432
  · exact b65_444
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_0 : permitBlock 3 69 0 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_12 : permitBlock 3 69 12 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_24 : permitBlock 3 69 24 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_36 : permitBlock 3 69 36 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_48 : permitBlock 3 69 48 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_60 : permitBlock 3 69 60 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_72 : permitBlock 3 69 72 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_84 : permitBlock 3 69 84 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_96 : permitBlock 3 69 96 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_108 : permitBlock 3 69 108 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_120 : permitBlock 3 69 120 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_132 : permitBlock 3 69 132 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_144 : permitBlock 3 69 144 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_156 : permitBlock 3 69 156 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_168 : permitBlock 3 69 168 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_180 : permitBlock 3 69 180 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_192 : permitBlock 3 69 192 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_204 : permitBlock 3 69 204 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_216 : permitBlock 3 69 216 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_228 : permitBlock 3 69 228 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_240 : permitBlock 3 69 240 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_252 : permitBlock 3 69 252 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_264 : permitBlock 3 69 264 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_276 : permitBlock 3 69 276 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_288 : permitBlock 3 69 288 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_300 : permitBlock 3 69 300 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_312 : permitBlock 3 69 312 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_324 : permitBlock 3 69 324 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_336 : permitBlock 3 69 336 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_348 : permitBlock 3 69 348 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_360 : permitBlock 3 69 360 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_372 : permitBlock 3 69 372 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_384 : permitBlock 3 69 384 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_396 : permitBlock 3 69 396 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_408 : permitBlock 3 69 408 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_420 : permitBlock 3 69 420 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_432 : permitBlock 3 69 432 12=true := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem b69_444 : permitBlock 3 69 444 4=true := by decide +kernel
theorem block69 (b : Fin 38) : permitBlock 3 69 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b
  · exact b69_0
  · exact b69_12
  · exact b69_24
  · exact b69_36
  · exact b69_48
  · exact b69_60
  · exact b69_72
  · exact b69_84
  · exact b69_96
  · exact b69_108
  · exact b69_120
  · exact b69_132
  · exact b69_144
  · exact b69_156
  · exact b69_168
  · exact b69_180
  · exact b69_192
  · exact b69_204
  · exact b69_216
  · exact b69_228
  · exact b69_240
  · exact b69_252
  · exact b69_264
  · exact b69_276
  · exact b69_288
  · exact b69_300
  · exact b69_312
  · exact b69_324
  · exact b69_336
  · exact b69_348
  · exact b69_360
  · exact b69_372
  · exact b69_384
  · exact b69_396
  · exact b69_408
  · exact b69_420
  · exact b69_432
  · exact b69_444
theorem all_blocks (i : Fin 13) (ne : i≠10) (b : Fin 38) : permitBlock (orbitPriority i) (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases i
  · exact block0 b
  · exact block1 b
  · exact block2 b
  · exact block5 b
  · exact block6 b
  · exact block9 b
  · exact block10 b
  · exact block13 b
  · exact block14 b
  · exact block45 b
  · exact (ne rfl).elim
  · exact block65 b
  · exact block69 b
end CoThetaProofData

namespace CoThetaSeven

theorem checked_lower : CoThetaNine.SignedLower :=
  fun run out => lower_from_ranked (raw_nine_short CoThetaProofData.r8 CoThetaProofData.raw_shapes) CoThetaProofData.all_blocks run out

end CoThetaSeven
namespace CoSwitch3302

open CoThetaNine CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def raw : List (Input→Bool) := List.ofFn vtx
def bank := absentBit::(fun _ : Input => true)::raw

private theorem vertexNorm (i : Fin 9) : norm (row 0) (vtx i)∈vertices := by
  have z : ∀ j : Fin 9, vtx j (row 0)=false := by decide
  have eq : norm (row 0) (vtx i)=vtx i := by
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  rw [eq]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

private theorem knownBank : ∀ w∈bank.map (norm (row 0)), w∈vertices := by
  intro w hw
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_self
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_self
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact vertexNorm i

private theorem rows_read (w : List (Input→Bool)) (j : Nat) (r : Input) :
    (w.map (fun f => f r)).getD j false = w.getD j absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> rfl

def f8 : (Fin 8 → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))

theorem cost_with_not (gs : List Gate) (hasNOT : ∃ g∈gs, g.op = GateOp.not) :
    cost (gs.map gateForm) + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at hasNOT
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := hasNOT
    have rest := pin_cost_length (gs.map gateForm)
    simp only [List.length_map] at rest
    have small := form_cost_le g
    rcases List.mem_cons.mp hu with rfl|inside
    · rw [boolCost,op] at small
      change (gateForm u).binaryCost ≤ 0 at small
      simp only [List.map_cons,cost,List.length_cons]
      omega
    · have h := ih ⟨u,inside,op⟩
      have one : boolCost g≤1 := by cases e : g.op <;> simp [boolCost,e]
      simp only [List.map_cons,cost,List.length_cons]
      omega

def projectIndex : Fin 8 → Fin 9 := ![0,1,2,3,5,6,7,8]
def small (r : Input) (i : Fin 8) := vtx (projectIndex i) r
def wires8 : List (Input→Bool) := List.ofFn (fun i r => small r i)

private theorem reconstruct : ∀ r : Input,
    (if vtx 4 r then (f8 (small r) || small r 0 || small r 3) else f8 (small r))=ans r := by
  decide +kernel

private theorem base_survives {n : Nat} {ys : List (Input→Bool)}
    (p : Ordinary bank n ys) : ∀ v∈bank, v∈ys := by
  induction p with
  | start => exact fun _ h => h
  | inv _ _ ih => exact fun v h => List.mem_cons_of_mem _ (ih v h)
  | binary _ _ _ _ ih => exact fun v h => List.mem_cons_of_mem _ (ih v h)

private theorem raw_mem_bank (i : Fin 9) : vtx i ∈ bank :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem switch_cost (lower : SignedLower) (P Q : Circuit) (idx : Nat)
    (pf : FanInTwo P) (qf : FanInTwo Q) (neg : ∃ g∈Q.gates, g.op=GateOp.not)
    (keep : ∀ x, let w := P.wires (List.ofFn x); Q.eval (w++[w.getD idx false])=f8 x)
    (clear : ∀ x, Q.eval (P.wires (List.ofFn x)++[false])=(f8 x || x 0 || x 3)) :
    14≤P.size+Q.size := by
  let ps := P.gates.map gateForm
  let qs := Q.gates.map gateForm
  let t := execute ps wires8
  let val := t.getD idx absentBit
  let nz : Input→Bool := fun r => !(vtx 4 r)
  let extra : Input→Bool := fun r => base false (val r) (nz r)
  let mid := t++[extra]
  let result := (execute qs mid).getD Q.output absentBit
  have preRows (r : Input) : t.map (fun f => f r)=P.wires (List.ofFn (small r)) := by
    simpa [t,ps,wires8,List.map_ofFn] using circuit_rows P pf wires8 r
  have word : result=ans := by
    funext r
    have read := congrArg (fun ws : List Bool => ws.getD idx false) (preRows r)
    rw [rows_read] at read
    have ev := congrArg (fun ws : List Bool => ws.getD Q.output false) (circuit_rows Q qf mid r)
    change ((execute qs mid).map (fun f => f r)).getD Q.output false = _ at ev
    rw [rows_read] at ev
    change (execute qs mid).getD Q.output absentBit r=_
    rw [ev,←reconstruct r]
    change Q.eval (mid.map (fun f => f r))=_
    simp only [mid,List.map_append,List.map_cons,List.map_nil,preRows,extra,nz,val,base,read]
    cases hz : vtx 4 r
    · simpa using keep (small r)
    · simpa using clear (small r)
  have cs (b : Bool) : (fun _ : Input => b)∈bank := by
    cases b with
    | false => exact List.mem_cons_self
    | true => exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨ys,pr,hcov⟩ := pins_to_program ps wires8 bank bank 0 Ordinary.start cs (by
    intro w h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact raw_mem_bank (projectIndex i))
  have banked := base_survives pr
  have vv : val∈ys := by
    cases ee : t[idx]? with
    | none =>
      have v0 : val=absentBit := by simp [val,List.getD_eq_getElem?_getD,ee]
      rw [v0]
      exact banked _ (cs false)
    | some w =>
      have vw : val=w := by simp [val,List.getD_eq_getElem?_getD,ee]
      rw [vw]
      exact hcov _ (List.mem_of_getElem? ee)
  have i1 : Ordinary bank (0+cost ps) (nz::ys) := Ordinary.inv pr (banked _ (raw_mem_bank 4))
  have i2 : Ordinary bank ((0+cost ps)+1) (extra::nz::ys) :=
    Ordinary.binary i1 false (List.mem_cons_of_mem _ vv) List.mem_cons_self
  obtain ⟨zs,pg,cov⟩ := pins_to_program qs mid (extra::nz::ys) bank _ i2
    (fun b => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (banked _ (cs b)))) (by
      intro w h
      rcases List.mem_append.mp h with old|new
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hcov _ old))
      · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp new)))
  have mem : result∈zs := by
    cases ee : (execute qs mid)[Q.output]? with
    | none =>
      have e : result=absentBit := by simp [result,List.getD_eq_getElem?_getD,ee]
      exact (ans_not_zero (word.symm.trans e)).elim
    | some w =>
      have e : result=w := by simp [result,List.getD_eq_getElem?_getD,ee]
      rw [e]
      exact cov _ (List.mem_of_getElem? ee)
  obtain ⟨vs,free,hits⟩ := simulate_all_wires (row 0) pg
  have ng : norm (row 0) ans=ans := by
    have z : ans (row 0)=false := by decide
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  have hit := hits _ mem
  rw [word,ng] at hit
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have use := trace_subset gs knownBank
  have bound := any_nine_lower lower (show sufficient vertices ans gs from ⟨use.1 reg,use.2 _ (eq ▸ hit)⟩)
  have hq := cost_with_not Q.gates neg
  have hp := pin_cost_length ps
  change cost qs + 1 ≤ Q.gates.length at hq
  have lp : ps.length=P.gates.length := by simp [ps]
  change 14≤P.gates.length+Q.gates.length
  omega

end CoSwitch3302
-- The circuit monotonicity lemmas are from the checked L-meta-1572 (using L-meta-1353).
namespace CoSwitch3302.MonotoneWires3302
open PEqualNP.CircuitLowerBounds
-- The wire evaluation lemmas follow L-meta-1353.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

abbrev AO (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma wires_mono {n : ℕ} (C : Circuit) (hAO : AO C) (x y : Fin n → Bool)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases h : w < n + C.size
    · let k := w - n
      have hk : k < C.gates.length := by dsimp [k]; unfold Circuit.size at h; omega
      have hwk : w = n + k := by dsimp [k]; omega
      rw [hwk]
      refine gate_mono C k hk (hAO _ (List.getElem_mem hk)).1 x y ?_
      intro r _ hr
      exact ih r (by omega)
    · rw [missing_value C x w (by omega)]
      simp


end CoSwitch3302.MonotoneWires3302
namespace CoSwitch3302
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open MonotoneWires3302

private theorem last_mono (Q : Circuit) (ao : AO Q) (ws : List Bool) (b : Bool) :
    Q.eval (ws ++ [false]) = true → Q.eval (ws ++ [b]) = true := by
  have snocList (z : Bool) : List.ofFn (Fin.snoc ws.get z) = ws ++ [z] := by
    rw [List.ofFn_succ']
    simp [Fin.snoc]
  have h : ∀ i, (Fin.snoc ws.get false : Fin (ws.length+1) → Bool) i = true →
      (Fin.snoc ws.get b : Fin (ws.length+1) → Bool) i = true := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      simp
    · simp only [Fin.snoc_castSucc]
      exact id
  have m := wires_mono Q ao (Fin.snoc ws.get false) (Fin.snoc ws.get b) h Q.output
  change Q.eval (List.ofFn (Fin.snoc ws.get false)) = true → Q.eval (List.ofFn (Fin.snoc ws.get b)) = true at m
  simpa only [snocList] using m

theorem switch_not (P Q : Circuit) (idx : Nat) (fan : FanInTwo Q)
    (actual : ∀ x : Fin 8 → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [(P.wires (List.ofFn x)).getD idx false]) = f8 x)
    (zeroed : ∀ x : Fin 8 → Bool,
      Q.eval (P.wires (List.ofFn x) ++ [false]) = (f8 x || x 0 || x 3)) :
    ∃ g ∈ Q.gates, g.op = .not := by
  by_contra no
  have mono : AO Q := by
    intro g hg
    have h := (fan g hg).1
    have hn : g.op ≠ .not := fun e => no ⟨g,hg,e⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    exact ⟨h.elim Or.inl (fun h => Or.inr (h.resolve_right hn)),(fan g hg).2⟩
  let x : Fin 8 → Bool := fun i => decide (i=0)
  have noEdge : f8 x = false := by decide +kernel
  have one : Q.eval (P.wires (List.ofFn x) ++ [false]) = true := by
    rw [zeroed,noEdge]
    decide
  have high := last_mono Q mono _ ((P.wires (List.ofFn x)).getD idx false) one
  rw [actual,noEdge] at high
  exact Bool.false_ne_true high
end CoSwitch3302

end PEqualNP.Outside.L_meta_5048_aux

open PEqualNP.Outside.L_meta_5048_aux

namespace PEqualNP.Outside.L_meta_5048_aux

theorem bound : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  classical
  dsimp only
  intro P Q idx pf qf _ budget _ _ _ keep
  apply Classical.byContradiction
  intro bad
  have clear : ∀ x, Q.eval (P.wires (List.ofFn x)++[false])=(CoSwitch3302.f8 x || x 0 || x 3) := by
    intro x
    exact Classical.not_not.mp (fun ne => bad ⟨x,ne⟩)
  have neg := CoSwitch3302.switch_not P Q idx qf keep clear
  have high := CoSwitch3302.switch_cost CoThetaSeven.checked_lower P Q idx pf qf neg keep clear
  omega

end PEqualNP.Outside.L_meta_5048_aux

theorem PEqualNP.Outside.L_meta_5048 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (4 : ℕ) ≤ x2.size →             have x9 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9);             have x10 : (Fin (8 : ℕ) → Bool) → Bool := fun (x10 : Fin (8 : ℕ) → Bool) => (x9 x10).getD (11 : ℕ) Bool.false;             (∀ (x11 : Fin (8 : ℕ) → Bool), x1 x11 = Bool.false → (x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) = Bool.true → x10 x11 = Bool.true) → (∀ (x12 : Fin (8 : ℕ) → Bool), x3.eval (x9 x12 ++ [x10 x12]) = x1 x12) → ∃ (x13 : Fin (8 : ℕ) → Bool), x3.eval (x9 x13 ++ [Bool.false]) ≠ (x1 x13 || x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro P Q pfan qfan small budget last pin eval
  exact PEqualNP.Outside.L_meta_5048_aux.bound P Q 11 pfan qfan small budget (by decide) (by omega) pin eval
