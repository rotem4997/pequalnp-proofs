import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_540_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover Finset
open Relation (ReflTransGen)
open Function (update)
lemma subRel_ne_hubs {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 1<=k)
 {x y : Fin (PEqualNP.Library.Subdivision.nS m k)}
 (h : PEqualNP.Library.Subdivision.SubRel k H x y) :
 m<=x.val\/m<=y.val:=by
 obtain ⟨u,v,_,_,p,hx,hy⟩:=h
 by_cases hp0 : p.val=0
 . right
   rw [hy,if_neg (by omega)]
   omega
 . left
   rw [hx,if_neg hp0]
   omega
lemma subRel_unique_slot {m k : ℕ} (hk : 1<=k) {u1 v1 u2 v2 : Fin m}
 {i1 i2 : ℕ} (hi1 : i1 < 2 * k) (hi2 : i2 < 2 * k)
 (heq : m+2 * k * (u1.val * m+v1.val)+i1 =
  m+2 * k * (u2.val * m+v2.val)+i2) :
 u1=u2/\v1=v2/\i1=i2:=by
 have h1 : 2 * k * (u1.val * m+v1.val)+i1=2 * k * (u2.val * m+v2.val)+i2:=by omega
 have hdiv : u1.val * m+v1.val=u2.val * m+v2.val:=by
  have ha:=congrArg (· / (2 * k)) h1
  have hpos : 0 < 2 * k:=by omega
  rw [Nat.mul_add_div hpos,Nat.mul_add_div hpos,Nat.div_eq_of_lt hi1,Nat.div_eq_of_lt hi2] at ha
  omega
 have hi : i1=i2:=by rw [hdiv] at h1;omega
 have hm : 0 < m:=Nat.pos_of_ne_zero (by intro hm0;exact Fin.elim0 (hm0 ▸ u1))
 have hu : u1.val=u2.val:=by
  have ha:=congrArg (· / m) hdiv
  rw [Nat.mul_comm u1.val m,Nat.mul_comm u2.val m,Nat.mul_add_div hm,Nat.mul_add_div hm,
   Nat.div_eq_of_lt v1.isLt,Nat.div_eq_of_lt v2.isLt] at ha
  omega
 have hv : v1.val=v2.val:=by rw [hu] at hdiv;omega
 exact ⟨Fin.ext hu,Fin.ext hv,hi⟩
lemma subdiv_adj_iff {m k : ℕ} {H : SimpleGraph (Fin m)}
 {x y : Fin (PEqualNP.Library.Subdivision.nS m k)} :
 (PEqualNP.Library.Subdivision.subdiv k H).Adj x y ↔
  x≠y/\(PEqualNP.Library.Subdivision.SubRel k H x y ∨
   PEqualNP.Library.Subdivision.SubRel k H y x):=by
 simp [PEqualNP.Library.Subdivision.subdiv,SimpleGraph.fromRel_adj]
lemma subRel_neighbors {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 2<=k)
 {x y : Fin (PEqualNP.Library.Subdivision.nS m k)}
 (h : PEqualNP.Library.Subdivision.SubRel k H x y) :
 (x.val < m/\∃ u v : Fin m,u < v/\H.Adj u v/\x.val=u.val ∧
  y.val=m+2 * k * (u.val * m+v.val)) ∨
 (y.val < m/\∃ u v : Fin m,u < v/\H.Adj u v/\y.val=v.val ∧
  x.val=m+2 * k * (u.val * m+v.val)+(2 * k - 1)) ∨
 (∃ u v : Fin m,∃ i : ℕ,u < v/\H.Adj u v/\i+1 < 2 * k ∧
  x.val=m+2 * k * (u.val * m+v.val)+i ∧
  y.val=m+2 * k * (u.val * m+v.val)+(i+1)):=by
 obtain ⟨u,v,huv,hadj,p,hx,hy⟩:=h
 by_cases hp0 : p.val=0
 . left
   refine ⟨by rw [hx,if_pos hp0];exact u.isLt,u,v,huv,hadj,?_,?_⟩
   . rw [hx,if_pos hp0]
   . rw [hy,if_neg (by omega),hp0,add_zero]
 . by_cases hpe : p.val=2 * k
   . right;left
     refine ⟨by rw [hy,if_pos hpe];exact v.isLt,u,v,huv,hadj,?_,?_⟩
     . rw [hy,if_pos hpe]
     . rw [hx,if_neg hp0,hpe];omega
   . right;right
     refine ⟨u,v,p.val - 1,huv,hadj,by omega,?_,?_⟩
     . rw [hx,if_neg hp0];omega
     . rw [hy,if_neg hpe];omega
lemma sdTF {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 2<=k)
 (a b c : Fin (PEqualNP.Library.Subdivision.nS m k))
 (hab : (PEqualNP.Library.Subdivision.subdiv k H).Adj a b)
 (hbc : (PEqualNP.Library.Subdivision.subdiv k H).Adj b c)
 (hac : (PEqualNP.Library.Subdivision.subdiv k H).Adj a c) : False:=by
 have h1:=(subdiv_adj_iff.mp hab).2
 have h2:=(subdiv_adj_iff.mp hbc).2
 have h3:=(subdiv_adj_iff.mp hac).2
 have hne_ab:=hab.ne
 have hne_bc:=hbc.ne
 have hne_ac:=hac.ne
 have hstep : ∀ x y : Fin (PEqualNP.Library.Subdivision.nS m k),
  (PEqualNP.Library.Subdivision.SubRel k H x y\/PEqualNP.Library.Subdivision.SubRel k H y x) →
  (x.val < m/\∃ u v : Fin m,∃ i : ℕ,u < v/\H.Adj u v ∧
   ((x.val=u.val/\i=0)\/(x.val=v.val/\i=2 * k - 1)) ∧
   y.val=m+2 * k * (u.val * m+v.val)+i) ∨
  (y.val < m/\∃ u v : Fin m,∃ i : ℕ,u < v/\H.Adj u v ∧
   ((y.val=u.val/\i=0)\/(y.val=v.val/\i=2 * k - 1)) ∧
   x.val=m+2 * k * (u.val * m+v.val)+i) ∨
  (∃ u v : Fin m,∃ i j : ℕ,u < v/\H.Adj u v/\i < 2 * k/\j < 2 * k ∧
   (i+1=j\/j+1=i) ∧
   x.val=m+2 * k * (u.val * m+v.val)+i ∧
   y.val=m+2 * k * (u.val * m+v.val)+j):=by
  intro x y hxy
  rcases hxy with hxy | hyx
  . rcases subRel_neighbors hk hxy with ⟨hxl,u,v,huv,ha,hxu,hy0⟩ | ⟨hyl,u,v,huv,ha,hyv,hx0⟩ | ⟨u,v,i,huv,ha,hi,hxi,hyi⟩
    . left;exact ⟨hxl,u,v,0,huv,ha,Or.inl ⟨hxu,rfl⟩,by omega⟩
    . right;left;exact ⟨hyl,u,v,2 * k - 1,huv,ha,Or.inr ⟨hyv,rfl⟩,hx0⟩
    . right;right;exact ⟨u,v,i,i+1,huv,ha,by omega,hi,Or.inl rfl,hxi,hyi⟩
  . rcases subRel_neighbors hk hyx with ⟨hyl,u,v,huv,ha,hyu,hx0⟩ | ⟨hxl,u,v,huv,ha,hxv,hy0⟩ | ⟨u,v,i,huv,ha,hi,hyi,hxi⟩
    . right;left;exact ⟨hyl,u,v,0,huv,ha,Or.inl ⟨hyu,rfl⟩,by omega⟩
    . left;exact ⟨hxl,u,v,2 * k - 1,huv,ha,Or.inr ⟨hxv,rfl⟩,hy0⟩
    . right;right;exact ⟨u,v,i+1,i,huv,ha,hi,by omega,Or.inr rfl,hxi,hyi⟩
 rcases hstep a b h1 with ⟨hal,u1,v1,i1,huv1,_,h1c,hb1⟩ | ⟨hbl,u1,v1,i1,huv1,_,h1c,ha1⟩ | ⟨u1,v1,ia1,ib1,huv1,_,hia1,hib1,hdiff1,ha1,hb1⟩
 ·
  rcases hstep b c h2 with ⟨hbl,_⟩ | ⟨hcl,u2,v2,i2,huv2,_,h2c,hb2⟩ | ⟨u2,v2,ib2,ic2,huv2,_,hib2,hic2,hdiff2,hb2,hc2⟩
  . omega
  ·
   rcases h3 with h3 | h3 <;> rcases subRel_ne_hubs (by omega) h3 with hlt | hlt <;> omega
  ·
   have hi1lt : i1 < 2 * k:=by rcases h1c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
   obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hi1lt hib2 (hb1.symm.trans hb2)
   rcases hstep a c h3 with ⟨_,u3,v3,i3,huv3,_,h3c,hc3⟩ | ⟨hcl,_⟩ | ⟨_,_,_,_,_,_,_,_,_,ha3,_⟩
   . have hi3lt : i3 < 2 * k:=by rcases h3c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
     obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hic2 hi3lt (hc2.symm.trans hc3)
     rcases h1c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rcases h3c with ⟨_,hi3⟩ | ⟨_,hi3⟩ <;> omega
   . omega
   . omega
 ·
  rcases hstep b c h2 with ⟨_,u2,v2,i2,huv2,_,h2c,hc2⟩ | ⟨hcl,_⟩ | ⟨_,_,_,_,_,_,_,_,_,hb2,_⟩
  . have hi1lt : i1 < 2 * k:=by rcases h1c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
    have hi2lt : i2 < 2 * k:=by rcases h2c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
    rcases hstep a c h3 with ⟨hal,_⟩ | ⟨hcl,_⟩ | ⟨u3,v3,ia3,ic3,huv3,_,hia3,hic3,hdiff3,ha3,hc3⟩
    . omega
    . omega
    . obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hi1lt hia3 (ha1.symm.trans ha3)
      obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hi2lt hic3 (hc2.symm.trans hc3)
      rcases h1c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rcases h2c with ⟨_,hi2⟩ | ⟨_,hi2⟩ <;> omega
  . rcases h3 with h3 | h3 <;> rcases subRel_ne_hubs (by omega) h3 with hlt | hlt <;> omega
  . omega
 ·
  rcases hstep b c h2 with ⟨hbl,_⟩ | ⟨hcl,u2,v2,i2,huv2,_,h2c,hb2⟩ | ⟨u2,v2,ib2,ic2,huv2,_,hib2,hic2,hdiff2,hb2,hc2⟩
  . omega
  . have hi2lt : i2 < 2 * k:=by rcases h2c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
    obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hib1 hi2lt (hb1.symm.trans hb2)
    rcases hstep a c h3 with ⟨hal,_⟩ | ⟨_,u3,v3,i3,huv3,_,h3c,ha3⟩ | ⟨_,_,_,_,_,_,_,_,_,_,hc3⟩
    . omega
    . have hi3lt : i3 < 2 * k:=by rcases h3c with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> omega
      obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hia1 hi3lt (ha1.symm.trans ha3)
      rcases h2c with ⟨_,hib⟩ | ⟨_,hib⟩ <;> rcases h3c with ⟨_,hia⟩ | ⟨_,hia⟩ <;> omega
    . omega
  . obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hib1 hib2 (hb1.symm.trans hb2)
    rcases hstep a c h3 with ⟨hal,_⟩ | ⟨hcl,_⟩ | ⟨u3,v3,ia3,ic3,huv3,_,hia3,hic3,hdiff3,ha3,hc3⟩
    . omega
    . omega
    . obtain ⟨rfl,rfl,rfl⟩:=subRel_unique_slot (by omega) hia1 hia3 (ha1.symm.trans ha3)
      obtain ⟨_,_,rfl⟩:=subRel_unique_slot (by omega) hic2 hic3 (hc2.symm.trans hc3)
      omega
lemma tfEmb {n m k : ℕ} {K : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
 (hk : 3<=k) (hemb : Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj))
 {a b c : Fin n} (hab : K.Adj a b) (hbc : K.Adj b c) (hac : K.Adj a c) : False:=by
 obtain ⟨e⟩:=hemb
 exact sdTF (by omega) (e a) (e b) (e c)
  (e.map_rel_iff.mpr hab) (e.map_rel_iff.mpr hbc) (e.map_rel_iff.mpr hac)
def stW (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wV (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ) : Bool :=
 (C.wires (List.ofFn x)).getD w false
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
 C.wires x=C.gates.foldl stW x:=rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
 (gs.foldl stW w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih]
  simp [stW]
  omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
 (gs.foldl stW w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stW w g).length:=by simp [stW];omega
  rw [ih (stW w g) hlt]
  simp [stW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length<=i) :
 w.getD i false=false:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 (C.wires (List.ofFn x)).length=n+C.gates.length:=by
 rw [wires_eq_foldl,foldl_stepWire_length,List.length_ofFn]
lemma wvO (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 wV n C x C.output=circuitFun n C x:=rfl
lemma wvI (n : ℕ) (C : Circuit) (x : Fin n->Bool) (i : Fin n) :
 wV n C x i.val=x i:=by
 unfold wV
 rw [wires_eq_foldl,foldl_stepWire_getD_lt C.gates (List.ofFn x) i.val (by simp)]
 simp [List.getD_eq_getElem?_getD]
lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ)
 (hw : n+C.gates.length<=w) : wV n C x w=false:=by
 unfold wV
 exact getD_ge_length _ _ (by rw [wires_length];exact hw)
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
 ∃ (pre post : List Gate) (gj : Gate),
  gs=pre ++ gj :: post/\pre.length=j/\gs[j]'hj=gj:=by
 refine ⟨gs.take j,gs.drop (j+1),gs[j]'hj,?_,by simp;omega,rfl⟩
 rw [List.cons_getElem_drop_succ,List.take_append_drop]
lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
 gateAt C j=C.gates[j]'hj:=by
 simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n->Bool) (j : ℕ)
 (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
   if i < n+j then wV n C x i else false):=by
 obtain ⟨pre,post,gj,hgs,hpre_len,hget⟩:=split_gates C.gates j hj
 have hgj : gateAt C j=gj:=by rw [gateAt_eq_getElem C j hj,hget]
 rw [hgj]
 let w0:=pre.foldl stW (List.ofFn x)
 have hW0L : w0.length=n+j:=by
  simp [w0,foldl_stepWire_length,hpre_len]
 have hCj : wV n C x (n+j)=gj.op.eval (gj.inputs.map fun i => w0.getD i false):=by
  unfold wV
  rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
  rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
  simp [stW,List.getD_eq_getElem?_getD,hW0L]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _ => ?_
 by_cases hi : i < n+j
 . rw [if_pos hi]
   unfold wV
   rw [wires_eq_foldl,hgs,List.foldl_append]
   exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
 . rw [if_neg hi]
   exact getD_ge_length w0 i (by omega)
lemma wvGR (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
 (x : Fin n->Bool) (j : ℕ) (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map (wV n C x)):=by
 rw [wireVal_gate n C x j hj]
 congr 1
 refine List.map_congr_left fun i hi => ?_
 rw [if_pos (hrb j hj i hi)]
def shiftDown (wOld u : ℕ) : ℕ :=
 if wOld < u then u - 1 else u
def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
 wC.length=wD.length+1 ∧
 w0.length<=wD.length ∧
 wC.getD w0.length false=bOld ∧
 (∀ u,u < w0.length->wD.getD u false=w0.getD u false) ∧
 (∀ u,u < w0.length->wC.getD u false=w0.getD u false) ∧
 (∀ u,w0.length < u->wD.getD (u - 1) false=wC.getD u false)
lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
 wiresMatch w0 bOld (w0 ++ [bOld]) w0:=by
 refine ⟨by simp,le_rfl,?_,fun _ _ => rfl,?_,?_⟩
 . simp [List.getD_eq_getElem?_getD]
 . intro u hu
   simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hu]
 . intro u hu
   have h1 : w0.length<=u - 1:=by omega
   have h2 : (w0 ++ [bOld]).length<=u:=by simp;omega
   rw [getD_ge_length w0 (u - 1) h1,getD_ge_length (w0 ++ [bOld]) u h2]
lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
 (hm : wiresMatch w0 bOld wC wD) :
 wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]):=by
 obtain ⟨hlen,hle,hbold,hltD,hltC,hgt⟩:=hm
 refine ⟨by simp;omega,by simp;omega,?_,?_,?_,?_⟩
 . have hlt : w0.length < wC.length:=by omega
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hlt]
   simpa [List.getD_eq_getElem?_getD] using hbold
 . intro u hu
   have h1 : u < wD.length:=by omega
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left h1]
   simpa [List.getD_eq_getElem?_getD] using hltD u hu
 . intro u hu
   have h2 : u < wC.length:=by omega
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left h2]
   simpa [List.getD_eq_getElem?_getD] using hltC u hu
 . intro u hu
   by_cases h1 : u - 1 < wD.length
   . have h2 : u < wC.length:=by omega
     rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1,List.getElem?_append_left h2]
     simpa [List.getD_eq_getElem?_getD] using hgt u hu
   . by_cases heq : u - 1=wD.length
     . have heqC : u=wC.length:=by omega
       rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,heq,heqC,
        List.getElem?_append_right le_rfl,List.getElem?_append_right le_rfl]
       simp
     . have hg1 : (wD ++ [b]).length<=u - 1:=by simp;omega
       have hg2 : (wC ++ [b]).length<=u:=by simp;omega
       rw [getD_ge_length _ _ hg1,getD_ge_length _ _ hg2]
lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
 (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u≠w0.length) :
 wD.getD (shiftDown w0.length u) false=wC.getD u false:=by
 unfold shiftDown
 by_cases hgt : w0.length < u
 . rw [if_pos hgt];exact hm.2.2.2.2.2 u hgt
 . rw [if_neg hgt]
   have hlt : u < w0.length:=by omega
   rw [hm.2.2.2.1 u hlt,hm.2.2.2.2.1 u hlt]
lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
 (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length=gsC.length)
 (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
  wiresMatch w0 bOld vC vD->vD.length=wD.length+t →
  (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
  (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
 wiresMatch w0 bOld (gsC.foldl stW wC) (gsD.foldl stW wD):=by
 induction gsC generalizing gsD wC wD with
 | nil =>
  cases gsD with
  | nil => exact hm
  | cons => simp at hlen
 | cons gC restC ih =>
  cases gsD with
  | nil => simp at hlen
  | cons gD restD =>
   simp only [List.foldl_cons]
   have heq0:=hstep 0 (by simp) (by simp) wC wD hm (by simp)
   simp only [List.getElem_cons_zero] at heq0
   have hm1 : wiresMatch w0 bOld (stW wC gC) (stW wD gD):=by
    unfold stW
    rw [heq0]
    exact wiresMatch_step hm
   apply ih restD (stW wC gC) (stW wD gD) hm1 (by simp at hlen;omega)
   intro t htC htD vC vD hmv hvlen
   have h':=hstep (t+1) (by simp;omega) (by simp;omega) vC vD hmv
    (by simp [stW] at hvlen ⊢;omega)
   simpa only [List.getElem_cons_succ] using h'
def eIn (g : Gate) : List ℕ :=
 GateOp.casesOn (motive:=fun _ => List ℕ) g.op
  g.inputs g.inputs (g.inputs.take 1) (fun _ => g.inputs) g.inputs
lemma eval_eq_effInputs (g : Gate) (f : ℕ->Bool) :
 g.op.eval (g.inputs.map f)=g.op.eval ((eIn g).map f):=by
 cases hop : g.op <;> simp only [eIn,hop,GateOp.eval]
 cases g.inputs <;> simp
lemma outLst {n : ℕ} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (hnc : ∃ x y : Fin n->Bool,circuitFun n C x≠circuitFun n C y)
 (hne : C.gates ≠ []) :
 C.output+1=n+C.gates.length:=by
 by_contra hne_out
 by_cases hge : n+C.gates.length<=C.output
 . obtain ⟨x,y,hxy⟩:=hnc
   apply hxy
   simp only [circuitFun,Circuit.eval]
   rw [getD_ge_length _ _ (by rw [wires_length];exact hge),
    getD_ge_length _ _ (by rw [wires_length];exact hge)]
 . have hpos : 0 < C.gates.length:=List.length_pos_of_ne_nil hne
   have hlt : C.output < n+(C.gates.length - 1):=by omega
   have hsplit : C.gates=C.gates.dropLast ++ [C.gates.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
   let D : Circuit:=⟨C.gates.dropLast,C.output⟩
   have hfitD : FanInTwo D:=fun g hg => hmin.1 g (List.dropLast_subset _ hg)
   have hfunD : circuitFun n D=circuitFun n C:=by
    funext x
    simp only [circuitFun,Circuit.eval,wires_eq_foldl,D]
    conv_rhs => rw [hsplit,List.foldl_append]
    have hlt' : C.output < (C.gates.dropLast.foldl stW (List.ofFn x)).length:=by
     rw [foldl_stepWire_length,List.length_ofFn,List.length_dropLast]
     exact hlt
    exact (foldl_stepWire_getD_lt [C.gates.getLast hne] _ C.output hlt').symm
   have hle:=hmin.2 D hfitD hfunD
   simp only [Circuit.size,D,List.length_dropLast] at hle
   omega
lemma evGtR {n : ℕ} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (hnc : ∃ x y : Fin n->Bool,circuitFun n C x≠circuitFun n C y)
 (j : ℕ) (hj : j+1 < C.gates.length) :
 ∃ j' < C.gates.length,j < j'/\n+j ∈ eIn (gateAt C j'):=by
 by_contra hno
 have hne : C.gates ≠ []:=by intro h;simp [h] at hj
 have hout : C.output+1=n+C.gates.length:=outLst hmin hnc hne
 have hj_lt : j < C.gates.length:=by omega
 obtain ⟨pre,post,gj,hgs,hpre_len,_⟩:=split_gates C.gates j hj_lt
 have hnot_read : ∀ (t : ℕ) (ht : t < post.length),
  ∀ u ∈ eIn (post[t]'ht),u≠n+j:=by
  intro t ht u hu heq
  subst heq
  apply hno
  have hidx : j+1+t < C.gates.length:=by
   have:=congrArg List.length hgs;simp [hpre_len] at this;omega
  have hget : gateAt C (j+1+t)=post[t]'ht:=by
   rw [gateAt_eq_getElem C (j+1+t) hidx]
   have h1 : (pre ++ gj :: post)[j+1+t]'(by rw [← hgs];exact hidx)=post[t]'ht:=by
    rw [List.getElem_append_right (by omega)]
    have hsub : j+1+t - pre.length=t+1:=by omega
    simp [hsub]
   simpa [hgs] using h1
  exact ⟨j+1+t,hidx,by omega,hget ▸ hu⟩
 let shiftGate (g : Gate) : Gate:=⟨g.op,g.inputs.map (shiftDown (n+j))⟩
 let D : Circuit:=⟨pre ++ post.map shiftGate,C.output - 1⟩
 have hfitD : FanInTwo D:=by
  intro g hg
  rcases List.mem_append.mp hg with hpre | hpost
  . exact hmin.1 g (by rw [hgs];exact List.mem_append_left _ hpre)
  . obtain ⟨g0,hg0,rfl⟩:=List.mem_map.mp hpost
    have hg0C:=hmin.1 g0 (by rw [hgs];exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
    exact ⟨hg0C.1,by simp [shiftGate,hg0C.2]⟩
 have hfunD : circuitFun n D=circuitFun n C:=by
  funext x
  simp only [circuitFun,Circuit.eval,wires_eq_foldl,D]
  conv_rhs => rw [hgs,List.foldl_append,List.foldl_cons]
  rw [List.foldl_append]
  let w0:=pre.foldl stW (List.ofFn x)
  have hW0L : w0.length=n+j:=by
   simp [w0,foldl_stepWire_length,hpre_len]
  let bOld:=gj.op.eval (gj.inputs.map fun i => w0.getD i false)
  have hm0 : wiresMatch w0 bOld (stW w0 gj) w0:=wiresMatch_init w0 bOld
  have hmEnd : wiresMatch w0 bOld (post.foldl stW (stW w0 gj))
   ((post.map shiftGate).foldl stW w0):=by
   refine foldl_wiresMatch w0 bOld post (post.map shiftGate) (stW w0 gj) w0 hm0
    (by simp) ?_
   intro t htC htD vC vD hmv _
   simp only [List.getElem_map,shiftGate]
   rw [eval_eq_effInputs ⟨(post[t]'htC).op,(post[t]'htC).inputs.map (shiftDown (n+j))⟩,
    eval_eq_effInputs (post[t]'htC)]
   have heff_map : eIn ⟨(post[t]'htC).op,(post[t]'htC).inputs.map (shiftDown (n+j))⟩ =
    (eIn (post[t]'htC)).map (shiftDown (n+j)):=by
    cases h : (post[t]'htC).op <;> simp [eIn,h,List.map_take]
   rw [heff_map,List.map_map]
   congr 1
   refine List.map_congr_left fun u hu => ?_
   rw [← hW0L]
   exact wiresMatch_getD_shiftDown hmv (by rw [hW0L];exact hnot_read t htC u hu)
  exact hmEnd.2.2.2.2.2 C.output (by omega)
 have hle:=hmin.2 D hfitD hfunD
 have hlenC : C.gates.length=pre.length+1+post.length:=by
  have:=congrArg List.length hgs;simp at this;omega
 simp only [Circuit.size,D,List.length_append,List.length_map] at hle
 omega
def aliasWire (wOld wNew u : ℕ) : ℕ :=
 if u=wOld then wNew else shiftDown wOld u
lemma no_duplicate_wire {n : ℕ} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (i j : ℕ) (hij : i < n+j) (hj : j < C.gates.length) :
 ∃ x : Fin n->Bool,wV n C x i≠wV n C x (n+j):=by
 by_contra hsame
 push Not at hsame
 obtain ⟨pre,post,gj,hgs,hpre_len,_⟩:=split_gates C.gates j hj
 let aliasGate (g : Gate) : Gate:=⟨g.op,g.inputs.map (aliasWire (n+j) i)⟩
 let D : Circuit:=⟨pre ++ post.map aliasGate,aliasWire (n+j) i C.output⟩
 have hfitD : FanInTwo D:=by
  intro g hg
  rcases List.mem_append.mp hg with hpre | hpost
  . exact hmin.1 g (by rw [hgs];exact List.mem_append_left _ hpre)
  . obtain ⟨g0,hg0,rfl⟩:=List.mem_map.mp hpost
    have hg0C:=hmin.1 g0 (by rw [hgs];exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
    exact ⟨hg0C.1,by simp [aliasGate,hg0C.2]⟩
 have hfunD : circuitFun n D=circuitFun n C:=by
  funext x
  have hxy:=hsame x
  simp only [circuitFun,Circuit.eval,wires_eq_foldl,D]
  conv_rhs => rw [hgs,List.foldl_append,List.foldl_cons]
  rw [List.foldl_append]
  let w0:=pre.foldl stW (List.ofFn x)
  have hW0L : w0.length=n+j:=by
   simp [w0,foldl_stepWire_length,hpre_len]
  let bOld:=gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hval_eq : w0.getD i false=bOld:=by
   have hCi : wV n C x i=w0.getD i false:=by
    unfold wV
    rw [wires_eq_foldl,hgs,List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
   have hCj : wV n C x (n+j)=bOld:=by
    unfold wV
    rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
    simp [stW,List.getD_eq_getElem?_getD,hW0L,bOld]
   rw [← hCi,← hCj,hxy]
  have hm0 : wiresMatch w0 bOld (stW w0 gj) w0:=wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool),wiresMatch w0 bOld vC vD →
   ∀ u,vD.getD (aliasWire (n+j) i u) false=vC.getD u false:=by
   intro vC vD hmv u
   unfold aliasWire
   by_cases hu : u=n+j
   . subst hu
     rw [if_pos rfl,hmv.2.2.2.1 i (by omega),hval_eq,← hW0L,hmv.2.2.1]
   . rw [if_neg hu,← hW0L]
     exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stW (stW w0 gj))
   ((post.map aliasGate).foldl stW w0):=by
   refine foldl_wiresMatch w0 bOld post (post.map aliasGate) (stW w0 gj) w0 hm0
    (by simp) ?_
   intro t htC htD vC vD hmv _
   simp only [List.getElem_map,aliasGate,List.map_map]
   congr 1
   refine List.map_congr_left fun u _ => ?_
   exact halias_get vC vD hmv u
  exact halias_get _ _ hmEnd C.output
 have hle:=hmin.2 D hfitD hfunD
 have hlenC : C.gates.length=pre.length+1+post.length:=by
  have:=congrArg List.length hgs;simp at this;omega
 simp only [Circuit.size,D,List.length_append,List.length_map] at hle
 omega
def rewriteTrueGate (wOld : ℕ) (g : Gate) : Gate :=
 match g.op with
 | .and => ⟨.and,(g.inputs.filter (fun u => u != wOld)).map (shiftDown wOld)⟩
 | .or =>
  if g.inputs.contains wOld then ⟨.and,[]⟩
  else ⟨.or,g.inputs.map (shiftDown wOld)⟩
 | .not =>
  match g.inputs with
  | [] => ⟨.not,[]⟩
  | u :: _ => if u=wOld then ⟨.or,[]⟩ else ⟨.not,[shiftDown wOld u]⟩
 | op => ⟨op,g.inputs.map (shiftDown wOld)⟩
lemma rewriteTrueGate_fit (wOld : ℕ) (g : Gate)
 (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)/\g.inputs.length<=2) :
 (rewriteTrueGate wOld g).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
  (rewriteTrueGate wOld g).inputs.length<=2:=by
 obtain ⟨hop,hlen⟩:=hg
 change g.op=.and\/g.op=.or\/g.op=.not at hop
 rcases hop with h | h | h
 . simp only [rewriteTrueGate,h,List.length_map]
   refine ⟨Or.inl rfl,(List.length_filter_le _ _).trans hlen⟩
 . simp only [rewriteTrueGate,h]
   split
   . exact ⟨Or.inl rfl,by simp⟩
   . exact ⟨Or.inr (Or.inl rfl),by simp [hlen]⟩
 . simp only [rewriteTrueGate,h]
   cases g.inputs with
   | nil => simp
   | cons u rest =>
    by_cases hu : u=wOld <;> simp [hu]
lemma rewriteTrueGate_eval (w0 : List Bool) (vC vD : List Bool)
 (hm : wiresMatch w0 true vC vD) (g : Gate)
 (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
 (rewriteTrueGate w0.length g).op.eval
  ((rewriteTrueGate w0.length g).inputs.map fun i => vD.getD i false) =
 g.op.eval (g.inputs.map fun i => vC.getD i false):=by
 change g.op=.and\/g.op=.or\/g.op=.not at hop
 rcases hop with h | h | h
 . simp only [rewriteTrueGate,h,GateOp.eval,List.map_map,List.all_map]
   induction g.inputs with
   | nil => rfl
   | cons u us ih =>
    by_cases hu : u=w0.length
    . subst hu
      simp only [List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,
       List.all_cons,Function.comp_apply,id_eq,hm.2.2.1,Bool.true_and]
      exact ih
    . have hne : (u != w0.length)=true:=bne_iff_ne.mpr hu
      simp only [List.filter_cons,hne,↓reduceIte,List.all_cons,Function.comp_apply,id_eq]
      rw [wiresMatch_getD_shiftDown hm hu,ih]
 . simp only [rewriteTrueGate,h]
   by_cases hmem : g.inputs.contains w0.length=true
   . rw [if_pos hmem]
     simp only [GateOp.eval,List.map_nil,List.all_nil]
     symm
     rw [List.any_eq_true]
     refine ⟨true,List.mem_map.mpr ⟨w0.length,List.contains_iff_mem.mp hmem,hm.2.2.1⟩,rfl⟩
   . rw [if_neg hmem]
     simp only [GateOp.eval,List.map_map]
     congr 1
     refine List.map_congr_left fun u hu => ?_
     have hne : u≠w0.length:=fun heq => hmem (List.contains_iff_mem.mpr (heq ▸ hu))
     exact wiresMatch_getD_shiftDown hm hne
 . obtain ⟨op,inputs⟩:=g
   dsimp only at h ⊢
   subst h
   cases inputs with
   | nil => simp [rewriteTrueGate,GateOp.eval]
   | cons u rest =>
    by_cases hu : u=w0.length
    . subst hu
      simp only [rewriteTrueGate,GateOp.eval,↓reduceIte,List.map_nil,List.any_nil,
       List.map_cons,List.headD_cons,hm.2.2.1,Bool.not_true]
    . simp only [rewriteTrueGate,GateOp.eval,hu,↓reduceIte,List.map_cons,List.map_nil,
       List.headD_cons,wiresMatch_getD_shiftDown hm hu]
lemma noCG {n : ℕ} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (hnc : ∃ x y : Fin n->Bool,circuitFun n C x≠circuitFun n C y)
 (j : ℕ) (hj : j < C.gates.length) :
 ∃ x y : Fin n->Bool,wV n C x (n+j)≠wV n C y (n+j):=by
 by_contra hconst
 push Not at hconst
 let x0 : Fin n->Bool:=fun _ => false
 let b : Bool:=wV n C x0 (n+j)
 have hall : ∀ x : Fin n->Bool,wV n C x (n+j)=b:=fun x => hconst x x0
 have hout_ne : C.output≠n+j:=by
  intro heq
  obtain ⟨x,y,hxy⟩:=hnc
  apply hxy
  simp only [← wvO,heq,hall x,hall y]
 obtain ⟨pre,post,gj,hgs,hpre_len,_⟩:=split_gates C.gates j hj
 cases hb : b with
 | false =>
  let big : ℕ:=n+C.gates.length
  let aliasGate (g : Gate) : Gate:=⟨g.op,g.inputs.map (aliasWire (n+j) big)⟩
  let D : Circuit:=⟨pre ++ post.map aliasGate,shiftDown (n+j) C.output⟩
  have hfitD : FanInTwo D:=by
   intro g hg
   rcases List.mem_append.mp hg with hpre | hpost
   . exact hmin.1 g (by rw [hgs];exact List.mem_append_left _ hpre)
   . obtain ⟨g0,hg0,rfl⟩:=List.mem_map.mp hpost
     have hg0C:=hmin.1 g0 (by rw [hgs];exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
     exact ⟨hg0C.1,by simp [aliasGate,hg0C.2]⟩
  have hfunD : circuitFun n D=circuitFun n C:=by
   funext x
   simp only [circuitFun,Circuit.eval,wires_eq_foldl,D]
   conv_rhs => rw [hgs,List.foldl_append,List.foldl_cons]
   rw [List.foldl_append]
   let w0:=pre.foldl stW (List.ofFn x)
   have hW0L : w0.length=n+j:=by
    simp [w0,foldl_stepWire_length,hpre_len]
   have hbf : gj.op.eval (gj.inputs.map fun k => w0.getD k false)=false:=by
    have hCj : wV n C x (n+j) =
     gj.op.eval (gj.inputs.map fun k => w0.getD k false):=by
     unfold wV
     rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
     rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
     simp [stW,List.getD_eq_getElem?_getD,hW0L]
    rw [← hCj,hall x,hb]
   have hm0 : wiresMatch w0 false (stW w0 gj) w0:=by
    unfold stW;rw [hbf];exact wiresMatch_init w0 false
   have hlenC : C.gates.length=pre.length+1+post.length:=by
    have:=congrArg List.length hgs;simp at this;omega
   have hmEnd : wiresMatch w0 false (post.foldl stW (stW w0 gj))
    ((post.map aliasGate).foldl stW w0):=by
    refine foldl_wiresMatch w0 false post (post.map aliasGate) (stW w0 gj) w0 hm0
     (by simp) ?_
    intro t htC htD vC vD hmv hvlen
    simp only [List.getElem_map,aliasGate,List.map_map]
    congr 1
    refine List.map_congr_left fun u _ => ?_
    simp only [Function.comp_apply,aliasWire]
    by_cases hu : u=n+j
    . subst hu
      simp only [↓reduceIte]
      rw [getD_ge_length vD big (by omega),← hW0L,hmv.2.2.1]
    . simp only [hu,↓reduceIte]
      rw [← hW0L]
      exact wiresMatch_getD_shiftDown hmv (by omega)
   rw [← hW0L]
   exact wiresMatch_getD_shiftDown hmEnd (by rw [hW0L];exact hout_ne)
  have hle:=hmin.2 D hfitD hfunD
  have hlenC : C.gates.length=pre.length+1+post.length:=by
   have:=congrArg List.length hgs;simp at this;omega
  simp only [Circuit.size,D,List.length_append,List.length_map] at hle
  omega
 | true =>
  let D : Circuit:=⟨pre ++ post.map (rewriteTrueGate (n+j)),shiftDown (n+j) C.output⟩
  have hfitD : FanInTwo D:=by
   intro g hg
   rcases List.mem_append.mp hg with hpre | hpost
   . exact hmin.1 g (by rw [hgs];exact List.mem_append_left _ hpre)
   . obtain ⟨g0,hg0,rfl⟩:=List.mem_map.mp hpost
     have hg0C:=hmin.1 g0 (by rw [hgs];exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
     exact rewriteTrueGate_fit (n+j) g0 hg0C
  have hfunD : circuitFun n D=circuitFun n C:=by
   funext x
   simp only [circuitFun,Circuit.eval,wires_eq_foldl,D]
   conv_rhs => rw [hgs,List.foldl_append,List.foldl_cons]
   rw [List.foldl_append]
   let w0:=pre.foldl stW (List.ofFn x)
   have hW0L : w0.length=n+j:=by
    simp [w0,foldl_stepWire_length,hpre_len]
   have hbt : gj.op.eval (gj.inputs.map fun k => w0.getD k false)=true:=by
    have hCj : wV n C x (n+j) =
     gj.op.eval (gj.inputs.map fun k => w0.getD k false):=by
     unfold wV
     rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
     rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
     simp [stW,List.getD_eq_getElem?_getD,hW0L]
    rw [← hCj,hall x,hb]
   have hm0 : wiresMatch w0 true (stW w0 gj) w0:=by
    unfold stW;rw [hbt];exact wiresMatch_init w0 true
   have hmEnd : wiresMatch w0 true (post.foldl stW (stW w0 gj))
    ((post.map (rewriteTrueGate (n+j))).foldl stW w0):=by
    refine foldl_wiresMatch w0 true post (post.map (rewriteTrueGate (n+j)))
     (stW w0 gj) w0 hm0 (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map]
    have hgC:=hmin.1 (post[t]'htC)
     (by rw [hgs];exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.getElem_mem htC)))
    simpa only [hW0L] using rewriteTrueGate_eval w0 vC vD hmv (post[t]'htC) hgC.1
   simpa only [hW0L] using wiresMatch_getD_shiftDown hmEnd (by rw [hW0L];exact hout_ne)
  have hle:=hmin.2 D hfitD hfunD
  have hlenC : C.gates.length=pre.length+1+post.length:=by
   have:=congrArg List.length hgs;simp at this;omega
  simp only [Circuit.size,D,List.length_append,List.length_map] at hle
  omega
lemma minGS {n : ℕ} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (hnc : ∃ x y : Fin n->Bool,circuitFun n C x≠circuitFun n C y)
 (j : ℕ) (hj : j < C.gates.length) :
 ((gateAt C j).op=.and/\∃ a b : ℕ,(gateAt C j).inputs=[a,b]/\a < n+j/\b < n+j/\a≠b) ∨
 ((gateAt C j).op=.or/\∃ a b : ℕ,(gateAt C j).inputs=[a,b]/\a < n+j/\b < n+j/\a≠b) ∨
 ((gateAt C j).op=.not/\∃ a : ℕ,eIn (gateAt C j)=[a]/\a < n+j):=by
 have hgmem : gateAt C j ∈ C.gates:=by
  rw [gateAt_eq_getElem C j hj];exact List.getElem_mem hj
 obtain ⟨hop,hlen⟩:=hmin.1 (gateAt C j) hgmem
 change (gateAt C j).op=.and\/(gateAt C j).op=.or\/(gateAt C j).op=.not at hop
 have hncj:=noCG hmin hnc j hj
 rcases hop with hop | hop | hop
 . left
   refine ⟨hop,?_⟩
   cases hin : (gateAt C j).inputs with
   | nil =>
    exfalso
    obtain ⟨x,y,hxy⟩:=hncj
    apply hxy
    simp [wireVal_gate n C _ j hj,hop,hin,GateOp.eval]
   | cons a rest =>
    cases rest with
    | nil =>
     exfalso
     by_cases ha : a < n+j
     . obtain ⟨x,hx⟩:=no_duplicate_wire hmin a j ha hj
       apply hx
       simp [wireVal_gate n C x j hj,hop,hin,ha,GateOp.eval]
     . obtain ⟨x,y,hxy⟩:=hncj
       apply hxy
       simp [wireVal_gate n C _ j hj,hop,hin,ha,GateOp.eval]
    | cons b rest2 =>
     cases rest2 with
     | nil =>
      have ha : a < n+j:=by
       by_contra hna
       obtain ⟨x,y,hxy⟩:=hncj
       apply hxy
       simp [wireVal_gate n C _ j hj,hop,hin,hna,GateOp.eval]
      have hb : b < n+j:=by
       by_contra hnb
       obtain ⟨x,y,hxy⟩:=hncj
       apply hxy
       simp [wireVal_gate n C _ j hj,hop,hin,hnb,GateOp.eval]
      have hab : a≠b:=by
       intro heq;subst heq
       obtain ⟨x,hx⟩:=no_duplicate_wire hmin a j ha hj
       apply hx
       simp [wireVal_gate n C x j hj,hop,hin,ha,GateOp.eval]
      exact ⟨a,b,rfl,ha,hb,hab⟩
     | cons _ _ => simp [hin] at hlen
 . right;left
   refine ⟨hop,?_⟩
   cases hin : (gateAt C j).inputs with
   | nil =>
    exfalso
    obtain ⟨x,y,hxy⟩:=hncj
    apply hxy
    simp [wireVal_gate n C _ j hj,hop,hin,GateOp.eval]
   | cons a rest =>
    cases rest with
    | nil =>
     exfalso
     by_cases ha : a < n+j
     . obtain ⟨x,hx⟩:=no_duplicate_wire hmin a j ha hj
       apply hx
       simp [wireVal_gate n C x j hj,hop,hin,ha,GateOp.eval]
     . obtain ⟨x,y,hxy⟩:=hncj
       apply hxy
       simp [wireVal_gate n C _ j hj,hop,hin,ha,GateOp.eval]
    | cons b rest2 =>
     cases rest2 with
     | nil =>
      have ha : a < n+j:=by
       by_contra hna
       by_cases hb : b < n+j
       . obtain ⟨x,hx⟩:=no_duplicate_wire hmin b j hb hj
         apply hx
         simp [wireVal_gate n C x j hj,hop,hin,hna,hb,GateOp.eval]
       . obtain ⟨x,y,hxy⟩:=hncj
         apply hxy
         simp [wireVal_gate n C _ j hj,hop,hin,hna,hb,GateOp.eval]
      have hb : b < n+j:=by
       by_contra hnb
       obtain ⟨x,hx⟩:=no_duplicate_wire hmin a j ha hj
       apply hx
       simp [wireVal_gate n C x j hj,hop,hin,ha,hnb,GateOp.eval]
      have hab : a≠b:=by
       intro heq;subst heq
       obtain ⟨x,hx⟩:=no_duplicate_wire hmin a j ha hj
       apply hx
       simp [wireVal_gate n C x j hj,hop,hin,ha,GateOp.eval]
      exact ⟨a,b,rfl,ha,hb,hab⟩
     | cons _ _ => simp [hin] at hlen
 . right;right
   refine ⟨hop,?_⟩
   cases hin : (gateAt C j).inputs with
   | nil =>
    exfalso
    obtain ⟨x,y,hxy⟩:=hncj
    apply hxy
    simp [wireVal_gate n C _ j hj,hop,hin,GateOp.eval]
   | cons a rest =>
    have ha : a < n+j:=by
     by_contra hna
     obtain ⟨x,y,hxy⟩:=hncj
     apply hxy
     simp [wireVal_gate n C _ j hj,hop,hin,hna,GateOp.eval]
    exact ⟨a,by simp [eIn,hop,hin],ha⟩
def evE (env : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ :=
 env.getD i (Sum.inl false)
def sGt (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
 List Gate × List (Bool ⊕ ℕ) :=
 let (gs,env):=st
 match g.op with
 | .not =>
  match evE env (g.inputs.headD env.length) with
  | Sum.inl c => (gs,env ++ [Sum.inl (!c)])
  | Sum.inr u => (gs ++ [⟨.not,[u]⟩],env ++ [Sum.inr (n+gs.length)])
 | .and =>
  match g.inputs with
  | [] => (gs,env ++ [Sum.inl true])
  | [a] => (gs,env ++ [evE env a])
  | a :: b :: _ =>
   match evE env a with
   | Sum.inl false => (gs,env ++ [Sum.inl false])
   | Sum.inl true => (gs,env ++ [evE env b])
   | Sum.inr u =>
    match evE env b with
    | Sum.inl false => (gs,env ++ [Sum.inl false])
    | Sum.inl true => (gs,env ++ [Sum.inr u])
    | Sum.inr v =>
     if u=v then (gs,env ++ [Sum.inr u])
     else (gs ++ [⟨.and,[u,v]⟩],env ++ [Sum.inr (n+gs.length)])
 | .or =>
  match g.inputs with
  | [] => (gs,env ++ [Sum.inl false])
  | [a] => (gs,env ++ [evE env a])
  | a :: b :: _ =>
   match evE env a with
   | Sum.inl true => (gs,env ++ [Sum.inl true])
   | Sum.inl false => (gs,env ++ [evE env b])
   | Sum.inr u =>
    match evE env b with
    | Sum.inl true => (gs,env ++ [Sum.inl true])
    | Sum.inl false => (gs,env ++ [Sum.inr u])
    | Sum.inr v =>
     if u=v then (gs,env ++ [Sum.inr u])
     else (gs ++ [⟨.or,[u,v]⟩],env ++ [Sum.inr (n+gs.length)])
 | _ => (gs,env ++ [Sum.inl false])
def simplifyInit (n : ℕ) (l : Fin n) (b : Bool) : List Gate × List (Bool ⊕ ℕ) :=
 ([],List.ofFn fun i : Fin n => if i=l then Sum.inl b else Sum.inr i.val)
def sPfx (n : ℕ) (l : Fin n) (b : Bool) (gs : List Gate) (k : ℕ) :
 List Gate × List (Bool ⊕ ℕ) :=
 (gs.take k).foldl (sGt n) (simplifyInit n l b)
lemma simplifyPrefix_zero (n : ℕ) (l : Fin n) (b : Bool) (gs : List Gate) :
 sPfx n l b gs 0=simplifyInit n l b:=rfl
lemma simplifyPrefix_succ (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 (k : ℕ) (hk : k < C.gates.length) :
 sPfx n l b C.gates (k+1) =
  sGt n (sPfx n l b C.gates k) (gateAt C k):=by
 unfold sPfx
 rw [List.take_succ_eq_append_getElem hk,List.foldl_append,List.foldl_cons,List.foldl_nil,
  gateAt_eq_getElem C k hk]
lemma simplifyGate_env_len (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
 (sGt n st g).2.length=st.2.length+1:=by
 rcases st with ⟨gs,env⟩
 simp only [sGt]
 repeat' (all_goals split)
 all_goals simp
lemma simplifyGate_env_prefix (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
 (w : ℕ) (hw : w < st.2.length) :
 evE (sGt n st g).2 w=evE st.2 w:=by
 rcases st with ⟨gs,env⟩
 have happ : ∀ x : Bool ⊕ ℕ,evE (env ++ [x]) w=evE env w:=by
  intro x
  simp [evE,List.getD_eq_getElem?_getD,List.getElem?_append_left hw]
 simp only [sGt]
 repeat' (all_goals split)
 all_goals exact happ _
lemma simplifyGate_gs_len_le (n : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
 st.1.length<=(sGt n st g).1.length ∧
 (sGt n st g).1.length<=st.1.length+1:=by
 rcases st with ⟨gs,env⟩
 simp only [sGt]
 repeat' (all_goals split)
 all_goals simp
def sInv (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit) (k : ℕ)
 (st : List Gate × List (Bool ⊕ ℕ)) : Prop :=
 st.2.length=n+k ∧
 (∀ g ∈ st.1,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)/\g.inputs.length<=2) ∧
 ∀ (x : Fin n->Bool) (w : ℕ),w < n+k →
  match evE st.2 w with
  | Sum.inl c => wV n C (update x l b) w=c
  | Sum.inr u => u < n+st.1.length ∧
   (st.1.foldl stW (List.ofFn x)).getD u false=wV n C (update x l b) w
lemma spExt {n : ℕ} {l : Fin n} {b : Bool} {C : Circuit} {k : ℕ}
 {gs : List Gate} {env : List (Bool ⊕ ℕ)} {gOpt : Option Gate} {res : Bool ⊕ ℕ}
 (hinv : sInv n l b C k (gs,env))
 (hfit_new : ∀ g',gOpt=some g' →
  g'.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)/\g'.inputs.length<=2)
 (hres : ∀ x : Fin n->Bool,
  match res with
  | Sum.inl c => wV n C (update x l b) (n+k)=c
  | Sum.inr u =>
   let gs':=match gOpt with | none => gs | some g' => gs ++ [g']
   u < n+gs'.length ∧
   (gs'.foldl stW (List.ofFn x)).getD u false =
    wV n C (update x l b) (n+k)) :
 sInv n l b C (k+1)
  (match gOpt with | none => gs | some g' => gs ++ [g'],env ++ [res]):=by
 obtain ⟨hlen,hfit,hvals⟩:=hinv
 dsimp only at hlen
 let gs':=match gOpt with | none => gs | some g' => gs ++ [g']
 have hlen' : (env ++ [res]).length=n+(k+1):=by simp [hlen];omega
 have hfit' : ∀ g ∈ gs',g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
  g.inputs.length<=2:=by
  intro g hg
  cases hgOpt : gOpt with
  | none => simp only [gs',hgOpt] at hg;exact hfit g hg
  | some g' =>
   simp only [gs',hgOpt,List.mem_append,List.mem_singleton] at hg
   rcases hg with hg | rfl
   . exact hfit g hg
   . exact hfit_new g hgOpt
 refine ⟨hlen',hfit',?_⟩
 intro x w hw
 by_cases hlt : w < n+k
 . have hev : evE (env ++ [res]) w=evE env w:=by
    simp [evE,List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : w < env.length)]
   rw [hev]
   have hv:=hvals x w hlt
   cases hcase : evE env w with
   | inl c => simpa [hcase] using hv
   | inr u =>
    simp only [hcase] at hv
    refine ⟨?_,?_⟩
    . cases hgOpt : gOpt <;> simp [gs',hgOpt] <;> omega
    . cases hgOpt : gOpt with
      | none => simpa [gs',hgOpt] using hv.2
      | some g' =>
       simp only [gs',hgOpt,List.foldl_append]
       rw [foldl_stepWire_getD_lt [g'] _ u (by rw [foldl_stepWire_length,List.length_ofFn];exact hv.1)]
       exact hv.2
 . have hweq : w=n+k:=by omega
   subst hweq
   have hev : evE (env ++ [res]) (n+k)=res:=by
    simp [evE,List.getD_eq_getElem?_getD,hlen]
   rw [hev]
   exact hres x
lemma evalWireEnv_val {n : ℕ} {l : Fin n} {b : Bool} {C : Circuit} {k : ℕ}
 {gs : List Gate} {env : List (Bool ⊕ ℕ)}
 (hinv : sInv n l b C k (gs,env)) (x : Fin n->Bool) (a : ℕ) :
 (match evE env a with
  | Sum.inl c => c
  | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false) =
 (if a < n+k then wV n C (update x l b) a else false):=by
 by_cases ha : a < n+k
 . rw [if_pos ha]
   have hv:=hinv.2.2 x a ha
   cases h : evE env a with
   | inl c => simp only [h] at hv;exact hv.symm
   | inr u => simp only [h] at hv;exact hv.2
 . rw [if_neg ha]
   have hlen : env.length=n+k:=hinv.1
   have hnone : evE env a=Sum.inl false:=by
    simp [evE,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : env.length<=a)]
   rw [hnone]
lemma spInv (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 (hfit : FanInTwo C) (k : ℕ) (hk : k<=C.gates.length) :
 sInv n l b C k (sPfx n l b C.gates k):=by
 induction k with
 | zero =>
  rw [simplifyPrefix_zero]
  refine ⟨by simp [simplifyInit],by simp [simplifyInit],?_⟩
  intro x w hw
  have hwn : w < n:=by omega
  let wf : Fin n:=⟨w,hwn⟩
  have hev : evE (simplifyInit n l b).2 w=if wf=l then Sum.inl b else Sum.inr w:=by
   simp [simplifyInit,evE,List.getD_eq_getElem?_getD,hwn,wf]
  rw [hev]
  by_cases hwl : wf=l
  . rw [if_pos hwl]
    have h1 : wV n C (update x l b) wf.val=update x l b wf :=
     wvI n C (update x l b) wf
    simpa [wf,hwl] using h1
  . rw [if_neg hwl]
    refine ⟨by simpa [simplifyInit] using hw,?_⟩
    simp only [simplifyInit,List.foldl_nil]
    have h1 : (List.ofFn x).getD w false=x wf:=by
     simp [List.getD_eq_getElem?_getD,hwn,wf]
    have h2 : wV n C (update x l b) wf.val=update x l b wf :=
     wvI n C (update x l b) wf
    rw [h1,show w=wf.val from rfl,h2,Function.update_of_ne hwl]
 | succ k ih =>
  have hklt : k < C.gates.length:=by omega
  rw [simplifyPrefix_succ n l b C k hklt]
  have hinv:=ih (by omega)
  rcases hst : sPfx n l b C.gates k with ⟨gs,env⟩
  rw [hst] at hinv
  have hlen_env : env.length=n+k:=hinv.1
  have hgk_mem : gateAt C k ∈ C.gates:=by
   rw [gateAt_eq_getElem C k hklt];exact List.getElem_mem hklt
  obtain ⟨hop,hglen⟩:=hfit (gateAt C k) hgk_mem
  change (gateAt C k).op=.and\/(gateAt C k).op=.or\/(gateAt C k).op=.not at hop
  have hval_eval : ∀ x : Fin n->Bool,
   wV n C (update x l b) (n+k) =
    (gateAt C k).op.eval ((gateAt C k).inputs.map fun a =>
     match evE env a with
     | Sum.inl c => c
     | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false):=by
   intro x
   rw [wireVal_gate n C (update x l b) k hklt]
   congr 1
   refine List.map_congr_left fun a _ => ?_
   exact (evalWireEnv_val hinv x a).symm
  have hlt_of_inr : ∀ {w u},evE env w=Sum.inr u->w < n+k:=by
   intro w u hw;by_contra hnw
   have : evE env w=Sum.inl false:=by
    simp [evE,List.getD_eq_getElem?_getD,
     List.getElem?_eq_none (by omega : env.length<=w)]
   rw [this] at hw;cases hw
  rcases hop with hop | hop | hop
  ·
   simp only [sGt,hop]
   cases hin : (gateAt C k).inputs with
   | nil =>
    exact spExt (gOpt:=none) hinv (by simp) (fun x => by
     rw [hval_eval x,hop,hin];rfl)
   | cons a rest =>
    cases rest with
    | nil =>
     refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
     have hv:=hval_eval x
     rw [hop,hin] at hv
     simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
      id_eq,Bool.and_true] at hv
     cases ha : evE env a with
     | inl c => simpa [ha] using hv
     | inr u =>
      have hu:=hinv.2.2 x a (hlt_of_inr ha)
      rw [ha] at hu hv
      exact ⟨hu.1,hv.symm⟩
    | cons b_in rest2 =>
     cases rest2 with
     | nil =>
      dsimp only
      have hval2 : ∀ x : Fin n->Bool,
       wV n C (update x l b) (n+k) =
       ((match evE env a with | Sum.inl c => c | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false) &&
        (match evE env b_in with | Sum.inl c => c | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false)):=by
       intro x;have hv:=hval_eval x;rw [hop,hin] at hv
       simpa [GateOp.eval] using hv
      cases ha : evE env a with
      | inl c1 =>
       cases c1 with
       | false =>
        exact spExt (gOpt:=none) hinv (by simp)
         (fun x => by simp [hval2 x,ha])
       | true =>
        cases hb : evE env b_in with
        | inl c2 =>
         exact spExt (gOpt:=none) hinv (by simp)
          (fun x => by simp [hval2 x,ha,hb])
        | inr v =>
         refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
         have hv:=hinv.2.2 x b_in (hlt_of_inr hb)
         rw [hb] at hv
         exact ⟨hv.1,by simp [hval2 x,ha,hb]⟩
      | inr u =>
       cases hb : evE env b_in with
       | inl c2 =>
        cases c2 with
        | false =>
         exact spExt (gOpt:=none) hinv (by simp)
          (fun x => by simp [hval2 x,ha,hb])
        | true =>
         refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
         have hu:=hinv.2.2 x a (hlt_of_inr ha)
         rw [ha] at hu
         exact ⟨hu.1,by simp [hval2 x,ha,hb]⟩
       | inr v =>
        dsimp only
        by_cases huv : u=v
        . rw [if_pos huv]
          refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
          have hu:=hinv.2.2 x a (hlt_of_inr ha)
          rw [ha] at hu
          exact ⟨hu.1,by simp [hval2 x,ha,hb,huv]⟩
        . rw [if_neg huv]
          refine spExt (gOpt:=some ⟨.and,[u,v]⟩) hinv
           (by rintro _ ⟨⟩;exact ⟨Or.inl rfl,by simp⟩) (fun x => ?_)
          refine ⟨by simp,?_⟩
          rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
          have hlenw : (gs.foldl stW (List.ofFn x)).length=n+gs.length:=by
           rw [foldl_stepWire_length,List.length_ofFn]
          rw [hval2 x,ha,hb]
          simp only [stW,List.getD_eq_getElem?_getD,← hlenw,
           List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero,
           Option.getD_some,GateOp.eval,List.map_cons,List.map_nil,
           List.all_cons,List.all_nil,id_eq,Bool.and_true]
     | cons _ _ => simp [hin] at hglen
  ·
   simp only [sGt,hop]
   cases hin : (gateAt C k).inputs with
   | nil =>
    exact spExt (gOpt:=none) hinv (by simp) (fun x => by
     rw [hval_eval x,hop,hin];rfl)
   | cons a rest =>
    cases rest with
    | nil =>
     refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
     have hv:=hval_eval x
     rw [hop,hin] at hv
     simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
      id_eq,Bool.or_false] at hv
     cases ha : evE env a with
     | inl c => simpa [ha] using hv
     | inr u =>
      have hu:=hinv.2.2 x a (hlt_of_inr ha)
      rw [ha] at hu hv
      exact ⟨hu.1,hv.symm⟩
    | cons b_in rest2 =>
     cases rest2 with
     | nil =>
      dsimp only
      have hval2 : ∀ x : Fin n->Bool,
       wV n C (update x l b) (n+k) =
       ((match evE env a with | Sum.inl c => c | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false) ||
        (match evE env b_in with | Sum.inl c => c | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false)):=by
       intro x;have hv:=hval_eval x;rw [hop,hin] at hv
       simpa [GateOp.eval] using hv
      cases ha : evE env a with
      | inl c1 =>
       cases c1 with
       | true =>
        exact spExt (gOpt:=none) hinv (by simp)
         (fun x => by simp [hval2 x,ha])
       | false =>
        cases hb : evE env b_in with
        | inl c2 =>
         exact spExt (gOpt:=none) hinv (by simp)
          (fun x => by simp [hval2 x,ha,hb])
        | inr v =>
         refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
         have hv:=hinv.2.2 x b_in (hlt_of_inr hb)
         rw [hb] at hv
         exact ⟨hv.1,by simp [hval2 x,ha,hb]⟩
      | inr u =>
       cases hb : evE env b_in with
       | inl c2 =>
        cases c2 with
        | true =>
         exact spExt (gOpt:=none) hinv (by simp)
          (fun x => by simp [hval2 x,ha,hb])
        | false =>
         refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
         have hu:=hinv.2.2 x a (hlt_of_inr ha)
         rw [ha] at hu
         exact ⟨hu.1,by simp [hval2 x,ha,hb]⟩
       | inr v =>
        dsimp only
        by_cases huv : u=v
        . rw [if_pos huv]
          refine spExt (gOpt:=none) hinv (by simp) (fun x => ?_)
          have hu:=hinv.2.2 x a (hlt_of_inr ha)
          rw [ha] at hu
          exact ⟨hu.1,by simp [hval2 x,ha,hb,huv]⟩
        . rw [if_neg huv]
          refine spExt (gOpt:=some ⟨.or,[u,v]⟩) hinv
           (by rintro _ ⟨⟩;exact ⟨Or.inr (Or.inl rfl),by simp⟩) (fun x => ?_)
          refine ⟨by simp,?_⟩
          rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
          have hlenw : (gs.foldl stW (List.ofFn x)).length=n+gs.length:=by
           rw [foldl_stepWire_length,List.length_ofFn]
          rw [hval2 x,ha,hb]
          simp only [stW,List.getD_eq_getElem?_getD,← hlenw,
           List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero,
           Option.getD_some,GateOp.eval,List.map_cons,List.map_nil,
           List.any_cons,List.any_nil,id_eq,Bool.or_false]
     | cons _ _ => simp [hin] at hglen
  ·
   simp only [sGt,hop]
   have hvaln : ∀ x : Fin n->Bool,
    wV n C (update x l b) (n+k) =
    !(match evE env ((gateAt C k).inputs.headD env.length) with
     | Sum.inl c => c
     | Sum.inr u => (gs.foldl stW (List.ofFn x)).getD u false):=by
    intro x
    have hv:=hval_eval x
    rw [hop] at hv
    cases hin : (gateAt C k).inputs with
    | nil =>
     simp only [hin,List.map_nil,GateOp.eval,List.headD_nil] at hv ⊢
     have hnone : evE env env.length=Sum.inl false:=by
      simp [evE,List.getD_eq_getElem?_getD]
     rw [hnone];exact hv
    | cons a rest =>
     simpa [hin,GateOp.eval] using hv
   cases ha : evE env ((gateAt C k).inputs.headD env.length) with
   | inl c =>
    exact spExt (gOpt:=none) hinv (by simp)
     (fun x => by rw [hvaln x,ha])
   | inr u =>
    refine spExt (gOpt:=some ⟨.not,[u]⟩) hinv
     (by rintro _ ⟨⟩;exact ⟨Or.inr (Or.inr rfl),by simp⟩) (fun x => ?_)
    refine ⟨by simp,?_⟩
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    have hlenw : (gs.foldl stW (List.ofFn x)).length=n+gs.length:=by
     rw [foldl_stepWire_length,List.length_ofFn]
    rw [hvaln x,ha]
    simp only [stW,List.getD_eq_getElem?_getD,← hlenw,
     List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_cons_zero,
     Option.getD_some,GateOp.eval,List.map_cons,List.map_nil,List.headD_cons]
lemma simplifyPrefix_env_len (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 (k : ℕ) (hk : k<=C.gates.length) :
 (sPfx n l b C.gates k).2.length=n+k:=by
 induction k with
 | zero => simp [simplifyPrefix_zero,simplifyInit]
 | succ k ih =>
  rw [simplifyPrefix_succ n l b C k (by omega),simplifyGate_env_len,ih (by omega)]
  omega
lemma spEnvS (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 {k1 k2 w : ℕ} (hk1 : k1<=k2) (hk2 : k2<=C.gates.length) (hw : w < n+k1) :
 evE (sPfx n l b C.gates k2).2 w =
 evE (sPfx n l b C.gates k1).2 w:=by
 induction k2 with
 | zero =>
  have : k1=0:=by omega
  subst this;rfl
 | succ k2 ih =>
  by_cases h : k1=k2+1
  . subst h;rfl
  . have hk1' : k1<=k2:=by omega
    rw [simplifyPrefix_succ n l b C k2 (by omega)]
    have hlen:=simplifyPrefix_env_len n l b C k2 (by omega)
    rw [simplifyGate_env_prefix n _ _ w (by omega),ih hk1' (by omega)]
def isD (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit) (k : ℕ) : Bool :=
 decide ((sPfx n l b C.gates (k+1)).1.length=(sPfx n l b C.gates k).1.length)
lemma simplifyPrefix_size_add_deleted (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 (k : ℕ) (hk : k<=C.gates.length) :
 (sPfx n l b C.gates k).1.length +
  ((Finset.range k).filter (fun j => isD n l b C j=true)).card=k:=by
 induction k with
 | zero => simp [simplifyPrefix_zero,simplifyInit]
 | succ k ih =>
  rw [Finset.range_add_one,Finset.filter_insert]
  have hstep : (sPfx n l b C.gates k).1.length ≤
   (sPfx n l b C.gates (k+1)).1.length ∧
   (sPfx n l b C.gates (k+1)).1.length ≤
   (sPfx n l b C.gates k).1.length+1:=by
   rw [simplifyPrefix_succ n l b C k (by omega)]
   exact simplifyGate_gs_len_le n _ _
  have hnotmem : k ∉ (Finset.range k).filter (fun j => isD n l b C j=true):=by
   simp
  have ih':=ih (by omega)
  by_cases hdel : isD n l b C k=true
  . rw [if_pos hdel,card_insert_of_notMem hnotmem]
    have heq : (sPfx n l b C.gates (k+1)).1.length =
     (sPfx n l b C.gates k).1.length:=by
     simpa [isD] using hdel
    omega
  . rw [if_neg hdel]
    have hne : (sPfx n l b C.gates (k+1)).1.length ≠
     (sPfx n l b C.gates k).1.length:=by
     simpa [isD] using hdel
    omega
lemma deleted_of_inl_input (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 (hmin : IsMinimalCircuit n C)
 (hnc : ∃ x y : Fin n->Bool,circuitFun n C x≠circuitFun n C y)
 {k : ℕ} (hk : k < C.gates.length) {w : ℕ} (hw : w ∈ eIn (gateAt C k))
 {c : Bool} (hc : evE (sPfx n l b C.gates k).2 w=Sum.inl c) :
 isD n l b C k=true:=by
 unfold isD
 rw [decide_eq_true_eq,simplifyPrefix_succ n l b C k hk]
 rcases hst : sPfx n l b C.gates k with ⟨gs,env⟩
 rw [hst] at hc
 rcases minGS hmin hnc k hk with ⟨hop,a,b_in,hin,_,_,_⟩ |
  ⟨hop,a,b_in,hin,_,_,_⟩ | ⟨hop,a,heff,_⟩
 . simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hw
   simp only [sGt,hop,hin]
   rcases hw with rfl | rfl
   . rw [hc];cases c <;> cases evE env b_in with
     | inl c2 => cases c2 <;> rfl
     | inr _ => rfl
   . rw [hc];cases evE env a with
     | inl c1 => cases c1 <;> cases c <;> rfl
     | inr _ => cases c <;> rfl
 . simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hw
   simp only [sGt,hop,hin]
   rcases hw with rfl | rfl
   . rw [hc];cases c <;> cases evE env b_in with
     | inl c2 => cases c2 <;> rfl
     | inr _ => rfl
   . rw [hc];cases evE env a with
     | inl c1 => cases c1 <;> cases c <;> rfl
     | inr _ => cases c <;> rfl
 . simp only [heff,List.mem_cons,List.not_mem_nil,or_false] at hw
   subst hw
   have hhead : (gateAt C k).inputs.headD env.length=w:=by
    cases hin : (gateAt C k).inputs with
    | nil => simp [eIn,hop,hin] at heff
    | cons x xs =>
     simp [eIn,hop,hin] at heff
     simp [heff]
   simp only [sGt,hop,hhead,hc]
lemma scEx (n : ℕ) (l : Fin n) (b : Bool) (C : Circuit)
 (hfit : FanInTwo C)
 (hnc : ∃ x y : Fin n->Bool,
  circuitFun n C (update x l b)≠circuitFun n C (update y l b)) :
 ∃ (out' : ℕ),
  evE (sPfx n l b C.gates C.gates.length).2 C.output=Sum.inr out' ∧
  let D : Circuit:=⟨(sPfx n l b C.gates C.gates.length).1,out'⟩
  FanInTwo D ∧
  (∀ x : Fin n->Bool,circuitFun n D x=circuitFun n C (update x l b)) ∧
  D.size+((Finset.range C.gates.length).filter (fun j => isD n l b C j=true)).card =
   C.size:=by
 have hinv:=spInv n l b C hfit C.gates.length le_rfl
 have hOL : C.output < n+C.gates.length:=by
  by_contra hge
  obtain ⟨x,y,hxy⟩:=hnc
  apply hxy
  simp only [← wvO]
  rw [wireVal_ge n C _ _ (by omega),wireVal_ge n C _ _ (by omega)]
 cases hout : evE (sPfx n l b C.gates C.gates.length).2 C.output with
 | inl c =>
  exfalso
  obtain ⟨x,y,hxy⟩:=hnc
  have hx:=hinv.2.2 x C.output hOL
  have hy:=hinv.2.2 y C.output hOL
  rw [hout] at hx hy
  exact hxy (by simp only [← wvO];rw [hx,hy])
 | inr out' =>
  refine ⟨out',rfl,hinv.2.1,?_,?_⟩
  . intro x
    have hx:=hinv.2.2 x C.output hOL
    rw [hout] at hx
    exact hx.2
  . exact simplifyPrefix_size_add_deleted n l b C C.gates.length le_rfl
lemma length_eq_sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l,i ∈ S) :
 l.length=∑ w ∈ S,l.count w:=by
 induction l with
 | nil => simp
 | cons a l ih =>
  have ha : a ∈ S:=h a (by simp)
  have ih':=ih (fun i hi => h i (by simp [hi]))
  simp only [List.length_cons,List.count_cons,sum_add_distrib]
  rw [← ih']
  simp [ha]
lemma tree_card (n : ℕ) (C : Circuit) (G L : Finset ℕ) (ρ : ℕ)
 (h : IsOrTree n C G L ρ) : L.card=G.card+1:=by
 obtain ⟨hg,hl,hgg,hroot⟩:=h
 by_cases hG : G=∅
 . rw [if_pos hG] at hroot
   rw [hroot,hG]
   simp
 . rw [if_neg hG] at hroot
   obtain ⟨j0,hj0,hρ⟩:=hroot
   have hρL : ρ ∉ L:=by
    intro hin
    apply (hl ρ hin).1
    rw [hρ]
    exact ⟨Nat.le_add_right _ _,by simpa using hj0⟩
   have hdisj : Disjoint L (G.image (fun k => n+k)):=by
    rw [disjoint_left]
    intro w hw hw'
    obtain ⟨k,hk,rfl⟩:=mem_image.mp hw'
    apply (hl _ hw).1
    exact ⟨Nat.le_add_right _ _,by simpa using hk⟩
   have hsum : ∑ j ∈ G,(gateAt C j).inputs.length=2 * G.card:=by
    rw [sum_congr rfl (fun j hj => (hg j hj).2.1)]
    simp [Nat.mul_comm]
   have hlen : ∀ j ∈ G,(gateAt C j).inputs.length
    = ∑ w ∈ L ∪ G.image (fun k => n+k),(gateAt C j).inputs.count w:=by
    intro j hj
    apply length_eq_sum_count
    intro i hi
    rcases (hg j hj).2.2 i hi with h1 | ⟨h1,h2⟩
    . exact mem_union_left _ h1
    . apply mem_union_right
      exact mem_image.mpr ⟨i - n,h2,by omega⟩
   have h1 : ∑ j ∈ G,(gateAt C j).inputs.length
    = ∑ w ∈ L ∪ G.image (fun k => n+k),readsIn C G w:=by
    rw [sum_congr rfl hlen,Finset.sum_comm]
    rfl
   have h2 : ∑ w ∈ L,readsIn C G w=L.card:=by
    rw [sum_congr rfl (fun w hw => (hl w hw).2)]
    rw [sum_congr rfl (fun w hw => if_neg (fun (e : w=ρ) => hρL (e ▸ hw)))]
    simp
   have h3 : ∑ w ∈ G.image (fun k => n+k),readsIn C G w+1=G.card:=by
    rw [sum_image (fun a _ b _ hab => by omega)]
    rw [sum_congr rfl (fun k hk => hgg k hk)]
    have e : ∀ k ∈ G,(if n+k=ρ then 0 else 1)=(if k=j0 then 0 else 1):=by
     intro k _
     by_cases hk : k=j0
     . simp [hk,hρ]
     . have : n+k ≠ ρ:=by omega
       simp [hk,this]
    rw [sum_congr rfl e]
    rw [← Finset.add_sum_erase G _ hj0]
    rw [sum_congr rfl (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]
    simp only [if_true,sum_const,smul_eq_mul,Nat.mul_one,Nat.zero_add]
    have:=card_erase_add_one hj0
    omega
   rw [h1,Finset.sum_union hdisj,h2] at hsum
   omega
def OrStep (n : ℕ) (C : Circuit) (G : Finset ℕ) (u v : ℕ) : Prop :=
 ∃ j ∈ G,u=n+j/\v ∈ (gateAt C j).inputs
def OrReach (n : ℕ) (C : Circuit) (G : Finset ℕ) : ℕ->ℕ->Prop :=
 Relation.ReflTransGen (OrStep n C G)
lemma rInP (C : Circuit) (G : Finset ℕ) (w : ℕ) :
 0 < readsIn C G w↔∃ j ∈ G,w ∈ (gateAt C j).inputs:=by
 unfold readsIn
 rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
 constructor
 . rintro ⟨j,hj,hpos⟩
   exact ⟨j,hj,List.count_pos_iff.mp hpos⟩
 . rintro ⟨j,hj,hmem⟩
   exact ⟨j,hj,List.count_pos_iff.mpr hmem⟩
lemma orStep_lt {n : ℕ} {C : Circuit} {G : Finset ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 {u v : ℕ} (h : OrStep n C G u v) : v < u:=by
 obtain ⟨j,hj,rfl,hmem⟩:=h
 exact hrb j (hG j hj) v hmem
lemma orLe {n : ℕ} {C : Circuit} {G : Finset ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 {u v : ℕ} (h : OrReach n C G u v) : v<=u:=by
 induction h with
 | refl => exact le_rfl
 | tail _ hstep ih => exact le_trans (le_of_lt (orStep_lt hrb hG hstep)) ih
lemma osUP {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (ht : IsOrTree n C G L ρ) {u1 u2 v : ℕ}
 (h1 : OrStep n C G u1 v) (h2 : OrStep n C G u2 v) : u1=u2:=by
 obtain ⟨j1,hj1,rfl,hmem1⟩:=h1
 obtain ⟨j2,hj2,rfl,hmem2⟩:=h2
 have hv_reads : readsIn C G v<=1:=by
  rcases (ht.1 j1 hj1).2.2 v hmem1 with hvL | ⟨hvn,hvG⟩
  . rw [(ht.2.1 v hvL).2];split_ifs <;> omega
  . have hveq : n+(v - n)=v:=by omega
    have h:=ht.2.2.1 (v - n) hvG
    rw [hveq] at h;rw [h];split_ifs <;> omega
 by_contra hne
 have hjne : j1≠j2:=fun h => hne (by rw [h])
 have hge : (gateAt C j1).inputs.count v+(gateAt C j2).inputs.count v<=readsIn C G v:=by
  unfold readsIn
  have hsub : ({j1,j2} : Finset ℕ) ⊆ G:=by
   intro x hx;simp only [mem_insert,mem_singleton] at hx
   rcases hx with rfl | rfl <;> assumption
  have hle:=Finset.sum_le_sum_of_subset (f:=fun j => (gateAt C j).inputs.count v) hsub
  rw [Finset.sum_pair hjne] at hle
  exact hle
 have hc1 : 0 < (gateAt C j1).inputs.count v:=List.count_pos_iff.mpr hmem1
 have hc2 : 0 < (gateAt C j2).inputs.count v:=List.count_pos_iff.mpr hmem2
 omega
lemma otGIP {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (ht : IsOrTree n C G L ρ) {j : ℕ} (hj : j ∈ G) :
 ∃ a b : ℕ,(gateAt C j).inputs=[a,b]/\a≠b:=by
 have hlen:=(ht.1 j hj).2.1
 cases hin : (gateAt C j).inputs with
 | nil => simp [hin] at hlen
 | cons a rest =>
  cases rest with
  | nil => simp [hin] at hlen
  | cons b rest2 =>
   cases rest2 with
   | nil =>
    refine ⟨a,b,rfl,?_⟩
    intro hab;subst hab
    have hreads : readsIn C G a<=1:=by
     rcases (ht.1 j hj).2.2 a (by simp [hin]) with haL | ⟨han,haG⟩
     . rw [(ht.2.1 a haL).2];split_ifs <;> omega
     . have haeq : n+(a - n)=a:=by omega
       have h:=ht.2.2.1 (a - n) haG
       rw [haeq] at h;rw [h];split_ifs <;> omega
    have hge : 2<=readsIn C G a:=by
     unfold readsIn
     have hle:=Finset.single_le_sum (f:=fun k => (gateAt C k).inputs.count a)
      (fun _ _ => Nat.zero_le _) hj
     rw [hin] at hle;simp at hle;omega
    omega
   | cons _ _ => simp [hin] at hlen
lemma otRR {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {w : ℕ} (hw : w ∈ L\/(n<=w/\w - n ∈ G)) :
 OrReach n C G ρ w:=by
 by_cases hEq0 : w=ρ
 . subst hEq0;exact ReflTransGen.refl
 have hbound : w<=n+C.gates.length:=by
  rcases hw with hwL | ⟨hwn,hwG⟩
  . have hr : readsIn C G w=1:=by rw [(ht.2.1 w hwL).2,if_neg hEq0]
    obtain ⟨j,hj,hmem⟩:=(rInP C G w).mp (by omega)
    have:=hrb j (hG j hj) w hmem
    have:=hG j hj
    omega
  . have:=hG (w - n) hwG;omega
 clear hEq0
 generalize hk : n+C.gates.length - w=k
 induction k using Nat.strong_induction_on generalizing w with
 | ind k ih =>
  by_cases hEq : w=ρ
  . subst hEq;exact ReflTransGen.refl
  . have hr : readsIn C G w=1:=by
     rcases hw with hwL | ⟨hwn,hwG⟩
     . rw [(ht.2.1 w hwL).2,if_neg hEq]
     . have hweq : n+(w - n)=w:=by omega
       have h:=ht.2.2.1 (w - n) hwG
       rw [hweq] at h;rw [h,if_neg hEq]
    obtain ⟨j,hj,hmem⟩:=(rInP C G w).mp (by omega)
    have hlt : w < n+j:=hrb j (hG j hj) w hmem
    have hjlt:=hG j hj
    have hreach_j : OrReach n C G ρ (n+j) :=
     ih (n+C.gates.length - (n+j)) (by omega) (Or.inr ⟨by omega,by simpa using hj⟩)
      (by omega) rfl
    exact ReflTransGen.tail hreach_j ⟨j,hj,rfl,hmem⟩
lemma otER {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) {u v : ℕ}
 (hreach : OrReach n C G u v) (hv : wV n C x v=true) :
 wV n C x u=true:=by
 induction hreach with
 | refl => exact hv
 | tail h1 hstep ih =>
  apply ih
  obtain ⟨j,hj,rfl,hmem⟩:=hstep
  rw [wvGR n C hrb x j (hG j hj),(ht.1 j hj).1]
  simp only [GateOp.eval,List.any_eq_true]
  exact ⟨true,List.mem_map.mpr ⟨_,hmem,hv⟩,rfl⟩
lemma otEI {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) {u : ℕ}
 (hu : u ∈ L\/(n<=u/\u - n ∈ G)) :
 wV n C x u=true↔∃ l ∈ L,OrReach n C G u l/\wV n C x l=true:=by
 constructor
 . intro htrue
   induction u using Nat.strong_induction_on with
   | ind u ih =>
    rcases hu with huL | ⟨hun,huG⟩
    . exact ⟨u,huL,ReflTransGen.refl,htrue⟩
    . have hj : u - n < C.gates.length:=hG (u - n) huG
      have hueq : n+(u - n)=u:=by omega
      rw [← hueq,wvGR n C hrb x (u - n) hj,(ht.1 (u - n) huG).1] at htrue
      simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq] at htrue
      obtain ⟨_,⟨v,hvmem,hvt⟩,rfl⟩:=htrue
      have hvlt : v < u:=by have:=hrb (u - n) hj v hvmem;omega
      have hvnode : v ∈ L\/(n<=v/\v - n ∈ G):=(ht.1 (u - n) huG).2.2 v hvmem
      obtain ⟨l,hlL,hlreach,hlt⟩:=ih v hvlt hvnode hvt
      exact ⟨l,hlL,ReflTransGen.head ⟨u - n,huG,hueq.symm,hvmem⟩ hlreach,hlt⟩
 . rintro ⟨l,_,hreach,hlt⟩
   exact otER hrb hG ht x hreach hlt
lemma otRE {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) (x : Fin n->Bool) :
 wV n C x ρ=true↔∃ l ∈ L,wV n C x l=true:=by
 have hρnode : ρ ∈ L\/(n <= ρ /\ ρ - n ∈ G):=by
  by_cases hGe : G=∅
  . have h:=ht.2.2.2;rw [if_pos hGe] at h;left;rw [h];simp
  . have h:=ht.2.2.2;rw [if_neg hGe] at h
    obtain ⟨j,hj,rfl⟩:=h;right;exact ⟨by omega,by simpa using hj⟩
 rw [otEI hrb hG ht x hρnode]
 constructor
 . rintro ⟨l,hlL,_,hlt⟩;exact ⟨l,hlL,hlt⟩
 . rintro ⟨l,hlL,hlt⟩;exact ⟨l,hlL,otRR hrb hG ht (Or.inl hlL),hlt⟩
lemma otHL {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {u : ℕ} (hu : u ∈ L\/(n<=u/\u - n ∈ G)) :
 ∃ l ∈ L,OrReach n C G u l:=by
 induction u using Nat.strong_induction_on with
 | ind u ih =>
  rcases hu with huL | ⟨hun,huG⟩
  . exact ⟨u,huL,ReflTransGen.refl⟩
  . obtain ⟨a,b,hin,_⟩:=otGIP ht huG
    have hamem : a ∈ (gateAt C (u - n)).inputs:=by simp [hin]
    have halt : a < u:=by have:=hrb (u - n) (hG (u - n) huG) a hamem;omega
    have hanode:=(ht.1 (u - n) huG).2.2 a hamem
    obtain ⟨l,hlL,hlreach⟩:=ih a halt hanode
    exact ⟨l,hlL,ReflTransGen.head ⟨u - n,huG,by omega,hamem⟩ hlreach⟩
lemma orCCD {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (ht : IsOrTree n C G L ρ) {a b l : ℕ}
 (ha : OrReach n C G a l) (hb : OrReach n C G b l) :
 OrReach n C G a b\/OrReach n C G b a:=by
 induction ha with
 | refl => exact Or.inr hb
 | @tail c d hac hcd ih =>
  rcases ReflTransGen.cases_tail hb with rfl | ⟨e,hbe,hed⟩
  . exact Or.inl (ReflTransGen.tail hac hcd)
  . have hce : c=e:=osUP ht hcd hed
    subst hce
    exact ih hbe
lemma otCD {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {j a b l : ℕ} (hj : j ∈ G)
 (hin : (gateAt C j).inputs=[a,b]) (hab : a≠b)
 (ha : OrReach n C G a l) (hb : OrReach n C G b l) : False:=by
 have hstep_a : OrStep n C G (n+j) a:=⟨j,hj,rfl,by simp [hin]⟩
 have hstep_b : OrStep n C G (n+j) b:=⟨j,hj,rfl,by simp [hin]⟩
 rcases orCCD ht ha hb with h1 | h2
 . rcases ReflTransGen.cases_tail h1 with rfl | ⟨e,hae,heb⟩
   . exact hab rfl
   . have hje : n+j=e:=osUP ht hstep_b heb
     have hle : e<=a:=orLe hrb hG hae
     have halt : a < n+j:=orStep_lt hrb hG hstep_a
     omega
 . rcases ReflTransGen.cases_tail h2 with rfl | ⟨e,hbe,hea⟩
   . exact hab rfl
   . have hje : n+j=e:=osUP ht hstep_a hea
     have hle : e<=b:=orLe hrb hG hbe
     have hblt : b < n+j:=orStep_lt hrb hG hstep_b
     omega
lemma otGTL {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {j : ℕ} (hj : j ∈ G) :
 ∃ l1 ∈ L,∃ l2 ∈ L,l1≠l2/\OrReach n C G (n+j) l1/\OrReach n C G (n+j) l2:=by
 obtain ⟨a,b,hin,hab⟩:=otGIP ht hj
 have hamem : a ∈ (gateAt C j).inputs:=by simp [hin]
 have hbmem : b ∈ (gateAt C j).inputs:=by simp [hin]
 obtain ⟨l1,hl1,hr1⟩:=otHL hrb hG ht ((ht.1 j hj).2.2 a hamem)
 obtain ⟨l2,hl2,hr2⟩:=otHL hrb hG ht ((ht.1 j hj).2.2 b hbmem)
 have hne : l1≠l2:=fun heq => otCD hrb hG ht hj hin hab hr1 (heq ▸ hr2)
 exact ⟨l1,hl1,l2,hl2,hne,
  ReflTransGen.head ⟨j,hj,rfl,hamem⟩ hr1,
  ReflTransGen.head ⟨j,hj,rfl,hbmem⟩ hr2⟩
lemma orTree_proper_sub_missing_leaf {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {u : ℕ} (hu : u ∈ L\/(n<=u/\u - n ∈ G)) (hne : u ≠ ρ) :
 ∃ l ∈ L,¬ OrReach n C G u l:=by
 have hr : readsIn C G u=1:=by
  rcases hu with huL | ⟨hun,huG⟩
  . rw [(ht.2.1 u huL).2,if_neg hne]
  . have hueq : n+(u - n)=u:=by omega
    have h:=ht.2.2.1 (u - n) huG
    rw [hueq] at h;rw [h,if_neg hne]
 obtain ⟨j,hj,hmem⟩:=(rInP C G u).mp (by omega)
 obtain ⟨a,b,hin,hab⟩:=otGIP ht hj
 rw [hin] at hmem
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
 rcases hmem with rfl | rfl
 . obtain ⟨l,hlL,hrb_l⟩:=otHL hrb hG ht ((ht.1 j hj).2.2 b (by simp [hin]))
   exact ⟨l,hlL,fun hru => otCD hrb hG ht hj hin hab hru hrb_l⟩
 . obtain ⟨l,hlL,hra_l⟩:=otHL hrb hG ht ((ht.1 j hj).2.2 a (by simp [hin]))
   exact ⟨l,hlL,fun hru => otCD hrb hG ht hj hin hab hra_l hru⟩
lemma otELSS {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {u l0 : ℕ} (hu : u ∈ L\/(n<=u/\u - n ∈ G))
 (hsub : ∀ l ∈ L,OrReach n C G u l->l=l0) : u=l0:=by
 rcases hu with huL | ⟨hun,huG⟩
 . exact hsub u huL ReflTransGen.refl
 . exfalso
   obtain ⟨l1,hl1,l2,hl2,hne,hr1,hr2⟩:=otGTL hrb hG ht huG
   have hueq : n+(u - n)=u:=by omega
   rw [hueq] at hr1 hr2
   exact hne ((hsub l1 hl1 hr1).trans (hsub l2 hl2 hr2).symm)
lemma otGSP {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}
 (hrb : ReadsBack n C) (hG : ∀ j ∈ G,j < C.gates.length)
 (ht : IsOrTree n C G L ρ) {u l1 l2 : ℕ} (hu : u ∈ L\/(n<=u/\u - n ∈ G))
 (hl1 : l1 ∈ L) (hl2 : l2 ∈ L) (hne : l1≠l2)
 (hr1 : OrReach n C G u l1) (hr2 : OrReach n C G u l2)
 (hsub : ∀ l ∈ L,OrReach n C G u l->l=l1\/l=l2) :
 ∃ j ∈ G,u=n+j/\((gateAt C j).inputs=[l1,l2]\/(gateAt C j).inputs=[l2,l1]):=by
 rcases hu with huL | ⟨hun,huG⟩
 . exfalso
   have hno_step : ∀ v,¬ OrStep n C G u v:=by
    rintro v ⟨j,hj,rfl,_⟩
    exact (ht.2.1 (n+j) huL).1 ⟨by omega,by simpa using hj⟩
   rcases ReflTransGen.cases_head hr1 with rfl | ⟨v,hstep,_⟩
   . rcases ReflTransGen.cases_head hr2 with rfl | ⟨v,hstep,_⟩
     . exact hne rfl
     . exact hno_step v hstep
   . exact hno_step v hstep
 . have hueq : n+(u - n)=u:=by omega
   obtain ⟨a,b,hin,hab⟩:=otGIP ht huG
   have ha_node:=(ht.1 (u - n) huG).2.2 a (by simp [hin])
   have hb_node:=(ht.1 (u - n) huG).2.2 b (by simp [hin])
   obtain ⟨la,hlaL,hrala⟩:=otHL hrb hG ht ha_node
   obtain ⟨lb,hlbL,hrblb⟩:=otHL hrb hG ht hb_node
   have hstep_a : OrStep n C G u a:=⟨u - n,huG,hueq.symm,by simp [hin]⟩
   have hstep_b : OrStep n C G u b:=⟨u - n,huG,hueq.symm,by simp [hin]⟩
   have hula : OrReach n C G u la:=ReflTransGen.head hstep_a hrala
   have hulb : OrReach n C G u lb:=ReflTransGen.head hstep_b hrblb
   have hne_ab : la≠lb:=fun heq =>
    otCD hrb hG ht huG hin hab hrala (heq ▸ hrblb)
   have hsub_a : ∀ l ∈ L,OrReach n C G a l->l=la:=by
    intro l hlL hral
    have hul : OrReach n C G u l:=ReflTransGen.head hstep_a hral
    have hne_lb : l≠lb:=fun heq =>
     otCD hrb hG ht huG hin hab hral (heq ▸ hrblb)
    rcases hsub l hlL hul with h3 | h3 <;> rcases hsub la hlaL hula with h1 | h1 <;>
     rcases hsub lb hlbL hulb with h2 | h2 <;> omega
   have hsub_b : ∀ l ∈ L,OrReach n C G b l->l=lb:=by
    intro l hlL hrbl
    have hul : OrReach n C G u l:=ReflTransGen.head hstep_b hrbl
    have hne_la : l≠la:=fun heq =>
     otCD hrb hG ht huG hin hab hrala (heq ▸ hrbl)
    rcases hsub l hlL hul with h3 | h3 <;> rcases hsub la hlaL hula with h1 | h1 <;>
     rcases hsub lb hlbL hulb with h2 | h2 <;> omega
   have ha_eq : a=la:=otELSS hrb hG ht ha_node hsub_a
   have hb_eq : b=lb:=otELSS hrb hG ht hb_node hsub_b
   refine ⟨u - n,huG,hueq.symm,?_⟩
   rw [hin,ha_eq,hb_eq]
   rcases hsub la hlaL hula with rfl | rfl <;> rcases hsub lb hlbL hulb with rfl | rfl
   . exact absurd rfl hne_ab
   . exact Or.inl rfl
   . exact Or.inr rfl
   . exact absurd rfl hne_ab
def stepCentre (n : ℕ) (d : NCCData n) (w : List Bool) (g : Gate) : List Bool :=
 w ++ [decide ((d.role (w.length - n)).1=Kind.z) && g.inputs.any (fun i => w.getD i false)]
lemma foldl_stepCentre_length (n : ℕ) (d : NCCData n) (gs : List Gate) (w : List Bool) :
 (gs.foldl (stepCentre n d) w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih];simp [stepCentre];omega
lemma foldl_stepCentre_getD_lt (n : ℕ) (d : NCCData n) (gs : List Gate)
 (w : List Bool) (i : ℕ) (hi : i < w.length) :
 (gs.foldl (stepCentre n d) w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stepCentre n d w g).length:=by simp [stepCentre];omega
  rw [ih (stepCentre n d w g) hlt]
  simp [stepCentre,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma isCentred_input (n : ℕ) (C : Circuit) (d : NCCData n) (i : Fin n) :
 IsCentred n C d i.val↔i ∈ d.cover:=by
 unfold IsCentred centreFlags
 change (C.gates.foldl (stepCentre n d) (List.ofFn fun i : Fin n => decide (i ∈ d.cover))).getD i.val false=true↔_
 rw [foldl_stepCentre_getD_lt n d C.gates _ i.val (by simp)]
 simp [List.getD_eq_getElem?_getD]
lemma isCentred_gate (n : ℕ) (C : Circuit) (d : NCCData n) (hrb : ReadsBack n C)
 (j : ℕ) (hj : j < C.gates.length) :
 IsCentred n C d (n+j) ↔
  (d.role j).1=Kind.z/\∃ i ∈ (gateAt C j).inputs,IsCentred n C d i:=by
 obtain ⟨pre,post,gj,hgs,hpre_len,hget⟩:=split_gates C.gates j hj
 have hgj : gateAt C j=gj:=by rw [gateAt_eq_getElem C j hj,hget]
 let init:=List.ofFn fun i : Fin n => decide (i ∈ d.cover)
 let w0:=pre.foldl (stepCentre n d) init
 have hW0L : w0.length=n+j:=by
  simp [w0,foldl_stepCentre_length,init,hpre_len]
 have hval : (centreFlags n C d).getD (n+j) false =
  (decide ((d.role j).1=Kind.z) && gj.inputs.any fun i => w0.getD i false):=by
  unfold centreFlags
  change (C.gates.foldl (stepCentre n d) init).getD (n+j) false=_
  rw [hgs,List.foldl_append,List.foldl_cons]
  rw [foldl_stepCentre_getD_lt n d post (stepCentre n d w0 gj) (n+j) (by simp [stepCentre];omega)]
  simp [stepCentre,List.getD_eq_getElem?_getD,hW0L]
 unfold IsCentred
 rw [hval,hgj,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true]
 constructor
 . rintro ⟨hz,i,himem,hiw⟩
   refine ⟨hz,i,himem,?_⟩
   have hilt : i < n+j:=by rw [← hgj] at himem;exact hrb j hj i himem
   unfold centreFlags
   change (C.gates.foldl (stepCentre n d) init).getD i false=true
   rw [hgs,List.foldl_append,foldl_stepCentre_getD_lt n d (gj :: post) w0 i (by omega)]
   exact hiw
 . rintro ⟨hz,i,himem,hic⟩
   refine ⟨hz,i,himem,?_⟩
   have hilt : i < n+j:=by rw [← hgj] at himem;exact hrb j hj i himem
   unfold centreFlags at hic
   change (C.gates.foldl (stepCentre n d) init).getD i false=true at hic
   rw [hgs,List.foldl_append,foldl_stepCentre_getD_lt n d (gj :: post) w0 i (by omega)] at hic
   exact hic
lemma bwS {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
 {d : NCCData n} (hv : Valid n K A C d) (t : Fin n) (ht : t ∈ d.cover) :
 ∃ j < C.gates.length,d.bw t=n+j/\d.role j=(Kind.b,t.val):=by
 obtain ⟨j,hj,h1,h2,_⟩:=(hv.2.2.2.2.2.1 t ht).1
 exact ⟨j,hj,h1,h2⟩
lemma gatesOf_lt {n : ℕ} {d : NCCData n} {C : Circuit} {k : Kind} {t : ℕ} :
 ∀ j ∈ gatesOf d C k t,j < C.gates.length :=
 fun _ hj => mem_range.mp (mem_filter.mp hj).1
lemma topGates_lt {n : ℕ} {d : NCCData n} {C : Circuit} :
 ∀ j ∈ topGates d C,j < C.gates.length :=
 fun _ hj => mem_range.mp (mem_filter.mp hj).1
lemma icZIR {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d)
 {t : Fin n} (ht : t ∈ d.cover) {w : ℕ}
 (hw : w=t.val\/∃ j < C.gates.length,w=n+j/\d.role j=(Kind.z,t.val)) :
 IsCentred n C d w↔OrReach n C (gatesOf d C Kind.z t.val) w t.val:=by
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  rcases hw with rfl | ⟨j,hj,rfl,hrole⟩
  . constructor
    . intro _;exact ReflTransGen.refl
    . intro _;exact (isCentred_input n C d t).mpr ht
  . have hjG : j ∈ gatesOf d C Kind.z t.val :=
     mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩
    have hzt:=(hv.2.2.2.2.2.1 t ht).2.1
    rw [isCentred_gate n C d hv.1 j hj]
    constructor
    . rintro ⟨_,i,himem,hic⟩
      have hilt : i < n+j:=hv.1 j hj i himem
      rcases (hzt.1 j hjG).2.2 i himem with hiL | ⟨hin,hiG⟩
      . unfold zLeaves at hiL
        rcases mem_insert.mp hiL with rfl | hmem_img
        . exact ReflTransGen.single ⟨j,hjG,rfl,himem⟩
        . exfalso
          obtain ⟨s,hs,rfl⟩:=mem_image.mp hmem_img
          obtain ⟨js,hjs,hbw,hrs⟩:=bwS hv s (mem_filter.mp hs).1
          rw [hbw,isCentred_gate n C d hv.1 js hjs,hrs] at hic
          exact absurd hic.1 (by intro h;cases h)
      . have hi_lt : i - n < C.gates.length:=gatesOf_lt (i - n) hiG
        have hi_role : d.role (i - n)=(Kind.z,t.val):=(mem_filter.mp hiG).2
        have hri:=(ih i hilt (Or.inr ⟨i - n,hi_lt,by omega,hi_role⟩)).mp hic
        exact ReflTransGen.head ⟨j,hjG,rfl,himem⟩ hri
    . intro hreach
      refine ⟨by rw [hrole],?_⟩
      rcases ReflTransGen.cases_head hreach with heq | ⟨i,hstep,hri⟩
      . exfalso;have:=t.isLt;omega
      . obtain ⟨j',hj'G,hjeq,himem⟩:=hstep
        have hjj : j'=j:=by omega
        rw [hjj] at himem
        refine ⟨i,himem,?_⟩
        have hilt : i < n+j:=hv.1 j hj i himem
        rcases (hzt.1 j hjG).2.2 i himem with hiL | ⟨hin,hiG⟩
        . unfold zLeaves at hiL
          rcases mem_insert.mp hiL with rfl | hmem_img
          . exact (isCentred_input n C d t).mpr ht
          . exfalso
            obtain ⟨s,hs,rfl⟩:=mem_image.mp hmem_img
            obtain ⟨js,_,hbw,_⟩:=bwS hv s (mem_filter.mp hs).1
            have hno : ∀ v,¬ OrStep n C (gatesOf d C Kind.z t.val) (d.bw s) v:=by
             rintro v ⟨k,hkG,hkeq,_⟩
             have hkn : d.bw s - n=k:=by omega
             exact (hzt.2.1 (d.bw s) (mem_insert_of_mem hmem_img)).1
              ⟨by omega,hkn.symm ▸ hkG⟩
            rcases ReflTransGen.cases_head hri with heq2 | ⟨v,hs2,_⟩
            . have:=t.isLt;omega
            . exact hno v hs2
        . have hi_lt : i - n < C.gates.length:=gatesOf_lt (i - n) hiG
          have hi_role : d.role (i - n)=(Kind.z,t.val):=(mem_filter.mp hiG).2
          exact (ih i hilt (Or.inr ⟨i - n,hi_lt,by omega,hi_role⟩)).mpr hri
lemma lam_true_of_input {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d)
 {t r : Fin n} (ht : t ∈ d.cover) (hown : d.owns t r=true)
 (x : Fin n->Bool) (hxr : x r=true) :
 wV n C x (d.lam t r)=true:=by
 have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r hown
 unfold LamOK at hlam
 by_cases hr : r ∈ d.cover
 . rw [if_pos hr] at hlam
   have hreach:=(icZIR hv hr hlam.2.1).mp hlam.1
   exact otER hv.1 gatesOf_lt (hv.2.2.2.2.2.1 r hr).2.1 x hreach
    (by rw [wvI];exact hxr)
 . rw [if_neg hr] at hlam
   rw [hlam,wvI];exact hxr
lemma nccF2 {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) : FanInTwo C:=by
 intro g hg
 obtain ⟨j,hj,rfl⟩:=List.mem_iff_getElem.mp hg
 rw [← gateAt_eq_getElem C j hj]
 rcases hv.2.2.2.2.1 j hj with htop | ⟨t,ht,hrt,hrb⟩
 . have hjG : j ∈ topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,htop⟩
   have h:=hv.2.2.2.2.2.2.1 j hjG
   exact ⟨Or.inr (Or.inl h.1),by omega⟩
 . cases hk : (d.role j).1 with
   | top =>
    have hjG : j ∈ topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,hk⟩
    have h:=hv.2.2.2.2.2.2.1 j hjG
    exact ⟨Or.inr (Or.inl h.1),by omega⟩
   | z =>
    have hjG : j ∈ gatesOf d C Kind.z t.val :=
     mem_filter.mpr ⟨mem_range.mpr hj,Prod.ext hk hrt⟩
    have h:=(hv.2.2.2.2.2.1 t ht).2.1.1 j hjG
    exact ⟨Or.inr (Or.inl h.1),by omega⟩
   | o =>
    have hjG : j ∈ gatesOf d C Kind.o t.val :=
     mem_filter.mpr ⟨mem_range.mpr hj,Prod.ext hk hrt⟩
    have h:=(hv.2.2.2.2.2.1 t ht).2.2.1.1 j hjG
    exact ⟨Or.inr (Or.inl h.1),by omega⟩
   | b =>
    obtain ⟨j',hj',hbw',_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
    have hbw:=hrb hk
    have hjj : j=j':=by omega
    subst hjj
    refine ⟨Or.inl hop,?_⟩
    rcases hin with h | h <;> simp [h]
lemma bw_injOn {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)} {C : Circuit}
 {d : NCCData n} (hv : Valid n K A C d) (S : Finset (Fin n)) (hS : S ⊆ d.cover) :
 Set.InjOn d.bw (S : Set (Fin n)):=by
 intro s hs t ht h
 obtain ⟨j,_,h1,h2⟩:=bwS hv s (hS hs)
 obtain ⟨j',_,h1',h2'⟩:=bwS hv t (hS ht)
 have hj : j=j':=by omega
 subst hj
 rw [h2] at h2'
 exact Fin.ext (Prod.ext_iff.mp h2').2
lemma nccSz {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
 {A : Finset (Fin n)} {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
 C.size+1=A.card+K.edgeFinset.card+d.cover.card:=by
 have hzcard : ∀ t : Fin n,(zLeaves d t).card =
  (d.cover.filter (fun s => d.tie s=some t)).card+1:=by
  intro t;unfold zLeaves
  rw [card_insert_of_notMem,card_image_of_injOn (bw_injOn hv _ (Finset.filter_subset _ _))]
  intro hin;obtain ⟨s,hs,hst⟩:=mem_image.mp hin
  obtain ⟨j,_,h1,_⟩:=bwS hv s (mem_filter.mp hs).1
  have:=t.isLt;omega
 have htopcard : (topLeaves d A).card =
  A.card+(d.cover.filter (fun t => d.tie t=none)).card:=by
  unfold topLeaves
  rw [card_union_of_disjoint,card_image_of_injective _ Fin.val_injective,
   card_image_of_injOn (bw_injOn hv _ (Finset.filter_subset _ _))]
  rw [disjoint_left]
  intro w hw hw'
  obtain ⟨a,_,rfl⟩:=mem_image.mp hw
  obtain ⟨s,hs,hst⟩:=mem_image.mp hw'
  obtain ⟨j,_,h1,_⟩:=bwS hv s (mem_filter.mp hs).1
  have:=a.isLt;omega
 have hocard : ∀ t ∈ d.cover,(oLeaves d t).card =
  (Finset.univ.filter (fun r => d.owns t r=true)).card:=by
  intro t ht;unfold oLeaves
  apply card_image_of_injOn
  intro r hr r' hr' h
  have hr1 : d.owns t r=true:=(mem_filter.mp hr).2
  have hr1' : d.owns t r'=true:=(mem_filter.mp hr').2
  have key : ∀ q : Fin n,d.owns t q=true →
   d.lam t q=q.val\/∃ j,d.lam t q=n+j/\d.role j=(Kind.z,q.val):=by
   intro q hq
   have hl:=(hv.2.2.2.2.2.1 t ht).2.2.2 q hq
   unfold LamOK at hl;split_ifs at hl
   . rcases hl.2.1 with h1 | ⟨j,_,h1,h2⟩
     . exact Or.inl h1
     . exact Or.inr ⟨j,h1,h2⟩
   . exact Or.inl hl
  have hlt:=r.isLt;have hlt':=r'.isLt
  rcases key r hr1 with h1 | ⟨j,h1,h2⟩ <;> rcases key r' hr1' with h1' | ⟨j',h1',h2'⟩
  . exact Fin.ext (by omega)
  . omega
  . omega
  . have hj : j=j':=by omega
    subst hj;rw [h2] at h2';exact Fin.ext (Prod.ext_iff.mp h2').2
 have hbcard : ∀ t ∈ d.cover,(gatesOf d C Kind.b t.val).card=1:=by
  intro t ht
  obtain ⟨j,hj,h1,h2⟩:=bwS hv t ht
  rw [card_eq_one];refine ⟨j,?_⟩
  ext j';simp only [gatesOf,mem_filter,mem_range,mem_singleton]
  constructor
  . rintro ⟨hj',hr⟩
    rcases hv.2.2.2.2.1 j' hj' with htop | ⟨t',_,e1,e2⟩
    . rw [hr] at htop;simp at htop
    . rw [hr] at e1 e2;have : t'=t:=Fin.ext e1.symm;subst this
      have:=e2 rfl;omega
  . rintro rfl;exact ⟨hj,h2⟩
 have hsplit : C.gates.length=(topGates d C).card + ∑ t ∈ d.cover,
  ((gatesOf d C Kind.z t.val).card+(gatesOf d C Kind.o t.val).card +
   (gatesOf d C Kind.b t.val).card):=by
  have h0:=card_filter_add_card_filter_not
   (s:=Finset.range C.gates.length) (fun j => (d.role j).1=Kind.top)
  rw [Finset.card_range] at h0
  have hkeys : ∀ j ∈ (Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1=Kind.top),
   d.role j ∈ ({Kind.z,Kind.o,Kind.b} : Finset Kind) ×ˢ d.cover.image Fin.val:=by
   intro j hj;rw [mem_filter,mem_range] at hj
   rcases hv.2.2.2.2.1 j hj.1 with htop | ⟨t,ht,e1,_⟩
   . exact absurd htop hj.2
   . rw [Finset.mem_product];refine ⟨?_,mem_image.mpr ⟨t,ht,e1.symm⟩⟩
     have hne:=hj.2;generalize (d.role j).1=k at hne;cases k <;> simp at hne ⊢
  have h1:=Finset.card_eq_sum_card_fiberwise hkeys
  have hfib : ∀ k ∈ ({Kind.z,Kind.o,Kind.b} : Finset Kind) ×ˢ d.cover.image Fin.val,
   (((Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1=Kind.top)).filter
    (fun j => d.role j=k)).card=(gatesOf d C k.1 k.2).card:=by
   intro k hk;congr 1;ext j
   simp only [gatesOf,mem_filter,mem_range]
   constructor
   . rintro ⟨⟨hj,_⟩,hr⟩;exact ⟨hj,hr⟩
   . rintro ⟨hj,hr⟩;refine ⟨⟨hj,?_⟩,hr⟩
     rw [hr];have hk1:=(Finset.mem_product.mp hk).1
     intro e;simp only at e;rw [e] at hk1;simp at hk1
  rw [sum_congr rfl hfib,Finset.sum_product] at h1;dsimp only at h1
  have h2 : ∑ k ∈ ({Kind.z,Kind.o,Kind.b} : Finset Kind),∑ v ∈ d.cover.image Fin.val,
   (gatesOf d C k v).card=∑ t ∈ d.cover,((gatesOf d C Kind.z t.val).card +
    (gatesOf d C Kind.o t.val).card+(gatesOf d C Kind.b t.val).card):=by
   rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
   simp only [sum_image (fun a _ b _ h => Fin.val_injective h)]
   rw [← sum_add_distrib,← sum_add_distrib]
   apply sum_congr rfl;intro t _;omega
  have h3 : ((Finset.range C.gates.length).filter (fun j => (d.role j).1=Kind.top)).card =
   (topGates d C).card:=rfl
  omega
 have htie : d.cover.card=(d.cover.filter (fun t => d.tie t=none)).card +
  ∑ t ∈ d.cover,(d.cover.filter (fun s => d.tie s=some t)).card:=by
  have hkeys : ∀ s ∈ d.cover,d.tie s ∈ insert none (d.cover.image some):=by
   intro s _;cases hs : d.tie s with
   | none => simp
   | some t =>
    have h1:=(hv.2.2.2.1 s t hs).2
    have h2:=(hv.2.2.1.1 t s h1).2
    simp [h2]
  rw [Finset.card_eq_sum_card_fiberwise hkeys,Finset.sum_insert (by simp),
   sum_image (fun a _ b _ h => Option.some_injective _ h)]
 have howned : ∑ t ∈ d.cover,(Finset.univ.filter (fun r => d.owns t r=true)).card =
  K.edgeFinset.card:=by
  have hown:=hv.2.2.1
  have hP : ∀ p ∈ (Finset.univ.filter (fun p : Fin n × Fin n => d.owns p.1 p.2=true)),
   p.1 ∈ d.cover:=fun p hp => (hown.1 p.1 p.2 (mem_filter.mp hp).2).2
  have h1:=Finset.card_eq_sum_card_fiberwise hP
  have hfib : ∀ t ∈ d.cover,
   ((Finset.univ.filter (fun p : Fin n × Fin n => d.owns p.1 p.2=true)).filter
    (fun p => p.1=t)).card=(Finset.univ.filter (fun r => d.owns t r=true)).card:=by
   intro t _;symm
   apply Finset.card_bij (fun r _ => (t,r))
   . intro r hr;simp only [mem_filter,mem_univ,true_and] at hr ⊢;exact ⟨hr,trivial⟩
   . intro a _ b _ h;exact (Prod.ext_iff.mp h).2
   . rintro ⟨u,v⟩ hp;simp only [mem_filter,mem_univ,true_and] at hp
     obtain ⟨h1,h2⟩:=hp;subst h2;exact ⟨v,by simpa using h1,rfl⟩
  rw [sum_congr rfl hfib] at h1;rw [← h1]
  apply Finset.card_bij (fun p _ => s(p.1,p.2))
  . intro p hp;rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    exact (hown.1 p.1 p.2 (mem_filter.mp hp).2).1
  . rintro ⟨u,v⟩ hp ⟨u',v'⟩ hp' h
    have e1 : d.owns u v=true:=(mem_filter.mp hp).2
    have e2 : d.owns u' v'=true:=(mem_filter.mp hp').2
    rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
    . exact Prod.ext h1 h2
    . exfalso;simp only at h1 h2;subst h1;subst h2
      exact hown.2 u v (hown.1 u v e1).1 (by rw [e1,e2])
  . intro e he;induction e using Sym2.ind with
    | _ a b =>
     rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at he
     have hne:=hown.2 a b he
     cases hab : d.owns a b with
     | true => exact ⟨(a,b),by simp [hab],rfl⟩
     | false =>
      have hba : d.owns b a=true:=by
       rw [hab] at hne;cases h : d.owns b a with
       | true => rfl
       | false => exact absurd h.symm hne
      exact ⟨(b,a),by simp [hba],Sym2.eq_swap⟩
 have htop:=tree_card n C _ _ _ hv.2.2.2.2.2.2
 rw [htopcard] at htop
 have hper : ∀ u ∈ d.cover,(gatesOf d C Kind.z u.val).card+(gatesOf d C Kind.o u.val).card +
  (gatesOf d C Kind.b u.val).card =
  (d.cover.filter (fun s => d.tie s=some u)).card +
  (Finset.univ.filter (fun r => d.owns u r=true)).card:=by
  intro u hu
  have hz:=tree_card n C _ _ _ (hv.2.2.2.2.2.1 u hu).2.1
  have ho:=tree_card n C _ _ _ (hv.2.2.2.2.2.1 u hu).2.2.1
  rw [hzcard u] at hz;rw [hocard u hu] at ho
  have hb:=hbcard u hu
  omega
 rw [sum_congr rfl hper,sum_add_distrib,howned] at hsplit
 change C.gates.length+1=_
 omega
lemma term_eval_iff {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d)
 {t : Fin n} (ht : t ∈ d.cover) (x : Fin n->Bool) :
 wV n C x (d.bw t)=true ↔
  wV n C x (d.zroot t)=true/\wV n C x (d.oroot t)=true:=by
 obtain ⟨j,hj,hbw,_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
 rw [hbw,wvGR n C hv.1 x j hj,hop]
 rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval,and_comm]
lemma term_roots_lt_bw {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d)
 {t : Fin n} (ht : t ∈ d.cover) :
 d.zroot t < d.bw t/\d.oroot t < d.bw t:=by
 obtain ⟨j,hj,hbw,_,_,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
 rw [hbw]
 rcases hin with h | h
 . exact ⟨hv.1 j hj _ (by simp [h]),hv.1 j hj _ (by simp [h])⟩
 . exact ⟨hv.1 j hj _ (by simp [h]),hv.1 j hj _ (by simp [h])⟩
lemma bw_tie_lt {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d)
 {s t : Fin n} (htie : d.tie s=some t) : d.bw s < d.bw t:=by
 have hs : s ∈ d.cover:=(hv.2.2.2.1 s t htie).1
 have hown : d.owns t s=true:=(hv.2.2.2.1 s t htie).2
 have ht : t ∈ d.cover:=(hv.2.2.1.1 t s hown).2
 have hmem : d.bw s ∈ zLeaves d t :=
  mem_insert_of_mem (mem_image.mpr ⟨s,mem_filter.mpr ⟨hs,htie⟩,rfl⟩)
 have hreach:=otRR hv.1 gatesOf_lt (hv.2.2.2.2.2.1 t ht).2.1 (Or.inl hmem)
 have hle:=orLe hv.1 gatesOf_lt hreach
 have hlt:=(term_roots_lt_bw hv ht).1
 omega
lemma nccBS {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) (x : Fin n->Bool) :
 ∀ w : ℕ,∀ t ∈ d.cover,d.bw t=w->wV n C x w=true →
  ∃ u v : Fin n,K.Adj u v/\x u=true/\x v=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro t ht hbw htrue
  subst hbw
  obtain ⟨hz,ho⟩:=(term_eval_iff hv ht x).mp htrue
  obtain ⟨lz,hlzL,hlzt⟩:=(otRE hv.1 gatesOf_lt (hv.2.2.2.2.2.1 t ht).2.1 x).mp hz
  unfold zLeaves at hlzL
  rcases mem_insert.mp hlzL with rfl | hmem_img
  . rw [wvI] at hlzt
    obtain ⟨lo,hloL,hlot⟩:=(otRE hv.1 gatesOf_lt (hv.2.2.2.2.2.1 t ht).2.2.1 x).mp ho
    unfold oLeaves at hloL
    obtain ⟨r,hr,rfl⟩:=mem_image.mp hloL
    have hown : d.owns t r=true:=(mem_filter.mp hr).2
    have hadj : K.Adj t r:=(hv.2.2.1.1 t r hown).1
    have hlam_lt : d.lam t r < d.bw t:=by
     have hreach:=otRR hv.1 gatesOf_lt (hv.2.2.2.2.2.1 t ht).2.2.1 (Or.inl (mem_image.mpr ⟨r,hr,rfl⟩))
     have hle:=orLe hv.1 gatesOf_lt hreach
     have hlt:=(term_roots_lt_bw hv ht).2
     omega
    have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r hown
    unfold LamOK at hlam
    by_cases hrc : r ∈ d.cover
    . rw [if_pos hrc] at hlam
      have hnode : d.lam t r ∈ zLeaves d r ∨
       (n<=d.lam t r/\d.lam t r - n ∈ gatesOf d C Kind.z r.val):=by
       rcases hlam.2.1 with h1 | ⟨j,hj,h1,h2⟩
       . left;rw [h1];exact mem_insert_self _ _
       . right;refine ⟨by omega,?_⟩
         have : d.lam t r - n=j:=by omega
         rw [this];exact mem_filter.mpr ⟨mem_range.mpr hj,h2⟩
      obtain ⟨lr,hlrL,hlrreach,hlrt⟩:=(otEI hv.1 gatesOf_lt (hv.2.2.2.2.2.1 r hrc).2.1 x hnode).mp hlot
      unfold zLeaves at hlrL
      rcases mem_insert.mp hlrL with rfl | hmem_s
      . rw [wvI] at hlrt
        exact ⟨t,r,hadj,hlzt,hlrt⟩
      . obtain ⟨s,hs,rfl⟩:=mem_image.mp hmem_s
        have hle:=orLe hv.1 gatesOf_lt hlrreach
        exact ih (d.bw s) (by omega) s (mem_filter.mp hs).1 rfl hlrt
    . rw [if_neg hrc] at hlam
      rw [hlam,wvI] at hlot
      exact ⟨t,r,hadj,hlzt,hlot⟩
  . obtain ⟨s,hs,rfl⟩:=mem_image.mp hmem_img
    have htie : d.tie s=some t:=(mem_filter.mp hs).2
    exact ih (d.bw s) (bw_tie_lt hv htie) s (mem_filter.mp hs).1 rfl hlzt
lemma nccBC {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) (x : Fin n->Bool) :
 ∀ k : ℕ,∀ t ∈ d.cover,n+C.gates.length - d.bw t=k →
  wV n C x (d.bw t)=true->circuitFun n C x=true:=by
 intro k
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  intro t ht hk htrue
  cases htie : d.tie t with
  | none =>
   rw [← wvO,otRE hv.1 topGates_lt hv.2.2.2.2.2.2 x]
   exact ⟨d.bw t,mem_union_right _
    (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,htie⟩,rfl⟩),htrue⟩
  | some u =>
   have hown : d.owns u t=true:=(hv.2.2.2.1 t u htie).2
   have hu : u ∈ d.cover:=(hv.2.2.1.1 u t hown).2
   have hzu : wV n C x (d.zroot u)=true:=by
    rw [otRE hv.1 gatesOf_lt (hv.2.2.2.2.2.1 u hu).2.1 x]
    exact ⟨d.bw t,mem_insert_of_mem
     (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,htie⟩,rfl⟩),htrue⟩
   have hzt : wV n C x (d.zroot t)=true:=((term_eval_iff hv ht x).mp htrue).1
   have hLE : d.lam u t=d.zroot t:=by
    have hl:=(hv.2.2.2.2.2.1 u hu).2.2.2 t hown
    unfold LamOK at hl;rw [if_pos ht] at hl;exact hl.2.2 htie
   have hou : wV n C x (d.oroot u)=true:=by
    rw [otRE hv.1 gatesOf_lt (hv.2.2.2.2.2.1 u hu).2.2.1 x]
    refine ⟨d.lam u t,mem_image.mpr ⟨t,mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩,?_⟩
    rw [hLE];exact hzt
   have hbu : wV n C x (d.bw u)=true:=(term_eval_iff hv hu x).mpr ⟨hzu,hou⟩
   have hlt : d.bw t < d.bw u:=bw_tie_lt hv htie
   obtain ⟨ju,hju,hbwu,_⟩:=bwS hv u hu
   exact ih (n+C.gates.length - d.bw u) (by omega) u hu rfl hbu
lemma nccEv {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
 {A : Finset (Fin n)} {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
 circuitFun n C=graphFun K A:=by
 funext x
 apply Bool.eq_iff_iff.mpr
 simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
 constructor
 . intro hC
   rw [← wvO,otRE hv.1 topGates_lt hv.2.2.2.2.2.2 x] at hC
   obtain ⟨w,hwL,hwt⟩:=hC
   unfold topLeaves at hwL
   rcases mem_union.mp hwL with ha | ht
   . left
     obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
     rw [wvI] at hwt
     exact ⟨a,haA,hwt⟩
   . right
     obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
     exact nccBS hv x (d.bw t) t (mem_filter.mp htF).1 rfl hwt
 . rintro (⟨a,haA,hxa⟩ | ⟨u,v,hadj,hxu,hxv⟩)
   . rw [← wvO,otRE hv.1 topGates_lt hv.2.2.2.2.2.2 x]
     exact ⟨a.val,mem_union_left _ (mem_image.mpr ⟨a,haA,rfl⟩),
      by rw [wvI];exact hxa⟩
   . have hne:=hv.2.2.1.2 u v hadj
     have hcase : d.owns u v=true\/d.owns v u=true:=by
      cases h1 : d.owns u v <;> cases h2 : d.owns v u <;> simp_all
     have hrun : ∀ a b : Fin n,d.owns a b=true->x a=true->x b=true →
      circuitFun n C x=true:=by
      intro a b hown hxa hxb
      have ha : a ∈ d.cover:=(hv.2.2.1.1 a b hown).2
      have hza : wV n C x (d.zroot a)=true:=by
       rw [otRE hv.1 gatesOf_lt (hv.2.2.2.2.2.1 a ha).2.1 x]
       exact ⟨a.val,mem_insert_self _ _,by rw [wvI];exact hxa⟩
      have hoa : wV n C x (d.oroot a)=true:=by
       rw [otRE hv.1 gatesOf_lt (hv.2.2.2.2.2.1 a ha).2.2.1 x]
       exact ⟨d.lam a b,mem_image.mpr ⟨b,mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩,
        lam_true_of_input hv ha hown x hxb⟩
      have hba : wV n C x (d.bw a)=true:=(term_eval_iff hv ha x).mpr ⟨hza,hoa⟩
      exact nccBC hv x _ a ha rfl hba
     rcases hcase with huv | hvu
     . exact hrun u v huv hxu hxv
     . exact hrun v u hvu hxv hxu
lemma exists_min_cover {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] :
 ∃ T : Finset (Fin n),IsMinCover K T:=by
 classical
 let S : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun T => K.IsVertexCover (T : Set (Fin n)))
 have hne : S.Nonempty:=⟨Finset.univ,by simp [S,SimpleGraph.IsVertexCover]⟩
 obtain ⟨T,hTS,hmin⟩:=S.exists_min_image Finset.card hne
 refine ⟨T,(mem_filter.mp hTS).2,fun T' hT' => hmin T' (mem_filter.mpr ⟨mem_univ _,hT'⟩)⟩
def aoc (n : ℕ) (gs : List Gate) (cur : ℕ) : List ℕ->List Gate × ℕ
 | [] => (gs,cur)
 | w :: rest => aoc n (gs ++ [⟨.or,[cur,w]⟩]) (n+gs.length) rest
lemma appendOrChain_len (n : ℕ) (gs : List Gate) (cur : ℕ) (ws : List ℕ) :
 (aoc n gs cur ws).1.length=gs.length+ws.length:=by
 induction ws generalizing gs cur with
 | nil => simp [aoc]
 | cons w rest ih =>
  simp only [aoc,ih,List.length_append,List.length_cons,List.length_nil]
  omega
lemma appendOrChain_prefix (n : ℕ) (gs : List Gate) (cur : ℕ) (ws : List ℕ) :
 ∃ ext : List Gate,(aoc n gs cur ws).1=gs ++ ext:=by
 induction ws generalizing gs cur with
 | nil => exact ⟨[],by simp [aoc]⟩
 | cons w rest ih =>
  obtain ⟨ext,hext⟩:=ih (gs ++ [⟨.or,[cur,w]⟩]) (n+gs.length)
  exact ⟨⟨.or,[cur,w]⟩ :: ext,by simpa [aoc,List.append_assoc] using hext⟩
lemma iotAL {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ j w : ℕ}
 (ht : IsOrTree n C G L ρ) (hjG : j ∉ G) (hwL : w ∉ L) (hwG : ¬ (n<=w/\w - n ∈ G))
 (hρne : ρ ≠ n+j) (hwne : w≠n+j) (hρw : ρ ≠ w)
 (hgate : gateAt C j=⟨.or,[ρ,w]⟩)
 (hGne : ∀ k ∈ G,n+k≠w)
 (hLne : ∀ l ∈ L,l≠n+j) :
 IsOrTree n C (insert j G) (insert w L) (n+j):=by
 obtain ⟨hg,hl,hgg,hroot⟩:=ht
 have hρnode : ρ ∈ L\/(n <= ρ /\ ρ - n ∈ G):=by
  by_cases hGe : G=∅
  . rw [if_pos hGe] at hroot;left;rw [hroot];simp
  . rw [if_neg hGe] at hroot;obtain ⟨k,hk,rfl⟩:=hroot;right;exact ⟨by omega,by simpa using hk⟩
 have hRI : ∀ u : ℕ,readsIn C (insert j G) u =
  readsIn C G u+(if u=ρ then 1 else 0)+(if u=w then 1 else 0):=by
  intro u
  unfold readsIn
  rw [Finset.sum_insert hjG,hgate]
  simp only [List.count_cons,List.count_nil,beq_iff_eq]
  by_cases h1 : u=ρ
  . subst h1
    by_cases h2 : u=w
    . subst h2;simp;omega
    . have h2' : w≠u:=Ne.symm h2;simp [h2,h2'];omega
  . have h1' : ρ ≠ u:=Ne.symm h1
    by_cases h2 : u=w
    . subst h2;simp [h1,h1'];omega
    . have h2' : w≠u:=Ne.symm h2;simp [h1,h1',h2,h2']
 have hreads_w : readsIn C G w=0:=by
  unfold readsIn
  apply sum_eq_zero
  intro k hk
  rw [List.count_eq_zero]
  intro hmem
  rcases (hg k hk).2.2 w hmem with h1 | h2
  . exact hwL h1
  . exact hwG h2
 have hreads_nj : readsIn C G (n+j)=0:=by
  unfold readsIn
  apply sum_eq_zero
  intro k hk
  rw [List.count_eq_zero]
  intro hmem
  rcases (hg k hk).2.2 (n+j) hmem with h1 | ⟨_,h2⟩
  . exact hLne (n+j) h1 rfl
  . exact hjG (by simpa using h2)
 refine ⟨?_,?_,?_,?_⟩
 . intro k hk
   rcases mem_insert.mp hk with rfl | hkG
   . refine ⟨by rw [hgate],by rw [hgate];rfl,?_⟩
     intro i hi;rw [hgate] at hi
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
     rcases hi with rfl | rfl
     . rcases hρnode with h1 | ⟨h1,h2⟩
       . exact Or.inl (mem_insert_of_mem h1)
       . exact Or.inr ⟨h1,mem_insert_of_mem h2⟩
     . exact Or.inl (mem_insert_self _ _)
   . refine ⟨(hg k hkG).1,(hg k hkG).2.1,?_⟩
     intro i hi
     rcases (hg k hkG).2.2 i hi with h1 | ⟨h1,h2⟩
     . exact Or.inl (mem_insert_of_mem h1)
     . exact Or.inr ⟨h1,mem_insert_of_mem h2⟩
 . intro u hu
   rcases mem_insert.mp hu with rfl | huL
   . refine ⟨?_,?_⟩
     . rintro ⟨hun,huI⟩
       rcases mem_insert.mp huI with h1 | h2
       . omega
       . exact hwG ⟨hun,h2⟩
     . rw [hRI,hreads_w,if_neg hwne,if_neg hρw.symm,if_pos rfl]
   . refine ⟨?_,?_⟩
     . rintro ⟨hun,huI⟩
       rcases mem_insert.mp huI with h1 | h2
       . exact hLne u huL (by omega)
       . exact (hl u huL).1 ⟨hun,h2⟩
     . have hune_nj : u≠n+j:=hLne u huL
       have hune_w : u≠w:=fun h => hwL (h ▸ huL)
       rw [hRI,(hl u huL).2,if_neg hune_nj,if_neg hune_w]
       by_cases huρ : u=ρ <;> simp [huρ]
 . intro k hk
   rcases mem_insert.mp hk with rfl | hkG
   . rw [hRI,hreads_nj,if_pos rfl,if_neg hρne.symm,if_neg hwne.symm]
   . have hne_nj : n+k≠n+j:=by
      intro h
      have hkj : k=j:=by omega
      exact hjG (hkj ▸ hkG)
     have hne_w : n+k≠w:=hGne k hkG
     rw [hRI,hgg k hkG,if_neg hne_nj,if_neg hne_w]
     by_cases hkρ : n+k=ρ <;> simp [hkρ]
 . rw [if_neg (Finset.insert_ne_empty j G)]
   exact ⟨j,mem_insert_self _ _,rfl⟩
lemma aocS (n : ℕ) (gs0 : List Gate) (w0 : ℕ) (ws : List ℕ)
 (hnodup : (w0 :: ws).Nodup)
 (hlt : ∀ w ∈ w0 :: ws,w < n+gs0.length) :
 let res:=aoc n gs0 w0 ws
 (∀ k < ws.length,∀ i ∈ (gateAt ⟨res.1,0⟩ (gs0.length+k)).inputs,i < n+(gs0.length+k)) ∧
 res.2 < n+res.1.length ∧
 (∀ C : Circuit,(∀ k < ws.length,gateAt C (gs0.length+k)=gateAt ⟨res.1,0⟩ (gs0.length+k)) →
  IsOrTree n C ((Finset.range ws.length).image (fun k => gs0.length+k)) (w0 :: ws).toFinset res.2):=by
 have haux : ∀ (gs : List Gate) (cur : ℕ) (G L : Finset ℕ) (ws : List ℕ),
  gs0.length<=gs.length →
  (∀ w ∈ ws,w ∉ L)->ws.Nodup->(∀ w ∈ ws,w < n+gs0.length) →
  cur < n+gs.length->(∀ k ∈ G,gs0.length<=k/\k < gs.length) →
  (∀ l ∈ L,l < n+gs.length) →
  (∀ C : Circuit,(∀ k ∈ G,gateAt C k=gateAt ⟨gs,0⟩ k)->IsOrTree n C G L cur) →
  let res:=aoc n gs cur ws
  (∀ k < ws.length,∀ i ∈ (gateAt ⟨res.1,0⟩ (gs.length+k)).inputs,i < n+(gs.length+k)) ∧
  res.2 < n+res.1.length ∧
  (∀ C : Circuit,
   (∀ k ∈ G,gateAt C k=gateAt ⟨gs,0⟩ k) →
   (∀ k < ws.length,gateAt C (gs.length+k)=gateAt ⟨res.1,0⟩ (gs.length+k)) →
   IsOrTree n C (G ∪ (Finset.range ws.length).image (fun k => gs.length+k))
    (L ∪ ws.toFinset) res.2):=by
  intro gs cur G L ws
  induction ws generalizing gs cur G L with
  | nil =>
   intro _ _ _ _ hcur _ _ ht
   refine ⟨by simp,by simpa [aoc] using hcur,?_⟩
   intro C hG _
   simpa [aoc] using ht C hG
  | cons w rest ih =>
   intro hgs_ge hwL hnd hwlt hcur hGlt hLlt ht
   have hwL0 : w ∉ L:=hwL w (by simp)
   have hwlt0 : w < n+gs0.length:=hwlt w (by simp)
   have hnd_rest : rest.Nodup:=(List.nodup_cons.mp hnd).2
   have hw_not_rest : w ∉ rest:=(List.nodup_cons.mp hnd).1
   let gs1:=gs ++ [⟨.or,[cur,w]⟩]
   have hgs1_len : gs1.length=gs.length+1:=by simp [gs1]
   have hgate_new : gateAt ⟨gs1,0⟩ gs.length=⟨.or,[cur,w]⟩:=by
    simp [gateAt,gs1,List.getD_eq_getElem?_getD]
   have ht1 : ∀ C : Circuit,(∀ k ∈ insert gs.length G,gateAt C k=gateAt ⟨gs1,0⟩ k) →
    IsOrTree n C (insert gs.length G) (insert w L) (n+gs.length):=by
    intro C hC
    have hCG : ∀ k ∈ G,gateAt C k=gateAt ⟨gs,0⟩ k:=by
     intro k hk
     rw [hC k (mem_insert_of_mem hk)]
     have hklt:=(hGlt k hk).2
     simp [gateAt,gs1,List.getD_eq_getElem?_getD,List.getElem?_append_left hklt]
    have hCj : gateAt C gs.length=⟨.or,[cur,w]⟩:=by
     rw [hC gs.length (mem_insert_self _ _),hgate_new]
    exact iotAL (ht C hCG)
     (fun h => Nat.lt_irrefl _ (hGlt _ h).2)
     hwL0
     (fun ⟨h1,h2⟩ => by have:=(hGlt (w - n) h2).1;omega)
     (by omega) (by omega)
     (fun heq => by
      subst heq
      by_cases hGe : G=∅
      . have h:=(ht C hCG).2.2.2;rw [if_pos hGe] at h
        exact hwL0 (by rw [h];simp)
      . have h:=(ht C hCG).2.2.2;rw [if_neg hGe] at h
        obtain ⟨k,hk,hkeq⟩:=h
        have:=(hGlt k hk).1;omega)
     hCj
     (fun k hk heq => by have:=(hGlt k hk).1;omega)
     (fun l hl heq => by have:=hLlt l hl;omega)
   have hres_ih:=ih gs1 (n+gs.length) (insert gs.length G) (insert w L)
    (by omega)
    (fun u hu => by
     simp only [mem_insert,not_or]
     exact ⟨fun h => hw_not_rest (h ▸ hu),hwL u (by simp [hu])⟩)
    hnd_rest
    (fun u hu => hwlt u (by simp [hu]))
    (by omega)
    (fun k hk => by
     rcases mem_insert.mp hk with rfl | hkG
     . exact ⟨hgs_ge,by omega⟩
     . have:=hGlt k hkG;omega)
    (fun l hl => by
     rcases mem_insert.mp hl with rfl | hlL
     . omega
     . have:=hLlt l hlL;omega)
    ht1
   obtain ⟨hpref_ext,hpref_eq⟩:=appendOrChain_prefix n gs1 (n+gs.length) rest
   have hres_eq : aoc n gs cur (w :: rest)=aoc n gs1 (n+gs.length) rest:=rfl
   refine ⟨?_,?_,?_⟩
   . intro k hk
     cases k with
     | zero =>
      have hgat : gateAt ⟨(aoc n gs cur (w :: rest)).1,0⟩ (gs.length+0) =
       ⟨.or,[cur,w]⟩:=by
       rw [Nat.add_zero,hres_eq,hpref_eq]
       simp [gateAt,gs1,List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [gs1] : gs.length < gs1.length)]
      rw [hgat];intro i hi;simp at hi;rcases hi with rfl | rfl <;> omega
     | succ k' =>
      have hk' : k' < rest.length:=by simp at hk;omega
      have h1:=hres_ih.1 k' hk'
      have hidx : gs.length+(k'+1)=gs1.length+k':=by omega
      rw [hidx];exact h1
   . exact hres_ih.2.1
   . intro C hCG hCws
     have hC1 : ∀ k ∈ insert gs.length G,gateAt C k=gateAt ⟨gs1,0⟩ k:=by
      intro k hk
      rcases mem_insert.mp hk with rfl | hkG
      . have h0:=hCws 0 (by simp)
        rw [Nat.add_zero,hres_eq,hpref_eq] at h0
        rw [h0,hgate_new]
        simp [gateAt,gs1,List.getD_eq_getElem?_getD,
         List.getElem?_append_left (by simp [gs1] : gs.length < gs1.length)]
      . rw [hCG k hkG]
        have hklt:=(hGlt k hkG).2
        simp [gateAt,gs1,List.getD_eq_getElem?_getD,List.getElem?_append_left hklt]
     have hCrest : ∀ k < rest.length,gateAt C (gs1.length+k) =
      gateAt ⟨(aoc n gs1 (n+gs.length) rest).1,0⟩ (gs1.length+k):=by
      intro k hk
      have h:=hCws (k+1) (by simp;omega)
      have hidx : gs.length+(k+1)=gs1.length+k:=by omega
      rw [← hidx];exact h
     have htree:=hres_ih.2.2 C hC1 hCrest
     have hGeq : insert gs.length G ∪ (Finset.range rest.length).image (fun k => gs1.length+k) =
      G ∪ (Finset.range (w :: rest).length).image (fun k => gs.length+k):=by
      ext x;simp only [mem_union,mem_insert,mem_image,mem_range,
       List.length_cons]
      constructor
      . rintro ((rfl | hx) | ⟨k,hk,rfl⟩)
        . right;exact ⟨0,by omega,by omega⟩
        . left;exact hx
        . right;exact ⟨k+1,by omega,by omega⟩
      . rintro (hx | ⟨k,hk,rfl⟩)
        . left;right;exact hx
        . cases k with
          | zero => left;left;omega
          | succ k' => right;exact ⟨k',by omega,by omega⟩
     have hLeq : insert w L ∪ rest.toFinset=L ∪ (w :: rest).toFinset:=by
      ext x;simp [or_comm,or_left_comm]
     rw [hGeq,hLeq] at htree
     exact htree
 have hnd:=List.nodup_cons.mp hnodup
 have hbase:=haux gs0 w0 ∅ {w0} ws le_rfl
  (fun w hw => by simp;exact fun h => hnd.1 (h ▸ hw))
  hnd.2
  (fun w hw => hlt w (by simp [hw]))
  (hlt w0 (by simp))
  (by simp)
  (fun l hl => by simp at hl;subst hl;exact hlt l (by simp))
  (fun C _ => by simp [IsOrTree,readsIn])
 refine ⟨hbase.1,hbase.2.1,fun C hC => ?_⟩
 have ht:=hbase.2.2 C (by simp) hC
 have hLeq : ({w0} : Finset ℕ) ∪ ws.toFinset=(w0 :: ws).toFinset:=by
  ext x;simp
 simpa [hLeq] using ht
lemma exNcc {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
 (A : Finset (Fin n)) (hne : A.Nonempty\/∃ u v : Fin n,K.Adj u v) :
 ∃ C : Circuit,IsNestedCoverCircuit n K A C:=by
 obtain ⟨T,hTmin⟩:=exists_min_cover K
 let owns : Fin n->Fin n->Bool :=
  fun u v => decide (K.Adj u v/\u ∈ T/\(v ∉ T\/u.val < v.val))
 have hOwner : (∀ u v,owns u v=true->K.Adj u v/\u ∈ T) ∧
  (∀ u v,K.Adj u v->owns u v≠owns v u):=by
  refine ⟨fun u v h => by simp [owns] at h;exact ⟨h.1,h.2.1⟩,fun u v hadj => ?_⟩
  have hne_uv : u≠v:=hadj.ne
  have hval_ne : u.val≠v.val:=fun h => hne_uv (Fin.ext h)
  have hcov : u ∈ T\/v ∈ T:=hTmin.1 hadj
  by_cases hu : u ∈ T <;> by_cases hv : v ∈ T
  . by_cases hlt : u.val < v.val
    . have h1 : owns u v=true:=by simp only [owns,decide_eq_true_eq];exact ⟨hadj,hu,Or.inr hlt⟩
      have h2 : owns v u=false:=by simp only [owns,decide_eq_false_iff_not];intro ⟨_,_,h⟩;rcases h with h | h;exact h hu;omega
      rw [h1,h2];decide
    . have hgt : v.val < u.val:=by omega
      have h1 : owns u v=false:=by simp only [owns,decide_eq_false_iff_not];intro ⟨_,_,h⟩;rcases h with h | h;exact h hv;omega
      have h2 : owns v u=true:=by simp only [owns,decide_eq_true_eq];exact ⟨hadj.symm,hv,Or.inr hgt⟩
      rw [h1,h2];decide
  . have h1 : owns u v=true:=by simp [owns,hadj,hu,hv]
    have h2 : owns v u=false:=by simp [owns,hv]
    rw [h1,h2];decide
  . have h1 : owns u v=false:=by simp [owns,hu]
    have h2 : owns v u=true:=by simp [owns,hadj.symm,hv,hu]
    rw [h1,h2];decide
  . exact absurd hcov (by simp [hu,hv])
 have hown_ne : ∀ t ∈ T,(Finset.univ.filter (fun r => owns t r=true)).Nonempty:=by
  intro t ht
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hcov' : K.IsVertexCover ((T.erase t : Finset (Fin n)) : Set (Fin n)):=by
   intro u v hadj
   by_cases hut : u=t
   . subst hut
     have hnot : owns u v=false:=by
      cases h : owns u v
      . rfl
      . exfalso;have : v ∈ Finset.univ.filter (fun r => owns u r=true):=by simp [h]
        rw [hemp] at this;simp at this
     have hvu : owns v u=true:=by
      have hne:=hOwner.2 u v hadj;rw [hnot] at hne
      cases h : owns v u <;> simp_all
     right
     exact mem_erase.mpr ⟨hadj.ne.symm,(hOwner.1 v u hvu).2⟩
   . by_cases hvt : v=t
     . subst hvt
       have hnot : owns v u=false:=by
        cases h : owns v u
        . rfl
        . exfalso;have : u ∈ Finset.univ.filter (fun r => owns v r=true):=by simp [h]
          rw [hemp] at this;simp at this
       have huv : owns u v=true:=by
        have hne:=hOwner.2 v u hadj.symm;rw [hnot] at hne
        cases h : owns u v <;> simp_all
       left
       exact mem_erase.mpr ⟨hadj.ne,(hOwner.1 u v huv).2⟩
     . rcases hTmin.1 hadj with hu | hv
       . left;exact mem_erase.mpr ⟨hut,hu⟩
       . right;exact mem_erase.mpr ⟨hvt,hv⟩
  have hle:=hTmin.2 (T.erase t) hcov'
  have hcard:=card_erase_lt_of_mem ht
  omega
 let oList (t : Fin n) : List ℕ :=
  ((Finset.univ.filter (fun r => owns t r=true)).image Fin.val).toList
 have hoList_nd : ∀ t,(oList t).Nodup:=fun t => Finset.nodup_toList _
 have hoList_ne : ∀ t ∈ T,oList t ≠ []:=by
  intro t ht h
  exact (Finset.Nonempty.ne_empty (Finset.Nonempty.image (hown_ne t ht) Fin.val))
   (Finset.toList_eq_nil.mp h)
 have hoList_lt : ∀ t w,w ∈ oList t->w < n:=by
  intro t w hw
  simp only [oList,Finset.mem_toList,mem_image] at hw
  obtain ⟨r,_,rfl⟩:=hw;exact r.isLt
 let addVertex (st : List Gate × (ℕ->Kind × ℕ) × (Fin n->ℕ) × (Fin n->ℕ)) (t : Fin n) :
  List Gate × (ℕ->Kind × ℕ) × (Fin n->ℕ) × (Fin n->ℕ) :=
  let (gs,role,oroot,bw):=st
  let base:=gs.length
  match oList t with
  | [] => st
  | w0 :: ws =>
   let (gs1,orW):=aoc n gs w0 ws
   let bIdx:=gs1.length
   let gs2:=gs1 ++ [⟨.and,[t.val,orW]⟩]
   let role' (j : ℕ) : Kind × ℕ :=
    if base<=j/\j < bIdx then (Kind.o,t.val)
    else if j=bIdx then (Kind.b,t.val)
    else role j
   let oroot':=update oroot t orW
   let bw':=update bw t (n+bIdx)
   (gs2,role',oroot',bw')
 have hfold_inv : ∀ (ts : List (Fin n)),ts.Nodup->(∀ t ∈ ts,t ∈ T) →
  let st:=ts.foldl addVertex ([],fun _ => (Kind.top,0),fun _ => 0,fun _ => 0)
  let (gs,role,oroot,bw):=st
  (∀ j < gs.length,∀ i ∈ (gateAt ⟨gs,0⟩ j).inputs,i < n+j) ∧
  (∀ j < gs.length,∃ t ∈ ts,(role j).2=t.val ∧
   ((role j).1=Kind.o\/((role j).1=Kind.b/\bw t=n+j))) ∧
  (∀ t ∈ ts,
   ∃ j < gs.length,bw t=n+j/\role j=(Kind.b,t.val) ∧
    gateAt ⟨gs,0⟩ j=⟨.and,[t.val,oroot t]⟩ ∧
    oroot t < n+j) ∧
  (∀ t ∈ ts,∀ C : Circuit,
   (∀ j < gs.length,gateAt C j=gateAt ⟨gs,0⟩ j) →
   (∀ j,gs.length<=j->role j=(Kind.top,0)) →
   IsOrTree n C ((Finset.range gs.length).filter (fun j => role j=(Kind.o,t.val)))
    ((Finset.univ.filter (fun r => owns t r=true)).image Fin.val) (oroot t)) ∧
  (∀ j,gs.length<=j->role j=(Kind.top,0)):=by
  intro ts
  induction ts using List.reverseRecOn with
  | nil =>
   intro _ _
   refine ⟨by simp,by simp,by simp,by simp,fun _ _ => rfl⟩
  | append_singleton ts t ih =>
   intro hnd hsub
   have hnd_ts : ts.Nodup:=(List.nodup_append.mp hnd).1
   have ht_not : t ∉ ts:=fun h => (List.nodup_append.mp hnd).2.2 t h t (by simp) rfl
   have hsub_ts : ∀ s ∈ ts,s ∈ T:=fun s hs => hsub s (by simp [hs])
   have htT : t ∈ T:=hsub t (by simp)
   obtain ⟨hrb0,hroles0,hterm0,hor0,htail0⟩:=ih hnd_ts hsub_ts
   rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
   generalize hst0 : ts.foldl addVertex ([],fun _ => (Kind.top,0),fun _ => 0,fun _ => 0)=st0 at hrb0 hroles0 hterm0 hor0 htail0 ⊢
   rcases st0 with ⟨gs,role,oroot,bw⟩
   dsimp only at hrb0 hroles0 hterm0 hor0 htail0 ⊢
   have hne_o:=hoList_ne t htT
   cases ho : oList t with
   | nil => exact absurd ho hne_o
   | cons w0 ws =>
    simp only [addVertex,ho]
    have hnd_o : (w0 :: ws).Nodup:=ho ▸ hoList_nd t
    have hlt_o : ∀ w ∈ w0 :: ws,w < n+gs.length:=fun w hw =>
     Nat.lt_of_lt_of_le (hoList_lt t w (ho ▸ hw)) (Nat.le_add_right _ _)
    have hchain:=aocS n gs w0 ws hnd_o hlt_o
    obtain ⟨ext,hext⟩:=appendOrChain_prefix n gs w0 ws
    have hlen1:=appendOrChain_len n gs w0 ws
    rcases hres1 : aoc n gs w0 ws with ⟨gs1,orW⟩
    rw [hres1] at hchain hext hlen1
    dsimp only at hchain hext hlen1 ⊢
    let bIdx:=gs1.length
    have hbIdx : bIdx=gs.length+ws.length:=hlen1
    let gs2:=gs1 ++ [⟨.and,[t.val,orW]⟩]
    let role' (j : ℕ) : Kind × ℕ :=
     if gs.length<=j/\j < bIdx then (Kind.o,t.val)
     else if j=bIdx then (Kind.b,t.val)
     else role j
    have hgs2_len : gs2.length=bIdx+1:=by simp [gs2,bIdx]
    have hgat_gs : ∀ j < gs.length,gateAt ⟨gs2,0⟩ j=gateAt ⟨gs,0⟩ j:=by
     intro j hj
     have h1 : j < gs1.length:=by omega
     simp [gateAt,gs2,List.getD_eq_getElem?_getD,List.getElem?_append_left h1,
      hext,List.getElem?_append_left hj]
    have hgat_ws : ∀ k < ws.length,gateAt ⟨gs2,0⟩ (gs.length+k)=gateAt ⟨gs1,0⟩ (gs.length+k):=by
     intro k hk
     have h1 : gs.length+k < gs1.length:=by omega
     simp [gateAt,gs2,List.getD_eq_getElem?_getD,List.getElem?_append_left h1]
    have hgat_b : gateAt ⟨gs2,0⟩ bIdx=⟨.and,[t.val,orW]⟩:=by
     simp [gateAt,gs2,bIdx,List.getD_eq_getElem?_getD]
    have hrole'_lt : ∀ j < gs.length,role' j=role j:=by
     intro j hj;simp only [role'];rw [if_neg (by omega),if_neg (by omega)]
    have hrole'_mid : ∀ j,gs.length<=j->j < bIdx->role' j=(Kind.o,t.val):=by
     intro j h1 h2;simp only [role'];rw [if_pos ⟨h1,h2⟩]
    have hrole'_b : role' bIdx=(Kind.b,t.val):=by
     simp [role']
    have hrole'_gt : ∀ j,gs2.length<=j->role' j=(Kind.top,0):=by
     intro j hj;simp only [role'];rw [if_neg (by omega),if_neg (by omega)];exact htail0 j (by omega)
    refine ⟨?_,?_,?_,?_,hrole'_gt⟩
    ·
     intro j hj i hi
     change j < gs2.length at hj
     by_cases h1 : j < gs.length
     . rw [hgat_gs j h1] at hi;exact hrb0 j h1 i hi
     . by_cases h2 : j < bIdx
       . have hk : j - gs.length < ws.length:=by omega
         have hjeq : gs.length+(j - gs.length)=j:=by omega
         rw [← hjeq,hgat_ws (j - gs.length) hk] at hi
         simpa [hjeq] using hchain.1 (j - gs.length) hk i hi
       . have hjeq : j=bIdx:=by omega
         subst hjeq;rw [hgat_b] at hi;simp at hi
         rcases hi with rfl | rfl
         . exact Nat.lt_of_lt_of_le t.isLt (Nat.le_add_right _ _)
         . exact hchain.2.1
    ·
     intro j hj
     change j < gs2.length at hj
     change ∃ s ∈ ts ++ [t],(role' j).2=s.val/\((role' j).1=Kind.o\/(role' j).1=Kind.b/\update bw t (n+bIdx) s=n+j)
     by_cases h1 : j < gs.length
     . rw [hrole'_lt j h1]
       obtain ⟨s,hs,h2,h3⟩:=hroles0 j h1
       have hne : s≠t:=fun h => ht_not (h ▸ hs)
       refine ⟨s,by simp [hs],h2,?_⟩
       rcases h3 with h3 | ⟨h3a,h3b⟩
       . exact Or.inl h3
       . exact Or.inr ⟨h3a,by simp [Function.update_of_ne hne,h3b]⟩
     . by_cases h2 : j < bIdx
       . refine ⟨t,by simp,by rw [hrole'_mid j (by omega) h2],Or.inl (by rw [hrole'_mid j (by omega) h2])⟩
       . have hjeq : j=bIdx:=by omega
         subst hjeq
         refine ⟨t,by simp,by rw [hrole'_b],Or.inr ⟨by rw [hrole'_b],by simp [Function.update_self]⟩⟩
    ·
     intro s hs
     simp only [List.mem_append,List.mem_singleton] at hs
     rcases hs with hs | rfl
     . have hne : s≠t:=fun h => ht_not (h ▸ hs)
       obtain ⟨j,hj,hbw,hrol,hgat,horlt⟩:=hterm0 s hs
       refine ⟨j,by show j < gs2.length;omega,by simp [Function.update_of_ne hne,hbw],
        by change role' j=(Kind.b,s.val);rw [hrole'_lt j hj,hrol],
        by change gateAt ⟨gs2,0⟩ j=_;rw [hgat_gs j hj,hgat,Function.update_of_ne hne],
        by simp [Function.update_of_ne hne,horlt]⟩
     . refine ⟨bIdx,by show bIdx < gs2.length;omega,by simp [bIdx],hrole'_b,
        by change gateAt ⟨gs2,0⟩ bIdx=_;rw [hgat_b,Function.update_self],
        by rw [Function.update_self];exact hchain.2.1⟩
    ·
     intro s hs C hC _
     simp only [List.mem_append,List.mem_singleton] at hs
     rcases hs with hs | rfl
     . have hne : s≠t:=fun h => ht_not (h ▸ hs)
       have hC0 : ∀ j < gs.length,gateAt C j=gateAt ⟨gs,0⟩ j:=fun j hj => by
        rw [hC j (by show j < gs2.length;omega),hgat_gs j hj]
       have hfilt : (Finset.range gs2.length).filter (fun j => role' j=(Kind.o,s.val)) =
        (Finset.range gs.length).filter (fun j => role j=(Kind.o,s.val)):=by
        ext j;simp only [mem_filter,mem_range]
        constructor
        . rintro ⟨hj,hr⟩
          by_cases h1 : j < gs.length
          . rw [hrole'_lt j h1] at hr;exact ⟨h1,hr⟩
          . by_cases h2 : j < bIdx
            . rw [hrole'_mid j (by omega) h2] at hr
              exact absurd (Fin.ext (Prod.ext_iff.mp hr).2.symm) hne
            . have : j=bIdx:=by omega
              subst this;rw [hrole'_b] at hr;cases hr
        . rintro ⟨hj,hr⟩
          exact ⟨by omega,by rw [hrole'_lt j hj,hr]⟩
       change IsOrTree n C ((Finset.range gs2.length).filter (fun j => role' j=(Kind.o,s.val))) _ _
       rw [hfilt,Function.update_of_ne hne]
       exact hor0 s hs C hC0 htail0
     . have hfilt : (Finset.range gs2.length).filter (fun j => role' j=(Kind.o,s.val)) =
         (Finset.range ws.length).image (fun k => gs.length+k):=by
        ext j;simp only [mem_filter,mem_range,mem_image]
        constructor
        . rintro ⟨hj,hr⟩
          by_cases h1 : j < gs.length
          . rw [hrole'_lt j h1] at hr
            obtain ⟨u,hu,h2,_⟩:=hroles0 j h1
            rw [hr] at h2
            exact absurd (Fin.ext h2.symm) (fun h => ht_not (h ▸ hu))
          . by_cases h2 : j < bIdx
            . exact ⟨j - gs.length,by omega,by omega⟩
            . have : j=bIdx:=by omega
              subst this;rw [hrole'_b] at hr;cases hr
        . rintro ⟨k,hk,rfl⟩
          exact ⟨by omega,hrole'_mid (gs.length+k) (by omega) (by omega)⟩
       have hL : (w0 :: ws).toFinset=(Finset.univ.filter (fun r => owns s r=true)).image Fin.val:=by
        rw [← ho];exact Finset.toList_toFinset _
       change IsOrTree n C ((Finset.range gs2.length).filter (fun j => role' j=(Kind.o,s.val))) _ _
       rw [hfilt,Function.update_self,← hL]
       exact hchain.2.2 C (fun k hk => by rw [hC (gs.length+k) (by show gs.length+k < gs2.length;omega),hgat_ws k hk])
 obtain ⟨hrb_v,hroles_v,hterm_v,hor_v,htail_v⟩ :=
  hfold_inv T.toList (Finset.nodup_toList T) (fun t ht => Finset.mem_toList.mp ht)
 generalize hstv : T.toList.foldl addVertex ([],fun _ => (Kind.top,0),fun _ => 0,fun _ => 0)=stv at hrb_v hroles_v hterm_v hor_v htail_v
 rcases stv with ⟨gsV,roleV,orootV,bwV⟩
 dsimp only at hrb_v hroles_v hterm_v hor_v htail_v
 let topL : Finset ℕ:=A.image Fin.val ∪ T.image bwV
 have htopL_ne : topL.Nonempty:=by
  rcases hne with ⟨a,ha⟩ | ⟨u,v,hadj⟩
  . exact ⟨a.val,mem_union_left _ (mem_image.mpr ⟨a,ha,rfl⟩)⟩
  . rcases hTmin.1 hadj with hu | hv
    . exact ⟨bwV u,mem_union_right _ (mem_image.mpr ⟨u,hu,rfl⟩)⟩
    . exact ⟨bwV v,mem_union_right _ (mem_image.mpr ⟨v,hv,rfl⟩)⟩
 have htopList_ne : topL.toList ≠ []:=by
  simp [Finset.toList_eq_nil];exact Finset.Nonempty.ne_empty htopL_ne
 cases htl : topL.toList with
 | nil => exact absurd htl htopList_ne
 | cons tw0 tws =>
  have hnd_top : (tw0 :: tws).Nodup:=htl ▸ Finset.nodup_toList topL
  have hlt_top : ∀ w ∈ tw0 :: tws,w < n+gsV.length:=by
   intro w hw
   have hwL : w ∈ topL:=Finset.mem_toList.mp (htl ▸ hw)
   rcases mem_union.mp hwL with ha | ht
   . obtain ⟨a,_,rfl⟩:=mem_image.mp ha
     exact Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right _ _)
   . obtain ⟨t,htT,rfl⟩:=mem_image.mp ht
     obtain ⟨j,hj,hbw,_⟩:=hterm_v t (Finset.mem_toList.mpr htT)
     omega
  have htopChain:=aocS n gsV tw0 tws hnd_top hlt_top
  obtain ⟨extT,hextT⟩:=appendOrChain_prefix n gsV tw0 tws
  have hlenT:=appendOrChain_len n gsV tw0 tws
  rcases hresT : aoc n gsV tw0 tws with ⟨gsFinal,outW⟩
  rw [hresT] at htopChain hextT hlenT
  dsimp only at htopChain hextT hlenT
  let C : Circuit:=⟨gsFinal,outW⟩
  let d : NCCData n:={
   cover:=T
   owns:=owns
   tie:=fun _ => none
   role:=roleV
   bw:=bwV
   zroot:=fun t => t.val
   oroot:=orootV
   lam:=fun _ r => r.val
  }
  have hlenC : C.gates.length=gsV.length+tws.length:=hlenT
  have hgat_V : ∀ j < gsV.length,gateAt C j=gateAt ⟨gsV,0⟩ j:=fun j hj => by
   simp [C,gateAt,hextT,List.getD_eq_getElem?_getD,List.getElem?_append_left hj]
  refine ⟨C,d,?_,hTmin,hOwner,(fun s t h => by cases h),?_,?_,?_⟩
  ·
   intro j hj i hi
   by_cases h1 : j < gsV.length
   . rw [hgat_V j h1] at hi;exact hrb_v j h1 i hi
   . have hk : j - gsV.length < tws.length:=by omega
     have hjeq : gsV.length+(j - gsV.length)=j:=by omega
     rw [← hjeq] at hi
     simpa [hjeq,C] using htopChain.1 (j - gsV.length) hk i hi
  ·
   intro j hj
   by_cases h1 : j < gsV.length
   . obtain ⟨t,ht,h2,h3⟩:=hroles_v j h1
     right
     refine ⟨t,Finset.mem_toList.mp ht,h2,fun hb => ?_⟩
     rcases h3 with ho | ⟨_,hbw⟩
     . rw [ho] at hb;cases hb
     . exact hbw
   . left;change (roleV j).1=Kind.top;rw [htail_v j (by omega)]
  ·
   intro t ht
   have htt : t ∈ T.toList:=Finset.mem_toList.mpr ht
   obtain ⟨j,hj,hbw,hrol,hgat,_⟩:=hterm_v t htt
   have hz_empty : gatesOf d C Kind.z t.val=∅:=by
    ext k;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
    intro hk hr
    change roleV k=(Kind.z,t.val) at hr
    by_cases h1 : k < gsV.length
    . obtain ⟨_,_,_,h3⟩:=hroles_v k h1
      rcases h3 with ho | ⟨hb,_⟩
      . rw [hr] at ho;cases ho
      . rw [hr] at hb;cases hb
    . rw [htail_v k (by omega)] at hr;cases hr
   have hz_leaves : zLeaves d t={t.val}:=by
    ext x;simp [zLeaves,d]
   have ho_gates : gatesOf d C Kind.o t.val =
    (Finset.range gsV.length).filter (fun k => roleV k=(Kind.o,t.val)):=by
    ext k;simp only [gatesOf,mem_filter,mem_range,d]
    constructor
    . rintro ⟨hk,hr⟩
      by_cases h1 : k < gsV.length
      . exact ⟨h1,hr⟩
      . rw [htail_v k (by omega)] at hr;cases hr
    . rintro ⟨hk,hr⟩;exact ⟨by omega,hr⟩
   have ho_leaves : oLeaves d t=(Finset.univ.filter (fun r => owns t r=true)).image Fin.val:=rfl
   refine ⟨⟨j,by omega,hbw,hrol,by rw [hgat_V j hj,hgat],Or.inl (by rw [hgat_V j hj,hgat])⟩,
    ?_,?_,?_⟩
   . rw [hz_empty,hz_leaves];simp [IsOrTree,readsIn,d]
   . rw [ho_gates,ho_leaves];exact hor_v t htt C hgat_V htail_v
   . intro r _;unfold LamOK
     split_ifs with hr
     . exact ⟨(isCentred_input n C d r).mpr hr,Or.inl rfl,fun h => by cases h⟩
     . rfl
  ·
   have hTGs : topGates d C=(Finset.range tws.length).image (fun k => gsV.length+k):=by
    ext j;simp only [topGates,mem_filter,mem_range,mem_image,d]
    constructor
    . rintro ⟨hj,hr⟩
      by_cases h1 : j < gsV.length
      . obtain ⟨_,_,_,h3⟩:=hroles_v j h1
        rcases h3 with ho | ⟨hb,_⟩
        . rw [hr] at ho;cases ho
        . rw [hr] at hb;cases hb
      . exact ⟨j - gsV.length,by omega,by omega⟩
    . rintro ⟨k,hk,rfl⟩
      exact ⟨by omega,by rw [htail_v (gsV.length+k) (by omega)]⟩
   have hTLs : topLeaves d A=(tw0 :: tws).toFinset:=by
    rw [← htl,Finset.toList_toFinset]
    ext x;simp [topLeaves,topL,d]
   rw [hTGs,hTLs]
   exact htopChain.2.2 C (fun _ _ => rfl)
lemma gArith {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p) :
 l≠p/\p≠q/\l ∉ A/\p ∉ A/\q ∉ A ∧
 K.edgeFinset.card=K1.edgeFinset.card+1 ∧
 K1.edgeFinset.card=K2.edgeFinset.card+1 ∧
 (insert p A).card=A.card+1:=by
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 have hlp : l≠p:=hLPA.ne
 have hpq : p≠q:=hPQA.ne
 have hlA : l ∉ A:=fun h => hA l h p hLPA
 have hpA : p ∉ A:=fun h => hA p h q hPQA
 have hqA : q ∉ A:=fun h => hA q h p hPQA.symm
 have hE1 : K.edgeFinset=insert s(l,p) K1.edgeFinset:=by
  ext e;induction e using Sym2.ind with
  | _ u v =>
   simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,mem_insert,
    Sym2.eq_iff,hK1]
   constructor
   . intro huv
     by_cases hul : u=l
     . subst hul;left;left;exact ⟨rfl,(hl v).mp huv⟩
     . by_cases hvl : v=l
       . subst hvl;left;right;exact ⟨(hl u).mp huv.symm,rfl⟩
       . right;exact ⟨huv,hul,hvl⟩
   . rintro ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨huv,_,_⟩)
     . exact hLPA
     . exact hLPA.symm
     . exact huv
 have hlp_not_K1 : s(l,p) ∉ K1.edgeFinset:=by
  simp [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,hK1]
 have hE2 : K1.edgeFinset=insert s(p,q) K2.edgeFinset:=by
  ext e;induction e using Sym2.ind with
  | _ u v =>
   simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,mem_insert,
    Sym2.eq_iff,hK1,hK2]
   constructor
   . rintro ⟨huv,hul,hvl⟩
     by_cases hup : u=p
     . subst hup
       rcases (hp v).mp huv with rfl | rfl
       . exact absurd rfl hvl
       . left;left;exact ⟨rfl,rfl⟩
     . by_cases hvp : v=p
       . subst hvp
         rcases (hp u).mp huv.symm with rfl | rfl
         . exact absurd rfl hul
         . left;right;exact ⟨rfl,rfl⟩
       . right;exact ⟨huv,hul,hup,hvl,hvp⟩
   . rintro ((⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨huv,hul,_,hvl,_⟩)
     . exact ⟨hPQA,hlp.symm,hql⟩
     . exact ⟨hPQA.symm,hql,hlp.symm⟩
     . exact ⟨huv,hul,hvl⟩
 have hpq_not_K2 : s(p,q) ∉ K2.edgeFinset:=by
  simp [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,hK2]
 exact ⟨hlp,hpq,hlA,hpA,hqA,
  by rw [hE1,card_insert_of_notMem hlp_not_K1],
  by rw [hE2,card_insert_of_notMem hpq_not_K2],
  card_insert_of_notMem hpA⟩
lemma cArith {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (l p q : Fin n)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {T T1 T2 : Finset (Fin n)} (hT : IsMinCover K T) (hT1 : IsMinCover K1 T1) (hT2 : IsMinCover K2 T2) :
 T.card=T2.card+1/\T2.card<=T1.card/\T1.card<=T2.card+1:=by
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hlp : l≠p:=hLPA.ne
 have hp_not_T2 : p ∉ T2:=by
  intro hpT2
  have hcov : K2.IsVertexCover ((T2.erase p : Finset (Fin n)) : Set (Fin n)):=by
   intro u v huv
   have h:=(hK2 u v).mp huv
   rcases hT2.1 huv with hu | hv
   . exact Or.inl (mem_erase.mpr ⟨h.2.2.1,hu⟩)
   . exact Or.inr (mem_erase.mpr ⟨h.2.2.2.2,hv⟩)
  have:=hT2.2 (T2.erase p) hcov
  have:=card_erase_lt_of_mem hpT2
  omega
 have hT2p : K.IsVertexCover ((insert p T2 : Finset (Fin n)) : Set (Fin n)):=by
  intro u v huv
  by_cases hup : u=p
  . left;simp [hup]
  . by_cases hvp : v=p
    . right;simp [hvp]
    . have hul : u≠l:=fun h => hvp ((hl v).mp (h ▸ huv))
      have hvl : v≠l:=fun h => hup ((hl u).mp (h ▸ huv.symm))
      rcases hT2.1 ((hK2 u v).mpr ⟨huv,hul,hup,hvl,hvp⟩) with hu | hv
      . exact Or.inl (mem_insert_of_mem hu)
      . exact Or.inr (mem_insert_of_mem hv)
 have hT_le : T.card<=T2.card+1:=by
  have:=hT.2 (insert p T2) hT2p
  rw [card_insert_of_notMem hp_not_T2] at this;exact this
 have hT_hit : l ∈ T\/p ∈ T:=hT.1 hLPA
 have hT_sub_K2 : K2.IsVertexCover (((T.erase l).erase p : Finset (Fin n)) : Set (Fin n)):=by
  intro u v huv
  have h:=(hK2 u v).mp huv
  rcases hT.1 h.1 with hu | hv
  . left;exact mem_erase.mpr ⟨h.2.2.1,mem_erase.mpr ⟨h.2.1,hu⟩⟩
  . right;exact mem_erase.mpr ⟨h.2.2.2.2,mem_erase.mpr ⟨h.2.2.2.1,hv⟩⟩
 have hT2_le : T2.card<=((T.erase l).erase p).card:=hT2.2 _ hT_sub_K2
 have hT_ge : T2.card+1<=T.card:=by
  rcases hT_hit with hlT | hpT
  . have h1:=card_erase_lt_of_mem hlT
    have h2:=Finset.card_erase_le (s:=T.erase l) (a:=p)
    omega
  . have h1:=card_erase_lt_of_mem hpT
    have h2 : ((T.erase l).erase p).card<=(T.erase p).card :=
     card_le_card (fun x hx => by simp at hx ⊢;exact ⟨hx.1,hx.2.2⟩)
    omega
 have hT1_cov_K2 : K2.IsVertexCover (T1 : Set (Fin n)):=fun u v huv =>
  have h:=(hK2 u v).mp huv
  hT1.1 ((hK1 u v).mpr ⟨h.1,h.2.1,h.2.2.2.1⟩)
 have hT_cov_K1 : K1.IsVertexCover (T : Set (Fin n)):=fun u v huv =>
  hT.1 ((hK1 u v).mp huv).1
 have h21 : T2.card<=T1.card:=hT2.2 T1 hT1_cov_K2
 have h1T : T1.card<=T.card:=hT1.2 T hT_cov_K1
 omega
lemma gfUL {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p) :
 (∀ x : Fin n->Bool,graphFun K A (update x l true)=graphFun K2 (insert p A) x) ∧
 (∀ x : Fin n->Bool,graphFun K A (update x l false)=graphFun K1 A x):=by
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hlp : l≠p:=hLPA.ne
 have hlA : l ∉ A:=fun h => hA l h p hLPA
 constructor
 . intro x
   apply Bool.eq_iff_iff.mpr
   simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq,mem_insert]
   constructor
   . rintro (⟨a,ha,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩)
     . have hal : a≠l:=fun h => hlA (h ▸ ha)
       rw [Function.update_of_ne hal] at hxa
       exact Or.inl ⟨a,Or.inr ha,hxa⟩
     . by_cases hup : u=p
       . subst hup;rw [Function.update_of_ne hlp.symm] at hxu
         exact Or.inl ⟨u,Or.inl rfl,hxu⟩
       . by_cases hvp : v=p
         . subst hvp;rw [Function.update_of_ne hlp.symm] at hxv
           exact Or.inl ⟨v,Or.inl rfl,hxv⟩
         . have hul : u≠l:=fun h => hvp ((hl v).mp (h ▸ huv))
           have hvl : v≠l:=fun h => hup ((hl u).mp (h ▸ huv.symm))
           rw [Function.update_of_ne hul] at hxu
           rw [Function.update_of_ne hvl] at hxv
           exact Or.inr ⟨u,v,(hK2 u v).mpr ⟨huv,hul,hup,hvl,hvp⟩,hxu,hxv⟩
   . rintro (⟨a,rfl | ha,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩)
     . exact Or.inr ⟨l,a,hLPA,by simp,by simp [Function.update_of_ne hlp.symm,hxa]⟩
     . have hal : a≠l:=fun h => hlA (h ▸ ha)
       exact Or.inl ⟨a,ha,by simp [Function.update_of_ne hal,hxa]⟩
     . have h:=(hK2 u v).mp huv
       exact Or.inr ⟨u,v,h.1,by simp [Function.update_of_ne h.2.1,hxu],
        by simp [Function.update_of_ne h.2.2.2.1,hxv]⟩
 . intro x
   apply Bool.eq_iff_iff.mpr
   simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
   constructor
   . rintro (⟨a,ha,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩)
     . have hal : a≠l:=fun h => hlA (h ▸ ha)
       rw [Function.update_of_ne hal] at hxa
       exact Or.inl ⟨a,ha,hxa⟩
     . have hul : u≠l:=fun h => by subst h;simp at hxu
       have hvl : v≠l:=fun h => by subst h;simp at hxv
       rw [Function.update_of_ne hul] at hxu
       rw [Function.update_of_ne hvl] at hxv
       exact Or.inr ⟨u,v,(hK1 u v).mpr ⟨huv,hul,hvl⟩,hxu,hxv⟩
   . rintro (⟨a,ha,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩)
     . have hal : a≠l:=fun h => hlA (h ▸ ha)
       exact Or.inl ⟨a,ha,by simp [Function.update_of_ne hal,hxa]⟩
     . have h:=(hK1 u v).mp huv
       exact Or.inr ⟨u,v,h.1,by simp [Function.update_of_ne h.2.1,hxu],
        by simp [Function.update_of_ne h.2.2,hxv]⟩
lemma graphFun_nonconst_helpers {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p) :
 (∃ x y,graphFun K A x≠graphFun K A y) ∧
 (∃ x y,graphFun K1 A x≠graphFun K1 A y) ∧
 (∃ x y,graphFun K2 (insert p A) x≠graphFun K2 (insert p A) y):=by
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 have hlp : l≠p:=hLPA.ne
 have h0_K : graphFun K A (fun _ => false)=false:=by simp [graphFun]
 have h0_K1 : graphFun K1 A (fun _ => false)=false:=by simp [graphFun]
 have h0_K2 : graphFun K2 (insert p A) (fun _ => false)=false:=by simp [graphFun]
 have h1_K : graphFun K A (fun _ => true)=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨l,p,hLPA,trivial,trivial⟩
 have h1_K1 : graphFun K1 A (fun _ => true)=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨p,q,(hK1 p q).mpr ⟨hPQA,hlp.symm,hql⟩,trivial,trivial⟩
 have h1_K2 : graphFun K2 (insert p A) (fun _ => true)=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inl ⟨p,mem_insert_self _ _,trivial⟩
 exact ⟨⟨fun _ => false,fun _ => true,by rw [h0_K,h1_K];decide⟩,
  ⟨fun _ => false,fun _ => true,by rw [h0_K1,h1_K1];decide⟩,
  ⟨fun _ => false,fun _ => true,by rw [h0_K2,h1_K2];decide⟩⟩
lemma exGtRL {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
 (A : Finset (Fin n)) (l p : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 {C : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A) :
 ∃ j < C.gates.length,l.val ∈ eIn (gateAt C j):=by
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hlp : l≠p:=hLPA.ne
 have hpA : p ∉ A:=fun h => hA p h l hLPA.symm
 let x1 : Fin n->Bool:=fun i => decide (i=p)
 let x2 : Fin n->Bool:=update x1 l true
 have hf1 : graphFun K A x1=false:=by
  simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
  refine ⟨fun a ha hxa => hpA ((by simpa [x1] using hxa : a=p) ▸ ha),
   fun u v huv hxu hxv => ?_⟩
  have hu : u=p:=by simpa [x1] using hxu
  have hv : v=p:=by simpa [x1] using hxv
  subst hu;subst hv;exact huv.ne rfl
 have hf2 : graphFun K A x2=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨l,p,hLPA,by simp [x2],by simp [x2,x1,hlp.symm]⟩
 have hdiff : circuitFun n C x1≠circuitFun n C x2:=by rw [hfun,hf1,hf2];decide
 by_contra hnone
 push Not at hnone
 have hout_ne : C.output≠l.val:=by
  intro hout
  let xl : Fin n->Bool:=fun i => decide (i=l)
  have hfl : graphFun K A xl=false:=by
   simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
   refine ⟨fun a ha hxa => (hA a ha p) ((by simpa [xl] using hxa : a=l).symm ▸ hLPA),
    fun u v huv hxu hxv => ?_⟩
   have hu : u=l:=by simpa [xl] using hxu
   have hv : v=l:=by simpa [xl] using hxv
   subst hu;subst hv;exact huv.ne rfl
  have hcl : circuitFun n C xl=true:=by
   rw [← wvO,hout,wvI];simp [xl]
  rw [hfun,hfl] at hcl;cases hcl
 have hwires_eq : ∀ w,w≠l.val->wV n C x1 w=wV n C x2 w:=by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro hne
   by_cases hwn : w < n
   . let wf : Fin n:=⟨w,hwn⟩
     have hwfl : wf≠l:=fun h => hne (congrArg Fin.val h)
     change wV n C x1 wf.val=wV n C x2 wf.val
     rw [wvI,wvI]
     simp [x2,Function.update_of_ne hwfl]
   . by_cases hwg : w < n+C.gates.length
     . have hj : w - n < C.gates.length:=by omega
       have hweq : n+(w - n)=w:=by omega
       rw [← hweq,wireVal_gate n C x1 (w - n) hj,wireVal_gate n C x2 (w - n) hj,
        eval_eq_effInputs,eval_eq_effInputs]
       congr 1
       refine List.map_congr_left fun i hi => ?_
       have hil : i≠l.val:=fun h => hnone (w - n) hj (h ▸ hi)
       by_cases hilt : i < n+(w - n)
       . rw [if_pos hilt,if_pos hilt,ih i (by omega) hil]
       . rw [if_neg hilt,if_neg hilt]
     . rw [wireVal_ge n C x1 w (by omega),wireVal_ge n C x2 w (by omega)]
 exact hdiff (by rw [← wvO,← wvO];exact hwires_eq C.output hout_ne)
lemma minSzLB {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {s1 s2 : ℕ}
 (hs1 : ∀ D : Circuit,FanInTwo D->circuitFun n D=graphFun K1 A->s1<=D.size)
 (hs2 : ∀ D : Circuit,FanInTwo D->circuitFun n D=graphFun K2 (insert p A)->s2<=D.size)
 (hs21 : s2<=s1)
 {C : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A) :
 s2+2<=C.size:=by
 obtain ⟨hncK,hncK1,hncK2⟩:=graphFun_nonconst_helpers K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hncC : ∃ x y,circuitFun n C x≠circuitFun n C y:=by rw [hfun];exact hncK
 obtain ⟨hupdT,hupdF⟩:=gfUL K K1 K2 A l p q hA hl hp hK1 hK2
 have hex : ∃ j,j < C.gates.length/\l.val ∈ eIn (gateAt C j) :=
  exGtRL K A l p hA hl hmin hfun
 let j0:=Nat.find hex
 have hj0_spec : j0 < C.gates.length/\l.val ∈ eIn (gateAt C j0):=Nat.find_spec hex
 have hj0:=hj0_spec.1
 have hLJ0:=hj0_spec.2
 have hnc_updT : ∃ x y,circuitFun n C (update x l true) ≠
  circuitFun n C (update y l true):=by
  simp only [hfun,hupdT];exact hncK2
 have hnc_updF : ∃ x y,circuitFun n C (update x l false) ≠
  circuitFun n C (update y l false):=by
  simp only [hfun,hupdF];exact hncK1
 have hl_env : ∀ (b : Bool) (k : ℕ),k<=C.gates.length →
  evE (sPfx n l b C.gates k).2 l.val=Sum.inl b:=by
  intro b k hk
  rw [spEnvS n l b C (Nat.zero_le k) hk (by omega : l.val < n+0)]
  simp [simplifyPrefix_zero,simplifyInit,evE,List.getD_eq_getElem?_getD]
 have hnot_out_of_inl : ∀ (b : Bool) (hncb : ∃ x y,circuitFun n C (update x l b) ≠
  circuitFun n C (update y l b)) (c : Bool),
  evE (sPfx n l b C.gates (j0+1)).2 (n+j0)=Sum.inl c →
  j0+1 < C.gates.length:=by
  intro b hncb c hcj0
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj0
  have hout:=outLst hmin hncC hne_g
  by_contra hge
  have hjeq : j0+1=C.gates.length:=by omega
  have houteq : C.output=n+j0:=by omega
  obtain ⟨out',hout',_⟩:=scEx n l b C hmin.1 hncb
  rw [houteq,← hjeq,hcj0] at hout'
  cases hout'
 have htwo_del : ∀ (b : Bool) (hncb : ∃ x y,circuitFun n C (update x l b) ≠
  circuitFun n C (update y l b)) (c : Bool),
  evE (sPfx n l b C.gates (j0+1)).2 (n+j0)=Sum.inl c →
  2<=((Finset.range C.gates.length).filter (fun j => isD n l b C j=true)).card:=by
  intro b hncb c hcj0
  have hj0_del : isD n l b C j0=true :=
   deleted_of_inl_input n l b C hmin hncC hj0 hLJ0 (hl_env b j0 (by omega))
  have hj0_lt' : j0+1 < C.gates.length:=hnot_out_of_inl b hncb c hcj0
  obtain ⟨j1,hj1,hj01,hmem1⟩:=evGtR hmin hncC j0 hj0_lt'
  have hj1_env : evE (sPfx n l b C.gates j1).2 (n+j0)=Sum.inl c:=by
   rw [spEnvS n l b C (by omega : j0+1<=j1) (by omega) (by omega)]
   exact hcj0
  have hj1_del : isD n l b C j1=true :=
   deleted_of_inl_input n l b C hmin hncC hj1 hmem1 hj1_env
  have hsub : ({j0,j1} : Finset ℕ) ⊆
   (Finset.range C.gates.length).filter (fun j => isD n l b C j=true):=by
   intro x hx;simp only [mem_insert,mem_singleton] at hx
   rcases hx with rfl | rfl
   . exact mem_filter.mpr ⟨mem_range.mpr hj0,hj0_del⟩
   . exact mem_filter.mpr ⟨mem_range.mpr hj1,hj1_del⟩
  have hcard:=card_le_card hsub
  rw [Finset.card_pair (by omega)] at hcard
  exact hcard
 have hval_j0_step : ∀ (b : Bool) (st : List Gate × List (Bool ⊕ ℕ)),
  sPfx n l b C.gates j0=st →
  evE (sPfx n l b C.gates (j0+1)).2 (n+j0) =
  evE (sGt n st (gateAt C j0)).2 st.2.length:=by
  intro b st hst
  rw [simplifyPrefix_succ n l b C j0 hj0,hst]
  have hlen : st.2.length=n+j0:=by rw [← hst];exact simplifyPrefix_env_len n l b C j0 (by omega)
  rw [hlen]
 rcases minGS hmin hncC j0 hj0 with ⟨hop,a,b_in,hin,_,_,_⟩ |
  ⟨hop,a,b_in,hin,_,_,_⟩ | ⟨hop,a,heff,_⟩
 ·
  have hcj0 : evE (sPfx n l false C.gates (j0+1)).2 (n+j0)=Sum.inl false:=by
   rcases hst : sPfx n l false C.gates j0 with ⟨gs,env⟩
   rw [hval_j0_step false (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl false:=by
    have h:=hl_env false j0 (by omega);rw [hst] at h;exact h
   simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   simp only [sGt,hop,hin]
   rcases hLJ0 with rfl | rfl
   . rw [hl0];simp [evE,List.getD_eq_getElem?_getD]
   . rw [hl0];cases evE env a with
     | inl c1 => cases c1 <;> simp [evE,List.getD_eq_getElem?_getD]
     | inr _ => simp [evE,List.getD_eq_getElem?_getD]
  have h2:=htwo_del false hnc_updF false hcj0
  obtain ⟨out',_,hfitD,hfunD,hszD⟩:=scEx n l false C hmin.1 hnc_updF
  have hD_ge:=hs1 _ hfitD (funext fun x => by rw [hfunD x,hfun,hupdF])
  omega
 ·
  have hcj0 : evE (sPfx n l true C.gates (j0+1)).2 (n+j0)=Sum.inl true:=by
   rcases hst : sPfx n l true C.gates j0 with ⟨gs,env⟩
   rw [hval_j0_step true (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl true:=by
    have h:=hl_env true j0 (by omega);rw [hst] at h;exact h
   simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   simp only [sGt,hop,hin]
   rcases hLJ0 with rfl | rfl
   . rw [hl0];simp [evE,List.getD_eq_getElem?_getD]
   . rw [hl0];cases evE env a with
     | inl c1 => cases c1 <;> simp [evE,List.getD_eq_getElem?_getD]
     | inr _ => simp [evE,List.getD_eq_getElem?_getD]
  have h2:=htwo_del true hnc_updT true hcj0
  obtain ⟨out',_,hfitD,hfunD,hszD⟩:=scEx n l true C hmin.1 hnc_updT
  have hD_ge:=hs2 _ hfitD (funext fun x => by rw [hfunD x,hfun,hupdT])
  omega
 ·
  have hcj0 : evE (sPfx n l true C.gates (j0+1)).2 (n+j0)=Sum.inl false:=by
   rcases hst : sPfx n l true C.gates j0 with ⟨gs,env⟩
   rw [hval_j0_step true (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl true:=by
    have h:=hl_env true j0 (by omega);rw [hst] at h;exact h
   simp only [heff,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   subst hLJ0
   have hhead : (gateAt C j0).inputs.headD env.length=l.val:=by
    cases hin : (gateAt C j0).inputs with
    | nil => simp [eIn,hop,hin] at heff
    | cons x xs => simp [eIn,hop,hin] at heff;simp [heff]
   simp only [sGt,hop,hhead,hl0]
   simp [evE,List.getD_eq_getElem?_getD]
  have h2:=htwo_del true hnc_updT false hcj0
  obtain ⟨out',_,hfitD,hfunD,hszD⟩:=scEx n l true C hmin.1 hnc_updT
  have hD_ge:=hs2 _ hfitD (funext fun x => by rw [hfunD x,hfun,hupdT])
  omega
lemma exists_minimal_circuit (n : ℕ) (f : (Fin n->Bool)->Bool)
 (hex : ∃ C : Circuit,FanInTwo C/\circuitFun n C=f) :
 ∃ C : Circuit,IsMinimalCircuit n C/\circuitFun n C=f:=by
 let P : ℕ->Prop:=fun m => ∃ C : Circuit,FanInTwo C/\circuitFun n C=f/\C.size=m
 have hexP : ∃ m,P m:=by obtain ⟨C,h1,h2⟩:=hex;exact ⟨C.size,C,h1,h2,rfl⟩
 classical
 let m0:=Nat.find hexP
 obtain ⟨C0,hfit0,hfun0,hsz0⟩:=Nat.find_spec hexP
 refine ⟨C0,⟨hfit0,fun D hfitD hfunD => ?_⟩,hfun0⟩
 rw [hsz0]
 exact Nat.find_min' hexP ⟨D,hfitD,hfunD.trans hfun0,rfl⟩
lemma revDir {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 (h1 : ∀ C : Circuit,(IsMinimalCircuit n C/\circuitFun n C=graphFun K1 A)↔IsNestedCoverCircuit n K1 A C)
 (h2 : ∀ C : Circuit,(IsMinimalCircuit n C/\circuitFun n C=graphFun K2 (insert p A))↔IsNestedCoverCircuit n K2 (insert p A) C)
 {C : Circuit} (hC : IsNestedCoverCircuit n K A C) :
 IsMinimalCircuit n C/\circuitFun n C=graphFun K A:=by
 obtain ⟨d,hv⟩:=hC
 have hfunC:=nccEv hv
 have hfitC:=nccF2 hv
 have hszC:=nccSz hv
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 have hlp : l≠p:=hLPA.ne
 obtain ⟨C1,d1,hv1⟩:=exNcc K1 A (Or.inr ⟨p,q,(hK1 p q).mpr ⟨hPQA,hlp.symm,hql⟩⟩)
 obtain ⟨C2,d2,hv2⟩:=exNcc K2 (insert p A) (Or.inl ⟨p,mem_insert_self _ _⟩)
 have hmin1:=(h1 C1).mpr ⟨d1,hv1⟩
 have hmin2:=(h2 C2).mpr ⟨d2,hv2⟩
 have hsz1:=nccSz hv1
 have hsz2:=nccSz hv2
 obtain ⟨_,_,_,_,_,hEK1,hEK2,hAp⟩:=gArith K K1 K2 A l p q hA hl hql hp hK1 hK2
 obtain ⟨hcovK,hcov21,_⟩:=cArith K K1 K2 l p q hl hql hp hK1 hK2 hv.2.1 hv1.2.1 hv2.2.1
 have hs21 : C2.size<=C1.size:=by omega
 have hC_eq : C.size=C2.size+2:=by omega
 refine ⟨⟨hfitC,fun D hfitD hfunD => ?_⟩,hfunC⟩
 obtain ⟨D0,hminD0,hfunD0⟩:=exists_minimal_circuit n (graphFun K A) ⟨D,hfitD,hfunD.trans hfunC⟩
 have hlb:=minSzLB K K1 K2 A l p q hA hl hql hp hK1 hK2
  (fun E hE hEf => hmin1.1.2 E hE (hEf.trans hmin1.2.symm))
  (fun E hE hEf => hmin2.1.2 E hE (hEf.trans hmin2.2.symm))
  hs21 hminD0 hfunD0
 have hle0:=hminD0.2 D hfitD (hfunD.trans (hfunC.trans hfunD0.symm))
 omega
def iM (j0 j1 j : ℕ) : ℕ :=
 if j < j0 then j else if j < j1 then j - 1 else j - 2
def iI (j0 j1 j' : ℕ) : ℕ :=
 if j' < j0 then j' else if j'+1 < j1 then j'+1 else j'+2
def wM (n j0 j1 v' w : ℕ) : ℕ :=
 if w < n then w else if w=n+j1 then v' else n+iM j0 j1 (w - n)
def iW (n j0 j1 w' : ℕ) : ℕ :=
 if w' < n then w' else n+iI j0 j1 (w' - n)
lemma idxMap_invIdx {j0 j1 j' : ℕ} (hj01 : j0 < j1) :
 iM j0 j1 (iI j0 j1 j')=j':=by
 unfold iM iI;split_ifs <;> omega
lemma invIdx_idxMap {j0 j1 j : ℕ} (hj01 : j0 < j1) (hj0 : j≠j0) (hj1 : j≠j1) :
 iI j0 j1 (iM j0 j1 j)=j:=by
 unfold iM iI;split_ifs <;> omega
lemma invIdx_ne {j0 j1 j' : ℕ} (hj01 : j0 < j1) :
 iI j0 j1 j'≠j0/\iI j0 j1 j'≠j1:=by
 unfold iI;split_ifs <;> omega
lemma invIdx_lt {j0 j1 m j' : ℕ} (hj01 : j0 < j1) (hj1m : j1 < m) (hj' : j'+2 < m) :
 iI j0 j1 j' < m:=by
 unfold iI;split_ifs <;> omega
lemma iMLt {j0 j1 m j : ℕ} (hj01 : j0 < j1) (hj1m : j1 < m)
 (hjm : j < m) (hj0 : j≠j0) (hj1 : j≠j1) :
 iM j0 j1 j+2 < m:=by
 unfold iM;split_ifs <;> omega
lemma invIdx_strictMono {j0 j1 : ℕ} (hj01 : j0 < j1) {a b : ℕ} (hab : a < b) :
 iI j0 j1 a < iI j0 j1 b:=by
 unfold iI;split_ifs <;> omega
lemma invIdx_inj {j0 j1 : ℕ} (hj01 : j0 < j1) {a b : ℕ}
 (h : iI j0 j1 a=iI j0 j1 b) : a=b:=by
 have h1:=idxMap_invIdx (j':=a) hj01
 rw [h,idxMap_invIdx hj01] at h1
 exact h1.symm
lemma invWire_inj {n j0 j1 : ℕ} (hj01 : j0 < j1) {a b : ℕ}
 (h : iW n j0 j1 a=iW n j0 j1 b) : a=b:=by
 unfold iW at h
 by_cases ha : a < n <;> by_cases hb : b < n
 . rw [if_pos ha,if_pos hb] at h;exact h
 . rw [if_pos ha,if_neg hb] at h;omega
 . rw [if_neg ha,if_pos hb] at h;omega
 . rw [if_neg ha,if_neg hb] at h
   have heq : iI j0 j1 (a - n)=iI j0 j1 (b - n):=by omega
   have:=invIdx_inj hj01 heq
   omega
lemma wireMap_invWire {n j0 j1 v' w' : ℕ} (hj01 : j0 < j1) :
 wM n j0 j1 v' (iW n j0 j1 w')=w':=by
 unfold wM iW
 by_cases hw : w' < n
 . rw [if_pos hw,if_pos hw]
 . rw [if_neg hw,if_neg (by omega)]
   have hne:=(invIdx_ne (j':=w' - n) hj01).2
   rw [if_neg (by omega)]
   have hsub : n+iI j0 j1 (w' - n) - n=iI j0 j1 (w' - n):=by omega
   rw [hsub,idxMap_invIdx hj01];omega
lemma invWire_ne_j0_j1 {n j0 j1 w' : ℕ} (hj01 : j0 < j1) :
 iW n j0 j1 w'≠n+j0/\iW n j0 j1 w'≠n+j1:=by
 unfold iW
 by_cases hw : w' < n
 . rw [if_pos hw];omega
 . rw [if_neg hw];have h:=invIdx_ne (j':=w' - n) hj01;omega
lemma wMEq {n j0 j1 v' w w' : ℕ} (hj01 : j0 < j1)
 (hw_ne0 : w≠n+j0) :
 wM n j0 j1 v' w=w'↔(w=n+j1/\w'=v')\/(w≠n+j1/\w=iW n j0 j1 w'):=by
 constructor
 . intro heq
   by_cases h1 : w=n+j1
   . left;refine ⟨h1,?_⟩
     unfold wM at heq
     rw [h1,if_neg (by omega),if_pos rfl] at heq
     exact heq.symm
   . right;refine ⟨h1,?_⟩
     unfold wM at heq
     by_cases hwn : w < n
     . rw [if_pos hwn] at heq;subst heq;unfold iW;rw [if_pos hwn]
     . rw [if_neg hwn,if_neg h1] at heq;subst heq
       unfold iW;rw [if_neg (by omega)]
       have hsub : n+iM j0 j1 (w - n) - n=iM j0 j1 (w - n):=by omega
       rw [hsub,invIdx_idxMap hj01 (by omega) (by omega)];omega
 . rintro (⟨rfl,rfl⟩ | ⟨hne1,rfl⟩)
   . unfold wM;rw [if_neg (by omega),if_pos rfl]
   . exact wireMap_invWire hj01
lemma twoDS {n : ℕ} {l : Fin n} {b : Bool} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (hnc : ∃ x y,circuitFun n C x≠circuitFun n C y)
 {j0 j1 : ℕ} (hj01 : j0 < j1) (hj1 : j1 < C.gates.length)
 (hdel_set : (Finset.range C.gates.length).filter (fun j => isD n l b C j=true)={j0,j1})
 {c0 : Bool} (hj0_env : evE (sPfx n l b C.gates (j0+1)).2 (n+j0)=Sum.inl c0)
 {v' : ℕ} (hj1_env : evE (sPfx n l b C.gates (j1+1)).2 (n+j1)=Sum.inr v')
 {out' : ℕ} (hOEv : evE (sPfx n l b C.gates C.gates.length).2 C.output=Sum.inr out')
 (hno_not_D : ∀ g ∈ (sPfx n l b C.gates C.gates.length).1,g.op=.and\/g.op=.or) :
 let D : Circuit:=⟨(sPfx n l b C.gates C.gates.length).1,out'⟩
 D.gates.length+2=C.gates.length ∧
 (∀ w < n+C.gates.length,w≠l.val->w≠n+j0 →
  evE (sPfx n l b C.gates C.gates.length).2 w =
  Sum.inr (wM n j0 j1 v' w)) ∧
 (∀ j < C.gates.length,j≠j0->j≠j1 →
  (gateAt C j).op=(gateAt D (iM j0 j1 j)).op ∧
  (gateAt D (iM j0 j1 j)).inputs=(gateAt C j).inputs.map (wM n j0 j1 v') ∧
  (∀ i ∈ (gateAt C j).inputs,i < n+j/\i≠l.val/\i≠n+j0)) ∧
 (∀ j' < D.gates.length,
  (gateAt C (iI j0 j1 j')).op=(gateAt D j').op ∧
  (gateAt D j').inputs=(gateAt C (iI j0 j1 j')).inputs.map (wM n j0 j1 v')) ∧
 D.output=wM n j0 j1 v' C.output ∧
 (∀ x : Fin n->Bool,∀ w < n+C.gates.length,w≠l.val->w≠n+j0 →
  wV n C (update x l b) w=wV n D x (wM n j0 j1 v' w)):=by
 let D : Circuit:=⟨(sPfx n l b C.gates C.gates.length).1,out'⟩
 have hdel_iff : ∀ j < C.gates.length,isD n l b C j=true↔j=j0\/j=j1:=by
  intro j hj
  have hmem : j ∈ (Finset.range C.gates.length).filter (fun k => isD n l b C k=true) ↔
   j ∈ ({j0,j1} : Finset ℕ):=by rw [hdel_set]
  simpa [hj] using hmem
 have hsz_pref : ∀ k ≤ C.gates.length,
  (sPfx n l b C.gates k).1.length =
  if k<=j0 then k else if k<=j1 then k - 1 else k - 2:=by
  intro k hk
  have hsum:=simplifyPrefix_size_add_deleted n l b C k hk
  have hfilt : ((Finset.range k).filter (fun j => isD n l b C j=true)) =
   (Finset.range k) ∩ ({j0,j1} : Finset ℕ):=by
   ext j;simp only [mem_filter,Finset.mem_inter,mem_range,mem_insert,
    mem_singleton]
   constructor
   . rintro ⟨hjk,hd⟩;exact ⟨hjk,(hdel_iff j (by omega)).mp hd⟩
   . rintro ⟨hjk,h⟩;exact ⟨hjk,(hdel_iff j (by omega)).mpr h⟩
  rw [hfilt] at hsum
  by_cases h1 : k<=j0
  . have hemp : (Finset.range k) ∩ ({j0,j1} : Finset ℕ)=∅:=by
     ext j;simp;omega
    rw [hemp] at hsum;simp at hsum;rw [if_pos h1];omega
  . by_cases h2 : k<=j1
    . have hsgl : (Finset.range k) ∩ ({j0,j1} : Finset ℕ)={j0}:=by
       ext j;simp;omega
      rw [hsgl] at hsum;simp at hsum;rw [if_neg h1,if_pos h2];omega
    . have hpair : (Finset.range k) ∩ ({j0,j1} : Finset ℕ)={j0,j1}:=by
       ext j;simp;omega
      rw [hpair,Finset.card_pair (by omega)] at hsum;rw [if_neg h1,if_neg h2];omega
 have hD_len : D.gates.length+2=C.gates.length:=by
  have h:=hsz_pref C.gates.length le_rfl
  rw [if_neg (by omega),if_neg (by omega)] at h
  change (sPfx n l b C.gates C.gates.length).1.length+2=C.gates.length
  omega
 have hpref_gs : ∀ k1 k2,k1<=k2->k2<=C.gates.length →
  ∃ ext : List Gate,(sPfx n l b C.gates k2).1=(sPfx n l b C.gates k1).1 ++ ext:=by
  intro k1 k2 hk1 hk2
  induction k2 with
  | zero =>
   have hk10 : k1=0:=by omega
   subst hk10;exact ⟨[],by simp⟩
  | succ k2 ih =>
   by_cases h : k1=k2+1
   . subst h;exact ⟨[],by simp⟩
   . obtain ⟨ext1,hext1⟩:=ih (by omega) (by omega)
     rw [simplifyPrefix_succ n l b C k2 (by omega)]
     rcases hst : sPfx n l b C.gates k2 with ⟨gs,env⟩
     rw [hst] at hext1
     have hstep : ∃ ext2,(sGt n (gs,env) (gateAt C k2)).1=gs ++ ext2:=by
      simp only [sGt]
      repeat' (all_goals split)
      all_goals (dsimp only;first | exact ⟨[_],rfl⟩ | exact ⟨[],by simp⟩)
     obtain ⟨ext2,hext2⟩:=hstep
     dsimp only at hext1
     exact ⟨ext1 ++ ext2,by rw [hext2,hext1,List.append_assoc]⟩
 have hkept_step : ∀ j < C.gates.length,j≠j0->j≠j1 →
  evE (sPfx n l b C.gates (j+1)).2 (n+j)=Sum.inr (n+iM j0 j1 j) ∧
  (gateAt C j).op=(gateAt D (iM j0 j1 j)).op ∧
  (∃ a b_in a' b_in',
   (gateAt C j).inputs=[a,b_in]/\a < n+j/\b_in < n+j ∧
   evE (sPfx n l b C.gates j).2 a=Sum.inr a' ∧
   evE (sPfx n l b C.gates j).2 b_in=Sum.inr b_in' ∧
   (gateAt D (iM j0 j1 j)).inputs=[a',b_in']):=by
  intro j hj hj0 hj1_ne
  have hnotdel : isD n l b C j=false:=by
   cases h : isD n l b C j
   . rfl
   . exfalso;rcases (hdel_iff j hj).mp h with rfl | rfl <;> contradiction
  have hlen_k : (sPfx n l b C.gates j).1.length=iM j0 j1 j:=by
   rw [hsz_pref j (by omega)];unfold iM;split_ifs <;> omega
  have hlen_succ : (sPfx n l b C.gates (j+1)).1.length=iM j0 j1 j+1:=by
   rw [hsz_pref (j+1) (by omega)];unfold iM;split_ifs <;> omega
  have hlen_env : (sPfx n l b C.gates j).2.length=n+j :=
   simplifyPrefix_env_len n l b C j (by omega)
  obtain ⟨ext,hext⟩:=hpref_gs (j+1) C.gates.length (by omega) le_rfl
  have hgatD : ∀ g_new,(sPfx n l b C.gates (j+1)).1 =
   (sPfx n l b C.gates j).1 ++ [g_new] →
   gateAt D (iM j0 j1 j)=g_new:=by
   intro g_new hgs_eq
   have hIL : iM j0 j1 j < (sPfx n l b C.gates (j+1)).1.length:=by omega
   dsimp only [D,gateAt]
   rw [List.getD_eq_getElem?_getD,hext,List.getElem?_append_left hIL,hgs_eq,← hlen_k,
    List.getElem?_append_right le_rfl]
   simp
  have hne_len : (sPfx n l b C.gates (j+1)).1.length ≠
   (sPfx n l b C.gates j).1.length:=by omega
  rw [simplifyPrefix_succ n l b C j hj] at hne_len ⊢
  rcases hst : sPfx n l b C.gates j with ⟨gs,env⟩
  rw [hst] at hne_len hlen_k hlen_env
  have hD_step : ∀ g_new,(sGt n (gs,env) (gateAt C j)).1=gs ++ [g_new] →
   gateAt D (iM j0 j1 j)=g_new:=fun g_new h =>
   hgatD g_new (by rw [simplifyPrefix_succ n l b C j hj,hst,h])
  have hD_mem : ∀ g_new,(sGt n (gs,env) (gateAt C j)).1=gs ++ [g_new] →
   g_new ∈ D.gates:=by
   intro g_new h
   have heq:=hD_step g_new h
   have hlt : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj hj0 hj1_ne;omega
   rw [← heq,gateAt_eq_getElem D _ hlt];exact List.getElem_mem hlt
  rcases minGS hmin hnc j hj with ⟨hop,a,b_in,hin,ha,hb,_⟩ |
   ⟨hop,a,b_in,hin,ha,hb,_⟩ | ⟨hop,a,heff,_⟩
  ·
   simp only [sGt,hop,hin] at hne_len ⊢
   cases hae : evE env a with
   | inl c1 => cases c1 <;> simp [hae] at hne_len
   | inr u =>
    cases hbe : evE env b_in with
    | inl c2 => cases c2 <;> simp [hae,hbe] at hne_len
    | inr v =>
     by_cases huv : u=v
     . simp [hae,hbe,huv] at hne_len
     . have hgs_eq : (sGt n (gs,env) (gateAt C j)).1=gs ++ [⟨.and,[u,v]⟩]:=by
        simp [sGt,hop,hin,hae,hbe,huv]
       have hgd:=hD_step _ hgs_eq
       refine ⟨by simp [hae,hbe,huv,evE,List.getD_eq_getElem?_getD,hlen_env,hlen_k],
        by rw [hgd],a,b_in,u,v,rfl,ha,hb,
        hae,hbe,by rw [hgd]⟩
  ·
   simp only [sGt,hop,hin] at hne_len ⊢
   cases hae : evE env a with
   | inl c1 => cases c1 <;> simp [hae] at hne_len
   | inr u =>
    cases hbe : evE env b_in with
    | inl c2 => cases c2 <;> simp [hae,hbe] at hne_len
    | inr v =>
     by_cases huv : u=v
     . simp [hae,hbe,huv] at hne_len
     . have hgs_eq : (sGt n (gs,env) (gateAt C j)).1=gs ++ [⟨.or,[u,v]⟩]:=by
        simp [sGt,hop,hin,hae,hbe,huv]
       have hgd:=hD_step _ hgs_eq
       refine ⟨by simp [hae,hbe,huv,evE,List.getD_eq_getElem?_getD,hlen_env,hlen_k],
        by rw [hgd],a,b_in,u,v,rfl,ha,hb,
        hae,hbe,by rw [hgd]⟩
  ·
   exfalso
   simp only [sGt,hop] at hne_len
   cases hae : evE env ((gateAt C j).inputs.headD env.length) with
   | inl c => rw [hae] at hne_len;simp at hne_len
   | inr u =>
    have hgs_eq : (sGt n (gs,env) (gateAt C j)).1=gs ++ [⟨.not,[u]⟩]:=by
     simp only [sGt,hop];rw [hae]
    have hmem:=hD_mem ⟨.not,[u]⟩ hgs_eq
    rcases hno_not_D ⟨.not,[u]⟩ hmem with h | h <;> cases h
 have hWME : ∀ w < n+C.gates.length,w≠l.val->w≠n+j0 →
  evE (sPfx n l b C.gates C.gates.length).2 w =
  Sum.inr (wM n j0 j1 v' w):=by
  intro w hw hwl hw0
  by_cases hwn : w < n
  . rw [spEnvS n l b C (Nat.zero_le _) le_rfl (by omega : w < n+0)]
    let wf : Fin n:=⟨w,hwn⟩
    have hwfl : wf≠l:=fun h => hwl (congrArg Fin.val h)
    unfold wM;rw [if_pos hwn]
    simp [simplifyPrefix_zero,simplifyInit,evE,List.getD_eq_getElem?_getD,hwn,wf,hwfl]
  . by_cases hw1 : w=n+j1
    . subst hw1
      rw [spEnvS n l b C (by omega : j1+1<=C.gates.length) le_rfl (by omega)]
      rw [hj1_env];unfold wM;rw [if_neg (by omega),if_pos rfl]
    . have hj : w - n < C.gates.length:=by omega
      have hweq : n+(w - n)=w:=by omega
      rw [spEnvS n l b C (by omega : (w - n)+1<=C.gates.length) le_rfl (by omega)]
      have hstep_w:=(hkept_step (w - n) hj (by omega) (by omega)).1
      rw [hweq] at hstep_w
      rw [hstep_w]
      unfold wM;rw [if_neg (by omega),if_neg (by omega)]
 have hl_env_final : evE (sPfx n l b C.gates C.gates.length).2 l.val=Sum.inl b:=by
  rw [spEnvS n l b C (Nat.zero_le _) le_rfl (by omega : l.val < n+0)]
  simp [simplifyPrefix_zero,simplifyInit,evE,List.getD_eq_getElem?_getD]
 have hj0_env_final : evE (sPfx n l b C.gates C.gates.length).2 (n+j0)=Sum.inl c0:=by
  rw [spEnvS n l b C (by omega : j0+1<=C.gates.length) le_rfl (by omega)]
  exact hj0_env
 have hKF : ∀ j < C.gates.length,j≠j0->j≠j1 →
  (gateAt C j).op=(gateAt D (iM j0 j1 j)).op ∧
  (gateAt D (iM j0 j1 j)).inputs=(gateAt C j).inputs.map (wM n j0 j1 v') ∧
  (∀ i ∈ (gateAt C j).inputs,i < n+j/\i≠l.val/\i≠n+j0):=by
  intro j hj hj0 hj1_ne
  obtain ⟨_,hop,a,b_in,a',b_in',hin,ha,hb,hae,hbe,hDin⟩:=hkept_step j hj hj0 hj1_ne
  have ha_final : evE (sPfx n l b C.gates C.gates.length).2 a=Sum.inr a':=by
   rw [spEnvS n l b C (by omega : j<=C.gates.length) le_rfl ha,hae]
  have hb_final : evE (sPfx n l b C.gates C.gates.length).2 b_in=Sum.inr b_in':=by
   rw [spEnvS n l b C (by omega : j<=C.gates.length) le_rfl hb,hbe]
  have hal : a≠l.val:=fun h => by rw [h,hl_env_final] at ha_final;cases ha_final
  have ha0 : a≠n+j0:=fun h => by rw [h,hj0_env_final] at ha_final;cases ha_final
  have hbl : b_in≠l.val:=fun h => by rw [h,hl_env_final] at hb_final;cases hb_final
  have hb0 : b_in≠n+j0:=fun h => by rw [h,hj0_env_final] at hb_final;cases hb_final
  have ha'_eq : a'=wM n j0 j1 v' a:=by
   have h:=hWME a (by omega) hal ha0;rw [ha_final] at h;exact Sum.inr.inj h
  have hb'_eq : b_in'=wM n j0 j1 v' b_in:=by
   have h:=hWME b_in (by omega) hbl hb0;rw [hb_final] at h;exact Sum.inr.inj h
  refine ⟨hop,by rw [hDin,hin,ha'_eq,hb'_eq];rfl,?_⟩
  intro i hi;rw [hin] at hi;simp at hi
  rcases hi with rfl | rfl
  . exact ⟨ha,hal,ha0⟩
  . exact ⟨hb,hbl,hb0⟩
 have hIF : ∀ j' < D.gates.length,
  (gateAt C (iI j0 j1 j')).op=(gateAt D j').op ∧
  (gateAt D j').inputs=(gateAt C (iI j0 j1 j')).inputs.map (wM n j0 j1 v'):=by
  intro j' hj'
  have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
  have hne:=invIdx_ne (j':=j') hj01
  have h:=hKF (iI j0 j1 j') hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at h
  exact ⟨h.1,h.2.1⟩
 have hOE : D.output=wM n j0 j1 v' C.output:=by
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
  have hOL : C.output < n+C.gates.length:=by have:=outLst hmin hnc hne_g;omega
  have hout_ne_l : C.output≠l.val:=fun h => by rw [h,hl_env_final] at hOEv;cases hOEv
  have hout_ne_0 : C.output≠n+j0:=fun h => by rw [h,hj0_env_final] at hOEv;cases hOEv
  have h:=hWME C.output hOL hout_ne_l hout_ne_0
  rw [hOEv] at h
  exact Sum.inr.inj h
 have hval_eq : ∀ x : Fin n->Bool,∀ w < n+C.gates.length,w≠l.val->w≠n+j0 →
  wV n C (update x l b) w=wV n D x (wM n j0 j1 v' w):=by
  intro x w hw hwl hw0
  have hinv:=spInv n l b C hmin.1 C.gates.length le_rfl
  have hv:=hinv.2.2 x w hw
  rw [hWME w hw hwl hw0] at hv
  exact hv.2.symm
 exact ⟨hD_len,hWME,hKF,hIF,hOE,hval_eq⟩
lemma clsL {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {s1 s2 : ℕ}
 (hs1 : ∀ D : Circuit,FanInTwo D->circuitFun n D=graphFun K1 A->s1<=D.size)
 (hs2 : ∀ D : Circuit,FanInTwo D->circuitFun n D=graphFun K2 (insert p A)->s2<=D.size)
 (hs21 : s2<=s1)
 {C : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A)
 (hszC : C.size=s2+2) :
 ∃ j0 j1 : ℕ,j0 < j1/\j1 < C.gates.length ∧
  (∀ j < C.gates.length,j≠j0->l.val ∉ eIn (gateAt C j)) ∧
  (∀ j < C.gates.length,j≠j1->n+j0 ∉ eIn (gateAt C j)) ∧
  (
   (∃ u v v' out' : ℕ,
    (gateAt C j0).op=.or ∧
    ((gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val]) ∧
    u < n+j0/\u≠l.val ∧
    (gateAt C j1).op=.and ∧
    ((gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0]) ∧
    v < n+j1/\v≠n+j0/\v≠l.val ∧
    (Finset.range C.gates.length).filter (fun j => isD n l true C j=true)={j0,j1} ∧
    evE (sPfx n l true C.gates (j0+1)).2 (n+j0)=Sum.inl true ∧
    evE (sPfx n l true C.gates (j1+1)).2 (n+j1)=Sum.inr v' ∧
    evE (sPfx n l true C.gates C.gates.length).2 C.output=Sum.inr out' ∧
    let D : Circuit:=⟨(sPfx n l true C.gates C.gates.length).1,out'⟩
    FanInTwo D/\circuitFun n D=graphFun K2 (insert p A)/\D.size=s2)
   ∨
   (s1=s2/\∃ u v v' out' : ℕ,
    (gateAt C j0).op=.and ∧
    ((gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val]) ∧
    u < n+j0/\u≠l.val ∧
    (gateAt C j1).op=.or ∧
    ((gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0]) ∧
    v < n+j1/\v≠n+j0/\v≠l.val ∧
    (Finset.range C.gates.length).filter (fun j => isD n l false C j=true)={j0,j1} ∧
    evE (sPfx n l false C.gates (j0+1)).2 (n+j0)=Sum.inl false ∧
    evE (sPfx n l false C.gates (j1+1)).2 (n+j1)=Sum.inr v' ∧
    evE (sPfx n l false C.gates C.gates.length).2 C.output=Sum.inr out' ∧
    let D : Circuit:=⟨(sPfx n l false C.gates C.gates.length).1,out'⟩
    FanInTwo D/\circuitFun n D=graphFun K1 A/\D.size=s1)):=by
 obtain ⟨hncK,hncK1,hncK2⟩:=graphFun_nonconst_helpers K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hncC : ∃ x y,circuitFun n C x≠circuitFun n C y:=by rw [hfun];exact hncK
 obtain ⟨hupdT,hupdF⟩:=gfUL K K1 K2 A l p q hA hl hp hK1 hK2
 have hnc_updT : ∃ x y,circuitFun n C (update x l true) ≠
  circuitFun n C (update y l true):=by simp only [hfun,hupdT];exact hncK2
 have hnc_updF : ∃ x y,circuitFun n C (update x l false) ≠
  circuitFun n C (update y l false):=by simp only [hfun,hupdF];exact hncK1
 obtain ⟨outT,houtT,hfitT,hfunT,hszT⟩:=scEx n l true C hmin.1 hnc_updT
 obtain ⟨outF,houtF,hfitF,hfunF,hszF⟩:=scEx n l false C hmin.1 hnc_updF
 have hDT_ge : s2<=(sPfx n l true C.gates C.gates.length).1.length :=
  hs2 ⟨_,outT⟩ hfitT (funext fun x => by rw [hfunT x,hfun,hupdT])
 have hDF_ge : s1<=(sPfx n l false C.gates C.gates.length).1.length :=
  hs1 ⟨_,outF⟩ hfitF (funext fun x => by rw [hfunF x,hfun,hupdF])
 have hdelT_le : ((Finset.range C.gates.length).filter (fun j => isD n l true C j=true)).card<=2:=by
  change (sPfx n l true C.gates C.gates.length).1.length+_=C.size at hszT
  omega
 have hdelF_le : ((Finset.range C.gates.length).filter (fun j => isD n l false C j=true)).card<=2:=by
  change (sPfx n l false C.gates C.gates.length).1.length+_=C.size at hszF
  omega
 have hl_env : ∀ (b : Bool) (k : ℕ),k<=C.gates.length →
  evE (sPfx n l b C.gates k).2 l.val=Sum.inl b:=by
  intro b k hk
  rw [spEnvS n l b C (Nat.zero_le k) hk (by omega : l.val < n+0)]
  simp [simplifyPrefix_zero,simplifyInit,evE,List.getD_eq_getElem?_getD]
 have hnot_out_inl : ∀ (b : Bool) (j : ℕ) (c : Bool),j < C.gates.length →
  evE (sPfx n l b C.gates (j+1)).2 (n+j)=Sum.inl c →
  j+1 < C.gates.length:=by
  intro b j c hj hc
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj
  have hout:=outLst hmin hncC hne_g
  by_contra hge
  have hjeq : j+1=C.gates.length:=by omega
  have houteq : C.output=n+j:=by omega
  cases b with
  | true => rw [houteq,← hjeq,hc] at houtT;cases houtT
  | false => rw [houteq,← hjeq,hc] at houtF;cases houtF
 have hno_three_del : ∀ (b : Bool) (a1 a2 a3 : ℕ),
  a1 < C.gates.length->a2 < C.gates.length->a3 < C.gates.length →
  a1≠a2->a1≠a3->a2≠a3 →
  isD n l b C a1=true->isD n l b C a2=true->isD n l b C a3=true->False:=by
  intro b a1 a2 a3 h1 h2 h3 h12 h13 h23 hd1 hd2 hd3
  have hsub : ({a1,a2,a3} : Finset ℕ) ⊆
   (Finset.range C.gates.length).filter (fun j => isD n l b C j=true):=by
   intro x hx;simp only [mem_insert,mem_singleton] at hx
   rcases hx with rfl | rfl | rfl
   . exact mem_filter.mpr ⟨mem_range.mpr h1,hd1⟩
   . exact mem_filter.mpr ⟨mem_range.mpr h2,hd2⟩
   . exact mem_filter.mpr ⟨mem_range.mpr h3,hd3⟩
  have hc : ({a1,a2,a3} : Finset ℕ).card=3:=by
   rw [card_insert_of_notMem (by simp [h12,h13]),Finset.card_pair h23]
  have hle:=card_le_card hsub
  cases b <;> omega
 have hstep_env : ∀ (b : Bool) (j : ℕ) (hj : j < C.gates.length) (st : List Gate × List (Bool ⊕ ℕ)),
  sPfx n l b C.gates j=st →
  evE (sPfx n l b C.gates (j+1)).2 (n+j) =
  evE (sGt n st (gateAt C j)).2 st.2.length:=by
  intro b j hj st hst
  rw [simplifyPrefix_succ n l b C j hj,hst]
  have hlen : st.2.length=n+j:=by rw [← hst];exact simplifyPrefix_env_len n l b C j (by omega)
  rw [hlen]
 have hex : ∃ j,j < C.gates.length/\l.val ∈ eIn (gateAt C j) :=
  exGtRL K A l p hA hl hmin hfun
 let j0:=Nat.find hex
 have hj0 : j0 < C.gates.length:=(Nat.find_spec hex).1
 have hLJ0 : l.val ∈ eIn (gateAt C j0):=(Nat.find_spec hex).2
 have huniq_l : ∀ j < C.gates.length,j≠j0->l.val ∉ eIn (gateAt C j):=by
  intro j2 hj2 hne2 hl_in_j2
  have hj02 : j0 < j2:=by
   have hle : j0<=j2:=Nat.find_min' hex ⟨hj2,hl_in_j2⟩
   omega
  have hdT0 : isD n l true C j0=true :=
   deleted_of_inl_input n l true C hmin hncC hj0 hLJ0 (hl_env true j0 (by omega))
  have hdT2 : isD n l true C j2=true :=
   deleted_of_inl_input n l true C hmin hncC hj2 hl_in_j2 (hl_env true j2 (by omega))
  have hdF0 : isD n l false C j0=true :=
   deleted_of_inl_input n l false C hmin hncC hj0 hLJ0 (hl_env false j0 (by omega))
  have hdF2 : isD n l false C j2=true :=
   deleted_of_inl_input n l false C hmin hncC hj2 hl_in_j2 (hl_env false j2 (by omega))
  have hnot_inl_j2 : ∀ (b : Bool) (c : Bool),
   evE (sPfx n l b C.gates (j2+1)).2 (n+j2)=Sum.inl c->False:=by
   intro b c hc
   have hj2_lt':=hnot_out_inl b j2 c hj2 hc
   obtain ⟨j3,hj3,hj23,hmem3⟩:=evGtR hmin hncC j2 hj2_lt'
   have hj3_env : evE (sPfx n l b C.gates j3).2 (n+j2)=Sum.inl c:=by
    rw [spEnvS n l b C (by omega : j2+1<=j3) (by omega) (by omega),hc]
   have hd3:=deleted_of_inl_input n l b C hmin hncC hj3 hmem3 hj3_env
   cases b with
   | true => exact hno_three_del true j0 j2 j3 hj0 hj2 hj3 (by omega) (by omega) (by omega) hdT0 hdT2 hd3
   | false => exact hno_three_del false j0 j2 j3 hj0 hj2 hj3 (by omega) (by omega) (by omega) hdF0 hdF2 hd3
  rcases minGS hmin hncC j2 hj2 with ⟨hop,a,b_in,hin,_,_,_⟩ |
   ⟨hop,a,b_in,hin,_,_,_⟩ | ⟨hop,a,heff,_⟩
  . apply hnot_inl_j2 false false
    rcases hst : sPfx n l false C.gates j2 with ⟨gs,env⟩
    rw [hstep_env false j2 hj2 (gs,env) hst]
    have hl0 : evE env l.val=Sum.inl false:=by have h:=hl_env false j2 (by omega);rw [hst] at h;exact h
    simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hl_in_j2
    simp only [sGt,hop,hin]
    rcases hl_in_j2 with rfl | rfl
    . rw [hl0];simp [evE,List.getD_eq_getElem?_getD]
    . rw [hl0];cases evE env a with
      | inl c1 => cases c1 <;> simp [evE,List.getD_eq_getElem?_getD]
      | inr _ => simp [evE,List.getD_eq_getElem?_getD]
  . apply hnot_inl_j2 true true
    rcases hst : sPfx n l true C.gates j2 with ⟨gs,env⟩
    rw [hstep_env true j2 hj2 (gs,env) hst]
    have hl0 : evE env l.val=Sum.inl true:=by have h:=hl_env true j2 (by omega);rw [hst] at h;exact h
    simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hl_in_j2
    simp only [sGt,hop,hin]
    rcases hl_in_j2 with rfl | rfl
    . rw [hl0];simp [evE,List.getD_eq_getElem?_getD]
    . rw [hl0];cases evE env a with
      | inl c1 => cases c1 <;> simp [evE,List.getD_eq_getElem?_getD]
      | inr _ => simp [evE,List.getD_eq_getElem?_getD]
  . apply hnot_inl_j2 true false
    rcases hst : sPfx n l true C.gates j2 with ⟨gs,env⟩
    rw [hstep_env true j2 hj2 (gs,env) hst]
    have hl0 : evE env l.val=Sum.inl true:=by have h:=hl_env true j2 (by omega);rw [hst] at h;exact h
    simp only [heff,List.mem_cons,List.not_mem_nil,or_false] at hl_in_j2;subst hl_in_j2
    have hhead : (gateAt C j2).inputs.headD env.length=l.val:=by
     cases hin : (gateAt C j2).inputs with
     | nil => simp [eIn,hop,hin] at heff
     | cons x xs => simp [eIn,hop,hin] at heff;simp [heff]
    simp only [sGt,hop]
    rw [hhead,hl0]
    simp [evE,List.getD_eq_getElem?_getD]
 have hconsumer : ∀ (b : Bool) (c0 : Bool),
  evE (sPfx n l b C.gates (j0+1)).2 (n+j0)=Sum.inl c0 →
  ∃ j1,j0 < j1/\j1 < C.gates.length ∧
   n+j0 ∈ eIn (gateAt C j1) ∧
   (∀ j < C.gates.length,j≠j1->n+j0 ∉ eIn (gateAt C j)) ∧
   (Finset.range C.gates.length).filter (fun j => isD n l b C j=true)={j0,j1} ∧
   (∃ v' : ℕ,evE (sPfx n l b C.gates (j1+1)).2 (n+j1)=Sum.inr v'):=by
  intro b c0 hcj0
  have hd0 : isD n l b C j0=true :=
   deleted_of_inl_input n l b C hmin hncC hj0 hLJ0 (hl_env b j0 (by omega))
  have hj0_lt':=hnot_out_inl b j0 c0 hj0 hcj0
  obtain ⟨j1,hj1,hj01,hmem1⟩:=evGtR hmin hncC j0 hj0_lt'
  have hj1_env0 : evE (sPfx n l b C.gates j1).2 (n+j0)=Sum.inl c0:=by
   rw [spEnvS n l b C (by omega : j0+1<=j1) (by omega) (by omega),hcj0]
  have hd1 : isD n l b C j1=true :=
   deleted_of_inl_input n l b C hmin hncC hj1 hmem1 hj1_env0
  have hdel_eq : (Finset.range C.gates.length).filter (fun j => isD n l b C j=true)={j0,j1}:=by
   have hsub : ({j0,j1} : Finset ℕ) ⊆
    (Finset.range C.gates.length).filter (fun j => isD n l b C j=true):=by
    intro x hx;simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl
    . exact mem_filter.mpr ⟨mem_range.mpr hj0,hd0⟩
    . exact mem_filter.mpr ⟨mem_range.mpr hj1,hd1⟩
   symm
   apply Finset.eq_of_subset_of_card_le hsub
   rw [Finset.card_pair (by omega)]
   cases b <;> omega
  have huniq1 : ∀ j < C.gates.length,j≠j1->n+j0 ∉ eIn (gateAt C j):=by
   intro j hj hne1 hmemj
   have hgt : j0 < j:=by
    rcases minGS hmin hncC j hj with ⟨hop,a,b_in,hin,ha,hb,_⟩ |
     ⟨hop,a,b_in,hin,ha,hb,_⟩ | ⟨hop,a,heff,ha⟩
    . simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hmemj
      rcases hmemj with rfl | rfl <;> omega
    . simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hmemj
      rcases hmemj with rfl | rfl <;> omega
    . simp only [heff,List.mem_cons,List.not_mem_nil,or_false] at hmemj;omega
   have hj_env : evE (sPfx n l b C.gates j).2 (n+j0)=Sum.inl c0:=by
    rw [spEnvS n l b C (by omega : j0+1<=j) (by omega) (by omega),hcj0]
   have hdj:=deleted_of_inl_input n l b C hmin hncC hj hmemj hj_env
   exact hno_three_del b j0 j1 j hj0 hj1 hj (by omega) (by omega) (Ne.symm hne1) hd0 hd1 hdj
  have hJ1I : ∃ v' : ℕ,evE (sPfx n l b C.gates (j1+1)).2 (n+j1)=Sum.inr v':=by
   cases h : evE (sPfx n l b C.gates (j1+1)).2 (n+j1) with
   | inr v' => exact ⟨v',rfl⟩
   | inl c1 =>
    exfalso
    have hj1_lt':=hnot_out_inl b j1 c1 hj1 h
    obtain ⟨j2,hj2,hj12,hmem2⟩:=evGtR hmin hncC j1 hj1_lt'
    have hj2_env : evE (sPfx n l b C.gates j2).2 (n+j1)=Sum.inl c1:=by
     rw [spEnvS n l b C (by omega : j1+1<=j2) (by omega) (by omega),h]
    have hd2:=deleted_of_inl_input n l b C hmin hncC hj2 hmem2 hj2_env
    exact hno_three_del b j0 j1 j2 hj0 hj1 hj2 (by omega) (by omega) (by omega) hd0 hd1 hd2
  exact ⟨j1,hj01,hj1,hmem1,huniq1,hdel_eq,hJ1I⟩
 have hj1_shape : ∀ (b c0 : Bool) (j1 v' : ℕ),j0 < j1->j1 < C.gates.length →
  n+j0 ∈ eIn (gateAt C j1) →
  evE (sPfx n l b C.gates (j0+1)).2 (n+j0)=Sum.inl c0 →
  evE (sPfx n l b C.gates (j1+1)).2 (n+j1)=Sum.inr v' →
  ((c0=true->(gateAt C j1).op=.and)/\(c0=false->(gateAt C j1).op=.or)) ∧
  ∃ v : ℕ,((gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0]) ∧
   v < n+j1/\v≠n+j0/\v≠l.val:=by
  intro b c0 j1 v' hj01 hj1 hmem1 hcj0 hJ1I
  have hj1_env0 : evE (sPfx n l b C.gates j1).2 (n+j0)=Sum.inl c0:=by
   rw [spEnvS n l b C (by omega : j0+1<=j1) (by omega) (by omega),hcj0]
  rcases hst : sPfx n l b C.gates j1 with ⟨gs,env⟩
  rw [hstep_env b j1 hj1 (gs,env) hst] at hJ1I
  rw [hst] at hj1_env0
  rcases minGS hmin hncC j1 hj1 with ⟨hop,a,b_in,hin,ha,hb,hab⟩ |
   ⟨hop,a,b_in,hin,ha,hb,hab⟩ | ⟨hop,a,heff,_⟩
  ·
   simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hmem1
   have hc0_true : c0=true:=by
    cases c0
    . exfalso
      simp only [sGt,hop,hin] at hJ1I
      rcases hmem1 with rfl | rfl
      . rw [hj1_env0] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I
      . rw [hj1_env0] at hJ1I
        cases hae : evE env a with
        | inl c1 => rw [hae] at hJ1I;cases c1 <;> simp [evE,List.getD_eq_getElem?_getD] at hJ1I
        | inr _ => rw [hae] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I
    . rfl
   refine ⟨⟨fun _ => hop,fun h => by rw [hc0_true] at h;cases h⟩,?_⟩
   rcases hmem1 with rfl | rfl
   . exact ⟨b_in,Or.inl hin,hb,hab.symm,fun h => huniq_l j1 hj1 (by omega) (by simp [eIn,hop,hin,h])⟩
   . exact ⟨a,Or.inr hin,ha,hab,fun h => huniq_l j1 hj1 (by omega) (by simp [eIn,hop,hin,h])⟩
  ·
   simp only [eIn,hop,hin,List.mem_cons,List.not_mem_nil,or_false] at hmem1
   have hc0_false : c0=false:=by
    cases c0
    . rfl
    . exfalso
      simp only [sGt,hop,hin] at hJ1I
      rcases hmem1 with rfl | rfl
      . rw [hj1_env0] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I
      . rw [hj1_env0] at hJ1I
        cases hae : evE env a with
        | inl c1 => rw [hae] at hJ1I;cases c1 <;> simp [evE,List.getD_eq_getElem?_getD] at hJ1I
        | inr _ => rw [hae] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I
   refine ⟨⟨(fun h => by rw [hc0_false] at h;cases h),fun _ => hop⟩,?_⟩
   rcases hmem1 with rfl | rfl
   . exact ⟨b_in,Or.inl hin,hb,hab.symm,fun h => huniq_l j1 hj1 (by omega) (by simp [eIn,hop,hin,h])⟩
   . exact ⟨a,Or.inr hin,ha,hab,fun h => huniq_l j1 hj1 (by omega) (by simp [eIn,hop,hin,h])⟩
  ·
   exfalso
   simp only [heff,List.mem_cons,List.not_mem_nil,or_false] at hmem1;subst hmem1
   have hhead : (gateAt C j1).inputs.headD env.length=n+j0:=by
    cases hin : (gateAt C j1).inputs with
    | nil => simp [eIn,hop,hin] at heff
    | cons x xs => simp [eIn,hop,hin] at heff;simp [heff]
   simp only [sGt,hop] at hJ1I
   rw [hhead,hj1_env0] at hJ1I
   simp [evE,List.getD_eq_getElem?_getD] at hJ1I
 rcases minGS hmin hncC j0 hj0 with ⟨hop0,a0,b0,hin0,ha0,hb0,hab0⟩ |
  ⟨hop0,a0,b0,hin0,ha0,hb0,hab0⟩ | ⟨hop0,a0,heff0,_⟩
 ·
  have hcj0 : evE (sPfx n l false C.gates (j0+1)).2 (n+j0)=Sum.inl false:=by
   rcases hst : sPfx n l false C.gates j0 with ⟨gs,env⟩
   rw [hstep_env false j0 hj0 (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl false:=by have h:=hl_env false j0 (by omega);rw [hst] at h;exact h
   simp only [eIn,hop0,hin0,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   simp only [sGt,hop0,hin0]
   rcases hLJ0 with rfl | rfl
   . rw [hl0];simp [evE,List.getD_eq_getElem?_getD]
   . rw [hl0];cases evE env a0 with
     | inl c1 => cases c1 <;> simp [evE,List.getD_eq_getElem?_getD]
     | inr _ => simp [evE,List.getD_eq_getElem?_getD]
  obtain ⟨j1,hj01,hj1,hmem1,huniq1,hdel_eq,v',hJ1I⟩:=hconsumer false false hcj0
  obtain ⟨⟨_,hop1⟩,v,hvin,hvlt,hv0,hvl⟩:=hj1_shape false false j1 v' hj01 hj1 hmem1 hcj0 hJ1I
  have hDlen : (sPfx n l false C.gates C.gates.length).1.length=s2:=by
   rw [hdel_eq,Finset.card_pair (by omega)] at hszF
   change (sPfx n l false C.gates C.gates.length).1.length+2=C.size at hszF
   omega
  have hs12 : s1=s2:=by omega
  have hu_ex : ∃ u,((gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val]) ∧
   u < n+j0/\u≠l.val:=by
   simp only [eIn,hop0,hin0,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   rcases hLJ0 with rfl | rfl
   . exact ⟨b0,Or.inl hin0,hb0,hab0.symm⟩
   . exact ⟨a0,Or.inr hin0,ha0,hab0⟩
  obtain ⟨u,huin,hult,hul⟩:=hu_ex
  exact ⟨j0,j1,hj01,hj1,huniq_l,huniq1,Or.inr ⟨hs12,u,v,v',outF,
   hop0,huin,hult,hul,hop1 rfl,hvin,hvlt,hv0,hvl,hdel_eq,hcj0,hJ1I,houtF,
   hfitF,funext fun x => by rw [hfunF x,hfun,hupdF],
   by change (sPfx n l false C.gates C.gates.length).1.length=s1;omega⟩⟩
 ·
  have hcj0 : evE (sPfx n l true C.gates (j0+1)).2 (n+j0)=Sum.inl true:=by
   rcases hst : sPfx n l true C.gates j0 with ⟨gs,env⟩
   rw [hstep_env true j0 hj0 (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl true:=by have h:=hl_env true j0 (by omega);rw [hst] at h;exact h
   simp only [eIn,hop0,hin0,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   simp only [sGt,hop0,hin0]
   rcases hLJ0 with rfl | rfl
   . rw [hl0];simp [evE,List.getD_eq_getElem?_getD]
   . rw [hl0];cases evE env a0 with
     | inl c1 => cases c1 <;> simp [evE,List.getD_eq_getElem?_getD]
     | inr _ => simp [evE,List.getD_eq_getElem?_getD]
  obtain ⟨j1,hj01,hj1,hmem1,huniq1,hdel_eq,v',hJ1I⟩:=hconsumer true true hcj0
  obtain ⟨⟨hop1,_⟩,v,hvin,hvlt,hv0,hvl⟩:=hj1_shape true true j1 v' hj01 hj1 hmem1 hcj0 hJ1I
  have hDlen : (sPfx n l true C.gates C.gates.length).1.length=s2:=by
   rw [hdel_eq,Finset.card_pair (by omega)] at hszT
   change (sPfx n l true C.gates C.gates.length).1.length+2=C.size at hszT
   omega
  have hu_ex : ∃ u,((gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val]) ∧
   u < n+j0/\u≠l.val:=by
   simp only [eIn,hop0,hin0,List.mem_cons,List.not_mem_nil,or_false] at hLJ0
   rcases hLJ0 with rfl | rfl
   . exact ⟨b0,Or.inl hin0,hb0,hab0.symm⟩
   . exact ⟨a0,Or.inr hin0,ha0,hab0⟩
  obtain ⟨u,huin,hult,hul⟩:=hu_ex
  exact ⟨j0,j1,hj01,hj1,huniq_l,huniq1,Or.inl ⟨u,v,v',outT,
   hop0,huin,hult,hul,hop1 rfl,hvin,hvlt,hv0,hvl,hdel_eq,hcj0,hJ1I,houtT,
   hfitT,funext fun x => by rw [hfunT x,hfun,hupdT],hDlen⟩⟩
 ·
  exfalso
  simp only [heff0,List.mem_cons,List.not_mem_nil,or_false] at hLJ0;subst hLJ0
  have hhead : ∀ k : ℕ,(gateAt C j0).inputs.headD k=l.val:=by
   intro k
   cases hin : (gateAt C j0).inputs with
   | nil => simp [eIn,hop0,hin] at heff0
   | cons x xs => simp [eIn,hop0,hin] at heff0;simp [heff0]
  have hcj0_T : evE (sPfx n l true C.gates (j0+1)).2 (n+j0)=Sum.inl false:=by
   rcases hst : sPfx n l true C.gates j0 with ⟨gs,env⟩
   rw [hstep_env true j0 hj0 (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl true:=by have h:=hl_env true j0 (by omega);rw [hst] at h;exact h
   simp only [sGt,hop0];rw [hhead env.length,hl0]
   simp [evE,List.getD_eq_getElem?_getD]
  have hcj0_F : evE (sPfx n l false C.gates (j0+1)).2 (n+j0)=Sum.inl true:=by
   rcases hst : sPfx n l false C.gates j0 with ⟨gs,env⟩
   rw [hstep_env false j0 hj0 (gs,env) hst]
   have hl0 : evE env l.val=Sum.inl false:=by have h:=hl_env false j0 (by omega);rw [hst] at h;exact h
   simp only [sGt,hop0];rw [hhead env.length,hl0]
   simp [evE,List.getD_eq_getElem?_getD]
  obtain ⟨j1,hj01,hj1,hmem1,huniq1,_,v'T,hj1_inrT⟩:=hconsumer true false hcj0_T
  obtain ⟨j1F,hj01F,hj1F,hmem1F,_,_,v'F,hj1_inrF⟩:=hconsumer false true hcj0_F
  have hjeq : j1F=j1:=by by_contra hne;exact huniq1 j1F hj1F hne hmem1F
  subst hjeq
  have hor:=(hj1_shape true false j1F v'T hj01 hj1 hmem1 hcj0_T hj1_inrT).1.2 rfl
  have hand:=(hj1_shape false true j1F v'F hj01 hj1 hmem1 hcj0_F hj1_inrF).1.1 rfl
  rw [hor] at hand;cases hand
lemma otSG {n : ℕ} {C : Circuit} {j a b : ℕ}
 (hab : a≠b) (ha : a≠n+j) (hb : b≠n+j)
 (hop : (gateAt C j).op=.or)
 (hin : (gateAt C j).inputs=[a,b]\/(gateAt C j).inputs=[b,a]) :
 IsOrTree n C {j} {a,b} (n+j):=by
 have hreads : ∀ w,readsIn C {j} w=(gateAt C j).inputs.count w:=fun w => by
  simp [readsIn]
 refine ⟨?_,?_,?_,?_⟩
 . intro k hk;simp only [mem_singleton] at hk;subst hk
   refine ⟨hop,?_,?_⟩
   . rcases hin with h | h <;> simp [h]
   . intro i hi;rcases hin with h | h <;> rw [h] at hi <;> simp at hi <;>
      rcases hi with rfl | rfl <;> exact Or.inl (by simp)
 . intro w hw;simp only [mem_insert,mem_singleton] at hw
   rcases hw with rfl | rfl
   . refine ⟨by rintro ⟨_,h⟩;simp at h;omega,?_⟩
     rw [if_neg ha,hreads]
     rcases hin with h | h <;> rw [h] <;> simp [hab,hab.symm]
   . refine ⟨by rintro ⟨_,h⟩;simp at h;omega,?_⟩
     rw [if_neg hb,hreads]
     rcases hin with h | h <;> rw [h] <;> simp [hab,hab.symm]
 . intro k hk;simp only [mem_singleton] at hk;subst hk
   rw [if_pos rfl,hreads]
   rcases hin with h | h <;> rw [h] <;> simp [ha,hb,ha.symm,hb.symm]
 . rw [if_neg (Finset.singleton_ne_empty j)];exact ⟨j,Finset.mem_singleton_self j,rfl⟩
lemma otLI {n : ℕ} {D C : Circuit} {G' L' : Finset ℕ} {ρ' : ℕ}
 (ht : IsOrTree n D G' L' ρ')
 (fG : ℕ->ℕ) (gMap : ℕ->ℕ)
 (hfG_inj : Set.InjOn fG (G' : Set ℕ))
 (hgMap_gate : ∀ j' ∈ G',gMap (n+j')=n+fG j')
 (hgMap_inj : ∀ a b,(a ∈ L'\/(n<=a/\a - n ∈ G'))->(b ∈ L'\/(n<=b/\b - n ∈ G')) →
  gMap a=gMap b->a=b)
 (hgate_op : ∀ j' ∈ G',(gateAt C (fG j')).op=(gateAt D j').op)
 (hgate_in : ∀ j' ∈ G',(gateAt C (fG j')).inputs=(gateAt D j').inputs.map gMap) :
 IsOrTree n C (G'.image fG) (L'.image gMap) (gMap ρ'):=by
 obtain ⟨hg,hl,hgg,hroot⟩:=ht
 have hρnode : ρ' ∈ L'\/(n <= ρ' /\ ρ' - n ∈ G'):=by
  by_cases hGe : G'=∅
  . rw [if_pos hGe] at hroot;left;rw [hroot];simp
  . rw [if_neg hGe] at hroot;obtain ⟨j',hj',rfl⟩:=hroot;right;exact ⟨by omega,by simpa using hj'⟩
 have hreads : ∀ w',(w' ∈ L'\/(n<=w'/\w' - n ∈ G')) →
  readsIn C (G'.image fG) (gMap w')=readsIn D G' w':=by
  intro w' hw'
  unfold readsIn
  rw [sum_image (fun a ha b hb h => hfG_inj ha hb h)]
  refine sum_congr rfl fun j' hj' => ?_
  rw [hgate_in j' hj']
  have hmap_in : ∀ i ∈ (gateAt D j').inputs,i ∈ L'\/(n<=i/\i - n ∈ G'):=(hg j' hj').2.2
  generalize (gateAt D j').inputs=xs at hmap_in
  induction xs with
  | nil => simp
  | cons x xs ih =>
   simp only [List.map_cons,List.count_cons]
   have hx:=hmap_in x (by simp)
   have hbeq : (gMap x == gMap w')=(x == w'):=by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨fun h => hgMap_inj x w' hx hw' h,fun h => by rw [h]⟩
   rw [hbeq,ih (fun i hi => hmap_in i (by simp [hi]))]
 refine ⟨?_,?_,?_,?_⟩
 . intro j hj
   obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
   refine ⟨by rw [hgate_op j' hj',(hg j' hj').1],by rw [hgate_in j' hj',List.length_map,(hg j' hj').2.1],?_⟩
   intro i hi
   rw [hgate_in j' hj'] at hi
   obtain ⟨i',hi'mem,rfl⟩:=List.mem_map.mp hi
   rcases (hg j' hj').2.2 i' hi'mem with hi'L | ⟨hi'n,hi'G⟩
   . exact Or.inl (mem_image.mpr ⟨i',hi'L,rfl⟩)
   . have hi'eq : n+(i' - n)=i':=by omega
     rw [← hi'eq,hgMap_gate (i' - n) hi'G]
     exact Or.inr ⟨by omega,by simpa using mem_image.mpr ⟨i' - n,hi'G,rfl⟩⟩
 . intro w hw
   obtain ⟨w',hw',rfl⟩:=mem_image.mp hw
   refine ⟨?_,?_⟩
   . rintro ⟨hwn,hwG⟩
     obtain ⟨j',hj',hjeq⟩:=mem_image.mp hwG
     have hge : gMap w'=gMap (n+j'):=by rw [hgMap_gate j' hj'];omega
     have heq:=hgMap_inj w' (n+j') (Or.inl hw') (Or.inr ⟨by omega,by simpa using hj'⟩) hge
     exact (hl w' hw').1 ⟨by omega,by simpa [heq] using hj'⟩
   . rw [hreads w' (Or.inl hw'),(hl w' hw').2]
     by_cases h : w'=ρ'
     . subst h;simp
     . have hne : gMap w'≠gMap ρ':=fun heq => h (hgMap_inj w' ρ' (Or.inl hw') hρnode heq)
       simp [h,hne]
 . intro j hj
   obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
   rw [← hgMap_gate j' hj',hreads (n+j') (Or.inr ⟨by omega,by simpa using hj'⟩),hgg j' hj']
   by_cases h : n+j'=ρ'
   . rw [h];simp
   . have hne : gMap (n+j')≠gMap ρ' :=
      fun heq => h (hgMap_inj (n+j') ρ' (Or.inr ⟨by omega,by simpa using hj'⟩) hρnode heq)
     simp [h,hne]
 . by_cases hGe : G'=∅
   . subst hGe;simp at hroot ⊢;rw [hroot];simp
   . have hne : G'.image fG ≠ ∅:=Finset.Nonempty.ne_empty (Finset.Nonempty.image (Finset.nonempty_iff_ne_empty.mpr hGe) fG)
     rw [if_neg hGe] at hroot
     rw [if_neg hne]
     obtain ⟨j',hj',rfl⟩:=hroot
     exact ⟨fG j',mem_image.mpr ⟨j',hj',rfl⟩,hgMap_gate j' hj'⟩
lemma otLR {n : ℕ} {D C : Circuit} {G' L' : Finset ℕ} {ρ' jv' l1' l2' leaf_new : ℕ}
 (hrb : ReadsBack n D) (hG' : ∀ j ∈ G',j < D.gates.length)
 (ht : IsOrTree n D G' L' ρ')
 (hjv' : jv' ∈ G')
 (hl1' : l1' ∈ L') (hl2' : l2' ∈ L') (hl12 : l1'≠l2')
 (hjv_in : (gateAt D jv').inputs=[l1',l2']\/(gateAt D jv').inputs=[l2',l1'])
 (fG : ℕ->ℕ) (invW : ℕ->ℕ)
 (hfG_inj : Set.InjOn fG (G' : Set ℕ))
 (hIWG : ∀ j' ∈ G',invW (n+j')=n+fG j')
 (hinvW_inj : ∀ a b,(a ∈ L'\/(n<=a/\a - n ∈ G'))->(b ∈ L'\/(n<=b/\b - n ∈ G')) →
  invW a=invW b->a=b)
 (hLF : ∀ a,(a ∈ L'\/(n<=a/\a - n ∈ G'))->invW a≠leaf_new)
 (hgate_op : ∀ j' ∈ G'.erase jv',(gateAt C (fG j')).op=(gateAt D j').op)
 (hgate_in : ∀ j' ∈ G'.erase jv',(gateAt C (fG j')).inputs =
  (gateAt D j').inputs.map (fun w' => if w'=n+jv' then leaf_new else invW w')) :
 IsOrTree n C ((G'.erase jv').image fG)
  (insert leaf_new (((L'.erase l1').erase l2').image invW))
  (if ρ'=n+jv' then leaf_new else invW ρ'):=by
 let G0:=G'.erase jv'
 let L0:=insert (n+jv') ((L'.erase l1').erase l2')
 have hjv_not_L : n+jv' ∉ (L'.erase l1').erase l2':=by
  intro h;have hL:=Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  exact (ht.2.1 (n+jv') hL).1 ⟨by omega,by simpa using hjv'⟩
 have hreads_jv : ∀ w',readsIn D G' w'=readsIn D G0 w'+(if w'=l1' then 1 else 0)+(if w'=l2' then 1 else 0):=by
  intro w';unfold readsIn;dsimp only [G0]
  rw [← Finset.add_sum_erase G' _ hjv']
  rcases hjv_in with h | h <;> rw [h]
  . simp only [List.count_cons,List.count_nil,beq_iff_eq]
    by_cases h1 : w'=l1'
    . subst h1;have h2 : l2'≠w':=hl12.symm;simp [hl12,h2];omega
    . have h1' : l1'≠w':=Ne.symm h1
      by_cases h2 : w'=l2'
      . subst h2;simp [h1,h1'];omega
      . have h2' : l2'≠w':=Ne.symm h2;simp [h1,h1',h2,h2']
  . simp only [List.count_cons,List.count_nil,beq_iff_eq]
    by_cases h1 : w'=l1'
    . subst h1;have h2 : l2'≠w':=hl12.symm;simp [hl12,h2];omega
    . have h1' : l1'≠w':=Ne.symm h1
      by_cases h2 : w'=l2'
      . subst h2;simp [h1,h1'];omega
      . have h2' : l2'≠w':=Ne.symm h2;simp [h1,h1',h2,h2']
 have hcard_orig : L'.card=G'.card+1:=tree_card n D G' L' ρ' ht
 have ht0 : IsOrTree n D G0 L0 ρ':=by
  obtain ⟨hg,hl,hgg,hroot⟩:=ht
  have hnot_read_l12 : ∀ j' ∈ G0,l1' ∉ (gateAt D j').inputs/\l2' ∉ (gateAt D j').inputs:=by
   intro j' hj'
   have hl1_ne_ρ : l1' ≠ ρ':=by
    intro h;subst h
    have hGe : G' ≠ ∅:=Finset.Nonempty.ne_empty ⟨jv',hjv'⟩
    rw [if_neg hGe] at hroot;obtain ⟨k,hk,hkeq⟩:=hroot
    exact (hl _ hl1').1 ⟨by omega,by simpa [hkeq] using hk⟩
   have hl2_ne_ρ : l2' ≠ ρ':=by
    intro h;subst h
    have hGe : G' ≠ ∅:=Finset.Nonempty.ne_empty ⟨jv',hjv'⟩
    rw [if_neg hGe] at hroot;obtain ⟨k,hk,hkeq⟩:=hroot
    exact (hl _ hl2').1 ⟨by omega,by simpa [hkeq] using hk⟩
   have hr1 : readsIn D G0 l1'=0:=by have:=(hl l1' hl1').2;rw [if_neg hl1_ne_ρ,hreads_jv] at this;simp [hl12] at this;omega
   have hr2 : readsIn D G0 l2'=0:=by have:=(hl l2' hl2').2;rw [if_neg hl2_ne_ρ,hreads_jv] at this;simp [hl12.symm] at this;omega
   exact ⟨fun h => by have:=(rInP D G0 l1').mpr ⟨j',hj',h⟩;omega,
    fun h => by have:=(rInP D G0 l2').mpr ⟨j',hj',h⟩;omega⟩
  refine ⟨?_,?_,?_,?_⟩
  . intro j' hj'
    have hj'G:=Finset.mem_of_mem_erase hj'
    refine ⟨(hg j' hj'G).1,(hg j' hj'G).2.1,?_⟩
    intro i hi
    rcases (hg j' hj'G).2.2 i hi with hiL | ⟨hin,hiG⟩
    . left;exact mem_insert_of_mem (mem_erase.mpr
       ⟨fun h => (hnot_read_l12 j' hj').2 (h ▸ hi),mem_erase.mpr
        ⟨fun h => (hnot_read_l12 j' hj').1 (h ▸ hi),hiL⟩⟩)
    . by_cases heq : i - n=jv'
      . left;have : i=n+jv':=by omega
        rw [this];exact mem_insert_self _ _
      . right;exact ⟨hin,mem_erase.mpr ⟨heq,hiG⟩⟩
  . intro w hw
    rcases mem_insert.mp hw with rfl | hw'
    . refine ⟨by rintro ⟨_,h⟩;exact (mem_erase.mp h).1 (by omega),?_⟩
      have h1:=hgg jv' hjv'
      have hne1 : n+jv'≠l1':=fun h => (hl l1' hl1').1 ⟨by omega,by rw [← h];simpa using hjv'⟩
      have hne2 : n+jv'≠l2':=fun h => (hl l2' hl2').1 ⟨by omega,by rw [← h];simpa using hjv'⟩
      rw [hreads_jv,if_neg hne1,if_neg hne2] at h1;omega
    . have hwL:=Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw')
      have hne2:=(mem_erase.mp hw').1
      have hne1:=(mem_erase.mp (Finset.mem_of_mem_erase hw')).1
      refine ⟨fun ⟨h1,h2⟩ => (hl w hwL).1 ⟨h1,Finset.mem_of_mem_erase h2⟩,?_⟩
      have h1:=(hl w hwL).2
      rw [hreads_jv,if_neg hne1,if_neg hne2] at h1;omega
  . intro j' hj'
    have hj'G:=Finset.mem_of_mem_erase hj'
    have hne1 : n+j'≠l1':=fun h => (hl l1' hl1').1 ⟨by omega,by rw [← h];simpa using hj'G⟩
    have hne2 : n+j'≠l2':=fun h => (hl l2' hl2').1 ⟨by omega,by rw [← h];simpa using hj'G⟩
    have h1:=hgg j' hj'G
    rw [hreads_jv,if_neg hne1,if_neg hne2] at h1;omega
  . by_cases hG0e : G0=∅
    . rw [if_pos hG0e]
      have hGe : G'={jv'}:=by
       ext k;simp only [mem_singleton]
       constructor
       . intro hk;by_contra hne;have : k ∈ G0:=mem_erase.mpr ⟨hne,hk⟩;rw [hG0e] at this;simp at this
       . rintro rfl;exact hjv'
      have hρeq : ρ'=n+jv':=by
       have hne : G' ≠ ∅:=by rw [hGe];simp
       rw [if_neg hne] at hroot;obtain ⟨k,hk,hkeq⟩:=hroot
       rw [hGe,mem_singleton] at hk;subst hk;exact hkeq
      have hLcard : L'.card=2:=by rw [hGe] at hcard_orig;simpa using hcard_orig
      have hLeq : L'={l1',l2'}:=by
       symm;apply Finset.eq_of_subset_of_card_le
       . intro x hx;simp at hx;rcases hx with rfl | rfl <;> assumption
       . rw [Finset.card_pair hl12,hLcard]
      rw [hρeq];unfold L0;rw [hLeq]
      ext x;simp;omega
    . rw [if_neg hG0e]
      have hGe : G' ≠ ∅:=Finset.Nonempty.ne_empty ⟨jv',hjv'⟩
      rw [if_neg hGe] at hroot;obtain ⟨j0,hj0,hρeq⟩:=hroot
      refine ⟨j0,mem_erase.mpr ⟨?_,hj0⟩,hρeq⟩
      intro heq;subst heq
      have hG0ne : G0.Nonempty:=Finset.nonempty_iff_ne_empty.mpr hG0e
      let m:=G0.max' hG0ne
      have hm0 : m ∈ G0:=Finset.max'_mem G0 hG0ne
      have hmG:=Finset.mem_of_mem_erase hm0
      have hmne : m≠j0:=(mem_erase.mp hm0).1
      have hm1 : readsIn D G' (n+m)=1:=by rw [hgg m hmG,if_neg (by omega)]
      have hmn1 : n+m≠l1':=fun h => (hl l1' hl1').1 ⟨by omega,by rw [← h];simpa using hmG⟩
      have hmn2 : n+m≠l2':=fun h => (hl l2' hl2').1 ⟨by omega,by rw [← h];simpa using hmG⟩
      have hm0r : readsIn D G0 (n+m)=1:=by rw [hreads_jv,if_neg hmn1,if_neg hmn2] at hm1;omega
      obtain ⟨k,hk0,hmemk⟩:=(rInP D G0 (n+m)).mp (by omega)
      have hlt : n+m < n+k:=hrb k (hG' k (Finset.mem_of_mem_erase hk0)) (n+m) hmemk
      have hle : k<=m:=Finset.le_max' G0 k hk0
      omega
 let gMap (w' : ℕ) : ℕ:=if w'=n+jv' then leaf_new else invW w'
 have hLimg : L0.image gMap=insert leaf_new (((L'.erase l1').erase l2').image invW):=by
  unfold L0;rw [Finset.image_insert]
  have h1 : gMap (n+jv')=leaf_new:=by simp [gMap]
  rw [h1];congr 1
  apply Finset.image_congr
  intro w hw
  have hne : w≠n+jv':=fun h => hjv_not_L (h ▸ hw)
  simp [gMap,hne]
 have hρ_eq : gMap ρ'=if ρ'=n+jv' then leaf_new else invW ρ':=rfl
 rw [← hLimg,← hρ_eq]
 refine otLI ht0 fG gMap (hfG_inj.mono (erase_subset _ _)) ?_ ?_ hgate_op hgate_in
 . intro j' hj'
   have hne : n+j'≠n+jv':=by have:=(mem_erase.mp hj').1;omega
   simp only [gMap,if_neg hne]
   exact hIWG j' (Finset.mem_of_mem_erase hj')
 . intro a b ha hb heq
   have ha' : a ∈ L'\/(n<=a/\a - n ∈ G'):=by
    rcases ha with haL | ⟨han,haG⟩
    . rcases mem_insert.mp haL with rfl | h
      . exact Or.inr ⟨by omega,by simpa using hjv'⟩
      . exact Or.inl (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    . exact Or.inr ⟨han,Finset.mem_of_mem_erase haG⟩
   have hb' : b ∈ L'\/(n<=b/\b - n ∈ G'):=by
    rcases hb with hbL | ⟨hbn,hbG⟩
    . rcases mem_insert.mp hbL with rfl | h
      . exact Or.inr ⟨by omega,by simpa using hjv'⟩
      . exact Or.inl (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    . exact Or.inr ⟨hbn,Finset.mem_of_mem_erase hbG⟩
   unfold gMap at heq
   by_cases ha0 : a=n+jv' <;> by_cases hb0 : b=n+jv'
   . exact ha0.trans hb0.symm
   . rw [if_pos ha0,if_neg hb0] at heq;exact absurd heq.symm (hLF b hb')
   . rw [if_neg ha0,if_pos hb0] at heq;exact absurd heq (hLF a ha')
   . rw [if_neg ha0,if_neg hb0] at heq;exact hinvW_inj a b ha' hb' heq
lemma otLIn {n : ℕ} {D C : Circuit} {G' L' : Finset ℕ} {ρ' v' j1 leaf_new : ℕ}
 (ht : IsOrTree n D G' L' ρ')
 (hv' : v' ∈ L'\/(n<=v'/\v' - n ∈ G'))
 (fG : ℕ->ℕ) (invW : ℕ->ℕ)
 (hfG_inj : Set.InjOn fG (G' : Set ℕ))
 (hIWG : ∀ j' ∈ G',invW (n+j')=n+fG j')
 (hinvW_inj : ∀ a b,(a ∈ L'\/(n<=a/\a - n ∈ G'))->(b ∈ L'\/(n<=b/\b - n ∈ G')) →
  invW a=invW b->a=b)
 (hj1_fresh : ∀ a,(a ∈ L'\/(n<=a/\a - n ∈ G'))->invW a≠n+j1)
 (hLF : ∀ a,(a ∈ L'\/(n<=a/\a - n ∈ G'))->invW a≠leaf_new)
 (hleaf_ne_j1 : leaf_new≠n+j1)
 (hj1_op : (gateAt C j1).op=.or)
 (hj1_in : (gateAt C j1).inputs=[leaf_new,invW v']\/(gateAt C j1).inputs=[invW v',leaf_new])
 (hgate_op : ∀ j' ∈ G',(gateAt C (fG j')).op=(gateAt D j').op)
 (hgate_in : ∀ j' ∈ G',(gateAt C (fG j')).inputs =
  (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else invW w')) :
 IsOrTree n C (insert j1 (G'.image fG)) (insert leaf_new (L'.image invW))
  (if ρ'=v' then n+j1 else invW ρ'):=by
 obtain ⟨hg,hl,hgg,hroot⟩:=ht
 have hρnode : ρ' ∈ L'\/(n <= ρ' /\ ρ' - n ∈ G'):=by
  by_cases hGe : G'=∅
  . rw [if_pos hGe] at hroot;left;rw [hroot];simp
  . rw [if_neg hGe] at hroot;obtain ⟨j',hj',rfl⟩:=hroot;right;exact ⟨by omega,by simpa using hj'⟩
 have hj1_not_img : j1 ∉ G'.image fG:=by
  intro h;obtain ⟨j',hj',hjeq⟩:=mem_image.mp h
  exact hj1_fresh (n+j') (Or.inr ⟨by omega,by simpa using hj'⟩) (by rw [hIWG j' hj',hjeq])
 let gMap (w' : ℕ) : ℕ:=if w'=v' then n+j1 else invW w'
 have hgMap_inj : ∀ a b,(a ∈ L'\/(n<=a/\a - n ∈ G'))->(b ∈ L'\/(n<=b/\b - n ∈ G')) →
  gMap a=gMap b->a=b:=by
  intro a b ha hb heq;unfold gMap at heq
  by_cases ha0 : a=v' <;> by_cases hb0 : b=v'
  . exact ha0.trans hb0.symm
  . rw [if_pos ha0,if_neg hb0] at heq;exact absurd heq.symm (hj1_fresh b hb)
  . rw [if_neg ha0,if_pos hb0] at heq;exact absurd heq (hj1_fresh a ha)
  . rw [if_neg ha0,if_neg hb0] at heq;exact hinvW_inj a b ha hb heq
 have hreads_img : ∀ u : ℕ,readsIn C (G'.image fG) u =
  ∑ j' ∈ G',((gateAt D j').inputs.map gMap).count u:=by
  intro u;unfold readsIn
  rw [sum_image (fun a ha b hb h => hfG_inj ha hb h)]
  exact sum_congr rfl fun j' hj' => by rw [hgate_in j' hj']
 have hreads_gMap : ∀ w',(w' ∈ L'\/(n<=w'/\w' - n ∈ G')) →
  readsIn C (G'.image fG) (gMap w')=readsIn D G' w':=by
  intro w' hw'
  rw [hreads_img]
  refine sum_congr rfl fun j' hj' => ?_
  have hmap_in : ∀ i ∈ (gateAt D j').inputs,i ∈ L'\/(n<=i/\i - n ∈ G'):=(hg j' hj').2.2
  generalize (gateAt D j').inputs=xs at hmap_in
  induction xs with
  | nil => simp
  | cons x xs ih =>
   simp only [List.map_cons,List.count_cons]
   have hx:=hmap_in x (by simp)
   have hbeq : (gMap x == gMap w')=(x == w'):=by
    apply Bool.eq_iff_iff.mpr;simp only [beq_iff_eq]
    exact ⟨fun h => hgMap_inj x w' hx hw' h,fun h => by rw [h]⟩
   rw [hbeq,ih (fun i hi => hmap_in i (by simp [hi]))]
 have hreads_zero_of_not_gMap : ∀ u,(∀ w',(w' ∈ L'\/(n<=w'/\w' - n ∈ G'))->gMap w'≠u) →
  readsIn C (G'.image fG) u=0:=by
  intro u hne
  rw [hreads_img]
  apply sum_eq_zero;intro j' hj'
  rw [List.count_eq_zero];intro hmem
  obtain ⟨w',hw'mem,hw'eq⟩:=List.mem_map.mp hmem
  exact hne w' ((hg j' hj').2.2 w' hw'mem) hw'eq
 have hRI : ∀ u,readsIn C (insert j1 (G'.image fG)) u =
  readsIn C (G'.image fG) u+(if u=leaf_new then 1 else 0)+(if u=invW v' then 1 else 0):=by
  intro u;unfold readsIn
  rw [Finset.sum_insert hj1_not_img]
  have hne_lv : leaf_new≠invW v':=(hLF v' hv').symm
  rcases hj1_in with h | h <;> rw [h]
  . simp only [List.count_cons,List.count_nil,beq_iff_eq]
    by_cases h1 : u=leaf_new
    . subst h1;simp [hne_lv,hne_lv.symm];omega
    . have h1' : leaf_new≠u:=Ne.symm h1
      by_cases h2 : u=invW v'
      . subst h2;simp [h1,h1'];omega
      . have h2' : invW v'≠u:=Ne.symm h2;simp [h1,h1',h2,h2']
  . simp only [List.count_cons,List.count_nil,beq_iff_eq]
    by_cases h1 : u=leaf_new
    . subst h1;simp [hne_lv,hne_lv.symm];omega
    . have h1' : leaf_new≠u:=Ne.symm h1
      by_cases h2 : u=invW v'
      . subst h2;simp [h1,h1'];omega
      . have h2' : invW v'≠u:=Ne.symm h2;simp [h1,h1',h2,h2']
 have hreads_v_zero : readsIn C (G'.image fG) (invW v')=0:=by
  apply hreads_zero_of_not_gMap;intro w' hw' heq
  unfold gMap at heq
  by_cases h : w'=v'
  . rw [if_pos h] at heq;exact hj1_fresh v' hv' heq.symm
  . rw [if_neg h] at heq;exact h (hinvW_inj w' v' hw' hv' heq)
 have hreads_leaf_zero : readsIn C (G'.image fG) leaf_new=0:=by
  apply hreads_zero_of_not_gMap;intro w' hw' heq
  unfold gMap at heq
  by_cases h : w'=v'
  . rw [if_pos h] at heq;exact hleaf_ne_j1 heq.symm
  . rw [if_neg h] at heq;exact hLF w' hw' heq
 refine ⟨?_,?_,?_,?_⟩
 . intro j hj
   rcases mem_insert.mp hj with rfl | hjI
   . refine ⟨hj1_op,by rcases hj1_in with h | h <;> simp [h],?_⟩
     intro i hi
     rcases hj1_in with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl
     . exact Or.inl (mem_insert_self _ _)
     . rcases hv' with hvL | ⟨hvn,hvG⟩
       . exact Or.inl (mem_insert_of_mem (mem_image.mpr ⟨v',hvL,rfl⟩))
       . have hveq : n+(v' - n)=v':=by omega
         rw [← hveq,hIWG (v' - n) hvG]
         exact Or.inr ⟨by omega,mem_insert_of_mem (by simpa using mem_image.mpr ⟨v' - n,hvG,rfl⟩)⟩
     . rcases hv' with hvL | ⟨hvn,hvG⟩
       . exact Or.inl (mem_insert_of_mem (mem_image.mpr ⟨v',hvL,rfl⟩))
       . have hveq : n+(v' - n)=v':=by omega
         rw [← hveq,hIWG (v' - n) hvG]
         exact Or.inr ⟨by omega,mem_insert_of_mem (by simpa using mem_image.mpr ⟨v' - n,hvG,rfl⟩)⟩
     . exact Or.inl (mem_insert_self _ _)
   . obtain ⟨j',hj',rfl⟩:=mem_image.mp hjI
     refine ⟨by rw [hgate_op j' hj',(hg j' hj').1],
      by rw [hgate_in j' hj',List.length_map,(hg j' hj').2.1],?_⟩
     intro i hi;rw [hgate_in j' hj'] at hi
     obtain ⟨w',hw'mem,rfl⟩:=List.mem_map.mp hi
     by_cases hwv : w'=v'
     . rw [if_pos hwv];exact Or.inr ⟨by omega,by simpa using mem_insert_self j1 _⟩
     . rw [if_neg hwv]
       rcases (hg j' hj').2.2 w' hw'mem with hwL | ⟨hwn,hwG⟩
       . exact Or.inl (mem_insert_of_mem (mem_image.mpr ⟨w',hwL,rfl⟩))
       . have hweq : n+(w' - n)=w':=by omega
         rw [← hweq,hIWG (w' - n) hwG]
         exact Or.inr ⟨by omega,mem_insert_of_mem (by simpa using mem_image.mpr ⟨w' - n,hwG,rfl⟩)⟩
 . intro w hw
   rcases mem_insert.mp hw with rfl | hwI
   . refine ⟨?_,?_⟩
     . rintro ⟨hwn,hwG⟩
       rcases mem_insert.mp hwG with h1 | h2
       . exact hleaf_ne_j1 (by omega)
       . obtain ⟨j',hj',hjeq⟩:=mem_image.mp h2
         exact hLF (n+j') (Or.inr ⟨by omega,by simpa using hj'⟩) (by rw [hIWG j' hj'];omega)
     . have hne_r : w≠if ρ'=v' then n+j1 else invW ρ':=by
        split_ifs with h
        . exact hleaf_ne_j1
        . exact (hLF ρ' hρnode).symm
       rw [if_neg hne_r,hRI,hreads_leaf_zero,if_pos rfl,if_neg (hLF v' hv').symm]
   . obtain ⟨w',hw'L,rfl⟩:=mem_image.mp hwI
     refine ⟨?_,?_⟩
     . rintro ⟨hwn,hwG⟩
       rcases mem_insert.mp hwG with h1 | h2
       . exact hj1_fresh w' (Or.inl hw'L) (by omega)
       . obtain ⟨j',hj',hjeq⟩:=mem_image.mp h2
         have heq:=hinvW_inj w' (n+j') (Or.inl hw'L) (Or.inr ⟨by omega,by simpa using hj'⟩)
          (by rw [hIWG j' hj'];omega)
         exact (hl w' hw'L).1 ⟨by omega,by simpa [heq] using hj'⟩
     . rw [hRI,if_neg (hLF w' (Or.inl hw'L))]
       by_cases hwv : w'=v'
       . subst hwv
         have hne_r : invW w'≠if ρ'=w' then n+j1 else invW ρ':=by
          split_ifs with h
          . exact hj1_fresh w' (Or.inl hw'L)
          . exact fun heq => h (hinvW_inj w' ρ' (Or.inl hw'L) hρnode heq).symm
         rw [if_neg hne_r,hreads_v_zero,if_pos rfl]
       . have hne_v : invW w'≠invW v':=fun heq => hwv (hinvW_inj w' v' (Or.inl hw'L) hv' heq)
         have hgm : gMap w'=invW w':=by simp [gMap,hwv]
         have hr_eq : readsIn C (G'.image fG) (invW w')=readsIn D G' w':=by
          rw [← hgm];exact hreads_gMap w' (Or.inl hw'L)
         rw [if_neg hne_v,hr_eq,(hl w' hw'L).2]
         by_cases hρv : ρ'=v'
         . rw [if_pos hρv,if_neg (by omega : w' ≠ ρ'),if_neg (hj1_fresh w' (Or.inl hw'L))]
         . rw [if_neg hρv]
           by_cases hwρ : w'=ρ'
           . subst hwρ;simp
           . have hne : invW w'≠invW ρ':=fun heq => hwρ (hinvW_inj w' ρ' (Or.inl hw'L) hρnode heq)
             simp [hwρ,hne]
 . intro j hj
   rcases mem_insert.mp hj with rfl | hjI
   . rw [hRI,if_neg hleaf_ne_j1.symm,if_neg (hj1_fresh v' hv').symm]
     have hgm : gMap v'=n+j:=by simp [gMap]
     have hr_eq : readsIn C (G'.image fG) (n+j)=readsIn D G' v':=by
      rw [← hgm];exact hreads_gMap v' hv'
     rw [hr_eq]
     have hv_reads : readsIn D G' v'=if v'=ρ' then 0 else 1:=by
      rcases hv' with hvL | ⟨hvn,hvG⟩
      . exact (hl v' hvL).2
      . have hveq : n+(v' - n)=v':=by omega
        have h:=hgg (v' - n) hvG;rw [hveq] at h;exact h
     rw [hv_reads]
     by_cases hρv : ρ'=v'
     . rw [if_pos hρv,if_pos rfl,if_pos hρv.symm]
     . rw [if_neg hρv,if_neg (Ne.symm hρv),if_neg (hj1_fresh ρ' hρnode).symm]
   . obtain ⟨j',hj',rfl⟩:=mem_image.mp hjI
     have hnode : n+j' ∈ L'\/(n<=n+j'/\(n+j') - n ∈ G'):=Or.inr ⟨by omega,by simpa using hj'⟩
     rw [← hIWG j' hj',hRI,if_neg (hLF (n+j') hnode)]
     by_cases hjv : n+j'=v'
     . rw [hjv,hreads_v_zero,if_pos rfl]
       have hne_r : invW v'≠if ρ'=v' then n+j1 else invW ρ':=by
        split_ifs with h
        . exact hj1_fresh v' hv'
        . exact fun heq => h (hinvW_inj v' ρ' hv' hρnode heq).symm
       rw [if_neg hne_r]
     . have hne_v : invW (n+j')≠invW v':=fun heq => hjv (hinvW_inj (n+j') v' hnode hv' heq)
       have hgm : gMap (n+j')=invW (n+j'):=by simp [gMap,hjv]
       have hr_eq : readsIn C (G'.image fG) (invW (n+j'))=readsIn D G' (n+j'):=by
        rw [← hgm];exact hreads_gMap (n+j') hnode
       rw [if_neg hne_v,hr_eq,hgg j' hj']
       by_cases hρv : ρ'=v'
       . rw [if_pos hρv,if_neg (by omega : n+j' ≠ ρ'),if_neg (hj1_fresh (n+j') hnode)]
       . rw [if_neg hρv]
         by_cases hjρ : n+j'=ρ'
         . rw [hjρ];simp
         . have hne : invW (n+j')≠invW ρ':=fun heq => hjρ (hinvW_inj (n+j') ρ' hnode hρnode heq)
           simp [hjρ,hne]
 . rw [if_neg (Finset.insert_ne_empty j1 _)]
   by_cases hρv : ρ'=v'
   . rw [if_pos hρv];exact ⟨j1,mem_insert_self _ _,rfl⟩
   . rw [if_neg hρv]
     have hGe : G' ≠ ∅:=by
      intro hGe;rw [if_pos hGe] at hroot
      rcases hv' with hvL | ⟨_,hvG⟩
      . rw [hroot,mem_singleton] at hvL;exact hρv hvL.symm
      . rw [hGe] at hvG;simp at hvG
     rw [if_neg hGe] at hroot
     obtain ⟨j',hj',rfl⟩:=hroot
     exact ⟨fG j',mem_insert_of_mem (mem_image.mpr ⟨j',hj',rfl⟩),hIWG j' hj'⟩
lemma icORZ {n : ℕ} {C : Circuit} {d : NCCData n}
 (hrb : ReadsBack n C) {G : Finset ℕ} {t : Fin n} (ht : t ∈ d.cover)
 (hGz : ∀ j ∈ G,j < C.gates.length/\(d.role j).1=Kind.z)
 {w : ℕ} (hreach : OrReach n C G w t.val) : IsCentred n C d w:=by
 induction hreach using ReflTransGen.head_induction_on with
 | refl => exact (isCentred_input n C d t).mpr ht
 | head hstep _ ih =>
  obtain ⟨j,hjG,rfl,hmem⟩:=hstep
  exact (isCentred_gate n C d hrb j (hGz j hjG).1).mpr ⟨(hGz j hjG).2,_,hmem,ih⟩
lemma orLI {n : ℕ} {D C : Circuit} {G' : Finset ℕ}
 {fG gMap : ℕ->ℕ}
 (hgMap_gate : ∀ j' ∈ G',gMap (n+j')=n+fG j')
 (hgate_in : ∀ j' ∈ G',(gateAt C (fG j')).inputs=(gateAt D j').inputs.map gMap)
 {u' v' : ℕ} (hreach : OrReach n D G' u' v') :
 OrReach n C (G'.image fG) (gMap u') (gMap v'):=by
 induction hreach with
 | refl => exact ReflTransGen.refl
 | tail _ hstep ih =>
  obtain ⟨j',hj',rfl,hmem⟩:=hstep
  refine ReflTransGen.tail ih ⟨fG j',mem_image.mpr ⟨j',hj',rfl⟩,
   hgMap_gate j' hj',?_⟩
  rw [hgate_in j' hj'];exact List.mem_map.mpr ⟨_,hmem,rfl⟩
lemma valNN {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) :
 ∀ g ∈ C.gates,g.op=.and\/g.op=.or:=by
 intro g hg
 obtain ⟨j,hj,rfl⟩:=List.mem_iff_getElem.mp hg
 rw [← gateAt_eq_getElem C j hj]
 rcases hv.2.2.2.2.1 j hj with htop | ⟨t,ht,hrt,hrb⟩
 . exact Or.inr (hv.2.2.2.2.2.2.1 j (mem_filter.mpr ⟨mem_range.mpr hj,htop⟩)).1
 . cases hk : (d.role j).1 with
   | top => exact Or.inr (hv.2.2.2.2.2.2.1 j (mem_filter.mpr ⟨mem_range.mpr hj,hk⟩)).1
   | z => exact Or.inr ((hv.2.2.2.2.2.1 t ht).2.1.1 j (mem_filter.mpr ⟨mem_range.mpr hj,Prod.ext hk hrt⟩)).1
   | o => exact Or.inr ((hv.2.2.2.2.2.1 t ht).2.2.1.1 j (mem_filter.mpr ⟨mem_range.mpr hj,Prod.ext hk hrt⟩)).1
   | b =>
    obtain ⟨j',hj',hbw',_,hop,_⟩:=(hv.2.2.2.2.2.1 t ht).1
    have hbw:=hrb hk
    have hjj : j=j':=by omega
    subst hjj;exact Or.inl hop
lemma isoNMC {n : ℕ} {K : SimpleGraph (Fin n)} {T : Finset (Fin n)}
 (hmin : IsMinCover K T) {v : Fin n} (hiso : ∀ w,¬ K.Adj v w) : v ∉ T:=by
 intro hvT
 have hcov : K.IsVertexCover ((T.erase v : Finset (Fin n)) : Set (Fin n)):=by
  intro a b hab
  have hav : a≠v:=fun h => hiso b (h ▸ hab)
  have hbv : b≠v:=fun h => hiso a (h ▸ hab.symm)
  rcases hmin.1 hab with ha | hb
  . exact Or.inl (mem_erase.mpr ⟨hav,ha⟩)
  . exact Or.inr (mem_erase.mpr ⟨hbv,hb⟩)
 have hle:=hmin.2 (T.erase v) hcov
 have hlt:=card_erase_lt_of_mem hvT
 omega
lemma ownHOE {n : ℕ} {K : SimpleGraph (Fin n)} {A : Finset (Fin n)}
 {C : Circuit} {d : NCCData n} (hv : Valid n K A C d) {t : Fin n} (ht : t ∈ d.cover) :
 ∃ r : Fin n,d.owns t r=true:=by
 have ho:=tree_card n C _ _ _ (hv.2.2.2.2.2.1 t ht).2.2.1
 have hpos : 0 < (oLeaves d t).card:=by omega
 obtain ⟨w,hw⟩:=card_pos.mp hpos
 obtain ⟨r,hr,_⟩:=mem_image.mp hw
 exact ⟨r,(mem_filter.mp hr).2⟩
set_option maxHeartbeats 800000 in
lemma fwd2b {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (htf : ∀ a b c : Fin n,K.Adj a b->K.Adj b c->K.Adj a c->False)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {C : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A)
 {j0 j1 u v v' out' : ℕ} (hj01 : j0 < j1) (hj1 : j1 < C.gates.length)
 (huniq_l : ∀ j < C.gates.length,j≠j0->l.val ∉ eIn (gateAt C j))
 (huniq1 : ∀ j < C.gates.length,j≠j1->n+j0 ∉ eIn (gateAt C j))
 (hop0 : (gateAt C j0).op=.or)
 (huin : (gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val])
 (hult : u < n+j0) (hul : u≠l.val)
 (hop1 : (gateAt C j1).op=.and)
 (hvin : (gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0])
 (hvlt : v < n+j1) (hv0 : v≠n+j0) (hvl : v≠l.val)
 (hdel_eq : (Finset.range C.gates.length).filter (fun j => isD n l true C j=true)={j0,j1})
 (hcj0 : evE (sPfx n l true C.gates (j0+1)).2 (n+j0)=Sum.inl true)
 (hJ1I : evE (sPfx n l true C.gates (j1+1)).2 (n+j1)=Sum.inr v')
 (hOEv : evE (sPfx n l true C.gates C.gates.length).2 C.output=Sum.inr out')
 {d' : NCCData n}
 (hvD : Valid n K2 (insert p A) ⟨(sPfx n l true C.gates C.gates.length).1,out'⟩ d') :
 IsNestedCoverCircuit n K A C:=by
 obtain ⟨hlp,hpq,hlA,hpA,hqA,_,_,_⟩:=gArith K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 obtain ⟨hncK,_,_⟩:=graphFun_nonconst_helpers K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hncC : ∃ x y,circuitFun n C x≠circuitFun n C y:=by rw [hfun];exact hncK
 obtain ⟨hD_len,hWME,hKF,hIF,hOE,hval_T⟩ :=
  twoDS hmin hncC hj01 hj1 hdel_eq hcj0 hJ1I hOEv (valNN hvD)
 revert hvD hD_len hKF hIF hOE hval_T
 generalize hD_def : (⟨(sPfx n l true C.gates C.gates.length).1,out'⟩ : Circuit)=D
 intro hvD hD_len hKF hIF hOE hval_T
 have hrbC : ReadsBack n C:=by
  intro j hj i hi
  by_cases h0 : j=j0
  . subst h0;rcases huin with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl
    . exact Nat.lt_of_lt_of_le l.isLt (Nat.le_add_right _ _)
    . exact hult
    . exact hult
    . exact Nat.lt_of_lt_of_le l.isLt (Nat.le_add_right _ _)
  . by_cases h1 : j=j1
    . subst h1;rcases hvin with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl <;> omega
    . exact ((hKF j hj h0 h1).2.2 i hi).1
 have hpNC : p ∉ d'.cover :=
  isoNMC hvD.2.1 (fun w hw => ((hK2 p w).mp hw).2.2.1 rfl)
 have hlNC : l ∉ d'.cover :=
  isoNMC hvD.2.1 (fun w hw => ((hK2 l w).mp hw).2.1 rfl)
 have hv_eq : v=iW n j0 j1 v':=by
  have h1 : evE (sPfx n l true C.gates j1).2 v=Sum.inr v':=by
   have hstep : evE (sPfx n l true C.gates (j1+1)).2 (n+j1) =
    evE (sGt n (sPfx n l true C.gates j1) (gateAt C j1)).2
     (sPfx n l true C.gates j1).2.length:=by
    rw [simplifyPrefix_succ n l true C j1 hj1,simplifyPrefix_env_len n l true C j1 (by omega)]
   rw [hstep] at hJ1I
   have h0e : evE (sPfx n l true C.gates j1).2 (n+j0)=Sum.inl true:=by
    rw [spEnvS n l true C (by omega : j0+1<=j1) (by omega) (by omega),hcj0]
   rcases hst : sPfx n l true C.gates j1 with ⟨gs,env⟩
   rw [hst] at hJ1I h0e
   rcases hvin with h | h
   . simp only [sGt,hop1,h] at hJ1I
     rw [h0e] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I;exact hJ1I
   . simp only [sGt,hop1,h] at hJ1I
     cases hve : evE env v with
     | inl c =>
      rw [hve] at hJ1I
      cases c with
      | false => simp [evE,List.getD_eq_getElem?_getD] at hJ1I
      | true => rw [h0e] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I
     | inr w' =>
      rw [hve,h0e] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I;rw [hJ1I]
  have h2 : evE (sPfx n l true C.gates C.gates.length).2 v=Sum.inr v':=by
   rw [spEnvS n l true C (by omega : j1<=C.gates.length) le_rfl hvlt,h1]
  have h3:=hWME v (by omega) hvl hv0
  rw [h2] at h3
  have hw : wM n j0 j1 v' v=v':=(Sum.inr.inj h3).symm
  rcases (wMEq hj01 hv0).mp hw with ⟨habs,_⟩ | ⟨_,heq⟩
  . omega
  . exact heq
 let u':=wM n j0 j1 v' u
 have hu_eq : u=iW n j0 j1 u':=by
  rcases (wMEq hj01 (by omega : u≠n+j0)).mp (rfl : wM n j0 j1 v' u=u') with ⟨habs,_⟩ | ⟨_,heq⟩
  . omega
  . exact heq
 have hv'_lt : v' < n+D.gates.length:=by
  have hinv:=spInv n l true C hmin.1 C.gates.length le_rfl
  have h:=hinv.2.2 (fun _ => false) (n+j1) (by omega)
  rw [spEnvS n l true C (by omega : j1+1<=C.gates.length) le_rfl (by omega),hJ1I] at h
  rw [← hD_def];exact h.1
 have hu'_lt : u' < n+D.gates.length:=by
  have hinv:=spInv n l true C hmin.1 C.gates.length le_rfl
  have h:=hinv.2.2 (fun _ => false) u (by omega)
  rw [hWME u (by omega) hul (by omega)] at h
  rw [← hD_def];exact h.1
 have hval_early : ∀ (x : Fin n->Bool) (w : ℕ),w < n+j1->w≠l.val->w≠n+j0 →
  wV n C x w=wV n D x (wM n j0 j1 v' w):=by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro hwlt hwl hw0
   by_cases hwn : w < n
   . let wf : Fin n:=⟨w,hwn⟩
     unfold wM;rw [if_pos hwn]
     change wV n C x wf.val=wV n D x wf.val
     rw [wvI,wvI]
   . have hj : w - n < C.gates.length:=by omega
     have hweq : n+(w - n)=w:=by omega
     have hne0 : w - n≠j0:=by omega
     have hne1 : w - n≠j1:=by omega
     have hIL : iM j0 j1 (w - n) < D.gates.length:=by
      have:=iMLt hj01 hj1 hj hne0 hne1;omega
     have hwm : wM n j0 j1 v' w=n+iM j0 j1 (w - n):=by
      unfold wM;rw [if_neg hwn,if_neg (by omega)]
     rw [hwm]
     conv_lhs => rw [← hweq]
     rw [wvGR n C hrbC x (w - n) hj,
      wvGR n D hvD.1 x (iM j0 j1 (w - n)) hIL]
     obtain ⟨hop,hinD,hsub⟩:=hKF (w - n) hj hne0 hne1
     rw [hop,hinD,List.map_map]
     congr 1
     refine List.map_congr_left fun i hi => ?_
     obtain ⟨hi1,hi2,hi3⟩:=hsub i hi
     exact ih i (by omega) (by omega) hi2 hi3
 have hval_u : ∀ x : Fin n->Bool,wV n C x u=wV n D x u':=fun x =>
  hval_early x u (by omega) hul (by omega)
 have hval_v : ∀ x : Fin n->Bool,wV n C x v=wV n D x v':=fun x => by
  have h:=hval_early x v hvlt hvl hv0
  have hwm : wM n j0 j1 v' v=v':=by rw [hv_eq,wireMap_invWire hj01]
  rwa [hwm] at h
 have hval_j0 : ∀ x : Fin n->Bool,wV n C x (n+j0)=(x l || wV n D x u'):=by
  intro x
  rw [wvGR n C hrbC x j0 (by omega),hop0]
  rcases huin with h | h <;> rw [h] <;> simp [GateOp.eval,wvI,hval_u,Bool.or_comm]
 have hval_j1 : ∀ x : Fin n->Bool,
  wV n C x (n+j1)=((x l || wV n D x u') && wV n D x v'):=by
  intro x
  rw [wvGR n C hrbC x j1 hj1,hop1]
  rcases hvin with h | h <;> rw [h] <;> simp [GateOp.eval,hval_j0,hval_v,Bool.and_comm]
 let xp : Fin n->Bool:=fun i => decide (i=p)
 have hxp_K : graphFun K A xp=false:=by
  simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
  refine ⟨fun a ha hxa => hpA ((by simpa [xp] using hxa : a=p) ▸ ha),fun a b hab hxa hxb => ?_⟩
  have ha : a=p:=by simpa [xp] using hxa
  have hb : b=p:=by simpa [xp] using hxb
  subst ha;subst hb;exact hab.ne rfl
 have hxp_K2 : graphFun K2 (insert p A) xp=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inl ⟨p,mem_insert_self _ _,by simp [xp]⟩
 have hxp_D_nonTop : ∀ w' < n+D.gates.length,
  (¬ (w' ∈ topLeaves d' (insert p A)\/(n<=w'/\w' - n ∈ topGates d' D))) →
  wV n D xp w'=false:=by
  intro w'
  induction w' using Nat.strong_induction_on with
  | ind w' ih =>
   intro hw'lt hnotTop
   by_cases hwn : w' < n
   . let wf : Fin n:=⟨w',hwn⟩
     have hnep : wf≠p:=fun h => hnotTop (Or.inl (mem_union_left _
      (mem_image.mpr ⟨p,mem_insert_self _ _,(congrArg Fin.val h).symm⟩)))
     change wV n D xp wf.val=false
     rw [wvI];simp [xp,hnep]
   . have hj' : w' - n < D.gates.length:=by omega
     have hweq : n+(w' - n)=w':=by omega
     rcases hvD.2.2.2.2.1 (w' - n) hj' with htop | ⟨t,ht,hrt,hrb⟩
     . exfalso;exact hnotTop (Or.inr ⟨by omega,mem_filter.mpr ⟨mem_range.mpr hj',htop⟩⟩)
     . cases hk : (d'.role (w' - n)).1 with
       | top => exfalso;exact hnotTop (Or.inr ⟨by omega,mem_filter.mpr ⟨mem_range.mpr hj',hk⟩⟩)
       | z =>
        have hjG : w' - n ∈ gatesOf d' D Kind.z t.val :=
         mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
        apply Bool.eq_false_iff.mpr;intro htrue
        obtain ⟨lz,hlzL,_,hlzt⟩ :=
         (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.1 xp (Or.inr ⟨by omega,hjG⟩)).mp htrue
        unfold zLeaves at hlzL
        rcases mem_insert.mp hlzL with rfl | himg
        . rw [wvI] at hlzt;exact hpNC ((by simpa [xp] using hlzt : t=p) ▸ ht)
        . obtain ⟨s,hs,rfl⟩:=mem_image.mp himg
          obtain ⟨u1,u2,hadj,hxu1,hxu2⟩:=nccBS hvD xp (d'.bw s) s (mem_filter.mp hs).1 rfl hlzt
          have h1 : u1=p:=by simpa [xp] using hxu1
          have h2 : u2=p:=by simpa [xp] using hxu2
          subst h1;subst h2;exact hadj.ne rfl
       | o =>
        have hjG : w' - n ∈ gatesOf d' D Kind.o t.val :=
         mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
        apply Bool.eq_false_iff.mpr;intro htrue
        obtain ⟨lo,hloL,_,hlot⟩ :=
         (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1 xp (Or.inr ⟨by omega,hjG⟩)).mp htrue
        obtain ⟨r,hr,rfl⟩:=mem_image.mp hloL
        have hown : d'.owns t r=true:=(mem_filter.mp hr).2
        have hrp : r≠p:=((hK2 t r).mp (hvD.2.2.1.1 t r hown).1).2.2.2.2
        have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
        unfold LamOK at hlam
        by_cases hrc : r ∈ d'.cover
        . rw [if_pos hrc] at hlam
          have hnode : d'.lam t r ∈ zLeaves d' r\/(n<=d'.lam t r/\d'.lam t r - n ∈ gatesOf d' D Kind.z r.val):=by
           rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
           . left;rw [h1];exact mem_insert_self _ _
           . right;refine ⟨by omega,?_⟩
             have : d'.lam t r - n=k:=by omega
             rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
          obtain ⟨lz,hlzL,_,hlzt⟩:=(otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 r hrc).2.1 xp hnode).mp hlot
          unfold zLeaves at hlzL
          rcases mem_insert.mp hlzL with rfl | himg
          . rw [wvI] at hlzt;exact hrp (by simpa [xp] using hlzt)
          . obtain ⟨s,hs,rfl⟩:=mem_image.mp himg
            obtain ⟨u1,u2,hadj,hxu1,hxu2⟩:=nccBS hvD xp (d'.bw s) s (mem_filter.mp hs).1 rfl hlzt
            have h1 : u1=p:=by simpa [xp] using hxu1
            have h2 : u2=p:=by simpa [xp] using hxu2
            subst h1;subst h2;exact hadj.ne rfl
        . rw [if_neg hrc] at hlam;rw [hlam,wvI] at hlot
          exact hrp (by simpa [xp] using hlot)
       | b =>
        have hbw : d'.bw t=w':=by have:=hrb hk;omega
        apply Bool.eq_false_iff.mpr;intro htrue
        obtain ⟨u1,u2,hadj,hxu1,hxu2⟩:=nccBS hvD xp w' t ht hbw htrue
        have h1 : u1=p:=by simpa [xp] using hxu1
        have h2 : u2=p:=by simpa [xp] using hxu2
        subst h1;subst h2;exact hadj.ne rfl
 have hxp_D_top_iff : ∀ w',(w' ∈ topLeaves d' (insert p A)\/(n<=w'/\w' - n ∈ topGates d' D)) →
  (wV n D xp w'=true↔OrReach n D (topGates d' D) w' p.val):=by
  intro w' hw'
  rw [otEI hvD.1 topGates_lt hvD.2.2.2.2.2.2 xp hw']
  constructor
  . rintro ⟨wl,hwlL,hreach,hwlt⟩
    unfold topLeaves at hwlL
    rcases mem_union.mp hwlL with ha | ht
    . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
      rw [wvI] at hwlt
      have hap : a=p:=by simpa [xp] using hwlt
      rwa [← hap]
    . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
      exfalso
      obtain ⟨u1,u2,hadj,hxu1,hxu2⟩:=nccBS hvD xp (d'.bw t) t (mem_filter.mp htF).1 rfl hwlt
      have h1 : u1=p:=by simpa [xp] using hxu1
      have h2 : u2=p:=by simpa [xp] using hxu2
      subst h1;subst h2;exact hadj.ne rfl
  . intro hreach
    exact ⟨p.val,mem_union_left _ (mem_image.mpr ⟨p,mem_insert_self _ _,rfl⟩),
     hreach,by rw [wvI];simp [xp]⟩
 have hv'_xp_true : wV n D xp v'=true:=by
  by_contra hfv
  have hfv' : wV n D xp v'=false:=Bool.eq_false_iff.mpr hfv
  have hj1_xp : wV n C xp (n+j1)=false:=by rw [hval_j1,hfv'];simp
  have hall : ∀ w < n+C.gates.length,w≠l.val->w≠n+j0 →
   wV n C xp w=wV n D xp (wM n j0 j1 v' w):=by
   intro w
   induction w using Nat.strong_induction_on with
   | ind w ih =>
    intro hwlt hwl hw0
    by_cases hw1 : w=n+j1
    . subst hw1;unfold wM;rw [if_neg (by omega),if_pos rfl,hj1_xp,hfv']
    . by_cases hwn : w < n
      . let wf : Fin n:=⟨w,hwn⟩
        unfold wM;rw [if_pos hwn]
        change wV n C xp wf.val=wV n D xp wf.val
        rw [wvI,wvI]
      . have hj : w - n < C.gates.length:=by omega
        have hweq : n+(w - n)=w:=by omega
        have hne0 : w - n≠j0:=by omega
        have hne1 : w - n≠j1:=by omega
        have hIL : iM j0 j1 (w - n) < D.gates.length:=by
         have:=iMLt hj01 hj1 hj hne0 hne1;omega
        have hwm : wM n j0 j1 v' w=n+iM j0 j1 (w - n):=by
         unfold wM;rw [if_neg hwn,if_neg hw1]
        rw [hwm]
        conv_lhs => rw [← hweq]
        rw [wvGR n C hrbC xp (w - n) hj,
         wvGR n D hvD.1 xp (iM j0 j1 (w - n)) hIL]
        obtain ⟨hop,hinD,hsub⟩:=hKF (w - n) hj hne0 hne1
        rw [hop,hinD,List.map_map]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        obtain ⟨hi1,hi2,hi3⟩:=hsub i hi
        exact ih i (by omega) (by omega) hi2 hi3
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
  have hOL : C.output < n+C.gates.length:=by have:=outLst hmin hncC hne_g;omega
  have hout_ne_l : C.output≠l.val:=by have:=outLst hmin hncC hne_g;omega
  have hout_ne_0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
  have hCxp:=hall C.output hOL hout_ne_l hout_ne_0
  rw [← hOE,wvO,wvO,hfun,nccEv hvD,hxp_K,hxp_K2] at hCxp
  cases hCxp
 have hvTp : v' ∈ topLeaves d' (insert p A)\/(n<=v'/\v' - n ∈ topGates d' D):=by
  by_contra hnot
  have:=hxp_D_nonTop v' hv'_lt hnot
  rw [hv'_xp_true] at this;cases this
 have hv'_reaches_p : OrReach n D (topGates d' D) v' p.val:=(hxp_D_top_iff v' hvTp).mp hv'_xp_true
 have hvPT : v'=p.val\/(n<=v'/\v' - n ∈ topGates d' D):=by
  rcases hvTp with hvL | hvG
  . left
    have hno_step : ∀ w,¬ OrStep n D (topGates d' D) v' w:=by
     rintro w ⟨k,hkG,rfl,_⟩
     exact (hvD.2.2.2.2.2.2.2.1 (n+k) hvL).1 ⟨by omega,by simpa using hkG⟩
    rcases ReflTransGen.cases_head hv'_reaches_p with rfl | ⟨w,hstep,_⟩
    . rfl
    . exact absurd hstep (hno_step w)
  . exact Or.inr hvG
 have hnonTop_no_v' : ∀ j' < D.gates.length,j' ∉ topGates d' D->v' ∉ (gateAt D j').inputs:=by
  intro j' hj' hnotT hvmem
  have hNRT : (d'.role j').1≠Kind.top:=fun h => hnotT (mem_filter.mpr ⟨mem_range.mpr hj',h⟩)
  rcases hvD.2.2.2.2.1 j' hj' with htop | ⟨t,ht,hrt,hrb⟩
  . exact hNRT htop
  . cases hk : (d'.role j').1 with
    | top => exact hNRT hk
    | z =>
     have hjG : j' ∈ gatesOf d' D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
     rcases ((hvD.2.2.2.2.2.1 t ht).2.1.1 j' hjG).2.2 v' hvmem with hvL | ⟨hvn,hvG⟩
     . rcases hvPT with rfl | ⟨_,hvT⟩
       . unfold zLeaves at hvL;rcases mem_insert.mp hvL with htp | himg
         . exact hpNC (Fin.ext htp ▸ ht)
         . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
           obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hs).1
           have:=p.isLt;omega
       . unfold zLeaves at hvL;rcases mem_insert.mp hvL with htp | himg
         . have:=t.isLt;omega
         . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
           obtain ⟨js,_,hbw',hrs⟩:=bwS hvD s (mem_filter.mp hs).1
           have hrole_t : (d'.role (v' - n)).1=Kind.top:=(mem_filter.mp hvT).2
           have : v' - n=js:=by omega
           rw [this,hrs] at hrole_t;cases hrole_t
     . rcases hvPT with rfl | ⟨_,hvT⟩
       . have:=p.isLt;omega
       . have h1:=(mem_filter.mp hvG).2
         have h2:=(mem_filter.mp hvT).2
         rw [h1] at h2;cases h2
    | o =>
     have hjG : j' ∈ gatesOf d' D Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
     rcases ((hvD.2.2.2.2.2.1 t ht).2.2.1.1 j' hjG).2.2 v' hvmem with hvL | ⟨hvn,hvG⟩
     . obtain ⟨r,hr,hLE⟩:=mem_image.mp hvL
       have hown : d'.owns t r=true:=(mem_filter.mp hr).2
       have hrp : r≠p:=((hK2 t r).mp (hvD.2.2.1.1 t r hown).1).2.2.2.2
       have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
       unfold LamOK at hlam
       rcases hvPT with rfl | ⟨_,hvT⟩
       . by_cases hrc : r ∈ d'.cover
         . rw [if_pos hrc] at hlam
           rcases hlam.2.1 with h1 | ⟨k,_,h1,_⟩
           . exact hrp (Fin.ext (by omega))
           . have:=p.isLt;omega
         . rw [if_neg hrc] at hlam;exact hrp (Fin.ext (by omega))
       . by_cases hrc : r ∈ d'.cover
         . rw [if_pos hrc] at hlam
           rcases hlam.2.1 with h1 | ⟨k,_,h1,h2⟩
           . have:=r.isLt;omega
           . have hrole_t:=(mem_filter.mp hvT).2
             have : v' - n=k:=by omega
             rw [this,h2] at hrole_t;cases hrole_t
         . rw [if_neg hrc] at hlam;have:=r.isLt;omega
     . rcases hvPT with rfl | ⟨_,hvT⟩
       . have:=p.isLt;omega
       . have h1:=(mem_filter.mp hvG).2
         have h2:=(mem_filter.mp hvT).2
         rw [h1] at h2;cases h2
    | b =>
     obtain ⟨j'2,hj'2,hbw2,_,_,hin2⟩:=(hvD.2.2.2.2.2.1 t ht).1
     have hbw:=hrb hk
     have hjj : j'=j'2:=by omega
     subst hjj
     have hv_root : v'=d'.zroot t\/v'=d'.oroot t:=by
      rcases hin2 with h | h <;> rw [h] at hvmem <;>
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hvmem
      . exact hvmem
      . exact hvmem.symm
     rcases hv_root with hvz | hvo
     . have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
       by_cases hGe : gatesOf d' D Kind.z t.val=∅
       . rw [if_pos hGe] at hz
         have htp : d'.zroot t=t.val:=by
          have : t.val ∈ zLeaves d' t:=mem_insert_self _ _
          rw [hz,mem_singleton] at this;exact this.symm
         rcases hvPT with rfl | ⟨_,hvT⟩
         . exact hpNC (Fin.ext (hvz.trans htp).symm ▸ ht)
         . have:=t.isLt;omega
       . rw [if_neg hGe] at hz
         obtain ⟨k,hkG,hkeq⟩:=hz
         rcases hvPT with rfl | ⟨_,hvT⟩
         . have:=p.isLt;omega
         . have h1:=(mem_filter.mp hkG).2
           have h2:=(mem_filter.mp hvT).2
           have : v' - n=k:=by omega
           rw [this,h1] at h2;cases h2
     . have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
       by_cases hGe : gatesOf d' D Kind.o t.val=∅
       . rw [if_pos hGe] at ho
         obtain ⟨r,hown⟩:=ownHOE hvD ht
         have hrp : r≠p:=((hK2 t r).mp (hvD.2.2.1.1 t r hown).1).2.2.2.2
         have hmem_o : d'.lam t r ∈ oLeaves d' t :=
          mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩
         rw [ho,mem_singleton] at hmem_o
         have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
         unfold LamOK at hlam
         rcases hvPT with rfl | ⟨_,hvT⟩
         . by_cases hrc : r ∈ d'.cover
           . rw [if_pos hrc] at hlam
             rcases hlam.2.1 with h1 | ⟨k,_,h1,_⟩
             . exact hrp (Fin.ext (by omega))
             . have:=p.isLt;omega
           . rw [if_neg hrc] at hlam;exact hrp (Fin.ext (by omega))
         . by_cases hrc : r ∈ d'.cover
           . rw [if_pos hrc] at hlam
             rcases hlam.2.1 with h1 | ⟨k,_,h1,h2⟩
             . have:=r.isLt;omega
             . have hrole_t:=(mem_filter.mp hvT).2
               have : v' - n=k:=by omega
               rw [this,h2] at hrole_t;cases hrole_t
           . rw [if_neg hrc] at hlam;have:=r.isLt;omega
       . rw [if_neg hGe] at ho
         obtain ⟨k,hkG,hkeq⟩:=ho
         rcases hvPT with rfl | ⟨_,hvT⟩
         . have:=p.isLt;omega
         . have h1:=(mem_filter.mp hkG).2
           have h2:=(mem_filter.mp hvT).2
           have : v' - n=k:=by omega
           rw [this,h1] at h2;cases h2
 have hNTI : ∀ j' < D.gates.length,j' ∉ topGates d' D →
  (gateAt C (iI j0 j1 j')).inputs=(gateAt D j').inputs.map (iW n j0 j1):=by
  intro j' hj' hnotT
  have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
  have hne:=invIdx_ne (j':=j') hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  have hno:=hnonTop_no_v' j' hj' hnotT
  rw [hinD,List.map_map]
  symm
  rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
  have hi0 : i≠n+j0:=(hsub i hi).2.2
  have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hno (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
  rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
  . exact absurd hveq hwm_ne
  . exact heq.symm
 have hval_nonTop : ∀ (x : Fin n->Bool) (w' : ℕ),w' < n+D.gates.length →
  (¬ (n<=w'/\w' - n ∈ topGates d' D))->w'≠l.val →
  wV n C x (iW n j0 j1 w')=wV n D x w':=by
  intro x w'
  induction w' using Nat.strong_induction_on with
  | ind w' ih =>
   intro hw'lt hnotT hw'l
   by_cases hwn : w' < n
   . let wf : Fin n:=⟨w',hwn⟩
     unfold iW;rw [if_pos hwn]
     change wV n C x wf.val=wV n D x wf.val
     rw [wvI,wvI]
   . have hj' : w' - n < D.gates.length:=by omega
     have hweq : n+(w' - n)=w':=by omega
     have hnotT' : w' - n ∉ topGates d' D:=fun h => hnotT ⟨by omega,h⟩
     have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
     have hne:=invIdx_ne (j':=w' - n) hj01
     unfold iW;rw [if_neg hwn]
     conv_rhs => rw [← hweq]
     rw [wvGR n C hrbC x (iI j0 j1 (w' - n)) hlt,
      wvGR n D hvD.1 x (w' - n) hj']
     rw [(hIF (w' - n) hj').1,hNTI (w' - n) hj' hnotT',List.map_map]
     congr 1
     refine List.map_congr_left fun i' hi' => ?_
     have hilt : i' < n+(w' - n):=hvD.1 (w' - n) hj' i' hi'
     have hi'l : i'≠l.val:=by
      have hin_C:=hNTI (w' - n) hj' hnotT'
      have hmem_C : iW n j0 j1 i' ∈ (gateAt C (iI j0 j1 (w' - n))).inputs:=by
       rw [hin_C];exact List.mem_map.mpr ⟨i',hi',rfl⟩
      have h1:=((hKF (iI j0 j1 (w' - n)) hlt hne.1 hne.2).2.2 _ hmem_C).2.1
      intro heq;subst heq;unfold iW at h1;rw [if_pos l.isLt] at h1;exact h1 rfl
     have hi'notT : ¬ (n<=i'/\i' - n ∈ topGates d' D):=by
      intro ⟨hin,hiT⟩
      have hNRT : (d'.role (w' - n)).1≠Kind.top :=
       fun h => hnotT' (mem_filter.mpr ⟨mem_range.mpr hj',h⟩)
      have htop_no_other : ∀ k' < D.gates.length,k' ∉ topGates d' D →
       ∀ m' ∈ topGates d' D,n+m' ∉ (gateAt D k').inputs:=by
       intro k' hk' hnk' m' hm' hmem
       have hMR : (d'.role m').1=Kind.top:=(mem_filter.mp hm').2
       rcases hvD.2.2.2.2.1 k' hk' with htop | ⟨t,ht,hrt,hrb⟩
       . exact hnk' (mem_filter.mpr ⟨mem_range.mpr hk',htop⟩)
       . cases hk : (d'.role k').1 with
         | top => exact hnk' (mem_filter.mpr ⟨mem_range.mpr hk',hk⟩)
         | z =>
          have hkG : k' ∈ gatesOf d' D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hk',Prod.ext hk hrt⟩
          rcases ((hvD.2.2.2.2.2.1 t ht).2.1.1 k' hkG).2.2 (n+m') hmem with hL | ⟨_,hG⟩
          . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
            . have:=t.isLt;omega
            . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
              obtain ⟨js,_,hbw',hrs⟩:=bwS hvD s (mem_filter.mp hs).1
              have : m'=js:=by omega
              rw [this,hrs] at hMR;cases hMR
          . have h1:=(mem_filter.mp hG).2;simp at h1;rw [h1] at hMR;cases hMR
         | o =>
          have hkG : k' ∈ gatesOf d' D Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hk',Prod.ext hk hrt⟩
          rcases ((hvD.2.2.2.2.2.1 t ht).2.2.1.1 k' hkG).2.2 (n+m') hmem with hL | ⟨_,hG⟩
          . obtain ⟨r,hr,hLE⟩:=mem_image.mp hL
            have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r (mem_filter.mp hr).2
            unfold LamOK at hlam
            by_cases hrc : r ∈ d'.cover
            . rw [if_pos hrc] at hlam
              rcases hlam.2.1 with h1 | ⟨km,_,h1,h2⟩
              . have:=r.isLt;omega
              . have : m'=km:=by omega
                rw [this,h2] at hMR;cases hMR
            . rw [if_neg hrc] at hlam;have:=r.isLt;omega
          . have h1:=(mem_filter.mp hG).2;simp at h1;rw [h1] at hMR;cases hMR
         | b =>
          obtain ⟨k'2,_,hbw2,_,_,hin2⟩:=(hvD.2.2.2.2.2.1 t ht).1
          have hbw:=hrb hk
          have hkk : k'=k'2:=by omega
          subst k'
          have hm_root : n+m'=d'.zroot t\/n+m'=d'.oroot t:=by
           rcases hin2 with h | h <;> rw [h] at hmem <;>
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
           . exact hmem
           . exact hmem.symm
          rcases hm_root with hmz | hmo
          . have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
            by_cases hGe : gatesOf d' D Kind.z t.val=∅
            . rw [if_pos hGe] at hz
              have : t.val ∈ zLeaves d' t:=mem_insert_self _ _
              rw [hz,mem_singleton] at this;have:=t.isLt;omega
            . rw [if_neg hGe] at hz;obtain ⟨km,hkm,hkeq⟩:=hz
              have h1:=(mem_filter.mp hkm).2;have : m'=km:=by omega
              rw [this,h1] at hMR;cases hMR
          . have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
            by_cases hGe : gatesOf d' D Kind.o t.val=∅
            . rw [if_pos hGe] at ho
              obtain ⟨r,hown⟩:=ownHOE hvD ht
              have hmem_o : d'.lam t r ∈ oLeaves d' t :=
               mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩
              rw [ho,mem_singleton] at hmem_o
              have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
              unfold LamOK at hlam
              by_cases hrc : r ∈ d'.cover
              . rw [if_pos hrc] at hlam
                rcases hlam.2.1 with h1 | ⟨km,_,h1,h2⟩
                . have:=r.isLt;omega
                . have : m'=km:=by omega
                  rw [this,h2] at hMR;cases hMR
              . rw [if_neg hrc] at hlam;have:=r.isLt;omega
            . rw [if_neg hGe] at ho;obtain ⟨km,hkm,hkeq⟩:=ho
              have h1:=(mem_filter.mp hkm).2;have : m'=km:=by omega
              rw [this,h1] at hMR;cases hMR
      have hi'eq : n+(i' - n)=i':=by omega
      exact htop_no_other (w' - n) hj' hnotT' (i' - n) hiT (hi'eq.symm ▸ hi')
     exact ih i' (by omega) (by omega) hi'notT hi'l
 have hTSC :
  (v'=D.output->C.output=n+j1) ∧
  (∀ j' ∈ topGates d' D,(gateAt C (iI j0 j1 j')).inputs =
   (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w')):=by
  have hslot_out : v'=D.output->C.output=n+j1:=by
   intro hvout
   have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
   have hOL:=outLst hmin hncC hne_g
   by_contra hne_out
   have hj1_lt' : j1+1 < C.gates.length:=by omega
   obtain ⟨j2,hj2,hj12,hmem2⟩:=evGtR hmin hncC j1 hj1_lt'
   have hj2_ne0 : j2≠j0:=by omega
   have hj2_ne1 : j2≠j1:=by omega
   have hIL : iM j0 j1 j2 < D.gates.length:=by have:=iMLt hj01 hj1 hj2 hj2_ne0 hj2_ne1;omega
   obtain ⟨hop2,hin2,_⟩:=hKF j2 hj2 hj2_ne0 hj2_ne1
   have hmem_in : n+j1 ∈ (gateAt C j2).inputs:=by
    rcases valNN hvD (gateAt D (iM j0 j1 j2)) (by rw [gateAt_eq_getElem D _ hIL];exact List.getElem_mem hIL) with h | h <;>
     rw [← hop2] at h <;> simp [eIn,h] at hmem2 <;> exact hmem2
   have hv'_in : v' ∈ (gateAt D (iM j0 j1 j2)).inputs:=by
    rw [hin2];exact List.mem_map.mpr ⟨n+j1,hmem_in,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
   by_cases hT : iM j0 j1 j2 ∈ topGates d' D
   . have hr0 : readsIn D (topGates d' D) D.output=0:=by
      rw [← hvout]
      rcases hvTp with hL | ⟨hvn,hG⟩
      . rw [(hvD.2.2.2.2.2.2.2.1 v' hL).2,if_pos hvout]
      . have h:=hvD.2.2.2.2.2.2.2.2.1 (v' - n) hG
        have hveq : n+(v' - n)=v':=by omega
        rw [hveq,if_pos hvout] at h;exact h
     have hpos:=(rInP D (topGates d' D) D.output).mpr ⟨iM j0 j1 j2,hT,hvout ▸ hv'_in⟩
     omega
   . exact hnonTop_no_v' (iM j0 j1 j2) hIL hT hv'_in
  have hslot_gates : ∀ j' ∈ topGates d' D,(gateAt C (iI j0 j1 j')).inputs =
   (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w'):=by
   intro j' hj'
   have hj'lt : j' < D.gates.length:=topGates_lt j' hj'
   have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
   have hne:=invIdx_ne (j':=j') hj01
   obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
   rw [idxMap_invIdx hj01] at hinD
   by_cases hvm : v' ∈ (gateAt D j').inputs
   ·
    have hRJ1 : n+j1 ∈ (gateAt C (iI j0 j1 j')).inputs:=by
     by_contra hno_j1
     have hv'_ne_out : v'≠D.output:=by
      intro heq;rw [heq] at hvm
      have hr0 : readsIn D (topGates d' D) D.output=0:=by
       rcases hvTp with hL | ⟨_,hG⟩
       . rw [heq] at hL;rw [(hvD.2.2.2.2.2.2.2.1 D.output hL).2,if_pos rfl]
       . have h:=hvD.2.2.2.2.2.2.2.2.1 (v' - n) hG
         have hveq : n+(v' - n)=D.output:=by omega
         rw [hveq,if_pos rfl] at h;exact h
      have hpos:=(rInP D (topGates d' D) D.output).mpr ⟨j',hj',hvm⟩
      omega
     have hno_top_j1 : ∀ k' ∈ topGates d' D,
      (gateAt C (iI j0 j1 k')).inputs=(gateAt D k').inputs.map (iW n j0 j1):=by
      intro k' hk'
      have hk'lt : k' < D.gates.length:=topGates_lt k' hk'
      have hklt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
      have hkne:=invIdx_ne (j':=k') hj01
      obtain ⟨_,hinDk,hsubk⟩:=hKF (iI j0 j1 k') hklt hkne.1 hkne.2
      rw [idxMap_invIdx hj01] at hinDk
      have hk_no_j1 : n+j1 ∉ (gateAt C (iI j0 j1 k')).inputs:=by
       intro hmem
       have hv_in_k : v' ∈ (gateAt D k').inputs:=by
        rw [hinDk];exact List.mem_map.mpr ⟨n+j1,hmem,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
       have hkj : k'=j':=by
        have h:=osUP hvD.2.2.2.2.2.2
         ⟨k',hk',rfl,hv_in_k⟩ ⟨j',hj',rfl,hvm⟩
        omega
       subst hkj;exact hno_j1 hmem
      rw [hinDk,List.map_map];symm
      rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
      have hi0:=(hsubk i hi).2.2
      have hi1 : i≠n+j1:=fun h => hk_no_j1 (h ▸ hi)
      rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨habs,_⟩ | ⟨_,heq⟩
      . exact absurd habs hi1
      . exact heq.symm
     have htop_xp : ∀ w' < n+D.gates.length,w'≠l.val →
      wV n C xp (iW n j0 j1 w')=wV n D xp w':=by
      intro w'
      induction w' using Nat.strong_induction_on with
      | ind w' ih =>
       intro hw'lt hw'l
       by_cases hT : n<=w'/\w' - n ∈ topGates d' D
       . have hk' : w' - n < D.gates.length:=topGates_lt _ hT.2
         have hweq : n+(w' - n)=w':=by omega
         have hklt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
         have hkne:=invIdx_ne (j':=w' - n) hj01
         unfold iW;rw [if_neg (by omega)]
         conv_rhs => rw [← hweq]
         rw [wvGR n C hrbC xp (iI j0 j1 (w' - n)) hklt,
          wvGR n D hvD.1 xp (w' - n) hk',
          (hIF (w' - n) hk').1,hno_top_j1 (w' - n) hT.2,List.map_map]
         congr 1;refine List.map_congr_left fun i' hi' => ?_
         have hilt:=hvD.1 (w' - n) hk' i' hi'
         have hi'l : i'≠l.val:=by
          have hmem_C : iW n j0 j1 i' ∈ (gateAt C (iI j0 j1 (w' - n))).inputs:=by
           rw [hno_top_j1 (w' - n) hT.2];exact List.mem_map.mpr ⟨i',hi',rfl⟩
          have h1:=((hKF (iI j0 j1 (w' - n)) hklt hkne.1 hkne.2).2.2 _ hmem_C).2.1
          intro heq;subst heq;unfold iW at h1;rw [if_pos l.isLt] at h1;exact h1 rfl
         exact ih i' (by omega) (by omega) hi'l
       . exact hval_nonTop xp w' hw'lt hT hw'l
     have hCE : C.output=iW n j0 j1 D.output:=by
      have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
      have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
      rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
      . exact absurd hveq.symm hv'_ne_out
      . exact heq
     have hDout_lt : D.output < n+D.gates.length:=by
      have hinv:=spInv n l true C hmin.1 C.gates.length le_rfl
      have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
      have hOL : C.output < n+C.gates.length:=by have:=outLst hmin hncC hne_g;omega
      have h:=hinv.2.2 xp C.output hOL;rw [hOEv] at h;rw [← hD_def];exact h.1
     have hDout_ne_l : D.output≠l.val:=by
      intro h;have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
      have hOL:=outLst hmin hncC hne_g
      have h1 : C.output=l.val:=by rw [hCE,h];unfold iW;rw [if_pos l.isLt]
      have:=l.isLt;omega
     have hCxp:=htop_xp D.output hDout_lt hDout_ne_l
     rw [← hCE,wvO,wvO,hfun,nccEv hvD,hxp_K,hxp_K2] at hCxp
     cases hCxp
    obtain ⟨a',b',hinD_pair,hab'⟩:=otGIP hvD.2.2.2.2.2.2 hj'
    have hlenC : (gateAt C (iI j0 j1 j')).inputs.length=2:=by
     have:=congrArg List.length hinD;simp [hinD_pair] at this;exact this.symm
    cases hinC : (gateAt C (iI j0 j1 j')).inputs with
    | nil => simp [hinC] at hlenC
    | cons x1 rest =>
     cases rest with
     | nil => simp [hinC] at hlenC
     | cons x2 rest2 =>
      cases rest2 with
      | nil =>
       rw [hinC,hinD_pair] at hinD
       simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at hinD
       obtain ⟨hx1,hx2⟩:=hinD
       rw [hinC] at hRJ1;simp only [List.mem_cons,List.not_mem_nil,or_false] at hRJ1
       have hx10:=(hsub x1 (by simp [hinC])).2.2
       have hx20:=(hsub x2 (by simp [hinC])).2.2
       rw [hinD_pair]
       rcases hRJ1 with rfl | rfl
       . have ha'_eq : a'=v':=by
          rw [hx1];unfold wM;rw [if_neg (by omega),if_pos rfl]
         have hb'_ne : b'≠v':=fun h => hab' (ha'_eq.trans h.symm)
         have hx2_eq : x2=iW n j0 j1 b':=by
          rcases (wMEq hj01 hx20).mp hx2.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
          . exact absurd hveq hb'_ne
          . exact heq
         simp [ha'_eq,hb'_ne,hx2_eq]
       . have hb'_eq : b'=v':=by
          rw [hx2];unfold wM;rw [if_neg (by omega),if_pos rfl]
         have ha'_ne : a'≠v':=fun h => hab' (h.trans hb'_eq.symm)
         have hx1_eq : x1=iW n j0 j1 a':=by
          rcases (wMEq hj01 hx10).mp hx1.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
          . exact absurd hveq ha'_ne
          . exact heq
         simp [ha'_ne,hb'_eq,hx1_eq]
      | cons _ _ => simp [hinC] at hlenC
   . rw [hinD,List.map_map];symm
     rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
     have hi0:=(hsub i hi).2.2
     have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hvm (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
     simp only [Function.comp_apply,id_eq]
     rw [if_neg hwm_ne]
     rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
     . exact absurd hveq hwm_ne
     . exact heq.symm
  exact ⟨hslot_out,hslot_gates⟩
 have heval_C_iff : ∀ x : Fin n->Bool,
  circuitFun n C x=true ↔
   (∃ w' ∈ topLeaves d' (insert p A),¬ OrReach n D (topGates d' D) v' w'/\wV n D x w'=true) ∨
   ((x l || wV n D x u') && wV n D x v')=true:=by
  intro x
  have htop_eval : ∀ w',(w' ∈ topLeaves d' (insert p A)\/(n<=w'/\w' - n ∈ topGates d' D)) →
   ¬ (OrReach n D (topGates d' D) v' w'/\w'≠v') →
   (wV n C x (if w'=v' then n+j1 else iW n j0 j1 w')=true ↔
    (∃ lw ∈ topLeaves d' (insert p A),OrReach n D (topGates d' D) w' lw ∧
     ¬ OrReach n D (topGates d' D) v' lw/\wV n D x lw=true) ∨
    (OrReach n D (topGates d' D) w' v'/\wV n C x (n+j1)=true)):=by
   intro w'
   induction w' using Nat.strong_induction_on with
   | ind w' ih =>
    intro hw' hnb
    by_cases hwv : w'=v'
    . subst hwv;rw [if_pos rfl]
      constructor
      . intro h;exact Or.inr ⟨ReflTransGen.refl,h⟩
      . rintro (⟨lw,_,hr1,hr2,_⟩ | ⟨_,h⟩)
        . exact absurd hr1 hr2
        . exact h
    . rw [if_neg hwv]
      have hnot_vw : ¬ OrReach n D (topGates d' D) v' w':=fun h => hnb ⟨h,hwv⟩
      rcases hw' with hwL | ⟨hwn,hwG⟩
      . have hnotT : ¬ (n<=w'/\w' - n ∈ topGates d' D):=(hvD.2.2.2.2.2.2.2.1 w' hwL).1
        have hw'lt : w' < n+D.gates.length:=by
         unfold topLeaves at hwL;rcases mem_union.mp hwL with ha | ht
         . obtain ⟨a,_,rfl⟩:=mem_image.mp ha;exact Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right _ _)
         . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
           obtain ⟨jt,hjt,hbw,_⟩:=bwS hvD t (mem_filter.mp htF).1;omega
        have hw'l : w'≠l.val:=by
         unfold topLeaves at hwL;rcases mem_union.mp hwL with ha | ht
         . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
           rcases mem_insert.mp haA with rfl | haA'
           . exact fun h => hlp (Fin.ext h.symm)
           . exact fun h => hlA (Fin.ext h ▸ haA')
         . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
           obtain ⟨jt,_,hbw,_⟩:=bwS hvD t (mem_filter.mp htF).1
           have:=l.isLt;omega
        rw [hval_nonTop x w' hw'lt hnotT hw'l]
        have hno_step : ∀ z,¬ OrStep n D (topGates d' D) w' z:=by
         rintro z ⟨k,hkG,rfl,_⟩;exact hnotT ⟨by omega,by simpa using hkG⟩
        have hnot_rv : ¬ OrReach n D (topGates d' D) w' v':=by
         intro h;rcases ReflTransGen.cases_head h with rfl | ⟨z,hs,_⟩
         . exact hwv rfl
         . exact hno_step z hs
        constructor
        . intro ht;exact Or.inl ⟨w',hwL,ReflTransGen.refl,hnot_vw,ht⟩
        . rintro (⟨lw,_,hr,_,ht⟩ | ⟨hr,_⟩)
          . rcases ReflTransGen.cases_head hr with rfl | ⟨z,hs,_⟩
            . exact ht
            . exact absurd hs (hno_step z)
          . exact absurd hr hnot_rv
      . have hj' : w' - n < D.gates.length:=topGates_lt _ hwG
        have hweq : n+(w' - n)=w':=by omega
        have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
        unfold iW;rw [if_neg (by omega : ¬ w' < n)]
        rw [wvGR n C hrbC x (iI j0 j1 (w' - n)) hlt,
         (hIF (w' - n) hj').1,(hvD.2.2.2.2.2.2.1 (w' - n) hwG).1,
         hTSC.2 (w' - n) hwG]
        simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq]
        have hchild_nb : ∀ i' ∈ (gateAt D (w' - n)).inputs,
         ¬ (OrReach n D (topGates d' D) v' i'/\i'≠v'):=by
         intro i' hi' ⟨hvi,hine⟩
         rcases ReflTransGen.cases_tail hvi with rfl | ⟨z,hvz,hzi⟩
         . exact hine rfl
         . have hstep_w : OrStep n D (topGates d' D) w' i':=⟨w' - n,hwG,hweq.symm,hi'⟩
           have hwz : w'=z:=osUP hvD.2.2.2.2.2.2 hstep_w hzi
           exact hnot_vw (hwz ▸ hvz)
        constructor
        . rintro ⟨_,⟨i',hi'mem,hi't⟩,rfl⟩
          have hi'lt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi'mem;omega
          have hi'node:=(hvD.2.2.2.2.2.2.1 (w' - n) hwG).2.2 i' hi'mem
          have hstep_w : OrStep n D (topGates d' D) w' i':=⟨w' - n,hwG,hweq.symm,hi'mem⟩
          rcases (ih i' hi'lt hi'node (hchild_nb i' hi'mem)).mp hi't with
           ⟨lw,hlwL,hri,hnv,hlwt⟩ | ⟨hriv,hj1t⟩
          . exact Or.inl ⟨lw,hlwL,ReflTransGen.head hstep_w hri,hnv,hlwt⟩
          . exact Or.inr ⟨ReflTransGen.head hstep_w hriv,hj1t⟩
        . rintro (⟨lw,hlwL,hrw,hnv,hlwt⟩ | ⟨hrwv,hj1t⟩)
          . rcases ReflTransGen.cases_head hrw with rfl | ⟨i',hstep,hri⟩
            . exact absurd hlwL (fun h => (hvD.2.2.2.2.2.2.2.1 _ h).1 ⟨hwn,hwG⟩)
            . obtain ⟨k,_,hkeq,hi'mem⟩:=hstep
              have hkw : k=w' - n:=by omega
              subst hkw
              have hi'lt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi'mem;omega
              have hi'node:=(hvD.2.2.2.2.2.2.1 (w' - n) hwG).2.2 i' hi'mem
              have hi't:=(ih i' hi'lt hi'node (hchild_nb i' hi'mem)).mpr (Or.inl ⟨lw,hlwL,hri,hnv,hlwt⟩)
              exact ⟨true,⟨i',hi'mem,hi't⟩,rfl⟩
          . rcases ReflTransGen.cases_head hrwv with rfl | ⟨i',hstep,hriv⟩
            . exact absurd rfl hwv
            . obtain ⟨k,_,hkeq,hi'mem⟩:=hstep
              have hkw : k=w' - n:=by omega
              subst hkw
              have hi'lt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi'mem;omega
              have hi'node:=(hvD.2.2.2.2.2.2.1 (w' - n) hwG).2.2 i' hi'mem
              have hi't:=(ih i' hi'lt hi'node (hchild_nb i' hi'mem)).mpr (Or.inr ⟨hriv,hj1t⟩)
              exact ⟨true,⟨i',hi'mem,hi't⟩,rfl⟩
  have hDout_node : D.output ∈ topLeaves d' (insert p A)\/(n<=D.output/\D.output - n ∈ topGates d' D):=by
   have hroot:=hvD.2.2.2.2.2.2.2.2.2
   by_cases hGe : topGates d' D=∅
   . rw [if_pos hGe] at hroot;left;rw [hroot];simp
   . rw [if_neg hGe] at hroot;obtain ⟨k,hk,heq⟩:=hroot;right;exact ⟨by omega,by simpa [heq] using hk⟩
  have hDout_nb : ¬ (OrReach n D (topGates d' D) v' D.output/\D.output≠v'):=by
   rintro ⟨hr1,hne⟩
   have hr2:=otRR hvD.1 topGates_lt hvD.2.2.2.2.2.2 hvTp
   have h1:=orLe hvD.1 topGates_lt hr1
   have h2:=orLe hvD.1 topGates_lt hr2
   omega
  have hCE : C.output=if D.output=v' then n+j1 else iW n j0 j1 D.output:=by
   by_cases h : D.output=v'
   . rw [if_pos h];exact hTSC.1 h.symm
   . rw [if_neg h]
     have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
     have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
     rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
     . exact absurd hveq h
     . exact heq
  rw [← wvO,hCE,htop_eval D.output hDout_node hDout_nb,hval_j1]
  have hreach_v : OrReach n D (topGates d' D) D.output v' :=
   otRR hvD.1 topGates_lt hvD.2.2.2.2.2.2 hvTp
  constructor
  . rintro (⟨lw,hlwL,_,hnv,hlwt⟩ | ⟨_,h⟩)
    . exact Or.inl ⟨lw,hlwL,hnv,hlwt⟩
    . exact Or.inr h
  . rintro (⟨lw,hlwL,hnv,hlwt⟩ | h)
    . exact Or.inl ⟨lw,hlwL,otRR hvD.1 topGates_lt hvD.2.2.2.2.2.2 (Or.inl hlwL),hnv,hlwt⟩
    . exact Or.inr ⟨hreach_v,h⟩
 have hu'_xp_false : wV n D xp u'=false:=by
  apply Bool.eq_false_iff.mpr;intro hu't
  have hCxp : circuitFun n C xp=true:=(heval_C_iff xp).mpr (Or.inr (by simp [hu't,hv'_xp_true]))
  rw [hfun,hxp_K] at hCxp;cases hCxp
 let xpq : Fin n->Bool:=fun i => decide (i=p\/i=q)
 have hxpq_K : graphFun K A xpq=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨p,q,hPQA,by simp [xpq],by simp [xpq]⟩
 have hxpq_no_K2 : ∀ a b : Fin n,K2.Adj a b->xpq a=true->xpq b=true->False:=by
  intro a b hab hxa hxb
  have h:=(hK2 a b).mp hab
  simp only [xpq,decide_eq_true_eq] at hxa hxb
  rcases hxa with rfl | rfl
  . exact h.2.2.1 rfl
  . rcases hxb with rfl | rfl
    . exact h.2.2.2.2 rfl
    . exact hab.ne rfl
 have hu'_xpq_true : wV n D xpq u'=true:=by
  have hCxpq : circuitFun n C xpq=true:=by rw [hfun];exact hxpq_K
  rcases (heval_C_iff xpq).mp hCxpq with ⟨w',hw'L,hnv,hw't⟩ | hand
  . exfalso
    unfold topLeaves at hw'L
    rcases mem_union.mp hw'L with ha | ht
    . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
      rw [wvI] at hw't
      simp only [xpq,decide_eq_true_eq] at hw't
      rcases hw't with rfl | rfl
      . exact hnv hv'_reaches_p
      . rcases mem_insert.mp haA with hqp | hqa
        . exact hpq hqp.symm
        . exact hqA hqa
    . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
      obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xpq (d'.bw t) t (mem_filter.mp htF).1 rfl hw't
      exact hxpq_no_K2 a b hab hxa hxb
  . have hxl : xpq l=false:=by simp [xpq,hlp,hql.symm]
    simp [hxl] at hand;exact hand.1
 have hu'_y_false : ∀ r : Fin n,r≠q->r≠l->r ∉ A →
  wV n D (fun i => decide (i=p\/i=r)) u'=false:=by
  intro r hrq hrl hrA
  let y : Fin n->Bool:=fun i => decide (i=p\/i=r)
  have hy_K : graphFun K A y=false:=by
   simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
   refine ⟨fun a ha hya => ?_,fun a b hab hya hyb => ?_⟩
   . simp only [y,decide_eq_true_eq] at hya
     rcases hya with rfl | rfl
     . exact hpA ha
     . exact hrA ha
   . simp only [y,decide_eq_true_eq] at hya hyb
     rcases hya with rfl | rfl <;> rcases hyb with rfl | rfl
     . exact hab.ne rfl
     . rcases (hp b).mp hab with rfl | rfl <;> contradiction
     . rcases (hp a).mp hab.symm with rfl | rfl <;> contradiction
     . exact hab.ne rfl
  have hyv' : wV n D y v'=true :=
   otER hvD.1 topGates_lt hvD.2.2.2.2.2.2 y hv'_reaches_p (by rw [wvI];simp [y])
  apply Bool.eq_false_iff.mpr;intro hu't
  have hCy : circuitFun n C y=true:=(heval_C_iff y).mpr (Or.inr (by rw [hu't,hyv'];simp))
  rw [hfun,hy_K] at hCy;cases hCy
 have huC : u'=q.val ∨
  (q ∈ d'.cover/\IsCentred n D d' u' ∧
   ∃ j < D.gates.length,u'=n+j/\d'.role j=(Kind.z,q.val)):=by
  by_cases hun : u' < n
  . left
    let uf : Fin n:=⟨u',hun⟩
    have h1 : wV n D xpq uf.val=true:=hu'_xpq_true
    rw [wvI] at h1
    simp only [xpq,decide_eq_true_eq] at h1
    rcases h1 with rfl | rfl
    . exfalso;have h2 : wV n D xp uf.val=false:=hu'_xp_false
      rw [wvI] at h2;simp [xp] at h2
    . rfl
  . have hj' : u' - n < D.gates.length:=by omega
    have hueq : n+(u' - n)=u':=by omega
    rcases hvD.2.2.2.2.1 (u' - n) hj' with htop | ⟨t,ht,hrt,hrb⟩
    ·
     exfalso
     have hjG : u' - n ∈ topGates d' D:=mem_filter.mpr ⟨mem_range.mpr hj',htop⟩
     obtain ⟨lw,hlwL,hreach,hlwt⟩ :=
      (otEI hvD.1 topGates_lt hvD.2.2.2.2.2.2 xpq (Or.inr ⟨by omega,hjG⟩)).mp hu'_xpq_true
     unfold topLeaves at hlwL
     rcases mem_union.mp hlwL with ha | ht'
     . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
       rw [wvI] at hlwt;simp only [xpq,decide_eq_true_eq] at hlwt
       rcases hlwt with rfl | rfl
       . have : wV n D xp u'=true:=(hxp_D_top_iff u' (Or.inr ⟨by omega,hjG⟩)).mpr hreach
         rw [hu'_xp_false] at this;cases this
       . rcases mem_insert.mp haA with hqp | hqa
         . exact hpq hqp.symm
         . exact hqA hqa
     . obtain ⟨t',ht'F,rfl⟩:=mem_image.mp ht'
       obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xpq (d'.bw t') t' (mem_filter.mp ht'F).1 rfl hlwt
       exact hxpq_no_K2 a b hab hxa hxb
    . cases hk : (d'.role (u' - n)).1 with
      | top =>
       exfalso
       have hjG : u' - n ∈ topGates d' D:=mem_filter.mpr ⟨mem_range.mpr hj',hk⟩
       obtain ⟨lw,hlwL,hreach,hlwt⟩ :=
        (otEI hvD.1 topGates_lt hvD.2.2.2.2.2.2 xpq (Or.inr ⟨by omega,hjG⟩)).mp hu'_xpq_true
       unfold topLeaves at hlwL
       rcases mem_union.mp hlwL with ha | ht'
       . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
         rw [wvI] at hlwt;simp only [xpq,decide_eq_true_eq] at hlwt
         rcases hlwt with rfl | rfl
         . have : wV n D xp u'=true:=(hxp_D_top_iff u' (Or.inr ⟨by omega,hjG⟩)).mpr hreach
           rw [hu'_xp_false] at this;cases this
         . rcases mem_insert.mp haA with hqp | hqa
           . exact hpq hqp.symm
           . exact hqA hqa
       . obtain ⟨t',ht'F,rfl⟩:=mem_image.mp ht'
         obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xpq (d'.bw t') t' (mem_filter.mp ht'F).1 rfl hlwt
         exact hxpq_no_K2 a b hab hxa hxb
      | b =>
       exfalso
       have hbw : d'.bw t=u':=by have:=hrb hk;omega
       obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xpq u' t ht hbw hu'_xpq_true
       exact hxpq_no_K2 a b hab hxa hxb
      | z =>
       right
       have hrole : d'.role (u' - n)=(Kind.z,t.val):=Prod.ext hk hrt
       have hjG : u' - n ∈ gatesOf d' D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',hrole⟩
       obtain ⟨lz,hlzL,hreach,hlzt⟩ :=
        (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.1 xpq (Or.inr ⟨by omega,hjG⟩)).mp hu'_xpq_true
       unfold zLeaves at hlzL
       rcases mem_insert.mp hlzL with rfl | himg
       . rw [wvI] at hlzt;simp only [xpq,decide_eq_true_eq] at hlzt
         rcases hlzt with rfl | rfl
         . exact absurd ht hpNC
         . refine ⟨ht,(icZIR hvD ht (Or.inr ⟨u' - n,hj',hueq.symm,hrole⟩)).mpr hreach,
            u' - n,hj',hueq.symm,hrole⟩
       . exfalso
         obtain ⟨s,hs,rfl⟩:=mem_image.mp himg
         obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xpq (d'.bw s) s (mem_filter.mp hs).1 rfl hlzt
         exact hxpq_no_K2 a b hab hxa hxb
      | o =>
       exfalso
       have hrole : d'.role (u' - n)=(Kind.o,t.val):=Prod.ext hk hrt
       have hjG : u' - n ∈ gatesOf d' D Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj',hrole⟩
       obtain ⟨l1,hl1,l2,hl2,hl12,hr1,hr2⟩ :=
        otGTL hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1 hjG
       obtain ⟨r1,hr1f,rfl⟩:=mem_image.mp hl1
       obtain ⟨r2,hr2f,rfl⟩:=mem_image.mp hl2
       have hr12 : r1≠r2:=fun h => hl12 (by rw [h])
       have hpick : ∃ r,d'.owns t r=true/\r≠q/\OrReach n D (gatesOf d' D Kind.o t.val) u' (d'.lam t r):=by
        by_cases h : r1=q
        . exact ⟨r2,(mem_filter.mp hr2f).2,fun h2 => hr12 (h.trans h2.symm),by rwa [hueq] at hr2⟩
        . exact ⟨r1,(mem_filter.mp hr1f).2,h,by rwa [hueq] at hr1⟩
       obtain ⟨r,hown,hrq,hru⟩:=hpick
       have hadj : K2.Adj t r:=(hvD.2.2.1.1 t r hown).1
       have hKadj : K.Adj t r:=((hK2 t r).mp hadj).1
       have hrl : r≠l:=((hK2 t r).mp hadj).2.2.2.1
       have hrA : r ∉ A:=fun h => hA r h t hKadj.symm
       let y : Fin n->Bool:=fun i => decide (i=p\/i=r)
       have hlam_t : wV n D y (d'.lam t r)=true :=
        lam_true_of_input hvD ht hown y (by simp [y])
       have hu't : wV n D y u'=true :=
        otER hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1 y hru hlam_t
       have hu'f:=hu'_y_false r hrq hrl hrA
       rw [hu't] at hu'f;cases hu'f
 have hno_A_under_v' : ∀ a ∈ A,¬ OrReach n D (topGates d' D) v' a.val:=by
  intro a ha hreach
  let xa : Fin n->Bool:=fun i => decide (i=a)
  have hxa_K : graphFun K A xa=true:=by
   simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
   exact Or.inl ⟨a,ha,by simp [xa]⟩
  have haq : a≠q:=fun h => hqA (h ▸ ha)
  have hal : a≠l:=fun h => hlA (h ▸ ha)
  have hap : a≠p:=fun h => hpA (h ▸ ha)
  have hno_K2_a : ∀ b c : Fin n,K2.Adj b c->xa b=true->xa c=true->False:=by
   intro b c hbc hxb hxc
   have hb : b=a:=by simpa [xa] using hxb
   have hc : c=a:=by simpa [xa] using hxc
   subst hb;subst hc;exact hbc.ne rfl
  have hu'_xa_f : wV n D xa u'=false:=by
   rcases huC with huq | ⟨hq,_,j,hj,huj,hrole⟩
   . rw [huq,wvI];simp [xa,haq.symm]
   . apply Bool.eq_false_iff.mpr;intro htrue
     have hjG : j ∈ gatesOf d' D Kind.z q.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩
     obtain ⟨lz,hlzL,_,hlzt⟩ :=
      (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq).2.1 xa (Or.inr ⟨by omega,by rw [huj];simpa using hjG⟩)).mp htrue
     unfold zLeaves at hlzL
     rcases mem_insert.mp hlzL with rfl | himg
     . rw [wvI] at hlzt;have hqa : q=a:=by simpa [xa] using hlzt
       exact haq hqa.symm
     . obtain ⟨s,hs,rfl⟩:=mem_image.mp himg
       obtain ⟨b,c,hbc,hxb,hxc⟩:=nccBS hvD xa (d'.bw s) s (mem_filter.mp hs).1 rfl hlzt
       exact hno_K2_a b c hbc hxb hxc
  have hCxa : circuitFun n C xa=true:=by rw [hfun];exact hxa_K
  rcases (heval_C_iff xa).mp hCxa with ⟨w',hw'L,hnv,hw't⟩ | hand
  . unfold topLeaves at hw'L
    rcases mem_union.mp hw'L with ha' | ht
    . obtain ⟨b,hbA,rfl⟩:=mem_image.mp ha'
      rw [wvI] at hw't
      have hba : b=a:=by simpa [xa] using hw't
      exact hnv (hba ▸ hreach)
    . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
      obtain ⟨b,c,hbc,hxb,hxc⟩:=nccBS hvD xa (d'.bw t) t (mem_filter.mp htF).1 rfl hw't
      exact hno_K2_a b c hbc hxb hxc
  . have hxl : xa l=false:=by simp [xa,hal.symm]
    rw [hxl,hu'_xa_f] at hand;simp at hand
 have hbw_untied_only : ∀ (s r : Fin n),s ∈ d'.cover->d'.tie s=none->d'.owns s r=true →
  let xsr : Fin n->Bool:=fun i => decide (i=s\/i=r)
  ∀ w : ℕ,∀ t ∈ d'.cover,d'.bw t=w->t≠s->wV n D xsr w=false:=by
  intro s r hs hties hown xsr w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro t ht hbw hts
   subst hbw
   apply Bool.eq_false_iff.mpr;intro htrue
   obtain ⟨hz,ho⟩:=(term_eval_iff hvD ht xsr).mp htrue
   obtain ⟨lz,hlzL,hlzt⟩:=(otRE hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.1 xsr).mp hz
   unfold zLeaves at hlzL
   rcases mem_insert.mp hlzL with rfl | himg
   . rw [wvI] at hlzt;simp only [xsr,decide_eq_true_eq] at hlzt
     rcases hlzt with rfl | rfl
     . exact hts rfl
     ·
      obtain ⟨lo,hloL,hlot⟩:=(otRE hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1 xsr).mp ho
      obtain ⟨r',hr'f,rfl⟩:=mem_image.mp hloL
      have hown_r : d'.owns t r'=true:=(mem_filter.mp hr'f).2
      have hadj_r : K2.Adj t r':=(hvD.2.2.1.1 t r' hown_r).1
      have hr'_ne_t : r'≠t:=hadj_r.ne.symm
      have hr'_ne_s : r'≠s:=by
       intro heq;rw [heq] at hown_r
       have hne:=hvD.2.2.1.2 s t (hvD.2.2.1.1 s t hown).1
       rw [hown,hown_r] at hne;exact hne rfl
      have hlam_lt : d'.lam t r' < d'.bw t:=by
       have hr:=otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1
        (Or.inl (mem_image.mpr ⟨r',hr'f,rfl⟩))
       have:=orLe hvD.1 gatesOf_lt hr
       have:=(term_roots_lt_bw hvD ht).2;omega
      have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r' hown_r
      unfold LamOK at hlam
      by_cases hrc : r' ∈ d'.cover
      . rw [if_pos hrc] at hlam
        have hnode : d'.lam t r' ∈ zLeaves d' r'\/(n<=d'.lam t r'/\d'.lam t r' - n ∈ gatesOf d' D Kind.z r'.val):=by
         rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
         . left;rw [h1];exact mem_insert_self _ _
         . right;refine ⟨by omega,?_⟩;have : d'.lam t r' - n=k:=by omega
           rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
        obtain ⟨lz',hlz'L,hr',hlz't⟩:=(otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 r' hrc).2.1 xsr hnode).mp hlot
        unfold zLeaves at hlz'L
        rcases mem_insert.mp hlz'L with rfl | himg'
        . rw [wvI] at hlz't;simp only [xsr,decide_eq_true_eq] at hlz't
          rcases hlz't with h1 | h2
          . exact hr'_ne_s h1
          . exact hr'_ne_t h2
        . obtain ⟨s',hs',rfl⟩:=mem_image.mp himg'
          have htie' : d'.tie s'=some r':=(mem_filter.mp hs').2
          have hs'_ne_s : s'≠s:=fun h => by rw [h,hties] at htie';cases htie'
          have hle:=orLe hvD.1 gatesOf_lt hr'
          have hf:=ih (d'.bw s') (by omega) s' (mem_filter.mp hs').1 rfl hs'_ne_s
          rw [hlz't] at hf;cases hf
      . rw [if_neg hrc] at hlam;rw [hlam,wvI] at hlot
        simp only [xsr,decide_eq_true_eq] at hlot
        rcases hlot with h1 | h2
        . exact hr'_ne_s h1
        . exact hr'_ne_t h2
   . obtain ⟨s',hs',rfl⟩:=mem_image.mp himg
     have htie' : d'.tie s'=some t:=(mem_filter.mp hs').2
     have hs'_ne_s : s'≠s:=fun h => by rw [h,hties] at htie';cases htie'
     have hf:=ih (d'.bw s') (bw_tie_lt hvD htie') s' (mem_filter.mp hs').1 rfl hs'_ne_s
     rw [hlzt] at hf;cases hf
 have hOSQ : ∀ s ∈ d'.cover,d'.tie s=none->s≠q →
  OrReach n D (topGates d' D) v' (d'.bw s) →
  (∀ r : Fin n,d'.owns s r=true->r=q)/\q ∉ d'.cover:=by
  intro s hs hties hsq hreach
  have howns_q : ∀ r : Fin n,d'.owns s r=true->r=q:=by
   intro r hown
   let xsr : Fin n->Bool:=fun i => decide (i=s\/i=r)
   have hadj : K2.Adj s r:=(hvD.2.2.1.1 s r hown).1
   have hKadj : K.Adj s r:=((hK2 s r).mp hadj).1
   have hsl : s≠l:=((hK2 s r).mp hadj).2.1
   have hsp : s≠p:=((hK2 s r).mp hadj).2.2.1
   have hrl : r≠l:=((hK2 s r).mp hadj).2.2.2.1
   have hrp : r≠p:=((hK2 s r).mp hadj).2.2.2.2
   have hsA : s ∉ A:=fun h => hA s h r hKadj
   have hrA : r ∉ A:=fun h => hA r h s hKadj.symm
   have hCxsr : circuitFun n C xsr=true:=by
    rw [hfun];simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr ⟨s,r,hKadj,by simp [xsr],by simp [xsr]⟩
   have hu'_xsr : wV n D xsr u'=true:=by
    rcases (heval_C_iff xsr).mp hCxsr with ⟨w',hw'L,hnv,hw't⟩ | hand
    . exfalso
      unfold topLeaves at hw'L
      rcases mem_union.mp hw'L with ha | ht
      . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
        rw [wvI] at hw't;simp only [xsr,decide_eq_true_eq] at hw't
        rcases hw't with rfl | rfl
        . rcases mem_insert.mp haA with h1 | h2;exact hsp h1;exact hsA h2
        . rcases mem_insert.mp haA with h1 | h2;exact hrp h1;exact hrA h2
      . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
        by_cases hts : t=s
        . subst hts;exact hnv hreach
        . have hf:=hbw_untied_only s r hs hties hown (d'.bw t) t (mem_filter.mp htF).1 rfl hts
          rw [hw't] at hf;cases hf
    . have hxl : xsr l=false:=by simp [xsr,hsl.symm,hrl.symm]
      rw [hxl] at hand;simp at hand;exact hand.1
   rcases huC with huq | ⟨hq,_,j,hj,huj,hrole⟩
   . rw [huq,wvI] at hu'_xsr;simp only [xsr,decide_eq_true_eq] at hu'_xsr
     rcases hu'_xsr with h1 | h2
     . exact absurd h1.symm hsq
     . exact h2.symm
   . have hjG : j ∈ gatesOf d' D Kind.z q.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩
     obtain ⟨lz,hlzL,_,hlzt⟩ :=
      (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq).2.1 xsr (Or.inr ⟨by omega,by rw [huj];simpa using hjG⟩)).mp hu'_xsr
     unfold zLeaves at hlzL
     rcases mem_insert.mp hlzL with rfl | himg
     . rw [wvI] at hlzt;simp only [xsr,decide_eq_true_eq] at hlzt
       rcases hlzt with h1 | h2
       . exact absurd h1.symm hsq
       . exact h2.symm
     . exfalso
       obtain ⟨t,htF,rfl⟩:=mem_image.mp himg
       have htie_t : d'.tie t=some q:=(mem_filter.mp htF).2
       have hts : t≠s:=fun h => by rw [h,hties] at htie_t;cases htie_t
       have hf:=hbw_untied_only s r hs hties hown (d'.bw t) t (mem_filter.mp htF).1 rfl hts
       rw [hlzt] at hf;cases hf
  refine ⟨howns_q,?_⟩
  intro hq_cov
  have hcov' : K2.IsVertexCover ((d'.cover.erase s : Finset (Fin n)) : Set (Fin n)):=by
   intro a b hab
   have hne:=hvD.2.2.1.2 a b hab
   have hcase : d'.owns a b=true\/d'.owns b a=true:=by
    cases h1 : d'.owns a b <;> cases h2 : d'.owns b a
    . exfalso;rw [h1,h2] at hne;exact hne rfl
    . exact Or.inr rfl
    . exact Or.inl rfl
    . exact Or.inl rfl
   rcases hcase with h1 | h2
   . by_cases has : a=s
     . subst has;right;have hb:=howns_q b h1;subst hb
       exact mem_erase.mpr ⟨hsq.symm,hq_cov⟩
     . left;exact mem_erase.mpr ⟨has,(hvD.2.2.1.1 a b h1).2⟩
   . by_cases hbs : b=s
     . subst hbs;left;have ha:=howns_q a h2;subst ha
       exact mem_erase.mpr ⟨hsq.symm,hq_cov⟩
     . right;exact mem_erase.mpr ⟨hbs,(hvD.2.2.1.1 b a h2).2⟩
  have hle:=hvD.2.1.2 (d'.cover.erase s) hcov'
  have hlt:=card_erase_lt_of_mem hs
  omega
 have hq_under_v'_imp_zroot : q ∈ d'.cover->d'.tie q=none →
  OrReach n D (topGates d' D) v' (d'.bw q)->u'=d'.zroot q:=by
  intro hq htieq hreach_q
  have hu'_znode : u' ∈ zLeaves d' q\/(n<=u'/\u' - n ∈ gatesOf d' D Kind.z q.val):=by
   rcases huC with huq | ⟨_,_,j,hj,huj,hrole⟩
   . left;rw [huq];exact mem_insert_self _ _
   . right;refine ⟨by omega,?_⟩
     have hjG : j ∈ gatesOf d' D Kind.z q.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩
     rw [huj];simpa using hjG
  by_contra hne_zr
  obtain ⟨lz,hlzL,hnot_rz⟩ :=
   orTree_proper_sub_missing_leaf hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq).2.1 hu'_znode hne_zr
  unfold zLeaves at hlzL
  rcases mem_insert.mp hlzL with rfl | himg
  ·
   rcases huC with huq | ⟨_,hc,j,hj,huj,hrole⟩
   . rw [huq] at hnot_rz;exact hnot_rz ReflTransGen.refl
   . exact hnot_rz ((icZIR hvD hq (Or.inr ⟨j,hj,huj,hrole⟩)).mp hc)
  . obtain ⟨s',hs'F,rfl⟩:=mem_image.mp himg
    have hs' : s' ∈ d'.cover:=(mem_filter.mp hs'F).1
    have htie_s' : d'.tie s'=some q:=(mem_filter.mp hs'F).2
    have hown_qs' : d'.owns q s'=true:=(hvD.2.2.2.1 s' q htie_s').2
    have hadj_qs' : K2.Adj q s':=(hvD.2.2.1.1 q s' hown_qs').1
    have hKadj_qs' : K.Adj q s':=((hK2 q s').mp hadj_qs').1
    obtain ⟨r',hown_s'r'⟩:=ownHOE hvD hs'
    have hadj_s'r' : K2.Adj s' r':=(hvD.2.2.1.1 s' r' hown_s'r').1
    have hKadj_s'r' : K.Adj s' r':=((hK2 s' r').mp hadj_s'r').1
    have hnot_qr' : ¬ K.Adj q r':=fun h => htf q s' r' hKadj_qs' hKadj_s'r' h
    have hs'q : s'≠q:=hadj_qs'.ne.symm
    have hr'q : r'≠q:=by
     intro heq;rw [heq] at hown_s'r'
     have hne:=hvD.2.2.1.2 q s' hadj_qs'
     rw [hown_qs',hown_s'r'] at hne;exact hne rfl
    have hs'r' : s'≠r':=hadj_s'r'.ne
    let y : Fin n->Bool:=fun i => decide (i=s'\/i=r')
    have hbw_y_false : ∀ w : ℕ,∀ t ∈ d'.cover,d'.bw t=w->t≠s'->t≠q->wV n D y w=false:=by
     intro w
     induction w using Nat.strong_induction_on with
     | ind w ih =>
      intro t ht hbw hts' htq
      subst hbw
      apply Bool.eq_false_iff.mpr;intro htrue
      obtain ⟨hz,ho⟩:=(term_eval_iff hvD ht y).mp htrue
      obtain ⟨lz0,hlz0L,hlz0t⟩:=(otRE hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.1 y).mp hz
      unfold zLeaves at hlz0L
      rcases mem_insert.mp hlz0L with rfl | himg0
      . rw [wvI] at hlz0t;simp only [y,decide_eq_true_eq] at hlz0t
        rcases hlz0t with rfl | rfl
        . exact hts' rfl
        ·
         obtain ⟨lo,hloL,hlot⟩:=(otRE hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1 y).mp ho
         obtain ⟨w',hw'f,rfl⟩:=mem_image.mp hloL
         have hown_tw : d'.owns t w'=true:=(mem_filter.mp hw'f).2
         have hadj_tw : K2.Adj t w':=(hvD.2.2.1.1 t w' hown_tw).1
         have hKadj_tw : K.Adj t w':=((hK2 t w').mp hadj_tw).1
         have hw't : w'≠t:=hadj_tw.ne.symm
         have hw's' : w'≠s':=by
          intro heq;rw [heq] at hown_tw
          have hne:=hvD.2.2.1.2 s' t hadj_s'r'
          rw [hown_s'r',hown_tw] at hne;exact hne rfl
         have hw'q : w'≠q:=fun heq => hnot_qr' (heq ▸ hKadj_tw.symm)
         have hlam_lt : d'.lam t w' < d'.bw t:=by
          have hr:=otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1
           (Or.inl (mem_image.mpr ⟨w',hw'f,rfl⟩))
          have:=orLe hvD.1 gatesOf_lt hr
          have:=(term_roots_lt_bw hvD ht).2;omega
         have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 w' hown_tw
         unfold LamOK at hlam
         by_cases hwc : w' ∈ d'.cover
         . rw [if_pos hwc] at hlam
           have hnode : d'.lam t w' ∈ zLeaves d' w'\/(n<=d'.lam t w'/\d'.lam t w' - n ∈ gatesOf d' D Kind.z w'.val):=by
            rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
            . left;rw [h1];exact mem_insert_self _ _
            . right;refine ⟨by omega,?_⟩;have : d'.lam t w' - n=k:=by omega
              rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
           obtain ⟨lz1,hlz1L,hr1,hlz1t⟩:=(otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 w' hwc).2.1 y hnode).mp hlot
           unfold zLeaves at hlz1L
           rcases mem_insert.mp hlz1L with rfl | himg1
           . rw [wvI] at hlz1t;simp only [y,decide_eq_true_eq] at hlz1t
             rcases hlz1t with h1 | h2;exact hw's' h1;exact hw't h2
           . obtain ⟨u0,hu0F,rfl⟩:=mem_image.mp himg1
             have htie_u0 : d'.tie u0=some w':=(mem_filter.mp hu0F).2
             have hu0s' : u0≠s':=fun h => by rw [h,htie_s'] at htie_u0;exact hw'q (Option.some.inj htie_u0).symm
             have hu0q : u0≠q:=fun h => by rw [h,htieq] at htie_u0;cases htie_u0
             have hle:=orLe hvD.1 gatesOf_lt hr1
             have hf:=ih (d'.bw u0) (by omega) u0 (mem_filter.mp hu0F).1 rfl hu0s' hu0q
             rw [hlz1t] at hf;cases hf
         . rw [if_neg hwc] at hlam;rw [hlam,wvI] at hlot
           simp only [y,decide_eq_true_eq] at hlot
           rcases hlot with h1 | h2;exact hw's' h1;exact hw't h2
      . obtain ⟨u0,hu0F,rfl⟩:=mem_image.mp himg0
        have htie_u0 : d'.tie u0=some t:=(mem_filter.mp hu0F).2
        have hu0s' : u0≠s':=fun h => by rw [h,htie_s'] at htie_u0;exact htq (Option.some.inj htie_u0).symm
        have hu0q : u0≠q:=fun h => by rw [h,htieq] at htie_u0;cases htie_u0
        have hf:=ih (d'.bw u0) (bw_tie_lt hvD htie_u0) u0 (mem_filter.mp hu0F).1 rfl hu0s' hu0q
        rw [hlz0t] at hf;cases hf
    have hu'_y_f : wV n D y u'=false:=by
     apply Bool.eq_false_iff.mpr;intro htrue
     obtain ⟨lz0,hlz0L,hr0,hlz0t⟩ :=
      (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq).2.1 y hu'_znode).mp htrue
     unfold zLeaves at hlz0L
     rcases mem_insert.mp hlz0L with rfl | himg0
     . rw [wvI] at hlz0t;simp only [y,decide_eq_true_eq] at hlz0t
       rcases hlz0t with h1 | h2;exact hs'q h1.symm;exact hr'q h2.symm
     . obtain ⟨u0,hu0F,rfl⟩:=mem_image.mp himg0
       by_cases hu0s' : u0=s'
       . subst hu0s';exact hnot_rz hr0
       . have htie_u0 : d'.tie u0=some q:=(mem_filter.mp hu0F).2
         have hu0q : u0≠q:=fun h => by rw [h,htieq] at htie_u0;cases htie_u0
         have hf:=hbw_y_false (d'.bw u0) u0 (mem_filter.mp hu0F).1 rfl hu0s' hu0q
         rw [hlz0t] at hf;cases hf
    have hCy : circuitFun n C y=true:=by
     rw [hfun];simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
     exact Or.inr ⟨s',r',hKadj_s'r',by simp [y],by simp [y]⟩
    rcases (heval_C_iff y).mp hCy with ⟨w',hw'L,hnv,hw't⟩ | hand
    . unfold topLeaves at hw'L
      rcases mem_union.mp hw'L with ha | ht
      . obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
        rw [wvI] at hw't;simp only [y,decide_eq_true_eq] at hw't
        rcases hw't with ha_eq | ha_eq
        . rw [ha_eq] at haA
          rcases mem_insert.mp haA with h1 | h2
          . exact ((hK2 s' r').mp hadj_s'r').2.2.1 h1
          . exact hA s' h2 r' hKadj_s'r'
        . rw [ha_eq] at haA
          rcases mem_insert.mp haA with h1 | h2
          . exact ((hK2 s' r').mp hadj_s'r').2.2.2.2 h1
          . exact hA r' h2 s' hKadj_s'r'.symm
      . obtain ⟨t,htF,rfl⟩:=mem_image.mp ht
        have ht_cov:=(mem_filter.mp htF).1
        have ht_tie:=(mem_filter.mp htF).2
        by_cases htq : t=q
        . subst htq;exact hnv hreach_q
        . have hts' : t≠s':=fun h => by rw [h,htie_s'] at ht_tie;cases ht_tie
          have hf:=hbw_y_false (d'.bw t) t ht_cov rfl hts' htq
          rw [hw't] at hf;cases hf
    . have hyl : y l=false:=by
       simp [y,((hK2 s' r').mp hadj_s'r').2.1.symm,((hK2 s' r').mp hadj_s'r').2.2.2.1.symm]
      rw [hyl,hu'_y_f] at hand;simp at hand
 have hMCP : IsMinCover K (insert p d'.cover):=by
  refine ⟨?_,?_⟩
  . intro a b hab
    by_cases hap : a=p
    . left;simp [hap]
    . by_cases hbp : b=p
      . right;simp [hbp]
      . have hal : a≠l:=fun h => hbp ((hl b).mp (h ▸ hab))
        have hbl : b≠l:=fun h => hap ((hl a).mp (h ▸ hab.symm))
        rcases hvD.2.1.1 ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩) with ha | hb
        . exact Or.inl (mem_insert_of_mem ha)
        . exact Or.inr (mem_insert_of_mem hb)
  . intro T' hT'
    rw [card_insert_of_notMem hpNC]
    have hcov2 : K2.IsVertexCover (((T'.erase l).erase p : Finset (Fin n)) : Set (Fin n)):=by
     intro a b hab
     have h:=(hK2 a b).mp hab
     rcases hT' h.1 with ha | hb
     . left;exact mem_erase.mpr ⟨h.2.2.1,mem_erase.mpr ⟨h.2.1,ha⟩⟩
     . right;exact mem_erase.mpr ⟨h.2.2.2.2,mem_erase.mpr ⟨h.2.2.2.1,hb⟩⟩
    have hle:=hvD.2.1.2 _ hcov2
    rcases hT' hLPA with hlT | hpT
    . have h1:=card_erase_lt_of_mem hlT
      have h2:=Finset.card_erase_le (s:=T'.erase l) (a:=p);omega
    . have h1:=card_erase_lt_of_mem hpT
      have h2 : ((T'.erase l).erase p).card<=(T'.erase p).card :=
       card_le_card (fun x hx => by simp at hx ⊢;exact ⟨hx.1,hx.2.2⟩);omega
 have hv'_leaf_other : ∀ w' ∈ topLeaves d' (insert p A),OrReach n D (topGates d' D) v' w' →
  w'≠p.val->∃ s ∈ d'.cover,d'.tie s=none/\w'=d'.bw s:=by
  intro w' hw'L hreach hnep
  unfold topLeaves at hw'L
  rcases mem_union.mp hw'L with ha | ht
  . exfalso
    obtain ⟨a,haA,rfl⟩:=mem_image.mp ha
    rcases mem_insert.mp haA with rfl | haA'
    . exact hnep rfl
    . exact hno_A_under_v' a haA' hreach
  . obtain ⟨s,hsF,rfl⟩:=mem_image.mp ht
    exact ⟨s,(mem_filter.mp hsF).1,(mem_filter.mp hsF).2,rfl⟩
 by_cases hother : ∃ w' ∈ topLeaves d' (insert p A),OrReach n D (topGates d' D) v' w'/\w'≠p.val
 . obtain ⟨w0',hw0'L,hreach0,hne0⟩:=hother
   obtain ⟨s0,hs0,hties0,rfl⟩:=hv'_leaf_other w0' hw0'L hreach0 hne0
   have hsub_pair : ∀ w' ∈ topLeaves d' (insert p A),OrReach n D (topGates d' D) v' w' →
    w'=p.val\/w'=d'.bw s0:=by
    intro w' hw'L hreach
    by_cases hwp : w'=p.val
    . exact Or.inl hwp
    . right
      obtain ⟨s1,hs1,hties1,rfl⟩:=hv'_leaf_other w' hw'L hreach hwp
      by_contra hne_bw
      have hs10 : s1≠s0:=fun h => hne_bw (by rw [h])
      by_cases h0q : s0=q
      . subst h0q
        have h1q : s1≠s0:=hs10
        exact (hOSQ s1 hs1 hties1 h1q hreach).2 hs0
      . by_cases h1q : s1=q
        . subst h1q
          exact (hOSQ s0 hs0 hties0 h0q hreach0).2 hs1
        ·
         obtain ⟨h0only,hqnc⟩:=hOSQ s0 hs0 hties0 h0q hreach0
         obtain ⟨h1only,_⟩:=hOSQ s1 hs1 hties1 h1q hreach
         let T_small:=insert q ((d'.cover.erase s0).erase s1)
         have hcov_small : K2.IsVertexCover (T_small : Set (Fin n)):=by
          intro a b hab
          have hne:=hvD.2.2.1.2 a b hab
          have hcase : d'.owns a b=true\/d'.owns b a=true:=by
           cases h1 : d'.owns a b <;> cases h2 : d'.owns b a
           . exfalso;rw [h1,h2] at hne;exact hne rfl
           . exact Or.inr rfl
           . exact Or.inl rfl
           . exact Or.inl rfl
          rcases hcase with h1 | h2
          . by_cases ha0 : a=s0
            . subst ha0;right;rw [h0only b h1];simp [T_small]
            . by_cases ha1 : a=s1
              . subst ha1;right;rw [h1only b h1];simp [T_small]
              . left;exact mem_insert_of_mem (mem_erase.mpr ⟨ha1,mem_erase.mpr ⟨ha0,(hvD.2.2.1.1 a b h1).2⟩⟩)
          . by_cases hb0 : b=s0
            . subst hb0;left;rw [h0only a h2];simp [T_small]
            . by_cases hb1 : b=s1
              . subst hb1;left;rw [h1only a h2];simp [T_small]
              . right;exact mem_insert_of_mem (mem_erase.mpr ⟨hb1,mem_erase.mpr ⟨hb0,(hvD.2.2.1.1 b a h2).2⟩⟩)
         have hle:=hvD.2.1.2 T_small hcov_small
         have hcard1 : ((d'.cover.erase s0).erase s1).card+2=d'.cover.card:=by
          have hs1_in : s1 ∈ d'.cover.erase s0:=mem_erase.mpr ⟨hs10,hs1⟩
          have hc1:=card_erase_add_one hs1_in
          have hc0:=card_erase_add_one hs0
          omega
         have hq_not_in : q ∉ (d'.cover.erase s0).erase s1:=fun h => hqnc (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
         have hcard2 : T_small.card=((d'.cover.erase s0).erase s1).card+1:=card_insert_of_notMem hq_not_in
         omega
   have hp_mem_top : p.val ∈ topLeaves d' (insert p A) :=
    mem_union_left _ (mem_image.mpr ⟨p,mem_insert_self _ _,rfl⟩)
   obtain ⟨jv',hjv'T,hv'_eq_jv,hjv'_in⟩:=otGSP hvD.1 topGates_lt hvD.2.2.2.2.2.2
    hvTp hp_mem_top hw0'L (Ne.symm hne0) hv'_reaches_p hreach0 hsub_pair
   have hjv'lt : jv' < D.gates.length:=topGates_lt jv' hjv'T
   have hjv_C_lt : iI j0 j1 jv' < C.gates.length:=invIdx_lt hj01 hj1 (by omega : jv'+2 < C.gates.length)
   have hjv_C_ne:=invIdx_ne (j':=jv') hj01
   have hjv_C_in : (gateAt C (iI j0 j1 jv')).inputs=[p.val,iW n j0 j1 (d'.bw s0)] ∨
    (gateAt C (iI j0 j1 jv')).inputs=[iW n j0 j1 (d'.bw s0),p.val]:=by
    have h:=hTSC.2 jv' hjv'T
    have hne_pv : p.val≠v':=by have:=p.isLt;omega
    have hne_sv : d'.bw s0≠v':=by
     intro heq;exact (hvD.2.2.2.2.2.2.2.1 (d'.bw s0) hw0'L).1 ⟨by omega,by rw [heq,hv'_eq_jv];simpa using hjv'T⟩
    have hinv_p : iW n j0 j1 p.val=p.val:=by unfold iW;rw [if_pos p.isLt]
    rcases hjv'_in with h1 | h1
    . left;rw [h,h1];simp [hne_pv,hne_sv,hinv_p]
    . right;rw [h,h1];simp [hne_pv,hne_sv,hinv_p]
   have hv_eq_jvC : v=n+iI j0 j1 jv':=by
    rw [hv_eq,hv'_eq_jv];unfold iW;rw [if_neg (by omega)];simp
   have hjv_C_op : (gateAt C (iI j0 j1 jv')).op=.or:=by
    rw [(hIF jv' hjv'lt).1,(hvD.2.2.2.2.2.2.1 jv' hjv'T).1]
   by_cases hs0q : s0=q
   ·
    subst hs0q
    have hu'_zroot : u'=d'.zroot s0:=hq_under_v'_imp_zroot hs0 hties0 hreach0
    let d : NCCData n:={
     cover:=insert p d'.cover
     owns:=fun a b => if a=p/\(b=l\/b=s0) then true else d'.owns a b
     tie:=fun a => if a=s0 then some p else if a=p then none else d'.tie a
     role:=fun j =>
      if j=j0 then (Kind.o,p.val)
      else if j=j1 then (Kind.b,p.val)
      else if j=iI j0 j1 jv' then (Kind.z,p.val)
      else d'.role (iM j0 j1 j)
     bw:=fun a => if a=p then n+j1 else iW n j0 j1 (d'.bw a)
     zroot:=fun a => if a=p then v else iW n j0 j1 (d'.zroot a)
     oroot:=fun a => if a=p then n+j0 else iW n j0 j1 (d'.oroot a)
     lam:=fun a b => if a=p then (if b=l then l.val else u) else iW n j0 j1 (d'.lam a b)
    }
    have hRS : ∀ j' < D.gates.length,j'≠jv'->d.role (iI j0 j1 j')=d'.role j':=by
     intro j' hj' hne_jv
     have hne:=invIdx_ne (j':=j') hj01
     have hne_i : iI j0 j1 j'≠iI j0 j1 jv':=fun h => hne_jv (invIdx_inj hj01 h)
     simp only [d,if_neg hne.1,if_neg hne.2,if_neg hne_i,idxMap_invIdx hj01]
    have hGOO : ∀ t ∈ d'.cover,∀ k : Kind,k≠Kind.top →
     gatesOf d C k t.val=(gatesOf d' D k t.val).image (iI j0 j1):=by
     intro t ht k hk_ne
     have htp : t≠p:=fun h => hpNC (h ▸ ht)
     ext j;simp only [gatesOf,mem_filter,mem_range,mem_image]
     constructor
     . rintro ⟨hj,hr⟩
       have hjne0 : j≠j0:=by intro h;rw [h] at hr;simp only [d,if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hjne1 : j≠j1:=by intro h;rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hjnev : j≠iI j0 j1 jv':=by
        intro h;rw [h] at hr;simp only [d,if_neg hjv_C_ne.1,if_neg hjv_C_ne.2,if_pos rfl] at hr
        exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj hjne0 hjne1;omega
       simp only [d,if_neg hjne0,if_neg hjne1,if_neg hjnev] at hr
       exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 hjne0 hjne1⟩
     . rintro ⟨j',⟨hj',hr'⟩,rfl⟩
       have hj'ne : j'≠jv':=by
        intro h;rw [h] at hr'
        have ht1 : (d'.role jv').1=Kind.top:=(mem_filter.mp hjv'T).2
        rw [hr'] at ht1;exact hk_ne (by simpa using ht1)
       exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj' hj'ne,hr']⟩
    refine ⟨d,hrbC,hMCP,?_,?_,?_,?_,?_⟩
    ·
     refine ⟨?_,?_⟩
     . intro a b hown;simp only [d] at hown
       split_ifs at hown with h
       . rcases h with ⟨rfl,rfl | rfl⟩
         . exact ⟨hLPA.symm,mem_insert_self _ _⟩
         . exact ⟨hPQA,mem_insert_self _ _⟩
       . have h2:=hvD.2.2.1.1 a b hown
         exact ⟨((hK2 a b).mp h2.1).1,mem_insert_of_mem h2.2⟩
     . intro a b hab;simp only [d]
       by_cases hap : a=p
       . subst a
         rcases (hp b).mp hab with hbl | hbs
         . subst b
           have hnot : d'.owns l p=false:=by
            cases h : d'.owns l p;rfl;exfalso;exact ((hK2 l p).mp (hvD.2.2.1.1 l p h).1).2.1 rfl
           simp [hlp,hnot]
         . subst b
           have hnot : d'.owns s0 p=false:=by
            cases h : d'.owns s0 p;rfl;exfalso;exact ((hK2 s0 p).mp (hvD.2.2.1.1 s0 p h).1).2.2.2.2 rfl
           simp [hpq.symm,hnot]
       . by_cases hbp : b=p
         . subst b
           rcases (hp a).mp hab.symm with hal | has
           . subst a
             have hnot : d'.owns l p=false:=by
              cases h : d'.owns l p;rfl;exfalso;exact ((hK2 l p).mp (hvD.2.2.1.1 l p h).1).2.1 rfl
             simp [hap,hnot]
           . subst a
             have hnot : d'.owns s0 p=false:=by
              cases h : d'.owns s0 p;rfl;exfalso;exact ((hK2 s0 p).mp (hvD.2.2.1.1 s0 p h).1).2.2.2.2 rfl
             simp [hap,hnot]
         . have hal : a≠l:=fun h => hbp ((hl b).mp (h ▸ hab))
           have hbl : b≠l:=fun h => hap ((hl a).mp (h ▸ hab.symm))
           simp only [hap,hbp,false_and,↓reduceIte]
           exact hvD.2.2.1.2 a b ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩)
    ·
     intro a b htie;simp only [d] at htie
     by_cases has : a=s0
     . subst a;rw [if_pos rfl] at htie;cases htie
       exact ⟨mem_insert_of_mem hs0,by simp [d]⟩
     . rw [if_neg has] at htie
       by_cases hap : a=p
       . rw [if_pos hap] at htie;cases htie
       . rw [if_neg hap] at htie
         have h2:=hvD.2.2.2.1 a b htie
         refine ⟨mem_insert_of_mem h2.1,?_⟩
         simp only [d];split_ifs;rfl;exact h2.2
    ·
     intro j hj
     by_cases h0 : j=j0
     . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d],fun h => by simp [d] at h⟩
     . by_cases h1 : j=j1
       . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d,h0],fun _ => by simp [d]⟩
       . by_cases hv_j : j=iI j0 j1 jv'
         . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d,h0,h1],fun h => by simp [d,h0,h1] at h⟩
         . have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
           have hrole_eq : d.role j=d'.role (iM j0 j1 j):=by simp [d,h0,h1,hv_j]
           rw [hrole_eq]
           rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨t,ht,hrt,hrb⟩
           . exact Or.inl htop
           . right
             have htp : t≠p:=fun h => hpNC (h ▸ ht)
             refine ⟨t,mem_insert_of_mem ht,hrt,fun hb => ?_⟩
             simp only [d,if_neg htp];rw [hrb hb]
             unfold iW;rw [if_neg (by omega)]
             have : n+iM j0 j1 j - n=iM j0 j1 j:=by omega
             rw [this,invIdx_idxMap hj01 h0 h1]
    ·
     intro t ht
     rcases mem_insert.mp ht with htp | ht'
     . subst t
       have hz_gates_p : gatesOf d C Kind.z p.val={iI j0 j1 jv'}:=by
        ext j;simp only [gatesOf,mem_filter,mem_range,mem_singleton]
        constructor
        . rintro ⟨hj,hr⟩
          by_cases h0 : j=j0
          . subst j;simp [d] at hr
          . by_cases h1 : j=j1
            . subst j;simp [d,h0] at hr
            . by_cases hv_j : j=iI j0 j1 jv'
              . exact hv_j
              . simp only [d,if_neg h0,if_neg h1,if_neg hv_j] at hr
                have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
                rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
                . rw [hr] at htop;cases htop
                . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
        . rintro rfl;exact ⟨hjv_C_lt,by simp [d,hjv_C_ne.1,hjv_C_ne.2]⟩
       have hZLP : zLeaves d p={p.val,iW n j0 j1 (d'.bw s0)}:=by
        ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton,d]
        constructor
        . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
          . exact Or.inl rfl
          . by_cases has : a=s0
            . subst a;right;simp [hpq.symm]
            . rw [if_neg has] at htie
              by_cases hap : a=p
              . rw [if_pos hap] at htie;cases htie
              . rw [if_neg hap] at htie
                have hown:=(hvD.2.2.2.1 a p htie).2
                exact absurd (hvD.2.2.1.1 p a hown).2 hpNC
        . rintro (rfl | rfl)
          . exact Or.inl rfl
          . right;exact ⟨s0,⟨Or.inr hs0,by simp⟩,by simp [hpq.symm]⟩
       have ho_gates_p : gatesOf d C Kind.o p.val={j0}:=by
        ext j;simp only [gatesOf,mem_filter,mem_range,mem_singleton]
        constructor
        . rintro ⟨hj,hr⟩
          by_cases h0 : j=j0
          . exact h0
          . by_cases h1 : j=j1
            . subst j;simp [d,h0] at hr
            . by_cases hv_j : j=iI j0 j1 jv'
              . subst j;simp [d,h0,h1] at hr
              . simp only [d,if_neg h0,if_neg h1,if_neg hv_j] at hr
                have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
                rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
                . rw [hr] at htop;cases htop
                . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
        . rintro rfl;exact ⟨by omega,by simp [d]⟩
       have hOLP : oLeaves d p={l.val,u}:=by
        ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
         mem_insert,mem_singleton,d]
        constructor
        . rintro ⟨r,hown,rfl⟩
          by_cases hrl : r=l
          . subst r;left;simp
          . by_cases hrs : r=s0
            . subst r;right;simp [hql]
            . simp only [hrl,hrs,or_self,↓reduceIte] at hown
              exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
        . rintro (rfl | rfl)
          . exact ⟨l,by simp,by simp⟩
          . exact ⟨s0,by simp,by simp [hql]⟩
       refine ⟨⟨j1,hj1,by simp [d],by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte],hop1,
        by simp only [d,↓reduceIte];rcases hvin with h | h;exact Or.inr h;exact Or.inl h⟩,
        ?_,?_,?_⟩
       . rw [hz_gates_p,hZLP];simp only [d,↓reduceIte];rw [hv_eq_jvC]
         have hne_ps : p.val≠iW n j0 j1 (d'.bw s0):=by
          obtain ⟨js,_,hbw,_⟩:=bwS hvD s0 hs0
          rw [hbw];unfold iW;rw [if_neg (by omega)];have:=p.isLt;omega
         have hne_pjv : p.val≠n+iI j0 j1 jv':=by have:=p.isLt;omega
         have hne_sjv : iW n j0 j1 (d'.bw s0)≠n+iI j0 j1 jv':=by
          intro h
          have h' : iW n j0 j1 (d'.bw s0)=iW n j0 j1 v':=by rwa [← hv_eq_jvC,hv_eq] at h
          have h1:=invWire_inj hj01 h'
          exact (hvD.2.2.2.2.2.2.2.1 (d'.bw s0) hw0'L).1 ⟨by omega,by rw [h1,hv'_eq_jv];simpa using hjv'T⟩
         exact otSG hne_ps hne_pjv hne_sjv hjv_C_op hjv_C_in
       . rw [ho_gates_p,hOLP];simp only [d,↓reduceIte]
         exact otSG hul.symm (by have:=l.isLt;omega) (by omega) hop0 huin
       . intro r hown;simp only [d] at hown
         by_cases hrl : r=l
         . subst hrl;unfold LamOK
           have hl_nc : r ∉ d.cover:=by simp only [d,mem_insert,not_or];exact ⟨hlp,hlNC⟩
           rw [if_neg hl_nc];simp [d]
         . by_cases hrs : r=s0
           . subst hrs;unfold LamOK
             have hr_c : r ∈ d.cover:=mem_insert_of_mem hs0
             rw [if_pos hr_c]
             have hLE : d.lam p r=u:=by simp [d,hrl]
             rw [hLE]
             refine ⟨?_,?_,?_⟩
             ·
              have hRZ : OrReach n D (gatesOf d' D Kind.z r.val) u' r.val:=by
               rcases huC with h1 | ⟨_,hc,j,hj,h1,hrole⟩
               . rw [h1];exact ReflTransGen.refl
               . exact (icZIR hvD hs0 (Or.inr ⟨j,hj,h1,hrole⟩)).mp hc
              have hRC : OrReach n C ((gatesOf d' D Kind.z r.val).image (iI j0 j1)) (iW n j0 j1 u') (iW n j0 j1 r.val) :=
               orLI (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
                (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
                 have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
                 rw [h1] at h2;cases h2)) hRZ
              rw [← hu_eq] at hRC
              have hinv_r : iW n j0 j1 r.val=r.val:=by unfold iW;rw [if_pos r.isLt]
              rw [hinv_r] at hRC
              exact icORZ hrbC hr_c (fun j hj => by
               obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
               have hj'lt:=gatesOf_lt j' hj'
               have hj'ne : j'≠jv':=fun h => by
                subst h;have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hjv'T).2
                rw [h1] at h2;cases h2
               exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
                by rw [hRS j' hj'lt hj'ne,(mem_filter.mp hj').2]⟩) hRC
             . rcases huC with h1 | ⟨_,_,j,hj,h1,hrole⟩
               . left;rw [hu_eq,h1];unfold iW;rw [if_pos r.isLt]
               . right
                 have hjne : j≠jv':=fun h => by
                  subst h;have h2:=(mem_filter.mp hjv'T).2;rw [hrole] at h2;cases h2
                 exact ⟨iI j0 j1 j,invIdx_lt hj01 hj1 (by omega : j+2 < C.gates.length),
                  by rw [hu_eq,h1];unfold iW;rw [if_neg (by omega)];simp,
                  by rw [hRS j hj hjne,hrole]⟩
             . intro _;simp only [d,if_neg hpq.symm,← hu'_zroot,hu_eq]
           . simp only [hrl,hrs,or_self,and_false,↓reduceIte] at hown
             exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
     ·
      have htp : t≠p:=fun h => hpNC (h ▸ ht')
      obtain ⟨j',hj',hbw',hrol',hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht').1
      have hj'notT : j' ∉ topGates d' D:=fun h => by
       have h2:=(mem_filter.mp h).2;rw [hrol'] at h2;cases h2
      have hj'ne : j'≠jv':=fun h => hj'notT (h ▸ hjv'T)
      have hterm_t : TermOK n C d t:=by
       refine ⟨iI j0 j1 j',invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
        by simp [d,htp,hbw'];unfold iW;rw [if_neg (by omega)];simp,
        by rw [hRS j' hj' hj'ne,hrol'],
        by rw [(hIF j' hj').1,hop'],?_⟩
       have hin_C:=hNTI j' hj' hj'notT
       simp only [d,if_neg htp]
       rcases hin' with h | h
       . left;rw [hin_C,h];rfl
       . right;rw [hin_C,h];rfl
      have hz_t : IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t):=by
       rw [hGOO t ht' Kind.z (by decide)]
       have hLeq : zLeaves d t=(zLeaves d' t).image (iW n j0 j1):=by
        ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,d]
        constructor
        . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
          . exact ⟨t.val,Or.inl rfl,by unfold iW;rw [if_pos t.isLt]⟩
          . by_cases has : a=s0
            . rw [if_pos has] at htie;exact absurd (Option.some.inj htie) htp.symm
            . rw [if_neg has] at htie
              by_cases hap : a=p
              . rw [if_pos hap] at htie;cases htie
              . rw [if_neg hap] at htie
                have ha' : a ∈ d'.cover:=by rcases ha with rfl | ha';exact absurd rfl hap;exact ha'
                exact ⟨d'.bw a,Or.inr ⟨a,⟨ha',htie⟩,rfl⟩,by simp [hap]⟩
        . rintro ⟨w',hw',rfl⟩
          rcases hw' with rfl | ⟨a,⟨ha',htie⟩,rfl⟩
          . left;unfold iW;rw [if_pos t.isLt]
          . right
            have hap : a≠p:=fun h => hpNC (h ▸ ha')
            have has : a≠s0:=fun h => by rw [h,hties0] at htie;cases htie
            exact ⟨a,⟨Or.inr ha',by simp [has,hap,htie]⟩,by simp [hap]⟩
       rw [hLeq];simp only [d,if_neg htp]
       exact otLI (hvD.2.2.2.2.2.1 t ht').2.1 (iI j0 j1) (iW n j0 j1)
        (fun _ _ _ _ h => invIdx_inj hj01 h)
        (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
        (fun a b _ _ h => invWire_inj hj01 h)
        (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
        (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
         have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
         rw [h1] at h2;cases h2))
      have ho_t : IsOrTree n C (gatesOf d C Kind.o t.val) (oLeaves d t) (d.oroot t):=by
       rw [hGOO t ht' Kind.o (by decide)]
       have hLeq : oLeaves d t=(oLeaves d' t).image (iW n j0 j1):=by
        ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,d,htp,false_and,↓reduceIte]
        constructor
        . rintro ⟨r,hr,rfl⟩;exact ⟨d'.lam t r,⟨r,hr,rfl⟩,rfl⟩
        . rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩;exact ⟨r,hr,rfl⟩
       rw [hLeq];simp only [d,if_neg htp]
       exact otLI (hvD.2.2.2.2.2.1 t ht').2.2.1 (iI j0 j1) (iW n j0 j1)
        (fun _ _ _ _ h => invIdx_inj hj01 h)
        (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
        (fun a b _ _ h => invWire_inj hj01 h)
        (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
        (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
         have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
         rw [h1] at h2;cases h2))
      have hlam_t : ∀ r,d.owns t r=true->LamOK n C d t r:=by
       intro r hown;simp only [d,htp,false_and,↓reduceIte] at hown
       have hrp : r≠p:=((hK2 t r).mp (hvD.2.2.1.1 t r hown).1).2.2.2.2
       have hl':=(hvD.2.2.2.2.2.1 t ht').2.2.2 r hown
       unfold LamOK at hl' ⊢
       have hRCI : r ∈ d.cover↔r ∈ d'.cover:=by simp [d,hrp]
       by_cases hrc : r ∈ d'.cover
       . rw [if_pos hrc] at hl';rw [if_pos (hRCI.mpr hrc)]
         have hRZ:=(icZIR hvD hrc hl'.2.1).mp hl'.1
         have hRC:=orLI
          (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
          (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
           have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
           rw [h1] at h2;cases h2)) hRZ
         have hinv_r : iW n j0 j1 r.val=r.val:=by unfold iW;rw [if_pos r.isLt]
         rw [hinv_r] at hRC
         refine ⟨?_,?_,?_⟩
         . simp only [d,if_neg htp]
           exact icORZ hrbC (hRCI.mpr hrc) (fun j hj => by
            obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
            have hj'lt:=gatesOf_lt j' hj'
            have hj'ne : j'≠jv':=fun h => by
             subst h;have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hjv'T).2
             rw [h1] at h2;cases h2
            exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
             by rw [hRS j' hj'lt hj'ne,(mem_filter.mp hj').2]⟩) hRC
         . have hlam_d : d.lam t r=iW n j0 j1 (d'.lam t r):=by simp [d,htp]
           rw [hlam_d]
           rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
           . left;rw [h1,hinv_r]
           . right
             have hkne : k≠jv':=fun h => by
              rw [h] at h2;have h3:=(mem_filter.mp hjv'T).2;rw [h2] at h3;cases h3
             exact ⟨iI j0 j1 k,invIdx_lt hj01 hj1 (by omega : k+2 < C.gates.length),
              by rw [h1];unfold iW;rw [if_neg (by omega)];simp,
              by rw [hRS k hk hkne,h2]⟩
         . intro htie;simp only [d,if_neg hrp] at htie ⊢
           by_cases hrs : r=s0
           . rw [if_pos hrs] at htie;exact absurd (Option.some.inj htie) htp.symm
           . rw [if_neg hrs] at htie
             simp only [if_neg htp,hl'.2.2 htie]
       . rw [if_neg hrc] at hl';rw [if_neg (fun h => hrc (hRCI.mp h))]
         simp only [d,if_neg htp,hl'];unfold iW;rw [if_pos r.isLt]
      exact ⟨hterm_t,hz_t,ho_t,hlam_t⟩
    ·
     have hTGs : topGates d C=((topGates d' D).erase jv').image (iI j0 j1):=by
      ext j;simp only [topGates,mem_filter,mem_range,mem_image,mem_erase]
      constructor
      . rintro ⟨hj,hr⟩
        have h0 : j≠j0:=fun h => by rw [h] at hr;simp [d] at hr
        have h1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),↓reduceIte] at hr;cases hr
        have hv_j : j≠iI j0 j1 jv':=fun h => by rw [h] at hr;simp [d,hjv_C_ne.1,hjv_C_ne.2] at hr
        simp only [d,if_neg h0,if_neg h1,if_neg hv_j] at hr
        have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
        have hidx_ne : iM j0 j1 j≠jv':=fun h => hv_j (by rw [← h,invIdx_idxMap hj01 h0 h1])
        exact ⟨iM j0 j1 j,⟨hidx_ne,hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
      . rintro ⟨j',⟨hne_jv,hj'lt,hr'⟩,rfl⟩
        exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
         by rw [hRS j' hj'lt hne_jv,hr']⟩
     have hTLs : topLeaves d A =
      insert (n+j1) ((((topLeaves d' (insert p A)).erase p.val).erase (d'.bw s0)).image (iW n j0 j1)):=by
      ext x;simp only [topLeaves,mem_union,mem_image,mem_filter,
       mem_insert,mem_erase,d]
      constructor
      . rintro (⟨a,haA,rfl⟩ | ⟨t,⟨htc,htie⟩,rfl⟩)
        . right
          have hap : a≠p:=fun h => hpA (h ▸ haA)
          have hne_bw : a.val≠d'.bw s0:=by
           obtain ⟨js,_,hbw,_⟩:=bwS hvD s0 hs0;have:=a.isLt;omega
          exact ⟨a.val,⟨hne_bw,fun h => hap (Fin.ext h),Or.inl ⟨a,Or.inr haA,rfl⟩⟩,
           by unfold iW;rw [if_pos a.isLt]⟩
        . by_cases htp : t=p
          . subst t;left;simp
          . right;rw [if_neg htp]
            by_cases hts : t=s0
            . rw [if_pos hts] at htie;cases htie
            . rw [if_neg hts,if_neg htp] at htie
              have ht' : t ∈ d'.cover:=by rcases htc with rfl | h;exact absurd rfl htp;exact h
              have hne_bw : d'.bw t≠d'.bw s0:=fun h => hts (bw_injOn hvD d'.cover (Finset.Subset.refl _) ht' hs0 h)
              have hne_p : d'.bw t≠p.val:=by
               obtain ⟨jt,_,hbw,_⟩:=bwS hvD t ht';have:=p.isLt;omega
              exact ⟨d'.bw t,⟨hne_bw,hne_p,Or.inr ⟨t,⟨ht',htie⟩,rfl⟩⟩,rfl⟩
      . rintro (rfl | ⟨w',⟨hne_s,hne_p,hw'⟩,rfl⟩)
        . right;exact ⟨p,⟨Or.inl rfl,by simp [hpq]⟩,by simp⟩
        . rcases hw' with ⟨a,ha,rfl⟩ | ⟨t,⟨ht',htie⟩,rfl⟩
          . rcases ha with rfl | haA
            . exact absurd rfl hne_p
            . left;exact ⟨a,haA,by unfold iW;rw [if_pos a.isLt]⟩
          . right
            have htp : t≠p:=fun h => hpNC (h ▸ ht')
            have hts : t≠s0:=fun h => hne_s (by rw [h])
            exact ⟨t,⟨Or.inr ht',by simp [hts,htp,htie]⟩,by simp [htp]⟩
     have hCE : C.output=if D.output=n+jv' then n+j1 else iW n j0 j1 D.output:=by
      rw [← hv'_eq_jv]
      by_cases h : D.output=v'
      . rw [if_pos h];exact hTSC.1 h.symm
      . rw [if_neg h]
        have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
        have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
        rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
        . exact absurd hveq h
        . exact heq
     rw [hTGs,hTLs,hCE]
     exact otLR hvD.1 topGates_lt hvD.2.2.2.2.2.2 hjv'T hp_mem_top hw0'L
      (Ne.symm hne0) hjv'_in (iI j0 j1) (iW n j0 j1)
      (fun _ _ _ _ h => invIdx_inj hj01 h)
      (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
      (fun a b _ _ h => invWire_inj hj01 h)
      (fun a _ => (invWire_ne_j0_j1 (w':=a) hj01).2)
      (fun j' hj' => (hIF j' (topGates_lt j' (Finset.mem_of_mem_erase hj'))).1)
      (fun j' hj' => by rw [← hv'_eq_jv];exact hTSC.2 j' (Finset.mem_of_mem_erase hj'))
   ·
    obtain ⟨hs0_only_q,hqNC⟩:=hOSQ s0 hs0 hties0 hs0q hreach0
    have hu'_eq_q : u'=q.val:=by
     rcases huC with h | ⟨hq,_⟩
     . exact h
     . exact absurd hq hqNC
    have hu_eq_q : u=q.val:=by rw [hu_eq,hu'_eq_q];unfold iW;rw [if_pos q.isLt]
    have hs0_owns_q : d'.owns s0 q=true:=by
     obtain ⟨r,hown⟩:=ownHOE hvD hs0
     rw [← hs0_only_q r hown];exact hown
    have hs0_ne_p : s0≠p:=fun h => hpNC (h ▸ hs0)
    have hs0_ne_l : s0≠l:=fun h => hlNC (h ▸ hs0)
    have hno_tie_s0 : ∀ a,d'.tie a≠some s0:=by
     intro a htie
     have hown:=(hvD.2.2.2.1 a s0 htie).2
     have haq:=hs0_only_q a hown
     exact hqNC (haq ▸ (hvD.2.2.2.1 a s0 htie).1)
    have hz_s0_empty : gatesOf d' D Kind.z s0.val=∅:=by
     have hz_l : zLeaves d' s0={s0.val}:=by
      ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton]
      constructor
      . rintro (rfl | ⟨a,⟨_,htie⟩,_⟩);rfl;exact absurd htie (hno_tie_s0 a)
      . rintro rfl;exact Or.inl rfl
     have hc:=tree_card n D _ _ _ (hvD.2.2.2.2.2.1 s0 hs0).2.1
     rw [hz_l,card_singleton] at hc
     exact card_eq_zero.mp (by omega)
    have ho_s0_empty : gatesOf d' D Kind.o s0.val=∅:=by
     have ho_l : oLeaves d' s0={q.val}:=by
      ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      . rintro ⟨r,hown,rfl⟩
        have hrq:=hs0_only_q r hown;subst hrq
        have hl:=(hvD.2.2.2.2.2.1 s0 hs0).2.2.2 r hown
        unfold LamOK at hl;rw [if_neg hqNC] at hl;exact hl
      . rintro rfl
        have hl:=(hvD.2.2.2.2.2.1 s0 hs0).2.2.2 q hs0_owns_q
        unfold LamOK at hl;rw [if_neg hqNC] at hl
        exact ⟨q,hs0_owns_q,hl⟩
     have hc:=tree_card n D _ _ _ (hvD.2.2.2.2.2.1 s0 hs0).2.2.1
     rw [ho_l,card_singleton] at hc
     exact card_eq_zero.mp (by omega)
    have hzr_s0 : d'.zroot s0=s0.val:=by
     have h:=(hvD.2.2.2.2.2.1 s0 hs0).2.1.2.2.2;rw [if_pos hz_s0_empty] at h
     have hmem : s0.val ∈ zLeaves d' s0:=mem_insert_self _ _
     rw [h,mem_singleton] at hmem;exact hmem.symm
    have hor_s0 : d'.oroot s0=q.val:=by
     have h:=(hvD.2.2.2.2.2.1 s0 hs0).2.2.1.2.2.2;rw [if_pos ho_s0_empty] at h
     have hlam:=(hvD.2.2.2.2.2.1 s0 hs0).2.2.2 q hs0_owns_q
     unfold LamOK at hlam;rw [if_neg hqNC] at hlam
     have hmem : q.val ∈ oLeaves d' s0:=mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_univ _,hs0_owns_q⟩,hlam⟩
     rw [h,mem_singleton] at hmem;exact hmem.symm
    obtain ⟨jb',hjb'lt,hbw_s0,hrol_s0,hop_s0,hin_s0⟩:=(hvD.2.2.2.2.2.1 s0 hs0).1
    have hjb'notT : jb' ∉ topGates d' D:=fun h => by
     have h2:=(mem_filter.mp h).2;rw [hrol_s0] at h2;cases h2
    have hjb'ne_jv : jb'≠jv':=fun h => hjb'notT (h ▸ hjv'T)
    have hjb_C_lt : iI j0 j1 jb' < C.gates.length:=invIdx_lt hj01 hj1 (by omega : jb'+2 < C.gates.length)
    have hjb_C_ne:=invIdx_ne (j':=jb') hj01
    have hjb_C_ne_jv : iI j0 j1 jb'≠iI j0 j1 jv':=fun h => hjb'ne_jv (invIdx_inj hj01 h)
    let covNew : Finset (Fin n):=insert p (insert q (d'.cover.erase s0))
    have hmin_cov_swap : IsMinCover K covNew:=by
     have hcard_new : covNew.card=d'.cover.card+1:=by
      have hq_ne : q ∉ d'.cover.erase s0:=fun h => hqNC (Finset.mem_of_mem_erase h)
      have hp_ne : p ∉ insert q (d'.cover.erase s0):=by
       simp only [mem_insert,mem_erase,not_or];exact ⟨hpq,fun h => hpNC h.2⟩
      rw [card_insert_of_notMem hp_ne,card_insert_of_notMem hq_ne]
      have:=card_erase_add_one hs0;omega
     refine ⟨?_,?_⟩
     . intro a b hab
       by_cases hap : a=p
       . left;simp [covNew,hap]
       . by_cases hbp : b=p
         . right;simp [covNew,hbp]
         . have hal : a≠l:=fun h => hbp ((hl b).mp (h ▸ hab))
           have hbl : b≠l:=fun h => hap ((hl a).mp (h ▸ hab.symm))
           have hab2 : K2.Adj a b:=(hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩
           have hne:=hvD.2.2.1.2 a b hab2
           have hcase : d'.owns a b=true\/d'.owns b a=true:=by
            cases h1 : d'.owns a b <;> cases h2 : d'.owns b a
            . exfalso;rw [h1,h2] at hne;exact hne rfl
            . exact Or.inr rfl
            . exact Or.inl rfl
            . exact Or.inl rfl
           rcases hcase with h1 | h2
           . by_cases has : a=s0
             . subst has;right;rw [hs0_only_q b h1];simp [covNew]
             . left;exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨has,(hvD.2.2.1.1 a b h1).2⟩))
           . by_cases hbs : b=s0
             . subst hbs;left;rw [hs0_only_q a h2];simp [covNew]
             . right;exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hbs,(hvD.2.2.1.1 b a h2).2⟩))
     . intro T' hT'
       rw [hcard_new]
       have h:=hMCP.2 T' hT'
       rw [card_insert_of_notMem hpNC] at h;exact h
    let d : NCCData n:={
     cover:=covNew
     owns:=fun a b =>
      if a=p/\(b=l\/b=q) then true
      else if a=q/\b=s0 then true
      else if a=s0/\b=q then false
      else d'.owns a b
     tie:=fun a => if a=q then some p else if a=p then none else d'.tie a
     role:=fun j =>
      if j=j0 then (Kind.o,p.val)
      else if j=j1 then (Kind.b,p.val)
      else if j=iI j0 j1 jv' then (Kind.z,p.val)
      else if j=iI j0 j1 jb' then (Kind.b,q.val)
      else d'.role (iM j0 j1 j)
     bw:=fun a =>
      if a=p then n+j1
      else if a=q then iW n j0 j1 (d'.bw s0)
      else iW n j0 j1 (d'.bw a)
     zroot:=fun a =>
      if a=p then v
      else if a=q then q.val
      else iW n j0 j1 (d'.zroot a)
     oroot:=fun a =>
      if a=p then n+j0
      else if a=q then s0.val
      else iW n j0 j1 (d'.oroot a)
     lam:=fun a b =>
      if a=p then (if b=l then l.val else q.val)
      else if a=q then s0.val
      else iW n j0 j1 (d'.lam a b)
    }
    have hRS : ∀ j' < D.gates.length,j'≠jv'->j'≠jb'->d.role (iI j0 j1 j')=d'.role j':=by
     intro j' hj' hne_jv hne_jb
     have hne:=invIdx_ne (j':=j') hj01
     have hne_i1 : iI j0 j1 j'≠iI j0 j1 jv':=fun h => hne_jv (invIdx_inj hj01 h)
     have hne_i2 : iI j0 j1 j'≠iI j0 j1 jb':=fun h => hne_jb (invIdx_inj hj01 h)
     simp only [d,if_neg hne.1,if_neg hne.2,if_neg hne_i1,if_neg hne_i2,idxMap_invIdx hj01]
    have hGOO : ∀ t ∈ d'.cover.erase s0,∀ k : Kind,k≠Kind.top →
     gatesOf d C k t.val=(gatesOf d' D k t.val).image (iI j0 j1):=by
     intro t ht k hk_ne
     have ht' : t ∈ d'.cover:=Finset.mem_of_mem_erase ht
     have hts : t≠s0:=(mem_erase.mp ht).1
     have htp : t≠p:=fun h => hpNC (h ▸ ht')
     have htq : t≠q:=fun h => hqNC (h ▸ ht')
     ext j;simp only [gatesOf,mem_filter,mem_range,mem_image]
     constructor
     . rintro ⟨hj,hr⟩
       have hjne0 : j≠j0:=fun h => by rw [h] at hr;simp only [d,if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hjne1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hjnev : j≠iI j0 j1 jv':=fun h => by rw [h] at hr;simp only [d,if_neg hjv_C_ne.1,if_neg hjv_C_ne.2,if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hjneb : j≠iI j0 j1 jb':=fun h => by rw [h] at hr;simp only [d,if_neg hjb_C_ne.1,if_neg hjb_C_ne.2,if_neg hjb_C_ne_jv,if_pos rfl] at hr;exact htq (Fin.ext (Prod.ext_iff.mp hr).2).symm
       have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj hjne0 hjne1;omega
       simp only [d,if_neg hjne0,if_neg hjne1,if_neg hjnev,if_neg hjneb] at hr
       exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 hjne0 hjne1⟩
     . rintro ⟨j',⟨hj',hr'⟩,rfl⟩
       have hj'ne1 : j'≠jv':=fun h => by rw [h] at hr';have ht1:=(mem_filter.mp hjv'T).2;rw [hr'] at ht1;exact hk_ne (by simpa using ht1)
       have hj'ne2 : j'≠jb':=fun h => by rw [h] at hr';rw [hrol_s0] at hr';exact hts (Fin.ext (Prod.ext_iff.mp hr').2).symm
       exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj' hj'ne1 hj'ne2,hr']⟩
    refine ⟨d,hrbC,hmin_cov_swap,?_,?_,?_,?_,?_⟩
    ·
     refine ⟨?_,?_⟩
     . intro a b hown;simp only [d] at hown
       split_ifs at hown with h1 h2 h3
       . rcases h1 with ⟨hap,hbl | hbq⟩
         . subst a;subst b;exact ⟨hLPA.symm,mem_insert_self _ _⟩
         . subst a;subst b;exact ⟨hPQA,mem_insert_self _ _⟩
       . rcases h2 with ⟨haq,hbs0⟩;subst a;subst b
         exact ⟨((hK2 s0 q).mp (hvD.2.2.1.1 s0 q hs0_owns_q).1).1.symm,mem_insert_of_mem (mem_insert_self _ _)⟩
       . have h2':=hvD.2.2.1.1 a b hown
         have has0 : a≠s0:=fun h => by rw [h] at hown;exact h3 ⟨h,hs0_only_q b hown⟩
         exact ⟨((hK2 a b).mp h2'.1).1,mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨has0,h2'.2⟩))⟩
     . intro a b hab;simp only [d]
       by_cases hap : a=p
       . subst a
         rcases (hp b).mp hab with hbl | hbq
         . subst b
           have hnot : d'.owns l p=false:=by
            cases h : d'.owns l p;rfl;exfalso;exact ((hK2 l p).mp (hvD.2.2.1.1 l p h).1).2.1 rfl
           simp [hlp,hql.symm,hs0_ne_p.symm,hnot]
         . subst b
           have hnot : d'.owns q p=false:=by
            cases h : d'.owns q p;rfl;exfalso;exact ((hK2 q p).mp (hvD.2.2.1.1 q p h).1).2.2.2.2 rfl
           simp [hpq.symm,hs0_ne_p.symm,hnot]
       . by_cases hbp : b=p
         . subst b
           rcases (hp a).mp hab.symm with hal | haq
           . subst a
             have hnot : d'.owns l p=false:=by
              cases h : d'.owns l p;rfl;exfalso;exact ((hK2 l p).mp (hvD.2.2.1.1 l p h).1).2.1 rfl
             simp [hap,hql.symm,hs0_ne_p.symm,hnot]
           . subst a
             have hnot : d'.owns q p=false:=by
              cases h : d'.owns q p;rfl;exfalso;exact ((hK2 q p).mp (hvD.2.2.1.1 q p h).1).2.2.2.2 rfl
             simp [hap,hs0_ne_p.symm,hnot]
         . have hal : a≠l:=fun h => hbp ((hl b).mp (h ▸ hab))
           have hbl : b≠l:=fun h => hap ((hl a).mp (h ▸ hab.symm))
           by_cases hqs : a=q/\b=s0
           . rcases hqs with ⟨haq,hbs0⟩;subst a;subst b;simp [hap,hbp,hs0q,Ne.symm hs0q]
           . by_cases hsq : a=s0/\b=q
             . rcases hsq with ⟨has0,hbq⟩;subst a;subst b;simp [hap,hbp,hs0q,Ne.symm hs0q]
             . have hqs' : ¬ (b=q/\a=s0):=fun h => hsq ⟨h.2,h.1⟩
               have hsq' : ¬ (b=s0/\a=q):=fun h => hqs ⟨h.2,h.1⟩
               simp only [hap,hbp,false_and,↓reduceIte,hqs,hsq,hqs',hsq']
               exact hvD.2.2.1.2 a b ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩)
    ·
     intro a b htie;simp only [d] at htie
     by_cases haq : a=q
     . subst a;rw [if_pos rfl] at htie;cases htie
       exact ⟨mem_insert_of_mem (mem_insert_self _ _),by simp [d]⟩
     . rw [if_neg haq] at htie
       by_cases hap : a=p
       . rw [if_pos hap] at htie;cases htie
       . rw [if_neg hap] at htie
         have h2:=hvD.2.2.2.1 a b htie
         have has0 : a≠s0:=fun h => by rw [h,hties0] at htie;cases htie
         have hbs0 : b≠s0:=fun h => hno_tie_s0 a (h ▸ htie)
         refine ⟨mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨has0,h2.1⟩)),?_⟩
         simp only [d];split_ifs with c1 c2 c3
         . rfl
         . rfl
         . exact absurd c3.1 hbs0
         . exact h2.2
    ·
     intro j hj
     by_cases h0 : j=j0
     . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d],fun h => by simp [d] at h⟩
     . by_cases h1 : j=j1
       . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d,h0],fun _ => by simp [d]⟩
       . by_cases hv_j : j=iI j0 j1 jv'
         . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d,h0,h1],fun h => by simp [d,h0,h1] at h⟩
         . by_cases hb_j : j=iI j0 j1 jb'
           . subst j;right
             refine ⟨q,mem_insert_of_mem (mem_insert_self _ _),by simp [d,h0,h1,hv_j],fun _ => ?_⟩
             simp only [d,if_neg hpq.symm,↓reduceIte,hbw_s0]
             unfold iW;rw [if_neg (by omega : ¬ n+jb' < n)];simp only [Nat.add_sub_cancel_left]
           . have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
             have hrole_eq : d.role j=d'.role (iM j0 j1 j):=by simp [d,h0,h1,hv_j,hb_j]
             rw [hrole_eq]
             rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨t,ht,hrt,hrb⟩
             . exact Or.inl htop
             . by_cases htop : (d'.role (iM j0 j1 j)).1=Kind.top
               . exact Or.inl htop
               . right
                 have hts0 : t≠s0:=by
                  intro heq;subst t
                  cases hk : (d'.role (iM j0 j1 j)).1 with
                  | top => exact absurd hk htop
                  | z =>
                   have hmem : iM j0 j1 j ∈ gatesOf d' D Kind.z s0.val :=
                    mem_filter.mpr ⟨mem_range.mpr hIL,Prod.ext hk hrt⟩
                   rw [hz_s0_empty] at hmem;simp at hmem
                  | o =>
                   have hmem : iM j0 j1 j ∈ gatesOf d' D Kind.o s0.val :=
                    mem_filter.mpr ⟨mem_range.mpr hIL,Prod.ext hk hrt⟩
                   rw [ho_s0_empty] at hmem;simp at hmem
                  | b =>
                   have h1':=hrb hk;rw [hbw_s0] at h1'
                   have : iM j0 j1 j=jb':=by omega
                   exact hb_j (by rw [← this,invIdx_idxMap hj01 h0 h1])
                 have htp : t≠p:=fun h => hpNC (h ▸ ht)
                 have htq : t≠q:=fun h => hqNC (h ▸ ht)
                 refine ⟨t,mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hts0,ht⟩)),hrt,fun hb => ?_⟩
                 simp only [d,if_neg htp,if_neg htq];rw [hrb hb]
                 unfold iW;rw [if_neg (by omega)]
                 have : n+iM j0 j1 j - n=iM j0 j1 j:=by omega
                 rw [this,invIdx_idxMap hj01 h0 h1]
    ·
     intro t ht
     rcases mem_insert.mp ht with htp | ht1
     . subst t
       have hz_gates_p : gatesOf d C Kind.z p.val={iI j0 j1 jv'}:=by
        ext j;simp only [gatesOf,mem_filter,mem_range,mem_singleton]
        constructor
        . rintro ⟨hj,hr⟩
          by_cases h0 : j=j0
          . subst j;simp [d] at hr
          . by_cases h1 : j=j1
            . subst j;simp [d,h0] at hr
            . by_cases hv_j : j=iI j0 j1 jv'
              . exact hv_j
              . by_cases hb_j : j=iI j0 j1 jb'
                . subst j;simp [d,h0,h1,hv_j] at hr
                . simp only [d,if_neg h0,if_neg h1,if_neg hv_j,if_neg hb_j] at hr
                  have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
                  rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
                  . rw [hr] at htop;cases htop
                  . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
        . rintro rfl;exact ⟨hjv_C_lt,by simp [d,hjv_C_ne.1,hjv_C_ne.2]⟩
       have hZLP : zLeaves d p={p.val,iW n j0 j1 (d'.bw s0)}:=by
        ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton,d]
        constructor
        . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
          . exact Or.inl rfl
          . by_cases haq : a=q
            . subst a;right;simp [hpq.symm]
            . rw [if_neg haq] at htie
              by_cases hap : a=p
              . rw [if_pos hap] at htie;cases htie
              . rw [if_neg hap] at htie
                exact absurd (hvD.2.2.1.1 p a (hvD.2.2.2.1 a p htie).2).2 hpNC
        . rintro (rfl | rfl)
          . exact Or.inl rfl
          . right;exact ⟨q,⟨mem_insert_of_mem (mem_insert_self _ _),by simp⟩,by simp [hpq.symm]⟩
       have ho_gates_p : gatesOf d C Kind.o p.val={j0}:=by
        ext j;simp only [gatesOf,mem_filter,mem_range,mem_singleton]
        constructor
        . rintro ⟨hj,hr⟩
          by_cases h0 : j=j0
          . exact h0
          . by_cases h1 : j=j1
            . subst j;simp [d,h0] at hr
            . by_cases hv_j : j=iI j0 j1 jv'
              . subst j;simp [d,h0,h1] at hr
              . by_cases hb_j : j=iI j0 j1 jb'
                . subst j;simp [d,h0,h1,hv_j] at hr
                . simp only [d,if_neg h0,if_neg h1,if_neg hv_j,if_neg hb_j] at hr
                  have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
                  rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
                  . rw [hr] at htop;cases htop
                  . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
        . rintro rfl;exact ⟨by omega,by simp [d]⟩
       have hOLP : oLeaves d p={l.val,q.val}:=by
        ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
         mem_insert,mem_singleton,d]
        constructor
        . rintro ⟨r,hown,rfl⟩
          by_cases hrl : r=l
          . subst r;left;simp
          . by_cases hrq : r=q
            . subst r;right;simp [hql]
            . simp only [hrl,hrq,or_self,and_false,↓reduceIte,hpq,hs0_ne_p.symm] at hown
              exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
        . rintro (rfl | rfl)
          . exact ⟨l,by simp,by simp⟩
          . exact ⟨q,by simp,by simp [hql]⟩
       refine ⟨⟨j1,hj1,by simp [d],by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte],hop1,
        by simp only [d,↓reduceIte];rcases hvin with h | h;exact Or.inr h;exact Or.inl h⟩,
        ?_,?_,?_⟩
       . rw [hz_gates_p,hZLP];simp only [d,↓reduceIte];rw [hv_eq_jvC]
         have hne_ps : p.val≠iW n j0 j1 (d'.bw s0):=by
          rw [hbw_s0];unfold iW;rw [if_neg (by omega)];have:=p.isLt;omega
         have hne_pjv : p.val≠n+iI j0 j1 jv':=by have:=p.isLt;omega
         have hne_sjv : iW n j0 j1 (d'.bw s0)≠n+iI j0 j1 jv':=by
          intro h
          have h' : iW n j0 j1 (d'.bw s0)=iW n j0 j1 v':=by rwa [← hv_eq_jvC,hv_eq] at h
          have h1:=invWire_inj hj01 h'
          exact (hvD.2.2.2.2.2.2.2.1 (d'.bw s0) hw0'L).1 ⟨by omega,by rw [h1,hv'_eq_jv];simpa using hjv'T⟩
         exact otSG hne_ps hne_pjv hne_sjv hjv_C_op hjv_C_in
       . rw [ho_gates_p,hOLP];simp only [d,↓reduceIte]
         exact otSG (fun h => hql (Fin.ext h.symm)) (by have:=l.isLt;omega)
          (by have:=q.isLt;omega) hop0 (hu_eq_q ▸ huin)
       . intro r hown;simp only [d] at hown
         by_cases hrl : r=l
         . subst hrl;unfold LamOK
           have hl_nc : r ∉ d.cover:=by
            simp only [d,covNew,mem_insert,mem_erase,not_or]
            exact ⟨hlp,hql.symm,fun h => hlNC h.2⟩
           rw [if_neg hl_nc];simp [d]
         . by_cases hrq : r=q
           . subst hrq;unfold LamOK
             have hr_c : r ∈ d.cover:=mem_insert_of_mem (mem_insert_self _ _)
             rw [if_pos hr_c]
             refine ⟨?_,?_,?_⟩
             . simp only [d,↓reduceIte,if_neg hrl];exact (isCentred_input n C d r).mpr hr_c
             . left;simp [d,hrl]
             . intro _;simp [d,hrl,hpq.symm]
           . simp only [hrl,hrq,or_self,and_false,↓reduceIte,hpq,hs0_ne_p.symm] at hown
             exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
     . rcases mem_insert.mp ht1 with htq | ht2
       . subst t
         have hz_gates_q : gatesOf d C Kind.z q.val=∅:=by
          ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
          intro hj hr
          by_cases h0 : j=j0
          . subst j;simp [d] at hr
          . by_cases h1 : j=j1
            . subst j;simp [d,h0] at hr
            . by_cases hv_j : j=iI j0 j1 jv'
              . subst j;simp [d,h0,h1] at hr;exact hpq (Fin.ext hr)
              . by_cases hb_j : j=iI j0 j1 jb'
                . subst j;simp [d,h0,h1,hv_j] at hr
                . simp only [d,if_neg h0,if_neg h1,if_neg hv_j,if_neg hb_j] at hr
                  have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
                  rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
                  . rw [hr] at htop;cases htop
                  . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hqNC
         have ho_gates_q : gatesOf d C Kind.o q.val=∅:=by
          ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
          intro hj hr
          by_cases h0 : j=j0
          . subst j;simp [d] at hr;exact hpq (Fin.ext hr)
          . by_cases h1 : j=j1
            . subst j;simp [d,h0] at hr
            . by_cases hv_j : j=iI j0 j1 jv'
              . subst j;simp [d,h0,h1] at hr
              . by_cases hb_j : j=iI j0 j1 jb'
                . subst j;simp [d,h0,h1,hv_j] at hr
                . simp only [d,if_neg h0,if_neg h1,if_neg hv_j,if_neg hb_j] at hr
                  have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
                  rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
                  . rw [hr] at htop;cases htop
                  . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hqNC
         have hz_leaves_q : zLeaves d q={q.val}:=by
          ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton,d]
          constructor
          . rintro (rfl | ⟨a,⟨_,htie⟩,_⟩)
            . rfl
            . by_cases haq : a=q
              . rw [if_pos haq] at htie;exact absurd (Option.some.inj htie) hpq
              . rw [if_neg haq] at htie
                by_cases hap : a=p
                . rw [if_pos hap] at htie;cases htie
                . rw [if_neg hap] at htie
                  exact absurd (hvD.2.2.1.1 q a (hvD.2.2.2.1 a q htie).2).2 hqNC
          . rintro rfl;exact Or.inl rfl
         have ho_leaves_q : oLeaves d q={s0.val}:=by
          ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
           mem_singleton,d]
          constructor
          . rintro ⟨r,hown,rfl⟩
            simp [hpq.symm]
          . rintro rfl
            exact ⟨s0,by simp [hpq.symm],by simp [hpq.symm]⟩
         have hin_jb_C : (gateAt C (iI j0 j1 jb')).inputs=[q.val,s0.val] ∨
          (gateAt C (iI j0 j1 jb')).inputs=[s0.val,q.val]:=by
          have h:=hNTI jb' hjb'lt hjb'notT
          rw [hzr_s0,hor_s0] at hin_s0
          have hinv_s0 : iW n j0 j1 s0.val=s0.val:=by unfold iW;rw [if_pos s0.isLt]
          have hinv_q : iW n j0 j1 q.val=q.val:=by unfold iW;rw [if_pos q.isLt]
          rcases hin_s0 with h1 | h1
          . right;rw [h,h1];simp [hinv_s0,hinv_q]
          . left;rw [h,h1];simp [hinv_s0,hinv_q]
         refine ⟨⟨iI j0 j1 jb',hjb_C_lt,
          by simp only [d,if_neg hpq.symm,↓reduceIte,hbw_s0];unfold iW;rw [if_neg (by omega : ¬ n+jb' < n)];simp only [Nat.add_sub_cancel_left],
          by simp [d,hjb_C_ne.1,hjb_C_ne.2,hjb_C_ne_jv],
          by rw [(hIF jb' hjb'lt).1,hop_s0],
          by simp only [d,if_neg hpq.symm,↓reduceIte];exact hin_jb_C⟩,
          ?_,?_,?_⟩
         . rw [hz_gates_q,hz_leaves_q];simp [IsOrTree,readsIn,d,hpq.symm]
         . rw [ho_gates_q,ho_leaves_q];simp [IsOrTree,readsIn,d,hpq.symm]
         . intro r hown;simp only [d,hpq.symm,false_and,↓reduceIte,true_and,Ne.symm hs0q] at hown
           by_cases hrs : r=s0
           . subst r;unfold LamOK
             have hs_nc : s0 ∉ d.cover:=by
              simp only [d,covNew,mem_insert,mem_erase,not_or]
              exact ⟨hs0_ne_p,hs0q,fun h => h.1 rfl⟩
             rw [if_neg hs_nc];simp [d,hpq.symm]
           . rw [if_neg hrs] at hown
             exact absurd (hvD.2.2.1.1 q r hown).2 hqNC
       ·
        have ht' : t ∈ d'.cover:=Finset.mem_of_mem_erase ht2
        have hts : t≠s0:=(mem_erase.mp ht2).1
        have htp : t≠p:=fun h => hpNC (h ▸ ht')
        have htq : t≠q:=fun h => hqNC (h ▸ ht')
        obtain ⟨j',hj',hbw',hrol',hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht').1
        have hj'notT : j' ∉ topGates d' D:=fun h => by
         have h2:=(mem_filter.mp h).2;rw [hrol'] at h2;cases h2
        have hj'ne1 : j'≠jv':=fun h => hj'notT (h ▸ hjv'T)
        have hj'ne2 : j'≠jb':=fun h => by subst h;rw [hrol_s0] at hrol';exact hts (Fin.ext (Prod.ext_iff.mp hrol').2).symm
        have hterm_t : TermOK n C d t:=by
         refine ⟨iI j0 j1 j',invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
          by simp only [d,if_neg htp,if_neg htq,hbw'];unfold iW;rw [if_neg (by omega)];simp,
          by rw [hRS j' hj' hj'ne1 hj'ne2,hrol'],
          by rw [(hIF j' hj').1,hop'],?_⟩
         have hin_C:=hNTI j' hj' hj'notT
         simp only [d,if_neg htp,if_neg htq]
         rcases hin' with h | h
         . left;rw [hin_C,h];rfl
         . right;rw [hin_C,h];rfl
        have hz_t : IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t):=by
         rw [hGOO t ht2 Kind.z (by decide)]
         have hLeq : zLeaves d t=(zLeaves d' t).image (iW n j0 j1):=by
          ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,d]
          constructor
          . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
            . exact ⟨t.val,Or.inl rfl,by unfold iW;rw [if_pos t.isLt]⟩
            . by_cases haq : a=q
              . rw [if_pos haq] at htie;exact absurd (Option.some.inj htie) htp.symm
              . rw [if_neg haq] at htie
                by_cases hap : a=p
                . rw [if_pos hap] at htie;cases htie
                . rw [if_neg hap] at htie
                  have ha' : a ∈ d'.cover:=(hvD.2.2.2.1 a t htie).1
                  exact ⟨d'.bw a,Or.inr ⟨a,⟨ha',htie⟩,rfl⟩,by simp [hap,haq]⟩
          . rintro ⟨w',hw',rfl⟩
            rcases hw' with rfl | ⟨a,⟨ha',htie⟩,rfl⟩
            . left;unfold iW;rw [if_pos t.isLt]
            . right
              have hap : a≠p:=fun h => hpNC (h ▸ ha')
              have haq : a≠q:=fun h => hqNC (h ▸ ha')
              have has : a≠s0:=fun h => by rw [h,hties0] at htie;cases htie
              exact ⟨a,⟨mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨has,ha'⟩)),
               by simp [haq,hap,htie]⟩,by simp [hap,haq]⟩
         rw [hLeq];simp only [d,if_neg htp,if_neg htq]
         exact otLI (hvD.2.2.2.2.2.1 t ht').2.1 (iI j0 j1) (iW n j0 j1)
          (fun _ _ _ _ h => invIdx_inj hj01 h)
          (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
          (fun a b _ _ h => invWire_inj hj01 h)
          (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
          (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
           have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
           rw [h1] at h2;cases h2))
        have ho_t : IsOrTree n C (gatesOf d C Kind.o t.val) (oLeaves d t) (d.oroot t):=by
         rw [hGOO t ht2 Kind.o (by decide)]
         have hLeq : oLeaves d t=(oLeaves d' t).image (iW n j0 j1):=by
          ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
           d,htp,htq,hts,false_and,↓reduceIte]
          constructor
          . rintro ⟨r,hr,rfl⟩;exact ⟨d'.lam t r,⟨r,hr,rfl⟩,rfl⟩
          . rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩;exact ⟨r,hr,rfl⟩
         rw [hLeq];simp only [d,if_neg htp,if_neg htq]
         exact otLI (hvD.2.2.2.2.2.1 t ht').2.2.1 (iI j0 j1) (iW n j0 j1)
          (fun _ _ _ _ h => invIdx_inj hj01 h)
          (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
          (fun a b _ _ h => invWire_inj hj01 h)
          (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
          (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
           have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
           rw [h1] at h2;cases h2))
        have hlam_t : ∀ r,d.owns t r=true->LamOK n C d t r:=by
         intro r hown;simp only [d,htp,htq,hts,false_and,↓reduceIte] at hown
         have hrp : r≠p:=((hK2 t r).mp (hvD.2.2.1.1 t r hown).1).2.2.2.2
         have hl':=(hvD.2.2.2.2.2.1 t ht').2.2.2 r hown
         unfold LamOK at hl' ⊢
         by_cases hrq : r=q
         . subst hrq
           rw [if_neg hqNC] at hl'
           have hr_c : r ∈ d.cover:=mem_insert_of_mem (mem_insert_self _ _)
           rw [if_pos hr_c]
           have hLE : d.lam t r=r.val:=by simp only [d,if_neg htp,if_neg htq,hl'];unfold iW;rw [if_pos r.isLt]
           rw [hLE]
           exact ⟨(isCentred_input n C d r).mpr hr_c,Or.inl rfl,fun h => by simp [d] at h;exact absurd h htp.symm⟩
         . by_cases hrs : r=s0
           . subst hrs
             rw [if_pos hs0] at hl'
             have hs_nc : r ∉ d.cover:=by
              simp only [d,covNew,mem_insert,mem_erase,not_or]
              exact ⟨hs0_ne_p,hs0q,fun h => h.1 rfl⟩
             rw [if_neg hs_nc]
             have hlam_s0 : d'.lam t r=r.val:=by
              rcases hl'.2.1 with h1 | ⟨k,hk,_,h2⟩
              . exact h1
              . exfalso;have hmem : k ∈ gatesOf d' D Kind.z r.val:=mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
                rw [hz_s0_empty] at hmem;simp at hmem
             simp only [d,if_neg htp,if_neg htq,hlam_s0];unfold iW;rw [if_pos r.isLt]
           . have hRCI : r ∈ d.cover↔r ∈ d'.cover:=by simp [d,covNew,hrp,hrq,hrs]
             by_cases hrc : r ∈ d'.cover
             . rw [if_pos hrc] at hl';rw [if_pos (hRCI.mpr hrc)]
               have hRZ:=(icZIR hvD hrc hl'.2.1).mp hl'.1
               have hRC:=orLI
                (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
                (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
                 have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
                 rw [h1] at h2;cases h2)) hRZ
               have hinv_r : iW n j0 j1 r.val=r.val:=by unfold iW;rw [if_pos r.isLt]
               rw [hinv_r] at hRC
               refine ⟨?_,?_,?_⟩
               . simp only [d,if_neg htp,if_neg htq]
                 exact icORZ hrbC (hRCI.mpr hrc) (fun j hj => by
                  obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
                  have hj'lt:=gatesOf_lt j' hj'
                  have hj'ne1 : j'≠jv':=fun h => by
                   rw [h] at hj';have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hjv'T).2
                   rw [h1] at h2;cases h2
                  have hj'ne2 : j'≠jb':=fun h => by
                   rw [h] at hj';have h1:=(mem_filter.mp hj').2;rw [hrol_s0] at h1;cases h1
                  exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
                   by rw [hRS j' hj'lt hj'ne1 hj'ne2,(mem_filter.mp hj').2]⟩) hRC
               . have hlam_d : d.lam t r=iW n j0 j1 (d'.lam t r):=by simp [d,htp,htq]
                 rw [hlam_d]
                 rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
                 . left;rw [h1,hinv_r]
                 . right
                   have hkne1 : k≠jv':=fun h => by
                    rw [h] at h2;have h3:=(mem_filter.mp hjv'T).2;rw [h2] at h3;cases h3
                   have hkne2 : k≠jb':=fun h => by
                    rw [h] at h2;rw [hrol_s0] at h2;cases h2
                   exact ⟨iI j0 j1 k,invIdx_lt hj01 hj1 (by omega : k+2 < C.gates.length),
                    by rw [h1];unfold iW;rw [if_neg (by omega)];simp,
                    by rw [hRS k hk hkne1 hkne2,h2]⟩
               . intro htie;simp only [d,if_neg hrq,if_neg hrp] at htie
                 simp only [d,if_neg htp,if_neg htq,if_neg hrp,if_neg hrq,hl'.2.2 htie]
             . rw [if_neg hrc] at hl';rw [if_neg (fun h => hrc (hRCI.mp h))]
               simp only [d,if_neg htp,if_neg htq,hl'];unfold iW;rw [if_pos r.isLt]
        exact ⟨hterm_t,hz_t,ho_t,hlam_t⟩
    ·
     have hTGs : topGates d C=((topGates d' D).erase jv').image (iI j0 j1):=by
      ext j;simp only [topGates,mem_filter,mem_range,mem_image,mem_erase]
      constructor
      . rintro ⟨hj,hr⟩
        have h0 : j≠j0:=fun h => by rw [h] at hr;simp [d] at hr
        have h1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),↓reduceIte] at hr;cases hr
        have hv_j : j≠iI j0 j1 jv':=fun h => by rw [h] at hr;simp [d,hjv_C_ne.1,hjv_C_ne.2] at hr
        have hb_j : j≠iI j0 j1 jb':=fun h => by rw [h] at hr;simp [d,hjb_C_ne.1,hjb_C_ne.2,hjb_C_ne_jv] at hr
        simp only [d,if_neg h0,if_neg h1,if_neg hv_j,if_neg hb_j] at hr
        have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
        have hidx_ne : iM j0 j1 j≠jv':=fun h => hv_j (by rw [← h,invIdx_idxMap hj01 h0 h1])
        exact ⟨iM j0 j1 j,⟨hidx_ne,hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
      . rintro ⟨j',⟨hne_jv,hj'lt,hr'⟩,rfl⟩
        have hne_jb : j'≠jb':=fun h => by rw [h] at hr';rw [hrol_s0] at hr';cases hr'
        exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
         by rw [hRS j' hj'lt hne_jv hne_jb,hr']⟩
     have hTLs : topLeaves d A =
      insert (n+j1) ((((topLeaves d' (insert p A)).erase p.val).erase (d'.bw s0)).image (iW n j0 j1)):=by
      ext x;simp only [topLeaves,mem_union,mem_image,mem_filter,
       mem_insert,mem_erase,d,covNew]
      constructor
      . rintro (⟨a,haA,rfl⟩ | ⟨t,⟨htc,htie⟩,rfl⟩)
        . right
          have hap : a≠p:=fun h => hpA (h ▸ haA)
          have hne_bw : a.val≠d'.bw s0:=by rw [hbw_s0];have:=a.isLt;omega
          exact ⟨a.val,⟨hne_bw,fun h => hap (Fin.ext h),Or.inl ⟨a,Or.inr haA,rfl⟩⟩,
           by unfold iW;rw [if_pos a.isLt]⟩
        . by_cases htp : t=p
          . subst t;left;simp
          . right
            by_cases htq : t=q
            . rw [if_pos htq] at htie;cases htie
            . rw [if_neg htq,if_neg htp] at htie
              rw [if_neg htp,if_neg htq]
              have ht' : t ∈ d'.cover/\t≠s0:=by
               rcases htc with rfl | rfl | ⟨hts,ht'⟩
               . exact absurd rfl htp
               . exact absurd rfl htq
               . exact ⟨ht',hts⟩
              have hne_bw : d'.bw t≠d'.bw s0:=fun h => ht'.2 (bw_injOn hvD d'.cover (Finset.Subset.refl _) ht'.1 hs0 h)
              have hne_p : d'.bw t≠p.val:=by
               obtain ⟨jt,_,hbw,_⟩:=bwS hvD t ht'.1;have:=p.isLt;omega
              exact ⟨d'.bw t,⟨hne_bw,hne_p,Or.inr ⟨t,⟨ht'.1,htie⟩,rfl⟩⟩,rfl⟩
      . rintro (rfl | ⟨w',⟨hne_s,hne_p,hw'⟩,rfl⟩)
        . right;exact ⟨p,⟨Or.inl rfl,by simp [hpq]⟩,by simp⟩
        . rcases hw' with ⟨a,ha,rfl⟩ | ⟨t,⟨ht',htie⟩,rfl⟩
          . rcases ha with rfl | haA
            . exact absurd rfl hne_p
            . left;exact ⟨a,haA,by unfold iW;rw [if_pos a.isLt]⟩
          . right
            have htp : t≠p:=fun h => hpNC (h ▸ ht')
            have htq : t≠q:=fun h => hqNC (h ▸ ht')
            have hts : t≠s0:=fun h => hne_s (by rw [h])
            exact ⟨t,⟨Or.inr (Or.inr ⟨hts,ht'⟩),by simp [htq,htp,htie]⟩,by simp [htp,htq]⟩
     have hCE : C.output=if D.output=n+jv' then n+j1 else iW n j0 j1 D.output:=by
      rw [← hv'_eq_jv]
      by_cases h : D.output=v'
      . rw [if_pos h];exact hTSC.1 h.symm
      . rw [if_neg h]
        have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
        have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
        rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
        . exact absurd hveq h
        . exact heq
     rw [hTGs,hTLs,hCE]
     exact otLR hvD.1 topGates_lt hvD.2.2.2.2.2.2 hjv'T hp_mem_top hw0'L
      (Ne.symm hne0) hjv'_in (iI j0 j1) (iW n j0 j1)
      (fun _ _ _ _ h => invIdx_inj hj01 h)
      (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
      (fun a b _ _ h => invWire_inj hj01 h)
      (fun a _ => (invWire_ne_j0_j1 (w':=a) hj01).2)
      (fun j' hj' => (hIF j' (topGates_lt j' (Finset.mem_of_mem_erase hj'))).1)
      (fun j' hj' => by rw [← hv'_eq_jv];exact hTSC.2 j' (Finset.mem_of_mem_erase hj'))
 ·
  push Not at hother
  have hv'_eq_p : v'=p.val :=
   otELSS hvD.1 topGates_lt hvD.2.2.2.2.2.2 hvTp hother
  have hv_eq_p : v=p.val:=by rw [hv_eq,hv'_eq_p];unfold iW;rw [if_pos p.isLt]
  let d : NCCData n:={
   cover:=insert p d'.cover
   owns:=fun a b => if a=p/\(b=l\/b=q) then true else d'.owns a b
   tie:=fun a => if a=p then none else d'.tie a
   role:=fun j =>
    if j=j0 then (Kind.o,p.val)
    else if j=j1 then (Kind.b,p.val)
    else d'.role (iM j0 j1 j)
   bw:=fun a => if a=p then n+j1 else iW n j0 j1 (d'.bw a)
   zroot:=fun a => if a=p then p.val else iW n j0 j1 (d'.zroot a)
   oroot:=fun a => if a=p then n+j0 else iW n j0 j1 (d'.oroot a)
   lam:=fun a b => if a=p then (if b=l then l.val else u) else iW n j0 j1 (d'.lam a b)
  }
  have hRS : ∀ j' < D.gates.length,d.role (iI j0 j1 j')=d'.role j':=by
   intro j' _
   have hne:=invIdx_ne (j':=j') hj01
   simp only [d,if_neg hne.1,if_neg hne.2,idxMap_invIdx hj01]
  have hGOO : ∀ t ∈ d'.cover,∀ k : Kind,
   gatesOf d C k t.val=(gatesOf d' D k t.val).image (iI j0 j1):=by
   intro t ht k
   have htp : t≠p:=fun h => hpNC (h ▸ ht)
   ext j;simp only [gatesOf,mem_filter,mem_range,mem_image]
   constructor
   . rintro ⟨hj,hr⟩
     have h0 : j≠j0:=fun h => by rw [h] at hr;simp only [d,if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
     have h1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),if_pos rfl] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
     have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
     simp only [d,if_neg h0,if_neg h1] at hr
     exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
   . rintro ⟨j',⟨hj',hr'⟩,rfl⟩
     exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj',hr']⟩
  refine ⟨d,hrbC,hMCP,?_,?_,?_,?_,?_⟩
  ·
   refine ⟨?_,?_⟩
   . intro a b hown;simp only [d] at hown
     split_ifs at hown with h
     . rcases h with ⟨rfl,rfl | rfl⟩
       . exact ⟨hLPA.symm,mem_insert_self _ _⟩
       . exact ⟨hPQA,mem_insert_self _ _⟩
     . have h2:=hvD.2.2.1.1 a b hown
       exact ⟨((hK2 a b).mp h2.1).1,mem_insert_of_mem h2.2⟩
   . intro a b hab;simp only [d]
     by_cases hap : a=p
     . subst a
       rcases (hp b).mp hab with hbl | hbq
       . subst b
         have hnot : d'.owns l p=false:=by
          cases h : d'.owns l p;rfl;exfalso;exact ((hK2 l p).mp (hvD.2.2.1.1 l p h).1).2.1 rfl
         simp [hlp,hnot]
       . subst b
         have hnot : d'.owns q p=false:=by
          cases h : d'.owns q p;rfl;exfalso;exact ((hK2 q p).mp (hvD.2.2.1.1 q p h).1).2.2.2.2 rfl
         simp [hpq.symm,hnot]
     . by_cases hbp : b=p
       . subst b
         rcases (hp a).mp hab.symm with hal | haq
         . subst a
           have hnot : d'.owns l p=false:=by
            cases h : d'.owns l p;rfl;exfalso;exact ((hK2 l p).mp (hvD.2.2.1.1 l p h).1).2.1 rfl
           simp [hap,hnot]
         . subst a
           have hnot : d'.owns q p=false:=by
            cases h : d'.owns q p;rfl;exfalso;exact ((hK2 q p).mp (hvD.2.2.1.1 q p h).1).2.2.2.2 rfl
           simp [hap,hnot]
       . have hal : a≠l:=fun h => hbp ((hl b).mp (h ▸ hab))
         have hbl : b≠l:=fun h => hap ((hl a).mp (h ▸ hab.symm))
         simp only [hap,hbp,false_and,↓reduceIte]
         exact hvD.2.2.1.2 a b ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩)
  ·
   intro a b htie;simp only [d] at htie
   by_cases hap : a=p
   . rw [if_pos hap] at htie;cases htie
   . rw [if_neg hap] at htie
     have h2:=hvD.2.2.2.1 a b htie
     refine ⟨mem_insert_of_mem h2.1,?_⟩
     simp only [d];split_ifs;rfl;exact h2.2
  ·
   intro j hj
   by_cases h0 : j=j0
   . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d],fun h => by simp [d] at h⟩
   . by_cases h1 : j=j1
     . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d,h0],fun _ => by simp [d]⟩
     . have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
       have hrole_eq : d.role j=d'.role (iM j0 j1 j):=by simp [d,h0,h1]
       rw [hrole_eq]
       rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨t,ht,hrt,hrb⟩
       . exact Or.inl htop
       . right
         have htp : t≠p:=fun h => hpNC (h ▸ ht)
         refine ⟨t,mem_insert_of_mem ht,hrt,fun hb => ?_⟩
         simp only [d,if_neg htp];rw [hrb hb]
         unfold iW;rw [if_neg (by omega)]
         have : n+iM j0 j1 j - n=iM j0 j1 j:=by omega
         rw [this,invIdx_idxMap hj01 h0 h1]
  ·
   intro t ht
   rcases mem_insert.mp ht with htp | ht'
   . subst t
     have hz_gates_p : gatesOf d C Kind.z p.val=∅:=by
      ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
      intro hj hr
      by_cases h0 : j=j0
      . subst j;simp [d] at hr
      . by_cases h1 : j=j1
        . subst j;simp [d,h0] at hr
        . simp only [d,if_neg h0,if_neg h1] at hr
          have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
          rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
          . rw [hr] at htop;cases htop
          . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
     have hZLP : zLeaves d p={p.val}:=by
      ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton,d]
      constructor
      . rintro (rfl | ⟨a,⟨_,htie⟩,_⟩);rfl
        by_cases hap : a=p
        . rw [if_pos hap] at htie;cases htie
        . rw [if_neg hap] at htie;exact absurd (hvD.2.2.1.1 p a (hvD.2.2.2.1 a p htie).2).2 hpNC
      . rintro rfl;exact Or.inl rfl
     have ho_gates_p : gatesOf d C Kind.o p.val={j0}:=by
      ext j;simp only [gatesOf,mem_filter,mem_range,mem_singleton]
      constructor
      . rintro ⟨hj,hr⟩
        by_cases h0 : j=j0
        . exact h0
        . by_cases h1 : j=j1
          . subst j;simp [d,h0] at hr
          . simp only [d,if_neg h0,if_neg h1] at hr
            have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
            rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
            . rw [hr] at htop;cases htop
            . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
      . rintro rfl;exact ⟨by omega,by simp [d]⟩
     have hOLP : oLeaves d p={l.val,u}:=by
      ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
       mem_insert,mem_singleton,d]
      constructor
      . rintro ⟨r,hown,rfl⟩
        by_cases hrl : r=l
        . subst hrl;left;simp
        . by_cases hrq : r=q
          . subst hrq;right;simp [hql]
          . simp only [hrl,hrq,or_self,and_false,↓reduceIte] at hown
            exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
      . rintro (rfl | rfl)
        . exact ⟨l,by simp,by simp⟩
        . exact ⟨q,by simp,by simp [hql]⟩
     refine ⟨⟨j1,hj1,by simp [d],by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte],hop1,
      by simp only [d,↓reduceIte];rw [← hv_eq_p];rcases hvin with h | h;exact Or.inr h;exact Or.inl h⟩,
      ?_,?_,?_⟩
     . rw [hz_gates_p,hZLP];simp [IsOrTree,readsIn,d]
     . rw [ho_gates_p,hOLP];simp only [d,↓reduceIte]
       exact otSG hul.symm (by have:=l.isLt;omega) (by omega) hop0 huin
     . intro r hown;simp only [d] at hown
       by_cases hrl : r=l
       . subst r;unfold LamOK
         have hl_nc : l ∉ d.cover:=by simp only [d,mem_insert,not_or];exact ⟨hlp,hlNC⟩
         rw [if_neg hl_nc];simp [d]
       . by_cases hrq : r=q
         . subst r;unfold LamOK
           have hRCI : q ∈ d.cover↔q ∈ d'.cover:=by simp [d,hpq.symm]
           by_cases hrc : q ∈ d'.cover
           . rw [if_pos (hRCI.mpr hrc)]
             have hLE : d.lam p q=u:=by simp [d,hrl]
             rw [hLE]
             refine ⟨?_,?_,?_⟩
             . have hRZ : OrReach n D (gatesOf d' D Kind.z q.val) u' q.val:=by
                rcases huC with h1 | ⟨_,hc,j,hj,h1,hrole⟩
                . rw [h1];exact ReflTransGen.refl
                . exact (icZIR hvD hrc (Or.inr ⟨j,hj,h1,hrole⟩)).mp hc
               have hRC:=orLI
                (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
                (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
                 have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
                 rw [h1] at h2;cases h2)) hRZ
               rw [← hu_eq] at hRC
               have hinv_r : iW n j0 j1 q.val=q.val:=by unfold iW;rw [if_pos q.isLt]
               rw [hinv_r] at hRC
               exact icORZ hrbC (hRCI.mpr hrc) (fun j hj => by
                obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
                have hj'lt:=gatesOf_lt j' hj'
                exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
                 by rw [hRS j' hj'lt,(mem_filter.mp hj').2]⟩) hRC
             . rcases huC with h1 | ⟨_,_,j,hj,h1,hrole⟩
               . left;rw [hu_eq,h1];unfold iW;rw [if_pos q.isLt]
               . right;exact ⟨iI j0 j1 j,invIdx_lt hj01 hj1 (by omega : j+2 < C.gates.length),
                  by rw [hu_eq,h1];unfold iW;rw [if_neg (by omega)];simp,
                  by rw [hRS j hj,hrole]⟩
             . intro htie;simp only [d,if_neg hpq.symm] at htie
               exact absurd (hvD.2.2.1.1 p q (hvD.2.2.2.1 q p htie).2).2 hpNC
           . rw [if_neg (fun h => hrc (hRCI.mp h))]
             rcases huC with h1 | ⟨hq,_⟩
             . simp only [d,↓reduceIte,if_neg hrl,hu_eq,h1];unfold iW;rw [if_pos q.isLt]
             . exact absurd hq hrc
         . simp only [hrl,hrq,or_self,↓reduceIte] at hown
           exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
   ·
    have htp : t≠p:=fun h => hpNC (h ▸ ht')
    obtain ⟨j',hj',hbw',hrol',hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht').1
    have hj'notT : j' ∉ topGates d' D:=fun h => by
     have h2:=(mem_filter.mp h).2;rw [hrol'] at h2;cases h2
    have hterm_t : TermOK n C d t:=by
     refine ⟨iI j0 j1 j',invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
      by simp only [d,if_neg htp,hbw'];unfold iW;rw [if_neg (by omega)];simp,
      by rw [hRS j' hj',hrol'],
      by rw [(hIF j' hj').1,hop'],?_⟩
     have hin_C:=hNTI j' hj' hj'notT
     simp only [d,if_neg htp]
     rcases hin' with h | h
     . left;rw [hin_C,h];rfl
     . right;rw [hin_C,h];rfl
    have hz_t : IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t):=by
     rw [hGOO t ht' Kind.z]
     have hLeq : zLeaves d t=(zLeaves d' t).image (iW n j0 j1):=by
      ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,d]
      constructor
      . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
        . exact ⟨t.val,Or.inl rfl,by unfold iW;rw [if_pos t.isLt]⟩
        . by_cases hap : a=p
          . rw [if_pos hap] at htie;cases htie
          . rw [if_neg hap] at htie
            have ha' : a ∈ d'.cover:=by rcases ha with rfl | h;exact absurd rfl hap;exact h
            exact ⟨d'.bw a,Or.inr ⟨a,⟨ha',htie⟩,rfl⟩,by simp [hap]⟩
      . rintro ⟨w',hw',rfl⟩
        rcases hw' with rfl | ⟨a,⟨ha',htie⟩,rfl⟩
        . left;unfold iW;rw [if_pos t.isLt]
        . right;have hap : a≠p:=fun h => hpNC (h ▸ ha')
          exact ⟨a,⟨Or.inr ha',by simp [hap,htie]⟩,by simp [hap]⟩
     rw [hLeq];simp only [d,if_neg htp]
     exact otLI (hvD.2.2.2.2.2.1 t ht').2.1 (iI j0 j1) (iW n j0 j1)
      (fun _ _ _ _ h => invIdx_inj hj01 h)
      (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
      (fun a b _ _ h => invWire_inj hj01 h)
      (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
      (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
       have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
       rw [h1] at h2;cases h2))
    have ho_t : IsOrTree n C (gatesOf d C Kind.o t.val) (oLeaves d t) (d.oroot t):=by
     rw [hGOO t ht' Kind.o]
     have hLeq : oLeaves d t=(oLeaves d' t).image (iW n j0 j1):=by
      ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
       d,htp,false_and,↓reduceIte]
      constructor
      . rintro ⟨r,hr,rfl⟩;exact ⟨d'.lam t r,⟨r,hr,rfl⟩,rfl⟩
      . rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩;exact ⟨r,hr,rfl⟩
     rw [hLeq];simp only [d,if_neg htp]
     exact otLI (hvD.2.2.2.2.2.1 t ht').2.2.1 (iI j0 j1) (iW n j0 j1)
      (fun _ _ _ _ h => invIdx_inj hj01 h)
      (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
      (fun a b _ _ h => invWire_inj hj01 h)
      (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
      (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
       have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
       rw [h1] at h2;cases h2))
    have hlam_t : ∀ r,d.owns t r=true->LamOK n C d t r:=by
     intro r hown;simp only [d,htp,false_and,↓reduceIte] at hown
     have hrp : r≠p:=((hK2 t r).mp (hvD.2.2.1.1 t r hown).1).2.2.2.2
     have hl':=(hvD.2.2.2.2.2.1 t ht').2.2.2 r hown
     unfold LamOK at hl' ⊢
     have hRCI : r ∈ d.cover↔r ∈ d'.cover:=by simp [d,hrp]
     by_cases hrc : r ∈ d'.cover
     . rw [if_pos hrc] at hl';rw [if_pos (hRCI.mpr hrc)]
       have hRZ:=(icZIR hvD hrc hl'.2.1).mp hl'.1
       have hRC:=orLI
        (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
        (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
         have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
         rw [h1] at h2;cases h2)) hRZ
       have hinv_r : iW n j0 j1 r.val=r.val:=by unfold iW;rw [if_pos r.isLt]
       rw [hinv_r] at hRC
       refine ⟨?_,?_,?_⟩
       . simp only [d,if_neg htp]
         exact icORZ hrbC (hRCI.mpr hrc) (fun j hj => by
          obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
          have hj'lt:=gatesOf_lt j' hj'
          exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
           by rw [hRS j' hj'lt,(mem_filter.mp hj').2]⟩) hRC
       . have hlam_d : d.lam t r=iW n j0 j1 (d'.lam t r):=by simp [d,htp]
         rw [hlam_d]
         rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
         . left;rw [h1,hinv_r]
         . right;exact ⟨iI j0 j1 k,invIdx_lt hj01 hj1 (by omega : k+2 < C.gates.length),
            by rw [h1];unfold iW;rw [if_neg (by omega)];simp,
            by rw [hRS k hk,h2]⟩
       . intro htie;simp only [d,if_neg hrp] at htie
         simp only [d,if_neg htp,if_neg hrp,hl'.2.2 htie]
     . rw [if_neg hrc] at hl';rw [if_neg (fun h => hrc (hRCI.mp h))]
       simp only [d,if_neg htp,hl'];unfold iW;rw [if_pos r.isLt]
    exact ⟨hterm_t,hz_t,ho_t,hlam_t⟩
  ·
   let gMap (w' : ℕ) : ℕ:=if w'=p.val then n+j1 else iW n j0 j1 w'
   have hTGs : topGates d C=(topGates d' D).image (iI j0 j1):=by
    ext j;simp only [topGates,mem_filter,mem_range,mem_image]
    constructor
    . rintro ⟨hj,hr⟩
      have h0 : j≠j0:=fun h => by rw [h] at hr;simp [d] at hr
      have h1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),↓reduceIte] at hr;cases hr
      simp only [d,if_neg h0,if_neg h1] at hr
      have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
      exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
    . rintro ⟨j',⟨hj'lt,hr'⟩,rfl⟩
      exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj'lt,hr']⟩
   have hTLs : topLeaves d A=(topLeaves d' (insert p A)).image gMap:=by
    ext x;simp only [topLeaves,mem_union,mem_image,mem_filter,mem_insert,d]
    constructor
    . rintro (⟨a,haA,rfl⟩ | ⟨t,⟨htc,htie⟩,rfl⟩)
      . have hap : a≠p:=fun h => hpA (h ▸ haA)
        exact ⟨a.val,Or.inl ⟨a,Or.inr haA,rfl⟩,
         by simp only [gMap,if_neg (fun h => hap (Fin.ext h))];unfold iW;rw [if_pos a.isLt]⟩
      . by_cases htp : t=p
        . subst t;exact ⟨p.val,Or.inl ⟨p,Or.inl rfl,rfl⟩,by simp [gMap]⟩
        . rw [if_neg htp] at htie
          have ht' : t ∈ d'.cover:=by rcases htc with rfl | h;exact absurd rfl htp;exact h
          have hne_p : d'.bw t≠p.val:=by obtain ⟨jt,_,hbw,_⟩:=bwS hvD t ht';have:=p.isLt;omega
          exact ⟨d'.bw t,Or.inr ⟨t,⟨ht',htie⟩,rfl⟩,by simp [gMap,htp,hne_p]⟩
    . rintro ⟨w',hw',rfl⟩
      rcases hw' with ⟨a,rfl | haA,rfl⟩ | ⟨t,⟨ht',htie⟩,rfl⟩
      . right;exact ⟨a,⟨Or.inl rfl,by simp⟩,by simp [gMap]⟩
      . have hap : a≠p:=fun h => hpA (h ▸ haA)
        left;exact ⟨a,haA,by simp only [gMap,if_neg (fun h => hap (Fin.ext h))];unfold iW;rw [if_pos a.isLt]⟩
      . have htp : t≠p:=fun h => hpNC (h ▸ ht')
        have hne_p : d'.bw t≠p.val:=by obtain ⟨jt,_,hbw,_⟩:=bwS hvD t ht';have:=p.isLt;omega
        right;exact ⟨t,⟨Or.inr ht',by simp [htp,htie]⟩,by simp [gMap,htp,hne_p]⟩
   have hCE : C.output=gMap D.output:=by
    unfold gMap;rw [← hv'_eq_p]
    by_cases h : D.output=v'
    . rw [if_pos h];exact hTSC.1 h.symm
    . rw [if_neg h]
      have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
      have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
      rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
      . exact absurd hveq h
      . exact heq
   rw [hTGs,hTLs,hCE]
   exact otLI hvD.2.2.2.2.2.2 (iI j0 j1) gMap
    (fun _ _ _ _ h => invIdx_inj hj01 h)
    (fun j' _ => by
     have hne : n+j'≠p.val:=by have:=p.isLt;omega
     simp only [gMap,if_neg hne];unfold iW;rw [if_neg (by omega)];simp)
    (fun a b _ _ heq => by
     unfold gMap at heq
     by_cases ha : a=p.val <;> by_cases hb : b=p.val
     . exact ha.trans hb.symm
     . rw [if_pos ha,if_neg hb] at heq;exact absurd heq.symm (invWire_ne_j0_j1 (w':=b) hj01).2
     . rw [if_neg ha,if_pos hb] at heq;exact absurd heq (invWire_ne_j0_j1 (w':=a) hj01).2
     . rw [if_neg ha,if_neg hb] at heq;exact invWire_inj hj01 heq)
    (fun j' hj' => (hIF j' (topGates_lt j' hj')).1)
    (fun j' hj' => by unfold gMap;rw [← hv'_eq_p];exact hTSC.2 j' hj')
lemma sInD {n j0 j1 v' : ℕ} {C D : Circuit}
 (hj01 : j0 < j1) {j' : ℕ}
 (hinD : (gateAt D j').inputs=(gateAt C (iI j0 j1 j')).inputs.map (wM n j0 j1 v'))
 (hsub : ∀ i ∈ (gateAt C (iI j0 j1 j')).inputs,i≠n+j0)
 {a' b' : ℕ} (hpair : (gateAt D j').inputs=[a',b']) (hab' : a'≠b') :
 (n+j1 ∈ (gateAt C (iI j0 j1 j')).inputs →
  (gateAt C (iI j0 j1 j')).inputs =
   (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w')) ∧
 (n+j1 ∉ (gateAt C (iI j0 j1 j')).inputs →
  (gateAt C (iI j0 j1 j')).inputs=(gateAt D j').inputs.map (iW n j0 j1)):=by
 constructor
 . intro hmem_j1
   have hlenC : (gateAt C (iI j0 j1 j')).inputs.length=2:=by
    have:=congrArg List.length hinD;simp [hpair] at this;exact this.symm
   cases hinC : (gateAt C (iI j0 j1 j')).inputs with
   | nil => simp [hinC] at hlenC
   | cons x1 rest =>
    cases rest with
    | nil => simp [hinC] at hlenC
    | cons x2 rest2 =>
     cases rest2 with
     | nil =>
      rw [hinC,hpair] at hinD
      simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at hinD
      obtain ⟨hx1,hx2⟩:=hinD
      rw [hinC] at hmem_j1;simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem_j1
      have hx10:=hsub x1 (by simp [hinC])
      have hx20:=hsub x2 (by simp [hinC])
      rw [hpair]
      rcases hmem_j1 with rfl | rfl
      . have ha'_eq : a'=v':=by rw [hx1];unfold wM;rw [if_neg (by omega),if_pos rfl]
        have hb'_ne : b'≠v':=fun h => hab' (ha'_eq.trans h.symm)
        have hx2_eq : x2=iW n j0 j1 b':=by
         rcases (wMEq hj01 hx20).mp hx2.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
         . exact absurd hveq hb'_ne
         . exact heq
        simp [ha'_eq,hb'_ne,hx2_eq]
      . have hb'_eq : b'=v':=by rw [hx2];unfold wM;rw [if_neg (by omega),if_pos rfl]
        have ha'_ne : a'≠v':=fun h => hab' (h.trans hb'_eq.symm)
        have hx1_eq : x1=iW n j0 j1 a':=by
         rcases (wMEq hj01 hx10).mp hx1.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
         . exact absurd hveq ha'_ne
         . exact heq
        simp [ha'_ne,hb'_eq,hx1_eq]
     | cons _ _ => simp [hinC] at hlenC
 . intro hno_j1
   rw [hinD,List.map_map];symm
   rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
   have hi0:=hsub i hi
   have hi1 : i≠n+j1:=fun h => hno_j1 (h ▸ hi)
   rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨habs,_⟩ | ⟨_,heq⟩
   . exact absurd habs hi1
   . exact heq.symm
lemma znDN {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
 {A : Finset (Fin n)} {D : Circuit} {d : NCCData n} (hvD : Valid n K A D d)
 {r s : Fin n} (hrs : r≠s) {w : ℕ}
 (hr : w ∈ zLeaves d r\/(n<=w/\w - n ∈ gatesOf d D Kind.z r.val))
 (hs : w ∈ zLeaves d s\/(n<=w/\w - n ∈ gatesOf d D Kind.z s.val)) : False:=by
 rcases hr with hrL | ⟨hwn,hrG⟩
 . rcases hs with hsL | ⟨hwn,hsG⟩
   . unfold zLeaves at hrL hsL
     rcases mem_insert.mp hrL with rfl | himgR
     . rcases mem_insert.mp hsL with h1 | himgS
       . exact hrs (Fin.ext h1)
       . obtain ⟨a,ha,hbw⟩:=mem_image.mp himgS
         obtain ⟨ja,_,hbw',_⟩:=bwS hvD a (mem_filter.mp ha).1
         have:=r.isLt;omega
     . obtain ⟨a,ha,rfl⟩:=mem_image.mp himgR
       rcases mem_insert.mp hsL with h1 | himgS
       . obtain ⟨ja,_,hbw',_⟩:=bwS hvD a (mem_filter.mp ha).1
         have:=s.isLt;omega
       . obtain ⟨b,hb,hbw⟩:=mem_image.mp himgS
         have hab : a=b:=bw_injOn hvD d.cover (Finset.Subset.refl _)
          (mem_filter.mp ha).1 (mem_filter.mp hb).1 hbw.symm
         have h1:=(mem_filter.mp ha).2
         have h2:=(mem_filter.mp hb).2
         rw [hab,h2] at h1;exact hrs (Option.some.inj h1).symm
   . unfold zLeaves at hrL
     rcases mem_insert.mp hrL with rfl | himgR
     . have:=r.isLt;omega
     . obtain ⟨a,ha,rfl⟩:=mem_image.mp himgR
       obtain ⟨ja,_,hbw',hrol⟩:=bwS hvD a (mem_filter.mp ha).1
       have h1:=(mem_filter.mp hsG).2
       have : d.bw a - n=ja:=by omega
       rw [this,hrol] at h1;cases h1
 . rcases hs with hsL | ⟨_,hsG⟩
   . unfold zLeaves at hsL
     rcases mem_insert.mp hsL with rfl | himgS
     . have:=s.isLt;omega
     . obtain ⟨a,ha,rfl⟩:=mem_image.mp himgS
       obtain ⟨ja,_,hbw',hrol⟩:=bwS hvD a (mem_filter.mp ha).1
       have h1:=(mem_filter.mp hrG).2
       have : d.bw a - n=ja:=by omega
       rw [this,hrol] at h1;cases h1
   . have h1:=(mem_filter.mp hrG).2
     have h2:=(mem_filter.mp hsG).2
     rw [h1] at h2;exact hrs (Fin.ext (Prod.ext_iff.mp h2).2)
lemma tnDZ {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
 {A : Finset (Fin n)} {D : Circuit} {d : NCCData n} (hvD : Valid n K A D d)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 {t : Fin n} (ht : t ∈ d.cover) {w : ℕ}
 (hT : w ∈ topLeaves d A\/(n<=w/\w - n ∈ topGates d D))
 (hZ : w ∈ zLeaves d t\/(n<=w/\w - n ∈ gatesOf d D Kind.z t.val)) : False:=by
 have htA : t ∉ A:=fun h => by
  obtain ⟨r,hown⟩:=ownHOE hvD ht
  exact hA t h r (hvD.2.2.1.1 t r hown).1
 rcases hT with hTL | ⟨hwn,hTG⟩
 . unfold topLeaves at hTL
   rcases mem_union.mp hTL with hA' | hB'
   . obtain ⟨a,haA,rfl⟩:=mem_image.mp hA'
     rcases hZ with hZL | ⟨hwn,_⟩
     . unfold zLeaves at hZL
       rcases mem_insert.mp hZL with h1 | himg
       . exact htA (Fin.ext h1.symm ▸ haA)
       . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
         obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hs).1
         have:=a.isLt;omega
     . have:=a.isLt;omega
   . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
     obtain ⟨js,_,hbw',hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
     rcases hZ with hZL | ⟨_,hZG⟩
     . unfold zLeaves at hZL
       rcases mem_insert.mp hZL with h1 | himg
       . have:=t.isLt;omega
       . obtain ⟨a,ha,hbw⟩:=mem_image.mp himg
         have hsa : s=a:=bw_injOn hvD d.cover (Finset.Subset.refl _)
          (mem_filter.mp hsF).1 (mem_filter.mp ha).1 hbw.symm
         have h1:=(mem_filter.mp hsF).2
         have h2:=(mem_filter.mp ha).2
         rw [hsa,h2] at h1;cases h1
     . have h1:=(mem_filter.mp hZG).2
       have : d.bw s - n=js:=by omega
       rw [this,hrol] at h1;cases h1
 . rcases hZ with hZL | ⟨_,hZG⟩
   . unfold zLeaves at hZL
     rcases mem_insert.mp hZL with rfl | himg
     . have:=t.isLt;omega
     . obtain ⟨a,ha,rfl⟩:=mem_image.mp himg
       obtain ⟨ja,_,hbw',hrol⟩:=bwS hvD a (mem_filter.mp ha).1
       have h1:=(mem_filter.mp hTG).2
       have : d.bw a - n=ja:=by omega
       rw [this,hrol] at h1;cases h1
   . have h1:=(mem_filter.mp hTG).2
     have h2:=(mem_filter.mp hZG).2
     rw [h2] at h1;cases h1
lemma zrNeOr {n : ℕ} {K : SimpleGraph (Fin n)} [DecidableRel K.Adj]
 {A : Finset (Fin n)} {D : Circuit} {d : NCCData n} (hvD : Valid n K A D d)
 {t : Fin n} (ht : t ∈ d.cover) : d.zroot t≠d.oroot t:=by
 intro heq
 have hznode : d.zroot t ∈ zLeaves d t\/(n<=d.zroot t/\d.zroot t - n ∈ gatesOf d D Kind.z t.val):=by
  have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
  by_cases hGe : gatesOf d D Kind.z t.val=∅
  . rw [if_pos hGe] at hz;left;rw [hz];simp
  . rw [if_neg hGe] at hz;obtain ⟨k,hk,hkeq⟩:=hz;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
 have honode : d.oroot t ∈ oLeaves d t\/(n<=d.oroot t/\d.oroot t - n ∈ gatesOf d D Kind.o t.val):=by
  have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
  by_cases hGe : gatesOf d D Kind.o t.val=∅
  . rw [if_pos hGe] at ho;left;rw [ho];simp
  . rw [if_neg hGe] at ho;obtain ⟨k,hk,hkeq⟩:=ho;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
 rw [← heq] at honode
 rcases honode with hoL | ⟨_,hoG⟩
 . obtain ⟨r,hr,hLE⟩:=mem_image.mp hoL
   have hown:=(mem_filter.mp hr).2
   have hrt : r≠t:=(hvD.2.2.1.1 t r hown).1.ne.symm
   have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
   unfold LamOK at hlam
   by_cases hrc : r ∈ d.cover
   . rw [if_pos hrc] at hlam
     have hzr : d.zroot t ∈ zLeaves d r\/(n<=d.zroot t/\d.zroot t - n ∈ gatesOf d D Kind.z r.val):=by
      rw [← hLE]
      rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
      . left;rw [h1];exact mem_insert_self _ _
      . right;refine ⟨by omega,?_⟩
        have : d.lam t r - n=k:=by omega
        rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
     exact znDN hvD hrt hzr hznode
   . rw [if_neg hrc] at hlam
     rw [← hLE,hlam] at hznode
     rcases hznode with hzL | ⟨hwn,_⟩
     . unfold zLeaves at hzL
       rcases mem_insert.mp hzL with h1 | himg
       . exact hrt (Fin.ext h1)
       . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
         obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hs).1
         have:=r.isLt;omega
     . have:=r.isLt;omega
 . rcases hznode with hzL | ⟨_,hzG⟩
   . unfold zLeaves at hzL
     rcases mem_insert.mp hzL with h1 | himg
     . rw [h1] at hoG;have:=(mem_filter.mp hoG).1;have:=t.isLt;omega
     . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
       obtain ⟨js,_,hbw',hrol⟩:=bwS hvD s (mem_filter.mp hs).1
       have h1:=(mem_filter.mp hoG).2
       have : d.zroot t - n=js:=by omega
       rw [this,hrol] at h1;cases h1
   . have h1:=(mem_filter.mp hzG).2
     have h2:=(mem_filter.mp hoG).2
     rw [h1] at h2;cases h2
lemma fwd2cA {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {C D : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A)
 (hrbC : ReadsBack n C) (hncC : ∃ x y,circuitFun n C x≠circuitFun n C y)
 {j0 j1 u v u' v' : ℕ} (hj01 : j0 < j1) (hj1 : j1 < C.gates.length)
 (hop0 : (gateAt C j0).op=.and)
 (huin : (gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val])
 (hop1 : (gateAt C j1).op=.or)
 (hvin : (gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0])
 (hv_eq : v=iW n j0 j1 v') (hu_eq : u=iW n j0 j1 u')
 {d1 : NCCData n} (hvD : Valid n K1 A D d1)
 (hD_len : D.gates.length+2=C.gates.length)
 (hKF : ∀ j < C.gates.length,j≠j0->j≠j1 →
  (gateAt C j).op=(gateAt D (iM j0 j1 j)).op ∧
  (gateAt D (iM j0 j1 j)).inputs=(gateAt C j).inputs.map (wM n j0 j1 v') ∧
  ∀ i ∈ (gateAt C j).inputs,i < n+j/\i≠l.val/\i≠n+j0)
 (hIF : ∀ j' < D.gates.length,
  (gateAt C (iI j0 j1 j')).op=(gateAt D j').op ∧
  (gateAt D j').inputs=(gateAt C (iI j0 j1 j')).inputs.map (wM n j0 j1 v'))
 (hOE : D.output=wM n j0 j1 v' C.output)
 (hDout_lt : D.output < n+D.gates.length)
 (hpNC : p ∉ d1.cover) (hlNC : l ∉ d1.cover)
 (hMCP : IsMinCover K (insert p d1.cover))
 (hq_cov : q ∈ d1.cover)
 (hval_j1 : ∀ x : Fin n->Bool,wV n C x (n+j1)=((x l && wV n D x u') || wV n D x v'))
 (huC : u'=p.val\/(n<=u'/\u' - n ∈ gatesOf d1 D Kind.o q.val))
 (hvTp : v' ∈ topLeaves d1 A\/(n<=v'/\v' - n ∈ topGates d1 D)) :
 IsNestedCoverCircuit n K A C:=by
 obtain ⟨hlp,hpq,hlA,hpA,hqA,_,_,_⟩:=gArith K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 have hA1 : ∀ a ∈ A,∀ w : Fin n,¬ K1.Adj a w:=fun a ha w hw => hA a ha w ((hK1 a w).mp hw).1
 have hnonTop_no_v' : ∀ j' < D.gates.length,j' ∉ topGates d1 D->v' ∉ (gateAt D j').inputs:=by
  intro j' hj' hnotT hvmem
  have hNRT : (d1.role j').1≠Kind.top:=fun h => hnotT (mem_filter.mpr ⟨mem_range.mpr hj',h⟩)
  rcases hvD.2.2.2.2.1 j' hj' with htop | ⟨t,ht,hrt,hrb⟩
  . exact hNRT htop
  . cases hk : (d1.role j').1 with
    | top => exact hNRT hk
    | z =>
     have hjG : j' ∈ gatesOf d1 D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
     exact tnDZ hvD hA1 ht hvTp (((hvD.2.2.2.2.2.1 t ht).2.1.1 j' hjG).2.2 v' hvmem)
    | o =>
     have hjG : j' ∈ gatesOf d1 D Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
     rcases ((hvD.2.2.2.2.2.1 t ht).2.2.1.1 j' hjG).2.2 v' hvmem with hvL | ⟨_,hvG⟩
     . obtain ⟨r,hr,hLE⟩:=mem_image.mp hvL
       have hown:=(mem_filter.mp hr).2
       have hrA : r ∉ A:=fun h => hA1 r h t (hvD.2.2.1.1 t r hown).1.symm
       have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
       unfold LamOK at hlam
       by_cases hrc : r ∈ d1.cover
       . rw [if_pos hrc] at hlam
         have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
          rw [← hLE]
          rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
          . left;rw [h1];exact mem_insert_self _ _
          . right;refine ⟨by omega,?_⟩
            have : d1.lam t r - n=k:=by omega
            rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
         exact tnDZ hvD hA1 hrc hvTp hzr
       . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hvTp
         rcases hvTp with hTL | ⟨hwn,_⟩
         . unfold topLeaves at hTL;rcases mem_union.mp hTL with hA' | hB'
           . obtain ⟨a,haA,hae⟩:=mem_image.mp hA'
             exact hrA (Fin.ext hae ▸ haA)
           . obtain ⟨s,hsF,hbw⟩:=mem_image.mp hB'
             obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hsF).1
             have:=r.isLt;omega
         . have:=r.isLt;omega
     . rcases hvTp with hTL | ⟨_,hvT⟩
       . exact (hvD.2.2.2.2.2.2.2.1 v' hTL).1 (by
          have h1:=(mem_filter.mp hvG).2
          exfalso
          unfold topLeaves at hTL;rcases mem_union.mp hTL with hA' | hB'
          . obtain ⟨a,_,rfl⟩:=mem_image.mp hA';have:=a.isLt;omega
          . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
            obtain ⟨js,_,hbw',hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
            have : d1.bw s - n=js:=by omega
            rw [this,hrol] at h1;cases h1)
       . have h1:=(mem_filter.mp hvG).2;have h2:=(mem_filter.mp hvT).2
         rw [h1] at h2;cases h2
    | b =>
     obtain ⟨j'2,_,hbw2,_,_,hin2⟩:=(hvD.2.2.2.2.2.1 t ht).1
     have hbw:=hrb hk
     have hjj : j'=j'2:=by omega
     subst j'
     have hv_root : v'=d1.zroot t\/v'=d1.oroot t:=by
      rcases hin2 with h | h <;> rw [h] at hvmem <;>
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hvmem
      . exact hvmem
      . exact hvmem.symm
     rcases hv_root with hvz | hvo
     . have hznode : v' ∈ zLeaves d1 t\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z t.val):=by
        rw [hvz];have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
        by_cases hGe : gatesOf d1 D Kind.z t.val=∅
        . rw [if_pos hGe] at hz;left;rw [hz];simp
        . rw [if_neg hGe] at hz;obtain ⟨k,hk,hkeq⟩:=hz;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
       exact tnDZ hvD hA1 ht hvTp hznode
     . have honode : v' ∈ oLeaves d1 t\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.o t.val):=by
        rw [hvo];have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
        by_cases hGe : gatesOf d1 D Kind.o t.val=∅
        . rw [if_pos hGe] at ho;left;rw [ho];simp
        . rw [if_neg hGe] at ho;obtain ⟨k,hk,hkeq⟩:=ho;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
       rcases honode with hoL | ⟨_,hoG⟩
       . obtain ⟨r,hr,hLE⟩:=mem_image.mp hoL
         have hown:=(mem_filter.mp hr).2
         have hrA : r ∉ A:=fun h => hA1 r h t (hvD.2.2.1.1 t r hown).1.symm
         have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
         unfold LamOK at hlam
         by_cases hrc : r ∈ d1.cover
         . rw [if_pos hrc] at hlam
           have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
            rw [← hLE]
            rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
            . left;rw [h1];exact mem_insert_self _ _
            . right;refine ⟨by omega,?_⟩
              have : d1.lam t r - n=k:=by omega
              rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
           exact tnDZ hvD hA1 hrc hvTp hzr
         . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hvTp
           rcases hvTp with hTL | ⟨hwn,_⟩
           . unfold topLeaves at hTL;rcases mem_union.mp hTL with hA' | hB'
             . obtain ⟨a,haA,hae⟩:=mem_image.mp hA';exact hrA (Fin.ext hae ▸ haA)
             . obtain ⟨s,hsF,hbw⟩:=mem_image.mp hB'
               obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hsF).1
               have:=r.isLt;omega
           . have:=r.isLt;omega
       . rcases hvTp with hTL | ⟨_,hvT⟩
         . unfold topLeaves at hTL;rcases mem_union.mp hTL with hA' | hB'
           . obtain ⟨a,_,rfl⟩:=mem_image.mp hA';have:=a.isLt;omega
           . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
             obtain ⟨js,_,hbw',hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
             have h1:=(mem_filter.mp hoG).2
             have : d1.bw s - n=js:=by omega
             rw [this,hrol] at h1;cases h1
         . have h1:=(mem_filter.mp hoG).2;have h2:=(mem_filter.mp hvT).2
           rw [h1] at h2;cases h2
 have hNTI : ∀ j' < D.gates.length,j' ∉ topGates d1 D →
  (gateAt C (iI j0 j1 j')).inputs=(gateAt D j').inputs.map (iW n j0 j1):=by
  intro j' hj' hnotT
  have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
  have hne:=invIdx_ne (j':=j') hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  have hno:=hnonTop_no_v' j' hj' hnotT
  rw [hinD,List.map_map];symm
  rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
  have hi0:=(hsub i hi).2.2
  have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hno (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
  rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
  . exact absurd hveq hwm_ne
  . exact heq.symm
 have hval_nonTop : ∀ (x : Fin n->Bool) (w' : ℕ),w' < n+D.gates.length →
  (¬ (n<=w'/\w' - n ∈ topGates d1 D))->w'≠l.val →
  wV n C x (iW n j0 j1 w')=wV n D x w':=by
  intro x w'
  induction w' using Nat.strong_induction_on with
  | ind w' ih =>
   intro hw'lt hnotT hw'l
   by_cases hwn : w' < n
   . let wf : Fin n:=⟨w',hwn⟩
     unfold iW;rw [if_pos hwn]
     change wV n C x wf.val=wV n D x wf.val
     rw [wvI,wvI]
   . have hj' : w' - n < D.gates.length:=by omega
     have hweq : n+(w' - n)=w':=by omega
     have hnotT' : w' - n ∉ topGates d1 D:=fun h => hnotT ⟨by omega,h⟩
     have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
     have hne:=invIdx_ne (j':=w' - n) hj01
     unfold iW;rw [if_neg hwn]
     conv_rhs => rw [← hweq]
     rw [wvGR n C hrbC x (iI j0 j1 (w' - n)) hlt,
      wvGR n D hvD.1 x (w' - n) hj',
      (hIF (w' - n) hj').1,hNTI (w' - n) hj' hnotT',List.map_map]
     congr 1;refine List.map_congr_left fun i' hi' => ?_
     have hilt : i' < n+(w' - n):=hvD.1 (w' - n) hj' i' hi'
     have hi'l : i'≠l.val:=by
      have hmem_C : iW n j0 j1 i' ∈ (gateAt C (iI j0 j1 (w' - n))).inputs:=by
       rw [hNTI (w' - n) hj' hnotT'];exact List.mem_map.mpr ⟨i',hi',rfl⟩
      have h1:=((hKF (iI j0 j1 (w' - n)) hlt hne.1 hne.2).2.2 _ hmem_C).2.1
      intro heq;subst heq;unfold iW at h1;rw [if_pos l.isLt] at h1;exact h1 rfl
     have hi'notT : ¬ (n<=i'/\i' - n ∈ topGates d1 D):=by
      intro ⟨hin,hiT⟩
      have hNRT : (d1.role (w' - n)).1≠Kind.top :=
       fun h => hnotT' (mem_filter.mpr ⟨mem_range.mpr hj',h⟩)
      have hi'eq : n+(i' - n)=i':=by omega
      have hMR : (d1.role (i' - n)).1=Kind.top:=(mem_filter.mp hiT).2
      have htop_i : i' ∈ topLeaves d1 A\/(n<=i'/\i' - n ∈ topGates d1 D):=Or.inr ⟨hin,hiT⟩
      rcases hvD.2.2.2.2.1 (w' - n) hj' with htop | ⟨t,ht,hrt,hrb⟩
      . exact hNRT htop
      . cases hk : (d1.role (w' - n)).1 with
        | top => exact hNRT hk
        | z =>
         have hkG : w' - n ∈ gatesOf d1 D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
         exact tnDZ hvD hA1 ht htop_i (((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hkG).2.2 i' hi')
        | o =>
         have hkG : w' - n ∈ gatesOf d1 D Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
         rcases ((hvD.2.2.2.2.2.1 t ht).2.2.1.1 (w' - n) hkG).2.2 i' hi' with hL | ⟨_,hG⟩
         . obtain ⟨r,hr,hLE⟩:=mem_image.mp hL
           have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r (mem_filter.mp hr).2
           unfold LamOK at hlam
           by_cases hrc : r ∈ d1.cover
           . rw [if_pos hrc] at hlam
             rcases hlam.2.1 with h1 | ⟨km,_,h1,h2⟩
             . have:=r.isLt;omega
             . have : i' - n=km:=by omega
               rw [this,h2] at hMR;cases hMR
           . rw [if_neg hrc] at hlam;have:=r.isLt;omega
         . have h1:=(mem_filter.mp hG).2;rw [h1] at hMR;cases hMR
        | b =>
         obtain ⟨k2,_,hbw2,_,_,hin2⟩:=(hvD.2.2.2.2.2.1 t ht).1
         have hbw:=hrb hk
         have hkk : w' - n=k2:=by omega
         rw [hkk] at hi'
         have hi_root : i'=d1.zroot t\/i'=d1.oroot t:=by
          rcases hin2 with h | h <;> rw [h] at hi' <;>
           simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
          . exact hi'
          . exact hi'.symm
         rcases hi_root with hiz | hio
         . have hznode : i' ∈ zLeaves d1 t\/(n<=i'/\i' - n ∈ gatesOf d1 D Kind.z t.val):=by
            rw [hiz];have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
            by_cases hGe : gatesOf d1 D Kind.z t.val=∅
            . rw [if_pos hGe] at hz;left;rw [hz];simp
            . rw [if_neg hGe] at hz;obtain ⟨km,hkm,hkeq⟩:=hz;right;exact ⟨by omega,by simpa [hkeq] using hkm⟩
           exact tnDZ hvD hA1 ht htop_i hznode
         . have honode : i' ∈ oLeaves d1 t\/(n<=i'/\i' - n ∈ gatesOf d1 D Kind.o t.val):=by
            rw [hio];have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
            by_cases hGe : gatesOf d1 D Kind.o t.val=∅
            . rw [if_pos hGe] at ho;left;rw [ho];simp
            . rw [if_neg hGe] at ho;obtain ⟨km,hkm,hkeq⟩:=ho;right;exact ⟨by omega,by simpa [hkeq] using hkm⟩
           rcases honode with hL | ⟨_,hG⟩
           . obtain ⟨r,hr,hLE⟩:=mem_image.mp hL
             have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r (mem_filter.mp hr).2
             unfold LamOK at hlam
             by_cases hrc : r ∈ d1.cover
             . rw [if_pos hrc] at hlam
               rcases hlam.2.1 with h1 | ⟨km,_,h1,h2⟩
               . have:=r.isLt;omega
               . have : i' - n=km:=by omega
                 rw [this,h2] at hMR;cases hMR
             . rw [if_neg hrc] at hlam;have:=r.isLt;omega
           . have h1:=(mem_filter.mp hG).2;rw [h1] at hMR;cases hMR
     exact ih i' (by omega) (by omega) hi'notT hi'l
 let xlp : Fin n->Bool:=fun i => decide (i=l\/i=p)
 have hxlp_K : graphFun K A xlp=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨l,p,hLPA,by simp [xlp],by simp [xlp]⟩
 have hxlp_K1 : graphFun K1 A xlp=false:=by
  simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
  refine ⟨fun a ha hxa => ?_,fun a b hab hxa hxb => ?_⟩
  . simp only [xlp,decide_eq_true_eq] at hxa
    rcases hxa with rfl | rfl;exact hlA ha;exact hpA ha
  . simp only [xlp,decide_eq_true_eq] at hxa hxb
    rcases hxa with ha | ha <;> rcases hxb with hb | hb
    . rw [ha,hb] at hab;exact hab.ne rfl
    . rw [ha,hb] at hab;exact ((hK1 l p).mp hab).2.1 rfl
    . rw [ha,hb] at hab;exact ((hK1 p l).mp hab).2.2 rfl
    . rw [ha,hb] at hab;exact hab.ne rfl
 have hTSC :
  (v'=D.output->C.output=n+j1) ∧
  (∀ j' ∈ topGates d1 D,(gateAt C (iI j0 j1 j')).inputs =
   (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w')):=by
  have hslot_out : v'=D.output->C.output=n+j1:=by
   intro hvout
   have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
   have hOL:=outLst hmin hncC hne_g
   by_contra hne_out
   have hj1_lt' : j1+1 < C.gates.length:=by omega
   obtain ⟨j2,hj2,_,hmem2⟩:=evGtR hmin hncC j1 hj1_lt'
   have hj2_ne0 : j2≠j0:=by omega
   have hj2_ne1 : j2≠j1:=by omega
   have hIL : iM j0 j1 j2 < D.gates.length:=by have:=iMLt hj01 hj1 hj2 hj2_ne0 hj2_ne1;omega
   obtain ⟨hop2,hin2,_⟩:=hKF j2 hj2 hj2_ne0 hj2_ne1
   have hmem_in : n+j1 ∈ (gateAt C j2).inputs:=by
    rcases valNN hvD (gateAt D (iM j0 j1 j2)) (by rw [gateAt_eq_getElem D _ hIL];exact List.getElem_mem hIL) with h | h <;>
     rw [← hop2] at h <;> simp [eIn,h] at hmem2 <;> exact hmem2
   have hv'_in : v' ∈ (gateAt D (iM j0 j1 j2)).inputs:=by
    rw [hin2];exact List.mem_map.mpr ⟨n+j1,hmem_in,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
   by_cases hT : iM j0 j1 j2 ∈ topGates d1 D
   . have hr0 : readsIn D (topGates d1 D) D.output=0:=by
      rw [← hvout]
      rcases hvTp with hL | ⟨_,hG⟩
      . rw [(hvD.2.2.2.2.2.2.2.1 v' hL).2,if_pos hvout]
      . have h:=hvD.2.2.2.2.2.2.2.2.1 (v' - n) hG
        have hveq : n+(v' - n)=v':=by omega
        rw [hveq,if_pos hvout] at h;exact h
     have hpos:=(rInP D (topGates d1 D) D.output).mpr ⟨iM j0 j1 j2,hT,hvout ▸ hv'_in⟩
     omega
   . exact hnonTop_no_v' (iM j0 j1 j2) hIL hT hv'_in
  have hslot_gates : ∀ j' ∈ topGates d1 D,(gateAt C (iI j0 j1 j')).inputs =
   (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w'):=by
   intro j' hj'
   have hj'lt : j' < D.gates.length:=topGates_lt j' hj'
   have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
   have hne:=invIdx_ne (j':=j') hj01
   obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
   rw [idxMap_invIdx hj01] at hinD
   by_cases hvm : v' ∈ (gateAt D j').inputs
   . have hRJ1 : n+j1 ∈ (gateAt C (iI j0 j1 j')).inputs:=by
      by_contra hno_j1
      have hv'_ne_out : v'≠D.output:=by
       intro heq;rw [heq] at hvm
       have hr0 : readsIn D (topGates d1 D) D.output=0:=by
        rcases hvTp with hL | ⟨_,hG⟩
        . rw [heq] at hL;rw [(hvD.2.2.2.2.2.2.2.1 D.output hL).2,if_pos rfl]
        . have h:=hvD.2.2.2.2.2.2.2.2.1 (v' - n) hG
          have hveq : n+(v' - n)=D.output:=by omega
          rw [hveq,if_pos rfl] at h;exact h
       have hpos:=(rInP D (topGates d1 D) D.output).mpr ⟨j',hj',hvm⟩
       omega
      have hno_top_j1 : ∀ k' ∈ topGates d1 D,
       (gateAt C (iI j0 j1 k')).inputs=(gateAt D k').inputs.map (iW n j0 j1):=by
       intro k' hk'
       have hk'lt : k' < D.gates.length:=topGates_lt k' hk'
       have hklt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
       have hkne:=invIdx_ne (j':=k') hj01
       obtain ⟨_,hinDk,hsubk⟩:=hKF (iI j0 j1 k') hklt hkne.1 hkne.2
       rw [idxMap_invIdx hj01] at hinDk
       obtain ⟨a',b',hp',hab'⟩:=otGIP hvD.2.2.2.2.2.2 hk'
       refine (sInD hj01 hinDk (fun i hi => (hsubk i hi).2.2) hp' hab').2 ?_
       intro hmem
       have hv_in_k : v' ∈ (gateAt D k').inputs:=by
        rw [hinDk];exact List.mem_map.mpr ⟨n+j1,hmem,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
       have hkj : k'=j':=by
        have h:=osUP hvD.2.2.2.2.2.2 ⟨k',hk',rfl,hv_in_k⟩ ⟨j',hj',rfl,hvm⟩
        omega
       subst k';exact hno_j1 hmem
      have htop_xlp : ∀ w' < n+D.gates.length,w'≠l.val →
       wV n C xlp (iW n j0 j1 w')=wV n D xlp w':=by
       intro w'
       induction w' using Nat.strong_induction_on with
       | ind w' ih =>
        intro hw'lt hw'l
        by_cases hT : n<=w'/\w' - n ∈ topGates d1 D
        . have hk' : w' - n < D.gates.length:=topGates_lt _ hT.2
          have hweq : n+(w' - n)=w':=by omega
          have hklt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
          have hkne:=invIdx_ne (j':=w' - n) hj01
          unfold iW;rw [if_neg (by omega)]
          conv_rhs => rw [← hweq]
          rw [wvGR n C hrbC xlp (iI j0 j1 (w' - n)) hklt,
           wvGR n D hvD.1 xlp (w' - n) hk',
           (hIF (w' - n) hk').1,hno_top_j1 (w' - n) hT.2,List.map_map]
          congr 1;refine List.map_congr_left fun i' hi' => ?_
          have hilt:=hvD.1 (w' - n) hk' i' hi'
          have hi'l : i'≠l.val:=by
           have hmem_C : iW n j0 j1 i' ∈ (gateAt C (iI j0 j1 (w' - n))).inputs:=by
            rw [hno_top_j1 (w' - n) hT.2];exact List.mem_map.mpr ⟨i',hi',rfl⟩
           have h1:=((hKF (iI j0 j1 (w' - n)) hklt hkne.1 hkne.2).2.2 _ hmem_C).2.1
           intro heq;subst heq;unfold iW at h1;rw [if_pos l.isLt] at h1;exact h1 rfl
          exact ih i' (by omega) (by omega) hi'l
        . exact hval_nonTop xlp w' hw'lt hT hw'l
      have hCE : C.output=iW n j0 j1 D.output:=by
       have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
       have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
       rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
       . exact absurd hveq.symm hv'_ne_out
       . exact heq
      have hDout_ne_l : D.output≠l.val:=by
       intro h;have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
       have hOL:=outLst hmin hncC hne_g
       have h1 : C.output=l.val:=by rw [hCE,h];unfold iW;rw [if_pos l.isLt]
       have:=l.isLt;omega
      have hCxlp:=htop_xlp D.output hDout_lt hDout_ne_l
      rw [← hCE,wvO,wvO,hfun,nccEv hvD,hxlp_K,hxlp_K1] at hCxlp
      cases hCxlp
     obtain ⟨a',b',hp',hab'⟩:=otGIP hvD.2.2.2.2.2.2 hj'
     exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) hp' hab').1 hRJ1
   . rw [hinD,List.map_map];symm
     rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
     have hi0:=(hsub i hi).2.2
     have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hvm (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
     simp only [Function.comp_apply,id_eq,if_neg hwm_ne]
     rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
     . exact absurd hveq hwm_ne
     . exact heq.symm
  exact ⟨hslot_out,hslot_gates⟩
 have hu'_eq_p : u'=p.val:=by
  rcases huC with hup | ⟨hun,huG⟩
  . exact hup
  . exfalso
    obtain ⟨l1,hl1,l2,hl2,hl12,hr1,hr2⟩ :=
     otGTL hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.2.1 huG
    obtain ⟨r1,hr1f,rfl⟩:=mem_image.mp hl1
    obtain ⟨r2,hr2f,rfl⟩:=mem_image.mp hl2
    have hr12 : r1≠r2:=fun h => hl12 (by rw [h])
    have hueq : n+(u' - n)=u':=by omega
    have hpick : ∃ r',d1.owns q r'=true/\r'≠p/\OrReach n D (gatesOf d1 D Kind.o q.val) u' (d1.lam q r'):=by
     by_cases h : r1=p
     . exact ⟨r2,(mem_filter.mp hr2f).2,fun h2 => hr12 (h.trans h2.symm),by rwa [hueq] at hr2⟩
     . exact ⟨r1,(mem_filter.mp hr1f).2,h,by rwa [hueq] at hr1⟩
    obtain ⟨r',hown,hr'p,hru⟩:=hpick
    have hadj : K1.Adj q r':=(hvD.2.2.1.1 q r' hown).1
    have hKadj : K.Adj q r':=((hK1 q r').mp hadj).1
    have hr'l : r'≠l:=((hK1 q r').mp hadj).2.2
    have hr'A : r' ∉ A:=fun h => hA r' h q hKadj.symm
    let xlr : Fin n->Bool:=fun i => decide (i=l\/i=r')
    have hxlr_K : graphFun K A xlr=false:=by
     simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
     refine ⟨fun a ha hxa => ?_,fun a b hab hxa hxb => ?_⟩
     . simp only [xlr,decide_eq_true_eq] at hxa;rcases hxa with rfl | rfl;exact hlA ha;exact hr'A ha
     . simp only [xlr,decide_eq_true_eq] at hxa hxb
       rcases hxa with ha | ha <;> rcases hxb with hb | hb
       . rw [ha,hb] at hab;exact hab.ne rfl
       . rw [ha,hb] at hab;exact hr'p ((hl r').mp hab)
       . rw [ha,hb] at hab;exact hr'p ((hl r').mp hab.symm)
       . rw [ha,hb] at hab;exact hab.ne rfl
    have hlam_t : wV n D xlr (d1.lam q r')=true:=lam_true_of_input hvD hq_cov hown xlr (by simp [xlr])
    have hu'_t : wV n D xlr u'=true :=
     otER hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.2.1 xlr hru hlam_t
    have hj1_t : wV n C xlr (n+j1)=true:=by rw [hval_j1,hu'_t];simp [xlr]
    have hprop : ∀ w',OrReach n D (topGates d1 D) w' v' →
     wV n C xlr (if w'=v' then n+j1 else iW n j0 j1 w')=true:=by
     intro w' hreach
     induction hreach using ReflTransGen.head_induction_on with
     | refl => rw [if_pos rfl];exact hj1_t
     | head hstep hrest ih =>
      obtain ⟨k',hk'T,rfl,hmem⟩:=hstep
      have hk'lt : k' < D.gates.length:=topGates_lt k' hk'T
      have hne_kv : n+k'≠v':=by
       have:=hvD.1 k' hk'lt _ hmem
       have:=orLe hvD.1 topGates_lt hrest
       omega
      rw [if_neg hne_kv];unfold iW;rw [if_neg (by omega)]
      have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
      have hsub_eq : n+k' - n=k':=by omega
      rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 k') hlt,
       (hIF k' hk'lt).1,(hvD.2.2.2.2.2.2.1 k' hk'T).1,hTSC.2 k' hk'T]
      simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq]
      exact ⟨true,⟨_,hmem,ih⟩,rfl⟩
    have hreach_out:=otRR hvD.1 topGates_lt hvD.2.2.2.2.2.2 hvTp
    have hCout_val:=hprop D.output hreach_out
    have hCE : C.output=if D.output=v' then n+j1 else iW n j0 j1 D.output:=by
     by_cases h : D.output=v'
     . rw [if_pos h];exact hTSC.1 h.symm
     . rw [if_neg h]
       have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
       have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
       rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
       . exact absurd hveq h
       . exact heq
    rw [← hCE,wvO,hfun,hxlr_K] at hCout_val;cases hCout_val
 have hu_eq_p : u=p.val:=by rw [hu_eq,hu'_eq_p];unfold iW;rw [if_pos p.isLt]
 let d : NCCData n:={
  cover:=insert p d1.cover
  owns:=fun a b => if a=p/\b=l then true else d1.owns a b
  tie:=fun a => if a=p then none else d1.tie a
  role:=fun j =>
   if j=j0 then (Kind.b,p.val)
   else if j=j1 then (Kind.top,0)
   else d1.role (iM j0 j1 j)
  bw:=fun a => if a=p then n+j0 else iW n j0 j1 (d1.bw a)
  zroot:=fun a => if a=p then p.val else iW n j0 j1 (d1.zroot a)
  oroot:=fun a => if a=p then l.val else iW n j0 j1 (d1.oroot a)
  lam:=fun a b => if a=p then l.val else iW n j0 j1 (d1.lam a b)
 }
 have hRS : ∀ j' < D.gates.length,d.role (iI j0 j1 j')=d1.role j':=by
  intro j' _
  have hne:=invIdx_ne (j':=j') hj01
  simp only [d,if_neg hne.1,if_neg hne.2,idxMap_invIdx hj01]
 have hGOO : ∀ t ∈ d1.cover,∀ k : Kind,k≠Kind.top →
  gatesOf d C k t.val=(gatesOf d1 D k t.val).image (iI j0 j1):=by
  intro t ht k hk_ne
  have htp : t≠p:=fun h => hpNC (h ▸ ht)
  ext j;simp only [gatesOf,mem_filter,mem_range,mem_image]
  constructor
  . rintro ⟨hj,hr⟩
    have h0 : j≠j0:=fun h => by rw [h] at hr;simp only [d,↓reduceIte] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
    have h1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),↓reduceIte] at hr;exact hk_ne (Prod.ext_iff.mp hr).1.symm
    have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
    simp only [d,if_neg h0,if_neg h1] at hr
    exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
  . rintro ⟨j',⟨hj',hr'⟩,rfl⟩
    exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj',hr']⟩
 refine ⟨d,hrbC,hMCP,?_,?_,?_,?_,?_⟩
 ·
  refine ⟨?_,?_⟩
  . intro a b hown;simp only [d] at hown
    split_ifs at hown with h
    . rcases h with ⟨hap,hbl⟩;subst a;subst b;exact ⟨hLPA.symm,mem_insert_self _ _⟩
    . have h2:=hvD.2.2.1.1 a b hown
      exact ⟨((hK1 a b).mp h2.1).1,mem_insert_of_mem h2.2⟩
  . intro a b hab;simp only [d]
    by_cases hal : a=l
    . subst a
      have hbp : b=p:=(hl b).mp hab
      subst b
      have hnot : d1.owns l p=false:=by
       cases h : d1.owns l p;rfl;exfalso;exact hlNC (hvD.2.2.1.1 l p h).2
      simp [hlp,hnot]
    . by_cases hbl : b=l
      . subst b
        have hap : a=p:=(hl a).mp hab.symm
        subst a
        have hnot : d1.owns l p=false:=by
         cases h : d1.owns l p;rfl;exfalso;exact hlNC (hvD.2.2.1.1 l p h).2
        simp [hlp,hnot]
      . simp only [hal,hbl,and_false,↓reduceIte]
        exact hvD.2.2.1.2 a b ((hK1 a b).mpr ⟨hab,hal,hbl⟩)
 ·
  intro a b htie;simp only [d] at htie
  by_cases hap : a=p
  . rw [if_pos hap] at htie;cases htie
  . rw [if_neg hap] at htie
    have h2:=hvD.2.2.2.1 a b htie
    refine ⟨mem_insert_of_mem h2.1,?_⟩
    simp only [d];split_ifs;rfl;exact h2.2
 ·
  intro j hj
  by_cases h0 : j=j0
  . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d],fun _ => by simp [d]⟩
  . by_cases h1 : j=j1
    . subst j;left;simp [d,h0]
    . have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
      have hrole_eq : d.role j=d1.role (iM j0 j1 j):=by simp [d,h0,h1]
      rw [hrole_eq]
      rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨t,ht,hrt,hrb⟩
      . exact Or.inl htop
      . right
        have htp : t≠p:=fun h => hpNC (h ▸ ht)
        refine ⟨t,mem_insert_of_mem ht,hrt,fun hb => ?_⟩
        simp only [d,if_neg htp];rw [hrb hb]
        unfold iW;rw [if_neg (by omega)]
        have : n+iM j0 j1 j - n=iM j0 j1 j:=by omega
        rw [this,invIdx_idxMap hj01 h0 h1]
 ·
  intro t ht
  rcases mem_insert.mp ht with htp | ht'
  . subst t
    have hz_gates_p : gatesOf d C Kind.z p.val=∅:=by
     ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
     intro hj hr
     by_cases h0 : j=j0
     . subst j;simp [d] at hr
     . by_cases h1 : j=j1
       . subst j;simp [d,h0] at hr
       . simp only [d,if_neg h0,if_neg h1] at hr
         have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
         rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
         . rw [hr] at htop;cases htop
         . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
    have ho_gates_p : gatesOf d C Kind.o p.val=∅:=by
     ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
     intro hj hr
     by_cases h0 : j=j0
     . subst j;simp [d] at hr
     . by_cases h1 : j=j1
       . subst j;simp [d,h0] at hr
       . simp only [d,if_neg h0,if_neg h1] at hr
         have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
         rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
         . rw [hr] at htop;cases htop
         . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
    have hZLP : zLeaves d p={p.val}:=by
     ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton,d]
     constructor
     . rintro (rfl | ⟨a,⟨_,htie⟩,_⟩);rfl
       by_cases hap : a=p
       . rw [if_pos hap] at htie;cases htie
       . rw [if_neg hap] at htie;exact absurd (hvD.2.2.1.1 p a (hvD.2.2.2.1 a p htie).2).2 hpNC
     . rintro rfl;exact Or.inl rfl
    have hOLP : oLeaves d p={l.val}:=by
     ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,
      mem_singleton,d]
     constructor
     . rintro ⟨r,_,rfl⟩;simp
     . rintro rfl;exact ⟨l,by simp,by simp⟩
    refine ⟨⟨j0,by omega,by simp [d],by simp [d],hop0,
     by simp only [d,↓reduceIte];rw [hu_eq_p] at huin;rcases huin with h | h;exact Or.inr h;exact Or.inl h⟩,
     ?_,?_,?_⟩
    . rw [hz_gates_p,hZLP];simp [IsOrTree,readsIn,d]
    . rw [ho_gates_p,hOLP];simp [IsOrTree,readsIn,d]
    . intro r hown;simp only [d] at hown
      by_cases hrl : r=l
      . subst r;unfold LamOK
        have hl_nc : l ∉ d.cover:=by simp only [d,mem_insert,not_or];exact ⟨hlp,hlNC⟩
        rw [if_neg hl_nc];simp [d]
      . simp only [hrl,and_false,↓reduceIte] at hown
        exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
  ·
   have htp : t≠p:=fun h => hpNC (h ▸ ht')
   obtain ⟨j',hj',hbw',hrol',hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht').1
   have hj'notT : j' ∉ topGates d1 D:=fun h => by
    have h2:=(mem_filter.mp h).2;rw [hrol'] at h2;cases h2
   have hterm_t : TermOK n C d t:=by
    refine ⟨iI j0 j1 j',invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
     by simp only [d,if_neg htp,hbw'];unfold iW;rw [if_neg (by omega)];simp,
     by rw [hRS j' hj',hrol'],
     by rw [(hIF j' hj').1,hop'],?_⟩
    have hin_C:=hNTI j' hj' hj'notT
    simp only [d,if_neg htp]
    rcases hin' with h | h
    . left;rw [hin_C,h];rfl
    . right;rw [hin_C,h];rfl
   have hz_t : IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t):=by
    rw [hGOO t ht' Kind.z (by decide)]
    have hLeq : zLeaves d t=(zLeaves d1 t).image (iW n j0 j1):=by
     ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,d]
     constructor
     . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
       . exact ⟨t.val,Or.inl rfl,by unfold iW;rw [if_pos t.isLt]⟩
       . by_cases hap : a=p
         . rw [if_pos hap] at htie;cases htie
         . rw [if_neg hap] at htie
           have ha' : a ∈ d1.cover:=by rcases ha with rfl | h;exact absurd rfl hap;exact h
           exact ⟨d1.bw a,Or.inr ⟨a,⟨ha',htie⟩,rfl⟩,by simp [hap]⟩
     . rintro ⟨w',hw',rfl⟩
       rcases hw' with rfl | ⟨a,⟨ha',htie⟩,rfl⟩
       . left;unfold iW;rw [if_pos t.isLt]
       . right;have hap : a≠p:=fun h => hpNC (h ▸ ha')
         exact ⟨a,⟨Or.inr ha',by simp [hap,htie]⟩,by simp [hap]⟩
    rw [hLeq];simp only [d,if_neg htp]
    exact otLI (hvD.2.2.2.2.2.1 t ht').2.1 (iI j0 j1) (iW n j0 j1)
     (fun _ _ _ _ h => invIdx_inj hj01 h)
     (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
     (fun a b _ _ h => invWire_inj hj01 h)
     (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
     (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
      have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
      rw [h1] at h2;cases h2))
   have ho_t : IsOrTree n C (gatesOf d C Kind.o t.val) (oLeaves d t) (d.oroot t):=by
    rw [hGOO t ht' Kind.o (by decide)]
    have hLeq : oLeaves d t=(oLeaves d1 t).image (iW n j0 j1):=by
     ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,d,htp,false_and,↓reduceIte]
     constructor
     . rintro ⟨r,hr,rfl⟩;exact ⟨d1.lam t r,⟨r,hr,rfl⟩,rfl⟩
     . rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩;exact ⟨r,hr,rfl⟩
    rw [hLeq];simp only [d,if_neg htp]
    exact otLI (hvD.2.2.2.2.2.1 t ht').2.2.1 (iI j0 j1) (iW n j0 j1)
     (fun _ _ _ _ h => invIdx_inj hj01 h)
     (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
     (fun a b _ _ h => invWire_inj hj01 h)
     (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
     (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
      have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
      rw [h1] at h2;cases h2))
   have hlam_t : ∀ r,d.owns t r=true->LamOK n C d t r:=by
    intro r hown;simp only [d,htp,false_and,↓reduceIte] at hown
    have hl':=(hvD.2.2.2.2.2.1 t ht').2.2.2 r hown
    unfold LamOK at hl' ⊢
    by_cases hrp : r=p
    . subst r
      rw [if_neg hpNC] at hl'
      rw [if_pos (mem_insert_self _ _)]
      have hlam_d : d.lam t p=p.val:=by
       simp only [d,if_neg htp,hl'];unfold iW;rw [if_pos p.isLt]
      rw [hlam_d]
      refine ⟨(isCentred_input n C d p).mpr (mem_insert_self _ _),Or.inl rfl,fun htie => ?_⟩
      simp [d] at htie
    . have hRCI : r ∈ d.cover↔r ∈ d1.cover:=by simp [d,hrp]
      by_cases hrc : r ∈ d1.cover
      . rw [if_pos hrc] at hl';rw [if_pos (hRCI.mpr hrc)]
        have hRZ:=(icZIR hvD hrc hl'.2.1).mp hl'.1
        have hRC:=orLI
         (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
         (fun j' hj' => hNTI j' (gatesOf_lt j' hj') (fun hT => by
          have h1:=(mem_filter.mp hj').2;have h2:=(mem_filter.mp hT).2
          rw [h1] at h2;cases h2)) hRZ
        have hinv_r : iW n j0 j1 r.val=r.val:=by unfold iW;rw [if_pos r.isLt]
        rw [hinv_r] at hRC
        refine ⟨?_,?_,?_⟩
        . simp only [d,if_neg htp]
          exact icORZ hrbC (hRCI.mpr hrc) (fun j hj => by
           obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
           have hj'lt:=gatesOf_lt j' hj'
           exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
            by rw [hRS j' hj'lt,(mem_filter.mp hj').2]⟩) hRC
        . have hlam_d : d.lam t r=iW n j0 j1 (d1.lam t r):=by simp [d,htp]
          rw [hlam_d]
          rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
          . left;rw [h1,hinv_r]
          . right;exact ⟨iI j0 j1 k,invIdx_lt hj01 hj1 (by omega : k+2 < C.gates.length),
             by rw [h1];unfold iW;rw [if_neg (by omega)];simp,
             by rw [hRS k hk,h2]⟩
        . intro htie;simp only [d,if_neg hrp] at htie
          simp only [d,if_neg htp,if_neg hrp,hl'.2.2 htie]
      . rw [if_neg hrc] at hl';rw [if_neg (fun h => hrc (hRCI.mp h))]
        simp only [d,if_neg htp,hl'];unfold iW;rw [if_pos r.isLt]
   exact ⟨hterm_t,hz_t,ho_t,hlam_t⟩
 ·
  have hTGs : topGates d C=insert j1 ((topGates d1 D).image (iI j0 j1)):=by
   ext j;simp only [topGates,mem_filter,mem_range,mem_insert,mem_image]
   constructor
   . rintro ⟨hj,hr⟩
     by_cases h1 : j=j1
     . exact Or.inl h1
     . right
       have h0 : j≠j0:=fun h => by rw [h] at hr;simp [d] at hr
       simp only [d,if_neg h0,if_neg h1] at hr
       have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
       exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
   . rintro (h1 | ⟨j',⟨hj'lt,hr'⟩,rfl⟩)
     . subst j;exact ⟨hj1,by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte]⟩
     . exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj'lt,hr']⟩
  have hTLs : topLeaves d A=insert (n+j0) ((topLeaves d1 A).image (iW n j0 j1)):=by
   ext x;simp only [topLeaves,mem_union,mem_image,mem_filter,mem_insert,d]
   constructor
   . rintro (⟨a,haA,rfl⟩ | ⟨t,⟨htc,htie⟩,rfl⟩)
     . right;exact ⟨a.val,Or.inl ⟨a,haA,rfl⟩,by unfold iW;rw [if_pos a.isLt]⟩
     . by_cases htp : t=p
       . subst t;left;simp
       . right;rw [if_neg htp] at htie ⊢
         have ht' : t ∈ d1.cover:=by rcases htc with rfl | h;exact absurd rfl htp;exact h
         exact ⟨d1.bw t,Or.inr ⟨t,⟨ht',htie⟩,rfl⟩,rfl⟩
   . rintro (rfl | ⟨w',hw',rfl⟩)
     . right;exact ⟨p,⟨Or.inl rfl,by simp⟩,by simp⟩
     . rcases hw' with ⟨a,haA,rfl⟩ | ⟨t,⟨ht',htie⟩,rfl⟩
       . left;exact ⟨a,haA,by unfold iW;rw [if_pos a.isLt]⟩
       . right;have htp : t≠p:=fun h => hpNC (h ▸ ht')
         exact ⟨t,⟨Or.inr ht',by simp [htp,htie]⟩,by simp [htp]⟩
  have hCE : C.output=if D.output=v' then n+j1 else iW n j0 j1 D.output:=by
   by_cases h : D.output=v'
   . rw [if_pos h];exact hTSC.1 h.symm
   . rw [if_neg h]
     have hne_g : C.gates ≠ []:=by intro h0;simp [h0] at hj1
     have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
     rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
     . exact absurd hveq h
     . exact heq
  rw [hTGs,hTLs,hCE]
  exact otLIn hvD.2.2.2.2.2.2 hvTp (iI j0 j1) (iW n j0 j1)
   (fun _ _ _ _ h => invIdx_inj hj01 h)
   (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
   (fun a b _ _ h => invWire_inj hj01 h)
   (fun a _ => (invWire_ne_j0_j1 (w':=a) hj01).2)
   (fun a _ => (invWire_ne_j0_j1 (w':=a) hj01).1)
   (by omega) hop1 (hv_eq ▸ hvin)
   (fun j' hj' => (hIF j' (topGates_lt j' hj')).1)
   (fun j' hj' => hTSC.2 j' hj')
set_option maxHeartbeats 800000 in
lemma fwd2cB {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {C D : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A)
 (hrbC : ReadsBack n C) (hncC : ∃ x y,circuitFun n C x≠circuitFun n C y)
 {j0 j1 u v u' v' : ℕ} (hj01 : j0 < j1) (hj1 : j1 < C.gates.length)
 (hop0 : (gateAt C j0).op=.and)
 (huin : (gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val])
 (hop1 : (gateAt C j1).op=.or)
 (hvin : (gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0])
 (hv_eq : v=iW n j0 j1 v') (hu_eq : u=iW n j0 j1 u')
 {d1 : NCCData n} (hvD : Valid n K1 A D d1)
 (hD_len : D.gates.length+2=C.gates.length)
 (hKF : ∀ j < C.gates.length,j≠j0->j≠j1 →
  (gateAt C j).op=(gateAt D (iM j0 j1 j)).op ∧
  (gateAt D (iM j0 j1 j)).inputs=(gateAt C j).inputs.map (wM n j0 j1 v') ∧
  ∀ i ∈ (gateAt C j).inputs,i < n+j/\i≠l.val/\i≠n+j0)
 (hIF : ∀ j' < D.gates.length,
  (gateAt C (iI j0 j1 j')).op=(gateAt D j').op ∧
  (gateAt D j').inputs=(gateAt C (iI j0 j1 j')).inputs.map (wM n j0 j1 v'))
 (hOE : D.output=wM n j0 j1 v' C.output)
 (hDout_lt : D.output < n+D.gates.length)
 (hpNC : p ∉ d1.cover) (hlNC : l ∉ d1.cover)
 (hMCP : IsMinCover K (insert p d1.cover))
 (hq_cov : q ∈ d1.cover) (hq_owns_p : d1.owns q p=true)
 (hval_j1 : ∀ x : Fin n->Bool,wV n C x (n+j1)=((x l && wV n D x u') || wV n D x v'))
 (huC : u'=p.val\/(n<=u'/\u' - n ∈ gatesOf d1 D Kind.o q.val))
 (hv'_zq : v' ∈ zLeaves d1 q\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z q.val)) :
 IsNestedCoverCircuit n K A C:=by
 classical
 obtain ⟨hlp,hpq,hlA,hpA,hqA,_,_,_⟩:=gArith K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 have hA1 : ∀ a ∈ A,∀ w : Fin n,¬ K1.Adj a w:=fun a ha w hw => hA a ha w ((hK1 a w).mp hw).1
 have hv'_not_top : ¬ (v' ∈ topLeaves d1 A\/(n<=v'/\v' - n ∈ topGates d1 D)) :=
  fun h => tnDZ hvD hA1 hq_cov h hv'_zq
 have hv'_ne_l : v'≠l.val:=by
  intro h;rw [h] at hv'_zq
  rcases hv'_zq with hL | ⟨hln,_⟩
  . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
    . exact hql (Fin.ext h1.symm)
    . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
      obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hs).1
      have:=l.isLt;omega
  . have:=l.isLt;omega
 have hv'_lt_bwq : v' < d1.bw q:=by
  have hr:=otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.1 hv'_zq
  have h1:=orLe hvD.1 gatesOf_lt hr
  have h2:=(term_roots_lt_bw hvD hq_cov).1
  omega
 have hNVI : ∀ j' < D.gates.length,v' ∉ (gateAt D j').inputs →
  (gateAt C (iI j0 j1 j')).inputs=(gateAt D j').inputs.map (iW n j0 j1):=by
  intro j' hj' hno
  have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
  have hne:=invIdx_ne (j':=j') hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  rw [hinD,List.map_map];symm
  rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
  have hi0:=(hsub i hi).2.2
  have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hno (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
  rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
  . exact absurd hveq hwm_ne
  . exact heq.symm
 have htop_no_v' : ∀ j' ∈ topGates d1 D,v' ∉ (gateAt D j').inputs:=fun j' hj' hmem =>
  hv'_not_top ((hvD.2.2.2.2.2.2.1 j' hj').2.2 v' hmem)
 have hzt_no_v' : ∀ t ∈ d1.cover,t≠q->∀ j' ∈ gatesOf d1 D Kind.z t.val,v' ∉ (gateAt D j').inputs :=
  fun t ht htq j' hj' hmem =>
   znDN hvD htq (((hvD.2.2.2.2.2.1 t ht).2.1.1 j' hj').2.2 v' hmem) hv'_zq
 have hBZV : ∀ t ∈ d1.cover,t≠q->d1.zroot t≠v':=by
  intro t ht htq heq
  have hznode : d1.zroot t ∈ zLeaves d1 t\/(n<=d1.zroot t/\d1.zroot t - n ∈ gatesOf d1 D Kind.z t.val):=by
   have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
   by_cases hGe : gatesOf d1 D Kind.z t.val=∅
   . rw [if_pos hGe] at hz;left;rw [hz];simp
   . rw [if_neg hGe] at hz;obtain ⟨k,hk,hkeq⟩:=hz;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
  exact znDN hvD htq (heq ▸ hznode) hv'_zq
 have hBOV : d1.oroot q≠v':=by
  intro heq
  have honode : v' ∈ oLeaves d1 q\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.o q.val):=by
   rw [← heq];have ho:=(hvD.2.2.2.2.2.1 q hq_cov).2.2.1.2.2.2
   by_cases hGe : gatesOf d1 D Kind.o q.val=∅
   . rw [if_pos hGe] at ho;left;rw [ho];simp
   . rw [if_neg hGe] at ho;obtain ⟨k,hk,hkeq⟩:=ho;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
  rcases honode with hoL | ⟨_,hoG⟩
  . obtain ⟨r,hr,hLE⟩:=mem_image.mp hoL
    have hown:=(mem_filter.mp hr).2
    have hrq : r≠q:=(hvD.2.2.1.1 q r hown).1.ne.symm
    have hlam:=(hvD.2.2.2.2.2.1 q hq_cov).2.2.2 r hown
    unfold LamOK at hlam
    by_cases hrc : r ∈ d1.cover
    . rw [if_pos hrc] at hlam
      have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
       rw [← hLE]
       rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
       . left;rw [h1];exact mem_insert_self _ _
       . right;refine ⟨by omega,?_⟩
         have : d1.lam q r - n=k:=by omega
         rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
      exact znDN hvD hrq hzr hv'_zq
    . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hv'_zq
      rcases hv'_zq with hL | ⟨hwn,_⟩
      . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
        . exact hrq (Fin.ext h1)
        . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
          obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hs).1
          have:=r.isLt;omega
      . have:=r.isLt;omega
  . rcases hv'_zq with hL | ⟨_,hzG⟩
    . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
      . rw [h1] at hoG;have:=(mem_filter.mp hoG).1;have:=q.isLt;omega
      . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
        obtain ⟨js,_,hbw',hrol⟩:=bwS hvD s (mem_filter.mp hs).1
        have h1:=(mem_filter.mp hoG).2
        have : v' - n=js:=by omega
        rw [this,hrol] at h1;cases h1
    . have h1:=(mem_filter.mp hzG).2;have h2:=(mem_filter.mp hoG).2
      rw [h1] at h2;cases h2
 have hDout_node : D.output ∈ topLeaves d1 A\/(n<=D.output/\D.output - n ∈ topGates d1 D):=by
  have hroot:=hvD.2.2.2.2.2.2.2.2.2
  by_cases hGe : topGates d1 D=∅
  . rw [if_pos hGe] at hroot;left;rw [hroot];simp
  . rw [if_neg hGe] at hroot;obtain ⟨k,hk,hkeq⟩:=hroot;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
 have hDout_ne_v' : D.output≠v':=fun h => hv'_not_top (h ▸ hDout_node)
 have hCE : C.output=iW n j0 j1 D.output:=by
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
  have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
  rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
  . exact absurd hveq hDout_ne_v'
  . exact heq
 let xlp : Fin n->Bool:=fun i => decide (i=l\/i=p)
 have hxlp_K : graphFun K A xlp=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨l,p,hLPA,by simp [xlp],by simp [xlp]⟩
 have hno_zq_j1_absurd :
  (∀ k' ∈ gatesOf d1 D Kind.z q.val,n+j1 ∉ (gateAt C (iI j0 j1 k')).inputs) →
  (∀ jb' < D.gates.length,d1.bw q=n+jb'->n+j1 ∉ (gateAt C (iI j0 j1 jb')).inputs) →
  False:=by
  intro hno_zg hno_bg
  have hsafe : ∀ w' < n+D.gates.length,
   ((w' < n/\w'≠l.val/\w'≠p.val) ∨
    (n<=w'/\w' - n < D.gates.length ∧
     ((d1.role (w' - n)).1=Kind.top\/(d1.role (w' - n)).1=Kind.b\/(d1.role (w' - n)).1=Kind.z))) →
   wV n C xlp (iW n j0 j1 w')=false:=by
   intro w'
   induction w' using Nat.strong_induction_on with
   | ind w' ih =>
    intro hw'lt hs
    rcases hs with ⟨hwn,hwl,hwp⟩ | ⟨hwn,hj',hkind⟩
    . let wf : Fin n:=⟨w',hwn⟩
      unfold iW;rw [if_pos hwn]
      change wV n C xlp wf.val=false
      have h1 : wf≠l:=fun h => hwl (congrArg Fin.val h)
      have h2 : wf≠p:=fun h => hwp (congrArg Fin.val h)
      rw [wvI];simp [xlp,h1,h2]
    . have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
      have hne:=invIdx_ne (j':=w' - n) hj01
      unfold iW;rw [if_neg (by omega : ¬ w' < n)]
      rw [wvGR n C hrbC xlp (iI j0 j1 (w' - n)) hlt,(hIF (w' - n) hj').1]
      rcases hkind with htop | hb | hz
      . have hjT : w' - n ∈ topGates d1 D:=mem_filter.mpr ⟨mem_range.mpr hj',htop⟩
        rw [(hvD.2.2.2.2.2.2.1 (w' - n) hjT).1,hNVI (w' - n) hj' (htop_no_v' (w' - n) hjT)]
        simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
        rintro b ⟨i',hi',hbi'⟩
        have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
        have hi'safe : (i' < n/\i'≠l.val/\i'≠p.val) ∨
         (n<=i'/\i' - n < D.gates.length ∧
          ((d1.role (i' - n)).1=Kind.top\/(d1.role (i' - n)).1=Kind.b\/(d1.role (i' - n)).1=Kind.z)):=by
         rcases (hvD.2.2.2.2.2.2.1 (w' - n) hjT).2.2 i' hi' with hL | ⟨hin,hG⟩
         . unfold topLeaves at hL;rcases mem_union.mp hL with hA' | hB'
           . obtain ⟨a,haA,rfl⟩:=mem_image.mp hA'
             exact Or.inl ⟨a.isLt,fun h => hlA (Fin.ext h ▸ haA),fun h => hpA (Fin.ext h ▸ haA)⟩
           . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
             obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
             right;refine ⟨by omega,by omega,Or.inr (Or.inl ?_)⟩
             have : d1.bw s - n=js:=by omega
             rw [this,hrol]
         . exact Or.inr ⟨hin,topGates_lt _ hG,Or.inl (mem_filter.mp hG).2⟩
        have hf:=ih i' hilt (by omega) hi'safe
        rw [hf] at hbi';subst hbi';decide
      . rcases hvD.2.2.2.2.1 (w' - n) hj' with htop | ⟨t,ht,_,hrb⟩
        . rw [hb] at htop;cases htop
        . obtain ⟨jb',hjb',hbw',_,hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht).1
          have hbw:=hrb hb
          have hjj : w' - n=jb':=by omega
          rw [hjj,hop']
          have hlt':=invIdx_lt hj01 hj1 (by omega : jb'+2 < C.gates.length)
          have hne':=invIdx_ne (j':=jb') hj01
          obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 jb') hlt' hne'.1 hne'.2
          rw [idxMap_invIdx hj01] at hinD
          have hzr_in_C : iW n j0 j1 (d1.zroot t) ∈ (gateAt C (iI j0 j1 jb')).inputs:=by
           have hzr_in_D : d1.zroot t ∈ (gateAt D jb').inputs:=by rcases hin' with h | h <;> rw [h] <;> simp
           rw [hinD] at hzr_in_D
           obtain ⟨i,hi,hwm⟩:=List.mem_map.mp hzr_in_D
           by_cases htq : t=q
           . subst t
             have hne_j1 : i≠n+j1:=fun h => hno_bg jb' hjb' hbw' (h ▸ hi)
             rcases (wMEq hj01 (hsub i hi).2.2).mp hwm with ⟨habs,_⟩ | ⟨_,heq⟩
             . exact absurd habs hne_j1
             . exact heq ▸ hi
           . rcases (wMEq hj01 (hsub i hi).2.2).mp hwm with ⟨_,hveq⟩ | ⟨_,heq⟩
             . exact absurd hveq (hBZV t ht htq)
             . exact heq ▸ hi
          have hzr_lt : d1.zroot t < w':=by have:=(term_roots_lt_bw hvD ht).1;omega
          have hzr_safe : (d1.zroot t < n/\d1.zroot t≠l.val/\d1.zroot t≠p.val) ∨
           (n<=d1.zroot t/\d1.zroot t - n < D.gates.length ∧
            ((d1.role (d1.zroot t - n)).1=Kind.top\/(d1.role (d1.zroot t - n)).1=Kind.b\/(d1.role (d1.zroot t - n)).1=Kind.z)):=by
           have hz:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
           by_cases hGe : gatesOf d1 D Kind.z t.val=∅
           . rw [if_pos hGe] at hz
             have htp : d1.zroot t=t.val:=by
              have : t.val ∈ zLeaves d1 t:=mem_insert_self _ _
              rw [hz,mem_singleton] at this;exact this.symm
             rw [htp]
             exact Or.inl ⟨t.isLt,fun h => hlNC (Fin.ext h ▸ ht),fun h => hpNC (Fin.ext h ▸ ht)⟩
           . rw [if_neg hGe] at hz;obtain ⟨k,hk,hkeq⟩:=hz
             right;refine ⟨by omega,by have:=gatesOf_lt k hk;omega,Or.inr (Or.inr ?_)⟩
             have : d1.zroot t - n=k:=by omega
             rw [this,(mem_filter.mp hk).2]
          have hf:=ih (d1.zroot t) hzr_lt (by omega) hzr_safe
          simp only [GateOp.eval,List.all_eq_false,List.mem_map]
          exact ⟨false,⟨iW n j0 j1 (d1.zroot t),hzr_in_C,hf⟩,by decide⟩
      . rcases hvD.2.2.2.2.1 (w' - n) hj' with htop | ⟨t,ht,hrt,_⟩
        . rw [hz] at htop;cases htop
        . have hjZ : w' - n ∈ gatesOf d1 D Kind.z t.val :=
           mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hz hrt⟩
          have hin_C : (gateAt C (iI j0 j1 (w' - n))).inputs=(gateAt D (w' - n)).inputs.map (iW n j0 j1):=by
           by_cases htq : t=q
           . subst t
             obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 (w' - n)) hlt hne.1 hne.2
             rw [idxMap_invIdx hj01] at hinD
             obtain ⟨a',b',hp',hab'⟩:=otGIP (hvD.2.2.2.2.2.1 q hq_cov).2.1 hjZ
             exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) hp' hab').2 (hno_zg (w' - n) hjZ)
           . exact hNVI (w' - n) hj' (hzt_no_v' t ht htq (w' - n) hjZ)
          rw [(hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ |>.1,hin_C]
          simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
          rintro b ⟨i',hi',hbi'⟩
          have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
          have hi'safe : (i' < n/\i'≠l.val/\i'≠p.val) ∨
           (n<=i'/\i' - n < D.gates.length ∧
            ((d1.role (i' - n)).1=Kind.top\/(d1.role (i' - n)).1=Kind.b\/(d1.role (i' - n)).1=Kind.z)):=by
           rcases ((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ).2.2 i' hi' with hL | ⟨hin,hG⟩
           . unfold zLeaves at hL;rcases mem_insert.mp hL with rfl | himg
             . exact Or.inl ⟨t.isLt,fun h => hlNC (Fin.ext h ▸ ht),fun h => hpNC (Fin.ext h ▸ ht)⟩
             . obtain ⟨s,hsF,rfl⟩:=mem_image.mp himg
               obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
               right;refine ⟨by omega,by omega,Or.inr (Or.inl ?_)⟩
               have : d1.bw s - n=js:=by omega
               rw [this,hrol]
           . right;exact ⟨hin,gatesOf_lt _ hG,Or.inr (Or.inr (by rw [(mem_filter.mp hG).2]))⟩
          have hf:=ih i' hilt (by omega) hi'safe
          rw [hf] at hbi';subst hbi';decide
  have hDout_safe : (D.output < n/\D.output≠l.val/\D.output≠p.val) ∨
   (n<=D.output/\D.output - n < D.gates.length ∧
    ((d1.role (D.output - n)).1=Kind.top\/(d1.role (D.output - n)).1=Kind.b\/(d1.role (D.output - n)).1=Kind.z)):=by
   rcases hDout_node with hL | ⟨hin,hG⟩
   . unfold topLeaves at hL;rcases mem_union.mp hL with hA' | hB'
     . obtain ⟨a,haA,h1⟩:=mem_image.mp hA'
       rw [← h1];exact Or.inl ⟨a.isLt,fun h => hlA (Fin.ext h ▸ haA),fun h => hpA (Fin.ext h ▸ haA)⟩
     . obtain ⟨s,hsF,h1⟩:=mem_image.mp hB'
       obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
       right;refine ⟨by omega,by omega,Or.inr (Or.inl ?_)⟩
       have : D.output - n=js:=by omega
       rw [this,hrol]
   . exact Or.inr ⟨hin,topGates_lt _ hG,Or.inl (mem_filter.mp hG).2⟩
  have hf:=hsafe D.output hDout_lt hDout_safe
  rw [← hCE,wvO,hfun,hxlp_K] at hf;cases hf
 have hzq_slot_C : ∀ j' ∈ gatesOf d1 D Kind.z q.val,
  (gateAt C (iI j0 j1 j')).inputs =
   (gateAt D j').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w'):=by
  intro j' hj'
  have hj'lt : j' < D.gates.length:=gatesOf_lt j' hj'
  have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
  have hne:=invIdx_ne (j':=j') hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  by_cases hvm : v' ∈ (gateAt D j').inputs
  . have hRJ1 : n+j1 ∈ (gateAt C (iI j0 j1 j')).inputs:=by
     by_contra hno_j1
     have hv'_ne_zr : v'≠d1.zroot q:=by
      intro heq;rw [heq] at hvm
      have hr0 : readsIn D (gatesOf d1 D Kind.z q.val) (d1.zroot q)=0:=by
       rcases hv'_zq with hL | ⟨_,hG⟩
       . rw [heq] at hL;rw [((hvD.2.2.2.2.2.1 q hq_cov).2.1.2.1 _ hL).2,if_pos rfl]
       . have h:=(hvD.2.2.2.2.2.1 q hq_cov).2.1.2.2.1 (v' - n) hG
         have hveq : n+(v' - n)=d1.zroot q:=by omega
         rw [hveq,if_pos rfl] at h;exact h
      have hpos:=(rInP D (gatesOf d1 D Kind.z q.val) (d1.zroot q)).mpr ⟨j',hj',hvm⟩
      omega
     refine hno_zq_j1_absurd ?_ ?_
     . intro k' hk' hmem
       have hk'lt:=gatesOf_lt k' hk'
       have hv_in_k : v' ∈ (gateAt D k').inputs:=by
        rw [(hIF k' hk'lt).2]
        exact List.mem_map.mpr ⟨n+j1,hmem,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
       have hkj : k'=j':=by
        have h:=osUP (hvD.2.2.2.2.2.1 q hq_cov).2.1 ⟨k',hk',rfl,hv_in_k⟩ ⟨j',hj',rfl,hvm⟩
        omega
       subst k';exact hno_j1 hmem
     . intro jb' hjb' hbw' hmem
       have hv_in_b : v' ∈ (gateAt D jb').inputs:=by
        rw [(hIF jb' hjb').2]
        exact List.mem_map.mpr ⟨n+j1,hmem,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
       obtain ⟨jb'2,_,hbw'2,_,_,hin'⟩:=(hvD.2.2.2.2.2.1 q hq_cov).1
       have hjj : jb'=jb'2:=by omega
       subst jb'
       rcases hin' with h | h <;> rw [h] at hv_in_b <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hv_in_b
       . rcases hv_in_b with h1 | h2;exact hv'_ne_zr h1;exact hBOV h2.symm
       . rcases hv_in_b with h1 | h2;exact hBOV h1.symm;exact hv'_ne_zr h2
    obtain ⟨a',b',hp',hab'⟩:=otGIP (hvD.2.2.2.2.2.1 q hq_cov).2.1 hj'
    exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) hp' hab').1 hRJ1
  . rw [hinD,List.map_map];symm
    rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
    have hi0:=(hsub i hi).2.2
    have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hvm (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
    simp only [Function.comp_apply,id_eq,if_neg hwm_ne]
    rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
    . exact absurd hveq hwm_ne
    . exact heq.symm
 have hbq_slot_C : ∀ jb' < D.gates.length,d1.bw q=n+jb' →
  (gateAt C (iI j0 j1 jb')).inputs =
   (gateAt D jb').inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w'):=by
  intro jb' hjb' hbw'
  obtain ⟨jb'2,_,hbw'2,_,_,hin'⟩:=(hvD.2.2.2.2.2.1 q hq_cov).1
  have hjj : jb'=jb'2:=by omega
  subst jb'
  have hlt:=invIdx_lt hj01 hj1 (by omega : jb'2+2 < C.gates.length)
  have hne:=invIdx_ne (j':=jb'2) hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 jb'2) hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  by_cases hvz : v'=d1.zroot q
  . have hreads_j1 : n+j1 ∈ (gateAt C (iI j0 j1 jb'2)).inputs:=by
     by_contra hno_j1
     refine hno_zq_j1_absurd ?_ ?_
     . intro k' hk' hmem
       have hk'lt:=gatesOf_lt k' hk'
       have hv_in_k : v' ∈ (gateAt D k').inputs:=by
        rw [(hIF k' hk'lt).2]
        exact List.mem_map.mpr ⟨n+j1,hmem,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
       have hr0 : readsIn D (gatesOf d1 D Kind.z q.val) (d1.zroot q)=0:=by
        rcases hv'_zq with hL | ⟨_,hG⟩
        . rw [hvz] at hL;rw [((hvD.2.2.2.2.2.1 q hq_cov).2.1.2.1 _ hL).2,if_pos rfl]
        . have h:=(hvD.2.2.2.2.2.1 q hq_cov).2.1.2.2.1 (v' - n) hG
          have hveq : n+(v' - n)=d1.zroot q:=by omega
          rw [hveq,if_pos rfl] at h;exact h
       have hpos:=(rInP D (gatesOf d1 D Kind.z q.val) (d1.zroot q)).mpr ⟨k',hk',hvz ▸ hv_in_k⟩
       omega
     . intro jb'3 _ hbw3 hmem
       have : jb'3=jb'2:=by omega
       subst jb'3;exact hno_j1 hmem
    have hne_zo:=zrNeOr hvD hq_cov
    rcases hin' with h | h
    . exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) h hne_zo).1 hreads_j1
    . exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) h hne_zo.symm).1 hreads_j1
  . have hno_v : v' ∉ (gateAt D jb'2).inputs:=by
     intro hm;rcases hin' with h | h <;> rw [h] at hm <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
     . rcases hm with h1 | h2;exact hvz h1;exact hBOV h2.symm
     . rcases hm with h1 | h2;exact hBOV h1.symm;exact hvz h2
    rw [hNVI jb'2 hjb' hno_v]
    refine List.map_congr_left fun w' hw' => ?_
    have hne_w : w'≠v':=fun h => hno_v (h ▸ hw')
    rw [if_neg hne_w]
 let readsJ1 (t : Fin n) : Prop :=
  (∃ k' ∈ gatesOf d1 D Kind.o t.val,n+j1 ∈ (gateAt C (iI j0 j1 k')).inputs) ∨
  (gatesOf d1 D Kind.o t.val=∅ /\ ∃ jb' < D.gates.length,d1.bw t=n+jb'/\n+j1 ∈ (gateAt C (iI j0 j1 jb')).inputs)
 let lamMap (t : Fin n) (w' : ℕ) : ℕ :=
  if w'=v'/\d1.owns t q=true/\d1.lam t q=v'/\readsJ1 t then n+j1 else iW n j0 j1 w'
 have hot_inputs_C : ∀ t ∈ d1.cover,∀ k' ∈ gatesOf d1 D Kind.o t.val,
  (gateAt C (iI j0 j1 k')).inputs=(gateAt D k').inputs.map (lamMap t):=by
  intro t ht k' hk'
  have hk'lt:=gatesOf_lt k' hk'
  have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
  have hne:=invIdx_ne (j':=k') hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 k') hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  by_cases hvm : v' ∈ (gateAt D k').inputs
  ·
   have hown_lam : d1.owns t q=true/\d1.lam t q=v':=by
    rcases ((hvD.2.2.2.2.2.1 t ht).2.2.1.1 k' hk').2.2 v' hvm with hL | ⟨_,hG⟩
    . obtain ⟨r,hr,hLE⟩:=mem_image.mp hL
      have hown:=(mem_filter.mp hr).2
      have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
      unfold LamOK at hlam
      by_cases hrc : r ∈ d1.cover
      . rw [if_pos hrc] at hlam
        have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
         rw [← hLE]
         rcases hlam.2.1 with h1 | ⟨m,hm,h1,h2⟩
         . left;rw [h1];exact mem_insert_self _ _
         . right;refine ⟨by omega,?_⟩
           have : d1.lam t r - n=m:=by omega
           rw [this];exact mem_filter.mpr ⟨mem_range.mpr hm,h2⟩
        have hrq : r=q:=by by_contra hne_r;exact znDN hvD hne_r hzr hv'_zq
        subst r;exact ⟨hown,hLE⟩
      . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hv'_zq
        exfalso
        rcases hv'_zq with hL' | ⟨hwn,_⟩
        . unfold zLeaves at hL';rcases mem_insert.mp hL' with h1 | himg
          . exact hrc (Fin.ext h1 ▸ hq_cov)
          . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
            obtain ⟨js,_,hbw',_⟩:=bwS hvD s (mem_filter.mp hs).1
            have:=r.isLt;omega
        . have:=r.isLt;omega
    . exfalso
      rcases hv'_zq with hL | ⟨_,hZ⟩
      . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
        . rw [h1] at hG;have:=(mem_filter.mp hG).1;have:=q.isLt;omega
        . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
          obtain ⟨js,_,hbw',hrol⟩:=bwS hvD s (mem_filter.mp hs).1
          have h1:=(mem_filter.mp hG).2
          have : v' - n=js:=by omega
          rw [this,hrol] at h1;cases h1
      . have h1:=(mem_filter.mp hZ).2;have h2:=(mem_filter.mp hG).2
        rw [h1] at h2;cases h2
   obtain ⟨a',b',hp',hab'⟩:=otGIP (hvD.2.2.2.2.2.1 t ht).2.2.1 hk'
   by_cases hrj : readsJ1 t
   . have hk_reads : n+j1 ∈ (gateAt C (iI j0 j1 k')).inputs:=by
      rcases hrj with ⟨k2,hk2,hmem2⟩ | ⟨hGe,_⟩
      . have hv_in_k2 : v' ∈ (gateAt D k2).inputs:=by
         rw [(hIF k2 (gatesOf_lt k2 hk2)).2]
         exact List.mem_map.mpr ⟨n+j1,hmem2,by unfold wM;rw [if_neg (by omega),if_pos rfl]⟩
        have hkk : k2=k':=by
         have h:=osUP (hvD.2.2.2.2.2.1 t ht).2.2.1 ⟨k2,hk2,rfl,hv_in_k2⟩ ⟨k',hk',rfl,hvm⟩
         omega
        subst k2;exact hmem2
      . rw [hGe] at hk';simp at hk'
     rw [(sInD hj01 hinD (fun i hi => (hsub i hi).2.2) hp' hab').1 hk_reads]
     refine List.map_congr_left fun w' _ => ?_
     simp only [lamMap,hown_lam.1,hown_lam.2,hrj,and_true]
   . have hk_no : n+j1 ∉ (gateAt C (iI j0 j1 k')).inputs:=fun h => hrj (Or.inl ⟨k',hk',h⟩)
     rw [(sInD hj01 hinD (fun i hi => (hsub i hi).2.2) hp' hab').2 hk_no]
     refine List.map_congr_left fun w' _ => ?_
     simp only [lamMap,hrj,and_false,↓reduceIte]
  . rw [hNVI k' hk'lt hvm]
    refine List.map_congr_left fun w' hw' => ?_
    have hne_w : w'≠v':=fun h => hvm (h ▸ hw')
    simp only [lamMap,hne_w,false_and,↓reduceIte]
 have hbt_inputs_C : ∀ t ∈ d1.cover,t≠q->∀ jb' < D.gates.length,d1.bw t=n+jb' →
  (gateAt C (iI j0 j1 jb')).inputs =
   (gateAt D jb').inputs.map (lamMap t):=by
  intro t ht htq jb' hjb' hbw'
  obtain ⟨jb'2,_,hbw'2,_,_,hin'⟩:=(hvD.2.2.2.2.2.1 t ht).1
  have hjj : jb'=jb'2:=by omega
  subst jb'
  have hlt:=invIdx_lt hj01 hj1 (by omega : jb'2+2 < C.gates.length)
  have hne:=invIdx_ne (j':=jb'2) hj01
  obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 jb'2) hlt hne.1 hne.2
  rw [idxMap_invIdx hj01] at hinD
  by_cases hvo : v'=d1.oroot t
  . have hGe : gatesOf d1 D Kind.o t.val=∅:=by
     by_contra hne_e
     have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
     rw [if_neg hne_e] at ho;obtain ⟨k,hk,hkeq⟩:=ho
     rcases hv'_zq with hL | ⟨_,hZ⟩
     . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
       . have:=q.isLt;omega
       . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
         obtain ⟨js,_,hbw's,hrol⟩:=bwS hvD s (mem_filter.mp hs).1
         have h1:=(mem_filter.mp hk).2
         have : k=js:=by omega
         rw [this,hrol] at h1;cases h1
     . have h1:=(mem_filter.mp hk).2;have h2:=(mem_filter.mp hZ).2
       have : v' - n=k:=by omega
       rw [this,h1] at h2;cases h2
    have hown_lam : d1.owns t q=true/\d1.lam t q=v':=by
     have ho:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
     rw [if_pos hGe] at ho
     have hvL : v' ∈ oLeaves d1 t:=by rw [ho,hvo];simp
     obtain ⟨r,hr,hLE⟩:=mem_image.mp hvL
     have hown:=(mem_filter.mp hr).2
     have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
     unfold LamOK at hlam
     by_cases hrc : r ∈ d1.cover
     . rw [if_pos hrc] at hlam
       have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
        rw [← hLE]
        rcases hlam.2.1 with h1 | ⟨m,hm,h1,h2⟩
        . left;rw [h1];exact mem_insert_self _ _
        . right;refine ⟨by omega,?_⟩
          have : d1.lam t r - n=m:=by omega
          rw [this];exact mem_filter.mpr ⟨mem_range.mpr hm,h2⟩
       have hrq : r=q:=by by_contra hne_r;exact znDN hvD hne_r hzr hv'_zq
       subst r;exact ⟨hown,hLE⟩
     . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hv'_zq
       exfalso;rcases hv'_zq with hL' | ⟨hwn,_⟩
       . unfold zLeaves at hL';rcases mem_insert.mp hL' with h1 | himg
         . exact hrc (Fin.ext h1 ▸ hq_cov)
         . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
           obtain ⟨js,_,hbw's,_⟩:=bwS hvD s (mem_filter.mp hs).1
           have:=r.isLt;omega
       . have:=r.isLt;omega
    have hne_zo:=zrNeOr hvD ht
    by_cases hrj : readsJ1 t
    . have hb_reads : n+j1 ∈ (gateAt C (iI j0 j1 jb'2)).inputs:=by
       rcases hrj with ⟨k2,hk2,_⟩ | ⟨_,jb'3,_,hbw3,hmem3⟩
       . rw [hGe] at hk2;simp at hk2
       . have : jb'3=jb'2:=by omega
         subst jb'3;exact hmem3
      have h1 : (gateAt C (iI j0 j1 jb'2)).inputs =
       (gateAt D jb'2).inputs.map (fun w' => if w'=v' then n+j1 else iW n j0 j1 w'):=by
       rcases hin' with h | h
       . exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) h hne_zo).1 hb_reads
       . exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) h hne_zo.symm).1 hb_reads
      rw [h1]
      refine List.map_congr_left fun w' _ => ?_
      simp only [lamMap,hown_lam.1,hown_lam.2,hrj,and_true]
    . have hb_no : n+j1 ∉ (gateAt C (iI j0 j1 jb'2)).inputs :=
       fun h => hrj (Or.inr ⟨hGe,jb'2,hjb',hbw'2,h⟩)
      have h1 : (gateAt C (iI j0 j1 jb'2)).inputs=(gateAt D jb'2).inputs.map (iW n j0 j1):=by
       rcases hin' with h | h
       . exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) h hne_zo).2 hb_no
       . exact (sInD hj01 hinD (fun i hi => (hsub i hi).2.2) h hne_zo.symm).2 hb_no
      rw [h1]
      refine List.map_congr_left fun w' _ => ?_
      simp only [lamMap,hrj,and_false,↓reduceIte]
  . have hno_v : v' ∉ (gateAt D jb'2).inputs:=by
     intro hm;rcases hin' with h | h <;> rw [h] at hm <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
     . rcases hm with h1 | h2;exact hBZV t ht htq h1.symm;exact hvo h2
     . rcases hm with h1 | h2;exact hvo h1;exact hBZV t ht htq h2.symm
    rw [hNVI jb'2 hjb' hno_v]
    refine List.map_congr_left fun w' hw' => ?_
    have hne_w : w'≠v':=fun h => hno_v (h ▸ hw')
    simp only [lamMap,hne_w,false_and,↓reduceIte]
 have htq_reads_j1 : ∀ t_q : Fin n,v'=d1.zroot q->d1.tie q=some t_q->readsJ1 t_q:=by
  intro t_q hvz htieq
  by_contra hno_rj
  have hown_tq : d1.owns t_q q=true:=(hvD.2.2.2.1 q t_q htieq).2
  have htq_cov : t_q ∈ d1.cover:=(hvD.2.2.1.1 t_q q hown_tq).2
  have htq_ne_q : t_q≠q:=(hvD.2.2.1.1 t_q q hown_tq).1.ne
  have hsafe : ∀ w' < n+D.gates.length,
   ((w' < n/\w'≠l.val/\w'≠p.val) ∨
    (n<=w'/\w' - n < D.gates.length ∧
     ((d1.role (w' - n)).1=Kind.top ∨
      (∃ t ∈ d1.cover,t≠q/\d1.role (w' - n)=(Kind.b,t.val)) ∨
      (∃ t ∈ d1.cover,t≠t_q/\d1.role (w' - n)=(Kind.z,t.val)) ∨
      d1.role (w' - n)=(Kind.o,t_q.val)))) →
   wV n C xlp (iW n j0 j1 w')=false:=by
   intro w'
   induction w' using Nat.strong_induction_on with
   | ind w' ih =>
    intro hw'lt hs
    rcases hs with ⟨hwn,hwl,hwp⟩ | ⟨hwn,hj',hkind⟩
    . let wf : Fin n:=⟨w',hwn⟩
      unfold iW;rw [if_pos hwn]
      change wV n C xlp wf.val=false
      have h1 : wf≠l:=fun h => hwl (congrArg Fin.val h)
      have h2 : wf≠p:=fun h => hwp (congrArg Fin.val h)
      rw [wvI];simp [xlp,h1,h2]
    . have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
      unfold iW;rw [if_neg (by omega : ¬ w' < n)]
      rw [wvGR n C hrbC xlp (iI j0 j1 (w' - n)) hlt,(hIF (w' - n) hj').1]
      rcases hkind with htop | ⟨t,ht,htne_q,hb⟩ | ⟨t,ht,htne_tq,hz⟩ | ho
      . have hjT : w' - n ∈ topGates d1 D:=mem_filter.mpr ⟨mem_range.mpr hj',htop⟩
        rw [(hvD.2.2.2.2.2.2.1 (w' - n) hjT).1,hNVI (w' - n) hj' (htop_no_v' (w' - n) hjT)]
        simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
        rintro b ⟨i',hi',hbi'⟩
        have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
        have hf:=ih i' hilt (by omega) (by
         rcases (hvD.2.2.2.2.2.2.1 (w' - n) hjT).2.2 i' hi' with hL | ⟨hin,hG⟩
         . unfold topLeaves at hL;rcases mem_union.mp hL with hA' | hB'
           . obtain ⟨a,haA,rfl⟩:=mem_image.mp hA'
             exact Or.inl ⟨a.isLt,fun h => hlA (Fin.ext h ▸ haA),fun h => hpA (Fin.ext h ▸ haA)⟩
           . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
             obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
             have hsq : s≠q:=fun h => by have ht0:=(mem_filter.mp hsF).2;rw [h,htieq] at ht0;cases ht0
             right;refine ⟨by omega,by omega,Or.inr (Or.inl ⟨s,(mem_filter.mp hsF).1,hsq,?_⟩)⟩
             have : d1.bw s - n=js:=by omega
             rw [this,hrol]
         . exact Or.inr ⟨hin,topGates_lt _ hG,Or.inl (mem_filter.mp hG).2⟩)
        rw [hf] at hbi';subst hbi';decide
      . obtain ⟨jb',hjb',hbw',hrol',hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht).1
        have hjj : w' - n=jb':=by
         rcases hvD.2.2.2.2.1 (w' - n) hj' with htop | ⟨t2,_,hrt2,hrb2⟩
         . rw [hb] at htop;cases htop
         . rw [hb] at hrt2;have ht2 : t2=t:=Fin.ext (by simpa using hrt2.symm)
           subst t2;have:=hrb2 (by rw [hb]);omega
        rw [hjj,hop',hbt_inputs_C t ht htne_q jb' hjb' hbw']
        by_cases httq : t=t_q
        . subst t
          have hor_in_D : d1.oroot t_q ∈ (gateAt D jb').inputs:=by rcases hin' with h | h <;> rw [h] <;> simp
          have hor_lam : lamMap t_q (d1.oroot t_q)=iW n j0 j1 (d1.oroot t_q):=by
           simp only [lamMap,hno_rj,and_false,↓reduceIte]
          have hor_lt : d1.oroot t_q < w':=by have:=(term_roots_lt_bw hvD ht).2;omega
          have hf:=ih (d1.oroot t_q) hor_lt (by omega) (by
           have ho_r:=(hvD.2.2.2.2.2.1 t_q ht).2.2.1.2.2.2
           by_cases hGe : gatesOf d1 D Kind.o t_q.val=∅
           . rw [if_pos hGe] at ho_r
             have hmem_o : d1.lam t_q q ∈ oLeaves d1 t_q :=
              mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_univ _,hown_tq⟩,rfl⟩
             rw [ho_r,mem_singleton] at hmem_o
             have hlq:=(hvD.2.2.2.2.2.1 t_q ht).2.2.2 q hown_tq
             unfold LamOK at hlq;rw [if_pos hq_cov] at hlq
             rw [← hmem_o]
             rcases hlq.2.1 with h1 | ⟨k,hk,h1,h2⟩
             . rw [h1];exact Or.inl ⟨q.isLt,fun h => hql (Fin.ext h),fun h => hpq.symm (Fin.ext h)⟩
             . right;refine ⟨by omega,by omega,Or.inr (Or.inr (Or.inl ⟨q,hq_cov,htq_ne_q.symm,?_⟩))⟩
               have : d1.lam t_q q - n=k:=by omega
               rw [this,h2]
           . rw [if_neg hGe] at ho_r;obtain ⟨k,hk,hkeq⟩:=ho_r
             right;refine ⟨by omega,by have:=gatesOf_lt k hk;omega,Or.inr (Or.inr (Or.inr ?_))⟩
             have : d1.oroot t_q - n=k:=by omega
             rw [this,(mem_filter.mp hk).2])
          simp only [GateOp.eval,List.map_map,List.all_eq_false,List.mem_map,Function.comp_apply]
          exact ⟨false,⟨d1.oroot t_q,hor_in_D,by rw [hor_lam];exact hf⟩,by decide⟩
        . have hzr_in_D : d1.zroot t ∈ (gateAt D jb').inputs:=by rcases hin' with h | h <;> rw [h] <;> simp
          have hzr_lam : lamMap t (d1.zroot t)=iW n j0 j1 (d1.zroot t):=by
           simp only [lamMap,hBZV t ht htne_q,false_and,↓reduceIte]
          have hzr_lt : d1.zroot t < w':=by have:=(term_roots_lt_bw hvD ht).1;omega
          have hf:=ih (d1.zroot t) hzr_lt (by omega) (by
           have hz_r:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
           by_cases hGe : gatesOf d1 D Kind.z t.val=∅
           . rw [if_pos hGe] at hz_r
             have htp : d1.zroot t=t.val:=by
              have : t.val ∈ zLeaves d1 t:=mem_insert_self _ _
              rw [hz_r,mem_singleton] at this;exact this.symm
             rw [htp];exact Or.inl ⟨t.isLt,fun h => hlNC (Fin.ext h ▸ ht),fun h => hpNC (Fin.ext h ▸ ht)⟩
           . rw [if_neg hGe] at hz_r;obtain ⟨k,hk,hkeq⟩:=hz_r
             right;refine ⟨by omega,by have:=gatesOf_lt k hk;omega,Or.inr (Or.inr (Or.inl ⟨t,ht,httq,?_⟩))⟩
             have : d1.zroot t - n=k:=by omega
             rw [this,(mem_filter.mp hk).2])
          simp only [GateOp.eval,List.map_map,List.all_eq_false,List.mem_map,Function.comp_apply]
          exact ⟨false,⟨d1.zroot t,hzr_in_D,by rw [hzr_lam];exact hf⟩,by decide⟩
      . have hjZ : w' - n ∈ gatesOf d1 D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',hz⟩
        have hin_C : (gateAt C (iI j0 j1 (w' - n))).inputs=(gateAt D (w' - n)).inputs.map (iW n j0 j1):=by
         by_cases htq : t=q
         . subst t
           have hno_v : v' ∉ (gateAt D (w' - n)).inputs:=by
            intro hm
            have hr0 : readsIn D (gatesOf d1 D Kind.z q.val) (d1.zroot q)=0:=by
             rcases hv'_zq with hL | ⟨_,hG⟩
             . rw [hvz] at hL;rw [((hvD.2.2.2.2.2.1 q hq_cov).2.1.2.1 _ hL).2,if_pos rfl]
             . have h:=(hvD.2.2.2.2.2.1 q hq_cov).2.1.2.2.1 (v' - n) hG
               have hveq : n+(v' - n)=d1.zroot q:=by omega
               rw [hveq,if_pos rfl] at h;exact h
            have hpos:=(rInP D (gatesOf d1 D Kind.z q.val) (d1.zroot q)).mpr ⟨w' - n,hjZ,hvz ▸ hm⟩
            omega
           exact hNVI (w' - n) hj' hno_v
         . exact hNVI (w' - n) hj' (hzt_no_v' t ht htq (w' - n) hjZ)
        rw [((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ).1,hin_C]
        simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
        rintro b ⟨i',hi',hbi'⟩
        have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
        have hf:=ih i' hilt (by omega) (by
         rcases ((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ).2.2 i' hi' with hL | ⟨hin,hG⟩
         . unfold zLeaves at hL;rcases mem_insert.mp hL with rfl | himg
           . exact Or.inl ⟨t.isLt,fun h => hlNC (Fin.ext h ▸ ht),fun h => hpNC (Fin.ext h ▸ ht)⟩
           . obtain ⟨s,hsF,rfl⟩:=mem_image.mp himg
             obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
             have hsq : s≠q:=fun h => by
              have ht0:=(mem_filter.mp hsF).2;rw [h,htieq] at ht0
              exact htne_tq (Option.some.inj ht0).symm
             right;refine ⟨by omega,by omega,Or.inr (Or.inl ⟨s,(mem_filter.mp hsF).1,hsq,?_⟩)⟩
             have : d1.bw s - n=js:=by omega
             rw [this,hrol]
         . right;exact ⟨hin,gatesOf_lt _ hG,Or.inr (Or.inr (Or.inl ⟨t,ht,htne_tq,(mem_filter.mp hG).2⟩))⟩)
        rw [hf] at hbi';subst hbi';decide
      . have hjO : w' - n ∈ gatesOf d1 D Kind.o t_q.val:=mem_filter.mpr ⟨mem_range.mpr hj',ho⟩
        rw [((hvD.2.2.2.2.2.1 t_q htq_cov).2.2.1.1 (w' - n) hjO).1,hot_inputs_C t_q htq_cov (w' - n) hjO]
        simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
        rintro b ⟨i',hi',hbi'⟩
        have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
        have hlam_i : lamMap t_q i'=iW n j0 j1 i':=by simp only [lamMap,hno_rj,and_false,↓reduceIte]
        have hf:=ih i' hilt (by omega) (by
         rcases ((hvD.2.2.2.2.2.1 t_q htq_cov).2.2.1.1 (w' - n) hjO).2.2 i' hi' with hL | ⟨hin,hG⟩
         . obtain ⟨r,hr,rfl⟩:=mem_image.mp hL
           have hown:=(mem_filter.mp hr).2
           have hadj:=(hvD.2.2.1.1 t_q r hown).1
           have hrne_tq : r≠t_q:=hadj.ne.symm
           have hrne_l : r≠l:=((hK1 t_q r).mp hadj).2.2
           have hrne_p : r≠p:=fun h => by
            rw [h] at hadj
            rcases (hp t_q).mp ((hK1 t_q p).mp hadj).1.symm with h1 | h2
            . exact ((hK1 t_q p).mp hadj).2.1 h1
            . exact htq_ne_q h2
           have hlam:=(hvD.2.2.2.2.2.1 t_q htq_cov).2.2.2 r hown
           unfold LamOK at hlam
           by_cases hrc : r ∈ d1.cover
           . rw [if_pos hrc] at hlam
             rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
             . rw [h1];exact Or.inl ⟨r.isLt,fun h => hrne_l (Fin.ext h),fun h => hrne_p (Fin.ext h)⟩
             . right;refine ⟨by omega,by omega,Or.inr (Or.inr (Or.inl ⟨r,hrc,hrne_tq,?_⟩))⟩
               have : d1.lam t_q r - n=k:=by omega
               rw [this,h2]
           . rw [if_neg hrc] at hlam;rw [hlam]
             exact Or.inl ⟨r.isLt,fun h => hrne_l (Fin.ext h),fun h => hrne_p (Fin.ext h)⟩
         . right;exact ⟨hin,gatesOf_lt _ hG,Or.inr (Or.inr (Or.inr (mem_filter.mp hG).2))⟩)
        rw [hlam_i,hf] at hbi';subst hbi';decide
  have hf:=hsafe D.output hDout_lt (by
   rcases hDout_node with hL | ⟨hin,hG⟩
   . unfold topLeaves at hL;rcases mem_union.mp hL with hA' | hB'
     . obtain ⟨a,haA,h1⟩:=mem_image.mp hA'
       rw [← h1];exact Or.inl ⟨a.isLt,fun h => hlA (Fin.ext h ▸ haA),fun h => hpA (Fin.ext h ▸ haA)⟩
     . obtain ⟨s,hsF,h1⟩:=mem_image.mp hB'
       obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
       have hsq : s≠q:=fun h => by have ht0:=(mem_filter.mp hsF).2;rw [h,htieq] at ht0;cases ht0
       right;refine ⟨by omega,by omega,Or.inr (Or.inl ⟨s,(mem_filter.mp hsF).1,hsq,?_⟩)⟩
       have : D.output - n=js:=by omega
       rw [this,hrol]
   . exact Or.inr ⟨hin,topGates_lt _ hG,Or.inl (mem_filter.mp hG).2⟩)
  rw [← hCE,wvO,hfun,hxlp_K] at hf;cases hf
 have hC_mono : ∀ (x : Fin n->Bool) (w' : ℕ),w' < n+D.gates.length->w'≠l.val →
  wV n D x w'=true->wV n C x (iW n j0 j1 w')=true:=by
  intro x w'
  induction w' using Nat.strong_induction_on with
  | ind w' ih =>
   intro hw'lt hw'l hDt
   by_cases hwn : w' < n
   . let wf : Fin n:=⟨w',hwn⟩
     unfold iW;rw [if_pos hwn]
     change wV n C x wf.val=true
     change wV n D x wf.val=true at hDt
     rw [wvI];rwa [wvI] at hDt
   . have hj' : w' - n < D.gates.length:=by omega
     have hweq : n+(w' - n)=w':=by omega
     have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
     have hne:=invIdx_ne (j':=w' - n) hj01
     obtain ⟨hop,hinD,hsub⟩:=hKF (iI j0 j1 (w' - n)) hlt hne.1 hne.2
     rw [idxMap_invIdx hj01] at hop hinD
     unfold iW;rw [if_neg hwn]
     rw [wvGR n C hrbC x (iI j0 j1 (w' - n)) hlt,hop]
     rw [← hweq,wvGR n D hvD.1 x (w' - n) hj',hinD] at hDt
     have hstep_in : ∀ i ∈ (gateAt C (iI j0 j1 (w' - n))).inputs,
      wV n D x (wM n j0 j1 v' i)=true->wV n C x i=true:=by
      intro i hi hDi
      by_cases hi1 : i=n+j1
      . subst i
        have hwm : wM n j0 j1 v' (n+j1)=v':=by unfold wM;rw [if_neg (by omega),if_pos rfl]
        rw [hwm] at hDi
        rw [hval_j1,hDi];simp
      . have hi0:=(hsub i hi).2.2
        have hi_eq : i=iW n j0 j1 (wM n j0 j1 v' i):=by
         rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨habs,_⟩ | ⟨_,heq⟩
         . exact absurd habs hi1
         . exact heq
        have hilt : wM n j0 j1 v' i < w':=by
         have hmemD : wM n j0 j1 v' i ∈ (gateAt D (w' - n)).inputs:=hinD ▸ List.mem_map.mpr ⟨i,hi,rfl⟩
         have:=hvD.1 (w' - n) hj' _ hmemD;omega
        have hwm_ne_l : wM n j0 j1 v' i≠l.val:=by
         intro hl_eq;have h1:=(hsub i hi).2.1
         rw [hi_eq,hl_eq] at h1;unfold iW at h1;rw [if_pos l.isLt] at h1;exact h1 rfl
        rw [hi_eq]
        exact ih (wM n j0 j1 v' i) hilt (by omega) hwm_ne_l hDi
     rcases valNN hvD (gateAt D (w' - n)) (by rw [gateAt_eq_getElem D _ hj'];exact List.getElem_mem hj') with hand | hor
     . rw [hand] at hDt ⊢
       simp only [GateOp.eval,List.map_map,List.all_eq_true,List.mem_map,Function.comp_apply,id_eq] at hDt ⊢
       intro b ⟨i,hi,hbi⟩;subst hbi
       exact hstep_in i hi (hDt _ ⟨i,hi,rfl⟩)
     . rw [hor] at hDt ⊢
       simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq] at hDt ⊢
       obtain ⟨b,⟨i,hi,hbi⟩,hbt⟩:=hDt
       subst hbt
       exact ⟨true,⟨i,hi,hstep_in i hi hbi⟩,rfl⟩
 have hu'_eq_p : u'=p.val:=by
  rcases huC with hup | ⟨hun,huG⟩
  . exact hup
  . exfalso
    obtain ⟨l1,hl1,l2,hl2,hl12,hr1,hr2⟩ :=
     otGTL hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.2.1 huG
    obtain ⟨r1,hr1f,rfl⟩:=mem_image.mp hl1
    obtain ⟨r2,hr2f,rfl⟩:=mem_image.mp hl2
    have hr12 : r1≠r2:=fun h => hl12 (by rw [h])
    have hueq : n+(u' - n)=u':=by omega
    have hpick : ∃ r',d1.owns q r'=true/\r'≠p/\OrReach n D (gatesOf d1 D Kind.o q.val) u' (d1.lam q r'):=by
     by_cases h : r1=p
     . exact ⟨r2,(mem_filter.mp hr2f).2,fun h2 => hr12 (h.trans h2.symm),by rwa [hueq] at hr2⟩
     . exact ⟨r1,(mem_filter.mp hr1f).2,h,by rwa [hueq] at hr1⟩
    obtain ⟨r',hown,hr'p,hru⟩:=hpick
    have hadj : K1.Adj q r':=(hvD.2.2.1.1 q r' hown).1
    have hKadj : K.Adj q r':=((hK1 q r').mp hadj).1
    have hr'A : r' ∉ A:=fun h => hA r' h q hKadj.symm
    let xlr : Fin n->Bool:=fun i => decide (i=l\/i=r')
    have hxlr_K : graphFun K A xlr=false:=by
     simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
     refine ⟨fun a ha hxa => ?_,fun a b hab hxa hxb => ?_⟩
     . simp only [xlr,decide_eq_true_eq] at hxa;rcases hxa with rfl | rfl;exact hlA ha;exact hr'A ha
     . simp only [xlr,decide_eq_true_eq] at hxa hxb
       rcases hxa with ha | ha <;> rcases hxb with hb | hb
       . rw [ha,hb] at hab;exact hab.ne rfl
       . rw [ha,hb] at hab;exact hr'p ((hl r').mp hab)
       . rw [ha,hb] at hab;exact hr'p ((hl r').mp hab.symm)
       . rw [ha,hb] at hab;exact hab.ne rfl
    have hlam_t : wV n D xlr (d1.lam q r')=true:=lam_true_of_input hvD hq_cov hown xlr (by simp [xlr])
    have hu'_t : wV n D xlr u'=true :=
     otER hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.2.1 xlr hru hlam_t
    have hj1_t : wV n C xlr (n+j1)=true:=by rw [hval_j1,hu'_t];simp [xlr]
    have hprop_zq : ∀ w',OrReach n D (gatesOf d1 D Kind.z q.val) w' v' →
     wV n C xlr (if w'=v' then n+j1 else iW n j0 j1 w')=true:=by
     intro w' hreach
     induction hreach using ReflTransGen.head_induction_on with
     | refl => rw [if_pos rfl];exact hj1_t
     | head hstep hrest ih =>
      obtain ⟨k',hk'Z,rfl,hmem⟩:=hstep
      have hk'lt:=gatesOf_lt k' hk'Z
      have hne_kv : n+k'≠v':=by
       have:=hvD.1 k' hk'lt _ hmem;have:=orLe hvD.1 gatesOf_lt hrest;omega
      rw [if_neg hne_kv];unfold iW;rw [if_neg (by omega)]
      have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
      have hsub_eq : n+k' - n=k':=by omega
      rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 k') hlt,
       (hIF k' hk'lt).1,((hvD.2.2.2.2.2.1 q hq_cov).2.1.1 k' hk'Z).1,hzq_slot_C k' hk'Z]
      simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq]
      exact ⟨true,⟨_,hmem,ih⟩,rfl⟩
    have hzqRt : wV n C xlr (if d1.zroot q=v' then n+j1 else iW n j0 j1 (d1.zroot q))=true :=
     hprop_zq (d1.zroot q) (otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.1 hv'_zq)
    have hoq_D_t : wV n D xlr (d1.oroot q)=true :=
     otER hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.2.1 xlr
      (otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 q hq_cov).2.2.1
       (Or.inl (mem_image.mpr ⟨r',mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩))) hlam_t
    have hoq_lt : d1.oroot q < n+D.gates.length:=by
     obtain ⟨jbq,hjbq,hbwq,_⟩:=bwS hvD q hq_cov
     have:=(term_roots_lt_bw hvD hq_cov).2;omega
    have hoq_ne_l : d1.oroot q≠l.val:=by
     intro h
     have ho:=(hvD.2.2.2.2.2.1 q hq_cov).2.2.1.2.2.2
     by_cases hGe : gatesOf d1 D Kind.o q.val=∅
     . rw [if_pos hGe] at ho
       have hlmem : d1.lam q r' ∈ oLeaves d1 q :=
        mem_image.mpr ⟨r',mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩
       rw [ho,mem_singleton] at hlmem
       have hl:=(hvD.2.2.2.2.2.1 q hq_cov).2.2.2 r' hown;unfold LamOK at hl
       by_cases hrc : r' ∈ d1.cover
       . rw [if_pos hrc] at hl
         rcases hl.2.1 with h1 | ⟨k,_,h1,_⟩
         . exact ((hK1 q r').mp hadj).2.2 (Fin.ext (by omega))
         . have:=l.isLt;omega
       . rw [if_neg hrc] at hl;exact ((hK1 q r').mp hadj).2.2 (Fin.ext (by omega))
     . rw [if_neg hGe] at ho;obtain ⟨k,_,hkeq⟩:=ho;have:=l.isLt;omega
    have hoq_C_t : wV n C xlr (iW n j0 j1 (d1.oroot q))=true :=
     hC_mono xlr (d1.oroot q) hoq_lt hoq_ne_l hoq_D_t
    have hbq_C_t : wV n C xlr (iW n j0 j1 (d1.bw q))=true:=by
     obtain ⟨jbq,hjbq,hbwq,_,hopq,hinq⟩:=(hvD.2.2.2.2.2.1 q hq_cov).1
     rw [hbwq];unfold iW;rw [if_neg (by omega)]
     have hsub_eq : n+jbq - n=jbq:=by omega
     have hlt:=invIdx_lt hj01 hj1 (by omega : jbq+2 < C.gates.length)
     rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 jbq) hlt,
      (hIF jbq hjbq).1,hopq,hbq_slot_C jbq hjbq hbwq]
     rcases hinq with h | h <;> rw [h] <;>
      simp [GateOp.eval,hzqRt,if_neg hBOV,hoq_C_t]
    have hchain : ∀ m : ℕ,∀ t ∈ d1.cover,n+D.gates.length - d1.bw t=m →
     d1.bw q<=d1.bw t->wV n C xlr (iW n j0 j1 (d1.bw t))=true →
     wV n C xlr C.output=true:=by
     intro m
     induction m using Nat.strong_induction_on with
     | ind m ih =>
      intro t ht hm hge hbt_t
      cases htie : d1.tie t with
      | none =>
       have hreach_out:=otRR hvD.1 topGates_lt hvD.2.2.2.2.2.2
        (Or.inl (mem_union_right _ (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,htie⟩,rfl⟩)))
       have hprop_top : ∀ w',OrReach n D (topGates d1 D) w' (d1.bw t) →
        wV n C xlr (iW n j0 j1 w')=true:=by
        intro w' hr
        induction hr using ReflTransGen.head_induction_on with
        | refl => exact hbt_t
        | head hstep _ ihp =>
         obtain ⟨k',hk'T,rfl,hmem⟩:=hstep
         have hk'lt:=topGates_lt k' hk'T
         have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
         unfold iW;rw [if_neg (by omega)]
         have hsub_eq : n+k' - n=k':=by omega
         rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 k') hlt,
          (hIF k' hk'lt).1,(hvD.2.2.2.2.2.2.1 k' hk'T).1,
          hNVI k' hk'lt (htop_no_v' k' hk'T)]
         simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq]
         exact ⟨true,⟨_,hmem,ihp⟩,rfl⟩
       rw [hCE];exact hprop_top D.output hreach_out
      | some b =>
       have hown_bt : d1.owns b t=true:=(hvD.2.2.2.1 t b htie).2
       have hb_cov : b ∈ d1.cover:=(hvD.2.2.1.1 b t hown_bt).2
       have hlt_bw : d1.bw t < d1.bw b:=bw_tie_lt hvD htie
       have hbq_ne : b≠q:=fun h => by rw [h] at hlt_bw;omega
       have hzb_t : wV n C xlr (iW n j0 j1 (d1.zroot b))=true:=by
        have hr:=otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 b hb_cov).2.1
         (Or.inl (mem_insert_of_mem (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,htie⟩,rfl⟩)))
        have hprop : ∀ w',OrReach n D (gatesOf d1 D Kind.z b.val) w' (d1.bw t) →
         wV n C xlr (iW n j0 j1 w')=true:=by
         intro w' hr'
         induction hr' using ReflTransGen.head_induction_on with
         | refl => exact hbt_t
         | head hstep _ ihp =>
          obtain ⟨k',hk'Z,rfl,hmem⟩:=hstep
          have hk'lt:=gatesOf_lt k' hk'Z
          have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
          unfold iW;rw [if_neg (by omega)]
          have hsub_eq : n+k' - n=k':=by omega
          rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 k') hlt,
           (hIF k' hk'lt).1,((hvD.2.2.2.2.2.1 b hb_cov).2.1.1 k' hk'Z).1,
           hNVI k' hk'lt (hzt_no_v' b hb_cov hbq_ne k' hk'Z)]
          simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq]
          exact ⟨true,⟨_,hmem,ihp⟩,rfl⟩
        exact hprop (d1.zroot b) hr
       have hlam_eq_zr : d1.lam b t=d1.zroot t:=by
        have hl:=(hvD.2.2.2.2.2.1 b hb_cov).2.2.2 t hown_bt
        unfold LamOK at hl;rw [if_pos ht] at hl;exact hl.2.2 htie
       have hlam_bt_t : wV n C xlr (lamMap b (d1.lam b t))=true:=by
        by_cases htq_v : t=q/\d1.zroot q=v'
        . rcases htq_v with ⟨htq,hzr_v⟩;subst t
          have hrj : readsJ1 b:=htq_reads_j1 b hzr_v.symm htie
          have hlam_v : d1.lam b q=v':=hlam_eq_zr.trans hzr_v
          simp only [lamMap,hlam_v,hown_bt,hrj,and_true,↓reduceIte]
          exact hj1_t
        . have hne_v : d1.lam b t≠v':=by
           rw [hlam_eq_zr]
           by_cases htq : t=q
           . subst t;exact fun h => htq_v ⟨rfl,h⟩
           . exact hBZV t ht htq
          have hlam_simp : lamMap b (d1.lam b t)=iW n j0 j1 (d1.zroot t):=by
           unfold lamMap;rw [if_neg (fun h => hne_v h.1),hlam_eq_zr]
          rw [hlam_simp]
          by_cases htq : t=q
          . subst t
            have hne_v' : d1.zroot q≠v':=fun h => htq_v ⟨rfl,h⟩
            rwa [if_neg hne_v'] at hzqRt
          . obtain ⟨jbt,hjbt,hbwt,_,hopt,hint⟩:=(hvD.2.2.2.2.2.1 t ht).1
            rw [hbwt] at hbt_t;unfold iW at hbt_t;rw [if_neg (by omega)] at hbt_t
            have hsub_eq : n+jbt - n=jbt:=by omega
            have hlt:=invIdx_lt hj01 hj1 (by omega : jbt+2 < C.gates.length)
            rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 jbt) hlt,
             (hIF jbt hjbt).1,hopt,hbt_inputs_C t ht htq jbt hjbt hbwt] at hbt_t
            have hzr_lam : lamMap t (d1.zroot t)=iW n j0 j1 (d1.zroot t):=by
             simp only [lamMap,hBZV t ht htq,false_and,↓reduceIte]
            rcases hint with h | h <;> rw [h] at hbt_t <;> simp [GateOp.eval,hzr_lam] at hbt_t
            . exact hbt_t.1
            . exact hbt_t.2
       have hob_t : wV n C xlr (lamMap b (d1.oroot b))=true:=by
        have hr:=otRR hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 b hb_cov).2.2.1
         (Or.inl (mem_image.mpr ⟨t,mem_filter.mpr ⟨mem_univ _,hown_bt⟩,rfl⟩))
        have hprop : ∀ w',OrReach n D (gatesOf d1 D Kind.o b.val) w' (d1.lam b t) →
         wV n C xlr (lamMap b w')=true:=by
         intro w' hr'
         induction hr' using ReflTransGen.head_induction_on with
         | refl => exact hlam_bt_t
         | head hstep _ ihp =>
          obtain ⟨k',hk'O,rfl,hmem⟩:=hstep
          have hk'lt:=gatesOf_lt k' hk'O
          have hne_kv : n+k'≠v':=by
           intro heq
           rcases hv'_zq with hL | ⟨_,hZ⟩
           . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
             . have:=q.isLt;omega
             . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
               obtain ⟨js,_,hbw's,hrol⟩:=bwS hvD s (mem_filter.mp hs).1
               have h1:=(mem_filter.mp hk'O).2
               have : k'=js:=by omega
               rw [this,hrol] at h1;cases h1
           . have h1:=(mem_filter.mp hk'O).2;have h2:=(mem_filter.mp hZ).2
             have : v' - n=k':=by omega
             rw [this,h1] at h2;cases h2
          simp only [lamMap,hne_kv,false_and,↓reduceIte]
          have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
          unfold iW;rw [if_neg (by omega)]
          have hsub_eq : n+k' - n=k':=by omega
          rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 k') hlt,
           (hIF k' hk'lt).1,((hvD.2.2.2.2.2.1 b hb_cov).2.2.1.1 k' hk'O).1,
           hot_inputs_C b hb_cov k' hk'O]
          simp only [GateOp.eval,List.map_map,List.any_eq_true,List.mem_map,Function.comp_apply,id_eq]
          exact ⟨true,⟨_,hmem,ihp⟩,rfl⟩
        exact hprop (d1.oroot b) hr
       have hbb_t : wV n C xlr (iW n j0 j1 (d1.bw b))=true:=by
        obtain ⟨jbb,hjbb,hbwb,_,hopb,hinb⟩:=(hvD.2.2.2.2.2.1 b hb_cov).1
        rw [hbwb];unfold iW;rw [if_neg (by omega)]
        have hsub_eq : n+jbb - n=jbb:=by omega
        have hlt:=invIdx_lt hj01 hj1 (by omega : jbb+2 < C.gates.length)
        rw [hsub_eq,wvGR n C hrbC xlr (iI j0 j1 jbb) hlt,
         (hIF jbb hjbb).1,hopb,hbt_inputs_C b hb_cov hbq_ne jbb hjbb hbwb]
        have hzb_lam : lamMap b (d1.zroot b)=iW n j0 j1 (d1.zroot b):=by
         simp only [lamMap,hBZV b hb_cov hbq_ne,false_and,↓reduceIte]
        rcases hinb with h | h <;> rw [h] <;> simp [GateOp.eval,hzb_lam,hzb_t,hob_t]
       have hbw_b_lt : d1.bw b < n+D.gates.length:=by
        obtain ⟨jbb,hjbb,hbwb,_⟩:=bwS hvD b hb_cov;omega
       exact ih (n+D.gates.length - d1.bw b) (by omega) b hb_cov rfl (by omega) hbb_t
    have hCout_t:=hchain (n+D.gates.length - d1.bw q) q hq_cov rfl le_rfl hbq_C_t
    rw [wvO,hfun,hxlr_K] at hCout_t;cases hCout_t
 have hu_eq_p : u=p.val:=by rw [hu_eq,hu'_eq_p];unfold iW;rw [if_pos p.isLt]
 let d : NCCData n:={
  cover:=insert p d1.cover
  owns:=fun a b => if a=p/\b=l then true else d1.owns a b
  tie:=fun a => if a=p then some q else d1.tie a
  role:=fun j =>
   if j=j0 then (Kind.b,p.val)
   else if j=j1 then (Kind.z,q.val)
   else d1.role (iM j0 j1 j)
  bw:=fun a => if a=p then n+j0 else iW n j0 j1 (d1.bw a)
  zroot:=fun a =>
   if a=p then p.val
   else if a=q then (if d1.zroot q=v' then n+j1 else iW n j0 j1 (d1.zroot q))
   else iW n j0 j1 (d1.zroot a)
  oroot:=fun a => if a=p then l.val else lamMap a (d1.oroot a)
  lam:=fun a b => if a=p then l.val else lamMap a (d1.lam a b)
 }
 have hRS : ∀ j' < D.gates.length,d.role (iI j0 j1 j')=d1.role j':=by
  intro j' _
  have hne:=invIdx_ne (j':=j') hj01
  simp only [d,if_neg hne.1,if_neg hne.2,idxMap_invIdx hj01]
 have hgatesOf_nonZq : ∀ t ∈ d1.cover,∀ k : Kind,¬ (k=Kind.z/\t=q) →
  gatesOf d C k t.val=(gatesOf d1 D k t.val).image (iI j0 j1):=by
  intro t ht k hnotZq
  have htp : t≠p:=fun h => hpNC (h ▸ ht)
  ext j;simp only [gatesOf,mem_filter,mem_range,mem_image]
  constructor
  . rintro ⟨hj,hr⟩
    have h0 : j≠j0:=fun h => by rw [h] at hr;simp only [d,↓reduceIte] at hr;exact htp (Fin.ext (Prod.ext_iff.mp hr).2).symm
    have h1 : j≠j1:=fun h => by
     rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),↓reduceIte] at hr
     exact hnotZq ⟨(Prod.ext_iff.mp hr).1.symm,Fin.ext (Prod.ext_iff.mp hr).2.symm⟩
    have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
    simp only [d,if_neg h0,if_neg h1] at hr
    exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
  . rintro ⟨j',⟨hj',hr'⟩,rfl⟩
    exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj',hr']⟩
 have hlift_zq_below : ∀ w',OrReach n D (gatesOf d1 D Kind.z q.val) w' q.val->w'<=v' →
  OrReach n C (insert j1 ((gatesOf d1 D Kind.z q.val).image (iI j0 j1))) (iW n j0 j1 w') q.val:=by
  intro w' hr hle
  induction hr using ReflTransGen.head_induction_on with
  | refl => unfold iW;rw [if_pos q.isLt];exact ReflTransGen.refl
  | @head a b hstep hrest ih =>
   obtain ⟨k',hk'Z,rfl,hmem⟩:=hstep
   have hk'lt:=gatesOf_lt k' hk'Z
   have hilt : b < n+k':=hvD.1 k' hk'lt b hmem
   have hno_v : v' ∉ (gateAt D k').inputs:=fun hm => by have:=hvD.1 k' hk'lt v' hm;omega
   have hstepC : OrStep n C (insert j1 ((gatesOf d1 D Kind.z q.val).image (iI j0 j1)))
    (iW n j0 j1 (n+k')) (iW n j0 j1 b):=by
    refine ⟨iI j0 j1 k',mem_insert_of_mem (mem_image.mpr ⟨k',hk'Z,rfl⟩),
     by unfold iW;rw [if_neg (by omega)];simp,?_⟩
    rw [hNVI k' hk'lt hno_v];exact List.mem_map.mpr ⟨b,hmem,rfl⟩
   exact ReflTransGen.head hstepC (ih (by omega))
 have hzq_gates_C : gatesOf d C Kind.z q.val=insert j1 ((gatesOf d1 D Kind.z q.val).image (iI j0 j1)):=by
  ext j;simp only [gatesOf,mem_filter,mem_range,mem_insert,mem_image]
  constructor
  . rintro ⟨hj,hr⟩
    by_cases h1 : j=j1
    . exact Or.inl h1
    . right
      have h0 : j≠j0:=fun h => by rw [h] at hr;simp only [d,↓reduceIte] at hr;exact hpq (Fin.ext (Prod.ext_iff.mp hr).2)
      simp only [d,if_neg h0,if_neg h1] at hr
      have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
      exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
  . rintro (h1 | ⟨j',⟨hj',hr'⟩,rfl⟩)
    . subst j;exact ⟨hj1,by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte]⟩
    . exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj',hr']⟩
 refine ⟨d,hrbC,hMCP,?_,?_,?_,?_,?_⟩
 ·
  refine ⟨?_,?_⟩
  . intro a b hown;simp only [d] at hown
    split_ifs at hown with h
    . rcases h with ⟨hap,hbl⟩;subst a;subst b;exact ⟨hLPA.symm,mem_insert_self _ _⟩
    . have h2:=hvD.2.2.1.1 a b hown
      exact ⟨((hK1 a b).mp h2.1).1,mem_insert_of_mem h2.2⟩
  . intro a b hab;simp only [d]
    by_cases hal : a=l
    . subst a;have hbp : b=p:=(hl b).mp hab;subst b
      have hnot : d1.owns l p=false:=by
       cases h : d1.owns l p;rfl;exfalso;exact hlNC (hvD.2.2.1.1 l p h).2
      simp [hlp,hnot]
    . by_cases hbl : b=l
      . subst b;have hap : a=p:=(hl a).mp hab.symm;subst a
        have hnot : d1.owns l p=false:=by
         cases h : d1.owns l p;rfl;exfalso;exact hlNC (hvD.2.2.1.1 l p h).2
        simp [hlp,hnot]
      . simp only [hal,hbl,and_false,↓reduceIte]
        exact hvD.2.2.1.2 a b ((hK1 a b).mpr ⟨hab,hal,hbl⟩)
 ·
  intro a b htie;simp only [d] at htie
  by_cases hap : a=p
  . subst a;rw [if_pos rfl] at htie;cases htie
    exact ⟨mem_insert_self _ _,by simp [d,hpq.symm,hq_owns_p]⟩
  . rw [if_neg hap] at htie
    have h2:=hvD.2.2.2.1 a b htie
    refine ⟨mem_insert_of_mem h2.1,?_⟩
    simp only [d];split_ifs;rfl;exact h2.2
 ·
  intro j hj
  by_cases h0 : j=j0
  . subst j;right;exact ⟨p,mem_insert_self _ _,by simp [d],fun _ => by simp [d]⟩
  . by_cases h1 : j=j1
    . subst j;right;exact ⟨q,mem_insert_of_mem hq_cov,by simp [d,h0],fun h => by simp [d,h0] at h⟩
    . have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
      have hrole_eq : d.role j=d1.role (iM j0 j1 j):=by simp [d,h0,h1]
      rw [hrole_eq]
      rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨t,ht,hrt,hrb⟩
      . exact Or.inl htop
      . right
        have htp : t≠p:=fun h => hpNC (h ▸ ht)
        refine ⟨t,mem_insert_of_mem ht,hrt,fun hb => ?_⟩
        simp only [d,if_neg htp];rw [hrb hb]
        unfold iW;rw [if_neg (by omega)]
        have : n+iM j0 j1 j - n=iM j0 j1 j:=by omega
        rw [this,invIdx_idxMap hj01 h0 h1]
 ·
  intro t ht
  rcases mem_insert.mp ht with htp | ht'
  . subst t
    have hz_gates_p : gatesOf d C Kind.z p.val=∅:=by
     ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
     intro hj hr
     by_cases h0 : j=j0
     . subst j;simp [d] at hr
     . by_cases h1 : j=j1
       . subst j;simp [d,h0] at hr;exact hpq (Fin.ext hr.symm)
       . simp only [d,if_neg h0,if_neg h1] at hr
         have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
         rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
         . rw [hr] at htop;cases htop
         . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
    have ho_gates_p : gatesOf d C Kind.o p.val=∅:=by
     ext j;simp only [gatesOf,mem_filter,mem_range,notMem_empty,iff_false,not_and]
     intro hj hr
     by_cases h0 : j=j0
     . subst j;simp [d] at hr
     . by_cases h1 : j=j1
       . subst j;simp [d,h0] at hr
       . simp only [d,if_neg h0,if_neg h1] at hr
         have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
         rcases hvD.2.2.2.2.1 (iM j0 j1 j) hIL with htop | ⟨s,hs,h2,_⟩
         . rw [hr] at htop;cases htop
         . rw [hr] at h2;exact absurd (Fin.ext h2.symm ▸ hs) hpNC
    have hZLP : zLeaves d p={p.val}:=by
     ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,mem_singleton,d]
     constructor
     . rintro (rfl | ⟨a,⟨_,htie⟩,_⟩);rfl
       by_cases hap : a=p
       . rw [if_pos hap] at htie;exact absurd (Option.some.inj htie) hpq.symm
       . rw [if_neg hap] at htie;exact absurd (hvD.2.2.1.1 p a (hvD.2.2.2.1 a p htie).2).2 hpNC
     . rintro rfl;exact Or.inl rfl
    have hOLP : oLeaves d p={l.val}:=by
     ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,mem_singleton,d]
     constructor
     . rintro ⟨r,_,rfl⟩;simp
     . rintro rfl;exact ⟨l,by simp,by simp⟩
    refine ⟨⟨j0,by omega,by simp [d],by simp [d],hop0,
     by simp only [d,↓reduceIte];rw [hu_eq_p] at huin;rcases huin with h | h;exact Or.inr h;exact Or.inl h⟩,
     ?_,?_,?_⟩
    . rw [hz_gates_p,hZLP];simp [IsOrTree,readsIn,d]
    . rw [ho_gates_p,hOLP];simp [IsOrTree,readsIn,d]
    . intro r hown;simp only [d] at hown
      by_cases hrl : r=l
      . subst r;unfold LamOK
        have hl_nc : l ∉ d.cover:=by simp only [d,mem_insert,not_or];exact ⟨hlp,hlNC⟩
        rw [if_neg hl_nc];simp [d]
      . simp only [hrl,and_false,↓reduceIte] at hown
        exact absurd (hvD.2.2.1.1 p r hown).2 hpNC
  ·
   have htp : t≠p:=fun h => hpNC (h ▸ ht')
   obtain ⟨j',hj',hbw',hrol',hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht').1
   have hterm_t : TermOK n C d t:=by
    refine ⟨iI j0 j1 j',invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
     by simp only [d,if_neg htp,hbw'];unfold iW;rw [if_neg (by omega)];simp,
     by rw [hRS j' hj',hrol'],
     by rw [(hIF j' hj').1,hop'],?_⟩
    by_cases htq : t=q
    . subst t
      have hin_C:=hbq_slot_C j' hj' hbw'
      have hlam_oq : lamMap q (d1.oroot q)=iW n j0 j1 (d1.oroot q):=by
       simp only [lamMap,hBOV,false_and,↓reduceIte]
      simp only [d,if_neg htp,↓reduceIte,hlam_oq]
      rcases hin' with h | h
      . left;rw [hin_C,h];simp [if_neg hBOV]
      . right;rw [hin_C,h];simp [if_neg hBOV]
    . have hin_C:=hbt_inputs_C t ht' htq j' hj' hbw'
      have hzr_lam : lamMap t (d1.zroot t)=iW n j0 j1 (d1.zroot t):=by
       simp only [lamMap,hBZV t ht' htq,false_and,↓reduceIte]
      simp only [d,if_neg htp,if_neg htq]
      rcases hin' with h | h
      . left;rw [hin_C,h];simp [hzr_lam]
      . right;rw [hin_C,h];simp [hzr_lam]
   have hz_t : IsOrTree n C (gatesOf d C Kind.z t.val) (zLeaves d t) (d.zroot t):=by
    by_cases htq : t=q
    . subst t
      have hLeq : zLeaves d q=insert (n+j0) ((zLeaves d1 q).image (iW n j0 j1)):=by
       ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,d]
       constructor
       . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
         . right;exact ⟨q.val,Or.inl rfl,by unfold iW;rw [if_pos q.isLt]⟩
         . by_cases hap : a=p
           . subst a;left;simp
           . right;rw [if_neg hap] at htie ⊢
             have ha' : a ∈ d1.cover:=by rcases ha with rfl | h;exact absurd rfl hap;exact h
             exact ⟨d1.bw a,Or.inr ⟨a,⟨ha',htie⟩,rfl⟩,rfl⟩
       . rintro (rfl | ⟨w',hw',rfl⟩)
         . right;exact ⟨p,⟨Or.inl rfl,by simp⟩,by simp⟩
         . rcases hw' with rfl | ⟨a,⟨ha',htie⟩,rfl⟩
           . left;unfold iW;rw [if_pos q.isLt]
           . right;have hap : a≠p:=fun h => hpNC (h ▸ ha')
             exact ⟨a,⟨Or.inr ha',by simp [hap,htie]⟩,by simp [hap]⟩
      rw [hzq_gates_C,hLeq];simp only [d,if_neg htp,↓reduceIte]
      exact otLIn (hvD.2.2.2.2.2.1 q hq_cov).2.1 hv'_zq (iI j0 j1) (iW n j0 j1)
       (fun _ _ _ _ h => invIdx_inj hj01 h)
       (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
       (fun a b _ _ h => invWire_inj hj01 h)
       (fun a _ => (invWire_ne_j0_j1 (w':=a) hj01).2)
       (fun a _ => (invWire_ne_j0_j1 (w':=a) hj01).1)
       (by omega) hop1 (hv_eq ▸ hvin)
       (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
       (fun j' hj' => hzq_slot_C j' hj')
    . rw [hgatesOf_nonZq t ht' Kind.z (fun h => htq h.2)]
      have hLeq : zLeaves d t=(zLeaves d1 t).image (iW n j0 j1):=by
       ext x;simp only [zLeaves,mem_insert,mem_image,mem_filter,d]
       constructor
       . rintro (rfl | ⟨a,⟨ha,htie⟩,rfl⟩)
         . exact ⟨t.val,Or.inl rfl,by unfold iW;rw [if_pos t.isLt]⟩
         . by_cases hap : a=p
           . rw [if_pos hap] at htie;exact absurd (Option.some.inj htie) (Ne.symm htq)
           . rw [if_neg hap] at htie
             have ha' : a ∈ d1.cover:=by rcases ha with rfl | h;exact absurd rfl hap;exact h
             exact ⟨d1.bw a,Or.inr ⟨a,⟨ha',htie⟩,rfl⟩,by simp [hap]⟩
       . rintro ⟨w',hw',rfl⟩
         rcases hw' with rfl | ⟨a,⟨ha',htie⟩,rfl⟩
         . left;unfold iW;rw [if_pos t.isLt]
         . right;have hap : a≠p:=fun h => hpNC (h ▸ ha')
           exact ⟨a,⟨Or.inr ha',by simp [hap,htie]⟩,by simp [hap]⟩
      rw [hLeq];simp only [d,if_neg htp,if_neg htq]
      exact otLI (hvD.2.2.2.2.2.1 t ht').2.1 (iI j0 j1) (iW n j0 j1)
       (fun _ _ _ _ h => invIdx_inj hj01 h)
       (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
       (fun a b _ _ h => invWire_inj hj01 h)
       (fun j' hj' => (hIF j' (gatesOf_lt j' hj')).1)
       (fun j' hj' => hNVI j' (gatesOf_lt j' hj') (hzt_no_v' t ht' htq j' hj'))
   have ho_t : IsOrTree n C (gatesOf d C Kind.o t.val) (oLeaves d t) (d.oroot t):=by
    rw [hgatesOf_nonZq t ht' Kind.o (fun h => by cases h.1)]
    have hLeq : oLeaves d t=(oLeaves d1 t).image (lamMap t):=by
     ext x;simp only [oLeaves,mem_image,mem_filter,mem_univ,true_and,d,htp,false_and,↓reduceIte]
     constructor
     . rintro ⟨r,hr,rfl⟩;exact ⟨d1.lam t r,⟨r,hr,rfl⟩,rfl⟩
     . rintro ⟨_,⟨r,hr,rfl⟩,rfl⟩;exact ⟨r,hr,rfl⟩
    rw [hLeq];simp only [d,if_neg htp]
    exact otLI (hvD.2.2.2.2.2.1 t ht').2.2.1 (iI j0 j1) (lamMap t)
     (fun _ _ _ _ h => invIdx_inj hj01 h)
     (fun k' hk' => by
      have hne_kv : n+k'≠v':=by
       intro heq
       rcases hv'_zq with hL | ⟨_,hZ⟩
       . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
         . have:=q.isLt;omega
         . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
           obtain ⟨js,_,hbw's,hrol⟩:=bwS hvD s (mem_filter.mp hs).1
           have h1:=(mem_filter.mp hk').2;have : k'=js:=by omega
           rw [this,hrol] at h1;cases h1
       . have h1:=(mem_filter.mp hk').2;have h2:=(mem_filter.mp hZ).2
         have : v' - n=k':=by omega
         rw [this,h1] at h2;cases h2
      simp only [lamMap,hne_kv,false_and,↓reduceIte];unfold iW;rw [if_neg (by omega)];simp)
     (fun a b _ _ heq => by
      unfold lamMap at heq
      by_cases ha : a=v'/\d1.owns t q=true/\d1.lam t q=v'/\readsJ1 t <;>
      by_cases hb : b=v'/\d1.owns t q=true/\d1.lam t q=v'/\readsJ1 t
      . exact ha.1.trans hb.1.symm
      . rw [if_pos ha,if_neg hb] at heq;exact absurd heq.symm (invWire_ne_j0_j1 (w':=b) hj01).2
      . rw [if_neg ha,if_pos hb] at heq;exact absurd heq (invWire_ne_j0_j1 (w':=a) hj01).2
      . rw [if_neg ha,if_neg hb] at heq;exact invWire_inj hj01 heq)
     (fun k' hk' => (hIF k' (gatesOf_lt k' hk')).1)
     (fun k' hk' => hot_inputs_C t ht' k' hk')
   have hlam_t : ∀ r,d.owns t r=true->LamOK n C d t r:=by
    intro r hown;simp only [d,htp,false_and,↓reduceIte] at hown
    have hl':=(hvD.2.2.2.2.2.1 t ht').2.2.2 r hown
    unfold LamOK at hl' ⊢
    by_cases hrp : r=p
    . subst r
      rw [if_neg hpNC] at hl'
      rw [if_pos (mem_insert_self _ _)]
      have hp_ne_v : p.val≠v':=by
       intro h;rw [← h] at hv'_zq
       rcases hv'_zq with hL | ⟨hpn,_⟩
       . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
         . exact hpq (Fin.ext h1)
         . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
           obtain ⟨js,_,hbw's,_⟩:=bwS hvD s (mem_filter.mp hs).1
           have:=p.isLt;omega
       . have:=p.isLt;omega
      have hlam_d : d.lam t p=p.val:=by
       simp only [d,if_neg htp,hl',lamMap,hp_ne_v,false_and,↓reduceIte]
       unfold iW;rw [if_pos p.isLt]
      rw [hlam_d]
      exact ⟨(isCentred_input n C d p).mpr (mem_insert_self _ _),Or.inl rfl,fun _ => by simp [d]⟩
    . have hRCI : r ∈ d.cover↔r ∈ d1.cover:=by simp [d,hrp]
      by_cases hrc : r ∈ d1.cover
      . rw [if_pos hrc] at hl';rw [if_pos (hRCI.mpr hrc)]
        by_cases hrq_v : r=q/\d1.lam t q=v'
        . rcases hrq_v with ⟨hrq,hlam_v⟩;subst r
          have hRZ : OrReach n D (gatesOf d1 D Kind.z q.val) v' q.val :=
           hlam_v ▸ (icZIR hvD hq_cov hl'.2.1).mp hl'.1
          have hreach_inv:=hlift_zq_below v' hRZ le_rfl
          have hGz_q : ∀ j ∈ insert j1 ((gatesOf d1 D Kind.z q.val).image (iI j0 j1)),
           j < C.gates.length/\(d.role j).1=Kind.z:=by
           intro j hj;rcases mem_insert.mp hj with hj1_eq | himg
           . subst j;exact ⟨hj1,by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte]⟩
           . obtain ⟨k',hk',rfl⟩:=mem_image.mp himg
             have hk'lt:=gatesOf_lt k' hk'
             exact ⟨invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length),
              by rw [hRS k' hk'lt,(mem_filter.mp hk').2]⟩
          by_cases hrj : readsJ1 t
          . have hlam_d : d.lam t q=n+j1:=by
             simp only [d,if_neg htp,lamMap,hlam_v,hown,hrj,and_true,↓reduceIte]
            rw [hlam_d]
            refine ⟨?_,Or.inr ⟨j1,hj1,rfl,by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte]⟩,?_⟩
            . have hstep_j1 : OrStep n C (insert j1 ((gatesOf d1 D Kind.z q.val).image (iI j0 j1)))
                (n+j1) (iW n j0 j1 v') :=
               ⟨j1,mem_insert_self _ _,rfl,by rw [← hv_eq];rcases hvin with h | h <;> rw [h] <;> simp⟩
              exact icORZ hrbC (mem_insert_of_mem hq_cov) hGz_q
               (ReflTransGen.head hstep_j1 hreach_inv)
            . intro htie;simp only [d,if_neg hrp] at htie
              have hvz : v'=d1.zroot q:=hlam_v.symm.trans (hl'.2.2 htie)
              simp only [d,if_neg hrp,↓reduceIte,hvz.symm]
          . have hlam_d : d.lam t q=iW n j0 j1 v':=by
             simp only [d,if_neg htp,lamMap,hlam_v,hrj,and_false,↓reduceIte]
            rw [hlam_d]
            refine ⟨icORZ hrbC (mem_insert_of_mem hq_cov) hGz_q hreach_inv,?_,?_⟩
            . rw [hlam_v] at hl'
              rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
              . left;rw [h1];unfold iW;rw [if_pos q.isLt]
              . right;exact ⟨iI j0 j1 k,invIdx_lt hj01 hj1 (by omega : k+2 < C.gates.length),
                 by rw [h1];unfold iW;rw [if_neg (by omega)];simp,
                 by rw [hRS k hk,h2]⟩
            . intro htie;simp only [d,if_neg hrp] at htie
              have hvz : v'=d1.zroot q:=hlam_v.symm.trans (hl'.2.2 htie)
              exact absurd (htq_reads_j1 t hvz htie) hrj
        . have hlam_ne_v : d1.lam t r≠v':=by
           intro heq
           by_cases hrq : r=q
           . exact hrq_v ⟨hrq,hrq ▸ heq⟩
           . have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
              rw [← heq]
              rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
              . left;rw [h1];exact mem_insert_self _ _
              . right;refine ⟨by omega,?_⟩
                have : d1.lam t r - n=k:=by omega
                rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
             exact znDN hvD hrq hzr hv'_zq
          have hlam_d : d.lam t r=iW n j0 j1 (d1.lam t r):=by
           simp only [d,if_neg htp,lamMap,hlam_ne_v,false_and,↓reduceIte]
          rw [hlam_d]
          have hRZ:=(icZIR hvD hrc hl'.2.1).mp hl'.1
          have hinv_r : iW n j0 j1 r.val=r.val:=by unfold iW;rw [if_pos r.isLt]
          refine ⟨?_,?_,?_⟩
          . by_cases hrq : r=q
            . subst r
              have hprop_c : ∀ w',OrReach n D (gatesOf d1 D Kind.z q.val) w' q.val →
               IsCentred n C d (if w'=v' then n+j1 else iW n j0 j1 w'):=by
               intro w' hrw
               induction hrw using ReflTransGen.head_induction_on with
               | refl =>
                by_cases hqv : q.val=v'
                . rw [if_pos hqv]
                  refine (isCentred_gate n C d hrbC j1 hj1).mpr
                   ⟨by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte],q.val,?_,
                    (isCentred_input n C d q).mpr (mem_insert_of_mem hq_cov)⟩
                  have hv_q : v=q.val:=by rw [hv_eq,← hqv];unfold iW;rw [if_pos q.isLt]
                  rw [hv_q] at hvin;rcases hvin with h | h <;> rw [h] <;> simp
                . rw [if_neg hqv];unfold iW;rw [if_pos q.isLt]
                  exact (isCentred_input n C d q).mpr (mem_insert_of_mem hq_cov)
               | head hstep _ ih =>
                obtain ⟨k',hk'Z,rfl,hmem⟩:=hstep
                have hk'lt:=gatesOf_lt k' hk'Z
                have hlt:=invIdx_lt hj01 hj1 (by omega : k'+2 < C.gates.length)
                have hcent_inv : IsCentred n C d (iW n j0 j1 (n+k')):=by
                 unfold iW;rw [if_neg (by omega)]
                 have hsub_eq : n+k' - n=k':=by omega
                 rw [hsub_eq]
                 refine (isCentred_gate n C d hrbC (iI j0 j1 k') hlt).mpr
                  ⟨by rw [hRS k' hk'lt,(mem_filter.mp hk'Z).2],_,?_,ih⟩
                 rw [hzq_slot_C k' hk'Z];exact List.mem_map.mpr ⟨_,hmem,rfl⟩
                by_cases hkv : n+k'=v'
                . rw [if_pos hkv]
                  refine (isCentred_gate n C d hrbC j1 hj1).mpr
                   ⟨by simp only [d,if_neg (by omega : j1≠j0),↓reduceIte],iW n j0 j1 (n+k'),?_,hcent_inv⟩
                  rw [hkv,← hv_eq];rcases hvin with h | h <;> rw [h] <;> simp
                . rw [if_neg hkv];exact hcent_inv
              have hc:=hprop_c (d1.lam t q) hRZ
              rwa [if_neg hlam_ne_v] at hc
            . have hRC:=orLI
               (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
               (fun j' hj' => hNVI j' (gatesOf_lt j' hj') (hzt_no_v' r hrc hrq j' hj')) hRZ
              rw [hinv_r] at hRC
              exact icORZ hrbC (hRCI.mpr hrc) (fun j hj => by
               obtain ⟨j',hj',rfl⟩:=mem_image.mp hj
               have hj'lt:=gatesOf_lt j' hj'
               exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),
                by rw [hRS j' hj'lt,(mem_filter.mp hj').2]⟩) hRC
          . rcases hl'.2.1 with h1 | ⟨k,hk,h1,h2⟩
            . left;rw [h1,hinv_r]
            . right;exact ⟨iI j0 j1 k,invIdx_lt hj01 hj1 (by omega : k+2 < C.gates.length),
               by rw [h1];unfold iW;rw [if_neg (by omega)];simp,
               by rw [hRS k hk,h2]⟩
          . intro htie;simp only [d,if_neg hrp] at htie
            have hzr_eq:=hl'.2.2 htie
            by_cases hrq : r=q
            . subst r;simp only [d,if_neg hrp,↓reduceIte,if_neg (hzr_eq ▸ hlam_ne_v : d1.zroot q≠v'),hzr_eq]
            . simp only [d,if_neg hrp,if_neg hrq,hzr_eq]
      . rw [if_neg hrc] at hl';rw [if_neg (fun h => hrc (hRCI.mp h))]
        have hne_rv : r.val≠v':=by
         intro h;rw [← h] at hv'_zq
         rcases hv'_zq with hL | ⟨hrn,_⟩
         . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
           . exact hrc (Fin.ext h1 ▸ hq_cov)
           . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
             obtain ⟨js,_,hbw's,_⟩:=bwS hvD s (mem_filter.mp hs).1
             have:=r.isLt;omega
         . have:=r.isLt;omega
        simp only [d,if_neg htp,hl',lamMap,hne_rv,false_and,↓reduceIte]
        unfold iW;rw [if_pos r.isLt]
   exact ⟨hterm_t,hz_t,ho_t,hlam_t⟩
 ·
  have hTGs : topGates d C=(topGates d1 D).image (iI j0 j1):=by
   ext j;simp only [topGates,mem_filter,mem_range,mem_image]
   constructor
   . rintro ⟨hj,hr⟩
     have h0 : j≠j0:=fun h => by rw [h] at hr;simp [d] at hr
     have h1 : j≠j1:=fun h => by rw [h] at hr;simp only [d,if_neg (by omega : j1≠j0),↓reduceIte] at hr;cases hr
     simp only [d,if_neg h0,if_neg h1] at hr
     have hIL : iM j0 j1 j < D.gates.length:=by have:=iMLt hj01 hj1 hj h0 h1;omega
     exact ⟨iM j0 j1 j,⟨hIL,hr⟩,invIdx_idxMap hj01 h0 h1⟩
   . rintro ⟨j',⟨hj'lt,hr'⟩,rfl⟩
     exact ⟨invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length),by rw [hRS j' hj'lt,hr']⟩
  have hTLs : topLeaves d A=(topLeaves d1 A).image (iW n j0 j1):=by
   ext x;simp only [topLeaves,mem_union,mem_image,mem_filter,mem_insert,d]
   constructor
   . rintro (⟨a,haA,rfl⟩ | ⟨t,⟨htc,htie⟩,rfl⟩)
     . exact ⟨a.val,Or.inl ⟨a,haA,rfl⟩,by unfold iW;rw [if_pos a.isLt]⟩
     . by_cases htp : t=p
       . rw [if_pos htp] at htie;cases htie
       . rw [if_neg htp] at htie ⊢
         have ht' : t ∈ d1.cover:=by rcases htc with rfl | h;exact absurd rfl htp;exact h
         exact ⟨d1.bw t,Or.inr ⟨t,⟨ht',htie⟩,rfl⟩,rfl⟩
   . rintro ⟨w',hw',rfl⟩
     rcases hw' with ⟨a,haA,rfl⟩ | ⟨t,⟨ht',htie⟩,rfl⟩
     . left;exact ⟨a,haA,by unfold iW;rw [if_pos a.isLt]⟩
     . right;have htp : t≠p:=fun h => hpNC (h ▸ ht')
       exact ⟨t,⟨Or.inr ht',by simp [htp,htie]⟩,by simp [htp]⟩
  rw [hTGs,hTLs,hCE]
  exact otLI hvD.2.2.2.2.2.2 (iI j0 j1) (iW n j0 j1)
   (fun _ _ _ _ h => invIdx_inj hj01 h)
   (fun j' _ => by unfold iW;rw [if_neg (by omega)];simp)
   (fun a b _ _ h => invWire_inj hj01 h)
   (fun j' hj' => (hIF j' (topGates_lt j' hj')).1)
   (fun j' hj' => hNVI j' (topGates_lt j' hj') (htop_no_v' j' hj'))
set_option maxHeartbeats 600000 in
lemma fwd2c {n : ℕ} (K K1 K2 : SimpleGraph (Fin n))
 [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
 (A : Finset (Fin n)) (l p q : Fin n)
 (hA : ∀ a ∈ A,∀ v : Fin n,¬ K.Adj a v)
 (hl : ∀ v : Fin n,K.Adj l v↔v=p)
 (hql : q≠l)
 (hp : ∀ v : Fin n,K.Adj p v↔v=l\/v=q)
 (hK1 : ∀ u v : Fin n,K1.Adj u v↔K.Adj u v/\u≠l/\v≠l)
 (hK2 : ∀ u v : Fin n,K2.Adj u v↔K.Adj u v/\u≠l/\u≠p/\v≠l/\v≠p)
 {C : Circuit} (hmin : IsMinimalCircuit n C) (hfun : circuitFun n C=graphFun K A)
 {j0 j1 u v v' out' : ℕ} (hj01 : j0 < j1) (hj1 : j1 < C.gates.length)
 (hop0 : (gateAt C j0).op=.and)
 (huin : (gateAt C j0).inputs=[l.val,u]\/(gateAt C j0).inputs=[u,l.val])
 (hult : u < n+j0) (hul : u≠l.val)
 (hop1 : (gateAt C j1).op=.or)
 (hvin : (gateAt C j1).inputs=[n+j0,v]\/(gateAt C j1).inputs=[v,n+j0])
 (hvlt : v < n+j1) (hv0 : v≠n+j0) (hvl : v≠l.val)
 (hdel_eq : (Finset.range C.gates.length).filter (fun j => isD n l false C j=true)={j0,j1})
 (hcj0 : evE (sPfx n l false C.gates (j0+1)).2 (n+j0)=Sum.inl false)
 (hJ1I : evE (sPfx n l false C.gates (j1+1)).2 (n+j1)=Sum.inr v')
 (hOEv : evE (sPfx n l false C.gates C.gates.length).2 C.output=Sum.inr out')
 {d1 : NCCData n}
 (hvD : Valid n K1 A ⟨(sPfx n l false C.gates C.gates.length).1,out'⟩ d1)
 (hpNC : p ∉ d1.cover)
 (hMCP : IsMinCover K (insert p d1.cover)) :
 IsNestedCoverCircuit n K A C:=by
 obtain ⟨hlp,hpq,hlA,hpA,hqA,_,_,_⟩:=gArith K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hLPA : K.Adj l p:=(hl p).mpr rfl
 have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
 have hpq_K1 : K1.Adj p q:=(hK1 p q).mpr ⟨hPQA,hlp.symm,hql⟩
 obtain ⟨hncK,_,_⟩:=graphFun_nonconst_helpers K K1 K2 A l p q hA hl hql hp hK1 hK2
 have hncC : ∃ x y,circuitFun n C x≠circuitFun n C y:=by rw [hfun];exact hncK
 obtain ⟨hD_len,hWME,hKF,hIF,hOE,hval_F⟩ :=
  twoDS hmin hncC hj01 hj1 hdel_eq hcj0 hJ1I hOEv (valNN hvD)
 revert hvD hD_len hKF hIF hOE hval_F
 generalize hD_def : (⟨(sPfx n l false C.gates C.gates.length).1,out'⟩ : Circuit)=D
 intro hvD hD_len hKF hIF hOE hval_F
 have hrbC : ReadsBack n C:=by
  intro j hj i hi
  by_cases h0 : j=j0
  . subst j;rcases huin with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl
    . exact Nat.lt_of_lt_of_le l.isLt (Nat.le_add_right _ _)
    . exact hult
    . exact hult
    . exact Nat.lt_of_lt_of_le l.isLt (Nat.le_add_right _ _)
  . by_cases h1 : j=j1
    . subst j;rcases hvin with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl <;> omega
    . exact ((hKF j hj h0 h1).2.2 i hi).1
 have hlNC : l ∉ d1.cover :=
  isoNMC hvD.2.1 (fun w hw => ((hK1 l w).mp hw).2.1 rfl)
 have hq_cov : q ∈ d1.cover:=by
  rcases hvD.2.1.1 hpq_K1 with hp_in | hq_in
  . exact absurd hp_in hpNC
  . exact hq_in
 have hq_owns_p : d1.owns q p=true:=by
  have hp_no : d1.owns p q=false:=by
   cases h : d1.owns p q;rfl;exfalso;exact hpNC (hvD.2.2.1.1 p q h).2
  have hne:=hvD.2.2.1.2 p q hpq_K1
  rw [hp_no] at hne
  cases hq : d1.owns q p
  . rw [hq] at hne;exact absurd rfl hne
  . rfl
 have hv_eq : v=iW n j0 j1 v':=by
  have h1 : evE (sPfx n l false C.gates j1).2 v=Sum.inr v':=by
   have hstep : evE (sPfx n l false C.gates (j1+1)).2 (n+j1) =
    evE (sGt n (sPfx n l false C.gates j1) (gateAt C j1)).2
     (sPfx n l false C.gates j1).2.length:=by
    rw [simplifyPrefix_succ n l false C j1 hj1,simplifyPrefix_env_len n l false C j1 (by omega)]
   rw [hstep] at hJ1I
   have h0e : evE (sPfx n l false C.gates j1).2 (n+j0)=Sum.inl false:=by
    rw [spEnvS n l false C (by omega : j0+1<=j1) (by omega) (by omega),hcj0]
   rcases hst : sPfx n l false C.gates j1 with ⟨gs,env⟩
   rw [hst] at hJ1I h0e
   rcases hvin with h | h
   . simp only [sGt,hop1,h] at hJ1I
     rw [h0e] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I;exact hJ1I
   . simp only [sGt,hop1,h] at hJ1I
     cases hve : evE env v with
     | inl c =>
      rw [hve] at hJ1I
      cases c with
      | true => simp [evE,List.getD_eq_getElem?_getD] at hJ1I
      | false => rw [h0e] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I
     | inr w' =>
      rw [hve,h0e] at hJ1I;simp [evE,List.getD_eq_getElem?_getD] at hJ1I;rw [hJ1I]
  have h2 : evE (sPfx n l false C.gates C.gates.length).2 v=Sum.inr v':=by
   rw [spEnvS n l false C (by omega : j1<=C.gates.length) le_rfl hvlt,h1]
  have h3:=hWME v (by omega) hvl hv0
  rw [h2] at h3
  have hw : wM n j0 j1 v' v=v':=(Sum.inr.inj h3).symm
  rcases (wMEq hj01 hv0).mp hw with ⟨habs,_⟩ | ⟨_,heq⟩
  . omega
  . exact heq
 let u':=wM n j0 j1 v' u
 have hu_eq : u=iW n j0 j1 u':=by
  rcases (wMEq hj01 (by omega : u≠n+j0)).mp (rfl : wM n j0 j1 v' u=u') with ⟨habs,_⟩ | ⟨_,heq⟩
  . omega
  . exact heq
 have hu'_lt : u' < n+D.gates.length:=by
  have hinv:=spInv n l false C hmin.1 C.gates.length le_rfl
  have h:=hinv.2.2 (fun _ => false) u (by omega)
  rw [hWME u (by omega) hul (by omega)] at h
  rw [← hD_def];exact h.1
 have hDout_lt : D.output < n+D.gates.length:=by
  have hinv:=spInv n l false C hmin.1 C.gates.length le_rfl
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
  have hOL : C.output < n+C.gates.length:=by have:=outLst hmin hncC hne_g;omega
  have h:=hinv.2.2 (fun _ => false) C.output hOL
  rw [hOEv] at h;rw [← hD_def];exact h.1
 have hval_early : ∀ (x : Fin n->Bool) (w : ℕ),w < n+j1->w≠l.val->w≠n+j0 →
  wV n C x w=wV n D x (wM n j0 j1 v' w):=by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro hwlt hwl hw0
   by_cases hwn : w < n
   . let wf : Fin n:=⟨w,hwn⟩
     unfold wM;rw [if_pos hwn]
     change wV n C x wf.val=wV n D x wf.val
     rw [wvI,wvI]
   . have hj : w - n < C.gates.length:=by omega
     have hweq : n+(w - n)=w:=by omega
     have hne0 : w - n≠j0:=by omega
     have hne1 : w - n≠j1:=by omega
     have hIL : iM j0 j1 (w - n) < D.gates.length:=by
      have:=iMLt hj01 hj1 hj hne0 hne1;omega
     have hwm : wM n j0 j1 v' w=n+iM j0 j1 (w - n):=by
      unfold wM;rw [if_neg hwn,if_neg (by omega)]
     rw [hwm]
     conv_lhs => rw [← hweq]
     rw [wvGR n C hrbC x (w - n) hj,
      wvGR n D hvD.1 x (iM j0 j1 (w - n)) hIL]
     obtain ⟨hop,hinD,hsub⟩:=hKF (w - n) hj hne0 hne1
     rw [hop,hinD,List.map_map]
     congr 1;refine List.map_congr_left fun i hi => ?_
     obtain ⟨hi1,hi2,hi3⟩:=hsub i hi
     exact ih i (by omega) (by omega) hi2 hi3
 have hval_u : ∀ x : Fin n->Bool,wV n C x u=wV n D x u':=fun x =>
  hval_early x u (by omega) hul (by omega)
 have hval_v : ∀ x : Fin n->Bool,wV n C x v=wV n D x v':=fun x => by
  have h:=hval_early x v hvlt hvl hv0
  have hwm : wM n j0 j1 v' v=v':=by rw [hv_eq,wireMap_invWire hj01]
  rwa [hwm] at h
 have hval_j0 : ∀ x : Fin n->Bool,wV n C x (n+j0)=(x l && wV n D x u'):=by
  intro x
  rw [wvGR n C hrbC x j0 (by omega),hop0]
  rcases huin with h | h <;> rw [h] <;> simp [GateOp.eval,wvI,hval_u,Bool.and_comm]
 have hval_j1 : ∀ x : Fin n->Bool,
  wV n C x (n+j1)=((x l && wV n D x u') || wV n D x v'):=by
  intro x
  rw [wvGR n C hrbC x j1 hj1,hop1]
  rcases hvin with h | h <;> rw [h] <;> simp [GateOp.eval,hval_j0,hval_v,Bool.or_comm]
 let xlp : Fin n->Bool:=fun i => decide (i=l\/i=p)
 have hxlp_K : graphFun K A xlp=true:=by
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
  exact Or.inr ⟨l,p,hLPA,by simp [xlp],by simp [xlp]⟩
 have hxlp_K1 : graphFun K1 A xlp=false:=by
  simp only [graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not,not_exists,not_and]
  refine ⟨fun a ha hxa => ?_,fun a b hab hxa hxb => ?_⟩
  . simp only [xlp,decide_eq_true_eq] at hxa;rcases hxa with rfl | rfl;exact hlA ha;exact hpA ha
  . simp only [xlp,decide_eq_true_eq] at hxa hxb
    rcases hxa with ha | ha <;> rcases hxb with hb | hb
    . rw [ha,hb] at hab;exact hab.ne rfl
    . rw [ha,hb] at hab;exact ((hK1 l p).mp hab).2.1 rfl
    . rw [ha,hb] at hab;exact ((hK1 p l).mp hab).2.2 rfl
    . rw [ha,hb] at hab;exact hab.ne rfl
 have hxlp_no_K1 : ∀ a b : Fin n,K1.Adj a b->xlp a=true->xlp b=true->False:=by
  intro a b hab hxa hxb
  simp only [xlp,decide_eq_true_eq] at hxa hxb
  rcases hxa with ha | ha <;> rcases hxb with hb | hb
  . rw [ha,hb] at hab;exact hab.ne rfl
  . rw [ha,hb] at hab;exact ((hK1 l p).mp hab).2.1 rfl
  . rw [ha,hb] at hab;exact ((hK1 p l).mp hab).2.2 rfl
  . rw [ha,hb] at hab;exact hab.ne rfl
 have hu'_xlp_true : wV n D xlp u'=true:=by
  by_contra hfu
  have hfu' : wV n D xlp u'=false:=Bool.eq_false_iff.mpr hfu
  have hj1_xlp : wV n C xlp (n+j1)=wV n D xlp v':=by rw [hval_j1,hfu'];simp
  have hall : ∀ w < n+C.gates.length,w≠l.val->w≠n+j0 →
   wV n C xlp w=wV n D xlp (wM n j0 j1 v' w):=by
   intro w
   induction w using Nat.strong_induction_on with
   | ind w ih =>
    intro hwlt hwl hw0
    by_cases hw1 : w=n+j1
    . subst w;unfold wM;rw [if_neg (by omega),if_pos rfl,hj1_xlp]
    . by_cases hwn : w < n
      . let wf : Fin n:=⟨w,hwn⟩
        unfold wM;rw [if_pos hwn]
        change wV n C xlp wf.val=wV n D xlp wf.val
        rw [wvI,wvI]
      . have hj : w - n < C.gates.length:=by omega
        have hweq : n+(w - n)=w:=by omega
        have hne0 : w - n≠j0:=by omega
        have hne1 : w - n≠j1:=by omega
        have hIL : iM j0 j1 (w - n) < D.gates.length:=by
         have:=iMLt hj01 hj1 hj hne0 hne1;omega
        have hwm : wM n j0 j1 v' w=n+iM j0 j1 (w - n):=by
         unfold wM;rw [if_neg hwn,if_neg hw1]
        rw [hwm]
        conv_lhs => rw [← hweq]
        rw [wvGR n C hrbC xlp (w - n) hj,
         wvGR n D hvD.1 xlp (iM j0 j1 (w - n)) hIL]
        obtain ⟨hop,hinD,hsub⟩:=hKF (w - n) hj hne0 hne1
        rw [hop,hinD,List.map_map]
        congr 1;refine List.map_congr_left fun i hi => ?_
        obtain ⟨hi1,hi2,hi3⟩:=hsub i hi
        exact ih i (by omega) (by omega) hi2 hi3
  have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
  have hOL : C.output < n+C.gates.length:=by have:=outLst hmin hncC hne_g;omega
  have hout_ne_l : C.output≠l.val:=by have:=outLst hmin hncC hne_g;omega
  have hout_ne_0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
  have hCxlp:=hall C.output hOL hout_ne_l hout_ne_0
  rw [← hOE,wvO,wvO,hfun,nccEv hvD,hxlp_K,hxlp_K1] at hCxlp
  cases hCxlp
 have hu'_ne_l : u'≠l.val:=by
  intro h;rw [h] at hu_eq;unfold iW at hu_eq;rw [if_pos l.isLt] at hu_eq;exact hul hu_eq
 have huC : u'=p.val\/(n<=u'/\u' - n ∈ gatesOf d1 D Kind.o q.val):=by
  by_cases hun : u' < n
  . left
    let uf : Fin n:=⟨u',hun⟩
    have h1 : wV n D xlp uf.val=true:=hu'_xlp_true
    rw [wvI] at h1;simp only [xlp,decide_eq_true_eq] at h1
    rcases h1 with h1 | h2
    . exact absurd (congrArg Fin.val h1) hu'_ne_l
    . exact congrArg Fin.val h2
  . right
    have hj' : u' - n < D.gates.length:=by omega
    have hweq : n+(u' - n)=u':=by omega
    refine ⟨by omega,?_⟩
    rcases hvD.2.2.2.2.1 (u' - n) hj' with htop | ⟨t,ht,hrt,hrb⟩
    . exfalso
      have hjT : u' - n ∈ topGates d1 D:=mem_filter.mpr ⟨mem_range.mpr hj',htop⟩
      obtain ⟨lw,hlwL,_,hlwt⟩ :=
       (otEI hvD.1 topGates_lt hvD.2.2.2.2.2.2 xlp (Or.inr ⟨by omega,hjT⟩)).mp hu'_xlp_true
      unfold topLeaves at hlwL;rcases mem_union.mp hlwL with hA' | hB'
      . obtain ⟨a,haA,rfl⟩:=mem_image.mp hA'
        rw [wvI] at hlwt;simp only [xlp,decide_eq_true_eq] at hlwt
        rcases hlwt with rfl | rfl;exact hlA haA;exact hpA haA
      . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
        obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xlp (d1.bw s) s (mem_filter.mp hsF).1 rfl hlwt
        exact hxlp_no_K1 a b hab hxa hxb
    . cases hk : (d1.role (u' - n)).1 with
      | top =>
       exfalso
       have hjT : u' - n ∈ topGates d1 D:=mem_filter.mpr ⟨mem_range.mpr hj',hk⟩
       obtain ⟨lw,hlwL,_,hlwt⟩ :=
        (otEI hvD.1 topGates_lt hvD.2.2.2.2.2.2 xlp (Or.inr ⟨by omega,hjT⟩)).mp hu'_xlp_true
       unfold topLeaves at hlwL;rcases mem_union.mp hlwL with hA' | hB'
       . obtain ⟨a,haA,rfl⟩:=mem_image.mp hA'
         rw [wvI] at hlwt;simp only [xlp,decide_eq_true_eq] at hlwt
         rcases hlwt with rfl | rfl;exact hlA haA;exact hpA haA
       . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
         obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xlp (d1.bw s) s (mem_filter.mp hsF).1 rfl hlwt
         exact hxlp_no_K1 a b hab hxa hxb
      | b =>
       exfalso
       have hbw : d1.bw t=u':=by have:=hrb hk;omega
       obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xlp u' t ht hbw hu'_xlp_true
       exact hxlp_no_K1 a b hab hxa hxb
      | z =>
       exfalso
       have hjZ : u' - n ∈ gatesOf d1 D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
       obtain ⟨lz,hlzL,_,hlzt⟩ :=
        (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.1 xlp (Or.inr ⟨by omega,hjZ⟩)).mp hu'_xlp_true
       unfold zLeaves at hlzL;rcases mem_insert.mp hlzL with rfl | himg
       . rw [wvI] at hlzt;simp only [xlp,decide_eq_true_eq] at hlzt
         rcases hlzt with rfl | rfl;exact hlNC ht;exact hpNC ht
       . obtain ⟨s,hsF,rfl⟩:=mem_image.mp himg
         obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xlp (d1.bw s) s (mem_filter.mp hsF).1 rfl hlzt
         exact hxlp_no_K1 a b hab hxa hxb
      | o =>
       have hjO : u' - n ∈ gatesOf d1 D Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj',Prod.ext hk hrt⟩
       obtain ⟨lo,hloL,_,hlot⟩ :=
        (otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 t ht).2.2.1 xlp (Or.inr ⟨by omega,hjO⟩)).mp hu'_xlp_true
       obtain ⟨r,hrF,rfl⟩:=mem_image.mp hloL
       have hown:=(mem_filter.mp hrF).2
       have hadj:=(hvD.2.2.1.1 t r hown).1
       have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown
       unfold LamOK at hlam
       by_cases hrc : r ∈ d1.cover
       . exfalso;rw [if_pos hrc] at hlam
         have hzr : d1.lam t r ∈ zLeaves d1 r\/(n<=d1.lam t r/\d1.lam t r - n ∈ gatesOf d1 D Kind.z r.val):=by
          rcases hlam.2.1 with h1 | ⟨k,hk2,h1,h2⟩
          . left;rw [h1];exact mem_insert_self _ _
          . right;refine ⟨by omega,?_⟩
            have : d1.lam t r - n=k:=by omega
            rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk2,h2⟩
         obtain ⟨lz,hlzL,_,hlzt⟩:=(otEI hvD.1 gatesOf_lt (hvD.2.2.2.2.2.1 r hrc).2.1 xlp hzr).mp hlot
         unfold zLeaves at hlzL;rcases mem_insert.mp hlzL with rfl | himg
         . rw [wvI] at hlzt;simp only [xlp,decide_eq_true_eq] at hlzt
           rcases hlzt with rfl | rfl;exact hlNC hrc;exact hpNC hrc
         . obtain ⟨s,hsF,rfl⟩:=mem_image.mp himg
           obtain ⟨a,b,hab,hxa,hxb⟩:=nccBS hvD xlp (d1.bw s) s (mem_filter.mp hsF).1 rfl hlzt
           exact hxlp_no_K1 a b hab hxa hxb
       . rw [if_neg hrc] at hlam;rw [hlam,wvI] at hlot
         simp only [xlp,decide_eq_true_eq] at hlot
         rcases hlot with hrl | hrp
         . rw [hrl] at hadj;exact absurd rfl ((hK1 t l).mp hadj).2.2
         . rw [hrp] at hadj
           rcases (hp t).mp ((hK1 t p).mp hadj).1.symm with htl | htq
           . rw [htl] at hadj;exact absurd rfl ((hK1 l p).mp hadj).2.1
           . rw [htq] at hjO;exact hjO
 by_cases hvTp : v' ∈ topLeaves d1 A\/(n<=v'/\v' - n ∈ topGates d1 D)
 . exact fwd2cA K K1 K2 A l p q hA hl hql hp hK1 hK2 hmin hfun hrbC hncC
    hj01 hj1 hop0 huin hop1 hvin hv_eq hu_eq hvD hD_len hKF hIF hOE hDout_lt
    hpNC hlNC hMCP hq_cov hval_j1 huC hvTp
 . by_cases hv'_zq : v' ∈ zLeaves d1 q\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z q.val)
   . exact fwd2cB K K1 K2 A l p q hA hl hql hp hK1 hK2 hmin hfun hrbC hncC
      hj01 hj1 hop0 huin hop1 hvin hv_eq hu_eq hvD hD_len hKF hIF hOE hDout_lt
      hpNC hlNC hMCP hq_cov hq_owns_p hval_j1 huC hv'_zq
   ·
    exfalso
    have hNVI : ∀ j' < D.gates.length,v' ∉ (gateAt D j').inputs →
     (gateAt C (iI j0 j1 j')).inputs=(gateAt D j').inputs.map (iW n j0 j1):=by
     intro j' hj' hno
     have hlt:=invIdx_lt hj01 hj1 (by omega : j'+2 < C.gates.length)
     have hne:=invIdx_ne (j':=j') hj01
     obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 j') hlt hne.1 hne.2
     rw [idxMap_invIdx hj01] at hinD
     rw [hinD,List.map_map];symm
     rw [List.map_congr_left (g:=id) fun i hi => ?_,List.map_id]
     have hi0:=(hsub i hi).2.2
     have hwm_ne : wM n j0 j1 v' i≠v':=fun h => hno (hinD ▸ List.mem_map.mpr ⟨i,hi,h⟩)
     rcases (wMEq hj01 hi0).mp (rfl : wM n j0 j1 v' i=wM n j0 j1 v' i) with ⟨_,hveq⟩ | ⟨_,heq⟩
     . exact absurd hveq hwm_ne
     . exact heq.symm
    have hsafe : ∀ w' < n+D.gates.length,
     ((w' < n/\w'≠l.val/\w'≠p.val) ∨
      (n<=w'/\w' - n < D.gates.length ∧
       ((d1.role (w' - n)).1=Kind.top ∨
        (d1.role (w' - n)).1=Kind.b ∨
        (∃ t ∈ d1.cover,d1.role (w' - n)=(Kind.z,t.val)/\¬ (v' ∈ zLeaves d1 t\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z t.val))) ∨
        (∃ t ∈ d1.cover,t≠q/\d1.role (w' - n)=(Kind.o,t.val)/\(v' ∈ zLeaves d1 t\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z t.val)))))) →
     wV n C xlp (iW n j0 j1 w')=false:=by
     intro w'
     induction w' using Nat.strong_induction_on with
     | ind w' ih =>
      intro hw'lt hs
      rcases hs with ⟨hwn,hwl,hwp⟩ | ⟨hwn,hj',hkind⟩
      . let wf : Fin n:=⟨w',hwn⟩
        unfold iW;rw [if_pos hwn]
        change wV n C xlp wf.val=false
        have h1 : wf≠l:=fun h => hwl (congrArg Fin.val h)
        have h2 : wf≠p:=fun h => hwp (congrArg Fin.val h)
        rw [wvI];simp [xlp,h1,h2]
      . have hlt:=invIdx_lt hj01 hj1 (by omega : (w' - n)+2 < C.gates.length)
        have hne:=invIdx_ne (j':=w' - n) hj01
        unfold iW;rw [if_neg (by omega : ¬ w' < n)]
        rw [wvGR n C hrbC xlp (iI j0 j1 (w' - n)) hlt,(hIF (w' - n) hj').1]
        rcases hkind with htop | hb | ⟨t,ht,hz,hnotZt⟩ | ⟨s,hs_cov,hsq,ho,hZs⟩
        . have hjT : w' - n ∈ topGates d1 D:=mem_filter.mpr ⟨mem_range.mpr hj',htop⟩
          have hno_v : v' ∉ (gateAt D (w' - n)).inputs:=fun hm => hvTp ((hvD.2.2.2.2.2.2.1 (w' - n) hjT).2.2 v' hm)
          rw [(hvD.2.2.2.2.2.2.1 (w' - n) hjT).1,hNVI (w' - n) hj' hno_v]
          simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
          rintro b ⟨i',hi',hbi'⟩
          have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
          have hf:=ih i' hilt (by omega) (by
           rcases (hvD.2.2.2.2.2.2.1 (w' - n) hjT).2.2 i' hi' with hL | ⟨hin,hG⟩
           . unfold topLeaves at hL;rcases mem_union.mp hL with hA' | hB'
             . obtain ⟨a,haA,rfl⟩:=mem_image.mp hA'
               exact Or.inl ⟨a.isLt,fun h => hlA (Fin.ext h ▸ haA),fun h => hpA (Fin.ext h ▸ haA)⟩
             . obtain ⟨s,hsF,rfl⟩:=mem_image.mp hB'
               obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
               right;refine ⟨by omega,by omega,Or.inr (Or.inl ?_)⟩
               have : d1.bw s - n=js:=by omega
               rw [this,hrol]
           . exact Or.inr ⟨hin,topGates_lt _ hG,Or.inl (mem_filter.mp hG).2⟩)
          rw [hf] at hbi';subst hbi';decide
        . rcases hvD.2.2.2.2.1 (w' - n) hj' with htop | ⟨t,ht,_,hrb⟩
          . rw [hb] at htop;cases htop
          . obtain ⟨jb',hjb',hbw',_,hop',hin'⟩:=(hvD.2.2.2.2.2.1 t ht).1
            have hjj : w' - n=jb':=by have:=hrb hb;omega
            rw [hjj,hop']
            have hlt':=invIdx_lt hj01 hj1 (by omega : jb'+2 < C.gates.length)
            have hne':=invIdx_ne (j':=jb') hj01
            obtain ⟨_,hinD,hsub⟩:=hKF (iI j0 j1 jb') hlt' hne'.1 hne'.2
            rw [idxMap_invIdx hj01] at hinD
            by_cases hZt : v' ∈ zLeaves d1 t\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z t.val)
            ·
             have htq : t≠q:=fun h => hv'_zq (h ▸ hZt)
             have hor_ne_v : d1.oroot t≠v':=by
              intro heq
              have honode : v' ∈ oLeaves d1 t\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.o t.val):=by
               rw [← heq];have ho_r:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
               by_cases hGe : gatesOf d1 D Kind.o t.val=∅
               . rw [if_pos hGe] at ho_r;left;rw [ho_r];simp
               . rw [if_neg hGe] at ho_r;obtain ⟨k,hk,hkeq⟩:=ho_r;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
              rcases honode with hoL | ⟨_,hoG⟩
              . obtain ⟨r,hr,hLE⟩:=mem_image.mp hoL
                have hown:=(mem_filter.mp hr).2
                have hrt : r≠t:=(hvD.2.2.1.1 t r hown).1.ne.symm
                have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown;unfold LamOK at hlam
                by_cases hrc : r ∈ d1.cover
                . rw [if_pos hrc] at hlam
                  have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
                   rw [← hLE];rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
                   . left;rw [h1];exact mem_insert_self _ _
                   . right;refine ⟨by omega,?_⟩
                     have : d1.lam t r - n=k:=by omega
                     rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
                  exact znDN hvD hrt hzr hZt
                . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hZt
                  rcases hZt with hL | ⟨hrn,_⟩
                  . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
                    . exact hrt (Fin.ext h1)
                    . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
                      obtain ⟨js,_,hbw's,_⟩:=bwS hvD s (mem_filter.mp hs).1
                      have:=r.isLt;omega
                  . have:=r.isLt;omega
              . rcases hZt with hL | ⟨_,hZ⟩
                . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
                  . rw [h1] at hoG;have:=(mem_filter.mp hoG).1;have:=t.isLt;omega
                  . obtain ⟨s,hs,hbw⟩:=mem_image.mp himg
                    obtain ⟨js,_,hbw's,hrol⟩:=bwS hvD s (mem_filter.mp hs).1
                    have h1:=(mem_filter.mp hoG).2;have : v' - n=js:=by omega
                    rw [this,hrol] at h1;cases h1
                . have h1:=(mem_filter.mp hZ).2;have h2:=(mem_filter.mp hoG).2
                  rw [h1] at h2;cases h2
             have hor_in_C : iW n j0 j1 (d1.oroot t) ∈ (gateAt C (iI j0 j1 jb')).inputs:=by
              have hm : d1.oroot t ∈ (gateAt D jb').inputs:=by rcases hin' with h | h <;> rw [h] <;> simp
              rw [hinD] at hm;obtain ⟨i,hi,hwm⟩:=List.mem_map.mp hm
              rcases (wMEq hj01 (hsub i hi).2.2).mp hwm with ⟨_,hveq⟩ | ⟨_,heq⟩
              . exact absurd hveq hor_ne_v
              . exact heq ▸ hi
             have hor_lt : d1.oroot t < w':=by have:=(term_roots_lt_bw hvD ht).2;omega
             have hf:=ih (d1.oroot t) hor_lt (by omega) (by
              have ho_r:=(hvD.2.2.2.2.2.1 t ht).2.2.1.2.2.2
              by_cases hGe : gatesOf d1 D Kind.o t.val=∅
              . rw [if_pos hGe] at ho_r
                obtain ⟨r,hown⟩:=ownHOE hvD ht
                have hadj:=(hvD.2.2.1.1 t r hown).1
                have hmem_o : d1.lam t r ∈ oLeaves d1 t :=
                 mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,hown⟩,rfl⟩
                rw [ho_r,mem_singleton] at hmem_o
                have hrt : r≠t:=hadj.ne.symm
                have hrl : r≠l:=((hK1 t r).mp hadj).2.2
                have hrp : r≠p:=fun h => by
                 rw [h] at hadj;rcases (hp t).mp ((hK1 t p).mp hadj).1.symm with h1 | h2
                 . exact ((hK1 t p).mp hadj).2.1 h1
                 . exact htq h2
                have hlam:=(hvD.2.2.2.2.2.1 t ht).2.2.2 r hown;unfold LamOK at hlam
                rw [← hmem_o]
                by_cases hrc : r ∈ d1.cover
                . rw [if_pos hrc] at hlam
                  rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
                  . rw [h1];exact Or.inl ⟨r.isLt,fun h => hrl (Fin.ext h),fun h => hrp (Fin.ext h)⟩
                  . right;refine ⟨by omega,by omega,Or.inr (Or.inr (Or.inl ⟨r,hrc,?_,fun hZr => znDN hvD hrt hZr hZt⟩))⟩
                    have : d1.lam t r - n=k:=by omega
                    rw [this,h2]
                . rw [if_neg hrc] at hlam;rw [hlam]
                  exact Or.inl ⟨r.isLt,fun h => hrl (Fin.ext h),fun h => hrp (Fin.ext h)⟩
              . rw [if_neg hGe] at ho_r;obtain ⟨k,hk,hkeq⟩:=ho_r
                right;refine ⟨by omega,by have:=gatesOf_lt k hk;omega,Or.inr (Or.inr (Or.inr ⟨t,ht,htq,?_,hZt⟩))⟩
                have : d1.oroot t - n=k:=by omega
                rw [this,(mem_filter.mp hk).2])
             simp only [GateOp.eval,List.all_eq_false,List.mem_map]
             exact ⟨false,⟨iW n j0 j1 (d1.oroot t),hor_in_C,hf⟩,by decide⟩
            ·
             have hzr_ne_v : d1.zroot t≠v':=by
              intro heq;apply hZt;rw [← heq]
              have hz_r:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
              by_cases hGe : gatesOf d1 D Kind.z t.val=∅
              . rw [if_pos hGe] at hz_r;left;rw [hz_r];simp
              . rw [if_neg hGe] at hz_r;obtain ⟨k,hk,hkeq⟩:=hz_r;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
             have hzr_in_C : iW n j0 j1 (d1.zroot t) ∈ (gateAt C (iI j0 j1 jb')).inputs:=by
              have hm : d1.zroot t ∈ (gateAt D jb').inputs:=by rcases hin' with h | h <;> rw [h] <;> simp
              rw [hinD] at hm;obtain ⟨i,hi,hwm⟩:=List.mem_map.mp hm
              rcases (wMEq hj01 (hsub i hi).2.2).mp hwm with ⟨_,hveq⟩ | ⟨_,heq⟩
              . exact absurd hveq hzr_ne_v
              . exact heq ▸ hi
             have hzr_lt : d1.zroot t < w':=by have:=(term_roots_lt_bw hvD ht).1;omega
             have hf:=ih (d1.zroot t) hzr_lt (by omega) (by
              have hz_r:=(hvD.2.2.2.2.2.1 t ht).2.1.2.2.2
              by_cases hGe : gatesOf d1 D Kind.z t.val=∅
              . rw [if_pos hGe] at hz_r
                have htp : d1.zroot t=t.val:=by
                 have : t.val ∈ zLeaves d1 t:=mem_insert_self _ _
                 rw [hz_r,mem_singleton] at this;exact this.symm
                rw [htp];exact Or.inl ⟨t.isLt,fun h => hlNC (Fin.ext h ▸ ht),fun h => hpNC (Fin.ext h ▸ ht)⟩
              . rw [if_neg hGe] at hz_r;obtain ⟨k,hk,hkeq⟩:=hz_r
                right;refine ⟨by omega,by have:=gatesOf_lt k hk;omega,Or.inr (Or.inr (Or.inl ⟨t,ht,?_,hZt⟩))⟩
                have : d1.zroot t - n=k:=by omega
                rw [this,(mem_filter.mp hk).2])
             simp only [GateOp.eval,List.all_eq_false,List.mem_map]
             exact ⟨false,⟨iW n j0 j1 (d1.zroot t),hzr_in_C,hf⟩,by decide⟩
        . have hjZ : w' - n ∈ gatesOf d1 D Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj',hz⟩
          have hno_v : v' ∉ (gateAt D (w' - n)).inputs:=fun hm => hnotZt (((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ).2.2 v' hm)
          rw [((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ).1,hNVI (w' - n) hj' hno_v]
          simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
          rintro b ⟨i',hi',hbi'⟩
          have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
          have hf:=ih i' hilt (by omega) (by
           rcases ((hvD.2.2.2.2.2.1 t ht).2.1.1 (w' - n) hjZ).2.2 i' hi' with hL | ⟨hin,hG⟩
           . unfold zLeaves at hL;rcases mem_insert.mp hL with rfl | himg
             . exact Or.inl ⟨t.isLt,fun h => hlNC (Fin.ext h ▸ ht),fun h => hpNC (Fin.ext h ▸ ht)⟩
             . obtain ⟨s,hsF,rfl⟩:=mem_image.mp himg
               obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
               right;refine ⟨by omega,by omega,Or.inr (Or.inl ?_)⟩
               have : d1.bw s - n=js:=by omega
               rw [this,hrol]
           . right;exact ⟨hin,gatesOf_lt _ hG,Or.inr (Or.inr (Or.inl ⟨t,ht,(mem_filter.mp hG).2,hnotZt⟩))⟩)
          rw [hf] at hbi';subst hbi';decide
        . have hjO : w' - n ∈ gatesOf d1 D Kind.o s.val:=mem_filter.mpr ⟨mem_range.mpr hj',ho⟩
          have hno_v : v' ∉ (gateAt D (w' - n)).inputs:=by
           intro hm
           rcases ((hvD.2.2.2.2.2.1 s hs_cov).2.2.1.1 (w' - n) hjO).2.2 v' hm with hL | ⟨_,hG⟩
           . obtain ⟨r,hr,hLE⟩:=mem_image.mp hL
             have hown:=(mem_filter.mp hr).2
             have hrs : r≠s:=(hvD.2.2.1.1 s r hown).1.ne.symm
             have hlam:=(hvD.2.2.2.2.2.1 s hs_cov).2.2.2 r hown;unfold LamOK at hlam
             by_cases hrc : r ∈ d1.cover
             . rw [if_pos hrc] at hlam
               have hzr : v' ∈ zLeaves d1 r\/(n<=v'/\v' - n ∈ gatesOf d1 D Kind.z r.val):=by
                rw [← hLE];rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
                . left;rw [h1];exact mem_insert_self _ _
                . right;refine ⟨by omega,?_⟩
                  have : d1.lam s r - n=k:=by omega
                  rw [this];exact mem_filter.mpr ⟨mem_range.mpr hk,h2⟩
               exact znDN hvD hrs hzr hZs
             . rw [if_neg hrc] at hlam;rw [← hLE,hlam] at hZs
               rcases hZs with hL' | ⟨hrn,_⟩
               . unfold zLeaves at hL';rcases mem_insert.mp hL' with h1 | himg
                 . exact hrs (Fin.ext h1)
                 . obtain ⟨a,ha,hbw⟩:=mem_image.mp himg
                   obtain ⟨ja,_,hbw'a,_⟩:=bwS hvD a (mem_filter.mp ha).1
                   have:=r.isLt;omega
               . have:=r.isLt;omega
           . rcases hZs with hL | ⟨_,hZ⟩
             . unfold zLeaves at hL;rcases mem_insert.mp hL with h1 | himg
               . rw [h1] at hG;have:=(mem_filter.mp hG).1;have:=s.isLt;omega
               . obtain ⟨a,ha,hbw⟩:=mem_image.mp himg
                 obtain ⟨ja,_,hbw'a,hrol⟩:=bwS hvD a (mem_filter.mp ha).1
                 have h1:=(mem_filter.mp hG).2;have : v' - n=ja:=by omega
                 rw [this,hrol] at h1;cases h1
             . have h1:=(mem_filter.mp hZ).2;have h2:=(mem_filter.mp hG).2
               rw [h1] at h2;cases h2
          rw [((hvD.2.2.2.2.2.1 s hs_cov).2.2.1.1 (w' - n) hjO).1,hNVI (w' - n) hj' hno_v]
          simp only [GateOp.eval,List.map_map,List.any_eq_false,List.mem_map,Function.comp_apply,id_eq]
          rintro b ⟨i',hi',hbi'⟩
          have hilt : i' < w':=by have:=hvD.1 (w' - n) hj' i' hi';omega
          have hf:=ih i' hilt (by omega) (by
           rcases ((hvD.2.2.2.2.2.1 s hs_cov).2.2.1.1 (w' - n) hjO).2.2 i' hi' with hL | ⟨hin,hG⟩
           . obtain ⟨r,hr,rfl⟩:=mem_image.mp hL
             have hown:=(mem_filter.mp hr).2
             have hadj:=(hvD.2.2.1.1 s r hown).1
             have hrs : r≠s:=hadj.ne.symm
             have hrl : r≠l:=((hK1 s r).mp hadj).2.2
             have hrp : r≠p:=fun h => by
              rw [h] at hadj;rcases (hp s).mp ((hK1 s p).mp hadj).1.symm with h1 | h2
              . exact ((hK1 s p).mp hadj).2.1 h1
              . exact hsq h2
             have hlam:=(hvD.2.2.2.2.2.1 s hs_cov).2.2.2 r hown;unfold LamOK at hlam
             by_cases hrc : r ∈ d1.cover
             . rw [if_pos hrc] at hlam
               rcases hlam.2.1 with h1 | ⟨k,hk,h1,h2⟩
               . rw [h1];exact Or.inl ⟨r.isLt,fun h => hrl (Fin.ext h),fun h => hrp (Fin.ext h)⟩
               . right;refine ⟨by omega,by omega,Or.inr (Or.inr (Or.inl ⟨r,hrc,?_,fun hZr => znDN hvD hrs hZr hZs⟩))⟩
                 have : d1.lam s r - n=k:=by omega
                 rw [this,h2]
             . rw [if_neg hrc] at hlam;rw [hlam]
               exact Or.inl ⟨r.isLt,fun h => hrl (Fin.ext h),fun h => hrp (Fin.ext h)⟩
           . right;exact ⟨hin,gatesOf_lt _ hG,Or.inr (Or.inr (Or.inr ⟨s,hs_cov,hsq,(mem_filter.mp hG).2,hZs⟩))⟩)
          rw [hf] at hbi';subst hbi';decide
    have hDout_node : D.output ∈ topLeaves d1 A\/(n<=D.output/\D.output - n ∈ topGates d1 D):=by
     have hroot:=hvD.2.2.2.2.2.2.2.2.2
     by_cases hGe : topGates d1 D=∅
     . rw [if_pos hGe] at hroot;left;rw [hroot];simp
     . rw [if_neg hGe] at hroot;obtain ⟨k,hk,hkeq⟩:=hroot;right;exact ⟨by omega,by simpa [hkeq] using hk⟩
    have hCE : C.output=iW n j0 j1 D.output:=by
     have hne_g : C.gates ≠ []:=by intro h;simp [h] at hj1
     have hON0 : C.output≠n+j0:=by have:=outLst hmin hncC hne_g;omega
     rcases (wMEq hj01 hON0).mp hOE.symm with ⟨_,hveq⟩ | ⟨_,heq⟩
     . exact absurd (hveq ▸ hDout_node) hvTp
     . exact heq
    have hf:=hsafe D.output hDout_lt (by
     rcases hDout_node with hL | ⟨hin,hG⟩
     . unfold topLeaves at hL;rcases mem_union.mp hL with hA' | hB'
       . obtain ⟨a,haA,h1⟩:=mem_image.mp hA'
         rw [← h1];exact Or.inl ⟨a.isLt,fun h => hlA (Fin.ext h ▸ haA),fun h => hpA (Fin.ext h ▸ haA)⟩
       . obtain ⟨s,hsF,h1⟩:=mem_image.mp hB'
         obtain ⟨js,hjs,hbw,hrol⟩:=bwS hvD s (mem_filter.mp hsF).1
         right;refine ⟨by omega,by omega,Or.inr (Or.inl ?_)⟩
         have : D.output - n=js:=by omega
         rw [this,hrol]
     . exact Or.inr ⟨hin,topGates_lt _ hG,Or.inl (mem_filter.mp hG).2⟩)
    rw [← hCE,wvO,hfun,hxlp_K] at hf;cases hf
end PEqualNP.Outside.L_meta_540_aux
theorem PEqualNP.Outside.L_meta_540 : ∀ (n : ℕ) (K K1 K2 : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj] (A : Finset (Fin n)) (l p q : Fin n), ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 3 ≤ k → Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj) → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → (∀ v : Fin n, K.Adj l v ↔ v = p) → q ≠ l → (∀ v : Fin n, K.Adj p v ↔ v = l ∨ v = q) → (∀ u v : Fin n, K1.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l) → (∀ u v : Fin n, K2.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K1 A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K1 A C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K2 (insert p A)) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K2 (insert p A) C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C) := by
 intro n K K1 K2 _ _ _ A l p q k m H hk hemb hA hl hql hp hK1 hK2 h1 h2 C
 constructor
 . rintro ⟨hmin,hfun⟩
   have htf : ∀ a b c : Fin n,K.Adj a b->K.Adj b c->K.Adj a c->False :=
    fun _ _ _ => PEqualNP.Outside.L_meta_540_aux.tfEmb hk hemb
   obtain ⟨hlp,hpq,hlA,hpA,hqA,heK1,he12,ha2⟩ :=
    PEqualNP.Outside.L_meta_540_aux.gArith K K1 K2 A l p q hA hl hql hp hK1 hK2
   have hLPA : K.Adj l p:=(hl p).mpr rfl
   have hPQA : K.Adj p q:=(hp q).mpr (Or.inr rfl)
   obtain ⟨C1,d1,hv1⟩:=PEqualNP.Outside.L_meta_540_aux.exNcc K1 A
    (Or.inr ⟨p,q,(hK1 p q).mpr ⟨hPQA,hlp.symm,hql⟩⟩)
   obtain ⟨C2,d2,hv2⟩:=PEqualNP.Outside.L_meta_540_aux.exNcc K2 (insert p A)
    (Or.inl ⟨p,Finset.mem_insert_self _ _⟩)
   obtain ⟨CK,dK,hvK⟩:=PEqualNP.Outside.L_meta_540_aux.exNcc K A
    (Or.inr ⟨l,p,hLPA⟩)
   have hmin1:=(h1 C1).mpr ⟨d1,hv1⟩
   have hmin2:=(h2 C2).mpr ⟨d2,hv2⟩
   have hminK:=PEqualNP.Outside.L_meta_540_aux.revDir K K1 K2 A l p q hA hl hql hp hK1 hK2 h1 h2 ⟨dK,hvK⟩
   have hsz1:=PEqualNP.Outside.L_meta_540_aux.nccSz hv1
   have hsz2:=PEqualNP.Outside.L_meta_540_aux.nccSz hv2
   have hszK:=PEqualNP.Outside.L_meta_540_aux.nccSz hvK
   obtain ⟨hcK,hc21,_⟩:=PEqualNP.Outside.L_meta_540_aux.cArith K K1 K2 l p q hl hql hp hK1 hK2 hvK.2.1 hv1.2.1 hv2.2.1
   have hs1 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.MetaComplexity.circuitFun n D=PEqualNP.MetaComplexity.NestedCover.graphFun K1 A->C1.size<=D.size :=
    fun D hfit hDf => hmin1.1.2 D hfit (hDf.trans hmin1.2.symm)
   have hs2 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.MetaComplexity.circuitFun n D=PEqualNP.MetaComplexity.NestedCover.graphFun K2 (insert p A)->C2.size<=D.size :=
    fun D hfit hDf => hmin2.1.2 D hfit (hDf.trans hmin2.2.symm)
   have hs21 : C2.size<=C1.size:=by omega
   have hszC : C.size=C2.size+2:=by
    have hle1:=hmin.2 CK hminK.1.1 (hminK.2.trans hfun.symm)
    have hle2:=hminK.1.2 C hmin.1 (hfun.trans hminK.2.symm)
    omega
   obtain ⟨j0,j1,hj01,hj1,huniq_l,huniq1,hcase⟩ :=
    PEqualNP.Outside.L_meta_540_aux.clsL K K1 K2 A l p q hA hl hql hp hK1 hK2 hs1 hs2 hs21 hmin hfun hszC
   rcases hcase with
    ⟨u,v,v',out',hop0,huin,hult,hul,hop1,hvin,hvlt,hv0,hvl,hdel_eq,hcj0,hJ1I,hOEv,hfitD,hfunD,hszD⟩ |
    ⟨hs12,u,v,v',out',hop0,huin,hult,hul,hop1,hvin,hvlt,hv0,hvl,hdel_eq,hcj0,hJ1I,hOEv,hfitD,hfunD,hszD⟩
   . have hminD : PEqualNP.MetaComplexity.IsMinimalCircuit n ⟨(PEqualNP.Outside.L_meta_540_aux.sPfx n l true C.gates C.gates.length).1,out'⟩ :=
      ⟨hfitD,fun E hE hEf => by rw [hszD];exact hs2 E hE (hEf.trans hfunD)⟩
     obtain ⟨d',hvD⟩:=(h2 _).mp ⟨hminD,hfunD⟩
     exact PEqualNP.Outside.L_meta_540_aux.fwd2b K K1 K2 A l p q htf hA hl hql hp hK1 hK2
      hmin hfun hj01 hj1 huniq_l huniq1 hop0 huin hult hul hop1 hvin hvlt hv0 hvl
      hdel_eq hcj0 hJ1I hOEv hvD
   . have hminD : PEqualNP.MetaComplexity.IsMinimalCircuit n ⟨(PEqualNP.Outside.L_meta_540_aux.sPfx n l false C.gates C.gates.length).1,out'⟩ :=
      ⟨hfitD,fun E hE hEf => by rw [hszD];exact hs1 E hE (hEf.trans hfunD)⟩
     obtain ⟨d1',hvD⟩:=(h1 _).mp ⟨hminD,hfunD⟩
     have hszD':=PEqualNP.Outside.L_meta_540_aux.nccSz hvD
     have hcov_eq : d1'.cover.card=d2.cover.card:=by omega
     have hpNC : p ∉ d1'.cover:=by
      intro hp_in
      have hcov2 : K2.IsVertexCover ((d1'.cover.erase p : Finset (Fin n)) : Set (Fin n)):=by
       intro a b hab
       have h:=(hK2 a b).mp hab
       rcases hvD.2.1.1 ((hK1 a b).mpr ⟨h.1,h.2.1,h.2.2.2.1⟩) with ha | hb
       . exact Or.inl (Finset.mem_erase.mpr ⟨h.2.2.1,ha⟩)
       . exact Or.inr (Finset.mem_erase.mpr ⟨h.2.2.2.2,hb⟩)
      have hle:=hv2.2.1.2 (d1'.cover.erase p) hcov2
      have hlt:=Finset.card_erase_lt_of_mem hp_in
      omega
     have hMCP : PEqualNP.MetaComplexity.NestedCover.IsMinCover K (insert p d1'.cover):=by
      refine ⟨?_,?_⟩
      . intro a b hab
        by_cases hap : a=p
        . left;simp [hap]
        . by_cases hbp : b=p
          . right;simp [hbp]
          . have hal : a≠l:=fun h => hbp ((hl b).mp (h ▸ hab))
            have hbl : b≠l:=fun h => hap ((hl a).mp (h ▸ hab.symm))
            rcases hvD.2.1.1 ((hK1 a b).mpr ⟨hab,hal,hbl⟩) with ha | hb
            . exact Or.inl (Finset.mem_insert_of_mem ha)
            . exact Or.inr (Finset.mem_insert_of_mem hb)
      . intro T' hT'
        rw [Finset.card_insert_of_notMem hpNC,hcov_eq,← hcK]
        exact hvK.2.1.2 T' hT'
     exact PEqualNP.Outside.L_meta_540_aux.fwd2c K K1 K2 A l p q hA hl hql hp hK1 hK2
      hmin hfun hj01 hj1 hop0 huin hult hul hop1 hvin hvlt hv0 hvl
      hdel_eq hcj0 hJ1I hOEv hvD hpNC hMCP
 . exact PEqualNP.Outside.L_meta_540_aux.revDir K K1 K2 A l p q hA hl hql hp hK1 hK2 h1 h2
