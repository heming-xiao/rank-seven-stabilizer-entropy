import Rank7HighestTailReplacement

namespace RankSeven.HighestSlaterCoordinates

open Lean.Grind Pauli ComplexScalar AnchorSteinerTest AnchorExteriorCreation AnchorExteriorFive
open AnchorMixedCAR AnchorTripleEnergy HighestTailReplacement
variable {R I J : Type} [CommRing R]
local notation "C" => ComplexScalar R

def vacuum : (d : Nat)→Basis d→C
  | 0,_ => 1
  | _+1,(false,z) => vacuum _ z
  | _+1,(true,_) => 0

theorem lowerVacuum (y : I→C) (L : List I) : lower y L (vacuum L.length)=fun _=>0 := by
  funext z; induction L with
  | nil => rfl
  | cons i L ih => rcases z with ⟨j,z⟩; cases j <;> simp only [lower,vacuum,List.length_cons,ih,zeroLower] <;> grind only

private theorem zeroGram {d : Nat} (f : Basis d→C) : gram f (fun _=>0)=0 ∧ gram (fun _=>0) f=0 := by
  have h : star (0:C)=0 := by apply ComplexScalar.ext <;> simp <;> grind only
  unfold gram; simp only [h,Semiring.zero_mul,Semiring.mul_zero,and_self]
  generalize qubitIndices d=B
  induction B with
  | nil => rfl
  | cons i B ih => change 0+sumOver B _=0; rw [ih]; grind only

private theorem scaleGram {d : Nat} (a b : C) (f g : Basis d→C) :
    gram (fun z=>a*f z) (fun z=>b*g z)=star a*b*gram f g := by
  unfold gram; rw [sumOverMulLeft]; apply sumOverCongr; intro z; rw [star_mul]; grind only

private theorem gramBits {d : Nat} (f g : Basis (d+1)→C) :
    gram f g=gram (fun z=>f (false,z)) (fun z=>g (false,z))+gram (fun z=>f (true,z)) (fun z=>g (true,z)) := by
  change Bool×Basis d→C at f g
  unfold gram
  change sumOver (productIndices [false,true] (qubitIndices d)) _=_
  have split {A B : Type} (xs : List A) (ys : List B) (F : A×B→C) :
      sumOver (productIndices xs ys) F=sumOver xs (fun i=>sumOver ys (fun j=>F (i,j))) := by
    unfold productIndices; rw [sumOverFlatMap]; apply sumOverCongr; intro i; simp [sumOver,List.map_map,Function.comp_def]
  exact (split [false,true] (qubitIndices d) (fun z=>star (f z)*g z)).trans (by change _+(_+0)=_; grind only)

theorem vacuumGram (d : Nat) : gram (vacuum (R:=R) d) (vacuum d)=1 := by
  induction d with
  | zero =>
    change star (1:C)*1+0=1
    have z : star (1:C)=1:=by apply ComplexScalar.ext <;> simp <;> grind only
    rw [z]; grind only
  | succ d ih => rw [gramBits]; change gram (vacuum d) (vacuum d)+gram (fun _=>0) (fun _ : Basis d=>0)=1; rw [ih,(zeroGram _).1]; grind only

def synth (L : List I) (Y : J→I→C) : (js : List J)→(Basis js.length→C)→Basis L.length→C
  | [],f,z => f ()*vacuum L.length z
  | j::js,f,z => synth L Y js (fun u=>f (false,u)) z+
      raise (Y j) L (synth L Y js (fun u=>f (true,u))) z

theorem synthLinear (L : List I) (Y : J→I→C) (js : List J) (a b : C) (f g : Basis js.length→C) :
    synth L Y js (fun w=>a*f w+b*g w)=fun w=>a*synth L Y js f w+b*synth L Y js g w := by
  induction js with
  | nil => funext z; simp only [synth]; grind only
  | cons j js ih =>
    funext z; simp only [synth]
    rw [ih (fun u=>f (false,u)) (fun u=>g (false,u)), ih (fun u=>f (true,u)) (fun u=>g (true,u)),linearRaise]; grind only

def coordinate (L : List I) (Y : J→I→C) (a : I→C) (j : J) := star (dot L a (Y j))

/-- Contracting in the ambient Fock space equals contraction by the original frame
coordinates on its exterior algebra, for every frame and every one-particle mode. -/
theorem lowerSynth (L : List I) (Y : J→I→C) (js : List J) (a : I→C) (f : Basis js.length→C) :
    lower a L (synth L Y js f)=synth L Y js (lower (coordinate L Y a) js f) := by
  induction js with
  | nil =>
    change lower a L (fun w=>f ()*vacuum L.length w)=fun w=>(0:C)*vacuum L.length w
    have e : (fun w=>f ()*vacuum L.length w)=(fun w=>f ()*vacuum L.length w+0*vacuum L.length w) := by funext w; grind only
    funext z; rw [e,linearLower,lowerVacuum]; grind only
  | cons j js ih =>
    let f0 := fun u=>f (false,u)
    let f1 := fun u=>f (true,u)
    let y := coordinate L Y a
    have d : star (y j)=dot L a (Y j):=star_star _
    have h : synth L Y (j::js) f=fun z=>1*synth L Y js f0 z+1*raise (Y j) L (synth L Y js f1) z := by
      funext z; change _+_= _; grind only
    have eq0 : (fun u=>lower y (j::js) f (false,u))=(fun u=>dot L a (Y j)*f1 u+1*lower y js f0 u) := by
      funext u; change star (y j)*f1 u+lower y js f0 u=_; rw [d]; grind only
    have eq1 : (fun u=>lower y (j::js) f (true,u))=(fun u=>(-1)*lower y js f1 u+0*f1 u) := by
      funext u; change -lower y js f1 u=_; grind only
    funext z
    change lower a L _ z=synth L Y js (fun u=>lower y (j::js) f (false,u)) z+
      raise (Y j) L (synth L Y js (fun u=>lower y (j::js) f (true,u))) z
    rw [h,linearLower,push,ih f0,ih f1,eq0,eq1,synthLinear,synthLinear,linearRaise]; grind only

theorem synthZero (L : List I) (Y : J→I→C) (js : List J) : synth L Y js (fun _=>0)=fun _=>0 := by
  induction js with
  | nil => funext z; simp only [synth]; grind only
  | cons j js ih => funext z; simp only [synth,ih,raiseZero]; grind only

theorem lowerOff (L : List I) (a : I→C) (away : ∀i∈L,a i=0) (f : Basis L.length→C) :
    lower a L f=fun _=>0 := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have p:=away i (by simp)
    have q:=ih (fun j hj=>away j (List.mem_cons_of_mem i hj))
    funext ⟨j,z⟩; cases j <;> simp only [lower,p,q]
    · have zz : star (0:C)=0:=by apply ComplexScalar.ext <;>simp <;>grind only
      rw [zz]; grind only
    · grind only

private theorem gramAdd {d : Nat} (f g h t : Basis d→C) :
    gram (fun z=>f z+g z) (fun z=>h z+t z)=gram f h+gram f t+gram g h+gram g t := by
  unfold gram; rw [←sumOverAdd,←sumOverAdd,←sumOverAdd]; apply sumOverCongr; intro z; rw [star_add]; grind only

theorem synthGram (L : List I) (Y : J→I→C) (js : List J) (nd : js.Nodup)
    (unit : ∀j∈js, dot L (Y j) (Y j)=1)
    (apart : ∀i∈js,∀j∈js,i≠j → dot L (Y i) (Y j)=0)
    (f g : Basis js.length→C) : gram (synth L Y js f) (synth L Y js g)=gram f g := by
  induction js with
  | nil =>
    change gram (fun z=>f ()*vacuum L.length z) (fun z=>g ()*vacuum L.length z)=star (f ())*g ()+0
    rw [scaleGram,vacuumGram]; grind only
  | cons i js ih =>
    obtain ⟨absent,nd'⟩:=List.nodup_cons.mp nd
    have tail:=ih nd' (fun j hj=>unit j (List.mem_cons_of_mem i hj))
        (fun j hj k hk=>apart j (List.mem_cons_of_mem i hj) k (List.mem_cons_of_mem i hk))
    have unitI:=unit i (by simp)
    have away : ∀j∈js,coordinate L Y (Y i) j=0 := by
      intro j hj; unfold coordinate
      rw [apart i (by simp) j (List.mem_cons_of_mem i hj) (fun eq=>absent (eq ▸ hj))]
      apply ComplexScalar.ext <;> simp <;> grind only
    have vacant (h : Basis js.length→C) : lower (Y i) L (synth L Y js h)=fun _=>0 := by
      rw [lowerSynth,lowerOff _ _ away,synthZero]
    let f0:=synth L Y js (fun w=>f (false,w))
    let f1:=synth L Y js (fun w=>f (true,w))
    let g0:=synth L Y js (fun w=>g (false,w))
    let g1:=synth L Y js (fun w=>g (true,w))
    have e1:gram (raise (Y i) L f1) g0=0:=by rw [(adjoint ..).1,vacant,(zeroGram _).1]
    have e2:gram f0 (raise (Y i) L g1)=0:=by rw [←(adjoint ..).2,vacant,(zeroGram _).2]
    have p:=push (Y i) (Y i) L g1
    rw [vacant,raiseZero,unitI] at p
    have p' : lower (Y i) L (raise (Y i) L g1)=g1 := p.trans (by funext z; grind only)
    have e3 : gram (raise (Y i) L f1) (raise (Y i) L g1)=gram f1 g1:=by rw [(adjoint ..).1,p']
    change gram (fun z=>f0 z+raise (Y i) L f1 z) (fun z=>g0 z+raise (Y i) L g1 z)=_
    rw [gramAdd,e1,e2,e3,gramBits f g]
    change gram (synth L Y js _) (synth L Y js _)+0+0+gram (synth L Y js _) (synth L Y js _)=_
    rw [tail,tail]; grind only

def filled : (d : Nat)→Basis d→C
  | 0,_ => 1
  | _+1,(false,_) => 0
  | _+1,(true,z) => filled _ z

theorem filledGram (d : Nat) : gram (filled (R:=R) d) (filled d)=1 := by
  induction d with
  | zero => exact vacuumGram 0
  | succ d ih => rw [gramBits]; change gram (fun _=>0) (fun _ : Basis d=>0)+gram (filled d) (filled d)=1; rw [ih,(zeroGram _).1]; grind only

theorem vacuumCap (L : List I) : cap L 0 (vacuum (R:=R) L.length) := by
  induction L with
  | nil => intro u _; exact Nat.le_refl 0
  | cons i L ih =>
    rintro ⟨b,z⟩ nz; cases b
    · exact ih z nz
    · exact False.elim (nz rfl)

theorem synthCap (L : List I) (Y : J→I→C) (js : List J) (f : Basis js.length→C) :
    cap L js.length (synth L Y js f) := by
  induction js with
  | nil =>
    intro z nz; apply vacuumCap (R:=R) L z; intro eq; apply nz; change _*vacuum L.length z=0; rw [eq]; grind only
  | cons j js ih =>
    intro z nz
    have cap0:=ih (fun u=>f (false,u))
    have cap1:=capRaise L js.length (Y j) _ (ih (fun u=>f (true,u)))
    by_cases h:synth L Y js (fun u=>f (false,u)) z=0
    · apply cap1 z; intro eq; apply nz; change _+_=0; rw [h,eq]; grind only
    · exact Nat.le_succ_of_le (cap0 z h)

def pullContract (L : List I) (Y : J→I→C) (js : List J) (y a b c : I→C)
    (f : Basis js.length→C) (z : Basis js.length) :=
  let coord:=coordinate L Y
  dot L a y*two js (coord b) (coord c) f z-dot L b y*two js (coord a) (coord c) f z+
    dot L c y*two js (coord a) (coord b) f z

theorem contractedSynth (L : List I) (Y : J→I→C) (js : List J) (y a b c : I→C) (f : Basis js.length→C) :
    contracted L y a b c (synth L Y js f)=synth L Y js (pullContract L Y js y a b c f) := by
  let co:=coordinate L Y
  have pp (x w:I→C) : two L x w (synth L Y js f)=synth L Y js (two js (co x) (co w) f) := by
    unfold two; rw [lowerSynth,lowerSynth]
  have e : pullContract L Y js y a b c f=fun z=>dot L c y*two js (co a) (co b) f z+
      (-1)*(dot L b y*two js (co a) (co c) f z+(-dot L a y)*two js (co b) (co c) f z) := by
    funext z; unfold pullContract; dsimp only; grind only
  rw [e,synthLinear,synthLinear]; funext z; unfold contracted; rw [pp,pp,pp]; grind only

theorem contractedSlaterEnergy (L : List I) (Y : J→I→C) (js : List J) (nd : js.Nodup)
    (unit : ∀j∈js, dot L (Y j) (Y j)=1)
    (apart : ∀i∈js,∀j∈js,i≠j → dot L (Y i) (Y j)=0) (y a b c : I→C) :
    energy (contracted L y a b c (synth L Y js (filled js.length)))=
      energy (pullContract L Y js y a b c (filled js.length)) := by
  rw [contractedSynth]; unfold energy; rw [←reGram,←reGram,synthGram L Y js nd unit apart]

theorem unitSlater (L : List I) (Y : J→I→C) (js : List J) (nd : js.Nodup)
    (unit : ∀j∈js, dot L (Y j) (Y j)=1)
    (apart : ∀i∈js,∀j∈js,i≠j → dot L (Y i) (Y j)=0) :
    energy (synth L Y js (filled js.length))=1 := by
  unfold energy; rw [←reGram,synthGram L Y js nd unit apart,filledGram,re_one]

end RankSeven.HighestSlaterCoordinates

#print axioms RankSeven.HighestSlaterCoordinates.lowerSynth
#print axioms RankSeven.HighestSlaterCoordinates.synthGram
#print axioms RankSeven.HighestSlaterCoordinates.synthCap
#print axioms RankSeven.HighestSlaterCoordinates.contractedSynth
#print axioms RankSeven.HighestSlaterCoordinates.contractedSlaterEnergy
#print axioms RankSeven.HighestSlaterCoordinates.unitSlater

