import Rank7HeavyPauliGroup

namespace RankSeven.StabilizerCharacterBasis

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks HeavyPauliGroup PhysicalAntiQuartic
variable {R : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

def act {n : Nat} (p : Word n) (x : Basis n → ComplexScalar R) (i : Basis n) :=
  sumOver (qubitIndices n) (fun j => wordEntry imaginaryUnit p i j*x j)

theorem actProduct {n : Nat} (p q : Word n) (x : Basis n → ComplexScalar R) (i : Basis n) :
    act p (act q x) i=cocycle imaginaryUnit p q*act (wordAdd p q) x i := by
  let xs := qubitIndices n
  let X (i : Basis n) (_ : Unit) := x i
  let W (a : Word n) := wordEntry (imaginaryUnit (R:=R)) a
  change matMul xs (W p) (matMul xs (W q) X) i ()=_
  rw [←matMulAssoc]
  change sumOver xs (fun j => matMul xs (W p) (W q) i j*x j)=_
  have m (j : Basis n) := physicalWordProduct (imaginaryUnit (R:=R)) imaginaryUnit_sq p q i j
  simp only [xs,W,m,PhysicalEdgeSwitching.productLabelIsWordAdd,act,sumOverMulLeft]
  apply sumOverCongr; intro j; grind only

theorem actScale {n : Nat} (p : Word n) (s : ComplexScalar R) (x : Basis n → ComplexScalar R) (i : Basis n) :
    act p (fun j => s*x j) i=s*act p x i := by
  unfold act; rw [sumOverMulLeft]; apply sumOverCongr; intro j; grind only

theorem actAdd {n : Nat} (p : Word n) (x y : Basis n → ComplexScalar R) (i : Basis n) :
    act p (fun j => x j+y j) i=act p x i+act p y i := by
  unfold act; rw [←sumOverAdd]; apply sumOverCongr; intro j; grind only

theorem actIdentity {n : Nat} (x : Basis n → ComplexScalar R) (i : Basis n) :
    act (unitWord n) x i=x i := by
  have id (m : Nat) (u v : Basis m) : wordEntry (imaginaryUnit (R:=R)) (unitWord m) u v=if u=v then 1 else 0 := by
    induction m with
    | zero => cases u; cases v; rfl
    | succ m ih => rcases u with ⟨u,i⟩; rcases v with ⟨v,j⟩; cases u <;> cases v <;> by_cases h : i=j <;> simp [wordEntry,unitWord,entry,ih,h] <;> grind only
  unfold act
  rw [←ExteriorPauliBase.sumOnIndex (qubitIndices n) i x (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n i)]
  apply sumOverCongr; intro j; rw [id]; by_cases h : i=j <;> simp [h] <;> grind only

theorem actSquare {n : Nat} (p : Word n) (x : Basis n → ComplexScalar R) (i : Basis n) : act p (act p x) i=x i := by
  rw [actProduct,wordAddSelf,cocycleSelf,actIdentity,Semiring.one_mul]

theorem commuteAct {n : Nat} (p q : Word n) (h : anti p q=false) (x : Basis n → ComplexScalar R) (i : Basis n) :
    act p (act q x) i=act q (act p x) i := by
  rw [actProduct,actProduct,cocycleSwap (imaginaryUnit (R:=R)) p q,wordAddComm p q]
  simp only [chi,h,phase,Bool.false_eq_true,ite_false,Semiring.one_mul]

private def origin : (m : Nat) → Basis m
  | 0 => ()
  | m+1 => (false,origin m)

theorem jointEigenvector {n : Nat} (xs : List (Word n)) (comm : ∀ p∈xs,∀ q∈xs,anti p q=false) :
    ∃ (x : Basis n→ComplexScalar Int) (sgn : Word n→Bool), (∃i,x i≠0) ∧
      ∀ p∈xs,∀i,act p x i=phase (sgn p)*x i := by
  classical
  induction xs with
  | nil =>
    refine ⟨fun _ => 1,fun _ => false,⟨origin n,?_⟩,by simp⟩
    intro eq; have e := congrArg (fun z : ComplexScalar Int => z.re) eq
    simp only [re_one,re_zero] at e; omega
  | cons a xs ih =>
    obtain ⟨x,sgn,hx,eig⟩ := ih (fun p hp q hq => comm p (List.mem_cons_of_mem a hp) q (List.mem_cons_of_mem a hq))
    let y (i : Basis n) := x i+act a x i
    by_cases nonzero : ∃i,y i≠0
    · refine ⟨y,fun p => if p=a then false else sgn p,nonzero,?_⟩
      intro p hp i; by_cases e : p=a
      · subst p; simp only [ite_true,phase,Bool.false_eq_true,ite_false,Semiring.one_mul]
        dsimp only [y]; rw [actAdd,actSquare]; grind only
      · simp only [e,ite_false]
        have ht := (List.mem_cons.mp hp).resolve_left e
        have px : act p x=fun j => phase (sgn p)*x j := funext (eig p ht)
        have c := commuteAct p a (comm p hp a List.mem_cons_self) x i
        rw [px,actScale] at c
        dsimp only [y]; rw [actAdd,c,eig p ht i]; grind only
    · refine ⟨x,fun p => if p=a then true else sgn p,hx,?_⟩
      intro p hp i; by_cases e : p=a
      · subst p; have z : y i=0 := Classical.byContradiction (fun ne => nonzero ⟨i,ne⟩)
        change x i+act a x i=0 at z; simp only [ite_true,phase]; grind only
      · simp only [e,ite_false]; exact eig p ((List.mem_cons.mp hp).resolve_left e) i

/-- A sign convention for the actual Hermitian words in a commuting family.
The Boolean cocycle condition is independent of the coefficient ring. -/
structure Lift (G : MaximalFamily n) where
  sign : Word n → Bool
  identity : sign (unitWord n)=false
  product : ∀ p∈G.labels,∀ q∈G.labels,sign (wordAdd p q)=((sign p ^^ sign q) ^^ negativeProduct p q)

private theorem oppositeImpossible (x : ComplexScalar Int) (ne : x≠0) (eq : x= -x) : False := by
  have re := congrArg ComplexScalar.re eq; have im := congrArg ComplexScalar.im eq
  simp only [re_neg,im_neg] at re im
  apply ne; apply ComplexScalar.ext <;> simp <;> omega

theorem liftExists (G : MaximalFamily n) : Nonempty (Lift G) := by
  obtain ⟨x,sgn,⟨i,ne⟩,eig⟩ := jointEigenvector G.labels (fun p hp => (G.criterion _).mp hp)
  refine ⟨⟨sgn,?_,?_⟩⟩
  · have e := eig (unitWord n) (zeroMem G) i; rw [actIdentity] at e
    cases h : sgn (unitWord n) with
    | false => rfl
    | true => rw [h] at e; simp only [phase,ite_true] at e
              exact False.elim (oppositeImpossible (x i) ne (by grind only))
  · intro p hp q hq
    have c := (G.criterion p).mp hp q hq
    have eq := actProduct p q x i
    have qx : act q x=fun j => phase (sgn q)*x j := funext (eig q hq)
    rw [qx,actScale,eig p hp,eig _ (addMem G p q hp hq),cocyclePhaseBits imaginaryUnit imaginaryUnit_sq,c] at eq
    cases e : sgn (wordAdd p q) <;> cases a : sgn p <;> cases b : sgn q <;> cases f : negativeProduct p q <;>
      first | rfl | (simp only [e,a,b,f,phase,Bool.false_eq_true,ite_true,ite_false] at eq
                     exact False.elim (oppositeImpossible (x i) ne (by grind only)))

def lifted {n : Nat} {G : MaximalFamily n} (L : Lift G) (p : Word n) (i j : Basis n) : ComplexScalar R :=
  phase (L.sign p)*wordEntry imaginaryUnit p i j

theorem liftProduct {n : Nat} {G : MaximalFamily n} (L : Lift G) (p q : Word n) (hp : p∈G.labels) (hq : q∈G.labels)
    (i j : Basis n) : matMul (qubitIndices n) (lifted (R:=R) L p) (lifted L q) i j=lifted L (wordAdd p q) i j := by
  let W (p : Word n) := wordEntry (imaginaryUnit (R:=R)) p
  have eq : matMul (qubitIndices n) (lifted (R:=R) L p) (lifted L q) i j=
      phase (L.sign p)*phase (L.sign q)*matMul (qubitIndices n) (W p) (W q) i j := by
    unfold matMul lifted W; rw [sumOverMulLeft]; apply sumOverCongr; intro k; grind only
  rw [eq]; unfold W lifted
  rw [physicalWordProduct imaginaryUnit imaginaryUnit_sq,PhysicalEdgeSwitching.productLabelIsWordAdd,
    cocyclePhaseBits imaginaryUnit imaginaryUnit_sq,(G.criterion p).mp hp q hq,L.product p hp q hq]
  cases L.sign p <;> cases L.sign q <;> cases negativeProduct p q <;> simp [phase] <;> grind only

def raw {n : Nat} {G : MaximalFamily n} (L : Lift G) (a : Word n) (i j : Basis n) : ComplexScalar R :=
  sumOver G.labels (fun p => chi a p*lifted L p i j)

def block {n : Nat} {G : MaximalFamily n} (half : R) (L : Lift G) (a : Word n) (i j : Basis n) :=
  (ofReal half)^n*raw L a i j

private theorem matSumRight {α β : Type} (xs : List α) (ys : List β) (A : α→α→ComplexScalar R)
    (F : β→α→α→ComplexScalar R) (c : β→ComplexScalar R) (i j : α) :
    matMul xs A (fun v w => sumOver ys (fun p => c p*F p v w)) i j=
    sumOver ys (fun p => c p*matMul xs A (F p) i j) := by
  unfold matMul; simp only [sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro p; apply sumOverCongr; intro v; grind only

private theorem matSumLeft {α β : Type} (xs : List α) (ys : List β) (A : α→α→ComplexScalar R)
    (F : β→α→α→ComplexScalar R) (c : β→ComplexScalar R) (i j : α) :
    matMul xs (fun v w => sumOver ys (fun p => c p*F p v w)) A i j=
    sumOver ys (fun p => c p*matMul xs (F p) A i j) := by
  unfold matMul; simp only [sumOverMulRight,sumOverMulLeft]; rw [sumOverSwap]
  apply sumOverCongr; intro p; apply sumOverCongr; intro v; grind only

theorem rawEigen {n : Nat} {G : MaximalFamily n} (L : Lift G) (a p : Word n) (hp : p∈G.labels) (i j : Basis n) :
    matMul (qubitIndices n) (lifted (R:=R) L p) (raw L a) i j=chi a p*raw L a i j := by
  unfold raw; rw [matSumRight]
  have eq (q : Word n) (hq : q∈G.labels) :
      chi a q*matMul (qubitIndices n) (lifted (R:=R) L p) (lifted L q) i j=
      chi a p*(chi a (wordAdd q p)*lifted L (wordAdd q p) i j) := by
    rw [liftProduct L p q hp hq,wordAddComm p q,characterAddRight a q p]
    cases h : anti a p <;> simp only [chi,h,phase,Bool.false_eq_true,ite_true,ite_false] <;> grind only
  rw [AnticommutingDefect.sumCongrMem G.labels _ _ eq,←sumOverMulLeft]
  rw [groupSumShift G p hp (fun q => (chi a q:ComplexScalar R)*lifted L q i j)]

private theorem chiIdentity {n : Nat} (a : Word n) : (chi a (unitWord n):ComplexScalar R)=1 := by
  simp only [chi,antiZero,phase,Bool.false_eq_true,ite_false]

theorem rawTrace {n : Nat} {G : MaximalFamily n} (L : Lift G) (a : Word n) :
    trace (qubitIndices n) (raw (R:=R) L a)=(2:ComplexScalar R)^n := by
  unfold trace raw lifted; rw [sumOverSwap]
  have e (p : Word n) :
      sumOver (qubitIndices n) (fun i => chi a p*(phase (L.sign p)*wordEntry (imaginaryUnit (R:=R)) p i i))=
      if unitWord n=p then (2:ComplexScalar R)^n else 0 := by
    rw [←sumOverMulLeft,←sumOverMulLeft]
    change chi a p*(phase (L.sign p)*trace (qubitIndices n) (wordEntry (imaginaryUnit (R:=R)) p))=_
    rw [physicalWordTrace]; by_cases h : p=unitWord n
    · subst p; rw [chiIdentity,L.identity]; simp only [phase,Bool.false_eq_true,ite_true,ite_false,Semiring.one_mul]
    · simp [h,Ne.symm h,Semiring.mul_zero]
  rw [sumOverCongr _ e]; exact ExteriorPauliBase.sumOnIndex G.labels (unitWord n) _ G.nodup (zeroMem G)

private theorem starSum {α : Type} (xs : List α) (f : α→ComplexScalar R) :
    star (sumOver xs f)=sumOver xs (fun i => star (f i)) := by
  induction xs with
  | nil => change star (0:ComplexScalar R)=0; apply ComplexScalar.ext <;> simp <;> grind only
  | cons i xs ih => change star (f i+sumOver xs f)=star (f i)+_; rw [star_add,ih]; rfl

private theorem starPhase (b : Bool) : star (phase b : ComplexScalar R)=phase b := by
  cases b <;> apply ComplexScalar.ext <;> simp [phase] <;> grind only

theorem rawHerm {n : Nat} {G : MaximalFamily n} (L : Lift G) (a : Word n) :
    PhysicalPairedReduction.dagger (raw (R:=R) L a)=raw L a := by
  funext i j; change star (raw L a j i)=raw L a i j
  unfold raw lifted chi
  simp only [starSum,star_mul,starPhase,ComplexPauliMoment.wordHermitian]

private theorem embeddedSum {α : Type} (xs : List α) (f : α→R) : ofReal (sumOver xs f)=sumOver xs (fun i => ofReal (f i)) := by
  induction xs with
  | nil => change ofReal (0:R)=0; rfl
  | cons i xs ih =>
    change ofReal (f i+sumOver xs f)=ofReal (f i)+sumOver xs _
    rw [←ih]; apply ComplexScalar.ext <;> simp <;> grind only

private theorem ofRealPhase (b : Bool) : ofReal (phase b:R)=(phase b:ComplexScalar R) := by
  cases b <;> apply ComplexScalar.ext <;> simp [phase] <;> grind only

private theorem dimension (m : Nat) : ofReal ((2:R)^m)=(2:ComplexScalar R)^m := by
  rw [PhysicalPairedReduction.realEmbeddingPow]; rfl

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Semiring.natCast

theorem chiSum {n : Nat} (G : MaximalFamily n) (a : Word n) :
    sumOver G.labels (fun g => (chi a g:ComplexScalar R))=if a∈G.labels then (2:ComplexScalar R)^n else 0 := by
  have h := congrArg (fun u : R => ofReal u) (HeavyPauliGroup.characterSum G a)
  rw [embeddedSum] at h
  simp only [chi,ofRealPhase] at h ⊢
  rw [h,cardinalCast (R:=R)]
  by_cases e : a∈G.labels <;> simp only [e,ite_true,ite_false,dimension] <;> rfl

theorem rawProduct {n : Nat} {G : MaximalFamily n} (L : Lift G) (a b : Word n) (i j : Basis n) :
    matMul (qubitIndices n) (raw (R:=R) L a) (raw L b) i j=
      (if wordAdd a b∈G.labels then (2:ComplexScalar R)^n else 0)*raw L b i j := by
  change matMul _ (fun x y => sumOver G.labels (fun p => chi a p*lifted L p x y)) (raw (R:=R) L b) i j=_
  rw [matSumLeft]
  have eq (q : Word n) (hq : q∈G.labels) : chi a q*matMul (qubitIndices n) (lifted (R:=R) L q) (raw L b) i j=
      chi (wordAdd a b) q*raw L b i j := by
    rw [rawEigen L b q hq,chiSymm (wordAdd a b) q,characterAddRight q a b,chiSymm q a,chiSymm q b]; grind only
  rw [AnticommutingDefect.sumCongrMem G.labels _ _ eq,←sumOverMulRight,chiSum]

private theorem dimensionInv (half : R) (h2 : 2*half=1) (n : Nat) :
    (ofReal half)^n*(2:ComplexScalar R)^n=1 := by
  have e := SectorDefectAccounting.dimensionInverse half h2 n
  have r : ofReal (((2:R)^n)*(half^n))=ofReal ((2:R)^n)*ofReal (half^n) := by apply ComplexScalar.ext <;> simp <;> grind only
  rw [e,dimension,PhysicalPairedReduction.realEmbeddingPow] at r
  change 1=(2:ComplexScalar R)^n*(ofReal half)^n at r; grind only

theorem blockTrace {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n) :
    trace (qubitIndices n) (block half L a)=1 := by
  unfold trace block; rw [←sumOverMulLeft]; change _*trace _ (raw L a)=_
  rw [rawTrace,dimensionInv half h2]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem blockHerm {n : Nat} (half : R) {G : MaximalFamily n} (L : Lift G) (a : Word n) :
    PhysicalPairedReduction.dagger (block half L a)=block half L a := by
  funext i j; change star ((ofReal half)^n*raw L a j i)=_
  have s (m : Nat) : star ((ofReal half)^m)=(ofReal half)^m := by
    induction m with
    | zero => simp only [Semiring.pow_zero]; apply ComplexScalar.ext <;> simp <;> grind only
    | succ m ih => rw [Semiring.pow_succ,star_mul,ih,star_ofReal]
  have rh := congrFun (congrFun (rawHerm (R:=R) L a) i) j
  change star (raw L a j i)=raw L a i j at rh
  rw [star_mul,s,rh]; rfl

theorem blockProduct {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a b : Word n) :
    matMul (qubitIndices n) (block half L a) (block half L b)=
      if wordAdd a b∈G.labels then block half L b else fun _ _ => 0 := by
  funext i j
  let h := (ofReal half)^n
  have e : matMul (qubitIndices n) (block half L a) (block half L b) i j=
      (h*h)*matMul (qubitIndices n) (raw L a) (raw L b) i j := by
    unfold block matMul; rw [sumOverMulLeft]; apply sumOverCongr; intro v; unfold h; grind only
  rw [e,rawProduct]; have inv := dimensionInv half h2 n
  by_cases mem : wordAdd a b∈G.labels <;> simp only [mem,ite_false,ite_true,block,h] <;> grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem sameCoset {n : Nat} {G : MaximalFamily n} (L : Lift G) (a b : Word n) (mem : wordAdd a b∈G.labels) :
    raw (R:=R) L a=raw L b := by
  funext i j; unfold raw; apply AnticommutingDefect.sumCongrMem; intro q hq
  have c := (G.criterion _).mp mem q hq; rw [antiAddLeft] at c
  cases g : anti a q <;> cases f : anti b q <;> simp [g,f,chi] at c ⊢

theorem blockIsometry {n : Nat} (half : R) (h2 : 2*half=1) {G : MaximalFamily n} (L : Lift G) (a : Word n) :
    matMul (qubitIndices n) (PhysicalPairedReduction.dagger (block half L a)) (block half L a)=block half L a := by
  rw [blockHerm,blockProduct half h2,wordAddSelf,ite_eq_left (zeroMem G)]

end Order

end RankSeven.StabilizerCharacterBasis

#print axioms RankSeven.StabilizerCharacterBasis.liftExists
#print axioms RankSeven.StabilizerCharacterBasis.liftProduct
#print axioms RankSeven.StabilizerCharacterBasis.blockTrace
#print axioms RankSeven.StabilizerCharacterBasis.blockProduct
#print axioms RankSeven.StabilizerCharacterBasis.blockIsometry

