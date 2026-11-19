import Rank7SharedRoundedSector

namespace RankSeven.SharedUnionTransport

open Lean.Grind Pauli ComplexScalar SymmetricDefect PauliEdgeBlocks
open CharacterFourOrbits StabilizerCharacterBasis StabilizerCosetTransform StabilizerPairedCharacters
open StabilizerSmallCodes StabilizerOddSector FiniteProjectionAngles HeavyPauliGroup SlaterUnionBound
open PhysicalProjectionAngles (code test)
open PauliPairContraction (image)

variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

noncomputable def unionProjector {n : Nat} {half : R} {A : Basis n→Fin 7→ComplexScalar R}
    (C : SmallCodes half A) : Mx (Basis n) R :=
  addM (code half C.L C.a C.b)
    (code half C.L C.c (representative C.T (wordAdd C.c (wordAdd C.a C.b))))

private theorem shiftEq {n : Nat} {G : MaximalFamily n} (T : Transversal G) (w : Word n)
    (a b : Line T) : shift T w a=b ↔ equiv G (wordAdd a.val w) b.val := by
  constructor
  · intro e
    have h := (represents T (wordAdd a.val w)).2
    have eq : representative T (wordAdd a.val w)=b.val := congrArg Subtype.val e
    rwa [eq] at h
  · intro h
    exact Subtype.ext (repClass T _ _ b.property h)

omit [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem selectedSwap {n : Nat} {half : R} {A : Basis n→Fin 7→ComplexScalar R}
    (C : SmallCodes half A) (z : TransposeOffset C.G) (p : Word n)
    (selected : member z C.c C.a C.b p=true) :
    let a : Line C.T := ⟨C.a,C.ha⟩
    let b : Line C.T := ⟨C.b,C.hb⟩
    let c : Line C.T := ⟨C.c,C.hc⟩
    let d := shift C.T (wordAdd C.a C.b) c
    let J := shift C.T (wordAdd z.offset p)
    (J a=c ∧ J b=d ∧ J c=a ∧ J d=b) ∨
      (J a=d ∧ J b=c ∧ J c=b ∧ J d=a) := by
  let a : Line C.T := ⟨C.a,C.ha⟩
  let b : Line C.T := ⟨C.b,C.hb⟩
  let c : Line C.T := ⟨C.c,C.hc⟩
  let m := shift C.T (wordAdd C.a C.b)
  let d := m c
  let J := shift C.T (wordAdd z.offset p)
  obtain ⟨ab,ba⟩ := mateSwaps C.T C.a C.b C.ha C.hb
  have ma : m a=b := Subtype.ext ab
  have mb : m b=a := Subtype.ext ba
  have inv (i : Line C.T) : J (J i)=i := shiftTwice C.T _ i
  have commute (i : Line C.T) : m (J i)=J (m i) := by
    unfold m J
    rw [shiftSum,shiftSum,wordAddComm (wordAdd z.offset p) (wordAdd C.a C.b)]
  have matchC : J c=a ∨ J c=b := by
    have h := (selectorAction z C.c C.a C.b p).mp selected
    rw [wordAddAssoc] at h
    exact h.elim (fun h => Or.inl ((shiftEq C.T _ c a).mpr h))
      (fun h => Or.inr ((shiftEq C.T _ c b).mpr h))
  change (J a=c ∧ J b=d ∧ J c=a ∧ J d=b) ∨ (J a=d ∧ J b=c ∧ J c=b ∧ J d=a)
  rcases matchC with h|h
  · have ja : J a=c := by rw [←h,inv]
    have jb : J b=d := by rw [←ma,←commute,ja]
    have jd : J d=b := by unfold d; rw [←commute,h,ma]
    exact Or.inl ⟨ja,jb,h,jd⟩
  · have jb : J b=c := by rw [←h,inv]
    have ja : J a=d := by rw [←mb,←commute,jb]
    have jd : J d=a := by unfold d; rw [←commute,h,mb]
    exact Or.inr ⟨ja,jb,h,jd⟩

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem testLine {n : Nat} (half : R) {G : MaximalFamily n}
    (L : Lift G) (T : Transversal G) (z : TransposeOffset G) (p : Word n)
    (a : Line T) (x : Basis n→ComplexScalar R) :
    test p (image (qubitIndices n) (block half L a.val) x)=
      image (qubitIndices n) (block half L (shift T (wordAdd z.offset p) a).val) (test p x) := by
  let xs := qubitIndices n
  let W := wordEntry (imaginaryUnit (R:=R)) p
  let D := block half L (wordAdd a.val p)
  let B := block half L (wordAdd (wordAdd a.val p) z.offset)
  let S := block half L (shift T (wordAdd z.offset p) a).val
  have shiftBlock : B=S := by
    funext i j
    unfold B S block
    have e := (represents T (wordAdd a.val (wordAdd z.offset p))).2
    rw [wordAddAssoc,wordAddComm p z.offset,sameCoset (R:=R) L _ _ e]
    rfl
  have commute : act p (image xs (block half L a.val) x)=image xs D (act p x) := by
    change image xs W (image xs (block half L a.val) x)=image xs D (image xs W x)
    rw [imageComp,imageComp,wordBlock half L p a.val]
  have entry (i j : Basis n) : star (D i j)=B i j := by
    have e := congrFun (congrFun (conjugateBlock half L z (wordAdd a.val p)) i) j
    change D j i=B i j at e
    exact (congrFun (congrFun (blockHerm (R:=R) half L (wordAdd a.val p)) j) i).trans e
  funext i
  unfold test
  rw [commute]
  change star (image xs D (act p x) i)=image xs S (fun j => star (act p x j)) i
  rw [←shiftBlock]
  unfold image
  rw [ComplexExterior.starSumOver]
  apply sumOverCongr
  intro j
  rw [star_mul,entry]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem imageAdd {n : Nat} (P Q : Mx (Basis n) R)
    (x : Basis n→ComplexScalar R) :
    image (qubitIndices n) (addM P Q) x =
      fun i => image (qubitIndices n) P x i+image (qubitIndices n) Q x i := by
  funext i
  unfold image addM
  simp only [Semiring.right_distrib,sumOverAdd]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem testAdd {n : Nat} (p : Word n) (x y : Basis n→ComplexScalar R) :
    test p (fun i => x i+y i)=fun i => test p x i+test p y i := by
  funext i
  unfold test
  rw [actAdd,star_add]

omit [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
/-- Each selected odd Pauli test preserves the union of the true four
character lines. This identity also includes the transpose offset. -/
theorem selectedPreservesUnion {n : Nat} {half : R} {A : Basis n→Fin 7→ComplexScalar R}
    (C : SmallCodes half A) (z : TransposeOffset C.G) (p : Word n)
    (selected : member z C.c C.a C.b p=true) (x : Basis n→ComplexScalar R) :
    test p (image (qubitIndices n) (unionProjector C) x)=
      image (qubitIndices n) (unionProjector C) (test p x) := by
  let a : Line C.T := ⟨C.a,C.ha⟩
  let b : Line C.T := ⟨C.b,C.hb⟩
  let c : Line C.T := ⟨C.c,C.hc⟩
  let d := shift C.T (wordAdd C.a C.b) c
  let J := shift C.T (wordAdd z.offset p)
  let B (j : Line C.T) := block half C.L j.val
  let xs := qubitIndices n
  let F (j : Line C.T) := image xs (B j) x
  let H (j : Line C.T) := image xs (B j) (test p x)
  have swap := selectedSwap C z p selected
  change (J a=c ∧ J b=d ∧ J c=a ∧ J d=b) ∨ (J a=d ∧ J b=c ∧ J c=b ∧ J d=a) at swap
  have line (j : Line C.T) : test p (F j)=H (J j) := testLine half C.L C.T z p j x
  change test p (image xs (addM (addM (B a) (B b)) (addM (B c) (B d))) x)=
    image xs (addM (addM (B a) (B b)) (addM (B c) (B d))) (test p x)
  simp only [xs,imageAdd,testAdd]
  change (fun i => (test p (F a) i+test p (F b) i)+(test p (F c) i+test p (F d) i))=
    fun i => (H a i+H b i)+(H c i+H d i)
  simp only [line]
  funext j
  rcases swap with ⟨ja,jb,jc,jd⟩|⟨ja,jb,jc,jd⟩
  · rw [ja,jb,jc,jd]
    grind only
  · rw [ja,jb,jc,jd]
    grind only

/-- The four labels determined by the selected parallel codes are distinct,
so the sum of their character projections is the actual union projection. -/
theorem unionIsProjection {n : Nat} (half : R) (unit : 2*half=1)
    {A : Basis n→Fin 7→ComplexScalar R} (C : SmallCodes half A) :
    Projection (qubitIndices n) (unionProjector C) := by
  let a := C.a
  let b := C.b
  let c := C.c
  let d := representative C.T (wordAdd c (wordAdd a b))
  let B := block half C.L
  let xs := qubitIndices n
  let P := code half C.L a b
  let Q := code half C.L c d
  have hd : d∈C.T.reps := (represents C.T _).1
  obtain ⟨da,db,dc⟩ := C.secondDistinct d rfl
  have ab : ¬equiv C.G a b := fun h => C.distinct.1 (C.T.separated a C.ha b C.hb h)
  have cd : ¬equiv C.G c d := fun h => dc (C.T.separated c C.hc d hd h).symm
  have ac : wordAdd a c∉C.G.labels := fun h => C.distinct.2.1 (C.T.separated a C.ha c C.hc h).symm
  have bc : wordAdd b c∉C.G.labels := fun h => C.distinct.2.2 (C.T.separated b C.hb c C.hc h).symm
  have ad : wordAdd a d∉C.G.labels := fun h => da (C.T.separated a C.ha d hd h).symm
  have bd : wordAdd b d∉C.G.labels := fun h => db (C.T.separated b C.hb d hd h).symm
  have pr : Projection xs P := PhysicalProjectionAngles.codeProjection half unit C.L a b ab
  have qr : Projection xs Q := PhysicalProjectionAngles.codeProjection half unit C.L c d cd
  have noCross (i j : Word n) (h : wordAdd i j∉C.G.labels) :
      matMul xs (B i) (B j)=(fun _ _ => 0) := by
    unfold xs B
    rw [blockProduct half unit C.L,ite_eq_right h]
  have pq : matMul xs P Q=(fun _ _ => 0) := by
    change matMul xs (addM (B a) (B b)) (addM (B c) (B d))=_
    rw [addLeft,addRight,addRight,noCross a c ac,noCross a d ad,noCross b c bc,noCross b d bd]
    funext i j
    unfold addM
    grind only
  have qp : matMul xs Q P=(fun _ _ => 0) := by
    change matMul xs (addM (B c) (B d)) (addM (B a) (B b))=_
    have flip (i j : Word n) (h : wordAdd i j∉C.G.labels) : wordAdd j i∉C.G.labels := by
      rwa [wordAddComm]
    rw [addLeft,addRight,addRight,noCross c a (flip a c ac),noCross c b (flip b c bc),
      noCross d a (flip a d ad),noCross d b (flip b d bd)]
    funext i j
    unfold addM
    grind only
  change Projection xs (addM P Q)
  constructor
  · rw [dagAdd,pr.herm,qr.herm]
  · rw [addLeft,addRight,addRight,pr.square,qr.square,pq,qp]
    funext i j
    unfold addM
    grind only

open HighestCodeLocalization (innerProduct)
open PhysicalPairedReduction (dagger)

local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

/-- A selected odd word has no head amplitude between the four-site
character union and its orthogonal complement. -/
theorem selectedCrossZero {n : Nat} (half : R) (unit : 2*half=1)
    {A : Basis n→Fin 7→ComplexScalar R} (C : SmallCodes half A)
    (z : TransposeOffset C.G) (p : Word n) (selected : member z C.c C.a C.b p=true)
    (x y : Basis n→ComplexScalar R) :
    let xs := qubitIndices n
    let Q := unionProjector C
    innerProduct xs (image xs Q x) (test p (image xs (compl Q) y))=0 := by
  let xs := qubitIndices n
  let Q := unionProjector C
  let V := compl Q
  let v := test p (image xs V y)
  have prop := unionIsProjection half unit C
  have cross : matMul xs Q V=(fun _ _ => 0) := by
    unfold V compl
    rw [subRight,idRight xs (HyperplaneIncidence.normalsNodup n) (@qubitIndicesComplete n),prop.square]
    funext i j
    unfold subM
    grind only
  have Qy : image xs Q (image xs V y)=(fun _ => 0) := by
    rw [imageComp,cross]
    funext j
    unfold image
    simp only [Semiring.zero_mul]
    induction xs with
    | nil => rfl
    | cons a as ih =>
      change 0+sumOver as (fun _ => (0:ComplexScalar R))=0
      rw [ih]
      grind only
  have test0 : test p (fun _ => (0:ComplexScalar R))=(fun _ => 0) := by
    have h := testAdd p (fun _ => (0:ComplexScalar R)) (fun _ => 0)
    funext j
    have t := congrFun h j
    have eq : (fun _ : Basis n => (0:ComplexScalar R)+0)=(fun _ => 0) := by funext i; grind only
    rw [eq] at t
    grind only
  have Qv : image xs Q v=(fun _ => 0) := by
    unfold v
    rw [←selectedPreservesUnion C z p selected,Qy,test0]
  let X (i : Basis n) (_ : Unit) := x i
  let Y (i : Basis n) (_ : Unit) := v i
  change matMul xs (dagger (matMul xs Q X)) Y () ()=0
  rw [PhysicalPairedReduction.daggerProduct,prop.herm,matMulAssoc]
  change innerProduct xs x (image xs Q v)=0
  rw [Qv]
  unfold innerProduct
  simp only [Semiring.mul_zero]
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change 0+sumOver as (fun _ => (0:ComplexScalar R))=0
    rw [ih]
    grind only

open PauliPairContraction (normSum)

def crossedMass {α : Type} (xs : List α) (a b c d : α→ComplexScalar R) : R :=
  sumOver xs (fun i => sumOver xs (fun j => normSq (a i*b j-c i*d j)))

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
theorem crossedMassEq {α : Type} (xs : List α) (a b c d : α→ComplexScalar R) :
    crossedMass xs a b c d=normSum xs a*normSum xs b+normSum xs c*normSum xs d-
      2*(innerProduct xs a c*innerProduct xs b d).re := by
  have row (i j : α) : normSq (a i*b j-c i*d j)=
      normSq (a i)*normSq (b j)+normSq (c i)*normSq (d j)-
        2*((star (a i)*c i)*(star (b j)*d j)).re := by
    unfold normSq
    simp only [re_mul,im_mul,re_sub,im_sub,re_star,im_star]
    grind only
  have factors :
      innerProduct xs a c*innerProduct xs b d=
        sumOver xs (fun i => sumOver xs (fun j => (star (a i)*c i)*(star (b j)*d j))) := by
    unfold innerProduct
    rw [sumOverMulRight]
    apply sumOverCongr
    intro i
    rw [sumOverMulLeft]
  rw [factors,(HighestCosetFourier.realSum _ _).1]
  have real (i : α) : (sumOver xs (fun j => (star (a i)*c i)*(star (b j)*d j))).re=
      sumOver xs (fun j => ((star (a i)*c i)*(star (b j)*d j)).re) :=
    (HighestCosetFourier.realSum _ _).1
  simp only [real]
  unfold crossedMass normSum
  simp only [row,Compression.sumOverSub,sumOverAdd,←sumOverMulLeft,←sumOverMulRight]

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem starInner {α : Type} (xs : List α) (a b : α→ComplexScalar R) :
    star (innerProduct xs a b)=innerProduct xs b a := by
  unfold innerProduct
  rw [ComplexExterior.starSumOver]
  apply sumOverCongr
  intro i
  rw [star_mul,star_star,CommSemiring.mul_comm]

/-- The crossed part of a normalized orthogonal wedge pays the sum of
its one-particle leakages, with the exact product correction. -/
theorem crossedMassPrice {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup) (all : ∀i,i∈xs)
    (Q : Mx α R) (proj : Projection xs Q) (x y : α→ComplexScalar R)
    (hx : normSum xs x=1) (hy : normSum xs y=1) (orth : innerProduct xs x y=0) :
    let V := compl Q
    let f := energy xs V x
    let e := energy xs V y
    e+f-2*f*e≤crossedMass xs (image xs Q x) (image xs V y) (image xs Q y) (image xs V x) := by
  let V := compl Q
  let a := image xs Q x
  let b := image xs V y
  let c := image xs Q y
  let d := image xs V x
  let f := energy xs V x
  let e := energy xs V y
  have other := complement xs nd all Q proj
  have sum : innerProduct xs a c+innerProduct xs d b=0 := by
    unfold a b c d
    rw [HighestCodeLocalization.projectedInner xs Q proj x y,HighestCodeLocalization.projectedInner xs V other x y]
    let X (i : α) (_ : Unit) := x i
    let Y (i : α) (_ : Unit) := y i
    change matMul xs (dagger X) (matMul xs Q Y) () ()+
      matMul xs (dagger X) (matMul xs (compl Q) Y) () ()=0
    unfold compl
    rw [subLeft,idLeft xs nd all,subRight]
    change innerProduct xs x (image xs Q y)+(innerProduct xs x y-innerProduct xs x (image xs Q y))=0
    rw [orth]
    grind only
  have reverse : innerProduct xs b d=star (innerProduct xs d b) := (starInner xs d b).symm
  have changeInner : innerProduct xs a c= -innerProduct xs d b := by grind only
  have sign : (innerProduct xs a c*innerProduct xs b d).re= -normSq (innerProduct xs d b) := by
    rw [changeInner,reverse]
    simp only [re_mul,re_neg,im_neg,re_star,im_star,normSq]
    grind only
  have qa : normSum xs a=1-f := by
    have q := energySub xs (ident (R:=R)) Q x
    rw [energyIdentity xs nd all,hx] at q
    change f=1-energy xs Q x at q
    rw [←energyNorm xs Q proj x]
    grind only
  have qc : normSum xs c=1-e := by
    have q := energySub xs (ident (R:=R)) Q y
    rw [energyIdentity xs nd all,hy] at q
    change e=1-energy xs Q y at q
    rw [←energyNorm xs Q proj y]
    grind only
  have qb : normSum xs b=e := (energyNorm xs V other y).symm
  have qd : normSum xs d=f := (energyNorm xs V other x).symm
  change e+f-2*f*e≤crossedMass xs a b c d
  rw [crossedMassEq,qa,qb,qc,qd,sign]
  have pos := normSq_nonnegative (innerProduct xs d b)
  grind only

end RankSeven.SharedUnionTransport

#print axioms RankSeven.SharedUnionTransport.selectedSwap
#print axioms RankSeven.SharedUnionTransport.selectedPreservesUnion
#print axioms RankSeven.SharedUnionTransport.unionIsProjection
#print axioms RankSeven.SharedUnionTransport.selectedCrossZero
#print axioms RankSeven.SharedUnionTransport.crossedMassPrice

