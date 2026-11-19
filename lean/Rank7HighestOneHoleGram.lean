import Rank7HighestTailTransfer

namespace RankSeven.HighestOneHoleGram

open Lean.Grind Pauli ComplexScalar SymmetricDefect HighestTailTransfer
open PhysicalCutCapacities HighestCosetFourier GenericExteriorKernel FourCopySectors
open PauliPairContraction (normSum)
open ExteriorPauliBase (oddPermutation)
open WedgeSquareIntertwiner (wedgeSquareColumn)
open MixedDefect (oddWords)
variable {R α β : Type} [CommRing R]
local instance {n : Nat} : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n

def evaluation (xs : List α) (z : α→ComplexScalar R) (K : α→α→ComplexScalar R) :=
  sumOver xs (fun a => sumOver xs (fun b => star (z a)*K a b*z b))

private theorem reSum (xs : List α) (f : α→ComplexScalar R) : (sumOver xs f).re=sumOver xs (fun i => (f i).re) := (realSum _ _).1
private def coef {α β : Type} (xs : List α) (z : α → ComplexScalar R) (F : α → β → ComplexScalar R) (p : β) :=
  sumOver xs (fun a => star (z a)*F a p)

private theorem pullGram {α β : Type} (xs : List α) (os : List β)
    (z : α → ComplexScalar R) (F : α → β → ComplexScalar R) (K : α → α → ComplexScalar R)
    (rel : ∀ a b,2*sumOver os (fun p => F a p*star (F b p))=3*K a b) :
    2*sumOver os (fun p => normSq (coef xs z F p))=3*(evaluation xs z K).re := by
  have e : 2*sumOver os (fun p => coef xs z F p*star (coef xs z F p))=3*evaluation xs z K := by
    unfold coef evaluation
    simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
    conv => lhs; arg 2; intro p; rw [sumOverSwap xs xs]
    rw [sumOverSwap os xs]
    apply sumOverCongr; intro a
    rw [sumOverSwap os xs]; apply sumOverCongr; intro b
    have g := congrArg (fun w => star (z a)*w*z b) (rel a b)
    change star (z a)*(2*sumOver os _)*z b=_ at g
    rw [sumOverMulLeft,sumOverMulLeft,sumOverMulRight] at g
    refine (sumOverCongr os (g:=fun p => star (z a)*(2*(F a p*star (F b p)))*z b) (fun p => ?_)).trans ?_
    · grind only
    · rw [g]; grind only
  have re := congrArg ComplexScalar.re e
  change (ofReal (2:R)*_).re=(ofReal (3:R)*_).re at re
  have er (d : R) (u : ComplexScalar R) : (ofReal d*u).re=d*u.re := by simp [re_mul,ofReal]; grind only
  rw [er,er,reSum] at re
  have diag (p : β) : (coef xs z F p*star (coef xs z F p)).re=normSq (coef xs z F p) := by
    rw [CommSemiring.mul_comm,re_star_mul_self]
  rw [sumOverCongr _ diag] at re
  grind only


def contracted {n : Nat} (half : R) (z : Triple (Basis n)→ComplexScalar R) (t : Basis n) (p : Word n) :=
  coef (triples (qubitIndices n)) z (fun s p => wedgeSquareColumn half p (extend s t)) p

theorem oneHoleIdentity {n : Nat} (half : R) (h2 : 2*half=1) (z : Triple (Basis n)→ComplexScalar R) :
    2*sumOver (oddWords n) (fun p => sumOver (qubitIndices n) (fun t => normSq (contracted half z t p)))=
    (3*(4*half^n))*(evaluation (triples (qubitIndices n)) z tripleAlt).re := by
  let xs := qubitIndices n
  let ts := triples xs
  let T := exteriorKernel (n:=n) (imaginaryUnit (R:=R)) (ofReal half)
  have hh : 2*ofReal half=(1:ComplexScalar R) := by
    change ofReal (2:R)*ofReal half=ofReal 1; apply ComplexScalar.ext <;> simp <;> grind only
  have occ (t : Basis n) : 2*sumOver (oddWords n) (fun p => normSq (contracted half z t p))=
      3*(evaluation ts z (fun a b => T (extend a t) (extend b t))).re :=
    pullGram ts (oddWords n) z _ _ (fun a b => WedgeSquareIntertwiner.physicalWedgeSquareGram half h2 _ _)
  have total : sumOver xs (fun t => evaluation ts z (fun a b => T (extend a t) (extend b t)))=
      ofReal (4*half^n)*evaluation ts z tripleAlt := by
    unfold evaluation; rw [sumOverSwap xs ts]
    conv => lhs; arg 2; intro a; rw [sumOverSwap xs ts]
    simp only [←sumOverMulRight,←sumOverMulLeft]
    have marginal (a b : Triple (Basis n)) : sumOver xs (fun t => T (extend a t) (extend b t))=
        4*ofReal half^n*tripleAlt a b := oneHoleResolution imaginaryUnit (ofReal half) imaginaryUnit_fourth hh a b
    have factor (a b : Triple (Basis n)) : star (z a)*(4*ofReal half^n*tripleAlt a b)*z b=
      (4*ofReal half^n)*(star (z a)*tripleAlt a b*z b) := by grind only
    simp only [marginal,factor,←sumOverMulLeft]
    have real : 4*ofReal half^n=ofReal (4*half^n) := by
      rw [←PhysicalPairedReduction.realEmbeddingPow]
      change ofReal (4:R)*ofReal (half^n)=ofReal (4*half^n); apply ComplexScalar.ext <;> simp <;> grind only
    rw [real]
  rw [sumOverSwap,sumOverMulLeft,sumOverCongr xs occ,←sumOverMulLeft,←reSum,total]
  simp only [re_mul,re_ofReal,im_ofReal,Semiring.zero_mul]; grind only

def tripleSource (w : α×α→ComplexScalar R) (y : α→ComplexScalar R) (b : Triple α) := w b.1*y b.2

private theorem nodup3 (xs : List α) (nd : xs.Nodup) : (triples xs).Nodup :=
  HyperplaneInduction.pairsNodup _ _ (HyperplaneInduction.pairsNodup _ _ nd nd) nd
private theorem full3 (xs : List α) (full : ∀i,i∈xs) (u : Triple α) : u∈triples xs := by
  change u∈(productIndices xs xs).flatMap (fun a => xs.map (fun b => (a,b)))
  exact List.mem_flatMap.mpr ⟨u.1,HyperplaneInduction.pairMember (full _) (full _),List.mem_map.mpr ⟨u.2,full _,rfl⟩⟩

private theorem byPerm [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (z : Triple α→ComplexScalar R) :
    evaluation (triples xs) z tripleAlt=
    sumOver (triples xs) (fun b => (sumOver triplePerms (fun p => signed (oddPermutation p) (star (z (permute b p)))))*z b) := by
  let ts := triples xs
  let S (p : Perm) := signed (oddPermutation p) (1:ComplexScalar R)
  let D (a b : Triple α) (p : Perm) := if a=permute b p then S p else 0
  change sumOver ts (fun a => sumOver ts (fun b => star (z a)*(sumOver triplePerms (D a b))*z b))=_
  simp only [sumOverMulLeft,sumOverMulRight]
  rw [sumOverSwap ts ts]
  apply sumOverCongr; intro b; rw [sumOverSwap]
  apply sumOverCongr; intro p
  have hit := ExteriorPauliBase.sumOnIndex ts (permute b p) (fun a => S p*star (z a)*z b) (nodup3 xs nd) (full3 xs full _)
  have eq (a : Triple α) : star (z a)*D a b p*z b=(if permute b p=a then S p*star (z a)*z b else 0) := by
    unfold D; by_cases h : a=permute b p <;> simp [h,Ne.symm] <;> grind only
  rw [sumOverCongr ts eq,hit]
  unfold S signed; split <;> grind only

private theorem permRow (w : α×α→ComplexScalar R) (sk : ∀i j,w (j,i)= -w (i,j)) (y : α→ComplexScalar R) (a b c : α) :
    sumOver triplePerms (fun p => signed (oddPermutation p) (star (tripleSource w y (permute ((a,b),c) p))))=
      2*(star (w (a,b)*y c)-star (w (a,c)*y b)+star (w (b,c)*y a)) := by
  change star (w (a,b)*y c)+(-star (w (a,c)*y b)+(-star (w (b,a)*y c)+(star (w (b,c)*y a)+(star (w (c,a)*y b)+(-star (w (c,b)*y a)+0)))))=_
  rw [sk a b,sk a c,sk b c]
  have neg (x : ComplexScalar R) : star (-x)= -star x := by apply ComplexScalar.ext <;> simp <;> grind only
  simp only [Ring.neg_mul,neg]; grind only

theorem tripleMassIdentity [DecidableEq α] (xs : List α) (nd : xs.Nodup) (full : ∀i,i∈xs) (w : α×α→ComplexScalar R)
    (sk : ∀i j,w (j,i)= -w (i,j)) (y : α→ComplexScalar R) :
    let contraction (a : α) := sumOver xs (fun b => w (a,b)*star (y b))
    (evaluation (triples xs) (tripleSource w y) tripleAlt).re=
      2*(normSum (productIndices xs xs) w*normSum xs y)-4*normSum xs contraction := by
  let es := productIndices xs xs
  let ts := triples xs
  let z := tripleSource w y
  let A (q : Triple α) := star (w q.1*y q.2)*z q
  let B (q : Triple α) := star (w (q.1.1,q.2)*y q.1.2)*z q
  let D (q : Triple α) := star (w (q.1.2,q.2)*y q.1.1)*z q
  let u (a : α) := sumOver xs (fun b => w (a,b)*star (y b))
  have perm := byPerm xs nd full z
  have pt (q : Triple α) :
      (sumOver triplePerms (fun p => signed (oddPermutation p) (star (z (permute q p)))))*z q=2*(A q-B q+D q) := by
    rcases q with ⟨⟨a,b⟩,c⟩; change (sumOver triplePerms _)*z _=_
    rw [permRow w sk y a b c]; unfold A B D; grind only
  rw [sumOverCongr _ pt,←sumOverMulLeft,sumOverAdd,Compression.sumOverSub] at perm
  have flip : sumOver ts D= -sumOver ts B := by
    have f := sumOverMulLeft ts B (-1)
    rw [show -sumOver ts B=sumOver ts (fun t => (-1)*B t) by rw [←f]; grind only]
    unfold ts triples; simp only [sumPairs]; rw [sumOverSwap xs xs]
    apply sumOverCongr; intro a; apply sumOverCongr; intro b; apply sumOverCongr; intro c
    change star (w (a,c)*y b)*(w (b,a)*y c)=(-1)*(star (w (a,c)*y b)*(w (a,b)*y c))
    rw [sk a b]; grind only
  have contracted : sumOver ts B=ofReal (normSum xs u) := by
    rw [←HighestExteriorOccupation.selfProduct xs u]
    unfold ts triples HighestCodeLocalization.innerProduct; simp only [sumPairs]
    apply sumOverCongr; intro a; unfold u
    simp only [ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
    apply sumOverCongr; intro b; apply sumOverCongr; intro c
    change star (w (a,c)*y b)*(w (a,b)*y c)=_
    rw [star_mul]; grind only
  have atomic : sumOver ts A=ofReal (normSum es w)*ofReal (normSum xs y) := by
    rw [←HighestExteriorOccupation.selfProduct es w,←HighestExteriorOccupation.selfProduct xs y]
    unfold HighestCodeLocalization.innerProduct; rw [sumOverMulRight]
    unfold ts triples; rw [sumPairs]; apply sumOverCongr; intro e; rw [sumOverMulLeft]
    apply sumOverCongr; intro c; change star (w e*y c)*(w e*y c)=_; rw [star_mul]; grind only
  change evaluation ts z tripleAlt=2*(sumOver ts A-sumOver ts B+sumOver ts D) at perm
  rw [flip,atomic,contracted] at perm
  have rr := congrArg ComplexScalar.re perm
  change (evaluation ts z tripleAlt).re=2*(normSum es w*normSum xs y)-4*normSum xs u
  have two : (2:ComplexScalar R)=1+1 := by grind only
  rw [two] at rr
  simp only [re_add,im_add,re_sub,im_sub,re_neg,im_neg,re_mul,im_mul,re_one,im_one,re_ofReal,im_ofReal] at rr
  grind only

theorem oneHoleBound [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    {n : Nat} (half : R) (h2 : 2*half=1) (w : Basis n×Basis n→ComplexScalar R) (sk : ∀i j,w (j,i)= -w (i,j))
    (y : Basis n→ComplexScalar R) (uy : normSum (qubitIndices n) y=1) :
    2*sumOver (oddWords n) (fun p => sumOver (qubitIndices n) (fun t => normSq (contracted half (tripleSource w y) t p)))≤
    (3*(4*half^n))*(2*normSum (productIndices (qubitIndices n) (qubitIndices n)) w) := by
  let xs := qubitIndices n
  rw [oneHoleIdentity half h2,tripleMassIdentity xs (HyperplaneIncidence.normalsNodup _) qubitIndicesComplete w sk y,uy,Semiring.mul_one]
  have pos (k : Nat) : 0≤half^k := by
    have one := OrderedRing.zero_lt_one (R:=R)
    induction k with
    | zero => rw [Semiring.pow_zero]; grind only
    | succ i ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind only)
  have p := pos n
  have non := Compression.sumOverNonnegative xs (fun a => normSq (sumOver xs (fun b => w (a,b)*star (y b)))) (fun a _ => normSq_nonnegative _)
  apply OrderedRing.mul_le_mul_of_nonneg_left _ (by grind only)
  unfold normSum; grind only

end RankSeven.HighestOneHoleGram

#print axioms RankSeven.HighestOneHoleGram.oneHoleIdentity
#print axioms RankSeven.HighestOneHoleGram.tripleMassIdentity
#print axioms RankSeven.HighestOneHoleGram.oneHoleBound

