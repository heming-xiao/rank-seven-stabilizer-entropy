import Rank7PhysicalMixedFrame
import Rank7AlternatingTrace
import Rank7PhysicalDefectAssembly

/-! The alternating projection of doubled antisymmetric Pauli matrices in
the increasing fourth exterior basis. -/
namespace RankSeven.WedgeSquareIntertwiner

open Lean.Grind Pauli ComplexScalar ExteriorPauliBase GenericExteriorKernel FourCopySectors
open PhysicalMixedFrame (doubledWord)
open MixedDefect (oddWords oddWord)
open PhysicalWedges (Coordinate coords)
open PhysicalExteriorCompression (wedgeRows)
open HyperplaneInduction (minor4)
open ExteriorCuts (Wedge7 wedges amplitude)
open FrameExteriorSector (effectEntry)

variable {C R α β : Type} [CommRing C] [CommRing R]
attribute [local instance] Ring.intCast

private abbrev alt := coefficient .antisymmetric

private theorem actScale (c : C) (f : Four α → C) (x : Four α) :
    act alt (fun z => c*f z) x = c*act alt f x := by
  unfold act; rw [sumOverMulLeft]
  apply sumOverCongr; intro p; grind only

private theorem actRight (f : Four α → C) (c : C) (x : Four α) :
    act alt (fun z => f z*c) x = act alt f x*c := by
  unfold act; rw [sumOverMulRight]
  apply sumOverCongr; intro p; grind only

private theorem actSub (f g : Four α → C) (x : Four α) :
    act alt (fun t => f t - g t) x = act alt f x - act alt g x := by
  unfold act; rw [←Compression.sumOverSub]
  apply sumOverCongr; intro p; grind only

private theorem actSum (xs : List β) (f : β → Four α → C) (x : Four α) :
    act alt (fun t => sumOver xs (fun i => f i t)) x = sumOver xs (fun i => act alt (f i) x) := by
  unfold act
  simp only [sumOverMulLeft]
  rw [sumOverSwap]

private theorem actStar (f : Four α → ComplexScalar R) (x : Four α) :
    act alt (fun t => star (f t)) x = star (act alt f x) := by
  unfold act; rw [ComplexExterior.starSumOver]
  apply sumOverCongr; intro p
  have h : star (Int.cast (R:=ComplexScalar R) (alt p)) = Int.cast (R:=ComplexScalar R) (alt p) :=
    (scalarConjugation (R:=R)).fixesInteger _
  rw [star_mul,h]

private theorem twirlEquivariant {n : Nat} (i : C) : Equivariant (unnormalizedTwirl (n:=n) i) := by
  intro p hp u v
  apply sumOverCongr
  intro w
  exact tensorEquivariant (wordEntry i w) p hp u v

private theorem twirlAlt {n : Nat} (i half : C) (u v : Four (Basis n)) :
    exteriorKernel i half u v = half^(n+n) * rawBlock .antisymmetric (unnormalizedTwirl i) u v := by
  rw [AlternatingTrace.alternatingRight _ (twirlEquivariant i)]
  unfold exteriorKernel wordMinor act unnormalizedTwirl
  congr 1
  rw [sumOverSwap]
  apply sumOverCongr
  intro p
  rw [sumOverMulLeft]
  apply sumOverCongr; intro w
  unfold signed coefficient
  cases oddPermutation p <;> simp <;> grind

/-- The 24-term alternation of the tensor of two identical Pauli two-forms.
On increasing sites it equals eight times the four-by-four Pfaffian for an odd word. -/
def alternatingWord {n : Nat} (p : Word n) (u : Four (Basis n)) : ComplexScalar R :=
  act alt (doubledWord p) u

/-- Doubled odd Pauli columns resolve the actual alternating twirl.
The factor 24 here is the square of the unnormalized antisymmetrizer
divided by one copy of that antisymmetrizer. -/
theorem alternatingWordResolution {n : Nat} (u v : Four (Basis n)) :
    2 * sumOver (oddWords n) (fun p => alternatingWord p u * star (alternatingWord (R:=R) p v)) =
      48 * rawBlock .antisymmetric (unnormalizedTwirl imaginaryUnit) u v := by
  let J := unnormalizedTwirl (n:=n) (imaginaryUnit (R:=R))
  have right (x : Four (Basis n)) :
      act alt (fun y => J x y - J (reorder x transposition) y) v =
        2*rawBlock .antisymmetric J x v := by
    rw [actSub, ←AlternatingTrace.alternatingRight _ (twirlEquivariant _),
      ←AlternatingTrace.alternatingRight _ (twirlEquivariant _)]
    have perm := AlternatingTrace.alternatingRow (fun t => J t v) transposition (by decide) x
    have sg : coefficient .antisymmetric transposition = -1 := by decide
    change rawBlock .antisymmetric J (reorder x transposition) v =
      Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric transposition) * rawBlock .antisymmetric J x v at perm
    rw [perm,sg,Ring.intCast_neg,Ring.intCast_ofNat]
    grind only
  have both := congrArg (fun (F : Four (Basis n) → Four (Basis n) → ComplexScalar R) =>
    act alt (fun x => act alt (F x) v) u)
    (funext (fun x => funext (PhysicalMixedFrame.oddDoubledResolution (R:=R) x)))
  change act alt (fun x => act alt (fun y => 2*sumOver (oddWords n) (fun p =>
    doubledWord p x * star (doubledWord p y))) v) u =
      act alt (fun x => act alt (fun y => J x y - J (reorder x transposition) y) v) u at both
  simp only [right,actScale,actSum,actStar,actRight] at both
  have square := actProduct .antisymmetric .antisymmetric (fun t => J t v) u
  change act alt (fun x => rawBlock .antisymmetric J x v) u = _ at square
  simp only [ite_true] at square
  rw [square] at both
  change 2 * sumOver (oddWords n) (fun p => alternatingWord p u * star (alternatingWord p v)) =
      2*(24*rawBlock .antisymmetric J u v) at both
  rw [both]
  grind only

/-- Coordinates of the wedge-square map: each normalized two-form contributes
an inverse square root of the dimension, hence its square contributes 1/d.
The further factor 1/4 converts the raw alternation to the wedge convention. -/
def wedgeSquareColumn {n : Nat} (half : R) (p : Word n) (u : Four (Basis n)) : ComplexScalar R :=
  (ofReal half)^(n+2) * alternatingWord p u

private theorem halfComplex (half : R) (unit : 2*half=1) :
    2 * ofReal half = (1 : ComplexScalar R) := by
  change ofReal (2:R) * ofReal half = ofReal (1:R)
  apply ComplexScalar.ext <;> simp <;> grind only

/-- The physical Gram on increasing wedge coordinates is exactly (3/2)Π_F.
The entries on the right are the normalized fourth Pauli minors. -/
theorem physicalWedgeSquareGram (half : R) (unit : 2*half=1) {n : Nat} (u v : Four (Basis n)) :
    2 * sumOver (oddWords n) (fun p => wedgeSquareColumn half p u * star (wedgeSquareColumn half p v)) =
      3 * exteriorKernel imaginaryUnit (ofReal half) u v := by
  let h := ofReal half
  have scale (p : Word n) : wedgeSquareColumn half p u * star (wedgeSquareColumn half p v) =
      h^(n+2) * h^(n+2) * (alternatingWord p u * star (alternatingWord p v)) := by
    unfold wedgeSquareColumn
    rw [star_mul, ←PhysicalPairedReduction.realEmbeddingPow, star_ofReal, PhysicalPairedReduction.realEmbeddingPow]
    grind only
  rw [sumOverCongr _ scale, ←sumOverMulLeft, twirlAlt]
  have factors : 2 * (h^(n+2) * h^(n+2) * sumOver (oddWords n) (fun p => alternatingWord p u * star (alternatingWord p v))) =
      (h^(n+2)*h^(n+2)) * (2*sumOver (oddWords n) (fun p => alternatingWord p u * star (alternatingWord p v))) := by grind only
  rw [factors, alternatingWordResolution,Semiring.pow_add,Semiring.pow_add]
  have two : 2*h=1 := halfComplex half unit
  have four := congrArg (fun t : ComplexScalar R => t^4) two
  change _ = 3 * (h^n*h^n*_) 
  grind only

/-- Pullback of a wedge-square column by the actual fourth exterior power of A. -/
def sourceWedgeSquare {n : Nat} (half : R) (A : Basis n → Fin 7 → ComplexScalar R)
    (u : Wedge7) (p : Word n) : ComplexScalar R :=
  sumOver (coords n) (fun r => star (minor4 A (wedgeRows r) u) * wedgeSquareColumn half p r.val)

section Source
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- The Gram of the pulled-back columns is the alternating block of the framed twirl. -/
theorem sourceWedgeSquareGram (half : R) (unit : 2*half=1) {n : Nat}
    (A : Basis n → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    2*sumOver (oddWords n) (fun p => sourceWedgeSquare half A u p * star (sourceWedgeSquare half A v p)) =
      3*FrameExteriorSector.exteriorSector (FrameExteriorSector.frameTwirl half A) u v := by
  rw [FrameExteriorSector.frameTwirl_exteriorSector, FrameExteriorSector.framedWordMinor_sum]
  simp only [sourceWedgeSquare,ComplexExterior.starSumOver,star_mul,star_star,sumOverMulRight,sumOverMulLeft]
  rw [sumOverSwap (coords n) (coords n) (fun r s => 3*(star (minor4 A (wedgeRows r) u) *
    exteriorKernel imaginaryUnit (ofReal half) r.val s.val * minor4 A (wedgeRows s) v))]
  rw [sumOverSwap (oddWords n) (coords n)]
  apply sumOverCongr; intro s
  rw [sumOverSwap (oddWords n) (coords n)]
  apply sumOverCongr; intro r
  have gram := physicalWedgeSquareGram half unit r.val s.val
  let L := star (minor4 A (wedgeRows r) u) * minor4 A (wedgeRows s) v
  have term (p : Word n) : 2 * ((star (minor4 A (wedgeRows r) u) * wedgeSquareColumn half p r.val) *
        (minor4 A (wedgeRows s) v * star (wedgeSquareColumn half p s.val))) =
      L*(2*(wedgeSquareColumn half p r.val * star (wedgeSquareColumn half p s.val))) := by dsimp [L]; grind only
  rw [sumOverCongr _ term, ←sumOverMulLeft, ←sumOverMulLeft, gram]
  dsimp [L]; grind only

/-- Physical 35-by-35 effect as a Gram of the actual odd Pauli wedge-square columns. -/
theorem sourceWedgeSquarePhysicalEntries (half : R) (unit : 2*half=1) (k : Nat)
    (A : Basis (k+3) → Fin 7 → ComplexScalar R) (u v : Wedge7) :
    2*sumOver (oddWords (k+3)) (fun p => sourceWedgeSquare half A u p * star (sourceWedgeSquare half A v p)) =
      3*(ofReal (PhysicalChartRestriction.weight half (k+3)) * effectEntry half unit k A u v) := by
  rw [sourceWedgeSquareGram half unit, FrameExteriorSector.sector_eq_weight_mul_physicalEntry half unit]

end Source

section PauliGram
open SymmetricDefect (anti chi phase axisAnti)

private def mapSites (f : α → β) (x : Four α) : Four β :=
  ((f x.1.1,f x.1.2),(f x.2.1,f x.2.2))

private theorem mapReorder (f : α → β) (x : Four α) (p : Permutation) :
    mapSites f (reorder x p) = reorder (mapSites f x) p := by
  have h (j : Fin 4) : f (position x j) = position (mapSites f x) j := by
    have four : ∀ j : Fin 4, j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide
    rcases four j with h|h|h|h <;> subst j <;> rfl
  unfold mapSites reorder
  simp only [h]; rfl

private theorem sumPairs (xs : List α) (ys : List β) (f : α × β → C) :
    sumOver (productIndices xs ys) f = sumOver xs (fun a => sumOver ys (fun b => f (a,b))) := by
  unfold productIndices; rw [sumOverFlatMap]
  apply sumOverCongr; intro a; simp [sumOver,List.map_map,Function.comp_def]

private theorem sumFour (xs : List α) (f : Four α → C) :
    sumOver (fourIndices xs) f = sumOver xs (fun a => sumOver xs (fun b =>
      sumOver xs (fun c => sumOver xs (fun d => f ((a,b),(c,d)))))) := by
  simp only [fourIndices,sumPairs]

private theorem fourFactor (xs : List α) (ys : List β) (f : Four α → C) (g : Four β → C) :
    sumOver (fourIndices (productIndices xs ys)) (fun x => f (mapSites Prod.fst x)*g (mapSites Prod.snd x)) =
      sumOver (fourIndices xs) f * sumOver (fourIndices ys) g := by
  simp only [sumFour,mapSites]
  let F (a b c : α) := sumOver xs (fun d => f ((a,b),(c,d)))
  let G (a b c : β) := sumOver ys (fun d => g ((a,b),(c,d)))
  have last (a b c : α×β) := factorProductSum xs ys (fun d => f ((a.1,b.1),(c.1,d))) (fun d => g ((a.2,b.2),(c.2,d)))
  simp only [last]
  have prev (a b : α×β) := factorProductSum xs ys (F a.1 b.1) (G a.2 b.2)
  simp only [F,G] at prev
  simp only [prev]
  have second (a : α×β) := factorProductSum xs ys (fun b => sumOver xs (F a.1 b)) (fun b => sumOver ys (G a.2 b))
  simp only [F,G] at second
  simp only [second]
  exact factorProductSum xs ys (fun a => sumOver xs (fun b => sumOver xs (F a b))) (fun a => sumOver ys (fun b => sumOver ys (G a b)))

/-- The tensor square of a Pauli axis has integer entries even for the Y axis. -/
private def axisDouble (a : Axis) (x : Four Bool) : Int :=
  axisSign a * entry 1 a x.1.1 x.1.2 * entry 1 a x.2.1 x.2.2

private def wordDouble : {n : Nat} → Word n → Four (Basis n) → Int
  | _, .empty, _ => 1
  | _, .cons a w, x => axisDouble a (firstBits x) * wordDouble w (remainingBits x)

private theorem axisDoubleEntry (a : Axis) (x : Four Bool) :
    Int.cast (R:=ComplexScalar R) (axisDouble a x) =
      entry imaginaryUnit a x.1.1 x.1.2 * entry imaginaryUnit a x.2.1 x.2.2 := by
  rcases x with ⟨⟨x,y⟩,z,t⟩
  cases a <;> cases x <;> cases y <;> cases z <;> cases t <;>
    simp [axisDouble,entry,axisSign] <;> grind only [imaginaryUnit_sq]

private theorem wordDoubleEntry {n : Nat} (a : Word n) (x : Four (Basis n)) :
    Int.cast (R:=ComplexScalar R) (wordDouble a x) = doubledWord a x := by
  induction a with
  | empty => simp [wordDouble,doubledWord,PhysicalMixedFrame.form,wordEntry,Ring.intCast_one] <;> grind only
  | cons a w ih =>
    rw [wordDouble,Ring.intCast_mul,axisDoubleEntry,ih]
    have reorderFactors (j k l m : ComplexScalar R) : (j*k)*(l*m) = (j*l)*(k*m) := by grind only
    exact reorderFactors _ _ _ _

private def paired (p : Permutation) : Bool := p.1.1.val/2 == p.1.2.val/2
private def bitGram (p : Permutation) (a b : Axis) : Int :=
  sumOver (fourIndices [false,true]) (fun x => axisDouble a x * axisDouble b (reorder x p))
private def flipA (p : Permutation) : Bool :=
  if paired p then oddPermutation p else decide (bitGram p .y .identity < 0)
private def flipB (p : Permutation) : Bool := !paired p && decide (bitGram p .identity .y < 0)
private def orient (reverse : Bool) (z : Int) : Int := if reverse then z else 1
private def localGram (p : Permutation) (a b : Axis) : Int :=
  orient (flipA p) (axisSign a) * orient (flipB p) (axisSign b) *
    (if paired p then (if a=b then 4 else 0) else 2 * phase (axisAnti a b))

private def axes : List Axis := [.identity,.x,.y,.z]
private theorem bitGramTable : permutations.all (fun p => axes.all (fun a => axes.all (fun b =>
    bitGram p a b == localGram p a b))) = true := by decide

private theorem gramBit (p : Permutation) (hp : p∈permutations) (a b : Axis) :
    bitGram p a b = localGram p a b := by
  have mem (s : Axis) : s∈axes := by cases s <;> decide
  exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp bitGramTable p hp) a (mem a)) b (mem b))

private def gramAt {n : Nat} (p : Permutation) (a b : Word n) : Int :=
  sumOver (fourIndices (qubitIndices n)) (fun x => wordDouble a x * wordDouble b (reorder x p))

private theorem gramAtCons {n : Nat} (p : Permutation) (a b : Axis) (v w : Word n) :
    gramAt p (.cons a v) (.cons b w) = bitGram p a b * gramAt p v w := by
  unfold gramAt bitGram
  rw [qubitIndices,←fourFactor]
  apply sumOverCongr; intro x
  have left : firstBits (reorder x p) = reorder (firstBits x) p := mapReorder Prod.fst x p
  have right : remainingBits (reorder x p) = reorder (remainingBits x) p := mapReorder Prod.snd x p
  simp only [wordDouble,left,right]
  have reorderFactors (j k l m : Int) : (j*k)*(l*m) = (j*l)*(k*m) := by grind only
  exact reorderFactors _ _ _ _

noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _

private theorem orientMul (b : Bool) (v w : Int) : orient b (v*w) = orient b v * orient b w := by
  cases b <;> simp [orient]

private theorem gramPermutation {n : Nat} (p : Permutation) (hp : p∈permutations) (v w : Word n) :
    gramAt p v w = orient (flipA p) (wordSign v) * orient (flipB p) (wordSign w) *
      (if paired p then (if v=w then 4^n else 0) else 2^n * chi v w) := by
  induction v with
  | empty =>
    cases w; unfold gramAt
    cases h : paired p <;> cases ha : flipA p <;> cases hb : flipB p <;>
      simp [wordDouble,wordSign,chi,anti,phase,orient,fourIndices,qubitIndices,productIndices,sumOver] <;> rfl
  | cons a v ih =>
    cases w with | cons b w =>
      rw [gramAtCons,gramBit p hp,ih w]
      simp only [localGram,wordSign,orientMul,SymmetricDefect.chiCons]
      cases h : paired p <;> by_cases ab : a=b <;> by_cases vw : v=w <;>
        simp [ab,vw,Int.pow_succ] <;> grind only

private def oddCoefficient (p : Permutation) : Int :=
  alt p * orient (flipA p) (-1) * orient (flipB p) (-1)

private theorem signedPairCounts :
    sumOver permutations (fun p => if paired p then oddCoefficient p else 0) = 8 ∧
    sumOver permutations (fun p => if paired p then 0 else oddCoefficient p) = -16 := by decide

private theorem integerWordGram {n : Nat} (a b : Word n) (ha : oddWord a=true) (hb : oddWord b=true) :
    sumOver permutations (fun p => alt p * gramAt p a b) =
      8*(if a=b then 4^n else 0) - 16*((2:Int)^n * chi a b) := by
  let same : Int := if a=b then 4^n else 0
  let cross := (2:Int)^n * chi a b
  have sg (v : Word n) (hv : oddWord v=true) : (wordSign v : Int) = -1 := by
    rw [MixedDefect.oddWordTransposeSign,hv]; rfl
  have term (p) (hp : p∈permutations) : alt p * gramAt p a b =
      (if paired p then oddCoefficient p else 0)*same +
      (if paired p then 0 else oddCoefficient p)*cross := by
    rw [gramPermutation p hp,sg a ha,sg b hb]
    cases h : paired p <;> simp [oddCoefficient,same,cross] <;> grind only
  have sum := congrArg List.sum (List.map_congr_left (f:=fun p => alt p*gramAt p a b) term)
  change sumOver permutations _ = sumOver permutations _ at sum
  rw [sum,sumOverAdd,←sumOverMulRight,←sumOverMulRight,signedPairCounts.1,signedPairCounts.2]
  dsimp [same,cross]; grind only

private theorem castSum (xs : List α) (f : α → Int) :
    Int.cast (R:=C) (sumOver xs f) = sumOver xs (fun x => Int.cast (R:=C) (f x)) := by
  induction xs with
  | nil => exact Ring.intCast_zero
  | cons x xs ih =>
    change Int.cast (f x + sumOver xs f) = (Int.cast (f x) : C) + sumOver xs _
    rw [Ring.intCast_add,ih]

/-- Full ordered-coordinate Gram against one antisymmetrizer. The two
integer coefficients count the eight aligned and sixteen crossed pairings. -/
theorem pairedAlternationGram {n : Nat} (a b : Word n) (ha : oddWord a=true) (hb : oddWord b=true) :
    sumOver (fourIndices (qubitIndices n)) (fun x => star (doubledWord (R:=R) a x) * alternatingWord b x) =
      Int.cast (R:=ComplexScalar R) (8*(if a=b then (4:Int)^n else 0) - 16*((2:Int)^n * chi a b)) := by
  rw [←integerWordGram a b ha hb,castSum]
  simp only [alternatingWord,act,sumOverMulLeft]
  rw [sumOverSwap (fourIndices (qubitIndices n)) permutations]
  apply sumOverCongr; intro p
  rw [Ring.intCast_mul,gramAt,castSum,sumOverMulLeft]
  apply sumOverCongr; intro x
  rw [Ring.intCast_mul,wordDoubleEntry,wordDoubleEntry]
  have real : star (doubledWord (R:=R) a x) = doubledWord a x := by
    rw [←wordDoubleEntry]
    exact (scalarConjugation (R:=R)).fixesInteger _
  rw [real]; grind only

private theorem sumPerm {xs ys : List α} (h : xs.Perm ys) (f : α → C) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

private theorem sumPermConst (z : C) : sumOver permutations (fun _ => z) = 24*z := by
  have h : sumOver permutations (fun _ => (1:Int)) = 24 := by decide
  have c := congrArg (Int.cast (R:=C)) h
  rw [castSum] at c
  simp only [Ring.intCast_one,show Int.cast (R:=C) (24:Int) = (24:C) from Ring.intCast_ofNat 24] at c
  rw [←show sumOver permutations (fun _ => (1:C)) = 24 from c,sumOverMulRight]
  apply sumOverCongr; intro p; grind only

private theorem realInt (j : Int) : star (Int.cast (R:=ComplexScalar R) j) = Int.cast j :=
  (scalarConjugation (R:=R)).fixesInteger _

private theorem doubleAlternation (xs : List (Four α)) (hx : PermutedList xs)
    (f g : Four α → ComplexScalar R) :
    sumOver xs (fun x => star (act alt f x) * act alt g x) =
      24*sumOver xs (fun x => star (f x) * act alt g x) := by
  let z := fun x => star (f x) * act alt g x
  have atSite (x) : star (act alt f x) * act alt g x = sumOver permutations (fun p =>
      Int.cast (R:=ComplexScalar R) (alt p) * star (f (reorder x p)) * act alt g x) := by
    rw [←actStar,act,sumOverMulRight]
  rw [sumOverCongr _ atSite,sumOverSwap,←sumPermConst]
  apply congrArg List.sum; apply List.map_congr_left; intro p hp
  have changeVars : sumOver xs (fun x => z (reorder x p)) = sumOver xs z := by
    simpa only [sumOver,List.map_map,Function.comp_def] using sumPerm (hx p hp) z
  rw [←changeVars]
  apply sumOverCongr; intro x
  dsimp only [z]
  rw [AlternatingTrace.alternatingRow g p hp]
  grind only

private theorem collision {n : Nat} (x : Four (Basis n)) (h : ¬ExteriorIsometry.apart (PlaneOrientation.label n) x) :
    ∃ p∈permutations, oddPermutation p=true ∧ reorder x p = x := by
  rcases x with ⟨⟨a,b⟩,c,d⟩
  by_cases e : a=b
  · subst b; exact ⟨((1,0),(2,3)),by decide,by decide,rfl⟩
  by_cases e1 : a=c
  · subst c; exact ⟨((2,1),(0,3)),by decide,by decide,rfl⟩
  by_cases e2 : a=d
  · subst d; exact ⟨((3,1),(2,0)),by decide,by decide,rfl⟩
  by_cases e3 : b=c
  · subst c; exact ⟨((0,2),(1,3)),by decide,by decide,rfl⟩
  by_cases e4 : b=d
  · subst d; exact ⟨((0,3),(2,1)),by decide,by decide,rfl⟩
  by_cases e5 : c=d
  · subst d; exact ⟨((0,1),(3,2)),by decide,by decide,rfl⟩
  exact False.elim (h ⟨fun t => e (PlaneOrientation.labelInjective n _ _ t), fun t => e1 (PlaneOrientation.labelInjective n _ _ t),
    fun t => e2 (PlaneOrientation.labelInjective n _ _ t), fun t => e3 (PlaneOrientation.labelInjective n _ _ t),
    fun t => e4 (PlaneOrientation.labelInjective n _ _ t), fun t => e5 (PlaneOrientation.labelInjective n _ _ t)⟩)

private local instance {n : Nat} (r : Four (Basis n)) : Decidable (PlaneOrientation.Increasing r) := by
  unfold PlaneOrientation.Increasing
  infer_instance

private theorem sortedEnumeration (n : Nat) :
    (coords n).map Subtype.val = (fourIndices (qubitIndices n)).filter
      (ExteriorIsometry.increasing (PlaneOrientation.label n)) := by
  unfold coords
  rw [List.map_filterMap, ←List.filterMap_eq_filter]
  apply congrArg (fun f => (fourIndices (qubitIndices n)).filterMap f)
  funext r
  change Option.map Subtype.val (if h : PlaneOrientation.Increasing r then some ⟨r,h⟩ else none) =
    Option.guard (ExteriorIsometry.increasing (PlaneOrientation.label n)) r
  change _ = (if decide (PlaneOrientation.Increasing r) then some r else none)
  by_cases h : PlaneOrientation.Increasing r <;> simp [h]

private theorem dimThree (third : R) (unit : 3*third=1) : 3*ofReal third=(1:ComplexScalar R) := by
  change ofReal (3:R) * ofReal third = ofReal 1
  apply ComplexScalar.ext <;> simp <;> grind only

private theorem sortedAlternation {n : Nat} (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    (f g : Four (Basis n) → ComplexScalar R) :
    sumOver (coords n) (fun r => star (act alt f r.val) * act alt g r.val) =
      sumOver (fourIndices (qubitIndices n)) (fun x => star (f x) * act alt g x) := by
  letI : DecidableEq (Basis n) := HyperplaneInduction.cubeDecEq n
  let z := fun x => star (act alt f x)*act alt g x
  have symm (x) (p) (hp : p∈permutations) : z (reorder x p) = z x := by
    dsimp only [z]
    rw [AlternatingTrace.alternatingRow f p hp,AlternatingTrace.alternatingRow g p hp,star_mul,realInt]
    cases h : oddPermutation p <;> simp [coefficient,h] <;> grind only
  have deg (x) (hx : ¬ExteriorIsometry.apart (PlaneOrientation.label n) x) : z x = 0 := by
    obtain ⟨p,hp,odd,fixed⟩ := collision x hx
    have h := AlternatingTrace.alternatingRow g p hp x
    rw [fixed,show coefficient .antisymmetric p = -1 from by simp [coefficient,odd]] at h
    have two := halfComplex half h2
    dsimp only [z]
    have zero : act alt g x = 0 := by
      change act alt g x = Int.cast (R:=ComplexScalar R) (-1) * act alt g x at h
      rw [Ring.intCast_neg,Ring.intCast_one] at h
      have twice : 2 * act alt g x = 0 := by grind only
      calc
        _ = (2*ofReal half)*act alt g x := by rw [two,Semiring.one_mul]
        _ = ofReal half * (2*act alt g x) := by grind only
        _ = 0 := by rw [twice,Semiring.mul_zero]
    rw [zero,Semiring.mul_zero]
  have sorted := ExteriorIsometry.orderedToSorted (qubitIndices n) qubitIndicesComplete
    (HyperplaneIncidence.normalsNodup n) (PlaneOrientation.label n) z symm deg
  rw [←sortedEnumeration] at sorted
  have doubled := doubleAlternation (fourIndices (qubitIndices n))
    (fullPermuted _ (HyperplaneIncidence.normalsNodup n) qubitIndicesComplete) f g
  change sumOver _ z = _ at doubled
  rw [doubled] at sorted
  simp only [sumOver,List.map_map,Function.comp_def] at sorted
  let h := ofReal half
  let t := ofReal third
  have two : 2*h=1 := halfComplex half h2
  have three : 3*t=1 := dimThree third h3
  have unit : (h^3*t)*24=(1:ComplexScalar R) := by
    have e := congrArg (fun b : ComplexScalar R => b^3) two
    grind only
  have cancel (a b : ComplexScalar R) (e : 24*a=24*b) : a=b := by
    have m := congrArg (fun c => (h^3*t)*c) e
    simp only [←Semiring.mul_assoc,unit,Semiring.one_mul] at m
    exact m
  exact (cancel _ _ sorted).symm

/-- The Gram on physical increasing exterior coordinates, before the column normalization. -/
theorem increasingAlternationGram (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    {n : Nat} (a b : Word n) (ha : oddWord a=true) (hb : oddWord b=true) :
    sumOver (coords n) (fun r => star (alternatingWord (R:=R) a r.val) * alternatingWord b r.val) =
      Int.cast (R:=ComplexScalar R) (8*(if a=b then (4:Int)^n else 0)-16*((2:Int)^n*chi a b)) := by
  exact (sortedAlternation half third h2 h3 _ _).trans (pairedAlternationGram a b ha hb)

private theorem castDimension (n : Nat) :
    Int.cast (R:=C) ((2:Int)^n) = (2:C)^n ∧
    Int.cast (R:=C) ((4:Int)^n) = (2:C)^n*(2:C)^n := by
  induction n with
  | zero => simp only [Semiring.pow_zero,Ring.intCast_one,Semiring.one_mul]; trivial
  | succ n ih =>
    simp only [Semiring.pow_succ,Ring.intCast_mul,ih.1,ih.2,
      show Int.cast (R:=C) (2:Int) = (2:C) from Ring.intCast_ofNat 2,
      show Int.cast (R:=C) (4:Int) = (4:C) from Ring.intCast_ofNat 4]
    constructor <;> grind only

private theorem dimensionInverse (half : C) (h : 2*half=1) (n : Nat) :
    half^n*(2:C)^n=1 := by
  induction n with
  | zero => simp only [Semiring.pow_zero,Semiring.one_mul]
  | succ n ih => simp only [Semiring.pow_succ]; grind only

private theorem gramScalar {n : Nat} (a b : Word n) :
    Int.cast (R:=ComplexScalar R) (8*(if a=b then (4:Int)^n else 0)-16*((2:Int)^n*chi a b)) =
      8*(2:ComplexScalar R)^n * ((2:ComplexScalar R)^n * MixedDefect.idEntry a b-2*chi a b) := by
  have cg : Int.cast (R:=ComplexScalar R) (chi a b : Int) = chi a b := by
    cases h : anti a b <;> simp [chi,phase,h,Ring.intCast_neg,Ring.intCast_one]
  by_cases e : a=b <;>
    simp [e,MixedDefect.idEntry,Ring.intCast_sub,Ring.intCast_mul,castDimension,
      show Int.cast (R:=ComplexScalar R) (8:Int) = 8 from Ring.intCast_ofNat 8,
      show Int.cast (R:=ComplexScalar R) (16:Int) = 16 from Ring.intCast_ofNat 16] at cg ⊢ <;> grind only

/-- Explicit Seidel projector entry in character coordinates. -/
theorem physicalProjectionEntry (half third : R) (h2 : 2*half=1) {n : Nat} (a b : Word n) :
    MixedDefect.frameProjection ((2:R)^n) (half^n) third anti a b =
      ofReal third * (MixedDefect.idEntry a b - 2*(ofReal half)^n*chi a b) := by
  have self (v : Word n) : anti v v=false := by
    induction v with
    | empty => rfl
    | cons s w ih => cases s <;> simp [anti,axisAnti,ih w w]
  have embedding (z w : R) : ofReal (z*w) = ofReal z * ofReal w := by
    apply ComplexScalar.ext <;> simp <;> grind only
  have shift (z : R) : ofReal (z-2) = ofReal z - (2:ComplexScalar R) := by
    change ofReal (z-2) = ofReal z - ofReal (2:R)
    apply ComplexScalar.ext <;> simp <;> grind only
  have twoR : ofReal (2:R) = (2:ComplexScalar R) := rfl
  have dim := dimensionInverse (ofReal half) (halfComplex half h2) n
  unfold MixedDefect.frameProjection
  rw [embedding,shift,PhysicalPairedReduction.realEmbeddingPow,PhysicalPairedReduction.realEmbeddingPow,twoR]
  by_cases e : a=b
  · subst b; simp [MixedDefect.seidel,MixedDefect.idEntry,chi,phase,self] <;> grind only
  · cases bit : anti a b <;> simp [MixedDefect.seidel,MixedDefect.idEntry,MixedDefect.sign,e,chi,phase,bit] <;>
      apply ComplexScalar.ext <;> simp <;> grind only

/-- Both Gram matrices now use the same physically defined columns: on the
odd Pauli side the Gram is exactly three halves times the Seidel projector. -/
theorem oddWedgeSquareGram (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    {n : Nat} (a b : Word n) (ha : oddWord a=true) (hb : oddWord b=true) :
    2*sumOver (coords n) (fun r => star (wedgeSquareColumn half a r.val) * wedgeSquareColumn half b r.val) =
      3*MixedDefect.frameProjection ((2:R)^n) (half^n) third anti a b := by
  let h := ofReal half
  have scale (r : Coordinate n) : star (wedgeSquareColumn half a r.val) * wedgeSquareColumn half b r.val =
      h^(n+2)*h^(n+2) * (star (alternatingWord a r.val)*alternatingWord b r.val) := by
    unfold wedgeSquareColumn
    rw [star_mul,←PhysicalPairedReduction.realEmbeddingPow,star_ofReal,PhysicalPairedReduction.realEmbeddingPow]
    grind only
  rw [sumOverCongr _ scale,←sumOverMulLeft,increasingAlternationGram half third h2 h3 a b ha hb,gramScalar,
    physicalProjectionEntry half third h2,Semiring.pow_add]
  have unit := dimensionInverse h (halfComplex half h2) n
  have thirdUnit := dimThree third h3
  have two : 2*h=1 := halfComplex half h2
  have fourth := congrArg (fun z : ComplexScalar R => z^4) two
  change 2*(h^n*h^2*(h^n*h^2)*(8*(2:ComplexScalar R)^n*((2:ComplexScalar R)^n*MixedDefect.idEntry a b-2*chi a b))) =
    3*(ofReal third*(MixedDefect.idEntry a b-2*h^n*chi a b))
  grind only

/-- The original doubled word columns are orthogonal with squared norm d². -/
theorem doubledWordOrthogonal {n : Nat} (a b : Word n) :
    sumOver (fourIndices (qubitIndices n)) (fun x => star (doubledWord (R:=R) a x) * doubledWord b x) =
      (2:ComplexScalar R)^n*(2:ComplexScalar R)^n * MixedDefect.idEntry a b := by
  have table := gramPermutation ident (by decide) a b
  have p0 : paired ident=true := by decide
  have p1 : flipA ident=false := by decide
  have p2 : flipB ident=false := by decide
  simp only [p0,p1,p2,orient,ite_true,Bool.false_eq_true,ite_false,Int.one_mul] at table
  have result := congrArg (Int.cast (R:=ComplexScalar R)) table
  rw [gramAt,castSum] at result
  have term (x : Four (Basis n)) : Int.cast (R:=ComplexScalar R) (wordDouble a x * wordDouble b (reorder x ident)) =
      star (doubledWord a x)*doubledWord b x := by
    rw [Ring.intCast_mul,←wordDoubleEntry,realInt,←wordDoubleEntry]
    rfl
  rw [sumOverCongr _ term] at result
  rw [result]
  by_cases e : a=b <;> simp [e,MixedDefect.idEntry,castDimension] <;> grind only

/-- The ordered tensor pairing with one antisymmetrizer is 24 d² times
the physical Seidel projector entry. -/
theorem doubledWordProjection (half third : R) (h2 : 2*half=1) (h3 : 3*third=1)
    {n : Nat} (a b : Word n) (ha : oddWord a=true) (hb : oddWord b=true) :
    sumOver (fourIndices (qubitIndices n)) (fun x => star (doubledWord (R:=R) a x) * alternatingWord b x) =
      24*((2:ComplexScalar R)^n*(2:ComplexScalar R)^n) *
        MixedDefect.frameProjection ((2:R)^n) (half^n) third anti a b := by
  rw [pairedAlternationGram a b ha hb,gramScalar,physicalProjectionEntry half third h2]
  have dim := dimensionInverse (ofReal half) (halfComplex half h2) n
  have three := dimThree third h3
  grind only

end PauliGram

end RankSeven.WedgeSquareIntertwiner

#print axioms RankSeven.WedgeSquareIntertwiner.physicalWedgeSquareGram
#print axioms RankSeven.WedgeSquareIntertwiner.sourceWedgeSquarePhysicalEntries
#print axioms RankSeven.WedgeSquareIntertwiner.oddWedgeSquareGram
#print axioms RankSeven.WedgeSquareIntertwiner.doubledWordOrthogonal
#print axioms RankSeven.WedgeSquareIntertwiner.doubledWordProjection
