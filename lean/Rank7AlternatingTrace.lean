import Rank7FourCopySectors
import Rank7FrameExteriorSector

/-! Canonical increasing-source trace of the alternating replica block. -/
namespace RankSeven.AlternatingTrace
open Lean.Grind Pauli ExteriorPauliBase GenericExteriorKernel FourCopySectors

section Permutations
variable {C : Type} [CommRing C]
private theorem sumPerm {T : Type} {xs ys : List T} (h : xs.Perm ys) (f : T → C) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [sumOver,List.map_cons,List.sum_cons] at *; rw [ih]
  | swap => simp only [sumOver,List.map_cons,List.sum_cons]; grind
  | trans _ _ e₁ e₂ => exact e₁.trans e₂

private theorem compReorder {T : Type} (u : Four T) (p q : Perm) :
    reorder (reorder u p) q = reorder u (reorder p q) := by
  change ((position (reorder u p) _,position (reorder u p) _),
    (position (reorder u p) _,position (reorder u p) _)) = _
  simp only [GenericExteriorKernel.position_reorder]; rfl

set_option maxRecDepth 10000 in
private theorem translateTable : permutations.all (fun p =>
    decide ((permutations.map (reorder (inverse p))).Perm permutations) &&
    permutations.all (fun q => reorder p (reorder (inverse p) q) == q) &&
    decide ((permutations.map (conjugate p)).Perm permutations) &&
    decide (inverse p∈permutations) && decide (reorder p (inverse p) = ident) &&
    decide (reorder (inverse p) p = ident)) = true := by decide

private theorem translations (p : Perm) (hp : p∈permutations) :
    (permutations.map (reorder (inverse p))).Perm permutations ∧
    (∀ q∈permutations, reorder p (reorder (inverse p) q) = q) ∧
    (permutations.map (conjugate p)).Perm permutations ∧ inverse p∈permutations ∧
    reorder p (inverse p)=ident ∧ reorder (inverse p) p=ident := by
  have h := List.all_eq_true.mp translateTable p hp
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1,h.1.1.1.1.2,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩

end Permutations

section Alternating
open FrameExteriorSector (sourceTuple exteriorSector)
open ExteriorCuts (wedges Wedge7)
open PhysicalPairedReduction (fourWeights diagonal)
variable {C R α β : Type} [CommRing C] [CommRing R]
local instance : IntCast C := Ring.intCast

set_option maxRecDepth 10000 in
private theorem alternatingTable :
    (permutations.map inverse).Perm permutations ∧
    permutations.all (fun p => permutations.all (fun t =>
      coefficient .antisymmetric (reorder (inverse p) t) ==
        coefficient .antisymmetric p * coefficient .antisymmetric t)) = true := by decide

private theorem signSquare (p : Perm) : (Int.cast (R:=C) (coefficient .antisymmetric p))^2=1 := by
  unfold coefficient; cases oddPermutation p <;> simp <;> grind

theorem alternatingRow (f : Four α → C) (p : Perm) (hp : p∈permutations) (x : Four α) :
    act (coefficient .antisymmetric) f (reorder x p) =
      Int.cast (R:=C) (coefficient .antisymmetric p) * act (coefficient .antisymmetric) f x := by
  unfold act
  let g q := Int.cast (R:=C) (coefficient .antisymmetric q) * f (reorder (reorder x p) q)
  change sumOver permutations g = _
  rw [←sumPerm (translations p hp).1 g,sumOverMulLeft]
  simp only [sumOver,List.map_map,Function.comp_def]
  apply congrArg List.sum; apply List.map_congr_left; intro t ht
  have e := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp alternatingTable.2 p hp) t ht)
  simp only [g,compReorder, (translations p hp).2.1 t ht,e,Ring.intCast_mul]
  grind

theorem alternatingRight (K : Four α → Four β → C) (eqv : Equivariant K) (x : Four α) (y : Four β) :
    rawBlock .antisymmetric K x y = act (coefficient .antisymmetric) (K x) y := by
  let g p := Int.cast (R:=C) (coefficient .antisymmetric p) * K (reorder x p) y
  change sumOver permutations g = _
  rw [←sumPerm alternatingTable.1 g]
  unfold act
  simp only [sumOver,List.map_map,Function.comp_def]
  apply congrArg List.sum; apply List.map_congr_left; intro p hp
  dsimp only [g]
  rw [selfAdjointCoefficient _ p hp]
  have e := eqv p hp (reorder x (inverse p)) y
  rw [compReorder,(translations p hp).2.2.2.2.2] at e
  exact congrArg (fun z => Int.cast (R:=C) (coefficient .antisymmetric p)*z) e.symm

theorem alternatingColumn (K : Four α → Four β → C) (eqv : Equivariant K) (x : Four α) (y : Four β)
    (p : Perm) (hp : p∈permutations) :
    rawBlock .antisymmetric K x (reorder y p) = Int.cast (R:=C) (coefficient .antisymmetric p) *
      rawBlock .antisymmetric K x y := by
  rw [alternatingRight K eqv,alternatingRight K eqv,alternatingRow _ p hp]

theorem alternatingSortedEntry (K : Four (Fin 7) → Four (Fin 7) → C) (eqv : Equivariant K) (u v : Wedge7) :
    rawBlock .antisymmetric K (sourceTuple u) (sourceTuple v) = exteriorSector K u v := by
  rw [alternatingRight K eqv]
  unfold act exteriorSector
  apply sumOverCongr; intro p
  unfold coefficient signed; cases oddPermutation p <;> simp <;> grind

private def sites7 := List.finRange 7
private def tuples7 := fourIndices sites7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 700000 in
private theorem sortedSeven :
    (wedges.map sourceTuple).Perm (tuples7.filter (ExteriorIsometry.increasing Fin.val)) := by decide

private theorem orbitSum (f : Four (Fin 7) → C)
    (symm : ∀ x p, p∈permutations → f (reorder x p)=f x)
    (deg : ∀ x, ¬ExteriorIsometry.apart Fin.val x → f x=0) :
    sumOver tuples7 f = 24*sumOver wedges (fun w => f (sourceTuple w)) := by
  have h := ExteriorIsometry.orderedToSorted sites7 (fun x => List.mem_finRange x) (List.nodup_finRange 7)
    Fin.val f symm deg
  have e := sumPerm sortedSeven f
  simp only [sumOver,List.map_map,Function.comp_def] at e
  exact h.trans (congrArg (fun z => (24:C)*z) e.symm)

private theorem oddCollision (x : Four (Fin 7)) (h : ¬ExteriorIsometry.apart Fin.val x) :
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
  exact False.elim (h ⟨fun h => e (Fin.ext h),fun h => e1 (Fin.ext h),fun h => e2 (Fin.ext h),
    fun h => e3 (Fin.ext h),fun h => e4 (Fin.ext h),fun h => e5 (Fin.ext h)⟩)

private theorem alternatingRepeated (K : Four (Fin 7) → Four β → C) (x : Four (Fin 7)) (y : Four β)
    (h : ¬ExteriorIsometry.apart Fin.val x) (zeroOf : ∀ z : C, z= -z → z=0) :
    rawBlock .antisymmetric K x y = 0 := by
  obtain ⟨p,hp,odd,fixed⟩ := oddCollision x h
  have e := alternatingRow (fun r => K r y) p hp x
  rw [fixed] at e
  have c : coefficient .antisymmetric p = -1 := by simp [coefficient,odd]
  rw [c] at e
  apply zeroOf
  change act (coefficient .antisymmetric) (fun r => K r y) x = -act (coefficient .antisymmetric) (fun r => K r y) x
  exact e.trans (by grind only)

private theorem valueInvariant (h : Fin 7 → R) (x : Four (Fin 7)) (p : Perm) (hp : p∈permutations) :
    fourWeights h (reorder x p) = fourWeights h x := by
  exact tensorEquivariant (fun a (_ : Fin 7) => h a) p hp x x

variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
open ComplexScalar (ofReal)
private theorem noTwo (z : ComplexScalar R) (eq : z= -z) : z=0 := by
  have a := congrArg ComplexScalar.re eq; have b := congrArg ComplexScalar.im eq
  change z.re = -z.re at a; change z.im = -z.im at b
  apply ComplexScalar.ext
  · change z.re=0; grind
  · change z.im=0; grind

private theorem no24 {z w : ComplexScalar R} (eq : 24*z=24*w) : z=w := by
  have a := congrArg ComplexScalar.re eq; have b := congrArg ComplexScalar.im eq
  change (24:R)*z.re - 0*z.im = 24*w.re - 0*w.im at a
  change (24:R)*z.im + 0*z.re = 24*w.im + 0*w.re at b
  apply ComplexScalar.ext <;> grind

private def summand (h : Fin 7 → R) (A B : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (x y : Four (Fin 7)) :=
  ofReal (fourWeights h x) * rawBlock .antisymmetric A x y * ofReal (fourWeights h y) *
    rawBlock .antisymmetric B y x

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem summandRow (h : Fin 7 → R) (A B : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (b : Equivariant B) (x y : Four (Fin 7)) (p : Perm) (hp : p∈permutations) :
    summand h A B (reorder x p) y = summand h A B x y := by
  unfold summand
  rw [valueInvariant h x p hp,alternatingColumn B b y x p hp]
  have e := alternatingRow (fun r => A r y) p hp x
  change rawBlock .antisymmetric A (reorder x p) y =
    Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p) * rawBlock .antisymmetric A x y at e
  rw [e]
  have unit := signSquare (C:=ComplexScalar R) p
  grind only

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] in
private theorem summandCol (h : Fin 7 → R) (A B : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (a : Equivariant A) (x y : Four (Fin 7)) (p : Perm) (hp : p∈permutations) :
    summand h A B x (reorder y p) = summand h A B x y := by
  unfold summand
  rw [valueInvariant h y p hp,alternatingColumn A a x y p hp]
  have e := alternatingRow (fun r => B r x) p hp y
  change rawBlock .antisymmetric B (reorder y p) x =
    Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p) * rawBlock .antisymmetric B y x at e
  rw [e]
  have unit := signSquare (C:=ComplexScalar R) p
  grind only

private theorem sumZero {T : Type} (xs : List T) : sumOver xs (fun _ => (0:C))=0 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => change 0+sumOver _ _=0; rw [ih]; grind

private theorem sortedTrace (h : Fin 7 → R) (A B : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (a : Equivariant A) (b : Equivariant B) :
    sumOver tuples7 (fun x => sumOver tuples7 (fun y => summand h A B x y)) =
    24*(24*sumOver wedges (fun u => sumOver wedges (fun v => summand h A B (sourceTuple u) (sourceTuple v)))) := by
  have rows := orbitSum (fun x => sumOver tuples7 (fun y => summand h A B x y))
    (fun x p hp => sumOverCongr tuples7 (fun y => summandRow h A B b x y p hp))
    (fun x deg => (sumOverCongr tuples7 (g:=fun _ => 0) (fun y => by
      unfold summand; rw [alternatingRepeated A x y deg noTwo]; grind only)).trans (sumZero _))
  rw [rows]
  apply congrArg (fun z : ComplexScalar R => 24*z)
  rw [sumOverMulLeft]; apply sumOverCongr; intro u
  exact orbitSum (summand h A B (sourceTuple u))
    (fun y p hp => summandCol h A B a _ y p hp)
    (fun y deg => by unfold summand; rw [alternatingRepeated B y _ deg noTwo]; grind only)

/-- The single-side raw alternating trace has exactly 24 times the canonical
sorted 35-dimensional wedge trace, including both Schmidt weight factors. -/
theorem alternatingTraceToWedges (h : Fin 7 → R) (A B : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (a : Equivariant A) (b : Equivariant B) :
    pairedFrameTrace (fourIndices (List.finRange 7)) (tensorFour (diagonal h)) (rawBlock .antisymmetric A) B =
      24*pairedFrameTrace wedges (diagonal (fun w => fourWeights h (sourceTuple w))) (exteriorSector A) (exteriorSector B) := by
  have sitesNd := List.nodup_finRange 7
  have pairNd := HyperplaneInduction.pairsNodup sites7 sites7 sitesNd sitesNd
  have nd : tuples7.Nodup := HyperplaneInduction.pairsNodup _ _ pairNd pairNd
  have full (x : Four (Fin 7)) : x∈tuples7 :=
    HyperplaneInduction.pairMember (HyperplaneInduction.pairMember (List.mem_finRange _) (List.mem_finRange _))
      (HyperplaneInduction.pairMember (List.mem_finRange _) (List.mem_finRange _))
  have both := pairedBlockOrthogonality tuples7 (fullPermuted sites7 sitesNd (fun x => List.mem_finRange x))
    .antisymmetric .antisymmetric (tensorFour (diagonal h)) A B (tensorEquivariant _) a
  simp only [ite_true] at both
  apply no24
  change 24 * pairedFrameTrace tuples7 (tensorFour (diagonal h)) (rawBlock .antisymmetric A) B = _
  rw [← both,PhysicalPairedReduction.tensorDiagonal]
  rw [PhysicalPairedReduction.pairedTraceDiagonal tuples7 nd full,PhysicalPairedReduction.pairedTraceDiagonal wedges
    ExteriorCuts.wedgesNodup ExteriorCuts.memWedges]
  change sumOver tuples7 (fun x => sumOver tuples7 (fun y => summand h A B x y)) = _
  rw [sortedTrace h A B a b]
  simp only [summand,alternatingSortedEntry A a,alternatingSortedEntry B b]
end Alternating

section Spectral
open ExteriorCuts (Wedge7 wedges amplitude)
open PhysicalPairedReduction (diagonal fourWeights)
open FrameExteriorSector (sourceTuple)
variable {R : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]

/-- In the physical self-pair the alternating raw trace is 24 times the
sorted wedge trace; the normalized Pauli frame contributes another 4². -/
theorem physicalAlternatingTrace (half : R) (halfUnit : 2*half=1) (k : Nat)
    (U : Basis (k+3) → Fin 7 → ComplexScalar R) (h : Fin 7 → R) :
    let F := RectangularPairedReduction.normalizedFrame half U
    (pairedFrameTrace (fourIndices (List.finRange 7)) (tensorFour (diagonal h)) (rawBlock .antisymmetric F) F).re =
      384 * (PhysicalCompressionEffect.physicalEntries half halfUnit k U).realQuadraticTrace wedges (amplitude h) := by
  dsimp only
  let F := RectangularPairedReduction.normalizedFrame half U
  have eqv := (normalizedFrameStructure half U).1
  rw [alternatingTraceToWedges h F F eqv eqv]
  have weights : (fun w => fourWeights h (sourceTuple w))=amplitude h := by
    funext w
    unfold fourWeights sourceTuple amplitude ExteriorCuts.product4
    grind only
  rw [weights]
  have res := FrameExteriorSector.physicalWedgeTrace_eq_spectral half halfUnit k U (amplitude h)
  change 24 * (pairedFrameTrace wedges (diagonal (amplitude h)) (FrameExteriorSector.exteriorSector F)
    (FrameExteriorSector.exteriorSector F)).re - 0 * _ = _
  unfold F
  rw [res]
  grind only

/-- Linear overlap in the alternating sector. Repeated tuples cancel, and
each increasing wedge has exactly twenty-four surviving orderings. -/
theorem alternatingOverlapToWedges (h : Fin 7 → R) (A : Four (Fin 7) → Four (Fin 7) → ComplexScalar R)
    (eqv : Equivariant A) :
    trace tuples7 (matMul tuples7 (rawBlock .antisymmetric A) (tensorFour (diagonal h))) =
      24 * sumOver wedges (fun w => ComplexScalar.ofReal (fourWeights h (sourceTuple w)) *
        FrameExteriorSector.exteriorSector A w w) := by
  letI : IntCast (ComplexScalar R) := Ring.intCast
  let f (x : Four (Fin 7)) := ComplexScalar.ofReal (fourWeights h x) * rawBlock .antisymmetric A x x
  have pairNd := HyperplaneInduction.pairsNodup sites7 sites7 (List.nodup_finRange 7) (List.nodup_finRange 7)
  have nd : tuples7.Nodup := HyperplaneInduction.pairsNodup _ _ pairNd pairNd
  have full (x : Four (Fin 7)) : x ∈ tuples7 :=
    HyperplaneInduction.pairMember (HyperplaneInduction.pairMember (List.mem_finRange _) (List.mem_finRange _))
      (HyperplaneInduction.pairMember (List.mem_finRange _) (List.mem_finRange _))
  have symm (x : Four (Fin 7)) (p : Perm) (hp : p ∈ permutations) : f (reorder x p) = f x := by
    unfold f
    rw [valueInvariant h x p hp, alternatingColumn A eqv _ x p hp]
    change ComplexScalar.ofReal (fourWeights h x) * (Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p) *
      act (coefficient .antisymmetric) (fun y => A y x) (reorder x p)) = _
    rw [alternatingRow _ p hp]
    let c := Int.cast (R:=ComplexScalar R) (coefficient .antisymmetric p)
    have sign : c*c=1 := by
      simpa only [Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul] using signSquare (C:=ComplexScalar R) p
    change ComplexScalar.ofReal (fourWeights h x) * (c*(c*rawBlock .antisymmetric A x x)) =
      ComplexScalar.ofReal (fourWeights h x) * rawBlock .antisymmetric A x x
    rw [←Semiring.mul_assoc c c _,sign,Semiring.one_mul]
  have deg (x : Four (Fin 7)) (hx : ¬ExteriorIsometry.apart Fin.val x) : f x=0 := by
    unfold f
    rw [alternatingRepeated A x x hx noTwo, Semiring.mul_zero]
  rw [traceMatMulSwap tuples7 tuples7,PhysicalPairedReduction.tensorDiagonal]
  have traceEq : trace tuples7 (matMul tuples7 (diagonal (fourWeights h)) (rawBlock .antisymmetric A)) =
      sumOver tuples7 f := by
    unfold trace
    apply sumOverCongr
    intro x
    exact PhysicalPairedReduction.diagonalAction _ nd _ _ x x (full x)
  rw [traceEq,orbitSum f symm deg]
  congr 1
  apply sumOverCongr
  intro w
  unfold f
  rw [alternatingSortedEntry A eqv]

end Spectral

end RankSeven.AlternatingTrace
