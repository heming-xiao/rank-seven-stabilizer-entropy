import Rank7MissingHole
import Rank7ComplexScalar
import Rank7AnticommutingDefect
import Rank7PlaneProjector

namespace RankSeven.OddSkewContraction

open Lean.Grind Pauli ComplexScalar
open AnticommutingDefect (sumCongrMem)
attribute [local instance] Semiring.natCast

variable {R α : Type} [CommRing R] [LE R] [LT R] [Std.IsLinearOrder R]
  [Std.LawfulOrderLT R] [OrderedRing R] [DecidableEq α]

def image (xs : List α) (A : α → α → ComplexScalar R) (v : α → ComplexScalar R) (i : α) :=
  sumOver xs (fun j => A i j*v j)

/-- Skew Gaussian elimination removes two pivots at a time. Keeping the pivot
factor in the reduced matrix avoids division, including at singular pivots. -/
theorem oddKernel (xs : List α) (nodup : xs.Nodup) (odd : xs.length % 2 = 1)
    (A : α → α → ComplexScalar R) (skew : ∀ i j, A i j = -A j i) :
    ∃ v, (∃ i ∈ xs, v i≠0) ∧ ∀ i ∈ xs, image xs A v i=0 := by
  suffices strong : ∀ n, ∀ xs : List α, xs.length=n → xs.Nodup → xs.length%2=1 →
      ∀ A : α → α → ComplexScalar R, (∀ i j, A i j = -A j i) →
      ∃ v, (∃ i ∈ xs, v i≠0) ∧ ∀ i ∈ xs, image xs A v i=0 by
    exact strong xs.length xs rfl nodup odd A skew
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs length nodup odd A skew
    have diagonal (i : α) : A i i=0 := by
      have anti := skew i i
      have re := congrArg ComplexScalar.re anti
      have im := congrArg ComplexScalar.im anti
      apply ComplexScalar.ext <;> simp only [re_neg,im_neg,re_zero,im_zero] at * <;> grind only
    by_cases pivot : ∃ p∈xs, ∃ q∈xs, A p q≠0
    · obtain ⟨p,pIn,q,qIn,nonzero⟩ := pivot
      have pq : p≠q := fun h => nonzero (h ▸ diagonal p)
      let first := deleteColumn xs p
      let ys := deleteColumn first q
      have qInFirst : q ∈ first := deleteColumn_mem.mpr ⟨qIn,pq.symm⟩
      have firstND : first.Nodup := nodup.filter _
      have size₁ := (columnSplit xs p (fun _ => (0:ComplexScalar R)) nodup pIn).1
      have size₂ := (columnSplit first q (fun _ => (0:ComplexScalar R)) firstND qInFirst).1
      change first.length+1=xs.length at size₁
      change ys.length+1=first.length at size₂
      have shorter : ys.length<n := by omega
      have odd' : ys.length%2=1 := by omega
      have splitSum (f : α → ComplexScalar R) : sumOver xs f = f p+f q+sumOver ys f := by
        rw [(columnSplit xs p f nodup pIn).2,(columnSplit first q f firstND qInFirst).2]
        grind only
      let s := A p q
      let B (i j : α) := s*A i j + A i p*A q j - A i q*A p j
      have skewB (i j : α) : B i j=-B j i := by
        unfold B
        have a := skew i j
        have b := skew i p
        have c := skew j p
        have d := skew i q
        have e := skew j q
        grind only
      obtain ⟨w,⟨r,hr,hw⟩,zero⟩ := ih ys.length shorter ys rfl (firstND.filter _) odd' B skewB
      let u := image ys A w p
      let v := image ys A w q
      let z (i : α) := if i=p then v else if i=q then -u else s*w i
      have members (j : α) (h : j∈ys) : j∈xs ∧ j≠p ∧ j≠q := by
        have e := deleteColumn_mem.mp h
        have f := deleteColumn_mem.mp e.1
        exact ⟨f.1,f.2,e.2⟩
      have scaleRow (i : α) : sumOver ys (fun j => A i j*z j)=s*image ys A w i := by
        unfold image
        rw [sumOverMulLeft]
        apply sumCongrMem
        intro j hj
        have facts := members j hj
        simp only [z,ite_eq_right facts.2.1,ite_eq_right facts.2.2]
        grind only
      have atP : z p=v := by simp [z]
      have atQ : z q=-u := by simp [z,pq.symm]
      have nz : z r≠0 := by
        have facts := members r hr
        simpa only [z,ite_eq_right facts.2.1,ite_eq_right facts.2.2] using
          ComplexScalar.mul_ne_zero s (w r) nonzero hw
      refine ⟨z,⟨r,(members r hr).1,nz⟩,?_⟩
      intro i hi
      unfold image
      rw [splitSum,atP,atQ,scaleRow]
      by_cases ip : i=p
      · subst i
        rw [diagonal]
        change (0:ComplexScalar R)*v+s*(-u)+s*u=0
        grind only
      by_cases iq : i=q
      · subst i
        rw [diagonal,skew q p]
        change (-s)*v+0*(-u)+s*v=0
        grind only
      have iIn : i∈ys := deleteColumn_mem.mpr ⟨deleteColumn_mem.mpr ⟨hi,ip⟩,iq⟩
      have row := zero i iIn
      have expands : image ys B w i = s*image ys A w i+A i p*v-A i q*u := by
        dsimp only [image,u,v]
        rw [sumOverMulLeft,sumOverMulLeft,sumOverMulLeft,←sumOverAdd,←Compression.sumOverSub]
        apply sumOverCongr
        intro j
        unfold B
        grind only
      rw [expands] at row
      grind only
    · cases xs with
      | nil => simp at odd
      | cons first tail =>
        have one : (1:ComplexScalar R)≠0 := by
          intro e
          have eq := congrArg ComplexScalar.re e
          simp only [re_one,re_zero] at eq
          have lt : (0:R)<1 := OrderedRing.zero_lt_one
          grind only
        refine ⟨fun _ => 1,⟨first,List.mem_cons_self,one⟩,?_⟩
        intro i hi
        unfold image
        have allZero (ls : List α) (inXs : ∀ j∈ls, j∈first::tail) :
            sumOver ls (fun j => A i j*1)=0 := by
          induction ls with
          | nil => rfl
          | cons j js ih =>
            have e : A i j=0 := by
              by_cases bad : A i j=0
              · exact bad
              · exact False.elim (pivot ⟨i,hi,j,inXs j List.mem_cons_self,bad⟩)
            change A i j*1+sumOver js _=0
            rw [e,ih (fun a ha => inXs a (List.mem_cons_of_mem j ha))]
            grind only
        exact allZero (first::tail) (fun _ h => h)

omit [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R] [DecidableEq α] in
private theorem sumConstant (xs : List α) (a : R) :
    sumOver xs (fun _ => a) = (Nat.cast xs.length : R)*a := by
  induction xs with
  | nil => simp [sumOver,Semiring.natCast_zero] <;> grind only
  | cons i xs ih =>
    change a+sumOver xs (fun _ => a)=(Nat.cast (xs.length+1):R)*a
    rw [ih,Semiring.natCast_succ]
    grind only

omit [DecidableEq α] in
private theorem sumLe (xs : List α) {f g : α → R} (pointwise : ∀ i ∈ xs, f i≤g i) :
    sumOver xs f≤sumOver xs g := by
  have nonnegative := Compression.sumOverNonnegative xs (fun i => g i-f i) (fun i hi => by
    have step := pointwise i hi
    grind only)
  rw [Compression.sumOverSub] at nonnegative
  grind only

/-- A contraction that kills a nonzero vector loses at least one unit of
squared Frobenius norm. Test it on the standard basis projected, without
division, to the orthogonal complement of that vector. -/
theorem massLeLengthSubOneOfKernel (xs : List α) (nd : xs.Nodup)
    (A : α → α → ComplexScalar R)
    (contract : ∀ v, sumOver xs (fun i => normSq (image xs A v i))≤sumOver xs (fun i => normSq (v i)))
    (v : α → ComplexScalar R) (nonzero : ∃ i∈xs, v i≠0) (kernel : ∀ i∈xs, image xs A v i=0) :
    sumOver xs (fun i => sumOver xs (fun j => normSq (A i j))) ≤ (Nat.cast xs.length : R)-1 := by
  let N := sumOver xs (fun j => normSq (v j))
  obtain ⟨r,hr,vr⟩ := nonzero
  have positive : 0<N := by
    unfold N
    rw [(columnSplit xs r _ nd hr).2]
    have rest := Compression.sumOverNonnegative (deleteColumn xs r) (fun i => normSq (v i))
      (fun i _ => normSq_nonnegative (v i))
    have atR := normSq_positive (v r) vr
    grind only
  let projected (i j : α) := (if i=j then ofReal N else 0)-star (v i)*v j
  have projectedImage (i : α) (hi : i∈xs) (a : α) (ha : a∈xs) :
      image xs A (projected i) a=ofReal N*A a i := by
    unfold image
    have eq (j : α) : A a j*projected i j =
        (if i=j then ofReal N*A a j else 0)-star (v i)*(A a j*v j) := by
      unfold projected
      split <;> grind only
    rw [sumOverCongr xs eq,Compression.sumOverSub,←sumOverMulLeft,
      ExteriorPauliBase.sumOnIndex xs i (fun j => ofReal N*A a j) nd hi]
    change _ - star (v i)*image xs A v a=_
    rw [kernel a ha]
    grind only
  have projectedNorm (i : α) (hi : i∈xs) :
      sumOver xs (fun j => normSq (projected i j))=N^2-N*normSq (v i) := by
    have eq (j : α) : normSq (projected i j) =
        (if i=j then N^2-2*N*normSq (v i) else 0)+normSq (v i)*normSq (v j) := by
      unfold projected
      by_cases equal : i=j
      · subst j
        simp only [ite_true,star_mul_self,normSq,re_sub,im_sub,re_ofReal,im_ofReal]
        grind only
      · simp only [ite_eq_right equal]
        have neg : normSq ((0 : ComplexScalar R)-star (v i)*v j)=normSq (star (v i)*v j) := by
          simp only [normSq,re_sub,im_sub,re_zero,im_zero]
          grind only
        rw [neg,normSq_mul,normSq_star]
        grind only
    rw [sumOverCongr xs eq,sumOverAdd,←sumOverMulLeft,
      ExteriorPauliBase.sumOnIndex xs i (fun _ => N^2-2*N*normSq (v i)) nd hi]
    change N^2-2*N*normSq (v i)+normSq (v i)*N=_
    grind only
  have each (i : α) (hi : i∈xs) :
      N^2 * sumOver xs (fun a => normSq (A a i)) ≤ N^2-N*normSq (v i) := by
    have h := contract (projected i)
    rw [projectedNorm i hi] at h
    rw [sumCongrMem xs _ (fun a => normSq (ofReal N*A a i)) (fun a ha => by
      rw [projectedImage i hi a ha])] at h
    simp only [normSq_mul,normSq_ofReal,←sumOverMulLeft] at h
    exact h
  have added := sumLe xs each
  rw [←sumOverMulLeft,Compression.sumOverSub,sumConstant,←sumOverMulLeft] at added
  change N^2*sumOver xs (fun i => sumOver xs (fun a => normSq (A a i))) ≤
    (Nat.cast xs.length:R)*N^2-N*N at added
  rw [sumOverSwap] at added
  by_cases bound : sumOver xs (fun i => sumOver xs (fun j => normSq (A i j))) ≤
      (Nat.cast xs.length:R)-1
  · exact bound
  · have above : (Nat.cast xs.length:R)-1 <
        sumOver xs (fun i => sumOver xs (fun j => normSq (A i j))) := by grind only
    have squarePositive : 0<N^2 := by
      have := OrderedRing.mul_pos positive positive
      grind only
    have contradiction := OrderedRing.mul_lt_mul_of_pos_left above squarePositive
    grind only

theorem massLeLengthSubOne (xs : List α) (nd : xs.Nodup) (odd : xs.length%2=1)
    (A : α → α → ComplexScalar R) (skew : ∀ i j, A i j = -A j i)
    (contraction : ∀ v, sumOver xs (fun i => normSq (image xs A v i))≤sumOver xs (fun i => normSq (v i))) :
    sumOver xs (fun i => sumOver xs (fun j => normSq (A i j))) ≤ (Nat.cast xs.length : R)-1 := by
  obtain ⟨v, hv, kills⟩ := oddKernel xs nd odd A skew
  exact massLeLengthSubOneOfKernel xs nd A contraction v hv kills

end RankSeven.OddSkewContraction

#print axioms RankSeven.OddSkewContraction.oddKernel
#print axioms RankSeven.OddSkewContraction.massLeLengthSubOne
