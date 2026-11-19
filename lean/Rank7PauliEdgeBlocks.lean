import Rank7MixedDefect
import Rank7AnticommutingDefect

namespace RankSeven.PauliEdgeBlocks

open Lean.Grind Pauli
open SymmetricDefect (anti axisAnti chi phase unitWord)

def axisBits : Axis → Bool × Bool
  | .identity => (false,false)
  | .x => (true,false)
  | .y => (true,true)
  | .z => (false,true)

def fromBits : Bool × Bool → Axis
  | (false,false) => .identity
  | (true,false) => .x
  | (true,true) => .y
  | (false,true) => .z

def axisAdd (a b : Axis) : Axis :=
  fromBits ((axisBits a).1 ^^ (axisBits b).1,(axisBits a).2 ^^ (axisBits b).2)

def wordAdd : {n : Nat} → Word n → Word n → Word n
  | _, .empty, .empty => .empty
  | _, .cons a as, .cons b bs => .cons (axisAdd a b) (wordAdd as bs)

theorem wordAddZero {n : Nat} (a : Word n) : wordAdd a (unitWord n) = a := by
  induction a with
  | empty => rfl
  | cons a as ih =>
    change Word.cons (axisAdd a .identity) (wordAdd as (unitWord _)) = Word.cons a as
    rw [ih]
    cases a <;> rfl

theorem wordAddSelf {n : Nat} (a : Word n) : wordAdd a a = unitWord n := by
  induction a with
  | empty => rfl
  | cons a as ih =>
    change Word.cons (axisAdd a a) (wordAdd as as) = Word.cons .identity (unitWord _)
    rw [ih]
    cases a <;> rfl

theorem wordAddComm {n : Nat} (a b : Word n) : wordAdd a b = wordAdd b a := by
  induction a with
  | empty => cases b; rfl
  | cons a as ih =>
    cases b with
    | cons b bs =>
      change Word.cons (axisAdd a b) (wordAdd as bs) = Word.cons (axisAdd b a) (wordAdd bs as)
      rw [ih]
      cases a <;> cases b <;> rfl

theorem wordAddAssoc {n : Nat} (a b c : Word n) :
    wordAdd (wordAdd a b) c = wordAdd a (wordAdd b c) := by
  induction a with
  | empty => cases b; cases c; rfl
  | cons a as ih =>
    cases b with
    | cons b bs =>
      cases c with
      | cons c cs =>
        change Word.cons (axisAdd (axisAdd a b) c) (wordAdd (wordAdd as bs) cs) =
          Word.cons (axisAdd a (axisAdd b c)) (wordAdd as (wordAdd bs cs))
        rw [ih]
        cases a <;> cases b <;> cases c <;> rfl

theorem wordAddCancel {n : Nat} (a b : Word n) : wordAdd (wordAdd a b) b = a := by
  rw [wordAddAssoc, wordAddSelf, wordAddZero]

theorem wordAddEqZero {n : Nat} (a b : Word n) : wordAdd a b = unitWord n ↔ a=b := by
  constructor
  · intro h
    have cancel := wordAddCancel a b
    rw [h, wordAddComm, wordAddZero] at cancel
    exact cancel.symm
  · intro h
    subst b
    exact wordAddSelf a

theorem antiSelf {n : Nat} (a : Word n) : anti a a=false := by
  induction a with
  | empty => rfl
  | cons a as ih =>
    change (axisAnti a a ^^ anti as as) = false
    rw [ih]
    cases a <;> rfl

theorem antiZero {n : Nat} (a : Word n) : anti a (unitWord n)=false := by
  induction a with
  | empty => rfl
  | cons a as ih =>
    change (axisAnti a .identity ^^ anti as (unitWord _)) = false
    rw [ih]
    cases a <;> rfl

theorem antiSymm {n : Nat} (a b : Word n) : anti a b=anti b a := by
  induction a with
  | empty => cases b; rfl
  | cons a as ih =>
    cases b with
    | cons b bs =>
      change (axisAnti a b ^^ anti as bs) = (axisAnti b a ^^ anti bs as)
      rw [ih]
      cases a <;> cases b <;> rfl

theorem antiAddLeft {n : Nat} (a b c : Word n) :
    anti (wordAdd a b) c = (anti a c ^^ anti b c) := by
  induction a with
  | empty => cases b; cases c; rfl
  | cons a as ih =>
    cases b with
    | cons b bs =>
      cases c with
      | cons c cs =>
        change (axisAnti (axisAdd a b) c ^^ anti (wordAdd as bs) cs) =
          ((axisAnti a c ^^ anti as cs) ^^ (axisAnti b c ^^ anti bs cs))
        rw [ih]
        have head : axisAnti (axisAdd a b) c = (axisAnti a c ^^ axisAnti b c) := by
          cases a <;> cases b <;> cases c <;> rfl
        rw [head]
        cases axisAnti a c <;> cases axisAnti b c <;>
          cases anti as cs <;> cases anti bs cs <;> rfl

theorem antiAddRight {n : Nat} (a b c : Word n) :
    anti a (wordAdd b c) = (anti a b ^^ anti a c) := by
  rw [antiSymm a (wordAdd b c), antiAddLeft, antiSymm b a, antiSymm c a]

theorem companionExists {n : Nat} (s : Word n) (nonzero : s ≠ unitWord n) :
    ∃ r, anti s r=true := by
  induction s with
  | empty => exact False.elim (nonzero rfl)
  | cons a as ih =>
    cases a with
    | identity =>
      have tailNonzero : as ≠ unitWord _ := by
        intro eq
        apply nonzero
        exact congrArg (Word.cons .identity) eq
      obtain ⟨b,hb⟩ := ih tailNonzero
      refine ⟨.cons .identity b, ?_⟩
      change (false ^^ anti as b)=true
      simp [hb]
    | x =>
      refine ⟨.cons .z (unitWord _), ?_⟩
      change (true ^^ anti as (unitWord _))=true
      simp [antiZero]
    | y =>
      refine ⟨.cons .x (unitWord _), ?_⟩
      change (true ^^ anti as (unitWord _))=true
      simp [antiZero]
    | z =>
      refine ⟨.cons .x (unitWord _), ?_⟩
      change (true ^^ anti as (unitWord _))=true
      simp [antiZero]

def perpendicular {n : Nat} (s r u : Word n) : Bool := !anti u s && !anti u r

def perpendicularWords {n : Nat} (s r : Word n) : List (Word n) :=
  (words n).filter (perpendicular s r)

theorem perpendicularIff {n : Nat} (s r u : Word n) :
    perpendicular s r u = true ↔ anti u s=false ∧ anti u r=false := by
  unfold perpendicular
  cases anti u s <;> cases anti u r <;> decide

theorem perpendicularAdd {n : Nat} (s r u v : Word n)
    (pu : perpendicular s r u=true) (pv : perpendicular s r v=true) :
    perpendicular s r (wordAdd u v)=true := by
  obtain ⟨us,ur⟩ := (perpendicularIff s r u).mp pu
  obtain ⟨vs,vr⟩ := (perpendicularIff s r v).mp pv
  apply (perpendicularIff s r _).mpr
  rw [antiAddLeft, antiAddLeft, us, ur, vs, vr]
  decide

/-- Each unordered anticommuting edge in the direction s has a unique
endpoint orthogonal to the selected companion r. -/
theorem edgeEndpoint {n : Nat} (s r a : Word n) (sr : anti s r=true) :
    (anti a r=false ∧ anti (wordAdd a s) r=true) ∨
      (anti a r=true ∧ anti (wordAdd a s) r=false) := by
  rw [antiAddLeft, sr]
  cases anti a r <;> decide

theorem edgeRepresentative {n : Nat} (s r u : Word n) (sr : anti s r=true)
    (hu : perpendicular s r u=true) :
    anti (wordAdd r u) s=true ∧ anti (wordAdd r u) r=false := by
  obtain ⟨us,ur⟩ := (perpendicularIff s r u).mp hu
  rw [antiAddLeft, antiAddLeft, antiSymm r s, sr, antiSelf, us, ur]
  decide

theorem edgeCoordinate {n : Nat} (s r a : Word n) (sr : anti s r=true)
    (onEdge : anti a s=true) (chosen : anti a r=false) :
    perpendicular s r (wordAdd a r)=true ∧ wordAdd r (wordAdd a r)=a := by
  constructor
  · apply (perpendicularIff s r _).mpr
    rw [antiAddLeft, antiAddLeft, antiSymm r s, sr, antiSelf, onEdge, chosen]
    decide
  · rw [←wordAddAssoc, wordAddComm r a, wordAddCancel]

theorem representativesPairing {n : Nat} (s r u v : Word n)
    (hu : perpendicular s r u=true) (hv : perpendicular s r v=true) :
    anti (wordAdd r u) (wordAdd r v) = anti u v := by
  have ur := ((perpendicularIff s r u).mp hu).2
  have vr := ((perpendicularIff s r v).mp hv).2
  rw [antiAddLeft, antiAddRight, antiAddRight, antiSelf, antiSymm r v, ur, vr]
  cases anti u v <;> rfl

section Character

variable {R : Type} [CommRing R]
noncomputable local instance {n : Nat} : DecidableEq (Word n) := Classical.typeDecidableEq _
open AnticommutingDefect (kernelImage kernelImageNorm kernelDefectSquare sumCongrMem)

theorem characterAddRight {n : Nat} (a b c : Word n) :
    chi a (wordAdd b c) = (chi a b : R) * chi a c := by
  unfold chi
  rw [antiAddRight]
  cases anti a b <;> cases anti a c <;> simp [phase] <;> grind

private theorem characterSum {n : Nat} (w : Word n) :
    sumOver (words n) (fun x => (chi x w : R)) =
      if w=unitWord n then (4:R)^n else 0 := by
  classical
  have h := SymmetricDefect.characterOrthogonality (C:=R) w (unitWord n)
  have term (x : Word n) : (chi x w : R) * chi x (unitWord n) = chi x w := by
    unfold chi
    rw [antiZero]
    change _ * 1 = _
    exact Semiring.mul_one _
  rw [sumOverCongr _ term] at h
  exact h

private theorem filteredSum {α : Type} (xs : List α) (keep : α → Bool) (f : α → R) :
    sumOver (xs.filter keep) f = sumOver xs (fun x => if keep x then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    cases h : keep x <;> simp [h, sumOver] at ih ⊢ <;> grind

private theorem shiftedNonzero {n : Nat} (s r w : Word n) (sr : anti s r=true)
    (hw : perpendicular s r w=true) :
    wordAdd w s ≠ unitWord n ∧ wordAdd w r ≠ unitWord n ∧
      wordAdd (wordAdd w s) r ≠ unitWord n := by
  obtain ⟨ws,wr⟩ := (perpendicularIff s r w).mp hw
  have rs := (antiSymm r s).trans sr
  refine ⟨?_,?_,?_⟩
  · intro e
    have h := congrArg (fun x => anti x r) e
    rw [antiAddLeft, wr, sr, antiSymm (unitWord n) r, antiZero] at h
    contradiction
  · intro e
    have h := congrArg (fun x => anti x s) e
    rw [antiAddLeft, ws, rs, antiSymm (unitWord n) s, antiZero] at h
    contradiction
  · intro e
    have h := congrArg (fun x => anti x s) e
    rw [antiAddLeft, antiAddLeft, ws, antiSelf, rs, antiSymm (unitWord n) s, antiZero] at h
    contradiction

/-- Orthogonality on the actual complement of two anticommuting Pauli
words. The factor four comes from filtering two independent character bits. -/
theorem perpendicularCharacterSum {n : Nat} (s r w : Word n) (sr : anti s r=true)
    (hw : perpendicular s r w=true) :
    4 * sumOver (perpendicularWords s r) (fun u => (chi u w : R)) =
      if w=unitWord n then (4:R)^n else 0 := by
  classical
  obtain ⟨ws,wr,wsr⟩ := shiftedNonzero s r w sr hw
  unfold perpendicularWords
  rw [filteredSum, sumOverMulLeft]
  have term (x : Word n) :
      4 * (if perpendicular s r x then (chi x w : R) else 0) =
        chi x w + chi x (wordAdd w s) + chi x (wordAdd w r) + chi x (wordAdd (wordAdd w s) r) := by
    simp only [characterAddRight]
    unfold perpendicular
    have a := show (chi x s : R) = phase (anti x s) from rfl
    have b := show (chi x r : R) = phase (anti x r) from rfl
    rw [a,b]
    cases anti x s <;> cases anti x r <;> simp [phase] <;> grind
  rw [sumOverCongr _ term, sumOverAdd, sumOverAdd, sumOverAdd,
    characterSum, characterSum, characterSum, characterSum]
  simp [ws,wr,wsr]
  grind

theorem perpendicularCharacterKernel {n : Nat} (s r u v : Word n) (sr : anti s r=true)
    (hu : perpendicular s r u=true) (hv : perpendicular s r v=true) :
    4 * sumOver (perpendicularWords s r) (fun x => (chi u x : R) * chi x v) =
      if u=v then (4:R)^n else 0 := by
  classical
  have h := perpendicularCharacterSum (R:=R) s r (wordAdd u v) sr (perpendicularAdd s r u v hu hv)
  simp only [wordAddEqZero] at h
  rw [←h]
  apply congrArg (fun z : R => 4*z)
  apply sumOverCongr
  intro x
  rw [characterAddRight, SymmetricDefect.chiSymm u x]

private theorem scaleSquare (n : Nat) : 4*((2:R)^n)^2 = (4:R)^(n+1) := by
  induction n with
  | zero => simp only [Semiring.pow_zero,Semiring.pow_succ]; grind
  | succ n ih =>
    calc
      _ = 4 * (4*((2:R)^n)^2) := by rw [Semiring.pow_succ (2:R) n]; grind
      _ = _ := by rw [ih, Semiring.pow_succ (4:R) (n+1)]; grind

theorem perpendicularCharacterSquare (half : R) (unit : 2*half=1) {n : Nat}
    (s r u v : Word (n+1)) (sr : anti s r=true)
    (hu : perpendicular s r u=true) (hv : perpendicular s r v=true) :
    sumOver (perpendicularWords s r) (fun x => (chi u x : R) * chi x v) =
      if u=v then ((2:R)^n)^2 else 0 := by
  have h := perpendicularCharacterKernel (R:=R) s r u v sr hu hv
  rw [←scaleSquare n] at h
  have hh : 4*half^2=1 := by grind
  have scaled := congrArg (fun x => half^2*x) h
  by_cases uv : u=v <;> simp only [uv,ite_true,ite_false] at scaled ⊢ <;> grind

theorem perpendicularWordsNodup {n : Nat} (s r : Word n) : (perpendicularWords s r).Nodup :=
  (MixedDefect.allWordsNodup n).filter _

/-- Orthogonality of the actual word kernel gives the exact norm of its action
on the edge coordinates, including every complement chosen by a companion. -/
theorem edgeKernelImageNorm (half : R) (unit : 2*half=1) {n : Nat}
    (s r : Word (n+1)) (sr : anti s r=true) (z : Word (n+1) → R) :
    let xs := perpendicularWords s r
    sumOver xs (fun a => (kernelImage xs chi z a)^2) =
      ((2:R)^n)^2 * sumOver xs (fun a => (z a)^2) := by
  dsimp only
  apply kernelImageNorm _ (perpendicularWordsNodup s r) _ SymmetricDefect.chiSymm
  intro u hu v hv
  exact perpendicularCharacterSquare half unit s r u v sr
    (List.mem_filter.mp hu).2 (List.mem_filter.mp hv).2

/-- The sign convention is the sign of the cyclic Pauli product on an
off-diagonal pair of edges. The diagonal of the signed adjacency is zero. -/
noncomputable def edgeAdjacency {n : Nat} (negative : Word n → Bool) (a b : Word n) : R :=
  if a=b then 0 else -(phase (negative a) : R) * phase (negative b) * chi a b

def switchedVector {n : Nat} (negative : Word n → Bool) (z : Word n → R) (a : Word n) : R :=
  (phase (negative a) : R) * z a

private theorem switchedSquare {n : Nat} (negative : Word n → Bool) (z : Word n → R) (a : Word n) :
    (switchedVector negative z a)^2 = (z a)^2 := by
  unfold switchedVector
  cases negative a <;> simp [phase] <;> grind

theorem edgeQuadraticSwitch {n : Nat} (s r : Word n) (negative : Word n → Bool) (z : Word n → R) :
    let xs := perpendicularWords s r
    let y := switchedVector negative z
    sumOver xs (fun a => sumOver xs (fun b => z a * edgeAdjacency negative a b * z b)) =
      sumOver xs (fun a => (z a)^2) - sumOver xs (fun a => y a * kernelImage xs chi y a) := by
  dsimp only
  let xs := perpendicularWords s r
  let y := switchedVector negative z
  rw [← Compression.sumOverSub]
  apply sumCongrMem
  intro a ha
  have term (b : Word n) :
      z a * edgeAdjacency negative a b * z b =
        (if a=b then (z b)^2 else 0) - y a * (chi a b * y b) := by
    by_cases e : a=b
    · subst b
      have self : (chi a a : R) = 1 := by unfold chi; rw [antiSelf]; rfl
      simp only [edgeAdjacency,ite_true,self,Semiring.one_mul]
      have h := switchedSquare negative z a
      change z a * 0 * z a = (z a)^2 - y a * y a
      change (y a)^2 = (z a)^2 at h
      grind
    · simp only [edgeAdjacency,ite_eq_right e]
      unfold y switchedVector
      grind
  rw [sumOverCongr xs term, Compression.sumOverSub,
    ExteriorPauliBase.sumOnIndex xs a _ (perpendicularWordsNodup s r) ha]
  unfold kernelImage
  rw [sumOverMulLeft]

/-- Exact sum-of-squares for an anticommuting edge block in physical word
coordinates, with the cyclic phase switch applied to each coefficient. -/
theorem edgeDefectSquare (half : R) (unit : 2*half=1) {n : Nat}
    (s r : Word (n+1)) (sr : anti s r=true) (negative : Word (n+1) → Bool) (z : Word (n+1) → R) :
    let xs := perpendicularWords s r
    let a := (2:R)^n
    let y := switchedVector negative z
    2*a*((a-1)*sumOver xs (fun u => (z u)^2) +
      sumOver xs (fun u => sumOver xs (fun v => z u * edgeAdjacency negative u v * z v))) =
      sumOver xs (fun u => (a*y u - kernelImage xs chi y u)^2) := by
  dsimp only
  let xs := perpendicularWords s r
  let a := (2:R)^n
  let y := switchedVector negative z
  have exactSquare := kernelDefectSquare xs chi a y (edgeKernelImageNorm half unit s r sr y)
  rw [sumOverCongr xs (switchedSquare negative z)] at exactSquare
  rw [edgeQuadraticSwitch]
  change 2*a*((a-1)*sumOver xs (fun u => (z u)^2) +
    (sumOver xs (fun u => (z u)^2) - sumOver xs (fun u => y u * kernelImage xs chi y u))) = _
  grind

theorem edgeDefectNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
    [OrderedRing R] (half : R) (unit : 2*half=1) {n : Nat}
    (s r : Word (n+1)) (sr : anti s r=true) (negative : Word (n+1) → Bool) (z : Word (n+1) → R) :
    let xs := perpendicularWords s r
    let a := (2:R)^n
    0 ≤ (a-1)*sumOver xs (fun u => (z u)^2) +
      sumOver xs (fun u => sumOver xs (fun v => z u * edgeAdjacency negative u v * z v)) := by
  dsimp only
  have two : 0 < (2:R) := by grind
  have p (i : Nat) : 0 < (2:R)^i := by
    induction i with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ i ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih two
  let xs := perpendicularWords s r
  let a := (2:R)^n
  let y := switchedVector negative z
  let residual : R := (a-1)*sumOver xs (fun u => (z u)^2) +
    sumOver xs (fun u => sumOver xs (fun v => z u * edgeAdjacency negative u v * z v))
  have sq : 2*a*residual = sumOver xs (fun u => (a*y u - kernelImage xs chi y u)^2) :=
    edgeDefectSquare half unit s r sr negative z
  have nonneg := Compression.sumOverNonnegative xs (fun u => (a*y u - kernelImage xs chi y u)^2)
    (fun _ _ => squareNonnegative _)
  rw [←sq] at nonneg
  have scale : 0 < 2*a := OrderedRing.mul_pos two (p n)
  change 0 ≤ residual
  by_cases h : 0 ≤ residual
  · exact h
  · have bad := OrderedRing.mul_pos scale (show 0 < -residual by grind)
    grind

end Character

end RankSeven.PauliEdgeBlocks

#print axioms RankSeven.PauliEdgeBlocks.antiAddLeft
#print axioms RankSeven.PauliEdgeBlocks.companionExists
#print axioms RankSeven.PauliEdgeBlocks.edgeCoordinate
#print axioms RankSeven.PauliEdgeBlocks.perpendicularCharacterKernel
#print axioms RankSeven.PauliEdgeBlocks.perpendicularCharacterSquare
#print axioms RankSeven.PauliEdgeBlocks.edgeDefectSquare
#print axioms RankSeven.PauliEdgeBlocks.edgeDefectNonnegative
