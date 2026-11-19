import Rank7PauliFrames
import Rank7GenericExteriorKernel
import Rank7Compression
import Rank7HyperplaneInduction
import Rank7PlaneProjector

namespace RankSeven.AnticommutingDefect

open Lean.Grind Pauli
open ExteriorPauliBase (permutations Permutation)
open GenericExteriorKernel (position)

/-! The local quartic commutation table and the quadratic character block
in the anticommuting-edge certificate. -/

private def xBit (i : Fin 4) : Bool := i.val % 2 == 1
private def zBit (i : Fin 4) : Bool := 2 ≤ i.val

/-- Pairwise commutation bits on a zero-sum affine quartet. The vertices
are indexed by the two bits of their direction coordinates. -/
def affineEdge (eta alpha beta : Bool) (i j : Fin 4) : Bool :=
  (alpha && (xBit i ^^ xBit j)) ^^ (beta && (zBit i ^^ zBit j)) ^^
    (eta && ((xBit i && zBit j) ^^ (xBit j && zBit i)))

private def crossed (edge : Fin 4 → Fin 4 → Bool) (a b : Fin 4) : Bool :=
  (b < a) && edge a b

def inversionPhase (edge : Fin 4 → Fin 4 → Bool) (p : Permutation) : Bool :=
  let x := crossed edge
  let (a,b) := p.1
  let (c,d) := p.2
  x a b ^^ x a c ^^ x a d ^^ x b c ^^ x b d ^^ x c d

theorem cyclicPhase (alpha beta : Bool) :
    let edge := affineEdge false alpha beta
    permutations.all (fun p => !(edge p.1.1 p.1.2 && edge p.1.2 p.2.1 &&
      edge p.2.1 p.2.2 && edge p.2.2 p.1.1) || inversionPhase edge p == beta) = true := by
  revert alpha beta
  decide

private def sign (b : Bool) : Int := if b then -1 else 1

theorem quarticPhaseSums (eta alpha beta : Bool) :
    let edge := affineEdge eta alpha beta
    let ordinary := sumOver permutations (fun p => sign (inversionPhase edge p))
    let corrected := sumOver permutations (fun p =>
      sign (inversionPhase edge p ^^ edge p.2.2 p.1.1 ^^ edge p.2.2 p.2.1))
    (ordinary, corrected) =
      if eta then (0,0)
      else if alpha || beta then (-8 * sign beta, 24 * sign beta)
      else (24,24) := by
  revert eta alpha beta
  decide

def EdgeVertex : Nat → Type
  | 0 => Unit
  | n+1 => (Bool × Bool) × EdgeVertex n

instance edgeDecEq (n : Nat) : DecidableEq (EdgeVertex n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq ((Bool × Bool) × EdgeVertex n))

def bitPairs : List (Bool × Bool) := productIndices [false,true] [false,true]

def vertexList : (n : Nat) → List (EdgeVertex n)
  | 0 => [()]
  | n+1 => productIndices bitPairs (vertexList n)

theorem vertexListComplete (n : Nat) (v : EdgeVertex n) : v ∈ vertexList n := by
  induction n with
  | zero => cases v; exact List.mem_cons_self
  | succ n ih =>
    rcases v with ⟨a,v⟩
    change (a,v) ∈ (bitPairs.flatMap (fun t => (vertexList n).map (fun s => (t,s))))
    refine List.mem_flatMap.mpr ⟨a, ?_, List.mem_map.mpr ⟨v, ih v, rfl⟩⟩
    rcases a with ⟨x,y⟩
    cases x <;> cases y <;> decide

theorem vertexListNodup (n : Nat) : (vertexList n).Nodup := by
  induction n with
  | zero => decide
  | succ n ih => exact HyperplaneInduction.pairsNodup bitPairs (vertexList n) (by decide) ih

variable {R : Type} [CommRing R]

def localCharacter (a b : Bool × Bool) : R :=
  if (a.1 ^^ b.1) && (a.2 ^^ b.2) then -1 else 1

/-- Quadratic character matrix for the canonical symplectic coordinates
of an edge block. -/
def characterMatrix : (n : Nat) → EdgeVertex n → EdgeVertex n → R
  | 0, _, _ => 1
  | n+1, (u,a), (v,b) => localCharacter u v * characterMatrix n a b

theorem characterSymmetric (n : Nat) (a b : EdgeVertex n) :
    characterMatrix (R:=R) n a b = characterMatrix n b a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨⟨ax,az⟩,a⟩
    rcases b with ⟨⟨bx,bz⟩,b⟩
    change localCharacter (ax,az) (bx,bz) * characterMatrix n a b =
      localCharacter (bx,bz) (ax,az) * characterMatrix n b a
    rw [ih]
    cases ax <;> cases az <;> cases bx <;> cases bz <;> rfl

private theorem localSquare (a b : Bool × Bool) :
    matMul bitPairs (localCharacter (R:=R)) localCharacter a b = if a=b then 4 else 0 := by
  rcases a with ⟨ax,az⟩
  rcases b with ⟨bx,bz⟩
  cases ax <;> cases az <;> cases bx <;> cases bz <;>
    simp [matMul,bitPairs,productIndices,sumOver,localCharacter] <;> grind

/-- Exact orthogonality for the signed quadratic character matrix.
It follows from a four-point identity at each binary coordinate. -/
theorem characterSquare (n : Nat) (a b : EdgeVertex n) :
    matMul (vertexList n) (characterMatrix (R:=R) n) (characterMatrix n) a b =
      if a=b then (4:R)^n else 0 := by
  induction n with
  | zero =>
    cases a
    cases b
    simp [matMul,vertexList,characterMatrix,sumOver,Semiring.pow_zero] <;> grind
  | succ n ih =>
    rcases a with ⟨u,a⟩
    rcases b with ⟨v,b⟩
    change matMul (productIndices bitPairs (vertexList n))
      (tensor localCharacter (characterMatrix n)) (tensor localCharacter (characterMatrix n))
      (u,a) (v,b) = _
    rw [←tensorMatMul]
    change matMul bitPairs localCharacter localCharacter u v *
      matMul (vertexList n) (characterMatrix n) (characterMatrix n) a b = _
    rw [localSquare,ih]
    by_cases e : u=v <;> by_cases f : a=b <;>
      simp [e,f,Semiring.pow_succ] <;> grind

def kernelImage {α : Type} (xs : List α) (H : α → α → R) (z : α → R) (a : α) : R :=
  sumOver xs (fun b => H a b * z b)

theorem sumCongrMem {α : Type} (xs : List α) (f g : α → R) (eq : ∀ a ∈ xs, f a = g a) :
    sumOver xs f = sumOver xs g :=
  congrArg List.sum (List.map_congr_left eq)

theorem kernelImageNorm {α : Type} [DecidableEq α] (xs : List α) (nd : xs.Nodup)
    (H : α → α → R) (symm : ∀ a b, H a b = H b a) (scale : R)
    (square : ∀ a ∈ xs, ∀ b ∈ xs, matMul xs H H a b = if a=b then scale else 0) (z : α → R) :
    sumOver xs (fun a => (kernelImage xs H z a)^2) =
      scale * sumOver xs (fun a => (z a)^2) := by
  have expanded :
      sumOver xs (fun a => (kernelImage xs H z a)^2) =
        sumOver xs (fun a => sumOver xs (fun b => sumOver xs (fun c =>
          z b * z c * (H b a * H a c)))) := by
    apply sumOverCongr
    intro a
    unfold kernelImage
    rw [Semiring.pow_succ,Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul,sumOverMulRight]
    apply sumOverCongr
    intro b
    rw [sumOverMulLeft]
    apply sumOverCongr
    intro c
    change H a b * z b * (H a c * z c) = _
    rw [symm a b]
    grind
  rw [expanded,sumOverSwap xs xs]
  have grouped (b : α) (hb : b ∈ xs) :
      sumOver xs (fun a => sumOver xs (fun c => z b * z c * (H b a * H a c))) =
        scale * (z b)^2 := by
    rw [sumOverSwap xs xs]
    calc
      _ = sumOver xs (fun c => z b * z c * matMul xs H H b c) := by
        apply sumOverCongr; intro c
        unfold matMul
        rw [sumOverMulLeft]
      _ = sumOver xs (fun c => if b=c then scale * (z c)^2 else 0) := by
        apply sumCongrMem
        intro c hc
        rw [square b hb c hc]
        by_cases same : b=c <;> simp [same] <;> grind
      _ = _ := ExteriorPauliBase.sumOnIndex xs b _ nd hb
  rw [sumCongrMem xs _ _ grouped, sumOverMulLeft]

theorem kernelDefectSquare {α : Type} (xs : List α) (H : α → α → R) (a : R) (z : α → R)
    (norm : sumOver xs (fun b => (kernelImage xs H z b)^2) = a^2 * sumOver xs (fun b => (z b)^2)) :
    2*a*(a*sumOver xs (fun b => (z b)^2) - sumOver xs (fun b => z b * kernelImage xs H z b)) =
      sumOver xs (fun b => (a*z b - kernelImage xs H z b)^2) := by
  have term (b : α) :
      (a*z b - kernelImage xs H z b)^2 =
        a^2*(z b)^2 + (kernelImage xs H z b)^2 - (2*a)*(z b * kernelImage xs H z b) := by
    grind
  rw [sumOverCongr xs term,Compression.sumOverSub,sumOverAdd,norm]
  rw [←sumOverMulLeft xs (fun b => (z b)^2) (a^2),
    ←sumOverMulLeft xs (fun b => z b * kernelImage xs H z b) (2*a)]
  grind

def characterImage (n : Nat) (z : EdgeVertex n → R) (a : EdgeVertex n) : R :=
  kernelImage (vertexList n) (characterMatrix n) z a

theorem characterImageNorm (n : Nat) (z : EdgeVertex n → R) :
    sumOver (vertexList n) (fun a => (characterImage n z a)^2) =
      (4:R)^n * sumOver (vertexList n) (fun a => (z a)^2) :=
  kernelImageNorm _ (vertexListNodup n) _ (characterSymmetric n) _
    (fun a _ b _ => characterSquare n a b) z

theorem characterDefectSquare (n : Nat) (z : EdgeVertex n → R) :
    let a := (2:R)^n
    2*a*(a*sumOver (vertexList n) (fun b => (z b)^2) -
      sumOver (vertexList n) (fun b => z b * characterImage n z b)) =
        sumOver (vertexList n) (fun b => (a*z b - characterImage n z b)^2) := by
  have scale : ((2:R)^n)^2 = (4:R)^n := by
    rw [Semiring.pow_succ,Semiring.pow_succ,Semiring.pow_zero,Semiring.one_mul,
      ←CommSemiring.mul_pow]
    congr 1
    grind
  exact kernelDefectSquare _ _ _ z ((characterImageNorm n z).trans (by rw [scale]))

theorem characterDefectNonnegative [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
    [OrderedRing R] (n : Nat) (z : EdgeVertex n → R) :
    0 ≤ (2:R)^n * sumOver (vertexList n) (fun b => (z b)^2) -
      sumOver (vertexList n) (fun b => z b * characterImage n z b) := by
  have two : 0 < (2:R) := by grind
  have p (i : Nat) : 0 < (2:R)^i := by
    induction i with
    | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
    | succ i ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih two
  let a := (2:R)^n
  let residual := a * sumOver (vertexList n) (fun b => (z b)^2) -
    sumOver (vertexList n) (fun b => z b * characterImage n z b)
  have sq : 2*a*residual = sumOver (vertexList n) (fun b => (a*z b - characterImage n z b)^2) :=
    characterDefectSquare n z
  have nonneg := Compression.sumOverNonnegative (vertexList n)
    (fun b => (a*z b - characterImage n z b)^2) (fun _ _ => squareNonnegative _)
  rw [←sq] at nonneg
  have scale : 0 < 2*a := OrderedRing.mul_pos two (p n)
  change 0 ≤ residual
  by_cases h : 0 ≤ residual
  · exact h
  · have bad := OrderedRing.mul_pos scale (show 0 < -residual by grind)
    grind

end RankSeven.AnticommutingDefect

#print axioms RankSeven.AnticommutingDefect.quarticPhaseSums
#print axioms RankSeven.AnticommutingDefect.characterSquare
#print axioms RankSeven.AnticommutingDefect.characterDefectSquare
#print axioms RankSeven.AnticommutingDefect.characterDefectNonnegative
